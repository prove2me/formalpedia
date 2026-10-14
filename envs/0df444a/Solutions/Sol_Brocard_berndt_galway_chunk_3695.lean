-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3695
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:24:18.358189+00:00
-- url     : https://prove2.me/submissions/67f3a79a-e590-4f6e-b5a9-690382e51bb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 664388489 ≤ n < 664568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 664389739 1250 664388489 664388507
    0x70f030807140a02060f12010b190e0f06181f080705030705040f03060f1104050604030f060212090715021c030e011e0902030111040e040b13050d030c020f0a03 70
    0x40e04000040c41c109030380f4101080d1040083d805200018007004148000340688020004080c041c801d0713031398645a1940500c0743c0c441030355400c10042403900d4054040c1d003000c1d0316450041c1c4a4941c0030140008158158070680201d070100020b50803444240c03030203a0114646d6803d00001c42d842ca5101710b80039000e110080c1813a8240031001c00003400c141c0c401c5003520001e1000f11050103a01d81d580c01c0c40c86c01888500480c8031b6080c07c204a808810000108840840d44081c20f46842c1518584480c400c00405500071030b41542c003006007803090702003012558000c035404406400e82610f4181d90205d64103a000c03224096400c982000c1441c20740009114812000c0c5060200e20b50000f40144e03401800052205103004180c148070304011101540a00c1000748254005c0140c40f100011108103402103114818501d046000014001140c081c0320320381001c0b642241e10100c4505aa0f507504088070800d0303680009a454590340c1c1d51982c1040340e6040d800c5001c029141d5980786850041140c11 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 664390989 1250 664389739 664389743
    0x17150105100c02030604080a0e03070303080a0f02130b1b01200a12050c030901060906050d060b0d05031908070c03090b0c3a0f1e090902120603070f030807 68
    0x70760104032440b800784480000266008095884624192400386000c1d040000c854001131480c5418032510b040000d1040143d9801d9101c50700599a9000501e014142c080075480e0301c15004c0c0007510f28281d4916920024050034200184c5464201000108180e14000b2140c40790b8180030071360415201c400d400c80c400d000e1a151030f941c2c4500e02c01c801c1e9840c42080741450728291070304c800c2002407201c400295009111600c001e200c6140e0b20500d0700c054034220b000302c81d8490310b4035804800089040d0b0004500c90000340903024090419100c4c0c1d8110b8010701d001c0081500c11442c80046079030700c08480c5500c58132600b40034840c100b880d00c008242440303130700440590350400648041c2060040106160320049001c91001301d20b04021185035210f0b801602000200c3d600b800c84281c030b40505880e801120700c80d640c506004020300310802070301045000600a0081851000c9500e2001e030004006096100d02e41004d107061a01c10f141c9400c0081e03118604c0e07003c6a000500c000b0700d032480ac41e45496 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 664392239 1250 664390989 664390999
    0x1806020c0c0d121b05190b1003080d1d06040c0513020301030b0a0e0304050418020a081906020f042105060a1a0105030a0b030607080108010b04051005010503280617150105 75
    0x411001c004c40710094003042c01912510a499001400c1941c00704000182441500c0c42c9590b500c5017024000c0c880c0c2d031800001c14019003031140c40c03440a00b6611400c00c4a0388a40781850026281c041542080320607201039407000405407040c0450700b001040c030704000098038030843c6150b2443e111f1110320400900702c03101d01500c0f1103842a110324100181c03000383c040104100402a00450b0690301c48940905c203d004191048000803010800300c0c022020006420075100c4804040d0b9901000394030020209500a034180004100105440c0d01080c3d0102c03a565501c48042c1c0c141422490004000c0002c24080d04083d00c050f54201481c110a00d2040203081168880d200e0f40d08040151101c0082e494051003001c040100749036100c85080c0c104d075a42c00c000c020b0040d600d424041a900d04032081200030341000380802c515407017100116441041451812010881d10342c1c5d80c0143e00708950506122516441d090100091602145264903210801020010150800c10106040c144200c900c91 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 664393489 1250 664392239 664392257
    0x2a010b0d0206040315060b0a0504030b060609091314060106050405010216080304090e0c030303040f0309080d08060105070312050117010c0306050f060a021903020604030e0d030804151806020c0c0d12 87
    0x40c45822060281c0805d03c800e5823a8021580002d1158002d0b11040e9010800380c0041401403d122040780c4002c00064101c6090780d03510280d070f03005803516440c101c0700304406034200e046041c814041c6038040c0c40d03d47d481c103035140c0c51310700020301d4280301d1a20308440103203401041044050020445084502a210200b186014072152504102d010100d141d014000001000208842198201516403090316801e80a90301c901c0b0203659002c2d5000d01102050005021605560055018081c810301c2464070102e102614042d030411b0700d4081e884011016111070035902c01c80c00c20b008449002140c2c1c42d003002018074020010700c940d0601d9107054000e40b80002d00203005403003404180707080264654085003501d52843c000399a140e04503001d0303001950f0191890228a04070001d038a034290199283c0c04036881c0e80e15404d040c0d25595581c584295038801c0d5000d10406400c9011112038080d480041c0c440d41e00340040f032b04107083d020006225502c0d220b0311200060a03490314035010340b5145441520 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 664394739 1250 664393489 664393523
    0xf062e02160e06040e03120f040f020409030f020706110318060f030106050c01060608061f02070f0308030f10080a0b22060b10030c02030a0c082a010b0d02060403 71
    0x200300d0103502880641e4009040810002410708681d0b01815059130100b180c0000190071680b2409564032008031425031402040f052004c8a54258005006041440388944182d000500321152860105c01080300c400c40d1000d03868051140700000c00c1a42080d440c1c402c54101d003141c4900c00c009a202d40300078411142115501c1c0c10003a11404490000c803180e0b07950b141d00c40548580c00080c10111150f08221001c200c0c00e21a0b6000b0740140c0c00a020954804c03400107282800c06034400b4540e0071442410000504403c0600c42400154051240342c0e54074148000340c00020400113050643c400c1400b035042100b41d0f000142040059080402480c89448213000a140d01040c5008603400c402c03441c80c15414090309501c468000c0c00200e9111342ea20030300310002e0301a107200040700c40241e08180004200140a4000c000f101840b034a8124500203030f00308500a001c54400034142d4100072520030304403041091044056981040301c20300200517195000070414800d0f40002400c03011440b076501d0b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 664395989 1250 664394739 664394743
    0x5090a03050109061b0905062a060108071a0706090203100f1a03010603120f0e0d060c180b04180207022e05160809010516060c1205060a050114070501020d050f062e02 73
    0x200f00e5030b112190306500c00c02079010354ad865000303010341066030103802000142c441038990000481188101c1c0300c0e00f4000ca40c0c85690003040d800c030042e6003500074519001c1020180e80324103030007034441c01c10000700c00c2544441c4850200000b06064040d81c500841840400c0e001555000c0310030640c5001c40340e004501740129580c681e81d11840381c005001d030008400304160354005003012044c075540c0c03074080040701c040c8001d4040607205050310780004000078400c018507168001240702c00c10f040917141c0342840d030108016841009500402e018070705003a242c0b18212100003c000186464000c0c00c01002c2e1104a12007421080002d002a400184c03040269004805468407084214580f2180305401d0038800090a61201080009100449260078003600b80c81a00d02407400503111243d043e003400e0040d21074040d00000340080354800c1c400000001c000740010450020907840208081c1012030300e00051450281410380304544a00784845030040e450400e415400341c14a000c00054400c500c168 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 664397239 1250 664395989 664396027
    0x50a150e2401090f081507020312041104270209010b0f03070804020f0d0f06060501050f07060507141b12030402060d0506060d0204171002040f03110105090a03050109061b090506 78
    0xa991141c03c2000000c1601c004100f104081c0c00100306d000e00e583e118081242c69101e000c0c0300224485c00b400c04500071420f9881c1d04010301030080c1c800a114004910f800c800840c00040e03858070401420115030441c20030144150061504012960410380e442000c01c039203000040030101009039000008040d0741d50200070080703440c0050140064a100e0781025050010301c0481a50300071b0510a0028495200f0b9003129041c0307624801d400c0c00c050950303681c04007502015210380c0c100050009004148034100c001000c0004509100d1400c59413050f5444d42413035290100a881c1e403000384100001b68590a0880c0d50011009100040c940c0e58280002c009000d4501c201d0342d081d102040c045180c1403401081100a01b42e1000c035080603010759449070036032240740901d0700999109802040015810000c1410701c400504145003403010050205802038441c0c1d20560f46a03441c3c90045c02070050300d00c90b1140400740c2c540340c840c1d5065041c80c06440580c2612445003d50800610340a030410b1110000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 664398489 1250 664397239 664397249
    0x21030a0e01060b0c0f011401060905061b0115080f030304030e06031b0a021516020703170d020f07031d060f07050c04090c06080c0a020606040b030f01050a150e240109 73
    0xb0b60300c540c42c415401e503985402004d05c00d41396180080e080b440c100c0c8914042d04880d81c5544030002141480c0a0040c00d0300314200b0310240da640500344550000c028022131400415a070158460640780c17640c01490b000301400c0b05181c58000300140404658488600c0039040301c16107030700341d8a44a0f002620402588558500250b400100301480c0599010583c075510f6808012103001c07584450140c0c9226441b181d40040260344501c0301080061000705180103840c03141007031181400880c10300301d070907603000c2040004007160015941003015044400b6026035520045402034030001e580100700b00d4815100b02c0e61038528046608d00802c0b200b04440211110060414003143c1910324100b003142100e13005140201d9000000245510001030035500c40f100c10368010b04880d00c80740140700042c00c80042e100c0d018020355075204c219080034000c85000b1f0443c2013000400c4487d8030503003070f00342900790001c02c00c004484013409901200101480003000507c16408032450070100143c41a20b059402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 664399739 1250 664398489 664398509
    0x31506050c1c09080d0206090604030309030c12031d010507140913060b07170a09050910080f06010e0903090603010306180f05030304050c0f01021c121103010821030a0e0106 76
    0x6400d21141d84024003e08451a800454020100442c1c007642c4540701282c00090030b40c4401f0001e4082403003504840b4100f03010303040102c2d0407003140d12071001d461481038a407400709440d0f00c42c1d8010007040300c0311035070781c601800004c006030308019100400300200c10070700203094840405c03640700c01da407075402c18501c0151010f010004262780e585803203560b8201304400c2d14210032144440d101000c00744c0864a0900c407a964032461141048108442120090a10940c0810002c400700e8906020072480306202d5900008016a40c580000340c1c00c0c2d0320000700b007180b442d0030070301008a890f269001902c0c10b49501c10008035040da5400d402046440c05508007400020080741d040c028000d0200055000351b00800a462001111200b40403880d40c80241650045c2d0041041c944145d6102c0c8802d018100b103807909409007018403440c002682d0b05001e220203180c6000004226000041102500d00304540c1c62148070b0688002541c03616000081607801c1c45134451003440a41542948140c024060341a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 664400989 1250 664399739 664399783
    0x9030a080403090f120c0506040302220204270c090f060e2806090e04021005071103060a0b03060f010b03010e0a1b171b1b0a02090c0712031506050c 65
    0x1661001c441c4000c0000e46206d1028030b80400c160a018044070251790300030301141c00c000b180d052040012156036900c6c400596080c40082041c00c400202e41484554500389600c07610710b9841500d00302d40700101000e00740309504108000080100a0450441c2c6484c24078041505000f40428401610b1000c50710415011031514032400c0c00900900041e00c10340d680b14002184c0755442890710010680c0d01a50042e10015607981c09440b40c001040300344e01c144000400148103401083c60040c0c00d8032110361160319a2400400350030104035255001c040b10060301038952400c0c200d87c406200c1805050318030028400050045510750300221040f01e00c01d43c08003501c80b08070304001d02d40750240c104c40d880396940002240f610704800300108034030114280c0c02850046070b24166609078041c0100f100a42c05046402009030381c4121b8045e22904040681e5a921003240c5003203c00c01260202c010141031404068007105c40000110340181c80c10b5003400d0741d0301d07040b00c90424640b40120000c0084540303e02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 664402239 1250 664400989 664400999
    0xb010f052805030f090a15050415060b1c050f04061d07030b1012030206010b180915120706020601030f02040f0c0e01020c010c050c0925080601080f09030a080403090f 73
    0x80d0043d44600e442d4035090b00310351a01a401500e603894440d0280ca1340164840e10742c2419034552260750840c1c4a03e103510090502001c42070141d8403aa0302180144201040c031400d601c140140740302c0c0f08a00500304200d80d10b400201a40300103070142018110300d0b6034090301d080c03400750f0400c0700c100001048103d90009030f030703881c0c001000001102e401c010b00b580c001c40001c481c1101d4581c4010981d054020382490381c2041d01251841c0c001025140401101d5640110707a600c400b1840d80c01412031624518109400c0c2e428021903541c0c035082100203a00910080000d661701146103415241c0c0b1030325009a0200f0350000402401182203c0014103181c8000c005200380c000108107202c0a00783c0940d00d03907000301d60040d45e044144a0b4080d0075900400c01540c040d28180d400340f0f910a000300d1401d00010300d204c0040c40300c0101e81081d100841c1113401805241d68000101c5503004014644140340c42c5880040c1c240c1f640a2818054140840100820109401850000c0150111101d040c1d400f60ba55 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 664403489 1250 664402239 664402247
    0x6060309030c111c15140c07142d070506041226030a0c11160b0904110705061806040c0909030e0405130201030e0105090d120b0d0c03020f040b010f0528 67
    0x40003d45c00c0e6645855003000d0711000d00c440044c41000400c090750305081c0e16071505079001400d954000740074003c207142d15001d80804a070800302200c803050007c614900c0f00310b0846c6080d130741d600303d6441450140030030000c00c065902c840040503844501080400f070505d0042e00d15a0788130350100c141c15400710412000602940c08a140182a40e6419804141c50105151562007a04090440c420240f07c1400201624001001040c1c40980f00040c8107418220101e502e4006000880e1290444130511404101d0781c0e100100464625010b006179082035900c500c40110544100c00550340c460b0014410303d8002c0380c03040c98148000c2c3c000e000e603180050180404260400c02203000ca4980003018001b104148900c61241c41c601d4014403041034401c0307081d9403c1c0325150303065511740d450707a01041c15a140c50744240380c418490102c500065056104110b01d4a214041c52800f8501d00510314019a9210000c20942e004908195650305084921000d11540e003800e00500c0c1004520f81c400141e40c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 664404739 1250 664403489 664403513
    0x30c0a17070f182009040e0a020303040801020a4107050d051b03070b040224180109090209090601080c040f030f02121507032c0703050106060309030c111c 68
    0x3c5450200029854003882c2e240901c110b581c80620060309012403c028101544002c400c8920308045494010303169002a1444d482600035401070394000c034601500715044482101202c22214104100f03028000725888900d06215150b88180700d009100b48903111250304440d00507400c9025102e141c0d05203200640598030400603442e10000311406241084004003d07101d00300e5101c0c88015141c1c88a408120000100d8464041010344035200c10801b0400c450040c030104401d09440003402040000150503a80d0765804030451034010400c0c11a250346007000650301078401d0904549a441e0540c000a60b409150411954501e41e00c0d40841407180700300e180f040861003240d0080350710307105042040c0c40f000080154400d4a01100c04603503c18000c1e000000710036030300000d14081d00012030340040048001c9480070001e40000c5814024420301f8042c640140290781002d110308000765500820080080002605941c003410303802034140d441d4081070404450320200075425070364508201100b042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 664405989 1250 664404739 664404779
    0x31504240614160602031e0403081e0106080f0907180b15070c090b061911070e070f05070609060c080f0a0c0c082b1a030c0a17070f 58
    0x488406084850701214003183e03200150034000c180800c0f01070303880902a4101420355142d050616a8001102d6040991640310390f001b582c0303020850800310440072181400c00c40e003211081c0001c00600607190411441900860000d0b28a4040e81c1e40e44071050901171250014144148001c0c140c40100340141c02a01c0c010700b04560719156141e506003031400c04e129002c4028108040b81e039041203a20116408002100341c090031030303494590204180b0707084100300005003012031007034000d40c0e202641c200043e00251442410710401820807040c00b07400c00002c207103080200301002400710b0401400b6005820041c0d848a41880b0030750740c240004e41810411200c40c0d4050110900264102540b0b004034000c448442c0c60704102007441d600c4070b2203682e2242088030032080c0400000c40408060300c1380c10300c11002d5023100107221805088801242001c08600c03d00c2907024441450b259910301c0d0401e0200d488070103056400d050350912039414585998005000d4600240001440080001035a00014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 664407239 1250 664405989 664405997
    0x191202010c0c06090f0506090312030a0b04180311061b0702030102040e010801020304050d0e09010605090f100e0a0905010e0a15080102070636060213080a080405010f090b0315042406 80
    0x254a84007884110700808c5c140690541c0494400443ca01c0108000c5800c02407228000c41c0e402c8603040031906507810282c03003914691444094100b410340c000c082103841c005100151070305003003018202030103c0724004c9900d01070100151144c03c641d000d5048400820320b2070b0300c1c2d03820356035140c80302d42c001e400c00c07182500c2c0d41c05002100201d042c400c0100038465070b40248180709590902074111210342080c09519000611604d00c480ba5a48000007090b11182d00e50b40c1000d0141008207006040b0515481614841d0070000140800c4400300c20099200244000c005440c40f511203100c5924241503000c0102c95200181240034400e02c4d030440320710714503861603401c3c1b400d400b4100c2140f000130002c40c9204180c0480ca807207000900e142c00502c070603e05602c4c0344403003e44403208a414580002c030300b110f1160340010104459604500d509803201180e00700060200d282000180b014070000b000100c0e04070344121141d01550301c90b40819a581c01042c0403001d40c04100e030280c040d024907801808085 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 664408489 1250 664407239 664407269
    0x6060215010b0d050a0605030f071a0c0606090604090b040804051f0c120201060506040e090d03110a080403140f1b01110901030506040f051003060605191202010c0c0609 74
    0x59501850400d040311181d007011490810f0110b80400180000380000045a45036003001030300b95000c006001144254001400342caa2500c01080d603194849500c00c06802014400c101005902050065101c841912400071595819000030024072050400400385240c1500788000d100030a4040e00644409444c1041c120144640f040e100055a000e11000070f42c9094940300000c10704805415448050300000c01e0044c0c0310710003d2001c0e000782e001808621071020400984c04800c0088000011980c14200401c00c0d82c1a01074009205201d549410b01085030007107000c043c4201d000b0040c0c28140c0341f0158643d610b61680b42d14990100240f0741d5024000a1900440a010f12460018082035003400f0700e800400c02c01134020f000d00400f015440f541c2c3d81c1030340f80300d54000e000c0c0702d00c0350003180100b0680307070b056181c414201e071490741000340140392441c01c41c800400010786032015121400e42080800d15284012a0b00e10020440148003901c406d0780028a0f580014004042d210740250f41c1e00b207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 664409739 1250 664408489 664408513
    0x1e01120b07090f060e150307030b0a0b090306041b180902130e070510030e060703060e010e070504030b041e1b061e0509011827090b0a051810060602 65
    0x300b4010742c010003544049004041000501804015a00c0040600701c88000c604072440542d1a4000300c4145000c00d4942a490015107440d050340740203400900075885c2448003801c003080c0d841c00b005000034400800c0e40011072a020200e00040d0041880f110f4949000496003081405465400822400b501ca440c41c141c00302c0703050307004240c0058080001002d00901d88420032080100e42030660050590320900c0c008526001d0050501c80c4a070381c0c9000c6503039440c0845200400070168801030b003601e00340d4140030b8003130f80c44004c032030449400c401d01640310f841d241040d400c2940c0281c02009030456583c42002000010301c0c8888650844002d19241e0541e108003e82d8a81d13140d0758080003c1c1054103040b1001409034000c0c10845070706141c610408110b041d803a0540b0106a005502822440101000172071403510800082505400c402e10199201e5602e44005140c081e049520498403200020401d0ba040c104200303512560f50110b40540011110707400091042e80948001401100d90701c803e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 664410989 1250 664409739 664409747
    0x100e0c01031116151401080f210301060507020604181d03090102031b0c03030f180a12060504031206030f06050112020d06051b04080f0706021c03051e01120b07 70
    0xc0c1030850500814082c1031a130307150741a4607000014000c490342c3d580c20384500e0450707000d101406400d0900c01008003800c01003149282010301c90402048022402c070380610320380d4100c00d03203045400d00e00306070f0749680c01131002032400e026176041441142c03080014100010041c7e0015030340035030b02103007065100107130300d1413242c803441000101805a4410807800038a007200300183c8040e00e06081c181e56a8050341c500083c21a03201c2140241c4086010402c0048001459a1324601800c121507007402d50385040010240c10310236100c003401c0d02c1d5a5000080034035002c0c40303120180454104040050b981c59150010340e4180800b0261000d5107482c0000c41d01160b10003c240d6180d4004200241090540da074030005000001c19000100d042d101d80544014a2032014201034020305e0040d1540400404940d0b243c1900c660001c4115030000410309a01c5045819641c81594103240c00f080c50707030b40c80c11b2000c00382c1040450398441521400c0001504e005820803c03144505ca581c4001464a41e04002c035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 664412239 1250 664410989 664410997
    0x1060e0a23070203070b0c0d020406410717040b040e0a14041401111306031404021011011d070806130503122805060f01140d0e100e0c010311 62
    0x540d0007080300344080340403000410317407000c7c1c5056038514141d460b04041040e032700f1075808440030610304020801611480405584140740201c00c03e03441e44040403020842c06640221041e50f01000aa00e90a01070000780080441b0300d040e03040c0b030351141c1d1b03142400c20a51151150114070f8040c80b011540300038a03030082d00c42110403000040f5039500c454581402495000011001c10740d41c0d40d2041b82210b41c0c800c0500300d208980c145d0300e00024075060020b01a507001106d00981a8104420000140c0e20080202040801840c201640180f82130400d401002540044440b80340d9024003811240c9001444805803140e400584078903864500d690000c401c0c003840000c0c103940003480328440d10098035014540c03250917416000b5092000603e50907520f400194020000c42d02c92013041164240640703160703004542032070082050149400e102d00c1c10b019001050340c2041c0c850b580c00c112041c040283c6c85030720b0300795801004020124510140c1d10b400c0280410b0209e1b00b0b028200f140207180d00256 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 664413489 1250 664412239 664412251
    0xf141b0f300c03040f091407030506030a060f060f0801020d1503080414011b0b15010e01080615070203060f06032116081905091309020d1401060e0a23 66
    0x14044168880221580c100c2c0401c061107102c1070200082c0c103030031100803a0060010950018a980643c0029203c20328000d007208185801d100500c0525240060701150664010500044008800b1b01c00800740c01558002c1030000150b90000c01d241c0019030050010307000317981041108403902c1e00b1383c0c01c55401c0e82c48081c0502e6401e000c1042841c01c00b005440c40c0c0b08052405025a004c200d117008844c040d0188150ba1f0700c0a12410400b01c450780b00f4024034051000d080503c220000340000800c801c000810b0a0f000d94000000c1c01d101c4074080c000d0341c2d1100c0d801002d81c2d0807890607801110202c142151f21318403d100310500700784030b80c020301122100341d980003640c20300c0e02c00ca0321010700f05104e403840704036082c1c0000c02691560715140001c00d64040300307568900341d40310800010821981321081184044914051036400181d0f55070f401390100300d5002000c00031500032008040c1c0100420350141802d4984070301045044181d69001c4102040219418441005141c2c88524035600440786 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 664414739 1250 664413489 664413553
    0xf061e010506070609030e061803010608030301050a0b09030703050d0c11010509010815131802090a1112070210060e07020d02070e010504020d180b07140306010f141b0f 74
    0x380012440a1700f005070002c1c00f0b42840c81072030140d440810500d81c013040451541da2081801e1031042e142c2070290600a000c58401181154101400904188000d21400c001180d0000b9602519203040c86580000c5401c80c1c281ca512920b001c601400c1007640d80403c480300c8c058a41d10100641c059810703101c00e000180d4602100356146068181102c440021980c3d004e040c602061000c0f000902400401e0791410000e444e00452a00c14000c4200c00604891f001f10300300f09003000d00c4100481503909140b03d00705200c070540c99034002a824200320740340e55000c080c142100030802c02d201846003400740c03042c0d5017102e61540702c802c800c81e100d030064000d003050315070294010015450143c000d480401c800040009100703040d60802d005100d503100c41103528250000c00c120200780c0080103500300100c4c08080a04c3c603e0040300003880355041101003001d210820b00f640030100503400640303800303100b41901c0306141c82881c091580e17600300a01000d1190b00c83c0040f000d003a003801d5001068500c003031382c40d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 664415989 1250 664414739 664414747
    0x1306080c0a08070e090108011e0902031902060f0c011e1a12070506180102010b060712051312051c0203041a211008010b060a0806040905010e0f061e010506 68
    0x400702d0742d612024000f10f00300102034005800c1540e074802a40d00a204400000a100704055003040721030b80a802c1118030039150810b04005a02c0110f0038150320071034142019040c0c15184005442070003640c459445c1c104d0045602a2140c205622261410103001091080c50408864600648000c9500080748401000f0060404d04080801002c84032001c420781d07031640d4803540408d0040c1c10041030241c0c121008030410690396028406e02080c16001e850b40b0740303081364540301d4641c0104200340003420400005509503000d00519813880c05071122004600c0240d4142c10000e0340d48000c0710407092903420019840e03602c603000100b107404844c06620450001500c044510380c05c1d41010310111400c419491703c805400d8030f10a101c620645860700d001ba81d450801c0c800d6800c61342681c0000e8040c1d4000c1084200c07040c0c00c03040a60303100100301c5000c038036003010f881e045003d841b080741c10007101c0c42141c000611030030003c54014400c6082e0320f44183c2c1c4540c6840454503540e000c9c030030f860b00000100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 664417239 1250 664415989 664416007
    0x801050625080c010c030204090608160308090a09060b0d05070905030d05030606130e041101030207033002030c07031701031101110712140d0f02030a0f0e0301020a051306080c 77
    0x41c040c04510740925502800c11051203940c509403551083e201d80002d84c0064240215641449428007801070000100300300714107440c0c0744042e08070360301004d02174031404a5851416513464840c0300c050913500740188629035503100e00e075449030082101c0c045074a04000000300c1d0301748614180300441d41c000b402000c0b5031404040688580e44060042c80c3c0002d4208034184508038100320303078002096801c07241c03c03942c90700c0e0409443c3c906640c080e03141018010003502c400300303902441940540b050b484d0240441c80902c1c1c980c81a5484e03010040004070700110411009035200b0001d00101c90290301d9000903500c400c01074001301e0300d0034000100700031442c0e507682110307500c201d42000b9815042421100c030540c5174075540301142d090140841d010101f0882c0703a004018207004c18245500c02e07040070380c0c884102030806510f0307000300818041004066032a02c0360300c0c0d110f803180c01510b0340054000c540e41e04c0c0342c250080540d400401036022440015000054042c4a0041144200c00b59a405800c10042e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 664418489 1250 664417239 664417297
    0x1030639091d0402090f0907090b031c0915030209030a230f0601061b0c05060307140d021b031c02031b030708060406050f03070b0f0c0d020c0108010506 67
    0x21004010030065400c00104105081012440c0030b8242c0400b1800d603072900344104041c151005000c3c214201c1010280f003010540007899805840c04800041010340140000c44d2400401a0f00c0200603500312001c400b006800c110f0701001d49480124003040000d100005130164442c1050482c3c16a0088403002c000c02c00c4c0366005015140d40042c1c100c071038480192003c0c5820003071180c0300119049840100240e076008104054400591410020180088d0b1520105d20700c261003054010314000001945c624441c21061b108000091315107612440c005480400a401105109800e158180d01607a02ccc3c8000009641004480c840c94601c454124840403002e03410240c80d200d21040c2a1900c4030840c2a00b0000e144a2022540c1e41402c51810000304410744410742d011030302980e60f581d00920180c40c042546419035402c0d11a4a5641403040e40c40c58187c802c00c17070100c030603010741d842c8a0310541e1702180c0015440402d907141c1e107160341c0f43c8007000414070400c0d032a4480078812102c614461001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 664419739 1250 664418489 664418591
    0x13060b190e06150c06010504060e130b04020102010b060d0b090912030c1c020a270803040504020c0307020a080a03141207030c0c060204090f14130305070f1505010306 73
    0x10f4840404203003074003003410a80c0c1044590b001c154002c0300062095003428030036080205109071034086681008050640240f01010001e08202042400141964001d4100d210a42c0b405040250380b45581d61105005007108154144108110401300c0c1c0c04080000302d0a0280b145203403101d203152260421380d40300e9070000980d40c00c01031040000b4020128070f40701800c1c54295949401e9208260440c442c20a02008000f102500700e10a0707092090b2400081500c0554006407001640c415030214698070318042d0600c003d60000f40c0d99004201c0410220343e040f0070610a0302c0742640c00200c02d80c484154003880001141c102c48120000781c09a1181c0c01056540c900c90a02c034801c820b458865005903031044e0400e108c4591074032044408046184551054080030109141c500d05000e1040302d0740d072204940c050100310010400b2014000c0702d1942480140c0d000f16080c003480030040108001d000c00344815a42545444c0c21050121340a0060444144100001c001413001c0b40c3c0340d454075084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 664420989 1250 664419739 664419751
    0x151e12060120030d06090e0114070e220b1f14030618070906110f070b031905041a13050a03080a0e01060825060c021e060313060b190e 59
    0x8801c0c00007406105100a004c0c3d40718084d0040380071420130098400703a0f0030403141700b040e9a141c2124080740701e2024040d1900410149001c20f015002a40010300380c00c44101c21001059980d03a0052000c8401e90002a81210540729098041c044488800c00c44413404406800705020f08082a1140c0a000040d54046402000c0004074060100309800300441210a40e000c1140c035503091006a400c218480340300201540244800f03401c3d8141d180d1a9151840342841000010011464940c02c102603507084000c0340204122524150174240e500d207150150701100700b00b000c400710310120307441d40002c4041d17a0808001c01e17490b401a50700303e5140400402608075a5a10180003406240078041c850042c00110014500b00300c010a01122042c0ea080c1c802e50100311080f41004510303045004030f9002501190b021501030801461001c541c8a03250006a20010000800031010b0f040d00110f040c9900941042183d18040c002f80080c03099032217001514201ca8200401071000d121071072030381c402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 664422239 1250 664420989 664421027
    0x5030313140616111b040905010204050310060e0a02070f031d10170a0522020a2607080f030f0c1615020f0a030f03020702010e151e120601 61
    0x940c08206507003803141c1518034460056a18030703004140d0381d000050351044804400a400f2952485c60030142c007035130008916000355111605001401401e50690300207100c041c06943c04106140031110082215001d0b01e07042c44007103000718010b003442d4429101180e9000c284441e40801944040e140c00010089102c004038610b100110b1507214030603450380c400741c40c4d121501082c00d082e29401c19500010500e1105070701e84820048040d4040c565070003003ca601e01e4044138a031060000c03900c81c2c1510303082100301074520440a881500c0444401c0885c050201c08c0d11003032030b2106001e94030341e0440016005554130a0040380e0700300400400410f8500403002c04c030340960880c00040d036140c1001358020741000100d808171080c0107070144019000100124090080000035070341c0070300fa40440780034010401d58040744040c1103900841d2100314a0b034005042c01d401c0303014400d0352a00340c1d02050750340389070981c004000d110130444401615000120348020000541d40c40300116070310f83e00c0d505030300042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 664423489 1250 664422239 664422263
    0x1612022209020a06050909060d0b06010c0501060306020a110d09050a0506090406090c08161704170d0e070801060501090515210405030d0605010509030d051b120a0f0c05030313 77
    0x41c1d641c090f00000400c0709484032a00d43d4207440c01c2180c0118010326490282400e1010140000c44003108181d0001c42400d1101c00150701c0e080c80c3e0300500003604018012803001650398486900140d18020100d542d40c1140c40541001c4030480d444101071207001d4200346140e0b0284a1881c01202805803407070701030000103c5070f80c2d030000c0d0310548600e030004001207500041400440303404155802d245661606006070484a502e040049401000700050b050081d54081900c048130a003003120302000000e0fa061001d20b00d590380041d103444441c414072506601c0c00c0e40004507135005030101401c4410090030031000c032504650700036055000d045103001202e080c18101a03c55a44078456014a008800840c0c0b09c44940151000700e408940243c0e051010502083c8200d0350006890380b4034111724a030041e280c54031641c0e03000c1442100c0842d81402c0c0504070355000082c01150282480e2603140d60380842c403507030410041d01c10b444150300c06481a042000004d6500000201240015101304509640 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 664424739 1250 664423489 664423493
    0x1506110c0105090310090f0209090313140d0f0b060321041e0803070309141509040911030a05240c0a080903040b1206130b06090f0a0902030106021612022209 69
    0x2200d03180341040387d04984a808150070340c180b68040301c1e030024180004600e0001ea0007515844130b4001d10483c80102c5500d00701c0011a11031603080031200d03501682e00e030220403140ca008264136004844090091044807403c1c40064624008080c0344640758010914240c1030805031024a03d41e00f20390f04881e40484000550910f0420040002c1070003980e441403018103000c0d0b414001c0d1988650345204041006541000213690303001c940500c6800c40c1d0000310079450349004014441c03a423480e141d00d03028115a00d4140840818005224615108400840d61038582c40030a40d4106945034469480d051121b2401a4000e03603074640c00c580d1040480e030030140d0314142d0001c154042d013038026418032580180105803e100e0140034071000c4101d0140042c4c8004800300c0e5050081a4030b00e40701d040441020b4807e03803140010382d0060000f002c0306554a6071150400307035840b940b048002c3c4449150300c0c00050324054402c038400384290300034605c00c0741d20803429000b03001c00e418600b03240100c0d030340d15241c00c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 664425989 1250 664424739 664424741
    0x7091d040609051c030606020303040b070c050a12110c040501030b1b04050607030e1e0619030f02030c1e03070203040603110c071502012703050f070b04061506110c0105090310 77
    0x101c2010121a9594510a000300806840c047c1c1c4c4901d055503c14010b0000060b12000c0f0075500820314642007024800604140d07180c8401d02c0341c003502d12040000f032180940e40c4801f810001040c0001240d00d049010002c1c48111003007407001410520f40d010118058483c40850401014090510203090945440c0080c2c00b0342c2c0300741d80c02c4001c514521800102e81c1000442210b01854201008100360342c0700000c21068402d038802d100b18801c00d42c0600310594000d5100f80345d0480610403c6480e81381000c000c0b46e0b154032884190105038024444581c0002c005c004403440b85a9603070196040502d404803ea01820128a507160481814820b81046910030014880244600c0540038480e40d0403c0b0068211601080b1101074480b041d965940400ea5019402c120240c1c1131038941e03030b80c0391000d11402460040e00d40c01008101740c0020300092201c7e0740c008000f689811454211002d95071a41540c00000003030721111203410641188c01070b503000b8000390032140405800d4411440200c02c90b08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 664427239 1250 664425989 664426003
    0xb01060509030717060f0708100b0c0102040803040906091401080a0f030e031c03060626040f0c240305060102100b0a0803121504110d0c030f051e07091d04060905 71
    0x10f401540071703004100e502907030b0318900c03500140e4a0a01700074904000040c1d0740142c0302030040307030f400990000303410400792003d5040fa00204140c20685e40c9581e11010f441d00a00f40c180b1071280e0a03030070031aa2407049100d2090460480b65224020300c0001482e43d10b58461141425090301030009010084034903803003d0041d00d003584070105491049501640c4050704440598000804011803404440680101146203040c404e1600000101540d15841c00d0950040182c170001d00c6c0804060001a00351500d5580000f905c004406c41e840130441003000300c0480f00708070744681c0117a1040004030400d280a600000364040d015200c10f41c040c0d124a0014916031051451300051040d00c003c01401050308081400040c00807101405841d15803c44c200781c80c0140703082155501e079a280b03144100b9020b0361100c58400780c0f081041c0018601031451811040c944100c2c00800c10101d800240d6551103880042c0a6908405581c81c00000007041c2c6a40c6040060007191140c0d600d000b02404120100704d99 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 664428489 1250 664427239 664427279
    0xb0a0908041d090601080c0d061d070815061807020c03030c030a03270305030c09031902090a14070c03052101080d0807020c12010b090109020301051203070b010605090307 75
    0x140507003041c1602e100e075007000020320020140d0807000041c400f4920100f0b10050b40d040440e1014075220040c2000e000615505515030070f042c951b03989881880130041403000c200c500007400d43e464035100c0804200105000c8890300d9200050f03c80345e5510704001842d45411092510450707100d010508086031640d44819031100b150b0788085010402268035005001145a103190700800c0901e02e0304116000301c0f41c07801c1c02808c0c85008000150814008000c0c1d03680c0340b00c01030455600c1c0d0003092034000c404004d814181e0292a4081c00549206000d014548075404108501c401c1541d8540b001c941030300003140d003101003010802c6030f101c46986642ca04001c1c07010428820010b9458804040e07d01b1601940c0081802a0281040180c07500440c4001021074159510305019043c40403603801800c5031620107900048800c0003181c40c9e41c8030b9000c1c60583c1c5e015600d0030140c1650442c0c003a41c900403c00f00600c1445000c0040c468648103a01500390860041c044540d81504c559030a0503c108090003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 664429739 1250 664428489 664428509
    0x90109090f090b0114120a05030d091716150c0c120314010f06030b120a02100e030a0309081002041a0d110304121206061e021e0105040204270b0a090804 67
    0x860103629040b8606c40c000040c2d8402810111815550540c44c2d014044502c090141d4550b2040e007403124840f0485501009111025a00d05880e0100c0552400c00700c07055507541621100707070407001443c3c401e9000e03c29a540382d514400c5010b541d00c02003942440e005104042e141c1444001c0d8080d00c0030024041c2401c103001184550400350000c080b2103808081ea44171b030342502c0850458150200c1c2100d04150140c0321002c41080c070307040c1a00c4c10041d601d603068051181c0d00302c0f04103044d80a80281d0a82e44040207646001a00620710400d0340079600441c440f0f40061008400896461301c001c00c900300141d43c02141c010310700a010829a041124103441c141070046c0442c403d40d0380104074010f490659079040050b9401d004000b070000e11100b8407840c003030380d4401d141c450140c020410580c21140515100c5000928584203902800081d1801c030300032420606110614401d80c64460421004015030507500140c90710346002e451406401d80384030f030b9502c5980e075001c100650700400c06031503200c507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 664430989 1250 664429739 664429769
    0x2160c081204060c08032d0f0601090f0e061c0f060f1b2001020a26090316060603080307170603010e03030c0702010306170606120102090109090f090b01 67
    0x1010340d0400c500c25900c505001d00400043c00410b4100d030458002d2500000311503183d594210704007003c068214402074030002180032802580d00c0c03c0c807034288120a05c9001054030b484580054465098030301540702d219040c40428080540507101190788104000e0802e80101140207104100d076200d0041640c41d2090350f403428041c402c180c0036400710b01c00075032810489403c1e130112403411440c000d000790301001120401540b0303441100d1120902da01030100215544c64100f0805000b00c3d01100d038222146a03241d548a0310058008440d03846114440c0246140100c101d82c0349000f04682c02d8104d983c01e0f620711010010402d01005180b01c0c42c1d050301c5407009218800d10741074503113000801c802d10a078100441c1054001022064070340105d00c03a8043c948440c502d03c016005011240c000558800181c080c0c2d208040001030303035500440d000e9412410512401c48403a082c1d229480c005030103d84002c20401140743c1d0760f806040c1c0d1440040d400108403420741d80b6014880d10a034080802c807a0f400d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 664432239 1250 664430989 664430999
    0x316150206090604080d050c1c0f1404080d0905070e0901051821030604200703030b18190f0c03090312020a080606070221010911010c111302160c 64
    0x20280d900700c060b40d0002d001c0e528156a40120500c6500e4a42e00303e0f5481e40080b843c2280908103031903440010303910300224400010607610050000076a0300c1c50150605031440c0d80310051866690080e80c203c0c000d1880e0018541d450400b40200f003008541500c15100d0014408103901d82d40c5021303d14410021500e8100545040c5000e500d900745aa0a84c014601003007144102e920690305e0708020300000b58503942d80030000f40c028104801b1602504040000501c181e284020050003101d120762010010b01040304180203884054001000d20001c4401c00300307200103901c03200782400c07100ba440045122400e0a481074280e8200c100e070040840d0719000d001c000c051f00f0481c98543c0c81c0203c4011030410040c00c0b401017034180007404850007000000f4903201035403112820803002c074514200082a0b0680e500040f4001c000848042d6100e0000341981d007040d40c495244081d00c690403a000c440d200203480e0802c400328464500181d0f10316800c000003c0b014501c1020382d20214001c45261801074035003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 664433489 1250 664432239 664432243
    0x51b0307050406140f0a1805061b0d1707051c0e060f090111040b0d1512151e05061305090307061109060403030f030207080d091a061e03161502 63
    0x26009042002000780503c003142e45e01c18094a400a50340e182210052000c1b031070401201c90a500084d030030000005102601c540550b10350300805c403c40c1e08480b00d0803099181180d02d030207004c146800b44204000890f000611440151204d10103072108840a104000c0d846070480c0d25642400b081074000b4030030415860315041a4685c40300c02d40009001c105a420120f4645209600907100c0407007000c544c0003200061980300100b084400007100d40425241d9911900100c1d514608480d40813200c491035050701841d010708440d200d903d031111000914260809030140c01c0050400346c01c8500c508050141c0007542c081c06020310f0b9000041e55030742145007032410a5030000d24280c400c00104100036515a02c03540102d804583d014500350a807001c034800100e000e4418000d015210b02c20114481c50407104941c00000340c01d07c5500b518601d070f540810100020102182c02c10340c0680c03614241c403080340700309941ca603003514020180c0e103891204414003644844190403d1007030741e02e05500220b041c2c3d01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 664434739 1250 664433489 664433507
    0x8180a03320d0c0f0804260c010c0312090b2d04020d2603090c04060e09070306020c0705030f0d0315080601062118020406090606080a051b0307050406 66
    0x6186500103540001d910490742d5942d42c01501c50420048450403000d01c405220b101c80a10380c410b010a680c2da0b0341e1462a4841c0c952610a0729055480c07024402e02518001402041580c0c10b0f120b0b0418240705481c142d541b0f2100c012031a0583d41c0b02c0b840c11000940000c1d8241c410307440c80c1010007404291a014540c8031040c240d4984099200c4024003001d039640b820615900c070740c00001043c0b1038500040c081c0074124680414800302c0d002100784003030b01a001c181c20740041c40981c1c041181c59958101d11300c2100c003d42d44040103410294007840410300355001840c1200484003111103040c0d17580c010a01e4540842841c0c2d40a410074125654115414000c4525600d0034200b05806903007020301450304c0e100c043c0300b44002c0c001e003614035550074800010510385120035808108a01e11304200500403901c000ca1089100e240340100224030f440184c071910080c1c9030b0941d2030400176135650540500810010301803032000c0f0b05090703551485040c03d400451085440f43e8a00d0340311440c03c4005005558 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 664435989 1250 664434739 664434803
    0x3161a0f07120914090f0a0212091506092203050f0a0305150f03100e1c05090a0b030106090b07050f0337120f09020a0906030b130c0308180a03 63
    0x600084d4001e41c3c3d81e68485141d400c40800304014145456460189000f4440c1d0840e85480680c1d400030800c06c004007083e8012040781c2d5100313509440c0d481408020100e001101c0b0314100c4044044031092004000000d04440e501c0b0b400e186140005049001180b9000020740000081d120740401c82c0d0a03c0d0b44543c0386a80f00306440c8040c0c1c004100740001e4659102005002d101c584c0d0351507802d92810200000c2c80110031303102291a04085000e00101f09500c4009494022030301103000092100d030300000c40e4101c0e01165500380d007035401d001d98000f090784214401c0c0c41a104503034111841d06010f00080525403406040c4072145e245154041e10b4a0382c45981042082060880300004250031001000020f041c00d140000d003042032040c05c02c02007031711040180d00466100d0780422002e405600c5401640c0c001c0c0c0032804141c4c1c2d41c01e0702070b045c0c0412400040107000555420800200352201030202c1c1c2d0500300f00c58644002c88008140c2103401c40e40240e4074942ca5030b40711003070528249080c2080301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 664437239 1250 664435989 664436009
    0x109021b010903050f0315040207030806190e011724010302010f030b0310020706150b09010e151e0c010f1a191a040308160605010503161a0f071209 65
    0xb1540381ca02825601403a0300000942d40d0000018a44803500d503a0400f40d80c10040c400c43d1120070740c0c1002000400d080750303954003895070b120310790390010040214241194103014a0904a80c28181007003009000c1007081d454522885e80c95180700c40c619410f031690104046000e000961440c00018500c01014040c007060500e03000e040e011549000c12181602c0000c07990259860203503140000080501c9030b14507039900c038040d0340487c011b101940202500c040036a5200c10052540040090030b62402c412401e4066003003083c1c0d68164420007540021140070031a01d130409001d0082d403802d46192a01e1501d10542d118807080c04000c004404103000c40080e2025414016000000f00880119014040c0e107121403202c0e8407041c14001c012139001c0e40c1d0003103e0035200c8610b403210907089e142c00b00c01241c9141c01c02c4000f188a050004001f102c100d00300d504003c040b460010240c041e4031284200c0c42050307070104450400800b4071070043c02103910031039023841c4203040100002c01c42c5006030030144c910 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 664438489 1250 664437239 664437251
    0x5040302070b270a050306040507060305061903020d061404080d0f1a040b04062d0501020a1a0604180f0501141003081309050c0a0327120210050109021b01 68
    0x390010248403800840c0c5a864030f0040c10380c800000e0700000d85a2005030305208040400c0f042103004035503803084600c0341c2c6051229071202c83c20819040280c240041102c0d846040400246c17a04001c4c414135a800382200048151151610004c2c9440c111740984190400250000ca41c2e02d0300d102d240c50b40c02015038200000d2070b21a00110400042126507840f46071154500646036846500c40300040a8044511000b102800310380a5002c40c203101c0b00724001580c0c6000103041d400402e85e8641268040a81c8012241d24500c500c0310001c064102c0e5003041c2c0d91a01c40006100200551424034080c1028442e0103c02d441e040f425518079004080b00582c0080070b0061f1104006040d400340d03980198035a40f0380d450160b004594500c1c690064609a003410305220310703840a84010001c20303109036014002d000c0da08030f080201005c1101822500008091040c0104840000040c0c0000242c03040d140500c20882240041e24420303004816001c2d0300240f40002d82e18980c0d101409690340600034092 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 664439739 1250 664438489 664438507
    0x1f0c0c1e0e060109030b16110d09091407080c0309010b220f0c0e060d1121090604030903121e09051c021806130c02010204030c122f120105040302070b 66
    0x70082d07c1440009200d070514595a0302501803280c0943d00041201d2000580090040081c2003030b2048020091030010b205100881000c0040d00c1400c250b1651106030b1544d860141340356000030261101550ba4841261550b50741c810140c00410041c921507040c000d03011705d14400c980d003004a0244540c900200c4d041d034150402c54090080340b003140c589846a036040e4481e03029006100c0062241d45000501d5400c59281078007480c9005000e01007400c0551303c8091465407200d060b50044c003c160f41040410014004241d9020b940b0583d18014164030310707410449100b0040032058001040c10048140541d0400102c00c083ea141d0b018100450304640c1d4011030072040d410080c2d4185500c21000003049611030130540a00d00c011a8020040900c010000074001e41080c04210380011901c040010843c0b120b440d12290b00b03801c0007180c2d506c0c19941001482441c000c17690380e040d04580d08002001c980e6400c5030142c50300c0700c84c030002c1000d1400e403800a044c54403d0f00020110320040c484080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 664440989 1250 664439739 664439753
    0x1080d080705030a0609090503030a2d020a050408062701020702091314070303090e01270e0c04090809090c1c0c140a0302181f0c0c1e0e06010903 64
    0x1d0000501c1c10042d9503500c0303e210304800340015400c6002d4860522011360108003000008502c103480d803c004010345a1200d1800c0c02e0088600500c0e0003030610680082c03007841325035000f01000c00080c18028641035444401c28140306c011a00c48800110000d810000081e400e041007020840d150000c501d82041070b0f000138500b078000b0300380303c845403050308071102003180381450b05d0010f01c03448040b1240e155917860010420710305400780c246079990301000002c0c0c408806c24100705003c21442070f070480c460030340c06c1d0100030072002c0d4101c14544500c21203400c0a45503031041c0c80d102c0d4054a0550307030f601e1190080c0002c01e0405400c04406d02d4041004d07040d4030414200340070541201d01000709500c1000700c07040b00c040c54a0072024031443c000056521000b0781640c01042c22001003010200408420010405005446c1c4070011080007400030310040c0c07510840318407018034480c0320914a0716864082440101c4080c80006444499401c011302154450100b680e520210034600740b01030a0540c0e940c41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 664442239 1250 664440989 664440991
    0x50708041a0c0a0e040207050703080d0b0405070903062d0b04141e0411150702042d0e070306020a0c020102060a09110411090d110f1e09071704051501080d08 69
    0x1401c00031200b060324413941e42c85e01156030050300720046558182d107034105105554040d40048850a01d0b002200ca181d041501580d44605c1494444220141c03554031544050140c000e0440d44414039103002a034450f240d259840100483c1400008141c0002c4051100300c070100e418240003084040c0c20480d201c084503a5600720700f4081440441240c81d40d1410301c448903920048503510880c1c018889019100c444041c0000c0e600841c1c0030700045244900c1c0546441c0000048440d400d015000001e000c0c8140d04441c4840c50b20b98202c407092030307a030b440c0c1c40b08982000a40400003450320403903106542c1d040000d40d41000c90180c04000c9800c4503540e0f030f0b05100ba840d011a0140740c84000840c0c030282c0f81c900351101c100d0050701c8c40c1d101c0d40e9a40b03800303005016132501e550310800701710341c0ca15000c0c03c00c0414004210740031000308807030040b18001c002150000611000401483c1e001003411007c04450713271405a0302c070f10000d0608100140c00d4040e0220b0507002441581d000326884460103a001e032040e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 664443489 1250 664442239 664442257
    0x709060806031c0c2a0909200a030209010305030c0f06070512070c2108130302070515130902040f15120c120903020318010e0d1113050708041a0c 64
    0x409418000719041d608860051400752030f17490100018802c0d400f0030480e0100e4025224030f404680e684541091088880d940030152000c101c0d44032030a0541c102150040b41018010615800c842d500d030300041d0091000d820031109504003040b444605c07441009104848501103004d454580b5003103400614038010080342100e8040c850011a040c170b80034155a480d11a089030003441c0200200318104102080543c0c80800500d4142c00100030205040b010303a400b13a81540504485450b040400404418070341d01400c01020030890812002243c590b59401084c5000015884601e0318100404c1c40c292a0700809100700740742c450302d00385507000d480e18040103400e0f0400500102001008c48500300740c14010003907035141507a89010305030000701400b012194031140c2c180c640c0228004590480003400c49a400c0000c3c4802c04001030b848460821840c0406411048507841c0f0300c81c203c003a00c5082d00c0800100d18680144010710401000c1003030482180d000124607402e10710010507040c825103000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 664444739 1250 664443489 664443523
    0x3030a0c0509040501091e0c0c0b19090308090c0a03020904080d0605100c02150403053313021009060f1d060409240b0304030c05030c0f0303070906080603 68
    0x2030320141030240080e1540d442010b0703c204180d68482c80481d0040c10003240025520150003244030185625004440b0340d2012561012205030f11a40c13410440d000181c03020181c864042039a14001c44e00b0710a640c0c4a9020341d803000d60034249580300310304000f00300d03552034000d611350b02d401c0c400740e203950004a0b002584905031550b0707210384840b8030006003042d4000760f42c000109844000042d0340709502d0980d003030080710b001c0c203c6c1c140e41c120300d0300c6440b440c48004c0058018140f0703821800800301d0013040c0b8400070003c0d4410744107403520001e00721074103c442c01581408103c0c02c80950400d10303501c03050f00c010381c20003d00580c00c26802808024004c0681c404101c01c00500703090030000b403600c40d0b915000140c14280c88a840b8165a07000d40384c582000c004805000003500030b046010581001294030003400a450b6071620345003164114030891050310700d4072041180840c2c582c001c000c07005800c410103020b035880b401c007031748014541c1002e40c1c001d20070000300c00c040c0005590081440c0e40c00280d0110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 664445989 1250 664444739 664444751
    0x30403021e160806070905091003110102240a0c020303090a0b0903070f2a0308070609080421020102240105060307030e0303091f050f0708100f0305010f1d03030a 71
    0x34149410b500d1441c02c0300c0400d200744002920000007510600840c216260900c11544034400c1c0450007604035004141d02401d80c01c10404070f940e102641144043c180706071002200c10554102e5500040260b40d0401c108003000c003c0a840caa119044083c030300303407000d58075504107c0d000720b03034641803260040d02c29201c82020982d00c90b0100202c5400a50100032405090000e081c01100070782181d0f00d851001034240b01420f481c45e0300d2041d010035030780e002d0003d81c105003480d180d840040c4445c400844507501c0410020404565a01d5160740781c1c088a607000b0400302e0f01d44002818a1140b641420001445841308000070040800007415180300b40e50030344e101c2c0d640303078011005080039490000c0540000010322203803405c04071f07804014802c4020301000648203c014a0202c4404a40d018a20341d002008207811501c01c14480c1c0d000120142c0305415030b52200340c0a190b515503503200312116076450110380d4941172a0f001f0707940e0360226445804040380302d0b103404a03120b2100410100101d56581 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 664447239 1250 664445989 664446043
    0xf01020c031207060507080402030d1202070839030702060705030f0705070608010f1518150201060f0902090d0206071401110a18060905010c0c081204050a0b03040302 73
    0x30850158000030129402d11010794030608070756000c0601503d03210300744000503c417940140c01941c01250702500403d207280f0340390001c94402c4030030001e98003c00c0d0200b090714046210a40900440d100c4010a00350000782072200242c00c40c90805e112801800034070380602d88041c0403064036542038040c0d8255070380d0f480d0751505030300b1885403c0100320103100108010f01485030029540040d81c031552a1224540d80329a0303880c01c80740301441221108036423100e5011a0314810034990810402c440e038100099521003140072011249243c0c03c1006179500d0400300108145108010003e141c880700841c40c240031003000c120804030b00840a40902000100d01c420403000030342140001422000130026001d81c8000e0750070b6a4494084100042c201c5880000c0c02401240b00307004032081c5032203a1028a14020040d00c00d040511000c0d1081440e4080028481d0001e22502c0d480c00560300c40590350301c1c2044108410f2440c3e41e040204441018070030480080e40011b03400554003002d007410301c0b0f1088a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 664448489 1250 664447239 664447243
    0x90b01090b0705070e13020a090b0303070212010f1802030a020d0215030114040b19210503040f21080405040207080d02270111121809041a0714090f0102 67
    0x540c4054041c9078006064014440d0118000b0259580d20020074a02d4440d0381d01d001802e0300f40310000e94490511107007040311040301d44c840c10300718202078103403401c060071a00010b21121103142c504400365195102071002c28154890700b003084080c1c15007502409043d4021030759070410000c0003030080107007450310015540c40900c4103482c3c041d59860183d5030341c2c440c9549101e041c1800d120a00890070030b1403505d01c40c600600f0000030401c0140000c10300c54a030035141c80142d800000081030740b003154001e54002c184140010b1024001281d0411465450611030800703131401341c1100c02100c1d422540d004001101c3e0411602116012580540c9450407402c10a01921850014411092000940c1e00c011001103800c1d888a03044e0402904c404101d40e001940c1c42854944015007913000030f0b28030f004a09020b0041d002418080003164001e54184000c507a004409440c180e400354403211003000880e801942c101d900c0030b80d0b403404003c58941c0aa004010340610b015207407055000c0138945007a40d1003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 664449739 1250 664448489 664448507
    0x5070915050d080c01180203100b0609030f010b0a0828080f041214010e07030f0c08011503050d09050f040b13050114090108240703090b0106080f091204090b01 70
    0xc0203001d241c2c9102e01e807400d60190380c02044002259428018021408120365890058603900900540b0780440303010b500340014940c0110107036201c441404041241c0e281000402d04218020000040380a001350402802c001d07030360700100160b0320003d8040c01d1074090002c910089d10520007a4000347c052403911804500400400808002c5c02040c0015134421000701c054500f07002d80121000740e4070a038103080c20313280d4a8207061700f6070f80b10607820000101808405a41a4041c0c407071001800c0d16040403509503290401c002142142a14051090000034002c0030180c0c41d071400c0c07168a041ca020003068a50000000c0c181c030a5945404446c2203846000314151a988501400c005070340e119081d42039401d074000441030142c000c2c1d00004c030341000c0000d06400c2d854404d1200e01d84806c0e800440c010740c008001e0001c401c041c0c81c1e59105001504804445001c0d04054440300c90700c0c60300d9810300ca80140014148421a400329240c01c0d041c0004404407019556455000b05140500e0001602e003424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 664450989 1250 664449739 664449749
    0x13140c1308191721070f0201091e030c0606060503010608090313170109060c08010f0504150323010504032616080c2a0706080408040b07020409021f02160305070915 72
    0x40c2d080c24400040780c04c5a04d243c8680000d07120802e01c6103412030101d08031202d1220080200e003160364a213000c6007000e440d48110324880e15109100c80f01c2d950b180b0081d40c4c0558403070300215801100510400d60001c07812070340002c50b00b0086043c0111036503003800401c1d281c403c007103003012864180f200004003034104070300c41038010409000322012070000800c0400d0901c01d4240d000c0f518600421945803a0040c0d44040709640c1640648030304548030034400310003614450300c1140100489090b401028010039208a0003a203c1246200f4885101c22014090011002c0701c03040010403c881d100b14131049909204031803819661950390101c825020748034111003c06000c01d0740c6002d0303409024940b141448000d0a00070b0b90501c5580307010a440c2e03c2809d48000340791a40034041408510411800707442c05500051000c1407840058020501c03003a030700b0490181010040c40030300d080d15010800c0007000041c81c19000d54080c0b43d92151511040c1501960f540161104510000042181c1a00740585 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 664452239 1250 664450989 664451017
    0xb07170d0f020310031203290d140606040b06040e040b100f0e1806010b0712031407030f0b03060c121302100504030c060201110913140c13081917 64
    0x41010400c44c0c00303107070b66440200e400c1c141c803240031502244680140e05541a003003003c40f40c44000000c40c550454071140d551600151201602008502920b007d04103511120000d030030725091020900c02030360303840c90015001341d108210030005408035015030780d44560008240320050703c40c0d5080c0e01034203005038440c950001c40f560010840c202800105400b5a41c5005003110301c821150f1025203802d000d100b124000e100c24418040441c0c98120f482d0240c018030310300002c1000d9100e05188100c00d0541d6000300180c1e0fa0031440503880518481c0244010048008100900c2e28480381d800358496030441615641404001c203110300d4000d0b8141008581c014454526443c0680b0020265045807109582d0040401c1001030914010301c030343c1c044810700451503840e04008409220005c00500c0b10032900513603d01d075442141c1c444070025401602004038295039501c000080b00010611500104601c1d0803080c0c560700d1100401c01c01d0352407150f100c18001402c40c01104d09080f98091140000002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 664453489 1250 664452239 664452241
    0xc08030f0408011b02070605070503040e0f16020a0203211b0102030924070309140a060606020d0203040b030609040312092904030903060e01061a130b07170d0f0203 72
    0x8903080009001618903400c0204120040b540d07091140a015240c440f025810000307091214911450007864410f0091f02142e10701603a6414554500c04100c43d1048290100d000340310fa15040820b500002c0b0360540300400c2e8403009034002989030708038507011030311088410f00e06409401004054800c0c0c24070403050600155038a000441c041d40c4120f58207030b8280a0700b0302001000305130300003048142a803043c0040d4180e4a42a06400030602c1c1d58045c0c0e00c118217000c690121807820040c110105204d01310102c0c2891600c0c101030b14200c140c0000f802950010312060002950000a07254003160031650454a80c64a040655550444110f80f241c174034200502c220501c036403210b011a900650102c1400710740f03101b2001e102c0d07054080d00d0060006222500c1040402d101c0e0704562281e040c04000010541d6a5801b0250817101d080703110b9980b0100441e070404040100c41e0028010180035984515007207003661014071021100e1050454030602040e08801710b100c0394041c4c002c0c011012011581d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 664454739 1250 664453489 664453507
    0x203010e03180a06050a0c15240906140f010c050d030504120c03020d030b030f03070308010e0609012601090c08010209100e0307060c080c0d09090b0607020d030503040c0803 76
    0xa90340180560740c144000002e4071070071414102100b80464406643d81402c0c0300b4a900304039000304110304150381e10140b00300e81b0426006a80314116000c2a003c00880e03000b040180102e103203448075800b00c03c3c1c8a103840010001d0708084180c142c0c1d55007045030440c20600355600103071040c1103690409040c512518000569071a0503078002c0340681d00548104151020883d01220503110303110000b00140c1002e10381240b2140281c00103400c1c0c0d407009044d150000303200b007a190314607081994180d000900580040258030300740840a07403c03e0040d42c41c840250306100c1070747c2512412491440002c3c00c00410301c00010403e5100280b015406801c5488083e61049258040e40000347d2852103400d64401140c0c00c98003a01e00340403101c00c084c0140040c0c1e03140040544c0d50300700780c0c00c1c01d861903001000381a404440a018850702140b041d260721650324240341d02d80c01190b01e080c42481c045d0404129100150f41c4103134642d410250700d0318007290740b59542e10304445856911f9100070014800810480a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 664455989 1250 664454739 664454743
    0x12030d0c09060905030a0c031401060e0a140105030f0c06030a060806190f0b0f041119170f090325020411030a0c0309080d11130e1803030915130203010e 67
    0x4a803840e54941201d0f82d1107000f0541c990660200c001c044008a60081002030140e5024260030f16403100001b413103d0345c403c0940c550000c115155228681d6a40310303095140f4082c0071940c05003000380c0051001800210b951655030140640f494810354000c0002001c0e16a180c00a0003c1c00f03640050318510706040c49411204540805080d00b0740341408040c4079600b4a510504a00f41001000440c2c41c40010040c0002000c8107400301107015020081122120340d96121130401d41180d80d242424052680d030f0b10405280003500c00b84c186d403080c109001050000105a42031070500d200ca032840c24060b0508614805040d4100030740282c2071840c90001d041502000d0352080300c985009111001200c00214111010072000074038a403030a010270501c0055650091060740d004900342d80c0b0b40466030440c0c1c02c0f0f0110b01d80c0440c4d9506140c1c4100130062400c00142021070784030500850035030524541258980420100000f040c0340000c000400505002c00000c82203038000c1c0c0200700c0b40f010883c400c0d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 664457239 1250 664455989 664456007
    0x2121605040c0203030708010317041a13080d0e01030b12060f07081f0b03040807020901080f07050405070c030804050c0402070615080d0507032d020d02010c180512030d0c 75
    0x35216902c0e203054070001c1400403045a20800099444131034507821540d4001840c2d094a44d80c90595806200114110300751440004031f03040e0300d101d900c1d1145241c082c0410011a5500801c409800268481c491075401a401201014003401c000c510301000501192200101c400c10040b01e220b00020b004004000f10010380c054a8141d6809003503580b802c106135104000540b0003d114041010204201113000004d95080b5204400492038100d00d03400146900b0401e81150800b9040308403608903800c01041448018034050344c013400186800ca0001c0c01220380044003406001800300040c1c10400240156042c0780c100400440d107403219828450000d00c10a00140201d494099000c5000040083c2c0148124280d5035114600192a078040354071046a0385441850703211400048200e00c0c02c031400201030051b940c01031000044195009083d94007000e8003406003c404c850644416206c00c0b055029988195101240e01d054117240d03600d98800c0c003001c0a0041d280032141000341d58050741c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 664458489 1250 664457239 664457249
    0xa02160602030a0e01050c0a030509071205030a18030812070c0818040b06040b190e2106060109180c0203120f0f10180e0319020706270b07021216 64
    0x10450382c3d904c04152822a8420754550002580900950101d144039070081607001078104c007651449661583d1440e184001f40e2001c13030b01604003252001806600c418031400320701441c400b00800c00c0c0340d40c0f101100d81c450700c6090302c1d090151000107200b2500500011070160352110456070f036205410b404400e2000c190081603c1035091100d005058070f0008241e509540b0303131480d860314000d00d43c0d903415284034469600005001800074030300250b5407044400c1282c0342070910005c100c000302d40c0c8820306150000705050306102e0100030500c40028001c61480001d03122090004003003104040c240d00c1c0d0f0140302d4404550b81c18440c1000031035041440241d001d400c00d0004042c2d103440340c41742c0402c0c1c000d40f802040d41043c0d40c4000904400465040120301801c090305580c54090214082143c119181c01a0760250784544010010307540d008150208104010340c4601e95040189a0034203000c0c00f46c401c42d0094203003c14501c06540d10343c40110f032450481012120b02c20078945400740e4403040740c070038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 664459739 1250 664458489 664458491
    0xc030b090c0301140705070c030812040c170c010e0105070f061a0102060c03041101050405031b09371b02250302091611030c01020c070522050a02160602030a 69
    0x700d901820140a46000509440c110080940e5502000c40341c98019550640d83c2a001103000008134030380e20000c0182c5001900c040c0914940f5083c503540d10301d00c0da40070409286096203030512071100854078428074082441c1080d00c00102c880102e07168021450f0151075880030080800c10807441b5404031807900701000d02d001542c03860500580e00d40d2001c65880841c00c1042001500241000100c2c001041c0c0c1410400d0520743c441c0c0219240c0307116002c40b05192580222030414074503000e0041c1c1d5000031400e1549184204403e2942c01e00200501c1d80350032244403031030802246500d50018000c210313421b1a0012601c100150013940e88108840c3e50780c045560112102003060b00e40003000640c1d03006004c404050704d801003244548108034220b1020408003180e01d0314100d206000620300110000009602c555a040413542450110b90020b0301c2031102c403981d0761f42d0b180c03d221138034002a4018800a6030342d80ba880c0400203489061020028106000c0400b4100405540a0743c0200d480c0c142c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 664460989 1250 664459739 664459753
    0xf0b04060609050a030f08070807060c08182802030a03121a0f061b060109060e0105030319081305071d090105062209020d030c02130c1209050a0c030b09 67
    0x590b8040c03464000c540d0440c4001d4014408190407010400303425100d462040e141040603100c4801c90b803c11542283c0858450741d820005550250134a80c11100c100c0c1c0249514001e04e000e25584c1c1502d90039010388044030030810000c0d4a0104003010025005410b42d0f600d440da5140041ca2032607040c1071286070340e140020415424651000380d04800030040e00d83c02c07034400c0352000c001854000404e041e0f0b81d564055105802c1c8242400b03190300a1100c1c120209000741004800895076030140c00240c0240c0c001d0054006060740100090f030f0724545d034200707180c15854944e00d20b0903441d4100030142941c0b003004800654489c000001800c0b1482d07001400c0d146483d00d0a07482d0981d0001d41d0302c5a404500540c50700043c02c1030f0682426004500003000038111000c0d03020546051070160241c01080d81d803a03800e802d50030729601242800514003030400c82c001d001d070380180032450030302810300c10140c4c6c0c1e00000080220800060213403d070040d603540c4000382d1f2860490080d10003150484042d0040c5d41c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 664462239 1250 664460989 664460999
    0x30e060f0415050103080414240c0d050c0c1507060204030308010501120e0a02012604080d0e15011e170f10060305030414061204062c03031906090f0b0406 68
    0x3100d40f40c1a242c2c040000b900d82850510038010a00b4116509a4421300740004010031442d0350100403d180c1400c7c4150351244040b80c1c8242c2460000b201d0b80c1c0500c4020401c6000180c1c3c0451403140d420003c0b40c0c1407a03482c4509500001c0b0b070044e0072004164910018000c014180c01801141c104c8170242d0703408411a15118624040e9402c40351100c00942c0417404607401503001d200301d034800349050350905054400034440070740011400d036802d0320f003401d0004058440160600a41c1101c042241c02070040656058120303181450500c20344901c540045403103610951007000d0140145485207460b40014907041a80303841e0242040c0c10402ea202d10408104404820b0140700101c3e500813016508291a01c0c000040c848081000705910080401c91040b203441d40701e0740c00e07015038080d480008409000e10645040420581c0c241404030301c0c50361054074840e030008112980103c0362000e007903000884094200141416400400c6614207100b0100d0548040368004070301d81c801110240006503444e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 664463489 1250 664462239 664462241
    0x503090606180f0613090305090315040503040e040f0605010303030b03060619060e0607210e091b07150c2c0907050a300c0e010206070f030e060f0415 66
    0x15a4003180c02c9080c81000400031014062003982c000c1d0301421070f000201c034040c41c410881e0180d09089000c1400443c41c2140c1d41002c2100601c03240c22800103c155083c50f855039a520300891240c80d100440c01c1c2c002500b04551408004410755200c0b00a00541d40c403483d025000d400744070500c0b400f030f00c43c04000032913030724100702100c7c15507a10b0070350b1106007810240c00300c0700450304961a5070022810001d21000034109100300800c44800c443c941203268205000824410002c414144a40819400d0111a016948450020100b1180a00d9440282e80307400080d100b44011320342c00180c90030246021480d0444808000c00c000e101100840b140b41c040341a45240703a40003d07a400010410010b000107024100400c0c8400c1d49040c2600781010b0030041c4410003031101c0c440801044c81e00000103200d142ea00032b11000040c0707410030702d01210703203480000c3d912200142180d04206580038602e1140d40240c2c44440c192500c80152200762400091207140030506540480e05090180c498400c1c0da022 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 664464739 1250 664463489 664463509
    0xe1c060f06050f0f0a060f0c0f080903120906121f03120f1b231006030c050301090302100b13050a050f06031b01121803020f0106051e060a02011b0503090606 69
    0x100600015517507041030000c07103503c0002041002800045d00c0d0b02408160f00d00040400030748580001680c400c0120149400c0c00156080d108211906100000040d9115000e96000e041d0345a0780890039651490107809000308102c4041e01195030803000b1040c03003c084142801d03008a61905110034402d600304445203040d928402001c2840800c081e03000a0b00d0b1484070320500c5010aa0110141c901c50080307050400003e2001c8001c1c0c0c2d500383c02c20800075040400700003000b00701c00801640d0080d0710081c1d00c0e403c41804a0010b50740c4d41c101207240d0b54540340c0710307545c17101241020484c81c03500c48403d40c01003100b5120208514182e100140051400003860700540e000d84500c051042c03212801521030610215a081cbd4150300c80111610311a200780218050300d02030380c02040400c82c8100c4880c210f0302290012070061148020840314003e44040c000000300003950b8613551105100340407801840d10802520800546d9012020001c0d4000040d6008204000507641d042e19440308101c80921 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 664465989 1250 664464739 664464769
    0x3061e0614030c060912030d05090c010804030e1909111e03100b0307021c0c0b10120201120f1107060e010b010819060b0a02010c03060f05010e1c060f06050f 69
    0x4811144243c140c1400d0000d4201a0300c081c201c6100032015104071402c58021901001c030b8a0f64810411822103020880c85003103600c00e01f014069400c054500a2030441d042c1000381c0521101100149070301e0342441207400800994104000256402c0012041503108544580307000c0c2e041e01da55640d03581444100c0740550343c0c0500740e550741031904d040001c1d20340008144c601580141c07400b42801c02007800440ca10b10010360388042800a007032406460a0708081c0c0a01500c9006040a02413101c0c1d802180b00010340908010407034140e42c801c007001a1114002d030517006400c0092542605d4110805010550320448050180141000394035080301d80201100340014101008200c1c0442843c4841e851000b11242c007007080d0303894002d1030485601080e14200141c1d5508007504080354140310340805410b00c107102811451400000a1450310300120441c4104890341032848035841d40c401015600e5031143c0284002c45080c4003440c0207101d1445443e0145038241c4038266245132580280d0b541d00d03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 664467239 1250 664465989 664465993
    0xf13150806060a0e061c0c0303031b0f0e211506150f04031707021203030703150e0402010f020f07082b09141818010606180b090a03061e061403 63
    0xe59190301b000640100c0000a0341c45030594444540130840040da03c1014500a480105414514081c00301ca80034441c0a14030070000300003c003c02071a44910140c00d10390084402c0840c28800f00c07044140c4440ea4403030b503902c42c41002d20840118040b041c5031707841208100c0c0e11001014213210b1000c00d9102c2da01d124274280c541000700340001031845066503046030034080034500b001c0c42da0703010506e600292119002e1991022040107002a07050007884200e0403241034110040c0e240c81100c1c0c4d88510090802814010f4400b8240b036050320030041590105003c0341100c0f6003c0e030b28070003107442d0780c5401c541c000d170740e110250400c880031030b08a441c0801146595502405918081240c0750741524040d2140e803007126081a84025070385400e03424080d03085140626000c5030940c00d918211a09a848a0306210842d02c418115003070b80c242c00b000304e03410070003980d0b039030580e000004079aa00d09410050560340b4180800e0b0315101122110240c046085408200e41511038010201c43e10610345516450713 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 664468489 1250 664467239 664467241
    0x307080a08040309150305040b0130050a0b010b0408210304061109060406080f070f021002130b030c0a080a0b0d02060c010f020c1006230f13150806060a0e 68
    0x3181c8600031865115009181060065465420b05800f0014100c0f4420010b5115410f110500080000490052440f0414888080000f0082c4010042c95441d8000502c03640440c180920206000302440580c8c402802e4003e50784071140c00d900c54019002d044201c0c400c0b40c0c28035240301c0c080148111100c01c03441e510b90940c4d4a550f542c1000e0030a18480d80d080d01c1d401c0c004d00c01e080d01c030350700031b070001e0100360320b45403c54034005400e483c40c0f0710020480c07030402982c201c50904958004c14035032802816400e01503038403136508201200400396a4890b00d4541000020401d81c8061030000c1c24a030403e5030b680390415210a4119810f603400419042c1e0302042103041000145000e000402c1c40030200800410704400e981e030058101d030442071844005400045a00f00100070034401c1c031000d0700342d8241d019032801101002440300c54004071031501075410305c0c0c81020150b84080c41d22000d0058000240300c0705d2804080b40090340d940344121b840603c201070208609241a00a21095840c1201503142c6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 664469739 1250 664468489 664468507
    0x10f021206060319020316170f070804110a090903020c030610181d0109120f0504090504080714030406030e2b0c060e0303160507150c120e0f0708030708 67
    0x1c6a00141c0001110000076110b640e056a15001840c8907d03884020948000b4003c100030384417041e5000311180480c01c400c100008100e2203a5040d40101d40351520348516910380c0b0300380410200704121182d000c440c0503400201342107160418182c06110784d00395507400c081e0304180350395224103880d100d4408500a4051150b07070400940d007000c40344940804503250342c4959180c2188420003089400c0da035100e003000c8040c0700000f20044400c212034605415810b904060041450180e8000c07440b0482d20346010400340821181a601c50542118500d014106040c6955030f80e075100748a110080303030811007141e201e40030200d00d807241114181e4100403004c02e5112008000e0b000d00c4010801d105c0596800804aaa1482103002c12a40f0000569036424940c6450f01c080d00f810701c2010400c00104022400501241106540100c1d20540452071990980058464035a000300140c0e415140c071080c0e1030040c10004110080f40141420f60300c0c010780f44d4807582d031a88205140a014005c0070480445 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 664470989 1250 664469739 664469749
    0x30c07171c0e010b0a031112031201051522090e03180405041b03032736021c0501050607020102280f0308070810060c02060706180311010f021206 64
    0x940c1d1101032000045030006000000c16440013a00181c4028110742c181f030220381024820101150340c400001e505040380b41420304e00c400d105020b414003515103201c9182d00e042c020426922030b41540c0c08210283c0364110311401000c1c02a01c1912501410080c1005503004c000c002c0313403a02c020784030303441141580ba0760900000d44406041266001c00d4810204c01824280b4881c4014621075907400c6502285c0c0120001d042003480781a0342e1500b5444010003542d100c2d131030003004480750641c1c07101a07000524800c1c0000007075041049040b50000400140c1100c0064881d001003c1c03400b030800c40303a41c171081480f0090140a800902691012054940340070103200c141041d101d043c0780250024055950f211001c150f9401c0450110343c03031005000f4031540180003d50300c042110016400c02e460114020800700c0c5980010b03019420008006c4140010b9401050b00b0720080c020b0384080400900c0d00800f00c0410005000c2994a0328102004400c0e990080301d550241000590341da90312043c08105d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 664472239 1250 664470989 664471001
    0x1b030705040605071104110a020c03010b010804061d03030a09060f05040b0112051c0f0206070e061b07050a0e010f0603050606070204110702090103030905010e010801033302030c07171c 81
    0x16070302605c0608080c41c955618001c1c03001070b2400e14445070711042c0c81c440107403600519266032071007039060a0b5404446d90b40030b0742c0140e02a400001c081b41c4040b4251083e500400300c5203442200e400000100701941807650040d44006105040402c610b848000894044035030980d00148440060401009005078030f11451810030302030401d440001c1c01d40c40603000c8001e030540c04500859400f400f80d0014a8042c04440c2e8800c045e0b060103007099012074001440b074402e0000280300c1c10030380007d90040f24070800510000e49006405074441d5a02d640c62407032030304400d11840340c81c00d00701c0901145552190207141e001d401b01914040c10018a5420030002e0507074509100c3d11040c0601840d00035030349034840755000b50300035183c0c00c030f105080400040420508080c1d503410710914100420000c1d02901d11238004070014000304401001180550924110b05d00c0300d40c0c2c00d136001209000010300004010720a451240c00d0410030562141d6544445018a0160001c44a400c0b81300081d103084035000f03a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 664473489 1250 664472239 664472243
    0xd170306030706021917040803070c0906121110020f03030405010609110c120307032a0f05092404080610060e0d030e0108041115190201141306090605010e1b03070504060507 76
    0x1b841c207054940c0740003803458001c500c1c00c0d1840801510304000c0d4156505c24040640701500c0071141e0203c143e101d5002c04403d81c10028001da80700c030690746520f4800c0c04142041c40d0020141c95581c1001d0800c0e602a203181c0c0914824035142c040010250743d04003040fa0518102200544600f0119010811164100826010a1549440400e1005100320102e44c0120300c80c0ba0075019010008840200030364060700380c030024800100105000b965501d02004950006040c03202c0014401c03000b000024016903005c032901e1f1181c01c09104050301079041c9201603480301c0c2c0d41d11260014a400b00140072500d207001a0101d50001d4100aa03540b16030720041e0f02c1030290b408101011030140101d01c40390110854002d90b840f000c00c441094038844000014000701c00d00c02880207105401205012513009000320071202440000d4000304402d0fa0000030b5090741049040150b50303910307032400f50b002504a45009100300074000440600d030995003034074050061941d480c2c0c00c2a081150503180c9902604003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 664474739 1250 664473489 664473533
    0x3180b04030210020c030a020c01023c06040c061713083109060e0103050601172a10082e09060602151608060603060d1703060307060219 60
    0x81141410b00d0f0380003d0007180420802141d42e61110f910007030034940040070766811508800d9040c2100c282150102c02180310202103108112241c480e04083c1c810010382040f00340c081c000421041c0100151604201c40140d12812032458103003240d0b0342c0813801251300c4900496803462003008201c0783d1024200311200c1c0c0141603843e03103142c0807242c024011400300b85c00101480f01c042c041501c01707014400c000c00c1c9401c0390356103650442c1e886903220707035050261184041000b01244014041006150221000402c0c91030f00c204086a8445200103600c0400c0d001d084442039808450f4072074030b41c0a1080d4178070000e005a200007542c5100b28150090450702e20340e4081080807c03402c28170310410b802811990028480e2070750304401020001c0c0020704400ca080740403100340383e070990010b1040b83c0c018402c5407144d80e00c0c0c0c0c601c00040e21104040d10013510040c00ca0301c922003404418001580114421012100680e6503090f040380d8502502c5d001482c0681e140c81e842c2d0005030301c0d000c2c19000411040d9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 664475989 1250 664474739 664474753
    0xf02090c0a083706090c03061203260a150b09101b022e020f1b0616030201060905060a0f0b030604060b12060f0913140102040f091a0103180b040302 65
    0x808011032103034140d00d403e6420703035401c410040ba014600c6030030141806400c0520030145003044160204000700000360a2000c41d02503a0820500000c0c0f80307000001101141440d41043d0700301070020030014008110076419850f011600000d0501500d04803c0010800404d4820702c9004507881010301e0b0408490f00e2031491b0000040c1d4441100c000600010851441c1c40c24007078080109011003110342d203003903402c0300c42400c1c0e041401060640c0c1826122018002074a0039a02190081c41b5032013a282c0301e503c2c26400202090b03410b400c150100c4810107000d11450301d420b02040008086441100c00580c4080420070809403210040c40c7e210100600000d90b159a892401206520010341d01c141302c1da41d001000b18520b403c281540701c9582c207950200075031520b0820005000345000f00504481c0070f660104190170400d40450b0f01422a5103c580c00c141e0b070781c280350001780207440c03181d503600b07070b150500d84809520034841c070048031003c148000c17030448154540310b4044802500c181d0850080503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 664477239 1250 664475989 664476061
    0x18100504090c02030c150f0a0c0e0607030c0c0905060a050103051302061306020d030204060e061b012c060705040b0d0213030807151104180f0501030f02090c0a08 71
    0x1105074000b40846070055903551040c80c488030b0a04803404803480000d11408240252400c40001b85a80701551400002c0c0c5501c4031101928201107400206511a800045280403d80d01881c90350701c3c036124440101032a030700c44e08501d00769441160700a8120074101b404000f198401e03001139400c443c500300f0702c14400c14543c02107032250303001c0240720503113805100081145941c100403c00e900032172881c086040604001c0010300c20080f09403460b11940c0d0104501e001e4041c42448103640b80d0701c0302d0007040460780b0f5403482100c0710082c0d9622485c54103406040f030b03504800403030f06901c5011140e0303400f490181007843c59032841e0040c64810048a509100c03a403a004080340025000d14050711406850b0b03003483ca0522481c1004000d402079560500b80c1d406c500f4a0110259003d50b412200401e581390050703140c0b04c00500880042c0741c141400c04d000081409103c03802d45c050f8900075609600e465650b250428410300c1501602d000040051000400c12219100c01c03510305074210f00d000b90b0000f409 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 664478489 1250 664477239 664477241
    0x9040809040f0b09040b18010b061902100f0f0b1206010603090305071b1701090b042411040f1212030b0a030609230a030c080315150c0c061810050409 66
    0x1301c5003180c0b41b90b05442800b402c14002c0107036110350078166009001d460020004200e00d4020f000007604001805040245402c2c000d01c000c4282c5079041c0c2080081540312014117000c1c2c03840301e580c420365900d01404070311982084001c6000100103000205640c1c0d280400440007032440b500260108171044c440e4500207090f235101c200341200d440358818a454240802029032010202d4001c59aa141009607000561002d0304240d106801c48001c1001c8a03a003070b0650052544504041c403102c0c50581100440d500090103001a120b085074008e5080f078441c140c12050050502d000752009413064148003510b41320342c22004200c0700c00361414441ca5602e9841205950180c103048446800070041411248090b5247e9005a001c3d80000c100082403602c000d40354600d401c001602480d0000001101500712a80895030303101c015254018891000440c1a181d40100c2c28020260283c0c2c4480302c92440d0113000d841c4041c42e240340e244c041020150400c2580c58048a0110610000b40800030f02c076841 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 664479739 1250 664478489 664478491
    0x60905061902011d060a050a0221040510060f0e010504060b0f070201090e090102071403131205070330080c18040b0405130203060609090a0f03020a0b0709031109040809040f0b09 78
    0x4c3c00400c03150411300c415105403440103041c28406441809141c152052029101c0180210400841c80a0300c0d50b042c0750341880b880a0307007800c02e2801e03ca40000c4032181951003404551500741020341c982d8076102040165030080c4034211031302c00c0500034180801d0034007004208880c814108420201e60b0303071240084200003210340c840603035400700b0a101841404200101d103a820000a54642903404814000100b100d024002510318400c16007020080108040b5002c0d54000001080c408400c0503d19a2100e03c044170404035801d03103404801d024007400c0d03002d0260075940000e505026505004030000380014400340d074050f40b10358065696845910078140103038440b104040070244107005051038000b02929050041518104010700450046115041a503001303d1000e107030410360070700301c1c9041e010b44005040c900c050424050120b0b040041102100e201c0d02154046072111030800054100464026001480c00c00000c80c040c6410707031001441440080c40040d001c0e52001c045011060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 664480989 1250 664479739 664479791
    0xb040305040503011b050f0f0409111b070608010b030405011508011a0604050d030c02063a140f09070b1c0b030d0c0b0c0d050906040c06090506190201 66
    0xc0001d414040707410213004a03d6000820682c0030088242260018075611803521904c07011003011070742d500301d00c01c1d05084400400754042c0c1031010300610101c2006983c02140201c0c41d001d0b40c02ca092118000103c0e9030b504407034658803140016880c3c14001606039000501c1255903542c1c5800d0640044c0201040d100500001000080e8104e0b0580d2451400d004001180380729180a2208016070b5440004083c40940d0514159100c447ca030301c04581c0500070b808a2544803003903a40400c81c02c61912401514040366521000080200c1445010807560b44480381030081000304001026a10705002050304140c020b002c503140a40e03200045003181d082414480d83d99400708402c400008000d01591011507c00c5010340340340800100f0141260000e20f42c001c1c01c04994000080d07030000c414050751300c40c0d001e4140521803480d143d8285a12a031003201d040310344035002c0f14089188bd1050454205466001d0900c500d0020103e42c1071200d40400b1183c0c030210744d29501c5d0059035103040c116440c0502 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 664482239 1250 664480989 664480997
    0x6040b07110d0e010e15032d010b07061107051b06040f0f0806091c0e13050112200d063c06120f03030207020f091003020103050a050f0f0c070b0403 65
    0x980e90f0000421050b2882d0440b881101690484010000e5078011203070041410340c1c4408440115060071072050499407a4400590b06180000900d52201c1c0010705190388180d0040080141201440005000d1090090140e41c003454503240e076030403d400300104000f03008200c0c1d400e043e034941c0c00c2c52070070150790402d41400b25005810400c082041014540241405005d85500c00c0060780020400c4288000b0000300b10792042010016141c5001007062840c3e02c20303040c8101d41c1c41d0301e4003000000740b08100700c94107402d030310782c0016003102c044014034060401015031030141d01946540004c0c209a02400c2c01c0d00c840c2d4107060008540c840424080802e0900800040860302119001103c526520140c50104580c50881c00100b401c5655850306a0500300140c6811003800841c80c20903c3c4001070b50070101c0301047c016480a442010000c0b82d100741c4c0c2c14001503849401400690f90709850340402409070501061106944512007a44140700c490300a041440e0740d00c0b04449000c0548042c0c01003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 664483489 1250 664482239 664482257
    0x720011215170d02060f041b0f030311010e1b0f030114040c08060403050904111c2711040b1309060504030305150d030f03020d0207060e071706040b07110d 68
    0x6090307450040e002d240004009800040d05082019403650002001001d04100c040c00140401c4542c002c03141c28000901c06100303600e03840b008106484680c03800b003035010914030000004852070501540100d1901940035043c0d881e021007030b1104030b40380c0e0b181959100d0705020483c1850340f030911072100f443c10984c402c41b001d4201420001500c1c00b4940060f221900032604000202c0e0b00a02110024601070310001403029101d80009441d001d048000c4080c924020044a110105500038040609141c2c0711260b03441c04040c0500041b540f0902c009151440d0000c03001003e2500f54071184003400050a8640c004028040840803228680c0040300c40d166070b14244418550303d44241c80d030180f44001204a005500b8002840c1030030410001010007603a62006240144641c0503038120340d1000e00c0954961003c0e1401801411603909080518440e41e60006100d041c000070804800020700c01030607594483c0c1e140c03400d071000010400030601ca200707003010180000801408005490a540700406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 664484739 1250 664483489 664483499
    0x1706032802041104030b0c160f03172a090a030f08030907060c051f060f0f0911071a0901021b03090108160504051903021809010b060720011215 63
    0x454066030308410700c2d200d01344401e00c005a4600000c90304aa1100c600c0da07112103a4008000c0070521241008264030094110082055044160880740061900d0082c140e50346000030060362084130f141c0a00c02c00c8004144136400c2070807200804829201400340c03944143c6903100c0200e50b4580802c1200c0c004800000c01140e110140103720141401e890039074854521074075200e99440e500c00c030440c0e19030707180d03071498015424a0340000000c00c142010305000c1591000d200001580900c03951b2031a41c01e1100e5480051003900403540c200ea440a00306400702480303103040d0702d211002014884950340c200b1100e4201400c034090071201d280520020b40ea074180f03030701c001086000003600510b0741450452860601907008016541079a00035514040c00030181c2030003100070301c00e60b07101030b4001c00116070740341d03a0f080325810703a520a42004000b8040b00860406116591250000180881024030101a481c503605031468410140502d441180c5210108c0a0001c0320400515038124011408080003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 664485989 1250 664484739 664484741
    0xe070c0501060807050a090b030f0708010f05090a26090307030f0302010b0d020622120812010f0f03030e120d090612021303060b0d08040305010507110d170603280204 73
    0x9002d110003e444e000f0300c1c0c01c01250100308140101d80005031151207c250544040040e5003017004868100c070b9402359941e5a8034001e0002401c43e500160910b4006030185000240c490340507a4403980468004104440d5000000e0319260f812500806c03c00911003944e800300202030256026180016464070740e4035010b800c4580d01403400303002c0c4600301c2d108070150303880d00241d4003042c01402c4180040605030b0360b40300e40741c0300c2504884042440d1aa60406200008001d0a404034200e281c0312040c0c2d0300d071140007a988030b43e032044100c0070300d504c0402d1000074852070748883c042c01301400d00d0b000c82c030f40b42402c1800c2c4511414a00001882c40108114081d070001d0148411081d2038821850072a50b4008441855035500015240c0381d02c541c2c0452258940e5292125819001020103846540305d2a02501a250645070400000d20320a00c00014803400b01c1d08100e42d41060311100700700c0860482e10841420300406295150245900040000260000314a04402e0b0907180342401d04842c0f0400c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 664487239 1250 664485989 664486001
    0x3061306270509072304290607050d120603022d101202090316030b010f0b030c031807270e0f0307062d3e090a0e070c0501 54
    0x21003800c00c0d080c800300300f102040100c00e6990b1043c092010481c00c000d000c041d0f4251619141e0028500300c090486043c03d140c10b8a810007403a40c480741c04014060401400703000c0c41c0740140c103940140f494204500e0003402c081100c6139000d6400701e1103d80d00e8000031042d800031403c1030700b030a050510760b40c42d00440c40070414031290b00700d5507401404241d03000140400080b080f0041d4295000500541c0c075641002955440c40a54540c08051912403501098885080c401c103002c1410b441404203c181c4070324156031082c29050050303820341d540c0743c00e007030403540d0b2a244010590081641c0814451040c42030302000051111a1212000a4004240c2120050381982c22640c1100c079001c0802c800c084216008690040c001003414070548260060200e051698544c4002d0341c441c40498000107600400c40c080d01c0404040071040b072260203940c4c289801048442c0322140040d8521075070744400040c00c403030741e005403240f5207003910b50b06000c018104c15103034034000c290050032a1041110034040d10b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 664488489 1250 664487239 664487309
    0x105060414010f060305190606020307050609030412060510090e0f1905031c0e03040e0103030f0e1f0507121806090305070504020306030109060c0e1206150603061306 73
    0x1886a9890008443c000c07503203034000eaa08142d11000440c2920707815000c8800448800e4a00300503441d516000070355280d01c5124202c0d503601400c0c002400c08400401610122024503c178440010b0303203a91307150b0003054010000c64000320012030218010085104403030300301640d07c0091224000109400d40b60071420009030800c1003046c503070180090404015500c4903030300240c0310507911155038161303000780000788580440303844003103000181700940300c4406040364040d4480c003280c07140c60141142d01103811599240c00c001510210a10008243c40d400c61403915803401d00d040032003d50b54a520b001c06420310b00c00040c64078034507442c6000303600404401002c29007040d012070b0f491507452580300c0103680700d50391241e036004c1700194940c0c400f900070254940e031241080001c04000c40c8041c21031a01007040602820240306200f150f80000603683c0d008079041084122503210040070401660310050980c0d8008404a061501f0303000d4500030780029081c942d40c0642100c4070040d07101c5516000c0e100c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 664489739 1250 664488489 664488521
    0x180c0f050901080c060901020a080706021e0a021b0a0b0c0109110d15111603030614010309030509090c1605010204050411030708130302030c120408210409050402130e01050604 77
    0x1000080000640c0700c8244c0801c0e6210754a940b0b540740141c0c01c0c201d4a401c040c00b8110002810390821115078000d0002091a10895056035891050036050303008901011740981c0c00911440103116181c2405100880004c000402254942e02c181079503410000c208042c90b03450701e605030304100c40248030382c140e1141034840c08400300382c03502c07440303001150707044500812662524041a0906c03207204807205143d4203055003a0b00c0005290080040c1110300c2400043e00000440045a6101e40242e1450f20340542d40c50f401d0010b40d10070440d09444c0500100b64102c030801c030701f16240310031414001303600e0300410005807110320340b0041c070040c0c503881d50400d46040007c000b04048181c002c034034640c100c401d001c180c0301015218907007a03207180f00310340d8503010511480c0040c550048420008100341d401a100380c03001300d030504548418a50765010342e40690305d402e0006014200944c2e01039548140006c01d9050740c4240807031141c0803110800c1070039280d65181c508109860405002e562900700341c1002c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 664490989 1250 664489739 664489741
    0x90102090a06052809151437050418090c0b030a0605060301030210030e0a0209010f0f15050f070501060b070b060f0a03050606010f090f1212030b0121180c0f0509 71
    0x105000c43c54021151281210701b010a415441054550025030246054560707030801006100f0301510141e40c060041080d01c03101d06a0320b00e070030320191500c0074a9200c442c10581441744420510086045044010f56a90500b81c0820f62421700300c0010300031800306654a08121582006564aa8101a024440400040005131902801210070711a140b4000a00001000040d82421040b41000e0342c0101510000b082e040c03c110311400c1210300f803941003400c040d681c0345400c00803d2003a00d1000440c0081c07008045c83c90b4807078020044617104400014004c2d482c0d54040125401c00c01d0700b40c40b4000c050040200034200702c005000c0c030790740c01c40e10180010700d5030382d496a4800300106901d041044090018a0150061829101828588503810612030300c5040704c02b070480140c5401d460400026642024003802449400c1400034181e486c8c0500c400383c003900c1906001c21940190025603100d07200c040032080300d03e51041032882041c4460165182105e010200300302604800d00c1616444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 664492239 1250 664490989 664491067
    0x3060903020615061606090212030d0605041415010c0b010315050c07050601091802150702090606040332010e011e14220212010b090f130b090102090a0605 68
    0x110a56440081c5ca4054803451030151800700f01a24010304000d4201c43c05a040107540c280110241041d1003540c03400b0000d4541c0d603000c00041d2030406038421003a00d1840003180e00c20040191543d07400350107051441c8003044079500c0c50003440090340190342d92078100800410b61034190090641040c0e000d40c4180c00c0c45110b4544907281c07030043c80f1340f509155903108030700c204800d190a06001030341c00800303070000c41034031030f01e044107940c024a400c03481886520005000c2cbd14249060320140d94103c00350950509588032003a00001c0440e0062006a01d00f209035208002c0034001c210301c10103413000100d20b9440500d00110342c1140c40d800340001500b011446001540303e141403540c4019040b18484000404030071040503a41207a801a40246686040c03840310303071054000c446518130030b481d00401961040c4039103010300030a88460081210b45403039440410850050789030403100406c001450204280b00041d42e004455005501091020074100c500ca400c48804241003d0b94683c03071103003443c1e14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 664493489 1250 664492239 664492249
    0x2090709031e120f0e03030a030f11030103051009021518090702030f0a03090c1d19050c0a0e01091e030209010906080c1e0904060e0c01210905150103060903020615 72
    0x1181e0080304001820f240401300501c6504482c200420180681b070f50703800f40d0b140050190400d1a41c0c05003590500030b07280d0489440000f02e80c100c0343c010010303100c0c02820240c488064200c107041a07a03c000c2d0344404510521400b030040a2103400b00151212840100060082401000b02070006541081c080c21181d0003e0b0780480e00003220310f01e00010004294985190f1244158002c07030b94001d042d00c84440821740200403280544808440d0708681040c1e1980e10044e217908480203007981c2030a03c1010480d500645841349000c03014140710640361b03100c0c22982407980a4803a0a406a140c08100304107600709000d00e035024180c08001805401d0524020503078401d03450101a00501d22070f9100590000e1004901501d848010f02d03c0100781000e04040d40030b803441e441e440b01fa40c015a44100c1c1c41e0b40c05070200c004100d04207140078212020f03100c1c0c0c440c0204008241543c4a0207101505031503101c28907521400f86100c3c6500140c114202e0130000e10b4a1401090002180d0310020440d03480c1d510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 664494739 1250 664493489 664493513
    0x1081009110d0807050109080a1103040b12060d05060c18030c0312030723041d1009050c120108060708010f0605030c0307050d1b11070302010e040b0102070302090709031e 75
    0x642e0900007804151510300700c2440b03070840181040d464140c030070040250203001440010307182e594980010515141551702d9100f540b182500341c0100b08641b601401c4001405a44564000c11502e20f01483c1e032034450510104450b1119248000602d05403025030143d8610000c10058004003c08400703140400daa545203140744070700305000440027600081c400c8203160421505103503031400407541010004441e4015008044032404007003241c0d8107070314000c800780b40304a0b080400764030001c0c50720001200821000d030101c00059010081c0308003402c0701000c182e00030b00440d0028004c501c0c3c01d01d0000c00c20801a080000700043c1828100801a40002920b42014004a40eaaaa82c0b18810291039602c80d01424240081c1440e2541000c00c680c286c6480c00c800464440403030480144030201d48070206404003d0100d009002d00901505155006450602060048464071600c98001030944042142c0c2503001424599003030007004400c901d4000c148134041d03041003160009941e01c0c1c0443c50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 664495989 1250 664494739 664494773
    0x31b080c04050603030c07081506040203070e1306080d0903020406120803150109050a14010206151c02040f060b181f051303080c0a0c0f0f0510050d0501090501081009 73
    0x70700d42c0d001c240c07a0340d0180101c0e42100e4040e81202c0c0c0ca2039480660316114a078001040320164504c100161240c00d050003220711640707a03540c6010a2594030010080c15414034110620f0890342e6500c0030a020f2810044099403541c40d885540c10039203584108820364115422864030305d40002c9522002611800507250080f015200480c112181900101c0d0b21028550000303a00c041351503070000f10000c408540d61030002081c0e0071348210355100c54040c5a01082e10001c1c64110300c05031100c8101c2d40d58100920a03040c8014400702c3c051140d1516402030300c51581140c1c007000000034460007803038519130b400462890141c41f04011005580500034280d0040201300d018082c1c00280201c40b0007401c41d620300610340c810030aa031641d10301e0306420f43d500c410300400c8819031180301000c120410f03201c4a2008980ea070103800f91506082000b0312200d24520203840c001e02606110740051500c1500449018000b4143d0000700d5601d041542842d00e0321443d40700c08020301c0c10280c500403c10a10300b0300701c420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 664497239 1250 664495989 664495991
    0xe010603030207051011060a09060b0904050c130207140309010f030b030d0c0503070609140c031c27060c1707150213080303130210110703060b06040506070309031b080c04 75
    0x1174040c03c0a4a881c031041044560f180604404c10296103010b0b400040714600504d401c10480a240003484180074042d00c001d00f80364000e080c0c1a0302883e001c005403c4c81e164905025083c195a6581e0804007840b900410384580c00208041205581c41520050b076000c03a4a41170000140000110361182c100244003400c100a80100905200080080702c00041d44060100010301c1d80d0b00300340013008140700041040d03010f200c00e10900d91070f000030006100d0348900e40f9038210140180c1305039051001c2005002002c0c040740d100b840d00ea404600484001c045a4440c000003013114036160646da84450041413610700306000d0200802c5100032001d03482c014007080140d803a541045c141d42d4480c85035000322801e100000402080c000c2400722600c40500c02c0d9501841c0f0084400d050351000c03002048450150b02802e01000420f0481c1c000d03400c000400b9101500e40f54489c1c0c0401d03034640c0001c1d401e1f40801c580326820000c100c0e500741c003e001e40303121000380d10031207041c082c80c16120032411600f240f2035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 664498489 1250 664497239 664497259
    0x1051302090303030718050f0303031503010e0a0b06030105010b18010c022b06110c060a1a0a2306030105180c2104060c02010c052d03010b0d0e01060303020705 70
    0x1418495049442006005040f01d0b101d20b04002c0c000c0c003003c1e1400807188030b1070242c0000560b41c246280c60801d50040200554111b5030750398100015119203c041076803641d241d040982400d03d00b1f02c0991032040c0038050410841c9846010b240c01e441c4103030700c00d800ca480104414116142600480c41e1066001d02e024002e8020a0000800d0b400c0b1601c00560140d0306842a40c0d6180c0034001d082112610a210a201d00c0c41f450032281b074140100c1c2c6105100707030002000140c840445a004456074102d000d8199000c500002c0850382c09642608048451203136842c00341c41c00328203040c50100d07070441120714515640c14803000c1001e4810112880e01628280c90120704070300c60745020366503040060040915414112850300301e10040540d002e0700ca4624101115486500c10b005406a900709600c5080c40c1141c68a0f2032031201e035442c50b1703092201c00d07065401001040320100850082c0019001a9190b007403242e202c00c12180100c20301203107613141c103030100006038000c10b200342200c10803034042c042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 664499739 1250 664498489 664498519
    0x618050d151517010b03030306030606240d0203060301150501050a0c110d03030606080a1a0906010c0f05010b120703020315090a060e010c030c0c020307050609042315090c030105 78
    0x6040d02c00c0030003400881442c2c001c10344180d440940103540e501c240082c422869240c00f450303100e202c00d507803064041d00420f0000e44175060408950420707001e19420440400a1000600555000018002d92054000080c04042c0c60240030303442c1925049c0c290022250300d0300c00060000c1c0300744c0c44c1c41c1c0c3c184086282001c05002d44500c04d100090406842c044034039402e403800500511003400f070f64000c1441d100115000c89120b12440042c03500c9101031480015030031040003940781000300000d040041c0004403400040c6a4000100014402c100215032840468200101000100c500020a500002d002c00140e60001003c02e40005040000e081988580d96200d050145580340a40005e0610240c6080780405600090303042c0415034041040e0122100212030b071142d0ac4030069070541c0001e106002c1e030b21342140107200d0424010700000e03481c681c5900000c05440c3c461603921000d00d0160400c00c0b80c40140c00109035082040700c00f540b00f85015501e41e0441d0006000d010302802c010303000c8030b103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 664500989 1250 664499739 664499741
    0x4021003060e040b0105040e070b0405040b040f0216210203220509071206061d10020304170a11060a0206130f0803090f0705040b0d030c060b10090618050d15 69
    0x701410b80300c081e42d0800c0c60141010f04964600307108140c002c500e01040c41c1400343c400300c1d02c1c0055802c8600702e1442c25180070100310241c00009401503001c2c0c1d0392601d404420f0410f02c01450442c014144480040800d4140100e0501030b0007141d0990302c88840300460f00d243d0110485112201c1c80342c1c0e40150194014070742c40884d410b5042a500241c90b1010300001c203801c51200d42518100715010f2140c151a40005c4403a00d646083d041c200c100002980101441c0c4075064124401c11441100e0900b5603851120400002c09000e001e02508054030000910148821000d00300303a06941c00c078a80039280300001e40c3c4001c001c1081035100800c510788401c0019120500e0040c6070072014527a124145002059221038041310340d501c8910602000003064142030240401d41a0b0050102c8284401e90710306a07001806441c0454219544804020f1140c0d205000485194507a44e540c0041c54180a4060241d4001c0c1d6001d140402d259401088280d44d13034810800281d0344900c0181484c2c0288003010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 664502239 1250 664500989 664501001
    0xf060f0318062d0902010906050717040f0e0109050621010b030a06020c01050708040302120d060b18010206131e021809010b0a0b250c0b13180b0904021003 68
    0x404207410454400076065180b000d40c007012250315a03540300030b40d0800f1502c044a02004000380400d01c2c102003003101074040e01c060030516004001e0041e034281c0a4425a13001e40c040e812042220302000024404480d0900f4540d0240120300700811050421400084c461914407400d4405c1c501203124004071301c00c00b90040c0460102c050210340f8511050710b00342d00a9013041c1600003c943c42e020004840a118080306402190540c000e01100c411052080340c940d4480c4000f10f03407040c0c40d0f100015050303944030b0050034015800800401a00244800281404005010204904100d800c910049001900d80e01801c4080e09030407240c00a040c4080344d03d00401d83c800d00c01d904195001c0154a10041d0041107040b207049800a000980700c203410078403070044400b9801851580c04030040030b44000c00c2a40c070040e00501d0800240f41da90101c9184076440005070304064005804200042e02e600e481403003407168030207820703c002d6400d04081200924000e0004e4400c40e5500c4125003894043e82c415 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 664503489 1250 664502239 664502243
    0x40305070b04140126060a050d080a0e09010f140d021201090b011e05040e1912020d0c05250503010e0a05060c03070c030e06040b030901050702070f060f0318 69
    0xd2086a541c59200d900a9001485515140300800c100103100b58881c0d801c0a00e880082c44120120517481d81c00c003145500003c0c1041c1d0003201402d170201e51542c4c6c84110700001131107442e07060340e114072480b0f00402c803100303104019003d116040c0051001140b44c81246042d80c00e40d074400f0404c55000400038000c20030041000e50040c0c400325044034004c1d8103401041c03009000707000c00784099a031603845801c5c09a00c030841c8649c2189000082c044c52920382c01c40140788a005c4111000e02ca1821182a404036890320115034804502c0421a002601804074582005507401e150400411503142c9079120004031081115074020070550400c0315134180d80402c06040c1c050000c203c1100c480340c0307440c2da48803090f00c140d80a02c54031001a2020f035692003100d11806e0700d940c45000a21441c1e40c15241c2441d4406c1c215400380e010700000c940044035801452107804000d0020480d81071010340642018a65044407a818190000900865402c14034803e090750703c2d8a8001860034625000c0c5100715069900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 664504739 1250 664503489 664503493
    0xc0304050a0b0a021b0f040e150f040606080c09042406081b1f1202090d1a0a0626030d0f09140705010c141e06090706020105060d0f0206040305 63
    0x1042c2c1400c868040c3c80707000302d1034003290601107051606004c0d4003603000400303501000c810801c0300281002d03000040c44003540c2045807144ca082001136840c80d103040b42c80d03c90000f0080d04004c1400400c1c050480102600301c082c04511490b500071035448040148080c1c040c0ca44501c80e400c00d141a6400c56080000e4035038200103664035209995291480070511200c1920344c21660b800d146405c02c103032284264403e401e0007100b4601103081d107040c008800d03a442050b41c2806003c0441e15040416080180f26000c180d00c0c00c0c1d400c0c0d0f0210174610001d4402089649800000d0001c10645030a5091703002010a000712241d07203600185240d485400340c804d41c05402c0c05641121400c0b070340c102c040c445100c0d84070380400089042100d544d60f40c00b442160700140d45100d52001086c3c55404a03600c1c4ca010100345c504c840c41c4080d8507012084c031040c4240c51588074608010604c1401d101c80c402521961001b8001c82c03c0c480002080ea040199000e84001b0104010074119501d1104840003103502c441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 664505989 1250 664504739 664504759
    0x30305043909022a0a15020316020105060108071b0c0902031005180406110d05040302060a0f1514120f06090d0c08070b150a0e06041515050c030405 65
    0x161a102a141506612180d00e84a000c0442c014280b4000d0340c189201080004411398803118100b488403c54030301e0420240141d4000300301056002440000303030b51106001698030b0134503090030302074200009440000c41e4982030500c007460303a10041c429048055450000d40c010300181403600e04210312240108455100c40b0001100060307038010f14032407603090030f41100281d500c806200190300d02400e8500040001030006000031050350001d0322500f05003501c68101803883c14030b40216403061343c091300076038015810007040c0140b03409040e100c444025414410002c0e20360316003009005502481213001c104032012135040e01c03500283d05d0441764180c1242c09001c0744001141d08e0384400e417038100281c000d100082440500481301d680035664015583d81c03501c100c9881b1650f0309040540f4802030016203910b107142039500d0501031005440c0160f07076240d1a08004080008843c11610301c81915204280d08010914103a40c4ea000307041ea2600742a9600e03800707440380c00d085200c0c40e0000ca910080140e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 664507239 1250 664505989 664506053
    0x12f010b0d0c1505120f09011b03020c1b032a03010204150f0c11010f0216061d03150103030c0f05072601060e01060c020d050d030222030206030403030504 68
    0x1e004000c80b5600c4800340d8440c42c083c48111160300c165041d40c200608500c0206c5c0c8130000c98140702e03a0200303040b0000a42402c668440d01401401c0ca000c64001a40124241c46881018407a42c00c2c001d50351145628140c2c162404651954104099000d00d04514113036040010f01e01400ba804040004000b150303919107842200c000e9440d00884180021101c01e075091205000d201d54900d81c1360899500309038459402e00440f004d0b800e4410480850141500905418010406040241500c0c2d254036504141e1b86210011121421405600c01e500c0315640069004203403811505481d0503203010100c00e071881c10301c01908102c4ca400209944100080000c10704600340503218030f24801c20010449452180001d0700b0381e00240a10440950088010001c1c1c3d40904151203115201078101004444562240c2c1e00b00a802d80f60080072a40009643d600501c68003541d406445c8444101c03681c681c1145c008c102c5a010051000b428150758074041018000400f03100b10103611002d10301c1101003401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 664508489 1250 664507239 664507253
    0xa0b0a0527090d170f010e190920011d0415120f0308090307020f010f020f060109060f06020a11010c112106060a0b092403090a030e012f010b0d 63
    0x3085043c0b00080c141c010140454050200b400d004200740703035031401d080e402e005110b03d001c040502650103c042000c9102c0c1040001c2c000e51302c1082c0208918030b4140c10041d81580035501030240725041012902c2842901285ea00300060000401d660001d00c0240042c1c0107880c1c0c00c07003600710038020078102c0200c10800050030a00c0074014443c0d034803120329499201d80303d50380340580d42d002035000b0029010000700c0c1d482040942440010341c03044842c1402041c4500f1308061080e042050500d4842d2028000b00031140081402402d140c401081001c6c0961154200034000020443c10009018104410f002014030904d01440c0010320586041d03040036456603600000c0390011815004060000d86203203014007160044451a480e038616140380541009400c4030614007007020007001020001e07110b5a15400740d8821040c000c02800841c41c80e080281c072415080130440d0420903600005510b046080e4804113030104501117020f420050300c0301d0035015100242925401408000300203050240d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 664509739 1250 664508489 664508503
    0xa050304090f18020111030904021b0f0d1d010212030c070b060f01051b01140f0417030c0711150315041103010602030f031509130b0a0b0a052709 64
    0x111035420801d888030070382420140e03042c410003c418002518800009540a80366800c590b410440c190391400c002e05d00020100c1e0030244110120300100c425505480100300200c04122425000505c2d4090340c1d41002031181d041040780b0184e040500f0150081a40200700c400c40e141da280c0d18498032450701d00b440c0040303038124030003e442000211002c00c2a5040501041d1040901a50741c00d1030701e00048041c0c1c00034003a0b04c00c0c58140359a03510b141e2003082400d1404c28010342c08910040f100c2c1c2014101104102601d260240d2081420000c0c4540740000f8003c40344040d50114010044a42940015100c8003016107440e0001a000080205010586603040c440501c1280c0400c030414500600350b049002c24004c600140c1e008000d0007441906240140d51f001042d0242050881e0088001c5506060242c0d81403810441c460554000c1200300307503415500850300d01c0204254041c160000381d911090b44a407501030b0100a40e5000400340c4014015000b003060150713620785041c1342102c10f0359002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 664510989 1250 664509739 664509749
    0x31404090f1b27030b07020c09090610151205010e09070605070c090e1f09060c0f0906110c120304031b0e04020402250308060301050c0a0507060e07080a050304 70
    0x440c103030410540d510108104220307003102d6a035034501203109004104a83d06a0100060101d04841c000000510380003c00d83c0b00e0b0001d80d016100711808072090102105000d050394130700e80c00540400c400d4044403a034080840e0003002d01c0c50100001d15100307881c400240204492010305040000c640b84180802542c0141402c07811500d03e40e40d60041140c1c81e014828000b01481c0c3c0141c81001020100c1c0c00040c1ea034140f0700d081d00c013103007000d03583d0125a0801050345820fa54490b406d0b0000d00007944101d444500140c117040c10503194442005100c03007000d00034481400075200802042c0c00003003100d81c00c07140010340455401200c50310103035580c5d006880103c40d0100403001b102440000e6000b0b9a085458140c00c1300c00c03988581c0e003040b000e900054018040e0000c0c0b84c08980d100180d00410100c440d002e43c80b18008c1d030408000385400d40e5802007420b030045008000d0003505a40c0301d0101d52455401090024024203c01001c9040c440e840c1d12183c0c0a1059001c6001840000700081040721 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 664512239 1250 664510989 664510991
    0x12110f010b03060721270507030c0f0302060a08070e1207090606050f0a120902090118050a02092b0210050a02070501021c0815041e110304050303040f031404090f 71
    0x41e44520040302c401080e40354080120105444040c0703c0000e64002d013900006030f20440c1e06c0783e00d0b1048041d1030360320030720381c2690385034040c1d071080060110940c481e001600b03020740300100c407500b542c01240305481038402c80000c000c1c0c1c010002e04603520640b40000a04001401280c000c1a6801c5050362246180103a0019038a40720000035414015011503031402c1c0032000305030070001014400d50f41c400842d510280e8060320b620424005030380302603c01d0301802c0021060020042e00d07003c08021910018500c80000d4130400c0340320117658a890031450030444c000b81e901c40043e01c2d506206102c0c45040d0740250011510401d54030042d070050064494401d03e9030860b00c4181d80da1004a9403030542500c0d02074800300d84083c0f44452031090160660102030200741ca0840100d11010808a03485030b10070b500d84100d41c2000c102c901c40709000301046454519001070440c1410b8036826107900c406080201181c0208032007104150081205000c00701c40d4160701e5488584e00d41100004c0c01220340c1c0c440171a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 664513489 1250 664512239 664512241
    0xa0b03070b0c100c09030b0c07060f02071b03030503060d051606020a050d02300c0a030207051914040207020a0b18040c0c05060a180507090b09070507080712110f010b0306 75
    0x607039841d215841341980265a4485502c0c80c42c1c695043c0f290001c3d10700c09801808000043c00300742c07a0700448201d085250001039a6070614144030000381c010041d080e02c03036140340b901000440e03400740640c1d401590469042d5151030482c0b80180ca4030200200c1910001c400d0703c800203449401041d0300070110f0140e020b80b0b4a440c0c22403801c0b80c5907603081a400342101d41094440c0e200d0305030188d80100c01001505100e240c0b40d06100d40f1880c20410714000c500583c800082840941498040c0704000f031044c03181c030f4094906041c00c14200460490780180510360200d407003429596035036840c40003404a40c1401b41c1e21b0200c1e022058801804001c1a8041d6003000d03490104507200d1044611001c2c0c1000c05048282c503607160913001380c48203c03180c440700c0da25149044046030741807051000500c2000350004100d403031b16040c000e90250013040003042c0321040c002c003000704900f00211006240d2000c800302c20100d000c4015501811115000015481540d014806602c4158004c40c22280200c04a80381 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 664514739 1250 664513489 664513513
    0x1504051e0f032b180c080f100b010302070f2f18040201031b120b0411180105121515031e061f0801140a050a0e0a0b03070b0c 55
    0xa141251210300c0416841008042d08840d600c02c3c03050300c41c2052160a510a40b0240d5030751040d40c40000441c000580f100c41034500704200304da1424003c054030009828103548190106d41c9442c01c000518015646400300d013600c50b0f10a40c102c0f42c0d0f243d40302030301454808403070a00280d020000f14415034000701c403004848030704500080800310600004e0002c10400002844480e010b880917104030f05240e160048270b042d0b1700130001043c012070b4055a89110240030340c0b80d014241c61310202a580903514241c4540c85c00c84c01902240e0800050426005280701c487d80100d0b628490000581c10300c2c10001c3c244074160341001545041c1d00000c0340c01e0007841020043c072400740d210649c1c80c208100000e01048902800c803090300c95001800600d01001c1d41c0020540308145100b4105210005078240c0040c480b00f204d007048910300200541c0c08840d60390900c0080781240d07a030307070040081e0044003400140c81e0f01c4040c1c101b070130344242c041c060710402ca5440f070b000100c0e60403558151030103000320208090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 664515989 1250 664514739 664514743
    0x40213022a010501120f05010f1a0f090105030a1205120403050c010e06060609130e0d020f0d140708251212090c06050705030c0102030f16020105042001021504051e 72
    0x1058504100c01c0a0b081401990703050000d4000c6d500c01c507025500c80c01c00c0c08441c134080c484c0b0030f1440c41c00e0984201e028179420400c651480c0e051400c0d4425000e1400600c9546c41c000740810100e5480b4a0071401c0d001821400d0b1464090030805001c031002a80401080582c80300c0980f103081d03210f100a100800200c0d070031702d4449034202c44c0d20741c1000c0184501d125601d80510310b1440500e07505400114500e001f030b5240d041400c0304521070050703031000c0b8003000b140d0020421418024070b60700d07104e2405c00003081d0300e0031140314408010300701c0d00d40410403402c800051591010143d1003140c0d020090f4101d49060404d46229100900200b05054a442c13940741c1c40c0e005140e54654403d6416008509210381075030180c12911041d240e0748024441003d003ca8240700640c00b42501150003480c0785000703e5400d1010200b2001d00045904107400c0c8400035026030300812103540104502c6081e220070600403460585014014141542d19000380424010007080740b1400c40300c2d20110090080491483d19 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 664517239 1250 664515989 664515991
    0x10510090e060613020d0b060414090708040809101b06050a0e0c0a03020d050102070212060603070b09130b12100b0a062c18040302061e091203040213022a0105 70
    0x1580040da040c0400d080310b04e09030b00615206844031800950300311104045206074009401440040d003005010111600c1c2104144e98020305070301d0035026628040d51400740d0f601130401d91070b0007854482e14001a03180943c01d01c100d00c4c500c02554403004c040030f013002c4010706815110348803114540207540400301004501011858009014014203a1641c1d0902c500704240d06800d45079954280500d20040e9a040c00c0d02410981da40014600c0381080c500b0503041c540c40c1d41c03240200b0301042146100680302d06845801c2040b120000040d0302d50b1140206030345541000c4030104131301845484981820655100503900c10341910b01910103900e17880b040d0340c10f01545a4405420b0300d030381032015840e005440040711001000e01120b107064080c103484901440c0a44044026070402410842c500c14000d01c11100c00001044052107400d0103001c11392a540e000c20183d06440300040001d0654440d502003281180c2c0300201150f403000c5925030a400a05085d40004800a03440710642202c20140105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 664518489 1250 664517239 664517251
    0x313061409010819020a120e01050f0c03181603050c270702010608070e01050414101a09030a03030b130915020307020c04110a09120c06030209010c05010510090e06 72
    0x10500d095949001515640001001080361444440100101413224006040f10b040c0f252941c4202016201c410820ba5000700001c04c0740360700d408100310702020103204003130f00204c116030003031340d6600c0f901d401c940704040c0007003280310314803d03078260b451900020450003085074012801c1da5141d00c000300400ca2695126419803c050081c002c60310f4040b161000000c0c5c0104a9000000b005a40c8810203401d0480541c01414400c0f203003801040a030415009a0a003112142c0e103803e0b0601e0040941440400107024003803410707440b00c0d942d05064a410049550340e00004003150345890461400401502518100b41d024a0000344d00310341d00e05190185080707042d400b03192444140303c0100440f0080d000100508c2c1144a031000d00c54072611a0b104400c804040a29134640d14030720007030040d05924050384a6800416840002800705480c04d4036003082c0d9403245005030740d82c0c3c03985004130380160010f0005082540303040d0a0107502030960f0035003011545503981c2446880100c0080d503131252021149 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 664519739 1250 664518489 664518527
    0x40504080909090a0c0603060609091803230c1c020a112707030b010905010203070305030c030703110f07051e0a030e0406230f0306061e0301060314031306 68
    0x30440c038500d00901116809480c1404451340b0706480d07294000705248a81c06003000c6903071400107000d1180e024810002030070b41f0003030a1001e920304c101218a503118a42e000b50401c40e130325040800d080007050022505041d45a000c540b58020252200d481e00890300003d11018405040c15141600210b070702c10f03180345c211400300042140d050074845881135018690780b000c0d0350071041c1c007a200c0441e18824021840e994002510303802d076000141951509400ca541994424818000040d0744441147d90100314410080e4132038a803c0010340c0a4040d903040382c1d01610010540511030340c03c0d04058102c03103001c0d100b1601000d06038044070058000c090888445904400102c00210340102180407071400d0180c030024071503030399680c0361407120340c04115000010a00150000145008502060551811000340c5414145180006d8061112405844c01e0a042049a40850750b003036112000540d00241103c694000c0402c80f2612a80100f25526010705100c0010683c24402c039040e82e940c1003600303072b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 664520989 1250 664519739 664519747
    0x80606010815010c08030a021b12071b090204080307170403150504030c020a080d080a05010b09091f12200604050f0a080a0305071202010c0c02041d0105190b04050408 73
    0x148800500d54001c0e180f07042c0f144000c0c403200081c4468005510500140c000142c6860030b0040c210b00f6582c03200010304607076020b51300b80c02400da1a6800c55803483e500002e0402d4840011700c4558081d05194404102c072480450b000960100c00f10040025a1180081410034500c101220b5028010350002810070161815041e458000560011303070428024201403400002a80c0094665800c42e000542c0c0340c2c004002504503c0d8201c880180c005d09008800c0c400b56051060301c035014084c00c540d0b140300b440d401000c02c4090b0b0164038107045016404000c4000180c41d2484c103c0d40c000318800450f8442e000b40c1010001c0c5c24a29401c5504820041c05c0f41d02c1c252800c0c1c108290080c040d92900d40c00302046000041c95201007280720706051007500c40d603448107a0380c02d0403802c500c01007a28a095904001c071502407581e2000d004d280c100d504490002c0c20300c8100c81c21200e45812491300890540c070f488184480e0508000240304040d0440c0c0301031244168010500c0140c41040d100100b000200740 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 664522239 1250 664520989 664521001
    0x120f020d0309030c23210d052e0e0108011503080906090a03050705030c06040f0b03180312010f091103040807020f0a121a041218080706090f0806060108 67
    0x14000b032050714024900a8040307881e07621403145c000181a1818410f18a034003140d4400441409015800c2031032801c4000d001500f0341800c000d0b4484d0107100c2c400651355800252040000003424860004600940304204e1400310b01d01c040d00c56680102d03400b1110b40d00c00020003020500980100200b48501030002078a55a40c0d0040ca802440c0d40c1c5034444000d000107541521100500e034029405a00101040c92034030040c5414a01d40701201401000c0401080c0244004680b030071b01154207100340a5901d0b03444041008401c04029514561800009409603d01c4036070300c0124180c0390301c0b0341d21401590740c1d1046102180d1002803550b240d2082800003c0100e04480050181c49001403c40600b220110000501c0c08010f500310b220401030249a54080c01160482c101007030340741ca9807180146c18682c507401c0f100303030240441000300011407100007136910301c04140388010321043c8211100302d5104c50000c0c1059107035004205120408800014450070005801d901039401030b111103155807962 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 664523489 1250 664522239 664522241
    0xf0e13060c0203190206060a1a0304110103020d1d1006080d0e030a020603090303040c05040501050d1e061a15040509010b0a021212090d02070302060a0e03011401030b04120f020d03 79
    0x1050410640c0400d0019000010134046520204549680501410301e0030800704400c90980e5048001120b64030700702040545503480460f9041074000c43c00442110400004070003038440d07844001070080c145040a40210034074044000010345183c1595803105090305150100d40440c454022194040c00c044150749000d0280105002c3c00036050302c0603151180c010400d035500a841e448800d0380000100014800c9440e01e2002030441240c082c4080d505d004001100e514000e500075050020141106540320085044c40119562105c000c0c04012003182001e0804e03107280c844036001e01d60b10302c207001445280b40102c1c3d05030f03000200940c802da42006070101246c0c220320080400d521820065021030801d2401030300d5042d1a4507540b0416180c0358a0640c00d280802c038082055500c075150030320040e80c0c0c0b0707020341e00d55441d2842c1c00d5822185680c00203002d40190803281d0b003d1032050001000344955400002d21450050116480075a041039044607a08140070a010060f04814618200b031842 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 664524739 1250 664523489 664523501
    0x708090a200102030c010203041a010b0c071401030b15180d0c1512150609050111060109020c0c0d050f1c050406031a06032701090f060c03140408040f0e1306 69
    0x70601c101da00340396046041c6800c80e40260b40650720081003502c00c0003101c44002040740900500f4205c42d00348201031a42a070b45079028090301e100e031000c01100c1403891340300e64007a580400c1e00824000e0f40056180b03d55400e0382c0411151004074030100034240e4281481021440c0466100e14400d000c945000c84044032620442c0d5520304100002000c0300e4a50720b04d010b00c26515484440c90580149881000f078255001c55010301d0501c649592900400c50000c1545070454005038809640e6012030300d10a810300300190a066884081c5c0300c0c1d00d00c1804000144410052203c10031281d640c811504400300212001350000001b410410017405140e121790000c0717444d0030020108103800f20f4450001a01791f04201c42450b10f0b0800c0e80624149265146031040000b20814000c00580b403040d00c94020b048803810000e03092503191f80c1d5004803684a03a01082a1200c080750290580c00c0a2601c4e008581c0544244c0b6a0303501c0110001c144c041d0700910450060400c8052410112159550f9034040c000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 664525989 1250 664524739 664524803
    0x20f0616051c1206030b0a0c090923010b03012105030423092a07080412080c010608011b030902120f07030302010609020c07030f0f020a030b0708090a 66
    0x104104000005108100c140b00b070300601c2e07040c44240118050001c10046000007044980c504205040001c204202046a0044920b0f000841c0c0713413414031001c4c0d0790003400d54013940340140750042c40c1c000e08202c0b00500c00c0295054854213002e90b69071350502d4850100307000381c0482e4052030600c0e45000c4000e10404812512076019a4100b07540d541c52401d0755050102c4001d44d10700582c601120030718000c144107a019458544402c1d012005008168805255458804050310700103851070511100c101502c2c020b24600c8106181e03485070b440c1220303040d000036041001660030702d9808244034106000b41000c0c440038410050020364030750812405850101c2003641c2020f2410107001424900380802000041c800000302225441d51400034210350f1182c1c86214100e00c14481001da649001c204001240e0304010203195a4501c3e0901c0c24020703145800c02503000d420b05c4800010800e2a0b03288500c1841152966a1660b8540ac4013680342c0c10b10300b400420500408011000407403050068904101c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 664527239 1250 664525989 664526017
    0x1090201050307081f170d1d010e03010e010203090703050d1b170702030616020d0309050d081b07050a2009010302061e030a02030a0c020d170a0e0d09030c0501050403020f06 76
    0x420700c140c61340000700c046d0440c1c0070604070030343c620348040402c0161441d201914034140c00592003170390154002580e01c0e08814104508001000340e55542500200001403c8100071940da04213110f915623074200502c07040b515030141c254528415401500301410025100380d0703822591811b5680e10b80e002070101c203c060300c04024040e000c05030300e0401c441440b540c450030741420008000c040103460000000e214000b09800c1c03880c00c000084011420f00c100d09003a0a091041e0348030110302c00c08400a00c00014203584020400c5028030200103185074216024401c106640b0a515890419a106030038459821500403030040005041a03001403480c50845a540c004a00c01280c00c040164815903100407040c0d004014080e072107a1511504288003030b03034002082c1c5040b9100c4054081d541031103442c40ca55801e4400142c4462940c1c21160b60100007006407007039607403803100181950660b40000c0d16504031600c40814254003490442c1c007074a030020444140d000e850320400040c3c0c2c0c0810a111140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 664528489 1250 664527239 664527271
    0x3020c0409020103270605090a1e020303042301180e0411130f060e010803090d060b0f120307120206072a1a010303020d0311040603051e0901021201080109020105030708 74
    0x1003881605c100341c46600320a0b40403404000360030007500ba40c1d0054040016074115950120003d4681e06c00242d11298070081c604100541d8000a42140610b912071019102d1070701e00a000000c03004070f400300c2a2000d07241c05c0712000044440e100d0303000190003800166510100440c0c04a000711140c4000620001d05500300b14051740c1800080d01e400b0400300a2044d00e444062017031b507442c02c0da45405400c039000154140036418001404055a0b0100508440ea46860340c0b200794555402805842c3d1000c0c0018940780040c01d0319681d01d034401d040a60f0304003212240e038076600d0301c0426018041c243c00d41d941c8980203207803624660000c003000346160141c2000f195010005420190480344802c00b0074204010390315505020b030510312440711000130146840c0c40f80e080c0010900c1070754213403440d0b0300d00090b10b651000203486030302000101c00d07200300178880100010f03441d054000b03082c41507401a510410b039990310740c1e00c0e090f10058200240804d40070310008024905c1070406c1c42d80003140d401401c0c48 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 664529739 1250 664528489 664528511
    0x3070219020114280504051f0c08180603040b040201030f2a0e0901060c0b09030301051e0402160507060207050114121909050a020a0b0909040312110d05060a080a03020c0409020103 79
    0xd804c0440800049800490300b001079103005200d0024002d424410310307040068900001703100c82d0384404014004400410150510107009110107000a405041141d580c103250070040800003046038102d00181c109a2081e1940380755000c1c40c80d0030901e05103042221640c10000001078510b000410b000c00072107149201140d039800032001e00a00c00c603100e0480380c0d200e81c2400c0290440080c80282158002c00041089403115080700040da00010340107022071200c100004c0c041c0c400c1c038160034604003c1c48503030410700c58042840e00449100d9000c0342c0c2401c1c1d5400c01510720041c101c070094503403442488480400c4d280448541c4d130080c0b00741800016102200809400c803040c55000f036405602c6400701c0411414071243c160050400f440345a81080c0b04200011515100104014104a07082c56202415012600164010180000e083d6100d06c0ca03000030794000c0000322501841b5031140c02c00000c0311180400c114401c6034050f40900404032440b0f080c44054003455400301d04041d952200010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 664530989 1250 664529739 664529797
    0x6180606030a2403060e160302060a0903050a060e06090106030f121404080a12140702100e060c0c041b0518031903110705010e06041202060d0204080303070219020114 73
    0x340b040341100110080f5086082400440d4070048810b034959015003080701c0f4140c10850340b04101ca42c1103810542d501031507541210811440d03400104607201c0d050f00030007000481e0300442034408100c01120314a1796580314181c242c903124400980381c00c1c0d01458800211f45040e40002c1800a1403e102004a40702c03007400c43d00380e10a6001039040c0d00031100040c20000901d401207206034151400c1000752000010070a042e1160301c200901c00e40015200310055401031035030700a520070052501e0340322038450f242252180100402584194030707100c0c1c034400400802005401c54404c9540b0b0071705007440c0d03160260340a281c51076001d03854824001032200c1642c00151180750207110f580e45d0030035040001c40c264a88a000d8209070f0503c00fa80303003420f0260300c07048103803422076036500d00e452040d4825002085d2948039580b05400c00701d00001d40450042d80c00002540640101d03804c9880e41000380c0e51740b0041c4d42000b04005d00003404101010002c10403540500b0922402e03032440d030610545900a50f0f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 664532239 1250 664530989 664531031
    0xf0703021c0309020612040c0e0a020d05010b04060c0b04061b0504170604030807050a11100203100909020904030e011806080603160b031b0403120804060506180606030a 74
    0x40060740421022003071000381d012564807400e19818240000c016980c002805405a60460040c510070322000800303100034581e4241c02401c0c001e4400e052030900304c00100c080e44c05100208121806c0100004a610301d4030211800c0b20303402c0d6180d042c2121140d40d5501300c0b41020b00b0564045849243c00d0001800c01720340c4041c2008251a01c40d03803185041918101070000d0401000e03203401030350810004c60b8001d183c80343e100b919450401e6841c00d200700141c4000100361041080f030b00c601c49070100468003540c000d40c000c1341440545248560342e00110720a95803e0314000307401502901c04580043e0055290030f0f031201d01410600500001018203644d20780070b0350300620029076017100744201400d082c465000312662070000b98003020f0500d01941040d04c00039000f658000340e800790009007441d0b0b08040c0c50140d80d03c2840a000300007030a000416008068400b601c03042e1812001c240e01d8680b0101e00700c501a801d0b41d2aa0300fa03982c0c0f07030030043c1c15003000f040d0b0804140c903414a0701080f10022060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 664533489 1250 664532239 664532243
    0x190e0a0204030c0e070f05220e07020c0618150d021305040606030e0304120c03020603090102030106030501120b0f04031b0c08190c0e09010f0606020a1a0c0703050d020f07 75
    0x140c9882c5182400d84140e00350341d01115210410a0510000c0f60b400764011440e21410b041c003a84c3c44948203078124015110255100c030940090300045075001ca200d080380c0c01034106500311442c02c0110303000c00407a031081c603800b05003140c4809070054550504c0b0b401010f0540c6901c0c0c3c05824035286810709400d80c5d1080110a84c0e4148001050000740340c148035201c041d000d05e1034200a002d8088941c15030300d1040e401005400b045240006003000560038118015540c050805500e9041c86030045000c0d4000780200404a4109030000c00c4201d072403402c1070022900880c0c0f0203003079118088040d2000d103024200b0340800441e0742410540f9420001c441d03219074800d80d0f15081070381c038000c1a9401d145800004030821442c521003d008203184d040030303105441100801c0c81d010345071a0300907801000c1d20a00715480398182a00081d41c1900441d88111407802101c02c0c0380c17801c001141d400b810303100403144040021001d2108401103481000602400f0361101401882c00c1d640441014464114540c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 664534739 1250 664533489 664533491
    0x10b04170c1002010902101d15040506070515011413180611070c051e0907030e010920010f0912050102070c080303010512010204030201021c0318050c12060105030c190e0a 75
    0x5c94003c41c20900e4101e4411640c601d8601104100304804199a1040b80c003640d116088031008010810002c104036001031a006040b15506c16552410b076844140f0030116107038108680c800014030004840110000020041030030880d110703031004460040041301ca00e9220380203072035060400188184070700caa08045060529031550351a10b08000c031804940c103c14000d041c01c0b100d05024540c12411240b294004650506132035413411801c400500340281c0d468465070070540818180001c07040b503044150010006480c80000c00401515030306400040d000c002420b15508200200344541c4040e20302e8840c20000d447e040d4283c8607000c900800c2d400c003281d15000000100300340e00d41004000094140c92000750304243c9550000303903c42080c0d0505483d099000054003000b140b2a501c4081d4055a1000440781c2c1142c41c2005552004d01050705405a819505107840384400052035904030790004000b08201e24a02e018054031134600f4081c406d28043c09080841c0c1c2c011030401c0e0350302c10740d21144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 664535989 1250 664534739 664534751
    0x280b071101060512070e06060f07060b01030e010b0306071b0b100f060216090504060b04020c25050d020d03020a0b0c0304020f0a15141606050f0106020105010b04170c100201 76
    0x341481c211603807540070f14818900d1402000c030181e07000c100141102c0c241064540287c0c0c889020520500c201150004001350004919040012039030106100842c01e1340c0030000031124042e95400c80f9400007101c1e600d584100002003c00d48250000400031824a042c0c0500c4400c0d43e9602d5040348083c2c50943d8100030303000081c00003c07500e007004801800c00344018250201c60810354840c06140b40200518592584002000e0000c550015000b1900c003500440d034841c01001c01c0e50f211a5200c040f0380c07164014100c541e05074208504020b003600c100500c036441ea514140d080001c5101e1050044065020700c3e1400342c0420543d2070303580d20556026002c50758031b150910400c68002c1d0b1a0002c40d120b04890602840310081e090200541c000a504240d4651024030030125858003508080c051651443c2030313020200703c2950000b5020301e4000c0a242d5250341caa000517400d85109028140b0412001c1c402005044c040032031588851810300d082c2c506000219000c1503010403040d100c2400b40c4c0d1a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 664537239 1250 664535989 664536017
    0x313051009050a1103061311040b06070f0203120f0a050d0902040e0708161a0a030905030f0d0506030a030503070f0c0b070c1217191e0b0a0b030603280b07 68
    0x50b444c2481c8007000c40242105150552041800203c480030180513203a050010305501d8482d90320251642000810081d2030345854501188900d891060490281c040c1100c1c42886d0250314081e83c078906068001c0c81e0600900f42001c403403c1d000101c002c03020030f8036601c040b005038550744034002c07005603080080c003840c60404035041e00e80040c07407684807041c03443c418040041c030f101c1d07540d002200c0c10380001c815611031080c40d00310003602d03074658003a01e03601000072510000c400030780080440a071941d50a00c2242c0d140d02c200f64440c00280302c0034000c640c0c1080007544251181c03004e14480d2100741000e40045500c1d0321100c00720f039021a00140407480400c0c0300401d100c6900b56070b106104075072400000c0e549061306143e184142c0900a0845031103110b000d0b00e40c03400907800c03440c2c5142903040f01c4903241d101640d404028140c9400058040ca1000c28040b901c1040401180d104800140051418620a46a903c3c0c103202e0002c00300c0f115000c0d1a001400a4035241003140100d42030340c0e400c66881a14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 664538489 1250 664537239 664537253
    0x9030206070606060f140301230a0b0c0f0c030a030c1a0a0501090b060a020d080a020d2405010903110f0f210d110a02041d030d0e01050f0103080313051009050a 70
    0x1608100305100c0031130710121150884000b02d234195101124951840300c090780c000c20250030950646503014000900104216643e10040d005c03100c1040c040768120103508800030f84403400d292040c2d0701500544d60f18008a8040d03019558024820b01415184a20ba003090310408a01611951005a01d60004000394181406903052020080b5070312840c0c0b00700d03602d000e980d590302c00d034001d030502030504005400000c05505440c2202d10380c1000b8000d40c201c44000f6000d020011144a000644102e800719495104041d207200781c940c00203401c03190220110400008036000c400309580310341480821800c5460b0611500c80031945c0c0380781c03820b90074000500799007044030040034070301040140c40700e80071b1048002030309081d807a80503200040c800c400e1400c03000c5454804003021480d4400000c034035a0400b1980c0c85004900b20480080090752910024103a840700c080c8000341042005002081280400b601e10070601485082111240b40d80c011703001080d5003602a00362038a8100e1080c64003030000c9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 664539739 1250 664538489 664538507
    0x203040204150810050a110d060509010b0f0f13051e2112030c160b0108070602190201050901020c190305010513050d081e0f01060e0409030f050a0903020607060606 72
    0x20400c2d1442c12420000c0c01c2d6900c41000783d02040b05601c6101040c0f0003c1303154840c242000341d20340c07034560703c00550f005c0301c015260a100c2c10380264130210002502c00112801d9510b14180c003080b2924115541184200079004100c82201794000b000c0c000610b82c1c0e41d026020078913069148040000241001040700600c100080c03074442e1800310080d400c44560200b0410b407907502c034488064480d1140104003881b401b802540d00f1200400071a22010b001d69803820324101c8004204450305191511012a12441d4501d00011440d032904040401580218007400d2800010703c100c0c2c1080480c0800600711100424554052760000350040c4240310081c080d1a91101b004100c80c9014069942d40136510a04040d5041c10095130002190118070329014018502842ea20b1500c00ca042c05000150121428456074000c145120403400386410b00d4000c01c410190591100b00c11050542d0050b40c45078030407562102041001580400160f6400002d002e9140c000c41e4001542c9080c0100a0724840c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 664540989 1250 664539739 664539761
    0x10f0203121005030f211803030c0c0310180807030c151508010b06030105062d030a0e06041a0723070c0503070e06150f16120c0f060b060c0307060203040204 69
    0x801c250a04082000f407241b80b50851140c6030f50383c0e4408400081400040011034541c18000060036070b88035580080c102003403c1044054549603d040108601200da071100302140020022081d4000725811b103014101c03582c02410a00503203612036072a03000d003180d8034181121507036803801c030142001c040c404c5260142c9490700003002003c40c03020000f25039000500c0f640b403050000140d6241e071740c0840c0c81c1d82c504240300610795448110b00d410050403940c104541c454012458035030f8a04119500040c45c5000d076400c00d01c5140015800c070203808003032400400950501c2074240c1f00c0f410008403040000c40000f0021200b82c0c851039240384c04e004801d115071019220b50700c04d000074044216040c002541000341116401580c1c070850076500c900c0c6c092250611451140414032030080c591098269110740e10489014180212040041d14030b102c80c03207009401c000400c044200021b4031070f0701405822200400b81784c00c151401d502c80d80745500890701100c8680c0c010040c082141000c0c050414009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 664542239 1250 664540989 664540993
    0xa050a0c09112205060a03020a080a0903200717031902010509120c1212060f03010614010e03151003030806010912031b060f02130e060a0302010f0203121005030f 71
    0xe0020080384002c2e000d0a0701c03041e06041003005500d2494003a100b001c0040002400c03003501c1d540401006402504500150b80225500c00002000c03002c90388200204964581c4810400751503185401c8a040c88071040b010311481100008203600e0030328195072608803119001142d807000080c052800700380c240c80c0080c05680c10700b014010140710100310b001c01072910180007500c684240d0921454003541c0c85200500c445d00055200040c50003244561040c10309584000075082d80f03506040c01c031103051181410300d009a03c910390103907100d07401451440400804841c120a51003607c3c503031440c1c050703e02c10000d242c804070400400d80c11a518039030000d030900700000c00364039214041c140c0c025154001410482d403001703108003c0c0300c140c10942e0026003011082124030100b0204500952200d9040340800314140b800140c0c003d500d940d02c5200d00c0740075015141c01d5280d5401942c10040c8c905940c0c095010501c1141100500c0d854414411949aa90032f00700b5442c0009060a2042400c41d0001c03076 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 664543489 1250 664542239 664542251
    0x301030506010e09030d0c050415020a1502160b16021612030809150106120f0908040306110c01021c0b100f0f02030903010609020403050d051e07020609030a050a0c09 73
    0x120303002140d21030454090b080742d500310343e6607424140d00318450f0300e00010000e0f140640340010302c2e03480f102920a0310008a144044400f440409a9550109840050001440400d06004010990091321611500c0c8031212070001382c55807040b00c1150200e440c014481c0d18080d140d200103a0401c0000784070400000070b250680d041c16402602810354420150038400d116000c0f41e00c64800b00300c003000e04c000d104403080c0c0b203507140c100c001d100040d2004400d40c15418641e0040413a00544121034010754891890b0345014619503906010b0724107450326042c07030001407241040382642800180301e4038046049000e00d417079846000e40b080360201808540540080661000004d802001205044d07070b003030078108501156114101c1c40d40c85180445074040d403d0480002e1018176a4020300f0a0768415010f03510f20b160021000c8409008044440d0a86c0c00c203141e055000e4090705009120342c40c006403800f03180100a07004640380c04142802101c0e91340c8050740100500110113484c0c0041d10764040e09001c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 664544739 1250 664543489 664543493
    0x2130303092304180c032a120803040c03061b12020901080612011509021c050f0a0504060b12010914060c1204050309150a110c0f15090d0c06030615081f0806160e030102030103 77
    0x122300c1501c01c01055032200002140500130050340740401154000307801d000d50400000547c0150780701a070001c012801e51041d1100503109030081d03603075840046c3e5688000c5d640b0b030000c024509a400d480140035540e182c82d54169503422018500280201080142e0707500e640d4500c00421100c2d148000680b00e1510042c04004054110000d8000200100200c0c5075244d60916500824401407540d500500c0e106d060400c40c02d064000c225000e00401e4002c0301488448105520b58104071404e00f40e080042240c0c1c03c1682069801c160068010310031130341051820f1000c13410b0041c1c600d400c118440c0300410002e00142c1c5c002c50540312800002c1c080c1002c41e1034480840c18000480c0491880780f6000480302e004044110142c1e0103540d00201104008074550500c21000342460043d200020b05000010074001900c0507508450301c1d4035a94010303255240ca802c020580c011040001000204000c00a0001000c010b02d0340100b03003202e8002d080400e03d4a000e0075161911903064080d034014401080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 664545989 1250 664544739 664544759
    0xc0906140a0c06020c151e060a0501140310080307031d190b1c150305121306050f07060e030306030c04140105012102130303092304180c032a 62
    0x4500c41d0300c9500561901c0007904903904101c6e8100e00c14002906c15420011003401d800301d0180c80681605011211703480e55824403095441d50700030103010892071219000995040d50042d544800b03506500500c03643c850492608640c0082e41c140d000980010404000c859070260031081e050044802618452081c20031b4404500b840c0706e01c04552a011840d5880031001c4030381d444c20022090f00c10400c454010300c21440200e641d00041d00c8034820210200340c0745990008813000d0100c0c58030307001c15440c0b17841d80c11521603000c0d410a4010520a1140500080481c0100040c0d9603840c006161030385490f20034145400820305100c4c1c132a509005102c2100100c0410641c15075100b031070101850f90347ca260950319020740101e09820b40d4400180c0906244000000c2420780c0d1096650703410b9641d07900010350ad003080110900400c150602110242d030b11702588101c40f180341408801d8190003464580c240030018079030081e41c1c40190351081911040b002074811030402441001500014140f000810b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 664547239 1250 664545989 664546007
    0x6081014270102040915030b060303071110090b03040b150d020a030b0618130201080a050915060f060a11010b030d0507061820130e0a081c0c0906140a 66
    0x101030910200761800408000e4044501401444000b841842c5104d1210300c0200078a01c0141c0d91800e010011600c140303808401ca4249031740014450381c4040344d401c10000c1c45090f801d070080a1002c01000001c0748a00d81300a148100c2c0100c0e440c080700d113014212045540f912548180c032a03004e0726108401a61105150011359421525484d029038031100820001051076803103408803d81d1030b041142508020408400c000e01c01e81c1c801d94940c03280040309066607019225000c1a800107800b4500c0c004540420700d0b03001e10002c0c0b05080e20405280407840359808070901d01c0020307000c4540b454034a5424020400420b405400802d58843c2e001002040743c0a010300042c2803913241c030f415502c181071803014483c46640001c1121428a80daa1482d0741c1c4411950381e00c0d02500301184010b0891426200314003161035417801408041e265580c40d00c595070300110741301c018840a4843d034064000c1030701c6400003141e0142c4940c171459080075405014403141c1c2504d007201e24410449004641e034441c9802c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 664548489 1250 664547239 664547281
    0x6110a120b100c062c010b0402031003020409020a031407060206150a061101060801061502010507080906060f041410050a15020c0603180615010e06040506030c07021306081014 77
    0x2a0303c820020728094000d4031140d000f01c00d0054000203498400d28039030559400001e00c0d0002081840030f0101400141d000403515000325500e020420005420140c025402d510705c000e0a10b4086500e0307689024901800c8245129981d1020005025840d01006001d0704620145a048041074407000010341401090203940700f00102c81002402e500b20075008030b4060f0240700000d100c940c1e120145040b13080d4620711030078019030030200410300060164442d64043c110704400340c5480e56960f014040b10040420030f06801680d00c4c08856002085c141ca600e0240d07649101d80013085250108008010b040c60300032400f460b02d100c03940c1003825000201d0745103e0209880840d03c0341c0d10304004115500d8202c0c2e0482450040c0d608000c43c41c03201215448054000340c880d140c0320030204050010314000c0340280e41d0011000c00105203181e0100c009004054401880c0f069000c0150740700e5002c1d19510742c007100d41035220101c1d00c0c0d00414103008040302e0f25000f101c4070f89145441c1141c0c0d0341d001e100e4008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 664549739 1250 664548489 664548497
    0x50d060b0c1b1f1b0620090f040507021623100f0804031b0c080708030708030c071b0e0a05060111210d020f0304020a080307050d1b06110a120b10 64
    0x70f01000d82e402802503c82d0300c00b0921140440307034000c1c1403000250255001d505818180041820303403018180c415144100d502400c0103850189207000e010050102410030070540c0302c0c0a01d120000300082901102a10003400012181ea81c3d8000c2d101015003296940b40c46007074901891030180d54440024a201031b51481e1000c1c040c0c8660501791802d030104040758050b000031941c250280000c0d144c03250304032515a0121100c1c10fa44040e01d0f40ca80c05003410080540b2000c01c04102d007a04020060308070903000d02c02940c4a0070700000c10800f00509075004521704415002002100c3c061440b40b240d1200b420300384400150506982680c4801c556405000e40b404014502c1842c04000300c1a00d0b0300c10b0515500b10755070341060700e00d60115001203400328814850703c0c03c0420b00d10300100030f4a001e04da00000a00c1508a480819546044a4181040e0b03c0100c040c1d05400315499010306440100481740c0599940310141d0020182080c032038094010504101c036846158803031030500c088004140c94 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 664550989 1250 664549739 664549789
    0x408090d02270105010e0303040b090406080f0607020606010305130b25090f0f0819080c010c0f0e093102031c0f0f0e060a050d060b0c1b 60
    0x540000c0c4000c0020750402448040010841d00c0b00c1e040210100300c410000e00741ea0383e1400110f40e075040050380a0b8142d0030502c010031420114601034040d03200001e10100e1015140d501e1285419501c21280c0f0155000106022506405021041c2c0002e8286400d025901d01509404c0e004030510f440140031000d014009a44a03001100ba180c41007a903060008034900c0d6148014030091040c000c0c5403044816420024003680607413038103030480f40007102405800c1401703060b0340c2a4001c03611054030403140400c0100e0604c4801c0c4902600f000d102d444008081c4840a001401000398040305409501c00d00e0610448561142940714805a8400d0b614110b000b030003100d1048070052040250113108151400b6108101000c061030f00a00d10741c1c51203800d140906040700c10341e04608419010480001e00a0b4490500400411500109041151070a810007115404681c096406001c89080c0400c040840032010301c111403000301c82a1030741d102001c0c5c010000d4140030940307650074043c80e42d01e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 664552239 1250 664550989 664551007
    0x2090f10050d05040c05120105190902060f0f18010c020d120c080c100c0f1b0606031e02030c01090518150918010b040c02060601031113030302030403020301060803070b0408 76
    0x1404954400380b015106011a09013880c100310010f60b28000c00740325407030032070b9150a6080148107051050301d01d814449080304007004484010801d581042c0d800c0003080240700c004544680040c40506600540e2942d1211405204400d01d81c072200a203041111000502c80540c0e503005140d40215049181b680c00911100780c29504a100d038440201411400700360070302d2010000c608204180000c034018010403156140444200a8544041000c6102425000c141a0f40000100041031046c400080c000740c0300d48441898800c40c0e00800041002225030780110704090100a410792401e0030496003160816001035801c12882070801482241900000c400042400090280380c40185c5845a40d060801a408103285c140300e10034160340c2800c1c00e030071003410507129000c081555903002e40029181c01004601502c003000e46800c03c40800d11824180c01450b4810100551184d0010b590b120f10b103105140c03d541c1190302c102020740040c081003011800d513155050f4001d900c031608990305e11505c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 664553489 1250 664552239 664552247
    0xc1005090306070f031b090e13020d0308150a030b04052b12021e030a050114060d050403111f0f02032502070e0f01050405090f0c040f23040b0106020102090f10 70
    0x100b4003500030003445034040b10b0310342100c00c842c20b4031900e0308281d802707a0b10022030510700311569100035003000c2111040b0002c80d118403013160700440c190301c02098184140001a400b10035542054039000140e40c03d01003081010004c3c0e80305071400e40111115420b05180c10f840d00c030411903400301408410419990619050fa04592500561403504841d803000140701c000b0581088800d840d509140c040040b4a0003030f400c07080560840d004018038640b04440250a001d044007410444c14029100001c041d0034409010040b94a00501b41c4840b043d00300e9011030060b18030b0082c800b010f00b40b040061100c10410500078201d41c4810011134180d00050100072441c02c0008e074407005e819220041840540741c03582c80558100d0b00202c0e418482c0f61600e000b0076440d24480e0322004441c0e40600318140e824101a00407880c543c1d210140080c0e441143c8600184c07a150703036410385642032008810041003120510345140580560303c003c41c107100052010440da10b03094400203119805140300c8505051003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 664554739 1250 664553489 664553501
    0x40203100c11010528060503030901030b180109021905040f03110a03170301031703092a0909060f0f0f0106030f0f090f060f140103060b041803020c1005090306070f03 73
    0x454001304824544009030709440c1d2054613807000303600c03451000500702c980d445c002d00e0180e600040185160030141c10040d0003d2a9400c842504150890149c425815482d40301c68024210054050ba8503038180c004500441d40b80380422085c450244001d01c074140d252007520b02136a9004001440340aa80c000150081602d80d100804012034001802b10000c03420700590304813441030060006401c02000350b0807940c0400c40380074181398095022040c90003d0404131203081403880701e000b400c40744000c002c07400ca05021121102c0d1640a079013848540c0b10b00d110402c0d4820341d02018500c071410102200c0741d0000041c891030040544524142c1d403d910b40368031100940d0700e00101000243e0350791400d203e40c418000b0090ba0801e262010351011808140100c5018120101c4007651980c02d50782c48030000c0c0501d010300c0e0b811955561460b03070026043c100c2d8600c2070340243c0007401c406010300c04000c0c043c10100704280c200704c42480951a80d440004209410494500300886800c0360701c4000c80c01000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 664555989 1250 664554739 664554767
    0x80d090e061801054606110c01081f0b07020a05030a030f081f060c120e060f07060e01060f080118020f0603042402070506160c08030a140c0405040b09040203100c 71
    0xf01804c510032aa1640107801212511002907016a0f81c0381011f941000b2510044e903046e4101c911080180d600c2400c24590052a070465500f08070b01d201050110100d00350000144120001854825880d041d0320000040c0700890060058a03000c1d54014003402e5401700100a1008580100720150311440d0b0380740410782c00740302410803a41d81d2580240703600d00d01002039490307100c070680d1000110f21070b062024020101811091030501101905207240e8071559055542c140c0d54034084010a03020300900c1d0050101c9103d66003803504028405084446800030745c14882d0400c03014500580704e518131144120012200561207070b80364106100c8400c01e034890050001d4415110841c0d401c240d030301406186004104641481e0794160400303e1802001c41c800780403500c0303401e007640090711580041d41d01480d01840840e0844000d4140b42c104a4190b23455007490078082820701140c00c00f4454a94010f400308c40540c0c09041c90340100313071a9651103410505554980c0420f9660034060f07041c00f84410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 664557239 1250 664555989 664556059
    0x1b060a140403120914040902101808070b03060a0e04121d03010501083702060318010216060509011a090c1b01090c0e0c180a080d090e06180105 63
    0x311000f000100407015a00829010b1050744e03c40c0241802c1500c80e400d0300317a03405440c003040c0025510b001d0340d689a600f801b4440c43c1d003002c400482d051a0501104000341000e0b071006480e13050600030000c1c40c01850700100303443e00043e403c01010420f0b010031490400b110381021b800f010300700c00d1241107540c9030030f056581542c240310002030322480000704401c003440b0a11612107140c00700b0300301d21006080060401304070480794007103001614001c2c0081d80c000741c840c00a00320282c112101c150036a0042d072440311400306403060340800d02c2054000c0641c40401240208150104114480c1800780c3c1d03014118050800701000901d0ba9443d0030486500740c881440c03400007405400c00d040e0281c08180000c07680301008040000b034150301c1c1040785014091441c40306091800f1401c150f230760030821100d82070380320302e04550014140c90188005005859269104001c0c103081207802d004556001e000c0707a025005000e1664141c0f001c4103902c2d41550404c451314041f007942d43c0c3e51000707508154041c1003c42 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 664558489 1250 664557239 664557263
    0x4080d090f0501330605040b03070e09070504180c051c0605151c0605060a0c02010315060f030501230d062d050601020a12030b011101020301171b060a140403 69
    0x4070030540000c0510401355039541848141e06804810303402c645120306000b1035414401031220507100400f96a002d44d891800d480020900030018204140944035080407410004061218442d902c00d151800008505e052048040e1034400a240388075400200c0d080c298800c8910080700015009007000744001000c0003035104909080709034540c0071540d03000c5022200001c400c041c609a01490088800090190b030808004240c282d07020880244201d042541c1d86460740344400c040e810300800f901499540000a640e541d03005401c0f42e1b01a0800c0c00c40e849560840e900c1c001071102881c0c0e12034020b645c120242560b519000c0090040c0d910905c1c008506807410070560403091002240c5a2107215040c481e50300e07040016600e44020b5807000e820404a103920284090003500406111072041c900356411903011845203089800070b80000c0d140159052095024420411005840e0b140100040d41f82d2024035001038103034440c0320400024070503022600d80004510b076082d10000e541041d079044d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 664559739 1250 664558489 664558511
    0x209041a010609051e030619020702060304030e120106050a090c0201150902130f05012307060e160b040b0415020307081810180b0912031801021504080d090f0501 71
    0x3181c3d964042c480c012070455011000e80129481014001e0a002d005814140c490740108a411030410440110240c0c0070099600141c85400c0114411030080c3c1e00e9070061000c05c0c04128140c06580c40308001c980c1400700901c0503545000158003120304260b40010012886031090740074149012906140c0910054002907014140e0010b0428907203080d007420141e9200c0784410910129409003900150720340d04201c0702c0c01c2c9400c1070450140a16400d8504001d0301d650b4030301c180c906041200c9415003200d4100c4000742100703210180603140201c1518241350401942882c5402036108030082519021060306c4418001d0045500c90340e0440022a82c0d0b280d00ea00b00f20481e10780c0c0b1103640c000c038506403100070014420700c403011030f60141c03044500d003e030303d4401010020b412800c1c40303540c007034240d007509402c0c0300003000101107400ca048075000d0080c42038400a401d00d104100b051441c500c8a008010018035280100c90a200b1605400542c0b011a401c241c2a50740c00c8880044c04c944c80c1080742c042d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 664560989 1250 664559739 664559747
    0xb01050f01022e2004030609080c0307060b0a12110f040b15120703060810050c09120a0501272006040902120a0c0507020409080706090f060f05010e040209041a0106 72
    0x492001643c0a000000001d070004514400c0f914201c032142e50240002e10006035a5040703103000d42d0040c0720450600744003082c080d040d90312100048415a983e403038030b41027900380603d5480080141c15081e008141d000d4450111028000d440b00c2e03c510729003140079917595550740c04103265070380241c50188e00711345020000c0055885030021000b845850b03000200100d219028080c1030f200710001a0901000020300035018010140c40d02220340c405000f100d8003074860900c00341c24035003038000420020300c1c2800d20390700b140c2e02c07140429641c06035501e1480d810390000c035001d200a580200c032081000108e40b02d40849000490080b64041d0000070001071a15042c0c0103408456003138100303c0f8940d200c02c09078000b140c10508088003c15024070211000d40380580c000343c0c1443c054002c40f03140400e50340d6001700315052504202d030a1502e40c44100c041c070030b913407194140303001c401d850821280d41402c100c03c2d41e19400800013881406c00d08001000c003c0c0c1c02440c02030003082881c0d1190203503140e0b40098 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 664562239 1250 664560989 664561063
    0x307030f0b1e061815040f06050a0b090906210a08030103140a020916020a021f090b090904020d1505010e070f0507081801110d0206010e0a090b01050f0102 68
    0x82e01ca02c2082d40d6542e120300e0074000d424040d000090004030000750070030202e002c100006003280c90f0740181d00a0300b02c0329191405428103104101400107000307800c00d4100100608141c203d641c2c203403130030300480a1a885200c01035401481c100c0f50482003403103440e0144004040040f503082c45010341e80f441c2d0104100000614184c0e8866460131b02c80204107080d03642e5407403c6580107540405080040382c00d422200507445404400e51054a01340040d54000c5403482001040524903040c0300d40c03400c42d030203901515040140030241500b40c54141202c001078940318000c3d2019108401281070f90040146d04511303116540d03507081080c403440d0b80d50440d4151603c02110300d100070807201c429442081c0c0c4078000310790000e580308a1700707402e05a90705103c0d0745409000b101e0905000024860210f108420010224101860b1b401020782d581418819113440a002c1c0003500c14a040035a1034001403a101c0c042e505440c01940c0c035000300806100102d1601001d054610100d500e5000416012a1000560 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 664563489 1250 664562239 664562251
    0x6050f0607050304153515010207210308070906020a0605060f09090a0302060703090503070b06030f070b19110a0b0a15030c080105060d030f0503091e030309011413030e0307030f0b 79
    0x880c81e06c1001341800700f1001c10004e5100c0c890301c65940015105100c42c2d502400220040c81155501034550548101e0800003420701e4001d5000d1007100b404166018000b6680300b4002e1401c2d100040c41c04d480a96581803031f48000706403d860b00002000d5446813081410000030090890f142c84c10700341509500d50039181000d800500034800041d600c140240109103801d0b9002c4010b40c9000b02030784030802c0c0c0c0040a04550340c07500480318200f030101d00800254002c1c0080803030884d41c400000300f00d1008000030361892403d014840c4202c1645800210701c25100903001f440c071501c643e4560030b0381001001201c003140c650b0040fa250202c10300c2001000b070004c1d110003000030001030300d542040002c0200c0c031010040c0014011450004401d220700c001d940c200c2c01d104121510303d10354200602d26220310105000c49940040104403180c042402a0410301600c6801050b541c140300c400101d145481440160502940c904801155102008564001d503006550f08201e8002c91510054460043d104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 664564739 1250 664563489 664563527
    0x203030f0c16030315081908030c040b0309030408010c090f0b090316090b090a0b0d030f050d02160209100b0f07020303190207030c0e0108060f04020d02090405031c06050f060705030415 81
    0x1140030300700001e19100c2c404000c8180040c0c1c11052342c49021030b5000600300440c0e5041880009800d041c6c03d8061402001d03600051500c940c00c00301c840f07003168000c20402080049a0100700004040054a001560710114409a890070801e01080c9040b603038040c080141004088001030107001c607400410003000071224016262148132103001078641088650390b000b10318540f82c60001e130050410740d0764503400e41800c506260072101007070b08a8201542d04c100d00e44088034940218a400d1540e680d020900d504046551420249a000716000e2820381c551038885c00038546042d56000c00544001450740300c0007000d207145800c0001e40700c88a6200444a0418640c80410220780040049050f50302c0c2400404c80341c3e03035002d801c0a90503c0a0410ba8001d0f100303103da040980c0707810b007070039120b680200001e50740c90a100d01c1010491841c0da03000740c40ba510f804e1081c0859960740d03008241c0c60000f204e28645440b8241002400c40c4a1580484e40d0b0f0b00c954821f5043c6203070801c0344105e1401007410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 664565989 1250 664564739 664564781
    0x4050d09121101210203010e04020103060506070c0e070527102a11030303040b041103030405030a0f0311100b0a05120c0111120408010e0d0f0203030f0c160303 70
    0x2008070706005500c4002400c4040c10010440c0952090382494203c0141521625a003c00600184201d074420b0308903650551110042009650b098010071000b4001641c03114a011544e403591551810240610340448403100e012030726440c400c1050301c00e29010700c98500c9000f040b10b40c1c210300780048035030042e0040381e000e0308014005003c1c04036a4504a80200c8440103c08480602c0c115a0404101208c851140f8002c0032016201080914482d5108620100003030800782401d6030501c200c0c0f80014801da00400c01403000e900c0c081141121954030105d41002c0381c82c1031600351400c0d10b090ba2001900c2c419400700400d0214550041c0c0d950950603a10021341985413028014402c22014111882d5480703007010007130035440391076180610116941078844540001000300e81c143e014ad4460718444c2c3d100c461000d800b40080c070011503404900e08104102c3c01e09481e010303480b8040244414541a884130024040700c400f0021078128005001d25520740c0d6420345005030040034940762909905640c15 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 664567239 1250 664565989 664565999
    0x15030c15040f0e010b1e13060203120a0608210c01051014030d2705042c0102070b040312020d05010b03040b1005150a0509040c080910020307050307120b0904050d09 72
    0x102e42d6a06071740c0c1c40c00300c4904d031242e01d45e90420540c00c9808042440007003003005066501100440c9000781685a020350b61743d1130300115400c0300000203000d0703030405880c002c000c1001038800908180701d10303501c4a80b0032040c2580d455114450040c5c0380c07501c0ca1542050100b00504074001007a406803001600580070141c0f022003031680e41d89408200202052410b82e400c0c0c20a000100d91000e420692001001d4098840011500b500e0300c10726149081d00004900c60034a5090520703481d14a18560021800c10030540c5900e03403410005800a000e000006941155207212034045036942d1800c0303039040c040d0f544d40b004000c185910031541910004101401b28030341105545d19041141d400500341c40903d40303140d2031004983e01062203441440010040d0721040d40702c6016042411800751180f0355076183c802401c40c205030303085641d9002c2c07a2040040000d11078011040c1c94001003d0b240100080b075144a1510040007a5641c060348407001c4001c2000b00480000c20650814517583e45150140d51b074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 664568345 1106 664567239 664567259
    0xd0c0f050d020318030c100509060409020c0d0f02010b09040305031f1203091d040f06020705030d05060f0d0f06050a0b130c090b1215030c15040f 64
    0x490303404680304c4891a00841440b041d0f02078841e00b508500003c3c0681d4805200e8000d105003c580e03900c298035a44145da0103481c00a208640e60008001e240355100c100e203180c04001145041070f00320142c810700501346509006010b00b0415101e96600380c0701500000c00e0740901c01d500c2d940000081106c100190700400f9040c642005150450a0040ca110213a8001e010b0980d50360141070100d4401006140d4403a8102c11928540c90b002d143c00400391003030035070141c100d02c00440c07010440341055000c00d00a85040b0350004809c000e6a0611542c00c4c003145003d40707140c542c5403200000c1201900a107511620f060000101c0d0041100050744a50070040300725886561a40c8001956402044050150913070b101414188800c0c242e40c000c800304c00030600c00e00e0521620300901c040d20304100000b4031842c0104105018070108120b0074054000303200d9480d9488419400084003402 = true := by decide +kernel

theorem cover : BRFrame.Cov 664388489 664568345 := by
  have h0 := BRFrame.cov_init 664388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 664388489 ≤ n) (h2 : n < 664568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
