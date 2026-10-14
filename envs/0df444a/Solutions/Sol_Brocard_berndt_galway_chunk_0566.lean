-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0566
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:28:54.542202+00:00
-- url     : https://prove2.me/submissions/7ee36e2b-157f-44a9-9071-7bf48d0d1c60

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 101618705 ≤ n < 101798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 101619955 1250 101618705 101618711
    0x3080d06080601030812090a08040510120c0f0305010e07080402060304060e101a010c02101b020a03030c0302120712210501030605071205010803030a20030a0f0e010b0d020103 77
    0x15000010000301000e07007061140c0c0c401c0d10000070402000e400100482d112070351151080e034841d20b44e055a1040e8800300200b0f455402c1c0814002402c00a0701c00c110340c000c1d890f08400e840103160124003245d1801c0c00c008001100762195102e21070300750054500401c000c0f22850300b5864640e4000b03102035406030000348200c1c8004041401d00c0440e81020320a641a0300a6550b196110300104000740400c0c460261100c496945207240c1e507002d83e01d6010026000342c09550410494402101c540d1501203076014001c503a0040000035885410001000e1480394490441055090030041e1412074003180c91444400d00300801c600007480f240038040b40814505000303184d90005801800c1d0007000c411050707840c41c5403200000c00c4c42070382e4000c5d40c010240f50721200350b08004220702605070784090013100c520b94003c10110754414000c0c1c3c0000c12141c1c00742440000b80360042e00c030030300c6944240e80055175551610038410008100748a101200d001000c02044902c25401c0412521001e00d1006030605039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 101621205 1250 101619955 101619967
    0xc020708100903050c01020301060507021314040204050907030503070602130506032a0714060a050a0c09050d0224030f071110050705040906230a05150705120d020304020414060a0308 80
    0x200613420340b904100020700a54583da15400c00804a402c0306109074400c0c0d04a02c007100380c00d201481a0600c00f1a441d40c04240e950fa5602400b02030305018003d9005c5101c3c000340080400d0342480500704080c4269005039070f0310b440314000400e0350001d4201c3c1348103280070814818030410300030040b0050072040500400d4116640c01c403040a01400300b014009188100003da10a48041071040c45818204020081a06c07056003003001c4400c1044c40601150a1960a0003246440d0451400c01c51001b8000031445a149260110b0079040f0406104a02e801100307001400c403986150b19440212440c240581e14191004103550f6000030141a1072561f4031004110094422030413a4050b01e844d140c24803000c0da40300140008440d894a4010b170004c0608069020f0340707490a030b0343c412500010a001c0c00c0c41e0760a4001c01c0a80d00035a0704036410f04c10860f9405404521310003405059a40002c0145c5070320742030040c0001c0e90409002840b0a282500812549075955910101566081280d2a840f85 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 101622455 1250 101621205 101621207
    0x3170f0309030a1103040f050918010e0703030201050702060402060a0f140f0405090105040501080601030b07020102130e040203100c050d0b150d06030314030c040506091306180c020708100903 84
    0x881082249011a500003003000840100000100035048907070f599062005107488810f500d0b40200c0c0104442a12042c1c020040c03407411129042c3c028901e00d11120000c88140c02080c211000e000740614242c114850820034140c083c400c3c207601c02907074005041149040c0d4005601031041800407014070054182004404d4840c401c111010140b64041c40e64803230210a84140e2504288a01032241300d000c0c0012599042a01032503040700e804500820080e403c640ea041c0094500400a038110740d0309002120810000c9003e110007072921516025003030406006043c208900000c040071010f003840f080d40480d592080440788500907202c0c000070f05184000014180c28282c10056480031303004103105103c401c2c0341d030003e02202d1103500c4169502c54040007441903804119510310505800f80420042410103000a01c2501001015010300b000c04902684c100e9001e50000c00d03c1c4170b500180c504810300a44998078154140d80018040146442c2071503070744441c640d1041540c1900e42174110205 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 101623705 1250 101622455 101622457
    0x402060d09050601061112090303310f060305070201020a080610020a0f0503030a150f05090604110a02010501031e050c060f120702030d0605091504240909020a0e0c040317 75
    0x26030382c848242e410a50350703004010003201c082c2101d4a2a40030b416a142490104141210180040540a10b050082c0d140441410120b00032140061040000f03031915000841c5900c1c0001c0d100891320604c0283c02e0240060444800a20200035a84100700d405002e40d0048515940880203c0e40416000c11341d0720202c2c140035160000402941142d8255000c000d00800518410900742a04214004000c401c04500b03400300d11401107000d81131242071000d420813981007079001101a201040c507001000b01101c19a104194000c0140d42d144010f1041013494880e16121000c0c9005203074800360140c035405d13112110a82c10500c0f44078005501c60032540c00000b40c1e0440c0f6004074030304510303280c1004040d449500c1030140e00340e01860690040303030790b01c2d288040c180103000101440103140b0610050200070454411170940070080b4501050405140740b10020140002403004074526005205201d840613072034201125040441040011944000e03095904403070300700b01145910b40080601b4001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 101624955 1250 101623705 101623721
    0x161101030b060d05010509150904060b01031d0a0203121e180a0303021b010c0c0b03100f0f0509090f331008100e0706030c090803031e09150402060d 65
    0x20078086509003c24100d5401541202c030b00707881a0010b650307901c8003801004208002d90758410349510103e001f040150744410640350040c180001c2c00c103041c0c061070300f0501c00304100b00815446040d4a400b141020f200011241484c204414140b410341c83d1000f10000e01001c0e140c140da03002080e40c03600c0d110008407c01d13020501800a036410f64582c20000d4903808003410b4001d210030b54643c048141d5200b50265905103401c0308a0204240c00c0c994100c0d2140d102809008400c020100c2c003056010000c420348000340020380e07000112a24220620000c072034020040382454005445480d4062008034040401900d082d011440c1c8103504803805c0c1c0000381f00381c00c902c51029404100807403458035282ea502640e0707041e030407038030388541403118081998850403540c1c00c03d0b0070154041140e14060f8100c0300d603406440c18800d22043c0c41d9203496140d900100d51800d05078010b42c00455003401c40c41c9402d900315040102031300c5010f209840c0c940303050f8005080240690740c001400d401f100c82541c81420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 101626205 1250 101624955 101624959
    0x703051c140d02040509070206041e021809070906050301090b0610090305031c050a020304110111030f030a1a0603090d1206050315040c1509050d0303020c03070f050c06161101030b 79
    0x51a10580c2002c58025009401154007070030b080350109510500015441b44a6548410350001c184645200d0440380a134a100c101d0700181c0c43c40c1105003450040c0071091062070184000e1040ca4503291a1400340c1d0080d9118078003d0b4509906400031554414019034030130f400743c9030310015458981045906e009158406440c5001c041004410300a1036041408076140c0284144001d469481d4101e00701e00c010340340100760340105c4c5409007540d4042d00000d0980c81c00d841c00d6a0821801d49810345469100b00c520601d0503540340142810032940300020344079007074265005404c615000c41001d41d64000342c030000c4184041e110802c800b510103900190080d00018090b503408032035038510101d11080645003114554540c140c08105282131101c54540c017034031581c2e503038011450308040c8411030300d00d520305508140c0c00308418404014100020000588614903045041ca5241883c03420003d10a820720301c14001080307c440b80c10003050340600c405070407a00400ca9058a00d006800a06841c1e5000c2d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 101627455 1250 101626205 101626207
    0xc0309030c0304031407090e0c01031d07060c1509030f12090c03030e0a090c09050d020406090608031e0901050403060c17070e0a0b0c0d120e19050f0703051c14 70
    0x4410415017100710326403440c050040713914040c1c6580e540020396141c03c402c80311650050080300250740c0b09401004410a4000740440301403c13018006041c1181038003c48041020301e0000000c10800b28a01425042c00030401c0080142685e00109402a003142c1481005521004240e25244c2903101c0c400d80c0391303c42c015501d026a070385000340018074031100c118072a800c200030004481c03849000d131a07508602d035964043c81d6400c0100308240e0218804c42680c0055803400701241641543c815100502054001503844844403408040303c0000d0380e805002404040c41810410f98211060f98207981e80302901150415100d482191a074000000c44c0511400c003a05000185030009213004e100038040e00e40c5103000b80c9aa60780313a07061140c81080002075001c40c250001030381c498034100555001c2c0709804a48500c850b2480c620b880201390800c03820f1500b0030004004c0200402c00e02da10781da860380140c52150304d1900c403240c50f0f050f02a0184c0e1400300300803902c0d404070711a041d404501842d4002d11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 101628705 1250 101627455 101627459
    0xf14070c1403120f07061b03021b07050307121401050c09180f01170a1203150e10260601030c0504050606070c050618120d0201050117060c0309030c0304 67
    0x20200120041c880e00c0c50104000e0405001d5003030202e8445800010084107501e00f41e45407001c4040e517030043c17009540c461380c0c49015006c1080c04096a121050a41d0707009170b2250405a00410b00304401c480401440e40701902c20072103a01c002c21100211818644a03921040c2c0a00b44401251040b170081100b5500e4070007005040e204090261201080695070170060400d1080030000c01e075003c1c0c03017110380ea5150304010040207507a401011200340080050360b213101129600c0507030010320f4450903008640c0f40d008000c1560400c0c042c16004150145c0e40802e2820300403909001c242103400b8031405160803a680c443c400410303008040d440b40c007100c200e40b42980c3d00d003402009050b242c00780c64400c5003404041805850320100b07036030905411400c0b04410300d01e4401000820b91101c406000440840e5507084442d50340c601100440000001c00780c003100b03517003400003421500141c202c10f841c13101c42e07100304500d2040020303030fa98007200d4042d06559070384400d0081071650141c1445880c50740300010300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 101629955 1250 101628705 101628713
    0x110d05060f09120906090609031504020f040501060c060b030708070e0414010c08180a2306060901080a080c0a0203060c04090b03011112040c030212010903080609070903030f1407 78
    0x10080c82540c0350000031800340c880c80c42d12502c035a401101e1400451090010b0201c601d0b1a100410314841c000389010720700014100460304040400d01d9541340c0382500000c11080d42030000d1107440d208800c43d02044258103014010340300da000070300c024100300d550390344510140d1801c2100401500f880e104881005035500c40c5000001400ca031304503400a941c50302d056104405008401c00003e00b07440341c98891fa10010058280041c1c009064250b100300310a02e4040788100e2a4070340382101c0b007150361382c0132410100c84510b440300150a030341c06017010400402c01a80c000c5036000c0c3e1640d0200c0126030321050300b0041d505d000d90303250300650305010340c1e0140308900c0394100c000c10032110201401d100e510810030816080f02d07941c0d0f091144400341000b03010071040340510825402845520300022064590f00421a52441c4002e0141d440c3c1d5104ea00c0402c0c15004035071780742e0000048400000915201000a0401c0920300c0003d061001241d0711210903409041c0301d4400d22226242152520300b5414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 101631205 1250 101629955 101629963
    0x301090b0a171e0a02010f050a0203070803010603020307020f0a0803150d120c120c0203030409050711060103030f0306091802060c28060b0105030f1b040b0409020703030c170a020304110d05 83
    0x40034000c0c3c01d803020400d022410000c02d071103e10310303016195441002213262050780c0725401590a0421404100600030006110764003a502a004940d0016105d190050001c2d280c0300d4110301d0181c06921030440b2000085982c01143e13800401004026400c0d0400c5001c118001c803288001000c90030848284640d07217030b014681c5008240100c01211031242e40c01d0003500c01003640034001c0d42540003004140034600a44e00302d190041180d00d0180078081c05800f4842c200b003400c4e041140014040645468966814040c0c8406447c81000c00c00407141c5c140002c90340505071880090003071030042144001142c092050340600d10001e0203000c2545a0f00129220b070a48206045401a107010345010b03d551090741543c1c0301d24850148422262a01e05030317200081021004150b02d42d40c20403010500685000140c00104501940561982118031b0090f059405100c00b44003001081c9400c0e0a070090002d09a40c0c0124a10344016a43d0311030b4242590100411000c040d082640745080700c080080c005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 101632455 1250 101631205 101631223
    0x60403121b1709010905040c0905041104080a061104081e070b07030c020111010e0f1005161b03030b0a140102010c0f09030201080903040503010e100507020706050301090b0a17 77
    0x141da0840084126084410016407048001d0b080c1010009001c02984012009022071901410440c000542c1d4000007030640f18002114000110300d410700304198100303801284e21240000320581e0800d810141465034510b580310025241a4452100b14034500c2e41104460250100c0342c00e4402500001d689940e44080940c0c412109209409000800124890990301b8403a0706540c0c078041d00d0000c0c2c004582040000d1098003155680d920000d00c1c0707000c104a5490702c0060b490203025045054079100040fa80300071311405a5500003a480206142e0000c4811042031030280003c6180c222070074103d00500d10604803d4008590910104900c00005443c41500b40309074000d000382d806650301220b82c040d07040030500201c2d5107102d01b41300641c01201440d40c409043e004480c1400c0c1e540b070002e400d40314001d03042c15060b0000d08003010341014034090540e01c0b100364001050400e140c8800203082c0c0c403051084622090799440b40d03210319034500c080c02c00100b22003400b10381f01c0801003202c40e407902000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 101633705 1250 101632455 101632457
    0x6030a14090a050c030a02060f030a1407020a021e0603040f03090504090c030b060a0303051806090301050c0310060e10080a0e120406020114040f08091206011409070503101502070506040312 83
    0x213030900c85210b20340000e40f0200c240d40546100d05000d10f401c42c403007240d0005840741d05619110307440d8141c00c0c4040f014081c0300702e10790b600405641c566401803140c0017542c14009020083d07140140d5140d5151041126005079002c4d11442002603113040032524100242c1185902c5801d084e004030501085020860071b80f805981b0307000c02c60700c40008000c0ba0250b64070004001c54002d1046a5202c198084055011000501402c1c5840750200000b821030b10122031000c2002804418803000441001c64100a080282041d51200c0201000550102541141102041280000561200c105801420401f03040320202c8002c03540d02025020700350064000d82005600e0800101c80280300074009900640d040007100510311800d45801c3714992240c092250425011010054100c43c20003809000b0004c045c4030102c0402401c041000e070800c040c1c10f400400a0138001e0100b2094050321182c22076030b8483e2685604041d802040c0d05144495202c145d2050010400000303009d00041e200e5420001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 101634955 1250 101633705 101633713
    0x2030304031106060109050112020405060301120b010f1409060d0807060624050f0c01020f0c0606040501050103020903190c050402130503010e01140c0a0306050a03050a030e04021806030a14090a05 86
    0x564021a030391100c044030310318002031001b001040a0750140c1d285818a0030341c004058a00703525000400c296500c2079000c9140039401d20f18402c00c0c866508079150141c1565a024400170b840c2c10043c1c480070f4600d4110034810075001c03000c50000d646940c1c01d080303100e500c132050949903001401c00100a007142d129503040c5100045000b03036041c0d41006016084a40707030712a14140418001804ca20307410602e25250150340c2040501010b1010001508856112000411403854410103101c159841a844241410300610410f040c40d6000308407000301032803400000301103c040d81882e115014666000c20f80081c8001080c10381020f003003030b43c0402e45906400038002031b40d110a110b4200c0360b5103000803049441940c0441c04002007400140008544c901d00480c1540d100c000041e801c2d8066032045030550b00140d00c0c00100340c1c21040c03016140208450031801e0018525600c03038002c560b4040e19203e030300000000348102d80311303900802003003a4070100040c040c0b030915515507a45c0f09a0a0a84562007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 101636205 1250 101634955 101634977
    0x3030c020f0105010513090c080a12020c030307150b030106090c030603050714010203190e0411040303021e0709020903120318060a021801050702011b0302061f0f05060a0507050604030203030403 85
    0x1400f40ca0f04a61004d01040040d41d02800c44800030501e002007100c0c01c1518070300c001207002041180d000310500541000c2c480d0581c007d00640340803170000c4454007030b40082c040720780402c030450503441242d10030010104094125070006401004281c201c8000b1500c0c0c5082820810b0b4141e0061064912407421150b2107a02c68940031a4000b11005050050303004100d207994030110f8140201610000b41064a51104207000042c15642180c0040040c1030000c00c007081071660400580c03d2904036490b64560465041c1442c2e501c41c1241e01400d04519000075025420391030400000101412103003020b912410009450b13119480241c012514622a4901080c2045414402c6641100d007105004801080c0800150b403580c002e00c609034140700144550841510440d414003065501c60340c041c00c000d20304046600400140482c00014410391114280001d04180442a0656804481c0f541c1c4400c103e40c0d00f1645803040f08001021405008280010190004007a40c010f52080d1107040c01d410f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 101637455 1250 101636205 101636233
    0xf060105031221070302030403090e070f08070c140714121504020f04020c0c01030c0c03020a0602130f1503050601030b01020a0f0309090e030301091503020d031b0b010303030c02 78
    0x1100a004031079154010090180301d0048110041c81030080410a48034070203040070040c1d00110044aa0303002090b0008204070800d6032007910702c40944600800d000c0942407a110080415000c03502c81000e10000780086070410b030040c1c14401107983e002880d80703044010038103100d407120f113184101c00b51a0f58100500c401d91401c08120b0440030401d60061600454410301d00c039010740041d200b681c1000e443d07402c442c030584590004000000c0d00b040100340c02c04408000508840070300c4940e000b000343c0301c607035000001c1e40032440100d065000b50000d80c8074100d00d016640c04e0a0300e0b500035508100d09400020708600016010949512a80c60400070742d42c43d88010343c280c03a40d40d40c800b0300503000780c41c0b150006051854488180c50003490009010364440d1908000c880b0700d1860340d041070384040700401c41c25405000d40b411a6448041840080b071540e40030810103502d40134000c091003190300740a00b030201a001180006908016000b00300e51b52420041c000341505001701005002d2103800074050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 101638705 1250 101637455 101637463
    0x204090f0f23150d0f05030a0f0819020309120403050a061512030f02120a0315080106080c060f0702060406080619031e02010509030601031109070e03030a050a020a050706110f 77
    0x205100d03802d40c25036aa6590080081544001040341d804a1402c14040200320800800810b6a210f14011540c1e0010140083c1040c4403480c00c80341081804070801860f07050100180fa140da200040160303c0392121400c050600346051080040350401180010034800e0000b43e2012060080030100100f80c1304141001200c003850054065a060078010400000d1040ba44043e4040d540d10586009510b00c5802c149198403024400c00001c1e12408144040c00f1080c06400040603200001c1080328944108980c4645410383c1052181001142145020606a0451785da81e40e005090303680d11502e440f00645440000d071070150240ca40c121030159009002c03c000c6040d42c3d000303020602d086030240040325881c0f6900400b241004014480d40d001914108100d074040c503c0303040300e0030507010315a052040c40040144034004100e40c00d044100a901c0202c00c54170f07102e01a01d0416035800791080c0c00d920309075000000800d5032051183c0020603c5d44a8011050b55035050f007519440c00314544416a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 101639955 1250 101638705 101638751
    0xf050601031e080a111e030a1119120c0803010e0a0f0b180604022206020105090313050d061407020a0c060504060e040209030a0213050402010912030509090a0204090f0f 74
    0x1449001c0000c80059401411010b400702c41c0303041181c450003100805410240031b14003800071541d00120b0b1000342c8030f4105d40d104100000c0070740180760701d101d01000390080403507510000d010081c10010b4540042c0c0f0902c03140e080d0a8000b0f406680d00c1d60744403c507019200c0101c994081280c81c0c00d0a19003e044030307028140c2c1250000f000b064440d4030110b00f11074480c2010740302c41d42c0b15a00704804c440c9612180b08a90350446007148031814940f80550290a54100401032480c41c0c008010030300c0c0c1d131403806d0301c3c03501650000c1e210f20000444529040d4000d002281115001c40c640d003041001d00c1c0d81c0010490041480740c86413805090303071410f080d030709030099000b1200414042200f01444c0d00b040d42c09010341c01c0c8010103d41d030241c215004104081c400201c031031210381c5c44104103c00c1d035070003040940060040700f62504160302640c030024407074000c1d00e000c9481000c1900124a03403450540559010b402c1003042002008e25414114000f401c070a100c09070000d040000c201c000181940181c00d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 101641205 1250 101639955 101639963
    0x10b12061b0426010612030804050106170a080711120c010e01051309050c04031b030b1608130203010608010e1f05101205010207080406031d1c030b0d0f050601031e 72
    0x407600c590034001008100d0f0322020700c0c03042e41d40c8020025020f0241c20032070a81a00a8580c807203a800c00b42486400d40b40319811400c02c1e4480e000c202c5410806c0025099240798001020f291182e1682c44c1c415090044003605550000840c15180c40504000c9919104440d098070381c2c8912154410040d502c50160709a1800c0030b825001c0c0800180285810240d8003900b0007220601e00f5031283d80e482400c07407015070100c40c2501941c105000704820034007a10f402078014801c001e114844a0802071035484002c1c00c021030410754240b03200440d1003d4000c0c1026020b4503000348200050108a01c0c2d0f2040d40e51102154210a0300c612a4800410f10842c1e0140cd1403d000c01c041d00e040001c1039004455083e0102d40940d800c20840000c00c060b0700281028203515a000b203100300301a0486000c20105480002180d002540c2c03c020321805001d107020310080314100851030484420001d04481d00001014200300c6200c2107039020044007052440c1a0791181c00c0300c10320030440308500c000303003484c07410024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 101642455 1250 101641205 101641229
    0x170615120c0324100f030f081207030c020c0a030b040201050715060909020109060f021b0d051e0706180b0f0f0c070524030414010b12061b04 62
    0x14141440002403031411882000c8440360515080070a180582002401150020070007114a0712207502c848035030807031451505101020b0070140154a212400c2c030004080b40c24002a0380304000c3c01106960b0700c150f400c48107010310700c0c0c40e8002402070144001080010700a050b24412589045240c0d042a030703030000303011952a522a40150380315072107000e0649500031440c11003480c4079514041d81d0042c0c042c0c4078000c10070070a0752001504030401a0815024814440c2508003016030004280d1082c02220703803964940701e480004a4070341304c580071018100e070142c1c51465105c03000c5030a120301c410b550282155820f030341d20741b011a21007080740000d02240788104000c118140e0000003400d4800074001c40c0d545000c6004074880c0300703070703100100c03640d01500241820060380c0f0b401c40d010100241200303058104101d40e4030f0941424480140006c090903540342d0301c00d035a0300095005072203c02015102a24003044200d849a990004590b80308581c60071030102c82e6602070315802e440c101c40602a81b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 101643705 1250 101642455 101642491
    0x7110a110d120905100503150415050301090602090a050f030601062f0d0807050f0406030e10050f0415020f0f0702030c0303040f03230c1309020405040602041706 71
    0x48005006640c00d099001e0094007515010404904400440400644400c1407140c40c0209018105c0d191703030000014440140208001040c662421501c404001c031340000b03030140100301c1402c0950703140d00318a8066103005529810042640d0092130721400488101424558500c100440c040e0509030352a0590880c0c0010480319004803450f072211032078403400c07550442d051100c010182400e64566940340e4002503071558465040100260803219034175029180a0340c440492034188150312414041580e5540c03030200e0080140500c100e9000342c41030070310003030502e07410600000e101910309580c00f25100c1440442081b5510841d4021440c100301213049c200c18545681c01c5821001f03092342c060203030954501c041d5070140010005015000e107079480702400c505190f0614440a03404400010204418100c01c80b400a092070a85104603829003115001c0300c2050b0280090315030094206040005120403c602c0d03401400c244c4560020040d8001c0012085642d10034003503986003400d0612680c2c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 101644955 1250 101643705 101643713
    0x6050412060e060c0409150e190e07080307030f080105030a060f090f14010b0a050307050904081608040e060103022113051911060c030301090c030b130603060507110a 73
    0x2a82956005020004401064a02d4079090035811280018101000101400b01e88407502c1002c0c0240c10781c04041d58101e0415001d415046400b40c045154040d01600028040b8000d4008031581c00881d001c0d1010f0580c0d0b200025030700d800c29a13007140410043c45100000621509109040329401401850034a10740d844400007028030900c0e01c000c1c1600c80c0200c8001c1100c038511a030310580b0a030600e8484140c2c9079442c900b1100380c040c0c61485000d0000c0100700a550020744e8405849007114640d40a850b10b181002c0c0d00e200c0e03085883c8074641045092401d21800c0d2001e0b000b241c00c1d00038202d4403550340c02c004400701d2050b050031400c0106182061081c0110540546a2105d083c0c2403480410b05c264803124034124040700303903d0300c0f40d6025060804100d5892400c140c0f0403c156501824240000003058680c04140202d01b4803580e0b1781e03d41140c1901c81d4102140c201c8000d0705070500900d6400d60140a019140410f40e0741c7c60030321002c070f8821031140d10210050790400016110400460352 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 101646205 1250 101644955 101644979
    0x1f050402030c070503030906010e060406050105180109031a19330f030804150906051b010b0904060c03051602100b1302040e090c09130609230c031204060504 69
    0x101d80d590b501014004400041c10800041d40540300f003000070003940d80342462001e904100140300e076010702d060190401491741c00c00142c0b184802d42000a4060b114044012110180c0c1c07540054080d900300c44442021000d12500c0c1402503580c007003810480c0c206444180203a40b810384c01c103800356000381480d07403d12140303080d2120040c1200d403401c01c6c2540d0315211a08000c07070307507002620103440000b0104002148280424003803805401c08012013883c2003400f0b00701d03008201101034440303808118065505000e51022912080007419194141031509080004050300042c00000c2443c0031f000c140c10741d680c068250a950f00683c0203210403e04408000003500114514641204c3d0303861a007001c0d000f243c000360010740f50300c0c40d040400e4600a500c1e60b28014649041b40c1c01882d0210078880c01140c5500060f04058001d02d011500941741c3c0351a02d00006041052000408c84501c034507180d80010907110255602102140e8500a0f00350b202d605512851068001058041204014500c0090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 101647455 1250 101646205 101646211
    0x1202040609150306031502180a14010804050f0105160e0312030601030c0201060b0307051e04060504120206070b040302160e19051902070b0a06060516151d01050f1f05040203 76
    0x103c1c0101d01c0e540c0d25542c4031a0808090589201e440d00031482002c810842c091300c06000c002282d035440c019150004c1c241040e1005458181000614000982881420441052051a440002c00440c40d15035900b0340c4c1700b40031150003070010b0380300740d13021100345000210042c0784100402042d1840e25503c0054000f010403550603015075481d5040007504148034030146115500580b95241e41d0446950318440c2100c0c40340748699006002d000a20402d9404000ea400341e07142100c115174001c4803400051520301901070020940701c0b0041c100003c0603070111761681200f10030083c0c8a10030303840d00c0441800b80400c962184000c8036030711001e4540d01c4903401868001020366001c81107000107503030402c107a80c400003084d1182785404080c0810744c4198030a21004054501e0214200316284000204003104104003801034950480020800005030303105110078420284042c20700d04009207428041d000861706290507000810009101a80000310030980110203c0e03a21606410003082200a40001d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 101648705 1250 101647455 101647457
    0x110109050405102c090a02090c040f030206070602040302060706060e0a020403050616090e010306020a0906090302011b080d09050c03150705190215041a06010f0c0609060e011103010303120204060915 87
    0xc14a040003103080ca1307546400740c5110000703003140e141c841c0144030702e4120117030a00c0c503a90001c10080082889440b001d40c107a950448410366100214180107000c2d010701c0e08080c0d0300480010310802002605c0c0c1c4044211040340b4483c41140c1d0301e03000f203102240590300c000343c0305030080750000d0400f004000341c018000d400d504181030000d80701d0001e084106001d0f0800c490f0550700168011145400032903070001400d1919003d103d985c00c50340000d05003000020304a8107080e15100300020081010255040018640c0080120600c00c1c03d00300e40c1e419046203454004c0c01200b517581c81c1d620021810302e00c21032490b1146841d0107a41c025010100715400c1e07000c0c046000303082800400c0d032800d5051074040c42c0144c0c81c0b28000020814400c04c1d844020f0328003410310890140c0f800100307411409404030300b81c025500060000003420000e000d04042030a041e100c1d4178100a40c540d20002c007025506813402540c45401c04c1600b202c10710120b20441c0190f802240413017000b0080c2070f103002c00b001507503229 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 101649955 1250 101648705 101648759
    0xc06050918070f140f030403020d03050115590402030403090b0f040302060a0c21120c02160303050a021509060402040203040618050606030f070b0307030b011b11010905040510 77
    0x460f60717400d06a0400d86044005800c2020801c00c01070749801820702500e0681c1c1e04c0d1403038000d07201014021610b650401031441c00524440035081c407200d040400802452130200319511060000c82d4400311443c2035840e440c442610015440e400d01e44252840707194907446008085041c03515404031360704020361045283c4010440400161602c102a1613030300008d443d116003001481c80e00034192800c00d00c56205c04241d811400c15001c0c2d201204c43c03141143d5202c0010001440d041c102c0c00c04440701d420b20b00f10410f00f2000420107500c2002001030310349a50a548103500a20024400300320151900011980b03c1030105000d4a02a4000d64026215000c0001c1121141500c42020480040d06884980184040008a04052001c6081c11001c20080e0102c1f60030502940464007003e4032807001c065440d005120603034054020354084200c0d84820725480e4007245040007846521078103ca0010301602c10010311810140240780c01042c1501c017001b0130300d050001482039400650f541d2014410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 101651205 1250 101649955 101649967
    0x703050709050a050c090f0f0117130b060303070f060f0902040f0f0501090b0a140f060708130f0506030f04111e0f0d1a130c06050918070f14 62
    0x1000300224001010040c00104151034044070a500b00c40c0d0092004910340c05c20031501d00981c5d240286036002d01c0c002c40750711030000e0200300120f0749030310b0704114501d504220741d0034010901032491080c415144101d070b00811607600c550078103031a406506801007000a010000a0015510340c02c24081c03841c50000c00205100b0640002e02034400000310706080f240d65941c0461007100324010603015086800f030030306c09146c240010403d000c4880c4650182541c031010140810f50b582c81d119000c2d481c3c010b101e15194061801c03c1c412561180b401c051a4280d40c40d000603610301012001d40464000071305690556603880341035010b03902c000300100c40f80280708051540660300c8004559a5194100101d07003402c650390140001c0300b0500502d02c4c414001c401350300c400506040c200c0c403001c110712100c00c511900c0340700ea500121200e81c9c40c0141a442440d0001c070702c8643c0300c80508506c3c0000c40321055254841c2d003021030481002d41e0300c0c200103509035514408490080b4041d0400c101d050328640e00e020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 101652455 1250 101651205 101651213
    0x100c080d1503110307080606010c0602090a03020904210e1f140406090e18030301030212011803030506010813030816090504050906060109080f0601050405090c0301050103050c01020d0203091507050703 88
    0x2001c42c1c000300c90050f0f004030003440f0b50a0801c02d03680641014002415141001e0300040c003d00d03c041c0c0001d000c10780000d50340071141c403141040c2c03000b0f5602402003a4a03082c24a0080103103014036440c0040c0c0c0c200c81c0301c1c1c031201da032264054103800b082c0a84412540c0400020784492688424184420300240c0038012003043d44080041c8010401681c2e0140d5035030405600d96951040039001030b07200d5144d041134a0b0440303000b204480c1102d41c104e8611246903008803655000d0700804000c070501040001b16003007070603010b420040c03040c2801d03a90740780e00d83e6610403422001c8060102c0940001c01640029600c180c48281c0c90801440c5403c24200017a503580c009010380e88100d0350410150032040520081d075030005041c102500e4224040c0503610711420610b582c0d2a014810705200b41c2d20380000c11481c1c00d06002c1070300c03001c2010f00240701540c4c490a0407591680342c070754024018882d84c03400401852003c4103480e2208130040508030500002c10798600b8681021109507078034020100000005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 101653705 1250 101652455 101652491
    0x30e09160c11180403110705150a0e0102070e010e040201030506010206160320041e12110603040602040b1207120c02060f04140f060a0c0309120c06110406080402030705100c080d 78
    0x1485c07282d6142c6141c2030303d4402e49420301c9800d5000b180145810b0010b0814030003203405950388000070345400c550203421940101d1520020364891074402c124000003044048031184000c0c4a24000e80301800607480f000012a41c2c2c03001110340c04d035900140115800554881e803c0740344185800044a285443d40241654441c1d226a02c112018a1800d0b03e000410140c0007041c0d0003846034610021200006071a10150781da00d040000d40318900000c00142041400e505a5020f000204455510f542041c4040a12000d09480410204030781c051803000707100080c00f070040c1000555029003586d0f01c444080b4566400701900c1100c4250f0156160306100c04c08000701a4000030040040059041600e0050221101001c43e03c04040c00c0c9245540462030f1443c242c0c207030070f841e8500000c04540328240703070005105006d40c034a4078002c00903002038140d610078203490040b4022403ea4109658881c00c001240349100c44d030f20040b900c0c103004000891400009401c80000c04a80891607004500300321032a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 101654955 1250 101653705 101653711
    0x41a040c09170309060f0d0f0608010902090a0501120f06111201030c080d0509240c0a1103010e070308070f02030105070c050d030c050f1e07030e09160c1118 69
    0x8421078020000c0e5240c002d003010304442c18502a5140400b404041a4640300f42005668a42000601100100500d500911b80c8288540081117030702d07100d0444a020340700c440003c0e48500007403404a0b00319602481264122881c1c01068071103007000d43d441e0803140c518000c080d540c907070344c45241c80ca000000b08002c0000d5411050b00444540c15840d00c2c05480755503406c142026070003140f44400d81a042004c4071000c5c40221400d18120140d11503942c07501d0718214084101d6800030810a40760b40000440100d81403003102141e1181a00c00b0906080318094a4804407070351001d001000805c0c5144010301e40300e40a60744078100c81c54030b0303008a800d40301705442d45c4001969459011090000a0203551045102e40c41c0c14482c1c0110300034010801e000e80076810110100c00220400b403248908610b8440504003000a62140090b06000c2e10a074035000c0c095000d00384010014582038401d010b07904040440d43c076908035041d40c544801d071140c2400120746030441906e40991140001c0a001244 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 101656205 1250 101654955 101654957
    0x10f050c03060a080a0203072706090b030f010b0a12080c060c1207030e0c010f031d030903160e041b0302040f0509161a0a03060e0c070302010605090105010806041a040c 74
    0x6070360300301603042c07140100c0150322244094010400c040c00603600428094216410300c690300d0128003e202c0c1009006420000c44507407140b401000107140107003a080150100e03422810307a000782c0130068000b401e948880f400b8542c00714588030180031100c212000024054040c09070141410203580110746441d0301981d1b03c9016000100740e07280b400454442050b131101241c60f041c4140941c09101d071356224440f0baa1641400410300c62080154421390000d010030b103100b4418810005051410303501c0f5402412001d010f4010402c04264164843c1c01d03000455500b02c046002039a150f4480119010500320340150041e00c404000015941f5405849161480c2e40400511030416003805481c005080a0743d4070340b4110b85c4400c001100b00300030401c003020030070301c00141e5940d9407082c2100284103a402c02818903015001b07000040641c0c0000d007031894400e07002000040d8aa100704400c41c2b500b48203850004072401c000581c0c0b42440e0f042170341c102e1145070300a212503078028001020754000c59a000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 101657455 1250 101656205 101656207
    0x20703050c01050f030403030504110d0b040b010b03240312073c020409020409021005040905150604060f03290f06040803250f06050a0c030606020717010f050c 70
    0x1005000c424080c070200c01c0400d0074118a0480400c61413006400001c0024080c141d4a8000409011035500b42c030f50440c1d00113180742c0d480c0f0800e1401c5550260300f545c0903210310f2100800420030700300b564120b90107142c0d9107202c5851000e0101001d0500b1144034903083c1c0602458100e03040b00d40703815000e0001c00d03102d1420940004030411060318540b001e00030981d2507501c0981d647c4418510300070022030444c3c0588010507000c00e94004503000c1d101084000b5040b5040006210b00b00b540940030784143e402500050113a0348035a001c503690024940000c50380542c0800041008030700401050352030020030708002c034500149005585a01200451100e001c1c103038841c10810038944140c155090705800c80368181054101400d0f80c0ea6401540c81c0390b020b032034407410b40c10345500c0d001d00c09050243c0c2c88644406c0340145890008043c1800b600e00307003103e07401c00b4242e105460090295000f500c80030b1b401040407501d08070400d07020401c0c101c40c0503541c3d5a07945156031804030030300481d44100f0404c20700d070b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 101658705 1250 101657455 101657459
    0x5062206060f050f030109080a0f0516030c0b070201020721030917030a0c03090b01090e0a08040b18030d081603020405040216030f080c1914030a1a03031c27030207 72
    0x44011300188050051291749842c094034001582c90003a5050300105250501500b00c1e944401d8500e44128911441c824a42c80805810140d101000d1442c06202d0f8006841a4440d030b5802d900b82c0c05a0f240080402010a4044403c0b90702014961907c855903d0049081c030034580b940e180c0030b4520000f00b8501800001000480c400d54058413240310032038035040000b4400d540301c034100c20030180200d0b50059151060f051109600b04a421142500240c2240cae64950711462001c0c2030b404a25801c44005070300440299510700400e02040c140d80907102e401d8150740c0c43c04122b40b00d006c8018080c1c1496820300004c107440e16144003800300403601005d060350118060070041c00d60240c0065000820821400b000a207121803400e950a14030002207060a0140004c02500c80250880d00702940060120402c030300b010711030304403142c2e1264813401b4944404480e010b0545a10548002803140c041c00c441e100c01c620901d500108201e0904043c224150240c1300600403002c034400e00c2600140c2c440360003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 101659955 1250 101658705 101658709
    0x190201050d180201020c03030f0405040902032404020f1f081008012d0606020a060f0b0d060f06141507060b0a0602100507050a0e060c0a06050a020a1b05062206060f05 73
    0x1140c410010107c00a5043c00300541c20055030788600d00035680500d440b141c0e001b00b15101040304050740541ca603662001d5a9103007440a50041c800c48041e4841c0009176a45030290400092030120512401d00301d41ca20064a40140e9000c0006001d03e0f0300e0540710100000d58070001c0c4039401a400102407400385c020303c03201502d181c200000d140480790b01d150041c1080700d00d400007640d0302d00582c001c202284441d0121010300040918120268008030b0031903e120411600da030010f50380d07460041c001c0100940303440300b08400c0d880c25080ea030b4000b0010401036070068102400740049034402c59000c21000280380c0460703038001d8142e0029016034400080da5641804034011564001504c0c50114101003071018010485001c2c41903c1340180000070706040d02490900c81d01088540008040c020303410703c101103e0003944941500c1e000114804010f007607a400f00038003044541d40020042400d031701c0e0a88940700c036410200c441a25104610301100c00a5080e01420005105440e803507243d180c50402 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 101661205 1250 101659955 101659963
    0x212010c0e03070e011503020f1305120c010f0c02030106050418051509030f03090f0106081014010e040b06010c060f020a030b032e02040801060f0302010e01050c190201050d18020102 80
    0x2072254400e400c240d0080c001c040104080504403141035410844003c62000203130700030b00c204400c4482c00e80000426041060842c0f18880c04c5450507070b80d50303d450000540a9407030742c050701d41240c00030781104040400d280c400c1d40f10842c7c070b0740003d0002601c00e9460740041c00300d40c404082007400c0c0840701d200c40c05100b0705012084003440c403d94034664918003890315584a200e04610760410200210206040003810883e40860440e03c1c8000c0250503250310220b617407001440c4560070f8480c141000304030720448a041c01d6049900907040b10f9a26150303540c4103540c04070001c20031410040c00508280108440340903102622005010060307848030201401001d03586040d41290199001d100c1210004c8030144d6070940081e440b0348460000e180000c0c4d541d02034411584450b00030742c00c0c24800f05410726603c0d030704e8040361300c01d0301c498203441039203001135605004004420300341c0d42108850b0114114000d510b12890ba10500d440d03450310510541600032102d0324a5000d0001c121010b5035011960100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 101662455 1250 101661205 101661227
    0x501031a130c03020418050d09090e010b09061201110a0c0c0501140d05062106011514160c0504050a020c07083f030f0910180206070309030212010c 65
    0x20a0100307609019100e811003540c4a100007030096913108010705c2100110f2905100b01c0d6404010b680314104a580002d2a4500e0350190780409803910b407a07458180c2c0140700310301100b800074003212010f9540404111320422500c5001c00d0705d540350000d8100742c200301c400901021249481c0ca4481c503040341045248036209422070303414804403008081010781140156101c119081c5404a8141d49120118080c81d14621401245d203800507040451202d0206495069820905d900c501c0c003d20a40100c0c3c014101d030590744400c2c0420001003511107042001041014001d011035031541ea039400108040301c0048036280074456002c90303c04019101400044014081c04000b442c2682030241c1d100120384021107413502190a041100b242d0b290740c980078544020b0000b540c0740d1289443c035011440080304644013511801621800f049007846c40c4102c066009001000c00c0070609194248402d50b400158241c0521101d81e40000040c0e9403250300c040e0340e0f030100c0b001003903007588400098071824001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 101663705 1250 101662455 101662471
    0x30b040507050904090f0b0a0e061003020907110102040e130b0907030c05100207080a0f1b0605030c03060d050f1c080411040b152206020d090e06130501031a 69
    0xc0024801d8440d4094151407521004580000f021030980c9400c04024000721802007445a010b010441400102ea00040620051200741c0d4000c0d601c000d2030920344501408025032190251020400051040d985001f4030180c2e40300051819450322140c2240190844840900702e03000a9144100b000d1200166003010119004001407800c591b5103005e6000f60380501030042d00700040010000d0300c2000354070010901d200c142c50700d10204e0304101040894211040c0e034500900030968ac2644502010700d0220340d1240c0e1010309649400031000f07075070342c0060016544403c225294901281e400e01080c0703440310b100780c014412680e004007040615030000b1000f03010f100100c0200008203030107143ca030ae84900c0840d00020102c4c0e499000034418140b95041052a40d00403614082e043d01240c0c031080c42c00c108000300103505030b40d4001240d036240880502800119240b0b8100034900094051540000000300099403440c45020084221003003640f003034805440801c540d40e1170701a1070010607000310301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 101664955 1250 101663705 101663711
    0x60c0206060906040b0109050d0609020306070f02100207022707020105070201090c12030203041d0a05060f0325120b0a0c0c05150c09060412030e030304061b0204060f06050a030b04 79
    0x100500250202c8001014103004d1500c4800d080c0c0345e41e1245c405200070b080000c0061004146038205000103110b1450200c1c060301c02c00c03011403111070160201105101007a801001c401e80920003041c0a50820b0504a030054030130032000702c00005400307040a40b420b00480d0803680b4500034200a0a448020f00301c0c0056900d0003148002080c0022190fa041e10106140d5901e140900d01d001c0703156200300d030301c01c5d03248400d420451070000084903800b80c05802c0c00b02091003d525550104030428010700c240e654940e10500846a1155000030000c0740f4081c1c0400e051425583c0b50301e0b0401001c603004044502c0755110702040100c4400f44a240301e50034861030a4440d40b00d0503912243c0e90b0000c41074801d07941d4562000110000840c4e81103404042001e0a419180c90303541c500803107060580d28081b004902c074046c04040078100001070f602251481c0d0b070b9032150540d140e91f02c52031050540c031082c1d821588a20011400c1c80000e451400103111541d501a0749026412004003216443c0040c0d9101c4d6003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 101666205 1250 101664955 101664961
    0xa050703060f0528150305010e07080a0b13020307020a021504080d12091209051c0221010905060103050706120c090b0f21011d0405030403060b0307030f0f060c0206 72
    0x54a400c2505403003054502d1600b200d08035400105400405440804001003003001250781d4002c1c1e114004071210b170351070510099803507030202034052100f02c416800042008001031140d40583c2c200080c082405040c80c1545141000c410b4161382c02100e0410140c6d00c2107050b041103040200c044071980f42c0b40c12a46041500f048911038451218942c0c078010425031a2030041501d24541c04618980e81c403003180c040002d030140000d0048403a0344141d5106e21403011080300c011201c403003003403405d60f8000d10300f26540741c0c0c0da0f841c02114581c450030800d031996600c03101000108208030450103140102c0081c030540d171808800411859015030303202e05450501a0040c6d4054000c02d2807020303900302d84d400c0f644422040c2d0303040484c0d005500080c04103c1049080c4000c3e18856001581a12040f41404a1000205c1c0c01441c12410980b0014442c1e80f00300004c00218055070b11600c00305100600b501d0a107940c0e62145210228100707420f552480c2d400d1812070070407089101e800d5000700180003a19986c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 101667455 1250 101666205 101666219
    0x20030c0f0a020f03070f120507030207050909030d090f210903020906060f070309051005120a050a0905100e100b01020a14030f0a020109150b0901030f050106030c08060a05070306 78
    0x3014800104000490100d25051414000c0c825000e80c1d40301d820840351038030b810381031451049400c203e0550750685814141c0a1403031040e1f080350025038041d0010003080e45803405000c0b00d52002403040360b01e80401d1123784c1000c076260141e0304109010b0031003c0311066282c1440d419203150040140884030050b4840ca400903040840394080302e8040340c1041140d80c0d00e10100e03503e80306103a00102d4410740010301400b01900078112405681c0c055500040b580040034041d1420b00c200c1022000c1141c228000910f40b090076000607600200d000d2022514a03039641d61316140040d0704200c02c17600c503210803122000c05003c120f10f8031600c2070082e040c41b001c81c6240020703444480e0030201501100c940c1c50740c84031014040084410407807804c507209030b80d201c003080f00034002c1c041864211036504040042c0c042112031405241180e0400901e444c2003640f8680d104001e045003002c007191255243d00001010809014504005007804c030301405961a01c5540e1904440d4001c1005040c9450020180000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 101668705 1250 101667455 101667457
    0xe130320010c09080c0f0a03110105040e07020307051203011208030c0705011e0f0203100320090718050d08190c020405010f0513060312030b0a050d230325020f031020030c 75
    0x40ba00076080700100c10309c00c00101c515118540180060b464020248408190300100901c0880e005800740c4003450007900d1214040c1c80280318402d1022110007151003c18107600c001d40c2c010030320440d641d107042d85540e070341400d4680d070b00c1c0c120310002e42d2a15010411341d618044c040302141001801c5155141c00281084089017500000d8a4440340d2110481a5499401d901c0d084100003001144a407500c0a001840d20fa07100845022001c40018000780a051240c2060000e40e4400002410700301c00040c88000c880e0f1040503101080507402101016844030302c1000d01030802c00803840211070400091006460f0307483c1003004058074100040011405c1e03c1412074620140d03260100e0315011050008402c9130035504541d1f800510002a0020018140d031a4020355220200c07200303004640216513074a0b8000c00109282900e402c442849043c0007400ca01d0500a2004040060104d07005000c60b01d09282c1c40032031803401da9258407100718a004ea0030380000707107021000014590304e4214148616 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 101669955 1250 101668705 101668709
    0x8061906080a110f2206230f031005090313061b02041a03010203091c090806010e0709090c0801090605120a1b050607050607090e130320010c09080c0f0a 67
    0x4048028258401540c2d40c3c00010300c0c1454000303040c40c2980d1941000204030211014001060500d85040010100c400d5203c00303140155001d54140d0010b00001444010700501100503814080c501c0c170407854141c20b1003524024142d030b400442e200c102c003b08603055080786400101c140840f250715581e190b402880c0003a43d41c1e9054501150000c644c1001340b94080c4110201641035001004000705440005068580808030071444141e000e8061400d956042c1240102080c6030090070051000c03000400350383da000b403c00e01d0207000b61a51040c903102150b941c99220f50008244c2001080364640c07078041c2e2009810f08440c000b031110044010301c0d60300d054040b030041c500340c68800b01c2c03a0b03100d00c0b00041c14000d00014105075507494061a1407522a0000ca84040104600b450b003c01c5564035025214803032a400304014800421540302a940c10f01c5284c2d144008040d0b109020b8251503081c091b448000c142c1c0c0d02c6003c2d400c2d0411038040e00748000086803900034980c111018030543c2c0c51040200c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 101671205 1250 101669955 101669963
    0x302030d0e060d0c02030d0f051603020a02030d06080609060108030a05041703040e090a0b090610090506131506080a020f03061908060403170a0603050616021608061906080a 76
    0x200070035100c0c0030603600d0050200e002e204034680007100304295008801042d0b50030450500f00442c50405003450225042611070060003a0401c00b1885024041d41c000c1041c1300141c01200e0424110701640d00035928189c1140200b034206105000d42070804010710b0307014000c03440255081c901502c00c000c040b4000c5108200040030b0104034a14550030a0003228060304a0300002c130301038a80b00c4000b035a12203004804503030b40d9860384002a10801c001c03401e41e0140d15012865400149410000009007a02a040e682d01140d20441451048500c0c4a000340484140c01c00d580c8452038400042c0030024010600c130b004900421245034241140c3c8116070380074104583c10480d2801c806a4000300800c0d5401855283c41100180001d0580084401031008400c1c581c0801c281d4404084109a8406201c018080d81c4268042041c0380b064601c6869402040e00c103d400444031901d044018018a610030100d641000041c4664480d100d4080718903251040d00500440785403800c00740c0c0c0da1104100c060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 101672455 1250 101671205 101671217
    0x60d0506061c05030a08010e0c04030c060c02010e090f07020d181a0705030310030c090c02120c12120402100219080715050a060915060c1209080a0506010e0601090302030d 75
    0x1d034078070b20400705000140c01508072600c89840040140c0500420300078030114840f910300242030550341008503001c0d603602082d60404149014005d50315003440d440e08a060086505d0b03c80c2c4542c80e00c0e0005441070410f60340302c400310b080482c0068100392101803403804000038800300c40e595500302c0440100300c0300d01c032039088c3d40702512440c004440d00440030020f02e240000070074880805921802001601d010300c103840807140e03542c00080304450400c1992409600541150204800c0c41405840b502c210030050314480d00b03c2c140080c400d68003141c03032501c0c164044c405120650600c103401c604014024001060160f00841c020481d1404984009002040c00141c1c0001c03c04603065000c96002251018070007030400303468030f0340070f07040f103000794042c10346844004039070404441c01d51021909140c03140d01c0200055241c00002d074545c00906024464041c0000403000b0782004001c0b201c60013030015001550400c00034a40011002e00303210304000f144035040c409681c000c03c0d0b848200300c190070300c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 101673705 1250 101672455 101672479
    0x2010504020f0411040e040501111206030d031a120304050d0b0a1808040e040201090312020d03110901090b2206050301140103110a050d06080d091a0712050706020f1809060d050606 79
    0x5016101d420701c86004ad080116005100c00310b100b660a0068000b00c047e07480d0304821110072012100ca201c0c101c0c9440e0010459582141000c0c0031100d0880c50560030b480c580398640c0c010442a00e000003040752000119030800c61903030200c0c4104c408201303812990b4000c2c0e001e0703629a001103025600603600a2a2a80c020408580c040c00c0b66030001c42d8803014280d810b507030465020791280c04041e290f901090800692460602d45141107030311915050310392841650410b000041d490700481105080d001d2069615043d141c019081200105910f50f6003e03505c3d0306245d0800c54001b0500c055606050500c80b8020512500406440c0c0101031480c0c281d40303480d00d400d0800c0c050001940564114002e51080d1403800390701c20a03880c182c0c0d030070700489002004900d880030340c94841c2010141030410342d10000380200c0d03c20402044030901600001d801d040f0b03c2500f04e00355500c01c158a03411148010740c03081050501c1024903601c408212842c80000d074650320b030103469180007804148078040340d20301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 101674955 1250 101673705 101673713
    0x10050a090e04030e100810062f01060f08060f0109050901150603021801020610050103022115040c170402040216060f020d0b0a0b070b060a0902070302010504020f0411040e04 76
    0xc54020400c0d802400e000341410300340900070403a0700c1c43c20340c02201c60181d491034150207401c04034045d600c41d5420400aa1801030111200d544903d03907880d84000d40c10110304c425004040010400303043e0000001d000e4982444400701c001c40740c0c80401c03150062000c1050041480c64010704540180c600400c0950307034000910f006044902d144408186031480119a0907495070281c0800f40307074a40e00d88440c00c41c25005a0350340500f20340c030840b0b203044c0780e9080c40705512075005049807680d0441844405800011415089034048410389000003482c100da08440c9002c0c003800102c0e054604003400d0b0096681d01c0c0f10440103006001078007580c2c000568000b20344000495081c0c081d00520100f16000101c05280041d610004001c1281810000a80030500d0049000c10481350840760b0140b5181c11b0307a88000c60450014646584840015000601000c4500041810a2007a400010246010310401c6041e003111451640102d00d0000b000c8581c900d980102c4042d0741c14052086051b03a074a00e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 101676205 1250 101674955 101674967
    0x812030a020c0115030b010807030f060b03070503061608010f0b0306040b01020f030f0c06060319030e0114030103050a0b011a0a030b03070b1b060106030b010e0405090a0c060e01030609020910050a 86
    0x500c0e195803030262100311603212101044207803445441c44513082e90723a90266542e94030f45800050800c1c10940c04800c00654030b41d000d02c030b03440c501409951444ea500c1c0e0001c0e080c0842114410104036003a0007a80080364005601400f50010304001c401c0503007000000d0045010050007940034a940d044c445000d03030b0080008004c0c1001403000c50380e482d522049070f91003681240100d815039118000c00724002e80341c04501c80000f104000c040302c180025903101114882d04d0581e5441c1032021015410001030b10311801903019601031402001c1c00d076400d00e420702011005900c500c081071440042c0070b041d2034020041f20700700503007032401042d03010300300d40024141144d50f4041c0d44058000202c85205200132000500c0c0f601d000402c0d240d0b0384ea640c240c15400e032082010b103a80022010b0344450b0f82c6280c10381c0102d411504280845682c0c40040c0d603001c200f1402d83e00300d01c01140210400c21129a0316000b03d0b07020f441d20f840150f0403e074001000c0b07129540c3d28081c0c1418000081468114107108503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 101677455 1250 101676205 101676217
    0xa081c0c0f081b16180501081203041a040803041a0402010905010518030105150109080102091c14010f020c12130b0906160b04120804050709020a050904060e09070e010812030a02 78
    0x10141d41c2c0456503400d040344001c40a04c5a607000900b0172544002c1c66480d03200360340c101c441d07074400742c00081c1140c1c0d610034061740000c00482e9415641d1098a1a0021100869200328420003120f9035034103090505d01107600d05c00080540350a00b2804000040c0d074843b0841003140c0003805e205403100b0100d5203005e0a00c013800b800325015840d000402065044d07098660104850030f0321548411521074051070700781d101e12140e15800415200200211030102100c0c0d03035201d0f004a01801e6802ca032200110b0942d4910001c3c008650340124600c2941b0342d050050b1725611070502c420750b161a6000780744000301c0c50a0320a07081034000100c1c04104a03107a0340d049541d0007884600741c3d603000c401490840007618064a040e1085d1241c0c904040035540603140c8503003d1900000200b0300c5070719001485000c2c2d41b0240214040000c24406401a6100c901611b4041c04e0b42074007548152400510191800c2c16652281c4d03101030b8068010403411001241c40d03000d14a030001801d50360f03640e01c40c2c003401a1003a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 101678705 1250 101677455 101677507
    0x1103010b030c01080603030c013e0a0f050f0a030f05090a0213020309150703090c050f0f0906040f020408010f0509120304030309110a03081207050f09010804110a081c0c0f08 76
    0x1140e0100404000700c155040480c0c021a100c1d44114000180454ac0d021162050301000e0ba0402003854124022441803240083d5490075034070f085404044c4061039040500c00304042034440c0799a08c903000300d50040640c4007050303400811030030810307400060748002c0c00c0d145208542d6002001c181c8884050010004102000102d82d049050901006008000b89803040d203c3c21000180480c0c1442d08c0c1400e0030202c4002040306100c0002001007140c5124050610381d801aa12031182c0c207445101d00151000b0180d0b940001641400808800281c40e0020b180485941141002e0800c00d40c4002c19031f90002c1e054980000c0141c098079043c4192445490781a44c0b01d807184500108021400004041c40459151722101c0f80e00c0d10801070311070b40140e05041e18151030074404803200d54412002203500600a17290010480c4800010854600e545c1d00170220136001844224052039036034810300800b402524110400f03881e66100c5c041081c40155000304078850015417210f6601654504007104214 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 101679955 1250 101678705 101678711
    0x142d070b04031106010e071e09050301110909010504052a1c050103061a030601060e030106180605090c090604050d030309120f020f03032509030c030606031103010b030c01080603030c01 81
    0xc1c100607140f4810800e441c103c0e0b01c40c0e80d0011031820991400035015846584540c0404480c204048609040780c0e40e0840400c80c0283d80040c07150b9090040898070580c3c0190683e0303070302c4004240f00402c40d050b04051300960500d028081c0451100030182c54880080c950100b07c41910380d54a6184c0c03041c0a480c00c5640d0f14021036158508807940018104d0348280c10402072070300c4146201d0f50f15402035280580c0b50f00071200400465006a180d81240c40006000060064a4022007005041d64503070700e003c0d0681d100d20a202d039040203142d060300280d243c0440c500b01041400040d00303622803401494082c000c481e94034000c040c000c0e04000c01b0300d50f20803070015880d0500a8010a14110f8179400d41c010300c100000303c40801c402004407070043c0c4002c00c0741240081107104030a0504c0b1449601d03070411160314400004541c20004080103144914000300d003891840c1000742400103030b401841d2099140001c006c45d2641c0000b030040a4480a081000700b66440ca00004c0c110f0085500503c92542 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 101681205 1250 101679955 101679961
    0x160606030614060f03150717040501090c0602161e030807060905070911160302031e0a02120408061303030e030c01021b01020307020a1b030c0603020a142d070b 70
    0x42aa0040c01402d00701c00d140080d190b40e40000c101e6440003901407107415401c0b402d11041c140c03101100c02d550088035802d00c2902511a0019412203407411103041c1c6859564016010401c49041e82d94402043c0320301c000c0a0303210713400b41c02d04121850f80c4104250b01040310483c49603280b0861040004541045d452071301e404860078202c015080380d82c001c0f01c05014080300840d0400c000d100303012504070801d42060412500c1001d04848112152042e07096100a00c80c00104c44e02d02034400080380280310255440303111049019181a074a47c641095403601400148000100041c0c1c2075405a80ca074044000e42004e8181940140360580d00144c09010029001903450381c150006c10b0381c04c0000031043c400e1203d03000a0b070308030700050714034000503006101707503034046540007203000c6814070b40f0280054103681d83d41d2005410140c5a100002207900032500904240c0c1241c0d02c010740d01060b906441c60110081360f610b40d05550a00c030141005070581207200500c03071060940b80c4c81580311401c64003a003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 101682455 1250 101681205 101681213
    0x50405010b10120b060f07140a0503030c0406020705240a111603030206060a0302090402090403021015180603080f0a0203040801020d060f0f14040b0310060303090510090f030816060603 81
    0x3829014a11490800008203c0e60401001b01c1e5009640c9090030703130500a040e903030036841d543c40201e0482c0d50300c40c00072a000464800d00086000e11070000410340e6480c6050070107400c14001c0d0703000038819055203a14200403804882d140c241060010305081ea42c0301205410b0b1201a550f4000c02070f070740700b80a40d942481c0004000001500e01039000c9410740d5551204100000b00540802500021514007103801400c10780780d4160858400c0c01541d844150382e00201c0110b80802d50703401420420040c0c10005888008410007040741a640103011a604648841c1611311a0350910003c0c200000b5210307403018800e000361805044c5400096540300e54080302d41c0c02400082c0181d01d1450519040045d80680340c01110048039180d8112001c8860b4200070800140303441840c10303030140a11403008440c000d042c80764070061446030f00c42126090a050a0114090504d03807480c0c05d02121020038412a58443e000d282100e911041d8182d403104402d1001e01100d035907600090030745040c40c50101c108 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 101683705 1250 101682455 101682467
    0x316061d01050711010b03150709031a01030606060e030c0114070501060e10061d0f040b040e0604110f0a03140a12030b01020d08040b130618142103010603050405010b10 74
    0x900f506a0300c1c040220b0401241c01c0c00c84040b548816856400001c0c02184a880d101d010ba070301400c1c906114414540e240c480f90940c0701282000002c5600031401802042070501c1040301614030351800c14110f45c94000804c1d40c513280310001d141800030f181e203c007005500340d800300e0f40c895520a0003480b180e0750f00e0350b4000403a83c0a55402d40c0c0003803200808104540b040940052002801490f120003810120510164085502505800ca611240000ca403901c0320300495003001c25400081000c0d01d0a0300b842c000419800410a224140043d0107030440e98135030340381d90306803a04509904c4100311145000d030f25001c01e0b048010203040740d05c10190b550b1a010b6002e5820041c007a0241c070380740202101d040b20309140468000308108801004940c20311052049182620300c40d100c006040380414895414054103900100c0300e0651105044100700414450000822550f00c0381b031175004802d10105201d030205001c6e101c2003607542d030001424072400b50400c2d0350b13503140030f000c0c1e0b04044d100303490040c50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 101684955 1250 101683705 101683711
    0xa111b0708150702030f0c0712030c0303050c1306050f0d090c03110405010f14032a040b06040302010e27010b03070f02150106051c050a09020909030a020316061d0105 73
    0x205009500c0d409107081507201c5030300e209500f6540130f9803034854040200300c0c07036802c102c900312054490b101c1c020a0240c0c0b28845900860701030349a14040c05d043d49801019039000804805080030240041c2807460392140d240b01c26144141031039620b40020a040341c0c1035004008244c03842074208100c500c20700c00300d85098005e40303004a20000b441110711051001b610800c1c0b18020f840300c10500200700310f00724a0500911803000a041e60f2016000440802c1442c0c0c10038000c00100048008540d582d00d4540b150311403a41081d200e03107082a16540001c1d10f000007907a9090302864050300705081d13200558180d2450a01d04c80004031855858003240143c0d900216101008120141d50031102c16000140064901c1c81225508161380c1c20080100c45641017140c0c1107940d07600303607014800381c03058501644e0300c03a0751009070008035041d01e8010001320080241000040e41c204009003020194040200c0381143c880c0d40f0444030070000761a10000400c489601940750103000c84800780d101c5019000640 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 101686205 1250 101684955 101684969
    0xf0203070c0f0302030601080102090625020a0611012304060b011e030618090f0206090423041101110a02040506060708070f030e040606051605010b120102070308010b030f0a111b07 79
    0x8050780c8808c061800c038495802844c0d4400300500001c00c640031035064642140c1c0b282ca400c081c26503156804980d02150396045600820b0001d044048400001d106400d45280d400c00401140301303003d0301c040c4a110000d00040c0115407150010300300750b402110141ea003284505042011a012140002c00800050140740210441d40c0079401d5102c04600409107030130b401180c14910000301c0d45c06c200155024903181c0744c12030b444180d40ca00505000c0041702c1c90700b0289000545a207018980500c4002403188006d040c0000e058011103026400141c4100842c1c0c1641c00103140c1c0c03a02d0002810b18000e881c4003e010b000d000621808110140c500d0983e0948245c440c0f40480c4102020081900c0700e40c080c010001e035042c4250551000407094105e1807e0080e000014080703003240100700015000c801d40c6a051b900010550f0403d43c1c881111801001d440d0000c0d030860a0600c0100034103000584040b250544031220b940b81ca0f0301c200c0840e00c241541c0851300500b0002d0210303140d1181482e00c1140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 101687455 1250 101686205 101686213
    0x80a0e0a03110307141309061d0601140105040303090b211603050907050d0312020c0726070b0a03020705011104090603050105060f010e01080a0e0a0f060506030703050705010f0203070c0f030203 85
    0x4180a05c00000c114007000149028409000c0050900003000896002d40d50300b0745a090050303029510000113461070740014042c2030990304001d000804900c050035121b042080030001040405c1e40501c0b0344095440010200303903654000c0f001c4501614100e8806000319500b10203024214900c1203004030304155a0b01c0074400c0303941d403010b0542c841d0981e114464200744100c541c034000903c1032490005101c0c00c1440181030801c1d01242c03918004058000f200b51080c41c00414820307030000240c40c40601c0800c8010140c050038403502071042d00030310390000241900843c0e90340c1000300a4104104103115001d44680702c0340d855045c0741c040d20013407000b59129460500800c9060a00d0b2007007400352001a166040b802e90440011241c00324000c01000c0705650310482140060001d000c10160f45000e280048500d0103c0d08001048030700c040d140310312981c804a020000140b0116011045070000d0801458030883c0420a0303080d4440c5010042c48a141c2c5034022603401c403411110010350380250221 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 101688705 1250 101687455 101687459
    0x3010c1d1002070b07140105070801030311010504030905063006010306080f0c060c120301090203061206040210081b0301030f050c090f060607080f030a0b04200304080a0e0a03110307 80
    0x4080e0700004a009000140c1000c9070038000303000000c00501440d031103644200d555091441d24942143d005442c0c03074001402800041080c141c1c0114030709050b01d03004008010a0a01d507a0140043c01c00303214460140f400840c00340d061030184006047c4142c100b51218100c20042000c0c0c01a5a2046072180e01003850300c070002c41c2c4503400240c1915003020705001001400c1c0b0100820076160442d291004492180c0040d070b017640750207103010f58000c1851101c090b0701c0e81004400c0083c0343c244046542c449a00481c20030026136140c1403d01c1d06080d4600705215280c85420185200d01c642c100c110205007070020000040009442e00e584400740910309540549460f2400c00c03001000c1511001100850803012848500d0240700a00031940b00c0c03100319107062007614820b82c1e08d03007003101c4200146d80d40b009480038078106402103200e5402010303da440100e209212104940c000904090650000030074070125007400f40845124811b0024082802c03d941c0e4a000c00c1e08151115240c0c1c001d010700440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 101689955 1250 101688705 101688709
    0x10303021e030904050907050a060c06050a0522050106151206080c03070303180306050103030c02041104080d0e0301061d01060311090109180f050a02070201141812070503010c1d 78
    0x4031104900381d20040c600e0420700030200030143c00c01030807092082c00703162000600b50341d0b6a00007d0042220340c844445a40c861304041d412248020001014241408200400000752505401d907007003900400440103109405c00ca8010001074001108090350402182412500040581c03d43c0d5a003041c20320240361a02c0b056038803204004020354041d4000c0d401800001e00030320f07815050aa41c2e1b580102210742e41e032904016180c081e4425404036210350900e109505190149003e5808000301c864500752505c986a07580b4682003420340d0412607080444845031303900f900410000c0852007000c0c44000c201510f1089210800e01c600c1021900c0d203810550f00182c0c032400d9411000c4161100703800d042c580b5403001c8800c81d890160075619036590040c03c0f192030882c85a68007402403080b0040e203440c02840090315030000d520040900b81d9051004280d2411040c8004007480790554403404008850701c2d80b2841e1040c90f4000310303455404d00c00c6080ea05030740031100100340004848409003100065007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 101691205 1250 101689955 101689993
    0xb160e12102a0503070309150504060e0106050a180617060603100e070b03041401050421050313021011010513020114070302060c0c160905010305010b06030f040b06060c011401030302 80
    0x4042d00c200c107600749100c0c2005002c0c5014560040c480c1c2000314001810b5940e498005c4820b44a046441c1e9845c0c00f4401408036500c10301048040c800000c00c48a410007001840400c06440b440315042540440852000d040e40c005c440104500c1c00c403828040c01d51010603032202070407076550b802407090a429000c84092402a415611100000390031420b0421680c0f0300f09074401801030300c03c040c0441001d40c240c0c009100d40340c4034034091149595008105025454504040f90100701000380620034003000c103100c00c002c03520301541150280000c02c203800095403813000000440119500e08020040d0301c0220221086040e0300c04d0382c5111510055503ca80c0d810b000b1400301a005900178000601001040801401070300c518004840d02c644022200c110094a03680191407140d4560004204000b0240103941011208a4205003145012021109620300051015001003071184c0820700f1615448119200d4214800083c00039000354400030494400a120071001449403880a02500c50344107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 101692455 1250 101691205 101691251
    0xa0b060a0b030a090807051e07090c08060d021c08070b0604020403033603050304180902010212091305090d11010c020a02040510150809070f030b160e1210 68
    0x4002030b0458542da001d001c02010400000c0b2a0010100310480210b07008004a594010800701c413000c0c00072175615800c0c02c107299580200509800c040e030040040d41c22a1030940e2009080d20300d04e00c00b500c40c0c000159030001009000803011200101881407001c10f000520005020b0840c0790402d84030103042c00200c1c46103100140000d40505002c1c84450313001c880009141c070a0395051124801802c4a0301010403d41c0d008440c240d00004041140200c0c140f0512180d00711110300300701c042c41c0c940020307440d180030042800b620800000e00c91159581e0351380c0b8450460102e1010015841e00650640e6108840340e42c1d8800308024000c4405900c00500422000b099290f0140201040b10741c2884054440904624002c15041c24045444400c1c0703600107070300b0307565984c8010301380c107100000904194040e04081200503000310301f0b001062103d07440a82100f0b001c902c0103849141201c00703c40325295246d403a68040101160101081000200c810b100b00b050710042000340d000042e2507407001c00d0b030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 101693705 1250 101692455 101692469
    0x607050301032006030c1b011a060d0e010f0915060b0d020c07030219150c0215030702030c01140603070b0309100504170c07031a0f06060901050c0105090a0b060a 71
    0x30801800001c0310701150080c51840c501220600f5040f1400040050b0821a8a00040b5002140000c82540c0b031681c0d02e0300003007026000b003000d800c480c2e070545505144000e0041c007500000480441a004540c010131502c510280200070b555601100d120141008001c195100030b420080c0da070019100f44500000c8813180c01c6810304e8400c3d4010000040c0d000080030340618000c000c0000056140d414900c00d2400c0c101c00d00741059810046001100b101200b0080d00b00002c1b01c090310016154124805503001d944428241c4035514008108e1440c407070001000707080c1d42003000a003081110100c5280c080e98084083d60a420340f10411888203000440d4101c069a0110707400f04815151a401250894041c24000510044072207201c600d07a408020390308640d41c4604010801c2c0903801126403030941102d01c41c00e0460803c000102401180a00190f104000c0000d40030010f82c0218102c03903102c000da90082c0807520b01254034940344e00386030f1800d9440540c1b4500080c5039103841100b2105032401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 101694955 1250 101693705 101693707
    0x81603181409060f0d080f031608040b0705031302030307240e0307060f0b06040b0403060b01050903060601080702031314130e100c05090a2303011803050c01060b030f01080f060705 79
    0xc0e000401010071948040d103504400c44100420109911000411f8052401556207a84c0e0078601c4034411501d4070341c141442000016001e201c0040c00380a8200c2d003111980c40c10540320345403c00040249800d00700020f515100010380349040107410780305040d100340103400002081080c00007100c20b480c4410001101500100728220000c1d0090f800484a0102014006801d60354a40850203950042c0c005204082e0b010a00f0400c0041600525003258020f103001402c102c281d03000300c0d540342806402c0d58144400f85001038402c074400c00c243d400c030002000d111a18165140351401d868012040070a004034200c481150014809005442c9500c2401004104410102c4504c000802c1050710308804c000e020810015180c1d2045403901c00792211800c8605200da0000d8900e00324034a81c00c1c2d450007030741001100b90410320b140613440d4009404d814400c0e82c42e5080003940340101450b0b04605130722a000310911100091a4a00794145c4e81100d08a50a00030000e54050380c3d00011a106000250 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 101696205 1250 101694955 101694961
    0x60f0109080d05071103010510030b0903070f080702031f020a020601080703050703030f0504050a060806042405010e150a080405060106020a0c090b06070c08010b010905150313081603181409 83
    0xf128000404829000d200104c401440032000030703080d44c5050320f08601c040403125090050224900c0c0b0301c1d8101034510020351030081d580e920740e41031000211b00030b84a00400300d054029518117001c03101400f44c6034424221003106103c100030003034204601c1c00d0014880c00300003090101000400900b52900070004244561030341e074003165076140b401c0c030310f10030040c05000000f0700780c0715403030090050060384d15914a28035010003071004840c0020152a8191080f92150860000005884068403820700e09080c58840d002c0101d420050000f140d500e00d0b04c0c00140303801e01c880d80089054021031207102620046c0e40e0380d21080340e80c2da02c2424090a0301c00c2c0c4d42d0082000c80c20035442000607542c0130346414186003d40e11421100d10b0316610043c01e0380d4440c3c1c1e02159a40c0d0092161001d44000c443e0a0b900040c0418111658040186504440d1034890004c00c14400e80205980c0d000500360100d078822000c42c0b40040121900c07080c0d804c00021824000709260310a000c140906c61170241140840b95 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 101697455 1250 101696205 101696207
    0x50d020616080408010504120c020a05010305070509190918050d03090c05060d0b1002030406052a0a0c08150f0f0c0f040b19050a051210090c0206060f0109080d 70
    0x307032244003421200212241c110002070000780150004082250000074035107040c1c100112030300c040c1900d43c001c00c003924400800603603815024605480c820b1a0005240e65141010b848c1ca125914000340e0040d0b141d40d00700900803500c4a810183c1c1d042c0b1006000440d08060552400143c8060042042d0858000c000744184a588040d80e0940585032100c010781e0781c1c0e00840e0700380d40306940c070300302844d10349561340024204580125040c3d201c510055141038508240100075000719881c8100f20301110303060f004035481c500003e40c3c04d030301c80c5800e03507415199034548510241e040c0e01c90307000103004281d4130b04801b00544500900c15000701070b80440e65990100800c14004005111902d4507105014558010300c00b0000360028016001623035540c0c0c075006403104c1c00082c0d1003c1c0c0b2810450200100c00300f896008090b6541d51807214070a82c0507403185404a04034040c40d4108212040c54220110044c0381c0c00030302e29005000c1543d0701d481c00e021050044445005500481103d0341c468000000c801e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 101698705 1250 101697455 101697457
    0x20a0902030408070f1406060603060102030d1806060e100e04021005071b090914010207170d0e3304081c060e0c0301060923010c02040f050103150b0406050d0206 71
    0x100d441031441504e8140d0660318080082c20894040e02c3c034200f04003150551000c204007241c1c206004486013410f519040300000c2d500d1141045261100352952010181c81c030760200d60280081c0d21000500c2078948405030112850300071204e1008a04200c84005801d6501410b0720f07001e55000340800507048400041034803541e012080c11200c1703086012004401d000c0c42918000501049003011410303203407604141001c4165480c03912001d0b40f0410120300041c8414021602d2400d400e00000d413101c52940c0e0b810001c010103100c000d0203005e50011101081d520581191000c00c0761001070316013880d584c040700e11141c42140c00908501c2c08100318031040c42c11148401000600d1380c004100c483d1503a10281000c05e0940381d402040f14007100521000f0b41000004029000c0c0f0410b00c0c2640c006000000c6408150018082c14002c00c4160f441c2591126040a08420b54400040c070095a50745421030f01918010041410305c0d00e0b20a10100c04d16080c041d12044800041c0314115400749a0200045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 101699955 1250 101698705 101698711
    0x150305061305100f080610171e0c1c020108190b060c01020406020f060f04110a0e09070306110708120604150308070b010f03080703031113081e010603020a090203 71
    0x210200c15045452241d005005a500c41c01d44a43c509407814a0300c1d01814820340c15030441d58481d0400d208101081d0344040e40b820444000303040c20240240c0c6248068100703a800494101c90020100000c101601c002a801e51103840075905000c0c102164100754a00c8a00e81c1d500a000455910100f005090600c1809407252fa001d04c00040b40100040041d50303580c07214050b1545650040f0f403c0102907010300c42070a00948800c042e02051030160048030590000820040410405443c64040c640b038030b0f09410080d14050a8001d81400d10166003940c0744d072948402c907441424000a025629940e400381c41da41940450b60706e04040e004802082e038442c00a1045410030303500c102d12070140703490040311701c021806400c29542d19400b80c01c040c0145107050b0401d82e80889078070710400000386450100c1b8040303501840d0000e50341240800c807118500c500202c00c61070354008070022940c0c050108003074a40e56114014821400840383c00749080e1000791002940c813a2823510204100100c83c0c00450b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 101701205 1250 101699955 101699959
    0x601030203210a0f03020408391003020703031b0825021e1c081b0702100e03010603170a02070e31080a030e0105090105060319030c0803130309090615030506 69
    0x2c01c0a40314040d5074a0027040c1c140c250246500c0980541d80c04c1740e50445c407000340d845c2229a00c00103003040d0101d00860f055031074004c02c240c1d0001e41c1505041c400d50000c0c1c002980031401600c01d2440340d500600107101070303070004800055140110f41c001104811030070504c8080d005880c0f004e822101030042000d40484211440c0101d04512410300202242c00342843e07034076141c1110300d0410026102020700e2044031406d03580410032803040542d03a106800460241d4520f0400703010302c803e0011a0140960364002000c0c8900740c1c2d2040c03040f81d8448043c01c1c840565a00300c444881d503459455101200549210766100344c11100da042080350422003d204e5030f08030384070402c501c10a41d5000420b500c8a080301d8002a40c40c1803102a02d1400c0c001c0030b0704108820020f000600344100040d8992640c071911200c10082a5a95420140200010404150081e607410b40f079180c0103441711241c6240c0d50007100002c3c1d1341c40c0c0c08502440d407840f40c1400c0c0c62504540e040c10074440c0c42e00303400030540944000e0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 101702455 1250 101701205 101701207
    0x9020a140d0602070605010f141804060212070302030603010b0913020607050f2d0f0c09100e090d0e03160b030c040909030201091202030913050c0403080c0601030203210a0f0302 78
    0x800410b00b40c0c00240a180d00c40c0b540010150f140c581d100c0301350003ca80000c0d00802102404881c260713501503107070550700038100c00c00702c1a40340c0d454901c000344030341d144211004002c3d5003086105901980078503c190341c10380081c4040782104080188500c1c0c00c486c1c808100c40303c000c0c80c10260401d00098150300e03101d2000c450180600304600392a24001c55a10961181888100302100031030000c0054580203000041c0794102501e860540c6403504031130a9030066404c00300242640c00c00940c80b030010000b03030403151600e040814905440b00f4a220702e100203d4100b1b1600c4603d4180011123103111031004805001450070404442c1290740301a010321240303141440042003903c501c2c07103003101592084d0000a181c4810340380400c2941000d20010702075400901400015480d0014000c41d420740c3c0c2480000c0a607160303110a4028000c9400107000e4007408228800142c2000130082c2c10307280220200c2c0c10510a0209000e0b4200018140b520300e110b00b88440d15041d070284c0856909064582005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 101703705 1250 101702455 101702479
    0x60207051f0c0f080702030909040804050604091512020d080304030203070218060108011e120204020d090b090705060a0c03080403111204061101060308220506030a021206010309020a14 81
    0x90081000301c0300d540d1180ea41e6920240038020781004001407940c01500f08842d092604010103512070141c1580e003401644e01400040802c4840d400300c4000d444001e240319102c42c1c44481540003890000c0d22040c00aa0284010a160b01002549007000d9801070010800001340c1e920740c1c140da0070240046017940301c1401064016545c1c08060080744030440c00101e03051401900040000710f06070300803e1644282080b80d10040101040c51043d02d01d070480401e139900c1a840414000d205003036194441c20f14250f035080400c00d00818050047c50942c00320b130301464540b010002c1d14410302503402c0218202003410030020703020b6104a5800b178020300303183c64442e42c0c06402c5401c0200404a076103042d0b400107428030440d504110040000b00a84000300300b103508545c1c03481c540744112003019423a103a5000c59030300d005040440c42d034003070040540199228181801120040d400c0a0070101c203101d502d50000d82c0c01c1d44203100300b030111a001000f4030140b43c0340c03081c1c200008220005a90f001641c80280e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 101704955 1250 101703705 101703733
    0x180a030803070f0c060c05070201030c110c0d020d08131e0506090f030f0106150f320c2d0312010e0c04081e06010501020d02060403031505030a03020a06180506010306020705 76
    0x81c0e5414103400e4a0385c6030388035014800107083304e040d84550360600c0081c0003c0000c2d6400010494179691081d1400c1400b141a07000003840420bc0403001842110000740321310302d007507030348540342e080b502111401c0342d500d404c0e403599850050b40e600580b900a4810b010300101403805800c4002c91140c042c1c243c50701340000358451400e41300d0a807c0680f00c03e414050100c1055488010040c0612842c0b030710402d003100440d0045203a01c400c14113061007160480060740c503071040310201c2c4d0356080d03034100321f170b0243c80d0300c1d0030101d00541d60b5840d1003580d240c4950f0401d2034403408011100c1c1c0c1061890000060307030800d5411040110081c1404201040c140408140703550100700805001810641c3e541c170060380d20304040d16000050300300c90304540100380500c803d40e0b00055441d070003590504010071030030070060b03500400100917800785505100c0c0024690905801040010000340150340134070410194501801102c50743c050300402d183d200707400400c00309074541d014004451051064640e95110a02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 101706205 1250 101704955 101704961
    0x509011202071407140604050a030b06030102121609060306060c0f03050d090804030605061206070509190306140705030601091815260a0f110a030b010b180a030803070f0c06 76
    0x300703e050543c0150b0041c800702400b800707035071403601040741d580d443c260515020a04101d810310004110268442c0400d941c0c0da003c1d0142e80d441040c0c2c0c810013007546010607081d000700040849a401048240f20080340c224843c0c011801500d000c3d07250008118440d6444100d000b00e00c01c003c0e001c010040c031822048a1543c0608110a4015468a9215421400d007081141e001030002441032200c800d614825940101e0303910b42c01441814141d44070006c0705c01107603484800b0031600da62a0034070380d0040700b000215882440035125401d907102c1250f840c000c00f940c1d1031100361a01da0202d0303818182041074800750301c3c1c045001d001d017202c0480c10401019840641200320b420000c88401141c08003004e20309503040f95040e240c0c40030010420411962101c81008401c004060500302c8040e09032000c544800c00c0043c006c0d9800b90703030b000c0c0a41e0b4174800e03024150403e04e200c10745801c00e40011205407606500550959401401c05851074a800d0404e5803e01500d21614040c05407052411011035542d00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 101707455 1250 101706205 101706233
    0x316050306011e0306090e0102030609010315020412060903033b071505121e041203090210110c060301350d020318041b260103060b090601090303050901120207 70
    0x2403030105506007813111b401c00b52148251a00d02e26071060041003043d40c1c8040c80c0504494000d614000401a01302294010f1701c1140c0080e40e00181c007240d0b100400040d82c2c0700e40795090080da802c112402140c03420300303071512114120701c04062400e4500307507400511203000508000c105046885141c0d65151041d40c04d00c05406000100e48003140540a883c1c1c140b0009602c1035102c942140e1556480051003000d00000e44080e01240c041c566688440780240d006e00071198000f8a28050002d01045c02007e40850381c2e80c00440d401000c41881c020300f80002a070703060f5500c00d41c0501801550040c000e007907000c00b408512609003802058402c00c4424445440b4459265010f1a80c41c5012100442e8401920301101d0203a440c146401010b0700d000784c0c001c1002d0940303160500c05075000c3c0c0c0c1891202840301481600f0395107910300000030400950310108210400f6204080282c0d60080151000d410300c1c400500407076000c210b00385039503200b10020041035080c0c0d000181080805c0d00ea9104000c052 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 101708705 1250 101707455 101707457
    0x6030f0a1521050d05030108070909030302070f141006050112020304020103060f0906150c030210111c060906090506060304030e01090e040308180c0a0302060711030d020d030b0102030316050306011e 87
    0x1e803140007030003c24000340303070056118140a0301e19403510b00300c1d079070f40d40d0305208040364140e4501040081503c2a0116149203421a140c010040040e0425292030180c10019514512549200c120400c1580c0104c40c106c40c016184d19a40c8007910b001c80000c1d42c00213108030f041640c2c69a000c102501d44440d80c101900200748002062401c11a00c0c2c00c2c140d10100780c0310244404210200d0001350f001807182082d19451202080e8000f1004050380c640c014a07010019214000900d003111900b1540301070211b030034208050114982c2c2e590500103c80058070010b40090003000010701081c064400105540f10604d00724020b559145140c1404100a0790128001002d043c14010340304c254030340540510304040003511001c0380d0b400026102c48128071000f800b49401040c00001e001c0916a012070014002e010f42d47d142082d020020349840d9051011401f0a14062505000d9480081524801c044102c0080742c0040200425111070f00010b203081e040003c00d01c64512104030700c0c490440344c0c500e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 101709955 1250 101708705 101708759
    0xc05150307030b0405010b0a120b0604090903030b060403030804080c03071e020f031606110f01060801060e0f0c0a050903010e10150602150105060309101407090506030f0a15 76
    0xc400c0c010107440003c142188078506180051041041d50402c46225030a20304041d0b00d0030500a54007406406104c00b045c9d0701180c041000108014550440791180b23110356400c11013010300e682000540c0c029408050300160720400060009004030000346000c0166208890500c0329540c0d41d10075150903d007050000000c0800d03407400714101f60002c020003603000c80c09044c2c1c190f42a005664494032508c1ba4034100552403000c8800f0501c207101144212060000a011035034032141c409010f03010760720905070000d03103502c000380d2061000480b15005001c1028400e1174404140b0b000c0742e59400551030a58955a90518500d03125010004c4910401842d00c1c045400707100e41c0d500c981c0220003a130240701035400043c0209480360440510505645c4115581074813a110300346480d00d4069030b45048040b031860b01800e149683d50079a0746a01c10801c559a24014580b20340600c0014001612030102022000c07020034081d04084d00301079030642c12000262100c960700d4640b01c05003918140340b0742041503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 101711205 1250 101709955 101709961
    0xc022206030b010501020102190305070c0212010c0f02030708093a020901080109080702190f0305070801050106053910060518010302090c030c1905030907051905010c0c051503 77
    0xb803000309030040500f40000c41c146190320782c2581e07a40380070450b03080815a45400248089000b2146100810340103082c0d05410701408420034000d01c280e45540000c680f020740c1f08845940300100300c44050364401d9205082c1468103040c8040c40c448002210030405a070741305100c0f080242601e85009508210b4440c60000d114010300607114810303040000a41d05040360b06010542c00401c81d007a4590640301c11010790316501c4007070a9030308550000c4241c6c200c401800003d1200002d0341c00b05540c3c80d000200801d0343d071113506444600c00c0394202e482d01005a00114454203580860209003803060a1800c0d42e0745503400900d00700503080c40d18070700381a9203640510179404c043c104400341c03a1425441555a5065400064002400909003c3d00c4040000084c1c81205041d0a0b68008030110f009000100661701002e80310b03030000c60384504284120344002542e894040c0a03080e4a81c25418046100b5040400440300d103181100d00303840c1c0f201e1500d40010b55845040190f00712411050300c4d00d8a0303007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 101712455 1250 101711205 101711213
    0x215040f02010801050616021309061514060703092315070c090209090f0910060311090f04030504140402042409080309010905040b01030b1905011814010c02220603 72
    0xa001a00038178082c01b4140140e96070f480c1c0301003d414400341c040b240c0610085140d0510700c0a451087d0004105509000b009600c6032211450702055403512601c40ca0813200c3c101c20f121450052020280001f600d03000104101e80120502203150f444030f854024103c410701d000b051000132060705010391158002482400d020f5107444050282910150130743c500f0901100003118064040c116251010003c40070a058500820803410600c0c1c008000f0b1082c9a43c2c0d0525a00324985585c125025001c41c1002904100c0304040f024815035150700e40504080c10103640800741040500d0381c1e9006030b8208008150000c00300c0c2910361000701030030300c800a003021240c01001031800d80d001c064503500078014200e0a0b80c10081c0d0f6415140d050300c00180580148004801600f001c411090304400074060402105030303010211070a0b24400e8944a45203002c2940700c144400c4d0922902c66076a540e610802d05640c807510154042900040042c0008040c481c26841014034081c0001c41c000c0d07070392800704100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 101713705 1250 101712455 101712467
    0x60702010f06080c0105030903130305060f0f0907031b031b090e0a0b06061c1d06100806010311041e0f0b04020a05030601080907150201050613050103051207030215040f0201 76
    0x950181d0106225003403038030500075a02c2110380d8143d03040c0000800024440481001544d0451641c84075100c4d0300c90392401d100b900d40340151821144041c4d500300143c80408030036102400b64002d03100801000f403441c1c4900700e02c0c0f040b41400341a00b10103050008049410820311602044158180d44455441c0c0b8540100700d07140001e40d95696041002110042600002102c0c2c4c03113102a60404e54550403803d03444600320320b08001c0c3d0486840c0001d4650132018083c1707c01c1c0106002c00c1141d42c151a80b45021a01d03001a101c3c801403030340b0a40060000950045800d16141c102420124000801c0001350480703103011070814498a13030314054206618550700941c445403a040d2800c41c601680c07000000d01c4d40c8401017019050000500100382a403400b0854840102070414070075240015040c80213000c0c00040e20b5040c4188004141c41d607502c1d20030300c03880f412039034400001e1107149074007003c0300c0298100e0401681076000d0f042c048000d200b840107100307101e0b030b10400141c0c1c81060780384005016 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 101714955 1250 101713705 101713721
    0x203030a2019090b0f071101030b0d110616030c0b0a0c051611090a02070b0603010506030c120309030604150c080105030c061b0d05041719030c05010b0a03030206070201 74
    0x61030707805a482206010340c81110090384010800a10920b5500c1040e10b1180070344c0c2c009140300c6400500b011070700324a80041c0010038407511210320550804801101a2140000740640c4400260f1038200055001c08098600d800040c00640c200004204440022a20700205502041c02c82c06580100b100b0450340941c4a01e100c01c003048481e8202030300170324a0050501c96125490500360000034800290300d000181e6134010300449117860008883c00203500036460440d201d6060700e000c1412450180103a40c42050050002d00b4903840c00720401880f100e080c02c3e8041d0602080225036041d0314144a92441140101c111402e0322002e0b5540408a0710401002c0c010002c010005000c29a400320354245100b4080310315540300d43c00b0150070200c00c948035005049501c43c050b0354108054004c0c000d0821103201c51241c0c00c14440080c1102d440b02c550382180c14901c8001c1c200386000901908103801001c1c041d000000d441080700001c625400c03055041680942e01440030882055424000d0b403034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 101716205 1250 101714955 101714981
    0x106020d05030702060f0403170403050c010b03010e0303040b19090f03261f0906120c0503060f060d1403160204050907120210021518101e150909030203030a 69
    0x840c501d040c0400944802011b131495100341658004201031610450030140c0d1586080c1d0b141c00329082924018216901010716035199500b0300c05900180d10b4184200b048a1642c64080c520310303501c40d502d0862a1074018021141e405c00407103000d1822505100d022034a500c10348804501c00141d00303010f0070b031039030b0040c0400349000600302e00c2c9070b50059404200d4001040140d071480f030312410409401c01010f550041010b1910b4108001004902515013083c0d4500500180d2259170f00c510605460b1030b401c030b032003c40966480002c0303249410b000085032405802840000c0c541e00301041000e046030311145014141240000150043d45041d100302030f0040303c4000100070041c900014800c0e00b41441c080a41705405d08410302031451300034010104060107806043d90b240c80e00b022803044c0c84c0e8420301425098400c1a02c0c0f101d0803d034a00c1504251201d0301c1c080d83c40c5100255151011b015030503400d4207842c243d0071001803481c0442c000d10b420144a03401071a16440c01d803028030220340080c11890 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 101717455 1250 101716205 101716207
    0x10305010510030819030b060a031e0603031d060910081e06150d02090a0b04080d0f0914030a06050a0605090609070806010c140601030b0a0b040903051c09080403050102030106020d05 80
    0x90400c2c01100e084101c50282586080c411703680984c014a1401c0450703403c42c6000a8207800a03625500c00b441d100d0110300d4000b00c81d20103018003021a441400010080f400c0c3c010700840929414006414401008000e03502c0c00780d440010600754451009100082650b203800c0c04111400005141c4449040d0790805039645030980004030b503112001c40e101c03016140000c8422507002584c044448a040142101286568030641c0030040d50040c0300e4101d1500901214482c6207208070f01071510729400741d90340d03143d090801d0603010245c042000480e80c1440f4100702840020f4450003214410011240e0006800d0b00c0c00042c0012500010300443c1309200000402002a40005501e604000c080c07030198075007206807a01c0e07200c404010300103141e244144c5000004101c1d07058440d0744107001e8200240600c4d8104d400303001c1076984000000340406c2c03060144138041d0780720103c103101200b4801c9001c00c1c194240c0e20b0b003815075842600b003940e081e500040103000064041080400c0039180d480c0107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 101718705 1250 101717455 101717459
    0x3210e010327060902091003050f1b01080a0e2a010302250c030b090c0406060c050706030e0705190302030d09030305090904020609060c0a05190b22050708010203010305010510 77
    0x1259141100300d1010b101d480b10803a0030800e00c0256844110010b50290411046040407044030301c0d0218644011a00b07803040c001303821120742d00481c1c0004500f0307484e12106e030303c90322030401502d000c04000c01d401c104640d1801e000280034010416641c01101c0d0f02040c416560030b001250130100c030b10003c02c50606004018254071000007910b1006064a00710180e202180c1c176162030036040705103a00c041e10088089060282000002c502807005400c01c84040107015a550415152100500d201500d242c01c200c00800c0041d0081e080a041074003034006403400f058403013000480042907542d0280500005140c00d0013103060070800200401e00f113040241c2010715541d0000c055206031100c850140840350007060440d1034503000e4401e0780000400d01c2d6255501441180d40c4c4007001c12040c3d03903d104900703504201108a60b81c03a50000d41140400300b01d9910004034200039910307507560f074021900c01e07640307040410307802d10030000030b01010000076a495165041141c207445000d0007604410b114100c003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 101719955 1250 101718705 101718731
    0x31106160b0f070c1a040f0b0103060c08011706070e040b0d081207050c030d09030509040603030c0515070e04020304110d080c0c1e100c0b1603060b090d021903210e0103 74
    0xa45c4030b0304120241d00401c0d5a00c91410400c518401d483c0100410f650000101c204201c3e504a105030444a40c1d4821483ea40d84140681c030a01c02c81f00c0140130b40044020410b0766115540004000340060310104010301c0e00c81c04103107180200f06041d14a09808620030420200d00181709402407102d1420342e0038020000207840e100e10034010310501040c8d40e00e652004060140041d00c0c80901d00030400c005450b039905014110101700003003225940604104c1512010040c107001d40610840d0783c5103001c07042485c0a102c000c1d40040c3c001c1e0b83c82030f82032403450002e50703441610f450542d01c2080d0302030310384402c5030655140c5085d030a42d080c0f0502c190b00c6001031140c40701c800f80f101901701f100c203a01c400107c0041034030042d0001c03401a04c281c417140c042146110100c039004450b051a0f54003003240c1c42d55040b01c0030b110700cc1e8200781c0354400c1e002c44880000d407030719910701840c031501007000c1401503030741e9625000004c2415000501400404074000e00b0a034005a0300c1601e07990a09050100b021a03040d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 101721205 1250 101719955 101719973
    0x406030b03060627070c081603031b080703180609080c1501080a0821090319170612030f0703020c01030b060901090b0c0f07080304050a120c031106160b0f070c 70
    0x90202c0d0103504c050002007005215140c0008100d8101c1e40c2155104100c0510760391b103084042c8280e02280c100b0011001c1250f141c0ac4000300080d144d90750300c1007600c030b041c001c4000c1c0080000f06818041901d07020700c0490001c1c814140301611515101d0780d0b13032542c500c01c6401c1ca02c070462801681c04805004000e04100411100c080d1a80202841d41ea245001c64589c0e00765145402c1000310805082004000900000103240d0130700800141c0034003214503602110020401c2c40c80c4031a01882001103265400c001e0300101c203009c0410192401c0c0390b10503010781c0352600300010580060340b21803041c43c050b50301441104103020058815a01d0107034080c0003e40343d103119204400340f500c00040c0c0c18942c0780b001d2041800d5042540169522b07907541b016040da07a038015010303443c82051480350000342c811000c00c4c1d0307111140d44903500c2500d142c03075920340f50385022001280076003041d4100001411902102c2ca103007010780c840d003440e141904140060a4000400030300e0001400035004d490070104448117 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 101722455 1250 101721205 101721259
    0x5090a0b0907030b07030c0c1b0603052424030403080a0b06120402011d060a090f05030c011d0409140607030506040e0309090411040c05030f10050d0b0601140406030b030606 76
    0x100380411f0944202c04110b4500d0701c8083d020700310301d030702c00e038200341e0b00e809925000112041541c05126544036503503290070340b4101c911580b100346089085043c1d41d0402c02d921000050091700341c0501c1480d0322031090950360040f141180044e510804001002c07200c0c1c41110540315081e51400d0074455268022036001d60040c0c00603042c000e1583e0703144803c00d07022201c12810980901381c552551003085000d040400c903030180c503255080000d404941e0b4100000c110725401d10580d1410300a18200c80c00003801d08416070382c140c020ba00c888510700414101c8000d0042280d03c900102280d180404004045a02c0500290303c12410101c0d0b60a80e0340d0300006582d848802120f0361b011a0700c40c0c0c1f500121400c02b4808050f001402d0030140002c0c5900721024600c07507220f102800120395141c858401a40741c882c0121740d40a88000a94008100305040c41580040181807590004daa08500341c00d00b900036501003070020b40c5035904000f540c1428803200e03401400c00e481400c0c84503180c101d0191101040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 101723705 1250 101722455 101722457
    0x50c09040e070503030a0c050105010e04030203040303080714040b04090c090f0512100f0b0909070308120c07050a140106060e06250f0507050a060518041d0105090a0b0907030b07 78
    0x21000003100c04002e0140348010100142120f81d2242004130284c134126841c3c1045d2801c0d441c6c00c00000e8200400043c1c4c03842190f0540c080d61a03d403c558046d20388090240041081240d40640c41c00c1c9680c181004001600d241300650344c5507894140000107881b406072000c400c00141000c00c1000c0346152094a041d0b45007100d002c00300044043e241d0385440040e0001104450424440d07900c041760a50092b1701c80441559148a182d817010000c42c1e6581c2c4c0743c88014290203007005958441c0014022031600401e400000b585000881d44686142500030301d0150340c45182c0c108070322918070342485150300415050904040c40119480017900798091002622074030500100440c0300b5004103580d408000758000c41c80e4141085904108da0707102002d019241c0034107151940450324601500c10b0b10203078845203418800b08443c090502024100f42c3d2400c0c052010b072400406c0c0300e10002c1c015180310321850070040001d1100e03801c21401e0b440025140c4441908151014070126450742c10141c1d1040789 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 101724955 1250 101723705 101723711
    0x181b0f0102030c0105040c03060e15070c1a041208010f03020a120813080601030209060105030408160503130b2205010210021c06090c03050a0c20070305070807061101050c0904 77
    0x15100141e095205040d82083d40d546080200304c2000709900f0f01c04242d9000c1e031703420000058001c61155444c83c1600301d15000311a804d0005116620036a49407070024815500e06c1c01c4000e210281e40300842c41a03408450001040105051403540404107900420b036413940c2c046900c1c550780200700ca21a071401006291000a0301e10400c0c0a4400300f1107000b4605120050241c59070351014a071941020b0004a2280361014041201c0358800c0d010f490145410034000c510b0194080e402d00c0b2404e100359001ca851f8042441500d1b242c4124100020050101c208081e80d2202405220700d00001d1041e41d84cc404494403409001d0307a42c0c00100503408195600c001a82e40c020b090381c4500100459003e030500714140103000c03452481c035403c00740002d08191414001600c1d05890401650420042140042c1140180b030340c181c0c401500e150359460110303003552121903d0792101810100542c110354250f9028940c03c00106600c56100580c107404c1c10b00800541c00c0c291080b0000d441813421103446203071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 101726205 1250 101724955 101724979
    0xa0f12110601060507060e0102090d0c0303180f05130e03030c040e09120a11031606020901121a01050702040912020a02120105162706020706031d0303060405070504030605010608181b 80
    0x1027541103505004005091050718441894240d0181000c0e000460014404e100c1610380d0f03454104e818003e4503000034490b01d00c0e6003081d0500440c0c980312503010301500e4480300c40302e0510005100035030203410701e80802a919030821000130030b00803001d010710300603034005600ca00c60139048a007500c100c2c0040345020242c0318880c1103a1703440c2d405a424084d0302103100c08102c904000d0b1316401405051800c0c5c0754913160851950100d000c940e910440d4146818480c0c04087e00da6116200400203640300070800149011551550300320f0304c280100362130250b0310145000b002d42c903211140041d1f94a4250080c4a03c4c03400d140c1c0c8200281d07000c0f40003018048035201595a44080d80d04014500640079a003a10a0b0364401d00203590f8000d40c458080403a10300141c2e003d42c01f1440d08002c103c03c1003540118510b40b07810080c80003c1000412644c10488280070200008200d4000d60b4003c0c10142e40d00c0c20b41d07051040c0740c903e44804505204825034400e00c00c440c0100c414840740c01a1031000c031681d6840cbe079 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 101727455 1250 101726205 101726231
    0x9040b150309010203040c290306030312041b0512150402010912030e04060906050a0e04020a080a05030306090c0c0615150a200102040501120e0a0f1211060106050706 73
    0x110455400c048104020040202c0020154041c600c40e600515016103c26901d5110000340809110b60f0760742a8030940742c5030b0442152a0045030440c9000e011207203040c00f03810580a590505990486085110010181c0d400c0c0d800c0d012080608021550603001800c0c0b12000f0782ea4014800d00b0b66980c400c6080060f05684c0200a9500101103040b002031541b441c40ca40101801d50610034688500d190000100f019496841032509803100030305156215414581d24000321a0b005008a82c051441c000100d20110240b10020720944982c00464a9007032074400c218100c00000c0440141b6038080c021000180c400148807600b0404080c100c1441052940204410380c441041084421380700207034030a840d540c8a4210030380d84041e03160107200d001080c841d203800e070700c500d200302e6000403265950203080e4085a1b020b4040b80001350216403003d412680c030b02c0301e41d40100f80261000b00000a0050701c20f60404a40e00200218201070000e560400740090000d015181d40075251941e00e1030005599 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 101728705 1250 101727455 101727469
    0x1050c12040c120f0c0b0c0a0b0604020d0219020c0904170304020f03010e0c12070f050114040f090504060f0501060225030b0114031002030903040b0c0102090918010c0e0609040b 78
    0xf400c103103100c0c0054094a81403410092a004008030346003003189000041d00030b40003003520006280c00001e4000812180c507503000000c1d001d85481d81c4a5800c00802802d802940300038000d0702003d50a0b0b80d11010100806418032642610890244400000300320024480c00004070b0f45011040f01c0940300c0d121400800da26547c00b0100c66055868150200c100000000f524480b410048460445034410100340b291a21072500ca001100642420148020741c0510444102e44120214507070a041d41c03403090402d00da141d40c0c440e100c00c42e580c00c01e000500a040c0161b20b0701e03c08041090110f545000c9000703648181c10b80d58011143d050404c00100701043c480f41070011a08000642c8807541c45068050340f501008079620310903c24114910600385150013524030030322481c2c02840c24503203040e0204030701d41c2c40010300c41c4995600f001000b11560f51001014040c541c0814000104c504001080342151030807051701080c000c2e414141c0009548890480712031520a980201c4e00004407804525a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 101729955 1250 101728705 101728709
    0x5060c071701021914071a1501030e1c180f090b0303120402010f030608030309030c0c0d03090e060604030b0906060f0103020c0a0809060f0a0c0302011b020307061505030a110a050301050c12040c 85
    0x1e2030030045845047c403460b0b003083d500a410020030601407250000c015011610131029801d070310f400c003000150441300b104003c4524980700d81000c525043c0d8290b6500380701121034100d130000715502c000c180845045403080e040120402c0c1c000f10318001c65440c0d10b0340e600314010300080c10010350800c1202c81c3c2d8400e8010070700414500e811652641010440d0740e0702c0e50881e0b101b035901d80c400c0c02040e003c0d602e4103418116286825440d50700540d4149211910400b000504031500038908010000004070104450b070b1148001d2800f400003400e1610812007841504a44203040500520801c0403040011032000c0c0f805d64070642080d60342410002041e02406592140049010085101200203410404541101c0d00c254000c00500c19042d140300c44450f4081c1c6400d006a100f0301111001074032550180303202c0c0c0020304ca0039038115a40c0c0c00081c030f040e81b07026003100d188295400d8030415043c158151070241404030f00902079450b00d20142072150045107031003481c03400600081414480e10040c2000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 101731205 1250 101729955 101729963
    0x6050c04050a031401050615040e090a1e050c150d02030a150803030f010b130311032a03100209010c020d0f15090b0703050103031b0c05060c07170102191407 69
    0x14180d950f90a002c10b200c0c000300d02001c655400c000001f4080d2401c0b210410703500c450340e00f020b4203150070901000b58056009241002da4807030301010780d000c202120410444102ca00a440d0100c5c050f62400504107460309512a0103452480e0351050f0300d2500380141c1d5000e035a032140050316540d440d004d0801070454280d0701c8400011000000ca100100400210f1042100c00c25980c1c580c2d81c3c603800a0068480d4500b040c0c0c1074645a1000c5c80000e5501050f0340c0307002d01c000c080780c141c0c6003040c4900110041d82d00050600c4841910b00d10883e0409108032944080f100c01c0460410341e000340040c19900301c09400910960480d03512800700210014410f84081c0c0002500360180103420b040d10081441c00d80139a00e001e02d107000113100740d110380141c80c10b0780da16030b82d00524074490303c1003100e06600c2c8a004035082e200501011901d038031140c019000400902c80100002407a01d8180c0d031407058280b6032034040d030340104100e01c00341d03500201d03860383c0c014640b0700200c00302c0a155402d1414010b03040014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 101732455 1250 101731205 101731219
    0x100c02031204080d08011d040605130203070e06100801031a0603150106082707090b03120c0109030306121e0c08030c010902040b041401030204022118061005010c06050c0405 76
    0x443c03c81000240c0c0224980365031582082c617603c1b0034100300e407906008918800b0344080340000e00054183d801494101c0100c4038004405140c82c0c0c0041d0a290194005081915000d008c00c0041e140c891038a4130120003900301408254119103c0d42c5000381c0007021090145101c2000c50056141046281241800c0201e5036100b56100e04008011340c0003550140c103081c50700000d91042a14014054046032a83e00090291510f00406500030701041013185074540a02c1540c00001c0e50341100924144183c0b1000040789000c61501070100c41d8960050644001c0000c50500040d50360359500845d10000d40d400e001c0d4400f03c0c0703041c000400940e0070400513800085560010040d05402641400f071007142c05020043e00705e01030004031161814000c040100b450010009420190f000b000040c22030050f208075136a4410f540381012200f591a508142d2044000c2903084100b4089076410506060756100058030b0400000c000001720382000d04210b95500200391450441e02c00c48000300800341c078074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 101733705 1250 101732455 101732459
    0x20709060b030a0c170103120e0603010b091302040b04080303060a091806020f041205060403030f0c05040303050c1c050408060c0708030a05060102070e0c13090b0a030f031407140d0e100c02031204 86
    0xc4048c0086003040d00c08224100d1011085242c29010341c1e06076002a81348500384802d604c1081400341d01c44108015003582048041264020480100098243e0a00842e035909103a0305201e503040081d40038a00c4185800c100030344544107034921610b000c1e00610050384810181d0400940781c443c90303100e44c0044042941402c01c10101240091180d0f0180e1410422088010800c01c00d80e505020084009001004188006401039026040c0c50328003004944100c1d403041d030802c41c180300d46211040440d0010504004440c81007009550080c0340790702c00c0f4207003480ca03a10342c0243d001c0940f40b10840e03a1110700080780c1d0392081002c0c81c010407503452600d205003001c00c1000310503844071000d01d91195100e1404640d1401c00d000b114280c0c20040c22031410140756448603000f40c950880120104100711341104408880300700a0410a0b010b900c040300c0b082503c00c0020300d0000e006950744244802516045001e540e01c599448101e102c50038500e842c1d080038400a0f00300103401442025056000c100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 101734955 1250 101733705 101733713
    0x5121c06030609050d0e0a05011202190e031204050904080d0212010b1c09080306010c1502030705040510030902130e010902060c060f0c070b071b140105040201020709060b030a0c170103 81
    0x110310f0106008505462000484e9803080764503500500e4141d4101c0801082000030b9441100300090022200c0170050400a01e9042a10701c044645004000591444080c20040c80e007030002c00c1101d4800a44a03142c289820f001c2105a0300040029120180c0843c1011040003980c044903480d0326136031b0350a2034940e102c1001c115a5001403808926007001c211042d00e14080b070703100d4003c5c4d4607013020070709040d03903184c80046800c0041c1090455903070740c2e101c0400e030785810b140c0041c0d4050a1640c446540b25400c2c0382c240501c4440b444110f0040500382411a0301686030500e8501c00710800d50f00204541116100d418050400c4030070007904200c0008070303a5100c080105a40c0d024007107503d0900800e4803070b0003044001d40240600541488605030114003000d01603441103402e109400161003030401940c48020410005c540c070407116035110801c00c801c40d0303810302c000c0d0050060300400b00502c40c10103000384c8041c00010b000b40440341e41c4159580159005e6402c900110380f00d540b41c225190307102c0c03034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 101736205 1250 101734955 101734961
    0xc090b040f0e15060f01120507050c0a0f150209090a0c09080304030f0501060b0309120a03060e040302030c060601051824041e08030910200304151b05121c060306 71
    0x10035441a0034003e4003007451841c180c211508580c0c0140d50703440020b83e01c546c000b00100401b60403613003800381c1048003450960b01800070302c5c4154014007182c0c09001007403e041b81a0110301504554941c8101301c1a012617581030045504558000360000d4010943c04069070304446070341100d4a18400850f0000130080b441e40440941841032000f405400d60b140342d05481d500060310bc0607110b8200c4c00ca031101e000101c0c009810605201e1a0200700665258456212a9002c4d6010b4006810000780d116140e2020080540c0040c001e1030710900d800b007404000183c0e00502480944951112480b002058620101009100600e1908166140d50398240c030311450703900c05c20101500e10501000210034030080b06850b120030700079004503800c40c940700007261112040051165121030011030001070520802c060f2010b00341031240404504003054016241003101007448040754200c81c616400a000820130104003c000050252128070b444c40784904800420640f5500e42d00d0f00134000107100c41c1c0c1e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 101737455 1250 101736205 101736223
    0x303090c03010b04060605071502120a0e0114040c09020a1e0903122105060102100e010b0406050303030603030d1812170105010503162a050706020f0601030c090b040f0e 74
    0x70000c0000306400740901c01501c3c040d20032180891003e200301c1e07010a9199004000d00003201c1d10040c90440c00c00d5805a1486003035402c90001985c070a1410f00e074081c01d00c159a4445000d102e01c540b20f142556684080d60003602a00314440e40205128961038091411001035015113120000b44c1c03400488003c1c40f4100500c02a945203050714035421070340d4040c00140e8020036507900450030070103210340d20a000d00005010241107100c0d0380c01807902068144180240c0708514030022900030020743c00c02c0181c40c03194000070301c660010801c1c0102960008102da030000c105440224000822030034958444000010240101c3e41c490b0040040d594014800f03006421019001801a6220320045510b0b00040b03601c0112809051307010280176009002d091700c82d4200040d110301c82d22071001fa18a0641000b2011909a40051000d00c441c980510002001081101c01005507600d1a214240307420307040d10800c0040d5650384004021038489400041b115140d100d42406001520310900e40d84100712 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 101738705 1250 101737455 101737459
    0x1a040e0309012d05071e0309030221150402031204090204090c0e180903300114091501180b030624090118030b040b0a0c05040f030b0403110303090c 65
    0x512400180b40c401c01e20f10140b04610312146030305040c961001601c40c0c0e03002010954400e040c8034a01042140e00c070100c641120720039030b00c6040b8580341d441841000300440440301f80c1c0614040806882000001c0e1482c6840f001842e8000a80c0391030020900301645103204c00c00e009000640415040607a0b0024400c4401000c2c04200300141501c00725000b0803d01d01043c1d1040c0d80000380100b06800700c2c0038941003000b40c819240b4040d0111400300600d44182d80d100c1ca43e03801c980f410810407440e403a03581c0c01030003011940c00c0010561800540c94010050040c0d004040418142c0c2e03007644a81000012403a0032001d03403000d251983c048029940007194803910400c6150004181c0351026035002c0a03210701d40c0c68a500b8507401f1130040d545104140d03038655a0350020b03d40080845c0400070160301440c011400010981041003110054425180c071000604c9000c1000300b001801140442003120381284010840707407640d02d022209100800a1140a840007000b804424240414400c03030640f41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 101739955 1250 101738705 101738717
    0xc080435071d040c05040204180b04050c16060204180504120c150f09050712050601090504050a02010e0117040c080c030708100b06130308030601030b0301020310091a040e030901 78
    0x1820300019640c541c140100b5080203803140000c942c01071241503054020b0301c2203800c8070045071140b012500300d030031a40c400800581c2038008044230012610810200560544060100c0e1800101d0b003800d80c0325041100c189022100041d0090114070750640f000b41040585101da0f00000c040040d0250078159030070703102562040a0210f5250040d260542850340c0240c1c810305c0900c00307040c01002402012900c660094641d004900092414010b20014121710901c044ca0220365082c15458044141c014103030b168a80424080401c1001034410324081d82441e02c00d41c408941001250020016604541c1036152030301413100300540d14009500380c42642e000c4070441c40300002003503512070080c81040f01da03030088040c148010b407003508564560100130740228980700c51380f404564501c41c2c41d4001c1c0c5140c0300110611036951b0b4540124071641c0c82c11170080d411810140c42c110101d5020b03108001146644141040001c1e121400340059040010002c10000c026002d000b80c82c5d40c031000c80e075400250 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 101741205 1250 101739955 101740049
    0x60e0a02090d03050a020c090a0e1204120b0406020403021c0302010b192303060f070e2205062d040b2b0303020415030c02010b010801060f0c0804 64
    0x54425141c1c0c081000b01502444869038405a440b80e010b20308640840c05050807003d01030b19202c1007075010390440c000c0050390803644481d10382499521b018056121404000810041360700e46403002da511703001445404a5100e0385090300080c030880d40b000b034012a1300b800100e0082020082003024601076002488004400c00400814810b0149104103251101405114610840e08501c42400c01d40340360444082066001a01c2d207241181c0200f00d41c0b194604000345558040c05440c0b14690640d2000e4850702e4030820300c21804018221000380c1d6640350001606076840081000106020407200c803d40e80102c41411a2801c40084540c0140d080007500c0340141002e12003481d540003c04c1a240401700194107012102040280503020181c0a00010805007501d9820b4810380c10291000110703011609000b80c00e50389180340c000d06214806004114840e00310b240d111009115140c4004000d2080c506405180610b070070020318840144451018180a501074a0062080c2110602802 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 101742455 1250 101741205 101741221
    0x403030e030904050c09311a0607080a030b03060f04060e0a120914061204080c10020d0c08180607030c2105040b0109050903070b06010309060507270807050105161203060e 75
    0xc0c0c14104410803912082c561120b00087d80d0340500d011480032807080a90032000e000046140d0010442a02c2c03c0000048926405425101d45184007406501502079031400c0c1c03d0080d40c410f00100b0150a0323988801058540c203c0c00d01200c44841d80c4035040c1c03510300c01c007034074010b1003480d1500443d030b079448890b900c02113649820029500107810f00d44010b46560769964420345250840350040c5094420210f2640801510b030014046c609005200028103000380714005008110240c201840f44070020302401d16180e0200e00359a0100490801251810684004482045c507051b15031802082c40180038604c0d2006411007401940200c0b20012a45d17202c0f00e1041c1254801d503582c000310780c010800900040c0040d00c2081d0301220506000840d400c8a444450681d80c04552030000a4170b0311195074100610721800c4c1c0c1c24402030061405141c2e081c134514640c0d402072402568140080400e0311a1030b44400400d401500394444d294840d240f404145c003501070f103440e004c0d2070352601080380020129 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 101743705 1250 101742455 101742499
    0xe0303060a0603150b0c060a06090207020307030b13021302191403041707020d0b0702011109011403090f102003040807060902131a1f080403030e030904050c09 70
    0x5200000c2070212400d10b40101900140100d2031502c07158140d051002034070380d0781c0c0c001410050f054103000d0032640c03508031441011580150043c280c00c52042c0103840160300e000454500f0340358020340314115600c0d2440040e01e02003280300001d42c000075164015035907180079000b400c2a14000441a80740e8921003500b070312806804000c0c8941c00c0c0381403001401103004080024174000090040350301d0404250086440c2a28602054036030640510502900b03542c24824181ca5441c40c0d0b121078288154400001e00181c15007201e8140e007503020010512080c0c09100c5400351117103820403900100000100607028007020380940a2910000312102c140b19058403c4a215603407110f5140d01c0c0903050341d644402807032624400e80c0c01c1441c09103090b8010181d8440e400700c02140c2c00342480c0300c0c20035030308015030b58032104003000c0011904e5101c845800d030080750340c9403c00c2e81400c0100d5480c1644020a103076004504019501505000034024100031540042a500109030f03026485034074031001005c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 101744955 1250 101743705 101743711
    0xb090102060a0c0302040f03121d03030a0c0213050f0f060108070e0d0f0b0106120605030f0303010e040f0c32030606010f03090503031f060305090a06090302150f010602010e0303 78
    0x3607084000000d0649071a6800502000e400d824010304043c2c454000c555112525001220314a020b00e50078004660270070310805042d00810010242d64040e83c0100b52030380078000c2110240410038810804550fa098001c00c400607084104208a240c9000c00798003250040c0c2d01d41c100d000d41440401e400e54854040c05114408070345808030301c031401c07030140710700b40c0c1e07040100351034028036603042c2e130300180300c1c100b2881c0240040e0b0f80c0c08880000440c03420b8204c81c0203912007442603210340b800f859481d0700802a03d0444112a034481056030340d50401301c425404e00c0c580100780c0c420f880c50100b4483c01e00d9901d110012000d04080010502d40e40070b0400e0310b00710860155042e4043d4000440542c482c0d0300f01d00356401c45290104803c445607840601d542c0040d503c040c05040c400d0001104040840201c600078100380c0303428442070410f424034a13155803003400c010780300310744031179a00007414020405200011611740e08107000e407404020359000c0721002c4c00380380c1c015401c0c501048407856000082c1d0380 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 101746205 1250 101744955 101744957
    0x9041a120307020a060f051b010506030c0303090d030c23030304030305090604051c0203041d090d020304031212020f120901050108070305030d200a090311010903081605011b0203040305070b0901 85
    0x100d907170a00300241c414a0318008142c00f0403d04101414000510a800c60512280240042400d0502004141c146842d41c805980a03074005d00070040c1a507140b4a24810007609400e00c012201c00d0b90810701080218070031030403032114183d030359031441c81000001184110b0080d601040b15464003048591180c0050718080d09917404440501c412110031035030305a50b0441c500450b4130b0b20340e441032405240004412440e5080c0c4a507400c0150040c000e1103d22001c2100d403000c0c5103000d00b584e0f02c11400c040e5461191040141d110044407a41d04154122640d0041d240d400340d13100e8128a19900c200181124509525401e02000080c02d442c00900501580d611001075820841000c2000c0e00900d10f0403000b00c5140a40c244002404030120028951842c10350f9a000c0d165042d1b0500d07141c62240c7c03010050400400550400210b4104400e49180424402c024481c155460070b05c18050b1074101074003800101c01400d01c0c0601c94001006200300d0707110381c0646811540d1201150020300580041c01c3c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 101747455 1250 101746205 101746219
    0xc0607030b0f0d17090a06020f0601090606050307030f02090d0501020304020f040b130513021c030206220602070309050303030a060513020313030c0f0803040305040602150105030316060209041a12030702 89
    0xf000055401301d805107040300640b091428003040000243c005046507220030007607000707103c4c5c400011105200c002e016200050b400d0060524214008101e880700516200416913203a98030b00540303045030110340c0c4d854801412540c5e42540790410314002c0d402518103d1241801c44024101410540501040c4080042040c801b4881018552018000061040300b01d400c9088507a0018aea40e400c02c4d940d040890b01c40c2130709451642c074010386010000740041c6041e0b88900c1c0342d24443c15451041940003a80240c001d80c8629551805a9564005070440741e810301011082146c6030700d9a9118104960080702e81840c00d41d1002403a80c103e1000341c80d079070780524420f4800e0700464010380102401512810b0440d41c0c9078a580c84071981ca8005860440000b48009400c000340c50341044041402c5500c107103180481d502d08000682d69100b600c1c1180700c084032550010f01880155810f07a40c51600140c024032600324280c020019140e600b01929200c1d0300305c40020001ea02000040d20300b03980d4007410710 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 101748705 1250 101747455 101747479
    0x60111150610090b12010810060302030d050d140c09040f0203040c14030703050102210106030b0d02190f030602070203010c0906090b070804080a0309030209060319080901050f0c0607030b0f 83
    0x4000820b0308400c0309414002007400005168000d0350040c0448002c002c11455154140b03000c0d035013000e041c400818003140c1402014805645c011401c2c030800705950801543d03501c2d80d1030004000c0c1100d0701c0c10162807910b06040000d91810240145040d01c000c41d02080001010002c0c60200d00080d28042c00407020310609000c02a08800c2c0e010070740304010206c481e42ea030f0300d558441c26130340600e640701c1c424602c108428050b540602401c1740903002c141000d02c4140707050f10200f4903500c4e0068000e0b10500001c40040d607804101c2d081c0c0000740c032103a02000d25003a2a41032440103540510803ca009621700300003058494072594005003075a409680b036101c408c1c0781510380c19040e0022842900e98a904020014081a0800c4850b0340d05209840c2c0b802028a10300402000c1030005050700c0c065004404100380180c1494200c90086500c031200340d840302e50220041307400b40101e14074049070352000100d6600352800040c08078461007480c1d5050154040740c8040c0075a0001c20608143c0040f502e03914 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 101749955 1250 101748705 101748709
    0x507060201020717070309180b01090e070e0114091806090c030f071101061203080405010f0c0f180302030a03110f07060c0f05010f06120308011d0708070203160303050601111506 78
    0x10402d45000f4500411810344230344446068101c111141d49100d541c5411800b11945c10844142c0201218801241d00d8500414090200042d440a2504020a6006001c81c0521400c00d07140c9846025042055072181603400481800080c3c42461080060000184498001d0000c0b00d2203014000b04207a215120810309803141d203000403401100355200c03140421641a11900000c0c0240203903648000c5060500b01182112954103000b42041d003441500810540c011074801083d600d20724020440411344e404403003840c10b46400c025898091076070000305155204488108a4082c1d90941c0d07a806801800603594000d11700c11040403a280344080c0b00402c400c48500d00c8442d0045c03002061419041440900302c510390f8000d01400740302000800f003410352240b102400341a40e01c600d030500b1100007619240322540144010f040201040000f001e030f6100f0301c2500c000818034980e40fa0410414a80070380900000c880c80703070014110500c0014400b0000400c04001d070a000c50308501e946a1500b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 101751205 1250 101749955 101749957
    0xc1232040c0e160e01030b010503071107180905100603020109030605041406240a120f020307030503130303030b1906120e030d09030e18070f26040507060201020717 72
    0x3050740d10036550080080c0940b010500240704407001000c0504a129a0701c1c050300406a11054034101031030210000307401e9030400c04580d040103981c2005e07a01b10365135104030707483d26181d500400901202c0010b049207070201030300214076440c460010f6604c016441009441110154807001c2e001555880c000c00200324580d10003900715015000380e10104103002ca8803881c3c0082501c000b80c07444121034076240d00380501000745070508022a1041c4109250200d0302e031703c3c8900e12802400000d4848801c40444d642009a08001c50340841502c1e200c11103071304400c1c2ea415007071000750003090922001f8802850590860510a001c031100151840e00b800e00445660b00d60b040102145980d5010103101030b04200054240032150000100e03507a85c1038940140071300d802c840d4460181d80d40c180d02c00c0b8565803d04955034002c1407403070300185c2d090f09024111018402400f4a41c0b40c51402000003c0300c4503018002840b4601800449680c6943c403c412400c034819020040c20b00706031001c003a843c04100303070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 101752455 1250 101751205 101751211
    0x503010302060a03090b07110616020c060c0109151a06030f040b041b03140706050301030804030b04020a0b03010e0a0615020705150c01050c04080709090206030601030207150c1232 79
    0x450001017041e4141d962204460003900c0d603030017040200f900c10074404010020039501c04410000310380e0400301c4e028040d545141c1068201e100700701c0800c12444005095100d0140590800e400d16540b88102c0e40d01002030001c8800f2280600e40c80130b00071991b080802c100c0340034801010545203959100e8480040d40c60b80030b001201d01411048071a61440146c8058001030b502800030b201c01c00001e094590b00c0c3c1846036000d41c00f032200c10710040020580c1401038408598000843c80032030b9031130303100041900c00300303801c4060141c0000c0000700d525502034070001d1003076801e5501005078079103c40e80035031240d0b140014400182d10142d400d01441c1040380580c01c0049100500c2030800b01403102241c25103004560f00800354001103402c205040d02046814020801910f04014503070030f41c0c0114101d840002c000314185500018100304215018085c0d4912600c0b00c1400c01210b003444600501d060384001c0703052902c42c00c11807460b040c0714640c132103000103607500d00c00d41c0d0540c2020440f10001d01001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 101753705 1250 101752455 101752457
    0x120c02030c090a02090102150c090105031503011a03010506010804150b01050c0a05060403021501060c030e190b0414060f0d0903050c01050702060712050912030a06090f05060a0b0a0503010302060a 86
    0x240e01298050303280d90b0300e524010554284056140c4446100081c42d100400d50840345c0c6100c82c006008149001504950300e0300000e20741140d40340c0c1c81c1c8040104843c5011700c020781540ca8440b60000740070841c80d16050b8040700301d00a02150700d92030011513a4400544002d010b0f131b264140c40310800718840d03103c6890040181400360800d400e001c0d0260411158603402d60781c50f04480c0c100003c05605101c2c480c4190000840080c0e25410a0402021040b00342d5000781403182094002009540c0d0742c0301c08100c010008544601c43e42c56030741c0340380355401038400d00943c3c0c2140c1044144500d0540150b50741d00030040b5a00b0304100581c25070078080e282141e81623080c44000c000000c1d0802c000c2c01900e201e140980c00401e41c41c107020300000c208106920518011034609418805d40007070100d100c5101212100795291680c6440486034010700c0581c2c0b05002c550316244c0d0f003a4102080341c00441c0300e160308403420742c0321030355131002901a07119080d00400090400c0005000500e001806030402c2446 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 101754955 1250 101753705 101753713
    0x30c030c08161e0801230f15210f164106030a09030206060607080a0f020c0d03030b090109060503070b0a031107150506010e030d080a091e05010b0409120c0203 70
    0x70381e20381c4d6400c46105651204080050703a0950390398000c43c2c00c1494220b01c45d04000c801920b0400c002d07104500e07804003500e204540020100c1c00708840e0603504a01c1c00d030034005031048225246961030751100340000301b101c07900d2146030010341e01030b100c110b07800c854500038852403880001900940c2a1501903286144e1040c841145174030680f910006540b25031800f60002800d0a00e03810041c1c5400e1006041c00e10408040089900180c40c0780c1c2650800105400c011404400350300c0207a0a00501c50312080d001402d2141100074503a0680180c0c050a0080e98081c0d12642c0311f071502c8003581d5445c0a111340591000e03408000c101c0c8940c0081040c1e225070f00d0300181400340c02c10300065a500140742a41c1d000034025100c00001d6051007100d400420900305019100352020120b51640d0315145940c042c8001100021110341c0b0907000080c1050b808028141c0f1000030200c403d44861060f032781944c140d0f1800d01407170140d003810b106080580e9000000c04242c4072030340700100c1d001101007008a8042c05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 101756205 1250 101754955 101754959
    0x6090f090316062408070504091104020a0201091b060e030d02060408030c090613080105060f030d050a02030903010e01060f17120313050a051018020f0603040201090f030c030c08161e 80
    0x241034001251034035100800d0242c013502d02090b05240680c2500b200f4811458040a000064440d080b00160144140c0e000b5840f1060420280d004082102e8060505000400d141080c00d0400d01c500042d00e0b10758031090041940c81040c1036603140d12843c01000f5900100c0450040340c5c0c04800785034045c20b5603c40d81d10704400303100420f40e01d0b000180410750710443e8003014040000f0078000d061f8810019215203d04810b5a40001d644908861416060042c0064103501c0075200b0b100303c501140d0054001e01c1306001c215045402402c3d00d01c00c0f206506241c01001c43c0040440b040100346081c503000400d10700544a0401c081d030392000d0102c041f1052125503c1000407400e11030b6400c1e0070b00a101400503a4a0541288145c0f275110041da8804c10417180c1d00700050743c400810308168202900d80c252241e0725480140c1d92807100e5000f0700d8108400e00700000c20007440c0e0f00c1a02c141da100b0f07541036403a00c0d44c950500e595024600b08814400c0d1400380d0611640480700740f4501d51040c407410800800e9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 101757455 1250 101756205 101756231
    0x120f02150d1a01020d09090507030f0207110907020d090e2e0e06190306181401060501020c090106080402121c020c1503010b040902070c09060b0306090f09031606 71
    0xd805644075921190310341081d40e00d0070b241800d00902d055020700150062081c00c10000304040c0c035601a4174240d039a00e101240406210340e126941d0080d0304032046640301003a0402c1c2c10b041ea40b80403401d108090a90004400c14804111141d0040d030315220348a0640c140f20781c10401c0800189540e500d00784240d043c00d50600000f1100c2002032101d6612080390f0b0510380656456000204000c0c01401c207a5070443c41c1e800c0146220007281c6c1c1200c0300003880d600d03442e2040c3c0c01464408001e04807030140740d0070701d040305411b510100480b03800342c0880b041001e810081c4100c0203800d104110100342518000f40140c1403140216102c00c0f4000150381001e4800c02403080c01101540c001e2005030300581c11481c45003000012401034103001140c8070f05540c540031044c222440b43e40542c2c1d00d12078000c00c1081c2004100c10401025100300708052140c140c0f108400d4000e034100b02d865500c0342009501240c6140f002c162250700401c5103002035464001401c403c0d01039a18024000c4035210703a078102922102d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 101758705 1250 101757455 101757457
    0xd11030c070309050303090a0902030903130602070806010e0408160611030109060e010f0e011214070b030411040b1e0d140a02090106020f0c10021903180609120f0215 73
    0x340d80d2025103151115160309000f81526003503000b01d40258003c0000c0703a41a0b030390390500720455401c01805a502d5a4a20641e415030080c0e0903210a8a4000c41c404114113801003664410385803010308446181c0c3e600c0e00390352580a0180c034098066582000642d40c1c429540d0a001c525500800c00170030314208080000000d50300903400860a256a224113108200c03059016a004241c0d00081300c010505010501c42e01c008180306e0070013221010f200d0324041040d61410f9070f5503000c4010a80303005c180d80741482900740e030040b5001ca0b10701401c7c100030b04c00303880d145c410b805d60944041e09020b0540c0390345100149150b0389481d010741c00f0303208118010020311000740c3c004244800d81c0c09441080050303c14000d0b4114180c00000a40d0400a003903140c00000044147c0c62103822600d00340d417985d1118003a402c040e00c0e0614174885000040480c42450341000100a054090610361550985d4805048496240300e02807400320b40c0915040101064400a0f12a0540e000400a09511140e14400e40326 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 101759955 1250 101758705 101758711
    0xe0108220b06030c04050903030a0b032e0e01140423070b04060206060319120306030b07090305120a02030306060f090d0b0702061008031c0b03010c02280b04080d1103 73
    0x400101c00800c801401c0c1800103016060b8251010300150401e009020b440c2c0c00003c1409000c55910f2441710f03110340d010401da034004140080d08018800d60b494002ca040e03500c510308864002c0c07c04101c261031681c141304101c00031a00b1030114200b61074a5039240b0706803e903128105200200410041ea815006000a900408070a00701642e118a080720203810800010034040c07098000e02074030140c1d0441d4a09900e05140d12029940e503080144070309900078607440c2c01c003601c00c2da0207100b00260f050700040c41c801a02d004400b00d502c0c00c040070301450f409204240b0403c005820a0003c1030490600f84003070600c03811008559424904002c011603858a80c200003560019035000c1030004058051040c1900706201c0c61080c4c01c1c0c0380c140502951350388a000550380401a50341c4550705802502d030700000c01d5440c028004c2c4010000c0080003561424084d0405102c09402c099103a405d800e100080b0303990542c4100c6010703455995482d0100e10348c0224140d4118036842d141c8918007219284000e40c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 101761205 1250 101759955 101759963
    0x30a030b060d0606230c0303010303080402010c0803011d090d0e01030209040b1504030611030601050715200a0305010e010e0103080c01090c0b03011706040b0a09060605030a0303060e1003030e010822 87
    0x100c1719115074070b91110007164540c0341c0200364100011800301d000441260f0640c0d405082c1031030a038855200480703c40c201140040c003400000700000ca484c01da40301507000c03c40e12883c0d000191b500c5060b41151200d141c10180d8000c1500c1c0c00303070301c10781303501a80151144690003000010001d80351001314041142c000c401e20039121000a0034030801c200d510840340320b595040303503071030462900400191152082c894041d15001780365025003882d0b07501d600503501304c10038000c41000050812a6001e85034000341e02c9800461f08101c004503000881c8040c0324101c950f00c00c0003200c664030b50780b1540010392040c420540c0c295200d0400034041034040640c00e004004803108103541f90f14203401e4100e828011000701110760014420300002ca081e954101c0d070070040a43c8002651100340ca0254000d007525070010380c140c05484014802e058056100d603040b00c4402c40001c9040c3e481040d4030701c00f40003d00005000c10f90320f070b0944c03c00c0e5120b03910f0540e1000001c3e681100c0030000e644004c800341440d8500301c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 101762455 1250 101761205 101761217
    0x903030c020d02030a05090405060d020d03050d0e1b01140f04150f020102031302011407051516110d0c060f05130c06020d090509100506030f0604060b030603030a030b060d0606 77
    0xc205650400c808800d03005a4409181410040c2500602905c04d02c0c0d100b522854440c0f0204120350b071078240d011582a40204000c240d5440b5203405030030360300514800442140307040301000304c400c000b081069507012140c04000c01025403a00548441c046c1040602c00880240910340c24600d801e0003e0001d8001c0c072402c070340040501d9000401000483c4145c0085900500512400019183d0106451076090a02c10240d0303416089450701c50003400d001a203103228590a076003c03641c12100c0d040c0110400714181c030115403d46400d550410a003a035802d03499000509148910f842144484040d511615020030f003000e410711340d481500c4040c2c1e228500d081030b0780e034050704001c250640c5400a00702c03170010f003081c8260058007038005020b922405000c3c511040000300803000e204c5100c0d014060041c14203032242803003440d00c184070030100c40c42e034000c5250440104604140d0030981e4400c00c0c009000798030300307440d9200c2140a4000f0443c503640200b014000c003680b00510b405060080c04040d5250 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 101763705 1250 101762455 101762471
    0x190e0a030b011a040602060a0903020c0a091e02070317041506031506080715140705070308030103120201060b090f0f030f03120a0501120b070203040302130b12060903031f09090303 79
    0x220000f8081c2103a03000c41c020041008212040d000300d40c3c9030723000c4141d440001d541c28043c2400e13424601a075610316030084a5150102e0b0802c807075801042016119074410340c880d07503400b01280481c8a91000030700800c1810104010341c00340c0740062a4864442c80e034103c850310708400094103465560300203c0c0e20341044108010fa02110348200c038001d1183d00e000380742c00f518068007a40c2c268010543c0380c042080001007018041c40d00401c848110394001c0c1228002ea83e03030304105003550001e0004681c0e440d415049034101038414021002a9000c0c03644c818540b001500400185070800003503240c01558800415106a909200448038440c030700f00a19510b0200e200350700c02c041c0c0010640c094280c134250050080c0240d900c44d202c0602e40c0000840b100780c07224034050389140542da00081d440f100c86100072040800c16040103240b1a0152401115005500801a2294404c40b0700d520140c0c000e00c0051206020400405519000756078076082041d2603030051030654103c0c3d041940425220300007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 101764955 1250 101763705 101763719
    0x60801020a0915080f13050f060907080706080601090b03090a05060a0b131a09041704180f09150203070e030a08030106020601050d030206070302030a0e0d03050405010506060f190e0a030b01 83
    0x1420341801e0f180c43e10000070320304035210035907500c0d000e02800c54001446012804100080200d83e10100303071a0201c0e8800c1c034255280c50703920400c038020212240a04071002a2090140d590180684816154210340504160000c10160001450403515104029404004c40d01c00d0101078013501c00d420000c1610b03070208041c002c0c01c20380600d0158800d031034003c0c0e42c200218000f5401c8044803080b10f84000da5221401c105402d507414124500c3d0f0084000b50000d03c4400004006806805001d82070000c1c4500e0001e0f00122010294080c1c401d808582440e00500d003107034002c0d5400085400d01c0102440080e000c2464681006401c0303505e201c001005100d80c0d5010050f240c014a02114148124045507078003d4440300060f10f508103040d00807000c00c3d4203207a40d420034040d260342e400407907006400c4940300402804081d42c09442c00e51030314000c540e0a091040866010400032280c203031a09a1300000f04450848800800042129400c0040b1250390b51040720001940564100c1040f9410050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 101766205 1250 101764955 101764979
    0x180403020607031b0512070201090b07080609010914130615140310060302010f030c0215090d08010b030912031504091b060f0c020f010926160503060415060801020a09 73
    0x104844c1d44200d8882088001c1d0b01500300d03165540b070028074151a0300c91880990240c030860780d006241d00ca450301000341242d40b0443c118811802141e5105d03860341d8481e0039070704462041d841d01d03c0d009090310008800c074416290f00c101c980d00c0703600000341e0b83c0910118035a408070700c1e400c400344840e148003a00000d4501081800b1f04211104410001c3c030b0b180da400a0038441e0340801200c245903e030020314085034000e1008a8044101d41880b10151800016650306d900c282c900c1e81c0c000c5000a03001265032135520003a00c0c030400704640203003003603000140104004e420050481c150a0b49550030128140c13242d010b101e400d903228000202403d4034500f40c03015178602a800100421080260240c01c4d1584000312415454040d140c80c0c4044c84114012198260281c0140c180442c2210039008a080c0c001c1e000340d03009814005481c50070191040341c0b01200d000e403103183c0d416400f90300030030040b41c030f000c00013244140620000070702c01ea40e80380564260780045040d00081100c002d010804000154 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 101767455 1250 101766205 101766221
    0x304090e070e0f040b150301141e0106080714090406030f05100c05031521030a09080a080414130609050103020108060103090c2105010e25060210090218040302060703 73
    0x8940e080b0a031a01e280c07400c80d00f80d4010409090580241c0114514584040140d0317282600a0300a00c2000a59540d0f102c5102c0d050b1140e2640c103000405416a0726072100c2c095040c0c588541c0c644100d502c4402e41290f6880c800703084c500e83c81354200942c3e1425a0b4612401e00114460064400c00040ea414014184440d03000c1c2e80c030045082414114545074002d080383d80c00344214402954040510010440c0000c0082c94052400c07118039101d089a040000074050000f80d690307078a01e900b5204c07010306840f0003010704003c140c042e0a010a2002000d08118070982c008068010200c0c00c0741c0800b40070590360280e2042469558400040c020355038065070041e0300013000c2c01c0c07d0004074a1607841c60500449407140c8911020b24031803901d0740074181c0c4202882d60340c01c14020320642510006440d201c203240340040c1d5141e500b07c05490b1041a04821a20865005401510201210f46140e1011f00b00e1950f00320303844013008500303d00c0d03526641100c1c0d016178003907030003865a0328140101500300c0b0691 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 101768705 1250 101767455 101767469
    0x180c0e040b0f040302120a45210f023109050319031401060f020705121009050313090b090105040e06011502210d060b0405061e0c03040b0a03050c0310030201200304090e07 75
    0x8000180030904180305109400e8039001507009c1b02c0402400e09001009850500a5000800d10319841c4100303c41c011100c011003a80c0036600080e8080c591003400c640c0a404000d106402c00d100c20700003400d08401c2c1c84900d03505401c0c00b048460112031440f0700840242c110030041566803d40515a96040101a001e00002d4401d501180600303807856a0714000a0b090b190718644442884040120503c2030740d40c0040d2502c903840c1c3d02c548071041140907041850485004014031000010146000d0040400841d50000606282d908258207448860702e81c03c803000a520400040030801000e078041c281460380b241e424280c440b4071000e00581520f12503030000001402c140010f10469071004200c0301081c6c1d048010a0710ba10a01b0702c10410b900850112510b00d02000c2030010381c0340034041c010624030703001d56010402c5646040d281016030000740c640c685600305c044020320041d40207011610510001c609600710b90760305d0001c0c051540d400340d0000007419880d02c4030580020f00c2009820043e1800d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 101769955 1250 101768705 101768837
    0x105010306030816030201110a050a1101050402010c080a020c0d150c080705030114040f02070501050402150415080a0207020306240901030510180c0e040b0f040302120a 74
    0xa9629103c20a0040758420801400310400b042d0415000354030100d03126042c452801d440740c02d92840078006402280c200004901c00e40d015940204040c410148220703030503100c6624045030b684030204142c001d203920310705502c00c1708000720850303981b918211000e0f80700d131429020b40b8180d044000280c608814a0a080c0000c1030144030b141500007060324191400368441241020180300007502410540d01d1058000f88000741083c127101040d0001480f4600a84150902004002a0081c0783c45030344a450700001960070141461391080c07014a802401b041005814082c5a0f00061700380542581c00b07242c0181c55001c1c0c420340c41461041c4050104c02124682c40640c55511500c1e16821400500041e09a8840c5003104c0003101d4105458115040311082c0e0100d034644c1180e02807524142c03002d496400403000096282507902c8541403145606a001d00b010300540c6200c40407030781120500c00c0501c004003030740d41d00340301e107400035130046108984101c14055110304200302002c410083e20403d443e9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 101771205 1250 101769955 101769959
    0x5010317030601020d0f0c0b01230a18020a030624030b011b1205040f0303020c1e031504020402041a090405090a0c06081e01060503040c050306130b10030503040315050105010306 78
    0x3030085a6041c0171502030500c0009070800000c102c840b0000c17980000c01000040c0004242060301c842c811f2000409002c0b9101c000d1082d1041001005562040800100303245103c0c0021082c15005451b450b1510700b804078689880303101d03c0c400000c151b01c40280418085d04d406110341d07414010301200403004c6c01c12240c4900c048204030500d04c020800941507644800714080e1681c422800c172401400038800c403600c016102d10b802921003101071000d51181c19582d031605005401700f03d42c900001402002000c41001d0a00d907a20044001401640c0c0f003582070000050030603149800103030154040d0134140c0d40d00103910810048a030040d140c032240358026030104002412034418101602c1003400d140d9a5542d500c8070040c80e000400b980301500d124003070000036070550800055806148980b64081c0c403152108141a030302c840846404001103840014035003c41c003d03c6655070410f482b045a80c03e601e4403903c2d81271640e801940100c0790100b03e00000c0c101d040251040c07a003d0071003442c0034042d140c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 101772455 1250 101771205 101771207
    0x1511030601090b070f0b0c0301080c0a12060b040609020c0f060c132904170c03120d020a021504230a020102030403030509040e010507090602150c0406030b0a0b030a05010317030601 79
    0xb01d05020b18111040300051220078010f03800da0390151326500c003040a00614025200b030120381c1082c807403801e0078030070800d03074207400d1806440c01800c0e1210012480c90945aa4aa0134060078901d410f45801960321000405e40f62128001050381400e83d20080c99030003031519150b40351039002041840003010501801e1500c00b02404400c0841c1c2081c203402c1058030301c18a00c8503900b5914160714030740c0384c0000340020703400c50742902d00e802d20f424040a641c40c2d0014102455107070a000c1800040c1080b0411403901c01d5180755019100b841340a1046498006840e40c00d0031030401c00381ea05951544000e020914100c044409807008030000001510b603c103000e0340041d5503030145020090500c000480d5102c00717512103a01400f400e404502c024045410711400150040043c2d002e5030b001402015001d0640d2009001c107140104002c0d2146d0380303002d15041c403c4000340480c0b1100d550000c885000019034071760350360280d409001002c000140315455403400000c1600d607041341140c040e905200304401a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 101773705 1250 101772455 101772467
    0x102180405012409120b04060f050f060111030702060309010203010801150312080a0f020d09050606040209010c08130b0d0f15030b06090405010e01111b0c0319030e06071511030601 79
    0x210790280da08405229021401e8070141072541001e00c481780c840c0324545c14818601c1c0600d02482c01104104003221a0341070f51400e651041b941402c140d6030740d2000c130b64154415008082404040801d0701d080c03400ca6030000700300c3d500035035a05950340c2d001300c01400f54000c02c0c0b0072204d281d0705a10908455a295070742d04030354066981d40c10300a12410760b0011782c0e4041aa00811054240d00c441195642c1c18032201000070b00074000c007960540310f8078000170058245442100e040d2070058540c2e294554441e62024a150300103400000207941a14000440c0c9280302c0161000d40760121000c00d60900361200c2c841152840000a00300002c407003410800b040f0307200707802ca8015105880c510900c1d03030b840c1015405040549040705413503103000420428000c0c042c000c0c1010540c0030f9840b8020648082107503980346201141b20b80d01d508103041ca10080002a5110111107100341054141a2000340000c0d501e508107101c10f0b40c0ca4018004e03100003100e840d00c141c65000300702154041c21410001c00013860 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 101774955 1250 101773705 101773739
    0x1e030207060e010e130c0801060503010f350f1603080906030a0b030d020c01081b0a1d03010c08270606191a0405100504080a020103022109010218040501 67
    0xc2c051081d01c00d04480c0d1040d6541c0b924008080e04100d64100580c191000034501701640c4000a150040040b405c80d2083c0304590403582c1c944103c002143c00c0021030032140b4400c0c21080b050742d44000c8107692554850306241d46071004400a000582500700c3c40504102661500b580087c0c1b44000c244000b8044000b038500c8010269050781d200e03070704e1103a150b0007041e00d1044c3c03550501c030f0003105158095000515610218007a0303146540b81d21540381c00c01d100c6641e18081c03900444240501107207544600c401c4924101e68801414281003118082821110300f0100c03074000400d12001c100c00c081c841d070741040240d04521a0b80360301c15882440c09442c0c0002400c44c0780300d00007188200c4908040c0a4501c00540000b80c5819610b540740c0f81c000440303078414422980624640b2030414030460254080e14200c0702c00d4000750004c080c440e40110000d60003000000351301d1981d0010740d4800f104030301c82e2605c2403d80c0c9000580d101203d004454904040401061045003014018010020700c1c40112503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 101776205 1250 101774955 101774957
    0x10503040b060d0f11010318050604170d0c0302070b07020a02010801140a031a01080f03040b0403060207021507030c0209062b0c0503030a0e040f11071209090f091e03020706 76
    0x66115079000034030340701040f03801400c00101e40c442001070240500003002c08074002d072000c0004042a0b9000c0416071150340c000741c04c07a000320300001d0200344452051a04400410b46003807070050309520b4071048411807003685000a03404242e2804004450f6036464015100c0d0009250103891503000800d0b90300c0501400910303a5001d2002da502d42c5613011030320059036021061201550b1402003aa00c2002c09100e0f01c14680b0901d0031401c0d10b21404011142502c0d442d40c54a0710b0182903403230f600069448028203d1300200c820000501035400b00024205d41c611a640d408d00301460340c01003042d103101c00b42c102407040c850183c19000d00c1401e00066003440e2456524140c400c140c9042c00701e01180d907940711035010b0000084810750b80ea4455020060480c044404214035a0300d8507000e800c90300e1040510b801010104100800300380100d40361441c0304014644a642151620241d00c00e47d00c0444841c00303035949581400d0100f20080c1101c1901d400307403603ca100c000300d01c1c2c3c400950301e44162050b04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 101777455 1250 101776205 101776223
    0x4080a020121090302010e19150b0d020a0e06090f0c04050f03031926060108060d06060807060c06060803031509041a070c05011406060405120a0b0c0408070e0601050304 74
    0xc8100c0c61036140306002c2c0c2c103184104410b0009090181c040c04603040307610924014000f000100a158490080030301c0d405c017000d4003510100f610610010003088a80f56444a14000b030707500113a4038428050081c00210316407501c00e0a041040c0601c061000d400414083d0200080048400b01341040e9021213904444040d004110f020110b07040d48602c429150440b0500700340112000c0c2c01ca805000b140381d0740382d0030400945560300070f525000d01c1698a03e000540c803201003181817500000b00038190b800752000298440d61181c00d40d2400ca8290320a03030108150341e120409001151003800000c000752400766282d0319000c0200094450040002441410300c01e0110f03080c0008c13203441e00f90035400c0d5001c01000d414100f80142030180014811180e660a05000b0427076056103640441c01904041c0c40c0d1ba04240c103001c1044848034200350042d466100c1c0e5011800031079038180750a4061894818415512414804a1414804160441d02148500d4414270450783d0b80003007280d40c041e0b000744c00c41c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 101778705 1250 101777455 101777477
    0x50d020a0302090a060503011701060503120702041b020717030c0703140a05030a0c060f09030e060318070902090a0609030c0e1509070e01030510030f080f130801020c100204080a0201 80
    0x2503000b402103104013600a081a030300440ca441d00240114144c4940000c0350404240024140303090f20510700409806401c58100d502c01d2290000c09040302a02c010408600704048094034100ca040c0a0248801644103070740400100d054a00d880d461b28440d100039614003070300d0b0f60701d480da07601543c03000404007418400c28464103101408507101143c1c1c01419203a880c040c60b00d00500c140f50b82d00302511034516008040d48007420701d100e41103245515498035454a044042003041940000b812042c21903c0c0980c0249000c1c0b080c0181405080384440058540041500340951480c0b02d401c8007040c004091000d0000ca4190a000c50403500c0340d04490403d070f65102848192603480400c00b5400c02c00070014040c200390401004901c0300340c00c0e601080a541e891603800003038036091102518581500c1d441d100414010b078020285107015003441441d083b01c1075a40040040315034817405030350358003250760b01d9807100602207410b5035800d205080d810207050200ca80e0b11350034201802418040d4603844 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 101779955 1250 101778705 101778707
    0x1728140c151312170301060f030515030607080711011104030c0b03070c110a09140f060108060607020906150a09030312050c0a120b1e030f010e0304061d0307061d040c050d020a 77
    0x403101c00e40390713510722440e140c0d6543c0d000502060742401d031003000300e401d00700041d540d08200300c441c4d010703400d000300203100580310b958050310354903c050010b03c200042940346100040090081c01d4032900700d848201d81d11851410708806030040f03608154042d070300401c18008021782c40307900759060503080b9001b804002c80c1d950000704940040d0740103034081c504060010260305600e1135a503119400f600100c0686646581c01100d031030008545195100d5800d00204000d41410080321750701610181c441403c2481c822403003480703608105100c00000d088050248101540802e51040c1d00448031800c0c081170a05008901c0b840c000ca501020421801c144546c0070b034800350b0040440400040c1c4010700401d01e000c400004995511805c81c042c0c403500c4000f610000051040b070a030b120202c0302442c1030604090080744d50200364940c040051407402042101c984e400d001c40d82c0245015102d132048185424240c0c0f071010088880c00380300780d1400e1000990950480201c0d1041040900e005a0314441c041c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 101781205 1250 101779955 101779973
    0x1290c0c1203070b0a09060b0a08030307050f0f030901050717060108011802130305102d23072607020703080903010e010618061728140c151312 63
    0x240207040004d101e000d2160b42150391784920034013400384005000303026480c410300100b40702c2445234580c0c5510800024002c03512a00103080c40302004084540780443c1c42612103010f40098800c145640d54610900c060203412407101e1314060f082414040240c03805e04006000500e0520501040d101d602140011070101a030441c2c0380055420b6101e8007071501d0341031042c0e580c400d07a9540f001040c130b88406c0c03551000e8070210340c0404908501c0524440c0c445245501c0c0074000b0442412409a2140c4240c09408c0396900c40621171005540d4001c54119049a200360501c007214a02528140001c00d118206034046408425030f030b001800c8981e103a1110000c0303801080d100310340d82029460070401054407a00c0308000941e003d04ca5030240f05840e280c40080a62506031030b01c02080350b000d01c40000c0b0713032031003955192848840d031810208110115181e800c0c501980034840d40300c5400140703808001d40740401081340b141541407074190405074070729145601954140900c4200380c10317516a41b410081c840c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 101782455 1250 101781205 101781217
    0x601090f020c060702070608010b12060d031404290a0c030c0521070501050705090d030311120c090301061505092803051c02030a140304140601290c0c1203 68
    0x1d02240c1c0e040c03401d2580252a100c0d87d0251000207413481c2c000064040c034500554101e00b00b80c0501000c07546640707040010080c0c407030304100c0c180010402c20200b400d05010103880101400d190307010007100e40c0ca49003074105100018207440048148541041d00344d00801c510501941400c228030400c400c2d0810f14a080700c05074070030200c480d00379204004000c4400c050300c5894413400c000d001a803038404c42138540d80607030306d04c40b500006125841c4c07000c00e200f038101d1202c0a01d141c0e04546041d042e80d049800000c5c04661050031070a00149010f228102449503030000c00700c903600d04401e81440b00004005100e501a81b44c0b0410011510000c500c17010f03041d1152400e0700f00b0300000419500d240280d207400c441007100241c0c056101c2000d03a26030010048400c52507240c6d8030442040704502c85100190405841560202c42006880c0d2038030300c0411072103000c0d01c4507000c0074031f031007581d4800c00d07103400401021464001014080300c8041e840014503a40b159104840804205a5a1a40303e00c0c3d40200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 101783705 1250 101782455 101782477
    0x8071103010c050d060e04030203090d080c0109030c02091303080a0207020604050301152301121802280902040503030a2006040f0c09050f07080603030702040230090601090f02 77
    0x1c849603802da82150040c20100301500040c081c0c0340c0e4030300c3c0c07001c8180c00440d0042d0142e002002107054a143c9046d0b5205410f12070410ba5080202c909030180c00c4505625040340071130580440d00c2d0952400e00465544014840e80441134240b6540d001400d01d03402400308070744a40c0104184c000c6546030025503000e003a0250081040e00c1d900c101e0141c1544183c421642c0c04140d00c190201750b020340000301d2340d2400d410307180da042182d90003602000911818501004d6150100007140059461040300e0030b115000e031441c1c0c10f07036000700802500094070580c4940c2845e0302c10002000603880c00310503610114440c0c200b020200705a03002120700c01501e940314002d24001c0790308000421900b60180c0d00c10901440040b9911510707460010101d40003900e4680f5030840010001e4a1a80b05141c12a403110010341038034100000755000c42d0503030300401400401da0003040070f1141050300c42c8540d10f001d940050b40d024060b0800758031701c98803000b06008842c003050715984940600207954040311004000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 101784955 1250 101783705 101783711
    0x30318080a0812060102070b07110a051f09090209010c06020a14030c0c19030804020d02060c01020f03090d1b11010309080a05120a0204050f09040f0b071d03010510030807110301 78
    0x40e14103540385900c00c07040f2814400e00786010071100e52001071600151102000e076140f80c58503030340b03c03203024141c040c0750503038008407044000c101915600b06c90b0700ca1009000e0801e518280d400c0004d8030b00d81e0700390043e0885610512180480760307400b0384280c129507041240181c0d41c2e02481c074202c541c04907030303091440364010010910050900c10001000c10080e00e500351400740d804c808261400102c111b001500042c11403011501601e050302d845400c55200604c00ca2130800c0921070751b402e90b00401058100c0c00d90100400c111107006106803000c600e070394645041c404504086c0301481c18000c0b0400381c501e05041c0090003050340a54410148103030001c11141d00c0f01d100160051590b4000e00e100945103201c1c0000c10000700d0a4000c4c3c130141c0c0d00040006024200880030302c0080d0318010829600c004044c4062030100c1d0910074200d001c0c6e10355030307103829420417480e69810341e140b0840c90490081e8542070400c035a001e1090a68010b0320383c002c41032070b500e9003141051812006100001c9601d54a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 101786205 1250 101784955 101784973
    0x30c1305180a0f0c1e03060c090e0a0c02070e06150309030702060f0a02010c030501051c1e030c0215040f0510020a0c0b040f05030601050607020405060a21170a0903031808 75
    0x10034060f1082d202d031003410040c2501d515050203507901c00070000c895008050318603083c0005540307a0040d24a103c80c5113001800d0640e0307038125000300320055a600050654844600c10050ba05204602c003411400d140d400e45070500b000401c0020b0030841210304211804004204c4902080c0100e86d65160014056034440c41210322003001c1c3d030301c0300302580055031038018a00f2000d8000d003c0c0904883c80101072059070208080b50800703540030340c0c008072101403425020030340c446621004003681d00d001ea9958201b03060144180020804288a80c29140710240010030400c1d0130742e80d07694103551054a080041005e8003a05a10305807860400078044040d04101007004a07004000e001200c201e21000408903a4440034903440749801e01030b40790402c4081203034501505050304007641084001d0b150003011030780d03041480c504003030703010b1495a83d1017800700301c2e810700020b90540c0301003070030340c5191501d040100300b0050842e486510004003804101081da10911504004070001402c001050f204060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 101787455 1250 101786205 101786213
    0x4060519060b0901050717040b18030607020714010302070c180e06040803060d0c050d11040b1e0409020d050a0602090f090f1305030c030a1e03110307030e010b040c03020711030c1305180a 82
    0xd0061074ae540000403110381c00b0b90032450001003241c09130042e42c02410101e4200003120303d2421410344118140754081080d00d000401d1041498002d0500540c0340350741c11440b800d000b042c0e075100c00805000b0b42c0010140004100680e044a070032943c1150b4402c00240e40c1d2608002100f00e9522159000041d40407170418030020b11400904101c04590802101041004002c03c00c600d0070400c440c00560340d840828681801c0d4803183d6083e0008101410700040d81c0c0d142450514030840c00c403055500410030984900300750044031042041240d05400900e0500c101099403540101400d800ea1610801c2c10280041032044440c050888410750390b80f910101c0001e44813036a040b401304400002c2081c2c8040c1944a442010303450506984100e1a6483d032507c12006032080428400240d580c4000c3c083e1709903254411117440d50400e85025031a90894144806011180a6030314000d403c80c00c0300940f40c0d03581d5010f20032443c40e075080001d00c0e9114101080d6004007142d03021480d42c41480d90b840180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 101788705 1250 101787455 101787457
    0x30c0d060504240b03010f1e0801091208070e0d02040207060f0e0d020f0307030806060c01060f090501051201060e0a11090a0609030c06090e0a0b060d0504060519060b0901050717040b 80
    0x240499200b0403c01c180d0341c40c03600b13885100910410014500e498418444c484800c44005008013980c001840010f03118030456003114100d0000315258186c071802c0c480c80c0c98001140030b0380080c16040c00c007800b40c00100401d040c1c69143c20024420342d40001c1000030401164801c24030150b0511081141d08100030600d6540c80641c18402c000d44282405641c00060000440f080b841e403656805c2050b440e007400740300b5150450704203103155540704c16010440710800750f1450001c0112443c0841c1c1c5516217803d02000c281c0c10000a02c07a64107002c018007449241c0300f00d0070b0304a010007a0005d66000c84504180179805003c006a902c20b9070b1101c00285240d00103100010340740104a00a0550354541082d074201c0181e20401c8014030701c1034005040e40201c2d90042c202080094a00c034505017410404204a5008a4003110700710b0b614070a000b01050b1408200c100762010f00030410000b802c0c580002d2160040c0007415041100029214081001100108103030000c0000182c2d2110340710f05c10315843e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 101789955 1250 101788705 101788751
    0x50106080c0d020a031b150210050702012d020f0301180b0306090a0f0303020706020d0522020d02150c10050402013c0e0303070510060806040305030c0d060504 70
    0xc0c0e22840e840458949092946840c003264010981e42c0c50503c0d41e6240e916021880b0310000c80c8010307059000031424402441a20404945d902800400110500719821501c000e0404000c5a241440b0307544031504107810300c801c45205120800c488248203007050007038455640003103600f01020000050105402c60000008880301d48140310880d00482419a03400d0103e81403600396001425203c04035000d13001030340400d03000346009441d000c081d46440040e40d00030031591a007030b03948204000748105003e001c241e2182004003d04500503250700016440002c0c1000a885240c00d5600b0014140c445000c4544c5003803c1000d8030041100400004001d0004680503030100e07030264180c035411440b44000441b242c048030408582d98a0703942c180f0140b941455019802c0c00103080010040f9901000a07104041c0320340000c08500041082c4041900c00c0c5510100c1194800410702c40042d8011040c0c903030200400b000c440e242d00070f07403550700702800c51903004e140c0142c500000c040c140c050380442000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 101791205 1250 101789955 101789969
    0x212004060b0c010e1203040206041202041103180f120d02130510180b03010e0c0d09020a080a03110606030d1101090204060f05040506030d02031b0a0c060201020301030c0b0c070317070f050106 84
    0x1700c0005803594826511045900940c1b2241c20402884032141444044030b405001400c0001c0d24200b8041d035940d154010b403104000c00c00e0810307045880707000800c4080704491414000e820000040a02c1c000680502c000407040c194000c1044c00305160328000500041400624290400e40740c03030390141914540381c0110140782140717580450006014411281250050703c80d2281a99807040210300a402c00030680c40001e484140c0e2001680c0c9144c04070000c0d2a640b00940703074150316440c01402071010080c00100c550070100030070400c2d50340420041c200d0a440e0901000b041b020714031603030041611b4080203502c24900b8a0200b0812000c2078140c05541d01600e080060391580c0c41003603a070703c40d4001c0180050f4002c201c16003803c9000e411060050a501045450071441c079681d412030342e0b000742c0280e40142c0d808001001405071080c1020014203101008901e4241e00c506c1c0151504060301014011190340d1242c4014000c0c9001203e240c0c41e00000795011241692401c00e001c0d0865100c0d02d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 101792455 1250 101791205 101791213
    0x12060a051f0302090105010f0309050f0c01030b0409110616060c0824030703031d130e010501050a0e07080c040905150a0503010c270510020304212004060b0c010e 71
    0x1200000c1e0342062080e40c0d00182610200e0317103884011a82c0b4103095101004040c0c03a0041e000c0015805c109034010b2191070006081e40340c0b014000103045400c00134446201da030030441c56070041502841c0c0350001c2d2005840b020395440c410040e44402060728440100102c0c60410058011a070050400e030203076046070b291035000100e1100d84140c03031001344422507040d04103c00400010380548490700d0414001c1cac0685076052a5003001520b4003192005a40003941c0740c1020004840c0280b02d1240500030488100c3c690354200300240f03044d03120041010342840f11040214440e0510142941c00901d8190030501c80e07480c010301007113115190010014001e40c0303800004602440c1c18010320b406841140e86201c00c0b0346c0959070040b00b900750901c2c4e0400110801c070001c14540c40312030b2100300160543c0c005640c0c880c500044410a80e40c2c0c0c0210324004058607101c000081c44d110104140c52102d905441058081800010020061940714481040002440f0000e842381034000100b08034088081d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 101793705 1250 101792455 101792491
    0x150106020c0108090309010807020c04090c030605060d080a0c02010504050406080c03010c030519020904020c060403080f0901020702010f180503030406090305011401060203162406080d1e0e12060a05 87
    0x43d25442c60903200400280c00a010002d010351081c0842c945c820780034412507084240d2100030504640108030241c90300103000c10b051050045602990b50064016900038140703007142d454924282c00303900c028004021090500da010341e07114600303440c00380c44000d10400074103642d0304100c3e80d203452600742c0030f000303500f00ba0070400d80078002d1141c548980818802071110b1001400d180c0c009500c80d15010f503105509020408031420b00f0010944228800e8075010380d10f091021101c500b40000030403030411603004100b4900180d80c40391041a8003016801c00350040402401e0002800203980c0185416100c0482c00055040c2d0040184d011030f80110020405008401ca0440034032000f401004c001d40c2c4100452411410400080d035480341c015110a840c0308001034020720544e0100390451845910348100780035400c018002c00c1d42e40000c5081250462080d00c080540d80700c00054034030184030b100e10709250039458085c00100c030600040b007515507900e4480c14101c02080180e4100e4002d025050070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 101794955 1250 101793705 101793707
    0x50310060806190204180506130510030b04050f10020901120902090402060f040b040b0a031109010e090901020c150106140a0206041e08070f060c0e1302090111150106020c01 76
    0x80c940c00e68548401805040c0d0b40e400055415250394885803420075403c001c00220b0031480f06901107055004c80e408940307410100c040081c4100c0d0300782e8200d2400c0c600010300540680c90b98002c0122544444275111654840c00c04905012030154002240e000e15215454256065401020114000d0301d840280074a100004c404070b404842009410018100c081405450803071701a2280d002e040c245189016100c9204000c9a0021f0703100e103241c103101050003203036650903015448081f100e0780e060f14140203030800024203040c8845403140c020a29480429031008080d0111400301800710111030300c400001c05280f188900c2403084d500001d0422101e0554280d603102160400d4509a0052041d03444a84030a690b074030400007440e004100441c4081c1c001101040984003850289100c0c848042d901c0c00c00d00195606281500c040040415130780f0140e81e07130150b1840b0b184104030001030300c60075400d0041e14081034412900c02640328079180001d0039458003d03c90706a55166080e0f510b00025180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 101796205 1250 101794955 101794961
    0x20c15090307110915030a0302030405031018140c0a030308010503010605040504050607030203060109030b0a020c1506010504030f020a05040e0d030f0207020609040b1519180503060106050d0908040f050310 90
    0x2c0c40f040007440000e0140c030b070402045070070001c040f41c603c803440b00110000b4640300d0100401c50140e003010404000c0c6150500815201220b101003d110000118a0010003018052001440180704a010b1a404101082418025140540180700c03068890501a00e0080709201d030754882d6080c180c002c20780f403c01e8043e090040f03510400400d120340300d800064000e50802032810b41008081400040803e07c0b440b089030040501400050303403241c10a600c5420801d011801c2104070280006100c80c90340d001c1d08440490360401c0c4005101d005520000c3d2500304140d0080b50312500b4444c0b400302c100000301300c038000c490594400b00b0031903a88045110a078007441c00c0c040c2d8002d500780492441414150401140d03100c000b8007c0513810548500c0c994140c0201500701c4900c1b50382c00d1140ca2080c0c201400e249028072807620303d1016890080003966036101405220308015000c40c01d1078041c030581e00301c0e690440c1d20814450703d0729200c002d2082907402d03901c607040c07280c420702c1513003a40301d01c1500c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 101797455 1250 101796205 101796217
    0xa02041701091205070501090206030a090b070810170102040b071101121802061b0d0207060e03030906030408090a0f08010b040c08100b03061c06060e010b0f0901030c03020d020c150903 81
    0x120fa00084044045000e481c65000144150340075500c5400b02c400590b90130340118440e00406600007451415820b10481d409002440310702071001c00004d10800c40b02192109040b50391041d041c0b5640b480100c7c4440c00b9000d1540480f11000010130343e0803c1001c240c28a02d80c01c142a617501d40100800358507070080d00d80010810b403540c801c1c041d0100150503c1c02c0242041e205081e0407410313a81345140c0052400000001404c01a0001d0106020495124a0402528034210010f50505014600203501440003420060446000281100c03007625130010000084c5400700340b100e21103599440c2ea82c064942045002d225a1419161100042c050300005010b100d49861850103a801e000841100e035201030300311b5501c005c056484080c48103284400d041d900d40701324008650945031840410503a08180c000f120082c07400d0008100d1044800191050b10401b480d000c1099010090207400a1007034002405195000040d40c1c111441e0000d205404c00c083c1c000444269510b021083e5184e020320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 101798561 1106 101797455 101797463
    0xe04030306150e031905010e03030928030c02010e01031d1507020607120c0c0c0816050307050f13271118071101140a0204170109 57
    0x81c11010900c030016081040b003c80d0580c00217a15001c0d1012502c9248a08007840c60500c10250000a01c000c008402c0e00c1e070301e050000b030741600d856180f011500081120325500b1a0030520000085c0c04070341503074880c1311604080c0d00450b090260503403020704043d1200b12400c83c4000b0707581100300f1031008100074001c410010121070000c1100404520540d003003130082003441c0ea0040e803042da0b40000c0940018030480710260540742c0f5000c0d0140500502c0d80707224081a403010004583e9103d10100b80c040040740d0352941050b035214190700813650400c0700202c0c8080c043c00c3c0984a044041c0803954080f454201000b101d11030402079602c4000c142410300a0384081c80500070095204070000d8400c1d0402c180300c0d1900605101000c0d0001d4204000b103004090451003e40c066012114420001005400d01c605184e0180d080b9000342e900c0c0c42e90303c1d15040103241052040051032688 = true := by decide +kernel

theorem cover : BRFrame.Cov 101618705 101798561 := by
  have h0 := BRFrame.cov_init 101618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 101618705 ≤ n) (h2 : n < 101798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
