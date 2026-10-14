-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0597
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:39:21.299372+00:00
-- url     : https://prove2.me/submissions/88e4452c-e4fe-4a95-b282-96a739f8ea5a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 107194244 ≤ n < 107374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 107195494 1250 107194244 107194259
    0x2411010615050702060904090b01060e0f0d0201030e100c09140f100806010e0603100302190f03020d020d0501020a0e03010b030d02070b070804050d050c0a0611190311010606030f0b01030501 83
    0x11562181c004014010421800710343e00c140480d00315540c0100705001808990500100f080c50a00c55000410301d2001242258207095400600001c0014008000150300750015005800310384080c2642d801122500b0300c003102c0c28444d910701d1400744c1d900c0d00c010a007056640110001c3c45d9007614411491180c034072980d0703551112000e0085000703241c4103140e03450b10401643c18440340304007540d0220010007008008591b0b1840d0350200ca00880d1507100599000d110455180707150701031b00c9409280b002007400541410b417141d22450388050000500100c0300d40302c1d1802c903040881040b0000d0314601540f0818079090045042028044020303145901e503000010350356a41c28444d1514038280410a4014401a001500c2c000e040103441101c1c1d2440d940307012a202d40c0c20b004003611400c894900030071043c0c8100c1030741503403d005c2d400400e0621145501e4195840302580101c0400200c088000b08128080c0180320003000c182e2008100544224001d000365980968a070303040600d440c00420490 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 107196744 1250 107195494 107195519
    0xa080f0c2d06010f0b1c1b02010207020f090c0703050a050913050f01050405101e09020301060203030a15150806030106030c0b1c2007080c0105040c0810050603030f1324110106 77
    0x1003103842c2100c100c1c070f07040f43c2e10840901442c02180d0090610000e071f81102c2501034008054861007103400310582c07800c1400b080301c0f43c58181c1d541c911510042c0f1041000a000d140103009100c26400e20b141400140800034100780211920309103100d44400c1400301c1ca0000099503805081c0c1260140310501c0d000c3e8000690b9800d51050998400b510300d02c9030040c4200c001c1c050042c26256600307554035030f1112800ba54903801034441821441c0b401caa968800d80b11034403c1e00a4801845c1a040903102d5401c0c126840e000203440f030b40d0b15550f1400c00100003420500003200800c0c000f0a9591151500744400ca48114503000d01103019007060f81161044440d849589203a4004120140d10b8070500d0810a110380150703441540745601e0035041c03106012209581d40f0486494030708490555405a1305001a500240c4109406034018080d846109400c140500480115002c0c000c0c406135884002507a802031401c1c2c041c04a022912900c481d140c0e12110754580b0f20038000003804124076002041452 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 107197994 1250 107196744 107196757
    0x10b030d0509010c080903060411090a020901050a0807031401061e020304030b06091e0a020301092307050309030c0109080c010605180f0705040503010e0f0f0a080f0c2d06010f0b 78
    0x10000488003c000308405c00040d1001c04001400315116480e06140c0320f01c03071300c0f0444500ca01c01c10000c400203a8505181c0204d40c003a20303041c0e680908208aa4200751001c6030040d00e954181901d4540241a0700c502c0c000703050007400e19541302002c00c454081c0203100080e40c80884011504200000d01c041030f02d1155454018009a40d14480d640e61305031840f03180c4600d458164003244440c03081c0041e4004076009903050395006103081000d0100c0040c03501c00c0c183c0440f8800300082c09030000401190069001d154044a0103082e280b801c030307003c03800e18211001382100301d444070004110310031409004d11a110150205681050b01c81030200c40c1c845403c88001c0c807420a036089440000d082d5841071f01550001c000140c024000d0038030074a091620740b503a0324600542032003550b00080040c00300046005c0c030036810980d150300e000c14190380e041c1c0d00d9100d0613a02c04c40344180541107100d0384081d514807040c0502601c203000240404a01d072806c01c03606901490b00400d01d02000e020106020b41180e00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 107199244 1250 107197994 107197997
    0xd0807090f1a0703050705070f051005030906190b040f090b0f0f0406020f04030606062006060604090b040603050a140f0622140d03020403050f01020408030a1107031b0503010b030d050901 82
    0x1120f42103403034100c50600c00c4c400c00501a029007100061605090680c80d01901c0c0119901400200c2c2c2003000c9505020071030300d082d0079603c030324041400da0702a4000801d0510030703580049a01c050701404503040d04c00b0a404100f0444d651242c16083c4100b120086401042c00903040406041c085580050000064000b0344031690010f008900344651030308482c01994040401d006d0140c1d0742d40c0c0500040440c46804000e10320964480c03006800105250748602d2006080d2410301e8140010440140004014503402079500c603004408640c08204030803a1900c40d00c4801000c40407440c8407810080104021009984040107000c42d05100340000d24500d02000140d02c2020600d003009060b2044401850100317005280c4110300241d410380040003601d000708226050441e41244043c03c03442544500300311500141f021106080c4100d41a0819540f07440890340510707240d85030b244001a0003011401030840101c4c04002c07a09082c040c0000a031011005043c0c0221500b50244c00c42c411242480e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 107200494 1250 107199244 107199247
    0x60901051c0b091302040c090509070513080f0a0317040203151509010305100c0801030c150207090c021c020a20040f09140606060a02030414010e030d0807090f1a 71
    0x102003584540c8901d0410800030489801420130100c0844000b00c0c9020603070045040400c14189540590f401d141240d0000d0100d400d680c2d20004103d80580142d039064501810720400081c907030304200080000c0c0c003a40b030701401060410f850050b1803180190303140c07400300e00c1100402c0090b81d400300780305a240701d01d0200f000599843d0400032241c44421500f1035400b61088001109003c4001040b2888104035001000401100344041d0350b288024132000f8400c40842c41c00b03200400c20a00d031a00910320900445840303030380303500c0d08200391401c0c100d0481c01039011f2070450005600c02911000c04d250300d40080c00448850340c55900c154100c2000310f03001c681d04000006120f8032198803417000c6101c0034004110403030303103841c10300110408504900501c0c810000031070441e10303000045030210501070300154941443c104201400181112842e07040c8a50a90121030640f81032200400c3c9040f00e40c0c60400a140c40c1c035015040d100302d500703ca04c50316400c2d4410b21000c0f04a00e000204411050201c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 107201744 1250 107200494 107200537
    0x2070201050403051f1a0a1a040e040807050d030e030a0c24091b060c120201090206030c1c0605010c0609020a0f1205060106030c050301091d060c0d0b06090105 70
    0x1601c203445682d00041c901c0c8501c0e00c0f24032a483d4848a00c00080504171001e0141090510004034a20156462180e0120703800d0f50401501900580b000d1038201c43c02007060505aa6140c5482800400c071400d0b962044005003040400c0003d1091090314010713400d0030052406c00051240e664006d0045101c00c0c0300310300d01d11106004013141d40c800000800c8000721024240601c408016040061003250021400305d8810214402c00c0c00107000e8584550f2240f8160201c1c2c2c41e00c1485502c5c2c10103490555503640442c401584a2200461142c00f100811594803c840000500c1c1030b002c0b89001024545000070500160385e105030b012a070381c0e030404004500140c090001410402941e801840040c0302100c0005040c0c58182d01403280da40900c0c00e4501680c2c1e101e00a40170b4480741540ea03000114200300521140701942c0c440a041091110341904401c2c0103c03400340f4240e0103864945070401b0100340c40303980741a81d0150054400d07041c0c821a040c00000400a092230250841c50000c1d00001505e8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 107202994 1250 107201744 107201747
    0x2a09060103090533040305031b0708040e0708070e03060a1d07091d070302090109090302030712120b0109120311030c030d1e05040b040210020c0303031501020d08070503010902070201 80
    0x80002903410801383d0f42054007201c13040e0078000c1011001a40c20503103990681c1c0c000c01d4510030a124a4064459600e07664518020201884061064010041d028008400400d0b00c0300701400c0500b42c980203e400b242030507400a0f101c45d07001803800040100c0302107090440d8501042040e0040d0f00c0b18404a18428101508c28000b044c54200c0320440c41188070000c0c0744042900000b1a03011006282e0000c0b1044451003900c49c5c0940c00040d400c030b03680600401c03d540301e0782e000c6c000d918024410b490909505666034224135080c0c442d044000782c072218007140201a01d00c80e0003410740090900c85013040c60808030007603441d00040081c040c02052950544410014001c6920114801e42565620a008165080205045032180042081041c0b101302100c0491055a000c2c2d0f130405039840c401d6440e5400c0180604440b924041107000380014070340c0ca510208003460141074020107980b50384101c840020b140c8641401c09034100480070301402210f58002c401c40e41900c2c4008000f51b586c0c2500d000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 107204244 1250 107202994 107203001
    0x120302090621040204050f150d0807120e03010507020307050a11010201140108010204080c0f01020c04051b0c0f0c04050c0706050403090f0b030a050c0a051210050d080307022a09060103 81
    0x2051100c004502e6000c6200740d807018544564401c40701049151200b001d0f407076aa000489401e031082c142e5143c08901c501e050307071000c55224491508503190110300d6035509074002c21100703403502080095520040c145030a0082036404100b600c0254108840d5407140c6a03250004600600302900720040d0442c3c80e4401c1d00326071a88052041e07030062550791042414001c2d441445079400c94042c0391002c0d072141c601001031020b0150140d00030002300c0840b5082000502c07014004840405042c0c071708070340d4454040007800b00c0e2940c44000d040004801ca01c00703410304d00407200303241c441c500d0b0608002c48404004c0c1a00c0ba6141c00500004e45a551880d00313458009441d00008210380c4c0030382d00043e248903008011032007440703041c0c4144055100c00001382454000c001d070110204000348040080d40c40340c503514550042c4442c5810111a80e51004900c6181c8001d50a41c2c440e0800000c00c8000c41d0100240c10503d01e030000c2481d2502d05034402c41c141d00d0b8100322518841c3d0383d2035001c50507980c40b940 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 107205494 1250 107204244 107204257
    0x106061407060e0a0611070312140a020309070e1603060801020708030c0a14180f090412051e07050c18010e01060c0303090b011401090b040b040608090703080f030417071203020906 79
    0x31410014215006d818440d00c0d0000311007100050794243c0d03451105404d40c002c0035861600c5200d860300640301c440c00480650002090403196206299000030410050b00c00345008194190001386465405000201034030340540101040f60700402c640300004a203201229840302c551300c1d1f443c0d190b00d0940070840c1c00f031640322121fa411090201d2800001040d01c0c5e020302e83c02c0d00803159203050b6200c5038180b0403c01c500301c074050311400010145c501b800d40120014501d82e424058400740c96540012110039130f1704504001d0301c0c564407541021040d4105000382034050000408071981345d45c5030000d5241a001d050117144100081a903819041500070342000c030315141d111061061560f113400560b010704007110310142c0001ca4403400012140300c0c02d030403036090352000e0084038070740350030642c0613600c0b110040d005002c24820341c0400000710342960054500c5180640d02541d8030b0a041c2030184240d50307148041204220704200c003800161400001511440c2d040c00c01503213980c241000507000e400360300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 107206744 1250 107205494 107205503
    0x1d060a0507021804240902090415090c03080a090b0c0727140a0b0d0305070b04030903050f0312060604060e010e130e1507020f1b0607060e030c0106061407060e0a 71
    0x5000400c0b440c2d1200e466621160320100030544070700c117448003d5840c04a8060740064516022a01080c80020032030781c03020050101180c0c0310155a01c1c5014804140e00942c0c0090380850b0300c81282d540180c51703c008000d440c0341c0c1801c113074002c4080c03a01c4250b04d210343c101e440d08140c1c8589410288503982c0c0359046914400300514030501d440e06003a031008032100b00d0024940782c10a40b103450b0a42e00f810025403d5925241001401d641d00c25803624003610603014030940c440000000b91040040d07004007221480910340b03851a150307008411040103801a07105501c00d0206015159005a00001509091034030520a41c541d2000c26000010381c68030b021124100b101410400100140e41640051503030346107280750b5941c00c2c081b6124803060400d56000e4100e00240c00807a803554010400c2c05500a000c5490200305950f100c040f1421825a426545c1011504516181d03081c81060020091820142651103100c61415a14400d40e8001444240e40c4c1d01301c0d501800c0100045c140582c1d01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 107207994 1250 107206744 107206789
    0x403021204031214040f050616051218060f0711130e0c0306060d0c03021002010e01060303080708070c0305040501050f0909070903020a09060602070b0306031c0801061d060a050702 79
    0x283c0c00c080020031034142c5107602013141c044120254260000890b0103c0b2000307012811550b0070318040200650015079407000104118000f40080341003808401d98801c4000b4189640f035051401480300c0384003d404144c40350b4400c2c00b11032410300d0588210b0f040141e015118410200d841030000d07aa88094008000d0102c1c41c05000d00035050000412481009007102141d41c50354440003040100c2c05c0e01e09004109406081c030800040c10408826600c0110600001c9081c5078201d01c0c46085917003991080c2e001541030b0040c0900c0542212500f500b02c01c8514049104104d59100901244920b1107018100300001443c1c407440035074101615400e8000900c90049802d007040001c2c680c0010303020a134070843e2031203000110415a845031200302c42c0c00350043c002d0f4502c1e16246114a0300000e00e802e8060040d0910b040c0700d8640691449142a0152a894401c2d414488002e207100d60700250300c0c9070381411a0300e803590380d0350310416542c80614510f404c9955490610120b0380300301c0a807020060280c82c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 107209244 1250 107207994 107207999
    0x915060108070c0b0c030703180c0605070c0e0901091709180916230d0c050108071704030c030f0c23120c01090203011a0f0111030903030d050604050a05010e0f0403021204 75
    0x1005e00850181300c2d03e075024440c0060044c24102c403078520240007006151071102c2080301c80d0044c4003030541a8007440320003088594030001c0e072030700349002c90729445140d42d10969082000441c100a40507c411580381d582400500380101344041c1c0da1803000004444c4550016213076200070003111440b5005c00448921031039031a940c80074168120000c0c0d070b6a14a03000000b010905200c440040200c1d0403181091049140c10015241c2502c0030b0108410000781d100108842044c0c40c40d400c0c041c5209954411720500b01c0e0600030601c6501034183e5080141c20401c0902064184c80c010440007459007452000d00b2281c0d9000385003030782c0103596407415200400c116015981c194408a07050340242c2c020302c020105404004600301411030340b2076101d41320741411066544a5a4510070052a000480340340031288400039280d90031000b100035000e80c0f640f04100060509004064204400000522640d4100302c0001c010742c031b0040c08001c0b01ca206600160a0510030042201580600d00042e65510b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 107210494 1250 107209244 107209261
    0x3070b0901050106020313030308100312050309010c0302030c0f1b0703030914090f0711010b04060f030c05030606060f0d0f090f061b08150406030804090e060915060108070c0b 77
    0x204494151055291a000144090020085031a001100d032003c00c40d95046990546081c400138015400390202038802000061091042004000e0a0340b1b40c070703440f441d1441c922130035251004949000c060040c418040300c0e0742007900340c84005410f810641c1c1c850f6003810304880001064100e44e17055118046000060540008142040d284e0003601410f040c140c9405010040400b07031030211405200e0f20002e44914840c292058419804000100b0240d40c500001011344040c0c1d00b1110503481e070443c00b0000c000a000c0c4a400070801600035020394030700000042c803207000f40208074006190004484e00c0c000e601340e104148503140d10714100100d0b1418200030f508051440303030071103260703141061080d070605000f5420310003100560785181403652034407069010903031201c031010340103034403150003000054a1602030b10281c0240c1d05d00061071150542151300e403400241503a03605420010f05030403c0d04101041e260702c0300080c00c140c10140c440b070b101100d003280708520151200c45803406108100f07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 107211744 1250 107210494 107210513
    0x21c0212040b12010801090c0509090f0703060506120a0b040609020109030524090c030705010e0411030108030306040c050a0206010b03130f0f0c0f080a0605100e07050415080411120705030307 84
    0x1010070242485241c5c4c03105061400c03200d900c080a402249244810844c07440e00c0d2010580c00300b140026541c503c2c9000800d146040203540049825607141c90820000b81403808622560010790030003800c048110351105000200f01400103802c003622030a1401c00d5900a17026500156404001c690801d000b15080f82c41110038142d0000080305881c01058240e94001084114140700401402c101454180191f40038150550202d80054403070701c00b01588184400030318000c04110020b142d8034a406001c110440700800c034403405100702400480007865001680e10305450705464200d6807a15051070040403280c814000410007c4504005c1e020080f8081c00c4a15852050040100c1581c48141104c00041280a482c803240d0042101802042260b0022904401900c5003a44155141c50016008110031607150001c280000380802030005419204070314420145000d0500381000c0c0c4d00d4070049402490024031070411040e904407540f4080c800c810041000508490742e0301410302e88a00e48 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 107212994 1250 107211744 107211757
    0x20307050d0302030903030a0504210c02030c0102010207210315031a0609090a0b0c0c060424050606040302040209041b1101060504050702030a0f0201150f170d021c0212040b 76
    0x214021818000070490190013075901601c2044061030855491100d07400040400610645440006804052120794445805170704120603944d80d004a200c45e006040c038145200302150304680c4104515004105000e08607200e11124188003240c40c4400d0000b01e02416072040540584010b61000004004054001218078003102400c816070396110313020850880401c0b520189076403c1511260000380030040d05aa00801c0044190305110317005100500d09001242d00301c2d06d00706050304a03544460034009031846a14024421f010310319006021032502c1c015444000e004a80100e0300141903a642d40000904408103a04020040c0b038020004140703503443c4107036048951034040040382c1e904081c011148119001e400440c03030100c0e00342041301c1d101000c24810b802c6560b5860000d001060b24054407006110406c115521542440108265038410b41086a840d511984100100341d0300402e001b261074080396a00100d0f89440c000036418008544612011400d0001d00881c04400510217440c0d03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 107214244 1250 107212994 107213003
    0xa09020909060a03151508120408060907080703020f010210050903032703040b03060a08100b130509071802130b0d0612080d051005030a110411120a0f020405060406020307 75
    0x40703480782e209010102100b400042d1800031011000a1415402d070086000e8900143c0401c403c0d07551400e2850a002c1d0b00c10954404550000e420081002d003000100d420074043c00141c035003d484c0c00c1110750f648546200090080711410507043d1160300034098038500c9132010380280043d26000c0703990b5840b50701c111042d03a41484146007000c1806984100003542410810003549014100a90030045800040c80540c0c13240507c200801e0080c814000000d81c0c502402c80070503031401960070040c00ca94102d01d1209038900e00b03000c01807001000150304007107070000d404004d8440702d01450307a006842607000a12104d40349001c0040d480d441c4000030701540145510420000f5102c404100400390481e101521484c4240000040c06490764080c0303810203207845280301c0066541020a04011048105980811410030040050706060040740305011840c01c1e0f507403400016500004045c10b000c0e0020042998903942182d02108590440b0080e1030000c140a4540b035075a60300a58940c8010000ca4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 107215494 1250 107214244 107214259
    0xf050d0c020c100c0b0a0e0a120c060612020d030e13060609050a06020f060c091c060902090f0c0f071704080607030608070506040308090102010906060902090a080a03021c0903020a090209 82
    0x800b944c450203603209090f80c000b2480403580c4981c0c260710080c3c070290b403c203040c5000384007400c0c0000b0300010030100b4080958440a5484c2140c0c1440710449001e58401048880342c0d460701030059581c2510a40e01c140d26081c1640082e080c1c00c0414801c016562a200301c50b45010008148a03070491300c088102c4208a071141c42140c0c0f142000c0f41c0300c9a0481e40b8040c1340d4804030110746020307c01030240c500c00c04040d0071a981c8840104e040303802406510f4040d00d40c196140e814400b54101845450703441820003012040d241450b5014002034030814500d81c0d600000410307a00104115200d8180c1c20500d00d8000e00d803515101c80500f512100140c1d51900401e1612100160800380400c2220803900004c3c13096080c40d00d16100c42849078801c5a642c1d04655803011150000f400c03600c5030710302608002000586680b000030034812085015041113a880d80091004c60009500041402c81e00c1c800040000c1d1400c4020015030349590b85070002540962042004580c5000c140e014040751003080343e001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 107216744 1250 107215494 107215519
    0x1306050c12061e010c080d2909010b040504090503090907030c180503070303050f0c0115090b0f060d0b060415020d090e10031b0b040e09150c0a0f050d0c020c 69
    0x1070754200090b0709800300644040c43ea050358060400401d44c42e004103000d0389026040c540c10401c581000509101e0585500300380102089070306410108600252014411541882910f0200c0e010703038414184203e480d443c2c5482084001e000740d070f000103000707004036105041904014000c2c040b00c441403000112031000c0c0c000300c1c00001c802e1800321040074000d0500f403030458034111065400199000b812040402114043c60801d01c1041040d481500c4206e0f0340078105901e40d002d4504c100d1901744109107012040542d5034a040892311079522560000681c81d2400000c03034514011a0302c10034101d4601e00103988802e03004030f0707010f1020b030090b03030b445a030a500e5031104540701380142c612200000706100705100181d03881d4078150b002008030004030802c540c2c0304c250451a070b10942200e540907148030148900d20100308039030301c0f040d02c28102c10050791034030342100c0e6124040c410400040000e40ea007201042c81c0900110303210801c11601c180094030240101035036481050b80002c0c0500803c0d42403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 107217994 1250 107216744 107216749
    0x20108060d080f0a2007030605150616020d0807060501150311091018120b0109021e090f1315050306070905150904022106030c0904020103051306050c1206 68
    0x7462409501000c8903080081d400d03420150358202c01290300501400c200d00f011030305401c200d655030f030703040d034400800c255800d41c0790200c1079440c081c2401d62441e011080c02c0989507603100c10b951101c1110202c0303800c40741c19800020b1442c402003901604002000820005004071608180c1c1610100907081504501045044013101c2c3c3c000001042d03410140984406407603c00d0425500d41a903140503003854114501c1031000b90490f912410364000a061844100701d0243e83da0760040030245411400e10501c1c041144074000c80c8401040c2802d000584c44104d49c0e96201c98901380d881c040c0c4909110300b042c50349200201f60485030300030100010b80380001c43d80f8000811510558041c1d8074103480c0c92401d030a10403c0c00325000446150103003480790a038551564400341c00b85000c500c03040c0b01b5810048280d040c110f0340150481e80690044200004c503501c86100e0150000e60a1800150942da40039051094402c140c80c004c046504210600c031038903038220040c2681600c10b1111084507140c4508 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 107219244 1250 107217994 107218009
    0x60301050109061d03060106020a0317010f1502100203040f031e09120303020c0d09051503090a0b06010513140102150f01030602030402030a1208040b07210c05070609060902010806 79
    0x361a001542c02801809a644a2100500e40b2050801c118007100564000282004000d0708000010707441005070609050b0b0003038607007421040c030b12440c40055041070300702660a101ca0040749070244118003c0c04560788200720120181030701990031916810301c0d00d00308150840071042038001426180d080c8103140144007140210072503980340c11483c503141030040780c00204084025400e042e82807150596911061125592015403682d59001450504040168241031901c4020300b401d03003030081010b41a0006480225941c009011000e151380d000012a1079102d42800400125408440029242c203030601801c0c5680e0241c0030788010540445035000e5880c02102e02c2c0c254208814010030104a29500642e0031600150603105004115103901d200d480c030000c2004000b0700144100824403600009141e0003200300d1910140b1400010b80030300605812000f001401d940c0d5540d0548811701490807140010b40c0700340c0c244004c5005003080310041c40d1541d020790119010700c000400078a17161a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 107220494 1250 107219244 107219249
    0x2010801090c0e040e030c060f061014030408070c0b1b07060e030312040c0b030c0405030706030509061807050409061b0f02030a03050c0f0c010b01030e01180b1b0307080a0b060301 79
    0x81d950034043e00c54070200000360108081e841901c0c001000a01200d00050005038890540c0300307181d006c0c50405609010b0b40600310402803003045400c2c40c00305141e881c02800c490304543c1003039250381c640303405080c2600c000301c10341c0c0255400ca00014a00802540300200445080340f914151844c5903541d110589821103020f4145506802c1042264180c06040721560341040c050a44405c0540d1105161b440c3e690056900c00304c444000b0074108038903d010813540026201500d42800541030200e0304079078902000e07008424006c041102c0b0904403900300310910042000038001e019090540c1800c90082070440400c42c08603448503144403070f6074040c0c0d0086085217103d074000c600e41194040200c004000182483e4a802d1041001d1a440800d080c0034100042d200381c0000b45801c2c5a100240c1103072442542ca5440d41d0501c40021890b0500074130303980c0d03000c2d00422140c01560311900850021800b20710707455054040030080c020031750b44c82405248a400c1030b900800840e01c02c4402c00403180802d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 107221744 1250 107220494 107220497
    0x6030c0a030303020d060e0718090c080a0905010902090c04080106051002060106080a0204080a03030c120603080315040f0c02061602030c07180e07030809010e04020f1e07050105070c02010801090c 86
    0x36001c000180c4207900512410780708060018045417030f40c2080c07450b41001c0da2a100040c1c2a481031981c82c51a6090340d0b40201075201003000208803447d80549281c60043c03524408136641c14454050103c20b40005104a600500d2000e481c584440500115081401410f10075031038843d01042a00705244a0040342c0c042c0d40080c941c1d0380c6001c45c11500f0841c002c084002e0385400348000100702c10100035100f202c91198a02069180030058000c1c5220716001d0682c0c0c60310305011041000c543d08008494011009011041044110002050282c0a10f201c02ca440b9407402200410309540860314070300615100e0441d41d564500300c0c004070307a240100fa0660280e5003054400300205104803500740c8901d50841004655407006442d1070b4100310013903100b80c80070315001a05550940c0e008031003407039032101110210f00b08680354000b04124024031100843c807a20b400440e62100d01d40c10f0944421a9002c03009026524091000406181c11058102d010403a0703040040790681c454014598004280e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 107222994 1250 107221744 107221759
    0x80c031203100810060312081003031101021b07030209091513170a08060103150e0406050402221a1804030e061312170301150309080904060806090606030c 68
    0x3003035001415035002038880195a0b019940010303102106100000701a040e103940000c840d0f245003040901c3c00c0d012500c40041242c0c800c00c002c000404604194240c903014900903058512100001c0c0c020300c940c3c120b40c0e8200c2402c1c04444040c01d40094404180c92007030b0b5401c0b01c1522000c600c8ca9030342d8482504500d51400034000250380c124203038003148440380104049065641000c0901c1c039554841512240054110401c100d401d58041c05a000d24042140e441c0e14000c0c50b2014205903004041c00041c0041e07150400300c5d00317540d03800c0650161010800c10300c410050962003488001c00015444201d03000f504040326013149000400c0d0390300001e02140d0588036950300c0c3d40c100c40108800809503170069045c00820108030303010281d00e001d0684800561003050890a00481800e041a5050b1212004000504c5204240c4d00c180c0844c1089040114002e000c07880d24000c130703014900c0e010782c00c14074000d80051a9100040c000d40500d03029400e9641a807103078800d25454000100301150030054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 107224244 1250 107222994 107223013
    0x30c010b0306010b190201092a2c090102040906080607030501090504080301030f0311030d06030b060306100e09010207020603040b0402190b0a0f0302040e180d1715010224010f080c03 80
    0x1c8180c10345c08603000d803000240a543c2c03681d807a82d0401d85030041d10256050714108a804840c00c84102d0003402204030b0719050840c20381d4504500a1101d80d4030100201040c0114548542c2501594003401c0c4016061040f5522601c2e034a40d42d000444280c0300080c04c150000030280303000c0c844c1c2030080b40c01c203109500d540c0c00d41d141c0300310505010a0407401c1100864a11260b0f0301c0c18409051103546a46021495074a0344c108580c0048002d8000e5100c1d402c00c4003401303c0c241044035648100c50400c1050f49255884056850081c0070f032020185d0404000800c000c1001a0442507a00c07071442103a10a140c110300048031200300045000348921008100865260180640c9510310a20b16916005d4905901c1d141003180c1c2c0c3c0710503550462241000080303109007000c00c2c040001c031528a4901050f403504010503c0940c100c0203450915801c1550342c207680d01e41d200380680c20140780300c481003d900d51000d50803104050803d100300340600f6520324010400ca400400e03131741c03140d500040c020036001c01e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 107225494 1250 107224244 107224267
    0x22413030305041e0c05040e010b1809030c06010303050a09060201150b0d0e160e130506060f040f0507021c090509060f0f030609100f0504020619140705030c010b0306010b 75
    0x1501400c140e4a40113100301c0e0110941801c14102403079845170441c0741c0b0345c914000902c07081e03030641c003507141060341084040c058646400c20f0503203890701480c0c50500c0c681c403401c10702800e51284808900042c003441d000070040c160484c00401d1520f40c41e036030344000e081c0c0c0d4560407401c0f1060f500480b40b0300c5409001c2042a00b0000d0081c1c40c0410440c100000c2c5104064911460540000120400440444020440110600d0304543d000c01410741800283c03400380d49040d159200181584c0c8510b8020b10003003c03540740ca90089500050418082006040c42c001c082c0d03441005800d2014101d00014009028504c6588071508449010b4010503054541c07008002c0c000340b2125101d41c0102c1c00584511682d9020040345004001d0280506aa00e5050315041e00b520f0000000000b0740381403030240300068807010111603080d069580404070440da000d100f150ba0391080695107041281c00b040d82000d002005c0020700d0180d550100030006003e0141c10316803200d0091007a29101d101c180100500103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 107226744 1250 107225494 107225501
    0x9050a080604260406020a050111090306010b0a02030f0a080f0603030c121b030304082107080103060e0f0105011701060e060d08070302010e0a11030c03010e0d0e19060224130303 78
    0xc1040c80f1400c0c14000c050241007402d8000340d00ca140143e10060034001404000e2107007600c143c08411a062030900c0388030101e43e0f503a07411700c01d00c0687ea100091a0031242e100740103484070054000c407103942e107100000313004241c0001a19880400711501c00410300f5494000101c841043c0343c0b5014155029490344a003d50303405c10030500440d08400300088007107100910055108900c24005d00d5260030038070321401503040134480460000e80c444810710003080d070421011411a03500800110f255013003284c185003410300003c01420f40d5070030000041150076600130b8500a858034800200507050303444110025911080d1841500f201d1140e00001c0400c004400401c0828000d000201743c41100d1260729140810080c0141c800c8100c001d82032010f1b203400c1c01444441c4c54100c00a21400c5c2000302480e03241d8400d00d000380306100c501000941551036175800080036100d4503640080c0250380b00b00103500d90540500400041025142c0c10301105801000907000360098681205401c51030394094009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 107227994 1250 107226744 107226773
    0x403020d1106060d0c0e0406020301060210060e131a0c0301210f03050a02032104020111061512070306020d09030201050708010b03011e0506071b050402040509061e030604050304030309050a080604 86
    0x40307107480c5c0804149450f82181e400d000764030030364005070360b50b1400d1002800c19072503180e10440ca50800004208100400c0040c581002c0422140300b40d000e581e1801c541035201412a01100e040c4040400000070186405541280c4a0941502031711010107043ca40400701440000c00b41c6112480b0280403034403503c06842e040b03440d030040728900641c10f1400380012807103520b00074110b05040300708811540d0002140c1485990b070300041071700e41004081c4c20103000690b84014041d03468110b00ca510010100000300095801203400c41d90740c1d0780c03141d044000e0100c140c5c068001d5070034040480d5109100d498003a040720b04103a18141075909042e020540c210405215009054402d9800b04495803050300400b480c40c410312078005426004c00d40400d10340a294402881188188820040341d10b070350650340e5001c0011900d0000b00f040c0002c01e02d00041003480300380e82503c90034003003000301701e400070041050341d000c5e481c3d518503d07983d901004161004d034059030520340c0012020800103018651400030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 107229244 1250 107227994 107228003
    0x1030b032406010c05280c0e150414060d0c0b070f0c050d080406030203060406030605090c0a0915060e03150106051e03130209181c031a030d05070507090f02030403020d1106060d 78
    0x120381c84035250313082e01f0f10040c2c0000c1034140f00281440008005100c9036820302d0741c1540c0c144400040c0112107062224000d08043c011001c4107044010803c800107440301500c6402011070b00c032501410040e080b14007462044820800b000b00100f8140750010001c0b02099001c0072080c039150030701004502035003001e82810742042d190100400011403070f0042c42c0c4180707581002003070003044140400040d102242e11402e0f00300c0c5001c1c0c10640c2e4484ae00c1601c0b081d40c88170b040a004550a9202091500e41010040b200390036107880041015a030040050807031282c4910f4038000f804072240002d10503c01a0f5084400c00d0305140c0100060130f101302a9a8040700c2d8031411084503002c402c415042420445e401080c48000480880800d90107201da000e01c2c03d030801c040000d00501030b0100f66240382404002042c4100031505204000f410050100540694001848884228000c1030041d4000780c1c5c08502500a0100c4500b00c14824150303402e12142c0d0000501c25030322000280801d60f11003010945 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 107230494 1250 107229244 107229313
    0x11100911100e030709020d0f06050a1401020307150504050d0e090406050402061309020a110a0c030f1401020703030b01092909011710080106082a01030b032406010c05 73
    0x1c507641c061050030005c04840402680c0d80344408118801c44140044d03503106645055014416510b80c2c4042809807092020003000130400100181d141d4020464014a06402c2e8004160f03405150340045005900c03074400c641a20094102c243c0750203074041c45542c0c1040c2e034030700000c0c0400ca042d0400ea4100d80040c096604d005405c000c10008442c041e080000c00c141c000510320b0382c0c1548602e03c10307560b414201c06400c3ca10125910800041d899100191144544811010038080401242200d076002c041c000c564802461178064050070f181e40c00680401c3c3c11820024180448007450014032202140801c5c840c03405191405840e0030504048e410000f18410300d09014941c1c20f01180180c0510078094603907882c01000d5429500700f41c0107800786400003810075007007045d00801d200702c01e0302d14401000780c4020180101c00800008020319458855141036000140000c848101100343c1000c41c45681c0d42d0311401034030020b0300c08400402ca980070074034111056003840c00d206071082d24a00c545 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 107231744 1250 107230494 107230517
    0x8130515040201030f05090105150307030201020307061d0f071a03010509130503040503071e050a05060d020703030b0a030b0403031a010507020d0507030204020c060a05070309110d030207080d1110091110 89
    0x464408580b8813047e60f66850a010b0941103541003401802011801480c902e0f0650340000e449000b00d0350000d0600d900c81c1c203000c1c25200a85072402c000f0300c2000c200c68080200b0000d80e556204144613a014030190300d90131060410040c800c0b00c0c1682c3c0c020b03095000e641c45a200750384600007154002c2da21030000344001300e0150740900c1140c0c02001e517000354040891105840c880d018803242c0c0824418048404104916111101034507000b4442c03000041e00d80429050550140c00340c0e070009540312495040201c20400c40d07010850081e40a40d80411881c1c1c800350002c1c1c2c01d61403540c6002e010a1040c000d040051500003030300d45800380f10304181e465290307480e80130074140d030000c03000303101c0c0e503000307002006040c05040c400c2503405250340c030f42441601c4003501da080a8a02e00c0d11211b024050040484080c58020480c0d20010100b010440d103c00c0c0da40300b0000c0911103604040e049030700a00d0126120b92005001c1c00180b15007021001070b6825a80c0c04001d01000e001c80f40c5020b001c04c42126 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 107232994 1250 107231744 107231771
    0x2060705120a03020405011b03091a0408060103060c02010507030b060301091e06090902130207080702090c071505010503070806041703060d06020c0303010311011b02040527010605010813051504020103 88
    0xb4100d40e5030b840c0c90150301d030350821001401d031501c416500700c440c1c0d001c4c001a002091b800700360f0a04684e1940c03500801521000401d10705c0d44684d0b0040a5940f1401000000700302c419071215420003030f80d6008100c0c50f1240c2a08405441c03601d44c54990010081c40140521142c6074040426800000d600d0021400891b400c0400d8450303690002110340d41d0f5104600a42c24090814001c03803035208411490700318181e5686025000301c1001a0041c42d01703e0000e010030704030707200311050560404103c84049402e0420300002d481d090043d140a401090700018401c03800003065800b6540c040001c5250041041c02c3c1e0885401c01840075500c401826010004038006100a200380074a031005150307250b0541c205150890b042000440c100320000314581c40d4414410860043c140c0d0403900401c1e1611411320401410000a40c610494004510703c1a81503005601c180200d400a0300d0300010340c0d442c00c00c049800a80c258000e4160382200404816445542c4030041d48a4414100010b00300c070300107007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 107234244 1250 107232994 107232997
    0xa0f020702030a14070e0c0406050a0c2a0902120c07021801090f050f06010e040c05090612041e0309090b01020304271b1d04090b09031804180206070512 67
    0x405440c00480b01858138a0503100340200005807030001c4c1400c46608050034141401d10480c4036030002c0180c08503145084034891180a010190010010748050200c80601c1d080d0041c02c0720400c1e0724050031030380011011818000c0c0c0344801070b500c0c82510940d95111805003581d014510490b4000080c560440b00c20280d410340368064140b54a0002d80405030420390811208082c0017070b0010300000c42080036580e80030300788001b8080203907804a5000744110040c2c826000d012501a400b420101d00b8081e804050801140b26600a020307201880410740c002454559411002400240158906015551464006404090703061045901d0a035130740c00c010501001c801540c803101b2542c03004000010599020341c460a030510101c420b41c0d9028100040d001000c0e02600903140340e000c0c0000042c0d030f07541d940448200d0b03401c642141d500d481c1c090341554481d4071101c041110f51414001a1406082c075104011103801070040320300508100d90200441600034840880c0c0300d00c510a0030401401b001d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 107235494 1250 107234244 107234263
    0x80a030215130f02061803030c0102070614040206040b1602030102070602030711060105010f030c090302100503061008011d0402030313081b12190201020313151d01080a0f02070203 79
    0x240644440025201c1218401e0409016958000c0c00100344001140414034102402541100d10f1595002e03882d032103100120300340c00d089506000114500082e644190028050280b140c0020422000440b000102c2600241c4010350491030612060120b6234088005060703400196200d1040071070941e001a00b0380c5d011800460b80590044148034003079400800902d007402c8848090b1806605210000341148007130a1042e04150300c0f444840340a078041c4180c540555006001003042609050001c1e1103035005031040380c041d00d11903414200389407080f90000d040c0e8411441640c480c0040c41100d0400050282003070703905000400a0307154250b16a8002e500405640f405000542c1c8070304091220100007140c800c1c018403a44010184051011402072041d02e8243c90300d20004100d800100d11794060128900c20b800c401c0030010a0b2070000d501c0c54005803116944543c1014400710b0b040d0080e0700b8100455006c02c01c60300c0800c03400c5503140c00c00c0140440507200181080303034030f4002030714041105 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 107236744 1250 107235494 107235497
    0x50607050a0c1404060902070f0201030b0d15020406140a0906081509090f0d020a050309190b030c0316030b0f01030c050d150509090d0f0e040617060907060306051e0a080a03 76
    0x81c854541c0d981441c0c081c0f0710082c601b1100c11030800b419929840d03a01c10030b480000f41059641c1010712403d603100da96075003086810003080001411040045402940315026040c0820346800942c1305c011201d500301c0d0b0b00c2420907503400400c1c2d881c1031402d40d01400017400d03140c48442141c0c401d840940301c60010500c00c02d040c9009240f03020302c407041c0c2030400035802c400310110341180c6000400304500000700c86940300c081d1203104490075070114001e880b41c9036410a81003c1400018070100780c5022025500804070004004022020540158203d8901c10034142c2c00030315000041140758000e602c1605220b80b2810064500040911400119450154007104030f1003845024400d605040c04200d6100c2010001412900d041a501814041c440e414000400c9807002c40f1030160b8a030354111400805030000f90b00c441000a610583d1500320072075000a040c420702e207002541300d1290003010100e0700050001210a003003d041e03611841104000c140c0c00c84404040081d8081c3e0400889503594040e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 107237994 1250 107236744 107236769
    0x903060c021e10050c09012304090203070c0c061b03120605120d120513080c0109021309030206090a080d0b030c030703061401150e1002010b1809071707050607050a0c 73
    0x101c10100880344e026141001050003844141c4150342c206500f106101c080d2801d85814007000c1204030594442c0341c06c010211400881400b5980c0d8000c247e0000301c42c828001c07400407544cd59800c84000c1c003001070802100204131942e0002c02c1c011034640341c565044140100e026605c900218224103140d000b12035082d804010b45c0524158890b507450003215010070107108034101140da0343c00032444800e0140040c400026101c0d1445802d40c4101c42d52031303014014580940c1c1400640e402041860410740150180c2400a80b5010b07011a2580c0100c0e840000203003050340007520b00d4002c10010140e03a40510405207602d010380c1d001c0080700c0040d40710b410003241d1080c02c0351420140710011ba000c0e4140002188403200410b4000320750260300f41e425100f20611001d0a0000c0b0f01412038100b8854104c0140c000200200a4071482a489604290101c404050303840a4a9002123000103a0039502d400141c824002403a10034010030946014070100c400103842521140412030782940000300c0c0c00d26 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 107239244 1250 107237994 107238013
    0x20123040f0b03060a06030507092706080115031e080f0c0c0a030302030304060c05121311010903020f09100308040608060411041d0910240503060105010903060c021e 73
    0x1801e55441c0098503028012508500303001c0085180380d140f41c0144030038991030380002011035104d4810500144030345100100480205082013000e008030400300002142001c0001c05c040405020312100c03030060640807640580b9544503640f480021410101c0c00c14450034019000c600700601414006041d40d4078656110585da16075460020500b494034000c0c0711040040010a40100035130740c0c0030341c00040c003003589615018101c0d801d1095016590310030f1149414001001004200c441d1000d00c249000c2d01e14541110054514860510000398081c4107a82e01c02d0302810a950000d401c511000c03406802c003622513940024640080d0007030800512514108160b40c17400c0d010305441c404e000e980480c545030600b070740340b407072200490364100000720940b0100b0a50f5408000f1070517030a251400400800882c9010442842c03031070303c1446414140e0b0381c80800c003480c012070200c0c12510143c45044107180f40d0b40e904c101805281e840e204c1580a061322810310700050f0203100042d00700c9840a41110700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 107240494 1250 107239244 107239259
    0x110a0203040e0115020a1e0c0303030e01050a0501050607230f0a03080115080a02030403170702070e090d0207031407030b04080c010c03060f1a0403050d08010503060a0507051602012304 81
    0x10b059000000120600400203141500455014141508a41010901340d12415403240511381c503c2c00074a001d41000c0004141649a030200c000c0045800c024007590300c41c030301c0400c00c2e11820300869900c41002c0101000150403a1a2402c002005e0310440111805407074a150815051844000141c0c21a01b081810541c0c4a00c54902500c60b580e039100461100090040446c180148403107000f6600101142c24980210301f0b001e80c0103440700554185140030300c0029299401403107101805107401020464510002c43c032018004500c1d0700810825240d51103034008001c0340c400c0410a805050008404a451680f840d44901c0c0100419603542085610f01400c4a488051306020036180000901900f56901241000c0380c880c41c060060204290f0322a95051207258002070562103007034030751510b0035044014281220380032000e60b81706c2d1341c072020300800341c03030084948900040741008070180d9000040e41c4210307180d00616100f1700300c81c0058046a61109410700c5080e030004d02090820008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 107241744 1250 107240494 107240519
    0x20c0402030a0203010f170706030902010509090901061701020421021201020c01020301030308060d02030c0613080106140a08150a02070f05030a1d1c06050a0e060106030b01020114040206090405040204110a020304 93
    0x1081c0c0c87d81900c9448100c0907040d03031600014001d00b420951151551010b5a00c80c000ba10718410000b4001c0007d4104410418002c051600c44c640c00001c2841c08100c0701001031082c0c3c2d08490f651104041d200d102445440c0ca004002a01268001814009440078031024400b41103900c0e210350005a0ba5415810301401d87d080c010034591084584519050060b100816102d00c1d00c0d00039250b09880e10344100a0480700016500154034540c40e28400140c01c11500001070185001680d14409c0301d500c904455172560180002c420b0803801070310126030843c440c2d50042114034003900c901d05403c1c0e4030b42e55807403c681c8001c0da0140040c6055504280708a14840074500c0074608984601030000004115a4440c0f10107030702621140d07490000504841c41c6030010003200c142c020030340c0c1d00b5685807000a0000c0c100f08907030500662070301d01c016090040000c0701038061500145007a08001ca010100005450000c008030b80054a8a040f420701b1240ca0b030140c490400d0740c1c0c010719125802d0050340c0090 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 107242994 1250 107241744 107241749
    0xb0109030819021b030d030c031803090f05090f01060806031203040302030a080a0b0a03020919061502060c09010813020a150504050f03010c08070c11030a0f03021009081603020c0402030a0203010f 86
    0x501c0700081d024103ca0b41c00203900d80c40c00071b090a0104040d02c0c1d04a060300100b200c50300e580c1020023600104002c00d580010441c0643d80c2401e07085440380e8881c0c040c020700c0f1004440b410960701030b080041c0921030003004401d61045009013101c0240071050300350320300c5801c10b48084015074404900280e00c42c0e04040d000d94403010103a000c00510f91202c0020b11700d81d0f0a84030281c002c06ca09001310b420721030001000d03014005d00d598240a840e50f81c5054861139010042c1c0080180a5040401c2c070000103a02210381d81c4405940d644030544540d25105c001910345001241d10040c24200040d04504140304103d403103006407100c540b41d038a01030a00503003404005045200b645070015110295400c03070107181c0c20616900d400200c0c12024903059043d008401c00b016454462101c1d602d042000006651084501c030764203039403110010310380b07070400d40b000d1000041418009101198402e502e200300f07188640c1c080d00c101c0d60a40360b0000854200d134029a0300585082e00040144a42805881800700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 107244244 1250 107242994 107243023
    0x18101a030c130902060903010e070e0709080a151b0e030c090f180f1005150301090507050402181306030203060c040308091507080a0206090d020a0309090b010903081902 74
    0x2241101e090000b62507103180040d00e0b4101c0d030350b000d08009544900c016182050300280003000700788a5200c04030741d102e589114203038000900c407000448140c030406220044503c00c0b0002c10514865039035a000a00041c00c5d0074511035039651107664240380c1c251440110b6909038841450001c020300c241401c121410440380c0c01100e40c03505001c25001140c0005078001c606400c040308144103000c4050401c821040300900794415900300c04608403d66110b80e00542c41e00c1041d0b1000c0202400b854240e610019000c0c0a51704000720802040c2855002801e0b41c015185100112285081c0000c07840e0f0f2501d4912031100d582d810b400d00450404106407600f00140744521420303e4950f9550700c520744503440b2040d0044500d00310503001a880d50041c0da806a030300600c0c1544911280c50f00a58426040302c00b11298803074000100d0000b4000700d03110341c0958040d51507100d030798203206d1400080c1c0303048042e07141000104800007010482c61305c05400c50003100d00c80170629140341c14000b454140103011456 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 107245494 1250 107244244 107244253
    0x1501020f150609040c030f0c05040609141321080f070203030c040909020d0b040614011a0a05090312071505090111040e06030a080414150702030307020918101a03 71
    0xc00040c54200c500d40c0100708960020f142d13540c61800071061051640020039040000d0034035420084124025425038206807420082c10355a0030030607044d1601c1200360303009250720740c020400c208111203040c2040c0f80298441d0580e0310804031400c20400200c02507400051001c0d042c0002a5001c1c0c00c400d42180c9548011402c50428403005c1020384100c2c40383e05041030b030b07940900085480f0180c0030400036801610185103440c090170000301a0070500b011412580c401400481c1224a80d8000380d9151401441c040c1070540c05401640c0691000e8225071303152081000361941d50f0503020003013020901c20116031040c80703440c40384d107015194043c2c14405564103140c2200681c20544054401b2610384c440c401d981d40d202c0d40c000c01e050042900740906283d1002601288a04004400042d10310040d98803514001c1c2030b1034211064060440003e5240c2c1080040c68050f240c00c0745500e4200300c4058070816941080c000840c030300060400090030150f22918a04c0b840e85136404200405181a4040c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 107246744 1250 107245494 107245513
    0xd0624080610020601062105070509030c04050106020705041109040f0b180708190e061f0902030f010b0306120a0b1008060609010312140c010605040b0607110d03030908031501020f 79
    0x84d4455005000348000c1000703004a4001c0000004032905c200c180c0780b01c0030481c1d8109180014040c4d070191040c613010303214061012041d414a4403aa5048428030350261107800c0c00d000800001d80545040e1400c0c0c260244000050380c0d441d8450220311a0b08901c0000d185c0c0382c18800d0040014020400c0c00000b4600d100b00080340c2d03008269158030040d8802d0b403421542d00080c0050041281c07000d003040a101d1b0b0010810f40c19018284012908250546415a07980e51950340d026440704480c10b68801041800400401c145a0b0203183c00a40041c048603046020661540c9450303403035070080d19200310079000d000380292036130351ba94040c082e46170107440f0b20301d45203012030f032400c4041c800207010b0280f000103d41c51501c0740410b01d02c0213501500c40c0350340c0e403901d0103064042c103507602400303214600e4014101850307d015001c90380303126488000423072034041150811031401c50b004e2041c1c080c1758032202804000740c0d800b0000d600c209640b2a200d0804808680020301d810b4056240c41c0301c0303078040b6090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 107247994 1250 107246744 107246747
    0x3160218070c0615120b0702070f060516030203090616020a0e040201021b03010b03030c071a090d03080a1806020c01060e10050d1a090f0c011e050d0624080610 70
    0xc800c0c070a43c000c0c0d0080b4100a0400480301c2c024013640c4140755818010300507604002102105902070800740e822242c0c15034492030102c16091043c0b1500c40890f50030482c891445c54030300441d4181a000b40140d90034601c00308081426644405a50071810820407c2d0004524020b007564010b0b0403c13030310500d02450a5030002c0d540c1c500618110800841001220388039940075001b0321420310020f001d03251928900c864282d5110001e00401100881c00001f5883e07042c0c201050381c40c0c62800070490545441140c80c11340c0c2c5424064a00c8501c942c5549028500d103800b1082922003d00c9210300603691141186100d0849809810201640c43c0d0309091205000c1510024000c1ea03008990001900045140a00303020010412040b402c0041c60100715130300801003011595000550150b80b404205a03004403003050000c60002180d01e0440c0041110521520103400c004045250029000d0348070308880ca04071901414040e495000f025607006029480b41d2001d80003101601c02c5502504491070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 107249244 1250 107247994 107248007
    0xf01020f031f05040e0a11031c0f0509031b0915090a0f0902120f1c0c0b07030b041e0c030207020f010c08071b05010f080907090506030c030316021807 66
    0x41c114048042200c0c48031100075035800c000348002002080348417002c03500302e9103440507a1810b85200c000d0400200342410046405929001c55613000c0d100b00800070030507603080384022042c1302000070a000d81421a10100187c10855070b0580040217900100c100700925050014070f01e8801005c104e031a501141ca8040701c5a401000f049000700c0c00c1807091004000400e01e04502a60180e070b164400c0032001000300e0550301913121041514914801c9100110a04440c4030310540003030401000d50001c100110103240c2c01c040e8510b404119040c0d80c138002000e0310000801400000034824906881d86994801d0090b10050382c202076080c0381150700040d05010480ba403c6040c000d45941c403408210828048030000303075003c00c8100c100741c0c41c0d080c40404856580200c40c08240020301d00b124203070194078960721404401c0000c02c4180d0402890380d0103050064855038040c400c03220102e032180e5040c00540425a80e51102100b100355034010004507001c5241c070410b15980350014808415807150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 107250494 1250 107249244 107249251
    0x40e010b030a0213090c09020309010c2303130b100e101206090302150c0d0b15071713060302030a0f02250f06020a03020c120a090509040f05061303020f01020f03 71
    0x303c0c0d01a40e441949404d41c050b0210070401042c5441d1803002013000021580035600500300d940007080038600811040e1a032a04109a43c00c3c040c2826030000c44807106240210340c4a0118030812040f5000b955641501c10800d88403102d228050020070f03c2864500c0c0c00b840ea11681d40d000c0ba9011914000c509250060f81c04400380c009910751040030f0a050080201d0a510116404101200c0c64220b440b100c079a04140c0c42c90001d1030500c40c5000d6245800103032401c40c00e192808103498201c00e599000d840402110030000c03058000e104841082a440091000800e40c6481c0580e4a252000400e021100e00782104502c0a106100808500d004103c0c1c600f0080180b04410301c00c003100382071201d03d80e45240303002040a030000800d071081984c940c0107441040e030b40004881e103181500c4000490b41c010004844001400140704008600c0c081c03500c190000e01135803815058400c00c0d16441c1c2041c1c0200c61120a0f502041d003408100341d810010802c90444440003142011007a94040c40d00d8840039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 107251744 1250 107250494 107250499
    0xa0f0c020d0c08030a0204050a06110118200102070b03070c050105180d050c030f0a110607110d050a1b030201050612010c09050f1c060f06090e0a120c0b040b06040e010b030a02 77
    0x1c00081c0c40705c0303ea5412a806000018800710101d41e6842000702800700c0d01c000610154202003c0c0f1811041112160880c20350055405c140d20744004000fa9800850340c610302e0451107064800541c001d140c50042d40600c48640c2c5022044da46d0742042429a04003070900810081c1c0300707500b04e030114008540c0440b0300199107441c3c1d5031040740200031440c500549510006115000034541e0540780c110003064a8809100d040d1501e5664401060f00d40c810b8040031200341d07802405417002d00724440c00040c90210b400e030800c0404e5500f5040890343e450f90102c8110050f030340d5601400404c2c5001d80d14680b2411159000f804a5a40c80000400c05075061007003e00411481070540015994010901e00d070025100d00c100700a011030514070080c18141d0b60081c0c1c101d00d001400315450000e4000c5091048810300100072580081d6520341d01a040c0b410401c0030010007113a600d00240f03891018600a82c001c2d8808103441c1011002c00040b03038039004400c03019a03d440e020b01c1301614086040d81000380c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 107252994 1250 107251744 107251747
    0x10090b0909060a0b0423040e121606090c050a0b0c1506180906010609090903090b21010602030c06060619080a0e0d020303010816030203030304110a0e0a0f0c020d0c08 73
    0x141c2001c00c21910054012940c1c1138008200414915602040514160b4020503144100380f0b00d0303820f0008982c90030595034860741110245100144081c4018154010703400c51070200a01c0300e84804c01200e111b900c0446940c507003038400300318278502a8140d4000e00301d0781170102d1424000710609699202d203145150301b01036007000040d410340c1e0344844d0040c04200010310840c0602e400c00400ea00c45c0d200b4007a110104082d0500031540f6141441140c41c0b103a40340c0c0310402c2e810309042040d50950014801e408001042249030780c0180d0340010000d00074a850b07001140c40700d0400c2c02e002d0409000510490090300180f00a802c0d00041e2030345105030480d603040c07034000c0341c8400941d00b0203001c24002d074400c03030300c102c400d02c04200e41d000000794102d80100c41600c05241040703200703144440d26444007a41c036900c01e10126001c102019a048641580101110b001c0c40d60b4820f81484038208550000c8001e5a8048032280c035400d60148458080c414030182441e035054000140140000d440c0c040c105120 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 107254244 1250 107252994 107253001
    0x2130806070c2d260405061206060403060905070602061506040b0918010f0303080105030604111507120327080a05070516030b07020715050901050a020a06091110090b0909 75
    0x116814410b0b00a02c5044028110004504100841e04e40140c505008083c0401040d00c0182081c410349099480003000146007080380b0843c1000445e025080984c00501003000000060a511850822900c02c4014001c0c0c949058406410050001c2c0001c0b4911400e83d04450203030303120011542610055558151540a0800410407803910440e03c0705005c5840c13000420401d0f5400c8504080701e20954a600003a070700c613800d060b141e48003910002c0c5078071010581f1a00c0c40c5001c6012070b01904034245075070b00740146038071507021501c40d082c0c03d20046540c840501c2c031240d070f8100c000c4490100f980d00d03100a0302e505585a5105200341c0303c106042100100707101c410010280a416a043e8180105141d802d442c0c4c1841c000190040c0e82d640054030503040005611851a443d50a00a04503110a404c00c019600152210f61100740c2c0c14045000e1405480c0000f1024442c08103c036000300c2e0012440c01b6500240101d400018030150203000d00b080b1304000d007814420403280702120541d042c860686 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 107255494 1250 107254244 107254283
    0x80901140909042012030d0b0117160e100c0b06010c0602040b030603012403030c060608030c0f1e070b0f1614010f060509130c120602130806070c 64
    0x558811140d110101c00180300030712444c0300d0362442813100e01c081203188200403420400382400340185086036400a0003000c0d43c04849903c00009800c0605103810f08044018000704c140310b00302c6500c003900c0f402076030f0a25565030003500c85880d00c1050741c0200809800140182a19481c01d100030701595240700080c00d642d1054420145841e4040300540d25291618041d00f41604112601c5000390710b01050b10001080020903180039031100301c01000f155080d0307101120404101da9060b1001600c5a10000746000100700400c40c810a01018040140360303401e4a030304001e150182d01040e0885a0790194815101090300000c0b100c0c2005a99524801420380b088203000307400380148c9aa18281740c1c4402d0020b00d819000303108000c0c1000b0060920920070b031a0450b201070280a030803000e202c00003820042060740400d80a80034082d0300e44065038405000c104e0300f0a92a01700c0d8080d030003045a0a0490400342e01101500c0010050401c0f4603082100805103040c504010303060a00100b4000800d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 107256744 1250 107255494 107255497
    0xf0105061219060914150904060906020f0301081b06030907050d1406161403040f06020901030e07140915030d12060506030106030614010306140d0212190b0903030408090114 76
    0x2c04500901486a8840003140204600194a0001415100080c99500c169203044214240003842410580c03119161807004103e0b10104941d119030801c82601c0c43c0309020081c6000382003241c000e01030241050003407401945150341e914011101842071102c00700340030420708240ea03001c3e00c0f92880900b46041c0300c44007030701d40c0e0044051400b07460b0512041401150803880c0042113512110788170401084184814030040b1005011011221460000a0926001030107070500524002c140302c400c3c010232504004841d0722030100007404006444090500b0001c05034800b14880356400442082d40109460b9240004402c042111100251802801c0c5502013800f038040502129282e6031078040c0a8000c0400e401070041000082c080e0500642c864028202030700d8220a10904620200c000c0c4a07403102c1491040f82d000400d0030400315140c0007040f40c989607071005150290143d9142c107007908014809019610716800810802001c00d031404102e0384201000e00c4c040100000d44050010355 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 107257994 1250 107256744 107256781
    0x10c050a0309110d03020102090a0b0c120702011e0206160c020a05091b040603020405120109230a0609050604020a0501090609060f03020405031f05070314010e0403020307080d060e0f01050612 84
    0x1308007603201e500f80b55055000c0c1103246003e54901d00707420344540d40035480e8065500c010809070320003120780401f070805c60003420302248103040001400f400101001040380c850400c1d500180d001c1c008000c800c042d540c442d0095403829081c1900780b150b245d00481d0480506010b154080c1702c100000c205030040e4920300d420340c080e1009120b80c44a40314000203029520500c2480c0c031032018071241800908061040f01980756001c100c1e1200b842c03442940602400681d500c00945018218102002c2003d9000300c54490340700d9009032000e45424410840703c00c9032a0070041c10040d010030107000c1c41c1d800c8640041621860708001c80c107040c8020045010f4469600225014042c04079035045443c1c074483c3c03c11003804000c034140704035540c0100c01c5003141d91001c1d0f039092124014004201280c8958034840d000307802441928a00303801d913200e0641d140d0101c4030804e200ca51707485003001151050f10f419600b0942440071008076505d00304c000340c00c0c0d01860901622201d001c0303000ca04203d5000052516 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 107259244 1250 107257994 107257999
    0x406111809090309030f010e06010f081e070b0a09050a09060501050a030203131e0614060303040501050d0906050c0c0105060d020607390f0f030203070e1306061502010e010c050a030911 81
    0x12125110319000d4081c000c82d4123084050b10480c3d0012540c108940000019904120010032a41c00c06140c0041c0c840c5040558000c64000d01d90013203401e1405100604840d826911600541d91a01e42445095000c5a00001c3e94603e814018041603a1110441e0144222441c01685079103a507100c1d84240d610f0f00400038800c401022851904001000181d10038a0217043c0030400c40821440c1654840c04c112030440d0315400812051040d507005501520f03561520820001d400942941c828003212400e07104511010004a8039080b2944240901d6602403000e50b11011902f05a5020030302034011458001c080c504803003c0c1c00f08201048040039440030740342441c5501190715440103440e504890044902040c607004011651000d5140904100c990180080a1080c5002002107907080701508903603840807030480c6040880e14500400d4090251841c4400c40c40700c502038041d00311035407030352a8000b41e41003071134600d9030365040010b076a07507150a0b0602042c007403541e203088080011090700349607 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 107260494 1250 107259244 107259253
    0x100c06020c01020a0e01080a0b090115020a0503030903091302070f02060d0f14100608010302030607030207031403090309090601020a0b04020f0d060f050604060e1006030218060a0305040611180909030903 89
    0x300721660001e85d056280d442a200c011594680546c418243d4004140071604040c0d01d0004010403404c4125505000301c0c203205070f51940c5002c1c0e0b911402c40c4e0094803403005503440841c81d05041e20f8034003000c071400d48001c4411803908009698400b112f41c800c030000303446403a01081600c51400702e0b07007040340d0110300d0907010014103c0003081d2400520090316030840040b4981400715882c1e009482c2c090599400a009005913640e00908401a5000c00c00032400c000000d020010388090040155003e0148540a90b844803000b10601c00c0e000130081c42c0904551140b0103180104042114181d00640c055900d000807442c160040741c4a0010b100004110502e0700c1c400246068069014034040d24040b1400d101481da00e5850011080083d910360314005801c02c0200310142c001d90082907484000c1c440041c8401100c8001160303508150b003000003080d190010081007140500c00d840e80ca01c26460f80604007102403140c80028117591590601584040c2d01080c2c0070345040003500d4587c0d40080440c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 107261744 1250 107260494 107260507
    0x6090105070305090a02090f040606080712020301110a0804030f022e05132003070f0b070302121c050606041a1207030b06070219050a090e0c0f100c06020c0102 70
    0xa008040031140040000d00d404085800007501040b403c11503a00100640070744e0301ca0401a560b080400f410494645941784000030f00303501c2c01e011640080041c1004d22286c0c44003401898295021881425000041000041c481c2c0b030b0040300f1941c10a4040c5496808124481400c0e0b00e03060141912591101d2040114050354a90021001e40034006513018441a00c80c04551030340c2d0046030100615000b213500307500e849150b104265544550700101181e1955075150100440103040c0c1d0002d00c40001c2c00111501810340400404e03a0042da0241091700d4100601c0107070083c0380001c5008225180c59401207103940d07a070803041c0ea02500529143d4004010b00c080d842e03002d81d1114546031105046000090141c81c06441903140d44080a44001c0c50400b07141d0070055411000f68081c403000780e982e60045810b46440a5820141c845841c0c00030380b08401d428040d203402c40d01000c041c031030f004041140c81c1e280c944880351401c0a02d203061980c100312042c50f0075400783c004c0880701c502030361012800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 107262994 1250 107261744 107261761
    0xf060112061a0d0f0507030803070507050105060d0b0105040c03110412050d0203090901030b040221060106020118021305100305190308010608091506060f2d03152106 73
    0x30a040c207803242508208811903903901e0903040c0c2400081c1680300760042c1070080407541340030041840070f10034000d80d91940c0d140d68a003c4142c009031400000a000858941e040003c03d2095a8000f1011100744006d1044c0b3b40ea080300c00f9005028090159440d25104034102d4065084802103090700d005054a4507160030301180c407030700b071050b0a445c184543c8034000812030000c001c6810504001d4134800d0280c0c295142e0040c04d54000e40120b8012441c144504403004843c42c0d84140540a0405011154500346000f030945a41406141e00709031241000c10050b628001e51215010030094049065a1521040c02e802c17096948080c0007070280c4e5200380c554018040100c0212482602c0724140c60342c07100c000325102d100031a0043d0072984141040104036041e170000c541d2042c0e0043c075042c0751490b81e40044559411402c0b0102111591020442c54104800d66400718811505e20b114191b00d0846d10f9000f500c04540c1e8a140154108481d000b0120398481007a101c070704007a4102c400d5800c0c034404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 107264244 1250 107262994 107263019
    0x91b260408031006050f0717070204050f0a0e010c081812040810140106020a1104020d0f09150506060a030507020705040c08061906120f091406070806010207050109170f0601 76
    0x15901d22020509802190150250003900c8080c44080025800c040b0540d98100c041c402e00c1c000301d0342c2d1240c09d000c80401655039008062082415418210035800d0904044007503039442c3d8406503075030741800307503000401c2d0b80441010381c4500800381488400c85801e10003810070605c102402c1120000060118100a0004e12608144c8440d5420000b8610a44030140c00340401c0c042d081c0142c000c0b0203094003003011841384185900740200010701d03104152048500700c55040d042c0030b0405496203002818080034035001d00c1c8641d40f40000b4400c0b45041030020700148242d0413654203144c0c0d580082a0102d00c00c11012000d003130050000c00500d40c051101800b552411514a80300320302601c145114803210003031420031213405c1e03180c040c100e81e0070900107002390200304032070852203076a20060380109140710100c24801030890050710060500050052030700c0d000902a03030655011210800150364001203ca00701c46810340d1654185919000940c2400c2100030311050340c0c4542000860180c074070b0030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 107265494 1250 107264244 107264251
    0x910120503220302130c02011104080f010506100503010b030c04150c020301150f09020a020a0c03110918030703140702040c0e0a06020703080a08060d0f03020a0309091b26040803 78
    0x1810300149055014000500c0441400000d402c20300b1036110041d540c4c0103401002c04606d10f40000700b045051901d22100a0300b056001020030744c411540d041741c0613000c0c8a0b50303410075070a0320b040b140c00c001800050414881803045d1038160390000f00241003034050310150f901600306004002d04412100d00014895400940144d110b9443e240b200034076000d4000251049400f6500040d50813441d101640000f5000400080d056010b040ca030240060000070a00380903511414a28407100b40039414444111001045100140140141c2c1c036840344000050f11442d0354503140c4208400c1d00b607000c40c41c0a00802d50000e41140c04c0083c0200030310342100d044d010a8100f80c1d10458641c1c0c0d1414226512445440081d203040e000f00880c0404a204110306030f8404006030500350180700a5444035451891001c040d80181c01c0154003400b007541c40440840200308490052002d80900002d100c03420030300c0c02c08201442001d607042a00d605040142d0880505075403c0281310340340a00b41502e1550048 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 107266744 1250 107265494 107265517
    0x3211312090e1005091e04120212030c0a0e010203040b04053708061e04140a051204150e030615010908070611150702120c1612030e01050f090910120503 67
    0x9000801c1442101d00700c014889a860040c0e9182d02c03940c844026010b40d0b231082c5402c500840d00d12001c8a00c1e140300079400b484d04039942940e26082d1000c01840000c82d00001070444d041004100301050152054030140c900480e140400c007074880191a5079221041c40700e00c1c96007507090205290164802a0004980070402075490660352480c030b0860989650088080c2074101001040c0800c180c5600c0846840050b02266040c1690340c40740e900d00007510b0720308070040f00300080a01020a0505480307800300700c2400e0000f40c00410708002601d40f0402804803900b03200c0311042440c582e100d0481c241c000c012910940700304640f01e035001013901c840203401c40c040b40302d1500480348281940003d1481008540e0180150706800010500e2603404002c1000b03280c440c4c0309a14684c00c000100d03041c014094078803840000c1c41c1c50714001d0125200e440b107581c14020184420b00c83c01111a0490383c3c8400c003120f0b00401641d503203560319442d0360113030455001c80b08240380c55420000700100820480c5001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 107267994 1250 107266744 107266759
    0x9020901060201050c12040602090910080c01090e0718090f0609061a04061b0c060f0206060d050c060f040905040b041703060f01050a0201020c0f03211312090e1005 72
    0x31180700380e0a80f8015290003000361801c0202204c118074070111b142c0c00c18032401c03015252198007400030b402024152070512244135041c104010842e42004074261046080c00c00d00a0a0302e00036200030003a0b0b004140e80e00740aa000180c5011980b111440405408011130410401d0390201d000320040460380150344840d46001404a84244441ca8030b03181c81000010b190724003418136404441c0d0780d6144003402d4036000c10300801d10005403002c07000780c0501000e0b514619600c3d24032100a203002d001808260041c0e40751416240441d0011522036482e100c2698069910309036a20040114401c5500580c1e28501c0d20302400100310410017054021401030400300400521068141c1341484180c030110b501c0301d03030b00c1156076282d4040d40180091038038500005040c40042c2184904042c400509204150400540380030102c402104000c0500d814030880607441ca400c040b04c4d000b481d26a400a060358040341c4199100c0c030f103d0340c1d020001e0121601c00c00101d003028445110031a9041c003c84e4401c0c0b05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 107269244 1250 107267994 107267999
    0x106050402070c15051303050109020906010c02090411010c0501021209120f03010519031e0302010e0102040e01050f0d050d030920030a0b270f10090b0c0c1c0309020901 74
    0xc0500a8030100c0d41c2015190300c44614100c1c0d150180c9422400d684103101041c0044002c12426440761002940240c00110740101244104450f10100410503410b01010704a03010160302ca620740306a01540c007540101c0c203035280c0001a50426a815002041580000b810407a01d421802903d0701030101d103000c558441c5400280d07034002e40140c0783e4a020782c6c04203000401491411400380100d850100f55400f11664880e220f90414001a42c0743d40f00715207540c400d01c0e080640c244940c0140030001d41c001c604040c10007041d90f94511041c40b450f480b600f41141402d030b241e9078024178034017102d5205c070498603405c00040020300504103001c01a150140d2699285d0000394101e4100d5003000e4004002d400c06101540e1070342551580a0102d03d860000b20102a0400d0201d543c5109610606401090301d4215440400c0c58070741a4550724450314100100c10b40050250705100fa00221a40000c07074544d0b6282142c117241402d4442e13042c01c281c00b17070b4900251094156015160740390003662505056038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 107270494 1250 107269244 107269249
    0x905090601050607060b0406090f05060117160c020303090910030c0614120403110318090901060f12030e0901060905030f0c0303030703090f0507030605011d09030f0307020f060a0e010605 82
    0xc824440c2581040c8200709002c0001c0e050f50003134056000041001800649804061007121507002600c941582d6480c140071540d83c00c10005580344002d002c0601c83ca16155910910003401700b0300d12000e1203041018070f421980c05005034bc01526028007000c0161405030a00c05400d8075171f110a44100c10f00c408042289445011403610945650141600c0e040b105810b1010000340204180c0c20071004050003408180248018001c04594041043e00040e2181c01c00000d210701810340e41c074aa24040c010410ba03280d950420049405054071400e5060f0581000c0d030341840400c0303070b00d940322401800118805800203140400e490064003155489104022942c0d522110101661792540c010300016141c80c0c425000002c00501c90114030ba185501c41d0369031807030038080e504212203043e2034100601004000c250000408540c1181210f43c5007000140c4070b4982c45030146a26403c0300c0040040c0b000b900820a00801d201204129082031602c1e0032068001e044151040c40b0725401d011300000c0744e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 107271744 1250 107270494 107270503
    0x130b151c090305090f0d1406010528090213090504060501090f02070302150601050c030f030106020f030708090f210d0e01030c140307030b030a050106030303060902210c0c0a0309090509 81
    0x3a036041d168140780c51030711303400c1041d000400522107500c00301d41041030740000d4102c0c00400c07491038004c0040c44194103007002c2100c000d10012040c260000d0041548a11500d000060411104801c40c0180d49098181f035080d00d2107196040b4051044c10a000c2c881000700c42c0d84418108c4a00c03507010004042d810050070141d100d582005401680207200c2800004040c801858200384141005403500c40380000030f505540043c081c1070403600010004110450301030108a540c8407030380000d945054040d82e00c010440c0601c2d00841e000e1080106500c656844004494140006101c40207030f08004001c00700d80d4405100d100b03030380044c55600c00001d0715400f070301034810b404055449400080c0281d090b9001306400c001d00000030144c40d0040743d010761b05d0520840308503900810003c03402078114240507042e110f0680c03113240c000380704002c8414203083c84c0524004a03028042410215268880101041d0107881c08120b0180181004001010b810200800403542c81003024051555403000c8540c45 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 107272994 1250 107271744 107271761
    0x10b030c09040f0b03070603091103010507021225060b010e0f0d0201030e010f06030507030b090303010609180b03191a090303070f17100311120c130b151c 68
    0x8031040c01060840d00d450340062107811564034000905161020000340307445071a0f80440c020039a9601c50700180000501e8010341c2410560080c0414202007900a65883e4110a2142a1030003c42c1a07400c5501c102c1690f8000b0002d4540c0541044007030818078018500040d41340e02184010f002c28400b030500500c28001034000500300c0c01d00141940040d00540307040101a0441d540c0c40220070811000b070f10030403001d14002e02c0202107140c00c603c1d000c003045501518156003a842800100200c80d07200140c04241c134140503141640c40d0345a243c1d00042e1210701100b95140c0542c021b04016114001d01c0c0f80912801000d800d40340c28000961640c07003200650b561182c40d0810000503030f2660160030702210041a80c90329011480100000c5206042c0aa800c0c9000c00e4609200300f0500c901e8405044903160f0841e241d000241c4035174500c0e50340703102090815010341079000407040c202025520000d25211b02600a010380d4070810141d43c00c0b544100c00c00c0d144000b041b80082007241c058420401c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 107274244 1250 107272994 107273011
    0xa110c030c15221d070206010e0408070f1a10050901081002070c08071e0501020105072c0301050a09050609150a0203060a030f0507080c06090108160302070c030515010b03 75
    0x150352641050710301641e201001089492212070602d0302c00c03066a9040f4002007502907070090700083c4102a2100031540a0050400c640c80b10005001da46407416407980c11550248160b90b403819507180140120710104806000700c008082c406040b441e03001405403041c200d40319250320040d100c0042100003403003030060040c503612503104242c10f0200c40c2d0041138140d006034102804181d0301c43e003061811410360800c03100311b600f1590062203030402e4a040009044240003e010303900d030607007008058041c6c01d01038058080094403a001c04d0a00762010b0130f04043e018000323000d0b03407070083c6540d00600000002251103208541c00140b00c95004a207150b40008020380541d01030300d8690109020750000f4140b1030f8403030000440000040c902d08802c14902e44100301400702c2d540751807062820700d00f000c40c00c20b00460302000361140c107030381c080103055003c0042c0c0074540d5100b607079103000c070b00130f015041005102d180c0ca401d0201c00d000c40000e44141e0ba08003804490680e0303803070b500000b030a400240d07000c41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 107275494 1250 107274244 107274259
    0xc0907030207110f0301020f1801080c040537060504030c08061306091a010e04021005090d020607140604030206010f0f0f05011b1709090906060d020d030c06020a110c030c 75
    0xf00f840c0140300703010f0000d402800542020340650000065901404102003107010444003030b40c031560404c0c500c0307510080794071005040500d41404100d000302a0b04ae60080150803803081c5588040145500d030f03200a0b0311490031211f603103071540a000f0b035001740002c2da80e000400c100000c091741c00241c12031090040c11346080e440c0c09030b50b440d0790190030300b1f0b1800c5503110510303402d21040c10240c0100e90f00030711004d40140d03000d0400340103100781824000c24060400008200640309521082c0c007004a0b503a060300c10341d54400c001c2c140025062044d50269140303025034414030051590009102e81a5800000340c50b0000d80e6501100400c01e44510400c0410019100300b000b01e0342c085c18169001840c0c000358450316060070343c0c0b000c00c4030942d031041f2265075201046680c80d5040c40414281e2101c0188003c107994140400011031221044500038850840d002c0c00d801014460310500403c0c1381c1c440d00554031059605000f40400141940740711192007801d108684520340000c00120364072002c0d01d681c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 107276744 1250 107275494 107275523
    0x501090b030a0623120d02060712020702030a1a0f040203070303030207031e050a09080610030204090f05030309070608090a031409011b060203010305011811220e0c0907030207 77
    0x142060700000c0c0702c42c0b22256190700005000c10740c021300078070880f0081e900c429040e20300710401c5281e05543c0030211003644400d18480e030302c5800281c910f81180301400d051581e644200340c448040c3c8142072000390140901c0e190074041218403102071103132a500c2c21106110703603a802c0301c150520314110b40c0a0b505a201c84010070110b8000d6000381280f5000e807030000b0200c0140322a500754604414003410001d100040e40017032695020f0108005000200c0103440d0740d007810610f84200c19150b01010303108640d20321b032103801c200c40700c4070031100c141d4058207903500c0786460140707180c075805103224120103c4e8690b400202d104034040b8403824015815100e440343d019031141c0c88803846e0003c80d443d505104040c01d2108907031259200030020345200300c00143e070b41d604518007030742500e548010217175003c10700d2200800000c8aa000d00490301d0015102481604404040003074100c410024081e0040c0c900904500048804a00101140030945036035059071034910049089100700d40c000361002d00c485414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 107277994 1250 107276744 107276759
    0x60307080a0b01051b06100b0c06012c010b0702030c06070201080403030c09050307030b101203050703050a02031b030a0815060406110f06091005070201020403080708070c030c062304050109 83
    0x1030b2212070600d4441d04008010700e050000c2000710f1518515070b8030080410100c8915807501401030050300b03503114104041c03030780c095030b9030003060080800e410740503440003125216000f1a080c880104804114442d69a04481e02c52640241402c4c1e00901651184203020300f0030804030342400c0c0e41a503030b64180341e031a51800c9001740310f101c03002020004864030005e0641d03000c210200145000d03110f03012250170132803030204002540340c0c00400480603d8107031001194114043da061560141041707542c440402c0d40c203c3c00c5203d1006100404800c450111030710b0340303002014120203000c5031109031071500c0320080102d1741c40c0e81d150300c0e0764001d0080006003c03051190310f10b062625007039000c540c100b078581c6840d182041012507035012103500440d619540c880340d42c05226000009070008500c0e00f811902c0300700241c4112100a452004001820410801c1c074070502002143c000d9110200c29440d81d4004000000c80c1c1a0108844400c2d001805903038410400c03902200c0b01615001d041c0c1d840c0004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 107279244 1250 107277994 107278001
    0x611010f090f080c0c0405090d02010b030705090c031009060303031b03140a0b12030c0109021e0a0608070c0530040b0403111504080c090108030c1e0705040f0f0b060307080a 76
    0x407540d24901500200705c0d541c1e1100d02546010f420314001403c41c04282860003400c65000200d20f500c02e501c222070070410f42d212800f0181d00030038074145041c1da03a40c2e005000550741e283c1d5401014424901317040007080c143e06a2201c200034400d80d01425a2154080707080f0b0544d0401d0185009210103000030550b1101d80354014030090901070711600c20002c4465841d070868010329a12842651a0340c0d0b48400c51525804100c900803040801d0001018400045460102140200703028001000080307401c40e40242a20395600340e00030b04540030031511003900303c2a01480484c2004200e521228030166100ca40142e9060303441c0c02002c60305003855610703080101e00907103800540041c004500d00d01080f1510300104041d1003a08000c4c03010303500c44030502c083d0b22016231085600f5007060040384803200001c074824a94459210300000e03801800c408032828880d00e0350000781d120345032032144100b424081d0062102e01c1c16004040081c81c0307110081c011188811200c0305c00043c10000005c5d060103041e403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 107280494 1250 107279244 107279257
    0x22805040c020a020303030109140105010207060c061505031006032013020706061802030f150117060303040906030303060812070506040816080406020a051002160201080a090c0611010f090f08 84
    0x2c1240d26082003600400d003547d00030780100c4400c0d5266054040c0c2030141c400082e00400b421b1000300411031801c0e02c014200100050018225a26140b4110200d88503140c0400500ac006041d16014146910880010070503480100e8a802603030f0303c1e060000c0c4803403002c52018940542500c90f80000c40646030700962000b041190a180e0b601804250300c5580000540b8001021000695034140100440c066520050406c2800d003c108002006130341c0c040b101503909840079207400196251034001074158001c0d0b422071840b00e4a85003001040c0350707060300400100d48640050f0307902d840000d5420070702846200c070064410352206c404034001642d0b02005043c0c0d0540b00c24403074040c466940e03450110758030035409100103902c82003c1c5814408240001002d48081070b00c01c602d0308804402c8220200450307480a41808102c00008803540850740000030f80c0c2d82e208040e81c40d916107400001e4625514101208030941c80d208503054500d072144248213440750480a040e018510030f0b694501d170b41c0e101c013 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 107281744 1250 107280494 107280497
    0x11010b0a180e010c02030c0106090902130515040f0209150f0a05030703061d04030206060406050906010e030a0c09140f0709090902061902030a0e04050f13020d140a022805040c 77
    0x28000c102d6800400e21904460181e43e40c041c6a5070302d8001041d031b080d41d00c03e81080c030707966240140752340060351b030058800c00041041d01c1c04102680c0d002190150b4260003200140c00070308000301c0030802c03860f9500401c03004400315100100019103c00702d51090242800075008250b003040002d11460194010350343c006014603002c04c82984410040780300c10100004d0a14046c8404140030815806000540d84000d06550403c41d40745170100152120801a11482c10301010121001d0301d40c0741801403001880d0001d03a007100d110342c1e6081040003003000000d900540440800814a43d50148100fa03025030490750b6039038a40e40c1414a00d000a1411b800b0403680450304018070350b00f0b02c104d20400c124610b104d401035901e03181102e0005c1c101d11820b11207a032155250000b000041040c2e03075401e0307410424060321040c908135140701081650000c0d000141010400044648003050000b500d55851842075a102d04100c00710305000c2c00d002000d800032003162840c4c0e9400c1c411800d0a600210320040503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 107282994 1250 107281744 107281751
    0xc0f232b0318050a06020d0b01050a2c1e1f301b0909060501020307081308100606120b0913020102100f0e1b0901030807080403021305060111010b0a18 66
    0x142e03a100d103859120132040701c4c4d441d000304130840c15003601d1044000c0e0140a0a1286c600301e100b0600802031541030004803c800c0c00c40c2040250246007104603104054090128440b03030034118a1003000c8e120708075078144100104009030000704241d0030055080c21803616205081c50019035076032513038440000d18500c040544043e6030141012801200c3c000396000c01d241d0585400d0032001406104180c20442c0402e00b001010031042e64000304072250950440c58107034468040401805001c0f00d00c0d48403007000d100f2200103046104150f03100504480558562200c50030880122409440c49210b20980c088807910004400540c42c00503014224414415200c810400b032102504075840a0f958683c095602c1d02c804000030001c112440030b200b001c02803040251a00000a144010b050000501040c80410414200951141900c010350342c01094290300e50000940c3c40c0050004403a03e500188004e41f8040c10054184124402030700003400b6140d05034203295482a034040170540000c0390694 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 107284244 1250 107282994 107283041
    0x31203020f0a050d050105011107030b0901091704090c0801150302070516060908120309030306011101090b0f0f0a060f150909181a090703030c0f232b03 67
    0x100d15004084602c42921a079860380c0a1003206801c440058022605000c130f41e00504c11880780004803401140d610002018650790340d454002e0151004c003d0003048004070120000d0001d400c0c40c0648190b9103402010002c80140031021145001c007880794030410442040403c0003184250000e1100c0c40c00f81d0215459140c840848260502460740583c0014038014030038001ca407070500a014a4140b030120306030031030a1000c650754880c44007801c501e041c0280c5905030024440c003900210611034100860010305c1c5000702402d20000c034101c2d4036800040304d9600192441c01944550800c0c1c1c0c40da1045111020f0514040340104640b0041e40c509000265100280c00681030003803c00c075030b1440040060103102443e0180c4c421145d0a482d15403070082404118440c03200003411000c5982500d00485200c0041c1461125407c0d1454007406c103c0c80800c1d80b4200000d8150310401c1c40641c2c200300d41002c500f403035402c281c036900c034091015080e0045c005021000c1c40383d04001c0d8000703107044a5910312076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 107285494 1250 107284244 107284267
    0xc060209090f0610032304050f0303010b0d050601180509100e04060c0e0108160c141c120e0307020904080c060103050c0a050d02010e010309050f1213140a03120302 72
    0x1e0484140790049801000c0225600303203c03601000d0542c49083c00e10122224030400545c01c3c0c4801c0c1000340c031420000004092000030441d00c00140400c0303087e2641c958452100810301c0e4000c02c0d4403e07582c1d0502d00803d04552081c03003460300c00c51104100d0252030741000108904c4450150a0640305528a1804502d000c41000c0550155104980000b4440552500a0941d80c00b901044d41881030b02d1040000410301008250040081852308030850705540c42d0275001c0c1d10b444003c240d142c1c400c0b004505d85070306a160f0815071900054541a06202c004040c110a0365025268030243d904144851001400c002d1070b0103410170320441905061451440825107082800d900580c0c0a50180750000b81c107040000419000c2c2105880c11140c1880a4001905004030600c01504055881010070240301c005c2c400820380080c80d01c1039034901e00c0076407180041900103a50b04442000e05100004a0351900e803522002c40700060601012075240d5110b030280707048039843c0301080c1602080f0703156040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 107286744 1250 107285494 107285509
    0x80a0506012106091104050612041b03030e031519051015050a030b03060106090e0624070b010815011511010f0204080c040b090a020711060a08091b010e010c060209 72
    0x40b00402c80024190314107100102076519150720301c2e842003c00c2005100f55100c21007102c503600401c00a40705542c40750b1030504407000412b48511000c0003205070100c10954000c2d020041460110211038400e4001400602030340c00684807100640e004082961340d440507a0051540400785c0128042201c0e55860210002110848000002080040c0c2c82c080340b5003601c03032078404880c245c0c0208841d606280300070345080380d507020b034038590201c84c0c00143d44c40d80c50795802040414118048031041000400d400708603000440101d5040b44d40000106e00361600003409070b00105e0080c1c0d989010b92900720700c61781e8822540c2d8101c040180c046c01c2ca080c0b9407424090302081c100d51040040e0760b64500f003503144c2085d02d5000b056110310b0902d00d2500090b9507920803540c0005a03d240140d40c1d940d5840c02d460900c0d46a5481d03a00700401168009500307800a070b84601c070b1800d206c2907560681c0b07071008804105020013850ba010450a440010080d4410704480140c80d104450040c80c11542c0e40025440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 107287994 1250 107286744 107286797
    0x60102060c09190e0106200c030d030f0906110405010e04050f04030e03030403240b030d0207180b030718050f0906040f03090905100305010e0a08070204020901050f0304050703050c01080106080a050601 88
    0x4504078942061f1081d08801d80c101d41c032140da6003d000c54450013000070340c840c0008404203040580358030310b05010301c00580c0003035149070b44108208003040c46281041150717000761183c1400704150900d944002e0800e80116807143c0145122a6103070394032581c054a15601224100b03402d0310040c4004000203080403803020100c83c9007031100689a130f4041044007503651a05e030f00c6000b0f400120660368003640000300358098030504101c02d01c07101d50402e084070080100b0204d0f02e61520420500280b0341c110540c0141c0405612001481190356811506207150710550b00d42c01070744d001c9030004002c41c545c0c03643e0119651203494250f8000c0d563301626400e4030015101424240d2020b0802c0007081401d21a06403407200140141603941c0403a2280c0c082c2d80030302403010303004540018050420340c0c4140226007546600c0b91085440342002d05005686141c18082110030b8416560360001c29070188911504070741050303a4001d420350b100c000682c094000a0552410b200c1c51346215941c440c00c52040700308 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 107289244 1250 107287994 107287997
    0x7050f06010f0e01150503060d0305093303010509010b0307090f03050d1e09030813030203010c050c16181a03030a050d0b09010803120408040f09090308060102060c09190e0106 77
    0x40403420001561481d203c181d03c00c400203600c0c0198241010380010503294407a1042300d07451808026410123580350301c40c440d0055800004c03103105c8035420f1101c80c650308600d40b034620496001241a101600303148428000c1039404804030004109054031040107641c0142140780c9001da1598401c0c0c4076901c0800f44e00202d401c0e400200c0f8100d0680d0303000c0640410030034161411002280b40c42c1003d04180601e000140104400041c00525042c40040c5c4134019035019008104002800c44000d00c070382c001c10741034000c40c0039440c030f01c5050045403403120041d20125144500d01c044c2a607e80c0e0024140310b401043d0b040407c00a400d05a43c060019021424668403195a00e481b09038442044a800800b02442423100030b0051016030380000c00d0350800c0d214254040400d4840f42098207007401154030150b081a011500451181c0c0c2e90b40205003c1846912000c40070703203c0d00016a1540f100302c80d80c084178581405000325514003d03603034292032000800f02d031403095295000da0945a800741c00490 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 107290494 1250 107289244 107289269
    0x3040b04150c03090b0702210c18061008151003020c0d0801080613031707050d050c070201080c130e040c08060108150103060507050c10090b0a0608030301030807050f0601 75
    0x300c84034810041954036440c248a2500843d5805014444240220004503201142100840d01c801751800d003005001c0340c0741210305070342c1d03261940d4480816030301501480011a00000b500305000c0000d0003150700400da0200c0e080d29000441d111030300182000483c20f0f2803501c500e1652101c071203202151130f807564096500da111502540c60441f07180c0700074041109510040020078404580c0c5908524000d800151082080c202151541e0701d21101d03400c01c6000c14248442a42c002d00100441006180244900d81d1540503220042c000d401003c0d000c10602ca0000b0420102070740100003600c85504014030503510703002c0c0d0710410482107130100c88907041178909102040c0200103c500404009004000502c43d03407407203050820042c44020489616000403072007a500600c180c1e040109850121b80038100e036409400060b1949101c01d5600048410200e004001c4a00070072040c2c0d1310140056255074a981e07559076040e0310564090704d80303000d90888807450240921940e4000c113035030600791 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 107291744 1250 107290494 107290499
    0x412050604110a0e011208040e07020a0506071d130f020a031406040209030d230c0d0e06040b0f090a0e040f14010b010801050409020d0204050c13051918020c03040b04 73
    0x11559668a5010140b003105810350130002d1010135400781d030550320b141035072820a080c5803810040c907004580240b20f98554920412000743d038000b074504045405242124115110dc80090300c41440c8080660150b280308950314545080c10800e0522021444400088a401e591211003c903002030022100013522207900300e180e021980070540e0803207000c0720214900b44a050010f541c4a040060301400d200c01c10104502ca14118803038000b022025507111a035407060707982245e41303810040026030042400342404408034100710081e58166018000d4041c80c090803040c1280c45504080003440e48006695404111081c03c200b5140c011440b819007464062921314102403500c46084622410307078034000c0d0071312040ea4041035850456405540c00503c212560000c2280c80b9041c02d8044c0d042400e000a0215000f2584011f00c0050381c034015031143c60782c80b5003c021f4940d03d403a240b1201c00144650034007042012100c120030031401c220005107030803802d5000c80e046411540c032a0b4001c10020804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 107292994 1250 107291744 107291753
    0x109050c0f0d020d080c010c0305040b160504061101290315060612070309050a080d15081213080d0903060b0402090901060503070203090405090a02030d1d0d0204020412050604 77
    0x940d06000c1046450603203000321840880c1c0b5040305480d01a01c00c0304800d412506000c034540031074000040960092068a0300700501501415007510301b26020303000d03e000035401c2205140840400714503551170b07e14051900d10126000c441c1c0010407045956a41035160100c41506140c01203004c041c82c00412245c609020141012070801c0c0300004d82d1011410058190380d500112084924201d5076401e080e100c10300c01714000e05441d1801011403050145070000e101d244800ba04406010410500079000a40500c801c2010184038000300340d8041001c40764001c1c100405400c2c1045226426802d450741c4805c21b0746071030408085603000c81d440101c18400d0103624040e1600540d0141c0781540b40000c00310200760707070700014415a0200240030000c03941540c42030003112002030f0014001e01c03003401c0c482503203030b1a48a409412407007846800b10400410703001c1c4810b001080300d003500f0304200450b21001d01070800e080180403a403042c1d08120209000d0003c20f41301c1c40003030040e002828503103058070700f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 107294244 1250 107292994 107293003
    0x60e0708010605031006120b04090f05010b03072105120a0306090b0607030f031e0e0102030603010615080f040c090603050d020d02010b03030a271211040c170601170702010905 77
    0x44241000f000f04100301c0441c201003000f4044941c0c6281c0040642050032011004141ca9041190702504045020040c440500942c030b240364000d9000b00700300919a030400d50381e4000303485001c50a1040c070880b82140d4000d06038204403e07000b54182c1c4c3c000b010b001024800c1d40e01010113500442e584090600c000c80043c4204030703649405071101807805000741c40c050300c0052030700d600340d08050701c5a1050761580080040038100264284081c451076801207201c0d40070390001c43c0d016009600c0c040c8002041c848205450841c00d0342d0740c460103242d84420240c0104d0f8480100240e500f400c81050000342c01e200307403040d10f00460041024084207580b82c00000c0c04d000180c14620116070501c04071407003e540101c02c6510300c2c0c1e01c41c10041010001e01c0d010209060728581c0080a02d0101304000406072108030000c00d00740e118404d00071003007610300100400c42c1e0079144448002a00e00e0300c9400260f003132003031464000405043c080803101c1141704015006004941290060751144c0e81601007040400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 107295494 1250 107294244 107294249
    0x60c030318010b062d0301080a0311010612120c05060c030901051006050a030b0d0203030c0f1006080601090c120c020d0e062d0705030a0c0215070f020402180301060e070801 76
    0xd21a0044142c001811402a1400b40394184175000307403910b0000128110300120082c09030502d850f5030b516241d83d500d81d41d000e8400c4d408138456800f08100d0920600c120820303101d0301c204010f10341400c0d0b141d04a0f01e071032840780e0301c052000c0b44102c2d4010510030007a80b031190b000d100a580e075a107460840d0f607003540c502610b03951960840007814890039030090103803220f80f00c803032900107003866440d0002040400300840c0030b034050000141100031080007050030340f042410f0384201da540c07202005030720302183c0b940d20660b0981e401800c014494507009401c0f11101c40f000345410104202034440f0f20b01129850501030015900103990b01991907002200f1400c0d05404541c4d140c14140200a0700d00c3c0c203820901d04002e074080c480781f0308030480c603c0416560140d130094200c80e12011b00400262800b190030b401a03100d051b0307054460a61001d010f0803100c5555200d681d041d0030025175400d002c00784d0841ca00601403500c402060f071203107460074480c0c04001d0006140349400da08004a01900f0b00034182c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 107296744 1250 107295494 107295541
    0x605060a0b1801050c01060b0f071b06020a020f04020f0c0105060f0d0803011e0b04060305010801110712181706040209070207081b010903081206030106050316050909030702060c0303 80
    0x280700d2010900450402603060403020b0a00b240e51705003c905003401012031786c200c114100008540b1219912010014010300b41c070442c0e82c444030040c4000b000400415602c21b00005178030400c0f0307400040c00c2104007122180e80140c80541002c10b01e800e80c0c00d903500b02c1810401941c1d900c3c8200106031400780e02d0501075020a581c12035406178940c8480c078803840140203030380c0d900e02107805480030071050602e540024242c21745800d40722a11104010042c10080c440c19140d176003003800d0300440529640850314003544c8101050402440f1400542d0760348140422468a80307071070000042c0c042c804090098404103824040d00840c07616104100296070050000300c00c40d0311141c418059560005030340e020403c904440b070500c45440c1c0300104c41915140e000108020000f05001c00c0520801c1512030085104074001c0c01044c0c0c90300245613550381001d0304d03031302c1103240904100854101411713215040780800c2b09803440d203030a40d00401e440d607204410100542e8400000c01c0040ca030703a540c0811601c120f4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 107297994 1250 107296744 107296747
    0xc020c10050f090a05031f0501080328020c060a05130e0411011b05010234030e1e1c031107032f040905030309100203060607030309020613030605060a0b 67
    0x2504010030030b0080c0180c540c0d03403a00000f822415990b4540c032503001007100400316440000c800742e10034413148460b000e0b0000e50b424100003156512020081d05e003201a00400070b05402050f210034004003100780c010704258026042454200e0320b8005c01085414480d41b54596a0391403c01084001d0880740d100100400d014014003000928000e00024000024605101442c1500780640c0004e8400d4000030072070f41c400500100041c00c040900200c1c1c048002041960b5103a1180c03241900c0e011207401400928003041030f44032071138050600d580d480c0900c0820702e51001c030080860550201e101011100744680d04090080523488008000750508460127001d095145945a0707500782c4200e1090646a0b00000070f0b1009003018440c2c1c0c401d407820043c0240140482403d101e13031603901c1958031944901884103200307003044c2c0e6030003128020a005400d0600e090030742d0f20203c000303102e00034049a20942c200120412880e014040b600514058900000c3d0342c200b034020003541c4001c40d40000505c3d5030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 107299244 1250 107297994 107298019
    0xc020d1214071106070812010f0e010b030906040b1815011a04080c010e041e0f050a0612020f060c0d08070e01090b0702040518030c01020d0501090e061b040b030106030c020c 76
    0x1035120f10310300444400d5070381544403a5940780016040c000c100702032038100317200d07000041c1c1b03999015842421202d4000d103c0d900340e41c070348290191500c411920300060f64042004200014107a04e2540d901000d0002c05981180f2444680d6003414000041203107101d003084010b0080320781c590b203c40750b8580c00c0d8004502d8180741010680d00c0d51105c1e0044d9060001c4081524019191074110308174010050003d414460100c0804000130f0458001002030b1900d040c00049040105205060030f817021a40510140f8040350700700304015100d00c014603000301c0180300081100c8000c0140144c00010b80e19120305d18640f080d0020081800705100c00e0412802010400c082c20f541411a440180c0554000c0b41c207644510020003a010b20000c0f45000e80b2001402012600065001d4100030315107003820f00899a0342c044c080243c1e203210341040d55603041003001c507000910024200e1088042018440d040503512005c0310603a8000341d22000c04a03480b18985000658140103d114004048038031007a03004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 107300494 1250 107299244 107299253
    0xb0a0302010f1101091a151c0b09010908121501180501030903020a150911090408030705030a140106120c02070e0c0c01060503070603021c1107060203070c020d121407 73
    0x151040e00b000502410720080500f041c0e0039008901c40d2500102014940020101e050740f00c4202110200c0251082005140ea2442d2104105488404082a000c1158050786426a1080c0c010381007454030366030340200320001520000609151810350300070002e03515081e1421f200041c1a9081a41007045540c01680080606000b000607a20280780c0054200700525042e8607141d06241d001e0800c85100403544000304035500141d583d03512444841c400f107000c80d070501010100a075001802108180002010a803003140035541c00011200c020a0071282d100c03a580c09840282c0051001807000003944505004a001302e0b9004c0c0c0700c0344010101030f860540380034800303403024208172580c1c040000c48500c140402d4010b034026103c0102a540c000342c2e6076002400a521407240070004c60b4205c5040c00c1c0c0c051980c414604050010b4031040d2800c0701c550b490310029407006000600f8000c502d0b40c1c10002d80c440b401c804402510a2848038807400b010007000c2d00072600c20005016603003081180d40b0008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 107301744 1250 107300494 107300507
    0x7020c03030a45090216030c0203160f060f02030f090f130204060509010305090303150907030e01050c04080115030b15060c010912020c0a0515070507051302040e0610051605071a0702040b0a030201 86
    0xe90140b41100d236007201840004d050840c40c80340ca03001d00c0c1107580081400b03090568000100d6400d070b2180159a0704540c000d076180d008a1903100c4c2c0c10ba000788100e038202c0c1409144c580b03948200400142030851401ea601c02283c01076000080051804070b041103c5581601c242034104001000641c00c42c0382a801540701200c12049050103102d41d41c012038207040c02900440c8858804000a00140c505110100c081c0d4204d8031501c0e145600f04400341e10810707030038146141640d400802210303407035540d0340414004c6040d10003450b410140401111010100030310940540901c9614000e060f89480c0c54024600700e401001544030f105500c00800c407542d521304240074405042203429072030b8616070400a0800c94507500494001c0c02d0124600e00c1141264010025941c112104030815211501440342000080080030045001002241014520341141c1315101d8030950482c0c0086880d100301104441c981c1000c626180030220381c000c03c6180c24051050400010380e48207101070310310740000b080c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 107302994 1250 107301744 107301787
    0xb04030f060b0418051c0504060503071d120c011205060112050a0204091e0516080c090d150204170123070c0f080a02010507020c03030a450902 63
    0xe150b030301d90350040c1a4565800c40203000075150001d202d80203a90400c540c03609800c01c14000c0610002a00140042c00303101540c05031100b81c0d43e0070742035a0f140041926810b01d003560f003c150301d00000b90800716a4400c20660f44518411016111a4075803038009003c40c0081c0642911081c140401c2011f1a40d01020b00d80c00783c00c22050102e0141c80709000403000f4400c0d80c01132442a4101140800c484448446802d540c0c000c10200700b00d141e071024201411041e280a444002903402e01c0461004982003001d8031440c5002000040a9006a0703280d00c80e0030302d080d4004030805e4012a00b00059070305d04c0300242c1c0d500081b10091150080a0201e401445600c1000b1500324900c5c0010030243d0b8413030000a450f859200081812554050034644d4194114000724001503003072400240b80c140c0b000c9842e204460000d0015410504501c03000c0c0c800c010007c104d5981d01500118003800d03004003204581e100d445c68400034103108680f0501e00c012100d1a0030142400c2d00420a03140085400240d5001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 107304244 1250 107302994 107303003
    0xa0b06040c0903050d020309090c07023618010b030109050a170f03010e15011d01141606020d060b031509190203190c0e030a110d23070b04030f 63
    0x204007035a8001501c04025640010380701d8401e80c0d16500741503030000014040300c042151880b0031a0b50f040150090392180e200025041858039204040c850354501294200c105400e110346507080d61030300131101c50074044038155146205554840300020b0203200d006940d8a00b90002d010407207040d1911581c5800d20b6400601241d0b03c100c00882e8080c5d90015070b454114044502c5980707596a81c2d151f142d918003070340c010b06807480700e4440102c60b60041d500d4000890403030f402806030325040c0005480802845103600a0518108100c1c1200e0144d02e05103039003184600001038960506400000c202c619a41088080352410003c2c03001048800d4011052285c044418075030b16070b41e4004800c180310300b0f0b11000e60028004401d100c0c2c811004510303140c400a03d1f4004000c070b41d600e14000c4814801d070321007581e059001840100003007031040c800501c980a000d02251110303a1a5624003881c0301401c1003440341300311100390aa4080d0005d00c07800b001040c20110040c14241940c490125486d00240003d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 107305494 1250 107304244 107304251
    0xa05070e060a0806040305041d13061d0a0c0e0106140316021c05030f0c0418020711090c03070806190e060d0c0b04050f03030a080601080c0702040204060e120a0b0604 73
    0x5910390b50b4580100050600d00050b1040303800c2c103180103002500701d03010315120b127a020500e164a5a081d103003c5489110030100c940c0d00c29045480300c400401825200203900380b1b80301e4080113201c05c00c00c110b180c8240f01c2e518000c5242d1900700301e00441c0ca03042e00a5001c01c607902030004c1e04101c2c264140e82d000114200840344140e02d429069282c011500e150044070501454100e0380250070030080d51160400c51782c8010141e031215501e892502c1b5034082c1460160504026044250080c0e0191030000c0c8104003030070301681144002140410100e80500da055000010000325603444141540c0080040c0e850008101c1454580c0742400a02d00030300f030b408008a000910b8560750204504d0300c01e50002d0000b8030007511420300c0032182c0d015010300ca0003104004103003d02d03828008220740c1c111400c2d0360303030503404d071101c00044802d480054440b0550400c00d01c81c000c003681e518402040204001e440381c241100d4035134248800000780c3c0065000e103412405010010a412501c0e055100b4030407600003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 107306744 1250 107305494 107305501
    0x60f020f0304080a03081e15040f050c030c090607081209070807060912110a03030509040606050403112110020304060e0f060a0e0f01180605010512100f020f070501090c05030a05070e 80
    0x46851f450190705825040d1486024054070070509141d10100f00410b540c144440c010740c01d07420307050303440a4519281c00001080051024603010010b00384c5040010001d500e0f0995586400105d50044503034841414011010710144200410103030380205101c1001d000890f1600c100600100c03aa44540c00020260010740c0e4104071810240d4021040b0040c520480681c40303003401041c1d600031600c554010791400c0c0c030128505000d08262070071aa402481c40116204c01028440c0307401d10504a41d031002240300448200c1c0400703129903160040f003080016100c0c079060514100340c41c0b240802d540d0740d800c69465101d880f04041126940409000d001040160010890a15121280d00c5440b215441c1c150300045100340341c840c4c00300c42401508103100b41c0e600d803000c1180d603021080c2174031604d90007408504100301040d0456001142078042c018204103245001400070740c4100c1040310280d64030014142049600820300010304029002071100c04029500c13159112414040d8568007000c02000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 107307994 1250 107306744 107306761
    0x51504050d0c1706010801150b09190f090e1009050604030c021909060306050709080a290103050109030807080702030d05060a030c06020f010506061c1805030301060f020f0304080a0308 81
    0xb107a000b00015103a203d81d181c00c401120b51162003e0007584425401c00f20421403e030f14220000c0c06031000c0c8000580781102d0311080001444903011814a4101c1e5400d000400c0203001d0710070b000421032103501050460710007104d2824010041c0002c680c070b501c1c5c502420041503001038103651040e03150600d183c0c126a9400003820345370301c0144840b0003030760154003c101e11603e40c11a0b0f040b80c2c441d140a00070764523080e00907035070300d140c0e8091031207203510003030552012881400d006204022005009100456404140360340c04800340c10607543c07a03448525290401da404803450b6030190f994035150900e4104210001e44910419041346480358071140443d000780e503489100d000440d03011184894660703035080040d448005240105000307519100003d625814100c0171a2041c60360050000d030303201d40b4100701030000c1100c1d600e0410000c0ca4004000c0029004000840c081c0c403c40d00c4040c0030008030703003000340303412250340c426401500188420072400c4030010b0100380300c2d541030502e482d60780c0d500d81d503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 107309244 1250 107307994 107308013
    0x303051306020d0b03160503031222080c0d090b030a020d061716060503070801060503150a03060605031204030203070905180d0c03140703080610020c0306010803090a051504050d 78
    0xa000d4079140c800a040403840589a00030528160f042d001d4508900740c000c9141e954201c0c504c292038041d001040712094040b030000c0c1c45c691115040c0030324000c0a6031030403038100c01910408111880200001c00e2110f042c002c00c84803005010b01d2502811484c00c20140c0000d6002c003800002c2c40f95004034641c040182d0a0700b01c80094060b070340c4007501301e902001205a40b80207050070314500c20542c031030200d4018800d000f120b100780071948030781103a0f03440d0040c1150700380d000400c0e10340103000c005030750b0a05642d44c4071154000c50081001048044c1004105410050301440795110703c0010881000107880100d4040c00b00c602c801c02c00102542daa00303404507881c84001480b0241d01901e0b1642c16080e402501140c5003500a42d51400d080c2c80d4505440214880c1c41005004152607600041d500d1600102c2c3c440344000c544180c95450040b10003180c6413403401c0e04100c0703854001255004040c1000c00c15040100012120782c2842404079207900d55500c1240501c9001c0ea1a042018003031000441 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 107310494 1250 107309244 107309281
    0x51302070b04081b070803120709030f03110601050402130306180803190b300f010207030503060415120303020a0512040f060509030a022503050102040b0301031e0b04030305 76
    0x60007070761030b1a143c03011050b031112003403441c040a14000a07444a2001030900d040d10b007080c00035894145e146c840346d407050300020008010400c08480110000d070503011085005440794888a0402c00004241c42c00e0420580200c1e0003944184030b0710b81412048031601c400c031b0760420000161040c88000001c0005201500a8103584001080c41a01000090322810b049003a40c0c00b048444441001c0116100c000b40004440308410308000030f900f07000c800c10701e036010a8941100c01c8000d580390b00c0c509a8120203c2a408110f0220070010281014098040301616908088120904180c0b95001801484030068101030b80410011240c070b015804942000f6200a2182250714151400035170601062004880260400c3c000c111000000004d4901425144d000362a40302d8071181d070030885085454052490005403540000841e07070070310080015001110145c0d0b506d60450030961558542c00c50708107810b0303c0e0300e00f01d200820310144465803c241c1c10700c0e01207001d0311070001c0b80001e1400c40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 107311744 1250 107310494 107310503
    0xc01031e020c070e0c1e09030705100905090f07051e04030515011e0e0c071b03030201050106081b09010f210c09051503060f030f0a0506060a090b010905130207 70
    0xd5000300300c0c0000036150304613495040440010754617404c0d0303034000b80520070250715242c80b0f1903d03002c1049508400b800020a0142c200c40960366208009201d241030481e1401c0404d000325028000742c02c0c980c18141d40010a0104500981011400100148901c0c04071031070f5040025046070761607520004580c000c540000484220030200751845103c1d400070310400040c0000c0341c0d101041d45521204100444220320000e400d1a80e9229008545601002c07003152541c102d00149078120421800c004042c41c000e074000070b001e6040c26005860040090b14500da4161110a44101040058119201c00c0d000303282070040e15401c2102501c080c0c0c10040100e0300c154580040300407203601640800c248006658406070719a03a61010b00070428010300c5042401001003001070210304000880408650000d01116240c00c2c0000006041c01101c801c04c50f690340002d000d00c44540b61413070400303014004000080240e88088400078011006a1003900e0140c41c46074603542d11501c05070b05840342940c12 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 107312994 1250 107311744 107311747
    0x60f211407080607030c020105041109090c0d0f03020c01051206010e0f100f020106050a0e010e04111008011406030609040b0405070f090912020102030103021309111507030206180c01031e02 83
    0x19403210703c0c0c4a400032244040005d00e81400300d00c0702031050203004d00468001c080405440402d60603c0b02e2840001d010802521a030040d2908a03218a540c00740117038001c07019078011078400d1800906100900100c00d0400a040c001119014130b404000c0c0d41200090034030b40b02510300340000c075200b82c3c3e80003004c0751302141451310341d490940c204058507d40545903000300110760f104c01c00c00c00d40d0280741c029080000503890042c841084249000e070f0b0014010f10b0140350007091000010314154200c0c00c0e032000164804010001110150000c085000d02201d070360742146420008501e80541c02003010b00400d1014010500f80841171222002030302c1c0000f6403481c8242c0f5415003c0161501c00c070200c030000c2445614110a61041c402c1e64183e03a4001c00b084174044400040c0800f41072404800d440b865040c01c03105915941d03404c9280008026014002e480300120304003c0d0038640c0c0100401d403060040c10100c0401c5002144ec00b20648003401c002604c1d40d240c159443c14915000080c0b07400307034030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 107314244 1250 107312994 107312999
    0x402070503030a05010605040f060509060403020301090305120f0f0c071b140a09020c1f0f05040f03030b030c0105030c0714071403100605030318060702031f060f211407 74
    0x3000c80158400e07440d11005020a0366100000c51381480b45102d00d01036007004003024401c4611505c002c15040c54010500c41c285030f102c0e00081c1c21030b04403100031008200d0018058a44c10f002d2020580c0c4400740c42021142072030244a50100300170300416040c05c1c2e040c000303085030400c204a0f8501d05441e0807075080c1c000300c42d290051444084149a8078903c9040304220002d0b40d4881c81c02180d2100100d0009010605805001d0300410465100021031081c0c490458980c01d8581d84580341c402ca0007880080c0442507541005012110308004440c02500071400e8502507903041800c0700d401408804450380c0e81d0034281010030700d4081454000d050750086840004079a03089035908030442a04805030744a0860000c800c1c0c045803030600c51960150002d01c1302c07601c01c40e80c4a44200d030400000c0c2c0395924000b16507000a0821080c00e64044040c0c0d1140041080c0e04010310500c409415a0f04c001c040c42400c3c480f10710110680d000b42e8641100034904182c0820515221000101c4840310172690b2464 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 107315494 1250 107314244 107314253
    0x21c02040504110702030d0e0102100203070905040b040902090105150c01141602030a0f050307090810060303020f0c01200717010b030d0e010c12030e1204080709060e010e0402030c040207 82
    0x502070320072a88140c0c1852800c82c045005401220f0b40d460b4014001d241c0c08900c5034041d0349a4400c0c0405605500032214924480b0050380011485500c0030350f0b41e03510301414041004200c07034a04580343d00032407800ea1000c0050310b47c0c00d101d50640c0c50840d4034160f1080d001d8505105031140c1c01c150b50380d41d400d041800045001d11f05442c5d0080e41a091004600584c0d440100da9a0048076414000110200145227003d409280195003200c0030b8138110b50000c1d00c6d809180c0c50b00788601001c0210550302c0400700185a0306100400340850154041c11610384803000003003c50200b0038507040d0a480c1c110803a200d0413003c2064000038001030104010380b1009189003030080040720002070090052640394603845204030040c10039800140c455001040c529118242c0168604480780245541c80e82c814070307225020000228083c0801ca1000d0361135007403488031070a188184e03100030881401c2c040148a41070a800300b01d070560f442580c080c0f0715030741c0fa400000e20309100c0700300042c3c005100040709014003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 107316744 1250 107315494 107315497
    0xf030304030c05100c050307110613080a0309080624030f0a0804030b0a0b060403030f02010608060c071a0f041506030b1e06180c0c0114070801030506010608040c03120201021c02 78
    0x1100c013103800303403909001d40c141038529490503107000f0300356081000b0304400100f4121a100c445500130b09024240190b0680c0903160080640020306e295111007900010140c1c07200f440d00251090502902c21410820407007102c5400500c1d81c04541c020400040855403010860b90f0041030780b07401114410070300345c03e000e03c1c03d50180c0402d0343d920b108000007445516190180b000c140102610803840e00b407645d1011548620b001d003c040465481c4c110010700c1c40c130100903c501803269003089a0785c800f007074a82840100382180c103030034a480c05d00e0304011103100152015036010383c1095100c400c43e079581c00d906d4020006508014191030170203060000380c4244011852010100140081c41600e40310100840015141c040b05501020700b00014040e07200740010701018040741d0000307e07040312015040c03805001d045608030b000503542d500410500c403080001500510060500f0603950074076403500301c540c4905000241031000c15400c8508124800d604039022545140d050300310456480c80324002a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 107317994 1250 107316744 107316749
    0xf0706050306120706020307060902060d0507050306032406060913020307030219020313030206160c08010b1f02250513091b050109090905010603120c0614010506030a0b0f030304030c 80
    0x1030012880c3c15807180000140f18041d903045030019810600380b503079041d01030182c001040380c1010040c801d5401c044100e0251500881d42511001c4d16031500500741440c0c4003202000308500303000340181c0c2092144080d5403030b402900a54010750b0302c99100e8086180340d0820b20880d8000d6100100b08140c0640c19406425402d10032044007006401115003280e0b00d014100e010440046601d50405c010314143d07004044698000107603580012623034030b4048008105600040003a51900452490303890300c003443c4007003451032448a100200820b20000d6031014030100c0e280300f8091000459600e40032902d01640107090003444001d000c0b40034406580a0070b0819011110952111078101c0304c45152540b0405846045c0c2d907001758039203041e0280010b001c214405980d40d558030100030021410a8480e000c40d998107403a80b050152151401204403a141c0343e47c5610003e40000500440e03458408482e041048907202203055101c1d207000522442d46c0c0941c03164507201c0010000100b10743c0c61140c204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 107319244 1250 107317994 107317999
    0x909040311100203071b1103030c03030a06051207090b04090209070509130209100c1e0b011e060503045606030316062301050301050604150501110f0706050306 70
    0x240c90b008040000780e0000b590514040380380302205941009641943c0710f25540a003050440000e11140440d00f543e11041c00d840080e040001000300c2c1418a0244000901064450100078a441090341c4d8a9040e107016000449860340e81090a5075519000a60a250020120111401d00b060003501e554461168140241c458110080c0302014901c00da0740031103000340003070417603901d8144c044402d07003101172040345d81d5005114a041c1d100742d902e1074807000c644581d61002055043c200d102154150701d03075900401c11140c81043c0300701d9622000740ca0308203901010048400d0722001040c804848603c804110801344280c68100c9011500e079007807c42e008003200a039903c400800314881c00704045600c550542c0c0200410f0820341c40349007018001c0e90140c1c900045107440c05500780c40c0c030701180307402d41c1000c219000103004a2400b03201d184c0e040202194100b0441039140c616888040d0503210349818000041c403e4031000400703018100b41100f038041a02c0c042034030f940c0054216003082c0e035040d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 107320494 1250 107319244 107319253
    0x30412050c0108061f02100f020a1b02060405040f14240108130b09120a030b0405220605090a0204110a230301140d1b140f06040302040f020909040311 66
    0x44a55026250440c000d04d40a0007209100200310b4003007014280030440c000451040400d1201c03041e1140c07042d110810029440541c1d01d44800340300030301c24601030720b205410300e0042181500590700e04044400f11103080d24049845081c01c00300c0f02c01400070000ca4000380c00010100501038650544401c50300e001c15a2402c800c114810044850103800c032180c0d500094810035101c00714440095203503004c14000200c0c2e131a40300c240a01c10040c0c00c1030702d64401182e01d1f8503e4a415207054001c19500c01c0040c55803003c40b41d5051080c0032950000e03940605580c2e81c880100c1c810100900140d031500c0c3e000380007844076807031100e509503213a03205240c00400900d000380d141d07030981a0ba4100041c00380c0c40003e504e0850342800700c13000020f1410030310282d000001141310300004903041000c0c2c402c060440341ca50b514926080800c011600303140d09140c4111540c0c510784c02603517600c4040c0d400780c0350141c0b000a441c2000d80440e4000740301314524190310686c01e00800c001c05500154580408120000340d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 107321744 1250 107320494 107320513
    0xb01091508060103020411040f0308030708010e09190303020412080304020306100302100e0307050a03050303070f0224060a0302090c0c0d03050f0105040c18090c0e0d05060606130803041205 83
    0xc1981100d28000c0568681060b00108090300d0190000461800d05000661601d55112201508121030703502c111190303080071040144450f00319041500500f034004c086500741c0b4004008035200c0084c650130036070300720700d003e103000038180710b030b41a90301501030500c1c004003415460402c08032035002110220f10a214910014009000071807500d02100d90142c840140000c1c800c0041e41c030180c550300040e402d446094800125552421082c80040d8003810142d0355070f0428900050040410004000546d880b0944d40003013046051070801c0c800c5590003e1600e00d40380c1c84001401d1001f15400607500440310002c0c0021500603c0045c4030328000e2900311205a03003070503801d6068400803145218000000350042001e0300b0950800c40d001110740c6085c004d001020303010a80301240a812501e0110b5070b9506070a01c2e107420024848171103000325041584041541d07202940c0d0300c03004220300d0103041e001c1000d41040030b000d0300e4a00030708a1203090385d848940f5000e81d10004151000241c440b0320541c07020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 107322994 1250 107321744 107321771
    0x31f050d020a1703070c03030507060e01050c090105280e010215071205040311060903030a0614150c0708030d14010b031311011101060e01240203032206090b0109 71
    0x2500601a07028003075092a0746851150078144800141a40c1d5074007003003101700d0016102c03940b00380c091440b80e180c1076201c5241d0700703220301150f106014a41d40340e072500050113846959a400c0d5208060b0074a0301a0740e841f001d007603c044440841100c0303040c1013030b000568806a6000341054100d00020780c200e070a075190510440c0e1507914161540004070742d900303044130341d000016004280d019000c0c1c1080d200081e600c0c00ca503894a0012074450270903070800300034490900320501402c8010702c8221070485010460b2000111b03120040100d500d010740c00000c8c4207070b85501c2480141e00038003420041ea912511460b08400c0a0300098080400c1c0082200000c9003441c03916090720f001c0c50f420032113024a1009961050951862403042c00d0601c149200000e080e072809010f000042c18000c1002c8489514103103201076500040e24060f4011081641074102c290360000940380e1007078640010315000c00314181c0010034a01c204002405050410307081d001480100b030100c50403120750390784c20054040082c49 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 107324244 1250 107322994 107323009
    0x3092e050405340501050f04030228060306030203100504030201140a0f0c030c0c170405041514010809060f06010c060203040302030909010b1c110405060a09090f05070c0f1403031f05 80
    0x104035495541c1c103c080c0700382d52180d40940314240c200d0342003901e01034030ba400140010813a410160030107550124203030024400070f04000d009000d40d05007407041505590000381c5401340244601d554580e071b5000541418404d4024030002d00403800390f5862410840c4152000d44030310240c07400d1050510181540c80d501c03a101ea00790b126040c1da10000c0c0f11409139907030070000c0b213001d0070102002c4007400040313099541c521407603070527483c0301340c0b1011080c3c98a9040500b440d901c0402a050140c58000c205c50b40c800894020390220381c0c1058610569561401038482700314160b00070f0002c910100401003015000002000d092074122901106d60382c2e1385405d2240c9200320302c504500e8221082d1800c6040d0700700e0b0080100103040d06046402e1940342c0003ca00c85800003c100e0700043d80306001082000c6052061844035001e03da010711042c0780059025005020000700100001c140c40188000d0000c0042c4100a0415000a4079900e0500103002c102070013003805942a0301076445400074071884e140d074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 107325494 1250 107324244 107324323
    0x180607080a020334021b151e0d02040501020f0a03050d020c0a02040c030b0a0b0306100e06070b070305090f0304030c0b03270a030801050603092e050405 67
    0x5840c0d1180c1d96504901e1806900301400001204d240c070110280019400002c40c1020740c0040b100001c0c01142040c02841c01200403510515107030001d000640c40c0c0c0720b41ca00045610302c44074100751754646c0d455041200d11001c0703043c514850b00104254800540f181c0040044400036400c03101d50000450380e0544800030b00340018042082000320750039103001a0040c0c241c10603004160b8a034030040380c0214040c1c540c01050500000c0e07407004600038034030340303c0300e16006801c2c0428a00e04500d001000b0540060b504401d010030311200007410205943c130302e421505850751003e100c01540c03e023903034064003812050f1822243c40c000e144981d07060840000680c0c0031244c205000700c0c3d5851525240c070710180c0c0042c02d41d811000102945241c1c0100840d80802d0458000e002002241441d0031700610004060704400c0c440c002c10070a211039218006000000300304d04483d0420700c21140c48001e07004400002081503140c1c01d1004001c1031044c003141020b908541c130001d00f00a84210f1054401900300d05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 107326744 1250 107325494 107325497
    0x10203070c0308090705030321070518010806040626190f140c0d0c08160e0f0711011104090510051f020a0c080a0606080d02030702010509030309040c08180607 70
    0x141c0090000c82d2045003000d402c03411101c152681d968071200400d0841d44000003410003070314034000c00f11a000f00c0400090348100d0074500385041035003128200506240000c221410084600c0100e0500d44d40c0358009002400d580012a1010042807006501c0c0760541014003d140a07026100044104868600055560000303800c0c40070581c1e651401c1c003011240280c540c1602c81d03e09040780c00d850704419000d015000e0071030544010702d00b084491a016079400104820303e062001005000410344030a6040201c01000610980e5081000c40b0842c0e07000c00081200d43c205210950f002c940034004000380e8481040500455641e07410002c99030505101d1190082d0800e1420b10391540c2c2e2100c06242002c0c240b041d20102d442c142c039501315003c01c68000f0030281d0032051078030080005600c41d4000801c5d9003800f40c2500b0345c510030003039141d000b082c0b0080d05008000400044d50382d02401102c094140040003000300c510a141c00501000c400c40b49014211517003000002c2d03000000581a11800d1035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 107327994 1250 107326744 107326757
    0xd03150f09020304080405033a120c0e150904110f0f0a020c0613050f0301060b040603110417010c1101110304020d050c09040b16080c0d0e1009080405100201020307 72
    0x307101100300250302c0107000f40c2d141181400701003950755081c040b00c280040041c0461040c1440701c42c9a44000c085c80f42c00901c90031800758102d410542102c5002d0100050b0080022007114049040c2c0765600000c2c030b40d07a404000c0c091008241c41001d00900f4100c0c60035181000000c00030a01094203116290700c943c1484014807180c1c42e010740c500300400e40102103205076854100128007107010347e004214880e8109400000602c058103103828507148142c4105c0c002d011041c500b131074078007861040d80101400c051700ca07015001081886030480700100180d170041034207090048001360007006617004020020f401c40c01e02c0788056005010701d2040c202c5500d1580e24507101c0b58208183d10900d280129620301a4194050f1140d0781c17064494440e03070082c5009400c40c5820380b030f54a0340c2804440d00400303111201003484590110f00c405c0e01c030b010902a000098001110708810f20b044165a00c50850f14144a800010407070400064021a43c090f50144050551a10164240d000803183c50000411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 107329244 1250 107327994 107327999
    0x8070302040209130609020307030e0c0a1703130801050a05090a0c0612060308070c030209060406030c050607050102040308040801020712050f1c0e0d02011e05010609060507230d03150f 81
    0x3000c0c2e00400002100034015403c0e500104e5180b0261025548443c3c2c00079408030402c001940c060060600c1040300002511352400c4850004481c05900e01440500c800b40d1074244035020810000c41d410724104800d0031903050313a16800c040c041e000072200107082504081c042440c9410005403c0707900c641c00414540d0141c14110300304c6214176140c03002e000558036400000042901c5030000c090341c0f80540070458030f6509600500201d210060401030050389800d4040000c42d4a03981043c00b500c0080300d00d196103160508080780a4040c035000504481e0300060300184003041580185a001c2c4203090501c500c60300a08282d8480c01502c484204c034110030048055941080031179125103814230200080e00d290600800f502c1c2150f00e04074480541c0d0749400401d4029000740c10800c1c0c81a504070240090760501000070442005449020140540494034100700003050303d0844242e4900010701a5504c09488a203031f40341260001c140202e8070b014009207041c50206050f80645100e01d07101304d011351 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 107330494 1250 107329244 107329249
    0x503040c09050702030706021605150910020f0f040608250e060306010309050d0302040504060e0c070f03050415121b09050d050f01060b07170a0f030b01030e0f010f0e01050108070302 80
    0x21005100ea41180006c00030400018410b10282055400310803028103011031910342149044c08140c05051006002c070100408444009a04000440c2440c0c000d48c0b566108216046035019030041d00021840101e0082141503012110358404c00014a40c00031002018a84113140801c030200c0e1400110750030b941c944d0508000000316000401032400103602e4455854030381c00c08d01c03103c080c0b5002070b800140800961a003406400042c200361805034641d401c00301442c0843d1b00c02d84500801034000415404113141c0540e0507034000301400e20503200c5420940b0b80040c10090016810b21009103070045402c1c0c00413102c60b02d610350880315100d000c0c685003400c04124000900c2e0400311190f10451900c000d01030381c207005401c01402441c8209880304441c1c80d040c1ca1014410309482a23400062040340700f282c0c2c2c00000d4a680d404a801c0000b0402c6481004074003a158000c155030182c41458248004c500b0154065050710800d100304124800c03c007001d02e42a500b085c410704000340d01044080c805031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 107331744 1250 107330494 107330501
    0x70e04080304030c1b0801020307020c0a080606090709080703080306041b09210501150503120304080307030b0f09130c1a0304140717010603061104050d0b0a06091409010c0503040c09 80
    0x503030050a0102c4c9400c1217801c2d2100204281c0c029841c245d40100901c90b440d07030100702c1c090a00750111140e010850a01040c0d50351610000e2110f0b2160750b080c004100c0c141cac0221081005449498240d40358203440c0d003441c0000390320a58089000c1c40c6040c41c1c1c08454400c00c840141503422a40d54000300903d8201e861400480000107a040c130040c40b0b2414000072424801e1404100b41076090141581c07030b181c01c0604003406010301203403040c0304108000001d070002c411603510443d6828001040c10340d10f401b181098001c0c550040d0861141418012000c1005540380b442c50310030001c1006007501c03040c14220807024a581c4844120062012800203800440d041c000031041c20b0803500b0301680c0c2c001e60080b003a00c0b44422091650345100a2050001c42e00610040d000c2d0210441e182c07511b08400316115001c6504040d100301c807803c000c14070381d49480d040708c00103140c80402070041001c1d101d80210040000d880c0340406600c0c125844010038012801c0e40c1c80769400040c00015140b43c03c149101a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 107332994 1250 107331744 107331767
    0x2a0f090702010b0a08010515060a0503010603020c100e01020909060402041508090c0415292d180f040903050702010c0309030b0703020304050c011409040b04020d0e010b03070e0408030403 82
    0x81d035490351000602621882d401307038000c10300d0500103e000d00f01411041c1c0008041a0707641e02541e8108201c40c50b145e0003c044904444091030f00583d1255001c19503403c004034118100300140c203080c00b50850755015000740800e4031b0100c032002019244c03001000124440d900c00c4008540d00d60b645808110700691039960b1052241054461800e0000002400c031040300041d048060005400dd10610220101d44000300d005c0c00380c03152502a01005030402130180e40f44152407191341c80b0505c1d204022043c204480306d102c1d020180e4a4030142200c41800454508e0420300804400e83c01e8107592078640540f485a50305a241c0c2c900d0070b900e98004682c9454038210950510401c1032002002500004005102d2646560016268281481c00314108400a074010307041003000311841d00d9070881030003240d003241c008407000205c0d101d1000100c4c000c1d0080888006243e0320300b21040005a030306400c01c100c400c4c030407800d0328000c0340c50791801c034801c1b507040d02c0c05010400c1c2440040c00203405081150321 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 107334244 1250 107332994 107332997
    0xa0c0507060e0607140c0a020d051005070909150b0307030b030a080304050d0908010e1c020c0d0804051212040905041a040302010b0306010609060c060f02070807052a0f0907 76
    0x58090903859040688688903901100c2d41e00000030007101550100c210302e40520710683c25460989502c510594600c20003402a20800300d500444040042c1004003040030301003010107000310b241c01d50002e01050300034854480242c0c2032064011420700c01c0301c601e02c1962400d034140d908507104e01800310000d01070620b00ea501407080440c803401168055000c0c41c031071841703074004150281e8035010003488103031a80d0080d08107070b0400d02d400388412008181d407420201a0704076070030030b01c41001040b880c000c41c0354101074019444d03458101c03c1c407550500800607148113880c1582c074100c0d2241c0b5141d44d050707032290881d20150180b100307014103245a00090303002809112504801d1084d0503402c5806441a241180503070740d1000808045e0a06000d11070040c0601c1c14403c00041c5004005004079500800041041e83d8444c41c103510080319a042d41e55032500300c0065a241d60b03082c5031450340e801c10030501360710314180e501c246820080d4003000280e5221020b002c03156480f404500740169a40c0240c139550 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 107335494 1250 107334244 107334247
    0x5130e040206070b1519080a0209100f060c14150a020f04030206040605030412051801110109080301180b060405060a030507020a020402030901060603060506030403050403020d0c03080310140103140a0c05 89
    0x80c0450a0b01081c0317401744d4000c03015000140104410001380c2050500614801c20b054003007000000e10100c0c207071000c2ca40550b00e0800c19a0b03240b00c250b0075140241c20140400710b00e440c0c0401da542d4098040d11706240b140751000004441d03001069070310441c000841007405081800a1000240b41d006080c4000b01034ac4170038103144e140d41c0040da01e50042e4005900095001c003c020511504007001c2c0d179040c540d402c165141c00e110f070201c080c109480d407038150706104450741480c009072825801190380070340226209459513100d1402c0440d0f00a58055490410b040c000c01c1046403801004850444a005100718035054906800b40c02038400104660154010f1049003005a211400110705c9030001000010701d06081a401804680e925000980079a1041c410400020342040c05c0703d0940e40c04580401c0340c4440340c03500e403100440b113800051005101000340001c8400448104041e901001035a101d100440001101156a07196a00c558204018046450f10303c89034000058401e0910301035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 107336744 1250 107335494 107335507
    0x2100e0606101211030a020304050c0f0f0402130305030a020f0706090b0921010504080a12021201050409170c01060302010306120c0905090a0c0b03070e1507060b0402071e05060705130e040206 84
    0x4d049074004542e03421415400004000030000144444120b4140840340801c902c2c4402c80400d110021552a0300e01886d400a03e0b1915441d000e0041c000550f806000c4030740d18048800003c3d15041144100c2c80315108041002c070f003240c0100c205500380d865111400e404c05a14004010524030b95918400760010741407500e007441c036003e01805200e240282807650303984e90700d514010000711030842100c41d05817051007600c02581001072503d045500440e0f0205100149040c603082500e030386181b8400c01200050312829084040d040072048a0003600d0410031140d84484c4d0081e45040f80000400c8500640001d0004100c02da001580001c0c1d00022200200705507603402200d0a15500016030400010040000103644440c400000060690b82105808040300c2400800e00800500905007034882080511544490307060302c030403641103026080f60340903100ea0fa07107003400c206a0507a114022000024003007806101114104504140e81e0040c542c80c010030314482e001c016004913800764041188 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 107337994 1250 107336744 107336771
    0x30903030b0306071809060503071202030312070801030b060406050d03120e03070507080609160e0c07080301090b01021005070c20150c10090c0b07060b0301060602100e06061012 78
    0xfa200d03c425440750780c040580c0f902d041680507400e0384200c4415007044401d0001e5100401e070003044070075a264401c081d82d0741d807000900318015840b09010003881001048000f80e400440f140c101c1340510280038142d1103540501081c1c1d141806019001002004c410000902c80c90030940c4030035001a0000e0102c820942407411039000400642e29580040000d00000b030048c00304982006030600200f0070691403031044c01c1d840d0014880da403104144100011040c1542804980307105500c100030a50340d41c5c4444d120b1000300440f00c010350061187c0c50220541c00124402d1034001c00b07154580f9030f949425650703899a180040103001c43d100030031044850864954032a644101d441d00059151107003900a20140741602d01041301d0b50090814407800c0c08038101600c1d001c1512a101788003a5650298140032007c1c100d92001a80c056281403400240c241d4080b83c010341d416006041805090764240304181e4546050f00c5a551099012508514107030049659041c041340337540000c10109200b100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 107339244 1250 107337994 107338003
    0xc080913180203100c0c02090417070606091b05030112060902030d1112160b070e030a03030c030c05040b12131a01030b011508060907020c1f140301031101030903030b03 74
    0x1c110500c11101c01403401146400d02c4410100030b8010020800e4202c02e500c0200b0203444981d0107030280c04803401140c240042030004400200205840e10780c1d6010324030b0010300808541c0700f0b00444501e040c2c500700e04071b80300640d900c512040030380c0e50070708507420503544c0120240c03004421241c003961540340c05d005881c180300d5004044c245448462034400080c0a040c2000320407928030000303210805c802c2405c50400402040e1140d08283c1e8a02c0d190759039130090710207003800540c0c035a0610502e4884030405515411034519000d9960782030141c5940140c0540325401103001d0001d01c0c0b8800d1242031aa44206d05100c1d902c80007240d2903240442583d2105200410000300005079422000010301c00d210081c640ba0340140b1600e03c8840d10800e100c40c0007051420081e100e036110703070f5125000c6603100c2e1003000a451000001084050f001001400c4800500501d00107500803401c4003003503100d000001d00c141c03070480c0c0e04225280d418000c1600110014420300b0710440902d0f90700c0c0c01006254030200f2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 107340494 1250 107339244 107339261
    0xb0c1f14010b040906060c03080703051b0c07030c140a090e0307230706050c030307032c011d07030302100203040f0f0303020304050f1603020f0303122508070c080913 73
    0x2541c1d1103042130030030401e9035030720f40141060061001c10200040e60280d8070315800b40a074178001415441b003909941f84020311003981d8034240e10200d0f203071052400228280085a01c00c18900b08240d035102d81900960290103c8079600c0f0034804020450101c0c9504012811048001030b80d16219080e42d40c02c00d045440d800510007001c001c00c0c000f4080c20100075060240010303040840c20900c035010105d0740d030b101c010061000c05485200710760695440060140c818909000d101244100c144c03c01c80c02881e082c4101403040203079008242d4410030209d1110150f070b030591301400c0301619140784003010754005403080300c40041c220250800f04820000a2030320601c00ea40140c1d69080030300780f043c03904c0ca02e41c2d10043c240d00640010314421801c54101412603605458040130445400002411400b8029a071108461100c0400440005501d402ca10002d8640c02072204131290450031505038100b1226000400d00581c451004614900c01420011030010714050b0813038800c0080800303852110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 107341744 1250 107340494 107340509
    0x501030c0306050a0501050607080c010e1905060f0907230301020703030b01030c0e0307090903020f0f0a0c08010c0503010e06030313080c010905041b1107090501120c0b0c1f1401 78
    0x100060041003014043c2c0360b0498031120060055504210004e0b41c0b904c40c0481c0100a40400108005d54140a41000242c8903449040e00c44030703a031010070f0300c622801c0350300c0c111454003c440c00207181c8042918014083d01d0b18200602c480743c00c046040f07661003111034507000b204215a40008203035400b40000d00038203100303a401203207581404d0009000d8a008400101c284092a600c0800c00c4e20009444421900303c0440412096114201a41050101c50302e0a2041c00381c4000c0005c80b600024030031400301c3c0300e0f0622408407560350907002d0880d10410f001200180c1c1c100010841c04880300d041036040b070002001d8928004242410310f40107503040e44845440e41009048203403644e00240201c005200684043c001d0340305100203201801c84c079080d40010701c11a0318400c011400304000c0360005e030100f460208440c0d43c40b68404008104000d8049641450710031700031034511205803e503218440d150b0b0041191b40c40001e2144020418443d800705460b40c0e4801c01008803546401080c000e2a0b807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 107342994 1250 107341744 107341763
    0x7080702101803031d030d0c03180504240611030a0315050414061003020408190303181a070c1124040605040512010509060f0903070804140a05030c010507061509050103 74
    0x70102c5105c0344a1240314403074404d4005c150340f1144903811107441508940d00d40350005078001d0f1480120980b44964003e00d80003454441a00a0403044124130740c248040c400044845954a001c2294441040382c0002c41d190030620454000034000e2301303c2c403406400100d051604030b48480100d0704448001c40100680790200c0c003448054107103283c0b0142c030501e803490294600303410b000350b1030f0b13035035010081850f08180045420810700d4440e03800442015000e805c0e010340c0150300c4c208501003243e0440e10103c480c45210100f00c0b05030089800b2550507a012000918002d80d14040001da00c00c18002044c2e0340030007606002100711080300910207481540ca6191f260350030302080c80301200c900d400e980c2242c0c1c034103801d00c40e080500150b1541e205040340c0c2c40180327680d03030030580d0350842c021080000c3c8504008a0b000c10402070b41e803124081c07900e003a03a07a90300150b80c8030708141c0c0d075104860400340070400c104200008200031350810305200d030540040c02e40d484d03640c8900000700c42d000d0b40203540319030300f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 107344244 1250 107342994 107343017
    0x503070b07030902010906050405102a050703030906050316081f1d100b03062202040902090906031204171501080319020313091802090f0114060708070210180303 71
    0x2000a1500040d07c1d5516240381024100000304640c0417045e03149005004003011948075001e06141d0907400e42602109903041e4030b200c1e1420319034900890200300c004ca184550041051f512400070f69200745d8000040b003c944041000a8850007009080011240d08145090544070070740744d1400d0046c480310b081c245c1d80244000c101119281e000d03041c40c01020391003204202c1c038080a815290000301c1200e40390b10751017456840140741790314000b070f070100180007140000700030000c0c0d801f034400c1e4201600c0c5481079503501010541c48060f15400810080c806001c00d0120b02103901d910303201841031404540c1252041340c50300ea0508401d078002c80017a44002801c0c40e1206140300c102000b008540025820030351098042d03004040a409000e00281d52440d040e421440d284000000c03150300a840300340c00303040151003050040c109000d200c4640c03100d48056100c1d130074030711304032442560016007242c00c0420a0342003000d5076085520700d0003088810148600824480440240154131a0322039844004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 107345494 1250 107344244 107344247
    0x121608060c461218020f010504030f0c15020c01081506040503070902030a0b011d0f0402190201050603190b01030f05010b100309020109050108010501020d081f03030e03150c160503070b0703090201 86
    0xa0322948110f00303803420101050a601c01d4002d207a01116030443e0709500314041140102e40502403a40b01070211001c00b20200c05105080b0710b120152039100c9904224035601800a80c2d981c04040c020500181d1924000350040d640390f03009000500000313105600e0315a80e89c000a00c0c2c0b54845e040018401e5000007480980c0c4900d1041d140011b4080c00c0aa40b1181c5800c101c0311683d9180b0a52406502d0140e04c0c1112582c0b240d0407620515800c545500f28a00c0500000303008000c1200d180d80280301d03600c90104054010402c0c46000c0742e10549000c10382c2c3c2169104080b012541104403040c5d03484884214042ea918030160081e2003060354002140340c001c0c00014804ea4169001c1d03414441008010f200c5644d0114091040010905200c1c9041d00d0f40d41c41604d81e45407034103560420060504002c0100343d405590400301c450100c1c22941c2c03500010202c0c0d0400c40003601c0707400107170700100100f00e80450054090030300c0ca8002c0b0141d904107401c0c0e4071840c410075030455104000982e20302c2001c0440d07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 107346744 1250 107345494 107345507
    0xd0e03090409211704060209031203041407230d020307120510051003020d060b030c12030a03060f050a0302011808030409050618040215070c05121608060c46 69
    0x4181d10300d00324140340d04e00f80300800d4090000d48040d022a80002e40c2c04240e4078108004c0e00103880507803460b5924641418140484004403c603440b050140341c04c00210b0248036140901d182040d00070b202c074020800c5041188001180c03030200d8260003090710000e1802042c40104890600900180040e412048901021038800804c0e903c43c0c959074000a102584034540312024a59000340d000402074480800a858030300f202d05165881105402c0c1051685004806800790350701c291018025103490340144419408140500c5401142c040e4040002d584141039440d14900e52019280305280c071140d48500b554455001901015160030034020241040c178552400360345401006e010a04295000801e203a149200460702d804001c5100c1092001c0d011140c40100f030010100d03103510300a00c500e10340f0317100d12802000c0800c0c1c0c01240025540340c081007031845000b10a03001450401854101000d0b41e12200c84124050303208041d01132061201c0c4446902320f540d0081c4c0c1001c6a11015006026 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 107347994 1250 107346744 107346803
    0x70b12060108071b0f0f060c050406020c0301050919080f0c06151207030b0a020903030309060a060806011802030a020f070302010f050603030406120b0303091503010305160602030d0e03090409 84
    0xc0069815844d150301c112004240300b01607000010070760041ca10309000341a09040030001e41039500d0084124030454206004000f203c1b2690203036510081035004150890302d045a0902540d0020500d140c41c2050948001401c18801c421443c01c200030350103002d00c903030400810503040c0d034040024000c950a41d07171100142ea0204890b0a002c00c1c0c1054500b07074540d4460310000f8448074240010400c2900c0d26010b440c080341000d01269141e01e0480d1900f5951a400d650b89004a803600c000441e0301203010444034142ca001400c0c02d24407208104c100d200942c0f0060085054a90a1101d915008a50002441071741d0080c0d0021600002d0200100c0c101c1d24081c0c4000d11950042004100c001d81001c4103a00080d440c41d0b00040d144014000b0a05611880075400e500045512172201001c1980001d035040e60301800845501001002003040100010300030000075910601405c000c00030350381c104003540c0d1034402c16642480940c0010605a41c4410421540104408040d41d007490601011200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 107349244 1250 107347994 107347997
    0x50f03040f02180103050327030114100512281a04020405010b040510050d15060908060a0b0d021c02060307020a11030304030c03030804061811180702071502070b1206010807 76
    0x13549103994880d5684212090300f05003007950300d004e8820702c102c95090900000c0141c02802114420f03a100c07052220100ca04c1070819181c43c101140e01e051807102401d0000d40d4030020250391900340300560b480781c030030480c43c141c0c074044000300b50000d00c00000c200907584038840484441e080c80d104100c19504160054040d80106010801240e034a92040381030350480c07410702c4c41d500c42d02000c81c3c0f00034183c0c12001c013420400c1250002075480d0302c402c4810403900760000391a420b44600c41c0c01c030309440c0d0f10350383d8039030009184855030003502d002d10352480140500303a208a5015182c0e8003050403070b08110380346005608034a10307500a020440928840c0c80350110040e510300340c1155900e0741c040306640000780c2040307150800035040040c1c1c2d51220040741034038100044000200e2810700081e200d9404540d01480034489003031500d406180e000e0f405055642c028004060804859091502c000903840c000c6220b84840040c1e103266600c0144100b245401c0010458a401b030000340140d94043c15110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 107350494 1250 107349244 107349289
    0xc0305090606060d15080d1814060f0c07090b100801030b0a020c21040504060b070b0c0a12090803060109080d0c150e0f060f13080405040c050f03040f02 67
    0x1550310007069880c0e12000407900c00d034440054031107840062240714001c42c00d00d01141000308074020001840c800f09642d03607480440e10603020182201d085242d01c00c5111500c200790103500f017031504101030710790300208038142d41c20301c41901505440c0032000c1e800580384039aa02c00b00d0210b0b08004010035442e1495007068144c0354550760303451034241401441018015030208c0c02d80301001c030521600e1840d072040031200e40e1464541100c4451039000f07105052045241c10360008007030010b041031350a06500000e96509030340d1552802d50072a03022003904020450b4200a8019035115032250038090350154110340d80ba0319003074001402001260b04407102c0c50344000c0040b400c0e2980038011200542c1d001c1c0d401203145440604039005451410211030841c01019160521902c0014059101d94003090300c1c80040e0301e0b0300360201c45030000c048010781050ba0800003405241016000710b0388028091400303901d0103e1008546045400603542201c01c0c1c06060741c20f00961074a540d00008280d040c10300710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 107351744 1250 107350494 107350501
    0xd050703120f06030212151b12040506010e0a050c19030e0a110a090204030f11150a020105091b010e0405041506081e0c01080601110715020102040501020f390301090b04060c0305 78
    0x1f0742d0304a00624001c204140300d2442a203020a010682d0440047d8000c0601d0314141494069142c40c82401032000c910808000600a01e0b40e902400b809100300000c1c0c81d140821310385442c44a407290100400a150700c40c001103503550420080d01003600d00030900042d00c01c0d1314104103e00103140780e015034075440c014842800232030100798840704442d91001e0f4080c07003840c010780410552245c1c02290710a0440108044515a806411287c420700e445130aa404183e00c021000d008006134000c941d0000342c140c03034113881d241442c1d8050b03500300d805a03091000400416110780f00759035940d00902e40541102d032146200f030120081c412100400031002d1b00160707004000080007039200821041c1044a048004030084506200003000380503903200440030342c40404006400303075005100b1180184640b044000106601242d07505031040203c55141c1911030107008100149010040402e03140c4080303c180c0d1181c1e409101359000c15101e404101c0203881c207414405c040300e0654441006041c20403081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 107352994 1250 107351744 107351773
    0xb0d0e0f0606061309090803071b12030903020f0601080309030601060302071a0604021b03090109060c020a03110105130f09180c05100e130506030606030f0d050703120f06030212 78
    0x203140e1100e810382d480fa0316065252182c6040d22015404039020510340b04442c01409424401544699200d4440c035505502031554440b0002800e90080e00b40180084101030b001c2c13181e0407201003075000f031044544c040fa02201e600c0c1059020303806085580e1000400f16a1403c05102d400d00604e400d0a01b10309149854644540c602005240d16400c500c83d0000144160b4441d0b040e10b603400740c0c0d403411142d007a0185049540d01c1d4040b83c90741c0d002c903288a2000075410310030002072820990203042040c41a2035592100285128044400d052090900441e500d4522000c2440300811840c240420b800c0d00e00001441150904146150302c44182032088c000701c0c4140080e902160b41c141c50422103c20030000445c0c00100700d91115900c10040c1002100005140d0040c900604040b4142c0300d55440700010582c0c0d403205041e80d80403a41001c512030034010700550141c000e10f802401d0040d40c40d402004903000310f0b13502203119440199242000e100b9400c040068000c80c0744400d000300000d08a0441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 107354244 1250 107352994 107353003
    0x4080f0d020c060f04030609060f29040207020307030803070f0801050a120b100b0c0f1009030915020c0402070501020c06010504110405090402061306080a050c030f0105060c12040b0d0e0f 82
    0xb116405881e0005036120b1007201e40080380c00071500b00c502005400a0340c034000380a000000781d030740c0031141400d19403905541004120300d080300703050307401c81c0b030455440c402c1c00044d4108c1e8030280c0e4540125031001003c1541c4074025403041c86203a81d00307030340000f2180014000c40010b800841c002d81002006100d1640c8100e8000e071607641141d1402d840e42d0f03a041420b14031000580040f10a000040f41a900c50707003000561028007180b80c0700f0385103140c454400e00707012905400e102a001036044101005220300440c2c907078060b01c2e450b105980e00710000c24080f5040e80d008040840f500c2e03600251000964030248103041c05401e04450a02084454801f044203e010303d0044601c0340420f08045011980c42100b02c1b150581151150b00c0c0081d5180f030003400b624070844441545504080c0051a4105404200d03441a0178400d40610b00d64200030612000d60003c5040304060301ca042e00744128031a40c20003030300c0209020300c030159031105d00107050310a0360341701c1c00100d000d5408221441080840401c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 107355494 1250 107354244 107354263
    0x2061f061d03030a030f0b0405070507080a020c0603070e09130308010b09060d06060903032d03020c010e0109060e1e0c010e130f05071b03080c030604061a04080f0d02 73
    0x207051401020155410509038003803030300150303040c07000048240001e9010340001c540942c40800c204490011070041c031081e40c400712904400100100000740000d1000c80180500380b03003070310469011040641c0881c0c4554416907000b8041a150030382c0c1c40403441e01440d015844a640000061a00c0309990050b0060006025980d0301141c0410300c003c0035100c21054608018054034140301c05551140c001e4082c03585400b00380d0004800c402c0b02044000388041c60070721440c4c2d1000c024056088168110001e400006d180d184039501c450491214800c240604c46104e8060403000039601c1801e1281440c024849944e83da04580c5c00058000c814004500c00d04c60748800c3c20000481228440007840c180600520316005501e800030195a0403e02d0303014071b2188220340c90b000703441c0c512240268100e0010160080006450f10001401c4030805009140c0101005e0004103d003070306d4404040c40101c02e00c4460011107400320301040a05800c115a80000c00b0a001401441d058510300070346441800c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 107356744 1250 107355494 107355497
    0x271112041112030f03040c0b0f090405060f09091c02010b01021903020a0b010303090906060e0303031306021e07020f0901050901120807060c02160f05060d11040308030702030a02061f06 81
    0x1650610720b48641c41d403024048601c0382500d9644040e400d2400d804d400680b070aa0303503009115004903022552808652220920500c51800c0c036030044100005000004c0010ba0089051381401c0219114900b68a010744031180c003401ca0400410781589043c0c500350400c030b08582c14409080c44076600800c850003d405940c0b0316141956040c141685800325405000380410302041c000420b040e848011007066511442051003a030350340e40c0040707520070140c4ac1c040d0b9054100300b0100b0660b5184203000d00324140b1541c0058188481c0210320090b0031004000b0b11051075000500c44114a032100303809000782c01c00c485140d02541060041103991b541401400049121040344005000c508010b40360780562005d800c1c45000b811400c020b444041c0c0e54214440f80038102c1006c24084840e00d5083d06440c0b0140141e42003018003132007103029140305401210055020880030001c00d0000e001188560180d800940d030359016000020700d0050001c00130145400405071031030001c041d42800384120b941e01e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 107357994 1250 107356744 107356763
    0x4061d0a080a0b0411030307152a0f39060b040f0905100e1f0608010903020601050117070207060e0415081f06080309061327111204 58
    0x94045000482507800c454503510070380d8112010052070f401e41500c0b5a00c929a4001c0140c089014135540c0c0c001c44200800d42d5005510114514100b40e00190080000c82c1880e0950080c2d800c2940d100303400c107022a4001400b21061140c3c0c1c64000d0040300c40750407103101c071011440c030011441995103038101c901c01202c00d81152070014030150b5000032031041e000420030801d0f41c1c1451070103030050001b008200c8160140ca014040d40a003103200e0450745000740406410400800e059100751495445142e032601d81d0f1320000801c13019004d100d40100184250000c1c14654148000541000613414900746000521010800066404640201102c2250030061410a03170500014007034007004140602d101200700740001d400f6000600d021440741c0c41010548101801c000385c2050300c0d401d0103404880d500800094100d03003403810040203040c100c00c0c03410b10415140c0c0e003003060002007001101a143c0459940000488441c4618507072139150944503440c044244105280640c0020030180003460b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 107359244 1250 107357994 107358047
    0x30e0310050a0b011403040b071404091b0801081908160f0b04020114120f06030a1b050a090b030c040504080d02041211030a0b040b07120c1110020406 66
    0x24204003003141400340c400180058608554108001c0400b100701a0008194034024041903004604070380c05542c00c00d4841c0c410b551a00c0c800c1e646d41c450075112200034001003000040c0350120b845000801381600320200602107101500521995042e0801901d50f08601c42040820458a0544003100d90000351961030340780b00b42d00030103036070b0348280041c088030b504d40342c40d404205038032030b416104a100740c9a105410b0b24000f0294407a01804420148d41d1061001182d555598403040c183d0100004080307881d01e009540c1c1b11382502e0320030704188100c2c5000d10707000d12041c980005440040d0140c01070401c42c8000d4840000c1d47c0d0310500910b0307409140c2c1c9002107024020b81c0d008036400805e454000355580c564514901000b0322a05200b07031809000820218030342e1801085201146400c074886501c2c0341c41d281c85025070820040c10043c284208849400c2e1290303894080c044500d6002e072210f404402203a11310500b030441c00112071003214030400041c4120f81c3c1001d0f603103c40f40c4150159141c0d541 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 107360494 1250 107359244 107359249
    0x31101020405150904050109061202012304030b040b0106030903090504050a060803030112150e0606011103090319150509030f0903070e01030605012903070c050c13021b19030e 77
    0x210326041aa0085038501d102074160340c08000604c0c0e60041a281008981ea980140d5011503d50340584443d4450031000503002d0342c460809842c03074680d2801d141282d52484044104941e1091b07001711031031505e5400f000140300c0c0c0030721018010300c0142024020399500707990082840c403185c020944503980d5080424400d150584c05030001c0d006c1d407400c40344c0da03584580c29035030a070b05045411522440c1408119000301682c0c02800400070315170000b0701d000d8661100549400e111207103c04c2c8607201c184188815a9010016881541c08420443c0c6001c020350412078440164042008030013410318050241d100320002c01c0300c503443c40380801180c54030340d00030020341800d22562103d0f0f40100703440004000c1c031001d0b502c001c0c102c0d02c689a4484609450b034501c0080c1e41c0242d030581100d00418000910440c0c003e014240c410342c1b1030750550306888070410010300c41914051071498119400300d000e11003036182143ca4440540b110009001e02008a1381188075503520700001030400620100884d0300f074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 107361744 1250 107360494 107360497
    0x14190b0103061d060702011508010b06030c0702061c020304020f0108070807140c011a030f070311131d0c0102060a0605060301150219080c070909031727010207050d091203110102 78
    0x110704207466040c00c14080084c06003241541503060023400420002d043d0105110311508000c025041c00e045640c0c5071200300c2503410444003071343c200300100250001034404000c00c0c40d1250f003110005840f070a06006110141e03001400031818400380034140405141c011564a038024100d2902d100140c5810300301601c030b4019200400b8071507092442007051114103180311700c0e0142d010f0f41159410504640d0040d52180d0501c00904040180c808a2100382000b03a10b01c0d00268440e20702140f61540300394540005001a4050704c01c0342c2000e40000a40e4ac1d050051a410419400049c0030f40380c01d01000489070301c818400d903071031503041801c040c0320680240300e058902800052640c1c00c81103070307040a018a82c042e4001e03001d207004450380841d06d220360340700f40502c96400d07685404011714101003103516420050414110a500703007808240700348a10800700d40c2c0280201c000f58480400e40b5205281000080c0c0b0313241030091702e981c10302c14100364080c0c1c0300310300ba0035141c980c440b21440c00728140207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 107362994 1250 107361744 107361791
    0xb060c010906180206070f020301320c03160c0606031e0c09020f09010305090a0506280c0f05070f051f1107020607120c0c0f0815040512090103150314190b010306 71
    0x8202524009440c42e0124420be1140c140d1481140b542d5802d41c3c000c2036200448403061818600031800d2201e6100301e00348141c00307116041c0020340548030b841d1a03180c003042c3e5003242e420351600c0d44042c007048071a242601c014900c1010030b609050b035021014a0501910704094105582c920014a905108000c803008240d0880c0943c2d00360304180c42d55034600c140750542040d00103e48101010000203d2007202c0e4062803d90b684154245136480484080d80021030580e81c4d070509000c0d00000c958240441c44111b100813500c10a80f19a1418613426140c40400c80c0504c00030600c0751101585610086600699020603c079000240300030080e198000821805070001d2000c407004607010f18071f030754a081903446000c01c4030941030700c402c0380d070404560449009010380c0000d81544001c206000c00741c0408a014180465180300c640d40e14444591582d205030380003540400b0b0039a00e61028490100c00f1019017120441005007519008220304040c44001e00480c0e6450103003c00e2410b00182030708 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 107364244 1250 107362994 107363021
    0x90409050120090d0305030901090b01140102010606080f070c1505070503040b010909021815151e0f16060204050603180c120a0b0a0b060c010906180206070f020301 72
    0x941480c10514000c00901c10601200c112280801c10000d04030801da07603141d1001001c01502c405180c3e405c5030300da04080c00c0e548140d901d603107001001641d2903200078042c20f0001c960b4101282c0d4280020300f96085580b084040c0002c0101b80048048034414035503226100d8185100035081c945414001841441c6003546061302d880c080c089041e600200442c000e50280c512038030503036210702c451000c07a001c9810080d40840c0e860b0640261b040041ea01c0d41c0d0000443c01117084403d041e10101c1ca0025214000e1940c4003000503001c08022007d507080358041c2c0c01018228184440e01c25110010310400c0d400000c10480b615580c010004a0340445020b07040181a003a101e04003000041e00080c1d0040104445008010414a03182054083d00c460104610000c108100044e00c0320010b14001400000b5481d480c5c081c0040b50381c89070701c024040e03600c2c640000250420141441001c0b150089122440c20500c0d40c1e0040243e41c404060741c15094000d149055000101c0c40006d0041280918024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 107365494 1250 107364244 107364251
    0x20c0304050307060807080f1e0a0f0e1f05010b030a020711061c0c03380d030804060b030d0c060e071e030309150801030b1b03010b0a121b140904 64
    0x50349907220698501607001d40c0c1f105041c44d1114051505205011902004080110011014810414860035402070301e01c17540040c0c0d4900307440b01441500c12880300180258400315100e02401411f03048060140c41001c42040b040d41842c002540780d09c07000e0009619070b40c0114244040c40000ca10704000071704020310b81580c0d5141d00325401114000488019a1540340c80400020140a406203020846030b01401c3d1800448804001c284e5203501d1907032020100650103145026190488200c618074004d4032001130078907252500c8001e84400d20042c50080d00810806019035070044500c2c501d6560110002c1842c91134154494685405603201c800011240c84404c0c01095000c1580c005580c001d43d580742046440300350404580c8104213a5a0001c0da62000400104100c0c208854000109001e001d0340b10065003980030068000303800085524000080703041c0c1c0380f500b165070046c00112581c3d050240c1c011983c102c14001c584000c00d08240081c10040b8090b545090040f1484c40c14002c0c400c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 107366744 1250 107365494 107365499
    0xc0307090e011421061306090605090a050d0c02062a0d0906030e19060207020d051b01030501050f01021c030207020d0c05010f080c0406050912010c0e0f0d0c0504020c0304050307 78
    0x2d82d01e042c181001c9010707981d031440201034a40c00d004e5071504a03a442000f00155120755004c024095400001941e0b100d0360350028400103000350241034055016400200500005400c0860501162040030814040080e2280f070060300d96030141c40028441c2420300d00403802c46d03c0f00b5071681c0011403400000b401450240d42209030802201c206a800559082110030100e0340c019030742d02c60010011001c916105845000201181c000705200380c400340c920381d2807441641d120313484c3c40b203002c1100034004140d5070344500e075513414800c0c0e0b8014a01241d0030540c01a28600103034482e0030408070310700e06036200301c259509580640c04649195901509404102c008c0741807083c52511035000303142c000354522140100d16440f07800e0321401004554030352403074286000300a4034a60701c01c0e41c0c80340d040040300340f1165480a080c403c0c08030501e03032078941c2c240500d007107001c018901c011130006910440740c1b1016040869401c208400540d441a100140d441824528040c6540544d9204960501ca405000b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 107367994 1250 107366744 107366759
    0x5071704030906121812030209030607080f06010903030c020f01090506072102060c0a0c020109030212100e0303070203250c0807140102010614040903110601080318090405060c0307090e01 82
    0x6040310000d65903a4038108134028141c00390782e000e03d0062521542c4034611000701d04074100855158041742401458600ea52001c2400c01d6000c440510110304002c04002800b800c0c984915402130003483c04004c018219034000c0e01c1e0890400000e4002c4c0d201c5c031240308036640a50041d4015240c014992074030b511aa2800400d81c60f01c01d807295240a40441201344810300008080e4051088001c01d1410080841c00032106004800400d0b410050210000009608e411010b0040308070144003401e85005807401d0f210030b07100720500841c0140c1c002c00070056220b50105c180c0e8020f000329510310404516442429110105044024043c40000300001401c1c2c400041c240045950354032211031505d90b03204c0107900b01c0b4403074840c091008100500f100e000b8503060781700410403407107400c001501c20010207580d49400c02c260403031000c0e40d00000340c1d98000d1a42c0703601c2841c0703100116001f890519040c0d940a846c0c0d00054440c4c805c0d04400300214602500800030040640800c00020b8000d41c0e49509 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 107369244 1250 107367994 107368007
    0x10081807090b0a0e01030201090e0702070f17060718050d02040b090c07020312030103080301150201090606060e030c0604030f0204020304080c06041211010c090501110c0405040614010803040e0105040507170403 92
    0x8620f10680d0740c8000083ea40c034504da01c8074100d940585421100a10f070a02d2141e441e04024100c0045004034440440d6602e005400c3d20042c3c50851520058030807000d81c101e140400c050328000c10700034902820120b03a4400301c4104191102071f17030703040801c0006102042c007900d500714642e43d007d944981004810911840504080e50084048400d906500329240e0f10910081c04080c113480c900300014840c1d43d031390b003005154042c800c1c4000038103002981c03144c900700d600707681004000030340c9107a4680c040c0c0350400c00000c425404407402441c2614540e00c0c11103660110900a00860300400010140700305001540c903159040300903140c02e0b203000c0c5000b00d03c0d00c48030310070b03c00482c81c07218003945000c80501c5042031000301030f2510000c850030000190390700d00950f22000100e10075440c94030303810b40310345c000c090159201c0c210200d594085101d00309091031058200340c1d055032042c80700b0084454030340d40181c11a0401c1d240028a40c86070b12040f11203103040300d42d48507280d0034801400100b65010300d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 107370494 1250 107369244 107369261
    0x7030f15050c03070212091c050d030c0207291c05090105010b070f020906060c0d08090613080301031b0b0c03070201030f0204050a17070e010807090b0303091008180709 74
    0x4401c00256540c0e101c107078000d00060b12000c0c01640500c04807044a4283d6009281d9240e00030701501c04080b268103c2a800c103000300007100c03550041c2445016454040c064109040803a0000d0310600b400c0040040803800d02144440140c01e0022038015560089800c955551004d044520307003215510303a00c1c034090203040e50000055881c00c00001641c80128080e910580e0784a40f0150308816103400f044418840500400e0b031010f0100018096144100244480d0720510303114004146000c0e8601410f0060051140e02c00c040c0518080c000110390000b20307415a580f00c1c451100d502c440d03410464007080c864200b0740221000092003d6031100000107881024800da030207011030b5810104900036400307a84a5907030020720056050044541c1268000c03180000c0008076100d043da0f60031180240781c400ea11034000e98028010610412515014803035482009a000b0b529005080c4045501854070005910410100001003044101030b80391043c0c0d107845020071900b08a03100c8029000400c2d124 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 107371744 1250 107370494 107370533
    0x109061a1815042406020705061902120a0228030221040f06030506040c0c02030327100906020d110d0509130903030f0614030a06020702060d0501030b0118020c0601060f0207030f 78
    0x140000303541440060041c5c10f803007015040c0d6080c0f01012b00010400c0d8094524401940940c0c5200f0000c940600050500000c241d40105444600308803816698158148081d000080307010010022036000100c0f0041c0000100d182695442115000c1c00301d40035541050380c8400f01044000350407070307042d0003082c041e070000c40c0c00300510310300c880c07043d2465488602c00a4254205100c2e815120039101041d100ca52000840140c550851900044402d003400c4000f03000306d07001c280213100d0709604101e1117203089068141201c1701c1c44410354483d0303111041d000c00410001c001420502944904104910058000300305110103c418034020740684200015090f100b8034102d00001e200307684220388403100e038024020b444003440984803040654050101641c0015003013041500102251140c1c0303000310700404c1e0f18102c42d41030400c5030200061007825102c40500611100610020101c0c071181102c05a080c05810900c1c803500c1a03051000c0f990001e040e0308400042c0c4802d04c990004180d0026041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 107372994 1250 107371744 107371811
    0x1704032003010b031002030705070b0f04030f1404090b0a0815010501020c0d020f0603060f03060115140406080f041704060507060c03050f01060c110a06020109061a181504 75
    0x209801e140c01ca90014444a034181d10001203900d030841c144d8000c54110280380382c070501c0c104950b101d6980010f429601204403002d044100810700d5401004030b01840003900e800a44001d08103480312031400ba9019185c10990380d944031010b10b40d074030001c80000700761110603900549000c3c4010000c1c00c1c800d100c7d0310b0150064640e050140c2c6002034004107507aa0050200c0031180902c014040a81c1000b0b0256130480304441c02c0d11000d6404104050003060600c00384041041104001408418208010000e001b001e1100344122600401d105a00c030900c40418202d40d613660603e41c1c1d0041c2a8459940000800500030a040394008000c00e00540198400e206c00302440c80b00720100c40c4115440a41c01f81060010301080380302d018500038a074003e80d1107600a032002d20008a2024141d480100581e544111141c10081c0e14051040310120001841c0221501c4070b02007251500c0307040c5108401802d080000380052102400c0703c1000d4009001007140a240c1540c0c0c408114074215603103188003030b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 107374100 1106 107372994 107373053
    0x1140f0c070305070612090f030e01021002130e010815010611030c0613030e0a0e060f01020304080d090503101a010e01030f050c0d060b04120807170403 67
    0x500c3c0680303400d504e444005480c10b6030020b00900403508200c1c0c42c00c085655940c8200c1c84940505002c120702c4a8800101d06140080c12250903036032001c5501c035081e0460650040950b9480c08440a1598a0301445643d5001c40404164401062401403111074858544103903c400f1080451303007040c00160b9440d040c44070480d00040c0d402d4080511005055000103070187c0000160743c8035408074208502d03803000c60b40042c0014000c401c2c01040244992080080b20001d10b504029500d40ca03c080600425411440c801c2e14803900c02d0307034a02e0f810003502e48901d420700b030701e010b01581310800c0c5480151220144401d03001d050564802600f601601a0302480c1d105c0e510041082c0d40e01c10b8482c00d0340d022560300d07400c00f00d0000010700051040201d0300c8560036905801150701c50700d402c0300f46010000c68821100016140344003003000070401c1a01d88001e040c003510a0101005610b = true := by decide +kernel

theorem cover : BRFrame.Cov 107194244 107374100 := by
  have h0 := BRFrame.cov_init 107194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 107194244 ≤ n) (h2 : n < 107374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
