-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2617
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:14:44.145482+00:00
-- url     : https://prove2.me/submissions/d7d1bfe9-137b-4a7f-9956-8c7c06ceed6f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 470503597 ≤ n < 470683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 470504847 1250 470503597 470503601
    0xb0c0f0f011506110c060703030608190c0b09090406090302070e04050c010206100608131b032a0608040f170705011d0303150d0804091113060c1a04020a09 68
    0x1403544038165100c82040c5041401514414003c001c10304d0312031142d039500740301942c607480e000070150f01942c4000741c0c078420316029800c1103006118400849686d0034010744082401c0f840b071032045841c95900390000034014000001c2d942110001829042161116602c0e040103220a50088065000d03d0000084d183c200400052103140201c0140041e503c045000906150703008286807582c0450a80074440e140e484050740d0307400341014450790b1840007a41005d00038030030280400c80f06c1c488024404000c1120941d150307045e2940341c0ca450f003a20030b12242d03044000c1c200360040034001448000050040f4107440c0f4205201c034080e24001ca000e50360740b108e400c02580b2021040d21079a44850510016420341c11404400303410000c081d50460804140710740029202e010851311402d0142140c0c4284000750080350000d08110008010507141008000c00580000003070071700341c1e030130327001c0000c1c902c0c1c001c60b403504900742c4c810014581480c00b103201203200c880181040e60001e11402021030012114 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 470506097 1250 470504847 470504863
    0x50f0102030a03240e041103280c0803030a02090a080c3007140f0405150402071502070f020a062a031e0206010503120c0312091204062f070b0c0f 64
    0x1c0c445d90760003841e01f41041070440c82d0450400d0300a503c102c4400700382126092858218003804064a00c4904580c00e100403c7e1495400040032400002f05106c1011490390040105040507150058100d9031070a810340c841c0c2c03810401640000040da40e41c44843d547e4a40040c503003042e041001c01d2040b402840500c2d00c0d040360081c9610480d41300000902e45046140840601742c01c50301071045180103800380714801400441d00d4019500829500e040107405c4404c801100146a401c6454601c5800c024001c1c802a541c1a40580d51203480400d580b489200074052030b2280c03c8001d850b54002e05d03c00c0710140f6404e0b4050b400c05c510858440c42c0043c50401e11906844241c2c002c03c02c42d410300081600b059000b0205070b54640302008200c40308800803090301c80f0103040350040044ca039034000c2c1d20390412804040c40001700c0d6000030081903050304920241c20310f050341800244180e0009a0811800c1805890400d00b82d0204c03404012662001004006c04e0400300143c44860b43c0d1140c1091500640c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 470507347 1250 470506097 470506109
    0xf03030702031309022d04090908220803030408070212032701020307380703020316030204050f12011d0f0606040c0f0305040f0206031807050f0102030a0324 69
    0x440c0c02c1200050981c3c5400307424584011483c06460003c41031290880070382084682c41442688601072102000750750051489020030300401c0c0f5070b49040612940600c61002c030500c81080b016850744407201482080e210560700840c03035034685403521051900b1150040f6442610f8600a100201c0b05001402100d405c0d104620344500083c041580c41c1d4240e165050704652051060381c0104071030200110504525400041500a00d2080410340b40c0c2030201c0e1113856034000b01403007084c0394590b000f5445202c1004514600140c003060442c2644521f108103644040390410480107880c128040c002c40c207801d2000080c8820341c0314803080064034804241e4aa80d0010205152640c0c2c042c0040d5500203005c440070403d00127000c501030034050369000c0e680d08140ea1040001e00304071031103120070210b030340082000341c807441d204003444c500c030901210381c00d9a40580100043e107800c4c8491890ba070410140c01850030100c010b0000c80c01406450103000200e00b00600310180c1e42102d950030301c081e01ca = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 470508597 1250 470507347 470507353
    0xa090614030705061303080d06090c11060a09020d06150911040801060b0702091801020405030318011b0209070f02070b16030207120203070e0c071505060310020f0f0a020f03030702 79
    0x4850030405040c004164880b03405030307004000525211200075002402d40794045400c0340c4521544030032100501c27035034000a040514007201c4c80e420640205819061110000445503e651420144820385000540094210518100000000e03009400c28140c2c0000ae03d01256099070b02e05980d419a00607007000700c04030000250602100d0006e0044401810446c00140d103848143e5022541d04440100f002811403d410b211914865003034044900078a0028103da444041101c414003c1070b4083d000c66011540d681141000c20004050038110550014800074155403515429151015010407001c00c501603107a0101d10b082c01103028003805e80503418503a201c0002c17850080c1c81c01d00c59030407081310052450603400c011307035001840000340d4102d40900d0801d92a5603418141a0080400080449104600406140c0b582d42d103c184200702c22812503220004000003802203200c1e4044000100a0400c010340b03031316803000010320b1105c07041d20443d11010f41d40c214450458009840410042e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 470509847 1250 470508597 470508629
    0xa03020705241e22151406040b030f0a030f0306170105010905090712030c080d0e010905100209010c11030f1e160b090f0609040906140c0408060c090a0906 68
    0x4030f11001c01d211100c2d0030200d04051824051403110b51051300c580003001d40756544111400300000008401e40800300c41005002250300301c1c0d010303070000c80119131007800b8525180240c0a1f610303001602d801c1e04417021001d4000c02c00e151700d00b151620360b42d08540c01407503100e00d00003503110201d2070075000842e03142000140d2941405008006d07614040c003140c81c0c80d400342800b0b01141040c0c0b0407110b155603041c107010402d91414508000c6c18056030a41031500d80c40e0403081c0507a041c06402848402c2d10507004d45a131159903410050032401803804240c00181c103485910002000e2a07011904008020304480c0901c045020151a000a00e080c6154108259079140000d0400b000030f003c20011001d03002d10940d00b018096001402940c0403e4803410940108160603210903040f1000f41401034400c1c880840bd50031f00c0340c003810f209240440c103081890009040e44001206540c00c2c0d901b0300c406004d454450065852064004c074440a42c08401c1000010b0448268441c0000a118150401c2001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 470511097 1250 470509847 470509861
    0x201020c010c090807090203190501030f0506070f0e040203130b0c130501080103120e0a080102040b1c110301030b040503160f030809060421020c090106090512120a0302070524 77
    0xd62503106110091112842052001d094003044003001da0303113000fa0060310727907645902d00b00c54a011043c80c0704030203140000220070700444800381c01c6914024000c885032a110240b0444100840d4411940000c040c841e4241541c40c00d500159080038071440c511608a96039114101c01c8a025100800700d0300d00050500c001b1072031414550000e0509007000f000700e42c51925078102e020200900304040107451b484402d02d07503481002e210007401020000715103542c1c03180b6401d00075501c0134088480c3c0c028102130041000600f80259059800482825403c691075135030b840881043c003410032202c60000340122140000e4a5954002850142d01d41064000c1d80b810301400740000907040184a1f0425010400420408803884a400110884640d40c000003c2d40803400c100070f007413040364400000000060313000d90110220040ea10f044030f2024441030800b40d440ea80d050300e00c000300c000c3c41c024000411018041d9000c0d10f4070900600550704000130f04440360b2505041c0c14000740b0034418170004d0041c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 470512347 1250 470511097 470511101
    0x50409150c09081608060f1f08060a06050a0b07080c030d1a010e040b0918070b03010b030a0b06070302060408070c0e0403020105010806090a02011d19060804031e0815040605030a030201020c01 84
    0x54030704d04105a0001d0134031100701d4485c2001841100142e500001050031424205418030307000742d0007080d2548072501c9003003c40d1075031030a4420741d00b40c50400d88042a1071a001e200442241e5a40354294034001140e500c0e010250807440045003240014080411022014096240c030300102c2206141803c1d0807030000f5200402200c4154091490060300515a44803800300300d40103101030140c864001c01680c0094500445138100404409001c000024840c040c00043c2d80645041e4506000880400d014010741e406800c01c00b5005910101c08103010411010003030a6a0f4098a0034000341070712400902c0f0002d409482c11070040c0c0d0f45070010001c036001840000c2e040b020300b00213000c16002c5500028017404502010841030030070408001d130140d80e40f0f03072406584d400403c840c8000d103959880103043c105089174150040b500c59850f484c440400408507441b0344015482e061070795150305620000d100d8032030644642040e80d41c0c0c40401c09540800184070b849100b94000369607801d0814041d82 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 470513597 1250 470512347 470512363
    0xf030303230a090203011803031b0f090b0309010605041109030705090105060706020c0c0901170d0c0b0a0203040203010f151706070f0c0804151214010b04050409150c0908 75
    0x100d2540410032408661100d180440d0b0446200100800d0316602400024010b098140103010303074440c45200f2104254168101c402c400a21122064512559410580c0d40360004d080c1400050354007103051103d5030b83c043c055504240711100003d079254965010030b0445880a2101c603002e00007044298942c0b030100500409001c0c1a01d41d802c0359494040421b40a0052035401030455802283d0390b200d43c0d4080080e041004d800a280c0445540e59a0418038021106c80c2011001d00444896803086802040082c100c2580310790041d04940d98610048020340000d0030403a455501d901184a003118640106500b0346403038001d401e011850091020054000c000d60619103812040402888582018000c403400d101d03030401000700c5d00b140c907280c00b0038456074000c1618014030140b0220314036400104c2e8803d204030403104110244112404001d0701600740f00c0c80c060000200000c0c4a1410130b0380103d00d2991041308a00b1140c40c0c803210000c00c1c4d8400c11300d02030010360504004c00024904001c410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 470514847 1250 470513597 470513621
    0xd0b0301060f1203120614011b02010807140d09080c071a030a0207021219060e01020309070323060f2208250206030405010e1605131d03040f030303 65
    0x480c1600d040502d00720106103100c1c241003202e0781246541418091845030b8a50a0900010001507845546040c601c1c48080c3c0000d001400c07082c28213442e40341081e0100c00c0d194058448100d00c1d40c54100445640400442c0711003641014008a418401c4600445103003c2c802c4007500c1d00e5581101e1442d02d0300c141c9034071014008640c0486410b03000d1904048980040e40705c000075075a4079050000c40d0784c0c6e007c02c002500c028860306945c18001182050030070719440c415030083c0410842c40e07918509074002980c100400750480b02041000400300c003201c0075070b00884a500550a1200001c00781040300c1101c42d1580c2104100412440302d840840300c1e1384042241440c90014500360b2516000c500469a00041c0030381c8000c25600c048401000902e101980103081e00c0e602c1c5403a1400b940a800c50f41d80f81080d51140c03018143d0b2540c1211210010340c1c402505000300781c0c0c0f00a45810103004103a04454510308480c0c10030100c0d000030f01c01880038080c40300142d48030302e00d107150041c22500112514 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 470516097 1250 470514847 470514851
    0x20a0308100321180b0406030c0329030c0402210601050a050417030d020d091401050c09190503010509031309150303030c12051e1005010c0201080a0b0d080d0b0301 72
    0x500c0021101625550b50304030144404960a840c2c1400303942c18604008051306658018000088014900004100340e6440b56024010a03032084016070642d040e02d030345201944c0c200e51030307950100c14460846404010040449141c4040c8034003141c100e9012010700c50100075400d07031609000043c145c84c203070040400e29049180032038a406c001c01c2c2d404ac500072261100d280b08103c0020090420655a0707060300c0704400c41d03540c4500d5481400030412080221064800451402200300061203803600c2801840495860100c04800704032100802075081a44e4131044000483c06460034072a49119040707680c0110380d507100e070b2920010304078015400001c06505194034030104186a680c42000c80e689828086500740d81a803066880e040080310040d03903c0d00e00f10030032952141c0b1100b006600d100c1001482600e8071440c00641ea0f09031a4011540450b200440050041d4420075045a0115100c02700003207450081d40007403401d0001c608240d8008031b0110b071802c00c2c0c091911581c0360309a412002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 470517347 1250 470516097 470516099
    0x1030b1203030f0c0903071d060103151a0705030a0206010819030e060702033408030903070311060f030421170f07030e0604081201120c03020409140d020a030810 71
    0x26940ea40300c02800100c01c030450401048444e1311040c180c0d00441c2008041c6c80e031007034645000e64000032401e01080180800c05e00030481c69402407241540c00341c1c1985c9640580c40c100718068081482c588111810540200101004118244060142c407a082d81c090701d00d40d494034422038984464030030540c6111b9900712190300000d41112800c0183c1c0d400396455500c1e0340755400001d04001311400302c0000c03001c07507944105850b05c42009022311118817812501006846600780381c0e890007880e03038541d0150300c400c900344003042c0440c544454100c001003400c0e2416038010ba00324070790b03042a10200c07040c0404041034400c0c1d20f54684a2180c0a10500d04000360011714100840c0c02107028041c000901c11400104201610a40100380100d000300100d0721103080500c0e260f421135010000f0443d003100c0c1c44001280113040007081152254222000da41518219000c01c401444008400c59412101413201c12500c0818003400620707a07500e4028222410690074094a41e4100030016480300c5c0e05000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 470518597 1250 470517347 470517379
    0x6071b0507140316241b14160614070c12030c060b090f0708041b0608040b0907060f181802070210230c01060308270109050d02010309020a051e01030b 66
    0x6012866050000c5c0e8510003520301d0000c0e5044082910300c0110b8201c048180c8091001100401c079040c0c102100710381580c0c400600c624451480b43c0250800a1ba001c0c4000c0c1e12000c80c00090110280224144001241d85550310b82c00b591610720210003013000c41504109001051040300c4400320180c880c6401131824860030b080541000704100c05000169007c13a0a102107015035010441103034200e10b40ea2030710380300c0240001004880480f5814410000500e6045010507440704941c2951200504012251004d172189103000301c0064840d4801000080c64410041c0b03242e24942151900680c1c0d0545070040c4252000141800070910404d46180ca002814040540041150b100740785602c61440106480c05441c0d280c0c00a03000450100e10403446900314075220442500f000301b500e20100c03501c801507a0140c9144901507001e030150140c0405540a81c105895003440180b1022a0b6910b03003001404200d1200c0e5806002400403640c900c41d540c061140005e948022504414844001c003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 470519847 1250 470518597 470518619
    0x9060201150302221e091502040806160c0501050c03091902030309040902060d050c0c0706020a3804030306050a060912081b01051e06011106071b0507140316 69
    0x1c103402d80199404c1c80410701556003540843d0080380120342ca41640b200d100c0c43c410141c0368130141629401d2640f2500902c800007442114103e628107000382c905565000d00000f904080200c80c4028040c42c00744000000d04280710391440b41586150264980c248040118a8001484010084000c002d018980507130f40010543d90303070b42d004540c081454405417021441c0d50080101c00402141030600b4441003981c400c0c06461326495420840d400a6501c00c012031783d40d07190f031402508144041440c08840c080081590384071400703118900c0e0f8496240509011144003c03201980001c1d9a100180b100f440c28150384c0c001000c451601140560401d01d01140f11084204024010070001460f0b5084142d90203500c0f4080900724004c00892900040c0107600b581c0c0c000e00c0341c041d43d0040c40011582e40c0039016042e84440c440c0010070140c3da0348141500c480382c0c2c01d003580f0143d0f49100c90b040d000501c2088020013800b95040d01000d13414100040c546407201480b00084000862441841350100035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 470521097 1250 470519847 470519869
    0x90e0901050405100f0f05150f091e0402210d08090c0120070b04030605010f0504021603030c0908100204180504021311120f1e06031e190309060201150302 68
    0x404c00915074840741031503c01040030490380c1001c1820035040101001c040d0166001c0c1000c02d84420319902c0782c40040080b15070b4101d403d1320f40080407424403014000d180e0601c40c1d002c0d1000d4000100110414510601000c01c0c0c0c202035030f00c0c4d02809940c02182d1b0302c000d01d160403a4a460041078240340d030702c0018101d40f61964001e90030340109110b441c5890001c011000050504802d010350703c070f45a04001d4081c140901520120100454000400d800c051085030400006c450702059488400d9034220013034080d1030460820080c40d240c01040105091000103690740b14200e005076070f40e1070103003491500407483d450000d0310f600d0841000b01503100d21100ea200e0400418000130035425504102a042c099144400e0780c0070000300c00c0146908055011500900c0c2e100070901324056108280d400d000401c80361030360181c0092100010700b40e01c2c195a545200300100983d0080d81d42580703030716030072551200c2c240c00041a48404000c410340a1046202958520101c9603565040d900440d50100f41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 470522347 1250 470521097 470521123
    0x90302060f120106050a020d1806080604090503040801091406070203030c03041a07090311031f0903030207050123070c0305030c0309010b12030405010f031a06160b0106090e0901050405 81
    0x20008030310400503514070854140b081c04815402c20395858080051a0703400100d440e00251041848048586005075054210305c4840c0c04086031417030405000701c031020390142825402030340340e1040c000050000e0004c0c0c0003620480d4000511041a4241884003914030100034480703400110904c680d40d640072003100c0d0f1210b1a511280c1c1e507500c2e9458280096103800c0c82d0541c0c0101c940c2c013030280341584660300390202c1e8010550900d044407000d08154980c100045984c1340d085d01a410704c541c2e4402600925581402424014100380341c070b407552070135100e4140005102071a4000b09010284807032a04a170803003034034a8504500c00b180d40d8050a1440081e250f00e403003040c04000184904006d4000c000b07298000b40c0030014004d00902d03520340c0d0b0703002070040c280442c50712145441104d00c0fa01c00c0070548204026120340c0700084200f4000582e02a0002c1d00c4010f107141d24600100d410f07580301600825580d6103061840d8a45110030440340b4000d400741c550740c0d041000340700100354005460103200381 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 470523597 1250 470522347 470522359
    0x9010e0c0d06080606041113090e030409020f070c08030a0503040b10050d0c0e15010e090618010e04050c01050c10050606041a031006020a03050a030c0314090109150b01090302 77
    0x803040d980399014015255180030080c102840401c1050001c035080d80503440598040c80781c09844070b01050a4041c01080c191141b00d40c1f601000400c8480e042410320900d110156880d060700c99111000b40d0b80042500911060300160035020030102020f054001c01216001e0760a00000120060036480041d10261401000e0008070390400d09114080b0300803d001084440000d60703510301400380304420710410146800c0100003d0841c9052803c80e02c00100594034280f00c2400c1c402007145001b409000e0300e4014050b420049045801c104086001c0d1009901d01c81045c0b5103480e0640c0740100c610070a41c10000c06000903401d441000501c102d05031100764000c151a61142c021030358130702942d88540403140c1ea40504641c646084130080d8001c4032952804500c0544420041c3d82d2150124402030028100700501c0625512980c0b10016442c3e0605d00840e480d0070209444407121025210000780740d5480daa1102001211000b00c0c00d501c005580a00400740c040001810184c02480080e000e10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 470524847 1250 470523597 470523601
    0x609060909020f09100b0c0102040e090a0b090c10110c04092a120b0406090503030717100807030312090f0b0105040f09080f0702120304060e09090a0507050d05010b130c091409010e 79
    0x180c7c0a40584000d45500503070355420b8540000c0140c0e03104800201039a100b64584007084141d0320101e6010303c85e0901910068080e07219840449004006034a1881c00e80218041d41c03030b05a03528081c20000743e000f0032161200c100c950f0740140404514039220007031584100c00c1048070340b20500c08907a116810807601ca426a41d10708052016011840c0014020300001080200140d0007194405004040c0f040c0041c0b180d85405071840d03c0d02c481c4c02004299032010400300b000a1244080762612120598080380c00801e55541d480c8241030044112504210b51005001c282014495581c418400000c11f1020616a4644049501c169140d9440b442b000181d0321080d074560814020a5007040412a80d40b0380e0780b1080182000c01a01030039100708901d0300400c22070300001504610680e0003030041c0200c45c0c42c0c007041100440465104641c55505c0308644000f03541d0300320084030350a0380f40901054040e0240e2004055070015000706841c40a503c0b070582440d166400000e040d2404501d100d0850307 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 470526097 1250 470524847 470524867
    0xb030a020d030c020904031d011704080703140301080106090c2c040915020304020102061303080f100905241008010506031005030a080705010f02091807030609060909020f09100b 78
    0x3d484090040e4003c0030103014042096448501c08140c0b5200c041400200c800320030044412905c0da030350001445c218200868040740a910007440c0b0940310341040420100440c240003015003090740309640d180d54410b8100309220441c0a100980081850451810b4120f02c50011910f0340b0710100700080404413030942060746583e440300ca41203401081003401010400e00709400783d44121402c038018000c40010945818581c1c5118403020f6040d102c440c0245d891952034a05100001d1244400035503480001841c03864a109141c003840d0100d250b89a451849242490070110100c001809583c8402c4c01c40c01003580001400d040d2001201e501b40c1c1d80d26801000c0c120802c258201c9641406a00351000412034500020150f0034800c030028848030b0b10307e00e5490100c8c041c0f000c1c407e40000442c0e0b05c4490719000503818682c0601103040000f24107440d601e409044803a15048180c026a0b905140e805514001c1e00048080404440c0f0340c405180040c015000342d40b05215003201c80c1c0000c5200c80784 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 470527347 1250 470526097 470526107
    0x206270303040b07140303190209010c0f06090b091609020f04050a080303070201050a150b0a1e030e0609060c0405120a170a0e03070f060e041b0e130b030a020d03 71
    0x15491000301200d44482e12080c00180d00d90091500b00c40ca6030900d10250840c00010003540e119401c031100c007070303960010604200088d41c8502501c0f07041101044a8800103504002030521450240b2070000396101d091804030701000c400380c0304c0207440d07002040307890038211000409015a600c0c0784000d84c80b00b15884801c1c03040e025940200d5401040b1046c00710b10074400002541c0300d124140d000b40901e44a0000145c201d50301c498606095900b0b160040c4810841e0000a01b10000c12b07140060a2505118540002258480c49400003e40383c1d0f030007844040c1e04010560308048200701500c103074280142c008446104601c039440c083d5640154407151100b080c419281c00e141c000030700000c202c4084d0002c00c45680078507d203101142c2d0000000088c0d083c005040c01c1551508258414a04d040c50025104401d20103501c42d80079407100825814000e6040e581000d6841e242c0b1184a854001c00420202c2200f490140b88100e141c0b0095445950300025081d000c190140e0f8154082c440500301114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 470528597 1250 470527347 470527417
    0x30c0f01030b0118091b0806012c121023040209060127050a06050c101d0304030c1403030a0c0318080607080a23010306050c130e19090206 61
    0x8441c240e130014105182e81c1116010b81050f00e0407065040d5544020f456110713081e94130340d00241c40d0303980c80b1421485203402c0c0d8070000c03031245042c240c802e0103400040001c04040c262241580140b030014000a4540c001d994600c2641900d18240e240d600400c4c07998908010300c040e2040e030341d12000c6a12340c0d000e0402c11240f03007040f5038003107084582040400c0c3c015410380728003405640050360015103584a4400e40d880303994480040c0c0280c3c04145880400341221000045400304035506540c80705508200810086100301407000750203186c06884140400303200e81c040c0c0243c00c10002e041e9440c1d440050100e00903894286103004130300c450401c0c40c0d141640d07009001d15214800a220040350000791061003600c01c00c03410320000000c184041b4040c0d54400180640300521030043c40081d0013500681c0e03103c408403441d64100001380c0c01041551902c0e502440c6d1054081c018814040d2000d00c005d40c1c0e07442529010b21000036240c2c007260f0ba81c403c04a00b1010100c2a0301c2d180881e64042040d01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 470529847 1250 470528597 470528627
    0xc010e030c1513030f05010606080f040b0411030709180203010c0804050a030c030201180b09071e0513140403051b031611010c060e1f0c0e1005161a06030c0f01030b01 73
    0x170300d00340301c207242070b030b000344120b02410010640c420f001500300106130025a100301c0e807046100480307407161358401c818006159405541409513410200f034003521841140c29901a103e1b8404443c1280d00505085907098040e500400c000041000049200017a0315074a46605103410074030360031141401ca0041030170302400d0100d5201004c80805200080480601031101481581d0040356905003000648200c004100c800c0c10364504100441c0c903203025044441001650301260221022070000080c11007120203d003c00d20210305c1d08100f2002c8004c1c0144420703100000c5103400218076030000c40041c020801828640c2c0080c80c0592a417282d102481141d40c400814050400d18410242c0c40724444481c0090103100307008400c0b01da2200f40074105280845840d10f031030142c80c80c01800f40101d04120b118003445400c1240300e241c55000c40318031f01224060f4841100030414039106900241c000b4003502e100b07038044102d000250752003180c218008002400e0002c1d4068044005851211603040d0034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 470531097 1250 470529847 470529863
    0x50411150d05010311010f0e100c02121501080d1818020c0d020331060e03030c0d0206010f0b120a0203130b010815060a0303020c09150603090c010e030c151303 70
    0x1003142c101c00c1c0b1500c500c000d8070b41c020000d00d1f9001c01c4664114541e415644088094007104105e80902d4110040302d0024040900c1c102c3c40607800c501e0003051140700401002184010050020180051844040e03a803a015000c003c8000c940f0316000954014410032a40c060841100300c0200c0c1d04841c500d00401d41607608082c25800e001e510703500011413880110350280032203100318011103205134030720041026100c4510b040000c2216851000349005405201c00c02c0703144006282005001d0000000742c0c0182a19810541031001401e625802425181c4044c0714041801141c95040ca5000742080390043e02c80e61424540230f004c1c811034002800010402c400818034000100f0381218050701d1340301d800004c0c0c54000620001c010b00c1d12025005070040d14803000c2c945051007865800c28170a43d03255074041a0400051500c4c7e106031103a1200d94407800c055441543c0080c504182c1c900201c018100c802c1e20340c00841c900c00e401c0c009010795480006040a07040080041c1c500140d500408a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 470532347 1250 470531097 470531099
    0xb0a0f0b1303140601050907090b0711030109140d300c050d020a090e0f090a030c0201020a02040c0c020415080d033605010b0301020a0f030902030718060603060504050411150d0501 79
    0x1100d5103544c401e01841c1c2c014082c200014981e280102008012200d050100a20703250a40d103030340d07190318800320301c3e80e9041d52038880440101c1d41281641840100e090060041a4510580900070f46203a4010454a00e50300e03101e40715107a461030a05d260580304183c0851002c46580c0e007242c25114104600c8050ba101240d91692941d0000f050415588040300588440d00c4031510034441000840d190402c0b0b03403004408200180c4503d0449126900c10700440d031004c45158006815901c9094004002860641044003540303090b00403050442c900c3c14142c014141040100d40d182e240d56000310701450740f205100d040d5404088840c0118542c1d000c10b50083d07000d44980341c075104d0b44001007541e41c0e600b8561a04250718040c070884030f044e003203070b00c880540c400d06100c26030161441c51016030703140c0510100082d8900b0f4000003000200c050a2000402a040c5000070342243c00940005015514041c1004000303a000c06c058800300100711201184a0a854820445481403058079400d880c01d01c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 470533597 1250 470532347 470532383
    0xa02060315010e120a120c0b0c0c0c010c030206070f050717040f17030403060b0f0a03060b180c0301062703150506060901090905130602030f07030b0a0f0b1303 70
    0x1541c045251401d0f640d04610b90380303510402904502c0e20305259400c1d0004040e020004216a507002c1a8440c00c0c202590419515221340d25880f40c02c9818030b60f0410005041000918207100c107459018090130500c007040c2c81d6440080d44c2c1e400007445c0d00140f10030004007051441c003031001d4034011640b0a002d0b090001030115101d880d604507110307105800120000205410551002401d40420100009c6050902d5500c8090141c80410151500001c0340100d0301d82c01e844100c8001c01460040c0c04c08a600c03643e110600002010a4001070106030007e0207015210380310f8000c40381111030300d190644942c030344d81c0701070140740300000241c003042c1c04440c1c1c0010410504c0d508080240c000c80608001c41d685c0c490500c0118814246014005012030805110300141c1d940801e41000383d600d91400c90007256a03400040342d005842e000e42ca025804100154240e06010380f03100721f2425a5041c80032442c006040c4580d45c1d15019407944004041656000c80410544240c01140c00035441250254044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 470534847 1250 470533597 470533621
    0x303031003031e0e040507033308120702150c1c1d09061509040914010e0307020603040b040f08190314010b040909110d0507080c010c20030a020603 65
    0x840110302240314140c100707003d86100c11011603c10455100c07040f9500034501080002c1c10020550824503a0310011221454a004500b10b07441c512240340301c890201040220740d04520a82c0925030390392042c200039801051400680c0c0140b641994001c1601b212808080340e64081d84080360380701d11070300504164462f800302c8085500d60070394869590703004005103591803601600450b10b030010700e00c0d0040740b0641000d50b0720840d0303811801c24807407d14000c00002002e68884c000162140202c42c508210000c40a10814900520200045241c00c2a90740416a140002440540100d80c443d0008050000301004044029803000d001a9030300040c690030a0030801d200000d1b400a46089942c0c507015441600d5281039610661040d800d083c40c0036102d5004d84001d050071602225041e02c3c1c0300d0301e030b20740381d0060b910184034001030000c5034103100105240120f0142c0c00c9040212103105503000c1081c2081d81c0d06040320511203009003680203400309150a440c40d00007900303d0400010040c845441c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 470536097 1250 470534847 470534849
    0xc0c0a08030a0e0d091205070b0a05040f0f03021c080c01140403030c03060501091703120702010917030420010e0d230a05030307051b0f0102040302040f2a030b03030310 74
    0x4820403c200c00304a034245580c1c0c0a030a11003404200e00c00c00c00d0148170074101c3c00071285403084c0111006c0c0380e21411010000c0e0010f95017600402c1d40494103001c24512440404003410f4040301683d0f0030740c55a00018050001007031a04029512044d00d04184881032003100e980c49800d20080c040151220500d4450b43d80440b0300350002803408100d0b105852081c0101c40844105a407820007440c146807107494050483c600742c1d070302480308108481d1410880c200d028450304994000051201d6a402e00c4842c10307046120741c960700c079420420040018001458141d10510501e40304043c035600b580140c6c7d12000c1e0305500c0d94080810a0400104140721420f1008000300881001200b5804002d007651505080700c0100303103420a000046c40144244054039004040141c1112807109071311101d400d01015850607090390750002418401e40c100340c050a5031042003401c040040251200e80b800c20503050f1280f8910315100b03481c3c6208092b100741c001c6202258000c0075070390780b401c091021a5240ca45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 470537347 1250 470536097 470536111
    0xc03060c08070e0d05210417030c060106091503110c03070f151109040e070302060c07090c0e0d030c020301060512030418050705030103110312370e04050c0c0a0803 72
    0x1c00603903540103090000e00c40c201300c5e80c00402051204d0680301c840b0580c002c1c00c20010308004060000203144041c1100b406090040320001c0c40d0744509042031b25084c904142c00c4003040c4508040c080100c07080d05011009044481e10b400114808515010805031244041e0031105100c04a520000d02c4140700e04187d00c40e10809010040f9050340d580d14059846d080351180c404041840600c4450070b0503002540c0d03c48180e130581d0021600c039030001d1010340055100029503030000c941844400c880f4441c9030a00304490500160800e030f40170000d0f00512154070014200070420009004545094004001034140146207000001c6446022640c94003e88928505402ea265012180c00c105118040c052a0740381c0e50a80355a0942d160303610580d9110340c108ad050710544048244010686001e040092140c58140441d149046540c81c0c0034001c17140d0034004072054160017448660007003118003038184243e60114013550b528500d00024020014106850b01440f2803030300c20003011200135442101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 470538597 1250 470537347 470537357
    0x12020103290117010b0a050c160321020c060a18050a06110106090525020f01020706050a05090c0a1a0903070306021c02070c03080309010221100801140a090c03060c0807 74
    0x40c8030744400070f00c0300c000c2c403d9008440041112504461141009002200c00441200d0324030025a404600001007a0f105680e5070070340c0640f0030750340d08040d0003c42032400184000d0a6113209200024818451401d1700402d2012a10040682c036405542d040000c100c0140b1410702c1c90750f610760140c0440752150400289510300b450116a01d0b80610071a07004010030b0031080c03516050b01850040d4410141d40c42015481884034a08a5040034002809000e1103580c000c906410104c441c2d4042d203201601100164201c01c40944e110344442c402b100445001507007512030600031020009140c8a0046640d4060050340130100c00d00480e60000e01080c201642e20050010440700490704901410b0801040b00d0550304040001c251300002440d041080c0e00001440e107003000300049020304070201e442026081c0d8404025014000308401d13401440c01c88024410009009000c040090b0014031000309c843d6250342181c01d0001d04803c0310051035211204000c001c00c1e0f1880503010082c1141e081c03000403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 470539847 1250 470538597 470538617
    0x9060c120c0203031009090305070b0705071101080402101b1e1e110402070804090509010501031e0201020a060911060c061b0c101a04140613060f120201032901 70
    0x62000040783d202c1e580c0704021072a8941050807200180001c22015070800a0521803500814bd8203102940113250540390745568044a00e04030f21190700020180e81488a510204409a243c9158407082c0f4555482c0900300d04104107040340001d03001c24400b81c0780b03e2015109002481d0300c801840c60290080103491074010904540b14280c034040b91000700100c2940c0c14902c5242441e402802510748036414881c2465220f454020403100102c510240e6030391102d004209014446894810315a0b42d0070690140c0000350700040e6030349010b03d1f4000c120b26694601c00040c4020103008207888000100300c0d5540303a0008001030307613501c800d64a07045482c40c90500716603000b402c0c0d1b08071541c25164038003801d801c040c05890300000f0241e0b184078072011500d95901320804d40d03592284984403101c41e0805000360400100b0300c0404180c00300246511460000305000542d01e0340300000031245204c99004400e01325200480180024030780c80b450901d00700808041c446080e02c0380701d0b070014080c1d0fa071501c08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 470541097 1250 470539847 470539871
    0xc0906040507020a0303150923060f06070b0a0902121c1b0303020c010e0118050c1801030f0302120d0605180403080114031507051b030a050316020109060c12 69
    0x101e20584044015a000c6151381c00042d01940080d807a001d10a042000c4855560722944141c0c0c1d042d450031800710a20390180501f050341072601540049084e00c0f126250ba01c0400451400c0c440e01d40003074010840100040c20001c8281c0003040c4096001c0c14118621030110320b07c07540c0e204018502101d00752403603e03070030a441c4a214024800d50b000c0040201040307280d14250001c0d44480c07090105c1d07540796018050b10f400240141c0b042620010b50747c4950702d64a0800d80d0a05403039101c440c1c0314510241d0024150707903100140c1da041d40d4001000c1031a02800c1c2c603090b45403200071925a1015080072403090901c0d0b460b94480070480360f094075400c220040da82030301c40b10761030106c6006001c5078801c070042c000c019030240c4035844000d019045441c1c406a0400e0030380e04403001ca8074600000c0000544c010a480d140d250141a0302d0400000d508055039003001502d03502000b8110360f40a440f40d20004501d501c00d40044841c280c01000800951444210040403801e0f4650850300c0241411003091407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 470542347 1250 470541097 470541101
    0x11805040206090108061c030f0f05162a0f0905010503010207150e030c1222030c03081305040203090601030605160206190908120a06050402210a0f0204080c090604 72
    0x803440e4002d188a150000010065030b40c800043c0003180c100e00410305200242d200c03010510011070090301c83e0594100e01240061450384600f00c03580802c0418030551684242c01e044e001c06090f0302a06441d078220706102c071181c1d00d20405188149620809000086800c40044444190780010000b80314a03a01d400905080c0e10a040f002000300c0100841e80100504c0c030f0340700c1480794800340280d03440e14000105940c503040c03000c10038072014400011424140d00b50700303084e644040d07400c4004650389031450f110f49002560300d03c070241c8102c000240c07290009400f20f60030782c0a090300805c119264100344a011313644103006d00040320494039240100f1002c0611000d849038103800c5a00911190740c4200d54441c0343d001307805075100000c1e03c0e5803042d0002402400503202100c1b401d080c24002d45055601c2500f40c0390300b50301080c0110b104010405158541d40050740b2400c2c86206200707001d07110140d85600400321004c141501d244041000704140602248011580c00202c400702da103078803030100f0401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 470543597 1250 470542347 470542351
    0x60c030c05030c190908031c05060907020601031113060803090f041505130e1912050a120507020a08030a0902010e18130f0506070f080f07080a0f020c0a0803011805 72
    0x503480a004c4000c0116540341500e100448910b801c60b612956040e1007407454009602000c82d00c1d0000c0c5407460410011f200d46035110381b085030140e0309410045006501c8020602018088007081c100d601c0c0c039600e074000b4080e81a41c0c0c1000030480b081c1e440d001651290801051644284042c84034956a031034107000c0e05d00e650402c00d980461041c500800c00c80c2004003d501d01c106d5548404030800c07140c0003072003629000f401d8201f2081c1e900f1242d14056808581c0b42260702c0501000384070341911650300030402c100c0454030000000c0c8035145e030002a0700d482c10407180100102c00000c100700d2403540641168480078400e8031201c090150010800281c1180310442048100f2814001168420250102104280515180542001552600e600b0807000b107504c2404142c0d803610681082d80c0c0101401d6210b1802d0807103404504204000074107180025100c50702140d1120070622801481da8111241e080c0900f00700c0741c040d00c05103480c4160b81c20902c90a1160000c5114010502c0824003901d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 470544847 1250 470543597 470543611
    0xe21060a090816240603120212070b04050a050d020106050102010b0f060f1c0f0605010e042d14090705030d080103050c0409110d060b03100b0f0409110607060c030c0503 74
    0x941090300f12009101c85100340031058540d902101e40900b019850030007181880344490324017040721419820005c00d9105012402d004544c010741091310505c2042040d00d811650144c291606515141812407400382c402c0710140507402280340004040e501588414102c410030780003803000b1185c100070000d4804007030fa052508031104000b05c07007005000b00300902c2080d484000a80d1034814421110301141c80301c0b0aa0007440e0380e508000d0107590b0b082110030540b0501124140151501c0308061200104440c0c0b20040364401500031600203d01608080d0740c141c04e1014400b0603191012900343c4d44e00c0103100304d600034003a491204080a02c074000b007506807a00b18005000c0c90702c0d0300c400d00c4014102e441054402002c1c400045902e82d444060091030103014104c08200b10010908040c20314110900e652a0a4a414040a5143c46040c01030705202c1d01200c001502c01080e041c49100100c0b800700182d40480b00045003010800c45900030820f01c010355804120b25000018144d4491106139040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 470546097 1250 470544847 470544863
    0x905060312181c0b10050a03050d0309081902011b03050907060e010e1314180a03030b031507050d201903060504110403050c0904030f0f0e21060a09 65
    0x200080b181c000404503003894010f00260002a2030002010080c4401101181c48a4002040c0300c2d100509240c10005040101c4d621010181383d40c1e40c2c3c07a070705c0100d25040c3e402c2c9a00d0714000c805004048055506400e2008281c0c280c142e06440002d000b00f110b6100301c3d200c130001c810101310140c440d2007094132406a81c0020446a41001c0c02a101510304880d001d04000c840402030b400c90f00d0b8000c1c1c511442c0c4041d240490030010b0800c8000721741030010040036088100203c038903003032000014001041c0c1d41500380041c03e6020b00d00801d050088062040c0c0e51112000d0a216402c2d0380007004151800fa1045d0030860b850070009a440d40c003d0400c0503900018042c800da68100303030740c50049508a02d0900300040e515554101140554021b40d406004664011604009100c0c060100300345248003103a0100300ca1808bd43d0281000007100001810082c1c0040c1c0c4c106514040c00c0c4030662801e00620705103841a09004002003107401521514540c0900d50120b48804000c2c00380c03400c011350080030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 470547347 1250 470546097 470546107
    0x418050c070212030d0f020a12090507060c0c03020303040e040b0906010509060f0627040c050c1e1011030402040c0c1110020c040f02040509010e07052a010507090905060312 76
    0x81080300f02508410b036455010810490301e46425074070446141618013031015869420303001010706100c80f20b8250a0001e420401d10700001400490000161142d60500c100641000d050680104040e504000d405220000700071610000b20301c41c00d84136520035030404240e9500c62100d1fa40f036400230303c5240d4200c482000800c009141044c000742d40d00e074024140714101030401000140704044620f2401810500b91401c000d1400c0c80d008000c0d043c0d41c03e0400c54503000c04030115554480030014442c400c0c01010421035624513007407087c00b49940320820b040c050385100c80101c08042c1c0c01650102e22a520f49a0380002181c010709402014a0f08070413a16aa811244240b141c850300c07804079401140100a00c0030166602e9114003001003003001e00040c0c80d01c0c02c01052120030b20040e00000300300b48902c4100840c0d1613101084540318156411081d913001020154022803070800480041654203003410001003a6200c481041140e910312002d000d02d031a0101030507201c0680c240302c89048034003000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 470548597 1250 470547347 470547349
    0x1110601140d1505040213020406120504060b1005090f0d03020309040c09082e1503061515080a050a0e0c0603090a0812040b010f0506070303200f0418050c0702 70
    0x12401128080107409400c1c02d102681c2c5919410350301d0381510348416070342d03001d110544c00c1c00d079110072800c002000c0451400c0e00740440a8000148a032001c100c00307403101c00040401509401c104c200c00d078003400109100c911188051300680202c0380140c01518a00c0950800e8a0f21580b4003c0190f09900a0f600e029031030014000070b041c00c002120140403c04000040b0b00c01304000009414201c0c1380210526901031800300c282c00c1e20172602c0c100300c0d400d09201b048401084d01c284000c0346c2c1d00c030700001414041010011170909a95002c0c0d0140303030002071500241a0010001886201114010031050380c1e0034807000c0495405100784c80785507000c00740307040080c20204011078111500c9011500706a00c50350f100c040075071040f155020080c0b2114103000c10003141c40e600f03602502905401165950825000c030f440c9d409800405010913441c0e03000d2122079030700001d1a451a051100e00142d2302c00c081c0c1002681d5038010702c544805106140003c150403001446828060408589003514040e09030b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 470549847 1250 470548597 470548619
    0x30102040f0902070c080304121104020415300b01020d080c180310020403080c0607110d050f1303200301020f09270a050a0507020d21060b04080304090b01110601 71
    0x80e82156152505c00c0c0c0403404850410160008000504460f0841052840c10846022074600107500450050009000c0100f00c4800c205d284211490041214411048001015065881c50044110140c0ca90105c52200740c2c000c40480082a000c4901c84080d1042c01c951100046813820038540090081d90602034200e0042030000d0f41c000c08a0b81181c21020300c4000700d0b4000d80c0103c40750fa00000780f0384000300060103c41d500071160b05020495814032020315031620510301c00715040080005640003400700c12800e441044a00c0071010f0149510b07071602d65601c400c90b10400a02000c1c41c090550903140500841d901c3c4180990028240130b8443d05000015003608480d40305240c8a4500c1c100c12000b249110f031003440441d5000c10b5900340400408110303200034001d4030843d00540407450a403508120620170110200001d440c0d40b01068080d50020101364000001003200010002076000c0000050815143c000700e081040e1030928005540c2620301c400612416004800100042c1d5442 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 470551097 1250 470549847 470549857
    0x10507091d190b040e03220602190804030b04301b051f1506030501030f15060b1b0d0504150c051207080c1b0609280b0315030102040f0902 61
    0x44002040702c1c40030000150030f4a410b070005140300e9001188802d03c0210032815924248087d1404105942c24140002e444582540c10524203211030584001000400c00441d002550001455031150070240345c00d030b10640340810024205441605005448601e0070240c01485195440713a400078000c0c8008000c1382c1442c0301080d2060702400411f0824003102c0c0d01d8816118054090020f660349000505102c99001c0d5040042011b191400500001d050404040b10443e04544111401c00310b01c01400040c1c07480b6046400102c10106a80c105601880c03e01804543c403007050710902841a00116254003482c80340c50113600142212000040c081c115480d01280141d0030ba4a0541c0e000d80c1c800000d602c0004203ea04810001e05070495440500c10000c0e05180114100050b0281d80001030f003074014404030f144140200402c0803c160308046191042280d0507034101d803020b903544003c6503a900100d0708000914202c0740d14000610b410b2080720709407a100f80c580c01d11203060016100080d041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 470552347 1250 470551097 470551141
    0x1504020a09150603150501080a050405100204081b040507090509040305040506040f08010e15011a090310021b03040b0714030d0603050c010e1207050609011b05010507091d 75
    0xc150300100c0d4004040c015624600c20004002030700034688680241240c003028803402040515450501484c0c1e4808442074015030710b50004101d0307403514140301e410602111041c1004a00c000b0380000c01d100042603c0f0300442502082150721072041090105442c02154401d000410030582885a46061120a0340107400392620b182040e8545020402a500c1a0400d0b03003c3c51081000f0070600300240195614140a076015011090b0302aa8803405c040c03040c06006400d04444080c0c441900314407080e214076442c02421544041c4250704110003c1d03200c00d0020b4040038006c0c4070100840c4000003203c040b10580c610040c600070740b0391103c0c0184200381c1040f1142e40010000c04070907100a00802e80607500603405006900003400000d0800f4041d01c8400d801260303041c3c04051702e420045140e00854100ba05c49035641c1400c40e0048410300080d80c0320102083c1d03209500c60074460305500c840d00c2860b05840e402c11080c0c8605105000c8860342e01c00084122400000885600c0f000d00d007041d411034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 470553597 1250 470552347 470552359
    0x507050706060e010f090e10021e04120c21021c02061b07080106180b0102010209120f121927091a010c05030301120807021e100203030603150402 64
    0x150980d14881915039643c04002c90150001c0140328421024161000a1040020801c1480344c0003038019100c0303801001c4c800c2016400705000300c0c411503d0851070000310500c1c84007656151242c44844903003c42c2c0b401600c2e0440c2590700465070ba0300103c40f5041400401ba138100b8013040550170401c440e0101d400320080100c240c0701c03107401600d40101800c4a680081b000c0c400c00b01c050427500303240210f6503002031080d0381820010041c541e03a015400c0b54503002c040c000308080ea038450050b80680702c4c506089401c02c00c3c4240100c0e0880c0081109803880c074011007aa10015620310401155000e40c0d8118814501d200c039400c0099402403050f43c1c1d090341e4501000000444907654610502d80035404030041c5a15440303114109083d510603040440401d0a102c80307501c46d292581607403030005028017442041c0b038451031814002302c802541c4a20b0307401000000306035420603000110a91305140716010f100c00d082c42d000c0460001c010350384103d5029005040b071403500c096030148998082c00590b0045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 470554847 1250 470553597 470553607
    0xb0301021209010524010504061214010303051c0212280509010b0a0b0f0720041d010c0c0519021507050703170f16051c121103010b030406050705 64
    0x100c60101280c819010380000140c6450021141010704c51060b4541021000062102172142e8210301540c0541d10140340c481e4000b82d02c40c0c0914014600781040c440007060002c0000101a032040040903068182a01c18210031681880c40741070f402030324184021351480f900041c40768500f2101454143c800701c0741c1809003c2008071a1011198280c68410742da9441d003003001c2543c102510064003c0154122803407030002603d0100100d4024000000c2440d03540a01400805070380183c4a40c5449009004200d802c802201c10600340742c401d481d00c4050b500707002560703c030700380035801c000c0e03e5917000000b03410281010b480d441c150100740f00c000c907030090002c3c1c0042c40071410200907101280c4113400605040b13040d404d10001001420640c4103c2000801517804c103185410140c8072014044244180700e0701840c545141030040c914115100e410a40030700110385c0b036100859030b1180362514400c0200500c000404041403109006203d45a0030810205002511a03449103034007410074a0194205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 470556097 1250 470554847 470554867
    0x5060706092003120f0d24091508030910030507170f06120a2616050c19060203030c0f160f02030c0105031509040c0f0f080706030e030d0b030102 64
    0xc0c91100b4410803501d00c00c00c1c0c448081c10f040041d051200c1c0002e180c2420400030f08030802240c4102c9000d007460030340341e0140900b044c400c500b40346800d542101c41c9031400381c0c0301d220040c020080668000000301c6601c000042030280803040b80d082c4100540490101038046605030007808019200900300400ca101402c40f0380c071000d94031809400603d11101d035074184041009448082d19002d031072640c20090002c80040e1125258000c0041140d0458201803440d1001c01d201c3c0c000d04050203018034007001840c04005010450301d00110080324440600d08884900f0050041c20340101e00242e0b1041001c913000102800241641c02081034109103001c01802d490070441c1c0711b241c000c4981d1582c120030030085140034410070040100c28689a411880e08506911505990030752041c098141c19012806100001c00e00c940649501c00c7e200c0446503540c0014000d501e064801c0819034041c08d04c000c68031a03c45d011b01002c1101500045007003c40c550b488000400b84582865410f65003002043c105c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 470557347 1250 470556097 470556113
    0xd1707081911132c040302010b090411101e210e07030515040807020d050f0f1501081c0809070e01060504031a0f0106120b09040b090d0e0303040506070609 68
    0x3030542642c01c650b1a030071030b00d14030880b03070120790480f01228941c14100405440c1c50414010b00c07051910789110701340c07990b0400ba07005142d060322183d040407840c020801445005010541054000d0b6a20050788840c040b00300c9401002018209081d84c2600f0741c00344035031050018410550140351040da80441c0956102c048440c2030320f2142c0540c1207410300b041032190a000e800a007211010714111140342507505c1200b00d1140d100000c0c402d030310001c050401c0c03002c100200421241c0200482e10f04540c2c0c040d01d00d64130740b004041c8c881d0380350203070002203002007011464410480c009440341c803c540094105a601580083c4201124480c88a0001341c940204200038000d200302d4681c2c0d50780702d09504040d161643d07841031103040c0380401d00500c11020b5114409504480d854541106484142c640700009072000015180d4041c1070102440103105c1c1c1074404600400c040c400b111a00c81c2890b90941c1c90740d401050040e0b141d0428442003113a42480c5c00142442440795034005200d200e9a035030801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 470558597 1250 470557347 470557361
    0x3070e0301150905070921030305071205091e0c21150403030b040c03090c05010e010c0203010e100513320607021b030c0f0d0f0210020f0d17070819 65
    0x1142d521a000c0c4040d043e040741c814000340041f401d200f00410303503144900c01103242110000f03042603074400010300018030a030540350f040024104244800c0c20008a000d44d140c40e0780c1c44004d68a52559440540f9020020704c070110000040c007981425403400a00740054001c2e034890000c0780c0a1001d6100001c1c56a02131144228441d4a001660f201e59038240021100c00b1400e540a16140010210104035401202c00c1140c40919001720000c9508004842d0000e000760000d405600740050b0340f10301180031402c3d100c1c000c4142020092541c89000c2c161001914490203003582c82072900401241c002c0d001c601c020032800501e4646140c05a0356210725041c01118100c0c0141c00416251440c9040c80b07648801100080b001002824220000030300d030000d5040349144250a0034089104121102415280b850340040080741880e44044019450304802c00c1c6044031401100c1d21001c2040c040c1810300f051515000c04c4405076512410309483c0404c0250400d558020000300d96106945079008540c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 470559847 1250 470558597 470558609
    0x2090a0b130302121b010806010c0b0a060b070b1501210b01050f0a0810050901231f050304030e03160605070f0618141203040f14100203090f070303020303070e030115 73
    0x8611081030544084500070101c11702070402800800340440c0d42e9101c8040656a90040d031a4105620343c5000e4400400c603950101c03c0c903c0c00815260140100710490b9413040f408041200700340c80c1c041d0011101c2901340413070140e40210804000b0350403092540721403102c0006041172450f0810180100320790303800080403070700014a120100840c09030b0405202004140036200784400b54180030741c0c51302c502c1101c1078196028440c55070300b071495640c600e203101006600b102c0c1c00d4407a412445004040390b00440e425004120b0f00c0c0c408480d9070800007000001c0d50802c0300c542526030308102e03003182c41d54040e41080d507103d84164a201c020038034900c540342c20381c400d61b030321225180c2261800c0552286030f504200c00c25004104000c4100308040c04883e80240d00c481d48980102c420301e480c08803c046041c0c184181c1c80703002d524040e200c0060b4020b41c000e484481c11511809200596507070f81e00340c240002001a00203102041082e40108800200c0340750080002c108812500410102031029902075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 470561097 1250 470559847 470559853
    0x3040f0e07170a06170f100e0c0d03080f090c0d02010e061b010507030b06040e1810020f0406030b030f070512070b030a0c0e01090806060603071205190c0302090a0b13030212 76
    0x400500f43c80240785022101c0010140c200308402803a81611500c401031611185500c0d40811023810f441030000a01c815401081c160010032a410001c009100864400320000710841c00318201d20f030001000c3d005000002c01000c0328004960045034050130052030326410400921000c403d204491020103503480d08000006880d03e0603440c02426038480d54000d502640040209100e5006c19401ca01c2d80002001860030062426805191074015030f5131440200340d101098400340384034020b00500c11140503a070140548204881010741703c0f120310783d40c00280e6001075410869810942c10b40c0320b1242d0303500d0690344801da6803800ea000f641d000b2184056010b946d555503502098120246120501c403c0ca4001134050800c52200d580d801c014083e240b06900202c005100244160f10346c02c008409081c05100605007400d0003c0f81c003400300401c0e44801d0404d681a18202d103e842a0303012070500070100d07006a0f142030f080c0f41d02d40e80034a8511460140f000c1003c00561904c1c008a81e100b803064000b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 470562347 1250 470561097 470561099
    0xa09051011190c0504050c07080c0d02100204060e13020d020c0102040e1602060c131d0f0106030218040f06090606050d0c03050c0f090f0a060f030b0303040f0e07170a06 74
    0x4141c10a00c0d400072011084002c1030000e0b000c2a01c0b0000328080d034005072000030b410b45400b40081c000d4000c0c403000800c02c1c0800182e280c2940000328405102c03001c00e808031444e85072100400e8069001303034010140050781d40d420000c4645040f8145402032101c0741030042c603059140324464240e0b0322003103407010765a400103401c011580c4030203840303a07108905655500840200c000001d4030f03110050651002d04002260112103040c0c0c110740c04005040350203125030101c07641407036800a080102d0310390182c10001c7c4000a0114082c0c000c0ba80800302c2000034240290003142000018039441c00002c0c003465950342e0100b100c000500ca49030240660b0b464035a190403407890300e8801e95040700901010036090905003c50030000d0b01c00d0740d1203608c8654000b03848030482c0002c10100d000c0445d646600122400700046d601c0d410035810030480d8070590301807150b182e40e80c081c15541d20881c4074040e200400c0c0c020400c000150501d541750014400e103408250200c0c4002d81d4144003005555641016541c0c0d18 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 470563597 1250 470562347 470562377
    0xf1f090b090a0e03030c130e01030308150907141c0218100c020d06020f0c100b030106080a05070303080910020408011a0d0209060f01020c1c030e150f0a090510 70
    0x715140d0b20044169050000646000100da207900001c0c0031007007138007404907a49005401030103c1c3c2001d007888421021056950f810001d00724a0142c60003001d29000303070345041301070030200038481c0300750b071b09440b80505d581400240039042c1d48942600034410321001c06180c095030960000b05600d00701c0c40034085c40381c001502046442800101684148030040d1900001a1a5001094405d9401840042e228065a4041d150910940440765014012411f181a40303210300e034044e0040d020164002c10020f5190320800b40c2c1d480c60104041c20b2540704040401c0000d10038810305600501d1081501d0404044c080604280d0300a80c02c9001c490751a032503504102802c0028014000c2c800710355032a82d0001d1500461890b20b006803942c2d0042e0b150502840c1c15900800c8400010030000e850400d102c50030304180580da10500c1e60440000f40200e90900d0249421081040654a41c03890300e890007103031340600111584a040f840c4140882d10400040503a10a40036900d512055210402e0650541c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 470564847 1250 470563597 470563609
    0x30301090b0f0306010305120a03020c0a05010621080405040e070f06020307051501060e0d030e06070b04020a05060f0307180b1207030f1a1509220501080c090f1f090b 73
    0x402d10364040d6210100402c0480c900041c070180120b07041401c640e64091141c17040307001e4840e000b00e010b481c0c0f04442150081041c1544884200c0d12a500ca2089800c1014072004003a2a00080540001d000380810711007441c140c0e02c00314802541c00700316988607590700ca000c00c00d5200c0354010400f580010410000303100b400d000c034198000a07003010041c15030500d00c01600d28041381303c0c081c0c081d00c4505070714400c05024084441e03203c0302c000d0450780c441419103040da4560b441114100d0054501600c0001c603814000103540302222003042c036500b160b8801a00f141c5289131054241c004261085000507410400402080d03880c401c4c050b0800b55151464001e020b0751800810510101e00c1c188440380140981001c000000300100c56403c23190044003c01e1140780200d85c0c0301c0d03a001041920780c2d44008012000d44816140c00081404180c0ea01c10203261100d0801c4645034010a0040004a8451400512503400400c2c20004124484e00d079980c682505a25000014115a114502907241c41c0038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 470566097 1250 470564847 470564869
    0xb07060f06030f1112060c041a0304020a0b0c120403121b050c0123160210020604020f0f130e011a1c12200105160c020a05060d0e030301090b 62
    0x80a00900b89590390f50426039204400181c00c000340750030500d08640d01d8049252492103400d04851642c1080038035426283d10600c54225401c03002d0098406013540001603900c43c13600200403500762481d00703010f00d046600c069100c4126002e896001d12000402c130002d08080c60151000300880b1945a07030140c103201035203944c010a50511810040007907400162503103101803c0c81c200c2c0643d00c900c1e41c01c00800074030000c1c1030820300c004168850010751104800e000d0500031960102031607550f44050362213070350a4a0181d084039101c9030400050421812912046001030310130640341d182495110121500030007204026512a008400c40b045100b0b00347c1d001000446050b0b0380145112170310300941c1d002d154000e18018205206d10300382805848418410082420b9101c0b0141112481c64000e000440c0d03c1c01c0d4a080c0c042d000b600462040780c50788030207a03000d048801c03110f04080402425030400f60118901580300c00c1390301e0f81c0600a10195000f0f010403000400c0000652040000306540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 470567347 1250 470566097 470566121
    0x110d09261b01150b0903010e07080a030816020607050a1e080402090c0a021b0a08060a0e1c020d12150311030c0303131406070218060f0a230d05070b0706 67
    0x6110080c841e01c5154507015007120608130020f03a40d140008042400b600304554018441d0040c0000011507580110711418400d00c641c0c0e5a28041d9290710152008509007680500140d00c40030018066034096001441ca500300e41c2403141c0c4540340084040b1600f000d0403440000104002c0a200031400d00522316500080050801424441c4500f00250344800e00180340182c0004d032403080c0201c1d01c4242007180504000010b40300645001200031002e0002496410356074414000005a030b8821008000000c60031035010340b4920b0742c6103604981c1d284462401034042d5660307069001002c03150692140085221725414000400001d003010304005440e00ca00d802030b0030402c02401c2d030408101c1032409681d40584100d0305031600e400811600d002d070100c0250040b00c211000ca0072003a0941695110311002c03145094282c50440c1403000755801c0c0d00c10f00c0e03040800780c0d21b24100d05a0020301c08000f00c2c000760240325040003545866142c01566030286d040b01500140c5001444201c0c0286105018 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 470568597 1250 470567347 470567351
    0x2030d200703081905040506041b0605030408070309090e0f16030305091003020c0303040b090d020f1c0e03010908040521060103020402090607060c030c0210110d09261b01 75
    0x40d03640648149104114004042002e04000240761462440c11042452070072501080710345000d02c0c0c00c5a8400c0d0665040d01c44004a2140c0001e83c0d025054850544c0c032550350342130842d2519a070f540c9a40c4c014400440512050700408a8220101d11410540c18a684010241c2d0721044001c0750030031641002d06959502107090505c003080e044003c580d4800f0741941c00703400c52140354104800a0213290b100c0d09590000005010078404584003074bd0013440100242c42c40302d8804001079a0b1403603564040c00c01764000300c26500c0c0080c0320300b5205003840800c1c1019000750710114002400c50380719810844a41c4400f00e0140071600b00b08404040801c405081c640c800300c00c402c035940d070f12841440000d220750340020f418545030700c6620995403441d40c002c2d001d00134405144805000750480030b1028005119820076241e02e0f40301809849002c03400901c5951501e000e03604440701804030200b0546000143c01e400441c119000c00c0300800e8905405c80c0e41d078850704030445015000c8134443d69400540c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 470569847 1250 470568597 470568641
    0x50f01050415060b12130302033f041a07200d320d021c0605010311160b060d0803040305040510031a040b04180507031208040b010e04020d1202030d 65
    0x5007003100d017160002c20222882640300c0e0715140407851445440c007001e82c00c88106070f40c124203408492032007508443c00010140d02e82d01e042d100091820342260050200f9218000c0c1000c0c060344c1c58041900300c02c541c45d2070a40300d19003058801e400286100844166071001460380480c1e039014102c03441d00128034000c0d50402c06550399400014000341c0000849400000301d4207406421170341190806003c40c841c1c16011001e415034400144800e2103168003103410320403540c04c0f004c1e44c141220036402c00492540c40050b42d0b5143c0d9403c041004003696000280c445070304000c600190003a40c42144a580c1e803e1f0364a0410050100041100102030306041c1070400300900b00c1e203507044840d41070b10280c800043d00e0540c480000e0152024110841400b50352001d40c00522001040c1c080507a4002c0640c40c01c00b2804803011519694201c5001c0c1040e41040014007003884180416030700240001c2c07c0c40a0380d80140c0b6001e000345071258284025900c0000d250105c81614007403038094420010480041c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 470571097 1250 470569847 470569867
    0x7020c01090e10090504050f010c02061009050604020c03070f12021507032a020c0109050f0f0616020a09061d040302030904020d020409020d020406090807081009050f01050415060b 79
    0x104031540155900310315402c1c00181d0f020915245038004044010090041d0309003420880c0c0c856101551050700340d420311610b500641d00000e61940507010303022900c0d00040ca0310900307600806000e08015403058003006002d09580c803c00141c0ba10034042c160482c14410149440c221180d0394581410540d0000e0695100c01e800302101654000d400c2c1c10041800c0e91142101762901e081540e0038500940018414010a1360028808003102802c0e250101001e84540400c1a00d90b10f440300940c1c0078103800c890542c2c50601401400300304c03200b008030344100083c40c0c1c0000c915116980142c05855591042082812100c001d41451f040c0303038a000340c04500701038030300030f480e846900001da0180760001480d60215429604071001811380c100115120b500810030000654000c1c4624070004040a41c049428840851900100c5038102e00518408003c0b0140c0b8000d4190325501340c0c1e01e8000c80a880c101d2a82c203000d8280710398807400c070900400d016010356004440040d00958001041840841c03e6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 470572347 1250 470571097 470571107
    0x9240605010f0305090c030f0313090603052e0612030f05120a15050310020c01060803121609050913021f020a0b130804090204060e09040f060e030903070b030a0507020c01 75
    0x1102100d2401213516607900e59502d2030b0049032040c96400d4401d00e40c6901501c500400541a440100078031805c00e190745003054025145103000180c0b06820039a900100a03543d01c1c43d4100701d1a050402d1000d0000c602c14620881d02c0949c800d00900c600d4200305020140d01c218541d01028003824032506001994414020b9140002d00c070345882d603900c40c005956191505007070002454000c040310341c44601410910065005003001e070103a503007404408590004044181c40e40d030159442182c40c03a41c0c409420070204299014101c05200c10b01074085540c0e1543c6d50100d118030580c81015101e43e03454414002c0f0910b845101c000500380050a00c01055400720b0f2480043c1d4004440c1c140315240e0b002000c0d851141e2650007030102400040000e02c52040f6006042100d03d1a2200c056401c00380040c000940000c4900505c078114501c054070001d00140d0080160400400c1164208400c50000c00e00d800d5098001c40031169020041213a03442460060720382c0114507101800c4907040355030000e08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 470573597 1250 470572347 470572367
    0xb0c030f060d2406030506060d02061c0209060a08060f09010b0403143c1204090e150a0609050a1b0809031210081b0102060c07020307090924060501 65
    0x44922884002c220601101143c02d4071001c000d124800c48503d080d4084000a041c18070085030382d0300417000001c4013403816000602d00141c02a092078542840324450303401a0310000c0a240019900780b0111205442e071201810501000743c81b207915a080c10000c024000401010351441112600014801c5125620503a41265031010b80f410300d008501d4038081c14240c4422858241c0200b0107017126030846241c0c030035500d900b030340d01e503400043c035004201030703142e803191036106c6000c0308100420450520f16911202100c5c0d02501501d594010244030401e0050087d01c021500c96260402445000850b110305500407050703c2c820000703841004004c800c0311823581440701c288101000043c509074014000c035115503505450741006440c0000007010802482d0154041c20310910b10001d00e0074059104011085005030002c000a030b81ea1b402c1170340e5a5103c208101d8143c0580540044d28164601030030888500c03032059903002c4209110b103038010428031701c6219590360900c0c10401003070360050600c1c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 470574847 1250 470573597 470573599
    0x4020102031c060504020310030c1e05010c0503070f050d021227060f0327010b0315090a0516090c021b1e100315060201090218040309080d03090b0c030f06 68
    0x81042c001d580264000300a680c3c025a0054000800c01003040d4000404030103481c441c0c8000e81075242c4480f140701d0400c00c180c50030703041400784010034400796015004002c1c2543c85542220300c0c1518547da0541c80142c5004100e4403588005602141d00d0380502881092801030300d031036030600042c0e094103014802c40e9007140e1081210841d50030684d0315664200c80e001c07000c01201035524100400c48200810003422202c4584485120240d6096410300489059040c010000c00f40050303042000740640030081c0c40191203128060840700010780611400e440c68201100c0c05010070b161503200b10541d5844100d030411504008030348001c0000c0100154083d40707056690791108803110000303420726902c003000c0c15440780c030380a0340e0006294581c02801c08802c031074241e11700b40d0341d076003c0903030a884100d50001e5000c03048442d036074242140011103da0060203440c1070040c1c141c1d1030f2103490800104d2148900040c0e1102045014000d10710722007504841d92015481c95403501d01510341480802030581 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 470576097 1250 470574847 470574877
    0x240815060d0f021608040f0e0108060402130e0f0609060708100b090a0b0f09010905040b060708091c080a0908120f1c050c1b010b01020a0312060b04030605010315050402010203 77
    0x101c2d128103030b054030b4002080d100c0d01c0c4240d0205060185060f005407003504d86000789070501141072416850114101c3d12807200400304c98489900300100350740d540c098508420398550740744084040401100800ca2048000b0701100c2c285102024100200180445c0071f009511040c003038104200e14003401121000c10340c040d10303100e1010009020101540c0040020a000b0682d80043c00b9600c00821100710242ca503040c449503144103010596000520300342d8407001c180079180c04118080c00a024001c0c3c010400c001015411141101000448009864560021501c81c094941100c080000b9100c010020001d040180c00f43d09200c1c03240801007100d002020441460300b940c401c041e058504405d1800703000500d483c00a09900d9007000c0803000340703c0e10740c0e9018201c115040c4911400c1d1881a4003800c07201100341c074192060f03144003007003040c016a61303240003802d4590b00b8058000741d40308660104843d451410304e600280d0a241008800c00c1c605001e120060780c002048440b411810444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 470577347 1250 470576097 470576111
    0xa02060f09012316110a0308030105030f070608060f12010c080f2202060a020a0c060e010e0603090c010c020a0f060503250f030e12160507080d080402040213240815060d 74
    0x61781e114466400502e4006842c07640c04002c03c540100614180d460a9040b40d1140101c0ca5407d03a070707244180304007008181b0b0b000201e44c1c030f41081c0610911643c0098410f4451214032280e25003120140c40c200d100294070b0f40c1c1403000444403107014a422005600104507540010300c4452411b05110500a100b114000385041580c0c1c02405281c0c5c042d43c102004007022981c03210b01030240144948a6400034002c0d0703220904a1030007000b41e90103905d01400400c1020603941c01074441462590041c2d9005211820008000155041c40c101800d0180d4955413203080c81030b02c2003061100455811200b842841a101c2e4465014014800b4403040c1e02c5c002c200c0b00c918140d61410715a101c1c0400c140384000065210a0520350254210000e11800849040030395440b00552280100200000040d406901046c00351410750050310003e0305446504150a64810807080c010001c01c8500e080010301c0400b2a08658102214980c8405040604500c1a41e05000181f040c481c481001c07402d41e40c0d58807 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 470578597 1250 470577347 470577353
    0x506070e1c0b06100c0b01140316060507150605030309090a020c0d020f0607090f0320091e1503030a0305090c030303070c05061f05120a02060f09012316 67
    0x40c1d07090100c01c61140d2807081c40307241008070b03241d60220b07030032030048181005040080b8440c503c1d80101c2d94020146105990034010a4550302c0882441980c1c9407081480f60081026404e1001000b4112602c48030740d11039440c030706019250080c8040f40381071490304408000580f00442220789202d4210b940110311b80e036031440f0100030300035172080b25178a1040080c0b007101c490700010901c81840020080303a602352f0350004103c503455a18010785503100d6944400b000020000602d0440007000070350301700c110080c1e1002090981504548100840c0c4510074440242c0a0018010790003802c04a58071480403040c0002c25075a104500d0400c08040d0b403400018031b0f2500501030302d100250010182e0b607803420722460091042400c01003c0d1194050200881d07400c100c0541e440031055016826403a0320380c905401c0000750081480501507900511542d04010780c0c0b4036000780144c40326010211344071124240010000040aa00d400204072001c90301803072040e2990545440b000f01c420050a0282146 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 470579847 1250 470578597 470578609
    0x18060307030e07150806030c0a0e04080c0114190c090b070c0b0c0c03060a0501030201080103141e01020a0306090b060f070c0306050405010b01030e0a020918031b070602190506070e 79
    0x1c4402c4690f80608500803448401c2e00c00e1190322503040307507100c2e65207455003010561259100000306503c8060000100301700d8801c00300b8a0b6000340076100c21400e1510032a80a400d55203c0e964406804c07080008026100003040c0c00000c210010440030800100c4102000d0600704490046418420307001c2422010801c1e403000510260801070021519080b0840c1310030760742c805006030984680141000580710512601c18603040340c5d0140d60f903400c10792031a01c035815803124102003c10755000d0303c6091403040046004130010005614001a51511184401401c03036060b03801c0030002c5400e005406241b40da811041d2006007a18065483d030355440c42c43c0804001081d41d000400441c00c040c2004148401036104440b110000c1c0c80910031000c12080d200e03111000203600a6118054502042c00303140203d00940a048d08401140c1c0703044054107802140241056004000b603000500a1046d40d07030501c0f01c2051413190685400343c0800541c3c030a130f11090028036003010440c000c003545907141d4a003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 470581097 1250 470579847 470579861
    0x912050d0e120a0b0103020a1203020a030e13050708010e0c090d080a0c0b1003051504021e0411070b150301111206210c011706130e0a120f0809031806030703 69
    0x7402c81d014020300340381c203034601325003407006a21425002000180c43c040180c60018501d60542c0505800c00b9075503010358411030014507540c0c001d41900715803003803610303603100b414041d5940707440700c081a42c03400710503800b48400180003490380c81c7d00744019025905d605060080c000e03400580103454400152040b0345000107014080c0c903541c1010240240070003040c440c42d0699000c0c1045d95a0100c0345a0070300490041500c0007908806c0c10200004440c1d94004440d403046401003000c1171401e5200c2031540290440003054685102e8041484100c01c610030900c269100c041d0000d100c01c2801c42e0303c03450706000e202d161040441401c000161070b655011174002c0100a03008803c4150b03141426a6a52510072502c10b50118000d00d00c10896000400002403080400802c1e0b203141c909030b65144000303048215101040d40c403c4030809000105180c00e0b5541202302542d5a503020419260002c00221001d817141d0303c540c01c20090039210302c80c0b511b0011030044041c2caa00e80c1e00d40700d04004800a04403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 470582347 1250 470581097 470581129
    0xf0e04050c011e081305010507081501050315060304020f12160f030f0f03050c070902071115030a0c0e060c030c120408030f03061909150905010b070303050c0f030708070912050d0e 79
    0x107230108010606810088250045803506150b181c2d100e0008010740c5c0c540f1055072a00203114000c041c0c907600349004001940c1c40f51024143e002008400000301c1d080e40198219421141c0101c03041040d495401001745008192181d50301d1400c92540e1180b050180c90104003911800b1001e05000500d805031044982445049013114a680da40340011402504107403803c55062145000c28007030f40c0b408a0344c803000c1e8020a0039582c91601c50010140040401c28961018400c0326004401280c2c1d4401c00b0f00f44000c2000051580d480241030325038104000c42002c2c000044007031000307000a880000588018041114080b5901c0c0c0b80c080014800865444000601c0d4070140004541a142d07030f0812200041119100045c0503203c10988050318024002c11603200418040103010a2107508a1074104003800145850582280c0e4019410381c021103c1c500415401d0092146e065444440800206400728003d003084c1c015986a030f071216501d05d0703403c0400c020801d08603910359554043e5850829 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 470583597 1250 470582347 470582351
    0x20d030c1e080702090a1407050c0709050f0619080a030e011407052b020a020d0201090f0f0503100207030507020123180405010510090b03040c0f0e04050c011e08130501 74
    0x426403410396199800b10790124002c1001d400814146c4141d0b000b49012904100e01216603540c4a4500302c1d010b0f0811800800d8038402c0a00001da40c44a82c4a240d004000c0002c000001c0d1074800140b2298846480c2d090291118030303101000141c00100312420361550528040c1008008000101c50200302d2003039104015400080400400100040c0d507018031809172107100408401410254101000302c40c2007000d6003000740e9090061804182700b81c80c451050601c03003074607134452526840154007600820000282c0c0072090005240c100640c40c01d110043c40c081d0716254150f9002400c80c05501402410320400248a8481c1141c1042c8581480940c089641c1c448000205410102d1002c039840742c0a280341000104642c00d00700c04a04802c041e9441c2c000f9100d1810f068803c195100a1040d00c00c00640807011810082c8401028000c080700302c1c56015904090a00c50308040c03100070102e040c400380507040340050725808607162556220b400c11000070b5070b1300c4030601451515400002c007554 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 470584847 1250 470583597 470583653
    0x15040609090e0106030c0806070305060111190c090c0c0303050606090a030f0311030a0909230708091906140609190c020f0a030801030317070203030c09130f0f0b030102030103020d030c 81
    0x40d9001070409e1040000d0b80c0c00780080d45811006540701c000d04c060314009904014250380604810031120000d2a04c00e0081d10b00b40350b600e40201c021182001010380c0081c410138182018036030305004aa8001c20b0448135280703020345003000104c03111210320005110781403c0741d03401c00385030050300311050700c441c000181c0355280320f10500100b00b0201ca0060110320307854000c100301f614050b6000160950394030390f51181c1940740d2040039a00700c40003e0a920303852017903000120502540110000f03405108107008102d180a100580301b010748020720041c0501845403c00568142013100341000c2d5410610001704a110344608030300382907000034640960b21030541c0c0001095488111903040340c0c06651141417810100365507000d40d40d03054501d40d0060f4070500220310400032150050000c6100103107400d10340b034a80207011040c0c401203e1102541c5503203015801c0150307118013039201c0f51101103008615660540d400601c0303103a51810050200000c00c180c80d01001246c00400b01a1840d65810034112 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 470586097 1250 470584847 470584859
    0x61b070b0a06050310111204050a1a0403030c020d020c060c0a021801090b0316090b0a030b0703050709090603020108130303090209091f140601140415050915040609090e0106030c 78
    0x9004a031052030301034070842c2d801004441040c40307601d00c43c501c1040b01d0b030316151440c05c1d4640d07c0340c03000e4015116801040d1001000404c0610207a995800421201e01703603181908005d0f0494074240c40d80c3e800d6400a15002c010b1640c00b0403101e00c8071000f04c072030907202d998100a16180c01074a0030025040324600c01d5018045402299007030481d4100c1d501401401820750078140c8518964010741d014004140080c400c008241e04021050600a0928082c441d680c0d1100c0803848000d41c1d00d000401d50385ca00703011410790f1100040002e42007114040c00302c03910315800200700e040c00070264442c070b1131044561810907210f5040000b080c2d40040005407941803403034120352501c00c490005003a4002c0024030310340a031607071301400820a01c1ca0904160380d54480c001580c0410b4422003003418071400f04400f15518561100c0b51030104120313552942c469210b45c06220400f03101000c501c0091106102c00c2101c0c40c3e10040c1401640c18400010502324518820a03000d4642030b04010283c0502103800300f02c0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 470587347 1250 470586097 470586101
    0x6091d071b0f02030c0d030c080c010b1003090c08030f121b04030c0e0a1506030f0b032a04020f0a0c03020703050a151503020105190e1e01080f09061b070b0a 69
    0xe081e001302c00395020710301890700700462182282c1c001000709003010306410204500b040a4403110b40304000204104480c1000140b85074002c003a08130100e5961007262042c0111243c0341c5000d00114001186800600d80c1c01d080e4901540b250060701880090002d0310f8000b050080304084d0401c01066602d4948a141a100041550080b8003849100200003040c0103491701802c003448199000c001209030812070110080c01c0a00014000640c6490840c840e980b000c000c0c034203800100030300540602a50015402803803806805081c403807070040c0b000742441c8400904444007500e07503041c141c2403064945026402d14900b82c0c409000c50003021171110512260761440d0144001c0200104030502c40100044070890711400061700140c2d0507c081c02c01c0c9190700240d8030312000142420034140510100241d1036004442d8184000034035060028201c1d60001410390b006000381c0c00928091401402080d0b40e1500180400d5808a04440300e00404102008684869401c00c4030a602c80c9084080140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 470588597 1250 470587347 470587373
    0x105100308030c16080c1c05030c0d05090c19090f020309100e0a171306210b0103060e100509090a03020a020f040905030c0c1c0c090e010627050106091d071b 69
    0x40047c0440e030680401e407154007124410703507c15008909100c4910311060040c90000d0513000e031807161154203080390740c0320a00912481c1014100110285c103100e180401d5441c1c03080d80e468a1801402805903018022429100000009400095503652100d03070710714060b000b107406803000308203505035001000007400404e400000c4904000c1c2907903903404129902502c080a02d640040c10004c01010071b6031a8000c13203000001490003140c030684517041c2c0d290442040d00c4400e000d0039058410406406e011303020035400015040903090707000140d10081e4440459000080c801c06001c400142a69030300d500043c4041d800c5400c0300c1d1a540c180348020b0384d407010f01c56424454900040410540d0003454023402c40325601804c8c4803800d5240c0114070002d85450020b4220b80e54a500303010406001d003116203000e5440400300b54692010040e000c00840741c068000c4001c01c070b000e11080c09140c81c042c50324540f000030354403c0440d541c0c510004648220401410b0070a82c102c00301d401041c0030304c01101034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 470589847 1250 470588597 470588623
    0xc060a03021e0a0c06050a02040f0803071101050405060a030e160e04052e02070c12080d051e010b070c090e071706310b0f0103050105100308030c16080c 67
    0x4071507014894200c400ea00074a4402e03c0001c0300d0410781c20004015411040d0413500d581c0c000f60410380c45019003100003c1c0c1c1d400506555001049a000340540b0407204e420101e02800c01515081c00c00010031901c0c401c03625038106160b02c2d841d4032a40390804200b0175200729051104105d9440e21a01226804c4d00c0c1507405a034584100e0440482d104c000f9400808021410100031004ca1a05642d603000394008040680310000c41072400944505d1848a0310383c914861307800c0541e15400000d0000440d5005000c1c015508104090b0400c01c2d1444007030315055422107000c00c0e03103039401450001c070001c5540d00504c1105082c40308110b5441000107403d015500c0200c4010b01c901302e500000f5980700802c584d08a0100150031120820141d420300542449440c08215030f0202078640789c42c041c1d40000d9804442c1090103200400600400b8801d95400421034000c248826140d5100c800007400047c0c201f000c585000605e0900310f440c3c41503880b0030385034041c0f480c0b034072824511007440d00c40a00100d11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 470591097 1250 470589847 470589877
    0x20a0f051e0d0e010c0f1d010507060c02150a020c060a0209190906090b0f0a05150c0714010e09060d0312060905091b0907050d05150d05010b01020f01061212020c060a0302 75
    0x10304901d90203a0008001206d5030359550a401202404d550107140c46c01c0142418041d041200c180807070b4860117845d40031102500100f9004070040588600c044000707020704040c82c4180310701500301001140c041c1d0065003030200586c81e10440d00010b80003a0030b18285840c0100a054002042c0d04540c000380c0803114800010030042103810140040c482c042c4078110341c0304140040034401403400a05560448480007550760405d40c2d030a08040ca13103007890300098664552074444002941c4e1101e05020062010b540039059401c2c4900400c10881540500405008100450000360102988000c0c01400e1500d000d004e14107003d0a0652506d40700b5214210044140c038629200742440d48410707010300b102c2d0f91562314100e4110131100c014500580b580a80d40385001d1028841c0d0756014140c80d195010b17100008140664000180c9488106034203003115034101002084841d51b80d842d07540249401c0707104208100100704c41241000d40386a400d076401000451000170a40e410b40c00b07061481103a1a030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 470592347 1250 470591097 470591111
    0x30b0d141612020d03170a0608060c1c09140304030f020a08030906040e0702010f1d010f05060a0311130203011806080a170a020c030d03091104020a0f051e0d0e01 71
    0xe07001c0500d901e004000c080d08036082840c1c010b04140f144000c82074004d2a00b02c032032030000d0740b4802042009440b1135041d5515400300340043e031020300c02c05401007031552059141c00c4203c00710840c164508880d42050780d80d10380150043c84501343e0064458810344085d26540c0e5101d150a0650015120050340961400d0b0000300c0c41d01800012560100d030014080b40c00c06281841c51540d040000380b40300215500c0d07142004c00c50304c85003e6901c40c128080c80841001e0107444c4800e00719132410b040c4000a41c2810180962034560003061000e03281c00c0100c003512040080c022401581a80004045c241d100000001d41138411310aa02108000b400b42130061513559100710381d0300e5103a20005020030040d82810075104071150010042803400b40190f80510140c45d0001c0d04105260007480c0109840e86500d03400c002c103010211100200860b41141880341d4160020b021248402080b000c1c8880010350b044a0f20301100c200e81685042e00f55155514040303202c51000c2c28035102c0700801ca42c02c081c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 470593597 1250 470592347 470592373
    0x91606030e0609010902060403080a0e041109040e28170d15090203041707151416090b070201030c120504050c100309020d1b080114040308090a0c060e01030b0d14 71
    0xd00c0903c40c0e00203001500f01400c43c1c8440c0010350100c4100402d00181108941c13344e180c41c083d20060080340710280c0c0d11030360f0b0a001e10081d65034444510248e90400c032880380b82c4014074502600c010000c03248010820101d8940ba1028040c2c006040d410b0341804640d40304121030a4000c5d85220b4030641400111036aa100100140e02003510001c0c1041001220410081002e4001d045100c0c09031404403000985890b00100b22600100b036820b0382c0000d042086940301910010200c3c0d64203d150021055280c00904181d078060403800034101a01c4c1c640301c20f0201d00c2040304000b81d00020808114a05252501e25074400e1012480707405458801c80742e118884c024800d134004280c02404040a03c01c043d41d400340400892504424003c014007030111381803000748201ea0000840b90f4403048181841d0801400c002001081c06e130305a8804042c0d440019100501da004071202400c2452405e0003001c0181c1c0a4207044503d03640040c5540c203014148207140203001060105841582d41c4401100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 470594847 1250 470593597 470593601
    0x106090605182406160501050103060b0a0b04090506010c17071518260f1b03041206050a09120f170c07021c0204060308131e0e091606030e060901 64
    0x103c0311000356081c001c0343c2d05102e80760188103860300001000d007440c10800010480340b4201c81001a1042c0c0e54a030010300c10052a842824080034084451040ba28030380000c158661089010380051103464001103551640200c071003c460030b40c45031040310703030750107412100046811804040d01c602c0b074003200d400c40c10304d103074070840c030209040141d4070986e030702152130744408401c0d41103011220340040001400c5640c00c2c040904141602d000b041a51445505c106003410851089a10300c2500100000c01405220810a03a0380c0ca03400840032035641d071000355610092000010103040c0c50603640701070042035844181545201c203103480340d200e0807076120400240c086080783c00914540d8104507110161a0404203210071160b0740d00021000400c40c0e011400b504c0c2240d10849080760042036094850b0305001400003d0700a200c0400d40121036001048130791001481351030000e0600c500460320050b8280107965100b000c8408010030290740b141d0040003032140b15500515030040a010131ba80328018 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 470596097 1250 470594847 470594851
    0x90307050c0607022b0501111c050f19020705030f120702010501060f110c2e0f050d1a040903090501090b030c040312110f03031e060306071d03010609060518 69
    0x50f144810116840c282074174407602c0c3c036091000c0140b84d940103000044003400740301681c0d0800ba640a0b182c450701450012001c020302007441646051408000b1851600c3c0d50803a40030310310001056403c0d00150f4040c00921903120042c00724000011400300326401d05c4000c20f05041d11f00e0700b030041d13550303440390032401c0782e40a00825000508880030109558032600d038006c00c84001900383c1d0010b01411000071000c207002c0c114881030f21a1480070607900e940b4481c6100c614061400c08111031400340400038038602c100d110802000b0f540e100340b95480783c1042c04540f2195400b81c010440e020560401520080c41440307141e00144400b540404d0503c01d07035080da4040c2040d9106c160a042c01c640c0c2d200e00c04e481c800300c050100156518803c6802204000f81c403840e02101c400341da81c4c5c3c2032072018130184807050284103029003082d8051210603100090582ea200d20207142c2030220707440101440808040301c0c0306255056081240102e0103502d00d40c459401c0781d4044440038005903603040c101800e0042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 470597347 1250 470596097 470596099
    0xf15090403030203060301020d051015020d08010b1608070b090721060b150307090303020d0809100f020d2406080f041205070b2719020105180405090307050c060702 72
    0x45200030a0000c2d0182d0080c1d5085540100050f041c010360003542c000704c1d603085803481d00361003070520104414288118101c910790300e00d101800e00c450143e100500401c0040c855200c4025001400c0f510895001030740303000095201c03c18079516006400c01c1c2840c4c0e032003170b114a82c4038016840009044102d00000c3d1a8003841c10013209402d08040c0c5912004144411959401c400d8092800d41150076100c011b47c8201101c0e15806260f50445c280240744c0500b1a500d401405145820700540c0b04000440d201c10680c5c6c0c09010a04448058554001c1d000301c040031147c0506100c65007680580f02d00c04c4000840f00001c0c120940c0b81c3d201000c48500b5829070344890b21705024000714020490341c001132207981c207042c103000d454896240d072a11908030040b00c5101544400342c8001c3c2e0804840500002c43c1200c0500404030b0b8010400c103610340204482e002418030100040041070500007a47c203402d00b45000f0010401c5240143c50240c40c0c0d480003130111140c3c02032540d024090300d007101c00e0740d4556030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 470598597 1250 470597347 470597359
    0x706020c010f0302030402060d052706040b010b07050705040f1e050c04170a0f0c030b0f060a062f060106120e0a060c0c0b01091a01110613020a1505030f15 68
    0x700c0340003d0f4001d6002030f0081c1e070020030801c002508001d0f240284da010315450400081000301707030885003401c40c900c0740c041c1c45d2503040f80c804d01000c41c400e6002281562a0340c10304503174641552801d2454210310790700242e0001e0403c82c03040342010140d80304054100044048100401400051004a49003114001c00e500c03401e10040c030141390461944481da803201011074200c3e9400e5124140c0c802c0201d90116072144082070107008200c00d030f041b4180c00c40c0c20885103220b10b0400d5800280c02e1022802544100107420300c402588099510119000c941c0b0141500c10180008c881c090300c0e45401d016100210b00521540865880680b19480806110346d0141855142a0f40c518025084040c00e01c410403c05039030000101d925458028002c203540b9000107a089608030880301d8110b03154542c139041c80f840307210040951401080042d030000100d000da4003102c403c0e00c00102c0081060b00050784410902c0198070300d46410038000c5008a060f881040c043d076907040c030004242c005400314603400c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 470599847 1250 470598597 470598617
    0xe06010f0308070f150501181b030506010c1a04060b09091c0509120d021b06041703120a270203030d09170a03140901060302031f020409180201020706020c01 69
    0x280b82c0c0c0d8041c01425100d21041c6001e40720300d0310344040a40e400410b40c030070035076210010088000541620038003511802001e1040705400c004145401081d035413120189a01e503000146246e20172185568015848121404642143c5c50300c3d2004400032101250f40303078500b0040c0071007440c001c1d505600c1800c4c410014001e0203110000c2039980c086507140d1909001c0e09114203002544ea484038410841c0c00500103102c5081c00030002483c16030801c07d0048110003500c6980015210300e021602034840313001080c1c140786a6600320500e1032048650320307100c0001403418080c01100036000703020351041902c0c0c003c0400b81d0302d08000510a070100b0000358507a10410140344910115008014494045d58100c02c0201300708040e014540c1c441c008050010381d80e130400103440c00f55000400d82140c28a07008100b1241160b020958a40c8200f4940c2e414503212500300651030170301c1d01102c0180001c072800340031074601c45c034003590105804507003213000d0b02400d43c020a4403031000030809442081652611208 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 470601097 1250 470599847 470599853
    0x30603070801060e1609151805060a0e060306062101080114100315060f18060b0c0a02130f0c03060303020d02120301170c0306041212090302120d14190e06010f03 71
    0x12060017285401441244400040d8240c1911001010411107403103810300400800c4074030010014603042944112014800b11075010350101d101c05082600703845a599944500001444034040d2103450b55209280040005130011003050340c90485007200000d20420b8640302c0b00700042c200498515507201601e05007000481c07140144480c1c00010b030040021303200d031200400e41074104960400b41c649110480d0581c150f10b00d600c5860010410744d08050708082e48140143d403111041040a48034034a10411820741900f103a102c100f0719105006c08000c0b9800c04907019002d8465403200342c0160040440f04881c140c00491040341a4111000451440c0c0c00d096031000c450010308aa440c4030300c50a0b2201d01152020032915004600440710110414032428004000313480e0141e401c030710306040c90203100c00641c001401c0e60642c2100040c0f1600d0340f03a6100780310000c001d052300c142203440d58001400340707200c0c5000c1c00320b0b00c00c0c440312405d00c51600f1007a00559110020700c503d08031a40540d0041001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 470602347 1250 470601097 470601121
    0x1050106031e0c0e060d0b0d0804140303031b0c120c0109060e15010e09030904090b0f071d010f0e21060c040f031412040b0a0306120f060f0f0c05030603070801060e 72
    0x51800000c3c400108407807c01d01080302d01c11030140c03c442c00d1800040a00212280b0461050710b8001200158038528100401031180c00010642c80046580424880b1110600380103210507200c0250600744c40d1900d480e107081c00780c062000c0a43e0f1491503d60b00204a610100c0c1c07051030070074801c0c444a1141d00c1d11201003403a05000704250350700d0105000c0c02425a4680c003c40341e1071801078044001d241014003035034860b01c0b0041c0c41c40e001c1c4aa01e0840400781403000d00d098a50352404d0900f1059081210002d41c0c8040054590340e0703018494025002802d020401d211000e0f0314100304880302645d40b0a06090356101341d0081104c041740e010400c01c0041e0303ea0188036501c0c40608240c6002c02d440d006d41881c90742003134000310903034180030805004403503040c45014010400040e603103050a0558882031301c881ca50707100c0a41082d85843c218600001c0c1a0080300010500c00c0e000c0221100e52840202550000d64051707100380034000d0f0002700500c0501802c0705446d6203000d501c4160b00da240385182 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 470603597 1250 470602347 470602357
    0x20d0f0206040b0d0902091005010f0e03120c01050a0b0915150d0e07030308091c0c03090b0406020a170a080f072a0210030c050405010e01020f01050106031e0c0e06 72
    0x80c1c0004100300109129450a01030301c00c03506100c602089854641c0704001c80d0705030040520700682d2291008201d9a0f9003c50780380000402802e040340000c0701440480d0500e03080641610100c400010252003441056101c90300c2046010020005c28518008011440c2400c4d65000e10042d42c4c070181e0030041ca0700180d29401c4801e91005035180c011103051140a4683e4940142c1140c1c1007440d040042c50b820920695002c1c0e222030281c001042d42c00c1c01e1032000781c1c141041000b00074507107800c101014050070161001e00160f9103125101d03a40c41000a603500507184080301c90075010140078004000d40350603121080c00036100e00880da6900710f0488150400100010100401020200842c5407410060001d05107500380301215045907005001c281901080300c03104040c98606080081d035404401d850076100d00b485c03c4074020f218140100d00d441d201403002c4046506c1c2c83d00010f442509940304a0041d071921361204108000227500404641d1000008004140e81030b8141b031042c50700c080100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 470604847 1250 470603597 470603599
    0x201121e050412020f010e030d09140114160c0c38041505030603060c09010221030703270f020d12020f0c030718020c030f0a0509010806040504020d0f02 67
    0x80040c00002520400755001900c003a58980300c80c88441460300d606010380108015084000c4c400001c103460310315030324031a45c1d00002d46160355240d15000c12030002100910700110034000e201c060b0501c40b0b00c01c40381030b00f910512020f00c404000300c2c881318050500340ca1040c0e04810a80f14540c0b9007403601c01d41000c6400100e4050700d20207611012840240c000d02c40c000700000406448606050540c0c4003140c0c204000f41c1407040510402c1095034000811681c895001802d4640703c042c400d0040c0d03d41065942c04000081500c41c016140d012000055031003103025580621880e07548901d072060880c0202240c404000e007410703140010a8910b0f208107421480a0300d12403c20f03055449103000002c0e84641c8000503089001038240701103082045521150701207000c0c1480381e19280415011840492000011940104002c0c285031820700960300d0248802043e10703030300d5140b01c0004080394030003440540420301c0c90012070558280703885814400c0341d0150a51018882d07586844171448400c2c4012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 470606097 1250 470604847 470604881
    0x50a08030a0b0a0902040503011a0607060c03020d060303020c0901060f080a0c021207110a08010621060912090609080615010c260405210312150a030c0305010f09020112 74
    0x2c65880d2501c031001c0005211200c401a10395041c90109429500c0061584100e410704810188c2e59036281802c44003070300d610075400550341c0b1010406401034050f180040031a0391610000009164003c50091401001100c142d0100ea80303e00c4181d409124802d8038000090110000809003c2e036940a240e01500900445a406090310303516032565012640c11100d500420125902506201d10304c1006820984000c0c17021f141080d109541d03005030320b42110302940d041d40a4400f0f00140e503005034049500584400380400c00700c03401600884d064840c40000880a680c0040c0c0d624021822502078000d500385100740d5007141004407522007441100b565110340c2980101101e2081c6582080075540c2d01c081d0607240c078a44401c0181450780307200d486041c0c18070203e44c002c24000210494132400a2440b110009465a900f07a1034801d0102d1031a580003645440f0210a004c0b01502030320031203102e10000d0010011000c0800e0075907080443c000c0c0400c01000e40098885503079004000e00070013004c00707 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 470607347 1250 470606097 470606111
    0xa05210403081c050a091203150503060109020301150c020a06052a01051e0c04062114061c02090a0e0c03190c050126070c020904051e0a050a08030a 65
    0x4070400359100240c0c800c0e10010b06502d00c3c061121502840e54401150314003002031442070f446100306408142110780c20540e85442c03000080000304503030f41c080c10001e421204070790b8460707514600a40c000e00900c600301596043d06840c082c403903000035607150750140002138098034162041e00c00b9003140080500d550f03030121403100e150641c0420b42c00d42c01c2c454000819103007002c091540b245d03c104141010220003500c04c01100401110456048070000e103400307a40302d80100210090441000c0380c0410042c00c090400076040c4010b00490b00800302250b0310b802d01d2103194804481000c203100001c0d0001c40020009040401030f520014008018906444090245000083c10405010040309540c1c40700c400c0c84081c8000710b1f45e07000141c5403e00b82042810910501803455510a03545041c0000d11100018072880c82044100e00d0942c3c098080d24450805140c59a240c0f40401c44a003ca091940c50005024000080e0080c0070b94001018220410540d11024a260720003040070681985950b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 470608597 1250 470607347 470607353
    0x12020d060f1401030b0709080615040204080601331704050c0d050601090c05030f1b070b071707020303070c14010605121507020109021e28050a080a05210403 69
    0x3800b00030030a5003104164540c150f18084101c6100586100100170211b03a0900c241c840005109400c07100d80341203141840d03c524009000392280c1d400c248480d00964000040c40c0161580484c0002407172282d845242d02c0c21010850ae2000315188140011044071034008941862099250420f01410554045600c48408a5601d0500e52021900c0b07a02a8004011014080c45a042c2c81d1806150a500c4d50410103900f0520020145ca150440c1901d0822100c916098400b101c1f0010307801800c03a0881c5c50a040007402c05140c000c0c40c150501e0101002480c490f2000c011a0f00c60300d1261546a911141c9854020050b030103880046455941c03680003244e242c0d1101c00c2c00a002c15040000c0c800c030102040050500d00c4080c2c0640c06683c14851103600580e10090704007194444020510121002040000c0701380350044442c61030414041c0e030703403071102800c0e68085040d220280c0d00601c102e46da802e40d803962441a950058442e0300507094a8814503452000c0805580301030f506141002d841f40c0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 470609847 1250 470608597 470608601
    0x4171c120e1606030b090403020c010503070207030516060e0102010e07180204090e010902011803050c0103020c0c0d1b050303030c07120c080a0201051605191821020102150112020d060f 81
    0x101c2c02c8024144041410040c0c40c0c1c2c03500910301c03680c0099480328102e040070b80e00a940c5504009d42035042c010044001000144200004401180c000d400c81d110039400079200d18015090b40070b503200080c1c0c051448000c41d4014041e0b00d411400304001030108520340f070030f01c6524140b4100e07501c0c0201c0d000c1000050040c040c5c080c007091003640e20300000d02d00007248000b5150040e0f5044983c4400c0d031845040000c96804510b84100550a0801580da48400c204060a020005062681c051682c1c0701c15800e10131031a20754207031940f40c03d1001c00c1498481c0101940c83c00704542548010408010200008650303d40c01044c90029040207810055980c0e00c1c410f15411081000d40140c0d0755008204030181c1c620000102248942419482c1419469000502680b040002c000340300804540200d050b030305c04010801404c50301149040071201d012031400505a9100c140d00505c10080040007070030f42182014100c540007010260800820f900f03002c40d0701303031441d807e0741c1c0c0c140e40c0c2c443c0500c041014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 470611097 1250 470609847 470609863
    0x1e141f050411180d0b07080a0f0504030804060501060203040506031603090807080d05010f030506150f13050f01060203090d170706020f070c06180e060f120304171c120e 74
    0x100c4205503d8107141c61803180c28070f2482072918415010520307088041003410703452075000380240c40c00c1d4800d9580c803d400703800b400e02c0400c5281d1740c81c544000c1006165106100c60300a074800c2c44140582c1e41d0320350b02207075240a68003400e50700c000100301203440158294080c010b034240301d0402184071640c540b110907898004d03c0060395034810014141c030160042e4402c20b405051700b8560000e0032411034036a140d981c50700400a011900c51480b0401c11980e5401004691030030051120703661a00040a81016160030b81d1a03900d400b281000100310203001206803138800c4006040d0300380c94452a296511841d1034940b40c52454481003020b40086017190000305140e081000705a991901e0750703d4404490b02c4190712000c104118031a2811000154404943c11070b00941401c84843c2c82c1c00c000603240e036031187c1c806035110506600f041d01c84500400a042141c880395203c2e070507c00403000c2c40e61602d100c219181c0b80c42180c010b404414074040e040d00308140c0a00f0360001030340381038020128905001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 470612347 1250 470611097 470611121
    0x501050708090d030c05041806180f0614010804260423010206010e18032101081605010f03020f090a2405190e180a1e141f0504 56
    0x1000c1002403520b420091200c1c080c0940ca810402c02c440c080008056000e54024600c401200c028028842c800e1031b080a405001240101d032640762002c0c40000c003c00354100358034045401c1003c0007800c24044204a150380006071282d100355500c40e950541c403003130701d003010780d411304e90307540e18070b0303e154990030240001c0e041502120288491642d9241524a2074100c51411075004900503c14001c1503111140c021440e501c100e9902c0303580d200da0034118060300308010a5410758000b1109440d100c040041c0c100c0e500c030000c0d20605d40080100300d115242078002d6a02007415038604284240c8240d0080c1820404035a10034140305196000814020803603104503204424000300d145031501d8810802e01003009824120704c0d0075604101880c0e2304130315881000900248030031125090301c418010000280c000210900d0514141009d0801041100743c0c640046a00740702ea00f41c82d01240c45881d40da412041091007a40c0d0720004885401c010180640b403e48000300170015240d140e5000b00e64941c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 470613597 1250 470612347 470612357
    0xf04141207021509030a11030a051005040209090f030306090709210501060b040f030807020a050a0308030a180f0611090a080105011701020403020d08090d080a0302070308071e1b05010507 82
    0x400781c0108480e45540d00d0145003004820441c800c0300c0d40d00020340c00b014541c40f075019450300320303144d00080c1020070401c0060003a02034006250310b007515507804148a540708a41d0500c40351180900b0a5503803d15a41e04607213940100081501403401503041540304030a450240c0d1040e413503c021080b5800c41c00c0d5105c0201c1800580f41040040c01e01980e400340010b08215428986422020001074029100190100d40000380c26001d40d260b601c120009001d01070710080c4500d649251591640c1d00488161181030329101e1101c0d507660785003042280443d0440080c85071201c150b00e0740c40c010b05054040d10035034102003141c1402da44480280c2c0009020410000400390716240121030131510710441070700f40c0c3e44104802d000580d84c14001e80401900306101075202d42e80a800714030204c000820140c91101e001c941c443c10264940c00400c0e44070b10035502c1000d9603c2e40642600c0c5030762500001e802401441143d04800c41c07007080000f250038180410294108956110342d07084403000d5030f902c00050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 470614847 1250 470613597 470613607
    0x617131b1502061501050927040f1205040303080c03090a14030a02010e03090d0803070e0409080a0f0903020f120a0b10031b03031b0609050115051c02090f041412 71
    0xa0b406201d49a4807454990320b600201111000082007072040c815000d1080c410010950005510304c4198050b5240e40c000140c0c06080a040100d842c1c04240e03411200780780150401021948114107640449500d41c4442080b80c4030101d8105043c0c0000780200003d2046d54402ca005c5100c825521006154010141d0b560720100b807802820b4640e44038400305140d104011404041d2200030102007105c0d00301e0030098480d103540e5011141941420035140e4400e06125003101480202c4004001480b442e8844a080119207081543c3d00c2e0514400a0b501840010004285080c0705090f42ca0046090342036851428590303076100500076080e64086c003210240c1380c0c1441005003034440d003410086a24899107100c0d24550300240f1901d26203c8100d490381d0380e600f2050411080d034024011a82d8041c000340240c01d11007020084140342d9206240c46020f10910707050a01c12210000043c1d00d80103440c0f066150742c0c080c00d02c400214060412281e20150403101d00310404140500003d011610450613a2a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 470616097 1250 470614847 470614889
    0xc06270308090c041802040207020a080601030b1e07090e0c0405060d1505010c0507091e09200a030201090b070c0b03070203120f36030c01050108070617131b 69
    0x4415066800f502862401158548080401101c00072269040b200580d59051a20108181090a85c01070078948038400001c000c100020384441d00c510440310142443c0b00400721a501d9003031065442c07102184850509026961b80e01d8002980402c20034645890a0794031804106950700060f03413845034aa45903e812030400d15030780d2000c010402407030481c0002041c0d45500303440703010b5845901c92640c1c3e643c040e6800c46020031900e180c8280c01e48410845100f8900346074030b0003964403000c081140111403001c181d0380342501c003070001c1d41d070103031356850f40c1d00d040083e0304c0780503031103d0004d540b12420700d00300041305000d01c40118410045a4041e548644000d0b440d4407400402600100681e20103404100c0b101021210944814900c600005014440c010202c0f62009508040c003002d80800918142c0c81501500501c1c12904490103c90700c1560b207410443d000b624400f06040301400380804070b000d001c418412520658005c0880c4003c41c0b0708100c0d9200c0b5007a40ba40000d54045505602481c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 470617347 1250 470616097 470616103
    0xc090c09133801020c090f090a080f0c16080706140f04060c060b2205060103090204020d061d0129040504021908180c13090b01060203070516060c0627030809 69
    0x303000c04c0c0000c1c0154000000000c500a2008044134142e0843c2000030f480c09508205180a10ba04030780d003295122031402201165610551850340240310744200300a0141e10194540d00312005400600032450401104555441401a0400510406102890001c240301c802007000300010340b00c10303210f10403e1070f01c80300740c8288071089403150400c900c0e1801d20104c4140031103003852407060001120398034603006800821610a0194002d403011520701e45010a5901280c240d49540c940e0741c0c80a4418440c1940c3d00c00c0900440c2c82410244000325440c0c03004004c5ea100e503824a290f5113040907100d001007400c0f6004040100c0502c020051240b500ca60000d140307907003015203c0c00030208102492406a0b44040d4880b0306d90190341803c0b01000b0b041156030081951a174450002d441f25650385000951b25080120180e0b4680680d40a4140a902039502d01d011180e45441e812020002c03030721414010803024103003152041181c40c04800c9200e9403018401c0b102d1003500c3e40907041c10002c80241c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 470618597 1250 470617347 470617451
    0x7030e0a1509090605100807210506040b0d0c0e060111011a0f03010b22020408030408070608162a141609090f020d08070b010e07020c090c0913 63
    0x400616040090181c2e884400102c4000c401b02d050055090b10740c000120780617050040c01c840300ca001902c48408181c8d09030070950048004942c184900314052040007183c081d4031000809500c00183c04011540e8803001c0581d1000781414001c059031140c0049c00e007540c2c070580c940804400e6401008016107440c500c252410b84098000f003211500c5c0d030003c41d0505034411036440ca900c1c584070032030729001e1b0a5011103015003408000c1e6a00d96669541850381c1c0c02c058000d80011500301c00026000140c02074a007940002c00b565984030a0303a02e02819060a208188400c031f009441c00500000302d240d191030005403441c01802030005c4810b164882640390402e070031001c030307503421310031860302150b0840b00010078290126208040c6201d580b034200c0092040301c4006014065000001980500d51400d180c810800c0c1d800391254124008104104503e0031030308039462540138050b184440c1000507248091030900040000d008100c44280886140c1c01d500c0e0344402f807020202c011003000d220414072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 470619847 1250 470618597 470618609
    0x30f0312010501170f0f0919050c030d0c0f11030307060614010e01020303010b0a11070f06170105060f04060e0a17030702210601060c0c05100e100f0509040207030e0a1509 75
    0x551178107280c0c0d90303041d40100140410403c41d900c00003240c40070005003c03200d5180080110981d030403c20780b81254031081590700c860b01ca0701410030324030011805800e01020740f580c00988103000da40341c0e80d14821224640c2840e19090b100900406000425610030000075103402e920380070340c014003600010310940d00c15440604540041c0010051404a10103403100540b56080040640041c001c030710f854443c02d940300741a6121202c200090301c2e40c02119442403145200c01b0305c0101d80c2c0f0340082c080207205074002e154200310b08200c100038045c82071a5140c07403000000c0011040603503803522081c61003101c1d0000f01c942e030000200301c42107240000444074403001c00041e8001c4510355403821074440c84144209130504c5014180f590410041c03d00e0403018000003001129420103554006007010007a1054902900070703241800c03807107801114141618100e5a80b414500010b500070700c0007070b401078071003203091110700c07042c85600781c0d1031142c0b01000e000441c246840100842400070440c072402e034801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 470621097 1250 470619847 470619887
    0x50d0f08060d02062218150501031a03060a0606120b100503090a14160602031611040e03030c07020a1502070510090b030a0e0c100c02040b030f0312010501 68
    0x62416600005020352280c4201e030b421459510038008a115486040c544c40c40da00c0d501c204907080d10003012080001e881154420b11001403078560303010221440344440d4143c80e003041c03400b00240d40c86074006580c0400c01507001e070000d0200c50080381c546213094a41d1003405444100500125034002c01d0001c8480c031302d00d014803145200c2e2010410010070101c800c02000000000a01c4114040011014450703000400840800a401ca00d41d1502601c2960603400703020035070000b54052000054818040c042c21131706600b02074907940c001c51002c1d548411030308191201c400d07251501081c4041c0d403044e0303440d1301515907694291040046c400d60715045110035015007041110351a03030000341001170340d4050741c020b030403802040004d942500596001c4100e00340000708000d00c09180d5002150103e0b0510200c910000c1e800c8100240303009410380390000110748001c0d10001d4501500300380034401018055440105c0120902401e65200001980c0b6010500e4010802940c4c041281c0c482d04c4500606 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 470622347 1250 470621097 470621117
    0xf1a0a11030105090603120307030509060c0c0c090612010906090c05030633150703170c0d020d02040503030703090314150a05043305010e040807030c0f021309050d 72
    0x200c22203000601503d4000c0c0004400180300752804c0220581c0d5400c00b80c034a42e02c1c1e2030302c0c41c801405403204481031038043c018070001c50600c440800c25510700b03070640e03400740c01c10940e91400e010304c02000030302041e03105410785c803d03100d4a102841070ba1901400303588041106045801c01c1c9030301d10040d9004901a41c40b6100f040018458000c00310100801c0300c032100c0000303042c10f0289600000703115105074004903800c1c0001003240c02d2801405424840c0d182c54125804c900000c10910303004407500f161401d000c215400f110304a5500821180344007541c0103007040d03210f1002c00d103180c01104044001c241c1a40051051103280381d141044a4602d1001b080b002110201c2120745000c080c2c0158003054880010904005203005004991a41400254130314240000b4603c9040500e20070a007240b45040008903800ea042c0c0c4e801c500c1290000001480c0040b20b40c1d00700c072644602903099905494200410300141c0d121780b0303006644c020051000c54000d1060800c0e6007840b000b206104103103c0d0b2009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 470623597 1250 470622347 470622371
    0x103061205060c0a031103070c0201030f092303131401090909030507200d0302010c0f0311092b030306060327081e070807050c10080c03070c0f1a0a 65
    0x45030341d40f04903060200d5884184495064000d0710304840c9040101340d02004224989a00a80d07003105103000f6a03061004440048e5920704481c0510300190455194110046440c4c05450083c501720002008903850800c0d449140d072906600ca4101118800c0c1c0c0520300416580c1c010010400b4200320201000f19402c0303650050030600c10410001c101d80341440e43c581d01442c030f800c0d0b1080c00c8140070300a080310342000d1030001d000700b40d00c0c900800401c114a03024900c051091250010f24168244281d1030144803008214120040200c0c190000d20003174001c0001401400c54441400d2003a20b01160351800d100000d003e0ba80217420700004070102503056001011400940c440a540000c1a966911411880e548090640c401c92001100e1300290101c200000400201469800b520a443c0009800b030704105403d1404041c2d14005441078002c6080c000c902c0008581040650a20301c501403965543d9420b800015441590505004158011044106068564080c0318128104500c5410031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 470624847 1250 470623597 470623603
    0x90603130209101413110a020d031802030304090504060608160e0f0f070e040e2a0307121407052205010e0907030b040203030d110a0e01030b0d06200406020c0103061205 74
    0x344120380301c2d034000c0300d60301804c80311a800051140d606e1800340daa500d03401b001c06507895070040030402c0003d02c0d00c1d0000b000b000b10040e892030095401005945031034a8988440054440a8003d581d62955440002401c8404000f10740388050603071092042c248c941100071511010050039400c86550800030450142d402c0349003a03902040600b05034403e10b60680202d0010501c0c2030b04500c4902c2410089190010f1400040f00032083d00c50482e00b5462521040c582c80390a584034482da8580302c8240d810002d5000e5001000c281413032811190a1507075100010708442c05024084c20055601c2d69240768642d0340d0007034070301401c151080d00c0a030741132445915955042510000d010500e20102140c06c5560500441f0828601b525007406070340c109114150240e400540180302003801e03220102142e5001e4060310b043c3d000d0081c02c1c54041c02c1c0c5612010068502c200d50105c001c205502105004814440540301818140c1d0050134015903500000d03045803160f41014401ca0040012403000903000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 470626097 1250 470624847 470624879
    0x40b04142d0703050613060f02040b0319020d0501030614070314060d060605130c081e0109180501050c031807030b1807091406040b0d121409060313020910 68
    0x4006541100c0c544144090304040b02e54000a1180c090310084c81507040c60640c0e1004a2070044034104001941418008128031480c410000000300900002d01c102050000030a406e6004040152510340c200c988002110401d17082154050750710300305000390350200380b503c9600c2009414100504260718060191b0014003c2400c3d10440405800c0d000f08640d0360032480003014042e001013481005c6100f0726002c0c214105a4000041e850300000e400c10019a190300c0c0320b00707001000151140d08000c60035015101007042030800340f20100d440350002c0c00910581d0b00c40d00900241c15120300700f0884860949060044041142e8415070781480800c0754030300d0280d0004007040300d411600c95200d00c85401c0030340d558005034449203401c4010603005160b072003d40c441c030000c603020403480712000c0410605024480d0040c08528600000d19220b038040c41a44504c0d50050303525506200b480c0e00010001d50085445022150780d50f6481011820101c4c1020f400100040d20a0072080c18031020413042808 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 470627347 1250 470626097 470626153
    0xb010e10090e03090d080703111605060a03020c0303070e03010f0c1b1707050706140403051005060f1903110f1309153e09041e0203040b0414 62
    0x42c5440310008244108101d510205015041c20100009070916907466044108140c0205012641a42074940080780c00c0d000c040c0301210b400c0e01c5038100824880560130200c03120b02416400c2054910300e000810140d44101001c0c2d627040c0440009205250a48000c1c40300e4008e0075041c01785003459590410080003000c00c103001c54155070142410714107901c04243d0209600004005050018080c0103d4250161a010b4489140000701c00c0300d001903a1041d440040d0164002d80610500c00300542c000f01c0d040180105000f05c01c051080028008502d41c207400744602c40716502c00c02c2000a040b04403d42105d003100c1c2d40320450382d19400f060f4421404844841e601c1c1e510859003040181c1a40c4084181088031820459042c0c0ca040750360100800c20204044d11260321045082c8004120700914543c52501c10642003403911000e00010b0074820b05190000c403c01e10f40d1421280c0207102131840356000700c010b07200700d080c0380c01c0c09000b04c40907102c0710310f80d074025000010684400d04187c6460b170070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 470628597 1250 470627347 470627351
    0x25030b0609040509100912030c091823070201020c0c030304360203191401080706030b0301021b07061d0306010b0d090c060206010503100e060f070203040906090204030b010e1009 78
    0x521082d80d1814910880c04042c5c9003031401c4000c106110714101c54805814140e2010800300da203d02c3c095035440705510469242d0203504856a2075900d05810062011400c001403801c80740c17445418206512046480c100181e5001c01c2c1040c0d03900702013008070b2243c241074014600c2e083c1412154640e20114003c1d031841021021020f402d130302040c204800c2a00c032051411501d0b030610120301e01040b51113099900c075040c2040c518240000311041c80c07504030b410300801450741501d084400d40141c51786c0c11480f40c1c036550a10008008021a8050841213089078000d030000c0c0e4280840500740210701c002c03070700014105070a60380a64400007035031030640e010038050780e441d241c0342c201030381c00381464120041c50201a40000078a01c0e40003d12581a00c1d0210181ca100d405c080741d031041129051254981258004004601943c2041b00a107400c202d951043d00d250070744984105060320368907800045015400281001444803002c201c9001d8030510401d12a142014020b83c8072105082c094003424907 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 470629847 1250 470628597 470628601
    0x711070603060b0301091d07061805030c010c0311070e010b03090105131115220602010e010b030c100c080711030d05040e0402090c04050d03030e1203070f110307080325030b06090405 80
    0x1f041414880d00f2071002040301c020a49402c0028101c1919a210485464803541c021038a0b140c0454000b01082040e0f41700380c05035095460072100382c1d01100c0140d0882c0107901000c10320981d080802406002960031065036400c141d0400d900b141d2005000010081c8180c50810010b00400000000250200c540c00c0075603115000703c00c1c1c1441403000004103418420403142e1421155000c00d002c03105581c008110701114580c05a00361580d40b04501d43c5034000c4070030480c0926103a100500604c94900e00403503000180c0d07960038100d51086405031260706025036011101c2c94100407116046005140203410305190410528140b20003801c0203206d46296000129404140000c1e9001048002c000609140361403e000d002016042c24490490041c0c3d018505d042510000b142c0c040e0042d5a100e10b00135004141c01c0b510346000308412011070100304005c03408501e4040c06103009144070070549101ca00584500303c10440c501008078203040c200803410380582d80c1d00040e581071403000d98001c81c0759 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 470631097 1250 470629847 470629871
    0x2031c0c03030c17191a0f0d17030c0408010501140d11040e01110a0201051b0f0a0e180915041203150f1d090c03070308210711070603060b030109 64
    0x3e00010000d460302ca4088604001103a41e80301e1100300c0c000e8000c4410021801d1b030303225118902240d0304809800040614a052040c100b00074400007050041401e40a101c1b4042100001030b401520001300310000480e0900c00309000703215082c01006c102ea1400d4000f1042c2d40401c01c1d605000c0c01c0034240340d40c00d2511429030f8480340c020580c0611600000c00050090107840101900714205400041d03103803c000030601c141452a24100f074440500e550704000b80407140320080d0b440b00e500d44081100200728003600340c86410b080b440502e41100032000e240742c1014031501d400c2d200041610320117010818440450904035a4040420305890302144aa10100c0f00c0c140301c468507400080000395000e00060b2003110490070041100c80c1c06440c0909440d041c00d00faa80d030101a00e010b5143d000340c501000015110b02c0203080400481110b4a05214040030201004804840c0c10380403a400014540c408281840701d0406400c1c2c40c00c04200302800c21000c1a900d000c1401040e40b5207a880380380b0012 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 470632347 1250 470631097 470631107
    0xf02010b030a0c15140d090c03170307080c070f0314041703030f010609081005070c02030a06060816030507030209060d0b01091b05041203180b0705060402031c0c03030c 74
    0x145540501220040d60940c43c20038070a0340d02c2c2c403a0301d49030120030352204111031244c3c0258540321051702c000743c10004420780030f0000b052500c030202c44409000000200044d044d5000e901a01c0e8040301580c0c8a00e404540600140801004c0c4c40b211101000707152700240ca541c00040e1059014170308140c26800b40c403459500c41c0301e15040180d485044c424880442100080110b202d40e0300b002e80152940d07a00d08080d03078000d440380525407098004815004102d01c595101e540d05c0710b000e20f45440000c0d170540202b410700c110881e0680d0469220b807001e1080010401050102015002e11220420700e1619041c1d11240a400000d21542d9960301140317250390b801074044103083c2c0107804846203503507400000707005120b00011100c584502c00b0421112601410585007241d02c40201c00b164500c4540d070449200040501030400c1020310301000c910340140030040c20105109000901300c40c1070031300404d8909884804103840c030800780d02040e09000c1c1d10000c6080142d070b050902080701c1e48040301c1035074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 470633597 1250 470632347 470632361
    0x250513092d060605011b0615090c081e01260a0b010807080d05030c0f07170a030221252a0219050f060901030204090f051014100f0201 59
    0x42900c03208041c40d280081980d004000d2042e107007000003e41d01c40040d01d401c032411040c1507030702e6030011030800420801c0d000210003900d048078512096454148040481d40c0e00300120000628280800a00a4410504200c144007062808656614242c0c0001d00c0c01c08071450f900351100e0719001084240400c1000002007070f03000c80c00c50055a150308070350350341d51124480c1d095035114030035041540354010800c50f8010351580404030311385901140c59a190381d0020008580710b4000c89491801c0d42008030207000134558076030b009641c400300d03d8038410404403000b013940551003441c0c050205402641c0307040c0399411080303e0000204100c1140030380340222100e000710640d10403e024a4541009002500d0b442d620071126240c001003513000d499000790300ca0050700d821003079410905c1c080e4540403000c2c00c511038052501500c0e181d22419003500b600d00c2e0100c1a00c096460f502800750407025080c40700c016000300b400c080007454500000071034426071450440c081c088120b5052841a03c03c6d08119 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 470634847 1250 470633597 470633633
    0xd02210f070f0605070807030209060301030b0405150c0309070504060803040e060612010e040605130c1a21010302120a030c060902040225020a0602010e100e0c09040525051309 77
    0x60b142d034880d0700308400a0801281c941c40002c0305800080c04e898064802d607007019002510031401c581c255905c41c000c041c00940152441d1080c40321040a00340c22001091162040058064480c180704003018541406900704c14812820b040c0103010b110b40000a8808542e40465448100c0c0c44040200b0903910926041982083e002030020984155803050079000c0c17403040c242049541d0714811280000440700d280244204211141003141180407800386403011a62074a880c905911111408401c082d40c3d0720b0790b0740c0e04c080000100154544006070b000503480c81c1c070241c41e5210840d0390041c4400c0d400440104460380d5074903290190344560f4191400c81c0c2c0d401c2c2c80c102e1420f0130000040c00c45221104100e200d00c0359004089074003481800341da0400e0207081d0040c061103a115070000042c14505803000d50510500100034010ba80b01c3c0e80041c02280160003410140602c410301c40001844120b146043c1601001f080043e41c0f50141c104540070307200d0900042d044180d2a111f88141d299400035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 470636097 1250 470634847 470634863
    0x1e181a190c050a030305060a060804081b12040807050a09060b0f0c121c1d0c130b1f03060e160e1f05090f03010b10050c010e03040603020a020d02210f07 67
    0x303c82010f8241d030200380101070882d140d81c0280d94611080310428000c490040003d44e00b4024030302d401465403481c001c00c2090f80192000f000c02c07090101d0b0a0b400c1588000d500d64030002017000b0504103c3c0310a00078182410040c0040741c18030b42880a503208518003012410000203081c244404103000f0002c40b07400064040307035980e43c800c400084401c4007500c984a00ea1030299045a404403031048000f03400c0e0040060b000703030103040e000c02a251020448801e20281c850344000704a95031204008410084d0181e4902100f0a14000408075585a081801c032440c800042c400c3d2880c0046a41903c40304914016410900d11030204050525400504034060541c4207d20b101c1500040034050801054801c140c03480e000c1000c00d400c1c0d45141c1078040d00407c62088862811748900000c210030010100085402c0e03401542040c81c41d07104d5801900041e50208030004070303036810f010681800314148000c00d443d00103841080c0f03141482002e215151000090500003915122007648c002a400480c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 470637347 1250 470636097 470636113
    0x403020a06090e2802090f1801210b0c0306030a0b0703021908060a0303110a0b010306050402042a0f1404090f20040b07031e181a190c05 60
    0x500b281205020707202604802500041d036072444032501c03400c0040c80c200d60710304602820012030000c1d40419440382d00800c41601c18101516500c11950001c122000030450070761600e041070b0301c50100e5042c9102800c000441e81d10206014172181e40d00510508040c540d26242d80000030f01e070503004a4000c208228407030070406960b41541c0135010314444903650049580000800711010001100e01c0b644c09800c1c10001d001284c4141c0d0140103400c11b440484041c001c040e10b40100d184000d9108903041c5807204100011400d06009030310400117001c0482841404900e400c20303407a201e090021040110708400c0c941d0645c40382d6400000e698050410303541d944c2d20350f0590005050980b64920b00701e424840f4601607103240107180070f41d0343d2101d0012801d2500340607500c6070b01d80c001082501041110344105c00c861024030203185140386943c07070300c221201ea500c2480604480c0d41e4085954040d1400c5805440c1c2c0420007201c00103112030221203e074286e20507055540f91860400680390f803007248e603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 470638597 1250 470637347 470637359
    0x10c050a050a02030d020d0206180304030b09161a09040c12090c03050f0c03070314070e130611390d05030a0e0106030807080a02010b060c0a3807050403020a 69
    0x10b4081a00d030090f020384880142041c006d07a602c0041000c10340041e4041070010300d903410f69180c9046405441030a81e89040d40c0c84e00e4800c03040320150382200340c64000c450380809007000000140d00500c01c100003012030280314440c2111600503180214050341d2a40071484046102e150a521000c11003203003005000b9180c1040e08030443d440c04100c503644140f000d800c001580000f02d00b0709100008006244090950f07507616070442c880c8100d5440740c40740e1a00410240610701d0028030038000210180c40a101508010f01580c988150f0301200d078008002d00032003041100184503e012100030f642e10001e29400d00c903190f500403c441c111b00c03802268030b1070500652050046002e004010000d2000c100781c2c0c03000b14200c1e17105100050804e1010084c1000103003108020f40001c0c403550000060340002580031996940c00103006507a9500b104120600b04801c180d4480c0c00420304c5c0c400c060690f21100c0c62450207a020f010000c6d00c1a12000c0000c50b5144127000703c0c1c02a541c00707003904280b035903144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 470639847 1250 470638597 470638603
    0x1050412170c0c040e0703110d060f0c051809060a060c110a03030818010b01122f0a03060b1819150f0306080604020901270e15010b07050d030506010c050a05 69
    0xf020b5845107040401ca2440840d0001c0c2400c01e03650042840c451041042c4204400d1300007250040343d0a94a03940c1c0c066400800744a41c40d1084034980b21507940d070701a01c101407000c5100c1090790f481030b1a01000c1c42201d450b0620b2607420b690302810048030070049404e105e4141c40b5080c0e20994000742590001c41016030100c8a28010507407505c1d250701807030040190b0390076604500010303400140001680525083c1540040e0140000d00100c2c06400300e40d9a50390000144052100014800c0007a0b07804c24241d2500c14803000304031543e142801d0403c3d0110201c200b00c00303504000d20544c20703000202200048410810300600d626440d01e100c01d0380040c8041c3c10313482403100b65030100c6c1c58020001150305021591610070740e070051411000ba800c0c508500104400c02447c1001c0c00c00340402102c020803940324a040c01281d4000820081e0000c0c00701c04501d0005800c13000701d5080c18055000010000150110301000b2801c1c0481c181e5202d0300100c49458018902406920032213035201c0c1484008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 470641097 1250 470639847 470639863
    0x90a09060302090105150f0304141608060c0406210204180b03010b060903030306190f0603020429042102090117010f050601090e04021f09090f0b01050412170c 70
    0x7a1000d002070f0780d0300c90403c21b02100321039294078101d404000b00d08000020400640e8014403a4002e600005501e0005c54079005425089582443c007081c018010380404120361035018404208030b070300c0c0a06000e4001c16141d80d04211211110000c0d2401d05158be094040d140a461f4084030581030250060010010304000604c00e402946458020110380c03c05070102d803101035002d8000e61843d107031101070001c80c028a400c6c400716880c1022001c80d550164000080c01002c0a650160b241c1d4140303219105540703444450030310440c0c0200c1e1014245e450340c405860440e201e0a000c03120006008813002018044450300940c0154103074004100f024a100510080c2012100200070641802d41654102c4009035405400300d21001010040503400c040099070051000e414a2040c44109004c2400300d62140c1000010501d41c501c103000030f902c248100404800303102e609000c2c540c1a000043c1c40c0c2d100d680141560b000300e00e910401482551035643c0071a50011480b95078807040000010b4441c040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 470642347 1250 470641097 470641099
    0x20d0e06072a060c0218040c03050105180705040501050a030f06020f16050f120301050f1302030f061002070302180a0e0d02010b030c0a0503060a09031101020c0d0e100f05030c090a09060302 83
    0x41e54004900c2e1885041d42e5413000d5030140c00c01d01c507900200c0101c1da99080c014000c48013280304400200004000b80101c0b4010380c1d02418600a05c004102c0d8142030803d560070681c0540c0c900f4004002a540d481c2c9490201c0750030489000041c8080d003000c001902c1800c070380c44480352001920b81c0500c1c1c01d00d22404185800f8500780c03800b0a1034036030800d498000c0342c0b91030300c45448240010300051800c098041c41d1854003e08904182d0905850201660000c0710082500f0780c00340200074541c141801c940c217038680144060541d6506540c000340c250040071aa0031a0000040c0c005401c000c0503500061000150804940408805060090181c14000c0080c3d02900134079500301c80030708141c1185010f840004010700455594484200024009008264108212280520ac2821080c17006188503620003019041d80c4071024070140c203100201080500034003258024848032688038120031070780c01e2945042c0d0303030700d481d170403401d6103640901c0c00030541c004590100080c0c1e121144e0700038011284 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 470643597 1250 470642347 470642423
    0x80a03060815041e061a04050601020d02100510211401060f0b0c1204140102010c0e062a0f0105060a080d0f0c03050d0e06090609010b01020d0e0607 65
    0x1d1511407040e111500c10401034100081000441e001440110280c031103a10610000c0e500c01550f52180300c00d40e501003c2d1804070807454410301c0c000382400c0c000c80c2c0d07104030203000904656480400c0255540400054500d8060303543c8080790012003840e40350790040c08600e81036000c4034408481c21561740d0000c2004c03906115820301703034440d00300b0600410003100c400504400c000c0d481d000f0902525803082c41320078558080d000d28a081e08000f00b01502c0503042404107a4003141410300060700311000d010444041c4200341c0b070f00080c5681c410b01240c130000841c02c0e18004804404c0000000c0d0000e334003a82325180a50780a900e00c450055100c140300340001c41d20251407550307941209407110414080c9000041c9849400d81a45005241c0c1686851283c54003070300d04440c92081c64111f4004e240e1440b4141c00c01c0040c4080701001300030b02ca800690300c10081110703905000c0080c1d5144841003030b04051040800c2d503001d6075550101960b0709181c100800991801c200400060a840f0324034030b008683d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 470644847 1250 470643597 470643599
    0x605100801051e182a0103140402120a020310140609070c0b1504150302040c03110301171f050717011a03060d0609080322020904080a020a0609080a0306 67
    0x2014001d0b603000311054940d400000c02d403540d0341d5074904401440340780700070b8164220901c03220003001020a004a4500c0b0030f800c8001c42c05105604802800c1081e0425040c01c21502088242c81c1545411590403100748040c07209185005007020001c64000e03505000d24000d1114940b15500400300e1401240d042040c960364803170800080f00c80513240da90021301c603100c100c40010000003266410030619039000c0d2411200000007410f50340c442c0e5882d01100d01222040003142014002e0749580c07521070070700b405154040b000300700c1d05010510590000b04004d42d0340301082c00c014440d5605801040c0d8038100c21000e030480e08405040143c03140c03000100d0180005000303401410007181607a070b01c204000c00100356007404c20718903080a0441c62b80810080a0040060301600c241c0000c1c900c03602c0119142d04d081c595400542181c541050f900404840c0035000699035011460f038040c1d4451103441d1200e1915200324038200059100810052406001e0f00c1030140c0800031b0000901036a60900c041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 470646097 1250 470644847 470644859
    0x31e1506050304150902030a0f06020717071a1306090501060e0c0a02030331050d03060602010e1903050f0a08091605030c01140f0a030912020303040b0103080c010b040207060510 78
    0x50b100c1114003502003114280c01e028481c400707804c1441e490340001d08803050350010f52070742545440c01c10703802c803643e9a00040c820708001500c0e03035454120780d0280c22642002d02a448080040c44440144c11941300304800003402500ca070000508055000401003040601624056000f0000360060002c00c030328840c002015a0f0507801101c1e02000e00d40e01550460b03d6400c2603410108070813040c5c07103a400060380c1407003480d1032404e20102103e001d24024050003c0a0a0140840d507480c4c109904590400354130000c0d0325000294007031810301e001c040d503980712042e0800f1511030041c501082c5049a0000302500881d92206406003d103820009403509108021441c3c0c4210360710b41714503030301a0001030100007151702611012a1900075188100c0c80c18518400750700240d403001c01280040b9070340304d01d00410300c0408a10212000e8890005500e14107041d2a01c04503c401403000405103500040ca44034505002c0d0080103444802400554460042d440c003000640313403c440c0d04070b40c500070034000158 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 470647347 1250 470646097 470646107
    0xb04090209031006120f0f0f061d1204142e08060402120606031807060c051507080f0714030f0117010605010f120204050a0305030304020910180b01031e1506 69
    0x407504881d1040c0743c0701c00140e43c2d40b15901c506d80420380e02580142c4074038012654001c4080009442011700040501d040d1040340812221b40c4100c10181c1c0c0304c0c900003c800c944070070407078081d10b00489459141d9030040c400940d410040310460a0b01405002c42030511a00390003400c4800804da1700c0b80c4040342d85004c1840201e0284140701480c2030f150707801098050603c0b0005503000580d641503400c2540f01040458136200315503020100080c0360403106800d00c80184561b89035541e01840007250390070200402080c00700e010742008644203040000c2020300c1d000e054440003503001e003682c0644902d013048072400c5c0507509116079202c084040040584007141885400d0a548050710744e501c0102ca040b0007201c480104d490015000b40d0b01300720200c0c03a40d40b4070321341400842c030810055949240c40d00c11b01c00005806060062000010b10301802941c0e6140d40740103107240b12200003d442281000100c2c01742c420b01c00504d50380d454203002e07003612120a8000c410000801107500140c69079601040768 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 470648597 1250 470647347 470647349
    0x604081e031e0304021305040803090c1c110310090606050a081c03050613140703111e070204060e0906010602070b070803061201020c100b011b03170901060b04090209031006 76
    0xd58910b80911100b103000c51002860b0000e00180103c030346a001c0e015640e040754030607a4251900c1401004011030903000304100303c40c180d025250000c08403201e2400020a00d5080c1009200c0300320012500004d84041000d80754142c1d4000c418030840040d41031041c002e10380350141d01d000b2652100c010a0302c0e00000344809401c440e00c000c24001c1036280304120010800606416440b2121000e00f040e520f071180a100c0c2d03580b0903080740300114100b84501170212081c030080d40b403501e2001d00c103110400a143c448201c1c0030303c02c0f581d01903803a900b9100003001031006410161703041c1c03035042c18003404040004459040e2150380d0204d80710380340c440144080e00d0003010001011030408100042103030804110f00d004144040d0009070400d44d104258500f003007580415449003d80d652512402580d03c0b807860201c240d0b58400c04a22200d50740c600801014415030701d4200200e0020100d0880e0314258031010040c03003146603d503240c0b40c072041660080e40c090707005103200348107000040243c261707580b00d403030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 470649847 1250 470648597 470648617
    0x605150304050d121b08160809060f1302130b09010803041a1c0c0c06050a0606050a050c1606020f1c0203030403111501030606080d0903030e06180604081e03 69
    0x60f429400b1030049890039807400d60302512540301e0209240b02445d162883c1c03500603064580d50443d00d00f104031780c4070032481d04507040c6c100498034060001d00800802c02c103401904007800401c00d90345070305e1052a00701c21214000e421040d10344840300c00444943c1300032080341e001c0303c5d060300b13999030b41131499a05d00690058408014070007540d508003c0403100209500f00c5480401c0702c04042c20542c203c11140419a24004690750025103c100070740c0b44101c0742d001080780d00c10030035903050400050550181c0000b010603c1000502c0c3c0303201d114208245030304000d80a146801c043d440c0c00000f51a1522002102014171400d903c040b5004001201c107000c1100c10740c021402c550311500e084890041074980020300c1d0040e0341003905000d090588103401b9500614000c82c046281950031440c3c03110300500d404c100080d0310414800030345d200c0e0401f500e04504880702600c0b07807000f650501c054000c1c8000991b0001000500043d410300c0490b04c02c83d4164a00511031188502c01d4115441b131203100010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 470651097 1250 470649847 470649853
    0x30c0b030f06030d0206070e01020c0307030503191704031d0904080d0c05070b07080615030903280e1509031e0f060f0109051e150a0b04050d06090503090310060515030405 75
    0x1360034520409844948c1281441124038940c184000700c1d040100d160402d5505400000d450b9500c03240582013424032203110710f005d0034601c0885c2c034040c144041c0608001e0400c9011a900080d044100c07501c1d0001e80e20007052000213003081d1410444a0b40404070010f11642000305001255003c0e4040d29244c90b00036402c6074040c0e07103204046402440080185600c00d0799142149407000c0404060751240484074002c5907110b0f140c820101c2c10705c2d11600c01403841e00070403921000003944003485580140e0140c65940141032007001d0341a19014540c2641d0b014415111080e40c04495035055101c13001c848030036607900c00b10001d4205e851b402e044a0070b200f221600c8004002a654641c815640050459044040310b1051901c0061206043c0e4204211013a641c00402092412801c00390040c0480c0b030059142c50b24000220760700c0c281d1424041c000503038885114013401001c1c821141c032200000c01307072134a132400c0c01140d10080c8914000d55000b4807001c03d070403024100010840e4003480d085002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 470652347 1250 470651097 470651101
    0x1b0203120318070602060601140406020c2e0302040f050a05180c07061b0306060305150d0212070e011a040e0c1617120a0603021f0207030c0b030f06030d0206 69
    0x918102540301030310521102c031180305000c502e204140940d03c060405940500100d0400d24001040c00c80000102c403800241008100501c680000e801a50744800b900d440208200340c0c030300350600190054001b02c0102004100041065042d4000c00948032503e02c100710558456040c001a6000e074040d141d00003809803920003030a5800401d040c1e028a1151000d4900702c120b0b80c805007a182d00720f0080050035038070096031150a8040c010301c4040c000c0c5d854204041d00e488ac0c2181410368100c10014081c0001101c40425500c40c8401802c0b841040811106025590242c50700511024070600320300c418203560036400b1384001d00840d400c6502d02103188030152a18081402d156111135051a044190450980005150002008080c44400d9815030700c03260242466000c0c104001c2c40145030600c3c00c44103100682c2e03854030807070003003074068180500107088500c00d070700c0e01c0e030b0541001e0064424144001200b030003d000540c03141500000075007050700c4e402c1c00d0513943d41903140e0110141e041800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 470653597 1250 470652347 470652373
    0x512030a020702060711010e120c010f11030f0a02100b032107060c180501090f0b03220f02040f1e0e01020403020d0c05010201140903040306020a2109031b0203 70
    0x65608864103490040c540740c01c95000840580c0418400ca60254203418841120760304a000b25176150010b07200449080715404d4040d0300c400d06c51650506026030001f034054203a22070281040c400e00050110390703a400030504800807031707000040c03168014070400280340c1401034540030b0442c43e850094000d0403c03642543c0300c9003261a0744024141c0141044c403400d80440e410340524181c1d07444545a2000100c4162700706004546560000c40c1480711f40681002030001c19600c82c0d0480d4120041c5545984600d5111103240303000c41008aa0b000d802d040003801c0c0a4440c100111140c030841d0200003860104420800340d40038960328108419000c50741d500c004205400155006248a00052038582c40e94002100056030840a0301c000c0d0342043c0511844d6024440d03c00800c00b00c80c16107880703140c0543c510380c0da0b00c121f00000b82103540120303111081c54081c100098107540c00d2200c40303400e0300c1c98054000080590b81d030280c000400c9084c801400750340d4104103c510680140103080d01c09070900b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 470654847 1250 470653597 470653633
    0x80d08010b0f16030e01110d0518010c0209090304091b080601030b03031c02090315040b0c0c070b0c06070e0103020a020723060c07031106180d1104061503050a02040305 74
    0x41d07421081040304001c260b00402d180b400d240f6095100c2c0c0c0310a402040d902d0001014410800289001030340031060881e82c00381c10000781c5d2040652403807122004014540129080b0800c1a030094010843c0014020920700101c090300035030380d40580400520b540000070241108a019040300401c004070003058507075100c0e8001e440d444034040d08680c0f420501808402845042868640c1040d5020890038518030f01032001400007060a51810300504190301c915580c4c40c00079000f0b040d000d0001901c000d00e401d00340030300740050426140983c0c641c40264001034070b803801110010001841d444840d140d43d030081c82941c2c07407004107a00130801030f41040d3750503c00c0c840740602d44030440c159800880540e40c803a00142540031610005c0c0002d00e00d98a0031510400214060900c01e150900c400c0d42e81403103400d2042c01c1e1000486a52004501c03905000044e0b400a500d4107401038140400811455581e60401c18810b1240c2d42c1000710790748008505080340602e000040042e000260180111000b10b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 470656097 1250 470654847 470654857
    0x170c090f01030201080402040e16080106170d050d060e16080708190c020f0106080f0f01050103030e09060609030114160207150e0111010e01063002060f0909040b04020901080d08010b 80
    0x50030001c0d0703160b0020700c4c01c0cac5040c0840403150301030045c4141c1403000d9202030188400924010800810640700000e0b02520b84800310400701c104080480c00c50401c175910f801110041442442008803420051141a004001c4200400108241402003001d05100f070882604c41d1000000400100707446001e000d014200c00160b00d4214840c44c8104814468203200304c1d0002c21517180205908040521001d00708219061000e002c0c0c0d1500d001000802d801447d071001010b400c89461031a03a031940000ba50500a59242c00d40540c130740340200360249403880041c0e00854a103a107210700c04403c40d0342207a50b41c0c05801040c4407030021000350f0700d16070300492080e840c0d01c40504110455006454910b821600c0c8454500b84580d180c8001304802c04501074400660310000d000d40315401c1030f0305400da0000c0802d03140240100e03400546920b8082001c425500b441c0fa006242007140d0819080c819a410401d46069100740320030000020b41e9803000070300c5a0030705c2c226210300045d40c0c40c2c40300902144d000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 470657347 1250 470656097 470656099
    0x151e03060a110903060906090d1b0204271a182d030c0102030109110903030912190b090c0d2a05090c0a03110906040e040c0f170c090f01030201080402 66
    0x106103c9a141558244069841212050001e140e10710b40400c842d490103443c4400001442058514903018142010a0448403901908d010440791540015442c3c11182000031900c04058a032100c0c00300103200c149412100d03a107036131222154945201180c040340710b2102c40c0407a40d0002080c0f0300d15a44864034440c24908003250703100f50a00c02d402c400c0c15507000c402484480c1c1d50002c010301c002070203485072a4485410407003260070705c00d01c080460780c2c17482036405040c421b801c040351501c0c5269041200070102e46075103000998450380b61910802120f01542d100295000e100c1c81c002481c01c12000c09080e0540261001842d9070181c1212000c0c00590b060803000f003400304201180d03544a4900c0c4a000c0d0840e071040541d00da00512000b411140d00c0c0846c42c03d40841000b4003415036440d601903070144c0303851030046040341e12240b030003c0c132a4255900404a905160038000b80045004181140c1c06105070140d440d9054054108180d2020485128200000e101f0050026501c00c0d0010741c0e02500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 470658597 1250 470657347 470657381
    0x504020307030206040b03040b1003020a260d020c0f1005070807050c0418050c090c040b0d090c08071d0408161b0e07090602060f0a0203100b03151e03060a 68
    0x10b129008190f40c0d900c990840c04240d90000f06110070805d48c3c400240c0e01611080c000c0396014110307400503994910a00c1205440162041c1e2150150050740b000c07101c2c9030403001143e40c110305143c40079407a00580100f1510070100304007102c0090410142c200e61180c1c4070307a526480e016455980780c2964001980a03617051003201e1322155591668460a01e41703001131191400f2424507031034014609074513042250301406020701230103459410b08007030300c06071003280b820b01d51100e04000ea040024541e011001e00300d1000080d002880200204001d002e44080160401d10300501001040f088141500c00a02c3c0c1c4038201300303180c0b20b16840b01e1058109072044d46200044495015a100360500390740006400b00303610400e0180c0b05402402c1c00f4010522800500140d15001d842030001d141d00400f41c1c00030907000070010304d110a0102c500d034094500816190703201d09001c900c03401c41040d0130403400d004e03481c504040030411034003000c00c600d0414000d00415240c6c1c1d0707000190020780550314407885100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 470659847 1250 470658597 470658599
    0x30f0203120106090509090a15020307031518110c0d03050408042301030c0c03120507051608030601090f05060d0f0f0c0809010b0405100b0a120c030b040c0302030709090504020307 79
    0xd04801400e000f044207507240400f0a04203020811802e201804060443c1d0014450034000f4990020301a02d50410600060b00d0750303a50785050b009814010712000c5806c2c0008404142410120801400541c85450402034031100c2b000c030000300e11a0f41e00c040002d03030000c138400b18000d2007500705941c0140303c1ea03030103400c0c2503035a0100790708004004103031a10002c6d844101e1916580c50f208652108085c1e140100140a182d14060603150401c004080c2048c1c442000070b07401070040085502c94140100704c1c01c240d01850910b0445600140c500d180081c10300500054102402c0e1071500c00e440e4020500b41c40d0001e01c44400f00100003250b4000480f980390340c1045009102803282075001911070702d54104928010160790700b1920041391300317072059160400b84015841030503406000d544841b807030315654504000040d514a4161f000503690507003020740b450320311a4035411040c42c50b0f4054030184410309490380140e040e40001c81c0c680000035940d190070000313446c4075042150002d0014003941c0c041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 470661097 1250 470659847 470659867
    0x20114071e030f1101050c09060d090b041b0e010b2d0c07050913050d1101020910032403081912090623061c230d0f170103030f0203 58
    0x3240180401e80200e00310325502c0c80403e030030001280c04407035504c00030040b5140c21070090349a4056443c42034040c1401040d200e0800409900103003e0035040030f9500600d00e4a0301c0c0c1589403000020407655507200c545e500044a08082860310b0513225891201414000790a0700c0b103401c2c1c124811001110f008001040040309900c01c0202a03050007032014001c0d96041109004602c01d02902c000d2a901040000c2400f103040402c804074000c5d034a24001c2c00440c1e0b4540c2da0b40c007a0141e00c00c140c4c0c1c04596200c00144094041d4020b051000c0b8004c0741c8649145401401c259038007080c44007920b1003004000d0458154850b0b0444540c0104504000814015009414003110302d402000c82c1c5a84e5940c4003001b5142c201e25000d084809520030303136040b070b141c00804030301080000c01f03440901d0310721490303481c00f080b203c2561400c0d41c034000c0d150b9101980c0d1014131a5a1051044071450101d4101a44043e00300d1090320501008420500c5020027079207195400c40d01039841c0404c0b8011400b00384a802c00c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 470662347 1250 470661097 470661143
    0x14071a0a0c02010e0604152c1501120c210503032403070b070308070c081206040f15050607080f0310091505030c130f0c17010f0302011407 61
    0x403204040002040040302001908540b501c0d981078009510140411001907000480000e5403d4640c00200c1c1300620003000c91341e00340740c40070b05514101c0000c02c0155074010004810303030b602d01014100b10040c1d0307940e100b688011003082000380100d00307401400d0000c581c3c120f402d030049103c0c69034400300c00740f07036629100e0850308282c5488100201c420000792049500c55040c000007281200a424440e10b06089006103100b0b814004090020100008840da4012640c05420f10341003182c0e10707136540d581c002c1101c01d4002210001d115618148000c07000305020f1140404a1507088840004a42060304000302900b010400722101982000307840e4004a40001450168549104d50800e107402c01924400303407180c0c140a1904c01040070f90402c815030f00001c956a6607242034032040700e05140c081181c000340092080c10000d050030f03c10100441075004113103120076a1b001c514400903036200c002d101424071640c8800381c00910841003c000b0a40100c008041d507901c034880e04076651a20784100700c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 470663597 1250 470662347 470662351
    0x4050c0301090309090b090f01140303040b04030308090d11070b0c030706020a2303070516050c1c0606050906100f03151409090705010818030c15040c080d14071a 71
    0x4000384d18601c040007001800d0048502da0321003203030100c0305032408014203000c8220510801c404210080d0102c0919101402141c01600c81d00083c1035071aa103a04002e0890b06080d80c01040d1886040c40903000c091207004008040d16495000d805800d2a0400142d41500149403241c1140020400d4000003491440201180081611101814032209000c2d64126280c06070405410200300204100d51350702004580082d00000003008182103c2d0800c185841b14100304113130000c00340d1080d100b8000b100750306c02403024810340003804240e44882c107000360b101065540e280c00c20140003035000301d0740c010500da003403205007850001141880800d440715030b828141d1014100003207004182e0828180044416880341e103440c01007000030b2900c00002c0c4020750050103248a010703600300c0c144644005004607201c0c00306a1b81120f0420201c42003d1400f804151000c60308400e03c910005501c0c18040b48425211001e030b1141c1d020100c1035803101e4190f602c08030044031305c1c0300803001c40c201034804030600e58 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 470664847 1250 470663597 470663603
    0x1e01060b0c0f0607050a0c02042c0106140102010e0316030c1b091112071404030b0108071502060106050301050418080a0f030528271109010504180b04050c030109 71
    0x31060a00c68002c60805101912110411804001840010360071410707948181ea03040c2c80001d0030305207101414006013007039807046000c000c081440c6410b55005400a0055803482504021200310007030059007216580d2601a910b174209124104e40c000c16442616515402818030860224a5030b0b40c0c4800100d0303042c070822406c100d400050000e24104d10445801c110700100382407500301c0c00703424288044130041c203407401c1100740e140c0458610a60815100210b500c15400c80555031610207240d2115014054400d86550400c0c0450700c0d1440000d00341d0480701d072515043c0c650b07400c020901001c1c003a0345c003441d594914121041000140008010110520250b030351140c0716044650050940390050403810070001e04002c3e8a1002c4c881c0760090301d600090503000140d20000002200852002580a00100d4841e102d00400d04c001d4440200080004407080d0340c03c0d0703882d5010041120304101000c142c1007140d9100b000010010b080280e00b00d402501200d074403040d0600000c1c00d44901041c21 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 470666097 1250 470664847 470664853
    0x6092b1502120f0114151909030b0703020703080f090a121805061c050a090515040309060912031b0602030c09040f0b0306040b0403090b0409050f0f091e01060b0c 71
    0xa594141c103240ca0b0390b82203448010701c404a5403502c40592012032480311458442c94401e40754810f0551b4920407100c00042c001841e600868004001405c2600140705c151210084040001c0c1ca441c8248200d4001755895180c2813115200c0b4074664030503103001840040d02d0300c103e00e000f1021620403000d0384038a07140c5564049a043c102c903010100c11105034040e601400c405d0003e07001c181742c2e8141d00b030b98072405070b40c00217059503844030408042d000b40e00c40a4111302481c07401016488104041a200714000d440300f04880e80d03140030451b2807035010300c944610b0742101c101101c0024440e40101e501418105800714400781a6100d03034080340e105640020300988001405091410140640340300d90550180c02c100c491007034008242c464000400c001c2c110440300000800301801203000c2d1014200d80540d0b40e88954480e910b0314002c0009480344c040c2e84802000040a002c04c0c2c001540c820308070300c400740c40b0412048041240d10844042052402d541300c550100368030202402518041d502c010003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 470667347 1250 470666097 470666107
    0x12a022d0303040c050f03070e07030902060409110702150307080103111f0315090917030c0d050c03180f0d081801090503090f01020a1e0212010c0c1106092b1502 71
    0x100090780440b0050075012340c0003510700304134180b04544000e44c810901d0502003080005031001071b4030b40c841c43e0080c03000c00d4900a102454413403898064030300c262090300c1c3c48480882c4032000700700d68002280c240c0006400c110050001601110420a0002015040064002c80c0f0382c0c00801c000000a00c0d4000280e960a414030010807a00c40c0c080140b010070001c000700c10043d202c07018403030b481e0485400f030420000b0125040180d00030444180d03020a2004000c103003030050090792141d106130350b000d04202c000710512003d10008258003070b800101a0040850001c1c43c5425200340100800c00042200507038001250404203000b00228288500041c0d5541c1400c3c9007040f42c14958040142e0440d4030100c1c8a03000601080d40c03c00d2002000d004e000d2401c0810b01c00601d8a9040700c400c844503500b0280a880659008612221800d1003a009024003001010078031205014952115500040401d001c0c040082c080d0400400300c04405402194001541c8954216401c0e00404030401540018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 470668597 1250 470667347 470667349
    0x13061a090606031b1b0609250f140a0b03070507200603040213021908060a0e06010206010902131203050304050c0f030a020904051212040b07030c0c02040b010905040608012a022d0303040c05 83
    0x401006d8504056000e000d94500302140c2c0781c010892740c000d0b0a1581042042e1405a07919960440020510610155901d03d41030100078030540210104880415178180d5044400c5c4c01920076801102020341560304581d120b03002c10161600000500f06569030800401c42c2004510008001c04c07181900c9a00480c203017a824455549c07807075070021004860038410701c00a170707134042000c50440d0800c410158071940801c62a4000d480c0c0c40c0d2007550044655400c102c10140c108024520550244050301d0f545a2444280200c1b40600744800d503041d00000039080051400c00300958000703020700d00b01c0e2003001c1200344060745940211184001c0e6820602040100b00f4074450442d0f121413280303030a2010b14400d03a0003074110a40352000030f214540343e81184155903c9004881c0090400a10a00400342d0741d4110500800b05c01d450080310b0701c0c8007100300d044402042d81c41d05481840e035004083c2c01503c0c8035000c45529071307a40300e001cad0a00f0300742a004d880042000618003860007080c40b0140c0500e450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 470669847 1250 470668597 470668633
    0x2210705041802130302090a0e070f0617040510020c0a050d171b0304080d1509021914030a051b0a090f05190e13061a090606031b1b0609 60
    0x1100ba008403801001003510444038100070800302da605840c860f03829101d541501019000c1000321031001d20881c200045e150340b00004200444080380c80d00c1105040c80c10386503807240740403500900b603544a191040900a00303580200b562001a0382035407210302183d070700c081c10420302010300c00008816600c4034405c140d89000d459007051140320360f10b8030188204890f0560b80002440904030300c001107101c2200843d1600014403903041c0710700c840b0b407107500c6000000003504450580350881004010302001c4a005043c004c1104d8440700115055582c2c0700110000381034010003140c81e10300e4815542029082400142c090702d1040c0d15051415420215644980056a0700c601d202d02e0780c5c203040d14503c911881c12201135500d88804154641e455904022403050051401042035107002d40708500c040045032039111428080300e0420f0140c03154030821080707000585030954607100031000d43d40407003200d60041c81d5004c05c1c80b0342e014800168940541c01c09404550103129500541310944041c0404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 470671097 1250 470669847 470669879
    0xd14010f1b080106030c03020c0d0f03050a0e0a0f06021c060e0709150c02031608160501020d0f0309020d0b011d0601020d200708030309030406020601080a030f030221070504 76
    0xa400107818100c44402070140c0010300c281002d1540d581078a01c80035100707030100d4501030002800c4070303102101b5800081c2003481d480108070010b45400c01041400b001802225840203413040145010310300b540700e0381582e400140c012580d9545c01c0114000d07101001d00d4080c0c0310322100100091961400c80c0548048400034003803001c10981d03001c1404449540c0d41c10500e40403041c680303440e00501c40d20100b1310b4034851051200c0742e42c119604c0060516000135407419140060365101071681d50300c5005a80e034043c04030304400454020422114504c2c0310b988200076036800100b12608244403519101c0c04840280c002c4110389030343c4039448902010807500340f034001600388010106400c40e21001401c2074594000c54041400b80b0131441c21444c0100300c2d41c0003070b00300d100681e6968182284116036940c410701c10000940200d0740000f5503a82d0210300e000001e600764958000e80c003411402103000754081d200d0050118030900d801c205080b0440304c0c5a00c2201d05071116507841c0d0400ca842c0d0780808076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 470672347 1250 470671097 470671121
    0x110105040f06110109021e01110714091b0307111c050301050402090105040305061303020d020a0201140c0a060606020c040b1e120f0a1a160212090d14010f 68
    0x108001c100031501024804120b4059107015210003000c610018054200014040d61020603400c40b0030f81100c0c058245e50302c08209884501c0e20701c080c02c1c901503d038100c074410360707004408064a8900a09010201d039030300c00c0314802841c00106459011010075041695500b000031681408141c1e004000c10074544425014048040c081405142c02001440140100c078055038011400c140706900034000d6038041d682c01016904285800c00d41000100300c0785078150300500c9400d400386805400440c1780000f054040e9134002c49218082e00d024101e5000c030704040302d9031156800d95804500d26201d50400b416441d400f0701042c0306070780c0820081d03a25014036544504044841c480004203400c00e056040c5400303581c8000b0234007080740d166051500464510301d06004035400b00701008100c110500196100c1076426126841d07004c10a070108c050307002d901d0702581c40311b401c1582c1880010041c0c100340500625180030700700a5a581c0c42542c203941c3c0c0c200755682d12040f41c121503080c50b024100c0303030505d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 470673597 1250 470672347 470672357
    0x10f050309100f021c021e0708030708040f0210030603050601080d0c020d030e090c0a12110a1404050406030308150d0305070305091516052503110619020a1101 70
    0x201003801c1c0b61209954121a00d0165444000703040c1c255254051380d9001ca000795004e017000403e19880c0300a0740c0300c21002c8143d6040d030414141070765070400075a0b621640100c4031f07906580d07c83e901a18600b401400641c5c4422049107001c00503034924601207240d59450341c001c0384162031450110f180c0241038000d90604d0300300c0b595841c01c60b40d10008210240703070122000b032103001d014241511a000500f040070f8019004108200708002da2400910b51842d00e6a1a00e145d00c100300e055200301d07500b400100109000c204002e100081c0301c0c0e07400c80c0c0d51a61001e10381c0e1030555900000703802c6502651040300130401010400890450f42442d000800c002620503200343c000d1690300508502c5145030041c1848404034011807240c8442e14110303020b58010429640d600c02d4020042d0f2248406c4004a40078440c00007601003070880080c4803141d6010204121100b02d01310764a1803502400b170030540d900318a0902104d82401c2c03a81c01e1811005441c0e030040c20841c505400c01c0c0d00d024581d022501d040c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 470674847 1250 470673597 470673601
    0x810141612272f060d061703040e07080c1602040e01021c05100803190203040302040c050712090f06051608030a0c0f02160504020702040e0a2d11120f010c090302010f0503 75
    0x803d049550f600e450300d08896640d952407418030007400a00542c2c1141c8052034400d1000c034840380000004006480c034501941d0180c0d0740c0d0303c00c100c81d6608219032011050406000340c59900c0391141e6030708085480100b010500c0c00b124003460b407ca801506044e200301c031150710b10f0600c100141c800e00d90428101c1160350110380c14503a410340e40e8818005004030340142e407854440600c2c0300f4010384020f540d0040c0240302c00c0c0300141c0018450f07000080c0c00c1c0c4050340110071101b1075034090350000007111420710004001c0c51034400182c3c0c40740c0020083c40400074004c0502c07000180e41100031441041c0c1c00200299108c0b00d050014070948600c4440750035580600152042c902c004880101107442c122801742e1740d0b011500c0840d019004001c000f9156201e03240100b810080b119584d001038442c0c02c0e40c18524542d0380144060540c80015001d8104403150840c14914200411aa10103009035001c843c4043d0f501e030006400c480c031401070000040c01c090f0040c0115079000b030001025020324940a400e40c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 470676097 1250 470674847 470674913
    0x50115080f15030f0a050a150b0f0405090132010b0f030609100504020a03050712020405130c0c0b010f0303021605181f081014161227 59
    0x340801620090b00c41c4802050420140e80410011070207510138019543e80e52513a2421650310b080401c0102e4141c440d8503075111070240c1030302c691861440000d100d48480886c030001d000c02410094000c16543d520746001e41c21949603e0305031004200441200102402c1c4960f42901b44807040c2c1065030618001c1186c0c103403884801b429280c001a0860f500d10040d2102042d103214151182c0c80603030000d00100300d10140c0368256101521070155a110084550040409001280300b5801020f42c000c409941d2402e03040d9031680071103002451410000c46108807600c6195017038100361b0107911605010141442099818007008280007503d09103406424240380c00070780310680c407141c1c0041a8030007100183c07088580101e122920360340100701c22542a10741441c192203010b035a40e00c0c000241044040c205c074a41d4010f02502c1a203c200303034130340250210b10044407110a0708a00c89a0140c0303952403105001c8000455210700410318201d9401181c0350f2403c80e40a1481c0d0800e8070b82c01c10020201045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 470677347 1250 470676097 470676121
    0x10f06030f06020307021e0c090105010f0f1202130e0a14010311102015060a0803040510021f0c1803110402090a0e0405031209030414040c030f0c0305011508 69
    0x1c0d46502020250b04c0e680c540c0c600701d02c1d1100020313084a154444040300564280003044500c0d1040c0305440000842c1e8984c001556402403000c071a00014001041c009101842282e1900303200300101405868115882c1d40c1421035201900710403803040c0c0300c0c030030b00c0140b049910600c051408490180341441d8035540b14802c0a0904d940d09502500c0c4d400e08558441f8842d981d0324060201107200d112081c2a8405600d643d00c002d20446030181c01d9201c0404d05502d4082d50980848041d04015031905003081d081c0844a02841000800d501c0380e142e42e6031042c181d4250130071a00e402e605000658030400c0d034000700180d101d803030300c58114102c8900030b102240580d007101490640545015a1310002100807400794509640041c000e8507100d001d000800c8070120062250080d60700841c0c406444441d00c864580c810703481081442440c1c00d2a6020030300741904160100016410009540c1000040c0c040135184451a280002a5030b4001840505d0030342c1d081c607161503120315001c5030b00d203840e20801d06 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 470678597 1250 470677347 470677373
    0x150306140126040507060e0609031c020304090c020d0306140f150d090b04020114040e0103020d060608010219020d05040e040b04020619080a180b07030c020f03040f08010f0603 77
    0x20410003010b038100c01c440450b00360000408007848065a03240351038180389032544400d00800c00012010701440420b803800740107803408107500401410088000782080d000f424115085c880942c007042c0320010b004003041c403480b5006400c41d0003030892280107000080c2203030301d41d800042100480340341400c82ca807150703510b004100000340d0f0011344941030051503118074001c2d4498192403d007880ca40c0300400100c031440034003070752003078131035039036503d6043c00c00308441c055401455221101e10004001501d8076041c051102c81c00790400144517a1541801400d9074414100410644035030000700f903c0690404c07101c14010410703d4802d041906042c8604118000544050012844040498190343d00c0b4412182446000414540501d0f5a0304000d44403510481d4984981850719601d5a50349a1091000e01c1942d80a11600c017241c2e522102540149040070500d400c40c825401c2035503200d20200020405094108107441005180c00407040c291400460352a6080b410000100001010309003042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 470679847 1250 470678597 470678599
    0xf0303020a1205042d060e03100b04090206301005060d02040e0103030f08010b030f0c16050d050d1b0503010b07030509090f0105120d0516030903020607030915030614 73
    0x154030b214074484101c605000b5908403c1c4080307402c18032000d170149095011298141012035004100c1d540794000d41d007000c40040c0440d099044100380c0d01840045038044441614000e0001402c0310711500800c050384c02c0000440785481007502101c503400320542c8a00c58010400900c244645003500d02c1c159090700d680b0550b8040e48000c68511413214681d015200504000c0061408642c0e4038140103241009884c00c8802142c019000032810800d4002160b2283c4200ba81c00d24464881c1c24160800b58031450840604c0040702e0700c108002402400868890702e039940d10191100c031021032103000c1310021500320481a01000903608940d80104c00c0c0c0e4119a4240c580940f54003290609441b076106280c20b443c1d0250350740003000682281c41c003203941a10419105005e0700805081e02c250b442a900c03044902091044c0700014a0300e500a9001450903c01c0c1740aa051950381c0d40440c1c4290000c2031300304d0101ea107490b4103000207000f0400c000b00313920780c0e0310302400013030320b8000ca00d61482244c1c400c035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 470681097 1250 470679847 470679863
    0x702030d0902010e040c0306050108010918082a030318030414061c020301080105180109020123070212010203041b03080301060f11061305160e0a0203090c09070503100f0303020a 78
    0x701c02968002c20b007a00c840c8402030030900176081605d000400600c000d0003100e004c607442e50000300d0004298070410841c1440c2031a03001c040f000d651655020368005400c0203d541001d03000320660302c80508180e20380003402d07130011612401c1507800b200003039400b0082d04005620a10040103120030030303407885510748400c3d50280d0395000701e200d0900d91042d04000962199000000000780710740150702191042400c0c040f400000056842e0040c00c2c1c45050101034000350380e4000c1c80c918004030050200c2403200c0c0d1003c851030300e91035502254800201c1014601c0340c0e5800300800040c401d1440211100765040ca00200c0a230317085035104013050206002d07a5040100c82e8003500c4100d405442000c400d4805502180e600e840e02000c40b00340c8040b14402203c1e05d0069a00c2c40c1146081c0b01c54240903941d0500f200b2000e90b40d0090700b03000a4100411120480c071964002280940b81c80c0303505402010130b6605d042d901e140404c0c40c0441241550710507040401141001c0000c81d44c08102d1000082c2d1240361 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 470682347 1250 470681097 470681111
    0x20918130506070c110409030f110c03010f0b1302090102071e091803090618050d0206070b07170108071805100f0b0705010b040203220c0b040e0411090702030d 70
    0x400c622004035000020075611804051041c1e064200c2e40c102e4640c1e00c02c696491490364104140020307500b440c0e100801003800180401e51003070183c1e400c81c19130011303c4115821400c5400003e400e4444206c050b15619a441c2d10340310480c1841200b0703c00d00d4200480961400c80d400300000d550380c0b00e40c4105844003850308040d1302c6140245401c4002440140d40501020f503140d40b800e1001040104107c02140c0f18840000d01b050050000c42c42945401d9520400ca51900e01449050703841c51808030b030700030010402d074000250140c2582d4003402042d50b0301c4072039185a0000d400d40790701c1a0800c501c180c3c4948400c006004000c0f5038502c2070001004046900c0d2100340b943c40783d40f0701c281c20000d5032a5220502084070752054001c0c0100d11b01500c028444000b0201c1030000b248015100d50741c0d54814490121703480c221050481d04801d200766480310005c0e80d68000c142d900d4016800c400882c1c401d1030309001c184840500605014541215010158109124069603910440c0c0c2e00221458990301 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 470683453 1106 470682347 470682361
    0x304062c0a09020a27051903061505120f030a0507050309040603030e1c02030d0f140403030f0f36050303071101030c0c0f1b030204180312020918 64
    0x45c080100343c1000140b00030031003a184482885052001300100290191044405084140c00001740d02401c09042200d0b130040342804082d240e02100340b40b02c1c05040881120406609410aa6075400032481d00703e00754056803031919442450540c0000c10b00d5080603002c50708000c1150381c05074a811403400c29100210000c0b019416600908202c20014001c0c100107112011320f0030a0440c00300c690101c1e003d99401604100c00147d00c07100c820660903000f4803126030106030748c1403280200201942401c1c4a6040b402220340301543d0a1180000001d003d0700310024000140540f582d60f141c5007005c111143d17030561030b24002854010b07001c8041d841113110b80c1e0103e034030000454070b00d405074403281d04c0d501e0342e1070f200d081d407031002c0c0c00020041c0c1d03c611502400b415440b003281b46091460401400120307219441699030b9004100107011030703480540380014000003000804003615145 = true := by decide +kernel

theorem cover : BRFrame.Cov 470503597 470683453 := by
  have h0 := BRFrame.cov_init 470503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 470503597 ≤ n) (h2 : n < 470683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
