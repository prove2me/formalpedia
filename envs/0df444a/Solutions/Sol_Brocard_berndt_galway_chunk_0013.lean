-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0013
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:21:48.992575+00:00
-- url     : https://prove2.me/submissions/805b5b51-54b2-4d01-b7fe-f279e12419aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 2158281 ≤ n < 2338137 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 2159531 1250 2158281 2158291
    0x1a030702070306020c0a020f120a02040b010c0204050f01050102010c0503070f1b0501090b090c030718050603070f080105040303050a05010302030a03030b0102070f0902030901050105010509010c0b090309060703020f0c01050c0d0305 101
    0x19509007540701e90381c02c0242d17440181450a240e22030940f070419480c200c83c580040d2001240d040d0581c95190940d03a85400031000060703c0350b5940d808401d00740e4003c01c0d144480c03e038020301c10425842d1401107505225021300030b2b41e00549ca00000800c055001d401105d01131206504c07941c3e0744c1c1c001c20b0030072201c08000140001c03920206291040020b04240038005d012449850600c80302e18041d1402c0d072600304490345091003680402c20070013400c49040d5003101890003156022813660f480502080c41e0440561000004156110300043c0e082419031080c0d0140380300f60703000c0c0016103521188600b80c2e82c083c08043e6042d00021004000203010350f10110a80300c060060760006651081606101c108680c0b001c024203800108106000401b8455280074ac6002d080c220b041110440001301600410907008000c000346d0b2004c5050301008205131082d60324001c105c0c1f90f984c0407030f2600030348883c0d401c030312445070b407298800080c06980504c0c05e5402080c0d44000074802e8208044d800c50113003401500d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 2160781 1250 2159531 2159533
    0x8041205070c080616031505010e0d050a031d0301090c050904050c04020d09050c0303070803010315060801020706140f010608150103020c0a03020303190501050a030204021803060a05010f0603061a030702 89
    0x1114034006605034520342e0003003420340044d0800c1d29003c1c60001e45244c10300d0060041526140b49480d81c00300f00717200341c81030711b42c203181c18404844240c0205081c1d50001030040c000b48902101c040030513510210902c840650f01c005880025040c03418103081c1d558516005101d4000076006000c941003000803140d0103406842190b46980ba02e00203e8207c0c1e010004034864241c031030b401e00c0c0500c80308002040341004203500031032812141c0e07103a1103464013060100070800c0c14a101d020301401d2035600000080e0034190b00865480103036280c160300600c62401740013607410f20080094210244c140616040f02c046842e6401295514400350020403202c01440b0705040d403d00120341c6151040203009030462198005585c1c07401c0c80b207542d8604000050b07071b43d545182401e00600183c0c41c3d902c0800b04495050f1005130f1641401141c46c0400c0c40014806901840f43c0001c00011003d80d4001d07a04030f6403602100201203844100c12001d544050154050400c04020a5618020700030005c55206030b043c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 2162031 1250 2160781 2160787
    0x1080402011b080a0207080304080307060902030703050d03020405040b0f011d01020a0b0a09140a0c0b07030504120c03030306080102090a0314070506070308060103111c0c03020d0207080304050f010c08041205 91
    0x9411480c5000340b01906807503032072000c994140700310b80400000010b012a4070046d8141481c1000c40c0340d80b8821000c004280741e460304149011034504228010140d640041a00c1c802d10b40c10b44018000d421174031505103d141014078003840e909150010b8803c0420681d55040c500d90744842041341c883c540ca920341c0c11449002091000718007000c030928000c4c0c003540008184000e803814611501d035401c0449042c2604948030100026509420b42800c42e102003901c2d5403180c0d0f240c1404e660307078000c50307000007039442800795900100104e01ca920010b5901c60b40741041103d44070031070b81e0b08174001c81c02595040301c0900024008910618005e08503007443d101220b46098031075000c15460381116070210081003000d0248a40b56030103029005940000362081401c00c0000300c280c05c04022140c4d09008415580d880c0006910311036012503040da21210025950f0346a18507000026900c01c0300d054800b030252011142c1d507c003060060980c8a43d055076904069200c035181c070701c950b030810340e4031a051000c10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 2163281 1250 2162031 2162057
    0x1031109040906020309010e0607020d0c03030b04020408010e0111030601050909060a050d0b0403021c050a120902040204080a0308010506040311010518041404030e030106080d0c05070504050903030103031409030c0108040201 98
    0x35028401010f03106140150300c0342808111036094420381a802c980b2500410100040c0650000c0c0501032580316251200640c0aa4201030b0010104108100c0c2c20038000a004614810150801b45101425030700801000c802d103201c07601c01d80010390b8694000f030001c100c019134071b103070403445c0b40d412480040040180303d9070361002078907202e542c981c00c41d010b500c180200010f054060000028044c0030000d135020000c948070b4002c00900c40d480c5808244586203807003061075081a841004003e0313016008564807034503000540c0e50744960b050201c0000c0c45001c008151400c100b82540d040700c0e404003040a030540300c200152580d8000340c0c80038031010458201d400140d40d490041503009002c00444100504003410000e14001d40b8501a500036810b1030070822211000107180858100d0505e4500f102191500d05141003000e944d102d0f1754040d0030b00050005019010000398102d80c883d03200c0d901540d00c04a0920400d000740e100e0341d40c3c5a000342c985020303254051600d050344180305141590015101c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 2164531 1250 2163281 2163289
    0x10507061509050402030609030304020609060a1b0308090d09030f080319051311010309050a02040b0d02040e010605040b0102070b0a03020307110607020109140a0b010b0a09030b0106030902040b04140601031109 92
    0x5552110300d0043c0c46a00340710640c10140b0919170000d2807030018626524094004c11481d1040340022402100001415403840784944279803c1044027800760710180a0740c0d800d0052000b6029500b61512b0300920307016401650040c094401240c1e800070b0b03691216402c0ea01c0b1140346410003002124070365000540d052a118081c40ba40e0310130074913501203041300c103180c1c2801c3c1072034280d10300c1c0300c5c2c10b040c500300d04000403070b03070004000d4600d541c100e9010902002d200081801c1035104240217400500b4030590280304c001c190018000d4a605a80030030800310319000499440c01c451242451401080052404c20303446130b00150f40c050014148203000b20050306d81580b074210116100d4005035074600d46a410000d8151502c10300b83c829800520032006643c0701c0507103895043c40390581c00240000d07400300d402d0289c40f44e4002190440d51a1100f586c0d14800600504500c000c124841e03485e11124085030b207040e100309803405c42c82c0d001008807a542c4c0001500100705000d40c0c03d2030300d0000e101e144000e5403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 2165781 1250 2164531 2164571
    0x70c0512010c030f020307080402041109030111030405010513080304140a120f02010f150603090615060206070e030102070305040501050d06081204091503050d050307181d150306010501050706 84
    0x90030100010702d580d0204001011500110401c18529004000b8000c1301e50384009001d402c1601224006040280d0405c016040d00c11000d03616095400d1540d004800c1d48848003852040780504001d0005076200042e0120310340156000401e0940184081008902d001c80204d80052900f001c0f02d128015648902c0340c0d4210b01d460f507500003090400790754407081e42030180d0310044003014000d020366500342c5801c821503034140c02568201355a0f1a811014402c0703a800145540040c054030f00101c60312008025141e21003115240e0104900740f00006150605208132007081ea0180d4170903042504043c011500c5501800d0b0800120740c5407d0041a40c090521490f80c0811100030780b50744d40e40c900000326041c3c0f18000180345900c2c1c68050200301180f4049500110201c0310b14029941c0c0d81c441400361000e002124540020114030305d008141c400c24030003079002c0d16039140e07024030032a03561202c00d0500c0251455402d400d81c0210703004102550007000942010740c400c40000c5586007404411555200c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 2167031 1250 2165781 2165809
    0x60305100501080d08040201020309011416060c111506090603160803030a0c0203070203060115050409020406022a0f1309061506030c05030103120c06060308120402010806040903020a08070c05 84
    0x15541e400100105481000000c01c01d00450030642c0f580d14198001030349900500d111103042c0701d55507a85c8130b00d8100050454030b405400e40081038001103c1c0c20034a000704204494080414540310369005204400910f881008455003031101040d5500828800105030103072036140c0500c1689080c100c1d01c001400e80344050001c4800139610b0385002843e00090354000010041550000c01c00d8030301513103010410782d040d5024651482d0010b514030300d0456007440b0300c1c1c3c00380c420240b011030302080c2a07501162040402d81d004440c010300b0212155981d1140360410403156204645058190f05810144103510b04205056000900c0c001c0e0fa4441c6801e40701403810b0002e010841070801c0c03000d19018814984a607100345829800c1d981144c2ea0200f600740a07202001c1403281c113429031400c10a664201c24055940402856150a0103444005003800241c41c00c90101e501000010002c1c01c10b4841c00b080c0381c2d0140d00a00c5104840d4803909003580c400760b020388600c030b128100810b03552565003000480c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 2168281 1250 2167031 2167063
    0x3030703020109050c0a1211031207060b01030b0406050607060b01020f0703050c0a081203010b0309030715090b060f030c0603060612010b0301030606080c01080606130e010b18030a1a04030201060305 87
    0xf4003614140f17080807904a0702610520301d0400c14016408010005203409034091b9201c404803080c100060314101c0c05213203d001e00c0d003000415408110643d08840f41050083c2c0381849071902401c100b200783d43c164040c1076000310702400828045007580c0c01041500f001801910f0700a4141c10900c1d0520440782c00c20755242c2d206607407020300c500380303010300800800c01c6001408034802d1060883da40c0f0711040c030414602200120118100d0041402200e1089600c450184074200c900c08442c0050401c884069803514030b0400041c03c5070621002c02d00381520002d01402c21038000204020310794101800c0b66070040d1307080c442000b0041203a801c4c0740c06408141c98840e00c80d0300d10f1418505441550304034800c40e41006038900b4080e41c001286a030406812140240c503003a045840c49515869640201c1902c40d205000142030710301c4d50000c0c83d01c040500f51041400e10104281555180c869000404002c81044014640348078030103000e400511038800420001d1380c940303c00e0302d010000200ca2085d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 2169531 1250 2168281 2168291
    0x6011710050901050f01050717040e010e09010b041b0c110402030403020c120114010b090111010f020c07060201050c040603021605030309010506010801050102010e07050603070203040e010902070512040b040b0706020405030307030201 102
    0x18504501c540b8010501185d1011420000300d000921394020404010800b447c14042d5021100002003502c015200c5404880b8482d03950f001146000402500d03240265464108003018904050140a0365080d41e0401c4e6001c1f24400c1c0000c40c2e6803482c02100380c84161030f0798281211992140001c40c007590003030740103014200c212001c111070480f00131000e800583c900354507002c1500f840c2c1c10a03411540b000c4081901c54954900588030b000362440100241d5282240c0f4a1507008194003030040e0f0000c00080700c81042c1c4821040c0e088a81c00d03500c20400100600c4200601d601c00e40080020003503188020741d203000c06507200380c9103401c15140c030b0300c083e5156020000b1650703221040034010a005d100034085d40d0b20780441706489080902845018601c0080000d80c020300810803900103011241e0b0b400103541e52861341c030340250444001210079010f240e040110f4030038201c0545083d20181c804007840d192078420a4406503010010458026800b0f110004003507800f8009408800e0180e000822 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 2170781 1250 2169531 2169539
    0x3050f060708090a03080403050702060a020a050c06040305060a020c0c0306010803040504140708040b0702010605030a110306070302030118090215030c0d0e0f030909040609020d080415030504030c0204020306011710 94
    0x100303259009010404025039a0200b016209001407015041a0941010506a107450400701d036503103c0d124010350000c0c4005920305069034001041c1c01348600480a45100800074010042c0c184aa888081d02a61001c80030400704402039000b001c41510b103c0c11a12001000b50200b0709040b400d80c00b124203900041000c0029017481d0040c010b1008881c209081c1515004902802c0c802000e400a05294014000100c0c0c0c00d000b54060005000010116101c01b0320a181c000380d0707078050048807802402000c020601d604d01900940341681c0000025504504402444400406600f0016684180f000c2821a0202210f000030342c01011400b0740b4070780e55010304242c4401d031111600341400c5903200340605810028080180d4010384411034003001c2c5500d031400c156014003a844000703940001c0780600241042013500091085504182c0d00c00c0c0c2c6000c40c40320507422141e0484000d00811181c071144c400600d000d900a42d4803a00505003c0101c004400d948100d030881200c0c90802c0b181740c2c1307900344 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 2172031 1250 2170781 2170783
    0x3080a03050c040506070605060f090c0703031b0206010302060a03021909030302010b03070b030c0903031c020316021203060909100603060608150114060306061c0203041e02010906050a031503050f 86
    0x80d80c040702e0080d4003841d0070319003000700d0322901c03421001a0a0715070358004500e1603590310f8000404007030014001311060600240d44112030f4849041100800d113001c0b548003411020a08843d446403241c6c0141c50641e1031078082c001750b94810307442c4004140c1c2c08c0003503014142c0d00b0706141c4104035155448401e0b160440c42c0103421540300c61203a5220798030082c0104203550301c4800702c0307a00c01250841e40740c035150320303d010174610b0007a60f10b50f0b8809203101054001010700c0d5030156125100303d18602200c1461450142e89542d1900740400301c0c1c0da8100700050507414410314154000300220110760800518540c03400468450b0b801c01c4038000c0e1552010058503100b002072601c0c4410007101b14015502d0054421103102140340e404c0c0c0940404000280f45075540c4003510b040070003240c200c00451003101903081c0203600c22141100c1c180d0441a2000c0d00d040031003240c0500f01d60617180c802c0e01034103051040e00c05070000d030442000c0603210441e10030680c4e0104000b42c0250304c902c0c000c1c500030504441d82 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 2173281 1250 2172031 2172041
    0x20a020706200c060c0f01050f0609010e04050a0204020702010509030d080403080108010204050102030304020409060e03030a0b0307090b030d030504020406150309060e030f040306020a020307140d02060105010807090306051302090103080a03 105
    0x110302c40641c11824104110020450302101181101c8480c1c0e60150300c80a40e04003202131160040c15403801c0201304e02d020462401c1d900c06c0e203044482c002987c0e03ca04205001715020340d4042d25a502c4204844014182940181540b1f80141859424884400c0c0000d01c0d01d02c10941c1000080d4803501407000b0150080d0046001d007003018025801d1500700b000003036990100600291055882d0100141032180c141e00c2400d90381662420340340d40380303480b100d0076010301807045900b4001d00c505600001c405986200740000164000c02400190000c90300445c09400c0c0500140c1c0c0c410350724180003502000b540c9800c1c040655a484c0420010321a00300b0030120b84083c104001c80d50000c00001c0d40312141801220140c0e5030101d0010380702d20011000728030b580502030006081c00301c07031950b603401090f0004102507480096402c56403030307a8841004641075603040e01c2090100b186030000313000040c2150031150340140b4240c840c07030b00004c1d142c0000e2004142a0b0098a000d10b0000381503802c1a418012 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 2174531 1250 2173281 2173307
    0x501020711031902091308030106021f0b0603040204050414030d0f05060f06030403050705030c0607051902070302011d150703050901081008060103150e01090b010503070611031209030c01020a020706 87
    0x34160403c1e800c0d1074103c4142d003943c0020b1160025900050b80221001d5006940e0f40e00702485c140ca0350386800c0041d40c2c540741321101c0700e81f01c0e44040a04007084414080c0c0c503140780300030744120300f50745440d824400a86005401220b010014a50201600c44104064011466012004180c2100e40800e46040b0707200540b140c4d0140a100e4400c2070641c8410003102c1d045640740c41c025540b0001c504215095004074401d04449010710300501c012180d0280c05091202003a2401118542d03414070181c0e0fa880c0c00d840000d000c5808540d211324080c003402e400c20f01402c0098404905440202c406040070344c0048012408540007180705400303942c3c08100247d001c0c5100303543c080e1543c00d03d0800c80c1c0e03405d0140320003000240750b000c0e81540d61031983c2180c0d210072000802442075061a240103500b880c401d0041d03e01911400c0000280144202c0b29444151303ca50055850884081050703810b0810003400117916100c100410070004009100500d88440f85502030440a0f041a000a100d030240c444 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 2175781 1250 2174531 2174533
    0x2030402030d050304030c0b010f0e01060509030a021009050405010914090a0b0406090f0807050d030b0411090607020307120804090f020309102a020f010f0603030801030807080906030103050102071103 88
    0x4204001030328001044550980c0c0c1d400e05544075662881d049a503c40c04241c0144090741e04000040e08003428030311715060b14041040b2244981c0c0b1803400311218042c1c1d2031038035455804074000c130380035080c1101d007004013040510f00b03400c5081d05c4602040c1590020703800360a002d0341d82c5800e0044079a00402150300000d1460140c164000242c445203c02c0402910260040303680381400ca04122003010307000c0096030720101c890780712000c0d0f09149440d115040c04c8900401c1c10406100001d00e018441d5042512607191482d040041500a0001c00d8014910803078043c8264034010801e0076910003050310241c45030001d540e660b03080501000070b54050300b015100003801070062107805000030802c400f0701503a01d00005030000c4890101da458142c1c002c04400d10703013111240d1200700c0e82e0228000030b103014408001d02004035141d86000031149148805000100c0190050000512020041c80343e18020f09115060041d5403001441940c000c0e030048905039030000c0e00c4030800040001681c41684110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 2177031 1250 2175781 2175787
    0x507080d080106140405090f040302010e060106050d050907050307080706030b010201020403020906040b01021509030a090806010605070b0703020702040f05040510050405060a090204020d021305031203070f0f0509090702010c110102 101
    0x480180180704103001d4101481007000b4000384801e003903804d0b5001000010441d0000b0b0401440300b861031107059030160015403e003041c0c02804131000401c00d0403a20141c0d41d0f030740b8000007010700310001c01019002a4060140c0e000000311a40c0410a05000e4401c0d1030141070303113070310303150000e01254641300d410340c156401841704002507170f96407840310303484281500c000c941c0501c8000101d0a210460703c00820350705010040c001245c2e00007000d05a8101d10340c13503811000b5121004156510024810304001400400010001500035008107402c10010708025040c44440d500040135203042d00b000e044400d50f06c5081000f44403041000003444101280100581c0c140798440039103410009150302d0203162144403103001c42d1a1035046810060300f01030704544400c0344000504044032207108640c46031042d150002c1440c0c030361500308e0f0f000e8034036612042485c1c88918801c0d518290902e04034818410280601007542d194050024410600c641c00098071203800720004e0868045000100c00980c814 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 2178281 1250 2177031 2177053
    0x303020304080f0f06040201110a060908030105030118050c06130803030403170604051b0a02070506040308130501050c0d0e0105040302100305010501020111070201020303010e060d050a0302010c08130201230c0f0604050708 97
    0x114105e42c01507020328141000c164208192450302074500001004d00d46441c43c81014480c8041c0594142d9004400a009822041030061420444940081d2607500101140300c1c41d442c0007002014105202c3e4404201c5a54850b000c80c00c54004440640c003180c00083c000001490f0030141c5a40043e003201c00700660b09100403d0000340550250144c42600300042c41c5002900030010301c3c004020050880e540c8580700c2c0303801640c0307400030b010948840f08054800b04a40d80600305943d40889148020000f440507000100c402c1c1c0d00d0100e016041c00400c10020000d47c6a00e020301c401d290751a00c01103043d5244c8000207003100c3c140310b03290341010401e0001900513a030200c202c904444442c0c030900c05d00c0d11031100164490315001d4004115214420b4258200354041d00700c4680c0f051b8580f03500c20140e549403006152643c040b50001c1c0024002c1204582201c100c0040c40c0300410041001818440e0b0013026618141ea640b1082e21140d001c40704000802c4410059100030b00800005001c4040403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 2179531 1250 2178281 2178283
    0x311010207090e030717091e040c030b060d0203060409060903030c11060115110705030a0308041205180618030d030e0606030106060806010c0302010b0406090507080f10060309020307050a0303020304080f0f 90
    0x19048001d2411b40140c0b04424a000242c003640d01e42c0c08014a01005101c04000c0480700052904169010b903003840500132a09001e8882c150b4080d40c06000303a40782501d0350107a030000b03500041003158840c0d0f96030310b4203011485038818004114441e450014810582c603201a25800482a00316074960003100148036100a88100654180b541c0c1032072040781140c1d00078541048100d0f000a82c00d8442e12007188141a40701c400c00b8066400307000c0c801c01e113040d60b207401ca030180700315400f074001020001c01a10480c20101c009114801801f8405094400d0440000c0d0910200c0c10703208000a072a00c6442c800c680060140e540c00441c120001c04c00e051806001500301c00d00100940e040c010321250719000c0c14002e40060b0355840004100304210350b12031101d00010081511060000754441d8001240344c80410540b5003d180c0c0064000011072a14071708402a2182403400c03030301030284402c00034082e00e510b11325001442c8290003454032a8203181c98070f4506a2b880043d407525a100d484100701c0500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 2180781 1250 2179531 2179537
    0xa030203190309020904050102190c080906030403050d050c190c020907030504020d05060f0f01120201020705040b04020903060a060303030c0206070e0906060f120402040c050403020303030612070e010311010207090e03 95
    0x54804021441c40d0103400b80c1c01410f5400c806504582040d00300020060198010b010400b4015091814500305074802c0b03c4000300c0703010040142104000d940403d10744a806107500901c82d141140c5012036400d00e0070281c500a40c1d4045403007030007040d031070f400e1060400e00c000c0520b598644070001d150542c000034412140900b03900d044c0750b40c03000407400b55262691407482e87da801c041151560300388107000c8290030703008032030910300d242034180041070116100c141d6003000d940580c0180700050400c000c010081100344882ea60081d0f00b000460581e807414410304d4802c10400b000041c0d8546181000b800f42e40e0302c03101000854101d0801c001400b42c208200004103201a14400070b541d032010049945807290b44600a05e9580c086a07080d07803c200d03500081c0c441c074400c1da01408802d007004416a61801903010003507140d0014000603079a810129201510900c0c841c00b16034060b5038885034010301441c04c0e081540d520940e00042e02455804015840062114403403c1004400c0303c1402504c82c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 2182031 1250 2180781 2180797
    0x1030207080906030601110a0305090f0901060c300306050a0906050a0902030a020d02030112110301060f14030705040203011d06060702010504030f02040605041109030114070504030f0311010513050f0a030203 91
    0xf80011001c19a41c3e4407904c3c200c0c90400d8028102e8100ba2000e00b009450703038000d40e000c10700c10304051288002c24189084640d0480308142c4070006012200c2d59499107101030403414088004a5400e419100140d902100303c05071056180080e0642c1000103118521075070782c208980c03c9040480c2040b06072502c0b0345a07000c65a403010010b84a480d5403010001a11410f42e04800050020001003040140c7c01c0411010364401d402411007030710b40c04181826500540310700c030580081c1e40707410410700034043e6841f03000e4603000b000c1c0c0722042c0e207410000e0105d80080c4c0042042081e20010021881840c1c613803590401000c5410701c0c18403109a00082c214400ea000c0200001840d54240301191241e8110f20084d003001081840f1844d00c0c120031360010f4002055151281d030900580c541c2c0c1c880e4007440e40d030241c5c0f403039602e0f6840d1509540b0340d000342003502d08045042001450882000c48028820300340551140c510f41c5444071001e0900a18011540880a00c3c90704a44294400681c000003100c41d40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 2183281 1250 2182031 2182039
    0x6011208030a0609020d06090f0507051611100201150603110a03020a030b03010f0b19031106090a08010c020303010f080c1305060402090616050f160302130609021303020a05010302070809 82
    0x6507650444100c00380c040ca9024500450002c035035842c820340c01d501700606030b400c442c10400c04058070b400300b88250742b41550002c2c046441004206480300a070440c40c1002801280d003003000d054000080f900428020381e072800140d64441c4074000c82d00d07009826800605075840e09110104502580e59424030596010006166001900c034440c58000c0d0882050350200500270014603540814100103000f6111005124882c60a189030043c01320381c0d11001a20f030044610401e4407642024403010764803108a46a10844890000035005403d0096110714103c50340a0b544030351600c03038490303441c08581e007018045400076074401c05140c075243e04000003200345140c0403070703242c445001080080c4281c01100d60041400950348413111444d4110f8540c0600c18411103c15200d52a01c0a03226a1011540100484d9116013003000d0f140c8075070003081d50252000e0002c2c1084c2d0382c0b0756000c12a03010610101d80314421040410541c9084002d090080a003070800b90302c0c100251361048031a02c80d04110502c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 2184531 1250 2183281 2183287
    0x1030507110d051303020409061a0105040e010e0402010507050307031107050105040b030a0f060902040303171003020102100b0f0a0305060601080108010b060702060c01090b180601050402070206030601030f090b070f0206060306011208 102
    0x10300704e42c6000d4400107640141007000601103e0810b0700c003804040f01007030100700040003800300c2540f040d8100c80132118241d8020713055908240e504910808007400030b138100314040c0000004075a0600090104a1003174070380c004507a140380944d03802c0c170701282d01807030500c03500b40420002c40b059042101d9019007410b10020b000341c0b1900d081e2009002c1504004100b510220f0044101504030002860051140380d00701841d5403092074620280c902408020300503000040c880020110700d170000c4031032410003080002070702d8810003c02e031051030380c1d070080d6030941c49502804017950300440828094080c1100a00040013220017003001c5202c0c4400c02801a1000910045885000c0d0301c40b26500398480c0101003103007068000f40c8444101900a0300090240b08000035036490300d807084540e110703405804a810741da981d40040d00113103425880300702e80d603444642d41d0340055421032207144184880c2d00e811072008440e07100249070150060000c0e0190340f0280c0107003c540d0094074002c41499003c82025030f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 2185781 1250 2184531 2184547
    0x8010203041a0615040602070501120204060915050d09030309060510030201090b0702030307170306131401030201030f18061b0206060603010504021308070306020403021008060a0504110903030c030901030507110d05 94
    0x50096860740d15070750079131000304001c0344465010500301c007103034400d82ea041c00d0121f159407a10700701c0c4918401c075004241c11080800107440c200034070b81008020f5082c401e041c058617030311700001c1c2e0300010001c50019640d003e2000400005109990308100140c407640d1040341541d001030103c00e507a000f0614400b01c04280041156010021502d0079548141c903c01050100c200091003a0000e45800303100d030034080c10940314403d09103d4580c2100191402e0702c3c1e140d01c0d58006400030310101d42c101c200c680e1074030035170056140600721410941d031180740002010001d41601082d4407002c0c030000c400719003040302402007507038900c000d803419240c08940041c3c0d200889203864043d201543d00044039806110400000c2c4400c60f0302800807603000741d584500d040a4204d08491004044520540c0320903401410300060600368000e50f00c01c90911401480e010400000a2468010000c7c00a00c2d80c000228180c8550b49801034640180180c20a03e4441401d0a00283c81e4031042054100704140860290 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 2187031 1250 2185781 2185789
    0xd080603030d090c0e060d0c050609010302090603090a03080603030903030d0c05070c03030206040302070e090307200a0905040c06030209130203060307180e0601060e0a0509040206070c0e010303030608010203041a06 94
    0x18a42008140c1c02c2000c120300c1e140135020100d0304d12a065066908000007100341c2450441458002d50082000f40d4803400c0030104a9140c0022011504155080c0320001390364403408001d40c01a42140d0003014180c0d5140340040aa00c0003c01860080c1c009002d0110561400021360b002060b281c0c0b00031440000807082150103010341003000e404049840d600009150b00071503101d00690203907094440385611013450010062080c5c900765a10351040103600045852038041051980b0b920070f5070f548010070000011990b0f8102d8111000d11542d030003e110400044142c1c2d0070090116050650401d6410000146400c41c140746e44511079800000180660f81c003885002c010309600500404a014081880c4c0700808812041c01200e101e60800410702a004807842081084011300310503001b0304201c00c2c01112040523004a810540601c0792100150030103411a0250011000240c40c643c554180281624825400303507401d6441081800081034911a000801d011101c5c010140b90721030300045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 2188281 1250 2187031 2187037
    0x2090607020402030c03091005010302010f05030613060602010f0b0301050103050705090c0706090305030a0b0d080a0507060213080d02061506030a0e03120c04050a0806060904030e0607080a0210060e04050d08060303 94
    0x20342c001e00c00801c000e150103a01d4051409809034030201c410b480090b03030b8807030200c4100f0b000c041d010800050444012500c52401180d202102804049030290707007072182c40c00e5408170740101c40543d4640d0303407940c581000c44c45200b4007100104c000340a41c3d45152151a01d5040b81e001e814020111000010f10f072408103000ca0790341c940e0140c001c001c511810f060081280d041601c1c512480c50134560400c001d8602600741e2002c90b90040303c0b05140c400d00c0f043c1903c481e402442c00321000341c1c090000b500c0724441d0581c0781004041800c00b1700f080b8050380100a040040080803400705482d28982a005603c0c3c0006030790b4030152401c400154403100101c0701d841c5005602c040352100e01c0b500c00f005500c1000001900c00c5400580349090032a868a410301e8658004941c4241c000b0301000018002ca4410b9032070307010b90321000c1c211904d0701160792110030103580700c2d10398000580c0c0f01403031541019203140b04000040203110104a9941443d548541d1506881c80903802048503a0000c200e40d56024012 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 2189531 1250 2188281 2188283
    0xd050a0506040b0708011401090905070903020301060308030403090b0301060c0303020703170a09050c0103020c03031f0302100201050f0a02040501020d030b130204030506060f010c15051302040906020909011e03020402090607 98
    0x403070301d00d494240391120540b5012540800000c0401c40001040c440010b07070724100000584841c2c004a0501c6001c80050000030910b03070030029030880002c0561028403800c4040e60050042d19035901d01805c0143c24101154400754105030100010015594045402607141c4d5145c500541d580d40c50342021107200c5610b50128410341c50701428412a802c1c15801245c1c128407503000d68102c5c0d032111300154200d000d84030400f001038108100040e200460040fa4030303002030070889040d00d0951240c02241e082524010b004015039982c60a10054007100c100582d40024282415481c2904000000391a20030444940c401d064507007501b00c1007030b82da00034013012400c100d600c119111580d03420003540d036036416203c41b80200f405032440c0d119544150f40c2d030725170640c00c03010f80b0f80b0141c05108084003e080c0141503036610350350203038031500590300c5008411034107024131005a22000018100300b500c1c0c1040c5e0180e008289207500c500c0030000000d405604036501201c0c0182c4a54070200456007611903040c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 2190781 1250 2189531 2189533
    0xe0301020417060717060d0311030403050102120405010b090103020f060703020709050705040603060b0301120807050109020607060c020606010f0206070e0103151d01060c0f080304080c01060305071a04030c050d050a05 95
    0x30780504a1070000a900344501351559070410940c0c489514100c0c03400054480ca6008a80e0f000c0c80c0c00842d000e4a40704600c03460400442c4e10b0a135407a03c0d59401c80c1c100300e02c3c01d9031108048050000744402406580844101152003da940d4516800200c00c4a00001e640e07000d090081004801e0500a000900c01450200c40a105d1450150001481c990007402154042031a102c3d005c103401d502801030303e0681c3c01c84d03d8402140203281d1a20394841c1c02c214002c840e03964071801a14011f0311400083c22045100780701c0480d80301c1d680b02c0f019042c1000182010304001c0b04080d003540456000a1041d0040f07203030b0400101e01d02c0007a0040300500726000c459104032a80290010703005c09003120b031140c041d00104c08481c070740e40c036000100e400c00841c55015003100c4a0031101004649128015034209200e10103840c07500081d25082c60135110740380d10988854110800400c85c040362600818001d010003604545080d0540d541c2120b000d04500803540291035900d01c00c410404108100310070300e60014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 2192031 1250 2190781 2190809
    0x70203011104080d05030121051906020424020604081b0304120b060604030503070206030601030902120a050c0103140f0702070f030b010510030c050901080a020409020706061d070f0e03010204 84
    0x1c0041442030b0300c00e00c1512603510404150482c1288580180d9040c1d0b85521100d0302c0c031010600000324400d64820050b2454000c100110b0009500c02c40e04a0303906116500160300e51b494008141007958026040106400200e140070411a030b01140c0740b0791207540700c001c241e142c9140d0303c201c85589140c482c0907602403000007004286144900e001c1c00300d4138070888481c041a07680000340b05540c029407000420b41e6000f408802c0052a01344c000d5980040f041c500080e50a00c2d90f00010004c030000511a04940c00041d010001e01109008050004000b030a042c07058840740d581040d2904802020280d158580318003140c4024400e10402c0002c2900c0300d104900c03c0c8e12410000d054010a100300b41c07003180000352011185010b4000c02d84035a480da10313a01d01f0320307546100541d9007450050030340c03c0c0d2660811010451101600c060f2030400e0003680c00107a200d08044440f2004e00b104188040701d4070000b01080115a0300100c16440d603002c0d0314020b08400048008640a80243c0c4c10102e403c04440c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 2193281 1250 2192031 2192051
    0x6090809030114040204060807060804030f050f0a0c06050606160803040602090607050303010603050f01030b0703020a02160801090203010f02040302030727060e04030f0c0b01060e030a0602030103121709060103060504020607020301 101
    0x7101c50f8600840c000c490070810f01ea0b4403460b540c0e941c4c400c0d03c910804030360071400040c01303c0c4c0504201c1ca0f11b40007a081142ca81900c0620070b458503800186800045034040440750140880707440b40581c000d2003603440381c0c5040c03000045450b5811511400501700e05000000504000141c0c050f203c1d1107070060002a00c9a110303103040c0d500ca405c00d000d0100041c0c40c00c03002886040741604580d0480c0c0c0c00443c024819210942c0440195001d140064254421026503210271108000e0001c02003110b18000208160503104060030340d11215503d034181e0740180024000f60350b0100c1e0640c221200403424444042003404222000b0700a101030540852810340000381b1040041051842039201e42d41303440360000960801d5403100c07081800904500c1982c001401001e000c0c22000c2c54241b00281210782008041e91500160381c0242c00c01c41d407004020b100d400300c042e0060310003043c50b98a88500c14a42c90401525a9908030502c40a003416403541d01041c00c3d500e40104480b040d6030050000d2140c00c2d05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 2194531 1250 2193281 2193311
    0xc0409110d0803010e070807050306040207060b090705030109110309070e04031b20090f01031103030403050106140102010e030a0c060b060405030a030201060602060603010212011502030c070e01050307050901030f060908090301 99
    0x3407080c41445d000000015400a104058081c801e000301d0710350034203541f02c00b41070000940001004a61813a51101c2c0040745075502051648a0701d46a5180341e501c0d130400f400302c03054989041d00f451100d0028010321450000c00b0814200355501c515176882c3c1592070781403c03a85500750802d001402640012460280441490301801c04510742c03044003501c800741c0041c85030344001200c00c500b0b2902600014000078820345226013442c00c0080441e410729403262a0302d401c403502d03030344404100c1d1001880703120316580a00510001e040f111000d542001c4041d00003809125000d50010441542c88a1800c41c036136070101650041d20004d000c403484007400d0729019000307207414013451000d482402d000521902d0140219200c121005200104030303482d01a030074070340c1c04201c8482c4066000c140928103d0141c00c1040400828941c4602c4129502d003106040c1003c8007500710a0003030138500e005201294510458045041d4840c40002e95807004d4108100303140640210140e15500701620048403c00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 2195781 1250 2194531 2194537
    0x6040c02011104090c09050901030305030a05090c10080108120319020309010f0608010b0405010e0606070f051005070f0e0102150606090a0305010606030b040e0102070210121b0908010c0906020c0409110d08 90
    0x40d00e5258189580d03100d40808c2444a02444002c00040c0108002010005590091038111080c03904407040043d0346030010b43c6a04540c00c00b640024200401009200d42c1006038060010f640d0010070315608000c3c10807051400e6903000b94204540000c08520f00c0c601c01d40c8001e09452080c2d004129090329003c00074040e1074146c1f02c240c4164200360003c191440b40404407400b078100104550702c3d00072643c0c1c820702e4041c00d4030025185802150030f80717038038012a0b0043d184103181e590b80f8003a65101c0742ca809882103410360303440c074115404060b01d140050030025845420210440e45c072901c800c40d440004044030120340000301607500b8141d001a400fa019040741c44105000c5509001e8001c04404c0613080340520b039006580680c07001c0158013010f00412110034803102c6640046000100058054880c8806c0c3c50004005900c901c2d08003c144801c2c40346990030081c0d4a0104000c6140c484020b5032035040d99030091240d541c8400c0720301000341c80c2151030074400018042c1e0040d00b0392030504c170070385070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 2197031 1250 2195781 2195801
    0x2313030b15010504090c0e0405010806060a0e0702070603090203030c07090b03010605030a020901050f06070c080a03030c050307080c090118090c0f09030305040303080606090402030a0b0a1205030306040c0201110409 94
    0x1034100205030025160780c049284600706945590500c1d16041020f07018295501e84a01404010200c2845a88503070103241d01a0110100500050503c9d02c2404514400c5a01695a003d01c0303409101146502003036500884802d0724000c110720760707140002421072181c0c2869801c40c2c400d1100001d00f42c900c5410580301520f044008110301d6075114141a220203903500c0082d805544079005101ea0302d060b060310a12000090001c0b03040209a558030300500d982c07a0007065141d8800041101015494026043e422030313540b51880c1035080c001000380c04800098080508040c01140f00ca107980d12803940c0c1e020a80d0070350101400d00d580c8200076001001d4140c0900c00180165409241c2d66000f100e18a00b16549552450724240c40c503181180c0c000406440d880d80036101304070f00e040e550f855001440c041d1841c01c5000401510078410071800c030b100d80e0700407156114018039400c0400c20100541354071520030b5a01050001d28244224014191130040d8203078800007241c0841d00600a0340004415 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 2198281 1250 2197031 2197043
    0x60a0908010b150d051003081612090509040f060e0706110c0118090506030304030f0302060f09010b03070b030c07050604030903050d0305010b030703020c0c0a060c06180203030703231303 82
    0x7500c4030b01805a4402400c810740002641003058402001300d550125038040300300d4800e81c0581313459070b0782c5280070340c031601590202c0040f0361600014442d000e568148044194106040520314100c0810a0321000820150041a00500702000c0c48204e41000b2480b100c190141d0720410303240d0001a10400b150b40e060355451044a030303484059400784d4030100c680014424925441c41c074080d40c58000d03150040009825000034000007001035035251030000301910a40280c502e0b0f01d0a44141c2800c408002d201840c268104154124262000310703900b0b0555010b0460a0303500d5841440042c580e1090140c004c3c4140b00306401c00081c50380c060002c1054a20502c141c0f0141c90f2004800c5042c1c803400c1c0681110701408001160308203010381d00030407000c100d040666121880d03030f10000d00040c1041d0701c86800304043d20005410090644511941902000c1860007903400c2a00030990701c0c040c0d120002d0511680008100704d40c1e0518a00041090301d0504095072100690844025600c0c2840704540c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 2199531 1250 2198281 2198291
    0x7030b0c1803010b0a17030d0c03051801060b0f09040204030803010305060405061608282406050301080a0816080301060c0b0609040203120a030b120307030f020a030503060402030c0405060a090801 86
    0x618541030144130000f84000700708481c464100a15008140b0855040c00e81b030b88020030104141d010140204c1c01d000305291000501d91400100e0000d951001c030060781101c1c2d01d0180244211081d00e000e9074074607418004840c3d205d0400c0d001040007482103810280c0341c2c40700400004204540040d11902c82c47c4a44196800c5840300f9007024a100303000e408034408205a0400201415010201000480c4040108205a80c003410240045540e5081c404000d600e08034103880303145484181c964020042450032601d0340d031401810307584a0031030100080003070744006400f0f08480c90000c0724101c0c03540c10107441596035030360300c40107800c80c08030704801c541021110000030018608044490312664002e0040d240c0400106900380b03059010103030f00e0080c5996210000c000344c0f0782e50884400040d2441c02942d4545240c103000d00b00c1c203001a500c6046500440303901002079440010380750021400d50f80540c494130b9200c060798160145400898202c4000710388405004c0d40091224211b940f04030007044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 2200781 1250 2199531 2199577
    0x4030201060b0304080405010503060d060203040b010503060106110318030c09090a03030b09060904030305071e05040314060112110406030609110405010905070507020f0d050a0b150a0f030b040507030b0c 89
    0x2c190000b110090002c1a0a000c10802c950164008542c4414024060b4184249ca507a5000c02c070b030000d9406440041c8240c0042c8914101000480d0140401d401c142001c0c5008502d440e990344107134445400201240707400d101c00d40d10104a2288443e80081c0303207004524042d16119503030240c0003020780c002800e1522040f96400c0221032140104000752800c20980d81c5c0d514154090000501504c0c10007914407050101e889881d00385d185407005590740c00342e4031451824498281609160a81d1031078000400400c020100030342c0c020b400f140d00101c070150050405001800910985d400a49030070304281c202410015002c200d1044090100c6041106076241d103849012038404546100c00304070b0030420b050151510101490510710300500c40007a02450380c0d20181000072102c000c9403503060310f100f4403041202646070541510000d940c841505403802d03086c112140c00f10710024001110300808074003400000d01c1801c000d0f42d0027182640090600010f40a5075034010103c100c880003200c01c2d262 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 2202031 1250 2200781 2200799
    0x160e0103060506090603070c0605071d060a1709030706020d02030115020a0201081302030106090617060708040308070f050c0604200301020301030b06060906040810060312020303070903110a08030c01050403020106 93
    0x80250744024042600301550201817146903071000c0d02810034028880d2064001032010f000d030328800d40c0b81e5030740e0182440494903480f052a02d2801001e104000c1441401d1101f54049640300c1c0c64031526151110f1500e0b5180841d04501c500000544000e000007580b8001c000c10717070010b6040f6809401c0e50f111040e60700c0d41c101e842c0c00c500f440c002c1c009818507012a99804402c9034001c10309000900000b412540c2da101c510864189038405201401c1040d43c80300101c006004240d441401406c25030042e1030966402000307964010491024040304c4280425010721980560b640c8450711800c0b103c02c0d083c039040c52038a0000d01004224101035261365401c1d10700707040c0252412282d00c0200ca50a54540b1810420305401c4041c590781c0180c010b101c00240109d0030464021001c0c4c203c00700003002c900b1070800c503040000b800c031a441990b20410138811803d40c0321202004680c0c21031140440c54a5000c005190030300c050307101031803a20000c40c00c0c1c04103000650265000d503200780c008210f9507956643e04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 2203281 1250 2202031 2202041
    0xd03050711010515130b0604030506040605060604080304150504030506070801030203071401021209010201020c1603050d1707030507020c0607080309150601020703030806010306090608010c09082a0a05030105160e0103 95
    0x105007020144c6201c4401c1d081501e2104903a0b41c860707401090f8651b182010560581065005650582c0841e00344400e0042d580314035500f15005440035031415040000d107079500c0c45944150004e0702c407a02403074141d051062042c0c170091540f00d01502d07400e0625081c01400007000780000d034070034050104005604601d0444000d80190180c02510040813061a051075580100340c50f01d040d5502088003400c00003041c0061545415141030300509d450441c10140e02d40140e22030801c0601c0301c05010070140c00c4420015550203800c070b14000c0340f00d80d03e41c0b404070304010040161795080a80071801004003c0075901961040c141d100880b02e00143c407842da5a0a201d09030768107401f5821400d000e0010910036440380750711050604004c2041580c4118070811240b040d88400c03c07595441043d1805564000300c2c0ca001041140020965800405c100820020b03031010182400305255440b11000d0300c400302003000800c0010000c11440c41e2100e036204104140100d03801c0000e8004040c1c041660080c421 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 2204531 1250 2203281 2203291
    0xa03030f020a0f0c0501090506130507080604031b020d0b07050703020606030d050f030c0408060103030c0201020105060316120203100203070503040b0906100306020a0201150906090b0a08030a050304030c050d030507110105 97
    0x5216a43e2480c400070303103084004003000d40e407039500e0700c416101141d8204220b90003220b4580c00010140303800c2c01c0c06810309441d504045200c1c1c0094003408040b0b03920152800030205e0400181e0f02601081c07000030402d001c20300c401044002500104010203410001909426000e034080d901c00d692100d0030140c440150008140204100f48000c1801510200281d94040c141841b10340c0f40c140c9408455241c0074013684100c00140426016000319607083c041c098004400782c0c001e1140c280f40c0c920800203020070f03004079120051000c0100c000d564041050f5031460740010811940d03800c04c400d00904560007202c0a550214403079011401540000900c24454240b104100700c4450950765100080d40c030442a110440d902da04006074040e85d8074010000070b0406010004115140070200c4080d5031140100e60301c901080e010805c0343e00404000c4800d50750f100d00d0603a07600c0c2d4481c5400c1e03a00304141080034203680305816007241c07480e81540c0128003400a503110191101350100c551801d8a0040364 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 2205781 1250 2204531 2204537
    0x80a0203030409150305120301050a0602010b0112020a030908030f01140a080a0f020d0510060311060a0504050d031404080604030201050c0c0a02150c0a05010203060a0803040b030f070504030204020c0a03030f020a 93
    0x108190f101940c8440004052503810b100c3c1c4030b54030b486040c0f8000c5e20411061032040000010041c0d0b03d080410100104142d00081c8a546201340021f0805e550481400100d41d40001d503040d26035100c0d0b80304030046940031480c20f44a00700441c0d0502c4096003401210010a0701d03040c41143ca05d441d141c0e0301308654540008195107111951070740c440b614410130032a0803001e4070340c0241c0014401c1c05001088055104001551441d500300100d2a0400c3c1d200c490054200b041401401c60340001143c0c2038900a0710f03a109500414582155016403441d08800606030126000c140c2e0031020078514000d43c000e40c001c0c451510f440448107880e1281c04004555980051004001820860b10702c80b02d810000b0205400c1c03a4420796283d040019544003107805950000c20403c6a1800043e10009060110001d504050808a0b216150310014084d01280a1200c000401091080c2c00329005140c1c00b81c0259201d40d0424506070380e0310b158030f40440c00301e810041560102c0320341d031027501d0048046603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 2207031 1250 2205781 2205787
    0x2030709060f030809030c0d03030209040c080907030201030e070506030405070e060303040b030103060510080d02030403050601080601050607080f0d020f0711010e06090d05010e010903020619051014011209030216080a020303 98
    0x15413000b00b203a0240d10866050700401502d0616a03481e078200c11341e01130282c3c4025a4403c0000208012511002c001500303228142003803090301c050001d200401e4036030a003000110781050800c01e514200240c0d001560006000041008000000c900e407c115582951000410345441041685a02447c01100500b12061004002050309070300181e42051001842402190f01e90028500380000740c401c002c0540e100060410811030100109401444190060405541042d000800742d1041401c050440c1401040c05030074100c1000448840512601c001c660ba5000c103200200107400048040c1d4070440e50b500c1096481d4000c1144401c034000003130082c1d1a013030940080040b840344004e010340340f665071580040ba50300e07400d1080c900f10074040c3c1c0003072800b8a8400002052148038999540c101824135050040d0410304d0f854900640314040000c19581540d500100c541c42c120016210314a42800d40e44000d0503004164414100d51002c0708011950b11060302c00d42c0d4030907025000b90598020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 2208281 1250 2207031 2207033
    0xa11030306130209010e0d24020c03030403030203041e0302010603060605060307020703060e01140420031216080f030a060501090f0315020304060b060406030209030105060901030209040308040501020d0608070302030709060f03 99
    0x40c1e070051410842c14100706c100701c18404045501c03512402c40031105c0500340c0e10031301c02403008031600100f000008030066240c80c42c039540403a164000900001c081c16004404a4200040d000e0484410300206000102c40d64050900034083d1205100030380e000c5107481c0000c1954204501200d105880980060250f42e02e1541c4906c003d201642e280c4255541e00c0401e08082000389050038025409808600506415041c032441200d8004248030f1003540b100184000020020040d81c40d90040c0a1411a0b80348e520700b4100d00901c07600f240001c406500204000c50351030990b0002c42502c40030703643c5d00c08064403140c903540406800c1c0000740401104074507044024032190000c551151107a00c001c150f81000da804525107800c06d03007000004c00e8010078160241e00f000d10400340d02540c100d60088540d451074000c146505806000070f01041008070019080c42825011203007000b10402c410041d599451990b240c80b500716002c00c82c46800b42d20b40c00205040d050081d0407d0300e039800e659000a0f071031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 2209531 1250 2208281 2208319
    0xb040c0306050f010c0606080d03020d06210602070c0308070b07020c0603011a13080106030807050105070e091302011103040807030201090b03070e0105070c030503120a0b150a030903020c04050403050a11030306 92
    0x481c0c8030441c1d46c16101c0c4400b055010080c010031449042030f403070142c0c4807620100e004095964a4000d82c0d10003100c1000e0006070305189011403503541d00070700010794035009030514485100c442d400c0075001030070015810042220702600d46110b0906075080d904112203203002c00600b44400e100c1e0032180e0220840401c0701e111584006e004c00690701c0da00c8010960349000180c290b03911030b803042d10544d10215180382130041c28010503500c0b090514007001b03144030300030000d101d4020140040c1d1085500c41c11300c0045900400c0b80140f02c41042c81141d4440f6590440345039140745c9800101c0c001481000005141421041524014429500d07140491200c080c01120507402001c8141d80380501745000001090085c0010085814802c54130512450012110710944401484203400342841c910002e80c20000300040c0c40b81d0240624000c40d20000500b0304a207084d891040c1d0355030040c900300c24401010340240040509030216181c0c050407075442052151a400110b800c244c00070700304042c43c554004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 2210781 1250 2209531 2209547
    0x712020901020f070323010905030d05040201021509030a020d0503060303030601030509030706060303030203010603060803090a0504050703110f040501020c010801060207060509010309050105130203010f09020109030206030a02070203030a02010b040c0306050f01 114
    0x44184112503600000c00500e40c41c24619a00a46d102c4c5520b00d80c003826640501001a41c0c211102d009100c00d070301c0f40d51007540d03c0c0f044458003001e042c2c2d9a0b021608582c0700b0700001c0460b041d064804071081c14540c440d69103d520040000d40507212700401e42040c44c0c090320a0740e2040500a029600710390350b040c0194003600c4000d040b400f0354001005540f0016800303100300f00165000355001030b2a0743c10306101070704403a89a001190a54020b110101c00741e540d100d26081603034000e5902240b00c5d00c503484c0940241203940c1c0d580d000303400d02180007004c01800c000078000f2141d09a007101c0c96402c3c01001592904000e018850041c2c006a40c24420640690014840c50f9418500000c207208a510341d117003100c4096401e10071060b101134030350003135142c2405404803550402004000c8188258000307804900300b031000074040c200200c00208100c00342c1c0d0503540c4040d0041c1c1034039540c5105040c000c1c001d0044248141c4a18600110640f0b181d120784142c0042c1c52001d46811444240140199440e131 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 2212031 1250 2210781 2210797
    0x80609060f03030703050703030501050d02031f020c030424090b0a0c030c08070303051806150d02120304060918060302010c03050310091109181003020d030203070206041206050f071202 81
    0x11503003041c10141d64808000901e203060296840a4913030407103140040039100e040c4c1c0210b100d072030400e4103000540e502040302c80e02031a00c1100310781c0309203a030002c0e800170780130b041c8264030940000b040004403000c803170b100d840c0c03040c0702c0a14007158015051030a070360350040341c090310300903444c20700442c50828007031880501828020b051881c140b09a50341ca4800e0381e4010602200044c0d10303602804007002500702d401600c20b060102a1259103081c0c0780f007142c0c4040381050948107940d58460b62065403522000c003103880b1080000d032980c59448090262000c4418411610b0080c0000103240401b121841000c05407907059441c50140480d0341c5041342d150b04040c0c2150442180d0f06000910b40c00c1c00d1281c4800801041e070078a03101e0142404001d10b0b2080c0f829005a0318801e00c0402110b51100c1240a040c1daa0443c0d160140508a040c128070358010340b0802504141e00040104080c08000000d0069502c5030f80c050040744d95107800c1c940011030658004010810104801121039215009404a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 2213281 1250 2212031 2212039
    0x5030a0503090712110301050a0c0203160c0807031b06020c090f040303140711010e030c07050d05030c01021305040c05070210050309030702040f020d050108060c0a030c0306051002010606020607020c0108060906 92
    0x343e5158401038000b8182d07070104480380100f0314450300a50400703000300d030352200f4407040c00c202e50400500040e440c1d2241d031000100d040f11907282c0000b084414450900604030384030494038519120f29101140010402c4055640d0340700d254000755407440050803848882c1c1c0909000043d45401d50303180404000580104e0505450300d2161100c504841e594a105105550320b20002d030ba400f1440c542180c0008084010382e40081007014503032000060070384200c40c41500c248042c0030150803c41d003580180400d5070b4180d400000c0f03581c01103040131440740507034108413000c0000404c00041a01e4920407030800079000781210002840d003a02a03805554007205800c04e032464401d0350307400182140c00d07031000c4025041d80852864541130b41d9204603800b400050300140303501d041070041c6545900402c0490020140c03142e68103003585100740c010f000140005400c410070036825600180c042c1074640a101c0041c46003070001500188002004588002c0684800d2240d031641028004d8104000b842c03e504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 2214531 1250 2213281 2213293
    0xc070c0e0613020c010501032d020609030c130501061206080c040c11010c021f0203090303040f05100c0c020102160f18060b0f0c0708011407031508060703090501050105040905030a050309 82
    0x1e070712180e0005103211340700d10000251030f40c114a0400d550080d40c00f134245000180003003458503070314a10301c13040407283c04841951702e41c5000c0e000a407420b00320221041c0c00114503148601c1403000c40d04100d0607a04151581441c0300c01c00c030600700450713203984290011580401d07203a10040c1081d40c441d4036072056500d08030020050110342d540c20340d5860754010340181e1007480e065501e4505604d0701003403148900320952641c28400c000e1039a038040070b0300c06070201880160080820000b0400c0c060700c81d01024013809a54124a03001c0c21010f00d91340242e001d401210711170f00303650441d40444000c1d00c0c820703500c203039842d8288030300c000c1030350b841e5144c00c500c8550340d4001040000c407480181c6141c814410103255078401d070500a074240304aa80c05942d65a060001d440c40074910b1984c1d650b0321590914001a2114800d50f980d400c440160340829024018403007072040311039041c0c0084217154000c0c0000d21031070f40d840003400f003205c40030480036003160400d01030810140c2c4908000c1d85c10406034000c03105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 2215781 1250 2214531 2214559
    0xc0f02030327030109020108061c050607030203010e0708010317090303040e010b04030201020d140a03050406020702090403080601030c08130206070305040902040902130b0703120f020409090b06090c070c0e06 91
    0x861a4844403056a10380b074030080445141c1210180c400160909038002d0000e0720743c50740040c4c9040c42c05041a40304903820030b0900c00b000058000c2c0225640c01000301c40781030408090140081d8000c6c0604505820f508000030f00c21400740c40d040f8101c83c0e100c107404c5000b0481d102c2c0315609401c005070980d0b050204110004110f800100124040c14040414554461440c400a4542040440110300317100019824102601483c030076035006e04524100452640d42d1490480024882c82c0710080d484000c0a0a00040c140c4c000c5015205d40350030b88042008144ca0070003694030030012115100940384203c901001818910041d01c2917620900b01a8142034a401150f0266003054000102da2076020400c0390f000c40044044100810030002490704d0441c43da14010010b0381d551a50704042034a40030031000f4130107150f045800400c100c0c2020054583c0c540703070104102c0c00c20303a480340c031503171000010460171414070f0100c4031600d62012001e4245440e0100c84c01d4202c0c801480303c0e901148544c500c030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 2217031 1250 2215781 2215783
    0xe0309040603060501050a06080c0406050706020909090d080108070e011401020c09010308090306101404110c0706050702040e010204050603160309080f0304050d020607020d050d0b040204080703060509011107030c0f0203 96
    0x1d0245109800104903036052600b840f012030001d03230210302000051414090100d02c903508846c2541c40621744240d5564090400c1c1c0041d01c114002c80790080840810400465004548801101c2c075030358844903146da9441c15035684115a001e46551440071100401c40701030782c502c2040f422481030069400c5004100002400b00109920031b88220a000403520704038902440791552000c0c07251295800203007080c900302d440b620f50200c002d00841c1d40d07401c2001c1c019000c4056981224101c0100c036102a1115001003454228290880c0201e0501c4e4402c001d0711418003e5801340c2e040985018119540c10b040d0540062a00754144241a03454401da40450748410007170a4452000705100da03030f030503e45040d9142c110340040c0300e400c41d000303002070091817a4046480f44800c141441d04035120241c00404100504c02a0a810380c0309100180c0011000b50120302c3d00d041300d00505041000c1d0391010180382c2a600d441010410641d8100280b10001c2c2c000c2d03505030203181c024041902d00112681c042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 2218281 1250 2217031 2217041
    0x305040204060f03031d030303010e070e01030e010c02030a12050c0a12020d09030e0f0a03080426010e010c0f0201020301060801120501090f0b060f0a05030706080702030d020708030609130f03030e030904 89
    0x45d400150b109500035070180c100c0e500180525400d070011407856140813901401808060010020004450341d0030316260700c039410064200001c40c000b08401e8042041c040d54952088242c030300441c50002c041c0c0500506803189078469882f01400524220480b40201c035407184240302d5144c120b42c28000c00750401c00700d20966400e540300381c80f095a0f07080c02900304400d544c5485034179032044c68150f40500c002070100c81034900301c51950004520309840e84c500e140c140030f41103981d104a0741c68842440c2100783d05400c103131211483c03619a00c00d13905248200320b081c0c0c4002d000354408509010010888011808103c0c043c0e00e0242d0000501e003e460b50fa1000c00d0b0340c10020a454441200061180e00c1c1b42c0031340f44070b0a60200301c42c0400c0381440e00c4086a1981003911855060100d948000f481590003030048604040071070308110740d1040c0700d29003101650003d590203030007441c101c80042c151a03003610051001a03000074031420307050035541d4110060000c510080d01c441c08280311161164607980a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 2219531 1250 2218281 2218283
    0x1d03030408070b01090203060d06110c010e070e010e0f04020d030c06020703030905010b0a03050c0f010c050d0201020706050c030c120a15090b031504020105070b06010c0222060501021c0305040204060f03 89
    0xb60b8a8030207080c260032684043c1c0000040c58410030500c40642d0f10894004401c550111009c220026001d011510b14004c0c0802e01200c0e501306441d0a0320314001103005415221004a940c0040c0d80761402c40096141c00c640d00d071905042240030070003500c2c1c03808802070701500c00e181619100085986c1e08044e41c21040040340800c2e22004100c040240c20f00542002c1d40081e200740c1c014501d542c94103640d4418900d940b60203a1002490801da503481000600602d030b80007000c55a00d8032622000074001d60001d801a07400e140f410011131110003004040701d010b034002180190800360b08a0b40d40210201c05400300b6403544d686c02c0303001302152207480a40c0081415a81c0001c100303110009240c28042c00300c24950940c1d06480400c00142e0b000420b44040c10b4210360604086c0d40c40f5001a50080300c3c011001c1d41c4542d08580c03a5100701c040e5210001228041d6509000d180d98a400580c0c2d100d200e007051400081060440d0030800344aa80569805400200301041180c0c0d50400f0035004481604 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 2220781 1250 2219531 2219543
    0x1020a03181a070c09110d0504052d010605010309030906050d06050307080309090a020304020603041b030203030f031f030302070911040b0c0304081203060a0504090303020c01141801050c0306041d030304 89
    0x5081001e0000c4d1490f42c00081a58001c141314602003100e40c030020744504d11310500b00c0d6503910040390911404000520362504a41c6038901100344a100c003003040e51050810407143e6080040210b41d44d4800d000d040401d65054460681082c2030510030782d82c6401030208280480d0382d40c0030005460754100008002407168201a6a03202d0545060252211000704500e269038010030901c801600c0782c1c001c881c2d101d07800503400401032507690035412408842d580040c0d410b1001140f1040b801d03480341c00842c0a6014104403a80d1044941c0a58800e02c5035440040c0146e001038104000b2030000390861860702c06990b040a182c40d4980c1030141c41600b1000600700541c1c00803d041c40b0551081000da11070f541d04048880c01d600c0c092000a010814501036903015503103542403281018003c4d0140c6060004290080c032000c035488414070000c480031622000a8840c94880054541040c841d0070b00036100180928515038461090102800c2c00ca40800d200d4900b842171200341e030b003083c40070b140514401c078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 2222031 1250 2220781 2220787
    0x3090f020910080d0305060a03060b01090905010605041409070206040605060d02060c01150b1606021806070b04020405011205060a0e0703020901060f020c0f0108070e040f06060e0301050a090201020a03181a 90
    0x180c40c3c1e1422403a00c2da030100303251428003030044541c3d070f5901c14422264007010105d103080c00080103c4000107594020300c0a18103000000c207000343c202d03000c0c0c41600c1c51580400c1100015004018a4086c2520382802681005000c98049802a00040c0c3d00100107040d090b60400d0950200e0700c964010039106105954400560b111007c020b0010310042040c02d0301c144c2131800c44d8100e560140c0702840010101c03580010700100307480410a45c40216035000700015210311103418144c44c03402c000c440032846149090000300c0d8040140241c60304107038021009215a0762080804002841c1d02003080071640303d200c40001c0180e454150403406021240d4071200140949000a854941a582900e100300403242d2206402c1c0d900101841c1d0088039403600608581601c0089801407241e062440d501c24101540803d5158111118a016042c243d000308010340d2021294422115103000082c01031b00301640f01e001203071055840301041d03041e84401070042a07455407070103c5840c88404190020f8404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 2223281 1250 2222031 2222039
    0x611010605030a080307050c01060f03060b0a060203030c0f16020405091b0a050d0b0a06030210020a02030c04020306030703030c0302030903010c111c02030d09030302040803030405060103020a080d050a03090f020910 94
    0x80c0144002820160020002403807261303035805003404000c1100040201c04540740c0314900094115000601030082802d48998a905050020b4410009001d00524800c00d000961610000450b84941810030500e421314201040d4903140f40d001180c02c0824001c00a18200542c2d6144181d03802502c0110040003142c0d8080e40c05c4141000c1e00c1c040354841c0320303030030410000c030740710316101101c2d095200c80c011980f55524001e4200a2856410280d0091711400400e400660001601078806008908441d00581c01100708016848200c9420303030990441441000001d0068a500355020300c00e0040d00d0500110380086821a0f002420800c0010365141040c0d1f00d0380c0051145c003807080b401c000850440440c011010b513aa200d04042010410750f900030100c00c1c540702c0ea06590140144c4419241d80c5d08081c144203a440500307000592003000c0c5280c002820b02c000041c0121060455240e43d0305100b03840c64141d0042690207815600c03031000420620041e60754041051064a0780b1500041803418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 2224531 1250 2223281 2223283
    0xd02040312020307020f0105030619060f18030206040608130b090303150d02030d0e0d05030c030d0509070602060103021c0602070609060b0102011404080a03090b0a090201020c01050301030b07080406150611 90
    0x15055040c00b550002c01c080800345e107403440760040c2c003c42801c080e9640c2d220034012510440350202c9000c0401a104008114a5031117446a00801710365560f940b0402030694081414004070700c8001e600280400c81000784a000311f8416034001c011245980b40107050384c40380031806a0440c0d8a0329503820010420180c814030440310200e000060b182c544509010340e010a03594407442d115442031226856020131550741b941c400046031a4840290783d01d9000c107039516035480d0043c0000e46049424070000414010001030000e040752000da0091205910356000d1001c403026013011134098046080c03106001c220280010a481403003203000048020250402804452800a10904590520300703c11180300b4113540d403581040d0044807096403004810341c2900103010b02d260040c150100319080000d115119845041418000c1e002d035180f26000c640111910710090000601d65181c00000c80c1c44580711f0000d00e0745c007505c20f410000d4040305141c0320000702c171200e0384240300068402d07170303509074000b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 2225781 1250 2224531 2224553
    0x70e0703090201170603010b03030a030b030601050102030705100509160b03040201030510081b030f0105090a0302071208030a02070201020106090609020405040b040c05030606030c1213030206100b0301050103020c030f0d020403 99
    0x406490204401d24250b03000070800c90150303401150990b610307404200c0c42d9a082d8000004050000c003100d07502e060000c3c010b006000000c514038401c6c010240001480d50002c02216001a801805400c0d40b0004075507841c000e110103040c0400d036108041002000120b928880c0c000f0b80b0061041513100c0c035040c4001015200c009104942900d0450410401c0440001d0400d1401414406221200c685e00002c01d180900c404840303c015130a000500842d02c0001c03407003010160081d400d03214065210000f90a80318201c02000300015400c10002e040c004041d4041c002d0144144000301705259128103100a50301540c002d080f8050b40003a08110314a014841c001000000b9038081c414140c030000c1c058514000100300c030b4014400040011100b170b81c4c3d031007150541808140d6074407107800c10003103403c2115041d180441c098420703800881c0403034044100c00b00840340032499992441e0f08110046010303401c840c1850809200c10701104d5040e50602c4040d00c11450f08400060300c3e00d15504050030040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 2227031 1250 2225781 2225791
    0x110a0b0c010e0106080712050102070606031103070b0309030901110a060e07060e01020a0b0106050901050408070602010f050601020a050a11030102070510050601030b0111060106031518090209010f052404080609070e 94
    0x1c1c0c509242084440070101d54081200e130100d0302c40c040d88032641010b5000e403103a52f1005010a20b001408001c0000b82da1940d01803220a80465102ca0744030004c21245200a541c0d03141c40e41d00074007029500e58841c0c0c644249400c0064159501d121065a0302402c2e10f001d510f02c003d0581108000341b1a96501043d09a9450b41c2403001346140d08072900d4903600c1031410700956003048000224080d8030390040040b5801000704c0c4080741c080c40e0f17032a0300c0207000780700302c05107040168103202c0441c20f15840080c07514401500900507222000c09176581c4a1f803441c4500d08a038055409124010114400744420b038121901820081100c0c640781e00010308449620440e241480800740c19005645d0000a015040d82c25608000440103060a0b0600201c0e116034400090003034004601d20740180c20760048507070544251ba0841c01640c0740d003032900d03e9141c1400380319040741520034480340200240302c40009a80103150b14524240d1074000980c2410801c885d074482952007020100032034801c10034115805 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 2228281 1250 2227031 2227033
    0x40203010b1c0b06040603080403050307020102060604020c0d08180a0c030c09060305060f0606070804060203180402030105060901030203041406090303010f09050105060405010e01030b03030307030e06010e04050303040f110a0b0c010e 102
    0x49111075004070b91004000b10080d1990070030100250325910b4079840038016503007011402e612246d403807034003580d81c0c0d015141c124018011140410b50300d06041c000e0b44c01c0e42d1009000b5140c0284016011601c11600402c103200768440366403441d0640c5d10621801080d680a803885464050460230000d410721440e621208003546400c100300041100815029042074103515030b9005038075030341c6c0020030360b00600a014011400000b000105d04c0e40000c028a5024001124110001510307000c000490000b440b5441d00140704001003803003503200c0e82c02140e20522890844038003a4420b0641403130310500300e40001040e480040180210703054522a1401411614010f000540c1020003250701030140744502818801184903580b41c5a01035007151481d040041c080b00c0c0c4925101c0f100402034140c0c0320703049050f80038800000c900c102020252a1040d90484015031a40d200c594a4000187c01f1200c01c0d9583d040300c15580c20559190402c82d030083c0411404252185040c044041c212003c5c6000d0740d0007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 2229531 1250 2228281 2228299
    0x3060b0307020a030c031806080105040b0f0303040b0708042301110601030302070314010219020105060a06020f0d1b080703030903030509010c0c020121090c030501050105010c11060304030507051005040203010b 92
    0x94a0740003c038606035580c103251050583d401403800395240034000c0021030010b031b2084004074200f64440c2c02e0f02d040351001c0350184161b030649800d00940d40c02881030b0f07507099001000b00b40304000f18a00200700c4a4440d0301c00c0e91400b9a180000741c1d0b17501d03204039246c0200c2c241140c101c0d40c569025400c00a0091040d000d0315280d459540d000e56a1155484020301803030088a00401d004804c0d41624a110329100412154540c001d50007030080c01c1c2191090b105903015100801d01600c00160040c0e500c0c004801070800a01052041d40c0102d10036040003041c2d000490a000040c080030040d10380e40d842501c010400c4220340c640581076540040c5600ca00340c0c98001c02510302da174442801c41d502da4084c2400800c0da1500d104409054080300d11184900d03051521200c00c000c1c401e11818204c82c05400200102e0b40c844004590312550b21801508010f07808064001500c2c04400031a00a0701c6410801c1c540282a59800d0822141d04442c5200780e61f907004100940c1800c0c00f80620391502200c80e0b401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 2230781 1250 2229531 2229541
    0x310050909030910030b0409050a0203120403030806040509010905070609030b011d06040b0418050c1509010203040306020a02070504050f0a050a0204080d0c02030a050a050708010605011b060203040507031b050103060b03 96
    0x1a0300c0c05240105403154140130010700e603817800f07a40808440007001d00144164201414650380d41c0c07400b0b40c803c0f07003e8810084600d00c00c400d00c1c01a142034a5150307541c20102e8840ca0b007003001034440a0300c2e803010b9550b60300309080022410458400100119103840ca40c203482e500741580c1050050780040010891450b1401c023860203201c01560012003210000750010034030001c00d00800840129596882c0304887c800e040c010f002450a05003070701202d011034010b000c140303504124000c103140302d80503038030500003400000c2d050f030082c080061072441251801a550000a42514030a4a82c480103042c2d01c8107001e0200c00d180540359005281240640c54107140c40c003042e42da5020f4601e050100101140303800115030381802000421034100c0d0803103058400e0740c10000d03100c06007407040c500701f91b103400000291540910600004007100703281300c0c42d44000e9a203601000e50f00003041181c4c0b40c014240040000380a41c02108240100051491415030a01c000501160030070f030080c2c0d401110030b0040207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 2232031 1250 2230781 2230783
    0xd120603080703261009050a02040302030601050909030f030703020a030e0d0203040504021b07090506010807080103050309040507030b0901060207051905130b0a0b07030509040c08100e062101020310050909 90
    0x1c0d6141e0381807800040d072110190040c204007005400c518030881080c1c4c1030207001d07404808540192031240104114946505844000f02d01c19440000d4040d08503900403c1a032070270001c0c032507002050a003543e00e0a196020400f120780c0c81107a030880032a0780844d040a401e640741c072650450309118801005401040b010103540c2c0d008920581784659000258074200312500040b64a43d5920802250640d54070b481c1690080d1104880841c0010101c81c00115628440d01040d81240e8112010f580ba00c09003005210141c0b600038140001d040d00c0f01c107199540d4880c83d002c64000c0c1801d0f030182002a080800f0050f44906551040319000d0301214140800c0e41c880c61103540c030035070040c0b0010302081054042605c5d0001c0380d20002d0340c100086a00720034160414020030300e001c0c0848041181d0706000f40280c8190300280c0380392807000604001840180c07507102c2c0b910f80040b0f0081c000c0301006100d15090142c6c9201c040c0301e4040da500071050241e90700c40700310100060f1100b00c4450140340b030140c080c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 2233281 1250 2232031 2232037
    0x312030e120a020a05030301081b030312010b0904060806100905010b09010905060703030608060103060501180c020a140f07090e060108030c0d05030a0b0d0807031205070e040902030709020c0d12060308 88
    0x2001c002007050059000b08130080300a540700741541e80300c0d079540d2040c0b42c8401036248500d0490540d86000c510398940030040b24400701d2415401d910590a01d0050400f80d0000c00c0e103035400c56550000890f2502c0c040008501c1034150b00a0b2040590420000c035007614030680c403c9d01d00c54000d104005079a0b810419280941d4011b44041c2d480790341d035040032400341c04590b001c2d61160080342d0011040c480d054000700d05031180d04840550585000d401601182c401c0d003881c900503081001c1500c0082c009000d8143c61214510884030402c1c2c01c010850304083c4154800c00105135203000600703007100107200c01030051000b080558101140e5103000b68481ca100030803c0104100080001c00054456100703600042c4081d007070640900842c0703040e208650080b0015400b007190002c0c0000045890700416115181c281e403950f0000034400d00b0301c130180940070001c0303914ac041e104000c20242d40500c080d05607144c0d10001448550944180640f49a014298040100e401c088060002c10041c2e011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 2234531 1250 2233281 2233303
    0x4080703020d050109060c0503072601050607110405090309010e09010503070501050d0612080405030c040506010509040b0105040819030f020304080303011a0d0c03020c010c0302030103050601050405060d0807030305010312030e 99
    0x410355002d80e06107010750042101c08401001507151040f000795042d40710020b14400c95141d11026034541c4c841c02841403400152145441d00f0314020014041b5007080c1e0701800d480c9215031000700030100f691002405031801240e8642107a4000b02d180d11196920491101c0200000c0e030385000b25504060101c0c0e04e8020718003400e41403000000d56114441a20344c42500101511510386001206a14000c400784c2d00074420b0b18841e1040d5601100203250070f100c0c0a0003124161126890200c030101400090603104d01b50038188803062000242002e424000c6488195042d01c1c8a18000c1c480c2ca4051300708020011440b04540c030501040c01b032417500000700d2741074640c3c20400800f034401c01c2c102d1500030300c10b003060101118240382c1400ca40e81d03015000360810030a501c0c02031000075108441107041740001d1201519542c0704034010800ca00301680510b40040003c1c21503003020360944c540f16481c1c1d0220000324002917441004105222449004160951040ca410300440003608880d07951002c03070602d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 2235781 1250 2234531 2234539
    0x901030303090311010c0c030305070302030709060f0203040e01090b10050c0a030c06060302060a02060703060501030b130b010512040809010206130506060f01020c1207080c0604180b0105040306020315040c0201020408070302 98
    0x8010010f15000321048800c0000758802400001944a4000d001c0c1c5c041c0c0c0021400b00c5d0811004c41c10035030007030003507901c1a44c0d15994101d00f0b86c54508126250480e1003540000c0d40010080418200c5c0034080b4580605040380c4042100000d042c103100c400754088143c07030b007017207401d100c1070000f2480850540b02c201c4c1c00d407401980c3e4140c282031038001080554002540300c44001982015540c021031300e2446180305031000c1203217a0b516001134042d2142401929800030400040401650150b0b004081c030401c10702d822810a0984010540034a0090303406858442022803001e2584da130420255501008c1c0e002c140d80d4000981c1d50704c0d60381c2d00000d8003230b078450048801e0f8030109900c02c0004034180940141480411f400c21078a00d030300e80c400b43c01006a00d0040325411111410004100c60450320082226a0026600c40080300100341160015040000401001000c900e090018501540400d0480c942007101641040200c40307100d0700d04001d590040c0420011000040b07150000c0300d405039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 2237031 1250 2235781 2235791
    0x50303120a150506030f040b07030b031504080d05010b070b0106020d05030c0c0a051b0103060503030a140a0c0203070902180906060a050901020f070306050708010b0301140103020c010b0301110a0905040203060901030303 96
    0x102c40000b4140c66048180c2003030000c000c011a200d540f07804540640d000300b600b000991a0b00e101107042d02c050550300f40e0158007607100384541400d462001a440b5019003203150411300340400d001c4c29100300381d000070541c10b00801ca2400b401076440c1401e0042201e80000e02802c466403001500500000b06030549400c40414212845001030158144480d03000c13050741c036060740101060001c0c050242c8003e000916010001c901410000110f07407038030f04039448018007220190582603140e0720040b808000c2000603189400146c5081050601600141c580540c803125880c03032210720304880e603814a204905501c1800700f2a102c14040301e0f58090310f8035050360750780503e40050345403140201001e0151302c01e645000040c44034941c80540103006a5440c000241d90b200c0b4150500d00082c065402d2150079128414030960007030b4000c1c50300903864400810128002000a0308449403510040c0210302c000032000c0415501408503405800111403c5003141000c0c40412a80c21050000a040c90390314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 2238281 1250 2237031 2237051
    0x2040b0105090a030803010f080111070209060d050a05011b03050403090513180c0305010c0215060915061207020105070302040602060606030709080601030606150504080d180f0902040807050303120a 87
    0x541d04031100120003070070180246690f0310303200c203143c0e109220f80900c10101c5c06010440003c180656a02500c00010700b03800c128281e004c20030b94142c081d0a013a4070020074031414000900610401141c4c60084c030001035101e4a05c60102c0c1c108403400107010403d8130780070800c000203030090260800e803482076038848039040303009055100074582d2290aa26005c04000c0072010800006103078002d592040009014134084003200740d03600e441c1c00d1540402201c0020009a8a080800b00300343d104030494074160b600008131010445552100c00502c007000300c40c0b010000e40075024011035030880f8952400314501494900025100e2802a0405118400c0000403581c15441010301401601d94042920310550303491a11400400541c031824401d80e85031007805d001e9030702400940d0210f0741024040c04000080c01c100311040110744a0002c5005001000440c00d8092017045801800c03828000582c1c6500301020507140c509a944894400c0e48104030003441c400c1160900d0390408001800400c030503084e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 2239531 1250 2238281 2238287
    0x807080a02091e03120f0706020c01020405041803080105010206160503090a140304090b010302040e010303050336060105040204060203040e07020f06040308060f0901060e011202071a01030b070801060c02040b01 92
    0x1a40b240700d07512002580440450f00c41294003016052400c0381207407800c2500c1114124240100301c00085c42690a020500101c2c0040d001022040f9200d00010b09c1c1c81d468200113000c4401c010030300101c8840501d2a0b00030907070070200c07003400341c0b4007400241850318051070b1000501190100480c100200440840d40000701000745801c040d034030000300c5417440300015949640fa0005c1c4691149903041003e20705065000744204c40c1610003650641c0050b0f030075510b0035a8980c2c80903004040c2d42504a180c0741850030019100c0e0100d81d00c030b9551140d091070781d00f04149840010382010f40f140344108020803946070000225004c4810500545201e07a81b80311082e4202441c5000c00c1302c4601a0758200001c0583c4203200c20300c10081100e106c960600e0040500010300e02c00d00034280420401e0b1111a11036001e2104030242003803150002d4540304186e80c440146070201001413481c018034000604c1004035003204264011123a01e007204c030075850403400500361540c40102034000c580d0ac81d14aa001c1e48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 2240781 1250 2239531 2239537
    0x90109050a06030203040b010f03020105070210020a0b09010c090501030b09150604090509010209040c1b060203100b0c0105060306070f020a03050d0204081603121407110301020c060103080a080105100807080a02 92
    0x44000c02019407581d5550003e4040d50049400303c914001010010416640642082c010b40741c06a44035824810b41c0e900748242c0103000303034522007076105401c940d000080c5081c0b98280704500e62800841c0051398404058140381c13664000038149414030446006030707250281810360007c07020024a11403000c1d00c4c00b0412a02c9148c006854150415080022403003054000703140452050f9020815030200c4041200d2180400f090880380301d01120f0745601144003034004c1c580105580b04101c203c0c956804052446130301018040c40f143e515882040000d14041c022581d10020300c1c1015040040800702c000d440d0800140b0080500038045445500480c083e410b0390050403a4100b00c410b0140c141c403043e0419a007910084480c0b202d111b91408400d845603d0100c2100f00c4128084e0a1010b140d803146041048240c8458042d0740c00e124007001c240301000710300d00a5000c1c1144d980c0e42c8104c001f0007001004145c021074002d000540c18034880580c000007866001a80d440d10000a440345456580a44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 2242031 1250 2240781 2240789
    0x60e01080a090f08130f050a030201080a0f150608010e0c030606030c1e04080c0307060201060f120602090603010e0103140105010b030a02130503010507020c09011703030601050c0111070605190e0303060105090109 93
    0x40003150a9002c0045c00350805c05075080582107040440c0e0310313010400702d48198040203000407a80c00100d21000a40c0c1c204441c08485020041010320f24130301a404048140c0e0301c0400082c1882c0010420507080c442155084000344c0d088a05e035280160104e1441c0c07101a180200c2c414000a10120803c003803540584a101a890b8280d0b6942da1383c40342554138051407803050701c039016600c800100140148203420031260740c0c0010790802e40c0f0341000d07041d620f02800c1003503980c142c0801104185540305401103000c3c00445c868034000354110f01349551000c0d20030b0780e544400c0e80f621005220b03010201d02941d501160a24001d40e940031280d80d10307011606658080c5800d9803c0c2011300c4242d9030085406929404241c96400301a030360b0b802032000203035070380c02c0080594104001040c42944036000401040101c0c4001180000e003103051524294011101611803e9498040c000c0445d07503010340e100099024001232002e90020b0036083d407203200242027181404000182c0d0000d5901502d4034100070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 2243281 1250 2242031 2242043
    0xc0d08040b030a02030f0601020a030813080904020a020d1107030803010509130203010c02010e010b030102070c0302010f05040806330a0501180e041a0105030a030903030807170702010b0109060e01080a090f 90
    0x1c1c3c148032250402030f400981d510f80b81c0b807044000041d119480003450320040b64143e9985032141e00e400d0b503003007440526050241c0d0300d03140c00c2244000e2a102d50005080c61802036000346680010f12100030000001e0b80f400d24001d4004600800100705081b040d070f4151181100d0813949030725800e041d03c0e1030b0407176440001d41550814030040c102e01c1c3c06500c1a090314154000901001c0d1f0906c040508034410b01800404d0000340c41810701c00b65204d0403503086002050309289280c6600c903285d01c0c1c5050021142d4012403652104061f107011094641c00d04003d8002c00c9030814201c8000c0024603091842c001c840c10008825051403801c80040b000c07100908030049552258101400d003a6070591400744010140042040009200d080014008504070f0305030340e42c21010340c1590b03401c070340d10900545200d0402810700c90340242d010440c41500e0041c920368000180c03034181c400014044180540c00715090101003000c6405a9030000251a071100441f403000820907041c2c0b50140c80c11a001e0006006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 2244531 1250 2243281 2243287
    0x702030a0c03020a090b060d0c0302070b16020705010c0308060d030203090414340e1801080312090601050303040603090501090c030c031401020a051207030e03030705070b01050a03050c0d08040b 85
    0x81c03015040c81e01098a0003901e00c1c4040b66101c94007042502d114100107a0408410805004940744030b60141c0385070707a10740c0380151070045030f905c500406003015100740840200b00304007010340c1d41d010011140140fa081c20300c007038909295200909141c000516560051085000e40030406100703000f11740201d0b200800410a1400c10740c85001105000c54a403040d5954500103810217a0781440d02441d4148962074508070546121000c440401c14100d821360403200203a41c44511000d2a00c680b8060140400119200d001040b05110015130141c5440b580d604108010f1190b0740b4003004803820b41700e0909001c12034141300c1ca09980140542940a40381945810001c8100106554003404580c02a40d4401c010410041242d01701d21400d161301d800704104020004860b001d482d80140c3c8035890b4100080c0b110300e2500c500d8212b0b0b00484080740043c1c070001d0b6010801c60716400741130162400740d54400880d030039a9102c6a54050424a042c45140780300580d50070812068200c0f4081d08040b010035813 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 2245781 1250 2244531 2244533
    0x12010606020c0a08011103010b07030302040b0703080603011406030c010e0112060b0306030706030606020a030c11030604030203030a1d03070609140a080403060608010902090a050c04050405090601060206010b0301030b04060b01050702030a 104
    0x24441018840c82c40c4038100b10000001c03080014010340c410f00720714080961030341e4070705080010194070403403086082c103409001c00140901c662024002c0d80d4000c7c1c45001c610700e030001c2050f0031501c000700301c584e50340028014807456490004802c1c543d01003c2c05c00b007198482220058a0b00e070a0713003aa165400741050800f00d451b04864000c0e6000b65020f82c11178056640f41c0409030150744070340c016400180d02240c510030100f03104d80100c1d000c5600480c040c05251482501080c240f840849054026034000014091650000d02c80d480f4911180801d0004d0420090103041d100d104285000e0b0195403681c112505000f2803e0166890300c01c400d0032601e1481127480e040d0016045888180c9119180c1300000a00030418081c0741d08160b801444800159140d000042c02800050044001c00109001c0403c55403101e00c15180a014410000c2a00e03607d0800020b2030544140c000c080e001905100420014107200e1500b50801d52000c8049561000c441c0100d072507009100010b5030610600c00c1c2c0c04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 2247031 1250 2245781 2245783
    0x903010908070c050a0b0301080d0c1103060a14010b091e010215040c09050c030705030604090602190306030506060109080d0804020f0a030609050c010201060605040b0c01060b0c0709050a150905061201060602 91
    0x411250117131080e030107240e45c414100210f4042441600c003950015010400b65a00c501050304c3c000340710f984804101c51001c40401c0c40c18204907000040c1c0c030364032074a51070110b90300d806803401800c28020b02450071000c04003064038583e44c0b1f09540f0130354203540b0104110f41c0c020300902c40250241074041640d032400e0b0500307100c074035918440c1c1d50210385000d01080391140c3d80e900f120300c0303503c0301d0300d40f285182c4454040c003004180a80003074035041d900307100340303039101c6044502510502e0300d543d0003249403070841c2030450034050040d00190501c40032070400c01003014003143d442e22410f00c03402d0450003a9500e002160505161401300d66026405c80c0d004010411268803401e40540902e045a002101c5200164201c60071402080c011038810302040003040f00900c0108115550800007282241d0343c0c0171002c1301b6030040c00704502c3d00d4100c4a818401c0141503c103a503806001c1080c02c2c13044484210051480c54414090840d0040e1240001801c0e51a007071140d00e01c0e604004020054241e8500c402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 2248281 1250 2247031 2247053
    0xc08010e060a0b01020102071208040c0305030f09010e0901030b070c0606030203060106030c020114010303021c020309060309071811040509090109020d0302010605030c060405030d030216080a0e010912050a0602090301090807 98
    0xd4101c180f512903c80103035441442900d44859004101e4046814905026207075050010000c4962062014000c40095420310150441e1a00380d010203440300500c4001500c0140200021800f13100c0040042000c90341e0444901e40080c0c00e414140100c3c00305050420141100340c001940511400000007005540b50b4000fa21503001a4020000d0211508405d541c0880078400540140c2c03007402d002503c0300c14510035010140c807038011a803409800303c02040d001e4004076450341c0b039074100c039204004950304038124007819412503104104400400542a240340164001c0b1800764a0700130010b0145d0b4025881044010380007000c030149503400c0d290082c003030b1241c2d00a8a019008640701c3c40003078201201030301c0c00d0742d80040240a002d020644100d0094120719400e11480c01c01090707540104001d1802810091646d54641002c03070010030000d0802502507110f908072144410020000c12808522040b1440c0e0214000d40e41d241210300180c05801840b8026104120001e2088100b12140e18a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 2249531 1250 2248281 2248291
    0xc0306060b0a1b031205060301060306091a0108060f040602070305040302040f0e0c0a0302031b040b090a020409110304020105190306050a080a02030105010801050601021504080f03010902090a090204050315040c08010e06 96
    0x34007065903110704502003e2150b0440c005012504201c00980c403013007141c000a030312500207800000d4003a503c0d2141006d441356805e050760f04400e01c2c2c0c000e0010b48002000e90780580307001c20003016182440303202031a54650040c00541800c1d4080703064000c0511503011a00210b400170400d100700c00052640100401c1942c0010f5483d10402c1d0802ca42401c004c0c0403081142d0f0000c0241130200301d45102000304810620710540d003c0d580365101c5203aaa140038059020f1108440300584880c04d0055040442e5945180440003000501c10400140c0e4082d01b180e44c1e10000e808032555a1206e04c4064025181c0c60700640d40c0b004a0102c085007030342c00015420800f078000c6000b03000507640c07079001720b00300c0c2e0b020b4034900c0c0141c0011011b0801e43c0d000ca0145a00700e0b1148005a240200400c10603086030020303048170118680004200b0043d18140c01e5042c050710300404118a001d14200c00a540c42094a14504841e807040d0001000d002e04030a2800051a0300c0d0000d00003021190380c0641c0300e0740102c40e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 2250781 1250 2249531 2249537
    0x8070923030705030118020f0402090402070b0a0b190312030b0405010801021305062503050c150702160e01170106080d020106030203060a0203160311070f050706020c0d1e0c0306060b0a 81
    0x80501c2c050040d1b03c1c0b0300d40001c0400040440c0f079001d02a640540c100c9031a0001e07005c0011102d01d8840d48001c121090080c20701000b01d0400204001c04e5515a503012440b56a40b070304030b0708103c1d081c481b12404590740920840d0314120407003000c0d0045c000d81d10580380e01c40c2c51b14000061015064004040301c0c407041482488154540003000b1140c02a400b007115509004520ba0109a030911350400006020f81001c90600c1c080c9400c0504d030802d903004e400e8261820b036050007081380d010440081b03004805c080c1c552106042c080a00b403200c10522540c1a40d1000c1c00003415200c5082d44200090a00b0784142d5010030b00c0141c0180c00713041a840101d00030b2103003800003450031b841d0f44243c034010010b59103001e05080102804902401300503082c041018010001500010410054644954844d1010703284041c50424040d08040d070030701c2401d02503030100d140039002568100c9850030400d0100c002080c01411404d201000c0d1a15801c000c082d41d16050000c11072034218405052085082d036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 2252031 1250 2250781 2250793
    0x906120d2303010806010b0708070501020307090504060506120f06010c0803040c03031106090703030f030209090a0c0206070c020a0306110919080105010f0305030904050402130204090f0b01170103030807092303 92
    0x1406403101d480309100b0104690445801445456440401040b1150180e00356a007090500d48646089a0050b143c00c404910703000010491820180650300003860111201410307c1c1c15008041d00d4590000d104a500c0440c4c080002c020381c0c0100030200450340c11807251a103a00c0c1918054418035000c0c00141e002c00c0245c0c102a90044000030110303c40c80352007000d0460245182d4042c5c61807003440307049406260702804401103030380360304000500c80d65103154040340c4041c3e50341d40039081c59006080e071010007640100b2100036864858460040303981c000000030f44800000c0036400c89008400d0007a07800a4425003a61040300c1001d000b0080d589000000c01c03050b6a1000500e0301d40205200040041d04103021160940c40c003544002c3d845400a428294904046d0305500102da0185e00641c40480e5156050341c852100c500c91106045000c3c02c20b901c001128003443c95156505100084c2000016400102140c1c82410b44000030290b84e5000248c52002c82d05560101c84c0c0781c496103000e0701c112 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 2253281 1250 2252031 2252087
    0x9060b03010b0102030d0905030405040c05070605060604060507140f01020304030503070f17150d0507090905010f02040503060c0a05090a030c06080a110405010e031501120b0901050103020a050906120d 88
    0x18401c40b942403405030010345c5444080d40082c00500903440080c0d84c00d00040c800050b1548843c006c24180829503954244d54140364034004044420141202d4000c210600040c0401d81c1c10900b180c168a03004440d8407a4410188416841c014110020014650000c0300740400c254101c005103001d1b030745503120b240060011040c100e50034220b4242211041c0114401b042c80a110175260076010300003d4941c007002e00440c2c8400b0300d411402d074020318960755180c1055044c44002e21071080c01701141d603c00d5241c103203001c0c00640d485001071b125a40384500014291400c83c000c100703d130035803203010700b10600d040d0356410455000c5001e88038240114000400044410384c46104030021941441c0d9440d003400d00305001120000010b000c10740c0c05202c0c401c42d01410012000c282030092600b481e048212000501e84192102c4001d0266211607041a00500050381c6141110707090b90303010741c0c4103195a6514000501d03020b0603a520b16200b07010301c051020b14603078022015903134290700c00105440ca01c1c0d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 2254531 1250 2253281 2253283
    0x80a03060513050702030304080a0314010326090607080a020a06050c09010e0405060102070611120c0106090b0a060804030503040303090f0507050906030a0c0302060a0915030204090b0103020301030b060f060409090609060b03 98
    0x480c4c1c0d04005800400009000880910141281046c00d140016074168000f0b4000f410b000c1c01e07001940c510a00c280c40c01024030505812042c41032000d40c0003401c01ca174410100da0103004404004103407103000f00b000108180f003001205c005680004c0148081c6c10210401040c40d8081d041050002e02c0c99104d074001400d060141314051441030b07008005440c07801c1c404660244071349800c4905030103075484010752801e0500107004907024101c0001071183ca007040d00012101200081d900501140e1300130803804da08044650340c0503815091280d035030340e16441d0841c0100072198001703117640700c1d298210050150005503038090355000c1d68000e889031a07a4041543e114040b00e03004160000c5a071082c40181042400f602c940c400c40c0c24500800d070344554480c644084880500030000740d0100382044a2030300da000d01c00580000b0f003011481c6506585070b21003103200c001c06036801190b400721480c5258035402c0c1181c004040c0000700b001005114605440038007080c00050341c0d4541400030b103440c41c1c64 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 2255781 1250 2254531 2254541
    0xf02060c0708030402090403120207030909060e04020108011503060f0605090406060318060902040b0303030108150f01060806040902030a140106031104050702030a11010902090f010302030105070e1003020f0403080a03060513 98
    0x203003210050b41181d441703600f00195101d000b8400c404014400b06400650041800a000c6041c440d8a40190003410306050b00100e880035030000700b8901d03c0809120250340c01c401840d0549200154202d15580801c8040d0b000d000700784d000401c1440d0440c0300090b250ba00001400c1c1744c034811941405034076950031048003a00e206401b0031412400b0580b80b4030000302c05502a960302ea10240003c1001500500003e045800036032110030b8a1704900b821840645400700e01a038445a00101c49d2a80d5040038401400010010300c1d283c003442d991550340c0c095503420008945030741c4e8441c0c0f4040712045100d080f68060000d84c4402c4030080046c100c98202031516010f054030038a160b80c011403c201caa50000c03100100c5a04021106544c2ca00648002da1502c207070766445860382000e0500154514814035003100d10050080007040301d10a9043c184e40c0e501102e0142c41411445e0140e25011401201c0d410b920940d80024004400040c54040041c0c040e0000030444508444500c8049070000d802c0041d01c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 2257031 1250 2255781 2255783
    0x30e090115030e070e04050105070f0302030702060a05130204050405030406021204030203060f060109031b0302010f03090c05010503060102010e0106090b040c050a080103021302040b0c0c03060106020705010801050618060a0f02060c07 102
    0x4031601c5200e191520942c45444003282a2084860b403a0b6242481c5280d248155801e48090751a101000356003078008240d01604243c40c6070462035450915402134884801500410400e910350001c155002d5016034010700b00c4e038004100304036030301b42890030715a694890b1088002500038040034000b5022076005403000c4070b402401410f80c5a0303824602002c0402c0c000d0505040c4202d103180170000c20194072607050070030781c101c0c0340d94049411400050b02d9006050b0741c6004141c01c00b40c42c4070000f1180140d4204a443c01e0800c40d0b140e480717041c0141c0c00f41411046400c2e10f5071078004000f407160025044800042c0060b04e04000c002201c401c2143c26120b03040040c00482e030460010001070038a840810b600400e205d1380182819107450a8010399132141e1070f19111980708490030b10161500f80b2609006000d50b0009100e207524200000e03105c1d0380c2c14401c0606c9000f0201d01c04680740d2000c41d07100042840180003550359074000e14058144800b0316502d03001486001c0c0001d404841d8041114109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 2258281 1250 2257031 2257049
    0x604030605090307050a030203090a05040e15040203120d0603020f0d03020303010b090307090504030c06060801020a0903020f0609040603030801090c02060f011203030906150302040516050f0703090f090207030e0901 94
    0x115095484a4000e00405425403007544002c02c004408507900b071000540c03c500c00e6001c1d540c0c0e01001c0c010401050b1072600494803030761401d4843c40390017400003078030212400000004061942c840c00000e003400079002d0f001080c01d00000307500c2c202e91403070b60001056030b10846070240801c0c1080d0034403050701741002004015038810001403140820000180041860050480d18030303e491b05202170070341e1420f880c200c0c00702c0c02c624008420071429020b182c0c007921440b0021406e01d500c440009011204c0e51101a000c0d031818410310083c1d80350b00040741e0007003030040e00a0201a940f442e00410040c0c09114104400303152045481400e48042603850240290940c00305050b420030320021a0101820f000b03c09142d51020a00300064141c0581d5a42000040e00c84d1812882c40c014001aa00010006105148040e2800844540140949a11203803a44c5625210f800307a14003500c0a640c6078000320740303140308804000b425120640007481114466621269003560400c148690940280035040003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 2259531 1250 2258281 2258287
    0x5070905010c0516060f02060703090c12020414010b0306011209020102060c1606050115030608030f070f050a060203010806040212010c021c02010609020c0a060b06030112020d03050405060a0c0303060501020c06 92
    0x3950710802d14892042d010300107940001d1080c2e43c6a9603514210b0744040302041c0004080034540e034040c07100c1b9500030f01d1070400740020ba0050355184044801e500519003406e006d8941003042d51a107510504002101c194920300f15610303030b8a505002d400c202c0b242030015000c910003c01c03288540c05505011503040c1c0042010391155200343e01c046d0460300c040424001503500c0000840c00902a16009040b40c00720f0701c41001803850f008094071056007000109910400a01042d040f002045610282c0c0000c0d04c424450b04900d03001d070520069400107403240e80040300114810a0109646005610840b010b803204000c58a095013079442403841107000d600029004226a240010300041c0030031144000600c1d80e84a005420883c0c100903240b510340c0d801981d0f40010400540f144184803001101ea01c4e09661404500706486981032030002c0c011a415803140e01010b00440130f0300d01911000701401d4945060001c0207010015440c1c0540000b0705110001420354004203d20007800300c0a81924a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 2260781 1250 2259531 2259539
    0xa120b0402010804020d0203030d05040b010801020c1002030601090302090103050d030b0406030503090904060209040e0307020a06030b0603010303030c1403070305060a0515090609030c090405030705060a05060f040c02100e070e0a050709 103
    0x24580002401a1b0304515001842030040c0d40600c0200f000c00110301c400112424281021014460140c100c00c0007a8070400c5200604e2000081c003091040c1200d502580e0b90340c0e0980100c801d460070b079000035002101c004c0040700300107011130b401c1c0c14520191303000c00200c0900003c00095a1941c40f02911540040042e4096403c12003902d40c3e1090107000054601042100818215940c0782085101c41d08007207034501c00c610f88039403500c00905840c6000e10024000b00d0020b9014070061000405155445481001d0701e4040d180440c0c1040c21482c660303450f46025072004c0c0c040d00088900c0c9100300f4211034081381525092070501c004552540b00c403820300c075510081c0040790340407001407030b89441086080c0340146c1c0d50000b00d40c030542c03081c006183c556240b4504680307440070190940510074148010003100e900c402c00e14502c0740e48119400f09a000c5c02c13000680c02c0ca010300d107502c4952800c140a81c0500500000c070300045590030180c42c83c41d6074908000d6800c45a060b1543c0c1d0001e144020200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 2262031 1250 2260781 2260787
    0x40209070c1e03080a020c060601050a02010609110a020c120709020702040207020604090b030f0105071407080c16060e01140403080a020f06070306030b0906090715031503050601050a120b040201 85
    0x2640300c601400d0145900718561680303000000c5200a842440e000325642c1010141e200a0b000e1300702203107000035030800030b07154000754881c1c030300802040c100f041c042140c2c40200d200b5007041008240380d4108201d4458030501401d01940849101005880349804551a90903c000c009103c4446600940365041c20003034035001a50240310183c1c0d20540030f11194016a4a4800800c014100504005104081503043c18140380c0d00f000b000c07243c0d034900030821140e035410281955051004d41200e030b81e2903103286070041d180c1c004c2c0800710720b89100380300d40d2440311080e012802080d5207490712900c0b107034407000004607102084d140e82c008070000240010030018000b06c0160003828041d005403100748180c0444240340000803030382071000945885081042c86241d030034203a001107071403014041e9445c1009445649003203500c034203108180c90140200180b4801e5005805a030a10341c0f500c0c01440d80d070700300541c0e500401e0040c00d00c12003c0d845e0000b6050036800001c1803459001e9210425a51160019 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 2263281 1250 2262031 2262049
    0x60f0606120106110c03030408060f010e010b0906030601031b0e010201060b180609010302070503031504110711120106050d0c030b06040b1003020304030c0206030c03040c0816120203070915080f12030402 89
    0x40407081c07041c10300382d0485035018000750000d00f0702740000302603a10b05041c0c04010041d041e030083d00c10803680d10061045642081c2140c0060100382c4030b850741c0b40c0f05e0000480c0100702003c0c20801080404280c110341c941c0c0008480c181c03d40c240e00910495403510b600c3c212500c11a040701c0b403011511101600c80d030606101500418030141401800c180c05030b200c0038295401110428000d01841e10b414811340f41a00c10780442c0900c081416080000070350b1a0451640301020440c4642408405001c0c211802d4001c40c001d001701034115002100a80303030002d2205202e00044401220b0303080055528140340c480c000f12007070000c03d1000d0980544030309400961026005400f00701c200210100582c5551000b58060b807030081016540f072810341020318641103941c010b000310343c0003412004c25210207060004113990112764125202022480002d10b4901d40740c1c00301c130f82c140c10100c8403240c01c4a0310364454200d076040700c2990091000501c2c0640c0700c0800c1d00c0801c1403054140702240240c10300d4844 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 2264531 1250 2263281 2263307
    0xa02010804020d06020f070507121101030203060406050307060e040e010504030804021207050406060f1d0609040209040b0907020106060807050702030601090b040216050304140901030b0601050c0a080301030302060f0606120106 99
    0x4807808076000e840342c0d000c0e0f80c05010b80421b015400a012020804100319440040c01200d000c07480008940d0b94210314100724540c0d0718101600803000c40ca469032254042d03070042100030100c420195071400d000c0c24010780320b6110340c400e034501060b2a01501e0103001e0345200380d0f4903596a6070b280e5139941c00c110008801a4075120750740704d203840c0841d4640701c61043d000a000140c61b440000403020500401000d9541c40a208a40c0d04060012142e00c0308401c3d80c159140455016807600803d02c04200244441916180c0c40404130b000d0000305901940440141c42c02030362809008d60f50200141e500d0300c40c0e4000290550f10140041000703050353740c40f0000c01d41005001524104075150b4810801070505010745841d040001c00704004254422005050b1005403024940c562454503460707031664001381901d0500400052010f4180028000303c22003d6004d50491380307a507100e0070020b6440f04110361081402c918880421550310741401a109085580b19600c04c56a007880c0d402c85240c502c0c440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 2265781 1250 2264531 2264539
    0x16020709050106050316030c020604060b01030f0f0209030c01020a0506040b070314041208010f0819050703150b0f0f0915011103070311010b04020903030a0305040206090604080d08070203030105030a0201080402 92
    0x8804103000a040c09401d000b03140c56a103450300c03810004504490306211040c100e090506e407003450050990007180300c0351b002e40c100c0c03000240d204511006a01900291440917000761600109503040100c0303a029110307040066003100c03c0f609803640160703560140318034060a05d90080c40010b0001e842910000c0e4005070701c2c40d0204410910450b40304c403103542901c0c102d4400c02003910300d5406903803003a5503d0041480142d88864103140540d4281c90b2404000c0400c08205000ba2001c03c2c040e0801840d0011648600c0110f8000006012440100550b9010503c0340c046c503140c0441714a010000b500b4a084000c15441c1c00c2e172541c030024a01c803404180d0301418040e4144048040300018005405058001d861701400100368260450840308100c441070710640c411700c0f1a0140d030b180082a20602142d40c01c0004158a1b2400040d405010756261554005400035011801031408100721144114a480307140c52622864001ea0300c0b40024000c5a80542c03203450007070059841601c9494020340007034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 2267031 1250 2265781 2265793
    0xc0b09010209090901050406140705070b0c040e0702030408070b03010609140102010609050a0b09060603010308030103080a0c1e03030c080103080a050703110307030c020a0602030406020c010503090c0d05010f060902040e1602 98
    0xb00815030000040f150010a030b590b8000b00814022540950440341a80c06050399941c03038040303405081c2e4000e4250282030711031524000740174500c168007114007a111b2106410868a040c050003942c0b03a0140c007610f409402800c2000981c6d50954040da8184c83d0561a0300048504240032684031540c11080c4074119900c440340025100700034800e00c3d020340b0701048007003800703811070091180800d0301030030180c00303000e04000400214840409032070540e80d10490ba607540702203192048412a41684014203090803102d403040b00c41c1904010083c000d4802d131001d100807101d1000946035a0403d101c0034003403032420080c0c10240c80c8a03400421410b882420044a9504243d500c1c6107160130440e41200800c2c5a082400f0942c50b2280c0440c0050a051000f54036007420311400a40320101030300b0907810f0041c0800841c0c10880700b03104608038500040e0598240c0e105030b080150203800680e04084505280c010040b890013850b00854003581e20030300b14280c031501c83c145482100c1d5500e0050500f180109 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 2268281 1250 2267031 2267047
    0x10e040501030305090301060501021902040e0a05030c060f090102031306020310031502070303050912040302090c07050a05060a0e01060305060606072102030408012702010809030d02040803040f0503010501060c0b090102 96
    0x91141a001e54000c1d44c40c030752034591600605084650f59001581598444c1c08668580494625a40760150f4140c4001c100c0c0e40d000e2301c00c2407502809420042a902000c10882a20b4100140003441844c50f40390500d030716110b80a240c0e00300d01c402c1d210b04454a80450912002c950103030011030f004140b40d408400869543e071112a030305040d02901d011601e4000a0321030034140c1c58083c0315000310700f030360240c40310103030341560b142040c49580720007405000c002c000142802403d03025504901d402400f1349890001515000e9202c403002c440c0d15001e1458022080400c2805101d0b60054035400070040096841d0301080080c2a000304404491f050b400d01109901011017a01c100100c0e070301030300110740ba14105040d503425a00e0b82c10154941200764071260404c5034100e20b210000640a00304100143c41e540c140c64154420032480a00007400018005121840040144110381c040482034a6441d2541d04040c00d0310000e102e60030002d8041c08105012840c4140003d4000c90560001860320003e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 2269531 1250 2268281 2268289
    0x6040620040b04090b0103020301050a1806030204020a0c03021209011205060d020d030504090605040209060306010e03010b1009030506010512071e0e070306050108130201050a050f070b0f01030311030406140702010e 94
    0x2e400460b011040864108804034890190841e03442c2c09007010340c15036061a000c2100c0349071030721492600c4c2c100c46148400c1d11000c5e500000142d60007820075581d4860380c2101070650004401c00f1001445565051282403c03250140c3d00e22090580d910003080e040b001d81c0c500900300c06020190b11160b140012070041c3d031420010442c41c0e2098032a5500e45240a00f00c50849a15905c000c0c0030b0707401000040b400d5a1500c0860380d004400342030100c040941080481d0040c0270801c04150410401d801d4000c1090f0020280c0c4101ca12a40c101e076405d0ba00c0c1c10030301c00130780b40b22000a521540001c0007405195200348582420041101d004101e2a5480700042c003c0e40d0305941441c0425610b0b2014010341d40d0182d20030380c2c04400820b028aa10805900003002c038499140108100840410ba0300100c548000446a005800c0316084459052091032100401400e100c00c4002c030b44040040840c086002c010340c0c044440a8441040030b8400b80e29905150f403119404904100b4100e68410341035803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 2270781 1250 2269531 2269537
    0x11060702010615020a0201020304030209070e041401090c0c0c0501030905030705150106030501060e010206010513090203010603060203070201141e040609060f0b0301060501050702030705060f04030c030b06130b0306040620 97
    0x4140d0020610510303200c02d83e02c80500da0281d900441d000350101c0800f50360008203c45c1100d0381564a41880c1d540c001045880c1c450044040e40c1c451f041142c03080345ca0681e04c1002e416603207040c200b00442c401d0988155004071003040002e107440402d042c00c000c00e6000b0f80c40701500502030826645083e207160307596030502c17920811040041000c000144001640351003481e01401d601e003800d012000441001030b580300030500c43c9a200e840c100c240c5030300c00c00b0140c000505041d805002402075a480e4500b280294108440e0040150701c1e02410b40c618170b45049a25010340e420300c1e43c20820580d2030400168010b401082668500c0d11110240c1c0014520711440d211f801c075004000402900000415003969119880f0904110040c000c3d0720140e58007007060000c8600854002e40e584803980c03242074107070085a1001c0c2440b5040040042440071a044003407003080101c41c00040143c0564100c41212281c0e40c403182c02d03904c07610024001507007647c070100c0145520981b1604081080c42081c5c5668 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 2272031 1250 2270781 2270791
    0x60203120606070804031b030c06050708070b0901020405100302090405070801030b130203120c0a0b0108011a0108040f020303040602030304030e0301020f030703050403090503011d01050907060c080706020d050703020c0606040c021b011106 104
    0x21000f1f000810602c0034104c51540544440c3c540649410405d8681c0c4400e4090040302030000486540883c4480800b5811a002400054440705800b40400740141c020340146101a0145041c0000111120300c00e5504c40c2c1a40c2d4850900380c11919a0360001440e140c000c40c04a07054880e0403401241d0704040d10240c502c3c662020f0080c8121806071500c58103101041c5d21951550381400300740898214051032046001030300b803a0681c40c0344c0d9103041c03031603120805c404041c0d01030000050205416901000941c4164040e48860007500c1c1400300349400c1f0710510100c600c00b5841400415611486a00103681050092610302c24403a00c5000185c01c448120f040c0c559040c10016002c50150428000c0c0c0368004000d4010700441d500d0000040c08192020f0002030100b07000146a5040010640c16113040d0303001d000041216281500303000e0029404203c04442c6481100006000d600e054010004136039400e42c00b42c40500c840d00016028110440c4099043c03040c00300d0000021003040161910032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 2273281 1250 2272031 2272073
    0xb01030c03030e0409021309050c090903030105090c0a020307080702040e1501080c0414070c0201120c050409060803130501050903070305060405010c0906090b0307080406020c0a0609020103050106020312060607080403 95
    0x401e01d10314014019960f6100d505008504010a040159561601c080030580c10603e010480c0061898450f040c0500d010f810b1394050030f00c03418042c0340e110000c082e505a0ba001e490180303040c1c8071080c482d107444c05a13940301001a8020000400020101009804014805000840c0300810070140c6424007250040d8020f049000900400542070f0401c40f461014030292000c0004004505007041040c00041012091049004c1c2030011a4400d100c0c900d01006809820003502c0d0100c2d00003031850380184594011541404008514000c000c001c54400041070500910014079080055400d6040992820b40c5070003007c800100cc20b1044c88940d11452048000088001080d04060107020440d00803c081100181c03050003080411012250010b11605160703045940e28905000a032082071081c00040c00344541060400c441ca8000e40030582c0300362018400c60b80c942c50300300c0c0d80b402001c0484030280180b8010402604000b80241000340c081c020280c0303003541300d45a02c4000c62010b0700040f10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 2274531 1250 2273281 2273303
    0x2130509010507030204030203060f06011403070306140108010605030a09140703080306040614090703020702040902100206160809030a0c060608070e040b01050418020f01030603050d0201020406030605030610120303090b0103 98
    0x80e80000780302e0700d94800e072203040031400e042c20b54010941d01c1800610070410b201c080800300c2c4c01070380070741d10b80c1c111042c200a025549141100c0000c6c0542604e1050100c0c401500004101d950301810b2014140da800383d4517581540d45a4804034042d0041060075500d00b0003000309150301860a11400f80a14018030600e65242420418031003218255400481011052108901c4641e01c3c00b0215810441d14640581c41c0c0d0b8181c00010000c01c0003000003580030004840380596180c010480500c2910421100daa00340218841590100401c4900c84500d4100f00a0760320250b004100300c491180c0070f1680011016128884a45040e01c2c80d0001404a0903903400c0004200c1c81ea01c1d800d000d40010b4406100c010001121109030b200c10b134000a01c24480c40c440c90506901c2584103000464210086804003080400d001c0c4c002d510500a140003e0305090010943e4100024128015094400d505180501d00a18801ca08003038240403030405d600c41c07900ea408a03203a00b1000e0302840c010591000307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 2275781 1250 2274531 2274541
    0x503030915010b07050a03080705090307030308040b06090108120a030204080708010e070803040302030703060e0c04050106080a061212050708190306050907020604030e09070504080f010b030c030601030807061503021305 96
    0x10461030583c018400c0b0b40302044140002280400d00c0d00c9500e6050800f0070b07130780d120707864140c0d40780c00303601401601840341d084000305060b8022040ca00403401410001102c0d00c41d8410300c20900000d000e000d001380e00c48640391001c134010302c0c0205420392180c900141820b403940b0b07480e0b050003003981c0000056915000040140741d014800080148907150007507290a18550100352260b07020311020f40381760f070fa07511a1252110140092100c1c010000d104021540c0c48102c003402c407000999101f960720340f5090000c5000003002c03204602c99508044001074100321418100c0e001c3c0e11802c0c044036404800c0c80841518540d02900498440369520003203405030500044c00100380004001c48115480401400003081d0049130030614001c050b240b0110a5070be81105682503c290383c00301744503105a1348443d607910410340c052100b00d60210300740d40e4039010380d000b05659031100f800081d110580800100001031620b520010100000c0c0300d0600c4610b070b030f9400146c0044540c040001460f502c940c2004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 2277031 1250 2275781 2275813
    0x2070605071106010f06030f06120309140d020d020402070804030c141306060503070c05121201090501050307061704050c090405010f0b04020f0a0503060402090918100c0c110a0305030309 82
    0x1042d00203014000c1c2003540c54a00042403c2c1583d10542c0245507036484007144044e100c2c0c01c03103005800c400c04608849005458010500c00c150b1040a5a2020f40c80032449589404a203020425400078410003e880c5140c08001c02507120f140c2c00c4459001c200070000c00100c180850400505038684500c100310054400d0044512083c0c20b40300140d03213071232820b001141d0000c09881c0c1040552400461101282c03074414586207500c64448031809001c0b540c03c50041c401000d00d810390302000820305c416640c0b481413603591913040c0905400304400103100480c2440c4074410340da001d4041c0007241e103a0710400c0c0119400b188140c2d0300ba222a51141c0420700f840d4000d001d021800c54042d1340031880c04541580c02c80c0c0c18096060003c04001c0008003040781981e69406a030135446005019814506141c0410542c00700005e401000602807444072000312400c611908061010b02d44480e814041c5c41d40d40c131703d5020ba42440c0c080d4082201c0c00c0100102d007003040030f5441964070800030301000090306022 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 2278281 1250 2277031 2277047
    0x20105070801050a06050904140109020408010605030f03030106210c0503060306060108040302030301060f1101020c150106030204050105120901020d09050303061c050703030509030709020a0e130510140607060207060507 96
    0x80e405110855004104a4940106000403a40c540c6801c076181ca100b1400036021b440d1402c000c55100350072034004032301005154010401c940c4540c0003081001c2d80d80b401d00d5202c920703400100c42c240d00140010090a401020010b01c00b0056a0042d02c0c1c0d0000408481d046850350030076000001c1c804010000349040400c4103a030441d0090800c0546031070f141d0360080d540d00c0140111410007405030160f00415004901e034100b403890402c001c0d901c0300c24004480782d81e5000035105503410301c036180000844a000303108590545006075551483c00c0c007200705084901d04080c181c21060740d400c00040384084024841c44203054401c401450b82c0382000070402180300d0004c6014000d0a41c021861030000d040001c2e61000c03282d141c06d00580380ca2694000034103081c03140d4451b0300820b0001403800a1194800e9400d50710704402c07100302c95100900d0403a0011034408581e5440b8800040c1003d1004801000c0111003441006000038a80a25561042c0a070f801140003103411549407410b002c1c0d80703500440a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 2279531 1250 2278281 2278291
    0xb010e06120109020a0c020306040f0501060b0c060a0207022704060b01020d020a0605040c0e0106020106031a070f0804050102130803090a0801051003030327050c010f03020c0c041509090f03020105 86
    0x5040c0c20240155030400d0070181c184544180d80d070f40000c10480040c05542c0502d84160003c081d1502c03460681003c0c100c80040390340884140d480c0035000719140d04008103842420021000408460361220007000080d404800140e0340120341031101041d07111142310b050702c040d4414015005500341340c0307004000d44e0304013000103040d908481c1c00342803026800140c2c8014280c006102013001d03100c60802d022036480507041565034a2980c0d001041311501504184112845010003007074084111925041c41007060f82c100000802d40d070f0820b02220311a1a825801a001d0b4000500c2d004040b00501003160f8154002001074001107201c05480c81c0003040e41004042e902c009001901c0c0204102c040803c3c03600004090541c2c400344102600a4002001450042c02d008003c18001030f04100c5d55540020110340c0c0001c00d0403060580e160710a00907180741d500e00d10003c3c07014105a40030800500280b0540b10104805624001919007050040c07d0f4500e00428200c28001e14a007002801d441000304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 2280781 1250 2279531 2279539
    0x6050703021c1d0a03050102030c0304120e060d0207030e0306090a03020111040b03060d03020f1009060b0102120a0509030109060609091e0b06010e0607020d031107050301110a0c03020a08030a0b010e 87
    0x401d01d82d0080d00600c103003440c04140c928080790282c04100082d08120303d908042d10940c404010003500c0402c00d8000e602503802802002c22528030302c142100c030540d0540155800010601603c807800b03900f90042d02001d8480c0c1040700004200e0f40219190500032a900c0d200b65010134289000c5c140c080c031501c0b0070724080c60642858181807001000c2288170241070300b0300400d20241c2c40001d00d4400c0c841203101d03c0540e4142d50102103000502005003505000545100c0d107048075564141d8000501c0e41510b017140441075007051580d840075261900100c1c80940c040d5210350000c3d000a86510480016007884c0f0000208404a810320418100300d2049418441c101c44002d1804a414900300d80d9001000340307410001f0f0044000825620f00031210029000742c15401e5800405400c804503010380a14401124012540ca0341014241c400005c0c00452480040180000c0c1c94840d882c04002075000c2c1c0120794201900f0b0351402001d40c0f00325000349442d642c490903034100b036a000c0c41005c2c161500711 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 2282031 1250 2280781 2280823
    0x1505040606050309030f071a040b040b0f04050a020402030a060b030c070302010510060e04021312061a0d0b010306110708030705090306010504020903100c09050307090209030f0106030309060f03060f0605070302 92
    0xb01c03245c0c1d0f00c0c17084584400c0d8074540450302c1e00030081e5402c210f4100058203001c403002400c143ca0480701010080d1402c5502900c21000213125804082040f8401d54001c4014200d501c01902400001d50018144250300b5484090110729203400d07400650007800210103859030f4000c00c0c103000b800c43d00302500d9a00c6010b010306040140590080140c00d001a0889006981e101d10541303940034240c0c1a4041c0c07040784e000030484418840716074021007101568540d031030910500c5070100300900490110003801401c24000502c0440c1c0554000048418041d6070a40f07007c92940341c03220190403ca688600080000401c0c8100c0c1c02d0601100d401400141c2c2d09504040d99840040e80303070540270005000280d942e4203030300c9004d4421100030b8014000a819074081d42d44480a01010350f0014026034040c0c4900c04144038031a034144612400c603505592289591400d11608503040d440042d9104101511600007140c0d08100c10301c2d940c01000340d5115117946417490701d800703400d24040e03a0030b491303186501c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 2283281 1250 2282031 2282041
    0x30d081501020625121a010e0907050f0306030c09040b090c010f09150311040b09040617030a050a0513060804021002070303080c07050114040501090b0c040312030e0c0415050406060503 81
    0x600e00708a482005a07440e0900c101c00090700700c50451050f08141155030410400c100140011b101d520880380080c0c0e01e01210000c1841408103140c010f07070703161000501c1041480341c01c0f14148055600240024181d03520b505030100022a80f82c015501924960f00c024148640c0c020208210b00d03071000e080c200001d440e42683c2003d41407030014803822800400d81520b42ea5940d2003036001d000b507940c40c440e04580b15911130300303000f0441e00154511070046241285c00300e00e0b41b180d800304d01070701d01c0d10a0007140350540d00d0701b0455444d00702e08a1801805414424200403803030203e1f0300f00c003600306c59a0380c0c0c0e494541401040340442d1620a40025900040c07010f01c00320350300240990340445a900501e030f840702c0354580180101411114881c20b9a0f04909000400a0640214480c28000c05aa160a032a411041c140c98816840028210940e2001c0d9006d564001d40101d80201d0003101690001000f04d4042800c1d0380c500e2000b868413001c046000d11061509206540c09000c003031070301038114504 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 2284531 1250 2283281 2283301
    0x15080c06120402010314091006050105090618011206030501020d0c05070c1a07050304030503031602030a05070201030f06030f210201020405010206060f06071401050406060e0601021504050705030d0815010206 91
    0x2104400180445074800003019a40a500103070428100e16115030303140d1409011503502d504500b03805820150030075000080d558440c0b000c6c0e40c4030910041c4400c1c43d000c03501c01105565400303040401d05001185042c4003064280748a00401540100000760740c410061030007500300ea0301103420405000c0140808000b1504100e203980540d241d00104100e41140a2a54070301070286074030061580c0300000b03000c410400040040c5004603885c1d2440f00c1e812031001c13401d80c3c403030190b9261311000500900c00703c400740d07102c0c0d00541c202e281c1c0400005840380c4c807078441700c807035004c0d0080aa48050383e1074440e8603154140401442c0428861008509040c10040000e40310346c1d001d0000ea2003542c07184145d00550b036428084071031081c6c0c040b1881d140001070920040c00b0303200845064075421321b01000040c4060b4030454003403040805070f001d090310501d0003000e4200940c0c00f5005036a00d04c992800440e580d2001c01c0f1240f2440c0d450340351460b02d4900300024810030402c4040150444d0088424003681c001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 2285781 1250 2284531 2284537
    0x301140408091002010f0e03040503060105030d05030f13020a06020d021501050a03020105070203030d06030308010608010f0b0301060305100e010605042603030103030c110301060b03251b0303020403050d0315080c06 94
    0x801c40f0100c400c41d8201c10100d001d0314091600780100b900e05080000700d00300000041c000c85005038160383d0141e90342d82c101502c5079031207003601c004078100b040010b1200002c1d04882c0c1d8848002080c202c228040c98010a1198403030f07030030441c09a0f0001040c1445141c042004000500c0d11102034101981844042180006c0702e1000034140480070403000d0031550280190340d01081c412008002090750713818002c01d111020700c188400724070f68200118200318a050420301347c6508214480c607591030036504800806000f0001d0220241608010417811440940280280303a10f40d1035503140c90901401540d10b0300d01d00e00c444a12a401400c91a0555012060364110380c3c0609103c4c005142d2400c00c90014501101c8540d80f5510b0300c0c0c5c02040481c4900e002c7e40c003414200d940e451b00101e01403051400c44144011034008501d2500d01014602741145150381441c0c420310f0054102a9207540e102d240c0602c1080d11000f00b620340c5000c41e09031250300e55090080c001d61008000240884010941600c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 2287031 1250 2285781 2285797
    0xc0303090409020a030209042301020f0304030c02010203070507180f06050a03030806060c0a0302060a05060607031d01022103041209030f02010507020a0518040c060f0210020a02010b060309010b0301140408 90
    0x2d850302052020741d515598050f00458019007511818070341498010718800a47c5480c1440e078070318106403c00c107841442510a20380005111900c0e548458400351226801000100d04510041015a001030801d102d104c00410005c40d500c10000c2082c00904140c2c0c0c05d041032402023901c0e01c0760811450b80c0710080c130011a03070035044c07800c0d2a4a600c03022409600c40c0ca0008207039440707001c803000c040650018516200f094440000c102ea0340380d11302086058420510041c00240040c0c41248019142d04494481503405004840006020301e550b240112589003211079a2034001c010801030024042600015914915281038601c6c2990343c0c4400c1d000e00c2c1c00300641005004904c000c215150454507402038100288180498807454000283c4000100c900700d8918184030742c0050001d0041c69805a516000e0700900542c000c1445101300a401c0f1255080c1151340724001440a074880300c001714002c0d640c01001107091107802c4103160a640b1418804076038094043e003080701003040541030310380007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 2288281 1250 2287031 2287039
    0x150f05060c100203070201020403020d031106130206090f01030b0a0305010905060703050f0a051306020f131406040501030e03070b07090608010b03070507140106080303130c090501030209060105070c0305030313060506030c030309 100
    0x245c40350b072400c0340203020390342009400c07221a507002401e1680041c00b00441080e0101219500c4c0d0700c40340c40025039114060000d40202d42403006140c41c0c0f80441c64488000018940082c045102c500000c0b50101141d1042d9482e035513070031071001803000512a5503400800c6040c188a5410704c909080b414000044c40410015030314000303d031400308a40b00c0141601d4004034155146d40600e280c0c02501d6129440d600c04084030b605000139206001403039060550350003002582414600300c0150098600540240098042082800d0014500c03022050041002e940c2d1030f980d4078106540600b41c044107810510000109008101c800c44e4848112090309910404005ca4081d00344d45d5035014265030341001c401404040304102c90015640c18031110980106250a41e00d903481c94280110f901c2804080c1d00110440000344495014200824045218000540e0030703030740e251200c50442c3c1054540301000c04000800c602481020b00034141c105404a01801c0b5109081c00001d40c0e92054591850103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 2289531 1250 2288281 2288287
    0x114040506220f03030c02010b040b0a052209060204030b0702060108060103081605070b03091e0705011103040906030501050601030e010b01080402040c030212040f03080912090f04020904150f05060c1002 89
    0x507030440b03032040b4003407960298034000300d2011460040c0240082022010042d0b1810704001c14501e41406814460600501510240c5003010180441e01c07403c43c5103440c0c9024a1501000660071610403030002c00d01400700181c842c3c0c21840c1c0f140c00c03488050010390031584040010300c1000c80110307105044903480403000c0d54505268400178034512502c3d0029026001318000021044100d200070351041d803d80d010f0341c4031140c80e040444030329003888100403e541d100003c04d001e154040c540c130042c558001000c5a091a6407541d0803c203441490300211502d0351038405101040d44c050283c0e01490311401e000744060720311100002c1070020300910191180d0b03166000800074034001e40c1101e101e5064a02000d20501c4d0908040120b000b10071412400200b68400147c40341d180801e43e1841d19031002103040c50800c02c2d60422074008a400c407540e500c298204150120396840d4884d807241c66010000820a40e481c245c03100c0c0940200b0b50107280100010481031704900c0011a41009041803c240161 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 2290781 1250 2289531 2289571
    0x90601060e13020a03091b03030504050909010e0307030306030b060906030a110f1c0c080609030d020c0102040b0a0305060a050102010507020c090405070302090f040b010506070c03030305040215040b040501020114040506 96
    0x111500e241042070021840055103e142942c1a00166006e07402840c515840003611110380500500c00c0c0303c05000104180030901003440c105030300c660003401c0c00d400460300e81e04513120b160869004260407004030756101810010469000011a0b1002044400740000d18154001c04d8494050700c000405c07001a10707003120703480c0d0396800006101d42c101030215410000126103032403002d1500c0b0b5054417146158000000c1051000038040e2090305004050360512000d8105403000c0e400808250b83c040d50280400b08044540130040d00c0d001c00c840c1d5022410341020030500c02410b009400240c11a410001040060303500028001200070b41603464400c980e0b00c60601e1402c00e509a01300039440880d400a10000400000d075080c061405007101040300d0f41d0320800c0110610131007000611440d0b80200803c04680281d100701d60040c00078140050b1140c00d103402c0c0406502039001301c07035424000b0801380a10b5909106400b11003030440d00340c0416051641f80c071070f03841d54000d015000240c00440c58203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 2292031 1250 2290781 2290789
    0x2040906140106020a020f0402030103050d080c0c010218010f09080309010e0310050403020309180601090b0a0e0a0801020a140304020609040207080403080c06061c0b04080904020403020d05030a03060e090601060e 93
    0x2038408014041c0080a50712410000d44411400070142d00c1450147e41983d407510700b40c400c80741201e41c418008d00c0e0030b4114203426180240b009102c980309410500c030342910100b0030b00090805041044c1000d030b8030b2900400240c00d40d19500700360000c20031500c0c400d01c20707004000201c92844209081c02e200000071000000e20b000809607840420605280c2880304042d0000080c04064004640207091200400854500350300102d03102400140707a0b2030100400910800141001c83d041c3c548410f40da682140402e0702d0040c140c0c05000d15a6001641c003048036400702e00049000350924182d40b460509400140a034051320010074482c83d07000030108100f161500441d80255400400a86c561034403400c0280c0302c10003201c04601400e8000500204000000c5211031002d0780084e4040c419211034031348440540020001035049a4200f10100269851003a00b95070319100d907005554410348604020150343d2950f1100000d02500006e004281a010851038103482440c500081020b1280d4001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 2293281 1250 2292031 2292041
    0xc14030603010e0312060a080d08010603050411030d0c170405010c021003020405190806070807020a0605180a08030417030402030706030b0301020405060705060a050106050a0504050f0307090e0607020f071202040906 94
    0x3044030f84000100c00090b45c003a0804540302d0784089602840055a508030f003070301c5280b003d94100003d0566001800060301a60015410034000c4a140300d51003070b6032010903e000c400341442000301d8518201c02040101c4030421040c2e18071103074049420a45800000b81c42801c042c003000780f00b031452000c040d100070b100768165030040c40010b00b04444040d80e140000d6042d0014003644016001d5800090702090068080d98007600d0103900401e881d03d556128103000b85070140c0044006000b503580800c52a03010081c81030800e02800855640e4205407034040b01854401042c812449010710800000d40c0d000324500084810700c0c01c000c6203071031a1000003802845a60815944883c0106001041c01400110184a804010710030441d90341c0312242682d1502402d0844400140b08100070300c2582031101011810b40005011221b0054036540c0f05002d9a0700f1490310280c95000d00e0420110a84c100680c03a0100d03106400360580904090810500d604505c00c0a80a191115804402c000941e480 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 2294531 1250 2293281 2293301
    0x807020906102f070e01060e09010510050702130501090c0305010e061012020c12090102010f05010e0a020a0909050403050901080106080105060307030b01020a050a0c060201140606040504051801090c060f02010c1403060301 97
    0x40e40d40e0361784c03544030b107148a000a000d0318000038094590140c00c1d01386100c04034103a5000401e04800c03138482b0f0504a074958002202241c0010030a8080b2007550094010a8080c064074003002c00d603107a40490007012518147e000c40020480013050003c2038454416402181d04640340140c602a940c0407807001a11801300503240b0780c85884041800c8005041c0a800704000907802404080408040001942c10a00800e10b00c0710300b1202068000d1860741c001d015112180c181515844d603128a0801200c00844041d80840c500280956003580d015403158090641030a01180319410800822460b0000902c1c5509041d03550b003001e13245a000700b041c810300300c0d071046c101c48400700303980f40013501c40016210320405582016a402c0c0b202001103500e501c1400c020348182d003810300e00403c010151030b001d0440760740101030818003104410203029035a60a4000c80c04500082e242800041034001c06000950031640f4040202c070000360f0010140d49455294800142c807a100c1d000064010441414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 2295781 1250 2294531 2294533
    0x509090307050a050a0b010806070207060e0d0507090203010306060e01030b1603060b030a0608060a0605030a1b030213050403020c010305041104050403051309050a060909050304060507060212040807020906102f 92
    0x2010300e0400500084117190319108820000d0b059a075141d10a54440003178424801680181c441480a41e100345075805004400a1a240c2489015141c0b5802d1409a1b08584441900040140144510760158a005106002030390300a989075440d90311081c00082c04540e04400c900c001a40554400d030042c00240503078103ca40d5490400c00c1e070240090425102d410f90300e014020000d0f1501503548240c10807203c014019080c42e6881d07503242009814030801d035841000040001102586428842c200507010a12000546080030704002e031403d034450300e02074101400e0404120000340001e401004100c0241e401248545031171400351903900801c0e0100e408020b0074100028000069003026001d00c58180c0704002c02e80d02e130848241601c1c0d4822003d0700030750042000f005030301e01c1880101000c5000c0c14006081040c003400c1e41c4d0b445601981c00703844005012076034a09501c0e0540d05680c00c120708583da000840c8041001a040c208110f19804140014510040c0c0c11003100d15400c02c01200c1c54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 2297031 1250 2295781 2295793
    0x11040501060305060a080c0a0302011101020f0a02030a020111030402010e04020d09050616031505010f14071a07020625030c0509030d080412050a080109020906090406090b010e030115050909030705 86
    0x801d0050041c60212051846450004000030300850702056861301c03403034041c0104c500182150015103103c1c80c4100b2a50b190b660802000b46850f1000010b0800c072500745c0d02940e07980d140349030001d09550f00070140341401c081c01c100b8040103030b030880b0960005040c1a5400340e2181281c0e842d440042c600020060081e000344c008121000c0656003031400688016102040704580306903407507034510300c03078000c6c603000c200c000304140322a60246004021494440021900e04035040d9202c1302e145147c00b1020190341c5016050012054051010310362000032602c0010f01c002c071040d02006070300a990a070009140e078a480e0b000540c0e1113a0115208520060216100f64410440042c031843e4219802d48000b000071001207460f40c841d20889221010701c0d90b91034642d900b0040000029400010f211343e10900810410310640c03540c1c0500e43c000c0c0484480041c84408000025000c3c8201e80c0c82184030fa490000c0b540179600d81d0b5003004003a200240d035054015070f60482c4003882d61040120140c1144100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 2298281 1250 2297031 2297039
    0x10501110f01092306010305100504020a0803040801060906050301020a020706030e07030803090304030c06050a080105010305060105070b07021c020102070f0b060d02031204090c080105090403080703110409050405190206120411040501 102
    0x109444400285a0044c0c1403a210700058542d2100c4080c0001400c54200000322141514103800264009000600250180781c0e1582c07903170314562269004d000c1070394466070100060140c611800d07000346020745c000e500d466288a40291a44001d01689080c55519170390310801420030028540030b10381c0220140e80d00e05022120036034a400510044a100310220700100c0e035680f081c01a19840c80d06900d80400700e9081100540140500030540d03030402a00b4011000400e0f5039004050282d1100d401812210315400d074110086500000703800b095a0041001600180b002102c0c1d240e15504084000a25105d03a8002501102d0302030001c3d40c1880f84812410050380420020030441d14091020094085050419582d02c0801d1092642c840d0740c02c000203010901032002142e01c843d06203800558044d40719075090003600540c0040081390740c3c071030030031040002c20098022000c45054007007440c40d120b13600003219031080b4842c1c488581c4400300400d0402ca182076140c40001c0c00104280415a10307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 2299531 1250 2298281 2298293
    0x10f0903030603020a050301060308071203020f0a0507020316050a140a030206040b0309070f05090a0903020a02061801080108060103170c01060906030308040204050a0509030405062505060615090603010501110f0109 94
    0x10b03e010603486a0040741000035203140501c117150443e9070100101c0d0415441d52a8413a05500c05c0f054102070680800c00a12040341000052030004902d071a5503403200c0035401494a0a006031541e07101031215800180321642d201010a0304584a0044c1c0712204040900441e030070b000503920080d08010302182c041946107001016510405100381100d144e04e46d0344240440c002c45a02c561502f001c02480851048171150b009200c51324024011501083d07010740c04125141e0165410030b45030b20108c55109084c5da48000564010325040380105540e50440d01d402c40c0c41c02c01607025540880380081c403085100c800703410460081820b6031081200d03d50341d040113441c00c41c048800703c6c800e0345004006140d0621900c245400b0309a8030005608040c00c001c14086983d020b9030988036456110b106901d131140c8540d502a502a00c2080940000d0810301d040c00b4024807218000b00b03010005010564041d114803003500c4c11644246000146402040362050800c28500128039055091111150620030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 2300781 1250 2299531 2299541
    0xb030703050d080708060607020906041401090509100207080415020708070b0a11030a08010501030b0f0301060803070203061608040305090402071406010501020706030e030d020711030604050a0308070f05030711010f090303 97
    0xa05440f40c140075500e0220403540d140c02200c41c2c42c0c1c465400e001c8c2c68058201840125800100038000146561040d0340409188600b6070000510b01e45400401c441c5d82424481c0d1032401840502c21350810007030342d07212031040c0100d0017590b20240c0c0a140d0496400d10800c01540140644401d0300d0000382c58860710b0840c0c0d80151281800701c0d14440c000811f09400100711416842290348040e9140d09000045015000c400d07280d43d80300d4420805169035540c2886642d000380b50b508002c2d41c1d113072102d01c1030506120008060303c0e00904d482e041c40d89000c0c1c02c0076003954403d50615200303a40c0d0401c0c0e0b000078001d024040c000b4224801440311245040c01c0010b501c0e069038426000c64021b2941d40c413048080c0c8001d041c0341c4806402c00d000000d4500d8070354000c2c4c01f40621820046030982d0510021a107003210454060f5400d600800a410a250b0041c100ca074100800b854400781101d60020050710510010702403504200240c1c0c60741131505000e60101402d404441014043d2210600300140070308 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 2302031 1250 2300781 2300803
    0x41109060a08040c050604060210150503030a05030604050705040b07080901020a1e020901050405010b0d09020301060306140703060e150904030201060504050705040501020f061006050a0e0405010303030608060603010c02060a0b040b03070305 105
    0x100701e1310000308852034684269000c40351541d00400d0010f030a600c0b020041d003007030600c0240c2803d00c05804581640e0502c080d01030140d00742c0c1c0f900d0300c074a0180104426520003500c088203102d07040005020300122a402c90f0500c13070301712401507aa1646000101d14050388050084c05005000103042c01001c1c10b12400c3c20014002c440c5005140d0701c43c001c100c201d60b400c1c40341c03040c8010f0801c22400006119088580e0040c0014000908203907a0307210344068400c00e01841e4801e0241c0d40800014980601c11900500310f4211650720510307000c49a41d51a03651a8051440b40000d64000350800d4400d407c000c000d007002620900050909100c0585243c00c01e008a6000d40039032810307000c11950001c0c000340b0030300c01d03200034500d020300c2d140301600c071980700e035906000f002440702c038a05140d20f503406590f008602c00d94000236081e00c0c0c01429828418064840d9101e80d0400c00d0b03009105030700045407278015400c107600040e112501340000b4014800d02d165107805024400002090120118403500e140c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 2303281 1250 2302031 2302043
    0x13060303020f06060604140307030804060e100e0607020603061c030905131503030f0212040e01090f0b0f09090307060f050901050f04080301060c060b030105040f050705011805041109060a0804 84
    0x14aa02e100500d0321902e01300c90503900f10509101c20030070072003020384240c20301c9009010740300d01a441e0380300d06020b0f03400b40c2c0140b0003003a9000c008007140c1c00c040d40d0010f1100042c1c43c00e100d20405410010b0243d10500e00042d1041802102180c151341c0e80720051100310b40340038600401c104843c80c001e04400c1c0a0300c6020b02c621740c0790345214140702540c011b40341070311420710140c1403490443e9003e541c202d01c07580d200011032080340c0302d4403240d1a101c801440500500c058640c015890070742004152205281d20655031420309003490f8181d211081c214a8150b0200d5021900da41d070740d9101442c0d400b481c0009042281080d07030500f0b1441d82544454050220b01c2e0081c80b9559030341c60110100001a90000c092180c01c00c010490244100c4000c0390b041e02c80c1c00e010a028922a0009003075070403c0e03409550243c1041a214200042040100300400c42800e082c4036408030310041642d20560751103078600031925440890b078001e00d12030443c1c000f807400402c51912031000b09001800010100d07000c03148 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 2304531 1250 2303281 2303293
    0x20706090203060703150905041407080c030c01050a02060703090203030d060b091203040f030807020103060504050c0a021c09031403070206070c0305060a0204031101030b0102010902030f0109060609050c0f0a05091306030302 98
    0x100ca1003400703007451586c03100c000d2522a0340703006100001054000c2081d681c1401042a00d010700000780316000040140d08001c1804050306820903080181e5140142c0c1441310030466822002d801086195201115080000e82410180042810f51080383c0c44020114504000407855103c040040c065040c010381c0c9240c000a040c82074965030348a5400303511881141841c0403c00104194010480e091061601140b84c0765148042000c1da04140c404151048020641c2101258100241c000c620064001100c2c1305100c1e10000d81011141d00000d40260507c075141c0c20032420400845108550240106a43d81c40c0c03030070729640529841c001102c0d64000d80300840c0c0d8911890003910141c03030700041e8540781091000019001801d89282040c15552112401005030ba0140480c001c5040900004512007040d03107482c00807100790340c00031410320b4a00414402074203440020748840c140c52a0150341e54500800c01500c40d402095005903100c14441034503283d20103540c2042c001c0300d10075021201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 2305781 1250 2304531 2304541
    0x14030703171c02070503070b0a1401030305030402011d1f0201091a01080f010203060102060a05060433080a0803010306150b0c03120c030f04120306080a05010203040c0b030f011505040902070609020306 88
    0x2080e4032030404c0180042c1e05c18811003000c552200c1006070451043ea400007980170080509060000c0c09038800d501180c40402040b00b03550300032000c0e00a4240d10076002078000300c0c1c80300161840c0442040640807020364040442c41c54002d51082071816000242595003442c03082c0b40e1030440c6c0b0300b4090f0018a0084003e80001d1840500079207004d0030058002e4901c6a84400503540142001004035910a03280c01e04198040480c1841e0b13000c201c010071005d00440d1981082c40090030040e800048258055410f04011642c0581524103480c1d1100020800040f9403004140c0c0703003150703000800051400109000e00b408000024a220004e242e000000e0399514005c08545020407079011000142c0680003030001000040b800c8c18040e1103040c0003070715a80700c1c0e11311454041d07031082c1100c1f01c0c2c0d030002c203002c140901c10300682d0081ca40088408e1039440c1c90744d9001a001018454200c80385640441010071358007820588000c0d005032071045485204c4c900f0b0050250591303450036170181c090100829 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 2307031 1250 2305781 2305837
    0x507060206190203071707020607081b1204081e030406050106030c050901030f02042102120a02010c030c02010903021003140c03060a0303080402060d05040506010602120901091403070317 82
    0x10784510107021450920000b00e140401c06507200522400c100011440644100e4144c2c1c0d1700c4030701808a1303038014080c9181120380613020110244c0a01d000301e078007000c6440d98005050445000000c0746d803035071806454a2a1400d00b40c001c403440b48083d1011900355203803045004014622403400342c03078280702a9985042c26411117003014600000200204000d1005501a821503007610550101c01807406a44085040e00c07080080a400c0a15520f41c2a880951170200d0302802e40800303045c00381a80c07403030544c0040d00510f542c42000302841134210410382568001c1c0c01100c01150003500301034004d051520001d00030310410701d881451a03045000b050707a4802e6071064034880c84016280840345804c5480907200c2c030900800c120f910a4041088e840041114058180030340d20a40017030060b541080c5002c0d0403c0da0340d10551002a1050101d15140da9008585808030342010302800b08122600020906103942500701505c01008000d5080c1c9000b401001081c0741e000801c0d0001000c03d00b08030310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 2308281 1250 2307031 2307043
    0x11070204020f120c09090705030402030703050106090f06050a0509011701060302030304030609050d030504151d0318030706080c04030605040204020c06070203090a050108010f0605030702031e09040b060702100302030702010209060408060405070602 108
    0x101e0b0008606c2c0c0005401d40e0142d4019034001c1c4c002400c036104140e8981d103450940d002a0080b141440e19002243c590302e041340100c0c4c1c050201165444c64090a0002080409805100d9412420195000c030940300d8800c1d03001102854002e010f032070780c0e40d450381406409002c55800c1107034a4421171a80c0071a251003449841c0c02203912586505040d10b02c403045202400b01c2024410000326110000b5514a6040004001c424a5519020018a0300c01e00b01400d0041a80c030803418040640d00704484106d41c3e07400c49080d00c0d070000001a5944450010800a0103900100d60480c8030300b00600c811150008003514418000300c0d40020b02e03e803107000442d0516400c2c4213400c3d0903840d0b40b40034080540100091036000d5110305c1181d0921400c160b80461800240c003400d241500d001682244030b0a0901842c1c0b44090169445460030f4a0ad6000c2002441600d500c01c0070940d020010031000e82c0300307404032043c46c2c03401010b96031159110050652149425542281d05200b20039000500b03600102d45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 2309531 1250 2308281 2308297
    0xc1d04030903080307030b040e0c090903030106020a080a03020903010218100903030210021803060412020c04060303020307060905010b060705070e0702010b03060103120e06040803030906010602030c07030611070204020f120c 98
    0x80c40c03001c18034669070303001c040d0406040f540905031510761342c0e00161a14032443d50000344071001416400f426009021005101401e4620b46820400050003610340000b109007050f580200d64559a00190704124024000e07002d841d84c3c035500018520104196810005400d180c00300d03a40e20510070a48015101c42005110040240c2c100c81c40303101c4075140300e501a0040c1c4001c244000d03845400100080d00302402114125440b41102449003c2664100910005410150f0303040200a0031a18003035500d003d100c900038031741c603101d40c01d03903040000039000103204200140c0415150b040618040381c65900b9805030301c0c410380e4000005908107105024240c500480540513052690070741e280c28000740340c4003a030316091140010780d2084603116640203000402d020170185490b4100f0014550400d141079004400b19071007480400d02250010801c0402c4a0b4452030009030392840c10018541401086d5000c1c1d48288040750000c0c0280c0c0712001005841402c40300e0743c1c6540c0d5001041c1c0c1c00c0c2d001d0200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 2310781 1250 2309531 2309537
    0x6050307110d0c0201050304020301090501020406050c190f0204020310080105010807050405100b0405090a0902061204050105090d050a0f0c080c07050a0f120303050702010b030d11070905010305030d0207020604030f0c1d0403 98
    0x41070004d0f5000d5002103030001e001400110340c41c01180c45081c260380c426070052001810004d031000a5901c148042105008541d04034a8511119141c00e1928101c0f4070f00a8400c070384c0040400d00312154103410b6070003890b400b030080c4030300d40c0c1d1a26a582c8a840300d01ca444d014906000018401c5540d801441055440c41280c050800341400d060045045005040d01c1c4903d594a402c04003607500c00000e04219940c0301c2c0214150728051038201c0c25a9009091903038294030100680310a241c20030151a80c010306880d1201c00450a05000c0b150303500b8078503014185160000711100311410104a01c000d40320f080d9901c409940c1d5400d20a1104c80c294490500241f20303007840c28002900c640c0140d5048136880c4004660003050750001b03411f00c4119032103d004500c150300c0d054000e8906103c100004d090022040003150b245444441c3c13a40b09104040b15101d9001035004110b43d5003000b0749003d99004035a0a0340c202c250f29003104484400e014604007a0800b000e00400031f440b0303440b414440ca50641d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 2312031 1250 2310781 2310797
    0x605130f15030e120d05100503060402030a020103150b0301090c0806010503130b040609020603090703030801091103010e0907030506101406070f0303090204020c031309050f040209070c1502030106050307110d 91
    0x508400814410f0f49400741409100c0c20003100035000c901030812070810303440003d9a0300b82002d079085644001d038040303402070300004100800741e81c01041740b034101a0203013000706440c414000e5405186200313400035201c0da03502100224200100c0c0d40512000340b001c0e212240d072525604010b486078001103130150507440b03941d030b455000241c4103041543c02910403440850360702c4484e400150310b9042158500843d40c0300c40c03010001e050b805840c0a0040041c14000c00103141125840695844140520044066004040760845004000030001180c01006a07106414403581c0d40000006a200304c43c56039032414101071461400d035040340c1100c0d0780140b0311103540010b960f0560252002a80c2640e00070b5080c400c05240c12824402815560f1401d40303c8045981460402d030200e0b13802401c80001e503203002c01080016201c401c4642d400101030304122508032268604815100b030007010700d12101d40003000018503030390820044e500803c0ea0344c9600c003c402c0641d9000c2c3e5509210760560000032961 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 2313281 1250 2312031 2312069
    0x30c010c2303040e07050c010c0f0c0b04170a020a060605030705010804061a0406120201120203060612040602070f1109161d03030d060308030f090d091403010b03070605130f 76
    0x8110020881c10303400007a0b90a041e0344181e050b503c410105e8103440803d0380002c03c044072081c01e200700314180f21641812004c0a40030140140b10b003031503101c003d200d59900c1e000308003804600c0310804000302c03420161560300c12028500035102c1041c040211480d80c28100085882e1502084580c1940d806a41d05c190f282c1c0c1e00d45402014104c0c00c0c0c201c0c5a104041c8025001e10744490050002408401c4082c5559003581d02c0010b00500c0008044c1d0346140c8107109200d402e603200ca003101e0304200a609807800310703212801d082e8000e06c50400020400c4440e03180042c02c10030715100c6040560070460350040a81d5400704c0360000c038902c019a00c1c002420600b03030007665903c0301d180001b41c558040c1c110b03401c1c05005500e5200701c0394070780c105031b8003400c010041006207c106414960b000205802420740c4820800010b080c4080c0c0c3d0280b80880703942c41254116580342503002c0740c810b040c02401c0320220765a40c0c0c009442984100c0324a00341c140082000705040144207091406c0b504602c100400243c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 2314531 1250 2313281 2313323
    0x30c0507080601031236180603020a050f060d060306051006050c0604060c02030403050105040c080d02030a08010b09130207030e010e012c060403050601060206010f0608010e15040b03010204030302010506030c010c 93
    0x8402c4007038100303503210400609040384810324900380c6c002070200c450711341002c0884001c140500d280e66005801c4c50001e00058a9400703102c02100c4099520300c4001100100250040c024506c82e400700c0d62030880000180305840e00f01c43c0c000c00b0071140e188402501c84a04032903500c01d122100e4026401140820001030b00c903071140c041000701c2e1040d00d0819860707549483c00e44000745c8054a02742003140c410f011f2940d040c41501c01c01e49103400254039000700c5610181240e0700511036140001d41c0400c000740c0ac2d0f1034514940c0401708030040210f66600f054034014103c1e440a404007400030b06140500ca005502800c81000c0720983d00d210558800448400446d0030141061525046001800000b000443c10403d075401303004075801402e90b5604200c001800300503954404030400c09500010801000062038203500500c07180c10083d91068200c000c1405052a80c08082e0198030008001050503419445540912812070940349015810b500459419484003000361140080300100d240202d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 2315781 1250 2314531 2314547
    0x20403022101061a0403050c01050306090708070e12060703051803040e040809061b0d0201021905030604060305030d060302010905030a02010e06030405010b0d03090503010c031104051002010204050409030c05070806010312 97
    0x1070107500201d9443c4d1a840580c00d14116404007900c6400082001d108201c0c0074004d821282600b0f00c0d001f0308529082c0001030101030094a9202444680400700e81520700c10300c9070501c1ca000161540980c4140111540d0342e40004480410019140c0030100c1c4000c10106081002c0910450096003800e040c003280c4001124082c104035541c0400304152030a0b42c984202804070341c1c1c00315410300c40c2c2c401c2000b64075090403040111001107920400100c0c8048d5418203030b074a03844116181c083c1c0c4a9a0305004140206081c2d0030103804d601c00891900c2440140c1d070440c405072403003a80c0300d00b5100c3d0f880341416550411280c3c003d004c51626020f10106040034405182c0c0207000e08004500404000049013100303009400030f50000b41150300900c800d04090055800c0c42c0c1c218075080241118414071641c0a01617402041e00c220688d01c3c1401040e4400d4040c1c90140c0001401003040e8804da29000e448811951710032a0380b40039154001038a90740c0820460b04990f04071040486100802c0000c4031151 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 2317031 1250 2315781 2315839
    0x1a01080d02010606050406050a0e1203031909080714031606020a0f050906070b070c0b07020c040507020303060306010e070c05010509030301030c061404120c030b090607030b03070b0d0905010b03031603080a02040302 94
    0x10ae101d00303003440d5941d039a96007100c80320688000f55a072424040f101d5204002060341e0750b8052410440710307000250548044a0403550404108031540303030342c018a10304501c500192201c1113038a41c0b054400b4010154014171402560f52985401ca8003450400e4032070313018030b20106034085814885400414180b148c019404003003881d000200480659a69028003000d031030f40c4006a00c02e600e00c8a90307040c0f5210b10750b040305e1140025800d601d00500002e9840c40c0500800000540500c04a15000d00560740d1721040d03a4400000e010b075140040b112550307608244020303201e5a15a08000500d54001d010360324203100400340c1d16182c00e040c040000e0704540800d070200c5810407a550f000020401c0616014003d10041c0701804290520240050545040b004443d1013500001810040c001012080303030907210b045480802d4000140c1416801003503405070440d014000050038007028001003200e81d09462190b2900203840e22800c450008078041c03400002d411440c032004614851840d090000e00503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 2318281 1250 2317031 2317037
    0xb010f020a08030702070f0617010f0311040902060906040306090c0b030c030106080603100e0102030601090504020309100b13060f06080a0b0603010314070315020c070506160813031a01080d02010606050406050a 92
    0x6c6030764050094000d0303900d1780501c00090064805020701008840c00b113004250000c516040c840c11610340354096010110510b10465543d0f20f0035085444a60544202c000c008201d030f81c88a0303807820401d02400c83d8040c03c907000480107070081a03182d1081e003a01c0c09406100c59407400c1d40c0c240070050324402c102030072155240c8504841041601c6203409040120361400e0009030322400d140002500052640c2c200903c194014020080120700c001071b42c102c0400e8814001c145c0c080c50801280315044045003401549040110119014401d00350650841d5000d580303810541c0e40d241581d4003215002d0344040c4d800348003000100082101d400060481d280c800b8152004140c0da0341d203c05444400301c0580514a8012616451100703041c49a0700c0240b009880d02e5180030600c0aa03ca1050b00c5002d004101d44001704115100081e00e82804018580c8081501481c40d40940c0011001d00248124140d070320481200c0d8400303034418011f10080792200d403139282c1040d04000058440c1c0d0800c20030b210030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 2319531 1250 2318281 2318293
    0x140a06020403080405040c02010902010e0409060207020a06050a02060a1401050909150709090605031b01030e030d0606020a0b010501030c02060705030a11071406010501020604030c080a03060306020712030b010f020a08030702 98
    0x414028401807005611a2002603620f51600040c0406d640301c1d41008401d5901d07082c40f010161f600030a0f86024414100c8000070181e07014070f000402030040d0030011303410043c1e0510214003550844024410a0782540880d201c40c0d4980c3c0c4200151040b08152042d80c4803103e00400c01c074200f411005410103038080c00e5441c0312002c400c06410240381280c0c0100000d110390750410414049100340006000250043d010301d4000340c6c0700d00d9041c5446c0c80700604041d1ba8142260b007200c0706105a40701401c0e010818020759a448100941c0c540510400b503d071501e0f007200001d029800f034441c01ca0300c6403060b0041d21055031010410f0300c80d500001c0001e540309881d54960302c008040e01c40280080e0b403017181001158551103140516103071050300412f055512210502c0003094006a55032035890340205001d80d1242c1c1c6503000c030301400d910ba10003030850f40027240700010090f0701c0301d034007440d40b00750740e02040f083c2040001148d0309807681440e4005030f04081001070104480707600440c0d1040c03440c0100c1d20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 2320781 1250 2319531 2319533
    0x6050d022101050a05010c080301050616020d03020c040f0516030b0103020c01140a05100602120705070f06080a0e060613021303050706050307020f0606060409020c10020f04050a0509090a140a 84
    0x1200c0752002400090001c04401404140f4005071140044d000c01c0c40c2201842c03503d0742c2d40b01698801802518490384020489541003100000c84030555075000e00440d08903815454041c0d51501c010a005110b0350414006c0080030f09648105445400c2c8074054422444c41e1003010f500034040190340504164007003081e50566002409042103031500e652082c429031138010000c17011180041c002030454001c1541c10440f107503001542080034814003110540e04e081c1031a20340c0c07400005901c401980002034500140454100070315520130359208005109101d4070341481c03600c0307001c1107071011380c42a401c3c81e40f801da0b0009a8041c2c900441c0f0300d90701c0070240d901c98613210302c0c010541c0d10800c000746001080004003503040c881c40c08400c2c80040184414102103000602600460140c540900da01244414a000c0200201c251340800707407100710747d01d0200440700c000e264014082c0a00907400c03400e00240e00d00346100f00c00e100304410000381c0305120740b690350000c003009400708000880c8200f400001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 2322031 1250 2320781 2320807
    0x30b01030f051005040b060c0705060309150f04050c01170c0f0c0a080c100605012016030501060602070506040e040f020a031502040302010f0806010f08090304030602040909050c060c0706050d02 85
    0x58092022043e14050b05490001080207442e600d8100d24050001841071007800c010005a00041e00c004803a0f882c0c60b40d450042c010300d08045030760407038000d120340d034280918591140303c604d0080d8018020b84012010610040d502500b0500640d00322407440800a00c01785001c074060800324280c100e10750f24183c1502c008902c6c1445da2441900e070100d0000718144a103c0411101103901d41040083c0300907450030002800d240c034450031002d203c2c0540b10040b43e84000c1800090020141c1000c462181501d81c02c01e24020811030107081c000d8403807560049010715104082c2c0d4119204001a86038075074070780d0383d00d2650804401d01203800c401c07c000c0110000300813803450b440d4815120401a2183d145000040140030314905450500080c10705201d0780381d903c02480401d004860030a401c141d100c0c3c001c02860f601c905c2c0d001420300c0e840400e011803011110b81001614030700807802c403940a80b20500b04246031140c441841314a0340b00b400d040004070b005c0e5024110034054880010b04181c11030300c0071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 2323281 1250 2322031 2322041
    0x30902060c06010e0108060c0a030c030b091501030509010e0303040210031506030f0c0306060203160311030a0503011703030124020102040b07060b03010c02030307051b07050303040608090c030a03050301030201030b01030f 97
    0x5440341c2d003205005100c0302c003024640500510140000705540c1c1030900003940c040c85286d01c200c081548898000e42001d00a42055948a030090408520b91070401081c0189204201c4458000790500c408034800b00b40501440c1880040a03001e9032441e100c2c2e500b0024010014016401030607200d540d041580b0306015600002130186440c00f007040750100e03242c901207528001484040c10b01d0b0003c1882147da000040d0741e0300e41402c0d2200101064a81025140c140e4400320012940c8400207080402aa00c60b016504aa0107a240d9000d042503030200e840d02c0780030900420980318008988016440011002040008524000149816141c0302881c11755800754009407a21130301c4160411090a0911410032190b0312440034508500300302c0c0005000b44110001c1c224a81c528520401840c1070900090000b418018103c0e82d545039240c40c003a006e02003c0328000954095054503035110300740403601c0c0046540c10341c2c403d0b1841e821036005400074460000d0b00b604150380c034407100e0103140f11b9121f1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 2324531 1250 2323281 2323297
    0x30906040302010f020403030e130e01111206040c02150403030605030703030c1e080906090a05100906020d050304020102060403051606090302010b1309020d0605062b020109060201050403080105010f03090206 91
    0x1810151810303007406400d46140b4034446500a20400040000c40d40c007680d0a0008074080340c00608c2c40c81c80c043c041703003e40000c001144e030952811070392605821b440801072444145960024407030740e0785c410402c42141d200e1400d80c03000da0408011584055848a0000d80c4203100c1c0c180002e8441d110008240341038001c0d04206c2c04110317000290700c1440700880480c0705122024a405604080503034071280240205642140110404111042c0c560b4403040c050b0040c00c4058406103680603510801018040c2c5881b41c00c0260043d11800c0c0e05481c03194040700c0c461501070300200300e60f407182d0358200ca0987c442e5150481c0207841c600c7d2040090018016640d00a0081d8004a8090100c1081015034140c2000b510801480d20f500a0f006841d801c030541601030300104002007a5580c00d0100341004101001e070714000f4010f098020040e42111021111107000fa603446841c82c0d201d420580c01c82d442503602401103420035004010030f601c1031407500300501e81403802050145a50340414055000424 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 2325781 1250 2324531 2324533
    0x5060403020703030306170706030c0903051504020f060301080c0f011e08090c0109050d0605070c0209040c031707030503130804090c0206060f0a030308150f12060a0509010e0705061e0309 82
    0x41051503171502400000d0100890144091030105d0365081d035868040c4a484245a2920240203086014010340c500450701f100c10b4901d003e0303411078a14207450003200c00300c1c0303c0d0703501c2805007103641810020340e4127070b80b034000092002030883c40800007126036030740c545410040e2200125101044400c000b60054050b503e4551060408100650820501c1030701d039810820010404c01c102e91b1202c0601203690340100000505445401c000ca6145203085806900429038805000c00c001019001c0400ca078000c40350a0400d040c804e0b07100409124440c0040c0002d0b8052010500135032000e1403422901b4403408616141c1382e0303204d6103501542c5850704c0d510050307080349013000307280c2c01c01c030850392603c2074100c81066140c1d09642d0301400c82c180c00703040381051988004000c0903a445501c01c04103000e10013000c400742c050900c0e1980c0e5980c50700301d40300340e003940c00c2c04080b81144505004055404180c000a050107030b041405020240c1c00103121250034100c42c80000c60b50f00c4491000714001d085043c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 2327031 1250 2325781 2325793
    0x109020111010e030a0503040507090903110705040501030807080c0a0203010e0a11060712050a020106050402040909110103060b04050d020105091201060815040c05010302030702030c060106200c06030a05130506040302 95
    0x2000150040d4080107031220181d05041080c464404044100c4100c040036007085a240e031124148945000f02e5034020300c6501c0d1400c5c030a00c00781504210152041c0381c0c0340c000c0703510300c1d510b800034881034030428400100190014800d0074001080c44002e03064406015084540351142500002d003592144001c000051700200c1e641420301031401ca80701c190084c117070740b42443c05020760344441d543c05c006460380003085808180803d07a14400c0d0040300051800034003d5459030340381c0d0030800c01090181c60072142000f0141c042c078615402402800102d0b014490340e9070a00345001c0501401c240c20150403410048200305000f040c1d619640ca016100394210000a48642042c4105181108900003442d1942c943d8040000080c10040400c042d90070a02c0d015072680c54401c03007030340365001c1c04000b41058040c410004c1580ca600c03103c03072000c8000e00c183d603460000300152010b880d074060542e415008101000000d1402c1010b401842e0050300003010400088881d40301e1909058050700c0480040e0003407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 2328281 1250 2327031 2327033
    0x903010b040b06030f04020d0c0303120c1b02010e0301090605010b04050108011a040603090206040305010509010e010501050d0201090e060609060705030d0c05030108060609090f12030402030d050304050a0b040804090606020109 99
    0x91003200000c00e42600c0070406400c039100041c0d0107010043c4060600300003c0e00240c119220508030443c030341da200700c45020441d160f10303014009107414860111316a18005148241f03d20480488621100b964003c1041c6030707650300111061103220001942564840211400184e00c9215071402410510a4240c079141843e0006081c0e14040c1d00850035068420781c0f82e0075151a034422a008c803902800c0008d12543e06101042050060340d1015080d5440c0c0010405e00c480107400214040d80f186e8002c0010b070303132100d081090841e1541400f0b8005010400244800d810340f0100c241c012034001d00107070901103114001043c6600c0102c0407a802c3c0c00210302484081098000c111400c03c4a04102d81558140b030340066440f4001496140304190540c00b044c0c000909020300f100b5040904188c171400228030b0042620380c0d0040d10300700d00074402c202d48250421301c00e10950303000303d912001410034841240c5500f040c402c00504161110401000001019416403140710000c00d243c5d00081040380503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 2329531 1250 2328281 2328283
    0x703050403020f010203040608012306180103060806070909050903091507120305041203021b01020a030e0705030706090501120b03011803081302060306011803020a030503040f0815040204020a12050a020903 90
    0x114031005055500500c4240700d01a0804205e90546214103184180da503d4a160bc11101c00d514116940040c00051401d0f1035003504d401c54003110303d007030b2014007516603a070040698030a0201c0b02d05001600030803050080907a170341c01c903640101d01c09084a0900e4807110000e050b00304911b880c130348941d4000079080d0421050552807030710351560381010080e0349429101c2d15829440c80204204040d4005150b03d42c0c602c1c0070304004039820614008540398828030001070014020407540035524030034130500090501e4005205e4007076488a54540c11010302c0e20005440380c42101c407501664580b90303050010292024410081d0024264115014101060501510f0041c0160021b04211908070398640961100401c07250810702c20f20740702c614800042e08940c0a0016a04020740c004500040042800780020241c4241c55695080d85405940d81211560b28103a02c6040c1c5c2000c0103c0d40005d01601e0294058000b240071070030315010805000755450221242110182e9141d6800324450899040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 2330781 1250 2329531 2329549
    0xa06020313090504110f0103090b04080d0f050402130509070e04050c012a0b100b03090102030f07020a03080118020d0c0906030606170402040b0f0303030c07060b0a050609010f1103070305040302 85
    0x403501508114a05103519005c4240142d540000e006d82014240505c550b4400e50010341e042d41c11841402e070303d080c2840c050520341e0154848428483c10203610111030345075031041501842d40100000c0d0310004480e007002c0a854010b01c111110302075400002280307014907980c40e129601c910058041004010005480c91002480a076008030350140b070009196070120312000900d03081160070303c1940e075250700f40b1070b00b00068001148240010040c001e1358003054010714000c008400980070707a552400c0f002c03a0755461070800038002440d0f0900420405a843c021400d010402e204094509600418400140e07029500d01400060545000308985941403242c60058541e43c9042c4d04800280c822038208180007030000f0b07114617910040c4204942c1e03088040681b11074041c040d2a00c80c6420421203c040c0c005600a541080c1021208000d6190105611050380d000500070f50404000c4030045400d00e0880b0048018032280b0031220442040c10009000c049200b5a0390907941e81c11b520510100c21 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 2332031 1250 2330781 2330789
    0x30a15060b07081806040f060801050f180106080405120301060c020111070602030a2f06040b010509060105030408070c0806091f020c060606070503040e0703290102030306010c02030703020a06020313 87
    0x810522840000480c850100c44152450310140d0180d84c2c0000005020b82c45039a000c15404c0500780c1c40001e1264002031214101c460440d0305601958006003485400b04c504090f81492104910041c000207024a00542c1c2050240d01100c000c8048554100e4041e0320a070014000314031800100000c41d070313004d030100c9500c1c0210070250110381d10f41000a59070b8091540400b003840a0f2032110903801c2d000400c51100156415003034802001e16022540e1a44000d443c1a00e54480a00c0049500d0500c15101400742c581070307490714030319a0b40791585d1000d600907003c21980181c50220010315074500f000720780c4c010b072500000752a2040440c06403060214090b8489410b01e801880341e081001c03404111107070b2005040d90780c0e568442d113901d401401d61113280c100301003d0200388144030103207615a0081182090090001100480ca440280c1803480c401e42c109005034030030400a015541700c0e030004114a032003d004c0740c10840d00c81e80003508003006500a0b500581c004507020000b0010740c00054020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 2333281 1250 2332031 2332049
    0x4020f0903010c021b01030c0203090303030709050a0602010605090c0a0509090702010e100b0901060f021f0504030306060201050412050f0d02040305010203070216060c020103020304110303030405070f05040209130e0705030a1506 100
    0x81c0c2c810103802d20303901c002d0300c05e8181450341d940ca40b0448680248100c5000190040903203990b4903015001070058a0280107141c003800320108003150960051045100343e800061038070b040c43e5a580000045071380544c03084010000180405515511103590150060301c850b00003181042c06400c159107001540305860840b9070808120303d0442d00e5020318503042d16518907148280e00d42c0514260724106036000c0d82d003c031441340700d1850b500000560181d4041c0b8825074051100740e60700c0e0000c03400ea5200355409000845650220580c5a00400040c83c003845a014043d08002900117408200e0708207505c03d81d1140d400004102189034103001a44046001c4000810068100100204450b0002c80001e06266000002c9400d2001200300c0c03811400e0010200e80d0317a0f01c0e092400c1900e8107050710130a120505402c0011a252810307000362507956502a124000690242058201030b01204030003c846002d4032402041a4a05102c01c811090094900e65041d6004218810844030a94071014007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 2334531 1250 2333281 2333293
    0x120a140d05040f03140c09070201050702060c040605030a090201030b03120414060a0503070807050702090103120201060609080307020105090a03020402030408040e060607020d0303020d0608070f08010f0207030203041a040504020f0903010c02 105
    0x560101d44003c1003503d4001c0d00008900b001d01c0412481c00120742030b1703203a02200d080d0820140720381c1500000d03c10b8a246c0e0a8501c20707121030811460170f0140d80514801b048044c4006001044103a01200b20729005260104a2504410100717041a00b1101510401d00c00020280844035141090b0801e0303034420781c0c1d910b103070035040580209240030241010b005c002e004804a1242417089050f2192190001c15a544650752460b00b400d0214800b450311015500b820000122a0300404200040380c601002941c82e1010981c01110b141d070105800d00c2e484035070000c0100240c0c0326840070b140b10b01e00c22070351a80d8607410091038145100004046a1168004004100c01a12405510941300354141400b581300d50580b170340040038090b40c1c1c00c0600140b1468600203400721241180d40c04807803140d00204031480c21101d1607002d1340318562014016a03c20842044441d80c4400002c00901e08400780744d00f416200e20001c0c0907a0f000c01d00a40800d8070120303500c1c8240c80d0a216103140d03100c8500007465 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 2335781 1250 2334531 2334539
    0xb030f03090a12060608010606030605010f0305070806010c0213140403110606010215090316030201050601030c020f0304030803070908030a0e0a0e0402010c06050a090b090a050601050108041a06120a140d0504 91
    0x14141c0180c0c0914459032450140040402c0705540005e8050320380d1800030b00216031150401001001244101400200300c00d54100c80d0a010788079060090009640d800c000d0b913590303001526880c6c0d003810200c0e04801408182c0302c01000c075100e042902840335410001c80d01700741c200208100355003070103007100383c0012050040c0e0342e800080a4055006d494040840c6640d1000f2440c1180504204008031076615035080d130404d541036202a201c4d40e0242c8080191550790001240d5860301c0042204650740104401d002007090f030001755902903441d28208003216111803c050840d00498006000300f126a18401500e207440107400c2c0140800151440c0359180580009210507042c0b071010300850f80d503c1c0400c448098907040140c01681000d10b0500600f441600ca654481401409599034001e500010600d9849000c0301e0340074542001d503020308841c0e54000c1c04200c940c05002c0d0f50303101e15083e44d401885041407000821440c0500010070b1208007640c45a8200032950300c2940420604103c144 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 2337031 1250 2335781 2335789
    0x3030a02070e04020a0b07050604030809010902090a09060e121215030d0c0204020f040f0503010507030203090307060b030a0b010b0309060c090109060e06090405040f050706020303070e01110a020907030b030f0309 93
    0x508550310201c4860b220303115030010800f00811a004840c0c240380006402c400e00500094450199100360349025881c0c0c0c501690303d01b00e0300d4401d0000e41c812001d9000c00c0c120f02094000c0f10125004100008060201644070f500e0448000d80e801d2061102251f200344c415407100e50395038000c00d0320204000b00e0300c502000a8035240038040d28410b0203445481e1034150744541d419180c802107040d8110795a50348421480150070301d01e2084610a60900000449035880b074002d403401442031100071410200303181d0326440a804030200e2141c03d4450740c80040041400c0c2e0001c6c9001704030740e0040da40d680c14007c05003030508100500040d0901c004104501550364080c0b80c02c811194030740742c086011200341c400a1468840e0004175a80301d4109010300c000d0201c040792000c41c2c01d124030f0454002554865080e41c880c041298450b01080302450b94081d13a500038000b0001c071500580c20b9078a0842c09034001004c0110070740e450b03000290b80d440141c900b4201003200c0460f5407044002141040718000000f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 2338137 1106 2337031 2337043
    0x608010e0a0302060112140a08091201050105090105040f0e0a060c12050403050d020c03070b0903030106090608010821040b04080c0103060e130303020c030c0303010f0e010503030a02 80
    0x681002003000030030650a076031640103040c50741e103004209405030005034030030b899200c0155071105102d072060100c102003d1245d00e40503142c0000c0c01c18829072403c04041030302c3c4c5a162078018441a6910400c907411a5011140410f9400e41c0000c0b80000d028807207881925032050900400400c20150084030713036920140d07607690011414070300f40310035030744240c0380135001c21010000d02c3c2100c1440e0f0010082a119802124500451a5100b0010004c200c0d50350f241034002100600180390712a08020007407100f0310f041d0b00b40307504040c411a01c40481c6041554400c01d001c10406807241e80c3c0c0103907401042d640c031101d03840d665100c50f03982c1c8a41c5d0005c00d05000a242a5010504260001702c943c003d00d04003554030380710083ca980c250000d611071140f00c02244018032800920500c204019806043c88455400946180c003503612018101078215502c0785e0010711452180380d0b8000b41c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 2158281 2338137 := by
  have h0 := BRFrame.cov_init 2158281
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2158281 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 2158281 ≤ n) (h2 : n < 2338137) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
