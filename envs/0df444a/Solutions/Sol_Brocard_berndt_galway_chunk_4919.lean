-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4919
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:09:31.614303+00:00
-- url     : https://prove2.me/submissions/313c2f0e-ad25-4a4d-9d44-a952569d8614

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 884532374 ≤ n < 884712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 884533624 1250 884532374 884532421
    0xc0114100e0124050d0902190503010606020312130f06060f0509061e010f0905090406140108060403090501230c1e1b04050631050105010306060c0f03050904060905 72
    0x43c84800c0d50703204188a0305162411540e5180d17401c1858010b01420407000c0e40c418080d9241c1080e402100d0707103103001c50f02c00350700900c1802e6032628182e80b40c3c050322110565164540c0006011580d40c001c00101240c454078a68403031080980f00c000c212182074018000c100c50140381840903192403150183c2c0031b4000c490002140c181d58050040307800d0b6089407103040c070029191102015014041100182401400c1c3c0c2e0349a190500340003000d49244411000c1183c0170030004111030b10081009072150380c2507152450201d00c2c0500466204190b404800e02d14020f0502011401c036605000b803625840f4040288051013031b4925001d03290410741c400000b00d6124040c1d0118481e8555901600780c002101d0014003507aa0801082c449042e01030000140d0445c40884500b036010204d0340c4112101d061420006607803107400540c01c41d9414080c1d0804180101846000101c00588100c0c0b164868038044d4200740c2c0720700208065400b15008400400d841d01304108000c6030544488080d103141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 884534874 1250 884533624 884533649
    0x80a110106050a0b071104060b0a0305040c09330e0c07020f03011a04090f061103011a03060d1506081207050c0604030f14030f03040c0521120c0114100e01 68
    0x180340c039103510345c0b0405000900c041910004080280e0b21039102d00000c0400d0300d0324650343c00c0341410060091004450455040d0340306580810206218450b141d8035004010b074a0540311200c5102c0100410280a0004180d2880314046052220702000a018030b6143d440c40b0703100d4140f8410801011880000e00d80242e140c80314aa004280c11460000caa4100780c2e0006081c3c51581050301030603440d010060261414841801c181040e0113006604a924441c50080355441d0254a4015480180d0b8440d62002c101030084d404211344481c000321001600c5800540d069072101d03024241107000700310070015038001c40c90310300b4840288018215410115019403400c1c1c2140d944140c81c6690000c040c001c10b45103e403969840e1000c108450052500302c40e81901ca2920740340040b0b40303a003240a102e00442035200303103160f0000c80000100785e00c0c00780c00203081030180c600e0304444140c20020b0079800ad076403988400140c0714001181305005000324440b4808442c113010403002240c506a0091849200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 884536124 1250 884534874 884534879
    0xc020f0303130206040302030105010e0f070f0503060906030a0215030a0605010207081c0212030a02032e0311010504090911100f090504021b0d02060106030e070311060313080a110106050a 82
    0x10003004807070b84601041e852841941480c004281103000d0394000030742642c81d100c00803404500940000d4031440305821044000d91300d0040881d101c6001c8440140070580500210790310b45000c19156500400c00740440d0010842da400094101c0c40c18402d80c442c1560000070b1000300b10240c00b03404d002c0e04e028001041c0070b2745401d40c0345aa880c0011800b078980410a05041c40312442848200d4030840074200180d124200081520000c3d441541c0c58050000071100c1301c030303800340c002d44241c001ca10503104240c03990b80355888114406810341c0c2500e041080401001c21411564466001da86014030340741c0b82c911400c0c1050010142020311b0b10b80900160600802c074456004040b001036400941e005600d41401c415a800740b21070291080d040d5000d1a220703007420540c0091418100d46040d40c0601606414040c01c0d600c0d041d180c00003620400b04042c0c0415541009401036402c400c90000720039610035540c42c0c509064005140788400504094003071120081c09007d908041c01080b181084000d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 884537374 1250 884536124 884536153
    0x2030610052808070b040602010b0a27021c0b030d05070b0a0c0203091003201314180103232d0c1c02040e0304031e1e14010c02 56
    0x56540038002c0d0341c0c0451403507031903801c0e6400d00c0b400107008100441d04003c0e00d40c2d851311416007003405a6001076281c0140c0c44c4e03852601d0701c020800c440b0f80e84503640c1d9a41c0001c0c10680303102d1640c4202a513480e000c004198045a0807486910b4070b40d00b61200050102031001014100384c240001c2ea02000b90a01140c00440e65002600c5d401c0030111900155070041d811080e4214040c20800d1503208a01043c00009182c1580001c00301d04080c0001085000444501151354040c0200c1402143d03802442400fa026070f941f2030924104004022484100c0140b01e00461901c00760400c079280a1110542a61880c610315110090b503960b80c05003000d10000c1e4501c3c3c604544000344400408081114a04002814000116280c0700501050701d80c40c40300c075008080811403130303040740107501d0004c900384012000701c1560166540403462407039280103802884483310140c00b058458015031080f40700300c4402540c001e241240b0892403d2130039200490341ca401c48407401701e0070040d900030950310074068 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 884538624 1250 884537374 884537389
    0x1309090b06060c071208030403120c0203092206090c0906080601080f040f0b0123030f19020a1715090102130312140f04080d0f0801120f1e0203061005 66
    0x80000d403205626611074000f454505200d0354401c1c55882000e0002c94140b00c01c0c0401544a00d019864106e03102c40c0c191000360403203003104640c100580051107141a0780c80d03d800e400c40d021654114174003801078148005811160561f1100603419a290400d028164001300c00500030045424103805603d04030340003904448005242c0341e400c40f004800101004584503c2181c026000f05811615607110b054000d400411000e81041c491105410440c02d40784c0000c0700900c916140003e0030700c910081d101c6040742081840e0032680103808040c04141c1c0c1c01c421022200a03080710f401000a410203007282d60040310043c24169050b4010420070f45151f46120301c80c02100e41c4410640603c041c142401c44442e903030901b04003501c03a000075000b0440c1d070b06400a08151099a1b003500c0710400741e0304c829541000c400452074082500c40d40100090421100d99660003405045250b0000c699507641032560540101111032040c3e40c46000d10540c10100070a0354425188440c00030072a00340b00014004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 884539874 1250 884538624 884538631
    0x3080306060906070609030903051905070b090109053102070807032a030815010201020a1710090507020607090f14090604020c0f0307120e0607080904140c1309090b 72
    0xc8400140744141034460030100c4d011a40c0207102003110106074503000703241c03074040d20017520203114015456669061501c9103000e260742c01002001c2c084e1038800b1400303054200300c5415042c000d03414400038003601c81c004000c0145259070380c4004c000ca6a40004407aa01d070a0140741242c1c0d1043c0600800911400111041c090305400d0041000194441c2c4407035031803a0b07032442d110700d400c4034829800305500440242d018211851004030080901b9004900b01c0c000d01c3d40d154001400c0c5002d14806420408000390400d070040c003012010f9885540c3c2000303554054072010b005a02c20320070002c0036a88910007801070321120174001e090314075001102005680001c42c00b48105458408500d0981c0c80e0b41c101c40b600c0c0d4581d4103403200c0402c410303015134503900f01e40400c0e00d406202c01072070200e0501c1201d0302d10624a000708544d0400300da035100c0c00c00036040b440445400c140d9a00c40c0020100780001511700c9110402042e6540e0307640218841445902e55100b522990700b807181810010f00d02e4509070785c2c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 884541124 1250 884539874 884539879
    0x906030b03010b0418050601051519110d05042405030c2113020102100e1906021e04060905060f0901111e16140306010e090c03010615031503080306 65
    0x2005250100024010883d0314070065001c1c1c50039401d0303d0304407558000c01052602071801d8a900b6030b41c60091006000c1083d04082032a04200004034a035240e6060218940b40b4510748151900716050790a850001c20724440300104001060130061850030030956410725040124000c1c404460982c041c00600016200c0900c91001044944001c12682c041400104c02706d89000759508101c0e180d0350f400068480268010302801303030844201c044a00603162688214401044442c0d0312007400802034200709c1c001c5030070503000c100500c841c000030191100004041c1c907040d0b40d070350701d81280a00302c0103050348410300800f0140554043c0c5409101030b100310050a00300341e4400c600c606481800c0090041441c0000c84000302080c1071584002641c0c64904030034001031107070a0702d49003000f018200314106030782e050344900c00500003021a1f0810329046028842140c0e18100c9000000b400c0d24103642100300800394125602201c5507250217104405039028a1940b851402d6890f034401c2c0f44401410303a070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 884542374 1250 884541124 884541131
    0x1110703140c03070902130e011a0717030f0906071701090504081603050918010e131103010c080a0c2c01211b030b0105071506170303040308090a03090603 68
    0x2a000607041c490903400c80c6008082c0e40d4043d480d0103a66009421000302c01c1700310105440041004420052094140c40d01500090070b440c2c0110b0320355295070b0020b0070844071441c0d0b84040200d25080c46000e54000d02c020070354541c2500e46031010070702d0b040c0020020401c002100700342c1002d01d00012103035415a0700807100410030ba81c0c0d40c00c00c8036003403081c0c0024034015411580300000341079001002e04030a41044640040d003e40d15203400c0805802802150b10008514000c2801c00c0200e04e841e1109510914410b5a5961060000703821284000b00c46800706100030304000001a0394030402d1007032a4182030038441076858800500110341d24505580c0103c3d0300382c101c45440c0e030240c0704401c443c040c40e00c0c2d9071800b14403451920020388501d202d45006850a444051340083c02400341c0204400182d5466043c404682c130f038441c10648520301c03801000c0c4e4540004c1035192101c10324445a00070036000f9940d070308140c43c00a10f4440000d011543c5500720308521030000ea4403a090b42c00f00c3e0524a00030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 884543624 1250 884542374 884542403
    0x9140c0a0c0f02030a0c1d01090903050d1e06090917070b0708070203120106120b0306060f0d060b130b0a080c010f050309012c160b0f0f120903130501110703 69
    0x10b441c01c5ca640e9000740c00d106000c00c00041142c2c904155501040d601d004d82c3c21142da80703010741002d5940d080b8008001c80c10500455004030666841240c44481c03107940395071000d07400300c044000c8928941210b021140c0700c842c2403083c00420003180c00046586481e007440c0c0151500e80010302d50015181d01f003080320200109140782d01c20030648a001c5410503403101c0302c0d40d50303001c0030340716209070410001c0da1403d0544d9964685030104a55101ea44050812100c0481748030030004c1c0c0d100946000c50721160703a000018203607200d01c00c0d1800c00f4003019500141c01c9803420300b0000780c2e003220b40c0181041d03881400003000c07e9a00206016118000341000d84c0c490b00d41c151524050500808200c8180c002c502c2010351107028028910800b100c00825a6036a859064959040711014000c0c0303404d501c410000c80f0388240040c4c00400780c1860b10030703800381850740703604a03c403044900307039816101030f400490500700c41c00c00c1a40c603400400090910090031030003a800203440f0061480054046c17101034108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 884544874 1250 884543624 884543629
    0x402060d0e1c03090c090e1b060c01020d060501080108030c101d0a1121030318030919050901061d090406231009050405120901170109140c0a0c0f02 65
    0x2c61005100c40410401040c906403002001420005400d880381d0354001c000051028047c0b089620344001e643c040c000300080807010400c4914980401038000301c0070004203036915001c0c409403000301902c040206109142c200010468941a00410311a400400c900a00c0090016506d02007482d1b40f80b0104e100c0154465050140c0041103522155005007c000c004020103180120b1200b4412610f02606021500c0908031810003400300e217426600030404103145084200707030395030b095070395104076413a00b910034020900720b4485c0c81c420821b40a00000500035807400440c110b02601841ca40190841060445182c200b040301d1603660098080748040360512000f5008056802e0b00304507260031028a803048a42d0050b070807503034800d0100d504280490300014502500380596003080050104c1c404500c020705499000d0f00400d8140000a55200310408501c0080c0e80201148000044c0325603a041101c0403c16004140441c800001c1241111031a0010125039866401c08121220481240f01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 884546124 1250 884544874 884544883
    0x304082e09020f061c1103060a030b0408041d0a180f080d06170f10091a070e03010603060e0d08040c091107060908070210050a120b1306090f060e0402060d0e 69
    0x403d030340c00c400c0000704104c054180165408820690120812205108121a1039a0f0009540070790f48000440010000f180601a01c1900140910403a519066940702c00400300004848409240115031080004020b09440b516148014000d48042d00d400303690760300062100038620042058001240c00f0344500003c0d4007440c0503100c58414000842100d010b425941c0140e605006030074883c120207a07600c40740500890b400c1d00d502c40e0102d00500d0811040f0030101c0c000505074020085e5900780d20303089903024062800210301034100000c9800315500c589082640400840b01031040c00c00c01c1c8000540d1100e0318070100c1300302e004000350b80361041c20002d50b0342c820b095000d40780b00c0c202000101440142d10003011014030071038100ca00c1d100f4007101610b19001d4040310304045039114400080403a003d80180099074802080f01d140f4003e400e06850440307500e41c11a808142c2d645c4a80c0720809500d02c02c41c00134041c01480a100ca1500d030340051014840d80b9565050591941500c3e0b804150420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 884547374 1250 884546124 884546149
    0x40504050a1e06090b030712020105071e0c030303060e190e121810021b0906300c040905071205071a07050705040209010e040b1507050304082e0902 65
    0x8082c034200d04000d08000050200c5024495015281040803040344ca800180641100c050f0140340725001aa5001510390b600039030030036100050303c2410600710102c1c0810f040381c5c5030302c101d0503114402d0450500404507841600101c035690300140a1040703c082c4100c01542d50400031001080710b20303000c242c076420215010314913440d0400105502505160486106079a40d005407580840b1a10040c012650f42c1c020046288440d4100803060341c00f0300709200203591012000d000d45a00001414406910b81150f0b001350381e0700e80c00e07400715261010307050200d50002841120240503030101503c0d4561a06d02d107115509242d00c04103040820000300b401002d00428268002c20581e010413002c0503c0341d44466000c8400d03011b9284d021419103414030903074080c0f06040c2c6d03804800098800600c0300031f20150903081d901c1651160030340c02950910004215192141c0090342d01c0303500e0000114a0704070200e06011070103400c0c450895400105070741d500d03251406020f01003800034a60000c1850031400c04e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 884548624 1250 884547374 884547401
    0x91f090624050310033002030d0c02280c050303071b0902071502030a06031e0c0e0c0f25321b01211e0e03040504050a 52
    0x1540c000303104040303038506a42488004040d465240c5424804807031034401140c4a111107804075005001003554001c40030700c0300c42440a8002c3c0c03081941d9048020f850903910300c0c0010b81c00040d07000700d441524041c0c0d4510041c3da0004144c200e001460000f014002e035a008460f032000c0d11381c00000c2c4030800c06000f0040601500381c035614003031820440601c071144601e0030042c040031300300010038a07000c3c8215011903030001d000f0303a5103030408401c01020b980081d001c150400d45031000403010901e05414802c00c483c2400d00e03e001c050246c41c20318200301540e0f202c252070030b000d23908003c10000040d049400c0c0d804240d40391941c48103035200003014100707900c1d900400343c0c442880c0203040140e0180343c01c04e583d580101c107880c05200c15190236107619401310000340307503000444100c0d03135240b441400c00000d030b805042000c41040c46032501008440c02d0646641c0450b00c0c1e03003500c4548601180302c00089025007000f808200e1550680650300d02c2248151350060b0380d900c0028000203250360091041a074072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 884549874 1250 884548624 884548631
    0x2250506011418130b090c0102190201050d05010603020309070b0903030d0917134509060504061a06070812060f031c0f030b010801051003020f0a020d0e010806091f09 73
    0x769100c2131003400b11070720440c0e050700402d010402860000a042041c0707a416401440840e8101130043c114401208049060000a10910801a20318050a4060079007664016203d01e80740b001c0b6031030310300301c0d905c001e421a43c100981e14076a1008021109100110840400c000b001c41c5000c40c1541c0192501d244180303400b042071640300306807030420000c0b1049100d0840345112030302104145d640644070f203039030a40c00c1c40c0c031203410a04c22209940c04800c0304860000b000c546c141c0721302c070070707103900320b4044580a41e2080340ca140d48050400f0000040001e88400e030801e4100d648a1191707119510009040306120b40014805564030902d0325003001000d016911881c005440f02038650400000001c0070400324011100c0051091080885000059403210480c4c9d00e07200a00204001681c040c608040d020824610007020400003000c9200c3e4a9008280c40340510380c0082407405044034060400c0b404c002401141e980300c018082d0071003100c034001c50ba2031040c80d440641081040d4001b0031030900b07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 884551124 1250 884549874 884549881
    0x1230f120a05091e0307020904140109060f1419051b0a03020a17070c061e180308070504030b0a0b01021c020c091f17031c02250506011418 61
    0x1e410907802843d040c0c0c1211140035014081483c040c00b08524030215900c2440080007629009140c91740160141020307030002e40e0020740403402d41d228120306a038001c3e00d880350b032001c011043c45002e040800c0303003086000c503080c000e07641c11140e120100c12140e80c5071504e01140c01c480e050421039080450108207181d48102d10440038010b0b4100013a640042140c0036610011003084660b11391090340c15940b0850507017025038948009104105078030284d01381c00b0812420f0741d00b041c40b6050ad1400b8250340400d10b2105460001c0010900900380310030400280420400901c1200aa0707811080000700480d1500740c0c1c000403482c001c051400709442c4072041c80300340d100ca0f8010404181000f0b00307580302c0481d40d55125030b40481000c1c50b5030450407403880c0300d000c1107a206502c914945107a142001ea034941240c2c10030b01000c5034412070034420030660000d050310600710070b11100d50600c0d40382c00c1c0b0051014190b440b6240c0701c80b01481003214440c440113074102e031562400c5444d40e10000f007164424003401c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 884552374 1250 884551124 884551141
    0x100903090e0603010605010819060305030f03100b04030f110112050a02031918120219080316030911060a030e0a0f050f030c0a110d0b071d01230f12 65
    0x25814411036080c040e8540220b251030030b041c01070748192041a1244941901e420040d4010b2104c28008603144503601c003000b000240c0240b00030016440803007400c0791681000500d058051b8225403184d40134030341c10401000014207043d5440c1d00c0703e802c00e0390009042408801a60b650b120303038021901640c5050b0420074a041c50358091405440e030200344003400e82c07a0040c004101c8084075856011444c00090301c40001c0d1080b24030840d030306807601c10b0720b91140c0306d160011440040766030101c03410400402004461595183c44410488d42e40c5814070250b001510364861000d441c2d03100c24003c2074001921903600740223810403120000300b5400c076020800c0c83d05000d581d82250f60030488050044001c1c0c3e2010542c00810344070311911038000f40c00c4041c43c235038400c100136110841582e001510354402e0b81c041884042e00e00d10070700054440c0e645400300b80c261000b04203c802511414824951442c00200e14050101903182c0565050700e039403051504038010300c0b03000300c0c1d5481002e121808104000c2c2c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 884553624 1250 884552374 884552387
    0x60108060c0d18060e010b0415091517070816060f2703050102220503070605030717010905061306061b02120d1706031b0636130e0d0f02100903 63
    0x102c404002c1008047c08002c100076504400c082c00040c0d035041c102072001c18895809000c03009100c80200c2912641d80048070040c406d400011185a0802c90003000700704420301c13010ad1030051800c031142d80349080a4001e03000c83d101ca103880d8208008c048168420140e9003551448000c030503a00580d47c00d07900d242c40e40c042d40c80400c52001d1801800b00401d0700411181e001d4090301e100502800000e418060110f5103504000c0032602009184a01030f02845c031400c1081c0e01904000328085080d2514500344a80b102c10801e0169000d880c1800801c05258044012219031510b0318240e00c840c1841c0c000621400c08803040c951180c0543c3e1b03010300203e034210800e070465000c0840001341c95540c0000b0141c0380d10384000c2c00e044c00951202100c0c0c0c0d61074400d00500703200300700382200c4041407911052480461804107400d0b0700e0044103c490b034000e142c251801421000e0407001405405020680651a0781c0f80751100300a101024550f000729500074043d4080703035034017104200400500c904005084 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 884554874 1250 884553624 884553641
    0x40308180303130309080105071707020a150207050d0c1104150e010605040e070f0206060409080c0f0c1306030f0b06030a061b0f111b0f2709060108060c0d1806 70
    0x100d40c0d070500000d20b010060113280c1c0b00720200d03150301105840c00110042e4002b4024116800c6010f011550f8001481041d10361803000c00c4900016101d605520300075140010350a691001d0203605103400000a03a854404407050700191000700740415062903450500209030440150132020398000b00b103065001000d003003103070200d50306004591900c55040e9880801100c40b0b00050f08a0000901c0b94281030300a421810f2107400d1407450306400c0f01d0844d040100c9824041560b40040508038103e182c13044080c2c0d20340e058400c00b008854516a03503405407400400d001040c0d020610002180390b581440f03150b4101e904003c080c054040f003038480b500307a0311105402901107000090000013681c403903a61503c0a8108500030f00700781000f4900c01c2582d4580c00303407455208010035030815554484051148410a0250b2150b402c995850468211000f00509440159001c0001001402c1c40007070b1aa80001c003000645940d0200311003904007030084400c03601740e00c81c0c0d00d111050821107513a21a406 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 884556124 1250 884554874 884554877
    0x9040b0a0c111e2e05151f080615030a050903160b0601120603121805030106081b040510032021010510082a032a0102030a080403081803031303 63
    0xc401604400344c0a40c02c4442480000301054020302d90b4040c03240754055070300140328040079540807107408001041c503204c3c1c681114000c80c020419409580c0c000640c81c2e00301004855420b00d0032660745180125002c02400c00546c1034503003020404020041c0100c07458044000100e02800359507050588104106a80040c0080c140d80344a80340c07000c0710302c1000e00f44d036400b944010110070311550441d0712402000241c002c4100344140003441e540c09215200c001c049802c007406900c41c055807140c4a0740c8608414500480c2840c0812408940b00420310059a912551400001440c40649050540081225500001c124200300c0081e00c90a13a130200d40400100288003ea0340e41851101418075803084940c03030b6000308a1112a02101c0045100c4110441803c0e07902910031030019203440c0501000041409240340d5a0b121001605c03992070b0407100c2800210310300b55160600503d03844d0001d0000e000c004802000c103014142c0b019492010304d000d181125240e0810803007034101000398160850 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 884557374 1250 884556124 884556133
    0xa0302041d06090102090d060504150501090e1002091f1812110d0c1202030a1a0613020a09050607020f0301060602030901030606020a020609100210050103030e040b09040b0a0c111e 79
    0x16610310741402141c0c5c0e2900c002d4488887c80c80241d07180b00203450301810482d0354103039140784126507150078810305000740148c100c08507a480380300d2501400d000307045012140c014010000582d0b1070700d5660443c038034101c040701032000305444484202c40d50364030790107416202c402c41c2c2e80010303070380f410200c8084020340101702e01d10429600408102c1141c040d01c0c0018005e84821604000803100c3c0c00c401b140803800641030742e00c1c8502070f903503200e034011581d104084c441c40c14000b88031060501c0e0f5040078404840c604c0440c98909648000303401c0f100302c6d1240f0fa12807030780002d030901151903a02005600d007801a000740511900c60801a459400c500b0043c1c3c0002d1500e00c0c005003487c800901d1011042d0054640e0b80342000100510411a5040b0f0318401035110b001802000d010451160038029800780c0c0e100358003036a4500400c030954204000c0c0c00d200711441010301c0082403c80e50865001644000e000401041c81f000565041110440ca03404074051400c28211000020030400d405c1000340083e00e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 884558624 1250 884557374 884557381
    0xa210303230103060c022d060702240711011401051c0c03080903160f06030c11062701020a050909010503060c180f0a1d010501020f1b0a0302041d06 65
    0x400031424281141d860781402074010404108194410702207040103106881c43c10606041e450300039441d1b02681d01f00c00500a140080410003844016040b642d20f1014080000f00d640441c441c0f140e4102100c0001c01900300801c0d501405000c0000540113400f009126441a003069015207241c2446098010420b001d03c1e2820312828245858049a0084e4801032071030441e01c0d16021500300c01c0c800b40c0c1500c1440344a031854690311007502e004103812640c0c801844c0c10f0074401010f5446c1ca4025a00740810100060348043c8003048169210440c3d00074401e031100d140c080a520561451400d5459510001c0c207080314030740c05001407803255030075101c842036a640c40061581e640012150144130503c140124000b680104014a0040d240204207040d500da101c0300140401b0786641c010400400300819622059580c0c08007240104804d002400602003010720580e01c582071076000300700314580e81c01020010b0350341903104000795030081d204204030b54540d80c111240c0c000c0180c140c0c46910402001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 884559874 1250 884558624 884558651
    0x30c03050702070b12040c0b040810150e07110109080408030714030a0c02060c010e06150405070e10050703031401090c080112030e1512040507050a050901050604060e0a210303 77
    0xf142c2226044c5501c107103442c0400d82400c0c030300b88000d4801c8881103d81e6200182c0000c0b42e901a0002e0304690010b03001c0800076031031284c126001c0310040d00040d01c09203401c01240d403031009095407041081c2007215654480d58001030041c001210010000b12022401241d00c0c5000005001181d02c64990360305855500300b40640d5900034043e01900140450904400600788900034080c4448604000700701840d250100718100030b003c072900d400006009a10002529050003400c0e0085d645003010252a90b017480410144c40301180020309000c000543d60082611951140d5002c0024144110b071313a5858054440141c03802500900000d1016400410700414040c2c4c02502d0320f81c1a10f0b1034000d65624010b0141480580040302c00b454020f00446c5115103110121600c5148a18042c00032541003404220060306a0340101d40281c90303c40040c01f81d80c0b113400c100d8003542d41506169520610750000140011910f42004c000d01c1e050980c0c1070b0040d104c654040c0080b03407082e1001d0140d40c480d5901c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 884561124 1250 884559874 884559883
    0x30706050c0c01030207050f010e0a0b0c0a0801051504030c030c032a05240d09021903050a0209060f0a230105070f062013082119120c030c03050702 65
    0x29100200d401884280b20030b5030003035005140d0680705100f034801200026104c107003164103000c440021500700581080800c00340900b841e902480c03032403d1a040c20300495006042c0c41050142c0d9001c0d00f01c1004510080d40c118042e10029a4030851083d1501e80340e107452159000d45103c1112020302c40e40700840c0140c80070000d0483d03542110340e8940c203280340408000001d51018050704250400d000c529245e034100784000c00c4424179103240400d00007003502c18131052640c900d00c0c83c9084030450341e041c400543d01083d1803403003940444014406031074074800680040401c140c040c0d800f50600300c0010761400c0c1c0352081c10011040d03c25001203030103160015070f15481554801080c800c000c00d03583d00000d920f5408110030044111117031f09004e40d28560750041c0e5010700d548100d85819090100401c0c00200280d6401c031044513240d800c11000000890180e00a00483c0c105090050041e0240da922400302c0051143e8806018010302000850103001480c600c80b081e00064103000005581070700006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 884562374 1250 884561124 884561137
    0x804050613020105040f0801020a0e0108102d03140c090708040f1a0c070203060a020a1b150203042d0b01062001090503120a181e1401050603070605 65
    0x806041103940700a80403a0341e280c204000ca040c81000c0c0302c00300308100c032170003504040c6c20305034001030b603402d0208005080382c01140310050400082c0c0081040e00e0070803081d00c4044034003080c04411030803152940185c4a0302c0c612240c4e510183c407914004207001c2c002910101585004c0180c80c2018182800d00c01103440c110303549804540c08034041400a90445100c40340c0900400400d0540800a00503100324401a84c500304100320225010301585400c0c4895078100509900851401d001c44402800720754075052441c031000e810b40c210380d040c42551600c44100c0100080215900d181034a0051020030314058034911141d800364440c1c2c02c007003061601c0c40000303820551400d050b030310740142298600050303052414802c2c007100c400c804c0701409001d0781d40480d02c0f40000d5621203a407007901150b071080040107810034a05240300c00c01c1407a40b81c0d140c01c60580c1c1000d071310001141441200c48800c411144018200b2100c08105c12034440198451800341c1c0c1c0850035600d047d9a00c0030704448038060314 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 884563624 1250 884562374 884562383
    0x609080706021f1401081f021305060f040803030103060912170610020f06040b0a0c0f0e090a090206070f0c14010818070302100215100305060f0a06150c02040b010804 73
    0x108954545103542140700c0201c00155020800c44c2001c20303041a440c0c4d080c1d00c00c0200c4c4d48807190281074184000b5000c15000da40b8a0304509142d85d4401301d00007600c20744251800b94800080d90703a4a6074841c021030700a013042e0011640d40303594a25142c1c005000f5440151600c00061403d01d224511a884203000e400348100c6042542d02c403101001502c40da01e074020025413040e1a501e5450400600040d0300c44d60285440c441145826400c00f400e48002e13110203010803084e1858009025080040081707001425540381034503546140001005090341d040295000d000410508204001841104000f5100340310301d00705aa51030030702d1901403080c0c02526010a042c40700042c00030341c1c7e080e800000c0c80341c3c0d24210340c4825601d0f0042010014040c03135503801a00001c0304c0440d000a10650310f034200039004040e0b02c0c494550384503952074440203402e5800741004480821100320309500302c0700c0074042134140502400c0100d100a0240e80000500f01d01607420b02c13407403510a60281c10354a1055800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 884564874 1250 884563624 884563633
    0x4060b040b210f010905061e04030207173a080112060905031e22030b0c13030c0f0f0518010317070501022b06080c01030b0a0b030403020304060908070602 68
    0x1010003101c1c0700b000300305400d43d00c603c64101070201024000d0102403400f8901400550030300c00352404204503018009207803545540c00b40000691300040050840310307014071f8008140201e403982d13420010034583d42c800d01c000030400c105c100da00b03002d41d825100510624802c620643c13182d041c1d0709414244107528024810040100200f00e982c0c101c10300052250042c0c900d80348545200030040b40c00f081c0c0300e0104010203e60340400c600c0c3e02c85e0303460358a07558800f500122851903070390245c80440102810038007100070034006800352020b00c2010103941e003c10340030070700c5031100340f1440d443c0c0310343c402c0c00f10703035081d4050010710740c01e100c2d00c41c0d84c1c0c46041c2c0c50400002c1e800d40e00c4031464005a180b050f444030400304100d8010030000c2c40504502c04182d400b6821185954800248100c640c0c240140c2c2c4a10f03000c000c00080c00c001070550840c10080c03c010039484005000900310040315401604070481c004200003c00d98044000c0c401d6802985076456141d454114050343d0720024012600035030b01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 884566124 1250 884564874 884564899
    0xb16080d0c08010602010c081519030204020703031e0203060915010c0c0603020a0e0f0a031b0b0316030f0c020709051f0e0604180503040b0f0c03160308070e010206060906030f1504060b040b 83
    0x18a0b5120010500c0d0014440100c2b940e0791f40403404990155505400180d0707503001030307100003203520225518803600c05030550440c1007020008500d40c9014003240c03118842a5200d40b6a64010700030030f1541034200d14800d0441d0b40e9000d000d4080e500140000002550100d24850341d413400250f04903c0c4400680216000303030440d515400030030f660880c6550f80c4007107220002040700a04005510544601c0312141c1e001514500c0502558a004110311445003080822148a41d000072074400702c03602034001040320344450498422147d1035401c0400618201080032450f800e030116528041d03103059408020002031000000c095030781c1000001c1194000700005c001420401c00604100465140c04520b0039100000240c955403214003071003210311200003908181500810354503400881030411307120324144031000075210b041c010a42c6102e80000d00c082503c54a04018018809c0d058000f241e81d984010400c0d507907098400c0702c08880081c145904803117036040c14061a01e407008007404c6c00c049001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 884567374 1250 884566124 884566129
    0x1140f0a090b0310050316050d020f13020d09050d020601060206042d0b0603070e1611010905011d070b070305030a05040312050112060b0a0b16080d0c08010602010c0815 74
    0x184122100010008007000100b5140e102c00300840c01000700500c2003051034078000c00d140c00e1500d02524043c880400030310070462902d5141c01c000c0708a5046841d80c2d0005200310000340c1e0004442c1501c0c60647c8041007510400031243d110044140c000c000310781c060107035120120b80d1034200f4080d410042c0c100350042000108040381001504d0014a1160840044400399401c01201c99002799544001c210900103941418040140030300f50006018281d45803041b0940503d100d80711a840410100e00031114074080c080d40f00c3e2170003c2e07104c0004d1100c80c41081020314600345101c0b14220074050710400080c449400c4040311001a4980c441c181940e544035540d000030900104164140301400000f0802d82e02d90388100b5020740100c002108000501e410302c1d4088503000650103009440e000002c2c8100c0c466182134410360f44d1440b0040d982c0040600c4c0030710280c0240c540200440d8203101c41100f08035000212039040e05c000750700800404900400403110880b059803124043e0f80144204800390 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 884568624 1250 884567374 884567377
    0x50f060304050a1e080d0218030109031b06090804121403070309030b090f0a080a0f0507151e0507020a0201031a010c1106071506170609060708060a150314010501140f 73
    0x40d01604c1460f1007035215840300000b50f844160250002c0340e002540341e0086e1070421110f006800e0a9008100d114401d0750040c00c2c004200c41c0030103920900022060402c025a04445c0d803480c0c0c000354941e140e660300c01c041c070446803020b5007c882c0340045904960032942d0000c190303202c42c0d4040d039481c1902803441e01d0f641e20318200a0490406c600508041010100e410060345042c03d12071040d1a40d1841da004006000701300640780041080400c0196001107190721204003d050030351100040d0250038602140101c1d544405000300c3d0500b003004201e0703103a8010441d228213034000e8a09000860140341070040182c201460700340030500e280d800c3c5003c0380404c00320801b8400e01400540c07038445203407159510711840307810848009441d8042440741180c1d41c2000c1c0d000301c5008000340010304208103d030b03441e03100041038641045030b400b000425683d112180e14005084120741d0300d0160a0002c00240504041c40301c00101d03403611400000c11303521a144152600c3c1034003106505000300e0301004001d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 884569874 1250 884568624 884568653
    0x308040f0314120106020f0304030c090e0f1603020a1d13080c100e0d030e060a020f0f030103152412050106080d050a022b05090111070906050f060304050a 68
    0x2040786424580382e20714103540007400b1410020700c9840403913143c004d0080c0b03805420107440b2410b40080c0000c0001400403c81c00081c2d0740d6100000c0b0f11040c2101c3c0e001e15003800c00d20b038040d242c1310311801c03403440d034290008200540307000b0788940e410551540e2100c0701903080d150006060100b55800640e003000c03c0100042254407074000b06140101a4010343d240c504612196015180d0741d041b00442190108000345011302c4600f010700050740403510709070b142e140007010b003100d458001841d412500c01040c00c8542c1c440c502a0380c29200d584074100b29082d40d100316070086400d803038519075444400400a04810f484003042d401c3e01031505000b417421106007801421200742d0748981c40440c4016050021144003190741e56000d0311041d02c0800245031500f604038210320121a000d220704903920130703291a0100101c03800c00346ea64203e031800403201c50f1030705001070b0980e019100001c41d00d8801a0418011540e040f1000140302c0e120104004007031000b2356001700b05900c0284184002285030b28100e40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 884571124 1250 884569874 884569877
    0x21503090c0910080105160203090d03090302040504030f030c1e0e12010212040201021603020108221b08010c090e01090e0f0106180e01050402030a020105030901110f0702010e0d0308040f03 83
    0x240380c1116001c01e0745074030141c0782041d10043c0a01e0a200c1c42d4801d1040e26840321407451109541a40d51402075268807840504502030700d440a003039400e041c0030311a001c000b194050400c0015141c90b0600400003001440b034030000030b052405a85600e8881c600c05190384115000f40440858a03410989180d52860401a00a1038020002240801c00e1000d07100210340c5101510461038140300081c10031208401c04400380001460500141c5d9120a840d80e101c442c034080f00c60b01c50f5108411188914039007000804020300031740c83e082012416801d080c11511031400900488241d0365098682d00c0d02070003034508107840c41703004000411050b00000d081a95042c15141c0c1d1a0203000081e0954225070800a68549954103070300c04099544280c402200f9540000c000600340307603000179181c0980220280c100304001c808120140d20079402030b0344401d2580c0301aa0385a0a80340c05142c5a000484203a0128450a003000081e0501244c2468000d40c90f80c1d860805990b941e45065160035040d4080d030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 884572374 1250 884571124 884571133
    0x2040b010239041112071b020105030c0c0a03030b0111030f0d050a02040f0605041d0705120411041d06180a0f0602040e011d160f05220608040308060d02150309 70
    0x81c1d40b214400c02505a035010300460341d41c2605103402c0c68a0750040c01d1402080108281003c550011200e647d044941c2442e00d00c0c0d170394580700660900c5001e0701540703c40c07038050034003a030303042540640c01031101e904280c1f106070642d541d0620030b9031070b4001d08168103802641008410401c90440e1700c807541c4042644001410151624031161444006410a90110308000780622040010440910410403c40102034003464600c000a2450180070008040040b00b000441c0c200012040c00880c2003401920400840c0001c14502c034450302d0b03a035100b1159000d0302000c1103451440d806065000d9415030010200254543d8800b4030310685940103a071030a5080c0b00216841c3c4590280d82d000f4004404085181c40824500030075804003e813074075164011880c40900c0d80754102d03100401c40415420300a8860994600c3e02081c49071f410200020100110000f03e90190803061050103940640d45d103004907941ca4080c00701c09911484c1c00303588040709810074844402031100039a4410404410f41e0b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 884573624 1250 884572374 884572483
    0x3070f05160b1b0a08090418150c030f0207030906120207050115090b010309111905420f0d02091002070518040c030206070c0e0403030902040b0102 65
    0x74440060036800507405900001000032420160080c245001204030001e0100c061880c0d407550103d10400001c02d00540d250f03441801d40311042e00b0140145500004a000740710301c03c004440040881e00c04000101c0d140c8070182d0700c01d800510a079840d40ea4143c640d281e0322820080d00352001800d805100c22120b40030091680000c3c8207000d13009800c002480019042800c02c0315403c192003401c0007890400d868000d00001180307964140403031400741036603024400f40d42c4400d6104000c2268014a40000041000c0282c0c80041c5c1a00c0c600c81c4407540c01d4034458080c594030139221102284040200c07400070b0001a01c0000c20320700034480c03540c0d0050018540b518200114544902e20744107000907803c8980100558200754505c0b40c195812080d00e07807680d103030540c0c0f00c049000c000d001c080e00440002c65224204240d13800c08001030501690f912129140c2441c0040141515041c128001c41c104030380381030340d5400042d1804080c8120703941c100f50850070858091840e6015014540740340400140e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 884574874 1250 884573624 884573653
    0x5010c02010501032102060c090f1215010510050702010302090109091401060f140426030418060608011d0a0b2d01050a0906030504031808030d05090c010203070f05 72
    0x112504980950008a040d614600b061320002203000440c980c10108000d00c5c902d41940071440c158000292100c2589840e821070100300703008818010304e07400c01e100c039008001c11140060075180d40910b81d19807008503070321032050294400c1e20b2107503000400c07401e104001c011741c042d402400703500c603042c03512410941e601d00d00c40040e25200001c003d04942058018400c041d80700e0130b107008a81507420403441c0c03920071030940e904511030b40c400c0000c51140164031210301c1c1c980e070280300406003201c401c5036115510b0b60300900003043c0061010b007081e4940b4500040e4580213001550480e42d924050940d8400307200b2080c0315810b0028a100245540e809016440d5901c001c0000240d404032610b80d40d8000c010110502580300d1000254140035040c0106a041e0758440015402e0b0f03403061402180070307100d81c60305a540c10015000e070803418a600350040f82d01700700003010709620090010207028648860f1001034803085603000b00c90058000300551000b0490910380070106a100d6005c03900c050b42200c92 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 884576124 1250 884574874 884574881
    0x14041b080a021903050601110f0a0305070501060b030f01090e0606090f060d0212010e070801060b04031202031c02070b0f0705041505120708061005040b0315220f06120812060d0501 79
    0x70f41c00469070350418040c965078800c8090025003506002890340f071040000099039040c4801008080110000306281002400e4010788001d0005000c078541360704101c1540c1c05194001d000f0b11104900d4154001729281e80090b00b00e014940c0a0003010701c586601a202e18140300040456402a4a0052460068480f9042c004c00040ca0307400002d80c0d01304603201c46003800034070352100c2c0a41e070500318203201c00c0c41444120380c01c8992011401142d5054284143d0450040c144440d82d08400340352414040c44140e00204045445400a50140d580e174124810f031104041e1800c1c1d000072000d210900031005200c18440c91602d050811314103200c80d81c112075410260441c1ea4000044408050201343d0a18010800c0e10f06da107820940d00b028180300b4195145d01008001c403001d140030421610440d250780a426081440c04c81203400e40d40500d0610f040600100d0b501c0c00f41840c500500020301048501c9900d40342d50340202e00d20704d42a400e082c581d0600c0405004c2a902024071059000001c04c01d11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 884577374 1250 884576124 884576167
    0xc0b070210060801091707020d050105090601170313271812020615100c080309070e07020a11040218121507050306030613080f1314041b080a02 63
    0xd00a241c0358080400107000c2c2c8450342c2c03000d00e1aa06101040c00041c103100351801d28100502d813a40e8542ea42800012140000040c02818651904003801014040441c961b030680f00300b810550b01407880c0d601000c0c1c1c1d84c401d181b40600c28060b1544103110380002c250701141000042240340c10621684100c010844042624114081654070700c0b050400100540031b10421405001030251882c140280320750180a051034a031040032503211100300031b0301940001101a8000270310340e840f032400194544d80d40c041402200d05132568200007824152000902d9039030701d64441504050019180c06001c00303500b1441000045101d01e11142d0740e981c5401c1240ea210140071401000c1c42c1c50320740c100007030402c005031102c403c000d01001003100d1a1030024442c0c0e00810004c3e8203101042070350800f4441030040601a071400d250004581c4018028800e68400313550385854200341d84540703241008125008824903100c00000c2c2007034680e000d409000d103964400d80aa401603d042442c1058660a20303951 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 884578624 1250 884577374 884577377
    0xd0b06150f0c1902030d0e030106090204030515060f03070b031005030d050d1b0c0b04050f030d06050a080c01141c0c051c0b030304090b060f03040303050717040b0a0c0c0b07 76
    0x210b0200c554442c208204070108141c2c0c01c0c01140c400d11500071a803149245c24a41013030000e03285442119880035400b0f00c0090006a40840d01c6903201c5c80c001d6125484805802440422079011035118549041030f10441c1c40000c009089580c540303140440140c0008011703804403ca154800141d648080c40244400c0b1540da586d90350303034602a100d0904a824a00c600c1c1113150381e9440981c0c005c0d4128031002d41003070700300510041c0ca60f643c0c036100d80741400141442032103000102e07000c125400107400c583c0a4a1045641500040c3c86001150703403541c0000c203290008602d0300c03241e0046040c01c0010b103c1136440351030300108070b06400243e0301a034a1508255000680001b21344c0d2008150390300c000113210349203200b448000d1100b000a40e9034001d034050014900e03030f9410040119550242120900d1040489051716072a00c0c2c1000350040000701c8802000caa14013820130840355a007080301e4843c1da4003c4141c3d0326070b101e410341d40006001c0e2a00d400300388204502064045000200c00601c990150f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 884579874 1250 884578624 884578627
    0xe0d120b18091e0a06020702040b0d080c070e0408070f0203121c0b01020f15090307140105010e0f04081e0d020d05010609271104030c0f090b010503060d0b06150f 71
    0x6002c400b0310b0304101e62807080c400003043c5116520f8100c00b041c940c40c1c994200d07a0141c2c071159240005030060500c04800d5502103805c810b0a010012603001804130048071a09540c00290750700000801d2240c112401410304604003d003038000303807820f801e46c0000e5001804039002c81d5071100100260380d03c0b180c01032040d082e204100c2c0010701014010b114140740c00b03201600b00884030040ca90ba4585014a0303410b170001c10ba200168030484200150781c2081d0308443da0380b511841c02c2200364001d21082c082d40a41c1c0e922440010310022421b04040d00076a0303c840818500001d040308540301c041e140c5c0d62954101801c000c0c030800c2c034005001422030038220980000382540b400d900a80202101d6214010486c0c00302c1440c00c40d8450741015904691508002107503880a00c81484158403443e00f005020000c0003e01180c03040c800441c2e9000d840708964104040c40c6100d0040d541c43c0412140c20f50f00404000a440025441070841a00b01d10050407107114880102c0144a854000c44607061107483d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 884581124 1250 884579874 884579881
    0x6050c0403140303250e09070216140901141507060b0d0602090a06020607020a080f090312040f0b090927100c0e090108030f070804051c02010e040e0d120b18 69
    0x20007400381d114030326917154a040d07504030b0031380c01074800030304580d846c1d200b07140b00000909811f0013403218400030b9524001c3c40070390230b440e030503d0610412191a041c2c01075000b14008107000700c0e041d01000c2514001003188800c208103600c2c805e0190300415003201d82c252105100422038844202c0420342c00c1c42940c02507140c00703840d410702c50a00718a034000c204550042c014060f02c29004164801016040600d49a45500300c10380f80070b8922400412941510600e02d02c540c12032844e80251003030307681746142440d040d0303503c3d054503055001d075981c0c0640c081c2c000c0c0040b40c02e0f1065541e02c13058020001c8100446018103003203540c10540c081d407030070003440e4072865403001c1246c0c48a07841da00002d0884060741c3d01e5060280c20f5949000d561940c855000740002c01c481404200015100204001040c0c05410380100e1031241102e040307110200e005c5460810110214074260103070389628407802c00100f142480e005022a9950041c2d0060302c13001c0d607144804921903e8400da8642615900c28280e105400e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 884582374 1250 884581124 884581141
    0x80403050616050d02130b0406020601060f0201091104050601020a1713120b010306052203180506090d08090a1a12072604061b0228020a0306050c0403140303 69
    0x8600500d1103469002c90340d0750b0690300342c102040d5060b40312003040050f2a402c2c50f80d2805800c43c1590860a13a4081c007240014040e40e0010b001d81c10380c1c8050742c80e11120105110140c1c243c1d4000c040003404402c1d02210800681010b50003658001014411075984d818a42c58101c84501c0d4034181d81c0d0516400140e45042080300340310b000041908a000c0000710085840e450b042480c1800010a43c07070b10342020480c0c40100c070900c0d80c40355840700010f086c1a8050b2502038203c0b083c00310f5800f0004044040007500380b80c0719003500c469040c054803c1c5100ca00d140d55000c1c07558805074031301d980440021404940342c0d14641a9007a07030020501400d41c3c1e4030300c0c003280e40041807000b050007041000400b16003150300c000c1440e41200b03075441d05045c403407900c991500c2005444c101c00c4503c000480030034502d01d5281d0020740d04d041c040039001d100c1c0803507500391600c811901319250041d420810014040000400550090383d1101400c01e4442c113090300c0e90340b1507812074920b181c0304002e680044280500c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 884583624 1250 884582374 884582383
    0x30507210b1002070b0714012304120f12050c19030f050f04150905010b040e150105030d021e0a051204060e09070e060306010c170a0201060b12012d0308040305 70
    0x80c0581c0010003c3c0d91810003403240f04d118110005080881200c00440000c80c00d4209410030507001e102c0c22441809e4811440f092801120185c0b0082c90350b103240c00c1b566000c1c044042c0b0701d1085541d181c4412169400c00400341c10050016840300600700a2490f500079946000000070b491960081000c50205400b01c0590740081d2101c0c24400c0c060080c00000389074945854010540c00c5d0000c40c2c502c4450401e02e00600807540300941042c103203040030b0b500c807078041601c1d0b00302840001407100c10f90722441070507512003885c05503002683c40000883c0745018007400800340c02c9100300859501080d15034489061280038680103030f01d04004034061018642081034202c21600c141c0d00b6491754a002c410090811400ca400a4054034000003c984940d1090b040301c9401900301c15645a60140060b500b40311307a0141c0d11340c60065103000800b10300b9440e004101ca0049501c079195010036400e14003cbd80c2c2403540f0400641e515a501e61070a1803464a0440820041d4000e40e0f105071554078504040c0d082 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 884584874 1250 884583624 884583649
    0x162d05010614180a090c260a0203060a24030309051e030307120509040614010e06040503060103120203041508010617060d0b06030307170714071401030507210b 70
    0x2041040700b092041c6031a41e07080c01c1407002a51403a07031210784806501000811752008050b0441e4109103000c510490003200642003251810514181e803040421269150314400800960542005010074440c0865412854120010381200c020314035654034400c940c14015030041f8040340079450100704a103031400d0f04030307141e00b40100310702940e040000c00130307840780308a01c03000300000407140340b0080e0288517000f603808042c8007500800c20341d40c90303c02c881c41040100c0d00b0303a400107101c0700c4010700e1400c01c40140d0b0700300d0b03602800030300c0c80d6402d540d214058407081c40080f008610084c0700004600903010302c0364000f0001038451441d15410b02c8401003071200d00f0100c0351201c101d00824000c480c1c0301c000008040903000b0f841c0b4503207070301c0d1400041c2c02c3d4440c2130005000c045080c0c0c0808100036054004081040c4035501c0120150700802c0902d450303420603c200e10024003602142c01380380d4066004540d0000031032510780211840c010400c505010103503090b90032035603203081c040514102103040d13024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 884586124 1250 884584874 884584889
    0x1050102070821090d0c030620070f02030a0c0f080705060a08180f0d2a030c08030601090f031412033129070302040308162d050106 58
    0x100c10b0300b4045616a40c041d901640e080030140142028280c81c90f030015a01c841c04001e26a4212402c00c0c101000008001d00055440c94580000400815070081c119901041002c4150b824409aa02e0340c24030030384c1e40c02d02a600340c064059a540003c5080172014050410181000940d5080810007842c1001c180c1005003c0c0408100204900350060301c9a0b511982c074440001c42085d424480c242825941c150035041c070b1283c0948a40340c150030140131718110360502a1601c4a44c1c900c0d50001d00300117034039000780109220341003131004214040010760703010806062031010f013a80c0340c0101055060582c01a030b0655451408080c1c020700501018041c641b1501b0131600314140b100201c076480915038014505000c0110b200004140c1880104e600142c004104400200c44d00c003640580441207039102c0080d05034400094139081c02031080e101520740000d1018100242c6076000303481c083c100c00c0c081c0c4508140702c4035000c007000b48a81c1c0d1500000c032030760214201c50070f9140090941f00a85c01c2001c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 884587374 1250 884586124 884586133
    0xa1d040c06021615020a15060512010b0d031206050604030c0602060601020606011d040f111c0c0203040501050306031c2c030a2904030c1703040c030210030b031005060901050102 78
    0x40c00f002501d400c10140d60710701c541d02141c0d005425084e8a0080c022600a00101403651404040d091942c410401c640040c2c03160201000858072171400c0310940d21078a9401a61300141a0120b40301d02488465a21440000140107480d0b40025116400c10b0788100d40c030111646080c000b003a030500003690466402c1c0002c1480307040803400600010303942c050008142401c1e9444082c3d0b039481c0d8000480700b01d40f00e6401c00044e0140c04180d9103036031040f890103910340102c403540b01c0b2040040c418a00c40c6030301540954105402c120045500d6031019220581c140310329002c0039000d4110f03904d9441c05003142d464088034040c820321842d22001c00f142014080341e20300c60508100e0780300807408a40300740e03102c142e2503400c80b00710450340c28401306c02002d500c0c542849020401096000320304d00040ea40100c811803d0100d65945900c8140700488004044001080d0104010b0410b081c9012212800b400e01162403602c11000c07914140d1504550381102e0b071100113102382d60800c13017201d5014000a20180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 884588624 1250 884587374 884587393
    0xf030c0d090e0a02030c070c2408062b0206160c0806010f1a091201150b0f1e0408060f1b0301080c0d080408101401060e0918070e01090c020d050a0c030e0a1d040c0602 73
    0x154080f16840c084104045331080314030b00107198011003c2900d6001344480c0d200c0c140c010b02c1b90100040c4080803104d40126100118482e4030010f03499040700e60401400c0481c030700703281c0c410005200c16026180a00024400d220b82c545c0c0d02604c00804041e00d000004400704020b000f20b0004249510000b1004820424102c5d0132002d14101c0d0303001500c04006409042000791440001d20440c4c0c08045903009400521020070389200d03025000b10803201200750f5910b03c460800c94103100a2044c01c4d4981d00c68030708a0b806061040480803440d0061001e02d05141d03480c52014101242422160204ca507100c00c20b4069a03e14800a40900f0b564507011188400201c04542c1c005405010404d04994001c10241080810855003000d040410003072035213942c0d10082a405000c01c40300c2000540a0480c4038042d03c2e1040090360003085407a554600c030095192000d445104a0000188d04003190180100b28414450825a04142600707513801c0e0710314060800030108285500842c0c1150800f4205 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 884589874 1250 884588624 884588629
    0x30b0102010f061d1306020c03030702060901060e01053c041a0604120f0f030302030702010c030b090a20070804081b010815120f030c0d090e0a02030c070c240806 71
    0x2124880d1002c00513125030358550400b074030b070b43c250800b01c010900c2c0d0000489041426004c405540500d070b031134003180c5e00394841a02e054242e40c014000c520701b50350600e00401092502d00f0812000004071404840c4581c41d0011030b20141a82e0141035440c005a0403000001b428203200d0701c546111000694001c2c000424000340c04c510039481003240280c40c3c4080001401041001c10130501d60100303603a081c1201c1031030094065001225024059460083c0402c8814024012030f0040c040003410024103a40b006084c200400d41c102050000d020b610b070703004940c520070300010a41d081c007900e9006d0300c90b07103001c0c40c461070180c1800c0d03009107461262000c01440e9030004005c070340103c1b03403980118000c030005000c552400090744c080300c510b2040f0f44560581c2900070000b40218449401030f20b40a803140841501c401713056100d08854000d4080025200111030350203903401c626220341c2640380c80859100d580d281d002c0c0d50041c0204100f40c40404000c0c1d440c4002012142d07255040038007151908200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 884591124 1250 884589874 884589899
    0x230103050c030601030c0203250b010b07020a0e0a0b0405090a0219062109021c0c0b091e0a0806010303170a050105010215060613090b04050f090d030c021c030b0102010f06 75
    0x4003070b040c1506c034a03015115a0007031041d5807944810320308030400d490210010410180022034150f400c1d000a000220301506080200c030a81500a0072100c141c603e0108000c0d82c0d400000d008900b8030384c0da00745110840d60745002d036034021166540200b141346054010400043e4012450f02c001c200713500e808010311130f002045840307540c02d12103401051070381003100c420180450714802580610f0b1507040f83c0104240201107140b00d4000c1100f8841607498012001c054840c811041d948954001b034031900b0221000d050245030040684a01c1034180d5400007140b81040030b8000b2400325001920502d02c07a4200300402c0e07848607500d4000d000d554506000070303481e1007043c0c4003201126092000110151185022030b1501d50009035007003a101d0352100c4080003451010180c41c411402c0801040f01c03103a10341a038601500d100300117405c00b03060418080e001003e0b440104004d601691810700c1880c00d8002801003e44056180800c00100c00d03000207085800140d4040115403030305c5803e0020200c90b50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 884592374 1250 884591124 884591131
    0xa023007050a09140415150f03060503190f050604050d02060a060e0a050a0b0604080714041a12070515030603010b090405030f0903030d180b07090b0711040b0406230103050c03 77
    0x1400d0030040b050010100b005051150714011b0710200d001d10004190703c00c0c20141c0b25019196a510041e404401011403c0e60154412981d05074406580e010007580d4401c41c03214031900c2501005402901c50307070743d01e09128085605903101d805c942c66910050342c040c0400c03548805a01001c1050f107040140007e49050041c0c90460310711f5860002a4041c1d02e0b03940503561300c0c2c50040840b902d0320b5485083d25541d8406019110030400a141d00700001e08060059696540c102002660700103804030a00210b10010000140c1c207204140002806848043d2a18008d6416008041d56031030302c90149400d40d848420507500a06242080001040001c41520008004030040c1540c0c0c04c08240000e1440c0240c801c040b40c0c20303182c0f0703455a04000c01114490303003441c4150221b0348155035602e400d4a04004920902c0c0e0401010043c0000040300d04460071030850004000040304202c0e00c01003812140141c0020342002ca4022404140b400043e2800a030b1410034a010f120900c2c0c0300e03800d08039901026 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 884593624 1250 884592374 884592389
    0xd09080303250e0409051e06130807080d1e0e06070206040303150e010e010311060a1421040b060a091104051c050609420a023007050a09 60
    0x41402d00e80c41e807050f109402038400040c01030200510b2814000d480d400c2050074603400900e40c01258034070305000305600e48124402c0c0f40043d00e01307140d9100c0049941c450407044440c01410000b448158100d44148104500e15800d410300704401d0015840490b584502500b0f519031084040082d5a5030000b070090340b255161a000c00d4010340084a2510000350760412a1800c3c0020004100440700c03284441c102ca000300c000300e48a00c03c0006010080c400d2070807040005174401c856100000c00c00f0010100e104800c0d039003221295501d0354044917548259002c40b40f07129072000380a4a86080705082001d041a000108024400c44019012510039442218043d5940c290284440c105498024102070303000402c2d14054070b040980c0740c1e112501145184d4840344811903020300b40d03002c0300e400314503a0421010a401044107140c0c00d20801001080300c06001e400300900c0c5414059a84020200c1c0c80440384102204140410400340308402045201040350501c0355083c65944054040200c40c2c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 884594874 1250 884593624 884593681
    0x1090c152c010c05011b0c051005100e1b1b0106320a030b090f01061508040b130c0602070504060b03040c05150c060f0105031c140c07170d09080303 65
    0x151920502401c6c001411001440414041e054450b0300000b20220461140047c1e4864104150300c20003151000c1d00c044c00c11484401c028410380c640300107401e4010418400040d940c0c0386a503503d83c43c40e8042c5607080208001c1c08000401c03401d09004101c050001403880c00c1c10034484626140c001c0c0c160341c2d109410002c000c074030709009441c0c0480400c003450f0061001e040720714000025540e2a0704034684044558684480083c1192018207025201c58842d59000901d890f6034071000c40aa8028007102840e8050070540c0c00010340808203280240003d402500c0716a107440304110440b14980c0c840c11504400b0420000003d280f540c40030300748c560484018243d01410642d05d103990240e00a50400b0344141810b110040c451485014100ca0003181203c6410320348541030140720300712001039000711341900940d0350f80c548401c015159001c4c10b8800c9801a035940d0941c0e15406461404441d00c1b0f4000c3c000410f00305900c401c0d400d0161035090b0045241d41802034030010b030900c0030302640c8810000b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 884596124 1250 884594874 884594897
    0x4080909070206090c01031802030304090b15180607020325090e06011229010902030a0b12070302090c070f060b0a0b0703050a0f0c0506040b091e0606100201090c152c01 74
    0xd82302c041c070540a8014049989843e25102500c0c000c0c41130461301481545000380c408000e034516000c40d0015819044084201800c620501c01581c2103114100d030700d0f00454120343d07072002d211030b607030f2070041c038110840f807442c926012850003200d5030101a4805900400c0040c014180d06101400c0c940f58840c0d00e04010b06548118000d00b41d260301d40d03081000c4601400080d984070759402445c0507040e0f080c0308219050480701001941c081400507000c0c550040c8200308054603120300d000b80e0050103004102d18085440d07551402c01a042c5000b1284643d448400070340900f0308140c040702401d981b01c0c040749401d503603850191482c01050f103402c0c100810510140c0d0b074140701d020010300c07540e1f20608840480c2000d141005d01c0500460300300445120b0b161062000c0e50300816001011100700c4007a100b15140d000134032660b07003643d2848505540d00c84d40300b64001803403040310710010500085480320482107080000c005002d40d200f069403043c3e10b01c00004017143c00c8410400d8200003424220340241d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 884597374 1250 884596124 884596151
    0xb010c081e1b0a0219030f0b0a021b06040b0907260703060c0519051305010309050f0d08090d0302040311010e240406030f061202101704080909070206090c0103 70
    0x2c618a030340000a10907082c609101240010b600e52018030880c2d520201d200d041d0480c0002030002d110141c0036140e0b03079840e6000700300c2c3c0c0194541c05c8110094054a0010801e244034034004901b09001e205501c01010042840035158406400180c18800750404d645010780c0824032248035002107048006036801e20704214401c005030070040d130340200140709400303c2d498040c0c06a005080d140c42c9010010700010f044611950031944071081c0120446d40042c20b060045000307141c0f100d0121882e220301c640c40346410900300096900340d143c070380d5500c140b450301264150418682e0003015040c5401400244001000c0000b20f1034141420700e410031070114040d0021341c004001030300280214561240d0481c55403152802032040d1100c5031414000c001412680c00c044821601c9401200000544441e006103000c032503917401000a0b140c0304c0c001c010280c3c0701c0405000152000c9419034000541000a4200a50943d074080002d001400f903901c0c2c07104050345c481203110881410160750781d44a06824 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 884598624 1250 884597374 884597377
    0xf050a020f06040812060a0303050a0f030207061107031b11100e102c09070305060d0c061707080615031b0c070f050904030f0c02060c0d0c060b010c081e 67
    0x8a150030708a5038203003498144281560312007a5004d40c03603104a4000341070b0b8100004c4c4002141d0345a40c0d041c3c508102150122400c0340101d0f42c15080503000c12125000c1003ca0007440402050400b440e0341c4c0c0c020500d0301800140810054580035216504d01101007403100007210400107040d100009103a900c081c00308c80020300420555403140315a400f020722240d00c403000c5202440d0210541a0780d1240c80e00320b805011641a00c1503000e0882070008082c3d40c4a41c10541c3c02031005058019901002c4d9100f0400d50415000000082e4581c08180d121400d210031980d0480380a050904040c10000081110000a071209520426000012401ca034a4480040440050362192140c4402500700441d84501c0244643c0b940340e8614000850903181455005002e40d9045d01ca6042c00c2c10300d002d05440c50700c0c6881040c1d0b40300c10140200c0c0c40c1070505012902456a4540e10001885200e1404134111003c05070024100000c400d10000003d40e1601180d080b62280ca08022903901c00d5800c0b0300c0c49 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 884599874 1250 884598624 884598643
    0x8150c090a080f01090b010f0302220605120105190908181903050105010512072d091a01080f060609041a0a3803071d0a1e0f060f050a02 60
    0xc41c814014400303d007140661110000a10602c070720003c59903134a060352218681c81c0006540b00020f80421b20034510f881e2405911000007041c04694266036030001503c440b040c2c113414809135120030030070425000c1c030a50a0184c40081004006036022a111810580944020600e842400c4442c0038034540c3c1e120880d102038180440003a8407552249051400303885c0070b1141034003511107244003070354420001c600c0c44140c40d03241300139840004a080d071003ca00c1c4001d08001c2003d010780300010455044500031103904001080042042c00121400104048801040201100202c9042c0702e1a41d40b140300b240ca10000445001c620501200c1280c0d21714590900c0b503d60243c030420000031081000021040c140100c402910b0382070840140221600341c0000d080c00b80040d003000080c058038042c00071a64071482903603800c8402d007206004a100714449420040c0341c802d07185000c00ba54480045188044c2c01c00175400907500707150410240c00003041d000c08078140400480c00100c0240700704245c480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 884601124 1250 884599874 884599889
    0x120e0103141905010b181521150d02011d180a050405100501060f050f0d0e0c03010e011103040b0c190c331505060414090108150c090a 59
    0x314100424030386051441c0010b00e900e407a090500005050304d08000307640e01d104075940503c03400360043c010059000300071240501d03413640c01d205100c070400000c40401101c11840c0300700d288904040c41041c58180c042e00300c90b803060308110407840050340e1103802080b2858809080d424142e20010004489c913440d0007200c118140003004001c0042c00d541c0010b030299000d0000e4821a424009601041d508240030740e1000c101b882044070305882c4224003d0041041005402c0d05110182c0c442e641070300d1a01c0c456000e594424a000484c41c038080c85952204201d02c402005001c149a1002c0010b010050001e44000c0b00000042c6100654404540c159807041b0100000d03414185405402e02d61032150503542c19180400602901444c02d130300440c0c44600a011a101001c0541003e019045031500c10070f804180c0000060170761a03a40184c8003502d1061803502601a94100340700081805034425262944195450300c840c2d840d0207407032500881080704144d031784c0c0c40c00000700d50b00c4101ea42c00000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 884602374 1250 884601124 884601161
    0x30c0e09070b16140a033f0902060c0c010e040606140d0b03160306050a140f0c0c0a0b0a0f0204051302070c120f05120a050a05071a07090303090909120e0103 69
    0x1c04d0049008151640309840360030128004240c0c0e114000c1400a1003200744c0170000b1100800b039070028480e401040340c0307031000c40d2100c85030707010800c50b41018011a880c1da200039140304a40d80c200c0d240a01d034141c00d80342004940d04d007880c010324035160360181c49042170380001c04c202440a1900a6920b20901400f21400c6d920300b2000d641090340184400c0d40d8052031301c80410f107107009601542c43c160000c0c0c02c0700c00240c0c40d8041c51069020001e043c071b889011003000843c440c84010720040014501440d0f032803c2c103150400c1c0700401c2d6240102001c5038248100710074071140e40c580b01445401140b1800050b1220000e14003409400f20340e0300002085480c03108242c080010044815041c244290141d0b0a0404201c02c003041502403940044040385060040c14201441000503001c41c034003c02064041d05085511420640006c1d07450100007403000d5424000d02d50415800c0008004004040110341c645446041404600d41c0025081005103004064242e00c2a04081d115803195a0005c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 884603624 1250 884602374 884602403
    0xc020f0c042c07060809030703090e130c090218040e0a0b0a020c10050402031510090b040912030c020d0e0306070804050c3102030105090103020613080303040606030c0e09070b16 78
    0x7507850540344079800000d07175071400190aa840c04029610203035407540701c203425030341892030f101084070b4000c10b5188800180c2208401143d003007520038005000488005030b5641aa6010101c60b03000c0540841c0103c0c2840c000402c0310f10005441d035042d40d0069400103441e298070700010060b1181c0c8408020300d209400103614800042d5100d203001e40c0c4202d04451002c44c411012244071030084420700b400d010b00040400c02480103400c20510070000802c001303070300042965032210301c5800c2580f42d00060b640340e00300f092040d01007000036a84800ca007050040c0800355800aa41d0308002890802008610390102c0c0030420100104240722100900d41c55600048161540200c00d501c2c0051000d010009250910002c03075108407810382d131001e0b00541481e130030f5409205199019001c1006011400600018010414400b4600551003a48007045103441e5060510300340c202a0051000d00b110302c4280482050002010400c41c2e4080c00c0312920b80c0001e03032030050101352160016200f841c000d800d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 884604874 1250 884603624 884603711
    0x5070602011a09160311090d0f030e03030403081c060e09390f0d0813090b0916080a0608070e0a0e0601030c090209061e0d0c020f0c04 59
    0x103000582000020303500b10007038010410003503c50076074207207202e501c40c0c00e81d40006521a4204255100301100524907100701c54000c1f6102041511082d07035811018201c0c03000301a407001025210340c170201c0082d41000c1c255142c0141520801450350354000111410f156002020f8001d0350040400c450081040d251010304141c440f01d42c1102c8a05603454820003079800210582d50401030740345002800e21803da84800d00030300c0542c803a0480e038407408070741100000601481c014029600d4200a401c4028a41380402081d9050012818881d2150f81c08104a450005d0840d80d0011460700c0d181d900b03902c4110a8400800072a0041080c60154a50108030b065042d024940a840c444004010180c081e0031b00b04d449840c203020080c128803541000f00b0003840c29030040c04416000820441ca040c484004105002d4200d40d41c00d640000702080f0741000b15220b202c2c80c42c945c1c1c828005002c03020b075250212611902c601040d20b1140b50b840c132080904480101e5202e0028142c002d0314040440c04100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 884606124 1250 884604874 884604881
    0x90105191202070803150301060f12050f0105100602071a032a0d1d010504231006090e010e06070801051c08180907090b070b0703020c010f1b030e070614070507060201 73
    0x10b54806c000e240101c07881140c00c0c144918011101032442155240b802d000c034107900b00e4079900c01610148542ca0494041c42070a1051070301440a2007a054081c0c1d18094010781041459400700700286d220880004010b0070050407240d105d480b00046030302d4040344480c4555000701204c80111092004640e140300c1c2d0300a6401100172003448400c0c89103000100c14414265101150001c09098107140d40038112000020740780c00d620030003016541403500c0411844100d4481c0d0b4030860300c070354907140c43d00c2d078205082c825025865501d1006d0320603881c00180240500c0410312490340a0001c583c055441186050076044240d58000001c507641d4000081c0803507038407584041e561051401c0d03808905558010a9410b00b142e5605031440d0030103d003a02c5078800488020a0030044c0342e0200180c0c44070b04400e21540031900c401810008030000c101c43c4045a00c0b00b48502e80090600d001e5103601e00000002c0c5603400c0700c40e01c1c82c01040c00e40f1402001121401030440090842c480c02c5404550aa010340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 884607374 1250 884606124 884606131
    0x9250e061b101d0a03031e2f090a2106060b190c050c0405040c03050312090c0a140405060d080715050703020f160c08120d11090105191202070803 64
    0x40d028843c0800b074440c0f050286001038000c142640c44040d881e0b00180c002d0b00a50030f5071517180c17002035101551151080c01d440009103d94065404510102c1c69104000d80741e10200700c41c440b48906041450000c51206a164000c00c40300501c0c0f1003240035500040c460540189604c00c2c81482b50680c0c0b10200a1075802c420303c3d86c4440b0311a001c0c040b1400344201c0c000c40141c1d0f00031005284d81e52141d4140801800c001c0c001761004c0c0100d01c00440843d50820060401001790816428a840d016164500b40088020a1882424002d004000c0c825902c1804501003004850004440d203441d8009202540f100c540203000c0c1002245180070720002403280c50b00c0450b80b82c2d0900c51030740c031a00300314124494a00c8840703900a043c042c20b14003220b4261440c140764802c0c81d815801a445a00c010b24014105516020480c030011307612042c003103e80500640d031810b40f2446130911480000280c010b01401d10350f200140218100c041007648642040c09142c40400c404541e1080c450403e02d01950086 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 884608624 1250 884607374 884607403
    0xb0f12070b18030d05130909080f0c0a0605150102071a090405010308040e0f0402130c030b06131d0f011502010b0a0b0d05060928020f0c0c09250e061b 66
    0x4c505801c20f03a805101140c0240c009020503100307007070511380030f400104144081501c007054244903504c0310344144801058002d100d031008040032402c92070502d095840c0204003100d0581101721903901d99070009038002c10356030340b04101d4280301d10303401801155015200707040d60f0103400c0c500000140704020004109950710301d10050b1840c6e4a0052880c403502080d10020b403c540344044429010781030780d000702e441c10b10a00c0c000c51694034160000c1d005400c40d000400c4045c8a1420400190388000300380440d0680c444a0000d0314904031040120f107440c148210828550002c252120452003903000c100300e28002440101b40940703440e080f80e02d503000301285600c43c85c50040400c006141c003d044600c20b011941702c43d034894a00d6600c0217102c003010342050400b641c0070310403e00b2001c031300d10107010110307000402085c01e49a0481000f204e15005440c00d1109211042500e40e0000c0081030814058a54200180300d449190041101403041030500707400c11084c040c021a01d624041500c0c008130750078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 884609874 1250 884608624 884608633
    0x7060e270c091801060912020d06050a0e010612050c10090b0c0d1101020c0a02041a040e01051b0f0304060c0c150e0f0313090f0e0a030f02100b0f12070b1803 69
    0x500301491a0700c0e405e000e101c0200d003065800300502d03810900c207081c6507032019240640e004084c2d80c618090321016589000c1c00c80e1179111196840c3d4092040700c00907e0041410405000251116610380115000c000d000d01c14054a240d800d501503c0c1000040c0102d4011995441401f00d0f41c80e202c0801744048000180b00255a4407038440c140246c0701420060405410000386960800c0b00138103040107620020041041e03040d41c0c1d540c940c45104060304c2c0207400402e031458070025505082c2d400c0d25480c584481e081c00841026040f0005807640315500813400550954005006d44510750070b104002c1c01c3c0034179042c0c603009071400da030810345080c501902140c3c01c3c2001c6148071520b0340100815600031000780e190410040d01c01303070460b0364107441749a80040c4038906251140c3c14044944d40643c0420f11010700360040d180d0400c500f4050102001c0c00300010b07038215002500b030140000d5101c0c442e10214001c008a4070061155400914527004025038a904410768100340c483e021410302c0c030902a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 884611124 1250 884609874 884609899
    0x41508040b130819020f070612050903041a07060b0424050105090d0b270d1b02060a0f03140709030c0905070207172a090907060e270c09 60
    0x1c61110303150143e5010030b00c1418040301c944d0b03407500d800071802c21000718401c0c240a0311500109006c0e09026101c1030341c6600c5141c503030171409001c3c0c0f9800351044c0c030789074010442046184652164610000140002140c0e1000d0609040010780315074450140c6c040d2a2140c102e90004490301c000d9100360078041c251075521360300d02c0159584d018001d60540c00c075845101e00380c00140b8950026602c2814a00a40401101000c0a4984440b034040c4408150b100003c1000d40c95001100000c1105803000c2e075090308205035022407124010b08a941341803082c2c1c2a8968090740c080e4000c202c800c51001a40c111a24022070300401c4a00d151105580e100380c0e220002c510108a8050795101300803030b800405d510303450400c006c0c21040c0519041401d0b03003d0046c40c5802c107071a9074a200b9011044000311240070001d101000150200500720300d0070f0b58011031082000300d0300b0940403404200211200c6007265103c0000007181c69040d500b2408011054041207203360300100500013009003903d09611405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 884612374 1250 884611124 884611141
    0x3060a0e100501080c1201270b0a0c090303030e03160b010612050408040302092d060916020a020130140c04120807030c0510062103050d11041508040b 66
    0x1a02030041040e983c0003560100a1030903c4a0040304181b140c400000ea1801c1070a0f5441da41d00901441ca82103454910300e240c2845020810f071604603a10000c01c020107160741501401c4035100c1c1c4002020b160b107925800c0e030060010300c1642c0342221140d03600000e00c03080380f41c80d020461b400d00170f400c00300340c280742c640700c0090b910300c580b6205940c00740840c1e2620f42542c00304000d0100c014954101006039035011044184400c880c01084590a420780c06907080c414100202400002c1840c1001e841146154a2007540001c010056940a08107000303402040309000f146405d1900080200500e00010a42d403800c050b400000e58010030380c2581c0032916022040c0040788101e00c600380e00350b2114000b500110baa03240c0140304d22032003070821000541c02070b6682c1d41400c0c1000310103010075503144020001c002040c00071240010603e410034610b5805035802804900813040070024495031074862850700240c0c2e1041300c01914249110031800700c01954010042c08c4229011500318252401081400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 884613624 1250 884612374 884612381
    0x501180303080c070c12050f060717160e040e0c0a0902040e0a050910050f0402010f031b0503090a0605190f0209060a051c0e070303020708060609180a0203060a0e10 72
    0x100c0d41580c2c0d2401076111040100d04a4001507800d0394800c8030008001200c441c0680ca20310002d100d000588002c02e03a0400306401c1c090014850420301400319221514500c0240c0070952182c440c003098050074402d89400c80d028961005041d401c945081c0d003c80c014071001810701c000c00021500390310301da03032140c15101c240d0041d44550440201c01034042540d00701c00d5000158405141c0f0200c0301c00d15a8a1408801e44a040d6507058001800700184815541c1c48131100492449034141406200764a018650701d000015500e50f08200000c00802c0c24039001703204090b11a5007284040c04a0300b4403106020503003a0807014440c006150070920b8030100814000e69405420050005091200e024800d551b594020104100c1c42e00350700c040c5220400c0b0720301c544512007000d20b00400002d41141380c041c0c60300c001500040176079406041000f08560300c1c02c442c103a00203011520104c00d800c1300410304d454004a40b00c002e42c17501484c020080441c1d07103131740400e51001000c4110340c43c10751060502c000300e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 884614874 1250 884613624 884613629
    0x30b10180f050a0501080c0721030f05091c0c060c030c180e0403080a090c0e16050424020a050312100e13060b060403050712020406050a3203010c09050118 68
    0x7010f2840c008100a41c021580c0740d40c41030031101058a00003045e0b483c4010000c01f02c100104412105141800360340e81031142c81a0341080e504200311038100301c001c15541d80e00700f0260310480e00078040d030904001e201c2c80c002084158000ca0500801013400800b50262460030301c3c07a40041c00c0f004a0035442000e0070b00030400c80d00400d1a202c111749846d141243c200ca0020b100c00900b80d11090311200152100c4110002010803c0120040d814015030b81d090b681c0c2c41d400310b1403c01c8000e100c01d0211140e590400000c3d41c0355507510b50341746d4020307000a0742082030000c0082e1081c00085a64104036800a808620508200310740020341038441c1040c0c40380c4402910b240d43d08038880c0c511100080c04a900c4801d541c00024036060a00340d5942d5003514041c8a500440d4860345004005021030902d806094042d140807107d86038030754100810101c1c00c2192240d806c6e059160751407404e50b00c003500064045404000750081c44260020300c400344c2010712500c180c500180306480070112500c0041d564005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 884616124 1250 884614874 884614879
    0xe2e050c04061e03020408100b040c05070203030d02031b0c0d08060405160c030e120c1c1a0a06260706110c0f041112150a030213020307030b10180f05 66
    0x562101d84120104400d003d407a140b018545d08200101d01c4c03140400c80100d002d104010081020b2081c20248026617240141240c180013040c8401d02c0160b03404400e80c0c075011020300f40180c6a6036200b152002c1046002c1c0d544049240019200502050201d218407060101e0b454152041e114a4207001c115102140c0700701c00d1301600000c1c0314603284208040703800d66000e4075044d40110084c20001c1d4400c1c10103180c00000b0351000305e001c0c03002e0901062481c02481c016048114070403030317912990900f840e115200d1031800303200740000700225016030041015207083c1342e005411a0340d07416452650b4000300d070400e20a00c2891030001703826120351402d10349044040c01500b005402c51080c4a1009005000f969019480308400d100c1c0c51501d00140200c070200200304010360800000b00490004085041c602400b0006c0b81440941c450809980071040d01060044c0e84c2c1e90380c0a0114014082d010708150310074801c201d02c0d0750081d48400081d03919440c8107803000c010b0f41e6a00d580e030143d00b514400d007034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 884617374 1250 884616124 884616137
    0x804140118090b1305071106010801020c06070c0c0801020f09010e19050d0201030f0c2102130611100c051c06290f0706090b13020109090e2e050c0406 66
    0x4001c28560700320300c4103c10060101501081c0351060103050320700840e82d501c00620f900a07640d005107420011a401000420001c61030300542010b601d440d003030001c02280501030b6074029a01040320801e2070400400f1084000c64492180624400c3e0652108120743e000603004104080e892501d6581420030348220400d2030105407911091001038250200700741d050554415420b20100e0190091014050541d602c901d0041542d81c5480301012807a004014000c0c414000040109155011413050310594105980c55040c1016118600580100f01d0340d0100c1c100800291165048409042480d069030035083d0b8000480440130200c50702f6104200d081d10b038076048032842a240c40f15800a940d5000305841c600000c0407031340e00d4645e22410080b20115a941c0103681402103034940250400850404080481e01030b1b0002002d2800c13500501e00b50542d00c0001101e10441000111040c44c0704804080140401604000b1904543e485031003c0d01c0c10480041c00c4203d6440c211410307184103480c0c60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 884618624 1250 884617374 884617379
    0x606050909040b1506120105090c19140f070c18180219050a150f03020c0c01110c0a0609140111031918080a03091401020c240301030804140118 63
    0xb180c1100e0140c20404c881400b890800a282c9421005000384076440112803c60751401051004001300240410041002484021101c0400341d032022540003040c6007545039009019000c004d503110b003aa039010303041c800003800380c00c114500303a080c4200c03990780c03001c582d04c4c51b400703821202641d81c0c100f18100a0031404960300010f01e00401c2d0300781600c1e59010174881c01611103000c25a118880e03003200440691500c40030380020781c07151140c0343d6186a0301d0158100641d081881c6d40e21704c4400d845506110000300c4a0200440070481440250b20007416800c04030b0f920400908002c0300d6004540c0c00108000d1041000c4d401030405903600302c040300c000d514000c9881c5146001440c03208c4600208100e000a041c540c501c880d52442c00361021002502011742c1500d806031595249038001c04548141400541603070782c01040c1080070310000c0d1001110008a1031012411447c10306428400240200010044c0300300da03806442520303080500040303140c40840c0196031100d490b0030250914140c0c0c0805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 884619874 1250 884618624 884618633
    0x31309330513020417030c010b0102070608060d031e0c030e03060c03041709040f14060901060909020d060b210c070b06040b130c0f03110c0a03030c050d0e01060306060605090904 78
    0x200d810b0100c800c018242600c2d003d83c2c80244a00304000a00e550011485120705d210078030510300700704008d000400080707107050400f070722441000749000d2049104604690a0600481d11120000110890703101074202004001e000c02103d507209900080b03003040150254180069441d0041c1c641c003c1d103070f00710358890741e440d0101440e018290700000c2007445140620388880c007070441040309003040450810303003807000c007222400004d0455210f0000704004014050f001074805040d200c4d240405070b0745d0b0b03c5c503c02610142c410b50740300803002c007800640302884941e4498242c2e44402106a43c2800da11845134100c820300401a0180c9900e0160f8003064440c5080e0740146845500074194102c0c40100400e400c088070102511f07000420300c03001d2411004c581c148655500c100e0300400c210b040c03143d24800c142ea00d010038803008090503980c2406480650046096654450202c0305c24890103c8101c4002d0113032590f880200c0d40d090a10f400850110b004101b900c0b09030300081c0824001c0d41d81e40e201c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 884621124 1250 884619874 884619889
    0x100603050c10020a050a0b150d020901050f190311030706080c09060706090602180f01140708030406380a1d07030f14061f200313093305 60
    0x7108410751007221144d60008000740083d940003402070107034140900d00855805026042d28103c42c1c466059207005800503a200c9004505651054580402d00d914880100d03190b583c560401041d404502a00041007003001004010404ca055003a0341c0e0440e074500058507000d00a0b6000c1d1480d013001d118802d03c9040c50005807100030302555011881090075220b81c0d00305d911011412410503121030001c52181841043e6110025007071a0040c001142e0b5a124581030003940c2000789006000400301e018080d031500148481d610034804100e801014a02004070345540c1c03c40c4440035003844e05c0b50310043c5007407042d28040b5054210890704200b540da50720f0919040060052050542d111980001c03890548608007003044a45410b103164280007003081505250b80218401e109500c4004600a130342c0703c46406040503290300005850354004d00745c1802c40c003402c1d8066600d02481d0380d0004250109400501c1944000c03448040500d16411000c00721044034106c03d003680481c041c04001c00e040650 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 884622374 1250 884621124 884621149
    0x19050d0809061b060703060501020c0a050d050a0501110a020c0a030201140714030d1401050d031403070c1209090e07030803180102130608010509010b21132102100603050c 75
    0x100b00618104a0b4031820044043d84848080203600c040104284590036102d450060442400140506502d8a0005554403614006e15000f42c02d10b0042008200c0c040043e103c05a9003d8000c0c00340c7c030300d0704a0003561070b00044000c1005219045a05081d82091201041980e4041e9250705904800b110b982c20180e1000204451490358424524041e0800384050b1141c100107050206160081e90700000c0c907100c042e00064414900554100002034008404490400300f00c0300f029142da581640586500c000924050542041c0c0c14123005031030351001c91803041d140b080c08100485036903001036030390300c1c481404014000401000450b0040d080c101c503807030aa0310104009441c1c40e4040908000817000b992083c0c000c00d03101c10051100346800d050440c05810403a25282c01c044150b0030070b18540a2603501c01500d2203946020811003000c4400c511079141d080b4910103001880e8407016890840513004440043c0180102010081c2080c05003d0031282c00c00000c042d607042c880100001d505604 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 884623624 1250 884622374 884622379
    0x1a090c04050108060109060b0c0d0e12120316050304050a061a120d020d0c0510090303020d0912030509030a0215070c0210090911120a150504090b01030219050d0809 72
    0x1511004a6a9518000c0e02e000e03160302805070800e5498584000c0a03903800360880c01c0c0d020000d000c2d4034120384000030b6002c0038203828039000e10100854070105241c80e442c3c01060360300d40200382c80400503140800c000d50091000420203e1000c018940885450000f6240242260000e0318090b02141403500001402007560245502d01242c920008120300c00e100b07102700c2d4a8000c104040b840701c3d0180302500660005081883c80080996030707140c0c0700c403941d48100c04035681c0c49401c44145407082d41a6103180103640c000704510001800d20300301030040e143d00e8000007801d21000038100f80c4044141d070503401d8982c000300305015410a030601c003810b000340320b00c0801155001c0c41c030140e998014003c8200a05490703020040341000c400c0001d503070100e803103509001020407000644443c13506d811a48400010030004803015200004c0300010400c1c2e120356442070800c80c1c01000c1c8003042d0381c054100ea10846641041c404003403100d4018104501c030b203943c081c8002d02c210300442c488070000c18120200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 884624874 1250 884623624 884623633
    0x6040204080a05011a01140a0c0302070509010b190306121104020d020f13080a0206070308060f03030c0c190b030112061113081509030f07140f1501121a09 68
    0x25800020b01d080e540580568890303448000c4e0815042d0145100740c0044000e103404800c043c1d05110b90040ba1003400a60010010240e080406051090042e00060500184110036a59440203490410f80011122800c14103030071129180f180d00921890b0704442c203c08038518080d10b00d481d5403001200208144d90020b03008c000d9500010020300c02045412082058583c9a20040707407104021080c41e04034a6003070f40200c50240c0542d42e508281e4a4007a85440c00361a11b46e10003000c24134a824030240d070350301884045080c0d900f840c0b001c1403144248005440882840f540d10340c105a400b94903200302c40417030900b04018400d240c0d04685510b07503913000d14008200030302c0e048041c00700d0b039000c0c1c00300a2040a400701c0502c2040307070611200c83e40768505020000c0500b040d030b40041d264801c20444212409002500500b003006003800e111142c0d42c2142601d4641b040300c550316071210000f0394801420080c0c5030003c200d0350250300c46200f406130059550840c0c01d540c1c0701c05443c06180270b846142c0c81d218 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 884626124 1250 884624874 884624879
    0xe0d0212090307080a1b0b0c0a0206030a0b1503092506030903020313030501090c051e040b0f0a14010201050106020d1e090e040507180e15040c170105100f080607030506040204 77
    0x204008031280103100b062446c140c443c080c2101c1c0c25002c4c003500004003001c0c0c00c1018201540001507030030244ca0301214100d50384c1e2101c41444000f884020391250704140c2e0328000702413040004000d54031440001e000e5400030a02801140125020140c0c2c42d0f6114a00c15020300c03000b8460360149070150321a00449140c016070040302090341c0003079442200c45a4550302100104050308140000038030054480300a11600e06140081004203e0001c50195a43d0340342d425203031781c901310201c84944029001c52801b5032104e4822251040c461010343c095800c0400000315103200040211101186640d500c50740110121201c0c10886080c10000c00c004151002007900509030903080c0c0250b116000802c0030f5807501c107207112422000341640e10414507001020210800110f0041d406981002d41c60990b80c2e01d070b14001c48a40ba01e6000a016400b4808400d402040150312150144103800f074000d00c0150788a010440e00d00080c052039030650064404a52224003980105401c01c60040026007881e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 884627374 1250 884626124 884626139
    0xa05120304140f1f021c0c090914040210020607020303010306022d0d14060607060506060d0e0f0f070b09010c1103010509030403061b020d050f040e1008010e0d0212090307 75
    0x1c15480b100e000c00e8100c290025400c40242440090382200707501c00b582861040c110742c00b010006c10500c50b00300f51712052200503107841407003810058240b40300d040001d9081745202001858044400b02d02503803403a001c18080c503000203000c51180c03500354021441e50b0b00f5652410041c1d006030311610798005040c03131083c1c40c1c0e000b4407059500144540003095150b0820711001800e461100c3c0a001c42d0b03004003000e0005a803079000c216040c40da007050002c102e03a15140082202c91181440160200b8944140c0a1010202103001c00c4403c1d80e00048071011440110480d0301c07188980318200e00880200403c05003540034408915400d801940c03d50041c3d80d918001ca82503075012124181765400000e414001c0108034494250590a4100781100c109aa020003954480c9140803c0040c004081500503020b9440c0c4200e4021300300345803c038a580d0810454644000049014200055007400d1500002400025078801c400f90141e00410010710724641d8007840d5888587c503160103004503000801e0b1107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 884628624 1250 884627374 884627383
    0xa0228030c030602031f1a0c0a1b06020f0c0a2115060f0f080307080f0f040602060a0c020109050c120a060e0a0c1d0f43020a0512030414 60
    0x11402100b0151790f03458845007520941c01c140089414440441c1d1050002070014a8420303a141d901440003070356268200c6806103040206240204000b0314103010366060400142000c084a800307030211242d012a00301142e4503942d410361100e03041500041c00308110789003c00703c0d94013076425501054282e40c0c261203030741f09191042030180390251103070810000181800400401420f0441445128a06000380180c8902c0b071b080d4013900541001c00c160380ca81300c410302140d408481206040c2d80d80c07950744401a480c0c00302281c3d583e000354034140e130181041d130040c010301903510391141c00340402814540801064003440d400c02c80b1288900801070000039403030b10402c111042c445000b03042e405446d03d0002403400c211b030080d0041405500305104004a850070755a00b1280c91000d070f24280d920244424402c0028080852614116450100c50b4240c420703202d6050071b411080354400700310320080503a03407041c19820090440d440441000c50415000001d140c001d449041d05102d846000601715152 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 884629874 1250 884628624 884628629
    0x6101e0311120609090c010c0605061f0c020a14031f0f0207111f02060f04020f100c02040e06070c0212030919060305161409010c2f030a0228030c 64
    0x40c40002c091000500c1d0900249922045190091400c1d41d246c20000309840e12015008104c2900c5101148440d074410610100310b084c9040440180c4c04d5490f401844900c01c08010780c0100050b000c08201c2e544100203040c1d0000018000700703a0412001d2841e80c0d56030095200d007200b15560700300380020040038002045214011003100399110f92804c02c02110f960303030151006030a503081c0400c84c0c403190041a995840b2000b52519082c41c2e84c1c50003c191a070884180d43d0382d1141070001c064404907001038003030071464001c0d01e04111049120003480d130340c3c5006481c1034000c1505500c0c00001454408a880c00c00f61030a01520704043c0b100003c241806203005071040c11508a500910503d60325209190340003803250010a071080c08c1310800381c80c04038050250341c180c0c81c00090340e12140c0d000341442c1c10030950010440301100c188000e030358103c0000c04030520743c0c140a04525207151500103810880103800812510008403060388480c1d00240501028042c1400c80f0b60001c085240b04200000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 884631124 1250 884629874 884629897
    0x90311010e1f120b100f050d06230d02030c1306030204020f0415020102090d120c05100203010f0b04030206090f0a080a1b0905040b06040c0e040e100506101e0311 71
    0xb40110300001418044000070320080c100c1c9011001c1880d0f40e58019600303071600e1a4205005030809249044440c4e216a031070076150142060000a4011015050f134400350402c007941001c070000d9501001440b4440003000381d811b034003440d04d1030103d1900b00303800c40205129000c0055850b039282c1c0030a040c0d82250104440d401d001060410100b90f020410580c02e01e5144001c518003040000050000d031881c100291121240003201c0e086c0ca4040c00d490132280760020304640c4224170b0810b4940c0658801d0140d41640d11031318800081c8810303400c0c1980c00b41c1e80c2c0140711a00f0071030940e0a104009a00501d1075038011700d50440001c56000030311108816901541ca810159a140d00d1050000905640100100c81c600801c2101290701041c0041c0c11400c2200c012500f0603000d0809c0740e64081034219039501a29041d000702c1e0207900000c01c0c4c0d1202c07408240c01d10042e135903001000f20f41121035195030046405034000c54200650020ac1048460290400081004585d49945000d402100c6c0c3c00c1c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 884632374 1250 884631124 884631169
    0xc080f04050d0624320612060f0406030503220b040f030b062b03020f0f030706051803030a090302071a0c060a0204060f080a090b091b01030606090311010e 68
    0x500100c1c4a008581c107600d6961488040e4507041485c0380c98292841c20300310040c1e500c001c40c64090002e5014068240000703200f036072900502e9a4444030001c0c00e8400510881800042180600740740c0915800c403a0068003031030800d000c0c0d2000c0d4008629649268200c8000840c01185402480f0081c20150042c819600c10090031442d00c0019040003038201c0d403090b00340441c0d40d4101450140100c2050f80000c052031072101c854a0241e10341444c0100141c2d050103203100280785050000054074866000d0101070006850b0348407a0300c545120307813400d9125600100006400e4000c0c0b500481c0004c0e20070b20441d117005ea030741c3e4000224015083c003160f00d50000020f07800415201080070b2034008011180441c9400d1070030030050400010700d142d607000e204080c000102c0c8203101c0d0307000b203000c60740210708261180f50440c05103885002d0342c00c0907c0c0020b0100c40640803944039100b1002918600e8840340b11090441c2c40b0307400c180b212599941c3c1001108004480c154403008070031800c0b802d0105114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 884633624 1250 884632374 884632391
    0xa0f02060108120703030b0a0509011206050a020c12030c0403080a09150e010504050f03030904060e0405061302150304061814010b030309061204020d050f0a020f010f0c080f04050d06 80
    0xe0802030103900c152801e030310080e418850003000038200c0b10900d5140c140028200729007030105203001d8050740032070b0340480964000212a24900f010000b8284100d100b001107070345880c60f002c100c0c0580061000d8662140c01c0040f40600c1200007141c110620041c0141010341d01d40d5060165400307683c142c0c00085903a4820002c90000c42c000f18088925420700c0d06102c4c507200c0c0002c0080c0100d20400d071207a880803c08405030f0b00c0038811103030701c65009001444000c0d1102004030b0101d4058408803082c1c400d0200150401000c1048420403039402002e01812801c0d41048610035080a801070741d510740e5609410901001112401c144d841c403e08402d00d42c03004405070783e400c440007034400d580250410031003906565905e02c11a00c260101031400d0b00e0300c0c0c4803400850100c2001080003070461103240f000d40f500c20000503000440c9c42c82224124601c02400d8011585002401d52640102d07505c6000300c0002100c500140041c08200c0c49094141952071b40010340403103c1e06020340305290f0701c003580c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 884634874 1250 884633624 884633627
    0x120403050d050c150a1b02030309102f0a0e03031201061d030d020d02061803160317040b01090b0607020303030a3c110304050a030c060f1109030606010806061608070204020a0f 77
    0x756080306e00d0b001440c214a465018030f52251100f40b001c07041c00340e0741d41c0402c1e114810b80b0545d5107030b20045000006819081c01003506281d0011001401240741c03000d060340545000011128215010f089040599203018400d442101300649815861040345540b002651000c00c03000e19100c00c594000c108a08582202905181c406015041200c808180c006c5c1360b20400011a00400c00c0031035094050390380c43c10200c039507106241c42c00740c02d40000b1041c442400b140d401da0a040c1c60b0a09801c00001302d4490401200340310380180250103400600008143ca03495900c040d40c120340041d99002c52414004101c4510f4450500005408020312600300d4040070b6885121000f0302840c601710300e107051a440345d40d03441e08210700007400c01002c00c2c0010304000d10707a0401d8100c0d490841d0140184071803000300c0940c40d080250117a00070311518000450941c4900d00711f60044102070031451511400400d4200c0c01885800d0076100c00741304000181c01030304c4d03074401440101d2440c0e550400c2e60b003c1c21030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 884636124 1250 884634874 884634911
    0x220f1a10050406091a040f080601140604031a060315010602010e0705460620061b0f0708130f060c02100f0c020a03060e120403050d050c150a 62
    0x310581000320a0209204035a0004800d4050b6000b2400004540b2450000021035120b02c2d004001c508580090008943e03d00140301416180300d084a00d4000c080742d000c0c0911402980310180280b0110200c0411510310360340c0b80b90f004000542560b204e482140c0110003041020785c06400180e40d03400f45c00100358001c1c07202102070442180c92032a0608165989054030b002900780720701d9440f4110390006041d01500e890548280c4000b055184c25603144806454440c0e420025865100304619001c1640d101003500d92041440d031400704900301580f20500c1c0581c1122141003178884040112001007180b1308040d02c03e0700c0c8451008d02285080a601d200c001b1100d071721034000d010b20310f200c0c0c00043c0c2e152101e003401c0d25003d18103401ea66207582002c03120800c3d00c0f0030103500248264004001d000741c9400c8000c00c207a030b82041b20701e0104030900c0c40100c0d104a11000e800750f00120a841c07541c03840703240100b41200c0014110f035074400481401c4409000161481e81965940e000003c00c02041210b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 884637374 1250 884636124 884636149
    0x40f0c1d04140718080106060c2009010b0d060b030a0608011b0e04091e230a030c0210020102090a09020703020c06030402010c0b1f090e0714220f1a 65
    0x4805000c01c0404840c04002510050b00040a11054402c0d004c050302d0611081070041c40e000f4000d110301a51800c000c0c080400d01e000030358000112429143c2c0c00340c03400b1040c0203560360140900754507038a0501a814160004c1c1c0e904a4002d4030b5020000384485034001440c0076101040e00050719510b00380360035003180d16005010004080c001402c50b03410703401026200c2090310030785001ca0242811718182e05105a0500c0b1341c03401e907404d200100180101e0140741d5030103031f000d032400c560a021015920b079034901401d8001000076084826200060400300000b410304019400090b003408401d00004600e0407141c0c000c1d1204503408102c09007410b5040001c2402c5020995140e8514145900001c00142d0004c1d00a0319040a88010480c0c2e0b110b200442c0703401d940400321441070303a920b0720f140402500307500003d0480c520400300041144285590000c0d01c148000f403403400d001c0166800803140412170200c01848a82e0740380d1450380c024040c02480f1802214441c0d08041254140400103505a00c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 884638624 1250 884637374 884637379
    0x6050912010506010c0308060d020d080a170c040504021e0c0d0e180606030405100c090905010b0337091a0a110f16050d0206041a07020607030b040f0c1d 67
    0x140511003d641c00c02d012454494061402c1d0540d55541000f20f40340c0d803d142d500030b4014105096030014804c0c3d180c050807005105a0b01c40c0c2660412407090704200c241921a1440a8000c01c000c021a1901e68000d00c0300400c1960011045c405500c000e4000c3c0d08981070300050768100b07031600c034925503202c003810a003100c003110010749480507680c1d11201544c00610007030117181c000000c0360074030a0800101403070034a0000240b010f40c0e90f181000700a10303131b68880c606803107090400100d000c0d0f1074042524803400506420807004100000754024680c0300043c1800a216076502c2c2030451581d03800742103c0c190058004490050b030103c003c5045d079900400584100c0d10b00f004440035400d02c03034101c40c05000c440345883e03180e2000744c0920b150311625601c01083d0303100d00c02c0030380c41032354011407014401d50182c0b46044c0d10b000d07100c40c00c2e803410000300c0308500113820000000b103000d4040d6005003e0641d024100140a120080d102c0c0200c91002600c0ca01141400062491030341c0294040921800c0a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 884639874 1250 884638624 884638631
    0x7121a09030403151103010611160b1b1903051617250c0b0d060e190b0d030c0318030b150907020d0203030109050a140f1e01050306040f0611040605091201 68
    0x2d14030745c1c640c60700060150300c042103103c2e445d81e03150403c100410401c1c041c61100c000403a81d5034000c0c80e211680500080e00042c0b401450031402c42402190004601c81c09640110351440d01c0e5400b01d5440e0300c11410032035454450b1003404046880c0c0b2500741a03141490b82e4042c2d840800c04000e01c0c1c250020b82c48000510720014480700016131820078003088800240c4500d880e64048440c01014105a80250504944820800c82c400c4a02028080c0c18074a5150420005180310244410100d038424040c0204240254203030000e80b0070030310310704815010250080d80c030fa12076030713a00c1c7ca50303809440306105a00d030110100000e280c0300c2c81d92604066140020141c04982c1d0001a40340d0005101d480141da566200281689201e60000e8605000c0100d5a11aa00d487c04050001a0065800d00741c81c034005617400c2c1030550709580c803a040c0e070b20050042c070040d51203a41c1c11088903a5030208070740c11615114441c2d01e50444030060710203800f26843c4c141c0c23580c0c448003e2160301c84c00e5600384001a0304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 884641124 1250 884639874 884639891
    0x503030901020c011b0e131806090b09070b0f0f09090405030a08150d0813080706080906011208030105040203040f0605070e011419080901180b060f030f07121a0903040315 75
    0x801c4080c00c81d40406c241c42c075000c135240b40715090004109107200004481968001402040110360000031260720980c03c000d0341d62030f0045c0c115511003031800347e070410301e41c10000b030060121160301903c1c14011125050349005a181e003c01d2a004056404031803c0d8400b183c1d0b24241c43d00101c080f03078419215615800c0400451000500c0744184001c064182d400020700e25000805103800c2030040c1046100b2030300130b1540e4400091072450202c904981500a103030010488404610344010501d40016000d0308503420141084002e40c00a082100e600402145110015140f4010a03100c1c01c499181d808410341030302c0025004c411910003805203194100001c01c2790700d0b10700181c007030314080034a0724240540d100c40c02a8010304c664071094641c51a40b86c90001004143c0729940e2041400351880c095a0440300300f455501d9071100103c6a054020080c1030204040140e5400c000c00c7c020032558140318145181024074920075504003c0366040020705201307108800382500410f100100c0c0c100305581 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 884642374 1250 884641124 884641127
    0x70e060306040b03160620030403080403020f0f0d0b06031209091f030506010b0406092403020f043f1113021209010504030f022e090503030901020c011b 67
    0x480103107007900c107070341c1d071400b2000c0360f2801c00c80481402c00244041038441e0700c0c2d54000e01590303400e035440e003822460880b20290340703000801508d003100d9124006504040c1154200301665419503031080c0c229544944115a0b9620345e050144e41031f015022401282c18440c0a050030300d9100144203109510030042140d4039180c42000175400110000410340c04440c2c9190f8140d8650641c1c4041c0071803082100110350086048024811140c6540714810429030f0303400c41c1d0044504080450003100100c550404130580030707400600e605441207615501d0b103070720380f5410140301c4813840700e6002d00101c0040d255503031a01600a030340b490000906009001d02180e45101c0c0e50822060b4960140c082491050062032503a0140d8084030303010b07807003071a851901d4000300d8000c14084409400041c21000350741102d50001c508441c020115030441440c20082d5240c0c0b20300351046001f648442640c461540c000718106101460042d0024400541d07030302c03c200b2940c4e082d50061580200000c460004403201039 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 884643624 1250 884642374 884642377
    0x501091512020c0a24060515030f07050405060408030310120f11030c0a080c090a06061b080708040303020d0809070501080402040e150702031b01050601081801091a0f070e06 76
    0x7030040200560f4030140007000301d0511800004c0140300e1000d03103199042c5070600e50740c0081c40e401001002c12071030f5511001c101c0000501806000c05075010004100149440780c0002d41c80181800c1c01407500b56034074003050707103a805940070360f40a40011041c481100380b0038404000034200b41600303541e64001900c0b460282244c0c07500051a0380d80202d9400e030b45072030602c400000254024640708450b035842c41200d40314000d180c1c550344143c030041d001448001d11480303900140c520f203940e0415043c040307000315030004281240035214414140180c130002200c0000400c082c51003035014240d0300800e41405410140f01401c80800d68001003010312441c0d9000500c0c40d4003a40403680410075081040c480c60030f001c0c419a800c5220400d410801c9001074002000745004203000c04a8082d403440070250b00d00325070050b90f490b8001801503002c0f812400c003403078003034030000b02c02d1000003400d01d43d0703545140d490f07140e000200110428040800041102250310154030028a040c038800b00001b800005030a07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 884644874 1250 884643624 884643647
    0x40204050120010f050f16031104140a09021803070602150402150c0708010b1315120212030a030c0e0303070b0106120905030f0c010b0d0807030c21030605010915 71
    0xd85450280071042c1d002500300905600a0040070032280c10400c9221995100444500d2440703108141d030008100d10a102e50241c40b01e6219445d814141012655099045501c03003003580145129004908081d0031705c01442d1100510400e104018290800c0c50b0908040d0b6115805541100c400480454410711645030f110340d044803145030b401200c4081010f00d01601c0a69000340c400c20f0b8001ca0000c03015407050448007230449070020380602c142040c0080e6040810821106541180200034002c02c400c2d035160038910080400e0302c04803c140003d455604a5210500081d0301d502c0d0321100703580c0000046000000980140d49409141d40381c030914481c06100399000c002070014100016201c030f0f171000b00b507030340d014013942e540c4d140380a94402560401c440d0078100354a8540300c1c1181c1c3c07030004501210039622141d11824035940380c8082d12a943c14981c2070b562500c2442c2055002c5400d00c1c00c580c0528260348001610508103000101003041640241020481082d503100e0f40b06c4c4c01c038010511 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 884646124 1250 884644874 884644907
    0x90a11012c010903080d2408100507261605030915100503010207030c022704060207030306090504141b0f151608031f121e0c08010603110402040501 65
    0x2800400740d0048074001803075400900024408203149006076115003040c1007596071075031b66513541e52010a403d900c0380b1051281d60341c5a4040100184c012501d50042503102c4140d080144001841c230304035990280b0000e50045080603004108815001603441042c903c80c91844c01f0741c00c1d480d000468903660780c0b0f006103a281040c0583c001900f044e03400c1180c0d0014101c042c3c005c0d52075a00e02d24000d41080301c004400c078402d6948140781c031070a01440000f4030052054200300d249549490715020004c0d40802820380030191942c00c04a4142c0960103090700840c03069115801984010740c401d03050544011005031120143c0b40000625914203103c2a4a0441203070640800701325440000480e1180c044813002240031b9120200500001d04082d44c850b81050741c01248540c3d48045030aa4141c0c540102480465581c4000f4082050481449408510718500009200c0349440748000c3c465160b105119682d11006e01f4000c01010040c2e0300b214800c181c50950405e07041000103070010b0085804206c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 884647374 1250 884646124 884646197
    0x71a01080f0d0e01210c09090b031c12021201030c06020c031b1003021b0102070302070b0c0a080313050a0819080105090601030203040507241d1e01050f03090a1101 72
    0x3848282070301e8259020349801c8404201350510b086010b0607a81b96481241e81151512427043c54a05011501014003040004551140104418140da80c81d01c90312181d09907c4c0e0901c484000c820640c110540690f01466100500c5882e10310000e00d40301d92508454020b030403c244003442050855091844140100e031440c3e28103501d038400310002c0c002c201614000095030300c05143d00400c19401010007034043e6080e43c03061521044804418400c04504101d941d0001c0c440c1e41c04541c0d0031001e0b41c1c00c1010400115034185054442e60700c3c240e16100150b0742ca0704002203102e410406054035405921407400c0001196140c100010000c400061419040c182c0004c0001d0800500b40f10030b0026240c40301c0311460100e005e0504451140b401c0e680e003004a00510710307583c10310f081041300044140e80101040301c2c04511900030614140c40b810294107104080c40310701142d80385031000c1c6200f990548000e0404090314206014005281c440150521440c040709582440340401c0d003110740d0f4400e44111307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 884648624 1250 884647374 884647397
    0x70201090615030209070503191a040e0106060305060d051009140a0807020414150118120809090601050306130507140a020a060f0c120e0102071a01080f0d0e01 70
    0x16800340000100050000303180001c10b1040c0818401c000003541c0c002d40d20a40aa03442c080c0c1a240c620096684078081c1c1c060115042c401c03252a00928078007514941000040c2c0900c070007082c15682920404841a5101d00d000e2080076898820705038001c100b26108081306220b82c0301c4580398841c040300404015114080740061003000d40d000c03d85451034408a13840b10109090180c199045214124416400c00b680c2d103405501710031000d4040c2441c1400a0fa280825400546290112520900c0141c540d6240051800c40e40306803500f086000301c41c81c1b41d403000c0e07442c00c1225107040280030070306000f01403040c000710b5268002d0f0500f456240c50400241512411020f036018012600003800100000801146483e404030382421003500c078a0081c44030000c180c40036802c0c1c50010211320001014000305100c64155500a0248022140b00051400401c1e07140c403c00465030001c200d00f5140780c00010440320b90104001090300c58040c0150172500542640206900f255801440c108070202c60107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 884649874 1250 884648624 884648627
    0x110a0906030b0d0b04030522050a15110d0e0301060b0c0316060f020f0a0329010f09050907020f07080105010e060f060c010e010501260312130618110105070f020907 72
    0x210522113801584404d0240790034030380100355502509490034014600c501d0038a180c41600d00c1c4000380d90700204220022400c01d00d43d0600442030700c02210400c4031102e0499001103003030100100c51003003075681d0070b81d84180c8000d2500759001a40890400c1034100184052014040141e400003500144000340d445101d04103640603020300c06900040b0b41c40060020310107240c020051041e681162002e112099004c030f84803d40c42e003000482408210150700d05c1e85035600c60104464181c0f107900303112816a4943d004501c41c1c62040fa07041015a114003455149041f00300702d803078000d054940080c03183e5810403505030f408132800b030b15271070007035110300c488418030340c1c84d4410b440701464000000c00440c082e0140e124040c0c8828802c08019064020000c11b2100e165030715010784100600c002c5160001000100a800000a0140a000959040100c002141800307040a0400e00e002c7d102e80303031841d038104120603510301411141800000c100c3c5030000b4418081303003130a19404452070555592880f50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 884651124 1250 884649874 884649889
    0x90c04051b040603090311210309160e091513170706051f1401080609100315020d0f05041115130f150201090309120c09060608060301110a0906030b 65
    0x111641c03a041c085400301e11240d0545c04501228080c0d43c1c1d0500740d0301114401c42d1608081c5d400c07404030b075407040d01c3c004c482e410403802181c009001000b151152229880c002d6485603882d001250042801d000380310010b00204112000769080e1541201c80c1c0c00e04142c950790740712901100030081d5180340d500b03040701d80346802951109504880b050110b440c02000c401500c2c041422aa04a40c0d030901010a24901d81b01c0500c24000c010303100c554241e00c0d120701700807e04800400c0840301c42035500b008800145120a0040140a070040140e04d407aa25201882500c0c1c00c0410b085007186080d0801011808400c210701410030161111140582c546100035218481ea540d1401c5d064400395001501c0e4010014074000c44150800010303c80c488020100e00344c0c3c00541020f030000d540c502e400e0105000c0521080034092213001c202c00100d41d5030780c0c00b106070b818903405000442d003803108012282c202800780c14080120401180d14003019150060b1083c0da050040c1001c06580d520720984a40300c018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 884652374 1250 884651124 884651161
    0x140c0913060f0c020a20060a0806030a08040305030a08010e0c0d02070c08030309071404090206040e1e160f1e1d19030309090501080d0e011e030501050f010206090c0405 74
    0xb0382440300f02c181050207961060040d404840e400c1c4071407501c0c42048000700c00e03540e40d03c6004155914141c48240116092003024000d07541c14060702081c0340c001201003000300000c43c442c01c0959140c408900000d820000141d200c4081c0e0708406040040b2000341808440810540400058851745030303041400c041c107450303041400c15200000600c0468440090100e0440c2d0b0082c2082400310580c4051106985160f28025044403003400203101140402464070b6001142ea4420500d02c080c616010350302c00300071303941920854002560310890540c88507400c46140000d052030304d60310f00e00581650f160300c1c0002590341002450b030342e042d8010380c54000c01c00360203000500c0e511444582c0004804104030f18441280030803645d400000e2000c0b02400f56904035114a006440c0d0389100b0324040d2004402e10705d07c1c81c108851403181030031500000311107446a024658000880703604103002e02c8040d4101e07007141410f541c0020100112001c0024244080000545001c203c60303c0e181d0420000e08440c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 884653624 1250 884652374 884652401
    0xc0a03090807061d01060815010510051620010e010206040b1017030c0105070906090303050702040b190512030c19030e03070e1009021c1d010e010504140c091306 71
    0x40810b828500a01c6045a1342d0040800200308256880000aa40e81c4030310788998420b071240c600410980c5450b2100c1c1d4003012040c2445880c1041c0303d58030019041000f6000c03a20040c0c00304014842000e242c0322071400c40000c8c249620031000b0b43d00041e44d221001000102580c00c0c0741c0004414406114040e0028071050380c42c5035141403481d005540301d030000140300f42c0e29840e110000f0740051103980701d001116019103540d1206400c50702c04944660014200b41d800680f1603980c840107440750617281181641041d40000803078200ba0800c100d001d040d0a640c41c05610900400c11210740100313040c021002091712220a0700c03800e02e030a41d178190030005016418018580009103d103048a00c107440781c0e1804001c0303101c150b10303000101d0490040c201600c275060241c00c10102040141e502c080c41d1259207407005203142d42c5100039103080d9440c121100b0410303516602030100300142403c44980c0003c80c640a44201da0b03150010440fa620028083c3c4040054035035944140842680a5041c0300b200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 884654874 1250 884653624 884653631
    0x90303030a0911030f011d0a020603010902070314181e01050d0218060309060901050708160e120d050a0216032f060711100906120b19062102030c0a0309080706 70
    0x407117000078000d110844021005046050340c03120203400204448410b203074024902400c43e4201071440b0025005984100c0921050800010418004101401c08060100c09400ba030082d54428400c02400c0035005440c0c0030001020890b1a1b03810106580241e4003c4500585891240c0250b51042e409804003607081040001405142c0d0b10108055203d0302c207200c002e0100340c0b00c4580490340c0741000c071a901120300c3c00603d1901002e10800160700340341c400400101000305802c0c01e003410030040e148800c0204100140c41d15180b03805008160000842d81d64569080b40340d511503100d104040c1414050300c0b456194011107a280c450007541441801400da15264843ea107000c03000b10715440c00b909e00ca040d4408d401504184598640010744250fa074501c1c0e641d042c662000c2c0007805071404441c1d03100c4048100340c0c00704132608050074014461035413030b81c601c100f450341041d019105010180d03c04034010400c2013060032180d0119100c1d002a4900000c414400782850240e5005e03000d4020140f506 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 884656124 1250 884654874 884654893
    0xa090911040207080304120e030c12160e15040501031511130807060305280c0909020c030316020307050706230307200c180c07150e0c06090303030a091103 68
    0x4a013409503100318070945d0307000e80d1a006032034240d03426034503004002e0381a40000d24038425414201c901c400354188070f2085903030004440f10f101207203040c90f420441189004104000c2196000d2001190342c100c15101040594196101d441da1880b01c81030b601c0c9030b035448800c180030a018003011590035a14010f0700c0d00100d625441c003030740c40e803a01e441800300090514010413060b000d00000b80c4a461440c038052003100d035100b02c048018212400044017841b041c3d181c00202004980001c01c102400300f0040c59481ca00303075481107101c442c4a603640c41194414000b80300040c0d00003c0c0c0307c0a840c1a410600d010073740302c922034031455801d00c03800e02c0710410106c244052950000b1b20b0b041c100301d031001c0080d40d00110f0f00000741c0c0d038000c0c0e0120315031110b001c1881035942001c00c02c00a400a80010002e850700c9216102c8030541c4200400c2c20f19015580d11080006003000e01020f600441c044405c14540f000c141d000036036900020780143d94140d9221210303010013200050388a0852030180a40700c5264 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 884657374 1250 884656124 884656133
    0x180303050304080f131502010b09070c0b2a04050405010605040f090e0a060219022512020d020a030b090c010f080105011220131703040b1b011a130501050a090911040207 74
    0x2886c9240850166080c650300c45241c0c40e00341c0005100c2c0001b952009200e42c4682c403444100d84000e01201545551441c14090254800100011003000c0c0740301c50f44d0f00d40c6400280411683c05034494020000280700c18801e481186400000303c814410011510350b441c0000d05041400b410002482c0758400100d04001c9600a0709030b65540c412602901c40440c1030841440b842684901003504110820a040c000e250b1113117200500a4005070100c0404005680072402401ca550001e0701d900501c0742c10080d021508200c0020284001c0ca06607000400c1610090035580707040c011a03040c480b0b06210514030075201e501400044000c2485010f0b103600744402c07410740380d01a217000c12a48058450225501d074240d500e4868061140d8025850145060b1401350781e6044280320f0060502a10504548030000b4000c0d0302000b03084030b5205034420035480400c50210340307081100101500785001040707030b41d907506070351011200b032107002003808042c1d80b0701050340741c6081c0e0780d25038480d1002c181e0a0521 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 884658624 1250 884657374 884657399
    0xe16032c01150b25021806090a0e0a030f05070f1103070b040308041e0906030501060e250f0210110c240123041803180303050304080f13 60
    0x6038034400081108000b500704555120800d070160303071940d03c2d00300541c0150201c5078864051010784c801c460000c0084950010765010090740000410000c060240002498021034158000132a414100811000804806c1e160194150040d042c03000080565031180e0060341143c9441d0341c008075412542d0a1072401a0140e80100302ea64042d100e101d00c0850400003800c1142d081c1d82e048102103003001d140c8860365042d0080c40d1318a4107040700400001441e0b030141d010711409144140300105071241880401644100014201b03e2541c0741410b0602512800c0c1c42000c046109a10b0f1003a0311905031340080e407514070907001d10347c540da1a0480404a904003403000d8080320b46480e0550b050401c01c2c290b4030813684116910f40d5a84d1520400410503110290900608144808a01e00d10820440c001804607030607051408981044410104100b50307125840000b1100340b45942100c0a065840c02000c901004100030102a800a00d07849102e1041d015650a0403031401000300c1141c8440100241 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 884659874 1250 884658624 884658701
    0x5040605010501050c030403320606031006030b06010305090102190207030b1015080a09020904050c0405090111072a1206150509070309030320041d010e1603 69
    0x5520344400850190711400440b908008002d00450034103085407250400e400d0350b0a14030480c0358080c2e0840700c0022600003a5882030301c00c4c4000c0e0242d4941301d0145418418200018941c2510303002090001a8203606100d8202c3c0c0c080c64005280d0b81c40d0315905009208011154038001c00b0038041c0410b441d400160300050324401c1c1107800958998402c80c1c0804074040c000d003820240d48503d42e81d0554810389241d94456810382002c00c13030003142e8020462420041c1c0b402c0d07850350070208011b56070342440c0c042c1c10782005424000704120103000c6642d861714051804010700300d44007034015005080c4843c00164840024060614130203590303400c5603540b0340000808070340c2c060902101c0032141c654a90317000201c45000c1d21010702540e44d41c1003100140396501c0124245680c4211414002c0307180d54000840000f201e001507600c0b400c08241500b140c0d145130a0140f03000507080148105800100516000100c3c2c0707500404920b07030781409030080e20004503140302801c1301404051380c0050040c460348c00e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 884661124 1250 884659874 884659883
    0x602180a121406160f02030403020d0b060f0a05010806060f120a1e290301140f060a170c04110c0d050d2316031104180e0601030b0c1602130504 63
    0x310610b10015a2504411a40d02d80e44200509540300c000703000380241c1c1100c885a00c1aa4a499203941c00140042e400c000280c41c070440d036001304800d034280680e4400e00340b00119400403801d850000000d0040c2001010140100320118004101c0040c1c0c0094800701150031500300e11030b20701080400c00070941a10321400c0e4440c40d407800908031443e0b06c140c170018494000c02200e981c00c6072000742d04988d20900855055941da01400218080034600540106d0780c81d0b0a403246070038620100550440a41c00c00c00304188440c81d21624048009400c0106007015200482c1c03100034030b0103400c164000c40301c0d80601c500501d41c41c64bc00c2c5038050010503074420300d003404228000906222000c03081c1501082280c800f0b0000210307041c0c800201245000f41000c1c40c01151001c420062006180c04c107a01c080d415498682c50383c0e584105034013410800c114500004c104a40c5561660000d0000146c803602c00103000041c0e0481490309260054141d9402070007410300540c0e000c0c8040001d240c100c0e400d03603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 884662374 1250 884661124 884661143
    0x8090a03030f0b27072c120303070e10030c020304140109080f0d14070b04060b0a0f0e04051005070212091f050711090108100209180f071106130602180a12 68
    0x109032038003506c45803100e40115040a40c1580d001c02481c0c0e80400b0b000d4010354810b000e020101e41d400d100b00000c501c148810755441c403ca601035400c0c04025810700300110241403d20822a5140b80e00100341c030f0480d400211004001e005100060710700e86104d805c0000e160140070000305461400003404598020350b0741c1c49030000700300564080c00c0303400780d14001802d000c0210003080118507aa00b06400c5001e0040104500c588e54842603c0d19040540c05103100200c0c900400c03050120a00500450000d4101c052146181c400b900a48410881c205001701203000700d01742c01070b525000c900310b0052140c0388040303080c0300201c03002500c1500044c00440ba144010200301c4002d081c40302140d41203c0ca804010601c0b84481c8a2840103500b001c2c803d103030010481c1c24801c2c01c884000e02903d0064070b4a80c512104d609103140000c0004001c1103050710719900a40a001c8003070065100342184d61b030010070050300d42104104407440d21807620f2406501122241011800c9408060705100e685d20503180d10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 884663624 1250 884662374 884662381
    0x606070602030708090f0703110d1502161406040b061302130b0417010c050a110102120112020306070201060305030708030a0e0109050d09060206040c2108031f0608090a03030f0b27 79
    0x160f47c400c5d0078040102034000c82034095509061094510404070b118601000360440c01401c030750100c2e0000341e0780c100d210410440001c01d1014440c1d1007513041140201815003803034039032990342100c0e901500b441e0085182e0300a04101588580c1940d406591102448010a035201003a60480c0c000d8022980191041440c2500207141441040314021503074540e5410004003030026074103280a000104038a5408000c0315424120b4594024007070050140200700101b41c42c0107051508000420034425685446014400f145000058600c11640314207215130781c1e41d61441680c050090210240d24a41c20b00c0104820400040703182d021526250740d40c0e02d030256491030107d950311010f40c0c0141c5460200c800074406864180440d4005403165100aa0a140c0341c0d81c995080e5401122031035118112081c48100424603694103000528aa00d800c01107420010007542e1201806400107083c9135682018030413900554202081d80c05001340030600c05144101e00da06543c4000c84944a01c82d01c44000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 884664874 1250 884663624 884663653
    0x3050a1a0315280b0f1806010e01020c130213050a030305090402071e0b090609010b060f0c07120305070605010f08030a0f020f070902070b160504030303020d11030415060603180308060607060203070809 88
    0x1181000501c0b0481500c7d803200001950b802030310080d120b045006030203000e20591164004110003007413081c0c0060783c40420082c60401d54003c0e4201500c9820214801c001281c0c0c800141c8585030011200142d4070205c2d8078229440c01c034122040498503070640c1c01c40092015108071544500c0300c2505403440c0e5a20813400d1401c0754552070300c10742d00c901e05002150203090501e01800048920000700c90880b40c44103010182c0d2900680102d002075000070709402006aa405500d004060b004407002c1510300f082c02d01900c0740640090001004660100009094801c004ca10b00b0400c10f081520740d05ea44410384000030703500400003907810011020200320301000c100881e0204145555034941003900313543e4210042d60081018440b1240c5815920750510f004c01c00440c0610310565200c40c01e280d01070700020513104a0f0b400300c01450f282c0b070505070148003c0c0e001c003201e090781843e001400f65102400903140340609180502000c1c40030040010854000e40214050740d80c4c14215000c3e12082840c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 884666124 1250 884664874 884664889
    0xf0e0f060c130e04050a05010e240f010e060d08030106030b0f0f01050304030c031107060c060b091005060c010204080a030507140309010f052803050a1a0315280b0f 72
    0x10a01c80915200b10402021500452041d0010b103d0010350342c58498a031580e60a60b8245d985000894003c0350340b111465084441c420303450456081c46a005140c05203554000a005100307034070009051400091751136071100b24031006141d000c4c106c0c54507540c4070b5a004004101c2c840c0a10b004100568a00c2c2041c5062002c4072a0018140e55483c6103940b1a42d044030201c140010403010300001c0c1c0062000020f00b8005030000d4486603a84401d00d07459820300c40d040d5500d0b40c070a41d000300009000d0021783c500d00390b8000141c80c000e9130741594130900d0542d03041c02031041e940442c0c0305000c0c40100f1010150f100004041c641e00078603050240144070f00100d502ca10803000400c0c0407900591584081ea80940b000e0445802c4c078010305081c0307003d1aa14003c554003c944281c000aa841c0c04106a01c904c0e0300c45e0150302084540d02c2003189000a000c41d55403006540090242d140b802c00065401c071551112440b0b411600d42040200c07501503d40c41c1c0075001540c40107110315110100100241044070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 884667374 1250 884666124 884666137
    0xc0306020913050114010e011106092b0c030f0c0b15090928020a03053c07170c061201063009021c05060a0501050a0e0a0f0f0e0f060c 59
    0x1907a5005c004600b00542d20b00b1011080e032414000058808440c1c0f003010f104a620440d8a030002d0b1010040c0c9140f001d01220703040c0f00a1203403008a121000c0d256501425000d10a41c0c51700745000b070881c4148040c0c0d10500c070500020803000700081000744041440b8003015110702d0a071550760485d282e04084a0700c0e0b80007100012030b031091a0690070500c41040d580301d450140042d00c88503c003901c035180c85040020600400039031111800c0c0e00c402030410076505501c85403920030811410800c0c0c091180c1c17652014450094020010402d15010450500c0780901448005040c1a03480d00c40119064154000340f0802012803c1c1205410004400000403880c658110341540340401e100c04041c401400072000a0741c10009040d0302450051a080310002c82e14059001000149020301250094030816004036010b1720301d8020030000c00b041d0900c2540c01003116540802ca80d000141c84c0001000c14042d000c5540c1d08105005100240c0411800205200c51040d1007465070b8143c04001c2912444 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 884668624 1250 884667374 884667389
    0x102070c080d2c0604090504030e090c090103020705100213090c0c1509140111091c17250809013c030908030a060e071412060d0c03060209130501 64
    0xc800c01e540d8030344254000844403580d0001040f08440700000300784c40703421035007011240359030f00c7c4c09102c141074010514690100b01110900d8552500844180c46070044901e1141419008943d2104104080c4409620801400c4007103489548810a190303032041c0c181700f4915054600007191640521800006003455004850880161840845000181180c2c070040d204c07049035001d00490400c0a01a48000012001c881911a21f04201304108107440700c0d414030380c0701074260360340300081c0401e000e44c803210030074007419622a039000445c20f41b1021000a6500403010803074084003000341d40409044144003c0c1c3c0c89044158000304180c2c0e00c0c0881c140001030129090480c0212001a0340300301c10700d10468075020031015040d40d40c03001190010780f10407103440d80728007091090b080c6506035954484160705d80741d040c55000c1c0350702c0b82ca14812031204201700640c1e00700003403040d125421500071066010030525101c903544d0400800a4200c1800c00384500b0300440340f1011144079000c1c3c40e0588102c2d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 884669874 1250 884668624 884668637
    0xa09170a03050f07051516020f0d0309020a1a03010311030105060a0902090a120c03050c0319030f09031505010503010e0307050304090507030e190506060a1409270102070c080d 77
    0x80d00c042c0c8141d04070075080314410100300b10040003e4024003002a8498440c00c140d181d600704511541c011080202d04c1108541c06900c03216402400003c0b0700301c04c414a82800124042c590011132441c4945402032069181c60740d00c44100340441a00441c1200d0040b80001281c40018003050300b659425561036501001ba0b9605110340c0320940c4c010808083d00408a002041e611403031005044402c5c08256110005030f9020400d20005000703117a00c030300c4100c02411010740d0381d01c0d6055115504100180810040801810203d409504040061900101a000c08a01040810015140034041c0c54025401c000e007130b041c3c2040000940c0c01c10399200300614245802d0541c198000c046c000c0c820020035072502040704000f0000c3c0310a40401c229544d943c44c080d441410f1a41c642000500081d01070b680c04001084a001030440751420041c2c00c840c0c5038081d481c1c40101d072000c8015650b8121480c507040300800100c1c04158004c00307804e8416464242c11641c4c0386501a11607107a6001d62010919 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 884671124 1250 884669874 884669893
    0x1803080f3303100c0c1209050a14091003080301140a0b030a15060206240411310e01141305090a0c05041103010b1608040f030b090a05100e0705150a0917 67
    0x9003400e1b8924581c40c00c040f140340e50391300041c6114419840621207504a10041750181001002140e00c002102890f20955180d036842c0c61030740c0b105104001c0c04d99800c9203507000640d00c001c1c0d0340c0020001c030bc09094503030400e00c01e0040180411041d0611091a10341c0020703003a13001042d0342c3c2c82045241c1038a50402c205202184940c00c5000d22140d002d5503810345071308030020440180c1403100b82044041071300301c1c1001c00c845000300d030710110820300d0f000480e0030425981100d4510341075640601c810280c0e03840c10303008580c1078880300d100107d07814107080400008000000c5c030100194058030011007050342d80c0c410710089070b100b032070311215210f0200300510500007100010620f0300c405040c0381100390055117403030074150815004200e045040c010100f00707020b8040302e01030b044038035030014080110203a40c84a0340e8000014009043ca5100c0c41c058102300c10902000c001400c01400301214030905000501d1240d210407541c0d404686c65110108040c8a17100506001400b0400204a1941c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 884672374 1250 884671124 884671133
    0x140a09081b07080d03060608010803040f05011d09040503131a070f140312060109091407200601090e01051e060607062d1803080f3303100c0c 62
    0x40e031400c001c180c0c61003140303000514484100301c81c0c20b4032901c654000070194103007800104090070607130003800c542d40240030511068125011542c102c2d42c3c00d003410301d412601c2c04d01480b1a18105516260300c264110104030900070044001d0881400d0854000340558844121240490301300c0200400d880c3e040c490000081d10300308042031140d0041c4080d266030408075102a256504c40c104101c4070308009018410a0758102c007404010700b507001014820b000c0c04904048141600900b03140400048054845015810540780c5003460cd80d44141c450f0340d81c440c810f50000c0e01d00b80c1904c8050707610f0440041c1c401c42055000d000c00114812010b0f40e6504c3e0388082101c0c58100324026255180d40718845400300800310340886c90307130840c54240d00d40b0522a040c0179003190047d036460310015849422010000740e00030402c41d0302242c0401d41c00425180c21254980003813150f400003200180d80d074800440c5101401810742c2402d03080703045039010814106a44141c5001050311008601031090300c03000036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 884673624 1250 884672374 884672407
    0x42127030b04080912030d02181002030a030b01030204090c020303010312030b06120c1c050f010b03010b120c09090c040e0c1c02092b14010b06030402011b0501020d140a0908 76
    0x4120081c000c51030641d08401446c04c51b13102c8412a200135500080d003000810809406c1c0005820486021401c0502d4807006910391080b00800307010542c1d00c0d03000a901d130313010313a0541c1c000d00b105180c1000351140b9810060364070f520a020036608104107050b000c013a54841d0080b01c20508010b00400e00788800c2c202812102180074110380900c19040c8144071600c2c0740066030a4509000c1000402d00c2e041c6821104582e000c1a0442250407104000600008070781f401100c81c049103522400716150340c1c0751641b0502e0302440400540c0100003605220b0722070803070000b0380140e030206041c842290f19209000030302c500c0340100802d1070030301d804030301c013400f01240d03000e00705541000c2c00050009150300580746d1100d50000454070f0146032000818244003a0300c0c7c010f88100072100003040000b02100c00107605000007040241000350394074035079440c100d900e40c000d102198000029902d43c510400280058200a03c80010036110840040c02c000da0300c0c050003003080c2e04051490301e81200d40d02c0710583c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 884674874 1250 884673624 884673637
    0x1226040302010f032301230603011e0510030203061003060e070e010e1206070210021201032406081e010506090604021b1c0207050a0608060108042127030b0408 70
    0x50642c1c0702c042e50445c0c0d01030080003c2c90211300030304074240d604191402c0214140b080355045034001c2c01101c802551540c81c100c03410f407034221011400807100310581c003100403099048107405c00c10f03001c00c1d682880c1d0141c02550050304101c6d000c0c07080c607007040800c404880317007889414a00c0300311802188410780a032005184402040c908029039100c0390f40411502100748485500aa02250803ca00c0a90510402403170f80701105043d03203003594a010300c00c04403406000203000d4240301c503040c40000c100304c2030358484000c0542040c0682e95813100c20548030403013442500c00454440c18070141c26035040c4203680c8030b010010101229604c51f0002d2200a4100d040c50f4010344c400555030600401003040b05600f420400054101e1181c1c120700000c3c10b00d0a1503014500840005206003c15a00a503d1541c004020b1a10440541c1c42d41007888040e8102444007040e1170303030419140b0885901603108213100c4120100e4040d4030708952030b8400d005405100142908400c00040343c000345411009204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 884676124 1250 884674874 884674877
    0x160606060203161101052b06050105090f15130f0e0c04081509031c060f09360618050601061b08090a03170d0c0503061320041226040302010f 62
    0x1007503008441d00702d0b01d079640c1034004030603000f50407601c811f035990b07009034000341c2420319220b41407501d070b040030078513a400300817201e0b00c20480346440842009411044e5428041d840e40d445096907540c02804003400054060004034907030050000303e1f81e107541c5003200c0441d001c2000034400c030312220f8183d290600300a0481e0a03240401c002c1454150140c07a00c10b40c95400b2a01d0001c1e18610b003890032030075483d131607000b0803d890422031160309052424400c5851000044140f62900d030714040354580381951210001d0045243c58200e5040c1207060b0140e04c1003e100d0400c940003642c03144001d40e1030004407640d020403646420403203400a1040c03009020703421400b402500c803030ba499581c1c00450f100c0070360440b8103008001c203000c5054281401814079101c118100180707076043c4400441c20344240e8020403424a600d4802c4000580e540602c1c403c00b0088252100c4c1c0c6680d01c416403401920481d00c0309076505078400d00c50041c4028000c041c800007189d101400c0c1e00c0c051840d80152100d40c240700280c0c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 884677374 1250 884676124 884676127
    0x90603150b030907060e03190b180a080a110a0b061309060e03070c09090218040807050a060507021b0a1205100e0102040f0b0306180901020403050316060606020316110105 75
    0xc00e201c0010180d801004150f024005580c1403480044c0344007110381d0560f12a901010310915040081c0f40c036507802c19007101c5402450741d151001c2d100302202c0400c441c0c5c243d1040030461001d01800e0030103003541802d40c1d9221038260060780511596400348a1002e44807d5400c004a02c0d540b82601104582d40c0c0a40350106e140189525484112028101d107200c164100140381c20410200a50b02006060303110010440541d080e000720300b481100d0940002445801d0001c2014843c1542c140c1d11031a50210407540305040e0f6290402c0030f040e09413449405881242450000d9403000c03800c4410500c0c1c05040383d05a10700c1c00031411202e03900e401c020b0b119401000a041d04c00903260250107039003114a400983c0d103034030f001d2a218504106921000c2c1d101000e006012a40e030300c1400d428401c0b295005140d1654486004681c024842d5501c014014440041d1030400101c10342e8415600a0060300100500b0b41d07200e0050382c42c0d200354a140c942d00c21101c1c1e0101c001030091040d01012500c10303d000e9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 884678624 1250 884677374 884677379
    0xf2c33060408010902030f1204090b0109170c011e0e101107030f0b010911270604061716020a03050a0e0901032004150b033607051009060315 62
    0x120503a0050300002d1050b5120a03440065040c00c00c916880b10024a00501a14410342c0001105020301d00404000c41d44032490744506a104803411001340c40306907801003440c01507010f400d503a0600001d10034041051110070000c01540d0f9110026542204d071100c46608503075004009a04d181545408c0c02d06c580c0780d00c0101c40c140100403541c003039449400d903680440854240104010b070705038440382c149030400c0441071200164801303691880b400680d403a5a45540710103c4400c0b06241021640c1164020400141e5954044031810641104ca481c001190319114031440c03001030311448600150340b000492100081c826402004030402525100e44110724400004480140a901c15960b4882c502512040345102c0142000034420488040140b041000c2c201000c0003040c0c0b0403942000404000241c0d0400c0c0741c440c0f0130200720a20101000c2c4002c504015002c0074030000011240e03c00ea0b0008161401c2944060801801d143c0310710414038a40203084000d04828030050f0440c3d20000c800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 884679874 1250 884678624 884678629
    0x5040803390708010b06031501050d0f0c0306060315030809091504050403030c1803030207170309060d0e1005011202040218130518070f090b0a0f2c33 66
    0x100d14010400401a02d000d91500c80102e084d6140c05640c50b210321010424003840e014100c01e13500c0305810070708085440700310307105d0b5910041c40b05c1d1580c66800d038200b107180f40c88241d0540c0100161078050b20200042d14181c108000c072054140002090740b2800c20801c1d01c40c1c07410703846e02540f010002c20301c20036a860401c00b0505441c1c003500c003240480d8490880e001443d402801d00d680c04213900c501961500e02e10f0303c00a540f1561442142c41000c030550040e2041c40e010b1044075288040a807005075140300d000c41410040854000d00180340c060719052087c80011130003000d0403114404100028418640c08000003980240a42c14103094685507580d0243c452515071506550203810004043c905488071030751204a840007150107400c0900140210b544950600094528003100040c0015070307000890690811a0050702418034450400a05169040010803a00881c91510020354410440f5100c00d11401e4803400d02404070600103140002a000c294048184000c40309103800c1e079140e01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 884681124 1250 884679874 884679967
    0x2130b030c041502030327100f020403020d08090108070f0503070302210f04020f0d17070203120324041a010c061d0102040e0601050c07030b0c09100e0103060605040803 74
    0x1030381c80c0903070030206c10041e00002d00a08049013070801020548024000d03041c04d030701c0e40b802d0700358200c035075aa50040864083d102d90550b07014503400780140c800c899450030244455000848a513002135074420010b001d213071081c950760504941e0340d103e240c01c40d2120003064001e5000640d815010030607961113000c4e110602d9032098001c0303041c00f031a460181014014440605d061580140c0203900540701d4030001800322250030040749504280d25140d101c0d0707100082c10503803030100a00c800d11002c801c0c00b24048405031940074410600c01e0130120750348440d051000b911b01078103603d0741405041c22220401c2d4026151086854442c2000240304200400d82103000d107a402c000b2020f580d40450180a4107040d0386140d80c01c44024240682021020380c2e8607681d503080da010041c4014521000700c4d030359801c1e54040e0b4030102c0307001300a0917451030340ba94010201502d917610070340000c0c01d081c00000e017140580d0844043d600c074040514685445080d502104000c0000005015074003042c25030290342003103c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 884682374 1250 884681124 884681159
    0x150c031e05030619060c061503080408031b010c05040e072309030c04051003082104060e0105070e010909020f0f0a020619141513060e06031002130b030c04 68
    0x71241a140d0501c0e4090000726012130749034458410700c55105000c086d41110000d2601903210300013184100c60703c041018102070681c80202500c07400700707011505000c00300c042c26045850070b6000d06c81301000c10b190340c2601c850160b06404100100f00a0004c0350b01e15111030792102c0d440c1450b00410303503c0b0428004402404103000f10020000c0b80300c1d003091030244003100750b030355080764180f2190a240c01d428442040703621004020100022307101c0500c0114081310011003100f243c03d0041407a103400d04c0e6014003614000d100349940b03008006007025002d01d40c11040000c0696500000504044161000f03500440e58014075120070310280c04403003a6a4014031a000071580902401d0800954a00d0b0307031040300c05c041c2d01590400f07929201a00e8021900e40c0d001400b0541c12060324000008500e00c12001585223a800e42003060100b0310a0b040080a0301486040d401c49004070950b0140d42c040780030f1100001c42400e03070304104200c00500f4030080c0d60080c02c0d90f580c80e40b409a079001c000c2e640340382c0c41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 884683624 1250 884682374 884682377
    0x50c070b0a020709060e0a0207021512010e250503060f0d06022503020a03030c05090d050a211b020f0901060801060305010b040311091b0a03091b150c031e 68
    0x190401d03429418044880240410807081c0690303410481c200c0c48082d0002d00ca4070406902082220655603407607841150440922001a500c414401d08071000310b03000d00400454110b210042106070001e0640c007100b41c1c00d00c4070094920807071444121050392000c5c0402d580031015415003501c60766155080404503105500046c0e4941608980071801c01141507c41d040d080000001d00c003103900801d18401c022792504d0001090481000c0c250340724042c1084164005034000c90000030004c000504080d4140195844603a01c00c1a0444100d07105080301074034000b500c071100c2750a50000c5c08079040010342c07000b0320b2100809064408510604000da0103035000030202401001b495800d44101c81c0902210460036161604503140c14000004150656001f01c0d40c141c00244082005500800c202809d00d41c00396950f01091001400740c035402c4003c5d0f90a026100e0780c4240700541090b000c0840706000d05a54080720000c0d4152903000840c0c4055050002c59220a5040c2c0100740b510000c81ca03ca = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 884684874 1250 884683624 884683627
    0xc05160b0702030717191e0602180603060a0b0d0b0315070e1c0311070b0d0218060301210f0506070f0e03121c1d031e03060d020907050c070b 62
    0x500400d46058920b17031050300203480d030010440d2910004a480f00551500f51481c00c2d241c5a41d280c0f1081c581060400c064082d09446280e60400a00d50000d08003441c4000c0800900796260003000302d10311090341c100d40c1c401c000402c2003007045c5403940601178540c000000050303150400740109007480c1103030424082d0200301c002001001034210520000d0308005480100c581000000c0000000341586009818803000d84c11080250004101500c09001904005c0303071502489401c000c040c0d002207103200600b0002e80d450301c2003410b1803010f50b8100c035044030314103070400000c12070001e200900750b8094504904402c41031002c02c40c200411030040401d42c0d141005808070080090880080180c0329100303811000802000032140f030b06490442400da40130604070740644121000400626915000f40c0e94440100c840c0c048010000d030444881c00c080b070700210204608031075200c1c0f000f181d2203940300c0e00c030040e540054284808107540c00041070a10500e410745e007407645490120b040d400711030120300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 884686124 1250 884684874 884684887
    0x60e061e040f0605041202040207020f131b0206040213050c0f030c07020906060918071101050a0212130b07031a0315060f06090a03020910180203070f0e060702010c05160b 75
    0x900b4440702c4000e01591500c00d040a061501c80080c000d91410040d101c0c1d40c000c12600b0a5584806180d9000207000b050903c090007008185009802440ca034040c43c90110402a00c0395400480c129201c1c99000340451402811006500018800540514480d100c2070082d107140d1112480214007454901c0c203269110303081c40c81000103401004000a016000c244001c48041d00da090740c0700c4a02141c031141c80303200c0e62902c004452440c40304880354041e60a04003030002803119075005000c2c0303c0480c0740e5000d040e5103c1d0780c1d1405510402600070700a803007010001e00c1c214825405100e1a0b100c2c8585480c011601c03000180c500002c4102c9280a44141018800c07203251940c0040c0c089682658003c2c144800d00740000d4090044bc400a0700400d404000508080341c01103400303015211511440d0307032502000c1c00c05802500103c40b03250209003140d421260b060301508100c404140c0040c9024074090b001e6004507003691051408440600c256070060080c4001c03c05094050803a0112035501c40ca03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 884687374 1250 884686124 884686139
    0x61410050907050403081b010f150915080a060b0d080a031a09090a0602030402040f05010e0403090501021b040c020f06010603020d061508010b180d080301081006050a060e061e04 78
    0x100a800702c428400c0c2000308000203a070388404d5840604882c00300c0f00c1c48508200055016085841080028500c2e249043d0340358203800307903003100b9100030000407c59034075942c084d030044a00502480340650b11210707115000034003d0f045503001400103031034600b10801581d1440482e800c64100744d0302094480740400c40c1085a4044031030080e20403070300c1c0c152a081c45100e4645481d480d41001d011315030004000b83c02d64640da04071304031082c003a942c10043e9681d940e060b0401c8040548003140020104000028150710002c0c2c0c0400c40160480c0000d0820340d140108402082c424082006500420b01186e82c48070b014030940c0e000704503503200540e844034030079810313803c94566410500d505070440701c182e5520342c2c0c04859141508c000e04c1c03005585d4070040200042c4e04d0b140e0004180e0000711251a9400c000060010b54102e076039902c01c5030f0041800c280e854068032803602070581c100c04500300400031548100216100840050043d600c0c0c030081c618400a1a0945440020b103400d00140c10000c45 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 884688624 1250 884687374 884687389
    0x60e06150f12010920011202070c210c060e0423161815080901050402010e06030c131202010f02150a0b040608010212070807030b0105031306141005 65
    0x100e501a200305400c00400041d42440d05403034820300072036000c40520740348042584121461340d00010502403030b1180e6000403c02290b80c1d4145d50000d0350b030b1404811400603070700964a8666129484d011480c1c20911035480c0300041d0032110300e075480783e00c02e040003140c0c0c64a040340c09055107a03610100540e844c2c0500003a14407682500e40c05800030f1101070507480480c01200d41203400d054100c9407429100ea021541402204113040191801c01000101404c801d81000c0511140c0d403541005130381d44034801401c171b6004030f40c0039001c41c45100c00d180486c03400e03000666020711b20003141410226850803e4044061039000b090001119004c20b07000e540c0c202c1c2480350a0a2248001d0002120b0421440e511748000f4004d1215903840d840d5480351aa6240c002c440944240302c001c40d1202060810400015019590b11002c1841c040108004a110f8082c002d480031040e1507aa2550b02c64000c41d000c40911980180ca4107a625000e050801c840c50060750f014604403813900341141d00305410030240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 884689874 1250 884688624 884688631
    0x9060e07140604030b010b0a180b030114010309053d1413030f05090301110a05030f0105040e0318041409030403151803050d060509011206060b0f090d031704060e06 72
    0x202000c3c4030410008809201141c1034800d034080f41e503100d0300501d80503201203100700c02d85904c144081001141c0c0041c1f480c00b850403038003000c00000c0081c850b440190211003041c0700140454000141c013141c0e40c840201402d4803440700761180800c0301440b00040030703803840c03008040d80816103a40c00300744210410070790650803506800245450f509540c0c1d02610800c5a51007843c01e108022a0301d80e030755a000c0d4072609401841e80d06050b0742c1d000c0141c00401d29801141e40740f0322001400000701d601d0902e40300d90300c2d804003d1802180303002007145480c001e4401003846554021384a03003203a683c2909402c016409070b0440b500031500c640c118941541110404542c0d0550a40b400382d25424900141b03100d9a00103030141885039a89180080e0140030300001d811103908010360900004207281c2400986244074000c00003000720580380c10b410710040c82a842004004241807080d0202c51a02ca205045001d202e41071410700c0100140c0100200e40c1d084605946c2e207555491100c030340001c01d02c1015072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 884691124 1250 884689874 884689879
    0x8060f060a0302190803031602100908040603151203030623090c0c15100518060303070615080607030b040c080405070303050a02010e0318010e030a03090905060409060e0714 76
    0x10315010000c500364255074440640300f200d0070f40204152181c4a00d58602401e03c0100b925030341e14003060702e40d030100c0303900c0e104d000144166400004440c100d0710407080701913030100d4803d203094a0f081084000d404040700d0f48209445081000800c1d40c030a801c2020b200b8801c1c0c030080717501c0345031070f9071104000c44c00c40c0c001c120915518181c0c40203a40d14041280d110801c0e040080e01c0b44044c04130a440d102411a2410b00a02a0418000040051134042d41210021038047d004002d1444040d40c5080055402c0ca425900170302c9584001012600b01219070700400c14865521541c8a81c201d250000980ba07443c0443e83d41d62140e5018141800b40040700700c0d09091440c881e060640d5110358505403071102504210010440f84111407013074005800c81c0180c4c3e0116901c0b140b9101c0904480340f4400e40e0903001c114412229205810041360551025403d92584100c0c2450a08000050207000f0405030340703d80d450305220002261407181c03408019880d0010840c4606014804800b809049115807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 884692374 1250 884691124 884691151
    0x10509040c05010c08090d14061e2a03130b100e04060507090503151e010510050c030403020901180b0108150409020409170a09060903120507020f040608070806 70
    0x10200390003040c0d00c801c44400f840c1804e040c0046081c100700c01c1c003c11007550f0740006540114000d1100b50200100e6004d42a026078920780c0b1150ba640507240e2040102d81e501580040001e0f20881444006503103040c6124501009240c095103207101c42c0c0d000306e5513038444082d500b5844c0e05012040301c42a51003407210380004203080c100494a512128000d00080902d521080021899071040058000404020341141c2d0400103501c0c001072501d1003100c01e0800101e840034486400100d03524658100c4034040e005800141d02104212841c0d840103d0b01c417060700c02040008016103901c0b500303600a0211076500d00c240c0c41c0d04003108098800961290f410401c41d602403013854800d040321686c949100700d03000146580a40b010a0180074000340261900381d0349100d441000c2c410070001c09803414590350b003840003600c9810039955035590303000142025550520500040780988010321300640020501d4201c4401100058159116074100b45003542261800f044480e6042022030b0f0401710341c4030300342c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 884693624 1250 884692374 884692381
    0x5160f06030c4410051c02010915020f030a03020c0d1d010c1e0305070b070807020709050a021e0a14090f0907050d090b10080a0209010b0d0b0d05070e010509 69
    0xc0600310090380340680d004104a9050010b02d80901c080c0e03c20040c85140e22010386000d14203089100c00314810103008090064500c0841c2c4907078100305184950584a5000050500c0d814945001c600000745040d44150b0103082c8900d034080000d040071143d181c0d400b69440c609102c00c5070600040c0d29600c02400500c00050900d03d020300c0b0360042902007840c2c402c0c0407007443d00b421704060540c3e2503550420700034103202d0020f255100c0d009140007405052064040c0d00e422074100e9a0ba8011102440140c014041c24083c1d00c0c0b407500300355004001c40c000542410000c80d042891508041901d04407501d002034071000070b503003100b6588030003c80180312a040805c07641c04214240349014507203202d0706140000460180c02842503c804000c00c501c1007284c42d0b228502007609600660b181440311403c00303c0010400380000e10411480d50207404240c89911302130000f03020b6045001040c0d115516030f4800101915582800400c0074007030f6000b440810701e0306144d9459508103802140c06510b00c0c8040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 884694874 1250 884693624 884693657
    0xf06070302060613061a04060305090304030b0109091505090a0c140a090906060e13051c05070b06031905060f060609150c0307170904060b0c0c0d05160f06030c 70
    0x42d903600c0702c8152580103000c2815a5003100822054101c40002e000d0b98034441090861080900159406a1003c00c6035032a1802ca81d5681e008a210007004500084010702031070901350420440303a44a00e00c04039003941c850f90704100343d270303400c495180c0141c0c07000391740505100110321500300a00c144031400341315500420115200da85103029a0818030340b1005072004000543e80003030300501240302d80c00b000e030400d0b81718a12064140c0710300313070381500c50303105c80003a5441100e00200b550a129240c042c5407a0701c5950b644008440244142c2e4940105026041039080705602c2c480b2840c81100905058601207050001d549000b4021a000303010030700c002241d43c1c59a42c00e00c08a110f0000ca520389036101c01d0496490343c0b0821600501c149110300c15031140020305030140070f83c510125001d00c00c2a840c0d840900ca1030186000d82c50490740030038071004c0c880c03d01401980c0c82500400a036284074140f00000150200f80703074008040e00042c030200700100d50380761088000c43c00851401102c62041d00d000d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 884696124 1250 884694874 884694883
    0x7030e0a020108090a0506280510061803020a150809060115200d111b0114070317090601080706090b1b0c03010c020c040b060f181c050c0f06070302 65
    0x3814810311001013401000100080144254080708551072468803070fa51034500c0d01c018048445c0c80c8a50760a07001166030b10b000f1603104042c49866a031260313250010840c1d0b800440f1000380390b90b42180901101684039644450003514840c80038036222151900b0003031048200828400301904400014004018034104c40c00c1a5209440d1820803900f4130304052000f0b80020011920078442d0f042c0c1400b02d540c0119140c00c40c10030b4502610710000302d0403405003091054103c181c0c00150741182468030030310701102805613030340246883d0781c400384403d10f940280c0d07a060750025440d501410040010780e0042081b4009406e46280c0840e02d54501280310009004140a410303002c030003036554002141d010010074100c0b1b00d000340240f0412407200c1c0d0103501c0c2c030180c0e04075602a50400308507590a041032000c0b50399030010401c455142011095158200d41c10f04e500d155407080c41210710180c00b60f94102c05585d0395004401600c1e100200f21700b0000803e11a03000c1600403c424003d4802003500400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 884697374 1250 884696124 884696143
    0x9010f1701050c0d090c0906080c0909030306010f05180402040f1712030a180f0b070305060307030510051005120f010b101209020f0d03021b1203040324020409021207030e 75
    0x440401c40c0185ca14004101e5150758002000c038a2070030394000342c04000011039045a14090740d0300b613800d0320344444050703c7e0700c002c0703030b0590104241d810340d5100c80384124001c0641005044841814044000c002010f0b0303403141d4050030456014810502299126070758007844c81c8800c000400500e400d80e020000c09000c000d000706e407480c4c0e4071480700d40080bc0c02050310119a074042c0d4094200142407402c4411844280d038010002841c20000940c3d46c200003a581c2c05a075001402070a990210802e0180540030040000307248904121340000d26442c1d01c14400b8141a581c0d02800e00280c410400d10308544010401c1c500c58a10000000200c6401541c0081260040100410010321a0001c03070711010102544542080c01445610141540811030b13000f1401c0c0c0c6040b080070300f0504801c0151610007412029203640041100700300194420006d5940c80030640101244c04102d66010b000300e821960248031f04507000510385002000b030545007070b801606414200060902c000826a40720000c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 884698624 1250 884697374 884697397
    0xc010807181220031e120408010c11010b1528090801050f01032d0b1008010e0a0b010b03091009140c04140a0e0f0717060a0e0d0c0f0209010f1701050c 66
    0x20403002c0708001092080c40c0d1041c0102c6c2c4115502c84e0350301d08040c020074403150340000080c915611600420018064480b030745100078191104501d6039190241c00394408005544c40c0c4001c8140c40006100b200d240f90001c081d00d4848011040c0b030032a00303e095644c020030b001c1d0b003c02004010301c0001d00703c281040080d080500220304500318401079000d403d00040000d0100b0700041c2c00c10551203201c081200c16580ca100003070042e10000740c0d00650300c9a0081004200d140d1240050102480880255130f1100c058001c580304052907603014412140025015a044500002c401c04566010080760303400e070b901560100714010b0800d1507030382d0001e40a0038280e43c003500c604c40520f842200304450342410039180c0c113403240c890341d0f04805c540800d14211240c5042c05110001002d164480c8984500d60541c0005011000d0440740d080720050380f50001207902d5001e0603a0600580c954540da14040d187c1d2a0a020000b802c18548113204e291714069504c803030f070610040001900e07295080d10340326141e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 884699874 1250 884698624 884698663
    0xd1b060e03120c1f1b0e100c030c0b0f0f0610021c0314090d030c0215060925031512022b051005270c01080718122003 52
    0x10980305050841070a1000c10f088903401301d0300c21804850f0b02c01c0c81c003404200d03600800b120641ea810703145807040004450b031100c896480a041140107103e03a1403028841c0c5441009100181d4800a60130070035140c0e100b00e00010810452543d1120b1041c0e900024110f4400e0300181c8000e000960712156040509492561080d2003030280f030180c2c0106c0041c40040242604500c0c08031410b80d03035001c80e1001d0500182c10241c0c7c1e01c0391280046551080600c6000b0030b0302d116a1200c083c4094090301800038001046c0020091031140c9600c200454071b2000399602007918043d000c4050200c0103aa007000c0c4498280c0d003820310060741e0318020040c09140d111503440c04071010103441d44070001c65200c0585203010b081a011044030301c42d44014450342400031030240000c0045842542507100c40c8203226264040ca026110701d600840241d0b6001c3d1503440c180002c11105079100f17014211700e61202c456007602c100c0040c2002619400000d240c0703080e81c400c00d94085044002a990300034a0141804401d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 884701124 1250 884699874 884699887
    0x4021011101a0406091e050105010c12021e0a0302160522150602060415090825060c0e01110d0207170c030601030804050103180302030d0e0a020d1b060e0312 69
    0xb102001040d50100074010040980d4401e00200030b820b0348400c4460304031840741c1740e50300441d140c440c0381d06a62040c0e6840507603035540d682e9030035400400740c014815440748403100b4400c40090380001c000300b040c00c009004c20b59414500603240c58140c3d08001410742e40f02c00d083c042525506484d000600e9035a20510348864100c090034001c02c10b000c040c6032900040000840c031960009900760040380f042002140c88680031441a040356a082c100400c1c226041101e100d0124034407208146040c1341d00d2800110610071358401c412282000112070105202000c02402c645c1c009100340800c00c03042d005802c85101d03010000303440f4807981c0211103030b40c40c3e0a484000448004c000c40c0c10004c50240c03c450843d42c590900000e030350042d105241c006410300f80c0e5007110540c3c5d030102d5818640d01d0380086003081c12511028000e82507424000c3c9592081d2090b03d80565545808142c2041c0a0320703964805004407014001c0c41d0481d60000c2d4144800200458200d440c00204e160410300d8060b4038603244ea2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 884702374 1250 884701124 884701151
    0xf0702040c030e030a120605060c030c070f03020f0103050402041d16090207020607021c050d090906060201021303060c0c06020f031e010f0312110313080715200c030d03050402101110 80
    0xb235003040c0d4009034003141c4c44a000c60700100504984c507a034012034407040d940d038445c07102580c030034000290004000c800da0340f801d50182d0041600240b00400100d0320404015284130240303540e400c407403e10f910500c0d4124a0300c0140300074901a180c01c0505529060184d00410980e204450f0024001e144044404441000c48000f9401e0103922006548840490200060070140240240c1406500c0c03c01c00003100d07401482200c4404001c0e907200c2150a2035600c0701d0004140107424a4140024107201da4001a0130f440141206603d82200036100c1c1840141c17542072252007614110f50512500040c08001007010ba4002180d61000703e40300c2100701c442c8201c13140c0001041c144040d100218840f1500c1c0ca003140d80e002943e500c2d80480c0d02c440d9590200e11340d141400f5005402241440c46001601250018600f00036010601103400034803514010900e0178461710714030000030b5511810b200031844c0104c1d440c01c045c1c09619002001a081c620a161606010b9004070785981d901d18200c80380d43c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 884703624 1250 884702374 884702381
    0x512040b1e10210b0403030c0201110c03030415050c040b090117040614240609120d091d040b010501050c01200a0216080c0d080c030f0702040c030e030a12 68
    0x10048880d09000c1e041620309018072071407a02030a43c1d003c0c030075000000d504032150340e02101e0f40d40105860b0295200c80c4c80a030020201ca800080c11552581280c044c440c41f00b200810160321004010355882ca81414070141d4500001c294008041c184824001404008415a02650202001a907580c03003490010384507141800260b0300e083e01228100400d03c4515401040001d1b0744440140c45640d84075000750506c000500d445036401c01c20752245800303040140c090640d800014104014041d1300b1110300345080301e503d000c50001070140d2000d0184150810740885091b001e00050003250800d90755030700d850001401142d04101001c180400c04e070100350020315070b8140e411029024540480e8404955920007141040036106903114030710010303000c0340014106d980c6040642604901003042280208000381c0c152042c1d8820f0203a07103240e68050008010040e40c6030410750707032800680f0500c42503409408221061501d049203614807504040111245c0840700c2c90302c40282c040e5a920310005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 884704874 1250 884703624 884703661
    0x50f030901090b04061a01030b011e020304081e1b1305071b03020c010f05180105070206130906060e1008070809030d060e0f01081f11190c02010f0512040b 68
    0x410b01540f0a03c820b0017496071004490007120b09000118141c190010340c01e45003042c1080340000c1d402e640f4404400441000701107441c0f601d10650b0300d05640d80c50110714190750002400d0400300454454a4011810000e41b0b40d1310b002c0781c4025480080400019080d418840d00d07410560b07860f5000929414410b41080760300b84101c00c91404801c0c02810000d540b034075070500d2140424034000c4000100c6010318103651410f8125444800d00c0340d0460011251600482022604210144040550120b0032680000031b405d0702c0d100003031802d240050041104000362340316802012400311544501340c0c01001c8940c4813016040006854030b072a00c0240c5948150611030600b00c1c600000030440c50015854603000340781050101c1d00c90390301c448505484a0b6048602441c01c4c8100200c89002d01e0640c00080503070385040f6090b0f080070001d142e100c15002500c1d4208000074000700354102190303086001c501c01d0300c0c41441c20b6414580c00c0c0e201110f040e80301400242034581481d0000d0340c04c20068108141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 884706124 1250 884704874 884704883
    0x909011d0c0306151308070f0302151b0a210816030c0e041802040e06070c030f0c1205030a060e0c0a03110c0d0815010507020d030e0a080319110d050f03090109 70
    0x19a900e40042030745e1410064001c02c020340c0101c0f20700140d801c41540d100c0069a800a16408900f084407419000d50362103d6081344030400d000301100c481080a119803107030300d800f9601410080b144064075038020009081e4000502000340107219141c1c00386800c0c41c03203883d407500300080c500086100c00d40300d031014407845c0741d403040c01d248460385008150300003030b504103200f030f281881004801e0405644400341150f140d40018440c40748400482c1c4200c000b01d140e2007035424140701e0306030780d520765138a0120403140260215000109004180c0500e00c07c6100609450100c44214104410808202d20403500100200b50300c0e4845901c00c40002070480381215044000c81d60b03001141d11000c1c12a10045450018564066040c000d555000b81c049490305a40104081c02211551b036090703a03841240e43d0780a402006101c400b003041c40003007005109000389108894550300c400c2c0001005201510310565640d003128100e00c0f0025000700c280c54202c900b091816844e40e550100950040c83c0161004c1d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 884707374 1250 884706124 884706127
    0x1205040309090f200f0901180909060902030c03012d020417010e0d091802180904061b0c0209010303032708090a152f10020909011d0c030615 62
    0xf10740400e00d80c07100424800c00c071000c6a03c02804194900d840c080c03188101003a90b000c00c681c681641c4544001d9181e207410401c2240101c0c1c541d4040d0084444994007102d2080c0e81c1e200d04000d40c0b50410811320102da0460080c440c00c21030103c101c030002102004415441d0340c400c1c06060000e00f54041e03502810000ea0000c10303050a80b4442d5000c0c000c01580d8101c90701402841d44042c510404400055511481104030910700c50644940254000680010034607040101c003201c030350b03920030301c107004078011032011aa0010340c4c840c0c0802c2d03004070040300c01400404404c100068880300000d604581d01420005507078010f02134012100c6520749040d0500c6580c2815074000c201403840900303020803080e03e41041d625166081250060300a200400c0401c402e100710428078019007614811042d101c050740d075129001e0078580ca1401c04040003801505801003200ca00a00300030341e580c1d0040c6032610040c0f211038003800084902c0c03072001d03210b4502c0c46400000107406480302084102101010b80780c1a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 884708624 1250 884707374 884707391
    0x130c0c05061e09150f04020105070209090a03140c061506130b120c360d060501090b010504270902270a060518040204060906081501050103050403120504030909 70
    0x4490300c0c40455042d118a0703050011540e401c1c00050980003416108003024401e48526482c203c141c14020022410018100480e00041c0c0b10031003a03600502e09036009140d554510310f405800d85a6400341300c4505c00090080c80c41c01400014034a41203c032405035011101a0383c0c1c0491000d200e040024031881c00c50f0301c000140f03e1004802807400d2130b5004101040350711642c4480c81980710310f0341680307240b0302060b40c40c041464142d1940c01e03600c03440700201c4403159000004145401405003098551685e01d000400510ac400e01402090f00001d1030118074090030844d2400300205070204100c5ca1029503081c90048100d00c0e403244004540042c110211a0010b529045481d07000a030149441c600d00e5010914524240c0100b401303590000300510140020a84480d4100c00002c1c0207a074010b8071500005000c0c801c0d032141d240a41084006000040405049015000d42c10390186042518000400c004668094450541d03c0b600250104040d2120304003154961082c1d001400c02070303c2c040d0035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 884709874 1250 884708624 884708641
    0x6091c0b090111090915041e091407030c0b162310090506070c110405010801090c1203050405040c03021c0e070b190e150705060123130c0c0506 63
    0x566229070400d000a103d00607002a0601c140c0c0a04080282c102e2004004902000224070000d450000080c0c00001c9860300d4601007014800d03000a40b41c000b03541e400c1010184014510182083d002503001021218a56a200d55010284d07205000c504500400e00b119020700420240040c00e030803010340c104001000394405000020518083c846200303c4011a9604199005951265070810003822450341c4915003034918103134800c4112000c4c46510807540c081d035620301c1064040d0608500010b040351840c41d1048003015181c01c45060340103811506000668404226000d0342c40680740030482e58a9008145c02078000c07020001d0307209000c0b8100e00003003400c542c80511003030003000807190780701c0d07450380150360602c41e0174031410003044a604000032190013072030100100c5a001e0a180d0843c051103103c1c50060300140000c88068100710f0041004600c4451214400c0d000741555000c40000f031400901c00442c4418410300940c0c884800c011454001c04071400c851782c200d029142549040e5a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 884711124 1250 884709874 884709893
    0x10b0f070c031403250c091a0a170f1203150414040f051b0d06150b0c1b0a0522271505070206010314121809070f020a0206091c 56
    0x340c1700e1501e81500720b480c0408607840000542c01342c00c0b003220351009081c0074201d4060040e01d00c510a40d05002c01c0c40c3c41c900c3c1c40d0580004000c0046810301d420815921f0840c600b005c01134003100c04294030500c0035130150001030088907008070306407003c003c5600014000c50081c0002c00c01640d0070060940400003400b00c0400034400c0e062044081e5604402e00004554400f00050b01943d027000310421401d000901c6503114038501000f400007140606da0300d441007081580608900012600310f81d04c004034403460034940102612040f01c02c044610f0500010900407230a18402034844944002422404905c2d944000d0000d041d551003080c6505031a01c2c02158416008002c03078403d840d40100f80d44503207080c814540200707040d90140000b646151580d038031040301d0302802c0c005809801c81031150504040020014400000359880c0f80045840402101c80c0b0300601540602c030849049a8115902080404c041981192500d4442144d100440c000c10030000c1c13604100c1c0b18260310360003804003108 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 884712230 1106 884711124 884711137
    0x6090e0f2e0b19150801080c093d060e09070c1b080607080a140412110f03040b0702093615042306010b0f070c031403 52
    0x90f208402424240d0240503c0620050380282458221100301c2c018100d160181c5104140300000c00d0000000030603002d82e5414400745450100d4000d030303803452407841d403260095050a40021261880035a030241c000811104102840f2a140508030540718220a50b2881d240b2085076880d0b141c2e0118105605a9003401d5140c00b00b0b129000b008518860101907440f41ca42d414a200c4100440d18040410720004030f050040001042c43c1141159803503541346801a030142c0000e05280c149040340c0741030443c9010003e0001580f514560181003082d00807140c50101e52200c07000c0c01c0c2d07c2d100841414180000c100c810310320f0f41e0403102c3c11140800c09142540e900400120886c0c540300421141119848030000b10140040d10f8429003d280300040d100a010650402103407004c14026910001345107a000201401042040b6500000131584807240c50281c10b03224071300d030b0780301e0300240e = true := by decide +kernel

theorem cover : BRFrame.Cov 884532374 884712230 := by
  have h0 := BRFrame.cov_init 884532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 884532374 ≤ n) (h2 : n < 884712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
