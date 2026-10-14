-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0164
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:12:47.49272+00:00
-- url     : https://prove2.me/submissions/4fe640f2-e8e2-4aa6-aa40-269a6425f481

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 29316552 ≤ n < 29496408 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 29317802 1250 29316552 29316571
    0x106050915060d0f0906051b07050c0603070509030604030e01030506090105031b0307050d03020609060901060501050304031101020f0a0c020f04180303150e0106080a0c0507030903110a1806050108090c09 89
    0x4460200703100038084c0602d449050051442c0480d020140312030f0f5080203208091145d42c48400e1003854040b0385143c01020006071031a403088078412101e0905100441c2c010009050ac0390406442c0700001c0c0c9002c404503030403800030b9526081c1e03411950701030150a41021044410030b4a541c1004c02003030b900c2d02d4400200302041e00003c8800401e441c01d0180501500380035040300c1109129041c0650b582e07200f9543d50200c0e200b48000a800e1440c18850308081d62416075610341f86803100c1e103049070b00403803034945040e00e5503080002e030320840d01101c014007002c0c40344c1e1a80b00c40b01e41180100440c4601414800d80a141046905109200d43c40b60021035154103007400181030b0b03451981850f144402ea00103100a201d90b000120740c054002560310f01c6020a52018802401a500d041b42c0034001d0000003000b1540d002c0d018000604202c60402d512071000d4280d01700b00c4da6440741e681441d840000c50444c1e0300e660314018805c959014400d994061a518000c00c3c0c443c5031980413a40f52407004000d40700c1d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 29319052 1250 29317802 29317807
    0x4060503060f040b04020c011e0b0d14010f05010f031109091f060512060f01150f030903051207030e0c030c060f0901021c02010b01090501080610030209040f090c0602010605091506 79
    0x540c3c0c8680c4a0074400740040d2085440f030700070201e1a4020401c08106100e108421021000710301094016001c0180001d001d0385002851a41c41c41813046138584402055500c800b690701c0784044600c1554020b049505c48007c07018614100b10f0720754601645c0150003410000b04004113604006400c188030f0405101c80c03841c01e427800015000800304c80c0c002c907a208001c900b02d00d000d40760004101d8050f80381031480070240e981e5094400d00d5444800080d10220b6004044240c984e40258081d200582c020f0418600d080c0240c00c1082d03150004441d00320101365900316040342000104083c45603510190f0003804003481d0b080010301580580e1020492a900004c4c100003564400e00c030321151041c3e42c21510500c0307002c184010b80605105288240080c0c0050b0000465603c1025182d0140101134100328544c0d0384600c0490103540303e40d2805030400d4039109030150b883d041d407003500012402080002801400d210b0b00900b9a1250b80c440d500c6598030005010400044481d83c00101c4021680c00e503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 29320302 1250 29319052 29319079
    0x6050331050102030109061a07050c01050304062a0207080304080705040c0c05161505090108060405040302070f03030203040905060a03021003020304060603020406080a14011107170d0c02030a03050c0406050306 92
    0x600505815030062241d40040f00000c0d20344403e4118800317650440c0c50716035403c0d02070100c0304298090f1040c060316660104c01145041d502841c011078021340a81c1d0046490401e88a80700c041038044d040c0f200e6910000e50310914000d50502250014002140180d803609140080840d0399542c280515889503580b4920180824021446810700c958401c050b035003028911072601c0f00c481071170300c5030b415026051107825100d02c2c41002200d0300707082c3c142c40d040c0b2a0b454901c10f0000410340104110203500c580e039000b0405500300c032040000cc5103c6d0340155a50342c10004100c00391180900b80900910300202d00707200580e44c000014030248211301e0b0042e180d644a04011000d00901d81c0040c1d0414504000411001004a2812100390180d8582000421500005801c07510456000f41c8680c000740564000101070f00c04280c5d085c3c260704111401c00b521500d0a0080b5055202030303002607440020121403481c1c260180b103074014061009241414135220b000340c06440010200740c402c0e11400000c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 29321552 1250 29320302 29320381
    0x70b0c03070512030405010605090403080c03100305010615120603030c0201051c050103150509060402090c0f0403080f030403081501050d0f090507090b1c02030309010e010c05061f060503 82
    0x200c60307464101040360310004021020050f10b62040c2e038192110350070101c011505081050701103014560641e6101202c0d9030702101e1a070140c1000e8042c681c144018480003004c90400d01500c4003503c082c2c0e084c80010781182c3c101034a0318103503000f42a062400c117182040840c2d000b16001e100d81c2c1c0c0a00303040380d880e849944501c070840e885142840455151000200900003000600e040321078202c441080300b81c841200041c0c0d5260b040b20002e5210000310002000305000d140a09030318845a00c4403401e00f0f0300ea81d107000d52070b0451a0840c00800d0040100400d15034410360007508200f15190760f140c464007160009100e8800c0d5070a80007041c1d00c84081c8c1b59421042e0b4410703545c45030048103880081c0c0d2101e2000b0082d1011001240c032a0704080304660580c01061900070420b039000380110301d00080840107403040c15450f0005414080700d44112000b08030b052111a02c00d002c84a610340e5508403090010b41e14a201da0040d00402206008204c600c1500c0c2c8000c000103c10004124001c03503600e03821 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 29322802 1250 29321552 29321557
    0x12060e0619051e1318060509060603100b060403020402030c0c0c060313021c020d0c060908011518061d010501090b03061c02120d110105060102030c030d0b0402040b040608060103050c0c070b0c03 85
    0x10030f00d03840d1903009041e2070410300d171035500140700300002e0004c1d0300c81c1c0643c540c1c0c401003911015131507008459030b51444d40190f4081140b922000d003102e42000d03640d80001c2d040380c2085513032207002e0304009070610007000e0500505240d42e0040310700d9800c6081080d2031007961550312600078000d5001c070401c0465440d019165070107055008111082503006854200707401d949a01c20440412403100001c90f4001060043d0059a90300a08450000f440c0104940800c25080c005045181da110008201c034090380803600343c420030100c024025945040001007419620380e01240da1400140284101e954a07803241a0500c04000800312992510740009400e802c842400d480c410b01c0360350108411185c00458010b014042c000c0204025526903005903160b103d10000c10055800030840400c1c60f2880e075003e184840005000142001e4503072118605961141c2c002d00086415001042070350341c0e00d130040b15840100c0301c0d01a0705000d00d210343c2984e40c01860150803c103d0012808440d5203104105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 29324052 1250 29322802 29322829
    0x21c0b07030203090736060821090604081606020c0a0302060d1b12050108070503060f0c0405060423010c020f1507020604060c14010501030503030c070312060e0619051e 74
    0x10040312082e1b88031081d22185140c070f1098202c046901004600003203171052408545001005d44404136801006135080c003c00c00040a20f9070050201e03480603100c4801504c044c049400040052200c0b24442140300c481030790094003150301c052986101c0380c450b40021001c40c1c2e4140c400b20348480503404c14030060180102c2c0080400d24140740c0b8031139203510070402c0d2a5000000020400d690301d400805482d140c1c0740c0150380d096071059001c103c0d142d02c180d07501d07944961280b00c0c581c200758a580000d1810340c0306a1045a0b00813046190014089070b00c40074003c0642c007401c11800f500c080d07034040342d0b040d0ba8070442c4600c1000650440c2c62031491150071100c0702c550042400d075481e40c88920240c5000e05801c8150b5845000080b0103621400c14491107041e2078100000b1411542d400c070b100700e00e035404420308400700040245901d944038503a0144102501072900000d140e4038203032060000900207460040c0480205910030800b03500d964660620340c988a0740300440c014804808117008114202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 29325302 1250 29324052 29324069
    0xa0504090c0e1e0a0e090a0807021206010801020d0b03031804050601031805010204060f050708250213050a0b06040b030109090c03020a06080703150e0708060310021204021c0b070302030907 83
    0x903c03505508042e0500a14003601104c03411001c0e502c40c8080d90045000300da65254560210000402084811010340139051000b017140c1207214455018504200d020f074080c05039a900880c1e208a880040d0081440d215000d80095050208001c200c1250010000d40360340902d035580701180c43d60b40300e500301e061005a03210501e0740025a81c64201e0007584a0300ca214001032a060f01246202c2c4a81d040720700064021003c0d5080003140036110701181407076010040c1c43d030004083e040040e15412044240e01c0c070980800210351500f03417040c03010791303401c075482c240300c5d51040005104900009040da03064900e54040020300d0100c03440c001d81c401143d500f010b5406a802c03c00042c03459444600b007803065855503010b11403c420050b000540c00028068452104008400240b901703218046059104034005d0442e0001c04080c02500200e0340001801060140600c0c00c10007035081140744000581c1d48050706400b20112600c0b2010350131780c0500304000f00368001001c90340c084020011500940b2080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 29326552 1250 29325302 29325319
    0x4091e140a0804030c050102030708070809010210180507080c0d060b0a0801110403060c140301060507030216060c020f12120c010b0619080f040b0703090303020706090c080f030a0504090c0e 83
    0x40c1068041604540310445405c00c1103035000c04c4035440071094404160f80300c001c540c00c207201591a640300d60814110a8110310900161204840e114001c0da460241c000003502044c0700b046c24001e05000b519000a403032540400444140c5449180e0706280c030507041200051031092180000d8020a41035010402c15802c12002031801c0340c0900090080740d2240d0810800d0b0711110b01d00f0b5a030914140020030307505800780f0040102070300410080800cc0d03c1391054584015564607035001001c03068000300700089041080b141141071040c00700c184190100c8840741000c1029180d107a48114401c404400450301140241004c1d800b50400000030000808040d21034024840d402d410720002992803000600311008102000c00e4484032a005c0d80d0400001405070780c45020907030280c01d8540d003c8003090381c00c1050002141262094038000c0788280074542c6001d26105805240120010780d4035480d0704200b00c5940103a401c00301311811103609004c0452484d0001206880c52031041032001d4002090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 29327802 1250 29326552 29326573
    0x150309030a08070206090304060c03020a021908070605070203061611010507050a030614010f05032a0c010c111b0103020409050f0415020901021005090f0706020a05060604091e14 78
    0x120240041c110a540c032500d00703035141c20080340d0303880b010394848201c2d80081000703201141c0b0a90794000387c6800307401103d0100c0542c2d40441d0511011441d003c0709001c140d0400c0c00300100038000c0c6401020b482c540b16040c9060354000a8032404050512a8808000d8111301038441c06141d0400c013084019000f00002d00d00945d0180c0503504c172400020010345066008100c01200d0324003104c0c0e08506940b900704000d2048816295a40041c4c5605010001c0c0e4804104101166003410380c0000285a800d4803051103030106400d44440d8031658044c4440040602c82003071000505901c1030700040c40d00c0b046490312500680c003d2185821903020345043c081008072180090203d00e009500c180c07140d05400d407035441c14404074000d00314501d00581020100c1c070b100701701a8018640000c86ca90580784000c41d00050a0701d4a6003d50049000d40c0101504200348401840540c1d0b205900390f50521586403160f07a0f50a01907203501c520383c1200d101030030180c01d21542d5407a0600e28141c040448040400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 29329052 1250 29327802 29327821
    0x91f080a0305030406060b0c150604020f040801150f18020d15080c130204150c0c091e050a050408090402070507080d020312160503060d050c0a0906030b060d0305181503 74
    0x401c03607003600e402d410030400040304801042247c8c0b046190708082c10a207080c56070019103d2801901d1103038429002e001054640c0181d600400082c450301c0000103043d00c896100c07081c0c081107580b104000034900703c000c01107c02600c1603050384804000300160748074500c0410b90000c00c600076448009044002c00455299800980d0b20500d072001c0300d90484810310080b80c802644110b000300703180c90301083c1443c80040d000e88580442148214000c64125440e401b500040380d02785a650300b0440750b43d2000c1c101302202c502c644c94120f2204c503410b02407854180c1310010a4031544085900032980001e0030001e00005104000c040c0c491841500e240181000000f9034a0704000f00a60204588002081ca001d255034250f40c0d42d10f983c2e4980c2401d603591b500400031900500c9030192180d00600b03c200c0070590f039041000c0007404165400080321030441c1001c101c00c8100901c920300031560001d441002c01d400109070385141c038024551464120001d07001c03076414800c01d01d034207000c40004010f001c484403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 29330302 1250 29329052 29329057
    0x130902030408030711010b060a0309050c0402030a0507080a15060f05070b0705030115020a022407150501140d020a0905090a05073b040b042102070501030605030309091f080a0305 78
    0x200d01d41e03180005c01c03038081c001a003212030707004036298040002c03c02c460703815029401580003140600c064480081c0e1050104082e40c4c803c075100004130365a20100f001aa401051844d0480c800032010450881d01c028800401c0c10940600414003100340e0880b842c0e2441001250020341c0e0141002c0d229040ca01005002d981017130241200c4803911345040c0c00e07140d10006440480310340080c00000b02c070510800002c04040440026004840100054400b2610480c4928880f03208120001659071600d010300704103290803a207040c8100705c525144400744e900d0509400076124102000909a164070404914200e00108000e000d8011944005600c03e0110306808030f210800300801000307030000e5119210146200304262901300d100001c0b0300842c2170000c02036402442464101309464400c0403900f40d60030030f10742000050384036210a2100b560b1502600c401404160011810034554100050b044a401424100e0b03404940741a600100f18180d0b8060081003080c05072020550a400d00a140d40d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 29331552 1250 29330302 29330311
    0x30308100b0a020105010e06040905060f09030c0601080a020a0906080606040b060d09050c0f0907020318030106030b040b0a0609060b090105180402070308150306010b071104060806070302180d02060f13090203040803 94
    0x107c3c4503200040141c14240120341109600c0303005401650b4071a0181d510100c0003800020a03440240b0958600703945c00c111642c082c11391400240000a01441000f00a05094210300312150610904001d60340c400076099810000444000c0f07208500c20001c503079680113000e8002c3d1540d04000e0a8018808040780b56682058203840003440b81c04070344140044004255048070050340200700d800200c030081c0d088840d10210042c00070030f04690301d480b100709001c025501920485003100501888080c944510001041404004d0222908c1d0000131480b03405032641d120305100c00000e10301da4034680d490100101e00b800500c1151600c1c03450400070f0681c901103038160001c4404500112441c07600056050484000b4004a86488920b55420364041141e1a010f900191640404180300c1000e000d2039100302c04c8c0b641c00585803500008840016029088400d0051900d1312082d405a202c107400c07207294041e2020748656901007884062070301405a405041c1c0188084144802c0092120045009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 29332802 1250 29331552 29331569
    0x5070c080301062003070201080105150d0f0204060f0f09060e010201020409050906090d0203160305180301060303030c120b0a03060203040c2309010e070c060507121806050c030702030301030308100b0a02010501 92
    0x43c5100300d4403031740e240304140c1c0c041d010400040c010082c5240c500040345011080c5ca5030241441280d04100c1c007a200c03014100c0082036004101804059031094011403000e40610f001050f0039000031000d00324000174006e480410684007240c05041e4000d40440c0d00131b105542c01044140740c4440c87c1a1124400d407580c510310b002d4405407080c0544004260707003081014840030603d800c1d555400b583e5991200a03010114907000700c0c0c01c0916a000c0c4103034030096020b501c0c00f280c1e0351a01030f0010104000c0c440302d005600d2806e42c0c8009aa1240f01543d8196680f0800c0144e50f500c460030103d41c6407071103130b2100451a0709120065030a840380e4070380c4100c0c1e031800d032054140350340c0b28100818421411200000000c855411800c0400c2181d0007140d003052040c00c01100d0b4101c003a11050964a0143c83c00341110900100c01040000360321410360b1100c0b234003200303500b5030504180003503d83c0705c10321015040000c0c034008603009a10031304500c001485010b42c10b90fa6105185d1000c1d000e00b000f4401c1409 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 29334052 1250 29332802 29332847
    0xa020d1404141e07090f0e0102030403080a060b0a021209010219050304050a06090608071404080d080411060304030507030c110d0501051905010807050103020d022505010c14070605070c08030106 85
    0x1281c8500103550300c2c820380320f010b8528036041c018020300420088254040d01600c90001e9000c0381c5081c4000c6005038025074641403075142400751305e401d0320616448031002d0041040260b4406d6800f083c882e00b8031601d54032055a0f6029440101d2904951421041020705480420b82c10003000100400c01c40310160341e9008026918841612004d00e0381c40f901d004200b4000009450314414815003c1e1003104500a40c2403c3c0c580c42071a10b00310140b070041001c200054207100a1008581d4802042c0701d0441e0128a03500c1c2598004100340105440181231203050903205040002882540c100783c640074020a45400c00343c1412070107000103842da401e980d8801c4140026812032802010b050304c0c030136402004030034070f0040114000e51001616400c0c5607030a20810b40c4482150007548110f0705120310040c00005d0f00c0c20710900b10b0380364007419001c2c0038880403104419103004041d1a0250b0700448005099610910103035101400b55000418132180040042001500824412441c4030511842c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 29335302 1250 29334052 29334073
    0x20606030106060c02091003060501060c0309150e19080a0609120206090309060c010209030706020f0616090e0402030109060c020105010f1a0f0912030403050319080f0a020d140414 79
    0x508860160043c1070000d080c1018080160604002880d0004400900c082c0c5260340c3c0d0700d603841191070a800110000321550058401d042c1d109192401030200b40c98000c10102503a84050b100d80940c480c0140100b10000650a0b02c01c01941580001c2403035009070b41010701c8a24081c030040042c0c40d41110340c444100914410325200003100ba20070010f40f002140750241c0d410810003a60040c0d045104950340070040c510f01520b06015007802002c46400405602c00c2c91002203013030100003000301a840c08211050b038206680f00c20781c60102d5000c202c6a05260703c6e10300120b4058582c0751409040c070f42c10010760381c00d4103a0543c0702504968040403480380c440e07140c1cae4404202c0382c048243d101c1040820b01101003541ca00c1c000500000c10010100305546060b14a4542550420751040e6003603080800c200d40107040252490381c42040a10b44110640740172089140c2d03000340685121107042c1d01040c85516010582c0c00b80c00d2407080c05039985d055142500d0050120980503964242d40d006908410b03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 29336552 1250 29335302 29335309
    0x309050f0f03041a090a0b0d0204032111030a0503011208070609110901060311070b09011404030c172a03090d0f1103030f04060804030e060c0c010206010b0c030406030b130c0203030403020606 84
    0x545c0c188100030840b079002c914040404145030000540e06500c2c0d40c0c20030000002540640e24408040b104846030f00c1414503000001c0d00019440480c0b200741d4004100685855900004a038150340111503440c0e141002401c01813128001c0180003440d06142040880c180440112408003444003110001c0f034981c0c85000032019075206182101c0840818049000011596843c0c103511600344800080c86a10940c441c100146003503900b0303408240b0914020007402000e500c29205888a4a002494030000b56030090300c43c6018003010300f40c40426019012184c0051040f1002010000c0c0400d41540303a60034a0010340008520444101806012042c1e440c1408020b0715a0f250f00b11300310a00b010301d4a00b00f500c610100030412810003500554040c040c0d514980609610100600204403403501070001900c2c0c0f51062300056000344003030041960a003c00801c490507101c0070320300807480705401c20206134548040c1c40c100b19101d04004100b043c044d4004041e5105074000c0e400c41e106929a0300c1070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 29337802 1250 29336552 29336557
    0xc0a050c060c1906020904060b03090106050907140a1e05040801050907051c0807060213170c0901170f0d08090613050d0815090a0b180c03070309050f0f03041a 70
    0x40b04641d00300a941603480058a83e48030f030000d008a802500d84494100010203c80d540e420500441f0000f105010090609100b540080c120599521510741031000b800303081d81411481d015007018000a120103980d100300d01031120000b140e2250520865160b1000c0c190350000d0040655a601e000d0024003a0b4800088800841e4401350030b022650810000440c03182c100a01d00365550041002020000b80003440244045800400782c101514149401c0310b80e00c03240d2081a82080d8010460900c40e903548403402e0f4112040880f841c06441991050182030107690003d040060007250034841c902034004036402d01c900c82c1a070648070f05903540460075030030b106041c01c00b510341c0e030020746480319130303405560080d8000704c0001c01c912009011900081c402401240c0c0c40020503142c4040480d01d0405200c07000c02030140e520350440e91701e011000e01007140802080c1c1005c26840d11103c009104040c0310f90702440c155801500d07001000510510341d00e074414401e1541c203105807202d0903000303203000c002e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 29339052 1250 29337802 29337817
    0xd021509040e060c0304030c03020703051902040b010507020f0405060f1801030b101202010509010302040902030a0e07081f050c0909010905010810020a02060403080601140d0605030115030c030311120c0a050c06 92
    0x101354155112510f0868510680950450942c403a015011001c9841040910241500000303025141c0d000f03481400b042d280d00d406018148002442148016a9110480300c042c8000b0b03240001d480e0b44d100d000500c2d2484c45000c954100747d40302e0004014405610b41c0c5d6040c0da010b50b0455019407503a00d100240300c5914442c00c8102ca291a800100661180004040c0660149000740c107064641d9881c004a9005840403110306645000864400005004c3c1304010101e04003c0c00c8620722851340010105150800508100d80e29400501c0c0e00082030183c0b40b140001408038083d540c1c442e290304009140031300603034400e803141c0045540344185900890b202014654060402a04e90f903400341d401c0d80e000707400d803414080108520041d0381c82c1c02000e170a030071050038000300700ea0386044141802c46452010b16445040414000e0021840c4c0000240881398145001d4843d12441c51000d4145041d0001c00b281d050000107003d09a10000a040415540501c05807210307413441404101543c0f00c0c50700c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 29340302 1250 29339052 29339071
    0x90c0503211c0509011406010302030105060d0b040603050d0f020c310b150d11040f031202010209100801060810240c06050f1906060e0603060d021509040e06 69
    0x440040c860310a000549104004003001d191154101d802e128140c03101102c041e903042c0e65076101450004119a0b010750007146c00e00b070451944d410203020070480d01c25402c022412903142d230f07041c0c2c11980f600c0d40101c0040d60004252000e03005408002404411410b0309600148030755541c1107103d2500007060743e41904a003011501800ea18101807032096056032800442c20ba49107184007440d181c000c0e040c94824405005c5590ba0b8003155646412030300e541a0b0755020102c180028007400002c0d40c2403905076604406002c00e1201080e004a0180c4201d008564201c507507074040f403500c181c00030021030594020f519130300960340d80c20070300d100c03020072510605022091a41030301c00198100b040c42110032a00b071400c82c2c40031034280c59030b200750703803007900c20b074110401c10410481080c0d03c0425501b4060381c81da4080c0141c0b03141060090007100c10140640c42003000102003640c3d59262200d00501d00d40c00380492100d100c4d00400036842d40c02c07107440c10303004500b890100e030f184080c0462000d110710b1110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 29341552 1250 29340302 29340343
    0x60307060207061d01020a050604061b0c0807060b0a0918030e1909110f030906060301060501110a03050a030b18010512030702150a18080106061d100c020a120303090c0503 75
    0x5203480210042120001c0c154011707c8610b40c042032051080600c80c500958020404c08220003015941035010700c000070802c144592460000340740d100880388107a400c12404204a98002c00040d411113550b40446e038090b02d4107401d000742d000d4032801e07003403014000d8644940002130501409005100404140001079006009000c1900b02d170340b05090f100c03070020100d030a00f0f80d081e04c0c2560541c0169030500d2140d0250040049c1403030240a403401034502842c00b9141003803c08a141ea44910299004062210105040782007620a9102c0402214005c0c40782c2650120300d400100c44000a0154034000c1078210048014080000110740302c0c950b000d000c85a145522039220034441c0c00070b070450030800203260510031248400c04084000f4000342000014100d103012000361131481044010040c841c0000c1140c0c829a0780e07490881c01384da2050520301c261410520006e901e000781d07034100300d01d001c00c50084001230503859480284a24858078500111688403010950f448001f03449a480302001b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 29342802 1250 29341552 29341577
    0xa0b010b0406120c090b0c07090c090e0c0a0c06090305030717090307060209030c06040f06020c0a0b030609060a15030902090a090803010501120f05011205060703150504150f060806030706020706 85
    0xe561048651138090b10b0f213040025203507614102154881c01d101c920751341c0402d4060009034554400e01c0358170f44031405d122085a18280c2010b17072071070300103040d0803114002050142c0c6042c052144111015408482003010002c1441e0161282c0c001f0303a0400300080ba81d402112501c5900351541d8081d50b5a4401541050310b02da48a4020754840014107803d400b448200c2262a201e40014101030401200c8800040c3d0520342d00a01d450544100744d40b05d80c040b0803040001c0a43c0c001100d030000400e075100f40141d82e98001041661000f980101d0a40102c0c000c5401ca0541c075a0054903074034401c0780d010129480d004024030a035a01310320003504911007000104090342c003918171281e004d04a14400705564400f000407008481c000da0050140149038a070203020084240041075000810382410020b5000b0300c42c1800c00302c5858060680a01c4da100d40442c05c01c2540c040e010010500c40c508104204e8448030003c1411205503540d9000c1c2c0f090030300c00301e2442e00100c0c3d8038003907a140b5074450030701180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 29344052 1250 29342802 29342837
    0x403030e010908070909020d02090405030406141204020103050606090a061806090b0a050a09030c23040212010308090112110702040c020601030f02060d020912010504030f0908070317090603090a0b010b0406 90
    0x3246c0f1000c0343d009400c0440701c80141c6510302c443e48194081c0c00610340701c9282c042c003d0800f281c2c000c0c803100064402c002c555190309103010201c1d04282c084c41c0024140d90f07414046185171003026502903100d8a928800594554000c00350a850a010144402c85d2961060291206007050145914a0b1744c1403241400c002d1080300503291180007071034400025903480e00c03140d0929045030014107403c000b00f0342e1541c150707100d8440b50180080540f000c5290101c00d4943c04040c3c41c040c000184140d50008055005030700ca10a041036084031a24200700d8201c42204400d00d90b80309000481c000c909083d01c10300b080e8000710f400c42c103da8025210040076040c95007081031580c0800b40034000c41d9800d11a4142c25103811712130b0100a0380090001a19091904018201d01070b05a001010410340c20805d00c010a400700c1c407002120303480b0988441d8511030690304059801401c000981108004c02000451000025240941c0d80201c410a14a0742c07121100546840786006110100300700d040c460301d80f4030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 29345302 1250 29344052 29344061
    0x30909050c040302060a020304060201050f0402030a031d060408010b0f040207080409150306020711121b040203040c05030f0a060e0c100c05010e070b090a0807151b080406050403030e0109080709 85
    0x7000c80340d450b10303064032a80050115042503140c2c1006a001003820300119409108480d042081e03818065102e20706503000940e40c3c404600010700300b007018021489030201c01011180c100b500200000e8035079440d544107900070112042c00d80e00c142580c000c2104d85040c203100f00c0e40e0705a004050103140a0402d4814806480c0304c2040c020086200ac80000100e99144013404d41903100300100c040c22542c0d1410845072084007034240445401a40a079065000e0449520440032025580561030350f85508103e45c9003051540200e826001c0c1041110f04800040303011003110344911010025001083c0185540fa507007510100d07045481c80551106450040c0f20020383c961040c40045401620f00c0741c9d26007010820b900c041e2814002080b400c10510b4100281e40103807048100030b02040c0d2030010707a000c205800724034050502c000030200000e0310042000d031b401015000188195516550341008040d0340c45440103400107544004006404c3d07108600712011649010700501400381403507c1c800040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 29346552 1250 29345302 29345311
    0x601050d03051608030711070e01050d0f05010603060603140d020c060306131a0f04020903030306061e0c0c0103050a09020f0907050c010e0705091003030c0f06090506100312090303090905 82
    0xc001403200044501108450f254918450020503440b828611401ba1080c104020b42d4481900054003d005419541d41d00c6c504440c1c0c1140d0031150310341c0b41e050034001003078540130181c469401c001c004400d104480c4c2040c0c04803803046034200076685000c0d1a032a110044c007244140180c0103111000e60300c0c90500041c1d600190000d01d0b10390a400c09240304800ca904200748028000040d04158103d450f00d1b905421406a0a94040d45045180070020340c0300d00c0700614551280750007140807186e0401a075440c0e99888401029696103004e0002141d070b84007014014940007a0030000080c00c80d03c40c502846150660140c49403142809904c1000300c550b500401c9030b000c010040c4501c884508007406440051030080000c0e2040604000c1031181c2140000e20705c9480300444803003040040d5001c00d00645c0c01d90841105409070704286402c0f80a0104408050b00c0c81c4502d20500ca1504031005600040340e1081420000300c108400c0250b031002904d11018000c05c0a00388108100851500200c1d1f01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 29347802 1250 29346552 29346557
    0x70c0303020c011404030801090c02060f0c0906070c03021507120e01020c031f0c03050f0c0a02030f071a0106022a120304030b01090b030106051f030609020301140f090403020601050d03 81
    0xb4402c0c07407210701d401c49102c00c400310074408002041c0000d0580000b08a0f014003060303001403021005144001e903a807440030340415082d820900004445030324040544603501001011103698002e03608200041a480b400160f20401c41d000f403a00d000e4241004864400d03030312042a4034200c1000e0025501c3c5451480c8041c1076014482420743d032031380c06002d03503400454101c81d0003180b117892801c00d10845030b880003040e09040c90282401070b90300180050907841a0034000e1281d40b903086000403421401202c2d44040703051400f1400c40108602030702403290000304003a02100c2603a031801c01304e9460810b5140701c0b0007014110744450f1112790040c613543d101d06010b850141c43c481515400c1c0c0c070b1644150f07c1600d1303600c2030b540140500110342c081c001000c0000c070024000300b403c040c0050030000050050b0302e441d00d014a40803802c44d000c0d0b00003a0040c80303503840854880d0794800700c1403201400808a42d21401200c4510b681c00c1ca81400e42ca8000e40c1c0583c0140016801d01c402d00c09903403000324040d800d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 29349052 1250 29347802 29347807
    0x11514011101020a03020c1203060916210209040f05160c0501110c06040212010605011704110904050d090609140d030219050d080105030c090703021305040f0b0f060f03070c030302 79
    0x1c0c200001d000506100c6026900143c2d10341800b100745090044201c41b402c001002002480807550b01c045d100f0303400042c04c542000403106541c40940e4940c241c0c030700d40e069181141d4a40d010085c0d0584c0a0b00341d51000352020700c642d2015819010444504540401c502070902035072041e220f10480c286611244914000500b0200ca444402c0403904a608030010340d034050380400046050401c50303051103840d090001d0080e607003000f0000e005803585400c20541d060000c0d0000741070201c209840030302d100018003001010305080c117165451301039116640f40443c040200010380300e88504002001c0360400340002c00801401d104010401c100303500140c00718030034004c00148075120202411000b520407070042409000d2400041e052030016400b2a1098100b40c0d140101034a81c00756595029560b071400603680c4100c3c9020b1100104690401a001440d1032001d551054103540249000441123950500d500149010400c40d03101e040008200d14100380301080060340240c481c4110a8441e0a0160 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 29350302 1250 29349052 29349077
    0x8060105040503070e040303061512050402010e1012060b09130209060f0a0503040501050c030906040204050601090f08010204090e0c01020a0f020f040203041101031b09030b06190803040e060301151401 88
    0xc0c9490079640280041910744414801012380610030315008145102110030310595955000d0080c41030358010440131a1a0030001c0c0440e88541c841d98a4036400525400c0113008000f03008100c0010180d40070011860a0b9012134801a00030507030302010001860b04811815101e40c103400b0b07400c0402410740014060008108104120b000340c1091550f03951400e80700d00d4141001429a50003070304043c1c1a240400601401e5000072480a0303100e41c055401040c1030b102d0600488524540d64090311800141d80c801141900303042d0000d004540c1001710500400759031080158507007020707509060250b44002c0d462000100c1c0d03180185035060006121030040321803000420242e07801100c0c100c4442405c400c0d100015a09445041c0c080090003600720312070501104054810703400d40c00b001c0c011106c200c00054842d0f43c5d00070544d20b4081c40280c80c00c181640c609009550786c203d4066001c3e00c00070400081c0c01c90405219941100500b245103944851034940840c15400c042e203029410040400d0510 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 29351552 1250 29350302 29350309
    0x10e03030c0a030b09010b040b0c0a0b0109090b010509091c14030703060302030105130b13050f01090f12050906040603050603030c1e120c0309060319050a050411010816080601050405 80
    0x3948590640107429a0300e807a0084000d003200c51000460b0303c285c0603200113018403036007401590140e071081a038071a036851f2489000b51070192000d00040210000800205000c3c2140e00420700051040e001703440c85903221002c001c1086170440c2d003100740742d1100b0034103061619069248101c240050600c178184607807012032054640d104031207020200c0d84940c800c00850400348a026032050f224800481004855a2101c1130030001034102030700c8540c94181c0806201301031245d5480c0ca220030000b007050002078a407082003001c24800c00d8680341044a50701044501a800701e48040000416451819003011000e03401484080c00e900d425100900c220314990800b000000749502412102003e001c02c03940240e441c1c040003c1c50010310306400d0050303000510b000000d403101c1c180b00f01c5856440303580380d8030284111240722230490328250610080c010491000d521260250f0300441c8082a4002c0300001075410600c1912048c85a05a681000c402c0c680300301c01d03e6800201c145446454a40c1d1000007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 29352802 1250 29351552 29351557
    0x1104030c08031209010b0d0809011b0b0115050408060606030a1b020f100c0e060c1603060203040b010e04020102030306300127030f030906150608040209070306080d0c05010e03 77
    0x1000e00740e1001964003450204001d030b040c1c4c0039407200002d1010307560110115071a0300c0b041c400188020000b00c2e030f00c2001d81c055a9034200c400c0c0c00e4403820108009908009450346000c0c0b20b40041c0c0804189054100c0e88280700711170030384550400400c1507440d00c60500c484d43d40004c2c041c40b03525036545c140c070010341090350362180c0c3c10f01554014455404100441400c1200005485407214507118801c03030b5007034000001c81141c4a08460058480f490b50b20080d0902411906a0a0030899160b01104114507030340038501030f60143d412440b0603070f22800804030510040c0c030064090790040c00061845d00d03001c0580c81200c04a0801210202c15480c2100c0424020452001c1c0e580d440b462418000a4200c08000d200c884c4110790400d41c480c69203000d4400d11051407001d040546800392441032000c0c581048001400ba03231006501c4659070000180f032014141c0c0c1c224807070402c0303801080900384240254003d503240d80010781055141c00200b66001502c815045a0070f540f20f005044040006002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 29354052 1250 29352802 29352809
    0x40305070501051005030a020105030a1404050a0308060105090f0607020f060c0d0e09070c030503070c0f06060305060f011a07030215010603050402030f03030702030d0209061204080a030b03010b0d03031104030c 92
    0x89403500c40100703180c41c5094032001080f03041c480640c84404c114556000a40c0b441441d02828100c0c0d49403510701180c4068141038a80100150b4031300248410000000f40d04448940a66203010355621804011202ca00ca190206176100034100c111350068507088005000c461b00c000c3c030144213540e00c8030204000f6008005010901d4111090307198849410400c1804488030880e0954698a00480083c0c0110400c0c0800741c108600880007403040b030301414416060039048520a588900350340750001c050595400b08440c24055000460420701c0107808450607a0600f501e144000051180c0f0310115030001202541188101c0000c515400754041e031a80c0640140e0b500412585401e005151501c610081c80440d140d000f0020850069808004c0c0d03400609231407000340c0c0c0d508581d4009070680c0615030310803002c003c4403414481040543c40080081403690380b01800070740b01c020304040c00c03107031040b0b0143c0d0444c8114911000084c0f003035001180102c4011413440c20310f03407640c4610140c11150340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 29355302 1250 29354052 29354057
    0x60503060714221d090613020a030b0406090311010c090b0f0702040609020c06010b0a020703020f1201021305040b01030204080303040204090c0308030702010608120a021c0201111c0c030513030503091002030403 92
    0xf0030600030120701001e04d0740705083e0f05110751554200801d005036a90401440d21000c0762460084401315602c03240040c1c011030f00440d40c00140e0410717003000d000910f05070b0030803004200042e4030041184010b0103940c030703020038a031500d001c424903052050034564044944107100500c10804040144d0b214416800540030b4a40300603290301200aa851078510103070400c5804000910840ea64581d00003200c4041e03e0741925000c82c62260307280420b0034500c05c0c07030722400c0550001c02c208803544951609481103500441d000c2c44010707400c4006500b20700c100d00441400742c00c100001005802c0c5a0000b461307062084034068010f03030752515480070a800c03e0350b546005035110201000210003c21826100807903a030074403031414041d110080d6944602e4a030713000080f024402004c04003030003948202e08510515503266515124050080129403c15101a00180c035020603852810701c24401c49114199400c4d40302d002600c00c6d202541e0540000b8040d441500c6401002035401e00035002440c000c03403194 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 29356552 1250 29355302 29355367
    0x2150405092508090303190609180b070306050a0b0d061203030c02070608010501090306020c0a06060e0f0106080115030b030c03030d0608070906060e2404060f080603060603030d020708130605070213060503060714 93
    0x1032a102f605420080c0441c000c150a081c410f018942c1c42030f0000007142c20080105a480503540c2040303019060507404540b078080d40368810414590148c1090014a00541c2580d540e207859010030390f0060006c1c0182c07400141201428000610103130b004140c814a100e0444000718410b03541e520560302c2d41d41083c0301c03614904040c400c80052081080d405412503050104080d07040001300340441c5000e480c0041055113546541000351014000f01d000c81c40f005e0700b035903919500c66040c480540014820180b02d44110380000800803814440c0c0c1c02502e0b42640ca1031240545d140801800300302e0000050102c10444078400000d00e10340000340300801b0303180c451810411105801501c10000103060300e020b43c00c03881c100102a5404411211001030034400140c0300c5606003007841440c0214444814160b81000001c039009811001810781903100f200d8090b481f038903001802c001d4804034032849030160711030004180c1c2940560b0354659038400c0c44040a003480d00001d8051108a8145055505140c46 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 29357802 1250 29356552 29356601
    0xf060b0301030c08071505070f0f020a090219030504050c01030b0307080304060305010e06011704120509060c01020c010b0a06091401031b0305010315020f0702150405092508090303190609 82
    0x600017000181008070384e01102e45040c200240480c814440000d22070300c0c5480c540e0081045450601d044c40390041d000740740039a12420890002d502080541e50041c1010b13507803440051281c0681d07441035a2120140c42c0c610900e20041d4007900a284a503685030203207030004541c6000801c081d00041855507070110320f035427515404240441e4060b04181c100171a044003200d61a004100d00c030f030040d41c001c1428109502e0010200c54a020ba5812154800340c0040c0e410310203241500030f000d10b070708406d0080040750140006c210300c40460744280000701d001c100f02086482c011070380d0400108818180820580140d0010017201506058890082999240180240462520002106030741c51200310b2403d0329a1f480e10f2090b0140709402803103000c800034140a04400c94083d90300a12014002c40300c1e030f091402c01480c0d40c080070810301c01c0f03141e081c0f4098042244640b0180f80590340301d00c09185142c96548402842e26200d03a102580b080d12068000f4500049104a944036003022600b84404101e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 29359052 1250 29357802 29357819
    0x7030605040b01050712080702011b05070506071b0809030309120a030f0f090512070503010c0c031b0b01050904030915051e030f01150e060a030f0b040e060a0f060b0301030c 76
    0x5240b0b035850411000748900c1001821054a94078011040e08102e20300799110b00d000c0380076107500070540f0300c24041c010590070b0b000e4000780079100c65441101542c44556a60500305c500d400502501040c1c447c1e00c980d04408240c05800400e02d10340e01400792450030080301d011031505001003424503802ea01840b0150145680140e07091101002d91910b40c2c4000c1080c0c034018030000003406958420303107044603035140c5080200700c0f81004100143c000c0c00344040500703002e0f0140446160540101c0d03040040281c07100c5443c5107611519500c90100411a404c100c24007500b03080080c01202444100a4007080d04d042c0064126140c0701140c0e207103655419441c00b040110341a122100030f020505000b801100b41c5240700650540b0700b402d005103808480e03d00201e60b09180c201403a0380008002540303005260303141d0008040e841c40c1840500203148400144012106c0500100099070008030101e86100666040509081c904150201d44c42d03807150300d11100c0364800c2e403040b91014030340d8208110b1840e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 29360302 1250 29359052 29359061
    0x103150c02060402060901140702090103031e020102070b0f1306050a0b030c030703050d081308030f0103020406120c030206031005031b011107030816031e02010905010b030706050706020306040902090703060504 92
    0x1039540c0301600082c02c156001c103920b07000c0c2041d41c034180305101800c207407204180c01c19585011740040c40c11f0540d580d80d040290000320342a2545600c0d010000da03501500780140225100c048e40000380354016034942c0c2001000c4180a4410150142c000c2610008500d00340640c50003007040e050005a209180000c16280c105500b01280c041c1d002800208040340c0c020401d19951000c1e400d000390140d9549604801c10015104014800440401400703140c44030100710b10f059902c00e5908010450729583c3c50380f6452a40307000200024030036941440141011400344d0780190b000d5809030403c1e619100040e04000840444440c030400e2007030340c049250b84c800c1242a01c103100c40050200300303007191114105d9200f6248841300d24000300060408240c429000c01d016140c011032000c1100441c1d0034024064900c4103019101507081c400200000d00d000704a0004640b41600c03850719001196507060081d40004095503402940c032041d03080561102c43d00c4600c030b52215940050200e060104000845 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 29361552 1250 29360302 29360321
    0x7020d0c05010810050d0f0f0b01030f02030d03110307200a08030f10080304090209011e0210060605191409030604080304060e0304060804030809010905070f0807090e03090d0f0209010315 82
    0x85612444c100001d4450100c10011140c000510070155035241c1056210050f0074000100115580c00c000030900c2424400400c1c980d100b00c0949120641004049055580d81d00010007000c0c01000480c0d1030f0f50103401701d034043c2e04144404515030058031070414200f034513507003040e294458000704008011a00654080d40704038180c0004160f9410980820f80c3c90045014a280c003d60000c0d40348010703801007241c010a0039005203e03803461409000020349480030303086800300c120308041001c903040340524203540b60030003140540d400b90501c968040302c441b9008502c405062000300441d0165403801d006440c40307140520f40b0780e50b0701d0070185852000c8a007020b00f0790348190001d00040c00041e41c00010070b07401c503815107401102070301c9070035503540140041c210040451154420000b141d0450307100079011200d01400b13132680140d60340041c509403038000040401c1c54000f0041e01d1214030307000d0700d002c8045000e4601c615542c0e880e50302203640f440c02a00b050b01d41010b104c3c80c4100e000349901034000f40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 29362802 1250 29361552 29361571
    0x1321080408011d01022b060509070c140607020613061b02030403120903020d0308190e010f0605120613031103031f0b07110f030322060f08010b0304080d0207020d0c050108 75
    0x100304040242405208034946c858014009402000c1c00260994005401510004007220764504054501504044081c032049810558251207100c0045000c07811511400664001d481c84d90b5800002c01d141e000c0c800c40856007682d03290700078215021070000216000516400840d900c030305504000c2102603141b00b4903010440c4604060006803940002040410340c9070600311400d49582d8141c503400d840d0020000e01d054074104a1748480c000540140000303c1300b5420801c80652500c007401004035000b0003800c120390000300403810081d00e040240d40c0b420b020b413428900204c8031003000350940c0c4c81a14190040785d940070500081401480c80f5000034841c070b01340246040520307900c00d020540f101800c2442049003070801152a02c0510446840846540341d099003803110b644407030344580040c0a11070002d80c0e010165000907000704549410f03200c0202803541076070717078550350032000d0f60110000d40e030724540071303c404401a00e6200c2200d080741d100b051680005130800d000104034580c010321000d00d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 29364052 1250 29362802 29362807
    0x2210f01080a03090501050313050a030905040b0a0506040e09150103030504030b0115020d0f02030f0708040305160302060d02030403030b1302120f070f0c020409170301080607051321080408011d0102 87
    0x84d003102c4840102c031000c1c24003903100d42c1c41140c0b1800031100c0070b4002d8424052503145404148c1e10011070419510b003141c04000c0c40c188801800041c0b2100c0c0145034100604200600060101091041c1d104056800300d0f84008080340700706c03882032020f91089001c82e002003001d2040120120009005d401041508a02c403003120b40004d41c4c4e441820042c906109014030541c0e1500d00c02d0086a00c51242000c05581d00c00d8580760048013a801880305a4290083e10100e4141030362411038a0112a00113162a041c10001c4103440001c1d44043c00840c00c0c196035a010034460b88440e01d6031008160030701001600c030b20090f181040c000031700130034070a0920b03480810000b00c66045201a0300c22217161504061809403803001c5001081070802c05000c0038400c0100120705c13a10040118144d0711888142c80c000c0c2c440c1c003015281d50294200c901000710498030240594540840d0134403007010101c44460340d0892030b4481101030360058100d0110f50351915814a201c031102c1e150450030000a000171407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 29365302 1250 29364052 29364073
    0x903060e150c070201140313031403070207180204080a030c05010c03090804180b030a1214030103080909060f040e03090f0a0f09020a02031b010b040501090216080a020102210f0108 79
    0x107500c4035006100e145140004900e101c15a44100c10f00b148250f603200410341d403414141c030803002041c18840224005420016071080c0d51045200790b900a2259400502c4100c5c10035019440d00d03140002801c50f2244d00784000a40303144104903c980c41e900a0311140520505403c00609403043e20243c84240b508115100000a142d0800c80d02203e2005a605a151a510403c0b20203082103800341541440340501c0c480610001d140503054482240c1c0701c00310400650440d910181c0001d1201520012081c0903040c0030341041c0c801180e102c100140108000c62805000500700c40401454049651012484070224200180198005242168581d000516000b0a025212240d000c2e8489568010402c001500e0003041525135981c0702011865880c048124440c0c02010080401ca110380d00b041d00004001b102442114408010b00c00441107001080c0c840070255400340f007003601103640c02c11101450002d02e21018a08503c1d01c0300000040c100f11701840f1041c10180c014001940203580d181 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 29366552 1250 29365302 29365333
    0x120a260f0402060306010201061d0702010c08010f03061104150c0c1a030c070c0b031303020c04020a020a0f02060f070807020a14011d0316060f030c020102090d060f09120903060e 78
    0x403035000e581100c00f5039413903403240f0040780580601c0e4804803441c140347d004050700501982d0154450306255000b0045240100c0086541c00c10030300c54102c0c071010320a818004281507400086468404400c203d240940c3c4014030050440600d4030300d0300040c140c0c80a0b108002c501040e4000a1500010042c00e0070a8140804900e20024004810030078000607048200311074000729070001c00000302078544a16003450103c5c0c5405d10004214010b010b503d01c070103030a00d058803d1b43d60b4001300354005c1805c10100e40d2400c0e0004107071081a42c2c0140c040c000b041003100d803134005028541c0300f002420f4840640d4418410741030095001210800c209031503980302c0341d070700805200d4182c54602007203d08440c02e0700402c1c1050105e405445002c0c2c4244000324030a40c1062201e250b4038202d45d401c10135080000412030807400b452004a038028548190107000c41d1450304071400702c0320360a81c0041d18842c43d0380c030415282c2208000b500442ca01450400601c202c5209032103c85150030302502c907540c201c1601c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 29367802 1250 29366552 29366581
    0x2010905030303190e1204031a0f010e0402060a110d02030904140f040b0c0405090f090c0a030b07030f0213090506181005090703090b0403080613150603020c120a26 72
    0x31045d94507800c0348034480703042040074490032448941036511601d0b81803691114094801003148a40c2c850042951550b250919604a80040101842c1e94445a08005d0640d20000003a800c0140c1402c1204002405000c0078100e010b454005503a81c842000c140720503920292a852031201c4801e041100ea280341e012000e40c059845002034402e80d43d94a0116190700582c0c0209420006240400c0080351001141c10700504928045603040350300340d0100403120f40380c2d010040c03001d8100340100b110940030b07400c0400e03224000400942000e071800164848102c2a611000000740c075201031280504000403012211007001640c2c050b9031410700440115600c1d0341c8101030244000c440060307a424840e0340680076103940081e04807080e05141c20000d018900548120740300720f1071040c2d03c4e82420098421714480d006003150b450455450003805500a4012504440c0b0500400f258082104241001010941082d4455186020000e90031010610b1844031060b080110341040c40b0600008181 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 29369052 1250 29367802 29367841
    0x1507030b010210090c0905090307150b0a0506070804060314070504030b06060f0c0703050712111207081203090105010614090f01030b060a02030301031a0f070c1b0602010902010905030303 82
    0x801040340031854004074a0300e4440038007060301e949800d56407001c200e5010300310300c2203803800346007440075403108001c85480384600300005040d0002c0010641c1c441580303400c40c5010000041c4100c0c0c42c2c0c1e6490001c179025900c0410229131718000007070305000c11500f612910012441e4158103841500c0c1025000c0c20a1156000c050040d1401000081140e51900c040301c44946506a4460700c0e20503222031103549215a0000b00d40a0140d4203004c200024140c1c200f2415642051601c03d480d0711100900c20001101e0030380300c005001d20382c400305162104010785402c0034214190140e0b24038102c181c041c2144d0042e08008200496407856900603c0c103401903501c0b100d0100ca02a81c0034468800603001094404d003d1a00000046a015900c40e00400a14126809103410a28505107489040609007080b108400181c49500c0802e814600c03501000090741c1c40b4600c4e80140598440c041141c07410603900c2000141e4584402e10115684040e1f25002020154011411420107a820b0039000c01c4080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 29370302 1250 29369052 29369057
    0x42604060507080d06090b04060b270a050301050c0a0207050a03020618012f011a0306010e070e03012c0105070f0f0504030605150a0f03050715020309041104080f1507 73
    0x103041c2c0500010404480c442007206004100140d5a403034017001812040009621651500c040080d0404601040303800d0b100e00f407100620450074448039408082e4441d421540c000f05d10010201da540c8003481441e010b042d85e00740d00b0741c58a00e0301d80001d00d0100c041d04400d002c0c21003940100010b81b41d240070741e5024803100e910303d001c2800d5078004070341100c1c400000c3c0005681e845c4441586c50380d07010640380c0d400c60346402400442d0042a5031109001d002c4c011640690007080104094048400106c1d0000324038600716414129020000b0300b034400c03a4815681169031b030300403107001401414140f11071102e420001d200c14600365802901c192007004450080c0010200301050701e600c6641200d0203140d01010400031800c10014800c41148400e504e0340c000d5a52180200c6e004003044105412240d100008150b440e0502c1002c0c0341c41e22500180c8819440284212091555580681000c0714003040000c0d07180c1c0d1404e64128a811104483e100e102d03000090100c01500400c0301c40c6d54010b0207030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 29371552 1250 29370302 29370307
    0x306061002160f080f070b070201030b030a060f0c030b01020607021e070906091a0d050a0314090603040f060b010903020a030209090a1208060117061305040503090a0e0426040605 78
    0x4409030704202c0660301c4024240045040407600b0000103000034280c80c02e03181198249031080b9200c503a698121b01a6100011040c0a010010340c442d4200e0703010b075140a000e86104810350b64880051783c032210030200d44991220000a40154184908104000f0920040085080910020b0340306d1010b491003001e032803548448060125403c002880051880150822031243d8030f42909009140b003c4107200b03030340384002c401c04591601d254074001d229000009444208410740e020f0720389036421140c0d8825036106020280c0a6500c03070f409548601d01a28551895801e41d190410403500c4014a503818042840da0600160700c0c0c09001d001501c2d41560740c030031a41c59100400f80b8040c0011002070010b4583c04018180d60391041c82540204000c0e01c0701c4040385103281805088000448040c0c3e002403240b80580200c0740b0b87e411540d0064090790a4074648140c500200f1005080d036048801010780324410301081052254040d40580c441c00c0f0494824030b829200b0110340d2040303110b42c200f0000301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 29372802 1250 29371552 29371579
    0xd060b0103020f0a020a0506010f06080106080703060314060f06040221040602120403021c02010522030c0b0112020a05180103200306041101020609060108030409091103060c12010602070302030606 86
    0x2541210f00c82210312010b25111040f0340c0d4002d55a0a542c1c00841e0340d03004000000900f042400040e500303603141c0d0f4a401e41c05a0a0000460303040c50000d010030f040503101d000005c04038440031611200404190040c01d082d250003542442e0089010b04801c0c0201c2c810055181003050412806203480403654101c45a034480f070500310040e01401d8401d0700b0708020001131000301a000580c0104240071482040c1d00300914a10590803940304840031941500030001c1c0c011002c01e40c42d01c0e0f00d03d04d8402d052200b02648962075900c40b0440903040381c0001881c0c001c02d18154a041180c50005003811603404000c1202e44007003002500701884020500700e01c403400d10381c00c0c1c07d0901039104a0715000d000c0700c803140352505042d140304810590b00d9015004020100307028980c0810954161504540190b1401d464100c41c0f10044c800d0740c0d0103603081044010051441c0e5002d101700c0d8020340103250000d444204c84041124100d806903c00404c2d98444002080181c401180a940c060030031079825012000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 29374052 1250 29372802 29372807
    0xe010e0301090218010315020705060610050c06010b090102010e030f04030209040c080d030c1d0a0302060904020d02040906050109080f100203041104020316020c030111030406020c01020903030f0405011b020d060b01 94
    0x300c03040254042a42000c01c0904d04240c141c042c12240034400352211801c410303484030b04a104040d000b40054114900041180c03c040d851140713011500c0ca4200c0c136188508484908041c001e0b0001d251050001603034203010340e4240940c11400ca1804095441c1c070745c07494501c40d054411844000d0040e800304001a0500c900f10505a004010600680ea2101d1219000034020320101c1101d50104104c0090398002c92086082d58010280280004070804e080d0380030400a900240e1156911540810426869a400e07001420040480c0c140200740780e410800090314541017900003148650200c0c0000e803660320002016a404240154010303503c1e02d440c1411400080341003000c6030851300000a00001400c0360030b01401c90b1000d6400c0d070720241e0a0f5010582030b281c4581318040b1000090001c900810480d40c0180000d2980e10001171400e2412004641181c00008100b0546400810100000d5070400c1441e0400012450b400d103440c0840e6001680403100d015001e0205540c4041c00d1080380d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 29375302 1250 29374052 29374061
    0xb07090f170f0d020f0706170f06030c040e06190c050a080402010912030c060e03030106050a0806030309030109030801090f02090a1e090501090207140309090f090a0f0309140109060e010e0301 84
    0x50b00309068620f0500f603440060756461030703c03c07201e0341d6109a040018007070388114550f000000341a007214840d81c9480c0c0c0d8142072420003038101d07641809400d106031a199194898010004101400783c000342c2b514410030340c02070307141c0340c19a9445802d00780080c020070352002c08c540046080d03041858281d1120300040340c220f802c941000303e83c0006416640141500a08d1131200303140f195105104407181c22540c15104d000038407070300780802c6007440319001080c01008003d0307001c90090121390030502c4240019080d1030340c600c0103a0201d00b1020051205842d030703000392400c1c2c2c12401801d6160541400c04204d24079658800c00012000d404060640d80b8000840b0000a2641040c203102d035584aa0102d0001d5019040c12900003a001560f040501c6001c0142c6103040c0005103d454581c0e46c03a901d50000f0000140318a1641c0070b00340c0150002624012560b810318004c2c1d441d56402410320b0312808800b01e904549906114100c8020040182d005030350401051085c81d008104d01642e1000c00d0250 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 29376552 1250 29375302 29375323
    0x80408090a0306020d0f0e0601090209060c010501060c14070e01030f0203010207050f06070906080c040902030c07060c1205010e06090115050903071409060105070b0a05070504050904030c0b07090f17 87
    0x400750740000428001550017406828160010401c002c82d036082c01329080b10001e00403400113400041c01002041c0f2030b5070241a60b1200070308074a203014001400703a800c44000740c0040000c41c00c8445000c0034840160381c0504500c07521401000510708082081c2108081444003d0180c1c581d2110b1031700b192002e4041d81d1145034000e003240c0d41412141c414580705d24044811400041d03030640009000b600c0382d0081401242c19a1406280c9410095508061751004055601400040044100160b8181710b1828085c45960301c50f00d1401035841e1000907500180e00603001036412400780080ca64405c4139181c1141e4101c2046010ba10300710b001a0394900400700c6c025454000c04600151440c0301070b4500f074518000300c030b002d81c0c0f41d0ba50f04015a0303240501d03140500704c440d00c03000207029000385500641c0c000c00c0318145113092550b554009049245c00701c4044000600803020b0301c040000c107428480c1c0242541c20081c60042c10704440b06c0d40e94486218400201c80d850703594480a200520050400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 29377802 1250 29376552 29376559
    0x8180607080a0f020d03090305030c090301060b070302070e0c0405030c040f0e1608210a05090a0312031409010506010c0809150a08041e03050405010302030a0b041806060b07020102030a08040809 85
    0x2d44030150009414410b1000082c005800341c0311001d249244207101d04a815603050f2511400c545441d03880b1910f98004160868042d940c4413000b1841a41c100080d04034203229500038030080d400c0c03221190340128043e1401c56800000d10040c401d942d40403801c10125003003558001a110f9114030402d020b09650b0303e61000e18014803c41c100206c144142541c29542480c003160403280c0030080b0303188541c810081400e09420103011080d5031510800041c6a64500200183d0449482c6d0320b4080c1aa4400205d41011a6880b40744105c80319400074620b5001000700001c024900c0c02c2000070308212448940102001d00018040c2d956668440b100d02c0c1c0c118202c4201e81d2a0b1410410240c04400c0c20f440c1941c0c03c06e8072403040440140100500700186034181e94980c14146414010b4000e50005030072682030303a894a0015855850313511a01c0d1504c00c450780800303a0080c01c0c1c02c0c280119070940d040b050441804100440140c3d03000012104440b1062800741270340d40e96030500c201c1070701584035250b52 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 29379052 1250 29377802 29377807
    0x1050304171903151508040501020f040e0105120a02030c150706020a03050f0f06150f16060615021207080304080408060406090201140a140d091a0f01050d0818060708 73
    0x691a00c2c18400c041c001158904100d1001182100921069244142034121210105a0880c41d11a07a190340e04107109030f0001d8144600410360100903002034001841d00c4003400010031542c46c004003c41c0040840d1406012015131540109860f4840b0501e002d0066900c03050040007000380c6402c91302c80b80c0c1c111100315201c032461003004002d4441607650403103111000c030100d03987e108001d110500664000b400e83c0607182c2842c01401980d082500200307103890003800070b038607840b25039010301505a01c40c20002495900704044694141e0240c2420011036000142d8000c01c80410f000f210200c80c0c0003901c02d81c50340e031a031409902c2ca05c61500944110701440f01440200942c641200180902c03d0301e8031440d10400c0c00200c419406004c80010008082e00c181c2e802180006000307215030f10002101244101041d106c8003000d031102c0700401c241c15001e20400c4000b0984050f51303809044101e07544d285100e2251a010b24a01840c2d6030041640b40c400c5840c01035548000484034820390051440b40c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 29380302 1250 29379052 29379067
    0x50c030c060114040b031b0d020d06050906100f35070f14010f080403030f0b12070e01050906030304030303050a06050904060b04050604051003060b0613170c031207020105030417 78
    0x1a40624103d8aa0300a50520703000c95824900171514143e001c02104072a40117101d001c2c02c02ca8081100744050360030503441c9032003a0100c0c4450103610b1040f24040e004102504103028003503250611940010508030982034180100d41c40c1c85a5a60903500e0151035aa041e00c900c0074613600d203000344490040e10b10803104001410540084403004070b5041415400b0380c101040d0055031039003c00f8a8680002d0b4000b8009000613010354884078040130407a0780012200d500c6004618810b600e11a08a1660310a11040000302c80030b0741c42a02403c0152110440c50411070003090307490060303000003402d0503113420020308201426400072005000050105141f0305103424a5030003010740116440c065410040007401c40d0500d03008140c024119249007109252031038442c03c00415040c800740b036001d6805c10420000d9945611107a01600242a01000c40c1a036000980d02e0a0081101140260401401e88100c0c9130303114241c03402341e0303028208203540b6a95031400154054003591085405040840c1d0740c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 29381552 1250 29380302 29380319
    0x1605031b041506180602010c2007030503040617100501050f031506040306140a110405040905010f0c0e03070602150708070e040c03020a0201060605030108070311130e060402010f0c0b0106050c030c0601 88
    0x4982d94590f204d00d0440c10b03440e0841242602d2000c5c0c12480400d0741c40f2401d85000035103c202c00349aa00800a03683c26584941e286404c1d1303841640840c002512101c200794500300d1000030a40c204100d112681e08a0345044006007282c01b078144251010040400041d401c1042c8644401d94441c1c028840c0c0c1c3d07142c1c0c4a1130700000030800203140411900340c00001551110b03d0740f0948801200111400b41002d16104c200006028440000c036074a540365807101c040d014103400742124203403054035501013000041042c580703446020f5108200710351100b40401d8000f000c5010140d000040c500e046480303540c4040c000d50351004912100c2d50483d2611a40f01120b83d03055000c0d1545c00d215074001d201095403103134111805e000038024160143c00c104020000100158503007404404094a592004040d201e8500102ca0b40d024006540c1d03002481040110b69024400310415a81c60a11b1021484030b030710350000c0c41505024450603c0400030382c003441e4880800c03e036080c0101c008122151982c458210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 29382802 1250 29381552 29381567
    0x405030712080f01080d120c11011a030c0d1203150503100c08010503210304020f0a0f050102010b1f0807020f0d120605010f0507030806060415020606031605031b041506 74
    0x2422240340940d0010500d0200414545d4503401e0550320510300030040300340c0704000c140440d101c0c000d100c0c4c2054500e845003022f0040d03190b1020940b05400320034203140141800d0980e403074920391007943c50215541c006244982011002c3c0d2051400182d0340001290310b4420001a411140c1e0510603d02140321541c0e43e5004045036000d15503a01c042a41d940f814184d40708440c5400a080f42d241c1144604109604000303544e005000409c140703044c1031201e0200c1d50036001c3c0d810121890954050600045d60240540c200d0450180c0e00800542043c3d260150000544000d4000304001580407454084c0700304801c01c1d1158004042e1000c030851680c016108503603106800b1405070410900086940c01040749046c1101e0688506142000301d41d81260202c0e0014001940b041043c0408a07290b9562500c0f9125118141c00501e65400c204040605d0045a40041d8048003031119042c884c94070b010680e6404034508008090b14041d030407002401a00c0c0511104000c130414001c00103100e83d12128 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 29384052 1250 29382802 29382811
    0x1050f030141030708070501050406080925091104031110020a080f070308010b04050d1b03080d0203070e2e0c06020c0732010804020102011d01020a030605030304120b040503071208 79
    0x8640c943c1c3c0e505c03079015490708168410345000c1101400100300e82c900947d8200e90002d02d54050f295540008618001001280c0c0c1601d403444040708814000c540c0c0074031a5004202e1003485843c10720340b96a841c0129403230380c0b00d0100d001d074082c1ca5000d0a81c42c02040344e030900c554000c228913200d4072286188141604120710641c00540c901000160301908031003100e080d503402405040207c40e050701c4081c05010a00000c090903c01184000041072650020b00004c00c84c00e1805603983c01c180c2e50051403503205440052040c5200b40c116008010640702d4a910748903e1064444131100149041d901b182e5108009002d00f4000954801c0502000c1800d00035200c414007031400341032113003080c100301f9070b034040c8800e50602004038024419805a01c4040e40984140f00200303582c10700d440b1300d40034502c1280c01e61107260b401152641702150180180005040d00342c0007035080900e002405042c4055140e0b01030240d04d01e20002c107003485800d00450300e000b90828802c0e4035080c121880201151001c94 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 29385302 1250 29384052 29384059
    0x3170103060b10080105150705120a030504061a030714060d02030f06031c020309091012060506041109090606160507030b01060210060311010f090906090506040b01050f030141 77
    0x51000c3d000c0303401511a5810380b8405091309900410b455000b07409940044c10a90700c2c2e1007440007072040c60180304000d00ca0004d880d0b401090b82c2c01e00c1d241040503510b42d280030307070810f18042c00d051407151000602003044070221a06007410020980c003041e914400c554111503914000001c110300400409240c500842003507045824082102d000b03490252030071a1204c0c01604100301c140f0803450501c803030907003008180e40820800b9175030703504002c0103241c00401190501d8070742d0104111417030207206148400401d01c1c5c2c040d02d402d20a100044ca4a03c2c010f049070b20920001c181081c80348190030070b4202c40c903441011111010348a0a003034032400c02c00d02c5500018480c9101e0300201d1900307402604203ca80c80712003107402c03490480c015641c40c400361002100704580d001300040c40c8080c900403d4003c0c403500c5000641414154248000c0e500400c40413814040b0401c0842603050941c8100c90446030000d903501c4c3c104042e0041e09607045403951a1111a035441041c65410081c88144d810410000701c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 29386552 1250 29385302 29385319
    0x1005030a0c0e060609060708090301020f0d0f050108060907030314090303040f1811090409020411031501021213150219080405090a060501050315010e040e0c2b060903170103060b 78
    0x9030700704160340c82817a0030f042e00803505000ea000010f4509004d801e2001b4001c00241c1041800722589505030003600f9120318450710745900305c0c0b40f80182c0c891180907001000203040545842e1028543d078442ca4480101001594010510082580e00036900b10103002070599640380d9a4000940300481c481c02030004850030b96500845400140c82070640c04003500c1d03021030400541d030301000024103c20304184d8200c1c0e12105083e21203000c920040d4401e0511100c3c0e074032594a00c42c00240f900d402c0d00036a0341c3d0b80e8010844032000380c2c2000803000071914030141440000c040c0c0c8604905050440c05894100e1000c407a03200200807581d006001901c405440040456540d04491000c0c1c40f4944111b81c0400da0070804155410f840ca0301180c0419018100300030f000c210341001c60704445054540c002d0135041000f000e1681d08d007003102c0e00e00713a0b000301e1f8600c105103000110030000760400307a1008111030345d103202d900300705809124561001400740c00742d070a240d80d4906140000e0400d813880c980c4a4246c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 29387802 1250 29386552 29386561
    0xc0801060306080a021e09010e0106030e0307081902070e0c030114030307020d0206130317040e0f01150f1e09060212070c14040209120f061312081005030a0c0e 70
    0x1910030b0700704031025080144a80b100640038821503c1003200820880e5406002c0c803000c5403a5480198000c28132a102d00c1081e43c0740c81030040071900a4500c100380c54000300018004280340c030080d600030384c034001c40c2030b00f240c40c5c2e80205901c1e28480b07903c2060540b1050f42008103000a0502540c100e9400080458181e8440030805840c0c0c0702c2c25500035800081b0051100140c213003d0081d00450340d1445503985902c1d00ca8441d4400c0c40c1001a0b0042000e40001c0c1c207100f1801e184028541025900c5451551941000002002e214035600c11004010f818030b00300400501c20030120480302d07090050101100803601d0001d02030952401160054403d9071010f4404000c4031040711a020f03000000b90094038207258441401101c100c514075406078007032190285907907030340c407102c5070740c0c5511001030040c001c4024540d407c2040c02007084420300744030b0400d440030406011801d449803200d4a085035059944600c0040b51406681010390140b04886030a420000110150421386031402d50044c83e330344e81c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 29389052 1250 29387802 29387807
    0x1c02030307031b02100e1e010504060b0105070b010909150c020616020d0203040b0d020409050f04030801050a060905010807020709240e0105010f0f0302090d0b16020105060102060c09030c0603040302010c080106 92
    0x40f035544070f100580c00541c030140d400c55250f02010502808100f070b29402140f09401c0c1c4000c905210b941005655900300740010815180704a5000c064282006401e001d0543c440c443e1007141440b98032056034681c0511010001c0059551030107141c004c0e41000420034580d40250707101c5049400e0040c41c13081c50320701001381d400011007007500442c680c000d601e09814100030000e160400c008100342e5580a01011408500a0048a02c1682d0000d1899524a424240140304240c10b90100340641008038080c0400b641c420000401e9800030b0a1900003a1110002240380504542c032404225282600c043c02c0c00c209801142c1143c4202d1401a14803a151101d24010702c82c03c1c80307041d012030058501d01e41150301840800440001da070800500300021030b00803407001001c1d81800c4412031030542c00c00c40e441510b242c1c0d45109810078030080143d880c0200020307599070700141c403031803e440011859201030b690030030203c145000f019251540780c0c1018a00a80613000b50480400416010700c00441c00a2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 29390302 1250 29389052 29389091
    0x10b0607080705060915010501230d023408180d030e011202090d0f0203030403050d050316020d02070e270102031608090d0c060e031306021b0901030b091c0203030703 73
    0x2502c1c0c4c551065900e010015202b00c1c08000280d1040c9030f00d245030a4043d004000540816456000c0160b0303514080c0000003036400c031654502480b1400700c290780100944039160701c505650b0101b803007a59601001c2d204802d8903802000241e0101c0c24041d080c04150b4000e803050403031182a200c581c0c01024507580c03502039010b01e181594000e14080e44040200324501c0c400702aa81c000340c01d60785010345a80301c0d1420141d048005d14003290001042c00102511031943ca01c07041000d201a050003d030035130009403190030a100369078039580110045500c14841903481a609000844041c903913065050f0014080c1d002204da204001200b228100f0455016080c01c0340724101c820041d0060003d00d25059687c01007400c02074502a5540d43e800030502d004000400012003503030710301c04120740750680081c60188424403901020703a551100c007805490b00b80000e41907030b03886031600640f65110700d070141c5800101d2035058032401030140d00c515103907000700013503000d5281030b80d081c040071014552102200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 29391552 1250 29390302 29390323
    0x20c04050a0902090408180607030e010906050c03031611010c02061005030606060a0f0203090d0f0203010e07060f0c0501090c260a080a03020a09080709060905091b010c0302010b06070807050609 85
    0x4140c50001031700285159005144000042410100700b282031408583c0980001004802048a0340644155503820a04150061407107182c03807807400410315152526404060180c3c111175802c40350051419001d0301151200c810600000c00c00d079051604005c3d520441038411145210303036404085148d040215800d0710644010b0100c0c1e01d0000748076030403200d09100d5018481140030610954869903611610721042900031a00f040c241e000500406085509415000c0010350005904202d010341080394141ca801990805070010082ca0401300e025040016009044895803e0041100038481c42440c0402c2490b807524500603074001001a40e0b072070440d6000c0e012160a101c00085c03240700c1d8005140041c0c1038035100103180c0e55405170705c1c50f000c6607401042701907845290500566a0354810b440d8030803547c00003802407212204d0701e200b280c40300000070b41c100044035035128103041c000d40101684d028064101540c6500074108100d51303420003401214103001c0c1102040d01e600c1300085d80140c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 29392802 1250 29391552 29391559
    0x504050a0c050a1206080109030c0210021612081c020304051c05031b130602030c010c0201060f05060318070f060905010215180703060f1b050c100f0912020c04050a0902 74
    0x240303a0080004e880402c011401c0211035512080c01140c0d001081c0515512140710b902c914070796034890300c100f04054040400d02011036202040b85405841c408600c10220742e41c40701d500482c1d03a602e043c02c10382d074803030621041c0011148961007081c4c1d0740941e00030b5115600071000e0b169104500e208035035040c20184042c00c0007882c2800402c0142024007000e12521040100d11441e000160000319000004c583c400f40142e04042101600c8580c207010768010740080348000c0000906203400c0d01d03542c1c034541c007074030780039210100002c1d1300d401d80c4c1d00c5182e1400d44c5c890219501e103139842110304110031180c051000014034550000a065000107800303140414a00500d070f4072540c41c0d502c20060710f408130452031400c1c42804000000f140d2984200980d01800b05008900c8000b10801141c040c0c68103205501000300400002c251544045075580410401180124000c11000d4021020f046410310140c26082945824050b4075000501c0c110080810f59092169a4906a006040b10340c0307010003070740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 29394052 1250 29392802 29392807
    0x60c030d05060a090f0606180e150102011d0a0201030c0807020307060b04060b2106090402090403080411091603060f0602030d0e030417071a0901090302010c02031e070504050a0c05 79
    0x8441031a0040350740803501030003840025540308001c8082c3c4500a2040000a58400e400d019842d48500742652510440c1031f11a10b0301d180c14884030031104010550f48001450506c1111903038802e4100380441940c0c18505801091540981901c40e0000c00b4200d011074a0701c100c0100080c0500d200310700c1040660091401c2c18000d440d620702509095008a80c01aa50b040c0424030a001c0c6014085402150400d8446503500e094541c61401014040510402184040000503070b03800317694561059051801074243d498134074010003030101d81c00540358882104000c0281290100850310000c0c0f2a40c4c0d020310500d82d640d919562008030902440e40141c10400c205090740c9001d411003c00110a1021289415075501401c071101c5121260410385401c104002c0162445124100e81c0460032400c40320b140800a0b00080c15007401444000c0c140100e8951000c00c3d5a824407482c0400759040fa000d41080300340d9080181c90b4903c13400351902c81c501d040301003880080782d80b16031044492070762912403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 29395302 1250 29394052 29394067
    0x80d0515100503040609050d030f06080a12051e030403050c011b05030123030d110708010c0905100c060c091502060910050603030408010e0a0317060a0504020a05070507080706020c060c03 82
    0xc5050b0300084c41950034a4580d45a0070020700e04218610328045160340c0021003e40a440b80360a403002d65000303074541cad4481118074001c01d114400494501d01941840e5030342d1002403800207507540403103d1035040410044108814990814001c0803400d800d90002c1010b01240c1c8148c1c0c000a8400b801c1d0400100d0901c0184010004e010106004007108583d94950f0340801c0300003072410145100d000009a504500814480310030802d41c0050070400c3c0080c064001c140b40c0017841a8003030302c40c080c810300d4005021170005016841c0e505009411131003c0c054044014400703081031016119180584400303401c251016407010461034050100c501c0544030007a413102c205e1000d0080500313801e505000c20000000c00032024031a80d10f401d426a0081e14000705d4a0030060314070010340000030400d4412030b00300402e640d00ca26901d01981c404980050b21030b80080300c1101c0c07038004c9900003032403072040729000f00704500000390740e1007214490b030300302d468404e428414004a409814041890780c1c0c001d00019 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 29396552 1250 29395302 29395307
    0x20c0105090303070b0103050d11030a0807030b120d08090d020d0806090402010207120b010e06040506030a020409050102041208040807060e0a030b06130f0c0e010201180215070203060103080d051510 87
    0x700007003000201140c0c100b2007541c07030790315902800fa0710807502640300d642a02c044c1a0045003442103900f000c00510308100c07140a0140c40003600800c1c04d010160789211810507559a000e018140304045130445010542084014040c010103079032180c100c1c802e042c2d40303203007240c40018031238614001030361400400e8a94038180914880081c00407410750096100100d00031141c00e01451035140101161001d551408404491080300038013010300a50620007000b5268a00182d1108102e5054500280d0180e0a00701240203001c0e54100d054000c1008607032506022010f805082910055010b440c0c2e42c2d5500c11096403100b0004800d6070f0010520042040420400c1c60341c40e6228001818150254020314440c40840d904801201a41980c6103c048001a4022000d07891560207000070803030a0032160400e820711100e884028401d18000a00b818030083c1f05041c1c810855015007100c0e815612440c3c240b00c180c004043c0403858a14100c0040c4400b409424076842025000d031000c0789424a4007401c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 29397802 1250 29396552 29396557
    0x420160206120c130e0c070b04050f1c0305090106030f080c0304090f06080d0806010206011a04030f03030501060815060405060a051c0c0207050d081909150203030a0509030703020c0105 81
    0x5a91107001402141910906144510300ca03412040380395030f48450345000324003134039001e170008030000521000308030361000ca5004945805030060705c00d4460b550f9a02e4401c0c540244404481018041c03040d0b030910192240700d00e40483d041c240ca00340043e5030741684580c200c2d0030500c80070b0400b41d051001c0c0c8000c29401001081045100c009491501e03444404c030005071042d0b640b000c1201f03651840104040402403001c000350580d503241c421218200100000d43e9068180907200781c0014198621007600600000c90b00215808481c000f80580d0301e09014004000c00d206170004a0b8650340096120380c5480644225501d006003050304060502040c0965500620104002e003c4100040c0d0029039010101042200c0403002c0821a040402c00007414250103a0100340603c1043c11507200007052002134a494050003102850f00c07255203e4115299405580010049241c04000045040c1d01000862144e80520f20500083d1618001e080d0b4a1069500150060304280206012584600700 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 29399052 1250 29397802 29397847
    0x110307110a0918020901060309050c270906010807080a08040b0d0603060207050622050307020405041a01060f090609060509040f110c0705040b010e090403050a03140a0b0420 76
    0x1807600e010340316071030002251607400a000300195485100821442c004158602400440ca010701c0325502580e2030640d16821070b19154807848041c41a84402546140030070f20194100d82203a00350304000b40e1090702d603031080c01105071034020b188021925900c001503c80156500101245c6090f00d8450b545545ea000401c001c1d2005466250000120f201c60002c2c004181c0030b07501600c40340c2000703c0800e02803c8070a0107403000c410303019142000b00303402005071011141c065a0124195840c4c1c986002100b03815080c0303a0010032514004911140d0000200404108a03280c107240d40d5228182903401111b98418600040d80400c005551410b294104202c00780b2044004a07000008802c501b071642c1003d80100c441307901054081006103001d00403031240700c40070b00745082c075502d00030b0105030030100041015061040003c0d8000380d0920076484400b51101100180c506800c0c21100d880140104107695403040b401e210342d01c00c950807040c8641610100303049285140000e42c0c0712190b03d1060452 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 29400302 1250 29399052 29399059
    0xb030f01060306050117071205070201020c010c09050a03080d0e03070308040302070807030f060b040609020a02150f040b0403140c0d0c030f08160c11090c090109120b011a0d0606020c0a0611030711 86
    0x70940039580d48d940143c6004030b150b0340016071144600e0104d182140c180c805840704100310f9180c20422502e0714408182503e80052205a5483c02a8102c50190025950010061000082840a2561096490740110b11030b6080e1940d1540e5401450f80d20255408050203000309011500d0000c6e40f10b9011400e540405000170a90b581c5c0d03104020102d8020021100158000000820481e0f80203d482a80030048040c010020704142c1c8800d45070850041004050010a91a00600c0c4500c0710a403900c107031402045508035408035000030484840d00108a01045100c10240d4520703000f10300c0c0c60710800c3c940a0007407039612030f11300485110a000109407021444001e10003000c1e00c0f2a0440c2d4400c2013040c0d402903540c0d4000c400140b001040b81c1c00030b00d000400000920001d443d090410303046498400c000d4036500b004c0110301c01c0e5440707403400c1000d11030314010000540580100d65043d580c03404654081c86581d56a0041d0748400780c603500000715410800500340003403191000c0042d81000074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 29401552 1250 29400302 29400317
    0x10315110d0c20060a0c08011401030b0a030b0a020403060b040507020d1d0603040501020a090f0b0d02070303020c01051510050c07032a08010501031e112202040b030f0106030605011707 81
    0xe011241025040c8401d040f10342043c003c014a60b28140224580d00c40d103031912081540c9000e034030601ca448008551810161074004c16609965132000420181da00400c4c40d00700340c04c0012003c0e000b90300038401200c00c039040401000451625100301c0744581000d4000d40050b01c480300f01154040f85c602c11006a110100c40103002580350070001e144198800c2c000180d440c0c201000c081c0198845d03510200b618410341c8170500000700c54a05075803416103180d0340503840e000c191405801a001e801c180d00800c0d80381c5400c00843d03200000c0102c2c3c4d504801d5454500e40c10609004450500c660040e4130880e42c171507141000004c2000e1460312220010580c052403204068412103070728000ca5100d0300c100d80d121070043c01402050500c0c0010340e0300528a1015541c03503a0341d0f29920380c140c0c11103d4403031542102d61941c003000c8515440819020010f08541e540e89a81803504c050300151840c407489541b2200100c1e00074024171a1400b41c880c16143c1001d21280601c10300c9240400908007030411541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 29402802 1250 29401552 29401577
    0x110306101202120108210a050c1207030206150f150306060d02040608090d05070c0e15030106060f030605030102040506040e13050a0807120f0e0d0f050312010315110d0c 74
    0xc034400350099080d2030044801c15454181c101d443e00205095a222800410105a00e0300c06580c6c100c0701740d80d40908066403035098081c20141041c00c80d070300758120f0450024950b42019400701e0b005108424180b407501d80452002d050024000582d5500c07600210b03581c41410b0007003500405182e0120005224071318041c48490004c06036000303980b001010901407001e04c00c4901c1d0502c0f032082c0e1b50100d4540300d0b00300700b41900c0382520542c2c58413681d05900c40c40d40c0030600204e5440182d1120b0500030b00213001c51960f8080042c401852a51118002440d01c41d0100f5245018000c80b030403520009e10701800c190a081c40c010046030098039400b4100340c05070070240015814041c40c0c0d8035600400485448458500b010680489540d0240040001c5141800d0401e03402c01001c501c500d00030f079240319103040b0902c0e14660f4001e0140e005030161002003000036010440c00d0509050741e1003107034009242d10310f00143d1801c1d120b46207004452101d0520a032545050254801c4c3c0314045c07030f440e00c0c120480a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 29404052 1250 29402802 29402837
    0x71d04090606090506030d02030703020d030911030106080c0103270b06061b01020d050a020a17070201021c02040807060c050c06090d0b090c040e0f0606060705070b030a02070201020c0411030610 85
    0x30340c00803043c540c0f1041002940e180c01e200d211030768203950000e1890003c00c0c0d90002d4407206144000c0c0b003410398864a640501c50030011101900501070020420306844010701c55480d00e003821aa40081e013031984011411201002200c0c140c0c81c10380d1400d41e4914282d40f000070707940e4000c00c080c1d00074200384682c0780800b034401c0180a024100f00001a0340742940c85400c016100000d00c01c80203c0e00407c2805005507000c2c1c94041842d90700820403a0b240c4448a08a0181c0301d0402d0310b2903100040389000c004801954024400c03202c45400304c800755640c0b24420b03a080d1074107410182203504035400100081c200000200030003000104448006031041d0380f242d150300c4041d03070603070890b501c907400c520b541342064480ea600b0300302002c00601c0365001100500d07980d000000c08041c0101000301e22200bc1080c2003180c000a4291107a00035100d01d000c0354100000c0d00148801c0e8010310500003944620308107031150845035040c0489180c0303107a482d00b0503c241343d03203000e02110230400c0c59007800e52002c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 29405302 1250 29404052 29404061
    0xe07050f070b010305010510030209040f140703050606090604060b0d0f15080a0c0b090d031d0d050a05010c140706020c0705040f0e0609030c150a09050d12050f071d040906 75
    0x5210b400c00c90307665411800d040f400c4030320017842d003907440c03103500c0b02407015030344586d800b41d0702680c8041020f03141d80c0b851400350611503c480300d07284a4807070103101000b000fa01180b220f20400007525540415650380c81000155242d034411401400020040d0000301e0314650440840e0901e1101c021942003100710038942c4680061380202010b4110290400802c682c00080c1c0740240b034201240703400e156420001401c0d40ca10500001c040c0f01e80c440e080031400042e460f82d04a08040241040a02600380c18116202d0003050303000c444135481e0441e440c145500400840c3c0001c10a4030402d0f062000e40ea5a040003076102d80e001c00d80c2441030341c070000b80a58480c040c4410000804038082040d02c0d6801c0002d10701040900b40540c640c00510070b00641c0b01b400184040d42254003504001d1507120396030030301c004102c103940103405d5000702d030300701c500c0c46400024404a030741800100708000d42e90024450031000c4251041d00c002441000b0011008481113118132101c41c0052000940707103c40e580c3e05003201c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 29406552 1250 29405302 29405317
    0x302011404050d1a060109030b06040209120f0a0302060708010305070e06120607050d0606031a010503060a0801020a02010b210703021306080102041508070f081b0903010f0f0c0512010e07050f 84
    0x640650180124504c50030302c090b400001c00e08228403d42d00310741d5203103014000100309600959020503852010ba42da00e0101d0510380901c415a403058901ca010140c6a0700d04080c140c001d8802c50020030f4080340b203690094100c03034001000d814960304080601f000900082c200c550300c4007101c0c0c10391403030403020302c4810b000b9003294a0b9180e40d42980344010050f00c0c0150321440606162624140e00c15140c0040e41c410390750b0034a4166030307d40da0400000d403841d4a46d000210700e5880030039202c00d074640540c464044014101c3c3e4184a080440160000e40c150400742c04120f508210320420050500342c004403441c107003002c13000c6040c50316280040c1c00c9030015804880004034003902c200784950801140381d0007080c0c620341326941d80c19901c3c003d08000d10140a600111402c0071003040000f107200103076000c1c4c45004000740020218600302034003910005e55002c12046ca44040400d00f80e000d101141d9030013680c90204022603180c101d58044c003420040241c02481070402481c101505201c0003000b00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 29407802 1250 29406552 29406563
    0x7140d09030b090a030203040e07021f020301030213090201050a080a18030509040507020309030a0f020301020d020f090315070e01050304060914060405070504050408040b1c1a0301180c0302011404050d 88
    0x20385265052400020340054410005900101100c4e0042680401100d00b603510300c806000c020340f514070040707141001450b03001c1d030000304014607400c0c0040e8075002941241cac000c64664807000213030710220f411941403681c001d021940070080451a14010500c15501c1050f1400000f1141000032803050a890882001c400291000481d4049403419200d0313540c00c52214802541414081404659038000e00403003d0310502001c0068421982c0c250100c40c19008403140c195141c00c400c5003100d80c0c903044138820030b100b4041c4004400e44507a030b828003103110b03091581d6041d0310002e40c000150392a40c0040d00690700d01c1d8848580c10003148000d07c00714051204480100f00610781420711342c1c00c0c07100c7e40c1c102c00c0c0b2a0781800c00b0302c804104a03a0030344007a6111800701c6a912a01c0303030011010580d40400e4140064185016000107900c070042044020074244d00078040e006080303402c200b1860120030001e01e0b50284020601c0594411b4070001203481410454603c2c1c41c0d00d8000154100c554004101c0c1c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 29409052 1250 29407802 29407817
    0x1104050c041a030405060601180f0b03070215090c0d021305010806041506080c1e0a24021218030f10020306010e0609090f090a060e0c0f06040b0301060507140d 70
    0x510410901c140404992a02c107400c50400350703101511600050034a07410441600f0400d142c60002000741401007101e0156184080e41d94140c400c4a0381080744c413200903000b90700012406c0500c85004034822048003001e401140400800c101074108402020303a006290310361131b06c008460610500d401380002100600f2540340c5450b0282a400300300e54152061424040c0c1040000070014030701da144001224003c00c0003800b0400c4aa080b500346681c6030384000207a0000904034007090310405c0c08215035000d50b43c0300f1903100059940344104071031a07503011360030004881c00450086451440a1004060f54800c03c558942d081c54442c172448030003c8940c0c0001030084540c0c020b280e240540400351006418060003c000886c80071008103402248030341000001e40a80090003000411544500100442c2c0c1c04440c84503510b0a03000581c0f40224688000b25410f40f9000341960110307001905454503603800c080b8111a10340101d07408540003501c02d0381580d600d110034880000380c8406640d0b0340700e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 29410302 1250 29409052 29409059
    0x8090f010626150105010309020d0b0f06040e010e030405040c1103071a1e13030201060b0708040e060402040f090f0209130b04240e06030c03010617060601030204211104050c04 77
    0x10510b210380d40c00794500d54400c2c60343da8091809202264110707002400c002441d5150390001c1600181d40010040c5641d90050400400e282c00c20701c094012182582c00b017002411501c160f90803100140b105445030362050100f0030541c5026040f0040740100d518080b50306081e0035194500c0e5400c9a00c007180c3c10300324200881224128032081e035034440741c070070310b1411100307240001c0071004080500102018000318036000c080c54003d412000c000c0090310504c91351a200b5061180d01a08139025150a809035580030500a180c140265000d0382d50303032482401300b640b0f8441003c0c01841201c20602c01aa000e104204180c2c0d1040280600d1030450900402d03507148803420041100d419002c20031403081c280742400c59a90b484101c2406442110382d04807955190386000914141c64880c180c0c0e0705600301303400400c81c40202062511442e0b1581d00b20741c85503c4690054003640030314000e00072071101285000820700071f408201190340b4013408c500c80020443c24041415107404640941c4038400015040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 29411552 1250 29410302 29410349
    0x30f0703031b0503040303090507050603070309110409050d08041113020403060b010c151a04020c03040501020609070303020a1509050a080301050a0b03130311120409051602010203040302070608090f0106 89
    0x75807a100360441c4182e503040103041c000d419800041d001400301903540c8601c00c1004003c110b01809400d00400e5a034891401d003000801608648400f143c1c3d82c1000900300d480b13414203000f603981081d400700160030700c00309200048628007002801070f92001c210a4003544c6070f8580150600401c0c5480c0400340e5a40e0444c103100081d1464090940e0400401120020100d440c488002c1c4030703901c0c0c01d20040341c1c1303000c040304881690130040c51407a071291000801401d4200c000009104840c020303020782c1c1d0599960390007030740c41d0345035880060056003182400c43e00140d9040c04800004126207800207072a440c5884032441c0002d078a0084900d4080040148900d18000003142c0061014000891862401200b0f0030300401100f64002c00348114084101c40a24080c0b11030b0318247c126081d072a44565840d48600068841500c500806500e840f44202e01c240c0b060013200d21841d01a00241102403900070300b15103010008144800318054190001800242801528024802c2c40f000364404201c10400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 29412802 1250 29411552 29411561
    0x1030b060405181b0d0b0112050106061d011817060403030b060a051e09090a0c08070302070b0403181503060f0807030b0a0b0d060207030c0b06060301140d02040e030f070303 76
    0x20a6a81041486800700d64400240c0e0941c6132400300d40c82c0604619100101c3e0003181d426100400382c0a002001041d075882000a4550443c064402440440da0f9000c0035524642020309806007103c00c800b20312540e500503490072400003101448481420f44e5841040a80d840010711003204c0e130061418802410361500031420208011600302e458011164070142c000d02c6907030001050b45000140f030b032458480e0b0100b92078050744090510000d51a103541c110001b0481114560f0104483c0004600341714424800d40ba20784c2da1021191915072166141503d55072814a00200d11001511340454261001e0006030f101c440c03580c5000c80c0960400240034058003050f00b102c01d19503c036100c00c00200d01c0042640350480b0720340c035002800e4407444000ca500e05035081000780030240000740b00c10400d980007481581042c0129403195131a11088200100c41c402031103100d41440703c14000180c40d01c0c103144030002551000704000f401400ca0008941943c01002d03940c40d601402051034014917405019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 29414052 1250 29412802 29412811
    0xd0c020c040606020a030804110909031c06051503090a0602130807050f060415050f0a081504092d020307030609020907050403080a030c170903042303030703051c0501030b060405 78
    0x2014002281000f00c025582c5010200250404c03044401007014850300390605061084064a1807006140c81c02807107a07698021410140c00c070071b04007503040300034032035110b41d000b1303104000c000d2000344880c0220b50102c0c1d0009005041503004a564200001b8142d1000703202c01f2508010304c90210340b42140700c504000a913407085024805034801c00e01c3c203a496800f100d05517212410107440c000e90489040b10305000320f90400014503000101542601d801500540c89210607071101030380e00701d241d0148819120080d40040401d5a80c0c50040701e96428141c00d03041f410310244074101c40310701903000a0710385095944281c80c00355030b45050400f541840307a2419400a4203040c001c1c5014590b507544401032041400850805560703a00f4030b40700780e03c1a104a000c1c0001541e8480e45420003402c0c0c207481c0da21510a01c0c0e807442148101c0321000c0719070301c2d4100403030100501441c00c0512070b0b14262100c0c2d214007200c1e1405081c1d482400c4d5032442521a0502840c0203404040780c911f804014407084400240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 29415302 1250 29414052 29414059
    0x215150307061e05070f0b1e010501030b180a02311203050a0c030504050424050a050102030403080f1309050411010e0d020d032a050c0d08030406020f0f0d0c020c 71
    0x400340345404100c140800390f482010700d065552a0058200591410007440000305207882031001e0011004130303010461041c418074600444c1daa682d8030019400c4a0300110700300e4001103030307600101100c13408011255114250b140003514080480c0103048503c82a045400d00303a0242e0f0310040a40c4113006e040b603003c1c10004000140440d040e4030040d10b070340120780d0254200022803201008140c46142510020700024100307000c0d240d5242c07524040041c6000020900c0500d0b00c00000d030070300c0c00b00141c1c1e04643c4180c014603d02400d5844800c2d05621604117043c104408029182a00b0008401c5000605880c0c50000f40350170903291800000c1c0c0c00840c25070400041d899281126900d0140c5842c1450703046409881e201407910301615030b4811110311012070070304c2201c41c40e015070440c07010041c2c251160382901c00904450040000980000001030704003e070a0001400085a550050054a2400603400c0c148140c0c90f16051b4180d0003c3c002e4144951140346a00c00c042d01007192443c80c40044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 29416552 1250 29415302 29415317
    0xd020102040e04120e13090b070203040501091a0403050d0c05070e0103020a06050a0e030609070503060a0c14130302030303010b090108060d08090d06022809060201020301080319021515030706 84
    0x204110002c410003800107040300c80c1d90301c00121220b014080c0c1001182d8082c160801001d003565401d0000c00c01902c2c1035641c1008600056160762002c000c075400e4610584404840f50b06000810b2245948101c403030800580400010010407800c10220b00d8040c9181d41b100750700d800900d045d41c1440740c25440005801c90707500c0103000503542c85102c04140c40340c502d0b205440740d0361000119150707007004504c160103005403024440d0714100810302c00250b03031081d81200c2140d100c0c2004d080845410788a840001407218030410503040800004281c06001815009801522500000e0455100fa403120b0050b0200140c4c0524558105000f80d911044c1103420b030807001415113511182e03118005146101e0314100421000304600769041c0c1e401d24502039280c10080a4401c00c2804065004401401040b80300c2c800188492050085a041e6100000614200811b0801e415800c0c100490f040c000d501591080055141c201c1e80c08a00c20000c0e41140c403219000071040c14240003203038105074204503a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 29417802 1250 29416552 29416559
    0x9020f0d080a230904020a02030d060e09011d060114030304170c010807050903060103060b0622030201030b06162303031f050a03110609041b080f0601030c020c010815060f0c0d02010204 81
    0xf400e8a07201c1809850259469100140403805d40c440d038404503410701d00c1c5c0900469040d0016520038450143c03480204024000c6a07401c2103102c81358180301510703030701010040c000140000000e40c41c06001070205c03820700b51506c103203004100404528003a40da00caa4008191507a01c603002541040751400d0442ca4002c40b140801d0f00c1e103005000c003070903064442d0441c1020f81c036941c0031181d800c00c0c0303d8107400c480f42002030651800102d81c44203174006801c00209100030700c1c008084600b44003080001441c12003583e994140000c91a1b040900f00143c0e01a500c113500d141800118410503042c0c1c070752088450a08800c00001e4102c0e0483c5025544d16070013440010208011190300040464000780c44e5147d180001780644503058490460070503d19041c440542c2195006004030000c0030341d1800d540d54400110103e86088002e003005912203040740d10700f035020b00c04181d0400000700f01e5102c000000307000301c0c2c81640001026801c4c10000500341042c1442440905040402c520095150914 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 29419052 1250 29417802 29417867
    0x11b050304031103090402070605090709141503010f1805060a1b11010b061908060303160602091305010611011109030a022e0801031b080d0309020f0d080a 68
    0x10401000d026400340f0000b04403800300141e4003171190042055694402c54540758000d018180c1d408030540c4201c0f00042072481c0c40d800303807240300c550240381d00456948035190000c000b006400207070307015540c4000e50381c400b05090040310051ba041603030b104d14081091034020303d0040d004020010582c40e1101d0261400c07007a1421204258261804036000b207500907885006184141d0041e910520001d0703140115001c08015050110082e15000d280340d40e0241410f45921802e800d42d103030501800d400000203000c0394090801188043c0c0745014040110980394212002a003000b80404c034442c00b4000401824002e03d00c412401d8001c0c1800d0400d0200421740e80c41d09008004d2140b000c0c41c100e01e40550800b4a00d485140114190101040a404010f41514000c0c0020b845200f10320410280100241e005441162000d000170500000c00601c100c00502c1c1014040783e0080c03002c2c7c0d1030b031507584d15030f20410055030242c001213555000182014210b504d0b03010551450045c031b140c41c031640d0390 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 29420302 1250 29419052 29419057
    0x70506071815050409060801050609010b09090103020105030a0b0405010608150d0f02210102040b040f050d2d0819080f040b070302030c04180903030b06130902070c05090c0c011b05 79
    0x40002103007600b40400c0142c10f560602480c0c01207200c0c0c6242000c002503061f01500001c0c01968142c0300327208582d032282401c200c0d41c40303094003960b04036440f08010030065110b50011039002c0090213000031026601c80005050711020f80c4600005607000050008110002d262070030002d0003280c200322020503981d10b0500080701c0f000003a1140c5048a582804c46800e0030101e035208418800031540d450301d44440101640160007203601600d0085008140340c141072117400388454006441180c00f081d00301e11010040d1000401c540d0b0000c2030126140000e8210014181c0c41401000184039000081401420103000428812028881d40103000100d18210a03490b0001018640947d1f42d0382da401040384280310310340c04419002d12088840d61200e421798001080746129a03020300820341d00e4020003006020322015110171551a031002c00c41440c0c1da5000b000c5091003001e1880c0d88a13a5000080c1e00760000300c840803540e02c40068030300d0000078284078005448002100407204c45485100040090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 29421552 1250 29420302 29420309
    0x30c03060e0f03040306050709151b0201090b040906090f0203041214090d0302030a111605040e0c040203040f060509010c0c030f090f08010204030c080105070f0f12050c0705060718 79
    0xa9035003444a8405800b0b0007000140c440308002c032540c1d42d80c5d9240c20340c002d0004651880000b00208008071b1031080303450340c01c0581c20503650381c14074402c10010f410030200b07442d0000302c4c1444407031400054080819000761004000d0640d00040d41881c0c40540300a0320b001a01701c6480902c10001c2000003000c40241d0090b18856250440c0c8094a04842d00410710500358103a6100348048250800c00d940000145451070aa50b01c03051001d48891800369516034840c0c0000d0746540742241480300742070503444a0707016100d0790220381130311085201180072a402524192604c5241310920010f010460240e29000a045402002039041e83c10f07004000d8100c60340000e0801005d2002ca01c00c86105a008002038601100c003008016a906000d40c001d51041c031003240c5502e800180082d4ce0f80c410b204035446080f054a818441d4440c80000f2903503c000d0401840901980c1030115034808851f20a84e4810b24101501c40d0380c0700c44908040d0301c0c00c10000d001c0420010f9103102c03015040b0001075443d084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 29422802 1250 29421552 29421563
    0x307030801031203090c0e041b050f131d0703030f09050f0402030a020c06071d09011d041e030306170102031902091210050708010e0103080403030f09170601030219030c03 75
    0x25070f02000307046000c1c080300d580180034a000140c0104a45010541c81030080c0e101c0c401492051207402056070001003288074003684040742800300f40d05800c00d0005080a010811800111041c1c01c000c0d458840c079182e10000420b51051009000301504010030185001140c01d00030031092030100001e007a2081d05008038020f54020011034107a00c4560155056200c00c5401e5034458549000c0060005203030b4501c12601159113400b00e15181440308216050b0340040480040c0e00301452980f032114000a401101c0c14000c050000903003907241000403243e24030079074011500501c2d0415000c004d460010352b180050340304109110100a040c80324180c1400301c94401758403540d548000440e29244036104001038010820300300384648540c0d102a10480c101c0e212032800383d80b0340940780910142400014400300c410001480424010212460700d00711900e01044801d0310b03210382c14030f40d41c0d0b030303060074aa10740c8104010b20031807521800300400b072105801741c98000b601e0364403209401030003880054034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 29424052 1250 29422802 29422823
    0x6010b090f011704050604022403010306020906070203120406090906060c0320010603060b040c0201140f041106040b03041203020c030a030e01091a0108060601080403050304061a0a1e08030703080103 87
    0x805074002c0030014010f0514100710091494079061464490f101110101e104d00b41400c00c000c0000c0ca48549900103440041c05c180c2540e0031617031040005e5100c258001c1d4411004d00a07440103a07010843c2e5407003001d5041030203895902d0084050000c1a081d000040134600302081404519840251041c1458151030040080c00703068500f084004440c0d010100c0a50030800084180f0140750030131700364103106071b03803c00400044941c12400ca490081d0742440c410144000b00c0c0c516000040c1c00d40d04680180c0341aa90103000f00001061540b065104915441c800f0040206010020754800c00071516400c00754038041c031081010381c40344143d1504000f0701d9a50200c603001d4804c25440041803681c0014040f24142c0440d12000c44288240b00c0c0391545d100f0140095015446000e103203025540c0742c0c545038116226950340c04003a000110309104904c0030071a00004a03034038070042c040141507562101e141018103000383d10000c20241c0000041d0703442041340c0b40010340e100c5002411690070401034031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 29425302 1250 29424052 29424079
    0x309180204050f0f0103110412050705030a03020604080c0c06160303050a0b0109051306170a02031011090d08090d03120e0309030d111f0507320903100e0a030207060206010b09 77
    0x24018160040e1000032030318089030100e600c04c5442c0000381170314090012621840da84104053b50341582c2100200103070000300205000544041c05052680e00100a4031110504940401c416800c08d403075000e0540c0c10007441006154140c03081c00d400c102c0c108014482c1e101d400300040c1211410380310f103d002e0000c0c0c00c0c0b03900810b1441d0380700102030a00ea1500e003902c03150801d40c0654881460720309038401e001703a40001b21004001d100d05070350800c12600d1603081081c900b040044869180100f620310240821044041d907650203c5001d42c148207440759604d01201214500458240c2507403100c284d8070030890003010340d40010f0309100e02503151500c4a103c10140c0500d0342409881d105520551001c41c9040160300d045402c440c2c810b07022603403044a5221160105401118a400d0000d6032040c900f0000c04492818002000041360107011070740e107004410f0704841110b040085841803900300d00f00c2001095410701c03070341005080b184020001c40d4100480103e10348682002c0d130b84994262041403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 29426552 1250 29425302 29425307
    0x10f0f0504030605100303170106020a0204020d110a03060e15060d0b03010902060309060a152103020c060c0102070b070315120c0b0304030f2019110406030309180204050f0f01 77
    0x56010b0b540c440701c02d002c18107014500001c01107180c00110045803040341c4082c01d03400010300da28100c403041d500501c1207040d02c0c0c00b400300a600200d41402c5032510f41003401405401c2e44001d108045c1070740d500250440c82c0c44e61140c0d480001404002c42d00c0c4031100201c03203590b034120070740300414070304640000d41540c2600020700418002e4802500001e01008000c4890804518144100002c00302801005001c4440b0211003105d8010034507004400c0d20500050130100c2001030140380b00c0d0046800490040c0700040040e0003c02425020740c1d000168041008003602425400101c1420306208120802c03c2c0403000b20791038012443c941c80e04840000c2842a42d0b0220401414030807049962404c080c24000d20900081d0b040e00c5c0801d150590201a0341908007040c11900c0350030740904041414030041c040c0504404109a5000c0e03040750f11018550b881d40b2600000b18401c0d01c41c00a628a085010300c00b042905d400c13140098414030081002e5260b03044000c82c00b12080b540343e81d8810812006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 29427802 1250 29426552 29426557
    0x20307080310151e020a0b01030f05100e0a0204200301050d0314030a0c02060702152e083007290720070819050304080109080306040b0609010f0f05 65
    0x1031401034a40700003c42400340c1012001d0503c0803140d404a1103c5100c1109036078900c1c490340c0c0186211921801000480c0c00c4040c016440da2281d4240d0783c8414403c40314200340c03a0710034030b50401c0c1e40111208404604e024840d101901c50101e0401d2090300c203400c18200c05000501c0388078061010418105d003014403640e044c0100811349050241c5a0030080140001040fa0125880141c400d580101755040d0000901d60242c0c00c10180c541e51070347c0d99038142d840c08207911540c0903400c12034080c1c4619420000c040e660103003e1440c010a115030440c0703211426a1142c20600040c06082c50001c48102d0303031075040303601168002d00150701048001c4220652880444c0b401b60a00204030144081d080e070000440d88a00b1012014203862505507044585a80c018171038090207601850b02e01440319042c00b04180c68901070300949007000ea603801f14909461000c00e00b10b5500f1400010004c40e0710b01480b860400d4a8290341c001e041015247c00a0001d0000c0c030500c07010302030010820b03602e8512a208 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 29429052 1250 29427802 29427809
    0x5070803040608010e01120f120201060b0313060506060315040c0c021201061a090a050f01020f0a06020a02010c05180d0c0515070203060604230a090803010602210a020307080310 78
    0x1160340d600da6404000f011000b0a0242582c198280b00000455801c4004911140364104240a848500582d104d815042003490b2850941d5240c0f0720006000c4a440c1c0610b00c44e000d20603520741c0c00922842d043c42240c1c03009200a1180c13509006001000062105200078140251000140d0300000807090310302d03088068000754450100b810b00141510103400c83c00448800c0440d0075078105000142d40d01307900450300c1090b088002c0c00c104002034034040c032021041090600540e0194842d00c0850307820701d04000c10035640703140c00049035111142c1c240309a40c1d2100c50340c5031441c10101905e001c04410175154240c14443d0081d1070b000014041c140e40c899004020040c0403000140314070740e8a10080c0c000840c07c0e442405034400092150801d4001c8100300f500140151010b800250340040345c0c4071002e0114040c0d5507880c0b19030400201c00500940c040c0070300380c0080c114100c0c0220100350080c421806c08040200a10102e40c1c83d54001069440d074580c842d824a880b55076600c03a1400e444500d51 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 29430302 1250 29429052 29429069
    0x12030c0a03020d0c0f0e061606050c04030614240108010b1812010906050a020f03040f0305120f1603060803030606182701080705090a0b010e18070306060e0a030f0507 73
    0x13040c0c9850359800084001c040000c075110f000b00301c8040020424140501895541403014101c0c2403000215550701495100e409030740602d00706500c1c0d44402040311044659112000040c1c030502c081041402c2c4025046031002141901320200300d000204444410f04c903164050380041f8005502c18021841c5100041015040c0b411a440303292219010b4111920141e85003490300000c940140741c0707802103520b0107801c008038a00d99180da0f91482812031124100b5801c119050015800120401611724091691100054498148280e201d141ca0102040b19414141707850420441c1100200c1901e45c0410304031103040c5c8486100d424030022a200d02e09040d80800300803951032441110505200c1d00f644030081c1d407200d607a01c805109580b1022401101d5100071180300084d00145e90780c100d207000840c189020481c9104480208416a04c9900c410340320700c6034101000102c99040c4981c42c02041c10385091040351040750041802d1a62a0002030320605081e80c10100f44041007100800404528 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 29431552 1250 29430302 29430311
    0x10050a180503030a0b01050405030c010810030807050102040f0e04020a060f0c020a08060a05070c030e0d080405060703080a0c0c0c1203030e070803031603020c150a06080304080a02100212030c0a03020d 88
    0x601d0803580700c3d44200d4020796514584180c1800c0d6502c00d20a0302c05984010380140800141003005554101c8014145a250326600c000440014444030191824520410015850b903040c0750004000c0c10003600031b0142111802d04200c050b0355801080c1080303c11600300000c14091001003107400e07070380300c0501a4002d069170070001000000080e10a1141400d000104050348400d24101c1d042240350380d0145c001040207540700c50b90315040b2100c20505200c2c80c082c1e494640c0e07400c04030301c1c7d60308044000c0d40421200f034204546c1821b5070180f10302118403403422080b0600c40e40d4030005148943d00880c0c585030101a042010503000f0307442440046840c07030444400725075034604c5036501c1d032084034444c40801e02c1d000c154000c00e00a000740c40041c0001c2000d0304c0c1407841c103c4440c0402d580117046140325600c0740400600d07035000b0f1000348042c0c5043c030050314a265080c0140300403400101207130b40c11980050800006c0f104004152600000480c040555584c03034244220041d000d04015503c1e2030740380 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 29432802 1250 29431552 29431601
    0x714090a0b030c12070f05030327010504120807120810030f0203190b071e080a0504051e101401050105040302060a030f0c090302030f0708100b06041a040e0f0402010210050a 76
    0x480e01e0841b88144070200e0302c42d8a81c0123254490090520440703140103050a81c0500542458200d1120881890414246580c850820040c6030b947d020554416100003201000e11165544440b040030840c01d03c0103590502032820f82ca004000d202c007810b52403600d0b180d4400c66405004203142c100d03213942c0c03440040941e400c0140d0b040d81c3c1a60048085003100c48480300801920140d00d5401005489460041c1c0c4d40300030050207000000c5c4203c1e001e003d403002d13081c8480340d601c82c0e4004111500c0d000301308203520b040d50103044a40403c5110881d401640042105030384c070000322400d07290706654003916401e044005601804801100344012400d00400b5005d0b15800a00071085034001c60403902c3c00207820802d01d80f02c412074041c0c1c24250b04260540d00310150140c2190340c103d400501898940b07562042c0340d010913900c4144000c00780d100000e007003003840c03642544079130411002c01d9440c965091660010b035a445c610000f41407055181c0002a000034900d501407502c503c514203418440101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 29434052 1250 29432802 29432839
    0x403020402070632010608090a05060702060601020106050a050306060103090f0b0411010f05070201020604021504090e070815011203120f020a030f051b0f03040c0b040605070201020714090a0b030c 86
    0x1c42c00000340c030038030070031400401c04a58850300840002c3c610303840754034590030a0030440d041f4100609007c02441000201d02c006102081590b100f2001540a01418200803000a0a542141d4010340c4110700010091000343d80200d2060307001074090034002441c56261402010040c42400050a9612007000b00824443c64099000410000760384003c0c1002c07009109491601580c44042d0050b40300c2ca000400508011003030061218490380d01c13508090343c0c0c0b0b00c43c106859a41a245009421400f01008580000c000e4428070341550203100e0650b60401012240a03044c1c00c2000c0c2c00c0000344145002c00150650140c821138160310300540d035981d460364000c0d01400102e03504004a9140c000001e04403891b84d40c003001c11840000d00c1900d0401400090042c540000d00140c40d480d000d40c0740015103560140081c0018040ca0b180c1c1c070344a402500000e81080441d40c04140482140c466100b51540d842100390b5000c4c10a10700059aa1070700804a072400b0400c40c2c5041c0c2186403c0140341400e072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 29435302 1250 29434052 29434061
    0x20d0311010c090305060609060303130611060108010905060714040b030a050709050a060203040302060c0f07120c0e0601090303030213180b030f0d050306060703170a0903020f060402061c0204030204020706 90
    0x44140c000c0c0694107910100300e824043c1403101800783e402c00000310b0740302c0c0781040c46c07a500004014122414144a9030710071a00c400a580040d01140c4c070032180b03019140d0b081c0030141c010501ca074000c100c07075062620b80a840b40b90051070141040209401845c08119800c180c40140510308c20880d00ca2a0030b14801008110540c0e482e004203250450000303a40c5440583d0100361040e96002d182040c0c07455080c40615041404012003d0049600207080c200013000003400400c801c1c40c03841c000a299060040c80b405040c0c11246c001c0400d03008014083c5d03080f52046085030707818034005a030383e8882d11101020f0a21a0408012160054030403d00314160782c100340040c41e0110246c1f144040001e81260740d031010040c0c0040444d20a00000d1101d19252002d443c0c418064208070015031b00c410420602d401003228071408203a40d9040204c1499810031040a4212921005004030f00380ba4001803030901030340c0b2410604c206000900b01c040c2c1c1c0300d174069070020356015006645400a52070a08045c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 29436552 1250 29435302 29435327
    0x3010f06081506180a05030f060415020c0c010e01050c1c0e0103020403020f09040c08121b0a1a09030f04141f0c020d030309050d030b0103050924090a020d03 69
    0x42a0201141080400c035041c0802c00c480180568503010003a481d203c04000e00c000b54561041036160000b80c0c2d17440c144442d401c0402e110015090900d45868000e0925a100380b01000d454070520560507240b0000410704140c50b000d0815092414056004980740d101d80354074141c1600442070000c080d05030401643c0c0b100c40e41030301c6198962000100440880c00f070303840080d41c0329001c800c2101482c10b02c1d4810a8100b80540c0400c1c0700c203610f80c01e240e807400300740040030a4a000009000e4025101c54040309800c80c00f0800940418400f5840744202c48015280d100b0050214201060a4400c02c02c11501491642482940c4480c0d860b0384881d210303c104225107005004050a00c000b40911000040301a0565260f01945030303603c0d000d100044081900071002e1640e24580400421410032000e19801c495660200b007200c0e80a000500340c2d00042c07d0348455500440810f6081035202145c2d10f200418400e81d41c4480d82c0c1c0704100c41c5400400d0344080e4114203288000018140c3c800740e41000c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 29437802 1250 29436552 29436557
    0x170a0804020a1703180d05070305030403020f060a02030d0c12060806010503070602030306030d030c020307020901090504020a05040b01021e07050a0611070e240103110d09060501080105040b1f03060203010f06 91
    0x3403640c80a0360040034a400c002d43ea100d8008006a51420300d41e03012120001c1409045008407035002e6403280d107000e0043e00b05840c1c80d880070604000b14a42000384003071440d07044d00c204d420643c000c00007a607603010b80c80e00701c981c00d5241c900000e10103100e030401c0c1040003481d210522106d0b5941d240551606030030b010f128064050b600d008115140008102c902410380a402003205201441c42103005190242c8413004602080095030050394407905803501910450000248030305252041001c42e0b86a039200030700076400c0c01d0034408140e801081041c40520001a201e0f4072071400840b140c01d204158000caa80708034aa0703000700d07840c1d078820114201102c00404035000b0a40350040c12066139800c55903641d481c1c0402491300d9506e40c500c125402c2c40003060602281c01400406048007a4111012500c20103954000320420301c001406414010050040208058100f80d141c0720300d688001001094000700c102c03201c0f888100080c0e101c000542e00000308540b41d5845044034480000c45100b180c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 29439052 1250 29437802 29437819
    0x2150903010b031b01110312010e01060f03062108070f03050c060a060b0f1c0c0f02161206050c0706051009050601050a0c0b0703020705011104051008010e06010804170a080402 77
    0x142c90400003540c0201071000d2551195030b4800d0401120b01072100070410105000a1048040c200d1100704814041c20b0542104c84081d03050100041060784003c0090781090309040040141100d030382d030f8900c003210342810b088900f50818180701d00244103642c0001c20b82001c0b81c140b00c083c1a80440580240310918040d50103581b0382840000554030f06002c0c1001c0d06004011229000b5003071b00003040840c140c2c0d595160b0880b03488011701d003290442200b11011442e4071801405d4240d0500041000c10710042c01041501e04040d400c042c50004174074001c007000c1e9100040790540140c0000e495042d0350011f8140114a0108081d28a105842c8981c00e207050425001c1011507000381305442c0b410215a4031409080480c1c1c6500d070403076070041e00c8079003810b07070030403e480200c2c03c00c0c05610310b04011101d400d0381e40c44c0b86c4028800034812340b1040c48100f020030300050040266400260707401000034030f44002c05403258180044240101c041c1082810000102c0401e000c0d04511001e00c0780307008862181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 29440302 1250 29439052 29439071
    0x90e0a0207060509070803030f0406060e0403020c12120d0c0905030303040311070e06031b150a0309050601080319081b0c010c081f171204080303010906080102040b0711010c0215090301 81
    0x6a031034105e802100c2c815041803002600b155800d05402d81c1c41801b5000100b0501d49d00d07507110410740c0043d5003d0303005030030800d040025820000449004c09880c00001d10b220081000000382c1c1d40a80e50042d490030f601c4100301d003001e6108a80003005007000505480e41d0703090514014007030400701f203440812800350910001304d0702203502d507140c070801016000d8007054818103251001c07003c2c4040c0181d40729021051100100e00d04402410354610903803070001c2c1c3c4060906005107480c0c0140d100e44100c1c0c1c41001440c01c14204840300703d03500740301410643d00544542c080b9051901590180741410100030403007100b1550705400411032000c1d1611070821541381c0003070100300c0c4410010b0303040c8007003a03000041190011a0004440c403140c000103480300205100e145214651156020a00d154008001803020003d107200300c034010504030008500d060303e414084121401080c01c043c0014034004a00c00380b41e4002c0b0391421000b9801041043d90022091540c4115009005e10794001e41c03903d81c041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 29441552 1250 29440302 29440321
    0xb0a030608060411090603010e01110a110d020a1502040e0a0f0e010507140703020703080f030915010302030d030b04020c0f0d0306060503041509020112060e0f0a1a010f090e0a02070605 81
    0x160140313810103500d06400e1820702c00e01428810143c620764041d9618404400412000c1c40b03814100741a04045959420509e1801001400c0c21800081141c100c180e01c00f140c00d03000100000110340c00188820605000003907200240107640c0481d0ba030443e0081002078001d1203901a051030044104c0c00c2201c400c0b500010340c00c944003103403014081107940740c402d2508034410b40a0710b5254424130440340700503180d980b150625008005511407004000c014002148028400c0300400b00d110b0340a03118540c03450300066513400d884203004044c0b550700c1d1103144160319684c04540c500c20201007107440d8072800c2c0070642d50390110489580002817400c0004225248100c0449000c1c5401c10101400d11207180c40072001000311460403414842c2d0341d903e1100003491070107854001e1089083d640c0aa2408061021481c10001c0c8010100b5251480207022420100401c211b41d44080ca00495100c000c40415604c0144ca90041109400003034100418940107070000c2019612507101403180c3e85848100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 29442802 1250 29441552 29441563
    0x31603020a060e1605010e030115180b01110d18030b0f070809030a020a02130603021c12050a08070f02100e0606100306050a060309030306180b09060a05010f080901060801060b0a030608 81
    0x707600c0c040c1300008000a42c400c0301d514a041e80c0060000441d40b030001c654181c4403c40d5402412030f2690f0200245400000d0300c13410604c4c01082c00d08006010100010036107407c8400c030f052007402300e5202c400c07207080d084400310006154000710981316403d02c4244960f003240d08440c520005a940d070005617008030044199210420190000c00c009622a801c10107003003034601c8130914003034ad65140080940e4074007000364071420760040321444ca404d903410b088014410400501c0c060080c00c0281d1400c141e4440c1c0150317440442890000c3d03442400410417410310680314415580242440c210032400d940100300140603030012a0303000320906e000e41042d81500c40500c203055110364810801c21040340070360442d4580d0b0703200345400218540c9804003104d02104803180c0700c103210f55034002c02459041115903039800c40000c46040e00040d141000090070703510000415010000d184001c145405800d40151000d081400000c1c0040344e1110700c1844690042120342001078107216000560342004200c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 29444052 1250 29442802 29442823
    0x60c111002151b070f1103031318150e04050a060c020706090f060537120507080c030c0a0201090b0103030e0a0902040807060e0609040507020d09050a0e06010c05031603020a060e 78
    0xf82504264103615400c02081c0341110540c0c04422500110046a81c10300080c182014828100c84440e8201115060b05180d803409400140740341c00c401503210b41c1030020b20412030b41c02c02c0360725801d03669902d00942410f103107030001002c550a1240510788140c0101d214020388005a980b42c0110f6a42c1524030032941581c0b0880010801c10070107611803400c51001d48640d80380c240034840c8030706611207451003000885101c10b070001d001d0080548480f08540100c9410140c2498042e640381440f8650450520001e0042d18407050002078160085000303420262a01d41c100052004540e5a4100940005444801d0074490807120300b010407606c01a10036102a1080031004010440c00c00700c050360258803910140d948002d050040c0b24003640c60703000300b40c0f003141c80e60b020380925060707402d0213010690190081d0f80b040c80c011070188000c3e103145456075880070007442c1100d03041e509400c10a0451280d03517001a481c03800c0b0070203103050540008441c801144110307001c000c05a940310700c6030303100e084100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 29445302 1250 29444052 29444101
    0x320010302070f0201030203060d0c0303050a09090902012a021f11060403020a06090c0b0d0608010614011b060207050304060c15050603060415020c100f0f020c0304060c11100215 78
    0x360f4100c0507511a44c091540860060180c442030040c40e00c480940070103503031084002800c0012454520b03540030b1402c20040554041c140400b10107607001030044040c0000b00d051903e190407201404903e00e001c6140e00903005051070001280c0d0000d040080c40c141511080032038682c44000e9030710903001910600c5260075901411150b080caa41d440003500c00050309494080b548000401d10039004802005251038581b00000c145e840c1c200440d0035601d0561148004140f4000340c00c2c59640c00041c40a080e104024107103850050914000000340980940908544008100420003a800101c1c44a5031070007029041c001043e00a02d0000b80e0348102c8101d60036800c1403003c100091040784403165100000c0e42e0150030400c1c11075040349000106a0390700030803601c0c0c040d8034100a5080c4291100300f40c0070202546811100c0382181e0382c902c2148584010007948010081c2804151030700d100e5001c90060401502108801e0300a5a40200c144010704450161011075004080062280600141c44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 29446552 1250 29445302 29445323
    0x6060507020112050a090b07020d0315062003070c0803031f0b0901031a04051005010e03010203070219050a06021801081f0605131706040b0108010e070b07030513032001030207 77
    0xa0b070703c00140401800d980d000359215101d060006060660b1203106d00d034194000d1040b90b44908005040d14080d40c1004d42d0040c1d01d0b142809800e0f44541001c01c01008410006881c4505551241c42d5110b0f0b0701d0090410f452a0101050811f8040700444c010080448120080b4907070750043c0c45440d0051141007114031040010320119402504a00b2210103148207841c00c0e1024540810309945080300c5203004100003110030300080d82c104507120900728061f8000c50451510500107941c8150741c1d0304c0ba0100b800810754140400030b082210305c441d550700031070640d103804440441401c5180e0001525010400200005805010306a118014000d400c45100784581c900001036450b640905903000f100220003401080d070042c82000454030342c0d0410010241c6140a052005002c0c0042c2c200f00343c1d40e4180130982085a000083c554155821420360903590841d500d82550184101d0122140350f005600c40042800304180c4428017940302980f89040e203080310801142240305003030300184618500e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 29447802 1250 29446552 29446577
    0x910150503010501020a1e0606171504020307030209090f030a02030306010f11060403030f021308030403060e06010807031203090b070f020f0a080304060b1804080a0207060305010b270a03050709060605070201 91
    0x840140aa040c10f08040401d201885621448160f60b0b40341c005919007050058080d91480c001c0200cbd00d25007542e58400341d507a042c0766000a4a0744041d110107446614900046080100140043c92aa8041c0b03010ac0356503c0d400100651260801c550017400301b02c940c10304916483c05040300d060140034800c0134007404d0303503542c1e0141c0080101920303140c22030340d0a03c00e091590546002c10070207400084000c5031601e145242c0813007500c0d201c0702d804001b50011001040101740000e880800d0301d070300002e80c03803a01603102803c400070316102070082c01c1c954009c41400345e6031740c000c1200d0065880741da081ea45d9010758010010790350303401c2c0c900c000c101c0b400030000a000301e405d50780000305410f03004104020132503c2280000d05201e056400791030078000050344440403501001010002c042c10306090000e036240c403062114a0244d03100104290303840e1010b1001000c058580c07030201c1030000301000825626410450355a40d00340c0611061245403041c0880e00354065002da50f03105a05940b040102e503035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 29449052 1250 29447802 29447813
    0x50a060e060d0c020304050a090204090b060702060315040b0a15090e092d010c0f080a140a090f0c0807081b06030601050a02030904090b040501051005060d020901020c0910150503010501020a 83
    0xf07030740312103400c40c0414030000c00c6681d102c0c480c0a0080c100444056200c41c181440c80d000c8a054250440c410031041019a0058984501f42c03940b003a0701e907500020081490021601424204600c2584601c920b003000c00d03a03441043d801c0b0f202c03007085d560358008079450302c4030309c40c000c102907410941c0c0d5400300042104890101c510098404100c040960f480c0060700b80450070341e08490204800700d407584511060315a4031076071065010700000310511440407100291500514007601ca18003103500c0b01c2984062049900001b40c0441e0710108080c00360781d9034058607465000301d00910003075011340d041d03111034240c6994072096034450084c40280b440d02c0303403801594140d01c00411340301580800e00c170f00e6919030703150701c138450519000d40c00c1d4a00a242503d015802c55070003c283c40d1501282d1a818400c07510340307106803000d421030001c0041c2d035410003c0061b440c109540050540c410000130810000c1c1029004480072188600e40c56104e0a0354000e0503149800b00b4005c6a005911010032440403030f1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 29450302 1250 29449052 29449061
    0xd080907090e1204030507061d0904080306061c02041a1201170703140a03030606031509021c050115020606090c03042004020c0c0f010318020603060402040b13050a060e060d 76
    0x300b00500700d07000805480307003c4180f40c1060748241d40b103801c240010800107800c5080300c0e06100d44d601d400e41c208070084000a12590300500060104d240100c00070705240c0b28041107411021652700902c031094080c5101401070350290280790013014090b0f154500e8100d030401580d2807011a12100c43c1103a0914860340008104280c00c4141480707160f0000002c1841c01640c125884042c0c1e000c0d095040007402d0140940d91994880b9040526104000342d060444400100030780345c60710303000740c3e540750b00c040340c60600e50216451035821480d0000000304100c1d40040901c250410b1b0b002c3e10701e581e0f6071004103c0001d804031000c0c0c0c2c04100030000280041d42ca680b51100c00b800c819000d1400044940124040341c11560551210742d00c02c1d01a4601303840d0400d2100f0b42c8100904e01800150400e121101c0080e1a0500080c0501750110100f00540c2e50764058501608016010075141e0504101e440c0c500c11aa1188030b0151307016540221b404e0f44a20f000281140025080c01d00d0006100c50203c000d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 29451552 1250 29450302 29450321
    0x10306141216030623010311010c05010b03030406050d11130611010204090e150130021c030c06050c041d06040e16030605060306060d02090712060e01080d08090709 72
    0x14040c869500c812a541e004104001d1030040c034001501070300c0705d1005220084500342801c1070b0240740340100700040c441000c0986100302031800708454101403602c140941411103601d50f05000100d000710300240c0c080d002c0d0107121681700c0c0510400d18410f055131105c2c0300d040d01c0b281d4000900807091002c035001d100d03070f008a1030503940010300d8a5515103025044880c283d0b8446002c1e08103005410203034034400051805412940c000c004401d0b501c81d88140e80d0300790302103410700c040070443c400c1d030035940c0344240c00002c60f10282c0c00d03254050951800a210113040c0c0d5044405034580408901a00c440c1c00903501a5a03100c2e040e2445150390240e894504440100386030380c46a103a655108040000303101100020040030101a0303054103619044050304d00090000d400703a07100208008450340c07918040000140c055070358404980340c50b00c040300c1040b0442130700c6955500340b4000280c0902031100c03241c103c0c3c1c05081560981034400c031040b0f0b0b03c80b4040e611800d40350f0001d0720a100190003030b8420b10b00d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 29452802 1250 29451552 29451589
    0x8030a051b0601030f03020c030d020712020103060e010605040824010902070f050703060e0d03090203030a0f02070e150a0b03040b0c0901031d160509010602070e0c0702060c0a05010b01030614 84
    0x103101c4128262420000340c2045074900800ca4520007010340401c030301b00c003000d001c030050501c02c40508002903450030746d0b04c80e94079159034000c028801c4d64041e0b0700103c041d10341000c0c2d5244541e101e00000e4515801881103410500c10450041005002c07030480e800b1230070010103410ba241e46041c3c10203001e03401010050b500c00c80781045100028108200080003140f0840004c10a1101000d0303541c2425001c4443d0010301d401c1c020320ba401070b0340201c103d94203100d09060020081400d00c00491400300d6903003041041d5500f000c1030084007030b03a94070251001001155028581a11030b0b4500100780000d4130000c082090700030216150707122110191030303000418903000403100c05d805808032410301003000d8541076400c024015003000d01540c510070054801030311503180c42c2d49407030402942d03447c60784181040300c2d0100000c40c642100480071512100d030000c111580354800e064000b5190f0601103400c694541c0307482200301e0f542d4003c0c01902d0840300d0202118a42103600418400c0e00c3d9075000d0106070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 29454052 1250 29452802 29452837
    0x1050405030a030804020a0b041206050a200c0105072c0103150f0905010803030705070807030e0a06120f0515060304050c0405010b07140613111305070201020a02010609020408030a05 80
    0x3a41c1d2400c10815000078000e540b0b607a50b500341401401600401c940184400c07070020801402881e2184603143c908a60000000545980382000741c0c00078039907a4010b100700c102c10440011001c0c10800a0103048000400070415921810380c191f5403100b44035221803074481403843c0b00c40d0549044800030030307040b010704001c00c101a030440724013a140c259800001e40600c00d100148100a2140704a50150018074001d62550500e410080d100d40680381c00140380c52070001e451401c01d885490414040308002d482203020940312200074007001c510b000001b0120346030141c21810540c1070b00603030b40185003000c2d4440100204006001c0300e503100030003d403190b10400489404603152072083c1402000c1010b0b680e521600c903450041d6180071400b4508001d90321a42c2404900703203154400086007540328001c4408880e90802056a0882c00084d1820321803510f030400400c507030190000c0500b180b86500801c00c4c5521500540304a0069000f100550351050080d03004d4180a400140302401c2401024007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 29455302 1250 29454052 29454059
    0x6050f1309050616170609040209040c030203030d020a110c010e13020f0a0c0309060203030c030609041a07030203180304121202030c030a0903030f050306100f1119030206010e04051b010504 83
    0x20300d40072044d1558125001c4030020110480d074002c11680a0302c2c00080688124100040020300020300a08040c0c8107090b5440403a0800c65103901c403800035503029003030382d0b01c8003000807102000790894054400440d005001940388410082212140407505840c0c01c180b0041c00c41c1070100803990642e03022856079003001695001ca0f003a03001b801d18584640d5070184422030603e0014201d507225405101958402c0c018814401e5412094031f80c400c01c207071107950059135903061104200c25207040324203461100c0310034170111641c99002144034949007100850070b4001c801805540e03101d41e100d855680c00d4503500d924005485050541440c9420744103d90a203080204600c0c01c560003548990b0115811007410410150000411900325206051007400c5141c9040403502d440880280901000500301c3e404444c64050b9000c080c51314014000c40340e4030301c21a101c1d9030000002140a40152140b0400050403408206420744035680c0038028200800c1900291003003012089410f6050200a12010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 29456552 1250 29455302 29455313
    0x260a0b0c1b030403020312040803040315060e0a051012030503180a0b010801050f010501050405060d0915060902091e1c0c03080a0203090109080d0e0d080702120307060f06050f1309 79
    0x1907a00341c0560020b196924035502c1058a0511082d10035034403840280400c2205402c00f10541d001c0383e801003080d0071070b08804000d01c0024040340d040348161b44070324010f003c1000c1c400d50043e845030704144043c900590311340103403400c490f114002c020002030701000024040f0308803003000c180011241044460110031907075415001d007002d0704a200281c2d5038004000450521140d03080c0105420708001d890181400c02140d039910584080c4124103071500d0f03603481000302146d001040502059020481c0702d40f211141c0001c2d6011040d84e078883c0d07a4a18007031218005405014141c0704004200c00000c02002103584e4405548030425034201c80460000804503208a004190040c013a50185603141c520400140400d031183c2c01407500341d40400242c007031298101020380ca961800710780070078000b6420310b00f13003902e803207075410080d0404003510030f200d0126800030190003014810b000c244540350748120704800f240c000c1c1c801d040c2e000d032058107500818140404101001d03c0405808144181991181c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 29457802 1250 29456552 29456587
    0x4060c1703130b0106030917070302070e1905010504060f030210050d0c0302030609070903020907050d0b04090305040602060a050f07030509030d15140301050103150c05130e01260a0b0c 81
    0x2c80c0403900d410007200c0e04001080e900d25014000905081100300c5050b1191000d030000004500e40600e4002211303024940200500c40c01010341811503950b07460a40c841d4082203038403243c9041c415003000000314440c0b403d4058102074035403500f2416440340c5117808110040d945604070105002d020040c44c0c1c0882c01900a25843c03c4c00c80c4c40144c2e8a003441018040ca100d00100002d08200c1e60703020500041e60b0303103c1074a800101503c0c1040d120568400d0480040520049e01e981c00f0b841c00d1214010940c000002c0d104446154082d21070355922040c05a0036035108590651944501900103800e240c080c0d0b000980240a02c01101e00f448a1404008201d40d030803c0008001180c1c214104103050408101da0300d20f100c240c0c001d0107d9451a9220965887c0a49100d00101e40300c1e0403942900d4407450550300c004030b0703a400620074665240b4100d000d085080c080c8244800c07020b030b0f01e05814a40ea00804940030740c0807000303001c280742035103650040110140c210200d00004000400d8490006800e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 29459052 1250 29457802 29457811
    0xe0c1606060f18051e070e0a080f0111040803090607060609020304060f06050d0c090b010521091606020a030804020a05031023040c06050f1b0c010e0102010b030304060c1703 76
    0xc00380d8641800415031010b4101c3c00100f680d2400d240410100aa885100c1000205011186070050722190300a0352042c004040d40c42e00b29034910380014042c5c1000a4095034004c960380200046454070350301d0b010f00d110f180994242a4000c0050ba42c45052400040c08214090301e0300103900e549460080082e81c0c826601a140035445040c0307034540040a11480000300030072a1480d0300007900307903a0201368090300e10400490540c0c07070940c550719901a8007144e180e246028521041d190404408060910f025942da1301644181d0507019880d03e000724250082c0d480680050001802595088079510001071080340c004020540001d85034904001034000c04101e003002055182410680201081403003130910900354400c81400045400d4540a00a8406509e0700071ba882030002040380356813082c3c0b907031207002c6900c0040f6080c1c81c801c003154a541800c401d907212440d603500d2000487c240c428101816506400c10042044264050500130305100c2c441e111900650360315100100d8250401c0382c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 29460302 1250 29459052 29459069
    0x518040e010e0d020304051513150c060606020309060d18050106060906021006030b0103030c050a08070609120822150501031115040608070c0f02031b030f070e0c160606 74
    0x203568041c040042c480f500808165200440c03c003403809002a071111140e50198000500014150f0500440165210042d2070011100c066840c140c1e40002d006080a08040c0d035441d1400c078020a54a00c0070003100c65441004103418145011011031100801a80e40e610701c101c0c119090a00001d842030140704000c18060321030325451840c0c98000380c10a85000708401c4841d1800d001800002d5a103944103064a8240c0741c0f0412188182c5092403034031420840141010002182c50020412190041840a072094040070a18444070030b059800141c10389205a0038072070744141c0c540180c0b0500720320307145a001c0d16642c64181440c41c0700c0300451700d0030f03001901d0031400ea024a40180c20300d40c2030107003103416840d450341c03425103050801000820701038404c1080000d210990350900000c0005000200d0f002802e95840c02d0b440c40c182110b58103a100764902034060141482c514910208950317089503089111003120395030780540090207034454458080210501c004490104085105100c081c03c1c011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 29461552 1250 29460302 29460311
    0x60c02011d0f0d020c030a080a020304170607030605041401151205250216060f090b0a0921021c0201020f06010602010b010201110304020f1e0409050102030f01080601150518040e01 79
    0xc2d03030541c28040105250390030340d03004410690f43c4d0b8a0000381d003001e407500101010f4a98400150803400c45c8207a80c0b1201404181403502c550f5580c2c003107205070040009480400c40f00d0384d10380030301090310b5000171140e442039141d40c010028050525455a491540752400c00d1054520560100481c0c5007590b0600c500030031404210f0240110700555554101035000601800752000d003e076899003802d02070401000783c25200c19015600a4030b00d00003070440d9100c401d48078003402c00005c01d80807840c410181e080b41045900c90200344810301220840750042d0181c6400d01d9072580380c042030b8804401c103d0451107048140082f40c6030912060780070b40310a6001140c00811040020b0a484111011222a45003042400010390740c20092030f0b08c052065801c0041d001244400c0e01c80306408124950300241020a41c0040003810741c0218803600098040380d10598a030216075035156802d00664101c041d00020000095005030040c1942550510040310040d034540042019900320510803401c6a448 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 29462802 1250 29461552 29461573
    0x6090c0201050f0105031515040204030c0303020c100905030d030e0c030102070b0702060703050705030a18021201060603050c03040807080f210a0e16060e010c0203030a050319050f04060c02011d 85
    0x8560320f450041c40124020460160000705040900b800035000398600703111151110126151034041d02d006507080300140000e150343e802c0c0a5103a0000448080c880c404140402c805c26001c0d0f08080300b0384601500030103100d00c120506400802d003001d091011403080d081c480c84140e800740028292070388201118240c034100040068508000604103105050900040004465100c81a254005507405000c100084032000d400b500460212004e904200b080303280c02d03040041504130104031299903400b00000c2e0f40b20540c11585002c00e6500520340502042800046101d80b0b001d01048921500c03141d01d02003003c01c40c003044090380c03801c040c01705007444200420b07070b0744900c039030b0f6044010f440c0501001c4600b00c0c503c0c080c1ea000c6003e01c00c1031004170458036034a81d00c54142d807202c3d16405000c80e0703640c04441c08080c1280d0801c03183e20005010100040c3c0c03055000d03010343c0780202c03030800c5210403035110b541e21100030300404400042107640c0c2d41c28220307007a10705c1071009044010f4a805000410f00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 29464052 1250 29462802 29462821
    0x10c02060109050705030f070c12020106051203090a03030804080f0c0c010f0201020703020703021c0605150a080a030c02010c080f12040203070f0506030103020907090803040b0a0f0309030507140106090c020105 92
    0x591001c403000d8a00380c108070644e9002401c881c0d00410f03c0b03190707518565030702c60702341c0b13843c0c41c11203010300342c8240000540140354055002105486046602da42e4100c000da150a54034072910301d000b038004006180c2040040e0180040b240c11611400302c0504094001ca804140ca4004d0340e202480b0303038003005105040396041300307560180c04c105100030b40c0340940c180c40180d03548083e4800240100040441d01c08440780741892555050352200d0b0a02242c102026101c862402550400384220302900c0000f4a501000902050031a8107844150b4030f20016001902d00162003401500c44541c10809888990740d0007009254190b440401d004c050f05090060624001c85500319110202d40800c00348a0740d615041075a045a0381100c48038402c2d41c9982048440310520350209a06100100e004100490060098081c4691540d21549000324051084060342c01c1c0450250115000b045100007113800c2c94040141d4022110020400300c0c0d482a68604880198407450b005035507400c24000c4030702 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 29465302 1250 29464052 29464063
    0x90212011a040603020d02120f03070f02030d050c1902030c0916120509030403020f12060408070506330103140a0212133c140f0d23090a08010c02 64
    0x150700781d400304800c83c10359020441844000e00e0191203002e4441542515440810100000e0000b4030150b989406c4949491140070301c408908074800d001e4a28840803481c41141605d211041f5000200141041c0d00d20401c0114450380003640c040c0113204141e4220340700e40e40c03d5401000d00404004100b17201e8000200f010100303407695848903080c40240f10081c040001500d05982d012680c1005074003050300060b15459619400a006029060411090182c1c07500584851400755040d40c01170303582c0d00c5c03604905900c00c3c0c0c0d0300d12282c07402944100000415401c010709241042c10000b4080158030601114400121840c4070300c150001400c445001c00040c02c503420070028074940700301d401150382c2c111045400c40d08620781880e002c2450340068031010307105d1800d9480007a0600c8a850b550170941c10024400c00300d000c651080641c3c190248400042880c10684590b0b40e03071013140380c05180350740201601c002e000420b000601482609a803030b500f10301c1c0141414400042d4554407184081c1c1800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 29466552 1250 29465302 29465351
    0x501141002071505090f03060a0e10060e040b0402130f0501080c0603160c0c170307110f1f02010605060310030218040b01120309090c0206040b1003030207090b010309021201 76
    0x54100d0070080011246080c0c4500203c00b040c10324030303100c0c1541c1002c41d202c10001e14000381d1510903c2c06100104e549980301071140d2070484207844c41408545e0602065442d503104141490f10304000280c08038060004d0799402c14801402c55404180221030001542c40e010860300703000780e80e0001004918000c00c03100740f0100d0203440702ca00314a0f202c980d080b01c0c00c240480000c00d11505000b02010031120f00f182501400301d110081408480b18600c00da0b0b29084903404940a850381d103a2061103240c0301603503031030141c0c2c01050441107102040100380c6a80400502ea0107564917004042481c0e80c400300550f00c200c116042c910a40d038514010040e0a64454000e28a4000848140b1020070034062440d41520f50b248407400c1038006030314040750041c580d68441d401d150f20f0914070f000b13050b6005c45ea181c081c40c0100d404c1c590f140c0760240903400390120340c440140582e10490003000381c004079801003c0002414100015a41042d402141a2408990750015a41d54074514070045a5000c0201d0104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 29467802 1250 29466552 29466557
    0x5010206090d050904020c030403080403030201060e010f14040b0613030b1f0605030c18180907050103020f0901080a110406080906010807060c110307030804090209030c100507030807021005011410 86
    0x111803074402c09045481400c1381d03240280c0d0001444281e988041045030021070340400d000d541d440d52420024001c203040d008100140301410300026038a10000d06440c1582d100403134120025249408000003444076150302e51f040402800700700d810b00b00d86040d55008502814162400f46455585ea084203e6002c102c407200e503908000c1480165841400d03207601c40c1c0000d03103060384c950258a005500c407601c074021691215503603400a0040c0c540a01e4030307008032541c404503041c0640700d60040d01079000713031600311800d84814071184040d5840350080b9600100301070400900d00015903181803143d8042e40022001c00c41880034818406002c00c01c2a00401c43e00307018040c1e0a0801800401c00107000c84003401004400310100c195a6050000740005c5902000d075940d610398880e03401000c1d4000720034481c460300980c449540281000243c0c0030403c0856540c051030420070f13550903114604080c101200718841c003544041340030141e228047c041c0000c2c0309410b8085600000f0840d040301a000e04504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 29469052 1250 29467802 29467813
    0x5071d10080601031b03080d090201110c0603070507020a09060329060607030507080c0601170d020105040b0c070c030506040c03060516120506060c07031104060b120109050c070b0a060501020609 85
    0x1e40601040c0c003810b49501440b51944004065500701d400041030704007901d941e20001d05615803125581c001e844030b17803007078941001c1c4800403074080ba250002da03c0f035160008410000111014860300003443d00c988018811500307035441d400c008007241c840303401c1100d400700e00b980301103d0401d140102030002d03140001440d04628210020800034054143c00400303004003c618802003003c60801c0d640c8a0310403070f080f5507096940c1c60452410180441088a4501074480b69005552040c041c8034401c1c0e402c5002c810064a03036820b0881d1039070007000f051f03884188400001c00000d6080c070a2030b000700c6c01041601034003811401c1480484001030510ba902e240140f03543c115280d0045590081040303007110005042e03407041d011a2261141202c0350f40180103e660102c2084403110850301e8000081d0703400c011072622201c452071144240349100403000c00300001044505041e81200781d0004d01c0404050400f0300b08c1e9070301e2100b19010f03980c40603256101e92080c0290359040003510b91150b550002004e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 29470302 1250 29469052 29469059
    0x9010605040b1c03030903110d080708070203090109050d02030a020d030c02030705011d090711030706050411041e0c180305060a051501170603030c07080d0801060504140d0c0305071d10 81
    0x990402403c2c0024241a12024210241402200da030200d00c0140c1058494800704001e0040041d582129400082491603012404442c4000107031072034000c1c10703101c100c00c1c0f80c1442c0402c4072809801c0b804aa1500c074852041005031140b00314515281d1085e110b5805146403071041500f404d04c16000a8104401201100813041d40520805405001601c155515445015023290048001110b010709840001244000c0214030307132015104034040d00c0000c030043e84040410041e03030520401036103681c024000100c510b4084e50b00500c0403030fa141c14240300e60820701560029205040e80261002c0d0803403010084548294081e07140d000010100b400156031034680080c0041c008a403200711b209004030001603041d01c08004aa2440c1c50000481e002d980e640d41e0000d685000060305000054500300c00090900e00882c240c8041d01d1880c0c164908407046e00f014445132241000050310641d104550000125606014620280010b003045149464400500b200310110281c0562042c42c440d16040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 29471552 1250 29470302 29470339
    0x80c0306150409061506020a1104060b1c1503060915060e0c0f0c01050c0406020d080405060a02091c0302010608071208121305060907050f010305070e1c050609010605040b 75
    0x1c1104a1044a0000d891a21030400e50000c041c0b8a003c5601280f14810110318160002001307942d01d40318a513070380020000207007132005903030461003130b1040c111061044804a910b940300900c0d903240e40d40c030002442d4148800d50325940a45e80d00036281150340f00e41c0e10b0140090101640740d40000d43d103060103000d1900601c0c00c5001002084e001031024089490001400d01c401252107251a080003480641040c440344070003503100c1e06c5413a001d4464100007910301401207503803621841c0c000c0e010700000c2c0c1d6000584000303940007251203a8040e415624444501607a01305440d00303180680d0002807101e0406401d5458542036401c13401c407501301454a6000101d1600407900c00d002c0b0b44035554420b4030380302001000f07600340309002001401110104540384000050007001c5030004c035100c0e04159541d40043d81161810760b00c110004010341d01050b038900f444290301e05580d40710395a5511480d50f0351202403c0400584400c0b1060351540350030061842c150140a10541048a810030b4290209032070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 29472802 1250 29471552 29471581
    0x213050f04150609051f0806040803060f0d080d060303020f0c0604050409060b0a080c01020105060f09070806010504051206150301140a05071809090308090304140f03030c01020c07080c0306 83
    0x920103211014000180c806941002c0010440c1303150601c40c07414241000b80c501c03c15004070241c10303071049174001541d100006003980070715000800070340740d40c5800080c4042c41e03e1444145400104a61030400000c0e0080024111540044000195603080d4a40242030044040c1ca80c00c00744d100c0d051084840d40c83c0021101124421900018084690300d05100946180105d00764030088400780002c404602241c00510f860003603008020070f035108c10130000061903560b403041c1c014502000050a40380207400b4503802c00300c14180b41d800c1c940e80302c8c001400e0101c8081c0c00e4465030008804d0002d0b010600c20000b590304421002441f42c99400401c56418500051052400355141d101080089001d0007424421020480b540301c11684c6880c00880508082d00b42100002d0003200000c82840010040d9410b441c00c401c54075162184520030002c028a6141d07546a00d40002c021000d030019007403008003007e4501201401036a0314124030070f8101190200c0d00750290300300b41d0820041450340b030032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 29474052 1250 29472802 29472811
    0xf1b0406030e0708070f0815130210020106180b041404020108041b08031b0c01090e0105060a0e060c0601210c090f020c0a08041403030405060703030207030c06090f0213050f 76
    0x40000704100840720143c68014a644018994010300f10041400080e12a03507800746c50740c050485021500341030300c044441d102111000100540d5907200e100500e007001d01e40c0b50701401d620012402c151607400c00003566107030401000050340c0c0c0d2182c07805507007414062159074440d444a122283d03c0e00b900060001a00100300170001c0180800c88105803e032007a49401420354a82102d848101c0d0040885401840c0e00c00030a45101c1c2e15a11a82580f040c03880c2d0080d20621070300980c984c0d103003105212041c1c01002c0e020b410300002d0006580982c95800140c9510456100148541e5140c050b0100c0071041050416500040300900080402c078054068001c581840c02d00103007644880020034001c0c000c1800500e040e004480b0ba203c1030051400180060b0340d0503e0740d0510035151103081581e2846944611a007000e0306100d4100402d000742d02400805001c0d040414144a0390b07960300c0c08580b03075003d00b00c40e03000ca40380344181942880e1180700a040c405120800c0700d410710041e852039401c001031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 29475302 1250 29474052 29474057
    0x30a0201081b0403080a0306050d0c0902030a020d0e0309010e030d08130804050d0b0a0b040903020a0b060109030506010303050c01051501020a1b270f060302090c0309240f1b0406 78
    0xc010a440d841c0350140b241201c2e50150348603440c0c64603490000484d42c0002d070304400290070303c0004500792803c07404090303d450784503451010303840c0f8140002c4082e4000800120b0091b07400d0000b52000c071414018010b0f00d00c41c10b0301956039001558005041c80d41e6040d007150080c1d100a002c84400e03500b000240350048030500501d511004586016441803285401c855007004c40d50000b4001c104c80850307c607004030200c000074401c0d254440144000c8814804000e4016804a40d00d040401c0041039040d400c600189420f111440c0c80740c40303452414500380e2080f00000e600188035001c2510a03c15182c100c159001083d200c9011600002c0d41c41030984400340254a445511242c6840a5a850f40040180d8140340c50030241c554000841201116100c0407080d0030103030b030b036401d603c15480f035041500d038010299000c0743c4882c0c450038150380006121040c0c511074003d9400c0c40080901906504038591300c0c0c007100d94601800e80081d130180103811103040c1c0207102002d0050080321010b0740c09813038161 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 29476552 1250 29475302 29475317
    0x80a050402040609020c06040c080d050a03020c0307081207090501030213060807020a0204050a0c08101d0a060b1303030e031c0507020301060e130209010803090f01030b011101060b040512070302030a0201 89
    0x7800001c00424150740b10019041c40015404000007002c11464803583c051512040d20035070301d00c0d1058403400d0342407a9400040e42003203000c1ea8180640e0180c0150302c80703c001c403814030100c0d944540055200481903d4000c009000b04034070140c8c05010680a40028a02542030144c80403140b1008002400b4290910011030002000c041c030801a110031240c000b4010b010605004440d68001c05410761000c001400600006103051020b920210072100c011002082205060401e4407040101030a81c04d0b005403100c000244891080002d0603500f101c180e001240d15245140150203400d100781418042d0304504c0c04c0743d2103040040880e0b424010307503081040e512141c40c40001d0040c45907400584905140c2000d100061022422000007a8400d460801e00b990329014880d80e20f010309491194071100200e13200c0c4c01940300c0e42080e02074040c103040c00900c1240b0300501900799003540d00216484580030801300420303e07095298200049041e0b000c0c1c01264116000b09031248400c0304040c0c14001032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 29477802 1250 29476552 29476561
    0xc060527030a0605041110030e15060d0b01240309020102060109021c02041d070206240a1805040312020a0203040b03180303090f210a03090c050406081c02030a080a05 73
    0x9210014800c1e43c0010100100c5c500740c9003903a02c811603c0512800b500700c0c0120340342c20901a104003400e0345259401010002d040700d1b40d0700c108001c01003209401200c018040c20015852101480c041c00385801004030741c014071040e1005d060b001c4454001010309040000003d40d0700031070410f0542e40841005a1f4a021007072510340c81c441e4800d81e200e4224400500010411190048102605100c0c03d10b000c140c2c45510003243e07921b405542d41e031001d10344002410120442c1898081150a0181107201855941d0b0505020554905150345244d0f4a90b0100010140e1010141d40c448000c031104504001e02d5610003503a07401240031700100440c002000c20442507007050020540c0c80c94508803a980d02e484030701691620209418807013148104607500200000c00d01c000d120b040503004a04d0b0070070b071002404401404886006460703c410740d890220b03694545000301c8015000c441c00501d00109101d02e030b00d031211641051a0110341080c0a00707030400d40c7c0104510b030846458030000c11a504d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 29479052 1250 29477802 29477809
    0x1503030c100203010e0f060303120405010b0607030c030e03070f0b18151308030304080702060306040e0f071d0f010b0a020304050d06060305010b01020703020f0103020723030301030c060527 83
    0xd00406103490344503590359240c14420680040d030683d0840c6030407103072a0302c803006915460300081d10690b62542003400351081c4544000758403a8042e0041c0c0c0080303810030300000450400d510120b01603001860342120f2005250308441e07211401c2d9000d50007000c0044c40e20000440386003481c0108100000001034240b520306114500f04c40108008000300e201d0051003010b92119800b00383d07410034800030440000785441c400320540340725035080007506250004907404c002041d440281026803159841e1400c1c4000078042110850510415005200a50400707a08490100c0c0039142c00802d4005c041c10403003841800085181125415082c07152a207006c13000c1a411400f5a800058004114070710080c280300e400d4022404680c044c0d4000c21510b60a0b1004985524490001a4005001224482495100b9401441a40c1c0514805540000b440d0155443c2091203600013010380e0000c0018000e200400400300000c0255003410703850300c01c03880107403207103a9401085808400395051070b0004d581c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 29480302 1250 29479052 29479057
    0xf110a02090f06010908030a020615040f0e0105071b1205070201020a080d02030103110402030609010e09070b0c030d05011e05100509030307061d0c01120e120304060f180b150303 78
    0x103a004051144501d441031603810148001c0750314500043c0c4489000450f81d4000c8200e03010480701d40c0c050030103603071004154405aa5140b00380d07600140c3e03c00e40310700e10f109148a40f40c4000848000402c0d107040a200081030110406421140d881d8a444070500241c03005820561411050502940b80e03102800141d04050380380034003800307070400040c402501e5503030341e0300440c162845010096104100c03642840100c0c0003c071800c903006401365005020f45d48500024662002e800340c210b90b50300c0d454900469280d0403441240316079031700210740e4140e000c900d0b005060241061a45180b080940011203295000c0305125030750140303003c82d2008401900c120b040340c0c0e800d032000d400c403582d43c0041c0c40c01c03000404204a003904076144c00c0004014100b0045464031080405954800b180104200307604010100200d40392030503c103404010071b4490aa0b00950300c07480c0103040c0020350210b400c2a40040e603812100200d40c100781c06800c00c0004c1c070148001da40120b4404024003280020002003403651 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 29481552 1250 29480302 29480323
    0x91e0105040f15120203061303021b03191a1501020703060b0a151101060b0a05071407030501140901050c03010302100507060621030201060e0907030b040314070b07030c08070f11 78
    0x5054010380070425401035030130624180d00c01e074202c0f0200e0350781540c11042103202c10350080058100f409070031018a003007111800003041c01015104801295900d441608840c3c80007160401c901e51444400c0e50003c8000c0e40c0d01c0058100f6181c00d14902c2c0d0f0000b9221030660200404103980e400c1c0001160700d8801190000d0180e00d048502c0510018a0182150100045402a642c200680481c00c508503034160313906c1c2400e58550904002242d921000740381102001c03040c0900c1030f04030000120300d09000300144051441c103c82c2640c2030445c44c42c2c0c00d484c0002c2240007543c0c010801040140c0300c036482c0d906040300c80c1c0381254481029180090140103540c3c040165550140d40e80484e03d07607030281000344144650000c00c605071743c1e403202e03001c2c04008984281c0b064000d88400c101055050b289254028440e15058000119102151145030000d05c0c007aa460b401407010007550030b4261107491600700240c140401c40d0324000000a09008060540100300300c61410903902c130000410859801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 29482802 1250 29481552 29481581
    0x30712121b060b0405160f0e0301020c01050703050603070603020c0a14010b030607120b0109050306010b03041b03050d2a080f0702061803160b030a15080f010506091e0105040f 77
    0x8203019400d012002c3d280d904245445070303280102081c410181d946030700000100d280c540242103251101c040e9440e50140c0812030b090f54082204080d104000e02c60a0312517070840d24000f400342481001d251805505411143c24903104104400e061400020f842940380e611081c420424095030245034090895140b005800d4801e40c02404075958100c001d2070001d00368550704000605940d401120300316071030300c5207680613008030005100c0061490011503101d8000d41c2c06c00011a03940414058803040e0b94402d40f034940110104c440956800078808181c0010043c3d01101c101c1401041404202d0886005002c107200103410002000211309071040550001c0040e42c0f030701240030040340b940d55004c50710351190003040c56111513039000c4192601520300c0b1054030b600315504c016480c8020301d014240307002c4a803602c540000f8440410000c5017003203285840041b03202d080000070301103140800f07401c450940c2e00f90b0511030f4580003107080440c1191000c9501084080c4224503074001021344002e8a001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 29484052 1250 29482802 29482847
    0x60906050a0b1203040308030c2104050a0203060a0515010c110406140405010501020a030203070f050109080d02190302030603100504060b090c070506010e040c0303030c110304060f0e03071212 84
    0x16100601e034070942e034458040d6a5620098a1440311584900c52800000c01c001c5041c404504c445c5c1ca01d10241c145944280784000d1b0304d0060300d03811130b9601c001720380c2150140d11060700b80c000c504051103500c0c3c1215900704140181c1c2840d071560010500082003660402030703040c4847c4d0900442e20990302c0400c001510806c1010340310412403041c0000080118050790401e400040c0a510001e407482c0d5040e01a800342d42090502c0e5948203800003000c50a40c0c140d9250345000700480e50b0400140410b040ca000b006aa409506450a040200302501c460034548180200310154a01244114180c03544040006250b50f95203040e8006100741d41166421131014810043e441100030000c3c10024040e200303c03451680e0307901e1380210780c1c03808641c000c1032261040c604000090090b0840300f0801003070b0a00e42141c280b0009000e01c0d6130046d0b07000000181703440a075200070a402c4421149400d07801ea0103080103c0c20202c0c05401c0741c201d030000505c1e80c02890f24040c0500d12070f200d01c4c07422081007076070000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 29485302 1250 29484052 29484061
    0x50f030a14010204050411030702120c01090803160806010e01050301150210050a020408060f150d02030c030a05060604061706010b0a050c01090602120106050c06010608091f090b01050a0e06090406090605 89
    0x5000307400c14001d1710f01803854541c070391070203842e4081642d00c131f41c00540c020040140908000c088030303040985026220f40d01d0700e100900103515035000d50b2143c01803c01003100b030103420f80024003001d8058152810312078031316002440783e60701004803410740381810444040e80000c000200e180c80d03514641c08550626041c28800701c682e458000704220740392107007283c005407140080100340807000c0e28002d4050300c0b22141c4000604002e03609542e0f0a000a0545010708800130129080000c0074004580f2500804200035152401d4404c0750050310381c0d55481c0e1000d07003c81902c0d81c0e8442040c014411034040101c0c80c111840e01c220b08850310841c049000b84101e60a91a004010303400c0038175130b00040c40032800040f0b01c0900ca002a103101910703050081c040c1e80d1030410305441108004d0007100080c01090040304040ea20002e800d0703541c0612060000d028040c60800e940703401030680119108055255042010840a2400d56000b41c01203540404644583c500500100301e18100140f4041c244000c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 29486552 1250 29485302 29485343
    0x3033801020c0306090a02100f1211040b18040c0c1e0501090c0306050901140402060717090604030503040801060501110a030807020a0b04030f030614100c0602070609050703050d020303010f050f030a 87
    0x89a6500c00c1d5600c41d1023185e192010794a0084482d1050000740440e0310151482000e500000804032400140d42e02e0b03d61181c2d041c0c0030340ea001004000b90302c005e01940e800d49040178070074424182c0701c520b0207031600010350351030801c9030a00b8107100001019003521102842000c0d80141c0e0312a03409001000c42590344d03d400f030050001107607104459460060920100021030075114803d9a00800292514001e9901c00c14414598680210500701c1401031504549a5100400145000d00f005544551404110b03900392200354215a040140b00442144d10f28070001e0411070041e0705051045407980c030140101d107803020112000c0c042d01400c6040c4400e141d08200c01e900512529602840b280e5111016850141200e516443c3c00821044009050758820b1a000c1c005500c0351074003515180407626110155142c8000560311500840410000c00c0010880401007040d01d00140d8119854550900c140d04a00c1c4100e6010341842181c8103050356060003141d000f158061140da241882d02c0021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 29487802 1250 29486552 29486563
    0x9140a1d04050f010b01080a020d1b0507021903020a050d030e0d1a070207050303030c0a0302070c030506010e07031503060914070e01060e030604080d0e10090f03033801020c030609 79
    0x15641c5015040440c043c0000600520341ca985068589111917147c1c036440400075442040502081c650b506449038800c0c21400711224031000c00d0f601c86d6111500f5004010103000781e44640c100b0f0940c046c0c0e003000142ca94030503d038102d81003203c402c0f110803001e040c1540c0a42440000d150300c208021040410024542810048443e400014800540d0b80503000d99546589020303079580342d4828000501020280d20080c91000010b00d00582804425501e05160f07844541003107034180c200500500074003c5803920103a0001c500d250a00000c85450107a0700c00f0401c0340809800d1903202c001d42018001021403445000440394211101e450703442c03203010301d4a00c1c05e01901000070b503110f1361801c03c2d1900140031401180c025101781d1901500d245444020002c0c0800d0b0383c200c0c028218003a00036070492044400303a9001700030300039a07451540360007012120034080d070756018494105014004074074469800e1600300380c2441344000c4050900140e1600c00d5a4010b00d41c540309480c20400d00482c0883d0f03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 29489052 1250 29487802 29487811
    0x1b03080d02130801050f0c0a0905030616110307110105090f06120a0b040209030c0907090807141003060b070b100506070c0503060601030204032409140303061302030709140a1d 77
    0x1000b49201c0d4542003064280c60b410f40748541004280c0c80841c62481108004101800c082d00b00003500326555000b05e030401c07800b203a24504015910000c5200340e0382044c2003203202039941015510f0130f0159691003580800c07000005041040c0450100c800380c83d80c01007803000d0500140300584803040fa50140c2800079045034207403a42400c0c5081890542002d0007514541c4030020003810031520103000303001e02c16100030321080030450211000a000c0b14140030890242c01c1d20302c14001c244000d4010300525803030280030030303040600c0c1c40001c02000c0d101c10180c46426a00900200c55900c1714440c00b84a540c00b03402a40d40100c000814804000701c1141a20844009509407100d5643c1c100064089005034071010341040b080541c118412890640082d075000003000700060009016158151003454010303440480d680000240001d82c50200c245401c003000000b0154a5450b0410004041c0319051040000c50f00c3c5114105a807503654003214006482d140c0780b03240012441482003a0058020344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 29490302 1250 29489052 29489077
    0x1605010903170c12040c030f0c0e06010e01080c0a0c0c080c13020c0703022205070e01020606100504050f011101090302070501090e010303090302090408090d080306030708010203010f031b03080d02 86
    0x4421404607a01030442c2d2050700d0300b15105003045080c0c041c070001c40d2401842142e42c881752001c04030026101d180d40d0b0403014020058200ca03141041c1c8000c21112020782490b0500c560000311018a0ba400f20b00240e1040c00f5403401394649a10b01020f0700da841d142c480003000c8400c0140c0c0071a0b1558001443c50500c6811901131280c2413034942484100d10900a81c2103180e00452014405414112122800252184032600980007404c500f00200e400035030360f140008044043c41801980d0403c0034640241d0210780b00301a00550000290907440303584a002d0142e40300702c800303500320780c05108a0600c0a0000e8001e00181c001d500d00291a606039004030350100f542000701250400e25240568180d9a0540316441c840e07003150208480b0301c2d401003084501c4003003044840440d454800c07201c03100502c124503c0d5200e042070310804d0b04040749504801c059a10600041042014940b044000c03250442892615a000300a00c00c511001d65040509843c10006483c00300003003a9005003490309517003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 29491552 1250 29490302 29490317
    0x2009011716050a140d08040b03060a0501020606090402041116120306230411090301020a0906020c01020a0b0402060304020d0b09100c0908060613021b01050907060c23031605010903 79
    0xd1024810341c822900415400943c00b0070103100a2034a611442d103041c2c1c0c000c001d046001c8240d80c40c220603505c03a030800c83c0b14000c0030060180c2c42c101601c501000d81710900181c038a43c40c0c04404295800b07030051000c3c0c4219100e21181d0a01001042101c43c82009210110800030303140c2860104140d8020304180000e10742000040c800792240240642000b0b905041d182c030304900c40410001c0c100030010a0f100000401400045580901c024188082d50780c44000e005460408040c3c10a05030012207415508014100c01c001424501d140368050350455043c1d480e9211400450082d480b2040d00030004600d05051120700c060025000c10b0140c48030f4814010040800000c60314941c0c2c1e0300ca500c1d040d6000c1404140780c0c0c54080141103001c40f00b04001400d00c07080a00304041000f555080008a07550b801c1071210b1600103011301130151020f4280708240d59280d035074025006484061f240d0720f0406a00d0305041c03d010510454404e45805c1c034840070200900e050250003080d07100300c2100440d40c1c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 29492802 1250 29491552 29491573
    0x22230a0b01050906060406030b01020c0604150306061e030218040c0207080d0309030e13140a0c090503030a02060c0c010e060106080f0708010e070302090301021204030509180108030720090117 84
    0x70403869031041078082c0810f800c080c1f4100c0181c01a0910303d0310ba0781540140d0f0101107150301c0d168060401032003005031320141041c5589002d4101c51168000381c00b00300c001800e044000030000781c14001880c403464010b0b0780d030030301d90800c2e020070741f1300f00320030b54030038109102c080115500195171020707150800b05036042001d8040040c2c080300d0401c0002008200c4505002e01d041c5055580142002103200c40450001480c484000c0622800c44002c20116a210219965254080c0c0e040300900001c2c0c1c01036150503002d2201940d1950000c1207000c00300e13070004001940716000c3d00490000c4400408441c1c2ca0350f198003014040d004120740c00ca0705520103000146503244601060307412603c192080d00000d44400c20f04801a52140e85066099902000b001d040201540004d40c80342d0b01031ba03605078440c6134400800c010705024034004600142e2400040c8510a0301108030340b0429071016000841c082004e941500d80c910554030716078080b01d070800000c1c5410424000400041540c010703101d0711703001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 29494052 1250 29492802 29492809
    0x40815090307050706080603100509010203070e01020f071e09020d0609050609060d12021203010e100b031504050a1b0e01030627020705030405030601060c03020606060322230a0b0105 80
    0x181c2e41000c3c0165000181c108640c50281402031381141003d4160b40803036801ea82048240e840507505203540303039800000c102d03480b0b91003017070070f06042000d2014110801d0094210b0355a441e01c1d000300c414209160301c0001204159600840041280300780a54490700040c0c00200140b515120f4018410300f8a4005107503442c00440c250b01c81c800050080038400f0075502e8000c00404440c21281c1035114070301000c1d80c540d0050010310300800400c12618614a003020030f402d140d485a50046071010014020b018400504010b41000703000103940000e8295603868181c1d001e0120401103040040c0e010400080d0168004000721040a00303803002e0004a030f45a0901d40036080c1002900c81c3e100352a146e1a40c1d031640354000300415030140301203d08040d00c1e04006803c0200a0380300c200815403043c0d441003010b80502c141a80490100d0b00306086140a90b10340c11070301c55101140c110005a5074a003000c104880740e800c10320100750128030001c40d506044059890513060f0060b5002c0380007400000e46031a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 29495302 1250 29494052 29494057
    0x506040501030803191d06010503100203010e0c0307090b0406030b040b0a05031002030402040615050309100515061303050303010f030b0f04020f19030f0f11090417070302070306020408150903 84
    0xd030f00019503891503858800c1c100d8008110781c4010111900c400d22001c8015019100d55852102600980b0a07549401c00b05407620224000b1000d0890041c8010024440791180c041ea020090f400450f50b2545c600c04203d440c04c428ac6c100702c0d00f100c008036012072140c0c0e140d1300010030100d054904004080f4882c0c2049a608054400c150341030748048007010501e1007030303000795030014400b41011440300e8450310319a0480f484a1080b400242000c42080168034003041103443d0740041e088100028105201c0d43e03240c207a2280d5101e4002c442c0010284038606040a040e001560460141c3e902d1b941c544c5a0a0360001d070920060715400b06260108805035419040c2a0044e60700070800c2081c0c1d501c90090003604065000c450701ca50600d400d00001091034408070040040c8078021a861903c40d51400c44140c4c00d04940a9000760604c03c00c05c030000c1c18056040940225140006882d0302c138500d8202d10f428890341000303010030f0011900050f203042c0003078541039a00504410005030380d19804129901d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 29496408 1106 29495302 29495309
    0x10c05070306051905060901120f060e060601030c090b030601030b0a03050601330c03110c0402040b040302031c080f06041803200f0615030c030703060504060506040501 74
    0x440740b40e41180704081c4d909007080207090400101d041100140200178000c190f10104100340516030b0000c044080d8860801e01c2442007180495494840a6a0590119052486003055940590102025200e0200b15a400d5684001c01100904032000303006810010112004c000328130240310486c00b0704850079182c0180ba40c05034441502444c41291041c143c42c80185182c0000d03480160701040304c0d00341c0381510040700200300d003a09010702c040e81650300620000c5c002800210180282040341d000310103031018006410300030320710864142d6150000070f6012000400001d01c0c40000d5421a1020304000344460804034084920301880c001030300030a400641502c80c1d100c3d1303c00b2680e10302d00c0f4103000d03020461410703411a59810780904005295842c02c51081d00035242040369001d842001401c83e0503059803802d0030401000700340d0b010f44040307003803000040e41402c0600556049 = true := by decide +kernel

theorem cover : BRFrame.Cov 29316552 29496408 := by
  have h0 := BRFrame.cov_init 29316552
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29316552 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 29316552 ≤ n) (h2 : n < 29496408) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
