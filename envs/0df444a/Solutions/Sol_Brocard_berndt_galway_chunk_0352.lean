-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0352
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:22:14.395008+00:00
-- url     : https://prove2.me/submissions/8326f85f-2f25-4fc1-b1cb-a9d955be465b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 63129499 ≤ n < 63309355 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 63130749 1250 63129499 63129509
    0x10503120913110a0c110a03031b02010e091005010809010e06010302010c030e040f02180a051509180a060602060a02030f040b07110115080d05031303030203041a07020a060c020c0a 79
    0x145030301120020465521100d000c3c1242861107403190300c0c1480040c50704200380c10645440221840d00301d40e0386031003294030003180c1d45501c0d40700d41818180421402e16410314000d80c1409501c80030360102e80c0b00c60080c14032401c100c180d00881c03507041c0030001d490303000090201d40c0a41c0c540103400100e450000707802819207030242031444401d501440c00301c500c1c04070003901da07800c030742080c10f0b841074011782e030b0043c0c85800822200e5080d041e0317606d030a00001860a103d0948e0114506001c030710140b0480740181456800034141002c420541c01e400c2240c84000d0b00c41d40341056540742d0412106038103001150f08900507000c00c3d480c600707001179103000c0c0940240001d0800828140440c80e0180510a901007062008000384004400e6180d840307404291841407504c1030040440550205104504503882101e803a0408508076040351011002900000c0c0115200e83c6100c80406c030760002860300c103100d108694007e01d40d0b8510b074940b0710306a6040425107010f40d40284910314507550380c5040c0b00181e40d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 63131999 1250 63130749 63130759
    0xe01020d0201061a0313150204050405070c0201080703020a020c030708060a050c070804030209060f1206040308070903030207230603041b3312060e0402040e030a080a0905010b090f0f0105031209 85
    0x107141c050084207880c114960062100841140c07c0612200d0303500a0001c803030088504024564a120082e50b40c0034405a00a00046844001514460280c0c0c060400e8021030320484607100d50f200302291824405404c4030490764050700821000c01038501805901c0310314900854104000d0f5540c0b54482d0080c0c0c00002d119140c240e00049a540f109002c43d071450900510090844245451540d103402c400d03142600000c511000007403160780244141070449505500501003035181080c1904640082d020041e16602d071089001d2031690380501450155000d040095280c13403514043c01000d544607401f00c410700c203180c4040e2003070070040034400a04100c00600c4220ba149a076408840010b807410701c001c3d0540c50042c1c0842c0ca00301c100a100d105e10300c00c0d24104081e000708e049165036070241012510004201100207010b82180f0b411407980244a000045034070042c00000a55840c412980205410840b908110310b142d651901c090040c8400d5015000c40c8081c180ba8007854402d45008902071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 63133249 1250 63131999 63132001
    0x50609060403110411030c030406060e090c04050903160c06020105130c090b1917100216170c15041506060806120c100f1d030606090a0e0703030e01020d0201061a03 72
    0x540f543d030803417600b2250400c0040d03078910304800705110716042940d06440322072421001050104129214a0281700c4941c01440050803180802c0046d14006100c0302c014041030103d44e40d0702130840a064500c40c416072407115242d090082c02030842c2c01c014034030030104a81c002c1110209024102c1d407021380703d07400790102e40594000c01148030340f545800c1402c8900e01c10f03580054030f8240140c4214908490805680d4018524041c4d0010781c0100c01016030000c0c0035160080007e04514080f51400c1c0342409020f05000c4030500c120308008031703212524002a500007c12007003001c16400b9014520216100b00903082c03c0c060020314602d0000d040038041d80d0000d040c1c401d0510100441410408014613402d032a968a0f1070041a00069442120208030382d007003090740c00780340b071080d109040c000030b0000d255980c2c82e04208014a4006020001d0b080d5a401d109100c910301400404007550280c0c40d203500c007202c1e041c002071070038100300040c0c0300310b9241c0b1005200710300d1404020111000d0320b9000640b2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 63134499 1250 63133249 63133283
    0x100e0c03090316050102090a050603010e150d0506010801091505070905120a0501050a0903032d02090409050a030207030b010f080a06110c07090902150903150a0b030d0c0c050609060403 81
    0x185120b410143d0700b4001c0e0f12280c0b441004415001855400000d9581e072494541d11030a1009902080c0200b80440d1242c80000d030440406105408400000900402d174508150b124076042c000b080c0c001c0d48090b5101c10b0a00e0030b02030322060007282c0d140088402c02c1245840c0100a000d01c20070701a0610031811038100c100328940400140d50340b150440c0082103a801c0030301c811401008040003c4001c00d041103810321940c0741000c030881c0280d50490911a8041405c41040000c1d80041d0820703500a60340c1c03039101c1c0030078810843e1460b171521980080400314114105034011410580c0082054120200d003808160001f241c0c9070300f006c1c0e002e540440c140020050404c02406000d10312040c074801c12030b0002c3c0580d102c0e0081d40307401c0d000b90381488a41c008620111050721486080c91f030981c3c0481c100303586091404d0a0744d070344501e480c03800285400c10600080e040404c000240c02c00a00d900c40382105011710500242e0052004580d001d2400c981000424202e0080b48400341c880c4a642c01d850304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 63135749 1250 63134499 63134503
    0xa110304080106060e03070609120f02060706091103060609060f0d3f140301031e080f0d0b03190f03110d09090c031109060711100503040506100e0c0309 67
    0x2801d10034000740300b4142c591310000c1c00c0f2000412050b100b4410501c001942d140600040d400351890441c4140c0c03a00080d444142a682d054401260040010059000031039654400e42c00550b100c0c0940394000340c954402c042c03420a01030841417042c6005e00c14800c141d44ca01e18038118030102600c0c0344201400c0c900b400d0031600460405942d500c0340d00204070308148580f0f4007600720000350003021b90701c407080d0400c01c4516202100b00044400030800052011440e10039201c0c500300c2c500701050f06a902903076603030b8030540c102c802c00c00c8003100d01041904101c140303800752010340c031000d40040c43c2d15907100c4080961451282c00103055844212000b500b07140c0302e003440e00b2040754200c088071500031607100003d00a01052007000303c06c51404c0390781d450080c428080c185188806121040c02d00d10520b003080012303448468120b80320103100101007880d4a500d0b080504003e52601c0d126200c3c0f40504001d400c01600515903100a03003104424000581c08505494100688200050f101e5072180c00c4c1ea4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 63136999 1250 63135749 63135757
    0xc04170a0606090c120603030207050906040e01110912030720130501260102031b13080106090b090903030c03040809120f010e0d0201060803040e0901091a04030207060c02060a1103 79
    0xd84075500300040418000d0701a0001d10703032580103998050741d0020050310380044542d1030100800503006040e0030000c6180c4030f5107150b000800240002800044c1010f02801c50b0000e851108520030042507014541c039102e4041d04014210310302070f510b4982d4941c1d420000d4054000c0c0030340d0a07072a04001003202e468400882c1408041081c0410035540c4134054082a001d8000c6043c881c0491610002c180d80c0060007683d00a40d01d009406075640288450342d1029048078810902ca0390f140103000945000c2405000010701540400080c50107170307441403003080540101803240039441002400401c050344001c4070385c05500180c9031500d50f048403001445c0c030380d03030780006180600ca6600e110346a14010340c46060720a900004a0340801181d020907401c1c0c911034811028650000e200411660f00d14048042d0703c442c0200000520002e650380d40c00d1140700c41e070004105c101d41a003c000c2003580401506014103c0c0f4240070080c1c031065400107c0300c2c8100c05418041141c903404108854600308180c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 63138249 1250 63136999 63137003
    0x31104120609080c070312030209011d01030e03120a0e0c100e0a0509071e020c0a1a0f0705030703090b030f01170f01020f0a030b0f0a0312020703081c050601080c04170a 74
    0x4c2c1d641c1d103001342c0150fa4501901082d100296a081c2080c0f41d50301074801c46507440c1c01030711048101000d4509188800784440e151714189500e98240714040d440500c000c000441c24051303000814140b00d400f00c400c035001541c0c031002940c006c0c9114202d40d40e03440c21f0401c0b40c0010b071428101080344c0001090400700300c4c0c2e00c86504045603400340325400390444011955480340c00115880e071503c2400880c1d9490311007500507081064102e003480020084c107260b81920700012032007803a01403401c000400e43d5001c0300060358250804038120040580c0310711850010f2a82c400342c103045042421014010134130600c15900c18000565002d0b03000d03403042c040900c0d08010341f4021500c400c1080c0c2241541e600408040c400240f80c200c14006a1610701454010107502600087c00d103030444e0b58101e109207900d21070350107604c1840300c00000070358070f41c0040c00040f07002010451501d1011503400103860b40a840d481c1070100c683c1c1041400a084400e8400302e6042c4070003030200c01e0f001d4500e941031403040c0b400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 63139499 1250 63138249 63138263
    0x70519030f08090a1502090d0c0b070c060809060105040902180712060b0f0307080403020f0601080706030c050c0c01050901030603061418060c071101090b0315030c01031104120609 79
    0x2000500d90008110700c11412142c0b200b103072940d01c03440100c4c0c0310030b100c42000781072603200d802c0019030904c40c2d40034124078040a0031074802041c15031a0100621040d40c02110100d9000419000300b00007000746400500c04da0419072200e00381215660f8448205000341c030f000350703500d0700808255681d41000018101455420480b42d040c05a8010030365090307541070301002c41c14140300281c80b00c81c0318202c1301d0f02008103070036500f15110b0802c11500401c001e48203408500c500b01c544240c40c501031103158000c24403a0000c0075002c2c030b000c2c00035003030b070b0f26401860050107000c0c032014100c5540030070040c20004003460300a5a400800006a0003421582c0000d002d046ca05960040c2e061100074500707000c1c41c24400ca0140103000328000d40c1c0d643d030741210382d0100f0303070424492400094441c511040d16503e05060100e801e60701d0750903014643d0011200f6228440310191540c9407070400b03211130112031100303103014050303a40e414003070907070301d11031446144004448900568180952580b09500315540460 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 63140749 1250 63139499 63139543
    0x705130e0a06030203010b030a050a08070807050304140307090506010f120e0115030203010b0d0201120b011202030703020310150c0b0604021b0303011e0f12110909011a030d0509060705 81
    0x1e01d4800411603800120f0080d841c055252240346000600d8a115a43c414000e206481c281c1d80c03400c980307801c41482141c1006090002ca000103c040c80507101601091580100d00240d074000c0515091070303035005803e0f080c034003014002c207640c0c80110b501042205090441140460b144848000c00750902c1e000301c0385d4a41074408490310034030301f400b40403680218028044010081f0422410482c0d4660090115640d2800c42980351080c2d0029401000c050401002041c03001402c0002e80e4001c8501c540001c1c0d0010410080c0d8040381c5584010b01420361084441e1714244901510030142488042c240c60b015100213a42d5a4881e0100c17003001c000966900d0030201c411420603500c0e00700380036095200343c6101200141d1080300103490f089549107141c3c01d007401e1910301500880300480c24265505ca071145101c41c2603843c1d441c54640110050070001440c0318030f4003958025480c4540d200c3d80702c3c4e00010050800154802c00b50745055600700c0d030013503458510349450b0345491003003d030303007205104610 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 63141999 1250 63140749 63140761
    0x31008060907091b0207050d03020a081612090b0a0c05190b07120509030901050703030b121f0915050712051f05041e02090a030206040803090312120705130e 69
    0x204102d02250200e00c3c062003032094119004540c0e4614001881c0140d00680c8104103e141c802101004e0368080e00550381030f40342603148c18166a015408900080340300c214084200074162000fa030b551400ca162160590303042109406251080c07030141002c000100c02d00c0000d00c48181f02420070004900e00f00700c1c454030740d843c04030a0144110395041c00b0903d07111456100c4011406420b00c6000d072a0080c61408140704015a0582c010101c15001c055845480c0d01c2c0340e88030407a21100d0036840e6401032205440765241c0504159185007907440d450f0420101c0710004044c416424050441c0340808605640c6908003100d02ca03500364401c41003582090244820518403840061940c1e0307803c45202e000c1900c0724180b009a4410101c4460082090700103101780e481540d0151140303850080100d03d460fa030725000601d007034000b501b000781c45400c0011540b80d01d140c1003044805d40320f11074000c03506004549600011010303004040d18180300000404110001d1180c0481010344030a08180000b82440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 63143249 1250 63141999 63142003
    0xf0f120510181b0903050c1e100315050d0819030e060403050a09050d12030c0e040e060a06050103050f04030507020d0c030b071103040b0a050c1203011d0c090f060310080609 76
    0x35240300881d4005842110310451203900504c0982e90058021b000d07071080c2d10309020302510703042c19013615a4014410001c81d42e1714001c0322001c07140c283e070b800319804122001000341d51003154045486182c1d802c003140005580041034943d15142041d41071880c00c07522006801520108610134880d00070082044101034010004c0c10b4084140d50361041c81580340c07400d101c4031183e81c0c030740a401031080d1494440070301e110350042c014640c103501c1c01c80302d49100c202c04102598020716104600350401d00030080080b041d88500302c020b1009280c00d210310705240c50300d01c064900c0948040e0401c0700010792401907449043c0d5841021758000094800d0f40e549017404010010280d60201c00511b6000f208000d189000098809036810641960f1400ba088541512540c0c840d111a036528000c0b801c10000d040015400340d40200a00302e5a03105801400c251420140401001031017000401e021250340c07500c131060120030000c02a900d85550351189091007040f24959401280300d40b25280404c0942100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 63144499 1250 63143249 63143261
    0xe070302091f09050601080412030b09091f02070c051306050607081b0f030d090c05060705070807061e03020306040e0a121d0f060715060806070f0f12051018 69
    0x500c4050039482c80c3c072985002c0503524261945030020b440034022602148112845281d224018180065107062040c08550459411a00d2035869001074480c005022003400d0905400d6100c608210314012842e86d0f80d41c035000032805018020050a0030000360003215038000005007000429031511080a45400e115940c0700380994568440d0420541d042030a00181c1c00e0042402c0343d026509003080e06601c2801003500740806d07a0b454100c0c24000500703895050007005024080d0000e81403103410030050b03601d0900e40f80d0010b0204090700c4041402003248680c81d2010f000300d440e01590740c6c1c07242c1c800640178010a0342460080d014082c920780800c01c1c4017190302c41e100ca10352035a4500707800e803104a0005141400e0304c0c40c0c0002d1100c46100300741c9484002400703441d2150303103541000b04401824804856080e00800c05580c0000148044036810800d0710340403140f28a00205c04030350100300200f05400c849081d1030031507125000b28107085141c010314000751043c1c0c032004100e40500041c400181c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 63145749 1250 63144499 63144541
    0x109050a031b0b0105040b01090504090809280b0a0c06020c0a020a060518060703020a0507082506021b0102030c030a120e01090302060414191101021002090d060e07030209 75
    0x70a0a1200b905180a415080345454010300e502d002d9138a0301d02400060070459080504000168401090640c0c6900c40d01501500403007044d91a10504028461400e800c0600b0307000782d0096000c41c0242011081c0844199014401d07055128908810152006c0010020041c601030022a080c09a00c00009183c09068001c640a41003291382d0001078032036100b54814081c1880800da0001c2140c1460401046028482d20403a082c802807501c0d02130408107250480e03502500114004178105088801c04d200080c0d600c445503c1e464907104000c1d40d60b0842c1c50014050300c187d21405042c6a000f8015201034001103010380340d442c000e903d00140103052841a5607102840c08030780303000d0702005101c0c0303d200c154540c000701480c4e169a21001c40c242905102c0f400580b045103030815044001d114102e400512030710483c0a005011800641131011201400a801d44140a01d01c0c0315540c1c1c0100d0030f021178201800184410707038101501e05000d403980000e50040c0010090040783c01500024062440d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 63146999 1250 63145749 63145757
    0x1c081621030228090911070b010f06030b01030212010504091a0901020408011b0e0114041d010302121b010e030109170c0d0306050f060313050604030f030f050c0304030810080109050a03 81
    0x1641c2aa03a0580f011000740207000030a40681800503034090392020349100c192803216801c00342e06550f6007166950903000b11704043d500b4a410422582c0500403040550801d0a055007440414080040c4c001e030140300e4244910745070b405203011300606819142244c409040041e03028601240510702075407051103a44560344c6001240d0b5400c241c1c032110355180c1201c80ea11854807800b04401199420a000d21103440d025080000248240c58000c520b400607002d400389110719807441c01040907800c3c42c41c0605d074040d0071001051320860809100c180c0001c1007404c100080100c2400070a00404d045500100b14040001841c10b0b011a40400781c10b040d4010400c6902220042c1402c030207a4501e40310340c58204501440d5a080352034000042e661060030746281c403220080c2600c845150802c16101a0b02041e042c0080c1d00c80b965050023040ca041c240c0141c24809828030b19401e4940384001000981040f85040110310701c0c80c03910840c80000e1038400700070301c03c0881d18180f45803103801c4194220045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 63148249 1250 63146999 63147037
    0xb12010b100c0209010b2b061a030603060103140c0909010b0907110d050901030b09041a01050406030f0204090804050d030207051801080a240f0b1c0816210302 70
    0x550311a50424101650144c4a0701240c0d00c2c1a2a00a064100c441d160b04418034140c0c2c0c0580c0c001c0c4600403040014503a0102250b5a4903129032407180440e000b1803114104e06c10000c02440340c800240035811260711151000c0500c407111201801c054805d81210b61104e655410300c0140441500002040b034421a80c100c0d20751100042a80d800c02280342d02c412a0300082012604d0078020340181580002c107040100340e61440d03200298014100f202c0483d20240500d08900d058901000c81c180540300a46042040b0b80c29516803036100c054000009115a46440f40c2d081081700e0002a540106000f4041010982e40d07854040c1d12404280512070180040408540b50f1014085030786048a030900094440321a4685514000e10310f401030403801079a500b030b84500805c480d071080040840192000180c801011010016104003100c41c0d0f00c51001044a1000810004800c4555190040d00c03000081620f40c68102404104000c2024904d502403508040090b010b40050410303c0c6017424540070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 63149499 1250 63148249 63148279
    0x10509010e0f1513080d020d05060604120803060a03060606050705010c02010911060703140c10060b04030b071b02030601090515040c05030c0711060c0708070801020301030b04060c030b12010b 84
    0x2581d40011420000c80c1c0c00900c5502044404007105904130050100044001000792a840390541c0110410b140c81c03940041c1d007194030540c0e0300c9030b00e03008002221481d103441d1503c6104240c0c0307000071034054480c0100001003a22079891b581200d00865009005000703035076841d00040c1ca2508140c500340e49075400c00c0002c050386441032158641c019803140c002c2d0401c941100511070150003c00b42101440824245010f518031000040c00039080c641005040c0309001c88503c00649408d0340c02407c124000b407100b4400100128100c6034084403e241c03100c0b440c2a000b81011110411180c0a5010302031140045541c1c40c040c3c100c94420a528170303900d07400705060f07014081224200d1030a40b00052007440031400b043d030404000e0403da80100752001d800c400c00702c00501070b42d02c0602e81800c9a4040c51040002500c1407100000a05140c0001c40c03c540c5191544030840800610080045907150b5094051074080d40c824401c1e0280500071410400503040000e0007000900703c42031040c1010881456 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 63150749 1250 63149499 63149503
    0x30308010902070b0c0d090c090606090501080108060a0e0304090c05030403110303040c0b030604060306180620040501030b0a090c2a050a080306010201060b0c0a061506210f0e010509010e 82
    0xa141c0c2d500009440c082c1e550020b0035005e41e00484000f4101c5521081000045401d100021001c2d01c0090317000118039186c404050b101c2a1240d100a0500c64130100401821401048142d84070001c0c2a01040848810342850300318031554000c0c1c48803031f01d4000d905020a502c00007861286111b43c40d02c041c44481c01a15503030341e0000b114000c06a006100081c04005110005103800400281002c2230443d140c2d5501c2086d60440ca00300c0b40c030002c0c014004028088280030709860218030251004c001e0b1100342c00e08015110f41d00075241455182c0b0b254960390340360b01d00b0880c01031000b65001c0120342c090140050210520781701600c1c400c200000c8008560400003076400d0713600d40c0240145003242550ba201156900000c240506655880790700003403118200004200c180c8461028010104e00303450828102c0300110381040078049e00c81c00034004c458000d6103001408142c81d44204805040c2c080450241104d420036060701401c03d00c5803880c02105402550088100c0c0009004191852811039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 63151999 1250 63150749 63150757
    0x608070c0206090f0f0315040b0c040305070e100f08010f0b01030c0c03031503050706110607020c010c0f0c0801180c05060a09051201021e04030605130512250c030308010902 76
    0x42d40c080002c1010120900d411040c0901450f8084c00c000302c1da040c0c0c000020700f04040b070030480506817040d600b0803003040310300760201d80d11a00844440381000d040d40c460b02d0380c03900140615186d103881c0c1004100103c481c00c110304024200206c4101c40f0360380f5001580d02070314107400c400d1042401e0551012043d802401001d20440c81070760340c2088401551030031405480b40f008041c0501081d60f0011021030000d020103005803c4170b8880a81c10002d1803000707860014000c128400715000b030700c6d6920070703681d001c1070040c0c00641000c1d2041c00c044036070030049480d60702984040703000e6180500120000f007a40505000c110302490181c8a25543d0304103104a44c03159400c40310000b12820b4090102c0c5c035042c0d05030a00031030200001804c06505901103ca940c0a062072040c030000042410410171000e80640f80d4803c3c490110125142010794480b40c0d03800c500307a6034401c154000f18410124809070107102d08551845401d04640c3c48141c1461040740c0c0c000d01064002034604d60010441e68032074004c90b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 63153249 1250 63151999 63152003
    0x30309022d0f0d14150903040302060301152c03070b18042406030203061003020c1c111204060201050c0a020d0e040b040f060501110c01090504150503060906010608070c 74
    0x2240101c15820030030a401d00807501e15544169150001d00226554001030401e100080000341305034445500c40502c007140081c1250041c0d40200801c0c0010303141c003015207044516820610150030310088041d01c41000141c45410851841d2003004030200b0441e90454840700d058080d0b07000350340c640d603c11200c0c5c41010500300480348051440441d41c1440d5200c00c1e45440d542650801e54600c510003080450020b40c42400040d8011050040500e000101ca11100f041414114949540d000846840c2c205114020340c03c22351400441100307074094401d0000040321002980c1720150b4203020f611141c0c109001d62001076180c0000201c1c50b110341c50441c0c01d42a0b058004104801081e08200c54070001e089403076070095154680c0c0c040340e4803540204c410200d0318181c0030407640d0074000010142001c003913700080f07510241103001c8590b046465103040d20000d8074041a50100c48a09001d00d15142d806903405205850420041c0c200c08170782103050305c2141d600c5251a8845030012a00c80181d1500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 63154499 1250 63153249 63153319
    0x8060a05010c0f08120c041d160804080f0706150501030908070b0c0904050108100b04110f09042307020d0207030206030a050703091205070c09051005012001020703030902 75
    0xc9480882c0c581e00348114524032611815150034080d038071803240b59000746c0d01d01041c2c950100b400e0265030405072018800049103404081b0350b207048100b036102c0751800d04c8140c05109480300840c050160032401c603881000344400c43ca41c2c50b405071600900030941c407443c807011361000500c04503a40d80b00780600065580c00508060500d040c1d074403004940440074080707000460382040384070301310340321030050704d009000c00c102078001c002c9285602c81c140c1c1c4a5411851041d450511584200e0b26a102138a44681031080d0003078686001e8000b20300201042d0304061403241c12450150700301103050352058451002c0c1d03425540070389d488503010399540c0f5450100943c403440a2001802070f01e8568002e5071703c400d05203004580c41119480e0448020b00c0c1304855000200d001481d8014015924038a0000b0310418104015925294954244031031050281a040001000c01c400005c82e4050405030100712140085550b1142c0d450b0140082658140490061217202e818581840c2481810a0044000d980d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 63155749 1250 63154499 63154517
    0x905031501060f0c050706050a0f09050109090c050706020714070e010e040204090f02090108210405030a03030507021f0b1804020a0614130308040e091c080406110a0804020108060a0501 81
    0x50243e841d1008070100e241000203003c00701003c64000c0042400a020310340b1010b0b55035002c070800904440c0c0e4041d016090040d001010400c9036403100c0700742c0c1240d242d407000007050030300c040044840740710b40000501142e002240203014041000030100c080104241100c1000b640c6003c010200202407148100c07034080c100000b030240c20710380c1107821520300c5004400203a420550005040c4d640a07000491580e10094480344035240c21854941c0b544001c4681a007410300d4440002d60720100081d0081c20542c0354408940c1c0c040c002c01c451a8524a040c0c030743c0d80f40c3c90040d003442e401000100003082c0308a40d103038900552207019544580c011a0060300c43c003079080c05c00c0303001d0750700018040a280d00d00b501003000c6100c64000a15080103541b20b005029503682ca850191421010042c0c8107902c1504401f48510788400640503000000c3e03d60f00b0040c10355a200e091030f030020305500030356001d0100d00162905481e03901004052085100343ca07201c203251112414807a41c41014020b583c041a6644 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 63156999 1250 63155749 63155759
    0x60705040b0d02071202010e0705120c04091a04081201060e0117041e03020a0b011e03061a040e0c030709020c120f0d021923031f031e030905031501 65
    0x400070801e03000d0302c040140c54011695503610280303000c01180f0005035591300445e5600c0350705200f0f8070000c010440b800310031016200300c00c0e502c070320020760030b18400ea0703903064031408220304d4804000401685a01c0e0020034581402c2141c603035448040c80800260214002040c400d01030300b02c6800c01c401c1a590000c4503101c14080b8244000c004d481a11034600c1121144e01201e1148a581c4209209501810704820546000e440c1a407060308003507041150304103050400100086404200da800550206035020062200c1000e03106001903207030007074100182d00a4003080051680400d40058044401c0d0556801c01c5a04074041c09a51a060f50881003811469503d450003038007040b022202c0d61868803062030001e5040b6880350000300450455040d0b0050410b82208541d0441c200c1240040800408074444200903c0003d10001408504240c0e40b10b840d000003500c2d10146901038034009000e03a083c503103a00d08030440e450407800220484e10126440c2000315007804000c61310322990322aa404d02d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 63158249 1250 63156999 63157019
    0xf060504141510031122061a0702010c020105030a11030403081509040201050418060902040e04030206010e09030405010f0215010e16050405090402010509151204030f0c0f081c0203010e090f06070504 87
    0x1031020f501015111b030701d03145c541c8031817500b008014142d800080c0c131901d089690550070f01489840d1404e0074040c8000800340c0d0b000280121501c0d030900e046941c959030f0040310300040006078a1000301c00000f00811080541005605025210030b5000a40811405007000324100007103030001d0002c1c201340400c0007509031a00911100c2c4103202c4021540720b44071202e00d02260000e41c4241c0e048180d500a01c0241601800b8482c0549103019400015260552585540340300b42d104141c10800c0050300d1040d428400d201d0356101007103016041d21035596036900d0302401c00003640c2401c42c10004414865125000f01c080305e00300c13680900414415a41c580054070550011410240c104260030459080000044020416030050f41d201c0040e50509080c010003204c7c0c6040040140402c606c444001308403002288030059900c07203030140d602c40c441c1c41281d441081c5075411100780c0e80040300214110441c01e007003520404102c0d0032a020150321102c0140d5514054801784089041000140000c04c0e40d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 63159499 1250 63158249 63158273
    0x405040f060f060506030c0702090c070818040e01020d0c02010501050f0102100b030307050d030504060f02030906041202010e1006080d141603140a03050a05090c1003090f06050414151003 82
    0x34120001103c40c0e4035030200b1010b920403110004686000503043d411440c1a01c1c03001e4000820a0300035040c4a440c0e900d45045101d0404610003240746078049917006e644a070003030224844150b0080d92038101e0080303041e001d0301d103206000015501b010000b05003814605044450407505a00800250f511038560302d004090202115805000400011000c52030400800030702c0441942d00080900c1c0600340303802103518482d541000d607401042840309448001031110b0304aa00031448190542d8980000d90040140c060080024020001d8684150440da0300c82e03400c0340c0c03000701500c3c2004000d10040b2604200710302e000390810424480a006e0280078035a41e41204d100f800c202c1c2c0c82d039904c10381c8001140c100301c01040c00641c0703070400c119400740d43e0f001d115044220b410003013902c0340140c00052000b01740c2600030ba081640d541c0c112010b12216810b075900b181d400c107401300a41d061600344032018451090809100b0b11601106010110413451090711601c08103280301c03002c41c216a41c880302401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 63160749 1250 63159499 63159521
    0x30509070501051e03180604030c03090801060b0f0c0a02090a02040e060f0604120311011d0d030e07060c06110d0b01110309010c080306010c0b0f090106060302040b030721050c0d0b0405040f06 84
    0x21106d0000343c0100c070100b01c0a0300a0b4041c0c0c55002e00180c041c50001c2c200c8250303070050f0580c0e9051040401811602c030040d2081100c241160340d8603000012010351420300d202070040d6100c0d05040501101c20300d5a03005006035140713400c01180c1680d9400c240003485000510707840c1c10800c200400c014840000c81e00102403840313460000e40c104940480d00e0300355000301c1c0110020706c5021580c081c0400c0100440540b0110350f017030034060001c2902a0580321880d41c480d00e0705000b2100c0a0200b08000707680610000754984060544030300120b104500140681c2d81c102e804900c0310880c40d100321400200b40d82940350169070b03140c51901d160780ca2403629040070f424107050080c55a8440000b5646420091040308542003031b18161500c3d803143c0b0309440455011005152040000740412486034048941c00b401c0c07400c0502402c00f00b03e50504030780d8114071000307007171914200500814200e0040104035981c48a0b00c01e01c0f0001c80041007104a40054500410311a10307111001d0009106400802101c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 63161999 1250 63160749 63160771
    0x40b220b0307080307030e010e01020606010f03020a09080a080301081204080a06020a053109060b160f1202010c0e04050f0a1d070305070914060105071719030509070501051e03 77
    0x6588110f41072450b04508011000720300415201651540d100d05920b0700d000c000d100600c1c0b1030801038006040c45038110034880416800081030080d0b240280b0311a00242028001c0318000c00c0d850038180025017083c05004450301854540605400f041e0381620240c1740b800014001c034042e103641c0e1500950020904409016040c01407000103000300390040b00360410001c04444d01d004880500c0d051300030300d0b0003440d81149030880030301201c0352880035206154000040505489040c1c18103c41d500c03284000201030311524803640800c0c13079042d004007441c9419515180742c04120300c1c3c2004113441080b00c0c50308030317a100080050100720241d0803410492844e2040031401c3c815509006060844640003610598003541d01041840c0d054460084003d056101400d02418902e000074014842c9040140c25880000e0505020218401c1152701405540e130f2410701d650441c1030090090101118011104d0140e1307800058194000c400715900020a556900201c00103118403d10503000500825054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 63163249 1250 63161999 63162013
    0x90604062307080a200a0b0c07020904230304240903080f07051203010e0f040303060801020d0902030c010c0b070c050c1c020901090606200f07090605040b220b03 71
    0x51048004244190080c142260b0702c02c1d1010021700400e01080c0000f2001820020542e100030000c03841c60303200f5900c44611402512002407841c140c1c09a4a4081e40c848006000d120420101000003000c07641044110442c50301c0815a0303644a00461164008009400205510b9005002140c0392584c01900300080d1701034580d101c120075600040c80305941c1060014050043c040c003000440c03112410320401515642c104001e42d108558058442d0030080c11130408603003054001d0304042d0240004d04021503c0342c083c100e00401504a07140b080e40203008254203240507510843c0385c005980d40006500d00c0540f980182200d207201c8180041d6038902954100090f140e81d03104915403251000d196102010640307004000d00000c040c1d00c128015490f0110804c48030f50070050814151880210304141d40c0200b2003054104100e0303640e804001d0007260004180c8001c0c0c0d502c84025a8030954041102070568010b204c0c007801c08035448220b0b826503c07100010040141c116002d2071101800b03840134 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 63164499 1250 63163249 63163307
    0x308060316080106080c0f0f122505010806010807020d081302090a02030f010f1401120902040e0709060803120606070f0203070306020d0506090103020108150f19180209060406 77
    0x61001d40d811404003079446120401200404221415a0450866400311203000c000c1c0001e20140009040d18020a8043c1d111641d026003402581d0a03402c540c500341b4007161401d942c9406c44c1c9428018075002c12288004104194030410302c807446800150024211840e5601068a0f0b610000300412504169040e80c0c0d0016200e14151600a43d0780b60b070301584a043c00701c480c0d10700d00f0050700300012800d00b82c14100012880d450781d81d04060001e0800a0107803030166003540c09041e00040103074005041c41241640102e0018100c0100c8800203420030245440c1c8011035124459402c0c415405100440484c01d03600e071510042c000b091003010700c00e4014149501003414680c581e40103442281e400b103040141100e090041507401101221b04001540c1103a0002c3e009500103083d40c15a101d0181c911151a1a01c0d01e03800c44240d001082c021444904070041c610707141d0035014806007a0410040d0800008090007540e400b034800402090406052800c00c490031002105a20802914450b944030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 63165749 1250 63164499 63164533
    0x4080703061505030c03030a030b190308030a0b03030a14210c0703030606090e010905090a210e040903090b070503192006010e06040c090810020a110706090303080603 73
    0x401144981404a1040140c1da0300c2d940002c2c9a600060098200c98101c40940d0b60100803110909060704001130321140d12000b00c0d0f6104a032070011a00000f2209011043c0002000514400c003070051090000750b464405260f00c03801152182404901c8024141c034012030b850f07001e4540d10142d10942c091130307131030a50741e180302080680d00102c5109000440c4028558503019081c0a41994203203010f04500d04421803500582c14030925041c83c1d55100840ca5582c000c0c428010315a402c0000c640580466011078000081000c40500200311020207071134041c10715009583e071082d01904c450720050310301075115085500002044482c0e00081005505103805100c002c902400705a40b41c070b204a030300e002040d2503414180410409548450010800c04d204e625509621400c04d036400700e03440f2454030f0143c0745841150004030082c0510407007100742a0143e80a44503008460b5100c54292030740e2902603031501c2060054100042180d6030a10102c0d0081e035180f034014002804a80c860603080484103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 63166999 1250 63165749 63165763
    0xb0d0b041212051608040303020c060712060906030812090f06010803040509070e0f0103020c0c061b01060b03040f0f021c030207080105060f0d020f040212010f0e07110613080408 78
    0x250158450205030031003660007030400010030208441004030f810201504000c442c0c1c004e6000c0100300303225001030704040c07107901079480800c04001103d54a003016103010b0b00000400708110700940c40c01600045038004c900502003100c4e0002281741c900601601600b603651002400346000344140d110303280c00312800304480350003000d00401564a0340e08040800c0950300001d0241d00402420b2a80d81610b90740d02c100c04020b00e0024200140d40c0c60503003810a041c4641d0a10381741d440b200110b0f02211060b000e4600801c0c0f0750b007c80c0200003083d124401ca59036408250b0b8003400302100035809100241c1c01492582c080342c00101201e600400050248004814509040b001030300990410400c825090040c540c01c46802c41c1c0080d01c011203400072440c109415031000e8030500400c103548020f0307100d5a04903440b800d11a201d40032290303190b1a500d2000e1210344252030891082c6000260610b03c107002c031000c9010100702604558540048185042048481c03d8406000070080003c214100304404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 63168249 1250 63166999 63167003
    0x40e0708010306110306090f040204060902040f09060b0403080304140a080c01020c0c100f120b0301240603150504020a1101021b07120302060403050c100603080903060a090c090b0d0b04 81
    0x4036032a605500c0c15000740ca44000124a0900f024010300005984882c03140e42c0c003440b10284000b1683d02d500028000c0c1540380e001d0181c4900c00140840e8030042c803007604c82910b5540000b88403860341d860000d81207101701d101c0078040c4401400803070005006088440c944030380e100221840203c0310b84484000313502800044c041c6030340c001500d130003130081441400c00c4010b08a4003680b0a2408040103803464401d00d80080410980c82e0161000300714940c00500c207008041c00030007403c080740c104211000079400340520440c1c0007103400907100d440380c0550100c034000c0c3e406211205141c002804040d403c401420030a0048210341452105002d10141400510740070341a5003811030210590304050f41c2d604a00991507140020b540440e030002146078202d50b151a010b030380c1d05400c1b141e450822032000d0220b80800d007400ca0000c28010400050700c4680000c0303081c3c07180c545031140c1d00e1048901150008081100c65441086039611950086a01150290030680040d403261b8a5602d070030703012601 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 63169499 1250 63168249 63168257
    0x1060504030201180b1801260702070e060109150c0512040f09090515060109170709110307120c0e130c020c09070801140d0501090b060418030c020409020105040e07 72
    0xc1040d580d00149074200e41503180702c074a0342c541c2000800c1c580c520406c640d6084954080706414401c1e40b064400f0041c0c1e94068405014a801100b22884103407410f03205000184103008011030703550600c41072203000300d005858001d100e51820810f0003500c903801600c0018031807404d00718000315100b8007190440c2c0f9203e000c0681d4a900307001030b02e1000d1110380c1090024901e020a0440000e0700001d95000d07201010000f11203a6440350f0048030051031a82050301520740300186503400c5c1c1d0000840314160707104240284170301c1d01e003603685100706d002c2183e0003c0010120480a055108035a01800a0130441e1411007551481c01c03002ca481040d48200385e0a909540d841c8445419030306005005003814200c8528080f400c0c0480004c21508045c0034208428131880903c42c200e55903400b000c0300d0207078414024019004141003c1c0700d10b15045414901483c101150035000c0100d800c54440381e680d05032600c0c5600c007990f80074400280002081203061105c100300c042494016514003520548a03991 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 63170749 1250 63169499 63169507
    0xe0f0f060904062a11030c07052107090209040f0e06061509220e030403170d0f0e01050402040b010206070f050c070906081c05030408090111010b100314010503030408120a050909010605 81
    0x84000d200d02c40d99541c010a40d04203000c7d2101854000c03032130004954089401e0440000398080d5104100e8500140e0210351280b40c0c0000384075200c54004d4143d0403c112010440c1a1038540310f5010784280b400c55030310381c1d00320500044123440c3c460424230414609220071410444490081a4040341c10303540c680d03441180740c411000b03000950080d40043c0c000800914109071443d83d0302400c62041c0da4020b00302607004a151100030660368007107000c074145580d040c8106441a41031900810007694164000d60070000385402d19400050b5090081c00150b0f00d80361034149490045995810800f0703800403c0c0200da00000d850748c010701941c0041c00c188800f80120200c1e03001c0d031001d0403440d00340300818840d00b80204000f00c0c1422043c3e8a5454080c03c20b1240c0d20030701c1940c5401000303414110355001c03151035003035103c1c00d60603405040e2000684020b1083d0703988810030950350b07000d40d1086a816601150350101280f030188094020b007d442d0610a083c215183c0003d038201100340c0013080014070101d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 63171999 1250 63170749 63170831
    0x201121d0a02040e010e0d0f020f06040809100903020603060d060b0a0803120a09030504030303020a020102120a05070e0f0303030105010309020d0f1110030903021c110a0c0e0f0f06090406 82
    0xc801c440f507030864113000300508018850400e44a07405d09500e41c045c0104840c0091002d07000344043c00b0b1103c000720276034545103498a072200c90368100c003480c2030180880d07049a00c0141c0c0079403203450030f407a00207000034110781e2110200034111180714400c070341c0301e522011002c54503140c880e554000703811410042c42d101d400750b040001c41000018100c030004c1d82044100710100c0d410100703c40c01c3c1d941619025940c1d102c4081c00ba406842000303610440240c82c842081100003043e4400b502410666456141d04000f442c10805102e4800c40420303803603041080100800e60299024600d49880a406c1c0700d001e01050f00e0304558110f40c50000d840641d0b50054040d15031a0804009420070400c0c207041054401c9078500079070380d00480e090202c002c0c3c540d80b40000d00d54000c80038a54550042c008843e0102031501d058500748025201c0c0d0140f1342011000318104100c255000c92080c0c0b80f410000466039510010852201c0000d071080c3d0300d25a494100015241511000042c00c0340440c44040240e0450 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 63173249 1250 63171999 63172001
    0x10b0319120804170d140907080105010b0f030c03040606240801050d03020607030b03030f04030c050405010b04030f0b060f090f0702070b18040b0402090d120905060304020105070201121d0a0204 85
    0x2a01c07607081007002001c104000154040c40314168114034078801e64590301058900d000a044443d102030f051828001080000480086c1420580391518001c2c00f45036078807100ca54407405910404d8041c01e07002d01c00640722801050295520900400300490701c42c1e40d1354908907404152a003407511036003075501031641c1a034006194a00400b0182d514500034030040c0c80082d1a244003134000b208140c0c1382c0c28441c5d400e0741c0410940d8220409030b405683c0e00c60740ca01e86042100d0051181500860515000040440c89035003030307604407a00004001c070a100e0b80da03591400d081004140c84e502c8400008640042c1d05c03401020380c0f041000041c07035001400d2082010b460301c109a88024105035040180c0d440e034280c44d802014890000f234402241403441c0d039002901078050044200e03084003001c011082441b01d00c0c410764114807101d031507808031143c880c2c0500c40103100071180a80403c60401607500154800c50007011211640000000c01e0503001c4100b081051040a5150003981302c2d2404030103500e01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 63174499 1250 63173249 63173273
    0x6060a140d14010f0807051804020102010b10020f0c03030414060703090306060e0402030c090603030406030c020f0102130e090705090402100302090d0b0a0b01081006051c05010612060e091509010b0319 88
    0x4110006c203155440c00c400513582e100c1d04500000d5281c0300001083c11a4000d41040003403007401007407140e600500e044000d54950740326154003651312610061480c02d080200840b420303210142e0340b88548036207103030910842c0d0340a114100c00b000354005002020408500c589400f512005004030740900346070040524020b890361016202d0b03840b40050007103c0d0740020440302102e98608000c200740015120580c1800c0b10305d2002412175000188400c05a00b50b0030070340c4c00717590381c01140d0542c41c0c1f5950800c40c1c0d6034085004161300b120511000c50050300e4500e0010f1050021481c002d46400c401c3c43c046005c1c000458404c0342c100c200c1e40305001b040c5400d0b004a00d0750784802c0c41c280d05903250851701c05800154600c0f0b141b00740180040d11040030000c40040e294181c1174a003062010f56941c0a00903c22229180d502516500d40f0401050000c0550a014002c00110300240010002405c11518180c0040c0c000440d81d9070f100441126602c040c0240319940304044203100e00101c250a001494003d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 63175749 1250 63174499 63174509
    0xf030103230d09090e0708150609010b0406050a0302090609030a0f050d050f040302060f0f07030c020108010909050606010e060d06060c0212010b0d140a0c03050303100e06060a140d14010f 82
    0x1c0251000c942c2640603005070304032045078001050074030321820040d00b82100c0740c006981c1409482c0b00320049856060b407480c0a01c10560307001d043c2e030b80d803522070000034065401200c001075803c0001c2203500b4807d0300540410080184494903101c2c41e41c1c0003d00d03001014804035842061101c6020500c01e0910510130a000e05003846450b1910304040c0c41030a01c01c50200a11400011031224081409002502e0103035070549042a51507026050141c0807004150049000820710000072422602d42d025040c0655480b40040c061500c88000544445005150041e0005030502901158034000e0086600034a019200d040d40d60301703039006100721004519103411607a07051021508907500e0304954018080c0d0065524520380c070300040380c98200002c20b00c0c003030301c849103c140201c140320000c40214024961001c00d509500d9541c0d6400c100110120b403540d82c442401e12040c0c0700385004450071001c4400c04094185428440300914003219038044c107002d030b401e04010060005031401e04224020346 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 63176999 1250 63175749 63175753
    0x106021c020606030c12100213080606011b11030a080d0b0f030f03220b12191401060e03030c01020301060309021005031909081c02210f070c05030f03010323 69
    0x40f4045002c02d035603420401510380101140c01721340003164418001c2008803490784000755a5210f004158140503d810300809a160264a02146856020f600c0302001d1300c030401c0100c10969501d465030f01561210902d8507415028417840c43c00001c031900e000b40303a0703040034110000e200c80c018003d01c4000c0c2d0010100c10b0080d8482e0f00030028140e400003d80e0828091135034402900c03240100100c1c0320064640c84603003010340204640b10800c1071222b00c98821000f0342404418801c0c54400d00301540e1841050052075050ba0005024052240200d002c0035040030b81203a140c040c820680703600326031003680128002a41c40c0d051800310b280c6601e8030383c5544041d250181c214145501001100c00080341000125507407455008100704000e004c0d5021008548225990f0103850b00308040070703602001c841c071119541400f110340a04101703402a8080c5002c0943c03210207944250b0160f0341003022400649461100740000100f01242800450181d4407500e924002402e000d00c0c02e08080c4160840c1d0b050903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 63178249 1250 63176999 63177001
    0x8070b03011d220c0504050a0b0d080c1501080606120d09090203040f050a2607080f070302010b030a030207150807050702040c120f09120306060c080a03060e0106021c0206 75
    0x10502c401d5402d440c035010288441402d498038004010049011a102203064103010611802d2000b20880642240d80a860900060740d811310701c01c0858040590340e0f5131101030459600c0c086280803010b0104582c0000444072081546440c00110000c26448008240d128400300300d814180442d100c0c1c154900744000302081340300d4040152847e480350045980c0c1c070340d01000060600640b0000d010b0042e4200069465102c940e06142c07050340b11500703603259840c54040b2400d1b43d85000e01d089851590304040d4480c18101341c5280c0c00302507488044281c045640364000900c85580c140514a40c05120b90020810507181c030040c1c4400c0610502c1000c00d200300301003001016078100d81201e011960454000501c003480c207005884003da0f0703008002400b032070301c010700185d282c1c15444014041d0007561003440d0348034242d80c224103442c110b024401c00202c0722851040000d40702c2c0d014040d52503180c01c010581c00d4407000e00101e050002d82c0504010703400307004591083c450544898208205910180001d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 63179499 1250 63178249 63178259
    0x1080106030b010c02060403110f03070506090103110403060c020304080c040510051c050706121407230f030a0203070e03210c010f0c020307050d090e0a0506010c0f03020708070b0301 80
    0x1000051144038140741d202c0d0245481c030f80c07080c4500c110065005102544490300c0b030820040a0b44206415800350402030529440d038030740040e0000880c1d0008102030b280460300c10046002d84052900e01c812850705110101c0060014004c540c0480704075401162604d240c5140c8c2c40c9804900d15099000d14038240600030780013809000d20302915401c0e141c94001e076034112041070042441c40d0016200f401707440c0c3c0210b4080d5102d030101681c24009030060200c4102814003407410f0005407080d001284498007991040c400c50045158081a25040f4074140f07900c0c02021a0740d0382c41200e6072022194004108240c0d95004600d20030407102c242c00030a84054108a9a0211002e03440e00300c1c4a02c1d80410003d4220703400f50012415152810810310902c0c3c100c0c00040d650343c000a800301c41500640c0d0750007004512032034130074040b2105a08038032296151010803000900001d02202e0400040ca18440c01040c641c24100748024425030007043d14a150101c1c0c00c3c1001d5a980045842000400040007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 63180749 1250 63179499 63179507
    0x501030b01030204020c100525090e01092003040605010504050a0e1b03010204080a050f010c02030c10090c0806070c05120a020303040209090c132703051b0106231e01 73
    0x10540c0d80c192801a0340d854840749241c03074000c9000203800304074240000c00072200c0c22000340390108001c903c424030036844040f27020380300c00e04140244550540e02000400c0100e8150700112031190b110003401c6041d10381422407144a900403941a121a5240c5c0f00401441c1428440c10340d01c8600c2607802c000d11941c0300c0540f03441e001c0c3c00d02580901c0b1960880e21156540c298112002008020104e5000d042030b80340c0217807215440b92021401c3d51a0a004001c2d841c004400c0300c10321100030016000100814070030000170140702805890901c0c2c1c200002c202803074100303c11402201280c452108284143c07405901e4216002c401452540081c0080703030006400006482c3c00690403101d0a0141d9203026545180089034103041e5404605031245a400360301690200d62a184140802c4a9035105440000d07491159004001c000403c10000300810910201b000b83e03c0003280300000c40c82d41d50322011034a00100d8905184541088005011900c0c84d00b01d40340c044a03405001540340a145410003e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 63181999 1250 63180749 63180751
    0x30a0e030c011b0303110904020a0905100509010c0f030504032a060e060405060304060f0501030b07020708060705030a0c030b030f1605102106120b010303020606032e1806020a0f030501030b 83
    0x3c0034546c458005d031204400200c141d400b4610040c0c011500c2c1d1900b40b0009000702c080f841a180104030043d0900d60306489101181c441c4c94060312075403070143e015542c1c218903c020b1301040d010007909010100010b0311850604a801000c010004d801c0e241085400490000713030b6100b0003e100c403c07580b460740303a01c1c1c2506480c11628116646600c90f680d60808001901251102901181c9000004000c02840c0104c6900a10030350b4219000c460300d8a203403507500e40017070321600089581480024162901c82d00401090300c450324000ca41110400086843c00c0180545003485400010104000000001048c0001c1804542948040d90810302c00790a0600200c0406c02ca003c0501242c086810260031a900034004000d000c10310800605001c216000203001c110014003074100480c0352489c000503041c51400e0380c8249002950407440300b4081c0000000c1c244111030703840700302415502180e00c0709007264500940016980c0c40d60325200618119a05c2026014940380800520118224103d45 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 63183249 1250 63181999 63182003
    0x1080f0a03021e010204091107030809070e011203030e0d081906240207030804060e0f030a150c02070e0a050717010303021b2d03010b030d0e1908030a0e030c011b 71
    0x810f00765440c2c2c40b25180a07100b0f40c4c0111030f1041c20700c40b040400b0350b445c1c0001c1c10b01070f00a940700e80264607551030351500c0c2c07a00e6202e603090780f201000043c8542088003c02c0345180b8802d00780011304000c8043ca01e410141703080b803050081040f1100b004103110340d01980c000303640030b0b011003080f030b047c20044200031802d0038a0840380b840c4c031440f168025503802007091101a40d0080b00c1262a5640c03800014204055188440c0c040c540c0489404c1640c100040d0314000d1640c02040c070784550581d079018000501c0071665920852040080c0001c1034a600321409001d0419400c010601d85003404000e410350315141d00394a01003203103400400119902040c145074824603070b41a1412018030500051650480b00d0444006202c400c0c000880481c002209500092040c0c00134001c58004404140e11141030030034000c007003030b90303509038541a140c041108005440c801041d0707215203455003a42d03455034000321206000300c0c550000d002c1e880e1804008840400009181a1409402840c0000241c550203a00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 63184499 1250 63183249 63183283
    0x30c020a0201020a080a09180c0905040903021e030f040801091a0610080403030f0f020c060106050405060906030a02121608100f060e0d200f04020306090f040305070501050f01080f0a0302 82
    0x41c1070617441840b65400914441f24210f0618125003080d40041030b09c031500c40b01180e0441000941400d0500602c1c0300c4a425401601900c0010035805e80c94100316a0520b074140401c01240300c502d0514000b5101529641000050341c42c031914041b905801001184000e48450301c0801c091070b55086108203a1703d51625292807140c80d98503060380941240d04214040300d0030181e0309411002c040c0e018003410481d8004540a03a660740009aa5910440c080d544d0031210030000240c0b5410709070029a0401c66480005207010080c040030100b2001c162112410080c100440200c0035074080951600710b81d841980c00500c61401d4040c915011107885000700748501542101c40c507a07101c070410031845401c589800204c5050102043c10b000038a0013082c440d0148500c42c3c685410300d44252440303054050700703060194580f00301c006d03c000c9006004408200007040100c0020f48280180750040d408101a10b2a0b94102041c031424107030400c000600c540e02c00c0e84c0e2480860307030006080c5d808180d0144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 63185749 1250 63184499 63184507
    0x1050d020403050d080906100501050f0a0c050111040807060302040b0a110109020d0501021c0b0d0b040f140a020109050607021e010504050402220803070c05060a050d090308010501030c020a0201020a08 88
    0x241100181c0580da101078514042d02c003030001501d8201c0c1055201d01c03180000c0d2201d03941e80b01540071081802d402800d000580a205036100416488010703e0800c01c581441038030000c060380c42d90f095400e1518080c60100c3d02040411441c2d008014200192a0900f025030a0030300303003141c0c54814003610100b8001c10040d64045100d0341c0c029482050100e40280a42d50210918240a4040c4d408400303007804810408466a01d024054454084030b072000a00301d22405442e07480d105105580500b0950350900e0006c3d2013000501400000d00310000c886018200781943e50002601800c0183d200c203024a004026000044c0c0d100003582c003c0000c551003d40c0f1090352a00104d415010703a40056400c60310000d000b080c400c2c0444040c0510b00c9100041d070001c1c9807183c0d40c03035460340a905001491304803001e0302030246282c000301030440243c2c40d1801a00b40005080300308150382c101d810550101d510070340107200b1780d41d16000700d00c0340c01c0280c00103147c89941640000d42da407800c20006444218040703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 63186999 1250 63185749 63185767
    0x80313080702090f040c080c0a170705030708010608010c2f0f010c02030306030c0a030b04080c0c04020a031e0510050609030a0210170f0c180a0b1c0506040e07050105 73
    0x1034801c00368020b05070f107610740b60031440d00000c078900340c0e0f00b555012040364001a84003000582c205051002070100d40600c5e01e00301110100c40c0008001011900a600c404940c0e9202081964000e04504e000403405602e001440d60840f0281c807010402c21100002d860003002160200031203804501340b40195880344480303610b0510540d000300340d089500701114041499800800707107006100c00c4054596a280070820410070111a105c014242007541c070000300454101f0b000344c11002103040689010007003610005080740c0c020080040032036540c11038244407101d0140c86043c4c580300103504000d1401d1500d00d1040c2001940318171485440c00040100d4103032010f01c034110500d54080d101202ca02031154014100c0f02d0a189920103400540b0001089541e420401c0c0340100d22035490301d85042c50600307514a48a0030aa0016003080e10f442d800556403810394000e107404141e0903c01094850424100002d13120040d10403417280e41000121042c0c80740100e04001215030900382165210304034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 63188249 1250 63186999 63187013
    0x9060f130b030c070204050a1a130603050a06020403030f0801081207020310020309030c0d0e010e010e0d02030a080c01060b09130b0d08030703020403141c11160f03140307080313 78
    0x40c1d04440040800031090108603c400d0001c1c0480c507108483c140210354940d8002000c844504800c650004449000600a41040100e40c1c40c00c10202801054484c0c072621182d00c0c0a200540454900354001800c1043c10340c0b060148042c90101d14009580d5450000c8181c0d41e402c802e4840054200700098110171950100f02c42010070280e00000e540700c1c60725568440c1c80c0d401c0540c3c0500ca0340900d0313002504031403044080d482e090310161030304404d14a5030001101e41903114464545c0100d010141c1001595003000404410707407040a1003a600c2c1d08000e030803401d4803003a9001d150442c00070300124109a0391610003005401901100007400d450311400108160103540003e4102280002405121360740b40d0014010fa03405407403005d004444074042603568800700f568050340902c11910084165108020500160700c1d004129000c1050f03006040007003201c0c0b9805200d019414030810020850a45600c3c50b250103204080d41c1400e1290b12582c3c5079200040c2446c11541c21210401e0400c050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 63189499 1250 63188249 63188287
    0xc110d03140319051807060521061309060923060406020d02160803040521090d031e021507080106140307020115060309020109050a0605041a0403020909031e09060f 72
    0x61500140300500341005c10461951900c0c08140150090344000300394240100101d0380380c10443d1000d1800562030022200c00c5e0f00703001e002e659000728404811600c0708071901651120b103008800016403040780e0b182050131700702e070041030306d4408240007200c0c8188900440d030740382c1c0650070040c0542e90f8148006090024402d08440301c204d00a040401c00a00003450051841584654100c3e50000c4100141e50011a500d61948208141c10070242256007400d921401d002c40c402d0034200980007c144080c0c0c80ca04880b00c449005038410400c0038000303009688003c0d000070035420511150b50403d5401481e0440c64004040e0300940007011811041c401d600241c00346508400c03004009440d044014060324044000b603000034402500404c0304d28110045100b26100398554500d4140741400c6100540718582040b000682e040c403001001d6100d0005180c403d6416501659803400c01e104841c4140362264240b00702c0d01801e009076019910703082c08036141400b070509510784440524a8a1010240b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 63190749 1250 63189499 63189541
    0x22109061603151203020d030c0201110906070510020301090e1009112205010902090301231308070506010609030506090a03210912030e010e0a050a080318010504030c110d031403 78
    0x141c089082d100340f660201f0030102038404c2d0340d41403001e8200300d01c040b03090740d20104010704103100c100a0001c46140a000610000b4490f005651b000c000500c855001c0781c100341c0c0281d1115031550b00701002d103882401501c4175049442c40070070a841c4035494072080080200d103a58003992004099031008600c403010303d845050b580509110542c1c50b051004065004403003664025824004805404410700100c400310882c0b021010507179558000d0001880c000000d800d440d40802041094007103642400118081d10f003540b203417003059107180f0b05203103880310052098800b5048041c170030001941c01498440c15810b030b464641403124040444400800036000c004020030500c510002c0001c0c0c05812004400804400810440c0c101907140354440e99407140051181d044078000e0400603014a0140d60403940c42e035618640008000c42d59400c442c000d42d030075000b042c07401d805542001020224580350000035900480c2400d410365014140e14600c000810301841c003c8000341141c00c00241d0b25141607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 63191999 1250 63190749 63190769
    0x402060906070506042d1505070c05070f050307050604150f031404050a120203040e0109020c070e010e011e05010c0f061b0e040509120301060f02010f02210906160315 73
    0x41405c1c5000f06c13403065030b180480d0160070f40d443c012103850384408248043e42d800904400e15801d6210002c0d006210007040001071002054500b07005c036008100c0d84000e0b0042c00d918200c05814402058600f045547c07040e48500c4040105000300b800c0230480380002071250801149030024410f09074058103a051f841d0001004000402041c030100245040c0740e00c0c011180d400443c80c1c00b420403030b1a40709034015a84182614001040200c00c207a005025413012002030b500c0c0d160301c6440d454100c1e0b50030b0f401410441481c80c018040c2914072800f240b5956101d181e1034280c00d1030a00041c2c025004a00040e0010b1a07a140500612925030071003000345482c944e40c890786a40d1001301030903545002c0d40300390095240c4000540b0007031000504c0070f0000e03030320030b4002d09584ca4144200c2c0c41558840c0308008554036042c0a079091a602c0c00540346035205070414400d10080c04690050112009140070381550141081c440d2069100c030b40446c8030340741440c020a8501c1034a508030329000c0c040d07200100303071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 63193249 1250 63191999 63192001
    0x5040e060402090a0c091406040b0403030f0801060f0e090711120c10050105010801030b04080408030a110d030c080a0902120706080603100e030306061b010507051306080f0402060906070506 83
    0x4200045080e80c4294421110301030342d5212100d44c80100c6140520401c045041e040c42846800307040c80c1d40c4c600c0ea400003003805280c02c0d00c510382d00b5003640166000300c000c40c1281200c1450690060704540c05020140782c50309e000b040c1c2e803800a2402c0507003c1190b00800400f4041403d0301c0c803840740b41c100c40391220200c400c090241019403080e940700d5211180c0310b002e030b01c0e48811941440d00900c0d0403924141d4a0303440c40d90175511040c8a0200280044032070103010040029240c0051016090580d09925043d69984000c041c0354240402d000005040500d06512100d4041e00b0101c95a00500103a000081c03050305403010420340450401c55070400d2050303060004e0801d1384410400d106560950940b1800d8a03a8402030040c0d60b040c1000f0f15003900148001809800d01602520706581c55080c0c01c24420400c0131124210348058541600062000400c2c004951480103214020035552505503454908880c580544003000b030b200902c603d400040782d40d0350350307515802c0e04c0c5001d03005400d480503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 63194499 1250 63193249 63193271
    0x8062215060e10030b13020901180806010f060f020d0e040209090c031b03011a0901051605150c04060206010b0702030c0a18060509011203030b041d060a060905010b0f07020a0504 78
    0xa0b2000064110703210b400481030b0603504500c02c0c040c2c168200009031401103098036580e2040082d4000410700c0d410002c80c901140c0c5104c6082ea00180100502070140805504215100c02090f42c140c10901c1403028511309085160750005000c12015002e14211000c4102d9100190280c0f1450416940c001c0b45502403002151980004501a02e840400c0350185030380045007040c01e000c2441800f00d8041d04c4552014101490801420702d0b640516003070b8507041c0d50b00d0910000c0c59012000303440742e60008503503040c2c030b1071030858140d0411010b604550030a881c1c0100255110320502a907900184007240707084c2152410002061a0740c0010002c40d400340e120031801c0ca0b41c05486850008103800c00000196604145581c3c0c1c0c1600d207010494400c4a0780c648082c1d0241c00910209a0055581d0280c4810307114041e52a0034024054000b400c02030501c010b0103c25140e076904211080e502e054010860210440c0446200341c074030013a403644489081c00020240f911a511403504181000b0036214 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 63195749 1250 63194499 63194507
    0x3030d0209030c01020c01120903210504050f010204050a2d06180b090603040206070203070b0d09060525140c010203010b070b07020106031104181a0105010f0806221506 74
    0x90740030701502101c00b00d100b0072004a0340c800c648109103020071018441c908401c1c45607000800d2450090900082c145c980201440c540c05051f0742854000e07640740c00340000c210f000d0000340d1850501c0b00c001e605103410500005d034510800d01c6a80c04c40d000d010380c80d0040c0455000b0108080d550500f0700441555515405802000c1c510024000b00c81c5011000c01c0014103101502c1c00389002800084c1559516420b00c0301aa002c0300f0180d030f141c4241034000510f400e40740c00405c1444078102010a4018003403900d1015104050604107440c2c1b1086658100e20040303800c5000d480d04146480c28140084036920720755845103564003240ca5000000124010206100a0810611a144412a650b10305004900701c031a24080100410b050b90100c0b04e0307916003608807075008085d005154a041100b89d0300c1105003400f003400d090394441c08000401856812460752030308010103042080c61403618030005008440c00703013458018540d00c41c0c1c4600c0d01400a0713010115419081c906181e80c6a180e00c00a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 63196999 1250 63195749 63195757
    0xf200607020708010203040308061e030f03180603150d080415090302090c0901081513050406060807050d050d0c14030d0504120e010e09061804080309061b0702010e03070503030d02 79
    0x40140c800c0b1040051402014402c0700e120795010398529800d51a940e04000105034259025500f452402400c0107041e078051103100e50f40314140300150b65845400441c0c80c440810711180f18860107041c810802d0300c06080884140e00801250b0101a14020f13140401d01d0740620b8102c0e044602442d80d25007591900900300a040d03078001c07150721404c1d075910b0304041b0484c07003180381141c00103a1040100755496101c010482c164140106610b95043c54600c880c011250111000c0d07482a4403400104070030b84083c80b81e0000b03004c00703035640c000840c9240c58840d650000e40050300100003a26103c02c040c8010030b240b00c5101c0d02c40e90292981c80010008038000b80000356804e681e202c541c401c02008050044405060440703040c0c4511800d00d0070a000c00c18041e200a01041d000700503e080000c0100443c0011445a80f0422505403a803e0040303a041c03806500801c691000b003800000e20801c3c04250094828407a42403a00812803140030f0042828180305501064051002144503c280c00168000d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 63198249 1250 63196999 63197011
    0x201060503010b0a03050a030e01030e0d120c050c0714030c1c03020f010e070302040207050102161506050609010507080304020f0316090b1903030f03110f070b06090c0a0f2006 77
    0x910a44501200b005900c003210b05c001895a4024030048001a002e01062403e01805042c0003413036003103000b1518140b19036403048200182148884400d804c4031707407203181c58250030384c5000790512801e034001c41c0d5551518041c12000c08000480381c0d580c2d54003002000c0c000140601011205684c1201c4a20004110314088001d4000c0345d400901f06141440b40b1034a52200f09c0082019500d19002d100084d4403240c1e05503007654007000920150744540a40e1a105841a6616421002c69003005c8045950540002e8400c020401c03000240703a901c0002e88251980200b041a1740ba03ca6100048000900c0f0b0341984d054001c540d04460311001d5401140200c44092100707000ba004090704000317140110390718001f084011360f0024070210344540c00002d000485402d00140c0443c040d0205640368114800c0d1080d2624000350030000c010444480c40c2d00101d0599114101d4204607034160902d0155900d081c0030481c80044a43c040303031080044411080780545607441401440040c19190a4101c039a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 63199499 1250 63198249 63198251
    0x204091101030f050402100c030e04090b0601020f060105090406110d05150f0402030f0703091b08030403060c05030615131a0403020a06170103060902010507021002060f070c0305070605060a1203020106050301 91
    0x885190f2074075014042c07080b58002c0410703441024419054860803160101502005000d104816680e2101d2080c40c402d54007402010020340b400c6c0c80024500320620300c43c0015600705500411545c0c42da401c403250400c0e0321880100b040404407120300500d0040c9428500200d040805001e4203c46807a003181c82100d05032141d42c201c80b00c0c00280002d9202c02d03121040c5840200c000117802c02d20a5122000c3ca91180c0382e000d1144000b00310040303880005e6008018580c100250420421a9030302c120160380455007016402d528001300050040314a41400071000f90001582c0141c00f03001c1c03001d42c4094101c10000c0a404000078690318503e03005400f0807800780d5241c10b40482c01e03c0c000d0a5051a004407905010301c107a081d0b0b034449000c0c01684c00120306128040c821040145e90780c1c0402d0740c0307101040e402420076140540700c00d43d04000c041d000c8014450604265400310703500c44100c43c0380700d030026000309040c2c503514040340102c181c035400701c0300e4100100010300c04c059040d08010115001140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 63200749 1250 63199499 63199511
    0x70c050d090519050904020405040f1a19050910051f0b0408060a140112060f0507030e01050105010e030703060b060f0f0406091a0301030b15060c0a0b13170f07020409110103 76
    0xf00074019410b0783c01001d034400b00d6440014010300e040e41010342c1c0b007407040d26210f49007440356598803c4a20a110b0440c40006032034108071298001814003908201401002d12841c101580f106032600c0e125440da0b04041d4640300043d190400f0f45142840841c0d004018040c1c440c2e80e000c0c214810b40040c01180d0311401510701160100c0750314002d2400051620030411802d074070703001c5020764034901e00804803401c40d268007034044120703c6441564405c540a460103c0c0c0c5c1042c1824590840b070b4140c00c004d06122625a809000340c0340054042e080c0c1340d0000700068081900c00010b401e50141c0f000b90480c03550700040c0251840c9018000d00300302c0710315456254655403076520b8501c03420300661580b4a560000d100420108102003901500165041d21030302044a0000c0425041d600c51284d0202c0c50303005080100410201000700707588640c070b440503025002882e0781c7e003480307020402e400d1000030031020607029003240015044804c0250b00138005c00c140581c525000010070031100030f203070210745040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 63201999 1250 63200749 63200779
    0x30b0901060c0c17030a110a0204050a050603100501030b160c02060a030204060212090102030715021216020705030c060910090b07060b01031d0d0f03061d01090c2303070c050d0905 79
    0x746002c0041003444c007840c1001d900c241e003111400c0780030b400c030341d0320707200b102035400c090385076849010f00074a03491101180610700341d018146003070903140a4a106d00c0c1740500400101d010003010035040702c041502e02c3c0c1c4540c0c0380c48049560000d05074000c2c0d8841c40004200c600703990198000c3c805c5405940135140311000706110350419006503c11140507800030802580081c04d200100e140c4880d904400500f070103040c07410182e00c43e4003281c074940e000200985031007101d44c04026880c010481200204252034950010810358000c00b00d64900461015148003040f50150b078400010b4107400a1050301c0d840c180c14018040c0000706500f6020034900491602401010901d101c01212003500078042140c00c0d08046030185004801e1100b050780e00d2001080e10802d030b40041c0b8542007844015074180d41003c41c58021a40c1c03820000c41485581c4000240c0450ba21101c150b080e200103551584a03550070406940101c100360000340745008010003890402e4000c0951000d4038800e940f40030840d208a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 63203249 1250 63201999 63202019
    0xc06010e0408030705030a060e04030314010909020a0510030b0d0302160f0605071b0803070b01080d0302040f061d1804030e012a050a06020f03070305060303040b07080a030b0901060c0c 81
    0x10780c1c0c09007400c1420000030701524019001560819661000000d1107a41c0300c01c107160720b4030152021400a612079040043d1040c03131050303860242c096641d040020103480e900082d075080301032060b20301481c00b0781040443c190081c4c0c0440d10100002d44040290082c5143c003c1d141c1f4200c4003484100c0ea040140850929000f162400c2600e400b5120b07039107000080d454011000c00541040307035010000000204020000f0300151880c1c03031040d10800b119504101d14142401d85000e044401c01d44103100c1000034000740c1445208640d0a41098080460b0241c000d0300c07030030300810b038041d04403031020200090300350b8480b1200d104a010b61346008070a102c03400112682d4407841020300543d9450003500c4211403404d000051003500c1402198206010742d5148002d90300101c01c000001d00300131007040700d03198050080726448070048028601c0c0606110f04002180600c6002134021000468866134541c0203911031174020303400030141d103950f42c0c1d1070b50024030400804008841d01e440d8003100080304209 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 63204499 1250 63203249 63203251
    0x708070807080603120406090303030e030307050912160308041d07050d0b120706081801060612020d0b1306140a0806070806190b032e0915050301110c06010e 69
    0x15903521000141c44001c1d0807180e865002d060b69906000c1c411841e1000040348004100414650300ea00c01c4d11491814054101d8258000703120310b030307001002000304032070f403080495142c0c50046031a682080192455170303203044041450540c410484a1000c000e1140362800761040f0780600100c14400005040c6120702024203070b0708a008220107100d5030032000c40640002c3c0440720007400c40301076428405142860302d1443d40c800c83c04940c1d0381007806031902640905000d400c0c4910000c2c04010301c3e00c80b00411b44005070300e00e84070003075002c01c4a0400d0b10700c50300859082c00707004080a0880d40030001002c01081c00d0300c02d45044100044842c01c00d0f0801c4c0000408458408010b0300c16a0b171051403e9491920080c4019444807400e41d0301c0c0d8075503c0d8050440080d04000300d0b00c2d902c07450100c1062400d1600d440c0007152403480c080d80064248281d0b150403041d40c04105001c10640440c3c0d03a1801e9140c06134010a0345942001a4a180b000e01c0f180940014218901100c2880c0da80e6611211400c1c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 63205749 1250 63204499 63204511
    0x510050703020a0905060c03070219030308090f030d05180a03020f25090b010c0519020306011a031b0c0a0f0b0a05090304090b1c12020607020309030c01030b0f0a0608010305060708 79
    0x8590b204200760315002e4090f0140c7c020a4041d20b1620f40140c0c0021101000d080c0c1143c00b540002200340241035008000a502c619090000c2c13490112202e486907490148100c280070031900c441c00181d0350303041c074a401e20107096803404840304107402c0d12b00070b9244c10001c0401042403044454103030400300d0403291040c014544600034040281000310020141c98800051810f010349544000b0004004011520990422841c0d10707506c5132461041505020040c0e102000a10183c1c070382c9000c00201404980d0005609441842c4203800104801968012501154024052100260244401d00a12003034051046e005442d83c0c0d6070703580024084030010b840c03d041f554020301092000c080144d00102e4500401448a00c0a103500300210720040b888420440c1e0343c6600c44010b0348820b40400915401c9010341c0044e5041051280100c0c4d540c00c0310041d040c0c10103444585a0407240c072564072404961a0140c40190341c1a01c689024280000a200c2159507201d1540001c0c1141e22410590380940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 63206999 1250 63205749 63205757
    0x603080c1516120b0411070506010e1e06010309050a050f0309040e011b120902041d010b040b030606151309050601020f03030106080f2d100509090d05030705040801020301030510050703020a 83
    0x118401c4020010070b24244c03140c0c3c1059a64a00146100c00003007d481c080d84614028070066050400d2180c840e0301c00b400310f002a007030004060312a241c50b4040385030b200c642843c0005000001e030409520300000504c0c05006030158000204005c2000710081c003200760150380038004004c008a80070b0803038003210040030382d800c180c10059600c40d00c12600500c01c140050400710f52043c2c660002030844041009800c1c54904c002c405198108007801400d44210b0100c0b000c100c445500d9000c00d4070761714028030741d41c8201102c2d40c010000030021030940f0b48a1036004c0b07500c9001503c5214080041805544080c09880380c800491000d240c00411a4140c03075990761110616254424050380310391010f015010440842008000c14864a0700108203842d99498400c415007420076404014609a40001d070042d2100f004002d45400f001458544035401840d00070f642c1e903125441200c550065030890003c0e940004000018064001024941c2020204080005491f40c071800d404a101d04440c0b00081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 63208249 1250 63206999 63207017
    0x9070e1c05031b1002120406050117060106031d0303040b011d01030314030c0408010f1e0e03090d02010504030c08060402010212040e0a200a0801030506060103180b06040603080c1516 80
    0x11050f0000705407503d40021007140c02c9440c0074280c0009076000f044100301000000340800003408164081e840c0103040e58a01d0b41e844034881c0b0b18803619820705010380024180c90380300c006031600e0303450a080b090000b40c00c00d40c1d480b41018a0701d5a00c0c10000c3c03040700e05c2c1c5a0071080c0c0080906250120038101c9515486402000704000188034003504010038803682d80e01c0c14000001c480f207081c002c00708108400500001c0c80d00000c46607000e806500ca450524091901c0b9200740d04030740000464440203001c90701100080b8062004807601d1145401c001c0ca22041480d0000301c0f02c000098450103103200b41c0a0300d601d602c0e03140400301d045c021032007030400c0c9080ca507000c21107503001c0e9440320005031810480d07d86c1842c0340c07443c492181d502c085003031400109040010001e000701070100c0d6802440928082c41198000000101c421241c40701c0a00988050400f207945a078a40c2c3c811801554007440032602c03040c80f11a150748403002c0d03000c90307032079600f00c40009002035a26002c144101d500d2a01d0700320316 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 63209499 1250 63208249 63208267
    0xc0a031b020a031101030e0c010504180e160e0c0304030f0c030306150908010e07050603010b030a09060603030e090928050c09100302010f020604080d02071109070e1c0503 75
    0x1503600c0e19440c851041451129000c0940c41d0030707040c6400345000341c41000f11aa030039000102290100701c040280d41e008075500001681e4080d04960854851100e458140901e00380741100400160300751710328a119a4841c01925220145054200d030706216403842c039940e0781c2010450b148812100100024985081c0103012401004501d040c02c1c001c0c0360000310143c440f1188940b0a41500c0280d01181d803000c0d0400c031408090060544454401c0080d145c9986000045000c0703000600591518105c08000190717617030120351140300d150782c012205002055980c00c0152200a60220040c02004403500107888100b00060701d503001d08c48686a1103d05410108148071003101d40c1d0200d40500036141c22044030f45e60840018003a181080210103010300d54030000d05881c42c0a01280c05640002d010000810700541c192000202009005030741c0340d0181c40e15104109003064256405124041403080c0d140d40a418440001c2e81503400d03481705002803501045007003890030000e01350352040001d502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 63210749 1250 63209499 63209507
    0x305060a060908031b03070f030327050d0f020f010f0504110d05060412030b0d0809090711030f09040e030a11100207170d09020d0f03020c0607110405070513032001050c0a03 76
    0x30200d04016241032090590320705600c0d01100400381c0c0080d441d0700c6019102258901d6992803180d48bd100c000d0481c800399103850711507075402c504105008460101000303042c001d0001480b1049604001c000000d500c150b564000c0c0019a019030f0701804201000d100c5050100f01614216040300090840b0750f62070351000131a1803108204c070101511810805525110380300f1101000e40700706c05194503460304a0902c06480b83c02000801000b6007407003c0034103008040125081416107599040c0c3d00c0c1440c0d000314000e0004802c0000d1640303c0060081d81a503442480d0820301d40b0104140c0f00e03107800c0f07410500c0070703405180030103014005460744c800c100c058100003e25031054046c2d004245080303e500043c20811f00d4200545102240e0000c4008040d03060004801c500021107200703080c98101c0d16020a105444824503000d140c0e61004103030b0035400b03031041e981c5504c2000c00c3d600300b442c1c0724506804100340744511099041507602d00007445601410950f010700c010000184860201524215 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 63211999 1250 63210749 63210787
    0xb040201090503030706060305012a050d020f04080303040507060509010e040b040b030d0c03020105060301050c0703031a06040909020112200f0d09060603021c0209072307030305060a06090803 84
    0x24103108071100001495202030001d803101e540540700010392035145040141c01d40f03551340d010500c042e0600711281480031040140c60040042446e1554030340070300808510080c031880c0d10464025801090000783e000c0c0c0000114400ca100f1016a00780ca50340f1507083d5002e000d225146030100c0c11424890318542456800300c45060001400801d108a4140c0860f08041006a040c5c1c0043c540c07225100c24590240a40d6030000f03006d600802462421141d080d07401e001e48100181010f488107580318804400001c0c0d06214040100166a00c683c1c540c9182c005140c0000e04034081000361021880300d03403061041c0c4500103200d11821025051541c04408284e1211008450024017805042142040e9224010a181c401d1100064550640c010003661064803001c020b040c0c400040c840c00140c0751880c0140e040612814016011a505020100944032400c041e2000c104042126810305900d0740045024007c2580c00c0000d19844400448460b11039000c0c1d240980c0c0200480284030204018030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 63213249 1250 63211999 63212003
    0x41a070e120a0b040c0f0e040b041401021e04061101050c041a1c0212090303160e181e0112081801090504020706150914150307050a0305070f05060906070b04 69
    0x62800300b801c66441450b482d4081d00e003510a441040020b0050b1185100b40401501403070b042090345182030f42c0d13070980d540e000801c01004c5910318884540003082c00d4040d9014544a124841540c2c00414440c80f6260404d101c1c0308001000401100c8100c58180700301401040b43c03640c11b5240a081c0b524540f48551340c0b4020080d1160301304550100ca0015901d4060340b00302000e805660b803081c940781002541d03c054014605900200b05200d2070300c0352103602001c014054205540031410b4540020191f40445c1c00b404040094002009124031040c4020305500001e03d44070080b50f62221050240c403240100010f1a8800820040305800c500010317583c02ca002c14580140e1064682002c01e050b81c020600880c1e81644070782130000f21343c41c08078040000c0c00c0000000c00c851481920010941c0d0009407500b030150b184144010713040e4034140118805800d01520802100e41c1c0c81c9007060780c496541c0320f60250328050740c0300460940303040c0c4222881900d0042010341400490703150300c0350751038002e881 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 63214499 1250 63213249 63213253
    0xb040f05030f0c07060906030b060a0305091006030302061017030406180b0703180501030506011403060303070204150915051806030703060c020307110901050603040b0408090a0e041a070e12 83
    0x18001080c85424001c0c40301003003843c0985103603460500080d1900180d608402c00745400c003a4a1840d90300c48400340c540f01005031802203400c0c5c42d052030107401c0095000340880c89900340a00030052540000d401c0340a011283c010642444d0b507284440c040701c5c202240c05246e500200400c0003010300c9030f100403407150015003407002495030f81c078034052003036000101c00c0700440e0070000c40440c0006d40c1d42e5841d00801c401e080070b0040d441d050300001d140101c0c01c00d80d005010404000f2880c1501d0420980784420b5000d0410003a2124491391584052098407950b481d880c2002d5484819a00d10181d030307070448601402c4c246040c9114011900d070828010b107540d405200303484000011940d00d00035516801284d80103580da50882e401d0232240740f0b0380000307090700408c40503004112940314441141c0d0310542110a4428036212868000c2c01482418082030380070360f00f060007054802810b81040d01503803040311211103a841804d640020f0440448550011070a4407400032101c4c00c01c000f00d91000c404c5241 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 63215749 1250 63214499 63214507
    0x2090102060c0a03020c0601030c030201030f0c0509151303081b071802070218040803070207050a05100318060f020406030605041503060b0d02030307051608031306140702090702060402030d09030b040f0503 90
    0x106c4a481c04000740e00075280c0d1010b2100400965815100d04075080425140500a0440e10413025205105041a40703004888002c564002030049005607000321500c1c41c0f080c40443da49040c0701c0d603560007403140c1c0c003116480d00750305c8481c04a001447c1c8040f100081076441e03040700d211039098002c5d080200140d80000451101103003004051224510a512641100352242042c010091904101d904514018100c0c00414045550340030014100720a0340d00e0080b4410918045903038108003550300082c1254200003500000081c20f4020780280c84960703804200b91b540d940d04204c00d541010180000c40401900e060000c80e00f40e802c5001416001703841d0040120090b408285158401c1d803007035610750411081000c01c000c12440030402045910011410960a81e043d48405039051244000740410b0045075103816400074150360034190000e203c070840349080040691a000b046904a21902405d052481c00074016040030054079042450341689980d241d81d0783d000807428940c140c8180c84188 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 63216999 1250 63215749 63215767
    0x409020a0206070207050307050f06030c090d050706031413020409030e0315150109030b28020408100f050c1b0309030303280212060402090f030706020a03110102090102060c0a0302 79
    0x1000408002140e5030003002e0b586820b282c02130400382c090f000030b40300e82c104450401c41a41c0e1a2901c0342840c0d4112807040d5a41c446a8040c09036100700c90203030ba006003003000740130144031011541030129021910180f1016010414803480c0510807206078400c20450711000d40541829032001c007001d403003400d02c14004081da0340020f1400c1c402c1c01000385070700d8082040042046140c00503e010210a007481d40050741165200306004400030b05c120b00a5001001c0c0055800840310483c000000d14a01150b8032600c0b081101e480f116151040400c0c01c1c1811401c200c840094866a0711923540300c144c01d81011688003e800300406d40c100107402c64031050101c00601d40e000c1c0b00a41c05107041403603602c070f041809414107000560a1004c07003000c91040c400351406d80c000071031480c0e0151003181c0050b500c034141c100040030034850040c0143c00d4421400003040c526000038910070414026281c444070302c030102c1089803e0b84910070f142401070300440007140803400d40780080c1c04084984e007009820600c0300c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 63218249 1250 63216999 63217001
    0x7030207030b0c0c010f05040803041509020a030b010305010510060905040b0102010f0e06010524091005070b0f100b04030503120c161112010b0d0213091e06150e0103020d080409 78
    0x156012403000c1d40001340c130030040380240300e4800c100d42c0860003409246041c3d00c0b00030150000420140c50a00403101c400b0042c2c503a584032900641d4024400b110f550f450b41032004101c039007408102c41542c40d24001c0b44400c005032a40c1021105650f031640c0c00075061400f8040074089044949065648071402000d000c4054028004c94200c207074002c003165850581040040c80045a1001c807a80c04405600680158841101ca041101340c4011165216101085403544034862014043d2241c100c1030129900e0b25482c958007074400c806500a2158407503da0980c0781c4268400207050f9803007044900040f5581110b010341c84505000b03001c0c02d1014a000304020300319241d5040b103d00b41031124480c002e10b03125294072414109d140c02003124108003804a840361501100280c4240c6032074242d018401025040204801e6100344c40700a44ca8400c601e921821311046400ca402e2810440c0300c2c607201201c128000120b40c4000005510740e4a59005d103e84a20388680030764421104100c04100108a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 63219499 1250 63218249 63218251
    0x60a0219180b0a230d0507091208130b07030206010f050102161703090d03050a1713020d060e0a060b090c03040c09051f0305030702040b040513140c101206080601060c03030207030207030b 82
    0x410104d030b42d850041042d4a81200c000a203003030140451340710240580007501058941d515400340d4001d41c2d4103003100012101c3c29081d031244060b150300050b2403003010350100d0038904131281982c90607503880d00d0310010780e2241d040745c155001003c00c1000030484400e0010245105112500549260440c800d011640090032044240d0204030000b4100c90744544c800c2c0d4010613240071003075402540c00c003500380302240068010042e00c82c0285495020038405154004400e02c0c5000c4219484c44d401d81c030780b80c8090601000031501c20010302c2e00103200c401081c3d04072403203142d110850703800c0c0742c0c00d0184c60401484050b201046094a8006e66140d0405000f100400346000d03074011a00c0b00780307038410401581c8085007100c0c09282841d092040500c15102900d003910f912258548004034400328042c58500c40480b82648100005401c28106412400a00c180c121036a01800720326224032810b55142420711400c80080d41454507000441d12950103001450310030f10607990900d580e516800c0280e68 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 63220749 1250 63219499 63219557
    0x7020f0a061d011d0402180402041205010b0402120f0903160b0a1a011b14030d0b0108090d1b02060d0c030c091e03140f060a0219180b0a 60
    0x44010b080401d2510446521649030920700a81c03641030006500100503255080c040c00381da00400c3d586c06c07000c580307180b80d840c480025004544442d507030801d040c14030ba203500f001d440700c3d46000c07488006414580211603036502c00c0700144415451b00c940c09031045400908415281c003052100d805408070030001c8900049c064442c840440c07c083c4a0702084540107600d80c0015080c1c42e07000fa0741a6041040c480d00c2488401041d01c0f0210503090441c03481c25485005c01140c0000912440c608010343d0148820f000d081e41c0e405020354070145000c0d91a403080c0c0c40030022403003200440e460ba05803d198200024800b41c45d007824280599100c2d0f040d9801084900d0119443d0341001da10213a101d0111002000c0c6400f00f00e10364540285003031520781d071502002c0d11599105000c0944038a0403c1360100c101c5543c0c0031074080e80b03413030300802c0c009401c01c940c0380140800d0464405501d52003081c503a1405020600f044402d0b620b84a04900c1c1540071000d00418440e0109903030280c0140720030002000301c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 63221999 1250 63220749 63220757
    0x30c15020f0a0305040f0608090a0602180a03290f040809060d09060e1606051206030703080703020102090f040b0603060d05100c02060103050d03061a07020a090c0e04051b070807020f0a06 82
    0x3030038656a082546e000d070700080c0c10400d000e001c0102e01100080d94860745900260b0041c0d94402071601006181801420303030390000102c21000003040030502c40105031503116041c2c1e40d10303040c1d990251488c03640d041c4c030106549000200464040350102008000e0f041c0003c122519100098145409440b00c200c416a400b0b662020b500890f81024040340d9036440c0030b1081d103282c00d81403000180107030043c0811070300315445070300004045842c100844406150032040745511100d081c580240030f58400d0000602030030200301c0003071031410305020300d5503010401006207056589803424000000d8013a034003a109845000e00c1c1d800000319a2103407800ca88842e50140149604500780586403000c000180000c042c40c114040100800c0d601025014421203107182d070765031b4018000998a402c83d504903c1c00c6900c0c080201c040c25130420810300e81801300b070303409204039038601c3c44010445001c26100c451680c1c0c01c000100c00694141c000b0488540700070010106228000b01095054034285c00480c041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 63223249 1250 63221999 63222007
    0x20d1802030f0313030b060307050303040b0d0f020a0f0f0c080c010617030a090b03070201091506090e07050a0909050708010212250e01080a02090907022401030c15020f0a0305 77
    0x5401c0a20145040b0089540110701e0610f603135000e0b103007000841c84084c10788540074003c1a41a9800d2000700003d26006040340c1e1115207641003243e565000d40e4959098502d0800d0040071070203a40295001803580d901c451552100300681603414229003a958000c00c000c010b0700400040320000604490003920b400050345504101a154032507804090482c3c850f44203000f1228000d40c400700c0c0c101559000c810940e165281d61101b64054042124000d00e0740c100e050610600a0640e48684120f030303482d44090212031084241d054031030005010b00e0350441d101d0182401480d40540007031a45a108100701c4800560b1200ba141c2280c107c102c00c8080001c280e810300c07003101a223904038031880044035000b8101c0e01228202400d8070406c405007a042c821203800107400d0540359415580181c0000d400c007200307803400c6007009444801e007844107860b00407a20212010461326050040c149c95104840c98182818a500f9428811485000c0011841600c40010312014144a4410300c0c600c00d459058803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 63224499 1250 63223249 63223253
    0x105010f03050f1305120406021506060a0905060913050109020304170a0f080a060305010e2a011d0a050a030602090405011401020607030c020708070e0907080106032301020d18 77
    0x4414940c440c00101400c0c14140f1624400082801c1d401094200301084411030320b2810500b040079004010000d20740115000969640124501551060190f9480140c2e5544170400215018520705400003a0030054103000c2424088010406040000e027000010826081d1613020344600341c100100050300403080c0b000704084002000100303407441e00918205499048024120a5401e20010410540b000400c01c60506a4002c0000c0e50b00700300203014003545100741a03500d2201c401111400190090140c007009104046186040c60580d40c3c0c04e501c00181d00300c0c84545440c40300c41503015880b0b12000485684190541c0002c51042001584600d0010104401c84205034441d404009410340000420780e804103005512100c6800c2c0041d420656182c22403503d007490300002c07d9441485d01c041074003814200c0700361056405004552070503444410031380c01e071002807000030320b40462040c41e048410603201710540400f145034001030400d01e181e030440043e1980c8106c0c0055070b42e040719050003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 63225749 1250 63224499 63224507
    0x40e1c02070504050603150a0f0b0402040303020d0806100906050f1312030f080609040204020705010603080309010b090a0902010c1410090c03030e030c01080a0e011e0e1506030a1502070507030b010501 88
    0x1d03016908171b020f0108480004030540200f0700040c03a00700e6055444607403c20340600c60303008000c56640a0000c6444a03200e00c0c3c0a5600ca400142d004085050000000e1091400d141c2d01c00450540c0c0e40c640040d00e2030401d041c5c9407a0080101c200c0103100030311004d10462400c4072114001d14a40e01010318a020358280a040c000200f41a01d080100384801c12031651501006582c0103a81560010b91310445801d0550050138580c00003001441e000003030220101c4150040700c04840103d81030b4889031107220a0b0000c61b021910000d000c00c114040000104042400b40d200c490201d6040d540c00442000700e95045032a000c1003102c0303281171400184149a80a81030200d07140f02035009041a1a03000c0c0080e000d0b42d0010000c3c3c00b100c0c0c40d000418424142034022000c54900c5208015084102c000f181015046080c6000701c1032040d50007030450300b510100786600501014001d040170107030a0b210503c03841c205074509254907808004080c001541009008025402900e190119506000c0010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 63226999 1250 63225749 63225751
    0x7020f040e01150b12130302031b0102130f080c060a02070e040c03140c0306010b09011715120d0e090402010311031006090801111801090b0706090506010605030411040e1c0207050405 80
    0x1013400800b800380030300142d00ba61403203401032081d031804079602842d46002c074550322800840e83c034000c080030000e022402054010340320fa0b0403003c550042042e118a60040021050710603105994004407003400542032040041260f544980306640341c85860781d4800c010f0100c00e60301100c040c41c640508106100400d07000d003980d0110b41f400350030111780a00c0040d076104810300500000400005080381140e000328012200324824601c040700d2881e01d00b0a01104050320150350303008481e0ba10550a0000c00840c801400305011340790b00060341c40200074884007a0005004905042c0da454055000b45044c00c0610311400c8148820340200b400d180006025070420303448000b641c2e040052070b1030200030b114155213803035405545a400340308081c00100d90146155111001c0c00d10001800403c2c0101a0016040b0900900444040c1d07680c2d020304894900c01110080c110303184070840c80040d440d044c0c0028481a88a00031281c05070b41c0e100e50307101f640c400e43d0200c1001da441031004000d6403d19000d81 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 63228249 1250 63226999 63227009
    0x307050d050c030402030c010e03011b1107061115040c03060f1b0806130203042d060605240313050f0c010912020d0b0c0412060209010e04110a030207020f040e0115 72
    0x280342113052503400b0030b1741c80c00744d40222414000303904045139060320b00b5407100350b401114990b602500c07000d884010b0301065040182e0b403000e0043e50f401040b050701501e038a000d140490b00007408040d200c040a01c51011028100715599000380b0400000310304c130b41c003a0800101c0c0d1203000141c2c4908540514041c0d01c1ca611203001801fa4000c100800351351000200ca510341840d41d0090390700d9541e072070840c0c892000c0c10130000c00d4280080c04da0145240d50340701c14810030b111780d404111494490f4200580e908402c018200d20030240c11105015041e9030f00519046481000400346100881d074400e07090842c1c420185072160321040c1c00880c1e40d0384c03024498009001e9071841e1303202c9040580100e03030310303c2501c1d001170240040c06020680c000030001c00c0358010224209030409505c454940100607600464041f8005451102d0104c105c0c6440e103d10b00200d54044c10b0306240c01542c00055010750000c0c0d8042ea0b0084c98030198810f25100c40c00380c41081a500000001c0314980c00103010aa80341c1a000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 63229499 1250 63228249 63228271
    0xe0705031e0f070302070812010b04170105010b040b0901110a0308061003060806040602031003050a080a110c01090314070f080618030a0f1803060c11060702010905030414150307050d05 81
    0x14000c0d60b441199603a5041480da260140c2d40c0e4500d130420322224840d000d01c9070400724030b510002459882d4200a8000e5401203504001a0080e98000b6070a0355001e0040c1c03003480004000420101ca0701d0340c010561090b060502510b140d8240c0b20031402d10785020b0054021811400401c211072402d15251440c003c0700f41410402141868070b00380e80d414008000904040d030020200340041880c082e2040115808021101e1503a0b20303207082912a04240448004946010403d41c2d40103400305040400b94410783d0740716215442d40e02e46210204209040300313001e00401c4804a0040c02000c14a006000c1010003001d0905003195000841403501280c100700e038100740300b00c0c1c5481d0b07841a5114084009407034040415289103a1491a4075025803000341400c0c80d00c45500807403500030307100001c0740e1480000d030351031a0f40b0024107031309955900c9802452038204010a1140513000d003032030340d28440040c0c0300040d220751807200c0c0700c82c40d4016a078030004a0b8011941070110000c60254a85c000303405a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 63230749 1250 63229499 63229501
    0x20103060909170711030717010f0504110103051504020a020f0607030506130207050715020a060506030d17090c0a0f08060a0216081b03041202010e0312041503060e0705031e 76
    0x480107140c043d61032103610306010000341d0700144860101c184031031000040a0f685095650b425043c8a007401e049002c04550030060404829000c1c1d124440c421030304180900100707074000780114001d010050a0300c88820942c02c10300000e46440c03025007580c00b001e40051120401d5506100c1ca0440e000345644101030921040200d50345540c0c0400585000008004d0707194103152038018100a00341d001985401860b07810548420790010707504180a0103804200440d80300c14041c141c4400030411144007151001e0407a02080c80e01490003980b140c1401d065540d0601c021001902003d410390010312803c5215505020b0301009111094011904610443c0752650480e83c1d60313414214000c0c007404005000c60302030340b010084248103451381169401d480d82c880c2c03a60440c1c1d0701010400c20590025101424542d41414000b8412200015078015903040c54134000c80940c1c00780050f190303081010b0f210300b0300040e031a4503d8605402442a615500d07100d1070600d03403d01d584070740c1032820440050050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 63231999 1250 63230749 63230753
    0x6010b0a200703020d08120f0402040507140306010c0201020114010902041701021e0a0e0a17010612080306041d03040605030612010b0a0504020d020405031207050c010206011d04020d05010e0703020103060909 91
    0x2494000c99a0644405c41c500001c3d0030400f00d6805030120032a40762006c8070400004100c1c805801c1d01c10ba10890b0200b1142e10f60071021502100d42d441d0302c9880c5081000491090741c003420408104074414400072510490807550000e10030300070382c420341c1d240b9004902409100011b660341e8020340a01802103050561107a80803910110840341d0014501000441841644c42201e50504100c270107000074400640e030b607071908110802203010700c0d03182d46860008552940a41c01ca00c1a042d08181010700355100c60b001c00c401404800f007401d481098440301001511801c0c00078200074222a101c454880c54440c043c0002e4009a000c003d160347d00d0081b40e003580ea900e0401d01d43c252081920b00680312400903000d41d001703200f10f411580d8184240b107075500090090f18010030209114200b5540c0d0041c06100590b990242030040d03800f481410314031241129420305195500500080c80544100b00c0b9440c0ca07030844621030000849500402018015540c050042c00002d1410001c2004000115 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 63233249 1250 63231999 63232003
    0x2403011e050901141902031506030405160b0403210201090b0f0603060f1905072001020c07050a1505070f02040c0309171309110409021603030f06120201031d06010b0a20 74
    0xc00c1c0175034005540030000c02c01d081400300d1b41d002580c001400d095500d0400f414101e981360360b486280e07510002217001c04076070005800192011207a001a220316060310100c503401c2510f0201c0310420440d0f6903a00742101098052988034001e94559209505504040045c9814940300130b0a55088100000134400032610704484040f040c0d0740c2510000d003c0c0c448100458117444a44002d0149103030560a80b41091810f50045c19441074210858503420380e00d80510904850b00d00c24211030745050012260340d940100002d00646210302c080c2a140b032141e50000742210044a182e10000b9503d81e444000c121030626060401401c0035003c13420100e00311040245054607000e0305042a40b9090b00c002c0481e541c5007a54080e2105400564490700310005910107481300150940c00241003603101207406c4564400c0d44e0036156200741036a2120311a40065024101c0c03c03914401c13030442c0c180410703480d4030140203260180c200d011545a5440d0040001451406400c611106610006804c04a4542c0c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 63234499 1250 63233249 63233281
    0xc040513111522050f0303070201051e031303020c150412030207030b04050c0307090216021513091d0606090f0702070b030f070908062403011e05090114 67
    0xc44a0079540c600801c0c008a104601e104004200700e0b003010840350400e407001061607011035440c0c00014400380d5a1400c0055074480910100c0c0c25400800012001d54402d6000f0601c51031113140e1601c011074411124020782e401152a03c96007010b100b1120b0030180d0500c541c030702c1000c00316101e60401203404101c3d100c40c4078500c03909100303640c6e8807561020180244924001150403803240d6505107814104113443d1810b149603140b290081c1c40d0301162000041c802d0325029482c046100006c04107990031f000e40d41d030301c0610700211110144203d00c503143c000c41003600502078040c008689001d51010008007030f0303065844a140c0f5080b60003001400d0302c0c0d081405d98030054010f003c400300e41b280001681040c009810007000c2c0c100c004100540100c00d01d16460080c4550f41e2004c5480355903011154440d641038803005900b50090701ba500074210740c1b0040341c0c071926000f000003609480c00940705115000490304007040355102c2c42040710399807007880b60070003040e00140031035200d10388011080b0720969 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 63235749 1250 63234499 63234503
    0xe1003030306090213050f0301060806130309060f090918060e0c030111041202090c0909010f050102070f0605120405011104030302150a060b04033507020a0803040b0a0c0f020306040b090c040513 85
    0x40816013001f4190317000d412103001401020252000d600f495601000032159003071081c0d0214030a038100042c0d880c8108030f541c1d808a0b4956410345083d050010000207440d0a1541c001101c1102c41c040010542c41d120300104080c1503001018070342a0fa10030b140c00d503103280c528085079070010320080141c20148640f90341c22980c111412981e070750300e003203080045000381020306410011100011440c0390400114406a4a00340c08a0340c500340d403503c9500c81c05c2200d00940c0300103002403200c550480b00b400c441c0d9030050301c0b4000103d907840004040302a05e4100d80e2081d0011303440313550340501c140c2d4001c10198020100c2c0c40203100850038280c13020042d104a21005003425282c191000c407050b07002419040700750341c3e0161540d11000282c0842e4441d044648142e2040b102d41e0000204203900104403001c9801d01000701d42050300d0844251420b922004003601e54800d244d205a006075410f02c01d33a445a4030408100795603082c681c200c00d14004003442d01500407890b01051100020301e0b803c0e4040070356 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 63236999 1250 63235749 63235759
    0x60f01030506060706110421020d0f0311160905060a060e10030e030a080717070917030f0a05030106021903020a020f060c0706030b010e01031e05100e100303030609021305 75
    0x10300e0740400f00711244100d0340007403c03035441c0402004501000d0b40007001240c0552481e410380b2040350716540100300004000030350009a02c003a08002520305100c1140950180c2014840c9071f10f11001e40341040084140c52808400c40b00c000d103e4000c2500c40d49804c442d0688440c54000d00f44030f001b903c107030a6035081a10415040000c4103406110b9000342c080548800700ba41c1e01c80303c0c030305000380ca0004191222000b040d030341040c9a00351295003000c9845030546079142e00c20076250616003841c95480c0100402c082c04100642849000e150f0010700c1c090210781d0b506c0303035258503048000b0704001140240041004005e00c60f40003095000030a028025012544070035031100d0000014414030031400149000d00400c4000112a074150703200b00c40300102a2255042d081c01ca8004508444503c1c0341c90340c0d18402c0c0b06400092540b9540f205a0244400c2c058126a907112032040340400b004440640d5441d412141c10705c2016414020300c4000c0c040800194101046402c06503140c0000f8001d450040d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 63238249 1250 63236999 63237001
    0x106081f1104030606030f0c050909060411011101051e06010216150c06050f0f0606040b121302030f030a02010c1b060b01030213030609020f0303041203030218090a15090203060f010305 81
    0x141c2400211402154403103020000907035a80741c10a43d80c1442d9409039a0048140000141d9080a000d060b210b40c400002420301035440d50745042820b152004401d040058007403003142e0843d070900c2a103014107075170080b4902d0300304048000c002600700100041c0c11904400742c1d84001d00040209402920a0010342c6450340003009411030f000045100b01030b002c1c1d400c0c04184450076900d84c402070300030f0240d404001f0300366407070000380074491040e8800c0100100080142054030440c030f440312a0030101c001c400d0038003a040781d00028a0202c130684c00303601c507400014070380344440d40901c103504520741da40c101905440080e95210215001c0280007401c040d445000e090b026078030a0741160b0035103018442130f1800310b489060540081843c0d5400304c5c00362011354011002c1e454004260f50031900050344003941c41d41d1039a0210081c0d0000c2c0160b402031010b0a0500500781e0303a201e00c0e9481901410b40000388079100e420400b00c031801580c40b07030083c0c0e4410800c0c01213946655202c000d0b07424080c2004202c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 63239499 1250 63238249 63238271
    0x8090a060908030702070602010b0f06030a1d060f09070e060607051513060609090b06150903010f050a0c0801030302060112230a0308150f100c120e030106081f 70
    0x1480189100208618940104401007000c102c1c06540691140d5089600154031020160b0882c2d5034400010f60244608212120901e03005c0021603110861060110702410400800302c05441c0c14100c507500382c0c114500304203540081c44c03509070384441c203000282902454038614142200025001c40e018901c00618241405410003c0f013018070709000e01840d1518090543c14141000c080741100e07114200300300098001414054580160f80001c1c0069240e111401040023940000e2840c401c03501c0c0602460f04169401e1145100c03610701c0500c0800c0c1441c00c180c030101100c0340e03040310409101c40c2000501c0801e50000381c1605403a0010300c0d040341000541800900c8007030001d62285000c000c410542c043c5138000c04c94801c0340e4170076200c00459480c0c8198110304000103107280341e0011041c1250f02c1440c41c040042c10075102c0c4504141a0407001500c82017810940c20b00d001c00072403d4a4078200341d605092040300001c04402c00034108900c1400ca03000010105404890306d800e48031103200c0c0b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 63240749 1250 63239499 63239503
    0x170f0a0504030e130b10110706030506030a12090303090e071205090f060103050307031119030e010314150f060a0e0409030e0a030c03050105010b0408100c0504050a03060f110f0a0809 80
    0x60004002c20f40e2001c1c21301d00103840c001c1c0081d620300c075006240d00360286101d10302908000250640b110090401036081c1442200141001800710380d0504c01d5101c000c0204800e030341c0891007200d250b0780c0da20540d401d5080c00383c03904085034003031407419081c9410000c00750f5001e4198540301010b810301080316112009440c2c501741032541c48240500607000004100880000140300862103515045846040400b082e52075103800e40c1180710b0303120040a50b0f0000703480350050202402d41414002003401c180b00f070400e0b001d4070440d1200d00c0019101c0d07440c542441c140e0300b07640c0c0c0031804850441c541011510300410320701c0c9200c1240d0280d929941000b04040c0143c00d15220b07604054444400e9a6481c20300f17803901da50074401601c05528100010070140b8407841140c06903603091004202041d01c594000c0c1c002c2c071081e0292400c001080c4400b08071542c65a90880056014030f101041c460440f4445100b11070240d8240016074504020034204222690141c0380620303994246031113659201c0c41400c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 63241999 1250 63240749 63240767
    0x9031c0206190608070e0610090807061b060513020f150a050702060403060e0307060606020703020603010b0d061e0303090f05091909060906050114010c050303160219050a03170f0a050403 82
    0x3024002c0e8100400c5001040c6c44132442402c017101c2a00d807039620710f002a40c0c0f240b2603010f07180b40c9400c030100500c101c501070710101039030310151000b0040440c026164141110700a070b5690041c01c80000d001015454440404000c0310340858040e540e2103c071039402a203521030405000705005020030741c1e50541d9901402d45000703507003090043c064080c501075426100c0c1c0c0108021201c0fa40b8216002c2002e603c000740b000c064a5001d8082c601e0340c0d003440c10300c2203181c0020143d681070030345904000c210741b1500128600c001d14480c042406072401c610f80989030294541000762841900c4000b040641d646544c12500012130b044c41c0204c25030b810660502a01d8070042c05401d42c1e0500802d41c04020003035014904a4031801034030480865040700440b181003203008050025031003400030401d0f20340f0001e6059000000c81c011280c104011494508801c40140030581b1140c002d1501241410740091001c0241c1c41044030641252801e130072900c41c0c1e0b00c0e000d0280115150b4400004003050b000d0880a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 63243249 1250 63241999 63242009
    0x2030309040c02150903040509010b07050109140c01090b0f1b0a06020a0801240f050c01091b0f05010504080709020a030b060c010c090801230603070e01030809031c02061906 76
    0xb80701c01c02e2020000703555011210381102002c1c81441c00200f40d44c002209507401d49000820328101c69203460f04071000341d0003040c81542c0c40e540e9051048006405a07c02c250150f003a032019041d680050000900882c0180e4403801c4170301c0302000500a18050035080340c1056408551103c504595042c0c5507140600e10500100414800101038207260340169813103040b1a05c00c003551140d980c240401c0700d8803c80341c01001d40400c2140c081259501d01403400b030200e03403520302e00005140c50a07071244541104410b0046000440c291020b000c600e00900102d0081d1100307003041c6190500d407400341e03039444440d441220f40c0b4550104000404c28070036004030f4034902004150a4545000101d001d00800701d60034440e010a940b00400620400e060013000c04a00c02c0c0a0031510140424829a10640c0018455541405181d10111b082250f002219010710f00507200d00d61105001c0d41418901103002492000000e820854000c500e9170020b09150320200c4200012100e0180c0032584000d00010703000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 63244499 1250 63243249 63243251
    0x4140d030906060504020a08070e03120a0804020405011208030a020703140304030509030601091a09040804090903050d2a0f03090203070b0c010501050a03020a0b2b05040201111b0d0203030904 84
    0x40100540e041d045480300c54040d2504204540e40c40d8100000c911075000e1900c00300e445140003554040c0107444000e9070344030240c243c908511148140d800d86501038092880450094800d05c800c0d41450b1041602604a41e031604880642c991241c22060200074009141c45400098140030140b03d45101034604e270403440c4440c1c9a0621341b90261032600145440d500031300c10500002018851400384050720f248025000f40307005008000e000f00c7c030b00018003d403100d003001c000018030344420344100e0107040d000740e8072540c440101c50740400c19030f1a1000990303201d64034406040102030404003000000074075824a0398125641000580203408a410041e62500460704005070602d04200200701d001c10b600020442aa00c0d14100401586180000b0f07400c0070102b10184607180c5614002c05a01004a0180c03600513490500503101c929492001c3c212107448109110465800c941c0d216441c41c29800941020302d0f00b01600500c2d0b01c03503418001c5c45080920302004c150345086c01110300f00000540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 63245749 1250 63244499 63244513
    0xb090604150e040617060906010e060d08040b0a0302041707080316050f0a051e0601080a020603040c0317130b030906041205040305011415030703050606210a05010c080606210414 78
    0x407100c05440002030500c00705026041c00180f07c0040810700750b05890949407500d616481d041305101e9100c1ca55441164401c408000200301e960340540600480340c019900503030b40d6401c1680060702e004103184a100158402d20043c01a94000f0080e22043c040d942c1140c15100c0041c2032981c6006000b48008801d0300a50500605112010074800014100c0480c0080c10600741503442c0c2d6901000d100745002600034101e440c005107810802903410a0050302d2441c8a80d1b126261504d541d5080740c040c2401d4200001c0e00c24444e20692030800040c150340000c4c504600d44140903507201d460040005041c641c8180b0000300f910300ae501900c018640200c02000081c0c170140440d50300c00e03002d9035030384030030211392046524524000620906580c0d01c90040c20480d00c615003488000c030f40120702d00821092010305000c120703904204540046001e40d00104a9041083c0040c4c408080a4400f5002d01d1041002d070500160800302c1c90a0394000c03c01c004207a50315030520b4020329504080000c0c250040e25 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 63246999 1250 63245749 63245759
    0x406020313080d0903020601060f0801030f051f0204030209060901030305070b27030c16081203090307060c1805041b0503060418030804051203011401080a0b09010602160b090604150e0406 82
    0xa4813500c0418441d800f140c4072039032240416540c24450200610011f684800140002102940642d01c074a119004448003140401c82d4951118080101c0a03102540810104250b142c00c191140e081031050390324142035415902e0080151050303580181c100400034000c291106031940100014805c4000c441002c000c1034000c0030348039030103c6100c40540c070900480101c01c0000b9040e22040315035030001082400603200300c2c14a140c100900001a90005108034004940140100c900f080c1c4942d803490301607404441d00f6064020103402190086240441e1440603c03a0b4140c548007040030f905000d6200d030b43d8080017038054080300604026038011800c0c40710401d0303001a20140203e00c038009940b40300d83c1240b030580b02800240304586820540303410408155002d64019900054000400b184003000131021580d528401c0e809000164490803602c0c0e506118103410030083d00c0003064070384c98609440005080350185016114800170480010030501c0c1c0281c1081d004000c0c0500103001156882c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 63248249 1250 63246999 63247001
    0xa030c0905060a050417060105030303070c050705090403110f01050907060c06020405130e0607050307050901030c0c0507030c1a040b0901032a0c20010c1101050d0e030a11150406020313080d 83
    0xa03108006d1008100c454960400d00082031150507120082c00650a564407d00100c43c1440d0440040e10103001e41d0b00c1c08540b980b5800b0f1968401c900a81340d200c000c0c0b031480c99032450401542131422940e407400040c402e06010104001040320140d191494400d05d03a4203025000340b085600550307003c81c1d074842891450145801200c000000402900c150743e03280f200a0300ca5120803180b440009500700251402907009911052a0b018a03207804e100c00c02c00b56541d507142001c03035001601e01c00200d001c03c00806006042d82140c40740c601e50b000e07040c60b141590300307103041c0140c0207102e0603d5100c40d02d810507122410303090044510803024110107061242d81c00f0703101d03540440c410744891000d042112200402e2900020681c10180d40c1c610744010a51503a40c0720042e181b00060402c142042102c842c182c9501072240c21079141070145603545080e036805040d1010072510000c89800c0100000c118550500d1050380c0f05400080c00b51b40d941d11342241d1f01100112203401401e420001c42d43c0703a401005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 63249499 1250 63248249 63248257
    0x90c031615090e0105060d06030501092f01080109020d24080c0607110d03031503110f010201090302100c0c020d1109060603060a061b02040c0c050616050a030c0905060a05 75
    0x6286141081d80202002c440c2e810490182d0029104410010000c80c100b4600805c5222100b000c001410f0791255103050030b403075040711b00ba0b90007007141030b010340030034410000703105c00c040e20403007400381220444006080c00505201e04003031141d0214400c030038034000e500b140040c03500c06209080c002040404450840e211130040000500c180300d4544204c0c1020f42c01c48940b260494840d841036031045080005035030406004408154882d01c00451402100c1c05074001703148034075005141014104140318607418988140307411a810100c44402094010458580340c5d1046503003c2045040000c1c191400e20602a00a4111107800480300030b0080a000c104264441207801712a1505c03080700f0028079020a443c650360100d440e0b94204002c0f400b40b903d40c1c0d9107142d481b44009400800e0b400260480740030f40301220120303035030506040800009000060748540220084001f81e880030f00000c1060040104840070305580315070002c03415022b0a00180103180041403e55a240405001041c0e504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 63250749 1250 63249499 63249509
    0x1180f061b050405060307140c0a0308130803010e0c0c0601060314090a171e040905070f030213030b0a02131410080105060d0510030506070305060f040903080a05090c0316 75
    0x3141002581c446407246001c490300580c02d40c0d03002d043c6070400040190342e500184c01c54045c03201a42904940c5407402c07014242010580300644030100c1103090281c000314000707110400500c90b540031000002c941e40e0035a0706590300c00c6120b4609503102c041186040c0b299402c03005903807181d10f00002f10a58160480710000949482d24103458641f0748100d5075443c146400101041100840d908003e12010090098241c4802e21440b019001400303805c1d51740d21940000c1081c81d180d0341002a8182c20284500d076134903c0e45801c624100709840c03004400251804028411950040840c0700700007590155510b100c0e041000002203a45c13801c0c03d400110107c0d00d4140203c406c59200d490319030042466604886014059a24210302c06003042c008250040036120280c410742c90201c041603041001510404040d01c000900d42454420040c030044075280c15889a41032940c50000a680000e50542100f191400490306443e10f996440c2003100b0320090315014420440b820184482100480d81140c3d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 63251999 1250 63250749 63250751
    0x1005041e020d110604180e06070503130b190f060303020c0a0b1e070b0f070e06091008060303090d0c15050f041a04050409030309020a0501080105010c1401180f06 71
    0x340c030102658510240d10030065408070400b5106404100369030b1071501d0080d00200114a05074a50443c6044d800d00908090036840e541c19108218440400504d9004061420b2250030b41c42c2880036550011400e407002000384a50724041011044881d40725050301c0041a81848031111140841c8000c0c400c07440103a0052055814224003828000c1d06203095601490800740351145120000c0c0200c2c10f0070000911071901008644080351220301c0b158003540300c61009442c0c50174800e01c010482200c040b0094401e40741004816103d581e00510840d04002d1410466119a2403000103411401600640c40e0005c02c440d4503102000b600e1885074040d40c804486808515074030307440c112014081c0c40c01c001820401000184042d000088078111960020f01145281c1500c078000305064880307520b0b0882c042034880018104524020421030080c12080c80c001c4881c2d8034007000200741c0000200054040d00040220000d0b200007908000100306680c0c4c000405819280b03003210f414000c42c0c0c402e40c1c0d91 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 63253249 1250 63251999 63252023
    0x309050a2f010f0203040306051009050910150605030402090402040f060b070203060f0906040b0c04030501020417010f0506091801020d0c170a180605220503090109080102040b04140111100504 84
    0x2d600a44101002c1c05280c0e0083d4141425a81e03080c0040101030314050425090150019600c020360044612070742c244c0020704810b0f6030002c814425100104100030b182d060910041c00b07020351080680e584141c04490800035500d0744d001107401485160265035907a8106500810b0f0748040c10010200c040c809c2d0b04503000ca80d02c002050351030381429140c0c4900380e00000041030104400b0580650406241071082c0d107071036503a80c0c9260890344103600000d01c17500600340c00d1441e40400c1c0320b031005000c080300090100d450303e400094824100140210850300822401042d6004254159448180450000c1005407010310f80504120107890095000580200004464104500500c4000000070311144102c65096a07101c02900c4024040000d600300841410581d803008200b13110307114000c9025555694070907000422100d40c6d9000545143e00400080040c4080e100444049a03000e09002c02c28041d00340040300c0182810b1541d0b2401d02c580c0a4101114016a02850046219600f40048 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 63254499 1250 63253249 63253343
    0x307090609050d0201050a02160e070e03240702070f030503040504051308030105010c020f04050708040b07030c0507060b030a1a010504230703050604110a02011a090c0a0309050a 78
    0x901c4400307000c1c807074011400b401e04500550282c0701801120941d401540c3c6500d0080c0310b00006003c0541c020044548440305003c0c103d41c02c20b1035000303002d10640140c4403000140c0480302d03000500003004e6904a400308000785480e131090201201070032207030750251801556401c04079543d402601076180728a1034140819910000e0114081001d40d00420b1b0604507803801c030065500b03042c03c100c10303a04030b002a40303c000c65540714414144039100f141c442c42000d00305402c1c0b980000b000100400b041c540b0306034130203013000c4c0c101e8151612594800e00c003148000119006c00d040010b403020080c51000360b14200d003d4669070f45441c0e816500155020031000d00e40786440700c0308002c107182c40c80c051030b0b0301350100d50818420303040107901c007501400101d409070b048041c00c0b01c503520101081005075954550ba503c42200001815000c040803515000c042c140344010352018810742e658682810390f80c0d07071003004128003070140c0101c40782c1000c0b400307105080386080314518902e9544c40c0b482c5007610540e4401c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 63255749 1250 63254499 63254507
    0x510030e060408070f080309060a0f0b0a0e040614090a03030c0903020f0613030b0115080f090d110f030d09020f10120b010c0503160c0f0302010f03020a18090203070906 74
    0x24006803800010a0152220740f10320307045074022034050b00e2421042d51018003240030300b0000c600031996080204014606a1002c4003191401c448140c401800c0c800780c1c0310955251040c9106403000d440d90f2480545030791409100030040007010100344d0b4020401c01034403400101755584058020744050102c1c41403440111890001c40c04000d40c4001c001942440c5802c064010341004031002c000f00c0341e42034903134468140c000c0f401d07882443d80e41d451841d1403c08560180c01c46400c03c01e0a10010710a060100380f050302c0341044e83c04001004141003074019404410011000c8001c5082c007035070703a0340e01303d241448090001d0760020b0740510764840703644049080c8003120000b4000700d50ba0342c1d00c91180200006e40603088200e4031038100550a481680450002d10050055030700c0c1030b444444d072406030303d007007503180307907981e00a1607010b88800041015176048944400b0b81c40d018a801a680d440c11803094035001c2510050b01c81d80080241c0108004481d6070082d0300412a0b40c0b140d542c00c07a030b6010304035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 63256999 1250 63255749 63255761
    0x110a20240f0f0106030e030c07030b0a1503230a120503070f05030f0103120e060f0714060103080304060506011b0b0403140f090402070602090613091415010e1c05010501051003 77
    0x8114142c40e00d00400255100b81e00c4101d075000130006407860306201c150540d20340300c0c00f90029152480e0410a001350100b0300c0c0b0490704a042001007500c040703483c54aa61003a000d50103204a0308a0403400d9a0420090a11002e07130b2040e81b00e044015440800c00c0e0003099908100e40187c04140002280a80280210140c80c407038000f0b145450116800c5507075142034044285003180c144901d51190300000e540303c0d005001035a100c0307581c068031160241440040e6224840d818043d580249005202061405040725030241d00124042003a03100c09004a60001c01c0301c0c0d10007811400540400f007082104203205004030f00a585000622158101c940200d21860102c6050004100a5544607042c41d4000c0d2051501442c40181410654008220207500c2b988400c811941100383c244000c030301714800d03425150000e1046210300c1c582a03401c00502c0d2695100a418050440c640245542d2117444111610380d5140504d240850a4500940a00802c0c0141c520074000589003840e210b02c240700da4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 63258249 1250 63256999 63257011
    0x6050403061d0d0e130204090207061503050703080304020d06050108030903070905060d0b0c0c0d09080f03030f0105060702121c030b09040201080103080c01060306021318110a20240f 80
    0x18281d0210f80500584010a42c1501c1c0d1703810181c2100e0410781d03100c5a10190000b8404244090fa5825891070b20000303d550300c01c262604000029010b10109170002410010349521012041d920313121800001c500b5080a10010700580c10000003146c03103000400681603c200a408071a9a645c45111903001c1d0b40702180e4031904507041201e44008501c0c040a00b5811402c195046403034000d5088030281010500016000890341c001010030054400304035071175404030640099410350501c00c11615140d0b006200c0c2c1d91182402203038550556660030b01d042c0c0048112412030b103441c1a44d180d00b07040711103415a00c8010030b20303101c007007040350502210491249074142d64030f1006a0850f40c1e50240c03a01f0207000340989650300d481c00b200041c12031004040c00e034400f4a04e041005d01d008180000d01c00085840303404a806e04010039254002002518480e20701070038407004903072103504c00760701c002004a803201840c4541030802800440e42c4c0302610590301408201c00b0207a60b0716892510443c025504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 63259499 1250 63258249 63258253
    0x20f04320f0d02040204050409050a1709060d0902120115140603010308070f0c0e0a060e0606072004141303110d02032d03040302010b010f030e030f07020a050a06050403061d 76
    0x211000e1418103074250b03030640300410040c103160719803000c00e00f25000e840382100c80350b1042d1030503c01d000705042007032843c080003030260385004c081201041c5907000c2c0314a008103141d252a1030004545e5854050003144580f138000308211402906000d040014a21030600c4000018141007610308017030088074180ca03040300d0f8851a0015540e1000d0742078100d000300f611460034180c03000c643c0c0341d03901140d0b5004540546000c94407604082030002c400401400e0184124ac08000f15000200c03202c62031750b010703040e41030b44440900804011a0150080d20300700b070700001f170050400540c504603403c0400528002c0e6980504075844084290303a6440c180c001501590090105d1101c086080708240d104e00b0707036105403981340b0f004912142020341050301c0031030246c1d45035804d000441d64003a240484031500c40c40e0911017890042c8400c1e4681c82800441d20746110002001004d5403644219500281409000c1da031000d551090001d100d40c10070700040301d085042c42814940400040885003a003410140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 63260749 1250 63259499 63259519
    0xc2b06050f031b0d050715020d0306030b0f0703020c0109031e0c0f0605040314030c0901081005010918060f030506070e010e0603010504021c0516020f070807150201020f0432 76
    0xa24510520091510316034400c0000c0904130000e9824070012004180b2800205001112800064205502803500324205842e02e08100049030079014100e4210104940a00041d282d9071001c802a108080019480e982808801c800301507000103410070308184110764804808844c14200ea01c0d03401d101001c0c0c80c0e4148000d40b4008586e099000903082071103401c0580c400c584000c071220490b00120350392030402c01c0118040341d855802040a030303403040a03a00f0b901d403c1410400003078104196401948032000c00c0070b919040c070340010384c00b00001e02208006900b80b02c2d51b900d01310b0f584003000c4440000107500004000c09550042809188061000b080c070390551b8280810b000080d000010701076201c414442885000700700c1e522410b4001c10103201d85240804072658040c0c948503150080504903440b0190801011501050500036a01140074281181c00140c2c8220b0290198048100044600040000380c40d01c81003000c486018910712000744020321410300d0404070000c0a40c440c0c0203100c02e5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 63261999 1250 63260749 63260773
    0xa0c05070305220902090301050a050105010f0e030c090f011a0304020102150423030c010e0a0206030a050405070305030c1605010f0f03150914010806060603040c0308030c2b06050f03 80
    0xa010f040440d04000c03a404403501c08103882003010342181e001c0e044103a4001000c1000d810280500c561055000c1d40501c155450100001c0060412001390300c2081040b401c805071581d800c0c400108a094001e207402e056041c00400a6100d123030a2054136602c01b0400c0745080c0d80842c51301900c0c030454050700907004c000b0b0b2a14284401010080c41142d440c0411100d5110300104130386e2450b51000c000c40103640b03d09045011908451000500c0d401580c4140e06950040c2e88040c2201d41c41410001c001c281a104c038540180b900149400090090002040460000b07900050809070b91044890720a400ca64907001035542d05a09401003001803280d188681000703000340c01040d4030410b8181080417032907950310780b24100d40c48411845103491340c0300010444024208940754004604503042403450400b91303907240868049110080003c03d004c03000404032400c01050ba20003c8171480052017110004480e1000700c1080c00b4840155403929201040300d08240c28810108080038008052a04a107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 63263249 1250 63261999 63262007
    0x1e0302030403050c240105031f02090301020715021332010e041811150712050906030403030902030601060201020301180b040204092903060c07031b140705090a0c050703 74
    0x601c25800d100c8100045070b00600d04000d0001030302d0000700c0340042080c0c60110440d009006a000503c03a512404c1d004e000c031103007007083c2d54668440f140010b0b601c840060200340a40103095003d4000007a42e01c040c00c000301c050300180040754224000110690b1919510808c2d002102001c07024807210722200741c102c2401003a100c845030414140800c0d4201c424000500381e4407000410120b02200c1080c2c3d130100018813910340440e5000b2506c104501c500304e19410814014618040c20110f030002149045901513800c0781d50a080292a09507a403600707060190203051040012402403194034000261244188242c80c1030741c0d203c510800441c6600d14080024082000e0b207130b0f034002c0e820400003840c80d171144582d0340c07030303540e00c402443c0341e90801414134010383c80b0412100d002e5004070b01009a601c403210f08030381401b58035040041941c410b10070921614a0b8003503008155000c54404030700c000c0000903000d01142e10851b0002842e80d681c28084083d10300490710400401d2052051000207401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 63264499 1250 63263249 63263251
    0x30f040b13021005040801060f050130090807020f090405100e12030f09100209030a02060a0c120207080f030c0a030e0d050312070306060e012a02090906060102010b011e030203 77
    0x8404007100507620140c001501c60082c501c0e4481c04034400180410a20701d0a0290600a121007401000003529040010b0720380c0c402c2d107985180e040840e840f000c2901d0310b20b481070714000d5003940d82001484002c2c9032110301c581c01450141c0c4201c400092010705843d00b00541c2d4420780e03128001c2c010010100032800d02a00070780c10b042006015820030340c031518640b14050762154a504140c00340504200c1a214100648d54402c080340070b0040004c3c1d0240d8400042c2801c1c0340c0d80c1540e016a5881444804440740d0700c03490402003284a0084495154950005010b000e8440900645103800005074040740d4074450380503075a102d60450280c04c00800d003d5010252001d1025140e4078074146255103c1c0e0442e800100285162a03191b0700388200c5551501c41c50f40030317001d903003840c20311505108000381c0300c003208130071896125903102d80d40302020315a400300500d5558042d02c4044a420701000c0c01d030321400b045074564019842e1654400302c0398826400001d02d44014090002580803055040700a540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 63265749 1250 63264499 63264511
    0x501080d090b0c1915050c0705060106050f0904020d06030b0606090d06052508010617070e0d02220902130903050409020a05041a0909010603020307050f0c210d0b0105030f040b 77
    0x119481c120360682140c08a2213128840c01c401410982101511741c1114030103000441414018030070600002c0001414030305580c0e481c07c040d92225904140c940b4140300320140f80380c100d8008940303256200c000b0b400250549220b201c034081c055940001703000c51400303603500e1950302c1124081410b0101c0e5030b5600060700030f503411f02c00c52070340c00d100302013180d03056003080700100042d50340401040855407114050781445021402a00f103400c0c0242c1c0248146507000703140c0e100e0b04500920804544e1000c1c0140072903100305522078080108111500c00408851005034040c14040c0351080944006200e0030341c4540d41500c4042c2010304010083c0025003180400caca040c0601000040b660301420358105c29400b00c511041595419036206000c45100c060340071030300340342c0144280290140c00c1800d4038081a81001da194403040440c14661800362011403142c102e94fd0300034a00c58442d4100004c19030002c1007101070000d0300c580d200441d4070744001c440c000b4602600c40301203000501034485d115008a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 63266999 1250 63265749 63265753
    0x30303090a0f080706050103080703020c010302030c030a1d010e07140409020603190204030209010e0105010f0c02100c02010215012c07020d0e03030d1b0207080a080f030408040905010b09040501080d090b0c 90
    0x610141d4685e011a0001c0c2c01c1901d41e500d02003000010164100f082001e040000c0c40c0c01d5003141407500c1800d41600015051405864880208403c1c3c100c86035246040c03035000c0d20007407000840342101a912030303105020314000c2440003182c2e0b0710103090034060042240c2d40608124610390320305021464030954100c1212510350200b100002599545100602030842c005001c44c2552510700003625910141c0842001e00c010701010b100980c0e203070500c0700e0712121030b42001a40c40c515840103d06181c165005030f9028115040081001d082160403884403900341d030129220600c070318800220040b011150703400140e10184020030301c0c0c2d00c612820b1810b803c001c2c00b203904164010761300205407503c1d5802041c49113011031840e1045d541c1003190300000d055203000f0389007000e042c0e01c441455104024640e000d074280000403604000c5504121001426100d204101c1940c40720f840302065071140203028800c07801d140005c90039100100700c4070fa280806845900303140e8070f000010741c42131300108113020440c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 63268249 1250 63266999 63267007
    0xf0c0403050703060501140d020a0302042003040c03050d1103030604020a05160501090b100f1202030a050601120c06090b0a0c02010509030109140d0e01050304080d0902150705060105030303090a0f08 87
    0x7101006104041e500c202d402041560605c0104007481c1c02031016a48202c9a201a43e405601d0300b10080064030b80540700400c2c0ca2200ca44030008400f2007030314400c00f403a40001008244200c04c4903090a4030f20910540d4421307440204116050009104405865001000030400900d403c3d4010200800e1034146503007000c40d52000300340072440c030810540d42651203070740d20340401a51000c2c0d1503011180310690000642444c07a000c001200d0750290010400500d10a4410f56408112003004c95500900721a15503841e20304031103a512801c241141d0b01024001c022545170b014030946400d03280034401c56424201c55041c100d038100c1e00c141069052000800000010380c4003805880c00d007901400c5507400b82d81c49810503d2030004d2402d01a0100200d800485203d83c1c0d11100b22500325030803121481e00d84594941082c0104003540700294061501107214418414103005810a40d009109441e01c070381e664001e040d220310044904c0340868103c00041c40001e0882c00818a40742e01035401a414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 63269499 1250 63268249 63268253
    0x1215180a02150a02070b04120602130b030106020a031e0c0308190c18050d020315090f010c080604050603060702062403030a110f03071106030a09150b03240f0c0403 72
    0x1901d403842c4044110418006414800310b601005801c00038020018010301d41898115a00d034466055500204906d0300000e988014143c010585000b510303041c205550340c3d594a00000c4d54170324103900110081940300d50080440301c082d003080b03083e08019860703031110441d140ea0201c03442c501c000c140c01c41d5190700460507a40114203111b1030148041c607480351140c100340b14002d808a585076520940c0705e095a0710140c001a1004683c03c01410702410384002a0f4441d6035030070b801c0c01c0903d540380c0829842e01c486000342550101c1d8060158009503001c010503200c007400d03d44c076460111124001343e4050f80224010361b400b000e200094251450103417600c03411540000b41180c1c085400840002d40301d50545180390300078004440315280c1e01008516145441c0c0c0c9241405a4581100c1d114050100015000c0c5210b41c0110309140c3d407100b01d050402034001c01b1180144010364031540a0700c03810122010103000f001100c1070003000303800c4c9120240d80320b100440515100400010b6210414400000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 63270749 1250 63269499 63269509
    0x50909011d011a0d05031e1603020304061103090a0b03070c0506190510080d0332010e0a0603051b01020106030b070201020415030606050a0f0203160b0103021215180a02 74
    0x4003001c4900000c10f41950302511210921900c022082c0306800c2080f2003400140c00108448000000392055101070502c0f4140304040d0081d119841c091001d0707861894205a400b000600c155221910303209030740910701d0a0180d6038058030708030075000003904109020620516000d19400301c40c0d854000d1b043c0c1182c0c2e5400b0300380b01c42070301c0c501040e0040004500d0465414001c0d1a4012003841e0b030011954541900107984040e60380120060580d03c0009224024180300c400e02e500c2c02c140d03001c152082d41c2403001e1000070024400d003d5031020000c00300340c400c00c0c98003c420031039421800900010554140750314002d01c8040341705056642c2c580380000020304140403140b1422840d00016200c91822010701d10036454910f0000c109440e0420503c6841d0f0000c1c00e407059107589140811003059121016440c40c4180e216411030203035582c1002007046480362000c0d058a02c26160b1040041352602c5059560840a07006038958040c540081d0780c43d15000e210350404d00c2d07401e0803900c0d12500d40e00410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 63271999 1250 63270749 63270791
    0xb04020418051905040302070e31030f02030306030703080904180f0b090a020a1503060806010b070507120305070f080409020304062a05040b0c070503070603150605120105090901 78
    0x80c5502d41041002050291a00c0040c154614030180214549070340d009441c2c10f00c0703000f440e46134140400071031494034400070301c0340076643d811104400030080150080300c0b10b42180000c500203945510701e180035501c040242c0c3d020314000b8000308201819540c842c030160b00300003000c5401c5503494001440f40d0003100d0704100b000d4051800c8403504042400c3c41156020010450050f41d03004005030780060315007044903000c0f1048050032050704583c85004401906c40c6501c03c40a6205403000030824072641c2c07000b40754007840744044401c210750751800c0f051600354402c405804580c05000b01303400700c2d0031404a0007540d803048240c2e82c50280c8504c8038070101d8200b500c0680b001a5a8510004d6003140c42d09080c9040740398065603000390b4902800100703207102e00d008174808107401244042c25450308100d402c000d810024162141591100300040040c04040c4101c82441c2600000280441c0500211040c0d48042816003845070b08003424001800006046005103641e51803a000c07071200d03488250 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 63273249 1250 63271999 63272039
    0x1104092103050105130204051c05010b09040c0503010c1407110105041203080103060501120b0c0c0a0f120216060e15090d0c1505090d0b0402190303030c02100606120b040204 76
    0xc0c495041509000382c1740d0890f0302c4800d016104120078132156980300c180d0205d00c1d0903009480c048840c54903000b4003500d040003e6a1300002c0c103000340400c010021010300150342c801c0e0020070400381048812254140003003250f05010030100501d001080d600000880d40e13010605015103841d03030b00c480030342905d20100c5040d03000800c3c8600500421015000f801d00500c0c0248080c051b2100c07546034204520f1002e00740344480c0600044c42c0031400028040503c00940080c2a025421003500300801b000164000480060262030070241001b803a51030300009907900c80d6a03040d044602c40d02400240120741c00096900231040c080c241c61551100080850a48140d100a5106242c03105000600040300240c01c14440c060007045859104d00c00c0104170250020180034090320f03540007007076810200411051020103411700c003200385501500403403c0d004280e0708a03030000050300c1c0c0070000c440b098000d540006281e11150701c4001c5e441e0b0495103146c003004200601d001c1c1c1c2c0700300c400c40c0104450030b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 63274499 1250 63273249 63273251
    0x60314010606021e0303060f120327040c1b0804090c031a01081e04080c16170715032c0d0305100305071205010b0901170f0a1104092103 60
    0x309100b640d078144084144009040700b000c24045040d1291622400010702c2c00b8020f02410128028a0341c9502c00221508000070960b952520a00c40942600c1100610554205441e10b2801c04508040c460007126138001e5403164501400f15429000301403d161003580c440c0c60074000807070701c528284280703d8040811740b40024102c54948050501a91030190a4188440c40c02048065a031064011000070700700c011600440e901c0b072802110034002c005400b600d80c45010301c0440e0182d4142092402d03246144141100001c0c070b403403030a945040134018100381d842c3c0d00c045000740394002d07040700428051300012481c96404008070304201300d01c03440718072260707a1002214100045d09440f80907003180b0004400b0040d81c1c01d50311210780c3d5004610840b801195015100b4040c81429444511040e200400103500d5503550340e9080c4042400407410103403400340b42c0c500600c1e00310004404504543c410100214400d02204100060200d0281a0707030300f50b11401207543d2221000b4000b55040c500340c0b8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 63275749 1250 63274499 63274511
    0x90403050c0d0909050a0b0f0607050115030c05030f12090108071b150c0206010b04060c0206040306240b18190f0b0c19050a0f0206070b0f0f060105040e0f04050106031401 75
    0x2c04c45050302d20252010512901e00601925262118020118650000e8609641c0e5a10070303c3c2c801d006110a084000d41403044500200c01c002003880c0502c110781c0c045046454080f00070501c076407aa10900810240d400342000b020303555500403030429900a4980c100aa0b94905024208200060725030007200c3c02c0031307000e140e018034080a201f83e4000709418070060201d503040101c00341480c441e50103050103009803c08100308640d038141c01c86024650080d42800488208403100209156800803011b074101e5502d000315100000304282e8a5944501c81030070b481c0c003881c1c0b0501000c41c0c5100030201e802c0c041c5243c041000189108070310300410204c40084e030384401c4118564148560032500d001745400c0c0042c0800410800a2185080b642110b031002c403080080c40020344920585000421120113441000b0280e03a0300c1a1076413040760342c3d04020896940386c00044400b44154001d015900c014031000c80c210a481d06011030b40207106500014905450351070b888201d00810700704c51070b10781d1125 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 63276999 1250 63275749 63275759
    0x30c06060315151a040e04060e030a021c0302030c07150209040e0f070501090617060a0518040c0e06030a060b06070b011e0b0301030c09020a03140907090e060405060402090403050c0d09 81
    0x120503a002413051120320042c1c1d400300600245a840380b481a841d840200c2c0c4045002e1001c40e5104624003425542282d64404601001944403049100d2201445c8034802c09607400601a000301c0b40304030402c0c0d00a5140c801650354441d0490300402c50321112640c2400051495212441890b9005403400002e00003040b8a10080c0e1070401c180e0040790402102040400549030042412004a68540034007003281d65854045042c10760558072083d4001c0c2c02400c0d5607030b846081c1d05000d000d03030700a4044002040c0c480503070900d00d08003540d03417035010b5104541c00030105e416a03101000c01180101040c0c5441c199882d0543d440c102038021514800d444203442040000400c14080180f04001c080c900b1580340d45c88201081d90948100f9030b10b150000303040c2041612035030000030042900401c0c0300060901102c0d0366900d40c000d000d482d020b180742c41061501d0840c0021094465030f1300000030032003039840340d003803110540c4040c00450034003106100c12030a058040c481c1e1407404001c0e80d01d003d40305140c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 63278249 1250 63276999 63277031
    0x30a06050a050d0201050910030908030c0307020f0d0203040b09011701080102090901061407020f06070f14010b0d05062706090d08070f0c14030f030a0204030204060501110a030c06060315 82
    0xd500107480b0308580320f4a03500503600310040c0d401c01c200488a103450107c803100700b5009840380000041082800000b00220340d8120800b07140900e005500700d41520113031600180c0d481100ca11000c0259000780410000c680302a001030500e104185000b890724220410a08019502a04100d882e650081024612400c10501c00c9004043c203240170044502a400304682c0d0f4400e10101900a2805842001c015242d800c220740155900006004601240d41060200c504910000c90029402d0400040c0d8074a0f0195070100c5540e00000a0405500c517440e034085180c480050307010781030b9030288550740b0751001441a18455011140500001155a54000c04100004005c02c042c0414106e10038042c036485505240034940c841d840308100714211071200d143d070141c800c1170a05040000b080150184094010384102c0e44240c4092205075110340043d10240704244030780019a011001e8000400e20640b4881111400b0311000215291640c841e144840e0000620401594031b0b034071800d2510481c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 63279499 1250 63278249 63278269
    0xf0409020901030e1b0411070210080403090f03020a09020a0207080d0801062307060504140a03021b03010501082e0207240c0c03080a02040e10030b0108011109041503020402030a0605 80
    0x1942d001c1e0a10140110900d544010117500d414011a5183d10300311078907840d4811583d50940082210755a40c9148000801c03070788045504800143c8020f1001944e0902c40305210180ca50042c400d500c01403c05c2c1880000390060040c4604510903500001849901404084650411541c488a5070340c100315018201d030015a14a02405409140c4840c011480d2000e40b8812980003501040c60b40301d50402d0021794900d8840300c04c2ea402150201d80c02c160300003030301c4030031f45041c0605404095103480c101422170b1400d00c41c851503074011550039000c0c158191700c040051100c07480310174400800c0c41c50340012038201c1002140d1081040c070300d0002150003000034013071028600d60240401c448e281ca00500721a40b614004090000c0e08d00410408203254050750042e0040100c0030324245803880028120a042d44420b5480e40c4408001282c0b01b441030040c00858454503070034600e081e0441c0d041c030001700702402c201c40c4c96032040c1d140030005a542d400114041c040d100701c04a1640d05002c104915940c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 63280749 1250 63279499 63279521
    0x6080106050f0702030a060f020c0f0105060a15050d090b010509100803043003020c270103140114190606020109050606150f040b0a120b0120030f040902090103 70
    0x4111001005a298060125441981c0e660105030301d070b075080e1010038135000305028014000d40c100440600c5901c1c0311760150450726042400c0f1100070010b55070359800c8038415140107400143c10f80301800304001a6080c1d070010b42c464601185003003540d200400c202d50000c0811242c03400b405004114514111090720b420081d8100000e00d282e1600d0a156034a200e83d00c10300c41c3d51201081403252040300311400c50310408400403100c6007141e0321303c0d0094941100e036038100e1003400782c244140c8191540c12514501f4820800744040301d0b90039500e81455500009020004a40d202d107113400056100c00c040030b0280364804403070000a13198812880540d081c46c1c210000f168508000f01000c5000002c01036000b600c03d40e1000450700c09600344900c2c0744110700c0704201c001c0000400240e0681e44900400544005984482440d8130260a00d0b0070f441c1368900c41d40c0007030081581300b080411850101600190700c1400c5030314203440c182c400c0f00541c1140e4032074440305902091880143d60140039042c1a05 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 63281999 1250 63280749 63280757
    0x120705160503060f0417040305030c060105041103011203080a1b0906021002120c0309010603020a1e050d0b06150c070602030c07060906080a020a09050424051e04090203210a080106 79
    0x40b804c444802c4001c2001000600390411005010070f2000e0404100c0c1c02070754000044c7ca42ea4407201c1c034000da4a4030284140740c040d40c9000b641030184445141524140c46121260b89000c00740d0340c404540740880600444c8406589a001d04900aa58805101000c40944171100e1080c80d12002038200a4122111041d0f1401044070001d841131800410758071101d2880c0581e165190340103010300420007500025080040c0702808207084000311088520003002d03c0910300555116803e200c001c002c1030310003e09016040002c145586002100081e6481d2030100d90360800100f104c0c0c15203044903581c04280560000101c00700c0d40002400520f000c0e200030704000d41054908040100b451314014581c1c2c0809078003040d00099035100b9000c1400a0100030700601c07680c0100c40d2440301010b0245c2d440300f44030300314280004190402c2550302c62029002200501203403020824030015140541041740d15000b403071200711181b1904c1400782840700c81440119100d1440c110060860704040c2c002c10284 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 63283249 1250 63281999 63282001
    0x4060e0105070512150307061805030c01120b0f06030709060e04021318090501060b0901030e0109082505060a0c12050402030a0807240222031a0912070516050306 71
    0x35004001c0b103205500c841002c00040e642d010031000c1007085c10100a506001d1170300001012580201501503036a625420004620b80e22010140e4a070b0444070740030f0200361020f03801c0004078600d40c0300e42007214016206603c0c1c1a140d02c0000d190380d00c21070307070310b0086602e0040503c1041d42c00009501c1c054015102107140c000ca04041d007240550742e1240559034000c030080c8094901c3d17036400503096264000001c0c80313101e8498204440b030390000491540060318104c105600000e05008100c44945c00280ca54035041c05102460a41d00d00c1841c1e0405d0303109050401c000254042018511642c01c01c8400503000000d440020710100c070246440e90f1a030f06003404c3c003000d0ba43c082015038007140e1061040ea81c0b45218a807100b04c078001000c204d17102c40c1a180f8511208101ca4004082d00c204099801807a80105e41c15905034030000c0c00042e05a00100c0c0428160fa0b21040b10035401c900003d00b00c3c4e9030034002040380d01c481d900000003116150012403480e40c40c81c110088110140104030003400d16 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 63284499 1250 63283249 63283261
    0x1c032307020106060e13090312060e040b060607170c0a05190308010b040605041404060905070c120203120109090804030206040303050403060609050603060a090c0b12090c15040905070302040e0f04060e0105 90
    0x5041d5112610a40147e40c0b02920010075002e0441141192540c2d0014030201d607a910017008a007400311015580101100d002a00b1442c10000300d906d0b03103500c50710029188130000b002642e44d421500740130803c0d00c200105140480c504002046003140c0440342d02e0b00c401d1aa1500a054030410b074030409145006000034400c16411001303480c02e6440361803002d800c3c030103020000380160006902030b0300054070707101c240540030b030740448404022401105038000344000d2440885e40c0317215002e00614048000c00c0148200301381600014400d5006040d02410241c49030002038440d07000344c0c012408110009400c104100d16030180200401e142d4a0030001807620300c02080d114000106840704560f5a00d000c2d01c104500f40100700301030440903080c2d5440d09119400300c5854034050b26070105500c103002008850345060304140254105036810641414070380b84139000900f80160440051580074003011804c0c4003066101ca100301010f01200e03c803406c0a080c41c0044980b240c40401c071340d074104010002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 63285749 1250 63284499 63284509
    0x9040f0509011802010f0e0d080703080717060f060904090b0708040501060608130305130801020a020f0106150905240f0a08100f050609010306030602070302030306030d0c02031c032307020106060e 86
    0xc00c091450600711f9172480b150b80092207000c60340d48020a41000441e01d1410316600440403803107000c05445003500d0100d44611951514000c640d0240d000080d4802803001c1d06045d0043d008105019001080e890030035511485540300071607074000043c0d060010001841024000e010052103641000d07c00da0400074400c40e992514107001400b404400200140302c032140d80c2c40c400080903180000c540b501c14100e402525115000f03001101917003002c03000720314100c80340b10440b11580301d5110046032514010a101e86000103d10012440801003800f01d0307643c100c00010302e4804130100c02c0617a580d140d401c001e8041c0d000038216012081c0701042c103104400640c141c90b001e5860403111aa144d07182100120060810740d00000c1c60180045450b004060b00080594051103049047d43d600c0d81e1039a000321156840c40300f003e0340c1540070ac64000b00705014803500941c0410b240c03802003181a200e01001c10006175150008007800e01000030010819030a118080184c1803a01c1d0080d421712480300010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 63286999 1250 63285749 63285767
    0x11e03020c0a050f0a0c0e190207050a05011b030b0f030309040506120706081803030702060105062b020306040e030711010302030a060302120a140f031206010507020a0306020702010e01080c030f0c09040f050901180201 95
    0x1a408c03036000800c5001e10808124030242c0e140e00000a01c81c100103024101d21003144c1c40c45802c0440d0401c42014414508202700786060b141c098011400d00301304100b00070291001030602c0e5000420702c2c03400107410000340302da640034000343d4807600700c0350806150721901040888614401c03a0001e009100300e442d40402c1c01e42c1140d02c11902203444d562a00401101c00d15501d408400380b03000051000e2030f019840d000340d03204560458081001101000d1015224800c45000030404000c480d26075680d980241d02031904452640030014030700340c0b40d0f4040740720704912000720126544032041d840c080064525114101d003010002078442c2002c6039400c1e0741d59002d5203d128071402402c7e03002400d1a480ac1d41035882c1550000d1240c44081e90300c4c1080c8000390307c801426800a0f04049199010394011048540075604c40e8410614682c0e840c030016200c0c90001e04107000040d0100444d81880c3c1d154001c58040100c1c8d841c0000c0d4506040901d5400c40e981d058010903100755031015a40541c1c0c0040f122 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 63288249 1250 63286999 63287041
    0x501050f09090d0f0210150f090203041223031e0a0c02030403030c06140c04060909020418090501060812040e06030c09010e07020304030c090e0606011e03020c0a050f0a0c0e 76
    0x400131a0200301801c1e41131900280103916510f14101d01802101109941282240c4400b0f10722240c0c25207079803c1c0c0d0141e200844000d0a0390310b5244c07120010500c14158011122503000360f41c4009000c8440c03544480d44184e03003007000c45030042c04d948140b2002900480d000250302c5030401c013150381450082c1d16030095106c082c0c140314441103120140b200d260480410100361042402803464030a42c0584242c1190240b0b4000460344040400d00c01054030840b010344800c00b0901042031151047c0d1409883c02840880d141e54982000007448407041048040e2044000f54154645082038800f01d41400d00410103840f0781d01403510034500d0b464203003000781500c0441d44850b8081ea41e141c4140c0c41c600c500c2e440109504660000014070400746d510800d44c051554042d654640c54601c0110b4031440c1c080380b41e80042100348031941e440b40c003960003020314540e000300362000700c281078840030b0821009030b9008515800008130b480800c80659102405000c180c1d03a00c450b241000d40755400b40c4080702600d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 63289499 1250 63288249 63288257
    0x1f0501020c040b040b04050106020609120a09051203070c240815060a0c0f030306150e010905040c02070923011208040509040f050d030c020601050607030c080306040605030d030501050f09090d 84
    0x30701e050715121070b041454034100182040c00b840d43c9d1044001d640e21411150f40b04103000748140810035004840c00c503500c98282d503803030039142c904042c10001204402c070410034036031204001e080009101c082c4d1510003000e81d515000c82c1c081c00781d41e0741441030b128846c01801300040c0004200150b00c1c503140050901800f51506912a083c40c04217071082d44100710007500b050303001d240b60020907a040d0444d20568a001240c40c1d85441342c60360030384010b2401011b81c1d0118201c400240803a040543c0030511400c005c1c81190445aa00d461000488000040014a140044520588020000c0051401082c0c52000030800103282c0d1a00d1081d40158000c0c54032079544403002ca414040e0b0a202664940e4000c01954941380b070700000680101002c0500780b0150040400000713991404c0d0b4156084990035840d00c208440315940c0d8820385074030003000b45500c161707240d60100d81e85c0c80400c400903422606807400506941044208031800580640440c030559442c42001891440481c1c400030344019428 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 63290749 1250 63289499 63289511
    0x30406020a0f050f0a0b04060b010309020f1003020412030509030c0603060607060b01090b0f070b0106021f050603030f07080d0b0a03110603060d050327030105100506160203070e1f0501020c04 84
    0x1400c40d05000c04132103000d00f28894068400c0520400b03041c3c59000360f1041804000802e0340310300550907501501d00103580101c0ea42d081d0240c03410500c2054455107118a001860a03481e40307251144440c818500750000341001c110030303032030781010440c03054a0306003210b4103800d41c908800003d80511a1380350007085140c940c4508051039005242d028042e00c0c1c0c01c55620340344d10801900b1851504000010348030841a500001030140c004102c001c600709801e00682c0a55049a4002d00549005010300c0d405100c00c0100400300c072a10340c0a49074051064840541e6400000190f400380c80c90505242c1c8180031308003040002070002e40510380b0b0b44c1025a103058032a901c10303002801c00d48100780d020307105000000b81d003100b01e85a402108200078031007840091507549070060600b25082220f01100324001e81d9000d00c01441d00102030100c0c1c3c4c040d9441c02c01c441840c7d9011a0400c074503075000f45050300d0070078107002d844120711102d17070300300300f81c90071503401051510300002d54441d000383c1c07224003c0b1741e505 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 63291999 1250 63290749 63290753
    0x20a0806010b03061504080102040e15090610051b031b06010b18041a0405040c1802090a120c321804021c0212060103030809060412120e06070c020102010e030406020a0f 74
    0xc0709550040c007110002715240c0d50313146203240c01c4200c100c40003020035201c101d0003140303460040e0ba96406298062300c4141e490703000d0b4509032100c2d4071000c02d42e50046074908425000d01c10810007820403400d5048245005075411402502c0e05038103800103c0400c20601079218598101000800900c0b4122004a20030200c02400f4200d440e520304036a81142c14882003009002071a40114125140c9020a00a90403540306900c01c80c080c00421950042c880c0c10200400c52002d00d43c941d0243c015880288440d0741d8039101d8610030031003a20555107141081201000b000182c00c0000341c28000e84102d040c000c402c0207001ca072032200400c0241f20b40c50b26440240e04e0100c00300d50012441e0301510301078840000e0510716540711000d100850000d040400095500b0b20003042d0301c0d0155a01142d032001994400400355a110462986420780c1551481c607a84c800700304010300d6005a0705904c40c43c000550a000090a544010745c0380764840d0320030081004403641c001030004080750008170610034040a4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 63293249 1250 63291999 63292039
    0x11040312021c020a030f090510030c11150103110f0904110108010f0b0d0e01020c07060206091605060f0309010216030e090a0c09090207050f06280501050d030f090e070507020a0806010b0306 83
    0x123500502d410041c4000e01c00f42894059101d0303c29410903484076440c034268044010358826108600c0d5640f1401c01004000040c40716140b44181c000041268041180b04404100c14010807102525000b204002518003943c11007605030150000003255444e6905040c5810194403440e005070605540d05c0c6007014000710700b03505590306000d01b1401c2d240712a941e180c009642d010309694100e10b90254141c1503908111101c00e04003140e070007030402402c1c60140d940e402d510b80c00052005503295020041101d50010751190400c946101e0303103a150315006654180100e8003001403803001800c1c60490f4a83c10260042c0d0380720200c03a038640026a5449917441d06900300600030000c11824400d103010321000001c040c054030111260012186585400d10022030140d41e403e205660f00001040d10140c042441407402c0e150300c4c2c896040c0541c101d0b0f940c52060009070b0040719020002240461000c0c1145010000b02009004010050101e5410000707840083d00c801340c2a5489464207104107841d207540e03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 63294499 1250 63293249 63293267
    0x6010302180702010605030304082406180a021c0c0e0306040320150717070306241701080105090c0109051f0c0602040e07030e0303040b010509090111040312021c020a030f 75
    0x180523692110340d640510b9903500000c6502d00c10900617485007005078088403004500c51140100007a1b090340d001e403808102c0e00809061010f4444e02080304444c1c0000c2c11554056802c203050000524425022008002a2185058a210390420f405000101c0c0d07000d2500c0d0001d241d280c9070481680f0380303a80741a1801494201d4250000b01100411024540001007101c190a00c0c00b00b820300d82e524520101c040342c50f180204a042c1c4e0811a4100c2c6201e44441c003000c907059103092540b8021058070b44050713103c3e002d034070142107603440345c04000c00501e00340051906c401080c20f08058079801c00340014003c0c1030f103e102ca03480c0840e000e000c03401c50303228500c4d00507031a0304a0821540c8070745450004081032411610303900428202025041c9190300001242d00c11f503005901c0051a0b4209010003a00316000303044002e141d034851250380e05c2e0b40300450003000250b10680c0c1d0080c0d0144600b0b000303420680d41c1d0000c1e0715106069112048200d402140d90f03910346038980344c1002380c060034020596080c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 63295749 1250 63294499 63294509
    0xa140307110105090a0302010c1103040b0315031501081002040e0604050a0902180f130803060d11040e07050f03030f0d0b0301151811030105010e011b0203010c080f010503060103021807020106 84
    0x200b00028484c401d0780c0410000400c0d8025402403100f000c4010742620346081c440301080c20b03980100070801c0301c0d07100c4102a40c0c010240d40560310405005200103440c0c110b101c0042c52840902800402000d0f1040051410300103030075006504142c80d045002c540e5480041801380115154000a403d0803501c0e408460000c0d80201001002d2800c00c4901c0452002115003400c4041d00d48013107801600c800000d440c41c0390b4021381e15841c642e241801d1080302501c11004640050207010302c00d100360350b1405540c0381c801e050401884800d2a007410030009000050b000385c02500100000c4188407924421160b40450800b0b01254509900e0042401400c03804c08242c420b10540780e020405002c0d40b0418110600e031581c080c0404002030140f89000d03c421b100c0d031808a81c01101c103d400c0c0d40281c0461a180381c01081c003420280c403540110307095a055000035000941500d0401c201040464030040c090081a4020081c43d03046a02280c041c40e1407082c84060075039514005400c1510035080700000e01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 63296999 1250 63295749 63295751
    0x902100f09090c0e0913140d0305011a0304020103150e07020d140a0903260d05070e03010b09070f050403080f1314100e0616110315060d06110d110406090b0a1403071101 74
    0x501030010a84230460409890006420314000142299241c01f0410b50000521780d21032a5460701c1e401500181803100d21100740314017141000501d0748041440c2445900ca54010303040c80100c4090007045155015040800c4000500c444002103912100c05002c1c5c0350710062064039415030315034018800b401010710381c5010320300041100315040d0136004075000b2085901ca0003038000c6ea40c4105802d0702c400c02c0e1040e812041c400c00280510744a81d00003411014142401440c1503100e4860620560040010b1480c41e0000030f081a03100011040b07040080000c40c158071100009000000c3c80802d0b040d4407801084500c40201d10286d85e900308a074440e080c0004801625601c130310742a400e60100daa00c182c424003034408819080065514440c0c031170301e0f00400801308480982d86d800c000f8080e080045c25582c0c2e0a01c0040c1204c2c3c154843c124011700006d000c252030300d280240c018114020342c5c00c00c00400c0c03c148100007080c0d41051290111412540000f03890742c1c1c2d80041203494449900e0745210325 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 63298249 1250 63296999 63297023
    0xc0809060103030f09180c080609041106090d060e0f0d0807050a050304020f0d0302010b0f0d1511070210090302040c030e1905030f0f04090605010503090d080402040902100f09090c0e0913 82
    0x102c1d155404003071f58160a440b52681a0b95110070070001c800304640207806024414003044051511a000380060040148042c011501584418080390007044031100d040e40150344521035460100200c01d4009554504020700745040e5000503c0f6001d81c5070008284000400070508540d660a0807600020000c0c0c00200382d1216410020f01030001181598016207560700140301d1810b140200d90141c0c2d410041410ba940740c6005008000c00e42002090034003182030044400595400301e06100301c10342a501c2d90015811030040004a6098100680505107803079698003040700042101100c1c981880c0c3c00c03121442e5035007030080c20340c8611015801c0c0d0600009120500b9035852018006076080b00b8401c0189035107850055400e403100f5140c0303041c0755008682d0b07a4049031140740c5e43c41e440f0348098800f180c00000c5034040340948488020f80d030007081c0d40c204440481c942c44050180200706000040c004100c446401400324124610076500400c0d100000600c103450007040c100310264401b032085c1203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 63299499 1250 63298249 63298289
    0xc030e12060601030f06081207020d02040c0206090d03050f01030b070908010606230301030c0e040507030f08120618060103110f040b07030f0815330c010c0809060103030f09 76
    0x19600202c032101c0c00b003450a042400101124420041584c020000804405002140f0b46102e40c11400040741c0c05a580754400c1d0068650b40168018084a60020710503030614803002420809003c0c140710406103807404101c0c0b80d1004586281c116508419404510f8a6032501211070203100d82110801e582850f000081003035111604c503244050031818080302c00301084102005120030303c40680311014080081c804400d602c4070b126006841041152441c6580e40c0c0c0302a41280d03c0d140568541c00081002c050751404221102d42c44001103c415040c08919416241001409003685042658460806031200c10310421980c0380400000881d40341e5950f03045030401903008030412400900340f08905488a405071030060f0281c1c0b580749249840e0404074090040384007018486010301c0041c0b02e03218070540013003910740556407001803c5942c0c460004094074251101d0300004400c00c039501c000c000d074080000c103800e410f5943c1850805512400300c07000301c40384007150304032031003000750145a001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 63300749 1250 63299499 63299503
    0x201050c0f0601081005040b15030f011a09010b070510020307020307051f0e15010b071104020304030c0c050d0206190201150b03040c050906241605030702090f04050703030c030e12 79
    0xc104c0c1d180b4800c90340340350102c2031201c01b515001e4500a2400300b400317011542ca0706010703950401d1054060200c0d0003171855484442c4c00d503100100101c58002814001003603d051055119000d03100340000381d0720f011007640d20740f40d56641d40c40700c3d61742e49903010003c21001407003841207508282d0080f0484840504480002c40319502000004044a00c1c0068091960170b0125941050301014801c0050503880d00c080d041259100c410704541003101c200464286950b98400f03103015500070f0340c510b42c10000d20f20f0814a0450b907904a07512550681d01d04030300503070341c1d0300031907a04101301c2d5081801074881320000d03405000629004070a040d00d64001091111614002e5445a0f02840000d070325140e070f60040c8010608141c65183c0c014203945181e1405004e4441544549081c01114918101c0032490444113803110407000c9426800009000066140c000e40c940d0304015000241c50960400d43e0302e6a80c3c0b002c1c2c0348001410311851450300010702d400750401d51042007000c0c000548103030b403114400da = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 63301999 1250 63300749 63300751
    0x30e041b0504080f01090b0112020409080f090f010503060d0303020d020f0403200a1809050c0a060c05151302100201020d05070302041d010f06320304030206010b1e070201050c0f06 79
    0xf205031040d061980c0e1401d03414090000a03507042130490b085642032821a40207104210b00c00c0c0d0f0000e88a80f000390004030504014030702100380424858132040401c0420013440c40440350b00d03041003002d0040c08025a900110680203981c0341c2801130b0b907135203a110181c000c4c0c00f072130446179585000460000113101c3d4000041c0000c1078209a05110b40507820208804030405020714584108184a03007071390b070b01582d440f0540d080d000b202290581d10150000443c03070300440c0c0000c0002080500007000b005003c01542420b24004040d41c0610700d4261400e580024040f00c01901ca0702080405200841c002c4d411946a500e400500780807034645075a0240c0139500c0ba105070030640d484a200c1c8500c0b8080404050b05840c20500c4480220303142c0507003220b1048241e10460400d0101c0c0d035002e0203945100d6040005844603401c1c5503100e00d00750038041c0c10b1180c141c1c40b02c012032070f041214607400b000c0326001803004041c10a02c951a4000b90004848a0162000e020786522810034031001c841000074081e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 63303249 1250 63301999 63302009
    0x309050c0112093503070c0b130204150807060201050c03280c0e0907030203190b01030e0a050d09050306041203360204060909050c0909160f0f050103060b0304030e041b0504 76
    0x10383c50326130380541c80111203902c0000c200304000000113408040d501d4000b00800c01c112031003800d0b43c00150446150150018480000e15001c2018600511551000303100900081155180c001003100c528800104005454800584030340800070759a480c2d4424240804020801d45001c104040c0070840c2d500c4656100d02480ca0006034603d119008a0340329880c0d0f90031040304072a4040848019080b0081c2103414952604200850700f401000080d1419000e540104440070701c154014006d0302e000c2c1c100c0c40c0281c10100401010900305424401c914109180000f40e40010b0b12400740c003085c14188030544141c1500d05041e88034006080c240005000715420818950341e081c8240442e5008000100203030091000035080e4030b041404d06a0180302f0b1001d070b89200440c4014000100c02c00d40240c40d00048124041c000000c20880c0720018040a0034104515800d14002e0011804001c200130104880151800c2c5c0c142c99580280300e0003004a100c88080c14404000586981c10500070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 63304499 1250 63303249 63303323
    0x40b0c0705100c15110d020d05060301050105010801032d0609020301110301061409130903020304080c0102030a09090b0406030c090905190c0302060c0a0803040b040b070309050c011209 81
    0x102040a140030350444101c4051a140c3c2105040300740e80780411400d0b003e10740d621040d40c400c48010710040c2c01008025080c5a040f00680c2c0304a0100f20f00221800680664002c0c0c3c507042c01807116980000140d81902d4201018038060852500821040e0b02c15020700050340d015084078900700301c140d0f0000c0b0a003034401c034000d01240d40203880b440c0013400300f44551000140c0d4585443e44150344107000301841c400c0a0000d2101a0072180d03844141d03248080100c005034000202001040c1c0c050080c040c5078007003480514641440020014040000383c010100440d0351203c4442035652254404030007035502c8a004240f250340c500a020003815880310a441e1030050b204000c44201c0100c5a103c85254000c0003da100760554091000c00c1c0c00c25210303684c5906c6850b4441d000b2031081d1000d140300e1885840303002c40364a0507280c03081c0d40801c041c6c84030080c141003001c0c501c0010404640c660010400b8a400d188110030802d880028080050001d030800300c01040101b0340780c18200180508a80c03842c1c27 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 63305749 1250 63304499 63304513
    0x3011e0c030506030304150c02040606080412030603020603070806030a050a032622020607080f071a07080a050601020a1406070f050f0409020d09050102030f01030b0a0905070b090105040b040b0c 85
    0x14140d098442c1294a1a03240c5c02c108005e001501c401c0c104414100414500304400780c481e07034040350454039240c01c8080841c03881410070040100c40c04105081440300c3c64240a024507650100c1c071180400352407041800b000300001a070640b4100020b11a03a6001000c484a0103810b06010304140264020342c0c01282408260005074041d140005003d01071409024103da80e1058a0314070410703401c202280d1202c410001c80f408030b00038102600c0c1c00c102615134103660702d400d86400f03020303e101d00c0e2286500c21040005c101180340c104042d035a00c180c20b0f00b00030911790b64950041b13081c85001f103001800b00c0540a5408002600014050301c00d1807503490780010f40e10040425200ac0c0034042c1c100c4800d00c001c2100380a40401500908410224071102241c11000c0380c3da11802e90300101c409000000d84500100107005aa40c00c003600320844940c200102192a1901c9845884074050003802c001c000401c0e050f00c0c4d110311b081f10028a418043ca42d00c40f07465110092455001d10014043c5203c0c00c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 63306999 1250 63305749 63305771
    0x9020909010603030203030f0408040803040305011514061b011b02060109051003080708131a0a03060e0114040207020d0506010e040c06030c0509010c050705040203090a0204050117030a050c0c03011e 87
    0x480340b07200780c075010340045055580b03401c00c03100700210044c411a135046040c00005503c01080003d4400303184504001f003182204141c401546004a40c000d984850309007003142c581da01c0e031400301c42c6068440882c40b05600482c502c940e001d4a650610100148161801544469800b003042170690ba26450180b0803603c07044040c1e81040c0c02400003402c122400c2101c1800101000010440300e07201703003200c42c22150f40340400c542c81c0d070070313044071101703c0d00e0020f615010310307505209000182c40000048082541001c0703210901d004510304490040d035002592005540d98101a0a000c42c0d0050450302c10303607140c242c2c01c2e0050800351021115164140c10218030381d03000c1c1c02a0382c89490030390b03519800c0c043c80074011100c50706850b0007a56540105070021450740ca41d400214803407501ca000071311a0800600c11701c0101ca00513800606900328010740c984c11701c00080b040310310a560320324201d6202d0b9201400a41858011807074030b1b504d5840e1403014000400720521044403001040300402500c450a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 63308249 1250 63306999 63307001
    0x3101a040606050a08070207081f18150b220605010206090c1c410304030503030403080717090a060e01020901020d080a0207150905010c050703090315020c100902090901 74
    0x90b004100203e00700303200d109425407207000501e078001c4d150320483d629240e440c07030041d040410407110801c07869907949004140b14803a00a100d80d284030184000243c0780280c0300d4020021090800d1401e040c4c07902c0f03048a0036500c41e854240f44000924581410314017403516003000705518410940540182d00000d01c0307042d00400c84c0079a081028040c0c0003a0ba1a440a820360014210070440b0b00c402c280481441c05c01c020b06810701401c241c200348024010350341cbd4002603040480c1d041c034610f030381c42000103100081022003902d40150741424505c10030f40300e0600585201c24014070008221100030f0800c02030303020000c1d40b40011030140c00104000c4501d50307205170a034811303240d001e030150340441442d40120307200b4010164095006140141403003504c3d0343d181c80807520070078801001512402c0c0d01c41480001c0c03281a42c0508a414110300d040c2490f500a030403041e09100207406044108803003000d00c01c01c1c2e0121200705000c10300761000090036240340b4000b0b003040c65090b070148d010710740019104441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 63309355 1106 63308249 63308261
    0x50f0a11032a0a0507090209010507081303060c031424030d0905030d0c05072903042003010c09091104050d0b0f091605120c03101a04 59
    0x240200002c00c0740520025004950442d40c026000102c1c0000c852045032105d01c00907841c0e001050040e40c8a0080d0440500100000540344540080c900160f0095078411402040743c0c42404204804a8041306050101402000c02103140300200ca202000742d166401c0616940c0c2c0404008603040020000403d000b00321080e10a0081d4982030081c038a075038949140c0180b00000c10b4540c0e48e6120110701c0341407000c0e1544000c05071205e841c4075a1075021138901e0f00305960780c101890240509005220f44120071074454205400303510303041c06400581603040e42d0320f075441c42c2031440c42e000805050100951028007003200203600d888500c21074441c2802501c0c1ca003200c0c40c0071115003544100003084816030381c01c505000c081100e1080d000100b0b485055400c1c1c09480000c4107514686542d01d021180e00d0700c120314142c0c81041c055000304c1184170203144807503a0414050300340825958 = true := by decide +kernel

theorem cover : BRFrame.Cov 63129499 63309355 := by
  have h0 := BRFrame.cov_init 63129499
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63129499 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 63129499 ≤ n) (h2 : n < 63309355) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
