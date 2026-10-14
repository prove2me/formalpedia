-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0706
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:15:36.909034+00:00
-- url     : https://prove2.me/submissions/016b51f1-4ec9-42a4-b206-6ac23e16099b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 126798561 ≤ n < 126978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 126799811 1250 126798561 126798583
    0x90b060303071a040f0b09160b070804051212030f100504180210140703030f1104050a030b070309020406060203030702010f200d060f121e03090b030a0e1009060e0708 73
    0xd00303410b071303100d03031801c0140100d81c071078041d2220340715609200465002042c24041c02502c03403a18070700e5544401e003049081c4214100205004000c100070085801d00d013101f1600c04211005a95440c606079410714202e5104131fa80784640502d040c10401d90003c0c801d0f03070b43c001d131109403401c000c6041d99801e030802842ca0004041d1140e01c00b00741110065129020234168000f01c8480d0a440b521103150203800b604511118024075030400c0049484601c8400c155400c072403005103140f03884c40c515140c05200050141c0b4070410103403210610809a122801014004d105c1d44c3c1c0110350f60719240c04003e08682102c1c81c011240d5040c07060003103410841e100003482c981d9428404607507544001d60b60000900090344180103407981c0740e1b00021070114240c40d5040040c0202410868101c42c0c20000c246442211801804075000c9007081c002d000110000c0c0d94040d55040001a61030f00851420385401c0700c140b48002c0c200d488503514010130040740260010707208901c0003003916505017034940c5d8460800c000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 126801061 1250 126799811 126799853
    0x70303060e010e0a050612030c010c08010806040c03030f02010b1e10030504170a1716080906070813020f090907050f0a0e070f200d0801080d090b0c0f0709090b06030307 74
    0x5c08540555070700d1141040501551003160382d50307480284d038640a800688002c0010965500000864500c0442c0b51441307940d00081c031506603401c42d0750079140303041c83d149400b0440d942c07035003000003c0c0c03a03900b425a4403600844007a10310302c81410400000c0317141680d088042500304824840001c4080018505142108200b16110000d8204c1200c42d84c103c070741c81d100d445072254244600d150210080980c04440c0d42d441c17820359034928103810340d01c3c00180d52080c0054a0140000e040c01c0d070440403107540c28401001190f241403404001070031118255a811306540049000b0085840c191140e041001420b50301900700c185003408403462040024915414051070009000c802c511807106110000c070b4081e14100610b0002991b265244144104000032507850380020400a00004903040039064964a0007060340c200644220309400c0010307025118800e002001c0d00c80d00b41405440041c110003a40000c1480d41c6040410305200007401c014020341041180c400071662040e814000584103207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 126802311 1250 126801061 126801071
    0x12020f0c04020306040b1908010c05070302070e1305010911030d0f021903031103090705040b01050c0c0d080f220b0c07030609080d140609060a12021302040503070b070303060e010e0a 80
    0x150104002c2d140c0b45849551203544c1f0701c040c2e94801d503243c41c0b12059404100007004015040402520180305401c000f44c0942d0080d2000c00048141411095100880400c10b42107440c1965520f070035118500c0b4200c4420211203d51003039802c00b0080036001e400030b46881d54180344925006500d911104260303040c03038082d00104c001414000d03000710002c0302180c000950749213080202035880f41001d0003182e108504206020356150701c1202581c200105076406007200115040400103202c66424040355014402c0c001041030569071800b601c00c5280b142020306443c10b840001034500700140d0031200e05c030a414404002071010001c0c400c003e03603600600c0082c40107580c1c2400121405070a501e4403070030341044a011001090011403500441c015119a8040e40b902c5042207170842c99030141e01112a90b014000d000b5140058006500c15592000180303025107500102c4e0034400c40d5048880014030000d40341040661500c01c0c80010681c8000c100b4540d414040d000042013009840403601c90380350 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 126803561 1250 126802311 126802321
    0x415050a0e0307061d06090315010e0a0b06090105071713050a0f081509010f050a02040501081608070c02040f09110907050a020a020d0201020c030105070809010606020a1110020717010912020f0c040203 88
    0xc41b08950101030010704a50103a4501d400014191800f40110034400b04644042603810110b030086a01c05800181003a040c200c141d801190160450312042e00e40f0501843c4142040601c00024003841100054418040382454140074406105d81d018501640c020b803030801103080c0c040f40d20512101030100b02001e036280c0311502805040e85801481c48070b40740c1401d11900d03c00310307801401210420780b00d040b0f10355140455540c600c100c2040784408682200001202c4034030585d52a14294401071000803400603484540b42180c006c0a03040314444c1d0804a02001480e02c0c4041d16444010f500d0238500d40868002c000307440c2c0071290402800346685241c1c41086a009000381c0242d900007070001c2104e4503290000501c10b81080c4c1e640c1d0195440c2c8840414030610200d135911000d50001c80d1901e440c0405000d100c48549030008a5086000b86500401c038007800d05c408250303900d22100040b4600d1a1070030160907842032040f80700e056510046000085041c049a01c46030074004a40050316030707541c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 126804811 1250 126803561 126803569
    0xc0702040b1f030204230d1502040807030b0601030e03030403140703050c01050f0a0b030309030718150b070209010e0403080601030c110f0703050712020607080f0415050a0e0307061d 80
    0x48000ca54002e034250302d6000c03500c0c0e49980548212420740303000740796045400e10b140a0150030800740d55009201d052900e4081640e00000d241e400b2400e2030b00524160f504c41c69503041c001a074000b00c41907896002072050710740e40750290104104a06001d503113941030a540181c084d103481ea0581c1d040c0b201c085480c03c2418020030030703521006001c070001e0201e85405490a03802c48012034014907214a404444042e5040002c1a600002c2c0050000c0c50b0392800c1c804461303180c6a86540d0346603980d80303650503004d0702080401e00c0e20050200c81d0803140c07182c1c1c040c41000400f100580110110380014010040860340c0300103160b80200081c24001841003924070120340448681100011038840c414000300310701000500319003240e000300140c039490b03512440d00c00760602c003824000e54003070070600020012540b002c0003030486c03100c8204d10b40c0ca460303034422121041c80a06201c41d00482d4000c41d01e892280c3d0491039911a00b001100a4100c45082070405040e401500c121201c1042121824800e2130700d0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 126806061 1250 126804811 126804829
    0x102007030c1a01031101090803040614090409080c060118020901080105090405160b1209010204060c0215070f1a2a0a09080304091b02010203060a03030c0305091302040f08060c0702040b 81
    0x2c48215075041641e12402c003030f915103140400141c00182c01a078001610b42000c02510103454460795080ca0b1a48841c075040f1309600881220307075019a23240341c1d80000810102c0100201d10610015103410340c5020301c52090345201e040c0c1d810381c3c0742c0104080354042c0c0e80000d10340c1c1034980c221017140454855040062074a00240c5c200c1009054045003c20182d10220207040d0508101e8610045035403645511802c1c1d000724402d0401050201400c0ca00524000182181d11203e030f0100a040c2560354696402040850380f0a580d8000c0c8050010310425041c1010713035004188a5540c101b131005c81942e030750f05803c06a81d02d00464030200d04048000c0c0325400c0d0400a00c0e81c1004c8030f4650b900d81640344001c04400303000d5841d010320814102e40c00380c0103009480c07241100600703c2807603034656181035440440b43c0d1001c03000c0000400c1403403040d40c0c0c1e6516400d680368121000603206c0e810980c071031101680729080b00119501c0b8808000c0c045180c80f0855206075410313100410081e002401040d142e40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 126807311 1250 126806061 126806093
    0x60909071b0302010e0c0a03050d0522090506011101090f02130204170d032906031b030a09050f0a0819090512150f060612090709060305102007030c 65
    0x60306a140748003455415002425045240c0b000d5901c0c0b076000c4c03001c1000321000b9200090040c1c0150700c0701c41d06203029002400308803070903600c552820649080075030784042c4950000084540e9075000d00400303590285001c2c14495800e0000c0019490700d44640081030784a903802403240400740500102c0e4503181d0180c03001041110544503c082e110768000d5250b03079444409400181c83e00340f41c034000580c444402d041781081c1c59061418184014140110b07030340001c1180c2c00491a4800301510038000a0045105110042e00000c0c02c0625203845420844c00800c1d000301c035886603414001140509044030212001081c00e8042150a81816901c0b8405544656840b03440d100310140d2585c0c0224051803090340784040070b0a03a80e900e44400b9501c42c0700743e030543d4010304c041c8001c4900d14a4401c0f816040a901c108859071165a291128203458150b001101c1640164401440120072801981d0310000b444100308004500c94035201030078059004041c04000b00c1c00e5021060050560100b41c00d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 126808561 1250 126807311 126807347
    0xb06100e030d030f050c03100608060a1a0d0614060d0b030a0f031206060c0f02010e0102120f04080c040203130b04080f16030206070c0203060a320118020906090907 72
    0x101c1c81c402c5003c1c00070704400603007054560074500002d1403d050402100c0c45803040310031003000d0500304802141c200c0401411190001c4c010071000c11082d0300c0072101540c00c01c2c201c1303195a580f400f40d054a415a2103a5122a00728241071814491070707174415040c4c81c1c0040585074002290704108000a25000810b030002e0310a40e0848803943c14143c1c0484458000141502d007403000d40e40d02c40040300c20b035a1841003d081203201c07810f142c0056106000d0a0301c0c0000520484002010f0100c03450090703800015203001590000034100001141841700905a200480d821400c610308543c4800a5001000c8001c00142c2075100141c1048005800d41e9062410300014580754014043c806900040c4a041940581f03e41000511101d01c240350160200d68050064202c9890b2484550040d006800c600c105210541d441949019000c1e0680713030010801111001107545006100740c2d405086000d00e9000d42d00412419510b84c03214002c4414490b0182c403040400ea40303403042120302c1e1340c02c00b08000360 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 126809811 1250 126808561 126808573
    0xf020c0609030718050714040501080c0c011401080303090f010905032a010c0f0905040903120e03040305060f01030b010609060503040b060f03010e070603050a020403050604061a1201090b010b03040b06100e03 91
    0x344c08040d40f0540c802c0c0e0326500d454100490001306c00c2c40501903889a40e00040c45000040e900401c0300011f01040701c00c1800220303d210420713100c000c8800090300328150aa20200420605000030401c240c00c02e100d4100820410303605450715905ea01c250200c0714600d100c48080e810910030318440c2492410301c801c00070040b4440c50362004041d18501e8400ca4009204188007041e02d1030b041c8a03055080d030741920ba0201c08141c05071028090841d1035003130581c0e40414040000454070034012a071194052140301c2e01c5542c11803070400900f82041e0040b00070043c000e101802110f8000d0103d03608140c000c3e4202c00d882d520480041c3c0c1030389840c8a1a40c00d542072804c2c00410410004065041c3c560680341404907540304000201280107610014000b64000c0340402c020039800d40c4502c081c16001c001c040001910000419410701003c0101c0c02e41d41e40d41c40b400340c2440380d82c20916000d8401007081d18a1070030151141c0b17848078005040c00b440b41c40d42c6840a0b60700390103500918692580507090b210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 126811061 1250 126809811 126809849
    0x40201050c060f04020901140108150402130902090a08190305070507210b070206100b0f120f01170c01050a0f09030c0902040807050a030515150303070b04050d0f020c06090307 77
    0x80d0f00388261000c0b070041d4800380010961941c2c0b828035142e004810317075561403140c1d00c03070511130b41282c4401c8181d608170303508001c141d000420010403000646000c0c0c4000d0ba980c0380c010280300e505c800c103134821b46c1c0b0b0f03130820610000b0000c4011074140071541c05290050f1aa000c40c103115003070841d16405001074025020a0300501000f094440c1d003098010f08030315a5941e01c1000230798403010700312030030000018400e9091012045850180c6500804070a929043c4240f000c150004148103507070700140080d11354010003003564a142c1c90609041300d44090041b14400400103840e40c05040f0080703052184205640c845036201d0560480115004040404003a41d2001c3c0d42c4020340c018010b80000d07006049003c255810038039980b008403640311b8001c01072004005230007000448013400c4402681c5400c03070350001c0b0341d800308040c045140c000c08410200f0308051629500e843d0044c5040d03010301403404445050150042a00c504043d4192800d9550b80d900f41e00103400c040c515000001005000c4140903 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 126812311 1250 126811061 126811081
    0x40503070e091902130f06050d1a0903071109040807060f0b030d090503060705090607050a030f0e04090507030210030905060f0412050f04090f0209030609060a0b06090a030b040201050c06 82
    0x103801203107a00240e030f00309190900c682d0090002034801a400003e04200c44600b0300c20b9903c10461199202000030b44241c03076200143e0b0403147d020081e25080100100010125a40000740e82c10010240c011807400c181c507500e480300e40f030a00c4905c2c1d05c10321030240000e0030b01c46544103c942c0729501400400c0070140c0c9150510081c07a10304c059034020310900c4c2e07204003150f0241034800180c2c0c0008009001550750311070100c60301e40c002c0001c20b41000081c8413200001d202000101c03e000c0c82034690407408c1d180711000406601c03102d24414480d900302400c54002c184085400020b071b036016100c51480d02c00402c82034001d0003c004008081e40300b0701003000300e0507040c440e00a0041c0d02c140c103006107806800380215902c1c01581d9034500111400c00040041c10340315401000480000301c405803d100f6180006030602004540c061f032241c103c0ca00300700b441601c0d4030070502444000c42c2c12908200c883d0010036041c04407404000c002020080118065a0203042580c0c007088244d400ca4400d0f262800c103031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 126813561 1250 126812311 126812339
    0x1d0c18070f050d0e16090c03061406160203070803040e0c030105210123240a0e0601090312050c010e0d09060302130f0821071a0a09080f0901120e07050607050304050307 74
    0x2040c6c00d40c640b5400c02031607403081c010241110354281a00300390545050070040c0c0d03644038004612401e0355440c0901d0050310140031050040500d00701554a4a02c0c01d1590a200f02005107401c201c00010401440f07180c1c1c69001c900c0d41d40030303100d00d00c03240d07910158070300760042c82001003403d001200c0f0715406902aa8607400b0a1040c0c1c000107410b1a2030117140350028540300140c4400c0ea00c05610b140512940680300c260950004051400991007036032511a905a80503007414038002620000b03101c0369095090180e509140380180080c11081e5500c0801003c180c0c0d607028290030181c002400d1503100c40b90301070b040c0281035045540e00b901550f910b15280c1d20309039000e001a903062090506035102150f041507e0210f0340101c00300c00c500220036008a6400b000900c41e880090f03136001140c0200c0c0090001e010b03c0c98108040641e11540c01c0700150002006032038944444e400e101252448060100e10131007140c4040d2401ca444418514106080d4056504415090f104602c00050910128601c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 126814811 1250 126813561 126813569
    0x301120326010512031606020405030c0f131503080a0305040b0c030103050309090402010c06060303270f05010c0f0b09030403110f0a050906041d0c18070f050d0e16 72
    0x2034880341d03600c4818110011941c000345010041008004100d00c1c00c16a400222019001050742c3c60700e58400b1240c030311080582415200076501180c20b100300d04003003121012203c012581e541442c05403000064080000008050b0b910383c4030804420740d642d10000c040055030380001e4140c0c6840044500a000b02022942035a903a100c0d840440d9450f010b03981224160f940050185151520503824040c0c1c000b030213042241008409007140c0007160f064401c0d40055842070b134a402a003040822a0151403040004080401c00030030010040365030482801c0f01143c07001e00b000712040c45541015510350490290162500d502034080000d1080088000c0044e40d10660303e04849441e4002482913030140151a260020100b40703060115140400ca256844238004201007080c4800a80d0f00009040e01d03840d603204c0b6400f8010030341840c903086050741c0a2920552504000c0c0c87d103240c0c01041680c4840d0a101404000640100c281c0350a400c0520006d42140450b03054103882d41140303016444d40d00c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 126816061 1250 126814811 126814817
    0x5120303150904030504050409230604200a1a1b07080721060f0b03030c0a02040f0e0601030308042f030c0609100534030f020105010321020c0603011203 67
    0x700c1c0c41031400c07600c924002c64155541a0a080c1000c0a0000420030140c06503140300200c0c0785204444000d008031030207032484a0241400e42000c0c0307000c8580046018410300002180d0300600f1403074513584000350071915007400281c460750792211300c044240720b90150f81051841d0300681f1b0f110391000103001800c40b080c40c0c0c111600a5520001d90841d02240340c1c1074500e400c000440d510120702e1a42040001c81d18803d000240184000002403855001403000300058120141034419490031740f1500300c0480a00b8010f002507001c00a00a4039203605000090601003460f01050038041c03030505030002010500c2446413594200f0300d20031101600002a240f2a21030500c0c0212241091019500010000303001e402211090303003404c0d41c040c2c0056a4282c4040012a6500e4144018131029100488030300c000360354181c802c2c207004281104908070481961b040c0001080054803600400b048041007244c503240c8036540d6402241024049008540e01850200020841c0032040da000309051b44252 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 126817311 1250 126816061 126816091
    0x30627011403061b0903010b0a090b031902101b02030304060806190807050d0204200702010908010507050d050a02070f050d020d02060f01061110091a060f030d03020d0605120303 78
    0x1c0101655003900720b951007034642098150501c4041c03008090318021000500200e84840d0b0b07003005c10081c80350fa0784210304d0701e500c802e002c3c802801c051008015468400002e98401501078000c180c880c5110040340c002c10030503201c80d0020141001c01c800d1000c0d8000d054a6482c0e0b507440c0300810361507050340c10510551030360301e01e04010659020307981f044400030005401c0c290704d0030007005103403420000c003680c01944400842141041158600102187e1110640c0d1900340354000180800d149400a02e2140e00d40001d10049540000981e803071441e91078004a020381d50034140310083e003d9030704000d10081007202c001c01002804140844410700e15403c981c1220104dd03c120381c1d8100599021902613a00c0c0014001c0911034040d03400110140c20840d4503420700e100c10801200d461072416a4064132400311981c080412140254010340f0842e00000390b03040c4000042c0d240c1c5032089040c01030681c006440340c01c03903841c0d410007001030000600d9646040083c0f0006a240e6004482c40b0140041278 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 126818561 1250 126817311 126817349
    0x30606180609090515090316050106090b010c1104020306060903010207060f0b0f0f090402010903080a180b03011508151005030a0b12070905040c0905010308070309060203180603062701 81
    0xd032195800f899041402407000c0d48440c50303066242c98019140741c0c500c1c0806c0000d84200894841d189070050322410000518601e4040403104403551019501c1c1002400149031000c03035041c1350581c00003401200c0060307982d2207641c0001c3c500e1240701e04458040d4004a419070034059180d011b0307a60b401100c4800c0c0981c20180e4104186c2c034440c00c0105a0190032880b80303803194140010711603445441030403d0f00300c40c0e0704ca842d1600d1603004025000001401c5050403074035545800301d840000d01120124504550604442d91116084200b062041000034000180100d2040c99a50110721000d408007800c40211a030040c0503a1086074080c0840d4102101e2101c03900f060342020000381d40a4024104d22402c0c40c1140004d4400940140c40c5808440004500e0901070302c200c078001c501c03680005944500c240f8010300740c22a15072040e004d6400a000e40c224240110107100c8030345074202e4045e40c0c0da913145070024568400080032070081c3c44487c681d4000e04006449807a040e00c0010304244046041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 126819811 1250 126818561 126818579
    0x31706040204050d0b06040f06080a0c080a0809010f030f0c05071a0f0f0a0e12030702010c080903030601050a050d0f06030c090506100c05011b0207170307050a08030405070306061806 80
    0x60b9101e040c1c4c00415407000200031501244070035800900041000c104e00e050210401d007558a903801c018401d40088107003034108951044000c0007402090301400e0031500e1a100d1030000d0060700c4680d0305005050243c00a5288660301c02015501c500b40100719240d80c2150007030250300401c41c11100300380e640350f04444a441442410f1304c101801c1400540e80d60710824092006a405094141c6280d21030f1886601d0300c400f441082040300e4941c1c840350700c0b0b15004400900f1f442e1f01c58119030604c111034050051034100401120740c800c000303013409507440d408050200c4182c899150240745c010724203c107200f8081440e400010840303000304121031501e516010303000704541c4203503094dc0d03100d150811040c00e114000c50341c180e24140035100018500c000103036101440b0b007080c0300c507030010b80107510180b00414900200341a01c0c0b0400f001582050315a0707035074658484102c80d0240c05000d002c0f000134200a010031454001d180d1084003848069902c8180320051800921704015850403c40c0108003400c3c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 126821061 1250 126819811 126819817
    0x1202030709110409060305031c05073617150c0306010e13021909081605091b0705030909010b1c050a1b2006070512220317060402 57
    0x140080180c924103181507000c8000307190007102c0103169a0240400a842c5490b03104000085015070007440d40d441c07011488246034155009801d600510300b400340221964032020700e2a40c40f009020b182104480d80f000352510b001d4242c4120300200c8640c001040011008961075000c0c640701d01165902d0102421280c0c0808003105c104020400520004e2203561040010044c1d850000d4900703402d0303100d200300d51400d0340d001c6440c0c0009144220780c0030110580c421140401482d44102a05060000c030454800005181c811148a1130049010640c0c143e91352002c008440e08660a04c0e03916000c5280030b548075084242040d106524010000904083d18012030b2414411600c5a07500b02d01c40140200041002800007858039a0740d061500d4001d49103201e189100f002911200268000c4010301d4030079001090402000380c01c4242400051904003098488038051380440c1885680c03442004110107a07040810b580b11640c00d10a00145500000f0b40f020b40c05c080c00d001c0f15555500c6082c0f009030f00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 126822311 1250 126821061 126821063
    0x3210c070b1902040515070b10050f0607020414010821030f0105042318011a150a14070b04030806010c08220909050c010f03050402210307020904060204090612 70
    0x3108500015001e50b500c1c1c8100a64204040070040c20035860b14081941d07460180819500c20a0010310503007071083c0010196402000c02c0100d0794901d080802080700080058200b0b4045d4002064040031950380341c02c0304401c0d0002050003000c6603500e0701c1c115520101c02c62a01030740070451071989000d45001c01141e01c100124801d070003a0b07034644403d02000300324a54275140254040038007000501c03c1080342e21f00a0400310244002840388084a5003100c3c0c04900c41c4454811310513000e56652039410a200c01c2140d558207458541c0c0c8881401d50700c807640c0c500c0c803141c402c000040d4a001c014104c2c0c0c005028502a41c0c03103000590711030300152030000031458003030f10115052005404492309001a0409407010b04d4a480300660303070b080b105056481841049440382c100c1036401c012035030300c580420844021490103100c00c0c1000d4000c6945114031140c6020301d610b40607690b8003021410001c8407030265010b008480c1520b01410820000c0d04507008006006007000000555019130403109407240f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 126823561 1250 126822311 126822323
    0x10f020d080612030c1615080915042301020a0e0d0203100e12040801060e06011b06050c07152403051209010903020d03020f210711030c0303210c07 65
    0x5501c40d042041403c02c3c1081c1140311510081011940e040018080d804195049080c1c0310111824030120071a203c0301918000704101221b800c00001c1000098003d04c0100080e4040700c883c0c44a003480c00403506c424100801d980950602e0482240f415401801805c042da6116010003100380d04102c0c1c00e4003880c3e40130394168040b201c0701c80b203d411a4440030320906000201c804001c2118500c14680e040317a4012287d82e55140d40c00c102d529040c1e01303040d900c0442441c11030300003100e444c103028465101070000f030240c0782d5030340001d000c4940800846458503040520074401c0010781200c00003400070001085c50720300c180e0f110140d03c2d203210581d02090fa40d2240240400007150000712072941c0141c3c080d0b50406c1315505000001d601c40d00880c07556079000e0380c00740141019001c4c02910300100f148040b91904082079038504500109400c2d0344a003544060250b24201c50040041c0c544280e5920080d4180000031b2640741c00105050b4404a44265500307000305699003072010324060054203400390007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 126824811 1250 126823561 126823577
    0x50d03020d030b102001150807030c0902090a06180f1e15021015030b040b1b0a140304050c271f030212160e19150b09150309010605010f020d 62
    0x5d4454280a5148424171074000150055100020b4080002e41e034066840e54118407014014011000307010400b90a0159082d407804100300042801e240c5a44120001c00150307030030304101011280f4111008102d6003c8034036006803078103407000b440c1c01101c1c4020542da44000000038454048030150200740c209401806051031072000c1c18024014110030303500e902d40043c0c4040002040b00500500071801002c2c02a9140784c801600da40d00303076000010f0031042c4402e0110f01c40d13096000c01d021040c03000d6148035640700d44480c80d0082c40c0c010500340740350740020082450710054000395030000030b41003034a050540c1d03605e980f10003520070990b82e2500c2c0c2101310821003e0000d810440880e8440c0b400c10003c44441c001740e513201d40c424007840d4001c55040c1c1502000e004160740e041036040d81c00400c442080007034898460b00811000e41034452803800c1240490a6200c950300c00b506655150700c00b4021540d28606202043d0080080b80243d17400300d01c0c007441e04da44443c40003880c2111903050b500c030001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 126826061 1250 126824811 126824837
    0x5030a020706150306090510200d0b031b0102160515030c1e03010914060904060f230108060c0304170702040207020d0c0302011e27050d03020d030b10 66
    0x39602000e410b961058461801240c80001c00708140c0c001c40c0910700024003c2210714200e41004050904e08141a04020090110240c6003902e180f22504184100342d856603115001c801400410304c00343d40c54000d2241c118481f4540c91a0303040c98400076400e0b01c41c500e401001c0a4660799480c00f0311034114048140310000d50411138010b50b0406031120140341003084900c156402020007000100c01444084010405d20381280500b500780c04c148244006186000350108007112402480038007030a80310300c05175214002d540d001c024000500074500b0312068101024801d480f80030721031840d03280b00d100c0c00240c0c540c1c040c03401d40780074542c00046c5d42c41d03c14980194a035941c00c4032009aa0041c0c1c01c21540b4010380d95044034504040c4640018103c80c1d281d800054045100b280c0e809c89009201202d0100d004e512030080c1e4220300120321541084d0100c070070a06a04900c6401854001c0b120600b00d80c14590001000509016256411b00a60041c0c10900042c04958540d02002c100300c00c0e060300c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 126827311 1250 126826061 126826081
    0x9040207032a06200307031d15100501020105070f0311090a14040f050907051207030605010b040f0f0b04150e040c090302180108070509040c08011514030d0503 70
    0x45250080c507007110151000050006094000c02074607035060140000c007410008036001d40008400e40507403060b241d0701307100c00c048101d102c014940340030907542c0c00c5560180740002c610400d070030030601c0440b407071203c0c40700c140415260192801e0794519000d0000041c150710500602d4810052079031000401b440126003500076095480102090b0041413140c030409849a04507003004003d201c4582c625500040144400c03074030110540701c5840d050404101c503840f00054135a08403501940c20003030f40c8070300d01d403028240b01d17554000400d4207003094000160b1001490180040c1c55600700410742c0319a0751030720241c442c0e02a1244280c0c5150a0104001392000c2c1401c04503003c07850f04090610b881e02c41c0024046440c82021840400c0c003039241402541400f02c41144010244144441554180b80c5220703a9000765101d500d21680b00000050100000c1883c100b0040050304001c0c007040e8046142620000480d01403000b9540060700d090606140c0010626492811912540d2450f1141d100e9a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 126828561 1250 126827311 126827317
    0x604030e100509090705040509130308060f060714070608010b04060f080901022110050901050a030204020a0c0609030228030f03050c070206070515010b0c07062d020c0901060302040b090402 83
    0x3052000c02d000307001e11a201c112104d8429007060307a0f80c40e0307910306010402c00034034006844850390142c0d0183d0303880041d800000d01d1b50800070440301300070781c0c1c96450001450362040a20080881c04001c40020010200050030016143e6070b0322417114903070300c036503080c0c1d4a405148220030009480f1030410004501402c0e4580e08403803000005441d0000c0d00c541d186085180c0910440031442901c20480115a00850345029180484689406516020000f04203030385900019100300e5000a807030021030300440d218055107134408000d000810f03c41c1000ba456051034103082400d1129001100d0b940c64803281d03940380e6180d040e1108010400303042350480c020303c0014083c3d55180000c021480160b0341e4040038151784d6214000412101721030345412800c411042c1d1280d2a0b242050105424028003c90f654096500620f0716002c12000d8801c15008101500094444004200707107040100f903001c143c3e00c0e29000159600242d0381d0341c55000320100d10640c0f24806481d40284030f2040300d49059002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 126829811 1250 126828561 126828589
    0xc110a0f0309080f1006050a08030f0c160f0501030c1407060e030c100510080106050d060b041509050402010f0806010c0b130c06050c010e1204051207150c020406080604030e 76
    0x240400d03443e008028600086011030800d281d000d02d81c0d6000683c07843c0280400b410040c3c0300403d07054604a6200e580f80200042c015140801065a060307040081000b40b01420b4486101002d0660f02e03a10b403900c3d01640d008050000307050201d00c0c848140181d4524280203400500c4c94a807000e5519040018510045107010701e000c00c02001e001001e04001340c22014010202c0040c240c200140045100d1540d5880350203d6410000c0800043d1f552411002c07032950854804510980365500280060a06005020a5400700c0201007030030705640e803000d44510f01c00c0c0c80f201540c0c05120000e0703071f16120481e81640058a200b0b540380005540380350084d040199441340050146040d40d42000d5003c007a009000042d8011442c20050442401016005c44030a8054084000506426001e5104900480d4001c500d59541840e14050400c28000280300717003035209601d001d04620040c0030481100050b0300c6142001c0c40840d1001000c110b681c080c551540b40c2030080c0d41c254040c0111050040c038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 126831061 1250 126829811 126829817
    0x1203040c03080c10050a15050307080a080a09050a0303050a030c0306081c0203071e020307121101050906070c08010c03150e1602160b03040b0c09010f0e030708100504060c110a0f03 79
    0x101300824103c501400d4001e0a1010700400e91040703008820740450101d600140c800c1d4049042008200008940f00c03c285802016070355a500040c103043e14030880e1340d0b0000c1e4100706075040c0081815409009803011441595080c0420900040c003241500d4003800345040d02d41140282c0c1d1541c120b002500d40d000446801524101041034603440c151280c4c42c0780f130140c0c0386900c500030400c52030184481806000002032201d07107412291207501590341c00541d0b0505001c4000303405c0d1000d944241c19a19030300d900c441c0941c3d400352552281c40c040c00c3c07940c03071500100b802c000c0740315000301d0f404070080165030f056810011031b0b81d1103a400c14001581c1c0807e060650142c6807a401d40394050140002c05450249403440d80c0c1d04081c0b50800d070ba400300901c1c14201380c9042c80f55241580e0f0040c14081180700303e07e131140400036101c00285c18840141d120444511500301040d04002e0b0a0304210301c900e001da60100246007411100381d0f101c2480100420351070b0440ba01c44400941f400c48c2299040d0f002345 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 126832311 1250 126831061 126831073
    0x309091808040b03010e060d0503040603050c0d1d0d030606080f0408040f0303050403120306080c090c04080d0905030c03070501051605100507030f0501090b060f0706020903030304141203040c03080c 87
    0x1d00d400d07503070758095000503446003000001440018014600960020700582d50304c146181e040d29031940341d0040e4010081050380342c1001c611000c52100c00d482500402c16010008402c0300e1040b203540d03c0e8210082405070051070407203003519000344a500110f030400e4844184540d0703200355070044180010400c613001001030001141c003103500032000e00a140700c0e8440d20307511400d5052030484540034440d94410981048400d2249120100c0c0b28040c800b416a00752038162524083c8102c01d02554005002d1440303406c0c2d242e011181d000c41400101d4209074151560240688207268560441e401101d01003901041880d0382200c10002d134200450186040c0d802c41c1041000e207a081c1d0381d042e5030040019861b20000840807105110b264010030428000700905070810022841030f02417840700d01e000003c0410140d0038000a0340450b0780605004054a50381c1c640703450b24a0705c0800101c501c2001d0710410028440b949071007021640195000400c80e1019840d6549049059000045048242c0100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 126833561 1250 126832311 126832313
    0x9070e060a171009050304030b0a020304150b031e0d0801080f0607050a030204081b1c0302070b0c0309031504031e0c02120f0a030801090c0503040b04020103020304140312180a03090918 81
    0xf501c02d044e0a00c0c401e0300555030b503070301d14103002440001c090040320105104005000c00100c4a40305034422281c500408215010000d0010781004940203640c041182c8040102d058001d000c2910003031403070607844442d0103980300d030a00c1c0d81c0d82e9100340e00b212140d4047d8000c0749038240a0b83c0940103811540c98050700e015221014642400b2140710703081507018011058451038502030700640d1000a6004003010fa401c02502d00a44d120018810841994800526104041814011510200da0140840d080c42c6441203a40101c00320032a02030300002c1c0030761301940703411480c100090f020010ba50303212354071a00981c00300209802c007800310744824414060000c00604d018022076004034082e4031403a0440d032400d4200007d1f12240f0040100300303c020010070000600d6404a59041070302840d00503103035580c5181582c1c2d45814683c06240521001c1000c01958030003520191281005141080981d03270040b0010340e030b448045400501040c01840c09000e46185584440d48011035003058450402c11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 126834811 1250 126833561 126833593
    0x9170703050310090911060d1d0c100c030207030803070504090c0207150e06030f0903090901080303040606050a080604060c14070c0f05060a050724020f0309070e060a17 74
    0x104180440104a000c42081454003c8880c000000e1400d40c0040c4840491039030740004d0318040d0010316108880200e0480c11240303045d40061030f0682d82c070f030036150700012094519030f50780d40da202e45910a01c00541d21440c510b20503604540c4083d8540c0040c02600c1c21540ea44480b034000509103000c214060100040903511401543c03c05007254025001503405d10078401d2140c42d81080c4030007405030680b503102d00e54403181c0440398000440601d40cdc3c81030300c0c1c424050381103114882020345e10003250740010603400004030045018505c200c0080049a0b614001d0107010b090705c2c8a8800c2c0394209038002000300f6000e40010800e03286510300b100d481303001c21121180c503410080080c1e500c424024018013480c1c04000720305010304030894000b4180512040020040d100720000201310402641500c10160030f000c007020050380f210101552924011400d08031182c104030b40c40b0040e4808d00d8800074052100d4023034a4011100542240742007400e04c09041e8032003404c02007018083c41900e0300500c2e0504 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 126836061 1250 126834811 126834817
    0x60501140a09110f1605150708090610050103020315100207081b0d0311100f0912032a090806130b0702071d0a14011410030509100917 59
    0x50000c042410405041050154401481d00184400b51911001c040e1248004042e5000700301c2107060f4070340e40c20095074000f80c03488a084004196208588a11075014062403445100d54000d40d01e481442d903c003d80180d0303481c0c0541711190001030351001840254404c0d0001c5602c0f8501e11580305540d00f140380415140312003e4000001a0440c0009110580c014001031496468514150415078036240028610340c3c000200101880000c15511500c00d2051000c86009481d14a040220100e0401c400f030142c82c100c4003c64035904c8400740c2c0040d803402845840c0c403a21240302c1d103410404c1c01c0c1f40840710a4820582c500b05101a080340000c07140e4041002c10f00c00c0b807044a410040c040540b80c07001d00100054040001c0d504188400c0c0302c600c1c1444109812001c0640c0c008003142c03903c292402c0182342c3e042c030201640d4006000400e059240b07010140c880c0c581654400c2101d0101c60044045039000e4858140c0da40002ca040e0703d0065164106211a900450303804038402454054040564 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 126837311 1250 126836061 126836069
    0x206070305071a16020123070212030a1a0301020c0a03050f040314030a02010b0307081906180303140c09061602150304060c030606210509010f02040b0c0106061e050702010c060501 79
    0xe5080d60401c850507100c071380340025a6015000901101c0313040f5800300040c2d4001c0d81750310340344407041001034002442001802c0810800c00c1d0200c0e0349091460b1040c0152018081c0f501102040108910650505100701c1d0054003032800a81072207119a42c00b01d0f081e41c0b01e4188400c081a082c0800302c007092280d52a40d00c000e080f0801141e4030389941c500a030075202ca404200303209070018003040100400200ba01d8207001c03125540c040041c0c0440c174204009040400d0f681c1a05c2c24140302032000c040d0968411010116100b040d00d003d0707640c22014213064452010903d8005c10184401c2c11000c0d00c5004030840e0510007043c1c00d079041284d00c8400303001e400885042e200030b52034450210b81c0d141c06104040c00b03400d13545421038101c88548a200c1440515900c8101819910f00015140c10740a50000705149450301081d507503103a540304078403004e4004100d4011554030f041400140700e8054074080020780c1c61303054007803120800080203403240c5d00300c5081a03040c052400c0d84440064818480c0602034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 126838561 1250 126837311 126837353
    0x106020c09090f15190510030b07050403120809100b101d04052406040506090d02040902100c06060b0a170a060308071a13051009020d0503031e090316020607030507 72
    0x68a40020b03a200e140d001716043c80210307443d007018080340104805401c001d480e04001c54042da925960011191446035510140c014122200800d112071b911282c02ca0040d0545001c617000048003184600880320401c2a460f40640c1c0002486d00c00c0b401159800c000031003000449c0113a01c61403002c0b03015240f0403281c895010100f0540910710b41c83c0840803076030094068450509050030000814000d11850308510321644450801e50110b40e04d0760084400303550b014043c00320328a4540005059180302c0350084400505210001c01c4482041e000e8a007178403e5580c0d8448000141aa00d00240c600a40a40780342e81d10f0741d4000c0045a1150000c0001a00ca02040c5102000382030110005603809000d59035040008618000481c0d80005c0412404041b1900001c11a080e0320000321000c0e400b80f8002d02d140800302c1003024280e401001c40c0613441c01800a0f25040d5104400561a84100031440c040048140c40b100c015040903406001c042c1c0c4641011303407501007940c840e40c00c0c5041030244a00e407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 126839811 1250 126838561 126838603
    0x1d040f020a05130e04020a05010305090115080d0210090c1a0c0a0c0302040e03030f040813080a0f060c0203120103030513271503080f030901110406031506080106020c09090f 76
    0x155407214080100a01c811111138079242404c2d40060800500c3d8400d2a04041d20342c0c000c034190240a41c010300c4080d00000108101d544e40b140d00c41e440340003d000940140c01003110070704a0301c1e178a010b41c8a6443d80410f602c10403904240c0780c8140403414030038900f007015040c00364102e400c2c403c1000d003810b9070188880c001190300e18410041038540c01e00303040700316801c20300a00010340d810744981c40d0009e030702501c201c2d2250000925507003444040d0b4040070741d510900d4000300038808502c0800c1c045c5801000c0c240300b00070300c0c00e800366528481e0b084400078940c060030040002c0784c420b1000d41386c50703000c10000c40c0700540e84140080084003050034030010102054144650034010b481102e01e102c940b4610100440d02d9074030b9040e610300a40c00a0b0941c04000000100d0091080d400604540390f9030001c00c0d200d648401008008195850460b9401c0305802000700307056004505e114102c800d40d41c0100180c2503003c0901102c51800b400348a003070301c24200001841c41090121180303141d00c00c550140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 126841061 1250 126839811 126839827
    0x301030605010b0f0a0e0f03030a050705010b090f07030b180901020307031a0f010e0a03080301080a06050f0606041421100b040e07230901030b0403030e0d1d040f020a05 74
    0x4031101030b4003804012200b003101130380b041803000c1034540340c6403903080090038100d0b01004980d0885100b4142d59240c0000191404866006005481c0040c0154000c100d004114401c1c0602c3c02403d071500c00c2000d03041000202410b2090b00504079071200540b03020140d1040e02072408042105030b8501c071469402004106059905200d0001d01208001ca121000502c0a022407854011541481d04210041c4901000c42e00c880030840001e55020060607942e680d54510540c4544400c201110780d40c1c10940400c031ba0700c614003681ca0050f4001041280703083e181c031400001c1c04110440581d000b04c07926040494502c0c62201d14013040e075101c40500001640c40c540403044500d06a4500d1250345411034800c800e84000410390103981100e441d820880d0340c800c141c05c0e100c840360381049512421754030011041105a01915000b18443d0321b003071040741c4041052544400903800124002040841c40000003503400c0307000c0d106800e0107080010f401c01144980c41c1a41e0001c0e601c2d401107a40010009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 126842311 1250 126841061 126841073
    0xe01050a0911030a08031602120d0204031703060a171c03020a140f03070e15070807020f06090d06110c0102070c03030906020d020303013507180b090609040f02090c030103 75
    0x86074980c0440141048a00655030328825010142490f021414a00321000e1f40ca4000c0043d110803000d4141e04c1030b140d019924000d0082d5129000841e48065421050710a0141c5107043d20f000300e40003032005811380d0070035a03c0d0103541041c4407050054841c2200e180160b104000c1c01c5845031461380c3d0b000d80d9802003208003070700e034003041701407243d8800b02006000e500006c20300540c0c3c0c111188e49003400d8814078600008040c900d2070601020100300000d0079100b0410410001d0202901c240e4404d07070080030a10411400340502b042080d041002a06c0100008440d64001260040d540340302030b051554580f1940d007260080c54003190203840e010f0007482419040076928006040c40d100800000300500380080d101e01042c410000901782d61521a00390411041d0a40c100500d07080c841074020503101c107080e03900c0190344240140b800c2c0010755204c0315860f6018030061442c002d80f8401490301c8031024842c0200c4020415502c1144501e0100c0059a60185182c040c20101c20007a03282d5044d41000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 126843561 1250 126842311 126842333
    0x3070e0907050c100515030f0601030309050d02031009081303200409021e0604171005060111030a050f12010303020d030e0a0b040209040c030c180e01020406050405060d0e01050a09 79
    0x40410b010052106003e4150002654692980050800310341501d80e510721000d0202c0d592003d5625010f00021101c1c1c0c0d86000a5083c102c80c00f0b541c40d200c0e426999002d1003074480d007951019400d038000d40c1044098a405401c40c44150384100007e61814940382c64035604559580c1048908144940031443c0d04400181080c5403074808403002c000c2021240d0010700c80e4400700300860700b0306074200d110201b107964803c240c90081240344424111500e2020390b5544441c1c507082c6582c041c920f008041402544241201002419040003d510700411143d0650711900030142c0034003c244200060a8201850f4000500851080c0c0090440100c40e02019046e100d22450181c0d5651106038000c000c50151000682c2003901514842115150303810a5107280010b500b01815044048500181d44c01c40861a5210714080840402c000c180010400d801e0b807060b4440d82c0300283c001e010a0029203880310040004000140f07000460600c07a0006609480f0120350140c055903445042d0801e110044040d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 126844811 1250 126843561 126843571
    0x906080601060c0f050c060d02250305030c09040b060a030606090b0903030307030506060d0504140d030e060a0c0903060501030807211e05070203191712070c110603070e09 75
    0x140c0541d41c1003420081c16501c92030700180080015018400034082d0a20a40c0c10700440940a182d5524100b014030019510044000c21803186070032007a01c0300015810201c89003903042c0d4500c1e16584503002c641e0845d0304441c2650754080e81d42c0c0706031030807650b81400518040c510b0b0344021581d140b910310301501101c085d6101c080c590303204000c201000c2c1d41c084110703540b1054901300051940c80c3c00011805034003a5105d00130001e4900000d01007031180080040d140001e09008480641c3c02c0715000702d054450600821101d0b52001000c10500401c1d9003102950a143d407800348042603807512a503060b10802c3e84181c44c9031800003000002e2124204140001e941c0b0b032100c0c105080022840144141482a0300130100d4100403400c0840c181300e1800c4440f4a0380040485042044130019001b5a500c01c1008417400c0c13088000d841e200301d40030303000d0311f08403122028070f1017066503a0401521103c800d50b0084401d02d0400c0d024a42c0c0350b8034a00a58064a000c2e917070782e950600c004060158801c00544 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 126846061 1250 126844811 126844813
    0x15090f0305120a030906020d0515030d0503040b22030908060a020a1209020a23090907051c02011404080606100201060f091503020d08030a150b0f07031403010609090608 74
    0x110600c04614005410342c000b180072080c80d41c2e030741c01228045005014401005108600000c0c1c0800060442d800817401031b45400b05022004501004059850f040107a140300411b60034400a8040b4050100301980300c900a1001c0402c072100c0c05182d04405c00da200203c0118100c1c03102880350000800c82550701c080081800c52070060f038104040d00f2840030640910751a500e07103040d4800c5440704105003000348102c81d0014021a000c402e0062818441c1d069540aa04807800198110100240c0079085910190214401407507810080c0e02c540f0748030200742d050054060105884251240c01000241004030107001d176401d0450030484247ca80c0d05050b0110b82c1403100074070041280341c004104403000c03031130009800241000100f0032104141d101030750084285964500f8070428000451007096141c41c104250120000c2e00880c07442a40207020030310b80240000e60805599500403c200c502034103080f1713642c2d008090000e60540c0709130002c01c006988910100040c4186006a501420101e8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 126847311 1250 126846061 126846089
    0x603110306012a0c060c062019050c0d0801030506090604050606010f030b0603270105070c0b07020a0501091103121608090112061d06040207170c161509 67
    0x8000800301c40b11400f000d00002c0c1240b85002c14890303024002446503a001d24620703c0b86544038005400300c40c0c8040c09070f43c9a42081504041544582014010380c03190404240c1041c95030711506202880020207801400400c0022080d4031b207003000341d02d100b80e9080e96142e12641c1189402420b002010b0500b602d00c1e80910140000681c01054a03903100c0405e107800300c0c0e00031942e04102e0240c611002c0321a0048000001c1c02081000c2880401121140d80700581c4d4481001075690b08a480842c0c0000005030b185900100040740000000c3d0050642d20480309104500d40b10b44d42124101c4070300303e0310240d01c51a01000d44c03d0522000c3d800c000001070490610251701200d120110381c000d8000c0402c0170000d0b540020340c1c00703403c40412501000000300803207921611984880003440c40c03c40581d055120003c1c075180350a000305e0310340076880f850840b040210b190041c0440e8124500c0715034107000e03140c0614a2010b42e1481400141480b0017a03185030340b01d080001c0c0200071160081d82000500f8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 126848561 1250 126847311 126847321
    0x909020c0a14011e050714040806010e100311010507030c020913020405150102120a020102040f0b0d11160303151d060f1c030c080d020a030207051005100e09030c030304030906031103 80
    0x440c1928889400d11345011446139030b104000ca41c03403103280d10118948603000c1004036500c400002c0da54140c45110fa061006a100c01d40359005015603444018050205884201d00300d501c2000604260361190429071004003203a40010a513a000302d4031501c103404959503400962600c0d01459400218249400750034202000000307460358802100c842c6201c0000076844040d0340300f54101d030300a011042e00e0100c40e41d1680074138503040e840260146a440d0804080710809102041150110341c1d000c041075140c00c070503544c1540034000c584070203614441e80c620001014a10045101c01d8003001c080341040340e00c0c262040100301c1d09144020360254014080c6050612500b184c02201c842c0c06007002d02c002d40140c1703800d0000303110b45403241422a0000c644002c1090b05500a410038500c00d01c2500c0c1d40ca61000300040885004459049405001d91010004d00a00e03d841541141e40c02d400e8a1600b000703400c08a00d543d2082c0e5044001034030a0000300301c41c561601c5890322220600d40c04034514141 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 126849811 1250 126848561 126848591
    0xd0201140c0a03090f0209071106010504060b1b0709020a05210705030402090405030918160e09060d02011209081902060105150c0c03060f100806010b190909020c0a1401 74
    0x2090110014150f48a040406204180c12505171160f4002c2c81e6029510f04203600800250040c0d2440800f0304c240400410301d032a080c02803a096484051056040c070340d08180c03001c20441d26060000d5a801940d00c0071404078814001843c0c0304806407644ca03035401408107030017075080d040c0603081900d51090040c8004103502808498019030126542c0a05031114140241103108400341c1c6540302d045845141d5994031003c101910414250468140100318900103440400b0000c1c0042d074040070900000d040791422800c0c2440c5540185081c40564008094000440c2c10042040e500000081798001d5201c0b0001c42d9540341480920140c0707429494000030030242c039140c510000c2140d0001c034060301301a8040100760041e0728003d003220302c5400e1140307644800c80000e588500d51854a54804900c1d02400a06a412680c155801d01e2511003850741e1288411102c00c4880100181444001400400c900281450384420805444030444e20328115025615150750340c111a4100b0b8001d28002d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 126851061 1250 126849811 126849817
    0xd02010e0703030503101d070e010804050d12060b0d0504050705060c0d0c020f030d11010501120203070506250302010c0e0901050603040b0406060503010c0305101d0106051612020d0201140c 83
    0xf80c541881900c80d03c2e62044100c043e000d5030024042d4540d24158190400c2144c41418081c805640b100340440440c40c00450700042c1c00c40d00074003070350f1100315a0800d407442461810b071030183c440d000007182d60b10345030801d403290f00c0200a00b0302603840750244000d111050100c980181812100c0b149003a01c1d114440d5105c09080c9052424003035401d01030400e64130b60f030103c070091620040c01c1e01c200901907600980f5500c6960714502e2150300c3c0000100d41c41d0109042600d41c41d40040c01802e141d40340804100655100594030650484102000044a4105e140c003c006038031a80010466000b0320030000d04030b0100980282c4a034076030400403c80c5486040c00c403a003250700300c80382503190b80d00c0d81064000b80003554000758241d131803c0820300401d03a05501c0352f07001e23060303690101011598965502510302e0f024550a09030a0b901070040004038061002002c58044e102c90b0900700140303030b07102d615143c80d0440e02d03a005030b00198207410034164207109820b80824114050442410101c2805407540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 126852311 1250 126851061 126851063
    0x190501030c0915090905060703060b04051503040606030c0b0c011b05070311010b0306010b1b07060e1c02060f1209010615030f110f09090a0504050a0b04030c02030f0c030d02010e0703 80
    0x640d9403070560b0f000c0c002210360a800341402d80300034400c107025032030815652801142e02c000001e19152000c00c2124160041b501110402820851089030005458216601c0680201d8180341e44050001c0000c41601610004040c600b25980c0c40f920320030310b09030035900c0603401340942a100108054000340c110042c0c03841e658041c1340c020301c5600400142801005410211a8148a01c5000040182c0810000c0909412800080e894103508030f0300280d44180300e000314800316210103a088002d0030306468902c0400104681d0840d0b5040e90340104695038000081c6240104000034542402d107411940b890300321103040000c0100c540381403c4028131750700542000b001c0503141c000034040c6100c01d400c400245145412071a0391480460840c03112a40211103081c080c19220f000102030708190f10500d40304a401c400606150045942c900c032782102e00500840501140c0c80070440543c07400c000b1031907071440b04c0e4000c10707503840d1f4002010300c2d100c00184c44004583c1000c880030390000c8089500c004a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 126853561 1250 126852311 126852329
    0x70810030b04030c051f0f060305101e0c0503060108070c030e0111010204081b0109061809020918040507050a0f1217161109070305040b161115190501030c 68
    0x203455034507040b07a0315404e040c0c002d007551091896600120720b0320014401e04a201c06401c00486840041e1041500c849200141441c0c10081c190761140d121034201e40601c0042150034102a11200b41480480b50060f500000051000c02040b0041d41c000480179005005820309002003a0390341c0e80106031080c51490389041241082511200001c2501920050503201040d202a101501d04005004055182141c0000c0000400280c014014110041040c1100b230710348510300c1c10700e4642c001a60045902c19004903032220b800b08030741400b40d0214002c921840c081d040807031503d02041800005031700810355540d0803490403c050f002001615003a654000c003001d201d042c411031344030f0040c084c5459400c03451580d50048401c11102d026100c030a03800c11240c4203082d896035141202143d00849009003c9441d8030046501c1c0b010044031820b0041c401e290107491704040803209030a15485980c9221080c215506000075a1843c4450b0100c2500c1c4010401c500c1d071441c2c40c1c40c15400041e2081d4401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 126854811 1250 126853561 126853583
    0x405010803030718090e0309031e060103080711060d0e0d14090103270b070215071d13020c0304080f030903060103230d05180f0112020a0c06090605040b07081003 71
    0x2e100b041020130003829200c804001c404e00e110302c01e80c0c40e81d10042e4168402d0040c0481e991500003422000e5880511000c010601d41c3e08541c0c4858647d4044d03002601c03500c040880c00301045d6280c0340200780361610310030007040c1724a465242d54030b01b07030006100c03d003800b0754a078494805042640645010190900e03003c00d003400d80c440040c00c00e100070315441748520442d0744003106001403103101d1030041c00725900300c2d0308840400b019402e07d0801601c190000410400004a61011015040c6400c03d401010750300b80007030180510040780e0148180c40b8858002090400420100b40590345c5d0000c26040558070f008500d00010f9120841404001c00703104244134040082c0360000d5100180380c00079011900c60b00d10b04c41001e410b90300445d078942e400c00003107030750483e00e81084148401d815606840da044100003200c09039000c2d42101500e001002040d41d48800440c85a004a05003207009200c001000c0c01c190500c0405040700801401c01c1c0f0040c40c0c18440400c0781c101210301101e420602d0204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 126856061 1250 126854811 126854837
    0x1902010516020a0909080c1501030206031308090904030906090501020a1707050327041b020a030e010e0406030c0f0e090a02011409180f090703080405040f0e0303090601030c0504050108030307 84
    0x2c10303043d070f82e003000d6805031500d10000c3c200480b44009150340c1c203000003206c107001c1b0b03458164100c0d0042400004e4010a0038404104040880d8241c440414070502c80e0b54241062003000c141c09600889041e000a034607800301300522a0000702c80303400384c50300b840034201c03203001034681c3c000881e03c80381840202c040008641003404002d005440003105106081310000e40c801040c03113480f00f595054244164500010340c803000c04070f42680c040040701d98001d011034660689059807102c844142290521034804419401c41c2c0d164440d440281d8031840303003540d50604140003a11442c06a4100c2000d0031441d00600420050001d09030098a0707091074904c08001ea28803a51807180180d066a5801c240f05950041e4119800e41501e4810750085003001c0003540c4004642c1d6441d0164440a05401070402007806203045c80d4210071034a0540150200301258961217142c6598070031100340120340c00c00e50040c010000c8401321840204411074050029505121880380c40780700180181041c4005100340720 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 126857311 1250 126856061 126856069
    0x18140609030f0307140105220201030509252102010507170403020918010506042c15010803030f0a110301060324060306031506080706050304030203070b1008190201051602 75
    0x104002c0031609503500d031841440e005c802d40118599a034440c0d4203050006015417031682c00d100000203a2140e103149410b0700c1d00191b004000181070800140100c102075002000321011123111103034469500d000e0285010b4541c501140315490340c1c1d43d03088507424400003503a40001a2100b4540290745040420030000c0585039912407648000e4100070490104014521410800d000c02c040c0c0c2c1e8003d00c01030f0f56640810045800d0011944034691400c02c280c100c40703440c0c0000b00381c41c0241100715003e28006060112100009074001c0182d86c1c0004200020040d0004c410b6030400010071040c002ca030200840c441145c001401490109903172010400e00384000070070b44242848483e8010345c07000381c5031040100603140501094444000002c030401800610b885820704484000000d408030358200101158a5407000e0029021840140407240218000394003c2d0700034002c00841218080c6807000c55424044003c690410315401800c5900250341c1207001c80c0c007480045a000e5640542d184001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 126858561 1250 126857311 126857323
    0x308060909030405190306150b0d0209030a05010219021c120c18180b01080c040501081b040603090c091e0203061203030903030f1815040618030903031814060903 71
    0x21640302d0005e1901c0c150ba002c03442c0c43e03038003070300e01401d028005421b0700385200c400303100c280c402c900030070034108490300702411a40c2c007506232110001c6c26900e0000e801d403103441c00c0e40c00c4016800440c001c83c02203c02520b404101e00000340c203207407444440803846000064907504150b0880656540c55403400041d25100315440c030564030501111220541d03c0d07592003034080a07480c103110306070344c5042c0101510b98003d2010510500781c10210714034043c109001101d2240c0003500e800c0207042441811801d00071000d003d0005010560f8002945003c039080140c1402c2da29801151038915261000080c00040c502c40f141c9480003540260b82c0c0d032170780c4020440b008164446003116004c0401881030001c00400254025007a00c0001c800c0c81d2103440801c0e0450300028102600f0380c1c442829242108029001e83d0b40c882d025060020754020180085181c5003d0840c04400150030b000c0e040c8200340d0010001c040440380c940429148604201e802ca074910300030701515200e00b0010902c1d4003195010801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 126859811 1250 126858561 126858569
    0x203060a05030f06010602070f030f11030a17070b070302090f040b12030a051803011416030b0d05060402010f0305150f0a091103040c08010b010807030b03070306021c050f0403080609090304 83
    0x300c0e921800350b03c81d11512070000380640c100500a960000510600740881c6000f1340b60847d58a00b4000740ea6900c0180f100c59000d0038a0309400303007030301250210340c000315600c00ca40c0050440036512001803400c0c42030428001c02c0c50b42498411302c00307101d040c0c5648074041d1138134800381d40004400444000280c0180400404d0420a110006d4903845140e03000028000200212040b0107400c07022000301400da803840d085996004480300c0000c1d0140800c1d0f80c0c640100c0940d400c0004981c1180e40100b8101510300400303030380c5a0310220900045503404050135080d41e0035460200035904040d0040c01e66010486419841826024001c820650780e80c02e520004112080c000c000800d440f0741008055001118140c2e90140f566900007404030040c00780000752001607541c68210750311110b0550080c503941c2042c2e90117108100000c00090b0f5140700801c0d80b2564080380854202c10107800c8001d603400108071080c50700c0b00c14240000240c00c41c02c2d081d00504102c03404aa0766840817800340c0b440c019948 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 126861061 1250 126859811 126859813
    0x30a090506130509043810060807080c210402031608071a0c01090323030405060c2b02041a090f0907020a05060c190e01021f0e010f020306030127060203060a0503 71
    0x121700320024250382109501640c0f110b200040c187d403400f01e00d00c1c00603e140f2030b4402148500001034002e03071241446961100ca0005042d08060200b8103441c01643c81d98182c0c4c540040700f805100c25441c0810852090300702c0c1c0070300c2e4880e144c14030f800030b80c8a100d00d2060381208004121440400d40c00307a0f0540300d600200100810901045040081041a01e080ca413071200150350030b400b1040e10644101e13842250880e00900a0340c440500810786640040d1407150300c41084c601c8406a40210003588201401c5513401688039803c000641c0d00d805441411351881d1b41040040c01c1c0c07a034841c03003991120700c14100c0e02003140d83d45c0d585090741802a5628002c089004002c20070611651039405405d03200601e03019103041140703090041d03a21401c5c80800e00e0240e0b02000811b194100820358503041021070460220b03ca4100e24801b42c03e44000b03140c500ca10030b8001c002c014107400c0034441e84c10206003500441d01940f0028901c0c5038104e031407039409494260000300040d0aa240c41790491300402002d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 126862311 1250 126861061 126861113
    0x30e0a0e1603110a050313171207020f0f0a080703090321120209030a0b0702071707080d051207111204240801050a3005030a09050613050904 62
    0x100680d20007440c62a40840440c0c60940c0103520300100c0300555402d59034585840b0301d15103440e000700c1d01000e40c5080c00c0300d400e058103481c0b00d19100900058090700c1c1c440d03e0708401d035090080c406400c106451114585562088004010420f000109550380740d805c0103050350380d0082c074101190380b41d100c1e400282c01c4901d0300d540407942d8144104501c0a24809030707140d031000108449030401f644940b0300b80c9a8181c2c844c40b20070b0301150500c9005500080b1b10b00440e0710142d42c0300d003158075594510b5040c810036080140100802c003c24013124191402d1403925901d00b2818100614000302c0140c604000c211250389420a4100300f00f2610140c00407450109440700c0da108042e25001c0c54a1074080005c40c00f5041c0396828500842800d4166030004040c2000c150400700c078400007000144a4039014000c00d41c1403808040007002c48141c6d14002c0303024560f40d46030424040e000d001c140e80300d81d004100410480b001000b1103c200000d07503404403035800d0151501d0500382c0c10000c810381c1007a2152101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 126863561 1250 126862311 126862321
    0x307060c050105100302060901120f061401090f030308070c140604080d140f0a2c07290a0507030201021224010306030b0402060304050f100f050901090c03030e0a0e 72
    0x201004400c40d600c124028040d503510714207030038080c22a911000350040b03801d00880c400b540c007440381000060114400000c0f205030b401d000310306946c41580464407030190303066030030841d5a110705014080c0000380c80180c00c3c10b141d560010700191004200f1401c02491707168100401040183d403100000c00081140d0131803c190074441104c0c0e0041485040441c544201481040c1e2030701104c920442d00d81d88021443d07034491481c680a403928403010310480541c5400114181c000d01e03500c00510034520700070a0101d09010000c0c4540344596003164100c803191340080403100d543d13002c86914007020328007107807a85128941a03019006400c43c0c40c01203401042080340c41c0c10101144c4241101c180c04c84c0c0840121140154116411400007a0849030050006405410004000c6401034801e508445600d20b450003140e061903030308400403403050345410540b00142480c0c010340d9000080032008004255450750f483c40440c045200090a01c9500380500009580b030034031000081640c22102d020500e04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 126864811 1250 126863561 126863567
    0x4031803081201120203060403140c030301090207111e10091d10060323060307080604060b030d0f020303072a0602250206040e06041107080c2107080c010209030706 72
    0x100042d03009040d4000400011040a0f48102c1109650060090042e544a5440841f4013440010441200000c10021a002110100020740c000c0450880042e2942d0242c90b165425400c075800d07481c411485c00d40301211110700041c922054460440d10343e4290f041003403050b42c0000a550110a0450448103907200d004040c40f0564031845210082d0300c105501d505050b41100c443d43e0207541040020140202c1a08030007000f15046240281101e20f0a9a0707203544130320300034003101c040758030580310f401c03070411411b0410440402c0300d06400c202c204a20003120007503607404000c2c024410003404405681c4510342141d40c250001140300205050107116041c0000a03520196004640049070b0400300304102e10301003042e40303482d402890f5a1500b45003140c0794031020f4026054a502c81d560b0308030008880c021074002c02200348a032090035151505050024241064203142c8201c820310403a0040050065504441d00759510181c0300741c95075416902d0b9070090207070721030203034040c440c040c408107507590 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 126866061 1250 126864811 126864817
    0x915011205092113090b060c07061d040513020118030b07051e040509040813090204060c0210090602100c030e0f1e0d020c06091903060209030c01051903050403180308 73
    0xf4030b14107503d0b000078800da010b55082c410b2410405440a81090500a82000340c02071902468020112070404418146690030011582e2080010465071030304c2443c40c0410011551803458110307800c005518103400b6004100d9046400213040081c4020800c3c035403545482e0540146820148003146498460301c060700a9122450032503906007914941141200603008070381c29544050648030780c1d40c40c2c50707403607041a4014003014603c1d404402c00116281403648060002006540e40790f98114440740144066009a942c500c01000080f44e414403c1a4000071404c24034400d5100020f070003c0c010500314000d24a20645141c24080c0c103900150000c400240900c103802101000003402d040e00d56403d82d202480d1036041c0168101600a5201c3e2034100e018010780740021b07041401d01e402d61078100c81e100c12640c2080320301550109000101c2c2c2004c0101c0820550b0a00340341d854181140d00c035461006811a20004041e150000a42050f10a5a10260030400e0003a5280e440342c17617282c1015030350 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 126867311 1250 126866061 126866083
    0x2070c03032105010510050705070e0906010f0b16170d02030a140106020a03270e0702100b0105040b03040b1308070605090c060906120a1d1b010806091501120509 71
    0x15161540c010840f0321400d81210801050030f43c509461090581b6260810b40b42958113009080d000101c40d41c03c2e0340d0451051003030801405140d81001922281c0301f020341c00050441c0420f01c481d894120251115482c0306400c200a0212208000c46ca8000d500c44c00580b50a414001b10500040282a800c406042944250650381c00da8031440100ea940c68281400344c0001c80c14150481d00d840c050402038401315000782c0300101c840c0c585144010020003a690540140d204d40c0e00351080b00414400c240034180700746459481e191a1030280540c0b80800780001d440079100c072000c00e1031401e4440c008009030b86d001e400c00c0c3d107a04c1e4504010000740700880382045207000340b502e00001e03031030410b048a1a0090040c851401d0010a03229880c880301d00405090360b203660b0344190751441c02c8008401145407006401040000021072480941c012894281ca041c006c0712000d0045541d2051802603208880c0c044205c0c0710389101c401260440828603554080603e86802d100c05030304007003110150b0b5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 126868561 1250 126867311 126867347
    0x120f02092701080d020d0e040b1203030906090f0a030e040f091a01080d0f0f020f0708031c0c09050d030e040f020406020f0604020a12020310020408010b0108010602010c020303010e0a02070c0303 85
    0x80c2ea62644026181c07215141204016000040781070410750050413030718280740000e8000100905407038040307109404030320690032940e40044104260300e001000328540c8001010041c0040280d0f030015184e4880c0c01d40001410301804107001e80d015100d9600461a14410300c400744803085440c104480d4a81003102c49031102207200c1f00110710304400240149220140390384004102214100c110740380c200c088954404c40c003419100c4003222004102c1080501010f0001e9a500c240c0e0310855204d86c4005007013001044c0c1010b40380c82078139400075140c0c01110800e449039401107075589001c54242c5201100607502501c3c00e01c965200018940c0580161801c54007120300c0981d24138072155448000b142c0c000d51089400805101803a242110001c83e9440a400c886010511100c1071040c3e130040e402a0255039503e090b400c500e0f40c2d124099a0041c012400204545685000025220b1205010b00c010050030307580803500c129140d904440301a034000101c01801920f9180041020f59102d550300c000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 126869811 1250 126868561 126868639
    0xd050f04050f0102030112060506030114040b06180408030703090507080304081c03050f190603021e09100e0a02030613090c0305060a060b070605060d0506090d09090c120f0209 77
    0x101c41c1403017100d050300e000b4512848401c1003a40e803500605401080260155202d064001c40d80c081045464043e034480c2e541200d15190040501900b0300230403281642c1c4000d04e5050001040d024001c982e0401d020b4030300800c3c44107507401c00e00c1c07521039254400c0d03a49101c00100041d2113140403441c106111710640100d0805c51507400c044094407000c1e0b804402e881d503060041604c901c101c01440c100c0c082e41d00e40201e9a15642c1d00044c28018008583c000a5024900740011918104c034800f40c1c0280b54404045d541424200034140b40d103030041c00c6040c100d90000200d07220b50b80342070001001540d0480c0602400c001403811082c00c0c0d0481c80308603440d10a500104041c0c1c206401108261040700e500c0b20304112140c0c5592024103805001160054200380b00d107000f2544c107000e42c510402d100001881c4410900000526440183d4480d00d58645000a0075405035400744120b1541410308a0200b251340304400903000a00c0f6040c21035600100c1e140e03d2800360840f01402c080c91072425070140c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 126871061 1250 126869811 126869833
    0x10806060405071d0f01110d08040203060106170a0903020c15190f050702060d0b0a031b080615010e011101020c010c0e0d0816030e0301051014010207060f0507080d050f0405 76
    0x103a03512440701081410b005084c0c00e04060a01007840f0041150500d40740c00142c03030145440e401e01900e566681e0004030351504000a40c1010030225006100625002c07a0341d0103104eaa41c402120003a00300c0d424682c0350102e200903d407003002001208000141b807a00303920280304441e0705540c4030200c0354400000c07000030344070824001d407209100340c1010b4441c00c1c98848540d0810855a01841c16400095070b124900700240e02e40c502600090751043c034000c0342140d0303080700000752206190300034402580064200080b808031081d21013602e000a081c40d2403100c00d8070300117070340c1412580f554030036540c800724048803051415000078040091980350400612503d0003032114401c8000400741c0b1560b410030030382d0250080400d680c440c0c40c0c003d00d41800c0303403054100001e01751103040c1c80d10007560103007040a1251102d40003800e06240f409000a10009190040c007500c074200b190260320a0201c04581e00b07003400300810444000e07501c0000704102c1031a002001001d07031141a10152101d20590001403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 126872311 1250 126871061 126871067
    0xa0f0615121a06030c060c030d1107050f0d050d0207080d141005010e15090d080d0b0f0405040b010b0f0705010216110a1805070c05010e010501090b0d0b040f0c0e01080606040507 78
    0x10f0300494002d00a80241091030f0148107081e8800c00952940344070400c51034620b440503104280354411a8002c060751901503041030b80c035054440340c07405042c0d00800c3d0000318468002c01103a80c00e40c6c2029025890383c165040546031809022951039602e0b0521050b1000d801e05209084c0c07007600c00c04424040c10b5183c0004440c10481c81039000c5d00014003040c1d902c0c0e003841c0c2402a092802c00140310441020086d0b8400080741c00c0b0040440c0c120f0f86540c074025451030006070704010100183c500b001149042c1d03d5202c0750034010b124600d40403800207000243c55030508100c480c4542c009000759540d011500e04125109202c0d00f05542c040500c03401000382d0314104022038203d0380e56a100b1000d911074800d02000070400546442c0501443c80507590003d8402e000d541e04409140000042c10742c500058001550005001c6501c9400740038030301e000041c0803040e03031600325410000005182c040d030328044590003025044014945801c000001c2c00500010755030f40700740d006131410700c5540c8480320b0039 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 126873561 1250 126872311 126872363
    0x5040506120a110406020709050c070f14011104180c03020306030601090b0a0f09021e0903030d0b0a2103020f0601030c05010c0203070f09020a02010e0607020a0f061512 74
    0x980c004020860490140240942103800411507000011040314000d0640c00300d40c019842500035030441d8500700030295052040d11b901c8a07890344e11915104d220b48d92000c1d106002d0307400604408000450076418202580580c800500b4120301e6591789480e108600716256100400f07603001424000d0b80741015200340281d078080c40c800f40c000e01c2540d0a18900d48003601c00e003011a034016050050001e455440301d204a4001c0410040c01641c0307040b2215480038423006004800c190740410802c07c0c845032000000c803070101d00c80c0840050100d100d40001400344180d9401078150b405909100300151071030846038140c141c03290f000c54403040c424010082d1a02d909100184c40103906c01d000b000300d0b501582c0b2181ca5140700906481d81245c45410503540c414250304a03020300303503001c59000c1c92980c09101e409007200c031000050540749003015000303684000340000101807050401c001d034104111a04182e403c280390070300c02a01c00c0e40320503019100700c289200c01d07070b18034071480e801c555004000010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 126874811 1250 126873561 126873569
    0x80105060a0501051b192118061803050703060e1905031c0b0409050105011802040e01090908040b0c10060e070207032d050a030f050a050315010306210507060504 71
    0xd1241026139a4131084200302d04405a4402c90040e1b518140c806104001030b00c9019105218041c03480010401c000303411916283d1a0040c485103941d0171204041086034541100d18920b40b5000c00b01140c1036041340c80d442a80000c025200c1c41c6400300c100141500049094080d0408403150019074462072105400c40b940c0150480d0000c220500340c8402803031220303140303d001c4c0c0c6c404141064604086401c541c16120184c403665522401845102000503102010741c502000130340c185801d10143c6800442d0612a040c1101da03119564010041c4250544004103400316a19071200200c40c40103031900c0300c85401c10341d0746280090100d07401404002d014043c400e56401440230b0350665886488060110001d845010568003285084a10002400d801c00d4841d0000d40a0381c1e10610300a489146400b9286c42884814084415080d602c00c0c1520b501c614400c035507160100c09200140d00804c2d5513004100e141d15613034901511825408400040c40740f1400807144040d07a5190121140d01413401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 126876061 1250 126874811 126874817
    0x171c140406080c071e03090b091305041b09150603020f070b04020a05060f040e0906060913060908040803091e1014090d03080a14010b0906071109090106080105060a0501 74
    0x24001240700d20b52065124a100d0011440c0c001c1036141c811a502076020240103030000d803510002090b510118041c000d01080c0d89250138075602000090000e086501e40d490695a100f00280c180110845c03130711681140e2410300d1540301e84455409001d0080d461019000301c00310740700018000d1081c400c54941403087c10700c0e030f400c04201e59185500202c000c1d00c10303a070001604002095a03901c3c20000c0519254a085160351549081800c11034808020014204ca4000d40c1c20400c1c162100d2038031692103030b9054541d0f00320710b05910f00207008200340a4003030440c0d02e02003004a44e000300080101105a011582d0840c1c000403141102c0b8210700707161901d0b4010158100007c9020b006900b5641c10900c210125800d00c000440030881d0041e4600381900010324071814406048464821111000001e021008940d8140a5a4440341c42000499070081100042e00002d21140d008007080841b4018071103d12800e0010b4400c0c0030b0082409405851b500e82008910305141060503041100e2042e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 126877311 1250 126876061 126876067
    0x70b033309010312031506030c021218060d0212040b0601020c040e190311030d050103150501030b0c0f130b03011505030f06040903091203120e01020c1b0109171c14 72
    0x2a13120045041e2181c3c4010600d034403141910756162143c0007910240c5910341d00054420382641c1c0083c07804540d00c1401d64a800100300c0461a082d01b244c0e407640d114405d54403e40d03208036164034a0000d2040d441d080d0304024140702840100110050480e001e060240c1c01c0b5401942c0990400c4201c030040d080300b5481da400520540c0340d41040c5072444000901900740103040828a01559085910448a00c842c46039100014070420500030118030302d0f512404c2003048950f0442c1e03150054202c002c0c0c010300c01030030080340301e8040c8102d80041ba084034591680c47d208140e41c1c0c3e01041015007085c0500700e0f0100c04280c0c58115240f0410171b480c070851107611109201d88485082c0001030640310400d0b0100600b148020130541441c07204420042d10a942c0c3c90b000b412403166100842e0000305407e0901c0e401004034601d40c0c0400644080e1450690a140e11074030859070050381c2c3d800d01a40304140203000052609030100d000f0030480145024003540050f9107a45005c201d604080c0c5045410808030b0038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 126878561 1250 126877311 126877313
    0xf01030b0603190602041703040b0a030b06190207180209030703120302040b12011d01030f03030b0f03070905060406060e0102030318100e010c09140105040b030603070b0333090103 79
    0x400056500100c010741076580030b0303041a01d0f4040c040051a8150340050300002c080007031082507150301c44e22400802c09103041c54200074000200344140c007984c9041503119002002142e80f000d0072510f4505030540c40140701458594060340712201c5124803464081c024410030500200b23402102d9031042d0090180c02281e017107960310340004442090041c03c0507800d00c004a01401024010601400b404844000c25858110000e80707400c1d82003070089500c02140010000561003150007440c0c03550604010480400d4140807644054140c2c140c0e550610400100050410b51075108902036002a01c050003290748402054850280300c0e0001030060380200009220a0103404201242030343e024150b84200f1400c000260660700206074141c0a40d648912515039186c007c540440200703131100b0000f55104100380084e1560045100301000b4550020014280c0d60b410301c079a101801c2d1144640703840342007400c1c1078100039400712444035003420309101b070f034050780480f01789011302c10342c0140f061400f40c0c21 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 126879811 1250 126878561 126878573
    0x50f040306110c0618060604140f0912041806170303040308070e1807030c08010620030405060301030f1202190201120b03060f070905040516080c040b1602010909050f0103 75
    0x103401d00a450b215030a220303903c0d00f40d00070b0014500900080e16600001d07210340c08840d04044001e04143d1042d450004030654891003403000d0399000785549043c01c1e1503a6100303503041c146051008644080c290001f4007258043e201c071540030270507106e0081001001d482c0e01c041281680d0310140c0d4200c903030041c80081c002030f104010940e031109071890211020f000b410045843c4042c45034100445410304003c0084281e8144501c0e0040c4046142030242949003540c06099015540d440100012401c60a010b811404000322401080068242c1d0303601d69481c1041000f1000c1071208a5070406980800300741c08d0300c00030301703c03540101c11090002c03617501c00e5005580742c0b581200d11140340c035142c140c40c5407103a4051140a10404080c22280b80c18945150020044000d6810140c4140d1401c001e100003079075800c107948260941801d00d20b080b622500305010850146500285001e42c0000c0d14100001c811440345041600c00c1e00d07010748103501d80c42e140080d1038003180c841024003013040040000c601 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 126881061 1250 126879811 126879821
    0xc30030403090b040b07060b0f0108040816051b12030a0e040221040308040605071d0904080c060a060302040f02070b040f080f0c01020c0d020705090117010b1201090c0501050f040306 80
    0x48281008003025944140280f11500a90320142c01c0000208007030741400124020030190001c100c4800d03607a1b5070a0320010f4004840540040e10500002c43c0e01e24051000d041401d56030307500b01c0b0880b040d2000446880c44c0d5003102c82034881c007400f0541c00d10b50b0300b2180001a01c14210b025140d4522216065052000a410861084416480c0c1440b4105501e50340701230750340598040d50b070360708841c502400c041c4d0a0341d0340900744604000a14000714054041c0315a64181c07840d08450104881d151414980c40c0350145d00c403c05070310b00480c41800180e800b203510440840e032082d2001d000e25000410400204d0250450241038040680005400100456401401070740310b0744000c0e05146054a05c4006070b0844409544560340c0060110342000041044d02c1e0782c11818401040319a00340408a42c40d1302040c03003100c4050900c6003c4107a000400e40040c489240003030a91110b4001c8400c0450180c0a58070007550b11805950700400d29500c101d02302c036600c06241004a281c18a9562050000c0c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 126882311 1250 126881061 126881063
    0x50406030e0304050d1112160306020708040503010501080a1b050a03031110020a0903150608120a03061203080f1005010f0507020a03060203090328020a020409020105070204060305030c300304 84
    0xb010821012034250780b4070303c0780e000aa01400c05200300c1c00c1c5a905001e00e6111070f03c2c002d1507550060240c2c1400190110500b02500d078000d101603103c1449141204481c000d940091b6819420f0800115001c0000a14009158054070210810041001283c4c02d80c19142c064186c014081e1034080c000700307008001095003071002500300ea1100c503004030610100e030000d180300f00003d8035002c010800d204c0780b140e8440c00b01682e014100175903842c20300240d48d103654110444044040c04658258064005c0d0301a400410919a100d100d540503407400618040c2c00312a0760032013020241c045035100900960f600107a0b075040c1c4442c641d207140b5210541c1e9503045035000300d03444001e2200200008040c2d001031030280c0d0030100290740fa06024001c7c0d02070300131200e00e018004442ca00301d482c86207a0005d0450040d90301540c000a82c0c81240c00103c1d80341c40307012000382d00242040000001c0050000080c080c0408940944010a80443c00104450b026020022100100c0410003060410786002103403c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 126883561 1250 126882311 126882313
    0x8060f0607050d050d0c0806030c040e0a0b040303021c1509050c090a120b061c1203020c011b0e0f010c110a1203080901050705070b07140f2b0903050406030e 69
    0x442070755141482d080100c10310000060020410048000080c081d00e01d000895050680961424501180e900d400c0300180a10030f903281c2d1545000c0c41d105001084813950084c02e10031061510741000b402070350040d1001c0030803c1c084041010082c0c0284980d6004a4a16008621f0b05261000143c05004050441c1c1c018110810042c00c0b1a41d0b500f00f1400100950b0041070903200b1182407a80e5a094020710306c9008024034509004800f215039902012103612601000903550245030403802401100f0300a1501c0d881d000d1105801068a200c0785043c10155403040d50290007441444a60785e080d00c07580380420440c80d80500000d6601e0000c601c0500050075208419645030312017040914440d10039004119040140316000d1028012070f58481c03a1030900380d241140c9556034070b050b543d00508003c1006142031410107540f0b821003c4030b4105010702130301901c8403032061184038480b40c3e01501c42660790b4240020120400340703005004009826448040c00d16140c00d00980183c02201000011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 126884811 1250 126883561 126883567
    0x203041e05190b09010e07080604080c100f09020906060c030f0306040b090c0a02011103060a05060c1e0d020c040b1c05030903060f1603090b1f08010509060f0705040608060f06 77
    0xb24120110000314003814448580f800c14041150845000e004030740100e07003040c14144010b00002500395040340d4404001513030307074400100d22810030742215040c00045040000344480090550080341c0004d000311951606521380d00304201041c840c0541c48140c40d007050003911003d25604c40074551041010f0004140003615800160460008980e521b1107030502103840c44101c2e609214217464191810303016850b500300400003801414182c8503041c85144005041c0171084400e11140810031000d95044001400e0440415180c40d42044840014400c01c0171044903481e041c010b8180c0403202038900207086c04030351101101c00084010944040c4010001042c0f162001c0010510404c40010020002c1c10081503581452203c014240205400c0c403001c100450b103030b10700142d007140050010800070011280d00f5000c250242d4801c9000d9480d050400c507102101050300c80c03086500c0d20303c840e4161b89428041d103c0b402035001d50345c00a420b01c000034200b1b003807007654006507103401099541 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 126886061 1250 126884811 126884833
    0x20c0109050a051e060103081204060b04090c0503010c0512010302100c20010e06030915130c030809030d09030c181d010c080702150604090c0503060c0301030c090203041e05 76
    0xc0380002800080365594448481307188030308000c040b04d400581c280409010301d0b5146844036681802951003d81c81345040e030020400308030f43d070703802402c0810b0003030414086070f00107050104081d9603a02c14a402075090440c0d078541c0c14440c3c41100c3c0b020b049040c5003066039096400f408071011000704108140f00001c181000810b140360100d202ca1030484250810484404000504103040c4490103409403005000b4420040c4010810205603071140c0c0c00b402e05c955880c40090f910315405080503162468040000c000d2082c01002445602415011200310308804c000841d1400410310007d404524448410b1107014a00381c40f90804006003100466180469104c560420700c09000302041a03640c0c502907034201ea040a030940d4030a10a002900346400140007450b4480401814140f040c0d5a0305c003a10200701d50480345070b01802c406401c6814078640100c80e12441d40c8280400c5c0c80440c0c5003031001a111025000b03c902c113560108000420201007040d030380070f002c49004115024000e21004007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 126887311 1250 126886061 126886063
    0x1030507093510020d0b040c0206040210090b0d090b060d08041202060f030c09010905120a0f051e0609011b090302090601170a0605090a09050a141507031d0d090504020c010905 77
    0x1c0010f01c1840043c3da5241d804d000717408a40360403170014040c43c18066403200c41c98022421692081d01a250078000c0070008400722070201042e00315426108000c900303404030030001d91183c16114407803003000115880c1c00080260807051035400920f1000d0400c014000440d4800e6a0048584081d00d10b07400c192860648038060b4000b291150395011000c1840c41c240c0d80e000c0038803001458240d40c5030418519013582c4030b8031140f06a40203006409014560010054100200c108407141c0798511000300c00c0d5040d007951201c1059480462940c07d11180303003811040107560320b103404091344601c2043d0f07245074244200410010300903818003000000804001d0118031419208a5240c1c400107500303820003041101a90340900201e031068074104665001903030000790b03441c03c40d8001d1403103019001100c405c40e1a03c640042449002030889090104050709074000040f00d401c0c00115803844014008450350700c140c006002400600590303010491414540e0080420020b040000b0911aa00e600c4003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 126888561 1250 126887311 126887323
    0x2030c010c030906051608011a07060c031b080106050315030f070308190e06030c2203030c020a2403050c0417030a0e0303030708060103050a0f1a010305070935 70
    0x381c01090b00c03101400c04220b5148501a032010340c4007207445502c03c564000070000c400c140a0540351504071200903020f8011042595007050313000703800744040468248010040c001807000d400e9000c59481001001502a092030340c10b9542c250746c0c0c81e055540f2018030140088900c40d50f0780c0c050240c0005042d614000740b15403004ac501030300c0069505c04001285500e80769825601e4030070803903040d980415a682e00700469801c501101c41e11500d502400008000b00a45a1401e00c26882032250000030907801c82c2d4501c0c00b41e030084802c940b1466a803d486031051842820b500c09421854507508116801b076800640c20041d0910900d0070651640100540080407648141d400c0c0d00200e0700c048816440038420030007038001d070007640c11030501c2032020f80003680c042c20140c181910b1700300141800b100d0740d020300c800111000045c821408103080400c2c2c003016101030180000d081c0341c00030b84154080c5000d8002c440302a20b40b400b5599951045080c4900d03032140b401442c440207211109804010416 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 126889811 1250 126888561 126888581
    0x304030207080d020304051305040302010b1305040614040b06150d0c0e030c0109030312240e06010216080a0803090106030812010f0501090509010e180304090b01080105040902060304080a02030c01 86
    0x40c4401e90078840c44618180401642004560041005101036145c400c1c0c6200250805034000c42d258607141b43c161702604000d0300c9160410b020f0440000301c40c100e900300d18003580c0202820003d602c40048460102841210064034019a82010840d241014554640800b00c00140705040110884095007500d0030003900310b00082404101d00100d2501384403070814140e09007011003804d032540d54090700002c0700700c0070160403594030048031084011200480c164a10321801c1440c16035180c1b0002c003100300382650401e005101c6d80440d0f0010341c26080c609000e43c1d071441d0080c01d24910a0b520304030103900c0100200400d54884500000242040c0d001c0c0528405000408030b080d810525040200351007580080c0c10071022110070001601c1e6010f40506655240710b092000d40d441040032400c030408a9180c90b01c61000040004040400da840012240d0099071412210703684d840801081c0c0d00c400301c1c0079510000400201d030005021000030082841940190382c14030080c01d00e817500711b40100d41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 126891061 1250 126889811 126889813
    0xf0102070b0903030103021f050405040c03020a0e040b061b0a060212070210020f0901050901300f150e092404020405090f1b040e03030a0213050102060106020d180b03040302 76
    0x306502048100c01210b540040550000c40c11589141c0006100c410118414000c41d1000b40d1a1030550344244c08a8001c0d100c0948240409210000c0040c004d51018190100040d039102c0c0160b10b0385001d018031078506000510480c10302e500c003403000c1d00d0220342010f089501d00c16102481700043c0d29001500826181d400820354a1a0151001c1d06020102d00102c0301c062042024050b01d01c2c600301075515451080c6401e40e200c2000c00d00580c1d255000c44d1605040a408820707000e200c0422a80c801c00225154405118160751200d000302a25012022403242c502c0c4204c05021a420410011341d000c2542c4040702c010340d203510859510401c10540c10340c44892140d04200c19400d1030301980d50882c520b5001003a401d400704070416201c29803200800503100c1103001e0709015030356641010100c40c41410a2303c2e0380e8104080e41d60020740c840030450700601500c6d0000100d941c00444d82a048500359000b5081403c2498022110380001d45411072802503405008114043c4100c003030b601c614400e0b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 126892311 1250 126891061 126891067
    0x2e06030b0708090f0a030305040f0f110307091109062109060f250f020709020a030e1006030803010b0d0204030b0411040b041109120c1c0c060219080a09080f0102 71
    0x700001d040345030003040d000d1554000c1d014541c600500080410891744c1501d40040c8503100c038540b84400701512040a4624030725294005c090007440700d03c54295141c210125101c0c01d81e00d00c0e0040035600d44e6501c24008030400d100c0d0f41300909010000b0585801000070715080c02070b002000044c851015601807503075600c81003c1100c41071141c5a034503003003c141030754034600386d10400b802c3d003c0d4403c0c0600342040140544407034205038007c120310005071040620954075038041000080040403602c80da44030707070700c54050450341c0000750b032250000b502c0e0080403042c6140c1c00c0c02d045080d564080800d2903480355003040008003003031522000c03500503445590094035030b82c0e840e4108415280c0d00c00741981f00f5842d201811145440400840314070140945d564200c08030000d0a5604022141e07980c1034002c024100368201c8100c9403a0400348440c820301d1050126a01c50000300d0751080c0b0081007071143c079070119000e40481c0d604800703031200e8001c0c0d1078aa90020744840001d402c080141c800110180c0d004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 126893561 1250 126892311 126892321
    0x10303020c0105180d051002040816050a06022d011401050112050f060418021f12110301060c050c03100204210f0303151208040311030a03022e06030b 66
    0x5000c01e0001c20403d103002424504e0340c072842d251110420302e01034428821200d0b03500812906100c00801039440b01c3c011512240e41d0202280c40d403c0c40e090800103504007200104032460080344400a446056008185d0f440217401c0c054103580000207558039a066501802c050948240a08040541e000070b0b40030407945040009441c940c00c0c507100d5103481c0d05040401140105190180398849011a808100802905018113924040345d502a401c0b840c1807081018941038501000c518031a69501e0207032001401c080ca5080707551001c89608804410001000000d00c120099601c0ca070141d0240c44c00030700c50f100040e103001450011101e415402140c10040302d0851880c80e0708000b09200108121030866551a000302240c41004080c03541e56460320024500c940c07202c00207001148042e540f8106c043c2030885090b006031008444c4c11484507900e407000d040105010f2900741c0d0540040013030001420301640060782c8520390361101300e411040340e001c98400c2e0003408001c5008810080a078180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 126894811 1250 126893561 126893563
    0x10818010501320906060f0d11072108060d021f0201091103010c0c150902120c0328031d04020703030914060705030a0b010203041206050907150c140f01020f0301030302 74
    0x254402103a103801014001802c40e200c2204c40d80d80704504803070565440d0b40090342c0b981c00f405071522140702145000780c01c0d2610031994000301034460040070002d005401c0080202101c6600784a00b10000d400303040030a036242000000054076510050003038074a084002d1028921852007115140103239143d2806100380548004100400310050b002071101401c82540500004c0c00302c2d0b00200760000e0700401c000d152180d41e120304440ca03401030026001c503203800113080e80c0d1818082035034443d000b0403003802c0001c9001d4080c03000d000e03441b51141d481900c55483c01d65207100c0184070200c111711402e05941e801d035210f03c0144061071007610002003c00301410b040c5074a18410309000700300d0b4446c40c1440703181ea40201c01d50340d10000140c000306941003030800403821409180d00c080e041461420251040002031307045103110320015401c0f2181c0f10342d1090001822941500c12001060400e030f4503c0104160041e101201a000d804680d030078026400c2c1203003281e0100f640407000ca400400180105a8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 126896061 1250 126894811 126894869
    0x60f071a0c0a0906081f030b15040902100f02013e09030307020d0507030206030a06170105070f0c02030a0f0503190504180203070c0b0a02040603060501030911010818010501 76
    0x2104140c050418200b450b002c1c0000030b032405610280010940050124541d80325002580c1820700e04844139140c1d6460f01a1511318146c03080b000301111070440104a0425124298400341c00605080c00400080402e03a15404079001c030a045540b100000850310700702c1800340c040c800035648001c00d04911001c4600d0300d03408903c44485a0f01e4101702070b07001a0350000c20780b18020380480d07191100d00564500145011042c2c3d0000b2341020010040010249441c4c2c030403030440f845516946820900c0c80300c11400c9400454406e000304001d041959040351042c2c128440395031015088880b08081da44907004040d600020807902d0340d00005048426100007255030864003824142941001e044c02d045010403100c1d4036100b002294080001401c040c07041d11002c0c0e00d1500522040c4040c1440c00411000c0e500901038640841e013403460000b00795200e0b00c11444466007000d0482c001225100045509003c05003014165040740c250764007007441c00f13115040c0206203c400c21440350808242884000f6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 126897311 1250 126896061 126896071
    0xb0114040f0e12032a090a0902211807030f020307050a030f0b22110306010b0f0403060207081b03030106020607080702031e1903020d0f05101202060f071a 68
    0x81d0900c10b0200960000050030140006850511a12a40c03901009103122038455010307440904101c003d0f4420038020001000408070555800d8010b90301c501107031080c0e100c1c0071000c200e42248004c03205094100e00c4000c81c1c008082e03800c280c21003182000d0702454496070313400130f0b5940101c030a0300300d0461808100c04802090141d90561a45103035491b51000e00343e05d504042c04101e10346000442075112506040b400c4507011a4144401c0c40310b00304001020090000035010b80709440001c12000c0050054500700308200da9031360b14150a681c0c40310302a41000500301d070000000c1c480800c0080100030703808282240c45000b50307213a6242007402445c010001d00f1134401d0003d04800c5c404800d6003c012074283c4045148030b0002c807072703000e0a15142c03403280c00e28490005420b03108055403e5410f40082030f40000d2075078180640c001014880d07048030015034030880c405c25203071030420140c40a81c4500006500041140b414162407150800c0c6603401100d00302c800105e40a520203501d50a005065009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 126898561 1250 126897311 126897341
    0x1302041811040b0a03090f03050904060b03090d0302180603131704030b04140a05060901060906050306090304060f0210021206041a0307090e10020a031407140d050a02070b011404 78
    0x1181900384002210b20a0307000da4a2070700d07000980d003000d480c043e03003010032031940c009040c00303040307019007002001d40d003000034031500c140d0400f1f600060b043c03400300a890284e100380014183e00411410181c00035400780380001d0000c000e40e09a43e1596540d1805103102e41a045540007607201d003032605408074101824900460003041c003042c000300d04103203007450f4002c0d406410044c0b0303081004502d916142010310700034007030f2165204201024606400c03a5040b582c4000091002030f07100d00406031502c4080b200c030748150380700b40001c0103000d108800c0550800e1079401914036502030b4072070201c00e07644045968828a05040140040e5060511a061014500c0c2511012028100d00001e4483d0001d01c10201c00c66120800507100c000103022640340c105007414219a81c018000d8062f0203014040245142d1184e910006288603014442c0c43c1d14a00c80ba6504524195200d99060001d05000e000764070b59650a0007038200049003070110501921410b241d0b1090049104108829515400341d58899 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 126899811 1250 126898561 126898571
    0x918040309032009010303030b0f0109081002130b030903070b0105032b1101020c0105060a0605040602060412300f111204020f0a2c0f0a0b010e13020418 67
    0x1007079000445105481e4081c80c540000606400c400c06201100c00d0200d511075040000082010781640c0695002d050a8404c1d0403201c09030782c01992401c8941c030444190390400c580c003c8081e400e940c024281c52040802c0e40c150f80c3e449103d00100c0e42c000301c600c003003035610010f140e1041c852075940050044c034080b03000708000c40071b200414130400c4e903981445c40c05240500a0004041c01900d130140078072240c41c002c540b21400c0002c058041c0c201524000c1c0a65460540458807d01c44c0c42140d0035900c03990001d001948a9644401004010b01e2808007000459200b880208902d1060300d0726280701502001e01c10380c0204e804030704a803001e00c40c00d00000d190021510110384c2500645400940b0701da580b81c95681d0b140042240402da045e16250b000c00b040c20041003c0902c184150802200c00d01150700d141107074200804000780950b41c0100c04203070030300042c85255154010a20f41c01c010b1520449840c1808013040c5480800c41d200d5001c00d4021505100c1d01080d0034501800494078101401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 126901061 1250 126899811 126899813
    0x181104080a060e030906070b0a0b03030307050a0503090a02060406050a080a0c09050f15070b04050f0318040b0f060d0606021009110d110d110f04090b01050127080102091804 76
    0xd07890214070720007000e1030b072034083d0000f2050301841918103494001d4140e40e03546520340382c09043d002c011964241d009180c0a800f03143d504002054a100e40c1990b180c0a14100510b281a42e0641008000c54890700c1880180801600d490029100614898840341d07195544100040e0508000900300d003505841d02804070307421b170f40c0948103100310342055500703042e41481e04010801c2d00d81c00c5a004800e1410002d40b00c800c01c003401110512817401001034601070380528102c162a48a4008164200300c0e86c0b0076200c020703250039803003103c0b0900014007102000d001304002c9a4150001c1c000c000559a13100d8042046907010700c2030000344c803100d580030070a0102640c6d4045541c0800c40c01c0d903005004000f07440c403c10001040d01200b840d0010080b59150306540703044000d4a01007506103004042c00702c040d44e01c9003418000c80d03054030b9100c890b1440b1a07003400c0c011118814a00040040310040c0f00200b140301c2184501132015118a90001d0398410064003801581a040f9001014840100e01000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 126902311 1250 126901061 126901063
    0x1902030d140d0f0608030a23070309170a02100f02011505031b03161215050f0612120c0d020706080403020712020a09140a0b0609090606070201050403050718110408 72
    0xd00e0301c05000c007002843c03010030400200104002c5d040a4500d03c8002002c035074841c0c00c8004040240440d00c8900c0c115056048212058018000010301250020303900b40207000d5150ba0f111107401c903400c102d4450300e044d6000a102d018680b034215002c070360500c4122b01807036030a0141104420480c801004410f103043c0c00310795076004c1002c02d148029048c00800c01c855500344416a01800c082e0385d40801c203515014507456602403182d040760b825105e0f18401c490135445d4056140724260007a6107002d140d0b0740b9010310244c14440b0404803100d000700ca07070004282c401d00300640825160b040007464243c2c1440c402925000440d040003040c00744032030070000020340c0051001d05030361103003180c4002049140b010564906c01d98011091150030402144469800c0c1d010300b0344110041c41c8288031401c8413509101306403003010a11a0030050030300002d0418141b1500401040344103240c440d152941d0b9460386801c180043d0003000255000c10800505000b007070013250300410300007092070307c0c00b850490340e1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 126903561 1250 126902311 126902317
    0x20d0f09050f0a050a02040207020316030501020c060a0e0c0906040b130912020c060a030e151e2a0f07050102040b04082a010c0c0e0a0c140a020307030c05010902031902030d14 77
    0x1f842550001194411901d003401408680c0900b1407000d04a141c030b0345440c1d8040d400036001c01041d0310540001500707121446c00b03031103202040384000d003407510240018000e002d6001800a43c03c941c075450542c655440341c2c0488501c0200440d800030710400a0f00d08403ca010310100003504542c020740159946a84002c21502c031040d540c240000d007840f689413814201034170504d580981110485c1044180542101140d041c2c1c1c00044d5030b485141e84403c0e200c207204000380101944030b80e0140e8000d84d007030b81c000010b20102e072140740c1e140e040031019036400b401da03403050300040044540800e042000c11010025113007051079000e0103030b5100a802c01003010f60918103c041e4104112540303000280031541580c40007414000080080e20711309100484090541203020a00050094a205e54581010020b075100d244170359010b5454101540c030101c83c4025400c506440300e55a4090f141d0050340c08020641512600182c1c1e546c5400803030040609100c2089011400c0c080c0380b45444581005074011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 126904811 1250 126903561 126903563
    0x4050603010b1308010507030902010809060123120706031e020c0c04020a121d070906180e03130f06140a081605070c0305061803120606070303020d0f09050f0a050a 72
    0x40302c0e46a815002c020300c2e008a50b80e00003040380d4070344030034400080c2e416006814682d0003030704d41e8209522440745159550400b44101d9240540c000d000c00d5000e584180b0b035800b045c8000309206200320408083c1414003c02d503200c000401d90f0340e090005140b0310801c1002544143c50011410a100aa06551200c0d80b500159106039800909000581c1c080e400c41c02286000032800c000c064280908800c0791207007040d80005510502800046408c01070007104203960a4484001040c0100001940640361640301ea894900040c0052418540e40002d02c00003841140000c0401d80d103804005404440340895103201c008080010790702040d08529059000050b8201014516411010441d0a40103262008100c4540c4d14400420b2260008150380a07003042d00741d00041303083c0e4070f0340c440e664400c003180000300414240025001c0c0c0b03048000b41000c43d000e824050705e03161400c98030740c1c100c4000d401c2e07090885503071701216400e120701000000c0c0b42d44820002003e2591184d103c495540c080e1003c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 126906061 1250 126904811 126904829
    0x24020a0515060d060207050a060e12160f0b0906011509050f0d06180506090d0906020a0b0604090b09030a0908030c0703021c02030d11010b012f0c1c0b0c0405060301 72
    0x41012a00d4005202207801d03003011085440e030805280103529040b55238401d8504508088061040b4040418040c4100e040c0c041c41c2c928014941003400d04401c080c4000741e90400440c0c1e17a440209609030107140c442c052074805001150b0604501c40300f4181d440c0a80010080307541010b00007038541c00302803a040c2c907040f21203154911161520002411024000390100e00f0203200c004200702002079168020074261080d81c100c008500d00071219014140300711001a80100c0c00e0b00007042c54104511b4101c0303400b800200b1020f036543c80380d02600380b00b500d000a180c3d000043d07000e091a80302442c2c03030240460801035481c244e07007240300555034911400702070301c82c581e8610144e60114000c2c0c041440c0300d0780078003507550320541208081d01005041e002d42c4a0355080c9040c004c0300c0c0d0702c034001d80400350342040c1d1a10b00d44140800c1c3c130301c0080c2d403801c4da044c0140310f0300038080000d50341c410320220400d803a005031303601301c980a1512050001d00074105841e441c0041c402402640d0f6050252419078180c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 126907311 1250 126906061 126906103
    0x5120309101406011d0325060806040e1e1501060905010e01020601270609050906180d1205060310090c050109060201050c0901050f07061404231b0f030724020a05 71
    0x3905152400c4000c100440b01c884247c1c01d15200c807030000c02101c1083d1108032503a5241820300054403c80d400030096500007040c2c518000400145083e112668001103800b4440546c031403000b80d40007a0450f0000c540c2c4100f04004660384a402c0e280d2628080c80a442135524060300114104200d001d40c0349040546c180201210800b50b010000400144400348014240b10441e07a80394101920380b0b150041c1962240c040c40503000a05c01070a010342e0352070a4681040290b47c500a040c00b400d070580c0340c080c0103400c0029a95a0059001041c028040044400c0c5030400151111240e54000b0080d64102010084a4002c60703081c6d8640502c2820202d541d040c52a80380843c40c814038000826141c58668440c030244000d0070307003901c1948541e0700450b2114510407580f8448d291b5545200075644200b113405c1e10540511591002010090f00c40448081c9a0b03000030f0505003103801200340480316080c0c4020302c1007810880100750820340007034002c5403850f8941310b48503c40c4500b803422060780c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 126908561 1250 126907311 126907367
    0x121302010e0f0112050c03060f0d120e010e060711190e010308090d140106061b0503030a0b03010b0a0e09010b0d0201052215050a09050901050d020d0512030910140601 73
    0x11401d00040307038003403513003080302d850a581742c1c00d043e400c2580d03068061b200c10088480c10381000a44505003a411503060141012401011514a000040d6040c10090441d40e00780f0540c980201030f14001d485403c0c038a50b5090f840b014421100b0484200b004000344909040151403c0341030700c035055940080d032565403800340ca0b01084130711004000007800f0b0200ca0f02120011103065000000f502c83d00d5407440710890b0340007407285c0e500a40c400060b050b5003040000c9054402160b01c000c014020180020441e108088001441a50540e00c58452000c07040d04000324503000f0f00c520840a03104440702c8018141a8000030400d002c0d200191002d1200e003584440c1801143e01c501004040c03031450012144441c210041650300148628070105ea00c4100c085400d00d8184c0c13440b416220041c1101c0b201c1d05041e000c11890303050416003030755680101442444031055200045106e945d1550040c44844a0f00c56408110350030380024105081c6181c0c01d010590380e0110141c200c2d0000600d00110044139 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 126909811 1250 126908561 126908567
    0x1219080a090219081c0f0c0201090801020f0702040f1406150c060709261009030909020703090512061311012d030b09010f0909050307140102121302010e0f01 69
    0xc0401c082d500000c886281c030039111064100c0c000f512402801e4415030341501a403201e107015800018008a507524442ea140749200341a110b00d500e005140c00d508055941031010308981c052024a041080c0018156040d42814020500002c001140822241d4904075a04000c200081e00903407040d2184414040a040f28100f07480e84d002c100710940307602c0d0400c04005005800b03d4401c208802c26041181d290072044d0040708807800240b000500b800d0010051000300401c1c1c0310500300c0500103c0c00c0007040300c0700c1380d1014045041c07194480803941400c01c810418010150321030301559600910400015861140c02c0004595102002c607229000c0c00c801640c42c0f0b01c1544407000001840340c100707007412104403515585030f00544c4007044600300c41c506204203a2400d0003021040300c0c41003820455040741d68061015036001d201501c3c00c0c240d60303540d01d03078406010103410300e0780d81c2d0080744007400943c4490405070850700b000f61a08442403d0750028060802400ca41e604c501c40c440315521003030b40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 126911061 1250 126909811 126909821
    0x207030c030f080c07080109030809010b09070f0917010b03070e0702030a1803060920030120030c09060c07080705040204060c1209080f0a140c01090e090307020d0807051219080a 78
    0x1051041d1008586c944507464024011590260009003e01000c200740031418030501034a074030080c081800c0c668800c10255030f10b4000d61104401c01090b00b100042a000c00103075580781b000a540007003a1003c5002c10103140c8112600030407000450101030000494000040f2040b080e590304200d20341c0c1d0a04080721611007299031029107203d0900c0c00403030800844c4006401800070f988003030030b40d1030b6040080c94222014001070444100c6410243d038508452030014550000c15415203600c0c10800b4030204030940c10840c2e40d4001d82d4051101413005041c18400c00c00544801da40c02c5041514200c00242882c00c602d074054407080c8068070181c6c1c16841100c0c05d1000e085410100c030900454000309941e00d0b110000c0136583c45203000c211654060000c2060028030300140d44000002e410521034108015006e0480b1381c0340e00c001c00c080c00050300c070840c800c050b10b40130f0b518a640300c09050600c04d0422020701d01d001f1883da000c000d82c040ca95050f0410190307041c001e107000d49440d070b10044140e000f04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 126912311 1250 126911061 126911077
    0xc030d0b0103020d0618060b0301080309120703060e0303090d02011406010e0a0e010b0c01050907060503070f170f0906090a0804090905010b0405010b0c0f010203071d010e04050a06090c0207030c030f08 88
    0x141041000300e443c1d07003024a000d020403046d002c1040b42c01d0307441c2c19101701c0e800b01f8003490303203207400410004040d450080441c0108920f8081070710f41107507a0b5aa44030840f0802420994aca400100810000340000d00ca4868040004c0c0024404600881c1007104880c40041010781800b40303904035540035454001340b280251552012a282550b15070748034820035000007128102c5582001d0005c2d40801d0701003902004c1310b025459007802c5485070700c019526505a080c8020411280c00c4281080080c08000213014003098422103285040c8000041d040c00c0e8020300d504101d41c401100b8400181100044408540d40d0880000b49000c05c0d02e0400d014080900f400e0354002e08020020400b19400c20080030704190a5048411240c07101208174240d002c00c4400e50049021444030714180d03664451501c00300c1a0515140b243c510800c0c1c001821201c00303441952945948200a00134040745104148080314140014403485241d0360780c8c08a220081d0000038088000b06c60340104000a51007079943c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 126913561 1250 126912311 126912337
    0x5150a022401181107081606230a0b01080414010b060d15061d0d020406050303120709050d0c150c140307021c0b07140d09051c03020c030d0b010302 65
    0x10303030051148041c0315000e00031290340762403031110000035041e103200d002c64400c0c0d10340e022414516140c803484a990803041c1c3d800c3c1210384024520000580301c2c0310707005001c01c1500f600c1c14010590b40088a43c418001c010a02c1c02d498082c84419503a085181603a010398061104010340d00d65041450243c550060215008840840d100c1070080740303500b080403100000d0056140d80e40c0d444104072006811144000101d1a0304840e04a2030700380a8102c800050021f407000c21000e035100003003440e5500041040001c0ca6010061180243d0b120410a0080070b044640341c0782030196450314003c10000d8841c9150680702031035030114190042031554001345d0081c0e00d02c00b0581500c1400d5489a101e610101e00ca090728100e038400c4580e841100d004116000031201100b9560003405851800310b154510056840501041c7c098200500406039030074861000341c95036203101120410f110081d0195542814014080756080c0c8a000060b940c12190110380400c0d0203283c000142c0091042c170100f8650 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 126914811 1250 126913561 126913603
    0x6060d0e01021e030a0507080115110a12030504050c03061b0d0902030718060909080702060c070e0915060907022104031703070e031f020a0504090e01060501120605150a02 75
    0x210f203004078091031044240700d00900160b9110038003101d202c80240945104031500681040205200f2008400f0b860700f824101e03071480420781c440007204680c040c600c1000a45400c10801005020300055400781015401041d00e03003849460714035613120042c90000c50740f902191000e101030f01904080d48254002e81614219503da186003061121922024801c0c6810b181e00012150458492100c009410140c15420300c05103908004583e44007003e843c0e80c602c036180380420070507442c005080c000c400e03040c018082040075031011564030034010402480b803500c071001c09c140c01e6004554070000007102c08442e90820180c0d140c014580c011504094003a03a4100001d0f00c01032400300045001d51a05e403549900300442c00c2c00c16a0302c840ea450303500c0014840000700071050641e03130050b10402d01c480c1406030602e0345800030750084681b00718804001da91112010400340d40c010001d020210300040342800810304060110342c1c440718529440d00c080a00180420300280b0a210802202002c4125800d0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 126916061 1250 126914811 126914857
    0x50102120906120c07030f090e0a0e011d030a030c020601030209011502100f140c091503151207050f0a080a0b1503190210020d12020c030c0607030c08010e06060d0e0102 74
    0x51540c0005c08202c0c0450500c201d07205900b0b00407041c0350102c0700c40201c100820364038042c0c440040c0001012090fa590f40340c1940c2d440c51808000d940c0d07503000120004585680407501c0c0241950203840c601025500400018000358480340009030541d407400d080e0300702d1890350600491800d050b000e10780d0401868440300c90030552544c0c120300c0c080072860000040d00d48645a40b540700b8400e203940355900188480c0c00d48641c8210f44081d580c0907042080443c400740c10b90000c580310540042c00160190401c401c180900d20781540008402c000035106541040c1c18442155a55642000c000d060880d10a000440003c00c0010a0490300809400d481010300010b07030b4444030f94200b440c00c910074502400301190940c80028a42e5048600341c2c1c1e05502450810400c1d40254040d80400015010821404507003034020400700f401040c032950001000d03250030100038824501a0000d030354003510039050101c580e45110035929000141e02c4006848107c0150340303070080c854042c0c0c65100024040007030b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 126917311 1250 126916061 126916081
    0x90e1203010f180507051204051e01050a050a02090a030b0606040302220e0c0102030412050f03040b03070806030703080405060d1b02010b040f230a0e15010501031505010212090612 79
    0x40100d80d0403101e40c450b10f60f1005110b6007951022195036002840501504030b022281800b510b0f00140201d042c1c074600010800070801b502c0e030282c5030344a1a915402400070220403881510340c0300700f0724041141814407200000e00c2d061054031000d8403152050010614640d200740884000b90760050400207140f001802c00c1030454905c03040607850394039241111801c07410105d03107818110350590203903203004c0c18503174800c4001108000541d101c1c815002e4401925404200520181a036610f10035141e280002c0000c0c0180c20007002c06010b900064010000a603400040e20250b5000711013540d15624460600c0008150742080e90489400712000d8101c503c0d011351122207418810f0794103020440c091000c071000d8802c581e0004001610700c1c1c541e584880311052000d604071004040214801c6100d820981c40e01d00700c4912040c0300ca035a0b0004200703071747c0c040c80355100700641281c40150a51038200042c1d00c8401034641d0f05030440f0002146503540d5600000c0f60608007001d603408200f400c240d66a5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 126918561 1250 126917311 126917339
    0x90b0f041a150913240b091021020109060e0103090501060315151202040203130c0303030507081e010e0c040503060c071a0f04060209130c0c030801061107090e120301 73
    0x980c083c00038140401d081c003032200ca0304403403250066041618004e411000046891100b51001c180d030ba81d51101904d00e0740d9201045018031a250001c1030701300e00703118480c0a200f1403000d00b400d080702456650320050360001201000c0303a02c9810120300c1c190400005030003401c0324110040c000e520f0405c01104006231041c0c1c0300900600c0090070441665044442a42803510b400790400201075407501c54011f02c1d15030000d541c0401921040c030700d100c41c15600d510203402103400450210762a0300820011b5a03001402c07a0f8000342124202d0a140e4100d00085c3c2c24403018010100c1409450000914910313014080340c000f068060226000b82c540108072800c43c0d0042d0404580c0040742c0389240545180e08000c2c14090501201c25241ca914bc035525600250700c03141c1c1d01500f1201e03600c0a0303c02613180748500400d021480c1c0b514400030149150040003450140c00200601c445460581159600000c2e91000e8941c00080020011400d4250a00d07240c0002c00e0300481310800400807400900350000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 126919811 1250 126918561 126918601
    0x308040308010f0302011e0509330f0d0e1204080106140d0308012304020a0e04050c0c1e0a0503030c0a110303060d03030b0a03050607030c1101090b0f041a 68
    0xc205003030362100c142410f0005039204c064009019582039070505d000c03182d210702d8000f5060415524000507000403958484880344070600c585189038819803480c9860700312900081014942c1854002c0f1800d94598501400c0340841c9680e83e03485c03200500d90400c001c02c03d250403100c05a86e84495468501c81d020b80124007a40c810100b1a180544040c10004441c010391985500d80c00a6603081280d10040d4052035858408500460244100c43ea1580c2c40180703502107080d074031007010f6500c4030144821740f04042d2a010b2501c80c01c124201d4804004186060808110038104210541e041d00c06803601001d610040d180340000070a1003480d10511000303203207414040e120b01d450602e10118090712400101c940c541c0010142030700c0700000f40b10703501506600300010200625541c80361110f0b0b15158007264040d0210782d031030048602c496003046401c545030a0b010000c2c40300040550b50701e00031020103030004400c196502e0129080048040c14190702c54003400e40b07048503107810101600c1c030f0600340300703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 126921061 1250 126919811 126919817
    0x30c1626040906140a06120207080a0c020f121009020609090108010504021807050f0a17090d031404080f1309050906160e0306011404091a01050a060507030e01030f061203080403 78
    0x44000703a581001c440411300700100412100901e480c00e03c0c1502c44c0741c40120350040c0b003942086000001100300000d410159a5641e03040e00c000707228030511a400545500d014419800000c1d204101040000c00d40109405284041550015807020400c140103020000340d2080700c0070000300700030030150301091085000b215041c2d401142c041060501d824103641c0203000078000c0101a2075444c0c00d800400c1140d0113807802d030138400d400149105d00b2402c246c400c4201608008030100710140d050007124441e10b2504141c4d00503007826030f0340c0006485201c01c41349807120080b4444540300b00b18001c22008100e40f40051200740303800c4e0602c80e00d6000c101c030400c60b04844118000c09061003402c65024880020b8000e0000743d0030100040c0a83c4000c07516558440d844078824400200c0c07181c0e42c400d007030804540341c510325410202000041d40d06c680044d000c10005001e0b20021a0303001200782e40f100001c0c24001440b101c04403402e4054142c68010000e00141c4d010290201684104100c2c45240207903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 126922311 1250 126921061 126921071
    0x1b0c0114012306180f130212010602160f0e070e1003050403080f060d1401020f0406020609250b07020d06021c050a0507050a031e09120206060105030c16260409 70
    0xc04012960040710f04586404054244c18016410541120102d00500800e50303502e44102c0c04005040c0da00500518240050b190010021160108030700f01c440c009502081703219a00300004203042c40054800d131030402803910049691140141440c10383c00501808240001c02e08450113401b0b040b0660f0102c0c005000c03600001d0600a450ba00300703001d0799008080390507000258075005000409404901a195820480c4a45912001c00140006d1240c0d1b0003074185440c04840c1c040c1041d000402c11100d580703900c600c0f814178510094018094a141d110f07017071b0b11505107002048a400c020b940c010007031440080c1e40c404503607a80c0d01044d103400038240c00340000d81c5d4040075071301a1281030742e840c00415810300070b00d46080c0c0030fa0004281c00404102803450511514501016502c200209507854104c030501900c4196060110390390145081c20010b10390700300072018030500d1081856000c21100400104000c1051030910364508011211090481c4034000d84048855071207449416080d074904 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 126923561 1250 126922311 126922379
    0xb03010303120501051507050115060e0a150f080a09050a0c05090a0e0d0c1103190308010803091e0d051005060406170a02011b0b0705071a1b0c011401 66
    0x10b40543c506850000e400d400c0200080541e1682d81c1d08074000484565480344100000740711200c281e00b0003021035a4601c0985901c040034000705003020303004401c1080c0c03510f194000c59078014061035034040c150b10b000c0c41c04e9600d20540c803005084c0740c5001003490003542c2c001418001d008035020306440c001c17901d4000707a4071340c80c002200b1110188600c40860b00070b41d0502900030b015100b200e0605015184034a043c1c0c0d4201c0000c8e04040103034417065000c5514010705802d042d403200469026000e540300452900740300f007000814031a40035418036001c41c216110400aa11081041034400c0e500204541c81e2100400302d01d4054802211502d0007903160540014060514440c0042c2d011106070107003200b451550011580980003001414101203d01041c4001443e8003080c10b1040301c055542c0d40d190300c2585440c61000c00303030140b6082d81a130035209024106850480700314101600f0029650f58034a1f58000c14054601109a13945081d1020000154021071081c0e840031a001d0705000100d901c0e070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 126924811 1250 126923561 126923597
    0x9010207020a03030305060a0504020d050f160903080a032405010f0309020603010302040f0902030304090b04050a060302010509040504230114101d1302040903020a050c013f060b03010303 82
    0x380e108040c0d800341d4840020000309000e40d002c15000140030b425044500d45441c04101a84e10520540700c42c11345c1c580030030441c110001344554000d02000900c210002070110000c1c04040306000113090f1003000640450042d000f54042642024200650541700301620803101d0303d0313a41849494003140450100c1080c1511a201d500c02e1164001c2003d4296400c41d02030000030800031078100505a070b50b1006401607601040a0b000500303521a0110301005000c05000a42f0030240c64452a181800c0f420700050381c10905807019083c0507100002c15981e9030408a0304200546541c044284611485040c1980190001d000b4110201003820140c1c440850b64802c1c261103204103031240c0400945d81c81404610f5441640020000b0380200010b0b1054000034221020224118090380c84030704401304000c0c05000707501d0418000d08203500c4192959002d6a00880c5501400f150541d18000225040111211030002e41c0c0d03400c202084504e48071000c04a180d482804245c011918660a1060071a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 126926061 1250 126924811 126924817
    0x2030903041202060f0301120611130308030403171812180120010507110c010809060601030e1c08071106040f02151e0d060603050f06090c0c070303090e090102 70
    0x402580303050b00e05184a410a440d001c412030b4040c0e8200240130b16400100040c50103446900500344007191146004001c0360310244c03006013258018441a40401c041200020803a900602c00179070780ea03680d1400b11800c065041c40440503030815424080140710030f03050a212039a030030040307824140e095001884d0718002c0c540603000c01100780400d015907510030740040440a07100c4d07001c1d05003219484026420340300c00f214030700002112078441c8804034208204c2d5030302032a8282851581800c0000800da22140014009418507071141c1c5c8201d14140d0420080380d5501614403034140e00a88001e0080506805555140001e10b640701c0c90110702e1404104140601da000e425801d00010b07541c00d010000841030840006148240011031400307128050b117640030b20b00c045100b55200480880c841c111045600410101464201001070520707214a40a400881c100c0d9a0300c0942c0d5043c20744001841680c03402159801030100000402d03030043c8804041d501d4040f62011a5980c100129080340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 126927311 1250 126926061 126926071
    0x100504050d0f020111010f02071118010b0309030f040b0309010518030703180e090c12011a04020c010914030d050f070c110604090e150a0605030d030b130c03090506060102010203 78
    0x10030054001e0009035030024001441c1c1d02c1810050404079030810560b007100c40780c1002d1030100e50001020b0702040741300383e103140c11500c1c100c6420119106c00c0a201e450a40b050103190612400000415100c89c2c00308140c41809500c01c0c1070310f50761ba4441480d0b0040d03400c2552990030750b60807d40480d24180d241c18040101742945801582806841d407421121340d003104110811a02000c00701040a9a500320050700c1001c008000303103000c051550a10103070100e40010040035900d00a69109600d900d03070740d00030041364121000360f1121101e00c02c8500601050070000c00d84905c20210008280020003d0031412030412020802ca40c1e400603520340d4060100c03040d000103035040f282d0500081d0110507442210328090092818507071220050fa00303e0b1143c9194280360f40c417501c0442c1c055082c40031503560140007188180314003440c14012070f40d110185442c1100303042e00d41c00080081c2d1a091080759404c8400b0038140046000740c1c5d009002000c46200503a2035009080000e04c02c3d50050080702c0c09a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 126928561 1250 126927311 126927319
    0x181220060a3501080a03120c05040b0f040509040b09062206020d0626192607020a1d13080306120a05070803040f080106030b040f022d10050405 63
    0x1a0b60415442045921529060788001410b605100030003070107208090180060b40c0003020404101d041c06824050000c160303844107814100c0c40034030b20384d000c0117450456002c5201251114140c41d0209524002c64100d190002d8a030000c1000b813000c010030302e902641d0f518007a500d19403200040c0040507000e40d500794249194490042e0002110340d0f0090134001c14000c00011441d072500a0103040464002e0084884858003c2c4040030200034003d940c504c403c10400d0107036092043d92030840101e264180075041a80070070b10400707041c20100844084a9005001c21252500e0b00c0e2800c8151114851551110f200c2e900069051003901d1a14009690044c4449065030b403460104920416080c2c2c0c0c01030070703000d5400e1040002d4030400c0210060024030740035588444c1002040c400b5456140c0c0694801ea04028080000c501c00700c44403604641c0108824001c9074140c0089540e20149100d40c54401503001b03103142c4a01c1c40008a8441e4540460b100305150122030012941d501680c000c40c0e900c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 126929811 1250 126928561 126928577
    0x40f06020a050604080304060209040f0c02072103051e03040606030b01090506010806040209010203120c0403050f0a03051c021c0e0c06070c0902030711062d0c0a181220060a 76
    0x171820900c003440e0310510410000d0700c0c01680320042015180095403074150103403a5059100c0c0b064041c0416400b41481803080b41e04141d105451703000c140500c05018003071000020360b1500e40200040000790340c000c180e0f5015a02e040c43e10b802001842280301c1904e0780c0300b80400109061140e4001c86000d01c005940d10015604c40f0740400c4000d40c40000068107600c4100690b40301a400966070a1090100440e0309454170f107542030031401c100300e415a0615076040040d0090000340c020b826941890081c80c480008c00a149007100c00902c1000b20a2044020014000481c07010642009190901101c140da00300c11401c2d0a2142e64064500014201c035150001032010b803209501950344641540b0f4011144400407250342e0800805440c0e000c00b01544007440001c06800151030300718000b84030903030407003440c004101c545140217184448003089610000740c12240c2c03507030f034601002c2c003241c041600f49000c0a240890020300701000e800c0b2011035600070f18145240010544003107041c0c40c0c8a4041d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 126931061 1250 126929811 126929813
    0x5030c10020f070b030612070317090f1309030306080f032709040f12020a0b0412020f1006051e0105071211010612060e07080c0d06020705060a02040f06020a050604 72
    0x103441484810040118416200c2d0741801d000108440c00080c4072061856659040030002c0c00092222044c140c3c01e01c1d8052031b02040041c03945d107000c5141107c0499082d4036020b0345000604050340c1d170100e2039800390050b251401c0700341c4d0720740c064141c0a100e0b40b0104031440d80e4855081e16014400200300d4035801c140a4465400180e000e41144100000403e503101e50114001480b40f401c20344094900c242c000d0003050030441d41d50400300011006000400071400955180d04210b00003c200401c0c150b22218815107050007003111005208000c0251603517650300200031402003035144a40b9100300c040684212480300013074042200544180d540d00d141c00c0720742d101c003201500c051f404001040600040192098020300c9000c000c1c060140540c0119462420110261203041c4403040c0d0541211000700880107000440400300d401c240e4900801b03050700d04007600240542640502280560000c0050003501940103001359150115a1020981c54100490b5100c2d0440d0004041d6480301007c50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 126932311 1250 126931061 126931069
    0xc0e190506071403040807031a0f010506160204050c0a20100b210d03060b1303060b030f030d060314120a05130b0703020c091501020a0b0402010309050d260105030c 72
    0x10014500a400d83d038448005040c6240c60b5512070707845402c1503080a0014020004120a0188030194507104c40d189414664460302c60400f041c4901d40c8260000034016140708a81490746030080d80080007044030745483c04502800740d1108103141d001840b0030b0107040308265031507040710350b642400f4001c03d0b914000710003210080c501141074560100442100d44551202280e000d6500a01f00001d854240282480a0265091358010455030b4034103204600d0308104003000c904c220380e007084020503480104804603050520302480074100c3d010000388240e041c441900700c0001c6034440d100030381054682c61481034503402c2c4007072483d9403030008200c0ca44e200751007040a4614502c0d03035402107104030358500e00c80000340d104030011405a08840420000d92502c1029640e0003206410001c9040343c5100001351038034141c0f40002d000203000f00204096901c2540039640280d03100084460440380f061014110b483d21a042a07044000d0b60141c41c05160456915412103001070014007254003040200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 126933561 1250 126932311 126932317
    0x50c06161e02030a1a0117030706050c0f07050309090a02030c03042d1202060a0c020a150f0c08010806070219080702010212160606050d0309030f0503120403030c0e190506 75
    0x400d41041d41548540940c0d0280039a2101e280300308003240f4180c241e00100e24400170140d0020f107200c40640003a803502c000200484910315404000001d6581e5541d00f02505406907402d00041c065000c16050104500000100b9505030101c81c0d1480543d15508518240e1204886400c1d03000d00c04e1000c1400070340001300380b000184104e0700c1003040008082c13006000c0c1068000c02d0f68010040700403030301640e4041c0302c0c05400042074401800034800c1c01401070342c3c0e091104001024008617191812295585900104a6190882c0c3c00c2c00740c080401d40040400c032080c000c0c0321560007241d01107007043c1e0002074000001e02c0d03aa04844c0d0300a8854903011080d07080528164194011400d61002c0a18000014408030321302e98981b41b074410190400c0d5007107410a4025500841c1c118a1000102c0d4002040c54210b0b0341c8040581031000841c600382d4158041d8200003406107409500b80420503815412200300c0510b90f42e51043d21751080f070200688035004501c1440e40310701800040c070560400d1002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 126934811 1250 126933561 126933593
    0x31707030212120a0c0206040209070e130218030d0306030f0f020402070614090c0402032502120703090e06030604030e1302070209090627030901120b04021303050c0616 74
    0x16582d002c2040740004400da0b00500c203c00000c0210f00c20840d8810151080040e0309956100a028603d0240d0100d5102080500020288208da429141c40c42e56503402504896942e29400e45d140c40c00d20203001d542130108040148a4000c8040400f00d540c441e11400d000c070f03034008842c18070180031622070f1030100c10b90b8082039030440c2c3c08006c80d401054260055215100c003126842d03100f03141909240b4144010840d666208900400900414072b41002c440b820240001b140010070a00d040c20076031800904d0014403040300307008100e003800c0c190012000c2c802c64440480c0c1e122147e44500c1010b407100030866000700400d1040841e8951801e051405074140500a40c00503c3c0111503000201d40e14070440e6843d1b0035511050800c003c0007207070103041d003001080050b0701303010b00060f6640540703a02810101c1d90422208040e03121243d00030b07030070800e42400082e00440d41e94079644c1108028030101c1c001503c13640b20380701d9140042c1c10201d045a00740994806505296500e55030341c03189803d41944 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 126936061 1250 126934811 126934813
    0xf0309020103090f0c0906081b2e080601030c0306150e01120905010e0d0c020102071a04090f09110609180604200304031107061b03170903130f0317070302 68
    0x292400191350084641d4000e400307000040c4e407544c5000125800e0784d8260f00240815000084000704100384442840f6070604200d9002444c146e003980c074502c1000d08090b9003801d090403040c0c090031841c0c018241a01548007031b6400d2141060744c400580541d407c0e0710917881c403807031301c000c501104600c145025410460140742081091910a1180b02034411000c8140c40318bd5480070441b844035810070080c1c03440325007402c10f20400f004c0c940020751610380350300c14502e844000c0070654800d02004000c40c0c0c090f05031024200f050100c1c09523400c00034001c0c1c000c2243c03114000480c0d00c50511b00401619032112004141201c4c2c18465001d021300314101900050300903403582c252091030015403902400c440441480d090304c4e442e0900b4001c04003e2807002c0300032142c000f10b0040c8041580685402400c0f000d401c0c1544819105243c00c64920300740c0c4034804184040d05060200e550808070003002500c89001d010816661607a17138002c405110b900c8010a03010f11103d02c0381d0021941800380003c80c0c0a80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 126937311 1250 126936061 126936071
    0x40809040609110409050a14060904030e04091a0609040c060302090103090203030d150b0307020a030806030f1b040e010510090e030c01090c0513020313061a03030c030c0106060f0f0309020103 84
    0x141e41041582d1540343c10440c42c0f00042014085c5031154425964454084402030001c041100300c00507140034043c0c0094018080480013074203250046a10484c600c1010700200038040700c9080203035400c00c140b40c09822003d4440c0101c4c86c00e00c2d00c4c505c103034040ca07000102500110f1510034180c3c000e40c0a0590503040c1a1a2044000036030303802e2000d45103804208001084071010443c2c070f1112003c0e140c001d85142d090074018018615030000e4001e20b80d591500b0481c03016183d08001070f1402007100f801c05154440c00038030b25075000c1c00c0c40e030742d40e00135100b03403010300095880065160a0313031421170350345180e1a5402030802c243d160315003001c60704001036410b6074500b0219120756425110720032401d545203e103034081040306083c06211321007840001c141c21800d5051416401208661a0070041c2c441d0391a4800405209000c0d071117281c001070000e04507507503612008545a1290020801c0c10007c2d441c08500088140c00792103000104a56555040e00300180b4007030a50003001c10311401e9040603516 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 126938561 1250 126937311 126937319
    0x32060f0f13060e0c09010501110601060c020409020402030a0b0306090a0f0206090406030515160503012121020f19020102060f07200307120905010e06090f030604120e0901030201080408090406 84
    0x9449076039015607480018016005010045c001e0111042e80124100130469405510303404010580c5419100c25240960503501c10b400080c010301241140070798454800018010710b01c01540c8001c0d05c04d9003d07401c0c0c43d000e43c0c0311041c4540715100000003820919044406400614001c0000c00f042c10008000241040d22910b60902d003d88840413404144401c04c00d01100f10700200d03400030044100e1400d00d248d50704018100b2152803903600c0f0b000110b00020304c81810032004c159607007800750402c0700c26030000b00c0d406c1009555a51a402c508400c0c0120380d00341e1040b21041c20301400d905e030107030000c00d195124581c0d20200160002d09001c2004000c19008141a0a03030640301c00801c0400001c50b128211b6040c0070300e10301544100c2100303101e46180e0401003039800041070b80d615031040b581240ca0701c0064002c07860760b10408540540c1805850104020042c0034102d0b04c5041040d03680e1114003d1806050100c0300c2020301019001c2211000000c0c002400d0b48000c0616917400391000c80d0390390317403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 126939811 1250 126938561 126938573
    0x50603012009060c032109060112030909022107170901020a0504050d1509030e09090f0606010c02010e090109091a040503090409060b0a06050a12090f080306010c32060f0f13 76
    0xc03000540a42d002c0340f0f8107100c0707c410708000c0140034003014032034458038a1071550040e00f900c62502c1021001600407400092a5807618070842a503138450b40820040d280c41c40006003c40004510005040c180310040f4907000360510039621802c01e65103549142c1800c000801650b00900507040311007020803840390035400528020300c03e443e4841c1d00c0f50a8042c4501003081550100106109042d61048000e40d038450000104240c00000c00c1c01c060300e804045000495800e0f0303070301145a8000f17a17000000244d0558a03800064000d0103203032110141103a0b408400a502c1064a02401c545d10600c81d912403440c01d0741c0306420080c414100000e2106400c000b00f1203450307165000201060b8003142d0b00440340d1300304170171648006040e4820081c569007540c1d484820201c15030054011280480007403140d0b40140441c140281d007000c600f101c0030110f9041d40d01004042c0e9400c03a0303404055a15000714400001b6034a028803d508440e100a41d00c6042000310b400f00240f4030f070245010106640c1c04141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 126941061 1250 126939811 126939847
    0xc04030c090203010501030e0a0f080c0f0102030c0d06080601060804030815040f090201020601050414040807030201021c0605010906030b0d061505060a020a0215090a060f0302040513050603012009060c03 89
    0xc0420701c007580b20340c5050005001c442800c1541e50b01360b00001c0d003420020384521741103070f40d26a00400264a52545c44007151610025900003601c0390f2000050000600701540a00401180c0d08401c1c0011905c0f0304e40103881300310070322407600800c0070341c0b010074000b90141800941c44640309086c4403d10001074000b03425203405909881c0081d541d8410340041d56414400c2c94050b11065409210701c503841040c1d0020480000c01c050703e8540003140704010180300303404540003104c80c562020b015200111220000f4191489158081340f000c0c0e4000400034028040c1725a0031340020302c1e08510070403d40315040a000012103580c000194494081250356a070741c0541f440c0340441c0d0060008214610600c2500c0481421040004405100384204c41d07481c108042e081c4c519929180400b4034200c00180d01901803600441d6100d014440b108401601c1c55020f9441000e044000780200502800681810040701c0c0d02070b5000d1400308040381381810498010040c2207503c0041f24603108900184d042184 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 126942311 1250 126941061 126941069
    0x51b0117010603022a0703080f070203060907091b0503150a050406060512010806040b0c0d090506041202011a0a0506211006021506030309010f050c0d050901140906030406050c04030c 80
    0x2039804a051542d05c54168400c03000754030481c84194a0064400a41c1c0e5100410310005100c03190003d03450409081035010754260503405421240c3e603040c07d20225441e0b2040d4003408010514110900b95080103600e003032030302c0540e10345500345540c4403604c6010300107990700100c0750408400c0c5000142a103c51040600503e050b98801c0d894110540310310f01042c106900c1305940b40c0c0001c0600c4013040203058600d410140d09500d03160f944440b541c0d070b0b0740034180d40c11000d42140500c2d0100404c1c8824140000b90714881c9034000c12441c8004c1c1850b181c44131000da0480c0d0807000d401ba0611031814614024683d800b005003221540008030410503100d41c004640300c0d01e40a00d103035030400c08a50108210710801140000c101d0f011714191002c42d44d02d00074282882d0400c11142c401c1d0403285d0061003182c1030780c2541401c3c1c0302800d1080c03801a0180d03100071030b06030002c6c8034021138401c1c20044200761041c10314020705580c0783d51a541c5441010f0328014065265a48003000000005216502c51038014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 126943561 1250 126942311 126942317
    0xc21010603051602011b05091c050a1101020609060601121d0312100e0a052205010e0708030705061b04170705010206060909060414010213090902090106030207051b01170106 76
    0x283c5002140c1c0b0081082c2203000c10300f96030518000082110340c01c1ea41001d21010380c908507807280c512400242500d1115510610010f002d41560810302c40c0108052109902030240a82c00001c40700c01243d031201e04580d000310302d42029022800c10340c41040b07805503110100b40301090500c01d11303030b0000c0b244403410444001031703000050304004059040041c035449181c807000d89840034a072415041194000410305a2007503580d8000034041000e900f214018040b410b407400c141520a85003d5008010546a4014030310401c100001c400700c00008507140b5541c00b40107820541c5402140c0381d14002d55010705038a00005200100398003450030340d10301c81907502d40010f0105500d84000642421405400d081c082e50000040000b5100000ba4184e001a40001e01211144010130309a009001d1003d51805d548400390001441200c59040480251300840e43d142d400c0e680d85106800320700c58064000e05030307001100c042441605103440e40748000010b05004100b0000211000320301c0001740c10807008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 126944811 1250 126943561 126943571
    0xd031515050306180f0408090312030a2a022a03030a080709050607020105040315060314030405010813020d0b07050c01060f06030b221a090f0f07170c21010603 70
    0x400d150880001340b0410329100d00680714204140c18a0b078001c00100064503944001600f80031585003003040b0705068141540407903ca0812070042000342900c0952445501d0341580c5044884000080320040e0141e2034000300b4098a0342c2545540722490102004800744842d0300348030036520f00b0b00040411100a03030b1041e00c1840c1c034008c050503143e51904910b010358414446400181d03000030403034045d00e4021050f0a8545c0c82504a800a01040e4000400c0d00b002c55107102c03004a4000040c10a8a400b41c80b001540e60707406001903d1803807441e1010350b01c08084030a1501146000081030f4201603a80380540c50300315424240d50a40e501c0d07900c42c201d09095400108801e0381d26100f604210f1004445500d2503410340c0060f100502c41500480103181c1e40c41e07284440c5150301e0009080310240c00ba107025003603d03024507640c82400f800c88843c8980700b131043c0081c512910549803103004101d8a0f140410700e403141001e90141d600b2100f02c03a40c2c41060585086600c440c030750b006030b000300510b03a4007041c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 126946061 1250 126944811 126944821
    0x120f061503092001020307081b0d050a09081b0f01050c0d080114120601170f121e030f01120212031204030219210e0d03030227030d0315150503 63
    0x7440000100e44601e400140f0501c140c141c0e03408000c41e13459907003002a0581300e841083d0546202d540d01050440d09101d03201c1118066600302e005043c5c2d480140d10b400c0f2085940b002415110101d000d10b01c8012055030100f5041d1b03280c0350740e0340c451454042c9000b9040c030784090151071600104480b0407000c035401e440100901d1304443d981d000180020381d9001510f10310480100d544a0041c00381d074428003811741e00380041850400c10798082d14108012a43c01d0120903158100c160b108140c4403543e801c00d400e590300703003045030340071240202c452003a01100740e8640f9071910005184240c0407a408850200030041d101820400340000190f0a07502c84c442d81402d00d00a880d19401d8410080c0d002c40145d5440d011071014104402100c0c1036886140c0b100385521000c68121000c4411981d01103001040700c000e03d0b0341a070103010410300d00c40c00340015103d0343c41c90341411a0204045549a07201a40d41455188603030020000011061910a402030315001000a4a031a203007480300025004000c02c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 126947311 1250 126946061 126946073
    0x2030717010b1f0e0f060a08010f09060303020d0503091504060b1206060d030305060d050304060206070306090b0d020f0f1c06050a0608060106050f0d06170c03010507120f06150309 79
    0x2100360822a41584000107020f00c030741085101d51080c800380b04810070300701a00d440f807250100144600500d0340382d44451030310015020410a015461440e030103e01e000c691540307188544401d49405400170202c040b0850004c4a95500003481c0e540309010b048180c5c401c07405035a0b00240168818000031900d02c0000e0309010103210b4091101d41c0540c03040d4203001458540f10310010f2039641510300491259159000300d81d41c04007580d0300030002d2000140000e0300a0f070101d83e0a001e129295404d10205030385480c000c1c207594030f1440c00d070781c40050260581d00614083c003044c29050310161041c850642c981c5c0005580014030b52640c0c4c0e56034078800386401041b04904c6040c0c0c1c400c4501c03800708030080c20114010341c3c1306d0050103040148000000c90440702401401a540100c0c21282c042c07000f1501ea400414000c0042070b801c64051180c9403440c0068a0103028041c42210b10f0303034800381804001511030010340144102e8041c400c0d036690703022540f00d985804000c66804aa1804900000d01e03140c68 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 126948561 1250 126947311 126947321
    0xf031101290f090c0a030e0a030903030914100503070c020a0308220305030f0a021e01060e0702010c120b010c060515010e0a0e0f07050408011802030d140403060f06030203071701 78
    0x81d610481014001101d103aa614000f250001e40d103400380381d2210128001640104041c007081c0c1040c1c4a4220400100369000c0103001c2540e2296654100d1583c3e00e5001c0380e415030302d41494a6006014030034001881c0c1c866406951301c03a04030301d4000d144c45866004505106010b07001030781e241c3d070002254103a401110180d01403044408240e0151030b499601c429072a070181410074902114005000b41c2140e108010440314402c01503024090803c000300340038024402c40c46180c0c0864030703c100040e1024018440c401003d55282c5031000d00b41c14900c6000020100801168144a400c4000078003081c040d1040910805003c5000014466441c0001d0001c115480d0322902c1040f268205218400984401c550000c0b05a0380c0a0741503114640c00380c401d07002e0350708026181d6107001c0c0044001d03d000345060010030f00a40544451400d40041140da00703c0c0462a40e1119030100320400018030340381e000520304501443c2c0010725036101d50001c5c0c2411010f52003902010170345c4400135540c034000c2c495 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 126949811 1250 126948561 126948641
    0xa0f0e0304050d02040f06181b140901030509070801020d0212060a060c15090605040b06180601170a110f041e05010914030c04050a020c010e0a050a0f031101 69
    0x3541082d18180c0091140003541030000d00542d00d51007000310074081c940146011b006465100314044620200680060540e0145030b00d02004074550010298040c003500401c101224903100d14000100c0c00540c041d1a01419000d02d43c45290800240e08000303201500c44e403082c02d1b10141c0c1da800300d00d00303060600c20040c1c07101d4072810f0300820411040f0303000902c0d0380d107403680300e83d401c10800390684003c8018984c240300507004070b09282c1080700f08040200b02901c219021244580f0366940c0b080c100359009400c840742d0b404100c801c0c0450f192a11035421791507104121000108211909240300f8000d60044100d10500c000081024040c020040d65440301c5902c0109015448610b05030009144008510078400440b03a1407402c2d01c07140d201070008096201c030242007400b0307500708024010020340c007820325005d581d481c3c61001f2401c440b01144000c4039640140c01030a501441c5d4503500da110304181c0007103061080c21103014681d54002e00411480b205001003600185141d1940c001c031012124038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 126951061 1250 126949811 126949813
    0x60c040509060f060a181e090513050304050f0303070510052a0904020306011704050309151801111504080702040f0b13020c030c0a2006071106070f0b0a0f0e 69
    0x1240443c0f41c46500c01d0700c00c0c54aaa00e014400c044100c03094041c030302e401d03812402c04d5442d1213220394861381d620000364044800c1e01c501045a503a078034443c40c50007090214010050381003044200f0241c07800d804110003480d03000b41681d1820045588542c5002500c40c0c0c4092450340360410000f490503041c1c40c003241000c14594130b01c0020b240c1e0511802c0381c400c0000d8944141ea0100100320964807464502086a51132403680e2031030304060a00340c3d52600f0199400340706540031039061850010750307010b59200349070001c07900b03402c0c1d0f8884005480051001e030500810b807040301202090a54882c83c807601550040a81540c0da40060040c042a034007441c0501d40a281030044450703c41d00c0f0225502034062040d0320040e04d800b00c60743c0d606e042d446071920490b03161184485582c14014010300c07414a5031041a901418062441c090000710b00074a24050900d503044000105a824040d00810100f0300c60398000c1c00038241c644d20450700b42001d0302d41070340480daa40d50068400406129104e194580c40d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 126952311 1250 126951061 126951079
    0x50c071104110903030307110106060c0308010b070821010e0a0c08061021050a060905040201080a0f0f1b090602010e07030219080a050a050613080d0902010c05060c04050906 76
    0x9114404801045018140660b55500c07448442c02011000d9402c083d80003000c0d281e80b400c001c81d0061140b0b00c03200c490b901c0c1d035190400000e1035601034405015003d40c1a1508411686051191f07140780d0000c0c0f0042d94400c41c2040701c440c60014281c000029414261030b01c540039410700c0351187c0502d20040c03a10752000e1600e1001e04440350031140e0598420310807140c010041c04080c5044512003115458580401c40d40c0001a000c0405500014810705d40c0c0b000401400e03940e90b50081c265242501d01a010030514804203008042030340140b0880c52a640c0c0c08a080c07241010315608a40e2455807102200701001441d42106511020340001440184020f20094403401903072a2189010b01c0000c0c4581d812100c2c1c800b584180b524004001d004031000d6400090300c905015890b4240d810782100c10303001d0440014461420049207001e0130b90400d90050500244081210007041c50075010b82c1404040340b45180061400c1020b603101c1c44800d101e850321903140c03c09202420f60b018107500e10525801c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 126953561 1250 126952311 126952313
    0x50309070f0b18180c09130c11100c050f030901200901030e210a030608010e06070909060609050f060706090309180203060607030e0d12050a082410030f0e060604050c07 74
    0x301d091a0803001754991309642d01d400b440000c1d220f061290103c40d03d030b41004000701300c880d08054045000600c5806496803c030a8009840c2151801c80e100310200e00c0620030546051008005150b0040d04400001000108240b840007034140901154a03808000500c112240d40e15014005110000800407c04c2e80d20030441480d0107488a84001c10344440030074009003040c03003a008007000b081560020480100c1d50102a600d40404030b0300c08020503420040000c5050071f510640e01111800e50b50302102c030342801c04101004a40045560740b00724140600c2010918900c140d65440703100b03441e41c80c045894000316103511003040c180e9002240c414001c0140ca41c4440c4111100a80d00d460112a412108400980502c0c0509806003044c041c10383c4101520750003e006050a504544541406a6a0009114000b201e8280182c0315190752070b03c2c5e441c03608001c400c0780011481c034200410707005840d9403c04101c1e808082c441c0344640c00b4a00f480141d040c54412680c0003140401218a02225 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 126954811 1250 126953561 126953599
    0x30e070e240d05070b030a020904020f04051002070e0705131e05010207120804031104020c070b091912020103050a02040918061103070c0803091507030c03060b030610050309070f0b18 80
    0x101d1280415800d400000501f4040c80c0d64121408260014021500c8030741290748540113170040e0281d58003c001401401b800c0ba400000e00004035291000b82e9441035a41d91001c80783c41d00030b01035a440720b912005000c070310800c004a40842c14401400010f00841c0f034440020f151200c2d541c060521011250550804208060112000c4d260003120b03100300c50300050f0108009106440104915000e0480045021b6234044000c1a684108540d0440d0241c10050b00c011401d80c24442c2aa2002071005900015402078202c50741c00402c0d000c0040c1016070303d0010f1400e4401c0100c00c900078101107a041c80802c03803584a13070088072640c0041c00741940707014000034240340306e161009024580301100144010070201305c0076035640c0c02c0c8440149207041400d0080d0182c40c4800c141000309081074400308498016009480c880e2000400c000c02905280c40c0c01d48055102401e603101d1070107091004100e841e50140d1031401403103c031201c40e50301c035084250038902c0222100090301c140711080301d4010f1001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 126956061 1250 126954811 126954823
    0x20310060e0f0324091203190905190212060c0f0c07030512070b060d02030d031802030f031902030403030e04180209010b030118050f07030e070e240d05 67
    0x594105001070a0680002645500c4090042c42d414800c0380c070345030705500c042e2107a03094030b0403660201da001e920742a80c03581c0c0700c2c4800384221203d5401800024003640c00b07640c5c0181e0942060f0301c002654800c40d12400d0501200040c5041010603d40c0c812003141410f0700004034031001c03070000c0d04150900a20b0b2030914425541c0c2103051200109542c1d810101c240180310041d80d1080444644080c1c4e011440c000b40c06c1540140c5200d41c6560006801d410440700c21003404c0c0d402009094007040c851026001000c030b0208003150b0502840d18200140c804004411224200900071515131400c142a00503141c1c9400c0d17450f045400a000c00c10000c0c0e000b00301c07040c04820864010950035201c04000d160095000c1001c0d41c04441e007000020034500c4000254140e0305440b0310035203000700028801040da6403ea0f0098111100140042d078514400d905c141100d031882e40c1540c91441e6a24200b0801c440c09440048401035105649008140c00c007003403107005d00303042d204400c2100c1c00307413070309078a441d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 126957311 1250 126956061 126956069
    0x30a27060e030708012901020a11060c1e0309040b0109030308010b0d0f0203041104050a0b06030f060a03080309030a0e1002100e0c04060806011401030219030f020910110d03020310 79
    0x100c08144800141d0b5410710149024005500082000090841c2c01910200b5041d80f030212604101680c1c440070351000c603241e04e9054110304014031094202040c45915400080c807000d950080e2000c031545607403c40c1c000b0390544081c3c401940c0326003800d4208001c0b00c10343d02d82141441090341e01040025000200360b8110344110172040d480d01a0012001d029015441010342a40d1002003000100aa02801c40c81c422405603001c010035520514680100d410b04882a0303400b8005200041c190015900d116912801c080c1072400d0541e603d544a0149400549038031440b60030116113082e205a101c0b542c094640030407506402c1a01ca05007002c0e4880f15000c0e0007500c3c0984941e007020112004015200807480060410460140e4a44419480741002c2c09201c0056002c420000480d61080c0203640c0b4903c101c0d214600e0314112890300354024a8015140b07004140c0034440b0700d046640c1d44041214111050300d50302540c1c074035400100d092249442085050500c14418000c3c501c000300d013603105803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 126958561 1250 126957311 126957317
    0x150906020403060e0a05070b13051e0301020403230d050d0b01020a0803010f090b0906060f0a0207050d0c060206070c082b0e0f07060207080c09060111010c02030a2706 73
    0x410014140080684510b4002601c4142012003620200034000784a80d50709009400f85c5078404d84484500c04248200640c050111b071850384280b0081c9419441686c00e400343d14840400b409440001c02e0990f00b05a1040c2c50584402c020a12040c00302c02000e4041a842009131801c0041848082c1a03800b628100024007503880941200a034020054002a10303080712116423a0343e50380c514458021800d02400384c9103414580703407400c0d13410240c09103801250000c08090030401c0140084410343c0151071143c0840c42015400969038030b40714050110203005041c07052582c2d00303015019203080c4c1b020303203550100511030440001081d0310b003060710050140066501d8513a1201c0135900700c2001041440300301c4074a804a0072a007024001200c88004402d5020340c3d80150392100241e8482c3c01d01e214404443d0044c8503000f401c0d10348103441aa12140504016011840d0b07128010f08550141241c140564000900784042c180c00a0b8510b9a18185170313240e007484180c0c0707050701038000309038401d0b2000c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 126959811 1250 126958561 126958571
    0x8071410050c0307050a1101090608060d0b07120e011401140d0b06040204030204020f040503070506030403052a010e0c0406050607080906250c030b0f0103050322150207170a15 77
    0x25500043c011a0741803900001104e403043e1890a000c0c0c0d00381e45000c01b0a01003040300c2400107260307002ea0b28841c45614014403801400d0000d40f03961103107640c001c10b0581000381604580c000302110340b04a585002d402c000004440c01050204540b860041c1c0012791301849013564020581d64a24242903003903448022901e0319200c1c4e10114010b07000300d810003980a0700100e0000381e0458044040c208480f01241146e248580e12001d10010340300c19640900020b20400c80803a0074101c090b0507034940282d41c00c0c1141c0b0f40c000c3c1c2020508442151818001070340160800300309a150a005000242c02d048a82e5442c1404507583c1300c0407840b441c223801d400303510b012910203c000c40110007041c200d00d6074680a88110f00c3d42ca00703058510301d1400b0460341c6100c41e501041c00100040d8146060340d82c040300541c604200e038015140008501d40c04500c00d4840f0303403400324140d07002c1000c501c641d03111500104402e504002031140d408046044140407580103d1001e0b000c503054585062018001c802e0000b9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 126961061 1250 126959811 126959827
    0x110a0f05030d06031a0c030103020d06050601090302060d05040b01050312071e0b0f0403031a010801030609020f060c010b030c04020f07021005120106080402090702070f1503020706060803040807141005 88
    0x20450040b2140101c55500c0e00314000b003444040814001ca00c0d5243e40090460741e10f02404905a000c20300010303400007511060500018166403246801c4803050520881e00d07643c5e54001001c9500c0318005205840d124001d1000b0040864245405410124041c0a0f42206007002d11080e0240001c0642501c03540c900d0144010140381141070202d400107001c44c42854152004c5010541c00d4904800091801c401d56511040e60303054081c00c0b0105a4890646929546402000d864903400c2664400004082e101035995000300805000404000105103080b0920400d070600c981c48100d40d0080780104180c040c20a00d104c11034541c2d50b0b045402c20503283c4404801c1b1524051800c0707410707101c800030300046602c0783c10010161107584215400a659621034270202c1c0c655280d03220f40c6859681d03040061000b48480454a40621035918006041290a488038030075118244d02441e440e400c001400e01c442c0d00b0601a001c0078000b021042d0441045040209110000c4032400e44104100490811 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 126962311 1250 126961061 126961063
    0x201f0c0602040801150e0a05070c06230702010f0c110a0b0c070c060903061d1b03011509050103030f140406030f0612060515041e0504050f0604080a0f110a0f05 70
    0x34003410f60040204400000196646001c4d0028010f071905410540005110642c090082c58822282580d40100b10b44281d076070000601403e00a14000c00343d07200755042070581d60180544180004c0e030001c262403460300e41c103208490440342c0c10400c03c028080c6210140d0340001d90402c010340e00240008266a80028140781e602031940700505018036400c0005031550b10001003800e5038003500e001c00056407856002e200d4a10341300603814842d008104004100c0303507030007090402140090b0011800a140403c0103416029a4002e51901340e942c0d0014414076601c450f02c1c000e126010300780b44204e40d441d044644c4183c001c41c81840c003056220000c40200c00b11641011000304415481c90a00002c0c52030608054441118141c014030f0300c0d0703403424145203094021580d9050100c05100c80403420040108054140107109030703010310460112290b10201001610301c12400b8544941c0c035a120148010700c0070074072100100c1001a84544007c8a0b400442c403512041e9200c1d01089405040303140c03075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 126963561 1250 126962311 126962317
    0x607050a031e1434210801050d14070906032103050906130302120403030f08100f0509040c050901030b1603020702180403020703051b0f03060c0306011d04050103201f0c0602 76
    0x141340444481c030802070401c00c90300c003420070314110040d0b01c90701c0760301d0444103e62007042442010751142c0e00c0300c04540401c140c0031101c0041c3c2900c6c0182c5a00c2500c96a806041e10200c1d402102e1181c03030b609410180301c007070201e0320400d03c065103010301550600c0761545580301d401602045008606103180020540200001040f42c051401c080303031110b82e41d06000d0038030566103801d10040740208000901d031424103100c040a0728001141803501034100028800c04000090003220a81c503640c0004c285903403145404d90080d07104960560b05482c0092114070040f1803441e4800505006001c0302006a0b07444402c98500c802c045046001a038641c10101e00d040c810368000742007405100d84054561111070240703078135200e05582c81000700d040c03441070550f11003049400782540041800805c80a41c8292100b88105c07110700203414005401c400001d00f22682030b0b00c110f407045003802100b640040c0281c0318842040e07003180da0b1821580a010302c0d90480c11001d20800401030701d800c0030000c205031a81a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 126964811 1250 126963561 126963637
    0x3042102011b0306030302191203020c0c03010e07030309140a060e04020d061e06140a050304031806020a0b09010207030c03030221010b0304020307080f0c0f0607050a031e14 76
    0x40b0b81c0c0c80015516018009150500003a0300601600c40d59030b02c02101b0200b41900039a01107140a0310783c220403000c500940000c07a120706980200d280b10700709a9000d0041c1e40803100044082e100143c035629000d818080380b913204c8010141c1c0955405910750711660303001b007251280d081128080b00f850000800030b200342c3d20140106480d000003c03501c00100f454820421200035100302081c1d850f00410b54840040d0100f01c84141010000300200c2885a000f5542042c400d0420f041d44414440c0d0940c01614580c00c4140140e010460b0003061140b04c40e076160f0401c004000851a0003101e4800402d08100ca440140c1455000200c00c1c101400f4a10380400f6401c401080210700d584903803ca030701a0b0720507101607220748951000422140c1000c00c000140481c0c45004006103520002032240310350388504229030121007407008602003401803240d880064032954948403d01440140230f125088011084400c010301c00800107440500c1034125242c0540c1650300e07480e0901d120000c40030840c0c3c4004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 126966061 1250 126964811 126964841
    0x31903021b010c0320070f030e0a090e0d0e010f030504022805120601050306070c030909020307030c1202030c0403030302030a180302060a0c030c05090d0c050a1d0c0304210201 77
    0x440070410710650208070082201ea0707061003640e00c2085d880000c0303526070701d18030710718602088030100289007014200c0d12940309040c074000e1400070034005502428264030220580b03490340c0e24114150428040d10280b0b80d0142010b0200003c00c200003441504d80040e04018035546101150a40d41c076403402c1500c803040c0031040607161340088210540c3c0754551040301e010328103000c0507403284240405c2e443d058500103401810385580e0403004484455070040c0c02d50a200031f15001041c41a5240000c5218004c03684011841101210b40200b16480d0314103402da0b1944184203100d01201040100c80c00c0301d4041c42d015071661581c600400040c440b012100304061038000d109020582c0204d82d4500c16045005d042090600c03142c4107806039450114403a0014400300082001840c00c82d03092580d46025282c00701c000d076160b501091500c0507a400035008200b02440429260802c5d2881a9006c48045146815400c290340c40010307113800e400324055081c00958030450345c1c920035484a411180c04038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 126967311 1250 126966061 126966097
    0xf0304090b0307171c030b030312040b06040501060f0f030b06041413050f06010c050a0614100611120703051603050306040605030307030f05031f08060109060e070203190302 76
    0x419400300614010030102d009000703c2c14006030401c54045040008541280078003003038403050013908000a260607842091540d10f054458450720208094007494820b1011030009007841c0c140740044800040000340b14034106001844132940c00340300c60300e490f951410700c070740c0450307540e6000c0e4081d00d0380540442d0000004a00081e6002c0f403180540d80c003800640798080030301c00704290201503800884a105814207098041744130340d44140883c00e5440e0041083c1d8504103442c1d9a81c0741580e403110071202543c44a081408444130b002c07447c200060400381803810b03100102101d80340d03c41c10f000401d1008030401042c0c0030700b418002c100711030001c505d011001d138480745c41e03140103001ca400c2950310398007039441c0000204203810004102e030b41007501074480062030103000508a640b40d00c01030110340c003c0c6c045001d4080320414050503074054000640500f495604040700c000807602a907124441620b044402c1c81000c680100440740819070b0043d4a0511841c0017000368041e01c60b400080c500c1414030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 126968561 1250 126967311 126967319
    0xd0e0109180b0906100c1b08010507090e070512010b1b0607030c021203010b030612120705060f28090c12121d010909090203010b040c0807020c0a0b0406030e0f0304 72
    0x10ba807007006010001c903280035140e01d07101c05000c00d584135980c118012680024680002c01c0c880f15010f0545c528030185a4103068440d02c2031803d490301131358404041680e05205101d0b20f40c9003800c07540d1200c52850950304148035104810355022062217141400d11000800c0e000b540d15501514014000003c100d03100741c10143c0000b001407411200d50320060040100d01120f589800d02100c2c12951046070441c11170b202c5008028041d2010030b040400780c4079041301020062141009884d03410b024001501d0701d845c0010350381c40307440c03001004c4681e0712048095000c29200700342020700b440380c0e0b0345000003401202c1d4a082800aa61a00455861f40e58200a0307000c000b5494256014084141c0c2c47e0035458540c150800c80300e0301d2901545012402e681014000c0701c950754061028240003d00200300c0040c6039005c41c1c2183c400d6881c4800041d0180d0401c10f04030b80400000313881c103000f95140300d0518a40000c04100d8082c902400c810192500ba820314888000c0190000c184802403e413940d5540d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 126969811 1250 126968561 126968609
    0x5150729010602060c030c090102010e07090b010311340519050d0815040b011b08031b070807111f020d03060608010503120703020a0b0103060b010305010e0402030d0e0109 75
    0x5000031600d0080800000450750500c0400c40f18010901c65507428210307200e07041e94503507503001541d45a04543d40d40b840e4500302c0700c3c1000138a0040c001320500140011440c0001010382e00d6029184980b0401041081c0c00c290280c13902040108a078042070707048c0040c524100e0581121414098400d10400c211922041180201650028460011107a10002102c810b55040c00e04903034000c1207900040b140e0007507040c05d4000c4403070007030140341c000d40e4044030120000320304005c81c2d02682c0d940b50100410141e54202c19030300c5425140d440c0303060f08213240707540da064007841203002c02010788414180d0908240c5030301048e102d140291002400e40d410720641c00039965807804901a000a09120300021a0b6008900182c1a1100540503004900d442c100030180e56201c000d04a085102d40c074160390210b60f0b85400c5d24040c40c40303035601044003600039000400303541040e0001380600000707909200040e900041d110544e0341450806400880404005072844100e9600442001000c00c807201d800d185 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 126971061 1250 126969811 126969863
    0x9011b0c140103050601020a02010f14070c14030f070803090402130306020307080603070f030f120e06031e0705281b0303020d110406050706020f0702040606030b0f09060a051507 78
    0x15080c0e0f4200300c41e6032000d004982e100310192004e40030030404d502c1500da19200d07419402c100d0010718030140c07034000740d41c1d10000b800020350b1220711030507904034003031350070b85402e0001cac14600d85200c0c024200f041c01c021005440e44519011148110f500051842c400c0c841c488841d0300071904402c0454a0b840c00b80c8000d03001d007100326151803181c05810704c08200c002511095805603500308500080314021580c0303145244c0071621002d0240030541c0f002040d07541da102e00a510a031030068050b10440f9080c1011848114058102410302170700f44503020100030030766061049031317141150000000c074144000b0380f80c3e1034414030f0551525450f4010401810b4040e001480d41d415111010408420360307940c5908980140c2c05180000b400822021000c94101c6d000f600f00400050841403415403203500003400c584640d807101000c203840c1e058081883c030341a0380d0846440c400b601c5c03455003132070044001060052940900c41c40f41c11a841c4070300c1001109400d960b0ba540d401801d030015039021a0304004096 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 126972311 1250 126971061 126971099
    0x602010c0e120a02040b1f090614030114010513091503020a050a050306070c2d031701180e0c0604030c0f090903020601061b02090a0e0f0a0809011b0c 66
    0x5001c0c0700303640100d0a01c19510500420803401425110f11254200000341c00860320b840e502c6080e02c40d000180460000409108902c00c0d2191003c2c0341c0b038100094001e0210449003161103105000400c00c001e803040b000706a5160919020b03039104034030003c0da001900640c00500c201403600810003100d45902d0aa8000d03a4001c50714030030368654481c10401d524005005060705900000d0120300c5c0c06001d03c9400c0c40203032280203000343e44003900740c08248005a101c060300c040c0503120309000c18590082d6000020ba800c075010031080d0760500d00b100010b02d143c0d6005400684e0350b8040709a42c04018000001d030030030000c0040b96900d42e20b00f0170146400e8207002e400340c4d025440c0c100083c032072a1131007200d240e240d068015000d140c3c0382c16400d4816040902442c03003c00c070040c44000041c0e036071682c0588101c841180c000b51a9030404440b9207032111401c400100c41e80007820704804503401b4001d03144400d1342460802540549038600b14800303101c028005100e4500e80e04081001c00c5101c5180240c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 126973561 1250 126972311 126972317
    0xc020d02040222050f0609151b0604050a1a160f050409090507060923100c020303280903032106050d0804030203060c0301150e120708070305060f01060203030a0906150602010c 77
    0x44840d05c010000c10f4404c480074540d2010614201c0322200407804003410851004450400007001100402800e19408480c01c941940000175000e04001c1090040e0304090700000e40110145800c0044409501243c040442803240942d98461f4881c440d00072903010700a401010b120b881e0031071520b150703191124003c010200303803110f1011401d00312501588001b081540c581010b84d0050b40c05000d80d0348598600c1d801003003204d860303810151702c04000403c8240c03031206003200c800c000c8640802c0016044d141800801c8100041000444d5100c4e0700d1005c4030a09000e80b074140101501c620b0f000700929070105400c409610307016003d00100e14058000c6134001da040d02e0040d511030000d801c5901c401d0052503045d407a0140000403007441004181d890075030281c0552030b000c4500c4c1c40d90307161606aa02c9259154066007040c01004020300031143c204002003480b09a55043c044069200c0c00000c109005c1666034440d130105101242d00310305200702c0e00414a440280e1101002406001c1c3d4907959804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 126974811 1250 126973561 126973579
    0x160809040f0b09010303030209040b180402040b0321210c0408100603080a0c030311041e0e04021f0c02100905030f070509062e020105070219030c020d0204022205 71
    0xa40101030144031851180204680f00301e07803c585e02038000707400040c64036401c0b580e141484840c0b03072550b014100d1081c0384d410b4140c01c2c6140610401003a1248040a68000e4020403940c41601500a1070302d6581d25811500c3c03519503038441c1c2d01c41e581101d64000010406100700c148120b2690300380c010b2040e120b8080c1901d000107400d204402c16203069200040c000103007000f0123035000d8400c1c03002e10280740c405c0c0703400b00e186100d00c100003005402903000010010f0065080b8101189000746e01c000034148900340e09181e1401d6000a0000783c80c0c001e0070f01c13820b58180000c0c07041903c503005000800d54014400360074a04540c000a019620f10b009550091017803500160704c0501c005103078002c4650040403c02c0319542d47d8144030205080701c0c507070b500040c0041c03614071035004550001d909240d20340d400003a213441d21060092520141407515207000400c3e00c903c6020030f0b84120b8485940741c0541d00741040d80c8082c404180288a550f8041103044000b8507491a1001032180b20000c03100c0803114200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 126976061 1250 126974811 126974831
    0xb040f030f0201060b0301090908120411030106060e0604050d0201021c03090204050c0313060f0204090906020306010801060908070603051305030720060f030105040f0b03070605030f010b040312030e0316080904 92
    0x1081300c14030f00801c150407400380b0041240480540219842d0741c4a541054107007600a2460854040181c8041b160072401e20b003105d803503007424480c0c24010070041c5044043c0540c5180400d100b80f160b03008041c00740b2a882620421759008101e0003d405210080b100074414240c40000c00030a00001308078411400e010100d80c0c01d42d07640003a680908006080041c41d03050540e5013400603c001c0d2030a000554080c48005580303903542c0b280e260342d107000c0d9001590303902c0c0c0507000400c100e505800c14810300281e04400d101600c0000344940956040741000a20b544a0804950300595000300c0284584400100301003080166945524403158034107400c0e084000d0b01041001ea8040e4600800f907004c0e040c4010040361600c0c1d0484400580250b100040241030100440d040c25400d401201c0459800018008461100c1c400a801032220310051420700c5d096030740f4040c403088105800010581c40301d03110a012a000d2040301c0390f500c42c100d454507054489241903003007034102e815400d11861406003104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 126977311 1250 126976061 126976063
    0x3030f060a0b091806041b08010305010b03161a04270606020606030a03031a04050c040f0b0412081b0601080d02060901020c0a150e0d051903090b01210b040f030f02 72
    0x62590341d8010800307004c0044030803840120840007048039074010340b0355403410500e5030b501e08401040612070f501e6041c50b60450800d075081d01e05040d407203030080d0b21004802040b8140f00072082d00340c138084d80e9541c0f414841d1903160380041c0a1900429950071540c5080c1c50003807500801590354030965030050210300e0740c170801640c80d03000c2161182c2d0580c015005100000303111340e1040c0d0070300381c1c5a4110f071852122400401c0480d14100c8081d141081c00003024044201e0980141000f481c3c401003c034506810541030150021144800411004020030f10990090360140341d008803407020003c440c0e0079a5035801e40799840080301420005806118080750080f041070003194004d0135400010243c0341785556811808484004c1d03403d252550741d801e00c040d000c406120802500c0119980c490315500c5100e0014a4001c00300000001d15261032198000540c80840c1c0c14112a6041c65051103011014402201d40210705002040c0300e00080401040203022031101424500a17615403c150b02508810303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 126978417 1106 126977311 126977317
    0x80a0e212109031c0f0903020106151b141005090a110409030206010501050306010504030501020408012c03030103060b010e0405040c080d0e06071209030503030f060a0b 74
    0x10888803510880c031240725201c00303400c01c0d00904058101c540c0d02d106035240b40440e00002d40b5130b41d5080e050356100d0031041c1400c9100384000700079460024002c2c80035015440e0b06a031040d1100c804071b8883c420b5080648001407900038010b110307440d004980c02ca01540440d1501c51110075130790905441c0980d6018241540050510084c01e29015110703003510034125010703500e0700e0f80b0400460341c00070304281118400e0900c540e883e1540c10040b682c510468001030a15800064006038146055200003030051020500400390080503d1045036180011011191f50303000344010310100d01164828107001d10141050b00710001c01c003021a0582d203007102c040e100040b0940c0300b003103000c0c01031000c032000502c44c0c40d080c00700b40810400140c0902885138050078041d181c0c00750300d94540c00742502801840d04182140c1d102d140101e803440480301c0403910345001f9168014001101d407841c0c029 = true := by decide +kernel

theorem cover : BRFrame.Cov 126798561 126978417 := by
  have h0 := BRFrame.cov_init 126798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 126798561 ≤ n) (h2 : n < 126978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
