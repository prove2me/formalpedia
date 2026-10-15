-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4688
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:25:12.893165+00:00
-- url     : https://prove2.me/submissions/ab2949c6-9ee9-4239-9c01-e0f6ab3657b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 842985611 ≤ n < 843165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 842986861 1250 842985611 842985623
    0x40b090106060e010e120708030708041a0403020a0504181202010606140a080117010902100302120609090d20030714100e0754050c0304020f0d060603 66
    0x5000408100307029110140c000340c03801d4240c070f21940300001d040040f0344030468000c030041c4003030050742401480b2080181c4240411680e4400903482c041c0102d134094801c43c2141003c4000d0300d001a4107070700884003141c0e0010900c07950316041100b00301c024002c0034503426034248100c100e000083c142ca9020700c22403a56400006540380761290107040c20004c00144d80110404002da81580c1d0740000e55a41924a100d1040103c4030343c143c0720500405010b0380195000078060180c50203140e054000b8030307041d040c5a00c05903190304c0e0b00d010b108d100d00c0300340c4010020b030308203400e007400030391042c520a80014078285100c03075205c49511115085502110301642c1d400815032007001c00001c200504601c40d00300c02020812280c201c00d81945403401402074010b407490501101542510102c0c4035203440c0e905040350004c0102c100105100f10090140301500101c8490715069501d0292003045d1042610902d0b252650b5660b90810a0f80c404032040b096020740ca5003044008600c041c0326001c043c40c4105 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 842988111 1250 842986861 842986883
    0x90c04090c020c090a05071b200415060e0a03171306050304120f0c060e060f070f080606090d0b0405010504061a1e0406080f010b12030f0f03040501060302040504 71
    0xd40340825116081c000c042554000304454100762100003034540e2160000100040d0783d1100e18040791800b460034054a0748840520107030f0103010707000c40b440c0708840881003808807004165080c4801e544141c01c0640300146001c000f000551300642c40c180c0c0040000f0070410059440c0d0352021140811803c14080140002c01c0b0044104c090b8960b000185c440da040c028150b00e41390392883c0c8610482003100c01000701c03064041d04654081c2000d40d41c0c2d543d001c10b00703001c8000c7e04118076584200841c0e42032907000c03400e800320345030601a0f1580710b42016a0358a48a407680c40e0802d01207281d07c1401d80ca500301c50707450701c0b07007002c070745902c00c0340d07000354410300000c54103040c6401c1201c150f8155580e004002c0c00c00041c80320701036458882580e20700c2e000341c00c0c2c18a2501d242c000140203110940c06448580160922021036000640c01021800c83c216070721b00900840c041415a40d000b090072800c80080300300000c920f2544071001641e4024800d000115009481c0c1d0301140564105441c2194034803001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 842989361 1250 842988111 842988119
    0x60c110714090106021f0c09090c0c02090c030c0f1c0204080a0506070810120f080a02010b01180e07080903160602030f09060c04090c0203091203041a0309030901120b090c04 76
    0x4521840e005004d0b510041c0790031b0500190321990350305880d4030250910350790040700301d4003800f5401400050060f604104030190540101801000b0a0700e000ca202e1481d140000f49802c0c03160042e00d000780c2550009505000c40c500002070103034418041b8040d9000c188111154000c1d039070000304040d042401c00ba0005403014500070b8904100601040e0074001110108003102c034024461604a6407545455500070916050188151904400241900000141081200d901508208200340d02a603e9003910107805090080d69a410301518800030285408200100d101385001a0014500400c0c1e0f4503002c2c1c0030440741e6440d1003c89084800c1c42c0c000c802c00c40c41059000116501c0300e511005400107291000149849100d207005103818940d0746c1050190b0244208169448108094017400207074240450380c40c0d4a03000b52240003188000e180c0b802c20341d1001c0e0000c0da401740101c0401141000e50003001901d0802641c100e4010907a82c135642e00d1400c0d5a1000e0090023201c04206040d521418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 842990611 1250 842989361 842989369
    0x6070c0806100807090509030f030403050702120313050607020306040204050417040e070318020102060403050a12050906042915121c11030c0709020906121504060f06020307060c110714 81
    0x50340601c00303013843c0c5810040140c60110494116081c27040c405650b950b124502a1020f019000e0040d4001041010400340910004000c240945203100d004642555940410040d407246c04002500b680000d0041001030609421694102d40300c2c2d60800100e92040c2d8032184150007c1c0d211043c200609814060925018410000f4a1098004081034900a6000030390764043c09030004080043c0010000c00c9640b0400200044182581040c442410704041107580ea0320140c8003542c0a0030400c0c10713201c5005051440030000c02071554000c045584181c2c4090034552910106a005881c10041c40240b10f8144603180c4400c9001d041020780302e0b51510300800120914800180d15801040360100c202d000017908001c0b14845503025940c0c1a86034017050440c043d902406c0c0002000c2818040c1500c00b0f03444201c0300a801341c07020071800b5030310500006501150320030140540c00802011020842540000c1c1d024640d5040001c4800824200103281c00d1165100c59452100f0020304040f03460 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 842991861 1250 842990611 842990623
    0x2c13050105150403080304140c0a0602030c120403020d060507180603050411040e0c06031306140f0f0402100f1107081f0b010203040501050a0210022b0e0c06070c08061008 75
    0x740080580c1081c1c00c44d030300c2145c44c0c8070140001c0e0182481008102d8420740400513940c0000003d000700180b66a1103201960b2500804142d903400d000d5849900c8813125004151821243c0041c218800d010003910340c54010b00303004d044902000210f0400c071a6204003e030800d001490325580011b41460b0604006902020a0018501c80c0341000c0007810440f000084c1e035038400034203c03021135890301c400c4508003840107103104c02080c3e41d04216020721444004000a8454200000c1c20000ca80e250f103800741d80510200d030001c2d84030103c0c51940e14030503c50140b4440001050a00c00045402c0010907460201b0030b80c00103a89900003264111921441e0710100c511280250b414007090040c140040c0d12030240f80241410060085a0a00305034420064116481050b042c1159501c5560305000c1444410041442001170709600e110020582da01c00d04241f410310001038404081c1642c10444d280e40402c1050f1100c1c0700e254808200c00e04240481e41c0034180b0100f180012915103492642041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 842993111 1250 842991861 842991889
    0x20403020904350a110705091024020706051b060a0f0b03070302031507140a0504150c0c03080d0e0f06040b0609010b040302042d27032c13050105 64
    0x120440c0c1400700c40424150740c138060160070700311441c1034045507a525004081c0d12866101c040c403000e001c41441c03510414815124003807000c403c52440c0b04030615428522801010040e400318008020035407281026000b840500701c4401101260070b80098a4240155030101c07882c0ea803010082a0740809101c0d204200c5821f50103816558030303680001c0c0d2201d03000d0000c2d621451b80240011011445503401c00502d00d10200c41540f514450b00300201241c205000e0030943d24008124021403900810b03404603055800480504210b05642e40c032500c540090b10b1040c99a0344440c43c0000c02c41c01800018a03503000c0b40001c00c060302e4581403075034044501034555401021540c0c014481c0580000841d802d8940583e80442c0c0300c005103406554034070401a5401283c0b00e6006d20304224000d44d00110b104c282e07100140100d182d0284207280090300040c4004011611400b1022414005400e11140307a0441240e00181001a04041a41c002e0070144c2561201c0c2c1d11070040c45140750030341c4484042 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 842994361 1250 842993111 842993183
    0x623090d20091e2a040e1506122a0403050318041b14161505070e1014040801020301060c1703040312090507031401390c06020403020904 60
    0x20820b900f00d00c100d50783e400f804140c0d2490307001900c0000650076072154100390003466500703a6500c2d030340c5580e0040300106843e40c07104000d030021549240e1810300291065010701d881003096070384410f081e850240906055890f80062080c0140d40c504402801a01c0214000d00103590791ba0300042e8a49c0c3c242500d001103074400e074505004000d600701c3e110f00a003408141801d002011621100505409005815071807504000c130158400801c24200c0020106d1010304c00140031b180c13a8600b0070b0b07421200c41d088480c0c00001d0b04501081051040c10050301030b1038003060f114902603c0704046401da910903001100420911620b0404020500300c000c16400c41c0d1421090450800c1c2c0e8004001d402c281c05c9085416855101c20028050280304000096078403441c4035100401116040d070180004184501210b0359014240d0307450300d881a81c401c0e00c0c0d0f000c2c450000000314070003020760b9003856060f401d031090769003030002200580711606d00c1c40c000e9018803400220014204030110701002c5280e05e0a40d0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 842995611 1250 842994361 842994391
    0x4230c070809090c12130b0901140705131503020403142125140708010b06040303050c0f0f031e09090a05130611040608010623090d2009 60
    0x414079003010344101d40307002c403041242c40d15961039025107070003420780c40c10380c446078282401441040701a4207004184201540c41c034640d50080d610382207c184500300c407280155000040c0d9414440d1005050b00445500018201d541311910040f10035500c0d500c140c00303e43d0000c4c040c400e025801003100d06482da0840280107a0031200354507000141d040c0c03442e09003080c01103070942d00c2c964020b00c40e0765084004d09040032141c1d0b1509005400c0302141c0d80d03020880c0a10140440d4904060080b0125034802070700c1c00d8682442c0d42d90071a1103611100001031103024141d51a810342005101004454110a000310b8452010788150b20480d5411125290400c81c01c2105002d152900014650b001680b074000045c00d07552400d1079031200030010310041c1300398a084d09544a00000c48003800660308640d88441840e030700c1d07081c29203152150000c50b1305414410b450407021103500d980100511400544007003031040060399121115034800f403400d5546001c126851034142030034102642d11020140070086 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 842996861 1250 842995611 842995613
    0x501020f0a0c0902070609060207051605030712150b18060907030e1c0e030a06150f0302030a0b1e0c03072a03050d0b09091605040504030806010806010e04230c07 71
    0x1030462842001140f60700869054180706e11a40850701803608040250354403101c1d440e003036071a001c500140b02c84c40300c3c58820105041c100068048152880107007002c589020310303202c01140303108040c040e1303402940701c00f10b254403500c41d6810301e80d2307090001d003850449040880c00c01951100080a00040510b800300b0901004400106452440f4280217045c0070340c14425011110200603110440d0588200a007034020850b00d6881040130700c10440c074660440d6112240041811490310004c3c0d070640c4056060700100c0c0384076100d030b500314884800c12350b0b0701f0260350709409102c40106d481c0d400041011040200b200e801019172030102e08400583d411750200d003484281c00140b100005010032101059941289a05600810124000400b00617103807400d100c2d51a540e10010354070390700ca94008200080d1900b0603000d501d000395403544032031100d5920360004541443c0c00505150420614200c1c8a0454403584565003002032408803e51840103414100883d4040c0030304095490601041000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 842998111 1250 842996861 842996873
    0x1081212040b0714190314150618030105011401020c01020a02090c07031815020f030301060c060c120e01050106110715110703060608010c0306060503060a05040b0303070b0a060501020f0a 82
    0x754041e0380405030140310345035201d044500143e40150004000030020782403118a07921013001211036041d0b502803140f1700030b13014202002d010554880c8803c6000300c010194a00e8020040c0c80050b154100c0c50702c10518880009080d10000c1e0b11910398204c400003942410f590600c5030010468081c001496410500c0e80422410303000100001048070307010941004051051445810b9880c020b1007024807951070744071082d419460000c1b1900584507800707a03809054004015a8100c4000b501c590440300d0083d280c0501401c881d02e00101004041178100d4803e04032881075030f0041032031000001e490f43c144003000e481200304158080e8264441e2404102c2d00b41308400400003030906150902980a139002060b151000c030307400017403000e82811400300b1002c105603c12003104907590740600420341c4d900000d032598070059500035005541800144024100798001c4001203d001c2d045038078000b800c1e1500160341d1015940c034004540c41e0b640421507503034100140220700140002410419480b55101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 842999361 1250 842998111 842998147
    0x15120c0a061b020d0b090d1b020103180f0c15051204080706200c061008034003050d1b0b07020a020414090d0504150302030612070b03010812 62
    0x580e003008a254010030805510b01004003080340d01500c0040e002070685403090001004070b400d070906125071106210b40d00d10a8000320580f03c4616980d44941095400440150641d40d54104074103416041c00c1c4005415042300c400160f024030200360200e818140c15490052101c00745101300941400810324400e52484816005544989d0441e5035518a10b070030800f81013100a19a40d88412660400c010540742c4000d11101b080034080e0740c840d42ea88503034040203594902549100d60300500c0000628142c0308012014405119080030242a401941c01c058209104110642d25000d001c1041001020080248507a0040c10b02c4031001d800c4c514090350780003400201804000c1094045250603000f40038000100350040c2c01031041522603864501981007d48540940d4820342d03021040c40307881a0240c03025100180481d10070302000502c120041c0d04003400b201d41c0300140d0621070407041e40030420740c002801c0808c62a80c0769894003a00c03d05141a07240c2201103117504124000b0340c0780d842401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 843000611 1250 842999361 842999369
    0xe0307150f090e3601090506040b0a0504081603030e19030206010509061825090e07080702031803010204050a0306092a06050307030e070905060a080a05121c0515120c0a 74
    0xa490360f402550360348444403004513005264154608907000d8244a0003044c80c4c1d109034068203980342e8640300c3e82c503400c013151030484018041803801c0c8600c180414bc0c810400d00680c0c0240350118040b8090180141000e4010510034038162001070b0800400d601403011a0040c1821106e002141c03500f03202041990604401d24031840445074009100e01d20021620a08050781e00c0e205640b4410840d00688242d009025030404c1c1d455000008120320f01c41c3c0f2401e07115038203990146041ca103c404402c88001e0071a5411a4195000d200108541d220f45100000550213a00c010031944030782c0c28090f02c44c0001488501c400b00c4031071031007a05004a2914441100c15600d8210358035030780c1100460041801c200e200c40e95018042c0001402810b0b500714a0241c50221100808a07a8803880c96a8510180b10014256003104140088504940d4090840082200b61b2024035001c00004136003192001c0b1900096035005440c0003c00d41005041500003181d0600109002c00074a0001015005a441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 843001861 1250 843000611 843000661
    0x11419020306031c02030408060c130905040228031403130819020d02040204050607060b03100b131107020306070f030b0a0b030411060c150124080103030e0307150f090e 74
    0x400513004620810440c0e0040000e0740c207039092410328203c000c001e079100502c0d5821000c150100803400c9071084c0318a50155030f00410113103880004a80400700d0450180e25030181901c0800000040b80308060b2444140303032001d010f180c0d01c0d84524040c0d0383c41061340d005400c3c654031945441ea901200b41c411024540d40440b410f001c0d1988900c00240a441150070a50704503001150388030030070503c1e42110085010807070a0380d1070111414090011221601034090f070200e48890704148031007480d4003c502c0008030400445c94030003541c01003450400103031115000200a0381c014105c0c154144928070003040102c0c1c4ca41d13884c4d85000c81c91102c500000c2d01c0508482d10030b00c06000e00d03030341d454206c415000b4504195a1400880900546000344c24031614412000803050440340010318050a0201100e0f40c0340c1a0059003543ca00b201c0303a80740004240d416103d075400c04600d03101c00c083e12031080851039607070007155110160028600b100039404506146140c4007402800b00e80c2e02910303450410808 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 843003111 1250 843001861 843001903
    0x1112160207030b0c0d09050c01030b2b150c2610060509240d05060a0302060f031f231009050105090d0807062408060403030207021201141902030603 65
    0x1c80100313081e21074400300c3d514103460f1103400700800c20f002c41c01020300507007628100428070512044c040b2042807400351448465240f100c000a150082108441d4a4020302c0004018001c0b540b401045500d0b080d40c07003000c5081c20038580c16422400c11051919400201850704c0350400b042c0050b4152080d00a50050000100c2c500445896030f50b911200303091954020780800c45c1505031800c003944506100e2030103604000005040741440460003007140d5015048a243c01549840301d242034002425251030780b540c46a64401820690380610041c0446500c2d1240c451050141c249801d41420505030003070709094614080990045045000c442c02820003903502c00301000060081d001450009080c0040030444a0901c180c640c40151108056220100340100300c00c060181e0811902c104089640310000090000e4401c0d0003404c10f4900c00342100220301602c0e0102403d580a6040d413550711400d51003005008a000e00e800300365082da80608501d981441808a51228140421442d100142c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 843004361 1250 843003111 843003121
    0x1002250e070c1e05160f090f090c061803210809061e0c07020a080f010507020f1c1b140c0409032a0b010608040201120b220209041112160207030b 64
    0x1c3c800e05114500d52501781440a403225043c1305000311034020040341e41d01c1c0501070b4040e07018501c40c602510ba0408a03484075189888001c4aa014145580308400101640e0000006030704203440800e4902514000c1c0c85584080c8005020304030081c40c40d00c0907030109040c0b0580c015901251460000b21481905155848001d01c0181e0311030f2083c020341010400b000000d0340315020900c540182e403224000d0200d80c0b01d00300120b0b80c0e100403c100000c0341d002000240b0b900a81800c1d6040c035a4214141014140720456120b83e40708804c2000703480740e450001240b0310700c00080c04920a4858101c40c00c100c01a80394500400501d40d0140022003d03640c01c114901565039040c3d0b1032500d13a030000f400b40c2d80e5a154070000785107070415101207000c41c44e6010001c4c100c04580c0250030495001030500403030703e0b80d2034002c01d107108252950b4022056081000800944a070b002d503000c0c08220202c011b03500d0301d4041144100e094000c0c1031094946201401180150f408100001100d40044d0440e01075121 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 843005611 1250 843004361 843004363
    0x51e0703060810061d0702060a27080a0801062f0a02030609150702060c090f1f0906090503060103030e01050c0c0406060e040e0c0603061002250e070c1e05 68
    0x354002d001607205003a0a18018002d9070420415903450301c50351054250303041a840c0790034509440c41c00168200e000050401d40c07066012403080904d507030100001003d00000c0c0100001c15420a4a200000003600054150807002503801032210b440e11104407622800021220380302d00b00d1810b00ca02035011025075a900070042c074010f554005060f2a43d504042e13029540d079200d40752030710241d078254a002071027941c00411454443c4103c0200d81d1700d0f2542c24410081d480e14025201ca5003c0a10004889600501e850310090030085459407d0010f04040020380448075581c40107110b5031103080140002076000d07040005014084c00c0072900e803600f13138454604021041c800140c2051801c0c1e00050817030b0340a06d40d5400032800340d0342048200b4000c000c1d203844422800700d80780c001f00c0c01c1001c1409418000e40d6072900010f035106450f0741d070210b1003110f0050241c00360200c0490200d100e007400001116158079800c800141420681080d0315541c0740081070a450503200440e440c03004d40e1042c080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 843006861 1250 843005611 843005621
    0x30f121305041802100503040521130305060106030e1603060b0a080102180117040c0308090a090501120302010b0109062307020907030c08010911071401020c0f0718051e0703 76
    0x1c000c00900c6010000300203030b01c22100c0e03c0011391050003251850501076000d0f0044034040da8000c0040c1503007842074284159800640c0b030b01005480d104100e01f0202c1400c1c01c0c5088041c40c0300303070058861545400401020380e000c851011140350801703009403420f401c0201c03048040300d901c1900402c00701d00c1c00000440004040e80261815400015903180340c1c00155544503a00000340c80f0105015840740c0800d50205080324001c1a08410000134404100b000001c0e00481c50024510000103440764070080548400780d22500c407544550070460101a0207000340301c0e81103420b103030034a815450103074018141541c40c8003110402850003904407107403009034111081960080e168110908000740001c008140c64001000018400c2c0004128110103005140041e154070501e0350074070320075032104058000305000020300ba650030000b602960f40b091105081d8202140003802c1c1c3c0b20314144090800c00f070038240d01192145000104a076140c81c5210044140e40c0310203448002d95255102540100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 843008111 1250 843006861 843006869
    0x909150412020a0c08010c031a0f040902132c0307031d01121e050603030f070209090312101701020a09180b36070203030403052101061d030f1213 64
    0x1200c980e6010603000015005900814100d41c0d00308100c640c42d81542703c000000c80c00242d400580b00d8000001032400380c000340d544a0005000c0f490140340d480c404411283c5030325040841e521740210a40301c1d58100c1c0c40c0d40c0ca556490001551810070255402000302e914554440ca14030303500343c4010800e92049001c1030032070b482d05100700004c5c04c0c1e040010300d000500d1549040c555040078006115400c2c040141c1d101a1942001141000000c1d400c1090100004141b038549100034000c0c955103824040d0302500500003940800354560074035090003043c072828007608603540c2c010013440290316070000d800f9040350180c03806c800d92511074140d03420250171256a0664001d442c548181541c001080d05081001501c110404251000d4035920140060440368500580c00170b100040100b4005d400403c1d80c04040c0c040f401c074480f10740312003c141e0360081e0850000504c0280703001c3e0600e4404044440e5081c81180209801c0d4070303030002150358800842e0203031841039003c00c10f4008880036001e010090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 843009361 1250 843008111 843008123
    0x150a0e0903210f06030714060a051c0203041e030801060806010c1a090d090308030f1b070302030706050105010201090f2402030a0c14030403090e180a03020604020909150412020a 78
    0x14004918401c40c0e15050b2240051000003c0105403286000188402210860103800c403048500c041000b613a0b40240115505000080192107006480384002500250100800580380c2c00e0509111b203003051071400310880100c00c140e0100201c1c2c2c10406844c1120701c80e1815200990b6520f004a40c3d03404158001000c8014003201150070078070546540e0701c102c04080885042c0484100c0072500180c8034800507141120801c0071500d401c41c100c40301680715044840300407080209101c4031041d94006401034005820220712041080411300485004100c00d01c001d20000c01c1d15110004140c4e11303208020502680c8240342007011035014000304c451203100e641151280f921000140c007412081030761030001000e4412201c0710031f0b0390038162030185030580e648002c0c0f14201450250460342c094034400e000d04d52010a400520340c01c10000c1005032190f406011141040d20500c0b0000700090300c840c260350800740c2804400340c80300058650082e00b2040d40803408907046030580c18011010b10292603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 843010611 1250 843009361 843009397
    0x1050d02040f090c031e080d0b030705060d0209190e0f072307020411190c02010e13150f12020415170604031223310605150a0e0903 58
    0x10302ca00b0901c01c2003202c0c0a02c2403040721b6041006684204001080002d052030014800040d80305900e03402010101c401a0445011948810000c2c03250f400c0a0300d40000c4a4000510741d4540c20b241c80e010f00090300304500180000d0820038408502800245034501c100700c4000028100c80c40764071b10310304800c0391031031501d40b14214201c080050350264000343d0003076051442c02c0d6041e140c001d04413039410b0419203440c140940d116400f00ca6240c12840268100014002280280d50360340141f20341e20a09010000780115021a83d0181040d00e0b40c0151005c115070241000100c80301203c401e149941110002400c98602d100f07030f403420712142c000c65901040b05a4408030f80d0000100c1d0303030096001b515642d072100048030142054982c2000030030304004400c4c400e0b040300d2144407101600b0541305405601c200c0c0300c60100c40e90000c0d08285990b110b20b0f9640d01102800300c0b502c241a041501564460501e01c050000304030054064850810310a4003040000c01aa4040c02581c40c1140d4801c0d02d000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 843011861 1250 843010611 843010613
    0xc01120c030f060b040e0612060610050c0312011d0405030913020f0c0a1a0105010c03030c111c0f050702090c03040510050702011505010513060503090a0524070c050601050d02040f09 80
    0x30713454016003d0200c00075410808140e8038038250710b0040400b20000002c0107a03688007824004110684000c80c4140101841035840c43c000070300c09070550000340c101c0240d1562408041007684542d80061b0080da0b00400d0074400410030201c11036041d0b80050702c00848100c0840f030074000900c0741007001c0310300071804a00404062000b18000200c2c2d0b0003039003080000442015074142d030706030a00c039060200e03241c1c07401c24000a019030000847c048060414000c2005c3d1500803900788400750075101c42c406041010000295044581650121824500181003600d95404540c0d1441f000c0c200c510a510b000c0b00040402000308101d01d0070005840c010300c00303802e01000107170290514840c13140c24a00b02c06404102940310300141d48840401c00b190184040c904081603d0035030001c1c0c1400b206014410414010650400003400100c03040b000c80403030040702c03030254030720220040e246038100f1004000d03144c003003400018801c5c10342e50100c070382041050541c030000300102480c1640721902030501d1200c3c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 843013111 1250 843011861 843011879
    0x10c030815031e151b03010e0a020705011a0a061404050f03030c07121e390308130e1329040f0b060405130b130b010803030108010c020c01120c030f06 66
    0xc10301444d00002e40d109403203540c1461014821503184111451043c00100440e450001340280c0041007100300601e41061034075810300350792502c0e9102969601688140c101800d010684000504080c82d040d40322002400500c8640c0c81a1710626118840a00000c6216501842143d5580c00c07c802100c4481d40d6403004400307045850744c0140c40e8003100180011281e17418000c03820243d584121092008035546804030301c803840c4450200d00c1851003803405500040b083c042c00707000d58000e8209a40301c031140720948003040d10766040000e4903106041445001d450818103518800e0780080500c10104d4401d61043c1c5410b6142000311a5401c048280028030502c100f80c000328234055020003200381d4900c0d0520042d2403003a1141e00613042202441008207104280c030315080703802c60308000c5003041d5a0315400c40d42c0ba805e0300103400e00d0700000010044203400348101314803000d00d070018007200c85008001a10a40d60702c0418030000e41c0b0b03408403105072803180e40403142d200c00c4054200880c07074556100c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 843014361 1250 843013111 843013123
    0xf060206070e0f09041b05040c031505040b06040e1b041401080f07090b0a141209210f280206061504030f0f020102031c0b010e010c030815031e 63
    0xa601041c80d41d030450085041c1a9103051143d41c01030726003100e544880e070f03c0e001210960050440c140c450b400c0d012505664074003071184a84465a0007007080e0011151600401d291580f00e54411441c0c20501c1c1302a86410050b5001c403019030344184c44030754038251101102c100d903003201240380d60000f80209441e8407441d0340c1e160a140030790b108400fa58950480c00304040068400e0700c0852280320007008800940c00007801521550301c0c000f2041648100c0848094100101c12a540300b0310710100050b20728100030303c100200741c1a5000c20701c552078640c0c000f82071241e800a80c500320800070314100c0290885200c1d600320484000d09070340200e20000000e4441c101624030500c43c1103400758100f0303900c490400b42c1d42625040141d9500c0c5500c10b80d50321343e00c44000403080b81540014000c1990509d0107050962030584204008103114000c800018116100301d46490b0600c80c1c92146800481e60008240c0ea0114400e03204003540320200d0002407500117207030f000b40004c0c2c0340c0e2450102403600c0441c0c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 843015611 1250 843014361 843014371
    0x40c03060e1f0c0215010f0515030c030a0906110d051f060504051309020a08061506120403110c06180915060a0c0312091a060406060212130f060206 65
    0x200000c032401d284031911480e0501c040c0002c00380c000440341403078946900c80219854240111803180c1001c0c1401c00030850242d001d20a07a0001800c204400c0c1000880c9040b802c041e66035035441d510740b8030a5005140000b4001ca00c841e03070fa5420751810016613910481d00c10002c0c28215031200c004000318009060100c81499103000c4080c04000c880111910050a45041c2c1d15141d042a040070207000c80c4e191841801081e4580340c5040a0140c1c9984198402030030b82d82c00034000510746007541d851a44845185103004042c01c114003951030707405240c05500705505203008a01101010202c601d403e0000d60090340c0030b04c00040c000302010344030408010018003642c100350f640d9074039041002c1c1e4050a01c00c280e08614204102702c44d5a1041c0d80200c2c010780310382400703902c401c00700000104039081c02c0001c036410b204112105401c0c0b08c2c01d6248917440841128103100c5a030a0001c004c0d2940e00c100c000202810340402c12500d48010a200e00001c1c3c2455281000e58076a00c0310700a6480d03000b998 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 843016861 1250 843015611 843015623
    0x206160518041a1807090b0c01140112060501060504031a062202090a080a0c1a0408070b030a1518020705011d1608010528090c030b10080703050601150c050105040c03 73
    0x2402000c034130002d85414428030903a1901c100e02443c00140e844d4585c00700619a09a560b100340d03480800d030455039041d020300980c41408030100e100303141c1300e4211141030b0032a40134454184000c2000444483d4529000554426180107030346a00c0003042c3c400805011030b08000c3c1e101c0b00041c1014003d58060908100215410032071142d8903070704552070300c0600c0d801030101d05003120248162003583c0280d411001c03002000d90b10341507440390944d0400c04c03117420648490300c00000380415141180613200c4840c08500405c40c0080c5003101c502030000703002035403286d142c1d0040b850300300b80042948460540840b107099070308407924020740540c0319a288000980a04400c00c2c021a01e01070502c60944600c0c603904c4403001c20424911994040c54800714440c042c0c0b1748030108c03000060b44113007080c0f000303612458000344c040c10600c046060307031741c4030303030041c0904d030f48900020030100703c0028010f0704540c8210865550000201022150245800b002030b0003582030000303220820007506003140132280105 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 843018111 1250 843016861 843016879
    0x180706110f010c111506030d0320210a0b010e040b0a09020304060609140903160212160f06020c09060405130c080c090c0711090907081005160206160518041a 69
    0x1071a641e001c890961754150998810b500e23030303410f031030281d40180d140c020702e0344100c1c120f10011001d8844660000c0390050304c01d07031b031010300201c880e101c0d51820f604007040541c1400403146841c0020309021280394502e100f5a22410841d54036240c5089400140090390810365583ca000e060890203040d06103c2c074450603240480d404200c842c00065035000d07948031030241d442c207c0b01d00c5242d480390059407026a40310184020030701101404004008005844984948840d440d00c1d2074203c4203400ba90200c015074005802c445500d030b42e14400320758401c40860300000c40f80c0360007040130380344400200000d041036401580407d8110000410031080d8008540c00d282c2c69940201680541c06145002043c080b50342410b0601c520700131881551003034204085561503952415098a44070610450702c921179079800030f00004400112207040c0c440b0440c0010811410300703600e01403400d40030248000411130081016500d500286028051800d00200b0900034022110304420305410032040c82031107a00c0f10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 843019361 1250 843018111 843018133
    0x20c19060f1d271f0e07051612030e030306060406050f090a08161406180d02062215020319051306050d0e0703020916030b10080f180706110f010c11 65
    0x44a0309130300369030208103042540c509024400d035014040c0c50380040c05000c2c000d181c0c40e050510407010010f0702400724443c0c400041070001e4205c1d90741c0c1052481035001001001081d40383c800885044030100c2c50090303070301c0120841603400c40c0201c3e0707140781d800080c201303000441c0100002c0c4800450004001c0ca05aaaa01c811441e00700005405d015040704c0c00340300c8400100e103030b1002040b506002514a9084a070a94006641d503800413180704400c5e00d8407040c2c5010a00d02d40c40300c0000d031264001e00c403000402c81c40080e54a015058040b0110b030790442000c19141c1c4140b05803078400710250b0820740a252540d00191454200c041440c001c189030003d98800840c00150f0081102d402a100c0101512203110319007880b20000c108406154660104142030346400b00148641203480e80ca40f1041d00f4819121820389401901c4241110304103000300311920b4000c5090000c43c0c407607080008140490301107103814441c541c42d18034502d519001c100c40c5d2044d007298441c410031550718150b8501900e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 843020611 1250 843019361 843019381
    0x1b03121803080409140f090a0b0c1624020906070219030807030206010e061e0609150414010e0307061d0d080a0915030e0304030803090106050907020c19060f1d27 71
    0x119502010341d4041e14800c23020030a44039209400440850b90f60b40703403401358000c404d240703444401c0489110f1002104d594021043c0e00ca450030700c02100c281589081850b20000b9000d0160441c041d200703540d4502c035600c142c02c02c410070000859000000c1c0b625107015041c0691a01e0003481003040d80c103104400500c09162050b203c01742d52000200c40c50720201d092062007000d0b000780c00c1c015040380141030b01080040c841c13401303003004144002c02c600240715090001005010f10414090282d40728220038031499801614800cac86240c0348408541010400700011154100c00b00040c041101c0010580900b42c2e11402c83e20a403040b1030300c008820080044205d04854a036855545280c00500c170a0001942210003190045040350000c2005603d901c0060500799003074030480c016038051440001e283c14242e469107502c40080034001c902c01c0c17034180082d08401d0324000307540401c0100b440c1703800030340d40500440c2038000f0050488604042c0c01d6801b881c2291151555800121030b5000040910b48 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 843021861 1250 843020611 843020641
    0x7170907090b1203071b0f030510060b0309070902030a1b0e0a0e09030f090d020316141f030504210237140312040803041b0312180308040914 62
    0xf800500841c5005001c0c0c03590155110000701c1040820101c0350300013146c3c483c1200c0302019500403c050702c0c1c0900c407810040101c0d0030f16404400082000c0c001c00600c0c1c1400f05000d011540070500142e6a5038600c0c0035400109601c8414400490003d000e400007a648001c0c030740c040d07500656201c46042d8803081d032626644000c48014140d944200500d41d00f948400000c0d002408028212100c0894580d0001e82014211004c440104542c00400c00591310041004125007400b41d8500405c020a04c00e4803c040c01d00d41900d00034180c80b58003003820003c1c81803600c281c081002c01c0c07595515404210080d15a046c1806001d001a0081070300504c85005203410307030b0a51544034800c26034140d6039548580c540f0140600c01007500040c03280c4e140796115411074030321840c826040a0340d42d242038039004c542c0c1000d201c0545200000c0b90800d10000d01d5101403d4122081401d03c0e09000c1d03050000b8445040468000a01c1d0540101d000200720030283c003e03400300c1d24400c0e81c90384c4940d130303806006401070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 843023111 1250 843021861 843021889
    0xf032406031609030c060806030d0908060a0b12060c09210c100203070b010806012103200109080f0a0e0315060d210c0b0c090a0e07170907090b 63
    0x4010400b1501201428041c00c40c1000182020b480c2c3d25503907101c24600c12001d81c04070002c51880000c1141d10304d0148540d209150144c280600d8450800b8005a925840141500c80345581d40c9014030f40b43d941c5040502e80c00b65648219004d601d4814103071b200079005951000c0c06070b503280a2800d201010881540b60b015042c1c0001c0012242c1c0d0802c00040c140640681c00548c0001c1000002280750311140c00c0c060b10042d40180354a5140c010140c000d4003240841c0a544903900d102d5400095111215240c4501032910f107035407290b5225102801844000402000940c000800180400d440c001801000f415900d0b0030030f80e00c0d0000245a1503550515030341d0210030704007000a141d0f1500c04800011140290012840d80061241015800c00c0c42d20002001c62414182c2c0030800c00c20624241e03011040580050a01110101168500c6654010040340350000c0e0005110113103d000c2c00e0709020b10192501d0b103a420401c03031103a16029107020f100681c5040010501481c10040c041035040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 843024361 1250 843023111 843023119
    0x6010311070302070501120b150d0e15040317040b16050910020601091d0d030e100e0f1011091c0f0308090d02061b16290f010f060c0303110f0324 64
    0x90701585d400c01c003941d8043e5120b400701694a400c120bc1c0307500204603c554580b00030a22001d10305090078050100651b00d4001c2c10150000000c00001134201c8040030341090441801c00c0003910b40807000c0c0c81030f009910038540c00048005100001c99400100c96040343c041250410142e1030a20310b100210541410600c5598050170b03009d00104e10130ba12110394a9141001d0740d440c810000341d41c2c1c040d60480403400034264486003403809940c10621020020a00b001c40400180c1d4100790030184501a81d105c40740300c0e528818060040d9455808040c584660004c6c101411038920314001c1e00c8000d0030b030340c003240c0c3c3e22640010040c400d000140440c0600145c403058081c050740302d4540310300c0c1d034051003e0700910104600d4107000506c4d001c00c0078a0b050034403c11129a21001c0d0044c070444030004040d10b0034215000010418211184000e1054030714074500388070b40c40c00071308080c0d0203401c01d88021000b21030001041c1c0604240403010f50300600f01c03008000d20790900e9010074005030003123a913100d1b80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 843025611 1250 843024361 843024379
    0x7020d02010f05070501020307050702040c0305150f04060b030901150b09060d050c2b0e0114131b23010203070320151302010807050403050706030506010311070302070501120b 77
    0x5580107840c000c012010314600540384c01c40681d01c0300c0c2a6081540c40c0d5010601c04195001145005c0c02840b513820400d03e820050b038680820250441c44c280c1705082d00403c40340c1c0d41d003005910740f90440d41c041d01400c800e05a4038107080390f186000300350b8400010703214007040750b011401001c20800c4610200b4001d0029062100b40c002400080501424200c900c4030200680c00000d140801108025940c0c51005483c1e4400820f0704001c1e42e00e001a10009a4903041548009100c020500c03074015000b8180c4500c4c2c100a0b01d41820000781e0724007501d00d0884101c41c009203107540702e49041c0010303d051461444800b201c400583c0e8038081c42c01e004000c40c0c5074602c0d0445c9071028070301c580b1030f102d00c0408991104414801c210b00c41c40d426590700d002590884041000d558010229a030010b4091508a140ca4950b8948a4507214940500c0d01015120404107545a00c0784e002014040615072880790340700c50b6494081e654a02c284159401700d2807411303c0050840962280c1c040c56a0060300b0400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 843026861 1250 843025611 843025613
    0x6010519180f0f0504111c020306040b070c050604110a090605030c190b1206030c03060403080a050405162304020c100b0a090501030f210c02010e03100c030606120207020d 75
    0x80540b5006040c1e6155a54989201451201c107002d10b0b4000c50145013440c401c4a000b40a0000d21313924916000c0701014410300c0040140c500042e550341c0580c000c00c0700749a076120040200d482c200340c0000036100d4400d0030240000d100c0c0c20791203d542850f0031900305040c00e60304d183c1001510164440c031030f455000b0441d503031043e003080d032002e03001100c61641450203030751602c0da444c5103a0081c029050102d11144108090b07800c007081840d0303400320110b005050918160740c00401c0e203640201444c42d13241d22880820304010007000300d0b220684d08401071400851b1030f08007510301d4200c00b101c402c3d07028141d150142030380d040c940300700c540c44010070010f41490717007515031007402502070211800e8202e82c4030400080c0046451203400e028522500b0800040c4401e0706240d251102e48020a8824036100710310351a10306d030854511206c003982800d080300c20b090307004002410400e0904040c5800c5003428100741d49154964802001c0c0d40c050340b1846182000780320309508901827040300a40000b8502d040f10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 843028111 1250 843026861 843026909
    0xc17040209090a060f02090102010b0405011514070c0902070506060a03120c030e03060411130623031f0e191a090304091506080105271902070506010519 67
    0x250703200c02c0c1da00403941280b400c2e40d1482c04903042c601040610341d41c08114104c2540e428094885040c004560511203941031401035035100c1000811041444a500c101074281c00880b0140c401c8541c10a00348244255102c007820301a500101044035580210030000d5000c0ca060803d0780c003681d802c410010158590424140c40261385098140d0602440c10f50405e01d039542005514843c6206941907044518400140404241c01034001001981400c00600000c2801205210300c49410700201945c0710f007080c0800d04044160300110340b103801d03216400350303d101990403039412004420100c07030440507508910404005004001014445418112030440080c2e004580c1c0081c10070301501d140a5540ba480c90480f005885242001214640202300340c640041080740100816980040e459940d9041ca48400368840810040700c0c41c01404680281156030705a045c50302c0b900003c6666094509002303035101d07000d01c00d00307116000c40601e441880b00444400c0c02107802d41c00d040910301d45a42105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 843029361 1250 843028111 843028129
    0x709061805041b020d05040806060d02060c0d03050613061a0c0f0307050a030e060c030d0f0605060d20070f1709090a0f06050a0f0605030a15060f02010c170402 70
    0x8500a030080c004082025a0303a88290841c0314100302c641001040302140103400c1c8080100302c0c00c2440400e100401044101048442d408007048a990701040458400a105030259058400c124400c6070251401075030540d0105025100c03c46509518aa140c010201a44c0a50003a40441768482c2450501c0010100160012090200c01d56503110b80310b04d2920b185401482081c0d0341d640c8015421014183c00007041c0c1500c43c000d03101e861500150400841e80c0348184144160f51aa0307030001226034803800c0c0c0c00760b00a0718004000750f80d504a1842810003401d44208142e0350301410050200c0303840c000c401120b00942c1e110078545111070b0300381c8a144402c00841d12481985200304001d40d5140d80e0810141e1040d160740500083d0252414041c0003201c0850300114004c0f00c0c011424000035909550107401c5400e10320b0026907958500002d01c010306900e2005010307a4100c1000801e0a43d00b14041e148001c20703a900820841c10944000c891030310f901c400000044000c01c0208025040003516 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 843030611 1250 843029361 843029387
    0x50a03112b23040203010e0a0b0a1a0a0302060c010b0303040602010e060f01030308180c06190f0c020105180609060f210105061b154803060d050604240203070906 71
    0x98400804c03000d1230308000303040e0421540115100100024a031082c40340120003400c24101c2e03a0408041c101182e8440b01da030001903c00c0d0320204090310440003d410810b040440501581d80300e541d101400b0b4083c103101807080d00305000d01800186812400c220081c122074040e82c90070fa0b1601ca2501d4040350340c04206020485000c0d041c44000c00340c80e080c0080601202d015031120040c030880354018031901095a4038020000d4544410000d070780e1090507030b03100076100305010007009900800600380707206a05c4150b4005070003140a0148055850140107840369860000a2082c00c0e80c1c20880c840009015487e03014100340810003c04072201000e805c0510801d044480c0c0040f08600ca10f00341c042100c0407110600c0800040c2140600e0001030b104c0502945146d0107d40300c0800c2142c1c0d14100620a0000044d020002410b50340d9080d540c01d00e029088016a405428030b8184002c1401485c2c5a0010101c10368540701c3c0c40012a200b1284a500740313513a060002401c0075003c8444c1e821100c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 843031861 1250 843030611 843030613
    0x120d0b2d123d11071a1501050d1d01090b1b041505090d050a02100314040f0f020d0303020414011d042c0705030f01020a0807050a03112b23040203 64
    0x80a01002d01c1c40790032507118030143d03800c4d11860f141c5814030700c035040c2c1500d101c40000703588188050011516500e40c5281c0c4242030090b191850100028014030440020001424802014650280040d440f10807a24040c0610a050703a0312081c41c02d0f010f1402d4000012160320820041146a49026208030004101c0c03804a1420034140c0014031030400300001910301b0b030016050b1f14110720340310000382410b0425080070b000c4031900c14185440400020030280100d0500c0710020300304030607001c4081503650b0041160f94100300b2810002c000350401c1c042d490356100b841000324007940c0618002c1042845401c0f3341410503e4880500025000c3c49010a01c07103440394010a051000000b80d12030030100c44401400d4075450602054544410100100420307481080f1845040e640070000030f512820608007299101c00c601c404500404000543c0001070b0804034801e203841d4850052a403240f081d690301404003a48921003001140c000400340d905142c0140d80344010303405100e02641d03100707000030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 843033111 1250 843031861 843031963
    0x403211e0c15060b0d0608011503020d061d0f060708010b0a0e0a0b0a050c0c0a030c0501080405030904090f030f08010e0126071202010809120d0b2d12 66
    0x403007060b00b0b4881c0c1d50041c541c0d041010942c80c0d00074201d442120001d28181000f480301c15001c10701c3c440e100109000103400340c64040044414080a034002c05003c18114001101068400c02c1503612210400380c0000d1600854021179266440340c0c1396a03042c3d5450215041c81d000701d5003002ea800314280c0b840740c0d0300580818000103403103d40101408800710142c03100c95850b15001c4d42241490321a42900b88520300354a81440415201d00014045d50400c2c02c15150a84440c103140b851070260408881d07102d8280388408081000202001005034440d868903e0696072000e410b581703580d02400394000d415007000040090300c010f100084000c01504030300713440150904507083d08000c1aa00310020918541c081c0c0701c1107590021240d580811000090304d294404da8824403032504c240e0b410304103195280d0420920039030300c140164003000d04140e5055142101c0110030305080030302e06440ea1084440303586201c0c000740007144900c00007454070704482c006a0783c460114208450b0200d4464031540744 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 843034361 1250 843033111 843033143
    0x70804021014250f0326150103110d15050f0f01020d0e01050c0615190b07032d02010e060601021612030915050d110705031606020d020403211e0c 64
    0x101142c4c000e0b54041e50300c030440d0840020000c6400c41c80740d1011801003018030200702c2422103081c00701915100c2441d000c210f80502c10742c024007030700642104a62403440c15440e625800e010304c2540c02210800e4070b5001008064404204400c580c400328103000d03030020b4500c0c41c01240314000b14110110141041030810602251491030004100c0d08100d04801310240303040349103400758030502e5011004444422444c20010b0500c4d441c010321400405200580d00c0001c8880d080b042e030265960f1844c140f5410000001400a000c0c0203221b50822550180307102080140d4070103d066100c0c0942c1c0c10340c01045038a4203064a001c0d540600e800e601f001324181011818901c181c14461840d40310f031fa10700d501c4800d0103600c10704070f64106c00c60703024402041020308009903011043c1c809211410b20f0440354002c4500b4503a000e40b20b90380ea0108110301c0010080304110700322000910848519442d04120410384100b61120103000204000c1106603100c0218604d00c0703519a01011445202040c80c0c070948 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 843035611 1250 843034361 843034373
    0x7031107060501030c0b0705030f090109090e0a030305061207030b0a0e0312011a0a0e010e010306051306030c15021213030506070509090708011404091a07080402101425 74
    0x94801c407011511180100709200504441d00064070000610b5072910742c0380d589451792440f071428404509180232a510000307a0041172428014200c4103401e020501140c450161180321008086021a02d40400300e1014104046680c000c001004014258541591205002401e00030450740e1496110500140b20030028009000030300c040e0440007113554146040241441d4008c2007090340f8800c103000c02d135106541b14400100240007030801710107441c101070048019200f82c0e005583c0110307010241c10510a00d540c00003007180d000c0e150050545403690000540c0748810f805c410f00590240318030118400041004007140d000c0f0b20441010150783e0f07074640e03050036411140800881d802048858041c2400150703694003000618020b070041d070400d0740000d120340b00000854002c59662442c207080096100c05801808007030b0058240f20315140710010300200084070201d00803403030100032190280c001c0c0740340e100c0d51035480c0d1414100110340b50301119062105034113188030700b45401c610002c580 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 843036861 1250 843035611 843035617
    0x110403050a290a0513051b010f03150311180106120c050702030607110f030310031145090109050105011409040b0702161e0506120f070311 61
    0x12148028040002603414203005015550340010702c0070740701c040c40000e40241c203040746521100d076640000c1e00f511490030807603c01c0b00c41c4000610512507411001c440440d80f05e950400e80c44242d881401c00c010030300c011025036480b1000c0303020030304480c0c13414000142c041640480000d800f600c0003c0380085d03d242d54a92a10030b03481000411540e0000a200fa001405041190207590400501d0011740d0b50100381e0b140d00081000e000c0126200014420326014806010100d80c100700303c80d22424001c540214007481c0e440b00b262208400500241d1070b04085000701d1803004004d0000107950882e141150720b00905107c00e003002c107003450491622540000101c2e0040300710000024018065184c101c1c21210181c10952505850102c030811950b1b400020681c401d0b8042d00316200c80c0c41c0c08406034648441c805012451145030a000b1441c6116040c40e003040d40d0001c0c02d41403403180c3e00d500340240c0384a40d100783d441009810000640d201c0460513410341003120b6103000152503c0e0801c1c1041260 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 843038111 1250 843036861 843036863
    0x70e09120409090b0c09240d0c0206190507050a030c0e130207020901050f03120f070c1e0f05011d0a032003010608010605061909050a06032a0509060d110403 69
    0x2c0d80c0c3d03100610911141120070765100e91281d00071894045103000051822a040300941d44104600d1400d10124450300281c505071645a0028032085048600c042d4450350121244400d10510200510122000e402014040c0ca40d41d2a200e140c401281011005000500044420b00401c140c0d42003e94035001422030400012802c0141c50382c00301d10400c0a0300d441a841144074000d1000c1d050b51f1550085158226000180100c55a4602d03692404134075014428000d403a01c2810400001c1d00c0381e401480740c0c90320548061a201c0301d9112080d20170300000c01c3c05400e0002e00d00c041d80000f04820b80f401c14498030342c009c0c81c99202c1e903904d0f035505203240c032821210021800c580040c404141001d0040f04044d20344400240240c03414800800e046008c1d18220f03104c017121031009840494060615a000b404003d050f80480540711403014010b400104250360404501e100035200f0626120540c20041800d82d8891346841c03e501c0070081e86400140c2c14840712030351600256007022a4000800c011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 843039361 1250 843038111 843038129
    0x40503060f0f0a09050330010b030103030f0c050a02130f15081b092a0c06071b0b0a240f0302010305071403010506070f0510052205070e091204 63
    0x92030040004200148090324221030300c0d05000042c00001c5c0d0110503207808031419000c2042c008081750300d8070000b50b010f0850010701c402040002c191600503d0043d416a402a15404044600c0c4d1500f20360142854034003801c59007088200d00014a44201889a420750034400429807040b200d281030220381405654020b000e50783c00081000303050501148802841c1e003537518403d807900c4030200300c000900400039100c000d0501022208070030700b80d4451302301c0c080c96030b10291038003c100801179480c60184d40c00d0001c10040000512480c1c070f20050003085a0b48200d01e0641501c0780b0001c1c06c040d100e403a041132112002e14002e418460b1820800740010061007014846040c61400098100c0c0c1000d006d60003001aa843c01d155540316400480e41190030540d0085d41d50750040c106a0300c03910b07d83c4402403190250340710580907140590407060041e2156842007003002110b06049100d482c000400800c0d9400c6560200400012038110310b5000080c40140da0545000c01041411036209400038105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 843040611 1250 843039361 843039391
    0x60203091605010f09090504140a05071e05010e0d03110a0b0105101704081612110601091b110118050706021204030c03020907090506030c18030607091a04050306 71
    0x2400030409001030041c0000c4c20041900380099400901c0031801d40130329040e1a880c0c1000c80d081048400d001e4020221040640e5103119881c6401c9441c2e6000b0f2280c007651401a50b0404034480b01c10b11188111a0140c564907110030404003448448018404183e09000c0c107a092101010740500c0700d00d4910b44614480170443d8140410043c8001c0f99103200d0040001c29100141e0305010305a1283e0895006250305441d141c0c02400a034442c140c01d000140122160107240e6045500140f24082110742082520496a22404650201c500604c0c080180d12000c0b0580341c0c00500820284140140000010544000d21121742d020040d10740d400325410341c01400c2c01c000155051181d403524082d1562079519081c0303940c43d0000035094501002e4400c1c5182c00208003444d016010140081c0030241c0869100c1c605035a183c00a500481d81400344040510001040362078042103c900c00d03025900d420b108a41410000350b4103c40141042455880070080400c896508000c294441c800d0100341da41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 843041861 1250 843040611 843040633
    0x40f0615080f010501030b060607050709060b0703020f1605040b19080d08070c020d03031d070902090406120c09051e161403060918010b06280912081606020309 70
    0x49030440500b401c03500c9074540401480001c0721140d186400403000c85039251182028204141028010360190401d10f240c828005941356058000c1e0440c54003d0b001e5032403641c0035888058407003074021488040d0032440b00c400c3c0803d10700b80e4030480c510388024042400700045c100c000500c1129540114801e58000c0b0f0109080395400360703c1c90707800100c42c6048500114142e02094130950518030040a060b103450700314070301958a00c0b541000301468003c503550b450341c9451440081d400042d906000710301300007010031103440c407075640007a160340038481100051501030b071305004180203452100c000600d50039041a40414910082c0502400c0c5490b40d00d0400004001c0e149419026886594620500802015075200840d0907880108840032154105501d200d0741d0040a00c2d065a5501103004103042030005150b90000183d01c4c0c200300e030003208580f4070310f068a02148a2049111109209116000269644000d40440480c40c20291000a442e40d0342d441039070812207081d600f5074000310000c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 843043111 1250 843041861 843041863
    0x60213141012020d090b0414010623120c060f190309030c060902150a0203030a05010f051302090118031103100c0f03050606090406030311060105030d050d05040f061508 74
    0x30880001c0700c003118072420245016089a88035044080d803141d011490910600b9141c014000751644074040c180075150070718020043d2014051080031940c80c00c0000700390074607000f038644e8000310001091912003501c1003c0100800701c000c4500003030701400e0214501e80e21400e02620120b00384200241c1c87c1d81088001c051802210822241011304029802c00825040455040703e1500f0080100792070f14240082180c10044c2d00a0300c035560750004203890546c1e80071014500807060001c0500c20740e641d442440031959424010103900c1484590121103c43c0d4645c010510580103040c482594080030300c045404841542c010355014100c44054401c40c5001e22001b00c00d100b51700c1041185030100340004000c8004481440281591031010035995a039090548100910040051200c01d8692034014002d10b1403035000d441e181300d03076000840e06160201e02c0310100505591114100303e23141e11040050403000d0000d94074910b04110a0011071000d000b42d01d110f441c000b0611807503038a4100c0c02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 843044361 1250 843043111 843043139
    0x20f0d170a0e010f090302040f0e060a1d1204270515030f2d03040e0408040510080103051c050702031023011508191515020102031006050a020109060213 67
    0x904000ca010301012402c4c0c5c201d100c003401d417074055800150005019030250000d20007090661b01d50300c02c14007000041c0350301d03800000703005002c0f24445500c840f0708400b040c0c1c3c070b00e030400312025010002e10040c09030703c4070750540410380340c04c049441e000304444d561202c080b00c40135611042191401c4031403c03000e00f420011306c003050540c20014052015042c418040c00024803104d0315010003000c0c1e07100301161082055802030a035482e01e084140c101850710484541c03040c4941801044030b140d07402a235900500c1c1181c100d13500400504883d0920310840d0f4229040d040642061200c1031020784c002d40c4040006403005601070200003240d260000b003440e480111440741110007440d440060204500b802c1444190354030718140f0b04015201c00d40d513510b440e14056603110029107481045084034118402c0141240d00520b00340d050103140086c02c81c244c0c84203c0d403520b081c000c24501040201d110b91300074083d800c607078400060844003556070203007039038080c0c44071800524001400380129030100d401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 843045611 1250 843044361 843044387
    0xb0a0504110d140a140702060c2b0e1903020604030503040204060e04050d020c0d0512250f0308061c030e03120403051605180a051b07061b0e0d020f0d170a 68
    0x17026a0380ca801072000b076980c5001080c0c071460300000f1510340903401c0c0b1039249a000000040c41d01c2d074140f0b200703200800105040c11030726000d88540021507040000ca01032511007185c15a0203083c06a03a00d17141600d5a40c0040c2c003c0380c1180d07071060002607031082c1c80540d50095225001500c0c26508654000b46004011f00c2254030400f03980c559800050000103000481042d00382c1c0168441400400b0a0240c03011000a0241118412165810410010850103242e403081d1100491900e0321030501a0455418030406e0886d0149040c10010900942205c0e041c07140040c1201d00e0a040d62803140003a400c0780d88100e4155119203900c810500d0001c1e50107024000507910015002400d000c241480300015020841d00d0340c0e6036001c82c0085081c0d03d80100a0900600003a0341e61800d482c2088c001c00c0300100c6040f00d442d001040a410a1080706450480c490003410f10710410f11503001c00c411401c94600b5aa4841700050600340000c8a031401113056100810b000da856000400b0041d0071816040c3c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 843046861 1250 843045611 843045641
    0xc0f07060201060b1c0608030a0c1b0506030c161407080105060f01091701060f060504051009050a1511060f0106110a0b3903060a08010b0a0504110d140a 67
    0x3000380700705a5a80c1c00d407501d07948580c03410b2901c6614131450b000181351b140c00544140c04001040c001c0150000aa44a41032085007451141e0540300d2035071100040030f0180d95445481003001c0b4000c24554806007110401301803410030306124640d0f610352400050420410f15410011080000032020b00c1a6139004005654620400c914031000810031412801a100c000321100300160300e41109601c01d602521400d0f1032545095200e060150082e0054410140300c1d60141141900551060f00c0c3c8408507500a01640500e9041051424244401900c0c540800c400c00c5e6034052002c10821089000d80700503070f103054a550405400500c00225a0f48009195000c0058000040c071188202948450348010202582070001400f500c14116101540c0030b2440f040b1507943c06500039002940070342030444040206591310717442d4a0a8070030508086a000e81100f10800c0242803c0d0080005020680d1100d0b11340100c1001340030813030b84407070f0001c9103600803a41040300040782440380250603141c0714 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 843048111 1250 843046861 843046871
    0x30190e07030809010c0c08061e0105040915110f0d0f06081c2001290321090d08041514090d24020a030f06060c0515090309060c0f07060201 61
    0xb4440c800644140080607042000410380c00d0709104003480300d0809880610107982c1c0074102500001d144c40602d00490304031000704000061107140a1280701d01441c0c0c0486200c0c0880484000c4034010413a0f170b103400203035103410860101c82c15905001070403111f24141e80042c0c1c0e08207001000c0100c031104d4005920ba90300001c1521840c0c41a261602c076a00c2e21481c080035441074a4071000e10090612540c14200d60800b031071003107441c2c06964140d2400c0300c0461084c0d1540e03507000c01c16a030340341181ca045030903c60356046213030072104840003072000d0036010f0840b00c04103103140c0c2c03000c0c4e00e90701544c0030741d003101ca81c4800030201e00d50001c45180842c400703040050078003c1c104001001480040c1004004443e80200d807901da00c0900c600e0000650b08610031900c40741c0105016001d0180a088000000c1c540040812a0f602580341d00c4000d80c0c129008080781010b00128004a120240502d56588000e00c60b0044070f668000c000e10f100100040500882c0c3c0c8410103031403818516400035402d40e4144 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 843049361 1250 843048111 843048113
    0xc10050f01090e030f0f0315031204061d0a06170703051e1519031e0803010b030a020403060c0903110f0328050f03040f0f0b30190e0703 60
    0x1000c280c1581e4155030001400703400b000100b8610310440c0b025060084000c103914081c03809a070041c5101c1c1c103200b080c8200010220003010b441d5484000200c203801001c0c042882184e02c01c01503038044007080301080040c0e40c400d20000700c20803026402013000508040d200c3c0f510b2800010030720b070046801e00f414041803d007d0680b0502c41c0940010119440c0d0300790006040302d2054071074031800d9801074400550f20b00f18680c4450607440900082da0321100120105400500207000c0c4103030650401e518038210390070300104a90780d910107840070040c25000d02022001c1101e5210b0316080300d02580703400107101d1451400c001200810743c3c10301c1c0f003240c050700c966000340c4020a10b13145d4441c1c0c14420004140403071400705c00e580001d000c040c220b40b14000010388003034400401401520310480d040c03442680d80f082c404961000e1400780600040f002c3c440c40000281c188100351214294031350b42c0340d41040315481710482202c104d030800100b81440d20818030400c0306120780c10000586a01816609040d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 843050611 1250 843049361 843049381
    0x9060f02030702011b2001020106120503070605091c0e040f0221070302070506040b0703050c03100303051b1005011707080c0d021909020a0807080906070c21050c1005 73
    0x50900b0107414820b03400e03183c20b241d05aa040304080d1503841454410b891a1115022007846015030703c1c0303800340d0b00e443c0d4046809084103c0103003030070703910500031858565aa0341740005801d0251400d0b0b21b03886a0032040101601408850110251f15035500c4508281d5000304030036a00314030050382142d4410021085005000e040000c02d0401450302031b105510340b507900b10000d00c200e1201a115000b241d05210403c102c04100714082c080e10303941482140c9840403070003900c1c8429208162107e0b0340385d00420002c3c0c011000f0305546010f6580d0024940d03e4950b0860818a0300c45240130060303641c1c0c006018a41446003942544080b401c0104029810012100c0d42c800e81200f100b88031b030b0302c541d0031402199280c004140b0b00d8074003203508030001aa241280e1020350081041000030503041000140e400b88100c80c0c0c6481a15420014410390700e0f80c860944045208040a81c2c2362002030080510741400d0928030035946046a80d07055a811100000a0400320510340c0c00e01145d042405128213601 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 843051861 1250 843050611 843050617
    0x60f01030b07140409020705030d060e011d070315031a0901020a090b0f0904090f110411030f1f0f03050f030a050715020c1b0f03070513091406090a0309060f0203 71
    0x140d40d04020303c0d0902e66210128280c0207607405450b10500000d030030010041c0200292800240c400c03414040c1c1e0fa1a41c00d158003480d42402140e0a074004504440d01c0821641c40040d04640d850130001900b0040405800b005042a0015038030032013010104604c031049030041d2544020450300860600d000c080c0001c2c402e40141c403078141d00710004900c40222461880454200171001481006428454a08640c4501469405903141b103c08071505015092a0144e8440b65010281092555546025502810344042c1c03040d054000136007180300c1d5400d40841c6141c05040181c0e00c54081c14550710f0902d1814400340318022036034006000140e0030030340050a031151070f03902c02c00e0032220f200380c01e818400a01030300b80e90342c0031840784d000d00400c070382e0204055071405042503c060743d100300c021007450342e110910f209454014014415004901d00558031080540b80300b05060781c02c0c90381001e4214505a01643d603560076421080e40641019000400c610007000c980c100383c0007004039000f0103500c1380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 843053111 1250 843051861 843051871
    0x20c030c09071d12010b13020a091a091818010204080a021c15020a1d010903030e040b040908030609060307030f030302030c040e090c03210708070203120d0e060f01030b 74
    0x2d0380c1c56640010450300f81400c02c842d90142c5140a404400700c0c24901818030a00700c580252008110700c007014145000700c0c1e0b0004195140c070b2603217500e8042d2441d9945544208082c000a0502004030707603540b1071450303505d5100d41c0c0c4d2a40390642040c09080e021b07030300f000307040d11420303881004100185040458090704058046500c007601e070b400304006024400040c00c0081c0569210390044911121581c0070705140101e95840104807907610030b1408840080030241743c0442c4150404200091140d0189a90b0000140c03011600031103d03004101a2550820126a2800c011003040031508002c4111640150124028150b0070328584511700c1345081450041c04058001002030401044030381258020700c0c035000062250718040301415100d18003100f166229024981a1050004410b509150006003020402c1e01c0c00506969054141c1d0152400b26018001c6104882a1180f004080d24615402d42e1003c2012503503400c2081c108540180f14000d8480120014000b08440036012382e445 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 843054361 1250 843053111 843053117
    0x12050c1c051902060f1b0705060c0c042a08010513140f130c0b0a021510060302070227010807050103050c030c160c06050c010f0203010b070209070905040f050403020c030c0907 77
    0x4416030020035407910985017500d10100e8001031214107032a2411001003003103116401d4131b641e41d8a49081102511401c24071303149542c04208003151a141540c40300c450f200c0c10320490000400410b00301214240984005004a104000100000c1c00c280056200c21482e481c2e080004c006a040010201000501808200c07008100010f484081d412060340c030058005003402542a640d072083c1206030b00162816005000d5040034201d5013a20885040c09910103041c145031240c00c00b80100c0c0250401d410580e84107061302c1065002800c4000c04111800d40003402042641c1424110345c6003480c05e078400350403d8541401c004007003020805680d0009070810250b036840f5040c4088600d50405c860000d050030321008000143e2a42090040c299400c001d0b009000000c0002032100490109200b945c6001000b00000801407620300300b05075000c1342d5401c0c0024a19262004501150001d60390a2100741c2e486043c0014150100201ca02000048001385200482318000c511030f402e0181c200001c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 843055611 1250 843054361 843054403
    0x603050a03050706060b03041103010c0f1d040f050a20070b01031e0b010b191706040507090b0406020a0c05041505060a09030203120a0e01050307022512050c1c05 71
    0x10000ca5420070001131400c0012141c903414103040841c94040c4240c0c0051096290130f612010037401000b1802d0091020b4a03042420307a850381c19540341c4500f0300302856019031781d482c6041c46c051051040500031020103000165402c000c220034401004c1014120088c50000d004200000c0e810b08621419258407100c05400210404140b0a107503040301001000020f542c400402c01d000500040c2094041d4000d40e1002210791800a50b410280c1d1101b60241800300000140303682401c0d000150000700364604000142d948070740010007a00701d508801c006801480e0240c0a20810f0f074005006020102c9003000701d0704210301550b500c8c800e030380305090044a0108a01c038006016074200f200540e00035003502c00940e906001961940d12281c018004074100e5403d1103015403040044d640715120030780051100b10310b452128000014900423007002c4905c242004500c20181d030403208070080c8a0801003c1e40e4014100f040f1501c0302199803410b000c010842042c0200320700240181c004000c210000074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 843056861 1250 843055611 843055613
    0x506101401030b13051f21020d1b03080904060e060d060b01020f03121e07050318070510030c0e030c030706050706020904110301060806010e010c1b0e0a020a0905040603050a030507 79
    0xd02da0030008441100f174030b824200318104074119501c89040d40d0394106514529100c004031035100d0703084182500d00354030915880c80142050031034042031602503030408034084e02d1140101c1e0346220070f0b0000c5035218008211402e0303c1c10300c0d0092101a0451005602031880d2000c01b15030292001c0030b01404164440e400010709034001e10a11190241c10301c103586d07a480c1d1801d00301c4c201120a4419803060008500301800000d181d012250288005039149455601e6082d045c0584504400d40e250480c00740607000102a035502c01302a0300495107460104028540714006048051601030031402900700d8a100003003654082000c405440e0305040c01e0313840c1d0303020707051800080c051035031078581240c6010010b0000d1740e180c10185048075244d40d03900720540c0d14200110703162681c1143d810701042e043d151100c002031141c50b050074200e0111014054590342e558512200301800e903905035a056002a103248600d502c140d5050103840160390a01a4920f55980d807940e41c03900c01d00103010003034082000740c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 843058111 1250 843056861 843056869
    0x31809010e041b0e010b091503070c0f111f020c0307060f030c030f0f060f1a0906030408070605100504110924280e040b0f09060303160f0506101401030b 67
    0x803015045882c1d0381d400175a1075100c0700c1144e902c05100644690941c6a600249002c0b49040703910600f010354038520580000e940e01c103621a8605000c944a07034403048950015107401002c1142d03281c0850314a40d80481d951006420300060110160194105100c240540b580020000552640f2850006018030091200b103005040c0308920680e001c1c10303d000303601e4031085030700b101c0181d4450b2040810019a240003950f04810800d844011804c01800501c0705880c02c030700907651090041c0b841603e0201281d5402c0c0413038208841c081001030400800b03204904082c860403007034807040342d5602c1c601044600042c8600d00e00b80c01e00c1c0c0c2454000c000303000100040100381c4211a1640400300f142c0c10b04100d03041ca042c0300c10900807001a0502c0d14415680c81c06014580b070544028001107000c11041041c40703107a60b03000302030300c2d010301c820045440101002207086401c80c0c01003440c1c85a0040314604241400005404444000c080b04014450403010203250304400f107003420002191030031740e0045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 843059361 1250 843058111 843058163
    0x60405013606241707020d1b060507120b0a060e04090501090b0a02040821070b060411180307090c09121a01080309130c02071a07050708031809010e04 66
    0x41211a0020a200110000d6441108040c521030321355681c001035581a180c0292000c94000e401039200082c03c5041ca4010524541ca1964140d02040c0100140c0c41d1030003070342c0083e84d90200082c030000c6d0000c64050148540c00f88148222070000145142800080c0038400c0f840340d0300d04c40e907640d0004000b007003000d40c001c18805034840700304240c0380b0380040048020340240c45800f2a501903210302e0700a8090301441003402c5d0000701c02d0f1505141072500d802e070000b00001c0480c0e030815070310395550a0907208000508040800885174802c085440000c0c982004101c0c0d114042080c20511201c0a154012600101b80ca0b24044090b9003000681807218008448a20b40401c0f8050352b4008234103c600800200a0024103840d51103912103280100d00450701414012030042e044a90240801c0080001c00008480b61640c02030810b0b403541ca0303990030b000141e80224000c0d0f200084091090707640c024005410107048039400203542c5003104d40c0d08140390080000703181070700c1c0e04100c0100724016510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 843060611 1250 843059361 843059369
    0x1d0607020f0f15060604091e06060801060f360f0b070c1203051905071b05090c0d0207080408010203061014030a0e16060f120608030a0503062106060405013606 70
    0x109004060035032840d0144080301612989230710341080c0c804680d0318040c6103054121001c9503200d841000090304112000c006100c0d901c01a80c2d02d800030349603031546d014007403403154100c50180107072540340540300e800c6054544d000c0c184d000001d1028a01150188a01004440b429600c2642c0d400140c0f03000c584c14130620042081020100261081c8241c0c800d010300400c0c0e22404a10050041e802d0080d0300c8185103120311940100242c0c0041c1402e20208041c140f2b0580c41a005410521960380c0e42c1129001900940c906a502008010b088d02d0f18040b00c0002010350700708a2a0010b608001c074032640300092485442503298a801c080d4042c003004201e1030100460000c0c032803c1e86601004100c064810754071400100c6100d45d11003040607500c206003c452060008514042c0141c00968203500014041988030b288030380040e07860308042ca1540080c540c550003405240c03410204100440304103802184d0780f0410712200c203407a09000c5090507554034110813000552080e40c0004005402d890700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 843061861 1250 843060611 843060629
    0xf0601140a17120d0b09040501150b07050319050708030907030c0801021215010c0f0c05010f1e080402130e0c03060c090a0311041d0607020f0f15060604 67
    0x303208000c60011400050111a5880d40d80c0d52989101502282c2e45051010703a04603c011850210941009140040d0285004a41039140e4400100ea001e0304580942d02a5120102c2c42410140000140040d00c40f8410003804c2c90301e2904c400d50781e402044900e00720041145a083d850078012010f903403607542d012a81550301c0c584a14020b46a400740e210031125800402c0c00032a8483c010300070741301d40c11000c9000c0000b55580c400072446510304046e41a040c402c04800c04004600c0010000c0c00e540d0043e160700b8800e42c6080001031400808d10040700c200501e031f14010340b04100301191010030010324a81b61045490340d00004188200523141d90080741c0c5041c4c584683c0c508041116820504110195002551420120342182c0700384c1103059445400c4d4030f814000500f11081002c40c0000c064000144884500d2036035610008182e041445075200070f080040c1c00da030421409051586220150402a4401401690704c082c1100e19030301600704c48001800a0f29042e05440081100709 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 843063111 1250 843061861 843061873
    0x140d0f060603021209030412060b0d06020c0607021c0c080c07051306050411130e09010e030a08090d03140112050109080d0b150306130209190e1f0807090e0f 69
    0x15034081c0081d0b004e0400480b44860f2807000815540e40031056408a81d2000b4078400001521355a6400078041c0c0700510303904c80c816031074130800320708148013400040c80f0300302c01041c15050040010745002200d40d130300440d03030600c02030b000380c0e465003c04030406403584540e881c0c3d10340054a104600740b101030340081d0b0304010801040f107042e900b650002c1c0c003203c00079541088170030540110b017969407003503c170303c088505c030400b104008035540c82038680d500c60a0b0000014400c0d5607200070b02d042d94420601e200004042c4400e0188041003406251400300050408101d104100e403028942880148104140720501001402c1804029041030011a80c083e10203552a0b0846029600074070242ea0240d00802c11018807114100c80d0b0700407213001d003d008004d07000c12070300000341001950001c0d04282d00015030b0745105200c40d4410506001400d9803c007854410b180c412111107984020000c0c220910720030540070010543d0200311a0f081c1c404200703000c80c4030300300c404400380f905a480445004600c240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 843064361 1250 843063111 843063119
    0x81509091006080105061804050a0b0c030f010e04120f0905060c031803150a0c121407031b09032a0e06041103090c0405190f09050f0a03140d0f06 64
    0x1091040300c42141d21001c000641e1141411422100112441a04001100042d80030050045d03041d41c0e015201d502240d860340600c0e900d04207034034401d4802c2c2101e00b9000c4107002000b040340280c82c0c09082008011251440d05454500c414401da81d001003d0044030b0304800e89551007440d0480c050200500000c0d641c1c404d0880fa542d40364492081980041421000e52125140200d03240e20160b078103062100d503946404441600802c0721023118424494601907e90703000b40c00d400343e20941c150300b1000d000c00e4078042001034103449040050500640b082d43e09107640c4c64010040360217481d0042c41d060a20600654003001007880f01007001d42c0e00312a200c0002d05410881115442400103071400d20200c44004c6000384a400252001d01858010400d103600c6414281e014036480680c6001400841541d61402400c5131035440780c00032a9621024280103000703040140750101d810b080000c00d906107150304c1c010318442d030502112501c0000020f50803030306031494002c225811401d5608004d000e540d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 843065611 1250 843064361 843064363
    0x109080c0106120305030a15030f080d0c050301150e040e01090b100801020717070c05120d03050f0f061201140c0702010206071706010c020307080106030602071a060105070308150909 80
    0x8003061441582454804580380c10045419943c85505898007800c61715540c5440c40540420140303104c0b0200300c40d0700007000c101c20f48070b0f491410740a0032210b90b17108010f988600549040c4800d08041c03000400040045040d2411a841100024680076028002e0034000902034400600c034040b640d820880c14400380515102c81302c4c0031326404405c81c00516075070b11000d400d078020801c028100004505014030140c40780c4000b0207445200d4018801107948410001322280071244207110709074001c031100646c09030184100c50f004646403001800914119442499010000f002640549403d8012110b4444c0941241e82a102404450340c034502d00030711406d0850700305880a900500c034400c00704000c24041c1040c59a2001c0b0000e5400c250783c0e4013001986d14807011035089070540705440c0e0004180d242880f401019502c100d1000da070b1000c032410169401c550001007942070100d218207112a80c0e030080220303010241d02d42042030a0f03036107003d0b411031040f03100c1d00e03441d412040c04400c000041074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 843066861 1250 843065611 843065617
    0x180b0d0905102c0c010806040b03150f010501090501031118010909110304030f0807080f06210105090c0a06080402010309061418010e0d080f09072408061c060903030608010908 77
    0x1080510b035079944407644090b13070392860680c0f100350100d030146021662a043c1908075007a00c0d40048c00315002c14402d00f80901b0050340442d10b22075003040c02c200501403580c2c030030300d4074004000910341481001303011440d0101c10303c901541c0701190b1881034001c403441d0340218540d00003030440351410170107080005680c03100e42c0c0c030844085000800308800030404502580c40e0b1801208140d03607014041d0f590200b00c15000c2000340078030740d11525684036109a02080a540840d0500141c004034650604114051810880c8031901c1c3c4100e080c0003040c0b100581c803c0455500c681c0900e80454950706904003640200f4100044004248082c2c00304000031144502d02c8050924140003041000320601d07500f900c8900214045000a200c0d00220721126000901690031100c804195079105981c0e501c1d1110f00c0c140c1038584600d0803403401e00c01400035082800541e1045c02580c681d81c00c40c400c00542003410302c03216001440d095803008080309151280d4422006407081c50001c02c4818264202041c0b250 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 843068111 1250 843066861 843066911
    0x50d030302090f121518190c050117070c110603070e180106051b010212070804050706050a0903060f141302030f0c010c02010f141207180b0d090510 65
    0x200310606030302e905040c20240c8a404c00038070301c0078081c00d007003001c4030503c1da4a001c0d049804d41d4003140c582c40181d0409000310458844400c15091400c0094078041c0c1000c2e1095121506000b0403010200048495800303d603880402403509502d25030031844c007403000e10585500c01da0807070008800c12002c00e030001c0603207440c0d12003141c54400d21400b0074611642076070709001c2c01c00014814004c48190714003588803801d8102c031480000d402d0011440040d0071180e000c0301d40200003102c0380140018084140007900240403149001807405099140c0541030b0411440f004000607556010704513690403940c080000611070720104031742400c02d003004054404007160b0a901c20b0151000051007030b000001d0610742e8070b1040e16213030080b40b820f80064a80105085901c07090124000940b02d0300d40d800f00003000313861210000b40700c16052060000300161141d15444107003c80d604030034407202902c40290b90340b0703640c40c20022900011901e086418000b2184071001020f01b0025803080340701d004003528480b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 843069361 1250 843068111 843068119
    0x60b01110109020a05100905180415200a05070c17010c0305010302090601110a060219080906060307030204020c0f070f080f2b0e061c0b03070506040b0a020106050d03030209 76
    0x500030a4625508031080c0e40c40007940102240001c01c164140b54501c40c40c004800d007480c4515a6445001c0f5410f9000520040446044541008100300f00040b0030502c031150200200134034096500a41156a542c506995004c5008141e045159204170100c075155688044400c030860f0303a4281c020000f8038040f001040079402c0003819480e451203032007094100c1b600200752581c0c540f1070800554544001c6243c401260094070521030205d61980000d02e01c40e0407004c3c020b0304d03143c4c242c2c0380109201400b4003000d085402c0340c030500031983e40c000b56000699404560059442c0076040e601c600e420065150401213001d030003800250b804000c1000d2007201d4004098952490006244030f442c0c0e1000c41001d1400d2040c1a007020540000070241040c000d002d04102e0b620120107000650740350009603600380f2171186d44c0342c400481007030342c000c1c0d090005007030f001040c14504000005065000d14000e2003800c07000412015403261007501b200e0000c00010b01310030303101030b80c5040080180d030001c0002e90103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 843070611 1250 843069361 843069377
    0x120201090c1707050f0604080601080c040b0603010303020a11031e03040503100e1c030915020315100c320609190305041e0e1509090a021c0c0306020304060b01 70
    0x1521a03030140380b09800191501420340c00d41410308000c6100052103400e81c120409210206408a0800c21240039200500050001c14400070400007a6a14480c1c02030280c1000c0c001040002c0c3c000600100d1030b944111a07006540001c404203250a00d17008201d40c480740c0c40c40c0078181031507020009205481058060303803074140100707107502c0660f00446103400645c1d001014954134900000310601703442000f03190100d44800217403942c81a00082e4804042c0e078960000900c4a40b1a10310301d813020f00c14050300d501e907602c0074041005d481d0302d46d40900503200200b03142c0000842120804e100c041c0401035229810048100040750341d80300c0088803280c9081c0718117900803401c2c82c070010440280d02d41c5030f52140e00d89800c082ca48450f094840e1b043c1c10105185480105408403000d209038468110f40a4054008070341004004202d44094850061394008000000250b01c0740700b1402c26401120070b40c11040c2543d0310340011801c074154006440ca80c80442401b04000041c4c009420304882640c440760 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 843071861 1250 843070611 843070619
    0xc0c060f0506150f0d020f0406020114010609061d060307081e0c0415110601032604030c0b0901020708100f0e0c03060a0b06090a080106081510090f09120201090c 71
    0x800c4074410b542140d4054030f40c04040b50300712084030041c600c02c01051012400c241ca08249502681c0240050700d841090100e4144880703542403041c94076620110320400d2180d450004090405560781c054201048140c410000340320148188035002004080c0881d543c0c2e00d8100ca00034100307a029a944000c18114035800003040344e540501e180189900d101807407504d45002c0310381d103140c1c9404201006200600d000c4a528183c14000b1130300841c0108201000c116a007009580c070f00c811a1f24000e01c000b0103210030f2020a00903e0002c007036a600f0780781a9902c4845600507850134103203501c840f20390710030b8848456403504c6a410143c5000c05050080c049482140d00c0d50f40c8402d1403e40054159214900003420700c8010303007058416410290402d0701d01000d07c1d0108a52082541000a16a4503800100700142041007000c51039003031107046100701d040a000036200c54800d8030607002040c0d02c8111407440001903038441e00e21694070108414003a480524040e01a000403070301951800b101840c005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 843073111 1250 843071861 843071891
    0x1b0a05030d15061d04090b180d05120a0c030603170717180d0615170c060918060f090a0c17070f030e120c03040e0a060b0306010c03030b03010c0c06 65
    0x81690f40c0742c0c884448103610014000d4028210352031503036000da103c0c00c07640042000c14203014081c026040d50389000010070360141e450038001e001070004020040040b20410030402c03880a801180b1240041401c9203e140100d001d80120381016280003219070480d1100f01c2e1500060126904c00c20034042480da09100d418a14052610b03900e00380c07584002d038100c8a1800351201002c1c1c52086000144000038103154003090115500b110320550f00503191000c1c4100c00b00908040b400085944918090b800800326a014151440c18065440c4120214003160b40e50820300d03003121005419030b41d191900303200000152040303452001c08500c8005420541d07000d50302c1481e2149166469410381001c110b04102c3c0106103800f490310352405100824940003c00a009140503042c5200a540751814502e40f2521080c000d040f110307000f403600c0c02c01c0124104050980f0b6001c138003420f2014540302a81000c7c0c010b03080c3c409555178154a0441c800c1007581d004803d0040150080780d04202d1003420066103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 843074361 1250 843073111 843073151
    0xd1506020d030b0409080909040f0c090c030b0901060f0807020f0a150e010903300e0606010908030a02100b120d1805090903190c0c06260712021b0a05030d 68
    0x54034000341082820340b01e04002c8e41c25604a44290040c106a510a0b00e5070004c40300c0607003217078144c1d2351991030314030445505014030402c6000071a0014241d51404101515440c64544580300b0303c940103001551250007880121650301180e402e80d40014420700e00001031803c442c031041901c51504002403621001403041c0c00c00b85900d40c41e480c851091500019001e8142d81c015251300b048222286210100300307000d2840c0e4407091038014070302410040c0001d025a401a003020100e544103010482445600041c0d0215080c00341400045910448010415020b01f0003a1100c05100b08a5165411984400d2200c80700100b0042d404490b0340707074010001141401c6d00d41c801c540e0301c03d02802e4005011a091640c81207090305254121000319950546030000c5640201c3c041039080f100344903007200300c0c000d44074032004030380e103030300507890060000703045002c4030b003580e6500503404105000384151008580e0400e40a1134221006590a0700c1d08980d01e03031201e1000c8000d107042522078041100c0039114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 843075611 1250 843074361 843074363
    0x20709140103030314270c03030d05010524091e0306130311030903100506030307020a120605060d02030a0b0712020f130506042115050405100b010e01140d1506020d030b0409 76
    0x19050002101c00d990007441042081b545189014140619416980800003444100c100050100d42585004108040e040c4038180d140124000382d10900c60699400782110403841085800402c00700c00e0048020900c041d426866800d48901c10a0103400c94180c8072078a106071103540e4512440d940040c05544034012010010f4040d0311103000399840540c950003030741c1c0c80304014003240e040200c1500054803030702d56640310300c0c17090040600203818426940515a44800709881c806e60070003665002c0f030344d40e60b40c0c3c0c00c0152400c117250020506080c41000541e0311001c5a410964544004081c0300c80c86600896420380361051003540080d1a0410f407040d20b003103807d104030718580644440800e1401403881001141c00210b201200140b00c2c41d184200d0340030360b010304010000f0052000400703084a21205e140e6050041a0480c400680c0e8416000c00c0e82201c003282494881010b503c849028044501015090817240440800c046a00203507001c024a13465405200d503440a0301804111414528 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 843076861 1250 843075611 843075631
    0x1101090f030201110114010b040810020307140912010e010b010201061509291305040c210e120a020d0f11060f04032717060f0610020709140103030314 66
    0x180c1040550f0241c02004e81c600f408a002140c9911041810140d10100360440c104070480801c00740b000076802c20101110a1050a0031071035400d0900001e0008508a000f003140404001942c3c1c1542d10b40e046000c0108945e040244980103c80e0306d1180039003a48544240150b103400302c0010110f01c10031386000b001c4450b884240c840740c1032010b80041741085100b01103400307501d805411401c1c104140203140600320b64003400b62940c1084200020b4032a5448240100044004188103414800c6901c806405511900140d00d480d042811f40c10000c8581c8140250103000c01c602040b1034000c03a161100c50140d03940c4280c450908802503d100310120130000346a80141c0000e6400d44a4090141d007250290500140150303080d40d00701d6400249031003804801507100300800001d1040d04840c1070012101c80900403a1500764103003005c801d4018031035882480b4058148402e14000d11409020b041d0030700f02400114000b014a018218080c4400c6000a1070305a6a41d440000503810b1400764005c19 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 843078111 1250 843076861 843076889
    0x60d06172e0203040219060c1a061008090a0206070605010302012a420b030a08160c0302060a0915050414091b040e01080705030c0102120d0b0a0b07110109 68
    0x41c00810003504010800c0ba001001c0c5541d031032042d4801400704004096694403245002800d24051900481c0c40031880540c5000100344006d0750f4174401c46450210840c54030003015924080264074201c41a58043e400100c00100481401440d4004074103a134003e8171600300d4010100341e00c2d001e0302c8400a1201c66120501081e0300041c84101d00036800c401903481240402c1c0c100c2007113a0580351918200040f281046034052601c951030301610030904400c030043c1800003201e40340d070601880344ca0364020b2862080c1a401c8100714035412042c01854001d4040380d26802030b0795002e003400b0158011424181010b1104002c03040c40b540485090714403801c61200074080e0360080c000380400c00b0b04000f90303210340741c01044919000c0c44058001403031040000081540b401c3c3c0280d0500310650410740c020740000c48000700598000515182c500d401d020299a01d84540380190001c1040440b15075100c04481e0380011071003144030203001c02c90b008138400c1e40100f200d2001940d1941480c41007107950842c00b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 843079361 1250 843078111 843078193
    0x21507031d0d02060a020a0302010c1803140123070e0a03110108060103090b070e011e020607050714030a0309060b040c0e041e0c09060801090506010e040209060d0617 73
    0x72001d03240c28880240c449005864070b0760006440b500444c0b94840141d00050a42041c0341e424020000045003504040c1440c6603514114241003a281c01302030203410010308d009040b41c070254044504604100c0c642510036244110b68100d845c1c0c15038102000549011002404d4070704040c81d08122903200101100844a400041d16101c800400c02030501d507803400c80202145010035407921a070b09a0350b40614910a9100240415110a00c141c00d2071039080742c02b1a129400164003900f007c030740e09040b92185428a88414000d108840440705400007254800200382c00d0380106d200540b243e00700740900491541440b0403030301c804624200003070701000c045607a030170181c0c01591402e1b04151006403892550014406584610081c2d2001904403041046a140c6c4241020b01404410030180002e042c0540002c0c0100664000319206a600042d21003855448100b11410300e15080c109224076550ba10f20310203207042a5007070954030f00410610000f0843d60303070080c01e00c40d615a12104410140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 843080611 1250 843079361 843079397
    0x240801051c021309060b030d0e06181201060315051302090c03072a1713031b090c09050109141309080f07141c0c02190b0403050a02150703 61
    0x30981080c1d070409403c0203121071458480c000c2140e004e009400101d6099541018940b40444003001d0703004014480e00c150f0203681e00c2c0822244140c1c011101280e00740c840b500014400700340e101d1944817561030040004108240905410860103807100d00f00b20307a80d40c2108807601c00801010007036000039034100144040546070051a041002441d2080c2000b00c4001480b980300c034440089c003001d0320062000410412002517804841010041b80e074244210402100c40514050000a00006481c0c00804080d1121700d031803c000d010b240b00520100010150103010b6117120700030540000e540180118107401c0c05001102c81e000d0103407503414040c0564040c00002c02014004403401c400400005800d181d45c00041e2200e9400780081102280011118601e0468400c00940f20710000c0d9010818460308056401c80103038060301c0c41052084034644848413a00590480c002149004c00d012040c0400001d5501e0507600c01c0d200148500e41c215412401802800401030000c0e000c587c91511401c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 843081861 1250 843080611 843080659
    0x504030203031b03041a0c061f031725020102070e070e0402031302030d02030d060909080405091306060b070b090705210304090c05030405010c0c0b16020f0724080105 73
    0x1c0f6026241131035140c008003076142c410240c900c0040113011541a01401052065036009031050071035041c01400d1452590410f0914400a010250b5100ea411550001c12007103a1003810381d04200755240d01025040c6403c2c10403000300345d006100b02c0c040850507603070386290a409010251200c2c07210f00c040800300400380d80010040f94110011114600c01a00c0402c25148415102e80155481780d490780f0302d4100f100c00f107a0042e0040d50421441c00b000c2101c0c48115001e403001540c49074411360b0303019403150702100000d0b0700403e03861603c03800040c08905203000d064030700e2182d5100d06c0d00e03859201c600da560b100c0c240211540000d03601c1207800000030305119014151200f90030740cad040554548000c81114441900d003008914000300f0001004028800e850001100b41040351485040340c45a4048050082010742c0982101c0c404602c501e008021040b0171982c0d40301240c0340c45864445000d403400c400c4851040f003a04810308410f03a140070720b4005068580241810042e041c05134000e4400c01c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 843083111 1250 843081861 843081907
    0x260609031b1002030a021b12030106030f0b1807022415150a09440313150e10082a18100309030c0602070204140a0605010807050403020303 61
    0x101c02c0550302810311a540c0081c602c02c1d5024440181c450300181d00d1031528010300124524281c01242c805110488404c080e80c0c1902d019203000a10308451a43c3c0d0310003081701782d4100f6130141048014044c184044080c56104e4406a400d5405d001062001c070180b80c4003011030040c01c401d2240006a6001e203204100c1c2c40741000070407038650b40384410190300240d4400903003200007a00d00c0300d051082c01d034049100026840c00e0407070705251040c3c80c21421000d900402800b141c61076130100550404108106803064a0000e482a10704640d0310709d03558800d205201c0e004404100c2900d0750030203500c1e00600800741034201d525000102d9544650740c00d002c00441542c2403180b4000380030802240c0d09c0784040c068a040303041c15101a00c0d2101c0410218051022209040500700020880000c2c0e1000e40e0b0359100f68407040150b1514640d2000030050010481d0180d480c980c80d6003003040d018165007010382110000e80b03070f0381d0710380d121814110360318801c6020113034156004104002d036081181002d1001c031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 843084361 1250 843083111 843083113
    0x40b0a031220010b18090c091f1206140f070c02040207060606170a05060303070f0f061e06050a0e060d0c03050d09030c050402042d050a260609031b 65
    0x1c1d0100c02d414000b2044034981821182e5480e0f01e0311440c3d0400e151140c3d0400a0444c000001d40f801030440ca41c1c0b10b4a20411070b0007614480081000c464080b03004555240010008a0110f900d03200300000550031404180d0300301d810030806103034840250b00194050040c901410076540e413061420b81e03560640c11000c0f60096400c000c1d050109555202e0f0f540901400d80c0c503491410451868070840d10380c050305c4440428a00002d00a055071300008035002180e015042c000400c800d41400d0300c005080c0300001e00391038103044040b0841c588158501808040d46c050810a01c0d4540080c05420a020f000c1c00c03011181e0f00010030518a003468504601034400d10040441c3c1e03860307985040c00c1c40564403c520102c0da110350107004010050014201521040d030303085007002d00d480d051107060810320068542040b2700c1e803400320b100d084000c440d001800d000345c0b110448a9440d50707141e40302250000b0030b4080d81c0349084444030011000c10038a002e6421580210304000342c40100c1030801003291003e50031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 843085611 1250 843084361 843084377
    0x1706180c0120011b5003010b03010302031501060c060218030f06090c0f0a051030060503010203040308061e1905010f050307080a150504150303020c040b0a0312 70
    0x54500c0901480350304402c1c036100500e5803400c900001c0c040c4201c58039102c0d00c000141e100b0100d2070f0017440c8000a2000d21403c034031a6299859003030002e01c100807403804564540040003141440c1500015412284240e08075440e450400c500500980004e004aa00055a46401d43d0216905801410503032032220003555500d640c80001900c0d00000340c5100580d5044181044070307a800038403c00b140500140c3d020894034080c8400900c1c14800d50107007902c174201e151040c428052080040d04030501e5042e40c2c0b8012003821800702c030074803184529404181c50030880045614141802601e001c1d81e4562074500c5a40c0b941c01c100000b600301c414905440c481c80d41302c1c078031082d0740d11208a58485a011380d04880c4a08003030005085003807000c01d00061203410402d1100460b0701102150388410703900c10008200042c0705040c0d481c0c2c10700d0303800a54030034100900b03201a545038914040c00c0b82c0c402d400700c8118600040510081d82c03d103030440c41d8402035410f02000804c1011344802c00b4052540340c0940b0f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 843086861 1250 843085611 843085667
    0x70e1e1008030703080601030b0a05011e020a021c060f0209030a1410021b0c040c0813172118070b130b19020136050a0506011706180c01 60
    0x450b6400c480c0c01074000900c64070900c0b034507507018031a84600d1501074503001845428800064546e841d0b00031021030981080702c2c1120300030700c2840070b85100da50040c61901140c08800d03002c0110344806074150f41061525090701460106407080764040f07400a00500742100d1951038a440045c00c0d030000b02c00e0340c01540c0100d6400200c91000f84940240b01e414040e210100e803c2852404800144040c001da241c1803403041c1d510b8101e62802e80c44880300d01071035010b40a52920f049c1c00b00d013580c004042800007107038040f505401425240701c984a00342410388a9a6400e109a41c680100300d040b000c0f80d000000203000f001041402000d210401a050840c07566484551030902c0d803040c2d29104104044061001140d50b0a01074020701c0c2614546150b191107a0030a0341110104541c40c0c2e040d01d0003010002420800f0910020314080d0300320054855035a91104410800c0603200102001d078003d12001a010244820300d0002ea82d007000c0c01082c4801c0c105005440d050924034440c071800c512030010754 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 843088111 1250 843086861 843086863
    0x9120c03140a030e030712080d0204030605070c110102010908091005120705040f0603050417090f0405040318061107030809011407060b09130b0c0a0c05060406050405070e1e1008 78
    0x5404450380000707124400300b604000700150f90b940000e5119030081c031001c102c982600c00d580404681c20081d0b060b80c0b01500d5898100a100e2940010310080c04c11042100d50340e00045030301001c501034000154000140b000480c00c840c9480002083c1c0e0b50b00748503010082c00c0c4100b401c94071512600b00541b80804901068400a1003110801c0004030005070a0000d2101c040c480c40041c102410b080c0182c3c10981e4510f1420000c019550003103000c08504490700d5910210460455440644208100d04050400500502c840603080c0702c0c90780c1564000407801d2050710b6540c5642c0000c4090003100c0d007190340d24500c030b900540401f13040045554443c50400a40070080031024826000010f00591450134031010a034010710080c0035125110440c030104e220114500e0388080d90214141d0b0315100307100d0649402d20039141c054600c0c032a550030001042601d5102c1c03401140900111031a280c1d40b01000b0090030741c11a00c0505000500e1480b4410840c6500c01e0340c1c000203044544c80f030807a194a01d40d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 843089361 1250 843088111 843088133
    0x4060b0a05120d1709060109090206220e01120818010e030f0109030e0d02010f030519110418020306130506130c050d0506040e0c0d140604080304030f0c020109120c03 73
    0x100d40b40f07801c00c06190000c0c0c0c1e00038503080c0c108030043c5980000341c54010509600ea100502c520440643c03600842e10466458004a45807400d01d0500d10f55101004000e00010b60347d64041c0131049004003002040b042d181c944a108821f070b01c440030510b810740500080c2011a0142c00c1603050281d40703400310708142d50905c01d083da038801e207600018850000b03080040040709451007840c090800f80c0c00020140c0d070300c11001581035405050104203501d4540c40007910100340741d1200c54403843c1c210027802480c981c40040c412142984410300401c0ba00004500492005440181e400f005c10600060603c1050700003d0380b101e00285941c00f0140416601400c0d2036502da80440003602c0002c0000302280c0d223200d03c1d50400b500341c0e010003a8010700035200342d8038800c4240c078901c41c038101000a001c1010348480324108001d400b060b20b4189c1000c0c039243c00c158005960480210f02d200880380d010611804088502540503500c0c07495980c5491095800e110304ca440a4400f041c1190340030003c98048480303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 843090611 1250 843089361 843089389
    0xf020a09051602071202010f05032a0c060f070503060d080c011e18020108070e0d02100c1a060307090b030f0109050d1419031112010602010b0f0306090604060b0a05 72
    0x1902c5141c9102150090826039107400400b840841c41e185003001d40d900217002807000f08a400c14540ea619641802c402c00171380484083e50302203050001c603900300804000303402e600c0c0380b4400302c4845480b0b690400c083c84a00310341a2001803014000911146410b08868010a0103085000c0c81c024103103205909603001216004c0385003841a0840035040c0c190b00c80c041c000c19000340b440c1d20910207580000e0071003001501e15810041d414154400543d01c0010b0007640135401080316490107908500640f40740c500c03000540f400c046400030328030344991000c1c105204180c020094401c0c10300344505400201602c021180d05803085c02c22504c0145401d104051070035004000518155807070f144014811000d602c03168040710070600c10f40c1050321380880b9000c6014101d040101f111846404009014010511001c5550203068000111a90103500c51900c6038400d60b07d0106545080b001d2551361038065800300c100758800b00006011a441d544070301304820000b8500c01303205070f8a03000188040d0b601c01d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 843091861 1250 843090611 843090631
    0x10e0402120105190b04061707080c010504060e061e180a050d0302070e1503060f010905060402041d1503100e1501031703040302070306020a020f010c0513030f020a0905 74
    0x10511040d4604099001504400c5100a00051034000494516001ca0161344125140c480710800800e540b13540000b40a001d226900160081e403c2180a03529841031040a0443c09074055a0525501c5001164240e908030b403070700000c00c48a10144402980b00244811720594140c003d03400665405000b400350801c1c2514034003020020004018000a07035500c41c1d0710440300c5401c80000030390081a441c0454920042030380080d550226140e9003c0c0002d41010b50600130903042114000359509070b241a6842d00c0b80411040d6110704c20b00007244141d0103000c0011012034042c2c16165211140c941e03000c9128180303161000b81c80c81c0403e02d010140c150114860303480302c071030503580b41d03080001c041208200b0203412001d501d1078880c003061040100061261140010008050500070401e00c4003c55201208669580700800025110f5419007031104e41c550130300380d070020024824010b94407203501216000810601d141c0d40d5008402620720201e03081410450700141d040e529115042c400c59005d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 843093111 1250 843091861 843091889
    0x4031202340602070609120606080a030c03020d14220503030d020903060609040206070209090c09010303030b101707110a0210020106061103030705030106080a0b1e0103060b04080d2601 81
    0xc2501c0c00010150071620855005803000c00995a102051030b0403560007a2803040486100d007042c001138075036604660300520421070f0520805900441d0350345054026425500440001d42c4201c8942d403a281c00c0141c240800d2040069400708141d034050000b0a0480302d20741a035840000c02d0444e0440e10300c4507100340d0b010034a03811030304061210550200341180d101c0a00c3c5010703400200700d0b01a000d0b001e401228402c1c00100700791401c014101101c0c01c01840c1401c2507a4030300d03004020304040f220250140c510091121090b60096182c0301e051247d1001d0000d50b03039a0410200d411824014011343c1034403500e04030b075000d81c86a101d150700e120025800400c0f10340c00d00c40c000d01b125011200640007544200100100c00d41d001055a054802a00d051012070700c400c40c142c4041d118031083e25620007640c414440121a003104a484c850780e081e00c050001035034334600075026000358496441c0c40d0708108803548080f0310801d0032059801d00c02d0f000c41c0040307100040c80c0e44806003d8000000e096125 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 843094361 1250 843093111 843093193
    0x92709010605010302090d1b0b13050a230111071e15050408100c170a05040204050606070201090510050c0d12060b09030a0f02060f0d0f06080105010b04031202 70
    0x1e0081002410080c24190b280044060104a2400c40d208001d02100c0b07030140020f240304400d02001380245081c42c4019102d11664000c01d0f44161607100c0c0c40d00c17a08204000085c4000c02c245540c01e00c1c44c4e01200819030405610054410314825034138011180074047c4045202d9a042d0900c02c058031003140e10401150400b50703050043c05d00c4100b0f180910000380700130030054400080344285005030020105490610403030036268051006440e0021102190800602d00000e9102910941c0212002c3c041502c40f001840130a10580f180a800103001d4402807299040c05181c00c111180317a0701c0d05038585140201031038104050443c000e00043cdd00001445030408070703405150054a100d55841386440072820001e59100f5104900070301c415a0394108405550f512429140101c01c50210207a40b18503500c0c0c3d0390010b20800301040b914034038000707000c100d0420501c20641030324941d0b24854030f01030450b1600c0c18030311841d00c1c4140c218031525402101314000e20320400001c03038040c10911038528503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 843095611 1250 843094361 843094363
    0x2040507020f030318032a1006050a050f030316050d0e03030f0901080604090b01060512010e0105150319060b0d1a03030f07020307030f0b0603120717092709 69
    0x505810210340c0440b181e800035103808011a600004400304802c0c101003c0962682140105100c41c00000380d03050043c0074050454607500c284201d8003041e5040c00b540e46c11007608942c014040c1c1900840340344070034011800d0040d8244001000282181d0030405811005172845820800844458015800d030120050b042010302080307180131006181400d11082c0c1c502d165020707418400381000306902c003280301e903142c96001d07045203500300036a40125a101e00c8081c000ba8006000a0442410b0310000611003034112080c2d4183ca500a000000300c1360340e00c14000341604054080c0381d00038007a8100d450301c038a0901c10a03000300081d02c511038440c03040b5a0160222940c200800d031400340c035012900007665000c0103c4030b1203040e64903242e49400e858004a4035100c81c94000800b82004414610107118102030294170690341242102c81002070b0525500c080e014440e0001d1800c0140288051060f203c60064544e03880003500c81c0d1001c41034406e0044486584181c82d500782a110002c0c4112010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 843096861 1250 843095611 843095621
    0x801080102160f1506030302030c0d030605130b060408061e0f06091801140f060406050a060c0206030a0b0d030e01110f0c06030901242301051926040204 67
    0x480000310306264150126031022040e19000078a540440d81c040b0040040d00680c0807424424503104214841c1c480c50080c0d520361262241d249284240c42500418074424007400381981c601603d90314a407400141c0700c2d406044807050442d4000e00c240804100c4030001c000c800e200d812500303403800807202000308003608203a001d00a40404040e41c0b00f00840c545454503460780203101083e4440341e4a968100381c500400000d0701007440340300c5210610000c5000740310400c0c040c20003101c041099958a10400011000a1040101060000780c0190240c40e00c040a0750348640e83c62030104401100500050040d10361120032000300d0303240107209019580c40764505226004080040000e0203500070a2652281c1c486140c61290000000048400a00b90400e14402c2c0307ca840010707008054a1124206034020f00030012075480f07040038440380c8202043c1d140141801038660351b00d80031a4058030340300d01d4140c104620038050b40301207031034041034901200700441100c0c040584280c02e080c4100310a81d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 843098111 1250 843096861 843096869
    0x801050907090e070e0f1309050609010c120207150e03030403090f060e04111209030d0c0305160507030e0a0f0e090604080a0f0e130905010b040c050a120902040513030801 75
    0x8a0b81000340080e0b011a121140c2201d0182889401c00d8410301c0000c800c40110b075041a0090400d403001010311541c0d40200d0580c2d0312a10594055950708031000382220002c041c2c1c50700061030030f603103055030046542c01415064081e0300206500c80a25100c081621003000700d0060a900c004104424141d100c3e58200103000c0d6031032800c0603145480002041c85500307114080c46580c0c0d881d101207855400200711603201191480083d41d0345000031180e43c07039800005031050510b09212000030224440e10503207214014040384141240d84810088a6980001c0021411b2000e1841045d960340d580c100c4400040481c0f88000840350b0030300202c64001900500480fa00c0d40c0a0818800010030030003e075000c1203114a1b0196404200690807100701401c103540b50303040f10b40c01c100c00501001580240324101c1c011402030220446031402e0000312065014030314009103040c024015680d2096401c4841d2200c06003020500209540004084400c02d9441d101e20b5401071095408164206003058010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 843099361 1250 843098111 843098117
    0xa022d03010c05040501031d010f140a061a03190e061807050907081e0c0a0f020d09170124030317010b1903020f070308010e060a050a03151b0801050907 67
    0x3250b9a140e000c0d1040c09640a050306158807200702c41514800c400c9550b04040b03400700288001c840b0340703c110703005221040510031202e50180c009a0450a2070161600b00d410400101100d4109240c2d5030701a03400140c000c48a0090980840c0e1000400d409160103061007030014000d00d05002e61071100a4003010640d1703407107402c02482003100d035640f0210903078480250704046140303603901200002c070035240404400c0c2070791191040c408074a2880000d000200d94035210f10765412803490f41070b40d176621405c4010000808041040c009880091001c030502910440085209a4414006070500000c541e8401c0e07204000b02c000c00503d40d12051404403812040c2c02c2d00103075418020940c0c1d0754070a15442101c03403014982c04000f070320300c01e50440e200100040121901c409080ca4020400030081c070982c3c03801079100021641340d1a0001c420740407240d005100c0380703270750f45103644800c4070820690342d44a4040d96500c507582025411940c00585002540c1d0f02c06030b540c10321007003000300e21000d000c0e0020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 843100611 1250 843099361 843099371
    0x13060626130c080a05030a03060f0e1504020d061d0f06100c05070518040209070e060703201504210c0201030f0b120a020418051903020a022d0301 64
    0x51030298201500401414103045900d0a942048034026030306601181d002c1c0b2038100000240040440136004204059406000c010f03a203201c410891420303400341c03000340051080070800d031500d165209401810003034009801d102d03083d201d59049912607030214509180f098046011000d550301c43c02e50107840d046010350702c0e040030390226090281c0075003000284035900c0180c03c01d0050401c01c0200800700203005c014400f032619003004000009031402c030301070a800400f00342100d001303000c24201d80c00040d0200c2e0501d00c8680b0b0843e0000d1610307040001284000042d000c40f0712090081100600d20780d82c0c0405641030a01e001406a80d007090f020150341045500300043c0d80d44014000d04150302440c0c081014010720b4418001005e555120a5002d01c0101514440c004086500c0f800b60f0700071074040004812928a20390200d096040c01407441d0400c11800321680400703c0c0c602009c60192040310450306096010403d40880c0141c200c1e9501000c4001c1c152013240da0340301031b0786020282e000b0f101d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 843101861 1250 843100611 843100667
    0x40603061a19210f2c0c060715050108030307021c0210110903100e1011030a1112040503040e060609010f03020a1b0605040b0c0708070303020d0b130606 67
    0xa0200941c2c010790307080181d40c401208492114a410485149810000300416081c1108244c020219000800201400b0050340d140303600c4d92007a88084500910050251440ca80381080742c41da000d21421103840d003a0f500020982010780c495507000e041c0c4000255900d041102c0301904d00501c051201903400c803950000201150702140901c01c0c0c45819001048401d01501c0d4079980e4080c02604980520592241008016080c0c011014640070300d8191500000300c00606c80c02c0c0c070001034007944900c6041002c1030b10000c00394440c01110000b444903a0402e8840c10308400032001c00c1d00c045e210ba9101040c1030190806500c0f115812003000ca80c0145031481c0040080c0c5074540d440301c0c82082c5640131a501248a008801c0c02c852444aa460b484844519141401c014a000d6800340d40d524062400200001c43d00811502c56a40200415040220560b803c078003032f40c44280d20341641ca856901580c0f6603180c80454110602c81c5980126a007410808006d06c1780312000441440d0101b5041c40d09 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 843103111 1250 843101861 843101887
    0xb0a080a0b130515010326190306050a090218060a170726091603020a0e0603010f09050a02100f09031e050a081b150604020904060b040603061a 63
    0x1022140e01c5846104540c0e01c802501003000da00401c09802da003d00c01c03200c850181d42c20f014034184c900c220b40da07007900c030301800c0000003c0c0d40c90706154001c50010800f40041110f04e140b52450b6503171900d0085803040d181e9000c1070820207180d000b03401c0280c0105410488402109074840714841c280d503424149042c011004110101038050100d42d4203064001c20442c502c02d4040b42c80c0104440b82c0340d0019604500c1203441c4c0300084509860600801100d40940d01c0c0480055084a800034050703510b81d802c29018034049c81300038112070703410b43d07854030302c2c80c0104100d0281d4100580910050b0030010740600601880d200180e850408101c44102803158160300500607005494005007207041c0d200419403141030070441c85a0150051203040e51400411403554002c00001a8040404240d40002d00c8029030340c4041c02420f00800c80ca4000248903401c00390701801200400910100300c580e66400e0a005690198110100094030341005003c56027a0305524000792140420071403400007142d01103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 843104361 1250 843103111 843103123
    0x6061212120e060c070b0901050f0615041211013e010608060901151508040803070c0f14010b010c050a0803090f03040f1403010203191e06090f0b0a08 66
    0x110040c00241c1940c0000c04145900020b8981c06200c00c40d202414418142d4143c0c0c2c0044404540710701003a400075084500c107008030390207a078449002c41d40e40c0d19040f00b0404910801c01000e07500e5003040c000044d2015140882d160041d00030f44141d07a54000d198001041c5441008021850300101e82c40d00718080d400d0305a1504500b00341090386020480c00805078094030b4168454851840b420062042194043d40500090342000130000300340c03035541c0c9144507c0203116580740049030b888000500451005001158071542c83e1030445110665581c8050764640442030941d107806039114052102c00c3d0034421401c100d502420310101d80f140c19900c040d40d444070100010090180031002c40c2d44440f04101013900c4014003070642c0c2d26a40c8a0080c0c050540e503920444000310048420b2074203500341842102c1c0603510801d4404400c44c80e424107203018012503580100a08003a100840c8400d40d28400e00c005802200c20109500000c2500070342503a092040b0f05118481c61724040010010021301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 843105611 1250 843104361 843104393
    0x80a080a0b221e050603011b020a0f0c0302091801060b040f0b07020321071511090d1b0b0912010605010927051e1006020a030e060f16060612 62
    0x40d521030806900d4448080c003c10b00352040c0303000303050300d810b80c24002d10340045114038002d50003004210280e402c003442d44031409503810050f80181500001041d16400f003107190174010064442e81c070340c4d0ba0707010544040045904800e84c10614400f600c03015000c0c0110f000a09030034818030308007410010001d00920040c03040503d03980c80040c1100c2152000e000d601c8460342240c400350300c605420b0b028860f8960281c0d07000c590000c01c0300c00c03d440c452600d00c106007005580010389402c10300060300b0b0040140c031605050f20102000f41807888200104007070f0501822404001503280e030008010300802d8180704803a40d4450741855001d11450340d1200780c4200b2183e01441340c20030309987c0002c8000e480d607256403131155181843c08000143c414031203181503e08501d8030540c040e80c0d56126508418000b80214001a004014568042441030182410304070300103100510b050746003007080c0c40c140d0003078243c00503144000c1c0000b42406918031401d00200b40b0210f1703550441d5010740d5007055078418541 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 843106861 1250 843105611 843105649
    0x80603070b0406080a0e0604301704020f090703090c0e0c0712050f07030c03231e090406060809060f092107151a0d0b010308091903080a080a0b 63
    0xf000800c0d1031499000740b10558106c1c030a5070014203050070182580d44200d02641501e0481c10a1408003540b5800303450010722240c1d4901d0080c82d4071203206c0c80d1400014000766805407050180a109507102944a4010317151900d000500b40710b240362514259a940d40029250072800c410840d00340014011580a650322590f0a414000804400c0d10f542c0165006201ca0303410104040c8105030308140f1403060a80a81c079060070385003042d444002910400811003424440c1404210410707285006071203045051401e8072070500d00c0401c04141240d449611910001d000b01062000c41c0b5401d20400341c011103260070902c90b9141ca483c079145d80d00100c5000100c1c0c0004030018249604a1409450b1141d500c0407600c0c05081f007103619100640a0480c400205141c4c0440840d1a4a0300b40c0c9010a80c80d401130a00c50340742e10b0361700c43d01c1094200c02120354110354280340c149180f11201c1141009140300b040050780704c4105440060800030011700e42011545030a2814809030f89403a1441050b980c41d003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 843108111 1250 843106861 843106877
    0x1e0e030c15040c08030d1a030604020d1e0b0c120717060d020a0302062b090b0606031b0a0914010504050d0b0702030c1006090e030a05030705030a110316080603070b0406 74
    0x450f01825414090b0300c80152400040343c000d0144d0866007010302125071103602002144084420191101d03c00d803002580407110110303010004551241032900039440c00004030450360580c13a0344029040c1240d0b11001c5000018452040040b00c0c80055000b0b4054034050144640c44c401110382140080c001a200c2c1c4c0c0c14002a908558071148030401a55018003066191704d140011400321710b0b0300002040318a002000c1a40603002d20b445a02c44280e0401020122601c1f1101445880d41c405021600380d1140f0b402e111400100700c50040081d500e082d078600c040c582c500f25141e66a09122480a81000300400080015540c0c880025440c41c3c1c0204502e40c0303075101d030f2070164075502c40c00940038254000c8051200d014141980580101c42404005000044036500320613101d2040c200b054011580c240301040d5010301c26800740d98040740c0301000040c4520b41d2400c16080d90001c5805020040c1602c4054031902d610100d0160000000e41c010210030b03040c09903005840c0628014001084504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 843109361 1250 843108111 843108113
    0xc050702180a0f02070f02010207060807050d1a03070e04050706030b0906040e012903121315030e07090b180712020d0f06060908150c1b010e011e0e030c1504 69
    0x16500280040c901a00110340c3d5174030a01d003600d080c680f03400090340980242030740010480d01902c4503a109440c2907940034034002c80483c05200034034681c8800141aa440000040c1c0c94070304007d450064040600494403c2c6400d01d0a40d01d000102e070404010103090200c1341501e5111401c40c160054030480f8007055140400030300900403c80c0480095032041c076084410498182e40007a02c41d03680c4140c082e075080c00880c1051084a10400c808050318100504003000074402c0d14402800d0a0024a80071030280d85c0800e86905d031000e1a00404610360742c0350800c0c02503141007241402c40c0e150005120407036203841c210141003824000d641c01249500015100c20403401c0c0d501100c1c9110392800108081601c54200400191a5004200da13170b00c00c0c00300d40605000d688006034030400e141c003281480d0801c090082c080042013001724018a40d01c41d1145140d1003020702840b0b00c0c0f0407804151000440714000b090058482d084101d0705150401c0226880494021070341c2803424000c44110450b90300c2e0f07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 843110611 1250 843109361 843109381
    0x30904090f020d08031005060c0d180902041e080f06010e0612010e0d0212031003020d060906021603091512020c0a1a0f0a05010b031306061511010c05070218 69
    0x1030180080d0b100728000003c4041021400186000f0b480e80c1c0000b00a2507101c3e01031040e05e100f00840a0500e0340003540f03002e241072090a803007001520305550350164503500c1d111031081e82c0180d00845209100f50032010a03d452a14a0b00024148103004001c4403071a040c0c0796446c1c2d0300602801905000c0900017540c80d454440755010b0000000d0000c1101c2c2d55144001902c40000f40c1095005000e40c01b0b41c148088850401e50b40200010035030100414910303030800241c225005030032202e403600c4000100c0421403e1014160000b05200701030340000c1d0a280050180c3c80d9600070b584c20350650b007492903183c3d901004001e104510030300c0042e17489081d8808a894503640031002094031840510100c2c8070710806c04098021030303c82d043c0381140e844040515041d98006d014480e080703842400080e1841e0107514030450300c00d020300000200c554492120030b2850442c1c0f000000441c038140e0720701c801d0310b809110700f40441c00c1070300c1e1160a1040c0341e80000c110454903e400c1d024800380c0004a1101c00c2c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 843111861 1250 843110611 843110633
    0x31217071121030a0b0f03030d1e050109141b0a0c21051b0a24141005131817040b210708160507110604080f0f0f03090409 54
    0x15190003100c4104581e074800301c0b0190303c219450344207642000c17020011420005c1407215150b10080180d0b042c0413644407954010f088411100d08030f2241002903040402c0b0a21a460103400f4a0f01c000c9003403080f0203104420480054898a40100c2c05a00c0c51349000d1040301381c0300c04031160b140c207201d4001d50341401002d009000202004185001903c2600150000300a0171540480a0141c440141c1e01110b030b0784400300b18801415032071451101c11041d4a40154210601c03007940c1e00003031103010383d040451051404507400e92003106580c0b0107215618010200d00511242807009009044440d2424800c080b04104020085e0441034010606d540100040da400791410f803040607154240072105080900d4441541c6c202c0c50800350110741854400d44041d40300f40101074226400300c0c462203044916034040b200503102100c1d031030b00d901c050760365180061000b4884000108001c0c211150000e061407000095480b00f80e122101d01c250880c800b100303a17944114100c0d80085c0c501c4036400c05289400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 843113111 1250 843111861 843111883
    0x6030304061b1514151003021c09050c0f04090c051207090c0e0a050d02030d1202090a080d03141005011d09160306050d020901030816120503010312170711 68
    0x5070080c800114140e0301a8450a2001001394210000c3e484042612524541602c030701a08855a242501c0d0560b000e9002031048120f6410381d04c80811380c00b4840000c0715400b40c0300f1540d64000b1007120400c1c1c0350101c120540403808990820108113a03903101118040d040c45464041c81100c64161100a000c0c082c650040c84000014480b0b002a030b00024001d41810700c0940c40780040b190042502c4c1010314144080c0c680c00390046c82001040c05050310341c00310070a004613000741c080146803c99150700515100800054004148004105401070151030b01b145910761401514002c110300c0c41b50700300181085030001c1c03e0a50007191611556041403440028050f0803c040c403003402000040f1303900e4080c4010300b41d5030400000d5103d0301049017140c5580d030045c0d44016000010310205d80820003e04100d10703511340e07058040f1503554809402038009482c05002c5071001c0010424009a11050f00b22004a0720304505510403907d0301c42620400588050304001070030700c402c1f0440b80304101c0c00c4180d07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 843114361 1250 843113111 843113123
    0x3020408190f0f05060103020112020c060f0603012003180307120e060904050106080633090d0501140103060b061c0e0c0310060602010e01020708040605180a030c0305010c0806030304061b 82
    0x403c0090821554440081c84100c3c00954400810003d03801544240d03402816548050680382d1941011000d071103501900c09079255586605058040c106c2200c0f102d010000c13120940d48a18001c0312002400d02d0b130084921a5400800041b00000c0507403824841c10300c0c15090824070746601c0c0307012801502910001d51b42151034140045441d039003107507045103d0101250f90b20507010301406400082502e030882c00c1607114004a150404501d800054240c6800c0541003102c401c400b5180c035406d403120840c0210b40b16a0101c0188107120340d5000c0c0d46001c44050380c140f80b070302503440c01e00c0d04402034030120300060b00e5603000160b00307806050000484100000303003200e49451310300c1307102e20042800b885594003561070301000300520041802680c2015821080250416140074002d0381d980e48189500e899005e86804004055500c8220190240d07003e5800380035010f00358a07010f400c43d0108001d80082c848507504200c1c1c1e5075400000c030740650310a4508000d2a4103c50400044014013004c002c2c04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 843115611 1250 843114361 843114383
    0x20d1e05121306021314010c170c28050f01050601020c151204051c0311031611030310151803110102030c030c0102030412183c060f03020408190f 64
    0x1701000680d60441038605d0b26a22102e5000614019242112641401495404488600b10201c01c408000e0404060904240e0700c40580f405004060908450030825065002d4503144013400030422600b503c0c2e290b10782c000c0180d4280400003075601c04007280c0081c070a28840d8500b201d203501d0f071001d507134800303408180e280c00f01e0605281c800c0e1212603141410030500340200700c48c803c0728402d0207034845400100441502e5a02c8490348003040344869410f980030303c82a8102503104203000c10086102c0c0310203405958550b8180351a0b66840050700c1c10002c10002041c4030304604400948581c0704596101000c0210780c00d05100503401d60161101c0407005000110f400f008175501900158800c9220305883e10f400a1685403d98441880c06218086610540300a0000707400c105265280785110b000300d8000748850403481c11910020804161140038585810042d07541c11882d541000301180c1800e60820342440c503607907a2000d40300150700c040d1100000b000d00b40551107980308a050340003090001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 843116861 1250 843115611 843115627
    0x1609060905102607080a06030206030103020d020f12030901080a020f0a180801090c08060a050702100e190503070b0106140706021815040828030c1110020d1e0512130602 74
    0xa5032240071246a00411002c170002004900706119400a881c0d0003403080f070075030b401c40d028801040195078089800403407160f5400450754403c4440b101444105000750343c1c8074400030004091020141c01c0c00d0b84180144072040f03023450000181c4501c41803600d01244002000594002e900c00141d0004405502e841d5055003440340c00c610f00d0381520900c000b140d025032645104141140d208441c0400160084044030302080d100707802c5804402003520840e041088000c502c9005c074800c1c0c001c2200d0540c00040e104081060301c03c0c425006003071604003403903074540c2100015400d10841e14020300281d40001c1c0c908640041040700d244158000d00710403007440c40b908400e40140e0042c054203c41340b003001800c405504000c0904507055102220022410784555402e4480c5400c1d0700044074540071b504415030181d180c04480b000048440c1d130042c20414202d4102070003603104601d00c207c2142c40d0220040865401004840c000401c158880c0390564910141003a400340700e1303000424040c0001003d00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 843118111 1250 843116861 843116927
    0x51e210c0124060e03070f1a0f030a090b0a090b07050a1803030903020a080a03050d020c03090306040305041d040b010e1909030302070b0a022a0f0102040806160906090510 75
    0x10b01030703410b41e4403210715400700003003016a160382c3c40c41100d038030450054052003a440e00301500d60401d11445102d07821304850308007110042e00219500c5c03482566032000d4005000c01208090303005250340008121881c0d10703072507941c01d010006201030203020380040c1c041001032241c1c3c6484228070070745986100030390b20307460000d00704000c42c40142d110320300300d080120395048042105140560303d41c80382c0386030075240d869144c06904404603604440c0401d00400000b500c085c0f120a115038442d5450701c0e559404c20614000422400703100010b024025420040050030003000c0d80e05582600c00003528540d00d9404028155500398101c0c503c2c242031070602030405404d5000b902e00c4610540308041d00d5907031407000c01300320b0040056160100c0d4026200078281c0d80c9030814a02c450740803a0a0350b0820144074821400e90b40540c0c40985143d100b102080385a45000bd00c04205891074038000c40b10900d0408020701c181b1407402003500c03586514108956441c0141c0130303526803d85d01030154008600381a064 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 843119361 1250 843118111 843118181
    0x180e010e091216020f060403061e0e07181a180106020d140901080c0d18020a080f0703061a2107060f0f1b0b04051e210c01 54
    0x1140303851080b00394000784031020000f40c680b40d12402907a8500810207408010042094060003030b04038904000100104155000b46840780142d00d2080504000d1500c80c032044480d100f81c80c0586402804041c400740d0320b1740102c6100104180c00100c0d21035010041d101440ba580421603500201c01c007004040c0d130030006030880c12194507801740c6091284140040e203081c6000d0070041c1c480c4074200300304010341d070040c50302d10740285080c0310361030814503244480340440b243c55418100c5003015903518405c628007a0a101d000e00b011402034420240c1c4a0034440c0d07150300c1d07404024103140d1660b6002d448041c040c0c6824240ca10001d2501c002c4481446c44890300120f149241c000d980503a200100b9414002e68400701c01410355500c000807420710708030407a00540044110b400d000006080c04010030500702c800f9004501410162085c03c2c094600100c0b2a00820000c94207908001c3c0c0d5210000c3d41000f1400800b61446d031071031350380c0c512011004d0047c2880c15482840c1d09200c0e065065960303001401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 843120611 1250 843119361 843119371
    0x3160308070206150904050f010f0605040e0c06090d050c100906030e07050927030a0216060311030103030e01020f0d030b031e0c0402070201050715140c0a020706180e010e 75
    0x10a5040e4a51407000c0ba1542da040311400515a240e801c2c40442d400c1aa82c4075134020b001d9815140c041c0103a43d50b150035580c13002d40d4a06900e84412050185203001e200d2482003500d038600800f9a8409000880c4440c0a0806101e11850207820442c00b8000c1c01c1c490342040311300080100d8101c0c080e440018001c0b40e81c078014400068a4409006840040040c2820586d400148030020558510403d03144254900b0b4000c11030503a101028a40005c0400151031303649044e4001e001640094080e44940e00201e034031207010541807840102074044818101da05583c1c041c5401c0c00742d00130060050b40380c1a82d00304020700b42e01c44e40e51003514265041e8001490544114281c411742c0a800051440e0740884031170000c03441d00001c15a1003245010303401003040d04d2040c10458202505515442c0410b03081000c11880603484401100c115068200c006a04c00d030261101c030308003182c0d860025610b640034098241404034064248008002d450744190081030003181c03c81c52583c44500c001d40050302510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 843121861 1250 843120611 843120617
    0xb0a091d0402100c0834051506030712060609050f24012001050103050705030d17070e030703120f1e121d031206030703030f3005100801050c0426031603 67
    0x1c1070b1460380446c10f005003c4d51707000300c020107801c54090340700040950051716a80d0b05204220340010200d4140c46005911400307040001006031920704c842c002d40780010554515101e480007041180002c11000321030215402c18050b0410011000507944051407012074032200c0000300000d800c503001500600d050fa40f0400c00c3d03800c017a43d0b0314203040d641d4410f004070901040e040000c1c00301c0d02007002d440540c0700003c1d01d082c8034417075030f20404a030a082e10f5800944880b0030034445900c065410003c0b04041d4116403504400c0c0c0041d81401c40742010b4880c800000300891030900440d02c661941040290071124514100030b601e8110109680c1d500414411241c038003d41e0004907640341c081400000c0300d400d0f8403072002c4c1c055594012030754800c0c0100c0b01d02c0c5401c070a1007459454070704801c5d0845021491000000d05041c00b0b090240b400d140d07a84075054607030404040241c8410140241c40c2142c45904281c005955240c6004011400c1b8106c41c48451001142940c03010031603400845001d40aa1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 843123111 1250 843121861 843121927
    0x912100f050618060406090203040515072102030619081b060408150a0e0303181501031511040b031018020705120702010210060b0a091d0402100c08 65
    0x1039000310546808030b510315403100c04401d030741c840c41d03841404041e03200800a10010b0304945501106007281c00c02d0381c0980e91b075441030343c901c0c074031004c1c030303901250855920b080000d00c4180103860b1765580111038055110f00e0740c0100128095860f01a08090001260501d0081c80340d00c0300c2e81e603030740c440e44507040502c100e0b41d0a03070042310360a21504980c2540c040f03002428280745030000341101414040c04540c03501d5601d01c483c1340845824400385000d01c18046044000c611000c190758a0085141000002c000300d14004200085402279401d506040d82040414520240032081d11a03014960040c0e03008100001044503410b4031400200940d40c20f403800040c04030b4002da04000324040c040b0018081d03032081402e03085404c5101d0203413494500c144101c034401c4900a0411080d0303000390707005005d00403000c964462140e400404000140a414240c100da2442546403d914104003074000f07400bc1c1d4040005a0280f481441400045600540c030304c1c0c1d40321049170210111191040c0148040c0b01c1d0b603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 843124361 1250 843123111 843123131
    0xd0311070b091023040b04060f030510150e030f010209030f030711040902150d0e0c03010e060402060f12010e010609151d0406090603060b0f1002030a03020f091210 72
    0x1800075600b40400191060b0103400003108103640b00341c0042600a1543c2036012041c0802d9101d000400c040c242003e40d09840d42d16050000c0c2107003a048030781e1828142001c0811080100568155080b516545160240300022a00a484803043e01c0360440d0940101082c5c400780400540041044c0c0c4016412680c0031034691003583e440380120400200807002c50070080d100c5241a410451086000400e4175840c084458009005170303200882aa07038103a102e130703000400400300b4000e0459000d01a8000e002115940300b03103035203035240180300921424012465030070003e80714040e55113444400910600958448105480a000c04d105140000d10404800f007100b045541c0d00120400044e200c4c010300c64901142002e00c420b0980c0280c0c6c009956140c00900700500e40520002103024074000102d10300c1180c05d1009003165409940c0c01444000e900705d46040d4004200c5021091528005881d00c1107200c04040c4c1c0e10071140201d84c0883d0344110399030018404955051903660303138802002030320703070b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 843125611 1250 843124361 843124379
    0x1e040e060604060801060e040612050a12031505090c090d030c0510110406030c030b0618040605060703170c160b1e01140103091406010f0f14030606130b0d031107 71
    0x95003c2d03900040c181000400005000d04003007450b8000003440032410761389410b01600603640c003410580b4640d00400388203090011310000401040c0081c5810300c030742000d082808880205d0380c0300780e9009540700400283d64194260599000ea00300401c1090218594100244440440302d070a9801c0d00804183d0340014400c0c0c03042034030400c2032042040c20030740752680980044c510a5045003e143d211207506c901030b500d40004040c0e2502850907504400728050501c0221060b43e00306900030740d401c102d44400300c0e40000d050003150180c03004e076115030741d00d81e40703070312990300814507a807560040e40d070200010045880042c51145054040e8005e2200c0c0c540c0442d00400c20038401c4001003801400c0e04003203035120703403c00b42605d802046c403044540c40c200c0185187c007000340e21241c03c212078844103001d09440205904002c0c204034102c09100c24403200000c1e02c0d00b0010300781920881842c0498641040c0b19001807540c0c3d84000c0200506400320308006c3e001d0f54603480307811003e0050000210b01100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 843126861 1250 843125611 843125617
    0xb040507060c0507120317040c2d0b0a0903120c0b13020f060a03090b010b0310050604080606061308250f08060c0706021213150501060c171e040e0606 66
    0x203004002440320174500300105c41003203520441a400c002011082c0380c1d21800050415001300d02c520100b8040615186180c80b410070a83c0303c3c0310074500f603c140404602c214070740850503102e4000110340e943d07c03000c2c03081d1007140c0103903c02170107454601c3c041420030350080710031600117000e91a400c15541d10441e07107940a0308030440096201c04100400d2500b07040c000c0c0039002c0100325040003c0ea41d240354880d1106208240e11a00c0a51400010800c3e200006001540108010f854043c00c1c5410610082e844450003040940141c40104a060341c1e05d400d0707036103c4010030964058440c42620400c90200022019800041d01501204002001c101e034a054908a41038a00901a60344400348022002e503c9140141c5480750203002d141d003502d005405842c0103220342400c0040103007181c540301072185131004440b02d0a6140070010001c1740c2d008100020042e80c4a4030251048002841101c0d8600a0301c094602030034540c00c030038900c0d46140009105440032003070741c100c03141d40b00c000b00079141c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 843128111 1250 843126861 843126863
    0x90601080f0f04060e3004030816030c0213051e09101509050f1603060605090105071a0c280f0f0207031b0e0f16050c100204030b040507060c 62
    0x424000080036400780e040c000340c00511510000c05c0c1c41d06a0345007149040d107110032000103e202211900c06500d17140b00d09583c000001c0c0d00a138141403542e00c07042418092070616407007c400c1c003d198010113125a07841d040d81c0303a0041540c040981d1100800d07008040494101c40504400e01e9100c17a03c48011209600c1100c4d0f42d4001c000d409d0721190bc0c0000313040100711078440e51180c49000b15045040b406040d1081103d0103071445a0720341034410b107203c10180524081403510b089004e02049034040100c944500c07003801c15699030070b5030b840d00307940800280360002a03000c480c400780940458444014000003800c407000b98004072120340b1103042d00078038860910108541c6100c0d11609800780c4401d40e554025401610f00c0641d694984441c0880d07640c1004111281d4035100340318584c0c0e11001140c0002d5a144582c0d0586001c05000c420a43c8481e0504280400482c0c05e501c006000c10000e8840a1424010754940784d40c2e15040305211001d0b1403c03110350050b00c101040c21807046540b4600d903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 843129361 1250 843128111 843128131
    0xf0b040b100e040f0c02060415090203211e0408010e15070e210c090106030b131a031c08010b0703080a050a0b03030315091503030417011b02060609060108 68
    0x28420000c0195140501c1c180c1080d0415204e03e00c01c0c142d0b400b0341c416000880010b4002d00803500e401c0c9000c9280405200314091510b02d0170220401503140002c1c003040c8030b6807051044c0501c074092000e585203405841c068002c2c0c4004800701d0403004040c40e010f03108544d400c100070700c09a030034580413a03103541558040e080090f001c4000034a01c071f031141008541030300e00500040c0ca10308a00c200004164210364080d03a156004e110300e000b00b030030a12405801080030b440c0800c10a046440024000888241c80513503040d2035003116000c418000190f60140580101290520003100c55820f03000f000c1000320202040e0f02100002d03091319040c040b2005503505a88800e441e40d9800130070b01c01060040c220580301c503528041e060568504200441c0645140359407a240c0707108100400500290080071000c488210540d16070068900106540544d510180c02c3c5108600c03400b8010300400380d4030606c203150300300c200281184c00c1d008110180208802e5a0110140da44c0c440192a82a016a200154 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 843130611 1250 843129361 843129379
    0x9010b0a3606051206060f0405010506161e05100507020106080316111305060a090c02190f02100f0e03010b1807020a0204050c0909090d0531090f0b040b 67
    0x91161400716034821884a2001403000d445002243c032400481324207103030070fa001c082404010704d01a075518500b120201d03002d106541c1010040f038168000e030018002c403404402d4140e420000711b4020002c00755010700340d100e110304070790034902e5031118002662003c0a1030507001c107030000e01c1809121f081d0780c007440c019850303c0c04000f210020300c440340000fa60000383c007405041c002e540d080030400304440000e80100d891308000c0c007000210406544100206803800c0100d413191900071600300e20204060802103452001c03030a0900654815140c02075000c11074805107001780c3c1d0820002c500300c04095489401c00d0030441c05060886004004095200040181d61241d48500c04003250340320f281441038641c80308043d070110f41550420b8584540b00b480100310041c55041907001164803101c2c100007001440101c44e0b01900d42c0c80344c1c0d100514400b0f0100004c269203001202401454142d0500c01010140c1e04e10050004001d03d288055105d418031002c402c0c1d40c9014060307214080c000800f400c0d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 843131861 1250 843130611 843130679
    0x30f050411010c05030d0c0f030b03070510030b03100f15150c0f080903070305010b120327010504030f030314060f0307290f03010311120705010f0c0b09010b0a 70
    0x40c0106510b03c044401e44010030010400a40d00c0c020611100020b440c0c0c4500c9400781400501a00c01c3c401d841d501940c0f0245041101d503a9098003260380055a050014171585148003003810b010300b80300b01c060351504184140300d112901d40e10840015803814a84502103443d89400c200121341015201c0008060200220104c0c0284a25040480c401c03d140c80c0380100b19000700781089456403043e18141d54980c004c0b001c44c14102080d42040d210703580a149080c0301104500c00d0784a0000300c41001c402104504911030f401081207501441d08068031003802c0e401450000c1c0035040c100c54201ca20802e100c0803a02d0703030400b8800009034800040c05480c40304d041a1466401005410b41c0d8114001d001c80c404200160b014001c0080e9421040c04955941c10340c04c0031000201980811802003000340803026541d40089281c0099403001d01e020040b142014008482c480345c03221002d0014103e0030203002d2130400560006100b018151a0a4182540c80c80c0440d9040a1700c070142c1c0011100c110300c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 843133111 1250 843131861 843131867
    0x708090a0317060a0e132303030c220b0706062102300304030516050d03030f14010b09010201060b0a0c0b0c3001050319060207060902091501030f05041101 68
    0x5500a901400e510110360340c585c1001641902518202809032403201d0040c280b252040d03030644c2030a101805410b802116404191b47c82c4802000111410340100d014200c00309042c41d03003508161104240e4003003503140c010800084d400302c0d0044480518007840024020880d07064030a0404030410a420020aa6000d0100300d8040c08591218098060219011078803400600758214400c00000c0d074807681180390182c6080302c2022450306101440d001005903076100e00c0310b800c1050f1b00d858003280c25204140307818050540d042c05040c0300040c0e40008114031802d00090107822800f640244203181e40c032200341c210d51190307015182c002003075900300002203121618085d4120354480005440c00c0700259401c500b822001549261800c1e040004150300e801a0003040d024000840203011204c4030051a010701da620050010541600442c8510501185a0281e12096005850709483d4034110045813211504a2120381c0880e28060f00048409513921542e4400d43d444114910b8112603d8015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 843134361 1250 843133111 843133157
    0x5060903070f06170f010e04080c0106050a180b01231803011401231e19030302010f0f0e0c0607080d0603051c0c0b0f100504060803030708090a03 64
    0x426014400c1020000303010040c403080b000245800e59501103044541d000040318001c01030900a00c42880d0b40040c4a40d403c10170005130040c1d40002c0d082da4840c4584450f601400845d8030075940305030001c800066404a03030720141011848400c04100d02800c14006480b42440d6030310515030a401e81c58442001b402c104d0042078000680d031982d00b4012200c0c40000e09540b6203c881640c98100e4030010003480e600e40a544031400010300f4145550f4840b10080303040d100341951003004807560b001c5c1c0d00c5000d2312070100ca945106281c40c1c0a000705502c0b800c0190107170032502805c461340d81c030385180107295440501c14036441c2e0883c000544100000c140400400d40c04c010026102d082040084070824500ea220300d02c000c51168000d041184040703043c003104071000e9101d40c000d11a4088000c80001d010382c41050780302d2111400c0d105c01e034591640c0c10300c0c034070041e130400c941140c50506d0100d04102c0000c0070354440d440741d40c0c50005a40c1e810103034603125202c6900c020007166500c241200c00d44a00354003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 843135611 1250 843134361 843134377
    0x806090604060f0f062603030c1210050d0606031e050703060f022101080105060904030e100908070e010905070c030c0602090d0f0609060c09050a0e1e10060207050f0a0506 75
    0x10106204410800d030b10101c9019501241c6c4c5034801412030519111912540654604e00710b000d54103602e04034007820031510940303044c03072002c800d2140018001c05903615464081e003005050b0019013962481c10600429050000740c42000300c481200000640f80c00340d0782c6141d40d0201c01703001070501d540c3d90500580394040b00901c280c2d07028069071500c0701da0046000101400103200d02c00d954900406182115000b9019600554210b410000425080089103407040b4040e82c06031366100a4010440700300356103406c1a4054051207500181001da43c240083c143c41035050100401e03194500c05a0b50106118401008140303d20210004100030b680600300300000901482014401c0b1398882110605001084400c155100303241c5050003480d229025050301a420035041d42c0f402c00c00002c9098400d8482c0d040341803403880006075000e031120040322041e101c0000c9450b450500c95482110894940500f5005100b04040002c99141000c00322000315406007180300800c0c244020301000c0e07404820 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 843136861 1250 843135611 843135641
    0xc0a050a0e0903090301092102070b09060315040e010204062d11010609020d020a170c031303050c01020d0c0f05120106080c120109020a03151d100816030606080609060406 75
    0xc0e0b4038503031400e000300700406216907540740ca517040103482150284123071003041046501c45181840b00a0000003111100311040f21280e0f160b58440e0120040650340c14030f22504681044032074418484150041d1040d0344150701e5049440c14020014100407401d6007402220b01e94441e400341070345025100c2c26845a03088800420cd60b074031150701d80d00b41d034001d0760588100c5a000680701c0c1040e62010b080398010800304a07610160515402e94030b96404050144181c0c018101410410540100c040f2403120103210025902c9518605400f4000d10411030403001244141010803050f40c03181c070803100d0030014400d030581070780d082601c1100e00e150300509003048030008004001c806082e2040240c020441d0410140e44c0e02034001004043d01c001c0e1208008614040308280004e420090383c1c2c80d102c1c0b0719004289003940c0e90701428206280950300403842c078000c40e0071804007107601c2c9200304141c90043d002844003075503070f61240c0c2e03880c00c003180c9614080d0003003030110300042c1060b0054480820804 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 843138111 1250 843136861 843136867
    0x609030928080601090b011d01030c05070611070c17031204030e03100e0705040902090a020d2901080c0a0f08060a090e01021c06050105030a0213030803090109050c0a050a0e0903 78
    0xc2001d07180103030000c03110303075000303000401c41034a40d8012421031400c2841d01440c1d00c1116176000c10340d031650014103814140c45002c01c040c01407180090341c5d80182c006001307002c0005070784212030355580050015a01e10f401002c010888070000301828542c0c1308030300015482e1412241440000d21400b030411410040910b0110007070b80d500300103400c00042250030000b111006140c4580c41d21445600041c0540c0c2010920341c0581c0d651008154880030851015030394145680c240c0c002000312101210260b515520b03038a9a03040e00c5160888410420b807907905454680ca52295514083e0010080018182450b02d03e0313064415042c2c0e0390071101c060f20110b076881d11641d00500b83c0d030100000c040310ba9070208508012164020b485075004449a40801c201420301000800d58440100b5183c0901d0f0001003901000b1300b1175035602e00070768000d01c0d0144c60341807045109e03018092100054a59114a000211841c94000d500a0440300010100850289441000c054021004180410a010074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 843139361 1250 843138111 843138169
    0x110102030f1603020705091e090d1413210b0a05010506040603020c0c0604061d06040e22200111010501050108150102010b19080d050a0906030b030322080f06090309 72
    0x21502c010b0041230441030b003900346000641141a043c0d40180540c0061388400c0383c0600180c0c11031074281220070700d00302450362251304403410342144060340d2205c4150f101a440669501e0003010007a40303403078410144000309844152030310042c1c0e0000e000e502d5211000b000100201801380e802011882001d205071003c00c1d48070000038145800c80c1d4050008174500b1110035050b845c003501d003031030402c000712416810581007601101558400400c3c2c03003c0c0492032007415503009080c007501b00c5400d41c0700c004170395000c401074007540841064101040c0400e40c0c915034090a0201800340c24160740d010384d280c0c0819a1344800c604588500d034180789055568079400c010940d211905124400685070300240109460a450149001d6a800703101d800c020701400386040480d44030303155204035125890042204481a00028158400c140d20407029000114000028100b040711460844107990251844d0155507210142c403034404980107003241c2c000300030071401e516050884102c084003503c030b142090010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 843140611 1250 843139361 843139369
    0x6070f0c03050f0d0b1e10170a091a0115030501080307030206061011070308030103110a030f0f031e0c0519111e090a0b0f0a03050c010c050c060d09110102030f1603020705 75
    0x8001c200b1083c0040798100b9103450910303504102c00e4604500d030104c0c15179038107200820a18009040d810101d500d44844c4d8090015000c11000d85162851070bc01140d6914440526601002002c4001203402d000000801d04000f005031181c581d010f40180c403030f95039187e041100c05c035280141c890601040c040c00100009040200601035407045040d0360703495040d4200039000c076009031407051042c0400042400050741a641038542c2d198048002943c03442c0c58035080d0340001f900202c402d0005052019006201e600000140d0440e020b0025680010482004c512200d9082900a00380c2464442074003003a0034840181810b4603d4407082900e00d100c0c440001e0761541050300c081001c1c03070721803080c541c1600d0311004020f00c0c0d0200722246103a540c6181e8906440f46010401c0754184080e50b80352a043c00f000b40101d20380841e0040045a561040042c01801840004803d0740c408440310400344403540000120352a003108920864100aaaa445c001301108814411011402444000100c83e11 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 843141861 1250 843140611 843140629
    0x3030e1c0503040506150a03260c16090e0304050f030120030106080a0b010c120c05070803040306050a0605010203030412090302031501090e0106060e0d02030a0c03030206070f0c03050f0d0b 83
    0x4055407100e99a05250420625042c00603250f1402c100e19100b0711040c079510145280f044940c0001000d0140d0b55004040c419407101c141341c100b401000144100755002d01103240440086420b44450b1440e8a070071222017100c24588000c0031590040105000c1498110a10300c14030741c00030004100c1d00c60000060340751103804182c001c08a107003c8014003416810041042e4080d9000400300320001242d000203210545408024001c07140c0000309211151143c1039040401d500513044070340003aa1124101d40e6a0b01ca40305c1602c0f080e19010105641100e540034000031188141d00071401e5846a0f04e0721907840313070f5900040092080c10000000181c170305010b081c0e200c2c001141146210740c9803034118000d1319156005402e803070749402014800d040c0c000c1c03400940c0c918280d600f01003014a40c0302280c0350034180d0740060407030b00004000104256002400600ca4121665507034842a0440c00c250b40b032400d40d0b0340040106000b485803c4420405401810a804c015000880c284140501081c0d150b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 843143111 1250 843141861 843141913
    0x4060e0310020c0c150c0d1b0f0302060711030c0d0810150302090a06020105060d0803090705030102030c0705010b0904030903020603073501120b150103020702030f150601090e0403030e 81
    0x5004a9004c034042d1074103420483c40c0c01810040b413031a090001c1e00c200c2d1185032007041c1c60103009040e00c40c442d09040407451220190780c42080c0d5840900b445c100690790701c1c0300311401c000140b600e1301a6000c0c1c18000c001c3e5001c3c0c0004034001c0003140000f605c09d03205e900c1c5c02410506c1c491102c2030000b03060121007441d0714881d450303624016607038020b04e82804101030b5560003d0042d03a0404013403225684501000c020384036000303150591a80c81d001c80b9141842c5240d848594958008814010311141e90001030505511a0008000c041889824003003065000c4402801044c00c02c0d0b41000503091038070055030711002c54944240007070b48038a400c82112105071302c4a40034038070301c0d000030000b41ca401007024003411703a00181e51003a03503080c1c1c0c0b59510b411000b0041c10250355100c0c00165031303900980644041c80d81c01402d554140b50540d403210350f6000c4100000141c1025a40890700650150340403074141c0d1003180700480d0341c2d80e55460643c054000c80a06546c5c0d44a06048215a990200e40c030980e0f035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 843144361 1250 843143111 843143113
    0xa0905100902030c01050c100b010315060203041404050403050a0804230c010809031c15030203070e0f070305160f0903290108010606090e0c09042c01050c04060e0310020c 75
    0x841d03280c0181890000800012418090100410040b013007001418005401d29050b000c24401c00c280012406400c174002050680c0340d0b00340d0046259500480a07100740c51903010071801042813402004281c030415103000c0d021031070401a014041380308400c2c039907100e40928003201d4199801c3d81d84202060055210298541001403240c1d0650392000c090354011030700320700850404a031655014100010324610450040e0f0351142c2c2410901c011021000440c1c0013003d40300b45640d1013078290300d048000c4034000b201c210020001150107010307125403401103c0244406600f1074a0010540b80404402031a409000c0b84c1900000051100b035640c6200d00640705081403040582d04856130030120603008000c1507410701c1000d004003540103100c28101c617510b402038007039900c17501c0c8014110720501035019001801d06c15006501452050610030380e0203d25002802c13041c00b021401d0072030b403003039406025444003000b082100c24820389040c41502030050540320049400c0d000601244d10828500001d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 843145611 1250 843144361 843144371
    0xc0f060c02040e06040525080106060c050f0d0806040f0b09150102010c02070510050f1201090207031101090c0b0a051606090c150f0f120f1b09030b0c030a090510 71
    0x440c20203001c3e070110021020014481418a5500c44d501c407030081003881d1f6440354100382c901e44a031030340607020002c02240000b005102d03144c00000f044a00e00010940300c078420024144446079002a00e40c00004103513446043c2c81d02d440302000042d00342c540741d40b420240c94100c17140c419a103040c201c5001d5007008248000b031000c5140060b0039500100400c0c0290341016408200503140e45011007880c090318602550396601e50001d01c461402151201c07500d044a110001c9150900c55000f005014002c1d114880d0228525001c1401d0741c011400003441460314642c208070704d9001c0005004d076581c1c0360400c182410351040280c1d00c102d000e20400c0d1129a1038100510030320014204c11006071041e12014501c5840d12003000d82104442d11001c0704200e5008200c955182c81142e44040580300d042040c014100541d500300003420001d503d0f107070785207080340384c0c3c0c108140036101184c12072b50710004c6416650349040b20051643c10041022014544510207400000c505025603280c44800e040c0001d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 843146861 1250 843145611 843145613
    0x5190510170c030601050f0d0c0f03060f0506031e120a03140112030f0c06180803040302010f061802071106070b0f010806063102180922030c0c0f060c 66
    0x1d1001080030881c000d942000c10495015200864010b0648900356110b003c200524400700b001500a1100a031101180c90070114841078064403000849009001c04d1080c0c1080092510032504190f95665044d84482511182d451030b40045481c4009c4281c140d0f402c01251601212140d0301803100c0c00c2c00a035803881c11610b80d1400740040341c058250000d84c036248001681d4080d003450310704e01180050050410b030f400104180c2d03400c41500c400c1c031084030000c190020b25004216800645040f805942002010f0840f28214420351003240e1303141c945d50b0360002d9a40241d00080d0b0240b4400e480b6540d9003105c1414980387c00300148541882003403800c00d00d1601c4002418280c9040c2c0101205802031420301c6001c2d41c03411208856140450552004183c2c41e00b02039601041c000180616940003103200d8008400e91100a05070f14410380704e011503031341c46c541c0a416040c1d160400890300c9040b40d411001092103070704003442b0b103171003038114091160f101d87c0101c0d00210983e000000250364450120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 843148111 1250 843146861 843146879
    0x162720040609170d08090708030d0b090a050c031f09020c0706120507050d0c05160b0105040c112104090207051c18050423011d060607120305190510 65
    0x10300400d00382540f1507241d004211019142c0300e0700d1200604020b400300110345008018000c560080c907031802202d6882d45c0021104001c0c14620300780c0fa12511603800000d04a50144c01658414200c5005180c80d65484000508400b000745c082c0d81c1c0e02101130780c804211031280e84000e140450044008010f0700e4070303000c0d000b00040000108101c40b1810681800502a0485d00385ca140c4c4060038004a0001d40902085038a07000b00b9106200c429041000c1206200785030341c03443d041c1c850590f810701a99810003000c0d6100d0101a150444035407001c07400e00b03000181e8120810640b241d01c1000f80c6002d03a41c032110410b9030405042500e942e044201c030003003c115503d07840200076100d400c141d25031072092508220380000610441d405151503a280f000d4142c01da6109410420928400000550319046920031354a101155003214520002c0416540d01e400b505850301203911160a0b002d078082100c0c210040c2401814609540c0000100010000700034000c080c45501c10103804007144c1c0c40c104c414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 843149361 1250 843148111 843148127
    0x1c170c0a1a0c180d0311010207060b0307171209120708010c0f030c020c0f1306090e07050619260c090a05010f090e130807050f1627200406 61
    0xd00206001046400d10342c00f0340585071820305008481080a2141c1400d05540005d024020441e01d075100140480420005a0080b0b0030040c0c20b4080b2001691120211a071005508800b100580d219019480b05442e00800500c111100605070012644011034010301d44000c07a001044d4594650001070710b03041d4072100300d4050280c646402c0c80689901100a5100d5520524045c0121142c480310b50f50b5407241080080305502c00d0104102c0180c1d207002560080c520030340301c3e8031030740224000000c00b07203807038020307500650310250800c04440c01340c00e402e5030803400440001c8002e8591244501c015a9680030b210311403404200100e50300c00c0140e0400c25006d100d0340005050080394411244103544c889854003d0b039074681c42905440d144d200d048103c2a0b4250ad006100d208002088400c00002041c2c11009030714880866540b40341418800c01c803001c0b1070040d030b0108030501020b080d20104441c51139000a00d00c2e000003a02c00181030202c01094503000000740f105400041c01c002e411380c840c10f1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 843150611 1250 843149361 843149371
    0x1e15040e181609050a0b10050c060a02070803010b0c0703050d0903060516140f07080a0314071b12050d0501090b0315041a040c0902040f030c051c170c0a1a 68
    0x2e41420400224000c01c0829980555a5500c0e036400000780c1754a400d520260703480000410304001c10b0b08030b0b00e0051182d4040740603900c640c05070340c010503140300b45030095480d010783c0b00c0c003800d040d42c0c00d0407620101604116080760303961040000010201e10140641d0004242c1644d800e40038505506008d815540c014100402c030094104151945e181d01c511501c2c02c0000c3c5420440d69508200d1800c3e41d0303401040009040810001014200e054144e4820b180485050711204150350710301a0039a1082100c101c03910002070303c1d07450364000802102c1c1c141d40c00c444038100070741040202c0e6410344c11204240c000c00b41c0150b65480060040c502005040d400010800d9031180501c1d03c1e41d5040c091030b80301b50f9081e18100002010804100280020401400175000704544441c0e66481c0401503050601c0241d03410310a034a8045840d040c01d081003444060300807040312480d080d03a5605004101c000340c4001c264a414082c1600030403061001540b0640581c09054041600c01e124048120f00030706 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 843151861 1250 843150611 843150613
    0xd0513020310020a0e0a170d09082509020c0c01090b1314010e06070c091802220b060a08061011060f0405160b13050105091e15040e18 59
    0x10650005075400912091031410203200540c8801040c002900d20005011110b64480084400403861070521040004646d0741311040302d503a1040300700d081d50f40c61168042c00b00a0380003800c0310760f185030207410382c4006100000c500900d07450303461450408a82007007420b000c40d908900c501c1c00d40382d82e00982403005046885040c40c5880001880c10585c16501d00c0f41500c2e1101409138120b0381d0b0700440761407102c900044e14003661800300340b0300b400903220305001d44d102e1b0b07514240c10489051544801c0800c059406800c00070952840c1069007002c07400c0703580c5080260b032151608840c548a1801415848045445504807800c21004100c804d042c10041c0000b00028010407000c0ca0714009500b641144e04004540c00345e89844c1026420580c0388244022680c03042d006c0020000070301c00082000004202d1000303442a01c03800110b8541c8510140d10703500000c0c4550b10200c502001942407481c0e1001040c007184d147c0707000b03081017154000b540718490f600350035030030014600ca88200d515140343c0311030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 843153111 1250 843151861 843151891
    0x10306140d02090606120c0304060509070609090e07030c092f030c160501061d0708040507050f0d0c0609030b100b03040650060f01110a170d05 63
    0x203004103400c8118044080d00c12048400490070383e46940c0d040385d2010400c0c04c00a0ba051803d001ea40950784d01c2075504488443c60301c000105480070114004054840e550350302d1058910300078012010b0020401480082d008010780080059228002c0c0c60060000c024045001c50110f044014903400f45102003040c4812500d18030103540280003181d600003400b000d09030f1249802010346004203905c5030700400742e42c070780b8001140c800042c103541d00e030340300704a00011020390351844115002e0a081e24000e01d01d50100200384407510340007068864800c030103401c24108038103e0b214041d126465610100120300b280000340284807102030400c0c0d122180c3c4e14842521b030700c0c18003c500e607480005c001801140c1c1d982e0780c081402507140c0a05600c604d42c01510300c6100e8070300c85140002c903503000d0351000d4006150075100b0000706900a040c803542000784464156440710b8015a5061803080c18909980a8038642030009245040c20100354520f0072441d80c1c64020600c10f0204603803000d00f4143c0607011003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 843154361 1250 843153111 843153149
    0x9013c0603080702060708070c0b030a0e030909161202071203060501052803090f03090501020c0a051809031201060906021009230f07120204050117191b090902010306 73
    0x70074220f07540b01d03905445c410355401c8a4141800b00d8001c960b002016500051000644503c110010b5030045900060800143c0ca07640c401c56900e12500104c40d030401c0e418030005940800041041c05100018140741030301d500300200034400c9a011000c2115a00301c007d04103502145d042c440d5102038a004c3c20003034544183e00094010048804c0a04211000d800481420f010b12903000143c0c51903000c0c1f0794140c400c805150240004809015083c014412078102d401c5a1a000c6005405c0720030140c60760200d901007a03020035244800424603580d6100400101e10401c102e2100140200341c5a5032b5007030039600304a030003401c001030b4801c48070035642014482c2010819508403007600e1070558001c6a059121320900e1400c1010300303140c800c0d10b801202400504881d10f60909840c85100701c404100d61380e25810150309038401060170b2071807035100d05c18005459898004c030744103d90007640c3c2c05401c140c40e40c40804803081036030002c09403d901c40e0602021540c26024180180c1451000c941c544081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 843155611 1250 843154361 843154373
    0xf110d060f120317060301060302040c02061b2b090b09070f080d090501050a2c0909010606090e150a060f0f021f020d0b031902030f060105010c0b09013c0603 69
    0x70343c41c0e440300130b8016100401e071159070175801000116406032090000758030400001e0345a5074100c605880c41c5400d851004440c0030410201d500003854481c658060803030007440001e00c0310720303d8940441c10340c3e1030400d1000720303000401c40c920401d080c5000740b20060500a80c0c1d43e030b10b40d1320791141080744d105000020031190414120000d440302868010b444400d1403c08a071088140d91802d50f00c060b1010035200d0310000c00d240c2003c43d07002501c0041254841642d5a401c803840c0e4419100003c0c59030506003c1060401c00240d0805400131103441d005040000003242d41865600c0500852841c1c10440e4150b40c11640403545151280090500362000d100b8540061901004d58040b04d98001200c003401e0820380d000450780d001c041d0031a080c0d02060b020019217440e9000040c3d01c607215030012808460b40c001500c074142c49043e5581c200f64a1182d0381d104803c50f02900f00240340d529520f0354210520180e0100c80c2c03007230f81000d5524081100311103003070799494a1032920201a090500910124039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 843156861 1250 843155611 843155627
    0x1707020109051012060801050603010b1e01050a050f0307090e130b280e03070c12050c04090f050d0e130902011704060219020304050901060e0904060f110d060f1203 72
    0x10240e035050788102903035200b1140c0c44113011001c80c50601e04480070440c0300b81580300300d100c2c080a500811107400fa01040240c1d0070000803150ba071020601d0000b048035481440a4103602d41c03035040032410301606100c00e180c0340e007084555600107411210100130000e90f9a50440e0018103401c1403202500c92901d070042025002001c4003407000d04000611249400c00c40442c41ca1a030000c0108002c0118031303005600c9502c244800d5507412000c44001c21411a50065901999441801084111903080c02d200c054900580c06680c3d05401c9488031012a0741486200d030f100c1142d42e034220030a02d11311704206140c02c8401f0b072421154a40030b0400c0040c0d800c507400040425010342404650f81e110715080000c3e01c0f41c902c01c9072054407542801256a90004083c100b50307802107603c060140c8e02c070305080325000003103030303003580c0c850142400b00e40405c207507074042c1d56521415030000c1100c40554041c11900d80c4100d1007070415990790103040100121400e440000b51040205000d403500c0c46803001841c1c20303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 843158111 1250 843156861 843156869
    0x8040b07090b070b060f18251b0c0f0e190b0109030f0203071a070302150c0d0e0c03011509050a0b01021203070e03070e181f0e0a08070f1707020109 65
    0x750f102000c21701a070b5601191a1086a004201d4a5010003185100c03040e0a4252190348c2c00c1660154050226480c51440c1401e0301c90700e941300c60000c04032801c41e02d048100c00301f05644e038440340e0102140e590991081031000c0c01048509201c603040c00d240c403414280040880030085460884002c0342c603a0700410500450350401c0c1c3c501e15803c01030002a0500403150f20041b00c1012001e060003440c02c00320041e100440c001c0d002e444100464070400314216800300d0701e40160b0001003110780c140c0100d65110840103107a14040741c0900f24008003013421a440071403103007a03400a1000c02c22001c0c40f64090b05620030600c0c002808000c2121002035500c0c8007102c14043c00c01030200004031118170401180c45440343c024101c400702c0d40e480340030700780c00c0c4d40c1907461140a00e141001705a00c0d410000e100102c00c8038901c1040c141000c035400341401084841213a503000c0c001c050302d00d0003049142019108440c007407100700c50813061a2030b0460342c0350848034003d05800c0341400101c2c0507030303041440c407000c035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 843159361 1250 843158111 843158123
    0x12090f0111220807060314070c02030d2001050f091006080303060d08120a050a1d060106110c040501170c090114061605010e0606041d0303011e1508040b07090b07 71
    0x140030288400600d83c10a0f0010f10410200003500350780740e00007403c10100a01241125210345200329404c91207410081e40641c0401c160011440c0b1808103072080e00001112044801805e560b05800c0d50b0058410402000e042403d010303100b401480002007003803022404000031440e03d144281c82c0d000c002c00f83c80c8a8035010340d4000510a9903411030740821801d491143c660300c0c00d001040d0041070244c0c0d446400a10301540b4121542074240c4d101450050313140200b20982c0303024421586600200041040c90140e0400703800c4a0b1035501416000e407203680c410341c01c44650304072040d20300450070360780607c142402e000400c0380c4094103410115580007074070042e59410203080c8030710b501e02c3c070320a005026600c0c03c269540341104c00304135140503400c211018072070986412040500c01014032440801e6403c01c100400064a6441c0d0300b05082c2c400801d01e080040e0348003521050020b006031902d0218207500d080004100394420910740c03011507801d15030304260811031500b2084c014054000c0c86 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 843160611 1250 843159361 843159397
    0x10081506040c0c080724090f1103160807051504062316110f030601270e030c0607090b03010f06030902010905120d02010f0e1515040212090f0111 64
    0x10144140c03c2d000c12140c0140196680d45424540b0311640a40d818052000c0c40c40101810310280c401d0181101e4039070003494908004941b602c6112802190b81c0d401c0b0751521415403d904401442410754001b009480b01501c0700c10710b8403050104141640340c20070030030401004103210040e0031001102d44403400c0e000400c0c03007285e00001c0500a100e81a919110f16003180d0440c010485441c68408000106560440c2c1e403088107030a15917110000e010f00308000030003d800416006c80348500070180c20040d440400c100c60314200c142d0546c2e10802038595a40c0000e030410203400c2e08000e0a000070005003981600c2c540c0342c1241100a0101405070908041d00c2c0c10415095a100728409000303400c0003003000708400c0c000c0c10366a5880c40110184e00155081c5121212480b40310310a10f124ad0344c195002d45070500c01e400e00740040443c0142560002400082408960746851025003550300b0707100c502030041e04100c0700c2d0f1450981c0160034032460b80c3c10041031160031851031003604c407041d40100710540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 843161861 1250 843160611 843160631
    0x2030d0c03050c0105191401080d0302090a090203042306010e0402010c060b03010e010c090902070f060506010c080c01050601030614030d0f05070f060b01091a12130b0f1008150604 79
    0x164500c030f4103081a03c0743d070900c41032100d5516000d0700d0307081c00403407110204000400700070000401d440034814080c09420100690213a02d010b078004095444005007440e8030707181c4405187e8100d8109880c00d0310600800200718560714082400d6a8070f0380d80c8140188019854040910700c0c1c40c5001b040281004540c0c6144810071840d900441c810041c001c00a00404060140c418000e0001c0e01c0c00f40005114030f103000030801903070310845850540040380000780c0450361f2180710182c0b5000c1d1405040080d90032003200495500400390164200860000c54281030000c00101502c0d01600103000c2e502d203508003c1066900016102c0311045c07142440b4211107c4c07540203944034043c1c810003a01507225500f81808120701c65016241c03031203003601c070418030b00c0e144d580780c045602c41c20343d5400d0980003c00004c84290070036802d5940c8007111305c0e800d60700350310aa60340345038441c820344030341d1104180d0700c5c00c1c4417000c504038003110050201d000040c05100c0c044240e00880304409401c19004a07a1504a00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 843163111 1250 843161861 843161867
    0x8040315020405120c090a020c030301030615080601120b060919090c0b0403030206090d140f03090703080d02091e010903030c02130c110c04020f0909070309061b02150402030d0c03 79
    0x5030040c0f0004050140c0039000c01d1140d520f969242900e5481541c00d10300050301c01696100762038000700d104000303500756825552182c00410280720720416009641c480012001ca08200c05c0c2d020b0040440c1a0380740c1e800342d1600d81d0841d0b00280c0205c0c0310f0048081000706078807a02d440e1103002d200d4800d000c129411a0700b0304140e28805500800e40d07181c40020007105068000841a005503030280031560704c02d010440450f0507011a50b810581440700f00912040315034188040d41d0094509002c0d03c003030030b5890751020105d40c0a0300007209041d0b00411078003003900d0003141d44070140c00e11103442c80800484500081a1455600000b0300b40030701d2182c000c0640d01da0407107010102c41c00c910100000c0401c107601608185420750084518800c0d0348034888107090900070b546035110720308400c0c1d05181450041041c0d17540018000001c05641350341c8400422414001d4000105a0510a0401810096009050907000f00010b600c0480e031505010040e20001821050754029251000940d40705140c01c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 843164361 1250 843163111 843163117
    0x90a0302030303071119030c5706201507020f061008070e060103020d060e09070e04020d0605091219080106020a03080c0309100f02091c0804031502 65
    0x41c0d0103100100030011002d4216a0816407908a14100c51200400b00445074489501000003000641110a42000140400d4202c60403611038000380170007640d0341c00f4900a808690450340700d00703140100039140d61a00c820280b01011060340151601034100340014140074011041c00311f0365a00355440100040c1e05001c81c0d080540300010001ca1410036141c000d540e03c0348000442020700502c000f0031410740724182c2c048111648800506841850304983c42c8140d02c0c02454503040c15000c000706c410070307405441040c000d010940b6401c1301034182558068038201d1190001d027114ad0001003070002580c2c82010315501c144e403086000c01c855488195250410040b480c10001e075040100d85a007280030a60a1031142c00095030b6401040c1ea03031000200c2e50b82c900401d0143c0400c8203100816001d008010085034803508810496615034941003050702125085801e0315070b01039000c10101600c1c68154130301c41c2d182217030900c44161a00b560301c40c43e62501c03540c4001442c0d608514855a0820455019 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 843165467 1106 843164361 843164363
    0x10608150a09060b0603130c06052508040f0306090b151c030905030f010f060506131404140702060417040f0b070203010608160303020c010807080a02090a03 69
    0x4020042030041d82c140c611685a25040389540c9407100250300509841011510a01e800c1c1421200c41c803040e0481c008000c02005896220341641e00203113502d00510402d16000d1400e854000711504c030f15030200700300000c0d0210000610910742d00c03080c031481c000c0711503011036078982c4400d00ca030410b00c1c4a07586d402840074010b2403600f0080030503409401e02c00e05001c410240c40e20000ba240541d901c0000caa02e80d110951914455814010040140320540b00181810031080300030600040300d000d51703006100b60507003508180d5120340200c0c0c1e00c5052040210218140f00000a440d6181103406640f15103080c0c4000e800c520114080f1000c031041e80004401007400c0001016555000300b4059074150340712140881d01072014400c2000d0040e072440320180b85c0c2c0c59850040e0825a0800f1524103000c02d801c00c11410503000030a0550000803031034010f03510781410001032040300b16608 = true := by decide +kernel

theorem cover : BRFrame.Cov 842985611 843165467 := by
  have h0 := BRFrame.cov_init 842985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 842985611 ≤ n) (h2 : n < 843165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
