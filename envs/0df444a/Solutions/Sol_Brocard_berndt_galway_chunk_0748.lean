-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0748
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:34:12.439868+00:00
-- url     : https://prove2.me/submissions/40e5d773-4997-418d-8714-a1c3482a44d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 134352517 ≤ n < 134532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 134353767 1250 134352517 134352521
    0x306060504180f02060306040e0604060203250e0d1505190c0e0307141f11071508040b07180605070b090304120b040c0312020d020c03030a120e0a020402040b0a0305060103 75
    0x4071008000005800140f001820468050341d40094010000075401101d08802c0c4c1c180b8400b12800c44801e0307400002c11820790100d060303000c101100d82c00201500c1c090a03401502035004581014858211480f01d5020091241400c03201e40541c40c070306000b2030a080904284801e5405c2c00746c500a41042c10110301c061003140d66401030f00004004000040ca0110140d480d02e00384825150815029a80c0700c0c01c42d1488007401d9802c0890360368044080c460781100a0608150b900040ea1110344a5040e1544541c00174095400a802844401072501c841c5401e40c0e00484581440d42000101340340082c2c0950010003070301d0010301800890a8503900d2002c0141c4a101d14010281c45841003042c000100d800c0c0300300260302600c00d45118080c81d403252500201c140741c5000e5000141d0000340080441075040c003c5240384a0258029410a480040302a080f41100c030315013500181d852400c003480d18010010080d81322b0f00a0011907449407104140419a480f00c03442b40c01003030401c070105805500ca4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 134355017 1250 134353767 134353811
    0x6060e070e041d030703050703031503020d060506031608031e0310150e034c0b0321030402090f040803011203050c0f0607021005010806040f021503010306060504 71
    0x35a1004400d0650307400300001030800c003818500500c110050812080c004000804665004c1e4031580e459114501e4014169101100c00c940303400d480708000c00c01a1500c03025015440d80c01000070a60fa51402c0101c5c0c60803501c03212003400384a51000002c0d40c0e070008030040080c1030034407400d81c14914174400d505101c0e01c0195040042101c450070104a0183d160fa2801c0b00f50b03e8074a062a401400305002920385854201e5400003c401611001032040c0b000390800014214504a546543c0251030940b480c0d0302984281003005403280700b101c04a5805000c282c40d180340038803100310312900740090441143c01c1114100e0040a080001c40c809100c140b4407648290307441032901c0d15585c240001102c46203200c81c4101c0500009002100c105002440b0581d25210300300e0051000c1d243c800e41c0280b0b8440f194803005c00d0140303408018408084045000d59100f500405011490803451020a8151000a1524038801c001000200070064240c00c46001c07140210780610501c000480355102a07461 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 134356267 1250 134355017 134355031
    0x30504080a0516081810080712050c090a0e0a0c0203070b010b090121050f07050403020d0b062d1e06090127030503070c060e01080711010b100c06060e 66
    0x105210689480d80314a00400c6202602d9650080988213541d40342c0c019005014600d9001241c400307200c8250800c160784050101203071030a2861800c181e0000741100c01e544484040c01c603105c1000500000600d41118071400e00545619510f83c1e86a184019442050b5101a4443e0502d0080710481f4030000540d0241600503e0007a001c3c0d02c2c1c80da0300f14840d84100c0c4001c0c1400b445c2491a0400b082c1300c006100f120400700c80c08100762420f00540040c0c20001400002400301c188401c1c00941c550318004052940d0120040c402501c41000162741c0490340c012540d03145918040c2d0480c1040c074100c14012003142038a01704600d8038060b001810004002502c1900306000b07102150303a41d8450300c00000c0c0200318000c0b40054501180c5c8038a00940705c1d820559040c2d2001912074200300001e004a80100745501d401303c44003030754800007084068098409820024036171000c00d5001002e40c03102c1d240281c01090800c803040f40074405400c00008003000d035802e604d80240003c0c4080c42540076480394203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 134357517 1250 134356267 134356283
    0x305090907200f3903070315090201020d031509050903070f0f110103061404020a03090501060f1a0a08010b030a02041509080609010506030727060605190c020102030d0513020a1e0501030504 83
    0x85007010100504c200758001c43c1d454400d5010002c00f05840e28454400100c22040103d000d00d02c80c000a80352041900e0480c081518240030241c0d141320503007400068540410010a5507141d0340304107890b501a02601070400700d0f0250002041140002181d0781183c4a24004001c0c01d40000054044517000d209807242d01600c0c0307a800c91280b91035170050038402c6860400054103803c0b80c490500310b07060b40c0c000c501d011940380c00500008103081d07036800e50046140b03070883c542000540020300d400410300c19011503403000300205480d00c119405407005882440b20150380a004110000c0440403130380b00790b034654060000450b00203901030055501c84d0801400400c83c561400c42c50300900380c2d415000e00e10001c0c5080c1c01c0c4001c44001c0c00b8403002060035546150b22240001c488086820840344c640003480034200351100141d80200c1030b0380354015280c800144a9a56404141180065800080d0300012440000c10342c01e40e0f0401c1c40901c0f50b0b80b00c42c0c544801e508c81c001035045a04c1694068400700d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 134358767 1250 134357517 134357593
    0xb1f031101020312041104060b0708070b06120307030305010501030b030c150306030313090609060617040b040f02040e06040605150901030602070309080708011b08040305090907200f 80
    0x12124010240501010b00c1264a012114048281c11941c195011110981c0c00c40b07001c00c941c5018055840501250341140b171500b01c0541d20300ca100c0c855250002c1a040071400010140e40c2e80349d644240411501c000d0b21b94821151038020300411090040301d021a281410f414064240040c1e56001b019020344001c3e22441d2140d00f000380d68000034440d584c1807100700501c0022514100c018001450151000715400d403c08071280180c40b81508401c08008905940c0500b40c203504500b01e03006600180d48010f00e440c3c5041883c00314903000380194205040c015814416807000034a1071245019600c1042107484403c58407010322035440f2415030102510b001400404c2071a4001e160b00c500c01d041c400812940c03030008030b05005035640510017a03503607204444641110041e500c0d4117001c803842d09150034600760768094007034002d0410072409414008001141e440c0100c0025101d500400c3c80c1180941c015590555a03442110102a4902441004086401ca14981c100d21541100b0041c0307520 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 134360017 1250 134358767 134358773
    0x50303070624140a0e0c0a0f0201060905040f0c0b2a0a0b2a0909160e031603050c092e15050414010207140f040908030901090b1f03 58
    0x94041124003200c00c0c050120082500040c2c006090010542d02c800b2107010001c0900300710400b191607000d82c6102c03103007104201e0142d214900710b400c0d101c0141440d011a00e400d080403801000380e60046000207140c80c06100500410155207001c491040540000d5140c0319044da2405010b002c0750b81c04150b060340303003c0c00325090340081c041094014604903440d8408079180e03001030b00c400751000b041044800445081c1e00440455200500d05510798403890010b0b000c4c0031801444000701044860200d504210700004e10410f00410307204401401c807101c11100400107081c56910b8801140c20780f1903294000c4160401c0900c891040074400f001c0100800c544141c0c4480311822041070b0f05600c0c07518000324a00394020700c10500c0c0c40d46a961a81c0312818042d0441402c5c044005240c103541c0162801c0014140c042d400200191068132806c801c600c524010a015181d2442c0003405054003108200d800d0005601c9901d1960141c2c1d440901c981364510020340080e0000c0c1e000341010030b400c0c018408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 134361267 1250 134360017 134360021
    0x70b0417251a1c090302060907061d03010f0509060601110a0506010303030b030712050a15092f0409060f060605040605030a021b1c090f0b1902010b030708030703030c03060503030706 80
    0x700000722035900f031605400800141c1c031001191107140c4410b036500000d20a15038104051a4042800c1c001407a4490400b18050410441641c0c404005e2100200f8030741652400c2d0049036040f2040c0c0c00a1000d401c2580c0341a894110484011703000510729018100d5203800000e204140380d80200141c41c1036421034404501810424281c82c6c2c052113454000940c22010360301d4082818011400b5004103982c5103042801c0035002c4480640640c10711a11034041480c900c1e26030802e54003c08004041c0510854005618544100582e03002c0c1c03501072641d050000e91b0308004262942094104180c60b103c040c02c0d00c81d8011b40c064000062014000140b100c01d8503030040ca41c0544e941c000340d84140914a41500c0c0030340f04800c003d006140e112900021a03040500c1c000580948924500711604154100f4054001d540c1801c003030140106030f01e54503500030740c000720900702c000c0d094400240e01c0e40a4250342c1d910070751003100001e1070060346c1d0b08801c3c401d10504068400040140d441d0403a145ca803000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 134362517 1250 134361267 134361299
    0x60601091d0406020c03131406030609180c100804150212070c03020c04050a02120105030c060a0521070c0c0b0712030209040b0a170105011d01060c05070b041725 71
    0x103050f0341e0030042d481194100300080e15146000703a108110050500691070b002800200c012800380009106000c000c0d91102c00c156030000c060100c0e400b62000b080032191400500e41a141d40000e1800c00c500d00c503075488655240726500030418010392a2803185020224400c810a0300004508003011540030703071060b60100d80c01e5010344100c80040050a00140495009813224610b0590005004501e01e50400200d1300600049000e411002c0d44000800d0b8584100381c9900104200000e141c0c0c0510b0812102607542c0300030414200d05403400c0340006c0c1c100e040b18541a5201d40140c50000b41007214402100c4995500c843c24004403542c040c0241d0282d000201d400381d100d070300d8021000c800c0d16407012060081801c026001e0b1030240c03d039215421600f040c4c000d240d855901c4110500c5040c462855141107440324030b0000b090481c903090403401c0a050750480c941c14400001e0008001c450001c243c070b094000001503c0015030b2481000811541c0d140c200c040c90074900200300001a42600c1d414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 134363767 1250 134362517 134362523
    0x9092d0a060e01060309060b010f0e0f0406090e010902120a030906080411280803030417130902070b07030b060306100f090302031005010602010b010c050c09040201030216050a0302060601091d04 85
    0x41405600c0300c2c1e540e80e007420700340c00c0000000d0f902c20220381407010600809030011000c1c203103400c110382c0c4030800404c0111088044c1e07002c2c0c4110442c0d401a80c5613030740000020200000c0030007000c81c11030401c80c080c108080c01030f4230400c60030485c9100010041595041180d142c1c54041e245450a0020303194114014001e41310030f041845124002c0e1140c4c0c140c410740d45141c4040300380e180c1c0605040d4a51041075041240640c0c001d004100020304101400542980402c0e40c1d0360725408030300705030340503801c540e00b00b0032200380081074905c20400e400540c2400345030301c1d07201031080c0e840c41c0c024007101d401f003100c840750311600717405800b19214054000f0f40d070140030707514100300d441e038907600800e00c0c0600d08410304001c140d0712401000003590a21500d84546001d1030107668840b6a80c42c1e0b42e0380d648442c40a10b12411608003c04d08680c040e80c1216403440c4100c0900b02a05041d003482070325040410026005070041ca00002c150350b2080040074240c0d080380c8420000b10080e81607060341688010030031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 134365017 1250 134363767 134363771
    0x40201030902030a0308010608100b1602420703020d030e0124140a150f020102040e0a05060f0301111b0a060617070609051008040303090206040b09092d0a 68
    0x3180150f10140040e0818501a490b01c0075207515011005021000091180422801c5032209011040c0001c0859000c0100d11908c002c140c00e4900000b110340b10800b036210420410f10380043d14100c10300a14250041d0a00d008110740340742c00a40741c0d660b1140910041c010781192040703450607400b0b80d2243d101c840c042d130300000740c3c0341c94040e0700560710140c00895141b41c8034002d0100321905103021040d1401000341e8403060602d00d0310b2902c00b1340000c0d0201810900c40401d07903520b03400c1d00c00d50654000f0064104604518140490800d004160a695540c007400001003458a1803c05010300b4110002c410141480d10b5800d030303541111074041100c007404034050004441d012a40f0b03806514040c1c10203100401c160510003aa807403a203940303907101a0600c00c3e075030400c11556840d84105040d102890a00308640d607240c0c80c048000346400b0b60000d40c80072000c40c01241191909000c1e0030b04900603a40e4591030707240d606503901003801101001500c070101c25078480d801c1e403000303114a0700280150341c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 134366267 1250 134365017 134365031
    0x201903120b040f1401051503070507031704030c050c1008012603030f0105490501150807090e030f09061605011b050a020601060302030705090d05010212010b040b0304060504020103 79
    0x6095814248030079598580398100d44c5078150440c09014010041162012542c800125a07064203001c02012401400740c0410364000303241c020000138405544048400805252070324000d44400f404440556040c4130b000f10003200d078101b5851074281c000681e00d40207ca60710705503500343c405c009200c83c01d82c60011004d074001440030410185004123521400130025604180522054110410020f03204030020b112002c240e84001a200400f0344c50b440ca810190000c00924200c80c1415640043c459841c0c00031081c00055a52048416128800166208150f032041c000003968a0314105000070381081111f003001980d4080202121080501050b04184c00d0889980c4031402c010f0041d0398070f0351a0500c810341244100381443c40e02606081c502e090421401c00290340e0301d01409070106141c1e000020a40860042060390b02d0280c00030302003041e201079890014080c3d08502c5034260130600d40c0c4000308003a079841054400b0f942008810600f1030703545490700c1000d480040c205030706250340c0b215 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 134367517 1250 134366267 134366269
    0xb0109030b040c1703070b1f0509040f060e0a05030909150607050c0102070b03070203030a09051e03040806060414040321020315090c030108120702030319201903120b 73
    0x1c0403407049010f220341d40034161801a0344420710403649180201d907081004a10000782000030b01d15046038140da040d03a8114503007a0300d5015503900790400795100703210208100c00c0183c02d080319500c071445440240200c0c136145500b40d546003600303a0010201e40003400034000504005841c2607110030020302d0041c007a600440850590b038003020301950a41c108008030ba525503010403918000307140c8094005d10b1880e180c14000d403680005030200242075151811503003884001c210441c1800c0c180c1b841344124a80507012103940347e0140c401c441d43d0b4010017000500328605489030604001c151134081e030466803280d9045508144107122010000140c3c0064030341043c0504c051803140700794109200300800e00208001040800400b10011a00c0802c0180001c100215203131000c030b000c210055403038003503a2000a04500810803000320700e0020400700c42070581c1c05004d10f048042442c00404c203d071b1484807503072303160a05080e000003041050000440000c0c4a940c0204203100c03803040004458034248 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 134368767 1250 134367517 134367533
    0x20f030403050403060e16030f1119030308010f08030f0c0708120a0314150103020d0f0218120d05091002031902030307090504050405070608070c06060b1c05090c040b010903 76
    0x500c06600146010405008202c424130522040d0b42c242e030002c0011078030152034080ba1212602004141808042e2460304000b004403c111452400a201ca0104660001d03224182406407006800240b5142c000148500ca441d100805641e143c1018615000302d01401c00c00750b034041d03204243d00744521b0000184a1030f06020b4070003101c0c00e50394429561040d04200a094031080668540c8103849031043c40b188020710007080030074032020308001d80ca83e4120201100205034541142c080c82d1b00000d9112002040391a45120308001144c20140010f080903049a03076020014101c80850820070858800380380801102d824483c9074411a80f030407603104440f0b842c418000380c002016900c00b1041c0140c0a41010a03600a01420303181005940b802c0e0700d030541ea420f10b5101c0c40c400d01c100640401c10541c403d048840710160002ca09124059448080d05050f91190140f400c480f620614520140c05860060ba03008030300082c02000002d01040400c0000c10705080102e05000e03041c0740000001e440300e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 134370017 1250 134368767 134368771
    0x30c0c0e07020a0605060301020307020d0e040609020304061401080a0809011407020607030909110f0403060b06121801180317092a120105130303020306041409030c0f07050a030312020f03 82
    0x29034090701c0740820b54900704c0251030b0060a814820307401803040140d010350000b0a64a03140c0c3d00d2a024a04019810200d0020070640d04041e100d1070000042100b40104c035000105600000d030045006681d840300700a8170f450340d004004107030034810880c18825602c41e0801040320340050000324602500780d40000c520380e0120400f1400b05000007030801011400e407080b28204000140e00030b00d40b10502031500950320a60000801c515a500801805511004291041940d20600030415400c29030551501031840502090442d070030b01451b00324220811029480c006e505840307820941c803e11aa02c40c4001c2d00400781101d500c9014202080042e10a10206011200c0012095140b20200500500c05507280c82d240c2d00e0380c1001c0c14070010b40110340031004055050f140058407500c8141c00100584442d0040c0d04801d001e05003446041e55020000f0483c10b040b01c02202e00224a80e4009900c2d50070500c035550340811500410070220303000b0702080169541454005182014080340500d480d042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 134371267 1250 134370017 134370031
    0xf070218041401060f1203030515040c08011a040b040b07050c0907030c1404030506010b0706111201051309030801120c0305070f0503060f091209010c0209040813060c020904030c0c0e 80
    0x12030440d0700c0b0120038815600540312045050305064144103644904100240c4000c04160761840007032020240c00100d55100800104140302d0010007500080040400303004e0019001d100342042c1250307550f084225003c803078501c280e40e4141454010400c905802002d000c2c1c41c18081e0000c4046540c4d1091446d0b48903a0f4070b602d00140800d11660001d0407080c810702c09a0000d00e0410050011460016205045803200c0c5580d40d55500c0b240b600c1406000c040d80c0150fa100d401040015450614219050684a09507401c0008500d01c501f2441920358030140540401d0044006016041017842d0001419000f88a0403000559a81d91585445000c0d40035151a420701c45050005180502100740c1060b424280c00d03071345003040f80e04207454030000c07000c03042c5d00d03400000c150220764002c0d5441c0c480250018210b889a00e01170802d110303c1d610505000500084002010075000d0003807a20301c5075580c010f001c0c043c5a599658068450308034540c82a2020303d4247d40018089883c80340341441505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 134372517 1250 134371267 134371283
    0x50d0302011e021327180c0f0501080a0902090103150603021206090c010f0f4a01030e0c0f180108010b0301150302180c130f030209090109080f07021804 67
    0x9a90802c500010389038010120005c3d14000403a003500191680745088140d2000014180d058503680039000c2d4180580189102c108020004007611400b900400f01c910a0329508070340e070f46405401c0100c80440c20f000303500000e07880c010b00c040340c44020b204d0802d005100000500356225000100340258035000140355038008030400c4000300040c000b55a443d8420f0078901c20b590198280946600c8140e1801c004018002c1e9540ca15550b60708280c40b1441c1004641d42c0284802150001040f4900c000800b4245003610008602e07501c00c0c410002100000c070040c264400d001401c1184100701130b01b6141c2e0100498880151444901c500c40f4000e20524000181c6221000c0a050960b8240310107446035100100c0e0030009130700c4811580d144041c422249152640e101c4020503420f0103980c030303903a10049106030041019254204c00d0307000d6900032075044600c0c0c3d0302e000d1064282c4800c02c20082082205019010320000d0700b40240880b244020070900b40012421030707589540300b088500360b038070720 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 134373767 1250 134372517 134372527
    0x27080706060902030f040f060b06030106080405070e0c040501030e03040317180409020f0603060d0506090a03110304060504210506040606151715032d0601061107050d0302011e02 78
    0x460544148030042c00003007019421031411522200e9254030040000c0c0a95a50b030340d42404122044c1c0c8007034030503c0b004160f0f54036540c580b1001060030b20b0880c2e0855582c4103100010400b1486c1c43e55103841121160044c900c1d00303003058011000f03807117051351000d0b191000f444080300042e4401090003800103d01c58040c2c03100c0d02910009500103040080710300441c5005411005038550440f0008402015600300b030360fa071a6070020a41d008a008400b41c0340e8001c40c4140444440301080c2c0d030b0040c83c025980c12180b0310140085e41e45074030452291030042a03040004000f4541540084084542142d51100840c10103840346400c00004440465115070340d40400e100141900642c100798181b01d00c2d03c540e032204001050188900090950709403405403130b01481c440d503010820039250510b404920501d1508240111280c2218403919845600404001081107842501056000c4455000070102c0074a00014003040140454094045540740d01d940280800031080d5044400d102202c0141e0720 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 134375017 1250 134373767 134373773
    0x14180103030f12061818120203093d0c080301060207090c03020901020a11030705030a12080f0702060a020706020d0510030c05010314160c0b040305031b0309060703270807 75
    0x1290442240f1808549008000d0003110031518608880a5400a0004248075040002d0303514241462004044040c1e41e000008060b6011001d080e40900596080758004000e1402000302e40100818480c01c00d901c04444640c0e40441e20700200988840c00d1079004201c0e20340354116240d009030402000350f800140b04100070b010718400d0686001c0c442c9030440c07c0540c0c840000392903021408000d410441550105940f030707501403001c0030081100400312142205985865414000408840030102d12940d000460800c02c1802c0e9601c11782c81907000d48181d940c0d0003d4a8005e41010303009542c1a079081c05030310701401c00c900c5400d008400c4803008502c2d09186140043d80c19115401c07141c109800c0034100c428060000714800e03084105951742c800000380c1c00700121180307070304070102070410080182407005050b0000d00444c01244022100c0441140f140d5007c1c0507840241c6041d40c0c6a4000000202c415110741d00807440c000281c60300b00c41c694a0300e5100041c99642400c241c0305010000341d40410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 134376267 1250 134375017 134375027
    0xf090a120c0905090c0d1104020d062103021222120212011503080c0f030a050705010501230f0109030507090c03050901060803070b04051005010e0103030807170114180103030f 77
    0x2c0032440c10a1045203441060281c640d003031000b441340549401001d0070100301e6085c1d40750840020141045403980ba040f00c0b00d0000e0402841881480340050910303507030450440c60381604003505078005150008402c080142241d100e6a600600040d0380c200c500c01260080320481c0060514070f094018074009d500400c805c03641d0410740c510290b89406201107500200504010483c2e401c0300302c1c0c644469403a800340d41003240201e8644918040001c074149a01d801c800035143ea140950000c2199a803600000404843c0c0158001c400d4a804500315610b440c000e01340300740d8241e06140040c0001d940c1e80d0f034585408510340080c404507482d40f00d202c0420781c0c14450340d58080b500b200240450380ca810f1030141c50f40308407880039001d545e5807030000f418890100805001490010003c0025680d210501c0c041070000780030440002d10001e0200e01c0c03841c480c0102d056a00f40c0781203200c025910380080404401c02141c0305640020f109045040c0c1c07800d086038494021400394458154511864200801c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 134377517 1250 134376267 134376269
    0x702090f0f07120e1002130b0f030a0f0b0909030309010e070323031c020405100302031b031003060f020c1c0206040605060616030210050105040b030309060f090a120c 73
    0x24880c58010801a8025104440640101480c00d12120301e43e01d001560014007000f4503011441c2c4a20000b511201c1540d42c0140141410141243c09150b00da610301105da2107520241d0b05e8140341407010440c1c1d04407651121f03076180d03200754002811b5242003021a8020350120380c11102500040704000c0780210a0046a590b082108003600003981103650344d5403c070704c0800d0040c9109102c0d0050417402c0c94201b00b11503592071552084e05c2141104080c0c84c0c061360040c010a405903c840b4600080b4034000c0c000d0300d016000802403205000100c8182c21003c4c0c000400241c0440c8202c0000808a07803103100701d8002d514040e101598460340a400e07140f4204402c0320b410ba42c448001c090b040c2981d03011410031f0300f181e4000300125003501c400340092141d0299403140004034000074a10380030950001001000004800000d218680c2d032034007000211600c1016198064004202140301031030541c000b03126241412130083d003804003101c0812040c4415070014503102580400c400c0074004a0502d00c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 134378767 1250 134377517 134377531
    0xe0412031107080304061125030f080603030702040c030f0204061205011202150c011104181508250b0705100b0301020f2205130b130b01050306011b17070209 69
    0x3626102c1e8550f100b0b1002d110081010f804207607506116106000503000b12200a001c8101e60000300b040010500e916032103100080740030904000c810080e050140450601c07481004001e142014243d400340000382c00e01800700410196960144906c984840c03000d0b0014117030701e5541e00041c810051102080720b4060f0800c030080c210b40620000180d0350740595845440020410b00e4a40e1010f8110f24090300310051840b441240c0490040b030a11506903a035410034410040a010340825442032055408050107803520541007982c8500030081d494070310148007406d10120341f4480c0e650b41d4000d04241c000c01001c580540201c1303999a6441c045008445c000704048008610f80389100706030113400d109104011030103052410b100e00c0304516500e4120010303c80a0300c8401550482c890f02d50080103020300281c0705c0c4184485810910100c2d11601080301c90684806140d5110b0030b005681c408111654804100c02070161840002c446900d0006aa031624560546a60213803040090380c0740300415023 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 134380017 1250 134378767 134378801
    0x80a11030a0b04020d06020f041d06010f1b030e030102030403050c0607051305040506010507050a03230313030503100306020408070e06010c0c031101200601080d0206070906050d060e041203 83
    0x454003084002c1c1109400ca82c0c121080840c10032180b07807203006170188150075665400d0115002908514504212441640b8032a0060540d921000192507184020b880300c0c0001380a00381c03c1035580703c038420700c010080c00390808820000704980002d00761ba001f00c4040b40014004609410543c0c820481d0b0b0740c02c8000c40c1441d600340120301c00d0420554600d4420075100d180c0b41e102082480e4014011504259040305c25581e42c05441e09028240380c204100c401601c0f02c0b00498841034417806015207004070000c5820300340e4400d841c0c03030444040d04003a210402c0355401500004c0028640d2000300018502c0341c0c0a00f5246142841505505200038135060520580b140341c03130000b03a119215601640c0e44001c0441c0c0c0c4c21110001210728000c0f1103084100c3c510190f8420513082e034000348150407246494122620034210043c2240c96a0003925504041140650288401d600584c041d1229020b80840003a10b5990f410140760203000c19141628005c100468a0384c14680c035000c1d402612030035500e5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 134381267 1250 134380017 134380033
    0xf060f0302190b030712020702040942020c010b03060f1005040c05071b0b0c01090c05010f0906110c09040812090c2202040e1602010e0610140a0f080a1103 68
    0x34000744030041042c41008241c21103459006c2095065504058010307108216190051500d40380192a800f4400880303e01340d0000c03200000b00d00041400300310300c3c1c050a404410012070b0301c4003a41202190010b69501c45118034580e4508024030740c0301c3c0c50360005082c5203091030b22080030500c0c400d80080b030059080016400c02d11f5004011542c05540c000080645141c12204032200d8600395005140c545000150084a840054008c410900c0c02140f0680d05207688200640303c1400c041041c801050b05042c042007442d014040300101c0c2012142a160402910000549000d40844048480d00000316480494504503441268001500001040040e109400103a150107050104000000e4090b814a0900c66a81c040d980205103c1882c4541401c101c3d040d180140a586820001980703001c8000200c3e000001c0d0701c5007d1280d201d21070090b14140743c2c00c500741850040c81d803600700242d1440040c4182006062030018540d190242c0300f200040e00d007444e640b2452111243c0b00b5445109 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 134382517 1250 134381267 134381279
    0x305090c150c100c020708060c1e030a020c06040f050c09010602030301171c080906130c030303090206090315160203070b1f0305060703020703031d0a06020a030f060f030219 76
    0xe607003051070404810494540c00214030007460a52800e0480c04000d051000e00c0c100980c000900c0c0c1e0503103000d041030310120754442c000f902440c0214843d4017996041c580444010308500c10040d0340003080801c01501d400e1160014500d0200d081c1ca0494900c10800254030034001d0900440502d11011242c0700000e524000000390f0300c1c003060240b5219001c2d0b8414010091004211a1440d09041c40003403400076494180640940705c11900708401d030141c1c800140382454000c4620b40003a9121010600e181d085440840c01450480340485c0c001c2d00c01c104ca56070a40e01000300b034020541076800c2040307510b041c00e62003030b2031341c24a88030400b03540c010b005400020703580f4006164828031207443c00b032440c2c3c4100d2030740c41460150360010b0070502950302480016a070640003040482d010b80c800344004866038004107185500c07050384a8041e0040f060348000511150001c0c003100041d490003042460400c0c84800440d1100d80c042a41c1c00d407200c030100300b1820103034000c0d400d5412a00070168850f16002c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 134383767 1250 134382517 134382529
    0xc090a06020d0f122426070306020a09050d060e1902010c0f1a010305010204091109180703020f0d0614030607170a0f0f0e1203190902030721030305090c 67
    0x11407808180120001301480481d4268400d8129806451001030885080440d013018404680682031000400646c00848200301e80f400d003030000c2008000f460224a140c0320207009401040c0460100641d501c40001c5650707402c13654140c0e0b1800b0b9240054201c125140e001e1500d4450944850464080d03a002000750f80c010300300c50b520310740140010382e003c07803540b40030711001d140740301d4014080c810b0340000300602c1415406481a2181031204001c1e02c614001301528034052544901d600c40903180b100340240c541064039940080c01f03400d026040c105402040c10712504190141d49803142c1ea80003c001108514618400840081c0c01400d12800c0844008200d00c1c407460004010300150804038901d08015440341c40380c1d0f138045000304503040c0402114800b50180007030700c00c010301c95450701900c0c44208908613809010340c64000f0711320705002042c1c040607004101040e80e16008903800011034417020b070100340001c03514840c0c0300b020b40350030b25000d812180064802400369020040383c0c0807a44641c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 134385017 1250 134383767 134383787
    0x80c071e031502090312070c0803040b04090e010609060b071b080a0f0809062106010206150d06060e1f0f0b0307031109100e030d080f04080c07030b0c090a06020d 71
    0x1180d0440c0e0b4034065480d1020340729120b4030541601c645011031042c002c100001c2c10425118807500809640c1e07600001d9540e00442c0110341405ca03080004010081066001c81ca032003292000115074565205116803c07140389500194201200180d01c4041103007a04104c0b81078003192001c500058142880160303150035188000740610511403002041c4108003040c0c41c1c0307602001742016030b10f21044441800c0344440e41481101e254140c1c02040c0c6a41c00801c002d441000c454512402e080f400200b0821802c40d010760a40317450703135200c1c1c6c0404c8509440600c588079642800700300900d25040c1425a900d203150342d10088010307540390800d0110010600841e50407180c40d29000c00c00150000f105426845144850340d440440f0310a0f925032035030480ca101c0001c0c80c08400740c0d81e011039286404d4500b80d0003210380411242d40c0c00b00150029050902414151504404413134040d501c9903581040e04d00d0907100ca5a0180b808076040b8420725280d1314a44c00303090284003501e0001204000034000e06e0b01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 134386267 1250 134385017 134385023
    0x20a0201060e090c12150a0603020108090307020108070e06090409050304051513030201230d091103010b0108040b100e01080a0204060b040b0a0e13060332070e090c0409080c071e03 79
    0x4c5507060704c0a175001005245045907a8000d00c401d141014100d901c018481c9104c120701040203203001a030303500d03008010754035190b4041e1a030f201150340302c1500700d54420204002ca1341c000418408030100c0c1d01ca0f0300c900c2c05445c1c030840040d503403079040c00100300c01d074044540010301c0a5010002c9100207910450814100c0c1c0d0b081c02c0900305d003d6402d03201c01c00c2c3e82c20200850964100880d080051604980052001c0340c01a5600e162400d040b01c04e01d42a24039400c520381c01b040350f0303601080014102440c00740e07000c807148443c100c80c0d83d21079210414858080e803040d00c1541c0701304203210562070140314140040561000e06441c251070203d0a81450245811240030322443d16121800b035125084030070203201e089007040005503104e161006400560b000c184285070902594100319244011a030310216a0080003048050301d42190341d40030020040c4103826a00809010105035100d6008040c0c010f88904181a140c1d03102e500c0c102e24102c400d90141408001502c0342d02100180c0040d41d2040d650 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 134387517 1250 134386267 134386279
    0x10306061a07080306060d02190818120304060b061603020f06100605131806140f031f23010501032d020912070b03450a0c09020a0201060e090c 63
    0x85c8480c002a40f5001e00d043c00050703d400012000d410300c042a81c020384029071911504c4807901d5120301e8140342e504c242200b50580e8000d46480c10800c1d004000785034071030b114403404074003510f41002040850b000106280e80b55248032203503070b04040e014070030044603030352a000405142c5402010944102241d1142074280f2500081c44c1035040305024080004c0e050002d83c003030414101100359030040c2450f00c1804d0b00ca8120000c09000780c175200721040038026004008241d001445d4007800078140f10303410383e00b034004c0c1d5401c00c0f81c000091501007940e0724480c0c24041c51140d0f01d00400502641c1080582d5524210f040f44065000721040c50313801c6824007001001602d44984030041490428940034841d4281b007a4100004c0107180e40b40210322452603200480b034000788010308aa5040d1141e001d01c01c0d41196403000414054882000c20000c050b01d1084425a140b940c4a40c581c1510580040140540006060700d4054090007010000e06034a61200031514040388516203d400380c02e80148980 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 134388767 1250 134387517 134387521
    0xa020109050108150409030e0103060b13032406090c12092301151206060501020703110603040f08030a0b010809070503190602040b03010909050c04060b1209070801020a0503010306061a070803 84
    0xc602038840c120780c007134040e000300000304890034040c107540103c4548900182c2444000300d450b484a905941001c4040c41300c4d803550b107085541c2c6444002942c05508842030080b090407020741414010301000b088840000650f40005a10007440e044414601000c00d5040c000b9000015105a200840d10303405428030040c81410b07242068050140c9440ca5200d511400c2404159640e1082d0f8180e00c5910403002040125510001643c0303400c510710002d0035820a084240b00181040c06c021503002e07208500c2d18907074150540e511595034006407140e452480c1d0320a040c00f11940c0120b441900b01ca0a0801418401d14080c006075540800760301d4841c04014a0a80c40200041c0e50150380161094040540d1203603192080d08005000e0b081e02a2442d00c0760f00f001d2060780c1020300c01d0030191101106413a1518007800a00b08400002400c50780340d612407601c0004481c0800e00c0030340340012880c0d55071541c035495800c0920a0b56182d030000002c0e4101c1106c1510750300200b00460700d4042d40459460385036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 134390017 1250 134388767 134388781
    0x10e04030806150d1d010507090b0a02031306050a11190206070f0b0c0a1202040501050d0b0a03060227030705030319090302030703080d0c080106090603151d07110a020109050108 78
    0x941c1e801c64010329040c80844e040c0c0031600315401801c041c041c0c41d208820f0020a00c03091a0a132101038842c207010038580740781480708005140041c201f44034680110792422030441d003131200011407a402840010000308103103546950000c0c01510300301c4088008c3c4040845000e103e4070190704032200a01c03c050000e032003c1004101c00203a07030943c0e00a11584018600300e03400980b16489260020000361034041c010303400720001d10070f84054801c10303520389040880020100b0010b180850740590301040103e000000110303c0c1c0000c180d51b00540c0140c0f070050000c606220101e06141c0009442900302c0c040a02151714004140d41131040400300c0c1d00e40c0b4030120780040d108000150070194041c0280c410200501100c00004c1803858031200342040951509541155222028042d1000003600d0802c10004903200b500805198842120a4843e46070794581c0078800c012002c2000c05928021010004082d4011540220200e82440688007500060f40000c0658070280149418001c0e080003250784 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 134391267 1250 134390017 134390029
    0x90522050705040c03090b070302220e0f040302150c13060302030108060703021b03030906070e040e0c040c02030f190e060403030c08030a0e15010e06030708100c02030915030108060a05010e04030806 87
    0x4c000d1300856102e0003400e023107038001d002e58071203aa020700445504841000d410750001100301151002c0b0b118141c075444890300d1209143c800f51050b01140f14000e100c44080c0404a4054047d10460090a50b40c203c1c404891010440c41e51022040c50302c18030041020b01804118194000c2240c90016a102c00c0c484043c1c203c6140e02202d441180300c0401040411040000e085014040c40c1c1c1b90408010207403401c01c0244d511800c1000da03a0782025858510900b4070383c1111286120500549060010100e41c41c09d60340c2003100202c00b07004003a014080e4150704a40d400d1004801507030082c2c546800c41c1c0f405884070002c50300c001d14110740080003500c03028060f03001c0f6890b0403c000c107481d400142400c000c1290a070038014007020181d11400b00c1d06500d000201c4108580e480c00240914134400d414000080480700000300c03d6002c10404410150b07501260091844030403201c640e220350500030803602e48000201a40006c500d41401032049100904483da8000d50510344004541d46050209803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 134392517 1250 134391267 134391281
    0x8010e060409051204061e021c032d0501080316170f040b09100806010e0630090606010309080702120109080c071a09061b030f0301090522050705040c03 67
    0x8140a8511400804d4424800400c11141d0b59603803106420307500400c01c03104045501000c2c001d40c0c4254100c00c6115042a403c2c44a202c4c1400c00140c628505092703148041490380c1140807035440c5200d0307400300007414400c990240503090015400c001902010044681d941c1c42d0140283d191071180d00e08503480102100e42c0c0c0c4410713200840d204c03640c0c2e002507009a00305d28162032242401640c0948460b02c51900319228040580d0b503020380c020107006110701070380460540480440101c40e049a00c4440a907103408000305007806000314076125807840c0c100007002d8100703410141000312080100d204002541c5445030100c84100c00e61220417440781c0188446440140702c000045441340081e00081940821155024080c001d021030205001c28548100c0345441e070b10100502104411500c0d00d03c4880d140e80816049034035001c044d14042140303802c241c1c80224140d403908100200f400c4441191a10403002c1c030f4080c00f03020000da4030a61070300450302809024603503c000244e0040c4c46500609 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 134393767 1250 134392517 134392523
    0x201050c0702010206340903050c0906061813060b1908090703080a05120a0c033204020a180903030b010c0c0303080604150305030909060d05070b030a0b060a0314070f08010e060409 79
    0x2150030921358201030107c0009100c182e0b40d900071090300441601f070403000b0610a4000030611071a01d070402586d40452020200d81c181c20194898513100700f0b841034820701c000392901d0f03e40079880b60b2452806000d0314501ea80103408202c408000d0046e44c207400600c03082503c2e440290103441d61111002280c80380268101c0c04440071845c01880882001580403011029860b0ba00344448941e11004070f56400c9480c0c0480e080c013a400c01c0c80c503000221a0402a0010700c000d01c01e0010350758420700c1008200d40328140c07122680c0d07150b88807000c043d01442090381b082c20070f0810100c2c826040c0c0780c0003020005440301400b803164000000d001551142c4c05681e040c01034a00106c081512410999501c0d0040110580510b0220011800500d07204000c0140140e004004002c0c0300d080204584a641014101104650b00c038605001e90360741d141c010300102c1c8095034000900c02c103000494400010094060000c0c4655410451111a84400814103480084032040c0c4251941404a80101082c01000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 134395017 1250 134393767 134393851
    0x6150316091109181006110601030f020109260c18040f02031c090e0a060b19030216060b0a090b0f040e210c0c06130e060109240201050c0702010206 65
    0x10354213407a03405102d45c00f034025800080c1000c0d4a070030060365102520030425059910172001040050005e0502101481c41031400114490b0344084000102082c4c0508200c0c210b0007080390118028100f1020720103c0342120440b01400e03400d911a100c00700094000340011107020035190540d10200604524410321108600003c8440380d40100000100e009000c1403c070700304040358020b00c0d1401140180c4094889003850125050b43e4419150b0b00128041c040c50703000c1c01560311301c2c03c4014041c6201c2e40200c1e00441c038900d61000b001230b003441540040c94981d16140302c0d10b40a0311204601c0d88010000d4400042c0c402604540341e151081d00352040b0441c4150410b0b2a1001d14581e0140c0002c001d080d04031555846c0c1c09040120502444002401d040e8002d241040030340c4005c0b00168014006060042d152611810240003242e8200c054500700b524030040114890b5092088503400700d00e14160f90704007202540001d46400340944007441d01c026111404000660701c0c499207840c50550713080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 134396267 1250 134395017 134395039
    0xc030203060117010b0a0308030610030e060a061d07210b06220602060408070816060609050603150103050c01201c1205190c02030c0f06150316091109 66
    0x155501a0402d0030fa9102e41d54202040d0f4a45400d050001c0b0003170320ba010800038219642c1005000b10000009180c00c1010f885a0300109850700901440e8040e8062110210707001d81440555480039002800f00e8015840c42410803003940e0740018020003049031003035488a901c98099207070000d0038665450303036071040e0002a6601000d400248035800040200e95a40140742c0d940f5041c0d0301c419007154003502c0b17594200290000205044014031000310a440c1500c043c150fa515150101c0c2c6494101d054819910414000c182c50100000d0550802803024091558190343d42d80d6203805100c0002e50501180c450784c03001e014080e0451980110100007155114049003a03005003900c5008103c10120300602150710a0340301a01074148214080035640e80d804c1489171101c802440e1403084841180002d20007030064240510070000041d05440040450741055030401d00f100e523000030214880c3c1d0003503600500c10706643d04110100c0e1001c00300064540c6468410030030900c14404500e41c84550100c0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 134397517 1250 134396267 134396279
    0x60d02030a060504051008060a0f0e2a06040501050f0705030412060c030c050f0306150d060e0f090304030203070b07062a020d030b03070509090114010b03240a0b03040c0302030601 79
    0xc000c2c02122011201808243c131014490981100d42e805803226a80200300002e074107250302d030005608928120310005040001c0030b00e80d8104001082c0d005c62a11500c20b0511540b6000040d000c419501158003a1401c2d1030000080d009200e90064424000004110305042c1301041c81642d00408001c1c0090100482514040c00180411b1040c580440d1130310039016140c5106105591039200c160b0354140c919103600040011090310f00340b403010384140810102403c40d03200d024040c020041141c04460500b08400c1e4040100402020860070307038018041000503075400500001151100c10205940705024100407014000202c8008210342c08103c0182080181402e00450901641d003505d00c241d80400086080e030b00102e0450350b0551203601d0611052a1201550b078208c043c150000a100720755030180c422024090b84045044c40000c01005401c481d0400c1214420700f05104c0107601c0d00d140000101c100032540248224100d01100050401c10381141440145400401301d55466035241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 134398767 1250 134397517 134397521
    0x30e0c12070f1406040902070f050d051201140d1b0b0708120708010807050f0303070c03030903170c19031b050d030b0306060901150512070801050109060f021209060d02030a 76
    0x2100e0b1042a0400560015070307802414003000a07610000c14003803030710f490504081d01a41021500313441e100364200c280c02c0011001c0001050102054075001c1c1c5401c80c240002c030a2900590181019890305180c400e15952005603000255500c044040d11001e0307265007810f800b19003a001000c82080c00680ca0007440708107400b408541c264005030340f003150307100c90040300c8600081c0318213442540311a00a001c24502104142095140030303040324100541c0d03491311441200954000d601081c2014402e10502101c51031a00c030580300c2c0440703c0d103862040c0a0042e901d00f40402d1810078a00c20820320000c1600c6021040284440c0940784225291a81441c40d02c618142061101003850900c010301d01c4c1c18041811442284020101c49141c2c2c41c1c0880d41500d42c084154817820002c0030407000040061a1005901809540c0d8490302c140d81800000b6009102e10341001e4140403d07090051001d130b50010780c01d02c541c4a012030554888554001054180c0035135100003410074000700400124510719 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 134400017 1250 134398767 134398769
    0x5031e070201060e15030a0809030c090f090c09070507020f011707030e0d090605120a060806041109070c051c03060906080f01060e010e010b0708040b030103050a020a05120a03030e0c1207 82
    0x110200030302c2ca84900c5c5828021450008444e40c243c1c104062440202c1c400b44d016052421001d02980c2c0855090f50016900f007a0031600c4d800c120751403500384a07441008108844a010081d5506412800e200704043e21900038510020301c03440e14142041d0f443e034420110000d817802641441d0540b070900340c40c080c010b8403111030312503c01e108101c14060124030a4001e5030031104192030700d03803500418008900301d0807002015444420307203803070000a452204004880c842d5026410fa18074040c030000030040ea040028064004203c0c00c1c5c80d4a401250b808500c8204648680350400c02103030f40742000384d0180c90140d201a140601d003030000110400049060400d0341c482030000c002060301c401003842c0c800d03401c1c003402c16201015401805600000c20081180310700030300d05e060429540d6142041c0c2580f00341c10448040e00500403402c00c5052000c0601d01802044940d52014040800e007103680e0103402c1005020181c40b81c40c94140f020081c0901d021068010b07280400702e007060703140b90382c0e94001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 134401267 1250 134400017 134400029
    0x7050d0b180705060f1317030d1401050901050603090f070f05030708030403030f0c050709021603030506150901031e0504030e12070608010501030e011506110c0616020105031e07020106 81
    0x64aa103040744501c0402c80109450b0000e100c1801c00991079034082d03ca40200401a00c04503400f00c000c0b82c050740c51524410940740d0800216901d00c2101c02010503a00f450300c00c1c0e40915a102e005011541e9050782c3c85042d01c17001d03035007223460381e66113001131b481c00004000c001100e009064011034204034002218007502e4055086400e0b441e03469100b10f0703036440703203101c0640080c102e05c506812840c4115011350301c85005504a0300c034540c071062340c2c104036440381c02c000b042c2c444806112020183c050261581c0000b045800d05404081282030110920403550640d0415995035800e0104251100031221a000c1c8450200028031306880d02034400c4100001c81c40c40f0300c000f5600d50162000010700e400a4035000d036190200d41c0d28000064019001c5806503045035501c40c11a010244855941752004000581d59603841607920b9680c0307410a490528000c0c002c02c02000f4030000b280f000c0340c00c80f9145a081c0f03007842d41e941d1038081902e5007482400031891100030200500890a505400000540700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 134402517 1250 134401267 134401291
    0x100c02100908180108040206030a090c09020d0212010801020705070501050901050408010617190c03170c0d030b01110304140613050307090b01030b01111009170c0a0b0903030c0d0e07050d0b 83
    0x10101c4019180c2c16170071103000751320102c1000020001d4000f80c01c80102d1512503040040450b0711802c5a100381d03040450a00c554a5020507900f25207404011000d00410445000318035040c0c80303031519900e40b01e445c040e082c144540022030004d00c2c0d116038110390040906030000c1000540b01d401c1031281c3c91520b4101d41003807049440a42006514802d0b600c413442e441800e02c0c0300b591541d640c540c1007082c40e043d030180044051041004c000414411078074949080d5a00140030030403400050300d9041928009074465200707010030700100e24100d144003445042105c0003501c807000c2c2c1d0041039043c04290007040c3c244c0204440011071312102c0e00300d40360283d0241c0702440101c00d4480115a81c1d008030407592070903030004001a0300a412075020714501406002c0003501c050058140d8495580019083c1032250702540341302d002e00600d403040f6030704589910050351445c00c3c4907000c0c403050300603a1a6218040ea590380700f048141d00400201e0018900074003e2220100c45082030b2201c80030488040e59001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 134403767 1250 134402517 134402557
    0x204080a0501110c1f0908071112010e03120627150405070906081302030f030d05100b03160e03150405013602010912050105100b0408100c02100908 65
    0x1804260994501e4140e00000740038081c5031007a020741c060000c17413640001036035403100b1501207503540c002025103501581c00d015a082d9081d0511003822010480401030b80d00d0071003030304404034010007211034940b4050855031a540b2070f807002500252911fa0204020101d0901c051060f000f4140c840c0e10070401d040309500102c0d159005e0006031141151010005103d00348c2c01d03c4494040c9010941160124490780341400e81507001c01e10b080c1074070701182040da00c0860324110740d440c0c50107603d500090301d0a030403c0d490b1600c14120268000031b07000f43c0d2440c5030350f0a590741c105d1150380012000b190090884031058a00d0a028a070000c0a85c0c0942d215402c10356103e06d8a80c51001007034400034916203035020a80307071040105034502181c00490400105580004490b05c2c05041030169074041c02c00092035041c002c020b00101005030348409186101440100003101e40440c901e0006912404041405614040220b0a100c61790b05043d0702645000305407010b00403083d02a01031001c120324086441d0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 134405017 1250 134403767 134403791
    0xe3406181505070308041401090b011502010b030705091902031f080a020f1309020901030503090a0e010614310312030207111e100f080708061e03100204080a0501 71
    0x40040341e05000e0200c0d90400c58580040d110b503890035401405407200030390b03000201444600f5a00349607030503540c1d401c00d02d0050000c400d000900f07201001c0103000821100750104086505d624040c070a0905c241202c1002402e4040891501138100246100856032442c4c0680707003100b400142d040c01c0501c1841090003245400c40000c00d034100070b80040c900d07030071100150200700030481410308140c5e0090b02c40c2004401038441c2034101e8040d41c17054003e503460320f207004240b0110141c07503030220f260411240010840541c10024441c4030308425009240c0e22450265804802d106001644908003403001c5401140060350090301e042d64801c48a00c900404c41c0d030b00803020390165640280134440e0f04003d03980c491074452403070036058911071000204405854001560b5010340000755000c1a04242c0060f00030b644144180c0d44a05242080100c03800c0034800301c0c141000382c60f1180141150b942d50581240c1d404c001ca1585540728200c199600da80f1007010075152405014111155800d0031040209 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 134406267 1250 134405017 134405039
    0xb07020c0d0302150403020c0409032019060203090c280b251401061205010c02120a030b010306030516090e0309030c06030c090402030c040302030c03010e340618 71
    0x1e6560164001c0c0203034111800014295180a0f1044080d44508806120607844500401c2c0340c0500070b46680700403d0a10700da01865051504116140f5040b4800044e140c1700811052039034036800442c0162070f90b90704c1401602c0e141d4110f42040c0d003e4191001c501c24003541034000801d04000c49c810130900341c0d0302e007260195070046042e925070540c403c1c402450894292180f50320840e000b42810003c81c051039003540c0c2140c0c0c998200c042c9107640e000c04401400b5003400b0707820070b014807880100701224241c620f0301ca040c05031041c1c0000b00742e11243c944082e41e120350845006503400400355406144483c0e18080082000d00c981101c0e035090000742e483c0008003009807a0b000c10041c02030408030704180e0402c505944000c1c110080344a05100301c1030540c0316403018610a039640459607603101d0031401010b02d000d146d41e659910036130500d44c400d9550b20b00826007010003134036202c1c41d20042c8070044c0100c2d05200b07182e8050360703c8004000c0c00501603502c008040d10000080d0044506284c9950002c2d030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 134407517 1250 134406267 134406289
    0xf27030c1d0709140604030b071e090b03040204050603011d010c090807080604260d15090203060a1502120711010f090305030a050d09050a050607020c040b0a090b01050702030a0b07020c 81
    0x49900c0120400a03620014003d5010354001800176142503220355034400c0c1d1036000c2d10188001050070004222100300c0707040030104800307282405a4003c5c41e040a1030124880280002d004a80792408030704075880942000c080882c80b5211903101441c941c401e1402001d888041c03900140d0b009000080000002c10024103980c2184050b0000d9512901d695031440d00c601103001d0120355010751540ca03262090041c08001c10004000f1404a01ca04c0d14070351030200541049404610401c24020140d03034514002c01190b000b0140c0081450b003200e0240c0c203100398070425080d002e20003d400000c208008000c44a0f01c24245c84000a0743c00c0690102c68000c0b440c000203006500c10000f070080c0502444c090032020342c3d8035a01150301172a90b96200c0c20070b417014070200d95940c000018007032481d8050108a88409003620100500130607080024038019a61055501c203e58072810500070380d2040085600c0160058212842902e076481e0071072410404039071000c014001c07008640c615143c1000010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 134408767 1250 134407517 134407531
    0x21b0a2901090b030a20010336050c0307031b060906050d2c0604030e0f0f010e0f04020c1f05130303050709150302090909010c0f27030c1d 61
    0x80c01903801d06070180c004050001c0e0496140c49154240d5002440f00d6107058240200401c40514a000000c005001d403200d01088507078602400340306035288000c51510030061240c2040c6400189551b081144c1407890341c64145405d03003d051030100501111209045c0d101c4041e815030358205640f40b508440700a8140035110010f58100080070310941d05812944004660407a00c0301c89020095500140300c806640a010305c0c0c04c900208014542c00c504000b512142c10360380100c440181000040c0383e190301941913814848031081c066126100d0629800c14003074045d0003159203115043c2801c1d0381d804101980040903500d007400340c6081003036005280c0103507903c04071886401e0075079070250060840107010008000410400080d200710b941e4943c00b0808454500580d40c40540d01408807a250007030060340d07141c1c10a00100819948900414120212032a01d03140074150340d008454440c1071140c0c1c51861500e5184007200340701140207000c0868a1404100040c6580c2c10940d00090504442503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 134410017 1250 134408767 134408843
    0x6031d0601050102072d0303030f0b03060405031b01020c0f0c031908070f020607050a11181003060e160801060906091b03050c0c01050a1a0108010308090f04021b0a 72
    0x20408520701440000e10710581c10700551034070300c0e04a161b001c1941c09600503800692036200b10300009441d4450091216070690252529190a0715141d68034030a050001d02d0054402c049101c1d9030200f90b0660709036142480030f0700d4020004c0548a41d039076039000f4041d8440c4c06880d03459805281c01c4030b22110115480090035081258039119403d0b400e010880603a0041000c200310400103009214120210f4495002101c0c810440024002002c000d00d411302403881c000c405104030494a40031050459511000100d00f03024030a00b075900b0121105890380802c0640413002c502d4103010341102040e541c202c81c0800c002d5030b1b100d400b501503810001c6600078105102c81740ca4010b42c466003020f03038002a00e0300d03424030f00b5024105140c00c4842c00c59000452907687c2c0c0656120503c64410720724006001d20b808041c6504580303a8101901c03c14003d584602d0140c12200041e80395a0160303020603010300001d00122000b0343e102c0d52500c0380210b040320545c0c40c0101d10500f000050420521074440d000743c1e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 134411267 1250 134410017 134410019
    0xa02011e1d0109051320090d020f0d080a050301151d040e07121103070603050c0d090309031a060901050109081f02070c06170f04031b060e030406031d060105010207 72
    0x25604000e81201c03059041081c04000421141c5864403440a12038107518002032640c0a0450090080b50307401d00601c0d041020040404c80380d0f111849843c07582d4040b2940c2051484540014006407001c90000b00b42000104002680c43c0e00100514102d8083c0036401c03e2000123002d04458000d94405040300f4a00c96078001402800c0c90b078040b131924032141044038002c540794403543c640e00c2e420383d030121040780780318528101c0c0741400e1040000610f03882c1010700160416217220034640c01103801e02403003166143d0300c0714180352140555400560300b1460b0048076034507000c09401074200454401d40510000400060340754460000101144e0162002d0b0000d000071540083c10304412200f00d580c070300e0b001e000703000c04906040b4440c002401286c036801d00020800e10b024074444401030141407a2100c0900704401310b030b009200103000c100d000f100a0640105450902d00a11001c1c0c00c1c40c5145c030010402091042c3c0591101801e01083c0301810602c26030b0710a0195620340c00d0280078016040410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 134412517 1250 134411267 134411297
    0x216050d1a041104020301090906060906060801031202030f030f01080c010c081e040504060b07021003050613020309190b090708071a0f0c0109031d030105060f130902030f0a02011e 79
    0x602641040c0f1422104200000c0000040c090f80c100b0381043c02e44541c0c2c1c1c0460f800b00300c2280301d00402030415101c02e002003407906d280a04080014071000e00300b1900698201b5916209000b11461410303804802622030510310364108500f542405410200d1150071445103a5601521a04580e0395101616038070b04200400070011030704081d866894400700621010900703654601402000d8003078a10651b849034900e0040014000182200303400785482c042c02c0c451940c03600400006100c0c6954000741c2d0b02d842d00d80c0b0280c82d1141500006050300320003600d240802080000444c06083d02108a40803680c88401e030548403031403441030026500340b04841c0d40000c8a408041c240751154080030074200b4000e011030a0a540700404103c2c005682c0700e9500401b002038244009000100350001c111914041c80803400301c03820b03013405c0c2d4800c40041c850580510641d8005640310b55000d016600b01110b40c140460f41c0304100d407000ca0100328510002000803001c07550320b0ac00d0301d950760f90325025058100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 134413767 1250 134412517 134412563
    0xe0a030e01031d030a090510090b070305040e09060108010e010e07051002032a162d05030f010b040f05040201080106120207080f030711010509030d050915070216050d 73
    0x440024103041d210b01840500c2103030100d8011a01d036000000c4d550381c2d24010002060420300e0340119103d80001744403815003960003401442522064544190313900103500f0161402d010f0703039101050180340007080020f10700000ca40b0604a42d1280b00a1021a04490480b070982d403220401c600c951303100e42820000c600e480189080400514015030745060031a411880161140720103001181c4161000424220720410010703400c1c0144ca22910401c0d4207108590b5204000d1107030300c000220300c034810441b00c002d04040c100c0041c08010200e4810605a4504601a11074a199584620300e0200c041420003043d000b614403640e416500c07940145c4c2401001c2d43c5c40d100c40d1410748003042d400d01424002427914402410491460020b10b600d03441d048030014005148d92581860b50390504003484003400002080d21215450150049544d54401ca8064079080d90384900007804040c18080c04951600403c20b4036240c048c0c0030008010350389038414004220201240145110b5040e0964600d190035a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 134415017 1250 134413767 134413787
    0x141006050706110d090302070602070509010f031b05041d0105220312020f031806071107090f1b03060519150f050706090c0503150c1818040803190e0a03 67
    0x440074990404c11818034010440307410070011400759012000c2444156010420000140402c4440070764660500c0e902015446443c44008c00708600c54403e00000b000303a1900304050039010b0410810017035400c5280d80710703403081008a0019480d00300810107202200c000c0000d1f25a070002e203111800d0071554100c0d46504181c072054040741d4244001070b180300480b0f00a500a61114059100d0350424500150070a031000c1c00010038440080703561380c022200801c81c07108455030b0500000d003100c0d0502031070010708186044e003040300d0b803064641a02d0540543c4828180d07030060b180011b5428403440c0619a0b60071901429205d5140482c042c0304c0107104800201c1e41c00301e246001c900300b0b030041e80da20095a04540302190f0220510005200c3ea0038100850f10b014403060a00141c9401e2201c9076149a1013866a6031139030742264412640700da180e0700d400103c81c515650f4050181e140506040c40300350030580e01165140802e491000503032800e802001c052044400240c142100790340d4041c3d803147e9030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 134416267 1250 134415017 134415041
    0x50603040f0230031e120406110c070b1206010908150606040512060103050c010203120103020d02030a05070f050f0103020414130f020c01050f100317070302190303141006050706 78
    0x841489802c081e202c00340c0390f00b030300e600700c80041d9124540341c0018900460759280d0400024000d20120380c602508048182d002a08a02d001800040c1c8200100302c903c82e00351504203d118041c800564041075600901d40810304e50710144290700c4443c01100c5003c8030784544410f035032140c09407050001c80e40040e06e0b0007110083c1854502592407000c0f0712111208651681d041c3c0040c0010000c2c401c043c41b00bc4136400307003403001c3c40c40c0241c0125003018015040c000640078165501c405011924100304028001d9001002c443c110780c2d035294540e020100300d0184500071108513030461100c0d40a40291025100c051201f141640018010b100c60ba420503591401c08c5500d6891805241103e84000c01081c10f000c0300101d802c6ca440300c004c1c003034040c000c2e00c5800086400d07203040010800d548415090707030500c030101a41d91300050600f2881c00780e440d00b9400c0c1890100303640b0002c054140d400603000c00e40d40d02d03414035541e40b05150942844c4551140d603021034420403030307080014220361142c0b8545107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 134417517 1250 134416267 134416309
    0x70e1305060418060c0206011406070b060d020d0f0c09020a08060d020d0c060302070c08070509010501080702031201061e03110d0e030d09080702130209100f030e0f060a06050603040f02 81
    0x20851100042ca00f010032016600c145d0307039012980f200741e030501040c0d000d0b05802c00c10650324820b4501181317642c031400d58090440303058540030400a0f0f64103806040e030540c00824468560440342030103c1011824501110200350b9100001554440740c025225018982e8540c50340d0f40d682c2c42d0501001c030700c2d54102240e11140d4510031100190705020100040c000d9a138005889418514102036081d0f82504180d03841c1c0e0083d001008203640300d85100e4155682880c0c44400340c1c9903080241c1c03441c0108401c98040213401c5d000480c0156000c0c0001034040141d85490413050960001601291080310455022500400c0409140c0015030800c0003c030903640b040701d1400c040395190000712120110704940700c00b070003e011400d6180003c0c036012110b10000341145495943e40000340ca5008441040023030100686812808501135849510070301c0200b01900d03400034039140c03815102c1400b1148101002d02e0640041520308068081e01d100300c0c0e10240d4480c003040d9076002c100ca0100f0420a50030091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 134418767 1250 134417517 134417531
    0x60a120f06140108070504060e0703020702120f0a0b06100e150714010e0d0801080a0b10180906150f032303040b0705150c2205040e0303010905070e13050604 69
    0x240e03081c45a24036881101e140b28041e9410311000c103082410a40c012807049041010512140060328050340d040719041c24010b9482d07100d880030400400c055441ca5605009a040f040760450003c5516413003644507082c200c885030707100020481425001d040d1040014002d40400c105424580d80c03e039200340e040f603100c80c2040c3e51039980040e02050407000d1200c40c0d45449201c181d0b4130041001030032411541c01c1558840d1b043c401c1032039507101c0b0308030040d01d80b080aa000c55848032074401c2c0640500003000001c0d5030026000208009404a85022101c2c98030b02007912a00e04214403401040d81c0c01400c10360500d0b403650312900044040e1703c4491031000380003024a031b10800100001c2002707226902c000d035203903102c0c0d00b0071504001c481c1e0010b1864155100420000004074403c403a80000800101141c103031401c0b4580d119140c0680206d90400d15054102d402d5410010107181214141c407000d20055844c000110741c1400e003070002a4026004407400d0303183c1445600013590041004d00700003032030303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 134420017 1250 134418767 134418773
    0x9010f08010e0a0c0e190806060405041a070903170a0809060108030403080c0c0a03050709050109180303020a020a0813031103030703020c1017040308040b060a0303091802091201020a02070e060a120f 87
    0x48070035105181004c1e406c155082203141802d00c0502d5000904840c2004545080d4903003c4041042080101d4040c0c079000008210341d0107000140099a0090100c480045000d2541c2481d588858002004a4100c900017113a1032000140241628100d5000d10b0516285139603007900d030340000e00f00c100340d805070110342241a11110704a00007540100c00402d050fa00e070100a00c2140e806030050912582445594280301c01d4070b03034064009030340c54500160784c2e20700d100080341400103080e4002d0040c907002908800350303000300c1d0144094030f008103a1104280d015004050340e0b8410104000c025030441501c2c010f640c80d04140100746000c4038200200c01d040d00702c1007680c3c4c21408907000c5021521009c00e2100f0301c428070b48005e44c480c000b43d964403001c505644018040455034031030b4014099000c14103a45021031901a520050301c050030842c0d50380c40ca02501d9001c2c0d080141220010300c43c150f0001080c050001c01c4a001d60000f500792104c150801040324a01d40d540c400940c0ca07070005011003400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 134421267 1250 134420017 134420029
    0x20114090f0402032a04050102061503011509050709090203010e040308040212030d0c0e010804170f0d050c09100801031518020316140102030c0616110307050309010f08010e0a0c0e 79
    0x210b100c01c0307820280000880e07810300164010172800d09800c207006003c01d01c070b980d1b0006410b0360002d81e01c0035180c140e98070030b200290142101032040d440e1001800c0001642510580005003d00d000340c40315080542c0301c0d60303184202e0000f44038a600c220510703c040382c04240180c040c0c5410600140c40030034100080c018581c5107a202e202c4800e1883e9441c10380d443e555a00c101400404602481c1c0414141030588521445014824a4410010002403401c2a051540040714881e0741e40e0031007800f0900e002c54080e031141d04035200046c0141c6084000c481140e2040a090781601c1c1d1003c9210344e2140349030100c0004025020a0342c0680904001c140050794081004440004a0391105600f072420401036402481040504034151760090008001451021683c543d200000010040780785480f103808860840784105010074502000541c801403190210003400341c0c103401c1c4c81d5075201400c813810484a2a00c24803942c9000003d0790040390101c0516041802d04800724544a0340c090000800909 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 134422517 1250 134421267 134421271
    0x1020114090a02010e06070b06040f02091801090e0705010909020901090f03080310050103021e0c070317040e060303070809040e100f060302030c0d030507030807051c06051c020114090f040203 84
    0x28142d0311401c030500440d0b0707002c003050200380380030b03a55542420b40994038207004110140c036907480b490700d840711203001c803030241d040d00d4201c0c0000f00044803004030034a4051130070f00300b0b01448007045d05140c484071025000240c60812240183e680040040c41c28200d00000c0d0842c1d4607050400111400c0001c0382c51024006001039400f40303564540da410400e401c041180060340c031075814180140248114002d4040503025105540c1c13080307035500c4054140c5281000d000341c200820b41c0c0034000841c1c145460140261040d100002051030954840301c042668a008a51000b006814100110300480c00d25400c2881400304001c1107958003e801070150782030700e4059408100c166650300c0100103528007007001001070070f8250341842503107803191402003651140c410081c0038030515038049260a81f18400702ea402d0469000c1c000602c1200b220280090841c80c400c2d9842034203041e600c143c05070400341009200d203905071201c840741c480051003000b00e43c110000841e40300201000c1c40425445600080d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 134423767 1250 134422517 134422531
    0x2041a03160c051b060d050138070212030c0a0302281e020a081009060e060f0f0702030705070f050a0e0f04151118030c0d051b01020114 60
    0x54491900040001c0c0345400d15012904004107844a880031410124002d6400c0c0120310300c201107048140040790b440e1041e2040c2d00700c440d14100000401803600c12207043d030180303240002c01c070300d02100702d40211074090300c505512804410080000145090410391019214880681e4144005000d12a0501d4541501a03001d6084050b511031000d0b02000090b55003c042080c440404030103481c0e004d659000402c20210600c0314018200a550b00c0808041c0105030344411514103070300194070880582100e420441e016410040401c14641e004501c107031240b070709901203104a54841c011040c405102404200c19400104103400102e201808410b016211081d0b1052625103000140715118045a100c9003041c0504010b02c43c10706822064150000c0e04141648145030403401082d004248004615010704000548070310900c21100741a884104101d0030345107000d4801052001c83c203441003006240d5003103010b030743c1c4826a10502a030750f00c00061000040c20818083c0c95003031070006846003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 134425017 1250 134423767 134423819
    0x60f04090b180708150a09080403021302040f050105040e0a090c080f01021306020a0203030403030e010e040e0604020f030105100515040b0307050c010e0102040b09060d09120e18060906060307030204 87
    0x30b401900000c002c282d0050a2a000801110f403503400e1351800a88058244804d15483c1e4000d5401d0003400f40540707000c1c6400a103106002c1d542c60140a000307501910540c1e50317030440e4000010702c940c01a020303101220740800940c0155039910003528024080c1c810300b213138010042070001c50249010400000c0d884105030006a54161442d10740300111b00640c00901150b100030440da005860201c20307201102c2e0b150405080c55104500140e440d00010500541c2040c03400442034100e040020304c10b40114020307178600c21640b84400605007a26000c460115400c00d14500c01c0006090420b85501c2c00070b004040c2d1b500349516031001030850385c000d0f40c04100003440440e00000e0301e030080c8075041c00d104940e8003c500d020310303003060394005008131008140b040c0004a070811140c2c10f150031081e85281d0069a5000e81d10b086030028000c51014040c0501941f241810108950b1200d44803034010400100301c0c05007076503807804110507940024038002c00c141e001e000008040c0303165019048104005455 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 134426267 1250 134425017 134425051
    0xf04022206210506010c12030605090705091207050109140d02030102030a090c080a2001051303052107050304030206160b0403020109030f0512070503090102040f030c090501051008060f04090b 84
    0x30902e01180b8001e06241071494501441410381e040a543c0b0b92040d03001e02a000d0394036444d50181c000b051140d10007074021881c0300c1008983c035400702c0140520030049410010040956880550303d002e68080c050100d0b0304010709101c02e002900e000c00540200426000c40c50000f540801d0a903041130703552000e800d8a689030f0404001080001c000030f030118000816090005403600480c16101c0100c110391005802441c1040743d1155040312900e00c18034075081e542c1a171b02d251280c0d40309000c404c5410315801088031000c0340d618000c03c40c1c16481d0850002d40c209811a001c10180d60301540101450b01014100c0000184030b4080352403050b4007913000091a066541809819070024092001c1040400c04c004164003000c0500560080f5007490a03c0c0c0700d9654030701050091041d50046070380c000c0700102c000200486102a0030a40c0c00014050000c0c0c0d88c0c64041c01785041d09528104013140800c4000350036402c0481101c104140020004507c681d0702e40c0340c8030300c00072003544c1d0021090340c5464 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 134427517 1250 134426267 134426297
    0x51c0501060e0115210507140c0a0b0604110f0a05091503100510020a0308040c12050303060f0a0e0403030207020f22050c2110170607110a020f04022206 67
    0x95056040da42c1c00d040720174005c100d100228071001061000c40c1740e907489000c540b42510800504c0d401180c420002aa119504a420759a80d50b041d4000c03140c84541500240550409008003042e490750f0015032410182000f840651981000e80f91804010046c0000016980c44030700003200d61240480146d42c90900100009902c5125004240503404544c3d825000a42c0040d0b61780582c1e4040c034240030140c0341c0380340004480005074054500c28141d11002014401d011000b14010b000495441c612801100d007440102481803152000250350900010f010074000c6c1c0040111900c01001e0b88447c90001c030004260020007c64130740450540c1910401c119200c2c803e894010702a9072040f414920318140d80072240c06140b504c0348a58010401003250b020540b15200c02401c11141c0c04e4605001c00c12840750344990480d440d4000890080750b2940c9464041800c0c0354242d0041d128001000c001000d01000e588288220600e18900a02c0101160702c00c030a40001b6044660380c09892080c208 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 134428767 1250 134427517 134427539
    0x20105211f060207120809040e0d090602060609100e0901020d020703090e060d020906040e01020705030a081b03150f030c09010806071101180209070507060c05030610080709051c0501060e01 83
    0x2d0020000e542c48010103001004801170b8020019510480c0c10350389400060109019200150001c00070380b1410011044031030b00428400c081d9001682141c403a42d541c101004801d40041d2040c00c1c16019441c41400400c0d00070020b942d20014242c005850074406811402c12a8882001900015206c02c014400c11202c00c00d1650861022101c22031016942d8000503500c00c0003922480c810b5a03600381400c030060b000c2d01541da0303054000003078980b6440b600301c0c09000400102c0703201d9540c2200b240c00c0c80003134010400760390142903980d0002c01c3c4d0b1090441846100440903800c1c81d803511945003070904a503a510111806081901f0143c40f0314148880007610805441d00001c1040c2d0500c01c003103c140c40811560394003603404440112a5460303400080c0c0301d502c6002e001410041c2007000309030071941c1180003540501c106642c02880344aa0302e4044411000c103548040c001402c421040140385000b88500c00200d103100603107041c000d001d40d50582150b10070f901c42410185010010480c0d10f50803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 134430017 1250 134428767 134428769
    0xc181e080c0a09020a020c040212180d020712030504050d03030e0d020c03150402010512010803120a0603030c02090a020f1b100603051510050a080102030603010c1803020105211f 78
    0x1640200400c1c0074060000360100c507540074500190380c0c00b00359000000c0c42007011560b20300d4003034011541c803040402c3e004908201101c110707610030007111907541040b0380001d040202c5036070340d40500000b90030400e0080d07500c4400300c401c0d801c0080030700c07000c40c0c540d41e19034035081c2c8140700c1d807000114049104d4255041c031038490300d0304095400844440016450226403908031100309032032212583c1d0740d0310040c0d8440c01180e11040c13070130743c80000105540d0307070000040c22070a10800780c0c80060356614510a0030342d1407502006000481e028603030f40050a0000d0110b404c52a1004003500344508070304070703940513040a000e03001201900202d01001d0641400b0103024007a0742c40040c02001c0c215265a540c4088526980300704101110025940b10281c0100070090701e4002d20304102c89582e003107454040d41003910000e03c41c4d4a042c200000c518082c1141c0d10780b1601a041402c202da241d5001510b45400007000e0040074810380d111a05406820411144144c80c089239104440a110607589501101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 134431267 1250 134430017 134430029
    0x10120e06010b0a11011b0801030b060603040f06020307031d0a020f030f030301150e060a2a030e1302070b04050a140c0306041e0c090605040c030203010e0a0c181e 71
    0x2003001406486140401c44510481d0790801c03001d0074080c614640e004004d0a00341020a13140415050351107907106c0e001c141202c0c054009401075459a2040014a22065030000d02c0040d482005c14001007483c1c010313560000c22418002001c48013010001c1400410084100c03050304100c113036008514103d441960a0403042d0018418080001c41c1144d50388410701802d4071403041c80460300b00072445421100070000b0003400094546d62100005021020790904060f680e04511824040000405401c208803075050703a1030440704981d40042c0541c0441c003070039003c02d05400304285000704030301c1c0790000d0181d807081008200c60b01850030038411a544040c9020b60a4000101150b40d650700043d02035085508003a468500321500c00181081e40d00f048030090410b00d10030800604c903040e0750b1142c01265015602030103001203a5400702c007244024050448040100030100d0403030b00c1203034800c1600040703900b040d07003090b1120b104442c041c0c0c0b600e901402c3c01c0705448000c1e8405604104410005040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 134432517 1250 134431267 134431273
    0x11b0b010f051815010e1309050304140d0201020a08031f0320030a12050f0c010509010509100b0114031f08030a021c020604031809020c030702040b06130b0d060510120e 74
    0x18800030b102c0f82003810f0b0740624100b001502138090350b0365440c03e84030302c041f0b461003042110020904d05681c9a400c40d03c1125104104580710500b0303401e14032111404154164090040d140c41c035521100150009404043ca0b4240303000c2d940c00000a842044019600410b08000f04604d8035007481044030a10030824040c0d044085114006030204844c0c000700c03040c504110361a445004c0516110740104003103440d46600b010b05020721000103510413401001c0407401e54510009203d00202a29070161901d0f0009001303600c0a164054418040d68010100e07040400c40d001c03900800c2c0c0c1812410340c102c551581c0001038880049501080038070243e81d0310402806031400a550065110b200040c40602442031101e2610070100c0c2c4a0782c400023400c8805070440d241c07401209042d550341c0000900300c1c0903910b004112141ca2074242c0c1030b51810f0b0440c00c4133040da103042544940c115003103003000841085d16000042000c0e9100e01e40c01160400690351080c212200c030705c07114242c1c0e02d610541c9041e03070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 134433767 1250 134432517 134432521
    0x606050c1002120106030b0609060441010c0c08010504080301090e0a020f0d0311011b140c07060c0f06060306090219060503060f0a030f0803090d0201050c09011b0b010f0518 76
    0x90410f1078844c1141e0b110700300003d0f06e03038940300450014451102003d074442c900140100b000c03501408110064420042800c0d14040600d01042c05409070203100e41038050008891071980d0b10586c0e006d9040d92082e8000103125640c1d61040313003510f02c1500d044618000100052042201520074800010a200d00074009001d050f004540e54488a2984078010200c00d60f000c002c1c1b60007102c10f241c4009000f802081004440d121035040400844038040003e40e4000344400884449030a031541c280003840907000f01494061300341c50046080100b00c4407042c141e40858082400f91081c5030045010780b03000701d0480780c1c0744100b00300b400c0300c40803c010315250b1010922849034440144c1ba44a101034489140108907072001607128200d5038801004c5d14280d80b141001c000c140d501450041a101e0212a0003d82a070380c00e900342c0d00202c2d03020340803103001e21050480790703c1401400c007800241070285502403959101d0f004402d00980050042a0311104200700034180100402d40c12141d50019020b94 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 134435017 1250 134433767 134433787
    0x10603021918050607020607050a0b18030310060f0c05010c052a060403030203090708060c0a08100303080420030d030c09080a020904020d0503121305010606050304050d080c04090606050c1002 84
    0x6510f0300605024032004030380707941103480700000c8803841c0d5040000c450400c212441d0003540740e070701221710307810743c662807880024030800c0001a00d005050b20901d9070300752400c0c00b204a641441207051700c020044c0561201740815001e1180501c22030365a07441581e20402c05400c1c048030012100314408055800490060a04001c1103980c1c21a601d49400360f0f507501c5014080740b40a01c280c00000c580d029101c00c7c8491075007408001d24840405407100562a5520102034886076194480500401d4180740040c001565080d515080101c07030940702c1e090690400d011910300300c1e4016181011940d9284444240e0780c001c20400d00620320240244002c5001da408104002d6019100a010300b040c12800000c0203030500940e42c07800e400300040304171441c082e003c0c05a50b02d2000340030384480d40780010200300d0324417a5003140c1c840ca4000c80245102048040d04965500000b4070500308004148008120302d0380c58003a4100404190317441d140c0303955000e0102030a18801400c90311900388108121224 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 134436267 1250 134435017 134435057
    0x31a180606040e0f1b130209030d0305040204140906071101060b0d150b130f0602060408070201080402031c0504030b1807030201050f070c03060e0f010b0603011412060106030219 78
    0x4400350540b40400d006240140003840c010742a00b04800502803d21405581c1c2e00303106201140e41011607184210102c000d040c601248941401e0641641202030b28404c198000d03005150070501c098400582c0c1030300e0074814442e5100c103490028043d008041800701e80d1340d00c903135a1a07081d508800200101840c11921400314411008107080075500c82c6403110b8001c041c502820300074503641c0c0c55a0f070744102030650603a13441514016820084120300e0045107940c03000801303901c100d9010300c0c0170740b50252a030019110146c0c000c0040ba450712441002d14102e606c1051120142c081c1912540e444038150300d00f8000800d00240780300b49909040e280304c2c5019000140d800c0840340c0a003000c035564a1042c290112a00c600c000151404000c01c90010030070800740e102801c0350115005035210503011307902ca1303800d80d60400705499014034280010706c100000880058070300d40001b401d15010314002c0e0401410300c0000d0784044080303940402d580b041d0320154103400989442501c1c08010010a14443e01c2d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 134437517 1250 134436267 134436271
    0x1508180f0705010c0201050c0f0a0201091401021504081c0506030c01020a0c05040e1009030c0201031413060c02070801090503031f06020a060506040e011a011202040b03010509130c031a1806 83
    0xc1040504d00c0320805590103041100e10719900c03102a41c0842440081d1684e54000b00c0a0032400a41810f10000d1118121800c15a11200581c003410700e0141c1c20201004001c809801034401a00400000e15202c001000078100b41460080105051030000200750515015200e12815074104000c0b030400501c2458004083c0d4004076000aa140c5091404501e40b09044103124031141c9410307504000e140c0c000c4189442c0d54400d03078081c801d440c07a00a114005c0311058400d07103a150140511440061041d4214401c0e00402d80f0448031080d5a80007960b0a440e01070905803846d820000c140441c94203500305d254042e102c400741d01c80c246071070084001c0da13450300c040e4003400c0796a13101c2c0800d440e40c2d600d030010254003034603a009000c200e00201d002c0944401d01c0758607501241501d00030000107803007402070300c040701d4003001050306580c86c18082c8035014a0041c003543e0f46c0c00d4140300f10306c0055001c022a102071402554400219010026850344031140034161a10403241c0005098003c080011829 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 134438767 1250 134437517 134437519
    0xc030e0607021f022a151312050412020409061104060908010b06030702060f09071d150405070c080706060515040303110105160c0f02040e031206060405060a0c0c1508180f0705 77
    0x6040d40304410a500300b032034070460041c031003051505100c2040310705108807c0d2580241c0e40c544100301c1d170306401c2d41d0300c3c480c0348503005554210320011005407903d03034000c80d9001d01400c800f00307030041115000c46e40b50b4019003204000c1000e90805002000c000d128400509505482e103c1c5941441c40b400b81d960707140144881210258079000448428040c801310300101000b642001d0040d080301381582c84110308417080d0a460602c0401c4862500c0c0602506008101c142c81c1d1000d41c44142d229001d0503405014241e80c0142c407010000380a44441116030034013031446540700c1e100c0d420344c0307401885030440d071070690b03c940c1c1001c0520075804410300c0c407010080ca0358109a4121025440c020b0240002003c01944c068980903c0c41203100e030200060884d0341101d000a5011364414080100b2400760340035403a0003090610803540c0c9540244449080140941c1400d4030827a954100c90601110814007080000c038043e0178000e040500c10344c2c0008412010f800b40000c2581c100106554140e644209 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 134440017 1250 134438767 134438827
    0x4060b0405120c060a0305041e08030c22080c09100b18040b090916050a0b0403140304031407031e0b070e12060f0f0c040311040c030e0607021f02 64
    0x300c00303803000400c43c1100380304018118a80710310340302d4006001020100c03402c2d107180c41070920400c90340c418004030110b4240d0144429007192210080e4800b290810100b40900c00028003030602c010540515403401001880b0080c00d03081c0452040c810011809804484007038280398050100c2c02815058440030104032802e10032165030f9500190140c2000e070346883d0464490000c0c0004800081110b02109880c29034901d600e0b9600c0042c400c1c0f603115072080c2c2034450410b000030b0000851000c955121600b641045134141912501c4800710a10341c42d41c2854150b1140400300300300949801e0b0102c042c500d25030b114400351a0782d100c1040206005200104003c0c41c0e4007551501c0c2e5400c0403012640504200301d584034540480c1950144600340d40000b089403c0400140c0d594225000b2075042d2540301009030380080c401000d02010707100c403044080526440317442d1400c07040000c00034a84902596401003450095210349204a107013079420701c5030128010050700b4501e603c900d40b00d0105103115140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 134441267 1250 134440017 134440039
    0x5010c06110319050c120a0207050703020310020703020601060e3f0f1507020a031d04020307050a08011509230607030507030e031506010c03020f0f01020409060504060b0405 76
    0x2040140228a1008071000c1c0120500c80440080d416101d000d0020100800c0580c41c4c1d4404000d01d401044014104000200005040c549594028000e03d41c070070004c50f0b44150701d0f079001074100a1039881440400e5804617050040c1941041f04038010440343c20400b07141d880081c0801c42140c480c2c40404101c0700414082c4071004200151f15034041c034500c40d14100c0204504c003043e25203400c4211415144070313901f08610011008001c00b8001c0045400500300302e4100e680c1503031a1000705d849071010b00717014640314215448500042d40302d00040e41d50981c1e2688051800740c0002d1041c6c0110199405030301c10840800e4000006405540780e10704030b01c1548481c00e14403440c0798182c86031070750480c0303000c203402c82010b030840d02034144144243c85044040e0707845028159540c0300820261000c10801c00468000d5000c0c0c0700d48a421802481a00c0c141040f00c91039502c1c2c541e14482d8a08039a42c002030802110540e03115840c05000110340520903680b410a07207094074003560081c0d510807a91018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 134442517 1250 134441267 134441273
    0xb010f0e010f091a0d151d0405010608030d02030603010c0e0109090f240317030610050c0a020409050609100603120e180103050a0c050613061d040e03031b0309030405010c 75
    0x1543e00103221041d644507802114028140d0941c001541510405081600300094030452503004429944e680c04082121381d003801103d48004c0000e04169069541c035080400c030640107000030244801400c002580e80e080c42401d1500b1031b0310601244041142c03d51226003a40e81c043d29500c202d8a402da400324601c0f580e86038410082c052981410800101c1660801c3c0c0d0b402c103000004112801288000616540d40e101c810441c030089410320351005c0d4001e008407840e801000030342a109000c1c1c1c00c881c0c4000e00c690114003100e01448050314243d00c110104180c2c0c803010015100c0e0900035a60510010340f071030b614012001040c0c041803040c8115010400484d480340061000500c4c40c0000d1003145503981e04065844000030401a50003415800303000c00d241c00c10100301c890b641311010103c1e803d02d00e404422211041840021900314401c4000d0700c5543d80c0d41d005e01404040c00d40040d40e84c1c1c0c01c0c100d420204c03419070bc1c1e514003880030082c0100001580c1c04415101110401c1c01c200b8011001c500e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 134443767 1250 134442517 134442527
    0x62401021906060801060e040c0e04030c0f05010f050c0703050415051201030308010501032702220603050102040905070c020306010b0a02070f08010509160f090b0f0607030809010b010f0e010f 84
    0x4107103214118020041c0424010707550084400c540101008215050b11204040141101154007412071003010340d080111002d15010f56500c10300038038240e4003a80351903070b035613190681c0c4000941b207580d12440d000340c40f1070491251641000044170f83d070b8500b451030380d006010350180b4824020000042d0181c000041d000d50304030b0300601001c0620036815a160324010380151428024540024503120014482c2e000540f95440b038030000c03010456107600140e0800625403160b1241c820b2100740032010300c030145180d01034600075602c0303900003607100c504080003e001c0300c0e8001c20030003c020741410190050b850208080b41924541c5250075910703062a40140c0c540f0406034080d000760f4244150014a1010661003c0e018089000c00d69148021a00e4008810640e074010224145130768201046070004c9544548080b0384042d01048414007014001413403900070300d10a03404a003401d0100140c070a07003881080c81c40002402c0c0000420140480107185010003500301c3d041c44001c0d44800c0440d4058 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 134445017 1250 134443767 134443783
    0x906092106092f01170114150a0e01021b0a0308030a270b06010f0801090b01020c1002060f0108010c05040302010c260c0f0102040b070f2f1206240102 66
    0x202c0781d010603103c09a00041070724800e50f03010320400c040500640901d5840b50b070300c0c60682c1c800f4001c401030503400c214030404601142c200b0b180d849140020140d030300ca044803000c0d01104d43d82d81c0710b940c07009201c00000382c01c09401e26001c03078400c2c40c1681100030380d81e9640b4042d41600d4000d02050784a42e11001d540c00241b940211208400c14000414442e104083c40800380f0395108501e07200e52904d0701001940c1e1084c0e502001c2c404100d48100500030700003543c2c0a6444031034141304a4a105140c403000c10704075010700460500623002a0100002200d224a15900401112000301f00484091100400c035000ba404020b0400c11424521014041c1d0b015076128915801900f003076100300504074840450b8001d86080400b806009100c40d0106818402e540465001491b100d18020702070740c0d008494207241d4400c030b451240c00001c00103000880c0c1c1e50300031414803951460920804120401c00c082e00d98142240f0140d10130010414106080c0c070158200c003004142c410f40c01d14044005034240011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 134446267 1250 134445017 134445023
    0x302030708040305060a2304060b060d020f0901090f150e012c090a02070b0c31060201110a020c1306080a08090a0e010602060f15040e0d090609210609 66
    0xb28000c400e0110119002e406000d000404005400070300e080c86050805c84820441ca480c0400c0002c0c1c0820059041850b00342c030001c20151a0010b2041c0700c100301d8105a1000544000100da96509944c014001c2e40c040c1071012007c81c0000e2801249541c00b81017a1112001c0002558101c01580d009401d2001c5070011000010f29605d035807070100544000d100c01030340c8140e001c0c501043c40aa4144212220590411280c080700d59800809800d541d2001100243c0382a0f0314004d821000c0503d450341040710040c0b101885550701d8600d0080c01d650740101f2003002a0340401104020580010b01c0c50210441960559149141e0110540082c03096030702031801c90182481100030070001500502c100141100d03245180f41e01e42507070200c03540c024010f440250380400080383d191428801c1107540080e56100c10020564400042801d03520400340301c0340c55600c2b1806507188580c0180f222310150005141c5406603924000c40b034100d010004840e00350401c4140d00700c009002154001011183d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 134447517 1250 134446267 134446283
    0xd02040f090203040614011401050c100e060702060a0c091403070f180501080d02151005030d0f02010c031a0607020a090207080c0d170402040b01270f05010e13050403020307 76
    0x6a5000503101a42c01200c0c2100c5c81c9244c00355403c8914540e6900034146e1750075400c0c01d0249940e0500548966100c04081e0000d0720404c481d071071b2211f000d030054220394540400904200d040408019292502c00740091150908040842d4051548000001c1c1101c01c2000f10380700d0b11002401290030000f45403c802c10342c1241a4011544402d03081100c504008914410045a030707964041540f100800b40c5590016000192400c2c22600381103401ca8011080061030b260081c1e807800000c0c9031000101d0000082644c00450003252034080c450b4840101d40d604043c0b1080710982c01c5210041242a41a80314000108a40c2d0541d10b80c001c42c1c40c083e01d005a011543c49000341011900c6801800c401d10742032050603c01e0101c00c5c843e007441c0040844680b5941055141d6034200b00c0a840c07404075660401c12950107441c403107010110f049243d280324000610304942400004141e41d10f0f43d030043c6040c02020b4110075140d488812494203100004c940c00101501c913494101d003140301c1e50101911180d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 134448767 1250 134447517 134447519
    0x140909070305071b0507060e040e030a03020f0f0325080601080f0903070501020310090605060c100207080708031501080a0e1002030901020f0d0e010f051e0a06150306030b01060503100b0d02040f 85
    0x17400090950607034000d61910500c044002c400c00007030b80c1c0c1c0c8005042542d0804e110101e081d5001b44c0190080107010f20b003c0313080c000185210f150580080310385040b601011500032200c090a6000c64030a02c8091500114502e88480040d205172005003102402030346e40d0300050364288041c001d603407250b90303c10001d66507810402d1100d161240340b400340222141c58900e000405142801c1200c1c0800e03142c030043e03c011300489948200035002100c046d5a440c00400400d00000c91480095100c0d80100035050280040080018658140100003100143c90140600c0c054000001c0440c0c11044840b405070340d0b540c901504d24003a00030340560403840304000c1107540d2648129040750f0f0341007104000800a00c10300d140725070b0683e8800d0b88d5840d1503160110402d40700c0c1c802c240d00039602000c82d01002ca40c260b039072551030031010f44070b200c95000a61703501000d0041000e07002d0301500415040c45e115045042290880b400112244940c1000c2c1100180b844141841d40c1c06480003000b030b481140340d2003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 134450017 1250 134448767 134448773
    0xd12020f120108060f07120b03070e090105100b030108070506090f040c0906080912070201050d1e140a02071e03030605060f0403140109030509010309030c140c01140909070305071b 79
    0x14007400c2c00340a440c0d004140000c2c101102c0082098400d1200713654001c0d068a030400c0130b40041c84100c0b0750780e425008075080824000c2c2410350950180313003041c00000b41352400e1000440a101960030581483c1400c00040164400000301c80d01a03c108031580c83d510f05100e40000d0243c90b1404585400604244c2041d0b180740d0004d00c41d904444a40d01c4d404846d82e9a104100d8490020301100c0d016107005004101c09948204045c0609480c2c2400000d200382c842d003605041d00d5150b400d5003030702c152510b800c00c0d100700382c10300803e822400c0320405604014071030ba2120132082020041e100c002c0c2400c003e8106041c403030341052005040107800603517600848031300c007200d40d8000e000584140041d8003c050321490140300d5112840d4043d43c64509101059004402a10341880160200a90101c840000c03680760031181d4a18003440f0014030314502548000340c2044400300ca2a0850b010501500c0b440b40c9600d9582a07003d811481e001074559526041600e80c0c07800c4601c03d01403880c8034401c40c020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 134451267 1250 134450017 134450047
    0x50d09060206090624040f0e330a0e031b01020d06080607090e2802041e0f03021519090302030c0303040305071e0302120102040e13050d12020f 63
    0x68652641c290380050b80c411002c10764070300040d40d0307080415000c521510350444000c003030030704052401040420304421050080064403000c0c2c1040c05150030481d4050700307a01e400c0c01c123825030b803500158258464441150800380e80c2401002c0742080c2e0f803221100b050079a1f00384100ca803005802041c01c80b014a043c55424008c0d0000300d900240c0625144000c6144a800145a80f01c2c0b18070365281e810380e5041c40300b4000c078044090722020340030300c5040352042c42c070400404440c00307224425030044e21a450a89800e1515069071500c00030005409802e000503441141423206480e01514108190010460119030398414088904514080312030002c8220707070700c010701500f16802101215403e245040806072030f40f045110013040340c0d1040743e04101c500306280c0c40174004030006034180d1140303a4a0300899100303800074205a10503580003600b485142c1039140c00700e4120744000d507e104042d04c1a42c0303007a5107000390101402481020014846628510b804450b82c1013100703140c458903a603401d01c02c401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 134452517 1250 134451267 134451269
    0xa02100c0204060e04020904110f120c18060604030f030c0b07030515010e0f0409062705010c02010612020607020a0519030605010801022511062701030e1216050d09 72
    0x211660070703c480040c50340d01c06050783d405543c0007484007200e510f580c0c0d62100c0c60101400c85076000343c80c2d0f00408140e07940b042d0780d0300703c0d480d01c0b907020300a542d034903008101c8040246491000000d0b0728400b4040240c803248203440c00d07240c1c080c1c9400310070b401034101079030440c01e0300300010201a4001308004606d949034020034002e2201d92144144400208010b440441d00145542c0e0814820b01a80c0124945500450201401507038009074001c0300c94203d000280e5821f00400d01e008444174403504001003407060221000c034500c02000300c54100824100c908000d0300005e8407980021418605564803c2c03400030042c14001c1609440b5030b00001030b506034508601c026500103192000000e00c4032810700031207132a02c140c80078503140c2030200c00c01c003c8a0004034900380c3d020340c50840900510303140c400c0281160140c1c074040154030824040ca881c4001c6560503018100744c20145514022040040d240500d5804030444035101c00c003074844c1e0029622040c5001d403841c071850650201450b04062204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 134453767 1250 134452517 134452519
    0x30b071b170921030a051309020c0307020306010e06090109050705120405010615140d09030210050405070504061502070605160609110f06040e0a0504020f06070303060611011103010509090a02100c02 87
    0x4601c0d022a12081c030059200c803000c0c6554100b00400e00d82c0910460080c10324041c084076070610b96231030318003a600f00d0f00002004866035200181243c19443c0800041e030040c00d4041149150349400c2001c18502081071284134009a10b03a404a58024091402d4420702090b10000d00e54915041c284507010304594402c803c816910308103040da1319442001040902c2e010000300c0740c50107107512580c1c4021312500000b503007107018400c14001100001c0c01440d00440c0034a006103a004d0070700c0204422240c03030b81d02040d503803480c80c9007072882c403034001c41c1020488030070303043c4652182408850041d54040c04000181042c2c40d18007500d0810002107280300000f20159141902c0d030100c8410f0001c81d100d0390007081c506841708000500070241300e421540c0c0c8144060b01c4d018000d050800810101e8000b00e00440c0441d80341ca0082c0b0207154020b10741141250140000d01c007000840900c00f02da4441801024080c0b14101c2c00110aa10304012408556501030454119012944401003148441810403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 134455017 1250 134453767 134453779
    0x40e0a1a0114030604120302070203030301062d0c0b040c080d0504080c0d0312050402030127060506040216060b1c03050406140a09050d021f0e0118030b071b1709 71
    0x8141800c0c4810b40a038401e0740500101902c0c3c855445070030001001001c80004c15400300100d0005071070900143d0300810850b00c0d451a0000340c03807030216001428144415207513204c0389040c81c2082d4051030300815140c1002c403100382502c2e541441d61103c24903400100072403140500d0341416543c0310300144115003c86050728056190b01d07007007006100d0401c1000c1d00148220184a0018a4a0b0311481d00b00e44001c0001924000340180311070203400d6a03140c0703540c00802c40c0414080c03003205e0040302e42c0400221b0701140360002c01d4041c14030f03000785210058040d558400e0400380075200c0d8a00750030801c1541340101f941402e946001016903002d4059040003075696000002151081c900b0354a250145031180d1302c805003081c05100c01080300c0300c0141c1c2d0101503d0150740811408007100f22014007690b48001d284182440090807030a8451290303c2d003c20a51f80400c0400da00d0440d80c0d800000c01c4c94846543c05141841c1640903002140c094070b40c246441810083e400c5c410000c2111076011748007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 134456267 1250 134455017 134455019
    0x6010c02240c161403120f040e04030f030c0327080702060310230d06020a0e12011a06040e041113020a0e0a0b030411040c020f0105040f0308100f1202040e0a1a01 71
    0x50131500140d503084058040d4401000c4030488507002d8050000806288910750402e03940310540102d41e00183e806070081600400d407000314540c0340c000d942d415503c0d81014015800c1001e01590811458000e04c1c1200002d10310360340422803040c04031514584c0080143c0d840703042c0000b450748565898803070b405160440054170035410305040704034001c0403002000080e0702c00072a10b49001a502900602c0100000c0c400301c440c2c0b40d40c40f1a81d8284851911000103075a01f042030b040c032050486000c2d8544101424001084902d08031041550b0190303000070080780c548a2040441c00043c107203a20407540600200d8100d440980c007030400c0085c2141200e4106585694190f40c844134030043ea4041c00403180241803140500b02900154100070451040394103d00403002290f086842c04c0d85c0031512140b041d03403018181948049919004034588221910080c0340030440c004003029403240c100090601e1011805664659000310107901d180030558160440a00d03290901c0400400020902c1c0040c0d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 134457517 1250 134456267 134456279
    0x1b030708011104141203070f020a0b070f0c0605040315020f040f14030c1210090212010608030c060601031107030e060d05011401021204050307030f02030a0c060c110102030306010c02240c16 83
    0x5c076202411003040958604001900c0e441101240000c0a90300400140400242d190450001308090f40c020708081ca840201480c0100091105920110400009000610125034482006608140351500040e41c3d40031320300001d041c1d8001c681c0005a0404060300c0041e0a0702a03840803056202e045043c0d0740c0103100042003217101425029260031070f07444503c10615161850b804510098001030900c00c2d520340034000300c1c2c2500c541d03802c0039a054101040341002c0060400945420020034201400603240e0500005428003444030040e040050302900764074182c5444080340d0040c9451101031020390f13103440b482c05507201000c002c4c900501c25100741c4e03070040f4004016a03007698002000340001c05d00d0350b10340061180490030140e9050103051000c0c0e0000740002d09080050880e500d0300c0c4a551060304103400302c643c00300d19060640d08100108512a80e02201044141d40e048500c12102d09001c1c00f0540d00d03400d4945094003900c40020000b4008400140101007041c070301001e8421181c40350 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 134458767 1250 134457517 134457529
    0xe1002130f0f0605030c0a03060806090109050105220813120c0608060904020604090902060c0a030807110d0e0909010b0904061e18030c020102160303050301090f020307021b03070801110414 83
    0x8070030f8000048060000c038840103071240060080486502d000300e0000d848840003400d005041e00c0c11281c60707555610a8003006400e0041136401183c1d070810302000761b41c84580d0711038a049448000d04d140d200040c4810007601405d080000b82005140003c0060503130302e05500c03110300324010031002c10040c80024a461500c150807500c07695000e40400d003441c2c5445c240740c01800340800c00700c0c0d220f0f80030b1007102d125800810083c84000c2c000c1ea6400c4050506540142000400000d44013480d000207000c0c0383e040303800510044d03940ea8143e417150f070310707a42d2411002e0062984200c8175500103024800c0c00140308494010101c4e0072424415100c9030100340d4041400c0b907260400758607071209100217020110340034030741e4a0010350040c01a41c9403641c0d8440b2494071070109400071800301d8004801400865040e202d503045408240e0002c40ca942080c14020350fa0308807a0010450590050800c04c8480e1024003400f4000d00e04400203201c0031a59540360180741e0018002e1041408040000c00c050385012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 134460017 1250 134458767 134458769
    0xc090c080609040c0e070e130507110d0f26040c0e06010c0302150406091707120e1e130f0f0b01020105071209020307030b040b091b060a030e1002130f0f 67
    0x3500921144c4e2920100d01100b150003054181402964509000305413100030700903942134265a0001920f1400134030103010b0101202d074403156940400111036080350410340601d20040b25080c441880032031031814202c5107419900c4080008980c034140402c02400b038100000f9210400581c0e5401e64589004640010010074080c0059000d200c00d188901c0e04400d055030020301401c00802c03031010540b152011954100c00e50804c0b00c10008100301840800321000103208507519080d1002c07100c20b1b00140041c1110460a0070803403064a0060541c1e0341c511b843c0403048045501484401011002c800040034070042140a4505205408000390f2041c0308a40c45004161504403000c402600d5150041c0340003070081343c0520959401101244001001c1485144640e003030b801289860307400c083c20650140501101e007104040304026030361b542000d5840c184034074034001503521b8036a107a082c548030302d10200220031031000558251020780d407801002500e0340300b1014065981c2e5a2901020607030301d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 134461267 1250 134460017 134460023
    0x201050c0a050417030705070803070312020f03010e1e1e0901330902031003020f0f0306060f030a0b1e18030d0c0c050111030a0f0203060f19030c090c08060904 70
    0x4100030900000c2c0d0b0704c02e0b242c0c005440a400704e0b828201c09179640c6241c61820b822001c4070b64000700b540000c041e0300004401c00800002025400c00140381104211400180a407000c035290f480c0004e41911100c0c41d95100c64041449034042900380380c00d503003030a45084520380300c1200c28034000500d529814000d00502c0c0d0302e45001d04041c5010b50b44000380c0324210340464001180798081c006018061400614000c0d0000100b1803c070303d2440c8100203007984403580b103a004682403045004255004a1442ea02450aa070103400300d40710040000d0414004c0b402c0248452141c501388007050080d001c1d00711144900005c518074903100c45502805541c0f0000c041035499000700000c5020102a400c0b459031141242001e1920b0700140c0d0f00c203802d5030018810507001c1e060100c1040707501200c03030141042d419409001149142000c0000c41c1c0d02d0308120071058000c2544101c1c101c100303004038210300b00654120034604405a22a206400075040785040c0c8000039083d00085451454001c58890050b0b40c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 134462517 1250 134461267 134461277
    0x60506010f0c020604061b080c0c01090503010c0207030809010302072f011d06070303020408030a030b01021009030504030813080a1a0609060f01110309060d02090406140a09020d02070609060902010201050c0a 91
    0xc60310344d0487e18091401d08039440c405440da0701d20000f4204502410301444524054025140c3c000001407454102c2d6003c3c52003a030400e00c030460243c4d000300300d80c001d03a900320a949980743c1074000141c000c0c1c032030014001c0140d5003502111024440ca00f0b0041b06001441c00100349140000004403020462060248402c4049820390403aa2074030900520446111317081c050704003552604054219000080058007294031000d07640d28547e41801b00213100140000100709004958078014218040c82c08000c007456000102640c10741c101e00b0f02000205050710844031030a00510b0701c814081340907500c07006c404074030101149152401d03008044c410900a45641502c00c601401103818a034456280c24a9000800008d8202e4030f4040003800c1007a0400d501580d103140c060184000c44809901c0702006004280b20750803684e90782070300c041c11944c2e039000240c0c8950040032a00000e21904c54020401d91410101c08200103468102c1000b240c000d130020045543d500407801d440f446880304090000e8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 134463767 1250 134462517 134462519
    0xf0418090515040512040909050d02030f18040e03040602210304020f0405070e03010e070513200c0c09010e040b1303020c0105160203060705070c0b0a021507020c040504060506010f0c020604 83
    0x2c04108a01940503000300119004448682c1007414680c1c060380040030302c4d544036105031040c04800c2229401408807403008519001c68210103400328092800003680c85c0c1c0640020400c560b4840d00f1604491500100b07407580c039a61810040c1d5a071407aa14102c14229000c22007152401525050724415a0040d2180311030450500810004220082c8400b05110401c1300e02c1681ea00c003403080390f012480d01c100400c406414241045029500e8004640e5082e04011803041c28400d050b00044240c0e20030340805440e6440c02d400700d414034005d00c607102d40103101000006024414400841e0140303000d580d1602203911051000c03007080c00b80c404044c015070b2022515000d10351143c00281020700e042c0e100007450309840da001904101058403074200041c00442c0071010700c1452208040100700203100240340c910aa207010391148080b00588040020880000d66014000e1020150700c5000030400c00c4103290600d4114000e06d42640c0340d500041d1009407084010340141c0301991000d8000300380030f045c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 134465017 1250 134463767 134463793
    0x10e0c040e0c07030302160305031509040c03171c060312020d0e060904020708031f0618030b190c03060311010f0c020d05011103040f060c1b0b0903040503030f04180905 74
    0xea0f1001c40d04904140d420000d28800e8194000501c3e8200c3c800c3d03860503a20b08101455901301d49420180354030031507401083c00009200891a482140d6001c4180380d4914402d20342d2144600032070b80c0c1c003c0d01c02000480d8900740c4500740d1200060f01d2040000424034452550308a9807070000e9155440481c14041c000461441d1200140800f1440200f026150034641c2e81c84d607a060f0070a4681c401c00050030100102241c115025903c003030286450195072070307048090303188400380f640d01c070161040a800c000300c0c04600d402401c5846c25a2104403e000c003003400e100003401000b140c0720035170f0320281a04140d0b00b55882400642aa68500d41e200c50700000345800b0040d8004000d03404944640d070704c11900180032032400146104034002d4560103066032560401d181501c40e400b06031402c002c008010b03000794045034552600704070303002652840c0c0c80d518988131500d140b1658100303582c5840089aa16580c0c19060010701c15501e0070f1001c0030408041d081c03024245c2d040a1001400da0700039484440e58 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 134466267 1250 134465017 134465041
    0x8032a042102150c030405041413140102070b0103030f030f060b070809030a0f0c03050f01140c180604150306090504020a0312050913060509070c02030712032303010e0c040e 76
    0x52240001c100d4560010803190110f401c0d031040081c502503410100e0b00f0481c80c03a051040c4211030081c0e00b20000c003450100000c0f10b015034507080c010440408080081c4c0d80c1c15003541913440340c030703845106056503507141c0c103015084038006a04600024101422500506007500a08085410345030800e414910266240c1c04a41c0203110680e4241c41a280000041020240000301090164080070511400d44c24814113103843c0c1c204a081c540e0400741c0507204180000c0384075501044002c12107403256503290104415a200c00c445680c4030401160114100342a080b80b682c0c1c0f440c02c0e481c00c2104503910700700c000603240220b030045e41c0182c404c1d200b0000b2038090203952420b5050b900d8050b18107442500055600304281c900a032207555111814041c50410b0418150403030b03040c0c1000c154051440e80000e940e03176041c0c0569415440d5280d402003c00d8022000600009003400b480c401448485010075a190001d125031035001c011500402c1c04201d51500f12001d9407503108100c1013a0b0f442c240b035003036 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 134467517 1250 134466267 134466329
    0x90612061b0d11130801090f03110f0105160e0102070506070807031206030c1a1c021b0a08030604060e011802031009021306030f110d0b01020a08032a04 67
    0x1000388802c00216440c400c2620a010210480d102d0307140d11642c09560306102101e4541080701c05a151440302d0011400105c0305035003403941032401c80c4032007101c100f202d82800803424003802d4540c2050103118910100d11a0107500b440166a07241c4c41c4049000120fa54600078070450f90018000c01c622404160411300074041039000f0b007030982da99403c2920720390803071380c1c90341c01030381e011080d4041481540100c904190440840b143e001e81006540f060241c1d0780c91240c01d94000c0c0d80c0d8001809001c06030b5100d0b0b0641c400310190151441c070a0941442c030312941c000c45286220350714141c030208114241000d45070580ba18143c3c20b0f039540c1c40c400b11020003940041c00342c42264140083c000f90301181c0380001e00400c11601c201030600c0d0b19050f4040c003a100c0c45e00020122034200803040018403010070587c4c0b445014410082103802c04000140c0c14a800d800001d4055840001008040910b40290194040c8000c0c99551205001200c070302017409140110000c030008000400080502e280f0301075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 134468767 1250 134467517 134467561
    0x10c060b0d0f0302030405010215010b09010c021c06021b07061713020a23060301050312070609140607090506090f01031509020408010605010e120c19030602070b040209061206 77
    0x2802480c0903868031030b900c40300900114016440020140042d5a040c0680d07d00c412104802c2001740d41003900c13091050042240880c100917440c10030b40c080d136454040103040355004066205140180d4140729019610401c4181d800d060030381580c60980d034000851000321071803565400100f00d002d0b20501c040b04006400201041c1c51080d56001503620035980320001d000c584109242c0151030511500400d42c1a100d0520130501440100840c1d1004a0300c8006220051034107952102c0502e01400203008290b8054181010041c400005a0000407058003460f40c0b500d07001d03885541c0e0410024030303205a41d1181e421606000700514954080d07082220400403d1011080007610744920800302c2e0001d60140259a449600400c51035800800541d040c03a4250342c600b146000e22a0302d19660050404500d000303d01140181c0c00c0150b0194a00000d1944241c05540d10f0b0918204840f030b124055805a01c00e003141d0b00403848518208410010020051016006580d9104842d180da48002c100c61 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 134470017 1250 134468767 134468779
    0x80c13050406180b01020c031c0203190201020405030601090501120f021804150e12180a03080703030501030b0f0f010918020901120309050a0b1207050c0105131403040302010c060b 79
    0x411103581e03074003a01d00581100180d100480307034165010b01c183c500d880304003030564104000e003076025100828542202c00e450146c80d200da5640c014100e245108100700c3e01c044507210b0000c46901381e419001441100e8080341210b4650743c888941c1c0301118020301c20031206000510455000030b41c0050007503980d0307000a1001d442c0781c01c1e07841c0d48070240c01c4c201d034110741101625240c034422800710710584078001103202c020a100360300100051894890010031480c1111004400300040ea01c000c11030b005141c1c40981c00d40c9501c0140707006070142400b800100c451041d69000207100342e2041280510480c02c2c6400d1507416441e000e030410051490701c100360b10021040c034001c400740e01d6200c051070080c09860980c00070900d1508000703207214040e0300200e10a205072a010040d008045041d6502080070740c1a030382c09915020f00c1035034035203d4888c2c4804076500748001c0101c80c0f0110070510308a14010341440341c00c90750704100316480c2c4c412404028046401840030758003154050780f02d14032400d006446 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 134471267 1250 134470017 134470019
    0xa03120605030d0804051e0303061306030807140706050315130b0406080c040b01080606030f06010c020d0303020a02120903031606090b01080a050f030403110d0c090204081e030a080c13 81
    0x1c43e007820660148a0b01156088040c003041110030041440101420340b040162515002511516480007801681c8102440f00550f05503000c1540904000c5a02150440d60b510303680c5006041e40001601040352030080707180c00200180280110303849422500410704607103002808200d00f04000403c03140f983c0c0e41e42d42b60455140c460b4861480503142c10802441000c0044003000305548195401a04010202007030080540380c0c40b042c0c0741c0007070909011400c56614400100d41020f884d40001e5840202159030009140c0c150340144a15003490382501e00c504a00d100414a520405413103507016801000002956101c0760800c03e941b034400ca501041d0801d403034845036048202030f00500c04a801070510003040100410850b1040d24041c0080c1d41018619103a07580a44901d003d1113000d58142d4a41c2c504214002c052035000d042c48010071034440d500ca02080c0c0e0703650782141f9030908601d41c11800c0740e1005400415110304460550704c1404c9030340c84d200501c0c001d40014440f50b1041031002c00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 134472517 1250 134471267 134471269
    0x90b010f03200d0603060e030a0e12030c030307030b180106080c0c03040f0801020918160309080d0c020c01180806060f030703150507080c0c0a02060a02070305060c1207110a03120605 80
    0x402028003d081080108425080d400c141e070481d51040111000c1d9030041203000c5180d5000501e00c0f129080844007070710a4441200007904600c00c6283c00d84041c04000b00b0000c0043d015840902114010f0715203004185084101003020b5000b070240b400864607500006880c01c15a0009018103080501582d0900755510442c80b41000315400040d900d940109c0c560300300b030400059141325040803080319002c60030111000c190321403040e00c0000070191106480414807007400b0403500082580a410803500f07030100340094540c640b10780c03002d0018003099514900c030a0100d10751401c0c0c4035810090f150b81c2e215a01008001d08072001915010301403030900002103100203160450821079040c020400f0b250480e030042c03d09070300614503010507000f4014200c03000c81c00905154002d03419951141d8904850209901d02682a44010030701d1080c001084031660604010f410714107414035101e801074442c40019504025854811707043c80d4003180c100c03004039109007010340450003162030020762261540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 134473767 1250 134472517 134472581
    0x6090221060d0213060e06030303040804030201141c0c09060e010215040c0b0705030a08010b04030b04030c020f12010603060c090510080408130608060a14060405061b070e0907090b010f03 82
    0x4e0750000e110780c0d07882e4204a00c001030381c0100d5100000f20044c51540c0b40c41c0d82c51415a004501003c1d041000c00b5a8010395442200d0032240004440c107041c00304400120000700180040845084c00074010b000c00050450041d0003c0c019600140c001d010446043c0d000258056401002a01c0148072a0302c00950101050001c10503140501c01560755101c4544002e482060b0681c00452140707001c03c401c101080300c50b00c101c0c0d08140d2601d48101c414149000044004094510240e030290501020a2090f030301548468101c0c0d03c101002d0091074540c02d01900c1110391842602d4104e03441800580c000381c820022031340e026204010050030321a41340c190242030a1541c001801003500030702444030074500096440e0040040d845011542989000859410b01031881068050780300464040c039100a0010a050501c0343d8404440415a0350030040e1030b064810f580b071000e58001c1c40c00200d030201c028010b03091041c40607103400d031700c00d01c0c02c3c40114014001e070b00101c103440082190000a8500c0700c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 134475017 1250 134473767 134473789
    0xc050f040315020d051f0e06090711010f110c0106090e030403080307030e030304060b0306100f060c030207090c080708160c150b10050c010c0915110715090906090221060d02 76
    0x32401100800e1140400f86260f0701ba5801100c20f045024080001030343d29201030381c1e07121110713240c44650f0030390441015000d0030000c81504450380c1010701000340781180c1c2c40a0444e03010700030004d101d4195194901c0080b140d41800d0700798160030400c001c1c0301107100b07140110381006444c50001070309003480f6011403c681003550103c40c2c05032143ea02420901d004c01180b030b0081102c040b80b2100b40e18000c8101c01584280c8200d9042c803500070249410326000f40700303500040c030020340b09010000c1c4080b4010944407007120f860010074200c0700032849184d1241103a50b64a1032035107400d5540003103511280341f10210003083c142402d49808500c20180c44040c802c41c1d03510155101d240d1240b52089140342580c01e40700a82c41080310307100c2d007000720700052034800c2111459420507068000350600c0090030581d081d00080c8007600e90162040ba402d6101c4d807914216641c1103401c0003415141c2010701c1c140c0c80380c03d190101001e81025600a00c3c011b6100e1140c110034000d040b03c089a00b2135010034051400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 134476267 1250 134475017 134475031
    0x406020304030906021c030e1203040b06012006010605030a0209060a0903030305151c0f1a04020406061407031107080d030e0105060102210c01021c0b03010c050f040315020d05 77
    0x210901c0704042d0010b0891000d0000b0b40050b10500f1919031280f041201448510810117413603414619000505000210800103115501039403443c1504107841c44d000b00340d502600040c10f045299802480c100f000300318106214001d881075920713190044600390005015100c500d9402c11040e502555290001c140064441d02e85000171450350130301408440d802052210b450840c40da004070280e42d002e40100d03d6040794540c01107072900506000915680c8680c00804041c202c079070251114200c0d40500d8803a6200f2607062144640302c000032038007548511644248140c041c02520002401034265201e044100001c035050742e42d40e400ca0a260841240004010170f0b561940410003d100307014565205100b0300040900b0010b030b4080d601c401700e100484a0903140085a2545807031070a404a41508080f05901104481c000c070820000f4039404850300d220f58030740900030001500441c01c1d10065a4000706203403c280c030310340302c540e044404001400880b950030008a4482c5409100369401407503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 134477517 1250 134476267 134476271
    0x2306070302100f02091c060905070e160f050306010f020a061503030329010f090302092d0c0a121104090b03060a05013210021b010c080406030b15030406 67
    0x40e04a030b28001c8451922070301c0e5070b49004201038281a2a403140d011050f900340054049190598108400204a01d030401011400750810014034134501c403140b80d000d030b0040e00200c2144c03507008a00b544c8100d030303140c031b02e10200c0d0062000030300d1076000d90002c42c01c25005006035500b01103543c1e68001115411801c1d000c1c200c000407428014103900d40b1480c01c0305400078880a00c0218440001c0301c4034194219158100800f5500d000c6500b032203441060010340c1c0c00303031030640e59042420703003200050192804400e41041c940c6041c0720b03c0c401c07003000300d000f03080545030380d0f2130300c0a0384204544048500a03400d5425485038111300c10202180c0040c0010003921000103195030a100030142092006018008014242001031004501070513101c1420038105050a0310343c10308010500c3d00c0c0c4801920316a00c00040d114203044180c010179030075801501481e00320504c0d48903800548100780c0015011709071820510045c030003c0d0003a400ba41c40035400410200d461200ca6030465801e40c02224121000d035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 134478767 1250 134477517 134477533
    0xa0522080315010311040902031305241501090b090a0b03010b0301031208090303010b093105090a0b040219050d080901260a0b010e03030a0201090203070b132306070302 74
    0x480c5800e20a02c010900e81405841081c09403a1007501403030040e000301d603900001183c00c0001302c034144440c0030350100c04e40700001c407444402c480c050541e0000328034104844000038191b03c0c2d03005004140b400140c450382800e500b0328481c1d4146d6044180003a4002003c2c920101e0001c0711170020b10300038a0005250b1b5603d40c19441d18085460b90712481000744a1100c0500072544408415241980d40308040c003a01c42e94200000f600c0000c00c540200000307003070303101200c00301c1c4e6820b2401520013102140030300003600c0d041c220542d1103a2800000d0301c0300c000c1c4800f0070010320b052110405042d070030103401e0002e147c580d00040c900300d6032004210b50f000da0001d8800100c0d40c100d106d1400140c0031080103903000300540d0f00a102c20340020095440196550400c0d140390780600c115603100c401c00f40480e40c6615110308040d000b4031205078140c0c820301c03503104001541313030000080351a84003c40c1d0000b5031540c584006003036024841000c2e55040303201c1e000501d80d6900ca410140000c00d00036401000302e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 134480017 1250 134478767 134478781
    0x6050f130c03020c1605100302030f070c030201020405041b0314010b0d051906060503040605070f1b03020f011a0306062e0905060706090614040c05010e0d0606150f050901080a05220803 81
    0x47d80c0300058140f5005200b0808404582c0e04610f90103100303400c00300003480301840c040740284115005203600c180751045000b06e01114a11a003100f03200c0f0348040104103c00950201201000d119401e041e1004101307a038011042c0c0c0c2c21064001c0d203c41c9501b8a82100c80c0354110998525401001c00030f0030100c1040140036060050300d810140034113090482c0c03922110010141000c00c401c6074603844d501c110200805100300000c136130344411032008020841d11502e01041c0e005140b42e43e54400d01c03030b207000f041d00d82c501104c940c90604508541d10804c6061000c90080000140f01928248000d002c00024551180300c0140119849210b0000d0403040e9860107104840e908441800c1c03000000d01040002004041000d0a80d0310034249441d402200c04009007140c01c484a004180314200407000480c07035008584405104030340e440b480403001541c2d004640724040d10a44500151915010400c998403560002c2c0e04102812841518030f101c07101c0e00c8091648418080f208404008100041d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 134481267 1250 134480017 134480029
    0x3060112020705060f04050a0b090d0201060b0c0d0c2306040b01060e01080106050d0605031e0616080a0914060403020d030518060a0b01050702101206050f130c03020c1605 75
    0x14000d00351808509240d100e4450943d81e031001481c1d05c0056a10801250500c0010404940155130180e1070608901c2e00089058540c61040800d130095802c00c007001c112501001d05907415100600300038513440250103821201000d08040a841d0035264030303130080c2c041d41051080701a040d40440141040c4c2003510b0310881859059012100700580c03400303c05e03821381c0d0004a05044500c01e10f042501c0300300740041030380100203503400280d0620800a00b10b410300d2300510101410a450070540310305035106c50440444541c03140c0c0f4003002440b61070010342401c2c61640284451801003d039042c1c090700b0781201519002041d141034002d40d00090744003a07030303a1b0316005440d441800d1030340081200c800f084113695651000b42890081c5a110880c0c6e1040d64032030801c0d6640a5002000f510407c2031004c0041d011500400c02d403490f15003418408035950070140442c7c0c0c40e0807406040d0358100501d003010b4038010125036103910704054081007001e018682c1040800c0140340b0002d2020403075407030b00d010008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 134482517 1250 134481267 134481287
    0x33c090f04020406211d0a060f020a050f0a0201111210050307060c03080a0902030d090e060901030201140915040906081b0a052101020418050714090411130b030601 72
    0x1205500421082c040c40c0c4e440201c0001507101e4401c05c40007030070002d0460010b0541d005a044695842061900442000091800e0302d0390182d0030030422005004a00d1003070307225500038440810010800320b511640c5800041c00c1c18020383c400006c0351220801541d032164461000200f036010a1030a005540c3c201c0c0c2075200082030201c0007024124542940500300440a09019090100050000d480441036402c00402240d0040c1583d40013400d500d400780c400c1c5501d010300658004124002480c0b030400a052a050300c2c1c050f160003415826514107000e0961021403100c0c0c0011010b82c0c1c00410801c014041d10140c099144040b855504244515140c20304400042c0368901c4140c1c018420354880c1302c038102c1954016149800d142c4201003007400e100032501e10002c050361002600007001a0048900c040c1c8000c2001c00340201d4440c0501210200d8480025200a1604001000b407170714155100d441044d5a45900b0380c148000c81149855040183c0c2c41329981620000130845076686c0080e01e51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 134483767 1250 134482517 134482519
    0x1060509030f0c1509040902060c1e0d0801030b0403031b1e03050103020d0209060604330806011202031504140901050c070b0f25180504060602033c090f 67
    0x210100e4000c3c00000c200e2034861040c8a42e0000c0005d00b800316450b250007910100d90041c0216030b0b211000e00101d80d4844510100b01c441c901d0411503c000381d003010954604209440c0e441c80324a900b1503c40305120300024004030281542c0307400282c4000e001c001d440800f80d07226207402c0101c92107c11010405c10300001c6c1342c01054540320052005a0f1000305040ca210b4060743e84a01c15a43c52010501920654000710104081b01d4048044002c0020602403000b10b0340440b000c0c1020442c10a40d450f204c161100c501299809941219058459010f954001c0407880078188200013000410111001d082401c03a0852556080010001b0240580e83c0c019500ea4201c602e800301644030000743d4500504a5402c0c62240d10200d1501b00819100c192140e150701e44c40107480e05000000340030805001c0c40e5210307071301c1c3c0c50000060902d40b0740b161004890098028602e4507881d0b00803030080f0b1040c110700091100e80050f41b40c807040c0003e61842404104904102e030f0320701056003046403c644100d282 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 134485017 1250 134483767 134483773
    0x20601080d0203160f0f0803090c040525020c0a03140f0a030f051303080309030909010602010506060403260a0503010e0a0614090a060302060a05180a03110108040303110301060509030f 81
    0x2031071440d40c0042101c041d10502185001e0f02e4200340b40004400302191405022000400880405e024070900210b02404050080311090300e20081800240d0748104c4407020801d5008041485503104032003544000c0c4454419a048040d401c4001050008039800036242c41d00381e02d480d140c040d00b0400c03014420000d0f803c02042d81e49e80958001f00104803a181c1942000300c017264035402c07a0102d0203101c0103503520100054492400000c2699031f6001642c0b003c2c41511000000540c0a0040c85950b01404c400b80c81c10380f509042d525620000004503074845880d18804004418803c40355014208524407540e070580d89525284004865005c042c10075001940341140400c03003441181800c42007403074107440d0b140083d52483d1255004000d40d6001a400510002d00700706590f0303210000300b00c082c503110b581102040b00407051088603000360100400c4109c4404c00e44695601420b00560710a20030b03d800310302c42440c680342007801d4100f039200300046800800c02100c949028440c984140b0551002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 134486267 1250 134485017 134485033
    0x5040f061e20090607030e1e01020c0103052a07060f02040509010807050a0e0c1b0609070e0108060126101a040c020d1d03010e0d0305091c0509010905090f060102060108 74
    0x11685481180d1146102c4e5000007040d2003054001c00d94890440742c0101050105940444010201c241f1001c1260040c000c000400740158040e210709070113032410140f051740d007141911040e1269081380070500851b400600000380001c00f2030080801c4241964005612946032400344642c030581a0085807040e0041c8030b003400f843e12642034800885127902003003641512214070307400c107074401d50042041c45054890044a4000d000507414040c540c1c4004884032659200d40451a1180a000d07140503504980010490000301c140580325011100c014401c1340421510361614104100c0d4170866a0782d00c5100301e0b2103028005400c50798a003819242030012070a0408001c1d101c1d00c510101c2403c1c0204a510303201804010160380300100405802044503a262185455454202d528100c002a05200020381d2003280403c56545101c409001d050080307060820030744040e0000c2c1000c43c10020300010015982c3d4600c10143e0207400420240c0b00e15003004000242400701c140c122810766400112 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 134487517 1250 134486267 134486321
    0x215030906190605060a0201091232090604090902040b040b030c01030e341a0406032004090207060b0306060a12050f1507020c04091505040f061e 64
    0x41c20359105014445180c145842c900c0c1660051103540c0280d41c0040c4045507031040c0940540c0560000c601448805903007405004049aa042a003240d4503440d0707e42c4030094120224003d000710100314805041820320700900081052074100d98072032880076442d000d103d02581000d1044400c5410140d8080c00a0705220380425aa640c40c550068109555120300c17490210041c03002004c01b820708070008600d90352400940003145261940051004414200054415000b943c1c1046685809140c5402c00e1b00e400c405500821840000001841c5602e40c10b246a8540303000400103000d4031407005884400c00d0500100f1140c41c2c5119074080c1e44502d0a20030390380d07107098400c002c4130a051820303424912640740c0a420310300b020100030704505c0307038000c01d05410800c0e01c82e55118918135422a10b50340740070001c200541e0982d000c05001440c00b402d02010342c604136040998414000d171080d130700c1200c0c541c0c0d86a081700e004030100e107880b0040100c00e0000c2c0f007190088030b481c403c000012607034a903036882d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 134488767 1250 134487517 134487523
    0x919080d060902070b060f01031103090d1d011403191b020114040c1518150f020304030b0703050903160506010918020603060409050709060807090606110a0201030b01020a1e02150309 80
    0x241061f845140400c100c2081d41c0c0c0f00c4d03044840701c203002118094807810300c20f040d42d961301c1000e004c0c080070448000000f054400d10104e50284900142d41d50500342807810700c0703004164805000744480b01412140e00f000d0600c1809043c80c1c00c07054281101649280c820000e08403005211503c40340001c1d00144400302d01e154000501b40d403c45200044a04942181620b54031038504801c0926041d8600c002a021406000c2c11602c1c40d03262a02190302c2c00f400822030b200d115600005120312141c0740810031492003944003581c40440141128074007003004581d1703c40440310600427a2558004401405504250701840724100c605c08034401e159240c80c0d001500d40d020092016000e035036512481024850100500300081246140400200d5145c001d8182c5038512401420746481c2003c02c0054003d20840c05114007000c10341c068519504154011405810308221150440c8a045102004607800d5090740c8454061140d011200c3d1003103105028115440342c40c0381d1a090810720420203000008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 134490017 1250 134488767 134488771
    0x109050402130209012703060605030a0c03060c1101050a0e0f010b090c3004050c060a0f1419080103140a020307091e020403050303060f0a06050d050919080d060902070b 74
    0x2c0c040036032a5410303140100c84020050717035610208108864806403a40d02e442d8503a007035030701880b01804a075480340309141ea10001c0f000022b100b1013020004001003852a03000d25032018441c5000b451001c501a503150a580d801e461480020303030380300c80f104c404400070816520b034a2309000080c4945c41071a4001a5480790003400c041c103c0358009401d104c400c601400400710340100b94080580400c2051412044034130844040300c0e07600c40c0000e0740b00149071040640c0c2108032580d035034408408601c8070481c0d510805507110160607605200107001c245070300c00500100761031580c0e204929890750400c100c00346018644c0c821640c010f858014056180491002c080e2954840f01162940b0b031402c0c00d2070a2810010582002c234404180402040b60200041d801810300b00d8541c0d0096241d14200042554144505408518108841c05103200c841e000182c2c0508584d01341c8480001c2c041009511103c0c08030200c0d440b0800085c1d0410585140c8a018090910014114182240313591145a28440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 134491267 1250 134490017 134490049
    0x60a06090e13020301181203140402120f0303090a0c0b0301060203040b0c2406120f030a1b0203160e0a0606050f2503091409040b0a02030603160315050109050402 71
    0x400c20000362103050701229111003d501400030000c0c1e048043c0300e1124100038050440e4a105408000342040784a406071003031040c52030b01ba51201da00c56074200b158032000c14080440d80d001d40c02c20011540da06001071885194000c010705002c60300e23860220044e0685400c01d400041e401c0c0014800c0e2503000003510b0943d203500981070341d182c0c50104940e1501080210003824105000c0d102c6011580e0340c0c01d003d00828003512103900c9028880c00c0c080d20786190b540455060791052101c00c0415110780c0341121080300103218020701000756004241801840c10b07e041d5801b00300a03040000c2c1200120035036200f0403400080000c2802c00c54000c04a1142c202e400180010102d5902090b00300d00b030803c0c0081c4010705030702842c3c0e04075141c0541a00d80354400c06281c03403410141c1c83c0d683d05090754420b110b66070010b00810207070340707240f0908001d4001a244030b0709889403140b030300c0c0240114000d000c0070b5801090700c0c1d0502e505e0100c100d8141d544c1600f01170345250604040c80016200e5100c000c00c0045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 134492517 1250 134491267 134491289
    0x601030f080f0f0a140a0f08070c0203150411030601030b0606030a060b030901050a06060c05030f07060603080a080906060f0303030f19110d0f0c0c140a0213020c06060a0609 76
    0x111820309410301c0c082c00a414050400009440310070f0300f8840000e00030040c05490302046810003244c4c41c01d071800b4000000001c10b56a03100b942440b407141304520b9203c032050a018100000e02d4011074030b4148201034000e0400190024041840700c184c050100000c412401880990b0465135407280c2020050a1140148000b2005c19840d54250700500064040164556201d280240c803081c043c0c079040c0c130402141440d1510201d4800e206032810380304560800c0c02140340003022200d88010394424082a00c000d0354442001c400200c407130000380316407991a035070560a42000a0750380c0c18044040c00d103901c2a4030380c080d20301c466280401a280c3c04402c08280b8002903850400942d9482241d1019200c4140750545d10003100c070801014105a03c017400040200020803c1100300325100c0702016808030f1a0822080006071100e011000714800c45070942c3c0d010380c410ba020503000d14882441c00c0c01c0540100d62072241c5e100030406907a00035030448628070704500d030600c0640000428007403807506070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 134493767 1250 134492517 134492543
    0x1109100309030210090515091c050702060405060c07061103071a070e091009110a0e0d110406090204050906012309041b050307081003020a090b18091c080405060103 72
    0x98000d00c2443c130070a0806000f441855440e140c907a484502e1042d1001c51344170950302107041c0400024000d11b100641c01144411301c03154140954a5420002007242d011500704404920345d1124400380040e1800d8000500c1028149130011303000d04020b60110b500b541c01803180001040d5038448c1d000e03c504102504d00c1c0151107940341242c1421600780e410350072202a10611a980f0544c110032411505003102c1040002e91552040105208001c2c3e5040020f004104000b114644990200380143c412044070b5080a00034010074140c4419a0144003003941c089010041401d00c42501c0380e000c4002d00e000182075030405120b078a016480c400c414494000030482d8121030700d039580141c0ba40c940d60101070104400c46c40d0010070550046034814000344441001c100c80c05d0500c503000701070382d5000f082d42c80d10320301b060040d6005108500030154082c07010300e5843d0340ca00042c103441d07008449500103003c40060754400041180541c0040c4810000410308100209401140c6141545d40c02140c0403401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 134495017 1250 134493767 134493773
    0x705031603050c07150f020f0703020108070903050d0905010e0118090209040b060f0a02070608070804061104120f06060b070201170606091305011a03090a03200106181109100309 78
    0x10b401502100d0300e03540300d4200c000c101c0c9684445e407000c07050072a5559001a43c030794242241c48080b07610200e4401d0303100000030310056000d40354655201c4c0c0b070307464402095030340c4e901c0301403a01d89903000b010b0102d80f24000c140401d5a00c000246503404080c2800d520342e5242064901d0601840c0c441c00c66225804110362220341c0c0c45421140b40e542004080c0d070f84a1101046082c030980c01200c030400903103d01c2c0e0b4005185800792172040d10500880e269840540c0d1292180c0c03000d05404280e9001c40c0c2003c01012602950348610030b5561400382d51000321018403454500c080302d03026001200546018040440141c0c0d000c0d07101032080b40c542c810001641c80307200128040d805608000d03980700e09030081c40c40d895a442e0340200d0490760001e070181e032803118500210340c041c401603842440d241c0080d10036502081c094010406135804176802d502c0c521110002d090f08450564000e80750100000380002d0310316509000d801946901484c900380350940f00c00000d40100c4140f91010309154540d1409014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 134496267 1250 134495017 134495027
    0x71103120912040f0509010509040b0a020a0c0210020309040c05090d02190b04061701050901050d060b180c040315020301060f0822080403120309111207030c0312080c0705031603 78
    0x1844442410706480d01d03140d245641c0300007054001e4078010760346c07040001031900c0e1200282c1e0282d50408010b00301c80e217038005108044d5000c1100e10041c4101f0801010061b100c41c0c0740d400112885a01850301d0350b51680c1000165070700d803c251401c00c4070600c4140500d58490040c01e000b10360450301901d4058503600504198003145d440702c140940045000600244c00110740d85403450410300c01190b50f03886104005005000b07005042c0c0001503450041c001500c40d610041d500400103145542000500c00b0002040c0c0b000c07591115081804a410420444804003c43c81310070469403c0d0300315810510000c2000505a10301420002e0f44c0380443c0103254001e000d00781388a20031000a00611039402d140f02d01c0d601a00c002c031a85000c910b20b01d20a030707119204080c40e2a60010b0010b403101003030804c21100f80070815540d066801031900000016010f051010004c503c42c5a10403826000201c010300084030003800005003107070030441d11000840200448a0404009a940588101c0c3d8101107030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 134497517 1250 134496267 134496283
    0x3050a03211b121b02011506050a02060105010e120703030f02010e0615090417040803120a0c0e101b0f0201030b030a03090306050a061211031e030306120f1b090711031209 75
    0x41a146401c00003607191706420400d0420010074510684950b100000c0700c1c10b2003299a11001031b0401d07801800b556100f07014160951200820f40d100642c135550343d150911800740e00840204540514510306181c080c00f45280c5000382c84090226450042c00b086400c1c450b8541c1c403482418400700041c10090001500200800d040310b140340c846460348440341d625482040104d040d8030750400080d5081b1201c0c018038000d10380e00da4814100e94111020311203030880305940c210500102815070383c800072180c4071007501e850280804211050450001400320b80841161074080c5d00042550004203410680110443e940510000788607954080144000d1000360401070a052003109203405101e0060040c116606046094541002804400f8850745d402c20001510940090002460516048c025004403009031820f56140c18240f240b0303141810381100f03440c0340380b21070480308500b40d0401450443c2d1141c900c2c01d10320380d207a003d2400c2070344da070113100d40070b144400d50440020000002404110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 134498767 1250 134497517 134497541
    0xa020304030c0507030507051807050702040b0102010e150109060605040e130303180f110a1a030402040204091b020c041e051005102309010801061803050a03211b12 72
    0x1d44005e40364913006485415621031103104404542d100080c2c191814025030040700c15803200c03464004581e007440301038507280050303030b05555032166490100c00c024010301c5400c44c4c440f100719420350b040800d0542101e045400c24010050140001e02110000354a03107600322151403804800400e04e0b1404a0291448070078100c1e86020405140040207011941c10f910341d4491980d522030050002d0a00170007100f14130070800301130140b26401d055500a4801582c010b40007610261400340c4a001c01801d0b1141c1c110a00100d54a443c216004980d040c0001c05070010700b2102405840003241d10740c00364003160002c00039090398038800310300c2c0028840d98110040102802c520b6005214140c0034281618070709110203a00c6c0d94a2801c01d0501581e0100c4080a2050716171142d10390a03c031089500c00c28000c0c043c101c0341c1d000b49012010030410030003600751911941c0d502404901e19841041000d011130b00300c80c42d407818800c0c84956400d06a108203030007840e0380350400503000c92100c10b00207003040000350 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 134500017 1250 134498767 134498773
    0x1305070e091b03030f0a090801060f0e130f02090703140a150f0e011502120408010b04110304050a080d0b0a08010603031403070203030705160602030708040b0c0a080a020304030c05 79
    0x250424484000c0c038419888541035810b11aa401540c05403081c2c60300e08140c3c56041000000200c1454902600c0c202941c2e103003c65041c0d844450702401c442458210412003411145c0c00c100f012041600694048009102d0100343c0c02556164180b0619114000344640c03121000103a04a100c0e5201c0c1d0030f07084403c0210a09800d10502e0341c8001e0000400c04c4540640d000d00c04a0048050103404044075003104520941740c2c07904040c20210f450858102007107001d602055408120000c0c081d20251001600002d9084248005c01c0700325000140c4461040e1018000c0102062010451100054001c070a0b179035102c00021095000300301d80c074900c80e80501c010b0404200e0400c15841242920302c2034407404101c541e0810482141d0004840ea4001684100000f46406200c2d0b0060035100c0501d46040c40f842d1070359070b10002660030403508100040d80503010042072207200002103421a00d50301e81c461525500309001080e41e20010508448039400002003010036204107401e2110603040703025 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 134501267 1250 134500017 134500019
    0xd05100608010e0a030c020d140f030406020105010f030515071b140f010b09040318030c080607120e0a020609060421050d0f0804030e130f022203020315130507 70
    0x220402020a40101c008a6180080d2641d00400014401000340d4158440c2c101d108070070b500700243d640085401700c803c01b48000d19002440020040640104482e602a644590810f40e00071700b10b41050380f0244800e48a030b82d080000ca080070507443d0b441d07000800380890580e140b400907038081c40d240c800004804050b2900e8410320240c0c0e406400c09501d408250b03011101894985802d8801c2010516408000c10000c2000240a10489041d144004600040140d5280c9480f5a40c4001e5888180e0325007000e41049140b42d800152180d59244000c004c02150400070340c80c035038034040100000d000380c17400281c0010903540c0400780d400034000c06a0142030341014860102e1125511903045815114415041d202c20740103000b40e120584a03655480c41a940e162002c490380c4001441081cdc00c650303012140c6608034644e000c0c6512320300300b04002680d55420040c005800ca004841c9450380284e402d6011320041e5008101903101c030459460f20030013a100c007502e82e42d402c0300d8440010403034402d200c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 134502517 1250 134501267 134501293
    0x503131406130303060504052205120f0712020a0c090b01020a06020a030606080c0c0607030b040b0316051002010e1c05040b0301080705010816020d030c1b23031303060b0d05 76
    0x19803074602d80c402c0c0e070144600f943e142c1c21b200071f46200350354210344842d803a20010018004c0600ca600e05601030401c803020900c29100c28040c9600c00500c01401080020b084410700030000e415407024046072004005003e8503840c0c2c200c0355a01405100a000d46944c1510080e030300c2004085003c3c0e8000e101199200201d0034050001e250b079100b1000414800c100180b042501181900c40201c407020140400342d071409403c1b0010002401243e0384142c2c3c070810750b46191800c1200481070f0b01018254040b16041c2000c00c054540c603541c240045a0500c01c0b0a5524540480d8820748850345040c00c141080300710078280c51038007941d005520710f070002000004148030300052080031034001382c1b02c0328410b440d020890f00291034691004000341e0f001c0a095000144280c1c0000307a40c2416141410190b0101c0405400944040c1e906a8034042e0130081d40c1c0001088803580442c2045260027145851304101e1140000364407444081c00c81a517840d5038244586802c0003200c2100d40c810709449400240d14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 134503767 1250 134502517 134502541
    0x20d0209151c031e0507151418101505121903030b0a0f05030a020f19030c08010509030313030509010c0602030c2107021009020612250f0503131406 65
    0x105003940001c4101c131407503a08800c800000c0348070034480d50711186018226202c8460000803104503860959a82c8040c0c041320840d244118021a881c023812040121014a100c0c900100c0448002c05585088404150141d403500b558048034425500740e2450303218084d000341488460803d4690409160b851102059899444071058241c100c030180c0d05103885900160042050380070301d5070140e000c003d5070001751410300c0c0d1000d45400014458414200041d02e202c0d607070b034a5075100703c0b03c00054100505c5010420300034240d00a00384c500071411460030b0711500742d4440c40660058148480045d4215160744103040710014a030300700100b55a28181213850500030303808880700c240c81c0c091846038a01c4900d81e0400150042800703900426901610011480090054072012a84101c08000d024a13070308030002c0151060300500c1c9a00c00b01414101e60122401a0f1400325041007004040540c1054101c01900c1e0014050525000105e00d145881c440701515455814058894001001118410740f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 134505017 1250 134503767 134503819
    0x7231507150e030702010807030f0e01060b090a050f0a0b0d0e0a03080403110f06010902090d06060303020a140303041212150b03100b0c0604080f041a0301050907020a020d020915 78
    0x5080c08010742d6400055883e12801503120003800100b40101041c10a4402d401041e02c1c07120000001a0b61000c00d0001c07802c6400d01d512010036003001148808061401102580080c0303000d88d1241c01036566003001801c444030500815640420206415a441815a00000c0403051b51001c44400d002d01c1d05000c1e0108204407003c40c0002c0e010100015a01000302d0703003040b07a049090003010141d0a200032013011390002d14420341c10114a00154011501c0340c0548401103001c0d07005059100c0c03150034002e030600c21003810424254030400c14040040d080d0500820980a2490280d078451110fa04810280000c1c00d9003120000ba802000325504c42030000450284141c6089100101e960341c0b101050390140406104290b00440006004612907038002c124440c505140c40b440c15403545520800c45441e180b85058201d000700042c46181054540726402c4031250005042c00c032215800111510441400240100f0400001c645103401c1c042d002800300d4801080069991101c084406001d032003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 134506267 1250 134505017 134505053
    0x90b040c06050c100c12110901200a020405150301020d0b190f0308130f0e04051b090403030902030c0d050c040506091b0a09050406080d03060807231507 67
    0x25000c0024107540100101c826030420080604072400e9505019801004101381d818240300304540d5500e03860f4082d126001d070418031108565183c0c6d1502000510707041304540020010604c0e20040c4c0081040010b200c4440c80d030403500800c1c983c0d291104800064420030703c05405600101e41d10004c1005038004c4035011030f0640b60b01e44206400c0d819000448401e00c103c0c04e0a0300c2d80750003440481c840300c0040000a02101281c06016614041104500d8950340101160310b103190034441001414451000d00f88005180389404182d00230000f1940c1001400c0101415900c1d22200c046450900c00020141801010034442d0a22410704a0311014021070081c03249180c07200203800f5280494609006d41700320040580d80303004e80e51307a0b81c1d103a503c10074590781800b00454000403140ea59009000150138100c0113402094070009000c0c0641c0c0303c0b030708003000603003020310103000d014440302428404081001d00442c00840740d01c041040406426602c1c00740c2c0d000000c01400f84007018461210181e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 134507517 1250 134506267 134506283
    0x3060c021005060a1d090309060301120519030f030b03011104080106060e0306040b01030f050109020a030f1b05010e0112020904020f1905030c1b0c0904060e150114060715090b04 78
    0x10f0f50310100001e05416008000007106280903886040320f0b0581116030101c2e0502c112450702000c000040c009030000d80c8454410202d41c0e100b007081110600400501100c0c22a0a40d142025590003130040180c240d440400c066070703642404151b81d000d401072089245a080c11340d581d40d486920f0075019181034001c1c6400704403000510030f510708000502611543d0040401c01459003076540314184184030082c25030300381d034070b41d44040e01503520840703000000c0d8071942d02e039900501140313880510359046a00c0428208001201004242d8000840c01071910342440c0c21400c1d9140144804001d02820668541051000c80d4408221564000a120307004552441c1c4444c000b4461003180d07144011034a060328903c09002c0c070f009858a000d041611076951005464180c02e074a0302241e4424400c0714240d442030748076802d61001103000d22001c21109820030b07090300590b06001d0002041c1c400d00755540e020f01d00003d501030501062486942c0c0c200c0038000d09020244450800300d540250542d4292800717a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 134508767 1250 134507517 134507521
    0x1f090f0c020712080702180106030c11010209150d0603080d0902041b170408090405040609061a0d080a0302120405010608060606041212091a030405060601080f0a0c0903060c021005 79
    0x3400040c254048071070002c01c8060f040354660b20f8090310740140408030382082e05282400c1500c4006400140a010716982c0000d01000e90b040c000c4c65844802040e10442c0d00c10040305089031a0600c9069001c8000c6000070f90307408004c00008014000340e40080e16031540032602c01d400f0045500500701c01d500884060100308210340c0c00780b141580500038400402c081c032480704159041e10107160782c014000c446c040e080a102c44080781c1503030743c01c8400f2100941c2e21407969080041601c80d1089941c2c00b0704441c246401e0003000300d00374a1184401401c1a007020512401c268441d03012a45131801440c585102800c061034840d002e00040d01800c2400c1c020b12000a0341c600b0034905480885403a1280c50101036400e440d80c0c0c800300e0070041c5c12010808210804200418500703001c1401e0400203c1e4140d03217241c2801d24600300080906400d04100310502401010050181010b800a078907120000b600b4401c2c100550b148215640000e10f128201303640350204903008165200d01c00c020350070610281d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 134510017 1250 134508767 134508791
    0x20706140c040e190209060a080402040f060501020312040c0302040c2c0607110307080105010b1804020a080402130e0d0305041202010e030a03090213140610021209091f090f 76
    0x2401039020702682403114500164407516001c0c1361100700c903a209401442e1507203410110f00f40364042c20a00f070102d040309040c03000f1420b00380b10704002080001d204000850074200005d48034071400d00d90030300240303d02000c24180046814054019940100100101c07041c1c1000549081e01c1c1103462000342c00c00040f080d24049840c04c0b0301c0411728000340042c0c5010403135a903031034450400300c07991501440365803004512070000740b04060180181d0040d89449050301c03810115030414100c0e030240194014820101c81903006400f40f03411035412104200201c44610b41c0340020204e540d001c00c03c41c402c108808140e07540650210b030080d07005142010403a60f05040503800d840d00f00c040b46410b40d20403c8485030030382c80395110401c041e01c000c0c600d008414400401c2000d03114080c10303180f00c8403000c0b0b05002039842c0c0000c1021580c02d450000d050442c001d9240307140b05000d43d54405024943c079200060181140700350032040307040e9a42d1a0f511171526510b9a40042444020900c0520301d050101040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 134511267 1250 134510017 134510041
    0x8060a05070c0228090b030c0303040503100203040206120f07080601021606030c090816140108010e010b1804051306050c090d14011503051f020c19140102070614 71
    0x1c1114142c0318866550703002e6080c00100000103071034007980019101564000c1c0c0300c0c0e10740c100003004400004a40440c920080605194190013014440c0e0720421041150391404126405003106840f00143c8907a59400812220320a1035940e14034021408100100710784000b0042e03004a001e0b64418040d40e60790303001641d07994140d10700a801104d0301581040098400d4104428100e00d44c40c00046040c3d40e00d084a140004050090f407110405075014440403039000f0309000f8143c030901c4c00e41429403600841840311441030040c3e003607480c2d000803445c1d120b403407124103100040342c05482040b0b11301c0d040d00004402c0c03072108001c4400038144008120850001015600311206c000c0000c0c5c01c5003040d584599250004640c514895501e80c0b0348140c3c2e070105035421f03000460045000c3c0c10004a0940c3c1294002500c00d01e00342040e00c103001d07004108000040b5039a00041e190300c030038419002c9041c80c0b0304104d207410311034030326600005406081200c40e401c2164040c1d403c9000c07070742c591610401444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 134512517 1250 134511267 134511271
    0x7030b090c0307090f12062406020f0d0201060b0a0c03020c0a06121d100504050a051614060412020d0c0b03090d031b0f0807050904020406050c0f0a1e02010e0301140108060a05 77
    0x202d40c140307403500400821160b40c005032440c1001e030a00b848850f980140d00f814500396500c042c00ada0020a040044003c091000c2c003004c00951008011050414007000007500a5082c0c040800c8040392143e82014000c01064120400003051209400c0d44c031000101600d150030748001c60b060500308909030b001201c40071b540242d030101010700100f07a6640390410080c40000c100351040e204401082011a0040c0705103440008100c000c050101e04011000c0c2011a080711503a0184904100c00c02c004001003401907040f0341d044460f01100d03440b500b8502c1d040c1c131454015070480c000010900109210004842c4800c1e0002e840521050400030740144015903017481000c04510040342c0011060310500750164024664200b003410144000007240498005400074004078500003014040c0407000c0002610440c1681c00610400d0340f9075881b8440b46140e15480b0031008102600c100031680a014060300800010300208214102100d003c100c40e0001e22903209207000f074402113582000d980c06103034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 134513767 1250 134512517 134512529
    0x9031e050714181b1e0c0105040302070e0415020a030f060902090a090902060306040c12020c16080606030d0e040b040e060114010507170a0c0203060f090607020d120507030b090c0307090f 82
    0x40310780091302c0c2e4245107680b00d01c0c20200c441c580d4809400c007000004003c0c0841004000002078145428a406403901030f00382c015003064000b190820000852a00722940c1803401003c015849945003e0203071301034000d4602c00c0000340d0814001003120304582e40a42091903045403004802c550718510002115148032000c1c0d003281c010000a201e50600350003441084c003903881c02c5054801880001c000f260001c1d904218180c01ca100c000214100001c1014042c0c086e242c00341045051000010341d031903941846920600c202004030717000c0d41d0380c2c2d40d015000e0904050000e001118541c04400d448103824040c9480090b0310100c00c162651151040e20320140e400039411844902030b0084c03603072070381000c00320004005640c55804010b880a1121601032001d218240841e17050031610b290804000a2540085500c1484003601555110801c4080c034400c0100009154540c101c08402810382004030540011002041c0000da007099002503204138040d5a5804406468030010480c41d41548201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 134515017 1250 134513767 134513791
    0xd080702100b0a151b0305120f010803030a09050c0d060f11090618030106091806050c0a020304050906030a0602040617060103110403110f1005091504030309031e05071418 75
    0x24004003e00c03007800c0c41d0044103070030304040407200504d45c0e558400004101310002400415145800184564016000060140c440d04258100303030941c1d6903400010110031500c0e885480b10801c0c4882444201c20b01c2d038003e024a13040c4005800c1c088050715141c0c02c10695246490310320000381d01060251401c001004040ca0314005800c115128401c48022140c0d070f05542e500c1c000954030240d8855803040c51001002401422081e0600d0012110010072410001c2c000704244641264040304950543ea01140c0d10b207540c1d00c541000c6442c107141030304001c0c0198400540407540d180c00000b40040000744c0072428800f5a40e1600440c15110400510b9141c050248000d0000a015200030300e03908201400c5190343d0022040014000c4040340750b40c0001c201c00017418a4603061610070069030704402801c0914262030344da401055645e00d48409401905420b40a0980800b580000481540c101c01107512181d25001480715450b2034880461041007400c540d1a00c80c802c0000d024403a401c01040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 134516267 1250 134515017 134515019
    0x118090e16090b060702090901111303020103180803060d050703050a050f06090705060a1103130e09070e040503090d151a0f012607170a050f010803041503020d020c0d080702100b0a 79
    0x9025140354058907812644d50ac83c0c5640b50000d200401500c102205100070303002c480d00d50300024080782c0252030000030040520204c003020a4028080303a400200503200522044201d00b000e608010040d00000e006010354294a001c2c0040015000c9100e54184e013540c2e42600c0760f82220f1ba035641c4501c0390030b4000605010b001c1a0380c1c0500c0e070030061406100152031070070352100038250300d0811542101002400e81c0701400b0020904000a00181c40c82e05c915440300c0c1402c0c0c80301ca0303490040d00c01c071078480c100e06040c090030041c1494101143d154060402e0100103004041c1c1c58a20300c001c03503418003c03e0312090500f000d61190a00e103410354003014034209481040c00305040200d10003001d00041c48a60b5040505101c4014002031003170260703610000d45c1382018140084c5072881039100c000b06910512091014940c00000b03084455040d041c0141c0c1c7e84155140c03d00640108441c130140c502400c115045426040300900780305107010b0f425200d00048180c1140101d6000600c0e0f507800c8484000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 134517517 1250 134516267 134516269
    0x4140a080d0c03030605090709080d110a0b0a090b090a02130c0c12050405031005010503070807030c0612060509090307140102041208090a030503031609060503150118090e16090b060702 81
    0x201c0c2d003040501078600414015100c0340418441142680ca01d00003039a1000200040c040602c10f11712400ca0740c1c40d2644040210481603551a080100060b011244032004641c000c0d641d0b84c0b145012690041522026203895881d203034651744042c1c4264021595645001081006403040e44e00c14482500c2d00e801c14441070f1119000c0340290601042880030400011070142e904201000b5440b807042e801040a60425007030604040c01540300c04125030010300c00f4070000c0e020441c0541582c2c9503280501c505154103030002c000c0c04113648021b0300207403000284004c008e07012000f090001c0c0110b0004046502ca05403950803441640324802134004285544800514508000c000040c4000d002c000041d40303e4031180d056a1050300d0400c8104400e201004c1d10541007140003000b13000505005045150100c80c1d0038051440404050410106078108c0401f042843d03206e0000d0082c650003007141600b9800c0072981d40808a500105244000200144440d550f0203084c5600d040500118180b21040d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 134518767 1250 134517517 134517527
    0x10b041d071106150a1406071214130e1e0a02071401140115020604080d0504020415030321020403050d0e061e040f0e0615160f060204140a080d 63
    0x989010704205040210031200e80d0208500343c040d91000301c1107880150700740208a10401c3c1c41e03003c1000da902218019640d0ba42d401c007a120003940069541e070000341e0680e021650399401d007220301e08134003000c600090051034282105081d5012291004102c2e19510344407620b80201090740407054103503500048041480360054200c00c0c1c85100107070381140754100e501d0b0035185c84115101590145c40b0040160840f10000c03031401510394006031501e42810b49814401d88038600c3e40e075072940c0d1110081000c40d12aa807101901078000001c3c1c008040d1a0b20b0000c1155401d0102c4104600e10390a80c3c0340d00541620868003260ba100000b00040981c9a80945500c1e4545011070f0b03022605011104019140c1203001c0714840f20b141c01c1640d0786061407844401c9540617009045680c0b0240c040002c10345450300c0e50320348641e0311170046440303132141400c4424030886d0206c01004000489095400c0050300e402401c06e4441036904000001030200601081429a22401c075060340201640030825000b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 134520017 1250 134518767 134518771
    0x30c020303091002160b130506060607050706030b130219020c030c1f0e0907020a0303050a02192316020301111903050c070b0106270605070b090f0a0812010b041d 71
    0x110280e42d28140c1e0f03500c5130042c2e0702041f100c071541c207509440e100301085030911071182c2c07211007201c8103810712000b0b8890700d541720007900803102455595200314415513241da95900602056010070344d03403610070101c0240d0301003d024840c000f6104107003d5030210301d804968040c0d42080540400b1550003c48001010444105051801d115000c0c469090325101c20081c14400e14464000b48103141d03081c03500401321070004260034803003441800900904203070b14441c0b110101e1f0300c0c988078908000304840d00562140503902d0641d20000001c8151040329690503102c56940201c008125080103455645002d00c030380001d02007404a1400a03d03091800b07a070005801c0950b03500c62900300350342179448140301207081c0c2119012406c08111007100d02e44118415102e0502820a481481e00e0004c000e0013a00a100c1e004000e00401800148a0902000043c45060400701200c400940c50300300b5942d9540580300c40c2c01c00c509800d0021a00341132203c09c550454400041102c244403078800e01c80d80050740 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 134521267 1250 134520017 134520037
    0x703170912034803040807081b0105010f050102060a0e0312070c0c0605070623130f020406030b0106020d030b0913060b090c09030c0108060d030c02010c0c09060303030c020303091002 80
    0x41d00441a041c0100c0b541c0841c01c0702c2c08030180603d4029907415208a050000b40c2d640503400108104400100c00100381c0398007907803211540da158a20901555003007040c1c155005210b6191100000300512180c80a800b155801c2c0c0903500c2d16243d40d6030742e00a8580303c1441801651041100208100c104401c0561000780c9242c044505001c0360380c1c002452200d5804400010383c0411030400f80041c6110b04200360070f0383c0b4150400880205451680c02c0401064170000380f049901400921140c01c01c1190215402071040015940303d140030035103141c080c080d0400600c2105850380d0301074001c0c0304400c00640b00501c40682070341c0346207c50044ca081120101c0c1c0c15625500ca074288c07600c40c01c449a000d401155881ca4540400c001850703e04014420181d04002c200e6051213a152138420680d252141c051400084c0c0301d1103800181d4810005d848024450300012400044046075548a901624402e0b1b8003484a0003d0140c120390b039020544807031f0482e0700040034208840210b41d00030320040300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 134522517 1250 134521267 134521291
    0xa0c020d0c090c18052202070302101d060408250803091c08060d02041b020d0e0a0f0e04020a050d060e060f0103120c1704030c03020901090c12020903010212090102070317091203 78
    0x31070241d06e40140d8010f400c003100943c0c46003031881c0810410f401800303600e41c5900401209149803a1b0070701e9803880c0252005d81741c1d24002902540c1400e03042210945076221089203200013070f06141a24a039842100e28942c98000c41035900c2c050b400c008411540003000d80c0d032f02403081d00e4034030410006440710355089078415921291600000b44d44802e080365080d07250050500601d102c0000f91042854070461445400c02110038440400900543c8040d281c15810001d015034451000c9034540c002c81d000700e0380c030400e0800c12404014454020010708445071060f5640e64607100000c000000d002c1c040104610700409554604034480c80c189008a4020001422000c200f00400d455a610135001941e921002800910a6003044850035004207880802080490300c0007000508000102034a400c0f41078000418000b599000d40603600c00340440000c0750300d94100754048900070341c00001c08502180180d80400c00018080d000540301d10b07000c2014101d0102400c0140000d54801410480703040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 134523767 1250 134522517 134522569
    0x603010906050a0b010e0a27090204110a0e0402070b0403080a06090c09031a0c0a1805030106060905241b0a05030309060108120a020c060a0c020d0c090c1805 69
    0x441d54019180103840c1450000381003125000014045107808980a005608003e0100b183d07405018450740340718641000c803a680e00c400008400600f0f42010042d51003418026a21400b02440e001880d180d201911000412111103007480141d00fd9018064001032107440003602103400780c2807803640440d40b035500288040e107403210303d801c803240380080c0c40c00580c024000b0b108100110b400c080034054611102c060f14585034211003418031813030858000b00a5840004030950b07204941d000081c1c800203009120054584100a025030070501c01e00344150009004e108107002402081000503028850141c0f030504920500780004c9614494508030b44203007201100850f00c2031028500803070b1000081c200c86e51501003054a804150341101019400811208610340d4001600390780c1c00a0546070107850300002c03032055480e00314055010350410803020244041119100400058039401c0104010541109504480140106407404401020702c2c00c14040c514155000c0140c0b02d40525103078400d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 134525017 1250 134523767 134523773
    0x3140705010509010509101401050609180a020310060e01080f1503011a0a0611031614010504030c06060803120105150c0a0f0c0510051c0b060c070312030905060a020306030109 77
    0x154000c840c070220130795481051003d81030080c07102110703e9040c41028021072000c02c084402800f07042c86a40d12a203000a000c6d481c946a03260b10b0000b900c1d61b07030107a508510781f4210f0b2030045c0d0300403101c030001c2191000020070761a01032200e400c1d02180607540da0600d80d546d04885403840700080d0841c1e40041680c8920001564240629880c4070425404000009003d00c00c0c0104807030682c111700180001c5440501c0140800401d4403000346004c68420080c80c02404c001c8454141250802d1455007003e0401c81415080700140c81d80c3c40c480c4d03808014040d0750b0749049440e0f0041c200301551007c0280010041c0b440c18075401410401460760389458031100c02409840c1c440120011202e01e41c04104040610102404490080009854504084069203001440c61250f942c06c500700280c0c40441c00d460489550000d00d2042018181e25501d5036199045035a9645d503100854800c18424840040e09101303000f142c40b90f1b60320034010419500d440c907080000e504000d00c01c5415659a0404e0004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 134526267 1250 134525017 134525021
    0xa0c0206040f030c030c0503030c19020402042d061e1d091f05030303040b07110726010506030106080309060c0309040504060b040c14040519030204050a020a09080d0801030314070501 80
    0x5500c1181c80004c018074601d40707410084625480b1900c2030301b09006501d1071400100f802c811040d2500000f42a01c04244006002800740b42c01034240c80008801407025103c1407000360a403805040041440c0b55a0360780100c4000740c100c000c0c0030808031603000c940002801646c44041c081520103580801080c0840803440410040f10b0300001e0011008070b002c841d0180040540c040c0400f40c029510b945000d0b107415281c002c001c0c021108001c0920409180c1102c10321054026090704803c0c403484440100300c00060b408031410404141d403074403011907124a01442410101c07003a200146061095080822080d030301320f120808614002048140900d42d40ca02c98148114412800084c201103070100b440100d40d91071180c542030190312205141049500c40543e005c4810031508900c49035440f006403110600c1075400207400074108824405050843d80151001c0000d035900d061840d580c6990f025541c6e10703044600400704902c1070051000ca031241102c0b5881c0c02c92562403e261001c20b0303a0b0103003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 134527517 1250 134526267 134526269
    0xa0602030f0709090212061c02030106230901080705040c11010507120b040c081603060e04080301090b010206040c0608100b0c07030c05060915030703090f0507030209061002030a0c0206040f 83
    0x80306404071007080703442ca4002c003611020b0f0a00c1d19046082c0b0040204100c0f0180d005042107102c1c103c02e04880e00001d1440c00e01d0241d2990140c020300013250740c0d284140103502c0f0030403065441c11141001d034209060020b100d5048540075402000c071740c0e1a1006000051480121040401800c1002c806960a0074050140100c00c0d598980c00403200d42040c0d48100d40c40d6910140c0324606240c0303807400707242d4011030032500003440a000d1458034035582810790040055a02403a2403e205004002c10b00043d40d0155049415900c001d1042c103042800480c1c460108441c01070420441c52014040c080c41550b20a9004002c881d0b02c231012515a100407800360401009426142e10001060040210602c15040200700c2916045c4c100014040000c106c000400505051024040300244040d07119030440007400390006071958206e01e050403c036480c0c01d060b02080e80500e00103004903e41c0d007050840b410b524030480e8041c506085144508940d0404840402c1e44d0140b01400089081d03811049090 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 134528767 1250 134527517 134527531
    0x303071e05160b070222060b03010302030d08010302030a030c051f091203060609030308041707080307091202010509240c1e160308130306060906170109230a060203 72
    0x3010540305240c920302c0d100d0010340b002d60500301c2d20001c1285103c400191960181d049405908190030007600c85d07a8114803400e1250700d60304068000811148a02c02181668000d9042c1e030720f60021070700e056078200d40070301c002509940900c2101c1c0204e44200920389000303206105071000b0202d4071a601c00844c0700e411050701c0455175110a4020440356039803075440112242014041c082c9801030148c000461403102070280282100000e04001501d4004a56401c90043c0f031910740c0800d0400103000d4004960140220340c5900300406c1c1055400c02944c2d40550594502c2e1801c401130091002400e43c6c0310b42d28119210141d15040d010103180080c00018001c1d100608260741e9110381542038a820798101400360308034941c0c0c84540001d40d9000c0060704d4003c0700d0b096070360b1580d814461103840a42d00207000c851a02d880490a115141c00c0070b4100c2e00c50401444c00d8069442c0c156080383c0074600c0051a989041e103003000618001056811034155420070380d40007500d20f848040603039000315101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 134530017 1250 134528767 134528813
    0x40e03031803390d0e0607030215041103060703061206020903030915090f06130311011e0305040b06090f041101031e0e070e04200a030203010f0606030e01151202030307 74
    0x5015100e10000c490f44140c4603480100820080c0300d501903c1103620000150180e4400100344041c0f50003000401001540d04400c0301084c9400c0c18040c80445c0e03040c203210310030301600d4049020b16200340030788419076034200c2c0c5070b0085600903034501c0001d41c031180c980743e0140428801d80100381d0b43c440b1884c10703620a007820f07a03940302103c1c1d007085000300e10690702511440c028400d0002004d268903cac0703015a5071020f030b41c0c801c50302c0340f02c0140c3d00d84160f07080701d140e5401c103614603a549560642005e8006e40c4950030944007510b40508100c10f0040488903100314002000026002c03680e051000c001600707060500042c0d055500d4a10703a00485409034170b0031a00d840b21050001e1402c100700c0e1000400303881c40e52084900300307592035000748403882950034501030101c00070601907aa0f00c45828000c50380180200b080391074141005020707089603c1080007180c58116600700c02c410600620040f95044603606407031a042075040c0252050100080e80c01d80b0081c856240050303c142d00c804051000c0e400c0e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 134531267 1250 134530017 134530087
    0x921020405040b1515120703060b03090a050111091807091d1008032a0c1002010c09050f010f03090c0b0f0705060c07020a030201081b16050c040e03031803 68
    0x141444c0800c001280c60b00400441c042c402d80380e03240d0b005940c240c44412040c442c480e22030400c2100540510740202c0c0a05400100f030100e1080b0004450804c644a4002440345080b00c001041ca00c0c081e0081883c0c1001c3c06100840000005488103544002a07061034928683c0f580300c240c0c100c44842d01183d416106040902c06009409030440e80145030340401035183c61740700c1045609040584a0b40d28507514040c4012144084c240030907800c40401a004209600b52410000e0180c804200c4200100c0c0d80c0704d201050a05140030320524249040c0c603585500821407001710020803000700b007590354034501a0041100350010009220b030140720041652a480039007040384c14544003911404c41c0341c00800c448001038442c00c00d00c0c0c0483e81c090030b002e0034a0741c030411452400001206400c000000c0041d0500c051480c404104104601481c00c442e40c16100c41c040c48102e41c9101d0100310140e1003440050507040103166001031600a10041c0ca0404120760302141d005030030155042d22811041d41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 134532374 1107 134531267 134531281
    0xe0a1a0f0607081c0f0902101106071b0f03080717010302100f020f0703030305161d061303211b0b2409090c04060807060921020405040b 60
    0x340c117000e84074524925000400460303004911071408030480540152042003060780c003888020080806407501c002c29a0120001110007816100c210b0030301000402812048200078401d45891082e4240600e0180ac0e025800301049001d800c010010800b40e541d581101046801078100004c075000146001c908040c4107001c01040b61284078000420154107600481c4108041015038256000750a02141c1c11000040c82c9282103445e0a202101880c0400040c280c0207040c080762a0301a41d81d50b181c0c42012015443ca00e510780301c0780d04440500741c001907128000360100340e005091500d10742e0784003020b06014014400910030781288000081c0c0100074081c00b100c1c01054044a403900c040220341c0c4054031800c150086080001c000340da002c0014100d020b030740494681e8030781c45042039282d080742e04546c504071924102292101025032202e01c2601c0c080c03406152040c2d05450105 = true := by decide +kernel

theorem cover : BRFrame.Cov 134352517 134532374 := by
  have h0 := BRFrame.cov_init 134352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 134352517 ≤ n) (h2 : n < 134532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
