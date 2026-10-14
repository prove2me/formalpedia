-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0030
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:26:56.853024+00:00
-- url     : https://prove2.me/submissions/10b7f1be-4ee9-4657-9ecb-919cb607e3d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 5215834 ≤ n < 5395691 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 5217084 1250 5215834 5215841
    0xe0403021009110d020310150509010506070b0c03040602161410020a05040302011b02030109140c040504031706120609100f0e0a0308040f0209040602030103020909120405040e0f07090b01120b09040303050c0904 92
    0x481002c08c2840c42c4108110f041010b01c0c0c901414050340c1461504066072290b03221118054001400e62000000290174015158140c1c1d9003170020108041001049091503d803511703080304190280c0c015408040d4020445100701c5065205c04e8448a090078595001500c014009058503609030200c5078000005940030300c64000010301c102d02d0032513506150081e0914000074118141c0c040ca03d440c081c48040380e0444150b45c42d0b0116892442d0159807081e0208007482141074a0840d14821001841690301c1e0110710113140c8036030510708110307009010540300f05036a2802c41441c903580080100f800840d100b9501d040d0701600806014040070050703804500000b104480558640380c0c00b000500c01c51904903220382d00450f00000402c0343c04400e07401c1c480c40e84a54421184a40da03a1040c02c02c0b180b50a01c00c004045840700305032600d95a4624400c0050517401018500140c010043e51001007c1072041c41d000c01e10180c03001c1a02d80d88c3d65800c1e03004040152000802d0391061101c400300d03644600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 5218334 1250 5217084 5217101
    0xa030f060e0103030f030c0207090209040f06090f0c03050f0f180303040303020a0306050603100b03090a0501110406020606090c03070f110f0c0406050409050c06070204150e0403021009110d020310 86
    0x107020085036140d03040c010445584240b580e4205400c0000c0f03000840d40c00280c1c2e1040c0c60b140440140e455010400103001084805103500d00681070500003e400303150360340300d8211800000802c0c8242101c0e0300044088580c120f07480d1804520300310204030303018200c40840e60f002e500410301c0000c4030b9490390100d00e0760304103c80460010390009214000c50354580941001080c003603401c14250309106505625141150250903021600840020100002001140c0f08190060b00030480356440e0607401d00e20b40d00034082c0314054821180411140c0c141500300c0d80c410341c500440181540c860100446460082260b07a404119408003400a880c1090102d00070035010440244034203041c55040c401590301d5680018403d44c0b13001700000100e0408605070071400c13000c1b242c241ea10861072000600034000a00c0d011181c0c4031822000c903c40d044500d006c0d001d04e00035001c80740b61208144441044e143c15800003040c00801d03200701140c43c1428018051403510003000e9844414041400744120754002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 5219584 1250 5218334 5218349
    0x201060e04110a06030e0d0c03020118060504060606090b07030315260d030b0303070305130306021207020712020d0f030c20040f0b0105030606070303060803070305030105040c03050f0c0a030f06 85
    0xc2c202d5010500c0e200c1c00010040409040c01c1c0284400103441a4840c000340d44044203000d100941c50040500c01e41c0102648904034501b560540942d00340b500061200b00c508455440c074001c40801c4541c01192507104840280c4c006501c0c00c162039400f20050f002844c10220894946440440c59114841804d1076030640a808040010304401a10f03103000e115108400926207010380e200c5c02614080f045402035505800c02070781e00c40c0c0b1031040102c2c3c440c4580c070290140f480410951103200f04036812a02440c45a422980102d4541e101c2425450744528001d6000d104c0c4e0500c40300081316824900c10590107400c0452a00005854005104800c0b44403181c0301800e020140c1e42601d03041c424400320760b07860a4200124802c1c2400a00f00d4400502082d105070382c00b00c1c0060405102c1d80122000e4200300e400e40e910781c010b0b03140c007500c035400038060303640310f01d0409564070600c2d0b10920805102d01c088088241154490342005407003a070007001e80c0010035455003a0100c507180c8901450b802400803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 5220834 1250 5219584 5219603
    0x3070b0c0c010f0909150e07030e06010f0e01030204050a0b03120903070e01030b0414030d02040303020303061008130303020307020a0203060906150603040b070302030c071202010504030306080703031e0201060e04 93
    0x180950360800d1150304405052120480c540040c00c1c0c2c1c841802c009545052800041503c102c801c0e40382d65420715441540d410084404100040d64160003054190700140200c4003181d8a6003011071612045000315002a03280b0390041003d07181a030810313a007185a40c10005000502d440c0442e00701242401c1c2541c03141740000304101107040401485004215403c0040c6207541907a440540380817001d0800f411143c0d0704441e0082c40c440030300c202e502b03000104074215034456980c030b00139490ba001252418401e642c41038900900c03502035039142d4400d4140e1000ca08100d407203954150b0094102404200c214858400c11000580b003c110081c0203002c0c201c0180524a4401c0420324030324a40300380e4078082c0c1d1040c410300c000504220b8145400c0b0195040140e141d03074a0b070b484009603024150000d407418008808400f20a074040d4490350244d4040d136818480c040d00d408140755592803030301c001000103841006180b464003080002c4d00d50f01e2010b200100c0d00b542e0f200c40078900b126003a2015591080c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 5222084 1250 5220834 5220847
    0x30615080607030e060c07020a0503031201140a05010c03030c0e0402040801090b0105040e030304030e03151501031a0607020d060204080105041a070306060801060c02030f070f050a050301020705061306020903070b 93
    0x500300411503200c060b901d800c2c01454200700d400c544549028241c0c0740e5641d0080703080c1c011035464840500c0034084c05000c403920f55072a81c2d40003840c52002c0c820230010442146507014a0704103261800240d42060715400a268000e64044000f840c030b00006000300104518a0b410355591030004000a0402d2030011400070030504052036500b00c1a40010700c02c600c2c184a544901d540881503a82c03107a014145003c04160f507401080c10143e04518141030b0740f400f0410001c1e010300d9003010100c03807442a42d0402c0207040f0000d01c044ea5403034003014a940020117111030b00040c42c2049022500314410729001d428250fa1f41000e42c00d54206550031a03050b82803000001e075038400c04040c140d100c1c1281c07070148043d524111300909400018010907007000300d0340b0340043c150744042202d0005880c9000c00c46500503919400d405400740ea60141030703c40d550040d00001c16150500940f400640c01c036000d0f003032903103600c800418941c59001044a01c5a000d101040c0d0350307a018803c1d000284a24002241d84030f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 5223334 1250 5222084 5222099
    0x3050d0b060a030209031603030c121202031e060d02060f0a05070602070f05120403020d030f030212040b010503070e090606010f0903140c01031b09030605130b0103050706170714070606030615 84
    0x18000300e07c60213401005641040466401295010040c3d082400c0e0188094200003c941520085480e00b40301c3d4000010b010b98060113205c1400c002d144154aa45241c64043c200311090140b06006580000c050040301c410f08270180c0248503950075802e01e47d240c0a4580c5c3c454050340c201e0305c42640c5188080001c4004d0150920024240b042d690948514080c110350005230150f00500c80a401c0109452881c00079074000d5048690101c032110010250749441c1c80d0511112000f4000c150090181c108000341446c2448511400f55a030701d8050b150a40c0c4110044500540c4961640d080100040c0c00001144003006503403803405050f0302070f0520308a000c0000d01074076811800d5040c2d002e401d10f607200a281c3c0c4040401e0a6961100c1c0c045101d0b12140f42c85040000d030050050059104900000100000090b9640480f40c454032054403a00040880a16a02c2c08030381d514082101d00c4543c44040207600d008050b070303500c28480010456220b0311803a0840303c0031070301e810f910030040d4814001304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 5224584 1250 5223334 5223343
    0x7030606030302060601020607090e0a0f020304061b030b030304050906011403010608070801120308132402070605100e010e0402031e060405100c020c040b03070905090303071b0f03050d0b060a03020903 88
    0x10b1000c7c00284480d0404000052031111140706103400b8440d03130808241300990036040404082c40140c0c0664403800e080c00e0000040c11101030000000380d06200b00b440590103806100342204009000e507041512f040240240c0c5070004181d64104441c003802d6040e0075401001850181049558403c00ba00d418100070344050010381102a410100a440c01c0c0042c1e0320501c3e80c0c1d070200840c0450f440a006e02d00d070031300e04444544a0480b10303034980d660b04060a40700d6809800300a000d400d052240752182c4040103c0c0c0b80e058029600b840304450300600070b40400001f01034016201400f10b0f01440c0d0503074221b00e01d41401044180d0f4070f8100c10700340024404100543c003c40810840d00300580058000007941d66036103001a940165160b90b403c285130394007485488003c1131b5840d0184480e141804110341c995004442c440702251100c0c144130f04207210740c0d8080b1122a07002c1d04c0055843c00e01e8038241d40b82c1c0c01c4005038004003600d62100c00d003180c4501c0007030642890103403005601c03610104201400c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 5225834 1250 5224584 5224591
    0x9030b190c0f0e090c030711070302060408030c0c0a0503030a0f02030903010f05150909030301120c0b0d09030909090203030403030309080c120301060f030209030c01030905030403050a03050d0b030c0112020903010e0703060603030206 102
    0x3104e1090a0001000983c0112174100149041c80040c01308001125400c0035030a0744040c1d8000350100d0b00040107840400185000c4620106542102d5900010040c1c441c000380201a055801404220342441c000c1c94803400840703460044038180090000000c0c2503c01c511543c070841c5449106208594120303141c2104002422550b403512854100b600070307500d020501c11604800071025104082c000110b80481c0940703400440380380e4035900d170304016002e0320111608500151015500240c00d038100e10400309090b5008000c2c5180501d1030f20214064155460b090390220f40402051804880401035040304e54081d0707029036140c2d85030040140c890080201034005040c01040b85403000d50b004281507105520034240043c1c4c560480c240986103000300e8000404900c034181e40001459005006000c3c001ca45050520180000b04245030b1038008211100d80071514102c0b60b0f10b0103800b0fa030042c0c02035401c05400003c2c001e2800c0d1541c0d2405440d1343c000e0750110b45d205020310500d541800203952 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 5227084 1250 5225834 5225839
    0x10050906040302150606070c08070e0106020d020303010302090601030e0f0d120c020c1011030f030a06090b0102060f0a020c0d050309010507030c080414120703030b010e0a050109030b190c0f0e 84
    0x140e0318150300c010751500960134100200d10a9000052050f036100800e4440341500a6120b5000301c0d110007070301c0d40d200814042d00c8102e180b00000009d400703100150750451810381d54080d40c00c5918503420320400c0b05000e08100c1c180354642140d01c0c2040410042400b8a00300e1000906e45d016244a0141c003444141105410b41801c0490b040001c3d0707000941d9441c2d00e1815100409040c41a1800b110105c1c2c01500c10010380c00700040464001b08800f01550007004000000c0080661341c402e00c00495404062280c0544c22903800510b0311480702c0f0109030310603000d5202616080e0388a003424144a1440052070209030040240f01044109100301d541c41341c90703810201309000e903003074016103180001400202107454072602c544a40c0014000c541c0441c0000d0480fa40380c1c1c585190250142943d40c0186002034102d55010780c481c50480000c4088031810b071240c0e1384041c10368603440c2008000420f60003002d00e460a0110304000548121000500f40d60307a080e52107810a203005201101d1501d0251 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 5228334 1250 5227084 5227093
    0x204050604060c050c0a030c0e01060206040b06040515060a0302040915050a120c1a040501020607020706080a020706090b1f080303071704140708010608010e010203040f060b1809100509 81
    0x11a1603200444094406508001001c00b6580c80c0c501e00d015541060f06401120300c00d0b00004004450603084103440c82c07081000703e07981c0c031114101e03a41c0702d00701d8029211107180300c089680b60038640e1200740c008146da070a41e50b07402000c901180c0c0960110a9501c002940001e0800203954a8840d994940078801130b42c4803003a103080f001400742c003403030b0103403c2e00200301c1180c000030084250424801090b61103040c1805003121480250070390400e10480e4094040e46000452061010414005447c415210216aa226907140200a411400e81114265034035140e4034007260b003510f612032080c0884800a101104803480c40f000d40300c110b80c00347c00a90b00c2032080c00385103a00400b409400740e00c281400c680c40e03030361814801441c841201c40301d0024010048003003207040c17064000d4016140403c2c001d00c24800400145400c1744002c0b81d001d0030f645c82c030155060019004c1d4200c070003182030051201d10500c02001004100c880d0543d024842944030301d001c0000c4240500429030301038502c00152 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 5229584 1250 5228334 5228339
    0x1090206040b0f0d050901090201030b010201050714030709030c080a052103040f021305040506040615030203060a0e0c09070203070c050108060904120210090803091902030307060e0a02040207030c02130204 90
    0xd54180203900900051440110300104001400070650f48040b550a205208a00f0511210b074001c0c500124181e000908100035802c00e54014000d05005110300c0c0d840d80080c05420f1b50280c4250000751051080103002180000401c480d5410500900313459400f401030f40c442460300d14500703603100c08550103030300984441c01c01588014003580d501a400001040045001340b00141c1c2000d44410032001d15403078103050105101c0c0004401e48503600c50361040104406245140700210390600c40254150300c04800a940f40c54160051744280b40c1c580112160718405000081d4031820071180c0d400183d2000c503034442800310300000040204420b0030004041e081400115040c00c5008102624a40e00d0700e000034821442008480802040c080c02008020424034052809031700030307a00120540300b0714001001c110450180307452800d030300038020751038002d4a80d00d06e4094000032010bc00f01c0c1c02200907150150316a030000701a054400d980d50f1260250901c1081500e5034540141c012480c41480b06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 5230834 1250 5229584 5229589
    0x81006020f030301141305040807060e060903070204020c0a1415070504050105070201050a02070b030c0909010f06020a020904030e0a0603230403020709020c0a06060e0711030702010503070e0f0a030b0612010902 92
    0xc80741951503900d0b4107491700300400080346041c5068524481d080e4074140801c4140442e0001600c00c19203d49414004418940c600030343c1c40364155101d4400390010080340006103041e034003d02400e10068251280c0c40304039111001c40e9455400b14442c0c5401440c003141103500d1702e5241d594044a1030812034180385c10840004c00b68000d17518000e041c04000240d0000140c000c01171880146541881c540c2d90340340c109014411500302d8149a80105190400410040748202891003900c0d01170380140355035071854003041551003000d407058003030000210301c2d0041074446280c60000703405c1c03948000c40c0040d00440c41400b000c00031043c165051001030b042c40002680401e0440c11a603403144090380303e0720003c550301c0c10500d40041c010103492400e07000181c0c042100c41c540b44650f103d525145075000a00a01c142c032485510320013400036070104002800b080c061036038584500e0000e002119403043c6440862a1041150000e440c0448400100b081c280f90450f1600e140030401e200900005900d9400b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 5232084 1250 5230834 5230837
    0x301030c0501050a030912030c030b0303120c07080f0c0a1202060f0403050c0c0901150201050906040f0b07030b090f06090106050c1c02030c100501050405060604050906010305070e03030a081006020f03 88
    0x4090402100050049404d4425001440007980080c018040001d940d20084d008101c003055250200c1d040142d2012586001300580701c1014400145107a140e9503400c0c18141d41d0b000300c0044401c0d00e0140402d0f00c6014942d006440488031920060404143c1820607420000c0c156004104541c031000401c1030342102c0a00d800d400507818240f00c2d46030702503440114100400416402d0700144001c0000803c9401d4665034591503001750020007554451407601c6443e03480450f4054034000d600c2210754001140001941d62007d080e15000401244000c00540c0400050319513090345410101404554941300c0c0c0000d00401c1c0701e0501926241034408025100c014040850b0418007018030b401c80c9060081c02226064406041034443c0c2d0051016400003d100038011940a00d01e82000100103092990480e810f46000408001d410340c2c4000045020b070800610380b904204c200c040401190300d08002030900028152620445894400c0d841140089a940141c0840d40410ac2c0040070720004030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 5233334 1250 5232084 5232089
    0xb040e010b03070c0b0403030f110304021203030702030403150207020904140c0102072d030b090a05100606050d02070201030617031206030312071404030c091e06030309060f030b03120715020301030c 87
    0x1284a00e10395214203040e0010100402920b0127181004e2180740f2030100c043c015440f562080350745048820086c41090782d00d000448100000da0320401050000c50105a10b1101d5040c203150054030f00f200316800b2518010b810f840032104002400000e0407801414441780e06410307028801010300034070b4400c03031041500b0461015030030701801903a18043c580307080c0c24140c0034681045101c0c005061140446030f440d000040c2c03d0303a85004035032000703030114441c2c02014100da0701650340b1410005040243d000135482080d0880c103050b558080014a841d0711070a8240c00040000610f880e445051260a001440145854840d4008124002204414a101039000b41040c42c00381c11070001307900d07203000c1481150005442d0705005240000d040c8440d400401601070f04008900308002e0b12240b0300c00381c800074003005003c98020340d0148805445401503400401382072170f003c5050510080806d05140427104034000e68040060f00f401800145401c0014031000b9000861440d8510740f40c6807041080f90 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 5234584 1250 5233334 5233343
    0x5010309020a030f0b0403020d080708010522110901020d0207030c0b070203100f1505060a08010902030c040f03060209010f0c050303040605070c05060709050901150504050d06060f0b040e010b03070c 87
    0x41500c801551035103045000030b10b0f400300d81411001203509105a4000d8100e80c00c60041c0701d104228036605206412a0380141065295800d00382d003410100088000a1088444c0040111010300ca81d8003241c080d00d40404c130007962195989628070700080c1800c140ca442207080d0b5204100c20000038501c0424841207400c40c0b54180d86844982c4000307401c000c085140d400310b25044c02d0840107446ca05600c00e140e401c4e850701150b0440d82c0e0b5082448503500404200c0c0000c0f4a8540040004005580041d540612001c640903d41a141c250300b21091031103810039100c4c0f5902040c40011540c0083c50910628000d003040342540d4056034800d55a448010310051015845401107410310b4083e17202c4e0384840e54000c0940c0c800d4a0308040042065155119880c45000480c3c0001095100c1202900f0108016a5040e03c1d150505040c002e820210000c02c0306d21a40d076075000140d00302072800020142c81100364a641c2e9a01c0c0c41c106001c190010380044003845420024030031483c0d0000011340009510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 5235834 1250 5234584 5234591
    0xd0212030a0c0c15020301080105150303030601030b030712050708070e161209080301030f020a090b030a020f0315010303170601021204060e011e0203041a04030b0613020c0118020102010b03060709050103 89
    0x4400f101c00e81c19443c0014900d0565004480103c0869005581038614500081040c0e40d11080c2007d80c9500c095140c9406400400106d4800e5200380c0290701120000b40440e002c9558900c4400000c071001041078525030001201400f2001092007044010030144241c8600742c101402c0d0308140b020b151808105201703000920503052401c9421190041d50003c00c65078885da52800e205812107c4c1c05000c0340709400d420004281110a03102e2180551001b80c02010a4a130640c01e0000505190401c1a414407401710a4081d0a002c81c190314040c521950300c00c4a031690502c4074058212000c1c15060540d08124144169103035400c0640d800c841040c07402d0202d8400d0800140c51000704040e50a098181030009481000e400000600c221542114001840a030b0700448400c24099030100802c4500c0000c045580e503d0718141c1d41c0d0303c0c1c840174a0300500c0c2c40c100b10348150031200124952602095403600d14000d5680a03c80d51480c00829000340415150541d4020907070f40c2d17140070b118141640e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 5237084 1250 5235834 5235851
    0x9180303012309010f05040507030606090506090d050a061d0607050d0f0e010c030209131b03111308070302011101090b06040507050c0a050a02090108070602030d0906020721020d0212030a 82
    0x6904510b46107140c0050301c07900f03065840b6417001c1105040c42c0200d500460400c0003142e11140320340b181e441207070f120396501c007103132801c0c01c081017256806403102d240d200b080740890101140003842081d4229206090002714030302c02c80c4450004d40100c5081c445036030421000c0040c0f0fa6040011143c4609040c0000164074000d814040010101d80401c00101e40c45c1c1900d900e1107a03050b5004240d180d90880d2000d0304500502070400642c0d80d01000034031702c01808280450194040e0308440142008210b60381c2c10035013180d00031203103da00355128000a5101a60800c20740d45c1041842e008044190000c1c05440d9031900c980140310405030583d40107a07079407000106100c4c864015510441605001d4540c030744858202596149444042030b072013555070b180001f03100c1d000000e941040395110f402560400c040c050001c0c2c005c00040805484858080201c0700000e616240080d10501c9108841355801c1e4040300c00a20341950a5920001d41d80006200030391000258180d0341e00000e040c4001c00c200c02c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 5238334 1250 5237084 5237129
    0x30302070f0503030412030b04060302060409050402010c0f060501050405010504020a0215040203070510080105030c0a0e0403080408070204050a05090f07050102120903010e0316030e15070308040606030203060705090918030301 99
    0x1d0308031000703000c5000c08401d0108000c0c06220034440048266810f001e04000381003000221800e40c80b0082d07200b030b0200401c100c800340075009198040d0050400651600300c0fa2980300c1115020081180d0440ea1540140603a1170030b171158501400c01618114104850054069134030446105100705a0cc0000c002504540c1e00708019401340001034443e290804903400d0142a0700428003959200b0300a020803501d260038503070100310844041c034000c5802615952402d4941c00400b4005440003401001203502603211401082d014102d546800103181c07030100340031420300c3ca5051f200780341d9400880c010407050b03a00107074084034096824801a558041c00c0300080c0107001d1111114042d0001050301c41381010780d10b021a0358036020b5191010a8030141040017120100e501c0d907649900014446031010920030107400d54898459100094015101c2d00024a004000c0b0b6848001a0340051203150500345800540e821035204c90100a2500301c0502c099140d000c14068840e4041c14011010040c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 5239584 1250 5238334 5238353
    0x20c0a06020a020703060501080307080703080702010902060a0915031e0209010201020903071508090105090d0e010203070507030501060f08030906030105040915090c06032d021b120d0605010801080a03030207 91
    0x159000c00119990009298080d445603807900c0203403040c0303103030400010300118088112036001c0e0340444107524050407560243c1c3c2800014101c1e904641d41c1d00c068000586401d0700400040001d81c98000c1890321302a41c00c0e5120002d00c0300a010182000c102d0302c0c240b00c10300850282c0c2c40c400100540c542441d600100d00a0003840902ca03814850b940002400401c0c80c2c0c2e0710421860299a00d1450f6a9640034050903500281d9040085e544241c2c150511203111301800d4501303090501c1070300d10380200e036107515240c002d90790030554041e55150301c1080200c101103c060010010340d00554205070002001540f40d0005100e45405642c0350402c02041115611068011102900342003240400505180c0c840720301ea40140004039182440d03031085c2c440c0c0f885080c145085034943d8104440a4216840043c0d000103e0400101c10180c040413149c00d030074003035095000608000c03581c481842044d40030a6905903400b87d8180040e0743c0041c04846800314144c151942c00d4207016913a00c0e81c80c40e045024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 5240834 1250 5239584 5239603
    0x203070204050112020301050705030c0d09080409020705011401080c0108040b0a0905070801020a03110403021c02060d020a120c05030103020a12080f16060b0103050621010b03030c2802060d020c 85
    0x54a00800820340c81204135601100500a6008100507514260b0135900c921065071141c074075187c24000c0301d0302801c644e0480a44188105956401c06503164910700c10707038200d2001161265181d803581c00d05940701241c840d00424002c001081c0c400400400030f03060700d002a002520b001c060500207565a031060700503424513070f0301c44200d0b0480c9030341d140024002e40062000400190415525588035040302040e142920380041055070003003000716444200102c0300008980081092040111012445c070141640f540740d9201d40030308010079484e101c01c0f11310b0006007a080c04800d10060000d40c80350b4203035000362000920103100300d4210f030502c1071030f038001c800310361030429400514482c01d418080503412100b03200d104180101c2d501140150b06a540443c1d01d260002050407040d5100700d83d104030224900110000003442501070030200381140e101c4101d240c82d65004001031071358420902075808510780c04030710b40902c4018603400203c0030300c41c0405005445802140c50005a54207114400b0b6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 5242084 1250 5240834 5240839
    0x6010f030b0c13061710030b010b03130204020a091703121609080319080907060e04020a0905030d0503010501021b090604090204020d05012405070f03031d03161101030b0f0105030702030702 83
    0x26800c4d40d40b100204819680c8007501e414250740700100307a500c49103184c003d0907254410151443c03a8280012580300790002821041c000c006043d2441c0903032a07500c004c0510080a81e581d400302e506140c0d145058078075401089403254020415088950b0041c042c282e0080c5c08480320341d40c16528800b04440c28600768000440c1e500000444116804440303016615a031900d845003066695100c2e41c01d81c4070006440307102c011030140b520141842c506580100b10000c0740741400c5194a443d0030200c0e10342041d1841e101d01003080000103100715130b01008100488450707990118049089000459031240010b02082d001d251103e007120110766858041d2954400d05850401c030540c1e4401548031001000c1080c01c1404481d5801c074030441740305000311603010b074020280d449a20400d640c01c8000f030003040072841c024035240caa0110020340c18802401182041d01a054050b00c050070b04490300d5819940c414141880c0500940c015110440c2065640c08242402c540f40c1d42d400505074154403070100d0081d27 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 5243334 1250 5242084 5242117
    0x309030b010803120601020a0210030c050c15010305010506120a0b06010306090203070206040309050102030906030c0304110d03020a02010315050d030305180d02070906090506090c13030b150405070206010f030b0c 93
    0x2403502c400405408403d16803c0c0341c0c1856290a4010390710f441101e00040e4200764101041082240640c00c09801c014040c40d0180c0703001481c5074510b00f440b0744080b900440351445030040050290900a035a04085c040b1820748107040901050340d9038181184008094500001c00100d8686c000d0348003c00901742100155601e1811030f81c001c0d2101c8040320b044001c2004403c010076503500c000280d50344940007403c0d00f49035031100c20f107811968000500c111104590704400544549500f00c0348a05284290002c021004140c8005000d0340e1606007411111084903e040040b69200c80071886620f825040010342d41e03c2d88005545810240204544548500c40f48502d0441c1c1c0010303e0403c585040c5c608010441d120005c00c019901e0645055900c82c1d2040c0104140c640003a0003010940d0060300c03d120718540e240d071400c8141400303c4074020b512003010500712032800e103801340c4ca034002c49502c003a200660614429900e0340c1400d0001610044030f05001130948403400341262212550000000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 5244584 1250 5243334 5243339
    0x201021207020f0d08090c01050904021605030d0b040908070204180c060e120d02030405060a0201090b0c0c06070306051302070614010b0406090602070b0909070201020702090408030603010605010c050a02010c0309030b01 96
    0x7941d14001406410003a2041c401d41c5003145204940c414000c1d04488040c00801004d00011036651300712115aa0344550308001050740ba437035810b09154000d10442c040c3d91a00b10301d40003030003100d400341440c1d0b0040e030528507030b68000b8507003408450303189070304450000c4c25844060708103000e40340b4404000c0450b2080d00d004264590409440a40903408481003000d030381c0f000c490305840300f14800c581009070380141f1050080d442c2c11005041410114400040d40c0d00f10364403a14080b120039501036002c4500003410013280042803000c658000300a080c14003205242c00081a4245041d8003141040f60340072500c4e8041011a4000881008146c181d0413001d503159070001d04d0035402403280c3c40100f80d85140006030386001182076030840e00c51050742d50400500030144943d5040052144003195030030028100140d8500454074095401441030703e031286070030010f1608441141e00318a0500512585000011b072000469418a0307a0a02c0d00900340303102c03454181c610740c10b207400052440a515001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 5245834 1250 5244584 5244587
    0x7030905060f090f0a020d0b1b0310051c050a060b030c0a0801050703230402040207060e010906091506030b0402040903090e04051c05090102060a240306090506060609090a05070201021207 82
    0x2071a004110b5542600c03a801e07601900155959440c85c0001d420146158450001c80c01804031507500c000d08051110413003aa01140089503441214521a10381d15010700b8006418450f05484030007100345280000e10f60700d6201e2a40d01c0c02c80d044028000c544070b50045002d42c60030f00c4206103418010308401a03040e02c42950343c1c0600b200b00d0300080044d2501c10701c0b100c0d05100c5d6102040001c02c04001031303a0b07600e032038007404042e50004005440700d94480100302640c200910610a0141c094200007540452a140c4802c6c0303100124055451607083c240b061010a2014a615401541c101d500213041318081c0703400c1d646050103038041c070241001e900800003801000318074100172500e2a0074000080c594030342c0030780c0d0a02a440c040c0c0e0050f4844800501d03818601c0d070000340303598121404035408094145100700030714602d40048170034603101c1032000c0801c4070820009802c010100e460701e08080b001e0b408a04070700b5004140303541d002e4590010a405038007c2d030455864140481d0b4103095450170020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 5247084 1250 5245834 5245861
    0xe030d06060c060e010506090406020a0215011203080f060a0501030e0a05030f0714010203010e0403030b0a05030610030303050109020403020d0f06060b0f04170606031e0309030706020c01020601060c0201020a0303050703090506 99
    0x24243d4003c0e007440c0c80c0303d8002506201d07141c42903500601c6840151103d4032500002d4000825010540c880c0220640c030401e0905e8025009100c0c1841040100f200c41c50300500120010780314840740040b0000b030100b16610200840182c0b0320070b1800182c404030b01c140310b40c5406104480030303000d8080003c2c0003104490040c018140c050107100910220303040451014200e00c02403092114012002d4003080000b40b10f1382104a048000620340f40e601a251000a070400e2415a44c9028403400d40c4001c00c00c1603010b0140c28010305441d84114107007495a00450000d00401500401c2000e24030350f2002041826805440600f4600100544818030110004071075806802000340389032001e480c658242d600051000c2c400c0c10094058848650400f150382035040400640440c40c2c0005e208003117450310204114001491143d0044c0300803c5424006070400c40103821280c10400659081d0303000d41d0300000c40c502e4540d41031400080c9035403442e104030700802e00309800074540e00412041c803c02c00481072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 5248334 1250 5247084 5247107
    0x114090a1403040305060106081801060602010506010e01020105010302060a11030f030703020904060504052701020d0218041401032004181104060504060305060f060d020d06060f06080403020309040e030d0606 91
    0x1a926554925401e20081c0d40b40500e100080c070301d91080006201c1c4500c2101a82d0b004510308003030307a50b1510b96503090744c04d541654002c00c0c010f07990384042041d00e40e03018ac4061858107081c002080194110b401041c03c1d4880d800d00e40040c0880703c8523070780720718a0030000c4454601442700c16603201d040000005019601104159100d1420b000700070540c0d252a1042038003c403118004180c1000b0390310b00c0700d6440308202d482661b0b0740d5424440c0f0100e0a41c503000034031406010b00794600d00038811704104000c4642d10300e0300384920125400140001062100001c81c64205030389502942e550000c0010040c14002040410755000b20020404215852008a4a81e03070b00b151f051121070303210b07418001100d665101c06461980700070003040c6410001e808030f642200c0040c0142142c0a007a40103d82c05544640080b40c202c0e07030700c403010001c40e109141d180c3d01a05a0389031481003030400d900d0096480c05009411071155030384080c0744507401d10820841d008205c0610080c0a10f82d501d00020b0801c540c0e18 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 5249584 1250 5248334 5248343
    0x706080a05010b09010c030e03100207030305010504050c03040f0305090f0a0608040b0106021906020706090803010b070c08030a0806011107090c0e09091219110106030804030201020c0307030b010b0702030114090a 93
    0x800007043c21400c3c0410390b1904c00061351500c00c42c0140b9207084400c2400000d92540600034070403004403801b4940020044503001c1c0c1ca0104e969454041400100e8800074003040800b03000b4001d000006494541c040040e64052602c1394503004800002002503c000304c1e110b07445080a080054a107070032101c941d10450060800e07812581e0b80d02c00503a20303070101185440902c41d01c100d103040040c500e075001d0001a0702500c0e000036a02c3c46c41e5121982c9900a8101c82c001c420041404010014140807030b00c040e00c0d07104081e500b410b034040b0003d0010706000c0c054606000c500500303046d420004001090041403820f03020301804180c0d50019212460031809503000303411000008180c58130004003650003c40180400b460101c3c003080d01c11113010b10080b04010811000660780c4181c0003405100302440c010284280e0343d91071032001a10340341038038020310701075003001c034003000411500e5087d01d046804041c1010341e110514400a4010003008500d8070380c0058903018401500c00010320740c05480c3c8074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 5250834 1250 5249584 5249591
    0x1103070e0a15030804090207060209030105010303020705030d170f040201020a05010f0501060e01080903030103060c09090219080f0f01030b06010e040e0714010216050409030507020402030a0906050a14010b030403020a02030706080a 101
    0x10500b80580440890001800b00350301004100f18829856005104040c00b0348401820105ca4000081c2928020f078001e80040e400894213000f0b5240a010010350390b03005090100d8441d80e260426000351070003c200d60580700d0716000140175a4000d001c494503266010008116059851285c0f000a100a0140c08005070240a10800d0b950041c4000c900458074900154116840d6a540d00041e18200e0444801c1041061002804220034005442da0080601100e000765440d0311f001094410000d003540d10525003482400102c0c00e01c0003110b41520b42015a40226581d4200141c40d83c5050600054201d0314051407203600c12000300d0600184d0300003110840c01030000e40c00491ba180440000c81c0403003464010304001528003540044000351213814081e0604086400240498200712603c01080391101513603010030000c1c2c0318541d40010400310400c0700b0110386829008a0805020310140390314004041001c0c14000c001e07011480385d0040880340000e49804009229034410f80b80394210310f05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 5252084 1250 5250834 5250851
    0x60b01030606050304020402031e010807080c0109140f010201061d18120a0305090c04020408030d060501110304180e011d010507030204060c0219080d1d060405011403041103070e0a 79
    0x400c0c000c10701100c2c09035031824110f894540801c80254009000c0718221407008082000310a40040310a0080c4a01d0010b0316029141400703560030481100c441c60b041106012081c007004000381300b10506035406840040d5034080c2c2c0340c0143c0c0104015000004045607103006050b01c050000fa071184200c401502101a140390300d00e40c03540c3d5603101d80c6100b4a001060201108061195100316402802c43d000c0b580c9020040c40802c1c2242c1c0305820202035908000390801442d03015020f66001000b0070302c3c0102d26405040f03c51620781c019402031007408001030141d800c005496420212601c1d4400d0020841c4280c50341411403114442c1003a6250b030b500340320004142d680680300355012501d61b5200c0c61400038a541c00c01c48003a0340b1016a014900400c1400310f0022020080c00c00340d000c160300c5045405420102a000c1c2003400d00304031348103030300400041c000c50742d00c10f00904400c01c00051050b200e4a447c03800e15120a248500186c051040200c00100c001780c2074003160098180329010400e816 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 5253334 1250 5252084 5252087
    0x207080111070c05030d141e070f0204050f0606030a0f06030203070b0304030909020f18040e06040506070207050306040c06080702030706020309070303120203070806010e03010b04060308070201080f0907090b0f0d030903060b01 99
    0x5841c1c50440c00f1400103c141a898110f1034000c01e1248a100300300d00280c0c482c446440c8c26030300090001e03030302400714050300b60031800d0611070f00b600151604892111494168001862403000a154003005600c2c0c0020b14001030700e81e04684080d585c0202031394902529a261215140c1003124194002581540c001070000c11510880701ea41101a029501c3d0071400300510600c1d9400342405034105a58071000d1000382d0703050105a00a41c40f8002902440c101840000e10f4450580c21041c480c0d0040011303c0009007c0d0401d030400c941341030170071074402da8a284040c2c0c08c502a5141c0604900e0000040000e03c510205103002a00d1180e01c0349043d25a002c1415012030100300c90035000305841e000071401c81c0d03004805400d07000c0340c000c001040d00311081c0d01080c1901d4040d481200e12130340c0460850219a0070111080d40805090701c034058a181400c2190340c1c0328100c0c45042203c03640e94403070492a0310307070103040d0303450520243c0308203101919450010402995880150f40841c900003c105156 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 5254584 1250 5253334 5253343
    0x70906080c040b1303020d05070501030c17011208160308010e1003030206190605030f01060911031b0706110a0c0606050102010203060a03110f030604080a1d09010b0a0207080111070c0503 82
    0x3034450440150405040020300e401c65841139a80600d04404600004010f03940d842840c0c0c50179206030003800c1c2d2146840009001d460b1403810040c1804800402c0f6652400005e813032030304491761000100007804940c04c1402c00b5114960409284866038500b000606800c014281c0c100d51441443c18002c1c0d03644402000e01c0c01d46400001c006030042c03004140d1440600340e014901a01409001501030f5640c40064500300034082514481c1e511400e00300709a5656100300310940c200744910515524245402e49076051440d40020408400450100700303019507640b2002090303411035030b02070f6200150040071b0881807030344004955007030810340080740d194818025207000710000341000540d10306607a07074861002202c61906030031030001c0c074490701c207540c08000301c0340201e02580300305a0303d56000e90000d050002d10003c0181c60004407481001c0c43c0ca80f103600070b044074207540d0443d0320784182c66003c0b030030030455505c545100d600344800020b00c1300c8440024203285105074030106e06140d07a4010305849 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 5255834 1250 5254584 5254591
    0x40c06020a0c09020a02100e010903020606040b0303070f060f020a0e0f0a030818011b03080f090705030c06030604020705060108070503100621030512010e010e070804020d03120605030307060507090608 88
    0x40d004042d00b0001042c281d00075081c88000d90045d0f824545e0902c81c1d2030111005004082d110b83e44402156040c1a010300c00070740c002c40c05844c14040601e2160109a5a1298070030041ca8510702404010501c10301744d102047e444c200000a543c0c840001c0d40c024080b0f060140c400d44a400d926000d0081450490b54410880380d00c000c80a01b030a40c3d46040c81d0348044405082d078103010410700c3c50748255100300400700000e80300781c0f02c141440c10902d2000ca0841c80c02001c0341c803140d008546c1400196000a21a90307405001c49002d81d8075920140494040d0090103401001031242000100d03403010049103050640e0419800c58040300c0b40c1d259000e05442c2c21b8400c50040011401703d000b103001040e03a07074038001400f0342412890005054400d85080800340c1c4050058114940144100c01c41c00c0c0483c2d8002c8807d1505212504003600000d10741e0317014040050500101507004582d41c04260003180003800000d040d00d844580703a00345400640f00c1245c28900040b00c081c40070500c2800b81e68014003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 5257084 1250 5255834 5255843
    0x120203040c150c0203070b0c01050117100209040212040b071407020904020d05070812130e060102190606050402040303030b0301060602060103050703121e031e0506061204110315040c06020a 83
    0x1149880b8030507544144100b904010000c03510728400160f2810004000106020504159200b2a5250003800c580c2e040e04082c000a00c68000e0200c01c0704005503002d0907010701040142d07114118000200244148041d181400d54980c0400091080d90300b2102d1241d400c54407004817044070f43c030045400b88a0307001c0080d8041c00c42d0001c5005800d01c0051804c000f885141110145070f10780141a00e00b0001a40f40d030383d1b400c4001002c805c040c010507260801020351440345a114100900042c1d280e08000c1c0000814044800f180702c10300c24036800000003443c3c050411503440d0749a0074018003906045035070502a40c00e00074000f982e03c0c03000844074101d942103009040d03803905598030500b0240c0b01001c0c0710704101c00320003041d17820703100001e01401c41103482d00e000944404000558040c80440d40a0324105890042000541d40701ca10849041c0b4000344040f03012035070707949003490340801d8000c0129094801d02501c0b030240a4017862440c01140541030300c0c0001544c0340e804a1751202c3c820030060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 5258334 1250 5257084 5257103
    0x3011203050705160806150301022704090210020c0411030103050d0c03180b07020301050f0702062a040b03040c090506010c020d05011d01060906091b08041a0f01050112020304 77
    0x40803a228602070035100784a5029900c48082610015070b8080742c940120100d40c000ea0b0a108072980c0e42d036070801c40e072101079009500f810003c5030315040d69082510404401030030300c0458169a030b901c2e40040c00341036000b04484010340c840c0e800250f85010220004e030241c0d00e44000f10240004076425641202da00034010181d000f908a400c480c02411924100d090101d0384044142248100c00f011019010322010a0f0300c0f5210313401094295403028029032444042a0f0038851015800709400b07500c80030101500c2c0c0c4840309440141c0d800601c0111100041c14003042c0442c00601c034a0080d4000c50080e180c822199460b0307590042100d00644030349010618081c100d00041c208020000641400b4000000d21207549400f00c0301b200c04400d01c0c40321241d549040c107100303002c198421500035141c200420004d40c03000344e41d05201c40801500100900191800207410814000300c010030040e524403420380c3e5800d0007104000d08150a01480d0302043c80c00340c405074051103500c2903a220700d4000c2c0c25a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 5259584 1250 5258334 5258369
    0xf09020904060908070807080717030403080105090c04030501051003060b01020712020103050c1209010903110106060509151603021507080601080a0504080c030f04031b05010504090e0715020606030709020301 91
    0x1c02c01854407800031604240c1c10320008010510320400f408180740510039840d44d412641ca810f0071000e4400c14103c481e400700f4004e001c003107580581c1d1241501e40c280c1745150f032a121400804980c0c0542da00003007643d03090200b00704c0c2000c4000000c0c001c891040380180b2083c2c010074016a01d032103550181d4040e00d81070490342c00140d8840d400854200e04c51285641c0303421440181c0c0c05d4003007811251000316030b448443c40300803d40e100384003004070b070480d100130046a8180341e0010124400c9144261148000c1c0914010403042c041c211000741400c4d1045218903802840c0207501c1707103c0c1301c4101400340400070008034154022818540b040318165a4080703d035852390038030b90007014054010b80c1d9070171081c004c689980750100010408551880a5591920310b1440c0080c12000f200d1201080420801002c208903604102030380c1c05d88100c4100030562410695250b0314007913045d401022038030320715050030040c0303900070855034011413058058076003090315043c0fa00d003a80300c20710450151540e20040c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 5260834 1250 5259584 5259593
    0x301020403051b04020412081206030105010b0403080708040806010f0e070306050a03080d0605030304061805060a020c10020a020a030305120f15010302070302031303050d0f0c051e0a05010510090f09020904 90
    0xf042e083c01c010300040c2016154114107000d0b08859108440c04003001612020f1040b00521466000a040303009101c5503050125044090045100080012002050501c100701380c40c1d040e43c01421504007160b40799a55010030040000d000d100c1e00c0401000f800108690318480d01691050700c0015102c2c0030304a00d90743e95400264440c030300301070100c0c0e510840424a03580900082c401030a00b0b0355403e20754029a0340a0030445148da0145100707850410640070115004954080b00146c01c80320000b5254903030074182c1c104182c0c0e180081d840b402c1c425011003016082005811410454042402180e540041c41000107000303031030318040d11a804441c01f00641c40b070f40007004107d220384140c03804c0c52400d890340446181c2c1904121400e402005420211030b5000d450440075400d42c1c070b002e40a44010b5101d43d0f0321340c9034108a21007113081001600d40c845608022800100350b003d80208001d01c0c2c42154076840800c3c0740210700001d801c00d001c031000c80e0310034040c102405800500d6003505494654a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 5262084 1250 5260834 5260873
    0x30506060603070c060c020606030d0804051209120303040609030305060102010b010801030b0c090303030c07020312040b0d1505100e010809031c05180f0a0309060305010b030406090302010b190311030102040305 92
    0x140f04200950798a0ba0300000312103006038241403205800919540c102081010b081083c1c890640080068900801000c52800a603002c3c4001078900055a41c0e01d940e80484c120420b081c6003101a480004103010421110b5800081024000c2e5004c2055840740d0300120700b600d14606640d40001c8a600040c404a4418005a03400803211803459280c42a944042829a0411074055050f14030219100055050500c042c81f5005030760318072079250a040068401c514040d2144841183e80d031404050502410450000d000c0d10b0001c1104850f04203e21009203d01103031362000d4001041c103404540155000419a47c1c9403003200000390320344200f414483c000348801404103503041d600c60924058040140314030121214580c003d00034501550901a10200703a0741d00c403400f0035290500401c0b1800560042da0707001035200001050209c15030508a0250010b0a00c040d48421586081045910140701150490b07200c0c040114404400c0f4040500303c0c0a02c2c80301409981048800d0402001c900340d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 5263334 1250 5262084 5262091
    0x5060c1c02030915040306061406041e180e010e0321041a01030302060702010506030d050a0809010603080315010306080c010207030b18030304031d0406050a050f0607140304030b10030506060603 85
    0x204490419086400040080d1004c030750400b01e2401c00a01407052106034001c50016000342940000c0954006000c00c845100c0c0d0b20034071120118080303ca081010707418a010000340b040e0480481280c030b2041c51007009044052840310b00c2d6191a208140305a0084181d9250a40351041e086e884410588500319800000340202d13030700a03441d070200020048440210780a10f00a50090200c1d02d0305000290031160081c05045c403a501140e4102c0950380e1000466100b11654030382001c403900d030981410701400e034980004080314004010494040c041c01030441150038240c0c1c05000495680b0b40003601d0300003885040340140c002c880c1c24400718072000c14141c1c0241c3c8a02c6010b01d40b034204c800796030840d001034500700c0000e02403060b425480d007040e80e00c040785901d08407000c0000038a4000001e851480318400e0301d000d0b5041008101c070641d10360040d90070f020b8000d450304554501110505032650301c02d0108a80508101d004100c00326426258002688c1d48200204038070780720401001a10340006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 5264584 1250 5263334 5263337
    0x3070309051606081006020c0307061101020c0109110406050108130b0601020f030d020405010305060108060a0303030e010b0307030605040b180a0201080c0702100905010905010309030509040507031503080706050105060c1c 97
    0x81c207103100c00200b0031001c01031000d995910756031709082d842c1150603040342d804603085503c05c2c040c03c2c03481d644c041030403001ca44244c206060550382c440c0720305d0301900520307070704074625441d01c0300782014401e0003c003000c1000d504440400c4269214001554100400d03100300401e464a1004900050825807032160000014011280740071144901e01d880c40e80004992202c483d000308040009581500170207070800c009082c001d2840c0350510109044091a100c06000c268490358041c60b9410294403a824403140030301903400c0c01e038882c203081000c0c01d003d50382103414280741c00c000f400042694480d6240031500401421180e00b540d001116083c8010b888910454410000c100059842080018541881c0d4031000082403620340050700d40c541b00e500031418941070020b5500060343c080304032440c00204440000ba26256a1400c4005000d1040c1880180030b1669000c420f0000d1100034218032403040c2018070843c0c0e00d96042c00728a0150b000d007d038555210768042c80304002c4030811404010703002d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 5265834 1250 5264584 5264593
    0xb030102091507050111030705070f0215070506100b090607110a0909050109030809010c05070b100305030a120606020c01050412170414030606040207030e0108040606090f0f0e060403050307030905 86
    0x14161002d0149800004840014143d081042c00e008a0300e1402d61072034941d066192640c006041d41c890b001c001010102c1d1000c4540855942d65a984098032140480c25241c0304280b41c210342d1070205031002d204070a0001000207a403c41c3e0000c855070740da805840c0d01d040ca6050f0340c4036115180b40c5070038240d11520140002c110724049100b0314030b14900035030000c82c91381c94904000c3c0030100e0143c0003a8940c0d0406000c4489590480c00312030000d60b11520a1005596041100c083c10045400050440c000014103140e030741c2d800b0403a180d440d014010200071b410b940c0c0d0b0003640e0750441010080d0102c0d41c18442000364505044080107014003c20f1096654201c0e00280c44c4190b10a412070f0b015140d0308104214581410170034a0b91005044d682146010b101c4d031400380030f03025004010750400c14124001400c009058200d200105110070b0280100f102c8410854080c0080c11101041e8516202c05610050f600040d051301558240d140d00389140c44884084025050158003601c10b0300c01c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 5267084 1250 5265834 5265847
    0x70308130503031315090501140901020307051005040c1508010608130c09060f06140306060c0a050609150a050709060302030901110f03010302040605030d0207150c060911030609070e06040b030102 86
    0xc0500090122000c088080e602403420070520500100a2211050400c21b00300c40522169030000c6507250640d0348421495150464040101e20310710a0510051083c0550000c0c40000101c90700704c2e0340140d100d00301d0342000d1504c40752028018041900c0e540d0000d1034200c010040c071800740403919005142601c81028a551545034034099050316070000d1030f51907440004101c0c005014080c0b0003d80340074507145140c408000c4100c0d0403070001500c070030700c50200000c480340302d0801000b0783c442113540305043d070343c0510b050794a090304c0340b1118a50100f2504480300041071f059803440f50a1140c0400d80b03032080041d040000442c002d400c028903060b8659600d80c00031600110303600c042c080b0b18203181c511a03501d60461050109a800070390000b40285d10200120600a4003c41d0010903240d080a080400000096085030786140e040d102507c1d0340e1401b039099052140650607640065001e50881e41d003510746a007829070b103032024421942000d6094000c03400c245415008004403000003000076081c1784 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 5268334 1250 5267084 5267089
    0x3070e010531030606060e060403141501090504031707020303181f05060307060e06040306020a0e0402030112020111060105030a030e06040b03100602010c02060c04030209090709060b120a0507020703081305 90
    0x14141110029074440c000e0b0400400549000c2c00c00a40120301c0c110759610700c2c000c00700d030450065000c0284110a21121480c803008100b0039036090700c04131540c0c14001e503912400b50004141c02d4a050700040c90280c450760b00321a02c802214021840c0754001d500c1c0d82e446609029801b100c040f41010310380604040240001d80b011005102a008403200141c02c6c108030040500c1c1811641c4113006001c0c51790000001983d44c0015181100e42180b009699001ca0314812100c4d04000c09416500078404000402c1c2801e0682c3d8440c0e10b28400c3c4c072480e14001c0080040c0c2d40d2001c09109656140d4440710500001a106600180d900340c3d0180003c2d04103a104c151f940350b84d0f001164107440441c00c034101004040d03424001e600e20034100d40051304040c20319010100162003103000190141b5000310100d42500010480c89006004400042046984410064006900c4001c120ba04205020003103884510a48601030103104903070020112585140c1d40ca0800790404d258600d10f207640d0030400542078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 5269584 1250 5268334 5268397
    0xa050f0304080f060402010804030f0905030a0f020f010c0c060e0409060f0b09010f0e01060503040201020c0301060308132c040c0306090305030402040e010c0e060c030d020414031203070e0105 84
    0x104a400050340c0c03a5810072904901c1c10a460401e10202ea010380140009031b41c0024807540c1058251810a021015958042e00e00e0049940701ea9018401c1800c184107000395080002212882201c0c04e240900d5420300448030b00d40e8280380580b42000202e0f04014040c0545546070414401510100b040402c80d11284211010003031455003694660b0101c4880385081881940541104001581c040b070500d000c0d0021040140550320a00c440007002c902568002c020341010020010001c0c0726540c1c5074505940c030b90f0004889292000001080440c0600c03151103203184801000030400720300c5c43d400c01c0f00c0444000180c001c1d24041c01504010011950b00d01542a0690181e218241d80342003a10512086400701040c0307034050b9142108c0c941195034004c500c006c90704c5084804903206c0448101060440c401c0f0501c64400c00d100207000503030380c0c444414079000464101d055901805c0c030030800d121203110440f2040f000030480c1d4580700c2c00758050ac01928505a07444031700740c1440700c01907140308079 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 5270834 1250 5269584 5269603
    0x1802040501030b070908030a05040302090c0c060405070501090602030406080a021602030a0507030201020c0612040f140106080a05010b03060108060a15050a03051e1b06030a0b040507090609060203040e010311030a05 94
    0x3e180500d820044141d801600c1d00d401044490020341c601659924000c0290180d130000a2103851860301003200503404900750390075203080d13038155410303800c143c50410b90f101464460305001c58591400010421300100c00c3d0b4040340c0d15901e4540c0300c1d54854030b405009501002e00c0c0c800b01c002460440015072010041509020320510050600600b58000603290219294840e0311803e8100906140c0c1840880b8064110b5401903050203c02807a00d0801d1840c0311501d00c250203580f170309000094011001881a2003540108020050840f1107020305072540c1090107108103650006001c29509201a0702844848148074040101d07d5114070009150411a038000c0e9600c0d44085a103010461405240183e142c190800801030071701c03001108810301c0300f040c500364842c007030100000d800141300e84c102050034039005000300084c1c41d1039030010740b00d00300320b00031100024503e100c00300e000c1d4000012101a00c841c0c44280d9856807859803002140b0380c0a00caa035815000c1c00700c5d420001002045200d0a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 5272084 1250 5270834 5270843
    0xc0109030801090506040504021005030a0902030609070f0b03090303130501020408010c05070b06030715030b04020409050906040c09020c0613020303070203011d0c0a0506070b0714030103061b030203100504180204050103 96
    0x79652502421000392000608070620441c40c00d01030100594034140b000a00c01c1c0e007410700e80e890f0755507042c0b150000c003075084010350140510380030003044880c045003490980f0509a0310300c500580380c40c080d040e075020484003e0056841000801c0001d810384100c040410301c074100140c90070b0f40b641c43c245c0c00d413105c040403500072900114a00c410000c8104129a00030419001040c0e040d14040c00302c400540c0b507a4108082c035907168400d02454595404640150480400a1102d82054502c1964400046800780c0d0103442e1200c002ca010300c042d0007240d1f01080600f00402c29926a1120340c0344070040c444040381c0c5803004000807001a28280104036510150114420301d0465542c9614182000101c06500c1140031020500c5180c1c0d5403c00c5c2c034901500588500070070740d02c1c0b0300c041d81e00820042c005502540c001c40000200241c42e04083c500210001030701e84d200c80544400e40036404241d45040701e4801141c014400d07400c10364401500c0311101403050030704001c40c1d0081021100c1c00e070000e40e03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 5273334 1250 5272084 5272097
    0x6040909080a090b0c060a020306040204081207030f0c05150604020408060f0610030608030f03040501090507240801030308040b04150c020c030606030303040209150f0603070c0c050609061b030c010903 88
    0x7400c060308900110010311343c201100d490021420308030ba4036500b008200042c80d41d4044007141891325258160740c082c01024003200c0f02c811107107121300034503003040f10102d0010b18000c1048140610400c02072084641c040014030201080c2c0800c8500d00000601c1d15820030b074280700001d0703620340400645015070480800312905082880034400808050400b10042c10f08100c2c0400150740700104079280001c000d55030b01d0322a255460000e0141c9007285002d40603100b100800701700d02c0c81101c501441c3d81e5070050f1001740131a5045081d501c0403002d104c054007040c07540b40010003080030800680c4d44240720380c184050182c01030044904803070984080d00b00580c80b814040009060800c040380e08004110021401e5190a50020b10568030040c41225212900b070841c16080e110840e080340c0d01c0500414660300ca2600c400000c10360140100300b40c0b0401c0307058030005681d003414030448840040260006141c00545e0540800f5a0134800f0381c400644420018146110420322811046510035078492 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 5274584 1250 5273334 5273347
    0x303050601020c03012c070306020f0310090501050a05010f1205070e01020105090309150a030207080d0506090a1e020901091203050403050607030e03040303030b06070b160314040c03020f0604090908 87
    0x28600108003402c04c2c040c0e80341509280c0c010004110300860302d02048400a40046070403c400c0c201f0009600043c10f450022035641c4202414801940c030070000d4903400c42c8030641c0c1e40c4a64080d11004c1c0700c0e86801154001c170600145d4480c040c0164034907903504005003070f0325090009004442040b60154002001d144250729550703420b018141d08644080e00031360030078079020005407a510b0380c040445032003000010909107450203038040d42d28054004140d591241c107140504c601078038085580e01d103c0c0c00d804c0001140c0031814840c40c0e070341e001850008602583c0028040000350b101401090601c01288030009000141c0111103020f07601c40d6840d95105c03481c40c030740b092030840b001e00420245410007442202d10000001514222900340c6030200d400f069010104a540c4900403000d80120781203410480141c94210b0108107456141c0d808128032403400c251900302240c00d6400400d5114160030420162400340c1e4804810318004081620703040c3e4070135004048401c468000c95a01901003001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 5275834 1250 5274584 5274587
    0x5270307180e0102030f06060307020f06010803091c03020604030513090f0c08010509041e030e040c0228020d060b0a0803030f0714090d031202040504090305270d03030b0102010207020901030303050601 88
    0x402d049000e1640c020342c00d42c28540809015040000c101c2e17806904003200099501c0d100704400208500902d0540b015075854540d05500e0b9408141d050b4000c1c03030036900481055440c640001c0445c1d4145cbd01400054403159021519039010b00803000c0c5900720100c01042c2d41030310f4801c070300036481114000144448510b10191454805900080c4294445020030010400147c11201c0b000700301046008a03603c50310b010380c1c24070740c43d5102941141c54401460710054000400342c1503220383e0003e514040d11a840102c220f44000e04000b50805684030340380c40001c81d9500a559008030080003120440d4654260b03914540046518020054142d014402d103250050f0000d0702030030148421a28000501c80811096055400018200180603000281d81a15681501c0c00340200500911102c0200e0400a245d13403c060a0305c13041c2002d2803210300d40c00080034034029140c05e02400c0c0c10103080d03907618242c0060a44110031410355400b04a40001070b540d5488450203544039450004407030428800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 5277084 1250 5275834 5275841
    0x50310060518010e010b0309070f080618010e03040501050904020c060c030f07020c0609120c0a080102071104020304020a0605030a0603020d0c08010e0d05030112020f03010504081903020a0527030718 87
    0xa00501c100c102da0040c8090300708403082a05541a442c00d0f02c0d6262960700303241746030001c3ea9020804174003030002c0c0841c51000c04995540501300e81d51004012002c407210315070803612543d103182c09661040000300490f5000300040c01c07094100500050621003004400d6007401012501c09034250350020401044100e403100b51600700301d00344001c1490814a9000c01d01d20300c41d400310a8410384a03d007030040688820810507180303c202820440900707540e03002c41400703504505411512111000303828242d1382840d1007906d1146800800c0d074082545041d105440540c80503220641c42902d8104c007001581714a1100309226211f102e94114040c500b00d4124211044a00b421080340c0110b412400728981c4042500d0560303491310010b49172800c0310300c0000d059400503041c2e50381550a000800013071001c290058401c040b5622491030001400c60002c600301d11a4035814008a8400d0003841c6031202c18240f484044050300c80024541c100120000b8a0312116070320110301c0078002c0310b104141c0e500e50700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 5278334 1250 5277084 5277109
    0x20a0c0603050903030109090206071a0a06060e030a0b04030210091203060501081902180d0605011401170a11091306060905060702150a020c12010501080c1002030a03050705040503100605 82
    0x16042140703041110301c80303844c1d00c0107100b046c24940d103401c1b00f18155607030721040714802680680d2038040240e91501c1030301d82c0340007241c060002900c0d0810014540e40181418160310703000502070a040c214a0751124070000b000b41c410b03421441022568215440c051248145c054010960044440c2004400400b55025500550304000520040c03090390141da288044000c503d40030b0150b00c58003035440810100c5070f01031006070b0205510985c4028409aa0701180c10f075401000403030b0305150304034019141800150121203003940031400040d440d003c1d591200d40da0410b04c0d0815450700c04100f00040d01c0c941001400139100c2d94a02c000c00c00325030014810001441e09032180b80c02c4c020b20340c002507a0382110318140c030030103900096a0744020303100384103002d13160700300a103528071801c02008107500a140c240552502032142c00c406805a00d4418403009030710209900451a11015050072406404c2c05401042440424080880c207a0b40c00d00c03501028000154000884910309402c01002c9207000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 5279584 1250 5278334 5278337
    0x306150301062102040902041808040312050a02060f040303060b07030206090606010806100509130501030b04060b04050402060712110601080d08010f03030e01080c12070305060102010c0306050a14040608010c020a0c06 95
    0x143c0d00c0390544101e01c1106121940490300000d141c0f1050000c2006005610190700b4601e8110410b1340800000310058001c1c6d90240c6a050120307180f009003551140310303c500c800050f90140c00083c9000e107220002c00d40c0540310f4a40461256541c0c400c40d45150865142200960032207002c00c45015010410343da402082442c1902c0d450901c0004204e1840c0c1080c089020488005035410f2280c64664100c4c805441c408010403156075a4106400e404030151001c5625604094991849141078040c8a010300d400500040c0303803174a15501c49041c0015081510705110605c1d100c0c2440b00c40600c9441d0003410306402400c41204108002000301c0d0f0140c1020034900d004240a00200342d1200c016084400d081c03c203c561601c40386c4004039a800389844061003070100008004d1640d43c55040079000301c4003a0000c1c0003040320054150141c0c0d071076020741904850310007020044c0446808002010700c00c060400a8503680300c0e1101801e56060034460030140e408107410348100b108a0744450700070101d9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 5280834 1250 5279584 5279609
    0x20d02010c0504050409140a0515070201050105010e121009050102030907060203070807060203101a07020109051c02040b0f04050405010b090c04031106031005060304030f0318080f0315030615030106 87
    0x71160003a000740114050640502c0d625849030341000300301e201d20100c652000007101c0a1280d01d00d00165650f42181c00625812817841c04035403803d005002d014160b0394141c440b90760310904107040c07044030003407440351550900c00e03022215142c100c0c5200e080394441c05040003595900e800c1060300c0c6001c5d107952118046520411400f0045455042914041c0f07a0150000d60740e926a00258614590f654020461074440481d01e003095694000c01418994800e1702c40307405040c2d88400700646170703605041c0d101c80d80303140c82141c0300103207060380c00040c0c00b1400030004450202c400c00414100e65045400f110039139074030303150440780e480e1840c019607100a1006a0901c2c0ca4215076a020908401c0ac4229001d01c001001107001c034201c040022000d001e01034440b07030316840c0600300145030602020401d00441d1410700d84143c04211194602038aa81001e021454040403d91002d0240d000601c06a5540d1540e510700c1d0322030342e0600045004820341140c40c2c112541a100709402c54420764000d807410f282 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 5282084 1250 5280834 5280851
    0x10605060423030c03070f0608010b03060d0f031b0614090604020102030403060908191206050f010507020d0c05040c200d17130501020408030a14040e011211060d020307020d0201 78
    0x1078644802c0000404620541410035800000c02d16018000e43c406906001c1c42c0c00210b002442514136030125001c2d076840c242142d03070715508950b01e4482610146c1d00480e045040c4030103e207000d030300f041200703110f0f1500000e00c44000c03c2c440784143c011442156295120888843c002c85440442c1d80c00c90a04006400b4504140e40040d58a210345d10000b4a5152241034200501071424181e5030054150000f5001142850000416075031880c040c000e40c0910340b140c04105410315044482c0071580685903203103440c21503000c208810f42c0d45ca50464400e000a40d02040a8849005124100c0c0864984080c001191041034410a40d4105094201e03840740242404195103c101c0a0070640b071010b95001644440182186607007510001038459800000d00060603100000200402c100c0b41e9202880011127042401603881684100c924902a0030010320040781100d919440051094403502c03c001c01c00404a03205412052400014550200420005d10f0f0180305041d030548451008000c01c08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 5283334 1250 5282084 5282099
    0x60f06091e03050604210c02130b04020408010f0501081207020307050607060e010510060f020304080309060307020a0501060b0703110105060306070e03011d06040c060f0801030f08041e080106050604 87
    0xc92900c40c10030668079140c807150307900003141142000b8640040c10707035480b8503050808070191022100b440503090001c045604009100701c107502d08070350307008010207014138103805960013410082d40784950282d03080000040807942446070514101800304042082d6141194030780c24115640000006040104240001079401061045c1540c0f0201c035681d0312038100d401d00d42c00805c8440d144d81e0302503207040180031480c0c24529115003140c4ad140e43d80d11401080400c01c0f604e81c0180e11500c480740c0d2040c4680780092900001940d48821030b0320440301d04243c1ca445643c2035079010741c81448070001c0000c03030009040c0d1121801c00e1030740c0300c07030001d110310305210000c40d559a2006254100b003243c1c002c1c001d500d0360342c2900400361030308242c8003025804000a0010f42c03640010b03642110380321805400002c2072030040d03501000d1001952500d00c5981e280d0303100e41c04d00b100c0049007115035110810011604010815252400b10a07414211030071500f840d071910301315074103500030511924081c4410045034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 5284584 1250 5283334 5283347
    0x604060e13020706020706060f0602030c03071106090a030303270201020607030b060d020418050a06030203060c0c120d020a090905190f0912080f1005100c030905060409020904060f06 80
    0x38001078400d14080300082003920000e000c0c1c07110061895000203041000e0103082e401680a440742e05400c80d100507503500c0c06a03903d200b03210308018603410500502000c50035510f04803e032108064a4589040d0408001406035009900103c002c85c0c0e55642c410451010600030404500340c0220310b4003000d01d1500040e560340c8004101904061716940c2c034414540301c0500f82c0f00641280982951601c0d01c03001d0300c4421041c80c1070441e03030040c130f041d00181e0a1100d602504080b6900a0081c001c191507000f40c0300d245034004601c0d250341d0f02c5102890f400d20050000186150074110f50010380301c50441c0e8004003d100c00e80d0007095920300b464140124001003035010a041000242c002035410185004500a440301d040090042c0d00d84a005c0741c4801e81144034580719400c607212030401940e07000400c108407580390064503080000500d10840f60707070140c2c1590003514001c0c1444400240d0703481c00502c10358044d4001d001d034980c02003241c0c81c1608007809894050b00c014104011803e00f06074005128 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 5285834 1250 5284584 5284607
    0xf060108010e062502070801020d06081002030606120c12070c02120105160e01140a0905010809060403050405040903110105010f15021b04020a050f030f061e130e0115030b0703050105060406 83
    0x50000d0784e540100c0714000c118100091803440c00139074440540c0040031000b84594843c12406000c3c003060b022010801d442164070400340201034504000103082900d140f624000c14184004000300200040b1801c0c643c0f843c3c0c810ac40c039607120000807400348180b000800c00d48021900503070620080c005100c003001c032801e103824140e2426040b94440c160040350341626103040703d54504000a000c10310300d80e002000000341c0360207895500c0162540b0105503a074850442c0e002c0c000030300034841072001e86003503002640514000c0c03904a583c0c0854034600c9085031030a902a0180f032090410411102c1020000c110350701d031860000d005a914415140e174500038240510f40c0c840d13507000441c004501e014005a5000c3c1c1d00000c565034036440c001406100100040c2c44040c441c2d4000190002c4408103030001400452000e010340b00e4044904e0841c5000d04891180c0350844d5480e007211000c2030b511820a00f00039802520300901c1404d090501800f101c2c6c060300101d00504042200f480210b4100f40803402 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 5287084 1250 5285834 5285881
    0x603160e010c020405190c02030408060f04020a080607020a11060c06040f02040914060603011104080c0909010b120c0901060c050307080d020d050112020f1c0f02040b030f060108010e06 81
    0x1000140403004070384880031a030b002940031745002c051001079282c0100c3c1c0306068250705420070001c9884a0140c0c0e4900682c850700c091644400c2c0000c144545501b036444e006840900541240c58480400506064088400c42c006903c13460702070301405001301c075419814609072040c0d4a0440602081a219100148003400c1c07507851003030300411500d0703039802501c003d03400c501e134460701c0341d83d0200b182d88a840a41d0114843c4d0709040e803840716090250200d500321034031100104485d0810605000002c50010040099035689040380211a190a800542c6000070703a4060300503610210b0800c01d420700c042c2c20410800c40005200000a50300100712006240c2104003143c032000140104000303403107070b030202d10b103e40c2c00c004c0002800d1800c2410951454402c5586004900351401440340ca50389814020b11812150500c14003ca450368415500c41400500003041c1c1c403000c140840d10300001c01015900b6648410010856210b080c07042e1100c000b075580150103542400c0d11607001015003807a2249 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 5288334 1250 5287084 5287097
    0x90f0302090903120106090807080d050a0e0f030709091505010308030403080408090a0b0702030607021501060c05010204030204060b070c090e03030402010503061f11070e040807030e01020a0c0801020301090605060316 95
    0xc2d0b4042c4204151961011085810005584c54000040403000300f4441c0c42c034035216001002c600e211b80402c05008140c1c803603862500b000e01985040300c8503030403428440c1e08602a1091031495072024003140000c4d100032140030480034003d2400c10198244c1e00404102c0b00e05d01340060000401e1042140d07042901480c1a011070340710b6003440c0c0c249100c1c41500b41d500c882120350006443e5036a401800e140303402101541c00c2030351003810a07030300c1d0400c18804481c4400d014005200c814020000c42c40d4070b40c040c0000604040e01e990100702140c44640041130241d60108400040000103143e05001d844882e0b0140520306801d2185942c81c08090030090601c5004800250180c84414032a07004020984041c501c465014002502c482c44102d000c80903401146400700d0111000b181d414007556000700c090340744c0007031a2000c68410f200b0f41030181c11806001103c00200c0d0007405044064156040010b071b42e54500b103545011038503e0b40c032a40c06040d0500070800001b101002c040508800b80c100034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 5289584 1250 5288334 5288341
    0xb0a03090201090b040f030303050603010b0a03140f100605030d050f0405011407020301050a090203011b020a0f050106050604080c09161b02011e030b030606030304030804030305090a050a030303090210090f030209 93
    0x43c0c490440381e0f041000b5510700440c0020300c00c9003090f403c000b01c034029181048a0f442d800181800e841c035526a45800c18a804010000a0f201141b094140080d031410ba07101c3d004404095424600b503844181c0840b61640401e204a10b428008243c003805541019480d01a200290081c6030013584901303418440d914140805000070342c0210381c3d84580c010003c00443ca00300d19000d005010303001099010f5881c28001c0c1e20000c81c00c2d45a050650b17100d40041040c40701c0c641d00c43d4203075401c00c00200c845540340c4100240c907403100d4010300007130f111110103085818600410b00c00d40c600c000341411011001d09020210340e5401c421081c0101c00719801080e0b07165040d0006807408004011241012488162181120b40e41680102da03081da0850a90300251160b10400d540c1e8010760202030004901000100006030051000300b0076181c2c040c0840740040e03900d0b000110078a0b1603038800d4020944900c50002145001c100003034001540c1c1c241500b601d41424294406981c0601000313000d0207024011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 5290834 1250 5289584 5289587
    0xf03090512040303030218060306060409020309030702040c0206010911092805090a020702040b09010617070306030f0305030405010b09010602070504020a0e06040f080607020d08040308070c0b010308031506040b0a03090201 97
    0xd11001500c0e481403559650390b24a0005c00039809455502e44851600b0b010080034904041128010031005150a003082e040944a40080d480501207000307a220070804240161103500a84282100da034015045a616240e24001900d081d5801d0f0b80341005c0801c14500d01d5656580403400c842c524442078079034642480c113500e504040c00c2d04400d6214040e9020040c544000350010b0036400d10aa8050140619038030502030441c6080c020140440c03920b4003908220b5040c13044d400c0e13010a0302e03e0302103161550f9481d40a11505418010340c0061800410041070020900403c1c0408100b51510001507160040081d11a0194003486104c0d03038000030020012440340b804a030466000030411540c40f0755580704911101d9640c400c03040039011342000200c4c098000f02d0207004500043d2150387c650707602d554003203071207030b5004140e1014442c5161013800070400440013a80a144900070155407400c10001c113074019451074038200e11880c0304010078031504180000b40c521030140303400c011401c158240300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 5292084 1250 5290834 5290843
    0x1060f03121214070f0806030601050111120a0503070305010509040f0204020a110304090b0906031b0609010c060504050106030203120a09030b0604060b1c050a06030f150e0307030206040b0603060103030f030905 92
    0xd010b1046410300407045002510040082d0003284e00d41c031281041441c40109a8210004589859140c2c00800c0104142c1d406604030041d101d50100540d01e1484008105606941118a007000013440c040100326465415105103400b610003140d000f00c051070305640c1c48600b40d43d4030f50005d015540104c0c007004e4080c05103140094035450784050b81c0e1501c0e00c80c48000018a4101e000500c039480340c502007451418042841c3c0c426a1140e000c02407501800002d02030550704c6410803a0400c5140010700000c14075a110303417070050384910000b04156140d03004062030183c00c1c90300740e1301640c0708121074003005030410041c1c001c480d07100c00c0342c84103699510000f8000740ba8641c8401c181c1540011042c1e03400c04420217002144001d001d080181d9240c280c00d0f10120703a00741c0070050101c1d400b01d1048000c030700032081210118081800200d19000300e0700b00c09045402c42c95048000da4400c205000c00c100e00c2d00c0103603500800960040040750b1468500401981240307401030b041c59070fa6102003041c05000e12 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 5293334 1250 5292084 5292107
    0x103080d0b040e0a0b1e07020304090218060f031006090506160f080c0a03020609030414010503150a08010903030e030f03071107030206030103030806011d01050307051605060703140901060f0312 85
    0x1400c1d40d03060402c6007002090325908031030609110981c5140744203201c80c2d000700f21f030044409a005505007400c0440c503100070340c05004a510f5200150400c4902c4d03a4601000b004c1c81c046030145140c072814003819521149050760441002d101003218103100e40d40399030b81940c2c0440d0045201c211a07156905048241c080c840c540649542c0b00080c0c11584420f00156861035a8802d50840b0619a00c007135036191240270380c0c0500700c6800c2c0b448400300415032240e00a540c02032550400c01c1c3c00c1078884070000d0740302d4120358889078803030351118901001d1640502c1400c0d5003900020145140c910850f15942c264130004003907078140308018420710355000080003c5006194044c0c82c03075a481d6180e08001d40348041c1140d846001030f030303a00c006030001e52110700529260f20068640d81d0443e2130b0500150345581000484041c40762000c0d800e0800305600704061405807000d610b00040c80b660b1300240030b079803220090182d005070b0b04205007000f60310070b80401c200403640c000c0d0144000c0c548480341210080d203040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 5294584 1250 5293334 5293361
    0x60203010803070203070f05030d050d0e0f0106080705010503011809150203070203030a0501080a020102061504110d0c020d080405070902030601111006050109050109030308010b181002030301051302030103080d0b04 94
    0x8400440d00300000401000d4941c0228100d550709661511344454409035401040d4060f0032541703070640c0e07441c080e1000d4600d030500b100c008038007080e011080d5443c1411441c1410b81d56034407540d0410840c501813040201500c401e180861030356041c45200340301e5040c000046070740c8941c0c41d00030206001c0b0401c0d124417407407012002550380f402c00c018000e649400558146c01e80502e400000aa1040001202c01030140d06802800c2c0c16610b035120701028078890801c1603001030710303500306650203948180103200201040d07000080d14564010004d02d820b14084001082c8075441040c4004590005940310440b00101005a81d039900c1d100101c40503200903912002900c50403442015480007501302c681514030070b82e51103400d42e0f03031040115030030106440060003203048100180300b000050700040c41d0000808076400c1c41144014042182c039914903c02d200103070030200051009181c0380080e0100c130921014158151350550300c907102c480c46851001604a075440040410310b484d903411032200110035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 5295834 1250 5294584 5294587
    0x203070303050301090b0616060b03070f06090e01050306040201120902030c041802030f030f09010c05030408030c1c03060308040e0601090e0a0606021515060705030706020d0606020d02150a0f06030602 88
    0x1a40703406031040e0000e0143d45455420303c0c5595031542031000954426001020f40030141142e19140d4000810380c1c11034058060140500100b02c4080741c0c043e2800800d035503910031100341d10f07080600600c0e801c1a00114402e402072418000941e0b40030b40e809039071401e000c4000800016a200080c40d001c59a0145a001410f106140034002d030704c0114012010f0095042d604407220003441d294507480341b0390300f0403500c04e4103004600d40d9501c200035198040381325100b281d00d4142c50307164441c0303590003042e80c21140d58400605125810111780c1e070343c40b10301103d003400c0c08640c0c116a00d01d44140500e000d02408482208001051613201e020940e008010f0602100700c98102240000d01404140c064a400351281c6182945040240b065540c400c40e00e030580c0d80020790a600030000541d100680c00d490a2000b4403100e00460b0107440100004281d5000000d4814039200300a801e1481c83c40040c0300f550071400801e2240700c1e01e00032595108114590000e408000d10f4603c000034003890300083c141910 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 5297084 1250 5295834 5295839
    0xa0204081b040f0c051608090303030c04050a060903030503010603020a03020702120609010605061602010e0d0b090105070801052706210c040b0a1503050601030e06040308040b070e031e030403020307 87
    0x40e4822007002002054400b488001c0310100841c0541d5600200807000032010015811a04036405103c1d0311a44903140c024640b1240c0c20010740f6540054032148800400000c00304002c0c078003400c50304000c0c80a400d1024034240b954a01908070b0205108201c207250300001d040f92158460b90441e410290b006045c41c50300d03d003480040b60740720f00c03c83c0c0010156203464800b041e980b40c090b05460305045000c1d10700087e01030940c01114030340708500c841030b007240380061400002001d6660349442406c40304000515450401130041c012401a40414003c0340094820001107060a41c0d9044c81e605105141d01c041e00d529002c60140255000f0b040c94002407a0011441c462000c00ca8640020044070240308446502c02003104503001ca219822441c0c1c603006030a0ba0843c02908030590100050400103500400724560b1400c1103005c9030101c0000d0089020401000681d066150b00310000e45440a064900e94000c0ba9484142c1110500101c000420040c12010104119009554043d040d200c9469 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 5298334 1250 5297084 5297113
    0xc150908030703090c060306080304050f01030914030a020705010f05092202040b04080601060e0306041b0b030403030c03050c041203050c0a06060e04050c0405060f0607020a05060f1b0c01020706080a020408 90
    0xa5100130441c3c500e5030103080084e11a100b4025042900d10242c00356240510307200410806c2c1c0e0744005000c0c18103031a204a00e001c124140c10350040c80c60044051076a41050001c02810110550051410b1003101c040502c070141c0d00c00140d400314403050b10b00c4400b00c1501082c815401c41000100315005000040116034181c0c80340241049801c0765045405607625070304207490210200c41403942543c08800001d01250058040d07910454120405c0c4d8210364449144001c142d00403078094001c00e4030391102502090b41442240d611015850403141000e003891061400e506413140060100500400c1c0300c1500300f002c1c040d0315102540031404103c1c0301d80e24a440100c041044a041d40c1c1c40c01400f41210450509004082c4180700c001c060100e1244d088040045607000030105a0300842862000310b0140c0f00d0304010981d41c01e002c40d1440c0c48080200850811036080e516070741c61500250700340c2c9110303600010320b482901d040e4180b04503030341d5420702504006d010751741c812003140c4201c140040303c45 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 5299584 1250 5298334 5298341
    0x40603081b06060907020604080a05070204060e070e010c05120c0c030a050c03120315010302030c0d0501060e040b040605180405160b030f01060503090d0f050c0105040804080d09060c150908030703 86
    0xd14481c06403169542e90030100400a02c0449480026030070400004001950301d6004091181c428105541000015000300b0220383e1160407031000d4031000c4041c480030395000b8a05075070340c82091034a04050203840d92155155181e0b040407440ec0d400109213080700030414081041a1540501121000c005600701703541e031140b01c0340000e8003034043c0403c4015401a40c0c01101d20601000301642c441d0a00140110b00a40c0000c11a9071445428040c180140700c40740140342c000e1160780e44031026507a41342c040108548443c14418403032460107600b000f5903140c000c3c405410f20103040901c1c40a13902e038200107051240b1a1032080d1003407042c440c04108040024060b41c00747d072000d03100d034003981c0e00e429003910301348810381e940115540004103c0c001c843c4a14000403079401140703401d5080c40c0300d404000303003540c00648040b90701500c0840c0620420b0801c0000310503800c02440c18203c19460101d0260101d6000130014008417680c40d0344001100584c0c1055180c183e100d5102c9940e0303d813001c0000d005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 5300834 1250 5299584 5299627
    0x30403030b030d0206130c030501050f0702011104050f0607030e06070b04120318020f0301060b0f0c0c03010207020d0f020301090f030c03090e09030405060d18120809070f0306050604060308 83
    0x480c0c605032040c011410002210400b0446a1300206001e8644ea0402036417146207050440f56001c9070320011000030030a000309030041c0c7c0f408400910303a0070404006400e48140e01e00d51481d02209000c02c024a686140202400000a56a0507503a42460408582484100520607048031000841c0b208102c40005268455030050212410030403070319404030203440d400040e4102003020081c0c0a009864035048201d800f00005000140b000c1d551900e0320783c00d03084180c4004100300c01003800039400c14144000000900121700852502e0800d40c00580003d89142000c0d1041000425907002c44d1025131004410741e40005da042012080c0f454001c001d82c9004200320002141100000b42c041079098a041c080c0000c0e0000e58201410b2105101144d0043d09110b030607070f5124142d641d06034400c00704400d00300b07000e6850642550700e40d48000d0035440d0007074003040b52640110810407046001c801b4120603258400800701d00f903155040014081d200d141c002030b0071030b0000100c0c120b0956244c0d545050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 5302084 1250 5300834 5300837
    0x1030302010506150904050603010902120f06060a0602060c030c0f0f0301050117010305060a0c0507060507050304021f08040809060c01051008010c02060402100804170406030207031209030c02040c0306090e0102030403 95
    0x3840d90f44000340710f50031401020311400100c041c0701402d20b40ca802c0d0000c56100a0150000a9860080c2c000481c10909400f051f540c40e0044440c54018200c10302c0050352181c810384203800d00c24600a0003c1d0745000080106130722203004808282c01240c004100d9008044401e210703520f42c0d03404c110b038040580c420b104090200383c031140845181400300b0b41d04c5048039005000b0f40503564580e0b480c00090228048103d0800404108410000c0e40c03600c54240203054a07612031742c69140c50300c103012030030741c4040b04054148150200d54402582c01604a0f40c0721f5449130741c640e10b901c40207001c80d07100e0050300e10350481035007060100112040c0404407241200c014030020300021076070007400d0f038a464003624082c0d0081c40800c000d100c414019500c3c150403038446d080581542244c0401c00500b90490380009000980008400050640c000b600b001940034401040243c1c0c0796642c1c0182100c942d5020090085860700340d80d840d803e0080e4030180c0140341c0c0190a220428114a81364000d50003160220f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 5303334 1250 5302084 5302091
    0x1608150601020d021b0d020a0311040518070b09060706020a030c020d03110f03040206040e0103080d1d06070c050f100204180203100e04060605150307031407050403080c03040306060303080103030201 87
    0x9031258400140c03a01e2604054014281c03500150701c003410406402c0624a4110000d007081a00580300c54003090001c5004d00b0f081c0d0a410100c004001c15184003030a41850001d6141c02e000070303c5004140c1b403003207951a000065903a014040800c0c41401020005444076101244120869406810032120400a503003a58100d48200c18140c048230721008172a0304402041c0b0584102744d443c00000d68005000600442c1419602c141003860303410260800c0702d03031160110756000742407880d001c0c00250304040103545070b0042c1b41c04403465032090000c001c9800c00500d6a004070901c4000e1080b1b1400d650342c0c0003640c51010303c40c219803020750f00910980c40ba5402442c00940c07805901d10a0784e0081454903481c1c8a000d290210361500a05e0150050701d4031650351400040e21380d144803100d600704940720f02c0e50b512031074031240107403c8805006015641d0b42100d0200503100d03a0010841701540d03807007008580c45a1030340c4001e52039809103410050800d0b02d0400d001c401d041e0002e10441c1203a100394000d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 5304584 1250 5303334 5303341
    0x80106030203010605090402030a0207050111070c0902040b03220b01060c0212010204060e0d030203120f0103020f010305040b0a020a090b040608010e07050408030702090604091703010602010b010c020f01030905160815 95
    0x110102c0c0b000b48501c00010314144213108552400307400860f009100c414025003000030503140c0e035003101c6440c9001000348030b0010714002005040034448009114a120842c2000d103000d4683c0303504e10000388424056041541030201540040c17004c2050140c211043c04041d40c0c41e4540504082d100c040c05a1295114503000c13a29114140200d03810b468155440700741108080040c01031032181002c040341540001c6c03041407120707468005220f01c9820b2407400d03070004c2d51650050204004011880d141010305100c20000440c03818131040360003078981040142c7d98212000d040b00d00030499000450700c2600000c0001e4100d60040007036050315004210703222503440381d100580d501d215a105041154100f48460000b43c60000c2c0b1055214001400210b4a64116600c240c16202580a00c3c62151408401403107a07507824440d00b031465000382803510440a058000800e80d5803e002c01504141d10b8004440c204442070101045000d031850ba401401070304e6801c065251442c01c01040722a80810000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 5305834 1250 5304584 5304587
    0x20606040b0901030c0e0c0705010c0c020114070b010611030d020c0102030901060f12060c11010e0a0c12020a0302041d0a03020f0d090501051b010605060c0105010905070309081c0b040507030c080106 87
    0xa10f8104c96001c01c80e400018a0030603400c0c03107004010240c0c1641001404520301048080c000c43c5c0010710940d0b01c140d05071480c0d20001d400b038400d582d2900c080c14028460030000511295a0310305440c000e0512480c00c40840c00c0b46031552007010000409140049000668200c4c150055070250104d04000c0c0320064a9003040d0070903010b0342c0718520356000d087c4403100219081360702110f030602d403600d004000600c800d02e0407401c0d1447d051034007080f40e000344402800c0c40f40308c0107100b01514000c01c0180c3c400d0b4040d0002400d2002c10300004e441a0717a540350f14070a00504401c1e4149129007001903c0900005060194a03500001800c0495020b4001c02480140c40748002500380c0b10161100c40c1403052901c0c5052003600302ca600e022496681d16004141559000c025090300b09061002207460740c1840c0c1002e080d503c2c080c000000341801c1404450001d41020280c0da0044202c8005e00c410754a05008003000e0a92156410342062600c024015402d81c10342202070304400c03a448844040e66034800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 5307084 1250 5305834 5305849
    0x3021804020307031502090d03020c150c070b090406030b07090801050603030901050a030b040b130218030105010b090d03030605090a020301080d17011208070506070207050a09090c0302060304061506020606040b 92
    0xc0081d8183c10005090002945141414021554070b40c0b005080441d084045003460f11101000d41c0540e011074a1074070180b40500506124203c0c8401c5107081070303510210241e56524078000c0c0480d00001003a109120784407070f4401e800842d000131351680a410300c0d500c003130a02d80c900c0c001d80e001542000700103001810000221240440184e4a0070326020b6061000c4000f49240d001c01340d401a1030710a00046940c404002d201c1042a014005980314541c0082d8a2100c0d10022007900907418540108920990403003518080c40d030035a103030780340002c0c20301e0300702d0040885402c008d910121500074482c44031030a60166058460710f000b207403c1c442907800f060310709511030764842e016180142e0041c0300c54400407914144282c030820702d003824001c3e141d032514141a0104c5109006078401c010401c0b46143c115002d400401d0f021004201c1045c8949940b4480200c42c00040d00959001004c034040001c141c0c0034541d41c0307450240c840455911004029200c3c00c003902c1d894410381c1007032092031043c41d2060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 5308334 1250 5307084 5307091
    0x3080112050f0102030c130e091203090a02030d020313060206010803031611060106030b100c021f050403020904080309070e010b030403080601050f1603180e06040b031204080a03080109270204060510050301030218 93
    0x90003023031000d40d1004404ac0b164401080307030741c05025051200e0010b8400304080d041d41c1e40e03690061926441075114403022105aa40080f00b15446640100007a07180803089036000880e6460340c803620a4101c1c5c007618001c400042d088003610038140001202d95066220710304140084680c0c0e8109160f5038402c6802c010282c401950040d00c1d51405402d00040704412008519141072070f6042c5603407500020300c0c4203002c075815600d248000040200300c000a00c50b10300544140d049007182e80d4102487c0d5a07450000030b100a00b480020004a0704681c05a4169078a02401403d034560782c42100d074200506000034001140402d07110300710020b45110445052054519403100c0e40300c15500c410400001d49030810720180c05010310701d0004041c030602e43c014005440e0fa54000c0003c031381c4615004021000507403140441038a041d160070b40311050032102a4440c0459a010400c6440f10300001d03008098903448158080c900208409103603030080c010f54120303402228500c402070b92120304d01c04422002c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 5309584 1250 5308334 5308351
    0x30a0f021e1e030f0a0311010e0d0f0c0219080a1203050613020706020f0408030301030302060901150905090708070f0806060f0f0607060204080d0e0f01030903080112050f0102030c130e 81
    0x45408032005525094140592203000f012100001000b8148034200f40c81c80340250000b401e200020305840c842401840c0c00100128000c101e5403c031810010450241110000200440c005902e025035131005040c00003450014182c40038960784112281d50340c04110800c54030f840c0c07808228900d260291103100d200d000701070014403801c036810001000a51108904981c665400e0000c84901f0340c9440103013014106950086a80f5411428007070300e800f00c01011031089a05140b40b80000c0155180d1200880b0215240411241c8600b94141d060888a4216881c58402c49100060500c950086c0201310703081e483c261707504c5484200600c0382d112407030340c400384c1c00103e0500000003504100c0010700c5014068030006062640300c003803d0b420001242c00d030100050710401403030b002c1d02e80b40c1c1d0b00901c1e165003400c0030851058a07540c0034000c40300c1403040100c504ca4400707410041c0142400100718010030000215644d1030b00c14081c038159000503000407603600c0c210101040c8040105030550241800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 5310834 1250 5309584 5309599
    0xe0901180b13060e030703050a081b0d0911040903020d030c0207050618120d0201090201080c1c020309030c0303011d0606040f0b030403110109060f05060a05010903020609010e030a0f021e 82
    0x2c145600c412a10004400c846243d81c6850380c1480401c03c2c00540030b46072107507880903504c080c1d100d001000030201602842030100c005200d1001a80c0c000100c85920300880c1d008504140c290422052240111140780e4006043c00586010941e0110748408518902d860030007180204100407a40c1d401c00740561900107404001410860384c04991080c000b120041c65600d0a1140000702c0d030400d04140009800741c0c1d1248000b00842d84c02c540b03d00d81c0310060303654260a02c03903080d00003140226801c9440412580c0080480c141c1d00080c8202d61500c1c4030314049030707035a50b50383e43d082c5101c50303c0c00080c0c407162003100c0208842d4940101202c0407a40ea11840000c2b46081c800482026800500210b091005444482c00004003c0c0106250107008481c00030700044452810015120000c1143d403080710054014002a80c0040d280300603240c060390143d0312842040c0c0107039002c800d5040500d070f25100702c114030b80420540d920701002e100c0c030030342d9041e00514550300d40c500c0803907a8002e01c5500c2180c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 5312084 1250 5310834 5310841
    0x106030c05030402091314150a020306030a02010f0318050303060a121a19060605030702100606170c0409050906070f02010c0f05090117010906051f02030f16020603010e0901180b 78
    0x1400e185c0c90390805602c02100340804032a0b91010010480d00182e0742d140c2e000350351141c04038005100d1199110b40d03184015480c504e89403000035103820f40341e2002810f0040c90386181280701d20a610041141c03401d071281000204071400c141c0d9890300304840651042800d498042410041c5409540c0115031220302c0c01c00002404030040d041c0340005010300c102944680301d503142e0f5034903405403d000b40400d440b00c960301e007080311000381410341540c10345689030f0030704100704485544003000c03400306005d0080d4102140c80b0900c0d503480030b11542d441602c00d0380c1894144007554001058150060031903807200031040324207540580c01c1c0d400ca540c80d440814500648511440c3c016401800662414503118880c1040d0588000c1000340c00c5e000700e410380d0303611347d001e001a08206041c403142e4640380180c0f011480c800e0782c0c025568460142c040c1e42903000421081c03900c1c00b828182d41300d8981e00a218a45a43c1c41e103402031a03411003111000308941c01c16001d6098960750800e0000c0064010905811698 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 5313334 1250 5312084 5312089
    0xf0c0108040f031407060203010303030b090402130c0c0f0501150e04050304030209070e090a060501020d14180a030605090102030a060b1305010806030304031e03080106020f0304030f060e01020304030e0301050106030c05030402 99
    0x1400b404040d000c0c03004206a4021142240000300b41051041100503204e5045080c0202229503480100703000d41044414070002d60b03240389048280701c800507408680b4101c0741030b0440d800b20020314014905000207001e001008419040300a03e01d21046c0c1421030180e945614203180d00094a0203051070308104020b00150800181c900e600c44658204418072650100c04100c14140031103440a51503614002805203607810f204450701405585400e1080c40d43c0d1400c0042c0314840d0074065482c0001da100321f1140342c0c4450901800660b00120700708594a0512202400f1358070480d44100100d241c1940481d19004000030748000c0c40381100d4010700641044015130b0322081c0a4a02981031005000c0080000d0030215400840b1030446c0e4640014081c1d07290150042d0010782024056410595074040d10b04000415942120b411941440501c501424a0001070800320594000307940000104818190041503039070b03108005034000c10039a0780c2c40b1300450460b40040c03c0d110008404101040151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 5314584 1250 5313334 5313353
    0x1060c06020904111204030e0609060306042c010f0b01090803030f060604080102070807120203030105010212090a0b0c010c0908010c0e010305060415030308040308010e1905091e030403050f0c010804 87
    0x2600060030015003050f400c4450b0f213035034111400008010600d001003104040c4d001c424401005d00070350303030142050603000001d50a1b000040c07010b4019695001039800280d40c002079881c9a04040d00e406d44943c41b510b10240c0a0281c00c0d0b90390800500303185104895501c6041232030110ba051601841c15619038180342002d0a40280500382c0c060381c184004140c042d130a100071701713041e4811941940d03107041601c0d00006014001c044501035410034401004030b80d8001c1421581e85040d180056614528000020605006070300451025500400c04c0c0081c0c800c15800001d83c2d540e01d440b40c10b1480c1d9a00b8181c3e0030b07a04203800c2140007030040e01411045500941041e0f410010007800422648403145103030080c00e0f03032a4803d900281002c0c0c180018180c02034481c9024054914031502c030b07454811262900b0f200100b04070ba49083d5500002000d600c0b0600c00b036020f40805540c9420703921614007980f6030b2a08a40425181d44c0545424800742e11f10000308042c540d0070603115000d46a442c1c3d22100d030603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 5315834 1250 5314584 5314597
    0x915020705060f0405030c0603060a0b0d0f050a0507021504050309010e0103060b1602120304080a020607020609030a03021608070f090e030d05271b040e01060305060f01090b0102030301060c0602 85
    0x15446040310200301540d03a00050714200751199105034a644c40c11081614216010010a01071741d03041050103080e899686280058030a1424800e81d500c9589078080002e1603d2500410410b01c0c10041c0b0032501100c0d00064051600d55080703d0309000c00380d002c484502303030a84008000c0e074010040002e940d4000d160000300048141400608a9582c3c600e280e106e5014086c400e2030901480c800100310f00d45203403550070407011540254102400d1140a03035990b41d90900291042c1c0021650300c2c110340c0d400e0219014060301805031200c80e412482c01950341c162095802c017040b2a40305d4085070003140005c0203012151603460f480074051808900000400450009035a14001000042c1c1c0580440c040c807401054403002072400e6042c103101d410040c000c2303411241c035981c005070f088596040251440c0540c46408a600103410f402d912034440c014105984018024004d80b001c0004407941d46c040c60f8104d41159030309020b03044c0d0300001240c892200b40903800114407001034460104106901030241d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 5317084 1250 5315834 5315837
    0x90a0b060609040203010306060611070f0303080406110c0606010e040b010905060901020703050d02030a0207061b03140c1002090f0301050408030106050c0c0a03080705010609020405010c06050a0207080304030504030318060915 99
    0x42c00784100089000d0b0790098000740c80321601c0300420004240d100c0b081d44104510031016141f0203003024007604141150b88070160400001d900820107201c41a030240c685450f50011290b56280300380c00b629104c83c0211a00d0340869030056112090341005e00544404480594039260f1440c10601006003c8e008107039803504500c580c000100000b441000800c0401046030019602d9140401000345014581e4200b0010130000000d01044030010b0714900c2c070520351504042e44a101044402d1400c0e001e201c003e034015204202d8201c1c8003004903402008034000c107403034648401c1c4803501858242c41c002d440060030404108010007910b840740000e07180114203a01900d03685400c890002d00c1d52503007a0820346001100140000401c0030903c00d80c0d00800ca10740c0c0941c1403e00c0c0c0b50010b4031081c1e0001002c6c14064031480002c0c2c2036642641107514080d4006c028036202d00b8030b4280140301d60464002100828000c440741c0250700f00c2c250b044d0044417082d540d808101400c1803013030119881c0c440360450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 5318334 1250 5317084 5317087
    0x60906020304050a0b06010c150b041506050703030605030c010801050904060905011505040e06010f060c0f021e0a09110f090120011e0b0609060c1002040e070306090203090a0b0606 79
    0x22100d00095004500800051502800c20b0401c0c5403040b001a080505101341c42c01a84002003029107807131680307000c0690000300c0c0c4c00c0260108000c1c10b00000000c0d6068000303100070038025080405456898003954041100d0798071081455510410141d0f0309020540010042109140c1100340503800b1388115000326141545540b075a09540c20b00003425020040104140494203052240e416108020402818607514011a49501c3e00380c50151904112019440c036090000ba031200300d203515400b40c805118403440d1703900c55220b030b1070404d4014412040f2480014010801c1e0140d0f2040e045680b94880c60701c040c940100045511802150b0f050000c11810700307680c4503030360302c0c041d400031081000481d516504c00c00340340031000e08100c49040030b4540344280c5910f464440942c1c010790f8094030300543c3c1b003803850365403854201041000740c4402c2c000140441c00e8424002c51600074401500d0030b000e11526801014241d01007214070310005d2b03002a2000001c1046851259044140540042d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 5319584 1250 5318334 5318351
    0xf05040302090c210c09090702061b031f09020c010b010801060503070804060b0414100f080705060d0605030a03020a020102010506010503040f110604050301020a030e0c0102031c020309070906080a06060603052206 93
    0x26001d410443ea017044850001c22100c2c90f5040c58146203070322002501c040c05543c9050f001040e444654000c0215001134080000307203000b05091b04400e00e5550400a10f03a140766030b40e00b410080d60101001c940c40b5400c1001000b0301303501941e05207041c3d038400d490f52411691946421034010800030425242d20ba2180802e803d541c40e944200c150303484040d010a102440c2c10414103004c4182d0781e110f035040005a00d020407a50902184a6080da80111149581c40e41c46d4001e000c003405198200c1645405880d050390101900098402c8160b03100707070000d002a0b610003005480718041258041d24440260b460b040000303824903101c183c02c1100424950600c0c5e00d6001007805c83e001110000701003556400f030096800d501301704090081c80244002c42c501404058045050000d84105207140c940102c0811141002413080c44050414130904112065030b5146440d980c41010006648042c030704200410050b11a0007454481c0000300040c0d01c48044000262108100c003030340640b4615500c0241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 5320834 1250 5319584 5319637
    0x20d0204140f160905010c0602090301050f04290403120e01060b070506010b0301050105091903050d090e060d050c0f0303130b07021201090c050405150d0303020a0f05040302090c 78
    0x2104039103504035020080c54a0580c24840c5004009802030251075220700c03c54074101e42c04602507041c3c98003882e14103500001c502c0d2001c086e000e0b803200da079810b5003005c0401c18a0340204145a1183e405003484140350000542181c4c110b0888401d202122680c0d0310000e004a030080364190305400824600140100185000e142140d11980046869102c0040d00c507003444003c2016234007500c04400258915458240083c001e441658461400740c0c503640136a2003118020b101440040d0703005025103151100c401e0700100005428081c500c40d04200320701152003802c1c150780d41e4a00310380c44402030000c0d40c82201001034100c00d03403032070552501c41002038410800d07a20541e0001400610174007a100c000a10400051504080d1120400c0e0b1410186601003452040300404441c01901e0029443c1c44142c0b411185141d000c11703164012009240b11010990325500504c4400c401e56a0283c1c84502c19000312050701c11440040e60143c0d59102180514038100000d154000f0340503e03441a40110018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 5322084 1250 5320834 5320841
    0x70b0c03190801060306050102030c0a021c0606030b0601110c0d02060c0c0310020403060507022b050705030c0a02010e030a0503040308091212120601030509100507200705150307050313020d0204 85
    0xc0e100008002e603004010300d50b058081c00c40a000c003400550700b0000f40e944800e540d030f10f800d00041d00c200c810340d07060802040141d20131110b00340c0000b0280300064881c10542a540713000e40e0480d0000b040340703952250009000c95581c211f601e0041c03110082ca0000d8003000304039000180522524040c13860584030750703075042003103640302c20781e941000d41c0b26842c50038048100d070300c028418003d640010b420010a1182c0400e040c00f10150040c40f007004000302c00c0700f200c140c0a031190041192100140075602031a0010303004040c0d91003640c81c1402d2401c107d00b49602da00748050b00408591051005000040b552030250494a50107810700b0710003013121031814034004c581d462400d83c0301400507603140d036002603400842d44480207080900c2541480c1b2903107590792020b040680d007150f41e0780011525851041d0540340c40c1d068681e511040403003540d400c0644414461003140c0c4504e0128002d0056080800d003540c0c410009516068119a40c0b08003019010b00d07200e000300e9002002c080c912005039038911 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 5323334 1250 5322084 5322127
    0x110d0b060907020708060115030204090203011706070201110a05030a09051e010f02040521010605090a0e0106080a030e0d0507030501020301090f0f0b03070504090f08030c03040201020d030207020102070b0c03 91
    0x1051465003000c50901051581c068210030854200e00c10501c0015800949141143c2409140e400d07041607680041b0024002c6030800f000250002000013010411000c00c0c05005100f9015144d5036150000140e00703ca400300f02c3d200080038181306994002d030294014507800102000003051007030307155032520305081e400e9002c2d200498008a0790750030b840013480713801c0000c46544403c40c50f26090400160010035000000d8001c0c6058484008c6281802e420480c02040064030b240e196040032841003018024110a1490640c03070000c001403605000a00412819055141c00c1c2410110340c0900000420124040c0d4862040d9880000040e0091005500030227038038000043c1200b49000c0901910b4400354050a200d040c4001102c140d90041140303011a1821600000d40781564038051002c1c840300480502004404000c11940404d104000d603c60f0303100741e09a8101c1004c1c0c000c15400c038060681c4c00390069018680610041104c500148110364000085908041400040c0d203585c01501c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 5324584 1250 5323334 5323343
    0x807060206090601090b06030406090602090a0306020a022107060203060612040303060302010915080703330302091b0403060207110303070303060e060102120f070f0210032301030506070309110d 85
    0xc002c0040c80d080500045001d401c0040040c00034603c1800011100d00028101a24056941482001304815a4112141000e01400101c181e42d964140340c0e00a400880041c005409105510804001c0c41da640c101044040c4242904016850702c40c0c2000350001001603411031310420080781d41041410b040d5115038429503011079400c4c25880010010000b43c0e04c03c4c0360002c0021003e850050f0000f1070340342c3c887da140c03400203075000d125a4407130806141014040341048c02c450500c0c02484107000d02c0003c4c0c0c0d0095966074450b489942d040064410700039222001e0980c1884148001845500200f8000e4000c40080c00400c410400090840d031140c1030440100ba03540303408010504c80c41c0e41e603981c41b510034005040d500c1c000c2d07801d0b0081403081c403031004200200040c4107020080d10304254040c640c0c014140d520070329035048001d0001e10030382e500600341d07a8805284d04090108400154107899002000d00088d0700c4405007900a825455070480e4681002007a4100030344030501c815803c075018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 5325834 1250 5324584 5324593
    0x3080301050307090c08070305040501060f12120806030307030804020a0e09010c0306090b010507020d02150c0304090501050607020f0409020a0b0c070501110a05070303050307020a0501020d06080d02011b0e0a08070602 95
    0x10002050300d003000e070f03a0107101d4031030501511745100c03500a0041c0c1e41c003040c3d5080104580c0d880d860658010151034100a00428611102080740354a200b0404101c61040c12941e040b070034406070940c0c1e5940c0440c1c070164540d10402c4014006032103030a03803d8200744040c16444500383c072034509003051b600454220340f15a640b07400c41c0404a1341802584000c04000000f000f0341416103000901602c584140a4010319140c50503508549501c0c12544550101d95003e640f40c0010490003501d0745c3c4540b1a04070700074108800450145005401c4405041c2d00400380e00c0c0c0d00b0300c0482844081d1500d61026030f440155808002105030301140140b040002c1032029064460a0200240081600f01403442c2c003070307002094900c009180007031440c040d2a00750808035120750341c8810807031501444d55401451540003080700f030346c04101a00410191001001900d6480f51015004c0742242c043c00811440c01d140c24020103580d900412400e86500c00c09000f08000070303120740c420340c64011964003038070046c0d20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 5327084 1250 5325834 5325839
    0x150a020706140c1b03070605090106150509010c0b06030f070b03071d0d06180c03200103050702100b040b0405150103060e010b030402010f1205040b0403090803120411061303080301 79
    0x10640719140c48150610042c80075030408120368449405030a4000310088013482403504070315000c0041c2c424050f4001020720040c500751130788a0180c103044c411001c100c907050703507640c071941d004005030f4500050680d110710003107006132209644910050f00d010b815009a15001c48415000c1c0450400f0f0106500160b03500e0801b40c40050540d401c240303102c03218900d07c1e8000d82e40340e99141c1400320b03070030307004240441c0d5000220001240c55215890081030040458000010840710329201250355883c01d418818031400100154107481c0f00311404e4005812040701ca138440d00e0300750303c8a50119030241c0300107120302c1c08002240c11174a0696400102d01030b840d01c4002c0b6507905000740005800c98a02070031182d45003c01c20f940c980030152009052020030305a00d004680f0a044003d00c03440d03858014821400d25050540400105842c10340020380b80500128243c03900104841d0900c4608500403000d81e2140c8420f2100e02c041e440c0703158426000c12205401c00b20145e0440d01a500031980c1969070752 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 5328334 1250 5327084 5327093
    0x30308010614070605040204021c060e01090b010e010c030509130203060f01020102040503030403060504080f0a05070302010506030606031209061207050d060806060f040902030703020604060203070614040b1305150a0207 96
    0x20140d024808101410b80ca040c2c400c960780e416034a8090344950081085e813030f50f200040190003142d40c001c61380c2d20741c840700c15041c101702c1e005a4105c4050400481541e62078014003400d55402c0e0740b5050100e50624103146072540314410f01c2000500914000f428400200c000038081074408040302005500401844494900b201d40f056040109000861815150201003601c9010f0391101070505d50b644e000180c180b0091801321003400c0704450031195074070441c1c80064440d0700402c0040c8c1c0158600350010350241800100c40d402501d00400502002c0035900d07028190398044610700b901f050f428015050f038082000c00b20703130045605441d01070b1102656500401121400e038891401644000103105190700d809510781410780040d180464141400d0000c00e207443c07040e0384025001400000c00140c810b1380031001e401402d11a5109206000300019100302500d001c3d200070306400042c0f4086030184860304144100c05202d00103a4a41a502400c0c03504201c4040f1205a666070300094024100b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 5329584 1250 5328334 5328347
    0x5150301060b040602060c031005031c17040b0117010209060406090608070201051513090c03050304261207020109031e03030608010219030f0b130905010c080c121302030303100303 79
    0x2d1a95440e030034182850288000d5035020301510070203c181c400804616441c2c5041c0340540980009030445042e0b060181c1035417503211f078800314800014806c800300802a00d455007640c1c00b881c2c0000c0120843d90810008000d54083c0c040007814565007040804615195000908002c0c0895201c440c801803503c200544141070003000309045901d090100000c1c100103e0f140320040c1c5054901141c5546629403e400829200c0800f800c50095108004100000000204250351140489030610b0500040c0070040000c910509003140e0800d05040380e000c02002c000e400c0c0f56005140400c1c0d415542d0b100c096158041007030500365030541c50700311000e02d501400b40c9001881544001c5140284509680c0d0f0f04a54421017042016101d05900116020380c4d00920329428000b48080c1a03c0842c03075440c401030200cc48100d4041d420000b2080e003440c043d0302c0c20340c13054014040700c07442c2c8854100201c6240078002e100c2408180c14480e0040913803020070183d845150002e05c1c10701c5141c01d5040c09081c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 5330834 1250 5329584 5329589
    0xf0510080405031206060903010f06060e0d03090b030a02070b0103060605010216080c10030608150103020a06030501050901030602030a021312050c09071202070501020408030c0304090507030501050915030f010515030106 96
    0x3480361036001d210004900200300e4908107001c5040d00c42c243c031031000140ca40d00ca80301140e03625600b0030940c60890384880d84a0421507000707841d0f0010814110060015a0380e59807030140200f44007400030842004128011540030742140300c0107182c4040c030741c0c43c0000040c081e00140c40e8503907070310810301141d6010800d050b202d20421048450851400c10344540c2c40d101c5c0758010b8000c1c0d2108610745401070003504854007a140030004d94103840300c821284801c8031001d02c42a072140014000000d059400307842524166280070f01103000d240e0035600c40304041d40c0301030300004180c1d0f0b0803c89011f100c040800ca20300035040a420b070040d401daa0b410300354038210703400b041c0501c188011018082c400760401c1c060b2401303910031071001d80c4480e160b04100d4028042ca0340484c0483c00300054850110310080005c2003a21112901000070740c44c3e4502c2101211b074240922500141800c0204001402d00b040072020044028211015421249009030071340d18281d41c034542070136601518218a1401f030240e02d01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 5332084 1250 5330834 5330837
    0x1050c030402090105011b060f09020a090606090b07030504030b0a06030b0f060609010c06020903060f06030706020606030d030b041b1d0607050604020f010c08131403060610030c0203070204060f0510 87
    0x80d42402c1e000101904818452107041c0044902c0c4c01b012100c0408018040c0ca80100080181c0e08e0356000c003001804000701d08034031a85502c030010591002c280319030300550308155210342d265801c164114101e5404007c00303a003400404c1c08008001780e05800001d20404801c200461010f24519145d545800c004e4100011350b009207080000540f00d02040d16840c25003441c0088000b005410454028801c0c0000e168040c02030b0010401d001e115421098000d050540c11100141ea07036900c00c0f41c5a4034244e807800d5050300410341044003980709402c080d038092401880050480011420803080b00c484900c804007041c41c102660406060310780398064081000e82d00c2510740b041c66500d00d03448000050000744603007444032101c0076603449900310441c1c440d4080c1071940c1d40d140385902c1080c10380240c820070000c00c01c9100080402d080100c0e240f4040c0001a00d41c2c01081d102503002d40c0689845621070003181300c2403059070050381d0b07107009402c01800a00c0c1c502522030f09203400d200032419507160000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 5333334 1250 5332084 5332087
    0x2040b0a080903090108150a080304080a03020c09040302060408070201090902030a0603030f020706090e04050129031006060509040905030904110706050603070e011403030415020f0606120d030e010b030d0f0201050c 94
    0x40e41c01c203d480787c1c0040d44111108400c61180002020003805400500051101080110310359100007030100c140b6010760209c602501c0d4040400c000f092301142c0041c0140c0142010a00040c1c6a4026085203481410000c0d0640c2d00c0702480c000300d810441d0380b00b0005845410400505420500c0550030704800c1c8054403081d400c0600c00b034a0458184160309240344418001810300200707600c0303000303141c0f00c103c10b04402028424100c040891651441480703805860001d616000e942d01c0394a080750f60f175441d59400d0258090420008080c1c403142500c0c20b000030000004c02d6500d510880010307644090341c040d1100c01506051003241c1004201500079031102c0700c140f15401d000e400c50b83c11102134043c218040000303000032034110b0140303611000e8804070010b103000300c0c55000300c1d9454812330342000310740e0180c0d170714010003041c07143c018070b010401e1300222451071046200b501b0001c46002c13148000b084503594880400d1410003898110701c0040c0c1c0c0700c450040aa542801010b030042c1040741480d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 5334584 1250 5333334 5333347
    0xb0105090114010c050705100f0e180c030405070305010c05040303080c030705040314010615120f06050f04020a140a0302120a0b0102070605070201021f021e070510090503040902040b0a080903 84
    0x500082041d03076000f8140189134424008200e0200289006450041d004103000100d002c00036043c8e50505000c10b021815034405c551190a094050081c1030340c020b1500b8165482c3c02c0008105079201810980d1680120034001c404203030700f4042da0306e405055907902c030764440c47c5050041c54850041c2c00800e45c0e074010018004103030b6206003603800340c94000b0444020316031030000d094010500d0364400510640070384820340c5000d4002d80348000c2100070243c144411000c11400c94201c5420b80901d0b031780f00d0005001c00070340b1700f0540d014200280c01800d01d0400b4804c406d1030601c90b070300500010740c0001d80004401030f00182d5200f10320f4004411035000c0c0305041c10b0b000042d440740c00a014030802c01002003560b000f968800c0098105c5c29840740842d0740541140b02034a03029501043c015141d03101054140d100001104003200c1107075401c032005d4050014805480340c0580300c4020f06807080e100034040840d00c170000b40300500080402490340b40d600c10070369001802c1f540c40204a180d40d0741003400103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 5335834 1250 5334584 5334599
    0x15140f0306010e0c07050f030d0c03020c060103030302030c040509011e050a0b07080307030b0d0302010b03012913090206120a050601050309031b030409020403030c020411090a030602030910050403020105040b01050901 95
    0x1c150658400b0018070841c0d0b600c4640070102070040d90b102501340e1040160140e22080d01200404032240105400c0c130590140e590142c0a030321640c48008200c1c0d000100420201340310758051034100000003540c600d8541e5505c00110a00390070f03044400ad105201350712802c09070340703950440002d00d001c0e90781481c980c2c070340720700e140a80c01024800740107200f00000280ca440d00c01d40c04031221703050091401100b451141002402802c80056450280d03180c5100c030b1040005001c00d0005138800e4a01040030507034010180315a031301c1d40302d03010070407235490f0840c04c00107980c0c04014009142099881c6940c1c0e181110241e02a070f5005410b884c1440401c0060040c070300004000c54024414080035880d020a0009800749180b0440d0b12030310441d440890048105540640e500c200180219014040d40800b201012084c2c441e40d1211648408124410000226107070042c40d8001680b8040c1c8100c401050003c0082d10000c68040740145d56540421040084c0120481d01401080d07900f90b41d6036040021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 5337084 1250 5335834 5335843
    0x61f0903030503060d0f030809150c1b01090602040e04060b01030902090609060f0a081b0402040501050a1b06060b09030d030506010f030b0d021201060501081602030301030609060e0115140f03 84
    0x41c0410400000140700d40e1074a01584c88565840150601418158240201019000c2d50030322064014103100402c81c402c00a182806592000c820901c2c141c0981d03010500300d8030700106000c40d9500c0f440c1c0c8001181d203902c0900001c08000d00031144520703140c1340c10700803512103003503c038103141c07030012030401680b02c100c00d00354040d8058501006648a4800203514146034150180d40440c00309004a580e200114585a580307004070100d084070100001040240c6c0a03a0040398001034042c846800020312604120f101110202c0b42d10960141689074803064804e02d130050100f0a10019844100c0e080c07c20501d003040420b03203401c011038104440001c0170345060038002810961a015005026a00c40c4002da4995034000c092651f1494403603c2035000e08a1407041a010960242c0000c4e200c000400d00c000d0600e034280d0186295a0a50352090010420020140c48483d942d40c0d004041e040309104110340c0740c145003030741d690181c507020300400c86607001c500b094010107511000001d16180003a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 5338334 1250 5337084 5337089
    0x309080d08040602070609050f030d06050d0b0402010309030912050703020901080303070903060b121506040e060702060a020310120c0e060103060305100c020a050a03030606020705040e032d040806061f09 89
    0x19004d82d441c078440c1010005010130351000390150244c10742c0501c03514400001450039010300c50003803115036910010482074180c0b5400141a41c603401000070015882a400428294800c0c01c08540c42d64a521744c1c94500c01380704108a509078003007070050083d032825070102c45c01050940300840c950702d0b000310002e00702107503440001c1025460b80102e42d0256240d04101001407500c1c030490700b01940c040c80c070703035940c280c142d81c01c9004920f0300f07103903001c0c000d0003080071417190080d030700200703000e80300c80131f03542c00941c00200310341354981c076107070780422003490450360f523400c05000c2c2d00380300241c80c2400d52120701e4080240003241410702d4890108000b91010134401c80f266100000000e0003814080180d0501500c3d40c0010214020320711218100340e00343e40501c0070b6a05135421104001c0d11a01404101c900604502c14258410b003c1d400881c0c80100d03612421103400d0900f140440c024541100c1c0b5a001900701054a03009842008058149054644141213240c07200c2d00c90840d0165000c1c00c082c03e80e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 5339584 1250 5338334 5338343
    0x803040308010e060607020d0203010b060f19020a122604080c01050105010203031005010e0d0206030405030c01060b0a17060a15170a09030c03050d021207050408010b100e0118080708010203040309080d0804 90
    0x120708c1c640039503800b940207a0515101801c2c00c0e80e00e5418807140c0c6015402000305d201040a00c03241d82d08898800a81500c0c2254002c000c413007410201c2d5401d94080c4e400d2422021154110300d10019515010301085026921500c15142c0322580015200e0035a40160082811540300340b0403c000301c8080b140d444121002070900251844030400802c10803001002c010703410110000910040150000091003a1981f0707170020882907448000c1c0800601c23824210340002041c01c0f2809044020060406400c640010036a80985035907a02400c0031008030702c00720780815180150803040031501c0c8925907000010b1742c3c04000c24407843d54040c06111480101804001010410800004c4250b04036400000b820840408601d010103000700240c2c810701500d5010750810f124480702d070400902c5013503021050380315400c190302080300446292142040180c1698221000014098000c0c440c400c05840c884002694a180c6403c018100ca0078175400507515038840c0001850107a0701608103900310b64003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 5340834 1250 5339584 5339599
    0x5061b0405030303090703120905060301090e0c090c03090d05030f01030803060a030c080105070e010e03070302040f0f0203040c05030d0203040b0a0c032a0201030e0111090603090106080a0803040308010e06060702 93
    0x24010224050240d9004140c02d84000011300c4000203001450714200ca00c14003200c007805803641000c440b020745a03c84d0a4000c1c2041c0010b00000249070040701c0450250002c40390301c10300140011f04544800d445e80700303042e10000240142c81c101030204240091a90800528505041c40140c01d180b0052002070861100400814017582d20b6494031300046400c200040300311a280d00b1258000c210a07030b41c142c0031810f4040360500c10350207502038044404005002c0c1a41c80d285400f07101c003074400b103184054015076031302481403050040c0c400385000c1d40c0a884080d45c074505100031307d0303e40304074012034005540c0280300403c04406001c0807194061464038011111184a01e42070b01c209200d820540d004180e8a03003c0d510b442041003071000018004d9a0511404d040c650f01c00f030807919030401091918908010348005803d1100c01580c01c02c0080700000b5100707546103140d40c00c010000408843d840d100206000c185540040c04501502141300d035400c6900700f55000031500d20468100a0003141e1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 5342084 1250 5340834 5340871
    0xf0b0601180b0309071202180703020d09060e0106050405061e010504050604030b070306300f020409080301030302010b0a0e06010c06060f06050403050f01091205030a06030507090b03190506 83
    0x41071040d0010360303020060700c4215a4031041c0561441d002120314030b860b0b210303100001403169a0b4076500f80800b50042c10171801c00104115407400a20700500c40d0042c50b8007081766140307000c1da0340310b0114140c0c082c1000041a4900480980c2901c21550045110380e0030001444520f546540e050320b0b840e08082c6c0c04284007403280c001640c150007998001c40d803007000030900000340203030380c0090b601c120300a94080010700c0e02c0380c0415004252004280c0040c4416001c02d800d0200320301c11401c1003a014544202d402003c1e540081c043c0c030704d810400c071201a0b004c0010820950240100305400104070b406500c0c5600f042400c40d408200140210b04208810f8503550900000340d0101001e00f1701d24200100d042e0f103440029000385e105110480b018031409101000c554010300c0360920f1282e002104600d07564006100300c81b650005800424640c0d6a01000400108100030140046c683c0100100c2c0c071031b03a400105410301d1107101014031541c403511100710000d84040b6082d41d00c645001000c090505 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 5343334 1250 5342084 5342087
    0x60a02010f11070605060a0602030406050904020403050f16090603120f030207060f0515030106030b060103020901110d0914030c0108040b09070305070e1006050c0a020105070201110303070801090b0604030f0b0601 93
    0x11803064800d0712500d040074181e060900640142140d5019090900554031901c1c180a460789040c45100010b0304203100500401d0300c10001070200070001040541001e45940311103040c0a1070f41c1894003594802100307040b100f8013081c0400001d011200b010000f0703034559202c04500c0045030701000104098409014100703070007607054814098100070100124031503058200020030042d01d00e40071140d4000703000d00242c0f405018840036298424400401903c941d1300550203500005000d505004200e02401074448040000c00b19a08140e560103411516100c40c0222025a101c07000b8041d4110901d54026a41c220840d181c00ca54804500c1c0030716a03540031440c0c1440e80a40004200340071712440014081d00c415181c9000303182036403076540380607540c05040da03491258180720a034070313004440551301546c0113001400340b45006052001031070240051050a550048901c074001c61042401404000801d11500b640c05a003074a01700d00c0c0500710384804014110b41c0000a28002d001d00020354241d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 5344584 1250 5343334 5343341
    0x3020607110705060d06030f0b10140112230901140106050403020108070806040b04060b120a02030105010c030c020d06060b07120813080706020f03040302030304060c03050f0105040f0b060406020c0102160b0306060a0201 96
    0x6c43d0422000c2c03481c0081c278074040c00d280d101aa000384002c1007800e4003141c00b942182908074a6201611001412001034200c01c0180113940d40922144060311b618002030080010010302c00c0544000005906001c070a0b404e5400b80c06802c084c04101060205000603600201c5098121005007095030740c3d50380f41800580584000c005a03a00300b81007034800148081c0520242c080000104240780c816030703075803508004030b000c244a0a4005858810700901007070082140c6045180040d04c044c18180d010b454840650320541e12070707500514001141c8081c41403d950503440f0401a142080d4a410549920b40702c001e10004040c0c030b09640018403100b0448141d04407822000440e406030384030702d81410080d4403038200b100c0a607602c908080d14010190311a01c1030500ca00090804030145034240010f10000f0514a90503aa50942c0c440700300180783c1d6a100640000d2031550f00408800e01403400081c20012890a1640740d40b015200900c0589a6001682d51046007519210740b100c0729a501240907 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 5345834 1250 5344584 5344589
    0x2030a09020a0f06030501091505060705030906030f0601020d0c0c09020c0c0301050403020604021203030708040303020706020c07080d0201110c211608190e03060402011112040f0303020607110705060d06 89
    0xd82c0320800110300300500443c0b030458030291000c000507030f40c0d4906030058845034000b543c8021004070b814026440d00b0300c0601503050183d812070b0704114a840116505130300c10385261449003154410441107603410450910f2802d6503140885054070300342d668440024040c081c403d030150300819a242c03048420401c0a00624008000340b001b4102801d020b521843d0a4500b41c0c0500080245c400004e8030003c1282d0144081c1c0c1e1740c02c0f03440d41c1c9948084009400181d01120429000c220142d0780b80c00800011010309118000740ca1040d4070183c01034212645940c9010800340c0a1200040c035010104d0300c864401908010440750400d49030603502d091145805041d5011640e005034010b01240c040904802915900368a00e4008455001da8a00c0007003c01d180d03242d40082c0008005501c03030b80340d005540146100311a042c3c0902c026000c50740e00250001c00f50302a00e0002001410350400041d40c020100381000004101500e030580d45031074880c021035008440c000384803074424503141e1001c0700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 5347084 1250 5345834 5345839
    0xd0f020a0204020f030906060303040b0d0b01090801020723010608060408070206040e0708040302070e0c03180304180207021809070303050a020c060a0e09060604050105160501020403080705070303020d020604020109030602030a0902 101
    0x6441d03444010740310085d0000c1d2015040c41c82104001034403824000200d034244c9410342582030800b607051080b00003a0031f1003405681008000b880c00102084d0900145c134001d4071569081038030441d8600c00d841000c061200b000c0343ea0381884000c001070760f000301d41070303810681014040781c1d659114000300d10380b40700d6a40041440090b21713082100103584002258001c0c1d2081d426901103aa66140d1100211800d440c6010401820800305809000074241c40c9402c68104058174140b90755545902c50901d0f5030f4500d01c4603290000384090452802c2e80c031404030010010231030034460903c0448141d643c00d0304c0c00018284140020081034031030007080713100703050344009120030380d03440128100421101030014194001d00005000c60307100d10b00081914259a81a51140e09280401810320505884110b00780c0f081d5608200200104016038003d0034240c2c010001002d01601c0c5180c02031030010b002c116201150441414000140c1c2d1100010b421030f42c0200000d43c69032511100c42d00144441c0e00020b5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 5348334 1250 5347084 5347087
    0x308030406090f05070806090102040303050d0213030b0a0c0e0910060804062004150f050901050d0b18060306070305010e131a07021e0105010315110706050a06090f0e0d0f020a020402 80
    0xa040000c000b8001702520030202c140d0b0a0b54480313019140c240e003d24000140401c83c00d202e4141041e2490703020b400b603680303907004010f640c507030781e483d10704030b1003400e0321400001030305c40302c40c0701c1d40c0c50b001aa0f0640d04441070324292181c2c50801220200c0006070301410f0100034040d000300e4148541504600c2180c2001503203216240c95000002580707522900c915904080314103d502c982da40141c4110b11031910381e854141c03924000000440343c80d40b143c1141b20490756210340da4001501c5c0c3c44084542c003a8400300307070340c0136041407000c052400c100200500308042c100340045c0020b0145204807034101d04a6552a6241d09880c0341460a0011140940c100812a902003115007540003600440310080c418030008030107101200b4030b09848090101504c501c440f002503440c0e070199a40089003040728880c1c0903003845890b80d41d0030156201030b42e01e4840e41e9140e81040c013615017a44155507110b180044100030007a11200c4050700c0b200119a00001d02591951498180d0300034000340e404079900038800c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 5349584 1250 5348334 5348363
    0xb0a03050321060103090c0b03070c060f0f150602030a050708040504020d14060d03020c10051308030705070b04050f0f01051b0f010b0a180c0509040608010c0e06090a030803040609 79
    0x124074100c10b1044201d01040700700101c0c0995020b842040d00b40c0e40c000c1c0d0302c09400c505084c6422002d92000d0102010400480d05c20400b1512510401440100c3c2000101e49030554288290136902403c00c1650b03219070012003041880d40000c12035820701c18034281315840380c0c540d0410100600655029a4000340000350f107412b020000d91010750f807041d203101010000d032030310428403519444c0174400801681c0040c0f002c2503d0314041810900755202032078203500d410b10044085811488550014083d0350001c119042040781c1070201d04040c007c0354590a04041c9840c000904240742d404450b40590584035013540b00d640320342c04490b110050141007408000391100c80e143d407449000751146155103041e1444034a46031524040c0200d44651703022000f06001d010652000700600a03030001800810080f038075a944440c01110014041c80000049048400c18054654040c01c0600c0344501000c0016104c1c0741e0b00c034440082940e410000c00350300c031350316460b000000700101d03480548030742110748030f4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 5350834 1250 5349584 5349607
    0x706050906190c020c13090c080a05010e060c030403030c03091709040e030406020c1003090b0708010303020c01092412050c030103120509090105040c0203190302090f03031201090b0a030503 83
    0x140c60103819410005102656402d070618110364035542107a0050308030240c54170040c0380c00c410b4096180d41e05000040d070762141b030f540c02c20b9171945c66001d6406038014840000900c4001e103e000b9030003102e400a403059152003600080a844000c1006092668441d0424a064826400619681d6100c44965642182c8903a50030243c1c0200021620803401c003920142c1d5190040180e8045500e180c0090090fa4042001c025200c8100c0c415102055030b1502e0060105031180b01d410301911150f2a40300c40ea504500b03000303060400603020b00d814042130350010007100b0803040390451518025840d48904064501d4103c56840250100400e40f6040c0420f000e1f080c042440218122441610364400618016105598038000c1403041a440102e280042245d81401c0d0409001d004844c410b070303840c24079a07800641b0300b00502c00e04900006c0e404a0101100c0c1000008956038240440046051a01c8813842d000202014029204100d0300c40080a00d10346414604501031580b00c0c09494450540303448 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 5352084 1250 5350834 5350843
    0xc010507050d0b0301060308030f0405031c05040204050610020a0b0a060e010305010204061701030b010e0406020403020315010906050f03100b040b060a02030901120e0a030809120c060f010f06120f0207060509 91
    0x500c08880d490102d40160f00e140520484040340d07803041a0b582541d075002a542450500100305440c10f010400803c0e6181000440502132104a00000215820b0071700501040f10300040041c2d0141c12000144100c054000640c4d41c140e44e8044080c0d0401ea94a04281000d03081a41c000e4185584100c0040104003040d0040c00a4a46030390301c0e03000313041802d0312010006d00b0030720000e002c919840c40180942c0c50382100596202c1d0142a015107071076500e5010a140580042c4140001285d9200500c040300450140100030304c4e00715005024009620f00094035114044008030704255504506082ea850341d400041003d1402003115032038030100748000c0d442c3e80c846111140041c1528030440207401d039602c85d0403c0300c400603000300020040c556040e1010b56003c0c024040034428440e101404c50845401000c02c040c240300a8007050174030288451680606810031648401408010700003594072051b03c2001003d95400440c1141412501d1b80003803189240140516041c8400c00c04841707030024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 5353334 1250 5352084 5352097
    0xc030f030702090f060604120501021c0f060602010209010f0305100503030403080c01150b070615180c02010513020102191505041a0907050a050415050301020a080105030607090f030201050c030c01050705 89
    0x8440c40301590360000041000352044401701d60051003440f0520112184070100704000c1d1050000515010b5002010020002c4514242103000e440741e40d40c40104109000c0d500080480e40002c0d820448400006800e0300c582d45000800c25540d4000240b0b13075400701081000811014054950303441c0c0320b0600b20203aa20803d21300384190308080301c3c0700d00d204800440b1002c0b6110f00e8442401c08110f07030b84d0f150240c60034240d40f003901c6c00250004101142e140c09004030300750340280c0003d02103400000290964074010403680c00315144141e04005030b6001b091011720b02a0380e4440400e001543c1c41c0c4024180303040b52103e21014600030820041143c280414076240000400c0503c0a0f6901404103a548909004268001c030f811401000241010f40000a1104034041c0000c1e4040d04d4101190880c0c06c80e000140009540c1001000395040a02600d5000b1060b0718141c0035042c04c0003420120401d19100080c1042030008001d80c03152800c1c4180c44100c80140028496420301d88002455074000d030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 5354584 1250 5353334 5353339
    0x603080a0807020604050a02040f0209030709150503060f0a180b0403020c180402010c03080703020c0a050303060a0b070c031101030b041b0e01050c060f040201020c060d060306060f120f050c030f030702 88
    0x5002040050303000013650303032245078408000c11020920781e09100c05440d090042c3e403c040d070207100804080c0e509215940161101c0c03040003d01c4a12a24a00c50900d100d9001500039080841401034031490300300c1c0c903903000151000c00700301a03902a01c10340c1e41e00b0280380090404200d04040c4010554017185840350514120360044080402c1e030880c150001c1c054400902081c1d481503004006805201030680c00102030500509005407860400e080940f20901114150800020081e261904c0f449800c041c009450829080c907248d03aa075504d04604a00000d840c41010b440001010780c800c1d0420740705000c020700180180722401c24840c0840661602d02c4c2c0105a00030414180c6510074004d6031031a44aa000504954640300d04588000c84050410b90440c000c24100c0242d40d200c0b00d004101c0c004040c140050000d185040c15411680c841d0003021001030045401c1001c80070301d50040071442d4001c00074414042003450702500e0311040a4080e03806015101000145000100181c4401c0e03009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 5355834 1250 5354584 5354597
    0x4030605060105030702100c020c0a03080c0f0a02060403061808040e04020301050106140d0b06040b03071706010906080610030906061202040b040207050a03051606061401020d02070803040512010b040603080a 91
    0xc81c070054038180400c50b4090016805502c0c1e60171040c03181d40021140a00500582c1e04160403a00403d40030038454205131022200080c09108401d000c102580780c03680040c0180a0810381540021001e00c107522000d44902e407500d80700350461550784140e0391001c3c1e01c050001c0ea83c9070b8500300c1c11030311041210305a12035440d00000103101405103100016425a03600298500b6a40814180041940000b0103802c01810301c404165171004000035406030246440318407803d8064030400c0350b018001030400e810808030319010401950000307980b9800200807122015441c4190004400030b00d2001c030701404450030104c00003400341740801c0e001e503200e009136004e0041075459002e1009038443d80c44020041d0703010001c4580800c0c42a0013500704640c80c80c50785650f07103480351202415521310350044001500c80c12051600b0350f80400208a001030340740054210700345011265504d90142d1711540b80180900000c4401c42c10082d80f05500040c0d0007441048800d031a0304104100381c0042d41c801011a40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 5357084 1250 5355834 5355841
    0x1020a0c120804020901120c0806040f0c06020309010f0e03160e0106021014070e01050d0501060305060109090c0905150d02030901090c050d0b0402010c0206070209090d02010510060815010e0a0303030204030605 92
    0x2c1840018415500030348000e109902c0c20b60121078200c1d800505070389041a04001280b212018800d640c026401003040c95841006810480308408050340b0460a40d4020400703c0c8190b6004020070200c203076507062030000711745000d01007420102e5040d0034100ca0f84040742d01007103030f160036408141070702c81541c203c2d012100041300f48c100b00d40c00c2e88804a10002d03a00c00003803015105900c0040d00ea2018500941008402c07100b8805444081e001800426140c80400109503404800e11004242c84c10050050800040c00940b580d0428040c80d40070b4a582d0300c4d82140f030f507040c104442d041c140d00c1c8011560317440d02c03403009402020740110850b00e0141c1200c0c0001c4070b103803150036034a12a4211018819a841e6540152034214140800700e0300b1100901111003d40d0707440c001c0500c00c02001010345a482041d030402821150001e0030741c400c0481e0700f00240322480d07010130340c2d81d07000c00c03001c11444102d0801c00040c0e8410003030384012944001503003c04400c0540c5138002d0301c122486081d040c0143d45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 5358334 1250 5357084 5357087
    0x518010c05090904171204020f01030b0d0b0408040807030803010519030503040b030a1b051803030a020d0804020a0308030c0a0306080c060d02071505090115051905010f050c01020a0c12 81
    0x25180c0c00000009001800900c140d49007070b80083e900688100254003005030708400d0744005412442141e11032407200d004002c154103261814a052040c246010860740341e1071400a5a1081104000f401e8035020748001020000c00d074040b1406003c401e000c80b5040c0c0da070303031426840b264003d000c2c180c068810b0301000c0315034410803103008003076a0380b18018505003420084500d80c19000240b4401c440ba44955001034101c249080b0200c000d402c680d03a8950b614180001c041230151040810f9000b0790040000d961100e901089c8140100000d00c0c0c001c0551f00d43d400003400e00c0e441030300007501e081d100005108281c0031490040000503c01d4605100581d520200540ca45c4200c82810713070003820800500041500c0baa0080132041e100f01142803c240c0484504c3c803ca5504079025002603550307100c038907540740503d1804001410100c4101002009000446490490a00c1004d047c030000c401205403041c0150309640c900440c0380001c40d00c0da50b45880040200030b1440b001d0f50071604010361800720742d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 5359584 1250 5358334 5358341
    0x1409030c0c0a030f03050f0702040609020703180b030c1602040c080403110a03091a1207051b0307050304060e0a09090308010611060601020a0206091201050c0d060e01080a02010e0a0806070201051801 87
    0x2a5002041403584d50480c0d1410758140e404944500703c03081c400c01c40e000c01030360b980c42048081c00c81c180005071910358a0bd000743c4541000d9806030b0345502e00110030000e03020b61a0417268442e00c1820741e10f4a4803014611061903a440c084000e51203030900100345c0c100c50b440301c1c05600c81c40c0207030f03544400000300701b481c1512020041c0d40900000c401017410b005094000242c41c40c2c4408004c50340b460800580c0c03d42c0b0720040c040e500000064030010303066010f031900e41400412060960090b41c03034001c42e070b03035099541d102e5480780005002c40201c0801e0566a4040d8000040c4031044081c00200210b00d00185a000d0034003c83c1d01040c405111322182a400249042c03151006800802e015001c640030441c4d1274108800d03c0d03030700c542d8440c040240d501084c05038038021076140c0812a1200103180400d03003034900c1e5810130380c80030103003e0041103c0f040001c5c2c607105168080c00d0a400301042d030000314140744844d4211540612560b400d200c903c550540c841032060010300b41d8500b4490808500d5800d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 5360834 1250 5359584 5359589
    0xb010b070305030a090c030b040605060109060207080309040f02120106020c090c03060904110301061d06030c030105040b04030809070504050c0d06050102120d1a03010c0207030605060102060402090103080307031409030c0c0a 98
    0x600c0074000500030f03c0b0700b6400107003c0c1b8000c00000303060301d941c0d555501c1c0d4400c0c100c5080344c4654456081c00881e5030016100000f80030280058074581d41485260340d038074001c0518182c800c5440e2810500c9140c900d030f0407195030070503171042c26085603100c21020b9a2103030340022050040c05a40b000801100584003a42d0198900030840c5207262525100c80c00d0501d1403143c816410355880d0300001d02100c8000c2c0c1d0500039131001651162030714120081500740140e40301c1140c0a41d0601c810000003540010b2101e91181e4141060050b6843d0003844a140007261740105c0d42091400051000701003003640030b0084c0e031044020500040341c846004903210308108404490152051013150114441904040c01d5806c94410710b002c02c2500f400001c3c01d4640c4400c0a1001d60011102401800100d022b840e41c006c0c1d0a00041c0a1170138140e0100c0d140a0b014840605401408404606028404e4206a1864840544000740382c201040111348036440f44042040f00d11800703c801c10301d410305071152400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 5362084 1250 5360834 5360837
    0x60a0203010b04030b09120c07060809030403031407030309050703030503060f03010c0206010902070f0b010b041e08030313050309030601030b06040b0a0b03070507170d020318060603070303050a0302070b0a090b010b0703 96
    0xf4503245a4515504800141295400740107281d41807a90b4002c01c400342c1089403580004051b8a40b5116010744112005010001213030403c00c0240b01080c3c004140b01108901214025610b450070704045000f0100c110004041d40101d031000001c0c03660140c051401644112001001c10284004240c01c80d5000542c8401680046004200c010b41d168060103859000e94180980c0381059500c0c0c43e84210709802500c2c0031903000c00d05010701e0a11b0f080c40090b008801c4201300601d07003400c0c4050740d00c2c08001c005a6040031020105810000140256001e5050240440d4400c2d616837415401c3e070f41c400c9a4850066141445c80b441c2c42c43c2a1190400301e68058000343d2841e03d40d50000c1380c59901c501001d0303584400c00600c1e005851440d100030400703895500801a282d0030300c2e40d16070079031500820300501e003903019005021b5140d0f40420602e080300d40c1070612541d1824106000d801078002c105000c2c004140107030400455403480d80100103568481c030403020a503a22134881000034042c40b40040c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 5363334 1250 5362084 5362087
    0x108030301150f120c030908070b0103030e060a0819020403080a0809010c09030c0b13030f0f02090a0b010807110c0604060309110307030b1609030f060e0d0e060d1a03030f0c060a0203010b 82
    0x200700c4ca1103070340700e042c50000d28580414080c00f80d1311485c13469808404220345a10b0000c00410030305510182d611050002190f6603880c101541170000e010182c003502d01e081072118143d401c004000b481d81114001e50348000c80649568030050064140a41141e80780303065400e10b8041d000c2c0d148200802c0e01602d41c048042205682060300f25185600302224003000410328103008404038081c18100c40402d48650b440001d98880751041c0880680c0c00350a0007403d0341841d080700040ea1300400302c2da030700ca8400e2605504024a000c00b41e80b50000855410b07410110015010600d07a500d0340003244198040c1c008101c5100c1c260060580e500b60314071000d011280303076001044401e0240000301800701428600529101d0f12500d03418045a40c0c10710444020350f56803542e2201000a1290301c00a04007400c110181c1c10301074008c42c03101d101d0b41041c6040d803030b0307901c2080e6444e07501c0400c62a00010003504803525125503080417440c5030f02c403066050481c450f070800951030324407038003c69060390024203e85 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 5364584 1250 5363334 5363357
    0xf0109081b0310050c07060e0105070504030312060e1006080114030604020d08090603010b1206030f031605120d060315020c030d0203040602071a0105010311090a1401020f060108030301150f 83
    0x1490000300e001400d41c1400303080710300403c05107680909402006124040342d0355507007614080007150648a8000d9082c0d05000801c00850340020030f0f503044030b0309410546040b85840c8038420003010940c005440c0408110309102202d0b0302c80c0c00071029580309488031202c0343d0321522800d070700c10304006065a242e400b800000c0c00508112155940181c803400340d032401c00b40080c000820035042600005160040401e49527207101010f41020b420500503005050180e491007026a140d11401c10b4090070000c80b11249800c1250403c1152280c0b134504600c280c036060800d0307151020386054030082ea0000300c11a8400024200d9200b26543c01a0b094025403603d203074030b82100080c1d0401441541e01c03541c20300c00307980421004124580e0f0090b010184070b11a60421001404660301842c0e4600741c06814801070a054960ba8515025200401c411204919140340107e250a00c161002c540c00d000f88400041e61100010146068600e200851001d02c07107041d000b1544105c44480e03c100007a120281d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 5365834 1250 5364584 5364613
    0x1140406120807020303040f09051905040b01030624030b07020d1106040f170304110a0b07080301030f020a0b0d06030501060e0603030a03050709050301090c0305010f0608100b040f060909020f010908 87
    0x188403e6101a050740d08203990b4a99403805003403030b9806001e00c20b84401c10040c0d0315100d00d601400b802c0c4d100604101c1810213455000e010a8140001400140e440b060015080100010900c444c0d00e0111160322140d140d01d01800c0b4840c040d03a905025200d0b400700c0d030240d24064070a80110030164002030800c0c0c0d5660329014201030360080300350340078040340c1c541c0800d01c1d000d4401036101c0d074022008004609141300c18084440c40c95480792060441c28022000021000400c490440b9080215070602090382c1c0001032503071801d07501202c1203c80c0000c42122002294104d4011130b80290020801c4564404444c2c405c580c0c211420b0b40d043e0802c010118456001c2d40c0202e421a40034508140b605844901180c01c5031901134055403081400441042001403d001d0005414210b080c04e00110b458501c503242d1b5029030801702c510140e21401d100d42c41e07031a940e10421103020380800c2440001d07501c2c12280000d210403c0168050300d4450140f5030154001c480980403224200700500103c840b4202 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 5367084 1250 5365834 5365837
    0x902040e0321070512070e030721060b0402091008090105060303040315050403110f030d0b0d080f03040305090405010b09100206060a050d0c05090403050301050319020d080a0302070b0f011404061208 87
    0x143c0080c0001072000044040d41d10a4180c41000561101d86821846600b00f6245c0651580448030500b0a90000c1751646d0345010040000e642c0124086003681103240098080c0c010b0616040e04410300c44420000c065100e034000b030080304650002c0010751561000c0c1612441180800780c1500091003808140c00182c0e4403003039102c3d00a207810728880303225401040c10709070712041b03403401940041004211180544070341650740508440d100400e406c20307955098507004251041c0c22400010000400389070044044905269004004000d15a107a410910640d001a5001c502a1440145d8011190b000098131406080002e0400140a02d02001c1021840500300d088840c198010f40002d0783e51035100c1c209008502c2605c9990310303581404149403810349041c242035007441121740d030240540c5074622102c81c0c864101c08803a5039140d0303c501c10780c0688200b0700c0042407101a4410442c1c103481d5004020705a411400752040344001440030071041c1d440301d00614103a29010041140020000700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 5368334 1250 5367084 5367091
    0x20f030102090a0b0310060c020a09020705100507020a03080108010b010806090a0209060c010506041401030b0106030203070c080d090b0705040f090509011e050103050c100509010c03050d06090902040e0321 90
    0x9001502e800d40010100f0302c078100560003101001008001e020140706030603400d002038004c5240882039100c403070700040c461652601c21244855400070f50902403100500580c220300b41002000c1c051400d01c000002c1d5582c10048003940000c94400002c0b4074000103010351280180c050f900c0c0f003020344884040050199014041d030070000e50030040b001450310768202502122014400000d4240350000601090f035800107106401f084c503a03001400054048501b072815160382d89401a240c0d91900d07400d503001075a03100064095840460500b000080b00e80240a04902c51030307801d0160344581c10b045e9aa0f004078041c02e00d0b010301484041c410000302c0e070320159100301020000b040d11703a01d075580c0f60804a581c0c0c42c00c1c0c1d010303521500140107020301008603103c03290b41943d80c0b06004c81d442700d0060040c02074000305030420041107014000d2520440c142d400d9120000801c102071a80d6090050041c003200200720700a90502110301201c10000c4203851900c07141c1811480f21408200900d5103808009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 5369584 1250 5368334 5368339
    0x1b030b01020709060303050c0601080105090a121403010e0a060e01140105071106040e0702060108060c0405010818030a02010209010305100602150a0612150e0c010e10031d03030601090e010302010c020f 88
    0x142e00040807003c41c014400118001c1c0c0f24607940c2c414140c80142003d405070010140e0742e0500e0b0a0010341c1400040e0301c2c0205411130360044072208100300072142ca00d0310340c40c6039a403180c002c0004140b458000009138086d0314620400c006840e074401c0303410b8a60009200780c0f00404a9000c0003c046e502800061001c80d00c00d03c50f02800130020800240f290300150006448440344d5420003113000d404220b030343d0161003040c0081210749004500d400082c0f00340d0190504024000c0040f8100109481d4520150204101034035124083c44030002d00030740000803401c3c0000d0416001c04e110a8000c0011000c0c1e600c0c980c080c10702e011320901c1100c210a03025003403c481941e12240002c1c6202d018080d403241c203100b1803c40c4054510900b4090945010300350304e9840390403030712940c28207a8000420400c4160161200210440c01c814250003c144407143c40c2005160762076020407000000c0015803182200740c0310740c0b40c0318be1540020a0218000d00009001c1411352103008058030b444400c0407100b6000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 5370834 1250 5369584 5369593
    0x705040c0311070309030b090105100504020f090310020a1407150e0f07090204030c0509060a05091b0c0d0f0f02060105040b0a0909030905090c090303180d020a0305060603101b030b0102 81
    0x81c40c0b0107160300c6424203900041d103544040c4200500075900580050300d8000034015401c0140d0090104143c0d441010f108982c00200c80704040d60b0b8070180c1d4010400103040e584520b562546800280d400303030030450005802040c681c00d80c100c204040c0c2e0b14094002030700f080e1038a1001d00d85c2c0000d280488240d92203100f14250071603c61020440c1d82d02814010300d02580b55481c500d4850201e04060f08160700c04c3d0300c0c0608101e9680c075044507010440e00212015101c949031913084948a41c04203401288024000607803035000140003c5003400401e0b40d55a20380900001c1d0b000312070500e0071031600d00050700a100100079600d0030340c02c1211940001445494216600c3c11200110303048540110003080400404000b185072144685178429150706925140000001c00a41c0b00c0c40f07401c405402c20300302d28516200a80391101a0b0b1529a4098007400d0b80035140e0415913a114011540e40b0702c24459821000030260050260320000303201840c4241d0b00304034036032060b80908802090581140314 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 5372084 1250 5370834 5370851
    0xa0302120705070b070c08060f0106020d0c020f0d06020306090901020c03040611030405060d1e0e070519080f0a12170c03040203120307090609050a0b04060815030607080a050a0e0705040c03 83
    0x4560004115541c82542498903491821b200d075424250001c0041e10527060a600412183d074010450800f00300140c0b4018164000d00d20000d018500111032241d08404449030a03030410580e40d00035030081d80100d40d50340d0741e81d0302c1a04842c03d0b481440026045da800030b00c400c0048601682e5135055014981065908203512200450398a4010300990061151610368044074460000742c2403a05512802c000c0c0300d100c100f44c0915640d44054810706003d0707520865482d03070200c100350304c1c08050605c48059504110880300240c0e6241011041959491000c544100915000e426641c0c2500d1440305489840e41c0e842140d010f00307400040007641c03d40101544049001100002540320380300540340d0002c118103011000b0700b04020b0b900458050303040203c0900255410741c044e00d044503020314003020305650309088c0c000c0c010400650707507800d4400e1740188200c06030003000040c400e4040e62400c200b1342e0b54500c101c01c00d840c1c0d080c180d03004540003403000348480d00389900440001940b44c00c01003000d08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 5373334 1250 5372084 5372099
    0x70803041505130201030b0307030206031501020f010204030614010e160503040305070219180504051005040f0c0b0a030f09030f08070905030604050309030d0206010e0a020702040603020d030903050f0a030212070507 94
    0x4000b01c83e04036804074080d000d0f000f1581c240c419920507031810b5008010880c10365010920610000e01400302906613555800749981c400c00203001d41800040083d0340360b43e80c030324042000c0e010390180c8060340b00e40b030f1001164401d1803401c000e100d0744032a4030308a90603000e1b440a484130b40c00a802502082420002036025803030b00d60051104035a034605841c0070b607240c00d003d00002048810401c0c021760034502840301141001642c90240c0703c80540008198499240c82c0800c01d00d04940100460501d410001702c0f04083c030b01411955007591014000d903139828510008680d900c0d080100440c90342c9405042582c411000641d000005040000e01c4544400c0024130b070a0741160111403540c0002840069818188005c0704400707103900003001a03504200e19980091001040b4204141d0702042090542d03031260450303402150081c1005c076468000303080050564003203002c1600c081c481c00c500f0300a5071704000b0304103003003940590150400c18100c108140f01940000410313242c5100302d4034081980c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 5374584 1250 5373334 5373341
    0x21005070e060c07030309050105090f040b01090f0f0501030606030209011d01030609020705010509160302030a0b0601050d140411030c0105070609050109060c0203030703050112150207031e030209040b090103080708030415 97
    0x1e0001000805944d89589002015007000c2c2d042a8100301e800e0190350340310b84407040a5808643c044601107190142400100c5103c0b2145d806400c007480c1c03280c07000801e4042045060207981c0e0a070b070180440d50b182c0c44103a003a40b080d110079078009001c11480c4180320b000103481c40c0da81c82d41450081512036a5040080980c0c101a000380c1300381c0d40d40c100b402407042c01088117031201080485056141443c40e00041c0e11b940f180701c4040c04040c001000180d0781d0707200300c00b101d07001d44184000700f2030b00e086000c100050800446040765941d0008690f44154980001d00b401298416035441c0d14240a41da00e01c00684180c2804031907664a81054100084a0b4000d54080c000b10760f0007141c503458559030040c251841a4008441c0e1039181c624000401d80c003034143c074000380d120000076941c0c0e1400e01d02103403000340f480d005650340c2104958070441264107400a0580d050b04403400d2010042c0380c0c0c2040602c0c2020312008100c12420007107140000c40745000b840e803080c0602c103541c91185007000048140c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 5375834 1250 5374584 5374597
    0x30705030f0604110d0b010e09040c06050a020109020306010f03020108071106070507020a03050106080303040209160e04020703051201080d02010e0f03041703040308030408070b0c09030a0b150d06060608070f021005070e06 97
    0x580c071141c804c500c2d9680007002e80408c60341221500c2c01c2d41855290683e100503140140010044002041403003079000b50412840310340d001d0100d550560b991220800d0703040700da0004900144540b00400c1413a845080607988a0f03034007001800403901d0310030041c1d400780e000100407604004140000804214284151801440003a014507940d01d050300c10400e0b4803000130b1584c107003110070459806450b5444010b42155600940d001070380c51803103080944070f03801200d04003038600c4040b00021480074000b207509a09040241c000340803a445c0c246000d901c1c1c0d07a000512021690090004211003483d0f400c2d0140071300000c100760307440e05480383c60380c12140e442102c064481c1e10b00001e43c031301001440f02116030710600d030f1135045082942000029440e20040380020300014280008034050492904008181d40d0000b0211020061a4a0b0440c040e1165214141c041440c0700c00245c400741c0204940c00f0900300c0e0782d01400e805610400100010034018144408004615010401d0b903241d50004258 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 5377084 1250 5375834 5375857
    0xb03100504080307030506010f020307020d0c0308070507080d09080a020f0604030c080c010e0a0302030309010305060402090d06090b070801050d060207050111030103050115060207060507080d09050d0c06060b030705030f060411 99
    0x29a403401300c0000d0281c4e88040d103414108962030ba010004e861303001c4181ca00041d8115a0728207100c0d001d05140c407840046400152610302d002a000342004000103054045914510640d140b01403104410355036083d040c401c1561580201007400c0052a00341b0040103c040028242c500b40b680329110203860030502d822003103040d4480030050b0102d68010310001d55201d4200d80403000030703055a0101340c0fa800352440103030500da21000461401da036103405860701114050300c40d650103010f60908070054250306074181c0d90700e019980400c42c503501c640521416240b02070610780c0f40c04d0156480100a40c010b100070f650340d550715400f006110400f100250b000314081c00c004103503060142c4c604030396000b8030790101c019544500c1c07003000f030b8079008825640469040043c10382c4030307a2100d044070080c0586450042c02d81c083d2410b070f00806504840400b29280c0519420000944c0b14641c81d00a88011340303000001c41d0003400056400802c900e0100c0c6e20078009400455014a440307510351454021521580 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 5378334 1250 5377084 5377087
    0xd0302070609050327100f0302070302010e0607020c040506060304030c02100306090c09060807030509070b0d060b0a0810060507030c0803150a2d0b0a03050402010203070f05010617030316030b0310050408 89
    0x8940f1040740c600d40500000481d0011106d415003c80a443e50b00d80300b5520050640104da0501818000e6210348181c0403507400f80d804a1421601c021344908504d510a403190f03140c44049907003402c2003810f4074807a9525455600c0709450796000c002034a070420180d80300b010344030180414040845c0c055010808216183c141d0901c0c1019005410158000c102c0f108251910b4200105c1d1540010314a049400740200281e942c0c0c03d50201c4400b8140304d0300485140107000074412a44e030351000c007403442101020b0310b5081d00c85d1aa00101c440d0310070810301a0008000e80180c10100d80b241c00110382261851406422007803441011618841659100c0c040002500c0d5054001165484051034800483c055140f4194182582c180d0580211080241090b43d9200000c08690081044980c0513400866061865680745051030182840e40100314182340c207900c503030000d1603002083d00d0056804080440640d02c0c80701044000b84501240ca0703074544910100c84814012a01c1014082c40c0107094a6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 5379584 1250 5378334 5378377
    0x40801020d0b010c0f02190801060803070201092403020d02070609120909090b040b04030203040509040f0204060501030501050f04152c060603010503030406180b0c0105090601060504080d03020706090503 89
    0x16411295900e6290f8140700c41c2000d00400a80d480503090b00c45681160280c2c040c50f08030404410044064100c0c0031958a0444041240c04000024040d4540700341da074425801d072120b0007519107007150002e480062800c0c010300307801940650040d2058000c10301b0014200310040d140c4605580c1d00401c142d401601c03c015100c1c0c400e80c004a000064945664148054030b419610503040b984010405444059000f01103000c040c0b0900464008003001000c1511038145401c0c4005c041600100483c0f04500c1c0840005a0394000e0040c0da04039240200803040a40c6440144005082d0243c0c0c0ca8841d81050500031403031122440e41e58029440c00d020310a901d42c5680c4c5080004100030303008a101d0f80003480104203581d0000100e5003a0b0b0000d160001c022220150440d4900070300d900300c880007103000705030303c0e0342c02c1c40540c8080d129083c2d060445a250740e0750750094580d841180108411600304038107200380c140c02600100640340c8240340004e4585900d440309415600640c2e5074804100003808138 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 5380834 1250 5379584 5379607
    0xd08090103050a110d0b030c0405100608090c0a050f04060f0b0c07080a02090403050c19030507050d030b03030d0905070b041403100c0801030b04150c0207090c09050612180304080102 80
    0x1520360041c4102c0c4104142000e0b000b102c03604c0d00640204181441d1940010203c54a0500038a44013510180061110b802c00003509800f100c1d190140d10001000c0800040190740005500c01101c0b0020702040d49203070900c0280402e030410f01c10301a40140e100c8500050400b00384901300000e001400040c0d03100c168030000d03107081901c00e90003c165a0300100a0001503902c3d00e01c907076009541410070b80d50340c04c00c190403142410f07045115400c11245d0f40a010040c540c004000703141c1d541c810010b0354600036101e50241c04880700000500c0d055032060015042d85031080c2d011501a500400480300010713a00ea05030010b0790300507040f2022a001d40d612000c80c40c14200441182c0400703440301030180c03411001c0002d01480c3d05100140000009a0100d002e03c400032007036000c1011407130000d001203596402c001e5500d07e51841400152498203900016051249044070150752008005500c0d142200d509040e04080c094001c002030004860140c19031801000140000c002c40c50000d0f0325040002d66 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 5382084 1250 5380834 5380841
    0x10050102010b0f060d05060d06060605090405060102011503080a020309030a050106050307080d0e090406090b0f0601090605070302120c0309100206040501050c04080a150e01090501050105030609030f1204030e0d08090103 96
    0xc409005040060311007109640d044150381d61009540000221682c0305800544905410b01c40540310b24502b540c0410500c0c1e0081c0142002007003964188955260a40124200c0708002040d0f9281e01c1d00590070b000080c1c1c0d00c030051032a90001c3c81100c7c03d0a40150000382400c0c400340d411907282e9035a50042290742000c4c04078400900701c00000c1e090560349018058040080c50b800c0314403a10141c40080d0030005240e110485080d04000b4030000ca25140360300d010b60020640c0c000d4007050100700000790b21803240080301c1003507a143c1c0c00360500c1200c898107081c00c0d1304110821001400b00707103c0f05840da00e03424490040c140c0d19600608282c1014100b0034211040686060710980b81000180300b000c00000780d0500c05548580941c0e403028940c440b0400603d00d07102580b810b54248035114003480f0b01500880d050b1401101955819194040e000f650780c82010080e1825030000c1c0008078105032a03985050b882406401d00d1800c0044100005105007400c982c11100c4901c04981c1c1c4030603590510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 5383334 1250 5382084 5382101
    0x901050f091207030903060504030806040b030613020f041409030310050102030405010e01081b0301140103050f04050a030f0207050a0308030711070302030712030309020901060302040312020105060108040209130b1005010201 98
    0x4605018145100c45a8544014520003121980300080c0b043c20144144c1030b1500440e04104100201d0038140f4000b000740c0400e0310124400c905003c4118024600414200d0164401c8401141c3e03403030003942408100c00080b0700080d80075035903690044084d4107175000b17140300c1d0300710030055071b42c81c03401c440b09890786682500854110351003440240200d07600300c031000f00000800d090000440e511a881c501d00d034030728101740128042d8040000900bc00030031f1980341d200042600d00384010f40c3c410074401420101101c1c098007581c4060307104000305e0300801c4242900806481039901c03880d143c8000c500310010702d51048402d504004204903030716911120f4040324030302d424041c0401d10324540003c1c0e5550320030f01036203c4007034480c52a041050700941c0b05100340c0346e001d0003006c000c2d81e54080140003500035200a031156440c001604a00c0c51040c4582480b03001c4c142c54480d51030719a6002d102101c0c00042603040a407510b81d02540c08600103c035914071441d540d894060445040c10002030035140c3d5003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 5384584 1250 5383334 5383351
    0x2060108070b04060c060209040f0218010206040b01030209041415010e07050a0c0305030a0204030204060306020702030d0903240905010f0c0f020f15040501060b0a0305040606050a080318030106090606020303090105 94
    0x354814850a030b40715044038211140c901e8803071156415814800300910a801d003184e4030074070340b18041031051203c0e0083c002c0700c01d02c441c04141d02c40c1c243c001a80c8544044400a1003990100014401458402c0c007407030308280126520000481c608114900c0d200003041d4001c070864400e0010414135000d440ca01c1d5201c0d02c00c0c074019060412840b0007400f40c1c42706503001000c0c04001f0000481e041382c0c950668004540080040c4001d030f40d03c0c00e200c0d00079030090400381d029009683c40011094010303201401120350100e8071400501c1c5c034000203510a031040c4070700070340c0e9516001c0340c0c408100700340101d60260701d080c80c0002e2103100b148000f80c000a812626682550000c40380c60300c005030081000c03e0a500d011030a10020354039407800c180101610b4116400d03600000c2141110140d2544c401c1c2e04ca14400c00c8100540713500c400800141c3c200500c21010541e000300302569030041d44070100c03d034094000d400424041d071a190340101340c6440350400300c0160b0021040202e81d075024050b854110f400d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 5385834 1250 5384584 5384593
    0x110a05010203030f06030111120a060602010e0a12050d02030c09030c01030b1003050606091009080c06090604120615060507020312070302070b1c02030703050103051b012003070503030a0c02060108 86
    0x10100040e480380002000009007030fa285000803d01e0306c082d040751003020019000c1980d00d142051003200180000d6070022041403801e200850b080d8014850120000300500050400124a0ba00d8104500041c007401e030400c402402205c88071030007400594081e00c21078075500e46401c89007042c1850180301d00c58107030400d0f08245c20f440389034480394480c001881580c40c0c003050351b1751200080f8906206103048036800240c494015114a03610803032403400c0d9003283d0162000704001d41c0070025540509503503a68450000c20040045c2101c0c08200c0c1191882403401007000c90320040742c5c11a01000368403d1000c1880000d1160462809101c80b10020a94003600c0341400300c2a203009599005034041c1242c10700d800101c40b424440b0342410400b031113100350b005540e603190452000300541406c0c401241c05200f00341e405e01414207a24200f400448040c1c0d1010800e0708074900c035288000a42480f0700c01c3b80000c110800203e42c0c280015882845401c03000b050003100d205d23000f85820016484100143c02 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 5387084 1250 5385834 5385839
    0x305010b03060d050102040806070302030f0f040203072d080c150f030105041d060103050d140319110f031006230a0c02040f09050a03080a020405090c130b1303110a 72
    0x54a4081e60340004041e03d4212802149141c03070790080c0319541198200d0320a0108002c84907605400840c8102c0500200700708980300c01d4140300201070140e50003035158018640c1404146d100c00391142c2990741d050b20310717402400000010381058126410004064001e000c828000d41404070400c0c1064034a40700382d614142040c0955822800706000d100d1050391078015400d8540003c503514030a00247c18195812541d40e413030f00941d030300d00d840c419030701003906042036082c654428401e0b20b214030980015940180a95a00f0000a006142d281c1c5003820040c00900702205100c009548510211011b0000e81402c000c00038124500c00c44c0c1d0380740240040304090300a14100c1090301e651910900b8203002c1c0511034130003d0040c0440415001e159450900e040041c0400000e11081c094081e480d5014643c0b82d09030104107030302c02d6000d6030fa0001c0210001c110540f003401c1c000d00c4043c03103074003006600c030307071690341400180d8080c2c0c0342d8200341031140e05d040c4240000c2c18040e040892040325000b884d5032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 5388334 1250 5387084 5387099
    0x8071805040b041103180c090403080703051801090501020408100e03040909030c0f030206041101030203010501020c060c01020f0307020706030b0a050a0509090708070602010e070504090302120c100203010603020403050d030501 99
    0x5903004450140d601c40600701c40035107654004103407a28002043c0e40d140c1c6012181d50410241c03120b159246841a25404041428440580f6010304d03090b50f6000200c2d9264442a8098100504103030b0406542c140c550003c88020b200395006640300b00d001690303440c80d10480d41d00d01305c211030340002054900181c1b050340ea00000111030444100d0140403078144000d00f020744d00d404100e07001401d4080c140c40880100759001c5802441203104030100d01300403000c64011400c0303000034005c660150340314014a68651a112010f0882904100c00161500044c1d440000c241c3e0020f840001c0541c0c00314038117001d026058004c2811a48058130b07031502c0e19240000190708005544110707401101c806020502c2040c00380241d83c003a281d01021641200c0da10300e4000d00a044c071520320b190b2230041100c00b150034540750180d4041581c1507401442c40c242010408403ca40c4180d030080c805115540040e04e03203110600280d402840140c0380180c0b181d1442c200f103400c0003070441448041600e001c00500154 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 5389584 1250 5388334 5388377
    0x1605060426010605060a030e0105070c020604060309050a05030d0504020306090f06061302160c0906080312040803060604030b010807030605070e010212090109081902041d030d0f06170d0807 83
    0x265104410200d07010075508065004041c91341241d5040900001d442c14040d405801c074400000c0d010300200580c6e81c920000315500c44203180000c0d4400810402045541c0c13081e002440080d0060083d110200a00d5031350520315405610178a60658444040100394601403000a034025007000240c001c0640e060b403d5504c03030400070324680c4a5a040419802284240e505a42c400c103d20320081c0101c014600b0448901c01e034911071003251b5400c1041c0132518140c04420356104505d5804a25942c0e252079440c0113a50300000c09054019000f4480080031481113500305000301000b038054a1b0460450502c1c00c00c3d10070081a4034113210124007000040e0740c7c0003903d0200c4c85000c80318140c640340303040b004a41d0300c030266000c8682480394404610000c3c070030750480c0f09802e02c00c403410800310300500029203041e4440c005132099500180b000d415070091035006001640c0c11070500007880c80d211542c144030f0000d0034031070354500c2c1e01c004a161f400e550060781c0c0c0c50700312107241000c650102000454550300c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 5390834 1250 5389584 5389619
    0xf0a08120c07050607020c030607030204050105090609040212040303050901110702031b040e0d020f0106060e0102070e04060b0405160e04050108030a11100c11010b01050307050d090c090e16050604 86
    0x40d1414440011000710300e034000d0301e2501e6405000d40d0300340d050101c0002d659a41c170050007880390007808042144103009100b00c80480e10182c5a4034100303100c01c010021250007010809401a40070440303606001400c81500f071086200e92400950303810000031300750840700310b048111400c2108100000240c1d800159080e40805911000078110f030f49072000c10003401e0f00c403076608442d105030801900c96540104074500804000c0d070003040160b50381d030310417941040042883d41c0947c0140300144020000140301550150040a001c141000210086012a00f04807081580c8141103080070000641c0034038200c203244000c480500043d410546501e48074441c400e4188203010300b1440b4291205028455131080d10703c011010441910885409800d00c903107407a19058a510f440b804c541c1d1580150207981c082d144542d940350620096001e400000c129180c07003501c101002c1c11001600c40b04500810b4900e00329100a4900125115410092030805810a51007200305120520041400c03442050f513 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 5392084 1250 5390834 5390857
    0x4150501050f091b0406020106030201080c181011030703030f0e060103080405060703020c10020c03070902040b0d020702010c06060b09040e01090f020105130e0408041a07050d050901090e10080f0a08 87
    0xc107502e40105844244400c42081d040384c04c804140007402640641c000030850f8004c4e02c07051450b564140700070003c3d00c03c010001140300400740703821445050004210986182030300303200c4084100c00c0c68541c80d5801840c01100002c0d100d011403466100b15009401c0750010910081c0115419640ca4940f10301550260354020b150128100c800d01d4800c1040c41031086002d4143c0e0b11506829030029199104220b00c54042d10580b140041e803240207100702c900300c0d80805503050420320003040000c040d601c2030100382d0400031114140720104405110f0034008000568400d517543c1041c406020560341c0d9400c803c03095034901141c0e400480d0a5190341354000d5070928081d503940700040980c041540450700702c050301c195950100002c0111b02c0000780140d903001c401c001d038003208031448150f0754410070000912607045070070050425402039010f4803580340c0c141403001500e40ca9140e4028041011500304100003c40c1c40c1c100172101d002d20240500c5510301026003407241d402e40394404d252064855044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 5393334 1250 5392084 5392099
    0x30f030b01050d09061a0907020a030c06110c060415020703020303191b0203070201092c040602040504020f0910020106050603130206040e040b040302010506091303030f02090a030b04150501050f 85
    0x106a1141c411111041010032040103283e1190801d83c5c0245800200ba5564030031524040b035440c90041d024622400042e03008144100c0039076001c491214000104032911a16581c018842468240182207a540280000e155503e4075044c03005d0408015201d82c8045841006041c0c08207601000722540003c1c180d001410026101c0f400c24001d00c0c0440381d1403603010001c41c8074401d80343d001c030040c03c0003130007681c070718141c00d4540c002c050822110b200320400c81800c100e8082442058132036016400307405082c00506003950765000c64244da21580e500c4440410004441d80e00c1e1402c01070140410140c4e100030828a0708000c08548688005003a0b40038000714080c1c854210342d94902201c0180660380b904854a0426180541c50394400342c400314059400c040c005081400c1c6a0390f1036118002009007030b0340403107480c8c606900a0500403540315669400304076428407500d60f0400070009500c100c585641c0b07032509040001800c8407041600b031090b820140104107541d0380c40400d083d5003000b2034803107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 5394584 1250 5393334 5393351
    0x20c03040e011203110c010f0305040f0219050307090605010f1107050301090803010e250e04060b030103050313090603020f090a02070609080c070512061611150a0b010c030f03 77
    0x614602880d80701e18030700101d01001240780c104075052007042c180303c0c1d243c03001c0714403440e40115181c0b1090f600d028001421520011082c2d4030070340040390064002d130501082094243c0101d082d243d500094091f5460540c00100841e00b810013510009080203213041041c2d5090000003072045001400d030b00100110404203200d40a0188844001450000e00030440005030349041d403480c2d00b0921032000d2090340d0038002541018450040620941070402d15a07a4881c00d0100703556803944808250740085e030f200000b0820714031a400943c0a10300610007507440d4040381c0034214002c000350b0800801b40c2d061030010001a140c4d240c1d006403041080b10b40344900c0d51000b2802000307004090019241605000030403041c484218028602001708405803903616413101e050001010380007030300040c2940a000080c12900c549030ba417041c1071410346800c2d24028808426146050580807116814031084418405400341900c030b495604002800e0002c01c446003920054110415501007030145500c0d260341c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 5395691 1107 5394584 5394607
    0x70507050103051f080105090105010609030519030509060a090303031505011e0203041205010c030b011103120c09040e0102031506040308041406090402040905060f040e070902 77
    0x10455245032800440080400038020b010002540304000460030540301c20300b000300b4480d4008101d03070610981340d03400c4600603401102849400c8104100007040460328403001c4501c4045d07001d00038080e05090300c2070311510b080e0580c48203000800c2580150000d01d40c20070349010303540c00c1200304c001e0300044518254900078680411440040e0380c501456090380010980b100d44107a0742042e83c2e0f1082c040c54040c01d03440403030381c41e5140c8117840d01d059030511031780704110402d2a09104000760307040000d450b0320490000038041140d41c0300180440800b50200d40c0d502c85e001d0720130410841c1c039240c201d00035001a1014010b01d034080b00010400d00c1e02c80281d03026207801c6440c0700d180510705082865224251944c0c6130308580d0501c0302100c50f517500c0c406003008081035100400c00e846e0500412105200c000c4805100d6440c054030b1903d05000001ca0400380c0700550070059403854038401 = true := by decide +kernel

theorem cover : BRFrame.Cov 5215834 5395691 := by
  have h0 := BRFrame.cov_init 5215834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5215834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 5215834 ≤ n) (h2 : n < 5395691) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
