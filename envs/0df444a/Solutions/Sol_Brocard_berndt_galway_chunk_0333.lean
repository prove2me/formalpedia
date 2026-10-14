-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0333
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:16:10.465935+00:00
-- url     : https://prove2.me/submissions/d5e95712-9838-4275-a756-d6e19dee3539

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 59712233 ≤ n < 59892089 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 59713483 1250 59712233 59712239
    0x30601080a0c05040506040e10150f031707031709071703180609010302090402070803040501110304080d021303020d0b0703060b040f050904050304030b191b02060703051510020c0307 80
    0x100064001d06150081105403042d0320300b40400024140080503a500301d9216004041006002c11414020214044021840c07410b0500c0038019400a644071240b400d100340010004640d00e00340112041c0c182c09227103640c0e150141000e880d072400c0c450b04c80b0b8820000b801081512800800c199058800071100c0398a400b80208016503a030080b07507041025003402180c45140c41c075125000740080302044c100541000c04400000303049800c0b08005480c0c082d000410001000300070b02c6951090214181041e0071410300b07032901000b40c016841c4000259500058015203c00c40c03072950304c01954000d0569150030341504d003101c06241c2c02d0b664400460b0500e1400b04484d0503100540342610b0140d003182c00d01910740710401100c0280984165041e01003000044003044140721114402c4240084005403120180d80e507104440c0d54641020106142d50320020300c0b51b501040003500200a80783c0402d803601e80c4280c1590b1508040d50481d40308401891a84416402180c600880320084095440d91a6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 59714733 1250 59713483 59713499
    0x30703020403060b01081e091e0c13050c07060b0604030c0801090b06030d02030715020d0e2505010909090606080f0f0105011703040303051b030f040302130608190215070b06030601 79
    0x12091311046019007c0155012180c0c0303803440a16400088001240c004002840050140306001d803c800200d801c901c4020845d807d02060007140441c12003010415850996030300c1101d4040c0d00c100400894407a05015603d40e0360340c041d02c0185401c008800b421542c1d03050701c0d500030406102d0848140b154000052503914000c151144011055000345281c00d810350307121035003072030021100440203900344800017084007140304603000116044002c15044521080d014280401c1100b8030200500300a000c2c440c59030310480c1441180c3c04660042500c0d2228038102014120076000145a403051600ca456400c2c00040c5074a913032640361300201f1550f40c840255021000c1c1c101007100306548100030420010744140010003032020701040711010350070350001003400c65021441c50f1900032408901030055250110143d488040b41510400c1201c1c60044026210b00c44402c03070540451100180030259200c0b10680071006484984041c0c1c1c0e00d4032484e280c0c00c0f1503820344403540a44592800421202 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 59715983 1250 59714733 59714747
    0x3051807051309020303070c120b09030c0c211510080105041a100f1d070503060307140102030f0c06010806071103070b1005060a02010b011101090b151203030703020403060b01 77
    0x207000075203486900b51034484104060403c1d03440898062008100400100e0302c031107a0755001c1c101901859020120300d0420b00350f10200a0300440c1c41e0307001008964188000000c6d101044d5100b662030000c60001d440d10911132035042c42604000f40111000d030300700211000e01852140c07412410300c101168a4211450880742c0403140109041c200d08003803544e0213a480011607111000c07078843c040a584505000031106241d50000b11590820301d0880d401440d04021160b01c82018606903040d480c00303e00296070b84107039115403580403040340e1148240382d20900481d07001c017048243d880c1d65684c00c0140590307900002d100307507004c41c0500c1011a0901d88a0020303142e401d84e0f520002c505201d02c1e511060402180a801400a2464a40300180f95103e000151514100a400003c1c920340f0f110005045031010304907113140c0342d1514410f01c00280010464641080f070076040f243d804000c040c04034230181d945210140c3c552101000b00b080c5d25906400a00070b5074400c030018801690140010f45080e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 59717233 1250 59715983 59715989
    0xc021908030301260a0501050403030501170c10020f070b04030b0a050709090b0f1203030a050c0a09030305090d050109080301080705040207021509030c100c0323030c0310050405010603051807 84
    0x25401c1000108000c102480c02c0e04030b80c00c1640c0c4003241c0c15012a10385460407050400466443c1d444004001c24142c051048500410a980805248503104542c0c99110b042980c881e42c0f0a001004852824601c2040340385000140c11007203900d015121030510301250424401242c4441e400c100050b200d80a50184501609441d00d9518100d401d084428000d4a0302181c9a40c010b0501d04c1c0340c0d0301650700e0308046150401d943c4040c55887c00c003113000c1000d030b030401071405c1060f0030200450a02203903c804003d003107c0c2c040c0b400644400c040c80019281c5001404068160740c201001c0701d042c0710789440114103d0300c48400322401c03242d444060000340d015401010b9800030011050b02480d4031010b00807e04185c0c020b040e104085000c2000880c0181105070240c00180c1100c13100b4201a0000e07c0d41c01001c0610010398102d2a028a25041d1840018407000b00c2070f201201180d4202100c1c51a00081e2100030814425986c407410020700408040700e040d40c90444144c204c14001c10040f8034003040e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 59718483 1250 59717233 59717249
    0x405070c052a2116080d0806031e0f070f0f0602010e0c0d060f14060f04050903041401050705030a053a180f05010c0807021605010f140a0c0219 63
    0xc41c022550400c5800c2c078180b81240c03061410302000e502c256000784010001c0440300346805a0617802c1c50755880c42d2004059604003030002d404c05001d02079030000742c04010410b00d506440c42c0d07050b0300c1c0003480c184a50b09280f90510320030150007055006680e2511002e542503544101c0d461075580780102c0c280e814000360311a4030b8004007800c00d12030801000ea5030400e40682000f040310b41d00c2e1505802111400c0c1908400442c42c03400703006461400c0b2500600081d8110b40600050914101d4180c80344940d00c5942c1591103400f9800341c076640a24180d50200c1e4001087c0d03a200c1950704000b4041c0d601081c0402c4500840c80c3d01c1d41050380580383da4207241c1103420300115070004d402c82490001c10785212141805003e51f0031260000b01d155141018041c454000892104080705000d8118440500074100b07640100c02d000d065550342102c1102120000d1905078001d0125200030748080304802b0382c03000740040010301c00f20f41941098280905a00c20749520003108101c2034081403295042c005c00d90 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 59719733 1250 59718483 59718553
    0x7060e070303050d0c050c0a061b02160902160206030c0904060b0c030d0b030f0106090603110a030506042009040302060402090604021305060c100e060a050f0412050c0c0405070c05 79
    0x80061510391001e1072480140c1400c0389007e50603203c451901c0c0d60500216203098840c5003402c4040d400314203203800590b807030000b450203c1007039002d078503400024040c91341c42503404180042c03c0318013034810801441d0094a020343d0790500b21a03200e0560f2001400500031070a011002400459501c115102181580003460600d1760200c40344000d0a07040000320b078140324803001c024011340e0a208441c010881e10400190076460361030000791100302445150320411400c02c0400110b14007046255100780c3c4024030701400c1c1c0348071400103034462034070001c140c00c000e0a80402080540000f09280254021202c0d082c40c0d507a19000c0005900ca130410300b040000e074008082019040c041d0242030010b0703814040c0c0303000c20040d900301001c40307aa50342c0c00803040d27012805000407030002e44906070700900f400c01340120a00c2c268980d451002c00400050081200005030a107a004003408040c04d414001441481642464040186103803894a410b60302400307030b09156400c102c0c8180b52100c0140b6640c160781 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 59720983 1250 59719733 59719747
    0x50306010b030601050a03060b2a03160305070c0b04030b1801050c1e040e0a020415020a020f010804020402130305010b01020c0102030313030507030c050d0306061b030804060b0a08030c0307060e07030305 89
    0x54082e00180258414143c44e898003027100c204c510007030505e0340c00c000b41f10005c503802c01d80304e505984800d02003440d043e0410060a900c0c18061140c12801c140c00d400c1039940e40c919071420701c07044106035010b90800c41001c03501208110005460074002c00e445560182c421403100c8100e4200d580940c0d54400c080c80400c0501c05412034007190100c54032031494038608190703841401c1144030100b115110300caa03500040a01c916181e0b403101591044a51004108124880e40880e05a940070490035041c0100349000800b1944e039078048507180c5145a00c44101a41d036407910901a003c048021400341c0280b400324900e0f0351001080d03a201e190000040c2d00314840541302580c0c42e03448108141c5c10003064402000104004206c0c12441004540d40010500c1c0303000c800420b0f00c00d07490308000f244040c070280040441d80c445005c5822a07080b0100160000741f50001070389400c0a03500c07a078028000800c0d034240012002c80a01800c034001e00c41408200c034040007903901e54855000c01004100c0910003d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 59722233 1250 59720983 59720987
    0x5010e060904150914100e030408060f060f1804020a05041109040e010e03030112050c01050307050d0c02030c0a0606090509070503070308372010090203071d0f01050306010b030601 79
    0x200d400742c460b003180010007070b01c0c41d2a0750000004a24a0720025444005a031b00d1030311091144803040341124003c0c50400d8204501d0035200d10780a0081055a03c01e0000700c2c2040da11500985002c0100420f81e001d001e4000c1c01c0d4102903001164103901c41c1b41c0a550004240c1418000c800c52040002c940034504000b54003004024004400410b840e9980d5840c0c06403a120108000c0d0302030084d04180c101800c403d40340842c946106003400c0740c100303c0140288010b9540103019214000c600c0742011405102c50a802c82c03550282040c600e01501c50003444005106690f480311003aa03071201c0b014403441c0d503032001d92540d80911b44076964040c0d115070010000304901c440a400c080c038090607504c8958101e04003038500052480d9003807282c0001601241540d541248841c08500c421b48580ca06114000861503254468051040c10a03921a000c07101199420301200026020401c5101c540f132803844441036400c0c03002c03201d10054216401c0041200c0c03400068140c12200b10500081c695502c0b6001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 59723483 1250 59722233 59722253
    0x402070809060c0a0605070201110301050d02030a0b0a060509060a030809060d0605040f02030702100903021209040f05090307140a0f020111011b0806031504020a05010c0503040f0b0d05010e060904 86
    0x10684203000244000310301d6960703410040c0800c07105040104442440c45c2000c0088510142c0010190781c94401070403010040369042d41d045a0088607201000701403070021074200000d004000782007a050008010b08001d43c4c0d445042911425266040d00341e40d440c003800903405d00ca010241c22401c06210404c071a18040b0010004100c00030804103045640d80045401d5030a44035046048036004000c001c80d696042001d130211307401d001c8090203c1700e140d403406901c030380071802c5c0c041c4c50340b50004a58449844980001e0000807840b10100840e203444150642c90380c00a01c001c8600100d0647d460804400004101e0301140d041600c43d45565040d80c010b40e004401c01188203501d540315546010701d1184c4c0d031180384141a0548070a2824a010700800d03041110b12000b0700004104035090001507195804c1d4001034480a00304810341d100c090a100d49035000fa98413030b00d04a140184080750860910300501003024804800381301d00d9894a00078000c5420458007550881c00001c0002c02007201100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 59724733 1250 59723483 59723497
    0x6070201061a0403121e08060418020d031101091e05060c0c0304330c060605030a08040314030415090501090609081906060b0a110c10020a060c21050a050a06140402 72
    0x2c00102100088100c421a01b00300408100403480d02020041c4600340340c060022441c0180414840051305c2d5030000e0115000c466014040010000250394521001d5000301c4000b6042000c00781400300c4402c03649001102034004030380d80d02401003c5a200c1c0c61400c2512080d00d48d03040550308103401c0424400c520320300e40c9480e146c6000c000142d50020b040e08804103001400968690415088608000b81558030650000c1d0003548001104804038682030b0503107050f2640038080c4050b1414000180b46180207642100404110754840b40034000d4209080300103d40003030300e07110902960345509603103101c0c0d68881d0344c840307821980b00b8026101c1c0030781038030501a01c42c46000070a541c4890b0380da007164001c20000302c0480d259104004218000b00004202014200e079240208017088400030349480c9006030007000c547d15582c003040554010b107940491013100c0040b500c034507051620100c0251005a414494041c40c1c00003182440308203004a405841c40d18461002e242c24420a002c0254090b107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 59725983 1250 59724733 59724737
    0x140f0d060c0e0603040803091b1c0204060306050117060a0c1704060617030a031109010e13020409020a08070f020c1c0305040905090102040f080606090a020c0f0f06070201061a040312 80
    0x8503890001c3d40c4450103180181e000302c40c920707241d29202080c0392030585003440d5402281c01082003004036594a8000d807403000f0380c5180d00d00300d080d2a480800c0240519410040c006c42c00c0400108045441c15030b0003203051050000c448250300c034034054508075448254482c000a4540c0c00032030092120640b5190014412040041e00c00e0b540c10f10000643c0d80c1d1501380301280c00c00903100c0c0300075034140240070a58210040031841d0050910003e001c041c4605421030045030501000e003207403000d9034107984c010001c030381e410f42d910014001d0007040d0f080d088841901099403465510030461001030156010b603405810707504030082840f03000c1c02d050b14401040301013003020040800c520400d030050718090f02114002503261070410401240040c502d401101c800e07071061302040040e6950180994100d5217080c0016500c40108201d18248542c0001d0000d0502c500600d021503c1400240c05102d1641d6600030007550b9141d6000c1308001d40e444101b42d5410720244020f00110b40c00100513680ca410314 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 59727233 1250 59725983 59725997
    0x1140403020f040c0e04061403070e0f070c03090306020c0304091407080f060a05030a0b040204241e030602031503010b0609090f0601180602010c02060f070512040606050a090501140f0d060c 83
    0x41c002030b05580d01f0381c001074021030b128102007a46050030040c12001c1c0074207030002030385803401c0d05440c1f130440303001040755081141000d0207900380340c010006107010707523040f2500395511110b0b0001203542e40d00038402c6c0d030021864200381c0c0ba0004602801140122010799807145c10b500d84800c0c404800c00050081c640c449a8024001540c1d90200300c0409058411070049175249030a004000454429101c1204907013012802c500c2e01c2d9015125590940d05800f042c00065451a18107014601d07540d0001044507100006000c900c001a030700e0848011401c600030b10003a0707008010300c455070081604a58004000f00081807000c01602e4450ba48442d0600d02000341c41c50000441e1040b810030f901010150355615a0b1101040d4140810b03031f48030110180c007000742c3c18485001840c0d44641c115952242c4540c401050402929402c5000201001808004203a458400070700040c20288180100e000e40b560401d4414100f03620a801c030f074180101400305210729030303e542c0050090021032204000c14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 59728483 1250 59727233 59727257
    0x120e040b0604091e02040302100807020a0b0901050405100209100e0d0609030f0210060b0304060f06051207050a050306071b03030b0301020313020415032f060a020c01140403020f040c 80
    0x8141c050002842c11040101d281c0c0c651030b00859155a510003540083c500410051000d61508404012103c1003440c01c0107c40c0d480c031808904001c0c5500d001426070320101e0038080c044205400c01d80c0114041d40a03a80308440f005419000c0f40f082090381e50f0800c140540c80982d0328084c0e40284041c240140000304050a0382e030f02e840071039031002070071000300d28406004010190704101440244101201c10070440f0f052241541d00e5000c028070080809440707640304c200504660700043c00400c40034044850580d90030140584815180c01050302880724a4400a0303d4a00003071107a000d45400e031900e03048054ac1008024859610000607001e164039404002480d4800344001c1d84500c00000c18000f4130382e041e20421050b2007070015070002c00d40030a0001c0c00030540501c60707148000528001007102c29100740c201c20a20000c40c4031241c0c4a13101003a403400d07130740d00400e000000403c00d03651440b448800391844540d83c01503000194008024070181b0311541031903802500e0201d014108560403401d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 59729733 1250 59728483 59728489
    0x27030803040507210b0c07060e0a0507090f02040509040f1a0a0f0b0906090f10051201051b0a0e0103020d020d02160b0c0703021005070c140303060112020403120e040b 73
    0x20041d10300701d40035800401d042050011a4200c8010401c2400c02c62044107643d0319005c43ea64401342110070076142c0042d845082044580c0f2030300c5035504c044103650b048030302800c049480e20000c1c807680903c0303414038804500b0003001e4800ca85c16150002c000c903845490710b1f101d02041420310982221840d40305601704081c003184112452080c19141130100d001d10009030400d00703450307400120a02405103201880001c0d81e0b090700781544064a00c03c0c80c02c4550b140e00f80306914116540c84144c0004400030704a6000c1d43c1900901d11521a205002a090f0f520307501c90103091040469020000c1d4241d2a20350072584260020295400c0d81c102c05402c281d200107141c412648803a41c00500c41240c02c0c4c196042250520b0810f50002401f9146403d2400a072006515200146c2e228108282d80f02c000540c03460240c41680300d01600a20301030621201592400e6495100b590b0f994041502d03051500700c1c1b81180d00845043e6640480b5044d8120b050140542c1c648120071041c070f44c40750701d40f403c0c803071151 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 59730983 1250 59729733 59729737
    0x10e181320420403021008010602300c0604020f0d030f05030a060504020d0903080c0f04030602070203100903050c1501060c24020f04050a050604080c01110f0607030506030c01080106270308 83
    0xa0401480290f9841c40d40c810400c2e1003000102c00018410002c004120054004c10010812492001300804024070694080103001035a6020707040c0d840003140c1d010a00c040020603600c0340d8801d9440b15014906036080149403c10841d000700041c02400003c2040303803180001c4c0d030f040b4000b20000305070161904002001da8101d0041142c0171507036048180103240d44858095000b1500b42403052034800c0e40c0201c00168459408050501078000401008640341001183d01011040f0300400c0400442d14008055602c038000f420020704c102100011208480214141241e41a480d40344a5060650b100d02d031041ca4294107814000aa060008109840340000d1402203050411f031603950742844104440441260044c40c0104c40502c03040c460301500017081c80310381800f4203000030b01002080140d45400101c50000266020321014880d92603015040540aa0421010745820000311001110a11001d1107481c00041c50682d00b6041c1c030b600070540c16090204407500003100f41c2c60341c55054170340d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 59732233 1250 59730983 59731099
    0xc120c05032d0703021e01080f24060f0d1d062403150a021309020309030d0b131e0e0d090303030510030b04050705010201051b09010e181320 62
    0x83d0301b011401d1004d5685c025503403680411000d207140b40b1824a680110a0b4401503400d521080b504200401c0003076484100b520201121342412540c2e5049000c0c9040191040c1180a000d0240700143d10f4241000416050311940400407031075503410302030034a503400844007074a194241c099201d40f903030441041c18696104401c031140150b60b50010401003c84c105076640302d00400e0384140f0a0000c2a0804000c59000400b03e00d400300e1071000300070002e1501d00c0d8480c10075107403c2c07602a01500c8404c44100d044100f0303104003000c00200940c40c049585600c1c10340290400224190710520010740a07500a68020046c0d240f0651020b0f12a650031504d04416142a180d59020300c1c010011581c1c24014180d10000c01003428160b110340d07901000c080d00490607040e051142d075013104c004a86503c1903444184a50901c600107504049c2504041c1d00c000a10075161950080050309421440080f24204600c028105d04045a1a9031916a0108140145038100340112011020400c0041004a41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 59733483 1250 59732233 59732269
    0xa0f0213060b1209100605030c04020c030c0703150b040501030b0a1505040915060f03050604140c0d0b0901050601030e10111201060206011d0f0609130c120c05032d070302 75
    0x904142a605203050b844800c9015aa1b05207841449117403000b1400c044010001d036000350301c510841109505502940c0c03580c820500c540c1c0c00c00010f011090b4411240d00c80580c03000c004411002e02440103450b024000580140041000b0585210b0568000031081000c0200c80910940b25070000d001d03210094025030f0341e6003000301a041c0e59a1a4032400005190100c4c5a100c540d2a44da107982d02d034a0000e101a081c03404040100c403c4540c00e01c00d54861001c0240590a40c1110b0700d492010740d8000d440c800440e620f014002041540603106100f008030415005021710300300c0002c010080e00300340403070a603041410b0115005650303000d100c083c081c1400350040c00039507040c40d102075803042039541c080304070a01042c24000a04491040586c1114040d6130f42100caa45802e8122a016020107005005503a034000000740060045003114006101e2400c40c801a40d8400030542c1e070b040e004001c0482c07001c0f40703485030003104d04080409010a81000a503099140d907031b0009401012031004000f5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 59734733 1250 59733483 59733517
    0x90c0f0503060109050103110907030605030303040f030f02060103020120030d090602280503040b040503130e07022116020d051204031205160809030a060204180c020a0f0213060b 78
    0x881031600b40302290141c038880100704400c0d13165490703007040500e540140e1405104d8800101f0361881c407942055018140180499640341010b03d4a041c0e07461341c0410a034000b802402904d407100d840419154120f0341c05a540303a084010090303011003811024036088000e8402040003038102211806a21107143c0210030040c1c961045020301e90141c154407031540c004407440050110b59175000710a0340d421517080303840c0c500306a42d5071420f146940b28101c1031151030260204001000c442c98001c7e18070825141c0d0a554002e400a101c0200305080c885004020410a00c0560300c03412140200504082c0014407440001c0c4c025103520f400c124244c1003260036100c0c0010b09000b403204030032204000038240d2030170f01d1030002203809900310340c940554000e00c4100b0004002c0d2150344c041001040c03071500040110f6803035640341c05c03841c400300b0621000102c00341440c2808603401d00220f814040340c0c0c1c00c00102d40e00c41c0070590811540300d1100101031030a580e80c0d00042520003074a0090030140031000b150303072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 59735983 1250 59734733 59734739
    0x901120b0906010308070f0807140a0c06110307120c15050709050109030503090909030f0a0c0b060301050115210507020a0c05030c0d060902030109020d1209060219030f03090c0f 78
    0x40654400105404a5a0300c1800100005205202201d440f15040b481c01f030400704d03651400d80c000303108164019102880d0020b2100703000e80c0c04203400304050310500b940f0198a6480000751501042c0c0565101190810701c0184003040760f2640f0110407001500e01030400b000660355643c020390002c4099101c183c0d550003000405034000303072010003524090801026092441e5140b5036240300e00d0001d00c0c000c080890218518001c200280d0342005000988152a4100c0c040000c2c4100c04206040c0c1d18080d40300b000c11040e05040c8180b40c140e0314031040c1c0d040280c0f0144c5d030564100c808001b03201200448035244480c140b15500c030709809200c56601030880385071130f401c04000010b102e4109034032941160030340e0034442e43c0701c00051055662265002c00c0158260000900600d19203401035040b00807030b92160f080103c10700d078500801089450f04003013a51504800c0f6502c4c815407030034103001d0940780f5a81010030f0051480611703081d194523000c9010010360780c0b654500c1700640c1c4424484160f400b018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 59737233 1250 59735983 59735993
    0x509011d0a110706020a0c0c08010c02100504030e121c170703111903090f03020c0102101a060c1011090120030d0504020604150e011e0e090a0b090112 66
    0x1180c0c0100400d1014410202c07800303206803180c428040c00910070355000a48581d09400b44403044a8190040e000e0070b106560343d01ca4030301038216031565000501a01b00c100d00c0e2120b2612949028039010f03610003120210442c28002c8592a151461590340b043c3c04104442c1c00d0344000e94120030156603141030348051112003ea107003c0c0007a051005050078001341c0d1000c08051406d80311309405c0000d0307941c0c46503410796090740142120f4030050f02102ca04585d0509140d0000340d1141940020781c00c079540c036140314120004440d01103030303070032500408052080d0403490600080c1c042e03007498100f81c034030000b415070005044905019607905483d0010489440c2580c00495000c0080700004082d00c11466402c821522032058015800c11141e544d004a020b45d01d03104140e902500910300000b201504404020b040c603c00240310342d0002d466043c1454514480c25503103001255140c5500500102080030442000b4006004a2043d13503210350300c102c1c40d560144103900820011050b240e446200b801c103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 59738483 1250 59737233 59737289
    0x12020a021c02130506060d0f05040506010b1314120d0801140303040e0a09050f0303070324030803070e03010221010801150614090a0909060b030d0f0f18050901 70
    0x6509001c0070031282100540c40e0384000c0050500d100c00f00007142d0303031008009203150240d2005512000c4c5059119415401a588818004d0740228201c2d00e250382c2c0d84440684a00c9585031040490b8400b030402c009203d02d10a5490130136000800030320581d100c030700ca0103241c14602c4046500082c04c4100411012001d614000015101a8007661a090410748903d107880c901501050056070303030700010402c1c01001d12800b0074074069038082ea556800c0c0071000402030400250001c050340c0668800700c3d20f0220042d10f80046a521507081e9042d40d42d100d80595010500800251701950200f20444001c0032244545010740d00c04128030300154102400c0508440700c80c540f900161030071400a1003940e0b0070490504402c100030807001e41d1421f16101080c0c1c5d4128070740c04001c049040c010504100300340c03a00a031003040015001c690001d41c6102040350b01450340d949074004240e805010640c1c045c41070703170b2980008021b4820618410342c4c920100b1b1041c80241c0c0089012031401d10038040d054030001d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 59739733 1250 59738483 59738509
    0x10030b0c0d061401022a040c12050106020304030f020127080a150501080601150201140a05072318060405060a0327050607080411120319080c040b0a050712020a02 71
    0x1c480503d0749040c2c0003035540c2445a42c0c1094002c1c08070b14003491105a004180344400c0007610074020b4145202004d00032040440440c807501d82818004038141e88000299801c83e41c002e83c83d001142000d40056450543c106220189400134000801032210750303c28103001401c45000074800034100d070514000700b21503c181c440b1300a00344401008500d02c00246141550700e18216901e510100a800381d00404142005040e498513070800c0181008c15503005071300c01d02043d00d5080d07003009182d8118102800300c4450f10a01c003418000701030301d04080c0e54404540500034003910f1810351544001340c1d07503411943c80b03c40066120545041c000810104011540303642c045510010f80107652500e03180c4000a18010400003040002000c0c4040a00f141404807006000d40701c400a40d110003640b00e500072030070b91840c20755140d00d0102140c424840c8501c41e8001d0003d140c1000e007400d0300d0344e4003548400c201d4020000d00388a4003011400701200d42200185c95001000500800d00c1401a6071030340407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 59740983 1250 59739733 59739749
    0xd061403120405090402040b060d0501140108070309050601151103070b180d020303070e04020403141c230a0507020a0611060a02030c030621030403050604051203011d10030b0c0d06 79
    0xb00007007142d9180d164440f60803d17030440d0045140c000c4074011520354025151443c0b0f103c0e0a03c0c000051010f04103030080301c2c0c40e0003070766411000d644d1100280c4c25100d05040050090f80480010070815481d28101103e805103498a011480740782c02c2c40314559081140305481940e1002c00340030a41c5585890034410340110300143c8028140400d019449010080003e02030044090000b003043da5582d0443d80a1a48203800c0c02c842ca1494101d01d560300100c01032001109040e4840041c0fa500542801c0c801c000342900ba422140300440006d038050b0024060642805800c7c00503a00599842c0d00d03803005070000e6500c0e000e00d00034030000c2c01d1615030b024000d0145c5130307c10001d00c000f08107a00c0860f680403c040c0c54010400c011903a00c3c03401d09540ea038460340d035030001040201c01c07c6400300d0498045c50041e03040303c0601c500703901c100115100138400da9034502c150312411800181c00f81080c5920254500ca1307002c0c61566a03c603070f0041c0c50125400d000c002030024a501304c810103440f03190052b280003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 59742233 1250 59740983 59740987
    0x120e07080106081f0203151002010f0b010302090a06052107050c070906140910080d05090901080601060206040f080d1b0813021309020420070b01060f051803030d06140312 75
    0x200c04d01c444c0020a2040d0780d5154000000a498034121401040c1510019201c00783c00c0301c001800078020b284100440c0030b00b60420790817030925072080c003c0c3e4940160007003071070074610718169050340c0310740c4500001c1d0000a403108034840c03002da901d290369215800303030344885d5079603110803010714204210f031f0700944042d9141101c180301c8020007100440240e00f069400190980b00d44003a0a919442940104110300c100d070f011442c043d03407040180000f11016140000c0c141d0301c40f0710042d11a0310034058000107a1080d400980854080500d1428a45c0204080e520304000b420180c410340b02c0a5105400151a0703944040341540d002c191694402c15004003029002201d90000310940084501c00707000d940c81724a40c40a40d942c5038000c41c01104110400c000000b182010342ca4203421840043d03440c11401c82c0000744180c040d8003a00000300d015a221803804202e2003005c41030409181d8100e4042c4014032801d1031309103252240070003601854100700c08102190080519000d10b600d003200d0080c02c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 59743483 1250 59742233 59742253
    0x1090c06030203010b031303180305010f06050306010315110d1401030b090114041202240a060605250f14010e06070302040501090509060102030708070b0703050a0e03120601120e0708010608 83
    0x41c0d000e50360000a6484181303221801408d0865015000d1491403100b401002c5001040000550044160f0101c2a2090106036541c078101074076941c003403002621044a50b950300341c4039a100e500c0f02c189001100c038200d052401d001c0300c02d0111114031007817410001c100c1c40144184800a00400e41c0314140500900485d0303c3e5800c609080d81e0b0140000704010a14204498018024004034028000307420640540c2010356490002285007995080e05443c80c01501144061040c4112900c081e10304e0703090455800d004011000804201c2d01c142d60b200101c951080014014400745804068141e0020a0034a1240f0140c0c0c00e040d0007501c01000e05204010810481e600014548115101292280c007244c0e2504010303403c44c810180002c107a01d00002d024010003404e4401203003e120169410010f41c1c3c0d404c80154100d480241c8086180d46c018040c50036072500d801c050a50007401807500d00c2804160a02000c295100c2003000c1115402c070100c00d210f0303a5024030442c1e0007000e04e44003c0540f618 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 59744733 1250 59743483 59743499
    0x603070215040201231e0a09030b100513020304111002120d1401080a031805130207050c040c0e03060f0c0703110c0607060b01020115080304050d02031e01090c0603020301 75
    0x62089212450042007000040c2035a00511000008404403002160021003d0030814500d501094134401c0b0300c005040e48851510380c000030342c1c0e9005681d4941c5040c00c2e045403140c101d079140080107503170382d003a1400020070a911000484141941d0203980036841c0d042034506901007203a255652800359075400c0884d030103c7da0000b150000c2c1000c01e1040340c5d50304001c9405102400111404544c00605503000103a0a20000f036005002d0b030081d6103410041c60303524049410b0307400c54402c907030740003030000810a403100c4150b0040400310300c582c040710f80c4070b02c1640102d030546000c10b03440c0300402c6424a40c10131b1820140b0515500506496000341c0328540020070005500401c0340103070400420030504030900808002840b1045802800c5607120015454075201138490100c0043c015400c0c82d064034600140380c00450241e07101c100c0035504080c04c001c01c0c4250003030510b5060742d0512885d0314140c81c0c40f407a0743ca828a8040c00d440084ae42c0078103030070a0b1300c001c02c01c3d0f40400c0401d8410001001595 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 59745983 1250 59744733 59744743
    0x30e031501150905031b0a0902030108100c030e060106081803071703070207030c0e0109180c03150f090c03030201050619150507050f0c0301150b0f0d110a080403030b06030702 77
    0x44404041a40b4041e01003001c03a42022160410b41e054440c00c2c0701241600b0705206407102d094811204c50000d42d850b400e10394140d000038454641c8176030002c214003240d1425500480c0c038069141c60000359035035002d50b0035841c0101c20ba02c070307001040c0b80000340582e1582c481110750b20741e0801801945410380d25510500041c41d00c4522a585074808070101e00a40d200707005840c01103401140f00d2504941320304114100303400c00c0c8605060189004030020b1580410980300b441250881803c2c60aa891a1102103040d0100801410785550312854101404024412206018010902c4c038130361078110300e4044d0840b01d0240902e44148095900e007c000d0212003c0241510008405241080c0714100107651074054050010004c1c054542a401400c80000e0000003010003200248441140d141005034a02c080e402074484041c4100300302c2c0e0550202000400268490030000168850100760360042d5800c86100c600c0007aa40105001c1815418002e40140c00411500345142d41072003100030350b8035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 59747233 1250 59745983 59745989
    0x19030b0120060613060503070e09010c1d04090c0f03080408120333060703020609010b0105041203050309030f07122607030902030a050304080106080f07030515040f020607060603030e031501 83
    0x440240e44e100100100750340000c0000c00000c0d00f10307501d0301d48a0007a03a001c203408584402c3c456180c0700c601c0d441c1a10940000200c218080c40c00ca911156030b8090102030806c507941503480c603181c4d09000444c000c0b9058800001e5010307000060b111030905100728140803200301e081008034400c0c81807000c41e070b200d11007280015030055820440c81c41c4d4402d104058a07044800b071a1b0144011418400f855000b007900ea1151400b80000c21003070444100550f00740c0281e005d40d5540c900000c0002d800a809070340110340201c1504112401d114104081080e1648003900898822131201c3c500103815400040803505111510041100100c03001200300e1100e00c014200e904054407100d4400964805101c403069164021094a5890b500c4030301d054080d184038418407405100301c509417140e005001c2400e02c140c036400400740203210740340130000c4400c10010304280c4520312500080001a550100100101441003002151951540c200500030350089085280250004484907413180e41c881000d03415 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 59748483 1250 59747233 59747239
    0x100507080606070606080106090b03160803030601180e0112050615010c0f080909010308040f0602160501030b030f0607030b120c090703180b10030b16021203070519030b01200606 78
    0x2100c3c258207010025121550101c0740c80e510305240481c1c4403030180c00001d8169800e034201c6240100c15070380c4410820b4944903250032604180b0115011703601c2290701e06003180024607045a201e4440000302c050940c01c3e4808001001e0780c558020401c0b0042c00707815841414918414400c22540001808031f04004400030500100302c942c50b0100b043c81d40c1030340c0b4076203000346c078800700c56843c0e24003144513600501413000d0001ca5000b0004c1c3c128030010360480890b070100240e1040a1900c00154040c0024a00060b41406032100c3d51050040800503075110300e03501d54020500c1c1d130800b0280500c1c500b4640301c240a03600701c0c84c81406507442c1c0c130b4441c94001d04945000101b41d101d842280d07400c0d0410000003000070b10a00103000001008180383c60035030740902040c03442e40e140c0022030040ca50358440a040540c201000d650410000440030b59480704843c00d080f868002c0703200d03588815210f441c96010100c1d950316601281542e001c004600c2071030740c454002085904400040e03959030401031400748 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 59749733 1250 59748483 59748487
    0x8060d0303020c16050102060606130b03091c02010b040606050c0d080903090316050a0504151505090402030106030c020601051207050d0602090a08150f040f0f020d0b07050c100507080606 82
    0x1041500c690b044403c00b100710400e40f803403602010040c510728001485624014170468002c55aa450074204032105907020001a40e44076207803010245081c1c000410041e824000c9041c8480f0040d02c9800e0424524030540c000074148001c0c1042004a42c1160080300070494180202000900c000402d441c2168003410413018a640316641140740d841004034003501401404100041c443c1c01c4c10381402515000c81e41d00301407d498205201c21a507100307180b41c450f07212910041000d140d064241b1110341c8207602e0f1191a0008450200c0d05991003030342b02400080e80d030940094040d034188440c5d40500001c81d44140c81c92a5002c12554400c881d000e9107102d48016055001040a254101c504008000d012a03401c0c07542d907900e280c0c0b900d00c030501d07440c0c01100030400a6008800d088116100e6a485114802c0c03034030841e150302d003039040b1490042b6000111462014081010070ba203013441500540da8442d6101c2001d5559400c05e4180b00d0030741c00319820141840701c07094010807016072021040e54410313 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 59750983 1250 59749733 59749759
    0x60501091a0d0203120a02030d06090c05070201080415092904020609040b0d0c030302010b010f02010b030d030203070e0a15110c0d12050f03010803040f05030c0d02010e030a06020d0906060f03030806 87
    0x10f420100065001c0000c83c50000d0702100c121f80100c054003c0c3c403411202044442d588200d41001d0311102d090100c0001c900308403080041d07008100c0160010300540300d071103008a00c80c05140455000340c000b501e0100d441b41c00802030560203031200c43c944985000403681401c10303502044c2980141c84080b031040c3d0f1241031103007490321103460b02600369400101d507011540c0d0301e0802a0003440128580b6001901d0383d82c150454500501500c2101c20b806002001d00f1a0710201c210f0003500094404001c1000c1d0360001d00c029a00c1c0c0780c460001c0c100445800403c3d0321401c1c009400d0740714505110704142c11002240000b680c0d607481100e00b4503006901982070002ca05000c40b07451042c3c1c50501c042c640f0110020440000000c060b0083c3e40c0740c4c100c42c05959440f081010340e12508a810680e2101400d507514005501c03603017201e080c141014040b40e003001400c0d41c40074166048032000007546941c031181901800f50b039000d154000d00408019100c440e0031610010304444005086c41d000350a81e030581 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 59752233 1250 59750983 59750989
    0xc1005040804140d15051302090c0a02250b090f061308210f0c03090a03050106030302060c030f0604110d06060509041109060708030709030b01061106070810090b06040302030105010e04060501091a0d02 88
    0x10f860503500800398411032800220026158000100110046c820120000404280b040500c6066075060b4084437080303290032690b4000c0c0d80440300854000a841900c83c086449200140c402503038014084541d0608100244e031074130000000c60091051030955080303c202c038503021900c80700183d8003113940e2845080c000c686140700c0c480b641508410701c1d110000612206500110a0320302c6030f401d46503075840d000103582443c001900c0c000786241c1d411021074031030b16080d800700100310700c0341c4180c078101403800315000100c0b07040c1c3d0b00c4200414800500080d951034030340310307500302902c10115090400c1807603c040b0b50b40c0d006805008151440020128200c20301a40495005541c8a252001550b071264801888050981c3c6582039a2046102244107503004010681c0f0924440064100072460030300c0ca14050400e400351030390132410420001c005600e0a01401e07020b003001e1200b4103050309142c0303051822140e05031320100d0081d1801000480c1505001d004440c401d40c11201050300c21000c1c000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 59753483 1250 59752233 59752261
    0x60f0f01140d111f02120a0801050d03090816050306010506070506011e050405040c03020103051509070c0317010806010f080d020c04051f0e0601021009050d03020c1005040804140d1505 81
    0x294402e180e164a000b40302104d07007400340c2d5000c6590a1380c0c0016420003580f03d5a0040c210341b40c001c50080c1c40140410b080061681c0ca580b8002e18141c01649d0361001c80c6801e00c80c1d2180b245a0705203000340c09009504042010b540101010341c3c2c03041c40e0122640303940ea2584c41c1800741601d1204807031031504d010354150601002406000340104090b007400c0c5459112400b6911040340440d00b0040040e8203510311000b85091902c003c0c00301c080e1507803004003ca0f000001080210103008108048441c601412803802e80645000d100074140f95052a890b582402a65072120000d03502c0780c1200e1030903a40c0070842d03c502c110156408101a242c0c000f00310540208003107128400760108000090394200d4180781c90080310280c0980f41d007111190180000e031101043d016120b50b021320801005244264018014a01e41030155141441850010003c1d194150740c184c1d180c040201b41840b03a4040307050005240101242c00b014002116950034899882543c5101400b43d680e000042e00c10769840c030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 59754733 1250 59753483 59753513
    0xa1106040b0a0c12030905100b060d0603050d02120a050f070201030905030c100506060702150a0c0b01030c09150602100f0b1005040e0604020c03030a05060d080705060f0f01140d 78
    0x503416250b07100c041c2c004259180c1800150f41084242c0c41200180e40240b02c2c4251840d0004064103502c0c2000440c03001624028403140d030400c1040000b50002a050311034003000d507105001405001c01800002403400c90100d4110445800801840d01281d07000012104c100d148010000d85900d818001030300209203150b4081c3c1603003c0044d4618201c100031400007082d607240d103810499501c41c0000e00c041e501403034800079040f080407003203000030f044c4600142414105a01d45044000066600c440d843c0c0303021ba100716166a91a50140031880041c0501101c40e00680903c01401e49800e034000c5d691040400380408207507031070070a08507001c001c3d00003400540010704042204d00602000611990003441603e40000891010076414600340c000c4524480550340150304645500090900404003d04010780c48404140c510340052902c0c4042d181d114020805480035261450704500f1010004000e048000b20200041c0302c0200340380c90f03884008106072001000c089880c0307841036164200da1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 59755983 1250 59754733 59754749
    0x70b03041211070602071208091f080a09020109050f0d0602040602100e07080c1e0a091a03060c030a090c0b0409020a020f070302061c021b0f0705120a110604 69
    0x104000d108455003200e40e4040941d445010325540c010b0400d44901c110701800005802c102410020750b081c454010f5a100c3c007849400340303007405010020301c030610fa0448180c2010b00054581d0201034000d21400c0e80321601210a0001c010390b0350009154011a0046521407001800c01541c151100600c4050701940507404550380c84e140e00c0040d586104179540f40000c0c1c2d0804485800c0420301140708012a0070181c024040d10042c903081159101d96011103403817080c4d05012040742a9200003d4800900c90001c0c00a40001825003141d0041d9118048900039440304040c8802d03000d914044962040000100251700300f901d01c0c00b0070001c0459441088449000304021495001035401050101e80075002c441d1100300103990305807501a03030300c40a907226a00b40301202c001b2040148161070304000050041c68a8106a4813505000c507006401c0d1180d405440d803203402100030007452010740b1301140d40d41020701e14403210558034030440380010b00c00b8407800ca540460b0340b540b10a0b203002c0c00043c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 59757233 1250 59755983 59755987
    0x20a0201090b100510090803030705070f0501021204030e040c0207150314150103051e01050d020112090f02100504050603161403010e040303050105100219030905271612090203070b 79
    0x80c09108843c43c54040d1a109400700071444108500449000040b18082e5002e1070456907042029501a00420010303550301d8030744e81100c03000803428070090200410044881d98282410f0500401030044840468015890303c200805007640004440c41103602c040a0171008400ca210114094510b03d00c205c007060107100c00b031041030151701c50f400d0304120082e80c1c00c000d903548015240320514110607080d12401c1040005001d1800c00c0710b5940e000ba8010704124011040020f000706c00c94072503940544806824400300000c61415074058507014101f450614140303070a040c0026014032002d000f0100c02d1110008030a902c6004804048024600c404c000751650780d212246103001d00308860032070003c0d18040010601d49005100311b8414400341d13004189500c82c42002031f030050070810090b0280a0342c030f4130010b49a6101c410400d00600c0c0400c0c2815104c184207240035486c0700107411744404808020400901a50240b003201d1783d008048000f1a43e000640007090a103901a00402c3ca40400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 59758483 1250 59757233 59757241
    0x6090d02090601110a0c230d0f051c030221191d070b190315030201050c0c12030a0207050907080f040f0f120f08010308270307081522020103020a0201090b 68
    0x200b403041d0003151601d03a0010240040507e4681c0348207440341200364131800142291000c1a42810b0380c04c0c100f4480c40c12640c1c040070b007640462042d22001d0007000020380000c0c502a01402d400c0300418020400e0400e8105814000490100f81c1c081440744400c540d030b0740002c003520881c00001c00c03144440e000305890400d5242e044000c10340d4003517100085803818101340908541c2c03091244030fa0000d806105140c0442c02d41c0e0044410b41c2c0700c00203c00651249510030085a640c0c65138807065011030314011981c0303007003444019003480c0541e4420303885207503201c0420405a800440b95644000b94407080030007070303445203044a5481803004001e4400046a54000100140d4422040900380192a40060300308a1030045801030000d00000341070070001d00000009003422045511103000070803180e450200d16002003071820306680e215030905d50004544007100068046640d030468008000240b404143c082083d80d0b40c030410344001c1c1059400a00b40b0170b0b55100b9442a0340840c0c1c4800a41c0140c18 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 59759733 1250 59758483 59758493
    0xf030705040501110303010f12030e12030318150103060c020a050d080103170913020a0201061d040c061b02060a05071a010303021903021b0a050a0f09050606090d02090601110a 77
    0x50b0003442d020401c890031800b40e43d2400002d07641200e5514160401301801c042e408050142d050904600307010080800d145595200c603040140c6816400045443c2e150031a868510091046015041034022030070103180c90500c440418152078200030040b03030000c0b400d00102d04c1c04242c14000303440c03806401d42d004803807030380b02000c07504a80c003c07504581286c6100c07540b201c0511642d18a40c0e4000701c41d12448070001b000d5000f50860816074000003401d20b0b6912007680c800000c80300d521000900380300404c020880e0550743c0700050b05003441c11220048995002c0c0004000c0c2d100003a1103094080380340c00d9080d115804556001d5481030410310b009007140c20000c13243c0020702081b00940030305800089100c2c8810416201c06401d90300030982e041940304070b00680131a4604e034039008210103030040b58a0710383e201000000c0408030103078509985089004800c45101034503c1d84254410040364500d030344d4120500d421690101c844402548441006a0b04088404032030340c018055400c1d03480c20700c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 59760983 1250 59759733 59759737
    0x60207050102070b04060e040b06250b07080c032e2918040f020d02030c03040308060d0c09050603010b030106060e0306060901050a0e07051606060501110607090512030f030705 77
    0x60002c0c0c086030403543e03c85902a5041c05603000d442c0001e071095040c1440c0c1d1805400400380d0f194007402e120b00c1d01c01c3d003010200e80d06501755060038141c1c01020b8850100b120b518451130b03112140c0d2404000368181b0389418a6948005422220340740c41d26141c4040a292402c0e801110178903c0300e0b4604015921030240e10400550040c4254009802c038801140c04039080803110080b90b88190002d000a07070308104001041000081a109907080c003000703803078428520003917001e0a030110000da2286031628005140360002000740340182c10820000001031100144141500c41e0a2808141c950310940401e0040641c0b0700c18541c1503007001000580c0f99040140d0550365101501510340d10343d200c030140840d041c405c0c420541c00c000d07001402c025141c26482c050341c1000b028070700149001040300c603d495060000409841e80c0e035079124108490740c0c1000341d4000809140010701058584460094030aa03181d1055a010b100e40c1c40220708020810b10403220f0084409100e030b500c80c106440c0040c095 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 59762233 1250 59760983 59760989
    0x903080a1a01080121050111041517040803090c0910081207020a0b07020a0308040803040e01080109051e07030c080c1207230604050402070f030219020109260304060207 74
    0x160340381040020888460041c0310741c45140686a000803070346004000c0040c10600b410000b031040ea84203416001860a0044115480c1c0e4030b8484c0f9212403c0c0800d5100303041c581c40c1c050090089105603105000c03100402c1c2a449500074a01a41720f80d203030040c942c103144000004540c02043c0c0c1d400c0100c450405481841130710126001c66160404144c00c16060303114020001c2c6d0310401103d41045100700042c014004203101411f221001580d9540e000156042a003242002c0e410120b400c1c000746d446840c2182c01000742c04000d00149000b919260b4070380320805512408800d404000d840540000c111500c021607010007040b9106940d00304190301e03503005070304c6180f180d10700c441009081d00c0d002804100b650059030500700ca282c5410044a102c604024150707400880500c80081c440d0340d80e101034842c05024040c0104030285510b002810f20320003d00c0c00c1002d0301d01000034070150368070145001c00c0d180304e02c0b1840e010840c103640b4a40b0b50308800300b102c9080d11000402203004c40d4082110021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 59763483 1250 59762233 59762251
    0x1d130b090d03061505190311040306090209060901120f0204020f0a0e090610140a0c060905030a0210020315010c02040b03010e0703050d02010c050a0e0f03060106030b0909060412080a0609090308 85
    0x803068a40c8100d0451444070842a400a0707170a10240040540380360440c0e00307400e03250900090460804128020641141d0b1007503d4817507441d890728055050501d9002e6100004955042c6a50b0409240c070009039501c00340507000841540c20201191200d81c12264005200d48020352a640320f905c009241c2d1800b0300210707008001500101d4040c0c1414080604640c41c107899401001e500300c80004460340109580360104244609074101003461485445001c80c0100040c60707070391001e6080a480c0c408a98107154059104008201814400309490070440b5024078242d0703940e08080c000140030f420100203480c0c4c50b500c2c0400020310a00000340120450b8401c2040c1d540e03110403504164200c0d40040984408124204444542c0034468403076580c4080004201c10000241c0c0804286020002d0b002140884d0b6601c000308110310300070701c0b83c40e0b00c0201c18009184030310b016039030366403501e58890480c0c060020500100c3c01d4907203950040d0010b005450b01c01c11484403903041c02020903400b5604040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 59764733 1250 59763483 59763491
    0x60302040b03010207030807080403090b1204030201150305030d0e0102040902040b040302120a020a090c0c06060e07030e0a020609040902011101020a030b18040b0106081801020409020a0f091d130b090d03 89
    0x1a003402c06000365002141c05860b5500c03207a840c450142d487c4040104210100706440c44c0104001454002030701a007a804c420900c007915142c90040c0c01c4600f042106829140f01c007070100005100042240c1c2c0b545003500001c15280f000b01081ca0180c0116000040000c1c0081004602800c0a80c064404c07a4021641003001e01602c150340d548504601101940206075060180141350464100c00f10001c0c85141c201d41d20002604e542007103900c00e400030045d005c0b100d018040c119034540505c80358040e07640702604d03004c2010350000d4094070910000500482d200c82001042d68042d404001750100040000c0d03580340c120325001001000f4100500f445060b088100c00010f40d9402c00320b611403030703100303141ea40780740d0900d070341503078013030801040081c2e0f0716001008040c00e42020700290000700359203c000350b01d40c41c281e04068141001d020001c010002c100c601002201c5103000300c100b4440d07207070740d080c030709600d6040822603905044d11780a4840c0c2041030511080d8180080c092401041680e0100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 59765983 1250 59764733 59764751
    0x7050919110f07082104050d030605010906120b0102071a070c170c0411090310050603100912050a02030d06060521090d08100f0b0307090b0a08160306050306010906030204 75
    0x100c03050052010000620701c050208100045400c001000c01c0504208030b40c800240010f20604240411941259150400230805441a0305400740e0005000c09003408070555080c144024a1040e41012030702c07016071140820703861a402030100f0000350460011002505040b41c130f60040d1a40240012503494016035000034021180602103000c1c4150030020b00f8043c03400404200180c0000c00f0407640580c0104042c4e149660708100c200300d503a140b031801154524254040500308000160140350107800c1024500004c1e2140ca1014664481802d03c1502c4007610f0302c04070f245000e0070200f844150710b401c0d0017040307071600301021b03141e20511002d4140b10302e89001800d00c0030844c117031052032480e03101c0e2016620603401140c5850344000308103500c156413a42c45000000040d520740c010803503682c000051017251984403000300c0c003400100e0101032038462180401861400000c0c414548410a0a403050303405200780c002344000d01006045401075611020030000601d6240300880c032a526102e004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 59767233 1250 59765983 59766011
    0x5030102090d060c090b04140406090506030307020904080702040203040c051009060e060a110102070606030b0f0603070e06012c0f040605060a08060a0f0303030c03060e131407050919 80
    0x31544880042e080710040280b0340d9070030001c1c041d550500c1d01407020251011032145e82c5503014000504a100109060941890a01042781c000c0c1d0444000c0c18104420045d02e510000f04071016198103440d040e4090303866080501c014000c9900007036100d4000401e2109000403101c0c07090a4800440e01003942114106003511034191512800c80403910041c507910301851b00c1000390001c82070500b085502a40540989822603000c1e01044400e5030f034072401442441210804607510551801e005011410101c0019607500028460104280d10311000158243d204401290211b80c0d0004540d03808403458074036050041c0c1e1100020b000702d0074090722544034035040c0a05c1044030006031056190000302c590499000c41c00401140d000a40d4500018020f02c9a0b0603900003540030b44d6001078182c16030540101507800540c04506544483c2041c40078210800c60324920480c0c3c0009164928007801d40038a080c04481c1c2d10460340040040308204a0b504032201851101003003100c04c01c68000c0391441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 59768483 1250 59767233 59767237
    0xb090303060307090f02040b0c0d090b070507270c020a15060e0604020c150108010b0a14060a0c020406090c02030c070b1c09050316081b010501050d02130b031e060105030102 76
    0x250380d6050f03000c043e042200c000076030322441d400202401c01510b003a0315016254940d6010f0100c442c030366030082006001040c0d00c694010090141c0000303c624050007030b144c050b91000706008199610950302c840c2d9200004011a00307034510307140003083c0019110020040d4680ca41e030801070b40c3c20144c044070f01d03c00c10200d00c02d10302907d01c001d004400d19180d440900c1b00a41104041c80c00d148a015100c5061406082940b070081140c4000490404104001d02c824405158032590002c001c011300410180c0d02c402c181c406104261501e900c8141e0680000b4015080301c2c2e100001c40c9141c0050b00546c0c55010000742001080b1100b160b01c0d05503940c85503041403040c003000d03201904903540c038104800110f81040201e43c2c058021a41011602c405c001900c3c80e5203501165042130009a0005000c40080044100c1c090f2070700800441d8907000c08544524100390000344916107004410300030f100564031400d415500038080760650f605c110b42003080440c030030a52003501e2103400000101ca15050003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 59769733 1250 59768483 59768491
    0x9070b0c0a03110a0b040b01140a05060301050402031003140708060916060f0504080303070503010303021006030b010603020f13080f10090302030405040906020c0f030409110909060904020120010203040b090303 92
    0x52914050700d84049600a0940c1078a0500d40650030b8060046180040141e016a004014484055142262031040c800c400b0b00d01d0360180c0030031001002240c0e104810fa03811240141d50140e0b681d0340f2003a104060440c0307900014052400307440c500d08002000103520050b246d1480840d54691111842c0a50b50144d00d00319006681c110300342442010301c2541c0c04c030b0a181080c201181007903140c034406401c1d030300100d030745000142011004005140e0f040107a54440180e0715400c220b11421074451000b041d0341401501c041c16000500988240800c4044980d46802800340c480c3e001c0d110461651110003204482100e40700360034070002c8825051045071700d160340c582c00440c40c1500c0c00d0706020184c20b06241c251110b550074443c04160301014802d51600c01503000c040c3d0740d130320300b4090503008561804403085074861003800071100315125003030140c0e0410340445e1140542c1e0303182e200417155008005103904c140c2480300d011100e04841500914090340c401e01c03501e1695991400d5055417404126 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 59770983 1250 59769733 59769757
    0xe01020c010b01091404020a02030f0a030b0906041b0807020f0303090a060b1e010e0f030a03080103120e06040504020903120d0f060605090306190e070b040f0504200310091409070b 79
    0x85151241c42d03d07900a0108c0186401903138180051744030700703074503e800190501011a4480039178030101c0c5802003402d42c0c010400c5400b08008299107443c0ca0b203110104405000340325181010481e280c5c000c00c490746580b210402140e07070703a1514004054441032000421248203050046044440c41c0845500b10030306188840081c0b41540744004480030070100114580100040041059544052244404950007901d550540354591b141c240c0032020341d103221000300080d50700d400002d83d0fa9101140d04407030342101c0c0561504051000a0304240500d4504225040e0004064080540302d410401001c0800641003020030f54440007a1514071488c060568035800c002c0003e02c805501a504c040007100351540082e0700c0149029480c40d00c3c0450700308452a401c041020406482555445805098195002c2c41544400c0031000d007911941c0314950b940003000302c0081d07804c84807d2000d00083c46000c400b030207000b902405a020b000b000341c88100287c01402004102e081060b8100c070300c0401b8003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 59772233 1250 59770983 59771009
    0x90f090b030f010c1710122301020901090e0a0f02040611070e0f0112150e0a050105060d0203030715020c0307120809060103030e041d06090d090f03120318060e01020c010b0109 77
    0x100821741000c0062641c0315240f03280390080342059540aa03403034264424405881c040049203100000c21103514032004d040d0703004000c2e4010f1030740d008800b5030499420000050003071f15603003103030b01c003402040d020100c1151021400003151640000c1c1086405042e0056810007902e449803203041c410100c07000300c2520104c0004000021116031460b074414001d41d451015951240c24090035104020712041c2d0b00d601c2981e040050290038420f45400040840d0f060480304401d5010039140e008024028002841c07580003150b0070000f0340c04588020341d110f000d50748d5800d25407030900b0700465806a10b0700002e41100c0028128800002d9180c140d94160300d03110b52440703140d01040081d05030001e84043e0340e00c50307904080e402c6034100101401100b440d4040c0200c5145484000d017150541e6101e401b40b03441020302000418485406025a9252450302140300700c002e0342404415810b00c10001c0c07015281c240c41c9000040d041d8042e01d140f030322a4009000d0740c46920300440312000c5600400079980b00c6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 59773483 1250 59772233 59772257
    0xa11040509070c02041a040b030313120201120c090312050901230702060d1d0304060e060904060e040b0906010602012d110c0105060301050a0e030a080601090f090b030f010c 76
    0x7209800741d01110a1400b11040b43c000d5012030150b4120300403445a40c0024841c02c0c6491070103000d04248403606a0003036080c004481f007a1031041a041c0300d410b859402e64400e00b019039202c3c0717a500540c1d10040b6003d00c26400007a0303005140e1802c0e071005803410425000d816260302d11070012142d464005954062a250a80c420b0030b00c030031420b8408220015042081400603242c1201400040c031080d800060030400c0c07145403904003070b0313030311520541034100b08403e202d416080320f4041400101600e00c15111f04a11020400405298200754507051901c4200030410251071038480c41807510341c00355621a42d039004240e01340e40c101c0c00120b5000031400125a0070503c2c604a80c0b211005111000c50804860300203451158440c158443c0d043c2d449904200440c04c0902805070440e080c02c00030040352845111080d10707030003038104500c10020301c0c02c0422143ea210745a410003a24041d41b50180700e90b41c03032030745400a0086103450340c024000c50100400b20f000621038500d40c0c0f450b0751503210003408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 59774733 1250 59773483 59773489
    0x11090601120f0902030f0c0d0605060301020403080c0f0d030c1704061d0d09050303030c120703060308130303140906040b0d1b03060819020a05011b05150403080a110405 74
    0x804240c100580090002051103070360003008180000d80e00c00081c00280307401414144000c41420000540c401422507015845e81050590f055800900015640e100c00c4000b90191007164005031603550082443c080701100850320071003608070f403803c8a2154035038000507000e4890707041040001c0b8176014280d0060016181a0544c0300e0b2040000007800c60b8150005c00050070700d00c4a9059a60089010000c41034001da000005031108500031421403910030745280807803040301c000021505444d40481c0f10341d03000782c11003400303076a000d66078580301c0751003100400c003104040c4000d8000400d03a1405c40c50100c2054220340c080780010b42090719043c10185540c00640c030030b41e2b2f030b064425612075011090078903100b041f01c0c030b10b161507902081c018900340d030a501d071002c880c141c200c0e490138800424006a4550682c0821a002802c21990f00030500b00e400325245c40c4c28030090614080c2680410344051901941481a4400c1c6c03944603190b00c600400d40d0480d00c1c1031900c98001c0b401004144140e103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 59775983 1250 59774733 59774749
    0xe0f1311040e0c03070f1e050904020607050f0d030213050105040b0304020d17040608040c15020c131103010b070201030c260c0903030d0c0306080f1002070c0512070e1311 75
    0x18140b00304a821214007200400d107041c8159002c5c40280513200c6051000300c401030041304e2a41500b9401e00d070300034105000030301080809840280b080e00002060000c000c400d1200301c00b18000c0c601a60210000340c2400340195200401005155041700400300b0298040c10683e002d5400d03200d031050640e60340e0b80c2030120101c0c009100790b5130b803c00b1400300103540580030010005442c0550b914109410310785400c40b942440d07074000300382008801c000240740b030741c0c0019180040c4d02c1c1150a9041d62060380b84c0d03003004081c0e2041c04104003100000204000c003061009002e650310030b170780030410340040e01c20459200c0300e0100e008088207e437036a00c408401e40000300c99002078840400300c0c40d1500c1240044d285510620380c218001c0c0d283d0352010710042d00751264070020b004180251404180d020510303034403408003410340c0b04002d902180f0207050000e0a600d45000d86000b600d402c000d0b01207071102e95030f1042c03c1d11540794046200400510072403c004102c809990380040e00300c10f40201e00c4100001c2c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 59777233 1250 59775983 59776001
    0x6020604060209060c060106030e0105060409080304061d030703020a15140a0e030d09030c060b1c0611040b0705061b040b03010b030601140d090201080a0c0206010b07060204050a0e0f131104 83
    0x2000a02102c01d1aa50500001f402803255840001d0361301340c0d92a110382503403001404944654a4850b051011a0401040745e500aa2103800042c05488503500c07043e02200354003901c00c00d80300109000c0c080540000310f075005e2034040e98026024100100c80305003604d8140d80c01c00790200d0034002041c03480d00142c0040150107a03100581e030038103192080311011189005001d900042082e5040c0091003c14460034500790000d6400009840400201c07143e01880c000c8000c180d5981d889074020380700c80070015100580021880f0954030709140c00c02556454098810603030b816140306202c0781c06103014040380c00311481c460850382541e18104003200c2540008082c00d05012289840c2403164001c07030000c0464400301c800c009100b86007800010000f2800a00e0100b4003881c14207811107698002a100d411903e69480d4142e0311718461500c4e0020380a141d01c026080500d945c008920036a00c1c90142d8480c0380040c1103d00e0f00c0d950443c801c82c1041860101a00d0440c00c1c400165440c2425003100c205 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 59778483 1250 59777233 59777239
    0xa050a030905010c12050a06150c02030109050a0f0308010f050310020c03070f1401060b09130c02070e041a0703090309060e0a08150405060609103b0601030b0a06020604060209 77
    0x9241d6a54584900b92420400702078001021041c41300400003842c82415004484800104011810700042000072410b4807a241c040c821620300040031507809400401c096640041603030b5454246140001102143d4417080b80441c0210300086191513603100c907042181c43c001e0081030341507000300f0305100a6000002404160004005410119040d0309511683c6445141d248580f1410629600c0c210b800303d4114118540040000d50703004e5480381d001d60b81d041ca400300000f80d00084c40e50203034540700d96940b00c03a0065240f43d0400041c4603034500d201040c3c550381c040d465156070319140700300d0495180d0320005002c41d0f00600140a00c7d80300c0c0031240c189007405031803190358075140c1d19803d00d013146030f82888060035441d10405c000c1003018400d094000c0c800390b4811105090000e1007480c07944181c00340804885040d000740d10701203194580c0340740001840151015005840050103080c3c90109c0e1b4482c0401d0900e00f501070b07241003008140f404c03103460343c0c058445601c481d03845101a503c59503490354 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 59779733 1250 59778483 59778491
    0xf0406050a0209040203070c020f0d080702040513020315160c020918120f03060a0603050108060a050705070606170c15160c031b06090b03070c03050901030906060f09050901020f0a050a03 82
    0x280c0c07600d132880198000c14003a00d956194490610400184c0c01800a08600840081c0c0000b80018910415154050350440300804d07280d41700030100b1941240380c20007940c07510a08140f8000f241c030300210f00d40143c0e040000f00c5c2101c941d070f01e01520301d044111002900300407041d002405000e44c00341321964980f0480c099621050700c07076031841c4c6540c224515035000780d500041448591f250030300c0d560008008a090502040d80341c099029110380380207104801068503040021080d9224030115202036505c02810891aa224030054940e001030400008040c85149610300c0c040c640404000d05080340309103404c1c54140d10480c83d400e4110000c000f1226005013101c0400001c241c80b0f07400010182d1000140e80091a001c0024200f00d050340c003140c51101c080041c01161607020180d01c6200d505810f20540c0d500c111030048004020448024006525064001c01c0580b030415014049509442090107035850b9030411500303d11800c1c142072026101046a41c4505d4082e10262054403a1820002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 59780983 1250 59779733 59779747
    0x90506120601021501080304170d090303050f0d050117061b160201110109030503070f03020403050a03030203060f0d0809030c0a05030c1504030c06020606040e032a0304030f0803040c0e0f0406050a02 87
    0x81c0c00444c003a08448800e42002c83c0502200c030000c01400c125006000040c0b101001400c0c02030700104c1c0030b00004c1c04100d0f00007224a0180040c408444155400400c104407660b0343c3d500c2003040140c1d405500740240145404158200c21004d004000d02d10720300e0540d1702e455240e00501410b03648502c0c04905000c0801d0212151038401e02c030351044980a0f88866030b072850641c0d401080300344c040d0415001d00d44140f00a00215800050070040c103030b8181001a40d81c1c460f4070005200f45c111240c0c259100c88400700800c20445200003400c0c1400d425011601c1c0390301c0140070441045c10074081d02e60180d000304005102d5150009202e165403072808038031031601d5140d4480c100c540c0555040f10015038048030a0102c9410039204100c035400c8904091170410340c840071030031081c8803c0003d109400d6250880030640401c01d00407140219441000c40d44405400d21304001141c0084030181c4002d006108001081c0c040c901c1e1103441407040c145403007465611742d9034070b5008002c041c110b8007100398240041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 59782233 1250 59780983 59781013
    0xc130c03110319110412060b010908030c0a060605040e100518060f04030212072301020408010207030c02041d1c03020403141006060e01021002090630010609050612060102 75
    0x860051285000f014681000c1080003025240b42c4d14098840c400d04000811000c1e001c0e00c2244481580000e010450181d2440104e44090050300301c40702500000800ca4160b002c00521011400d1141d070301841072030365900400086903043c100d0080c80f50440b0141d2900100b0341e0780144d47c41100072401d4006180c000c1e03101c07882c06100b141d801151001744401c2c403040c1501002040c1500000c00360741494116190b41d011a421810744030118400c4040c0070f40030303145000390140c5000d4401c00b0004c41d01c8032500e080080c414600e903481039010304e1419014007079182c466054009025101d0303006001c000000340308007412880000020f02015800c0c0004030002d6440701600c4412400c410003006090b40c010a4182100c80c10b52061082c0264180c01030280e980200e20b01c6c4054104840040e21819200e000c14818130a9100c030ba200a82910380b211030110800b0300c0072816441808610207242c0c4c03140c00907180d0368118020164044402e103c1c0503001114081c3c625441788041c819504800315500746 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 59783483 1250 59782233 59782237
    0x105070207180e0a060e161a090108040c0302100302041a040503030702100c080301091b0906020c010e0a150206070908031201030b06130f0209030c0102010b150a021204030c03060e0c130c0311 84
    0x1d1a03900410032249111507ca12100c2c00340402000e030989684444001c01e4032813203003009a60500294a00190500103400603400086030040d00c01700200e410340070010025840303402500b120747c054034000440e8081040589065440140003146081900d8080268a041e440c00c2c500811810300024000126030b038010314000c00c41100080340c100815640000c2c40e0b440128640e0401c11500b0b0708204c09540058803000305403080c20480d04860000000c5021603401c0d4210326882140ea2014411207580054094403450741c50752484001c0747c41c0d020150f280d10583c201c80390040025001032004c1088150a55000a00100192401c0c940340c0116002d4800b888580810144c0c08916a106802c040c052000c400c03600344020840908000e00050114148843c45000100082900400540200084298404c00c0e400c8552620364074039068029150714042101c1c3c2d9030900b5080303180f90310f001510001c071141c000d10392010507060341c0441000b00340c00341409003007540b0348196105000c65500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 59784733 1250 59783483 59783501
    0x304090f020304030e010305090c0f01030b040203040b01030c1e0b09010c021e04060801020421080405030a0807051006060e0d02010e040f0605100c080a030906090b0702010903020105070207180e0a06 87
    0x40075807030745840e050103030244001480103414142040200160140086455442d40c2c00403107c41c1d41018402004030001d250f0103034036680142c400800d0100344040000e40d94102d034403603809004516102e501042c01c40303003da1021402c911a50380e0034011004e10301c0140c40101818544075192031000e4000034141c0503224590412850440703c443e80d0790405000d1200a002d040c402546841d140120422046800c1c002900c03030580b00c0d41085d0100400403084030014070000b000c4030101115030500144540c000007084515200d0b0500004602c1080d0007010304603090342e200d15816080c01028801030007c4044101d041180700d0204d0681c40d0360720710500001e0032403040d0010380242801c0900c1460f424288014040c0710281d031214000901202c2140e640c446103107404035016542e40744c0f2402401900174018040883c850800c0089036055018150303403402076000340305584804900340d0b103808280c010911031180e842ca46880101c800d82204011034005400c40b041e0039416258281101c50004c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 59785983 1250 59784733 59784761
    0x4121e030503160207140108100306090503180103050f061908010e0d0912020603011e151115040b07030e1006032105040509040f020303160b07020735030409 69
    0x8803e01c403003d0241c0035480c421681c18001083e0b82030400d44003460b100400300b0607034108000840005c20218440780504000e66000713005002c519a5450603030f480c0c0d00a00030344c408440c0c0b402d5560215600c02c0c002c070b42c003400204001c01d00a86031002403000c840380c0310078200e205681c88031000a1110003440389010312050b0300042c007200c0c03c11550052100d00c031703640000c200741006461200540c0d28402224112035074134410250141309003420f501914010750181c50b45c958a08150040c064101800c050455031850030755040c2843c41080003035034038080d1405480c0c40d0080e00080c0c10030303011394440744000341d01c64200c4959040e41d0035582c2c156a01500112021282c8000300c01001c181d090f412100d9682c603050050420f810316000c25020780300140042c01c103001301c02e0b510702551000d004440d1400c090701100ca03010803079070404c02c60140c1d0680b03844c001841440000120310b40401c1c10a1101e00c490f9840140364040c07041414080c01c200601811a070000300000100200144640703038220030b040b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 59787233 1250 59785983 59785987
    0xb09011403070501020a150b01091a030103140d020c060313060518060f0106050307050f04150806030609070503120d060506030403210207031e03020405040608100b06090604121e0305 80
    0x10400d26081c04240c3d40010b056500481705500010b184c00d08040481c031031070000080c4400c003880125070002c015800301705245010702a29010869880086050305e01a15107c64502485840f0300e0361082c0e0400c1c0c500041c1c00c00d485400f91071800800540e00b050680386040c10302034590b01c07844115130095517856807000e03002c0304000300f55105110a075071203117910b42c03140c20b991325103040a086844020030311000c125000541181d034400c840d003070300e0140405070448802d066015502520101054400a2080c4258000035514000c00240c242c1031f510080d02800c0f00940c4800c0182558000c03032035008005403203030408078441d1121005107201e24081d540c1c50301802410075042c041a2101c6402010b118010401c0c100820741000717800390291030b5204d6100c5884020a8110002d01842d008554031904190000a1425001405c40a1b40341d003242c04214140b61202041a00d00c42d0508558201105000401c070490301324003000081d07401145046040c03081802100c5088181c0682140400c43c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 59788483 1250 59787233 59787269
    0xe040203060f040302071403210904060f06021b060405030f03070309060c0c03030c0314040602030a020705090f040206070c08010c051902060c032e080606090703050606040e04060b0901 81
    0xc000280c2c0001c030501c81d02c1e4150410b41c031300941391005030042021840e03000d00a4401a181045404403c0500c1200d048000c00c1d1080380306a207034032480200344034038140500468052002c3c49520202c030384c0c5400514290040d007040c03d076161200f0041d545d0000c820300000816850034400c20207401d46c0c10003c0c503030f07034030b40c40c940502604c80700e0b0482c004000008140c04000707580403503030300150f9415090080720300c0c1c400d00c0c0441b036002e00c0c10320b0705400707140100e40061240c1d00000500f0759400b55400741da01d801c1d1190103204103502c0490300c12811103043c038082000f41c1040780c000c102c807074022020444403d80717441c01d2030f00b0345081c001c0c0d040000c0e900082a021000f480e06610345800014406440e19042030078290655000c003501401c0205110700450042100181000c3c803030007515040308200f9540c840c44d080d110401110070320700031001d00c400260b5403407281c410780c1d02c2960300400007424241440100115210000c00807166660f40e4125045c103030b503c0c052414020104240d40c00c0009078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 59789733 1250 59788483 59788489
    0x60e010e060435030c0d0e0303092404080703050f040b0310080607140c01060f1707060906050a030b0a0504090c0303030b0301020c1c05161202120a0f0f05130e0402 72
    0x20040414000081101d00541115003045036004408203c3d00301d015103c0d00c030400b04045e03510445141c0c9419510305034041071456000300296203c0d180350740503070740b0302c02c4010700d6483c200c41482d6142c400c880c00c3c03000040c0010800d901401c411030181c5001d9083c0040d061040704e003680316800440b140040031042184003401c01e107446001d41119400b40c40c403410700b10f201a050320030342e196a4025000120b80030311105425884403005008944044811503540e000d9442e000d140d111500b4124029282c011031910f0140482100301c1e12695501850045180c004030028020b40000b50740c01402c880340003030740d0783e194000c2101103800352050b55160f501c2d40c5000380480ba4030109082c000e9005201c0703132190b21004201041604c04505444c02d08204040301100c0070701c100040303d130306524482070340014004c0c0108011814556502100c1110130301d110200054080c494810380000c0c500c0940c0c5080f54807486106001c141142807203070610003041e005821070703030494102c00b01d8015003400b08006d500e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 59790983 1250 59789733 59789753
    0x515070306230603070c05161202040c0903030c03050307030213090b030705040c050d0b1503071215030b04031d031e0610050f0d03140307080612010e03090409060e010e0604 76
    0x1c2c401400c00344010000101084060200503c0001801244a21007081c07120900c035040901141c031841c0a00640c503140d08101e42c848588050740070307e141090f040c0078039000700c0030b00b003e9030b0701612422a580d03a15901203403940c0c801801d1230201502403240407000c068590b0b102d406440e0349400030590110290a040c9402095844544158100025201c1c0f20f90080c0c00c880c0550003001e40441d0b24070350200460441b40d00383c500903100e100000100400c4640c000b06c041c41d40c2185c05418014544855507400d00c050050001401a41080000c9000607008803190124240d080302075101f1541900b00080c00c00c50194171013680d0460401440d0187d100a00c08160710404c0800f6400c51242061701140380003034405545030040205850a4061500950710302d40004144031000ba581d1502142c014101c07681550014080c03252143d0b03007030740d42c0b07418003c60504021080046081c50040810040903007654001500d81660740c1d40803502060003809032810820480000f00300c14201842e02c0f6001c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 59792233 1250 59790983 59791019
    0x1020607090506040b0a03090c031a0a0b0f040e010902030a061a030106030c05010507080409060b0702010e0126071103030c03220c090207240507080a0e06010506070515070306 77
    0x401c00d92024407265070781d03000f03036003da80c4005002511041640c909034010a041480640240b46c2c0d800000100b0200f1240706088000008130280c060325051046401d80c3c032102001d6501901881074a5258240b80c0d00c02c404204d045e0002092070b40b500d030040780c10002070100a0341d4250b16402200c01b4251520b4a5406921054000700070305843d50b224007104180da405940d0402c0b90000381407090000c0c00041c0d07001b070502003c0400006075512841c54a80e07010039022400b01e403111685028941c0250321100da01200c04480c1002c8013181c200300c2f01c803602c004120310180454000140002201007014500c1100005402ca580c3d0900003c41580c1d144003605c10522490b80311703481c20000348520302100807586400c5025865011030b140c9118070745c100000407400301c0c800314840e120502c044d800282c00740400c2d4641c214541c80710624002915000241401c65034400c000403c51410031740c0c02010792502034800e0f200602070404058980d01d40964000c000241c507680244441f512a501c00105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 59793483 1250 59792233 59792237
    0x18090a03180303020c130209100201020d0f050f1801020c01090f020411070203120306010c1403030406061a041814010e09060108030315040504020d02130903030e0c09040f03022a01020607 82
    0x722841c60758029900c030760600740369014245110134180045116015500c086c80c2c02054002d0301030b03071000d000703000350040031039808600c0c28150480010301c0300c0d11400b4020401049102d000c1d9681e201b5200a03040f001550404540d400c00c40e8402004081c419003500342e116400c4052030360318900411041c2c0310801c032405c40e01e20b41000785400585d4002510030040e040310721030945a0355078400503115816804c2014000501c000314000c103903600030009522440c45a04200301701901c0b040c06103003600d00340c40e11903405a001c010901030615400340410350304640b00e0b404103501400325006464424203a003c0d004109181041c000094414400240500711401c003c6003140b800703a89485043d5a14000503011f075641d50b005c5004c1d0b4650050030440c4503005002218100c01c1e280c41c0d80c0060403040e4060340005e1034240c5003843c82c80080f850000c0c0c0d01c0002c1003103070944c54030f465442406024480031800d511840c45400c211001c110526003c1c4481c140134848108129400681080303802000001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 59794733 1250 59793483 59793527
    0x903170f03180a05060c040914091b030705040e0d020f0c090f0903070f0803010f050f030c06090a080601030606091109030a0b06130e16060801030803040b0618090a03 73
    0x40544600098941c01228076200070310a24042c54030700d04105148901400070301611040142c041c0002004000700c2d01ea40c9000c010b41008400c09484080301500c00c0b42c40e036088030b03048241000000d034891031490300c000e041d101c0b000c1c2d0b101c0018007250240010000160000f100c2c0c0580180c042c8a0394526020490251406c0d0780c1907030001c3d41c9410002e00056800c0d80340b50104e100c420040050304c18150780300b00041c41010340c07820b05c506a6042482013040d040c0785444089218103084180503d0b2002c058020304201307144104002082d08200c0b102030b000806060b000034101c0c41081880d00850090f040060041e003080404000c0d210543c0290200300300401050700b05031400039501021a40046002e005c58a88800141170154458001a052810b0800c0f140c001e08010a05580140c1c10482404070165140b8054691200074840500207000910000e00030030901c0181552107007001344036190031481014846000c80094500c80102d034042003c03281055049000100c01c0040719072005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 59795983 1250 59794733 59794747
    0x9060c050f0304060c0c0209041a06030c01081b071b06020607050702030c0405040215040617060301060303140d02160303050f0903090d20030d05030406050a0c0c02040b0a09020a090317 81
    0xc10b80300c007070402052260b90f02da068106070710035002244081d80c0180150384c2070405040c0f01507484240505910255007410210700c0d58940050754000e02081a140c0c01c1e0141d0383e40d20601c1031030360615203981c4948020401c2e2000252000107007800e15880d02c40000a41d400c000000340b80483c02410b0b0000d011080060300e0140c2c0d400100c0c480321490455022415561b2880400e208a6a9819041d1808008140800c0751034120030450040c0500d190f00c0c9010781d0b12601090300b660050b100c044d020034035902840c526550000000c1400380c031040c1c0054900716104c000c0c41c18034003140300140c00003552030b400c1c0b10072506c500f20800e0704004020011420801d5840c00200340754201180101100104508a03111003000001200c3d60750307006050302c240307807021f6034050314503441140c003190814600070010350601c1181c031543c41103010070360300c50001c80e0310307030742408003c00200c14031684c4034580c8800003c0346000c0d07000402079040150b8506105920f580b0300690110061014101661030034003442c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 59797233 1250 59795983 59796007
    0x709080a021804030c0c0902091f0c1e0c1403010b03010e070603020d14070903050d08040f030503130b09030a0909110706091703090318040e0d031a09090109060c05 72
    0x10b0198644907205041c2c9491409489203180544001c0c254016074500290910341c44e0701520a19030151846094482c1c1c00c00c40d803200c01115410140490340500c1c074a0049020344584100d0010b80b0114030b103412036141c0390f0304d07261141640846240b4080e00c4a42c041800c0c20300500c83c5048007030b8001d1110034407004043d80c031042c603070140f0410145d0105e0030000e6140d441e005100e80045a945c1200541808140101980d101c0e000503161849000c170780c101c1043c4590382d0310344200d0300120704613201d00c482e5904803011341c409084104210b107801c88200101e00600485d03406440800c0044d6500c0201400190465005a00520001d031130300058450040044046600c0b00380e10140000c1c54803454a03201c10444100710f00d680309100040308100d01c240c0c0c000b00401c280c213014048052101100c008000075581540a02071840e00034240c101c80e054020703003011151181580101395502e00709400308100d50300c201e0f03150010781c2d192407441c418000c07203116080410f8044e00c0c000b4949281c00d981 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 59798483 1250 59797233 59797249
    0x306040c1701020f070c0518040506010303140d0c09031b0e0604051b0301090c0e04110d050a0f09080324090c09040615080604050f060f040b0d02030a08030709080a02 73
    0x1820792a90342169980080c0c007002c1d8102e4030722a402c80703203468440d0120b050822a02d01640540790042200c0001c0b034030f1070000d400700113101d264028010040c0b43c1c00d642d01102e000038014882e00c8152020b00c65070b4594440c500400d0001c100301d41c0e408040501d1030070000d080c0880c9480b200032010307070404140f1070550032500c250f5000f6410707500411242c40e0041a4040350400c8540300200c035030044000f033100c050302d07084100c00e0b100964503d100001a0001c100448a0b80d00329111070082c20801401d1040040e0451680140c0c6113100150304144c00c034904c02503400c00441200c0030380f8000100b1000441035150741500030540a40003044210403408601c0981028024030a91180807850b0541507865801003400b404d440c00240c4104001c01401810b400015942c05100c3e50516001420640c104100031303120303080048c02070300e90405940a0000031b280e000c010580015001c00b1080258500b003094010381e84c4034178902da6882c5030280d8014000700c0076400c031304081d130041e005c000701507520410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 59799733 1250 59798483 59798489
    0xc0a02070504110f1c06080c0a03060b01030b04060f0303030f0b150706020415030603020f030105040209060103020702040b03070e1e0405030d02030702010f050106050a1106130b0c1209010506040b0306040c 90
    0x1900040f00010b191042415024894140040200001d03202124803001c1c04100780d9034075007603020b100307803520391000070b8071201c503000000d030071440c410f03406c00225041d500203940005046c18001180701100003c141034a140740c01540c800307840401c0070010140c3c5132050944403801600108400005880000c00790408001070781c8510f0304c0408c0c508140a05903040394000d00d6660820b003065564250050090030070351000303901c0f480151000609500301130150078801c5a000742413910340e561f408015402034005003002d0360440e68401c1c0d41403450700c08010a00160090900c401000e1900300303c80c030400400d04001402c2079504005000c0003e4001042d1280343c203440c1405a122355440400324014592110700c0040541004000516a0b400c20b00624000c50aa90341358005200f0a001c0740d540d803003c0d500c41005481c9950700c000400c0c0b50342c0c205074005212000c020300c0c00781000f0307016400c001b040c0c49103402c0e6503480044c4850703444d140c4a2111043c0f015006486c503840c0c03e8440410201c0c41d44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 59800983 1250 59799733 59799739
    0x3010806010e180105041101081f1e090509010209041118060702040f090c03060608030f0921070e0f06040b030c0d02030f1005040606060c0c180902090f09060c0a020705 74
    0x101c04200c0d107280004240c1222145000200000c1c03906d403c014104116405900340400e0300d240c081030450020340301c00c000d81f408c80203441d1032444c0f03807540a0300040c107481ea415405030908c01000c600350869008947c0a051080005a12910034400b0401200c0302e40e000801c000314108405884142a1103055900c1a0101c0701207440d50071a00119020b404400425410726240204910410405102200c1035a000c0c140030808651242840b543d20300c24441c81c96039580c42409040c90701d180c1074200d1034103040c44003014010a0041450a0319148081d00040e020001072000c00c10103090b0010415071200703048600303100302e2410f0400b1a0701e9041c40b050450054022044071002c0d91420801e500003c080101220400d04002103001d0042c401590221813440c289400001c440e480794240d020440d0300a081c0825041c5000300c0b004003088000702c508a26a00c0f070310480d0141e61549a80d501c40c4640c5041e104081c030300f04800d00c3c02c1030001003440b2300708281801403211141e07000400c942624425 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 59802233 1250 59800983 59801009
    0xb0f060a120c0519030227010e0f0d0c060503040302011b080408160203120a03050f010803030705030a2703030b030d0e06160f0303020c0615030d0f030b0406091a060301080601 77
    0x61041240c00d40700b20101c84c000e00920801c1c03100529459401841e03540c0c182c0260005400e0109a11618401c1e000380e035038005054080e0f42c101c5494440c1c10180b0305c000044c846810089965540450b00381254000030102c2c101104202c1030603028010046251882c0c1040c041c3c07883c11040c040d0208201810240014402064016805010700e6100d440b89030000c0490755540e4801c055950103074022040080040d003010041076040100c81c0b4401c0c10384800102560659480300d60441e015003004102c000f00a455146062100144000d44094a13180c050b00201c140041c2c100136080e00d404980c128042c3c0e20102110798211751014104140e010300311071069552500000415001c503003648050805043d00002d2004c02d1740581c0107000910704403050701d5040c0d5600c010403294402e4101e1203030300b40d00045000701000e40306812000c80003285090024840030144089021038880e50414901240d031040945903040c1c03092001340601d242200d1075841d5606260415446600610826a4250b00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 59803483 1250 59802233 59802251
    0x15070c020f130c030f060503060109050c071205040306060e0f01140607060614040516022503080310090e0f0307081e03040c0e0105010806061b0c0a090b0f060a12 71
    0x1e80310103410356003002000d1014442c0c51a42400060800365000804a443c0290b580300410950048100f124402000f40c42c0326032a1204500241900601102c2584810020300000a4108000d03a102540c5640c40c0e0352902e0462a08100b11204c0d03800020085803014100143e0321001c0c440b0a042d11800c513090440b5031075100124040c0d00a0001c02002035042110215400e006940b4480c0610400c507018480341c7c44980030b043d400c03100c007903070389006810800480f02110014803441c88504607404400390243d90300d4840f6011508203a46004000796501020050800180100d60047c01c25074060040c040c0071020241e40ca214601e8014540d0b00045042c8000e09c0030000305c0c0001c8007400e5406583d070701d094070340080b12070118000d00c0c20b100f0b250390001c01d0651040440300d1040c40d000d807040d45080c01c40003026078007011001c2c1c50b0500b4440c4625450b2961150300d0000000c1c9031003000480e0500d110360800c40c5d40b10f04a4403660181c2d0381800304401346a17100f005035116100c0ba400005100740 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 59804733 1250 59803483 59803489
    0x90a180311010608010c05070c060c020a0306150506030415061a1209190f0c060903080f03040f150f110a051209010902030d0c2321070c0801150815070c02 68
    0x446980181401d5103061b9400d08285c0e000b00003890198450800704604a032078140039518a41c80220294020018580c18800100280d00c810080c8050506c840016640c03140010020b40c01240c003100d00b901901c0760481c4908030741c014440a800502d03130912010a02d024450854003540c001c0d0039800301044d0211f8860360b01031140a003408444440da06102e90b450416a03868215014112042801004002491403003894050700f9240c0c020452860121a441d8281c802e0308090007d450076580c812045000a0260b5401750700c08081c41c1003c03d1717161111039180100c5103020f000640e200c1c010800c0d421410350201c100c600488d4064403912a039250301c00428010094820001c1d0075101d01c52358030700d807280c000011403001440b0b850301d4001c0440500f6114a82d5440701c02406403a40541451180020070b641f4081e00c040c09a10360901b0600203444c0c10003115519031102d0210396440d982d40c14141284241407025160b85070041207440413041d1418123869000307040328104400740500d141155 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 59805983 1250 59804733 59804741
    0x8100911040501060806100503071d1f08060a050405010b0304020907020a080705070e09011808030601020307020a0902030601030b010c030c17070b040c06020c0d080d050c041503050105090a18031101 87
    0x220300a4800c01042d80c40e5100078000d4103056444511070351070081c00c40100e6101c0d0b011641711703090a645440d0010800090120141c0b8184200380c0c3c00b106103403010044038002c101003442215242d4902031581803650520030384800c01c2d00590700031811724005100c11000b40003241d401c070350f0540390b04140da0340f02d620072070811942c840c00a109140000c0c0c640f051240c0092840b0a03105030500040303603510752a2409003221121200810b04840c2280c0000102d118080915403042041c01501c1c9044035030b03800615211595001007811030741c04424000b003075174548107a01c4485030a0a02103141d0380242c81c054211541c2490007010103407000b40e400c0b50b1002c08402d880c1d4982d408000183c0c00e0809240c00c001e040e0b180d015020061040c00703c82807040c80c0040101c00c800350000d2843d0b2a0a803081d02e41d601030000105240d000c4901000001410240b4004440d5600f0440d030300040c282d4184420001504009002086500d05281d0081c040094135030031500e4056150801da40e02d90b443c02d00d041d000d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 59807233 1250 59805983 59806013
    0x30c020d1b090504030e010903020d030f03020f0c070305060a060605120604061a03070311030115110f030705030403050705040b060d05060d120e0102060903190f0c0203011506030e07081009 83
    0x1034006000000342d5081581040b80124801c2e150701008083c0314004503403c108a02c0041d500c0301041030b8000c0070900668040c0d24210003403801520744a8030003400b200c075a111407071140055009101c1042132250170302c102d5400900e60603041c40301c02d18091008046000e108801c5000480e00303000300e00c0c25a2184d020000030040d014180e03000252030f0105003420341088401c940442c1c1000349804105940300102d9060b40c0b1081d4560f80d610300c00c090202c4121540007418002d81c0328048000112440410181419511503002580c0d0359040d46449420031100d42d0005000e24100b1140390081e540b13010640d1429440924002441c0c1d5030800041d0400c0d0b696400589203210303030440b50303c02541c840c820780d58041c2c0c02c1e002c07034410391600e40c84580d4130320482551b0110300c09244941d00750035114000f0280d20342a6450701054015a580001c4d08550884004a800c560070490412480b5018083c52125205100c09040d180e0300d068071a5840d9103030794015800c1156a110f041040000700b007150050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 59808483 1250 59807233 59807273
    0x80d0e0604030329060a200307210c0c060c030e1503090d0c0f030e030f0105070e09010603020703023d06030302151006140c010e070906060309030c020d 67
    0x15801c160a0143c010640d01d900b0b00602ca2011003d0398034405404913850a10710041c104d0b41c90621003c10861301c030704176815038034040d4110712034100852804002030b00f46140541c04a10242c1005c0311100c000140d8401c030f5100b40a480000407010500142801044403100c1c200003201130414039007240c00301c0d154240351350320288544100a100000c40b006c0d40c0714000080c1210003c0c038035402c060b245580d000c000244146c000e103a01800003481403c40c00131a0402600300c0302200601c0c0d03003840c00e40e603045030004009060044840c1d80723460a01c05590051403141030440c9010780321f417030094550301002c3c1c1c03403484d4070402803404600300d0301840022440c04c1059028811400e5090002002d86541e00c010f90040c414040320030f5134400d03084165401a6a47d07030400780c96901c3c0c1181a12001c0c904110207021070001e01440740c401500780a044601c2c0b0b1810081c100503820461403c0440d6101d8028604252600c054180060740022004840d240c041b21383d0840d95641e07160180c514800044804c84c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 59809733 1250 59808483 59808493
    0x1809020d0b010806041a0d0201020726060708091507021009060501330804050309061204150507050a030e070504090b010e0a050402010903110a0e070512010b09010903080d0e 76
    0x18004580c0d03800301d00c0811003640c5180d1591101800c1205880c81005541e18410b844c07000125149000450a60b0292041c01034694141c0e40b2405070071003000110007601a0b00b029030361000300900510101d41d0140b074a0503c0d00c40703400e00c14403d9030b03113046494607040e421284a010400036070080201a400f04143c040c140010285864980094a020700c00d00104006c02062008011203000ca610303130448e0b809815001201280004540c030050292040e40e036400200507035803603078071060010190f21489039841c01c082c0c2030030b107048000040441c92903000c0528240134441441d40c020100c5444c60814900840c801c1902c0c42e280e03051214541c040c50384645001c000e5070401c035403800c01c541211110004103c041e42c0b003135031960a41e041100c00a00140c1c1340b8509200054000c03120011600c005041960150b49914041b02814815075803040800d0011480d140024400d00e0307050b01500c2d0b404201414aa14a03002034483c99580c0001012940003051b100080d0082d80c2c0290209594482150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 59810983 1250 59809733 59809747
    0x6121502030702120406020d02010b09010302180a02070803042405220203030903010c0809060108030c0a1203090f14010b120604030c050f12071202030306010801140d02031507030615050307180902 86
    0x6995023801001040140d42000304d10b17130203441e0280700c1d07034100d9030064850b1041e44c5c803400d01c50620260080802d10302e0b0f942480036001142004000d180700e40d102e4169580200c9400b08162010380716403100e010080d00300004c100c1300103100c020501103107010792041c0042c143e42d44002400c5003e40e100b010b8156180041200c8142e60191206018884060a449199880300030300d54a900c210a8902079a5101c41c0c1e420002070043c400c03000341c107421894005106040c0d96101380c80490404019a5103040212084030406404c0c400d9003a104411030f05102904001100704c0d07141c4100420140901a009003d0014420309010404194030000107698161900c80c0600906400805081d540c1500350021082e41d00d0000044030300400d016119281b4982c0f0300480c8441e8401019040e903041a142c1400c480103881c10004c1d018004006540b40b216403070f15400080490b09030758080c1e105c862840d00d500b040140c00508494001ca89807803c0c4400300d03d49038202c40c41440a07881172121a02c0098a5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 59812233 1250 59810983 59810987
    0x206030f07080105010c121407051902090601180510020a1a1b0a120e0f071d0c03040803010e06010c020901030803190501050f0d1115040906121502030702120406 71
    0x15600c10360031902c481a107640c0b11401150141c00c1c00b0001005060054805c0d81d160b0b006a081244040c0121081458618555142424082e4425404490703007441c004602c21490440c0b91560f101c03d007860300f4281d103c0c1d00d005020001d1164420280599450007451013914801d01030304e000b003900000040001c80e24002c0141a0034805c0755074200f9200458480c011040d47d0004984c0d10042e2507030388101103841a040440248030003141d8040c02d11441c402400d00c10400d001c031000424141408800b00c11000c648a000d45600800d00341c640101002001b00060800c4241c03415909419041003650380d400300181e60101f40707624080d5101801000000410018900540c860042006047c1c0d40d0709109128605494080c014030798001540c5014040302d0900244408400b80501011109036a0ba500410006007c0340c08903800704400203014490a851070151070014500c10340310041c5003001c0d0301c8003903050040301c55502d1540d03000408100d0486c400c200340340080e0500e003242d56035207982c1c2d500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 59813483 1250 59812233 59812261
    0xc080604060b010509060d0506010c021e0102070b1303030c060e10020406110703031d0102030d060b04050a0803040506030a020c21030907080604051009030504120c05090916050603090703020603 85
    0x21601c003401c00d00d0302c48080d4070400a03244000030140c1020704160f01001154041d210041890741080351141c08600580d0720305041d0506c81c0302020840e96105c49500009040c100c07203400031031084074104124000b0803007d049401c00c5035010b02d030840d54940145030100c00341c40518403481c0540304010304002d0015050340204200c500a44510604e100450072494481049110180c0031034030150008444640b0304491400000f014410780703250008118a03c81180e6641d0000580032030081014030142c201801203a0242510781e0043d4201440c0200194035440001d083e00345a640200303420125250400034040d85000c20401001012130003400303020130303410441d05050248151800000c500d40c002c104180038907040400b40118051030f503518800740806044c101d04210003000000350012201040911712841507100c062801d240c841081052640548595201d4210080515450085100b1a42194819169280c036a0f42e0640c001d8100036160740702a4005100000b0058414400c0b00c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 59814733 1250 59813483 59813491
    0x80f030105011b050705010522030b010f0803030103050309060f04050319170a080c0a02070f0612050f090c040911030a03090801110c100207050a0f0305070308061203040603020f070c0806 82
    0x83c0d5540c00802212141c0b0103103140410207407803600f280e04184095482000203000d104002144501d0180225254580c0d091840d0301c1660f54141c1030005002045030100303000700a010440c01542154119101c290b01c0740b042001d094440c1d02c00140010f8100c8140096070700030718008065610010818040f03030010070046130101c8180705607011100341e04601000b0350740402c41f65503440c52156030740c1e02d5040c104d40c48600044194411440009000d101890744d0074003411322039580100072088024a241a910f018200c0d01e000f409070700410042c3c000001c1d60400741001240d0201b4460285d06240005213541c02c411a050300521320f8040030b0542001e803400c211034000c4002c0009144010103200ca0340a0024425082c1c1c124030318007103d4181d01d402030804d1500035000d840000310309541e90482130f04242402c03408124081a21818180c01400c2540c0c018010f4502d4404101168210f0751640300314020081455400b1900d00c60760240301082c0c03000964484c915482c0a500d4412103580c42d10704417 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 59815983 1250 59814733 59814737
    0x12020606040b0307150503060f060307090810060e040206090a080d0e01170f0f04140303010e060f15040603020d020405061308121305100c05060a230405030d0216080f03010501 77
    0x302c0700071503080000d025000c0307910442140c0015683c12070f00f29265800608595070080c03c0d8540003800b591400700441c028102612480151450a01400d01b8140c5c44104101c510b0700d800c004104018000102c5a40701d98111100c943e1100420300050a00d80c003500040014404c420f0001985074028407032031809007090300c6091111f14000881140000d00f04d039800e542949100c0840c9098011515803038100340300d9401e82211001401c0c886240d904264480c000c504880401d10009003420807800301c0284e8244da0821010810b6940e2521502c120300c80c510400d940029601c0e00d0107480e81c10348026000040c065592641000e110300314802d490301a618207030044420f1000814120b0f81194108407941e00c006460301c3c40c010821400d1000000e180c020b0040c0c2034069800a5014041c3d980300b145441c00c0024851401420301c0e840b000341500001243d440f210901021400001c20b40b50240080c0c440560740d89603c604403811310343c03000c000410992020a003100400c07002406141650000c0e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 59817233 1250 59815983 59815991
    0x9050c040225050718021c0506010c050307060c090e10061d09100501090f081c1403070809010e0a03080c181801030501050a0504080715060f0801060302150f0301120c031202060604 79
    0xb54030300c00228801c0788492070701f00e01c404124240007031580c1c2285034800414104901404410f4440740c0c01c0d0b0f0701c10402101e12990707c1c6002203616404c0480034000d407034110501556131905407641080c1002c1401040184007800b07280071511240c0280005c8400005002c241290414410001c10300b003507806824082820040c2c003040e4011040c3c0c1e04021125040020310a0842182007a034428144198080030400400c0440882113034070002140208400d0750740101c140361688215085030321003020804940c02184211010a6120480340e401070058000e29a48056a01d04c0b451080ca01e12040d03074200c0b49020700c42d048540d203600083e04980c020002446143d0350244088121241110000c0c00304006225420208016108c0f01c8807092a0020001d00342c0c1c2c44284940e1100001d61080d1b0540e91264018011810140141c0c0c001d02e03003540300c00341400d43c1a039610344d190005000c0c520b1000e1040514000340144151440010360300304042c1603081e07001ea4802900d4240032100540102d0130 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 59818483 1250 59817233 59817269
    0xa0209060102030c150a29040c020c06120a180b04050105070207030b040b180709150f060903080c1005071106060a0308041a1905070507060309050c0402250507 70
    0x4022503400c0c0310510040c141c41e409401c200d008102010340b18072889565030810303044401480b000e200c5007046420b900c05d81d600b01c41f4100410390b6188000c0e03c04641100618800346d0302d451084d0b0f070005015112020455a810100030010f1030392101e40044c06107130b144030394203018011b4622402580218000d0205540b000820713640c42e902c52100170800da1117807000a01217419080015044900003100e41c01e0703082c1d9a2445481c1000c030742c104042c519a5403001c41e501c454040d04010091042e9081003c0e202d00d003000c00341c91343e0420312014210040000700d03040104400e100d162243c80b0140f204008500302f46030000c11a845404488445105010200700c04e0b25184400100300c9600c00080c03407426040c09e10700300200c0584000c0380c102c968140409902030003c544200c0300211143d9481e41c480c0010705050b890052258400c0090601e0041442d02080780130800d107510640c1918003599600f07001c26186608440c156410b9410782c00a00d01100304480441d021046030194a100b180d9055 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 59819733 1250 59818483 59818487
    0x303051209030301030f02120a0210021f050105060702040e0307060906020909070203090d060c0306030b0408070302061b09040b0a0b0d09063806040b03040506090709020a050a120e0f0a02090601 85
    0x300070f01019204d1688040d001d001480c017156002d604d8840c1c80141d48103510382d907010600345941c050be02005a0800102c45c10000110720990401c2c8052031030900865140c00e0120303640d4411008082e0050340c035100c40d032042000030030031110010343c070200c100105001410410025001040100c0c0725002c0200410101c07880001603400300580107080c81e0828995544040c018031110118105154880f10000045005101c0341072003a80944200c59440c0410300c0e000b81481d0004100c00321050f50340b0900101c098252090300d0052205842c006140a212000294924690b0b03124401d0760500064880d070b000700c00d0300000d15680c4505002d0098508007580c510b5007a80c10911a400c10380d401d0103941c079024041803440f43d00305001c4e200518294803110f00c091642e100b11802c1d45c4641c45074040c030120742001c11400004112884045041015040c030040c002d109009005042101001d00c4a90043c00341c2c3c05580e818007808116000c102c6954a42d54072092440e2099102d060020006001c40d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 59820983 1250 59819733 59819737
    0xa1a030702010f14150a05060a020309131b0c05010b060406031a01030b01120b0402040302030105070c030206090309060406050901020c03010f0603031808060c0d1503030e1c0b070c020118030305120903 88
    0x2800ba51100c0303180c2c0c17541326001c6017020381080c19600c42c0300c0040010f0315446000040c250490f00c0d5026590301d1116205202c001024210064030031858400058080845036260201009281ca0305001403849410f001d030262109150450b4404000038000610a416038840308025043d1903260780080a503c0c015400c5074000c01c459808904c0d9481c0c044900900b541c00940c0c00c5200410040c01e06071030740c01080c00c4a40448481000c030740ca010b40307a018160100142035005400000561408040d41e020411900a0b0301c40c007400c0c08000701c1c1c0780d20346a00a0000f03184011000c2e00070400c1c0580c0c540114060b086500c03042e40410500821003061000103da010161022340c0002c00f0507481d0341400b5801540141c0026400940d50006424100d400c1c600303000c0214002d41d50600b040420008201d0b8400349460a9003901d0901c5410a001511028030a507000c005410501d030a02098001070b20407a200d036039000da1102101d0804000c054009000d0108a401031003000010b40c1c840620319500c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 59822233 1250 59820983 59821001
    0x1207060e0f01020109080d09050601084e0406030b04020c030a050304050a06180c050d020108061c050109080d110a0206040204020708070203010c02100b0a1d060a1a030702010f 77
    0x186542840100303a04001111865800041c800000d00018903102c0c15119000020344104194481000d442444001c001c1c0c6270240040700040d0400c1c0000341c1d000240310456000300c20f144007514074004059800410f1007100f88003219030400440b2021849103c00798010b010b42c00201c5d16041c403000140c04c00703100740c1c4c0911626400031403034249091000e44172504002c008545500c110301c9000001030860055001e07442000805213144c9140e454610721080a54203e01d0055a90501ca00c0141c0e0303000c1420340d0041c10030f0319002c0900d410740100050920150304042e05942c02d00e170004042100d25001858442c039441c00800001705441179080d0180300744860030b030040e0300c070f140464007500d019402444403511a244a524107081d5501090941d2482e0f03d81c0c0000da0000048911500201d015500155104aa54050302401d003e50603c01083c02c0200011320303160480010100d403100303203101d0b020741302040c100c600000d070002c01c4c54a198011a0840010b500b880c108140d6241680100810 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 59823483 1250 59822233 59822237
    0x2090103150b03070308090103111224030a080d0c080402031203090a061109010201060603060b0f1e3403050a05030712060b13050a05030703021e0301050f06120706 72
    0x4564615103a50614200d07040a0807080707699520281e03a03e80d81004004c000358401c9086503112000c560000d4100e550b500000051000108800302c0c6082c0030f0811990b1006408e014070b41c05402600061f04074080390403410387c0510a80100f0414080e40340301820414880410034003528512400c12980044159002034040d0300449181040071850006154049480341c111405480b00d82c40b604240d07205002410705840c000209190700d0b590a00803e805015581402d000e05032504025044030304ca000302d14940140042203421004801e80903a10500c5c02821003c0d8549251032406070352112003100c001d00300f00c1410f003485840f00c90ba459100d0415010340740c0702d041850741c69041e601640010424801c01c507000e0850310300491a8407072000a0b0509a00c15525014840903d02c040541c13600400c1c410fa000c2e580410903658002200408daa40c1910000362010b00c2d9070501c90b0340409011515419400c000c02c21507182044124244503140071280d080821401045180d1520700c58010600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 59824733 1250 59823483 59823499
    0x1602010c060b18040303180809010302090d0b151e010903030807020a0212010608120c030316120606030504020f101718060a09050f060f1909060c0e120a02 68
    0x55806020511400350080101040080940001460161035030032141c050160f80780c28441403642c14407900e05d401c0c0040ca1394801228541e1514841400340701d5059040540011303d01c07510784c48034800390543c254080d544240741d0070018180141000c040404a0055000c1a0000c2c040400d49120411101c4180c40e0303200560700b1520103e40181000344400f00f984a42005c100050301d401411203950340322000001100390a200c61541031a100c00300041d408a01806001100d440210880750010446004403070343e5410b1850a5922070481c03285800c2c1c039441d04000040f0725401d504014802e42c4216100000403a0907002c100420040b203249030001100301140401c1c1140ca40790030354000c075110b00c0d507400b000b443d03400051a1900440701c1401c12900c0d06408400c101c0108200b40350b0141401c0980703028513141c651003a202800400e020b1000018144002007401954000e095072900709a0a102d440203428000d4200c050504803940a0591001250004600450040b80541d4014070a01d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 59825983 1250 59824733 59824777
    0x708040c03080918040c0603110c06010e13020d0303050604050106080f13031103070f1101141603050405041b0809190b090102040519090f0203010e0a020a0909050118050c 75
    0x4442e80c0054004540003c010301c8514021000d01e654030780305500c07900c160781c8054281a030080550b4260440494402d1040c041c2a00c1041c0200364541035800040b5502d8859817400128180010343c0903010b9000080c0003800c1080c0b50b0315030031051244074107070740600c070390390b41c0700340407200010102d840c00d0324198180701042c0ba042001507064a414002d11780000c0c82081c00300003600b03540c48410100c800c0b8240611001c2000240000108030034001d0902c1154071842e4107200740d00348144e510155501d9400144002058000c409031000f40c02c003d0010004400f242c0801d5040300780e001c48030408602c060001403d8a20001017aa18010501c203411090104d980d84031104902c015020701550f54081c00007144035125000c207110844c80101c5503070043c1c0e240c1201c0d030048a80409208440e40d004200610500120b00c0c0c036280c12078010040180d803410250b008960418294000c032680780d080c1000010039284220002400d074003140030400581e258181a0041d80c81484039840c0050b1010102e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 59827233 1250 59825983 59825993
    0x50c040303090612151d0f0402060a0807050f040f0501120c02030a0e13051e0906070e22050114130b03070504021605032b0b0a030210020c03060405030706050708040c03 74
    0x10f80c0703801c103458801252860140c8011150541c15402c148105003240300c850181b01a45560180c04c103100b114007502906150700440c4040c45060b0086051181d1038020804079803107070b422944400d4280c03050a45507901c2ea000c0d81642c8030907110349070000c1c00b4440070042d106420300c141c42c115112500151f107441e03071201d8141c6400b40402074050b0300c0070240d840864401c00d98051544039610241c204281800204105001a80094007039003440d80000200524140c00066824036003004075000c554540404555129005d034109621900c1400c5c100000340682e4580002044800111803c20b444412a00360400311250200d280d5495800207504000c0c50902d6030043c041000981d05100ca4079603d511000c3c91a030007024841e61100301c42c0b003255088070f0041400d111010b545035007404448207442c00106404081c1c00040e03c2103421640138006c150080210081c8400050b050700c40b00c0c54a82080350f16504203034001d59884d0300b03090004102c60700ca0a05540b00c0d0740c1c001400c441d024219222 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 59828483 1250 59827233 59827247
    0xd0e0c01110c1020070803030915040503090f06070204090b070801090e030f0c01090b160306050f010c11030f0a23010b01020703080913020301090e070605030c0901080405011b020a0303050c0403030906 88
    0x40c4e1201003541c42d060105590052143c500030b00320901c0155603e007840d007840c41c9040111030446182103208001d10000500200c2141d202c1c80040310345204902e030100001e0080d03c0344506c02980646000d072820700b081101c0d0b0855114822076211034207980c1e600d460348001e0360607808210751a504204071014840025001405d40c6411803000000d40101955500b00b00600c1920312040030701141c0c924607407480e03140c01440301600d820b84440c0042c03200800060107080c1080b0004081a1403066860200d0b00e04000200400707c4101c01c85d0000000740c1090340d08080b82c1c1c40c0d092143d80c108100504000340c1406022007140040c0d008048051968a03500c4640d041040c150741e203c11503562043c2d904196001440c044c1418080009050012a03403a61424030580d01940503c4410b01c200900b02420b40180c0701000e200b030030944c490380d899182603070040c04c46003120425034401c0000c01d11055800100c8160710361107620308010a4a40741a1540b16000b184070050005910a00602c0002e1040c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 59829733 1250 59828483 59828507
    0x501030e070e0f191103010605030402150f090102120301050108010e070c080d05060f0108010302131a040504030c020a0e06060f0703050c060103200901051e01050d0e0c01110c10 78
    0x1510466078a03080c4401c0501000d8454039800d03103c2500703016409005601000003210302d02c0c1c04002248010704030501a000500c106c209208020001906544401349039020781b60b1082e941c6680d4007555804c003522030300020410f03030051090400c0518500f50800440e41a14816100c0c4e4409078a08039404044103401010307641042210203a40d000646800003602c80b4401640c40441da524210003032002528081d49181e0401031103400410251300c40e0704d5110f0b03540a502e0008124581c40003800c010060300c10192940107460007080000380350344580810345051007100d06d072003056600e003e4003070411010343e42070358060420080038413441d0b41c0e0300c010540148242803650030031030010845820010241c0c4291109100300c207a00c4000701c00040d0002c074012048520140c01d50400000c0b40c8411414004a500307004e141c1c1400c1c040da0701800c1a501c1c00183d00c001841030742d01d03101ca280d8070b5000701c4008070b011400301074080b61803400211f191100d2000c041c0001110600b0008115101070f4192 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 59830983 1250 59829733 59829761
    0x50712020102030c0316030806300a080c01020403030806030304060806011b0204090c050a06110705040e0a0506250302211f0906080601050102030c070603020c010f0905010b0a0905090304050103 85
    0x404d4000d0070304180040c100ca1070704c4200102031040780342809040c1ea400201102c0c42045440b428084c104407449151486411400c072420200707001c0e050030b62030641d581d100604003100101c1c0c03030624200150003c0c42075910980e54000c213a00c415043c96034a020320300450300400c17154000103515510510300c600c0040301d03014210203801803d40104080f1030060b0400e07182600c41060500c4141080310a10f0001c040914051030000040318103640c07200c0150050906c00e984034003400e07042d15001c1141c0070f2030782e405c0004c0e2401c6080c650102001c0c4182c0e554034030340800f41c00c0b20318004c0c240a0303c20340700d55901d4400301132003200941d0340c1000da0480c0205200d4148090762240078110b102c2c165240c0c05442e070f0810015045003000000303460914140c0c0500d045500400062503400301c00705141c0c080341d01604000d40c0720000021403c1c0074242109100070064a440394a0090180c15042034481c42001c3c0d56101c40c00303848160400a85008541002e01a8820002002554407070f5104403d0b5408039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 59832233 1250 59830983 59830987
    0xa0f060b0412030f0e01140c030408010608060a0b0604050105030601030b0a080321090f0a0b040c1a070b0604060f170a02060a0f110a0312020a1b2a0305071202010203 73
    0x18600d036000ca604207400c800c0d055507000c0e484000301038000303040c3c458901d071a09240e181c032500c40d00020303c1402c1010a0400c94600444c5015009030700700151005454005c0003485056140e400c0140d4644040342c1c01c074490b03410081880e41078100141100c080d0b03801030f034550313196a07610710054000d0860980221b81010300c52000041031203060020340301c0400f61810803411300c04de01c04070b00050480580b2080c5c81d500901072802c94448009003542e805940b1020140c02560b0f079007003003140d0091079444404010901005445044503c0c80103044a620a004c1150b0680f1000c0901c41200c1c220b00455035401c401e003c09202e40141071940c900c2c3d544448041300c11030b1250740d000c20a03a070420300881e804240003d16a000c1d40340c1060b41c8140328060440100940310b510349001f03100c90a084002c50310954005000c880d51441480b640e0108490000703013400b04291860b066008500e100c096a040058070700c828400b20301d03401381d0041241d8008000b080e0f0b003070908202134003000c6104012810b40c841 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 59833483 1250 59832233 59832239
    0x5010302030903120403050405010e090603030d0518010606080f01150807030e0a081c051308180a050303220b0403080d0b040605090a1a0d030f030923030d0608030405090a0f06 77
    0x4c0e80760000d01c114402d98409445a14240024111040088466124540d01003c009241e10000113880585228660200d40354035100f80107102602c400581d0071046d400c0003404103031203800c644403e00800480303034100003d030f0360340030b150020840c0800444000303512440441c208e03c3c0b20741c20407403041b43e1050a4030b4222200d40c0d110680d0794480c040c580c034000748506100c20301e0304443c0b1400d030748124003040044034080259500369041c03064011004c81540f2040c00d43d400e07070b2074009041c400340c000a01120303903400040340c1c1c07a101d001c1a0f50030203500800e107400210b4172030041c40c151800c40307500824079401c284440030b101016128514500c1d8005035240c0d4000343c150789a07410b240c091442c405001488604652145803091560000180074540081200d00082e50180c0c203c10340e40c019180c002054800c628000310782c0400f59012010000c6610070840e081a80030004007051070089100b08687c0d9030b61304a55459000d603200d0f0f56404114040000c2c7c00c2d039602d41000d2546440711100084040e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 59834733 1250 59833483 59833507
    0xf06120615010201060b0d0603050c040203010f030b0a200306100207050d031d04050412110a020607020904060f0f0f050609040b0c0c0c13050105030d0e061b0a0602030414160b0405010302030903 85
    0x1111091203001c3c0c8c0c0b10401082408010f02c001009610199410f61956040c101c07907650754103851100800e00e030101400902120115440f000c1c0800007240510841018034074826196002502c2c0030f84100e14060750050b459000003000412204084c0c241250071600c5e07201502c0300600d00d04000c200c08800f07444905c0a41c1c1e02e04c1440c2c455071207501c240f800c64045000003031104890010b229a15406501c0c2c920140c2c0d01c030401d8800f4554111400c0c0350030340d11032070413001804040505150081c2440342e00b007400d51580c2c11a041d0300105a008020a9407900e04004c0e031118155405404841c454010a5401c2c2c1c0042c01480028920030844005080d09000702d614001201c50364110b682d40c2d84014011b42c541405030140c6141c65180814800c0d50f000700050382c45c4210303000b28100314080381c410b4111f42e8041c84191580c41d0020000c54503403800e42001c00c030316080800440300c0e500542c0c400281042d58007211100707980000c0d40080c00c040c10705006400030760016003079500d148014400c0d102962 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 59835983 1250 59834733 59834737
    0x4020c030d0606051c051b0901020a0f06050105190b09061612050a030608011b030b011b05061503120304020d030c0506090106080f010216060506010302130801050f06120615010201060b 81
    0x8006552415520f1910016841551180c6005e0480d0641010148011030a10040c0920404500320102d1380d20710500c0300503452301498070b400410030b04103682c82c1400e100a1760700c528101c540554560000030346205813481100d03058000c500c207031842400b2580705410080b014054020400000c00c0404a864840154103454118004002030b00003a41c900795a6040c011440200b0a1000a00221450085400c0c2440c3c07129101400c059a07034419007000d03840b480890f50400601c17103010301c1c440e186090013510788408890740d500b121094100d035009420006000c03c040032040041c6030854035507070301b003080c036103110b090640420400e5003e0390080740342441624050748103000009140c41c40d01c2e0350349044c90825040d5881c5a48180070308401c61070001c002034001a0301c071400203a01c0d0b50f0500160b00031b0103031039180e401c004240e1001141c85041540854001c200700391142082d6130ba0103003000fa100e88a60210f648030340048003c65003206164803000c103884414000403c106840f14214541ca03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 59837233 1250 59835983 59835989
    0xc03040501020f0705060a0f090506061002030d061d011e090b060702060a0206040506060f03100e07080312070311180f1206090a15060b16060f06120615030b0604020c030d06 76
    0x186d0070400030f0002c410010721400240c1f01c1011400d00c8010b120752222919040700a1030307140103550841e00003048030300c21b2040b03a103241d000510801030580c40d10101610276590b11144030480038594000704031006622860a480e0541c01603c294140c00d00d400003026108580203140c000d00107210400042c0c1e195070141c1200b510356401001c840c0340c10300f000ca1401b24054007143c061404800054041e880c0072404e0f2144240500001ca88240c034814031a191100541c40034103d8000883c481000040c82854140074024982d01400340c040354040300e24084c841c0107155000800c003541040c4840c10b1914a1120403503008041101401c8200003540c10441c08464404064100a4211081000500301d41c103007205048000c001007030405e03d4085180c071801041e5200038140c403101da01004069002030100584020050207401c0e9101940308001400860440b2401c0c20091010108000a03021004594002d4800e00c15a160f44050000a5210130b14112090100700f0101045070741600a600003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 59838483 1250 59837233 59837243
    0x20903030d05061e01200a0807141002030c0406080411040e010e010c08060a05010305090a05030403051f02181306080a050606090601050301080a02010807091d06010e060405090c03040501020f07 85
    0x560b14000d800c04c050142c0400e008409440c0b5001c80d0701e907a03644074254000441d62140001074220410b0340707082c500411580d004103c10b40c0018803a0821500385540320100303c01104a58007103520140f001e0907404203c03080764072b4800a00041040504c648403094111b03018640003444010010041411741d000351101d030000b691100e130301c4048400d00744281480c2c921a8a40380196040c84000540100300c14400d8604042c0c0b520003240342e00c41c051200d0038030070b03a202040b03a035200d59910382182c9074011505c4c0341100700101e101e180c554101a000329450801030718150300c0d00c4000c25042000c0800340741c1c0e110140c00d039104004107842c04100100b11405001d4401030020346000c03000c003c51020010216810000244010001d61400152400001b542401c04560958441c5000c440c55444e81c0d000d000f9580b0069056070811800750642e601600d003ea8580000990500520503140f0644c842c072030704080450000f409250401c80a503801ca4840d40015107088045802c40b12550801c25056071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 59839733 1250 59838483 59838491
    0x60703060f05040c05040b070507170a170c031c020f070803040209010609030804030f11270105030610060e18070807030605040504020618040b10090303090e0c04030f06020903030d 79
    0x40110301075006070041608a5080c410b00d11440c0c0020018016071260603000800800c15800b0481e0a0010201401d1b040a80310903210030329040355660340c0305580075546c600c0c2e940d800c060160740b64021200070300000c00c000c516191030203201001c9880d0303024102d10340603824050403a044c4181d00060884600644c08a5101d0605004011403020180e00c40c005100507041c0400000e0b14850070364003103941112071b00c0ca8038100f80c100f10090000e071a4509a00002c0b42c1ca12480c104034a02c2d09641c16034141d02810390913a00c3c0c030305140da0f40384259210000f113001060100840c80c855038544004940c0645074404c072500700c1800c0841d111054546501250a803010854426031510905004003c201ca0502c06410240c0100d03510f44160a0810704441012940075038988840c4c0000c0214003029001d004038140c0b41d14024240c2907640130840c00640c0d410400a0850516000340d40030f44e17603c15645182a01d1039552880750101a18103d58180c1c082c40303405c0d0159400d0000e046021403015002c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 59840983 1250 59839733 59839739
    0x50a0b160e190303050c0a08070b0106020609010b091f09020711012a0b04020d020a0b030a0c03020c060c091201060e16050a020d08150306040807020102070608070806061b06070306 79
    0x20300603005a040da00c0c020b80306a010340c900c0703201d03003100301d0101d0f601401d1003a5181c107002242824901144070151541400007024000c015201040b54100e811031b5003504c00d5600d540035540d01343c0349429503d9074000e90341c00110b00c000003400380210510703803252036035101130790341c0c52403641641c2125006a0742859032070a01040c55800c481d4131040203200303038000251056440035000000f40c1490340507081242c40b0002400715162500320001e255002002071103400d94505100340941d204a40008c405030500d02c1d940c903298024001c0d00d460074002d40240070305544400b600392a5400c080c807181e902405e00700710000d0002082c4140c0d0040c01c1d030400c040c1c5503860400c5048190001411464041120420069001b541e01061102181c3c00c189030219640d103540841c04c0307114413450346d0742c1e6150003980240030800c0b12500003461914400c0e000d943d496640d4290039070712054201c03400d001150040c000582c1c68502030b0300070000900003040710f030f01e03104002204c41e29103142200c1081c08260b4a034018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 59842233 1250 59840983 59840987
    0x109090510080c01050a120b010507050f070305010c11070306020304030507021305060f09010b1204020a1502070e0f060108040303090501021303050f060c0405010903020f1c03050301140117040807050a0b16 90
    0xf000d034002800c205103004555a40101080c1042d649000c826544000c00350050703100b54125114140c00c5400c42d00402e09181c4455154030302c40c40200d80c03961030b0407042103180d402440c000d0500707a0154040d020092950711120081c1d440200210104202044035400590b207040169004032000e500004903403404c0000e00444a2030681c1d030390310a071200d40040140c07444540031526200700449618900740c507540701180358400303a41c0110240d0600781034102480c40d40003c0d10000c41e04422042250707922102d44e881c0c552441542c045000842500018021a0017600940150741c42240010310b410511040180f8401d45034100302c800341c01410350004200000c01040b078100701340c000440c1c43e00b490200042e01c8c5081c0b0742310080c0501d0030030320102060341c1c5101551030000703d0848016061469460300521503032090245101409503860b240e4645d5104031203001451043ca41500c59903203850f1102582500b055200b01d07068859640b032000018169590740340079411400c20b005900c0420200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 59843483 1250 59842233 59842243
    0x91e2106010806190b0d0204020c010c031805031204030513030309031109010e06010c1b090c12050402010507020f0d020a17010606140703080903041a070c270506010909051008 77
    0x200c0e80043c0d0002c0e0a1141c0000800488582e55040d00400911001090040f440c2042080c0c406940503101058000c005001900300c1c00c1480a039540070844914072007100c1e00049540c0f44050160341c002d00215100c94005400150494001e0501c1e500b400d240104219205140c1c0e00b00320001440d1601c10003c001d4245c4c100580c111045841200541c1031100318249080014040d90400550300b810109200840e0701e01d0381c01080b640c10680c41c46807150402d5020b484402202000103644901e803602c07040103803040c107009550582d1280d142c41a607408005445c0e400c0c40c1056408411004040d00590b190407a440c01400103a486401c2c81c420f0b082c44608482107680f10400344041e503515807540054043c00c4411407581424544a42d0b190040001c1c07860086801022803403890000362041d10640d50083c1161521414941000549a0802040c1300710151f50031222440d501d80e40362a1035540d40c005a900034418900b1501d450350f100a50001c0c0c5d0802c0d10032a030001d01c0f0744024420b0a00a101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 59844733 1250 59843483 59843489
    0x8040305100609020717180409060c080603060f310302070e010b0406050702040f060807080a0c06030e1c030219030203041101030506180a060b03090f0f0111091e210601 74
    0x3d811824803103140c4a0054940d03503001301030390002c40091062807400b2611481c85103d680a40100426803240c54554000e1203000c9030b40d13010881400010300c29282c00111940714130000c056020450310742c401c11008146814244c1c010000382d00414902d20502001c046401d170340241c0c0100712a920341945082d810304183c12840c0207590400c4240000c94020045810244c1c0c1034400040d90211511a040144a1034102034140c0c0a80c0e10b001500c00d4000034007908450040e11190100d50b078807141a001c9a44614004840303421854659041d20035010a050b03c103045030401514001e44a6504e130540a9806c0955020a0307010050005014202c07400d9890401c0a0a04000320300706000083e5a05d0480020844962405c600142c3c807540d031034014100511a12101c0354170b84c184904201e8842e81c0c003d4a0025910130005c2c01b04500300705010b100c005900c032402451074160308209102c04658141061307c0c2c0c01e5495070101e105a00d4104209202162201080004a0308880524101039040e8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 59845983 1250 59844733 59844749
    0x90306020d02130f0807030b0a06080106030f05010b03060105010813050f03031914040201050906030406090602041401020d0c02010905040e031303050c0108070e0108060904020409020d08041706010308180607080403051006 97
    0xb0074045c0d0708000400c08140c9401c01c1d9800c100c1c0c5d0761143c406014050541105c03034103508100700001040b00440c9840b0043e80310700024003d0414110030b155881a09104050018501c1d501040503034000900d903003403141c003402c1521000009030045903c0c690050700c8000310581c0304048241e21a555108480210451b804040c8407070a254000070000d010f0482900d03c142000804142007004036030002c60120b41c4040c0035900c0f20750798043c4162083c90402c989000d4002c00607102c1070140f03d416440030300d6605844500b0064284010710004021080500359584002c10035848003016682d08140154440c00040250180241c0010041c1707001500020500144407601c0480c1c1e070304080019480842652042161740d51400002c002c0c100d607003006500030000c4541e0206001c003190080c4241c5002c01800c5040e0408061055666502403002800e0060180080d10f41d45c54140751003030310040010150760071710340141c40d10b142550007640111059444090100e81c00358850140a0043c0074803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 59847233 1250 59845983 59846009
    0x12010c020d0f1805060c160305160902070b0103080d151205010c0809120d06090518070501020304120f06060305100218010c030c030f030609140405120306060a0f090306020d0213 78
    0xb2030803d146040607025030741c41820b000c2685400c2c41010002d4126140c043d4586108080da02e05245440b8a003032503d050b120580c0c4e80000c00e85c48034078000c0340e8610b42c0c48902c12011741e01e11384454580fa004050350544c41030700d070507402c0c0414000003c2c0c1000b6048544100444104501e002801c40c0e107500c52203002d1191290800c80c1c07140001c1100c0760385240c284982ea03a074070a4012180010080c070b4201d15400c524017420700490715240409803e14140500032a20384175180c000681c2d1324011841890306011010101200240180c0281998588030380341c007050040c0c40b56101420009585a4810215404200d0f00d03118840710184243c3d51600307007081642d42442c4c3d20010305118002601406006c030b84101088401c0c465408080100100d90381001400700b243c52540d89004166000e0b243c501c90011584001702c7c0c040c08403030042500804052030248010402d80c1c03002d180b0010b8000f4403200d07150020108406000800054079010001071b5240d2450040e61074a090580006103d60b0603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 59848483 1250 59847233 59847257
    0xd030204210c120201031b020c040c03020c10020c1603050f01050a0606050301090207051c0507020306090102090a290f03010503061602060114041508011e020c0601090b12010c020d0f 80
    0x44482e00300c140c07001d821039104083e4560005901401d0711584055880414042c6410b43e25404603850b9442e0714111000d0125400ba03427400c40c26401011a14038964000c5240c0e110354444039030040c000a42c03044240c441194450500800c2074106074020744160700042e004100d061070030703c19a540160414401c11440b401c00100620a0205014010340141d0004c1c0c90b10500900708249010b0503802c81008030080e01101d0010200d4100c200101c0c00383c4030f8240441e414803c18002e42d0b415520103840c590034075252120105100d294039040320072143c14111030030040e103140c2c002002d2400d442580b480e07a039450302041c1464040d004100460b02c10307059920003000c59000c6500c504503034444400e807000c40f41d0400050000c0030101e000500c00c14540c3d40001d807484e8103410909186910401d00300b02c1d10742e41800f079021ba1042480c5281d041e001600180140c10f09980a50003158000c0e10303c247c0300d000d01654a00f100c110200b035074003592052000950441c0d01644418110580d40380203061801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 59849733 1250 59848483 59848493
    0xf0b030c03070f110a110a060801050d08070305130f18050603060f090111040305010f0506011e03050c0d2406032a17011502011b0f0f0e030d03020421 66
    0x540040200f0222696200d1440d01c103078140c840200ca2035090311524111840c5c41101210003d600c1401030880d0400003515031301541c0d6090480d440540380b6850500c2694a8410b036920180c1c1c100e0621030140481d03103c030040411184060b180c0e110882c0103050030010914003282c0903440c940c2e607060134001041450f480c04a040c94110821200602c41500c03168900c9000d03100541c0d01011900000c1000000d0090541180380e408044070010171198544900445013250b03d0f010720080302d580e03041c0905100f4403da100b1544605000300c02c03403d2404140c107001c240d401d0201404041d20344005201d64821980c07660000915540c2002c001c0e44800e40200140380354000ea12401580c0043c5000340154080c0c04c1883d8802d86030a00c1c540e0b5903860729030601d901003481c1c40b40030066181c0a5540080f010300034000814103c1500e840303034190000881116003800bd0088002000305410300180c403074800b00300d14821040e00d510050f80315030402540640e50300040c240b1190fa0b56880422602182c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 59850983 1250 59849733 59849737
    0x6050303090405060a0911092704080703031104030f060e0607090e04060e030a020601080d0801030312050a06030c060903030e0a0506032706010e01060807020615010e1201020c070f0b030c 82
    0x410b84012809580380000182200e0b0b40342d210342d011340d05019103a0728a40d43c0000500c4c07400e50803100c01e4404007038040f018180c0c00302039a070600c850401c003010070080340460002d40945407182c540401e40d01d1151a801c034003a0000d03402101c0107400300d0340720703001c0021300e0203100f5050100c0002000d40c0c2c906200c008042a2203031243c1e150280018000c141407040382d8200d620040384a0084a40e601e5201030005d6403103c00b48100d1606028440c803a100451160850074104c0f90559204103281180c600c4220040c000a003a5800c2135030b84490000009040700490070080005444190400b8550b04014154a01c5660310740d00c600b000c14000d00c05965400150303070b0440e04403a07001c01c074008880103170103030001440b012500320f115000000410755107404060307040e100d60342e0f201a51501d907030704140e035280380c00d0f1070307141e915040c00e50f42d2030307580d4440ca0180f8134031100201084075080c1241215030890344207241000c07058000f140240002000050a4030041140710b81c200d1441c5000e180d064464 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 59852233 1250 59850983 59850997
    0x90d09060f0216030b010302031603230f0d0201020a0e03071203080c04030b090601171b09060a12060204060807020a1203050621060103020108090c0312030c040305030c06091006050303 81
    0x20005a5500c400400d108100c8030500c003c0d14001c108155841c1d0500c10303c8842c092200b20301c644070321551340e5045928104858200c0f580900d0350b0146002040c2881200803034808510858860228107000d00001000003481c40c5074150001641c1d00480000100ba03654000c640b40d000794001305042005081005160402c940c040c0742008007515100c84200f400d06c1a6480a0074032aa90810710035040380210703c40341219100707403040021030448080c1139210038610190000c0000c1d6003444600c076040038124258492070040002244544070203400c80191120700c0c2c143ea0003940814240219504174070400c0c2c000c15640010007051010750344408845080c0d0700110105071302d0b000810078a4844a10f500340c0b80c04030b9031580308524030310100c1643c0d510017440181d000404d0900455030198001c50081502400a4054446801c00d091200040e520181c2000c094490030440040030600600c00b504101c50b100000d40b09600b0f10118180c944040300355807482e02454158100107542c0c0010442e012 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 59853483 1250 59852233 59852237
    0x1208090409060e1608010605041a0d020102030409090506010812030402090103080d0902040603060b0103200403080304080f0a090e09120406110f030a03140a0c050f1309090c050405090d0906 83
    0x1016190b00e4041c014003032035040340059120300d01ca8a184c1ca9554440401607900e5070008012250b5500100410350b032100c2c40c00c503000101290003903118200120100003a40c0180100c83c900350303842e10114201c8290081c195090303040b01c001070101c10390038480025925000141c49003181400e4001800c1d80e60180301c020500000061814106d800a411000c90503800820401c0f03100da5909260340a00250741030351b4002480c08104441080c90240c0c052911444068510705103411a45c6000041e4405001500d5210061001d0041c0b61900b90040200c1c090656030010300600d0030300858007041028001d900c55401000540e55020b9109068a0840700ba902c0c0c46d00021b0b40c0310041605103135152001540c1c030b001c00070308482543d8058115210f001034440101070719030340300303a4103508079080442d00400160041040e203444881101c05000341c400078007514110725507640b401e801207502c8028101d99038581c0441c00c00461815101c0c06a2010310b2102400002c2442d61000706081414024001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 59854733 1250 59853483 59853491
    0xf0601050a17040f0b0601091415120117060901020c0c010e0d020d061d0102040b0403020603040311010e0d03140f0106201b04061712031803121012080904 68
    0x2204520a041c0c229401c015507000407164200f0b81081c004a1079611419689000e466012400f44c0d48601c1c0101c044402c9809072000705c4064504100820b10703240f040600e1020140300c0b406000c4580903580d4000c01c02c088415804862a280d910b06001d0300611101450f40705000b0004040c401141c15283d00c802440d0140e11800f25000244120411800294008800e00c852604005903540b00e107107402800707900c0300c10306081e505070a82030f480f403030140f41e013180000d10041005082a40145420610900340a417041c00e482c0f071032900b1a045030200301d4055110b0a14034900c6601842119074250f480248219180b624a6130340010f10818810801003106451003401c0402030400d64203000c600d10b4060341e1928892007419130081c0c10041d5441d101d00e151880004a50f05141010900310140d00007801e00a2000c1c1d6115400e83c01c001c1c030216041603412010410200e0a10040820484659901455003007004440b0901c0c2e000344c00030852102d441c1081c40c0416219000d44000c4e81c2d0880c0c000c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 59855983 1250 59854733 59854747
    0x2070b09060d020408010c0c03020105010510120e03070203030a02030a08060d02100c02040b0a081c0801080d0e010e090a0507030f0506060409020c07030f080403030f020c0604181b03020403020f090f060105 90
    0x80d009101d1179010007115413914004103110b07980529080070490003503000744196600c45007000081c0c1171141400e804209031040120102d000c2e5003001421071003500980b8141215600840c1c21030b840700306810016000000d10400c200e03040302c2e00c2c4c0d420902c00c1d55040c0d0220060360210300034004600707d41d0180304c1a01d4400d000c5580d1908810500f04014107d41350485d0f548640666600d20300410003a8008244001c10025100c4d0030014106c1c0c61070402443d2040e00700f4010390300e580c2244209410007001e9210f0340d4203a2102000c09000e10b0440c0000030301c51410140080803034400c00301b080301c424148010f01a8540e00d8000391000e41d0628140143d032402e52441280c50084541e00040202894030f48074001e000c081000340003200d00036100e40d44400c881007000ca840700d444984075580018103001c01d01c440220580341224180c0d408200080700300100f540400e4038498502c076100082e40014081c400c50505601d00d019107030f400d4589801c0c3e4240704040702c80c0c501006103401e04201c4042220 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 59857233 1250 59855983 59856007
    0x5070605100302150909010503011a010f0903080f030a05130302060a1508120c0f07080715120e1605120706030908070f0b0403090e04050606130608011503030306050102070b0906 78
    0x40c5004550041c104d9803000e04a600c02010b40d0000e45a0a00c50511400001050300f8103000b03c0501c2c40c10382004054804c22440155510032504141c1e00c20400350580110008001d0001030540e81c03456a096902d905d4820400b100340e540c000c080036498030b00f4048410010b50001041900508502404901d038945041450108000c0364400c0c41548503290844c00410001c030010203040d07014900ba2445003a04089840d980c00c410f1051107543c0d802001c00b08000a042406100c0300c03801440c208412110461050054412500e8000c9458001301c8107000f20100b401249001000151403045401c006030552a480e0003ca101e0071041c140c44403640c1080040c400200c0300d59550021442e04400310f00d003440504101c08841c100c0114502c00c00101d84c01c019001010b100ba82d00c50020031460b0ba412040c001958081c89460b040c245d111400815850b10a0250364407500264030112012459400c0c01025070b0b185a00c450f0542d00042d10a0240510000c102c84c0ca4000c00d541095480d1404098 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 59858483 1250 59857233 59857261
    0x6060a230d06090501080c2e1b0c081e060109090305040f06050a0822030e01120c020a1a01120f0213020a0e040c030b010e0d060e0d05030a050c070305070605 69
    0x44a8492400c0000310b00c2c0d00f01c0d036103c20305a07020503007100c284680d08014014000c100300a070078002d40a48200700c58080c809000108031008526140c811101000c1c0000c1c00785800490445800325491406e010700300c1e08122054640302c154980d50403e00d11501317220344400040c000e0a52003922003c0010606018030115030051030f40c6802038815595071300e40107000f40c00808001c00060182d2012401104d0b03e004480c2210b42c00504000c101c905c0ea030380030744010710714181c01418803003072003043c4e09150f00a01c640704100310a0b4000e4403801382c2d1071409200030141d200145001e60f1340000140120008a042c2c210903583c840300074103c5c66120300002d5074180712025110304442c000102d41420300c0c0e01807910815020250340601c8107051040040c0d050b41d034140303d03750004500305008106880d1100c10070800714001c070f00010302218010780d65800c1c0300510061101248001061002d0494039200f09e50380310480c100300c181452082c0d68010580d200b1801c0c09020b40ba100e001085180007101c0e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 59859733 1250 59858483 59858497
    0x150f04030f020a08121201050406150e0a080105070201020403020f1801031e0804381c0207080403060203060901060c0c051005091011010b010801050d06180f030309060506060a23 78
    0x200300c40c2e5260b11918540030360740c4146c1d184840a4228800041c0074101405aa800d60365886103220006d010503508464102400208590245845400203200c4500703109460080480d58005a90740b0f080d03005214440580841040c0178084d41600529002d0070024044d055a60203005115211800c001043d0641700442c0084d10720540042e000403040c400b64200107402d000101848610210301d032001ca40c0e041e0010301e020b0414400c1210050500868109450840700000c00500300185502c80c030125411075081100c00c0c540c00800d000562404074450f50051101c2d00e42508402400d903555000300072a441784174000e0481c85440c882c01c0d0301850644814960141c52903400040d0440700412991344401303841d0b8994078040000000f035104802141c10380b20003500c0000041026610030004001e003402c0c04050420702092980058078564103410403500075940840e481040b800d0010032505d0141c0120300c1207104012584400380c1000821265070070703000c03000c0d004141c4c4210b400d88500c1550 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 59860983 1250 59859733 59859749
    0xa0203071823120d03020c0712081b0d301b1101151404020c12090a06080103120e12100603060501051014070206070f06050402150f04030f020a 63
    0x600081038071041d44110150902800e02240018a0b10506001e8007084110708031290790800c0900c0c0700203900035001803203810440c100701c42400350b480c00a04000e412410b011a9030b178000069000c2c0e107621030780c403412a20344418080c07ea0300200907400303012a042100f850117584010310303042040c9881c01004c0a2100070814003805903540301244281d6001005075100086001c0000840c02c40b58144125402400320b4140080c010b406d21168035401a81c074129a03230300a0b000c03c00e0248441c030600c01560001130085e105901c5050342e0003000740e8070034160028010088808010004294807000c510020540341c1031001c101c007900b0003c181c01420314441c503412031240004802c003558082c0e001c20200c0303008400402151742c85038104020100890400380001380103911848003080707864024071925100500003403800019517a030581c1002d11315010345482d50ba4004002c2907003881703c0f6440300a0320500000340380502d5200d007607059006601025292101c90506c1200315200e00c01e44101401c060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 59862233 1250 59860983 59861027
    0x5090702010c110c01020c01050c0a0c0e01080705030a08070b060d080309030903070914010501050a0215041a0a05010b030c07030306080a0f03090f030201021506010c0609060f140105090a020307 85
    0xa5a000e030107040035581810020310403062200745800081244c03241e800050f80905012030030707800110303034541150a0210759401802811310004003103680c480010115140304004a61402a880e42400041d61001c0d001e40c00c0001500002100740c000c0358800750b440419245039851303540100f591a4440782d8018184440001804051200007010b068076010880c103d0303a11985850b1442c090b100140a4070b60150091310040c8070641c01000a04081c05062045801428008501c08960384090f1802e8581000d000c0d00d61100c0d01c11b0096580d03225440b9802480254034044c00b0699500c0002c0013251512000b00d800c10805100b07400c018010a814000c030f6240c16101e003405c0b0141d14000100b100400c0707102c00d0020310890f2070303410102166016000f514081000e4002040c000000030007603410450024020f8000031124841c080030320f03008000004040c01200d1b01c1a0071241500d600951a8000400401082d07175081e01550740560020310242c2c40c2d4a408000741c4211610b0b19120103020300e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 59863483 1250 59862233 59862241
    0x9020a06030605040e030c0c010e030307051507030e0309010e2704080301092d1a060c0601030302070f03020f040b03070b1809060607050309090601110d080f160f14040509 75
    0x410b800c00d41c1641c07012a000c205003911412160354078810041b0700221038220541080c07042d03006840c042522030b00601600c0c40c250065640034102402c0502202d0f0b5080250148009a1f6151203110602003614005610b02580e08001910510525020a01c0341104503403150104103400083d0100c00900c1d4034440b41e0341058030380401a40c000340a08503135036140070340078801c070401d454048610561203610903001e4003130350b11500007420703c0003003850700c03400304c000301c50901d4407403070300408001d40c031f0101422142d4150714000f8141801980001d101c000108820300160340c52402000c0d414108980015141c404407002c203041042951000181d002e0106040d0f11502c0301e13a030400b034a03520880340072000b41d80f0340e400c2190034020035401500580c411301c151445410b000101d260051014107265a2140f507448801c2d180040d460040720020f100301e0280070380c000319070350059042007204820111020b14400020a280402c1400104114410b110001c1540004046402074400507225051500e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 59864733 1250 59863483 59863487
    0x40902030a110f0409090813060c020a060807020327060301030f0b01150806040b0d080d020409051506031603020426060633120a06080609070e010e0a09020a06 70
    0x32240001e4481c10404144840b18989040320400a80d12001504003414100890014403048604441e01c030380030000b07060b01c82d0300101c0c0e0100508460750f40403480c40083c0305000704a403081d0b02c0348051002050511111540200555507508800c0707124540011085100344c840121009000c2e412200000002c814860030400080d0594082c03d1048001e90740c0f50500d00c2007040881c160000640264040340c014a0a5007101c0029100280058000c606580342d00d50241d1240926a80d800c1c1e0020702040b441d031050040580c41020b501c884040480d00f400420282c0c4401840b18448a0341c0c0d032450f1542901990664025200c3d4100c110509140190010810080344020325094410344001840510301301032440080001c400f1001e040c864818000d004000004800100380c103001c1c4914000020484074071841101e030900040b40007841c0c50009401c162010340488410740110700240306591806682c281110303005580300c981e030350318107018000611002e031000394040c012280c00a41c042d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 59865983 1250 59864733 59864737
    0x405100303021209010c030e030c09010902090a0605040b09040506030f03030c130e13080d090602030907090c0c0803010e040c03080c0c010906032d090203030f2521090902040902 78
    0x28442d070202c2c1d1040c10078a0f15800c03240580740b109800915190140b82c0024801c2c3c42c100303107603407010302250025842c1d01e0010b66030120136002204081e0f40800d00404c40c0c81c1c01000311004001c9800d0440c60075081c0709080030305200d075800450107a030300c0b813011850644040282d10100d911302c0781941d8407030412000d0342039550301c03c02040000c400c04040101e01175449201041c06030380b03841e400a5586689640e42d503c40d4214600c80c03c94255a07035903035000b0450354001988100e100070040e041c0241005503441c2120800c124010411042000c5240020882c0044074113507100001c0c4207a859440b4941803800900c0754000400040c0d01044d0802c0c214000540d608401800b44c964907245500d0b000118211103400f843c0d01001d041c1c0e10b16890035444502c21a104000b92850045541030702a00400d281d98400710518601c0e084c005681c40a2000c0755980c01c9075410381d04010f0100e0365082d210841d110310009148610054216141d40990740645101d500600548405549030381e52030f51004025 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 59867233 1250 59865983 59865989
    0x90f0c070c090902130507120c0912030e040608060408030c070204020f0f0309150c0d0f02040f0602070806130c030b15030709150906030c180207020307030c050f0a23060702040510 79
    0x103007400c071300b1104405d00ca500616208007400d40d1518524a20001040050720414628400344101d050340424100b085003140d050050080c7c41b014101c1080300c05010880f5201c0c1e003c44240e400542c107000c005000c4038200ea40190031621035640b070b040d5900001c3c00034401c0b00e014408107a00020f401c00000303154000b841c8200307088000d0340c9480900b08144c04050300c0441d1702441040007080020130410182c0d102c50089070126070010700742903e07003400c40304110700390300003102591024404000582e030400c04254800102503070081d460410b95600352814019010040001d1110000101d000c1220f19421080f560010120784c1d0042c0e503900b078038006044030a101850f04c0040d81c004a030107a2680280c00807640c1c081c104250701440c051a2829401e0b50b51401c0045a400700001e6015075000c00450010314090b0941580740c41c03521040180300314100300000d0050003101c0080211020b0a1240c0d0610040f26140342c40140c51000000c40c42d00c0b5618009502c5882c25042c85017005d00500c10700d0903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 59868483 1250 59867233 59867239
    0xb100309110409031218081615020403030e011b0204060f0503070501020f030a0804050304090911101e141c050f0906090703020f150309010906060f05090f0c070c090902 74
    0x100d0031440e0107002c00e4510080026000c1022440e010700300c10004d1b07200307044101c0c02680d400020503003503980078110381c00703405040c2001101c0031102003030007a41c04a00d847c003200b4180c11840c15155580c040c00c0b801002c440781d4140030328503004c0303501902210340e0070040540c0100100005500e9000e881c1d1320300c105028542c064442c44d90040340715400020b0341c0117039101050056042c80d00340725080391154070040c000c54440c0024400050103501a004800c0460701c10780c01c1041682d180f02c1403007541d240c04901c41d410090900c4800c010254444900c015083c2580742648100088991088030f83c481c0c203442c0440345e041d84580c82901d00c0550300a40c00703407000c01090859a00c400f42810307901c00e026a9030b8400ca4020030780400c010b141000d03900c2650340703010b041c45c2d200b0070041c910152160003c8441c0803d0765190000081000b08a11810001d031005a007180e40590230440071410006000300304000c400007190125402901d00f0301030700c504641c0021031074141a103401501014018041c1e040380 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 59869733 1250 59868483 59868503
    0x1e0903020d140f0306030703140303061005190e04110f0d06050609061b0a060606030c0e01021b040b1309150f05190209010e0405070e011202030c0702010c05010b100309 74
    0x500a210b020b041c00e100c4502d5900d50304005801c8400a45640301400700b0303030b05101d8a0800000161040c02200d10109041c000c0c5440f0325001b028840480b9051403890100f04040200480049200e44058030080c258908584c0502064010600034130b070b241e54007141918082110a15690b07184010a0041c401d1081807041669507014410135004111004d85c7c0b1107070500c144851080000d04070441c40415404848421105c0d40f41c540c120703806901700b00000b0b5190809401400c0d006100b4030704445081c4010218032005860350742c0d02d420702c00300041c861501c50210003550350b0350060701d00000240700420405007180e440c0c2511041c07854010b03030704110f0034000140400143c0c0d200d22031040d50007001d00c1081c5140509000c000313601c10302e0b1413411b0040764a007461480c0c503a44a960b02c030300541d071502d026200c0000009403030a00442d0301d0b082407034010800c00a03076444840a9402d190f9080c201428200c40c0762400c2c80c0502158003545800940070a8690910f036895001030101c20302400c4944 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 59870983 1250 59869733 59869753
    0x210d0b030c0a030201050307020106050604170d0f1209050c100207050310021204020d021306030311190f0b070203040b03090705040b0906031b0301020c030304060207030e0a15121e090302 82
    0x254880340000781c4550b0003841d009041025500400085a0008551000051a948480c001900c5401c030350040ea50344001201006100b1400304080045082e40c0d00b0003015611214a009089000c0c1e4401c030415252262a99810070504003c4840300b1f01c0d00800214a05540d028001c0d0b0314a000c0c411588079109291403140380240610071502c8108514100d84501d68803a001c5c8003c1c101141000c83e00700d0070b0252848800002c51144030b000c1e501ca0340e05e032050240b80c8800f0740d1415243c0b03004144420015000c01c13002851500311503191650010460b40036685005080c0d045004a90000c100c1c01000800c2250101c004110311054580031a000c2150428610500c40c00d181c00b19065501a4401e0740d4025034008074916001e1202c4d00100050b1800c00d4680706e644c00d640059404540340354011034031108040d00403811040390305003030707a0321040d5510305000c090347c18281c01034000c280501d985070320b2100c202c0c5c1d8105d0400102c0c0e0024004100e101e00034980010040c580080d0014000c9a441c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 59872233 1250 59870983 59870989
    0x60f0a050c0f040323030d050402030615130b0103090b1503120307120e0f030a0c110d02100305042d0605010806070c1403091008011d0f0a050702210d0b 67
    0x70782e0314280c109480c1400c01c1d04550340d001c29411601030149a00c28104102004244100b00074504c1c10065a008101e0b4241481414a0f00c540030381020ba0211900703224001700c6c2c98903940061812840c0101064283d960001079004159800000e480e211070b91003046002c001c2c0150700c1101c104260200c8001e4158490400d0301800300351400c80011704032074129800e40304070f6084036090f488a441951595030101e00624590b82c0440c024102052075000e9500511030041d80c100d00302c3c602038540384050781c0b0a038001100002e504001c00c090582d03501c00700e0140100c0c5030400c148100c81007668020409410f00d1a04181c010100840b02e1354182400410007007004a1028012946501e5070440c020003540d5001244503042440350713940c4018032011601d0360710880ea491628503980ca8003507455050010300c0901005d00e0b0780c83c0510302000c0090020983d5404602076000a442c01c4c001090348031480f0881c2000c11001086403001d4040c441c1c006100f204000605100e500310000f008565894018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 59873483 1250 59872233 59872237
    0x507300e0d0201091e090e070609050a0605030115091d06030c010908120d11040b2503050f031314030c070801050103080301050d05030d05010803090405060f0a090b010302040305060f0a050c 83
    0x2000f80007072001d250400c94513000201840c20000416540c000340d076114038140c0222100c0341d0b155441a032203070804012130380d00304801748003400054070f58050003405e10b030014180d444103204d034543d45524005660151403041402e10050101c0000700000c1c680b242856412140301a03401501c40d0284a649544e80c0d0300640c40350089034a0003002d071403001503e05103c00c40d9040504075800940e10742e514402c405020708020000340001c0c030703080d948810880040b042403511212980c0800000c0c158036001298201c410340d1341003041c941c113096803a9107010000c10021004c160040c0481203084401c546820084086c01361001c140080f1489660b8509445090394002c0c480540300c20f2003080144041c1c108030540850090196044030f207001ca0f02c242940481b9402da00060b510b400105109840f403a00c0e006040c2c0110044400500800d42100051840d0546103d0841401c0c2c1d03805208000d1b0f4081e0b01958029a0010144c4095260001032980d800e00c0440c3c01031380251801001130400c00c0e817541 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 59874733 1250 59873483 59873509
    0x30c0304030c060c0b0a0515040e150906010f05091305010207050a1b0506250b0f070314061309021f05071403040614090103060f030807120e01020a030507300e 70
    0x44556091b4403082c0128004000141054402401d94440c0d50881e440e03c1c01403400207400d42000380444c004002000d0305030302003c2c10b280c600e6000007004110040384240454207851080703070300d0b0040c0d07100e07007000121001d0361800081c95940082825014400c012542c1c0426902601204052121400c01c0c03502d440014050164402d00500805185242e10001003c4050301410f01907240c080c26218500c00690850311104400480c10420010310350601850800025107400c0e00110304055002540348103903154880c8480d50344101c008159170300c0000a142002c09141428000c540b00c5400515a503c500001d03500041107140e200e450740800003c0f1011a040d80e070301c095410a4145260002d503100901300c5041503150072000c0340000e2000884401188a810480d59504244c60728200c81c600ca186a401448442c11180a090340c0100301003d8580e810f00d0981e503a04464076100c0030315000300c4140700302c056110032040180c49105500000c01040c0d9100c000e40c1c600220208070b8080c440d05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 59875983 1250 59874733 59874743
    0xc04060503280c080607020d0c020a030f06110a030b0f060306150d060807090207030e010f1209050f01020309150a02071e060e1005100b031b1308030c0304030c060c 72
    0x414907001485944070802c107012180401c0364a11403950b1030340c00c0000419000306006410200502041c5501004000c100303111500709480c40510980000f054006588030140074540419240e1040116541c800c100008003045030589600b0a9a0f00800500688084070b00589040095083c0d600d003d0701a40d2041500416204204c000c1d88544c0c0b510b90004030000b442103890760b0b804034003240c051015001515000b40c005841d11407030700b0018491010241480d06014082038120f003001ea1000c1003042041c0326900101e8481d146242051070b0584640102d0119440801409942040445c41c2003440d039141d001c58900d51281e074100070491080440003001512045204100c894a407500b030300c803e6000d5000000d041508100041c145201c0c0001030303140759581c408120320142c42800820207000007520050642c50b05080e0b01c044a080841014038064022032070040078044a82448043e2065000b85c9458181d0780007040d990b504503010031074880c440c05802040300d40c4074000c2c2d0740c0306e65046 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 59877233 1250 59875983 59875993
    0x21210150203120105060a0210110d051501080601030507020703050106150206100803030103060c1b0c050909010902030606360708180a0204051b0f030f1e07080601020703020a08030306030c04060503 87
    0xc08200a1242e100347e520b0020350060485080c11020320344541c1e249000fa81207041c0d550801c08982e40d00b100c80c01002e00541e4403a10500e81d40c2641c2c0022625030000003130800244584a5400c26840c0007455807009015609043d0045942c0f04c2205601035030354115002c5401d13688645404001f945083d01032201542d1003480104081110342e0000c440106c0b09061502c51103c2c0301c0c0d501d80d000700341e5044c1581c2c000b21100c000c21003801e00000e81131707100c1d081c4402001014040d0b80000e0b00c91038080c001501c640c0380c60b81112008046480310706030703120040701540508506441d9101900c50200e030a0404a40f0040026041c80b0104148400c101144006010b8080456081000030200a08481004003814061065580146009046025032002650385a2502d0303201903200038001401c568141e40507202e88440703d002c2c1803d154020f841c504000c0c1040d0780b1400102d103041c01c55803019501010303c0400107280340000c00114000c207419401d407480907a10300184000e5803c14850103070180d010b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 59878483 1250 59877233 59877239
    0x60408070309031e050705011103040608150607030807030f1b030519020307170105030c220209030607030507030e0c010203221d0712051003030507020102010212101502031201 77
    0x104001404403510908000801c15181c1c0c0b14813421444195034a10307107110805003801888820007400c001030400f40307030000c2c140c40d12221494683c0140c0c416402400b03a900081900d4000c00d140d050210b01d00a0071203601c030742d42410000d102c1c1001f9030300715011a2900801d826002c01502613481039031094020f00a95041500e002c8000b0003008200e0228000341818035801543c2d1070006500511490740e50513110012a611001102d4060380128441c0c4d00054840c070030b9440d800f00e03c40140c266859030000c20a40720501c100079200b841901a45070084c001044178182e05030f88014000c028540e0b003002400305180201c0d0780c507902002c0b8540581d0090000c80000e505401c0520f66400c4945101086140d94485103801420020000043c0b10400030030018055400182d51401d0361b084001406681003009904402e00214007020741000000244041564002d404442911020041c58001803405000500e101082405400e2403081d03002c64400e4035610000c16903c074000c41c0f495004981c0d107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 59879733 1250 59878483 59878493
    0x14010f0e010e060f0301090819030203090c010e13230f132a03060203042a03120903020607050c0307060525030207030b0c0306010201060603061202090417070f02100504080604 77
    0xa4010f040583c402c40010000703120f51401e000c0c020070703984900c0881e038444802e280c2e50805840508036441c1014814400c010a95034001041e0259840070f0804a00e150f0700100421884494501c0c0c1155590409512001c848954010121160180d00c6843c4603500d50500010180000351601d14421384985040c00108901c44100c0071150320034001032804c000c2c00c020400b0201c0050744252182030703001c0204001d002c681001508152000c504082074040c0f00724200940420038040640069104141013503041d020f940008040d54004103142e4594a1519002d95102e4040203940e000c0e004a0100140c160300a100b81c0b0b0802c4103500300901060301031140300c07080c40c180380b800343c04604c940000040072420502403140620410450642c0d03c0c94203c001909641301d079030000d410140ba00e03074108054610581c0720030529904403443c071034a86a0381400925426102c1030107003411000108070080051140002c820a4803d072280383e00480408029070b2a80154450814540c12603c0080d001917 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 59880983 1250 59879733 59879759
    0x60806011d0609031b030d090501020a030311120c0a030e06070507060f061a040306140f040b070909060801020702240a0804050a0f0b04030e0406031106160605040614010f0e01 77
    0x84800b074046801e00c1a002c0010f0b1401e503079070001c500c6012070341010403464107007441100d01c00001418240861460174000070b41e104007280c0d0141c10161b5070301d150b48610290408850f0709255400e0413203c0f9051507204a107003648030707422140c00709241c8024042c400001160451148416448050620f2440d40300c00303000d8a00105070306000c90380c5031408103204100180310701711a55440f6002d5162811407900a0884104000680c00007103010200480319a07100986980242e21038284101d6403110780c0305444051103600006138103414043c01007801e200540c040d00b0b00e2402211682e9092140040700d0032241c2d94503c40d018a01030170040d5465050044100395041803003401111440f103920703152000704110503c0d0031900e80f4992028041415403240309211104401c8408019042c615560302e803103803103d041c19501500012071103070b55400c03200300d003c0c111a4110400b44098902864144024892800791400703076640d803000801c2032000c158859080d5180210008085d90070400d4420001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 59882233 1250 59880983 59881037
    0x30c010e03010906060e0105120f0a0f0201020c0909030a0f0e3f0d030c020f0714130509030406020d0f1202070606080f0c03060c09090103110a08070b0c0706080601 72
    0x42d900d4059680c0020030a1041e04010b200c84444c1100d1941040c1c104100410303206114101a0702c642c070303205044040841d180f00d020f42d200c1140d4100c003082d880142c0c02e00001ca81c0569016810104003e144840480100100c0d0340560380d040d941440c0c00c606495240f946074186801c24100710b00404154502685d9110b0b42412442d0014100760b90400000e40381c2110b4295107403900300c490b0200070320303402d405015201503045c0058010440e19070a81692841c00b0b102c0c000c90800f41c100600c50b1500d4405a03e051002000742c00e000b20b1400d00103003a525485031140038014800c030400c000a0f01d100b290120301900d0543d46420400c02003541d080060341144c0c0007a181d803682ca10380003d4442d02081181c1c2501a110040c0865020741c40815090407001404c50061000c100401c1550356251100d4505481d4496014807901030740c10301040508503c2d802101c0144181d8001080ea580010040c018051803002217800594944404640c518802d9410351301040041d40420350010759801c04000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 59883483 1250 59882233 59882239
    0x1060602060f0a14010303110705040605060304020918010e0105010e01050f090109050a1b0f08010b090d02120a050607020f07090903141c05010b07020a0e01060206060d0f0b0106050c011505030c010e 87
    0x880100c04e01d4044070080c02c0e407085020071124003c5040c18101480242c00901040710100512440c02c0d0100320b09210040000344116808400103900948520008000141400003008a405081c1d0254004c0c4000e00034140c68a040200002c2c1c61b1500d82035401d0300c01c41c0540600600c0e441e04030b0740d03005010060186c0c1160b948600b182089910144199025031340e440d652450003410020000d002c401040e001b0441840c010001c680494644d522108401c0e54140e038003001014120190504243c0c080074000d1150191505125955900181da0030f10103103114241c0c1c0312141e4401e0942c040703500c80400200401c4c09401101c84800012015101e00d59083c0d4900c42d0405144100c841214400d8014a54800000c81c088081d13003002c0b10f02601504040c9120052541000f2000e0755038030004050307600ca1000c1c0c40c040b4081003115469500c4150307001810350b40035611040098400d0700301c0d5081d00c01562034502c0100d116000c0070801c808858010300602a054079180044070010342016682c2d0b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 59884733 1250 59883483 59883491
    0x21504110904080403060b0d020f0f0117010e0610080f04030e1306030309060216030b0a0203060d060207060203070e030d0807050313140c19030309060806040605061204050c0301060602060f0a 84
    0x480e0744a0414851146124101c003981e10f03402d500c0d001003200c0e00340c0380003401025004040c0c00140c4400c0010700c0030030000c4540105401c408030040310703080201e914840031401020000142d44528661980c00f810f0100c2d254600f5544c4c801007100e84044c2103c45849012003180031401190280d0a000c40c8808054481440f841045a000701500c0a80e4400c5002940d124010001c8170f43c10700900c04c040c41c42c140388001c007910f96110122607035000740c0051089a4008041201940c4820080100c2076108805640380d003501e041440080d081155641c4c04620ec08080c01c46500e004506801450700b651184080c507121048111665080205640803210303120401c84003040c0b80d10400410410b1340002019810003901c01d0013519418894a41c000210f01401840000c0d00141d5801c00c1e10420714003900c40d66240c0d00000d01074101d591203180c0050300002c01c403801102c5000014892806a02104c112464a100345400c0701c40d0392280034010380000c804180a0420452007581040410102103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 59885983 1250 59884733 59884763
    0x40f0b031507030c0504080a080307030e0703050c0f0103020421020111030c0f211225020303060a080303010f0314030c0f210a090603092a080606040507021504 70
    0x80ca452103998a12581c0695907040004841d4103000d540f1142990745401410700789400a00359840451031001400094048000350301b0394030070381c0601c10a458900031220003558034104551280305145a5500422185d0501310300395000c1d0003101c040b02e03042100d0240c085242c030513000b20a07a140e00220304010701c9072110038205c0400c00162441024800c041d201d2030b400312651601d050107034090341e0310f140d05a1f01c142002b03414a0b802d807440c0c843c1d013400c1900c1c00c1d640d0040746644082d40220611016018a100606240d40000510310030030041d0743c490301168880d01001e56a020074030a08205864020042c00001c0503806441414800002202c1c1001001741c4228100307421001900c1f26984601116031400f01100c0c0f480c1d02581142c60072610303000308d00d04000e0840032036004a5043c180c40390414020000207482501028070030690000220304044108281100c103403140056621440c804501645860b00c40c079030081c0116002030000d00a6000700c801c103801c0042c03041e218114101009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 59887233 1250 59885983 59885989
    0x10902130204050f030c0906010f090812030916150e04020d020c0f0d0e03120a020a0606090209030f061611150403020c0a14031005100906030c050102210405040f0b 72
    0x1540410400d50000d40c9450904080c80803540207001010310a030b100c04108207041c1c82c0e03098000e4000c6401e181140f200383d540e40c401c0d02c8032074641d03015950301d21131107209e1042c03182000080c60280c0d0b1400d09441207d440c82150f80c00c00e82c3d00d80070300207900780c6403d0101c81043c0100341a8011f1030300a0005414407480c11420002c81c0c01101110000390800b40354858021024042c2040b8a465801e1001d1841454400310b5511541c1104c0c07151802d4000403101003950080041041e415400f05049c00030a0f203d03070210000e50000d2129a006c2e104030b8803011030b040008500703503100d601c41c0c00c072400c101c12440904441301e1600c0541640c69010300b868400381d00d00c3c00081d882c03041c2d0080d0000c04007524290284004624154400004000b606103055802d9901103110000141c0c10103001c500b903107030700f400c0010520081c0d00180d02030780781000020410110600c61011200c0c04d03000d640e201c0300d0000d401c400c0a502042c2c90b80480000300020b000501d0554401c49050b22a118001001d8882c0008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 59888483 1250 59887233 59887249
    0x601260709050601141305040209011704030e030f0109051002030402011403161d01020607030903030b2205010801050c030711030403020d0b09070f15050c0a0209010b0a030e01050403050714010902 86
    0x807034030540d5250410840079503041500e4049414628942c9403034003906180d04454101c581c0952803113150001402c043c1b603881402d035140c02c0055030b100c514a81c20103140c0542803c0c80003e8003400f0b4000d012030707059101d40c18415011201d4000024001402001e042800250310040040741401100a80d1112110584003d548030f0200f5031143e84c0d0030002064080e0480c1e03108a1080c0c00c0114000c45400070385da0103d64960402c200e400c011504a58619007980507151a50005800c01000140000107403449034181740c01c0070203107108015507600ea404a600b0b892044903801001c1000b0808582114841d544110100f140801500d051603220741c000b4441d0003403440c0035181c2056500a210140c6000d0103188010200c2e2806001c82c00c0c54460081c1c24030034800314450a10102082041e1a803209110000380154001d015142c1580c40b0030f41c0f4480d42e0491039841d00082e1800b28003244034501480f60354000c81c2c041c1c0300c5509040c501c4d5600054502d5451000001e552142003410050b114510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 59889733 1250 59888483 59888489
    0x3090a2a03150608010b1804030e1009031e050c0108040c0801050f060f220b040f060e10060903020108060d080c0d09090e0a0b0103060504031407080d110c06012607 72
    0xa0642c1505202104180c203981140e000350303019034900104960a41d4428461889201d220080c50380955540c1c1010340d02c5c80d03010814540c01264111030581c0681e0700c01103060540b4801d00c00c0c54a8008030205031340c0104420303c4014903591103208910f4056010745401e80d40300e40300350020106c0545942104e42541d4054407035011002c0803405100389803402c402d1030740c40d080b03040e60b4050380500c2c40f00b0b0102d90501c03903032111091184e0368402c04000761525049030301c1500203100203009541d6280c1081800100480c1c1d1a411200c00c11404209a44181425422070ba0142d4810f10341d41c0301c900401941180c042021900c1500c10807907141e650304240200c564001d903c0d00da540b13003a8a440804401c0c1c4503100b0701048141c000709903c00006007840d0b040750540e9048070740060b2035962407400399041e00d451606100486004600041082603400080c075240c0003d2070244101484c003070350382425014500c1950302130f400c100e0062011110703000007900e40302005040d51400d4001041c4075411700407039030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 59890983 1250 59889733 59889743
    0x8070c09050f0601021c0305130b150103050112080708030703060e07211512031404180f0204030f031101060f03050f0105150109060806150c03031b03090a2a03 70
    0x7104011168000341800b0b50301c414280007800d8075044100c07400903411289201401415940d0f8041550f840103900042c000a0b841518101c0340d00302826601074011a9004d1140002e0404001048000d4480109a00a035102c8000c0c0e0a1861550314260f1076003004081c9070415071390705c4002614521911245009060580303420070181c030100c90b40c800a040106038910cc80341824900340398038804003243c90888402112010026500345011103001e20511901420404081404100000310071a170b10714206d401601008003603a0003100390180d0090303102c00307020b410404017501d002c42e00071808000c0c14803040000140b001d0301c601c00001e032004140c00070755459100f00c2103415002824400e01303400c41c5a038500c04000300c0030340e80001d000001c640940410441c0d2075010585030b03140c10a80024080303940354030701d4031894010352003652500200c5400d00500c2c402001c50741c42c14404e904990103004288003801001035644c84050303d9411107403444107000d032514207141c401201c030100359028600c20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 59892089 1106 59890983 59890991
    0x102063106061e060207080a0803060603090c0405011d090a0c1701060f060302071a040b01050d02120a03050406080108060f01172406101b02090408070c09 68
    0x10741e01c42801c60700003480e181c00c2900510503c10a0340c1a43e030803101c0d200d41e00c403da82d547e192203003409000000108003041d07242c20a0001035620540c40f038101c84400320ba0341e0104007110400d070301c1649a0802c80704020641c042500c5541d40014a9100910011956484041c483c040c648100b0080da0300f800b04032180303403c081d00110002c01010b6800580240c0e01c543c041c011b5849180e0072109100c010013410b552001d40307140c490040e0b0304076200c00b800da070810060000455078071000344d0740101d113000c41c60b0101500b00304031310807240b0907518607441c0e903e0810007500203001a0445801a0040d908000d1031000740c54240e0704441d40d80c0403004090b48a41d50040c14124031903419462070048060914408031382030b0206006140660f128500c2c610045000c03502c4010f00c0b4608100ba00c41c4c00544005840d218992541041c05042c0591a16115507104020065558001c0c8103164403 = true := by decide +kernel

theorem cover : BRFrame.Cov 59712233 59892089 := by
  have h0 := BRFrame.cov_init 59712233
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59712233 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 59712233 ≤ n) (h2 : n < 59892089) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
