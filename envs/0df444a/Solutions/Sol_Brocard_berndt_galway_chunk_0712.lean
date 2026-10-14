-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0712
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:17:11.605909+00:00
-- url     : https://prove2.me/submissions/41bd44be-c07f-4b8a-b162-2f66b581c1ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 127877697 ≤ n < 128057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 127878947 1250 127877697 127877713
    0x11706100e12010504030905010f08040c05040e01020c010e1b060a02060103080a0e040c080105040509070f120809060703030501030c0b070b07181d010305010e0a02010203072409080705010c0302160212 88
    0x1200d00b104d90440d01900002c40300c001c00d000d10741c1d014104d0006414146445030341d9080c1910381c00c04412051064a126a0b55036880102080d02901510707034111880c0000c03c101c40c0a000010740318001401d1013108110300d0a10380101c1c3c60701e501a80c07004016035004100701c0c0e0031903a40c2c245c03e42c090361505c07060190324403141509907030324020400310100b5503075141000d5140605100544030054400b140503042000c0030311041c8a221155011102c1c0e504016903501c4030b40c10320740068401d00107001d07007005002a540050580603008281206c2c451860185034170b507581d0040c0b41c50300401c040100f1503202403001c101114856031a480340c1c468120307040802e0a6494000412201031400360181c5804440b00401c00d12200780300d5250700d90a048041c2c200c50550f40d0000f1344034401c026000b004500305a00c100703044628a40c90070300d0806035000c01c11503622241001903807500001401c603000c0d828225942031442c4039009440c46942c0700300c1020f49450303566003041100f4400c2250b1122a200c2c0303201d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 127880197 1250 127878947 127878979
    0x308070c0f0b1e0906011d040609051510050a03031d0a0e180c04090201020703150f181b05090c070501021e040305120306060720130b011706100e 64
    0x100b64002d001d22002e4005107140e804107044034200003441094643c0000e001041030840c0414908260342041e020020b59a84920b0f2400c020100c0c3c0b0700182032481404480108804c44040c183d0042110042810f203050351380c41042801030250000038009960523803980300340284045096001c0b200149917140e0a6150104144469005c860320080085650f4001901d05420320152201e540180c2d001d00c040c011640000c1c0d642c0442e480001c011000342d1501c1c0504160f00d61155500c4802500b05103d111020003106640c400c040e24140c8200d11070800c00408a50203981c044100c91000c2d00349034840da210740300700c1a0b580020707800b5100e0395003c00106107403449400100c0400c80036030100c240c0b40ca003035080052519400c5240508098406c109210b0240d444c1815104900c8d4402c030100c003400c1884055210b0007402e00d8900e90415458000fa1158190030380281c1c0e42c540d000e84e180840c01211012148203100305844042d0850781e0380040560b11445442030305d461f44030142084150200c200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 127881447 1250 127880197 127880213
    0x90b0f040f0b0a080a020d030806180103030c0201090608131145040f12030e06040b0a05070509060712090b040305030c06070503090c04090c08010c0504090c0c0308070c0f 75
    0x2241d10a98203a8039454880036103080074074070025001c1500140008402540481d5800383c80540213414083e140f000105550783e90758180c0d411410300300b0b81c1400c1e03507924580074010a11012040340421065940030a000b4840d003c5603210700c40b108188031140c0b2150701d4003101217000c5260541c00c0b2001c40405088140d030703100005842c1b00c8024001070002140342a4070001c0f00d01a01840303100c41c0c0745051101054483c19150003035900403145c1030b02c0b903032a035a0940051450100503119402b40200b0131050100200000d449140504d1060006913a000000c6030380e0b1003080c0d070440c1d0207541400b0080c04100c0d84411900c24046504280100c16200d2082640c10f401c01c1d4021103e07944005142c42aa00b020b012950704041c02c5e051443c10350800030305454841550315800350090b90307500e404100344400f4500601c0104034038002081081c5040030000c03c00ea106005071021725003419505807506104810400c240c40c1c15a55400785a1a01242100c82c1010f108094914a0181c40f81c81e02081d0b080d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 127882697 1250 127881447 127881461
    0x70b04180e03090102060106080903040504050c090102011406100302030408041707080c060306130c02100c0201061403031e0a09030501060b0301030302060708010e070c020316030507030b0a020703020304090b0f04 93
    0x46806010800341800c021800c0d1900c00c0090141c0d50030034004401d86903000121103042d02c00c2c0341047c035210b5441000b42171a41c09a903002551103820041401000306400c0d0040215607000e034001e0203003000348a684049014187c0c0c503240c101039a00900c0002e103209501450b0400d1007145414074080e9280318640200c0c022002c0c800994000138000c01952200f00024602040c007502d002d415840c0000024100c00360f01c240365800a07440c0c2c003c01c08018170070320216050941d0040100044c0c0140d200080c02454280102d8503c1c00303604109242510b000029a07010768402400002041d600000d58410340c1c22081c115028002550b10101c000b46080c06094058a80c1d40c1c0000d03103962460500034034045003e8501c4060103103c10040c407207030b240c1601c1c803540076040d41042d95100280d0b20200f840d003081198440c4036036003000e60110400c040800d6441c00c59001e211809466256500c10300101e128000c0001c02580c401c010400c22060550402080c508000780400802442240810103a56032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 127883947 1250 127882697 127882709
    0x70812091201060602031327180c170f06090c0607020102071802032e1a120901060801061a04030204090201090806091c051c02070c150c121b0b060102070b04 69
    0x401f00d00d5050392031589603200c0c01825500100001c032111901e2850501c00c81d070310000c41164480860800c0d40640602e0800000d0303000c0868402c150b503903188403152a418406184031030041c41c900304000e10300041c0060069040e071010301120084902000650303800098100d040d4010300034000b50724802e00c1b5605844883c209805030380d9207801411141d84212004048480d0b40031300031800000444001d1080580d03140382c0c1000d000b4510b03002c02e070f13000d0b0182000d80000a14a40c040012590040d080402140d105000074812203071201c2c05541c034a84035000c048040603050008002500d016000103003258010b062156000751661100c60415804544204560f445503020f100080c1400c40c0c080180d9090346001400c205100350141c0543c10030384c0c2c07040c10450300887c05005000d50b102003200100b074004403a131008051070001400b01d0300c0d8540280d0b2203280c0c0c02c034030b01c200c10300800c401c1e16101728449420f0b004e004035a88480c4800c0016204034110311801401141c0c0c407007160018405810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 127885197 1250 127883947 127883953
    0x9091508070b0c0c09040f17090406080114070201020f120604020f0304050a12020715050315060403050703120327110405070e03160e070c0f060f0504030e03070812091201060602 78
    0x1981e14500c91521042000b91341c0264070600c02c2002185008016a140300e612501210702d0480b410740c58100c038020301c980c140e8041d24140d800240c4510550010810100c03107224040f8603030b075480c8140c2c02c0b030045003202d000090b820005c1c0785c680e401003403503d41e10000023000103081c000350b1a030031202a081203400b15240e5001c0021101445a15400f04c0e006100c10701c0200703111810b11508080070711045014205011011000c180344010040e90020072400c05009540c50759079030304255964880354402038030683d80070801001924485d000d4491607201c020009460181881042580761a80b0b04c42503900184e0364081180584d2070340505801072201c0d035a55021942e240e000c06040080e05141d00c0c031110043d031310802803480307040314080c0e2101c1941403c295240250030b0225540003103890007041d161a0842c450305520f801c1d48a0342c06203000c0d41d10000e0040d120350a05036150010f02503c4825400034860504184a010003003408090240500e580701d00d9142c245400e5440ca50841d0002da0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 127886447 1250 127885197 127885207
    0x6030a15020f1c0e060106021c0207030f0b040308010b0a020c0f040b091f0602031921050c0d0e0c0a030213020c1006050114120705030604020c0f060414010c09091508070b 75
    0x50900813401c2c0c030703a24400501280d52406401a41d80e41084a4103c0c100d030100e448130380e0300c074000d00000008540288401d01d920740140381c000310b60031003103a04402041d04040003052002090064501c1c90003282c0052140300582010041d000d54002d2029a005484410180d801c0d151028000c4c0905111000c50022981c09032000182c1c5040d500044115401882903469031140707117460808008840c10403003c520120a00800e5031510240720100c41400c10060010350701c22000201780200e1079003420810200b2100b4299114004c41c2002940500c0b4118148090710703120b40e0802ca0325042550051401d41408803850a1a500b81c15080417280d88580820080d43c1048850740302c40035800b0320918045021010240d00700707003e044982040804000515103440d00e90450341c00070424000c44030081545441d4a42d41d241c1143d0841c7d420010300b6000c3c030300388014000c14401c10155140c0c490110308203080b0070010308400c0ca1208004000f1080021020304c28001c210141c4103000d1601d41d15 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 127887697 1250 127886447 127886497
    0x5100f0305090102070f020609010c052a01050f03070f030f1d210d0513080705010b13201309020408030a0315050901030212010f1109010305010e06030a15020f 70
    0x2036000500003882c5074010000040018181514845010ba0450b00152a03403050f400480303030070540c00001061482007560700d01100383c401301d0300c0c10b000307002c0e0340420560701c0c0a1004554a010304510b24820181c180041041d0301d01035290311059110901d40002e050312000c51100c1a601d01d034131400700c00324000982410b20703042441078221110348080380b40d080315043d1445900314414000381000c12650b840200300c107406060820301703126800132082503c2d5503041c20a9402414200001849502c02007611401c0d440103000e9448542800311601e803003500208142100d940c0903020074548500041008124074003180302a1000d0410440210745480c41032001408035040104883c91190310000104851360720300c1c1100b415a83d05807490b4040e2019070301e260b80900b07048501c1e281590f0800c46212924080c0340c002d4115031009070b032f0034489a41d0b500240e07035440c2c0007540c416030180c1220380083c002c00c161b040d03407480240100701c00600d044c0304481d2845c85134000400000719800074900000d95 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 127888947 1250 127887697 127887701
    0xd080d060608011505070f0f1506051c02010e12150a0509060106050c030d020a031401270b031c02120c060402040606050a0e0121020403050309091f05061305100f03 72
    0xd00f104e40151042c04030864800361240c01400e40003000400d0391002e820800468074242d160041d441510850782e601101d1a60004d00054010140500080c80440c48203204110009105540684034058601001414040602c1c2c20403800b41d254402c00d1042501404001e003504c0c4154201e140001d000e0510000c544d081caa01a4004e0341080820320141000000c0407080712406111b821005a442d80d91078010380142c240b6202e4550100480400080c0600ba101c804282488519001d140d10002e40c1d00b0010856201c0703080c05405034865041118400c854030244990320f85c050040784c401d003039143d005403150b500404140150b40c200c80c0c140811804c081c0514000780c019030034884d0070100c2c2003a006103219090200541004a5040003110260b0342c0103034005a140812029581c0d2600c03424416a00e03401052a50f00986154002480c5404481c001c000c071098561306409031a890902082440c0d001400500070250690300300145661303c00141c02e43c03000d0390fa298051340342c92240700502 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 127890197 1250 127888947 127888949
    0x5010e070e0c18010306090c120b041503060216120207060807050c100c05041809020f0607080f070203031204050a0512040522020702090c030f06060a05070807020d080d06060801 78
    0xe04001104207009002c50940162040b18150209032400000e800c401200601801d610551009107000245400c07146d0001c04045071421114040c40b40c400d2031001d110458641c1002443c2c00b000300181880098510380013086004000d5124680c890500d4464910000312074618001580c40018200b00042c0c108104552190081c1805400c1c02ea078869030588407046019607088c180d41e90b243c0101003a0007103090b18042d0604109124003140503651a000901d00401d00760320603440450103400724a410310490f55065484aa00b0b030800180d080c05501580203168201c1e80341c001030102c440409104142c5038802c6024030300500740042542001802c004901c1035112140c04100f0043c0401d071689200010310141c8440c203444110480034a4800a00a0700c1c030096100c00f004081c0181c032a01403002e075014203c240c91102054503045e080102c140700e25080c60000c02c80030700c081408a51040c0c05011003500241410000e02c5c030741c0d5a10401a8403e02c2901d030519900c41040c402103511003e524 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 127891447 1250 127890197 127890209
    0x10e040902063702030a08150a030b09011d0111040312120f06050f01090e0612071e06020708011404060207060213030b0709060216031212050a02070b09240c120405010e07 75
    0x17600d005407401005240010003000911460484000c2c15065201c00e2040c030010758000301015980e0034003204040c041c089a52007800c0f5110039000d407044040c010311803451400c810054aa1a203441c654446400428601c010000e2020008440341c42c1da010f4007503031140441d2032a0010301c16040000f0450782070210260349040010781d450134041950501c43c030300c1d007003031049585507009401801d1042c9400c2954111100c40200c0c0c10b5441d540505014005040e507160360241c5402c0c94a80c6a101c5c02c84142020004283d803c0700c02013008550f00340d008240b4140a0b01e00507107444500940d40c0c40c1010aa441101c02d004a4010040c44507404448000509140e1016010382c108200c040c100d00186800041c112030700924501904074003c451228155803040010b2005107028022040250042c03681520f0090f8804c0024403401c0e004510042c040c20402800c0402c444d0407680940c0081c1e0080032181010030420003518030005900000b88694450400818108020b034852800c0003419446a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 127892697 1250 127891447 127891453
    0x60612020a03020603090307020a03060c020f030304050d1803061b0e0d24061505042c1b04230a0603090f03110118260405010e040902063702 62
    0x2500103030703125540c10003103d0301107a4203030301da44540035400e055210300000254070104401000040103070302d4020001c20001c50b000d40c1c1c0d04446072405035460f84011140100590000300c0c041c4031403402118800000480e280d20140910303203e5a81d9400c80d550810f401d4100c001280c0c400801560040000c00748004c00c2d110140040e15581d103102c03032180030307215034500040c03105642409810350794010801801d0004a440b48540b404002400d02d50141c09440161480600c0009201c0e0004031405604d038480ca80041c00340c1e0b10b0000309842516030004080400004100c0000d00203007510302500e081c50504100880e01d03480c201000b1a4080300d90001c0140340c00c01c0900e00106001c030781c51072502c540504028000611050142d4010b001d14140346000c0744a40c03000d80c0510075498400490700b4581481036100d11807152040d1120b003d18403132580042c03005141341c181c03410320342c2100e400c041c4040e2407141006610761840c48104400c0a040c202928038424901d0203148110341c40b0301802d494005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 127893947 1250 127892697 127892729
    0x61814030a0b040f0f0309060f0206011202010f02071a040602010b0f2202040e04030e030607030506060d0c02030909041202100612060209030c0d05032a0a1424040606 73
    0x800e4441c065141c020b482d03004500009002e00c40c4403065015582c1c2d101142e03c1302c080162402400082950051000003a03c282001014a00000d4103078103a03120220541c211103403030740c0110b9409072102c843e01d0840c0a0302000040038030444401d43d445c148003103a41d9484504140e802800c6801081c2c0c20307031144d4802e400a0070a502d5203400c50f8181d8040c0b02071007101c209443c800cac10180c41564804030318031084004120500d41d00100808031078104406031140b6840e01c1d4411010303100150351144c0d100a04011f504036031030315644081400744c842e0050764140076400700002c00480b012101510305441c3c3c6000859880d9060010070b50904142d1420401d150601209803039101d6840b2004000301d0703000074055041d50701000103024121303004040020560040c6001b81d12904a04282c00346080c40708481d29401040300c05c11011046104d0082140f25400d4868409440c7c1422811565006010091081244000c043c4014021400d804140d90426162103000c480640d4030090302d140000f00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 127895197 1250 127893947 127893949
    0x103021903021e0a02160e060306070503060406031a0a0c0207060c150e0a140c0a05011202070303090506010b0c060a0903020d030c1202040e180c030712050304050a061814 75
    0x6060103125169103070068a810030200358250402041c1c1c41109940c1010a82001940d40011511101800e507006400403a9541c01c1411119506440300e640c541c02c01c100007841c00307120b003002e1a44408002e101154041d6241c8a84150388804080e103d0503100341c038200031200c480e50080b0228082d040c401082014a0420000c11038103041c40002c0c202c28616003204002c041a4002113160171401060710070008a030303d020b41c0c01c10030110801c041c9009600480b10180b230400d400004895040e100d514015401035004030007035100c01c504074103250381da06030400130403c1000818040d1460072102d59403104d1800d5510718184001f4160760286040c43c107413400080c0e01140c0719043e560b49050204101c82c180805644641c0e0041007803012034800304000070651002412240100f00301c075a2101050000e8101c1502e4241d440f600d5901079000d08800c0218903850b211074075110f8003500681e400c207a1513200181e1051039681c4039500180b1090503002c4400101d0140c00010501094109100411303e8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 127896447 1250 127895197 127895227
    0x2031506100c03051e1305040606120e210a020105100312050c070e0c0d0f020702061e160c0905090706080a18060f09051b09010302060703030e060106031a010302 71
    0x502141c01c1000d200302c240105030081c000e541500015040000400444000707850031600034008014a2022050300090305003014403445003550342aa43c0d4142c0c032003100710840040e0000041c101075610a050026110f0141d00507196845851100d480742d032528220070003425124042d00c4841407002c00801000028102880c0e0310820308541401c1e5100d00c400f0702c0705400c1c400140d200d40500c600802c02c00024480e610018040810108006c101c0b01d81101e01600890045400094104108105c40b0401d00f80742003d1201d0b035415a06940c2c034021840c1c03000a801c01010900310303425041d50b8030078440c40b55940102c036445451080201242458900010111340018010100c05940ca40503100c0c4010551f60a200795a0058000d200c0d12100b140c2150092017800001d660500482c20040500c66004035403d41002e0b00070400362260342580c08001880d4800302c401c606142d51101113542d655814090a0b00800f00341d00c0008041d40d1300c800854102503500240c0303040503c1080007408850b038036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 127897697 1250 127896447 127896469
    0xe010303030c11011e15050906010e120a03201903050306010c05120406230409050a021210061b0201020307111815010e01030204080307030f090f0303090302031506 72
    0x1841c0c086076640e50104180c85501c01034500105035420100754000c6072428000e40038400040c41c404001305100c42051808550241c0212035000d20540046401980704080301141110300a0240340100901100d4624000c404442203001c075841e000e40c00640c03c100f010740d04070082c140018001c40007102801010b060b03080c180090500c507003c0040f44003030340700314840c00c03086900c2022513507e810b010f100480590458401da000240380e2400c02c4c03000d080d5903235203620359404414495041c5801c01d201c0b2400340c0350060189002c69801e1103c880c628601180b6280941002a002e40d074003410020001c000880352a0000780c098440342c12100141d038000f049035841c0f5000b107805041b0900c00c02c0041c1001c0b07641c054845089011800b801240d41c00810349468401c400d886242100c100d000043d000d03405144903c000d13503001800700601081c0a8140400e54409500d402c1c138440d0740b21420360600c9800c2d50400e40c0011080d09003801103060030032038540d9a01c1003a069102c075250550026100a0030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 127898947 1250 127897697 127897703
    0x90a05090711191a06030d1103040803040803030f060a030507030f0302030904060306020d0507050915090301090203060c03090c190308090a0b0406030905070b030408040b0c0c03030a0f1209080313020d0c09090c080105010e0103 99
    0x41c660031012448c0007401920041c00c403c2e4143d90f500d950310301034184d894000b507844e1600c40c0885008904146010304415084070f82c440d000d0020703217107140c58140001c007034080142c0035400200308010080d55a4810480910f100f41e00041e00c88401c00306820407680005c103480207000040180f41450b03a100f0000b46400f0400314003465603800c602d0007007405807e80013030003500b510840301804440301d00d52001e14800e000d20421904154400d208100d01c00d0307841c240c1c13034144c91031401c01480499580b41c0188007400c0041c052201035907543c84190956481680f104000a9880114204001d418030030800140750313010342103055081681f07644807203104911030305c0700106000401c11a40c0005101e8001c40703090040590307446040640019000c020801d00382800100b440494889001070303440750800c072a801540d01402d540d103c0c61074014030034215500b80e90140311072098400254101c3c80781800b0300480440400e0b244618a0709580200c0c6540042187d80d050030018000c124000100c1811260 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 127900197 1250 127898947 127898957
    0x1501020c0d1104060611062a0702010e0d030201020d150506040501031e02040806161d190e01030c14060a0c0f1a0a1d0102090a05090711191a06030d 65
    0x1803140350009481c02c04010060b0082e080a0000034000d0300300f0000d43c6100e90003001d484080c1d03205181070105100011740d48448138120200800d00c83c60340d5006c3d044c258818100000e0300c02c164000502c0405401d0340440041c2c0d0000396250403401c240c00b039010845654141250100c1c2420006902805140241410140d64043e110f48204442e50045110210440c00b15036680c0c64826642e00c6150440d00314800b410301c01340c002c2410744a800e0034054034403c2007030640448601420803500e100701d59503200c03003a81e00440c0411025203030369010f40218820300d1680754103880e0040c01c80d080251152194070804041c40405091600104102800c40d0300080ca40c200c0d1116240c00e00e0320500c075142180900010600300014040a607101e48059028000d00e801c0780700c08000d036982070f0701c60074118541040394200100654184086503507000f81c560f00700ac010b0061a25107940c80c0c0103041c281e0010803504000410180403100e03000e64124480e8a02ea40e00e01d01d81040030030798448000381c4c0c85003005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 127901447 1250 127900197 127900219
    0x60b0d020d14010b09011b02061b01320708090709050604090f060b04061a0406031d010c0c1403042d0b0a09030309080109020a050d06090b010e0f1501020c 68
    0x86a0702041c0760402d082018005540c40354401ca5040d0003c0302c107140030a00c00c000e2000380450f000588106254000c100d1850800c80c40c0d025038035100004c500008070340d20b44400c060511903640c040b111203004103140784d190144c0d01d280060344c020060600800d020b2200240307e0310648c04103c07601501c1264002055031345421010500402c85000094000c6000e481340d4410840c260f041229699001c0301d0600c03c054840d12000c5020004810401d220501004104003090094001c0c01c503001c448680060802075256070726007075035550000400020207111b0400208043c80368507011000d103010043d4103090904400e004901d0f92034007203620b01c640c0d8201c56110004600300c81c0016140c002e00e025210b0300d100001130805941c40c0021030201c9c07400e000104002005100c2c800d007140d00142090009490a801e0004035403200c0b0f026142d49442e02d0707138000801c400c0b0340664001c1c003000300e000c4424a00310305081241c00c405080c00c407400d0f0101d500c4400f60b03039001a6150100c1002c444100b024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 127902697 1250 127901447 127901467
    0x503070b1b070b0708090115061202070f060e070b09010c030c05030d09030302090310090b010501050a110307051506040b0315070c06050c030103020a060801030314070804080a20010201060b0d02 85
    0x7208000c0c000d01e5041c0300000c031401080b010340c4510340a01116160000f5580300c01044600ba40c100c01b50624100c007500c04d040101d58440e03c420407210031180030051901c580b540380e48440f001038000503951140c451145c4640d00c401001110000c0901c01c0d81242002c41a03000203000000440000e01005100c608280900c1010700850b0116040c1040030014001d41c0d14004c0c0c041e4000d1b82d8254801d000310f1464080000e0035005004080354001150310543c0e0034180191200c0d0040001c6030304000502001005441080004040709030084004281001c940fa02403105c0d691700800e068081c034117042c01c00c00d240d10b0001d50740e610041024240e40d15591108400c440003402c482000d0889410f1005000510005000071410b80c2d000b13640008503141c94807015207420324207110080004602403070600803070002c00050300081d845050076a01d850b9803484200d1600000110680b8280310581008000c2041c4c5540708600c10700030b00090151501c1c1c0211070f5280d004094084440d04d8000480c003200f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 127903947 1250 127902697 127902721
    0x4080d0b060307030603020f0a030206070605070e0d06060e060a3503042603032e09020c030a0e10050f1303020d1217060607080c0a060203070e0a120503070b 69
    0xd4000c050501910b80c40c00a5008024003028481640143c481d09045007260806086440a13642c01900179450811a9507070100100802440b0784200000700f9580116a9620001035882e00e0144401040060810039001910600948143e1040c1d8804800304480555040342070600411410030f101c0101020307460035640c80a0030840c0c520b81c040000c004c5200540c00070111000c40200c9003610954101d104426234901c01610881181815a060700085280c2245840610700342030081d20082a0b58500b403009a0b041088803506540010401260590340a903142201400845105890700000c24016215104c0d4050b04000c5100c00210500070741f08121500300110344c0500b00d09460b84050810b0480141c180c01c0e03030400580b44030b19029406030f8408040d402010010f1000786000c607240c0d40c0c04035650000b403081495009000c1140302084071480914803400c02c641310088911140b608010081a050304101c41c08a2030101440100c1d80c0001a201c140c3e9010381c441825480325020550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 127905197 1250 127903947 127903961
    0x4030e0321071a010b04030309141c0515010b09100c081903020c070e0423060712090b07020705040c0c0515040c0305030d0f051e07030c0e190501020708060f04080d 72
    0x11440d100c000080304000c05c002002224000e0b52004034003074031503410300288804a1011507000b120fa01e1349000d800c550400e0071968521801c2190b00b4079a413442d8150150f03200342e000044000c0007080080c100d09118121000900ba1840c060b401d0080030303a28100720340030300f0010750580f900b6021103c01103802a812a030030310b0403100460710000c2c0d881c03a007030380c45110442d0102d0b0420400500105e15003001d102c1d40a848945002800456503090002c50300714200f0705602984680301d6804c0c00104841c0c928113030060b5460390142441c0350a0409000a45030703c490100204081042503602044c0041100002203c086504076070544907810803090300380c071a404c060300c140000200041c00c801140d02100d10980d0448050000b66580c2d40613094195001e03032034000d040f12030310003e01040d11031390040c21b0b90042410250501c0e201c0708040b8100340a0310200419106440c070092203a503804100c40d400400003480281064503001c02c4504128001410041c80c007c00804c80581e0342d011303178115103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 127906447 1250 127905197 127905233
    0x1020702130f0605063a0509060402011b1104020901020c060f040306140f040b0a0e0706020c0405091207030c052e050907210f0c08030304030e032107 66
    0x1c1d4481ea1070306600e0004022208411070b20310714080d0005180d0911206a9070144042c25459291031081c641e903c8624038011039034842440c00d120075a07012000c030322550b80a10340c010001c200902c1e052002504511300b58401d800240b0642524030005220040c540c0c068100543d400b580310300745c00c40103078545244d005120f41c1c040e01c040760381d2080800d01d070007400443e4000c000038003500001c0624041c80c20401c4c0c80c0d0540024101000801003041442030f1900310441c1880021130821441c0722174144549900080c0040e005020b000ca51460300303004041e0800780c6030024094001012071740e11003d2007800c0c002014080580882014040c040c480300c030409150359812401c0020142c03410143d8003c0541100e02d80e071030840400c0010340c00050034803c0c1c51461508031540811004165410040c009044a0449922140c500060060009003008000e080c0003591641403c2c42c0c05850312081c04d0040d8002e900c088461044003080f51003005050310003120031a6900102e003054032141680001c44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 127907697 1250 127906447 127906459
    0xa06150f06120c030b010504090513050d110105150d15020c01140a142206110f030708150901030201030e100905160806010b09040203060a030f0305040e060303030709140301020702 79
    0x140705500050071182e0a04058000c01010095020542c11650785c401450f000550078441840100c445d40e0060f40c1000f203030012861180d540707688042c903290081e040100000c60300d80d100401e5403024042e8613003045840101c04024843c0101051007100d00140140500c098000300d04041d11840c0e0484900700d1100000b880310079450080701c51941800c0e256048143c0c90031901d0503152120000150041a0810b144003025803201171104010b400c1c004250b60b60ae0b55040014990050800103150114106c48216100c0c504003030007a00250000b004075400c0d92125525509a941c3d543c40b05040d640d09080000e40d940d21081c0d120300e0044446950500343d49042081c9060107000513900210108000c81c1e02d012648800d03225032144070a02c20050308650900c2841d6a902c2e2903000f0b541e01100240c141d126480d501e84500031030050350301054011660005d0180705104130808010791040f0150000c1d407542c10f0640b00140364076124840e0141d031201208804040d55000e404541a0907001080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 127908947 1250 127907697 127907699
    0x50304060320190f03180b0402090603070e040602030709170a0209090114061c02030706030f0f0c0e12190b09010b030712110105070c140f01030e0a06150f 68
    0xc050002c0c001440d07580a05840c4509401160504500f00d94100c0034115400c0640c0724011010344660b00240f141009040e1910301845501c8040b15280c0e4100f0701400b082c840d04d00307040c018040c03815030103001c0d40d012707412505040c40070701201c6500c107401c180c0c00703040142d0740da0300d6000c01c4038103400540118452500161103407500703502c000703403102aa5000326000017240c0c0300c801005080380d98680000b0410310103600020b1888c50240701e45610060004800315035804a94006410700c0c045070000d101013030f5502010107070b040c1e01340307c3c164202d0b4003500100301c8440d654001402c1500945801803080a04a01440d4280c1041c04005203102c25401640703540c60f0940b505500c04a0201c840002c0b561802b00034058600d0000303414412168000c2d40b016800c005034865100c022125642d0074140101046080c00282e038082c1200d0044c1070382c8142c0e034071540c6075a04004059004c0c0d11001c0c1014140a008003213103001040c03010440d0360100000a506840300791062024200f54000d241c00c5c011084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 127910197 1250 127908947 127908959
    0x80a05070c05040e0a02090604050115120f02040b07030201061d0627090c010210050705030403050d1103010311031c0801090c110f03030609010602030316211a0f0904151107050304 79
    0x2483c8010355100721f034442c04a070f58510070b120440f00c00b4464600c412907405151030400e8019031102c401400c00b55004076901280c102c0a809a9120740d000068508000070404141542071284001411081c0302e0b50018003a01e02d103400300401e02519507407085842510002c00c3c00580b0301070704006400d03000994014039007050401d07101d1010754001130141c0141c4021600050300c1d0310482d07103d50000d0b00d03400d007140ca40d52404c4030300d81c2100d40910362555803002d500398220b04400185000754030034003641c10b804520400385030a2907400e02c1c82c00c0840b0001011802d11540008095054443c440b00c001065400500102c440f80d030b030094107203407038016100244c000300e1020000750f11441c0301f40d0b030a481e681d076900c5007243d40303210407690542007100358105203005034441c02844003402e5030328042d4403079807961801c0c0e00122400300c3c1c01e01c050402d404a804401d401c00491001e044d01040701c0d071003050714050722103401198000ca071a184450740c1d2143c1c00d0400c3c400c101680d8200c0c0d04082224ac5544c0c03a00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 127911447 1250 127910197 127910203
    0x3010c02010222050d0f02061315030608061302041a090a0609050112030203070803060423090f07050a0e07180b0a0206130f030c02061c06051c080a05070c05040e 71
    0x102810703c1c0c0d90610100500700741d003400080001c031207028204601005076034030741d54000c4008039002c1307a00107010444040039048c041160f102034000c0391a854900d100820780134007200e4942d03100c200300350000c00030803d01d84210581440d0305070301130700c0104204d8180d501c03d60b081c5075020b44880c0d0200001c000d200d4820600d903c128196111520100626601c4200e82400802041c5005006910030410080003901e01c0f8051030f0448409000401d0607419100c030915010f03510307001c14101d0351040003080219582001450f5414500001800c809801d00c000304030b4584d1940240d481055050000c160500d00c94820b512107980200000c0002540762061700c1c94642c0490820401885160086291804c0d51000b80720102c0c0d1004041107048960794050f1075490340e0070803d036400101480b5071600d0500e82e11000f84440303005c40c3c0000301c850034a0108003d40c240c020859405028070b0341c2c01000038603103078121403441c3c80c80e040c403903140c1c4c0042c5481d42000d500c03504050b8206052407000c80140d0341c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 127912697 1250 127911447 127911457
    0x81c030e250b0f0d0218060d0504150605180c040902040f0f05011b1103010b060d090303060b0406080711070f0b0319050405101a06030f040212030f19020102070203010c020102 77
    0xc894842401030382c5074507400d014014241c02a499080c104001c8610000690042c04c2c03016039081100f454400800006425800800800c0740c0755490b5030400c410000c544c0402051030101c01c0e409c100241c20403000c1903184810710183ca01c060485c1001c504d0150800040e200100007142c2c0030b55030389844a40401d03a000e060b00c945000065898800b0174158001c460b032100f421008421103c002c03000751500f00c40805186110341c2c16540c1c45107280c0482d00c5800061008800c0e0030004900d000c0c040c500141101c90680c01420a03440500c810f000050b401241c06800119234036114031400004040d031820b0903416842420444148440000c480b4602e002451080c100684c0200d164801c00c0810710550b041120010003a4210b581842c0ba90b00444e8021842078800b003031100ba100c41074801040302d03075100395903000107885a001000110302d8100380007031980c0350007400746080440a14a0290600070524118907200c44445880050340c400d50680e507400360020300a010140420002a00039440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 127913947 1250 127912697 127912753
    0x5040806010602030c030306150d15170606030c04020304020315100905070203180402030a02070f0605090606031c030c0c050d0824060f090a0302060a030b041401081c030e 75
    0x38100000409900200685452854070b5029500c0d603a0740001700f000c010580204442c0422060080e0b061003000351040b8403c5011101c01469983c0c1004800600c1c1841c00b281c07405c05078090005c1284603100400c820a2801003a0380250300c0340c40707078070010342025124612181440e44030350070804294a52400c00040361f00058007004a03448000041b80c0304c2c4105541c0110720011081110706c281403c2d0b00850340003000c51001410100596641c08824980c0c1c0c000382c81d06901c4109004e07050b0000e00655422040c02c80040044c2c201b075407a00e00350211116801c07020f055a601021260303074000c80c1e1140300d19a0101c01c2d51039140c82148060014002924041251a40d944806084a6400e83c1031030602d0401000e03141045603a62802240b580316440c0d02e40c21168580d07000006880700d1000d000c940d6010b80740841c7c101464002c1c4400c1b24618900f88801c0490f100042022103000314040303410354009544288030030510901a00034182d40c00000079a881002202502440409101d00b800e0700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 127915197 1250 127913947 127913953
    0xf0e0402060c0f0109030314010b161103010213080105070305250519020d031d07090e0106090c050c0c0a030213020a032c0c0316060f020a020312030103061b0909020901110a03050408 80
    0x10b80c524100045902409482c2b210700c0300704070030000700110381000802240f00b0908a5240d0318070801081c00d9801070070310400d480f4036600f0f0901040000380034250b030040c0305150801c00c0d444c0c000207804074040b002c40001025000580c0403100d4600c03034400c80da0141454217503072154062402e0b00a50320a003400310800060318102e40c400015240490182d8105880002441d205080103000c41c02002c41c0ba841000700e41d600c0310001098200c41c06640c420852135102c054441c2d26000d0214140f4005a840e90310071180305c0018001039490707900c00a0420b264030001a120213003480c2c240c00405450140e401054524051000c0c1c01640391260b10a58003500c0030381f0b5900a588040c1980d0303000008161115814a24050001c14031582e440b0b940010a48121008082d554000c28100143e0103a40d4207148070000043c003d01c40c0c0e5004081034000301c0c0b0600d002d02070708003c005110038410300504940b50340003c0c2e0f22845070300c110565400003d9501c103a40d59100f0518014045500c03030722078050180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 127916447 1250 127915197 127915211
    0x105060d0e061815091b180c0714010902030a060209010e041104140409080a110a0b04030e09060f010c0201080a06091a040b031c050d060305030c06010801150f0e0402060c0f01090303 80
    0x5180807003813406029484006c10b040b90502c10445582c1000d4034106400a038008501340500741d0720081240607241c005045541c0d06202e05080640510380d00d0710310400c1e8108186540141c0b000915580e07816040000107131541200001240d0001c41c00c00d495a105042024164420308a00010003c544203003440d40082000c513810b01c4160781c01403030301074920103062182089480c0101c070000c0455102c007054a156413460303624000d00e104191000c1d80020041a00b81c20242080115035030419400c4411a481081c800700081a42140c0d550081c100140000410400202608a100070341204c51040c00264120002900288440282284100d04240b5100c07011300300419106c00d0500b8100700786c031600b18250001d8960b940300c1c080784d1200070f54170a00000420030030701c054030910308040044c048551602d038200b400c0d42c02440440300003800d24030041222180d05443d0108980c10241445841d5440d80001840c034081e800f0345124a00030fa1241145840041d403151a8051103503c08000c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 127917697 1250 127916447 127916473
    0xb0c07080909041203150b0904110418090201021615030e0c03120c0d0306030206030708041118071e0e040e01020c1228051605010e01060f0e0c030c030105060d0e0618 73
    0x1b1071a4810340b00c08034410886043d043c105a04118110728000700b00d00c3ca416a15003001041e120702d017002c1306405903280074600031580d050040c2c15841010180400c0500e003040c0d8400211440110080c0030b0656581ea01c401d0f501d0107100103019140c00505440c3d8008065510902ca41d2003991342035154050410a55841c0340244112012f4076009070090742507549101041d01c011401800a4400350240c048009c0c1d180d4800486440d07080e190209003003503040136a00030b0201d480c0c061444900d190700680250030750b54042d0345007050031001c4070040740c80c40c4d1802a0030700903c201c01c00c040c1a80290041e00e07a0040d840c0e0000e02c1103000c00e000104580c1c4050784510020501040c001340040c90411640d003005c1a003142c0441c030903008000004900380480316203421204283c2c06040c003800c44a00c100845842e80f01c026030701008208042c1c0c91450703c0d071143d00d211300c41402403d01c00c0c10040356031008003281c1e5002a40e1140241d0848425040500c41c0d550a46101092440c0b14403441c3c40c42c00355 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 127918947 1250 127917697 127917731
    0x82406061318060902031003020f040e0c0f0a080f0706091401021903030209030d080114091308070c0f090626070b0c0f120304050f06040b0c07080909041203 69
    0x6091100072852040e1801c00503801090311500e03248110094940e14040307501302c050702c0103500403500011204882860b5106200e181454409440e01c1245401c6804007400800f00b0000e0150030115281004000e0b0100000d00d540140d4105608501c1140c000300b07540a000102c480994100b904c0c0c214615a1f81d0600240c40c850700304500d4010f070021190310800856854646480e24480e040140c1002070000110b490410b62030ba0220001c0c00440040248426000d41c0d14580d18080c1c0c0c21429501d851580200d0001201500900f06403000801c40180180c1710b4010000d0404400d40c182c40310f903503052040182401e4044e89402c068103922074064042d991189030036029105020300892031416140844036006420840341a000720f81a0f664009014014062200300d00c041e00b648a04280c240189801c8010071980d00c9a4851424040031030b00141d18190b0180000120940d1070401c1d20b0003510ac0d018050080d80c00c04102c6041c4000c00c0645810b9008042041e501004051424820000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 127920197 1250 127918947 127918957
    0x2120c03010504061a1206060403021003140c040806040f02041503050604110909100b06040504060e0411030a021305040807020a240e130f060509040f11010203040b0901030902030708240606 83
    0x40403101b049018404100b9419176544010000d01c41802c003592500481c0c901c0e0310300c58801d0002982c80c0c0340303508000d0405802c650801003a21005042c1030510034882d64907400a40060040041f03501c007801155500d4020f10a1500403544808560b03a491038000d5982078155002c0f1245080380303000300d0035410701d144280d11544117880101040104140280020721541c901103030490002c20001c180c0ea182d50188600030700d5140c44030021450281080c0421401d00c009403403190b04070145010150381d0700b200d80380388440440f0b80010203072600d01d4401e805c2c1c401c0000c0203401003080a00021807a0313034030760004041c4903c80780da409000b03171000301100c0024425101300e6002c4d204807483c20031a400341e4040001140c1c02e500000e0030549034000a00106d0b42240c0c00c6944812540400003013180b00f55407450400000e00055041505181960034603018411a040c10155511407070815983d040000d0001050311000742c551480958060b07039854900c200f5003599602444011070050b0a241c030441d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 127921447 1250 127920197 127920239
    0x61c140d0e0109050906120d020309010905030c0607022803030305040b06030106030506010b0f0d060b2208031204150e01050709140f010f140d1e0b0a0302120102120c0301050406 78
    0x1183e50b420803003000030303516014000d640c0140d641d291204800780d04000204051429030001c544503818500014140c180c1500414040c0d003107100c0d02070203600c0d00020b65070381c0f50b03040300d00d41c90066002e40e80f104c544014420419140714540c000100703054159228a00071030040c50754207010b543d86401e05098444501c00200151700440041007803072800009086180d1000790028600812610104181c0e08540c000001c0540001021011040e000f40c000e80c01440d6800b10300e010310f1070820002d840b802201c01ea000d0300300100c0300003410403912004c699441d00e41c0c1041004400340a104040c000d08003201c424000c0ba0440c0404511244200d04202203d24010491240b58400000448001801c031034140305000344001da4034907000540780034040030045810002a1101c205005012041034100e07480141031500d0030800081d190103200205403901903400000030358403170060307900a1288100110045a54900744003165035020300840c100d400c103c03001e01c003150b15080c51005802c0340381c40c2d079 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 127922697 1250 127921447 127921457
    0x50601050609120f0615010f020c040b120d09090506040204030804031419030c170a02061803130f05032b1b020916020610060512061c140d0e01 63
    0x10801840e01c10300804036424050000120740c00c940d540c5900e0701e05100c03a192243c1e0005001c0150201445c00300060300d0209117081100b40c3c405000c06500d4501c03070042140200d03101c00d05078015454a407607000603010a00708450002e05925401840c1c0c0640d030007107140803402c01000c6012842e1074000d50b1309883d000342a0501c0c184c5190303550400700d59095074801d41e0b40500880c2d8000c680c00c18001c03030070940c026200c0140420282c82c01c51122401200340c1000c003075027409500486903000810390b600c0000844d481324190038401c5070624500423400c400c0d100042101d4082586c0201d030314203030111030f000d034215080c054243e00c940d010200c41c031551080383d2905542000b0b03d0b42c46041d07030f507008840b2080fa03845031000d150045020510111507004540e500f07012024507041d4100100ea90056503110702140b04c03401c050009101c2c0c03158803804c00201c070b15400070a07500c3d941c501c144040f60302c2040890f8a400018234200312501100551910540992444030f003100740103c07240142d9850581d50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 127923947 1250 127922697 127922699
    0x109110a05030417040602030c0606040204030c061b140c01110c15031306060e160207060210020a050c0102070501060602071a0306090901200405040b0a150806130204032904050601 79
    0x812503540c0c2009100355100c02c801d003c4c002c0d01410350030080020f88442e03809969101c514084040c039200001e00054061441080f0800100ba005018941074808520303240e0491081d04402a00c00d0410b03603005001c009442110003c044d40004030307551060700a0f00c1d41c120108030685e416440d5030100003d81e40003484c69501c920a01c4900c401564401c005c105418032200b001d45506d0b04846960f0011071280104606104034111804404441d0710500c0c402041c0c49820154002c0d200c8100090369034580d6000304650300b0160203503083e600c3d01841c0c0c00085440b10560b04280c0c1c081c0405114185c0035000b0b60b480400e08003115030b00c0c000c481c1580002030b40346444503030902075231000007040000300d5540c410540c1c3e040b41116030304008990601442c0f588450801e01080212030f108203203103218a2212008224816080003009211105405d151046599481c086940380c03a100310f0341c081d80c0748009400f000300510328500400484c03003109103210715040c54600031f12100040d94042d1580d401040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 127925197 1250 127923947 127923967
    0x1505040203040c0801150e060316051c061b170c07030c0212010c1e050c06060405100f03080d14090c0409020609210c0418060b03071a030f010911 64
    0x2581c2080c410f0f100c528155596006a030f0031254543c1c6000c00074082660200303c205445200141c200e8030842c003405900c040941411400c0c101f40c4a224042e40c10583c0000311070f80d205010303400d4150041030a0001464585102c2c102c0003030300c1039003c0401c8280c014141412013111a9510541044203000d2400780076880c01e403028a9141c4c005c80c3d00410320252000c2007030003805007030013640e12511a107122003e4049074246000e520700c040700811105110185000c0000100313550010004da40005054680d00d1030b4104503035070341c0c104880404050500104010150340103012080e40004108150b000c50390007509041c0d0140c40500f0300f2340c0712560010302490182d105048440c8010042840d240c000b002285111f015845500100c0c00790701032147d80340c0010b00c2010401c03c0300316410007c0c10481c001c40c203008083c0e680003400c0141c0e00e0700e440c0c006e0f8030104540300146c000948240d0540070306017803851050380100c408403007c3c091140008ec0700da01d140550001086c61640b002e0a185001c0c13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 127926447 1250 127925197 127925201
    0x60916020a0807060f0f0b040b0105160609020307030203071706130c03120201060e0a020405010201050a05101a040909080a11060709060f03090c0305070305240c0f070b0a0c0f03150504 81
    0x1040d540107035034064102e408211441586c283c0e889004010a000c22200b04010846501858041c14400b08220142904c403001c964200c0995008200080d000a5400443d01d4056240c0000350141301e02480412000ca1003032107401030000400455106513030300490402000d444403802010301211042c01d00c0001c0c1800c400520002c41407000041190380c0b8158002c80b02402e50319500c0705540068103000f02d590a02a180c0d10501d000740601c00c50809501c0841000054495400c0b600e0080302c002e03d4a200c00b5046500602e08604141b003218aa07040424199200c0b00440010504a0030380340007142022521a01c1421680c0f03405032120300e806420380d00741b0350150b80281096520030101000a00716580d2030065070058000306061400c5291040c43c205403280100302030030740f402d01207820100001c8500e5000c940c1451554580c0d0005005013a24013802000420203107000c81005903154007540b200c2100d00c0307590b480350340c1881020401d0302103400450700c1d180d21540d0840d050009080c95 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 127927697 1250 127926447 127926457
    0x1503020d0213030c170c030c060708040e040305040927060c02070302030a0b160801080304031101030f0207050a0606050409080405040c11030715060b090105120406061d060916020a08 80
    0x4030140c58107060816154150020b5003044031070f40e0709180c041c0641c888000a981072945030f68020500303900345a0000395650405e54126100b503000207449000c000a190545001307001c90f085098160416160240042c1c005005103503c00345006501c0c03611510b04081a001084079031004c0c0820381c0141c850401500ca440c0400c2d040d446620300000041c2c17001c00843c1d400d079000e0201e004c0107003040031401b0142c2412590810070081100010310400750044221411a5030204209129240040040c1c003e01035103000300115502c04505102840000300d1801045882003204000080e25503041000301c801c2c00030040c1070800e00307100170710250509501c8680002d42c075017406120b0941659695242d0380c003020381103510445105400fa5140b5103800703190064402541d8840c20f1202c090300081c201d0065519031a0f03810f01d040b000c45c080c080e15510090181807144090761103106807030386410050b1001d840c4036016840140c00260b5488006681110035180c0fa4054034601c003043c0c40320401c036040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 127928947 1250 127927697 127927717
    0x2003130f02040618140f22050c0907020a020a05060301062c030d020a0c050a12110409080a020c090a050108061810050406090308090f210702060d02040509090304150302 74
    0x5a01d070302040f540c1c00b00c40311141d01c9800c00030101d401020711701c0c508005c0300d001e801ca034032205c60b03c1c06108080f0301c0c12418045810303840801200c4040380d41000f40c0303400c0d003102e13040d90800c030f1550a010b400c1d94041103083c0740e58000d0f0740880155940d001440700c0c80c4802d00c1000002285015285100700e40c06100c80160f1003003a400503140c1d028840041e0a240b0b10140d040050f03484000d841c420021090303c5080203100854204240601d01402c0080d500400c00300144400c1c880301030912241d17195401480c3d51500140c0c0c0301e44442030150302070364807005046c0e680e01c079032017200000300700003400d0203120305880506011b0542c94480658205815070910004500c0e4081c60880b02c540d001244a044e2166008860115503c0120705001e0007460000e460048250002417102d1000c01e070000b944403441d950302a42c44070400d450008000f881c020481c00035488200012a4480c1102c01d40180059842c200da00044548500034407966a00c034500c5250b03203040c00d082404208600940c060880607013 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 127930197 1250 127928947 127928951
    0xc060e1204090c05040e010b070203060108070803091011070801020414120309040c051e030103031e08160203070605101e0e0106080709091815150b07140708012003130f0204 76
    0xe1203145511001c582600413030f41023280856210207502d0204501c0c0d005248403c050602203003000700d016101d1140303140c0c590081d1242030401a5051041078200001070284007503649032500e0700c0149010b036202d4032500c6501400503440c40100e00c0c1149a03246c80d18030303a5009529194403402804060108403c01c5400c0c40070a203c0303080356003102c3d16548102d5101e12185607a83d1b0440c9005024900c8000d194012018a5014521110340261540d500245c0c1c83c400c3c0b02a040114504a2561045032002840c190901091003111100e580903d803e40346942001d0415901150141c0c0034822140b04a101c0c0385181001006124003402d02d8903045007161400c141c84d16115100c0d401594155003461440300340c500f8614040c00b5640d8507407d00151424806e000e00c006102e021f030300c5a401da01901d070102200007000c03410014074248d1a111120b0078010740302d409a841c0001ea0080040e4020050401d0070580105954410001201e110788888141400341d4108d0b61524000c40038121000c03138220b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 127931447 1250 127930197 127930199
    0x105070e1311090d050a03090f031a10180504120206071202090409060c02100c0503060607060b030a0515190c1403041112030918061810050406060c060e1204090c0504 73
    0x44c98054103410ba2a0140340141a5245c05150003046103032030340d00c10262101303100811310000f041403d404450a003000c20000352511445086042c901041e071181e9a46001446e0582c00300001c0d0308010720441c081c0c83d4000155010090683c0c50f40b0084503120001020f0300811204c0ca00e290f0b020b00001c500142000800c4102581d89404690a003e01c400169000340e070444202c40442c050110356480030b10f489821402c2400200b5141e014040c801030005441d84290f0200c1c4d1820080310018a40000849004589083c5000709004047c7d500c00100700030400303802c0f2510294040c841c0520b03442d0380c41d07100f4000d03903001c0c035842904094800c5400310046010f03103200da55000110584985038001035903407032050001300300e4000540c440c0101840784a204002080e6506402c0140c00d196070403411289076070b280d8502004d212140c101590107031521001007180ba40c441c0c11440d20a1184d10b0800c460074003110101da40340781c104100385104d00108402d001d20b0072207130800c48016900c0e0070f0050030a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 127932697 1250 127931447 127931449
    0x6010e04030c0f0f0b16020f030d09030c0c0b0310090207020609091e01090b0103060815040206030c120f010513050f0c090d060218031606230903060403020c030105070e131109 77
    0x2681e0b0702c0c0ca045c0e404805981c14040400c1c2824040c426250160004241a001d81e0140544a02402c0c0d1080e120b40c4d918154102418016100d440d64a640840341e0712020352100120711151700300391120124840d0301039000c01e014000e03100300c0306080c2c4c00600322410310002d0000c01000c1c500050500a41186464011b020304501d06ea046d40a040b0300440401e03804207034000101126025030242c112381e031040703041403d410004403001760000d030103035000b17a0360b0b070b9551501d4540741c42104413407485100940d00301b005150030080e170a0705032981150400e0b240e0214110300c2060360020b603041d1181d0418403020500d404040c00c0203003c610b03409071400a55170b8107600c40b9070880e00211946c00301c0c0c20540103020460b1070203010040321245080761080d0054140b88008012003050302c10385468480c2a401140c000d0480000d032210346000804850302450149030080d01e640d41500800c0c021741c209004590243d008500e505020800030b05260f44000d01c111810001e01000c00d201042140300300410f8002e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 127933947 1250 127932697 127932713
    0x50a0f2303031303110609012102040512061605030105030d0c11120601170a0302060c0c0a12030c080a0501120b0a1404030c0b010801050118021b07140a050306010e04030c0f 76
    0x2c3e0302095050100c103a241d800c1c151422802a0241c0d80f0801d81081010721581e0070864081c49400481404104086804080e400a101d01d07001160300240001c000c0000b01300009285101e0317242c40c1c1040341d0803601204291031a00080c040c00350706800501d1000305282c491602800030600a40042c01e440c074030f4201140b0303040c06140c100c00b02600180014014154114503c0300450380c0580240b1413a00e280c0c40003501d54030050b03c140ca0801c4006504a592142002070070809900a1050b4941341c0e50f01201400401003c092080424200300004100507802c1c03060504075104545002100d81981d1354880d4803020007000d0581ca0703030703584030541c507201c140b154918420752094071081441d6060b424101640c4e541640031207241d0b0b0402c401405034208a1000f8010107140300b8000d030b16443d0030f803034001c40c015840f070686101e886881c400140c40861002100e8845009a6108401c1074071881815260300090107007880303085c080004940000d11886000b0341440c040d0b8001d450090103640c560403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 127935197 1250 127933947 127933957
    0x1141002160f030624050d05070b030a0204140d12230a020a021903050c132d060b030f04080f0c06010603020a08090a121107170f07050a0f230303 64
    0x400d6154903030280200001441503070041700314100401800c4a40e108240b16001c00f901495018030302200803001000303410044940900700010000c2d0304c0e41b034290f00c1d41000f0b411510501002e54140000104942042642c6240b81a0041c103211640d5148040543c1e20504095080e01054000c00200c42c07a410340300c01a216201140d130280040910500400c0a0411280384218071024000740400c0000c00c00501c039443d004080d1218124128241d01031401071a0908012051a003038481414040e504070790f004000f6200b0120410686440c3c410203640781c08111806400a1040c034040303004a0180c0303024240c408169134845142c03500021455040020030ba0025012130f0300441e5807140981c00c0846e035940004ca060042c104a92103403600b0007910b0a407010b06091108050074a05c86000600542c000b038071345503051701c034542d109990031a40c51842c0103a08159001e1104080350a1404202e40021500b004150701402411712081900f0440b000311020345071609070100f4400c684060000d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 127936447 1250 127935197 127935209
    0x30a0602040801110c031c0209030607030501080706020111090d020a0b0712090b03070f080403050405040c051e1611030a061409010509031611030c0303070b01030c0e0114100216 78
    0x2688031032401040b607095822000581c11a0101407005406100001080e14009034100481d40740d1328031400c44d00030081c481c4541c40794060055504114030302d0f8260704007504944050081780c1159561b00340403801c8941c00500c414814204104c000701e0b0340b034007062042925000514450403584c0d980c2c1050030315881884200d43d40e440d03000c03030800c900390000a182d0080c44003110359461b40c503100c1002028203901084c1d4500340008800805c0500d8450030945d009480702a204000441c40e8a00142c032581042e0507509000c06c0740ca00d40d032100ca035184266400340c501030940b00450f02c42a9165100c5160302c80429800d84505082080894664000c0084070020400f880034030342801c0f5601401d403a401404c1e04000e600030004900855000025044607503001400d01240000e0840000e0070204104200c1d98144008503a80d400c1c0440403020b94100d038450704a0400291756050800c40d40c1d4800d2103246002011480202054107200323303200749002d1984190342050904c1c603c403c3c00300406030001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 127937697 1250 127936447 127936451
    0x5010e160e010c06180209010807031401090b01170f010c050705160302150706020d110a0f020c0307060c060b090a0c030605030a11040c05120705030f0106080609040b09070302030a06 80
    0x4840c05211414088042284501d444141103029200182410001d550010705241d40c40218440c0107800081100b602640105500c0881d40d665060740d42d0b8241500059030803503070724039504260b040140305240da019888940c07c3c5c03da030310300000c064900c4621840d04e500e900946124686084003803241d0150101c15442e030360344980c0d890604a02d0703d05031004089580d0300e402c20500c050703950444100c00503001c11040039603900c8a89003c9010b4000c09040103103980c1880c08150020143d403000e000e40c40040e58903404010703003224007280e58900d18420143c05400041d13082c0708481c420840c052003240a003102180007038115000c0f681e4903100b107134802c80441e9108028880c8aa25004040060004400521401c03c11780c80380142550900040e6100f035a031420325414481c003440c144c82c0d40e5160341160414a10380f0440c041c0041e4012078414100c1c3d040c050000c540c41d402007400c24007030840030344203a09903550790b42d80702407180002c0c00704820f41c42000d0300000103070340400c00444032a1041c400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 127938947 1250 127937697 127937701
    0x90f0f01050f0c0c062e0b03060f03070b0421021009050306070f0e1c0c0b090316080a1b270b0405010503030a05070602040b2a06060325080105010e 65
    0x20701a2a6000d8080c09002c2000c001005004100040981d01b04140402100f400c1d4100d08083c1201c2c000040440750b089180280090440c0303001015602c181001e0340c034901c41403005020142c982180d805101e65a1005200a020001c0441a030005a9200d140313200c600351900d40001d0711180800050100007030403107400340700d141021321000da0081d849041c03040d41444103000290124005201090003000341988003d101107095048482e200d4100e41a0890746403501d001048550040013400d0107403160a0704114000000c0b0310210072551607001400c0c4400349541c3d04c034120401c51180040d007102569021401096810484481000c80c083d0300d40020359450203e410b4404001005101e28175000040005403404021a0386410080c6400d0340c2da00034601e800802402035411016140d036000c54601c1545102c000c04004c0010394003c2d1000044101d031010782e80c1d85c0116000781d00364006280d942040140f4038200b81e40b000c1126200c40901d0707141d0307000508442c826402006450b40b900c003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 127940197 1250 127938947 127938961
    0xb0402070213020a030c091211060f0309030409060b03101e03020a062105090a150e030703090314060403120b030708010c17010b030402090705030a0207020d0501020301051503060a03030503090f0f0105 88
    0x300e80f0b03582004606101f01e0b11481c103002600c0d0840320600103007160742c548200e20055603c2c0004c07200d10603080c2d14800d40780c0c00c003c0c685607540d070824020560032600e00040801e0000020301624030170152708080407801030500888c4031040e0402c06030000c15140200010005a64000342203002e88150f5130f440c5c0f41207a04461f4030001000310030020002d07078a890144a603009002c640c0000240d00b002025400c001e0700034500004201c040c9000da110300000c41c482082641c80117904045a028041c000d54070503a00350301c90340b00c00d030640c2c0040124051301050203100e150364000b041c900d4070003819a0100f42d903071030640b800d642c0c0e22400c8800113031444807144065144010708c1d44c05449601d4034917045180c1a40420104400540903205100010001580c030041c103404488010364040e0044180c06101d1420a000c0e40003800303214441d22180c105401c9401140094a11881740140030342d0381d0b6403035924181c5560b407001c4c0880e170082c00348884107424404200100d00c8510104400000c146c03400e50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 127941447 1250 127940197 127940201
    0x1508030a1206030503040b09120a03020606040e1501031101030f0501030813080303090309060d2d0b010201020c150601030207080309060412030504080d2a021c020705030604060b0402070213020a03 86
    0x140000c6032140c42e2110a01c0480c100005542c03d607800c580b41c0641d40d01a00001901411410015681c0b034030590000380e00705079010548602134003040e05e09008440a19584549410391f0340035100d0000782d85401000424072011280c0d400c0c10041c100080c086c11046480400d9030000d0b041500c0f820b0300058280080c0303410f01e00ca10010321002002e9411810401007550302d07489600350282c80f0f0304010070398480d9100e0582c000c0c10414005c40e071075182030341009520b8440c007200c0e001c408070309850705188545071b50040c0201c840400001000d4202d40b0700c8061005401c0802170141030400d03900b4002031002030300800c0118011042c1d00011315861901e8545000400d00d055490810581048244070001e004601501d081181070f400101d010045d4010350aa015005070b14554003141000d40042010b0b00450708035000c4a1200080c652621103c1050340e03158040e10805406a20040006000c00e2156000c081c0c00e0b90000c00141c9841c1140e000140d20b142240134600101c4d9001541c400b40603014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 127942697 1250 127941447 127941467
    0x11040e0613140103060209030c040903020d030e0601122901170c0409032a15020d1d03032a0f03070206060d0b011a1c0506100c0b01050409061508030a 66
    0x41000b8050034800100c116580801031000405898000c01d10952a50f01440710150106000c0c0040028440a00300255100780c050340c05000300b490840f408801c00383c0803030342505a6452508116884205580300282040c096080c0d084907600c0c4221074070740224211549000b46200180380180100594040d4140300000507403500c00c51408920200090700002034010380100b034809030705c1010b000e2413404142503142c1001800c0940c11011101560a0b0382d000c2d029681144404200142c0341102644011301c0303400d05096035510a0000800c4454500140524a80400000c10944806110b1428244c11215014222030340c00f004005000303604100340c1c5ea00a9041b42d0941034160561550094005d041c02007400303061246c2d0410415556000803140129103241000150410003d0803100402d001c0d0745003841180c0c2012081c2c4c0403485a0b54408050b600400b80c03400301c2e441e0604000041901140c100d0f4030540b9055104050490a0b8003000101402009550f4a058002c0001d040c1115 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 127943947 1250 127942697 127942729
    0x290f09030406020c0f0102012c070909020d0209090f0d090603050a0b0109090b030106180501030c0602060705030109050402010c050303040c0501020106092703031806020a0e06030105010e010804030311040e06 91
    0x41c401007112681c0041c4103080f82c581038440400070122000100d0142503e441044441910314800400c803895111100d01c0100950042d51030141c1c407880d9140542d00d042c2c4c00a03602c5031228401c9405072500080060304014800c086035280301030507c40c6400c02405080040c0807500ba50b000b00081e98041c01416804054090204800355000001a00700c03011030140e074642e070f43d030b44113956016102540241c3c060120910310b0701082ca00c580b10300d80508000d010456000c02d2075800050421300000e81a13000b58100d840d0a81586c0c00c0079840d200901d00280103074100804180c1c2d000206400348010342c0a6800748105004244c20308001900750388507075000c000b0355854405083d0540c8201a240312a04086030704040305c5642c5070808070094080b440d007502c42031000c03050f210700700070440c2d0060400c03540c1506c682c000c000072001085450301092162602003036172495915480c0d846444c405510501c24100051000001070840100350440d0f00004600031081e81400110311340a02501c0d01680b03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 127945197 1250 127943947 127943953
    0x6050a0b03040308090f0703060608070b0a17040c030b1302040c020d0c15090501061503060b0403080f0c15010f0611240903040b0f04030b0609090316290f09 69
    0x450412440e0561000500203010850908003107026403405001c80c45184584400311190540c0342e041003001080c1c2c1c2c2c03241e00042d00c5184000600302020900741c0d4000040741d00e41c440c0c281104804001e03000b000500c00c540b101200e0170084001004800810f00a41c104049003d070810300d40b05103c03c55502c408020107550000032800e42d02903108401b801070641c00b282c2d550030100c4001050f0050404420001c00d59401c1280114806e21a903c041c010045580e4091040c0fa541c2e21501d842440345002c0500411000c020401100c5625402001940c1e40d804c2100c4901c1145030703901145150a0300140724140c2c000300d040001641c8020b92110b400700c4540909905510642680802034a41d480040000750304400140a20010702c10b4030020600c070045c41c1e03603411011446000e507902030b0000b04d03401701601c0302256a50814880052281c24018002c516051f8581c0b800c44890349021411140c000030302403108442c04042013019103200b4014440192401d140c40c00c0c2c0c1b01d4403401000359180354 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 127946447 1250 127945197 127945199
    0x504050709140f01020c13021c02090618060706110405180f01090c050c0601030302010c08280b0a050402120603010c020a030801030b0a060806091b01090605030f1e0103051006050a 79
    0x80c07012154000001003c41c0c40c48800c0c0362280060b4240b0050503281c41c0d0040b901144228528440d4006224140110700c00d81150442c264414080303016078014250060000c0c807002c0c4100e02e9200d07030f40860000c0240241d040c0001d030758451055801c0081c00d0a036105005c141002103040c0710860741b40840041501a40c90728200315001c00c41c040521403140341949915000d04540d0080007260f0000071100141c2d10a581c403402e01030301803c401800800001c400c240024442c1c2c230750461b82880c9442070211100000680345100d009451807008166009030741c4400040e203551284018102d01310311b01c2007007003580f5190041508480e8095012400d64014060010000c0c0d808900c4a0541781c0c031a0f6040c0c2c48c2d4440c0c0381c04034000d0002d60058089032084505002d42c60000040c01c001c1d95a8100c62041c0040a02d401180c000000d0311404022500c1840071842080e2582c00107036000c81301d181840300080b4242c08090b00b44101382e00607241c0343c22121f514001c0c40d0982c01132030701501c400d540c480422 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 127947697 1250 127946447 127946459
    0xd090c09020f090f0a0509070c2003030304120201020405040221010f050604121a09302a061003210e010f0207090515030f0d0519050903010c090504050709 68
    0x9100b00b407103440c4182c0140a0503044c1307640b441094400b81a020b0324440b020715048001825181010005070b9901c1c040c11000c8114501c1c0c94450098814064007460454440750381d000c41c90f6407003141400a5540a010104540d01c0c0c82c4040e00d1981d61300b6003c1180c0155032103450715030711010b0300f04801d0307009070b00d2042c030141c0c03500c00440d4110742c40340048810100315400c1080a5040c040c1c91407041001000610650200004080d80d201d0090180b000035101003010440f18414141440181c0160622030302e00341400c0680c0c0c1d40301c42002d4005521440511808480c10b02808a484400342d001c080030910901c0311446d901d0844141000c0f03400308842a0350301c041d080c000c010413014100310320384510480b418801e004070001406d000a0900150410320701c20141f42c681e00c0140c60203445180319609000c44c2c00501301c0710000568035120714200b243c01120a1114a001010060113001c000940c90b42e2024401d5401d002146d40d40d110815060070200415664050a9070080241214041c490 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 127948947 1250 127947697 127947727
    0xf070b01150f050d0f020301030c0e06010e0a060e0d0b0109060e0a060503120d09020d050c01030b010323040201170108010c030605030d08190f1b021603170304060f020d090c0902 78
    0x20800c00e0700f4266103502e035642503107001c0c103484010000090300200000080002508004040e0b90b0307140e1002c201e6039200001150510745044949510101d0342e041040507502685413011b0020007c2c0c040444c0a1071a26880742060013a400580740755580c1008022074003149441c0d80d000000b205080c0021894140000d69410750760300d04422804c4c0002d1071001d094419444101020342c0500503c5d0448a9402c095460f0304031829018046828241e050502d076200c0e100780041c18000d0b029048400390300702000d011040000700100d050082c403419500072140c4202d046070007050400700101316079848200040503102e040e03200602079071100079050f03a100c0c0c0007102d1741e038840c00c64030b0b00340345260107050719101074203080720243d54141c5065004032049050000030f03800d841941e0202d0b000c03050200c80111440701c0714403000d1f00346041c1311455154803803980000c64225001e2080801c004084041403000c84e44003440d400702241e5590059000c206000d00d9050043c040f07d0421410468400d003840c038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 127950197 1250 127948947 127948967
    0x70513030305090604090e0604020103111c0905011409010902010912081204021f2f0a030e0307091404021002010b030318041b050318010b010c080c0703080f070b0115 73
    0x20078402c02052000c0242c8548054800034061418140507030004102c1035522440107580607400241410600f1040c0c825010403188111070340600b40d000d400703e4042e404001e005905048410f0b5481c2e18465402011030541c0e54091541e01c400041c80300700710320000d81a07480c03541c007039180020800000004200c0920690301012105c881c22455580ea034030000e100044583c210450303443c1078500002e0510380c861a817040b40d04031003400c0c200716014125200d04012401100410b182d00c81d60300d10f000680300f070741c9490340c0d80405000c50b980561501c002c1d000751202101244030f084010400c11040d0700d040d1101131140640b600007048008005070100382c0307910400c5102119140c1c0425000c0941d140d66014099520852080325240c0c80c0090000b040355000783c80d1200d22503a418881d4500303c0040c820320014140c141c60f05020211142c0d10445150004840f0341401d00501000101003030000008000240c0080c4106954039510b1400c0704085034180c11414076401a01d01d00c032500d17900002521 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 127951447 1250 127950197 127950203
    0x14100b0f100e03070306020c0d0311042702190c0302162615090f0714090103020d02061303080c0f0609070e0c0408100609050c090112050603010603081204050607051303 74
    0xa1850b907401c010130300e085a0b55200a0040303100041c00c1820f104e0202d006148240540d078203015908000c0c0c00d203155030046020701c1e44c24588800d6401c07055a0441a0303031000341c80e4210094246803020440d01c0101c40e0191485002c1850500300da410194184002001950100d440803003103070500995140006084142c45e00c0c0b101c90110f81400c401040001c3d0615116140e80d1000614200f0350701a120140d1420120340c1d481030340e102044100000071400c00d0044007500303400d660f80c42d540820241c861844401d9800410030081c203d0300c209110058405140503c070715543e03035110070004030719280c48091202c3c200d401010501091070070118886088504400c1c0b00308203034460403041c2e40c15125a80c0a80b8481c414440c44148252140d0051030459200101c100700070341da40d03006443d661081c00030707803800900203054104c0791190680c40301e80c000d10050000200d00792039580301041039100803070000c00f80c3e650380d08010800404000e002e502c88401c1c0307811030810b1a042028414419280001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 127952697 1250 127951447 127951457
    0x4030b010b12041203090b100608131a0408071407180b060403060b040b10080a14010b07030c06060f0303180f03081c140406050406141006180314100b0f10 68
    0x400302c00751191b04540c034160340141203040c050a0800b6584c1400b4042d100385400b203801c410024141011001c4601f141301c3d0004080b41c4d013031503014070846244500a0086813806000d0052001048041d04a44001c801280c02425020300b440d0303c2c29050b0f004000118480c600b050302d6508151110310944040b680d01c0840401c0041e40e100004000d0980f08513802d80052070801c856100b02e500c13516040c01100b08400030030041c0842c4010400d00d00e030900400841110030484000041c1c414040c5504603800f1307500c00145291646105e102c070028541c01900011402400b501560a00e0040c04005102040009804074919610a880d0740540640c40142c210841c4005448030340076044401031800b0006215a070b0b01c0c10f458880010030003642c054414602c0c110200e00c120401b085194061110380031003201061404108441d645010078000c04011440c0400200142108201c00c2a2081040103004c1d603c030301e1030303560003200d005070b500d14451169840b0485c002e4980880d4160010707081d00e00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 127953947 1250 127952697 127952723
    0x14010510050a050f0d1103040b0903070f08030a11031302120f0d0813020303070807050c220e07080106060c030f0206010b09040504020102031c020316050c0304060e030a080406020304030b010b1204 86
    0x38071320050050040e2421a107090604c2c04818000c1500210720440c400c000d2174025848404440d556402009001000810701c0860364011403c58070203103905c41034180020410104a031b6000c11141c005865200c880600303170b104c0303004514050040010700c1010740020030720000360308100caa41e641c0e64442001070002c030360081400111104101b100168000c4c08403983c0720064070b42510250301111b8165101e01804001030f44610380b03100b1428480740b00c2c40301000c1140c000d14030040100700c43c2d481c11040384500c00000819031400c1c010300c4002c0c40240c070f6040c89580e16060180400205030440c1003150010340051001e16995010b503980c01e0f009450005680d43c0d0340c03006031b00d140f042015030188483c2403c056034000c0117580065103c1c2030320710300031038183d0398410b42612203018054040b4200d030001d0000f400141c0c8500d0360340300c406a0080846983d0345032500c0c4c000c010f0740107400400c01170300001414014400300070a07260040000c00505842c16401e840110300036000504020050509104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 127955197 1250 127953947 127953967
    0x307030213090501060e01030608011e021b0f0304050117010f06050904020c01050f0901270605090109080a0512010609050d14010f060b0c060601030e06010e070c12020114010510050a05 81
    0x20040d01410402c08204910b584030007000d011500002c144500280c100023000c40e80303a1060195103601030300f032802020301c1c9500d4800c03003000e0340110380b01a0100090400b03102e01100100802c0701d08070b40c044090f660792400c180004040303c0480c0ca200c403903a400540100042d00c1a070805c40101d0f401403034407070784503c404000074001c0c0c86412603008196092005103e0001c04114107503014080b88802002404002c800c0804050051070720030080d44500350144022464a42190703500c1312801d0000903403180c080ea40c03919a9004038144500060021800e003040c2c0381180d000324050445810250b00380c900e004002545403d0202d8020328001ba20103034880a01425009181c0c80e10345000c1c280100d41d01c0b050206800e4020117140c040511440380440d1241d4007900c2032a4001c00400090320903603082610302212200042e020208102503071400030701080e4420710422022441d0703400803a1201c01d0f002885203810041e04110720400178000101c0c1e1b19074210045074031169060400c940c540700401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 127956447 1250 127955197 127955227
    0x30604080d1e0509070515180303070b070f1107030f06020a09050402030112062702090c0702060307031d07050a21020406080d1215050d06020d0f050907050108090303070302 76
    0x900b80c03001c1000311100080342c9010a80045114040c00e0040704c1c2074640e10710070000d644500a200b0a40c0301d0042048003605201e040e41102c10110107401c4030314000c40c0e5524950034803c110f544500049441c82c01d80b00c0759502000e400c045102801c0145080f504546469031303065200030340146800d60008054004a02980b0b4410081800401c01c6450f0344c0c0d41c42e402c1c00411b00415003241d0071850a1400900f1501d4034132030801290701c10110144420b10f59013442017541c8040c02c030031102d06040c083d40005982d401e008511815060758042080000750201016014408103840071941010909011707a44404072003800f100c1003a908003c50b0712241c101c00010f030147c408007a41050038180042200240094012510181581c440c0c03111364180e10400b00b15005101c000c2d001d401008401c000c030349854100c60592074040c4400500d4030211381e07000c0c001c071048e000c00000620340b18030030002c07212400c3c01610000d00c001c0c02d0286840c9080504c44c0c6d26448000c080401b851f6012a40c00c0c21183c0741 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 127957697 1250 127956447 127956461
    0x30a050a030b1e040e0609031803100603061a04020702360a1a0d030c08090414040f14011107060509120a1d0402070b061e030106120b0702010209030604080d 69
    0x107058000d030700ca003040041151080d1a03007594051170074420726949103c4009000c904c200e119401550510710010202d2140806144000c7c2d031602c01e605151049010038440c500041d4800c180c0080c40440840c80c040c81080d105010034844c61042c0086005a1240619111040202c7c06103001101212680c2d8244a511441599a10010000b001111211544030304200d43d5046000800b4502100070407944402180000700080d414410f42e000044c1c049000e80340c0f98800500104071010345203080300c07103102c01300c5003030791403205c01d0840034184400e82c80c1e6900d28000103c001e100b0810014075402d19440b4154004000e0b030303550b40000b070480030188001001e45100318411540e5000610008181407181c04408543d02040d4000400600d40351003141c8d5000c4d480b07201d04516030f40c0d00302002580c0c0100c40c132440d03848468000521842d5003c0c45250060071852681c41d040720b10a00340000c042000801c0c10341568410000031402d80da0000b600707644541c0c00702440d5612903034071455002030000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 127958947 1250 127957697 127957699
    0x21201020c010b03070509010303021903050d020c100506060324060405040e07090606020610090f0608030d02040602060f0108060f070e03030a0f0810140d03020c030a060204180e030a050a030b 84
    0x301003200c114004064101a1200d1001c80c11114615140e00400c01407007070a11004000da804866030400388484901110b11541c02410024205a442c28050301a030b4007240e00d900480d00300014a0212400781e20425801c0300c001c2d40c0c3c540c25071805802c0007e07800800c0395082c008000c046003240c04e40d40d40c24200e801401007c0d20601c00e80034140710040e5144081c0c081c42e61080c1c245000404c03042d1000401e1803103004155800a422031400a0b850000d000908111084c1c3c0d0722554040380340b1001304024040340c00710050059945241400c000d04002c400340413000921318203030041060050008159070085203049451100352112401038644001c0660b46540501010910940c095000307809584c28410307a4a58800c281d0310b44003042101303c114040c241441d05080d6030922641071010400b03001c5032182c01102c2a0f0b0122800091411075000703007c489198000070140260800c0380139080b4015002c40d8180100405034a15580301d020341d60041c0704000020075464030562080d04401c41c0c100d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 127960197 1250 127958947 127958951
    0x1401060315080106120506130206091e0a03050d02070803042d0f121a04150506010c020d061b09060203030609060a09050a060806161707090f140406090204081504021201 74
    0x1c0c0e2070985c803014172800441598640030701d10000701c0000d8890124078025500600b032a00d000d07401c0c801c01485041a8010b99108070034448034100b50340f0703030f80341490286000788024044000075200c028175210581d00107007080c0e00706120420910f102d480c00516a029800000c030f506842e42c0c15001000300641c1d1100c105c2014500002030407071340955507120290b02405004060000d48030310043c01030750a42d001000000c0500001c90724103000d0f03029a42100051401c130043da1040c4e00011860345c03410900b510407a5031799454000b2030903401301d507980f2004a824100300841c91700c10040d44a0000a0005000340c040c81c000501c9075440d89850409031101540801060030000700c1c0500400840c000c11419105580100e80045030a071a000000c0c900d41d0345e508141030300c0810307020b15820040d01c0d030303424440200404254440441d00c818050040c80d00400c01800041082206850440c1d0100b0a0070b8410801803000d03140100705001ca42e001d1b00071500381038503240301040c004c0d00c0b90204541ca0354 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 127961447 1250 127960197 127960199
    0xc230303031503010606030b13090c17010509010c170109050901060b07110f09010503030403170c070611060c0a0f080916060513230904050a050a03051b011401060315080106 76
    0x2502502400702c60101c01c1c0c0003007244584501c41901194005000580e0094a41029404010307032a00450100c81c402c1080150050b40c5080200040b00001d1044585075180c104100d1025000d21170022906082d1030106101c036500080e0f01450503060040c04025600c440c001aa01c08094101400802e801001c056550f03c150500c5003080d400302c115144624001080c0c1c01041c03400c0c00d4000e050f00e000901a620706451503581c1c1d60303d103444903009185070340244144403680c08144452801029191030f100b101000c447e00071b50404200928600903100244501103007903a00400180409426080c5190aa00c070307092914900b013524401e17484a2200c0f45004148117900c803028205208550200b4202d59031a04245000d04205074a07a20719203912050010701486e12541903500b03c0e0080091b039280414581b10303182000d80241054000c2100080d10b007166072204410b8100101002d0001c0141c446008404070980006114000406484000120801085158440041c00d248000300401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 127962697 1250 127961447 127961461
    0x60103030c050d0305060f060901210b010f0201051e09030d05040309050f040b100807050409020c010903080f040b041203021b0a1a040803071b080a0804020307120c23030303 76
    0x440c07a41c1400c9803240548220000d14901a001c0d05019220080048000120301010b20074650030001000d8104890504a808240b40d149031031701111841460201d480000c01001415410841060380c1c110781c5400c0400401c024002084840200c0c0c0300301004180d00c81022443c514081e89211001c0107240000f484209a0045402c0d070881c0c8041d2031081662040c0009c100484082c40105600124101d180481303c520940c001c0343d00100505081c3d051680b42d00505003244c110007841a2240c0d910f201000c181070300052025030000004250381c08601e0581d1703d41e54a0b25021f080105520303511107410602c0f9029070103403a806c041440c410344098a11200860341c6900401040e10080c00000c40c05441074418041c00d88141e03041120746155440b850b0702201d80300c61455401c1c024140e51071601b00041c4d049130043c009940c480d0342d0b501a50405004242c01c25441e50700851700c1c1c03003003005058009086125880215030384401041c100c00b003955405002e403030246148a915000000400c140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 127963947 1250 127962697 127962707
    0x702060a080406110705070308030c070f030e150405030a031d131b020a05030f030901090803010b0a0810080a030302090409020418120905210106030206031009050c03040812070c0506010303 83
    0x40b03240924818003440004480208952248100260898000c690144041540400119000300c52501101e20385105520303000b085143c000c4c0101d00003a1100a004014131700a21a004407900f0089010324160ee06030010f5525149040000c080c0184101e110720042390b054041400040060950121500c00600c905c0040521002420030181e1030507803001010f10024603144442d60140c0111b113042d100c03801c0404180c0008100280386e64030781c4480000a04114040c0d4001c0260018003600e440c1c420b80702074100b0b0801401962941650401001109030005000050b1901070400503030b40d001c0c000108002c0c1040f0040a1b411600b072a9948444034004501c65002c41d0085040c580103440c003250807541d0381d00d04d1003240d03030080d80d400000f500c042c98003800440c0302c44503100008100356240e0203e03403e90021a150051032250f00410011008580a0b081d44220f00031140d40c42d6213015950307001c0c103015a5a9001c0d80119400c00155200d02030007840b0031240e007101c00c0394006d6941e4a0000d00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 127965197 1250 127963947 127963951
    0x10806010c151d061608130203070906150201110406051e0c0705100309020915010216090204090b03190f140708030a111518030d021305031618050604020702060a08 72
    0x3543c01c51500e40c43c88442e00415032a0140344240301c4550400769480c411070340200c0141c0704400c11200d54211170700581d0304004030002005041000301d40d007841c0c5034419041005050100082da4181404105844069411902921003d00b0300a445042150320300c520f01041e1032030028025070003d00300022090018044c0d00320317181100e0148803114054421410f4a0303580900941106200c1e0118070b4081142182d80907040d0306104503044900e8940c0e8030071040c0d905501009940394000303030501035072070305000324642101c06400510104070360b0301e10285c0c03039903240380040c110b40c1541d208041009040707060320042d0324407802160790058484c4031182c1c80f0791001038150041030384c400d295841d5140200e4a04404806203128184955803103035022500c032050729103e503160004008048030181c852019007091411442040b41403070a01c0149440d0864150712005001c0908100300030294404035000f4070035420510109854070f0710008a0301074040e03904000c0d4402d40200e10845643d030702603a040c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 127966447 1250 127965197 127965221
    0x4030c050901060c0c030201080a0f020304030804020906010207030818011404030501020405011205090c210d020601080105090303060904120c060204030807061103060f0105072a09050c0f09010806010c15 89
    0x811103036030710300041c0d130501e481503c010514105014100301541c064844160300000540f0081205400c1d02ea45000b2648102e6003100490441000d0005608210b814254000802e0001b08906400c0d40c0741c0b1162405a8030750850f41c180001200704140e40319181000e801e16410306e041d502d80351640b400c2c9002c1d4116001c0c0d540040c5004e03140b003044a040d40149030180040d80e01078a2070200100034494500300c8030050072440700c4c4420401c2040c4c40d0400c80459180010b50140039a541450320103800e4810181112a45620610502061380c2e15021560307002944094595480311140030180c0e0f05c1c419a40e8090030091000c1000024131114900400303540c0c0c8034120800044083c1c0b142da080c2c90200341c40c5c042c3c002081e800000500d5024000400b03d03103000d1162030701106211100142e40c0b00c8410007030704009081c60010003003100c05000f10364202407103072140d60410b10030580042d0103000c0d18580d14100035012010a900c0d90240c4021448650000e0b6240342a407140c3c0481f00107003080240d44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 127967697 1250 127966447 127966459
    0xd020a0908010b0604030c210804080a05010b040509070506070c030501050106080702010e070312050c010f05090a030f030e2e0c2106030b010308031e100311240307030605030304030c05 81
    0x106454500b02c411901541d6000c10720a80170340c149121030301c802d120100c9489600c0c1c901d0008d140801d590300c000d030001b0710180c0007e0408044519089007541e500000c0b0038015803d003000c0c40a40d00d00421003c041c2c42003518441d860714041d09006071281c00f9584050007551800d400450480c0e03003c541c8034031440403500240180c1d949001e106960300c100344030240485402030350081400d482140100b444003426400814403d00300c0110a0860794181d80a201d00e5110808600c101030708001c03400045500707030808000c8038582e8420191601124540b11581280b00359150200203583d290310800c0310b0111004004448541030080e1007100183d00d4180300238081c405100b070750700c11b900400703041d02d900900301c05082e461941e071718003d038202a08030400d0b0701c410703000c072265a1100240d4510612000014074109480d504191005114403500c007030084c0700c40000c40458041c0c24400070400b046111501d80c1d00e543d0158200c004150030f400aa916000015000080c004d421555006843c1d0440b20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 127968947 1250 127967697 127967711
    0x240509010917071104180b1527060906060705010c09060315180e03040302090a050f1305190501060b0d02031e0912090303120406020712110a020906060d020a090801 72
    0x2400006020f9400d0003021000c07031003000a00790070280c0103101c052000c4610b002100d0b04941d03038290840c5044403202001819008405c2913031810449a40658114680c0300c080c0402070010039449007002400680613002c00c0c00410160340340e2108486900da0004000c1008660300c1400603e01443d034800c120000c0c0c01d00041102041d00302e920f80044540ea10b032048903032002d10600ca400ba02d0028480040d50206000c00000358681c03000035407083d000840d000074103180a000710100124060b010b40310700c0e4a00945200011070000380c1099000343c03010020703100d540c10300e040c40c05050740f500085944240441c0c0100c0c000c0007500513600410064407042c546500988040303100520071641000c13250300240c2141c00040090005204144c0d001d802e6900d00002040c0350360503107509490031030309168001060801e2002e403890b100805419841c094405980c220303c110303030381c1d40030200291107500c400c00800c01541d031300d80c11201c500038042d4080d500d40c500d010014260381e13160310034032995500b0400703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 127970197 1250 127968947 127968983
    0x22021e0907050a20070801050708010614070807030e12010606020109050c0906060316030219050913151e03050604050303010305060c04030b27251208072405090109 72
    0x10584030341c04015134030540039280b943c85418500c4040d400b01c0f0064000d0000201c1d8895003030042920a1f4019200e9110035454500018982c100b803010b2480031078800e200400000f401c0c201103ca107990035103042461703100340d0790004a4076407040111405035840d0410001e03e980c1c06400c06603000e4020010307100c100d100581807140c0840100d91086d88081e01f000010760506c600744400900304a6882d0050400c1c01214440408150079040e01e40844d2001c10030001074a0130202c7c00200c3d540c0160b0030f201c0401140c0c01064610614019643c120f1400c240c000300c403e4200301800001d50b00b20085070307440c1c00c107820455202e038403c0c0400d4501c0e016240c0003500a84c1c059049038100c0340d012440007c6035a50206c10b5400e003078280440645404103842169012108105900d141485d120080e4610300161042101c20001548442c212030300d84404200030540c00d03030a072201e40d80c11082ca41c00e441c00c403524800d6449803061a6038a00c9181c40d090220301c00c81580315240c442e2040c0072000280c48844 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 127971447 1250 127970197 127970207
    0x18050606150903100507170907030611120a020a030e15061002070602060a0c0c02090a0609050a06050a090e21030a0b0103290616050f060105041422021e0907 69
    0x2e00d00c0341e01030784452941c0d40c0c0000e6541c4400e5100d11b551802503058131951585642040c01600c41d985940e00800c01401401440d05c00c8072003412071450b0040c5412100740d4400b03030817400284812001680810044c00c0c0318001e80011012074641e000361207210322180812440a041541c00900460301100c28041c0c2d0b40c00080c101040e01c0c04d64004100c15500c24000202801d000038500003000852140c420051f251083c00b07034001c981c00b00021801d68140082101214001400e251440d41800740070052a21824944410354004990100ea00912585040d28085042800039190107481e84143c034040c11004c0914014403421400b4014100040c00440540c1c00851000315140d002213030395070060b4102c8800e03859a95019142d0342c10701e040ea142e8001c50b0724003003a01b52000e4014200b01d403079100c81840b0302401b40c682200c00b0056005801c0c0d4280320b00c10000e00031030a5203240070f988404c032a45003030318503812607000f003200407074050400d65942c8490f07503041d81d180503588100101d09468001c0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 127972697 1250 127971447 127971457
    0x10603120e011d0609060408030a03050708010620030408250801060302090f0402131a0a080d02030a140f070f02040b121903050702030a06050405060a060b0a030f1805060615 76
    0x1607589040b80162000502c1c86041008001c3e60700c140100003458498507083d003d400201200c4000e981c550781d0020b0080e09840000303001d5420018800010f01181d0340180c514003000b44403494500c49841202c0300300c1c1c55885180c0101256101d0100c0b014129401001007801c0e0b08400304a60940b50f0340e90303082a09a0f0f00600009520500100005401d60041c108055120340028880c2d403000d410b4005040440b00c441c0b41080c82d55502c195203d00a05040c01024002d20b0b011000303240d0b2601025000b5120301601d04a0410000381c1c40c0302e40e4200c0820740070f485007408908105561214180f40c84422410501e004038040da041140e00303000d0340380203510714410b5414800941200c148900682c10b0316030b0f0703062040303041c8501800703500c01503281084a140218030441c070002d580d05150030894640b4000030304480f981c50074404180444c030040016100c0e60942d0341030214000c00341c035007007030041d00360b0001c6007081c3c1e803248808100b449070006505c0d00410040c3e03040c980202900040910600c24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 127973947 1250 127972697 127972699
    0xa02180f04020f03031606020c0123070f11030a0210061202030a1202010609020c06060103050603161e0306140a060605040e0118060302060a0504061403010509180f0f010603120e 78
    0x40c08002005401c044907140309160000781502e1500b254070348686941100350a064400f0341d4003242850051009100303201e04044900034001c072a0000c80c0044441d000020300450401c070841003038507040381c055800c400000c1a8042900c1c0c483c1c0d04082d009588856525441f4403007424100000707481c80c0142c0e40603280c40c1d00a0040d0046a800c1d40340e4020362014001c12004541d82d4400000f1204801e1000d0103600e241000940410b00b4140001400e980f40541098442d03000102406404030091601da02210303040c0388890084080c1e480c0e280d5484103180d10107403042c0d0030407819041700c0c03d40404842c4598001141000310342e44815084900d40201c0c01540d006c15148401803242254100303103041c2c40a071402000ca1810b40780c1d4082005600161440000310310040b0b014080c094000c10503800044103540d000d404c1d036141c0400501c40b00d070054170f49800910a4807181242d40b005006000b40c0300ca05008032490301100b207403075a0090107203203c191030b004105e044050702d191107002c0a021142d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 127975197 1250 127973947 127973971
    0x11120327040e010902040b06030708240402070b040209010f05130e0a05030406050309060601051303020d0f02041b020c0a060e061804090605010e090106030b150604170a0218 76
    0x112540e000c00e49038003544064601000300c0e05016032155101d010340030715681d03010004101c3c5a0030b8814403058403491004284615014800c20121507401910140e000c481c18000e540b0b10300da009602c0e41d60424000c4502d401c0ba000090707010034042c040042c00d0080e44243c840440a030780c1c4120307a1941d081c00b030007410b600a0f640c44613112880c03c0c0c1d40111484c085400b040c1c48031360800e652442d245030303c140d0110020441c00f208000500e002408002e90000082c00c0540c0b0305030030400802031a80490000070300c108170311421807003444a0403814808007607010340100800c2c1c402100d0403800074500d410050040c40390944000c143e08140005c402165520340f030b1103a904020750200081d503080032000081c8015160061034550b501c900660f1201401040001100e504017210308020200c001c0080c40b690381003100405c0041c0003084859806800f07075541c685a0032107000003400741c0c415980001d4a00c894191001c4030f004000c100d18060303074800ca40040400e2038880003062211012030340503050b0300b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 127976447 1250 127975197 127975207
    0x3020105030c0c010e0a06140f0603030702100507020414090705030f0a0605061f0f0305060d1101230403060209030c010206011a0d060312200109050303040f05070305070b07111203 79
    0x100303004050041c00c3c00c40800812075143c01c07100c00d03141c0041c5c0038058842940f203501e01281c10341001e1800b038002081001d06152403824001183d80c0e8403c14100034040c01c24880018007041c440d005032405191f008106001440e5150b0140104400030f956160190141040018061900143c1d01a040385203d0140c085585030381c80301d0004040080460390441c200700c90104580282a4801c1c1d03c50708a916903a00c440900364005080780c50003010f850045000c1c000304000304071030001c000011002440c2950408120307100c5081800c00c50750316a401010042400700822047c0c1c2c001c1d0103960020b600b10744140211310012643ca40317080c441c2110910b5010800000e0340611001802020310302440401d030595240e44a404148c42a15040000781000c20001d260890303151103038003110410002480207483c10b0b1907140c0c130303440301130700c0100000301003c0d1800401c2018000d442c000c40d0010b040e40e001d159178400d40010780d48241c5045070182012081c010503441c04e180c03090102128100110301346 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 127977697 1250 127976447 127976461
    0x60f14031b0f04061803021806031f060305101e051e1806010902030c040e0402040e0a05031305040207080708090f030706120e030a0203030721061d100302010503 71
    0x940d10280a90004902031a09006406034010051500d00c5070340c0d1640365036915040005082c1c00d40c04c900030f000302122040401c05656218008201c491010401e0f505549454000a00e821100025800c0d240b8003600a03100d2448164131280480e0b01440a455800d140070900e00b0440da000e0548031405013089482c940c40316040d5010551008581800702d010006941c0d0010390341c8800c45480c43e203040000410000d16209100c000d0061800d0a0113605504141081d0150340c0141c0c05a8981c43c06100001015941c0365007116442c0c103000d80956100c0344041c20002d072641c0c040c04880742a115608030000e140d061505c2290011078000c0030060805816070346082c21903021405155100d040241481e90070783d400c0c44402e00605058071005142d11041d081c0c0c1050310651990804581c0081c05080e40300c86e0084220396106059140c0303030415100c0a000c1c2d5040c01303625241160403614004010801000c1a410b0303861189407502ca0003050341d41c00c903401001141e00d01009001a4041c0042125 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 127978947 1250 127977697 127977737
    0x10b03060115021c140c1002030a02030103060f1a0409030512010303020c010915020601030b0a0f060e1b090a0611031e0301061209030f051b061618030507030305182206060f 76
    0x24079a101b1003603074040140c0c140610240c4c1c01c02e03200080c2c0c0780e48c00001001000000c4c1b080c0204e0755541314041c0900a0b402510400300f03024151410b000324fc58848000400d4814400c403a504107100b50b84070003558403400e00942d1441116456404219182004221010070070162a084c9505130b00030452031b800c0d6500e201c0d621102404822000f9180c100d80010004240107000103842000c40b0920a031601080417501c010755180c0903651864100031118590b1268004071054405600f00741c280c400580801c80d00e0f5210f2054030901602864a8054100d8074400081d41250b0b003560310f00180e110000202000c840b01c0302c42c010007140a58200e9004240580c0140c0200e0841c0080d0704401000126600e00781641107401c1c000d05071500780001c071140c1c0c200e120711071136640c0f10514030f401900b140e41d01940c0d400340e070202400748600403c562011000190701241506009480c441c99405024101000c1c406620400003030282000780108400d889502c208402c6075965036520710f07000988ca000c02c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 127980197 1250 127978947 127978957
    0xf030c1801111c09032004290f060f070f031e080711010204080d02010f1d030d0f0f0903020f1005090c0d0609020d0c0f06050f070b0603010b03060115021c14 69
    0x2405410000000850504100c0c86d80c80d440583c04c04c0c650390b0308802000100c500c0402401c90f6402d00450341410441c50200200c0c04d440c00b9950030b002c5c8660140001c0c16805043c90354501c1600004c3c41c0e07410041000b402400c224441c0d00c880b641c0e08100104c07900c60502c01083c0348000361240b000510307070b40d10039520302541c0f000c02000180b51079240d41002d41006554142c400160791101241103509400e4410300051499140b40f5040d81c0c0a140d102580780c0c403984020700c000940342c281505c035021550f48017040b190105001017003416030503d0043d440d000346035010491303400341c01d03c040751898a9010712445225401c000d01824070003841001400c900d40e001c251600381c0d40b240fa400050301c64001c01c4d55100d0040003800301d000d00d000105040c41b64250441c0c4200030007882810320004011060345c1d41580d20600180c1c040d41d4a5021038010034811445562500c1120000a5050208852000d07660705603400d8502c4503003164029900c101140c01d2850004140d2003c506402c99204007901f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 127981447 1250 127980197 127980253
    0x606070209100e0a1401050604080303010501051c0906050402011806080c0a02070308030709050a09020f030c09030f060403030c12060806060108091515011706010c15020f030c180111 80
    0xb5035256840001010000c403401008699910f030b010a1103081680707450f004100c100c136164a01802d01e008941c40780010b1140906211000c206d4407803801660280e03a01c0e90544460400c00300130541080e50240200352000e902181510609400a4800141c03100540e105505c0341240f54844d9050a0001e6200301c007001c0440c080c1e00f1020000410300c60086010303030020fa13201c02c44103040400300519903d1580c8502420382c410002d103560518018180c0340e000c0f1407040301680b154450300209043c6100c0c40d40c0c0c45070302c0c00340408000405405900100c075030080c56440d00c000d00c00341e07a2040704882650040308000d600480005405600c00c42113913910200e48000c1e0f440d46030148006d00c0c60254240c81d44040340008107000b08003543e0209840d486400e4902c0001514106400040e02c0003148102c050700c000405c8514104d500c02c00d030100c84c0a00b448242032a504e2a2088020305240c00c41201035619000504128005611504888a03070054020103450034081c00b40043c5d6116040701200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 127982697 1250 127981447 127981471
    0x11a090f09061b1b0a020108010e090709020304060204090f0f05060301020a140714160603470303040609030204061212111603050604060605010302180405040804030b160212030606070209 82
    0x80400c0c6030750690001d400c2c0013018010002e10300103200141c8401c04c160440c400d01c1c02e48000b08511007400040c2c0c08207d45d0070314001641ca4139107003407000180c41385404c510400707070074850440a09003140c3d1242e400011215020006034071341000300742c240d105100312000040c00540d005103114103481c0003010900c1c0f04645150003101c00030b1b401414410700006c02c2081050000c401c101968050092049550710041258480742113800c000c002c18181c02c03007030501aa9020080c0595010050104803da100101140c0d12156140402404458940800c81c0540e003030581c00603568101c034040c1400ca0380c1c031910006491094100c1101c494801501070b41c10b40c41900034024a85048800d01409035001354054545854581004000c0c4d41d45640710504251040180f441c0c0041e4440c00303d15004c030101c81c041380c05c0c1c90340d0403c03a000340500c0d000680300400000c1400b604007601d9100290340c0000c0e8003940c146905a40c0c0005071400121a00ba4100d5420440200107190461149508c6803440d500b13 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 127983947 1250 127982697 127982707
    0x6030c0e09191508160e071b050303100306060e07020c0108090a0821060901030506060d0303060503010516021911040b01020316050c03010605030c030d03021308011a090f09061b 78
    0x541003901c1a26508403694042104203004403a8180403054017a01d0905403902d5251400100e0f08124100800036410892a000b444008001c03881080c8a540d403c607080300d460741440c60240180880320702c0101c1d8020b01e0300100103008410011000d02c9007600c0d401400d02e0307045c2c8000656040c20010301c09005c501444100c41c0001d0140780c068182c060200e5a810f1010110a01030030b446c4001402040c0306090003001000091400103c851380007a050794948101040d80c602500603200d142c2280742c1c107500301810041040200c1400030b41040b0a9800c9540c0b0031032498206400d403c0c850406801c40030040074680d190b090580050440c01010310450b483c1201c4540c416066100c907110440c0e15401070244014240b400340250030250200310090120301080310006507440809003941000e250700400c0c4040303c0300704c540400b40101030b43c5000f448072080f07074400706015003c8040c860344224410000300310030329803040741d4500c00d00c1c00c0380040040361560000060494030154002c5400001002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 127985197 1250 127983947 127983991
    0xc080d1d010509010903030506030109240603020405090604051e0303040318090c0e0306060a081513050f03130e0705070312060f090509070803120414070e0c0c060106030c0e09 77
    0x11803184140076400000600d17080c20301e001025210080e01840c4260b060280c160301051800c100d4070741030021503049551050400c0c0300140980f00c41e5001075841842d0004212030b190000c82c0d45c034030841c8207009540003a05806c0c28224601d15921aa48203648280002800213004a600805400f84542c000049542c2c540c07091080d924070310b6001000480c40c00c15485070781001c00c00150009400c9400900380c904100c0e00a50383c408a00140f010b1550070300c00314116282010f421062203030000142c039218060905410780e00e07072216141c540d01c8040c001e0f0001d03417a8510b02c0d030323240540c0303056455526001d001c3e20708079907003640c031180302d202c2554034000001c00d03007810980c0e00e006000f030403004100d0f45004c412441c105152640400d015800030040ca07400030f0620354550364041e500120829410540c042aa883c1c03070070981001c200042c002c014003c4100c00d0501a201d9a0780c6e0310111b403000d82c0c030740d201101500c90040d808004525003000c3d110907485c0155907903034030107007100078840607422188d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 127986447 1250 127985197 127985201
    0x5032206090c0602030a0f0e010c1106040f0e0f15060a051e031005010e03061018020c0a0b04050105060f0307090209010c0f03030c0207141503060303070c080705030d0c080d1d01 78
    0x180c40b843c0903a200151b61301107150072103040c41c2d25a50a00701140103441640000c0c0000640c0c1c10001d024914a640303010b059621001039802800d0400680c180305a2a0300724140d1884003070b0344648403810440000355034480d000032451521200070b070109040501c0a00c09551541080c040841201001d10308aa041c580703450103540714034041c91003511168076100015225100081403180240c1142003001040c02601803140c088845151641c10403403642800d0b90003d01a40403007511303e01171600410300740324925900038001d6000b00c00070801074545030100603182540801d00780c1c040d000420704011040b026405405041418105110180c003607650701c906041e00090114007080d540c03900c42c4c141680c10040d40003c0d1543c6510140c03003001100000e1032101d800c40860000722000000900540c03401d02c151041e80b83d01c22030300a2102c0e268041c80382c560400d030003024081d00c03660074080070b100e22a680c24104aa08003d2861501100607420030103045004d41c0c0c1e62048000030750f0410000c0c1d0134 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 127987697 1250 127986447 127986449
    0xc0a14030306100908070b0901050f030a050a0c02030901140a0912080304050601060503040510051e0a052409060d020a03050f030d060501090608130204061208071205032206090c 78
    0x8102556491508200f001481d07005080b1000030001c0182050020001c0020250240c80e031800041e03889488000c0102e40c1c81c414140c070580c1002010062200e012001d0700700a02400b46480103010402400c1400c07642d0f40141c042c0580001d8204550b4991071955400802c00540c1520f4000602510342c0c200d8881d1100030320341181e900303d00104000600c1401d225442c013606080c5421455404c1c86d0302c030150364040101129084170303038880c00b18078842005204120300d40d100709403441d0980390407500c49006140888001800072900c0f0001994402e174141582c5c40750a0042c03a8031140d444030f200f4041c0f001003038101280c000c0310f05800800841c80401404251005540040da81c41207512090420355006e64001c07810310910440600002c0c0d0070885040d802298404582005002070000401170403540d0305c038141c2d030a041c0c400c2c0418080313088000c2000318040d000d851352424047c2c80c1281c861004450b0003640300c0c4503415004124402841c0c40c1c240343d024440c0401c171541a03440d501d0b042061 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 127988947 1250 127987697 127987733
    0x30e060903121206010306030305030a05190504030c05010b09010f0909020f06070c0906150f0315150c05070f0b0702060d140106090305060609070e0d020a09020d02120901110703050c0a 81
    0x3c20001e8119035684040340d4030920a180c14000c8605d560780c050000d01000d44400011a101c100181e240010030701e04009066544c50b0500980c14a030501400441c1080c1040c0e4465007041c4400d5850300b0005007035412103901c81840d1040600c1c220040005021030101240c0c01000b101d1143d440d80d5416020f4254a030140800018103803401d4000011944541c0c0f10b8038000c80045c2941b40941c1c0c02290490200c10b1901340461310300c50000110114404030b421070203001c42d07140b0900d140302e81e009103803200b503034402c00480740c83e07985440030400760008510811105120401008005003810005886160a900c10120300c0000d84071b1b08180b419026080300c000980090000c1040c800e081014582007501030758142010305260078003c20111116030382c1d0380a42075980d0f0030411900d0f40c541803401050300840840d191540e50003020040e600283d98115129480790206054070340620541400d0740c0781d42e84075442c040040d5420350b00764000b071503408224000d40c0320440204403411440c03804141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 127990197 1250 127988947 127988983
    0x1020915030610020a05060f131506090f0e0a06020c070e0103120306060f080103020918010f050912040b040e04020402091c03020d05070302060c03041410020a0e040513030e060903 79
    0x1400e0b00c18814000a190f03020b00455001c001154041070001c604140c100410100d03290680e0b4421583d2000c2010955004082c03503454010042c0d90ba20348d0380868242d0f09944803d00a0b02040f5840c00b081d40c0c0343d4a1a20103e4010a01c001c00103003640e401403203012600c038117503030703469541d0a490f40c1074510982c02540c00440b54070700c0d035404980c988100c902030189030400a10141008000500004050100900030042c44010441ca0a10103a84c200c501c8039410080c40003420760980329003c2d0400307070b40b103202510178240396507050904d034802e650070740303081d0540d8a0800707240000941001901800c01d0fa001603080141c5501a12140c3c6044540040424070310b50701e840c6031400074501a1030400c01401c20070140302c0d440000741d004c9841780e009071019002c20380726102c2d421b02214030400d40940200600c2000c211140040d03403500508030204250721101d9140c50311000707000a0b80e40c01c491915408001c5404400080e0284844550420000d000c040c1003421590100e454040ccc0c00600c481842 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 127991447 1250 127990197 127990201
    0x915060a0908010c141606060b210705030405100f020405130203100603020408030f030a0e03070b0106080604141f0819110301020a0c021003090501061d0a0c021e0102091503 76
    0x6002d00942c002815241740981a604460201242ca401001c61000350f410b103490760035007071140540203940a405120783d5a582c41d0b52000102245c0440748801c240341010705c0000811b414000e1060381d00c526046800752841c00101c01c00d4030010001d1003038205400b40c0c01d00000c69551039007101c1e400c5600002d1130041e528145001103545e40d240d298080c50401d40100000d011070280402590030b0b0016194202d40c072a00e40030030700c8003c1d00300042e0f14100c030b00c0041000000cac000021300c0709048440988030b003c01a200e44090100361032054824440c2d150b07803c8007180f08078580701e0241054003502e500d10340189468280040c00c0c00c402c0300c0750701c0d280d0b009480004284611907070740103600e00e021402146000744161024154005a8201034420140341c28031440c6580030350006c0804c40da12100070400c1c26103400c44014140903151041c01243c64a03000602c0d150460b12a034031003508983c000748036401554825104800902d40000c0d0a550280100c0000c5d888400c10b00c6a00d60800301115140c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 127992697 1250 127991447 127991459
    0xc01090b041a0610050405010c020103020706020708030402010912081e070507030506061002071406090607150c0305070e010e060307020703060f05090d08070c0f060204030203030a030504021e0f0915060a09 90
    0x7025020f083c0602c00c4a85900740e2006941001c1190100c600c00c3c20b2240750004140016402800b509102414660002400a04201c100c3c402103210303e201340c0360040743d2500c4010a001803a8199001840d02c0c4081001d03201455030000c0e2841850350115080745045640d942d141c1c1410b805501c21a40b503488a818008a03141060144202040d00c1c8000c01c0840d242c10803400103501c85a2016000d20000a400a951b072651700c104c502094001000c044103031640b5180d00000d00d5024022800603240001095089214440908039200d05954031044200f0401c1044984c0d070000e0034507002c1d4450704078000001546401030000c926019900041c50f883c1168015041a4152700283c0400014400300038650360007810451172150041301d0321040c586645080d800910840e04042d5040c800441c0720905954150800d0b0302c04c1c1d20035200002c003800030503410701c55130503050b07846c80e0f0010018100316140d043c14110564070076207403183d48450081c00d0002c07541035030040450000048190300309000c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 127993947 1250 127992697 127992743
    0x606050d02030709151e03060501061b02041a030a050f1011040b09010c02091504060b0a020d080606040f0b07030201140c1803070e0a06050306150d080c01090b04 71
    0x819094a00c0e9140018503030010b03031180414021000200e40e104800d00c0401410243e0a003d411480719401695070b43c550340301c030090594802142c0c030300d00f07207000450000d00c2680c2c0c00c82036590034000300b100c00605508000180100001007201580c601c2201b00c2c159904005002d0309034000c0001e4443d800c00c0c0080c030350908a2105040000f6410115980301d20407103081290211601c486040d9190010500100c0d0000e0f006900a03610400b180e00740f00240c0c50100408100ca48202c404001d0950f6815000d0741c20b0061040a0380581c0004d1720303032800300f801082801d0340b040d40102441c3c50310740c40d988001d04504043d08207208801011804104042d024803540c2c010303803490407030f030407940c43e08160001c43da200d51115180451010348066896890070000103001d041c40d044484414a044400b0000900040c45821300c03074401c010118810401101e00343c582c900004e029843d101141d921452083d5001faa0f040c0c00665880f94150b001ca01c01c00d403c940150320a6510307401610380c84101c1c80b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 127995197 1250 127993947 127993949
    0x609050f07020303041205090307090507030e011a01050d06090c03020306012622060c0f0210020304020303030609040c0b181002010b0d0b0711070f030c08060c1e07081201030606 78
    0x401500c540140080180c000050381d41c003a0780000100b00c810320360402201c6500440f0109a0140318860740400c1800d2140c000d1403180515640422030038020f840024240e941200842141c040d0719400030b040c0d03510420060203000b6094001080d11540d071090b00b8103c6010251000019a02205011056030300500944020720081d10f0310401c0030300a0903403242e4240180c070f1403401044807001012800014620801d0894001404000c0583d4499000d0488205003540000500075103050b14125503161013034038061a0080d0045085603030301010f02010200103401690059074201c000200e010380c84004000507a80d0081e41941c42c901d00c0700703129083d203503030740e1010942e41001680303076080e00c0f1084803401c1c141d040600314a054544500c261480008184600b40c9401817040114076038040c2d140c0c003012030388210031482d15156640c1241e612900c0c1602c1c40d251068003002040c17117500401a28080412090405a144c1401030761003010319803000320031a8003038019400420621000c4c0c03203504 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 127996447 1250 127995197 127995211
    0x2160f06060e1005010f0e03030711030609160b07050304030c0603150f0308070605220b0906160c030c11060a1101050901360812040b060a062a0204050a060905 70
    0x1501d1800e202040f0288259540940fa041041030010604854410000c0c01c91200003d000c0e00e99603450b604100c00ba80303c000800500a120f2075001c0350790b118000858101c1c24905415950000d03042c02c101e40f43c640e1003410191418481844007102003841c0c02004001031009803400500c440c516482900c0801c0160700000090084600420114881c80101c83d42154044d000040a5075180c41b480e00703607403050b040300d030400c0483c21002c010004080919030080c0481021150281e80d941c01d600d0303d04020980410014118245100000b80188620b0a100d803040b8065081035008801140164000014000005007480e00141c3d85480138400c054100c0a900d0003031203500680c50100540031240a0141d10456101c1c4ca26900e040c83e10510400c0654031000d815034460410a82c00c1061106035070170340d014900540400c109240000302482203501c25120703244071004c020a00800c46401c40b0956440b0445111400c0050780c81d480381e544518000d10000801505001c0c160f001c5400c024a89 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 127997697 1250 127996447 127996469
    0x70b030a05160903030c170f040e150117040c1a03071116060e04060302090a090308090105061c1109070f020706140301140a030516052806080a02160f0606 68
    0x7890342c00303070302c148404140ca405042007241e0580c5440e143d4285e510141540f0401e0340c0c045204800350b0050700007402103400308044c501da6902da4800b0303000c010b1030180025000c11340030566404a0024a00c0c6594014064120520040e82d119000c1c40c40221401d08484622000820800e17525001200b01a0045000e0014101c029080441e1946001c007401b403c01441038000303140f80c40c2e685a4000794090b40e800340504085080c00c202900144c000100c040340400d286030009288882d0510032107100c0d220003810368040500c0f6080c2d08185000c6030100351008044500742004a486a04002c0c1c05010203559040145041d004024100f02840e0008030800c011110000c5c00283d413402621f0540b1500303000819440300140000311510480d03480100940100c0210400300030070b0040b00e4048482c1664100314060303d41c00c402c0219802d1000341401c20f48031071818072000d40300d4003030139902101904005146c805588000301040340308a07801c45141c0340c541042020000c550080070020000c84101c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 127998947 1250 127997697 127997731
    0x3051f05090709050910090503120c0a0509041e23011401020c0f0301090f15050c03041a0a061d1905010602030412030516051e121605030c070b030a05 66
    0x9032689038041d611410400039100d0021030f24130b4006020413a4480c11b649020461402d0900c1c106841f9000740210481135641e9030300241d0700d000420103c0e014070481c0d9846514000c40c0d442000010101340041d0401c4143ca101d0b10000304000c1d1150800c4d200d43c102042c806046a449078401010058100025501d001d414050290b6000110036100c0841110054840e0706500c011030700621132168080e0402c42c4041482c410710212060803038410311141018800c940e0b40170421140d921040c2ea00400e0400100c00d0298180460880503402040c1d107480819540c2e60307000365090030307498103903d40041c41c104018401e00c201c001808400694208100707102541c58907401039200d0080744103100c841d009121074001094421405c9490f0501034085003180745035182011540c9040b12015009003d102c0e8a4009207000d0020b03140c540404800e10292801c0c104030000105564038000c1155180300501c40941074032024081c0c1d10140000b5080e040e10b0386402206402a94006030070043c2800002072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 128000197 1250 127998947 127998961
    0x11270c04080d051c060e09070e01030b0708040510020c03090f041404120e030d0509040c020a0804090c0e030d02010b011b0b010306020c10060905010f1a0414011101050103051f05 78
    0x2403020108005062040e203803803042d00507004014554010070121407504002044080c0d00c41b08043c001d010303150449805a48580c8a22900740e030130700015000300d00c0200052801d52096234210f510920070410342d200c0201c001d8440d01030748c101d00d8003600c0310f40003c2810742d010301f0200800c1c1c00d841d02c102c4d0140902d04105c810f030b400d0b0351009007000e030240781c2c0724101204031401262100030b5400d02030122030150b010408001d00790340280300114840c1d400c04084c40c02e1940300090580080390000b41e01481c0c213140c812544010001c3c1140202030100e82c1c003071080c0643c0c0034800c2c0d0542c10b4054002003010340185e8001001c1008000d03207041460000700f6500041802d0030100344c10342c0d511610050391568400000351800b010103484c80d10f0340f410080701007000240c0c0e8010354121034540242c5c42e050394403000a20300384108151000301a000900c810442c440c82c20414651745a018100f8486104080d000c00d420348609030402e41e07403507000000c50380005113070385d40240c01e40110920400a80c10000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 128001447 1250 128000197 128000203
    0x1206010308090108090a05060408070201080702030903120901090302090c030a0b0307210f0210020a031206080307201302040807090b01020d0f051b061b0a0207030b0411270c0408 78
    0x501c03030030304011016002418858080110340c0100750000116151460982b510910590001600724005048400030030b07100d600000580b00f030200300030045d20a28941840c1c06d021b0760402071081e810030520801c00400740c0c4030705036501d00078540c00340c48c542e0744d2601c0300d900426185d1840702d441c06503006580030800c844d44600440030f801204c011500d08002a400d0040050070b507824041d44c4001e03140880d041c0140c0006807030b110705200c2d0700c030044102030280c00607040345c6541c440c1160981080043d41300141d02c051000c0c110380c0b10701c0000540c6540c03000109a0100d1400802c483b415400079040c00b444000708801c20080452620601010300c1c0600000c0d03e802e4808190b8040c000001d01c240d214a0150040d680d11401c8180454910740090b07044030f0340c401c01030f50716404d801116110504101346610403a0300510060700103102c0c040c0f550741c0300030402200034001d4540002c511000c824603682d004102d03466400c201d0401a0404440c0c00032a00540d01a2409074010030402c0100074030b840c08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 128002697 1250 128001447 128001457
    0x1906050304080c160e0708070219020409050708030406051c06120f060608030a05040518010605030c03190212060f090f01150509040207050105101d0c2a03091206010308 74
    0x6400ea10380042405040c0ba0010950003405185120040417801003c05640148901c2d09580e0b440d54070b03114114207a80f9094003203d0b02101c00d400705020800350400c1c0d0014030b40a0b01c42c10444041e15664600d1508581043d0404000500c00080500d4498510662000e2000509408110007860244406150004031038000e12003840048010140480d42e40918001c11041003500c0da80c5104ea440202140c0c01030244a03c00d0494602c186081170800329a241139440c42d4650624540750f01c6c02c0c410041d0801407e04180c1481180003600c91585400a4044a8000d8544001600b843d000b00801100d884803060300448141042081002d040c2d0142030440350780c0f4103450303a4207094100c100c6491240101c055007180c0005034200401030305605c40d070b1069410100074440f040d2074040290405900207200381014050001160300240100b008250302107208418180450302c10011003045a00301c0807452054001060360366031828003078500f80c40c004954024145e44d60551740c50350518060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 128003947 1250 128002697 128002703
    0xf16050912010f0501290c0a020906150a0206160507050706031107020406030c08190b0126010e1506061c05060d02090f010801110c06070c0204060b0f07021906050304 73
    0x440c0c0e60809020203503c20100703030708031582c00e00156071180600da0b08002ca044405000500d4010b807901c030901c016094030220820400a042c1c48400c80c0c080000c0500043e041d1907000fa600041da10001c0d0180c4000c0403400056001b4200d40d141142007207940300c2c11441802c05010080100b44001400030a41c2c00546060b03080010301c07000c1c1e0001c80d00781c6004240000f5046460501c0200c184404010410100e07410001212280c1d1180d0202c24042040c035480186000b46010060145614440c540c48800540211211801421100c0700382074809070640030410741c000d4080f9141104140251640c07004050351444d00d091080741c02c0d01018002c0c8030505c01200d90b200003140b89542c400f17042ca05082d80040980d54a030030109106084c0312020710541d041580b80078883d0b1540513652003644c80c8500403002521480d40d1300c89050795109134002302281d000f961484c02081a500c224094629050300c94581038036064241b0601041008515000c810400003071002c2140c140d00404403030784554 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 128005197 1250 128003947 128003959
    0xc0604060e0709060302010e040e10090f020301060b0901050711030102390f070306020f0705012301050108040c06031802130b0901050301020c0c010507110a03030302070b060a051507020a0512060f160509 89
    0x4041c42c0031400d00039032861040495007800d40c0f43302030005a0307140308a818021002005940d60340c4110154510480e05c400380425424010780300410140b01d452040e41101034000340c58035a0311045018809c2c18840700d582d00031001c03101101c42c4824040d258030781c10080c00060201481d140206541c41d9807511009003400c1e000580e00660b0039400c030a407035025900c0b100134030114018030500e41c880e015541500b40e10b02d000b500001080c1d8814454217001c0c603045050061010b0410b1000c038041c000c44203c0c84408032404140c1c000580381c02c0c80c170010030185040d0024407031118500b0030000000c1a441280700380e005000400c0071501c0400e90902e03884090038140d81d640c1035440c0030b00030000c80b4000103601202e190400020b05405800524443c0e00c00ca002903100d0703486a0801918400600030380d50403030440b0764440000600c8000800519000500d1080c0203642c40f0700040300c82400603104141a00f0050900c02040035054260350002c2110743c541c058a142c10070010a680030328024207108034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 128006447 1250 128005197 128005211
    0x50d030b012118050d020d0e0a0e090a0c17100902031504030207120506010905180a020120010e0309031e06070507060603060509061008030a0905150c0604060e0709060302010e04 78
    0x2e42940280681d900c0c0303241a00c6485900c0c03c00c0c54888208603d503402501a81803001842031142c5041b418220000303080311382450038084540c810020041c2001d1451042c0c0354420b01041710070035650000c09241d80c0d0303610b8505251000d9070a00c0741c0142003440e103908280c01000140e13400b060401c9440040300340e100d507680d00d6050480c60310740994041105002e000f007014061010124449051791036141040c403031600c031400054100820000c0300324450704000d00230001581310361101c4102c101c425840006080030540c81d04c0c21a0b480b802d04041c65400081c0c441c0c00b03810306009100310100d458000d1103115a854407640c3d11410010142420804002007a41c10010303280e0121029540100c820481803070454101655a501561480e0181103403820000360750400004641c640f04030b80d80c0d0b00c810a0700c1d040038003c0314002103202d80841002844001c50055040000910130350003410041011910b05004500780f1038240c2103843c80070b08001e41480540d0b0015512502c041003504c0004484c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 128007697 1250 128006447 128006507
    0x8010204061b0206121503070506070201050a080606130609150c0c060807021903080f0603030c07052419090806060108040b06010915090503061e01050114120f04050d030b01 76
    0x85c4a1586120340301542d003c288075002000c2800e2484041c0142c00300c03060346448a040040b00d008171036009000540810150f20f0031445101c14503084903000d000d690030450500c41b02c500b0508190081030000c0c041e01c00c10840d0905904001d800250310382480d9540303035455194003002c42500e0088006111411000c100c0d070610070403449104042c000030540b1000e22030310780182080701c1030741d0030003802502001160251501004944c05d0804c55002800d40034500428010030002480440c1181d8544d401c140a800e06140f00a11034882032844000040218403c0136090b550180c001300100d0340030004010903a41c01c8088281c0068108440c2d00060359000012182404075810203200018a04100b609107a0804000340030f070b403411016506c040d6504004641d0030422080d0000c1410f410800402407940030b80e4844814401840d2104d00d010969450f5448235101581d4070482c8110300700411061002c18826004405110724007032000030704034030000b414080c154110180c4011480440603003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 128008947 1250 128007697 128007709
    0xe070504030b28021b1507030e07030209090d0f020d0807200f0705040c0507020a05010507030207031704060f03090c06081503060a020304060c0c0510020f09040e1608010204061b02 79
    0xb07181035000f00103122800c6600e200040c1d00071100761000400101006203040b10045800d01e0302109440043c40250f4070340ba422000340150031458905401490300c040301503141c4829007842101000020200703880780100040c11000880d10960440d000a44200360319503200e40c0e02038200155150051304900b5181d01940b00c0301000c3c180150511a0000b4110403d4001c00c1550441e42c04070350030040192301c1e8200b039406103d500c1000b5400301c19964144411b60040c00901442d1380240f0442d04166201c0d580c2181000303030921204c1c46140302050400145500c5511102038413041e2805208414480d0b480804c04541030080205000f0390300009a590031001c0e1a009905000508481c04c50400804941c020340c42601c060700d01c0e60401c050719141c14000c01100280300c1d40a0f0081c05400e85040806000350410306c0340c2c074669242000b44810715540e900030741414041c0a005480c560208014001040400398058481640188000c100c0540c0000041810382002c08003120070203441d20000340c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 128010197 1250 128008947 128008981
    0x150105041503060303030b18040f05120301090603021302040602061503120a09050a0509070f03020d020409320108030405010e030f01091a0702070510050a111c0305010e070504030b 79
    0x841140c80000314035a542d4540c1101e01164025202000100042d0050051071b03042c2c1440e08900b00d40c0e9001140008662201072059070380100c050341c08042482e090f0b00c2c0b55501c00e0b030007465042d4541c0307018000e42c43c11010700110030000d44d10841c50715181c00c2010b500d9200041214100c00c40807000c40c4075070b03101403104c40b9098001604a5030b0700d44206d003014020300340358001c003401a0300001d804100350528010781800ba10f501d071907107142c0142480080340654005021001074580900000030203281d28010301c0203134451001000c403103600c2e942c4030040f41254a040c694141c0d00101c01000b402c00080700702e6050740d90030b00e4500c00c00042c000c082072503e0186410721603039610f0010f5401c28410007585a982e21406c1c4001840140ca455100320380e1540140130b400d0b4400d96800e140400c00d8043c4e4000d10096542c0d045c140002140300d0010327400d0a07820900e807144010506050f1044651503c262405003c0c000e0101a850400050081040c059404004c1c00c04d07030800d0101e8818000103850078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 128011447 1250 128010197 128010209
    0x110301030b15281511060c040608010e04030c0816030809150c07020324071706060d0207061e0e0c01080114040905030f03010303050901080c09090c03100b12010e0c070b15010504 78
    0x103100c1038007008024008450400480c0d00451020511447d02103045034100c50303c0c0e549008440c1d090007112213102e040034104030140000c0000220000d001140940300c1404049101c1c002074050b4100540481030040140d030403600f14003841c850070a19071340c0c9180c000ca44e01c54903a40700c0f002d900c0842c2c0f8184207071003903100c4a0349625140c6042c0b41034104c5580301d203007566103031020a504002c081c607100710155151a440796080c802403039800030540c0a008034030b001d010082200c081c0e03030112290320006050b90782100da44940306d40d08a49006c20204403450b03400e2810400d2503141190141c03898820864441c85582c40302036140a02c1020000d84401c8020807411541c1e9580d24030303015049600c420070301404030303150400168140703002c0303010780d40c05050203480000542d44414940c151580014801c2140b0034500401080d6202440c010b408040d00c43e200204003541403141c008040c20f4000c00e58014038404020850000f40204030683d04412103001200d84510100300582d01d81c05944c2060b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 128012697 1250 128011447 128011469
    0x60e04090819020c09070e1c080c0c011103070b160207030b0903030103051203090309040f0e0115030b0f06130f110a120b0118121104110301030b1528 66
    0x340901030400c841050559030243c00f128850f00d00381003400440501110b0074070100d00500048001c030304241803014590400358070403035078200c680e43d14404c10380c100c0c405a1800350302c10700000d00c2650308046118008807407000250305001159172005c1815000034400ca01242001d1190441c00303000b046030704041c3d58804408140c0380760520246550781c0092005585a00c21942c01d001088000f40460780980689070241d0b140500303140c1030001510014500c207944a0b075420f43c020040c1001c1c81481c4102d45d103c1c117440701491840c1000c15003444043d001d4211480b50350140002c559910001d0740082c400b1441c0800e0301940c5014041c02882807003104c40807031500040034901264044d00180d503050340e4840401a10a58000440b103407008981000080c070603002e01030101a5441180140b824480c0d104005001c040e580428141d43d066401c05203c0140440140104140840d00f141c2c041c0051900c1345d41004808000f402244086595000c00c40031076034000800c0d0742c04138011014005c2c58502c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 128013947 1250 128012697 128012707
    0x71811070f082110030219091508010b060a021f020d05070c050f07030302030a03020d020d231b090603060f03060408210f01030305030601180602010506010f080907060e040908 77
    0x19002d0351105211001412103211100c000a958452203806020400c1c20718103a1411a4203002c540d21003800a1191241c91110018454040b03024404c1071203400e42205520310702d000b140c1e80c25074011110013403140c5001d200303203001e065002401e9a0303400d50645192418604a10301d0500030301c07659108000b0241007204100c1c803640c109102c440740501ca003084600030526205c095480d034007240001801600704002000d0700394440d2300505034103c2c2c1c1b0840145802203140c8441c0803200d98403982c208560402e0080c3c503254a03001c0b41503500441d03074150b007403410240c401200000c0c41452613541c4600c04c00310100b021611303420f0408818000180489113541020f080000241d00a0107031009042030003036050b03810420a007141406a50240c4980d40700380d00f581d6007582d4680004001c60f040080076102e10b0a080741d01c2c803008004100070303000060a810006d00040010340100f090000b440b08000600001d1580041d010044961915101c13503a20540c0e0001005030110b010064120000825 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 128015197 1250 128013947 128013953
    0x903121905090a17090a090f020903010510030c080316060c09051309120c0305070b0618040804090b1c0209040c05060f0d051501020a0b0402180414060603071811070f 73
    0x288040c003e40203103c1100c8502248001101c58802c0e41800303034000300070410030004421b031070f04121401d810080015080941d0380b0082821a401240c42400300ca15071074040080c082d5847c0c0000240418901441c40c040c0c80d0009081d41c0c07440703c40020000c580e500d18500300c1d103100714510310240070010541e450301c014400b800005005011800d0303d000c400d43c000410340c207000d101c1545580c1e80c0b40d01c3d00c0e4140010768a46044607000200000c0e0801d582210f0220480ea584070903602c1507200701e2085446a0034501e0390811900e020030a24003440710080351520a03003500152025056044414003543da4a624004401c0780c0107622080c5c100b0b50228264254001c102d018200d108039040003080242d17a40c01803040083c09503404140580c0000e040a40030a003a0541142e205002800e16000c6840d5014002d44103101101c0070303204a00ca103a00341040d04810f004094100800318010508907041003030140580c0b40103604600b0082e5604140103c059090054846194000d0f1006e0219030440c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 128016447 1250 128015197 128015203
    0xe0c0720120102180d06060b03070804060606020a0b1303030f18060b0306060913060204120b07031803020d050c0c28060302070c0b1b0d2303090312190509 68
    0xd03640d108444006000c95101414800d4604040000c0301400c07591000d0b20500603488403000060314020348a02002c01e000c0c1c0340a0046028101c159240d0401e85480d0500f50301300c3e000e5802c1842103400800c92136021a1607001000e0308030b9042c4081e0414450725240030f4004003022440e10408906180c18a142d2564480880d400305000351414844450000c00b0592144c1e01252000d60000822002c903108106842040c00c1162042e4001480c064943d007200c3c03151010804115044401407007042060b59240c081ca440002c1c01c0c0d116182200f4075039a01030344580c00c40c3c041c3c50030058080707070080e83d0400400c000d61030b030607000c2c044041c014110156110340b04200740054650007000040003071440e10038403c9130b88164005561102260a011064595500ca900e00305036401c0da411424206035003e008229903410342d03440342d20ba403505400240103aa60000306c0316025420910400240d40400320444003440c54071452000c8541d110744040c4c1c040340c80e040d10074507003d15003004c100e0496000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 128017697 1250 128016447 128016503
    0xc030c0604030216080309100c1b0e100801050f0a0e0a1506090b1009060305060d0b161b080403060c02031210050306010504060303050913020906130306050703060303090e0c07 77
    0x101c041031650343c0d101e41000780d581c4034150207d17030400029010444900d00c10b0821000c080c0c421400c41d00c0500c0090303007107a07202000d5081800c2e030190358400c5c41015034101030013400400e0b040000344014a80000310b04114803000304003051260311a03151661b100d40c01e0000201c110391184841d001d465101c01158000c2c051030245007541490560483c00c2441d0130226500c0508155a400c0411b50034408110301801c0301600e4560840004a22040090b8600010328450a000c615061700202d81c1c200060280802c11129890200014059400b05440000310b5040d00c5d000030340441c2207000394004038918131030b86a2021121003080188511041080001011100124119085a601c0e40300304403c0b170300580f000402244c000c0019403080d0034030f10040e006200c1c916400604014081c4013080b0300303900590600d00011035a81c0c0500810010b03204042d003011440c03804200c81400c59801a01840190084111040b071110014205400c54421156450b50101074550354030b05001c00c1e900e0540e21 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 128018947 1250 128017697 128017723
    0x18050301022208070b07030f09090c0e13060513050402120105040f03030501050604230d021003060513090210080406020d0c0c02100804030210020a050c0a03020c12070501080103080c030c06040302 86
    0x981940002e40143c0001d803038007540c6422a21510704080e941e03050f20b000410302e9011041c01042d802c00166904c103441042c80c0524240c84550854844801b04611030054400d81080c46103001000c0c042519801880c003212441c50780009a031381c0b102d00005608105680001000e50300740b00c01c2008200c8943c4002c3d0f841d901c02c0d10203000350790329403040208074011030080180c062605042d040130702d200f050b01801c00c404058802500518944c02080760040e9034420180403036101c1c0810016820701291090002c5041401003000381d0031903000441c0d45c0b207070710300980410200002050900155a0450b034085119110812090006c01809080d030300450400385d1049149110712020b4901800842d842070307a01d85e01805c8051404881500250408841c40007080000c1c815411040320410090075414002d400400883c0406001c20030902c5081030400c0558000d080104aa43d03000001241500c2d84000a2760b26624981d02e20307880c6005030806064136200b0042404245500403c543d5481da00d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 128020197 1250 128018947 128019007
    0x30c04030b010b0408060a0b04241509031112160909020a051c021c0209010314070512120a1e0903030210020711100c3e0306071805030102 61
    0x3c0d0303071100031181d4001c0c0d11406145410490008944600e5070340300c400682070003840040e84c0108030480d008105c4140309800c04108041100327001200c40811a103200000600d0721414060540d5114100b01920042c468011708040d880d00007031080500004228180340c0084100c00e0b84e492010202900c040c9406a00070b040f21040820319041007806000c0c1110b8840284c1300081c015420720540c45490762039015940c08401c00f140069a41c3d4860900030b41c020201003c8490080c0111828072040d60303c1103100e4402191000701c1c03000d02181d454a0002c10110036921200380758425203401044030300c1c0004030148803d00403546074000e89440c0c20742c1e00a03421900c0c001181050b100072071080100c06000c0f00d0400c0e02c5003540d45400c103820105400310349011443c5903000d6071b40d100c0c0c0c80b240d6414841550220a51642c801c402541828503800074222000020080342000c01e454440142507101084600c2401005214000210b8002408082c000f19075950040919030078012035105031145900e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 128021447 1250 128020197 128020199
    0x204030204063201020c030f030d150f090e01021c0903171506030606070218010e070f1b020a2103110c0108010608091c0503011502060c0406110a08030c04030b01 71
    0x8660186440100c1032412000b882082003003c0240085510881d4a0452240f40340c0824540c4040c020340e005c000c0364000541c3ca91002c081c08074103694902c030f5031043e0051500010400d96441840000459200c0c0000203071410070b005025000e8400c00340d10300390569194002d1003140c2c032a940214081d90080c2d5901544000c9c01d045400800c1d82a1105040041c1c00201410b139490404001e42e002000200410f180007141da002c0380701d50f07001060941c460045079004200314040490402e50003d000d190200960114080140040603804000d03450b0114001c0440219182e2a5000000d05001d11030922580e110301c8403410f030b050b800b070012000a0350b0340d0a49500008009058107601c03105840c2e811850f82082000c0b1a8040c005100741c403940300341921518001c0d409035015568000f02d9803100d0703880d070400c0b1560601403d507024110455115000308034403101c0c06000e480c1640c41d6454007000080c0c008104500e0702103c0700d0041c00d081000030a00501c0e40395000208202e0b03200c2d0200756156 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 128022697 1250 128021447 128021459
    0x20109022e0f090501030b06040f0f03050f01020f030a050402030a020312041401020a11011b06061206050c0a02120901200606040b10050307030f060815040b0108010b01090308131701020403020406 86
    0x2c441c0300441c00041038049001340f040791300036003150903031180282c28981490780d500e404480140710340c3d03c0080c01b01c80704039040c818420240f014005421000001303510b0034910120060f51444000c15842046589030007090031541d09005855107a50018125020010020400c0843d50b10a11421000e451592200651540042440b13005a500105403243c0300c04103000540704510944040c2d0040c03802c85000c540080d0062041c400588035480045816580f0351600a0848001400031000c0e01810300c402041c5a40c000f80114582a0101e17a0684421610300182c84081c2c0c200705504040100461291500d0720000d0404d200f0281100d0510a525020081c03240e48002d08a8460010f002000003d404070300941040c0384940f04854001440b071f0352903180600700002c11201c841d184a100d014441404808045940540940ca00030861280b0880004e0407078041d0f403100a01041021404840700000614844020302031007100400c2e1f00b0041540500030741c840e000032441035192103004214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 128023947 1250 128022697 128022707
    0x609061b19020102040b0412050c0d1214090604031a011505040b0309070b0c0a0b0a020a0c1e0c0b0706110301050f04090c0503010612051b010807050703020109022e 72
    0x8850440c0066191000c1c1140c01900c440c52152607109564080100103940000d240040004040407045a8680c965900e06681403103002d0740214481d588018800e80410140f40010005d03450700d00f880740c114251607c45960b54065814915071003039003c10004280049002080e807202e001100c5542243c0c2c889a82101c0c1c290b5210b44140050343c24041480302c19912802550014000f0089038409070b81d0f4a2400404e502008e2140b1190f08508200340801030307441c0700c1c2078102195007015402c090030700200a203d0109410064603041040303550200c841030300f404084119400c2081c05013a070b07888003d44942a8405002103a8007850106000300c0c412800c4140d0f4160303900100940e9a440c00802008082d180b181070070303540607841680008440d0303803d00c906801445244960790f6203d10034103000e8100501c2006030f50310b900e00c1004518441e80c0c010003650788100303242821074941025007030032401011a00341c000d40040700c0e00c05110b0154810003c8030201c4c0d011851080132841c0d1a042250 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 128025197 1250 128023947 128023981
    0xb0a0609050105120d080c1201061d030c1c020f03030d0603150204030c030b09030d06060201060503010b121e0307120c0605071803061a060301090b0114070b0105040b04110a02060906 80
    0x444c98105100001d1110711911817a5040307401004803500308015100041d560707000a80c80400480c02510a00c0182d84800800030340000f42107000e024818100d0010500300328400c400d080b080c00e03006004008540d1101d0512440d0503002e803c880e11480003503a00001003000f80402d5403200040d00440d100400107000315015294482c00d0781d503403030380386a031500d0301194043c0044449001c240100c05000109200e404000c2c50668004907902d4940410300d401c6503042900c85000d041c8400a0100b030300d500040103000e1f504032042042d101905010b01504602804400500304c03c1c041c20000b56950b0311408540026000d4030041086c3e44800070195901c1280040344a80003031145130800200744150b0000340e51246c1c04a03040c40c071441e04000a20140c3c001d170440709032680e072000610129680040c0c0d102c02611b05445152511640d0344400f04e03010390501c80d6038480e58580880150544480d0400d19071004000055a115607002801070340707030201100c40040611490b0009000840d04c1c82c8040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 128026447 1250 128025197 128025229
    0x812010e09030f07032006010e0603031329040b040e0609010e130c0801140a0e210d1503061b020606011706040b031504060606020105071205060103090b0a0609050105 73
    0x1600e4088a80d507000c3e916001300300d041d000c0c40040035041c0da521039400b401c0c1e1496181e0750098403c0d981410004014890050089802584140000d011683c0011107000c2650002c80c0703e4a000404480d61800c40041c0345040303503a205003c80c2c002540344031038000d80142e8422202a039102e80e036003828800018000d10800c1d01044d1580c002c5000701e00ba10a0507040e180c00f590000c440c00e6210503000782910391510f1900d1500d075010081029460380c1c0c1c0f003143c04000d00030015091030f900002080604805010350505a0140021148102251640801c1a00c0e100442c0810f4003596800c040f00117100d103c444c40d500040c5080755040c2c1600c003080d2544141c0781619000800300040070f074144106001030070190825600c4108150390390781000b20402014040b01054840c0c40c0500d01803050360301c42d034400419a81032030240b1031540c0d000480c0031030300c8011300d20000d200c0e42c401004802800140a0140c8194001c6003404441b519035002102030f01c1104806004690341e4105010200704005401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 128027697 1250 128026447 128026453
    0x3070308040b03071121130902040b09030c090412121506030608011a0a090b030a050f0d02210301050907030b09010801020a14090a0905061f0305220201021c0c08070812010e09 77
    0xa000d05401c2e00c1b0103403101400b11010182102d4640109000300e0b0f000390880c01d1100f1000c50030701d400749000c0245050440080d1010b04c800d05040d500c000d481703c030002030360b0300b0f00020364480300094415504c1502500b20030105510100d40d03541c00a802480e05006d514865400c0213800700307401e00b4000c07406140a00c0900300d110010701d40001ca900401403070800c0e6a1602490340a500803820400c955a00c0d22541c0e40680000782c841c40740a454074001d2021100840305080d07100900c110500c041d28115007040c3c800c10000d54074800110003d00d00406040d45c460400720020600c040c055018002d03070f002c030792682c600c1e02c144880d002d170b400e000d0411070613807061200f2820702000c45203801c003e80004004c1c040714180c8031988103014aa40100328000000b03696481007106c144913100d11059880180d603412000d92000f43c0000752111343ca140788500210101d4100104144640720402001313800c045c0044c0c81c0d409600d800200c90703003d1038001346c80215420000c21640c40000c1d400740505000001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 128028947 1250 128027697 128027743
    0xc080a15050411090607061d0601060203040603020d0b0d0c0812131703090901090506090f0403080a0e0f1005090606090129091804020907030c0f0e03070308040b030711 74
    0x10400030b42000103c10440781d0060003003002c0c0307846040c040d0000900c83d40e0007094001c0480503901c08810f1034111507030564000001040035940120881d020358649103005a510700c001030741c180140c4003140546030451410f00d0b00c0002c0c0a55055100140c1c4c20b0030003640d00744480c41c0049105802080e4100000340906c900410000d80152400030794540c07030750160f030f040840000c00a8102d071400d0344840c02244d11041082160f01c2c010121513808101e540060106003001e0720b00600103180200f11400302d654450071244a030070100042040d000c0d50004555048001d001c141c009000b098900300803030710460010070003505e046e030580d505850050700d0140c951a1001c009058640e0700282054000b0020080c4400c03a44801c000c19400000074080c1200d40d00306841404481c0c20700504020400d46400701100c100c40d44000783c252501080e14001002d0340c44440020301b401d44a5000a0400c40001000101c0030f50b4800174611a01907034807440711246804174015114816241e90021011000c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 128030197 1250 128028947 128028949
    0x7090b070f0c06050c0708011e02070c08070801020d06090e0d0507081e1b0109030e130204080a060509070b0c03040303050a1809020d0b0a180b1f030c080a1505 70
    0x508101400340d03894281d803072226140c0c403949501c0b6800c0b00d8005000043c814401040400806004220003002040304070b0012440d100904d88407041505c01e10780000b0480e003480307a010714a8002d02008400d603032006a454450034000c1d800300c404090910300b0701c0000280032a191041031880005c2c01e01a01d2040c42d00d00003182c07a0f030b000706030856511074240300d140c50b4214003611380c0d40b9054103089800d54076103000000c418820000c203001406603040030540700019a00116030418040700303842c1000e55299a16041c1c02a0007903400c0028540300301042d04040c043c01d6084240a140b5280680e50015281d5003078200c103101c2d6001d01031781e82d44104010400a07208400414525006141c20054440024403031034480d04198416281c135070b000b0401a41800641c4078648280c003088070300c420020b01d000c2002d1001c1d500c04140c00406540c60500c03081d25100d10301d44030002c48080120300460960000094000d0010044440008050b20001501c4801902c02e2080f80c0b115081202c03811484c00e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 128031447 1250 128030197 128030219
    0x1902010305130b13020111030a020a11030a05010f150503060403050909070c051524030a0807050106051909060b03040305071202070b0403111c08070803070507080f030603010b090709 80
    0x10744190b10624400d1110804220b000701c4013402a080f40100e1540480540001400d0381c8001800c0c000a802c10880030340d0b42d41e0006079030f19002e5804284454018101c400003030a04140310070140c00d81d401c1c504004820901e6901088000109400c4e00100544400c20700d0f5541604580080c0822400c00c4001441d281030b070000c651140c05460180d1702d0310006d03690541031542c0142d084031208000401d2110442c41600d10308003003514000e50b030781c0810b20f44c00003035500c0c101800f0240910000003249001e0010a40101010b0400a44401c0c0160315200c1c0c1c00412008520455091a00c1c4c81d0010030059030003011240215056074a850801401c0d458001004881610100a40c81046800261100180042c0000710f02803554403424410420a00c41c405155010510a424910f04a00c00043c1003070305941c02c0300c1e04954a9a2a41e40b0900305076901d21030b101020700007041c080740f12804c81c042000210b114080c190001d00014034a0b40611250b084141c691601017410048284141c042d60303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 128032697 1250 128031447 128031451
    0x15020406092904080a02010201051609030b0a0b03060106050403110303040b04180b12010b040b09160807020a0501060f03031d061c020706020406030e150906010b0307050c060c030a0e1902010305 85
    0x2e521000c02400100c5078030410391099000d54155003008404800395a020700c120356003c0d0082940203507100c120344000344080402d000040540f4580004118600519480324a00020190441d095035031507401c05021a00a0310044492542c500c0c1e010f02c1d1824040181ca00312207808548078101070800e0026035454200192440e801070341d41280595582d150800c109403005400300004100e1902d50a00c002e403000e2055190082c11408140107000f60f10400120240c0b00928201500d900c8409040742480c1c1c440314050700300e41c202500071400e46288441001107034803948031818040141c80c2e0003e41051503000981e84114244020900a2000d0940003104811113400515160090b03880104a80007a000a03000980d10f030030108488904001015a8008402c0c030300c5064a0820851540c070303001400b1720882e038400403005c0351100740030b001511103482200c825101146000c0b0135501c0160021591085400e040c45142141c0020100d205490060b03000b4148440c030340d01da00103401410b00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 128033947 1250 128032697 128032739
    0x1f050f0906070606170c0402030105062d0c070f05041802090c0f0309062d150a03050609010c020d0c0201080109150e18060a0b0d1202120a0c1502040609 67
    0x8100400d0340040d002c0c0c415031000d00317401d949200700303941c40c00c031107a00d05050301c40720314003030352042005214503a1101e09072401c050328811599035041c804404828900855450b055840d280410f800e2500c2002140c0441550044943c1c807640340d94810400c421346840d815008201100041c2000c050f0030f00d960281d9200c10f510076003030f2400107000d068404550040f5488140380d0400814818400010204040030321180b0108065401c801001207584000141c01075440011540302c00388507031a400340684c020340d00002918154544100d032036000e0940040c00300d006001e9500181c02c00c50003001c51841441d01a522210030703a09007246100206011042204116018000014140b02a2807080d107d08101d500e02a5040c1d11240044d02c3c080d000382400d002c003801d0020b0b0201c1611840ca0030904941c100e481d60075403001556041c0c2c10700c070000e5184203a03e02c000030036009894219955809840c030503003000c0005c1c09201c01c900104c1c000e034006d490000702c143c01c081140c2002c1ca1140c4200000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 128035197 1250 128033947 128033959
    0x60e040515030a08040e06030a0312050406090803070513080f07090b0310020a0504180603080307030504060f0606020c030709020711060c10060f05040510030b0112050a02041a1f050f09 81
    0x615074001074648040b0840468070a000020f050011200c1401c0c260340080707040d8002d000307031440c540d00a803107901c000112900c0c640d65400002e080c00700581201c000185c111440303e69904280100401641c080b101050f24100e5840e0001100d9000045080d244011400a0801d075418203403200c016050340302040e58184500418860105031610003010040c5127900c9083ea581e01d0800c00c9000c00380d800301030f21183c40c61b21703d081000c1200c0c0011207601944070b1800050554940c58400020035820421400180c0303004408100d26170000f80b1009100400c400301c6152541c4d03079502d5010b0f4440c3d410010f0480b00e40b41110708550819801038410200c1c0b48003510308180c810343d0100e0850702594400407110b40c200200300502e080c90b00c00c035a013203142e107004c0560f403a00707540310a84c80c21010311840d039800c4030f21111013003400018011915460360062090101d000841414928841a040b9551040600600c110b441035401595007015030102e031202d0f81010b50314485000290040651160010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 128036447 1250 128035197 128035231
    0x20109020303042702090a090c030213030b0601020106050301020c07150203040b12160e03120f1608070218040b1306140916050415031401090f0303090303050709060e0405 75
    0x2a070140b01400151040d0070007041d081c10740c81d901504d52420102d1040e2960302c1085407103016120800040c0960b1118140400c03040741b2a03c08800030310982940002404103400080100005021003034040d010903130091000c0307911502094200c0c441c110f10484564800300e0304000e03005800c0b0300886991084e00580381403655554080811350303c001c072540745070540403081040c0384001203144a0900400e00d04592260b02182c042030f51780001210325000c40201098058450040c0303012161590207401141c0e6000d4040e241103000c0d07402c000e4003244a49410030b140030b4031f41c140502041c86950000d03161402c644503113800443c0c0c4030001600360743c0b6645480099100c0300180301d055018040d600010541c0c441c45000746004000c05411291240d410030b000500510148038240c01070782e404c1401144008041040107004007440e5000422803070711101c2450a054059100480c0d40d4081e86043c0420b5440320011146031500d40528808039035480b80d00011030400b40d00c420390080d00b10300c04c42110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 128037697 1250 128036447 128036449
    0xb16051c020a03020613030206150402040f0e01030204061d0a0c0c0807230d051b0a051c0909110f180415081204050d030c060212040c080c010804050c1002010902 71
    0x609008490340241e40140d8940003010341c10840c3c02c0e4072044a140d41c2c010312215a50080d11800c000d094140840d80c1c007032044001c0e51347d03541260000c04940306099600c56803150f01c5071290704240300030780c0304d207180c2400020300c000d62043c40800592007480a130000d580b4003141e0001484c407080c100007000240c286000c0082c00c200700030100180180c1e42e003441d0980000c15554079081000c1e507205071b60003070700c00914402c2c0c0140955010702a4200c042104100051246141412031403014085220782c0c40303a504031103003080b10042803402c190745400545441da11410b0607101100340508c105c4108008480750050071401030100110800c00b10410b020f06200041c0650b0b052040c003031160381a4080801040d0420005160006035442042d81002e2078040041c200500c0640c0280a00c00c030102840c00300a40f0f98107d40211a0b1001c2049180c2041e0400d50031464440c010401148104070001d00e203580a1000a07114540c810000d0079920004814003007a520110510000e42d074840c4282001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 128038947 1250 128037697 128037733
    0x302060a0e060d020403050f2803021c0519141606090f030503011401020a0b041707060c020601050a080f0a02060d0e03030f040618030503070c11090a0f150b1605 71
    0x1c040745980000d6141e07411407c00c40d04008050006281e158041001e00b15402410a0402004c10a201d007906107060a800d0690802e014000c40d900744074600451b071416160000c0290600020341c1d0000c03040c0b4a10b06600340c1c0c0646021500c1381c030052041c081440d4101c400728009904912542005c2400442a0b56a002202503181e00f02c0c04150040014442c40e8003240f111b014400c0c09100900480f0b10351b44818540d5040903102501400704428024402c035401001c40c2d10300ca40c0305001f0000e50204450003034403000207005084c40303141c0700400001d0700b0000003918082200554064117a8130301c035030b0803c40c0300c9d84415041403120b610703140c40c0b0182c02c00a001071071085c1c1c150114140030b45090300c4c3c12011100c40c0b00b003503251045000c3d482d202099014003a02c2d48205c4900b4510641850350420a034104a01c0920710740c40a81c800030010001d0003608080842e83d40c0000500965170f2100071000c85001d203004401c0002c4c01070219000040314807405805543c01002928060325032840700e802 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 128040197 1250 128038947 128038957
    0x61e0c0708120603060a02091302090103140a060e0604050c0d050603071206060906050d0807030e010c0210050c0601090606020c040b0f030610080d0801060c0b0402040e0609010c021504020a0302060a0e06 89
    0xc07100102008244d0400340300860780502039080461824400b800021110003001901d8824958003244004403079000b43d01c2904480048480c890413071502010800c05411f490042459401015010400d181000e010311802403a00c010312a090a410414890003060300030401039241c40b964200142c440c2c1c0a07080d00d943c1c0c034007508000c03580c02c0c01d151a00058035010b51055026210262501c8080f401d110103583c08503a061030580d56510390b49004a4102001c2e510180d480109407116001003500032004010203a00041a14982e0782c1e0f8a20100840d00079200b1440940c00500e011400362070b01c3c4d4494204076000802030b82c00940320303c0100e46011800c07030f04213044040556052045c04010880840d140c0a1450101c90640c145000104040c181e0300d001003192000e00045403c541e1103030800902e4019100031102c4030700e40031300c0c00c5018014901c04000980140e00174400d003000d01e808520320854000c1e244081e9103280d50b09001240d0b00441100c020010700c0c00c210f020350303990075000301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 128041447 1250 128040197 128040217
    0x509091b0c0c1c1e1b09050403030e0d08010b13150305061509060d1a030a0819020714091b030408090f01020c131e0f0606090503061e0c0708 62
    0x20015101d540140509040341c6410140c89100034544400022800708050001c00e28002c16141207034010710b400703100c80c070f00004102d017203190080000ca41c40c0d100c0c1d84041e104034003c2d5018000082050000b54503502d045845000142c0404010301030002d1240091800702d1803015100b4000741e4a6112030403c20811041e10b0000c2e40703980c20f00c5440c0c500a000652201003c050481c580780e441c1c80001ca9a2113440c04641e002511042c0b0000c0442e141181c03d04140400340aa45005249160080480c0e01407004040250020182c0c079050520008400b0151407000048500f243e2841c01000f0701c2500040219404820b105644840801c0e1140558020f5110700b15898849001b00304100d506105d01d000d2904640c858800a1240d0703070744440c82c489022035800001001220b01c0741c0345461b41e038141b0080c0c42d61b03030030142c0c0014449501d1348010b08603a0150baa0541c40380c0c4440030140ca0703c030166401d84950442c0f110381490940200394441d0000194002039181c00503079942e11460340c000c90158 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 128042697 1250 128041447 128041453
    0x601060e150304291603050421020a02090916030816120807140901021902040204120803040b060102010e120a0c0f1b05090603030d02070c0f080a0515070509091b0c 72
    0x248007074580b016104429030850200810365251885c42110503040f035900c01d01c10035444074086024055100c00c42040307046540c8002880c0c5083c500041e40d500402c5000301c0c010b214480025080642c042107940d2400305140031440e1080c51a15110042e03004103003140020b11840c0300080020b1020f102e81c2411a121761214043c0e0301d41a400030b40241d484607035a41a561301000b501e82c281e030340071802030280390383c05440081d11801400854002e015a8120507030804c1035402d1081800a488040c500c51441400480b12981c3c0d40c0c1c004a09032804407181e40c805500c101102c2b1700a444103406086140b0041c0b0f000b403c1000c42ea12a0690803603081c4040d85c4028139aa000d4882c05e100c685424041c1400343c0d0f10356044c0c144030021981c0c078421401d08051141d03001c0f5029040042c400604070090040d82c800b0032409448940031030b11a1365002045805204458502200705041726850b84215980d0b142d440c00d203820142400804180105550000300040781c0703004140f00d0920251640032002801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 128043947 1250 128042697 128042723
    0x19081c020301120308090d080609040303140c040f0f03120c0807061a04140105240c03040f0815040c0504020703030906110c07080c030a060c090807031b06110601060e150304 76
    0x130144c1003940186c11081d081d0402c2d140b800d9007503004a01c858010006846900643c1c1d52424101c0081442c04a00a8180100d10501c090104107030003800c1607810703410302c0c810007554400180780e010342c2e1840000c2914078000c0e81307610003600170409801850b009a0b02c151810303075290b6a0004485041a00720040342080325283c0e0a401c243c0302d802c481b980c50800000103541007800103071030101d50a81207201c071701781d1100e8408601820700542d683c0e201c8020440c0d03251500c5480f80f8240c0400343c0511007051180340d00303001c4002910064280295007000740000341c80d00b02010f01002c0d40c84003209400345602c0d040601c000481510a0782481030b0028800d5464944d03061145040610580c0681810340c4194001c500c030b41c1d8042641d071640303903200d8000600b43c03018240546580340d0f241d1000301c50b405004400024400c2c21080d0b28410f8810311448140c907034175030a05803140302c0601c04c9042617501080051080901900e1960000703400241078107190013490607000415403003194104c034088803903a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 128045197 1250 128043947 128043953
    0x705010e071a09010905040b060c0105090d030509030301060801030323071b0603020702012c03060103051c091d1b18090a020f070f170d0c09050319081c02030112 71
    0x207242c0c24080c2c29104103e140500c080b000800d81c1e4244c0c083c50b4411951410151042c0d0741300340481d900000301500901031440e20802d410b4846c80c215070198082414070002032241035010040b42d068652030f40302c00f2056400c58804942140c070001d0030380c1f00404440403a8be1405175031806481228440c0342403401541800401c1c14160800341e12001c2454014001100140e8110075403050301328040001c0204041400e84241d0400c4103450615003500910b07001106000740440d0b000d10754240f101d0b126182103000320044034001074606c00c00c014131040540b02650f502c1d8898480c1d4003c2e0b13103444440c4181d80243d940d04520b5004003500c018440c0c40c2035000710903050011015034000c502800031820690b411084010912a40300001c2101e101c0031f02900401c8144e4011499406030303880d0701901c2e061a003035504020240d010940c8003007074040e074000034103107800940d6101144010f40c0c40781c1c0054540c5da443c08582c03c821300400d1291902060940c1c1c01c102ca1000d140203000c0a03484003078001a0381 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 128046447 1250 128045197 128045219
    0x21e01180e04031409150913090b0906060f0108040f051c030606030506030d090b03101a09040e0f030d020c010605130204050a06050702030c010f050d0f1b03090b0f0603030705010e07 80
    0x200c081c04801c003041c042050310395a41860030240221001c060340c1d81f41000800100107004000b86901c0e018a0041c140c81030144519040d88144124011600c16440e010100091629112102d82c00140c0c0c000004000501220b0b44101c09403040c82191070f801b850801c00032140d80c0b098005000a55203050400c03080c1e03450702a86030010015000713841c0221401100401403540c50146030310350100040820764454440003140018410180c2d0040c515084621550090b40182e81291095040c03101018800401203600102d240003200110301c3c00300c1000707106002c0d4001d050600d10555030740301c0000307054071180c1819540500400340165a1401c140c100078002d101a00030104000d8284091030041e1000101c181c0100401d007400484620161030488880c41415140800c090a11081c8020b00850341c102c11222008105080c0c0c102c22401400c03012100121000f0f826151010007051501403207580064010030042c0940703160001d2901c42e1800d580003c94106100d0f4031070070003004000694 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 128047697 1250 128046447 128046467
    0xf07020102101b0f05120c0f040308030109060e060102010c0c14070305100608010e07031104020d02220906060e03060a0b0f090708090c0f0906100e0d03030b04110304021e01180e0403 80
    0x2030a0403030030003806c0c4411084084008182d2402410002000d6145111071820b0320700641d0702a8a403640c9603102c4c030400c6e020740006e04c5807141406403000403a01543c01800b540c2440e90007946c46001e00c0030652200300d902c02c3c2c1c144000329076010305503001c03001c500144a40000c69903400c101282c00e030307c4c00c401c950071160042511078003600f02c40c500340002017800342140c0030f0300f4045401580712116030b44400000d110b20801d4502003200d5807400d05038801c0b112113400803210446820030800d0344d0b0361015202c05c400c04010703039803640100b0006000c1c44002d90000510100282c2202010310f510300204654030000e42d0490040782005042200c00a01009003c070103120a0b101e001c044204800800c0d60303854043e103090312600135008048489403080c10b204070a194010064800700c201410083c00421201d40c2850140f401d00c0448003800480c041100e006680c0645031903d03204416030f0004007135110345034480c1002007808000c2c5101101036002006400580310118140c2820b18000e0085142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 128048947 1250 128047697 128047727
    0xc0f040b0105040b0d02040f030515010b1c02030c09030a03020304081b09010e070309120c0c0f050d0b070e0d060b011206150c1401050f18070b0f07020102101b 70
    0x10180c0003111640c0c4a0182c404551649188580f40c0103840e80c604040d02894018401603920090000b040c1b20000500f901450340e1420314400698999805001c0380c49510300380002010407050b004560aa964011a44049040115400c0c03558200004c2c0c10041200350550069101050030300c6806818820100c140703e440c5894410f400c10340001c40c000d84014403c1c64034018140c0c0004282034029084000e5440c1d020071100d0441c001d84001410300043c500c41624030001c58840030801d050340c40c1038003050710001048883d4444281d61500040da0004060104200030355183c54583c2c0c50300e402400c1c41034460744000c500003c10134001003c44511a401926807814104100b1020080c0301c1005109180c40c94000040c5030b6904121500d405107040c090107641c13070042008000310991f05890b0055804000c0c141045880b036803041e43d200d0311802a48004901001a0011412450020301d07078184180142c0f515292041e000404481200c100d1000c1c4080b400e500d150015803240b690030f01e100c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 128050197 1250 128048947 128048951
    0x160807020414190b1302030a1e0606020c0a050d080a1206030b041e030e0103110418060602010b150307030504110d14060c0a080f06060708030c040f090204030506070315090603050c0f04 81
    0x1800c40004a171132031203590018041c1c0d80040840d0050170700740c01c1612418647d20720524a00e00d40d4181c04010000340c07044600500845001a0161422803445001c54400902c0841407040f5500c0f82c0100c2d41c0000c42c2031050010007100300d542028940030348802036001e044480600d1407d81070003c580c0030001c1c42d0111014681c1752003030000b60420051601d01c1828078000909c000710281c00b090520440c1c100010306496515807100f0a0310540004003600c6095009002040b0308030184050510003401c240011801800000d941500c25401a944180140e1042501160345004181507418111099035202e0022034034007600c071000c02106401c4000c03400068076000c1c098000a050402c05029038143c4040c19000c5002c40d543c14080e0380c0000e030018465a600e0600b41107071003040c5e02500c261840040259400110034086109440c05c894004000c1e281c1a0b4a204085005040c0c0006101d4515004803002c20300c0c01176446040055446103009180c0e2881203806c20403070300c01940040344918 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 128051447 1250 128050197 128050211
    0x10503010518060a082b080403080403031e140702010c080114010c05032107020d03150603020d110d0f1a0a1a070b040b0105101416080702041419 64
    0xd1200d0420030110341d001141d070b240c0e940740d4500084002440c0d50106689200d03034401078511450080414043c1090750442c140b041640340e9040d6102d180403103001d00496201c10005010a0180c0c11040405004903907010a0070790007080f4400303d840c09848007000004078020000d8642d024812034400058030709241da00c0b50f140000880c03d19104809480c100302d104250340c000c00108005441c10a5400544105240e2048492040844007103c0010040c0325056000c0d00389802407080800c0400390328a5468101c0c1401425070195010280c010640d40d60b801c841d0038900390340c10241070020413800703000c928045240a204140c90700020004141d240035031303640825548520b10b01e01101e498402d1f0110f4a000075111b9402070080c01e1014004410520400c402c00c440050964140c44086404004008200c0c03011540002d6035a419480d050017005411240d01c00d0403e419410b510030110149000f0043c0c0c040303403e454a80a051882c1d210380014030602a03840445d41101c1184080200a51 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 128052697 1250 128051447 128051449
    0x501060206090a1112011107210c051518010c050d1d06010608041406010f090f051b0c01060b0d020703030b09040b060d0804050d030c0212010911100504260601050105030105 76
    0x40852a220f442c0308117440c0044c3c142c909402c1d00110184e01d000341c0c249843e07484a007400c5011481007445082010f002c200c1e112803103400f844c3c0603130034150001c000304140c003000c03442d08041140140151152165444205020b03020034000c201082405d5920583ca0ba032802400740d050320102d8000903200370041c10440150b043c00600346045076660f14001c0d0745a2502d042008502c1098514150310b40200c900101d20a101082070354229080a0410494252958210001c4400c181c600c00840c048030001030825154072000b80003d01c0070040005000355071444403520300d90200300e0459000b43c0100fa0360080c941c051069141c0300100340c9a80e02c442c80c140e6207180c0b1040c40200103502c00e5140182000a0201034000c0d2005082d01400b4107440003800d003006490154010401c9124481894100301c601c40c041c000c2002d4143c0c000c03903d284046044081004014403c407941c0200101408002040310084207000190030346010f40402003c0540394284c200b0344140c10907414010108010040d03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 128053947 1250 128052697 128052713
    0x50114130b1c0303020405030601050a150f1803030e120303041208040303020d02160b01090b0a06030207060b03070308030f2a070c0f060302120609160809010b0604090501060206090a 80
    0x403101622a000801001c600009400c40e03003031803500c03559100d03040100010150564001d0040c1c1c0e03412801c070b91680c0c1c0c7c0ca104001d0001118090f081d804030300c1a0220200c3d6002e00043c1070914020300b070071910b0b1050318031100c505411982c41500003075410f500700c0c02c1d5400e146200c0700d510061070001d1840c6113099102c00c00701c88070400085040019020001e410b0510990580b00104000720081d507485122502c2900c0c0854108400d07a0324036215000050f010441e84130b01581c1d138602511074074526243c65415402900808015101141c486c91442c40503a000e2140601035485040a2030710f9080c036902c40140300c0c800900040c225000d00050b00c00e00042c4040d12210f40381303500076a40d1b54550a1903d09204440359108a83c001488003011440e5038046e0081c0001107844900e0500607aa036504010344200281d0300d1071032485440460009052040c51711603889050f000010810030b50160100e0b0140c0c1c816808010469681c800501450307034180104d540198a510047c940c1c0034243d155460 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 128055197 1250 128053947 128053969
    0x40e0a0b010e07020a1a0a05070e15090d08030f0106110c030a020d24050915010f0e0402030a051b0a050f031c02010e0106090b090601170a090309050306040312050114 73
    0x26003480780700091510361003005258012540110700e50380a0034160720000c1c4852098603c8100c7d41d0810000880380c174803a0041c1a03500f20010086021403005c502c940c0650380c40f0350302d9290480104070b001c0000c600001c0045014501d0304201c08a80d40c5002001408280c0c0c0e100c40340615000f428a08a460340c000507040080e0390111060803428801e0300d444d40b541585140070210121481a50a0031007500e40e101c107105503039001c1a50329070f44d100800c5d04c080d80400d0058518020500320244014640b600e200350307002e48054121000c15407283c4500d0b280074250342e650b60111424075030902003802e0081003100140300030f42d081e004000400001a8440d568240c02c840030340350705071581e00010303c00d40004460100d05802006415201c04c251409450700b412402d000309100e00c0880e8995206a104120051071011304540c01c0c0c980e44c1c2480d016001a20040d010001d0310800407849507818408035002c0e034440d0300c0d80344589101042e610180c2c0c80590001c6000589034400c03443c661218102e042d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 128056447 1250 128055197 128055209
    0x71701030b06060702180103030e0114030a0e01020f03101d1306092603010801060f050105030a0209060f0a0509090906090a080304050715021005010801020405010c0803150603090a02040e0a0b01 85
    0x11a140c0e69002c0440c0035401031001c080d610101348054a540140440c82c07450580b40295280d8117141ca0328030041d1b800f100033081061034400204002030940030241d0040c04c52080c0715001601c1c0c8000081c0c0d80080c0e80059912140403407030b9400030030505d140c182050610310080340c43c01405280c85a8614011340a03640080c04198958100004005c01c00c0700e282c81030366140d000d4080c41c034494041940c0c1c3d83c01c00d004000c042d620300500801c10711a6109600304540c0142d55030f80c40c65484501c4000650450348909400160234040d01540c0d8542130080e02940c03c00b55902e40d140c09224040009e0404098011000c6420940a20060b40d8011401048058010090a50703c3d203891525600d800c0041e4001800d11611280c800081a4040307690403141903180d03400c2c0b001d41d0b02d5410b092300700d00c035034403038103000c40d13007e1a810000440d500040c651040c0d00a14207079013860100c010807071661045550340e10317541001a900702103103000d104e07c81001810344010085154641da69681c841d034107014003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 128057553 1106 128056447 128056463
    0xc02011103210f0412180806010905190c120b03101b020706090806010608180d051b010203010b0306043215122107050f07030b07170103 60
    0x65000b50f0301710508050381c841204007070b502080b0090443c075480301803400000d0303150070500105009000a0102140a1510710490900314952041d0392071904e00e40740800b21855804a46030081d00b100104c002405c40004000078600072000c54240b82e0141009a04030342c196603003107030403520f0304540c00312498541c07982d505486401c00d6000b01d039041d900c042d004000803440740030526008000303100120444100c2104403810240c070b088003540490300c005001c002c00a00450a1250304c0403c0b0000c501b55414010006090301c00580160301c00c1e0380740e40050000f010012a1988400080024002d148503000946a420b040840d400c81900060700d641c840b29050400d11008142c508001071b00c580f60040d500c0174449441e49401000d5014140010700c0091001c10061400d100403200a010080c40d524084031032890061a4204100e180b0b00c00b49105a000c0003480d06582c0d2041c0c00c = true := by decide +kernel

theorem cover : BRFrame.Cov 127877697 128057553 := by
  have h0 := BRFrame.cov_init 127877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 127877697 ≤ n) (h2 : n < 128057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
