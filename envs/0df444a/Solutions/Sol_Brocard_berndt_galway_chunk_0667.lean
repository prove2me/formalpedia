-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0667
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:01:47.75248+00:00
-- url     : https://prove2.me/submissions/8c329a56-9b20-4926-a88a-7518d491af78

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 119784172 ≤ n < 119964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 119785422 1250 119784172 119784179
    0x70302060f090109020402030109022d041710020f07021c0323090306072a0b18070f09060303030501060c050c01030e120309151003030509010c081204061e06 69
    0x80d1152402808400d0000920340064038800094005100c02034000d4411590782d44c651041c0c40103984461062060007515554034100030800c0c10800e002a5102c941e090705103820403100640491303501326894914801c644401c00e800c1a1480240005207840740410395800b010300c14000f0085c050f050518034500d4500c401800300f41c22288031031000000f13001f400742040c4000000e41e010300070b01d00d00541510030b0004000480e9086042c44030705042040b061110341d00445000c8030364a0034228020b10000c980070102e198a0302c041c810700320301a440010307118042e46507000c24140007201d605c03c00255850700ca0400515400d031080038003400c007070f292024290300380e03403102c41e618161401d650741050355031100f43c440c0c1030342849000242c820f111041030b584d00b02621207d81c0c1d0390709092031425210691001c10610581052104110784e81502c400f4280f80005005440880ea072500c01c3d43c4100d020026120a101d240c0b407454070903403003000300003100c01403000c4d4400144444d0035009006854a06d060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 119786672 1250 119785422 119785427
    0x1a0a090f0f03120909020a08150d08270315040c05061810120e03040906170d030e120403120e030d02030d0f1506080a0b0901060f05090103150803040302150703 70
    0x30082d03c0e000001415030030003080080300c400341c056200700740f0a880480d041040c079a12840701e50041d09034902c0b41a2003444042003100c01080058020300c000c40c03c2101005101101800301d140404802c00f040e10540840b011034204001d04900440c01c0340d841c000c2208010025084030043c020944609080c660b0b65854001c2000c1c0c0319404501c21a80c5a4032a002c003441850503d800307a401344070a014604e4002202907590300540a005001400e1010129980d202903131000032448120f4001c200314880390105500800107a1400c0c119409100b030304000c1c3c1c2c0c900c280207000651140d01182079a00401a000380200545880a44603030003202c0340d8000c0c540e001007a01d5440c00c1e0540c000070031605080d00b60004001101c10301c9044440306400044043e00285280c2c418021101c1c1849a00400010051000c0c000d0286102140030b050104845610800c00341c408200e041c100040c5464040f92020011a0b95a0124165500010b014421401c2401015000b40e001010481c1010903070740c2d01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 119787922 1250 119786672 119786699
    0x50616020a020109090e010e0d0c050606060a050f0f040312050301051806220b03010906090c0905040209010b0904020d050f090d050f030a090318031506140d030305060a1a0a090f 78
    0xd17140004e84801d103600d2030300020740c4580c8601010000711501100c1d6850044c2c41480f40d0502520f41e4000c450001d00c1c00d04000048410b002043c0d034801e8034121012402010a40040710407070030003881070201200050a042d2501c060069544600b5248c0d031400081018044542256880f6029080e080c0841d544680e400d01c3c51140e01044101d2150b40303440c134100020050045070b01c1d07242d82442004000e20030b450303014108460082410307a000a80f110156003e8800a0350001d40044801004000d0700d581400645508400240f015240009080c3e0102c1a22000d441c110100701c07100e000c2c4001c035542044840c0034080c0d00d00b40030703091009205840c0100d0000400c0e4281c400e0b00e54142c20109440b448011900046909440400d69160300705540200c06a50f1645042481c1180114800314000c00c0041c08440c01012203007049141d030f4085010f000081c00081e008150004003044c000740d0740b07030034010b00e80400c0b0a0340c1d240e04040e100102520031030352080344035900c0d030307441805040b240154 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 119789172 1250 119787922 119787929
    0x21042f010c0b060319060203010906050102061005011d1801050109050d08031305031306030204090506041a041e0e030c0c060301060c030c0f080c0a020307050105090a0e0604020c0703050616020a020109 88
    0x444510550390203004c2420300b15000c0320714142846119040040120550155043e0752811030b0401540746c82c0c000581c0c0d0780d0025106400306d5851541c0800c00e07036108844801c0319140c08804105aa4500004a2032102c1c0c804031445c1e031050703c04018012540e0000300e280081400b111207520100c06504c54540a10020340540b96811801202d40b080c0a0104121000d1740110754550301956614a070090094109001d643c40c0e89062101046c600d02d03040c044d080c1002c500500030b55120300c412041100401804050407455000121448030742c641e544100800c0c221f14070080c540e18500140ba040c2480b200d0a003580c8031740780520041c000143c1c403c0521081c2681400c01050103803150400341c0003401d080c4001400c1c43c40006105510b4000450307001142c5200350125000d00791200300555039801110005904505041c404110325580c81c40c4403030700a080680018504902e019040b401d110664009640c0741e07200030140300000c80c46021404c100c040e14809052103270301560000f48a00c03d80e12 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 119790422 1250 119789172 119789183
    0x70809030c0904151a10120f020a11010f060f03170f03240a0e06100504030506040807020a08060712050a02091e01020d0806060f21042f010c 62
    0x62001464030100241d00518a000b4000b049924044c07500c1c1c40000c40051001c9403131401d0410f01d189500b80c2c6800203000000c001d0051403140e24041c0d0488500c54081c41a81c0265107039a040001c144081c8001c100d8450a0383c0c0d10a0107812a40d0a2400c2d228140300003040a46492020407a42008922000c1982e40c441c0d1403c09240504101810a00070401a640046000010301c281520380c600d50404003d144404c0c040070340042800c00c01d620344e980c883d84041101003c0061a603141140140c1840d0b0350504040d410640c0300d44480c0c1c507010085400720350003600022580150324000c644003004180500c010300203403601c0304000300014210006450b44c582c8550118200400c2134068440110003d41841010450001070a120844000072036015018030345030403088038803070248a0b12812000e4405031600307104485040c1e840c0e000d0b900c0040d80c0301850301350040d00c07501c803103006029900072000c44900455414402004150512440008004070003403131000ba40c000e00c1c0c5d8501e0a8014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 119791672 1250 119790422 119790427
    0x30c030702040b0a030b010f0f05040506030d030c091e090b0a030f0206070c0902070b06120102070b01030b09120c160902042106020d062d030206120c0f0a020f0606090c0708 76
    0x4400301c3c501c10102e800050006e800080040b52400b01505280229000b0881061902c0c0e954014801181c1084d140590150006034464002e42c1c02500501031081581c03404c3c4011a90f51450504800c6074407024809121440008000102286c0944148108111008031031305245582e1801c0c0c400000100901034035001c1200c0d4180301c1c030b90348000010800103a003955100b02c070703160060343c0ca0300490701148110404d620241c0007070300510a6415656000030900070603421911450904080102661164810034001e005642c108401520001018200402c03a6694001c1d410b401000c0c16017200038518418041007082c000010000c001d80701d1518010001c01e900c0d420100080d200341d005004046040c598005502c907550050796042041451005400d19644640046120040d01c07000c0e40c44034003440384a609400c2c10401a4124201c0c46c207003454424251100751450b0025540d00d4056000140c1031070310864203100c0c00c0d41c01901103850344843e01c0d1150000b10319005101000e032103003001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 119792922 1250 119791672 119791691
    0x190801050a24110a0f061b0e0a09021803010c0c0c0e1e06040908030c0403060e06070804020118081b310b01170a1d07030809010503220302061008030c03070204 70
    0x520583d041070760062903852811600c3e08291024200047c040010303c03024844000d03081d0700c80c042006c81c54100411041081d0700d020038110103034004071000b0b109010084c2c0c5600c2c2c50303a0240724401044070551900385030455281880001d4800e1a40000b01c1180c0c1c0504000f48146000b21000d024400607000c0320f007545820000c10300508209000800001c00041485901270010f40a041268030520060010300a03111038540c540c1c81c26113110010801e0f03040420019070098022403c2c00940c00b0b428401d081e59445120720741025450310911204281d9107a00103030070325954030001800c010420742c0d6901910605801c0010030562100d80160b0b85402290490f0311400e0303465001c05400c0e80d450380e05d04002005600512070b40b0506400080e03284089000c5610106468086075040091035003845110801543c40345d00003008064915400d000807001c03503e11041c0207088900990080c001441c040065502080942e08151000c2d8801c2c0500b200c2102d000044a1a2550603240465503404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 119794172 1250 119792922 119792957
    0x60804030e03162c06060f120c1209010e120f1309020d0e1f150512010902100c0c090207060213030f030930030203190801050a24 57
    0xea41e00840e6143c01083da0310950031502074110800e40e800c0003401980c0b800401e034001c0515860310140348050503003a0004100b454040040c1c120025281d0340300b440c08203a1180e0500ca04801c846401c3c82400106500c4001140200d106074003180b200c008100142e1150310700b07940d0702980f240000e60700c080001e9081d802401d1500b0303100f00c11014000c05200f652503003100302c0a0741080071755417803443c504002d100c209000041d1655561142c05100d03011107801d200480e01414510380341301c4026841103070004e440d446002c2c000220070340711030000448201500c1048450981440400200480b602580010507003e44050040340c00f010303001655080c083c41d194010f8014050414003811100c0e8001052040c44088040000e21942e81c000d10301c0d8603981c20f60700d50b058442d030042c46c0c0014480c0a01c01c800c00280c0040b2403500a0044030704250180d0358042d2050401c0c8074400018030301c40010441b80c100f0700c6200340902a00310b8500d641c4003045e40101c200c10303071044d122802c00010510040600c1d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 119795422 1250 119794172 119794187
    0x9050c041505090601030603080a0f090b0c060613060501020c04051306090c0806010902130603090311060114030609010e0303070c030c0b010905041110021207031812050715050406080403 82
    0x44060024040041001d06900c0701078003901c42c0034007502c100030000388658443d02c02c205c00d0303950102005080c90300313002007140d0000e1240200028003e04941c0400c101030807101409440740341400030f1810b4034000050102080703107615200a002e04005e002d201680e0040703107151024109880020b801d030ba0348030540c505a07420388400f601f40d602d000d00000a000c0e400784a24280c410003800c46400e070744c0e902124022403090b20742d042250032083d8000c0c0150b522907005441c0850080c900800d10342d075a001407038140002039010301a556070102c0c0d03903521800c083c04010f038442a402c0081241080d03101074a138480c840246410b00b00800c40c2110000c040c001d00f0314070300040d04110003890310740e1101302c0300c1700070a000e54081c5c03040202c645482d80c0c20300d0308503454840744e2690360182c1300c3e00e80d44d900780d0085030300080021420f00c5000f8001c1040584103000c03a200901400810594903080c90610904100050f013180e60b5844401102c100c407242c002e0102c50032209030780b4281c0001d40c0c5905044a040e07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 119796672 1250 119795422 119795443
    0xd0c090e0a05040b0f090a0b371514010c0203030f0408010203062b0204020a020f0105160e0a27020d0f050106090609080a1101050910030203010303030b0f0607060905 73
    0x124108080c0054110942c1c02a8460780c416080300d50907858100c000205454100e507a500d0a51101084030001540b60181580050800c03100400354503280500c03e0392120002d0b00c056208120040f140710300c24487c09103e02d600c0a071a6031420080c02c00d07003100e80b05520007440f2418070a41d6800740f0115281042282d171005461501c1940303860f1113740c2c00d4040e500588200c4d20442d0924240304c2444600c801048503c00407250800716400c2681c02d00c4003035002070182c0815800344800c0c41c61440c00a00071a4810008905205850481d5100182c80b03811080b90a42c045d0710307620828007002684c1d851118510203a03551400302e81c418011444042d2090741014031015050080e0080b840620b03030016416610251201e0301802c0c4c4450040b40c50003042c1c0300d140181c3e444650054041a40c82d10780344a4980180340503441e2040e20170115986a00f02805000040c4d4004010018141c0c144200094901e0450311281001c4404000441600076031030040c040a54072100001040010440b2540e00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 119797922 1250 119796672 119796689
    0x21c09230f0d05011a0f061905090a060203030405060a110307141e13050f0105070219152a02010c021c0228090209060403030c030903080f0c010b01090b0d0c09 70
    0x50030354a0040d000c5c215805111081e696000350000f070781e250142c00b134504818050149800c001a00601ca000b5050a9466030203105007013045507441e40314070201d4000340031107070000c5030750f030a062410074a414401003408081c289000640c00d1180300840c21650404290f01c4c01c0d420310030f01d00b91149564420403203030100c0070f00c012010882d00b1000328050001054040c00952441d5a10402c0c0f140922184c00110b0024008010402c01817500d00540e40c8507000010031140201d48038201c0c807004071458208480030a06280030300100c5000038082030307550180140113404110903036001038a1101c0764030000303101c0c050a03d0071840f0528103541c150074080d0000c00001c2080351880b0109019107a40d201f0051400c0300178404070315046540211004604080c220a207418070b55101129240308903103040f020028140000404180500058140d0f26940c520487d40d0361311700303010350f0300f1201000c0085040c4200c00004100048507030040d90344680d0034940c08141501070080881d00c800494100c81e04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 119799172 1250 119797922 119797939
    0xb010303141315030b030109021318061406030706030603021807030e070306020c070815010e090a06020a050904230c090f0a0e010608010b0304080702060a0e040507021c09230f 77
    0x408005040380c0740062046031301e0801919242100745800e82e480c01030080d4010354031610f1440c3c40301595001360342e0700c00415001c1a4a889070754031a02528141c428a11000740100b0034081c2c00c0c41d0a00c50302c001130102c1c0c01c08000152030f50b0301040c40020304041c102a0501c0e56400101141e0284d004541d01c00007480c20b27070308959103910b0401b00941022160300c040d480f032903401103804600000c00100a6151483c80940790b840e281c07110450001c000c0c40c3d524280035488003480080e502e4000b6204d02c46603511110f840d4822941480111040c2c0a00080d2080095000640228020032015041400040003943d500e2501d40415100140110100e4101c540c0400021300180300820160607a0b80f903542c0e041269903a941c0380000c0c0e00041d074015040340c008200d103e00502e40480285800e02d100d00708690013240e1003001074100d41046601c003000d0b1300000c004400300d02c1c201d8040c0c07030107542a04000080a0820310134004007040c5095030027449985d03600c101e00c2c0d5070700d502021607040c600500910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 119800422 1250 119799172 119799179
    0x501050d1707060204150c03030c03110f0a0918050f160f03150f1d09030712050304020307120f06050108030a0c0204111207050c0c030118080d110c01060503060a0203040b0103031413 80
    0xc0000d240d1a1040d0002407a00c014000c0c01cad486405103000d01c40940c000389042c4900d24803819515070004500c20700384400c101e000a1210104221854008007194001801c0d1420034801034a00c03000400c6a040c0d4103c0c11554100290050150001c444444c80c0004045101c0380d10f00d101290150010005811000000524511078000ca18800c0c8a10b410a800d03985a808040d5940c0c0900e08004055010103c40a4010384c07144029640c040d0000f0b046a400c55900c01c0701002e031808682060301d0b40c6440c0140303c01403054602500e401049400f000b1442c1c00e41d540d00c000d0031218000002841641c8a4040782c030858090420303200d810005200c04d50550a0251003d0315561000901c1c2c4010302400e080040f86282c10710030000000080b00c00180800e0149e0f403403140a5104045000500b59121403101c050b0b80414060101c080300c6e0000001c1d01d508103402c261405800401d400d101c00e0040041200080c4106031050441c0d605082150700c1004440c0303d25904e000320340a0001c0402c00c0c04000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 119801672 1250 119800422 119800427
    0xc020f040609090203010b0906180c0904050106110c0f091803040e090c010906050c061503031e0a030f050402030d0f050f0309010c080109140712090204020309010903030501050d170706020415 84
    0x660145200320020040440b01c0e0051020207003040358a56031101d604200700d0104100ad80d502d42d40013404201302c070b103481c80610004045580070380083c400100114004540d0080402c0703200d20390141181c0b25220031440303070001000c11000910081905520015500d424002042540e0140c44000351004441c40e080681d00d5950a01110003800070300d051000040f0240944101e442e0702681c5000343c14140c0d41c0d100e44480a521400c4540e0701480708006d40a4400380e80045400c0319600a00700726030742ca0700341702d00400b40c0c1c004080c1800300500c0e2501340700042c0c3d000034214100200c507041c003102100d0180016120b03400340010812070001c000042207008207042d40100820b03401500c2d800d84c2c81c0d0702c0310507030001c031082c1c07183c550012542c0d01c001c030b02c1d00d60094401001c05580340303402041d0765030560301040030ba8100b59080c181c0d0743c0d180c0c807150041681600403907025020944140c0240c0c01e050f01c8261f10100414426510364200203503039000d100154040710050111102611610840503400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 119802922 1250 119801672 119801681
    0x13110306031e0a020d030e181501091206200301090903030501170303040204110d0603030525080403080306010c060216021008010515030907080616020106061e0c020f040609 76
    0xa40e1090050b403203880350701c4680c140849500d81901d00103000002c110760078005403900481055052117111280060203035a56204650503078480034510785141803c2c2309910b00d140c948060755046c0003211a050002801010100d02c60f2500f2500100d180c2c00c10b0340032080c4000b1341c20402c9040f044004008a0500d009070001405140b2968007008aa0303660514947c1403109809043c0080c1c00402c085409882c1c203030072408079a142e10648500d00356039004850100c6a4662048022400c040350090a00160148164420000101c400d8101000b55202020b51086000007082031301d000c40481d6140e403003005c43c000010384c0309000319038945c1a0480501101030141049100c0c4028005c040c548610610b0094103c54010349528071073320313040c03500c0034594000900320314040c41101c0b00010121020002107014001002c0201d00810001b44001d0960708260420000e203c4011206c0004003e50038009440302070901d8070f450340112510014010300c0d1500010395025080c1000410002e11a500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 119804172 1250 119802922 119802931
    0xd080d020a18060206040f0809180702010c180f180605032413050d050901030207020307030c08070905070519170a0510120b0103080c0f0105070207171b0f131103 71
    0x2c850200301e54078081244c0d60070080300c009200e048940e81d150000b41a05000d004800c1000f407150300b5840f001030340c0441c0b04000715401030050b9140c0607600d5013030390413488841d554440c045030b9000460500340c6030b00040c0401e02c6007030010403141e041e80302200074990200c40984401001c0d034140a04c403240f62031040b284407144c1d508080740c0700007264010396080c4069030b8640c1e000d400f07880c44c10070308403054030b190300b0030b400725810700d5002c02c240070060394140001c40195200d5402d03903075040e00b48000140b601d03d05800003406580f6120520200035040016940000b034540949904600c5541046420780500713000b40d480c2c40e41080502c4814052500840e00c030303220801811200b60f0b0364020720090096030350b001501000344100184040348400340108030344c0c64028110351003494070300d111074216036080300c007070f03005800c441c500344a03019420341c2401c00504100d000b0000d0611a41003000b01d42040070b03150307114084d80c8407a507400d0784071401c0d40700d440e46034080d04001e88104c0e4a901e00c0d003640100c0d07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 119805422 1250 119804172 119804207
    0x3040f0909050c0108061507050d03051e06100c020d030306050111010204060e060a03140c030601023c1f020315030d020d18031e11040513020d080d020a 67
    0x800880d401819210300503200303030000e0003050400080001500d9034217000d00600d8015440b0b1004800e494078a1300100702d11707071141c1c0040c1080a084000101110340241c400c1e58030421840c0c1c16014000221421500000d00f22541c0c0c602c00b00c0583c0507501d078600c68030001c0d041200c807084d00c1c090507090707030024040350000e80351001c0003082e040030310b400c0b88901d016480104901c856082c0b498140080500b491703003100e040000340c222140c0c03980701c0307120b0b81103030702070340c03104001041010550741802110800014860070a2080c5d50100d0040810000101d490038030303884011010310440d4003001203d4000e1a40e159014840340c0c0d903940d841c040d51044440c50503e10005088945604000642c0401d0182c20b502901280c9080703402190840340d804030a24041484d01404408a100000ca048501c3c0105819182c3c0e40300c4c0c1d00e8030341004d01c40c040100e07121314034000030003061400c2007400c0b12009604035000c25101099142c5150b8500030f44100120041c40030504e0142141c02c280c0000c105c14981d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 119806672 1250 119805422 119805449
    0x4090803060301112109100603080705101a010309031205011205120f040605030c040f06091707050105030a1107050601080a1407051e060903060403031b1d010c03090b04080304 77
    0x640c1d070580d052040a0120326503800d1750b5000c03185004090095070b0400440d07015607010017007204070b04040c0e424580044d00c441000144000070000204100c40340604e1103030007400303c0f44204008080f460107205020b414981c4138140c4004061240c0d0401c089203c0e00c1e4003c001039616003000f0807a4a01040c0111741c507121710415804010140e209540400c5c1000300080c1c40e140c01d01e1021143d5030400b50121404007070038080458400808585000503004581d02c0d984024a02251a4481140701111480700e8004003001e200b640d034000212544000c000e0790216a11564079070040092040090103800c0740a180004242d444011510031099409100c140311207036401585140c0b180c80d0341c881c0c3d0b80c0c0b00c24a018400381c00c200c04121403601d03200060206003071003a0007001c0703810054110750440c002980e070305060350109518045042c0c412213074030389103101038680007010031048280560740b414001015078201c1010f00c01c21b020070240c40145a07079070f200c60361800070302c0d66a041402150941e5600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 119807922 1250 119806672 119806691
    0x9060e0708010f0b0a03030f1101020c10051305070303050307140d060501032313060905030d0902040f140402150f07080304050706080405030d05041b0b0c070e040c090b0d0204090803060301 83
    0x984c0685600c4c01d0004040540b414690780d800d881c503604a801c01406c2c01240003407a21111801c0c405099a48504400b030414400450790b50000c0b6131004190313120340d030205031503d00804c500003550410b80b0b605060441e030329100d40d00c09454004407603a070000ca14500280d90b00a030012900150221a0280c03020f0040a84e0044458110b05e07580707806440d4075201500181c2e50a007650380c0c443e0442c0c054003000a5626054592710300350380c0300003440c2d2039007629040c1001c2142064840c1804102c204442000300007000f10f40f4078031a41024102a1140d08100040e10401d03106034112807010440340c003103e40d14022032814500f01c2e0021507082c0ca007406140c0002034124041c2c1825440b0b81e40c80350207185026104151040201809401034134500b480340603d06501c041c80c0980c1e400b030844100700c0ca403548028903030b461905266801200124405200b4400040d041340c03102c07030603580c04840104039419071001054441c0220700c03010f0b604c42d04090702c42040c00380754001580980c5040c0c0003840f05a04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 119809172 1250 119807922 119807951
    0xd0f2003010503031e0f04140a0b0c03091207050a0602060a14040b040209100305010509100609140c18040903080114010c081605070503120301240c11010309060e070801 74
    0x240702e001e405030010440101501480120700b0702c01a95010541c0c10407070b140c078541c00c0c0c0703821a0700041c4c8040707004001d400040c5007007407c8100a0032140310741d42ca0400428841c030340303034020503001c0d6014104041074801682c1050100001500000c0c050045480c0d650800950341c141c2510b201807018136024040c101c01d040004401d10443c2c00030703080030054445500740007805400070120100300721451030103c0015000c0c02441d01401045006000c030f8291080c011084542c0e44d4094291540b5204050110340d40f00c203a0305501450b110170058442c03000d56101044210301c60300086d405494a03007942c04060300005814140d0300441c8410ba940c0f0001001500d00d41d40c130100281c0700d48000d2128a084083d60105810700740c3c829420b5400f441c0ea564040b034138041455084852102002c8014001610402c01d40307583d0b0f50304521b815440c2c8820102c00391501018070303030242001200e81c200c14100d90094028441c0258482000c00c1103041d038000b156166505030241c540300e5401e06501c00700f4034a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 119810422 1250 119809172 119809177
    0xa0b0405030d05070201210b041404020a0b1605070f0312020f060402150d090b0403020c1008011e18140105180609100803070f05070e041212020d0f20 66
    0x100040c004022030403100b4815600d070740116004a04211030f40000b052080300381d10a003c00b40b610001c01248442400040009035080038503142104404002044056035030040138800b150445980700d070b43e9018184040c5c0d5502c2228130064030503ca8040d00081240038000e280080301c1c007490b40c4414800812404a8644020000d0040d19901000c0480d0240c40c03c0d012a40030b02d010b4060740c6203405a840c941500703460b80c11209641d94032802c4108024142c05000c0900c0c071072011907510707081c8202c041024141480c107000c1e10300070f003c0d0740f0442d1841200d0740c0981005018072030010310400b84c010758400c014100032911800c404a4001c00003a190500e140c00741003051880d4040103485d5030310400e10a08420042c08405402d81ca004001401c00b020b000410016015189034000384c446800d00701c0c60704c0110350042540c1e600303600802002c0345582810054052031440c00342c01c00c0c5080010403000e8061600700710345c0d00e483c00448169140721a40401c40d00d0300320f84501c1d01901c84d052076994150 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 119811672 1250 119810422 119810429
    0x8060108071e020c040f02030a0e1203010303120f0504080309070e2806030816050609030412140f2409060402011403040c26010b0907121119030501050a0b04 69
    0x5811840c0980e000114140400c0b1841d1440c41180e004002c01030000d400d45030500c2c440c880302c9500200703220301d01c6020b00035199070401c400003c0015055420302c01020b44814400501048015610121100115041040034020009081c0003d0410b4140401c01e42c0c8156881c1075984104c3c200000d085150b135981522561740d480e01600701041040071160b00c0c1c0c00121061842d140d1381c0c1404030015101c100034108801d40768007503010b264030a180440c82c03c10f001c0c11a00c1c2c0b543c400d000c2003003000c4800000c85901540140f1135400840c2d006a0b16141c9401d1100d0340d10940075554800c01d50340780485019051325410301480da80350712070508a03500d0714002e40e8003074005400a02c00d103040110000003103402903c01c0114464490317a40002c4050b004902080081882d458055089003507400d024a4840103022035030350a45082904010f46414121841d42303280d9901c4460400800382114203682c10000307115141d1051600815000300205400d025461096a0340c47c5d0100b107c03c0c1d80e1081d47d095 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 119812922 1250 119811672 119811677
    0xd060b042402120c07030c0806220b01030f020f10050c0d080402030a030807021203090d0806010810030209060604030609050307060615050f1317060703180803040b060316030b01060806010807 84
    0x1008103000d68140f19402022030f48010300c02c0141c000006018074964800034828100034001604000550b50303000c07080c405c0c0d0004101d10304a646e00c0458000c0b48a181101c2d0300c052901c01088491000c078104c000302004442e844145c04a040c503110340c2010040c0700c0301f0300c0803065580c040300c101c00540303224800f0380d0302a402d58403064070354000078082c04001d900503e05004485600b07110819290703042d8400c688100c0c050b00806002c00656812241540d0017040908101c481c3c0d01e00352110010303890813880040c0c492980480810035a48035042101c020f5500414103012804003410300940d66400404101e4070315103010000602810036910084411490b9640d5a140c98411034102c880340c0c000728513500300e0b4281c1800004071f45104092107926441001c01034015450403200140448400d50751200d80310b4100c05e00c1c440000e410070106c1c0c0d40a0350040c000c801e5030302c480020900c0c000c0f12405140c40c240c00400c0105c00d010a4590070740c103e072503690b100c0ba03c0760f03504001120041c40c03c0da2402c0c003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 119814172 1250 119812922 119812933
    0x20a02090705130303050702010807080609070c02040b03010f0504050f0a120309060b1314060102010501140103110909040b180c060301060305150406061107080705010e090703020d060b042402 84
    0x5191103040c094201140d4502981801a01c03003548042c0700e050741c42103011840c0000c0400c07c40d60040001c2d0360000d03032400c02a665151210120f0000c0c00018104010403c0e21041c0c0d00440da640c1d0f11250341030700090f008000c5640a0307241d140050000340d03000d488034410780c03038907003c40c03440040c511286503801110b046081010f1401500076101a400031101c070750700c50311198080c0c0c40d42c1c04031206903a030031103002c1140c0380202620100f2800c05402c0c54116410000180300000844003041201d610a103000110b856095441000034000d460f11164407107100010720081c002000d119038044c81281038210305118004600b01e0b07407100c5040394580c002c00144010000940a5402290b10550074003440a85000820000c0e00311a11a0085004188141200c80003136104200b241e01404841004188040c10900003801641c101600f0a01c1814401c1c00030f401e9610030340550310104407003481849110f031201c442440640160050014102c840921004010a0200e036a405144a5000b800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 119815422 1250 119814172 119814193
    0x210e060903070606090209150c07033e01050906070302010f2a020a0c0312030b1807030605060903120f040f031104050c1e16050601080f0712110607030905030a0606060e040c02 77
    0xc009070400310f003410032741c01040ca0000205d055020400d507003540c2e0328803904071105043c001481e01150500301c00354055103d60480d0840e46c0250854100c04001c558070798072075a0750710707049015041814050700d0860a00d10b8401403401e0302e1810300079044020340e0144101d1000c804c03c9a89041200c405040701e010b118040012401c0d03064410400b241c28a001715040b031000e004661809480d60361151254042da0400001d01e0f8584640300103040c04039691460511014002503407112091400400900d0014200c1c500e405694101d8000f00b96000d5114101541d0703040c895504034041905502a50074a400603c0c09018007045900948102404007264002445000f6460b0800e800c00260302164801e0100420380c20071285008001c030303c00405010902008060814034668400c20002c1c600c040c402c00014800d070500c0700c07150700c103548203501c950f614141143c16081d40e40c4029094040c1d03001180511089030854003c0d03c0090301e0340c2c00c80b06401018002242c41a07108000141c21400511 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 119816672 1250 119815422 119815459
    0x5030c0607021c0e0a090c1805040b060304020603092503060c08040302152e051011030a081003021806010e0a06020304031e02030706080106030e0d210e060903070606090209 76
    0x41c3c1c0d01d080043c0c03481c017070551642a400c04854044011101046422410906d00760078210706801510302038030b05014400b41c50000c515180000b80000303106000c00b00c006180120108000c0c41038461000d901c40c000280c8800303000c04203c86000c142c8480d81843c0d14480010b01a01842d40950b80c182e0090042e6601c446900c1514500500007942000c01c0c0c44e041c6082c6100c121450003a0039041500d510018605000c01070400002c00820017803050f0045404c4080c10040142e50219602c0d0a00074060756030751205542042290704003c2d07000e950003c00801d080c65003100700b13102d90b10a0301c40d07403032074202e40e810400c00c0b00c161f105540c0140d1040000b0b00012b1015040300202c0c141d01c1d845040903100039800a41031480a8010000141005004115140c0d0500a403521005101c002c0d00c160381002030b00800d060000d04d5100300c00c0c820440e050388050031591283c03800881d00003c0c4d8610707040202c0ca10381c503548080b00c01c0e14049d0070b000d40404e003401c0b41c3c42299140c0074010001c036003004416010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 119817922 1250 119816672 119816687
    0x120c0e09010b04150e0a09170a0e0306040f021e10050903100c03021e07020901090b120109030f020705060415030504140105010f091112040311010204030f05030c0607021c 75
    0x403840c955200c0500b81c07080d88582c0074110030482c0b409200000c00c1d04200041c0250130000b010200580d003000c1c48000410b005090740a00e64141d00443c56898130f6004c8291143d860011300d8a4040c802d18041000340890f18822000142c42101c07007800c524810417811401d82c54003510194440201c2d14601b101501507001040004401340c1919840100d1151400484402082c5180030033b400142c588180380da0103010384240c0c48600444c80c24001e164010131800c9005014114041e42d644da0080380c1030b903a80031004100c810301070091050940701d181c0140302c001c40024600240c0710708100440c1500c1c10f20b0a0700c0954180000c490080c0c032003544210064000940b040d14807100b51000b554890100703000d194081c080c1e00300a0640c84c0c8c540440c107402c688200c500c144c410001071010740401c031200351450390403e4243c40c01c4408518116046402423086500060041e0500d11691007000340100c0500f1001c08100199480741e562201c00340d0300c8045580c40c0c00140c00c1d89590100c1d116024881 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 119819172 1250 119817922 119817931
    0x1002120a0201060b03010b030a0501080604050307060b0d02040e0c010305400b1014040e0a0f0311030d0f0e0a0f030f0203120a021e090d06020f0c07030b0907120c0e 72
    0x70900c03d1341c40e20800c0466100380c0000c00303042c0001007048400304850042500401c038003001400540340c03a441e2280c40c0e00030340800512035034031401c0505940e601c04a90a20154000300200102d4400100c640d030703210b420f032002038042400c01c0c0006002c40c2401d1034030700340600c15010010591410b000e00d0b0a9a5101300c00c2d500300c1541040412010600c0d403201d052241c8616642682050b0078150304158002044481c14031481c00e0017084007201401060103d40766502241d81809512a443e0540310201403041a440368800420503221504441d04107052030301012000b00540e0312003000c0c050b00d49078940e038050300100205100d400002e01c00c500046601d10540b040e20704080c0120340c0d401198500f5656100c800b070300803880100e070004114498610001840c143e510707110201000c55407c880300e0030007800d899408500c24411030309a404427400d040940054855543e00c0746410f0800c84803e8602310010311038510085968140005c0400341150000400e0218502e40303019482469401403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 119820422 1250 119819172 119819177
    0x9040b100c0609081216080903070c03142104030c05120c01081801060609180516030b280608150a0b070201020c120616031503020402090d15020d0b1002120a 69
    0x105d658104e21081004d540a417054810341048851204d9005140801c003030310100740c64008012100c0081c518001d88030031294890391920114000c030502c0d074103041050764034201d6040c0a01540200980c10b40080054074828900152401c1d290003d0014841500d4400c1e48241d1084003009555030150706502d0307102c45a4019003040451003440282502e28960090001c02c2100e0703818000c00048003484072611100160803c42ca103015140200c421100e407100c9014556a40015089074444e868194844009008140c541c0000b0703c00c0160340428520031400050070140100750f100c0360761000800690002032280398428140412820035a2102030124158800c80b9044d162070380300c0c02c0b11907102095078406411940340803082001c0c0c000c0c1003000c800030549031030000d003803066011040341d050b6a01500c006858100580121b102d106400001411441141a401e64002844c0c0c004000d00300030300c41c00740041c80e0060180294051002043c0000d0380200c0c01150004c450300010300840700452 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 119821672 1250 119820422 119820427
    0x10b06040b1614010519020307080402040e070b03010f050a080a030e0906060d090303060608070e09010e040503070b190f1802010315050a090207061805100c0504050a080309040b100c060908 83
    0x35500c00b83c041d10924800901c5035110700c10040c44200c80b020481075038140310019803551a200c80001c26440000f00000d00c101c0d0780c1c0855050321b000401900f0f000d08082c52403965207586600002c10710000c0b61150505c02c0c4101c5d14003058180f40840e03001c20310b96041d2908241c1c1e0420500f0070800920080c6400c1d0080c400740641104030b511800b960000c0d034003a480000b0004d050060080070b91100401aa050107039118030a01a52a24400d80341110f601c00b02c01400e585881c80d00c6801d41c441e2180251100d200c050034400e4040030507456102c8220580e5041040e4540a41000195081020708240d9170308002502e4000d0750190700f01c2e6121841c461034128400e0b480b00001903c501c4590051081264040381d510b04124480c440c00032035041d944940074150300f850741c2d40c40d42d0743e400d003044402107600c816a4090040c05402901c014000051508800b40e4a03001c450350741303800c10003943d449035042c01419201070070302210802950384a5500c04200b0105511030a01510445a0891381c83c09e04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 119822922 1250 119821672 119821717
    0x5180607020d150c08012105030708131d0106080703051f080c0108090f0c1002010b040606080901050f060a091802030102030f01030507080c031b030a14010608010c02010b06040b 78
    0x10541d0b0001258400e82e15515000c41d200194000c072040c940c250424004101e005014481c0c102c0707840510112030403070f04014490346140c080d0450003201001015654041010007204510503004c2c025070700c84400d84100d40d19210014403100c10b0a2140802180900000c96901e0344070f90062a401592000358080c800d41035050203510200342c0e807052200340c2000e000c2448030360b407111407070340c01903281c60040c8031414125168a440f8034501107282d2040804100c6000054002c0d080004805c00c001c1c8100400343ea00c8401400c0c3c80c0c0122258000c1e5481c000000320a411a0402c850090310080d200c0034000d030030148208010300c008144900300c06c408001400050303900f4001103108080881e0302488951651500070300d414029000020250080480c4440c507440000d43c088010464821074a130044011000c00c0c00c284034a940031702081c4945000144a8005401c0070b011104000000c0118081c41142207088035000c9a000340d200108101c200000910100034007500d480800404901044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 119824172 1250 119822922 119822929
    0x10c020a0b030a150807091e090f0b06010516110301020d052d130b040c05030102070302011e06140907110a060b1903211b03050c0607020307030518060702 68
    0x10554800c007030900c00041040080c102900a070441c200350042c80000050602d0f146603102d03c03a5000781079a00d039603058074040826414007403844441c0300000400040c02241490040c1c2140e080040c1d030383c50303609000305419500c16030445586c80c461404407407103c3c02941d02c80c11842000f01040780c0c035640902c0030030f900141a1041e64011100c0500d2950700f0b01075807007081c60310081400c03800500000c6008001c0d410b04083e501340c0d09103500c601d0b03501c031980d00e62a10700c1100b080c03900701c07940662000c90101c08040e0158400480758070904502030202c2c1c40d07800c0030404ea03881d40c0210300300c10104100c100c8080c10901e04185c0c03c0301203401d080c41c1c0082c3c1e08640501c1c2c140700001c25545151943d903803c0b5541400441d0424508002e0011410b003030440d00c1d85209002d2603410304454504008502d558940300ea10340e1035040c80040407a880c4030029040042048d00600c010050f54090070011883c040c1c00002121125981601d406003000c81c007842c000c02034440315001c107803c03d004014500050342c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 119825422 1250 119824172 119824189
    0x1d070c050102131226040603050c040e15010801050f06040306090204090203010912112d01060b040609030c0e150d03021204060809010e0a200d0812090d0c0807030c02010c02 76
    0x800100f02040105140c10001745120b5200440504070700b00c0020740d0b209190343c5040700c040d80c000d42404a42500d4101c0405c000d031086c0d5000034080c00c0d00303505012010884070f5601d2401002640ca1540b02d90301c42080101da42942c4890301e03800305003044100f00088681e0004600180010f200140c0e040c6550040307800c0d02c248500442c0c50000105c220a8203d80002d40c984041d0740a0005020044281080401e2400b07802250a0304002032140001c10610940200000c0c001c103c26090f2038a94030940942100d000c0e003c11140c40c2c0301d0440224040805865440c840c880c050801e0000850010038410f048040c09415001c50140103800d0520002c1980244000d00081d0f8500d680b902e0101c0c001c0f8215080c400141038150442820440481d40111a40340304107020000c0d000d0f0448203800160301000f000d04024031203440401d50721410500141c0301d038400c0600c50240c491100ca9440c08560000e40d10740010290070043c0072110109101d80d18140103244181401001c0802c1500011900d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 119826672 1250 119825422 119825429
    0xb04020307030209120307050601260d08010602010b030105060319150c081503061902030a0608120403021819020d020d05090d0e0a0303020304090c050403021206040c1d070c05010213 80
    0x2c0d00001d604c1d4140c102107202d826030200c030704055401d0001945c3c50ba91521010b02c98244243c1c03240c60200605820817403c0c0c91030b0b02d002c00480e0315000c56100c01508060003481900b0155107012070101e002d00b4103010701481060300502a00034055648502030b0441c488c000e0a4501941035220711800d407001d0700c070f005d038112100d45034641e05d40b40c807040b900c5018a0b0000000d000303402010078031180d05035060100cae90051200d6809a22a95101100d00c01800c50f40d00102d141d00c6410b5a00c805580050000c00a80307000f5695803801800b9242c80c00d0008409999012800d040d07074040d85c0405200354050040c034500b1040c003528154150a010054544c1078403415619000543c101e401160008110401201c055514150386499910701030b440b40900c2c4981086107440d6030b02e0760041e910030800c40b0050341d8020300325003841641700d01040d9601003c49044568450300c90010851481d030081d10303001d1700340c02c0307a6a85481d660904215010b040800307044034199000d00c400440030501c026550044e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 119827922 1250 119826672 119826677
    0x150b0c0106120b010905130f140309040c0c050d09050102060a110405063610051e120f070e060904090c0f080a020a0506070507031403211602010c081302040b04020307 73
    0xb550400c980700d82152005002020030881e9800c0c594001488088401c1850340c09c000013030b910340185d0b07d0385e90540c4100c6820319446898205540280342d08001d602404a0050045580540049000303941c084114080c5602590205000481402c4250403d48032040130310700340d40c10301d0794031004507040790000c5132001d10341c3c2d1a1415001e00400d440403488021207071105001074956415010503081004541c5d00070400400046444003811040c00307001c58402428402a40e510300b60345614105402078440800382202080400c24552146a000c1d214801c020942841c0c00c20740c0c0204001050f03100022500c04204003400204030003811011001480c0c91406072a00c608144108040c2c2d4000e908540e116140c20f0000701c010503000a290802c1d02c0d031155020324480743c44900c0c640340d40107031124040758054071751801c00481c034040c0020740101017004400304002034645043e030986584400242c0043c41040006002846150021404500185c800140e81115a000c9000d0746d2045606001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 119829172 1250 119827922 119827943
    0x1060b03070c1101020606060915070c080a0c1a03010611150106110d03090c0308071406100501030b0d0203150718080c011b05070e07030f0203100f0801150b0c010612 73
    0x40c0071001c0180f10143c10248007034405c0c0d00d1312400080e500d0140c040030354040c10000030150940341c888001c80d1165a000004811345607130395082541d0b5a0014201202c1d00c2c00c4c0c0c0400050900b062000700f100c4810201c600078216800c00408442040c0031441501c0a84109010b0300c1080001c4004580170b4116946d40050010114080a103443c0d80d4040711410181f501640001140002d0410f4051700d600500d65035a46415003004280c40101141002d120701035282030003c0d0500c02801780c0304a40c0c080e203092000c00c00d402c040282d032049099020f03415030014110444c107540000f2905601000500704000580505403500e566072205800c2490b2961180c043e500c2103607040fa04911b8000e01c0711016040403070242d91544d8803480280b01d4500202c0319000071a554500039000b941c98076203840421500ca1820310822010703114548104020014180c00c003181090307040c080c1941803252150001c4040345800910041390340001c1034240030755a50140072410a03000c21200340b0f124068034090a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 119830422 1250 119829172 119829197
    0x4050906090f0331050604060305060a0911030402090a06080a0605010f0906060504060c0501061a091f0e0d0218160809010c0903030c0f060608010903020c090906040f0501060b0307 79
    0x20b281203601c105800141c0d00500502d4144030301d65041c08003c4480c0c1601481d0a1030003400c00810a015412030f551021001c0b5010900590503440b491080d0000c0701e0906505690306401c0045841460701440b01c107900708000760150504200d500d4112280840005286580c0c00c0c0c2e641c102080048210f94075629207004100e00f0024400300e8024080d01c04041105500d080c1028201340300382c5c0300721014441554a0603042c09800e40c4004001d003a040c50494043d5154058640c1c10f50000d005c061041181061540c4031601078640da1281c5c00040e00c0d0100004004810400c0b40c000158040342e01004603404200c5100480d0003c0b4010062501031081032150200c018150b000010510102685840c0e140e201301a400100d4004a0350981820310389540d89080694218480320800b81800341881e100081e10001580a11000c070b010740e081e82c13080000101081108141078500d503030190301100201d80803840c54103410088a02c42c0300005940307950f4010030007003074104a0720000840d01058020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 119831672 1250 119830422 119830441
    0x30b010b03060f092e05010c0b190219180605030a090c12050304031205190e0301021603051c0b0307090b211b040507081614030406052706010311010e04050906 70
    0x41d04821000345030702807550506d00000d2210040000190480344101d003c12040088200910131000c4004419903a4005512600c64071591142c0c1c16000202400d4135503100350f111354011020343d892640c40d240b454132040322050241036441c01c283e61602101d46c0009550340501d94103020a031007200a103031a20b01c0d5080005441400c1d12035041030000401200c2e0b0030440b41420070b002140b241c10440420b10742600468020b015a030b41b040005c0d0f4503160b2010516400c800507241521810034000d40d005804400f031420358150580050301a8048042440512800d03004910541d201402c050f00401401420348040364000314000a55040400c0c84603540e00340410541540c0410344091110781400e000043c8003c070f00400900340f07528038106801d0b049120310200c20501109440054490419050880040006850003081382c0310640c90510302042c2843d04080000410b406400c80e80c1c0b8586640c44240308411307440d4104010222207012990312172051901851500c4020704041ca00444031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 119832922 1250 119831672 119831731
    0x40f0e061f080f0a02040911030a06060e070207080a080c0309130f050601030c0516020105040b0d050906060118060c02010306030c090b040506010305160509030f030c0d0e0a030b010b03060f09 84
    0x1c042c290010866240d1500340007448010b41a815140090b0510441c02c2c81522815203006695040c003581c00b6403c1480b0150f004031058448048458034184c0761144142d80c1c0352480e00c5200304e076070880174100340814041c00203030001c20111420b5034580480800003402c140702d08030303d40154981c0c843d210300300c08240d03208040c4e12000c00e0070100300c01c84101c3d0300941540589072140813031800c01801201103901c01c0c405c1d54001c00b01401081e403610454215603001e84012140d0001d1440ba0038005200343d0310a1034141200b00d030301380340c03009180c1c208802121401982081a41410303201c920010000e0301d1005c2c088020f04e100c80b00060200040350400056940182209042500780030500070040c1521a410390280c0c200e090450740c030b040c10404030f42881c0d032504440780745010101d04100d1a02c00803270302921030501652060381c0b800e203038420450b0031079207408040c0c60811048010f0101e0b19022000b5500080d00410151294242c40c0001c0e240321070444000c00b118288d00159040110020074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 119834172 1250 119832922 119832929
    0x30c01051303080a021c0c0509030f03040303050406080907051309060b1504050f01110a03020c01091d01061b0b070504060e15090904140a080a080c09030606040f0e061f 74
    0x101070003040550320002c0412001808695820750300003640b40d4445407030010400e119150304410301c401101d108010384203402810307050380a4010302c1d10001701040301108840a803039141c6c888605003400e04030126951003005001c0c2906106804000c9040e0b44c507645090400c42c0d10040116540c0715a280c20410740e801495002c0c02880f054895900c40c0c405882a2410388400b0380380300d9005c0e1441401200e1882154180002c0c0d4001c0104020505a0101e07030b5209070f58003a00c41100d295607600c0282c1c4007141c0e400722107402414100052124500c601540c2c0145031495810800170580c0c3c0c0c540c0e02544500b42e5100f400704400040800020f0340000a000209404075560041000040b06d882810300c100c0c15918851911000010100b10708850081c42140707510040f134415086524084680b135001400b0344001c1752924000a091213014011104d10742805000751a090316046c003808050141c1041c0c0041c00d680b180084500d00100b003080c0c610600c8602541e00300e0b5410900300360148101c1e42c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 119835422 1250 119834172 119834191
    0xc06030b09090d0f0c0204020c060105030c0904200622080c0109030503040b0318120406080c0901020a111311040306180302060f130b180f06062202160302030c0105 72
    0x7010000c18080101c1c500c1842009820000551032250204541c50000c1c4207000b0340c45880840d00c0c400060f000105981615001d03012114240080d804000c078600003120010302d403590500c02075a049908628001082c0805000b0380c1c14000503140103024080a64503401c0900032002c400c008a200c1007141c8040301c80e0a00304000c0403030540d16940c1c1c0f24810f80c010900c0000f00000411407901403441c2c80c400c1210040309a0b0311802400500074903590252040c00d00190582d000315842d00840c50841e40c0000e0160010201c4a0090340c41041004c4440d2140f03a024403620640c0d401d400040c0a1002d0b841d020309151130307850381586440b004403400e039182e51030051400703903403000000c0e00014030320707001015026640ca5540c5c0307a0f4416031404561020042c80ca0040c501407282081e0050300000821034080262090b500303800d0115a9034010031035040e54400459282d240c02c1406a502000903502c87d898058601540003444c005c56440d1010b0807001644001500c0020b54020304c1450780000b41017 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 119836672 1250 119835422 119835439
    0x30c070c21061d0703110303040302061603260402240307030c080f0103050303070c06020405041a0f03010506010914010c02030f06041205030c1801020f07060336032007030c06030b 79
    0x10b040305582d5184d5804002c007082c0d400041030780d0a81c0d08000392002035500400c0c00340e075403408161442107800b26550480c080758540380d0720b407501501c401c00004085181e80140840d50b03165001c010440c05804002681c114001440021542120340114858040c54034040781850440d04000d0880e0b00c01085144203842900040c00040c00100440750000d015242c00302c0d2080460034840004c0c800e0380d0106500c28030b0b211461521141c4904000503d5404030b4402d0b185002d41360074542a1384048407564006412040c5c28065280403140700003165006151544441d0070aa000c00d1070410050020420340d80110200001c001c0c0401001a0010103031074440d0550608400e188200d0060004246e001c0d83e200e010308883e41d00c20040384110341204000c1720251641c41e000a801045044141d13102c080784c0c420f40c0104c1d2030079441c01c07130f2020030b00700d81211581155440c100d8141480350801410715080701500200c4031020030001003c0d500403111542d0716813424102400301e07080901c42c2801405034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 119837922 1250 119836672 119836721
    0x9100905030304060507181421060a0513140309120304060e010503070309080307030e1b060306040207061107060b0418020f010c030302091002030403020901050114030c070c2106 78
    0x3100b030301d80055210201041c2500c92a0050b02d01d461450400f10200c46560000220180e40345000003052006540ca104c0f501108440701240c03500c841c2e1018001da00c800e02050840502d07034080c640c40074202501c2175a0352120345d1041c81100b08010000c409601c08250743c513152910700405021140410025490140b0b041e038044d00c0701840306501d50502001000191030107020f90030031b140c4203900001c516920720300644041c00800303d42d400031503a0b01c01d000c0f184c0e83d0b140b07180101080901c0c000b4601c2d030440e42c0d10010040070398030903901181d0f4961100e0b80c0e5070015079540d001c1c0510074032824010a0485290061104803249001d8003042420012009409030720b0728105420307850030a10b810314071084c1905090303010b40714a00c0400d070400995403111010b10340c088040c2c41a03900c01c49403000240d030398400449800e20900c075007079000b280400c046040d80c2408801488603600c6002d0342c0c4200c0e9030725024001448102c00004280501c410703d080204101841900740c0781156800101d00c4116 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 119839172 1250 119837922 119837933
    0x501110703080a03181a160219170403080d0e0105010e06010302310905010f0e0c0c1903030207021206070e0d0507050a0807180c05070b1f0e091009 65
    0x100d900c0041c010620002c3d080d00c4407440b07900f107840c89107020b00a40c5100c40491904c6910307540c0d040b910340110071007a40072841c01c0100c40d19a4411254a60080124054400042c0c04886910070f0455450451355000a46e0171030410143c40150301401006855014410080c0c050f284042124034103a45040c2c01072040c480e0030100190040005c0ca401600d5602c1c50304042d901d9090340c0000d802d500f0340008444070140c00d025884043d244070940600107a40da07003154102000c83d80c0107621201c203404000034070101d440d802400c280c44944003140d594103c06c44203803030107010b885070540010307400141c000c0a5050403100100d188a6804c02003100746029040205076100800c0e0051080e955a4081e03001c0c018100000c8002d4540102041c02007507503001150b42e6107010380700341c06a42036410240c1c40c03400300c1d40c4a00342d5490b0403a201c10b460701c000c2c0d945201012200510b40203041224460011401403809002c10141000c25049005420821581803a0400c4010880b030030904141c40e003400030340c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 119840422 1250 119839172 119839183
    0x12090b0f0a09020d0b18071a220609091b0210110d0203090609162115050a090b161b0201090b0a030c030c0509090414190309030606050111 61
    0x180e551584402a84034006400e024015403a0040d5000200d103003030030b0a025082d114140501240c2d00029100041a40c040340c45551900c180d002d54a5900000300050304260300901c0001d100b090049646020340040513508106500180d0001c1c0340b510043c856014203103c1e48070540c2c0c2203032030340704001e1810000139610710111380c0340040c1c40d440710740c150582801c510a50b481401c55000a40d201c0c580030907a10390b074a4040b21414810b10440b01c2c64018040c000b0711550650f60382001e440746183d404401c00c030844d2407000084400c2c1c2031503107900b0080c0d00240708081c0601e20844010134101d005042540481c4009003ca00c00c082c410340f002e5081a40280e9405035035141c851402203454454001a5604001c0d80d0010034406400610400c945500d50301c06403941c8a603403403c00502c0c2e41d41d4000c442501032140700380c0e0081e000e2000300e0082050944000500c0f02c3e890102c030000f600447c6034814000161004802240d50705006004210b00303801070002410302841d1a54402600d284a03503981c9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 119841672 1250 119840422 119840431
    0x50c01030b1309050303040b0a0606050301090e070f08060405070609060c060905030d060612050108010204060509120a050f010c0305090a112404030804030302010e0f0d0311070203010e0d12090b 85
    0x503a00c4040d0266074544807142d180441400703504220306001070400329201d5204a40850701c0310350400014180d01d415119200c10342e00ca030394400703096a090480c01070003000c50b04072902c0a40b2401c034001511b01c0000e59060f000c5c09122020700124101803806d2403500f41d103034110030305004100c20244907865014907a1031105800c05004241040e5030305000e0304610620082603141c1d8209140400e030b44ad000201d0000640304108104501c1c1c0e640d0350319a080b070096024074000503108005003881e5281043c07070400c1c0c00c11004241c40304000d641c0d6844c0d1425103254001c2020742d4544030200c01340741d010310a442d4021448005010700c2011561360740a511080b40426116801c98107445a80300c1c0c01034416000c42648842032960b46031a404e203044590440d00c4101c00560078246101c40c41030010509404001112004048040103650154060302c40a180f44030303155014030159000d41e509020721200005488060850140c00385d000402a81c0c402c0d52141c40541040c80c1c4400140d80c02881c0c6920 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 119842922 1250 119841672 119841677
    0x2060f04021c020607060f0501180c090504020c0115180612050d0c05030d0e03091302070c03060b0103020c01150302030c0607030903030e010c06090b071b0503030f0606130e0907060c050c01 83
    0x100744183c800a03400b80195003010700038601d0300b0300c050140b44860744000d050302c0c0c800c41580c0b81c0d01c4000e0b0b0307900243e0780032401031000554225400c00c61400c054029040c0035100c4c20001c140f403070204800080c0301c4c106074440304840f200395108907201031881c441e04000d0009031450780b42812040d141c0c1c2d40c2c0c81383c403104801c0c1080116040c0600344078040c02683e06240300790000380118040301d0072803540ea400500d0b4251280d032420b0300070307400e00d100c520840f9134440c0d0242005042d54034644454005000e01407910341459000c0241108040080c03140900750000003601c241d2140c1507005040ca040c00426609014440401214000c00d40280103030b0110b0b0380c14030b03010908074010801240c040441290041c40a41040040d108024040458900c03400c1d29a40d101c80f001303100017484a154011040c0035003a43c20400106986601c80c101a41c6d0055000d02054900008000c943c6c0d4011001d50022807500c0c108400d0144c414001d104000081002e442d0062041c0c207940c60311501c40800c4441e0906 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 119844172 1250 119842922 119842969
    0x18020a091509030c030b060916020c040f1e061409040302120c0703080301060c03080f0c0a1803080c0d0e03010506060306040b010207050301150504050a02040e0c16050601030f020102060f0402 84
    0x1890300c155410005103920013441e888150b40c0303280c01d512604003921014855400035001400240108001c07034080d0f24142c0c02001c24a0b041c07000e2000805154a4a210054840710000a030103584000d50703881d502103c2000600600d0044014080400b4000c0d081c4110445404d00c00400d0340000c804c112020000e012542d0303801801c144910345100760380300619880d00400002150f81c2c100541030841030190f22500c0191307607070030031001c103810f070494018203401130038020403003000e108403a4800700300c05890303028100310345a07250300340150003844488016078454503424030895400403181d00f095006030001c0c005400e010780010070301d00004107814050f942d07490300881982c0c400c205103401440050020480f03852039001c10148401c0600a85001d68200401304810051034402c03101204e10602001c942e54540600d0388040f03902110031004022020290407000c51400d100180c001d40c412108883d02e2102072001a081c00401041045800c0c446010407000da2a10680d0303503682c0300340408803007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 119845422 1250 119844172 119844209
    0x30c04021e0d02091003020912010618020c011e0b0111070605070f05010914010213050a030206030f07023d050402030c120f01021611150d05040618030918020a09 71
    0x10b0013409500e03e66540710022014081c0310340d825034001c0045034019500d190801d40345d203110702d081e5001442125074001d441440c0c04007858081c2c0c05000003041d410000724101c6000c0c0d0782000c440c140c40454507243c0c1e5403408550855a04201c1c0038070f02c11211006040c01c20b180002c00b82071405040805406052491440801c1000039486110390a82c4a40d021703c0100f2010b0845000390483c4598040e580c0a0700c07008101841d0111102c0200ca90080005295030b0f1410f0001c4148000505202c0543c4212010803504070070351424072409031072014041c18910302c0c2c0c540c0c2420f418090709440c0c042c2890300f018000940c4010075500000304058134881551040560319030315103000c7c4011742445510203d41040c004046d03007000103c0c0c5015100109804003c072041000c00381d00a101646100000c018800c6c0e60283c603000f05502c64007501000500014205200c040513100c25030880001302c0c80b4000303100c1d12002140b0390005000b450760440c100b1400c000e015011880500a1001003500b461505 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 119846672 1250 119845422 119845447
    0x70b09041b08012c0a02090109030203030301030308100f08101e0f05010504060608162307060c090b04051c060905010213030308060607110904022409030c04021e 71
    0x6825150080307820103030a0100c0d01006000344400e00854074201103510510f00c1402c4122440d00c0d201102d01580010380e169803c0755402540300c0310020303060042c9810b001026a5040c000781d4000d501980781c0d002c19184c00c6c100d0031886640c80e007046070034a66a42090100b544002517030034080d4100b1900140c401d1a40d801003005d558207140c4803003c1030401c10a0b04900450350441170480304140c1c1d083c0001503c850b419540c40c1804c94008444560501c141c0c12800e00c20030b41448803800c54001c01c1c100b0500d080d0380c1040c5a00c6541c094850540300d400d88106030344d005005400814000250a0070a800e00c0d002601100c040040808100444004c1405100b81036128001c040c1e4400003c564480e450400d20107003585600c0294086103074080003a03128140a0101c03401154024458404684150104030b8100805481030303800081c4440c680400d1005070080c00000310b11100c10645803500801090b1401840b588510301440c01808640403244202154100d0420800b00b46525100740e6600e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 119847922 1250 119846672 119846681
    0xe0901060602120409020a030b06041203181406070c031b140a03050d21090b01030c0b03100b1602120105150103090503090f0d0b0f100918020907020a020301060b0a1e02070b0904 78
    0x10f0ad501880014002840411850b1071484a40c400e0700e4090400c031009501c540000b030700e44203860001380481d030542210b2505000038000c103071052540880c601d89a450b0100503654106451481030840c0d00c00348590308650310442d001040854075280d82505503640c441c0c4608002d08008280407a4004000300e001d03840320340d0f000d1514840c000300038002c00c60901040c0c0d08001e10040d50005143c08c008142901e940c811203110390a20400702c5185c80c40c00040003d2540a62500c201d454000e075040c0b00140e0301c500c0c28040385065900089998141800e0100040c6220700e100b0b410315103003458000011304048240c4518a0301102d80c00e00d08031401002c00d54020004070010204101e01c0104100c4805034288a405100b100491182d0b103900c46022000f11a9038000000440c0c019099034001484c000c0061644042c05205840303440200c0e501203400e458441d003210072441e002103884182c4541c0021440312380d940d00764400c80c01541c4070801070344501e090b003d0034500020001d841c008540781c0d03810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 119849172 1250 119847922 119847941
    0x9030703210806060304030c1e06050a050a0507020312010326040303050310050a0b0711040f02120108010b010c020d0308070302040f06020c01021002040f0608060411040e0901060602120409020a03 86
    0x4041d0700040c1640c42510501c12803080c48080755444020502a0801030181ca01c80c40d855140e40303003000b5850b21401c000070100c100d501031440024030850b0000d207060107014000da0207510081440d00344640d1440c2510b000a00207400c641c400d108a000c00261100c1240c1120b404c0400103000070441c0b1515644d02100f0811581010f80010b00041010360100045200f501220100d444d8070380c4030820004410290303c40d401054800303028150124000e004104481c200c001d200050003603654210714140c1e04081c2c0820300c020306103001002801001c0c01803002c00340d424600310720b60400035400108203500264003d8200851a800542840c3c0203038110f401402c0d0b1581c08030301c0700c3e5451500030b40c0e0343c450885070b5005004081c0b40c080b5507001c5000381d50580307c1000001103040d0503c903080b50061401031102d40c1c045e49428404401012840c003c0c0042d01b2210042a02407900c0103c0070700b5503006900c11070856000c2041c84e605425000c0581c0e003079400360140960381d9248501d04070040c104046 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 119850422 1250 119849172 119849183
    0xc030f0a02030703020c101409030106180614040504050307030c0611030f04030f02060106050d090203070b03040803041704060e0603130b01140103110f250c0603020417010203090a060209030703 85
    0x1a0549205400102500f115032196084491449032070042c0810107007840818400326510140c00c0c0d1000c20020060401e144014000245860b0303641c4001c4030402e1580d6104010b1692051b0922041e006199510b90f1a00709032024029400c0940d280d95403886080c1024040044064602040283e1070304046a400c024000c05522824034503040000c0200a84044000c1095041c0c5012050300104140b0b04a451036101c90b0305040503680d484001d0a035541003207074140628080030a4503600200518000c90203255072640301d140c14600492000f0100f58a02000c1d6810700003048115403069070442c0240b410390310382da240d441c3c5444240c1d400d00c0d03d000081080000d5000403030742040c1801c0c002c000300b400342d0b4180a180807a1411400a00c520104192115000c000790707001c89076003d4018920454a10f13203405220701d20b0f2246506040780d0b400c40e0f0b0009400150410140c01d11004c04c50340362102070001c41c07441c180409000c0d511134440c00020012900840c007c0c90f51350b01444654015074002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 119851672 1250 119850422 119850427
    0x606030d0e0d15020a0e0f0a0306180203010504080301050411040e130f06050f040302010510061403100812130f1412070f260d090e25050a08060402130b0c030f 70
    0x480203c8069045030b0071500c00175400d450404011300d40501c046c1070721100900302e05081c03415502c54501404c11072485850702d62490b04102e005840034480d592066010b11909a01d030350400f8104025501d602460300204035040c40144010120141440e0300030040109a84002e100c910706131603e0011010068020b0745403408101c00381c00551a4144a14400c1d8001c00903640d40b0f407001e00c07106405001700000960008420382c2c811850b07500441e00300c040c0198400516640f080d00e41d25298070303042102c90962001c182241c00001440c5034401510340f00c04d0300d001c0ca130704103000340200e1941c03496030303510038100c082d403003d8400000d20181010703114080c2149070440d2101070310b0780301c1c026002491002010100c0c00e02640040880c110300e0210f904c0e86c1342c12810f490540540445107001c1c00c1c2581c01401000c100f591070070300d80e10105e001d03034940d01c07103075104c40c2501005091588010640740c05980104007052881010b03051413019210760740c00607a164820044c049107140510740300c400046100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 119852922 1250 119851672 119851703
    0xf0905071806020a1b0803040b0f070507080a0302120415030b150a030c090807050303120907150e030d02070e06060703120504140714010c02100c02030604150e0606030d0e0d 76
    0x10654140740760081c01e010031001c410b040c804080e217090b8070420b83c3c1d940052100384111000b41e0010715602001c844d1103414034400381c4406041030280da00403107072030b440602440100b5805120409020402840c40340c100f40c42c024820107001d10400f145010581e40b4800c006990740d580c521060074850143c1d1081c0c5600c001800640240090180c02d008252881c04c0001c0d2a0b0b03000400405aa034061301660500c3c40c1404000301480c0c0c0074115042d01d018918000c1082e40c040c2c1c451959441682c2c5d107042d05004004145030420218000d400110b40001005202c3c2104049005070040c5064401e00c0d9208802d04044492011180719101f0351030a00d400d01040c03180c01c6404c1549455800180c0e480c0a98850200d0b0319085507130840750100d88018080005880c04c1c0c0c8501070300c1303003250821661034400d680c00681080b01c1118200c42000110491005500706445000050040d02c002840b0300d00b410301c0007070f684000030340f4280304000000600401c42d468030203404a80d1544000e440d82400755 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 119854172 1250 119852922 119852927
    0x117031c050711010207020a06051b0303070c060507030b0108010b0a0513080c03010e0f06060603250f0e030c0a050d0501060509010321090e040209040212030a0c0b100f0905071806 79
    0x1015501180003d04080703201c405200103208032222164000d05404185140040517030321504400c0c001c45184030301c46070075985444248001c1d0b110340d106541d0503011314154a001c1085500c003818007001c16281290f10582c50341c00c00034081c15281041c0c0100e17103c0259800859451050918008030b40280841c0012440d0b030000d5040d4040104034024081120240b56407991501241011040c607840603022401d2420014011a041030101c550080c2010301b480710242440d914151120000e8054158603801a030301c120005070b120382c110302420078110340000084503180d15006442c410709030260b640040040952160300140806480518950307901d04210b661744958a0900b40a03040401040c0100340c820100d0720b040d6800c4900a040644454080c4409030200800482e04603081c0003550007034110810142c0365020b070b1035807031030503080991520b2135007110080c10b4244c160781001418450142840801016103180b50703070000700c40d44d44110032503024402d00300150460442c0c00c404100c095 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 119855422 1250 119854172 119854181
    0x80306010c060b10020f0f030c1b0109031a0f0c04180b0402040306090b010305010f02090105032a181201050403020c090703090b010b070b090a0c1502120409050106120b090117031c 79
    0x3014000c0d1001c1c200410081c23a241d209108030740314030740c004491080c05007000b001203844010061503e03008840d00da03078607880d260003503681007010107409100704010300d070080d40c140380d006801d000500d00380341c501070601d4945540c1044c200704090320344000a03084e031101d0341900c004680019050101ca801c5080003410100e080c041034809500301000086400c0c03141c02191400f21040c0d642c00d1840c0e84040268401d4541140c1d1a0582848503441544842040001d0440d034092010040c003440000c81c10052490281c81041100da4180010400803d80200358081c014a040d558002142e41c3d0b80802c50040038602d0307000304558030304c1001061110103c4098401070344100f0002d0f0316515200d0307135a6924a47c114000b003d050764030005000002d104020710741505000d004440e083ea8060680140782d41194000c014a03da44400401c0f07450f0b40b0030300300081c00d41c8182041100408a8000c0f600c5c48005008184c510b03d40348411a1401c4002c0040756500d6050504a0481901c206100741c043c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 119856672 1250 119855422 119855443
    0xd090c06030204031b051c02041b02010203070315030f020d081201030f0308130b040311010204050901090f051b120c0c03190e03150117010b100203041d04080306010c060b1002 77
    0xc4040e0850b00445e80000b4220200b0341c0c41c01402e0048285541402e000305640c2c902040360020786030310f0300308012108444401608401c3e40c00140c0c0382d242000009048513290750300740800d0001a4020800714500c101d80c02460b54050f1600c00030408107007082d099521070140c0e607150308428403000000748003e0501c4040381c42d01c1b030340d40c05206865103902c0041c441d071240806003d00c0401000305000030b010318500c080d40002c0c98000341c00c003680c0764001516907409030300c6002200c0e1188680300c104541442140d40c000121201c0b0118201d92107503101c101d01911140000110490740820000e610290036680031102403001c80307517940f008100d00c800e20100b641c0841c0110b071030221503c0c110302c0c0c0410300580e48021202165010f81c030344580c0400c10381c0c24148c50701d050756035000d001c0281e480d5072208094940d03c1c1d07001596070301c1c90011000c01d40500144c0c04c0c1184c2d82d05209010010712040d085035040403092a114000b80e83d50b042000081442501203030340007040003281760b40150046400c5140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 119857922 1250 119856672 119856683
    0x90f010e1005011710050411090405010f080616020c0a180605010302030c0d18020303071406070f140306220b03060a05040507060807180603050612070806010b0d090c0603020403 78
    0x40d880781441403803940c0ca60700400b80802c4040941442040f240741d80b070fa07400700d0003c07444600355540784040f408941c03d8009490003c000058651700d141058010a0f0041480c01106200701e40303003100494075507101400c031001d6809910991a02240700700030320440320000414080300b50344c0c1c9034166010746160039646000702c0d0410000140942c007034400e4a02c904c02e071180481c548000c0b00440303c000e100c1030a1820300700031150b040c07d0141c1c0f0104098200140304048072841c0c4483ca001c601c0ca4200018020802c0251104500089691141c21410913034024003140d0384980f031355000280d54aa40b4007644043c40384c1c651580079100e0041e04040ca803040c0c00c3e0140c40303407901e078640c1110542d041250040c05560049208110451050a40c3e40d0b00c580c0740c1c641000107030001e81c5141411030140d0310500000b615401071042c1450500c0c1100e000200c3c110041c140140ba00c2d29680c0c0350401403091505c000c0d40860080b0040466400c1800342c180e10242034048940c81e0b00001c0d000f0340050109442 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 119859172 1250 119857922 119857949
    0x903020d0f1209150e030309010509060c011121060a180e0a080d0b010e1e010912060b040e0303040b010e07020c060403050d140f0906090402090301140114152502090f01 74
    0xb04c4600980e1007a480d100060050362a04040e0401511035521031101690032000030001d4051245080c03003503c600d12880440c80b40d440c0c001c5d804108d0881425041001e92810340380a22096580d1141504222418280150300c0c890061060400030421503203040e0aa0192013005000c0214681c000c2500e4108803504100e0008a180119045d5492000b1640c0000f482a0103046002e003004041c3c20b1900145412a80c15480300c04ed50100d40502c601106e034252501000c074018505030080c00680a402d500440c1103141a03169040c85640c1842000c010b0100b101c0420001c601c28003c40c00940300203080703e42c0c5c681c1e82e4a026659160130040c10302c00286030003080c6a501c15a0012150102510031010703080035401c0c0c1c100f00c00b6a00c981020b991181d420400721020b91000e01034034289803031640c2c50100d03642c504820303030050684196010744142d000ea55454040171882040d04c8400512007642c000d07840b80c201030040d8070090404065884170b002010814400d8002da140c60580349607400c81003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 119860422 1250 119859172 119859209
    0x405040c080403091d0c1806040b0405090c030c030402010e0f0d051005090106080706111009050a0605060105030709060c050a171306090311040c1e020a11100903020d0f1209 76
    0x118455100580110000161000c100903c1c2c900380900b50885158107158005440c40c7c000070340560050303208004981000c40c00300001c0c034041502d540e00c142d9901d40b940c990715001c1c50712207243c400240002d0500400100c10b01071510b4211445d00c003503d02411400d440901820b00705c0e501c034642c100306403280f8241400243d81e0501070007010b04407100034005044203800d0100c1652900c0801c00c02c118180b14174021415607103800c2c000d07804424055805461142500d060000907074400400c118103100302001480410740c0e00c403029104880482c42c00d507408260618105007000d03070003240a810b80c0007588481445a400c0c100030000c0441c10400344941e55541c2805a80c5a5030303d04c40a042d00c5d00f00b0311164640d0a0035080080c00c4000d918020748000f00381c20344640e04105c4200034600684c8039900790820000010406050100110b690084554403920003d04d60b0106000003030043d40036400000802040102c4003040551001c4412403070031801100900c82e510341d10410346c0300200c103040507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 119861672 1250 119860422 119860439
    0x1b07092306040c080606180307121104090b0118020405030105040503190c0c1701090210030218040501050d060b0d14060402150c10020307050906070b0106110601080c090c0405040c08040309 83
    0x3440d410000342c644e110569074034020400140c01941c51b02000e40780d02c80760341031295018850714014101813111358190159034100300307410340d4806444034042c9103000c60202c0800c1c0b101c0d034960304454440701109001c50f000b4000c0c602030700807503000c03a80560a06c0c044c00104440807003d0090401d48000000516010240846d02c42400300805030040381880c6040c04034400003201c4c03d80c5400084008559000d00d540030440e1880c84864132000260b000c144410400303603001d58188001c1c000c0b50140015410200020000c03240c4039002804143d4944c00301b00b441c2c07a4040400704294200c1c001c99a04490f00100503141c1500700e60491203601040740484100c642001950071402c4c080b002004a4038503009568004c2d4406800d201c203000c0d050003038207080e0f900d079002000301a108030700c41905545403ca02622510519001009540041d001400b10010000d604402013104840d244503903114012a20034503c03c54008a0b0000c0c180b101c00300125810081090045100707030f88010086a440b15103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 119862922 1250 119861672 119861681
    0x601090303050d05040221060108100e0c0d02041401090e0d0c1a040302070909050c030c030a171e04080a1208070e010503040c0f0f06110d051b0709230604 68
    0x1c1c04610280060b002e4038846510a641c8940f018000c0100200304420789503860324001808440c1c0c0d841035006104c0e1110900411520720f002c0c1c03030184542001c0f000d2494644c01400c22180c040c200710108082175681b02e80044400c00c8200c140305480c0d585842840c0c015010b8802c01303c40900c510300007040041e2086c1682241d6a8014141c05010149139450b40f40c00140a0016000c520a84a000c0f5103500e240c0b084400307e51148000b040210080800e1505080311302c04428481e8201c50032400128400d565500c0705038800180c55980e4000440084003081d945801602d80c42d5008640800c0031000040c80a0429000e00342c1d500c06842c2041044850b440c040350f01000144001e506a800381d40640050741d0814801c0c0006a45162507035142c060100f241c0d0f0200b07044607500c0c8410040703181c00802841c0c0e62907030360303001d00210301e42201c01034107502c1000f610701d040d140c07440f103208908401880f10801506000d101440140000c8910010303502c0312000c08031801c0c80600118400d071919104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 119864172 1250 119862922 119862929
    0x7260705010b091e040c0504020a120b031903050a05130303090501020c040b0f01030c140d0c0908030c060f0702030d060602010b120705030606010c0507090c0f03050a0209010804020f120105040b040b060109 90
    0x460071040c0c0c1d0407806440840d0001780040728103041c490400300d01a84c650000c0c1c4020ba13410303960122403140c45110082561a45c000d04c1c0d01a40000c15888040110042c01410403501030030440d50341c0308015011201481030b0720301209030300d403c2ca0001c030415038000c5c0e940089031400d9003114001d0320098100310031650502c03881c076485040b0211860307655000c1d4000c21400c912a0516000f0388121090803061540100301c0010181d070755480158405070802024000703040b0780401103060442030310740542c1d81e16000d440c0707201070645000001c01d0b43e0320030012543d60b403040040034030220356070704400380c040c090120b02140301d40312100403807940c45000030b0240100c031070040c000c051648410740107407510500d8142c10b40780c0303010740071002c0f03144810350107084103030703604c9a69044030100d074180e000b401c451001e400011400d0040006113140e07a403003042c0c5500141c0441c2e01c10552440c8200041e41006144200c000c1c039400e042c04c0105115501c01c10600c614065152202c5c2e680d101001101da5940d0b602 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 119865422 1250 119864172 119864191
    0x602030315060315040c02010f06240507030c0609080c0d02010e0706021513030e030a050307060b01030e06070818120705010605040b090114060403020909010b04270807260705010b09 80
    0x40e404140c0307806c2e04124001d8980f8000014000050f1401c2d03002c3c2c450b280c202d2207a05a210712481d03c20820000c810a03a0030061814900300601603030024400d01c002403020f001030351510500340500c0320900840e8440e0344024101ca81019101001a020b0004502c4a501c980100c8800151107800422402103461700c1126045181e07880396403201c0700c48004031090b801c00c00a0074000300320361010450008a035002d0001181c03903081910b0320406440c103440c240d6041509101410b8a906000100241c00c50b210b800c0c0b4a04554800e10026000f2000c41e1007114144600e0f00c18620502c640401090024002c0000348001511002808151000180002e030030800050041082e181c40154175910398900800441ca41592600015104c4800352086103203655100c0401c045450f00384242e403910b48141c0c0052183c140644041001040900b00240c00c1d01c5c00082c0344070400880c2109181c0040d2070900c01040341d0301c9903c1681c40750700016000c98680d0700c1e1010104107440c1100c2258030800110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 119866672 1250 119865422 119865451
    0x606010f09090513050304060809071d010605070311070f1a1812010b0303030f0105011707091211030a03020a12110a15090c030b060319020303030601080709030c06020303150603 78
    0xc2c2504005000040030741451460602569000130030038402400205241e40d50004641031444203d410103c46034007031062003400101201d41c4000000860b41140c0150400c3c030b445681505080d5101405606592080d0094840104040ca07004440205850f44000415580050406403104a200c0c81540c60320b482c445500d2100700d4035080a00c504003107161000800d042c3d10142c0840e10b10313001034070015824525440140031039640000304540124a04a4200503400c190402400c44042406543d810030891501d501c10300c05581040140082e002c2c0c1101c040760b00c0c500700252034105801048a00345c6000140d00c40305445442864604900ccd4005401405002d0f510720080340716900101030026169566000896142c8021200650048040074440e140c200209401c04a20000d100011a5042000030150b2000410b80740c0c000b0007030034903045985a1480580c1c0b41c144581c802808110a0304d80441c102e0f03404000b550050300515149041c006d07649041101034001102c00342d2400780e40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 119867922 1250 119866672 119866679
    0x2220c030905030904150305061e0a1506050906090a0e0a05070f0905090a0f0e0c040f0c080c03060d020d05160603060b07061e060303020705030f030403020d0605040c1502010e0606010f09 82
    0x40e038800824140b1000ca618031b0360b42c0e42d680300c90821200300c0d0040e4201248143d521070a14074036001c0740d446014030000300200d4691040240300052a8045c203800c0000109883c1540e0f140e9100311450104005c000d01041d50341c0740c280307060415080710003502c294101340100b6000c1d40164000300119090340c80e4041400d0602c01401142900208a00000f50702c6200ca901c000c240d074071960020a01a4002d030021412000900040d92101d01448600c64580030310b44031416030140301e4a801103403516106551351900304c00a007100e80080341c06980045045003880030000001080c005145013001c40b881119a201410340c21241c052103540e001003001c000c00b00000c3e1a552100d154181000d66000ca220301c5c00e0101002ca0710250400c4025900c102d10078000740c5000c0200300920380340c21005602d8107055602080d0340880b0500024030a688541c003203010011000207002c0646031145600394003603c0c0140082c06068040c0070242940039a401090241d445045071031682042c5071100ca807110324 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 119869172 1250 119867922 119867929
    0x609290f0c0d05040f020109050907022e050108030a0305010e07080103030309030c0b1303020609030c03090d0302240414070e060112110a031508031608030604020702220c0309050309 80
    0x4090340740d0070704100324504903405588680750249004040004948445100141c0300c04000d400c0346116640010411110030760004010348403481c0c061460712611001025614580c1c14000e050645504083c00403540d59000000340c61240c40a40d400c1c07003681d030b032010003018540c8181c40610010b00d40750010b20101e4000e42014041078030900d0080c01c0c25541d07498114a0003026030710003440403030648907002131590410204d50000c1d08203020f50700d41031750156920b42d640300c0c038804c0c280030f04c100244a4003818024044c1400504010442c2e2091200a085500e02c0c0c0e03004480c1115243d8000b0f240d401c00e0701e0001910b4068851f11440d01b40280c13199001502c910060300c0c0c030040912317200c000c00e504284d50b1401805c1e4620341c1e5103001c01d4114443d458840300907480e81101030680e000740a410540c078444c521254541e9007200e41c8079642d4668030046006031080000c065088264003d803810f020000c0b01445189007840141040340011048080301501e02014001c0c01039402440509103078074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 119870422 1250 119869172 119869201
    0x100507031e0915050411040c08060324010510090906060305060a0e06010903020609060f0705030729010e150613051003090305031906180203040201020610030807110103060b07060929 80
    0x1c0c043e4004401d2160a06d00180036250381052040c0003610034024060345007030820041c8000c1d45120001100404020021048804144a1148034042a5640c2071209000b40030101c007625a10500340501d54035014041d000d03200590b151070041400d10b80c00100032200d44111401000140e540300c090629507020400280c00c80d415507a071189041080d03171f80c450504002098020f00c0741020350f40300c0d09a030030680700c0c10b0410900d07400000295039034812221001c01144c1d0640750500750b10b0040341c4035188481c02c54a99581011340110b00007803502404c0d030880340a4811179000300d0740c02401c0010903d040b400c1d00d00b00400140880c8082c8040382c6002d04150040206420f0100c3c00280d03a6900c080080200e400c481884d19080c0d400014802907580c1400315070fa1014a08082c400400d19607a64103070248101c89000c1c200407007102500050741c0c07098000704000c003500e460079901c0325140e082c00402001e44100c00c4a2460003c00c2081e4508a003400403022040b1401003810160343c3c186c0d203420100b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 119871672 1250 119870422 119870431
    0x71a160219021908010603060b22050a02041a0c0f030a02030403020d02040e061014090103150902030a12020f0712020a120305040302060708040602190c090e100507031e091505 77
    0x2010b218880080a040e822441005002950010034441d2075408c0c0901150800e60300d10303014840100018956a91401d071a50316485000c50000d030780c0e507610000c04004e0080350855031501d081150a41e9020800d40054401c10701c0d0402910b1042c0e8007000c0850340d902c610503a550144e0402c0c0010005460440c07501d21105001400c00706403068400700041c00c0040c00c1700c8052454000e4a0244442601c400c180e1300c5001059030b1222465041d5180c0d006241c02409031000496250440c2004644040c085591040d9201d03296000b0494000006900c03202c00031b201c000e40c2c1c49010400110782035488e1001040c00d8019003a0440241090f00d000170010f40b82c10b064013485402c201c00001a01d511004140ca1030181800b1510b030740c2002d0009051003103e03500c0000c41801c01c802e25002c100c0d2044984120b0b900380d0f0b0006074444440f50740a040a2440c1390741058a4540000c00c0389982d0540c02003403c17841c851110b400a484071006060865014101c081c0c4200e0341c0d03482c40c1a04030415404540c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 119872922 1250 119871672 119871679
    0x30e150705030f1c0507120905010207140303060f0f18040314130509090c0f100905150403030905010503070f14040305030a020106090605010507080702060901030b06071a16021902 79
    0x41000d40e48440d4503540c092401c61072511000641c0c01601c0c04c44112a81040c0400c44050040d0304005100800c408210700041c100d20713035600300c140200042581141c80003035000c0c6688008484480d001a104e41044440d00d0059403071605003280c5281c003500640501100030804240349150a1042c02e401c40018000c505000944c01c10907511004200a006034404c032850740040b688c20a02480326514010f0948240e941c4903141c14501c580d210f07845800c80c1e2100f6603005c4050b14007000d04aa40303902c0741d0300c4503410103203d510000150b10003400500980c1c2c06910791950781d696517401192588401c4407550006400d1900714241140700c2c5841134030304c1019504181c109501da40b40c0341d0840d070050700a107002d03039921041002007400c680035503001410709007485130414480c0c1d00c407030b0001d1042ca900284075440002d0120305d96802540903604604000d480c045d1608401c0c82d010500b4000d450b4511000c02203440024030059060040c00201d02c00c40c0d000e480c0e03c01c0681846130f0702e003250b820200e91 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 119874172 1250 119872922 119872927
    0xf05030909010e040201121a152109011107020607060f061a070308011e090203130b090a060b1005040608090c03030d270507060810030206071104050a0603030e15 71
    0x141555045a0315000e490010307a900740384d00700361001604042000750180c040c4d034205032404040d2004c0d420480e464500c241c86417a0f0750170410f291228541b04461003103d4141d40c68000d040340d5131110090a200b809000000c0086042c030b480490200d004171100294041030401201e0005065600001d44201441d00c01040290b20740d82200c1c10750b41d4074410346d19a010042041170a16138008080ca00410700321138554040308444140c50040c4035030b40510a603907600000400e001e6134500300300081541d004150b01300c2d607040c1041695201c00e1001c0b0107440079800d000f40f010007460300d1038021811800a40f90640f40c6072414070300361442c4e24010054041400794405200d802c1c1ca0500090240700a54900042e0249918003a68803aa440340d0085544440d59050300001480000f403640c01e0301c4242c20003d10503903d02c16201d80c200e10a400003900400045003820800c2100b0a0310412410100c6d03090000740c0c0c0d020309843c2203030b64074072000d80050101d698010150400009000e801e400342e000c0c162 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 119875422 1250 119874172 119874187
    0xb1507150b030a030e03010f06060207150212030a090b160c061e090309050406080309300a05010f1404050a03080718120b010e0103030909050601091707061206030305070f0503 77
    0x82c1401d112030720a0740401c16155800d00e8510b0284122211104230802c1006154180240213560722414003440503e03410400101100c58001c004c1c512000d40c00c585034a03564a006110b80f005031200f042c080310781313800c2070780491002d100b44a40d00b11080e00343e07615103001c541c0a4440034040c02c004481415040e41802402d030303004802e40161040c290207034507541525440c200c280011110603030700c1891a074206200c810099130303032681c40080040c0c0040c509100d502e2070604203d6a00100314a040040c80307a404120308002d01900281404600107404000f070201004101c0302c040d004440081690b00401c900f28000f80c0902d0701076170004483c1c50001d90008025810301900780e0580c201c400141d213001d81c954100560364040c1c5000d4400b0b044041460b514542e4058036124a40c014401595141c000007400c1d0b034401c4210200420b52071030780b0001007410b10107198079461140201c3c0f000914038009100004c910b806560200d03075050b51443d103013030b07180c0e1a4440400069542262180400c20030403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 119876672 1250 119875422 119875429
    0x120f07051c060503060f150616060203060a1e15030b130f060914040204050901020f070f080f0f09090114030c130b09090708100501120f1406090a03030b1507150b 71
    0x2502c80c44908016001600f00000c084144600c49581c1c7c0e40f041604001002e4010080d1003d442003503445100580c4030b0b101c050000e088541c1c2178022154013090407000030008160003103e0005c540002c030b90760964080c840411002c0c3c415814982e600310009681d040c9604401e0760121103050606080056444c0d1590b8405003500c1210004a8814a908c414030013986050710450307410610304d01c000c5281900c000d900e0302142c0030301080504800070001d400c1043c401d188040f15031003000c1441c4281d807091104400e07a01a044001005d00580514001241564502c5101e1006e201c0040090003000075038020404042c2c1c103001000c0c100c644a00980034103440f058200d0340588a680c02600e28035007407014444c42c24480c0401400e2541c00d02c0c00400401283d80301d249074464115210710901812424100c00e40d032004048050107210700420000801000b0880c48025442540c043c003013607082d0b800f0880e201091200880202c1c00401c0110009480140f465144110303514011407181d4080000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 119877922 1250 119876672 119876683
    0x906070804020d211101060b0a0c08030411191403070e010902090415080c090c070c06030c050c06070306080c0301110406110a0b010305071a07030e091515120f07051c060503 76
    0x40b40445e0001008024405081c0141005417a12469190178000720a10041a10440e0000078084a10000108040c80107410104150507005450902e05d806004078a80c02d03c1b84511030400c8103c04800d0301c3c0e0081c80c0c00b00d29081118030030b12840590340d003061503003c0298000201141d1050340d4840e10b6081c0381041c00c1074001080140040c28003400c260092014241000f414018010802c00803031000a510702102001d0740d000d89000504004072a400740e40d18420351181884030304c103900401c900c065041e008403054680b60400d0f10340c040a404181800d841d038604040c018010f06010070710905202e0441c084101d0300302c6084031400c501940302c040b00e044082e0001d917145d40000c9414880640040e140046822030305800034613050b85510001d0009a0b071900a9100e004001c01003a10030810003022124800001c200b60b0082410f00348a4419030b0003a00c0c40064203100f100043c0c3d02c0605043c4152042081d40c489a01d44480d80001282030030b109002000c0e0942e60351800714054804008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 119879172 1250 119877922 119877983
    0x21911011424010521040c1e14060c071707050a0602010c020d2606010e0a0902032e0605070c09050a020a020c0307050a1208091005120906070804020d 66
    0x501c0a07103245040c40180c071441c590300e00b1414031104002400c100b0500e20340f001da480780c1c208001c41c91501c81340f800c010070b160f07541c2c004040d0381155641c041e010a280d0410030308032909100d412000304e4802003440028012040700000d1500600010000c01070301c1c1c485105144a80c85c00e0b20411170b00c401c0011500311a0360400e100603903441008010242c1c040002d0080300c081401c00c82401c4030f40060f90381800300f00ca8407a440c0e1004e4400814502d90040044000b1807000400c0501b40c00c2d140c8241c0382c02900b00700c1d030710090102d81d1404907040c5107040c01c0c00e09001007040c0055840c40e0401801751520ba10402c0110380c40780c80c1820000e070f40c038464440c45000317106074480544d48034180c22000b880c00c074840e0b81091081e0000c4030100410359511801c2c100b2550964030808011405041101d000c2c000c03803e1080e00110f25511482003180d000d00100181c0c5043e5400381290b8488503c0319a5514049440b00041010103000c01c015203481113540704210320030f424182ca0480d510f0700300ca0354290b0750003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 119880422 1250 119879172 119879191
    0x4181205030a051012080d0f020a0c0201030f02030f060603070e03010612111002100c02070302030d270303020c010507020f031f1d0705060f070501180c08010219110114 74
    0x82c0700c140801c1d805415006003624500040c07460a180007a040d51030030b000c00510100000070011f64400c0280c012580e0540d514504540314031810001400303182d01110202d00180c50308900c0d49404100d40f0a50340189030f0042c030740403a5601d200610001d6403020b800c020500201d40c0013024036070780902503540034001e5103000326400031280ca072140a198000314064800d48107280904121580041c05d105450517040010540000c0340ca001d0342480e045800c042d405004007201c0c100765a4011558100c0d1411240750380303090250021207000c2d0740f11079000c02001600418024002c940c8501d0283c200580010801601c0042140000e803400c0ae10010340c8043c0e0001d03c1d1301000070181d03841294043e40c030121220001413050513020762035000074020305209502c0800d400e04004a502d0a0b2184654004020004001084d0038108001c812030411184400b10b0500032510180c1802501c0d1050100000c7d2a650044850b055460324086000c4031410344d41c801c00350307102070105128070380111a00c9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 119881672 1250 119880422 119880427
    0x506030316060902040605030307120f0e0301090818030d050a0c0201050c010c0801140a050f1903170d15290c010c05071209271404060e010f0501050a030204181205 72
    0x138810300c41696402c0c0d200352300c40d400c284666804103100403541e1960703001c035150410003807007105010765402c0b41c44007840782c241d86000c028808204084008120221804280b81114403104080683d280401c04500d00014000e21000038014009c8074032800061050400a0601d403448200d9821030344008000740c00111000c004010741000380d401030201080940710740c140300d81484040740080110240366400b400000c00141c000608035a019805181e00000c0749141e0401c14080c03402ca07070000d0031080e03045450241c029140c04800912001160041c0400c2420710302c6c2d410f0b450200c0001c1c88032903000002c040000265030042840340d00d44204050b100d040d00c4406504200c83c1c403012296603813003400040700c410f100725800d41c180d03559501005418816103907176481000020b0010030312041d80d4401c945007400100318a5420100155110307500801c0b540c0107004024061780c0c400c0c441c1c6504101c0603c001e10250400f07800424581446451015a0400b15991030b0342d840000203d030400034001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 119882922 1250 119881672 119881691
    0x6032e180c09060b070f050109020315160c0b0c0a020f01020a05130801020f0301150e0a0303090501032f090f060706020903120f12070e0306100603060608130303050603031606 77
    0x164012074007500c04800208040c0c1d0900180031a035100f10301c0c020780101c008488000401609410440c5d01c10f5002d4140d80305001c0d4010a040310030001c1d42c0c1c4610700c0668101001d0500e12408031b40340440c0c0c0042e1a4070b0703151200c1d00728654561001d0703c10300031030081140c80c1c418904240014608110701e40e0b29113554072007040c04046850304c00d4126001c1e50b4010440000032000b1041540d05484411003d064030301005102514020b0703a0b2144190040055503002003030582001c1c014040314400e0b04c1c1444400c0f05100805c0645001082030305800d081e0340660840c0c448000043c044144003d084140000da02c1000030b82e2603004100101d84060300042d00c424181401d0103078000241c0700c80c40e042d080841c0100a0718050251448c100d07656998440002c40041c4208030340e0b20f4041c006403d45599040c00c664030320203041d55000b4940840c3c1010ba000600314816461103116a0880505600c581aa503500310080d21000d00003aa051000303215102e42e50048070340c080c400c07034451000003e000c80d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 119884172 1250 119882922 119882933
    0x30301050310020708070305130e0405060f07080709031b0305010212041b0e0103020409170c1b0d0201050d09060b09180d050909060d03021f020301031a06032e18 71
    0x103031090b40348100340144644c3c4000344803181034134542585402d2180d120181c0308809041c00c88a60b0201c200500c8040502c4188040450085d01a200503110760541d0795130940b09481c070203002c0d10b440000400c0c0c1201040440d0340603004458401da400d45c04c81c40345550b510341909a03000039141414001e9a4420701081210303000d01e08180d8092034244d5880d16140901d806980081440041c1c044e6840c0c80100007040ba03202c080b0900380c2c100c401e10703a031117001d50101d00e179483c840c0c0e000100804080010b000b07090b2405031011240c0340d5050b55654a0199146d070398802500102e44200c0c0d41c0da850b030701c811041e43d40d40c600240c13158100b14003481405001a03841440c025200c0d40321028400c040140f0556516014861540880d05407140c0c920200c140c5012458088000e81c095030201d1401c0c18440400c41c10b400070360403203014640c4110340349060340c0080f61110056548a615a01c8100d0048283c20810112201c801481c01c002c462069001313080019240341c81c41d004e40161040768803104000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 119885422 1250 119884172 119884183
    0xa03050114090d0915050906070f020109090b060901031a030a12090b040b0a0309150f09170f12090703020d080705010e0a02331206030d0201050402030312060f0406080303010503 78
    0x800c42e0b002000c11903440c0c0e0340a051507400d8080d80d44581010284074004c14000c00843e012200701512503036440000d410140195001c1e40d0049002230501140060b060480d80140000184014082e51400380705800541c001c10300f040d04800084003050000f455690248141c88a25015a140b1300c408400c0510082ca8114207030040d00308540c3c01d000c00c1c4001034014083e9042101c0c0c0d400c00088061030340c14a9854100c885540e00329941c20003140130044140340d0090b000c0d080c0b0424401c0c91104040d801000e44e03005041c0701182c440740034841101e5143e02594829044103c0505980e075182d00e82d00410080c840c00b40c002c4d034030900000703500810880c0920500c00207140301e0000e451080340c0b640c0050004c144042c01240001e144c140c6080d8440751510410209605010065603141501021b21804900454210340300303009080801c00c900b4010b0040754070455000340a9441c00482038210458108007074145504150440005220368450703200d414064449200210703200d624040c01c062511 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 119886672 1250 119885422 119885431
    0x2120708040308010506161b0f0f0e0f061201090501050708130c06050c010b12010b030607020d080408210a090203120a020714030c061b060709081005060303090a03050114 75
    0x1100c40d040002280d80b01d164181914006c9880030b554594106414200e912078010107015540201ba5010598501001c804101c030110b0741c4814540e9a91000150b10003540e00c03901040b501203074009030f0300241d000314441e400500145007a9280c0a005c0c1b61034210307802800200e50b680c1d541c0080c81001508580e00c075500140040c2003066a82e455581d854000e9501e101c0c1400717015001c01d040304002d000390002c100342c540c00b50540303c010306d4000e40c0e20301800001c0d000078049c4c010308022588051000c50f81130000125038880c2c008540300d554400c40c041d0f1101400007070450149428040e0083e00c0512603001c0c0c0c8c10641c000c0380400c0107004040c24104031300325820000c3c404120b00d40610b13801045413801c964a94603805030000b4410003007410040325a0043c3d90260001500c00142c0c500c01e003183e104100c0d06c030103c40306ca940c0c004054401940074000c090180d07002410350144a20030341c002c10b80c0510007034252828090118040f96084129400c200c4659440b134429545100350045600da02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 119887922 1250 119886672 119886677
    0x80301050a0906060c030305060102011d060a2406050f070204021b0706020601230a050307060c061103060a0513140a02071502030c03071b0b010e0106110703150209010309020303070501021207 84
    0x10702d1606201805d900040e82c40101415124000078066038006c0d4031042c00010810f03203940000d20140c3c2101c0d01c441342124076400c000e14000081c034190b0080142e9600c044010103980480c242040170555264202000d502d031881420040a4010389441c00603001c44250440924002e90b13400011506154450308110211750103407004012541040200726010201c200007985d29200302001318034651502d4101a4040c0300e6090002072306944141341c1c54800b401141c04100715560400b4440310344c801030715440d07030082c0b50100a00141c03812040f4801d0641c401c1d00002150710104e81c101c906201708446d1018101e5000c20385000b400320010b00d40b88100c40d0038504501c0c42c5840415000a8040a4020010400030941240c1c1380c009421080c0d0306640c000301c2194242d0303074840142045103401d000c0c80002071134210111810000000e03030314007075a41c03111800d0040401444e03120300a4101c02030450406880f8000c00300907803000d000400c5050b008100169403404801d1f500c2022200140941c0e04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 119889172 1250 119887922 119887931
    0x20c0906010906031104080307030c0b010806070206010303080711101a04060b031b04031a0121050a1205040914090c0108130b0402040b060309010b0a080f0705090c04030b04080301050a09 82
    0x2403070703a40002c0e030605440ba5800d0008044211401e84007040c040d03074002e42550700c00000c40070300381034101c0340c810701591182e0810a400e03030f00c8000540d00c4440640344040542c1c4800010300029005000080d0b1200c16443c0c01d0401c0030b083c8441a00d45041d03603d024001c0c070350381c111350740303040c0404148850f01c4002603c00b0301045242c002d070340c002480010140c00c10364000301181c24000310310908a4000359000440701c1441c02c90f60400d0070505000380326801070b114005462007c4040000319038989690800c02501003003000d900c17005000c919001c100001c0180c20800130426411611420281c1406488049144e181000280f0300c1e1040c20000d46060040c1ca10030494040300070740701210301d240d000724044415195440468050080710428651005002c4104640500154000c00048030101c0704580000d554692107030f00c07112903403448012500718200602c8039040810050b600045680000b61a0503604e0b11842c1d4071401c01d90b0308442c1c1001c0040100a98500500b000025061000d010003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 119890422 1250 119889172 119889181
    0x1110726070b1201090f0605012001061e0306060501210f020904020c0102090a0905100608130204020c0d020f010209091504090209011203080a05040201090302060c070312050901020c09 81
    0x240d54a01031003082440e00590300900242090520011000b0103a120107039894298003652002d15107000d02400142600c1d00744003042e0042c25018031000c03144181c48a040e114816494001c034004011a00000c0c0d640b02c0200041211600d5a44619248030254240d8110305600c1c08106a0300140c0c0128100660344540740c0034038440e03405040800010110018980d010488100d01034003410007103691040c40462115401041034004054095045a100380855107900f5950101e0340c05407440c880d401c00014060200364080e0198540001030f0490448070071405a00243c1642c0c0183e01404007900210b01504007035804010100c815607140740207500304203500c40443d02004e0024814540b061004100d072080ea01c46034071805426801610060041da115085140d02d5070344144100e00080ba43c00008034100400d00c510350059a059441c3c3c1e40a5207941c0070400990000315041c007240c0140c0c3c1000002650003100d00143c2d6400d83c0300d054a40e0028030003e41002060b80344a8011070403542040b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 119891672 1250 119890422 119890439
    0x3290604150510140703090305060f040b0a020d0608060703090c1706191d070510050313030c02120703380f0c0c100501051504030b0f07110105040b0105011107 70
    0x80182d45060700c0281a40c56110421200d625403041a580c20140005514080c168041c04201c00c0c0c90156003268010345403802030707000c0424110b601510564003200802c000c40565001451880d642e00c7e000f24180352a40d00c502d0a19800b980c07000003207a0391b01c003911f04003d26615450020701c0d0301081605d007004810802600c5820041c1480e008031000402c0442c40c880340d030b200d52040c0ca03043c003000d00304010740340025076514542e0199078804c50164038a04600d0b403041040340d00c109043c194035a03881d007680c2e60550b404031034008200d9004041c1c88400520100400200c40110300941e18684400d90541ea00310b00a10603448141040b18240040b00c802c050b6003034900c2d0004a60201e41c0219581c40074411980d00656014003100d00850981c01006001ea1f000f15044c0c0f0812180a40d1440c402441c1c01750380e20603440000c003d026440001040401000e9102c1d81c00307102c5040544420b04481c41e1682146d82c101d500f240c0030000b0350014052541d101c032040b00040c0282005045660800342c03071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 119892922 1250 119891672 119891711
    0x16030210021c1b050a030804030e0307030206270904050102040e06330c10020309010609061a0a0306050d03020f01140714070c080d0518040204051005090a03290604 72
    0x1840b00f845080075030042921980c000303e843e0541c2140540e0790349a40c0e07140051608105890039000079120b402c1340b54075450085048811260700400c118545900b2840a03203100410442050030b038164246265035646030195558402c038420f80005940310700317040210500441c0505694000d031190344194842c600b5a144a40c401360a400794008402c085e4840c2e41c02c07500c508600104a8054030324041c150000315006180074042e804000d100c2036489120312022642103110b00c0c0b064500300448034034102d00e200b00400810016145c0480c40f29110030204a05140a002c2180180c1c4600c046542c0c3c3d00003807080107401000041c90080a040c2b6420084c654841484540030600000a84100b00240384002000601300e0005030f860fa0410098043c0c826040920303210030300a07101d0303103c42241c5440e00c06c445c207462000305204008002c800c41129a90000303140c0c1a0085124880070000c2607000b03002d002440c03510440350103401c0c40d02001e244200c0015142d103001c2c60400b07400e0705600384007118 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 119894172 1250 119892922 119892973
    0x703050f160b310302030c09060325030501091a0a0b0303090609040f0609050f0a020a0203040905070e03100b0a09090c120203070906030305070b071e050f0c1603021002 74
    0x5215111041e4040d0282c8071520400b020305071400e08011041219010034a28013141d001310292002034042c2014400380e03107401c07180d9603815001030355100c01c3d00148100d10500003060082c0c040682e61603660306802c680c01c1d1102030395600c4144140c90007220030f404480c0e9010110045c18005032120f00c02080d528042c42102d00d22030311020505a0690700c4507405003041301c044030b5003804204c0d65052103034003d000903100c02c15801040c0f00001c03101c0c0414001c030b54004c02c00f940210300d46450200300100400002c0c02d900308200a0681e89110b036901000507003540c820070f42d000500100c8110400104c00280c2c1c2c00941030714140071414000c42e540c130036810100c130340c041004041d000b164800030b030800381182c201c041800e10702403010090660000252004904c1032010b0702242d1120300c010b403242c0054200c807d00840d07001810b012410f2143c40031300003d64010000c81d00b04407045c0704060416042d01121050f0681d400001c0042d440c01c051902d016041c14005404d4800740381541031441b003440103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 119895422 1250 119894172 119894189
    0x160f03020c190606260a1b080a0c0609150516021206040804050319020f0f040615020f010c0309031d0f060703030504050106060e280f080703050f16 65
    0x41d0010211405001030b03411802c010000c0240340001c0d291002c0144818024800010107803000d1710313a901521001610108041c40003014036201d16643c0710313000782c40221800e80302c06c060400019818820009003000f2445800300c1944982070100c010402e8101c0d600c104000000c0010721201d50750014115a418102001702c030304040240d002007148015180107000d07540c4a00302c204401d00034288090b206480c41201694509009074561044850902d440030394000200810009a8503240a0112200402070004106a40d94030f0103803044008000780c20025030004120662002d4ac20310070260030b02030a0504100446240d10007c004082d080f02c0c40591400e40c40114081c3c0d0380d0501d0340d18608500501d0359942d02014a4010060042902c04079003a60a2807004200079001365008814000003030000c0c050151078103d281042c0340718854203000420030ba440411001c000441c8503001c1c02d5882d0003002c100e40b0f1454150300d40899081c01c0010b9410620030704852081010b1a50101c60000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 119896672 1250 119895422 119895427
    0xf0906050406080c04051804050c0d02100807030f0c0c02032109060a030b0a060c020108060901030b060d08160c050307080601060509120f0709051807080c0126040c0e160f0302 77
    0x36404d84241c0c8104d40000d9480300e81200024607542c103105107544154452029220102c0560301401038140c00e5140080d03100403100c000e440002c3c4501c0055a01c49594a0082400b600e41130103401203032144940e00c000540000005020360508000080126a54a4032089503030040120030b151070264034800340c0301d400002290302c100c622a030007807540e00c400100861182070b0754a03406892021f08030012808240c404001810310b20380503413001d04903504641c40e01c6066448034100f00c071201203003208888000c002e1100401d40010300c5100412584a04401860a42401c040618242103a840003900303174000001444803681c0b0900395007090030f05441840c41c0340032580c5101e09060300d1103291a014881c2c007100041039620340d003145001d90351104002c101400f51b290040d440c0c0c02640240c800c981c0c80b620310224103500c604160300040040c0b440c03084034864002203080716190190340550341055050000e22041c2121180c190b000b8060701a1408801c1242c0000760008070310100b41d80034107901 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 119897922 1250 119896672 119896681
    0x21314130c09091104061b030e060f0d050f1503071401050f0d05090c01030605030c0616020312040e040309060c050d080405010b0d0c08060708010509130f0803040f02010f090605040608 81
    0x50000714014004241c004c0c8040c4030503010303000c0203400030301c2500b000480c076000810780000054a0040465015a42c640c0d00c038080c0780910047e03510006500e42201c0c4100204071282050307114450041e0040b00010040d800c08554080b180100c10840c18400e0300800d6080000401c0713500011161b071400e080c1191185c64103611003003140148881110124140b030200400d4110105010780e001509881c1000b60b50740700e1044c15600d2981c1c1c0800da8010f4810000c144201c0e1110121180c2544010106c6540000aa0325507082e074010740d00071040088000306010801d80c107e0301c0e00c0003800075842c020ba046141c646500355a4091001940c092000420124090000a402c04544007030081c00060307015800303140c81130301c4046903c1035560a0007a0408290140d200c0c00203981240d030001d10304e10254482405c0241c095404146c111410380460b81c0c0700000a803050f0207588034501516030046907181600014001e00300c50b0f030303814080019482085c01110b0300641640c1c00c3d5001ca07d41540b00c0d80c1d9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 119899172 1250 119897922 119897927
    0x40f0608060403080405150a0c230d110d021c1a0d0206030601031d03040f080106060e011103040801090c050f010f0f03090c030b01030803091b061c140a021314130c 72
    0x44280c147c425103100502000b2980c022900400154555541d80960040f03a1251144c08500141c0707000a100104201400c090200303a000300805e032450b00b00c0e0074a0481c05148400c00c0740d120741072031b4100284c8040c051103044c61510541038074485d10a540313600c001100b00041e81490305107030001c0c465100440490903c2e40300e0350200380120300184000d038800092100ca03a1344d0ba041840303482840b460006000c42c13038401c107004600403244d15840700002d407140900151014040066610424401400300083c01d00c000d00030041c0d51401140600300c0c0b00c2c00c010078464410180c0318032a05100c014040500010f030700c11a0000c4513180340c50300103181c0d580c9180000a41000e903001904d41c1d00e2940c000300a000da000010350141c66628201d4006114201551402510740044940d04c038609004c6101d921010050141004d0f511210001300c98000e10400c2010081c00c0d41d20701c0810342c2c041100d501c4e60300b0f42c1a01c030303006d480a40c0e00709408411603000101c00420501c2858020340d180d60b000300e130050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 119900422 1250 119899172 119899183
    0x3280204060906080c030715081f0e01180905070308030a0905010501030813080f120a050f0703020a02090c180411070210030c080606031e1f06030506040f0608060403080405 76
    0x268020300921407250b40312010405000c440c054002a40512140d5080500d00000e1007012600001e55516000402c0e85040e41c10000060402095181c124207020601c01401100c4c009814010100403440d41440704814000c200d06074400c0c061480c1a0560010490026034042181e5004602c0c0740da9941d8800d0781d8001e8049c040d001002c542c01c2000200c1002003880280819003036075124182000e5079824441d41d41c252055041000781c1248220380091010a001020302030400d0814524050366a107119103241c3c0002403d900507000300c5001c8045282c00460b003038201450f015564140700c07010340148081c0e2700703542250b44155580d014954032800c2c004155101203800425032841444d4800d00500038199200407500020340100015a59181481c180e030301404440013203128482c0d22007000d6480ca04007506221b003904a015440e480c85864420450103000d1603036000c6200c1c00c1070400d0106803500781c2824203400d800d1440901040c2c00c00500c1c994415018940420a80c80710b080150034070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 119901672 1250 119900422 119900503
    0x30c0318120c100f0603031407020604030b010b03040302120a0e06130801021615140f04050c030f1506040c020307030f21050121030504150905030a1a100503 69
    0x803076002c100360703070754074004a00c4912207540b281c804d008019044180004a4020713000040228003029210b0b50040301e040b0141c41d007a803001d44403614060b1241c40c0c507032902009a2011002c008000100802c26a042c070000d00c1041c84502a141030140514000d003018501e502d01600485012a100c400c1c0c02c04c52a004000f01181c0000311342d1018100100c9807007001030401500d04000c0e1030000740105c40b440c440c0c80301518065040031400d0325003d040c0020000e0140069409204900c000c6800b075905010360800320030070a008010040e0005000104460010521445580784c52240e105450b0080103d400b070070b41c1481c280d921544e4042c03080d64444a800000341c000008003010018420581d44603c1c140c42030204090b038060300140d1424030f00c15026400a00044040c001001030300700c1c3c1d201f0205455007a00f0003049042c3c941c400304e481c0c043e0a01d0165011340d80080200c0108142001c0142c001c108141010106818030340400e030340d84200d0042500034400c481d1200100d0b962403501e200351 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 119902922 1250 119901672 119901703
    0xf0c03050d060b04170d0203040b03041104060602100b0909060406020c1f021c20130801050405030301030209010e100b090105040503030a0c020f060c07050f04141602070902030c0318 80
    0x782525081c1611143c4c003d130080000314054520032890050380000c640032282d40c2a401185420b061410421158001402c11512203c1041407068182c0c0c680c0a90006886640c1c01019002a050080e209640d0590700e00c070700900c2c1340004d00c00c802c0740214500e58440d801000260703884d81280034441c5028408900c034001500c4800580c80c00e85d25980082c0303411100755003044c89081c406020b1004a500c0880310221514a40610542058610000e0300c989021100310010172580c0368801e0342510411241180c1c9604008014411450000d900d035001d400c00502d66040740c90b002d118101090030900a03445001c8010900302034070382c4500f0890300501406802c0c1e0341c40d010300fa40085e003000780c2204100d01c80c102c10b03545a0a0307030824000fa07035007241c0f0307079002810118500704c1800750341c05011380c0c80c94105454a4030034070f0041005688602031840f084090001c2c047ca504020b0900c0c203590800305003d40100240f000030303010b0f0b4040e42d80064600c402c041e245210400c2c050f00d0a010500040071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 119904172 1250 119902922 119902931
    0x105040521070e0112030c060608071715060d06020d110c0604060b0301020903150604020409060e01060f1b02210609010c03061403150406090203011d15010302010f0c03050d 76
    0x282507201c01c0703149a008040104442c021900c690500e071501e9424094401880f41102842001c00d101d85008102c090088070005052038940e604503041070201d82002d0260400340c0525038916008020040e54a001e0054840245c10700d04002006110010001340443d50041440b4001031030960000420303051940002d642d50788010740b2591905011103080d10480d1500412452509042c0200c07040e0f9200100a820200e9520342c480380003500c0074290a0300154207010106610a0030321400300900b9001c0b0b0603000a41c50190000d04002c01d0085190421240b0740004500c00b11030b10210400d04d0341100c44441145070b10510001102d09030b11081814030540c070501c2403813281980f01400d52505990144078140e240d840c0040c11240d0115100c1e01079108040c40c20000c90b070010701c950030500c5a600031444e980d1a40001b400e40b005803010001d400c22040111040700b10800c1043c0e00d03c00580220a00c940c90b580000c0c018283e44101c03203050185095604081622403030071140300c1108901d0400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 119905422 1250 119904172 119904199
    0x50f18011e180c08091b010c140303040501020903060a0213030f02060d050709080d140406030e030f0a02060709091b1d03060a0504030e01050f03011202010e040f0c08130302031801050405 82
    0xc0902152082d16000c20303113140120300801c9001c1790401c0005031071421a40503006110044408003076805056a4880e200042d04c40301c503e0070303c0294080ca000b44000350310740b0600c1d410503040010152048242c01d10400144e000c20710310103d2507044a800400800c001112800890401e00c5090f680042c024074040c200540305401c4100d80342030310440011035000c1c107003101c01a12440000d600740a1145002d000801002c0d1003500000310101d000c20541c5d05101031420f003640140c000440450240c5c008500304045280e111800e10300400704413605004905c1e9102e0b03104400d0710085900e40801034480c0d140d244441103282c00400f40c0300301a044807260310740510120000d00c01681e08400040ca005242d104642c401c4080e10030000b16071208030b25691810341e403800c403130240c2c000807410301c180441c48042d150750317600c62115501441c50000c204909031500061045600800c0c00e840078100480400229a001003500c0b16500c00c15142060501c00d040140c0e541e0089610180c0d11840c41904507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 119906672 1250 119905422 119905469
    0xd020903010f0e0f07060804080a140a030608150c12070918090218040210030902190e06040b0312180a0f08030421030c0206030415020310050f18011e 66
    0x10f0000a41a909882d030182c0200d544980f112564800d0100007110540490045030b0081c0044c402c44400b82440c07541c2189151251710150003008220300441ea40301420801c010003030000403a0628895814a030307a1034a00d004003420300484000c0704205042c4400034800c5c5015441e0070000c1d00d41010101080c1c410b01039580090441000300b01d001e02c1480c401c4040300a030104800f40600e038000c1c601c2c664115420380c00c4009111810040c0e90080c0302c0d0600900c02c6100d80c0c11f01019007902150340d800c6140190502050781c1d942c04500d4002e50103d40200e201003441410b4503401c07503003101a25001d105030b00000711031800075044010f04001c0b03e4000545510004020000c80703d40b1580c0d28080c0d8461450721042c044083c0c0d0241c040b81994a0030001440e00200840d0b00c240b06441080c69683d54050f103604981086600d00705a00d07014000303120f689007006012444030303000c68407003190203801450707032441c0c0034184640f808a2908165403c0410084001c0c103020300440080131540000d89801e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 119907922 1250 119906672 119906681
    0x50604080106081002040b040347090f03030a0e010902120d09060801081002090d0b0a061419060503040c08010903050d061707030209071b0b010306060b0c0a06020d020903010f 77
    0x3c0640c60b00c100300900d611181c1038000c1e0380844250001060a003891502c851540911480c5100c001e025503124041401e0951140c2a15000051207245204101702c03030200d6100c540501f20000503886501c02c048044000801c4983c000d54100300400c41450301580035000d0140038200039405241c40d0000d122483c800100074100301c8880d07845007038060340d4540c251a400300038000c6a055800086902980d100550002c00941401400c00d2585c0180c540340d1580003a400d40341350b0400340d00c4820030031001110241d0482084001c440da11003203803200003a03910a080c10b1144405100d00400081c05108042c4001c00040101d50b000744441d00070b07031600504a0780006158000c803850900c001c00c1d0010000c4510004014850050000c54155001c11503040801020300f4104200c68018000c9050326030b880141d014800e0031030600d50b5042d45009001c0d2030103600403103440c800600044400100000b80b40f001c0580011006903107194000f81c2c40040c1c8a87c9070f0154140d800d10300000c4000c00070b07922 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 119909172 1250 119907922 119907929
    0x70f0b030411101d0a030b09010e060a0209030c0d141b010807050a08130c08030a0201051b030907060c0c21020406050a060f030e10060b030429130309050604080106 72
    0xc4a25031030041c8003c02c8007040f00c0074103000c0000c2d10160341400e20510a02420355501c402032181c801d03e960f96075160b400e00803c4800035141e944521203c66003241c20000d45411190030081507091544c42000310359545024140c5504c03420444401c02d09010b44103943e41d00c048110003c4d1549502c0040d6031034058012160980e0003e442d110020310114031030070643c0e811181c10b80d100041a1601c240310322206008070070550b01c8000c00b640c00100440304000030134000120342c001080307030702c1c10a441b49078001500e001c0e0041c2150030001c0040303000005c10b04109a9280d41001c00c621003090402080c4a0360036041203000c064204004a01e0250005445440398800c60701403110760307107901c00d01041e8073b071510500c00894405100902e07114007940002030907004c000100c8104a04286a98003a1481580901e250440c00801e000078840090504807030060300580d4503100441e51409640a080e00034003c05403030114011080416114500304401004001e05582e00c40c0c0d190030659009100b01e10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 119910422 1250 119909172 119909183
    0x209220e032808040f03050a022506021501030209010312020f07030308090c04090b011a09180718030201020601030212030d0911030d1103030604020c033601030b130b03070f0b0304 79
    0x3010ba60815114400d803c3c811a071045a0101e07411403540c060b601034102ca0a408103600031040310403490b07480e0301c1c0c144041c225a03000c41d0310481d28140010741003120364030350b100b81c2c5000d402c01400584c41c1d994420341182c1e07011000c10710000800408a041040301740f0111010b01800d2000130034075520082c0640145d4141090321019070186080000b00c58400d500100038020360001040754280c44102617524203241d8540301e19003400c1c5c00c00120480d84440320307210500559424000c0040d48614000c0d4a0303100220001c4d151815500003075a40c0300140300091003003800d41608004540107005440501c00f081109000800040c600303029404004e6500a00a10800b21008180d0f0312451500401c0704140c8051481c5403134550a00c0043c1d48001b5801c4482c0c4010080d199002d514000300c1ca402c2a551a05034684003401c0080022800700c0f0703006241014200340040d40143d50f40c010084004800d00c0c070014004074038170003080c103045117a13100141c1d00118040000f15a41d10500540c8070f02c3c81030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 119911672 1250 119910422 119910487
    0x30b01150e0d020102060103170403080c06090c01020d05040509040305070602030f010303030c18050d05150703020403062016020307080304030f060b011119060b0d060b04050a0209220e03 82
    0x1c0082c480e142000010103030050348110010400b141021500042d010284c1c0103107850940c0701d4a40122950000101010a43c0500c0400072074076018003402501c0c0001b44080c2c035440111042c010564010b90041d00d00c10b5a09202190805000348100d9062580c461415074481c81e00114a61503154240b1040e0701081c10b044100c92010300c1002607620100b0440844410b1605100601600d41d100240807109445040c0b009030ba5a2024042548140e0180c3d0b40035135580d04624002043d6000d015401d01c0750054a100c0303001003c80300040e21a4180411405c1b20016828000603142c0340303440d8000000c5000c0050080f040c855901000c01c0210700070002031001c0c007452070045540703c2c03401401000a82041580076951041c444c6c44c00d444034000c80c40407d80c80310344070001c1c0c1120250f640071945160766584000d0103080a000d940d40c0014004001c5081003108000f00e582040d021031465030460400e0703a5002e50307070707401d901c18211803248004036620f84218525440b000030300310400b10401c0414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 119912922 1250 119911672 119911697
    0xe0a050d08060a09050c07020301050405160504020403080a0c030915020d20121b120a110c0310090f0605010603021b01020c120a271505040b070b10030b0115 69
    0x1c00c0c900e0300862024062801c2c141c504a1030744010031000d40304841c1c0c0901000341c0c0c000f59809004550055002e600640940400c1404030040707146541c1c080b60080d401800200003041510054a00e01c0d066800d0843c040d120354981104d880e1881d80140b40300510300c00d00c03444442d600044422203518140c52b1654010301010f0b00704001c50351f680e507600780d42e400400071a5991415401504900000720003003004040c4001005040100460319840060004680014069030022500300010b000a002e4006904000b01280d214013040243c0f5035007945481c0e0a00401c01c5d8101200542a00810200a81d5841e1400140650310010341e030400101c0f11503000d00c030010103100302d80c011500b050080c40400810031403041240c00c42da40c0d4100344918801252098442c0503500343e90844407d0000c0301c0c0e41e0500711008107148000d6681d03010000700f0700c800d0128030300c40381c2150b1684d5001034000740c2aa540c3c4801507400341c141d030001029942c48000000b606002d51441100701542911029a070540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 119914172 1250 119912922 119912927
    0x61914041107050307030c0812090102090108061c03051e04090917040b1c0207061802010201050a1a190807030f021e06120c1e0c0705030304030203060109110d0e0a050d 74
    0x240b458050b0598004008840c00240902e51540074603224164880c10010756030b200040401c0110707203a6003241d400040300c1143c4e60384510b4080c2c0c004000c80c0c240d0300717016031081403807052200365500606021001651100e0040c08011002c242003881c02000d65554460a580000d080c101c10221081101c030a10040401010010b440aa4030144a09070818041c0e14030118020514146100325036800c0002c580460b131207000c1d03a00c1c003808690070070f0072002e090302c002402c40340000c203543e403410303d0420392501c003908181a1045c071940c2211a6010b20340c3d400c40f1083d4120107a40000311034403840c8800001c000c0451b1807942298000ca4800304c980d56420920000003600b0700403154840707003c001d402840c3d007104112070b401c8407507140354908001582100682c4240300c030b444c2d0400d002010a0301c4c20b0384103042080394085d210a50180d814949540d010030358492040c0103083c00385860700c592840e07060740c0d202034a100314080d400600141c03050748145038960702d20410a54150003818500d0508a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 119915422 1250 119914172 119914177
    0x812030403020303070804020d06090f0309080c01140702180f07022107030f0306150e03070506040e0c0c01090c06121416110109020a0e060907020d02150619140411 72
    0x6070180c020390b10756541c1c4079080380d125000501c120b030721141f88884000481c042e440790b228440d100700d40c007d9001702181000b40c0928001d50180c807440d4000d00d90100c2d01d036804030fa0500c81604c240304150700c50340c0d41d00c0000c1c020502540307003004408c030700801c103d00890340884d52405030403190203582c240c0b501ca00004407040d000040c101410ba00421006001074884c50003000090014038000400c1500c0c0c082e00d4260b00c0409995030000390f60703013110600916090120300d0050208035002ca103014581b07128101400001400c030410503034080703960705180c00290446440154000f250501650300c80c000680384000c5d04114000300c0d0319243c2c18001c4104090035080c0104a1801360510700e42e40702e08201ca4030030a081c03001c125552504c4418005807103000100d030240070050714090072850402d0500003800703401044030045510034911808442d0b00410041041410b848050105a0f102c0000c0380740013441058544900d100c0c84030010f10801c81c0902e4240c1c80208440902c20090442007586150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 119916672 1250 119915422 119915431
    0x10504170702031e0115060e01020f0a0c0b07020607080d02030a14060117270304061803030503150a08100905010501050a081f0b030a0c06020118080901120f090309081203 75
    0x55020400340010004c1410b030700e2441c0c1040c007002250100ca4545181d00d84855640324402144006880c1040e0350303014008032841003103400003805403900a4039804109851446846500038002a600003951a40300440d00304d1900303c02695074650200810f88001c0d48100d41a002d840d00d84150010008480e40b074250007980d050356110300010004003a1145004e001c0c10403044036050f0b00d59002c05070410009142c2d03a0142c0d030060b40d01c1e14034000014189417491000c550f258030944001380002034000003904c0e0813224048808404021400c00700c0c848040c01d4020200522030200d1120100b4569080b040c0038622a0000744001c0e41d80e07000b40507040f02d041c003400e9615005410300d540348006c01c007984250740c00303111008182506180c1c046405c0410303050040d200545d015200303000141d02401040082d6204100e41c04404040d9180c580c80fa0003000c0000c0c2c10001c0845a6040100440d00804501800781604222901051902805010003841651114010340f04074464100f042010b8074485d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 119917922 1250 119916672 119916679
    0x100501090b030606040b060405030a0305030a1a0604090903050f0d0219050c12160c060c05120f040306090302100e030a09150206011214061509090d0905010c061b02010504170702 78
    0x10f40c0c039043d0401001c0c1141100ba1344e00000240400280c2d13580802c424503689009889460b070741e0904041c1c0301d0a0701c07456609251003096204203000b00c3d40320702c0e0071201260508400081c0c15520f524048405102e02c5070270310741181c00440d5002180c0f005a0080082009401c40e4401c0b2444650b02a00e05004403a01010242c02c10000c006007240d020008211101203120b03070981a8080e176607240d4034560103412000004202c0140c070030810501f000080e55401e00c07640e4050030700001e1070b03001c4081e20541c00b00425460312000c000d4105402000187c002101c0550107001941514481580d41d4000c0c050b03c10004002c07100004241c54198005480008554041c1050360300b072183d0800800c01c1c026084401d000e1391000d104070621300f4401c5a00401c0d201644a8002c007041c0304025a403100074041e00d445070030400c0000d940c60380182407202214000e00f441d807002041ca0501400400e55142d030040c450f17040e1041070800950650040f8440c1d882035501c485d400d107003140705e100d05003e4108025003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 119919172 1250 119917922 119917933
    0xe061003110405060c0a0614070914090403030e2a01031113030206090a090c0203130503030909070338030d0c0816170c010c090803270103110408100501090b03 70
    0x41428090b00a0091510174002c644002081d41d1350f00d402c943e000d4807140c288025aa00344400c443d40566410000c008400d1214860840080024404403000d8002404e01d40d9550014460501c04d01a0f10709049c8800c03080900d40480000c4070791000c600788400da000901d0803640c0c254603104c441c1511024040c452610b26154150b03801e2005551060110903031086551100243d01107a90048030800e070041d034095a1980340c110000e142030ba103250040740c0700c0d070400d001108964031000401a0301c01503d140100302004031624800d042c8038001d023224440c07611381e458100c04a4038001620345c80d050580442d4108542e491044030b03001a01e2000030101d1000300b010900ca100c601210700441070064212200401400b03980c0403959001d01912a01651117007030780c0800c2034001a030300b001000604099884c10100545010000b094440c40306070114040d1100c401e02e034445d50001d4101201680921f40c2c1e01d0722110010794501001c001d5810150816001042001280c01100e410400c06002800d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 119920422 1250 119919172 119919179
    0x3061e07052d1207030e070501030606020a030f03151d06010801030f111318060b10020307060e1005010e010806090c0109360c02010e0a030215041502040e0610031104 73
    0x80b41c49140000c09000054140071102d81000fa01c455240100555100051000400841d8038148406c81d40000c3c1072524160040103000e80110350091450340c51318044101c00b00d51a0140d00030000d040f10310300302c2c1440010214213141100a82000c0f6003410040c1c4001ba6210001168209024007004212222460007100010413910000e59000320080800b015880341e00c4032201200d03040d03465200c103000041d101000340061845200f07100c1ca400e0711082c070106206103000c0d680748500744008182555031001510015018007405030701e01c0c08282c083c80a542e44241c20590220300780684001c9000c0e400204120010004040f00c1100043e1900940f031303883c110210400c8040c0966118401076030701d01802e100861030384002c5103522003c0e00050744510011000307003101c26101c0461407940c400e0b810040402e4000500407088610741c1600400c0d9a41d44c40c0c000200c42c00703044400c07000b07800800c0129801400703030074142c400c00080c0c880001919180c070301242030307440c007840c02461401c04010070b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 119921672 1250 119920422 119920477
    0x30e0c03030a0f02010e0613031d0105091e130203090607020d090303050d0b030a050708190b04080318030c0123040b07030c020a0c0306060f240f0e03061e0705 70
    0x6159014030f130f0000080c3d0301203401c09907081c00d0080b00c3c04403800601d241803504154025842c1c0c000c03c2d984403183d200d0210303401c001900c04e20581328100d22950306003d10b42c0ca40500c5554010071204040c0001c0d90269100c4200406134100341c503440c078180119400074040314400662025104402d42d282e543c154559182030301c25600400b0030640c49515891560f00c1d945003003142d910082e20a20040c45000d240484060400001001b01c8640c041a462100c0104101041d0aa00190400300c01d0b5a241c84a40004221510f44681041e43d0701011035044503000c4190b2207460b46a5a142c4010a00c1004036011803021404039001031034861410045a4900d100707a016008801c11401103c011460980741c15460355802d500841d04251a445c09010042034041444002c0c410390b440c0446d001c500c1c8200380c2d00004010030301000c000c50344412442aa1203030740c5c104c10700c01001d01510b89506040503001510300000030705043d6042514041b45000c5c3c440c408490f0a06940c0d40030413003852204844 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 119922922 1250 119921672 119921687
    0xa05070803040c030f0f061a13020a030603021207050102010b06090108070c110303121506090102070b180405090f010b0a050f1519020618030313060b04060f1203030e0c03030a 77
    0xf610301410f6820044000b800c480300c40c2030000c0c0141c0e6010300804441c90900c080e10180c4000706c100314225514080182c40c0d0020907080302e280c220005d42c071590b0380003046000f00038a500280d44540e9640308100e442c040450014191203080c3d0007840351805000600580740705401881d40024034280000d414603124545890b074861081a2086404c494000000d241d500802408040405d910f828400e80718950f1204411005041d81d6590400000c2c8002035242c171150b10407201701d41d000055018500301d030070070000709c1600e0041040000d410004820b50b82c030005414119500c0d842c020929074185001a400c40c11208001c0c441811550b5034814081000c480f07400c45058a6000c1c000c0518202e14051550001440b03036000704007628003240c40c2c4000181c07103580c0d05102e4000300181712000601041c803001042d000f00300821300071503500101c0c00130445030b4840c020100c00c800c004a00c0341001c41c5111489802540c0178088030305074008440e1610403040303140d68140c0c01040f4040f901d0b4020310380c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 119924172 1250 119922922 119922931
    0x80d020307020c130608060603070803040303080c0712030203061903081b1006090b010807090f05040e0c04090303022101050303090f1201050106050306040609200c01290907050a05070803 82
    0x107403518420320401003109003511508101307140e07803a03440c1800044c01c10000343c0d5211104074000c240706468880c020b070301c83c403440c0030141c200019500001d001700031540855000d1a40902d0b105118552000000c00a4205458252150303210f02c07400c03144104d41c0000c94050300d81001d6024a007410587d000084419102d00284490043c1310b481140800680b1582005100b80b01c00400e0021200d00010688400205082e01b03028a000c0c1c00e200051650381d09401340c450540d8000b415414005055240100140c4940e034401d0412003080c0406605d50003802400e1000003080140c05080a0741c00e420040900a8981641c0280825151494118008c40742c2e40806001140c03040300c600c5c00c642c2500d00c01d803c1100810310000501149061511a00d00107080c2400f003005229000c40507405c0c528900c44110159480c0859070700c1110100b94401180d60207076040d4204000014681c1240d0343c041c50030003910415a00c00000c0d903d9000300102d603504902503890070302d01050307a070314441941c00150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 119925422 1250 119924172 119924177
    0x1061409100e0a030c030501021b190b0c040b070c05130902060906130f0f060f0c020d02010c0501110406180b0301030b040602031b03090a02030105011e0501030207110a150f030603080d020307 84
    0x40008040b81000c5c1a80c409140104009a650b20000210840b20a04441c100c1542e50110300480404040200c0300c0c14141e900c0110104280c45059400c2c00703a000341e0f04001c1c18013400051000400c014a000303030045070803e442142c4040c08003480c0004468440b040a508120100700018440c07614400415a1b4195102e001c0d00480c0c8078104900381280641000ca852504001d00780b00590300240d4058003001c3c1490300840c82c080c2540469a03000280720000c4c14400b504403042c040150a41000141d0580c0c450040e4540c4c0d62001c0040c424076060003100d0710103140f15000300c2e03003c280b50101d238144ca401c10601c064684541c0d9440c4020b43c0010181c100d44919020040d40c0e8816040045005005141c010480b08140380101421a40180d020840c00d603007148075030002e40841019030040300d10034200142ca60081d420a4118103544d1011150300200d0f00b500807908440500400001d104240e8074501c904003285015400c8403c00c0c000030f085a4424803080203642c682d60011503014690b071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 119926672 1250 119925422 119925439
    0x60607151803020d020c19030204200d1a090c0a05070302030705031201170a02010206060f0303090306100e01090506060405131e1b0203190806120303040b01061409100e 74
    0x8042480680440c1c210010b1300054031142150364108540210880f003203400350030020a010109441040750f1000034011a220040500c2c1000508121222166a8408035607101e240b42c9241004050072880d0714003080b00a20720141d01e05080301030b0f5200701c5986c04100c0c40e00d41c420a090340e03103400c44281142144010840400010310500140c00101d00f45401e030001d030750609140c0040c0400c0140b4002590340119009400340c1e03400920b06402200540c4c8000089082c4000720b4114400d0f1052180c0601c2000d003440902440c9000d09401c44d04e403d0460040303030744c032050309405648040e140d0030f600c0300d428401800b4603e040e62002481c1070001b01c001800e10355022a6015449540500801c682c0e601c1d4484012441034603c082601989440914603000c4410780865028070039058030000c00017020005829a21211042c201040102c41101d071640380510f4500d400d04001d0040300b00107503291488000484540381170718035010b002040d37000302c10014075049070802d100c1e2240507803140c581e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 119927922 1250 119926672 119926691
    0x1090c1e090606080604050106020307050a0303051017070501031404050604021306030b0708010305071a0d050c04030c2705070509092203020705041104061205060303071211060f06060715 82
    0x60b0b1041a0080c03090b91200c00541c5010070401c003c4620580c0302c8000d5402c20400c0c4000503802041d04414103a1508000402d505c4103070b0800741e252116042003460000500213036032981e0002907060101c400985e418400442c8290700700c1c5284005603030051039613205101050040c681440401c042c1c03098202c00082c8a59640ca80a09807241910040041105a001030051010501c500c1002d050740c104046680c1107402d2880703d852003503c40a1a5090f81c0e640403604004030281100c0c0110341000308041450b80300d00c1034001003000d555040c917440c1800c0d110501c9c030700c00c2401118414142d071307240ca0341808000c0d0f0600090110003444030780c0310200317001342d60030702128400c10410950196000301001414841404100c0c0d8480d40045507840003800204101c980c4800b60781656101800081b60741e40700d034408a480c500882d0f400410907580c1844030b142c0c00da0b000c0720b0003003503c116030100c400c3e40d00c441800c060180782c180c50040e00a9000c012007404945188011072000032540d0000552080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 119929172 1250 119927922 119927939
    0x803040b06040212040f031404080c01120209030601030305040906080c0105040e130b0106020709050f0903091203121302031519020a11030a020d1d0d030c02010e09040b0a0e01090c1e 80
    0x82145c044881c05440707065a403d05a120381025031031f540842c20946040e050895683e903c551800d06181003207160b04c2400d00b85031042d010f0743c05942d405011a051561a45006042c0ea003040c0521190740c0e00d030007030000b0380100c0010b142032550f8040c0c55a42c50b0a052950602d8000002070008014800c00b1b82d43c400050303040b400c0980204000d5018100c42d5047c2161502915000f400081942484400303118201c02c021080300c4181c98101e030340c00c04105400803000c1c02c500400381419110a04541040400b0504003059510b80e4400c03015100b003113844000010b44103030242c1d424400070b4242c09032004e11010070303802841c0483d0031303080c0382000c00480201a440e50344200854030051b080f0080c0004529040312a107441200362000440c080860309001c201c58003a0210081e08000e01c51952006590241c070301d400c01e00c0f20241081d05e680c5000d08104040c0300c0155000d1020f40c4c501a08095504410f00c584c00045a2088555002c0ca00d840d80c2004c170040b0382106d840044041c0c090004413001c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 119930422 1250 119929172 119929207
    0x4030f0e03070b0306011107030c0b0304050a06050f0a0f05040521040b04030f02031c080a0c110115030c0b0f1206010e030303090606040b010e1f0509040c0203030a180803040b060402 80
    0xb8190043d01d40d03174a0b186000510314140a614149107038040c0c4001d000241040c07181c4000da51880040c2e135101d944e079081180c41c0080d6000041d1003280b8110a210038606c407100d072148603112041090105d00031302501d02c41291411900905103420854440501325040d80c5082c0351700d008583c41e60701f841e448540881560707000341d01c00c0350410156480d5808506090042d507001d2000c411007034a1043c40320001800c00d40005001841d001e0b0368500198515008245400041d0300090081052119040d04950311b119a80016100f0341484203002800c0441c100c103c130070307501090501c00c0c104041d5921092015101800c0c0728180034081005140948042000c0c43c801d1030300c10300800c581e0a004003400111103032001c500e8100004080304211540340d0841494050604001c10b0b000104018804c6815006a60b4511b61050400a004c282070340e00102550049200f02820448a502c212041d0030001612100501c44007080c00082c0100d6006040c15034008006400503150004465448958a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 119931672 1250 119930422 119930429
    0x50714120109050603030702060a050c0102070f05032802030405010302070c0302220b3a02100f020c0a050102070509130b0f070206070206151005040f090e06070c0b04030f0e0307 78
    0x4400180040161000d42d00500d500210117a02071840d088064000c81d010b449618843c4c41802000204004d507880250b044803649070300505140010713003040c60520340320345c010652101841034120741880802da882181001000302e0390000c6251074500401500a500b00040c2540ca8002091001016846d10316100f60495440d41500b41280c0b01c034404081241e2840c4036050040f06500c0d45003d400d040c4503407540071149440c0316030a00c0300d41184c41c001115800603000f500442c2c0008103c20750303500007101d41c08116264086d12240c0e1060024850500102d101c3d007801a40840d0b820030840c20054013441d0004107030003086080d0381e030545898848140a503001c4070b03611002010400c10542c10301000b034200500b40302809850070200620308010070450811032058a4122414007100e0141040710700074005a9200900d003552810040001d1000d000d0203440c030301421740080c4440384076040b0031003101e92290500b0881e0b11103460071903004090441c1c40e014000018042545540c0401455004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 119932922 1250 119931672 119931697
    0x109060c09060f050405010e0108041e0b070306050f06030106030213080d1808060f010b0904090b0a050a0c0813030302030622060812040308040308070318030302061b07030210050714 80
    0x181c07460950000d000c002c00021140412106100a010301d0b80c0c41940803a05400c246407044860310f881c24916000000c0105034010141c198180900304070300d00003030b1803146015880c00c110955a8005000340303200e0706200130b03900c08010001400700d81e010381e000d0001004441d100d103072103036264040c4902e029009801355010a440c801d600341c180c0240d003031100c0a045c50380090446810005400d480e28041805580410800442d00c03580a49903640041c1c2d41c1034010701003648070300303100500100504090342c800c103000303080101829403d030088408c18002c40414580c1c80340301c081a03c08038000c0d00302900d00e03640a20407100d104e24907801c83d000c1c400241c2101d4400200701d4a02403020389080790146080d14000790a0004001141000c030a4404407500400c0c60f82da40d0742070340303011075900f800d075401541c01041c000c0b808800d141d80051079038412980c2a14980040c8c804c1c0121004601409800070010b920510a583c0e000c2616008075400c050242800407054086c2864400340e604564404000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 119934172 1250 119932922 119932937
    0xd0c030501060f06020607120f15051011060408030a1407050d0c030b030703020d060204030803100303020d050f04051c05071e0b0406140717030f04020f0a0501020705120109060c 78
    0x1031000c01e10802c001000350018201d03602e490000040d48440703004102d002840213120002c042c40490f90045944240d00d403100304125209101007003007081142c0605030248495025024100d406000d003207041c1d040460042400d681c0d42e5a8001103540000e142d020741c80d4445449122204441205d94010030141c0c480e5516614034410381c0045503034044054003014140b4810802d242c03400720f4014256a01511444454440c03401c2c04006807056600080444800008001040d102c2e00301e0740c0c00b9030340300c2e41c2517400c010104001101c1b50b004404e01e0300741c480c208100401041c41c1102090b000d4054000303030303040c20a90a4030b49074140320055015102a480b24040c6400b1010840c0c40718001e4520f4103002c1c0d04190804100510701110318030340302d040302c000180744d000f40a00a801c140c201900e2580895503403a054041540c00d60301524124001c000900310241c80c1e10b400c1407010140d40040e1300a120b0b00c0e01c2c0408111040c0e241d040000c1e402e56071803d9045c0490902e000e0045402d03800e4030b4446 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 119935422 1250 119934172 119934179
    0x20406050304120206060a0512030c161805011404090f150506030d0c05030315280e1503100b04020f0c0705010e0d05060106030f23041b080604060213050d0c 69
    0x182c194120040007190045c1c0c4c1000096500c003400c0005a400664503c3c1106100500282c554460185110000e100394403006d4800c1a0150a200903031f012002245492010809894180c41c42800303105070f44400302c00411000d0920354800d541c014044c00100543e10841d445900707e1b00d41d0746003c4010385407984100042c82c2020010541410813500d040c500034030264456a880707003c0179105800c00803404c0e140d45040d940700d004108465826100c129444600284c3d48542505140300d108051044140040c1c01801140180009010090050906032200e0070f1584000d00501035003503031142d82481519028031b29003025008001900009000c6141008005881c81034880b81039072040c40311242e442c00081012411504440e060305021410090341c000a0b000707002e1440c8800c8040880c00d801c440b00848400040d4040c40c00b42a074503030038410780c00041d11940c41c40e028400c5d040e4003140204000813259401411800d20014164080d1a200e80000310219560701e001c1d2111040c510062 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 119936672 1250 119935422 119935433
    0x30b0d0c03060501050f060f0c07030c120302010501050103020403020310090203030f160203210a030b030309090403030b1003021e030c040b0a0908060a05060a1502010603050715031401050303160501020409020406050304 96
    0x4e015080440d1290705109000b00011b00d10310980511b80840000400d1a4202007010000703034014580c010039001c4004e884d80c580f00c4a0740d0003110182d00541c01c001c0006025402842290107a80d005000303880340701040b2007490050801a18200d800d40710401c60301c0360301038000002d040002c19041c0c1d020f03c00c00a03801018a071407001c0d0800310511603070420075200c81551500300c8030340c00700071304001c1400d020490000b030545c05000503990300154840100070405608d90f00040ca04001250b190410390494402201280031b0320404004407030395030000882d903001004c055540680480c00c4d0038545601c8030098110b580044440d070002c100c2d1210706100c83e242c140081640041c54440c10012440e005d000540131101c0ba01c910034046036507462a4603010304c02c0d00b1040145410034200d41301141d4404900c0c03003580003140c0c0c2d000000c2c0b50640620780c020100000d14101e600040080d410841124160740e507002c0b4020040301c5540d402c210000319014140050401840c071503c0d5651240742ca070400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 119937922 1250 119936672 119936681
    0x708060a0e061e0103120302091309051c210906020d0501060801090207020906090415050708070f0801181107060c0206010611030705150c12010b0a020106081f0c030b0d0c0306 77
    0x82d081000300d10f80700e298014110445541100e4200c041c85c055207050900540003482541040740e00315841d284018151440b41d0030070050307180300c0e80803241d0300e880040d0386070318410384807110000148140e2003003031080c0f410001c690064004e8000000e6000e06075510507040781c2c0069401e2100c81c0c1c5460042100342d410807545070060a03050f005526044150740007401c0d4820041c0558840d09010022400f4814241c3c000a00d8403048502040710b400e150070f001d040c1c080f00b110740e1400140e000315242a0903104502d22412031701a0320505c12601d4880540d01e01510645050181c0b808052002901050300e90189250b209143d40142500e941004e500400805071102032020a0784200070000000d5000580030900701c5140c0f600007a151203039000b00b4224401c2105040348505c07c4800410b85140d40c1000740030b4001c0c42d0300200603060b5200c50710350700c2d6040d2100001840400720000a01c150709904007141c00d96040c0b0b0700248030b04103040014283c1450640a075100710b00c4a0050041050038401c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 119939172 1250 119937922 119937931
    0x7030e030a0c0209070e060d0501051f081302190b090109050d02060d0f060f030302010b0306060406060f0810090c030912091a220305030c0c18040204020c0708060a0e06 74
    0x950301d4041d00440280c03040400e020001c2c06469500f00140340188034403c401c010440c01003113540c0c1e9808a2591a018210a004151041030043d52039a4513044201800000e4180c42d22801d4555540958505240044403004c1ea006254101407211407034903661420090a91b0210698650a1680005240079625080b41d40912a8040c100001d690303010282e91903060b075040c0104070080122105005028954042002040780c4840402055010341005407504030540031209955640001c10003511070318410000454240131021070004d204038400c40e404840840041d8011741d80da1145401c803104a0012400a5a0f5040078010440c448205150810051504002c10b508100d0070348907002c05103c50034503d04000840074051001c2c031128083c0e01d0300f10690400d8032680d9091458403944900400882c0d80203400103c00b151400c440c41e880000185030900306a582d944c0d0901c002584080340d1020305200d10900001c0351982084000d1090917003510103d103604550600910b089000f81 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 119940422 1250 119939172 119939201
    0x41a0405061b0703020307090629071202160f030b060405070e0f030106080a050606150301080c040f0e0a05070810060b07030320030f040b0919060e010e0601030b0703 73
    0x4100826614101514201d9560411880900d0b150001c61881c01c446980001c0d018050400c00240c1150070341d01c004202c9003039096101c0c0b46541c0d46034000c01ca00b007240007c05150018080080452446056000b0074201401100d2140d62403c40f406a4211140e00c514560302207400700380100b10748044e0542d0850320699003070010b0b0510080260042d2240b81d0020301a04007010028400d64094001c140188030b48403d03120302e02110b0600d6a1100011210f044c0100d81e046075056036a0740700f5088904880f42d4502408540e0084800c0002411401c60350b01101500c1e00c0703c04203008001c1c080f401c00f4a11a000034a0b545103040c0ca05810480c01010003210207141010401c00400c04000f02c0e0f01c0958546400606402030101304a0a40c844404048402c507002c010441c882c403040b00450f014900546403d0700e6507681c190b00c20340c2e070512810740081040590010340000b91040d00541010084c0b02d001040c0f010400d03141d41c0c41c0003002da1041e51246541c00c00d02403025014402d030074540c2d100c003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 119941672 1250 119940422 119940427
    0x6180f0b01031509030e190e1509010501020a0510020304030e131410062a0b0709050a0b0a020c0d1401020f12060108070504230d030f0f1805060c030903030304030203041a 75
    0x20b4402a04030b40600300107900505007d42c0102c004031206403028054801d07184085504d080000b000d584a16005404c1802165007800201d400d600010301d440303000354820003c10f00c01e4103002d0200065003015204030148010b8040348003e95031a002407070301d87c0e40c503000c00099101c8a542d1982c91280060440c01c20500c181d1001c1c0481030344030521035254440711040c8000c0d00341c0c86001811305a00410082c0110a00000348051203138026482e2045800807035000110503102c0180580d14454a150392004d40d00c401c40703075190360038001441020070303000c0c0c400030f8070140d007403541c1d10309981c460aa1100c03d2200080d88140340c04040c0443e5401100038646205a8a40310401400d64416030241c0c1d0308040c1c0c074a00b8401d0072024045030311226280074083d4016181c1a24001d80801c00702d02c410030129103007411500c1c10500c900101c000c40710b241203000303440c2860318062140726402042e516005020800c030400503a1010001503008511a0f401540c1e15441c0c0004040901c0c840802e000c042c1070304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 119942922 1250 119941672 119941691
    0x105010504020c07030602210708040b010f0b180a050301020d0b0406120c06110a050109080301060809060f13030504030203010617070e0106050f090102150703020406030e0c030a06180f0b010315 85
    0x5000384c142d81e4400030050f41d82c94400d03003105440e16150303e0391054084203c20041c030a5405002c40d40900e1042c80300528503602c80910401d000c4040c0540c0c6c82001d0244100c02c85612101c5040f880854090514031070340b0340380d9002c00d007a640b18003041d0b51010b443d08908032076800d0900c11080109450043c0d00c0002c9160355035001010200d10502c0100b0008103481100030006025001b0110303071100c020441d01d6110300e41161107800c00d00ca420f02107171090000440c50301e008034455104241074420240c565032022801c0c1001c3c00c90900607001c21805020120041c0c80900c910030142031000b41e184000d4070b40d90085881d103915500051503c218074001000881e4100050b035414900c024501390b25510b880004030f280c02080300740b501400007114180f00685405900a00584d001550140301948950501300da079400354014045d099401840301a01103031469100425091682164803030301c030740300d88402d0100c501c08401600c143e10756500410800800074440b940e80b51480c84188103008a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 119944172 1250 119942922 119942947
    0x151207021b04140a0903260f06060a0806010f140d020403110d03052d190e01030e030d090c08030f0a020c0f090402090a060510020f0705010e060708160f030c0302010501050402 77
    0x1005800401c1c0591601c0b2400c003058040c1415441402980440c8060b90903031035044007802c2d00a56030285103c4564000c03402608100ac1155200c03029503c501501d503c403030f4011503080c128860000d0400c52040c200000f9808554001c3c0039594031310f13a0247e115811030404d500740529200e4181d1180440706071282c00650850203403440708404050007000c8040000200f000e0320204500c0b0010410f0010340b048110154040c0800c040ea010b5485030607102c000030040d03080340d0340c03ca5220103130381c0700780710055000c5200d4022041c040d100d05404540e55544144937407464010b0f1840503050310012603800941941001030807001001210134542d880204404900142405030029029040243c0001c03244c0480350815402040f010f4544041c61090140081d00d40504440f01751184c010800c5c000303090341c420301040c96403c00060105207003403e00d0752000840c2d03001c40400801000021051310204040d0900802880d01a84400404150f1427038020308550050b00708a04c203610502040c10003d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 119945422 1250 119944172 119944211
    0x90b041403130e040606050a030302010507031a0a0b030603030403050f0601061206060c030e030703080409061a09030c090414120d0c0c030203190201110d0c02060f0c030402151207021b04 82
    0xf2400400ca000d04d44640c1040b002034000783c0c100a41188400e00e00004042c4d0541c06a0710601d0165020003414030107883c049040c2c05454469688a400014148018a01f1000039030304103d00908132480d1a03940d80e1094141000700390404039030b4104500401460b0740149841d41100d0b50880104121400c050001d030074100308540203010408000b50a840303580701003140e100655008100161103c1c1d4900590700504802d01034046402d40850103080f402000009640103144020007422807800307200144581020001c0003039071030310440d441d44103c82d041400f403280403040c46407400c0d0f510343e1156894070556500c001c05004000301140d0030f50110b80c0c04000d850048908003400409994582030407809800090b004030200c020010305c040003805c0710b61144440485503000d80c0c000c2e6842c2c5030080c0210104454040c0b6112040000500500d840688040755504000c085170600110244007803402a0071030701d05025a101240e80c4681c011a030565a107610003ca40500524440d01c1c0000b2005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 119946672 1250 119945422 119945429
    0xc06080a052404090c080c03010606030203040b07030509070905041a01061e08150603010b040503011404030c240e0703171c0b040e0a0302070501080106050f0702011d0301090b04140313 81
    0x158a005100d03100350f515508049003050300700f00f03900c1d6215168505a522001c00821040c801d620b840800180b90780203009032840ba54010007026490f0390b0784902a000340c007000740707848503a00480101160041d45445100e0155014900d20111804400001030160b441a04410140003000e001e0310480304031001684509145031803c4065030b2910340c400c21248022001d02c2e03901c20404400840c0003400b5202030001c42d40100d0007032000405040606c009039800342c9002e00050075010a03280458105861529681d1010380288400b22000852000b20740a1400c1c051980d0048081082030010404e0f505091a1920711110715012250113a8400364410b950380c90242070310361034a9402c0d0b0750f841d8407014510406800f030701c011041a00e002900d0302d060f8001e16000c502c20b01c2c0042203407032088003a510a407085a21617450a28103400550b410402040588041c1e0040c0032001c0b0143c8003800f4450211348a40e48102160402d071500c03c504410178054442150700500800e60281a51803c01045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 119947922 1250 119946672 119946721
    0xa0206040b2220030a11100f020706050c0c060315100207120b0402030705030303090a1a010f180609020c1b0402032203021015092a0f05070606030c06080a05 69
    0x643c0c4290050f035240c411103071482030380340c040ca28254003030050a034596413844e501280c1400b0662082d0800303444184181d44c035070300103070300040c01841040d00543c000d250034240d800445042c2031425000a01030303401250200040d240380301c0c03401014240166008407003802400070341205c40c10040c10304002050f183d00989000080404a0159101406404042d04010b810b6903030303c3c600000c010780d940c00d02910485050071014082d0241b184c2280311075042c1d84c0505c4203210141d05c0c092141d0001090200c00b000c906549070400245010144000c12030b900c91100546000e40c00020070300c9600000c1480b85028500400810140201d401d00030842c461042d600a0000031540c1012480c1114000d0f605c00424540700002d948100005520f0007110010b080a00888684a0340384914403a1300311400c2a0810000050968500403c541e07440d140f103d18045080c100d039511031000b51201c60340140c07982d1507959000d0003000d0b44030322074950040c0c02841c181301504121009032190300d100c6100e81030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 119949172 1250 119947922 119947943
    0x40b24070809100201050420060403020103091b08070501021b0603010e090f0d030213060e09180a0c0b030906010f080705100c150608070f1a090a03080a0206040b22 72
    0x802086400b030380c0c0e00c40d101810342c2c0c40084100030007074000e0000707680586815800854411074000078401d005900745c0041c00d480e040a25650055024124000085038080c00d581c160700d001d0b250981181005002020041603030616001c00a400d01407013140c0d0384500c80650720401d86036160001141d0444209066000c2a50755000000b82400d0b500c038903541050055080c1a1045a80354028021140d2240113600d24144e4a09003950342c0b814107164180c1000c010000188410300301051950281180000e41c2d407214422795403441e65810303580209200c000c0100c00e06c001d4441c1003203480d0240c031080400c070790300728280418241c0c0d402152007140d20982d540c40394001290322132800f0860070b5034024901c802682e4216001e5015101c640112425031091070f0340011002180d030b501404a0b03110715a030b1420103540b6007070300440354003560150b41c01240c0c0080020010305040000c001300686940540000d05251a0910502d50041c00c00c902a00c3d0741810300501d8410303071501b810116480000c020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 119950422 1250 119949172 119949187
    0x1b1d15070303020705031b0c010f0f181205010f05010509040f12170103061d1f0504020604080d020d0212040609140d0501181707030e060f0c1b040b24 66
    0x2c0103071080c41c0300100176020100d0307403220701d1101c2c00c554218140080190780c204e01a800045580d035400f83e840c0e00008280f01125020309019243d007900007101152115845601c03062000402d01c55440b08507800d1b90b4900c0101000000c82c807403c0d016000403203050300d9505151325190445e848801014204160240280f401c1da0b001d000c103040c284e0502400c2c56881c2da502c1c141000145201140e050300d03134082d00c0f200761224002003440038003c0400704440001d80220a5800700a0400a00c1260495010440410101e000300142d01c803e00b600e60040140c2802d50b20000e0810700754554501e503200c0103002c14400036400c1440e110a46040c132480b09010101c000c00902484003c45001e0565481d1640e0500c01c0d289650072605914001c103020201d000c0c01e0f000c03181017441498070103400188030300004100f40c80c060000302200100001c0d05810b000004150504000600c0280684c6504d003145264190a25001d50071a0760b00c11104078150382c210790b03507020b03201e03522050300609100c0c00280c22 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 119951672 1250 119950422 119950427
    0x302060f1b0a0f1b180225050601080f06040305030a021c0603050d0905090f0402010c030c08030f0103030e190b09030a08030903120f0709030f020a0503011b1d150703 73
    0x403070740364040c0045414018141c100304a02c110305940c15240c42801206801d680e450390381d60380007250340105580f181c0040c10000c84000b0b402030400c0c1e8464074a00c60041031945025001c14041d18003400107000d03154980300b8194507001c060320b01d6050b6600140304000c0480d4024003030320350000c20a000940c1c0e940307100d580034150300c400344554425a460407a0102c02c2c00000581c0d21118852500c0c1c5041c84d0b0f803140100b041450007210400d00e1b0303564010010300154454802110454482d042c80c074440040c95407800b045400c100c49400210b072681c030040081c10740c041d0075981003007002d4400d0f131120b40c80d040341e516001c03005001f0902581c070b00040800b0790762000c0001017646034001400980f6818012195600e96000b003a02d0f072206115100410034405410464034060030054451001d0340d40b55903100d105900240000740e9005034140750000e190b03142030042500c0e40c0031490090212400c85200940719407044000c004a4042503090030f000d60711200094545c00804000d62a01c413500d900c1c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 119952922 1250 119951672 119951707
    0x31506060915070309090b06040305100c1b051b0609010c0f05031b070e010602010e031905120112020102100e1203090709140907060302031e04021305070e190302060f 73
    0x10085154400190326084c168080301950540706108410f01081c4034041c100540e500660001804640064100300501b4204bc0d018000c0484542002031406400b0000d00c60500f88000c000d0300c0e5a000b0b00e80c9a808a620f00760f240c80200d02c2118450f080a403400c0000380411400b280081111441240701400d0200400c20784200d09410f1405c0f51819101c41c500325224012486210107a600c00320010401d1030040c0140960300c1046030043d410000d0b400c200d9017410040d40064030038440304008d502d6003d480e44503150b01900080b9890a8500402d00c002407034000c0c07500540580a2070601040c00d81400030034500124100d03501000e8480d1103000c041400c000039a44250ba4043c6400b0104d10052029a10b02d0b210348150030a5500d801d40da02c1095069100440384030340c200541055403030021011100481d0021f002600014200041b481c141003141c2d01503d5800106600c0083c0c3c405520b40002d0140410769000070400c105851540803806600503401803030f5005002080804142c1c180d460b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 119954172 1250 119952922 119952949
    0x1020a060e0c01080c090d030f030b062b0e1009061d0c1c030504050105030c160804050f03010e0316022d120607080126070b090a050315060609 63
    0x804001105000031520b50b1241c810b015540454031a5001821942000041d074030f011700050421100e070880781d5412100100d1140148060566403906a00907854000c040c003440b07002080203092113602c0b94864040c0b0202d40c200940030301d0420003590111040411804150909601e0120720640c592400c00c01a11445110926040346403400c410520b6000507600f4124005039240b0810901e00e21403410003d10480c806008a04104010482c6510410040d40d00206e614042814020b800001200900440724141d42180021409100314036180c62100300003102203008210102d04014550b807640100a0072642a020305980c0c54199220301d80c0054505000659500081100d14505203010072100c103580d000c2c0c07481c1e003d4448201e500084060140006131100309681e1302c0e2440c0781c1248843c00c86440004501d8000081d5419810450034020345042c2034490385403814401400711050706607100c5e47c82070348031000c0001006511141550001415198150343c2c46c07903140405e60300740c801403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 119955422 1250 119954172 119954183
    0x7020d030e1c051006080a03020604032a03030c030609061805100305101e020301051c05070f14031902060708030405011104141305010f270204060f090621090201020a 73
    0xb18108210001c11041009a50b10b402080029181d40d280c80da40c1c0c031b20010080160b80726601140200b8003a01c0c0000076481c003c890744100082c09000d2007894200e0210440200f5112050a6031980d0540264000390424070004c100640c601030701030b111222045511071500c0c1d076900c046a03200301d08640310342c0595004012100400004400c607401000b407183d003040039018860521134241918001c5034100c98000b40b01d4813480b000c0504246039400c81d0101101c2a02c1450000207a08000d8440107000700b80c0541040c2040030a402403506008200303a200c08040c0460030400b0040e6510401c3d01c8609420000d099220350302c0307182c01401403250a1210681d40300100c0c000800b1103036032180e001c2d079850946020a0003910004044140c0701c00f8003400c1c1e000c4510f224184606890600b0079544a000401c0c01c1c0441c3d60104180022a409034124000240e07002846142040e003081401004055528000030500c40d400145100d5044600c2c40580703880d00c4010744015607108004074602d654020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 119956672 1250 119955422 119955469
    0x305090a06060b0a030b0603061f02010902100e0306060d12110705030111040302040b0906060a14120405250e1815070503060a05220b0a0806090a110607020d030e 71
    0x40180c1e02d080d40105130100006828174004400c14180081501c0c003540340079000040028030701042d0200044030b00c890300e0445d0360300c064880c0503035078411581c003800c161903ea004c0c400801200f41414140000d0803c0d0007000c1c8042c01c44005042d80b4a00f460350389140c07074507115444850740884d061005980c41291300d0740c04c00151030341c4204888020421207208440c108800c40508003401840b0300115080341d48520280280004e0785d0240c507a01a540705403071480d9241880c00040c52450101c00c1d14203545c0750784049410b08860700b9680e803404c084061241c90601c414038180c44520410070080549407200803015400d82164002c100c080307268060703203100c0b050314901464002d2658004072000c070712034840e60400290310705024144c046082c207000e603050b5203603100410241c081d01000203ca9013006107080e001501c1c1c0002e00040340110009030140000c1c1103d4289680c103003125810440c440c1908014190040e40c0301c10078146a2a81030030030521540d09400002c000d282c141140c8041d17410341 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 119957922 1250 119956672 119956679
    0x9060d150c080114040b0a03020913051506010f020601030507060f1101020c0109020a06090518040f0c09090b0106030513120e06180a080304030206040b070c12031e08090d0305090a0606 81
    0x120b50a14180d0b50070b481c0c0c10784101c02c81c60800083d030f20340012550b04080105014000b43c104843e1855110007403144900307454045075251841c203081200c60315104202081404070940c1e004001e15040b40081c0300801c01075042d5111162600781500c150020300c600309080b81c0c1da480c05a14848000305072000215100c401e8000e0f803a01914201c2e000b02e01c030317007100c01d00481c46501668004090b01c4000c0d0811112b02c007078a440c50100c6030080c000f5500400341c1c07040c0c100058403605154000c1c00c0c030700318041512411407400c0c0c2070718201a003000083c903051104000400e40082020216036801446200b00704081c5c61301941d4031954401ea81e50030500010b013160524402403401e10007658183c0ea480c4160340d03106e0945490f030299000080d0711440401c010000c0d030003c2e40240400328020f0000301e038280c0e42c80c4202010308412050403800714841e0040c4d1132113031003005544440500c450070020050b1600700400c0780c80c2c0c022628841c003032540d5000400e41070181000342c000a50341c072481c00c001c11a103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 119959172 1250 119957922 119957927
    0x9020901080c0a0501050310090905010b060f0a1223180105090d1e0918060504140a15052211030f0f01080c031005040305070c03060b0f0f09060d150c 66
    0x11602c0741a009044004002420f0752141341264810411000309030a0b00e42007295800150407a01020f9805640760441079100d40e407160028480c0c03222072000d0942e034503c0440d014010500c3c507080d02c98050300d0440b503115500080e030f50095111100b1a0380360310b01d55400310718003a000c800403a060100d42c078000c00c00904080000c3e444083e032003242c490840450006200c4041c4014080301500040c15031075041010599070303540b01883c22018200400c80076142e9000c10b00300c0350003010118044034403809201da14209885800c1402601910304c0c407809050034081402d0003968981083d1720650040c401d4002c40f12540f001007032180d80200282e89040c20703031440400540542d00c0d0074a1804540000990200c0064180d0800c9005400740491180d00100240142002403003a03081c03001c00c102d91030000c1c4451012202a6210300030000d40d80700040d051090707101130051002d001d03601d00c0082c0740c202da40b0795030030f2688010222020300001407a032500f00c03800c072000364000c0e40450914480c08000b54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 119960422 1250 119959172 119959183
    0xf010f1b03030203061503010317030c0706021603260c030a0603061107140d0c17091c060506031605190302060d0911060a050703080c0c0706030218010804020a060c02040902090108 79
    0x81084540c0700d0440400b09081c41b20f8402888002c062400030034070b4125444020300a1944402801841400c21135140c485405a0740070b50814500703a00781805240405403c0f00c08403e600720300c0c01c402108292845c00b44410000050036a08514030040001817030000d007500950040c560046041c0500741c1c400c40380624030b0704104422500341d140600c05840205001681b199151035070366982e40700316401d8850300d0b20548e110011092104c1d00b00103207070340e645422180d03000035030000040904a8500c0c0c2441411100d01821013442508804d641324031002c00d50b80c1840c250b44003181c164894041020010040e041c05030f000a40007003000c19400b8590400d82d1200051032b000c0d07064900303044582800c212840c4641c50101c80454010f02000022910808101d0740c4a8010407000313151100d1044d4107854040a5401040042e40001e050740c11104900d400540e03090080c2400c201c0c505081c1d0000d84044003d014200030481e030124540d0640d603d03a040f841010340c010306207582e50350312801c0042d180c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 119961672 1250 119960422 119960431
    0x9020406050607081e0906030432060403080a020a211407110c0303040509070518090108010c090b0918040606180b01020606010f050d0b060c0d0306170c0f010f1b03030203 75
    0x81e03040690004c91740308208076802c10b0f0000701042d1550351240d0b9000c001030060084159900310040751000c0c241c1460380308130280364a6000600703042c6028038009282400040c024807030103005000741501f064004a0f008010008555546000142e10700740000070810280c0c11940c0384900702c140700d00c00e42c21001c0c0c0341c039294905040c0c1e06042042001d0680d00d124611400790090034503000110524445c00241031446404042e40b100302e00050006050000280c22078805650350b071703043c83c0c03289411181500c000c262035400b00307040552010000390095200f298660160040e2000a4104000303640280090000d580c007030f661010025241c080144020101640544a4840418040d41c001d000242c032008180d0b03a15032500c115950309030054a9105820f0b03401c20000c2c030441d0198032040c0300900000007070350307000601d042c42c0560300d8a460441c1e01c1402075907041540070721159103809024043c10742081c02c01c551740001ca000c0840c0d051400034604d08480700c407135085208060f07041e001103018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 119962922 1250 119961672 119961697
    0xd111209070f0b03010302040e150c13120203060a0c230d0e0c09061002072c010f0308030c0315030a05072306041a1215030601090c080a0902040605060708 68
    0x1c072500d0700002c04807442d46000b03c0e5203040c0d05000400042c80c098101e403c051031500c05545092175403d821052442042d6408a1018030126204280c01c617120f040d20006c1c0301c4140c80e11071003071154000c251643c0010304100da0b560b0b1600c0683e4a0b140c042e2444550035100d40c0307004800d80e00080c0010780e2070b8014501010105044c24001c1610110024190800000007000101c040d1528802c11410b83d500c2031740801503028a00c40010884120000b21100b0703854154481c40350081d40d500300048500503086004203855801d020f00c0450141d0059940c00561100c0b082e80d0380d141c0404451061119069460b81889100002000c020000c00c008045405001c1c084964a59400713084410b00100d41c079031a000b0806200400003004016984010040003140151620000e2801104007100481d58030342242e0818140440d2400d0800a0038010281a001001f0030002c18000405180c8040c042c810384035128a200001d641d500e9114a0007090300a021070368070515881d050042c3c1d08602e101664 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 119964028 1106 119962922 119962933
    0x51c0c05041103040b0c1204290c0c010e0304050f0103050c0f070f0b0a1a0d0201110d111c0e010810050409030804050f070f05060d111209 61
    0x5102801e0084943d81c0e2070716007040505098080c16103c0071070000c0200c0b100b0009403070403983d0800c1d03101c8104003004104401c4c00706824500d441d29145a5001014018403407000c10040c42e240c3c504000034000041e000740010380340d00941c814207400014a41107110702c0d620a070300042d0300001e035026880c100800180c0c00756264014501c100d8405040823008003e0006008845074010005801407140f1030810911108940000310078034020300303a04c80300400b1a8003802d40384200514003002c481403041005401007000c0d0820000008038000ca0048a40c584803c5140183d4800140c58150001d087c6000441d1840002070560740351014100c00421a95910701a28200c1402a03548125509003410882c5c103000c092903440e41c01d0b5000b00004c00c818800f0380310b40f02c01c0710405c982058580c4002a1964064001c4440700043c0345d900003180d0b1510592500d5035400b42c02203108648 = true := by decide +kernel

theorem cover : BRFrame.Cov 119784172 119964028 := by
  have h0 := BRFrame.cov_init 119784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 119784172 ≤ n) (h2 : n < 119964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
