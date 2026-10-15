-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5124
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:49:41.783533+00:00
-- url     : https://prove2.me/submissions/3eea4b6c-6e28-4e88-8ff5-01ecbd14a579

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 921402877 ≤ n < 921582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 921404127 1250 921402877 921402883
    0x609060f0904050f030c0d08061c171201090507080f04170c1f06030201110d0c08030606070b0403080a0e01050412210c0c06050903090a1818050c10020d02 68
    0x341040d402074503640041070a0260801060f944560b21008480e540e4400d20603460710791449005260208124002156403440c00d03174001c0380b280100f401710721901c0d025629014541e40c480551003e8007030003003004d20004400014998068201c02c50003150500b02004000c109010060000403180504020f10000030340c2e040c4400f030300400a4030407940b12a158a101400e0451082107424510003440c01c1044800b403070303004a0100d9000742ca45240140794184a1616100819408000030780c1ca600340300300192007900955040040589400c0c02c0c1100756a4041e590901a6420b07004142da160801c07e0385901c6010300d0085009500c000c1c0854141640c4611a4200e046040c00601c9203860320300990049981d2901c0c4030034103440c1c0900000c1c0c2000c01c06072880c10010f40a0315028180800241d4000d80003040391001d4101514421804e4a030003980c01d24000c0341c18429440d1a201c00d58009a2003902c0c00f410102d41c054809809104071110421200154104c1041c065411811038298025004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 921405377 1250 921404127 921404149
    0x8162c0402220e06040b061e011206080102030a0f2d1a180603010f02040e06150c010618051e15010e0a030f1505090a140102040b04031406060906 64
    0x40d40c2c221001848090301c1401104050024041c41d0b190a05940c8001c0b80051000d005500540002945469201c140880c0611025060a4070818880007040c903512500c034030384104c0d0307100c0400103942d0b4490a0f518260703070054413104001d54490700300741540102031144510a12107611b410b94140c0c02410812096060709080b046100d507a402e50464603504621252409a0020700703003500c1e841000046200d1010694009000b0740c640423840b044c0c0382c0248210740503103103041c08030a4540d0300d0740100841c2410905820f10f1f8004144845041c168090003000b014100c04440d03080c011003511444421100700610b161292003074102e500e401c61340c2c2400e00320341080a42041c03804101b80c800068410f0000c051440fa000000008004244407450703260ac260144142c1d103910411500ca2800c0007a200c0070742e002c007803d41043d1210340008800e40080084c0d0240300d8000350a00f030b03880140d0042030300190b001b500c4845c0407800c3c40100d10001c1c0492a80b1400444007c1420704000010840210300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 921406627 1250 921405377 921405379
    0x10908070e061c050d020d09060801031e060f0e1902100516080415021005010b1b01060801020a020d020f01020a0e10110a03110c01090e1f08162c0402 66
    0x5107001c1101d58a800d01a200d1210070001c030007058580e54030304140c0c1c8000301e0075420014010001c6084956220340f80c0142168416a01c01606034210b8413000b0780c00820407111070b907110400001900207411402219119074441e0000980c04604100d40e5080c06503102c01128000d5440000800682c1c41c11010b0b20300e1142454400d840d00c00030400081404001e81026046180c080360025031950030b07400100100c003441c0e081d104446041f4043d402a1a420700030982540011b000301d4418402101e85040c1000c1e10703000101342d00b5540d82130075007241d10a800750300050700702184450059404004040c07400c54600000c42c40c050051500178240f441600450303101e00040031540c10168070468426150210007011342d40d4040041c41c0c003400120a0f580e000190740212500003080d903002e050346608451021200c50b0113540d41071401c00040e0009101440c9620310b02c800861002010001e003810b4025036000303a80c0d06424403028603403202c601010100036490121821b55894100c604040e00598 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 921407877 1250 921406627 921406649
    0x40902070c0f0e0103330b01120618060f180903050708160c0918020904020a15090e060909031909090e150601020a032007030b0a0c02010b01090807 65
    0x18080c90841d0540489600c0080004941c00c400303d007109540c40700b24100c0703200301801a00407010b450505242c900341e070f00040041110302600a07503502160054151800c0514203201c1701d44640c120082201c0706900300c000043c1042d20004180740c0325220383c40c09004a03d584681c03092800414541c1c03100b281d40780a0744141c031030500d0801c0500410a40380c04661020b215515031040242113010880025020f40710303e40c80c0340000030004d081d8401d50304055000130340d0303034814980c40e02404034810b400b500403600021005000100c04000d40c0300c0c0c4c0c0244605035100e02d00b0720300d05210144540c4000d01842d101d00c1610007809030415000048901200e517010718140038110b400000d40d4241c1155102c2e00405051983e41e443c03121002c81e081108070504407a0340801c0d140d4000480e51071403100b070010042070b40660800c40030842c05106040202d00c0c0300c1103409242d102d82d02c56031614001c0e01d4844980340c0744c6003020199602800b0316601d0403001e18111400d14605600265180c45c24891410206 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 921409127 1250 921407877 921407887
    0x10c0804120c151b2d0305090f0a050a0b010501030b010e0d0c090e0f1603022b0218010806061f05090f030708031201060315060e120601060810050312040902 69
    0x10040c1074818141540b03c0070003d07118410684070100340c0480d245030020b10791801c40348861520301d00010481c0a45800340c4d00d06180ca00c8140c009040280c502d210900c9403140c0319441c1c40d020411400f42501c02c0020340191300481c40c1c250309444040e00324038107141c05c010340350901d130340c0c0100b071205140c6040350702034040540f81c10204503411050b0003d03100c1c00d041000e100c071b030803000007900d0f18103001500440d00c030505044450900003c0d5030100961000c902c1102440b11f081280e490071200420100340e00311814031b43c2c00600000d0750104041c4503244168010440030070300b400304551041c0103542202282d807a0440034005908070100c01000d201000c1001030494403224454042c0c002c024044031000703501c030038445640780c01003203105005144810000c100c561282c01640c010990041d82d5a4001e402d0000c150340070002c03107a407540c00004441c00155038201c1088030500030700c0c90341c43d100c0301c07800c0002a9003624481508028003e40c801072070307100d80c03169240480781142d0445c1c0c0010b0700d80c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 921410377 1250 921409127 921409133
    0x20316020d0b090c210601050424030c0302100206041505070e0d08040f061803030503041e06060f17072c070f260a09020111010905010905010c0804120c 67
    0x1d44180d04028069215080400248010000f03a0081829088503081e100500c401c003a8001c021080c640c0d10240e800c10310042042e400c140d002203e041c0301108051804030302c0c94003c1032945890340d2090318207001d403000030415030421000c41c0740b2840c00c601c09005189815100c0380b9a141c08169514405550341c00064507091041c4000780e86010018034005100865051415407074219010b0384148000b2040009509800340010f95100310042c41c0c07085d9014519207040d212074100400c10303111a003500c3c5000344109000081c03040c9071403255500080c864244188607514040301d4210268407450b50f09440302c21400003c481d81220b1580c003130040c90411001032655030300c03031a03918920310550320814408003a402036504402c02d600c5a592400342c0048510fa4580203104160066070842800b0200c0d10124043e00102d11403401810040820b400100c5441c0c01c50340100c009032401d0350356102d6402085003c2c003030007941d0046441c1408e0f0b1800c003611802c11401e102c4c0d01e12418462a41400d00c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 921411627 1250 921410377 921410389
    0x4030809030903030d150e1303111f0e060708010b120907090c170903270102011508010b0415031109041403040608090d020706050d0903050705012d02030702031602 72
    0x802c0308050156511040d40d0200440501850508281c0b00200441d01240c03030404155a10712071318403c0c41c02d900142450300c0030f80d110300414541c0e95113409504145031544c91292100c480801c80c801d07000601ca4090305080e42410070203444401046100c0004010042009040c0c0340400004c618011503a00da055001e45030043d164072032800281000c41e01104607410084144401022120b170b00e0160b40c61001441e120b208111481d10405c86031203007500152103012801840d0f11060000052900c66100c49a0102c8180d50200885a4541582994900f440e004804c00300c00741040101205003190b8585100a25101065000341001c80003d403d0040b000c2c04501203d00a40c00c0e00d50310b80e00c66000030300030f50301102c1501aa215401d221311002d8800140311044818075a21107092a62104d0558058171b00b0f1507040d0100700c0d0034824407001c55028410394201651290070460701c0604071815040420420810381c100503c14000c2008264010003100c1c00500b4418041c54110190b10004007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 921412877 1250 921411627 921411637
    0x1a090a050a0b0717071a07030914030a0906050304021513030c08010902010912020108071b051f0e0f070e3c0c04052412090307061a090403080903 64
    0x341c4003129000029003141218001c0044034007800d80220046000040151588a5904010a0301203d843c44007a03184030301c40300f140c00c180d45140c040b074031082c0c680b124041180c2041c9140800d400000303510a001d600070200c030000b070415040060a62a10744c00081d500e40201c08030004252000540301004030035081307130f5400b45521080c034548840c2c0f91110325000b400080c904030302080400c0340c086500d81840c0c843e00d008560503903070030601d5699140121044940c1e00a400000340e00164000c0010300b09005090010607001858a00264150301030340580d00c0445c0ca00c8100c0d08060349001240c2d101140e00c03403d84501d507800c1113070b5486000d01c141c014990a10000782e0902d868828440d0810034202c0b003402d407586400851426110402c202e03200307201d1881502c3d8401c850040c0050fa425601100b02d8010100154082c14480c0448d81074460040c00c60381c12a10b5000000d19030704000652003001c010007001c2c44501518404100400c24480340604042d0612070740200041100c0410001c440d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 921414127 1250 921412877 921412879
    0x30215070e010e1507020409081c020d1506080a0b0109090603080918160804020d08041e090203070801050f03070503030a1220070f03090e07080406151a090a05 70
    0x20000d00e80380c00001c0810201d003001d14009a031040e000c0760710b480d014140c1c40d80d840c0e000200e14a028140c1e400c2200078441c0c400304030303481d030401e1007456041d84083c10030700002c0248000140c1d42e06070b280310940444400d822180e070405150704040c4012548075400c0380d8010700d01c20300003030302d650b10780b0060360016140da21111659003040d501004121480d07020300a480b0303007030720314000c901c6a40900e80d5494504403841300040003094a000b403814800c00d9102d401c50b00180c00ca50300c420003511031070b4966000b90482ca10042148403009150304903021070302c0052005410031421410b04d12170040c150030303040c4901403140e1400d0810f1850390342c0074401c00c001010300070700b101c1d51a120f100018000102c8040c40a0a441c030300031000c9c6821540321303014001c5141c9850f001e441c0820b5652001c200030360b004004e03400c120343c0c8038004c50300440d0107521600404e035540b2001540d1402e46410782c25286a86001d0141140c030000400ca1604c034844800d085000110000d500c4110b40070125010b1080c640c0b000f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 921415377 1250 921414127 921414163
    0x724180e010306140a05091b0607080409050609010603050907270c0e2404060f0504171b0118170a050102120106030605030d0503070c020a031401050601020c010318020d0302 76
    0x820003880b607100400038111a04034400b0341d034031020174030201c5034220b40c5142290006039800342541c42c009035240100030000c00031400c0640d5621807491980041d00a4070007075035a4802d105041c90400300e600d005001924040c0018a040c000082c0c075992144501512183c80c20846448010104604601060b410320100582c110200d07004001c514060455409800d00080309030940d400c1580a06807000aa86164945880c1140848141c80d0712051541045803e000c04245250480c5e420036840a41600800e00070029110b00c83c800f44030940d4040c1481022150a85400302d50f1501d9011500342a10361751100e2054904c0b2803c060fa060300091503940300040c101031016803e447c0506982e1a40e504220454641e014543d9440554402d840440c00c1070001448151042040d040d02c1480a000242d540c0d44e40c0e074409079031030140094018103945038010400c82d942d0400051045100902e801d0040041030542803051950000010707000f080d4403004181072600800115214800141c3d517 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 921416627 1250 921415377 921415379
    0x1406160218041b03081804020c030406020705030c0a08060f0406151712040315050702160806070e040b01090605160b10031a1014030f01020a110724180e01 68
    0xc4040c12030780032070301140d030102030011111202c48401d03e94000d980e07000301d19600c0e0540d00c81d10109000701050388103600a408012141000009002410090080d1340090904508050415042c80094070225000d203440c9001006207180010784142c0010003840304045589650800402070081c0301c3c034005036841d0200c000030714544044494034541e800c50081c0d8000c4c0803080d00c00310851165210240c00350300003201030070b03942009074896a00610b6078012030303002c0b032507100802c40c442d01c680e03101e65102e8102d1b20410000581100b1014901d40341214100034a11407003001a041c4105030040004018001c07036042030100d121118005940e4000c88003100916118191407080c1d5542c0c04100e95540c1a0003103c00c2e40c54002c05a1800b070f0110301d0000039818200000f901c03142840d080e110390b241c07040311102c1c82110b070f081c8010190419556105940901202d1a1074613061050740003c0c40002c000d00540040340c40240c2036440c0c001b2038900784500c01405010882e050070b940d003200300c8000303640f00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 921417877 1250 921416627 921416659
    0x3091407060e0405090705120f1516020c030304140f12070314030909041712010e07020c0904080f030c0724050a09051f0e011b08010f14061602 63
    0xa4103400c9407002c0d6510200c0d40800c80502003640d10988034000a0fa2201105010f54a040000e646a4000510455030915100c01447d890580d007204440c080045010030701a054403043d440d00e0540348680001c0c100c0070a60390109543c2d103e140300c3c11210061041074140340740d8843c81c20700040384000f00303604a4825600b0603192122580e1004545104011002c0e820f10903003c42a102c0340440102820748655aa881e00f0181265013010b00b204410104003543c04440300b00c0c01c20b0702a00d8a0485003d05180020019180c14400300d4000d1091988008000008e514501180c00d5240b111034065141e440d040f4040f50dc038000c0340001003114031140115180020641c0b000301104050100900c041d4a40c0900320341250600780c030145c40d6411401090341c2440b11a1071130380f0b42d00380a50300012440e5030100210b084480c455252400300061161040042c2c1c0c0c49070141d030240140fa80b41d803407010700d850425502c200c907002109005801c08a2074804115035002245042e54020b840062a42c81c3c3c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 921419127 1250 921417877 921417883
    0x402040b0d02030901050609010f0306020d020c010f060317250609140114061c020904080409091b06020c0d12030609051503070e090a030809120a081b070305040e07030914 75
    0x4c07a016415841d0a00040d42490302001203030407902c46072801d03450300341551103100282d07206d200c5614206400300150b2119100034828030213180084440041ea0701d05600c2c24000c203c001d00310559401c0c000703000305c400d08602c0b40604401000294a58510601c0170316085025200d001710203020b00e645060580b04480707064028110040c48007400200300c0d070398407042048903000200ea400c0b906501c4030804c0014240414240d0b0054000c203022070402c3d40d1241d0987c20303241c2600c0e01300e0342c81250000c00e1808225410469010700711034000341005055a2010900c02d1420880142c041c03008080d01d010703141d010380e04c044060180241c007400140b07015442c1c1d4000389020310340d0074024410f10000195060741e01c01124040c01c038080c060404007200b81c400b164681e2020380002c4890040500c00300380440d41c00014400c2810b41c2e1502c0b00945400c2500d40202d055002030403068207000c004c030400082e40403040300c094580115000c01c007a2540c4104070018103180c58000d0220244801c4201003900c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 921420377 1250 921419127 921419131
    0xd0c03080f1c09080412020a030206040603020c0609011a270a020714060408030a021b0615120708030702010f05090316090605011407061e02030c040306050606270402040b0d0203 78
    0x140540b0010480c08070307401411150a01009442c448090105224644005440b040d05500040480104e11f072241c00041032580107900502c040390b4005a01513402505204040c0c1c001000f1008004501d02c0101e1356100f541d145908078410003442103241c1c88408019494006482082e614440a15102e10900000e501c00d803403e4800143c83c0405e4808044002000b40c4240d85c00000c0b90708544070324012002035000300000306000e07038006080241c000130410026110707800140214507441c03501001d00140e081c0700c10840340180c01800090007103103000400c4a0301980c1c28a4581182070000e0400c441074081e11030002d40c1030040e4081d1940d11100300002101380c500d4100100090303641c1b8001540d00c0208040302da407071800300384440340126160707a205004148400e1a140070f08208168040c1c200c0e40101c43c032200105020070107105210192007403a80c0311006991851070104618441440c218480d80282001c000f00c180c000416190358040c1c4004051240034540c640c42c03209242c0d0042d402c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 921421627 1250 921420377 921420397
    0x40f02130c030506090a05041709060702040f06091b08070c02010e0916021018110d0206120f01090b030a0b070306170307120c030f03020d0221060a0506180d0c03080f 73
    0x2e00300450344041b440d11800b0300942c1c0c4078101503004030b42564011195004042c40c2a44031000340072180240c1c6441c01600c2c601006034000003146402c0204c207604440c3c2c9183c191038582c4d2624460f0031a00d41004007560000780c0c604200c182000c043c401259417440145c0b010341c00240907014070003e025290700500003102d19400f5035049a515484030400c5071100041c000c403034600d02c0505404541084800c58a44202400024048032541c011495a51001c000300303000e004041b041181c218000702c802c50252000c5001800102425070010360b485550f100041c00b110900e8002c905d10300d001c2e5014800a005040350354000d81c144103a13083c2c032a0003030709050f51800c60415814580c140f01e03000c103498403649030710385062003509075108038000c2d001300e4411901d142e82004401000d810300c1d070144200c196812030044652a090082c01600c2c0c2842e48128001d03101400601081003024a182903000b406981e9000041000d0404403480306090b84007030b05880c0c00090b503100402c941c40092081c098 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 921422877 1250 921421627 921421639
    0x2070306020f09061b0c0907092105120726030c090316090e070e06011b0c052d01030504020f040902033406022b0e031203070f0e09040f02130c030506 66
    0x209500740702082c00e0440302c4800050404609000180c100321a102b080541d40c900f48184607101e94505280012480202070f81c1c4038007150920410000d46030441400c0401d00c11110318000312503402d1000c1c000502a892000c1000c0b8078070040e07480801c003e0b01245512307052005007540d0364451800604031490070344454041d20501003071855054400d41e0180e94180d680c0c40560b1004100400b01082191044035902000f090000ba00d90300e07880c40d468511003055a600c00c80314031a000004200348480d48031b0506007007604000241c0e899016500c1c031481d05030740124410500703100080c20508c00803070605c0551303210542d00b0f1b1800007042921941d10f484080c10303440d0a4440c1d400366540c0c40c0c4079988050000390079140140109044105e0441403086050a0341c41c5010303200040d04001d050a1482000b44010003000305c0c0e0f41d4031400c1241c089880741001e41100c048140451456803004002410700021000300e401151140c03440d1400c58040c080b401c00101c025071000402814007961104d01c918 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 921424127 1250 921422877 921422893
    0x807030f2409110f0412051504030e010f08070903021c02030601030f05120f090607020f100309030e1509060717040b0c0d03140f07051303081e0a02070306020f09061b 73
    0x940c0c004480c8844101302e0307900d003401c0c5445202c0038014508041103406018116030500141103000080b40254800d0321004416610000010101040c101015040000b41014812000d401c40211415203805949601d140e8026140c00304141440c02e0000350544203181c00041401b0795052215040c0b80b2400617a4a4812200b500100318021850b0070510340804100301003ca00d0610024082d051014107042c0715110740000156160f42582d0071480441c2d1180650410160321000003070b0302c020100d403600100085081050014003a0b82411809918000760240c144079030100b8047c00465a111800d507110740300c81b0380c0715803500000c126246a2003002202500765000340107142c000c0410541c29002d95558201c0341c014024054816010300c9800c110340b0446460164140380590700a80c1906e0703030795803c50080041d03500c0d48000c4204400c018402c000801e41e0200702c90342180c2e00a4009601d4094030403002041d80f0524107100d50003000040c0460b038603224140200040700040054407420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 921425377 1250 921424127 921424151
    0x717030d06080c1c0510050a0f2a0c151e0606030504110402070f0519021203070c06081005101706010c15020a11060702010b0910060807030f2409 64
    0x40d2000c030008650054007075184c01030044880c040049003d010303804176880c44042c09042000c881c0141c8050025076210480c040c081c545902421002c120780c51008000103a0b56244040340c1c0000e001c0324010011a800c0745070921051640030403100005600403c0751284540582031041e0007010f01e041414180782001450368080d11515100f030b80c00005000400c4580740800c0000c2d4071400c0c0840e041542480224045102000f9181c68540803108081c2445040d00410108501481c0245540c2d0300c108035440019003511001da04a54141c1485000c6444810503100e41c802c168000581202c1d281d41c0c11117107560301950403d0325128410340300708180ca0700303401164a80f040090107004081001560f02e030602d0319078001c111003032061900405410082d0b03841810302400341c07210b00050791119a0252249041041c0503009120b408090306458079028001d8110400248400e061660364030325426841c425411403280340340300c6004032942070500c1031904510712140c081c0c0798105203068091010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 921426627 1250 921425377 921425383
    0x1020c042a0e010806040b041e020d0b03070b0d09020a030b10031e0c030b1905010b0703020607020d27080d030f1a010e0906041506030606020606101d030717030d0608 73
    0x10300c0c0044e55403042c0d641d554020b1102901c4100040c41c0c00a40e100250008803407060728541c4000c0001c0e002603070b144042203078101911041380340c9a1013508408010404a00c0ba0000c80c1c144252131000418002120b00000305c40005581c80036012020329170030010700c041e0000c0e07580103903407140403400e14010402900c02201d000b11030008140c0350b0990b00601c04102e035110b0b0b540e84140e0078a240109070002a11070020b541003a03001450300d40c80440c90004251301400f00d0f5070b0160091008000400404c0002048801500d0807a20f208000b12110100c1040382c0c01c800f8060300e4107071704a0b111924110001030043c0700c45100342180034500043c001c075007203c010f6181d07855581656280c260250100401c00c182c640580b0301541300750341e4980c0c450b00603084240c00006040c2c0b03840005044c3d01d0305c1d40103400e000c1c00501031442a00c0c01036010f00e405411099190416084030f500b2510702c5400c0021900d0b000707507500103942c20350b041203000030440c500000070401400e016409110155890203031660b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 921427877 1250 921426627 921426647
    0x30307120f0801090605091b27030613080f210f0f070f140c0a02040c02030307030f06030f0b060103090c1202031608030f0d0f05010608040b0610080c0901020c042a 72
    0x780c0725035140701046074400342c2d2008d41c42420340b641080c7c0c0350441c4101000700250810750240000a050707010440940f400340181c550002c0d44000c1420307c1c500c1a07032102144d104a03229000d42d00f02c0443d01034a4034003513402003000000b4281881c0c1031401c00e4140505030010440e482c06103804900006281c05102d0304641c0d00318070b04c50b180c4040096005441c000d403a08006034420141c841d801c00a000350746c49008445d000d240302c1c0c0240d6901d050601004058904189058460354244441040043d80a24480f202541c0010001c41a51100300c0100e015102c540da01500c003150050012904c0251140b1030740700c45100b2011900d900201d014400a10383c01481044c440d504188040e03c41180607400604a818548500194084003540c9281c1140e80a8001c840003440300000c100801c661860015040ba404a230820b08104c400c14000301083c0000f01585d848080104400c180b9034020440c1c0a20740200510038440024200c1c100c0d4820942c0103204039424503072440c8000070078000c1c2c420744 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 921429127 1250 921427877 921427879
    0x30d17060f1c02010e13061e08070e06010509041b020f010b18071803060b0a06020313030618020a1d0709080c0904080f0c010c020706030b01020615030307120f0801090605 75
    0x1c2d4064440c664124200c19054050341802100203102c20555a105100c05a254039103100182c80c5050101018900c07101c111000b508141440d800c2c0020000042c5c904100d03072a600300c01c102c996032000100d645010b0b0091041d04103061203601c0400403110b04581280300c1d419800c03100100d000c211a182a1442c0c3c1505d150000602c180300d02c080c2c0082440d90f5880380c43c0d401c1914480300701812000e40c0c075000354420350740c1503550724040e0002c2c584651420b000b0280f910007141818401c038041390926001e4800140b0180e075032240600d030f0140038081001d646400900c01c0011359902c4030403804032188064075a0b0b0490741400041c840324051440c2d081502c0c0d90b0001440c0c10040c4509200c060000075000b0b450724481407210800710781c00c0b40014818100c40d60000b045038008203101a00e000d1081d00f000c021300d414100800502d076400900c1503446043c0191481801c1c4090700881c2c114071801c103000c3d0800d04048203240510390000141040740c3c0e0107960702049a80d0f9403d003003080b02d01c240116 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 921430377 1250 921429127 921429139
    0x51003140c011407140a060c090e09031911011812050c030304120e1e03070501021c080406110304080a08010509010e07030c1e1205150a050607060209030d17060f 71
    0x2107107500540c0f01c007900c02d0328801c0c1201520010001c0700507151500c042e03c12501d45844510031814240d22150301c1d4014142c01702d10451a0502101d140d489000c2c89050011520200411200d8103108a00500411504c80d0081001804109a5601400a902098981211181880c0d51240c460f104880759118007a0255045803180d9942180e804840f080102c20041f2805104d1003c0d41d61460307400404030101928032810604105150034545998070250545d088003440c0c902429510b40018210b403041d180018090f5100e1810900411000f40c0019001c8408800c100401100314010b001c015078603112203203213070b980382e04011072500d090041c0c2c0008100c2d83d0100d011a03001340c02c070300c18485160405410079400481e50072014445100320f48002031848580d0304a6040610495410514003010100b060116038085440c0d41c080c0c3c0301d0a400303503100251510a102503a4183c0d0404d03000101518806d40390890024091103075040d118000c58141008107040386054520344000706409008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 921431627 1250 921430377 921430397
    0x31b26030a080a110409050103020f0d050c151b0708060c0c0c0d020d12050d240308030612010204080c0114070f06051302120a0302070806040b0a0f02040801051003140c01 75
    0x211042d100c06016484101e8a80d80701d5400f48403000702403c00b4040590300000e1a624500401505c0c1c1940c1c0d213814001c8050f600d100001c9040484c002c00d0030030040d030781c4102c03089040801342024805c0307010704000040c410348009078140011030341c1011654802c086801039225102c000d059880354081461250340800c11603407060620001030707074032280000c062400b145415210100c00001e1440d11200203040007903204a0107450384136060b00e242c80c0c042299003605401207a10040b081c10b0001600003400400061566910300c800074082c040c1901c004d42d00da56403007130390381c3e07540c9001089070740454400140b682030b030007040065500458000328802c064005949809004110190120160280341d9280d0001740e02c60044040300004180000d1460107440c0c24020b00300701c0d0f6a0041d581e80c3d003010050002240c020312181360080d000d0320300020300680c5120100c000384156030001c000343d402c0004021190b50050242d2003140d006401036980c080c0e480103890380300c6072500b50450104116003e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 921432877 1250 921431627 921431647
    0x3120216061202072010051828090c0f051c09060b100503010f0f150e030a0c08030d050901050115140c0115240f18031b2603 55
    0x1105681d20140c03001c2c01498805140c884280740785000b10646404110380485210f503007000748240c82c829001d85085030078204030515168032480e0040f0b40710701c500000c14020310100105004454a21180354100c0751a666a021071400f0303180c2140424040b80c010b06030300580d207007d141110f19040203016883c0240c000002c64100614030000c4c10341d0455558110482c0700e485d00e07204105030b0406d540300d00d500d80d8507041030050681495080781d0032003003071204100550840d1000e20782c40602141170a019030580b6a010928003c1d05a0000d062021b01b910001041400400104480c41e8443c2c41445103a03600340f4418203861082c40744c100302c0c0ba800c64a1180c17452240907250205a44007213001d2038803860805017400d407880300780b90f2140309185034000c21020141112409540321140013070144001060009494485a104c100c001d001003104001c5180740a100c3c02c0c000b4643c4500304cec030070380c05c0c4c1c01e41c0f00d0311018014041c00e00864a01203021010f5100c40f04c0d0b50100c409504025450118039038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 921434127 1250 921432877 921432887
    0x110405131a271501082805060c0d020d111b07030308060d0201030e0105012402060c0403060b060d0509030309160e0105101209050a021509011d01270312021606 70
    0x1040002c85401892140300f458850082e40750300a107408401403440300c04a031000c2c80081030700311200b045c0150300804034000540c0440e840b0b034400302116040782c0740e2001c4810341c0301900c28006000c00076803403c02c2841b41c0301c134000b0142c480c0c040e03660580d201d642040900940d41d0320a40c00081d003c01d001100150b42480c0000460368903901c180340202d00b640e40c840e00c0303e00307480c800c0c0c120514101c080300700800c0c240d0030314025258448452004003d141031404000300300c1c0c8104c2c0400380034107480b81c44910480c0c440c00100c034090300044030104030301d2801e8218123459400580d40d10100f40660f144402c41242d030016041c041d283d0460b001c0020b41d2904080108000801441c0c07814030809403400c1f01d5000343c1c0d104158209011f0809070400d41107d1041003080c4104141c1c100c062030b024400c07000aa40e018142c0400307009054440010152400300585900420388481001485070464030492942208482011139100f44d85c5170309940808a01039803940b1721450f07051200303c0d8a40f01088050b03c18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 921435377 1250 921434127 921434191
    0x721030f1d062a0a03140708041509080a0b04110a0617150a0314060c1c0c032c0f07060f0f14040801051510020a0609110405131a 57
    0xba01403941859030880007400e0110850f03200d5a090703004407000205042c2c00c40030700700d040c0b2504200b86262865a6403202e20314001c901920602c070305c0f50624015264002c11116018044010883c0c4844030640741c4a02203041c120b404545103401081c80c0d56007802c00d0301c1144240c03826600c0308819813070004610a032091008042e001c2a0728200b8101186403100341107000518082e5034a403170b40b400702c452002d02e44000505030760a03180e01049040c54100700c01c61001ca40c00707081c034001306945a86007012000b402680c41d0400c0400d641507003460302640840318a54400103001d0640307103840c1400445541302c00851003418082072840c1c0c072000100d44590704070384400d02241044a508180c152154049802c40c0e003203156517a6440050081c1105c203d13a06202825080380e00c0300a504000d14002d4584035840d90080605440f12060b40801c50203442e01d103442d28015008000e41e181004840c41405101ca0056420b10f01c0764000160a6030300c401d040b8480d8031035160100c0d8100e00541d4400c46d140350 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 921436627 1250 921435377 921435397
    0x20d050708090a080a030806030c3016050315010302150d0612060902190305210910090317090906101e030605011407050d110721030f1d06 61
    0x41007040b90308596440082c1c1000d04102c8004105030015032601412045d0041c0099100390f02a203003803101a03407034060900442100056084040c0100201c1041c0100c00b4000c1403458052600c0b00c1085048100040040755012011136207144e0f08a0315001c01401d0a001c041d4000144040340034104aa02c00140150303052040002041c5544010740d101064007a4011200d0b6500c0360100d00651901400813401298080c0c55482901d103165255980e5000310034290007441c412020011003910010240e40010030003800e42015100808001401613001d030000b1035401d40400110a400008a0705882142d04085d00f03403071840c1c1b908010081c0f00e0000201d46401c101d5030400c0c20000310050046001301c2c1559072404207445090500240041c500103002d2031130b81303030144003d001044c000104c100042209040013800380c1c824045d582e040120a03082030302c40030107020108907240c09010311400f4080c0a82d54980c2603891100085034140300030525009003031b020340242449483d11100078440404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 921437877 1250 921436627 921436643
    0x2301b15030a200703090f05040b010207060f030905071508010803041809080f120f09030c0c040c03060e0f0106121107121b0602040e0a0504020901172e0f020a020d0507 74
    0xf0303070305007000d54035800900114000f60103071342c0c104010203034100d1407c003070030044034140b01458a410000f5a200708030300c40c401c2000010b0b000c10000a020303500140e80b90384c002c402d5130092a29600b802240d000388110354400501c1d4403000003003046010042e40c1c25200d2080000406600038140500070b450b0005050310240000c02071028032a003088002c2460107101c43c80c4200c0e915210031000074070710000b000c608a03034004100801c09810041614080048129400a119083e01404030010041604a601c10301da01c030302030021119680b15458100c40c22540c2d0f2000c180e405854102c1620806501c110180c42c091044100080301c00300d400d003a001c80791070400400101582100c034640c1e4400c6017602d900b40c0c0014203000000030500d0b02648030300c14503003e0040f81042e5001c960800320503c20010307100c0078202103c0382c030038007403100129503181d4407420794420005481c2d1031a030410344d200302c08060b0b00c2c110100701b180038140295820404140c000d4032201c03140a206275020360201808554100e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 921439127 1250 921437877 921437921
    0x1c03111e0a0b100f0909060f02040f09020c0102160302100c1b02131103011707080a0b0612030c030711031c0906110a050a080306011d090402301b15030a 67
    0x46880031542c40200481c485c0850505000c0c20101c0444188429119a03940100300510540c58449980021510b02003401070b5a5131081d150140203026a00c80c1c1a1451a039011138001c0c5a40019400400c11200b9401c001d242081e000030b41e010403079802100180380c030801d16800545440300f071b01d334011040d4000c003055031040002e0a102d180d00903000304418040e59954043d60071b50400045010b0005180141503003181d6480341200b03144002c25070b0b44100310b1150764050420041c01a10010200507081301d449400c0e070724100c070030b18040c4102c4074082e100e0200d1803140c4081c845120180a0895210521030900f0300c0030444d03c0c141d24540000081c4500c042e0380000400800403084998020200c040e202d05060000510600d481c040da00c124600040c0d050000e41da80210058105030304941e100d10b0b011803031000c0129520b1590103000c22081350440d030340030010003050001d12007801000c41902c03403a03803004001c1c01e83c407c0c0c03003950038540c010f000040004015500410b601242812128200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 921440377 1250 921439127 921439139
    0x804020d060504230105090604060b0d0c0303091d07080f34090e010614030709210c0b070b150118090c0315050f0409021c03111e0a0b10 60
    0x1840d8242c800311404c200101420a100c1d442a884202800f0880c000344614100b00c0b0381e0340d0348c0d070310007400180a030350ba2a100b9000582e69445480345550303200402c0c3d00b640d0780d00d0901605038401845030b1651041c1c400c5100a8a4013030320700107881030f06a40c5a11076582c5aa0001e0707820b1101c0107080c0c03040b801c1e6000c5e000c02a4044c20034224080c0188824071041581c0d0904000c121115661191213581c444000610515401c401c00000c2803036001c004c0d0f40c5a64541c0822200c00784281c0c01800c6485000c0b07500d40c1140b403001103d20300140240e000d1140b0300d41e00c41802d41380b40304000c1c01030300d005a200081196030b0f000c1200c9845c042d6051604008050400403e44201c5107544d0002c00d10560303c0002c0101c5035054000c01301c10304011000039241d0fa1400f00411078a06100404a00c99aa00c0c60060308560b50390390f40850305c002680113417004484514000d41041c0c640000e800b1036101c0e00000c0700d1010041a52a02540d08400190694082680e600c06000d84081e004a003100760400c400700381 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 921441627 1250 921440377 921440381
    0xd0810051302210f160912030507020307380c030a050a020706170a020310240315080a08070501020708030a0516021203060f0604030b070302120a18030804020d06 71
    0xc2400c01c2007006035502d00d00c984400c01c0a0440404504001003001040090b40034405941d5010742c2142040c00c0c5518a0007040340e000c049a000041c0c910b025641046c18564440003601440b0b00c242c0c00c03114295207507500c0312485441090f50641c803542e20740740380c07503c0f04ea526003110b083c000205480d8140b80002c2da0b154103540029041e2000690003098030611140d041024100402460801c3c2e041d014901100782220300c8028070020303d03144c000022034205410499504020700d00c3c40c41400c008440381c04ca00c544940904da2000000f070800207070000410110f00d4400445000314000d226885a03560380c002560400a400d48255501344114408511050004d6200e0703248200005060714064032800c00c21203203540603104545c8a002081d02c03081d500d004507500321200301c0710321042030004400030303200b032080d03400041c424204030f0148400c2a8054015281c0c0515401d420085a40c82100b0f1104880405607a00100c5190b404048040707800b411956030450700240408d611034a41e80c440d0b5007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 921442877 1250 921441627 921441649
    0x30303140a05010b0f03150a180b19090908040b04030503030a0c0e010804110a03081201052407030806120115090f0207170f041502070906060507050d081005 69
    0x826200d510004461154035201035010306060410000c6505001081c010360066101581e0480303400000314810482c0c4a6100052400041c00a030209880f450311030740301d4051540175100142484404440c61070b00c140048004043c819516070b03001e1410364940080d003034482094503c01810800400c2481040e030042000e1030103000159502e00308101d04a00710b802002c0b20004119800c2c2e209032490782c0c441074240c0c1040c0c0002a501c94801800c00080380c84c002a800280000e42c0041d40c8130b0081c0d00402c4041c100c03034085400d107511a1141110170301d01591080300d4400c0d80800c1080a0000e401444026040203019100b0301105240e59030080c21140182c5100c105030762002010080d00e0010702400c0b03087c0401c09400e50404046654840b6000c4e080716101035402070100b2003811560004050f64010500c081004519821000020f034a0781903502031001348500f0503401141080c000c0040f22055039202004111210020b002103d1a1001506100b45143d0341c2000245999900011039 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 921444127 1250 921442877 921442883
    0x408120a14060a121103010b0d06090204230708070207030f14010c11100b041121090109030f050c120409060e0f01081f020c011505130b060a030c02030405040603 71
    0x4852044035400d4a480700c008100500c40c1810200c20b2044954100340d030380409034460f56042c00743c842080003070302401485020390f4000d40804000c0080c8074072134100704680e03402940c042244d01411840b8108107541000b44d851540039200100d003a2a00c40c0b60082d61000161040c0d61002c0d489039254450100350301415291080e9606480601d0304082c0b05640e07102d80360741402c600a291441e0025120703100c103211003800d2540c0d105110403945458004401c03404d064016180d031502c01d0f5015810190510300341c40b6101e00c0501c0020031414051240b811031a40607101d4400c5030b000c01c6421030701035122030155011800f441c414190202d0003d0090b1005d00302481000c80e6071400d00713000c22016000185582007883c00c05d070041180b01030214100803060443d1003070981c81545d00400788060320a006881c1e007107610b030450714088800d40305801026100c0844000710b000700c2029505007554038128100d50300810401408640b0382c0268012101e000c400d0050742e00b01961000000d00300c40d010342c016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 921445377 1250 921444127 921444131
    0x31e070f03050a06060f0509010e040228020c060d1107020a060329060d020310080316030e120606090a09050f1b06030408040506090a0905182e050408120a 68
    0x90034203406000d02c076400001c8500030040c4924044005285e003109424103070074000700182c00c83c6540d00c502c00304103410101034029951488030401e9861f07188030903e101d1034101468042c14641901c0403c00044213440200100e0030992680701c00702c010180c1030b5205104007010001d07040180c8074601420004c1c4103d4400048035490b41d003221104019102c0e4040c45d91410020450491b07030707180c00761000b08524450040c1c99607a210214005003150350400c1140384000306145c40482d0b818203003a28024480e964024071030303003104107000c3c641c1c003143e0300107441c1d030401400640c11f401c2040076240e01c0540c5e4800480c0281a40d01d855080000ca124959540e0300000309021190b844910514102d1b001510707880d185103013a48400c0002e0242c0d005e428400c80c2c00182d55480ca076219000640503092030141080f441c2098000301d9400b101c4603803400001d0150104c442228074280e001038558010001420030a4512604401d00820000380101d6078143c06104407505020f00e903482d1b81c0300341d1a080340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 921446627 1250 921445377 921445397
    0xc0c050609060a0e071d0601020c06070b0703060e0903070f0525030b10031205090a0e0c0d0e010b030c06090d050a050d0210050601090504090510020307180504020c060c031e07 77
    0x1500e8113448030f850480700d0b1680308110400100c01c801820070f0b041c0080c00700c14011625900300403414a0344a0a940c0c0d400b203404140601030160714045240a200e80f9103080040c241d541404001da1142260340000b20b400c28059a0081022442c904200310300c00d005480c2c0c084012410100048901c000300c1d40d511341c4500381071040103800c481140c0c01c14841004d0700382d03041c60740d55260181d812140784ea000300000400c0c07000d07203502e403100c040c0007810051004052611744104410aa82c000e034100b84000760803d05074ae560b03000c062160310300a14001e4080d100111482040c04100c0e40501e08640c0c101d40040046000305200703000c0c001200784039038090000c0b05c9480100034940613070000054180c80c9400c040c484281e03000b103000b00884100344c50218a000b00d41c02d109061007800e401a0000900020400640e541e1203600000c0c80c072120742604102e80c2d1110140000c0340100d41c03480301e15907c0400800c00b00ca10309070145038003143e8a83d0303126100981c1e1100200a40c802d0380c030480420000d00c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 921447877 1250 921446627 921446641
    0x1f0c0b01120b0c030f070f02030909041101020c0a0302060a05070f06050106050901020f0f21071a060a06080c0405060c03070f3c1b0e012c0f0402040c0c05060906 71
    0x20002d03040a4640f03901403d5040030861041c02d404064030741024080101c0d0040c081500a00541d00544001418086246040c1c1080b04141681140040c010700a0300c0c4120250302c0d0000b0200140c98014041d2810074030303060019030b0541d00800041c0c0341240c030702080c00000382990060314080e04a558071103072120f40b01400680f80501c041711103400c942240314848a00304000a0740141192036150723080d000490251422040d10450749d015018071140b045040c141454110110702400c81605c0e40103031155160302c101d034030070400e90f5000c11404041104000ca8035084010b0400c20102409a0386402c3d5159521421014800403c440d9119010000d019101b0b5030a0f0700c483c4054070b94000c1c4007440308081c0a0400e040a45001418113030b500e514204060400b22414000d440c5132480f0311015611200500701c0101c2103545010507455540400c0e007400800103126008080c0031881d00e00725222507003008081c201c111100c000b003105901101f07020076020440c403809800403401a02c480e003000c0b2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 921449127 1250 921447877 921447893
    0x19080a020139110307022b030908060703020a022d07080a020a05040e03030f0a1b05090a0b0a0f1110110715110702090406060e041506050a03021f0c0b0112 68
    0x440c424801015069403e4403004821601c0895049a03048081c110300401c00c0104d81030221200d001c204100060f00400d50031044080541b410b103c200c400039680c40d0f0f0100c040c0d103d219420781c0107800c6400c2c076914002e070070002003030200c0c003da1118601c40d1021100900c0c1c12090b078086429540614010020750074100c0381400a0a0305490600555040084207652031002030410310300280c0724400269048800c0e44650461105d1840c08000e440c04000000c01541144240500c07684001c0000501d4400d910100c1b0800e038441e890743c040c2c2c208a03039800c0c2c80c640d980c1d0092a81c1405264444a0a044c0a2291400000701c141d20503442d5403e50920650300300c003135241007a00345d14180102c0300c203104400036207400c0d5504031150509940d46150200140c07685910518070340030320105100c1084101d800310340d2a12501c038020401c49070b60b03038200050342c0300301d1002a400c0034003850240e55540f48420007000c208182d007010308541c1c0465860b120310540c260300502046c1985111103040040300303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 921450377 1250 921449127 921449231
    0x6090618091504300e0f0111060a09021504030c0b0304153908180703020301060801140f07080703050a021314040f060b0d1805030c0610050319080a0201 67
    0x128022030102e0703200c0003803d001d441005c4580b10304040841800a80e00c1000d4200000e0031800a5580504210200c00d0141c00d070f02408920a1011b961413200154181042c1d40860790010404200d81e460318180e4499540050b1084c2c884031400c0c00f0f5280d08105034002e1108040d80301e0185202079401420009051003c82d40c81d0341044035030090b0507070f55584000c10a40120300303140301d105012a5461150310304001603100039015401e11070001007095042d44444c0c070076006403030007044650300c3c91010741c501c0c00c0c1100d0f00804100c100010540c070a2003039000541c00b10340800010302d0f108201c0075100e8403d9595202000f0740b4036164092807203080c2409040305a04001c201071101c2414903000403841d001c0c02c2c407000c80082d9504101d90420111030f158081c90340d00001500c2c0d03070741c1415101c96111030007200c070107100320303c03651001680d410300041614078107100300d822a0311980144c2c0c4400c165802000b208046640725090780791038041d1917a8400c00c44005141e03032440c401c40300246844100b40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 921451627 1250 921450377 921450443
    0x221a070801050d26040503060924090a060c030f0905070303141305100207031506090507080105100e010e030d0c051002030903070b04080706020706021206090618091504 74
    0x10448180009013201c1c0601a01c141444c00c03624103200e00341c81c42c440a0280350f005991520462043c407220701000f14240704030340c914030240c25404503500e80050b541c050603500e940c165806005e001c1c022880940c40223001078281e2401140c0142d18019440c00d03118407480954041d081181c2c20810550400f032400d10308180307204030501700600c101c0e091000c20460b200d03180c0a01e5004045044640c403d01404001d0755101ea0000c4400c000b03046900b006010394042c1c135480c146440b010a462a000c3d6951a040f59801400955120815041228200061102503051142001c0d03c5112a038050241e07103082c0c0c80b190303030f03c00802ba01810410300d0300040e0803240c04203a01c10014061000740100803250070750b40204042c02d2640351850301500a2140400207400203102042c4c0700704100c215001898808001e0120b5a240d0710360301c0410600460550717105601c191a40d4400080c000202078050317005040c0c006031010408c20b1075000c000300200b200d00b00d45107c1d000070058400707803101803e0992048 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 921452877 1250 921451627 921451639
    0x9030c0f071203050f0d06080609190c06031d0708030901020715081609181a03121c020d05040c030c08030a051b03160804140d0209221a07080105 64
    0x110700b00014031600004000503040103400103941c2c08010500084418060509004100305541c46071031980318102582c1c0442c090050391888403041191981c003403902c0745c0103220000858a0100250000d1140510a60b00612032110444660324240500b00040c02244080c42e600c054890009040c0645904000040d030f2103182c448000d0355001c46159801011100c06603401d40030382400b680c200d4503907800008803404130654065443d100e83c000511410581c80150481250390040507210041d0a01e00071354000300b80701e0030250311000301070004400138910005161100c12280b08040d910101e5040d00c4214810008104201c50001c0081c000c1c94058007a40c102810000b0092031841900da203844628292140030148980c28402c03a4003030455202c00c1d4120424230715001d45180c016201e8003500321501c041c10791160805612145000354020403401480c0e0310160705034a4202141c1817041c12084070850940011070308141070003c416007190041e55840c003038400800c44501604801e000304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 921454127 1250 921452877 921452879
    0xc0305100e0103110906061209031908090a23010f0203060319120c03350601091206020a260103021c0b04032a0b0a0b01140403080307090e09030c0f07 66
    0x135490304204145003000c84000c291601c4440014400d809440c00c0700030013510b400d0901043d41e5001005102c0300c0030a800c615140076480209588008040354120f455801183c0c0d220700049090801000059501e0036002480310f0008400b42101c01040f0014003c0758000b003881b001d03242c200041d405c108065a003018440369950303a0106248020a82c1c00c0a01c140000680105070090b01c0020980e0008041914000d0494010700c014041200d00d02d400448200045003040d4412200b040503100510340041110020340d90715002903200050450030085001005041d885010102040c1d958100100f07101d0340d41513004020350309110700d05078018000b0080d00400020304001c1c1c000d6204e90141001d80c0b541e40030303541c8840400c00b4105008440002024540c003005219031480d401030701d40136000c20812480000541f58404002807000200e0000e10003000007403204002540c2c40b812074074007070700b846036910452901c1c1081510a51080d410101e218400b075442084403065484200008028031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 921455377 1250 921454127 921454133
    0x6040c080c150306040f0f1a0109060e2106090708010b09070909180212071a09030a0b132102010c090b030a090311060a060f060f020606220c0305100e0103 68
    0x30942c1c05074902d58103070080000b42d0990354075849000504070701c070000d2110f1281a4207000c02012074001d862240c2c40000583e1805500c541c07600c000741c0b0780a4686544100ca940d0410050b00b03049400400c0d0b60346161000c21444c402480b8050003004c00308000d0000e60f081603c0c60b403c0d00c9941c1ea030b450203105d40174100600e0701c1d400014281203801d0240000b6240440012080341203c40d51000307501f003e00618452590840050144211a0340100703242c4041c520b51001d544e01c1c81001d9510b41d040c0d12000c1035030003041c446002c581d0070640003036001c07038220015501d03501800016540300c80d001c110300a01150454080c01113106ca084640f91400841e402c1080411a0780400382010041ca983c9407407071801c05018107198101030160700c04480c0285480c801410103410203001d9a078a1028100c40003448502034030b600c0d42d802d00290040c0c161030362148140038501034079014107041c48041c0700d4010161140c601c6284002401c9580108051601c405900b8219140d540150f4000e22018010808 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 921456627 1250 921455377 921455389
    0x7090b06040b160f210905090402060a021c030621051002090303090406032909070509150d150b151207050702060301090204140402030f130c1706040c080c 68
    0xc0d90742e07902c481500e9012180500c94008100390000340311096509414003031102d291103200c0d0048040f4030701803c4071040c5404607641c020500c21035405ca840400440c00601d4808c002d0452618184100da00e5201610801c0c501c82400d104401e01280c0d640505003c0b085030358485a640305c485003500c08013080d9996401e95645c411504040d640c2e17038046800c0301f45036414003c4036080d940091040c088651070b420084a584841400b00c400c81030b0000c000000d903503014039058461840000076005207403078074050044041005250326600308803043c204181d9a1802081010302d40201c2041e0010410f03a500e00c41242c0c10550f4292250030300404254148843d0011154a0110403c0580080c5c403020003d48482c06450070080d0301000103c00883c444072540d003e0300803149010132100e40007406009001c05c80c842900d1001d08269120000b661002c1d40d0f11081d403a0b10b110340f5906e4092540e5004007018514420080c007202e412060130700c4188034514400e10041d02d21f0401800301c01440300c0009003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 921457877 1250 921456627 921456629
    0x402010c06090c080321070c1523070503040c050f1e130603030f1202030402060405100e030304060c1703070e150903010f140f16030f0612050703020307090b0604 71
    0x481074440c02c01004100c1400f01400042500000300da88520303600d00030303407074010903400300b220744c0c1c5290000a20b20501c243c0c4044881604107030519030440d801141c4038054120800510080c1c1180741a5a04050000501e9480b8212507a551a100d081c5460f112410241c240d01240c0b04151170a40d40f0541d40c1d5481650342881031080d4440f513114040e0020038511040c00f0f42050b00c440c502540002419000b90405418450b40e40d601d4042e4107021807507000701c3c001581c01940009050209000350b0070140380d0240070000909146600401c8400042d195520035000746000031000c01498041101040303000c645182a07924003410362400d00d20003000c00b02c5a0f61028419500c000c00c14030402d1002c0d0072600360280c06002401140e4448032602c0c05010490540c44003582100006021100030401c813074090940740f004c0601c4407009d07941c22000341001d60600700c1125030b10380300028070b1940029010b075407c3c440d001a250b82842c0d401010304244040d800000d01d142050304080c2180c1e105c2084034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 921459127 1250 921457877 921457883
    0x31e090e06061e0a11070608070e0f0102010b12011b020604050c041e0c0203130510080601080c04080609010912050415052a07080d030e030412140d0c060b090402010c 73
    0x30b4850300c8003071441c0251075903c030f01101018070008200b00c099603c00507000d6036190750f40440f801e2603501d95046801d800100c88000004003800410b001a00e041016012454130510000c64201c061500040300810041c4505599a42d6050100c0c1d00d0011078444010074013517400034080c14074054131031545848180d10440d216560b0b8084401482c1c8480e020300c03250451039042003000d03d062800281d42c95110241102c020300c440600040c05251028080c80011401c1d81c440e000368849600640340d518010341002c548403c10b2002241e40c0500b000298407603000c140010034100d406041110321080c905201604000c0100005e0043c68582d89800711500000d1820540d00d40088507a20f070501c5600c9013212030041c40c000700d80c07500350300041c07014183da61900c25600c100d000040c0030b80032102044c03400c140c1500f060004120611803c030942038201e024404074400b9103501701c2180d040c0401c40b070b24030b008a08010700480600001d8816213182400c01d45a900141c00c140d000a0287c8007611801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 921460377 1250 921459127 921459139
    0x2010b10140f0d1d060f0c0406051b10090606030c050904020904170909090c0f1f180b04060203030a1112150d0203011109190e2e03031e090e06 63
    0x401c40143c0250f22002c007800080e0105070a00168520050f00c0700350584400503c03c00d10300c080b44a400c254011142110f940d61a820702c1d00101c0c0c043c01300c3c1c1c54003030241c2d510f29000d0035900b890b0b44000d074003945414621a8800146240c1140787c48403004800780c00c55405426844204001a2103440e502500700303802824103000044001d40100c803600c9401714490700700b0865824086108c2d00006d4448400748111008000c0868440c1442082e40d2100c3d0320824920b04d0b65a450311650080b181080c1c0035a840710f05140080e111501c1c403003158882d134881c00050717000100f00041e065052180441182500b01500c0c60015440c410719a1050301404410301341200c0380c09442540e503942c4001d8075059001d402071002c00ea0800194503160000d411042c010a0600200e600200c995039260094031031568040041e5198803a900c00842c5001e0402d83c0d03c5510000131070f070302c1d010703402c070b484010342c4a95104200b070b00d0b070320307070001005803440d60180148403036034005000303444490700050751004080e20b04c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 921461627 1250 921460377 921460387
    0x17210304060207150603021c02031b030c09011e09020c070306020a17010308030105040b01020a120503041b27020a0906080c04050402190f020d121a040c02010b10140f 73
    0x41c1c0001d00c90860020150907040340c991002150b10380080b021a40211411031a590714500c103072182c6005414025807540140ca038030041421903621064125001404407110700c0ea0003c089131025a00b0380081021a220b100c00e90b0703103000090b8281000d8080c034402503051404180b4156940c15040c040104079940201e40c28414610824011144510101c03050380c0d40d580d0380c1000c1c8a08d48c001c0c010b032030149003000d181822075400090603044166211081000318507200e039007101c0542002c2d0080316032500380070008400310112294100078007104821407542110b41007104e00e49003900c4004588060040c000480141d40014001c400c883c41400c0c61403484c3c1c4c032604003010710b101302d0b08507a078864804580c07441c0032040301000c054003400c01c0d11040440e01043c0416030381c0b500e03003445550014034444020001215560050304089054080c03403034111146000013005c0d10102c81580c00140e42d10510715816152a249102840f1414180a00d401008428071206441000300b86401342c000018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 921462877 1250 921461627 921461633
    0x1602030c1507050f0d0c1206030213411006050a0c17040e341803141005010e090d0e0a120308100b09090a0f060803040f17210304 57
    0x300700d6502442c0c100302c00e90b403000304101150003045101745040c0007034070141b840400102c7d9446101c0580390002c05c060384001ca040d42c0c0e90090b1203008007042c010030070f1450300d015040e02d00c20701202c08581040036503070510000c0900c1a46200c020482001c00d0f0382d909040005a41000803140c0c5480d0510300703858500c030030b4107214039400040e00b0140c5150b400010005480c40950005502903c400c3e48922440301013042102c103405000a484520a214522008140c3c2c0c080d0141e41d107440c1801d040400141d56035114201e421200940c0101a03420540c5049080122449614050314500b03140c1d0321541045213060307994800e090342c40801e01001071302d58109582d6421f02d0000030312080c1141e0312890030380caca030040580c20b040d03800300d5504482d4400400c0005055060700e20710072000e070500256503203130351500c409055061300408900e60744100101d802c11043c40204090002001c841010516045114824544000e030301740d425045182003591941d040c074800104111450724294494035241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 921464127 1250 921462877 921462887
    0x2030a0506100e0c070302062418010603230117010e16081005040f06020702041409160f030f032f072111060d0f141602030c1507 57
    0x81028005114510400409601e04501081664201941d000c0c5a842c2e19040d410140a42c80e8014050303000b4400245009603420502118000d0076040e01c41041c030708401040c0c1151901038005e0192400e440107100c1d01d605409081001c1014045c40303c00d07103012040b21a41c4a07010300800701c00f8180100140d070003003000d400604a2041d50001d0fa0358440804c076882d4215000d52040d40e50034090780305407500842c100d102e07040c8a2504400b048081401e03613600c480c029441910126406607a07180d4442507441c4981c0480d2055807003a00806007072002c1000c02d800b1040550001c50760181c158024000240200b1020f5681641400d116135401940d080c007041140c0e02445596a43c0609400310701c10280000b079680844130207401140c0c03000b4044010800010b1f06440c068513100d00701c80c0030b001c0d508242c8010710408006c43c800081c0c00418460810070703103c10100c002c0e000c40700801400525400301d515801100e12a00045180885414031a07865a190003501c030308450312200002c0580c0d0003130f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 921465377 1250 921464127 921464143
    0x307090c0c02130e070b1201260f0604020906040c02070905060402160f02010f0509030a032001020409090203010b270402041803051206031212063d0c0b010608040203 73
    0xc046400b41c0201c07200a2008011407074100e1000e102d5170000042c208030040481d0030300c51a001030b440c40d40c1c3c28080f00d03d4a40c40c00e90210181c500194080888200d828481740d0000c0b454030000e071100c0e040c5401041142c10006d00881c0c03141d80f5240c910300c0e03069000220582126110319010581c2c0e910744000800a0141c1c15035004490410911a400c2084001181c0b4405200741c843d45030103000307030400700c925000350010b0540603408100e04201190061003240c0810742c0c603d2640a5031016203034200d0980e00b003948014065500c400c18441145000e004645174007505584440c4400603002c207194000b8000320601c8220390703508001c5015910365402841424803500140c10f41140d42c1d00c2c3c000d01d83d51003610035400c040c104034041031f0075250102d0b103104c400401045650400c90403109190140d03070054101c0c0c0e44800e040c40301040a03e120350241c6007801400c4007558040d4091a208000108204024030410182001110000e04030b84d14050658040e850a80e420303541d5031000c00e20341518 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 921466627 1250 921465377 921465379
    0x80912160f080307121a22090503040f03060b0612060d05070e040b331003140408041805040c090e0a211805210a06020706021201060e0307090c0c02 65
    0x2c004100301c3c4540e04449002c3c868260076130200b00180140154a1000140c0c908140e0300140300716012480c414030003500148448500000130744c480582e0fa070a861680141d12951043c0e6281c0320400910489105101d1813050584a0f1494204402c001c00015038000340401c2c80303080002c1d0101c0502404000e00401340214202480c0380d401c00d8104071101e418120380c8109103400e150711241645410360182030481100c0310384459008001c40030401d0302203c0b407510700105580c440342a8503600d00000c540703006a000f9990151742e90300f04a0851845d0102026840b015070500c418040018000303040c0300b080300c40351000000c40000c0780e1515410540100e0b0007800101c00603035075042d4454140242104d21140d9110280c1c44e070103e0854942c62241c41c03003003a5000101101e4024040c2441e50000b0700748007a281035940040c0c60b50f4540003280c00483c81690080c1d4040f4601030390403681c030f118901400300d17800c2140b0303481801c40000303a5444503401284241501c881102d5013182c0610701c03200200764 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 921467877 1250 921466627 921466643
    0x70b070f140d1d01091505070e0910030605330409060510050307050d0203100b0316030506040b010e2211060d0b03070e062b15050601080912160f 64
    0x4a9460410041c0070040b010b500b4003c000c0c1042e07034403000148a08508140e100700c01c960310043c5140c8007001404000e02942c24860310b9107110200e40c2c1c0315144144107100c072540c007880103400d40c280138044650007000d400b000d0580e002d030005010440c0100c480300c3c408420134001e0b46002140410f0282c03c07814401170a190800e0305010101441c0c0c0e058409036034059040382d5080b40d0713035020000300c000c01d18806901500240d01c41e0a070400c898006000464000d422140039100c800d1008591496a40c0b0a4619800500c2848104030881124a0040c03c0ea038001d10041d080900027681c1d00340450882c01c4940410805440030000d0b01044642c81c28001030001d078a9500c680710183c0640004601c0c14440d000e02e1801089005e6102c042d50b0155130301034186007091800520095080d024014044108c0035004600070000f00880030000c10708818220109250400c80c00140094102800d4201260403503c0c07403240040d00e013002c1c0c40c6145002e00384944654800e04104ca002c228100000c2c107118 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 921469127 1250 921467877 921467887
    0x140a061d01120e011b030b0a09110408060403050c060f0106080a0207141006050102010509011109061b2b020c1f03060b180312040e0402040905100e0c03070b070b070f14 74
    0xe906501070454406040440417140880707100407800c89400300841544904145014070082c0c0039070b4402c3c990b240b64001c442e0302e415141c0e50252300e130181c103c1c0c0803000950000b9031a61201c8082c8a1036821a4648aa480ca01d5040101c00b030103151005107903074101036020400714144102c00c4007258100b10380c142a00da81078624500c440140005004185c0950300300310110f01c21807014824040c9418800e01c406003405028000c0140590268208007422113808038000f8a00c3c40a10041104c0101d452440b0302c8200c2e0300858115840702c030a008030075900300c4880784080743c6a400c200140c3c48200042c070700c55101e100d80d059000340900d40000341071120105c0e00c202c2405a01402c113424410440440f10929900401452a0f1269014100f01c4a803c0700206006003059017100920030b105a00b82c4030880240800a0110b880500c0c0c400040d80c013000000c01641400e0207504040c04c440d4030146c4c504880380d01e880e5900b01024001c00d003002025584104d0181c49521103109030b00c404001981d541d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 921470377 1250 921469127 921469151
    0x121409030309010c090b03010536191e0b18100305010b0603040c090507200706120e06040f02030309030319030c0c021e01050d0e0106140a061d0112 65
    0x203a001160003000944c40c2c03e0301d20b445103002e00b20038001c451000d00075620f10b03800d02040c8000503092998101410012003100d0015461601e8801050701683e440c000a0b460b10100c001c1d40c80101440b9041c03c1841e1000180010010388000e40030101000b4010034038031000301c00b1811a00d52450700d01c58282c1000d05209050301c180d100b50007100d0003400240815802d40080110b0343c0b00988000308002d038555010480031185410207517018020303060009100d41c4d4125004106100068441c1c00c85c1c000d1941408801d03004450340b540407629040030061158800d1076141d440e140030b03101a003000c800180e03500855800b001190314802c40501035a407541072088208150801161808002c24200b180880c03d42c0c1c4070300f40001020350014540d9011403010190100070368040c0712418100a002c00091001103441d009041c88030301c82074000a41e0f00d16040442440090401142d481089070510400c4290b9028815803001440343c1a0a001d51101000603565410b00e038a06034103050400000000b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 921471627 1250 921470377 921470383
    0x1140f0d090c05090c07060510240305010603050c07020d052d0c1804030e040609060f14150f030702100906090b06010306060503130302030408030309210703020a0201121409 76
    0x20492280c8030b1020295221410000748201c12107103803071071030018400000451065000780da0004409008010000d4480702180340b4980c5141c0c0045541704501c1c89030304800d03071601c12180180601e15040200d41407050318110b40f48a080d06c042d20628001c8816820b01070b0502002090b030041e04500144c0030034040b5000402e41e04045c040b180e5005503151744101b420300700012200d0381c2261501e510140e58507a0300361014180030601d0358110b65600e03008a41d07040c0c1d0b4820f8002401080c0d0b04004160701e41140160b0b50842c250341c00e4043d503819610301c031200610710280c440c510086003c0e940c49aa1300e80040346080c65030311980381002e0a1140d00350038020765912111005004900344c03041c550343c0500540686089209000004501300002070903942d51000365500c0b1407285c8143c92400e66550003061445d0000e840005203a08044024075800e500709006503a0850546011400c1203895100692a004146006030621108481014450000e540450110142c8201828040c24400075043e6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 921472877 1250 921471627 921471641
    0x140a0f06081f06020303060d0618150b0103060803040504020a051c14091c08101d180a05070509040c0e070903170903071a0c0d0807030605061801140f0d 67
    0xd4004151481c0c11101002d00c69820784205400031450364980c602841440d43e0a103400303a0f0045e6980d40100b090312040b540d00200c541c0101d10b0b1014900c8524030070412580038001d081c0c18185004020003110a010007918115003085600585070301504c58140c4541c80740102c54502c5040e040c50301510164643d200b1034005d5000901200182d4440302c1032555009051641c1c250f80c0000700d0040c00e41446440300c141d110385e000e0140c0005a603100d20010320039001407120300d204c460400402060300c0188007032498910007040101080c072076980b902e540300c507400d0282600070300d404030004040c0512880102c004081c00e442c2080d070352510480080004245020440758402c0700700c81180d2143c030361340c181d0b10300b08001409042401e1030600403026400070323001580341c41ca60601030100300329001c0c8024410404181ca80c0421440c2c8040c00034101e51081c1c01451180d4018401c1d80c5856000c19803000c20712601303080891040c4105000c4d000b0354025809120703500607002800010442460304101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 921474127 1250 921472877 921472891
    0x902130e04030504150504051804020627090f0705070816021f090b0c0c1e0907180501020102030c0a180906080d0306080c0f0114091e130510140a0f0608 67
    0x10301e00f0b07880017000b1a5540302d68415070f980400d000b014030b503c00b441c0051142c3c009200418840c5072120145059001d803170b0448000150360a1301c07403c8811800c2c065002a8895160800c0381d0051611000241240c002c5100262402001040406203224802910030b034660700280240360000e0b2511900000c4810116200b000070983c800004d00c0110039402d44401c100f0710000340580302410783c180801042007101d080268601400503510384e482c0d1203c007a02828007642c40b00005501c1c98000c400081d01680654110783c0b0410421285201e401d059444a0b601ca181c03004a20500d000c03d420b02070259045041d0700e9140081c0004d24250006000205041c03580b000d001090b0345040c03c81e21030f80c1c1c0402c2d03181c00c044070b40095a85907215404d802c146918143c021800c0c0441d480101d55000c01c80048401014030303010140200e49049070910581d00300c00b203820300c00c40c43d0004408881000e01d21403040401c128503c0c0d81c081e03a99242a92000d8044105000590759407144024003030310050f1141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 921475377 1250 921474127 921474149
    0x1111315020606100c080702040204030b040215030709030209061906020714030a110918062701150b480d0e06030c0c2b020c03070902130e04030504 65
    0x100c00300d600204100d0300c02d00e4010030100c032404c0307800016100714524100403104a6000c000b11801a41d4502c05807000c1e60052403000c1e21407400d40b040c05060a9010480c80450400b482080b548aa10820f040180c0b68103560154250326a5000b042c018001d00e900c1140307191800390b02080c0168006800c1080722107032802c003200404820181611981c1c201406031a41d00b80000300c82841c103000407283c0d007101f0314100c0800381c0e480411209003060350550344005441c50080a11060400c001c801414600c7c0100082002411200c51841f07550030a1080c44c81c64403011401003864181c03070440d020820710501d480790040013494503110400400711002c154040705a801030588110000382c0c0b1400010030b807601001500700004015043d04014140a4920000c101225002c1020301181c40b10100e88001e03c0121610642e050b02482442c1803450119481600c600b41c02c0d80d800038801c4104e07141d030a4016541e144058030b181c0200e002d0f401c441c2c0c1000c400b030240b000b0594040000c001b2180b0043c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 921476627 1250 921475377 921475409
    0x130632060a0b040b16021027050f01030509030c010e0105041a0f150d12020a061d1009110315071d09060103020d090510020d050603190b09011113 64
    0x2000044602406140303074400b070910060041c009600002c00c4e024070451140050f0031016800110241195414030300020700c00000c0d0b0004800454020014010b8040034003222420300c0f01083ca04c003603400d1101d0400d510340002c90031440d002c1c012034103c072800c90001e00c0052501c140050281509550490f01c0300410805000c030030070b074010b0f140e008403815980c0200710745458600d50b40724050071590650140207401c40c28006025480403400215550f0080c150343c0b6802d007042c1d0100e80090002c3d2603840600b0f42419401880414100c00720035800200040160b02401c040100c41440700009400d84642803c41c80b01c0000d042895201c0c44d910740e19800e040000f140051903906e40844043c1d00107101d03c1c0400c81c158080e402900c0c5031601c621001035150b807903031110391070802d00d03000030502a0760004410329104c1072400742d1030303201c03d0540c020081112000040000c0c0d1401c054041e0607a48208042050210300390404411460f41c03d94180d241c6118500840b040b07406031044528070855142 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 921477877 1250 921476627 921476629
    0x7020a050d0309030b04051204060815010c12031109030109030306081014040b0601110d03150e090c04111605010b040b0f0a0501030c1103030103050d08130b13063206 73
    0x760504500da140c0e9030292810302d160b03151110b07500040e00448603802841049880c111011014000408031a07840d8941030030042c01c44007662488014031410001e42c2007985000c24940d09407030802c48d00c2850001001d2034000300f0007105001d10f034452a4554203040c3c191040c140c0c1600300300180c80e22a81504e00207140d0710b141070210742c4428000042407400c0d100050110301d684459640c0640181024540514104015424039116241d21004656a900c49600090b80584544090034209004400c4ea040c41d5510302d80d140d03031004410f44900d4803406050042c010031402c0d6034101d1400300f90344c2a005c11b2443c140e400b0300100340d11580142d181190380241c1d840c04160121500101410380344c0001d08040046001c1c1940070100024070021100d040507542d0100b00540c021406140a84140c044405004140b41009484414800d80300100300340407a0000480c41d42094010300c408800340c259241c854042c002592210400754050381102280003040c1400c0c00071140c2c0049103085a9070340700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 921479127 1250 921477877 921477889
    0x906060306060e010f060c1106130819030905060c0102070b101802071101030b01110a0b010e0c0a09060509032a03100203011a180603090d2c010302091504080307020a05 74
    0x11040310054814117000308a4640903000d9282000c0c054201b940c80e003a40b00003c58240d5024848610401d14003080c1007040403030a0020072200c07541d5900c40c1d80c8040d40d9803001001c0400b0b40c00b13214880d480c0041c1038815034200754101e030a25a40320964a082c1d1401314241c010300000e40c41100000249919a400103414510864440907404801000414610030044004040c000c01d010306200015003940e11005003080f090310380d544a5510f0700019810040c8550410b40e0281a5488140b420702084c482581c00907500001d80d95a490a01e44900a81d00060b02c1c100b800c3c030400c2211710344048015488862014030302c01c0943d09404441044280000303041c12407200f4801c81e0210421000008844103903d4014050001680032480c50440c00c080006d078164002c2d102d103e40340c3d1043d0840c0211640003840a900000c0c15079220044021450381260100b0540803014101a800a600141e42e9103403000100c1c00209450001d0301d9030303250791491b6a05e0b44101e00030381c803801400800080e00e213004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 921480377 1250 921479127 921479129
    0xa0204030f08070201031104090207021503040b0103021909050c0c1c0912053a08040804060f020f1f061a040308031806072a0b0f060d02040906060306060e01 69
    0x1c0301c1c400c076800e071a898032541038000307400481c105910b42c182d85000030714120160010303002083e401655529a441080381481d900910690f40b12001e00810000c9000072801c6411260152004801b071400766030700344140c7d06a0b07006030142c0d44c604802c0c011040c0881c0086c14203c03458800329005211884442c1200b05450325044000412488040c0013850034004601c100354413500440d076610300142140c0c58010703c02000302030088900c00c60300112f19010f00e154141300c0400c1c10050214142500c850000f81700d1401550144040c08c071454682a00c00c008002d001c50f4580d00380c840c00e0404403100d68a81004090494009091803000f150f800040c1e8001601201c1c0300805915082c510740c1da5000b290030003448000c171105801c014000c01042440703058810203440c1d41703101d101c200c402441c2c005032600c0c59185010000404280d00029020140207030082080740d41c844543d950080099656a41350340000d40150070481d10508000094000b0320540348540b400340309040d00c0d6000740000c9603003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 921481627 1250 921480377 921480383
    0x51503031207050f071a1509130303151d040b01270f021c0204240509090a060b0c010e0106060509031b0a050a180608030a0e0103051801091202060a020403 68
    0xa00400d10840c0518010245211603138511800d003030550b15003014125400040e0051480724608004042070041195580024200c801d1060760171703c14141141c00600000017003d1642e1004940403410516650000409100c400724400010716100a109140142d078100d407010000c8001003180860089112281100c465400b188a503c4c8045040900f11850307100b00d9103a03081000e900009000c0a00750012001c02501581e114501407071030007a030044001c4800806986601d034231f07140740d1080440b1027844d01260b00c1186a110341c40040020036641c0c1c02011001e80000e04d8a2400e081904104228180800204002c1d540ca1900b40c0d401c0c03050740322141e815081102d035054199092115000001005081e5240742521000440c09200c145d4000c0e02c1c0104000300b0b0000b0000b89400f0700005400014091410034085040251600f9500c8408a050546032000036410b4183d00380d41309500c1014000074001251f160401607508205120450010b00462000601003003050003100e00b20f80d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 921482877 1250 921481627 921481657
    0xa200a0c14010e0f1c1b08040e011802031905061503070f171005060a1101020417011b0e0d11031204030b0f040c0b09130c0504050112110306041e06080105150303 71
    0x51175a000325501c1101101e00e400740001c04482001282540002d0405030008003249074071541844a01e1180203210f0034a919514010030800c201e12034440745080354458030702c80100f0310b030301c0e2200007509558114103141520040801005580d9030700050403003c0c403401c0d44665803243d0350080200703042d40084421500c2c1165400d010006800c00c00c0c010b03c500b411710315081c13205801d152074450999010382d2041903106030505240d84294428400c0d00c1c1d0004501c500e04805920101d40648518812091148078546548580c0d003070004034030030340e20f91400080c00d0381d9024070038a2804980d03800c00c2c0800d4810781d892000040f09004c00120035802580c0115200200901c0c141c07442d521540070011194100020038161000140381b801846030145190b1912a110740c20500014415000b60305190091030820005140b1252440101c0781c0090042d10085900308903000301480305011140c0c1040348a1410400040e00e800650159000300b03800305104041740d8000c010950789004114a40d10f000d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 921484127 1250 921482877 921482923
    0xb190504050d1b0507140907020102121b1c09060506060708030606070c080d030e0c030304230d1e02041424010207120501140a200a0c14010e0f 63
    0x64000d640b0744546141a0603000f6610f0415078a03d03003451001d5000f0301d0069810081c8110514110020503480103640c4021801c3c031480224003079840f0030152500d05c039500c1d10780c4511210b03082c03a01111000c005a03c8841c82a0b014946648002c0602c00070541c1e80d41e140c01e0105400d4980441201c200c0c582062082d0704545410082202551014204880f2001250f40000b50240140141e0031441029180007807581c00030340c10142070940c4d4511591094004020612041c0948101081c00300c000c280d00d40040321450300418082d003040f440103080340035911400100117103250b49007441548240c5090125001000283c5800d081c140c0365441c05100350300d44030b52070100c0f16401d183ca2203014811117615070756459452454800301141035840d65140c5c3d07000b12401d8007104500744c00c51610300c01080352160041e0340e4000e0b10b10500c1504070203900003414501c15481158540c88080d040415101c4149404c50002e00800b003561b0001114003840c031048500e080040707501210303100c050085500d4a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 921485377 1250 921484127 921484153
    0xf01020a03030b13090f14010c050d021e0423030c01080c130e13210203040315060902120106020115080606060c16031103060f0c0418090f0b19050405 66
    0x1400c0c280000c0b42d0448404c96071011003540f80c0c0074003240c584c0102410482842c160a0100c851007580789059121780c1008c0940061070b6120085842c01e082e0001e00584980d080719090f440c4c6840c903c60b941c3d0400d00402c0c00300d091701140b0000c0343d144194003114031143c10301c0c400345515424802c102c6400300b81e04100040c03007070071000c004242e52240314042003103076919072240b04000c4030143c80140740000a81d80b44020400140c0508211100c6420b101c0c646940342c0000070355a00c0382c1c1c0030060584d402072640398a00c601035004035010785401c4070255200d8900701454102031809100d17210056007800d038403005400f04a44ea90082d205a407000e0010b40d03549070280f002c1548a8803082a051083d24100c40d5802c41d1450480c014501c12a00d200c5a0b01c82131040610303101001d012a0641c10b0004148003c11250604403403c40d150303648070001101d009150403006000800c0c002c1d001098010112003001842c01005124200190000c242403040d8103503001250401c2350300416aa01c00300c1c55400e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 921486627 1250 921485377 921485381
    0xf0109121101050f010603091103070e1501050c0d0513030c03080a030606081003081c020c07080d08072a05011a0112020414090c070210050d1d0c0d03052b0b0f01020a0303 75
    0x180780c06495503c51440c9d44034003092416005034846c20001c0d1004d007e104d60b0880c10440782d808a0402d10300181000214689140c41e0a01c0960040a00c0b200141100089031081030301c1c4011500658440c1c08241d0780d0804281591081c01c041d0000fa28000c008102c150081d0a0b842c0039110003251000003a045540320b00003984a60940842c14403240454038202249000914184243c0d03400f07000030501d014212460319601240300f2090040703c90400c0140e5038400011001c1c4003c900b004c00c0401c0f05604261034890f404ca0713025000e5401c10f201c600c584548440842041300b4281d0352084280050001041280950301606034101051100d081a034603012a60581110525011380d180000c26400075040100c404032090125401140d90004036800d0322410805c0e081e4030303640c03040c880742101100ba1030303000d03080c40c2078410351041c00318038107061095040e144158544040c0801c2e0446100c0070101c20009000d100300081d090501c24403490030002d0301d80f6800507041c0c00802c50f0824903901600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 921487877 1250 921486627 921486641
    0xa050114130e0d0201060f08150a0f1805030304170405060d0b0307090e07030308060a0b09040911090a060e1e16050d110d0f060f050609030f0109121101050f010603 72
    0x240103a142e00032201440c0e03062061892000c042d400009003a49400c0c0702c070725014403d5100300d000d034101d489003010300b200301412594402c0b48804001030818912141c48000d0880f0041d81400c003010100c0c0e4000c006001000b98065400350000e0242059030310724102841c0700703074051140c10a90030f00041d04000c1c81c540004681350001001c1c0e680c01c60716000c0c013030129a000454515117901c604010424560080c08464112100390f4510703990a0400b0007559552080c0340003140a15038524400e002c1c0f0400c40101580450003e10100349400c1800c0d00b85c0c06403120b4064420311180d06008184121000c01100410381d07410070310100e8a561710145084204c000341e0014060103000c108240c01d03ca282d2140e4110201030407900d94651150480c08003c544d0211907511550746421002c7c082d001001e000f0000300c0d40b080792041c0e030310009040400d00345000300200c030700998201291f41d8200a2071002c5140c0c20300f5240d50340010b0389003d20f502800d80b8800d41701c02c2c52a655540040c0445403003500100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 921489127 1250 921487877 921487909
    0x10e06070e2b05010501150c0302070b07020402070b010f06030f0207050607030b030709141602010b090a021b06010e0901050f040f08070303110c0f0d26060f0307060c06050a050114 79
    0x4520a100d916440080c02c40c5030400c640b5650b481006116001d00040d02c1515540c0918201d40314865998001e50703201e4150044910803000424a002150741d20f8040342c03103075a4050000c8a0399691040140c48100b2a4020000480d043c0340314941242158800d8074a21a0094028911501c6814050740249503100e0388642500641e800411106140c2c02065038090319003d41300d1251800e004200030954104900408590419140c1e0445603103560306941c202015a1005941321110410344a14108641c030b403003094010040001440d803502520184110307440c070000e0200c3e80ea16407440b04507a0007141c008000d241a62070030404594504040c4c002a407090600140d412020000240d04c1e03040050000055400311403034005d511000e00c02111a20443d0408001d074004c041d802c9140b0100305030300559804500b10004041d90740d8a030303426010b01c1e80078054406446d00c2c1c0038000c041e0140c1110a0302d00360700703202c04504d000109220311412034951410418200420700204a1035460a840c1d00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 921490377 1250 921489127 921489169
    0x30509031e07110d030e0102070b040e0414011b03090506070509090703090204020706020313020f011d150f0f180901121e0b0106050c0f0d0f200102040e09010e06070e 73
    0x1d192030303c0318420130000c035000b074a691201080d14400241390aa880d000090340990511041240000e0560340c2d42d0002d50003246440021041d1500e40d0040645420320182c20b00300c0200c002c120b075010b500a2040d1800b4070203840059032a11010340305841000300581e004078400d00007602c403a20a038000b030740309840108090718001c01a21843d050f07070001e45140d0028001c0c66800c81c21450041d0b8032010a00302801d20502c510508000d040b20049001c030501e014510311014a441c91804001301d81c00d031000110b1f025190010703ca203006154100242030b8220b01c20b0407001c40c20740e16002c0ba80504903141c0714040c252910700d81c2d03100e05a20200141c0a524450b0403400da9002900900402c0d001c1d214550b1070a807102c4480c142c6902c0c09a40b00034018058026100410b02254007030003100c13450321a8200203124407646105504017100000a106280d40301040218040400800550080081d14000c0c401115007604842c0c44240a807151004107100e0000c00189042c11440386000428200c2d0f4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 921491627 1250 921490377 921490403
    0x100207120b06100e0f21030d05101205060a020a0e100521090c060f071406100b031005011808100c0f1103091912050706030509031e07 59
    0xc0c0e41900e00304800403103500900d00c040100a0401d1512203200c41c0d0540380c40c0840a604c440030548000e2401c4840307001e00d03610a0a0142c03560b024440901e140885001c072035a030303400c0a0700d1800601003600e441070000e004160024540c01c0940c00c107001c4581040180020f070f00c0e803862240003036000441039000d22100070814407042e51420a1004c500724a603e50703d40e200441c2103a00ca4908800c12402c19403d2120140607000c0d2000940142e404001d81d0f4507a9036490720140e80c916409010340040540d580082c1d8001880b4010400e01e019012400c2500609503d44008040501046a002141102d800410860341d0302ca40320f0301580250042c0c004c124191034050160800042822080b841e94580400c0d4900c103070302c20100100d60030b480c80e213042071000501c00140c4a01c28402d125100b0429040a80c0001c1d909401120042001c940d4800e00b90107549045501c038107091040b007012910340f00004001c010003000300c41c80c002c00098103426203045a000b121550b000310105641d04450851 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 921492877 1250 921491627 921491639
    0x1006050315060d0c1b0c09020c030723060a0c050306040b0f040e0c0f0d030804080c150403080f0f07090504180501061e090b0d020409061509021e0a05040302100207 72
    0x1c1c00c0070b0f0f1001c07001041400c00340901812500c10741021801c0180810007901c0410400a460fa00f07540d050040965244040442c0a19500032030340050000007051040003400032091112174260710b210130a0700d00310385d41ea18903d0111410315040d480030a00410000754030789082d07030002c5000c40004007042c004803840ea001c9030480d000032100014981c40442821601e00c1c200c40303145146070045800388000d0341581e5006010311800340004001c1400401c02030500e520502600b0303080041480d02003050700d02801c00900040e8240c03902c0910441c00d40100c0d819155420f2082d10514894403450a51407421b41404020440c042403400300c03400b001e1800700024001e000b644024000030300305800c00e20340140d017400c4000b82c0f50702180c1c0760b518114070b0642940b0340d8041e04c1d031803a0f0111800200c9011a04040019014807174108034021051074002c076000d002031f4003401c1500307014140c031901d4402000c03038944944111000403003c50414041000185081001040e207000f451040d51040c41c0d641c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 921494127 1250 921492877 921492889
    0x50d0c030605090d08100302030706081003120c060b09100b0c011509150b1207120b030a0803090f16120c09020304060b0f1806060a20030403020a08061006050315 71
    0x245007003c49030816500410708540c000e00450301706d17501050200792186141d00081c1d485800344102014030a0301c000141d00400040c000900940c2c2082c0c0da0f13214070700206801400c014400030308460103482e2001c0030f0b2030380c05e04100c3c540c0301c0c0040e03400c4651600d0809207030b600103403c080300000d030640d2154003582050080580c0d27400104060b05001c2400c409040425140c20019013020421200900000d402d0400a402075a00900ba41c03c143c0e0394210050100700c080c0144800068051090408820030031030000010b510404003070301910452403040090305e494284c060200c2c1124024410144000500e0030031a8025620480080070139130ba4810003032059806c200c0c0c00780ca4450343e4070080e00040c141900700b480e071300c401140c0b0021a0301100040c0960160050020750181e90301040c4264002d00680100308555581c841c440001c00000041940d40d81c401d000c01ca0090140100015100744001006401540b0100b580c4a10300d0800d00100c03401e400081580724003400349504c01311151691 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 921495377 1250 921494127 921494131
    0x11030c07080d1b1e0204111206011107030803012607030309090c030209101d0406170c0303030c18010c021201020703031413020f0d020a080706020c19050d0c030605 72
    0x81c1000e402c041100902c003500043d0460841c1d200103501d0a91070000031a00350f1203490000f110101442c040b41035001040060002d8510200486c0b40020041921602e0340c4030f0620444092340d40744500c280d00c520707241c0c076801a03120080960b0800d000510801202021808120100c0312210380a807001007085490301c43c05a0095001c1400c0c0003090100002c00d001d80b0700400d4040c2420b500d0490041c0c0406d072829510706045041121841d00203a01506c2c1c1c210341801e0090040042c400306403944044200010b524450160510809e0864040d60a01000350780c45001c0d410440c070300707019820b10300300c40c007080504d01c4030f0403c00b60134000790040c1e45a00308114200b110500040c0c94440074503010301140c11008125018102190812410b070010001892250b030b419a4804540d08041c400708940b8071003808000e50142c070004001ca411000065800f003190b405d40e00711484520b41409000022410441d0040c00d105070080520907420240385012940c4d110f54145089590f0726100e0b48120340301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 921496627 1250 921495377 921495389
    0xd080313050111070c150c050f031b060c0915070203120a020d09030c1a0904020f070203060c0703050301150516110a080c030319050c031602040609050f0711030c07 72
    0x3802810000c1c40424440c43d41805100101e080c036107025a00d50190003d5903100d07035003901500c4022603046600c942e01400c1c095a00604490460005100443d201d0f04807140240000340d01600c0301416920006070360340909d016654081c03411404805120005030600702900076514100710820046e101082585400007100542546402043c60002c1c2400180c40300c2d01d0400242000038070105c0c0d1441070180031252155455105030149502c3c4070642d01404c88030307030b40c0300c2d01c0414500802c0e04068000c001c0c091089040d501c4543c1c403003500b006a40151640a0009074081c001030040003408500404115824181170b81080c0301c2d14140d1096100140c400c480c585040c050010341d608005144101030013015000d00381180c81fa81c0413a649010341911096030361064142d0040c4a8026800c480c4454030749001d0301d80d9a5140d90303000b2466050000300301d001c0d03860f20b100051004400c0c4500390242e9400902c020498072034071401c44085201001d85440c9000410040070400c000b00090002498 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 921497877 1250 921496627 921496651
    0x40b1807021006140f0f0a05030a050d0f09080a1506180e010b0406080303150f06040906060207141c020402093d0f03090c090f0f051021020d0803 64
    0x42c2c1c11800b2064034800d034009034180ca0745019648850b42d4500072030b0413000003a6042c106800c1071100244080c03041d81d01c02c98250103192100414440041608540601030742c13581d8040800e0340700120741568142c82410a580c020a0400300040c0103c42d11740200c103580480440c20741d0b00e80c21a09503a00d032002c0b103130500030350b11640c07580c4019080c0102c8150364000c0700e042108501d8142243d8880c800180241d0050322140d070190b01590b5680c806000004028048a80b200e4944100c54001c00d010b0080201511407114002800c00c51070003080c0002d08068507038a00e404080034680301a00d514a0200c1e40238dd000d10400d4629210b241c6002910344101d582001900210102050b40c03044a0203910700c0c1203d4102515415600520a804049207900e00080c640c3c800d82400551134150303400c00c1c8522420440960600d1240380c020321105184542f08105903103801c09800d10399007281c810308045001491045030100303540301c00d0101d15070002e0600c07006020b056898080641c011282a01c0c10a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 921499127 1250 921497877 921497893
    0x140906130e04060f051b0c030c0601031b080714060a021e0a030809060f0c0703090b030705041e03030f0f0905060708210f040f0f021f0f05040b09040b180702 69
    0x800240101d4a265070103a44c200000c0c140034185081c10100040980c144038000036a00368000b00820480e110342c4098000d650041d6101d20300b00c0646240114085500301080740701184074480800ca0b0011134140075600040c0c580c000d0240801c6401c050310340410b45c0a110802c1c401000e00c41d00f00b4014400b685d000e40102411403901400110300034140900c1030f4040c0d010000c9290000340c0444e0480b0520048540b60f02807858100c0307040c001d60f04501c05205000c001d1003016a0080080e200380c0300b486504202d03010784001e1b008884240c0f40310150010705040c01100b9000e002d80c0394404640c1e40c5103840c0c4c8510761100c0114130264861300c1c0032103012400292000c44001201801c40030301c0c8049448444904214202c8004294043c001910100c02a03c0030b008010031282d003440c210b9030140c550030820a00c0d00304948850442505000450f03014400001a1072140007100c0684911040440c1080700040a0000a101d4413200f44d802c083d0b00131103006044140d030b00d858805d98581e40107207040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 921500377 1250 921499127 921499133
    0x7172407020706090515070213093008040305160c080304061403040c030618140c0405070507050a06110702090a1b0309200415080106080f0706140906130e04 69
    0x402c0665200e4020403420f03510078403642d550b07901c1c1d50036a2448043d41c03944554040c0006520001244400c01c4040e240c5150a410040e02c0550503404a514042c00e130404001e00702c50b8400e081d44503c81100103501180054002030145010f454800311443c100038880f00c196541e070502d4462608000d8040c0e10100d020042c282c0c0c000e640303a01401c04541e180e03081d030a20b555160149601404000e20f1191070326036076126400502a00c502d05600100d01d042c090040d50125a11400840103030390195050800150840740604100d65400e5407040051906280a480e0040286070b00102c9000143d4100610f0000d41d0f01c4c1b40070607015035016071340021580351040c00f403110380d059501c841007454204070000c0c0104001860481c0758141c03454a003051480ca03140000c0051a0450750010404880316011841c3e000541c052001e50b2003540c1140d21030116104002d0761507201c0d10941c80000c14a443d0030050b2a040c2c4042d04010f1400b801260030002c58405ca07041480d501e4100c038541780b103613100300310038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 921501627 1250 921500377 921500383
    0xf040b030a2f0c01021317010515060d0e0c090c0d055205070327180b03030412210801090e19081308030c0717240702 52
    0x3a06240a8220801c4480c40507190b40402c1d409118003002d4602041140c0520710039012140b0f18103110052105041d101c200502400b004016504c0b0550b1034031001039103003024241844014400101100c1c18800c80590000c094000111454550701480c0c2d0526003030b48590b0300007030051800c07844141e201c3c140c1c10700700802c40700000c140e1491506000c0320341051035050a0f4140011991401c0008056030080c1c4144190740d110310f90210752800c20341080c4009034000040d201051003555100800220000c602d035016031080b0300c00d05560301c8035500304564440c0750080119050a41c0020404d954050002030458001f5402204070101e5121004104105410f44101036540300c465020300c18103050000380180014010000d02917a01c011090740d8180c100448c0301014020204040180400e05d091096904401100f041511200d5000305820708080152002007641d000281103240c80c18005000e01156000790507402d014120110f031861000b00c1c118506040301d00424406802d02c684000d01e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 921502877 1250 921501627 921501641
    0x180d0c062703081c0b0a090e010b0d1a04030c170d060e1302100903060203091606020d050319060302030604050d0e040b09012c130c14091306020f040b030a 68
    0x1036400701d0681070000840c03680603544209103140700c4003c248015a400c1000f4405403203e15070210b4141000511009503420410031100080000c0c84864003002c10f12070f02c80d00e440d030010a180d140d128410076000b07a1164460380070380070f032070600800030b2a5114000940100030100c80e03041000211070408124500880c0000c0c80d010050001074540303103581002c2142e034070700000c0c4209082c65082e820580318000e024091600000f04558a041503c0240e03502c05103400c032105802c8614600180380c0d03001051490142d00d468865034a1540c5040350326203080c8003004c14555903940d844010026031030070405513104500c1030000380410411620702612214001c90000d1055061400711016074485000580c11680c10b5805002c500c14640000701100341d0070251000e002c100d0204010490851b1002004654051491041015100c40d103580040c03464640007a0040003c1000c1b42d2a0040c5d02d51200544e03009090060030000c4040d48124550301c140d101c16042c1c2c2000c4103009000d90540b02d500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 921504127 1250 921502877 921502937
    0xb0115031e020a09150e040f0b12070e060a030c030308060613080a110f060703200d020a0c05041b0507140105010801140f04022803121220180d0c06 65
    0x4103203440b900080c006e600a215490040c2c3d2550252650500302c0d030410701c0881001454208028001c0c907006a8a9090b442102c2c07088200c000401c20600707100303440a003581d4001040408a40c1107407801c1d1403541e0050a003035040141004074540710742d08101c60307402a02000303001d030202a245081480103901c0300702c8034501c10b800042039035905907110310444174516454200303120f41d2104207400189003903485403c882d160141004d403180d0981e01081c2c0c4007002e48100c119668103521141480126034000513a08425500c40344c4c40c1105600807400b502d01903201e118076124030103a0302502c03402d4a10a81c02201036030b448001d09103901c000c26003c15480f440e84100c8100754980303500054480c8024000c1c0c444d6071171483d00340360503144981c000340e4090360704101944810404400c2c0141094a006020b0305c000d840d119000318480013003078605000d81207002c01c5e0f50410540396101c03c20b202c01d4441c810380c0078600c425150006090118030300c0c010503490311096100d00302d01c0b00324000070203041100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 921505377 1250 921504127 921504149
    0x9060e0102010c050d0b0604180605091506160219060201020408070803181c3008060a030b06010c2406080313140a031a0402040605010201090b0115031e020a09 70
    0x30f41c04aa102003541c0d0b021007440c42c0440c04895000110310a841340d40c10010200b06004036800f900e5202e90080002c0795002d54064126582c0c0c18007101c07a0041003080c503a403121040195081102d0072940340e409a9000815401c044000d0740038000c0c06141d81e17484000540d40209080040703540a01c00000204a001d024500c1c1001e4000300c10122005c1f0b81100d4410640c50406041d0510719924440c80d19600030040146250642504070030713060300100514841d4891401081e00b14030500110f801940302805070f4606508607500d0441c5200020401c504000c2d4202403800450a04110b071648208110005800781030a01c2c2d80209840058002000f141e00821040240c40080c4a45a04071803440344807550b07040115000810b07880607507102510b003071010380524490074191003c05010f203200311800c129076652000103900fa0b80740401c0103807185407004010070401c80c55010b2208989840d02c0c00084040c039880b900c1c00d40017601101401e040d940800d43c100c8994003d80b80501a00d000150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 921506627 1250 921505377 921505391
    0x9090506062b02160b09060105180a0e03360108010602030d05091516030f060b0a0806120a14010f02030f062404090b03190302151302060a09060e010201 67
    0xe000300c202c8a2840102610781c0c40d00c1040c1000e80c6905030b50310049041510058503400741001100b41e6010383c1d01d402d040c041c5000000d030174030b014031820114400c400c511b01029074035186c81d00d0040c02084000d80090004001c1d00110380b141420100118003900140380081404039040408007400c0004141031012540042c000143c0000507101043c0f01d0500104665443c086500e06151103528100c1505050109010442e00401900c0d25843d605940c200048107030342c1d4118055501a00c030701c0800c0e5030100501842503101ea802684d0041000c3c0c906c41451506000d01890001d0f49034040e9844000c0309041040610300703001c0c0003010143c2c54415404c504004001a8040e032000d01044d20600704640c040e042d0261120b4032000c54440c03042c82c2500e0340d503210404009800461486031080c02203509000d182c1181051514207641c050b4001d040703440c03039100c00c2400d014025003140b0285000ba00c28000590380c07100100501c01182e5540e080d203900d8160080d15190161055506690502603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 921507877 1250 921506627 921506647
    0x7050d0803040f03050f07060c082413140406020c0f03180d020301090506011707051e010503090304030c1410170f180109050304030b102d0b0a0909050606 68
    0xa903030b0000d8100d49401003000c0145019a024803c010380d0f001c403103902003224400d04c04268045a8005072a8481428aa90341600030398a50010354203002606603040e0b1028050601580c804200c28001c04009080110003210101c5624219401c89841741c00050b51202c808080c4031420030722052800039400d00c000351440403000d402103034241c0c0c01031520804210070b40d074094100c1d00c0238503000030596016503114562441c000000a0303100c8464411360308006042c0c00c24a01c07840c038494190303d5940070765a480b401116264009402c200b05480140b10110108243c0307154000140800d10302c60340464112018030408400c503458010a010101041c207807800007441480e50300540c0c0c041a0b00899507004000714800030803140c444030301c0d8a8507e84208002002000304241c0b030007071705058016540d41d01c40001000b090b01544481403034444000c291000301b01c003d2540000c04540302003038191907200b040000e0300b103100c00d00c00050710001d04104001d83c40c462540c00000984003e40b400103070034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 921509127 1250 921507877 921507893
    0xb010306170d1211034b10031b030b1024120e03030f0a0213180b090a0902090601050412030503040204090503070503120c03011a07020a030206190207050d 68
    0x515076000f40046114801901c000b1035001c104084400d102403030300c1e0704041c04c0c006540d00c41c00e0303038800201c0541c8003091540c0c503a6500d00081805041c8a02ca4800c0c142e41c140300b00c000000d0240d24085505910110002d4030301e9002d400048503000c801c1d40c1492541c00d084401c1c04000d8200e03003007207101040c02d00103803150442a200240058004011441041d2000c58903107940040030352071286007207003c911401e804402180111070300340ca5011305450340c0b039a03041244108280c00120007008403041002c140281019110405588000034107107000d5008202c10b090125039454031541c0e649101c00c114680a049160401c400b0328001c3e041500b0075003509a0b060070030001400b400390200015045568a0308001d84255110b02980d880b4055840c12039501e130040e0485e2014240c1000009030394425100c260303412540d194880d00080c0702140c500c11000e0f8170010060740c00c03100c0c8020110158403400c0c003c0420310b2904118500e1208801e400905000c416001a40300e81c10866000020400d54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 921510377 1250 921509127 921509143
    0x5250c060c0c03021002010911030f1e0a06020a0302072009150402071a040203060a09080913020d060b0c0124030b1015050327060126100b01030617 65
    0x290400c4120a8214280b4428042807a880298000c103c80b10002d0269070642100d00b2080c8100d81d41b5100c0404002016110b402c00d0071910382580c04160300000070740c0c6035001041003c0c190030a595954102e40c40b18410b0b079121315a01004a500050108100010540440740c0001c0310207440740c00421080005804000103090440030f00e0803518004a140d45a40c110340d26140c0c00f803a40513464203041e02600890008440a0f882030280b10f00050b594540c50080000040e4048034403498444a842001143c00c400020241059401c0c8818100011280b04d800080c0c804d10091a403100d8141000d0b030b00303403500d0000c074040c102d800142c2113413526009406081669482880711380903070b82d44503408007840d842e41d100c0603010034200700001080d5001001140641c03000c0100b10220240480744801c020456005c0209a5200000400021582c3e41d03800c1c043c981c0c4110744102c030142202041d40750000210f118818580d803a40d1900305903030544109001000860440d101007071003505095114410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 921511627 1250 921510377 921510389
    0x9031e0e0906040c210e07030f02180f040611070218010e100503120d1404030c17040e0402010c0203190c1403010b010504030303020d060f0e06040b06131403100c05250c 74
    0x142166078a5041211b40241c0e980011000071942c505a617402e00740310080c1c1c02c02007603028510b51004008104006026648034103002442c9c0340c0b040d1950342d104801003408113000034500c1c030103101507c0180c0d240c04030b2010001c4400840c4d001d42d4181424402d440a01800f166000c000524041102d0b072404161082650300d40d1454076150048541d042c4080d20340c52400c1842c05140804000800d41c0108074404240e00a050450302c20038801489555846140280e4000f0a180000240190b110300b4201c401588041c040e03d456460900c01c84420002c9070100b01d03441c44404400b40700384580c2c07880c40c4000601c1100240200c0c9030200019001e0b12841c013000d02096000220351121400fa80c0102c0700801e0214800d4035001d590724070889502d002625074910480c1003410402051428800396156540d40251002c510351901c4494401c018400c1681e6416001c0c0c0c20100d410308055214003150f58496856042da1080d14020001268007000c1015a803035a5039080c0c40301003200b81614a060b905 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 921512877 1250 921511627 921511667
    0x40218071b082107020f01021806070f081c05090106150c030207051e011b0b0a021606050c040305060f04050307150b1003020a0e011409010309031e0e0906040c 70
    0x5802c00b15424800c0070021400c0107545240b0151260403405102d11941056003681c1006459031181e80c240d200d541c03501406000d951883d0042450301d1001400c0052160000e143e00aa6641d1000856004440b8035951030f400c403070100410702c0480c028254032282d680c000304201030929594034107030211707400003300b0000d108507014101070003000750102820f03000f00074181d40505000044844400d8131b015600290408920019850034800c44c980010350064801485544408d0703610001d40003030b188010500400c25030038001c00c0f52482040d0181981544c01030741d8a055081c400d2401f0350140141400518810400021600201c1a43c0015500480c4100200300d901d0114001c1c080400e9080d078031041ca1007440b040d441e0154002c0c503040943d5200c07150004204c80041d101c1e0a129243d000180c40108480030740341d031180d07004010701703442410110090b5500075250210340b01900c90680c0802c6400301101107a1800e6102c00e6840f8a0895042c499258a5100200308002a20360500146 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 921514127 1250 921512877 921512927
    0x90803040b07030c1415010302150a0c02061c0908030610050a140306041128020d1b03140d0e100504120315120602131d04080d0b0a03060504021807 65
    0x800e0740e40c030798407550b1565400c039007401c0029040c6c11003840c000c0c80101d2050310030000502480f074000094500042c150344606017400314039024040e4a40c000c0000c44100c01c60307080c103c0c1c46143d082c4184a191400359480b40d03124500701080c402c00c983c1110300c0d0780500005000207204c0c2544541c60b0442d04070210612610383c2c540b50301280240603107056240c241007001c2401540d500207000f10120040051451400400e8013110a984508280c036640002846031002c03003820703484039160000c6180c070900d0161079025288850003400d800c040d1200c01c41540300c4801c41084501000302d900341e0f10300c4c20404c100701c4c10b15503550400e0385080b14055040c10340724900901c5c13a0791400600002803000f0030300060b0469651420b140298810946040c609054140214256030390301000c08103040d0380502c40b003517a01c0d1034903042d64035040004510311864032103541081544482112000a40c030820300840c10703080c1031041000d115110300382040380300d80000410030702a42c0040c611010240129040040d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 921515377 1250 921514127 921514133
    0x3010e070b03150f221505011403150901060c030e041505090603010b10030f11030103050a2d0b010521070611010209040507180f03030509060a030207021e01090803040b07030c 77
    0x608401081d42c4864140c07412030550390303010410035417001c08034001c100c3c10b2a8402510300b0704c2058026a400207a5000301040061a240001d50b0030504005004515414290000780752a400340c11400003d048040120304140d000307920428501411107062240ca28805141e10f1000030912953348208900c50115032962006c0d4801646048082c5c404804404600301c0603001e45103218401d000945841c04ca15040200001900c0c1a2907000024210b4220282c940020040c8000388a0107409a0b00d04c1000307640340703d4103008904912600480d02158074080070040c0950030202070391034101500156101d10100820a601625040d00344266909a600922402400b5040c2e049070018509000d00c4800b68019240e112003000c0c80c0301c11440c450b202c0311508070b4080107201c018041b440a01c882041c514000014007515015403400504120903900040d0849118146c1c0c84030307000da111101c04403940d0061045024107000e0b0b000310b01e000d141c0503100d0190310075485d01400b0000c01075401d03010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 921516627 1250 921515377 921515389
    0x9010e0301050a20120a0b011707020607030605040b1003050c1204050714060c06070e0f190e070201090503180d0b01080601091b020a121e030b03010e070b0315 70
    0x950001030001c000724035045100f40002c0543c1c6042641009140001080d11402c0c41d08a541000249045812a850714042d403005490788043c1d41d418000b000303180000000f41c07021030621500c1164010181414401c0c030180c2200c11580289004500b03203400090f054550000c0340c1c0004010303103000180c6540788038250219008050003000d00340704000510061200005000f4142d0f0102c803100100c0600c600104503003482122001c1c241c83d00305400150b0040d02541110b44030b0030b0080e20500c0c0107441c10380020300402c3c9034000707100d641070000e80601044034a0200c0640c019102d0000f00b00303104841e04d0701035503401440c207055140c05601103010300546816006c0c0b02215400ba030045001e50711035203107075100e580901403011454034042c4c8805058a02c421401c2d031000090f00030b0007500681f9166030b401145124082020702c030782d01e111014884941161071030012886d07a400a08140c80c0803c00d400c0d1000c5600040c81c40d0b1202c1010b0120004403400c0f43d40001442c0b41c2400055516004959 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 921517877 1250 921516627 921516647
    0x90408030f0405030d02070302071a04180e0c1206090d05031014030a0f0b010e0709053313180e121305060403030509041b020705060913321303050901 66
    0x311090000c618a41050340014ac80c03000d8a1240741c00300030307850701d607055011503000ba0311800d4031042400340e04e12840105548003180d481c2086040e00d0b00340c000000030803c120114440d03000d40c1c1d07008c44100b040c004818403079203072811441c0c42d109155040400b1003981c1c0032014001c280c11400000042520307940c3c2041405c041d82d0b0700411f0080c0840050400e1180e290092144038080c808100005140511502c0c2450582d000241400c90030b0b102d440300d01d09070183c0741040303109500b2000c00448031005410040e100700e0707000d65405882c9a042070a06840252080e9002c10510704001c070000c400400810a800540c4003403101070348a4910301640004401140e1120790800000100841850ba005004000c7d00000fa50117020103040d205100058400303e22400c001604040c01c2841245844401000213000c01007440c2400184142e00c20b04664081000201c0b540c64400745404d0300b208620a010188051001c5141078a03002c10841020004540000c04000000130f110b0301983c0184a100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 921519127 1250 921517877 921517897
    0x1080a0e07031703090706020a05031b01090606230301050c0403060e1504030e040c0f020c01050a0c1a0103060c0807020c090618101403031c05090109210e090408030f040503 76
    0x50701d50101c0c41c003c038a00358420348944000f8000c440c0c010030101d00004440e03d210398424000d500d864000d203200c1604d044964134144c0306548901860001c01c03da405904060b1003c0304000d852441c1c810311200080005031a681d000e641480b0030401c50403c0d0303506480c00c6a420a13408641c00700328507482401c084a1208030442108218107110606a004103181d01005003540c0c20080350503403180550381c02c03124903009801603000540501042d44120050700e525141030074045a003185550340c41c21004080c0c4c0c00f844032042c4000040003803020038003a08140c40d2813070074010214103150130001d458215200b40d190207600ca4501081641c0c40300321080e11070305812190003115040c5409403601002d060b2082400722141e502500c3d04520700402102c0381002040342c50000c0a11040f02400a01002054414903550b11004140071920100b0350b460703003440e0700c2100041490380078000741200b04c001c01054004c2003000100000a24584200c0350441e00724841d24441d40d49901d000361540c86201541c1e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 921520377 1250 921519127 921519143
    0x504020301091515063f180203070e100902160c15020f010203160c1704060906180b0f03090109140709050f090606060f090303030c1804090201080a0e0703 68
    0x6194800c041da44601c02601803102d400344070980e50101103440c403404180600c0180c4146c1c02036510f508103881c0ca10300003022070103075910b00c0c040c0700621012114071380106114114203182000c02c519081c44040054000d079000103c2030700380311003011125103c600030101c100d60b00280c004100780341c441c80b42c806070341e001081c200710fa9140c610403c6044104140c502c09480b9043c2138038903c041c180280c074861486030410700c01c0400c80c04021078842004650544650400328110060024904020005841652521020300f442c00744014540d03604509001c40320b990117a0180401540b800440d203020301d8183c00c280d2a44c80d0040c4480c014404800001c02c0314800c0501c03401282d40200b50207089501443d000c200390340e0380000c03440410390704941811554101a000900510380341c0c02804d90382811105a90601c48014007007484c6600540f40300c011101c0200d00c0c0c41ca2041d00c07184451500030240c83c14084030f05558006008940058505025241c031044445000c44003003085d40300940e00290b1b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 921521627 1250 921520377 921520403
    0x50121081608130501030e0d080a0b01050c160510110615060903011d1513030c051509010203100603090f030302030a0e0304031a010602061e10050d060b2d04050402030109 75
    0x42110103145604c03801d40400c0c117007a030000c000c0c3e0b00424944544481a140c20a86079074002c510402072100c480d1503814013400744059108010f0800411415101190103c0002c6003450f0400203182d610146c0c440401801c0d03405141070250104095030042c02d041c0700a000d000c00d410009203180960410281c26600c1c03c5003032919520700030346107800031444000381c5410540b014400030014a080f180f03400c00051905800000074401e0807606c4007540518107403a440140c80e0200c803030025098817440d01980d0044180070841080602c280010040f0b42400c1100070480d80e1640386150005c50040c00341513011000409914107074104045044012080e03d54032030302ea107000300e410f1035119941d502c3e04010000100b900e40c000200980206090003541500c180cd03e4071400301c46000400f81070b528103c0c40740000d202d845505220011a104a001041d80984003090052042019031000a10580390010041c81c0702403d0a500c01002c06803000718680c0d8070350000c41d000d0103007000014022a9a402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 921522877 1250 921521627 921521647
    0xd120b0415150c020a0e0604270b10080c010f052b0b030d080f091903020c12031305011101090b040b01030606140f010f031d03070501050121081608 65
    0x80903005840d41c40c81540c42d007100c852021202e0310b01d03e280003500034149203800d1150034044a500766000740014804039541c940a00d44000302210348000b003194140c8400d00c2d80c1088100351031154403141480b10941c01c280782c041c08903a80c882411203070341401800c01c03943e50307600c0c410b00403600506240040202c4990b40ca040c40c0c82d54000203a40701107414501045610140340c04286503003461000d940341e13a0720362240c0d20246816503028180761002e2007107441e4045c1e00c01900b0340e00358046009801034900160703c1018030940c0c0b028042d0074021600100421100f42d0440e080c03050aa45081c80e2094510792034441ca6401800840c001500241c00502000100210300c402c042c1030380e104120500581d695842c0102080d81c052140381d501c1140c00c1d200c50300b25407040080b103518030030703614000c544907080031300f19980b8288550000000d50000600392050140c24024640104503000b0622101040f291040e90071281e1070310020b101140008281441c603058854841c0d095412a0b8078641d1841404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 921524127 1250 921522877 921522911
    0x40209070908011a031006030503091c1b06030e010b3102220803040b071e0b0a0209041d030405220203010b04060909050411090a060b070812090d020d120b04 69
    0x80d98601c03030b2046d83d510400602150080ca803c0301e600c0801103052003880020003c203000c8051514080e100c0e5480c190020528150004101420140801841c5400d00708020203641c1d42c1e11110525038140040003420b40c55519418100d00d240e031010707110405450281d20715001d6480b800b030420b01c1c008103103d84040c55402c00c0054054100d21030142481d540e030340d80ca44901851007150740c551014403040010410440f080404624ac4581c844103071913042d50ac00341c00150543c0d40594455001c9842e0041d41060b10501c1800c8812011519560f03440c0301c403c44c1c0d01e1190780961402504c001a842584078420906181030f180c8441065440390307116040040c0302c0d0854410b250004515043c0001e00c00c001d4403a03a40034541041d81c1888000c3d01d003091084511016212915459950380c0004540003c00003615401c0c1c46048142d507680f000c451110401c0d1400751811010340c05c1018081071550b000981500072201c0c1e401c21000380d007103582002000740034055800b900141050f60041ea000c18070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 921525377 1250 921524127 921524171
    0x303040b0609070c0b0a1d06070309030e0d080313020102011508060a1d060604150914010509090705010f26090609060a020f040b091908060f010504050f04020907090801 74
    0x50b5010030166580b4074084581140d0240080d2134a91040040b440195041d000710b060301c482e00e08000e42034108030420500e00541110b2071300010b0f03521440c074820994001c1119402c54411610360800030200d1b156602d12b403101600750800ba0b809550a03608590007034008407a038400400d2240040c566035600d0b96100e00c0c3c1101c156459174645466642c01703400c2000100d1008401d0801840c00e5a200010b0100820940141c88504c2078603203c00925a54140104020050244c0c0450242d514241c14000c08200c09041070056411005c0140240d0360f20608003072204180340b40003202081c0c8a0202c20102010ba85094200c0c1c41d40002c1144031880000c500d4000d05e5960121200f9559245005d4224090078000e8840000f04001c1041100403078005010445002840f5507804444596190528007042c1d0108002d0340100c42007180d10303209031500c1401014259800d00262501c007c400082c51801800280700300d2022010510b114829a80390001d031084000030003c005a05e60100720305840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 921526627 1250 921525377 921525379
    0x90203190b040204141002070807150e120a02011d060a0c050f0f031c06210c140109090203070516051b0d020d0b06030f0106060302030a0b040b0d1202030c0303040b06 73
    0x70881d400740075040910032034085507000001d0502c4481407108001680802070f050104500c100203000c40c64060620400c001000c0c4403140f0f5200740c41c4100c0151030107100c10000380c480c400701c009150107103801241c402c698a41c24640a1100152104111030300036000c0311854203c100865002d25013504107648c40280d5000310122041a1710039003801e40da0b07107120310000c800e580040c1310016080c4006124944c2d0102030000214441c0d4540101600c2c07448007001042255280b00240d409005420342040e0160102c9029000018440b40000c3c004d1207940c403582e0002a80040000c0314036110380c003550351f62200e06080440002c01400c110741d50701c0e5004031800081d581c90384011714a10b402000c6640c416030291141140d0319141c7c548045050005060641601400d0410f201501c028403c0b070010f41340c19100144c803820600d01c001c0c1110812b002c014000d910300300f0f0507803d40e921500440300303c0d0340c040b41c0054104c846210032401c500812900100520010040c8010070400045c03007486808 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 921527877 1250 921526627 921526631
    0x60e15130f090510030b07030f0908030109110f04050d03030e160915080a0f05010608071508060108010b12070306170f010c0c0b0f0907171605040204050f01051309020319 75
    0x9111282c003003c0718000e0314804007031040024100000703103081d400940d000300182000507d00002c003449000784d409604040b942d0140002c0180010452032107003003503000078800d00d282003080d050303500c150900c128000d4911440c3e549100004041c40f03900b000382030761880001e0b10f444842c512680307c1301606c18045ca42003241044600100c41190710007840880b06000c0040c001c1410b03944400b600d6916040007036912f03548902d0003165000301048082d0040c0040782200e8007145511100401010024087c2c43c100124800100004252501580d420701120a14140c05440360030003a0002c1041d40d00640007282035200ca5500c039200411030540307a0041200038404005400c104468031808500001d1035605c41d0170120340030702080c070318140d44468890300711103010b5110045561022075103001c0300303c145d0112032010314502d01090054000c0400790340560900d420040001c03403008151814504218010aa4000c009100d900c520024425850300315a241081d4003004400355407070068001c1d041c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 921529127 1250 921527877 921527879
    0x607061d0c031b040b04061223060412080a0b2110050403170c09130207022106160e1e01080708100b0906070b01080c0f0102070807060e15130f 63
    0x1040c0072801c00d0f071140c280303511010841103c5007004000c5c0f00c40ca102d0303030300140d4075840455842c0201c2c001300502402001d00064034601c600780080c2c420401034480034550040b400780030002e031000100500d507651605203029641c2e100810080240b4030745408540c080a044010f0b81d035410401003010b842000803003699440e13660100c20350244d42c02520010000f03858480003152003c60b0450058105c001d10300821320f085d460b6000100c04154074a04503008039400a0700c03404502d440403100c910110072a080c4040703016024110354a59a0040443c0d45403120031100808203441010254400c41000344490038103403502002450114170900401d02060514010805050181007260720030005082a0050a428100d03a03005541085010a030040028010240001c540170001400b8024000081c100000ca44082110780000d08041606641000006110740000401c03007209480c49801d029003000d081c6c002040c24203100300300e20382100e031012640301c1840814a921004981840442c0c014107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 921530377 1250 921529127 921529129
    0x1205040821030c090a12060f0b10020604140c03060c0a030b091014040906090506040b06040b06030f06060405060d020903071710051f030f0210030207021c020607061d0c 74
    0x386048001e92588070310510005190807103d02c0206041140a0180c81e0b1450b03a6030380c41501006900340890b41980ca420007080e80120302e00c501d82120408581c400c405511741c001c041e44403031028001414000101720040006241080001d82c010b01c084d08540c400e1410441400294105042110010341000c4003280e4610300702d03036050b001e0a8294210042c05140245100381d45903401c010940040d19054204045881c1c0d2060201d0345010b2409040da600d4a8074041c60300000040007288198940b4010781001c0e00c40b50166588070000c902c10300d199450304c0001400a010310380c00f01354060000100c140ca0003800d80c02a00c4034440950441c1e2a103504d40c0031003641c50003101c0741c0c128254002d441c83c50206080d9004113401482002411201e40f0040c01c1d51030b0442c904e9002903802c091055002000c5003060744490407107039000e103030840c00c042a0ba40001c00c02144220303d181c281d07e41c5000c000941d039485c0b04950303503d0f5000700108810311700040300402c035144c256903c003210700910304181c0035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 921531627 1250 921530377 921530413
    0x91c17070c020a0b0309120c0c10091404020705031e040905281802060c0114130503070818060a0305150909101e021321050d050a020a12050408 63
    0x3400b0340c0200041201800c040754100c0540004028203110721421408403440c107020710040601c4508800130b04155036150b41880b8146004208010420206210807c001c00f045416022031031011240503948070380d5801d0051550045650180314419500740201985034520020800c540040360240002d948000705000600600c030300c5c4a1040e14910241c14925030203600404000115401b85c106406298020031030503086043e40b01d041c0d079542c480c641d1070121a2501030b9846403d116800c80c04060030b603600c1d6168000c01d040103199407400701e80000c0110440c40381c80d5040d54007401fa41d46807591420001c010340000e40e1a00c1100c04008076a011505003040c02c54443c044290080102801c1460200020700220100368560704072030815555845c000c4c00101200c2501035403da40343d608110854002030542540d800550a42e03001e43d20005a0115220002c008141442a1541d141800c01e90400601850003801c502c000002d100d911500f02e0060026211903100301c400a102141c01030340 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 921532877 1250 921531627 921531647
    0x10e010605030603122827080c011421012402070621060b18100c06050c0c0f072c012610020d0b0103020a0c0209091c1707 54
    0x42c140c0c100045a5041c86690402800039520506003c481c0141045010384100c803908501c030005082c0d100103090320718810302148400401101c0d87d480b0f041c94035580390307030718418800024140003032036042c41001c01039401510402071007030313051104001320150f0f02d1280100c24050b0b161207071120a00040000e800c09040000d01a40390000c0c8002802d04100b40c40d40c041503146002110165404400d2805060003a0f9004142454080392901150540603110508081e1494010841038009506540c0d00c443c0c4908103503040f90303000407661a80002c96155204078107071074005100c0c0c1411180c101000013081d104032042c4550002400d19602d520404d01c500302050f400c8841e400000601000c000b0300f980c0000d05c6040c1800e11400395080040500380340c401608018881d0f070110b81c600e12086c1318050a081a6400d00c0d04525200c210744010f481000b000d90080c0c041c280840004044100030841c001c005d80216012040c0b6105510000b44100e0340095540804414407010640b41d45c0210081c0c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 921534127 1250 921532877 921532879
    0x905010c090b090904060612030503090c06030702060c030a150e1038191d01180e070c050105100311060403020a03080708130612051e070f02120d05010e0106050306 72
    0x70b880c3c07018000c1044107080e00940150342c55a95030b480054013112011040d55500e11940340d5a0302c80c42c120b208181820306100419002d210b0070001c00061a40c04100503510810054580c3d0322519034551940050070651100055100408070208003c1100c0c16850b1103204007807101a11280c461008030055202004945098102c0e4100b41e070800a11001202c009039103000682d003007000440343e8035040103100003080080303007410011040a00c070301c24040003070820070b0134800030f00c8007440990030303441d1031500c140104140b00c2400b0607805031059025100c0d00f5000b01c02031046084c4100316010007101d5210448040b090303100c3d20a100e041810a440480b80c006100c218854519100d16100d5846204119107000007040304d04900320314085a000581181da8540000814071040a01201c2c00513001e00c081d001e901210b000c1c980203640d4056030080c02031400781c4500481e00c0b0280c0c0b0f4610020b4100380d1900c0041801301c400b00d00780d848079048a500010710b0701e607a42d80f80c4096409110640d582 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 921535377 1250 921534127 921534149
    0xa1a090a02060a0c020409021503010806090f0319121b02071a04030b07050f03190522020f0604080615100503102907050a120e0f09180703060905010c09 67
    0x1042204c3c0600e504441c00fa0001e13202148074040360740000c60700b1002c0700da020381c80e1a0100040c04070034020048160301044040042505900000026a4a01440190988102c1d210f83c106070114400e52400943c40041c900034080c9012185800380c1229201000c41c00501c01d11000141c40b16000c0140c61038000035a94240c035040c1540c031003243c4044020001d0003800000c010072503a640550703008500c12400c2020728440b140c035289100d02a140c002e0054905200d14442031088080d104869151866044030300c071070304142d080d0104a8a025551045419014920802c44010710303261800b9904a0f04651100721055415425035050001341c401c80c2c0815039500d02808211103442c2d504800916500e0501c04c800c2550740c0d41e002641c49403808a9103500450b840e0307001c200c50602d04190700e207660b0508000300c0581001080210310a6000e840c03154026501080312000c25456030798110498030113880c101903c82c100f01000e40030361038007298207619102c0e0789412144180194001e441c070081c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 921536627 1250 921535377 921535387
    0xa0c0201081e0c030a020f0d0603030806040e060708060316060309020307060201051b070302030d06030501090308311b0803070b0a02090616051216022704030513080a1a090a0206 78
    0x100142c4d0401000141015400c00c098004640b580018220024443c440030452600758540203000f448090040d40c0114200031548640180109140c0d034440701030311705460107070344a40000e442c3c041c2035049181200600c40c00407a40b95496000101e1040c020390403203060a9881d20200d0807038600311400d4030388110039043d0700b4501450200034140305002c1d1045034103100703061031544101d607442e601c1180c40760765584d4501d0800d500000300c281e005200561801d404c00701040c0215021401e600600d5802601c4a16102004000c00e0f44a0091112074240300049444602d25541d9610074039060b6000c62000c0c002a230b04040600888400c0c950240c04d0b03038140301640c00e100003405829501280c6a000b400c03231021a511303241c80941440038903030043b0145005980103006899003514040c401074200c0003601034800c5403814241c2d4005034541780c442d642d0b203503112206100d040160045c10307050082d11070950604c02101124060003d018091545a40713410b06466510800e510f0005e40140040c41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 921537877 1250 921536627 921536641
    0x150c0a020d0309030503040b181023070f0308010e0901020415050306180a0c23030c13092c01180213020f0c0a0303061215110409020a0c0201081e 64
    0x703003401188a07007000c0c0c400d55160b44d1024210341103030300a5600200d0101d000c84200364141c10040c0c04000c152070020011001100081039004041c02d80c0590b640102c440180c07400c110390031100102d40004280386240070342c1c600180400400e221301904000500e003c5049240c0600c03c440440e2109111b2607841c1d0342141c01540c00b03802c0203001962007d603105a00d0030b449194001c861042d8400c100000340ba03001c60368042c0c14044950800c2c0002096001c401d00c026001c802102d0700420400165038444801780c02c07503403d021541c0c000210f207508104454141c00640269003002c22548603114109003c103240701c9003212420400c5400c41e006085040001d0300b485000411811550400585082c01d0030440341c174154811403040f50682d0040129905155141c40b4400107400450281740084010342c4947d00510980040e4a110545d02c90300055441d1881c0c2c1100d0080c40d040c02e066448084002c0f018041e201100800d030f020034060800207608000440065108415040c540c02281d15022 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 921539127 1250 921537877 921537889
    0x7320108010b07170706050906071202040303090512070b1804050a0207050307060c021c0806100305010b0a0f020312010b0304050606012309190b040602280f2d02150c0a02 75
    0x13840e15034009000700003000103d4500e00170b0b14030a550f032500408241c207001200410001000310100801803041c002400040c1e8001c00c1035040381c1088035400c0080820b00c4d80e041c1008042ea000101200300050340407040d140300c0721072242007001241c0402c126940e071051142640308100000b41640c00420952000a04942c442007881c6c041348115210105a520340000c070102185885002c02c548004001a40c5040b180c401740410b2240b500340520b514041914055000d2011240103004d009890740d040756103300107491003224020004151543c1d1902d00c00342c0c035441035406072600d02070180024540d50042c1c1c001500ea010f1030341200124680c030b00005000703400403441c1541c000d6003100002d0150f95111000e902a120008a4030b545a16019000c0d2402c99218541c0201c954141d081d441d001c3c10f04114141d02079085421a01d0104c6d136841c1400c13130381c040960f1468a49621511125000c40d1003030600c0107991003540d01c940da00740c0c80040202c890164492102813580401804801030504d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 921540377 1250 921539127 921539153
    0xf010f020f0418140c09040f0b09010b0f0f1204030e0405041e0206070b0c120a0c0219060b030105150f032b0c0f0510060e1003080c07320108010b07 65
    0x20f9034001901c0707204104400c8111000f5a0342d01c41d15640030480001504c4c040c81850900030741c800f0704001c411804c0300800e43c4200305206a003580c030390104441c440700502100f101c18850020301c000da41c42035038004020341c0900c1503500380c000850442171000142030900c5014040c1e078004070300701c0c0380e5610140b4078507010031840e2040740c00140c1800110300142074001e500d4098008150201d0711a0003801d55000760084c010003c0300039030f041c54660412030760080341e0401c000c1541403010070810000d0609002510304070708201d4041d0310789020891120b4541d11a1040584226240c940c01c812502c2010740d10428600705200e81040305d080512201c003503d00910b1411490704044640341800d45801c544041e1084003645e40e500040181e0903d010180b0035031000d40f142081081d46818561280d0808085501004048280c006101e842910007088590000d01000080d0140514204409001508100b1080c5074588900402102d00e41c0240d0303405059665031031040d070421209031103412081032a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 921541627 1250 921540377 921540419
    0x8010e041110030f111b0a0c03060507032d0609060806131106040e0109110703020a0f020312070c030b01090519090c0b04091d060c0414120a050f010f020f04 69
    0x280f0f22079103036814554042d04043d05e04d100d0400da111000824080c3c1086610b00507103409800082d41d941c00102e0600340320083e203400610016040d81c505000740e000300100c0ca01007030750741c40a00c0c590b409025881c000d4000301c04820428031007070f80e8032031a0350161441c1c1c0c06100156004100000c00031907024000c80d07620f034050a1048540350790700380800c0b00d540c040d80000e18800c01100041c011080300c1c2c0903220100004901d884e00d81169034400075102d1061010046caa400304100006c15550700300048400380a10800482d40d911092804031070002252004941e02c1c000d500000a8100851040c107109551b41051a0b00a0b8601c15a003402072a0090044820b000046800b00c0e40305400005400a0818a00002243c0c40352a401c0340000c8900e100e00c800c5944060104100b01030124240c0d170440c2c1c828840e02070300584030340000f41c44201c4c40e9524500c901c82c4100715800d0140000f041c03030305d03092244001c000315405111203505900c5001d08070215100200000c00c03064111503803401200d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 921542877 1250 921541627 921541631
    0x60f05010c0204061707030516140108190e0d0e030105040201080f09010245011e050409050a0203161e0e04090501090507050f0904020f1002101b08010e04111003 71
    0x10716001c19102c14081844002c0031a41b2180c01481081070030081e2801340d089100d03104103110710381024006103009903c00d15041000b205c002c0741c05685515603011044170040c5050040d8000741c61055542d0042404000010b41001000c00c1503040621505000c3d82e010b82d903100c155600c04907030300755001014100043c4d5640c20803c1e154501104030100090040040d4000003000200380002107041303003e0f006071614a54420f015255a030030045030900c43e035425133914030307990780070034295054000c6500c001031140c20101080b107070000942c015441a41d281c000e0851405401e0f004039190344801003140d040340030b1205200f01d0140580b00c00b03c14100002e0000c40d62020542c3c80500351207281001f01d90075400410248400e1800d04584040140190780e0041d40c0d00e0030745c00042242c01c0380000b00d4000c0c2058401d1400c0c00e0b100f4051001c0300708561a05110101030030014001943c0e480080c0000034210600202d0040705a00c161401150460240f14000e200401005000030313602d103400041c15 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 921544127 1250 921542877 921542879
    0x1020708060f0403110105150f0f040f09050607080c162310050108160302060706060302150a03050c0f0d1508010e010b030c012c0f06030c0d0f060f05010c020406 71
    0x81007004014400d4446520748042c0c1c1c20300c3c0c540600004074000d07804c80c40764104400c10410300807484030003c0003801102d00c281a5400b070804034400c0c010380c1c1c00d500c0d0000d0602e1107a00c8070390140d800150940348980c04031b030000d1b56120021105001c042d0750130b0381c0c091020851000003040f0001d82c160014040c0000800f058180050400d540e00c0e10b050000f281d03003102100e1100000710b0301c0b4840c01410070101038840008160781071200840e4900000b48145000300701103080c041c40c1e5001902644d8003800c1e0201642041c000c07640c290304403903920700000f0f0400c00010341900c1c0c0942600c0031130f0244a5103a09001500c00400060400c0c1e080241a450300700d42c6c002100a000d0007410b40e010b04007000024401906001d250802c004ca0020303505200392807460058021040aa140d42c0d48500c203030f843d80401a0b20005034004a884600f42d90140d404030030320410f8038084c00104010100482c003040b001c1c04103280e4000341d602030310445180c5001d0500400c899406105040e140501c000e000144c0c00f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 921545377 1250 921544127 921544139
    0x1209030c0915030d02120a0804111203070b060402070b0114120105150f0d0308071d19181a0609030f16061101111e0c0607270e0114010207 61
    0x1d01000c4400c0c22a964460000020a04051006800d00519072000d0481011100090308061042d43c0d021420000080000340c10300035461124403183c1d90040145081003000007109980e070b0450301e000d85e9103803262408102c241c80c051003112407280c0d0004030a00030380e1a0240d2001d640d403200030200e03080311040d600301d29840028841d0038881c106160051441c0e112500501c00300c1c580e0f1401880c0148465000320011a41010305c90754045031900c3c02000103109500c5403d00c580341c042c031458000c0b00e80068242c9901d82c1e4110303902640d055031001c06842c0d081d00d240c0c2064554040d0321001440203850044010700700038000708801c0802404450604421200c0d80d40780034400401c23481c00c1d8801075001c1c003160743c0c401112541a248040280320f0241d01224800729849584140100b036400300503403040205002065402c6281008142d50091908100c0078084110000007401e000800c010282c4400b404148803601780d031101e604a0940d0307800c101e0304090004401d0561410b40c0f00300740c0c00041c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 921546627 1250 921545377 921545389
    0x1005031c05070f2d0f060203040309180c030c2d09050a0306020702150a0504090b0f040207051f0e1507050403051204081b1c060222080705040e1209030c 67
    0x1440740c040000148042d081c00d105902220f42d130000e85080c2129002c0115104c0407420b4406078000c0310050ba0f07030302d0b03628085c0c81c0d20910740e100d01d50b44004803056101c1070019601c06115100b0030f840034490403508c0b10307040759402d4506880c0c0c01864205042a80c80240080ca681d00c0400c0030300700025683c0d1501e0024000d050541e00888441d500015410218141488600346007280e0840c55030900c4024503000e0414081e07070041d882219540e0856104551b01d403914400f40401c042c1045503036446508050384c8809495038100f440c0c02144c6c0e0800309020b10b9101d000781802600025245005560307154021208014014000304074043c440400402c0f02840741d02da008214401c0c0b02d54881c81c0200c05424004911240c25121002807180c14003034480100c41541e8902c2d4951210240e0081c2c034004000b40204220444809451551511f5600c00304035640242d1306000c0031030710703225170302d20402c003d5420707041e0350262503007140444103030030049080600f920703003c01000d984090000c00c000c00c0c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 921547877 1250 921546627 921546653
    0xf0b0303040b040807060201060f27090b0601110f070b1e1306030b01140f030702010e030c010603140a031b03170c030f09060c0921150f1005031c0507 66
    0x11a030302c000281000010000c000c0300b0010302c03250000b4414117280c840340c00c483d1201c920405012007104050344442c0300c04442c510b503440b01d00c0c80302044804454288405541021600c03180841c00d201c43e01c0600b110000303000c50b550901200208200c60400d02c203c2d405421510500d003664803005441d46141c60481e01400700700010780c05052901c1d240c000002c06890b5150505030600581c4005256120480700446100c101d410724840d030380340c0700c0c10030807401000c480e04240082d010118242c00041c0701908040101c901443c480c0403000e25a1091544604000c04001d01069407245035045242002000d0007545004e03080c0100f4000c0311070040d201c7c0880403240e1041c3c40800108000802500c103008540000c40700005140c2440c10a011010074416165400c0c81031582509200e200200400520304400b914419136140000d40b51801c03203003030400e541e04140180444000307075402804240420482d00000c0040c5001500c02026080310798000408608004040008001045000b02c4d521 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 921549127 1250 921547877 921547889
    0x61b0201090803071112031f120203190206120f0106091406161704060503180c03060a1e0219021e061609090c022104030312050603030705120a09050d0b07030f0b030304 74
    0x31103804c08034100c45201c40030780e27000301000440304024003001da00c000441d904082c0f10014003200e191301500008805005203101811082c103224100000300c4c0c40f41d030f04141202c0c1d10740c0711b44005a44500101485c03021140905812aa00f48203041180b85911003c681d100d0243d040c1d07203011000c04000f0b02580d40542c020380e000c0340000060000d20507412100d004c16440d814090712820025a00298860201610161000b62502c02c20711401c000300301ea03c0b0100c040e5840841d41c590320740c6640d6441e22070090800c4098013426001d00c450281202404070040704100c040c16003951900c024080100349c05010900300520b2a90220304a00c2910440d220fa800d0783d0010429403d0040b000c0a540070f0b10100100c001c48144010000650400d030a50840c00c0c115601240c07075511180401c0c698090601c018103248241d1400314156001c0030001c01c00301c070503a610400200e0702c0c2c40c10310084c5450b01c00010090024100007900c41446036021409500b00e4020100c0c00c0c201c00c50000e032454120b40c0102d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 921550377 1250 921549127 921549151
    0x140d05070f05090d03032007030306090b042016060f15150905090414060705180301111804090c1706160905060a090b0403061b020109080307111203 65
    0x401145034001000d90911841403800b140f5000b2404080359803904e4002000f03040c50344441c10008001541e5a844901d8180c240d0010717126601c9040c001d0141543c3c0c4182d0032940c2c40d007901c039041810503000d100b02c3c0003440b6413004410080c03580720801c2a4080311b031011005404801140000c1c025006420103082ca44501040c564294003150050741940da028581e40e06404802031101c40c0c1140049080f65011940040c0c699a00d04003880c0306070140c120741015010b08010011202e402c2030140c0142d06e8a030a0100703054031444103050899800b524400504241840034103141d013a40100c10508200191006c10003401d507503107103000324400d50085111171440c640e4004591a04001640d400319914042080c0c1c440030721400780c6490114040c4a008403800107220100e580241d00d03a100501e4a004269543e5540b424800020006407180341c40680b080c1001054080c414010425104e80002265103103444544050b280e022031000c0341c40c0c0500418480c1205054a42c1c0a544504454603030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 921551627 1250 921550377 921550381
    0x30702190e0601172a0c030c07091109040c050c06090c0102010b010305010e0c070503040e011211030d081f030203071403010c02160302060318031c0e070303140703140d05 75
    0x1d040760981c010300da241041000c01071520076440700c840c000c0d0410810f5918603246a500d1092400c5915080349909402a0000342403a484600200506202600c64143d4440649030342c0807500b651440d068280300e200050019000c0c0380350580c00349205620a05000b40340400c20b903402070802c142110800c21540244945541079602070240f501049024038003000b056040c00e1103488180c0c0301800c80c1800c0e102c0410390701c0402c1130030803c0303d01421040074160b91941c2c2d1410400801c0018000c1140c942c02417003140207150070000f03203405901c2c2c4140c40380344055803212100b81c107030841301d00502c00071000c04800001686042c8003240182c1400c005486a21452005141c251120f8801c0742d021503110a040010685612100e90242d0303a0440b0304940c1c0303455030b480a40040c101c0c7e01d0300c115039001c00568a51541030380c04895130207012550003400300308409100d803500d502040c4400b80219982c0c6450f5458000314400a01d4110b1003803c20061000f120b03106081990051410100c4156407402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 921552877 1250 921551627 921551639
    0x4150c03020607180b0d0b03060108070f0b07110910050d0501020d2003010e0613110a0212040501120209180c0c0c090403210902060a0f0e030109030e010f0203070219 73
    0x40b1056210006080500e800007461289050540032445001c14112010944043d21a96a00100d000c22402000c84509503140c0d01515220001031143c0100e040780715400048918500041d17940e41e07034105480c1c0c1480040d550502403103610051152007801650000443e440c2da030008001506400348000503281c060140c4074000311405c10074503007031036003032642000030101040c03084905441506418464030384810000c540c40044030b0f03600b07101240c100324038032500c0325240011300703280700181d42180c05d0b4043c80020309902d846140a4203001460350460381c01c11541d00d03001880980d9016003040e03528101c20807202c8529000751000300604100150484070b0703450400080000780740440340c40d50300e8145554043c2000c590127404c00c003103a181c1d8000110316021680f02c2d01070282c0180130b00b5562150f448004060f0142e00700048049440f0352a050b80700c0c2070520802d003040341d0540b10300d0300601a400c015500e460f01c01400f0340c1140720811890006813910041d900743e05400c129080340f410f0900c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 921554127 1250 921552877 921552883
    0x170f070f0f091a1e0301091103060f012402030d020a05031e0709030204050402030a05010c02030c24010905041509060f3b0c06070c0302030705061603030c0504150c0302 74
    0x161019007414282070480880e0081840f08020800c0100e940c0c00b1092603983c19450080341e800308503a410b51802c8458030500180038100040f0800440030740d00e10740e5948001d050406402e000b801d03000c84103000241000c5141d07401000d4900c520b401200e0038440c060280c40d050303910400030000003d8000c4180680320326180f030140c1d1925103d94183d50300d440d2100340200040400c1c80043c1c4100c1d11a8042429034400b03104041516030400000d0018403004800a540c9902003d900b01c10791003144110154606481000c01d10070381d0005941c0116440c1000ca03101512018005440d04282090200c1c05804540304854085204a8011546170b040c0c00c012411529130b60034500145104d10000b84241c240d803151084041c201c0c008044007441d00080140c54509240e04054018400103002001d00007603444a40481e4803c030200c680c0c05455209000242c0a01c50b1080300e90b0f0030b592090000a80260010740c84a19240362081c00c040d40c0d82a24203644040781ca99902113071f01c2450303030703000d1540c14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 921555377 1250 921554127 921554129
    0x1031101110a0b13020103020c03030f040b090f100c0314010821180d08210906090a050d032004091406030c150313020a081501080a0309170f070f0f 65
    0x34a002c0e20141c2d5807a100c040c036060006041c3e125280e05100d00804682c081d6054451840000c8101c2e0345078a0075040061003080d0554003a14004128400100a1440042e014080d0b041d000c000c2c00c20000180b0f40c8501904100007503105041d100e40c18105207806001d00c40d0b0081c0020001014404007107200f5801d00381c10000c000b14018000c010b01840f607094661541d40d40c6c54151780c0207600e924a0b0420509038010300700c0f1603029641c030328481900d0301c0c50301d410a030140c1c5940003a10b8094840d809815500c0544240050054210b00035603a40d1034001c0e8001030070140c9804620f104600202c4c0804140e41c03042e0049d03900c0e10350b43d000015203a000c0c0036040d0b600140a030000c0084200c2c6100080f804c5100380c01c1008070303400000004500d441d5080e210802e05e503000d40054503030754075080d10548480c0b20501c1d5000007070049000007080800000c01901c51034264075080e00141c00e1a021000e401c000c6a1080b10354407132401d5201c042d5204000c084001c1283c150841c030035a05140c200c5140d0181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 921556627 1250 921555377 921555407
    0x90f06090b040b220210020708060a06060e0f0a050d080405040c03091a151e090702011e05043c1209050d330608010204090b0d05060105040c020a020901031101 70
    0x1130303000701110344031200d551071410341d804480c001c01400b010302080380381224540211000d0b000c1c01d82032203906000303078100307800351042d81d21414000041c0e80305202400f144010502e51000e118002001981000449004d140c0c3c090740072186400c0d261000b10702611503442c480320010ba03413801e81e081480710143c01c409680d00c1c0c2180d0714203036040c41400c0101c041401c00e01544070700c14180000d0740c5212032501c2c0746a145c4000c1e140d0600c3e8580598080d00a140303000000c000307842c4a07941030b0018502846100e20072030340400b030394078515500c10580700040b26000c0704540000780000710700002c000340361111800c03910601107921803d404e000c0040c1101d2032544143d01a444403c24800000c4070014908943c002000c20b0030304103000c42e0207810a0310038a840005443d0316014021903000010340041c021b0b294011802d101c1002000d050085085801401600e9074010200500c650320309500704c810308040c2c510490740c2c0c0e0000c0d60005000304200b81d0040725181014504c108013541c000c0810303074600803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 921557877 1250 921556627 921556651
    0x51504240c0801050906030f010501031a1b0f09040b0d0c1401021902061e0d05071d06070b060a0b0d022a0604110102031603051c020f090103090f06090b040b 69
    0x107040700544114010302409215030200b0001551680701008040c043d50a400000d005550303480c03c1807503441014000b03001100e10b240d40044c9803403800303074540c00d070444920800d60300d88003154108101d4dd810203184150b009484402c00081944c9402d90340c120366000d0b800c008450f51418a6108020351070140d41415500a0300758951414041c88940d41000c2c0c0607149680e90b10720344a540d5074111641d811082088002040507102030820348d01143c81001540c849041c3c100056034404007204004800580c4020b0804c0103000107422184515040b0310f018001110480c2ca445801c0340c2c03600002c0720500c199901181c80c1e102c444404440e040e90440c2400c4090300c1028035507505440e02002000589101e03040c020548060f4802c00c12180c2c90060800410aa01c544e0b1500501950248800346100e00652001c0e030030b199050720031510480c241020452070100312100543c050400140117990203040544044049a8107005004005201350b588008903d0300e86414107040402500380f00c01c0311 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 921559127 1250 921557877 921557891
    0x201050a0f0e120d060b0c030d0c021504030f020c04050112020a0e01052d0910060e0306160f090b0a05030916050d06020711030706180512100905150424 67
    0x2c00302081a100c1c014040c8022a0f80e1215108048003520880e4000350900d44001001a4500004409000700c0c10180e041841070b81207071881241e44070300c480340c0002c3e40c25106022500083c0511405100750041c2e006071404900103e00082c00c84509a02030f040a0042c04440340441c07600d040700700c2c0984014000e02c6103a505003408158140b001c0025043e410340c5101010900c00030050400a03e02c40040000609141803156000c800d4800d110b03030400300d04840c4040c3c80b54680468440d11880a0126007441c0f1210120203c403010490240c0d1418843c81d2100440c0304a440b00081280307250740e444076a568141040050b1034402d0015009011b07503004202400300c2d6840e03000c08090660410000340c1c0312515402c0c0f4219405011300510750610441e0320000760a41c1102d401c12180d40c2c1d06815010f01d0fa0b031041400b1000c41040035421141d0402030f0800f104d944188d102502e1140924125024015045201100d0714426501074404500d0005004050b24403140030841820208206202c05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 921560377 1250 921559127 921559151
    0x50a0b0421022a030307120518010e011d190905161803031202040b0c0c090718030210020c1003051b0406023a0309050c0307030b190f0c0201050a0f 65
    0xc8404856a41910108007000302044e41d800c2054603031031508000c201070307c1c5642c5100501240e101800441080610800004c00b560164410290050b03060f150280e0441c40b4503012441e251640c40c0569210a203000e0000c3e05a1100c580100078100e0b40d200083d207130070600c00c8043d080c0181414541002850041c210b6042e0310400c081c0122541400d01010445e045060a0040d014942041514200c04903c1800ea0072000418104250040d00c3d441c0361034540c40c00440300c0c0b2544210b2040d0b44020001e0400050403d95034481c2d80480d180306440510b0f4024001030074142000c13944000007600c40080c8664443c09405a02c092040000b40603d0240b80003006511800c44100329407420705c00f2444040d400b8002a042c0150390284030f03031213a05410914010b40100030103141580c0314072480260701201e0400141160541e0b42000e15041195981404040f101c6407858440c20403541322294401010307100e004a4425140c15000070502c0d00e4520107035804c4800352010302d000682400701c1c031228 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 921561627 1250 921560377 921560413
    0x515061215040804170c04050a15180f0c090602010b090717071202040f140613170c030d170a1e0b0103021b070f090c05030a09050a0b042102 62
    0x4001da59162031982d0322401e02035040d000742e9012161114031000f00000c03100c000b117030710016120300b10350800c1103440f90210f0710102c941940440c1500154110244100099126a40d860b40002140412403440c02401d0509460007012000e001c14013115040c01401e8080c0200c50f080340c2d042d6801402480c00910040008039480d020303148007020700303012071040d51044a520201c0c86001c0d406560725035440702c8094001210307200f410b8080c10480c4240c0e20601d068021541880c595010f071070101410100c404032580340018000d8003e10503a0000d1055440911840c4200078946c1c8565001340e0400c1d55242540000400c1d18039464540403a006894865220a2100c0e074a603c3c0002041018a80160300034886d0018001605e01000d41c032601016000a00c60241c8100084451003941d88420040075105800d44000101d5070a01c0000c00002c825400714011070300440880d08012410340b0307a14681c3c6403d0310256918000b40f070060340e20205043c0040d01092039071006001d00803540c01d03071140e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 921562877 1250 921561627 921561643
    0x304020d210809010e01060b090415120f020906010e010206180c0603010306050a0b01020d090b13030219170f1902150c010605010909020f0318010f020705150612 71
    0x8410905003994005100158034900c00140054842482000145030090120041110740342110341c24107003103042560040c06900101c0d50084015403c100d40b0404020203000840c04624120074203000c001015021058891072071400784504030855500c500512104e80c0006060a05202c0300c55038500603030341d00040070750703010307001c0740b444101007455441d92400c00344100f48032a070280d004000802841156031142d800303003a40d0300d020002c11341c2107001a42c5a810184040002c0350100d1001c011140301703003005000c0740d50b0008802130465103c0e4001400c010309000019040d41c4118414846010104404004582d101b0001d046514403216a40e40c0d0300c60218480344e081d000015400d045440c0c0c00742d4460042c050035012a11680c11200d8580206000d229050000e28481c2000803208010f100310340e00fa0211031aa0351441d0790780d4901c080c1c21500291010f1943d9601c1e5500f81100b0614400780c03400300d1207035024040442401450129071900508058414003024560040841c40012100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 921564127 1250 921562877 921562879
    0x1c0b090133120f02030610020a0f170403060603030c170405030c3006151f1b0b100e0c04270b0a1401120b09061207051003090b090111030402 62
    0x7680c01c80340942100c40002030a0301d400300906210841e42010240e4001d10700c9442c064440900040340800304030303569560034002030701142d0001180400b080070052030629548110040302c1c0742950f20b076120000c480b100e0380140c000803003010000040200f00c007840303040791014203030060815041c440003e0f01c0d0480190030a120380d210400840c558200901c2c498948040c0ea465110303040d0543d1500c50700d82c5d0b011502600030400c3c408541a50385030215480042d1001c468401010b180440001d844c055404a012038004000c99090300005007200d62480c826514035a9204a240c5002408426004082e001505481d811b1105100c08483c0c0314040600c14041d0b801c010018400790000c1000b0140d9030481908408019000304e40d4190b00100d40b1120078003130342c880c4043c4820f503107154100c030240c8d809a903204008401042c924504161980f40e450b60400c1035814484c0e179003000807503e540e81181000429203440e684024004582c071101c0e84004114000d0100c0420f004802440707200040c002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 921565377 1250 921564127 921564209
    0x9010302030d1812380a0513050d030e0f0307020906242d0304030905090c2206270603110903010e011509060321051c0b0901 55
    0x88181e83c50000108001040061840044d0072910308140c0e803c0c04d560004100c0891501c040085074040070b2402d4840180c140d040c0c002c994441c0202c2d400581406440041e003040b450500f80086841404211111402a03d002602000740780b0810b007000c130f12010029094000303014445c0980c43e00c920013a44800f04460780c002d070030621240d160744a864108030034500140400d03200b00f02503036002201011090701e487c00000506c01c9130550700301e00c42220014002505c0103c2049142481050182c011800200050424601c501440c1c017011321101100c80968040100300a40344d003054040c2d124129045040c60600380d103a1450180000910071081099a100ea00c141d440380c41c1c40c159610708038024000e2203450013000700039018000e600c9040e408444a1000012054450711a5800701c170745c000c0b00c000c0060b4140d08010102030f030701480798050110810007000042c803813200400f140b4600c0c010002e50220b841050040170302c0160800d03985500d0f159080700310f255110003100041400d40c000307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 921566627 1250 921565377 921565397
    0x60e090a082a030d0c021b032d030d060f050d0c0b03070c020a0e06040f02160f06270b10060909020903160605070b0a02040b160606031a09060609010302030d 69
    0x1400040d25240a03032814500012400502034080c54005e10105d8945508455105002640c00349041c6060070304070703078141c0c490744200300c0124407000f502002488040300c404111441c4040c0030708580c0900ca03040c0e05240d80704018002003182c584100c0c060441075554210440855541601d030007498040c0b111130900110006001034403541c80701e10145d6026080c481043d9551064103000071041e113007103115504007020303601404024801e0b242c0250040c01502200f8055440b41221400c100900fa15055181c2c00211040740088030f0400c960388400c504480d5618880c1010810780c080a00400d403a18400d1600300b00791980000c1e0303c800e039007050b040107030f646004400103480c003a102c0c041c200f48048588800030b1110f4001001e442c80c24000d4a1010700790341d0743c40e2041d08034031542c000d0f00311040c024004082c6281c940d40780400114030503600000c0b2540c40c0d0300c0b00001c0a1454451503000c42030001000300008040c80115000001610100400d505540c0040d40310405c0a1415042040d1005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 921567877 1250 921566627 921566677
    0x101701050408070f150c030c030c03110a0e18010609050907020607020607050f120a050712020c0601140604170604031209170307030b0a1701060b03040305070803131401060e090a08 79
    0x2180554148407800204146c07240c610000c1c1c0031b00030304050940802e10b042951180c0070301078083d440d111541d00210ba0f24200d00c68000f40c2d1809038601d81e4640082c40140c60300b108401c0307149500d0180200d51550004145850108448110000e0140c411074101c03205002c00640c001400c0d9410071040e041460b00c80c6441d02d1100b00301e001d06502c070820400820144081c0310070f5503000314003a140c2a034a07048004403070b00d03100303042c1d01c5150314003945c070360000c40104a01c03510240c0c61110108014059854665a480c89074442200384102003066005802031004054006010b8050341b246500c062080c1c9010351145000b0345589958040e8034040040042c0000380b09522181c061803000305100e10882d00c894502c020484455102851980790940200c1d152300700380191391240394143c2d259450204e0325079070348025800241450248101003010140040c40c0303030030503031007080c0034034000224246000b22041045001900c103c0058000381d1049001c14901c00c101c40082d00402c80d402e003c240100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 921569127 1250 921567877 921567893
    0x18180f13330c03060302030618070b0901020c06040b1c0b030303040b0a1b09051005031b071502040b0d050703020405150310120305030f010e06130902010e09101701050408070f 77
    0x400c01c0a8a0785004000402641c05038003a50650740290100c80060307407120150380645111044450391503000c5a020803010000d44000c0403004018415142c54108140128400b5082030300810104a03020078800d0100fa0004048185004017031028000540340301c0202e9100d00c80a0405010b0f05455400100140d00c250010300d04440b8940d00c2c54101114008000c01e061000e01500f8400c2c0c406d050300301e000b40c0c07080050724007440340c0001d84204400b03854554509a44a1340b0704903044004105a339a81110510280008291282c101075035894070350321000449000410030030070b1610510040c045034548120001202480c616981d03526141d00070310302c00d0ba4540343c0c403109100c1e01c400f01c0542003592003000341d1f01031a91400c6001d5582d884604c0b103042c0d00c00840d84a50420340d4860894198030058002140721401030503c550040d10030070110b425003a00721650340c03c010101e0010052030a80c10084d0340542d10160007001380e81070aa884103198400c50401403d102400080481404280c5d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 921570377 1250 921569127 921569213
    0xb040207030f05090f151b03030f060607060e061303120c02190f060207031e09060e06071b03030207080f0606060d1d031201050f060c060103030518180f13 68
    0x1403544680101e44000308446d644980c070307a0100c0041807040100ca4034000020b0341c1c040c01d0b40820b01c86466881005000301c1d40c21202040e90f003980c5030036407440c401c40144241401081c002c0000c0700d103040c403410041c081d084044040400e0600e425000c0e6000c80c1c1c007007000e2481c021044942a501001c2c1e00740140c10008455020706a41d1002608800f01500701e0701400c410240d08400c16032200100400759140c0c8410b00c80c0001160103c1c800358980d10703082c4010004a8800c0c1800351048800ca0030a01c0301607500e030821000769000080a200d600020401d108945000300d00400b45890284080358441c080c0e40f2003d00030b19195078034104855502440030701c0e20b0004004032070304d0b0300e1517548a49450400f849124011100c8003008801414081c0c12a00400c07418030003032403541d00e180d404a401c0c0d0b114482106030b4491090b5003603025070f00e00200d1241c2680da22405501c506081400e109a000c000e005600f440f04c00e01c0c510000208100300e403c8070708090b021480c0303804000801000e001000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 921571627 1250 921570377 921570379
    0x1080708060112141f0519060807030207050f0609100e07030212070305060f0103060f0c050318011b09090b010c12260c03100626100323010b040207030f05090f 70
    0x10301c0030410144441c29854044459070103080c1c170a90381d03d00520140031400c410420041030041d0052081f80c0c040d41c1e8680d0000050f1800510304456522a070f81884c02035940034a00f40c0010b000d00c00da0281c1004800310b00100e01d0310130407d186078035000079a5505148002400307010b000d61112106203081c441800151703041023741d1070901d000e00b141e41c0203140900003194240e10300603000c00c0310401d500c60b04a85000544803d8075503240d01c0d182410b95015241c0d820b00642d00d40402c000b040c410b514444c070520703009840e0111814204202e031030035941003030b240904002c3c0c0c140c640c01c080740c40310810650b084442c1c01c0c845070880320b00c01890b60300303400520891810710203102401034560310040214440e600f401e089101154031050100d070480c0b03102514000800d140c030582d0095a4410340c000f60000c0c2407010100c030386a039a40c3c800c92100d0b516503c002514681000d050140f00d4203001e4440014030483c3c0451408690ba9400307071111510180e420100a80802c5036482901c40300410800303424 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 921572877 1250 921571627 921571661
    0x2a1506080106080304030303060e0609070c2103020c100e0a03081b070c05010f090509010b13050d290f0703050901021e0a0207090e0309121002070f020f01080708060112 74
    0x10f1602c981030358980c490f2104800080c50a0400100e002c2050300042c01820010450303080780c3c681e0340c411070741880008400e0b54a0fa64003c0c01c045598000e005210b001d940c9501e0142c0c0ba01000800d99003802e40003c0e000765040c0c10000183c0c0515804606503003610b6140c00c02508543f149a981200000d0724a4483c044000c0001c00760f040c0300100c038060382161004d907a014034801d410001120380c190280f240503000010380d00117009850a28001e07003e100a01c0030f804120035030700c80002e20018150700701a940300240c400311008108174403450b5583c40040745080007042c07d00b01c020010384500207068000701035461010650000e029012244a0015030000b50106841d2031034001d1aa8822009200980704025000030551094041c0c40304890b07058003d54113088801c0c0521544d50b81e4200e84d505240603489049000b181c2c144084c25640780164032407480451a4414031000b60405440941808145810071162990100c40c1e44d50102d400c4ca024034100c20400783e0100a0042014200700802d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 921574127 1250 921572877 921572879
    0xc05070b0c031b1201030312091a01050a1211090a0608030703080f0a0b010207090c0c020d0b06040605040e060610050409023103021807200303072a1506080106 70
    0xc55140e01450041140303000503070a203501c2401c3c210141c42124044481c0d40803050040012174022050415030061400c400f040c2d0000603070340d4503202c1210001119100200700300500c900e04ac1203062201500804070100441705958a5031017201d09030b4100c141c8a41070040000b01800940d800a2004101c50021a51200c401c4d2401030310001089980035081e803012030001e078034510a40224014280c0c1078001d82903040c02c00d403030307031010b40f0340b4a41351814401400500360040e154600001c811900500340403203241041c10420055581c1d940c41076100310700f0402504681c0c0800f10758a500920211545807201c4801383d41958980241d171b1204203210720201e10001c80008002c81a56540b80e00311021011341c00034001c1c07410040b07040c00041d400c507018150707090211003d0005141c0200c0d4900340190107504402f8031440050303002c0c410215542020090041441d082a0030000b40d014154140c2d041c150045402d03980751180180207401da9042d088040e148603107a0340400081e0103010020701c441 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 921575377 1250 921574127 921574141
    0x5070e070804020909190303020c01150605040e0a0b090c030402130c0504030506060303120127060f0503010506010e240d06030c031e0c17160602010c0e030714040c05070b 75
    0x90070481e01607010314400b20001d90395100100c2c601c4904511400c0c0500c0342c0a260310110004d41040e61050203941d61941c018489920122608004052a07900c595a83d41000c110000b12800a8810704c13031281416030444440d96030020187c0c3c04400309807800d4591307442d40000f8081301d00c0c00f001942c40900d000c05850386035500c5001081aa0b000c0ca003161201d44030281810b80c0d0b8421305000c0010288a403006121030500d950f464010506008450190084c001c1c440300215642a0300101810582da401000745d81801e00072154014024200840140440d20102e060001c50712a034489030018582c0206d0f07103d015205580c82c0f2111200d00b0403100da168038018040d00384600044d94000300810515019100320045203281980c010401e0a000d40b034141c6000014000107a030740e0302d0f401401c0c1c1c0030314a412078504210040c481d0394004520b4058880c000f4141808003880c00e80250401101400400e4606510030034070402520000359110f6010012103242c01039000061444080703c090043e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 921576627 1250 921575377 921575387
    0x303061302120f06120604050d0c0507180c080901290d0f1202011410060e1c050d081006021207020a17070602010c03090b270706050d150602120705070e07 68
    0x310301e1094917948175600340c18003801d942c1c0c00e04030340c0100990b21580d003025030980f1558840000d644110111040a41c541d0300c070005004151207902e50540d41ca42046a201c1d502a05464000d13101400070800d6001c1805908810240c0c100c41900e002c003030301c81000084c3c55141c100e941d603e40002d11090001d60518017101941004048100150308100c0035603044111100503500a0081c219207002c9246007010507034081c60960790059100d0004464001030500505154107101d1003140a4448900005000b504164010b880c00408880050382070102a400240c252840300c601900d01e521030440e44001401c0d1041c2d900030f020818202010804444000180d0070166000c9800a0008000412040b400c9598100b0080c1680070340d100800c54400420103034000c1c1280c0d9001001c41e912000800616004156000000240700000c0100e086001480703a41510030a00b0411f016580ca0040025030b103181400390420a440005902003c200040001c0300c020402c202100d00c4603d40000d001d40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 921577877 1250 921576627 921576631
    0xa15090f09050d140d0c031409061b04080a080c0703050d08191401051c060c0c050c0a030507152a060f0c1b050102090409080301030212030a020303061302120f 70
    0x10180f1981c4441e01036140200c0e000d600c041035410425040441030a1800040e05004944e03009060b5507284800a58140420051084441c0d01c0102224281140e46540c1c0e071941c0c4841051520b014072003486070010114041760606e41000889481c0c21111400c20700f800b1480e07000419900c41d404086044070342089a49201e806106a5044416102c002c1601592036411401e02d0000070500140500e2806000c584401e0310600d951142411840d9200c60460b00c042e854000400c5143c184481000b00400045401030019501800040d00e0b50390b81a03900c03071590080b8642c8105580c10141050f100d401d982072122110040b4030020307000b10128560028403000c003078541c07906000300928000d40c40d0161000000180d5074444000781103082c0303800050380300030f812982550200400c600d1542c490050700109401420341942c0c0e949103204011046940c050a02007513001800650042070300402529440343c8191841c1e00400800d0b600007009204903101c1c168901750b00000d0000800015000d54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 921579127 1250 921577877 921577883
    0x11101150e0907140f04051e09011a0d0b06100c080708030a060b0a09091509020408010c1b0c050108101806170c0603180c090405010b1f080a15090f09 66
    0x41d00094840c0304004580c10b0344c100c4141c1012500c043c054290a21f86e200c2c55005c00302074072204016441c0244040c90045c00d403100e1b07540760346500100005100d03600343c5030a01d800c01c40c1c41003a80b02d800d07550030010b44c50050200e40725500a04000070f00500420520030281c1e40485210740d03510b568580f01c1d80c50f41050301d1340303080e251815502281d40c029000031104105086c0d150001c40c14a00203c910240003800030007001c520380c0010010390340c00c450000d8009001000c00106070001d081500038000d4551000e594070a014110594010852402121094410a10700361201da81d50742d02ca100b50b21501d600290080304518034030726404103030360b0010083c0d0b45071a001040c9040c2171036840b941d4602c0c8000442e80002e04202040c1d40d4000714440c079890b4040c52082d20640c64144001820030030044900780d60300d944411201c0c12915000d00208070310307541c042030f8104c50700303409100608010008004940b52690b0703001500741d0801402a440051454101c2800403603040f50340d1902a00444500f1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 921580377 1250 921579127 921579133
    0xb0304080423060d0b030c0a0308090f0a0b0304030c08090604080616021204090906060308070309033309020d0605151e0d03053f0f0402030606011101150e09 69
    0xe80c0070b1a003008142c0e0b190040200420b04001d101d095030780c01070010008440d85441007c10840068603107401c0c0100030750140310701d0b03511000302e0400d1000f81014443c107248a02c804000600044100d0340c00d6942154151910340d40340006031034072801a01c64201c46071340c082400302d0001800e40c0c00103162031190444500e801d0140142d03240a83c0d0318400d450900b01003980900080c000c81d10598010304105001d034901040c0f5076900c1d2141750450344a86000d40001c2c009e90f10038014400c11581c624000b524800c0c0d81c1d040c251044210280700e4150160040165444410364001d654501007801c0f0b0503500100b0030045400c06410381e0081162501c403c034002c90884009081040301ea8407a00e00310440681025988a65690200da1580c0844145a030b800301e4107500d40d055881c4002000c09074209440e070210000d802207040141603900801c0f241d0041c50300004c100058902050f810340001007820162054200b10592a0140c070000c1d141c001035400c1940002045221411594000c072001e100f6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 921581627 1250 921580377 921580409
    0x70501110f070212010b090105190306110c070f060c020603040218010b031b030f010303081b030f01231e040608010905030307090602061b0a11060a09120203070201090b0a090b03040804 81
    0xb1090036102c80b68455640010301500402503818840800e5501c150740f0400f000301d02cbd481c0d940d800115500e820200d5070b25040401c07441c0070b03040304100d0040901040c02580b00311a1800c80020322034100040024090580030010500b1901c2d51820030b41c1d03001e196a5000388540e159190798005400c22100b810241d19411001c0038010781341002c5900420740002007a6131682035880680e004000500304403040d240030b01c140600079044002a5008242c00496820a54903002180520301400510348400803c680c5405040e17590f10040d07101b0000c041081c2e403884400700b0740020b0003054243d2010b07005508011180003040f002000a502ca072000340c64407884240c44031403c07651003000711501d6001800c080d1520f1501c2e20090003070a8919054038140e003507a40d00301841802d10005031040404252101c00340000c00541c41d8140000000e02e2000310306100582d0002405120380d8442c0d007400c2c0da8000340c940d480b035114041c2031000d4a0801e10043e581d00301460100d90690180c0710300f401d0600d15182c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 921582733 1106 921581627 921581659
    0x60306151605070905072f011e05130f06021c091203140709090209040f020a120b04050c090910030b072a05030a05070501110f0702 58
    0x407500c0321000c1c040c500207241811a4200d03200c400d041501300000030354400312540380c845240c2410f1110b0100300014010381401085403800b90350030700583e01000d40d004c00180312210414801000305a0320102101011200d500004003840031036a0030f400490029000f0703108209500c1c9403151031040411070f50382250808401100c40c00b0221045120341c94061098080a40303660801560130b20b05440000e002c001d00e8040c091501c4e901042e90303001d0343c5a0741d01050080070561000c660b10300d100d04000e0048106010a001c4003802c0921003011410207001c0e05005040340060141030101d0038041110540d00100080c0d800e6451060010210700000d090501031032039611034180e00910004034645e032900c01d402440f0014485400a0005840001160340020491400907210040ca1404030f004d0068040e545040c40c2002ca030010303d5014020041c101e1601c02ca50224107207903501 = true := by decide +kernel

theorem cover : BRFrame.Cov 921402877 921582733 := by
  have h0 := BRFrame.cov_init 921402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 921402877 ≤ n) (h2 : n < 921582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
