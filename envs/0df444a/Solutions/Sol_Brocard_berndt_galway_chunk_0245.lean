-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0245
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:42:41.740977+00:00
-- url     : https://prove2.me/submissions/d7f1a8db-dabc-4ebf-b471-0b43f9e1fc50

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 43884896 ≤ n < 44064752 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 43886146 1250 43884896 43884937
    0x18021305012312010606090f05090103020f0105070c030506070e0a09060803120910110a03051e0a020901050f070326101a16050c0f0108090a0323030406050f0705 71
    0x9400c140b0392070701c41056201020b9889107503644802d200310b0000300385c10350320419607601d8030315582d0b160380c4290821400340b0788840040c809619015410303404e180c800c8c605695603c0040c104040e2aa14940006005005110038050101e5120030340c0441c2d800c0444003055040e076200f0060044070880d21074044140c00603c40680681c9110504139808480c080940f0804c28a40d845c182c1143c0001ca003240885c607012031042013890345441465889000303132042c406258040c00c20840d8801300240060703401030300025050b18a034801d8003542d40062040d12000e48805640c500640000250b00d103600c400010030a903c00041d51220f10316024000700100e58000758205020485243e6545100d500440d50030004030404081ca1407450000302e01034000f510307111420b0010844880710782005581000201010b01c0041c5d0b0001c1440307030750683c1c1814030700e850b0380d03041d4506042143c0011010141c0707040801040244a443c1d080f55105100b05007d040300c9545844040c0d50343c9c0601d0380080e100d480b03d0f001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 43887396 1250 43886146 43886189
    0x30f02130909031209050a030305070503090c040f180609020405090304030b06010507030905030d020604030e0102070815060109051503040b0601080f04110a181b0306030f06021c1802130501 83
    0x40002c1803402490007800c510340c000c2411082d5001036008845961201107414141039040c8034031b40d0480d519181071071550030b02d04901d50b6504c1c200c4100c1c3d44500d507103a48810240d00d00d60712041c8441c041ea50092403140850070508001d044003801680600d0815002030f034425008030890f42034a81c0805041d000d6204c4030011183c41d04061800c03014851408401305043d50200040100107070035038010f04013860030b45402080d00e07401551807030555200000503c080c07000850f159040d100500550764603503488400480f007000d656400b060300001034010300c0031248400d0b0020f43c89a4019000c00c011600c9003001150000001c4034004562441e140101c0c001600602c0046440b1200810b1400c1d20741c0c030748039182c0320100203400c002843d41e82c50315898009a01d0001c2d0140080a9060401c0502c1c41c0d62542015021a80801041203500140d0030070944881c07a012003000151807c10444020200004008591b0700003040c1c0c45084800800340310003240b401201d0507500480098100c9840482 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 43888646 1250 43887396 43887401
    0x30a0f03140d110d0c080702030a0309060f0507020319090e060405070905040f090201110a0b07050309030c07320a1701090f030c0b0705070c0b07081204060606030f021309 75
    0x302030141240d0100b003000c2007401240a80c2501c00303a00c1c2c10f00355407208022501d00072502c103e4803100c1403040d29001c0080e840e0300413055074021038413810046241c0584c1e28084004100c2c4209500d0481c0c5003406000032164000054041494841600e059082e8020702c180d502c5410741c403601c00e050303521a002803182c8c240b6803c40303034100099007004403200e0745840000301902c900094500040340d8403880712003550f0348154000c8041140c10041c10711340000303455000b01440000e0a90b02400303000000316001200410440d030713181801c142590180b5031038013052031025011423a203040c03071005240030303008001e80c1d0001c03006051002400e14804500c0c0c6400740e5003a128420b04101595a00c0c00380c030010410200c1001c4a0030300c0303562543c0c40c0208030310304881109009014402042803e018000000d01d0307190440e015130b4460b0b00a80e80307841d91450300342640c1c031846159110001018043c4401c101d00340d0410030580c0c04a0b18103004040585500400f03e00404081250b8a4003d00b41000001d00a5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 43889896 1250 43888646 43888667
    0xf07110303010927031d09010503030702040510030f0803041218030b06061b03030714030709030b10090e010b120f06010504020703030207020a0608061305042111011a0a05030a0f03 79
    0x100030512400c00c100d1011300012030280e0309030045018840c80750100482c0c40780c0700d0307031144d800c481d034440350350410020907503c6c003680300001e00580c0ea90001c10646c000c00e10f0140011540304160702401c0860749040d0510b40c03c240c508075807601500c145112101d004081111800c02c5070780104188034a140c407454070360345014246c1d58000404010706601840019208080c0714103080095940c2c1c244040000d0000c0382c0f00b5069030f94401c052085c0140c0340d5015000c1012030350410b05035002919400440843c08003164050341100f41750482d9203900c04010342101561210480318071041ea41320202c1d26403aa00c030a940806140c0101c8018003580c5030960290504a000b80b4006081210030b40c00704051300001c0c0c0001c2c0c0820803003420014145842a01a202e0309030514040c000760030140d480c040e4040d5404030f480118040eaa0325581c0700340c4141030740e003000213000000b40510100710510310050040d49611600600c44540c0100350360500142000f542030340304219020300c00040d2811104001d02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 43891146 1250 43889896 43889921
    0xf0402040806180f100f180b06014a010804150f0609020a02010c081501020d05160c08030c010609060e010302010c02030c0a091401050d0c0b031005180f090c030304051302160503030f071103030109 86
    0x44803400c2d1074081c05d56100b14070400c502c83d006c0c7d903016500c1010102098a00c0bc40307410000204200000181410203a000c00107000c000840c1c03409104121802a046070742204d11154030209030803569a60541214510401c507490340c05945d01c51a00341d003d500075100801c0c3c0582e100c4100c440c0070601c200d00400600700c60100102c03881065a0b611602d0014aa0002c1072950000c620516040001e218030700c02012503d20410100d8a03080720784514110500c07002c4c1c1400b117090480001c5d034806001007411080c009098000c2240c0711208000102141c401600481480c40d0021809041000b0400e560640104070502c020385402c5840c101607000514115400281c1400000c241d10f031a032402064000020925003c0d0ce0f111036000c01611000b04000001d44c410910702c50251400b00440b4140d4030151500400380200390200006441007504548203003400b090f14038184070011024502800c4110a43e4040752604901156016117907420308000760002c00c010402190a03503c021094011b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 43892396 1250 43891146 43891187
    0x90c0c050c0d0f0210020319030203070c0605090c090103061b02030931050a02032d161b0503042d0e0a0905030d0b0f0402040806180f100f180b0601 65
    0x1410790105d140c1110020300240560300100c1c0c280201400344024103c100000e1a00f1400c601c0c01c150010640301444c0c00c06031502d50784d400480d0022000303000003c50001c0181080d07125581d649451002003204900007004d02910000b0020000e1012040300c103504401402c0455050342e4510008a401030303403500c032500e000303440d40680250105004580c800c3c0030340e00c4016101d140c8444800d100d5420b5046444400d80a41124200300021070a526080031188208440c1c501c26030384103a030b4002280c00c00f11499111041c480040180000082003070341d40100c4030703104003041c6030300c00540b070f801002c102d0020041c9100c061100b540040351641d40002400ca0104164086841e03090856001d20003150b0410744403518041e05080110009043d4501038804510b01441c20385110388170f40c8060110b1585400c02c034900c81000c1800c00c51002103005070b60a88028540341a40800100f8841c00b82c054124140000c00b80d6101039190030304192608045040d4282d680e402c01100d0180c40d02244100149 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 43893646 1250 43892396 43892423
    0x7082107060f0902090f100b07030507060b01030204090e0601031e0c120609080406030e060f010815060d05030a17010e01030201050f070f060614030105100b04120305091504090c0c050c0d 82
    0x20f40c0e0143c1755010307004410b2000c01e076040140394045d46000d1500107401c000d06c00c1101000007948401210101da40122001540d50710001c0120080c2c803c60f401348810f103040c035803401c2d0f1186001c42c44038106e0b03210741100803241e0841d040810f003812945101400b00c6070307900c108021100c042d002a2408078402c40b000a04110180e030f07401402e41190300319000199650406800c040420412603400c2202e42c0310070351144d0b141090241e0342c0c4010003008903441c80e004010680e29203880c003046032070a90201c10f81c0d494803018900100018080412100c208521400001d02040c5400b40c0a0503aa010307074900d480c00031100941103c0350b0212030b00b01d5049084601100c081204c6101e458050071503800e007070080c0302d03080d4105070940f50080c2c82c01c01c40304505442000203034107040464040320211000584010f405042c00c1e00d01d0b00901c0703040341e00000a949040d070071a9048009000fa1650001d080126405508007151007140c000c02c0100a50f01c0a03410790f4a602c1d085040b0210284204041034031131 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 43894896 1250 43893646 43893649
    0x5030f030a050702010b0405040510090c0302060f091003020c03090d021c140c0604050a0510111b1c02010c0b090102090409060e070501080702060105011805040c0207082107060f0902 80
    0x40e80200e8a4440341941c600c28802850f50a000d2220b801100300c9081c0100d0400c2d8882c2c036110030b048002c8503152980c6001d144100300c4184504001160010a05902c4805007903542115501c111a42845140080c02c207840050092090702c461002c110003d5060603681c0b014003040300f60800040c0d80c0440e2020204280740c0042eaa01c0345980d102d84120304980c0e64608104d8036200c1c03a600000c0c810384052005011548584143e0400c582c000c844c841a5020000801e4440e554080100c10301d90059460600f0384660602d49402080d00030b41c1c90700e0b039030038480808041e500c211500c02800a8054440040440d910f9203005030071404a200041c90110920300060440d01c900301c04a8405803916420780054400748480130042000703007040d080c03074a02440c00a403241014000c0364180440c01c0d14110442900382c58100103000d000e4400c0104400ca041c000c1e507521010302c2034860620664a0210103000c0c1003003481c0207900200385427401c140d403655490025001080c445404240d030742e079144026 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 43896146 1250 43894896 43894927
    0x2150705220602120c030d090305161208060d030519030b0301060f26030d0e1e03070c0602010209030a03031131050a0e0601080a09140f0606040506030d05070503 71
    0x20300520500c5440914200e4040d050013a140c81540b0500c206005d8092816000b108070740b4242d00d0700c04006020701403440c041c1c42c00d02a45000c1d0a940c01804108020071008036031505010701d46403990125651250208104c425500c18000e00050041c0012460040140008203d0b404030341004952452a41c0c04a400c64169a00c04080300400520402951020120f1130440c40382d006142c4294007894044103076648601d84148030b4450b9a00445020414107110704400488101d00030350600b0303111843c0550320703000036034103441ca4080e44400154980c0144210f0700c00e15000381c094401c4a140361001c0d80100410441d00f0704060042284003030f105400c809001144200c03480300c2c010800305c0042c410825070190082401140e8440c4184240b120200c0810b40c090b03401d2800c0402030f81da814415025011088008254810072a0007611411010038103c4208582108813030b090b5030317000100815100b003a2210340c2c05030404800064028400d000808085005008491910500a040000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 43897396 1250 43896146 43896187
    0x20a090507090e0a0c0e06220603020c01051e010b0a03020d050109090c12050312090307020310270f030309080f030106020106090501080307200d050303040b0a11040602150705 77
    0x104848001d03c40c0301c0c0240050354001200790401c0002d4403502e031015005210040f4028072901d40859a000003024603030900c107003020b08021251156a503000d015010b0740128262041a5090800007400e520039004041c211082500001280741d103801c80c43c946070751103102000d041540801440750180914040d03203008050002c0001044200c0741044006414542c101c0c4220740c2621003140c02240d00002a01d0741640d5506d2941c280c0d03151000158698490010001e4047c000e9070b09800c900c6c0225441101902114507e181121020310754109100c540d11100030f0a81c00c500c01e55601180c480d034481c0360094410004580380000f407a0515180383c009911400050391200720a020241d49401400e0060884030021420200b00da5074a041a0190b1810000800070000a10006d6070703a92104801164009040da6600e0403d030a04003039a070000c84040340d8403420244081000400b907000c980032034035203602a00710b0803110351050445010290000042040c01d102020a5242088040300d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 43898646 1250 43897396 43897411
    0x303091207050a0501080c0414010314070210050603010b21030403022e030b01050711040605040c050c061003121b0210020102130509010f03060f110f030108010f02030408090d020a0905 81
    0x41c034586440d00700300c2039811681015040021610034071412200c10070584040c2d9501d42d1060403141142030040f40240f05a0710342911000e2007a05002e80300c1c6c0c0224444a250309110f40c02e00150780c94005040c01d0342d00c0c4801c040c0e040b12202d04140070300a141008038400c0d002c41002c3c0c0c6d2a044da241c0019082ca1140e01ca101d9072121883c2010300500680d48554446082d107040074880b9161980020340b03d03006414010b0001418060101c0d402e90385d07a40020068940184200101c5038207003c010495000007842d51100d01c160360100c0d480781e01042252044940c41b140700d001120003101c00b2038901c1d4610100d0700f2a200d91040c4580140d4aa40454400388000c0d8001a280d2a210b002c2c040c24101076032010380140d4102c401844081414010030003601d820440104d01c1844d411140d0006220303c5111a10127540440d0aa0f035003c03620000314120340c54800207000c6000110001c108078403003654000e00780101042288158142581c20080182c0001e12003070701103540703c03403000c141c0300219000b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 43899896 1250 43898646 43898653
    0x60f0810080a030206090d0801050f09040201090306020d0b0a0f03080f0705100507050a0201140402010206071103160f0c0609140d050a020306090f0106080c06030121080c1b011d01080603030912 85
    0x2146d4440c007005805022821898079500c20b525241c0854410100510114001c1721402e00280640e40100205801140e004038119a10303504064150014031174075284910a2111480000d44007100e00c0b004025207400001840c584034903500061025031003064100c0301d9004800d1500c400d503041d84986449029603450340e594611880400a084542a00c1000345149102045c080544d070b000601952008850414100d076845034807086286003c4c1c808442c540c040030401d1042000369809007106542c1c03042614102480e159a030079140311380b450103541c200c800d224182c94440e2500c151007041282c0104240c030f1081c07001c2c2d00800e041c00412260200154801041140111000d201d80401410410050403c0c2e54901c40044c500f0700c01803080e00c1078510038522161803d880700942036500c65000a9444ea11265003903895211602c12940324040c00719207000c455154015203001440402000b0f00b4000141d4900054902e00800703040303942c0600c01480707040343c1030319400040e09440304e282c0001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 43901146 1250 43899896 43899901
    0x171b22080127030c030f09081207060510060f1809050709030209060d0b06040c030e03070c0e010501030e0309041a18100b070203150c0f03042a060f0810080a030206 72
    0x500070b810304031201c181ca10b6500741140000c01e5011094503842e9a15141c1243c01d051110401c83e0003845940020310315003d402c4080743c480039068014a0020f101d4041440f0964403000f20507031a4a4622034038010803602c03401c070a0940e21400071642c039103004d40c0311400415280c4111100b2120226428804555026418020f51603c42e81180d4042011500751250448030395800b00b44a1020b09418040d44d100e4042035686406508407451142d10368048030344a02c0203043c1050003040c9846080c1040698400201d05548680540c500c000000300040d464529400c090000410340030400442140d014425440142d417240601d50719000382d200081003038140b0f0412852a211581d008600a203410003000e401601c0200e045900b10001c0b0004440c00c2d40c407803a0b41c0c10307580310780e8010403d00d4000008000030000c0400c100030051040000c07a0030509010507481c051620180108030204100c50710031360710a88a01e480950000804600300c110780d0f036500b0513624180c024201100541c20a508 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 43902396 1250 43901146 43901171
    0xb1b0a0513050a18020c0a051c030507020c0a0315060503071d0c0304211103070b011401140d020912030d060618120201030e0f0a03020d171b220801 65
    0xc085002d854101d45054509242c42400052012102000e002880e00403501072040d8034140203c4110320780000c1511b00c043c1924286c1d1080d015a000c01d50086403500e400b05242c0c62000480c07540145000d07011024650030f503103a209074a40b1303025101180350788814021581c0d032000d10003800100900c0c0c2c112001e070441c0200040382d0902c014200d80c0900310510811010801d0031070301003000b908107459142c1c0491150070445454030b0385e0321092441c0c40006250002c000401c4a928100c428a8150040040400c001150031403880c208244080300103000c41c1800703d00700d80c010000000c0080c802d0354550740042c070841c110b40018404050031950b560041105540242041c04c1c50340070822100010742c101545401c4807015400c0283c1016038641c10b015500b81c040209121039044101190400c1c7c1c0b69250003955805004900300000c4c442002c020140000844524000c4540b1517130402d152090009a010903008a010703142c0f02c000085100060405802400000c1c0a00c0e0b000807628401040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 43903646 1250 43902396 43902427
    0xe15010609080309030d0c05070305010203070c020a0b03090a0b0601031805060703060803040803120a02120f090706050f030a0b15041d06120604020d0305040f08010912030204080a0b1b0a05 83
    0x18001c1010b5007081203800382e40d0341e0114120703070301c0f0b546c3d400c1c0b50b001040a42411031814100780c0000740150320005c03c0c818080d030080404808280708403414910551242203440007130009903840001d0340c0c03082c074000000640000109500c0801031600088480c0b0700e41c0380008a90a500003a00d090708600306010500d0f905000d0765000d8803a50300114a401d00e4030324007a99a02c9008800c0c44405a503c0c04200620382ca6011500d0751400300c1074000c1d041c14210400b541180054903086400e105803000028514003031820390708a260820191401e543d201814400078004c5007031895409007090b1101e400c10305140d00030304042d010014503400d59030b4400f0048104000080c2c031513885980c180413000c454200000342075901c154180d8400b5011040f910b001e5070623028a810500f0381e500340f07013000f2407902c0055109050081c001c24848000c50540320080d402c03842980220212500010a2000443c45409480c2c0d00312103d140341d21001304589000034ac0e81d030001a03441c030000d2000141800ca408650 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 43904896 1250 43903646 43903649
    0x90604020c12091f080703050c09041a24040927140609060412050d0b040c030e01150302060306010f110102030a05041416060c050703050105040605190203010e0711010e15010609 78
    0x2e002c1210300c080003000307000460002c0031b0301c04044c0c503900001d22200300002500d6076100081c20900c00f03008070800c5200408138007a0803900070518910359242d6800d01c80c0c2c100c400c01d0481c218541c03600742411440d0340541082126500090327408000160203001d450300801c440e9009040b070f00c11202c5694292410b0031000707460080ba65200405000208910720400d8104140703034105281d4488004d0302450140c103c203008941e000b4500306840c04a26095040440480c00c0e0380c00070030514007074071003004600a8900000e50031400c1400041e210354000c65080c6004000c60a00321003400c501c5030000e082e64402c6942045150701d90b400d000401116100c0c41040140b882c1c0586410034441c108a0840703c624815802044140c00310a006e1210500503031018680220080c8510715040c10f00c0c7d070140c80300790b403080b85540700d41c0c280f0144440c80b8404d807070503241c001c440c0315880d48030303800d046856450340c5c0c0301043c5035541d440e0780c0042d002c02040a001000b03004814225150725090000e02070344c1e00c6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 43906146 1250 43904896 43904929
    0x50405100507080f04060e06070201020310050a0f06050304020d1b050a06031404060b0114030a0c0813050706030b010302040b16050c030307050c0d0302070b0d020d1a0102060402090604020c1209 85
    0x204400c2c410307226080070310a030307204000d02c4118515030340fa401c2441c054a20100307480f4441c012001400b0341254190015032044c5c00410804400036624810b102c0d6100003032083d0614020341b40d1051000c14400e070019904540000c101501030a51511a001c2c00c03050400e6100010320040d0301003205080490360003000b413805040400c02c0101c6607096105c484001000100020742da444080c1e55030303000c2c4001009010042c14459102d00d80322641f50300600032211980041042a00040d000d20001c1100009003507010340540300680c9408025800303000362655040c10725400f848042500e80c10000070b4814540804285001c1c0d1549041c8a0301b028042d002040c00383d041008520007080000444000954080d141c00d10340b41010304040b0700300300858004c003058080c002800568040540c0160800d12000003003084200000502600c40b80310500c40240560032000014015141519000c2d030301020180000d03282080d4144801d0034000c80f0b10300420202d0021a0003686400c111080101c10400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 43907396 1250 43906146 43906151
    0x5010f0605091306020c030711040e1615091a030609070305011422021603020d0320030403032025030203070b0c0c06040b01031a010513020d1103010905040510 70
    0x800d00071646010380145083d202e9241c071141e20040000300c0c3d0440384609006000c7c0c0391201d49502d001e042d03042407103808521450401819846848022401826482c03e0076440c6401500c0e042c25003007042880080d410034440e4502d00050540c056011041c1c0380e81104231102d1340ca2521800300141040094111401c06203414014000704d0754042d4103030f00101c400c540344662052140c0e007100e0002d021200d40c0b00f0b22030000c58210b1806940450421080384203809030b548050902e20203d044410b005000003000d66940422402c440c5034800454015001c0c1c50046020f6102c14195a070340d04192000518403640011781816041c800307500784152881c00405100711520301c0d00d00079906d000780e4001030007160301d22001c2494202078100300d803015141981a941240b4050a1420383c80900344025622450110089111032080c10750b52410b032400205100c41001403920003034000e400088044121682c0e07507114801100c0c3c007601070750007081c0002c004607640c6014a846824551842c804030800d60 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 43908646 1250 43907396 43907399
    0xc15030a150602070b0c190c030c08030906030109050c070c030b09011d0601060e130612030e0102030903070e06060706060b03060f0307030b071b0b090c01090f030218040501060b0307030905010f06 86
    0x143d021030300d0402c83c1c1880c06000d4803507000b035030380e281008190500d0b0090507008000c1c10003040703003010010301160b0064582d07030001c50f514545c0c10b0303c9108644820307500090810062064850701c2e80015008404019018200034482c0e441203040303640398205440440300700040040350a824080c1e109401000008954162241d08081da5039841c107018030400e001c0990b0071840700740c42c0d41d246020620740d0010144082d6645014050a4298820023680010014403185002c0d500000c21110f6054000e4000c0a200c0e00d008a4035002c0e820180c15243d00c070104003d0b5401241c181d002c0c5401826a8414660f5281030240411001584003000c15000760030103013040010400c0241c020342d002c01242003c250004100c0344522200d12012401091466190f09000345c0d140002880b0000e140b0070307201c0604884d00c0c1d1849001600d803501c0002d62000341010f00d540d01d00e407100c51868001d07106c4d40c00464400d4580307034030854a030022580e100020341d4420981c0140202401a402c020384600030030414076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 43909896 1250 43908646 43908659
    0x70e070e01050f0a020a02060d05091501080303040b0702011107030305010f061701060c0c030c03030203090f04020906070f0507030227070f09090c0c02060307050c1006050612090c15030a15 83
    0x6005900303c500003c440428801030440c003e00190340450380c000c051641c4c03079031001402030091006840810181c440c6420760a2614a1020310506035242c6c8001117046075641d9817140a9040c3c000c00310011035485e0003405501d0924000a4803019100c0c0d10302040541c103010300004251400d40c00b1004000030101100010003203620b0803410345442d07141c041c406011604000550f0703542a030004200c07244041c000024958080042c0440c40011145407040460b030004000030390088004559005404000800000745851401c5e858940300300f0554000c941c1c0c0f500040d0a0a0008024561030008185201c0c02c140d0000c0307100b61301000b00d040070114102228001000c40d28140100c501841c3e44400f100071040c0201c41d81030400d58014507031540c80c64041d80044c1180c00202180d06184214600b0031800303001c0d4080c03501510406011303141400750728411021307a903901400701000c60041d001d10501e29200d41e000d942d141516401003030303580e08201540c1d2003283e006d075080e62014440c079103050042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 43911146 1250 43909896 43909907
    0xf070f05270a020405012d0810050907120b0a08070b07020a1a0415031a010806030120090102070e04050c0d0c080601060e0a05011806051e07050703030305060907050f1812070e070e01 80
    0x211201c1c0d20381541d113641c444641540149c1e25070401d41c1d01410795010403401c1035100b040c0003417030b0205080500100206c1c0d41405040b141c2802440400e4000120a2142000300d4005d044024001401981825031725041d50604451407103494105600015080c483e00361402a0030080302c00514040000f004500804411101c1c140e0f8076904000d5504040f42c5281c0d800d40002600e1101c800d080036802c244074801c0706556100640c01c0d80075001c0c1403030003d19000c0031000e051140f80c005001d00501300d0340307004004801c0f00183d405c641c00070484801241d00d02c1c040107484c1c060011038541010860301b0a04002000246a02c41303130400c41c1e4100c4d902c1808040b40807410807550340742002500c4015500c1019a01e007080c200c3c4001102001c1108020321000007101d40442e4001e4400f0003007615a0420310030f08510407500000803030400c10003510300740340307007002000d60a01720344500420300f401c50002002d10718032102c0c28030141e120880520440c600450900e402c030105091029043c460800040d10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 43912396 1250 43911146 43911227
    0x4050d03050406110d06030203071203200a050a110a050a0315090201200307060609020f03150105120109020306130515040213050a0807080f070f05270a02040501 71
    0x4040c1c440700840c0400020381c10408414100c8600c080d20740c01548511002044148400e9120703104c3c4901c0090320400324a5000348554059030340c1f010380c1500c0d1901c0001800c10345000e030902d02c200440c1a010030024010314034811300c1041902d500e60902000c0007511440364200900ca5003007410104001240031407450b046102d40600801d03401201e000503224949542c080e804010403201c004264014003000030160b46100762004c0140c1625511007108a014400b81c0d00c40042c030410110b044100718595040d05000c3c1450882e26014440d07101c6411120280c1c040c098294001c0b042c41400d1a000c80c1e0490403180c2c600381001640780181210300b1100d12000114000c03a400070301c400301ca40c600480c1c100030700320181004811566841600f40e4070707103e9215055840c05030980d50000d120f40030600000b05c03488038000440c503d0074001003021400380510b102c2e5250100d10314200c0103042402c585445040208030043c1c4413868100090070005040c1f50481410a64800305111030060900100c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 43913646 1250 43912396 43912423
    0x406060e010e0d0b090a021e100c080d1b03140405030301090b0a0b0a0e09010f030b010501050a11060103200109050603010b070309081f1107030f120b180a050c030405 73
    0x82c0311281c0385010070040c5440480240c0803240c04400c000c80c08000052050300c0503c20360b1005c0300f60b00e04140c2c0030700c804040456254000c90154120342100d200d03500c02d440c041d0240c1d4050345841c20449110040300c4000d510401e00c2c5150031742c081420750b014810000d62043d00511602d0b0340ca01503448603164401405071030381e901d564160b00f0085884524070386000c1c1943e0030045960710000701b0701a200c09003010886100d029040004104540040280c10803654000e041181903402e04006403081d410860441003004941040c48402d424100401c50081d405998903c40d005208a00342c2501001c0c65060750510069503010081070715014100c904483d003d040d01901c407101c514045440d10003a500284091081d10711044103000f000080f90245000c0301001c210b18084680314049500036241d0250110f908415036000250144c1a120300c0b030081e40500107071604902c0c001460703e400c212078042d10007070410100701d030400d114411150404943c0403268150301c0c0503911180d1340e408026240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 43914896 1250 43913646 43913657
    0x5030a0507060f090b0c06010509060d1502030606271003060b07021201090b10080d080705070210020c06210c0f0f09010302070b0916051f080903120106020303150406060e01 76
    0x404070340b131094031010054144a0096655480c19450844d0b0700c040a0003141c4c0300d0444070002c61618681590f068040303d5010144000030051411354500a4000500f219089201000118800c00316003445c4c55400d07442c113a00c50600c040d0a0103110000c03c0890881083c546449010b10010709403105507811070b036049a410407040e04803040c050240c800440000d00054560b030920600607400181081550f03d42c030201c680d0b0840001e400c0720705a01c19600032010900c20001500581003131914205030310301a0048842c2103402d0404a0704d15404903940490283c2060541001c941e030b00710006401442c1e5050890410868001818541c4280844258000f00004800c0d8030303a40a07406582d107183c0c100440c87caa030328100c400f403510340c600c1d00d00481c0251010300b004107070b0746041d0380c019000b00c00c0d40381c1d40c0d5400d015002040e100b11a001d800c070440c0e03200901c0760b190003080d80c108880c045d011035400f5503200e051002c1184c0c0441d910143c000d10450600c43d0500c100d980c01240c031860b001c0246040d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 43916146 1250 43914896 43914917
    0x6130b040206040308040f08012405060306040b09090d09050d020a06080403030e030403030c0201080603010903051c180503070507060903050319110106030305041505030603030405062206030c0905030a050706 91
    0x350700352083d0341c0010550b44002c100000c4403501c034600c1d102102c2d5410f0003400420303070201034501280411003d2241055a40c54240b100b81807100113150300000c094400104602c259001a260a1003101c10a03060b6000d10b0140e600750354001c92400050900752920322144507581d000a00f02071050080310200410314000509061090300500c030740c10343e10310990f942e45803a4280140401411042603020400c031202003000b07400c052003100c00303003600740e80e855003080140b900314412441016120760595407078950031101010710004800c903583c810001550303224840d1030114108503269011209002401c01c0403c00724a001c402ca0302092240c1c05460070304001d200d003d41d00f80c0c1300c0030f0f55100d166180890100415401038010007e940801000c0030361600342e1007040750544400c907400c40e0580c00c144010811070030820090401c2c07400b007002c201e00d540420710716051a02c9a0382e100e41c00103900c6890801640c0d40020504001d014158060442c170b149641319280e95051511610f410001092070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 43917396 1250 43916146 43916149
    0x103020f120709090317090309010806040209120304180c050403120c0f08130303020606040603020a030b07021203040f03030f05090a02010f11010e03091201020c0703060b010302040e07020105070201050906130b0402 94
    0x1600b0281c81d07940010030060001d03041c000c1c042d0441c01c628120f44444000407a02c0c2500000540d1403040f0140d4684405a40e00c005001c040d401440030107030460708040116040b49401d10240006d02840c410012100300d41c5400b190640d04542d104000741b040070441440840c035161130b000001b400c6030a205001584514020150f002094409032440d0790102d0040350050825040300c007240d009a084a101d0345030003040104172126480020351040040d0000c100040d03412407029407103c1c650040d15428180050200300c580c1c02110200d54011400c590780c13041582503c140700200d181e101c402c01c01868007e070341541d61980d140000c0c4c1071103180c0125030300444c800d0f5002c444049418000b448000342d00a02503540c1e8008548180c41005402c0103044540c3d0140300380d0716a485580001d00c030702d40c55600c84038000d00486603070740d0426400f0400071518082100e5014040c2c0041d0703000050700d2070311407002400c440c1d01405001240d00000188295415548495a20a13401c82041921a26070f40b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 43918646 1250 43917396 43917403
    0x307030513060608010905010606020d02031b010e030c07080d030501030f0b1503010f06050f0603072703021f02150c030612010b09041b090c080c0a0c02130609140103020f12 76
    0x40c001410b00b4206180803481007010342000c01a188a00c000703001c3e0340d4940c482642c96564282492006a0082c45021072410000c000d480c03502c0c0c40000000361000300c0014060651744442c410544950000c50300b040501c40400c0359050802841c5000c01807541140c2c0d400704c85400c0c0020190810b104007000c2601c02101c11001107451500400800900a007100102c1c0605483d202d0103105d0b040e0f01001090504011040740c1c031814541c0e50314076005910b220581412078010700098001c85c010b000100040c0c032252002e00d0144081000c01c0d044001404000f890404150113015100c0000814808080d00c40c1c010b40c0e4101b881211f044c00f000400d001810700409066114a600028030401c1c00180720030780c1029003020302c0c910500030056885080c80826186142500b5001a010b500056100941800980000a800e24160a08241c40e0f0000b40c001c41c000b10b0000740451303440d1810050f2140e42d205a807152007036168555241c4d0300d1500002d0341d131581181101e0080a000311000142c26003030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 43919896 1250 43918646 43918681
    0x606123c080c0703031e0206041205071a040f0c1e0504021c050a060608070c05060a0b120a051605030c090103020d030e10080402011407121107080f010509190803070305 74
    0x64226495140d1303a007401000d101e2407600c0401000030000340791403c607201080300c0f449603070007642c0c8403200000890b04981c82d600c00305040c0c60302451110a54050100e81d10a5405a80104600d210441660501a80b490a103a010400500140b58480480b10303228003180100c480c01c540c0142c88084040f00c00a9118054800c0c529281c40c003401c200030b04029a00c01c40503140e1070ba441d540079a43d94602600c0c0c0e8198000701038000d6000170300181075201c568010108689000d040c0043c00460300711454a4014450f004940c10303007002c41001d11010600c1c82c00070062078114010044a90460040381d04220706010190240104500007810b050041e4100b603000d031b101401a00503011983c0b40144481c40c1600c0480c0000c3c07065524400c14010081a2000305402441c0b8401d41ca07041d82045d18404818070710151a402941400214590300f840f42e1000c04922000200c2d441c68401c248604180c540740d41840d4490050812401049190b400c4e2a0700c645c55040000752340d25190329110200d00354 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 43921146 1250 43919896 43919917
    0xa06090207080c12040e0109020a02010b0d0b0f070e18130c030b0103030e0603010509012c0a0c020c0306090606090c071506030308090a2a030606123c08 67
    0x1011400c00c050440204203904006058507000000b1811900e298444e038406c181000c100d480043c010410207500801c403220980c00001400b0100308041009000c45100580381640c49004010b0f45124035160142e000c1713100e1608420318080b0200040c0d04500a05060350700d415500f002810022012005401b45500000742c102040e58a16020314500c0003400110001640d1803032041d80e84c1000d8050324180e640c01001803003242e0811070351800c0e10071084500007076034616400e40d0f028141604c500a014403940c0c0008a00441c07104006413606501d050301500030713480141001141e14003c640c050b040203045a55100d00d407140c4800c1c00d014021040d01074000d002c8010f01c0d0460419591018040b00c0c461703241e030075040d03555800303260300e40c0943c00020302003001071082c002c050f8000f28101180f82c0d40106000140a8491729030302d0885070184c0148182d0422490800103200700b18803407002d02c80d421003a03005082803002c03421140c510480c540c405000c018425600c10403149905407200d6585 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 43922396 1250 43921146 43921151
    0xf1605060f04051203070507060f02091e01030c020c0a051011010219090501020c09010303180306020c0a05120c0c09060112050a051b04030c1e0e0103050a030909051e0a0609 76
    0x1059199101aa00c0035a01150f8510035580100c802c2260181900c3c818046c54469030300b8148151100c102070302c44098456800c1e6420040c003102d40c0e849800c442611003400005c030800a00c800009000c907458020500c0a6502000300310045980f000001d0042c0c0301e041d00c1004c000400c65405841c0207111144030101d030350001c60348071110310b180c41e0502a20004c65446404240c2e48000580c0c59002c01030720182c00003880b0b401403000c00d010300840400c04070a000006103440da69121441244c009440d010400d80101c60031009015007000b4084a059104055a1418214a640743c5d0703107151030080f4a028a201c000004c69036805081d0310421940424401d000c1803a01647d01d000411040b10301d01d0102c00100007103100f40f030080c02901c09890b0300403120011241088002c00c1c0140c0f4411402126401c00031001c6544180701807054003e500c02d9000b080d842d0450300d4081c1c04080682c11400440b86024104203031400034100c51035130611004919046d076107071580081e002e00180d8000300910350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 43923646 1250 43922396 43922401
    0x20409050c030d0f081e04031128061d0a0f030201020d141801060f0902030a0b0a0f030c0e060d02010305060d05010501080d020106150804080c0304090f06140a0b0f160506 75
    0x10740002d14401c8895045d59a4a0540d0382c03040318424100f10303091a801d00c00540400100043d00448181140031040822030f0314034848000078103000000d10600312681e075005001e413000c0181d54010130601d4441135a081e40305105184040c2d94a840b5002c000c2d00b003d203000044c1c01414001c0d4129290400c0008050000484d200c0c041da24020003960720b60300b400109408008418418415032041d1001c002020003075914052800011f504090080c000e6507540315a01e0b401c540d0b0320350616004104d40320010b181c0e02d1450814100429041c0d201c540007189074001c0020035915100075450b140c3c0c0c242000074003500c0e0b540100784140d1300036100404a40c603201c00812030180020b0203203604070a9034000d002e01a00d6140350031014075090240c0011800e40b402040c000b80c1c81201800a4070405000c5170f0030300c1d6856500009403400d07a255464419540e040612003010a45d03d0f1042d44501580d0110540345854011403141c0f0610322109012440881d4907450114658000d0144542010440d113090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 43924896 1250 43923646 43923673
    0xf080a0306120825080d1104050a030b091209030606060a0e0909070512010b09040b1b040b0714010507080a0b03071706090d020a080910030b0306040302010b01080601090b07020409050c03 82
    0x1c0c4d0024a960f800024080101403030541c3d8038906601c10395004000700c1c1410640354107034014203540c81080c58541018007002c1030580f600c14100e0004e501400c2900c2c50385c01d000001601384010288045020300c8100100c0707500f914000350058003c1f1003038800d03a0b40c5868050b421078000b403809101c1d0390300140c080c080c4200300324005400d10541d40c00300c803545c41d051559000c2900b212001000c040c3c1000d184400203001c526201c00159100000f1110300304618101604001c00341c3c055009841c442e1000704000040c0281d0180300780d2840490703402001181401340d00500f40d013400410748410651100344000f0191014801c040042000c5c00380d010303440715042100c6844000407912a00c1d144222820740403198030000c0d40c0c000d01d0313811584131071034400b012050040c10038038a41d00c01f05154030780c5142101620200010351103a0b000b6400003641d00c8100c0e00040c004440980b4650401039607000a2140c10b80030310403540399075812200003c8410a61400784d00308a03201202585c54081c6c03c418a449 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 43926146 1250 43924896 43924913
    0x1225120c03030b0d050a0609050f060106020d180308032a04080604210f0807020703120503040302150c0d0b0a080a0b0a050c0403030e091003080c030409060e01030f080a030612 77
    0xa0364800d031028840401030380e0a202502000003005440c541c00100321401080c001d0748443c8103503018509940c40e80c0395221107207107030000c00c5c2d00010050388a08030503410a50b108241c0a1080a40c0000c40403103480c41d122071402d40406880100c0c0301420407104030580340883d8502450780007240e00640c441e5070b0b03000d10700c3d2154412102520340d88600e454a02c0b412211442000c2003503429141c80c103104000300c604856107040141800e0662240840c040f0125203525040c801c044a00d83d10380d07541e454240b03070003410030403c0681002003914613020b01040e4107909094030002d004a0500090a2601a002640a03c51a800494030b0b014103889401070107500c1d00032501c20110044e0603c02c075100c0e12100c1249201d103100240000e06a46100034481c80d001103483e401c600d0303104d520703d0070310740760703118110542d001040d440701e01e510014042000110750302410b4010f2182200d01d0b850380d851074441144008412100800c00f18001a001501038020381c000000b500086002191004907850401503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 43927396 1250 43926146 43926167
    0xf0405042a11010e010204030203070e04080d050114040e010c0807050c030708220e1515070c0b0307030612231006030501060303140a21090503030c030f0603122512 72
    0x10710350918040071004c52050003210704480d40a40101101803801042c01c000d4800548210f6180004210848007410315008807800780c41c58000c5024040c103e1810002100e81c0c209022085074108a0a24036881d08060401d0b40060a403e002d555010000001411880741880041c41c01030003203031015551342c0003401603800020f80740048590a845032071040200d413045a401031a0701100d51001c41604200441040015001d258a400e00069542c2c0b00340c0c60205801203000140040100320585a140c044c0c00024002112281c00a01ca1503d8003591413110f001c2603144105030480c140902103040102018505c010311003000225201d01c3c2007406000346120650000d000f000b048103110040500300c03414136085844401143c4001d42d046c042041c5002070f480401603941d01c00c400412000e0006611984050610035941e14140b84000b84200024081030700991000001c1d203104202d100031640c101082c000480101c8003640c040c0034071940401002410780400480c207581558100c0c2881c1d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 43928646 1250 43927396 43927427
    0x10e04050405251a0715050a0510051903060513020a06050a120c02030d09030318081b0a0312020d090c091a0103020a090501050702030c120d0206060301020f0405042a 73
    0x61084410303140c0c52203207a680c1c054106080003841619a10740208130003071101e07902c1801c0c3c40120700300c81c0d8000c404840003191300781c2c4c405440f2001c2141c00c039030b54403480e8054941287e5200000c80b00c0c078249400c040e05400014070044c0d0b5400462200e80300f4000395001035600604000304c89860391030090032904000b0300c40c008503140500800065005002c1c60078654400ea004508041301114405e01034002d8040c2a0241070f5100b45241c8141c0204420140c101c0c0600100365440c802e0178816101c1b81441c007902e0640c5e821628008000940c42280c1c810011580390016854012002a40005120700d8030010700c0e210005500040002981e000303101c1407150840c40c110024407600040d400e074402c1030800c1c00014070300101400366602550281241034000f508558000144030085140700000d51817069031a0b203d100700400140c1c1c104040c980c440b50580082d0b0400000d16200b1030280100c0c00740342d105a4458580140207402d542150070f0b0900304500b180303000b1101482c003074800c4114182e0384 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 43929896 1250 43928646 43928683
    0xd03090303030b09060f010c030c060e010204030212060c040e04111c022e0309080d0c020319020118110111010c0503060307060207080607080606070609030e10080906010303030506010e04050405 85
    0x1010364030b403210302a8071480001c0c201c00b0006c42a4401114400c0c0e49502c100c087c82460010940402e409205030303404041507400041c1c9c3c41d401c6004006108001c1e940010f500d6000804003d080e40880c020340b000c5619000d60310a1a44483c40e00c040202c2407041c3d09504500c8240440603003010642c6d44904240c003e850180c0d00300c003501c100c040202c2a801e480b81403030182d0070160135050b101e6404604214061007c02c0c3c1440301c0300c0c103d1425101c1e554070480043c0e03c081411084041482c036400320114550008210145061500700d80c000b5040c00090400700c004034504e04564000c050140850301041c00030488035030f140e14040c0c43d5070002d03110980240300e849004501c1500024002054814010003010680e40f21482240c03000300040c02e560b0044001d0200400107241402100d0625110340c41d010b09100c9100e0921410040b255816010445e50f0000d101c0100004900c0905407a054940800c0541e038500045ea00380c000c035214150814903000401051003008200c401c100c0409003400f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 43931146 1250 43929896 43929911
    0x105040209030a1203061214010e062404020f030703060e010609050919090b0106080a050708070e1201110d09020306010603020a090e09150a0506010807090612050c090d0309030303 79
    0x1880100e02803803040729059407100080d03802103210b2610000e5203800d2494082403007901d40719126a10504148219100841c44445410910303003800741d086112030010081c107262500c0c2035520f03480c41c80b010b0003502c0d0203406607480c00b540e00e9540450304011003d800296807410705000c020000d084034031035890070409000001c16400e00c9290400200c035402001c080080e10ba04210b02e03502c40a41c0e82c840c0d2807980e140490800109142c1e5060b008242c030f525150010320306014003005035140106004c08010f1524104503442da00014200a0043c0a595a280c3d8101c11009540188410881c150700c11001161801182c0e4181d0403018042d4400d9080d0750707050742e948000741c0c01d0380280b00c19040402c0c0003000501a90600c1500f20741d01800ca4000c44401c6204941d148103050021707074400c100e40ea02d442c10005256004618160469064a13101620301e14002c2c00501114860102000884d00d4401045c004040364003034501883c00201340f0b4035400014500a061500c45100480c0800c0c00c0c10749 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 43932396 1250 43931146 43931149
    0x109090e0c031e0a08090402090907270b03040b07020f0322050a03032106090504080a020c090105060406030e1c0c0203060f090307060207080c0106090b120106140d0311031207080105 80
    0xc0c803d040007200010000c0c00082d540301422908a480c2080c0c0003079090164981542c1c415084500584103525807422190011102c1900e008000c0c0031104200462001000741e0007640c0101d0780d02c0b9402001c1c0800d2034403145012800d20701e0680f00c60140744008a0b03448480f8048110b02d0421544448060703002542c2d83c428031600107003512014003c00c85094940c0c0b90350f1484141c0400030741080c0380020b0b119444071040402c0b41e10980b0103588184021444110698040025251091084403e80c404e585000009892441036002340000c05440c2e0014031115035041112030b0350607aa0804401c40071501c1200280380d55290755060344684510400300e502c804240420f14001d952900245260507136a4490780040d40c8019000c0b07407030501c2085001d54200080c85040e000d23040c1c0e002c01182d800d407168104600c1000640326000c2e2030745007100c1044000c41c00100c50011000c140c0c2c08113042d080c80c0c02c050750040b481d14036681c1240000101900d0341d54509403420b215003032548800f0401d0b42c8500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 43933646 1250 43932396 43932433
    0x5030d050411040c080f27030d0b090606070b0403050901111c0206160e0d08040302040905010b0103050702030c060f040c030807081c1e05060a08030706020301080c0f01020613020109090e0c03 84
    0xc3c3c0603003038a42c0700d00100b8154000368020f4040010b28500307048200b0b8070307e22124507590048400f0590250340b011030044500e0300e500c0c1c240d04040d04035100c6090407a103854804234404003030801014481d0000380350b0096406060010700101d00441542c075900e200b003200305400c1c11540403000c018010400020611801c080d0092800059561003ca01c40c072007009000c240c100a507000d440b898070500c800801a1303641e02600300c5a40c82400040340c40418080094290384010345000b00350f410600900d10034910008540394042c4041521426507200c038180f000710002e20345c002610705040011301e00c0500136500b009060f000c0c9401c070000e00854128500c003044802c03041c41801c0c00f140307014521907040303410340181d50059402001030f07640650f030725155851a44180380031141950040010052800c00380b06802c032104068a04101043d504e1000039203408005000c2c00500302003c2061044d640f103684400301424040c4410802068a600d50030b40e9500782c0c0301ca49120f8451036408040410011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 43934896 1250 43933646 43933651
    0x15060c100c021617071701020a03050714070b06040209040504030f1403040b0106050a0e060409060906050a050315090a08070c15030908030117030f070605071b0f03080405030d050411040c08 83
    0x51000030359070f04106413040008907080c90850340e403040c04400b050402c2071300c090204801c0160001a92031580c0b42c03019040d22b03801040c3d48180500000604000803815044030304085d403110b051016991014001802801040110343d0001d180204000406400c8030b0040d614100391348a0340c01a68481d40807000768401290001c150041110041046600900292000700b95505109041d05084401721700142c106a00034000151a003408107d003e00a10480028201c240c2e401c0f22020f082c000400e6407050a22001e0a90300c1030302c03000681010041c4440c003d0103501039182c0d5070351102400c00000f0114a4010389002c0901b401d9604100c602074883c03410703000d82c0403090302e04584c43c2010310195400780c08800d20700d90008100b1050300181060080007460704ca5180015135040c000030080501c4441a0100c8510420400800102d81d4400200f007820f41e052a0251159950b803600d581503000b200006201141803a060100300115480000303032040341600c1c01c0000246140c000c03034006809 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 43936146 1250 43934896 43934923
    0x20c060112120c0303390311090105030402060d14071403040201080414070e0c030919030503040204020f040e090703110303040e01151103040b03070315030203030d0515060c100c02 79
    0x10900701100040c000e420300d1026070700900b800998424007040900c030000d29400c4191906c42210000d0031541c0e00c00581411101c2d441c54208050198528808858419182418103201c00070000a003103650b944210b0b00d40a107111418010004110001009200140e6140020880d08052012851031600540f03101c0e58059548040b80e89464480c2c4001d40302401001125019012001c81c42203140c03201907015401091000742d8a18020f00c203582000095001d50707200050703d00b010004a540102a039410980407078005a5440003820903803007510a80c2e0000c1000281a0b00f000300002012450904603800781d1524205818114209612846503004140880ca070400061004240240000d0f804840c1814000e00b00c802410241d4550f4005901a602c007110000400c00c43c240d15000c1c022001e2810404000da040c11640020744901414a840c1442642c440004d0300010140784602c1898001500c0030707903902c514101e499203640e4074008201e01e05091601000921348005000c182c0740c4103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 43937396 1250 43936146 43936163
    0x3120a0c061122030b07050408060a1e0c03020d05010b0412030302090d0501090b04050d05040b0a0309110406080c1503090304030212010605100e03100b06090105090406030503030a020c060112 84
    0x1030681e030351802482e0052500ca03060200b406400e103d02e83c900d0114126a07403003041d04200ca451494402c042850040c03a50040102c20f0100700440c003c00291a500b01240d910701141040c2c8488d20300344000c0584070344d00065400d105d0420411a0036074024070402d00c0c0020144103603070301d492040815205c1c600c103c01c00d060070028200d010904ca98050581140e000b440ea81c0400d4035921001c1c00d60b5405003064a5400100301480b0030884100321035802503031142843c9d4107040c03803c55078110f18000e500c0100c0905850f10b201c40c0030001c5030720f0191001e0200500800031240c480028a688011406425002d0710400c0007515482440300b0a4030304c502442d2008500c0e15084d0350900880e07008811907104151340725480402c440e62000b006042d4003030259a441c8031200140d042501d032504490074110003910348008240d0315110441242c80781c03202800d250395203101110104008015550016045e40800b2050007000604e9400502100800104458a990300e5460380100c410352031000070000007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 43938646 1250 43937396 43937417
    0x10605130209030106050a08060610020a0c060c02030a02120609010c090b07060c0903080c0606010e0103140103110a0801050a0204090b090705031302040219180611120c010b0d0c0503120a 82
    0x40e680c004046180c405000070801c9903030307800481c201d14420b400509081d0407107010403215003004507440d41d400080744010000301219458002640016004400802ca20849424107544040180000c5643e024054070840300300c0301d982c181c0344d0314241c5a600081d428607404510440c410025903007a00c0b0004030300d41c41c04241e999414010500700920005010107520000f020401e64000340c600702c081000a840b180c6405000102812800d0385001d05248c5041481c0c0c2c41c0c07010b44601c00e410f482d80304042841419900c00080c05004480c0d004d49045d40c04c00080040401882c0c0140044a08102050100003440d400b04008070030708880407000a90140000b5103410988010850124009880145000480a000c03805400300d00c4a00c4046070300682541c2840d56490b45010042c1000c0c07500d41c0d14507420000c5280c59400484501e04403400c085000c842020080d070282041d10002003849504a50783d1a110441c401035118492007070181c102c0d46030304514807030115926040150394001d082c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 43939896 1250 43938646 43938679
    0x30302060601051e130f06020a030806220509010e0f0a0506010509010621020f03040302010c1413030b0901140f1806010608040615051c020406090605060306100201090506010620010605 81
    0x1070704041140c1240c17540600000032244400e001050203008140c0c05030408140c5400d0180c52948081c00c07c90140284001808030290380c00a0310b140c03003001c0400030915407280309000e4090504601145d0450007601081c2e007c20000280191240b403095041c1c0b281070b030341c0320f007040031070031091140303501095032810703180c02010700800c42c00104503081d10014104603000304000d100f6041282c040b00940c0d9a0640c400320241c2158003500311246007404030b80707031100c2d00c414001103501c035100c01060040c003280460a00321003034202d0000c0b0b01a410440303900380b602000180303110100f51a401c1c0305450342800b00c0b01100c8041442416504242c0702c2d482d19480300d81c1e0302001401c80c0d0700045048518160301049942e549601514075621000c03061455200d60700412080726990b071304c420b1034286402410001ca40794001584e50003101202c044402920443c4280e000d4042c03d01c00070414090000049a4140c0001c0d62690b150b64a6501120f03803003a00c02010b00700c83c4280159903100790740d40155940c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 43941146 1250 43939896 43939957
    0xa03090801050f180f010c120506030106081b01030e10050609090f06070807120f02030106020c040204030210030209121c03050708040b0402060a050d090602070201020d0503042607081303030206060105 88
    0xd1038440200c41c000790400d005c0314219400a02c0ca50002000600750100009103030203003540102c402c0b40200001d519002d261a034a010302004021000300c9200304204c941c0c000c0e0b00070200314800d402034942030381c040b00f042c2c801088112801403080b1114008144459000146c0d000211441c8008115585951341c5c02d0390340030001000d001c2003051154401c900d040c144d000d40045544040340242e00e80d410081c02904000321044454050b510500080015030b032000034544100c1118200107a686442101040003280c0215400f4040e20624651403a0034903141c08550341040749550803c05034484080480c1d9110741078801501001060300420050b2800304c2c01000800081e040551502d49024441000d030303032010a05444190380030961009558061003904c100c0340c040c1c54182d24515059451380706180c1458a8007400d10006160461510311006c1229006908031100f140c0324005c0d080c0c51130060102d070104400600940300842d40c0355000398255020666a007580f4a03110742c102092802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 43942396 1250 43941146 43941181
    0x51203150904060e0307050a020a09020c1c02010e0312040b060a03080702150910080f0106020303130f1505040602030405010605011b060b0f09090304030b06011412090703080c0a03090801050f 84
    0x7461544d4210015207080104000c00c0d400e032041c4050034607510280104540c926880e4171100710750b07004020700c18180d4001716600c01e0368440d20703040d8880c00c3c021100803401407040040c20101d62000041d200301000c40b510310360384940e100e03404500c0c1c990b80788002d01c0a0b43c14617101c000c282d100c05000c000c1c01803511030600030040300c1e4a681281025407820000744600d1001102a004c01c0c90507052004804034542d1050140410f40021842c0d41825480c000080882c000c0150819841c540304d1000c1210410804802c800941c1041c41707070b42400c0c04c0250084d801518200c80946c80d00380006129400b5010894581002c0800101810440e0300c40b10003070100000d4050780706000d2401000160380f5880c190b8083c03c80d600c02562178a0940c500046001d10103818941486030a080f4504491501c804686d841443e0281042813031b01c585196929214007600300170400360b0081400c8805601c005070458055009680d00205180d03241030700303400c0701c006845a28410012030002140310700388500c4d100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 43943646 1250 43942396 43942403
    0xc050a1b0206041202031c0917010920030c090403020304051203090306010602011506090803040303052b020a0906030203060d02060307020709110706060510080f0604020d060b07051203150904 84
    0x1080d40c49a001a160380c0c82504207040151468580b4015400c04000d80501a010420100414020305c40094000c010511401c000325800840e9500350b0038007074001c84180c0f944203140c1c96585010220014401c00209070080c000d11600450a6091501a10b140e0203543c02d07802541c5080e080509001e01c00e828523030103034102c0c4030412a503240c030380701040114002c0103150300000f401386554180342c011041a500c250b04100c07180900348100c4001004803401c403035050401700d9580340e0329655084107400c1c10344070000810856466440141c0ca903002400d56500960360140441c0c4c40341029000c9010a0383c1c402c5e08007004a58400060824100440d000f2071180100d0342400d50fa50519020756001444214804c0c0000c560303003082001d24050030010303007400c444103a401e00360b6140c01484028001d0020101141110101d00395480782d50458030401d81c60f90007408070940722050018075911420741110140724224100010980381c2d0140e23409065680030350700c1e5071401107041210011018000340c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 43944896 1250 43943646 43943687
    0x11502070308040909060b090c12040212150f100f031506050901090e0d08042f060406020105010f140105040e090709020d090605090102180d08070605090609100c050a 73
    0x2002042c03001000e0700c010181d82d103020611056502d17040e400d075146415024041d4a580d4103009540b416130090300c0c1c1c9200920340340540f07641e0f0ba0001951400c0d2907841d030720030340c011030b4200d500c83e41c8001c1c5081c0c0b0900c0114403030211a2940c43c041c1c06a0350540c0325020050300c1c025810300014184000e104080c840031740c40132442d030343c8480004c1d4a00d2000c2c4d0020f006070383d0761414080f07500c0c404e12030842d8000e4503003000051460a92540c0b215204074260510340141450010141c5c56400d83c645090700101034001625140c8414020340241400e001d092144e640c81e100c0003809940c1d843c51551706601c1070391854101381c6007a5055003201805002c0f000c0c1406400004215036169102030610200210000309034400c80341000d500f222005800c410f0264010401c049030010352450009a890f020ba43e04007030075001e0700b042c070014002d124000340340c00e0410342805018500001d52034018640c0c001a140c1030b4104e0100e2008540d600184c1c40c000c90030030700080541c940101c141940584d02c19820 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 43946146 1250 43944896 43944899
    0x2330906040816060f14030718030605011d01080c0d02090417030406020405100e010503060d030c02040c050a0207150c1101020307050a0516090204180c050712030b090604021201150207 81
    0x2d00342803000300700500d40f180d104490304010480e8000c50441d2803180c20b080a9000301d50070f2001c21070340d10004040b00103108100f006035440d55030b403a00900085400460030000c2e0b50f10b030004004040c0301c41d128501d4210840c0000b00e0f840d103000c2100300c0701c02c1c1d0040c450b03100707042e095090210803200104151280000b1510303c00d41c143d40702c0300451180b8030400d8016030b260300340004c01c03002000d0400a20100301c443d803d15459a40c000084a8001000701d420016a0385039240485210942e02c20081d0401e0034080c1420119030000c019240302d280785c1d0250f4008545401c5040045800b0011190009031044480720104540d84008031044d1018410340c1d01d060f407281c0394549007100042046503140c2c4000d1007160b4040c0032880c0a006484c8450341545424503188940c250b0041911548908550b29002c915685025204541040b503021215420455140d40054018500444118050341b9501c0000365285807030302c22540c105c615450004516424404c0c007140740000308402c4000d42c89414030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 43947396 1250 43946146 43946159
    0x10c02031e10050703050601090302040e0c0a0311040c050a0f03050a0e0610180905030702100504030b010902180d02030a06051b070501050910020c12090a090207060203040233090604 80
    0x8050445030400c0000c2c012038440201807012250010903030340c20036181c9028460349a134000c0b9240101c82e0100c034007150070150060018102131480385070641c0003c600c4400010000602c0110b003c520007180c080124498002c02660144202075401001958102c03401c59468000e500c002d03041a1245400150600c03940c584501e0941c0944007030801510a8600308840c41800d003030f80105d040000c00900c0184640e580741581d80c040c648e0020b2003184481c01d1403000034410b01c1607900868228801d1501540d5540340c0e10003d503c01e07000d403005044500c0032903d003410400c1140c0c45a5a001d8024401100e40307446a400030b0a0142c801001d008207041305191140c100005000840d0091300006410b003490300b46140740c4903e00c0c031040301c070034010310004c0110040860142c802203954011591344009000c00074441310b15542040c01054808038044090282e10385c0030f076100f64801e40f0402d26040c3c5420140c40c20302070b28100c080c1c415003001c075041c0b2141c0281015112681028080e5401d003a100c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 43948646 1250 43947396 43947433
    0x2090406090f0803010902070c050307060912140304120507140603040f061e0213120201140d02090a030f030f0c2f0d060507081b040b09060706061e05040212010302010c0203 76
    0x1c1c00846c4a0b6000b040043c14064040c5d45c00e40244421801480150700d08040039214035100d03c902e00010105d01141400e00c400000300b000e030301c4c11080690b581c40d5120501549440d2603008203407058403403901d0103d040008000000c50962004200504594881e9a0741512000301d482c01c803041510380100040405001e45c900c08115031540000da1100310f0b200c01420402c4c0305038440190b4610100001c000350f6001071804400e50364510845a0742d8807045401d81c080c1c42195021754100c40b00b51400818003180c0b40f402640e4a00c03aa4500003400503044088503800000080031b0300320000c1c1c0300c091503180701240f90814000380d84e0820407d03411070400051b01039a1703030703070015910b8a0b200c4040114441d03004198551100202c5074071201e5065500401185005502030042d03400e82c0001c4040b8660b0f00d80c42038a062582c800000d006850300c035100300c2001079091105ea400d06201500200d49440c29000f40c0b40390316007908100c0d6486e071844c1c004540b0391000303581c183c2c5c06020301c041042a400307807034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 43949896 1250 43948646 43948649
    0x3090f01120903050c010b1c0204090c0f08010203070e0102010507020d08091e0601050f06070f17040806040507060f2d050408030a050a08060105030402030a020907050c011e0f02030402090406090f080301 89
    0x20340713a1503280c2c800c601c03415094418040d481c42c4206a000302002ca84618040700e00c220301d405480c0000d90b00d41c58a40034501e0402600f1000c503030f16139250001642c2c1b0b0150000c41c4960580e82d24080074200c40da0044e402e0780d4080c2c0d803007000b5030491404841c50700e1040f003020b680482da4074116002142e039008080d0311581060071340b0101e604000018070071820010300103134110405582107450116207445200d510054240010700d20816007681d0038088080000f590701600501d800d80310103051901e07041e42d8404451281102090032200907222030ba01840b00140703120004840e100d1001000b91032014441d8100c4c20800a0290034400410340100410103410324401e01c0c3c44055131542d1030b100180070808000e02d01810048100308000058401091021a1560540f40c41c0c2c815129010180d4240c09405040e0341d0540ca0f18a510440d907061805050303040310644000c1004013440c4c1038a005a200c115800707500700392000b021034001202c2d54815070009026060100c3c03900e0f00c1d43d84001c12580203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 43951146 1250 43949896 43949903
    0x108041106071505010e071704030203040312020a02040b01091a0c01110c060405061506090f01020109120f0801050307030c0b03040303060b07200906010e061809040c1503020306010203090f011209 86
    0x40c143c0e10a010905205031401341441191503040b525207004000d2406022104407076440b620f0b10085405c040c0200161390203035034042450f100d0b025008400a59030480345406030312442c103012203e800da50007401c0380b80a1315038160b0b210282c140c03081000111079011052a0b03243d903580d4450104543c010b10044c0042a041c10003030014ae08050408034580340000e01510440012250000043e5030703103504841110105079000040a0880070050380102103880c0003904502030030080e4440540d02c0ba41d07805000c0300d29150300e0502d980314000c3c0350b6030344102c2c00001e0440100d56000d00c0151100405140e02511030300d00421101e455820100c4035400203e003c944840d140030b5130700c9011000d4400703902301017026600300c401c40c41c252000038800c040502101c1c1c02000c000848a43c40c0c030002c1980458460080d101c4a8581014681032000501034401e86122480c40c0c69040b08080c0b2038000c40f030092005a0040d0b0600700300b031080000001d404103895060003000b40418842d400140104030410f0701 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 43952396 1250 43951146 43951163
    0x50306090d0f02060603070306050a090b010314010e0303060306010e0c041d0609070513051507060504080702120303040f02010503190507180b04180902030a02030a060c02010605100c02010804110607 87
    0x1c034600900b10440c18045002903401c0141003013a02c1c0c500056031801c0345d4000201084a0301c07503111401c0200703641d20340500007003000c80010040c421100da807144180c03400402000240d01204545441e800b003079510390b500d0303005403004001800d030008100b40c025114080a61602e40d0328a1140e40d0746407201642420b2141d44002c0014524124198650001150400c20314040724440e035503c20301c3d2038bc01280e1041c00c2a0303d21011054a50301640c51042d807000d0100440c0c289810001166005500100e00c181460a03046c5801c820100941340603d038003e51410101000360300646107600024541c1301d54062840108031989a10700a0780d02400c69520b030f007813810240a0824051000640202002e01d104010420490300d0b8203080b48c81c550030b984030010344600103100190a140011170040d5042c800c40d2140313030620181303500800181980c0d8000700b01d8a940d45c001d102c0c1810101c0010404200f2160342c040142d401a1201030744144500b4070829842901e00c00205a81c0011005031500c45 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 43953646 1250 43952396 43952413
    0x60e010e0907030e0a0605160f021c120f020c0105100f090c030225120201020a05040b030a0e25090516030906090203060c0703080a02040503060412020a0503030c030a1505010e04090c05030609 84
    0x480c46024110440c2c80c43c09c4001c400003d90041d50b1607050300c1241c000c9070440103c03402e51034861880320302c00802c0404103004152480003180003941260380d01240715460440442c40c428041e031402003c564804c0c400d501054a030a40403402007540c40a140305068082041480d03e90301c44c2502c0c2c01c8044140d01032281d20002d424010030424190603010f05581c41000200034140e007140940c0d08441341116041e98070b541c3c0d550340d40301038450490401201d03c41c0b11a11311080c29814601034611510820b000d410550711201d41d410384034240c407c07641003031020480c0180301b4440d41064218902411001ca101c6242e640400e1401e03070704075120f440d40480410080c04041d401840c40d034014035003060540c101410500042c2c0c541348090001449034000342e81543c2864000d009410042e90090140c0f41c0768030b0100c00c0c0040541c01181d108140a10b080e44542001c0c0e00e00035110180c41040e980c2000c001d0103201440014034100105540c1e004103014001a1703a6000c011079480f136030100c1b01400c0251f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 43954896 1250 43953646 43953661
    0x6040f03030e030c1e01020307150b1002011b030203060f0909010f0c0314070503100b18040c02010c090302040b030102040f080c01081006080408070c05030a06090b01060e010e0907030e0a0605 84
    0x1042c0100d1081e0800c600500e155540c003620003603285503020300394100da14043c0040c2c0c81e603c2000c600410005180e0550f400304c81c1e0795405403124641c191411401482c00c3d0608030300701c5554005400d00e1b041180c0b00c0c862114401c1e030280d0f91014010340165070103850100011141e180c00c0b6622149030303454000307540102e80c40780a1510708082500b024083c21726a01c0402110610007807a203810040c010001920801c2c60001910007402c0385003c090740c402d100c405107400400569076003030107541041c8620211074414440ca4400f00c0ca2542c940c0704042c156403c1001038580700307809641c50740d002c0c00040350452040c0d81210082034510020100903180c540050100c0c50018000701c492070f00388400300082034010708007590080e403001031907030798112500d08180c0040d0941c203e15094400c00b54940204030fa25800744649d240104000c0c40180ea8070241115401c808988660000e10340981181d558107102285036000308141c10089000581c10360b8162501f0040e90003030311115118410701c01c85 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 43956146 1250 43954896 43954907
    0x30503072f07090f0213051c0807061b110c01210e011a040506010804030c02010314040f05100b01021207060e0102160b0a0207020607030806030f031606050606160206070f0206040f0303 81
    0x40313611244003503090100310f1400c1101502c0390b101c2c5034020b281007100d0481e943c100d1101c6c60012503014022544465042c14480c0081860b04213071401d031140440105902c1380501041081580280000c0840c111404011501560600d0902e0850074601054030080840d901401c0015200d6000010700c1800542a41400c900c10200c1603000720f19043c02e011040e40c0c0038a2950340281c15041000d4001011b01c0120f0041103c44080b8400c460343c0400d0004000807c0798400f4487c0c0141d00b2103900f400c00825410460346180581409070b489100711460010a080103000114014240002d000000d0045035003aa800440c842000341d00c8800c40004119251307002c030350840ba550342700b1410000140d0100d2880d20032048041c050004c6100001c036036540410441450b510001d0a403070300d503441100c2d01116103218640840c3c466040400098040c2001c40c00c1e10980c06010201c001e1052003a024003480b540022010748115041c04500b0026840f80700c0180001c12031200e9030b40d00b803440d42c24014034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 43957396 1250 43956146 43956161
    0x3020d0b0d050307080f0c06070906020d080906130201020f01020c0c03070906050a0308071b091d010504080d0207050f030c03040f050f090402060c1e0c090c0304030503072f0709 78
    0x7250303003400c1c040400b155000054555040c0c0c0020090781e500720714102c18116020300301e421120340c8110320800003003039801241703107007101c00c16003c9400c0d50200600c01e640001040741d01d0400756103c400014030400e00d81100d00c00a60044c01914108000c915001342aa0302582c40802c580d0301504015040d4141001010010107092808004040c108800190504190321002d040c07103030042115010301c9502c0d540b070300c1083c29480803054803da603640d241e800744c5100c3c0c513192a41422141c40781d94443c1d06014940c4140c0c1d22500441c540142ea000b800001d404c0942c0a80d0a40702d8000030101c901d408200178628290f01c10000c503101e80c54900003001000f090381000340608400046d007a21070325111107641d08141c0c1214240d03260740c0c07152000c034a0400074a01078946147c403a540f00321030040224250010b00801e81d1546031aa554100030b0186110a68004000400400c0003800c114844c0c1200400044a184403080401000d281c50740c140709030102000e5990007824041041c002140725448 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 43958646 1250 43957396 43957399
    0xa060501111c03050402010e040507210c0c0b07030612030206060405010f0b09010e0609040c080114090c07150902060406050c0c01090f030602090607060501081f0b0d140c0303030703020d0b 83
    0x20392100346076860b001c8012510080070a043c3ca45000c01c085a005141e0381034040b4024004001c4c40c9080000101120450115010410b40d01d070f138400c10946090060020003030094444000c2c10390541d03070381045003400800c4a01010303940d42010405403140e51468a0042c080d500a10142c1850700801040794010391006840e250300c064104810928501075405014003403e001c42c6812081c0040340261040e100b0080d445441c1c4100180c01c5500544032506903010300d40b0008014030340310240300128000341d84100780b03510117208000001d007021182078100b0b441014003007038090903039011074143c2e08242c0118010a0002c0f0321401092810000080d081201b4030b442d001091070410702401c945090700001e8250b50300064071064507103071442200c0c04560701c52020440c940c1d40d132041d80e45030708041c03150050b0303140c8a603950355034a151406541003090000307244d00c820000a54413903821144071325500040f401000081c510558003400a5845002d0584000d0782c0c8400c107411190458120b4481d06 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 43959896 1250 43958646 43958653
    0x150513030906050c010e061305010b030106060e1201020c1005040b0601020106050f04020c010b0d050307030809011112040201020f0604030207051011120f0708071208010905161d04050a06050111 85
    0xa20119600c0850901262200d05250b565078001c400c0c0305024017078080003c0458072504042c4003401c01c90454203100c490144c4000c10891044104140c00d88106210b102c0011b03020743c003800c14502d800600300d03000c101c030600010310340b03580428098241039a00c0807034000665144104024000c04010550b4030480c00d10003040403509010004a41e1701100f103c0301d0040341e000c9046020403c0950011541800080c0018000d0b000c81c0b404954075442550200d0015a1040114007428414010000301c0f5200f5184a42007104034202140207510040060b41144209002c00103e2002841241d00440c020307806000d80a0500c030502c200301e40440c128000f04034a040301861801404121010200790014005603100d4100c002d40005000b0b030300c0060886100041d140c800c100c00c042000d2900a6191108100c0b6070f40c1e90b000008490781150700703810800503c0030000205202c1e0010300c21070300c0081050a00c88130440b001c1001c031a011036031280705964980043c4401e42e044034500e0350030012030009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 43961146 1250 43959896 43959931
    0x30309090b18060d020a080f010c090f050f01090b03040308010f060f05190917010203040b0a050105130b04060f23040c120c09090905060a0e01020901020d050904060e041505 76
    0x400d0b5003078605452554010092008541203581355a0300c40a00394005054102e2a03032508013041d1106130401c41100360350320f465640361080b03028440b490308403902551550009403400050046240081910504020881802082c03a2944070302550007580a076a800741c25604010807481c0a40e601d400c8401800407a2404800f4268410304444d0710031140c04640061403060101562446c4064100c88030149000d401000f0700e90056006d50f101d43e00482c41c15085450341c07504031045600a01a8540200300320700c1c000c21039502c0d5006070b403e0707101c050400182d039580c490007904203540542020314100305a0326003e01c1c5525540d6000d5800310700310340c00c100090820802414984007010485011602da03010051582d01605403100100b1031140d040c400c10303a640c41d00d2600c55004642000e003091420081000c0310a051094604081c0c042e001001800718103c41510582c01160b40030350b01549400f0080b6010441d40c5903a401144230b8541200001d9440311040107a0750000c2c04000200b013030009 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 43962396 1250 43961146 43961149
    0xc0b03070e15040b0708090607030c0c05010e010f031a0301020408070303020c04050f01050d030207081c020d080405060106050f07060e030306030d14070803130f050706090b04030b0105040b1801060504030309090b 93
    0xf22821240c1c0d150102c0d50320041c0b85400e140d540207030b500040e840724000c6060070516402900c1c181415100b96440203440346c0310313001901d55045042c25a4006600c07640d000b20050b0181d40104024210300101c5411880071200080c266030050300940c1c4107400882e020010160104040841c128041313409200301c0c42c00e02400e03400c0d00c03014803d42e4441c44400303071a4000d040c024011031014060fa4801c3d5508100610881c0c040742070b816840200520917130b189404071030720a45c16940940d43c80005040c00380d19002e030803286a040701d5580c00400b4010400c005c0042c0c2c242c03103003100d005103903000385490b0300e844410076041c541c04a07074040a001c6281000c0e07450082c1d04086501840c1e002a1083c0c4035200c0304024652a000c28a00130000ba484c20b00c1c9105101000844100b00d403c0b9075500d450058980224141d240241d10004009000e2000103000390700e0590000d90302203001078081da43c00101080c1c2c121003030a080e071110002c503800050900074950702000810203805481014403d00c14030303c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 43963646 1250 43962396 43962439
    0x10b060304030302090111010203100512010b0d0305090307050901090905060c04060903061e020c01060e06040209030307170702090a1e0e0a0303090c05180105041b02060c0d06030c0b03070e 83
    0x81c0000c080550010340e040c003a038000d40758018211140d034004c42d203910700b52641c1d0b805003503503018041c450241c135a0380e1308440405000d0342e600c00d0406400c006c409034040c0e0b070948294012300d01096040c081c4001c0130685480b6003100c2802042e410340046000000360809a091500c003405e440c5034400104400e006141d0000d40443c112640058001840c2c80003c1083c09020340c4145c0c08800103000080121064105400c00e5056544c00743ca1042030703403188400c002c100e01c150a68903030076400c10300c0b5500129942d00d10080f0603850342200d85e45041520303800035414400482d01c108040e0754074030411002101604914808000b81d0030100400c80d801d070801646c4a018550080405858070601802c2107040481d00d002008003403c0046442212007910788150000d000329409949008042c1540d503400302071095541c0b425801a24071502e031010182c403241d100c149031100c6191107010000000e40030010780c80041010500203500c1f4141701c040203050180349034100b44141c0300300e44c00001c46461107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 43964896 1250 43963646 43963651
    0x60906060c15020d020403060c020f0106061202030903070209070801030515040209010306021305221404020a050607030e090f0402030d02010501030c0909110406030503091302040305060f04031107060f030e010b0603 94
    0x15a8012001c03040780c00c2c02d0103031240524090300c1d1400402c0000070003643c1c0d0400c14820f00c4039000c0d14041d83c000d0800b1401c079519031180c40d000482e0103401441004082c0d0056402850790320580e0325005268000c01c44401c019198000042d500800400510406004020032000d41c4c280400241c1890380002c0d01c1010f06010280103554001283c2031900c06004c0c85070014940941030a04110503280b41041c0f100c010b580c00c1c1c5610341040507240c0c0c2542d030a90030030700c40c50740109060000c60030403091200640200030100c00740100d140e00b4000c5d03035481d41d0b400c5104070410034510009151074414076043c166007541c00000d680c1004c3c01400040d02c4680144181c907180e4400180a03c50b0341000140c0c05d01c0031018580080c0781c80300c0801445800310040083c0e8105a40c8030461121440d0404100c3c4201e1101400b250081c402040c00c2c0d5009001c2c0607005402072802640100c5407121a60810050b43d22000125a80d41c4e8400f80030b942500072030f965002c042e0000c11280064001003502c43c40300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 43966146 1250 43964896 43964903
    0x219050307030e070623040f0b030c160501051b0c06040210170108010b04060b0a052d0c01060305060c070506010e06060712050304030215010b0706110427060906060c 73
    0x480050041c40c8242d000e01601d1007010101c801c416503900028000300034100c031401020f502c5d0340c1c1c90038094000c0d004840441e0080303c090200b5a00c0c0409621301900040c0c183d01e0401d504011100e41c1d4901052507040301c0780510000951402c00c9150661a10759642d8542c030f41450602c0290000d44000ca43c0c5540180c06a4818080842194003240c8102c03c2d44241e109010078040080340800055022000d40d8038190743c104000b03500c405003103071107003c1e51041e400015420450b4001c8050449010039104898503400d220340841401503000d16004062060900c1e9541d03d8200240402000b8540c0c01c91600361806140029585400c2e490744014002c000c0c0c0560024003061450325040115030482d42c000406103030b1541881c1e0001c0050380700352000e4005100f6010111160b030403000c1c0583c1200c1c05a41c04516014941c1e850354080c00802000c119005010300c8001854001510b4103c0c5841940b070411205508030b550210440d6156006500040d150802c18130490790070001000c50b040d003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 43967396 1250 43966146 43966157
    0xa0303051209030d021305040501060504180b01030b040f050a05060f0310091a07110c061c0903020c061c0509010b030c010c062405030607230a020a0503070c0e0108010219 75
    0x1c544102d0351440c850b45580b8039805100080300b940070f1985800500940391704640c2400a03036642c07031040b1124051801440200022042040e100c03a819501c100700c40d0030103050100b10803010100007800c0b12050200d9020990b114003c02039482d40754402c440e1706c00002c4a000c04455901d0b00801e54550364141c13041c075050380da0f188080038402e03201b08400741812420070101c218170700000000c0104551900c040320a12400c84c00200c50300d0004190345850f494000c01c80c0306a281c0180d00d902510144800350150300540e074401c40c103a11114010180b41034080241d44c00000315200100407140010145240c6901d0850302c0305595030040340300d450880003444d0482007040c80d82081c400070a6040101c00e04442140c40c0410940b504000500c00c540080342980c4807566000d50a540411070403503045d112060140405041c070301c882c4043c0074040d4480c4119511840b0943e2401e1031a40141401d81705d540195404000604404c41c0141c054031100d4001c0d41003a903505001941480d152a002c8280503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 43968646 1250 43967396 43967401
    0x160909090206070b010308040e01090c020604060b1906030203060a080a0b010510090905070c02040c0302092206030b0c19021c20060708060a050d02150a140c1b0a03030512 75
    0x1540c601c156416144c004d209500156528034140d040340e4010311680035103902d8080000780c441c00c4c5104a00b440740c0150082e25003691107507200070003003601c1c580542d40180d906020301c040b8041401c1c008042c0003c0c1d20700585d00c0c00c1550070030003131011560028042c0d601820182d400201c103943c4130313411581d041d40c072000007841c0300302d0a0700c0c1441660400b00c2d4035441c0204018a03a42d004125542c07090007031350100005d0250281c00c8069101c0c00c4030303454220b4105200d801402261199400c0b0159003908000b07603490301d035030b646c0b40c500c841540d29280081012464010009241c03700044c90350a0f400100712074400010754908460312407101c02e040c8035081a1031082060304101c9006484401d40c01c2e03036003a1601800c0904007000130388103140180032688000c119801e20181070325560342c0041101d015481e0701c41d10500544e015004c01810091086029480d080095010742a4082044090710882c40f0380790f00340070207110b0800f842d449042500d60400220344c008003214101440d0144020069 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 43969896 1250 43968646 43968649
    0x1501020a0b06041d0a0314070206090d030e100e1305160315051f030b0f0a030206030603100501060203030106030e01020f090d0c0b0f0903060f160503220b010e1609090902 75
    0x2801442450013003032030340300300c010392448000c030b10902214401e440318a5800780318140795403540510b0300001c1d0410300410204c0c06916040e058604200c0c441e16150311400c400c0320120300e001d1080050180822178000240400345000c007130301029070281800c20456860300100c108901c82850f850001450368828005404888142c070b060040c050141180785906840008095403980526030240000c2c6000c02c0413140b890300104811680f000100342c21036450440e020852150300103402d9551501c40c164021100d00c2d40303805218000d095a030040c54a80d0b1402e600a8242d40c003030240303151940d00c10408051300c0d07500e501c1030380c000300c03401d0382d007644c1c0d00040703240c4107004041a4206150700c610115210910f800c901d4020f0000c80f000740c1c25201252038042c048080700c001910a45080a0f528208038011407040d400756038000310b55900d0600f643e00c801c8507510302d235400c0942a58101441001400140d0081c90380710b41180c1117400040c42d08030075610040860071540a03094180c0e0f140c01c1d248003036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 43971146 1250 43969896 43969901
    0x8030a05040317070204021207030f060608011a13030803011818031b06050f01060e0102010603050d050f0f040e100501321b01020c070608130605070309050303040c0501081501020a0b0604 82
    0x729a01034021551412132007084403500c43c04403000b10000e810b00f116014984041ccc06140111112600e98038226403c005030001d01040711030254448000c1401000e240d00f040784416001503008404e044d940b941020008924034250708141c0120f1030510000142c5118210b40c050b0b006a00340c0b80001203001054040100c03c25400409050300f82403805101490844400550494849423504c100c08022100168240c42803480060460740101e242101c00c54061070042078894007003065240b400f806180d000762a50003031f0300030805d107125140400c500348095022040c0a003271b09090820200c02c0c00051480b2550040351804207001548072100080d5814200355904514090130b4408607081303820103036000b074014401c50350316442222400501540a003030510300400c120718420481ca1259114640640f00140059040596810040740400d0090010b140a544250341c0f041420b494040010080d4001074a40d11060101000e40750180c0c0e00000c003020215446501c402595503500d002400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 43972396 1250 43971146 43971157
    0x70c0b09120f070501020c030a0b0a05060a030807030203070204060f030203030a0e01050c190b0a1416020307060f020702040b1e010c0212060408040e0708010303090e060a030212030702030708030a05040317 90
    0x26988660b1000e10b40d1120046072002c240c900a0b0300300c404840c4203104042d81d408400724003a1224040c0c80c007150034a40c0340e030001d9074001c601410003800305540e0703501e00f00d85900109055005800200b184411403030140111402803030410781c03e601c240c0c04c60b000a5141d106040e00c003000d1220750105a030b0103034050300554000003006004d071200014000c21b4240d803400d05e040c00302e955800003c0058885c840750310078610504005900f403852079403841c3c21130750a0301240300c00405511090285200041741c0e4018500e1440c0c02900250721119280b06010548070300901c6c10b0701c00c0a5016841200d0030000f02c11103e03249003440c1100c1c5178501800030844012200708116000d0003808100300500c80440020300072101e00461422460355610002c0320081c07020300005000528071081007214811441140c1d4020b04028800e1740d41e66500e5002885c1e01d80c0060500071140c00104203141507103400c2c0545030007406000302545c940320640c20000c0c4503100e58003005282a241810100c90010100e0039500c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 43973646 1250 43972396 43972429
    0x3040f08040902040306110406090e1003080a090305010b0d051002090402040803070b040318050109050d050f0f07082a21030d060e160f03050c09130903020c06070c0b09 74
    0x1a55203403600038002c0a0340c09808140c4a483c1000b8030510402e1410741100e040318016611711280301e052500c3d0304100e02001c0d22882c034180f0381d04c0001c0301150240000708641c2e243e0f038454020241c5145040c900307654102044612401d6514440b00100b8400f1607610010181200e0060f0740c0c08465000900901882e000301c1c1c0c0601c004686801040103011800d8041c50103501d80030109540441145071a0b0b6450042c01d000420040d800c2006040100700750711960712070020b88109800d1094040d2030036244140b2031900768040b00741004000e5007440480a200c4031421f4044c02a2101d83c01c03124042c1041348002d0041c80591411014502010800500700d640f00d010b4a82d01c88001c104c28001c1c02da280550310300903900c2c0c0041200035070316841c20030801180ea2a440900c1c400c844060f401440c00811401810344204507104032503035141c2c01000700301d80b5050006244856428001c0c84c050461085602480c0301b044004007041d040190355007140e0700141c2181c5d8030217011000c50240250044d601 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 43974896 1250 43973646 43973663
    0x10c120e1e21030609060307030c09020702010908060f18070501020606241303020901050108040317072003040f050d021e060f0409090506060319030e060403020904050304060801120b06040203040f 86
    0x720303212003000440c0104c0e0102c4100016484200c105a1a0002c0380710080180b01100d1003002804880d0300903042d980d0050409082c0390780e0760a909030419604444104100b5068010088440b170440f01400c0030b5075643c0c00400c0e00d01e0515002030366412020301040d218020704003000c0314040c08540760180103444071003802c3e150a500f5070301e00700300105400228452a981c0c000401c071544a02d400c50302c22030b00750395821800000310b41105030003900a4210810050180200d02c05400c0d001e5601c2e007140e620340b0055a80301d1502c0c501001c0c4801c0303500304034840e45441c17440102680d2800d080341d103185510146010324000c0140019803611800d07048540b00d8402150010311305840fa4444490340303000e003041d60b1103640c40d10304141d1a46486c01c40c9503140d1400100b4000031074412520321641d180003030595858240c1700e40024130703031000498046486030300001d007e02000d40e101407400d0050a20400c0c041c010081a520761002d40c10041c1014041c60340800000c0074000810700c03c0407400d80140e0781 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 43976146 1250 43974896 43974943
    0xd1b050304060e06100303030b0a09050c1b120301050910050904080a1101141b040b2215020307080309030d0e03040518160c0201020a14010c120e1e 65
    0xa085a04100c07401d4420314034150100d20141000b295031407243e044910000d07492411603070150b006241641c11030341c0102ca84c241c01b08040080e0720030740d070040d4131f150b24003511490710f00310010348040104c0c0c1d10722058110b110039500381e5403132405170b9065070000c0b0360702c4d991070350b0701c40030710140c0390495010540c0031030403105200500c81c4120041c4043c41a0b80e03502d00f03285082095540c283ea00100420514000084c00100141c00320780000d50817010030280c4c54606652801c1e0701d0041d8000b0300320700381d44002080d02c14064104601008004002c4401c0410b2003202040000c0c0d282e0207642406080c003100000050b242440a1040386c2210503184000c201608000480c0390741c0b074201d80192401122040c002100100c46031003028400d085000315030481c0c0c3e1908208541ca02c0b510704080f41580720b282040c1e40003e40d9030701a040d5043c039520000a40c000401e00040640380b507640c50842c042d190046140c1818804506c249000315000e40c1a140d80301440e81940c900f411552442d01c4030030a0000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 43977396 1250 43976146 43976201
    0x604032405161205100603021b01020304110a05120307060506040603051e0106050418060903020309150901030b040507050a0c03020313060201050603010510050d030e1c030203030f09010516050d 85
    0xd0300a009195468000c054070221290307003111801d4643c0170000e5600c0d6820480c4500c250005c00074656110f10301a00410746124950984e0815201214081440a110040c2e400c0c49590b0030002c00d0129200140c206005541c591a841040c1000c0e00041d1194000f81640e201d03504610300a40c0d1041c00c0703032860402c6881040c020302090392a60625400c2120025092501d030180c00d0700740c00300902500000407181d4802e0001e02c42a6401c50550100348030000040d502c0340c070300701181a920351034180d450320168001012249a030103a10710852402003444480c0e0b0703100080d200403100c2d500b444025100315050503441c500886580312a200894400030410f6a0b040d08114000c0009900034040c54030340c03030180408141075004540d04030481c0000325000c00d11402418940560141000c004032820f09070307107000c00e6080c460560250f4000070074400540c9560540c10740c80705548c0001c00c03c9013416001a00384504c026145801c000c0c0200e000c2d0b014000b20b80c88840341c84200f04002080d80d03010b1130f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 43978646 1250 43977396 43977421
    0x60b0409020c100509031b1c02031305010503040b0408030601030902060a030e010b030c0303120c04030609030e090a0e1002070501020d0509280b1b090306010906090f06050604032405 80
    0x500100792401005161060240e05008960180000d0341c051b42c2001c0030243c528160040c8001003a825128205529600740540d1440115145560303001c0e660b9811b1021000380c80c02c074203034005810420100100300200e100b0156083e003003584480ca099407501d500004a0240c99150b001030751190000481d0010990142e006903003030050300c802400314809443c00c15841e203218807070180e055002081102c1d012020894101d901c8502c612145040c25100d860301d108881c0008000c8000c40e2550300003403c00d2500b5010250b1003007007840140082103180711401c0d1154541019013a5a82d0041110010400300713405481c04564402e42c20001858521038207030744c03409440c10300c113010304454082c02c107c41d690b0007030205002d0304079008038040d403100c69800d502c405444108461428041c030401d521603030300344a824001c03d4215408a80c107428906103404860b10324050f0b071521031a1000400c141d840d0001a03908480c2c1140720981c0d0181140189c040380450344295003200c078038100400401e0781c840c030b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 43979896 1250 43978646 43978657
    0x315010918200307030f0803040629120304030b0a0506010f0804050a0209130609061407020307150b01030e07090203160801031e29010305010f140a0f060b040902 71
    0x14010700c0402540c0000d803a00224090010302a401400401464980845250b812440002e411280d205a0f25241c501500c914a207045400f40000800d010600000780200d07400740e9183c0d55640d0380d541107044051084192000003500500c0b5400c842c980709001803050300c00840c0c0040c01c4030036900d40000d034a001481e007120120f0114550b4001844064499640640b00e5940702001b8809500706808000610b203008021804107200410f403400000c069015502c600e610410740480e0381001700005007040b080051203d411940180101c0c80420007440e201e20200700d044c540000c3c1c0d1a1210700481c090400700f032180c40c40b803041080c001405c1d141c40d402103124800294044820680c0c428003164007110038070014003004c240703541e52001522401100f4145034814400407551170303000b0a00409090b0650300c0e000c1401508001082804802c0c0150902c003901d000c3d040000c2c0004d00045d1501d080302a01c807820b265030302d0f13502c0850100780d980701f00c001d043d450101030f0700d82e80e0302e842c0d0340f0295101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 43981146 1250 43979896 43979909
    0x40b040810050c0403171603120501060e0307140a080a0c0e0105060412080c0c0916020708030a020706050f04050301050112150c0504050f01030222031703010602060103020d02040209031501 83
    0x1516107000181d40d09102e400e00548110301d040d860b1a2a40e03c440c0128030800c1903c07135042d202000f404102e04c80503000100c9441c071079140c040c1890201e141e944111a016484242408211050100507590125101e001d840e01e44d809843c22f4030340301000c1581382ca6a500310141030301c0b401c80c04109111001e140e440880308860001c1c44079070303210401d01000c0e005a10403801060400408a00066001c1c4050440d0705d41420460b150000c82c034002400c0042c064900f080d001001031041c0101a60620105001d00000f0006510300905860300a43c0c0301540d00c03c00c020403101007220004004580202c80007064000c000344142e58483c820319001c50307a00c1b4001c556400034285400e45600d1540920000100f49880f10740c00c2c03d1070030040c84520302403044e02504041e820051120606c2c50005a41d007641414458100101e0139450010a2194081c1e40540301907000d000402c0500c2c1d0005005041d01e40c1900c401c0f40301002c0b4808103000c2e00401304180c0d4103020303000c2100743d44403e0300600e5041361319 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 43982396 1250 43981146 43981153
    0x90304031e0503090909100f0204080106080105150108060d0804140918070b0a0306030204060906060f090e0606070309150c02010909020c060604050405151609051008040f060e0102040b0408 83
    0x80c040700752803500000c500030141d82060100c05818038000c4034941d404084c80d4240d40c04280038259040454003106043c916662740802c0c140011301003440340c4009416410020055403c06498501c42ca03440343d0348035410004041c000074001d0701d6005030070196582c060a56a26284c0300d00110441c030303440d2001071780190f03590307000950180c0b41540c80300398a101203400352610070f05140c15090700d41d200c0081f800c10b241c0c03907134400801a01c40c1d10400004240e031210005210303043c003400070914410725540b4420410131420602c283c640250b00b07690040c00484d00c06071303601d0301c924080c0c0e001c60b811380c001c5041001603913240440903003100214030700340d100b6070b52101540c0d1a40d9002d0101e024001050940b070380034078002089401e00764040c580182c015001c1ba00344840c0942100307200304044803c1e5104c03c461800b25102c403500b00007405e0141004503480c3c400c801295030300400701c2030010006040c0e4901c0d80100820b10402d81e000341c800701650070007550383d9a19140c03401c00e03a80c0548100e054610 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 43983646 1250 43982396 43982423
    0x1020606010905010c15020c16030515010b030f190216020906040c02030a140d050106050414060915030406062411011b051b01060608011404060b0a1101060b0309030403 74
    0x42c40382c0c90074000c0d600e051710b800c01c100c03160342c0f16556141201c2012180003607003081441080744003000364420016554141074030f00c03400e41c540131742045860402c22098190520050181420207016207600520354040c00c2d0843e0388150707a04810310700f400c10681c0701c0d80c80020300141c0a0510884001854000d45d03510460386c0f0380c24248002c4904411507000140c00034011002d030503118100390a003400c440030901e400c22820381301010454800303a0282c400b20f800020304000d88000308040d0601d40d02c4c200c500750b0074a202c0764049800c6c070128040d0414036600000c0050100700d0a0761050019040280001100b000402d0358461134041e070910000200752080500e0041d0302050049410741803550440c030595032800d04090311640c200e0600c00107445107138500404034a90034850b01c001420a0394600016515264220540d281d0b007a82e15402035041400500a0108001c00c0740c20300012842c041e600300741c409031120b004101a42200c00780c2c5000200b842841d0714000050420f6a009170688403402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 43984896 1250 43983646 43983649
    0x40315050708090d1409030d0801080d0c03020d030b012606040f06031e050f0303090c010306050f0102120f09060418050906040c09110c030d06030605060307031509030e090903070201020606 83
    0x5000440c0c4800301c55015039201c002032481a000c0c4007071851700011302404c00380c0e00d100080c00c061001d00d60400040504004022031002003022840f015510b00b400344035180c41d920000e40b1072a40d0b440d138406060300c85030310041c1039100d1424160801c90039401000b21039020000040044025508503208a00709110464841d07030078458082240e074045840580c9407011100d04564030354040c03060b2014003420900e800d991409100941c0f080c802e80c0007412010000d48009011078003140c112501070b1044006150380c1d80d0b000560264030044084005880710051040c82c0418894104407603042000810009000b1070204d18120902c4d140d0801441240d0b2040a83d0fa650030088030003801d2074421200030405000254040000c500698100c0f5180c20102c110380c0d8615448200301c0e4441079559041001400741178412103070064400c8000c0d0040b545140c07a414007060041192002803907940c10707400304140c01803280c2c40201401612001c01032500400b815100d80281c03009a001d4050040040c005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 43986146 1250 43984896 43984907
    0x503060601031a041808040807080d030c0e01030e0c0612010e010b031b210903070c0603020412060f0b1504090c0c031e03090b0c040602070801050103170705070302060403150507 78
    0x1d210010144000c07540700c0314100700140000d102c150301c0300da0b0031030217000110780100001d1024018100060906600c1c003481d8500c1c05000300400001c052074400305400d40c1e58003407423940c1d05000c2407901290710300d40514030740e080503140100f070303039006a0002d14043c40310342c2c1082c804d040740da0460038a040c07a82e03668020300c01c2c0d11048800950110361907001400085d44e160141c10000014400b600340c4009800c0c81181c0c40c441951aa902640003090b00c000b00030031400580d01500c4286400d40c140380c0707030002c10401040046801001291180400c42049510364041c20100f01c00603d184800705c0c044c02d241c0070320342c840c1c000c0d25480ca0402280e100b00c10b0042c00c0d0314040700da056407603c2640b001004540c64541c0122020b204040d103e240d5803000c40c044175406802281d480302103070742d00c924041c0080d00d00300b0542e0164000c0d0b41858010000b251400e900c0584614400903855503514541c03806508214003a0002540064049000320501120210201e01c01d50125410403139078607242d0049c0c94 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 43987396 1250 43986146 43986161
    0x3090303070201080c040e18010509070609060c0510050703020318061902030a0b0307030302010c0f02060c070609081e04060f0201050f06040209040603020607050604050633010912030306050306060103 88
    0x4255004101050055100318001a0300c0203190702c0031400c00e0340395203440d621880262107482075172072441c0000e06058030071300c54203402400300c800518005203041400303084001c1d035210f28801e005e002d04072001402800d002180c3e6403941c1e034100304854a0131030070180007500103503604021303241031b05180100401e0010b0315074020ba42400c0c186141c203c1281d00d060180d8801000c2401d0346c0c0d1110088001600c08100b2000514032a4001007048428040010036640001044104640c41101844000c440003c01c58101542294010071200c40c2410441690310483c141c005420000380316a1080340041c3c0b000e00283c0da0165107004180c2e89401003203080e1602075806a00302c00702c40c0e020420b40e2403d0303801404580070140021504682d02d800146083d00304480a80c1c42d50400070800040041c2441015408405100c3c0204400f00a484030030b112900e4031014a03120211818201e86a03014050400042c0f810702800d0504036202d03c3d00801400442c400e06010b44a8100032030a0756000740503040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 43988646 1250 43987396 43987399
    0x50f0d0203160f050408060c0f040306020c0607030f02040b0f210c0a0207090c020606010f030f0c0e10020102070818030705090405031201080c030d0c0804030f0b0906070c02010509210105160207080309 88
    0xe031238403000c10402e000e900c0500311843c00101088000b002503001e00103006089040c4011300384901d01a00d0290580e60340e40e08000c41648100018000084001c0540e40310210055401c1d4884984903080c80d4440d07600d54030003481c81c42280400c100d0f030703200000920701c0ca80990b0a440e80c0a81d210401c1050360121005007000da04911f00144442d4440c0315403811b0710f40585808076000d003d120081080310041c507407143c00103001c68516401e85c2002c083c800071903a404d02c02140b420682d03845484980c060404501168803d00e902803040d50740400100015040c0240f00d02d4040c10a1b261150b03403a0b0080e01a40e100e846e880e4000039542102081c84100801d024014000c40c0000c2041104c04400700399040383d84180601002c80802e07811504003111900c034035503402e580d0804d0f664840c94840018818001c100881d028480140d80c4042036643c2600c081d43c46c01c40d203104003001014001480d040d250850340c602020054403c03001c00b009284903003560241c0c0e400b5501c4180c040e86a10595a005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 43989896 1250 43988646 43988653
    0x303120601080601031d0706091409010b0304110301060b07060f050705030a0c17070512011a0f0c011808030a060f030803010308130b070c14011806050f0d0203160f050408 75
    0x1a03055020300c41d425800541458006860381150180b0301201c6401c1e01449050351001100340125900000c92070060712001c4007000c1c02d98103020004051060500805800700c0b8080046400c0103007400200100c10f000800038000d440e160903c400e915003040c181034503154200550803031070142512459008000580d40e00e85582e460010700302c060400892000c0400142000024419030443c50603401001d00f55a803035a203080d0313480101c0c502c440680141c0b402e4080340800782e078140750307402c11507601013501180952610128400580101124912042d140000e0140802003151681c000c42c811040340f00b08206c083c0d00d902812540c44014000100150f0040005102041200002c1c20b0000c0795039940c0d003038032a142c5001e1841034100004c09c0ba0200089601446005141001400c01105c00c0c03a180c01c0d0f100052101d490448179600c00d0000784500010003e01010b514011100105280d0201303541c3c90800c41c0450a82c1114501008005201c0003c10703001c90303204804440441c0c8a40009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 43991146 1250 43989896 43989901
    0x16031d0d030f0e010c0203011107031e1e090b0a0c0c0b0405030a0204180c0b0406031802100f0207090e0c090c030f07080603100c050309010e0d05120a020904050f0411030312 76
    0x307403080f940e180002818044c25894820060364240074481805c401c4507000398403030545207400f5241203c03070320103400c113407003021000682964800380c1016040e00440400d00540e1f00300105840264140c1c2050000000014092205941081c2c02015981c82108000c040a90721000c1d21524010303400342943c145c20000d425000351409800c50a103c50031103000c0c0750101c049644600180700a0381c0303e154499404a410000103416124402130b941a4a2041032900702d1030380001c4a408814907010184111000d042241034401c1210f54040c041d152005c1000060b1030364002d55a915401e4841c3c03049419400003102020014140c90207284400d201410b1a110a4015115107a00810042d00741c4248a46000d95041900620190380003a85800b50740f41400b102d007500b955800b0800440690107000c1000308603600030101c4121808000e006e5030542c844070030718800b030312502601d070754041d00f44800d00c00e0305800141c0e014042d600c40c0b20a40d44034803141c0185030300c80c0500c1110a02c6050134a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 43992396 1250 43991146 43991177
    0x100e06010e0d0c0504020714070503210a032403020405010b04140d060b040f1415010f12020702030d02010e1b10030b040b09090d110708060a1116031d0d03 68
    0x70b00e1461510520a0108454035100440c0480e00b1201058403440c2814111a07100c1c0001c1c044400a003c0903006030044107920094800322120f40203410f4029100000c00030311140c8250300110780844560503000203010720f035120704803079641804181d2089107050000540c8202070422503046441011088082c60003500400401d0f00020009495090319031f82c5807402030750303144034881071a4010100041c0c10382c06001c440e0040305008110b80d10f1401d0000f00c040840e80c000c24080608200c9241203000c040348204050041d000312040290076100d006600490190107400400d0340451560440e900700f0f05403a00e0003001c004020341c20342c1001d0341c01c24501c0340d14400e80255000d00c10213040890b80c0944070f000300310540d408460900c52034000714282980d069100018103c00c20582000700300035401c1036400d41d01d65401815003032000c1e540c0c0b82092256284202a2032602045c15076018500303406080141a410b100203000e0000c1285011120280c50414001100d542d01a41c88121080007500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 43993646 1250 43992396 43992409
    0x1090c0911160f0516030803010f0503010b03060610020f030f03010e071d0d020d1e1e0203030405041505030a030801050103050106030c08040b0a060b0403030e0f01090321050f030a05100e06010e 85
    0xd845900400004590602c2c907190b117403004500c6403000d1980ca62500c1441d884d955900d8005d28840c1e410142c803140c5d503a0380041d5142e001281114000401d85102c5026447c0044408051810380400710324052848000307005503048503600300110300540e9501000310384119522203020f0340c0c0651b0117105840f9007030070190a400c1500c00f41c06c0c2c03074080c422506d0b02491110340300e04800c08005548809070820004080e82d22084c0070f401e041c0d91124400c0d5000944a00a42c003585d03005a580c3c0c3c5103070080c03e000e034030610300405000d001e645c042d402505000700480000d01500340400c0c1000000651203200b8480e0b0310a05081342e50700d00e181d80b42c9a650f03160315a0080d04c0611780315250b40c800b040031031a14005000551207612610002c28580043c000d00c2c0c1c013058501c90500078521810070110b01e18919440341d0200d00d00003400d5841420783c05071018016040b10104a403404000c00c824207866511140c0252480340a10354142d54450505468800446c0c015000500860410030b9904010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 43994896 1250 43993646 43993673
    0xf08010b03100b030108010b04060902030c160809040c0906020f0606130c0e0a060507170711090403051306080402030c040624030902030307121101050403021902010c020301090c091116 81
    0x20200b25540796651612510a40081e0000c03c910b965038038004903980350503c10b0360001c0c0341045082d803c514084030410458010540750304a00b0420a8000d020000c1090458040200040c002c210791208400014006901800350b54050300c030701c1040c81d45100b030002d03031140700f40d400401c610300000c50340c15610040c00144054106000c584a210700d860b80d038942042010340b109985154860015050461504001c0705c00241380100800c440808552040e00c1c98605010940c1e008609445030302d4102c6144c031a0840011840085143c04540903038407410b02d601960084044411050340c100c1080111a228460416130749091a5100000c91045038282c0c201030013802c00251107112a004030b402c641c0f000c0b00807114115103040011703100750490821407080100c400200311520742075902a43d039503402c034404000100b07150000c0045a1042c41c415440c10381c080c0003440303009052716020400d2803c070b00a50034118104200e40110705100c9055800c024261707160405801c401c2c0d2542c8582d083e15 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 43996146 1250 43994896 43994911
    0x402092a090f1002010509010f0203090c01030c02160b0a0807050a081503070806011d09030a0903030509040f02120403120207030219020301060b03090714040e0607080a0f090818010f08010b03 84
    0x11088001c5035503e40085100f00f00f500e40003c200c0745006010b103800c40e140446241d82c028418001d100d507810700003e48600317646003800c00003107020020005034641310402100c14014200b05001042620015000c0e00900025407135035112034480600035505030203640100c000080399003000424142220f012850f101d900503095a015640b542401c1e400e15109070004000c0c0d6040208180942c41b02e100711581c0804450701440c01c1400351900244401c40c0c5120113420040003003960280e541e05e60b0710000100550768011580d0384c4084221580c6480c04880980200300311032049500e00c000c5008490805a055000d00110107040c106031852145420f02607806658405000c61540403510080d406645141d00810200d444c0120f004224081400450f000e141040100c012031840016015006072590030700551175a10425000028a02115071038821410100d9001c14049100d0042c6010062070f06140d8510302120019075030b007000b040941d400a11800c004002c81c8060074041c6400104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 43997396 1250 43996146 43996159
    0x3010b030a0b210307120804020603010317040f140102060c040f0b03090f010e070806060d03090b0313061104030b01050d02090106050703020c0d0b06120d021b030f10050402092a09 79
    0x1883c0031800100040411002d1003039000003550400d01c0340340d030b4425210310510310b0802d255103000c0d80801c2c0a80010f1000608000076801c0207580ca07552003040d1400f42458030039452141e580c8032100b540e100c02c00f140150260007200042145003040c50200c9080d42c030b00d842c55545c094a0702c4841c2000e684001e041f600a0300403030403401030f1a8400c0c000c441c1006004801000c9142c1006101400c003c1d01404491190103000612000a40c1144101007207660300344c20191240c0d03441410b06040941080024141441c00c03008074960b0440a010784141c0b80505410501030b030702c4106010702403088103c082d60105106d0010000244150f0042c008980300384182c417181504100800c0b40d0340e1301d08008850503c003d204000460038200800f4019500100c01000c1047448504003a4440780f520680c0ca90401005491100c161810001154841c01107400c0300c88809501e0280f01c000c0005840480c0300c0d12001000c40c14114032003070108019465040d80c8080e00703600703900a111680c01000244d40020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 43998646 1250 43997396 43997419
    0x2010302040308030a1b0201050f0a0c0c0c0e0106020c030a051203070903050d0c061107030f14120f071412060603060409051c110a0b0606030c04120f031403010b030a0b 74
    0x150312902440c011003c20001056214111b50380f58070002114400000310380c90102002b41c80340741d80362551f40007140110001411404902c0031070f800c40394018094400403400800007140301120310700d14101e81180d401e90f40b4a280c00c1c020191590840140074110398040c20038030791902e400700c00954000d900d078101380e026203549659560800700440b100c80c000c03134504110001404004e009880305414107400d501e280c602e155034003800d840d0b01140240d080200000704080c0e07190078101110f5040945c1607a004481c9401c0700c0c048034034501198510006070402100c42a20716185094038000d24200c4103a50a580c0c401c42405501d40004041c1940103444520390000700d0300c00c0c41143c3c101041c104500400000701100502044d11003001c102c56548801128400300d841d01150942040c411911241c1c0c90b22580c420102c0c40c05180c1000520b6000d08940c00c00700001d40c00001c0c4103d200b5100c15400600354000c0550750f0209124183c1451400c00010303041e080caa60146044900c014043e840b1b12 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 43999896 1250 43998646 43998653
    0x90c1605070e0a0606050405060d24030b1b0310170a0c0608040b1b07140c1207090507030b010507062327070302030312101d07031503020319020103020403 68
    0x3181e408004082c06980500503100e00d03030b00908015040c2414124509803911000c01c4551144070310025020350b8581c8908001004d5580b44c0f180c00100c0d01400074404d85a007005500d00310260382d42210b444100f0000c05001c880756080c4c03407280103aa100040b9151820b0390495a00d501e00014036054081c0650850008854080803406043d40c2d5440c4040c80c603051915080400024110075201c0d089110540300c0040c02000301d9814603400512000f034800105e10942c82d00600c041c00315030101c3c1c0009241701500000505c00200d0304041000c0c011503c030550103404803580d203034649001400400900001c40d032107802030100a500c120310200071140d50340305080c0502c01030720301000c0c0b81d00000361f1440ea021a1440f400001c0c081c403010f410400e02c1c5070b000aa591054074000e50030301501000140c2a03107840c121080080682c9040550304490701c040784140550112942e2000c01c2c901010b08560008005540060383d40c041c009000f03014070940c489910301030403002241015006c12011000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 44001146 1250 43999896 43999903
    0x30b1008010207080406030e15060f01210b01021209010801030206070f0606090e010f06080703032012031e0f01090f0b04020d02090a1203050706021b010509071502070302090c1605 79
    0x6000d8664145c5035030502d0704c01816150513400e0444180d101d2819850070010400380c203078201d80100e51428104007e0360050f116003600c480740740440030001c94410100c0d030b156009940e0600e000d9007500c50013824004005920300803414000e00150301d00380141b006050400c02421041d021f03c17003070800c1c1c0483d50740d0780e8191f032125000b20000a032601d400c1c0c82840c0c804d0003018003079459180180079050500700420b64031906c5110280800814102540c1a0540c9290500c1c0d162411400e44565081d44090340d5410350091f220f28074a900c1c07840c0c00d0204c078040c1c1c0107024000c624021b0402e00591901140e800644041e441040b096561030810540c40d1b6030382c0c801403910010346a0003585444030b100070000c80c0112540721a20b20420240b03100c7c0000e52203411108011b41c0315a0040c0c40d04c680040035400350030088140c952039840c10023480078943c80018460116000c075a02482041c062110403030b1140801d20009400110800209204035040800783c850180c1d0085070051300c08a076103c507880c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 44002396 1250 44001146 44001157
    0x41e06020a020c0909010e031204030918020403020f0f0d030e030c100c14060609040602070303060906030f0c061103070209062b2a0e092e060e0c04030b10080102 71
    0x90780c00743c2480303240b50900a84040d8003000320402000200c0b1084a16501d0748141070743c0b1411a19100d002508150203500f01c440540f0104402213454603aa01244000394042d0000b0303441207864129405092900141139640c041010300082c100640c0b81c0d906449100e09000398030b902d4054050800441d03100c9144184100b00e05954010392a00642405108013040e001c0380710b201c0e00301c60308020164031089810f41d041503201c140165115180d050403401000d06d60401c0c8203040c24084004280540c2d00080441103000b00d024200c000d44e0f03008140c44e4548050700441981d0000c1c444e21000d850151202c51f48400e018201c0c2450141ca1103d0722146010a07882181911001d020902844814400503009100b004c0040400c0c0038001d400e040701e84800d100d6042010111030015144d64400c3c000b03140c00030721070124400c41c035080382c410182062241d418250194904240096400c1d032034480e05000c0c250344144240707841d045444460410000524100600300b01100001d80c0c030209200404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 44003646 1250 44002396 44002417
    0x90503061e0901020304020108040b0901090506010b070212010b01090515040305030f0703120b0f13020903060108031e160602030403020708030d0f140f01060516080d050a0b0d0b041e0602 82
    0x404224001c1d2028440d040503200034803580c414020440140d800c42d14860300540c20000c44e0b01c6c0390345d40004030b501404170040020841d000b0b00d00005a010209805002074620883d1a03111003d2101441030032542200350450001c2c990781020880383c18907002405519180141d51450039840e81c481078a16400200c00646ca0000040e02e501070550001c003092030032060000905c002c1d0107400c0001c20328240000c0007071144c0d035000302d41d070101d001c2c0758122042c502020f0280c84440d82e680c0d003034644070f0b00140c40b024006481c844820008088a604036500411a1405a14003070810784a510003500f004104a05601c0b803c200410b03155000c0014007200d018520380031401010010401e811794982407265149006000c041c08120406032800ca41500c00d00d141c42521030030340301d0a1200d00c040003500540041000511b40068540b030390411840f60103600c5041c00000c4400052209405440c1006060101c5040c040740004801e00c4450400790302c8180a903a054105454502c100d9004080aa = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 44004896 1250 44003646 44003671
    0x70c24020d02041508060a0609060e0607051b01080a140112020609090414150103020306070c020a0b0a080a0605010509060d020904020d110304120212090108090f030c1510051005090109050306 84
    0x2501c0c0a45c00794119600000c15075820400516101c405009078409004100910221000401c1c0703949403001079600558010086071012140d10b042040c41c401e102496500141c010750000f62001c5103401f64031410051072440c210142c1c82c1001962040456403022030740040d00708072035849661003c803020b00460040020036002c0f80900000c40c6840c1c030912801c42c02054400040025903004220150721041909101480717280c548009480d0b105941c110003000b40d40401e1029580d0b074811111480f440401c0e00401030075032241d00564560180010143d03201400f04070810414003190007070700c0703404406000503040580c845205400c4c2c4007030a040790031510b800b2003000203109034900b0311292503041d40043d110554070000340b2651445917115032810703c01c02a002c900d01040c1000f1003540c1403044c2041d291140340d540d08d21900c6501c49440484a84000808600ba01e21300c942d9403c00c50b800200481e0008505042c01d44a40e081007001768140302054030002011342301404402e120b9000320414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 44006146 1250 44004896 44004929
    0x80a021201021918090501121b050405070c020906030c03070522020703050c012004120816030e030d020606030304170c03100606090603050408090d17040e010e070c24020d0204 77
    0x82d0300195109a1011790390a040200402c184045d0540314070119400156017405260202072410301d000156112940240c5004100301d4003a50015181c02c10501c01c84004005032684410166641d03a010103c9a05402c01e071010089890075548000324001c4002050a070b2604c0c85510b001203030031810b4107902003140019020030300c0d5400c0c40307018140214019001159500d201c0500f85a000b103004030340501c103002907520140b00c11102074075030600d01150034003005c02e00c1c3d240043c4451115240340e4002d00c80c19440402250011403490300c201d00203402107041c0307031800d080c401c40792600818002c1c1c28040c00403004541e442c00d00c403040b0302c10070251002c140945003181c0241184059071000303040519040500000038400b804440305440c08646a100e48102405c0904144c4460501800300300000140010014903a40810f81210340d4a2030391303409961358000035141d91440782e8004000c400011150710450740c41c01d1041d04500c41d14800142807007094400d000c1240e00c5500000c00e0304201c80d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 44007396 1250 44006146 44006177
    0xb03100603020c100e07030f080903010608030f07020108060f2806020102070206190e09040b060102010b010302090f210f0c040b0102070e0c16020405130b0a06080a0212010219 77
    0x410100814a5103021450f02661140c8075844118400c05105000c1d142c40c0d1075803500c0020801d54025581107190318203072130560b1600752010303030101c20018065401c0c401c000a92503400310541c0d2404101030325691600e030a41c1c0c01100e9000700100b90a81c0700225014000241d1244804014454130040e03114000348100a4904551b01c1542e00010031607004001c1200103031103102c16280703426000e038140d01c08140e100905a078040000340159030091544c500700400e011488410740d01400c820b800804c45141c210004401783d201e0890b100d82c001c0140c00c910351301401e2500f00107a03100e40c10100c00c860090b0401d0564200b04d0070120281c280da01c14829100f143c0303841d12941621141c00d0009129080c9043c00034540303001c00420607003542002290182d203c40d034603083c402c6c0965008008010034a440f00c44025a0700f401c0c0f40075110a51940001a80020540309100c265503448004007034004565003000400121010304140030b540a000702208288088060003c0c0c0315a40c454002054170f03002c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 44008646 1250 44007396 44007421
    0x1e020304030201150f09020708091203070b0c03010605040b0c0708030c0c09010e0708010e1305010f020d1a36040605061c0305030a020a0302070f0302011505030c15090102160b03 78
    0x42d403283d41c036034510000c02c10220041c17150001c6880380d503c00340e00d903440c9040545840c060001c01c0c540040020710301e4116104040b0040c5101840f0303180954064841c0e18006549001c01d005d4400842d0341088140030124101010f403a105426070121002c5688400000c1d0840d0095071600743c807a03104800141213854003d0000d80908402404034035185003e5a0003071104006100d90804c4080220100301d440404480351303043c964118009101034030380b00c609a40250b003e4165104002e15003503003404401c10710b8614640c95400240711030071b407426800034001b000008242000b5612200c402c0d540740e880c500f25420388514040c800004151038000c041c0010780c4522200c2526140c1c40700c003010006030b0405e058a070000c0220000580781c40003030350700350020320035400c02420059946c400b4600f00f42e4150084c0080c001c2707030301c1d40c24a03180d6a0820f056840c42178004403030f0301c00c80e1950525140080e9501400c14080140b04450444142c03060244991815800a03a40c805000007000300e10a00507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 44009896 1250 44008646 44008661
    0x51806090f37061a0402090609040c1812030305060f0102100b03100509030405010212030f0703050402011103070507080d050a020a060b01091517060906030a0b0a020d0606030203010510020309011202030405011e020304030201 98
    0x1c5d40d09510b0407490070700041c8540f05014405125030381e120344e00303151144114019041c0c0822110410300b1036840b0310102c00003640c2d2103021030020f42484002141410301082801030300c50103030010844400810027090140c06101c0d20b051701b602c69501c0c14503000d51030b809050700600440001d50740d03560070000020305013405070054100c0d6100408c280214556000412030f40480c8919000426803903030b1004946154008101c81282c1c40b0204481c005e000022a80c0d000300c61601d0b04507000f00c410170a00391420701440c0d84010158000045000216141d078000710742041301450060401034039012050782907070008094070001000e040b03481d003011104101090f00b000040302d00e512280b90500c00240d0701c1e850280018104d58040001c04c421140c0c45d0103031031944890b1001404010b441322001002500f09100b1144039045e0300005418490010040740c0502c02c0c1a99a070141c044c02180c024041d6001500c110368642d80d0f0441d600b280107005204141d040c0d21a00c0160796800c160400900b0344085 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 44011146 1250 44009896 44009899
    0x2070b0a060b030a0f1409100b0108010b0429040f1505070b0112030c0209070c021306060e091f031113050f0105010f0302040306051806090f37061a 65
    0x1d107441072050084034415690f00c0550650b01061005048039410080c02c104641410b8014510083c895540b0000c07400c641108001c1c5410403011603840c004403803c030000c5c41401400c08080205100140300b400300c0c52014841e250018102840703450501d030300f60b40107900c4148002450001406100602c154840c980e41d0f0794600320f0706010f01c544503007032406c0062058a5041006241c17490426004100204035190014005e102038078001c034014162100440e8202c1c850561501040a2003900d0711841d400e4440680c0c0701c4161900c40d4080c003240342400380440c0c080d40d860703004400c0300709013a640640103144200c00e000c208039194424005904c009080700803601e03042000308421840c100d101103045500034a0b124402c00390004083d0000d10580e00003800c0c0310705103c1040070144c2e072104c00440c4c02300c1c00b0049603007564600c0c4425459502c9000c02c0c041075001170650f81c01e074207003030b024100b0090714042d000740d5880764100b006203c1040104044500700d403030b00c840540618100120402c080f40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 44012396 1250 44011146 44011151
    0x6031e01140105161536050a0f08070b070302040e0108010b090a0518010e15180d0528020606041107020d140309060703110601060306080a0201080a15060302070b0a 72
    0xc090000f91040c055030034101e8910416089541c140084141c00809000e0407407804c0103004030000082c001c40352410a0086c1e1091580c0000c41040901c45260010765040009007e030012903a88905256040d12001c0e11409004c0c0407410220b100403520500800036030320f00698591510014003c4401c0503440007060b40d1601c00c0b41c00841d00e41484c090303840f200745c45002175940c1c0c817080b44905240d104120801950b28107078800031403640c000307a25907811500703102c0303000269603500703d5284d007160110341441c1c02d0f00001503001040f40200c0c040c2040c0c030400019120140c018a500e080ea040c224010040142c1c401414004542403a204080e500d10328100303140d103000386c145c0101c0c03244070840c1001002040c8076600c1090508041c01600c000720b1000b0949580ca6142c3d007001001300c880e10705101c019020b03900002840034000d00c0381c0421601c01001412031001e4680064415410003840c10210075101d41882d0350701249031030610040c0c41c51751030040e20380140b0b04103405030920003461403903042d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 44013646 1250 44012396 44012429
    0x60c0309070e0106020d03050c0409020708040504141003030c06090602030f041a1e04020312160308090a021e030715050a03050108010b09010b070303060810050a0506220e070506031e01 81
    0x1071703001c80e1b0340c00c80c41c42500b00801d094543c0c40c90040507100d03a41c0a00d00e42840880c00201f04007140000b00129841101e060003a810003090901860b8000d851910404441e50b404100007409104090001c50240c20b0000d00d100c100d40b0b801c0d060347d01c00c44801c01440781d104104020000b414454001d255280d1680b4042498025200d4a0360f8540006007500d1204003c005801c650701005805d004000c0c00c1d41ca951501028482c400c2d01055100085010645140c00a03494942c0003071140b4450750010324030b5186101c20340802c0c070004000c4085980600808201244620030341098500c1015540d840d55550350042c4e00c01403c440741030308841080d0f4145407002196a40d2000514199040e00e140300340d41d100d4500d81a4020591980002d50a00810b503807602c9607951039005903c82c450714001404241e1b10b4200300300c030f11103060101d00c43c00c5200f200000d55503c0b1640c00038912060580894401036100d5001500e270342c000b25248020040300000900001201341c05490040807a21310f29402038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 44014896 1250 44013646 44013659
    0x807020d020c01032004060201060509011e030303091103070b030a0b090906040305030c040e010806070f020f07030305090d06090807140604030e0402030c120414010b010e0f21060c0309070e01 84
    0x207070710160b009410140c80385c0c2402c45c0268405042445902c003211003039a100c0c0ea9200c040d010304210711481b803041c92031000009001171b5140002d03981c2013202c0043c11800d4215a816401042e00c204150f509201d840c04a84035900e04020100180a50183d125187e01d03200f40d050302500c14a03502e950140e020f11007800b01481e4001581900107a06040c856120303a83c800102100e8001d40c2c2c42828951058030000940103008650a40940300f0741da580d0780f0340c0000c130b00142e0b074600d03a11010307880b41e504c00d610400c0802d101d02c014003000718000700126080451511f842c07095540c84542a64940b000244203010000015403980c0c0e0207088001a00d041c0c54261005400d8640911201d40115000000100c0c4614010200c440b58a40c51071500709504150924084120294010102c40c0d880c003e000d040c00d43c003508803c051078400070182d00540b441d02040c440c034805441e8040c0c140302a030030280c0c4500301041c0030f42e5108804203018503031285040310f0303098641000380c0c1c4030000b010b09450050084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 44016146 1250 44014896 44014903
    0x81b030a0c0c0918020609060f040f0816060f08071803050606040b12060f04030203090409050a17030610030e1014090601090203040305070318150201020406110d0219060b180103030807020d02 84
    0x41300d404849541d124100080490383c14862171180c00500c60380040c02040c44e108d41004030041d102c0c0901240c1038090007840385401030395130340a410085800c03140300001e4540f25090166003c00c4501c3c002d010b240041624164500c046e41048a054003c2401c02425080030311a80e8001402120340d0740c1d42020312180c071601c4e2031010300322418a48071100003406140c000c004603055860302900c104036907852410550707180c901c41c12086a092941800b01c1030566548400d070380c040c450042c4486c0490010580079801000440c0d610501d81c001d221100615103018880c440205503400368081031850700b01001824400c0c142c0151010900c1441404042940031094800c1d4682c0760030003204208114040c10000112907100309030303944016040422042d8103401400c00c545140d20799110090080581d5510342c1d03e41614134006074051007101c0d011200c003001400d09207001e001d00048442501000c52103480c00406680011031a80004004142c0e00858283c0d01c85110b20103031994900124000b501c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 44017396 1250 44016146 44016191
    0x70906170c0f061e160b130209071206080105010806060a0602060114060c0313060f020106080606100309150f09110105031b0a1b0c0303020120030103081b030a0c0c09 73
    0x3d5440810002683d00081c44400505120000c20380c0e01e59030300b1032100340709005e05002164090300d42c0b030224659450500320f01141a60042034070076240c0e034100040380c40104101140e07003da40c58800000b94a81e007032080901030700342c440251880d490300c1c0c0e050100346452944070004541c426001001604120045050140c4044500d5642d45508100f00352035409244602d51424442c1c580c0060600c0c3c0040a011001d00140c00074003806540712455038039510101c8415400400007622040f00074030130f6110680e424410185845807000081004085400b00368907000c085549000340400c0c08185c0522952401c402d01e02145145131004d507110301c1d0354a400b00c0b00c00c09080030504900060080340a000003e079061100d01c6032040c1c908000c100c084243c4010b40140d40b0381b00081d00700518490b00a0041140c005956103940d10315503a04009920000c006400c0b0160703054010f00960040c40100f48008031a41c510380340b510781c0c3c1085070300340280740d0140c103841d0710780902d81c40c668844403480c45 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 44018646 1250 44017396 44017399
    0x103050316080d021206090a0b0105090402030a02040e0f0415060605090f0111030703080f01060c0201021c021203072102130e060a030605010321080411090711070906170c0f 76
    0x800441c051411000a0284118101c105400400c50001c00c9000807445071069204440d030140507103034a8079410440b075840032080e000039800c001d030185a08090300299082100003d00500c0c141c3c2e01c06a0142c40801602c4516214611728180810701940480107140700071500c0d4100626450311102410301d00c0f8410f40240601030724410700050f60b0040c25994500080e020035240c0c1c900c010b03d070091110b881100c0c1c521007864000c0010491500c1644198095a41038006001c40141450001500300c1c41d103511500f140314502c0c0c0c0805c1a018071010318000e0740c154650042c1550002d5045003004844d60b41818001c1c070500003820680c08254900040b2030102c46a8080ca888403000700e504003129400152105003808000070802c500c210701165031909621052448200c4010100c911000c00d540103002d40c2407050881d4214070b0070140c4250004001d0401c54440300105800d20f09140311a8040100582d0300d102c00c1009106500ca404981840d110241407510b504400140202c00d030125800d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 44019896 1250 44018646 44018677
    0x93d0c0b1314010e010609110a110a02041415030a0c050111010204080303070207060f0f080402121005090705010e060304020915010c0f060b010306050d050a03050c03070218060f010801030503 84
    0xe0114100e41c440c14203841c1c11924590380d45060b100198003030301500507844c42542ca007070300001d00c00c1018030591070303038070301c1c20702c0c0e0360316240711300004560140295212144c03d00600000c2c0b00180c2d607610400300c2e0040e45480c881c8941c60100c0d6203003004e03280ca80c405070081e0010111103000038034203e544002d450007400c24102000950b4001d0380280140e41220045100000c28424101e0300012010304948155844440004605d003049500d5100c1400d4000440d103d41e000c00d00514003a00101d8105c9803850441c0d040042000c002010b80740c05980c0e08400e0341114405000360759110752032050381d00041e14003601d1070405070f02140868100070140c80c44d1142c6030f900e0207113581c41010074084040e086803035094021074908004009094428915000c20310b059000112030900c031150b000c50075000405801185001e031030036030741503200324403043c5a03000c1084406e005030390f284980c881c0074500070701ca0100d528010090203401d01084083c241841a94001000012b000100312905041401c200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 44021146 1250 44019896 44019901
    0x12030b0d0c0317040305160302030706050a02030316030b04020a120c020304050312070303140a02040e06120a0f03020c040f06090b090405030417101109040b01050f0703080606093d0c0b 81
    0x3c2c3d1a0500890300300910300d005281c00e1112600112a20000350f070b008609540300c5030b65919080d68140b05080348540560810300020303452050031b802840d48086d55003000b082210b41007000600b287d00a8440201140491510f8100c41c40e0354410303107540010b28002940381c0741c1040c00181d03a89000c1000444410400204501050b100b50058820300790540380d40413007801d22910480c084c0d0403038000c881642401d41700288052400341d00b200c03a042c10000203084a007400b510360390340c2d4801c1a00b040c0c081d48140c805140041e00d9600c10f460000ca10f241c00050190b0501d280e52090315021410a40b04020200c10f00c03010800100403a4215040030348280850310085281508100048402031002480d01c1c1d200382d11049a08003c1840d410202c6040005641800054423140200210101006801d100c0c0c200060b0042900b6908100001d10b110300b441c0343c207400601e101e4000c940ca5110711030080001e03062525000340f1500101c80b2201e49040ea01c070b40000061031807401040162290760154013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 44022396 1250 44021146 44021183
    0x50106170307151a091518040302010f050c03190605120c040501090b18100b0703030504050c01020d050a0e0102010e030c0304031b0b0901030b040902042d02030f2a030412030b0d0c03 80
    0x48001c0111006012420707c0041c162038141c0e000412101500954202024a0f083c000e031303071088030710607400c20325200c0c119160803d020300c141410230a601481546c4100c041003542c0d40e0303480c0e41c10074440039000f40303900d030044402c3c041610b4040c2c3c000804241000103100e0543da94401102c0490300300703036552055a0790781c0449024aa1b071540424045080040c10710203241d499007055100e640240d01300d400710102640120b0b902d5040003421400100700384030940f103003881146002e000345014800400c803806c11841003420765005181800f00d5906c0000c041081210b200301032407a86030084003002d907640c5001581140c0d40303d040300090405030364200c030152035591507018041c6550040c00402801e0880040c50b06103051104070b10180e08100146c41201903402d008491254035141a20005511007a2504648811b02107000d61080341140140f5160f50b00100076500c034900400c1070211803041d064001e0100e91840117440c1c0116442d00300a408912070b503150501b200c0c1e0000030010741c05031006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 44023646 1250 44022396 44022421
    0x901051603030f060e190506010c050303131e080414040f020d0c0e041e0504050c060f04060801060f0c0f0305090d0302030403021c1e050106170307151a09 68
    0x12140e80d4480c2000140500341540350f400341032284050541081102e4481e0180411a40c080340c00001001c60582200421142a0070036504200e0604140b162148141e031a04e082d0f4208a544043d1081c20314221010701035800d0040c5460070304561040107648558075003054902c03440c01980150600302c6520107060710340d54440c85210b10414070454481860f024100042e000240c0385c4000141c00200118444c6040d1240f0121103d01c0343c581c4907a02c0e45a800e000c060040103006603124054040c0342c003400d03114100100190308502000d03070b66440c10694054252003041e0092400c00c490703051600c44464010010380080780d04180800310301c2259140440b401d10078a05103a4000d040d8030068020190000060b0098a108441400a40b410081201740d0000500c0f0301414030807080c0c090340c040695058904004070b00a80c00440d50a445d034440000e201100c82ca80c0076248d200146603801d000b0301c61000146510918403d1040380240705005080c2d84890340c80d68819140d07a030220b1a440e80380c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 44024896 1250 44023646 44023657
    0x3120405100608010b01030c020c0d061a030a0308090f07030c060315051e0a1703030705180607110f0103050702100f0207060507020307031101020c03031603180803011707080d05090105 81
    0x71030050015a80350311006019251a000b07a03400f207810541e010758128004907a00314001e00140c2400707400030541c1c1b9000c01800c0280c1140a02c100611b95031004c07510240881c44840e8080d80340d100e0907040001100b031920000c030f9640d10807504842010700000b0890020181200c81d20b10700032030641002504900380381416400070703900c410350f41a03084a20305a400e6075421440111030402e042c40d514918808511100c1500760b169800402c0000d0041d4050320142214440010081224045143c0803900c641e02c001c0b000c0c1da1181d60030162684502d4100140b04001c202072030240211704000e00c01079503c1c2c0d4084500b12045850f84000c0d10400340c3c44e4140d0300744a411540c103000310305040790080d450b980152000e4001443c1040e800d000070405008503281c0741c88500c01586147d5031243c48407840000791110904040d250f601040b411001c0d81056202680245076190b9039524114143c000111156106002508030540800c0211408034000f24464001d05017295074001402c012034240c400e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 44026146 1250 44024896 44024923
    0xb01150c150b0a082103091519051e13020315060310050a1406010504080606060307030603060207050f16080606130e031c0f0203040b070c05031b03090907030e03120405 74
    0x40b01ca000421140002d05445c203440461400c1088280544d034440c07031480112801e44040d03001c540042c4060340d4180aa542c00031307843c0b0700d05407000c400c0841138058031801e58802d40040780d045503480e80340c42e040e03c40c190040c00c082819002c100f4a50b02203600e03601c010380c04440d80c01c1c50100040d6280c03024024602c10000903c400c01851400e0303440703034008002003203050300c02f600d44200003141c1d03501600440b415500341c400240b41d01d40e6102c08100d5154001002601015190240000003c0250000c1c0600c0d62066010303003044072071103922a1504840e0035402020b00c082003010403510310041105900200e0036200c0d1148110722802c440701900d589401c417103951000040c2c50082c3c1d0104816031041d25914082404a0030425502d00140d00040c2c03005000300000101081695019001c0c60714094803950551341080c050b820303111481c031448144d03415150030002d8690700a10309092404d07031003082410b04121403104031010300d40e82d0240e20540c820101141020a052100800002040044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 44027396 1250 44026146 44026159
    0x5030d020610050114030a05060f0402040b09010e01030b0d03361a030c0a030c11060a02041706040c03030c060e1204090c08010509150402090405040f0b01150c150b 72
    0x9810000359503040c111100032800c2c03001c2c0c602040641c032680c01642c0391703e00c12039001e0031601e50044c0c590091001800c4254071040e9180ba4113030039120760002e40014249544190380381c480003000075140d0340001c00401c0c101442d2810b1041181e680011a08043d501480d016480350419440507000440c10020965484445d6044003910030180e0125000c2c1e0703040386400c10581c0a802240c4a0500041e161850b5540e414040350811511036400381c401680c0a18004030030803031b80403140742400381c241c4510a00b1340c0c00007410310a400074110301e100303c0060f00c002003440c0e1800d600e455204851901000b03041241b41701c940c01c00c0c4070294100710f13018521502680e03503560038400301101765401803240201c402e0900031511089401224102d0480b2030181003540555600704074020b0304091302448a5101d50300380003d00c200c0d10707a40b091070300c01c521800760170500c0d50702424000c40010050b0b11452460422a110340c0606034010f412101c5664031400c060328a4000e03030b40c110042d05408804903001207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 44028646 1250 44027396 44027413
    0x50621010b280e060307060f020a0f030206091b0a090c0923010e01020303090c151b0c01090807060c02011d09090a0213090b01050d0606180f0615080f0606040503 71
    0x612081030311124030b910000000c0e02a80d2040e04050f00b49045458907890780021030104401d07406100201c07520360701031041d51204015a80e0f0311000d244440400c0c1c00503404242009100303a010050100c07401e4414080b07451040c142d00c000707041502140548602b0545a1504080c80340c02102c160b00500901b20b49409549003060242001c03e03050300032580010104918424a035002004490040708498003404910b10260280f001041481c82418903291040180b03c11a408280440c0d00c1c1521040280100d80c6001c00010a6000190440d40041d00310395020801c90f504003200c50b803600d0b42820000c40c0c83e403940401480d83c00e541c00401d604418a6070400400e0340000c00e241411038030071510700150443e9803958800712810100002c01c40c0c901c02006000c0c52520902c0e580125100328004207600380c170340000280041e001d845201d4402e45440c1101550b0300e02e8013501d0080c100f40d041e01d182003580b00d0401840c140024001541c03c1e2070f030300e0100300e041d154541114041c0c04054104c64000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 44029896 1250 44028646 44028679
    0x303020105091207021e0f0a080105090c090c0406030c0c0c0801020d0f020315040b030a170304030906030c0906030e10020a051b0d0804080a0c020a0e010e0a050621010b 74
    0xa110071142c0c1c0301a4050a090303203000c00305003801d0b18106034018103194000c4c101002c2e9000c0701c2ca00b01220070341c803042a410343c15180d582c0550b0f46001d0a070000010480381061040d01c0d191408100f00c0c0e500c25105581001a44c940c03030815601240d58510700410050b849420956040c60404005070009001180c007040e2000150001c085641120341c04002f400105450b420480c0026100c101000120108503040b40c6400e8004814411009041e940803a00d0b56691000c040c0c0e03501a00d540b044008410071007403640040c0510001c05880c04d0900c103580791014020820181401050241581d80d6140c0c040c01c90100503075101000c803c1e20465584607031190240080e00510035544d1003070210a107903c05400c001c10495240380c1903844007400c81d2556540d0b008030ba00185400780812407200b241802513a250504140184603841d01d494007941058601a100130300203007480700180c2007805011480c2c403520002c04645127809401880b59500715200e501400115043d664406036840704040701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 44031146 1250 44029896 44029901
    0xc110a0b0415020114061e04020c0c090702280f0c0602011d070e0c0313080a0c03030506030a02030606090705040e010b09010807090f0e07050d09050703050105010803130b0a050f0403030201 83
    0x1600d5a0318100c5140b024182422402d03948000d040718910080d07000411402e05015580380b54550048001c1414451021b0210701203070031910f41e10343c842c0c0c00104c256140d4101901e80c0c540140d203034800740114449001c07490301450b40307000c602940025020007100a03c01c400e00b5541105c1d90101c601c0320816920007001380600646620144170696071408400c20400010300c0c50100c0e5146542803405540f0941005400e03007008101c0244e08400a101800049402e002003207220441d48601c0840fa0603810001c013280d5000b030010380a40d000e4a949000350f500064800c2c0d00600072039252120f40c6d90744104855501940e400070f24022a03880010417910503010240003462000c0c0d07100b03111581c40348011900020f5500c03d660041c04490030900c030354840350840740d603c00c009040c09854884900321400448140c142c00b640d694200c04424010030101b0b0280900608900c40210700f00002000b0400c8002c103d032003880151080000d284407583c5c0140240c5006e0f41c4901c40841e115070b580c0c28017138007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 44032396 1250 44031146 44031149
    0x904020d0e060115081b0c07030305030703060b12060f0a121104150b271e040f020c030d050411090705030a14011202190306020c010c0806040504050a02010c110a0b04 73
    0x107601410380041104c40c01000003006a040c2507803002803d4548209000720301c800c5906001507030004000100d1b50120801503040211310a0756156620f00e0900300060849480307401c180d801220804c52400541c590022554105400f2500d10401c4107070000000c0203a0701b2603204c103070302241e03600102e01070203008950303424041c0040d68140500c010b480c0c02002c02c61124004e0450b0420180921a541f0010b80d607080440d071309554001022002e0f1a0000700024141911103014640320341d201d9040b400d0034010481861905402982450b06005002d500c034001d00c0c800301c41096490000800380041840c91005690014006151508000d940242107510858091139141d040c64008902c0019881c6007604030342d8030031000c1c071510700240c0c20040554800001400700080580c0f0200101d085403000b4640038080100001d0040d41d4460007900403d00100b10900c41d915182c02c02010440c00b05552422680c24604200c0d2a880f030302d000c4060380d112001d15a080040410041501400070f8010320 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 44033646 1250 44032396 44032421
    0x210109060e09030307091503140f010501020f060705090609031e0616090303050901030c2c040b06070b0a0902060403120305010f0b070507030303020306010c0516030c061b03050307050904020d 84
    0x5182d82c2c0d4003082d07999210503102c0318009201d4040400400c22010f1900c8450101441c0c00300c0d10415050345540c1501095400c016940c00c140e004001660701001030030000d101d260060851868000009440c50085140d824000c0400040d2525565810b225680c0e110f80b07400d81800900703012005a0380d840c0012214410740d858801303810107a19020708906011070798035540d09882d010105c2c0046000e01041c6a101d003d1040007015400e103e0b00c0b024030b21142040345080150003030f00e03400400c4240c038a4125080d000741d4041000078007241651364002d50100c40c0b01c50206074642a88046103c500c00c80d031000e8488410800598440c41d41904414100c450040840a029488001c0d00284e413048401c001d201c3e51151078100f000901a40141d680044141042c802d8500301c0e071503140c10721081682c02d40c64400481802c0c07040110880c50f8101a003084d02d010207100c0c007003600d10344c0c800c40d8541c0040c3c00c0c1301020001840b10b5215600f140c00400000d002503460312206502d1402802004042a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 44034896 1250 44033646 44033669
    0x30b01030c080303090a0f141504030306092702010c02061201030615050906010806030106050d05070306060b031b090301020708070510050c09010504051909020301030b071b0c06030221010906 84
    0x3440c140004140c03801145030b01c0284c1401d40c40343d52480104180c0000890f1444910403230041c115205015203941d03410300d03524420007807805140040484201da04104103851a183c8000034883c44c444803444079106030703090b02d4911609800141d403405110100250310000018040207071110000629040328800c500c11b210030f410301115110110042e001c2c854000c0c0708400024490740c401d45c1c0c3d070742d040034000c2c0001858903201c41c04110103500e208002c2e18039a0100d1810810065144142801062142c108030b0840c2003503260007503118616803858010042c0401ea16030507640c00c0d41142c642c283e026035525030b2190350303282c084c2d111450441d090320309a1808000a055038401012100d5102c41651554645406d00c030070007903040080c5601410010790050007040c0022035200440c007a50140d11000c00714900000014454042c03200a0840e0a02010b000000141401d035101c040ea0441d00300540c60701105480440318018484e050000c0d00e18040001910380d21a6000b141a1030020940 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 44036146 1250 44034896 44034899
    0x90501020616120e060703091a010b0f0c07090518010c0306030c051912030206041e0b04110d02030706030608070603020408030405150c0304060e090108060f180109060501030b01030c 80
    0x16a12078504807450b03070032442c0845007100410710070750003643d14003c00000018400d04680f4128607081d42110341c000032a54680800061000344a42c0021442920f09428025030401d03000340b615020314000074840314804200303000481c50501023030f0b0242100d400104414a4001d9800010030b42c0761800088130f502e06140541585c2c400d010384010f50782c20903510740c02a8540001d1000d00b02c142407410000f04400880425002c1c8000d0603444130301d010303500400c114103050505400e212802416801c07103034034820a42c00001c0215409580c400e0700070b007182c108800c90710007240f506003035803200a505010700c0a0200382e103901680b00c40292040d41c030441c0c1b041a00d428040e000c0f4440c40c000d040195006100401291812400219000211000c498182004a41158a550031035041000425141500c1e82124101140c28a006240400040c002801c06828175120050040e201d2001544054040416141c0c2500301301c00c1c440d8444420021503030342e800c2440c00c944013800100c68800c442c000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 44037396 1250 44036146 44036149
    0x30b010c1a042003070524030a021213051f090f0309060207050d020604090207020102030403080409050601020c1e0114040503070303080a11090105040b03130f080c060606041a0c0717030a0905 84
    0x81240f1110000f9004248440c10710081084104400000d000080c040d0410b03416a2581c500107940214050b0350050b03103c04000440380349004008046492603920a012103020960000340b4100d401100c40040300c00307a801c040b0042c040c10104401502d4080315507503420426510984040c211082982500d00203502c40b410001080443c0380080e50000c0144414400c04409034000c00c031251050048030701e4260381c0d0380c0b0347d100c0e904581d1203506c40796980d804014140d43c042c441c0d5540d030402110842c0c0803041c1c6c00c508803a0b248482698074100114149150f000070844c10844001c1c0030b0082c212064160340e4a0000c00d90316044071000501c9080c8449104c001c0c418400307903140003205840c0d8509150510081580c1e40e003004103542c0340f4200204c28440481e10040c0350031452030140550b583d40354074032000a441c0000150030303580034580070482002040001d00d492121136500750040350b56005000300c02444d10300321344c200340e105002e042d0401146d40c800000801008005458041c1c0d8a5640d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 44038646 1250 44037396 44037443
    0xc1903060b0702060c010e01060f090e01050103020d0f0c05041b02120a02031c090219091d070b0c03070c0f061709060106050304020d050a0302010f06080604050d030b010c1a04 77
    0x314503401d0a00921946006103800b5024150500c1404000116919454400c6081d00c0e00d42c1c0c03041c043d40c981e0140c1030202c107205020340c01400748094001d02455141d907000c10954030740301101906640c1042e10300801c2000848502008080040c42806080b080070311003801c44020400700c0f0058801c0000c2500302ca6003641c25121024070310380103141041c0c1d10f1603d04815112141043e01442d5480c002000180d076081c85414108030350440c0000064100345c02c00342143c0142e0003080200400803a00303202480300054a1080d01c95100101d0740b1003070b1020304145075004051f401000d4100150f030200719158000143c40c11100703540c0d5881070040c61009101d924410a80360280c160700200c1c0140f00c0d59018500030361b041480a001c0040f4043c5c0c0d40c80756410306550410032001030351903040c101074802c018002d0401a090300e102906e100d05261362642da40350780031600c05003415250401c103241a80113500100706940c100c00350841c062072000c0d2480321043c04035030480b6085001c004400c901503180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 44039896 1250 44038646 44038649
    0x7062601091e060b0a0818030c0105101202031b01121806050106080c03010603050c07020d03090807080705060403020f040b1002030703020111030402010806150c07090504021003090c0b030c0f030c190306 89
    0x213003441e10000360740c1111031203001014a19004000741008014034010030091035020005000000c503402c048091106862956103d228010320320341e4107001598000c540410443d2600c801c0e00d07008910280181c0700f8030302e8502013040041c501032100501d0080c0761311558030513102e040c040195a0300c4241c2901c00b8802680c240c900c161090005122140c083c0c0d000f1074000380945901c904010071795000611310f10718194103d00147e01d060f01080594800c10104010700b03601400341040c0781c10540815048d0040d07200c003034030488900711540d0b075a80320382e0700c0307a00e0011019082c070302076850020002e0360b00d5201e074070224015860134806005d4100350a05036801294140d50b0010f00d5114201080000010000c81e41c0d040c140030000380c16018003c01040b002010b110401055500d064010001d101142000305410316080000c0d050004001d0042d8a050b15162505291251204004801c09006050085003180c1000060200d00482d9030007800505440c002120109030300a042101996040d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 44041146 1250 44039896 44039909
    0xf04090804090c03110a0c0501050c0a020a170903010e03040608010b03011401030e0c09070f020601050d0305030c0c07050a03030c02040b0406080c0d0201022109030f06070207062601091e06 83
    0x1d100c1402900c20755080b00742c00015925000c0340705044042810416400400d416000c20900107424081120a005841c0d000074003a040754142101510043e440d0309102100030701c26008001c0e4825806e40010994031070142c00b5000f0862088903007079440c6e890f80f080c010580418a010300010b0b060440e4021681a51808030104040a95000064010308800e44400b80d00e40a00e942a0a0f1519500e00c000d02c02c0300195502140804820806400c091060b00014003410003995001d0101e82c03c00c0c11030340c00004407415141e44902024900742052116084540d201800b98000800d041d40210810241d50003101c08008201ea03003010002120028804d81840d50003198031501649040080d80340460b0040c010f859071800441c01c200d11898401190528004c0d002c226900303241410000f0005148a0b403004111381c0c10b2010001e540e64040c2d11075002080354061320320804006000e0784030010708214804400d6961905040d20107451031800224103a02e001c55604500c6216001d02c0c01200c41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 44042396 1250 44041146 44041163
    0x8070302130c0c14071502060c090d03050705060411040b060702010e150c01050f04050f07060c32011a060f09060304060605060a0521010602060708040c05030316020f0409 75
    0x104801c81c000340ca0881500c0b81070000d0710340c240380031607600208080402212400b0f8602d260400740d40d1010f80f09000c03c08000c6611043c1001040034202c0304950998208a581000c030f4203082c0360860300c07813244030402007545c00740381c05002c20480f03007014003480140300f101c0a20100f0310040600c4604d0003600406800901c08140701e108500740702da07586071a402026103071807410b0000184142915000e0740c040c220307500d561080000b4080284074030350030003480c40050044286411402040300001d850054650b107000a03018010035005440a03004508088011030301d0103c01c03840900070b00d42c164402100f445c0042215038249884421a94080410002c40d410072145605109258000400072184030b40d031007001003016910076015180d12220380d6a46640d5141030b4102da608860184080c581c11100100140800ca4002c28950303405038503850300d07640c142d403142046400c92016911554044c0000552120745031909030500c0c890030f0080e1100c0c00c24030401c0e000c0c042140c03100c11010f0f0003c0d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 44043646 1250 44042396 44042419
    0xb0d0812060303040909030c050c010315030b06010512070e090708010b1b10050903071104140a050603010b04050108030912030f0304080a020705090f0402030c010206040b0c0714060109060303020708070302 90
    0x104440016600420701404803402c0c1511580c0600403903190140a501188001603201c08220301000020104d000030f18050018401c0b4003100c0c0341c031080d5800020304403400000001c0440e446a030a45003012011134000c0d2284c10903081c041c1c4000c00c99018a0f000c2d944010000309414014541141200d444009162030b200001d41401282401003c19512034003a070341030700319010444e00480d0b00510140c000b0b0b41e0342d10114901008003151151040b401203040507104804202104030701980010842c90200b400d81c2c44600003401045001e51341d0750301c40c0c5400000f00e060300001010b461170b0304080e140540300146a800180d0399000704c6403001100c850800c0000c2c00191500003030195100e00c3e004488000b0703145e40005068000455020102545039010001940b804115502104800b030020748001d00341502ca1140343740b0000c1c04082e020000140c5403081100385101341154900c40f800b9650556103c64170540907000c0f512044c1c0044c0709061002c40d80d104040748690482e03170f0080506c817415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 44044896 1250 44043646 44043667
    0x30d0903090302030f0718090b0105040908160303020a030c020a020d030c14150a0b0d030c0303200304050d03321005030d030608120f07080c19060903030b0d08 70
    0x4028480044080080540001005032010003c1d07120750514240505182c90a0000c503100010160605595081c1010b60600c04900c15121180c15200f0540c0d020071900c03802d0074001c1d5607100314418003164080082e00e10301419450750144c50080401d175000e11484041100c200c1e5118034014003e035102003d001c2e460006402400079040092090055400440c0c41d480d40b0f9044c050081000d014218030f02c03080103e860f500d440341c081206012a452144d10b510b6840c000c16144c40d00c580107007890b5880e1154a81c48148026848900040d0007041c3c2d500d1600707280c40703a2075441c402c820a000c00d06004c402c0b2201c024410803071301440403c1a220503028441e584850403c60080e00362217004c0d10296010615442c18040c003100c1d800d91f6107021407090b181c21b030240d1500e8842400d00d440c5001c244404801141d040080340d41e02d40d08240b0290302e403e0350406080c20311600c036102c00d0341030002c07024400c1041415041130600d0303402601c0401c10000b040e0709000c0c100c1c00100c0000c044c034004001c5c02000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 44046146 1250 44044896 44044901
    0x5070c0e060d12020a020f01140d050702010f020c25060f0c02040b0901120c080705010509010e04020c01021c111c05130203030d061a0702030a02101205151011030d 72
    0x3140081c04000c2c2001c0603107802c40e440304518650401600711803007102c10750820a04590346000e0078030340642c403d8180071540d169030048440400d2426161000300d00300503c03d400c03031141c40f0740001d0119652040c0c10100c41c1c0d980305d5800310810500d035005c0d488800201d954810021101203499040c025000f92004a44c11104000704990295840744844540d8955250704ca01030300d501e42d03985400d0707419410030300d030711500f981c2c0140c42a601601c41441180d81c04000c0d141400b001307080c031003000032620300060041c1c05a105044201d61002c02c050450101d0101c2c81320700c845070050704100d1140c0ca68005201071040f071301c0b400100320100c0e54031010112543d120583c002c0e0710481d11101c4c1c00c510b500207030a65000c0302c0002240da803126418032a40d42d90200c06119164004c1e412031030100d880d40401e444511a20019100f8019400c0041001d07014074100d1f50040e4091800300414a0131103107a1000c003160303440950244185d0f24004840c107004d805500070b20701080f00150708002c4038900c080b02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 44047396 1250 44046146 44046151
    0x100c0908240c04080109030305041406280609020a020102040303181d060402070b010303020c011701050f010c1a04200603040f020405070c08030903030106110d0f0f0c080a080a0c05070c0e 82
    0x110040200f0000680322000e110f52800f284c820b0790041400c0c1071509048400b03180f801c07065800c50304402c0500000591300a00d40c181d4000d0000803184494540010074003d080c6070707000014040c00080c1c8110f6181d410760017441aa4882e864607034100c1004106c01100c2c40f4140503c007441c907070401580c0070f10114928000e500541c02007000d46042c6090b5242102c030703842070b8030071009a071041c61252144d40e0000603900d120600103444103140e41c03401000418040e00c10000c541441085142d20b01031014001d06001164501c50341201c4c1401c3c28605061729650903446482032112035100c0528502d016812280900d40050300e2944090f8240c00f000000c00d400740031503040c0600c000b082000a8003c10245104d02c21120296032070350702d03002010b090360411021038405604411030040c00640c02005618842ca9117142510005d4506802501e08049810340034060040c0440e00e184d403140c0c00b0362440c1c41481d141c1000d0040020019045e00c00380240c140090461058210510500d41e22075803166 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 44048646 1250 44047396 44047411
    0x40b010605130902070303060501030605030d051803030412030c02180c030a0b0102010b04060906080c0301020c0d030207030e060c010c18050d08030603121204060506060a05220503100c090824 84
    0x881c91983e42200c48100d0b40058400c40c0400d45604c4200065030701440b8840c0240002d90207404007003041c5400401c584203d0a41c41c00300758281c21501940c4c2c03020015507026091107078202007103031114100546000c0342924102d12440d020062008180c507110a02c0e0300407080181e070326045803141c44003c006080305034a21411590b84d07002d001040d980c0e501404004100c0034000080c6941080c44050800340c4e000f58050180c2e004104d0a01220f8000403c5c105d0410316280c016201c040301c1c42d084842040544d401503104401141c514440201984010112030340c40d140d00c2d2911015101880741e42d8041e209240d40020b11180400c0454040c5000790760218000301503d48003c801000740340c064111060b0445411190780420041055904c40e454018508031540750902e00313150001407040c402c801d4120700200300f0720380c5904041d420350300c0400540401819240c260034108071040051100002140c000303503800da40002c0b00d041c04585007a07548504204065489052032209444410250050303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 44049896 1250 44048646 44048677
    0x3120e0d05031602011403071407080904050a0509010b0f030606011202090904030e0307060503010b0d0c11011b030b0111030d021303050d05031b090a15020a02041a1008040b010605 79
    0x901c0c103100526481c82c0c10400440d12003800e0000410b01410240f5001c0100c82c01c206000c8066040803418003072000d200e243d6030381d0342501e01c0e003000b01d07000b98181c15400506000c00d10140360a5500000d00c140d80400007003040e180b040b001c102102518010454040d008400450502d5100300d01d01880340c42e09420152802c0d03d0035022400f015021074003075001942500c0400601e1030248410380082c80e151400a04550420300d41411314400e80ca9800380311541e0b40c0503003200500550500308200346900c001c004030300c3c0700d0107030318501c81e00070030010700207850041801e6080d8041c641c401e01c0e00840c50021400c2c28080319480009602501020524500704c00d00000061800c01c4648005030b843d56503c0d8903410301400d1032800080710403c512010303030180202c842580f9568201011a0f1907000c2c1d401c800f0705401002c0c0d04240d0090310180d045400c03d840da04a001902c00044807040c000c1d036204000321400e070012682c160741900c00414202c0500e00410909202d0741c007803c210301746d02d68507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 44051146 1250 44049896 44049919
    0xc0e0c040302190807060810050103181b030b06120c04090f02060a09060201060909050a110402041802040f14010c0f03120f0e060c0a050406050d020c0304061e050403120e 75
    0xc45440c41d08488a4a43e0800c00c400e000004060250300c0050a540c10800c0180c00c00c959004100b1106015080c1015070718030060341c049014400800005400508070322200d01104e40e44000310000b400241c0f00c004c5054041100c17401c01c50300700307200c0f41c1081025000088c00b0504100c00740000300b005403510b07a03201a5200c0507035203010091200c2c401503102c0481203454a0070180c00d4540030350110b54403034a0a030080000c50f1020607444181580249046140b000d02000a002401160000031152400301d001074101280d40c3d00038015240c0a5103000205542c400890000b8291950071900160850080c180080c0c04441e42d800c84610908012407264010402300044038002c0703207003500d9291a030340c0c2c2500c81441844820303000b450034071045251000021016089100b180314000801000007105c5401468a038142c1d095064244240c03941c0b6541d51000405600e00b05100c000031003103941c001c4071124040c400300c0d800c5036803003074442200210380c8600b5a41d594080e1415900403815586 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 44052396 1250 44051146 44051149
    0xb06070605070507030207080a1e03170a02070203070806070507121103030a0c0809060622060503010612030f03091502030403020c0301090b1803030f01050906031e03040501080903070c0e0c040302 86
    0x3020b100d10001d036100c2d6152241380c00e009160221551104409422030001000031494841c1c0c4181020b0b01003542c00e1484850b07140803503103000b5540703000b6400c040d01c0091080f00c24440e0001c0450500880072201301035120015151581c9081e030324032001c0fa8081001e00002040390505e12500710341303810802900c903075520314a41150300c00c44480004a6486004055403500130844a412406441c01400315162000c0403540640d0000000484060203002240800d241c61300058040c0101070000d2000c560350f0003005074a14407d0342c040b404103500047d800340e228401e100e200281600084030600d00f00300407107050000c2d44003a0060b41140216940000661802d0194469040c801c8800207203070f26001c407000d01e0300c1c0f031f070106003240c150000c0003403001203020300301154191101180c1c0c0c2040c0b42c9460001030310b01b100d40300910100c01002c6030001241e900101c05803085400a88881d09941d0b1a441016164031481c48002e21101550806101407861491a10b078031110820440b441c084c2c0301d80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 44053646 1250 44052396 44052401
    0x4030e030703080a03140c120601080907080304030f1703090304030609020a03200a0519050909030408060f010503010b120319050d060e01140d0302120d02070b010e071808100b060706 80
    0x100c207880402d48a5245107460340038507400942c001002042d031030600c2300750450b01c1a00b0f440038003124108100d1070b01003200c148041c0121401404000100c035941c5540313141c140200e080344181582e00180c0050086040b155120449202c1c0041c20041c518050450b6101801000c00f4982641c001c4040e500110000d030041c1c241b020305158020075520305280712020480080c1c10f03504800c0c000c6102d01e00413590b42d00320502020a0310400c5170b10503200d0743c5502071175203507005603070100401d4070402c41844140c41d0780c08030450503a0803c4c0e0003401040c00b60024003a40d0340005044500c542d10810a6240c035030a0107069018000c4d25103031641c42c01155408185c1926819001411681c150000410485801e03008102400c14256030742c1d1210310540d10003070740318050f82c0c0b040100c1c0c0700006003c3c2440445c0b076040303d000f07130b0b030254080485507194400101047e80846032400468003915a000744041184000022519548000e01101491154002c040c0c04603d6001d0340055003071250f00d00040c00b50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 44054896 1250 44053646 44053657
    0x4060f0501020d0f18060c151e0e030f0f04031e0c090b0123090108060f0f060c0a0204020a08070807031a0f0607060509011e05010503033f06190b0304030e03070308 72
    0x759a0381d132007c51281000c0310582e07001c1449005080c40c028440300550ba115403245284002c6c0ba03000208420740141150552041c40e8a4408140000079100d900d203c4140103030043c0ca00503504007040c00c0007007070411801c030441703403002c2e200703001e207080c1080741c054950004c400020040c0b5150051440060008054006805140d030100c64080381050040d40e000403d42e9200c102140c21b600d0500002022031400e1200081e01805682c002411000d00541008a540b80680c0030700110368a00c0182001441c180f802d0b51003800107200b880200c0d08451082c000c941e0814189507203000200c40072020406041c241d50764140d0040c400303004000204a407845503a1003540c100d400843c61001c065280034052460380901d4a02ca0b00d8680140007549000040e00c040342c220088500440070746c050b0540e81d00c0481100c00c206080c036003443c03e4052100e000010f028030410b5800c001c1c4d034481c2c01c6c00c910761207a003030080f11402c07102403000801217031041a814021100190a9a13446500ca403154901135108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 44056146 1250 44054896 44054909
    0x11b02120f061e060607020405101d040c0e1501080702101d1c050301060804080403020913060e03090d0f080705030301090e0c04090213050405010f0204120204060f0501020d0f18 78
    0x100d0b0420000d2540b51184103000034000b00c102855180c00c00c00034240d80540c0c180071703028a644800241c104441014520007502103214001894603001d501500074000445c0c0c1103d8140d2403940c0050f991840d80c0d00c1501031041d0580c52110740d20100c00442d481030006007160308610818554116910151007001070340c0513008006c0a160041c8038402e03182c10410f10003400c080c00585103048032140c0c8802a241910890729102c50241c869041c00748175030007190006540301174003d003030146001030381c40c0c19140346100e130303505100034052070b80d000d91240550810550408513408007040001d141140c9592803c1c8179800e40d078140f0030141c0b078007407554000f604a40e0103541e440300301c07041a04040201a03041c803401c603024030456005601044494890400e000005603c1e100481c00300a000c2d002414141140c100441d22596601c100042240a00300d0a0b03025901c0c0c2000420054800910305065400c180c000340b107601ca40311000c842c0c0c03000342030442040100c0c4080500749071a034541c03014020600d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 44057396 1250 44056146 44056153
    0x103020301060506030115030f0b12061e090d0c0203120408160816050d170a02030901170103050c090a06030210050406030c03140c18030a0803010e0f0105011b02120f 73
    0x5520526003101c2c07041c3c000390b108003c240300420007440c840051a20703000305482d01084030007420b013200024050150415a004009030340ea06c1c201800000c90702e21507080022039a0300d0f540d101c4050340756030000751400f9117603811140f83c4c624a9800381c0305041c4400d101804036181506070800c1c0d061103810540141240d078102c2c13070101d1443d101030181c03500545224809001b4884260102d105e1140c2f0620455025444030446501409404e80f0311100e5052030103941503844002c0c450081d141d07404240704602003026202e10500350524000c44506880d440b80c014954581400100444241c00170b1103031900355124400400181c0701c0035000942c00486458154556080c0030015083d9170546040d034041519058050708110f00d603915958006035100f6507117650302260324100b5040100c908001ea05445403000850401031035034001c504aa0381d0121151540c2c503251418540c8901c20703c6010300180011840058220000d00c0582a0510003403107020a000300c4080f01e0306061140d07200d010680c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 44058646 1250 44057396 44057399
    0x303020c01030e12040801020a0206090c090f0c1c02030108070f140906060417010c0e0d030e122409010c11070e060427020301050a0e060109020a0908030c010c0e0907080a0c140f0301 80
    0x80d010495581c0213300356010b00040f10030200410540c00c002800d0360500942903000c64400c809050403245031a22007846040c0742460a03040d14040e50080c4216600d03881800d00c0010300128002240b000e507071018994103110391030035003088607952024203000e0f40050100f01c00a180b4074065015140603071101d00101d41038003e071801515500f0b12409450080c0e10341c40c1d07080300088d4411805007401404540800f80302900d04406403801044a00f0070300b10b075080882a0404c18030074489076100b4400d80d4020701900e100000b045811405105001003d98400f440620602c20aa20101e03442800a000000c0c8100344000c4100e4118180c0c0304c0c1c80d140000d0311943c0f800d6080a0003503a5126070801c00c14885411080001a5150b0052003108990b41e800320b1b0317030701c40c45108e20320a40040c400041102e46844034401103074000d0406242200116005411140c0c0368107080704850300c210b10588030343d2107680e2242c0c01c000141081c203107418104039891105200100025004d840d00b00d920401147d204d6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 44059896 1250 44058646 44058667
    0x8030601090f1206050c07021c05010b0a0801060f08150f060102010906050406050a06050303030606040302010c052d06010e010f06030b12030a120f020304080304030f020c06030408030708060a0303020c01030e1204080102 96
    0x1507070003820f00b0703030717201b41c2000030b140540c03a0210980c50140c0030030b0750343e19081401d0800f1401810035070700e5103510100e21000080e054905421030800c0d40c1401e000000c0c882c2d620201907941e10007041c814040502c1c00d800103880402c0c900c2c08103078414810300001c51010900d03541c4c2c1088074012138044544580d501c00707001160f403c51003410003900054000354030b0b5041040016100d401140f0000b0704000c45500300c203080003401c1c03202000219600030038648150720b00024800c2d40008908001440c41240c00008040d01d0000a00c4c0c104c030200102004480c0c01c000307049014004aa82240e0007080b001100804440d0410040c81c080d544ca5642c032801c6402a0790b42400d84003200700000d0214010b20500003c50503000c00c5941103135060510103525170445070141c0c1132400d14540c069018001108000c24400e050000f503204022941d030703601c00340d960f034000c1040c0643e99010207401680145030030022540a43d011030080d100241c01c946005c58503d990880e643c0c07094114030102c0e5004601540d0301c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 44061146 1250 44059896 44059901
    0xc06051602061803030105040906020f0307050c10020301030b060607050a1203060f060305060f060c0a05060a020d0c02012318070b090415062106090504050708061303050708030601090f1206 83
    0x1640c20f4a18400d00a00981d6150743d81c001800b40074422039450b2050701c1001132a50441d0120b80d030700118191203160050380038100b40c1004d184020b041c010f40c0d800420710501442283d042e02da1020081145d034076404244502904114811142840342c460301c94003242d002140f6503251542036070081000c034103000c250046001d255000c60207041c2000140209603445c902c9600c0041030a80b1116121011210340514024004201601c076005481c284024504250014a96502c07280f509001c81180103030200e08981d120340d103400c600000c0b40070f1540810740d50b410085e0020035610140030800080b0700100d083c0003042d4480b024200d00066800a41d0038140a140481080d00503096502c40c074168026113030754401034031144003001101000109144540c84503020f401010010800c40c03505103820b9680741c04d00c0c01100302038400d09001440725182d07200c0c40c0300140e6055940508106c2d03180d403525920340001d403015061050000020481c50780800440d0003c4c110410881152611030406008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 44062396 1250 44061146 44061151
    0x403080f091f09090c140a0216060302120c0703080f0c190207050406081906020f04031a09011b17040c120308070f0c0f0b0406060b0d0603020a0503010e060f070c0605160206 76
    0x491031304001050f405070340c100b4003103c01840741c1200c1b26074500b0100412070801a100c0443c0b1310790010300202041196140c0c0c06860044281252044551622100361001d4041c143c801400600f0f090001101507618604142d04080c030744164904020380341340d41004c00343c0d500550200580c40781c1d0007000756181901501c4020443c031405400f5502101840c420b010030000703406081e040c0c0014013201c82000d001c04a50095420441052030b0010042d000e11070341d1404e03503000a5540c00d100122010f516844004070080c20141c507038141107030b2031101e04000c0c0d1034020026110381d6422540000c68440f910140300403e407080d80c800e03010f4580a080030b0300384030700e42480c0800c00141400034000907100020000e899904895540e41c0342e80c591030807070064100c0c1d4001080703603800400c840050242136088582030360b108545001140761282c041c5402c80c0ca04a01c600d15907802100800c00900074040c0f12a0000c00c07519180d08118020f480c0e8406540050703900c0e240720082c00c21085c0d0201c2d170500c46581c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 44063646 1250 44062396 44062409
    0x30b06040806060105130306050f070e0307050f0d0c090627060303020606040509030c100c0f0206060a030f0201020a0f0305040303140a080c0c0106080a0b0402010305010501080c0403080f091f09 85
    0x14203060804000955440b001003071903050000001d80b000141040080c100c00131603010340103100314076211b210200802000d03101600403d07442145162036203804101001a20b41c0076103848510b81c2e01c4010040c2611124609a807002642480450103440901030791001e48011284002880d0709407680303545907243c42c091401030343c0c0707003050901c00a030780881c0c480c0e080001210045050748034000708900390322030104c40305e540b4454690710881184081c0c03c190f40401d0b04d605c8588640e403e004050341c80d44030031034410f0350011307040310284001010340e200411018018070444d06095415640d0705c4640c00485001e41c0428070120b01001007540c4005200e40a04210100c1810140050009840c1540280254140500c0442c405c207aa203801d500c01c070001c0c51100c08840016066082001c54030a0a0310141e00080c207203c0086055400360a0142c0034101000c00c1c2464a8550303207400520350041d10b10000030440c10400d0050070365411100440303010046448808000320f00c0c41c049c0922a042e8410b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 44064752 1106 44063646 44063659
    0x50d05220b010e07110a02120106030c23010309030507030309031e030203090f0309010f0c11060408030903010e0105060303040e040c05060301030506160903020a090207060e0715030b 80
    0x1e4100c42e110308015005465021080300e2030303001c070a400300040d401241688018184a040c0c0c0c124000b0207400010200c0d20380da00c8070090742160303000f000080b14200e0380da246001c40982041c266030342400d040240f00020394018200e07010303d0700040c080c140d50305020302c2818026020070301608002098841c05484483c009402500262402c100b6849031441031800000000112071040300161620000c4d0040f1820840e200c0c0440d5500319500103010070484405c1d101d181c040c1000c1c0c00005c0255889451820a045c00c64400721012503039a130404007030000984011007101d043d00d51108581c4d0480c0d4440c1001d650b80d102c25840b0b20342000340040000180000403a40602510503080e40f103007400400b000444001006010103580646006010807424206038018203001c0c0c417840c404950500000300850601080307a01000034020300381d4150b44540d600d8410126030301c1c1e08a440 = true := by decide +kernel

theorem cover : BRFrame.Cov 43884896 44064752 := by
  have h0 := BRFrame.cov_init 43884896
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43884896 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 43884896 ≤ n) (h2 : n < 44064752) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
