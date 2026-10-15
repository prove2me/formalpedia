-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4500
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:49:14.922183+00:00
-- url     : https://prove2.me/submissions/26c918cd-6f9b-4706-8076-7a2a802d8d2b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 809172661 ≤ n < 809352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 809173911 1250 809172661 809172701
    0x1b041a1507031403130209040807020324010504090201090b13030c15081303020d0e12010606020106170106060909020c03040e0906061002120d02030a02040b0412050c090402010e0d0302010609 84
    0x1c540240090a0300d40c4801c103420f000e1081c08210541d000440c150950101c907504030740c1d241c5061817002032049801c029814495540340001089592583e048049080fa4180315140c0c0c0e10801d020940744414002400181800f83c1070141004480161000c0810010550304c000e44a47d202d0301d200d01c3d2904401e0072100b8030b603410500d81c1d6016402941c8203000202c003114445503950080e684113124100d1000b40074000300c00038000e0b100c4007645144841504028030103a40c0c0c6141c064002c010500403c007213469002d82d52820300005008000403101141c0c0d9201145c1d15010b14000203412420030141c1c103010402c000299141800d0000e405080b04201400341e905003a030070401840c480c40030100640d0000201c4054031a00d40c001d88100d00242800940d81b50fa45d9031901009100c0e5410203500303190003250201e8480d04004295990920403000c8401d500c03c070108218485804403030013800504401008030080c01d0000f00d040050b4400c2c00081030711601e500207402075a9a402c0151800500c1c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 809175161 1250 809173911 809173913
    0x30c0a0b0f0310080a0b190605090a0e101b0e030729040302100305012c010501030b030106080703050706020607021c12090b0723070503031618090903111b041a1507 72
    0x411404183d5000c0c00c0c2c0408c00980b418010071b800d0200203104040c40c640d20181811120401d00003a07001044071801088403c1c400c00e601c90203d025511641c0c000f0381c8440c048401c5040014020303013511a031501384034035405201c003401da5041011503d0070070008248000401038440c40440818100140c8011440390b0621071140364003c4040303503001285090004200c03111021303840341d90560f5001e180c0800e03644040804070340541869800b4003100d10400c1e80001c140306020600800391a050b500390788a07504c42203000c81e600d4800811251280c90a01c0700001349501643d201e8140302c08141c0003207018145522200304074031085072148042180242118440507031128015402d110000c012800c0c400300307803260f0f030b41c0340402085c41601c0c000c4000f074480101e0140520030141358095400c68009515143d060000c0d1009002c1200426401c4007203a040c4400401c90001c101070500101000c64507000030000500b1000946018000c00d01079550303855116503200880d04000d6121051761a0300d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 809176411 1250 809175161 809175181
    0x1a0c06010305030301240e0103110f040315051006090b070c08100c021c090e10050d0f0210030b13200a0c051506130504060227030c0a0b0f0310080a0b 66
    0x41544041b0b0024884464212050f00440521130b04902864001444610701480c070340341e84205148181d800002180010400c20900342050f01c2c4401d026091020380c881032098000006e1601414001c42c0b5078000502c42102d1000203800c480303001d11180c940089e641c0e003c407402d116211001d001c9003034848054850482c0c0401c000310081210340d0040c1c03403038881003000629120f100c0c000c0d82503040858001c112052050920301c006080e0040408442d40c000d07103440c05900700c1c1260120300894a03001c2034468240070b072003000003044019040005c6084400707406001040107518080c00c10840c000ba01c1025400e200203800704031107a071251102a00c190514034901030030a0300390398000142c07904008207621038803d000030070713102481302007032503212440c000e00170f4001c022141d0201c8203070321a0400120170311520103002503800d900b41d400103550f282c01e1142c0c94205000e02d241e021400c1000c00300d402690f8008550100032500c80c1105151106d2080d030030301e1a14181038851200c070200f40400240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 809177661 1250 809176411 809176439
    0x905060909060115030f0b1504170a02010c0b06041b0e01090f14100c170414010908030318070e0c0c150603120306030c130e120c03041a0c06010305030301 68
    0x81d640d0010181e070740c54000c0000301e006240c80c0490405465120a81d03a840083c0c110702a6150700034200500302201d009000043c1e0000c3c030846540c2c0066048180c001c207800b0400760f5405406a407810a100d03d941c40f0310304030034000340966402583c2d441c052040c3d1403120040343c2d0241e4450752024260f45d07551000400795403440d001104100140c00c410420310600c40036480032844107564520301c6d130800d00f00a5481e10080e41002c0c018100090500000c0d6480c0c400a005840f1440400e5001d500ca000044036064000e0158440c3d035402080403400c4101104a041c9035800c5030000c0300e400c0e80d04d0b440d511200750403e440000e000131020036048440c807014003648035944402c11a0102d903161480000782d64100004e0011030203a40080490815203040c0103805500c0030261100050040400000700185049000b40a10703004040219801c0c40c000c608071400d0345c0c200e4008504203402c000800b01301700702101c01e81c68404020007002d65080424400e55000b54010400b45403a9898000e04500c40c0d2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 809178911 1250 809177661 809177671
    0x19050426030609160207030c080304090f1815020f0c0a030305060d0807060c050909180f011503230a0f02040b1815121005090c060909040b0c1309050609 67
    0x51080000c41e40f198520b1a90104030850f036030b504440780c080140d090940b10b03040900071024001e00400c034404000000c1040741d5040d90304100700703110280749008030755080c44140c004100c00c441a038049941000301041c12011000c006180c4000d03204050300ba5071100b01040b03001d40014140c802896010b11944c4d42c0040f050320340700c0c50005070b503035580094410604c00524080d44c0307070300808e51180301d00241d0b104507502500405003818444100d1000f00c025101c000420b00ca02030b900d403003030360040c000e02411180c4070410004150841e40c1d0010062441420050141d80078a030f04441e40b00c0800ca80000140541302041c40307031041c1d00600054540d400702043c041c100041d107400d820b9003454002a80034901c5100c3e1000341040e4400560f20000201416500f0301c61404400c1c10840598401d9020f030318042d0864a18207403401c2400a94083d0010507940402650006000b148082c0411503101d146101406c4c6008048034900a10701002e0704070114069480041200d58106465143e42203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 809180161 1250 809178911 809178983
    0x409180b0a15030b0903130602150117030a1b06050708041709060307030f090822140a0303120f2c0c060306100909020c030c161805190504 61
    0x4200460190700301d000c15032100400300e6104d9000a11088000d10594424120100203181d940b9500c0c880250343e4040b100e5040c4c0022140d82c000500604120490b80c9542e0006000e94100030303414105481d203c031042854440f15001191100014a107441100c1c4551803a4642041300d0500c0d0514121040c0c4008402c0c09030f110400c01d24000f590313802d081d20740c40a2940b0b000700b07070307008800c400d00085c002041e40146120004035161180c0e6900e603c945000e01200f003034880f04203a072441e10250340f40d00703004450b800460703c45d014004a40b00d840c030741c8182582e03e09c02286400040150004132110030059500010101861000205169018441801000008010014800300002c0481c80003074201c0e4440d4400c80000c08215000f01b0801c03000b059580c0045458004c1083c000ba103c0e800003008a0203401412000d29600c40e01c00e5241c4140c44001c080c011040ba85091034800910002d00000841c40c00c0222803900b405017405054802c512442c25215000c40c0c441d00440d40283c058a25981 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 809181411 1250 809180161 809180171
    0x70c0c08010c20010b0d0b1609030f03030504140607030207020406060206060f0616061409011512030e040b0d0501140105060708070f020d0c0303090806060405090309011101020409180b0a 82
    0x40d0310f41c84107103100c1c01c410040303102c041811461450b40c01010056074560700001c544036840180720000307400910a206c1350101c4c00d200c1d00703c400c04a40c40000c6000c000c10f0411a40442030110340b29030704c082d50061041040611600301e0200d51440c1040440d00680060740000b000b804604040c001c8400501e400d000500850405500062000c440340c1c0007103000b940c1c00302d07a943d440100344010b105071a4000108201c1030180c180d8071444848100c1d40403c0135801c00c038113040c000412002c00d0086400d00b00000e8425003207694103c0340d158070300407081e50041c3c82d003140540035620038207000380d22032054000103000d0072910320b41c2c030141405900880c4100400c0c8003840100d400d10b011070303081030b40c00300146000c01e41c01e00c000b454000ca20000503100a0042002208254002201c18240d52001c2c04640841d500e07a001c0109507001110a001290811301c80d00c0703035a50062020510a41c5940c0015003010b403600f98a0f030440d214001442501e201e1000c121052000c504000b642215980c241800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 809182661 1250 809181411 809181431
    0x141510150219030e0a0e0f0c09030604030e0406030b010b1201090606050409110403080f070b01081b040b030f010c0203250f031b120309120e031b030f0303070c0c0801 73
    0x500da03200904030b80002403804444200f0144201101108180020515550035880300c0c803400f0018000c44507400030041003c00719100c0f803c21000c3e100b03075400040c01852281e070b03690f070121096048a90b0013500b054480b103020000800c04220b09010740200c07a81191111800e03c0241c034003102c1a8020030701d90b171074170f6002d110840d4400200c50030390340d03035210101c0e40320b4440c240031501c0e2146610140c605640420809040d0200200404d1100e01600059030142d89441c3e0300c0d920b036454181c0c3e807061301e0500c40081d126030802e6005040e05c18401025545212140414242501c00b56840c2d24010b0308005007804021590034183c800d40803445036044038074241ca0f50b4030301e02d0010503007024051203407107407001c0b0503091407040306005940e01910000c1d44c044401d90240c040c00700c01301d00f1603408040c0c243c040e9a0714410880400c40020080042c441220b15424109480c045003003403e03090b008016900002c1c4100700015401601c507070740c80c803001c40441c2c2400d6038800500d0308100740070390415290302 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 809183911 1250 809182661 809182663
    0x2217011b0e040e190c180605010509210d05041e0b0f0906040305070f0e060909060612010b0d110126060f0a03050d03050a05060324041415101502 64
    0x12000c103081e00c0000c0c04070400d0342500e01c1c0c0b104a006000381c4412012421080145c601401d03800c5884941c941a519014488800d044c0d034070314010103002641c1440101e869180500d15109042c14803001154036120903000c0d42c0c10087c18512040102d01d0000f010004c6002c0074082c202912a01206000d00ea820700a160176a4455500005000140840c10ba8620341d1004110780065600000312101e159a0f944c0d92201441c0600ca15800c20002c200050850708142c6041440340140070060040e030796408040002c1001030340c01d000304540d600c00f4a040c403a103c04800d060024060902d080417030309948001031903044072481da081c09181d82c03945442d003d0070a031000d030b8002408941c5001200e40f00804290f004c0c005610280651081d0b032411508103030154010790183c60101d00920480d5501d00500da03803184040c84100381264403041d076540521183d02c3c0c8641092285040045580d101e4500e01c1c600340040a00070170720007031102480850b602c0181c140340107014440141c0620350701c0c3d15000e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 809185161 1250 809183911 809183927
    0x1e010c0b07032403030306050d081c060b28110d2102040303030c02061f12141f1a100f09031b05030f0105010b040501052217011b 57
    0x1440c5448040124072030074003d810000c0c594070700c2c40c0302074061503c2e4030b0100145000342c841900400c3c54400c001c01d0505102e20540881900440701074a815442c1c506815019900603d6001e003595450010a00c9100d240060281d84054045440e0018a004000b498001905507640030b02851a00d072307904682c00414003a0310b2072518100f244403000d4903800f40900e10400001e021220380f0004000c004c154060340550750010301075088400716916165566030b44591031508a0350f071301902c00108035094a450b0b06030102d921540e10f001d001004404100d1070301000480d20300401c0d0942e03000946119140c4258580029041440b0b44514840004144e101c800c0c8140d503410000c00300385043d0405e003d0915107004652008052a243c1c0305160008624280c1d409010f10034092050021031540050080c6d505844030302000a150a01d068015101a03020055241d0340544a0140549818000f4460001400585260300c140410580c0e10307400c440e400e9558410302d003555988000c0d45a804803007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 809186411 1250 809185161 809185163
    0x1201030206030a0e03190f0809030d0f09060e1c1d06090d0b090d0f02030403122106151e0c1727010f020613061116030306051e010c 58
    0x44a95030f5107031602204040e05091350074880c144000584068007400c3c640706941001a00d95481b00c080d91002000c4940103019159a50103a0050000341c010582c01c2d0b005c032607071040703400300043c02c601c442d560281a200c2030712008000d500b0004070b10054a02071008400200564a4000003504a108119010100700c10143d40203050216160155494841e43c400030560004045c012910300f003507005c0c0da41d5803004822400a48290480883e440c00001a6410303294003000301c80d601c10034642c0c21243c40412084080510180044102c46850644680c3d00904501c000c1c0b0001c248031014064081a0140c011684441c040300c0b100042640c0400c2c45010241e00406801124019a082d955980151010050904801c0d000342c1d292000050602ca0f038590283caa2841c84410300da800d1742c480c00304484203040c40c41c0030729150000503000d0381f02e401011481e60f4650300300707014000400c8041102c200e00f01c01107540c49100f40018685400700c5103117072041884202c201303020704000034001090000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 809187661 1250 809186411 809186419
    0x608070b0c0a0f030905090412230d09170708040807120b0a0c050d0c0203091306030c120203030d141923040c05090403050a1d0f061804020301140f040212010302 71
    0x1200f1404c1520850510300144401090055039060604001000041030705990002c51383c2e6001009080d1101036144041e410b40c0e1114500307020006e00210043d0820399001c6819070302158a90504030418009002e84034000d4001c280c40d24144640d0b645003603080d0b044603100207910350b0403900192030142c8003a4080f41104021403d6165501c00b82e45602801c650f800c038450800c01445540b41d8004040c144000e02101c0074101087d0b118051811291103000103848181d50743d000703000c2000d103002071180192010b82102d14080e01c80410908403960710707080c20034081d841d00c1404079031801000904809001c040c0c2c10807500001142c48089000c54210211141040c035000a0a02103d11901c2c0001c101c06000512146441d1070b00a0055105c9900030b40070801c14200503a8070f262021019140000242115007081b02c488108403041c3c01040c1000d421948840c1e02444645440c0099402030540d4000903242c01c403544200325507001040c01d544d014520500c0507002c044c51181e260390449030195 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 809188911 1250 809187661 809187683
    0x909070f020a050f160905060d140313060914030f07060f0504050a030f020a0e0411040f230a1a030703030e060c0303070903060501140d140c0a08010608070b0c0a 71
    0x244264200041001d010b003c81c0164101000701100104040724144102988005141d0b110800c40b421290140d4406422009002c484030008945c415044100d03200300d41100c1c103100d09000d10700740045543e0041000510154810021104000010401860128060711040405800b92566a0343e644648410809484010814640607604a4014010213445140d01c0b9450b81054004007400c3c90b022401006402000600200a40400d07802241d11030ba0503464603c2c007808002c081c00341d5080c103d41c102d5031961f0358591034024440d8255001c3c01d030305a500311440c0902080c81150101e01c03d9008132482c520400146136804100c06050703e41c981004070b4201d000b000411424062000018030a1100000744950250449401070441e8401d00007400640e80398a4200700406401844503049201115400c000501c04881501407000da0400c41e9288486080051101041a40040c44a035510034081c094801e090043e0b10117003482020b241d140c55154013005617146000b200c040d019410503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 809190161 1250 809188911 809188937
    0x2c341509240305011212260a0203181204050f120109060905010b03010b09011a040b12013002010815041811030604080a0c05030f032d1e151207060212090907 69
    0x602c1d44030740851100382000c0c500d28180e580c2380c00075030040d1001e50704020003540d01d00400100280e002400080300030820300700703440c1c542800034890850691a90100080c50022020002403090048150154102203000413013030a00ca0700311030030107a481c0c1c0a40d052180d40b000d9601c0380c12003541103840020309007001209806141120b8007450f0464041917900141e00d001444080030200d05840114007144c1540c4410700c0281803400b58544d0406c0488550038120000d580a0580c4a50050300e540b80e210a5010b50000202207400c00100210010010201038080c080807948003d0303420030680041910b410251034513546402408519000c201d81410040c0400000b031056412103415903687e6920303820b000100806680310f1f000c0c01d00e8a882c00b05440e580741c0c1c0f00c805026026211640700c00c1252191a10f1488001500601541c01c982e640b8400401d141c94a10348490200da039403016000003805c048000b07040000302e0140d82d80401090045090381e54800440c2a0411160304055042d6034031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 809191411 1250 809190161 809190197
    0x90506040f1415071211030403030905040504030c1b180506030a0f050316031715060a11070e04062903102c341509240305011212 57
    0x503c005468284080307081c10400a03442c1c0e1100d640308075911510304070301034103074610780d0383c06035110103400a0a0010304022604282e4030039030300503000b8908210030a00c0c82d290040e40f1290b0056100003100600010001d64142e00c03140004008215404c1c046400c0260001e0742d65520500040c000410182850040090420071034145269001d0300c101101150708010b08580d11a120744c6648070805000a940920700b01c1d0f0300380e59140c0082c0400e00b8aa2155422524141d50005900300744c8030706180840c02103001d0b040035124034820361000c21486403400101c5d41c468000c02255510200b0724101170040da50110302c440c00390102e104006801c1a51032016a4040013101840c2c01450407517202da0044000401c031405404103042c01e80b0078140001c03409000410301000c22205c5d4451541043c8803038a0140c00350701041e40e052400c0d51049403110f050071044407048090903003101101c9090320b113481c0c060085a004040a200f4001c006907103446442c0c0341d055030200042080700f0b0310130415041d40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 809192661 1250 809191411 809191429
    0x6050117060f063c130e10081e0d140406030f1407030e06090d170406150f0608060a0303170c0d0e010203011a03270c040f0507090506040f14 62
    0x244d600040040307020100d501c5500300d10031000060b40e000503000f54020100440c00c07551390f2444001c0c146400c9191101400f0b0184010708005c0c0386410407a400612254204214805580b40110304442514082085490000d0303030041c640500c250503100c003000900c2d20082d034040b124035060114248280306144401440004100c01c40c1e4100070b0103001c5a55496403000204103034078011a0090b0311800e413080d83c1d6690703e5903800c0014400ca01022000a4000d0080b50030074410900464101e8102c509485940e0854000d01c590050300c420070419a607000854a8210030151b583c240507900350789005051000129018150250302d601155913400840210381201c0c8076200300300862030785402e600b8041d5200b8400c0e000210082e910a44c000d200c20340440c0e0040c0d01800034901c80000c5900d0984841400d04007180e06801040104070990b1a980a4405840e4aa05000a461400c0e100151201240d40c1195000d0181403005102c194550503e090680f030b403980a0802c800110400140d04603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 809193911 1250 809192661 809192677
    0xf090d06050f0609010b090604120212011103040b0a1103010902180306280203250e030d0903030f0804030e0415050604030f021003110405100c141006050117060f06 72
    0x70326001c100700886480c1a045801910100e03071044081e42e0f81c1e0002c4a65005081c1195071003078081200704800e18103180c4025845e03101814088020700890303200e41c2102d4500b401318201c00c000100b040f08105a80d041035a12450b80001040101c08507500071200740014043d41444540c000791042c6801c45a02e0080d07002c90009049400503d081800f40102e0300e00c400c0115600407071001c0d191840d15450082da4403411660014040440610140c1004510780750400f800b4400524151195610300b40075800303206030f2586400021030301e1841c00030912540075100c4003c21450300c0038000020384c000b660400344603007107501082c0712640d14550320841c103880d0300165002c44002400001c10203647c551054460003240d9104031011000000c1d803c0ea00d02d0f90454001d04010270052200340b0f01030b00746131110945450301001c01c030300558480e41400b00e80c02910410794020f6600e0601c102c203501901300500801c2c40c0c02c04c81603290300580c0c1e0443d10040c000e244104526800c041c0c19071a140e05944800c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 809195161 1250 809193911 809193923
    0x3020c1206040c0b070827012c0607080720120f10230a0c02010e0d1209080f0703110c060703080c0901260f070804080306130b0a081b0d0302030f090d 66
    0xc12803c07040f076042441e942110b408154410036042804203481802d480410380710b016000f49d040d240c0c003049070a600100d0100e400a1041c400300020030140901c0b01e10851100109150440c008001c204044a0340081000c15a001011140011001081a81501d404501c0c00301d5241d50305240c4c0c1c85004008600c0145d1000e01d00d0802034550211f800141c840d04d400e800802000004400480d02e0f0710f00a0500e4000c00d00e03980800001c0c5a00ea40079110283c001e40c4042c0c10311500480510803944200001d40000314207c003501e800740000d02820201c203200302d62251500c240c595000e4029030b40101a902040d1340842c042032564010241c49808070130300150100c40c0707141010034540305101a501010b0314019036001400c1c441c01510f00b81d010b190004c2200c0d04558900d001c01c12784041132018400d0854483e5040059038445000c0385001c2c1c0740e0080a002d1344407002c584001ca14444414141c82502440c0034a40800e0300442100c0b50fa1000c040810781eaa040540881d20340381a6000007490 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 809196411 1250 809195161 809195197
    0x18030c1504030c060201020f190e04020a030504120518060c0f0712060b09100312021608011d0105070504050d030207030b18061005100c14030703020c1206040c0b0708 73
    0x60034a00100103803031040b51001203040c0c40b1302d4228202d000c1d2a40d901c1028400b0400c59403009200d05030000d4005251400003212031041c0301180582c0c008005980c0031030784520510040116901120400000e20b1a2103805c0c0307185030010403c802030740c0700868010400000c501d01c5152042c051991024076007021228900c0c0c0d01c8402040f080400030003554500c1c50242d0750042d0b0300c0c10416690103110200c1c2680e070440c1c00d43d250f46180c1840700040c0b5065201d104900c3c52201c02030364219000300302a0300000340c00a003050f80c0b0b5164400303500134584143d1400d0204050356401c4800e807400e86030155903070f0448800c40d1030281e280c0034590300040d2561804204000018003480074040301000704000782c5440344c030781c1100c2503201c40a1b40241ea500c0341510b014178041500c10410440554042c501c0380754446080d190b1213081d50b020400940040c0c2200100b5081c130705143c1208420000c480300104090300e4680c94484071100c050103081445400001d11105200c40b030381c10707141c5011241c0c0103110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 809197661 1250 809196411 809196439
    0x4020705031216020d0302031509070203040501090e01050d0f24050a1a0d0b151305040204150e0a05190507020a050d111507020a080d020d051b18030c 66
    0x6502e81081c1c10710041c00b015900002c049190b8000400020729030790300100200040c4d200240e0294100a003601d4060080c21304007580355a81c40405c6019568540203941d449007420b000500884d0142c0014548014020041005450716000481c001e82c003c83c1d1120044428a84810700020020821400001200f5000900b039015030003140034101482d0704100c50b20805002004510300c40310042d0340301c910100d950700800cdd580c0d00300c0d0750302c140b04045c00150507132280000780580710500070301c2c0760b1103a9803020003045040510030481e091074811992035001d49083d02a0a1120000740512452034440c4081140698094088980035404802c10321040c40e01040003036459502d08030640300c0d40f0032289483d0110303010b20021141c3c2d03080400a409815002d04650340e1144001c0c051004600c01c1d500d03d10042000c59020300044610500e000d03a83e04d40060240054501c0540100b49407a2602a0301d020100d49800300c44000b156481c03509034821601000906003064115815040360786c09010315 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 809198911 1250 809197661 809197663
    0x10f0f0902280e0a05010e0306070309020f0607080714010504082b060b1206043b0d050a14040b031f17070504051003052e1a031c050d1104030204020705 67
    0xd50303401c8042c0d4113900c40596440045134803142c0e245140c0d4064000c20081a0070742d2207900070010070b50010b07081d000c20325101800b0a41c3e80d400210261941d00005c00d1290422044000111020900300005d00c090b040c81d44070301c10b061240880555070440862107203c2034540460000303030b40707500182040003104c3e41e4102c01c0c0c1c0c00d50300100c2c4621040369940000b4050740b51a03c40d06031101403019010382440cac03100d65a072030906006102c18480b00751a0b41d503400a60404c01a100c840d00759560791540714500c0c1000034013070600c031080112260728140418480307580b012003501e5001c01d030410b007000c3c42010343c0315408205181d6040205104001c510101040d80000713000c00440b8410b6a0404c01c95aa00b00e25901e070000358000100140c0240244030461045131140152603400b0320035850103a900140382004680302d001d107507680710881c005e080c000f034035043c4440f1420804001c081160840b03c1070f0000d00ca4451024440280769a41318508200c0d044034084e280910707030280007107649002c10f080403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 809200161 1250 809198911 809198927
    0x2030109061508070e060d090b0c0a14030708040b0612010e07061202040e0c070312050405010902100f170711151005060a02070e06040f150806010f0f090228 69
    0x203504007000c68920a103506205014492141c811540ea42c4002d80845c0c007080a42e0340701803181820240c940340d650001c2040200307568011080108169510703041c0d00c101604010008083d511400814020044000e4114007031592041d406125010965109030001e100e03000d030008808072943c07800e12194003d6000040007800da0342262103407040d040f04000c03200243e108030701442c111215204045000700303012070040d01c00b00f4841e0404e100503c80c428040c504035501110705035a207030345400000d01581802c0e82080303038658552a08404103014207901800030584100200f006066903000101030900c107600b11804d40b61120140c9003040c680018102c4e00040c00c1e02c1102c2c04407010b50f0001150b04c2d01408850031489960040c1c511030f864920549602000145000d8216031070b65103281c51030b0380c01d2044e401c5812550786001025820f03c81240c0c40c0000580246c003241686000601c0f0200344415008100c032102d0b800540c0e80c500420a41044034905860141c032100d00f0350802400c960450a1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 809201411 1250 809200161 809200169
    0xc030a12030f09050d090f050a080a0611160605040c05010302031608070e0d030e150903070618030c06030509060a1a0913080c060912040b0405011d09190608011a091503010203010906 80
    0x400287e5180c03020009a004a80718045070365002d48420780001c1c0580e005540030030f800081c3d140c03c5c0700d008984c1c0c0d84a0000d5542c00c03240d0303960341e00070803040040600c40400546400e10b411411440d00383c40b50502d0710000710220b4140f0038003100041d403240c42003800442181001c0e061192046a41c90064161880c0d40078491140b81014190b90840c007009007600c4425a0040003000c8043c50705a041c1c1d04ac0c04200d4280d03441d0151076070040301152021107140b000f880d650360f00068504e007484046040900140070142e60509200342d07000005d0745442c803000c6904040364903041548070317100b401c44103800e5920010032842c408201624400f1000c00c0e180d1207070302d1040945401c2c0081910700240c2d0320480c082c4c2030204034103000c117211a507ca06072405075051100b10380d2484c0c202000000c1d010820071594202d0307100c014541086141058054080140101c000a0000394408140d000455500800c5180076011103800030390107a04450300444042c0c4081e000b10344e00d50311640448060800c50107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 809202661 1250 809201411 809201429
    0x70201030501080a21051603080103030e010e03060106050a0c0209130209090105010605041214120901270e0603030d0905030307030c180b130315020301080c030a12030f09050d09 78
    0x1070042d808031340e582506030301510402c5080d013900d022030002030038004a01c04010060142c41d500d80303003d4081c050107034004d071910400ca6245150042014200304001810800c1140326106103840005000313040d42e070702d801c0503516008000f500312108407841c90081d601600503000e20030994910241140014020340e02c203500e0740e503110b107203c0c280c407000c0c0b2840c000110104400c1080c640c1603016411800d2061580300c032024170443c501c5240282c0c031202e2850fa1400001c503c40e2541e000903c101c1002940e00c220801420700c0c15002c11058840d110b0070b1484080100061303450703a002d00031202d070031490000401081c03e00d800c006030390b604201d40617000309240030540712206000b85128001800340c2120b101c03099007024031803400c0340c0003e10701c1c01c8032402401010002403005248000320700c0111800580702d41c5840320300d600c0c000410042501940080c3c0f90840030840da0f9a402070f0600107030801062501c559210301d0024a40c0480103080c80c05540c440c0b4032120b9120b4041c8040390316810b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 809203911 1250 809202661 809202671
    0x2031602120a0f081902130906080d021b010306081e10060e13141b0312071a04020613090c03050601020c030d030f0b0d0f0c27020c070305100207020103 67
    0x41c0c4026101d102c2c51903020042000000d40f180414400c140050340101d01078180e99a0310302894018050760031042048040800b8842c050100c1c0d0703054410315009041d8540103103015141c0c000007070345500740c8582011540400900c0201544d001e9007200c4010f15042085070700c0f01110314192900b0070107c0354400018095515241d03040b80950180c035080d0380c00f500b50260075494100d40c400142c1c244035811140c10998882400c4055011f03c10080c9003000288a00841c401030700170142002e4143d01d4003820f4401c18403650b00401d600c45e1141c40011003000c5414840d40311400041c4290180d850303803800f010b0940b00c012400505c6900300f4440200d864174240840d8a507000160384400f812419590150b010301340e01d01c0014802d41040c44907004550f800203105020101040351903071914016604440100b28560800111050798002800c50b41c0300889607a001c40c2d086840c800212904c2481a900440c180c03802c02020f2001100641e03001003111101e0400a2415010f50070650b0f040c0d02285c40c103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 809205161 1250 809203911 809203933
    0x3200a150e010914012d0e09060a14010503090307080a26010303020325120f0909111c0b0a1707081b09071b230a0c0509070e0402031602 60
    0x900904081d5a4603003520025100ca10004445042e900c48845000c04508640d10340c22203120600d46d54104026603410f01443e1a60302400301e60b14025004501035520000e00300500000003030400c10403002481e040f5030340c0e1240400c4034558010380308040d208040010301c280c003480d00011000c40c4144c45940912418a50140c91a03402009201c040c0258004100c034000c0b0003148400700c0303018510040c000c01e10580303d40704d46d0012182d01a045010451a18580c00b850ba00628001e00800e1940c80501c4180340403a482506401900040c2103151110003090340c00540b03d8000445240d400780074200306a5544440c0c40804082c0c403024400c902507044041a00f2002292041c2c111074a0121880c009071100113220040f50010611001c225101c580c07100d80c0d04d009240c04110300d010700341030611140d02c40d007005c0441c2260215901554898610840003810103450142103400459204a45a803044000d540143c0d800009a600600c00020040c0b410044032503d82c40000e16401c44000c190b00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 809206411 1250 809205161 809205167
    0x16060207150c0201140901030603050a0803040209160c0201080c041e03110f01091404090b010602010509060a0501060f0c17070f0b010608040b150f1c11010206010b0403200a150e01 79
    0x10642e002e4005407900c00390b070120310b07031460080040c40d5043c0b600254070380e0390b83c851504041c40808200e44500b800001c1c03000b503107001000650011180501d8160b2414001c80113448101503c80c02410322400c000054500205442a03c004002302c0c20907085079400c01502e640c6000103804121440c00207400d10302c45a00700f61400486514041e1603030f08503e810b00c6d101045154109960301d0384039490300d11240003d41c80101c02802001203400104840c100448400e003442c0e4001c1c00e0003190780c40c0c640100400c5921003e06030600b5004c1c1409062003209050080108009900c0e80d10030348000a032180070800c14072540d010440c0215008141030362103600132a04148180e40c043c02240344400440e445d40d2400e08a50b00d18540140724000116200001c1380f141d1015114180746140c4848403d400c0c0070391100c080c00700072000d2025003240c7d8104454108203014500000d8141d080d031543d1030188100d0102d90554030b11005002403000c55a95100003581d0a44010707900015030740416000941d40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 809207661 1250 809206411 809206427
    0x6040608060102150c090418050f0604300c2303040e0f07050910090513050108061608070c031106040803190209100507050c0405091b1207090b031606020715 69
    0x1032100d40380b45003524040c2040043d22350044051503070442d5100140020354200942502d40900d103015161074070741414007210b0041a1040418000400d4005e070040c2c15682111202c03555071800d15829102c0c02c1d0500340030b617048800da600c24241c001d08400e907500e440040940112440c18161a480703698000c4020941482a81c0b1140420400e200311000c510b0b24450101143c08117243c5014100c1d610b10005140e41807a00072000b202ea914001800b10320800d101099100d4880c00350000005803041004002c640d00030b06540404c030391000303100c007010b100b0144820002040300c100c0d00c0320b0806040141142d48152071a1140320011600190542030324001c1c0c6541000007012800d400410b5081924207a126840c111054002c40341414850f40d582d204031802540c004004010483d80d800d419000001c0d00d003c1188218420758908001c440005a01415507904481c0400c1081640c0040b81c50b0240740300070490b04540001e40810085d80c006a86401c0b0b40d42400c403000d02c11800842620146 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 809208911 1250 809207661 809207671
    0xe0c0402120103020108041704180e1504060b0301090c1502070602070303050a0807110303040c0906050103021e0c2b1d011e180e1e09100903030b0604060806010215 72
    0x181034807004001540c0281d0015074800d0090000b0301426161500c4600680d12a8000d159001210b02002a1a421a1140c8104071305810010100070102050036041d0780e9008000030002d07926048800f00c5500c003904032000407944015000c2c845c40d114505004002c080c4844d031001880340cc2c80000300b807840010740d4000c0f20b0f0181c40f164a8192490070840300407400400160038040e40030092a01d40c04204001c42c45240540906005d45042c42002c000f0f50304282d00c5a41014018007400c02041c1c5a100283c0000482d010320076682d400c1c0340b402034103000031084011100085c0d0250403400981c400c9000080d2280c03540c40560444c4001c0420f64454581080c603070000380301880c010325045001030700a00d4000c40e401c040c040401d09590041080c2d42c5c0b030708410440c072444c1090003103901c0c0c00c10030542e903003520361102c60452800908241c2d50700f0010582101040e04c403c1280e0515000354041c8001400141c18140d443d6118800a045041d0941d085030040c070132074011140c1d242980701a18095 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 809210161 1250 809208911 809208937
    0x30f040603050606130e07080117100e01060e190605270403090b2d0405101412010f06020606040b09011a0f190f0216091a12010e0c0402 60
    0x42800c04100324000c2c10020300d01ca4001008000e00b40b000c2e800c510450b4018044580700e00910710704442c0040101c078041e40180c07800328403490416404100403d9500c035004890f2400180c000252135694058075440c2e10a500070362112085c40000e02d600b21030000d0352108146d083c070a2513603e10503c200c200b06841d401c20000740c5056004510010080b03155007090003407801000c56a155020707a040c0d58401303c61401070001d410034003810060f100c0d281400708806c028400b800d0602d01030200d001c0d820384a404c42d040103551207a0510070044041643c5128495149402e441e60b119401d00108c0300c00b82c06104054801d03c0c00054191030107020b030103c0c000d4060484000c2e6440e20544118544024000e144040018441c40c01090300d40300203801c80030020039000440300000580502081244914501150820140711001d501c605580a088400001001500d22070102084603071640790078915622540390845206416015005082c01742841c0043d540070000c201d003040101e00c00c421404000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 809211411 1250 809210161 809210167
    0x50402100806060723120c0f0105091507180f0603050f1317040902181203190e060705100504060b0d150903140a02151803030f15151b030f 61
    0x140103050411100a4400800c454400305d0f0590a007054005072049491103404102e103012880c0400246508230311003c001c2006061014409450382c0710528407081210340b40010070100e034030034070346108100314803500d0885444c3c68408001c0c2110543c0308150010381007501280d100000b40b03d6a0740581410001c40211080c0b42da40c4a4003c04a107000980c0c29205100005108009000800854500154400000030404104080c000310300908106550061040c402d07011082c80c194001c00c07106080084025014400044540c0700c0d1150040075805001200003080040360443c7e0b000740c1c40764005218105103003040c04010140000c02502400c0e80404540c24040a40c0c820b10050b4040c0c0341c0400710000080303000300c10780d000b88400e40041c0c1c4072030420801000c0715038403141c004a42c2800c0c0a010075503050010703030320700018040070107440912000c22a44501141c1e10f0f8002140508120b550b00920740e4904019000200c0400032200c10640072001c4032030220895400b61614420982 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 809212661 1250 809211411 809211413
    0xe0108030d0c02030d06062003030412080603070f080a060b151b120412150c08041b0302040501061706060901050301060c1502070b090d0201060501140702011e02010504021008060607 80
    0x1c003a15512492805600042261040d11681409100c0c051b10381600c40740d5032a510f000583c03084150004040120350028400e101c00516800c0e90025032060529000702c00d80c441c2000282000318503405400050800f00f000101c80201046440400e8001c0c902000301c080e00905200341c044010068640303001c0f04103c00259000d08207800540d07850018111014003281600c006010b500540006011240303a03a8504104150301c0c001e43c0700340e02d000c032040c811080e0780344000d0000d070400b903c0101545002c02c240c05200e80340101903c01150024818402940d50303a80240c2031a86601c240c00983c800d4038001003142c241a4110782c41500103941d854a10382c40e103102100c05001b4a90115584002c080d046003001e299070010303215072801142c0d459064200140c005107803544080e844c0c0e040d64188201000703642c0c1c20080043c100d0704200529991182a032004880400b906c007255464144c0d030540030500d49030f05601c4240703d980300b91194010011485002c0d210040100c8856070b000808000b800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 809213911 1250 809212661 809212687
    0x1b1e1309030e1018080111030f1e0a15060e0603010314030d0f060e06010c0c06031d0604060c090518060418080c0109020f04060f0b030403050c07080c01090e010803 72
    0x3a44950003860074601d482d9551000825000025026400158400d94450404004050350000034900400200141d0031244000c0d113240c0402071a18501203090b07800921107900b038102c114990504149182001e24211800038000c01c09200c0315019000c151102184083c092031285c001e1003c0208a5030450703103541d84140b05806134070562451400103000304880320340075000320310380a0345481e80401c2c00d41c1848018108220b004107441c2c1004180030240003c200510010820f5400c903180200b80e20040001110300d08200c0d1401508900c9614100418001c4590004545800c02d030355204040760341d0000c000c0303012141d8407034660364012600812020728190340b010407411002074041c01d5898440e110351069401500c0364000994440d2b07823031001c40c0b50440b140c60b03003400c2c111820007000c0c2c100341c00a606020180907000340e0001c000049002e050088003564100201981103840d825220000700c1d480750030340c1410501041240303001190b001c45001099050f6801c3c01e00841c20141420800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 809215161 1250 809213911 809213921
    0xf070309030c15020d0c030c11010311040b03060f0f010f0f0909060b2d0d0b06040906181116080a0c051e07090e06130809031b1e13 58
    0x84040c000c0d100800000910000d100700c00810103082e03904104009100007900308840861942c013040000c072900b900103070700003c18408540c2c0109a10034900a20700041e0020f1034400c04200c04480081000210b60301d0301c81c01548550000d481e013090b50440601031003a0240c0703000c1e02c540880c020075007070f2019510a21341c4c40781d070352442d10f44a42e03200c1c2e4400325031007154010b820404070214001400d142c407207605000350400c5000e140b02164070b8000c4a0700804240218001103044d60f03201c10003146166148015200a0001d00e41c0c20801d095031a01035001041d1000d0000b03181c1d83c10091840310107415801524100c1d101040303d16021030b00d59503404883d80c4100f544800740541e116280d40455003c102405240740a00a07141d1001403c842c3e091801106a125044040c00c2c03c3c0034040c00c1c9130101d0102d400c102100300b0741c4a020841d1410070300c0c0d8014990780ba6003500c070307180812003502d0f17503d0b400348404e06064900c01031942d6031504a401c0c058840300359640024841606c2d00b4490307065800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 809216411 1250 809215161 809215163
    0xf030b07031b080a0b0109030302030a0e0112140403142a01091506080c0d0507060810030b0f0132220e0715081501050d06090921140f07 60
    0x40010402d1030b42180103550005560b10000164405003041030041c07041c841c94030344040c01d08082032100c1c91650f00030b6a91084200300802c12110f40c0000b80c40f40d000d104a00d01d891140003051080780d0f40481181c013200c0044400740d00045413030344034140b5010110304035001d000c02654640903503070035199215055401c0c41140c081f41d6503243d1416010038054505050502117001d0003003a641d2030070000c0b510300791000c1c1056228030f00c8502e02d5400038000280718001c032012410b01200540d02e03148940b0003261a5400948002a00c8080040501c02c90b04040d05941080395400c80c1c0070414489401c1c0e0846602d00190b0070350308040c40c029986880c0300950b00d81180025000d41d0711074107800700030540d44802c82410789a4400c43c0e00b8080700c034a0490720101d03803c56141840380f0345070407004800f600030038a071080d050100014910f294180320350480005061160414080b520640c41c080340d40070800750950100d80c0600300c10340030041c841d03030602108504800d0030f10309041024507840d280d9401110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 809217661 1250 809216411 809216417
    0x909030512040f030801061409091b0403060b030d030b030318041104080a061a010c08130b1b0c0103110703080c0405180f01120f030302030405010b280509010f030b07 73
    0xa81c10001c01140101e12561251901d14240346451038042e007501410381180d0306201c03018594000082c10002615208070045a164210781c451880d10808240072125075044558005004001e00450340c000c504440406d40442c0d0b510603411004030708403100300e0842a4141c108100b00744100c00515140d1f0030b445801000000c008001c0e40d00030410798400c1c2e00a40071071b00900c11000a0120510a10224804810107005a2600307280000c0500011401c02466a0000300303c1e114894501d482a00180c0b1105000c0d640d91030407a03c08034041a00305601000c0ca10a02e2408551035100780100d142060808098505254955400340c0780381000429510a5000038400020580d4445070b00290396244000311825030306007441d51401d280c2050300850401820026140c000416400c105440e0f1a018135005840e40c41da4034026000d800020b8002d9400084210390400380455804540b07220040c00e280e10220565400500001307140034425074009244070102000441c0729262171580c004c400f85 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 809218911 1250 809217661 809217667
    0x60102010f1b031401050a0b0c1204060c05061f180e01020703080403110606130c051227010b030307061d0303040b150105091005090a170604050d1809090305 69
    0x49004221180c1d82c0d2401286007603070b44804031040c0c06106940058144c0010711441d0b44c104008902480d13028032510400300c4001482960000d028000441600215001255a90b0b590400200b0680005806031103501176040400c1e001403561034000c0445010a4048404034500700414017a0502c2c10428001c5517111001c0c0c80e8505003e200400c82ca0344a5260103403e400c05040c0140400b0798003a96900c107500c41d83c14416640d81d000c4100fa40407000040100e240a840703101200c0f04e005400805401c01d03d050f05124403100007a20850f02130405c1100e1a40300503504600500345c95a0700ca41603010b81040183c800480c3c0c20f50040b07042d5609140381e800c802d0b40b13541015840c7d0780c0b04035000d81d0701440c401e040c032000744094041001208003d103081404d00b0401c800080c8000c5610340c2c85001d00900040e411880e480f229000340052420300105206221540c00c2c480e11038030200c404440600641190101c0e090050000326140307805a28a039110609002c210002481c00060a4080c080c0034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 809220161 1250 809218911 809218931
    0x10110c030105010f06030e030a120f02071407060f0903030c0803060a0f0807051302040b09040b0a120b060a0f260712110306010e130f08070501090318060c030f030506010201 76
    0x9005460003400c0c600c0b10a1016854101700404688001081507541d4008211b01c81003903a200400c5085041e0050300014450085100c800080c412100000d10964941224400c444c2c0041b41d042d04458864407044080306284000700c527074240a02000f0040b60040c00d5000208961202943e40100701800c65403040740c070b82448814610007a80042c0240c1c0c0003400900250900d404040300702e803140358042d4101410300440300800c0c001c01c0e5100f800790703540d00c0c0c410115503905203040c40184000b12203200703905958100300c80c00301011151140100011040001c400d4020207501c000c6902c140303c5400200c150340d4a1204505005206145900c42e13030344040b4041c0c0d0130b80d1050404600c01e0702c1c525011000c1c003041c982130800586c81007803405031100401060302d0010015500e03695200ca00d0f00e0f46a20740d45800100b46c0144000940b81d90700e0300c0b4400d8101508003107000c80d0000d0202010980980c0d4041c00c8030060841240240000c2c0030f101c4070740c105c41c0240c1110350130442c1400081403030052 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 809221411 1250 809220161 809220163
    0x60f0412061104150f0207030b0f07170907050a05090408093d0201150e130206040816081b1806030a150621081204020112050103050703020f010e10110c03 68
    0x3d5002802210740e10901e4440198001e03041a003440010700250207580d1031625803054407200102a10b13542d0500000241742c1510540c40804a901c05914a0300b150602c01e0390a40d441a8500880340104461305001c00ca9160840c1e60b50711030f40e80946550f1a0034010010300400392481526a2072141084c2c20f800400c1c62500d403006000348282d104d203c40d140c0e504000070b0039260501c1490441c1c00221206016260100410a9000140080c50404000c1900c0030681d2031066a000b0b8400713000b0f82c0011080f0b500c5180c8910b0849441100301c0384900c2a07003440802c4010348d000d2003a8440308568841039003030602060a580315500800703949404900b911200009554030701042c005566403d01480441d280c080c403001c8801843c0080f03031b03000105a5274104284541c0d40740021242c0240001001c5a2003085850410100c00c44e0a11031541c3d60303e0700c1c5030744522a0208a1103180d900c0c8422000c3e52140040100c0d0400c01403681500350822201681c17400340414404015000e508100d11090714 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 809222661 1250 809221411 809221417
    0xf080c010608150a05240111100e0f030c190609020603070314010f05091314070b0d11090105031603020d14040c081504060507031d0604020f060f04120611 68
    0x20307120203408005500b040103843c018000b0000c280051600c400d0000101e181b031340c039501c0c64482c2902101c6128208006132030405071301c00c0682451092031780300c0d00300240c160054602c240b040d80c2151611000360201c00c2d01c0380100c503200c06140c1d10000e402400050301194110781c040c0074a50000341c01d205900400d9040c1d10841c0e9030404a03480f00c100700d20b0495001d400c18018105e030301c0014030301814500014103005010700344082102c24070011106000606111180a04104046035040382e52460700d8038043c1c12040054061528100c40003c806258200301c0c0d4a8010581d1040c0c915070781c40241d2010744403030000e03c204150342407040f048015868450106440e180c1c0d20300d104c69242c01c1c5030011445000c0d400c8460150044501e01c0a5010045101c40d0030661141b404078282d41c91880840050105041a0092440002040300003840110f03030744d4050340c02a11181e40c0510349105001080c8654035001541340c80410082280310082c40c12039159074454103002c0f41e401203e14842d10160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 809223911 1250 809222661 809222669
    0xf07060204211a011401051b0106030506091005010609030f061b1d04020408060c0307022e0506030703020112091707061521020405070c150204061101060e01030f080c0106 75
    0x1450708540c007062024103c200180c1085059119000d03604040100c810845201c0801d41440f034049994900050003400c4e00c0003c00c07001008000041d900d080c840d03618030081d60b152a860191039556504240b8500501b4184c1d41c2e9920f40008040c991b5542c404050100d840c140e03125581c42ca0b081c1500341c000d0000000c2042e1b5035072540c465981150b0303800b00340d041d10341c0321300e1080348100000c00c0792640105040c0d9201c3c0c070b030024a07a120ba0701c0110a070b007040c6143c00d030510700084007a003403030b0703440c18040001504180c10602080759581e041c0a0507659002800080d011403252a1304a400c10250340260400c188034188440840184941d170b81c12035003001e40304035820f54440442140c21000c4050301030041101101c43c01d03a0a82a80b01ca030120f001d00f80c006800b17143c5a0002801e4940501d480e0b03008540d0000b83c2d440420412100c8200075001801544001a075000c1000317500403050050318240c0d0514940251a6480c50742d6401d00007072810801c0300c4000e814000342581c0c02d028030a590041c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 809225161 1250 809223911 809223959
    0xf180312090c040f02070209060d0c0305031207080105040e300d091b180f1d010603030f02071d0a0605130603050601170309040e0c0307060e0f0d080f07060204 70
    0x40920b000800094030004030003240d42074414440c40c00503a80311118250008010740303480c15507072100c1c00d16403030b00080c5400240803407200042c9015080402c5441074802c0d489940e0f106c06136600d0b201004103845a080d94520703c1d0344018140e01c40304042c0c100300103151040d1001ca0041c00703040003c0d41d0160300070044561007a039071200804248400d1117040760b14070030403507140740c50b080c10003c5a05090850741100c8413800d6540e4030900700491309601c4003c1030092582020311594500c04494040d20180c00100c00088d07071018400807150001034010281d0380d051328000b0320101083c60740b815110000b0a000c88003500c4201c0021a5101c2c0c02c84031072005000b20000c40c9003400c42c1411340c41e215060f40003840040580c00030709110840801a1815000304441c0404c0081d040c2c99418641414000c6043d81409180d030005621a04150300400020341074a4204254a9800c00c101003040182e401424043c0204240384402a8120092032040c2c400e21b13005080c15110303480300050f81103400d008100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 809226411 1250 809225161 809225173
    0x201020c1e06090c0d0f0606180203090d03020c0a030810050a030c090501060e0604050f0d1401020a090e060607020d14030f0406022b0516050610031205030f18031209 73
    0x4203110502c80c0640c032129079401007000001c81c4000c206820321a0102500100003240100f04101407030f0040002483c004003140c8a500750b41c4507041c000d501c103448405552040d41d64100324a4007038000d681c048110036018080c0fa400c0c644040d1004280103041c8242d049149074081001d0740da00c1c107041d018501560703411038042d0038005410101c50b8181c00a4061014060145155a889404450558100b46c80b0160b041c1c2603035000c21405481404010061012641c14042d8850158040c3c80b1041041d03880e00c8405a64000d4042c0390032007622090f0300000c08200410250400388803030100c0030b20074840740c50303518a918040da0031034000c3d0300b02c88850600042c04110307081d03040214040c640314039045810307032000009140001c04074620740403050140100729030f620741400e141d6001c2c20a804ca0191440d40c9030810b070491010360030f4041160015294a0084c02c1c403840745003a80e1240101c200d0800d03481c0c07a000000c071040c042d42100700c00140700810035068003000c1207031028013509080c0c0007042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 809227661 1250 809226411 809226463
    0x9020a030605070f1112090607050c0405090c0103060506120c160629030c010801090e0a050307060b091e0f06062104020306070c050615180103030c06150303120b010201020c 76
    0xc14001d111445c3c00d940a810190b01c1300e05000c003161001101180c40342d558407100e28020341018400020b82e079015150204101000101060381c090401e8241d8081201c59140e4040110302d006105090200c00741c090001031805280034001c0c4003e0b034800385038104441460f40c032074050f140000503c0410750350040c54030000000386044510079140807070103060000030200001380380d41c0c0e051103001c480070b071144006c6209460600000e442c0542010559503074a20b01d08140c8060020888120300400300c81c00010580e200001c92440c1806a03a4004160ba840d8007001c550700d80070250025511204c10028030240005100d00c1e00d850700b001b102c20f8806403a2900405080c014010300510502012896081c0028004100c0a9000c0d0b581c29101d41007801c0304012444051b100c3c0381110181030f80c10000310906812000c502046440381c00305000a42078816480000540c1c1d11004010459080c04030b45101c11540200f641080706100041c1003c02132041c42d4034040101201625240040102103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 809228911 1250 809227661 809227667
    0x11090d171611010306050d060f0e070f0e010501020a080d0209030312090a0b010602010213030b18031210080c0a0308090d023622170307260411010309020a030605070f 73
    0x9001c02d809080030411540b5107000310703030001d07500800205074503038601c51251321110780d5002c0462910040112550076456800d81240413095003d1003422b0902d01c1c00015140d8400143c02040e203078801c10340c0b400c0c100d0a0000d84007a40121407101d52502041c8409044251400112441822000c004000d00c3c0c0040c104040b0f58181a0000c2085900401a0407019008a040d0408503075000100d0f40e202c0d80d4400c07098147c004101013a2646000004800160340107100b0a036001d1900301d15141403035a42c81c207070030755940d50b0164000e400844c440f074108049000324018069154001e02407808000703c0345d001a07a0051f54542c61401c2c0c3c00c2c20014018171400c40c0c1e40a644032501002e030750302c003420b01c58151500103641c0d5030000220340c40c03032600c0c804201c84401049444421041c4030303503c1e403c2a62000d0002141d02c0048601d81120000300c4500007006d51801e401140c010000d560401e0940c0c0044010f00b10518044c1e800c50b200350000030024110b032250301d1042059903a02059603c0d00b207001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 809230161 1250 809228911 809228933
    0x40f030c0809061801120c230706090b07090626090c13020d0609180803090a08120f070203030f1801060f09020703090b040303050d0515090f040c0911090d1716 70
    0x104081c41e2914080b80c4847c0d8001200380031600d440c06803079900300c1e01c0e90400e400c244251200286240e007030003108010044440c0307005010f11241c2e00c2d4440400d8903074004580050342e074494a04c040c403502054400443e00b400249410414200603510400b42030130102d4078440303030f607424403080e940d001400c581c41d41050311880300034000006062000701e031400c4400ba0340c01c4a06c074001d40a400e0000c0410704040f410040707840c1060344051300c1600c1c0d040314000707000030090880300d5801212001e400076503000c4c400320440388600d80c10300000c540d5440c3c040410f9070000c803044a0103960b65a42e1404508400c58450741c1e8010002d5603009a07840c000307071800411050456100c0c0041040500081c40065000410b0300c5403120130031070016503070307485031b1a240d140007044100710703008240c07003062100740000300205920079802190f403d00c00319030781c620507021200f80c4a903103000500300b802003c03620b2404848101030b041c020001500300c1020840d81c43c0081d0b10039070160b44803141e5022a0010080c0c03030f40c01303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 809231411 1250 809230161 809230187
    0x13050303070f031407022202070f0803010e28051b0c0c0f0d02131a090a05040b09161406070c080318090115032a020f0c0306040f030c0809061801 64
    0xe0508140495011030405882e0b003004104001d0b010b038211007c00c00950540300060780041201040203114248078596a1080c000d1034185400d070000248011380c00d00481301e400044c0c1c03206454645481c100200144006001941140c200044000c002c0b0140c00c094036182c01401d000d014880383d040f0070031003448082043e007806101c00180711030242e42e4158000c45103500110780425102d0314034804040f1810303000312640d84001c120301031008001c0241c1c0500e11580c40b5225140c9651110080f990f910711410a185940e010300e800184041d0289214405c01d145026203990b05080c6159038034000c50300c1540240074140d0012800c403441903844000c0072a0b000301540d8054440d410001340f030010740418002d070002d05840382c1c4c41c41c0004414110b008078000207400824a106d100740802901c40a2850842d000c0d0312408880503a2454046840e9010b5a8000701d001c4002c12541c4c0d05030fa40c5201034009840400c024408103809440c0d143c01480300d012140c8441203240455000941040b542c000c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 809232661 1250 809231411 809231447
    0xd060510080f09030409330b090105070f02040203150907050c0d030c11060a06091406030a060c0908060c030709080303090d051b250608071413050303070f03 69
    0x20010048540001c0400e8010000786088075032641c8040001c0d00d544201c5d84443c3c1440d24000710041c15410426006440071141490311030300010751030b24200e00400600581201110400c42d203202507000d54010200188506d0b5002c3c030b89843c50700007400301d8208540e080310820264861212600e085507111f030b03110382c150422078101034024031410b540351800f12511042c1a41c81100c0700c003140c0a1002e410141c0218011520b6a2802c420b001c00070301407600c9601001c40c2001122100d513030400c2d05c404c1c0700e01d0001e401000b400b2840d89814001e0030007440000306000e0024000b040c1c1c1c107000c1c001980f1583c80300e000542d0341d00b40114004d140100303652141199400510070f00003c00300108100c0f4078101e46241c16600c81c108c4901c0d00d8040d0416406d43c82051140c1112648041184180304441d46c0702c02c110341902a0ba01c0d242581c101504a510f28000303016903601da91041c0106014151032030340b8400c201e003007030f4a4030040303480c5034001542585d00322104200b18080650003003030740e100c40e61400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 809233911 1250 809232661 809232679
    0x10090b06120a05040f060e161d040210090e090a03080f01030f0f0c0b1602100c23120304230118031d33040b040b09010e0907050d0605 59
    0x4411010300c0c01500300c00b800c6845a0118060007001040701600c01d0304601d040180703811402c58607554014590300f4203070425190380d00191103000b0142c441e501d1070b486030351110a50307126420082040f202900748020310070f00c1c0001203003c40201040c01e20130b00080c002801e140011b400c0142481e0401841500c00351100700050001440c5201c580513840c2e488960307540341040743e25110100c0f210b1500062003101001c81d001d14105401044018514003d45000700701e03407410241142c0a920080d13001e01410210b07204101d0214540301c06100c04000704041e01d05d102c203128117400040e84160303019220280080c40840114484108c0300c802c1c8001400200002418107680159041041ea000f40c18402707039090b2a0100c48008641004440c4011700661500f0706803081c800001f4030540d401d0744210840381303035441d48004841c22901680c0b000b040d00c0c1c1c181450071070904020341c0726a00c03150402458000307210f10354440040c2c1d113026019940340d60b51a41c512028010884503503500507441207440f6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 809235161 1250 809233911 809233927
    0x20c03070f330207030c120e13050405070510051204030e0405060f15070c090e03030117030406020a171903020405040e01050f0f180a1a090a030e01052110090b06 71
    0x102c0b03080c21100d20151030250b15110350781026200c0c080f10000c00760282c051b0503002c0004503440180f2981c03c3c94110340d0140115403144001c2d0481d0b5040380c0040043d0f0000d20144801d1424800d040d420406c40d1030400d14000310302c1c14259107280c0c240c034100c0c00b107144c26101c03d003140ba150065943c451410740341100b000700c0100c0090300100c24115100003202c03000624000703101541d150031001d46000101030003000004502e2594960091044841c00b022041080c000241d021085900f16032007030f4002d00b101d04542c1c80b181c4101841103c89403803400108000c2d414030044442489100300c03103460058840b80782400b400306175803a0340406100d90340744c0001c106c00d044060021035040700340d80d180051156900310360720041d12840e03160154170f8801c0103420030802403050105030500290b851144415120004415aa04440c01c1c00402040c2087c1c0c00c3c2c0065441003010300402078241d0300316002003032540038840c2c6030030060742d442519a255207010300c0b034a4040d006c3c103500310f68140d80c6280f8040300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 809236411 1250 809235161 809235233
    0x2010c02060f10080a0803180303040c051c05060907060f020102042d0b070b070912080d0906060504020a02030c0d2c030c06030705030433020904020c03070f 69
    0x1c020424000042c000012031001d0380d4184900b000340c082203003203070440c007010b040041c800d4100300d43d0303082c0351010081c010003101808401d50b80255070102a4040d018100010000303480760420121030701500d02824040816401c2094501811503070028000f4a41401001094600c54242280a42e13004000401444040003400420090001040008558005803c000a03405940500f1020002092001c244546118024004c07103054980440c200e03900c0d800046140e02844014012000c1030120f60b08040d00c1d0303004110018401c0d40001145911000040c0807a0829a110340044c1d001141e00d00c40003400700040b80d0340f4401400d22041c0d00c10580c040000c00101401c1c40320203403800c00b1030044281c44c200262005c698000304100e0312031801d00401070280d04204c80030345c2c001143c031064250007c507a400380046500d80c8100e426050070610000800ba500502c13441c2c2d0010b5003000360301c413406401c4c030141130640e209141e01c00c1b11100f94102440c031054611b40a1242945044044582243d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 809237661 1250 809236411 809236423
    0x20c0312040b0f07020312033403021606050c090a081504120315030807122102070f0c081f06300c0f0611010908030718090608061602010c02 62
    0xc0202c240c5540300038800d007040c4180103200c0700a41500c1040d08203600900c48401840c42040141e40b480003c0c6e4400c904818080c2c0d264100d42e44030390918a134511000c0c400e40041a80c2071004071a035140b4081e03a0b039010100c1d0341c1295085407000c0b010582d416580b908a5101d0000d000101c01400d6016800103140309400380940010f00c0b01c082c00c41800d16042c000d4000c61460429440040c0c0c01c0d40d640d0030030701c0d05c2d5405148200c90000c88030300c070480c0703031401105844080c4c1d042c200100103685004134060700030f500060342a1082d104041840c0b001410184a01010b064580e01034100240b4498134241070328900ca003816100c50070403006102c4072142110f09450080031414a982d0001d42d00040748850380062000b07011040c803082c000c0781d0703e245045140101e41003030340c6800c090188606003500300c1c2e4240300700030400c0e071080010542d020710504c135680d00801420005041240c0d41e1b250a411110316030300142190304440700700803610603050b000401d0b00c8044d00003440310880c540c000a40b111 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 809238911 1250 809237661 809237669
    0x118050105130308032406120103080c0304080307050a0b1803090103021c021305100203070f0605070504120b040203160503060a050c0c0f031c09020618030c040603060b01020c031204 80
    0x7002154a800c0011001282c200854100c000b82e5500c2c1070520302110040442c146000404c9040e1075101c801e4200340d011201c0e001740c504800504c40e400c6030748048840e0700c800a8520f00f0720003400045503205040c0700030b0200610680040412201d10302e040d140b0001e000b03100702c400548001804400d01d5000c0708450544209207070040c0e98401c030380090089074080080d441101c40c80803030103806019450704460143da40841d0320f041c541c0e5109100300c0e40d905c190030b40100401400400320700003600c183c1003240c2007812030809604203030300c500002100d0a440c060950b21945128280010350034107000900d01c242c0780c1c80030355045a0810700840e50b50000a03008a0340103658400284681c41e000040c0c5e0f00004030f0800361500480741c0440c2d1940c0303412070050789005884281080c6030480c1c1a00c2801d564a034041c1c21181083c03003241507480e06400401a450f00b41c021082e00150aa030b4510800026510070540080e04103220400245400003031300f26503000f603100345040440304103a9401d5800319 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 809240161 1250 809238911 809238917
    0x30a06080d0903080a02010615120e010e0712020f09041b0b0405101b0c06050703020714150a0903080d1b030b01050d0905030c0303012405070807201809010b01180501 73
    0x3441045c0d10403401010107030300c84811121113009030f6401681c44020031500715801d8030300f40400d00d80f07034960b2402c990340e00d2030402780c9610042d01003215a500c0582d200e00c4a0004045040c0b0b0200040410104602168200c1c0c04921301040c0c00c084040410943c00a818a02e443c0c03414103040c90085134917892540d181c2c4060044c22003070010840d02410151442c1e590040280c1815a41d45901030800d80141c00100c025000f59a404078403541c8083d035250070042c0c01800c208081d4400ea02001d21a800304003018204040e10902002180d081e03030040c062105c3c1a0300009041e05011608030403580305000c2c3d07004041c2000040c15040c0ea001d003e40b401d0300742c16403000404051900d0042c0c84e500c9041c001000501000c400040c814440c1c809946180d2031000522142c400301503401c5801c2e00c107410000f000a00280b110702c0100d0f016035030000d91410014a20104081500001418001d141c802c004d0707224208420040c90031005e02034007040031340030300700070328a41c030b000808100c081c0307141c0152410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 809241411 1250 809240161 809240167
    0x20f030405100c020f0a032001020a111005190c150b0a1802070f0809010305100b1e04030624050409020607060b010302161103120c1e01150803030a06080d090308 71
    0x80d90f03284461401102e20050644100c90340e60304d090b0708c4030a040c5407802044c010200070065154000b1656041c83c50303001d814502154014401c008401d010b0700707180001c0060520442c0840003e40d218000021003948401d03103c030823a40b83c54031b8200b03202e005e04000c2c0c904040c60f115180e20b40f0401541a66580c00000d0914601c802e02c10300207004094000d05075840741d90424007801113030b40090480c07003400c6e039042c45245d41703c001c40240200d1074421013250340010040e5074140f8901c0c1a03155100c00143c140585803e940b80c03200006da0b108014450880d81c21a00341c45603828120300140001c01d000d5909101c0000143c0000d5010f000e500c101511461321400900c0303442c0c0c8070741d048a4503215030499012608115081120f1000c1444504900034898021a07403020400178098981d299580c0c8024070a5a00e004821410304804503041e101079034940c0a844009001e0b14815806051542c0081d40c6910788000c4240c00e0303448d154040ba50a40000c5548202e1aa000d103002003a2034120502c1c0359 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 809242661 1250 809241411 809241413
    0x60b04081b012102040e0a0204080618070b0703051801030c0c0303090f0221070b130618050306010b0d180819210504050d0815010e12060a020703020f030405100c 71
    0x2841e0321a5401180f181c2e03141c2403d102d81c1d400300da000d8826035074030181d40900c5079240c151100c100d2007140501c024035800400024424420100c1c50901e568000080d50340301c0d9502d00c0301d1201078010800440201c0d2011a00d980329081c1080090303d1100240ba061081c0750300020094205140281c02800301034440c3c07501c3d000d01c4140198128401d07406040034064001d03442622215000c5078015400b03d0195040003c1e9100c413010944141201044000c05620300d045410750304c000c0858000d960030281804005150303501408064001c2a9550840390390b03101c0c0c01103a004803004039650502c00c9810800d41404140203205481d2100a601e42e0901c64099019060741c1c001c10006044804000542c212200c80c140b903004140120710030011550000d001c0302064030051001c0311902c03c0c014040b1803160f0198890900c1d60640500034042480448040f40c2090418a0445403811345580016040080660400510350016200409141041d084c40c00146800c07801c01420410803c480404c48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 809243911 1250 809242661 809242667
    0x501050c030f04060306292b14070e0108093013051005030f2a040e041b08030f071403121008010218190f0b030901060b04081b01 57
    0x2c115180480000f41c580380e441038018007a00c090301a1601c1c51070b04801c0250407650720400c402200f4440302c0720a04001442000d010344825100c41c4110f100d49015040550048620520b2042c0f0a140c1c4041c0c032902d06410058400706100c408681003210305030400c11004d5011445030006004000302e805064501090415050440d8002c1e02c0400d5001072803060b03c20716189514100c45e010b98159003000c84160099030f580c00204c0340c010801c04100d0000700ca9040002d103c0c0312240c102007440400749408c0f14820410b4115805c0036030b42c613140b10148418440c1071f10015050f04500c0441600303450400071415183d0081500d402e6480c036010546800304a401c241d150300249000702265202d24000d84514400c0c2010f40e0b258a0400e510480443c2294040c021294100d0016542c2841d40b6480c01c00c0c4120440c0c40b00c418030407002024000305400b1301d10301d4454018801c00c20f0031900c9082c41c08089003194829403045404950400c02081950340205440007610016660700d944c0c548480c0040e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 809245161 1250 809243911 809243917
    0x213290303040303080a0e15010f06080604021c050903130f03050f030f07060504020d0b07030f050702070503030906130306110703020f070f0302190e0109060305100603030203040e130c030f02040f0501030206040501050c03 97
    0x490303202e400841c0042009109000c0302b1085401a58441034961901014082244160600b0320b0501125550320071540000d604021342190f15407046a15118a282035600e240300507400c42e042c8800401c4040040c071a00308003060403440c0e50001b9500c1d11419031460800e5224408004140c140c40b500003d0641d42c1c1c5282d0480d1160b040a450b640c14030b40241d00400600441070590407041c504000305140c3c0c0d1000804000355400070380150f24041e003540030007980c1e0704281e040c00a070440c511400310004825004605845502d8800a61078003501c0ca401f0782000f0403001c00b2921540a500108564106606510304890301941d4412140d07200407000100005c160b00304440c089608000003c442140740d00c43c07401c0b40d003c3d4085e1584029020840c03016550f641c44003400592040c04140401d03032188003511381140840100740d1401c80541d980181c0c0c00d00e02e51040e68503000543c524400e5007018000d95030328003c40c1c0e20810156056070b00048960085003e00b0781003003030215621042c442d0800403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 809246411 1250 809245161 809245183
    0x4051f02030f0a030e06070c02030303012318061804050a030f0201181b05060c030a1119110f04021306050c030903150103020315070504050d0213290303040303080a0e 73
    0x202c2c5a42c0e004102c00034010340021040c420241c417a09000034807441c8600e040b030000303903801000346182d80d20786101004114030401100d590b4003200c04403125140d461244001c11000052220a020300d0008104540000302d0301940c08801c0030340f0700b00030000d0004100311845680c58240981e80d003000725000c03401080002d250319205100c0081c040309115a501c80c00011000c0c08810b00300303050300c640510540e405070302004112a40107020103c41e060203a41030304410380085c401c0383c4480054000d4041c0520790204180ca40801a04030034215081c4090b00401422065409510300042203440b400241e42d148a40c03010400d010071400304850050048580d0f40c080101114181c02d16400032000c6038100b0300c822482440b503c44207a82401d03865070014400c25044e152542071070700e80820310000d112510402c030391051a18149034020308d031600c18910881688940c0000b001300381a008c15081d0410894a03129a209000801c006a485800c859100600b00f00100d000502c81d9034451525a040c11 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 809247661 1250 809246411 809246437
    0x30905041409010c0f0909090302191103160e061011030c15060f0307030f02012c0f06031b0706021e070b06010801060807050a142101090204051f0203 66
    0x180d5218124095150709005060500080180c041c580341c00b5544034003030206103004a401248208aa030b00264000354145020780155110280000c0f10704d003041401e910201c0d09118a521000b02609040124045082054080d0a070641c14407120a03142c1c040142800d200b8071450700c2008445208801a414100b814004c40c2d44a110740c403562030b01c0d211150003140303408880000040b174500c1c000440390103074180034010b803080e1030550300c0b1548074417901c940c1a810f025030034691241c0d01c40e4144110714661114440040c3e01c40303450b400c0001d840c40d041403a610540040c803d0201031034117180b21520000c00b0503030141e5110f8151401d40043d0196420764102c0d601d212a1034816a51804010512284500c03120300c1169182001927403107420038050803002458280010f04503138014801003074800c0480c204442c2d002004a14030b11309502402101880c80300882c3c0e001000c0b2400c9d094a07014001309402581041e0418002c12400340082400028103950b0035000075505009000300c07001490820 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 809248911 1250 809247661 809247671
    0x2150a14041d150906090c120f06180103200409080d020403030813110904020607170c0d020316030e1c03092105060f09191406060a080706080403090504 67
    0x801031a4070304a018442c018603400310005041c940d1504002d0b00c034540700901c01c0469807074081c107000454100400400c0c10302c0342041403500902400c103d4521880c0081410f00b11072038402c0c180a032000714a206190410070980051000414900d660100c3d001c0340c2007017202a10802e000140604921140549910f400081c08005a44140c006000341c901175101d5012070340350b81c002c04402588940c409803680945010300c0602d0715091070701c5600b090006002c0390601c0305946840044020100b00c0d4038041c600014905001c44050205441c4060a800510b04090b00c1600194483c00c03074080050401c02c10492940c20f680e210081d8400300c05180740c0c072050b4641940f40150407080540150410880c40400b441c0074048075020bc0550164400e0240031651211085049010303400b0302814454003507800c182601d0082e5000c40040d540c01803012030b0300c0101e59000103007050360140c01903000d0301c28200c040c44100d40004d1a031040315414904003540d43e99900741128001041e400996205080c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 809250161 1250 809248911 809248919
    0x1020616170a020415050c060606090a031a07080c0901021f020403050d02030901032a12021c29010c03080411060301030f0b0c250609080708040e06090402150a1404 72
    0xba40508181c0311110518170348080d41c02d10640302d5004255a0f10b4144d88000c0c0020910700307001c400741c00e100300040c101900c0c2e241c4076960a0406804001070303154102842c410050301d5903001c44441d0700840100303c181c0c035001c0c0040000b500c9200300607200404601c0113000d100440229812a00115004800d4804003186100001c0d1603500c00e09035580000d0410451a4540590b50900071034600448d8250421804070301050782d0302e2299025080089500303006401500d84884001002e1030790082000410304411b1081002034615540303400796940741041d4105082c1d0304404450030190b054141441c032641c0d40d00c0c1c080c1003030381080540c0b502700c0c070007000000c20018480407400c191403040c4a946c005a0340c900d090703d481d0040700001c0c180c1c2c2d8000203140140110012072f980c0d506008240c0132404240a480311155507001e0801258480702c00541040600d1061007034580080c0d0407642a29607082680020342400c4596026100440001414000c108d010703143d00c00c40410588206901c45940f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 809251411 1250 809250161 809250181
    0xa0327020111281101091508070c080408070f21200a0b0c0f01050609061903050615030610080318010c0506041203150b0a14120f010302100309020102061617 69
    0x3d42c034200c1d14540f903124070400f40d42c002c071190300076500329014811901d03030842c004a4118401629031000c2c080401001c2c03010800d160010005860600000d007001450059200c0d000012640040709620070a0502d4451050716040d00c40e5064001040401e0000a071580112540240e900150300010805002031464005005403600c1c030407840540d98603000f070b4003c0d03900b070300d108450b01a40f0809000000c0c0491410026000803500c154007040c000c9a102c8e51501d00c0c08100343c0da407440c080c03164401d05440c0d2600300110303580011020764070004d01e0710701180d8503901c0c011070146202868800e0030192a80c0d205515031210b081d040f41c1115202e00b410306140070f00301d44d90140200080d061015080301c0c483c0d64840392007103075080340e0700d60f16100010404940401d45c002c00007401d60b504001d0000140000d040a901450646000b11701651540c0304108542440210820500d0b050815a802603038010540703070f0b0f0009007168000309c84c0000300000c840c0c01e100a12003c00300a0048140280011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 809252661 1250 809251411 809251483
    0x1090e07081806040321020f0d0203010f0f030b06130225020f030a0c05040e010b0a23010f08040f081605010501090e06040b0a1a0a06050a0327020111 66
    0x10b0340d18101c2c0414802803001c80d183c0c581150064003083e12170140b201c0402180b640c0074441019200c005040c50204001c00718141e200303900000c181c640100052110360000d940c0480140000d80700390391110b02d16529613042d598001c0c06541b00c2c06403000352001001c040d4040303c0301c04500d400b0f024100d211964900448108951041c0d000d40203150303211184e41400526212031a030403500c411321480c604410000a040e0309072010f010f554a8130680c12541d00d401324642c028240c003484035690100442c001a090404a10015040005101d900041645c12145081d0001d41141e80f400b00c105060500052500c66541803001440c0d802280d4018444190300090580f80d8000042c855003000300340c61a076032041a2400f03446029a80081400c4c1a4558008110042c0d00e450060300c10400ac4001501c00540d0790085000c20300021f91108016414401c003008811117404d10030007899450b950b446200c1d03000c58028140419019001c1c9100400c01610803880040d40c0f2000740004100509031040c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 809253911 1250 809252661 809252671
    0x19020307032711042c0c030a0b0a1b080402040209030f0601090e0705060c0c13060509100303030b190614090a030507050909010b030d03050c091905100201021c02070201090e0708 78
    0x503441ea100900da901e010300440c5517802110002c005000d15850b0f1002886146110081c0703d03100c1c915120f00300c3d80b0180400071a25018420074a12032404140c201c09a650001140020315942480c9694450f04103103440d80013601941e0041c0c64860940c0420316051911086d00c5480c455040000350359403803078020840500b00b030030590319590b82d41c00c10b0200f203000b41c848040c103035013080c90962841e042905c3d41c10302c0f400000001003881c540c6d90b00403510b03072802910105251200d03900b040c000d150b054041c0d5544108252031341c43e5039015200008402026038040c00c4100070240e80c2c28610b003144601030360280c6000828450780d466582c60321603512071151042c035000340c19150003d01100c50612070b2001c1040058040c1c60101c0b0700110480c01848010080d250b0321009104801040d03c0c0c0d898a505002120300c0c402c10454144030401041c0c4501c4451441160f004000c528184401070f5014900c0640005000d40c46590700c0c40180c0f80d2805503001241c0800b15002003000b00740c3c0c0600118010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 809255161 1250 809253911 809253923
    0x206011206092f010e0603011403030d0c020303150111060610050903030f04091b080423100b010206010f12080a09080a060b09070804020303072003010c02010e0d020105190203070327 80
    0xc8204100645d00c1c0c031048819240d01c038400b40010803a00d0b00104089981c1a0020107070791600040844a02c2155400c00c2e40100690020040108a14003400c025180c1602400c0030902c80302c42410440d520100100154081c2d0007284040c21041e004100ba58501c0c140201900c0d15161007240d0160a90014868080c402e400d20800031440101c100d00c1040a11065071400b0b40e0395a030752a002ca850b0842c0100a2040110040c1c0d008a072805000c0402c82120059001c41c5580d4020002890f003407041e004909a00d03440001000020681091000310650040c060740d1201d504200680c3c0c50040341e03101071101d00500c01800c00308030659218041c403143c2203400c002291200241114035640444001790194000c10030304000c07901c41100205e0303102e00700d003441d5010740703010307000c02d0039119904c00c80d0015030745401060803070b01020702c030174503426000388001c00c00e6140c182c14058108986c1104048e45a41c0000462080703803083d009400000c61180200c40940c00d01c5c402c860005040c0304007a620 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 809256411 1250 809255161 809255243
    0x2718040b18071a0906040603020702150c0a29041211070302180406111603080105030a080702100212040b04090e0708060601030209011b0807021906020601120609 71
    0x406902004441589034200006202c41401c0001d8800304038243d40390485464018048041c4640d01d00d402840a0406e9036000350702d501c41841404084208000c8004800c0c0d8203110480311100d0018109a1582c0c009100d590000040300741480300951b55440b0030050509901008280990801c1d90480d000c1203070384401c10b119091ba269a1250003c0c08006d51001c0301240300c00440018540482d005401060001600403003405c80d821198010545a0403000d0600228002d240d002500c1070300400e0160080c00528007aa0380c0c852884c4a11000280300d040300d1018400880c1c400c102c10500000d00601060380d0b20340b01c42c910101900720344103101c1b240741088a4010541d6010407020100c031407420003002a51220401540603411219105040005115103122000d00e01c11500c40b60740d000d05401c039544c500c0750040c001c585182c40c03000180320036843e074108281075000030341504442034500341000240c0340349804005011408005011001c0300e070000555003902c030300e2400307060840700c42d1048 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 809257661 1250 809256411 809256421
    0x40f170d08010b191205090c030c06070f020405090a050a0f0b060102370501060f03030305070c050604021c081b07090614120f060c04292718040b 64
    0x16410002d0003801c1440805000ca1050a2251250f084d00841c0a007460a5040c03000400702044a03000c50310901c0c15030042c02c10180c03a00b0300b400a030864507010355005280010f1620782415101d41da64000340159642d40000e6042c2109020f110200b0364030005541510328607061071000f010721620151100701d10000450340c60340c000604480c101d516042035a10100021000365295403180041020310100c583e24840060780a02c03900b030140c4007144035602e5180c11400c0c01002c4460091026080c060b0900030704020035800604c0ca5803103030381207500c80d402d00040c820700f00302d6407000b08004080100c0468000c8000c8180d01480e0791420844048a0700c1c190740354100c400b0b99440d03118078480500480c51340f28050070a0110ba080c032501041c03ca030308400985401a29081c5d040b40d103840b186002003010302c62241180a001c90b070b000b440d00b0075400ca8076070480e414100d10940014a00700707504140e031107851443c02c00ca0002e075401e005011000000620185c4c00350300c84126002c07900d000103580098 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 809258911 1250 809257661 809257667
    0x122909011103010302033d0f050105030313171204080606180709051e100810050d080301090b010e040203090709110c0c13090602190e0a050603060d08040f170d 70
    0x3070f04880d00100208000f5a075560404403201c500c012419080507001e44c0300b400c81c020025840700d05105074400142100c6440c0784541240d43c180c0055200e030300108842840302001d0031004003510456846600c60500e100604d524000d041d140e550301e1100c01203000600b900340071407620320500e4240c030703140c40071030b00c00d00c0c10806070104a41c1c60700400c09008090000d0b047c11310103600308003a454403c60084011000141c1c0140c0f0081040000400036004c001504d000d01e0b080d03100814007a2402d2030f40116642c0d0b1017003640014010110443d6894940c084030303038420790f4111903040d0054011075890a002d800544c48040a0080c004c2c241c0c00e1408440c0040080401c55a0740c944084c003900b0902461800c1003000f450002e410702c841600c0d400450007058141c4001d18407403640b004289250a1030031409000031013111000c91244c03007881410022a100c0f0001caaa016004440c0107410a109240c4140c1034040c2e5040098440e6815401140283c030f8440f038098285e00d41c00071241c1c103e1001e8421 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 809260161 1250 809258911 809258917
    0x10c030507090b16020613030317040209040602030603010b0a18060f1d09281a1e0a11130614040605191b05100608030408071229090111 60
    0x10002c0d60105081040314081009048024113414104d915180c0e03580000b6010380259541c400202c0005000f0010142c00800c020f0a074421a0000c030000d00e4107400040040350b0061000d00842d40002c0054219542944070040c6d4610040c450b0300d84c1c1e0f03214184844d03004414840f0100d468a040004941043c101e041401144c1c044040f20301510500c04401080d624050411340c101e204401c00c00080440c200e401a00d00c1c0400c0d45000312101c16130601d400c40113501c0030a840160040c2d402c0c0211a80d40b003020100c0f46105010b05204c40c0c951220380340c0141104401c40d101140b011401c0300c000200f04000408641e02c0b07981e09040c100000303051002e64410ad204a0000c030304104041c1c0352041e9400303030211003811031b0700701030f1007880c0328109411084400c010110707141c1c0c01c41e500426010f85e40f881840068124100214185030a0002c1a83e454625008070030b00d5514030007075102002201c803541c1140d00c0c010412081210b80c0510807040c01c80b415103107d00c1c1942006016401d8254440c26 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 809261411 1250 809260161 809260171
    0xe0319021e030708090402040e1914040b06010f11010e0c0f0102010c0804030309110d06020901030f0b0f0d02030a140601033008090106260106120b0f091006060c0203010c0305 77
    0x514030f01021a504c8080039030003a604107030000d03028440024003104054030750384242c0e12403850075a034500c9221403504450550340b0303403580d056444041c403001c511700c01c400e035074821000e08000000c0081c0c242c0985040145055802a40d802c0250b035000100f400300b40b0401b403500640b0f8000056a12400580c2680e04810315070000800410000300440c1c403903089280a1402068038000c425000030114040c22111541540e00d150002090030095a06125150a03858056020000c1079110300000d0320500e402c00b100d40c42821108103290642da000e110050600354050044100064000c00c0241c565000340300559040408030201003840007030007001c00d0303d00e40c060b00c070b13000443da026000d035050907010f0030150080d0342e45e85d00481c07190a901d102c1c0f000f90003800511216200c882c140942903419a401c00d2841c2c841600c4284002041d0f0a115074020903081b218338010758922800ca881c0800c040b090252a03418200c0015250342c000c020040094000d0b0000d0001c03d40344002642070b00c2041d10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 809262661 1250 809261411 809261413
    0x1606020a0305160c23120709020f250b0109020703080703022203050c120c0f040e0a0c140a090c0e0f0402130b0c0d0c11010804060e0319021e 62
    0x2803031000034800d00080282d02009807281e06405680d032203a448910702c90b04031401503881d205211844482142a43c0741907001140c40b03412541003811001d8880440344034130780c00d140c3c0100c0c3e0b280702c85940134199580d4100224103070b186510351004602c0b200c4110342c415605045040004900c1c9a0140203c81000f600f540b00c903103540e212224114002d500c80d50310443d9803a00c1c04c4d42564018102c5030004011405000100900a0440c00f00100c07940706100c1e21203682d10183c9080f0140c0c690b4003000880701800c41e4001610b07040500a6400c02444c000010191980740300041112001c9001e140c1000c8820f540303100c030741519250080c0032071b80201891000306800d00c8080b103280c9000203240211400c082c1003d41491400321400303001c4d10058000c00c1d03005c3c0c0d0103d20007608000030802880088424030308030300140710b182c682c5404061140b050301e04100400000600f48036003030700450301001413031045a03078900b040950070385c002070103014200050040806a0380000340300e10000e45400f40e00c030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 809263911 1250 809262661 809262673
    0x40b040e1b0117160915030e0607050a21020910030e0d050c150703110d2915030907120308040201180f261609060e0717040201090506130503160602 65
    0x11900c0300c13140920070059001c0000355100031580e880440302c40100c4000c55140407450001080e9083d0400b44024a40c004100045c0000725071a80e000c17400780840562440d00503048a403031091070000c0c2c0b04207880650083c40d0b10003030440700e0381d06a000100003c500429a0040c01ca41441101e0b540304124101311640c0c04004c104800b215001c0c90550000180d090000388a00407482200c034941011841d00c04c1d0640d07501008800c180e071241281103e4404d072101c0702c0f202501d400080c000c40c0001c40100b03c403200200c0040c071a0139007048284042c01c4aa01e070b440a841292400901c40030301118200e00160551000e1041c3ca0a0303130020005803084440000305490610041e0b280d4040c400c02c90707052007030300e44001c0008a0750a00102030341440d03d00b002c49100d8108520801581e040f0303130000160604040400c0307002a030298802c6c940e46040c42c03e800c03c9454900048541d07250070b40060b90b200c000000c250704091009210030045881c01e5050701c0b03004150840a919400e000e100d2000982c1044c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 809265161 1250 809263911 809263921
    0x708070e0c0909130b0703090221060c0d0e1903030e070312030e03070605010609060f020c01140c03071a1005030109080a0f0207182720040b040e1b0117 67
    0x42850b0a600032011803501c403442c50a0784407076841d440c2c19a62880408d94480c40034007507040c00d07100141c000502040140c0300408542e8000d40c0c5003802000094000d030003103010002d0807400d4000170381840c00c000845582c51041350701812820a6400e046021074275001c8200340303e01c00490048100c7c0d40184107200007100902c2c0680c060035a88820344854001044a4030010302d00b0300c51240a054295200380259003072000c0070f84040d02d1a1800e50956210307511214003a83e100454650921419242c5a107441c8174480051450064007001411340c241c841028400c2c44400503a03902c01c0b040380b1400b1840d50f80d01c03c181402c8500c103110181c4800e00c20055442c10b10701490307050014401910454401c269142021410080b6007401810825200c66142d14500f11611a10255190f10300c03034000b81080b1551a0080f00b1055101c000843e80315403107260070790352968003a448030700c405042401040100701c50344d500c41c1064000800304040007030542703880b544140b540548903002540d45c050b180d118 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 809266411 1250 809265161 809265169
    0x215011e080109020114130b0403080706052202010f11010c03090302010f0903020303040f020a1a03090715050306011229030d0f080a020c1f09120f022a060703020708070e0c09 77
    0x242400071140888030b01f00081c05075040d40280000c6000711542d035103034031701031400c0c4054841c0909101030200c00c074201242201d03601c02400440e9507090804a0b07003850701d039000703031212810a20b198016500c0c003000c1d0303120f45405402a4031000e2184d4001c01c8044142450141201d09052010700141c1c424400500001c50007200098a24001000709080c4c40e99041e0102c0100f00b00c130b180c041090400b1080c030032070001c1001490b026140244034607100f0401090020194000140814104145580e5405807450740e640500c400d030407004000046e05e420782c2c2e0502d113560301c1800c19501900c100ca00f0782400724415980c900c241d80e102d60b1100e0250711804d0912019400810048078030f07028040745003d0760048211845800c641d00c000101b40c0c15212700b0248650741003002c03004180a620003210075190350200303d40003003012407420000b2600d50703508440000c0b04940f91160708608000b031590103150300050700744100c6100300201c441340d5407111354941e908002940d0a100241d41442074040382c0c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 809267661 1250 809266411 809266417
    0x80108070621091209050f06030f2505120a02040b031b0c0d0804020f040504080f0a1e030e0d09061d0102100501030c050a080613030305070215011e080109020114 71
    0x78070302d00c0040c2014454208042100da81060440d20f0782c20301c0b0301d80048190060091130040008550103141307100c07800042a0f4600c0001d000d00600c20b020800241d81981aa80e241d089403c624000360032100750703550240465001c6140307e03001003840000a080d100d40c50089505940c01224842c3c107544541d0b942880c14401c040d10307105286824840f42c1240d080400c003d01031280142e541e00018202801445240c42c400e07801d060243d0308040c20000852001412205000700a5034456581c1010301c0c0111100702001c192080300c40e4005100f0014182d1640002450f411a04140c414071b4100322001d568140031071052802180d110702c2d420101846040030003c1d00501801550424a048031501003111000d0700b00304d4500f101000148030a003010082c04010b41181070052100307080001c00d83c2c00300c0b480103a000b41015240c40005428510a000c28460600340707070010b01c02540c641c01d0340c5a165a50000d070005140a12100040402d4140200e4003156010384881d03041c080f014182c0102ea034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 809268911 1250 809267661 809267687
    0x6030603070e1e16030c03020c0c0f0d0510090c120506191131030b0f09010905060c07020f0105210606091819090209130f0c090e0d0801080706 63
    0x52200160306001042e4040c640c0d2040380b44040444030b941c13440102400322a443d50381102014414000414582400216969500c0307089030522048211038001a1180b68800d400615030301a0a02e0034a540d001c0b60410100325206110302c80c011a1a10107081da100b151440240c51030f404403021a241e09a400d800d43c0c4006020800403400c1001c00094040a62080725032440c1c1030054500c1120124141820074501e841c0d007080c508185165848000582d400a03012004000b003110110780020f030254000c2a44039800303010307520b1518100817060141c0e0040bd01c1a40102c01c00c000b10f150941c415012102007070030070721001c02c0948520540e001880320080003941c210f43c04001403262a904c026841107442c0c00c4502a0120307151088420840c10307414485018418100045c142c011b03614400e8083e442000800709040b103042c40d0900e44000c400e5000060580014914081055080c030b0708501c45078100340c400c50341107104d0000300311a116001d21600d0382c2c4d0303046000c007809800c2c890401e540e02c403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 809270161 1250 809268911 809268931
    0x6030c0a060c110904030806040608060105130e071e180c08180a0b0c1b0c06251a0412020a080a030e0f0d0f080a110d1107150b0f06030603070e 63
    0x7003040004554074140030b46046d4085410b074001c03c52146000e002e05000750201030054042c552610300440c42c806201d0100300101921615200d15000c1d042121400800094604140384080d541400d0981c0ca05802038541a184001d10700da42043c4c0303401400d106204d83c3d660700300f5a541d01000d02c018508054100103103070292003203045c00306000d1180d0501511010306015030f0f80d18000303078054110711055000394042c2c202914550792a44c940c81615082c10600b008a02422400100e401041a02600c01054140d0320518008080038198005101d07500c0b55461892000005030f0aa80d90b004025006240e900c0805c0010520b91007a00038006140b004400c8038a0307803039180b00880c10040760303118140c00a00640d0302402c840750300145894105c41c2c9408108101d80d0003404040140c85025030220325241c40d40e143d1031100001d041100c038082d030441030f40341c201d802e411a5039002c2d0403005003407881800310f000c00860310b18041d0708503405070800400a1402c14506941011803920003850f9070b00c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 809271411 1250 809270161 809270183
    0x807050109050f030a17040506010522091109071b020f010509030318040506091306051b07030e04110c0316030c0206030f01051302030108030a030b0402040503070e01090506030c0a060c 81
    0x1c2d01040b00480000546000d135846141c1d41d0001003d0b0758100211040d04011042804041100030a0041c10b44e6800d49044064504104200084804649403090003900d40b4012900340008507a07075086250040341c03803001507110480704450019501d82c040c0400c0c0e214004501c018600500c200c40090410304107541000b010400007400c40c3c120322100086048845210005c1d032070241305250b404441158514040e08088405000005180000401c10740ea500c5c081141e46440c034825840d51107014040320ba9442d46c501d4001c04c0c01c6480c0900d01e0242c1c0c201030821410600201c20b0b1203001da2094021801c00001301e10207a207a149101c0e042d014003103003a0b811800341e103c2200031032180080c07501c15036865140c4000e10424806441000a40c1c81c4180014048500040202e07200d9826910300841c8003008400018020700c1194040340d0302d84110240090a20114101d95049400c0300d403007000140d1f215418152190254100998402400c940c01c1c00924024844204514040c0b40c4041c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 809272661 1250 809271411 809271413
    0xa142808030d0204030b010f0b070605090c06030c0c06160c0b060d0614250518120609010b0f03070e0606030c04080106060801030b100623130f0f0614070807050109 72
    0x205542c0030740700300015160000303018000e004400034071900420000c0d10000b4100d207400354155803409240c10041605440c1c40125004101c00c005440e0742c0500240480c2d0b0f00d08121403062580e50018102461394060140000d40c9580640c1d0111a41c80c0e42c3d0300c2d2410b2411841c1c2d070310401020010004c9601184240c0020007107030880c400c601000c110a40711200c81e0804c45150a0107655480101200349422800900880d070300101b5500d82c69508103ca0780031406c010000340d6043d44107603952000c3e2003140708002030204150840296039a003a00d4021746240c1d40b005140d219001e41c021034200c1304a1030045403443c14810011940a0700c1c03103003001e00303180d140c4c076400b0f09540c7c0e903030300c148005a031600050090090030500e01d0b400c0380344889242d034002e02c1d00c1806040e0500049007840c8403000d05606103644010b1a00301c54980c45545400018282c9412183c00f502d9400e001d0b03580d48200341440401c20342c1c0181390351030056040641e42400c0102d01e5035070410f154040081107803595280c0d40210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 809273911 1250 809272661 809272663
    0x309080102040b1e0a14030402040b031f0605060301030803040305161406040b0a1803140d06090614030d17130b07080103030e0a0326040e01030b060a142808 69
    0x4030151000c12441a556908130130b44004540b00840840300301c60082000b41d41107034200d041c60042402450b6195142e035078600006006144054101c0e0705405800420b500c02c500484401c2d1004038008020010030b42c80d0001d0180324003003404014038080c030800c042008640500003038201c0110309103185800281658404e03101c050400625005031b4042028441040b00c0c030200c4a07409114043c0412240e4119005003000c1004001c0150a010061546c3c580b1480c440040780c100d070051040910210356101d10103002081e03148502300501103101d00000e4245004030780c43c005800b0a940d01817852070240f081044890003d4094110440b0503400740c0c0c001800303014024070901c01d41d1141d10b103030740c07440c01d000d8012403000b05001d208100c90700c020300004094100c102c0b040c0305c113040364104020b8036500080340c40c415600000f07160264040000108120345100a00c20341c0c0039030f01c0e07025050b602c66040d60020410b2044070b9100d01d0504140540d40b040048020105400d401550003196845200b9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 809275161 1250 809273911 809273917
    0x1005060a030c0e01060306052d060d110c0c0102010e100b0d0f0311010c03060b041214070f14030c090411041e0902041a06030601050d090203060f04061a01090b070309080102 76
    0x10008003d604001001445c1d00351003010001c20b01a80c1d01980842c0c01800c202c40b0401980900ca248283c01a0101c40c6441c0c4100f0b50320360444460041202400300c0b60180b500d60030100039003c0c2032080b04006c075650352040c003400900c0c5030302d40d005009191980710100090400d01e40d40d2078005001c0c0c00402e001c00d80e41d59044003030600a450b0078040140e02103405094424002100b01854103015007040b1005450b400c84044a0680c0e00607001740d41f140c134201469161030b03801100d0501c070300d41000c600080c805041c00e0465650044082e100c50300c00c4d0a040d1a44000d091a55200310100c0008000c500034519540406a0040000604049a10200e0012085044100c00302d943d642c442c0421406e041c4641e40002011000e40d60110641100058240c80b004026504205000c11101c5a00400b504030038007c690007801c1d5800c1d4501034810000b100c1d8201e8040e110309041500b00d0207060281044040d001d28123a5603140c2041c100f10111040354003081b001c90400541c0c11780000c007078200b8405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 809276411 1250 809275161 809275169
    0x62a060203040605040b0f0907210623070905030d080a0e0a05010506100c0506010510140703020303271c0504091e0c090b0a032003041505010b0702031005060a030c 72
    0x70000f581c0c00c140c1003040d880000100b081c1e039103001c0c910500040c004005102c81c0ac40e10142100b50010003100d10700301c00c21000280080a0a08203504008070101100403003410480d65901e46119079520102203400041a02c501d07905030b00007180b071400861203010000d0340030f60340705400314090450072145d0303182c054a4142a58140d6541d400c0c0304480c0381c6003518a81012017071400d589120070b141c070f4036601d40d0410701c0781c00c1c864580e40a00c50b400314080c00b00307011600002a015071b141c0c00c843c02c010352a07500846580800b191080f881002c0c44d0010a009a0300080c0040101060590050902d01e0a143c00c24041e05114003480000b6021081d40500c0300c13540300c0c05018a80071204c0c10710260640c0c0d00c0c0701d110001d2103800e80c400d00074282c110050b6000400e03540350102d045140035004101d00d001c862000700c01900000104020301400364044403080300602010040c41c0c0c0d0700c10402846001c0c1c100002d5050b080440b000c48100000d4009a030400c174003c100040e02c81e80c03940d90030402d8481e80c1c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 809277661 1250 809276411 809276423
    0x1030603150b040b040b060412240b09180a2409060e0c040b010f0c02010525030e0604080706260f070305070206060a0608041104150f0f062a06020304 66
    0x5000d4209050602a01560a03130a603410310004004000144c801d000e18003074804030140100c0b1903024403060b8060955580d8034034880165400c40704030243c015003045000381e402044003001113483c1400b5185a60b10f80c03144007001e04400042d035510300b0b040fa04290750094a81040521184800009100d0200070610403c000641c2c024a1070482c0c0c103040703010030b8072407207070b881c0040314500390741c00548612080e0160b01d010900f444031031005943c180a00002104403a0091041d5051101c8411200840c54000c3e02c0b03000c803901c41071007000100c0c426800741c0d003801e030005001004064040e440c0d0200f401c04141e02c800d00c2c0c0f0880380c44107405030011614894000c6401c410302a481d81c1610038190425403d101520300351800c4030128840442e644140300401614000150600a8504010744a00c03001081072040d01070503003030303c0c25400c4c150041d4054206113000000700900112100000c44540d0341b91420800e0f2180741440130328030460a04070592120b214010b0000d0190302c0207602c0313244140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 809278911 1250 809277661 809277671
    0x120c0e1b0f09090f061c140304031208100b1803151e09070609170c3006100603021b03040f09110c0a1203060308040906080f0d050a0e0103060315 64
    0x30401044070710280c1181341e20f43d1442c06001407a140d403a2103a5616010204d0a8240c00d0203180400c030014500c41c200c0242d01000c00c02204001610781c41082517452513440d1802c43e21203020b000350079640ca100e400c85010040051003002031045420441c1010010b050715400801009001da400030110360f094102c1640d00e1032034501343c0301c0241258022190324000d00000d800c090014007020380344c0c0030314002584450112103c5070030410a03011800000761054100115041c1a8000c854003401d01552900303020441c4280040700007000351280710041d03c810042d526111090f030081d840740c1a2181e07880c850640825030000100000e1000700045005142c0d0b4515004682d8201ca20103281c40805020400240d41651000565030111a4100d201ca280728444102d007074004000541c401484500d010030001801b40076948204100c400540c169410603008000c51074642c084107880c072011800610042c0c1c04c1d5407041c60302850070307181070500080454aa0700c0e5445034072081010036000b69100c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 809280161 1250 809278911 809278927
    0x509060d0c0920070f03030f020f18030c01020a02090c220816060804051b030106090c05130905070203070305030a0f020706150603020f2d0705070f120c0e1b0f 70
    0x21218080f58030050305100c90401565951328181070400e440050101a00c07414460b00d0007043e60b04417841c00030040380c00c1e580e030b05805218200100100c0c1e01c1b10303c28000c00001d8500380d40046001a1010b600030310b108450b940c2c14404509039004a80120512450381d04004241c0c00e01d0240707400034265000c01410386910005240c0c20030342440e00f100d03081105500900001407000506001600140aa160102a07081c000700340103003150303846284410305082540403041e421400a00002c81203000020000d40c0f100c01c01010341b84152000c5c001a4410860303003000c03d2080340556085502c090010540c400c00104410603600301640507145580d0312124040c50340c00040b41c500040056050644c14810b000c1002441800b40e041c8c1d1150350044510060021964005880c4015441c5031010340c49a0803401c0080d030b41c01c400d00481d140700003a03400c0801c1e40d00204c1801c1c5450359010002d0740c000c60500d003005804180182070b4500706500400d0524500260070040d02d040481c0b8807806441700e0078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 809281411 1250 809280161 809280191
    0x3050414031201171204181e090b0a0e0d0f050c0a032c150703020102070b0406060512070e0610030e0d0807030c080415020c100f0207060507180509060d0c09 69
    0xc03150711940592100c2d0001185178001400c1e00c2c101c07001b03019401980714090b140c0340040c0240720720000580d0b807411040348811701c6507031062240724000c030303030090090f50780701e00050403182c01107000d2031558040400e03043d04034402c0c1034502c448106450003a04010600041515100045404401060303c02c8596480381e0316040d101d00b400118165024400203820000c60440202e5030b2000241c010000340780001e0600075011126031541c001503500c080d29090030000000d1015000c0c03244140c09040c1c3c0c03014601c80004a41d0251409101031000340e4490704c0800080240001d4100c2c14543c0300c402c141c0207040180002502e03108140c50f494428a0030102c020100d580204418040c800100d0501c0b0215480040c10004407031284401a03485003840605032910540842c40c2040e00d0810f121030040740d1183e0081c00c8818440c038428400342d1140c440640340c141d00030051040034861100104060f24000310350542140c4041d1400700a011280c95840001c0c0030381d0800c070001074a0320350041c8050f00e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 809282661 1250 809281411 809281439
    0x501030b060712180e090f07080303040302031602131a01030b190510030204080607050a0305010e150d11040207050f07080a050d0503100f1401020d0302031603050414031201 76
    0x44200ea40601e09280c82e940c0141015451200c1c0b0b08000c0c1030341010080c07401060104000e02817241400c00070b41380c11030320382c0d0365048102d1400d205030283c0b900015080000106990159030b040e0080c3d418001e0031400344808144949099900449a07020714883d80c00521802c20304000b5003903034841c114002e0002405840c1200d0700702c1d0181c44003001848583c1050700007401030302c008440481440e4a841e500710060700031504080704a000e41000c0c404c213aa0090014410035035a620248001d80e030b80d004030300c00a0300c100c2da40c444003c5104016205c61a200d080100740300e00c980c846001e20714003107020070100c0c0c0040c02d01315440c0c0c1c403100d10b4640180d4200500402051040000c22040e8401c1d5102600da1880f05c0105c030070700001101244003100108520405010f002d60304000707070b640e1580c0760101860301e450101c1c00f41c081c45020001d514860b00817244074000302200650340310b40100b8214000c01e0300420550302314603801e81d001d031418000c0c4003c014281a0603a8a0031a50501448018981d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 809283911 1250 809282661 809282681
    0x3051e1b030718050f060a06020307060504150e030403050f0c01050921010513023f070305060c03040b0a060b0a05090420030106090803070203072607031b06090e0c0703110d0306050103 81
    0x307038400c1f08015403580042184c230340c40d6005d24085100c0e110f03482c040b400c4010801c0120469824406880c2101800001501c100ca01a1046a0340d140c2074841094a86032164a16070000d88100038450503814204040e540f1808100038001c0520040806a400c686090717900071111030b0584401002c1d0700d070044020f41041e50740301124904540072484c03828072000002202021b0444011000e00c440d5041c0045401190000c0030780310300c0d2402c450580032640c0219400c542c02d03001c0c0c7e4003041419109100350350039500c49584840c078020304460266036076040341d1107440d8002c0c0c85010500c2d100481c1c140450699120443d429281c0d4107001c005031020040303420410250303000340411005a900042d00500700c6000c005d08545014480442001d141d50b2003003481031501c2128000070400808034115680c3c041115034441242d40c4079070040700c120b80c5600c01d80240b411310740049480c4050703070300003050070910071f0800340e08400035048503605041c81c41ca01c10307004c41c2e6655801c000303651305400f400c0403c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 809285161 1250 809283911 809283919
    0x101b020705040605091515160b0a051006080912040b04030303110720040609020a08010501180303080c0a030b0d050705360405010b03030705010603051e1b030718050f06 74
    0x314280f50105051030b170002c4c940b4418900403009800f241d1a80d0202008121569400607540d0b1450a45052030038400c003002c84004010030006103e0722070510541d0f0007900c0130900100500d15010040700d411a000c0c007480128052200c03601c800c0d40c81d20700200b00800031480300301c4d240c80c99814007070304071204012400d0007403804018040006800c986e0200c151581c6c0c1a024104c034040038045001027105070000d030307015480001d05140c01d50704562001e040316000d9a428800c828000b00156141c99544802808108610085061104454003400b13401031585400079400182c032000031029150302c007042c3c0b4280c220401c10f1040e810800e03103050901c009a40c00001c00d000900b00140e010403072841d079900860f000d90101e41084000e401ca00545c2500030110387e290748150034003600926032444106da0b140309070b860400c03c3c140003080d14003c0f102c00802031b00c041c42030205c101d90140100c0c24019454083d40b44081100d40f00c00d03191248150032001c0000e8640b41150342e4a00c07a100140c403140c0320f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 809286411 1250 809285161 809285171
    0x1201020901080109090812010303030b041b1b0f021903150203041104020a0e04051018112704061508060406272306010f0503040b041103101b02070504 66
    0x1203903000103002d411510b80701000124201d15042c00e9600340520b00d003909140000400000034140c0c160801e415001d011a030070000c0121341b0000361003042c1600e144402040181c2c81c07907058400503042007529240151400c0c000ba0344560f0029084c101718003507101d10055207040520030700504105c8550184102c3d40c0c02c42c84c6040c00c0d129429000c606c40d4645101d6500005c111080034403440e4018800c0002400a20950a040c0c44446003005c003406035040c0080910418a80265140601c0c015000d02c029401c3c500001c852280e03448070020900d0a4005d604844952102d840c1c034030039a0020310340c040380d4a030b00c0c1000c55402412620082c121700c0c802c80c02c082050140030301034200003003591100c1350202109a002c013422806051400c1c0f91400b00541b8a450a04507400003031558440d003400d0382c498014880307440c4191040e000645000c1c0000c554000002c0016148005c4289400401400c5550b4201341000d00016141d41000503160712008080c0109225010844a00900401c03901841 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 809287661 1250 809286411 809286427
    0x7080307110a0510240306060635040c0b030c03010905070e03060c1303140d23120c0c011a0906040c140d0b09010605120a05060904110f1806120102 65
    0xb56455004e0745560340165560032000000308040c552030f08020440c08402c00303c40d41d90070881c0092132140700b514045410200294041c203401100e01c0b1044540101610200594203454603000c600103000b280c0154500c20301042c10350f5000040c600c11010401400c2e40c0f5810204c1c2d0506442015042e002030240807140e030020f903034000c601580e010003048545500c407a148001158040308544c4040c03c549041c5a010b00045004213510801048030746989140c41001d600401001c0d5406048a0104400f40300c180c42c50240d100019800117100c070b9072a800c00840c0f000903421640104a0615504009500704d01d0a00300004d44c0c0d540b090086600f00104000000c01030415001412440b403198800104a101e080c03039680241911107001d070000005684551002e08a5446039603500301480707050000800d895040c0c0602031042d04003404158040d107a5075182541c00c60f400c0d105a80c41040f400310000e040e10fa081040200050034041403c01d400c045040c040b066891104c4801e4903401002a15 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 809288911 1250 809287661 809287663
    0x91a061809250521120f040e07020a08120601091a070b09161502070515040b0a140f1e030103020d0b0a14070305070210090b060112060b07080307110a05 67
    0x40e03140b512464038626001403400e05070314000e00350082d9030302c40000d480a0207403095040380b4442459110702200c4036207159185c001002d000b641005941400c0c100400d014061034000d186411200500403600400096610b0804540203c0f04400e00c4400c00c0c0e0070400d1035a03000c1000c3d4014054041d10304202c03480c00d4041d034503510840d5405406990600c0103c1c4003c6000c2054086070254664281e070622b803944001c1000711030140e820b60052280380c40204081c038000d04450081240c0a10300c5150038a09070030403d407500700092090900001c40629022180c803440100050201c503c1100d6941c850604c0359010451030b12409403001c181032005100688990020700300f2203401000d0201c0540e1000c002d040544142800c00712504100814020795a416402140c01119590240c540101d800c0101070200e429460000d03190241040c0840e0082d4018010320aa00c4138000b0003040316922108640300f01e41c8100c1048490310000000c21007a69440b049884005101d400948402c07030403902c0745 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 809290161 1250 809288911 809288923
    0x12051002181e0a0b390d020607090e060f0307140102100b03071a191809021e0904060806161403011413090b07020718140a0b0301091a061809 62
    0x1e5004440021032800b0300d00751060030350899841c4c803200c040c040f0721700a8a6204003a20040512940b01c0c0d8040c4202a0b80049403582c0b0030012a2b54030180c584c0f81000322041d0f05030140c41030f5000900c0d03c0a44120ba2800c0c4000c00c00b03800090401803034001c0d0040024034044400f404014024584007223a1401e0351301080840890304102a501c850310352581d2240360324442c96401c1c030840c82c000c140b02d801e82900059801d40c9182c104118196843e40c131140d00d030582c0b0920444041c0100e849500141311403c1401802007100054070002d40b00303442c1d81c07025207040001c0d920b8000d060003985551110b680c1c80201c0001c541c40040040341194940f48484541419a41c1164411024500740b1840c002c1e13a54418a2195004105083e050401c201c000c0e48941030790251a140d10041044002503002038010781d07031010b00a0210310701a41d80d4900c1113005140c5504150f41c59500c0b1103601002c52900080b5900c111100c0d401c8400d1828141c00f0010300901c0b40381d80703d0b011041941002403122340071843e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 809291411 1250 809290161 809290169
    0x8010c0516061e06030302060115052208070803120a0902220b060d0507030c09083004170d02121219020d0905010b0901080712051002181e0a 62
    0x318801e8011500d8148040d140104801d4074101c519004100c0c204103a4100f14201da0298003a502c05980700d031450b181c21000d003010213001c980d0401a040c2000005204404958a188465480c4ca6100d484c180e0034181d83d9441000541c0c004079008856100c6030218503000b084001042004200a40c00300d450b0f0b1102000c0355200f0b001524109607620307210742003945582c1c4014401c0382d48005000740e140c01083c058941200080c901501a82c0950082400c50300341c5550b00f000744091a01400c00c0502c00d0712800451102c140c10035a00306101c111800608050030111501c0018181200c6c401c3d460300076410420811944003450400344d084803002112a0075040c3c2c0ca241340b0650710200d55000020000000880385c610008902130143c1b0f96520516202d8460b000901445421408101020100f0701800300e050308903d0342003001310021514446114460b00c01c2c1c4d1923842c180c00c0c0300c4007260050341c0f8007800681603954105180c60030000f4400c020151a080010320220640403914038002401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 809292661 1250 809291411 809291437
    0x130203060f09070b0d05012303100e031204050c12060709060c031e1d0910060e0d0b040c0509070813080c010b030102030a060905010b16021309021c0c08010c05 70
    0x800305102c500c0600841000c2d0090041c10313a980c0c64031030341910090100b485202d480d10000c405988101d81400c40142c1c104d5402401000c1001c02c0415030001800b140244d240584000c01001c5510048c0464461165020390082c0c46811055000d007c000c590071641c1d0591740c4c00040400c4410b030740281c8601c040d0361862070b00141413581d526007501c48441008181d4004103140319912840d540c410090a60808514070040280c500103007801214034003540c4620003200064000d0202500c500074150f0304910040c61180300c486961030b400010241554117685e840c034150700074805400c180204580183d11752420b0b2895251203174440c07261a05590b402010640f002600e003c900b08250400041610001e00031907490801511090080485202c0c19000c2810b120001414010120a070b8219441882e400c8050b8121030f400c000b88684c000d06d0807208150b07141c020300003680700c40143c200c888003074141402c241b101c14144001c1a0099501403051603050001c42d41c00b03123a0150543e07d814401003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 809293911 1250 809292661 809292691
    0x90f1d07032006120a0e03090102031602010c0b130201140301033203040915050f1810030804061d0f01050a0c2d030e0102070506070807051c0c060513020306 69
    0x40010307000c11801c6464140e00c003c002c00e402ea900d00c4100c003028000d00254004208000c00d40710310720345a0164100043c0903030024460714403000d11040904240f94414544804040400c0c0d98510008200717a501c41c0c2d6403c0c401019208550b080b4000a02e0303a90013042c510304546c0f550341c6d03003100028075034401c01484907844001c150491605013128410904041030ba9281c503101c00034100100000201c400203807200350f50004482c00d04000500002c000905165002460301003000da4134100580300520346a40c440c000004289000041c001521071643c1d440505200c5c11201710051050300642071040b4091049108039a8000d811120308411605203840b0340c0c40181010201808416003200c0010109482c1000d540c0509982428141c4a916141340c0404804012a40ca0b02c4034002c0c00d0b0059020803da001141ca071038060311182c2e01c581c0071604100300b040612160b040b241c1d00b00002041d06051000e0030404540203035940048110000303407566a00340c000036034492015000310301a2040c0c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 809295161 1250 809293911 809293943
    0xb06070f1203090b1806010902180d051f0606031514040b12070e0412090f1406070606060801090e011e020c0724121a040c030b0a090f1d0703 62
    0x240c002c00c0320706030051404c100a152991200040c440c242d400c220b00e03402000d001003045c4181d4400d03561a01c0d1082400c6105540c3e0400b4407174800c09d641c00984051244444040840c40d452819100301d186444000c54203500d0980c0c007800789c6849001840c085c418602050040120f101801c4a41c904115804508140b220300404c0600100e5034403d44d0a02030b8141c0400c03c0e400205802e40030b07034490300f000f11400c03000003004c58600d1300a020340b0215452550081040f10008480072010820007094103203401883da4440007140d81541c8080041030340c2030010407100c042403051148060a81000f404800e1244034502244000403a101c81d011394041440400000c04001e0500609210814045900203038000c01040300306c8400041c0000300c1190a00490704290302560124074280401c40002e070508804000181182c102e0f110105541c5403c086d080d82d5481c071000380100250a4005003060403050308400ba241c804842c03c03030000301d036500d000004600090031301c200c1e0340250020088500e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 809296411 1250 809295161 809295167
    0x1d0102060619030605090601150519140c1f0b0409050304030b0c04030c090e012706050403030e070f030b150d080a0201020409090605090d08010f060e040f09030c05010b06070f12 78
    0xb81d900f010704814036040400070b00c60070001c0c82606035044a104030981c0001c00004031071b5449820008400c00062010840006000f4488001546c994540450034000031400a600d001008040c08610283c00c04c0c110b82c2c506501e200d085080e1314191018801c01d0101c0e16003507507901c074902c4012f0101101c0000603000840e240c0a440241d43d0288050003641e55420300c0c03101a000b091000c2025510f0400d010718170820314100d4000350650403858504044c1c132502d500009100041058090545034650a5503515040c8052006001000440031043c2e01314208401d00c0f06000707209038000e20942d0300c0c020155071000200992540c3c8000160354607203500c44124060300440e840008680d0600b40345404004850f04014461041102198070000b801c00c41111124428401c006038505034410900c6400d00c00c0b13040000c1c003003011b480498207401040c144404c440c2240c60903400505044088020004280100c6080c82c6003101c801e400d008554036801044101c3e01d800400d031004200c0001d000c680 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 809297661 1250 809296411 809296459
    0x160f1d0a0b0a06120506100f210c09060215061c111e1c03050313060b06040329010b0a081e01080606040c030212040b0403120e0705011d01020606 64
    0x4405408080b40d81d80e2078001070210300350990a01c84840c20300d40002d1081c104039100c0c41d01140640d440d103d24000400c810754480c1e40403d60103455886c80c1c0400b000c004941d001b02c1c0d0324205142d4411144900e07140c03000781084944807100c1c02d5007031036005100c11503445008413003003001044a000c030703803030182d207405a40150052400c5d078021904403044d62800c0c0e018030030352810401c1a101014000e8408227540250342808070b00070b020610910210340305484210f002581c484c4070340c500143c001e4070080000c0c4180c11035441201c112000c2402c0788a446055010115001c50011303007030105504280c02c6410b03c0c003030750b14660100007a0000044c00c0e43c1110407007140e521000d890a141558480302c4068495008880840c081c80c00d0000c14461a80b00f4402c50311030000b2040f00800341d0b2255520665800c502800035400c218018109042080e42e502c141412014120001c1c1201c628200014000d1802115000c000383c8140c0c00003805a600465503c0d070000c021108a520010950381c1c203c5016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 809298911 1250 809297661 809297681
    0xf0605030c151b0d030e0c030d1d040203010b0901020c1915050f0c0d020606190302040207031112070b0c0a1d2b0203010f09050a06050c0f0309160f1d0a 67
    0x81445000f0b20560000c503107410400710640d0280016000d600300240c1d80c0c45131410b10344d09503000300b515070151441800030840401c80e02c40001c40ea002c20100040a0707070001c2c6c002c10b401080c00100100a17680400602000319005d07181740d62540e01e10414041107003218440c800c001c0340342c0d5090500b024443d60031120b090030740d00251a1104010034005d80e4405814000030b0140c03182002068040c5490202c030103105081c3d070641005542181d09100117500490000c40900c4601c0c02142c000a0007030001d00041230100d030496445002504065401c908041d006103c642c404112264020394011111504100960b00101200b018032000c1445141d508660000280a0b00b202200300e0803640100c2d840b0350b0085000344801864140750b0700456a000c007006010b03a004038146c2002400310741000394030600b5210041e0400c000c1075140c52065204580d80905030700400d04000c5a440c1906555004c1c14540c4003002103282840200594080e690803151406c0ea01c0c2400604801103a401155402e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 809300161 1250 809298911 809298937
    0x6010c020a0305061801021c11041d150a05100c03020a1e05010b09130f030c0602070f020103140606030a270b01080d0c03020a06271101030f0605030c15 67
    0x1982c0e400c0140c1c81d040155950004148511008a041c44050003501c11910700043e201c240413600c6034000e0000c00349041c41401d041000e00c0001020302d002d04505d80300914105501f40f00380740032400c0190303241071500c2c2280301e809860300610131038031401200045034907581403652807180141016071034074203401c030002c000c401c805400060340800700c4008450180b04900a0240c1e007412402c00080030400c0310105141e5505000400c041041c10740840e601d28040c3c108404c5182160322400181e902c0440151185120b81c1c01034401c5580c50710a00c4000d020a09459902d4208100010000d102c0541002c044ca81c803140f41407007040b24000042154449081e0b49a6041154034100321004403d101f1a402c034002c03984100f1049000d60040d01445034541d000c0c103000c0345582d440c0c0d0010054190890960141444001c142c81f4603000aa05201d00401602c1d02ca000036070b000609842e504003030281e1550030250208920b441c00074607010b0620003111008403001c0c0342606100c087c0034409a002203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 809301411 1250 809300161 809300179
    0x80705160b0a1e050c030a050c1303030e0f1905040f0e060f10080a0f320606030606011805060729090d08011503051f030c090e190b06010c02 62
    0x405500307903003d0b00f0a410598649441400c4001604048031002c9503500340002c820000624444041d034444c80e481404100828100b541b554001500f9030724503041140402c0d03940d05c40321b1140c68010050030401c201121840f80f800c070310940900c119a0309102c5e05010f2900d03103180350350110300c507004181c1250340b040c01c540e8540b0b00048011841041500c1e070610f08082c910b408a1340707400108011b1143ca40056502c00c4142180d42c94491407241c03203104140d40400001c0f071090134860404109403140300003004182609001c8101402c20300050015418031441c45c03500303800d01b0b50784243e4408962040b07560a803152014246001d0100c84007040044550480c0f1601610304400c14480d4029044181105c00003242200159801c1d4400e001e4130703401501c0c1207007410200e4442e070070140e071002003240000c2111080306001d80d503d140640080390b01c0b20b1900000d1094035090321941d02450842030080100728414060456055610000074144c50504800200f09900a204480040ea405040002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 809302661 1250 809301411 809301421
    0x1e23030d0f140a050702040e0c0312090f0904141204060903080f09060f0319290a0b040906061806050405061605100b040b030a0309061101060e090c1002030703080705160b 75
    0x3004c1d5126180c224480e0380f03444111038814100150800309000040e00621401105c503006ca60aa00001c60103580101c1002e4291101e41303079480b200d40603d1103807204050f0a030b58a0311050410005083c00d10300c0840c00d02040100c507031704c069040101c0e07070401c1c802c40c1d94000c542c00c0d6190602c21101d2940d0403010010b54141c804a54100451083d04d4a55400c031000c45240300e10820b844090101c0541c013422030001490044140c40c100076000c10080040302141d5942403101e280c1c0c0c00c00c3d40a41410b9584003810003200350440c52580c4584e8855611500c814100344015047d4013030340c0030f0720f030194001140d51240044005201311140b90414200c442d81c07002624188040e2052a154030f004a052800c104158100015410322550f07042d01c130341c0940c50a092044410b50030016180345a5074030340c4e0001540e8a01b8450b468060300d8141d000d40081d480c7c40c13041c48031a000042e0000110744c01003001401007584800644e4006055140a5580e000000704007402594451005024050600700b40302c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 809303911 1250 809302661 809302667
    0x60f030b090709081507050315030109050109050706030c140711060c12030a0b060306210a06020d05010f0e10050d081b070306050a020a1e0203041e23030d0f140a 71
    0x212200c000881d034513003114605c0e0801c090070998442001c0340c42400820b00c0e91119102d060035054001e8000aa2202503458903800d43e8990141600c45800808003800700c0c55150041c0e11000300d05040c130f0007041e008807509540e10b10400401070200c44090500c9541c50f41d482040380c084103610400c45a04c040e035180b4003940c43c1c0c426215101510720b08900ca4103141013a802b40e901c502d000604196403400700501c2030b0340070604101c07417403e01d004070820200007078034601c003803e21018031b0b000004942d0306140d610070072580c0d150400101c0382880e000704401c2005c0b035040181540c00c1500c260700015001e20f0406690300452030580c0c41c0d80055440d111840c0c000044450849009940c1480551604881903003288a211400c05c001a80044801003651817070100200d00c54007441200c0c6895030340c0708074104d0154210100a01c1c850f2400c002c0101c0700c5414843c2c6d91a2901503000c2100b4440038000031b40c1d5000070b03800d04c014400000110340d5010300034812038801c04c1025080c16900c0500500003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 809305161 1250 809303911 809303927
    0x7020106081e121909050f1e15121608040b180a020a0303030e0115080309042a0906030509010c0f0c020102161403011b020c060d0204030807030c02031c09060f030b0907 74
    0xb000544020000403145441c1c010f0041c0341c14050001c09104101483e20382321411b00b4542d8503003089040000241d100702e02e00003000844406008a117090800c2d09101d2008103d5820784002c1010501c1800081003100e203405030030444244503000d080c44807a03102414202d0098010b03510242d03e00b4004207142e0140c10014007500030700020040392401c3c41c6021084840782c0124000c640c418000c0e01103905181c5d00050000c1800100a0320a0110b0325018140d0303200555000d0000c1e000303000400541ea0140182c80d081205003009001a5040d0300700249002c0180000e1000c104c030b0074038420150b90003441140e02d80c1c03031741e4074254000d6034490000007024500005424007079071a2500800307503c45040310079100c048555024001200c020000c0210941101c03100c8908a503080000200181c4ca5000070901c1c24800d4403202c1401c2824010513040480e4002d9100ca00402d52540d420103a901540c1d0005484240c00e1500c0142c0e508a400c8005220b049070035038011207010700b4052919040140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 809306411 1250 809305161 809305207
    0x21180d060b01030e0f031902030d0609090c0909120e040b040606110f0318060703022503060501050301090213020f0d1805071a03040f0212060f04020907020106081e12 73
    0x1c18804c44508490055603402c0402d00c3e02d4003034005100d511752600341040000c20710361702032045038204447e607030341c83c011604650f011144c0b043e507811821041010152102c801000b0f556010024020180c40b40540d25006180303200400c840d0584201c9165281d6118008a030b6010300200076454039248003030079083c0000e0140c203c5100301100d6048200c0c3c00011034056150042c900b400105220f01400040c1c1c001e02812020b50040070110442a0101d0300e10282e0038851081c9d5031112403460400104590040e0001802a4100f00ba040301513146d891038101d640d07141c20303030059582a0405042540b80a00c0305254901e900b80600c0780070800b4044000794909008805940000b42d50b0b890448800204030748046e10080706000040200b128098a503485500162100c01c0c07000034040d015051800403a9044981030040040c0000e50401010003580109240001c00c442420320855603030f14100602108500d0000b040d100c41c241c0340c14480d00d4101c800301c503096034983d8071002108107520115a5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 809307661 1250 809306411 809306417
    0x402090105160506070306140f040504080f070b070311190f030b130b040b010e011409030a080318070801020f070b0406060815090609160314160609030c0821180d060b01 74
    0x1f000b095080c086805415041801010100da0344040d805020141100400513682540b0520070101d491000c4002800041d01c5040d696015144c1010044d080700c0e0f1142004500d40024090040042d14082604041000d0307414a180c505403005022005890f0001d4450313002400c007101819182c80e941c02c81252101d04440038030406995000440d850705002c0a400e00041901c0201400148030304000d021180c0042c007900c01001e825160850b2660080c0e60f41c403d01d00d4140c0000781c0302071083c0301d8000a040304000940c5060500c5180070464014914080c00d0200c05802203001c01c00da50340b04a008045101c1680d0b000501c40c1c01d50a0300c4a4101c803000c86034019400000d1a152000c40d00f00d200106100c1513512450650325400c9554103100160700c440d11542d02c81c520041c41d40e100f404010040b6603129003105003986441c0c040c00b21076900c03441d803035441544202e8103050303212004001c0052002d480c64803030894155000c1e0704e0b20f110004035040015049581d003032218a40003500440b000386c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 809308911 1250 809307661 809307671
    0x60f050120030304080304050a1220011e23091501170a03030c200304150302030906040f03051c0b040513030e01050c0c090a140c0c030904020901051605060703 70
    0x11030401c903451a60302031201d030800c100081c00101c48101450b001070069084031150b0384182c1d15400010158140760010032304001c00c500340302600290b007080001c0e00100a22000c2c440d40e48004500b00005803500e002c54803815020700b4103040405007114503603120018909424007054181e111040c1c0d0304198a070710f403403000100d400042a00c0011220803039200034003543c0201c1d01c2c201c0040c5032800b0350004200d80700e0180080a051000941c4800702e410010b540e50760f1402c4000d03a03180d540d42400405140c014010004d0074880403a800d94030a4001c103240c906044145400c45440c400c400d41c4000784036541072034104401c07003944041009401528100115199402c05120912400d1001000500312022160841d4403410180c111102600c003120074821141c400502d5100044400744140c036070303a0b245c02d1100600c0002e10394108506c51b030802d19000284c0a45600c0740314001806020341d0300040e45c41001d0340b15a040b075404203225580b07500c446241c3d150081d01c0b82002d55942d00024103103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 809310161 1250 809308911 809308937
    0x21e030a0c05040b120303070507020a1508010608090c01092c0f011a090f131b11010b0d0c0303080403050d050a0209030f0d05072607210f0f21060f0501 67
    0x481c2c03800c1005c4030030b00550031640d0306c01d800c507110f521078401240c00020085000032280ca500303600c135204482030b4581446d60b40c10200000c090710f02c010303c0b001c0b03554401c0c844030001e641c200d0396800039501103900702810120a00c040e250300d040300001080034010230034200005070488a00640c142c9502a41841c840920501100c07120b0090303180da140d010400d82603520007807504500351202a8030050f170200b1102c4106e5400b0342d80ca40b89034003074004284415840c48490000384124a05101d003100c442041c1440f5807500200f5480600004046c840c2940c0854181401481641d81c151100c40050209207031250109000c1e4111042650007072140b207000d211100008260140b019849544041c04c00f80540c40d0044072101903180c4180c102c070403c1c002c5152411150003041414001d40500359842d04280c94090710030030403400c0d41c040050005000c141c90380c0c000c0c1030281411161801c41c8004014a9440805030902c1c07501c505200d20301078000032803100340c40401040740c100b42ca03040c2c000504 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 809311411 1250 809310161 809310169
    0x20c0402040f0506030414010c030906180c0506160f0c0302040509061b13080a21020106030b070507051507180501030506100f12020310032d021e030a0c05040b 70
    0x41c42c011015459400e4406200a0400070003440d405401254800d00e0b000000001d603086405481041c030020ba26890640c0602c0514026800c00b00da020603144100b030100d89403900e8010860113076a01c41d590000c0c230f190712180400103818903241c1101120600c101c081c036208001c40f1076440200d00031400c020001f400443c000c544e9074401c1000d00d0610542d404d2414020000e94803203c0d40405a405061003c1011f000811407a08950b22075240360390585030001119841620110325081168103242003400026481c8141a07008581750501d1a166002458030318140341d0410000104111880200700038254410080c3c40c0c0e4580020f144068207440380b00442c140c1c0c0d800c0724005c5e003010201808030700c00340c8200080c200442c560325160805542e82580c5806907442a0b80210400d6040f090900c01d0001c0c42d034901d80c14002130186010038100128210424094079000a40304040507146c440b0b050b00280900842004000d05a85056101e454655054a03c5028003401307149010007242c69414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 809312661 1250 809311411 809311417
    0xf0c0e040204050c120103230f0321220213020c06060405100e040b070318080403021c11040c0203090402070f05010b1002060a051b0417060c0f0f0304061b020d020c0402 74
    0x589050710005030303081d070b00c03406a02c40000032420860914941c50f60031000b0144844004240c0a4003e5980d4541c68401e18421518bd40c00d620b00b100c0c4400e051240ea40404803848000c034684850707507070804e001c03400028080c0c4820740e2400e02450002a400310716202c0410348a1258204440800c866201c03040340c400ca10580c1d009403800d2000c10b4010070b01050101c411142c2c042500c1c5000b156071221005010b00301c0f100c0301c41c102c42600c000b040c140210314190007003c10405d00b40d00c0d03140d40c0d000f141c1c403144529100c50318001e0081d56203c1c1200c40803442030017281c1e11400050005e542d11704407490406e045a00c0781809070341ea5403a00c0d260070f002c0e1502000ea0171a402c15940146880e444481c21200140b00c041c1050ba100902d070301d511450700b1480c1010b48020482100c01144540c4010b80c903500b0050001d04000140e276007008501503045102c016030311034201f45c1051680700c1d941c03450498020312803d0350840c810b40d0780000c80301c82241e001501c0702d1090b4541c1d00340c4010700c04840500050740 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 809313911 1250 809312661 809312677
    0xb0a060510080a0905120a080a1509020d0932120a0f02010b030a030306080c030a052122060f020309030703020d03021903020d090b0909010308070f0c0e040204050c 72
    0x16100c40941030024400d01c515500156032010001300180380f5500e4900e001d0442808a0700d1000200780c0c80100c90f01300c0f071900d038850342040702803041800100301a1340d80c0529005942143d980030600300104a031640c08402d02c958040e81507903a101184682d000d5442800e600802c0c000c6140d4420345a03980080b5520141540001c1c3d05401c04141c26006d0341c5400141071903904541d620100c0d15141e6400b0015a05000d01a4400040140c1041e0b0700e5810300c4400300c600d600070b070302c16404240010000581e15102c0c91007854040c105100424030150b65114280c403100820079070544e00b2506012648060b0200c030600d854090700a242d85c102a80c50340101140325a041d040f0401c100b0150070803041d164800c078402d01c141d6103150f811880c0c911001442c541c0035001070384807a81040070650820841c00281000d4040c440c02e00d50f0560000708030420501004020b104085004010410402c8602e070b4959407101454250039140e4541540d850801c42c0e080e44101e0034078012030b11403d00c61007229125 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 809315161 1250 809313911 809313919
    0x100605040503060609041a07181203081620030d0c020604031707030603050105070e03062220030708060f01050405010b0a230a02070321020d2102070f0b0a0605 70
    0xd90b103404c00c204c50010000c105442d034100c0203520300c00c2ca00c100098940320300e00907110020089100c60008512804075080141026415070300c40c00426008000c1c00d0340041c1916000700002d40d042c8003100c002c07201107460114003007510f0700e107008440040081c0c00842c210200421041c0740e01042241e40720003d54001e404180d62000e0300c224000d0b1100309540c4080075080c04140d140c0e490703469900b1200115001000030381c003c50781c02541e10f410300c40103812030562251140f4003540c810544968035840d41005200a0b40800c40b81400c403a40086030f61025401025200da1503520398149445103000c40e04103e001404030000f003200e1609124050581d18904030391411301040e001c3c240c5008801b2034440d5400d070210782da22540d22041c58014010405e45502502401e0b1851500100040880031452a00030350fa442122800e5400100600e005d001842c2604525840f544400380146100ca19a25114000a103030424820b83e1802105a41d10540602c92a5a19050780b50119202400f4540c0d03c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 809316411 1250 809315161 809315173
    0x40f060509071202250c150f05160209010e0114010c200406180605010e030a02010512190204091a01020a080d0b060903030c01050412080105150703170a05100605040503 74
    0xe402d109001094042200709401460304a85c50f5400101e180145007800012808081c0c0c4010000d00e4035805000381000c5280c5158200e03440c1e40070341500c00040f030381d208021000c1101103503910365260103140e031600070b0071240041d61240c80d43c007815442401221486001401034035000e52140c48481402d0760011144403015140d10b481e143c1c03442460784101e6106072500380104403501c0b00c0144901625a00c00002103070740c5400c002604000700d80c402c540c8030750800d43c0d001000d0f07600700048400410b180c81004c0d1042d9503240702c500340100c841000c4c0021030710104000c5030b02201503211441e03400c0d200420001306070600d001240d4034030309254000c00940081c0010305402e00c441d0042c22060038001c1c8803506044a203400701e441c60300b024000442c2e0b41c0d101c0c018403041c450254044a14015189010031096061001160300d02009841454103860300060a80c03d0510410010780c41120190000340d09060906e10000505025500030ba900c0207070f000700040840c01a0121011200041c000e001c1d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 809317661 1250 809316411 809316421
    0xc01091b080c040c2c01021002031e040203031b2b020a0b0a0207140d140f0306012a0605011502032a010b0603010f031a04150903021006080c040f060509 67
    0x10300803559215081c01001039011982d00c128170030012501c401e80f001c40c200096002c0c00280f42050003514450041d1040040c0420361154000c3d0803c03640c4040020045a00c4d02c0c40803a245104000080340901160b000200c0b1001e008101d00d00b0408142503002843c41501c50304d14803002c50070048001681c4144001c0d0b00203186580010743c0320144c1c04c0014100720030f50b01c988800c1091196802c203035811402c0c0000d030031074021003000d43c980b1014400504240301450b02c69042c1c8130107010b0343e05100700f5610501440e004a04051140889103400b01c0d03d20038140b5024014010a0007958007460701091400d0f2240d10000a4542100e252060300c0103000c01442e4111000503a50001c007501c1d500ca143c4001140c85090065000746019061500c0051840c14021a0340342544d20034410f881c1200e0510000c2601e501c8500304141e25400001451411440e040e031500f0740000003e00b0040c10704400140f44840414440188002903a090060380c2804554001b1202a8050b00c1d0784800201c01044c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 809318911 1250 809317661 809317669
    0x8010c0521060316030303060e0a23100308070803040507090b18190509031e04050f0126010807060e0f091f0306060f24140c0703080c01091b080c 64
    0x1c0c2d0040c0c1d001e400d4800a455551000708100d01c25007003034000c2a100c4204000c800c0b400245658000700e440341c01c00a05000e904500c0c011200d0a1851801d0421040850841c0650041c501e00466100359019980d090386e140907500c5410496003511039024500000406140034002c05075484001450b50502d14040403001c040d201000d0801c055421400d00300c600c55400c2c0340704290141d01094000d42d122003030107221140c1020034190145582d60706100c20000d40d1105080900c515509091103901da045032041400c00c0400107200704000301c2e05c040001008000030a249064030619500c003000b80c031702d01051003403c03042c1021440d04022040b00003218845040c0c4103a44c04029011000380d5181d4a482e04c0085c1d904503080900968a4140d0070003409608800924580309045030312400060250320160485c4100c00c61462841070005080e01c59010a02044010310f40c003801c95500d46521904441c000e10100308206c0d5681025000700c102c854281c00008212500c8200600c00060808184 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 809320161 1250 809318911 809318977
    0xb010b0d020f03040302030408160506040b0a0302090d0b0702151509060d0606062f07180902040501031b0512070302010e0d1221150b07170304030908010c05 69
    0x2000300d1503400c0c00b5110010300e8180085008902135070045850b0741c00c1000c024182002c102c94543c800c0d0882400f00300a0311040103543c100c03042c021302d643c0c0b41c09455405a000e44a05064a607002181c2d01e0020200b100c400e070700a00840c0240d017160008a45400341d94030180c404e55012800c0380b0490101c203918079040060f20b501c1980600800700c017014130346c0c0e01030070303103240350003590200ea031850907885a01066110094070814907034011402c02510341d803442d1990310714060b4010707c280740c0e8520070040c0700c6a0003c503810382e8081d1080005694034148146003081c0748c480280c48006a203070010360303840c110482c0f204101100700a0103c66140d44d0040d07600e10f2112810a80200c2c0303807110309000ca000711710030b551440413030b444241c2418104210400080f0002e040f40306094039000700d90701108a182c0051050340d03419034240e541e840140c1007210400e91180d10000110700d00204000400d5409210041103500950091003180d205a00580d064014007c80d41c805610007088203621002d04000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 809321411 1250 809320161 809320177
    0x1104090305130801021c0506060a110c060a030f0c0201060e0f040f02150702011806020d08090a050f07060e010c0f02060d090606120b09010908120c0d180506070c0b010b 74
    0x80c41c54000922502c1051050603400001c503a5408a1140110080d0140600c4c2d55103000d1010032503440d01c5030019420b400344601034410000a040755145130042008038a25030394005140302e80b121800100107020340203901c021082c035800c1882e008481401402004140d88900c030301d100040d03582c400e080490407030061054070001e54154025000d03841d003034140e802000142046c60b954042500014044002c211031341c0341020a5003500300720007035021a00c1464014030386091042c985503d10b080d403500f903184a01904501443c00340c0d0400c0130001070600704942c0340b40c070382800001400005480c594060741c4c0107001340844115075401840e10340000d105901c0b5440740003842d000c4e02c0c3c6501d01103440a82081170800400c910f40c1c0d007030040310a03403a980702c0480d1000340044c440c55500c0c10380d135000c3c082007120320540712000720342d11484c80c00a0310301c2c0003422081004002500c60142616405c1d810055440d400307100049100e8a114424900c1c195030410144040d82c0d207400340d02c0109074000380e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 809322661 1250 809321411 809321417
    0x18031c18030219080c01170115020a020907020d12020316110f0a1b0504050606040b0a0507120221030702060c0c030903070f0519140405070c050f01151211040903 71
    0x800140e442c43d62404844000b425214502c81c103001d121460850745042d002e06008442c0e002d44040542400c01034151442442d000688020903074050307103464205e0800a6112a40c90700b0810003a038005103451554045681d8030000f000000c0014003244030079100d00803040403034142d9120860080c00140e00c00220001102c84138010400e81303c2c1858000c007000c45103150b140c542c0400191505070404090700044030100f00d141884400035102e8460745c4a20b480807007002c2035102d510344c013070000d5695403500100441000000488029291000c001c07400084a079103000006401a255013924420f100708c0e002884a5150301c0320b00d0170300340c1140d02c2001862000300810601c0e03880c01d00403900107100c20750952209504110400c031500d031907400b0720369054102103401c00001c4c1715030000c5903a0b0101518000b51580300c03e40100d548528003c409440c0e449000c0031101100c0c2d056203c90060710300c1102503a840b548624150441d0b103900e0350040c0191a1003d0275507030038a056402442564441d003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 809323911 1250 809322661 809322707
    0xb070302150714120105030f071404090807080703080a15051c140d030b030f060705181f120b0f01020705120709060609060206070302040303080c0306010c1718031c 72
    0x120001e0382c3c96001c204c084001c00c01d01d50040042d41000c12103e0080101d010162640b58107210225a00c0000d4109071031003030b81c41d08040790902c180403003100c458a400841095503000c0ca41806041100c0c1540c81c180348500e8400205044000600210b00f6a4001004021001c5503c056107200c0b42c01c61405a4a01d03e10040f021006901040400020103160710007080c800d0301a0101814204422000340d4a504075004100c001a400f1044880d5040f802500701074039403480011951042072002007e920140f1a002244030f280c2020010049a4030f010341400043d1905041c404181001814140580d001d050b06211520384042d002550305181d6084502140e6904041d00550b4566481600414100c80c2c0c1845440c0e81404401d50094003810190b02d424a540d0b001070800304010320b8254030b4030300800410f541c0d078415000c194603d034001c0700c144040788480807500b05591240000da900c0e82030550002c000382c00c000c240d0201600748130740c3e03c1c0702c11080c8144c165200e506603282c030130b0708003124 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 809325161 1250 809323911 809323937
    0xb030609010c091a1c020d020d02041701110306010f022b0824060705010f0501061d18220804081b060c071509030812100b0703021507 59
    0x1000024495000c03034001041c2d1900303041026102c8112a00000b0011a40c20300fa00c010302d0383c003811211004500c5003801d0b2488000050703d4000d0182d0303045181d091380001114000e604c00b64005d4000c0d145205490400583c0e241480c6003290340c4101e103855250001d10000302d135507002d50074030500080d160045d03480c011110700984030022104002807041d0b02816541d248070907803144403140c0c09282c1800b080c040708140c802610700100400e902501c00c00e0002101810410207400c6803002d0548200140501c0d40c456038060902c140c4694491b240d416443c0e00f5005a2074a054108203100012030041d600392070304c100380040c98090074044500034009040500014492000600062154002400140c4002822101361444162207684141000d000b62424118085450700485403004040e000240c0700e031b842903508820301d86c4081c000500200e98902600343c084403903803085040950481c2065203480e11600c0d2801610780107001a4858000101214001e4000320b030000d90608101040e0700070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 809326411 1250 809325161 809325163
    0xf07050d0609050106020c0306090726010f1e0b09240d0809030105070c020102061f08011a04200d090f12031505010e13021c141006081314010b03 64
    0x103902c500300040d40c85004004441e414082408290011000b400300c0b410218940c3c0d07030355003050007110300e104030030900b00040340004e5840603043c110180091250383c55680e010320007002e10241e200f040802c010550500d0000d54418940707405d0707005180c00490303100e81e00001c0000184000c0020704c440340c0e01c003404040d40d41c0c99010800b80e00c20524142c0d12490b403070a05003940c40c0500b04105020080c1c481c100140c0e0049036041e030243c00e5024420b110182d10041c9500c00c105a03018103d194030306a403c0074105640022541e0030041550306000c2d104030100d034074811010461404124510a2141b0010140141c200054440c0910504007a140060712403d11f00d00c1981005000310340d0301c8090b4000611260a400d009003400d0030124410384042022802800c4000c8906940b99400a20850f00d028603a5680d4203804005408000240889400c0c200c1b02c901a60f1200314814190000a0a1841080c50a100792a10124021800303003981e40c8014a4039040000e400f6552541085007640d14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 809327661 1250 809326411 809326421
    0x80c040801050c1b06040215030411040513140304050f010507060b150403050c3106080307081b01060f0302040207030e121b0904020a0e09070306090b0a0b010c0b0f07050d 75
    0x15654003034564038061024000000440c202c1c44111301d8110508000140c0d4070071a403c0c640f21013055204d9500e0303581e80b50059400d4000900b03240d02c28070b4030742407188007881484046142442800350403400103d600c80107a490085124007039004484820031042d0754030480141c981584600c0d07000c11350356046070020f0b4903903401c0510381c010328034042003c2080c04001c000d400000398003561880f10075207201c0c1144030400d10340c202580e8240d000044080e02da0041c1c0e484030004144a40540791a283c0e189021401607100c0041049000301070102800100018424034084402401461402619650030320029410000044c0d00344004020507030507a4a521007201c64107c40304024100001400c0b01c41b03000021814401d5006410141c1040010384400d0142c0b4290f506140c01030a0556405110074604426608014407490924844071b040283c0e06007410300034401d10009000d246580401150100c140384005003000150394007007a182200c02c61f00f80d81048142c5070251500c2500b07981241914 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 809328911 1250 809327661 809327671
    0x40b1303020a06052409060f0127080a1b15030f060e090d030c1b200d05010203070e0114031b04091d060f01120b07021e0f0f0616080c04080105 63
    0x28498030041c0d1107400384e01032040c01d000750841e00e0b1b02c081d0400c0804a01440203060a0320b060062404d10745840d2107803502e051603010802441b040300035803100c4445840c3c0110301000c48501d10083c003275030170f42480c110550302501c03803840c0c03000480d600d25001140506031071000119050358410f40403480b44007210300710f80304020b0340c0b001349441d1140302c00040490700080503480810812682e0f00c014803600800040c240c40d007001320088012407421815425016000089510403410701c401001c000e819009584509400d407507030302d10129240e0040d40d9064a00c05150000c260400c005500000c8482565011203101d0b1030740d50410f503c80c92001c0446905646101ca81c48021010703c01442e01000859802035034032a1170011549082030020711195003a03001040190400700051031a4070802c100d40700b0852004c0c0c0c0300f005600e488550343e1100d20880c5405e105014082d000016a0700c0002c00758028041c0d03602c1c514003502c800104503103582e0b001d003100351104410000020700c1002401054029 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 809330161 1250 809328911 809328931
    0xb03070819020f1e0307060311090f040608010207030c1b060e0402160b0c070b060409020612090a020904142103060d170406050310120f06020304020d020306070207061106040b1303020a0605 83
    0x30794009010185030071b0203948040205400c0ca201c03141d0313032400c600580c0c103801c4003500d01c40c40b01d01c61580014003a00b490f4024545661001c140f540505074000312070300502d80580c600c85007880d40b06c1922842e507151405003c0111319950304141c042d09165006045000010b00b11b2101c0c84842e5030742d43c50312072058800b0117048802190680c1030000c0c26022503003041c0e04640c20040c50426074085983c50040144100030034101c20002502060284511400154018440d0445180918280403200c400d894400d009100b103041c030140207040f40e188800000001e034030746800c1d55103c40400c01e4500c0b0400c021190001c0c0014015900061200038101400d025128180c4a2800c2d03842034502d01d50355441904400300241c6102e01107a030822100084540091000d41e5941d503900119800650a58009401d071040c4400c22524a41c089040000c1d904e0960307450801c480c2006106a6070002924050f100080203070110b401c5400b109107154400b03210340140e4900700003540340c001c110361044600d1180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 809331411 1250 809330161 809330209
    0xc0a03020c01030e010510060302030702070b070f060b060315060c1e1b011701091a0303120a0b0a0e1302010e1c0c09020f22091503060b03070819020f 66
    0x1c960705030181c1d41c00101d0b150020000c0f403070f2503045016040c0b802d2040e8000d00d6400408030300d030980f00f40301d560040c03c4240c0e8a02c0e640c2e10640362441440ca8001c0042d00c072546860956000c43c41d10500f1280113407100c01070031280c8110700c420406158450410750741c0034400c105060a490110641004000b528940900740c00020a90000c83c4210010145070401072048451420417814844250550380344a80009900d03294151003481c900301203140542c94803000c40c900800e182009220b40c400c03407075210103214004a00082c411180d00b240160b4508646010000341c070451020b001054450052600c9006041c1300004100d500c6404124405400407400008040c45454015100188040541103207441d0b10101000c4030340c0202050a5401c0306440885005010044850000391005010400c10707061119200100080d0a01c4103c4c3c5260801900359818a008902d0004070341301c103406002c40a2840002213002c1d0076600c0100c1e0300030148031040582d40c80342064440c18000f0f042400308 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 809332661 1250 809331411 809331433
    0xb09061e160605010f05030a05250b0c0303150a0b070602031504020c0d030c0f050304030c111908070803040308040509100918020f09011a0d06030605070201021e0f120a020c0a0302 79
    0x4480c11290b00144c1c0030382d115000c0b640000e4000180c0d5590840c12b000e0382c5188403c1010062890b1015a11081a440b0301050784800804040001d60003121354203440e8101c032140708144514a002845464100c0a0a2140c400407451640055911004030700c03449403110000000a000c9800180e2a038003181c3c00300e540c030000c3c50f0301845034050b41c00450030905090f0245140060180c0310080c070040030000020310b14010400c080408001d420710090103000c5405c0c89450159044169118103a510b200f8403070001000c1001004843c00d880d0800718280c42c00781030406101008401170401089620802400101030910f0b01c2180c590503203544a41802507800d0040000c50040820028400c1c503c040c0100407a00000c0c100d45106102105640e494410040251008281c2c41e80b0190082e03041c0410400c80c15810341c010080e07061ba155008411a81c804030602d4580210700110b01c0d1130703400700621a440c02c0320b820b24541c44050680090302e080800420740d4180b201d5003800700c0141e03010391a290 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 809333911 1250 809332661 809332679
    0x1c0905041109100e0f130b0d050606032506181a07020127030201030b04020c0709061d07080601030b041d011d0a020307150309021807090b09061e16060501 68
    0x2450b030307400518013680c4070b01c203d200140825850b00905807003042c281442460700007140e0003c200b101002450b040c43c0f482c89007045a15143d088403c1c500c40c2c080d44092409108018026074810504004095582402e200c0c1c2641c818101003082e600301011030200090070b40d4011074210150508400300360f00c0310607a20001d03040140e030343d04c84554100b0440290740303503020320f200100440380c09103030214000010601003002031091103601d44a60003802030108113034840d41c0001007100c102220102003800003448100d1480020b48030200000d00c000f02040e22980700380c01140c9102c03001840000c40354192401007681c4141c08002d600700d65100e42118090302145500750b45610030000140550840c00c0e0700203900d80406000d4011400601c961902c00a84240d001e001c0250b805818808010040042016010000c5171b0a600140d441c2d4808074405080c03506583c420140500741504086007041c6000b500742c40b0391018005040c090122902c0c007031040b00445090f500816002459505169003a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 809335161 1250 809333911 809333929
    0x40302012406120c052502120f0303150316060f0e0103020405030c060711030105130b070c0317061311070512040302010f050f0903010c030203090f0f1c0905041109 72
    0x1618221105107010401e5581212088403851002c90000452605035031003510340c0d000e40480185008002d02086019010102d03040c2c0340b040c021940c1c034003032403561641c565890502522541d0300f03400900200707002aa40c42c8030000c600d00020152205001001a44a443c9032254018000070702840840d6004581101e0307200d46451003031806510b05410314000c00d0792071101c4075409001e2240082d862013841300886030540c4041e4010b00a2000e42440d11400001b690007180968102c1c008002103051980202400e8548540c9a1154214000c4503d4032011810004040e590400c24014515038020b500b03104031460a03540700001c68403000301e400c000703140078110702d19507112140030442400981e820582118280340c640c034005680c2e14a0441004180c050102216051340c240303d0b0140050707405402451141000720704884100020001c03441d074400c3e40b010554040d40000a6a0204e287d102e43da640c1c0f0040303541004c004c100d0391040410202d07400c0075420a03100703002180b1910b280c0717090600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 809336411 1250 809335161 809335211
    0x30f0303140705031f0506030c0f040906030c03050709050907150c0f03081b0c030915071505060f0f0d0204020a0c05070f0f060f0207062016031401060b1602150304030201 75
    0x30030b02c00c5d80c3c1003401080d542d02c001343c141241c440c4003280c20080385040783e0459014001c4a9014044140c0e04d140c40c070014902800700710390702e008900022901c032965104040c0708610321002001958901800c40c14485001c0038001c08204480800501091924000382400fa109594003002441c0c00d50185000d14080600103616603010482c0c00007922001060f00c0143c10102c0b1483c942d82006403100102e80304100d401402110700e06809118107001e0f510a0f03104d00c03c180c1d01108214010001c001910204501c1642c0c40000746090744007504166019041041c19400c0c420203800301741c0c03035107890030800768031003d01d070b80d080203040c401e51062444000081165040c0850554030454010351108000d0050008100012a600300c121040300603078040c17140f40c1c105480c00c6194952140003883c0305408256806c82d40d00700e45401003041407058400b16900303880504e0a244003d1104050100c046a059a208650244141010301c9000007503002c0e03840780c1c00002d03080c0041311010540d6002188 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 809337661 1250 809336411 809336461
    0x90a23120f1b1c0503180f0d0b1012050703023c0d080a02010e07050118121401110d0b04110d09050106081c021015030f030314070503 59
    0x6510341c14200000d4149603440104041c508514002804102e20000c641900c54628a09003d500c0078018044020035004c50983c41050090b003c15043c0030141a010b1059a000001ca254280c0400c031200540c6030040c00a00d65410b0040d500d00e002e5190380034809056a417034210140030070440c6000554006103003e86007856102249440340091198490380c6c0c942030480b8110300743c030b6a680d24010000410b0340d002c2803098941441c091300900801a003501005c86103d1410041000e6004000344c0055110307200803169820b040114000c800c00815204031094094042d841d00220800e01a40c2515018000703040d0701c1e0b6400742da2a10a40c2c42d6841214011072620059100302c14102c0d0490303c80b203100d848046088041d601c0c0150042859a0003510170707028680c0d85200e0000d0f104400c641d00b1005900b2030380000003441e4402c0807103091040510240f6112041000056418004500d48070302900340001c0011210701c00c0c000c1c00604030784140010300000308010303440c1040c51424040000d212 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 809338911 1250 809337661 809337673
    0x91b09050d02060f0d02220815190f0608060a140109020313030302160507141809100e0304090504030503010302040c050922110f0a080903031b090a2312 67
    0x82c0100340a8450104000c01c2c4500000d001d807805121340d0110741c0c101410703000f400744000d032114014a10194070b01968006025001c0c046000e0144030000314000c00700c07142541c200e617005612542c018081c0c10f03445512035896210004018405210441c425590500042402108a421603a02401c1600400007061050003403045129180e64004d0b180d9615081c0140c0d03841c01c0d086503ea8151000000500c180b16500000c10401c0e4902a559030001c010b036102001c0840c402e1000450000458000640e03510044800308110030780d80000010180c0e54054070b2406031154000401e60340200c40c142c0104000100400841c1804d20070750001c0001460107030704200b9043c00090f46482c481480785110502e01070181d807200502d03070204511007078660025540d041014000740c290740000c00400701084041c00000c0382d0350f03408801c0728800c03141880b07500320800b803068010405030001c0014580090040002185007008086441c0190600c0640103001202c940208a46104214255581d5070411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 809340161 1250 809338911 809338913
    0x70605070317073507020d0e1306030c0e150105040501210e01090b0f1803070605090106090f021e04050f060705210a0305060a0f0303030e0106091b09050d 68
    0x402460580c4040c03602e450b00548030510125900781c413845480d895940502041c1070b01001c0c01140014020a5115842d0aa130b141d4000340d071100459480c01c0080340003070344402101e1500c02c1c88007400c2c0203440c00001d08641c03251030b10b02c81d000c010f4100352200c00b148030900907040160310044407241000d1a21516003414400000d002120860114100d080205804151710400d6001000c0c001c02c810700801404425003403281070813809490710b15a500d0068041b41c0c000440403c0034429078001c100841c030308038803030f03072030700014400144041041d542e070300c00100e40320505000d004803012403194050385440300b108025649211a00c41aa1130a01c204400c21107034407500308840c2c0742d140440e10703680c4480710340c1001410044642131512800442c4030003521424002005031403588110ba40402a0b542e482c001d01072503041d03c4c080c0d560405003080081000a00c42d410069451355100004118280e0ba560f0351416207100482502c0340e640e0b40d240322024181c3c04404100100400c6481907074034006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 809341411 1250 809340161 809340167
    0x901060315021e19110a0c0b0c0304030c12030f08101202040b04020d02190336053315040c020717070311010c0201021c2f0706050703 59
    0x10034001c07451490380200745807110440000e04086040c512122203595500a04030301d103500082803010901148455840c030011400001e490591183d01c49070b485009414802c0d80c4180c5d03003000c64180c0c2c091008010200018800c10b100300010105c952221f0610381d4149400344c50240b200541c041001700d020b0801508840541e103082c1100c0450581c20740f000c800d400481e01038103074020400d80081c000101c810400060394014001415030407407403090580000320840c1900c103410491284028184450342110000c090100341c020840742015140400c0c680d02d4904041442c0403215000c40c000001d9a00c11a0303038800c0340024260690350f400c1510301500c03a2b80b25406070350409401256501c0030b81e81698020000380002d000c905e060301d400c1c031000c521140e40d1340c109404101d460100c4d5400855565000d480c14442c03135039058014141030f10103c006507000303800d92425001008252036000c0d0450840c1d80d015003005040c000724401c203c0e825102c00f4a4a081580b18500f002410018100031981c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 809342661 1250 809341411 809341433
    0x1b08060108071716020d021507031104121a090c06030109022110140612130309050d060e0f060105010c0b0606280906110d05031807030b040b09010603 66
    0x1401d09081040d512002d0040350030254070300401120301182424000d0308409403002c841012080e608403900b102401e04200d8031024000e11404240c111400842e118600941280034907a051086403070416940b8128132020031440103069400040c1040d81c0c0c4844611085540d902c51210001040e0340c0034402e0100340e65110511445040c15404542d0f4000d0703085c0042d003500e80c0445008403503460704020f18000469060707071103255070800c91070b80c2480b90b504249041e030350300400c1209400c06543e1801c910702a00101810100e0800152170004101503996001c40900301d07024400c0010000d00d001d002d189010380c8010301d003889030300000042000303030303446801100000d500c10001003507611120b01040c0707540540361040d03407940b00281c2c81018400051820101c00c4215940d500301c2e055460900b665184c030710218580f0a6000302520401c4640104011a048044807500700d000d030460307407100b6050210380c1d081100c2d03044101c01030005015403501c00c0c03038108500304001c110702803965451401d030700703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 809343911 1250 809342661 809342671
    0x9020c070311040b0d05060f152107090507030207050f0708030316090f0e04060c03060b0f07052a100305060303070f03110105010b04170c0a140d080a121b08 69
    0xb003000c40c0b01c100d2a0f200c58116900c2403c1c06031900d894580703d80b4040e034540b401181e85410100e4650002481c2d40340030906184040d5019201d2082e0300090300c503d0110100c852101d60940c03042810004028009200340c0380304407810341e001030701c0398120326009090003102c10324040341da400003006101907000441100d8224060721140d002c80c214104d41a240804198000c4007010100700000a41c51a6060014460751040008000b19103140c0c0d010703000c032134050149401c0c01c1410b0051404246d461400ac0203000c0c0180b0450380c1110714a4143d4828540c402c3c0d400b110038a002108042505241001c0000303108203041c01c0c001858184046952801800c001605120305c242400d006d241c042c4860884c0d01500700020703c1251785070b1000b880594094803e0110940412100c442c0109005c54651314524004107601c0c3e61600d0151f604c15540355000d1140c2d4002048003181001501e88030040903148400c1d02c8481340080d0440c003002c100d07440c40701d05840da018070314042800c0c0703039002c42915409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 809345161 1250 809343911 809343923
    0x50301150816110f0a050102131203090312020c041104240c061d06090109140a0b0a1a130c02012a080a020d1d0c12031801030213030b040b0109020c0703 67
    0x4550070308880c0d8500413168006100c1c0c0d010701c00c082c009000d0b043d00103010f006902540702d05243c0d07903605054443e1000c000042c0c0000c8080d0003d0001440012040c80b54004510465007840d55680009048a09a00c0100c41e4042c1c005030420100314043e11245c07080c800b0940b80e140503c481c03d0042d0113000740700d030001c0c1101d549440441000c088008880c54940c100c600b212160f15001d4000f42c02014003203800e403080003612084030000c0b8000607028110b2540104190700c3c54a0340a1000c0c040c1210140d50b010644290a0740d00c0c883c3c441404a410301c0704074080101d4411022540030b42140e80c4954041000001c25034224010041ca104164040e6800e02c0c050240341e841c1c05d01d00009004d0361103600c242c02d042c096a40710001c100c0442d014000d036101d056481d4103403504104208000e90340184102c1d9042070190300340804040140101e802c10604001d8901001013507441c82c08210ba82048407144141e009010502412001303840c0500590401140740022000d9865903500d2540300051003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 809346411 1250 809345161 809345177
    0x270c020304031101021501180608010507121d0607050409050a020910081504020f09011403070c0b07020712060f0f090c09020d060905040b071b21050c0d050301150816 73
    0xf03a0f0b4030030000020299510701c0c0c071513069615400f91208034503098480ca0f450500700400420003010601c030303190043c85540c44540c140007143c800318018001009624030129011050038103010001d0105038812407680e5103c44d030791406c08803460202d40e000740c244d1818610602c07244940340c5840040d00c0218455082100c00340e683d0000d000c6040560000503500a0b001142c44049400d0000203400d1210090f2603003a1441c40e200d4400072140001c450794000981d0303010008001c241054400c54001c1690704c107461040e030715100e50501d47c2d15009000c4520f01d603074040701100c1d41d07950322444441e2010550700340f00744503aa4954040045143c01503052303040c1c2c0040c0140c0000d40540c003c00091010040a010a01d4182402002c2c202c085545c3d4012812117245003000801135402202c081c0d500480c595140d40c0803c15020f0791000350803507041485001c01c120959a18100406c1e0001815995010341d82e6040c03014114440a0000000c01845650b405000c10460300b500340003814402c46c542201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 809347661 1250 809346411 809346443
    0x70506160320280909061d0105040e0307120806180f150f040e060f1b04180906090b090c030703050c1903020a030302210a020a0b09070f270c02030403 66
    0x150036840b00d15a1901c0f25019080c100d20180c20100c2c030400c03609254400c03c081550345000c55004c00504849403c4000448010b01803440c00e0f0f0312019014185e40102c0341403c203150384405446840301e0700c21001c100c0010400101d89000c40c0401d1403030740c0c1d203c01c0003c3d03800c001c060740a400401070105064bd03041c20441c00200c2e1980300c501c5e1310200e0020801d001a600640749951181016140d1309104c03c01c40300020b025100302625007208080306c042e414601031418421780d50b240034034440e413a04291150641400b24405e802100c1c0340d6801200c18400780c0c100f0b102c109252454070318015010350011181040480c0d80400c2e58440b01000761201d510b8030043c441441010b030143d0304001d41c01007803044040305260b400100b10320b154001c80035400002450410190041c094401c1142c0143e00100c04a0b00042c110a0616000084582111402a00da110001c03410400b138204880c000071189405220590010842c2ca015403000400c00002c003000200a407030b40300300d020251030318240c4410170f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 809348911 1250 809347661 809347687
    0x3021b010212040902031006020a0515040602130b030f06033007050d080114010c080906070f0b070509130213031e0c331211040b070506160320 63
    0x5015081c00b8401c140d446403140600d40080d001900c0c00210408040c1d00480c00c540001403001c807460308400207080c03420007100903ea807401c006004444003134091100e2400f000d415134161000d840c109900c580c8914194800400e1114001c1c413103480307603000092001d0800c40c000c0c402c66070700c503000c04404110845428400214481c40384002c205115510b400200643c7c00130015040c0c88802203586081c015103401101c0c580c6800f00d010745000c00801c180d1b150b500e840d10051440902c00c030310302030003050640c54000c40113100301c910310b01081001036a44101d103465110712035007102c40d00d41181402007a04103014074103400e010091880804c0e003c46808016030240550ba1294041ca00204594a800d4100c0e202100c06c0f603280005020111856030380168010840c0900d1100e03600c2941001c814003011004e4908009402d05101d820400441c0342c45a0303d00801c2002d004800600d41814061404a00b00c814504c4800805140ca84088606410102554071301403200207950b4442c48401994 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 809350161 1250 809348911 809348923
    0x306220215070503040e0c0708041401210213060311030f04080f0d0c12020720060405090108011406060301230402160c080709021204021309170c060a020703021b0102 73
    0xc8299600041080c2c0c2c20401c1c004001c00545000e84802c01c415241c03009a030b0070318011803a008140c404240030034032a510218500e01d40c40801490900c0800d9640103403000e2081c8071005401c02c2e02d800103240c1c266410304001d604000c240d10310b010002c10b200c1288401050001a080c0e00d4841440d0340032034240310016094801402034407100565a95541700d515004200300c62004002c20380b0715040d20518080c80c070a41d1656508903a0310b00b0b501c3c20304801c0726500407001499540c4141e0911012486894411105020309940c00c000502d030a0b000c101e800035420000c1040348203400c200010722441d0707410081c00b407184c5d4048840301010303032045000501a01911294041c0c07000c0795485041400700d14544072086810803815100300076200c2c0e00d00c0d0280e12449010320510154032001ca401810320100591005140ea100001c0080349036641004a0310304a03610340c00c020000c241c0c9a40b480c02480303016000400c0420443c44c1c0001554060345500012034a20f40b07004515861034020b9000f4010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 809351411 1250 809350161 809350189
    0x5060106181422020301230102060a0b151305040b0a240c0b040515090f1207020d1a07020c09070e063403110a0203061305100507050a0e03062202 64
    0x3e00b40c070f030300c02e41080314000790400d01c80c000304860444013500e103141d0090340030749600b50182d01070881c03652454194400341c256447c0907a00040c101400201002d14000940340d4ad0030082d144400c045d140001300003d5510f40d100b124403419000b401000041603800e0309000c0d414001d5054515515201c4042c1d030600034001c00942400d808408100421901041d0a60390070054808443d00d501d50741c24140e52000d58800480040e4441d0f2040c18004040c44040c000d002e200400c044682d51060f617901c4148004d0070110054000c2d039405100704070f078040c455080d04400c283d0700d180799840e000c10000c0480c0402c507130241c003504000171101c2e07a40483c12b031070100c580488a61081d2403911403d21660f400000c07a000e40020f01d0302207481c204884080341102d9500d4000300145025152010f0444c44000004003c9903144900000d0920540a0f4003e19101e00c0c030701d03207e0688031603159030040d000d55130f000b030401c0c406d0b0000070800ca6419049800a000304407032402061a440e0540301054045054041c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 809352517 1106 809351411 809351449
    0xf0403260f09060d020409060806091c03090302030d0c021e0307080301060810030614060a08010513140f0105100302030d080c030a0207170a0804050601061814 70
    0x4050b210700540104401c0c50528030b214001c0407a8400d40c089030026884010400018005000700342c2c0c4860450083c051244100f400c810307030008085251014103580d6403e00050500c20401e031110f8140800040000b800381180196982c48096030f50302501c114400d60001c100d0002c0195440715038000141c0d82142d00300386003a25664401843c181a00541e01000008510907004011480340c0c40d038041109070409005000601456400801c031680c142401c2c03005002f40b4611810b83c0d1074103c3c60700d85401100c4c04a150500000300c8080e0055800c0c1030510200c0e030889518501100d10843c100d80b00c075480000181d0b4211021a0302e503500310000e00c000b0301382036420380007071480301e11a0700030755009140c030746090f82c0507045000c0b0b41001400c0c21040204200c0208040c2e8050900340c14020060b1041a28109002c0c803140100a03504000704210041354440740708100700003601d14 = true := by decide +kernel

theorem cover : BRFrame.Cov 809172661 809352517 := by
  have h0 := BRFrame.cov_init 809172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 809172661 ≤ n) (h2 : n < 809352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
