-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1604
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:48:55.721935+00:00
-- url     : https://prove2.me/submissions/040378da-a80c-44f2-a18a-da92f0185c4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 288309352 ≤ n < 288489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 288310602 1250 288309352 288309361
    0x50d0f230d0b180f2805010608090f430305011505090a0905011404030f0e12031b2a0901050405040c0b09030709050421081303030b040e060f090d02060609 68
    0x2c244d41681c400d2841004411444403001c1507a550380303201d1000510180c0c1e0b90700505c000c5030043e0155412406060081140001040c002076480f5210b1000100800e0b02c158120208012447c490b80d03000e0802c032121038400604952040c052066100554846d0300300500c071942980105480000d1b5040608884e03d10780e50300c603041000d0060000304403015944c442c40c13044034044e0020b001d40514440e6481003103602401c08001c01c170f5004038bc0030921401850718007203044080081107402050711102000c242142c0013016500786000401c0c0c484107107203a29005401e000003241c0030480d42904440c941c0c0c550762284180001c9400496005204850310801801a0040d105c09000c5418005044070185602c1e400c0703800c1a43c100350360440c0c0181015011400381e00c1c501c269500d0301d0b030103807070f1140807841c20020120604440e02d5001d01495501c1c1500692500c458100254188c0054220740352030510103139628541d001110304c1c2d4a01e00503c03012290541c40426a2401030f400140400002d454 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 288311852 1250 288310602 288310621
    0x50c0304051c02040504050a03030f15060305041a012913060c06020910030b010e010305060f060c12030705030417090f01030209060903100b100804050d0f230d0b18 72
    0x404010446880a51402e00b200507600d50045600c2031f4407c0f00035001412103441c014007943d0880c0008800a4100261701a10341c10100c0c50100702c0d085450042110303101ea01b07080e10b0004211950103081c111440001c1500b980e0101401c171012400207030986071501e1008c46200714000c01c1094616080f0490003048080c0c03060f02480051030142200500d005400800034254201d17184403140441e440342c1c81d038046036800c40010a450102800c040c0400d14000000800c500f0381d15030201e20441c030100300d0714420041040303160705200021121558a040c004800391107508100c07011070f41c1c030030808091034040382c0c04000e5540c004030142ca0400704200040054019400c514105500110140003a142d16601004507001e8894984d5001880304088001c0c0480c00c08039140550502c0905418400010f200050040c038046031442e140515940f215011a044003c480c1190305000d500c0003004001c40100006201a501d40c484c1041011418012b0045146017840c1c2403080c0c60803440041d25051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 288313102 1250 288311852 288311869
    0x7021801150504080a0b09071d0a0f02130312110102181c1a0a0207020612070e19050402031503070e010503150603210c100501090e030f030403230a02030a02010c050c030405 76
    0x1f0240702640c042d191a00340a0f0200031001001d040c480f04110f080c0101280c4511407160025250300c800c0d0724102c06c5c4165048203002c2440b000b041e84e26080e810032141842078004000d490700d054002d658032012045296030b003e403400e00480c07007002900c60503945010f100050301a0035500c488000306120b8444442403605400411007042079808003c00b40c0140e648030300401a0140d2211000749034241a02b00910300e1140200c020b0092180c0304a407038448040d030124600b12a411500541c1c1c0356100301c40b00049d46e4244034440d41500c40e812000c100702d844a00e6a50503180290704a600f80b00b2000c0c02c499070343c102a2001c81e05034111000d140c40c2810401080011103800440c003030b250100304131000749400200a46460790b5581d5500520103005030303004d81c4138000718041c0214107040000819008a21004d00020309224442540c180d040d206405903000c0501440380301600c8941c1400060344941c00b80c28034000552034408180340c61405142601c0c2c460b22860b00450400b400d0800340b03d401d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 288314352 1250 288313102 288313111
    0xa0f060b130e03030a050603010b1c110d030203030103142b0c051209040b19051912210212030109020c070f24140702130207021801150504080a0b 64
    0x18074808040300e02041c14080d2404045200c0b0046079a407400c2050b00301140c0015103d180320764113041c2c01c04c3e99aa40c030784200042c0070904020900044251070850244400d41841a410a90140c0120203064000c80a903040702c0c05040d01c0c08038801e0031590141c40e000c00380c0d11800000240c2050040180203103e600c4004d4030395081c0341c400190151941460203014039100c440800300020580100c0c1001e000700000f00d40195000d80d100c600c011191003a40741c0c83e024072806038403a504844030f9031440a14003030040c9a04140c002900d5a03606054071442181c0106040d4010341c520f070f00381c0d054400250054820502e024a608590170407900c44044e50095a840c0d1540c40781c010003180481240d8540c5000b00341e0803809940c03070002d080380e006146126032804d000380203848001c0e40e5010014400c90b0519541102c0010321142c040c0d461600900030154040c1d00049454070b440000000030b8210f074160780007a446481c20400e8084104c44500c124050241540c00030701914000039040d11065811 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 288315602 1250 288314352 288314359
    0x12020f031305010e0609011e1104050427121b02151803120405010206070f050a031104030503070303060e0a110904050a11210105010908030a080c16230a0f060b 70
    0xc000c1030313841146007600545010340345955038030f1881200302c413204882c48444d040c40d00c1448008a03c1040c180390740183d2082038041c544507002c5010b50301135990a10500c8941c0c5245000691003810300030010103c0c0040c24020520040f604500c1d9001c0021400740c0302e074002c0508010748032090307101d405070700021501440010000021480395805000e41d0b030808082c82c0300d10317407550710b018002490004c4c040c114600307000c4c1d484800103549500c2400c0700d48012203400c0100b003000c401c1d245040d8522071984041d00a004c0451264109079158000500700c9250410460b19600c3e0303410030104507a04210030074075000080040980c14202034009640c0034030a0380002a0001c0180080d0035150321568141036581c004c0003d45c0c1082c140a841d0034094a020300c6e00360402420294425601e20034507600906004005000440340c4103030741c088840c0b080300c4100103035607001545000d050755110048104070201d0320400200035804002200382e041500103030600804c7d0340c9603c0d000000c00c100e0300e1f840d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 288316852 1250 288315602 288315611
    0x1f0f050412030206040611040303020a121202040602030a0f050c0d11010b060301121e151e060f05030c09400f03021915020a03180803040312020f03130501 68
    0x2659052545072142050098000d8000392806280c00301c01c85848220703c03500c1240500041c40401d03170004216070041e5000e00030700c2d0302105001095900c4007000f8956000036000042c0842d8659010010708803010480d1200c00f169420070340e040c0c8a41c001c003a9007441c1c90780400d4401d07041900c07030709020241d0507400000142445940e0045400c940c0260010651451001202c10400543c0040000c140c0c04c00703080001208142d0362210a542c1a03031446491145d2108805a0854006031034004040d0654004000d2982c4e1503002101c80011845054400d00401d00114414189210081d220341a00c61014005100143c10320404580e8207aa0012070f1501030902039841c00040e0034400c84038091480701c2080221440c00074608504a11903120900c00e040ca0840029080c290445070764810820141c0c440b0031404003180244444550305820780c0b4103d19910511030450000d41c050341c045e0b80c4009141e00f801a6042c1603101d0b1480c1c2c20b10203582000060400981c00c0c10303100030340303104500105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 288318102 1250 288316852 288316859
    0x240a080c0d03182c07020a030503090c03010c080105120c0f0424060c0b0c0c0a02060c0f1006060807021f0504020d060e060907050102120702040b01090308030907050f1f0f0504 77
    0x44025800c1c3c0c000042004554006005290080d825802210311381c0d8000c1e0100e18040c00025101c081c0001d0082c00c1c0b100100124000c4c0d0010b200c92084042d000d0f000304641c81c0c003018000d02c1c0380d400f0310030b8500a103a80080d6810300709000c6210002564082c1054140c0806401448000c10500c40030044448500d02100400c041c24220b000041c0180e079074400c03240d54107041c40e250220010b002c00c4450202040202d0718070502180a283d255011101c1d0f07900c9036080c100050410880d0000041180203101c1121041d40701c903402132041d03a0165644611a0780d84002c243d9607000c2000c1d5001204540d9125803108100e01d800031680a0310103441d03248001c0844c3e80d00c00590340d402d2060070706600480100302100004100440013040301744018203040045544034203040c820690b001c0c1c0980d0300d07652003074502d0f4003445d0250002d580c0003003415a04c1c42c11003101a150040c1d1301a032031040222014100701c51600c1402e6001503904030204c00310b002c1404c64140e44041080588505105007440b000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 288319352 1250 288318102 288318137
    0x9091305070f090c0314010e070c1511180109060c0f0c05150d0c1803022704080d050108120a05031503030d090605010e09070e07031103240a080c0d03 66
    0x2802007400c203202003081c0d213484401406880b041d0042c00840c9602c0001002680c507500d07407942e0803e009040081d07000d462409d02c5642014030401a488c21400c0224034511100a0b0b002044138010010755000300b59109001100d20449600ca5070000445199004020031200e05481c1a003621440e48012015910320102c0e407a00804e40318840390283c04180e10041940034003404c070b40c01000d45085008003045124410079035146000280c002d00b46044096824400c00c4181032a041201c0381e0f1030914502840c040070b1507400240c0c9410820304050000801440001e203d0202c40354050840d414901c103c03504450319000105040b18078030f010140042c00362810b100806061400000204400956003080c01c1681d506078400014030882d00104003000c60086141c1040e60003006040032681c6605104030060304a080155803c2c01001051020040034528030380014104100381e51001c40031081000001c08151040000f1070f00101c82e0351485103082a02d40340254030ae4140780320081042040c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 288320602 1250 288319352 288319379
    0x31f060909110f040e0c0c2b031512020102190809190503030a0302160f030f110a0c0308070203210a08010501020c1f05120f09070f08101503020d0507060809030909130507 75
    0x2620380304c0c0c416003401030642107641902c0f069230740c1d542801e0090480003271440e141c3d28030910984c5d22481c0000040421684203120b85a690119481d5030a15401a42450541644012041c600c1030341d1303a50005031011240074a10b000ca54008010394102040181e05a010f54418140d02c0003005102c641500040c3d039003981130b00d10303c0c042d6a64106850200341e0240c1700400303490044034240d1000c0101800202d0010100046e07035030010300d03030362141c05030701c00729203040f1070240716500717448442418008510f40e04001c1c0c00d50340d03107680c3d03400441c0e40d0314801644c0300e105d505091a0010080907406103105000f406840505109241042c0b030004403900b003504611f02600d500042e0174050302400700c81e6408120300c0020300074241070200d0345494800328658a0a48190f5028120b44071680c014460340409003c1e0003c50b005800a08818402d181c443d841d0a4640a010007003040140460913084000056500c421030181c01c410b0b04e6160110300107050040c5d20021a85885004804100c40e100c07240c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 288321852 1250 288320602 288320623
    0xe06041206090b010906031106180915040507050319090305090d0f0501050610050a0e010207030804030303020705072903060d120c0b1303080c031f060909110f040e0c0c 74
    0x90025180301689085061220f060f8070005005040a10034000701c1c2c5d21280c51080d04400f142c030b0303a0381c90341000030146203005007500041d80103100720104980510011001e2003980002c69040010b6659505d013a2600c1c001a43c0c0d58a961144043c02c000038a2141e1140f540316000303050150808417180c7c0003844058010000b21024400c0d02d100c4010003c090255a401000c1114071814030f000001c4020154000e6140c0c3e0410048030083d6030045034000c4c4500b0001e0343d000314a0603545ea4503428054003030750012804072110304c00e0740000030381d640301d048810185264510040ca031801c400c0001c05050f07003014000b84d03481844801c2c07400c005986080c0008002d003a030789920a140105040200743d03c1002800310110701421020702e000a54070140043d0f005040c40712081c1c0302e4682800b00140000c5a058501900f81204004902680c00074a02d6049031040c040500419140c81401c4030107024008411003000c2c0c0600050259500304040c0981c0702c14441540303818196600c9101d494441d0410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 288323102 1250 288321852 288321863
    0x30f1407050c0601170c0d1703010f03031b11010c0302011112070f020102030403020703030f0c14010506040e0a020f0d020d120f0e0108061e0a0b04080f15070f0e060412 74
    0x5502c1521000900c81c150040504d0019401c1040c010038420307841c1c3d9a001c5031984544c0c040b41180c030400500b030034104185d42d01c40340455241d40c0c489000c11288042400300b5404540160209240d40b00381080e880400c1342c2c011103c8404103c008015030301085a400100d09554071010420801c840000c050400c03445d40720600c0c0400e00b00460054400c803104018401164010420480402d400240c0d41e0f088940c10315242c040c2c0c55100e070084502c400d03041001000807240114103207011105420403070241e07004417410400c0c80000c0f901d89070f0351000410025003282815415284c28500103503540c0845001515103aa42c42c80da6032441084a0300a07001c01c04102403e8541520301d90011600604400c2800e1203c043e050110005180002d59003d070311400103c20541c140035160700024000400d008000c035a159a00c64094946a20200c40107071014843d008041c00098101d440b80c030f010742c10b181c6030b00d44049003420ac12281c042c4180c5100b900720074108000a408031090f59400d54607401031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 288324352 1250 288323102 288323107
    0x20409050a090c0b040e0411011101050406090201080622150f080a0618150c030e0d0201050609091c05030919060c180807180e0d0f02010c020607050307030f140705 72
    0x510f0030600c000c1041d0402c480d40001031005101050a000c0381c4c40d082500a4280c1c2240c14158004031030301d00c0588030001c500d5082c803052104010300c542080440c0c0e8401d80312241540d85800078050000c1c8480719101d64900d440441d02003000d0b099101d00d1034004440b103104002e80d12040d0050381d4040960003503001e07601c0110200b007440600c0c41030599925032591302602600c15615a41c483e00d001000c0c03104200e0f83c641c1c0e8a400c5070b000354000c904141e02a800c2e40d0100c00f224001078024042146c20038018940c401c0002c03480d210100307681303110118140101800301c2c815881116241c10041c4584a0381c4103070052200015641782014820b01d100321400700302d5026a0070000c01c64000c1107080d46504a01250a004008004c180341d400e4130034007330700b001c0e40d201da1a040c0800303081c088403042c03a10700862010744080b40d8407480748100d40c03801e60001c0c0180b070703800c0800b2a40e070303c4215104400280280003094015209402082c0c0301041500c002c1548080c000c843c0180c2e160640d100800304200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 288325602 1250 288324352 288324371
    0xa200910150203030402010905090a09171e03060d0b040c0b0310080c01090513090201030b0607030807022505060309100e0d1106010b041a160b06010822021201020409050a 75
    0x110003504120764107880a0b60a60619500280500300d075400f03100d200300c5002c0006007224045a103e841641d0300202080c10b152201da20180751035100c0000c0740c01c03401c5c5010341080e040c010130044a002d44c10141000d0211060b0b51140c5054032805401180c8004a41c040022440c02d554045d601814000c01252202440c241625207002803080c0014180054400204407550740c030050740460113249180402c00c0a250b00c012030003030002071066588410042001000d040d4001c01c80c5229042c90340032a040d8102039400c0425450075200400c00424101030140821305180300a1608080500c0032941d0b08101803801d1001e44046900c0c214850748621104c00440f6813102c9070240410700003003d00500d50410303031b041036584281c0c0100c2480803940d01900100b05507000071100710710220300e07207004403403058a0601c503240f900355900c41c0060110b03000700f083c000804840180c028484e6014000408050b0b007402134501e0050308040c1d4655082c000080c4412041c019603118014401000418a42 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 288326852 1250 288325602 288325619
    0x62406190201020901030e0a1a0702030d02070f0201080c03010806040f142505060c03032e08060a0b180f04020307090c0503010510020f0717010612140c03010b030a200910 75
    0x150f91f1100130554044200580441c07080303904a400c440034085403540b140c1c0c0f0880280d2440c824174010050746403002401a00f840240801c00300300300d100740c1c1d40e108991034451001a4900080c0104251900007401140c005089882034900c040e00c00d19040c80c60f00300c4600e20340e04003084000d41008110000318401518041080311700060134045030b07a00c0c1403002c0080890350700c0c000100815900341c5245040300b12500f11007000003040300746120480141d615050070588030001524a9011281420001d103814502803000d88038160824a00c08020f40d20a0b503c1c6802c00c00141c0306070b07014000c1840103d0281002c3c090000b055030b468482035030b81e51500c01888440722410805404540003540d0007803150b10007048000c211000614501160440941124010805c80d40701c2640340e0000c5200c102000f0140c068a202d450404c025a00c4c40701b800e0060500b0381c1c028400039981604031494400010384104600008a648860103021445516001c100840010384150418041c0c015080040301c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 288328102 1250 288326852 288326861
    0xe0603060f0c0901140d050c0a0f051204020105091519081003020d03080910021216030b0310090f020a080c090702070b1606140117070806240619020102090103 70
    0x1038512101d000d4a140c26541d500260140c0b50381d0034104188075400b035007803408100603915503c0c0800d008002d02d090061041049500105003440411590302c042c08032103018006071070600068448100310799803150300446007507004101140e8454184115900c0c43c803810300c045d0103040c0100e070b0000c10b01c069200c40030b04200320081440002c550f41c1c40d01800141c991481000e18503606080101b840e0b215208454200060402c4080001d0300c0400c40703c094008680b2100d01600000c0e05030303104110074980481c1a240300360341607609980700009404a40c00d0550249441900540700308070241003980c0015100840341c0d01c501240d80c802410b80310149064082c154029007580018032461340b500c1007080080c0690f01070700d070240b01e403625201c040c401150844025044081444409507031180e4a04658400039420703112030f849030b0040800e0340302c8001000c60081001d80e030b443c203484681007612001142c1c400c00d000d40101040c055450090000e10880100c1c1000c1c0e0009a19a101e0800040444 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 288329352 1250 288328102 288328111
    0x60504060e0627060f0d051009020309070b0a0e061210290702010915020a0c0f0e06210d030506041104060c060e010b03030409020301080d0801030804060e0d0209010e060306 76
    0x500b42003004680300d00010840d001054400345621200f4801400060214000c2c00c1d02c100d0b00341d00008100e0015800c42d0700c11441551140c20501207079885034010003c80c081100d80e982141e00c441014400c9071110300244c91666500c1c40e1418440048001003030300d07508440c48d1524540421020302c00101c4008020001420190b840c000280c80511041c0102400040508642c07140020b02d0030156440340356200c01500c1140d004070001000050000d40d111640074003551400441500820003000c07a501403811030340f04000c1035060781c69000070041314969a6190440e00340b0a0f013074030000303000184414100000c1580b8001200d20b80750040c0415159010685400e040c0c2c03c110520100d604503070b080b00145c1c0c06c0b1200050000d6801c81d500d006281000350503906104c00701e00001c140c08981c000318160f620380c40960354110845402601c09080c00e0000411001082c0000c0c0845813051059424403000140034201910760b6802203402002d080c1c2002040c0885401000107a0504000141e0070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 288330602 1250 288329352 288329359
    0x1e05070c0302030409091a190e0601050a1806081e010b0f0114070c050909251410030605220c08071d04110c1e060c1918060504060e 58
    0x28800c180d6070082d01c903c80d81c0641401e440d50b40c04040309004c8240c06035008211805501601070500b4050f9203410f0190314101082e440c09c000b82c4802c2d603017012400c81d0403074201502c2c4804050138031441c08100321040200c1580030f80c0d206000140103604225050b40d44011040480314603006081c11406d4640550405002d00346850040c401643e201d00422a0840b6507a00c0e0b80e101d500e00c1c0b40c03104013261305034069540100d01c041400382c06940070400704031021070703826840189501c0341217150490342c56108141440c04003610840140c1800b120301108280d207031800207a8039455900207080c049a582c9503000c801130b030714482c4891072220300c907000045823703003445592460200c00040c07804442c8940010504100304504065846a4010810001c1d45981c05074680b04500e14195891500c00c1c03180c0c11043c00700b00e800c1401e00c001300b5440d002e000c2203880c90b4907010440c4403241319180103a01741d40400550401c0e02e9000411407007480c020340102c0d034400d5038079490480d006011079200c8416034070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 288331852 1250 288330602 288330617
    0xc06020712030206010b030606070c2d0e04080c07171c1d0111010e01050a05040b01062a140d0c0c0f060504230d0809090106030e0a140c03011e0507 65
    0x10940011300c0504442d15800d14036900ea565a01140d00c500960400919410100e2004a00c54176002d03000c9802c07a01c6504003000e02c0101c448280c503070300c03241d204090100f003440c0c020501050348240100102c4104c4c07000c480000d692410009403902260700340000b80c2d00601007010720b42591400c4c002c1032042900d050122401050420b0800c4000800c009060000c01041c00a441d402074024000b105078200080095250082201000d0316086604940024001c80041902c070301684c03424002244481d041e07001a01c601019034002d42404505440301060945105480034040003c99000d401d1669101020407492600506040040c0c00948030345e4108401409039990103015070b8101c8401e0f0002e801c1c1d5803c4160251020b000c10341070a5000000d9070030389001e0001c0703c401014902c03019660f5220310307079a50340304508580300540000150340141c2d000d0b90102e00142024500043c00c4010344d42c03050422030000303084603811384404014401b5076810700d40340c40343c80c49525885142810841e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 288333102 1250 288331852 288331889
    0x4060305100f11210702010f240611030d0f09080a0f02070503010c020c04020f04082b0207031a060a0504051017061e0903070f0c0503011503080306060904020c0a0c060207 75
    0x5022002107000f401c000d513040c0d00003546040c402d4010741d030303403040d00141000907015030380d12041e200c00465013482413503005002c0054900c1c816010400355803d4000a10b06000081c0051009480000c241070011500c0c0e9000402140003800144041a031b0707500c031002d10034072902020341024a01d50000c2d1003079140103c00c0c1d501c650041010b1800480407580180e4690030403a414200380210f800611081c401c0100b0404100c0044d108034201c0c0c200300d1403010b51800304290480c0e540700240030043c40080344003c80c000009092500035000f00005010350391b0991244086001c440341268001d00c036540a40c0b0800801007076440d581d0801850b203024050519001c001c0f240045405d5854100308450f000001e410181e09101399200b5070b034440154107154040d0b0801e296451842e000d000c0c03007540307000345206141ea48941080304882d4400d45844c150394030481044110b80010071001e411540800c00d40b4440c900602c20701c24264072038a0303034629990030503030000d180ac1c0c282c0c1c04c02161040c07007400c5c08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 288334352 1250 288333102 288333127
    0x13090f0b1c06061d04020306010e07050f0a0c06111c020c0c06071a01080304030c0b07050c0928050106031407050d090201110303071e0905010c060b04060305100f11 72
    0x110360580d640407210080380607034a00207008100f1a03000a10140303440c4801602ca075103244600780131768002c808650381f990b210b11030720003107100945040c070108004200d2560b03032000c2100909880031482c14010403043e00c80d26604240d40c4110910160307032034001030700508081c0c05503030f0440410f071070702046003072131040c5001c03e03901c074038a03002e007480f503800400c1407000c120101004114145c801500340d209560364034041550380c1c005000844900d0395058011810700004000d49650300d421000500418907003205000d80000c0180071003241205035809040701703a000d80166141e200050900103115854214010111070703000c440c54030340805500c00d001013964804207441101d00125000100c2c0b003140d01c0143d584104558842119001c040200a1002e402c03442280d509581d2400000b080b000c42d510440d5490214003469000c80c0224030a0030201d1541d42c0f20701218400a4000183c107522a2522172514080f92008121680c503010b0200e6603140902880d4100c0a00d00200c500704074842044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 288335602 1250 288334352 288334369
    0x20a1a1b0c130c08061008060427050a152306030102041a090f0105040602070306020d110c0a0521040e0702120406020703110d050d0809070b13090f0b 66
    0x111460014185404504001403107007a80040004000070b440e855200d0034078010300009014140460103010001c0d009044c40e14045c20b40c1e030001ea554418650b07402e0708010040a0111001001c1c002000c2c0b014490084110300d0020070703000f60001c4c40b68071854038003842c004406a045040070390814640c2c3e070070b641c090b0344d01042054403000310303503103942e9440046030080c081d42c4e220078100945051184a000710b114010070348400c0686010074400c0040c0010f5980d84542e01ca42c20060380054401c00c041401a8090b20407200100800b044034041c10100078010f42090106002c19041200314100b0003004114000481458550000c921080000d03c0000e80c0203600c10460f0f028010030015664510902c01c6a1280403041c0b481070b15140c84600003540c40d0390600044804e183c10081001462806500181e901c561103002451015120390007251420001b0300017183e46d11450f40042040c1c00044050000d6640c5105083d550f103280c803030702d6030a84000c030b41c00081c1c0c6441d011a841c6507444e0942d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 288336852 1250 288335602 288335617
    0x180105010f051f020a06090c17120316110d02011410051806010507020a090606030b010507020d061112040605190b01020705040c05040b07061d160501080c0f0307020703020a1a 77
    0x3e09100d0302d9241000381d0030b041d01000b0082c2481c0c500090407080081d011000c0d000c3d00c1d64001302c0289640ca550181c1d41d0b45400200002e107151080c40055115540020f840010303048602e001001e001e603040381585003626081c03000c00980d4488120b10ba15040030001036074800d40701400d04000c5032600001c250f1451807401503581d90175070440028850b9014004035150207901a00384003071142c0d281c0c2628000c00c078900a01c00002d042c072040041c158441c800751185103070000c1641904600d541d0b1107000400b04e8a08860001c0414800c000041968a50647c4564010080858246012060500b42e000c1d0303021003050840c40c1c04100c3c10584d070b00252031829100140c03000641c18520500580d06405154404d030700c1c003c0b000130803504108103500b0440801407182c11042c1010644040c1e640c0341d62680c904032107850303040c05042083d584a004420b0308224003012003840c05144120049240d4000c44d1030001503031050000b002141010081031004100794013010880d4104550315016a00c14a80c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 288338102 1250 288336852 288336889
    0x605030408070309051210060801020406050313050a020303122a07172203110a0503030f0307120c02160b180405060303090301060305161a03060409030215180105010f05 74
    0x80d5400c205401007444130080e100043c400000d420180c0c00c41c5035211050400c480c0032905004001a4140050003074809403509600c0316030455907003890201251103005010b03550340c49421000405a24188018403c2d200b00d44516072162a140d40c51402048402007100e40880f003000c9840340e01216030080ea90419440608400f43e01c10026881e2141d01508012408031031851199014007142c0c03025000803288200000304614940c80100003000c1c405101e0203800d500704001030401020f9900042d58000d1050030035403002003100b148981114400d148010150b40121101a201d03044003040c00010b00324030812918000002020303200110006402a02468482d80130030b43d0b940e400d002350b40208102030000c001440d0340f410b210340d5a80c4510800380305007100c000080b0b03010050707040700d001a0f542c0321403440c03039a00c078102400020200194103408500440d2700e201c01c1040340b03102d018012a0f40c02203000708640c100124a08584041c2d112194006525400b0050358a40b11000c108040500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 288339352 1250 288338102 288338107
    0x615031e061e0f05060405040f080a090b0f0301061704050d0c05031b0c1002030f04030b0a0b0909010204060e0a0f031b08061314010e070e09030d020c01020c160605030408 75
    0x28903211000e4030080b20701c0c014252003110650440c4805a105014603280814244980d4462200340405c0700e500380c1d005041a16024421130115581d403004020043d0350740b400ca2019035070340ea02440d45421640c80324403001c1c0f0000040046640c0b02886041058a250300c02034103090550710035980b01840000a01441241205002402001c1c002d0b00e90f103585a0f6040466045210001a00d41c01c8c40c00500d88900030000604169a1001080d250402650345900e454035003940c5580b42c460b50010304091505440f208039400301d403158007005000c1c50a15001603291820090064181e0b4410341405006010809040040600321000002120307040000030b00b00701683d801d250540c207030540010360107101b01da0500c501307541e0341240c0c01e83c040e001d4032807440060820140542604c21081a11034a42d208440c18481c2812000040d5000fa4825040741c0c81c152a61008109a800c06010b400f0940d41c0400d42d003020305414003c0c9a514100720011aa041e810000003500d0341c00003410140082c50301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 288340602 1250 288339352 288339413
    0x815150103110f030915010f0311130903080105030709020f0d0b011407050706080c04151d0a060206010f0e04021305070c02042a020706021218060f0403061503 70
    0x39911042c40c5050324050550b4804598103000910b0380142d540031003604c24404a040200d10710070b595416038001c2c01c581c0000d5461901d50341444400c400400740c0c080d00c80c601d0904108034a10402e41e03c1842921941c00030741c5054201414001d04d9400155168010070611000303003640012500b4a400c20140024200344400040754100b181c6009078044013030014000c001d22200040420440f00107680d98006a502c01c1303901c4456008620440035000c0382e1103002810540514040c006600c4031139814006550404009050090154400000368014a0060018481d00843c5401515100d141c260082c2015030200e5103864880201641069980d000709100c00d2045030321200d140e40050052200c505094a00e00c0807102e11a1076040c45441808880706050001c06d03800c00f116002c7d00034065540064052004552050007188610820303140340c0d004680d43c10019103500b1426088a5444034158a4100d040300c508032150800007030300790010800100e8a1962020301d03e50301c408001038008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 288341852 1250 288340602 288340607
    0x40e160809120d0f021b010605040207030519020f1e0f0a0b01031509050d0503150d02030613080403050304060806100e0603072a080c0106050906030a060e100905030403060608151501 80
    0x11061350442203400020100343c01e82d42c0500250007008a0320080100a50743c5040104030700c2144d40041c08118203200c101242d42c80b90000510740811401600c0f0201400d0510606101c85071030681c030a100c800d003411401c01c10800c00003100704058002004031405036118481c044005204c020808a00c0f10580200814590001c494440e4048112110340c0240c00c0040e14a0f0801c0350680c4070340c411106210711a181c1845e44810030764000d0060050b81d01c074141c0c07401c862400510165410f00f4100030002c001107007040100010a141e42d034950260810404010341c1504900745d0608009030406407619950303c07202101d4000d1101d0034898018070b220203a180343c0d0000e4140303518168040c150f5080500034010018054040802d008000240e00c3d0003c00c82ca4600544110f40c040d071101070440001030442d40003c4868500c1400c44500c1d001c000c5900d0265034101d102128150008030b020000c0101e1406007102070403c040203440748404c608100915044001c040c4503150205c0c016840442c2d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 288343102 1250 288341852 288341861
    0x403081b010c02010209181b03130206040f030201141216120e1005090706080a050916080a062a030908040506120610020a0f03051e040e160809120d 65
    0x4240c50007400981c00e6030718064000e403c07848055004021040c0c2000809040c080c0441c4540da03481883d50180484481807509034000600a0714039010805211004d6035a504c00342004000300034050300b081d0700f1880010704100c4600041c1a07417040c244001404109000d80c0a5400301114066800f052015001102e0791210300721104111494840b01152105c404104070a0221045009101d00c0d200c42c440140d403400701d072207040002070001010032950803003134010030303041404601140c401a0800d080316050050561204280303600c000c40740b00802516000340525900c107094088900c05000c81000e00c03081d1200007000806540c0e02c0c0f80d4041000010550f80548805480d540c1c0300c8410b2841d8101c0d600040c0c861502c1002c011503080c0c9003e10010b0030801c4241d100c000c41903404030507078003900e140c0c1298040c00d01c0e25840c0c1d0032880250486101810040c041d04c4140c070709a04180481c403171903545540e45c8008003d04181045909080080d40442440d002d0b02c3c510390b102002c012440c02003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 288344352 1250 288343102 288343147
    0x1005130602030a020a0305010f12031b081204050f07060e0d0311010c0f030608030306060a05130b0a170f010b03011a090306010801150b0a0801210204050a0e190206040308 75
    0x441c07021041c00314810f070550250095101e036032401c00050340c03500814820400980b241c410845101c42c044d9000034407907511100d02c2a4101c1d45800c1d07882c925503420343c0a4100c01c1105100e100e5102c100004e20508100e01c081000305d20b4064441c45081c03450050103940b018044030b01540410008904140c4680c1c0319520750140c9070000c01c402000320340001d160f4880c201681c07001a061160100360304c0c1000c41200d001d10001003030f2a150a980b18000c2d00e4a40013002082d048105c49040010900c11040090090240b0b0b6a90030703000c004200030820700388401500a03650041ea120041c48552188000c8034151089202200c00269000e20650b04620490100c030fa0540611000050071401c150070441c1044049014850b4003502d03100c00c00440e001c1c500c103500001d9201e0f001000ba01c0c00c01343c0c1d05c40c00064180c0e481c00c81c2d03054940204040c0c41090f070b400c452aa0313640116201d222014041c0b01e2801d206000203480c5052541c0008849000300d00001d05080000034400141e5150098608100c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 288345602 1250 288344352 288344363
    0x50702100e010c0f0506060f09010e010509041a0a23090a020108090705040e0c041b0804080d0b03190209010b04060c0206030709030b040b01090f06080334080c01060b07020102100513 80
    0x81801d00c5ca80281c4541b000c5c2e0700b00380180b10b41d6044035901d107001070151741640c0718440c0620035070707180c0420031289007405003054030611400e5a41c03460443d40c2000452094055510200e003204113014201c0086d90f1780151164408003d205004c0d8061001c00c03120041e540918010a058071035100a41c28004154400355015280c06003500c5082400314148a045204980410000b00c4051040880d060240f403160000356080c800680011005009481052549880003030344d01c80d84d601103032412400c0054445d41c02c1e80c003d1000c04529200782e4a50161031a004114141881c7c6800681003502c00c00d0000c0c89000044002104203100d219030b0402560171034211052400d150170404d46900d000e00540d01e2035410025400040300b101d0040380100d89103607000f113107814080c41003214000b01010341380030340406545a9055144404048201c402d01030010766aa50011421490031511550702c05c050212041c80650003503070300410081c1071001c04500100c1c0700d5680e48080c0040b85080a4000c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 288346852 1250 288345602 288345623
    0x50a0b0307031401050702010905150916080c040b01051908090a02090705070b0109060e0a0e10330b0708070510090602090f030a0c290a0e0a06050702100e010c 70
    0x14000c0f408202481c103a4010002c005c40c0d11640822030070f855a2001c05845584900b01d4000410714a8618580c015009410b80c2e49406004008001242e4140c2c0540c495600280d44030f8034078a041d12402001c0b00003420b2013451f140710303201c2001c0e81d038509084c034409010034000002c140a1060180007511540202491545d28100030040d009420909055a140040d4030000c51003604912948080c1d0f011500c1e04006503031040b4410028140004904190b409420554000103103140229610210324161142113118800681584d101000400303081e1004111402c101c02e00181c0304442d249a04a55240d50352405810f07c039181540f0b440710100e0040c5044014005c1c402c03136034040d200c500c804942410355001e040040594422021710f0280c1886a5060200410251014209181c0189610400440169103038405203038004e80e583e01c02158103039440c000c040c0307410203a0401424203400e00ea8103004041d000300b5009600d030071801060103c942180b00d001e81c001c18110400e650f20948030705 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 288348102 1250 288346852 288346859
    0xe120a0509300d0206060f040f05040c090f050c030106050714030a03140a050f07110c03030705030a0201060b1e0f0d180203120f1608040f0f14010f02060a050a0b0307 73
    0x35228541c012500202ea0941c002c04401c1002c5104a0920403a41c02003280d51500c408000121580d2141198415600d83d201c0040540d0790050501c228010403e40801c2894811304405442d440700c0b40b20121072078901003007a6880340c102030301d055500510303007152a4400351601ea10842101401c1c50b01c03500c000701d0140b02d107a9240d0400010250102698031258603a0054102695003d03620f07840c0741c2080100240c0303001c0c4940440854540c0c2e482c200d90251251341e01190031071303108180a07140d90f00002542107010380c09000e000b0080007591251454460046074a1489081d40720a81501410004551400024507425a855103080203400c0140c031140d98041c880c0d044002a080b40603000703100b114590000c1440540b10b120119882803860f03e0032402c450030402e0402e00d01220310741c00a00010400012a8070101e02034603204c0c016115060038035990b003048140c032601c80f41c1001002891b801c1007540c08188260824000100400c1a845401960003d007038040c1d10560948902400017 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 288349352 1250 288348102 288348139
    0x10e0a0c140301330b0903030d150906170f0c030a1202101a150a05070f021309030503071403130b0a0905010c021b1905100c020d0b09100e120a0509 65
    0xe4000c44c2140610303c005a514651030815001c4c0c070b030050380d0507001405402d124801c141c000143d541ca44040071011035031206004021641c01d600000801c03801e03220410a00b079002c0002c1c04646045500605401010400207a0b4074006207200411124108840e030b4411402000000041115004248000c0d48080c55150380c140c004035907184600040103032060003866000c11680400751546e242450400c3e40d88500c24810f004200481e002200740d007102c0c1300450144102e002d081d01c01d0350b5840d5070381401c2d18000c01100c4c401620150070300e000c005103c1c040a15400c1282500e610150098169644294820080489800c041d00035420060b17200903095010a9020301e018604181ca0322000d903410a002860300d810400b58451500300c44184070354130b000f40780e40144002520b041d124109099010074080f0103400d0b000c44502d0094ad048c8074404e8801d0104000224018204000c030200405403642d8036a068082c1051400e40042c0401209100304100c41e41400042c100355003190b51405807 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 288350602 1250 288349352 288349421
    0x13032d0f03031a01021002070809130618021c05061807020607020d020705031002161e020405061c170403020607050c0f010c12030c09170609010e0a0c140301 69
    0x701d002a02d88511064403880824016400910690040c0054103203c42d5000c0254040700c81642c0d042e40901070411300340c0c1c40b0214040030b01c62880021503503600c0c21501e007001070601f0107800142d9005001d40c2e01c004111a0f803079485c400c081c490206036170300d600000c104202c1d0103065018182480310704000322140c0005a090040c2442d90840305402c3c480c400407601e600050003170b541e2640001c0d1100381804000d801408441e08041c00900041c0c909a44082c610620700601440b0310386410908825440d040c42415072010099880103000407040c0d02001030b030501110b00a0106003689020903481d12050250b901540e8050301c40347e65240c581c2826550b580509411910030b004000040071503522469085284583c02103650700080c1e8020019005010300c3d070740d08001c2026000002600404042010b0a10a13414014180d01e080c081003542c2590131a41300d9203a40c0c1e002d4000d00d8001007110021404407000810050031072003038980001d003d04250000f450304800d02d5410f8241d00c8821910 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 288351852 1250 288350602 288350633
    0x1020a0807110c01080606070615030f02091005060904050702190c090c021c0522121704050d02040b03250806010e040b01060804050a060c0f080603010213032d 70
    0x2074800d440380c000c0507a1a680c0003640000f80c0007904034004124982040c602505615204400203c0c040624582c0740e080340748294425140c40300122042c40a500340ba448450304190b10469004030a810000891000d1040c016564042c598440001d4042e610078132a030b1000c1000004041c200c3c1c00d5a0030001c544005074011004260710b80408020301c1070001402d40e00c1c48440060740485005001c0c0251025041450418525070303041207140e550f401c0c43d0075180b000d8410181d010001000c2424030494441d130a09a008144070b00f00024012039442c0b100510780d441d41164045401c103a08004641082d03580c0f00c00d62107040c003c1c42c02c003100160500080060300d00c408211685680d8a0795004252070042c2e0b0090030a565507001886a02d02c10900160702c11b0060044603140c1d01c0d641d50b0300c402c41d5440c0b0310320800070701c1e84081480f90903070154106030000d004500035410880710819030446007101d44070090000240401c41801440c01e20000700000964202c0404031148505150503a003440b0003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 288353102 1250 288351852 288351857
    0x503040f050c2d0306090a081e120108012910030204030602030c0c061e010e07020a351908040c030501060306060510030504030f0509030f0f0a060b0a061d0a0801020a0807 75
    0x3c0800b51401d0002c0c81a128081d080000c00b158180c40e03ca4003c0c0d64018500022038101070b940e0700345005802d00050050442d00300c1101e1841d0b24080242d400c40d00b9014000f44e2801c0120b00000c0b14030400c028103204150f0403103042200340c0320120141c009102d55400102018004030030003100d640070310050081651000155007a550310030b0040f05910910042c0188001700c86001032200041015070b140d170141e000e0044454685440e1500c8065071840c051080c5680200b00544000000c01c0c001104406041c0d2191401e119a550380c01107910303101c00603941009440d400003003e2000a880c08002150020020040281c40f414130304041e14260050078050850018100320440c4248039940c40f0f107415035941c111070465020115825070003480d1046c0d162207200b4204504c81010321242d0701d107010080080c85416814540130042e20f40490715640b140070b03da4402c01000b6045191881ca01e80c1c520340303028400700c0fa01d0005203119035a0b008408650b1020800603025900900064003906154 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 288354352 1250 288353102 288353179
    0xb03012c0f0604050f240c0d06030209100f05030a02030318041116030306050105071e1104020a17060603102112030b040b0402090114091201111201060801060503040f050c 75
    0xf1507811111050340200d4441b83c100e4000303030076208548094200c8200c07044000c01c0c00e543e2600014141c6130305a90004e582c1742100340c05c101c5014043c8840000307080a80184c07503403c2032500020388a000f440a004101c4c1c000701c0754502c0c665203d900c100c1d002c0340c00400030b544500210f41e480c103001c90840000c501203458075502040d030750b02440540364850781c400321100b402c2d0078904007028507503d1060300300c0d01e10b011100b80c08020303501c130300281c0010942c41e40d50b8072114441c00c1d0b41d400e07040740141c04a40543e8081003445205086180030b41e058a072040346d680038121113180c030305003030716036500300a464004050201489142e0581121030b069000b100d0030f10196980004000803840f82030090307404517901c50b0148447d040110701600c201c6800034008824641d00c01426420742e5280d402041d000c42c80081c103840c0000903030058034050102450000899810002d0180807440040d201508025150440100b0040d080107441203660002d4035020603044040c0c01c071403082a40c900310100f0000d04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 288355602 1250 288354352 288354373
    0x20a0c0e01120807020406030c080c0406050409211b030806090a060506030a090c0308070804031b0819060906150602010609050f0a091502030705030402040b03012c0f0604050f 77
    0x10318008906851514000c1e945569556a407901c00764004c00e01280c110fa02c071500000816540b4800d8401064110058486e010071401004201c40c038540146100c0c1d49056000d40100e06100031002c88680b121100072905650500103450004110400340d03182c0c0340303503101d075810968000740341801400c06640c103440740c0c4c40705032454054a510f401201d8001c0c0b41800050029405034000280081c011213000d02c20549a4964a038147c0c080d010554000c100010f003041001191034103102c844078645010500c05007007124a540b15802040b1000d07082014418041c2400041d80c4100e03000d5501007010000480490b840034000e4015101c1e12015510300840000c0015043c001c2510400590382c0580a559849407440d0003010b130003806540012000002d07002c1c080207071000f18003d52984c0c50782038403481c1c80d2040000b13503142c942c0c170310f8041e904105004091205034015074809050b6584200110100714010b1480d018644040e25114440c0405001c1400400b040343d0f140c401402007964071080c070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 288356852 1250 288355602 288355619
    0x4060801060f02150c041d04030216030b0406021c0c0305060108060301020a02122805040f210f0201052a011506081902040b03010306020c010f05090d0c0c05060703020a0c 75
    0x2802d0002c0005070300304181d1031080441149a469000240102903800c3c55282d0040040040b006003041d8414001101404107040d010448524205825a4004c420a0951b500c1444041c40640300825480d00820036000002185d0648040100c1c0c1600401c007440c08510000c01514041d16820301141c402da000c01d80da0705040c000c4034000c0110750020000386010510441c010b6000c2c0d0b240e4003502c2425000c101412580200050104130960780d080c0c2c82c0e50030400300c0603118a107644111900d07a89948040c10443d500b503803648600e50402d005480c5031006000686080c412100c01c0c40404420700b40d000300e80408010085a6141e080000700141d1b116030a80c000700018030f004800124140d5000a5484080070750b00683c1d941e2860005070030503035207240c8111a40c01c00e8004584003a0041420282c0440c01d20a240981c1784440080c4020301b09280110b48441e0300c3d4000104104c810300c001c1c000d0044145200c3c00a0201805a03a65490345040003503c420b100c410446109001b990300203582c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 288358102 1250 288356852 288356867
    0x50901020a11011b1407020a060906020609030406140304030c0203060112051e070b030c1215030f1204050607020a051203130602061009240609050301290906030708010906020406080106 81
    0x80088001c0710070040e00360381c103607001722940c115030900c8081001300b1001619150207210007442e054440740d00c6075050040c0a0b00f07200004044015650080c441046560b40c07107951500e8424206032000d940c1e07251070800315145540c140700690541f0800d000000d044030401402003c1e03500490640d55030707184581000f03100c4940ba100454850340150003c2c4040b1855800075a0840301400000781341c11a010500c0d00c2104048640c0080c0c00b104500945030750a00344801c018001501001e0701c00412842c40400050042e8010180110808070f008402c6458500c0c290002d0000107180d0304520580205d4159a45c0c4012030011361036200f0480010b10600000700780d8050111403460703401079410b04500d44010601c1c00e00300702200c0080c10944400250b007603c80006407405907203012019041a05242c00d48030640c8044080422002421271f1038442c4c09900441c801d000c0701c2c0a00d141e10745800003803030040e8a4109001551030b0034034020410040780d0080040750200c1e20f421509030390302c000c1030314100c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 288359352 1250 288358102 288358121
    0x609010612051506011106070807270e0c07020d0b0612070305060601050310120c030210020309060d0c0e0310020306150f0d0903030e03123103030905010609050901020a1101 76
    0x680c801ea483c0c1012209000e80c003035100d041031628020b5065600ca402d480c0035007da800b0070200d000300003031000d5180d1005907807543d03001c0c50740d103800c8554014040c440b10100610404007080b8590b00130540c440101c00469151a80040294240d10a0b50805c80b44000081c1d90702d600c00c0c0c03444a4403190808012802d9070440360040b026000a03902c0b0001035403d5840241881d00c800c03c0c100e0003150200300000e0280d5098001c002c00c110302d50035481440300b03241454410f203043d07500500500e10343d9074a06080340d44001c0851404641d2080d070303800c01c0e03070010f007806a40d5a141c0074000100083c809558040c6101d454103c0e514036490344e070b80f4460429880703035001c400c807a0201048603488201032600003000c2d541c0b2070b1400040f0a05e5940340386045810500808141e28808400c0c44000807004100c1c248a1007007290580015120400708111140b1000b4000d0034192501d81040a00a0a5201c10700920720903a0911243c039045140074000d5005040c01c0003c151400031848043c00305105e5060302 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 288360602 1250 288359352 288359363
    0x110d080916060c06020913020a021c023004082e0507050a05280c0203010501080d0f140f070809010f03090b1b1b07080d08040c150c0c03050609010612 66
    0x303420300c0c0d480301c4c006503111200c250340040140b10004000c0320b1071b10080c04040c0d03850b40076101c01c10801040c1d25492010081d200e04540c0440d0b903a104045440050344000b4024040c200b00c2c0891140409280717004590111906000e20000c0c08850300399510250313220041c01c2d80d9000c0d004414500d50084600c1540d803500021014000d40182900820042520078a080860000091614503920704044141072000010340036840b80001c5003000d02505014207001c401415560302c020900030700014101400c4c0f01040301d0b080f0a40d980380520402c0f2205e1540350b4200f2503480780c40d0300300311a50740d1007007801d140010715540814450303078460b20401540c03d60094626520b070301c030310700100a90100c00c102004240410884800c0c000328401d0303020141c540e4140600481840c08008500708880c4c80000805d0001580030030000684031441002506c2c003203c015145009031820480e02c0006108008010104014000c0180800025a03501c03c0080100900145445540c0040b108d2071401c4c00808 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 288361852 1250 288360602 288360617
    0x618030b19020d0f0b120c06070204150f141314010303121806060e0108030711010302030414030324040204060905060c190c03020306061804020d03110d08091606 71
    0x803540c2041e0400c1181500001500f0000d40c0341c42072045443d070120b003101c2c0f503503514001c21141c10103800400c03200003140054403090118102140031442540c000030b00c0f540c0d48007083c0c2420060901084081c0c0b07801c0d59504401078540f482801c0e005070040b4058800d4012541c40101c000e51409105d0701e0049038040d101059203160b07025680e413500080740040c1180c03a44070000a02040c12010b01d01300b40280307804608545000d0bd220220030040e0401e02050f0410407015005c0f40c0680d0008e2590340f828600180d42303039502d0408941d040000441190702d40000024051034880b46a86c0c2290080440400300c13201d90b1201c1040201d1295108034004500409010045032401c4009009401d03a00390540d00f5513842c960b403004001255042c11200008100c034140f01754203007086481c4e40603805031350078080300b4401c40c50341c400000000e1009100d404510040010948520120901c090442044410340300083c1e2015050b10750445010010380f00e50070f045000038906003d113800b150300030b446424 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 288363102 1250 288361852 288361861
    0x280c0920070f0b0a061502010b0a06020c0604030f020d020a081b030601181d0a03090f0806040201080627090d1d0d0308070504030203150402010e01300f02030a05010618030b 76
    0x59840b003000302000200e0380c0d42c140000b10a06d4010400149501d0b544c0005002d12074002042080c6c03c02e41c0018045500c00d61107030b2041d8070f528003220107a0b500840d002100703000601c006460302603950300094210b44000400610000b00064603c2c1180c0114051040e4460800515035200001d20401080c4130807080c9513003000d503560340700ca1010500340d840680c2c008140c611443c5051403035041200010744203042080040c1c3c10000c083c014106020103480b081c201030f0002400604084c0059200b81d1413828440001c20130015440000a89020703141c0716480d0658800d62a12004000b25000c1400980381500402c840c0e0412501c000300189140c80302090307901d007122080b07402040181482070401c0044050f0341c0810004040702c1c3c00744840750b5a854681b00050000c038404552781e0600038990343d40702c240350b44103065214250768240c1e400d02802841c00d055000e0701207191400540c900c0003080c4000e80500790813050688900e504e840c0702d071021030300014264841d14880a0007001d203600205 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 288364352 1250 288363102 288363113
    0x1c031b02040f050103030507020321030103060c0c02100504090e0f0613020117010801050a0b09060a0b0306060d05100f0803120114210105150d020102280c0920070f 72
    0x142029001410010307001c185101d4000481e0003e0700290003140000c2100800c5280801028091040a0317010100c1c0d48130b0241d04868901040c000184103a07210740383c50f400d451295800454464000700307000c4056080e080d0150140d4814002c0ca8245410400310070182e030400204840c28041001c010b201c40d54400c5101d0007404c245403401c03410010351803d01d144680d000f00c0140e01030103004000003818103102c12100115081041d1050203085990f00f00309a07959500c0d079220071100c01154040d030ba40d4440c40000d00c68468501450001840c0905100710303404125a04026190030101c1401e8041d1102780b46650307400340c002c2c404000170a00d00144100b5065001c42400c41c10050280f200140d20302149c0c05144403454025100c0740e658074100b000e007100380b04001c40350034411b480c005414141038000070745030382803c4a281c00301e0a40d2441d40001d1001c030340710070700d81c0c0b80c01005901c1f003036441c1c42c440406400d0f401c1c203050841d1207421030000e0300c0b010001220391407070340101101708000c201d42e600c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 288365602 1250 288364352 288364397
    0x30c09170a0b09100c0e0108131e030c0c050315011403030412151109061b0708030a020709060621050403020f1b03060f100b0d06081204051c03 63
    0x4059402180000000030381500e1030140180643d10140140025040903001114000d004500c1001401001e00072a0f0f600084402d802100f54000c1080741401410444400510a01c00740700c211402c000310024154407044007401c55200b4000065015922001c16980340c40050585423045081d8004021a080c13103a0f6825040b1800b4090360305050780d400b10344e444140785110a42c1c141159500191000d1210f1146100d0402d42c01489400e040b0307004040344c0700340103010071000f0104001e0606c6087c0b280422403180148166000c41e40d603640c0802c002911400f45120b25480745061200c081182401100510380358004141c595a44a2084505c80b0181c50094015020f44c0a40c01000351700003014001d181c2081c802c0101000c2500d4424140361034060300400c2001000070400510a80c5170208001c0720880300703010f12890b01d4220b4152840024442548441c007141b0075003040742c25030401c1c0e101800803114205c40328860319901c2c400302c0140401e1150003c00082c40c0102c1d059181000758076 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 288366852 1250 288365602 288365639
    0x5090109050606220515070b1605090f0d0b09160602010603110904031b110109060201020702030a02091e0115030b04091a071808030304060507050a08040213110d09060c030c09 77
    0x15980e130525643c40101d89506660340002113a00400500c503001e1083d504903540e00700b00c0002d55000b03151207601005080d0f00461544134402c00303000780142000e1b40d92032405641070b42c1099603010282850120299101420fa86c8120061000d11002500b50b0040c420b50741105d402c401e43e182d580340044104061a00001e2080782030140d0321103840103210208902201c2c503071281c0311620600310310000140401803560b002d002103a00401614005845c045000d80d519503059440701002d8036071842c007481100003080c2552840b01c174040001140440c15880c0303101c81c14591800c1001e0420b1000340b00a98008890180c1248500c0d078214400d001e10042c0c6aa01455600d4040103031100b404106210003050751001032158404002d10092004038403400d5081009410090302e05040d003c000707045210000c101a01c2819600c1c1810848441038000c0944690340c07001072a694130b210003458000341081c400c19140302d4a810003050016000f0310a0100400366900c1c0c80d010285400f100080b100024030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 288368102 1250 288366852 288366907
    0x90f0303050304231506030c0a030204020d0209030f01020304031403060904030f0318320a06020f070c03060905120a1403100f0b030f0a0218102705090109050606 71
    0x500c51354402d180e00ca0001854810602a042d03044041035803070170746000640418400c3d0440040742c1c1d8251344a403140401c0300c0d415600540c0b68030103030a60780c000703006000625401d80100c0034640769544040d402140305d94466241c080fa240c8800318080c4090004076402500440400003040109010744015400301d9200d180c08100001d50b042e20025030554a20100c42c10b80300b911480e44801e10840a080d41001242c103d00074000c000b1a40075a03414200d1000303440c907580040c81c11000100f0408a034022504402d0a01582c2c2c1c0e03a1406030b00514840006840d680602ca80f500350b41c4141d00e04a07844400710755030b000b01d0445038420318000c6a0000c1c20100304580740b01400900c0d22075211218006140c03054171543c480c6850903596682c110024102c48800d84100044226141c0f0f120400550300070503a1101418026030405a46040450045080465000419200c0d1803e400d40c1c0505541081d10041c850342d80c1d42d00c40c00180ca1045d40d840d50300100c00e1020241404800031081c1c001c0300c1c0c0c1e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 288369352 1250 288368102 288368123
    0x415031e1a060607140a0212100b0303070305040b31090c03110a030c0905040c050c10061a0d150b04080f0304051c03090308120711060702120d09020604090b090601090f0303050304 79
    0x650002381ca000102a00e541c80b5000004410103032850b6108414160390107401441c500b21507070390010420b11941c0251301e02e29001107850012400300c504003516030304810101c0d4501000341801130380081e4191062a60660505141c0329003640709005110761490b0b144410780c1001d8403651305070040e100c0c2d0003110703007080000f0b00300145a0741c440c0900707820b400d03050f15002c0e51412001070f40c03800c6c000d100d0701f000340c0745050800030003549050b0441d40d0104103a504010703403901442c4035140042c0c000a40c119102c0000c180c00881d954901a00038000c958200048070904030800340762a80f0383c001d510803e64407500c00c8100c51030000b00183d250100c2480303441d040081d10b40700d0303031350090a4010200701000d401c07484040020791904841c0c0c6517542c807030140081000c1d10700400002d59504c02c6ca40c0002c102c100114900c20449038540089140950062803603486545909106008021408140344501d0410010882550140c1c41c4071050b14070040b0701d4800700341540c805441030b82c00584100c581c001034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 288370602 1250 288369352 288369373
    0x30806040f0f0f05010509010e0702060a020315180a1d07050d03020c060d0501063b01020718020702090f01061d0a090507020c0a080304140415031e1a06060714 70
    0x1d00c11141c60f280d21400c00101941440244404030b0016007100d80e4012000041c442041c0d00080d50a9011032034040140c0c2d2944d9080c00101020601c1c9403803900118030000701c15413004001d040038810000351408100700c1402c1410b1a8003010f41048410300c071b0300244802d00a600b45880c1170380403035020380110b82ca48242900131940c19400071034070071083c81d6680e005000155124000d40181c9840d0000b8070400080c0f44140f446400c0c9001594030340d02d80810261280340d0007482580020044210b44101c9550b2180326a0041d5102d104200d02c507840520000f01d107600d1900115058450680d0340440b07a01544203c3d81c03140000a201651042c247c60b0700180d0314003075005503845900d066000e0201c0041d007500b80b000c20505a000028290000d0000b031020510210382441458070403280818104e801400b052107542180c0c001400000c2035240b0600c003014869100810a403040314000003500c110020075120010544215500c0041000030001041485100340340f1002c1520642d103a403901c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 288371852 1250 288370602 288370631
    0x1110c0604030f0c0503010524120304062304030308010302010c0f050106090c261f091b09060503040308070c05150702280f0201030e030d02040303020109140a030806040f 75
    0x1d64070485050f2a03d090a00c10006003240f480b005000030341c0284600e0070300071001c0199003000b0040004102d20421030051507914007400450040342403040e01d950b00c0c0c07981002070010034040807400102e110881100140e1401200305c50840e80c2668407aa0380ba421a401140c242d0b9900205441b9104c2d204132601c0406c0003889000b0040407800c01c001082004010040c22004d07421080a10940352001100d00340307a9552601940481800701c01d2480a800558200010903d60030003480300e407a1134507007500d207000c41c00814882c41003915000d4455580f00f404588901c805c032402000555040040b51017940250001502c00703202d00290703900700240c500c241e800800121240340041e40103d5098481080410424020341d261182040000035643c4407000d0052450700000d04140c3d4501020b800e0040034401c1e5070f0405100d0304290341c0c2d19030301e00f0000d02a03c92240b040d1084030703801c4500c100d010070004040c2d6410342d054448000303581d00e050130800200000c401019100d03440d41004442c000d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 288373102 1250 288371852 288371857
    0x3010b1c060b091503060306041e0506090a170a090513060b120411030109031d04020c0d05030a11040e0703150504060618150203030a020a0207031a040308060609010c0201110c06 78
    0x420b640e1038100350810882d9440e002010a1100903080007441215103000c42d080340d00c0758205004c1c00d2241110f03030b003084181d11410310140141c060070050101411001c2207003041d0340c0c01540810400700c28018442c150b4803896900c480481c480071003c000a04010707204829441880000007007071039660204006640c05080e4590030440480c0811040020428100103040c005030020003ca20069074003401c0034002e100000407068010014808643d503e4048550640c0c0010030b6030761084c0550740140c0a904103032080044a420403080300c0524410364240c070100d8030747c154041400d071551403054000340580102c030030708000742c000c010840e920365000c2d035001445665540c50207641503221003001d43c030558100c62031820215900701c003e00d90002c08c2d80d401881403d40182c2e41c4555401c02c2c3e00d02241540014001c0040200078131020340c2021410703100d00d00985074259103990f1181008140d01c2640900350100c0c00d540300c424050f5108400d101f10084407801101d8890000d0b9001416a4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 288374352 1250 288373102 288373109
    0x309050a0b0f07081f0b091306080303180615011121180a06081b0d060303080609090a0c1502070506162a0306050403050d1d010b0901050603010b1c06 66
    0x600c6010034032041640c0140380130342c810003040d403007104440c458609036088041440ba40f40c80c6c10011a121a2a9135454030800500010400400c8110b03501c0c0c901d1616074104541f0401d540d03080c8481140d103020b01044141c0b040c3c044620040c64086608015110034691003c0c43d80544502a10004110030003403000510500c0c14841035250408036007281408010009036a01885130080204880391308417031061340001c4111644180801e000104c0f2042e400b0315141c00e031005e030800e88000b040c5500f20b00d0480c0580415a6400400d594035240b0680e1000000401045080d04200070450019200d10302c8400024901c1901c24440d501e42c0040c00a42007110703024140307041890990200b103085214280340b9001d00c004400d80030314413110580c0600e890712000d04000d8503540001c0c00c051003030301118003036000c8000c03c012064840c41c00d1b00c00800c25508650b0304d5031a0112110261920b0b4074118100c1b10000c209a14507820031100e5015a00201e00c0001050f2008108031040415070250348084c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 288375602 1250 288374352 288374371
    0x901080610080109120e011803150e03090f0f03010605030f030a02010e16140607060515120102040b270a03031106060103050103050318010e040906020306150306030303070309050a0b 80
    0x182004846103403801d400394003200940e807510403a03a00080341751003c05000100340c00c20340e68020030000140c40a1240c40641d61021640140110800401c1c8843c1d0b1040c489080c41004000003c141c3d407a980d22840b9040d40c1d1114040d5801d10651424110700f618480b0b000d00082401d580d58804645046854003120602d0f400208c1e0001c1941e50900c1a2038001c0f4072a00181400c405a40d440c141c92180c40c0582c00f141c0484003825450fa468080071501186d502203800c000910f09058503000005007218440c0c411075020703e2210500005009480c00c1e5511850071340c0c0b070071000740300c0c0c134001001b0b4410030007001400d04d280c05500e58801602900031030113600c3d0581100b09110030a0700b000002030495060511306001800407450020940d59400c050407400c00002541100580344c07500d00d4103070f099002d4240105282008120740156025000503071b00e1030a0b51980910110300c0303000c100c40d095010303841403001901c1103100c0d4201c000704034041c4081c0ca0703030b250858494614280d01210309840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 288376852 1250 288375602 288375613
    0x150b0d02040810020304020907050a0323060118050f0d021306180f0501030b070c051002190206090703030503040b130510060302181006030e01060b0a020f0709051009020f09090108 79
    0x80b04800c0c490301a00318040c020071861480e00380c1c00103418000c0035001c00108440413854640c82e6000780e02075142da4000314000312a242d0000342c2c542c43c14104640b442d000446e01c01a040f078120b0791040d084180c800c0200318413188980d420901c250042840c90581e4403403112080703554011018406c440180c88240416844024203150820643d0408190b608504d40307040300400215082c0c650254108280d80352804103d800b47c20428500381f000c07030503000c10500c0019400d040d04481418108152519000d480303256a402c0801601c1e070500d4800507000c90410000180011100307a906903015034400b154000d0000030361959031812004513400c0301080e0341e65000b0300c02d61511400007040075240c3c0c50484003071310b4072a001d12010140c03485800c050546a03e1070342c10204081d0421005000c00c1180c40e901c92245010003903455288541d002844d0140d15404201d2002d1401410b00c5001d0800d451101c152801c00e00c50001d40c8101c400c111107800521501c0340076541d45c00c03860300900e1070900414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 288378102 1250 288376852 288376859
    0x302011b03020a1104230901110c070b1b15040b0112050a030509030a02060d0603110d030e1003022a01180f0f050a05030a050a020c040c0210150b0d0204 67
    0x1451499008000003503111150101000039900007154940c142c1c0c880603580d41282003c000c42c02400c00b0000c0008040d00703112940154a9100e444944100f9460000b8052004404005012031040700d55003111034122807014002e03401e00384001c04003481c02d02e803040e403410b042c03005150501a400001840c00300b000c20500040c082103102c1c0c14050030300c0c2203000103d401c43c2e540d801d583c1c40c081d400040c01e2100124040945a070107114403105143c014103201d550b51030040c0307010020540d03070100702d840082484410686050051040101030340c191a600401d848030010400d1540e41c0d000c4000c2010303004c10050a440100c50714903d044590300e0504041c008050225a0030744056070480060310754060307441c00c0840e4050000c0720780980c01031095924030a240c1091410240c000002130094880082c00050580c1e2100c0140385800c00365081e640d5241420080005035080900c40d503006900001c200300c025080c40e840b46600003141100707241415560362810304140c0000c024001c8c4d040e40402c080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 288379352 1250 288378102 288378107
    0x1a0403060c1106181903110609010b1c060b040207030e030c040203060604050603090705040c021005012c0601020a050706030b0a0f0b040e040609150c0e03011401060e0a030210050301030201 83
    0x6428004090a0500780800882c0d4210f90300e01009014680c400b0f000101d6243d140030500c07061450030243c150341a4a00e105042c050180c60b01204110700c07070702c52913001406041d0184512002400d000b01801d141480b40d0007204481e048004d4242e43e203540d10158500e10f079555100804140d482903c0b449440036030702080504008400b410f41d07006900400820900b0b43e202c0048406684081710307210303220780311700300780614218013500107540042c0342c0f00301e040e511500021003000f07445100c1003c0c0596071302c07080024903842802d590030704542403070000340d01e02e4444400d032545e0040c011f03c115803074260356480e480e103400141e80c00180481d03940c1d52034031500d040081001020b00290f07050005520b00c1c003180040e4510662140c0980200b0b50703404242008600e4101a0001c0c0d0051a41003000d00c0ca031003190000c148040100021030f8180c000380035507040c18003807512130329807018100c1c20607803804605443d4007080843c4070b540440f4562002c4010707503131404c082221031525561991607605501c0003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 288380602 1250 288379352 288379361
    0x1050f0a1d030906160834110d06230a0b04050c0d020c12041508063c090c0d06080f0a0201230703020a0215070c0506090a1a040306 58
    0x400c81c80031180155845400030010494010480c2680c8241e660400e18203803010406100300d00410071840015846c0c0d001144c604c0e2a25224400700c0f00c0043c1c403071a045070100308081220700a1541c008a00c07034500600c0c1c94a80442c0b030500130b0b0004a000310082001c0e4808160600c6a118001190000e0000c800494402e0030b40802c001e8508021b14100810540100d000e02e9000e8007071260001400c0d580300e0b1003070000c82c0000c4016000c694a4035210a80880c050078015440c1001070841d03000a2011300e270862030703000c502d001c0c41480a80b685000b030510b00b60003441044c901c180030480c850741e21551908003d1510640d0031110382910340952001c0c1301c0a407829644207005942c4074101340340d1a048041a00c100032542401d00b2440c4110800d4540c140b0030a20b0184860383d40081600003d040d0042211f241b428802c440e40384802e903000c1d080107514040c2000141120f90700b0320381030006040c1038000b060301d01d078010003040e030103a580c40750001602845250a0b034070741c0380400c0800402115004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 288381852 1250 288380602 288380621
    0x40b060a0c050d0c03051204030908060a0f05070801290f0a03092102072d06050a08010f0b09040f09050706020f0705090712021305060c0d08010f030c050d03030e01050f0a 75
    0x5013111220380ca5100240b440c06036420892410903007202040400d8041c500c0c01005190300d9080d01e220f80f5090000c84000d040b4401801d20440c01c11001807000b0384160749941c16180c0b80e5401500c140003c0811502c0640c01400703a01460340200030348881168050003500310001d413039501103014403551034100138440070358510940750f880440c80d8040c0182c02003800c40030794105902c031070304445855000204414203000280d010307551440020034901e6224008008554644d26425413699803141360740c030001410301c030301403007504180040d040e10314003034000b240203020090b404601c054807034403400c3c1029141c0c4d02440250744034011075115500144a020000d1608072004d5006243c040c201030200d003441c1030501e0180c1d1340007610302c4201030b2140040c8040d04000e007955031240340c1414010303035a0b00180220381c0411548400050051500388488007926440416446c03114542020301c2020201401c0c01c4061684034100d10020210074441d15100c1c8241580041450a189908078110707543e411 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 288383102 1250 288381852 288381857
    0xa0803040b091003060302130c0e010e01050d0e0a1509020111010509030a0e060d0606030204090b040e07030b2d06040c0203070209040308060d0b010e07020723040b040b060a0c050d 79
    0xc41001080204019582910810350f82d001d841c1025a01c100d00512041d04020750101300e0b411241e02c84521036000204c8181e07140c9503803144002c0100191056003540a500380011800c003d06901c440d83c60b000402071045035400c481422a65a0314004203080710307060203107407580c1e03140340505540c1c4c840b000382c004041400007040035040441220381c9912455440c08240f007a103d2400c1c0880d116201100c400c6030001e80c04200d03503500d070827008021358484d06c9440c00740b6003402c01d0500245414441e500d05500118010038901745195504043c501005160304051401013094400121000c00c1070000d2140322030400b0200e1602e1000c2100719180c588102d01158001c0c04050f005807a1146041e8003d5018105900c4a40d503620000b144000c10050051114068000004002c880107401e240140c4081d0241c503842c50712280707a04d150790005841707208018100750b00e000d07450800f644100c041000260010603503030044400b040140e4001c107003900009003092104020304c0301c103000070300c1840f9651 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 288384352 1250 288383102 288383107
    0x50607080a021c09120f060f0b010206070f0531060c020a09020c06061216080c130e03030c07020105160b040b010b041404020c0703060e0a05070f15030915050c090a0803 74
    0xc3c00c0149048135a008520760301401c9070000c428050081051003c0b00e5001d001404a085110000c2014002e8607118501606c070302e10100380c059001e64000610803203e60741301070806610307103020840701360040c6070a4400041c0c40a41c031035514034102000301401180e00d0344540c0841038070602c249000f5641c40281c0d2244107000341020340c040400d445803c21411100300941d0514500c01c079041024a10b0054171101c0003420001e031a580100d61030810050840d820f281414181403c0e50640d40e0b000c0c2848041d400030000200d0b19045203014080340e03030040c50903904041d002030005c0e18417010f00c2016100e1441210411041000c014000390140c4140a03e460070a803521402e83c04256401070424410340c0c01003442c0108410070403481c40115041003040c00700300007010509031030342000740c8195600c2c01804400f0a08545400030381003201d5034000b000c4001e1070a00b1044006100980080703409518842c000180164140a010300070805000c0e01c81d500c4070b250007005200344a580c01503031190001e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 288385602 1250 288384352 288384403
    0x200a0b0405010f0e060d0b090903070b0f0705041d0f150f060915070b01060f0306080c100c14010c0f0806060405040b0a0b211503060a020c0106050607080a02 69
    0x205940495000303003481100351201d01401d881c1c64941d000f00703541180e0042030b030202050303040d040845860b000380c946d4403850f2650300d080c684a11891130060001c0d18420042140d403515200000da001e2004e280180c105510b0b40380403414000242e01009045140c1001c2c4100f207100540d01035001841c203240c801000318144041510b6140390b18505101c1c5001003403400c40c60319040c1c2d1102071541c40c000ca0641d140d1092922100500080c00707810005200b542c62001c0850280c4180c40c140d9980d000245007441d060f070104001c03e03032461458001c015035080c41c0e100041034000b511040c41c0b22500081200d018101c03004101c070031a4030f00402003041c003505020460312010304a41c255070040c1c134041042554000868501c0c0c00d198484940960002138080d00c00400110080c86001d07191144501a00c80b9100c00030000c180100302039040e000000840d8240c0b4540c0e005008a20181001054159464001802940000303c048d0b40d0a080001c0c0d1240030342c2d05002241502c0c101c2c3c014000a041c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 288386852 1250 288385602 288385619
    0x7090b03040b01060815040f15060813110402090d03031a01030c05030f0901060b0a0201050726070c051c05070203061b07110a0b0714010b0109080c0d060b0607200a 72
    0x62181a040c8243d05c03002c1511140360390074203124510080d0003030141d0b100e0b88042400a20002d0601c00095008480c08220395205829603806113075070482d42c040d1101203494100c070359002c220844d5401982040451169140c841040000ca800394900040c040b4845100108409894110a040502e01106120403e400c0420323079410000c0c0c180500c140790784040d452801403032a130b00421a402000310b1643d0840d54150440f82c4188850b6075070300b20404d410001d00c10740186441419811040705400604140c0c4100d4130302c82c00c43d0086045075208966140c081d0800c031014881100000c1d00007406a095003410030000d5003014120720502200c40c2034012180003401a100700401c804c0802800580c40d07600c1d84541d4018103040c0204640d03031801454050f40c2c05c0c0307081094039919400c101101c2410f6001f00082d0085403069000b50580005900400800302e419000031180c441d961411058182c81d014040d1840034032034850105070008500d00f01444d4100440602d10900440310b09100422 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 288388102 1250 288386852 288386873
    0x150f091115030c04060e0a0302090c1b0a0b060d02040605040e0a050c090f0f1b04090b100c080a11010204170a0203161404110d05190b15040b07080c120307090b0304 72
    0x110350b1302d416050941c50100258052181e0348c400795010b40d211080c003410811100c000d00c103040803400511808100401d000b622000112405030119410500242c480c0c2040083c0c410003034401000010020740f03900005081301d080000321030480d0301030482c0c5400c001c000c0200e1600f07200304440d010014548880034440aa5009140484880c0704101003541090712002d00070303000e10149501d94540d600c81c0f0505000302400c0341c405101d5034124400d1000140030300c01d205440740e0040354007840c4c0049a00103903050070380c8060044207503500304800508105045072035103442030460050b07d0411001c0c010185000703420208041500480a820490176152204407040700409803408605400007141010590080c51768080107141000200034444100d00e00601000101401c00c206110303040003408003010800e01c200320095810401030206980c00d4010700101841341000d2440c0201c440c22803420700880e43d0100e15030f50702c0482804030254001c961b0302e0160440c00da46a08615042c6c58281d04203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 288389352 1250 288388102 288388109
    0x1a010905030a120c0503043308010603110408070e1e0f070305040c030f0c03020103050a020915300406050a0b0d0b0603010e030a0801080705030c010c150f091115030c04 74
    0x5041d07401080c1c5698000c480840065410109036030b12a513581c00d050007000300004d03503845141201050307500235844405420094106654030511280e08090054008017041021203000c040c003071000290846080144001510452148031070600b400f459040181c00c1f031400010265210108010540301069070701036001c4c0b160725001c6069100c0d818204550001d07500040c3c111802c0e914140f0501c0102c1d10701d0411240300b0703a0108500d89c1d405911000300d02074600c0701c550105104c8080c0030420008400381c00c2040301c004051012014001c00300700d51500c002002000c030358400040000b4415140720381c680c00303102c0000c140452040180003034440b00c60071900038031407520a40428800e441c254805900103641c0004c9954810140d41c015040110900c1541002d110305d20000c40e2504000c60b44074881001030b169510866035030b03902d982e00318482c200643c480c25070307a40000071005018051904400d00600c480600c9001c0842409071803418086000403404040051042c088001c03030445088 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 288390602 1250 288389352 288389363
    0x120f041701180f021915120b0a12051213090b0103090210110106080f0102070605012c2203090303080f04081605010f020a051b070503030a080c0d060602011a010905030a 74
    0xfa05841d20000f5100200c08103068031440c0800c40214045000060960003134900703480c1c2c07010040c400701c14402030b5401032070899003024001004109054002141c1c400291049090300c680944640403050740b42c0040b03954035144075610700100080c0700c851141e4030409200b86030500040c001d940200d04106030740b2401d1020000c000c19840d0a081c3e0079400780018000f20019a8901c0d0402c4074054042d411125054824500d04000065840a0482c1003240700c1911140c035801e1400518003100305040c010300d14054000e0a0202c0311a140300000e02c085a20b00c030351290700f00309041d420018241070b0010003c2100c50020000d01010422240c2540d800d140045404480d0420320316219002d82117042014485600128030b80d08030907040030150510345c90b141c5041400ca590704408a944542c01d100d0142c041c0c03c20810030304880d01c901136069100301c40242841c03916100390312007800c0396090782c0f02c0d80050b507440d00c0043c64402c000080000004c82441d003028907a091070000f03510340c0e4115400a15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 288391852 1250 288390602 288390623
    0x307051c09030203030109060e06030601031101180b0a031109010e061308190605060102030a05030a021305100804030201240902130509090610090504150e120f04170118 74
    0x4003808041003451999428142030040440034a0080e50700e0304207020700542075003402c0000c16a138480f114007038481c4000400406c0e2507403854442d10b10340d19001e400c0038100000e00b10458000040300140300001c019818802ea9148880030300101200c035031124a441c980c1003000062034980e407089007802446004c60f001c83d558540f6181a100488280c1c3c002c81c03450145c094882c090b6040c841c1142d03003240c0503c07014072082c2d40307410049032a40b05250300d003804210180b0124051300e0480d40035101d81880c034281445015103680000c0c00028080054000007600c00f410802090386c280104481c0810941c0b11420240842541d01c0010b40c00e40174181d103003540400e205454100310030842004000140c0f90703007150f0901d003080d1600c918003101e410b441007214990010320910359118407441703240c01400701000c8004407081d00c2c1c082e0000310386041083c41703040d0304180400c44503402018002d004644007541e6030703e45035801404001c001c4004a05900d00041e810460503484100048964062240503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 288393102 1250 288391852 288391867
    0x71e030225080d09092d021c09050303040c05040c1b0c090603030207030c050306100b0313120504050909030301120b09070306020403030908061513021c020703020a1e08030705 77
    0x5004080c0c0c0710b180c05100301281040c001d6001a2000117440c00d0480c24080c0540518a00da030914654103d4220f07004d0700a5010035189096020b880c5125014160907030b25a440c15010041d180070003000c2d1456003001060104210617400e00c14014a025141405050b6202c0710240000c8a082c464050140c2c41c0c8448c1410460315112540c0503140f42c2400b040441d41ba420001e5441d006800222040c0b4044c40002c00d003840c0000e100b521488038540c05090b86810103512590a403c041e19200190f44546400d030700140045600704560a960740d911502c55103010100621500d0240c0720301c4240d00104018085031140040361200160044298045925a610081c0c81c110381540301601080c40807c02008142d40304102c402114002030845040b621041541030220a0004c40290f0024001c40481c423880c0c07090300580300ca500d43d00050041c544900383c40d941641d02c00501140146c01a4040000300118016090329580700241140d00c5102c00755184020b621010b4515818441c0101d10f48 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 288394352 1250 288393102 288393163
    0x150a02010b09040b0709060e0306010504020901170a0f0c1b261207030e06100522051009060806092104080a060501090c031104030b070c050a08071e0302 67
    0x20303800801500c1c0b0031032840c150a01e0000114291030310740c00140f0090002665030f20540303411040c1d40000700506820303442d0030f003044029800903a025042c40340049010305080320105001d0301c5001c0004c40130907582d034084a0310040702c4034450b00c5010300007140f803034083e00700c1c40d540541c0f60a42d000c411080c401d45610040b4801d4a000800d0303c4030400b0000301016072429100030b05024126a032001d01504c105c4240e4286c440c042101d00e44d1049480e110300300041c0c03808040c103c0ca0b10204c1003502d0301d40a40c5240c4002030b2601100c4030005007190300d90400c074400e514030171840202000030144c030090814032071260310364106c040c0e86a8401d80001844100d0280b460480e0024120903045031000074007460a40080c04003403103460380c040c4c500740c02c080380d0034040e006081c0e00d001381c2c581a030700d81803c681c1c81c898a48c0e00506142c04000b1003d41d00e030001001088411803160240d214503444080074030340f01e04010030405441d10900c404041860000743c00062452885092040c200c00c81d203682e0b13084 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 288395602 1250 288394352 288394361
    0x30203040e06040905060703020c06070c030f031a19050a0605130e0402060d05041101090e27010b060c030304051605090a020d0e070f03020f030d0f080403020309030a030801090b0a05150a0201 84
    0x64206d00aa509101e541c64041d4000c00001d00c04200ba42d045585042080e178195907000d130050003040d60103100701d00311442584030320500b04210114016100712a00449d01d001c4002c05d11030051030a0400900152803c44c020b14010002c5123001442c2007014446640007106038841e082003c18418080703400c40d5100026104000d2039141c0c100414039050500405140c142c200c842e010400800e0042a00e2800500c2d861041e6511440074034882100c0480c04c1c12070064828540e1a075585500d20501541ca54000f4803010059500070b5460781000d0401c603080080c012100c81c103001d60a1000c004c552501d400d46503014448000060700d550b04102d0f010060115262500c4c224056001e010400c0c150140e6034200381da00030b68030084814501c1c4103141c0d540300103030b0005001c54807504054600c00d1258003515400780c420700c1030702d05000c1c80303201280c5428018039045000c42c0c9100018041800a8030038804105e03002c0f5010310b4564644004580516107038411400d104800046c8520054000d410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 288396852 1250 288395602 288395621
    0xa0315060531060602031b01110408160e091903051e1b15040f030212070303060e0c071a0601180308070b10060212090406170f07050d030203040e0604 66
    0x403540d0688441d800c0c00407102a142d10741e4000d890301d00395103444074540d10400c0c0545240c1c1c0c00443c50312400c0c1d0034a8002100c079210502d0159260101c1c035103031041e0040940300a000c544010f225424202d000741d203c8100c141c000d0004d2a4400303040010244002982e04078123503a049161818441300e040448562103401c0c8550010783e50b183c034501e018a05000100081145000b520164a02d0746a5854480300b2200c100c190b80700c0c1c070a01080200f80500c0c052180310f48240121000c40d456108001c403907030400310b402c0c0c0c04680e170b4003002c1181c50f800c51100c0d54400c0d01c40184c649010203d5460741150410310205600c8001c8203000600c290b4025000702c0000d80a40c42e05080f4140c0c0d070724120509612488040ba10800140d002c660307000302110108064401c01d8003d03055040d034203210800070b40c000311552035020341c4840e40010102004041c03845400e940102502c02ca4400710400b41ca8101c03150300c40c83c09003055801060120f030307020083c0d40c140d0707105e4000000d10f03441c0c07a00054003818003041c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 288398102 1250 288396852 288396859
    0x160e07050c0d180503010b0904080c010231060507051c210203090c0402270607060c0e010806120717070305011e05060306010b120a0603050f0d02070905060a03150605 73
    0x1140540310380c000c00b540f00507805a412122299840340281401e075007408128541201950001c038001920020141203d140c9100005007001c000385050103102070440813680030f070600701141034080035800721043c0103000075041c00ca280029568030706950324442624211940d010811914600d403007228003000154065180c8101c51102940840c029031090f245214548a20000c501c240e0410303009403404130b0703050401107030b4030b070120760240c000e4440800c02c0c0303680104c00b008508002600c0b0700c2030b66012000ea5603005400d0303040c2e80001d403101c08060495442082c051000c0c050704480010303580140e03400c008030b0085072070482c6096803511000303401c02420380d400d007402141c111142c1c00c08002000c4155000348603030389444050645942003070107002c007042820004c1c44402410703465a43d42003240440e00180c4030703a8981340c07241403003024410f83c0400c1d04036404100e503031641045003002400c000c0b0350803c81804d102000400814080c8401000380c807140015850480ca02e5006400504015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 288399352 1250 288398102 288398113
    0x906030613110418050907050a1e1d090606010e09071803050105042d05060a090819030f0c0201020306030a0308070c0c0801090c080102120402040510030807080a11160e07050c 77
    0x1140882c0080c01c01e013100558491a2000098101400040c40f0088030f1000c1c00802400c1c1c145030701303045404041003079180019080400011800701c0c490190079501c4c0d801d4070700e02403414000e494070b0038140c020385114100b01e400500c0107059542c0c0d6205580148403400c043d0024150b4150300e04007003203031740d03c06080d551078982000240001034101910860000c2842c01002c2c4400c0d04000240f20380c80806059580a0030028030072110a900001c0c0706801603011908111402000410b0820038824040009440c1d0410495441c95801200c9500c41d4500081d400c52400c000403e58801403000f01400700039802002c546228002d4070004281900f00c0c1d55000d02c1501d809445002e4171388603504403101d5180080c0080e015030103109652000181c61304c2c105094545800b0040070700000b4104400c582d080540000000f03650000410809106903901622005041005130915029649500140e04a1050034107480c1d001102a003c3d00d13019a41d01748a0b44860000f224a405061040901813161 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 288400602 1250 288399352 288399359
    0x140a1502071d06040c0c210306030623071d0402030a1b03140601052505120c011a060304020a12030513060203091f0f0e0d0c0f180209060306131104 65
    0x54280607214990941342800014000304046405402042d00901858054141c148505e42015003075a81450246000700e100c0c0d4494440034202d400075240c070301030007288052030120010007004899003c141c60800c021502c5c5201d80c610b011f406c41003403907481242d001001a040c00c0c0300b58094000c1100c00d4480d081c1240d21000082c00074600c040301c130310044840d400007404035031040d800c980c0d15174902d101c130413030f4610400d104041c0041070810407612800b519894440140d0400e000d4014283c148002054400078200ca40000c85ea06420071030080100f04100710240c1c50740d60340c0740c00721900d1288507598250f075410112454003d4510320f0080500d8400c2c0090881d9000025005902e011140d18500f000c00e462043d00117501fa0745000d02090440744904201d900030b00c4000ba200202405158140c0403550b2250171072444c640080122103890641031220710f0711510241b2340c2c416180c6046280c02002c0e03000072403a00000706018400d02641d0f00782c03040e00c0b0807504007040c0802d05104aa454946 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 288401852 1250 288400602 288400649
    0xc0e09031804110406110a020907020c13110703080a0b0d060504060b03060124050d11070c0b0307050702040506030109151d01050f070f090b03090d09140a150207 71
    0x10220081514025665402905140c1880385089210f0b01200c076071310f000d28020782950a01078450310024107004116903000940c03a400481031146055a0140c441000c40354200113420030144417403611700785002400f00c49100c1c4002240d4000d50503042c444c40e20f40e030f100c144002515843c03100682008807961a4001c21000e40c0042e402503125110610201c01482d0038140e48241c01d102d0a40300c898601d0742c031160b00105200711803200c00b040c60100d01c0d151542c1112030660302c2080900400b4000050581c1c180b200048249014101d0040c0052450911035802030050140040c06440ba84da01c3c000702d0890380e000d40c080328105902080805240c18028150b4000300b001c0010341d205488032010400f054201841181c0c072400e2900d0880c2c2a948480c0f02c1200c402251103080c5c070070b000c06072001140319019030020314880c200c00302c0200090f00c0c5090006005c152503502c500e101820901e0480b41c903940c0d582852007070b01c206103c406490440203108a00d41600e070b50110b00c2017020300102080e070b8107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 288403102 1250 288401852 288401857
    0x10050601030b0d022b020901150905030f0309041104090504030c0c08070f090e0a0203060108100f020a0806100e060d0f06080f061504140c0a080609010b070803040c0e0903 75
    0x8400d803800c1120720690410b0041c101c041c200000d40c804d2100303044103549141c01044c0051020341e90048071169450380e01040f0164020f030070403200e28210409403400725501003802c601904054000e403021100040440ba520b0082c5d020faa440b42e5142c2061103001801a82940d00400c1d1684080c40b0f541440e080140110340700301c40030782c1c0c03004c0c5440c0c0101c4d41480005040b0102d9038103212006401e80380030900c100038801d5a600c00300c68021026440c026035400c00180d03010303095000c06403080900d42900d100c00c45152958003d0b2050050100c1d90400c2e0b00b01d44001d81c440815030b070100748229524000c41d4104074100a840d8003400115102c0041c2181d0f52000000c500400b4007000820384844210341c0d18845180006c5291344040c2c005108001c065099521b95400a0030105c0d0540000b6200c2c101000202c902c007004c2d050200d0641d2945603c544031030303040b0406844921035541403440b801301501c91a6009081504000003140402801b4175072100241185040048103080c2018120b4490f1b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 288404352 1250 288403102 288403111
    0x50a0f140c010f120f02130e0928030c0302070306020d060503010e07050607081c09060b04140f0112080c16050a0902121303020a1401050a0c0c05070905090f1005 71
    0x5100e00d40000300c07903500400c0c00c0c41150610b40c488150349010500400e028005414013460195024000c0d15038001c00034006002401610020b42d00b60301d000ca452038a04041045282584011403221801da807070740b2451440283d4040c40d042440c00050f080aa00d4821070383c2c402054148009003e140f005441e03400706095a204034002d02c0308480014580d03a0764035580c002c1541c040c0741045203400245103e030062921040c009072030712401e48041040000c44000000c00d940403a150030400b01c2c07501e010710030031841220b5401c50410380e0524584100c0c0030351050148018841c000f05e80042800354103010b50700307141c12903821180700d06400d9041c2d00d849a0359200d80f0340584a003d0011a445500e03000345c035080307003c03000000140c1e520010461b08180c40a1410760650080d01c407141c0c00300701c0031050000d0400c1c0070341c00410a810440c11500032280300360a40c00c20884291510030000701c01107003140072108040404a201d89800c0c501700c2c1407904600e1000814811100c00740d44800040d000148503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 288405602 1250 288404352 288404393
    0x507030302012301142715120102030f0a0e1608070f0608011802070201030b0306131506080a060f140a0501060320070f0302031e1b030903030d09050a0f 67
    0x8201280c14094000c450a020f8000ca01700035003852100743c240329120705e82c000c0c0c000030078648510762107203003604152069641000d00708140111450340d0402c0c0040024808501c4002c500d517107810400c0401400025200d107601680302c40201300245410444003c0e140090302c000402c0e81d60711204940d90743c0b45131142ea0340e40d0000d8000002c8c56802200003e049503180111200e00c24a00c004030002944000402c80c14540d9640218000751030030841c003440b440d0440002d802c46601c40c2050040d0f610b01800302c0c4021820064140103007400490002135195010720046848400c8902c0e031009821105842010890028200303c0200300c0b9801c000d0488030651000c0000708440741c01200c400d58044070b8454111010000c00c00041d0501c80c01e852003c1c028419030b403c10000c041d10740d00307200c3c8904006a40007408a188032001110100b103088001074100190715000392030380825200d01440c442d044007140e60300d48010900c64103000040d0013503031003c0c0151540c6039a140c0300605c0350105100d00748 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 288406852 1250 288405602 288405641
    0xc0a0c39030506090607090e04230f1c021005040515090a030f0c020d0803091509030705191a040311030a03020c06070e0102120906070f0c081005160f0c050703030201 73
    0x241e041001c58006e004100655400914a040052410025401030f1086444c005c00d107500307441d080140c0d10180c4204403ca40903048004a0340c4243c0d191144e0060128480c81c550340102040e2600040d4000490480c0f03980807441d40d0307131030406904250013001e4a0443c100c1103010060409408034003000310501c40d0b2514ac0e5020300da8032045410300c4210303400035009680c0386103070004190703000e000c1d5511004400445050610f0180802c540e110700355035041040e800030401c0d4041160030300c8815562454510405005003131502d4070005816540c0203100c0440ca8003005c102454442c03e02ca0f80312041007001c40e69281c1e01540020029400310900305405c0c082d210108102a101d02c003521209c0a050b0700070304000720030070780703190031544544065a44800d0401c0080c00040011106d16090b034090140030048502d880541030901e8142054260054036000400c004111400c01001c000c1c8410718140005100c04102a42ca908640101602904c620080001010b41c15041800710f00b40359298800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 288408102 1250 288406852 288406861
    0x8070f0c0e060a140d0c03030210060902030903031605040f060e0a0503010209010f05092b06180c060305040303180b010302030c030c01092d0e0f0c0a0c39030506 71
    0x81441e40035500140d02020b0441c0c01c0098800d01d01144540580043c1414181001c6964110201085600480c0542c01c0105119185070701449a840280300701c0506510b545421003289403280300040c0020800008006624441c521420644024088100d0f00d031580d10740354003003d45441c0c0701e0002d8a200e20041c1c04003107940c1c10b042c02512914041a15001002803455005840da500640c0116802170b0b40903038480d8912510610382125070350b160b0380300e5060a6140c140401603544101e4000c69144002c8007910004141c00b505908881c0b40e07150000e0540c40301e14088014244c52415840c840055400200c10320065501c003904880c422001c980c41d64811105042d21081c0040116012400307411080103500388212041180042044459498035080c0c0c6c05030b40c03007462a411142207030712100100450310020790350702c3d50450200c04039641001c0380c03800003d001c40e441c188020081441c0e481100e44150000175980c00c8504200b0b21900490000c0480748800d151600c01620f46d03200350360108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 288409352 1250 288408102 288408119
    0x1210150311161b030f1406040b0a091a07021f05060a26060c0706050c070b0c0a020a05030f0a12020c03041203020c1906110714040908040308070f0c 65
    0x1000c081d0210781e20282403405024203806040901c41003a140b0015050740f005035031880400c6480036501c40d0300d00040c40801c0781425602401d244041d0055603201c002400040b40d2044945071740406109004140e042103441d041c500f00a6004031560714840c0d0105004807550003191001c0d00c0b01c0c40250b4854041900350100046e22002d0b18001d230800801d00701400302c60100851b6081c01240c01a040d100c0c642e606202d5031412004075079041c049000031810800b00501400341e545c03c0013107031420904158060316810313110000a0803064003540001441d501e018002c1c003428003900c1d00401a02c0c0ca130300c044035100c04141e100450b03440c001100d031a51120880c2d294400d48641c425400300550606080091201249864141c02d806500c24000070f00c65a968409002404011806d06030112528008000c3d1000006030ba000380103820440003441000c0306000d40b035540c5181201d01160307a0074942880030651080e41c001030406540042c076082846940b16148030302d43d20900d200317940d44d659241e9a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 288410602 1250 288409352 288409361
    0x20a030c230a12050a083103120c0f02030604120e010c050c040513081303020418020904020108060a09050a0501050a17030708030711010f0e010c0905220212101503 72
    0x61951120448000388858110f041014042510900c1140c3d1900c44079100c08200c2c6e08440014010006016692241ca400c0450110200c00b40d0300d0000c8061402e641e100407988a064900f00d042001e9000440180810400f00300c411640140c02d91700a42001d06060306d84e030322035280c00d0020807140c074882402544034a020044d0150010064620350103200304120141c90050b100b421108140c00031600414a503100a0900864000c51184130718035600c1848141d80a40882483c6050761050041c0075880d40000c00350700c19424078105101e9510f0800282e829286a0443c692441c605001c000540f0759540c002411780b030044030200305030f6035619110b00b03501d8600410503400da0414041e15001a00200140da004507850401442030b04000034110300f120205c1c1c049003801c40c1c450100300c840b52070030702c95504002003e1400100150a25010440041900d00d0041000d1858002e151249455a05031380501040c03c0c01c240840c00d0500b4060743c803e81c14014a5980ca45000c80d180410340240b15 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 288411852 1250 288410602 288410669
    0x9060313200306160306080d0309111c02090406240302040e060606070305030c300a0b0a05090a0e0105040b04031103071a0403030b0306101a0c060c16020a030c 70
    0x80c000c5681d0b541e0555040004d1a00c413109141e110701d0301061a030300610400c0c3c40088141c0d40040c2a0500d4101142c4c0541c21a0301c0902564a50481440d40250325a81110304c90701615000a40d0300c95141020080c540440101c4005604a40002c1d450071a2001002100e0007240d051100700c1d0b45c02410741d11440c0665050780d1141080240b6000607018202a540c480c1e048440c007420460080b8003810503400300a22040300d803029480b030006990428920b00d0300310b96420000c2103404000404241c14644c6405140d1044001d50000b500c58582600945200c0c8400c600030320040c105860031410040040e20200c001c24403906030354000540000540780c4550f008412401d0891155081c49007540b0098010f82c10561a030003a140310b82c80400c82c0300d0149040355030702d4000c580703040200740c0702691003c0701c0d010440d4104030801c0e000c0c0d000600c154100404d002c80603035070032009061140725583d800000b50000c82c0c16800209118180d1709000403100199030201010f200c0e1401d440c3d00c4900c1c8032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 288413102 1250 288411852 288411859
    0x20708071707210b090c031002030a14010b092b050a0302061503030403060b1906090f06020a080d110d23130b041401060308120406060f080a060207080906031320 71
    0xc800f040451204284107400c2030070002038540c4088003002003030803c1d55500422a0440d000030a000007910b561141401000c80072180e0811541840e40000c024410400d541c3d21803040591000c500100305442410100d04075007103485a2601850000d444000c80391050f401b600807030380001da40c0301c151031495802400c0207001e5864181141c0d00c0b40010b00c1210302d61078020b00d9540c040203122203509000e40c0908500c3d11100300c0c451910940041000c41908010110342202c03505200240404c0191850000e00e1768001c10940041003555030b490050700d0101c50060f08280700409802d81400492040001c540c03541c0049540b80f4111100c0c4611920700201031045100004001c0380740b0390041071030400c0080001c40d40664035150f400da40c1d0404115808400700c030078140f104000491103001c004003043c607888042d0910b40040291501000940902065000140034003040300400464500c040001d0580c0d45030b01f44811010034000c0c40a8080320743c046244048078414030741c60f28940d2004d2004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 288414352 1250 288413102 288413159
    0xf02030313020405041112060a05060a1238091005040807060c02100608011b0207080d050705070513050a051f1a04080a050d0216050a1401020708071707 67
    0xb03609110052200502c155000300a1805200c05aa24003441004c4440400014052803d051038150121003019000380e00c030701c010010800c450822051020580e42e0090f0100c801c6444050214510f070b01300b075800805510380c200c1c4240780c504d40081d01c14060301014007212038250488080f481110010344001e00210301c20300c000800202c1c6608070102d94000d41c070541e58000c91501c00c8406613029034000c0c09032a511482596928030382440480003500b0300e4402421001c2ca0301385026182e90040000200701b04001800a06026080040500601c00540543e2000070038036a8040103000c1611444501c2e1309100110700c0824100030308500d2068150610100e0314a0708540b0102c141074210040144401400001a810424080503032035030b010700f001d016100e10320080242006402024002c000c800040240119207502d00c40c40d09980451070508446159180103070b143c48191ba03c080e82f03a12031040082448072982161000b80703c00001241c440c01d4958604003a8900507040c9007040f5000e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 288415602 1250 288414352 288414391
    0x1d0708010e060a2d120302060a091e03020307080d0f0506010c02032503020a0b120a0203010f0e041a01060f0e0108150609060f0409090c060206100302240c010902010f020303 76
    0x81d51640880d40a00321000740c00c01c0c00398446000b2a044d562020b4041821108030009040d01417106035400401c0c40c0c402c0000440540e00c910b0b0030040d08620320341d0061400c50000030180200201c0d81c8558010300341d207494140e014103038005000441c40b9103031110b06101c0850501c0d4050440025269030080180284100c440381100044c42480c00b40e400a4200b030400002580710303041d442d009403070000c2e1159034600003903920203440391019101c0c0c0302c414410401000603c004001d075000b13582c40c0600107003154640d810004042040c148202203d103c41400010740c0e41c0d04000410b00c40111510343e110f000c14401700550302078208a48590000d40403d004445601d09540100b8104c04010000d50a110100d80400b030980c0064100c4c0010b10f41e0380aa09003400240700d03280000340a1031009003007510b00740c000900d000119100003401410900c50302489404c405421001903250215196111045080c115000c0c00014009a0108214001008006101004891103a004240c641e00032149 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 288416852 1250 288415602 288415619
    0x7052a0306100b031005130501050a0506030903040e07030e0f0601180c020601050d020109080a110103050c04060e040902011b21030605030316030903060203040f061406030c040e071d0708010e060a 86
    0x401031182d80e401170310300c00104060791303006052034003038440410000c2d441d81484103004003d1031681240384584401c0c820000360031000422a0166660014003544645030300074260701800c0411550410703406403c404c0960380200140d41c034120740c2400071036013401d64502418402c407590007051500503044500144424148115030101180c4185030080c1065616a903060410030f003030404607550403c0402c807016540c0d06028070340d00b00e240301d42030626161170454040c0216952600c00c1d40180d484400004c1560b0082111890610241c4500301010380326151100c0c080120618030000003080c0c0c508490740718400e11035403080d9070300640194500b044003601c408032621001070031020012403400200005440380095030040f84210540c07008094181f0b0404142d81442c81c0d41101100d07004200b00040da00000d02044000b019200010300741540ca91203030074081c2580201c0da44042603501c0380c41201420806c0c501c03a0407280d0710b54450b66203c11141d002d0a0064541690100d1000418001800d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 288418102 1250 288416852 288416857
    0xb030a110f04020307050a030e1c0f0e120706021635070905010518090d0311070501142e06051c09030306080d02070e160507052a0306100b 61
    0x210007051201c00a000c50300240503a40100c600f5800a01d01045041d030142e0507001e0507600c003001901920104d9801101640040c502c08002410445030800c0f107290540a100807403403811010789001e000c0504001000c0c0d5071078682c4201d000520907125071016400400090205481c1c19852042221420101909001a40006041d10712011810001031880c04121a03170061030f91842c0030686600d05420000350702d1500c01c1c450342070341603001000601c19001c5003412a02c0c0c886c0c207001500c0505490729400340d00603503030010071070342ca4110039180801441500511880420b012404c8000002c001c840784a96802e048880c0c0d401031130010f01481d0b0040740030749200048140720a40e0343c04141c0c4032a042e9180301c0030a4010a5503110244800034082c400742d0300f07040c168001440c05629003d10312140000c0180080845043c1d280400f01d601c1c883e004803900290081c04981c0c0d480d0320180501c90060b04032110200555600109500905010400b10311a01031415100072080ca85038600502d41d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 288419352 1250 288418102 288418133
    0x503070f1d0c0d090b161d010f020106170a21080109090f050d0f0206090304080703060b0415060329060d0504110d0507030b010504110712030902090c120a0b030a 71
    0x24030116250080500c00c01ca031313690180019000703e00b0108410780d0004079162040080020301c650001d0503002c01e203000c07080d0301d0003803070007100c02d28407008204e00604440d000b0912010588405404081c0002010344401f1b01403a00303000400381079074040c0c040c1030f910703070300500070518a00040ac517001c810740c0b2401031140645036a8801600f260b07900c0e0b06000e1303080e91010101d014601c41c4511160b04019070f0b503000f45d458005525081c10024429541c00c840e01c802404291243c40001c80e41d19150884c100280003403480c1c0d21240d4480e08050081c03d00c050124249041d40c100c400d01245a02112190060300540440c2c60401c0384131281c0d000c1c1070010019110b40045a51007a40c903121440c2104000c1c2c05400688140750031440c000700b150006900c924404c0f4200001c40d50840c1c6104102c9414031f41c80794901182d0300048400781c010309044100603621852880c00c100401d0405002055134210b40050b0440ba42d8580501e4021590341c4000039402d0342c042c075000c800040d80c660000c0c018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 288420602 1250 288419352 288419371
    0x30204030602030106200f120309160b190e0109050118050307090f1d03030115020c060711090f0103030509041d0a0302010b0a0b0724240503070f1d 65
    0x4198a0740c0710801668030a034002000900402e60700540c285440c42c041e10068a0900581400e080d1501496a81c00740c07140c0c44a5900c000102107104c14408100c0304807100c5042c0560322030b4a60360401f2002c150819980700103110000c160b0100c54901ca50809040941c0c141c5588100d20300740790046400a241408800700300301030b9000450655010000d030b40003071107071050214402042c04086020354002d95801081c101401d0b400b80d13556500401501d064032440c0c115800c400c0c1b46a10304925281d1001c2c102a01f10900007154401d020000404452804055640d001b09444064240008840034480070f800200d0a10101009191a0700103101c00410724079041c3c04c2d46480d00803181442c94210003103026030765a61951707034542882c20b0510014044140e40741e0400072180c94032401d2101c9d00303136480300045c00c4440d0800e85486581c4023800307501d110801490b946036120104038000b909030140c284644a036034000100c0b201d0002d454400c2e03590040d4904420241c08466826100f400340c0303180c6070b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 288421852 1250 288420602 288420607
    0xd05060612010311040e0609150603071e091a010c030509040f0203010905010302031c080609060a0b1303030801050a030f02060304020607020904060b01030b0105032421011a040c0c0809010302 84
    0x50780240400e4a80c041d40c007a40100b141c44292800700000c40300310b106e130344a094102004224041501144030011a81c4d01c1000d88119a5000002400d09060740c0000451000407003a09000700306010080f426518095030030044a8241600c2c0c84840c100b4541e4640042c0b00c0194640020703114001814a40c00050030103d500141820303404240c0e08240c02c11240c643d42ca100400540c43c00300014010020404000d10041e41c40000003403529100600d0b060007004080c012906980307030000f101004115070890b1a80710000d0b50903850051409100942c00100a10004a41441d180201d441102c0c2d100d0310103c09807aa80c3c0c2405103070b4000820907a88550144009005602d0300d04410f84a14898030b00000d800c0c013032100140840d441c03650118108142401003019a10b0004084890108441503e0340200005000a000744194580404403096812600941803005400c0345102040b002c000141b041249402d010480300c400c00d8940000340c5400c0442e001c2402d0700c00509010700b040c5400751 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 288423102 1250 288421852 288421867
    0x70c061506080405010c0905090408070f06140f061e12010b03030309030a1403040b0a0906090203030a181712030a020408030f0d14010b0409020901020307020910180c050d050606 78
    0x4008568049400b0903290740c01c200c1000401e00c2080e01d440b0302c0e0b0800141c03050074200031901495008000030f0103580c0c0003416034140000030042001c625840702d030600c0a214184a00000030368181c40a06801822001091007444c0c0003586410204c812028220280b00c0c042c20042c40104612400c40345d5540c5825a5009440520040d031050b5114001150b54000000000f4583c0d4210380003881186e90600030700c400101c0c0c1000389500040544000b280f41c94603800c12000800050301300079410300c4005a4090095080f84050707003008004109035a0141c0d43e003c3e0405810300311705040920307405c050709019011007900c01841e0848a0041e00600700ba458050780e51450740300c1112000e5403d40401e001400560742c0c0640400d148031103448444a515081076010300e801a4050003620540100e07980000d03074400c00907200310075002000a16542885108000c603600c0d00d0113181851841d03800c2d1034841040701d000d80312034000d150b0380381d41c60044841098001440c02400481d030040081060a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 288424352 1250 288423102 288423131
    0x60b09311406060102060c0901020616120c031b0201051b0a02070e010905041104020913020d11120603120f071b18050702010501090603112103070b041502040509070c06 74
    0x9107188100700040c1100d0400d200068501a001084018448420480c01d02d881e64081541600848034101421035101d4034941600c0384003901010001e41460100d018020aa05400c00000100100640848481c8c0c0b000300700e0903681d0490311201401144111810403018a000520328003125105590034151640404040c0407020790010101c01e85580a200510054400c22828030790112021460b012141c070106080c2c40c401e40c00c1c140c8099010034407454182e841d810041c02d014801181d075640e41040100e508041c5420f507102d40c041e00c10030303009801c011003440c100c584807060a11850f080180c690385440d0060760012a000c6020303590000040c550034034a241e04590402d40300d01040c940303801c1c0c07c002d00b1a601640a43c01d0542499010404075181c0322030452034220070707140d8847d0f0302e401c400880d550b5614140d440030140b0001a00e4010300c49c0900050f8000da1254609068101a010540c4140e00403406841e520420140200b4241d5014600a1401602c1403902103402179104011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 288425602 1250 288424352 288424373
    0x270d05030a17010608041109100801061217090a0306020d0617060414030a0903060f09080f07060b0a1401080601030902030d09030b0c0304050d1412070507060b0931 72
    0x4603004110407078407148800c02007645480c09413001d4030b0001c203245059103600c0700202c25141003c1c040c81e22400031428951126001030007810108000748007603035581d0041c8400150240013601d1003034400888260461500c000c45016400081c07548080d6403c5448940003540b002d0b41e0109003079a50b000004403070501c80c03050788100302d40c00060000fa250900782020f0500003180b40082640040100b902c40e00d0300801c0400540703421001c005694002b404840000f01040300b8094400d82002c03038400c1c0300409403401031080621440e824420440d9000501c801d89846024080c030000c10441a504154800c01550364801c0c0145008141040300e50046070500850050389400103072a4402803044c0400c840b4184d070002c0640c1801c41c03071890507480d1035031200c00d071461a10030402c8041c0d000224050b12000ea078065001500494041e051401000d4140d0348940d20847d1100d0608143c0381d9685402c401007449642000c1c8602003000d9118050200e540c0c0346501c1780092400c1070b012001260300350a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 288426852 1250 288425602 288425617
    0xe09041110080702191b030c030c060f0c0f08160c14060c030403020d0804240306060c050c01080a0f0e2404050a1104110c070501090b270d0503 63
    0x40c2103000c0c1a01406a40000c20000c0024000c2650510040b40d0307000810b240012020344100b507514010b46450080440289040808120b18100100c140440e24090303c1c1140c0c810310540c5406981c402043d1090002b043d0100040b51351001187d01142d503200700c10750200d12801201d45003e540702d203054000391a108007640c1c1c2141e240000c0c000c1244945105490711002c442590030b0000b44801c2980e06d01c1a170000a0203161549000d071300f0084039005550180510ba030340c1210351021071040e60f28403105544d0000c0040c4c101000002e0242c09042c8440d8865049000740540d03411981c01914511409400300c44c00656440483d881802c107407007030b0701c046401c80020b48100c6a039107102c1a641c000c17082e00c5880213465401840002200003c2c2c4040140e803146048580096501c001303801000100307180311200000240c0e19134054000f203002015900240c941407d000c7d161003e003080c9004080792401c10b8005540e14800308010b414003040e0380c0e180207056081150407956080e082d50413810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 288428102 1250 288426852 288426863
    0xc011704062d0e010b03010908071403120a0b03070b0a08072001060e06180907090b0f04020703030516090602030a030207020406030f080417120906030402041b0509010305010e010608160e0904 84
    0x841c101d1030f850207000e000c4200900b00c0090003012000d40701c240692088140007849007240c50b08414002d5410300554041c0890b1a481c41d0803031411640e040d01500032900305910a0241c000c0100f03081005806a404001150340c580c0d0f40c0c0c1e40e80c0d41007030301c0c0500e42d81c0310800c550310746d401e90300042d00007401043c01606090881c00142c1c24080c0c1031103c1800c042e00ca1100001803c1c003085070340e8900003980f400301e50840d500410036540d5240414400c1c0400214030f50800d0000070b4520905801d60441c0b40540c01550131044201030307102e0100c0d110801401080c1c0142c00400188031014881d0300a080c419000030400201c241c0c1d0b03942d549061030510441141c621501080410418004404092607070610f00081c00f090200c03140c85004034491a101140f0a19000c0042410354a0f1680490044511a0511892000d0750f85010382035030418080580004d040800105200c000028668101c840d0768641a05540750124102514195540d1480400c0095101711ba4a0b65842103418002d50240307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 288429352 1250 288428102 288428111
    0x15020c070b0307111c170703090c03061416020606011110050f07200c0d030e0310050a0b18041103031201060e0a050409020f0603090102090406080c030c011704062d 72
    0x41c3c80b482c0c18104150103a050817010b88107140d070311641200021005484460b1041d034036568001080d00141803403200035105000a44000c4100482c5034022400c000b41c1000212003561080001e0300c4441da4420700e0001600304001145095003c1c0301745075002c1c0b050032f0588010a0104031514201c40045400f03224001b035020074030007041e8001c000074800000d064900008010041c000780e5442c00c0320800d842c05112901c4c50802814400c20421002620040540c0d4410300c4044a19000e0314050310341e040340a10f440d41459075460300508220401c4680030150580381e443c1e440c0c1080000720101c5140d0180001c008002c1c0b400c0140609501a00d1140c441220055015007404984611500aa40120b28060440c8050380d21624090001882240d409031b807135a0380d04a290181c007407107000c150802d08202000c508443c0119074204000c04c154221140301e50581e00445081940010300984600800045008660507030021011140f00c0c4d0707000d611107400401c0401c5418000003810417420b595 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 288430602 1250 288429352 288429377
    0x60d1b05120c120a08041412010c0206100b040503120a0507020d050a0b060603090c040f020409060f05120604021f0504030c0b070b1021020d171305090415020c070b0307 74
    0x1002c1007024480e1808001c00d03600d29141d880c05c5440c480c9010301090005000f81d041003a07030b2540d142c110001c18090007400186800d42c006580d8640a0710b804031803c62910000c11042c0056050310212003004000707109000300d162154a40e43e1140340c25800308101040aa405031700c500024441c0f0500c2280244440009400d0281011001a007054070802c0c04000707200d19440c0002d0002411001214009a21143c03441114024410741d8400e03655642040310004046c604540004200e440940350a00700003642036110f0303141d4a003103500035072114240143d2011400700320b07013030034010810341801c40c58540c4036101c0c500195015031006000300e02c0040c0e20000c00c1810f44003039401491400000001506248004018000c01d4048004c01c50381402c0b02400d5640c2e2980000645070003588010017004108848885a848035000340c008011000001959090810425109a0f0803403540c44440c1c034040c050f10069400020103c80c144a4040c01041c401c42501c011401600661203805c6400c86 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 288431852 1250 288430602 288430609
    0x120a050c0d030507060c020f06010b040e060d0206030f0406140f16020a030815011808010b01110a0203030406081906090b180114040e10020703051b06060d1b05120c 72
    0x202401150048880707035032910001c0d400c5801d03200100c2c1e02000201d141018440308031f28011001c0703850900d6200f81d4000040000341d1900a0081d20904030000b40c071503451206100d9040c3e41c40d0b0009400075000c000044581c0c250001c020f030400d115000100f1108621646450044800d03680c40e40c0c641806800d001164052070100d00001c03816001030140480617490242880f03800034442c081d200046081030045a11441c0300d44000f90811000c4c15010362645601c60007003803802d00301030100d0748403051180b54000000d284a00c196000300114a45070500000719041280a08182e80800030b4a400e5158000c00303004640140c494654005104c503408010050480322401c0030b011105504401440b038600410b1010741c40300e4086e82e0100b000340c0e0072904903240050006001010038408a8500105640034008180007070f09040310302c94003001000555190b01e4281c40d450352081d5000d02c400300081c80c00c440c038108410200c0508013000e0303454000c40ca40c003640000e100701c03d401c00d500c003800340c3c42c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 288433102 1250 288431852 288431863
    0x1008030706150e161b020301090c050102121c020d060b0a0819020705060604020702180f010e0c0301140f120a0b0901110702010210200d0903020c030105060112110405120a05 76
    0xa525040c221007410514a05921404490009005c0004007440c0300b003030384003042d400d000c500d40c090000c200c00c50860400781700e400d400303005160050094111484a040f180429903500d81e078180c1501d2042540d201c40307400250320804c1e94008031500c94400003900c0c0307099006082400d285488041c5145048205021066010385510340201c0c4140300140129100041e0107038004410360740141ea60030a40001000c1d4813044030880500c00e403450800948541410f080c5040710f11024005000d6114103001c1c0b00f40d40401d0160794100074004c03c070100c06142c0710740f170040900000f1700306518200401281908110900c101078136090034220038848245400d205031160030070b48100c4507060100340c1c0e00007522012140403c014040d15000303034541d11200440d5407001f101010711070303669401d031020481000d08104107040d8058050054081c071103040c180110791003080140c1d580742d6060328100340302005040988005030001da01788004201e5448072100c000b910b00c2420002c040e10201c51034294030b020f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 288434352 1250 288433102 288433109
    0x30c0c0c1401080702070614031008030f0d0c08040209130c0b0a0201020a120509120c011503030c1b060212070501020f07230c0a0b0901020307021801060f1103040e100803070615 78
    0x1541b11081c1040201d82c0002480b10400e01c81410943d251038000702803107000210341210320303140800600d0410101581005200c0c03450352200511010400a40036a049a400c49010307412810701e1001072408a405860300341c00601c100010800140c561807014015000f41c100c1c403015039400a00900403682220f240c1003009000d180a014500e40031400c140c44840a42145040c0d1034041303030340398a4890079040b5490002c0022110f244042e940c1c00c001704414005401902c4504c4001d07945603005880012107010b40318580c004101b000b10369100190b6603808810107440c0d55500f4021a0419807000300213090490080c14903d0307400b038480120307041c0c103080140042c08070350041c04611843d0710f44100740c00c00c941d8020000c54a4803807610046c1d0461040a000035404086240d0700da00c0b441703d200314981651450340d1117840e851490704040d00d003480302c4290000242c1c418041040701049042c0c5659101d1a4000044042540e50700d026203550400e4804030703042a2122031140c41070003c111b045005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 288435602 1250 288434352 288434357
    0x6080c032b11010c050406090b0c0723030106031505100609050f130527030f0904150810020c100506010509090a0209120a110103020a050406030c0c0c14010807 70
    0x21007007072a001003106201000105a104040d1000a00d4007400c2c603544a14060340c000d000c41066400001e0090b4440d00a0401040070030f400846c6506030802a41c9404a880c0e00614082c0d08003200103440040321010061400b0b40101a12415102070280704011446840040c0720581041928400d440008116861480c502081000b0f060340c002d4045080b60b00c15030310365446a0b9180080b40100c4a90155040518100810f01c00d02c43c1201032a581c081250601c01d8072848817103003c2940340d02c645030354140004402d002401d8a850183c0c4944180e40f0514451079140c0e42d00c403442401d155841600d0308643c1d41c0404d14008403102401441c412a8200e0000c00441c544100060554024001d0041c040d04e68103000410b0980254121410101c00a10301e5a0411030000c102c0c2d5500c84419044911100000f50354120b94020f00a854a0a105031a0b1302c1c01c060134414210003d02d148050041004510100d140200f000510b8070009800c02981d4424a11002d0340050020391002d01241304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 288436852 1250 288435602 288435613
    0x406020703050c0111061612141504020c0304030303020906040e19060f05060706090512040f060e040207020a2c07050408011404171305030304120201080c07021324060306080c03 78
    0x350400c001c074074150b010403900e80c7c50800c0c000d025070807a074a0480610040b035041c90048441c580300c00c01e00c080c030f10038042d01807040d822145c00310500c0207070b01400081c05502e5105000500009000750080c190201010300360070309007035488002015250090300d10000a42c59403203040034900d040e00500b40900340001080c111070b031404011902d50b200d501000383c01c0d65a9001c03000100b20040c8005400280d1152105444c0c40d1201d06180068030588100030204204406403500b0303081c80c2c0240c9041940060284100300e1405c0181a01354981c10307a480703a84402c8003490500c4020300302d41d103030046a8a5688646590901000c54216510340c24560f80c40c10140d405c05c4001101d1000c2001210035604115841e0700c089410290343e44204d4102a505000209000c6481c585a425591080c2c0c001d0b80c0347c1d801c40e16090070b0b5080700c0c41180c20180d000b400a4020422841c2c041e0400b80f42c03291000c1e0490740c8200250720b00400340420307400c4540045e85072a004c00038100100004061414100e01808 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 288438102 1250 288436852 288436877
    0x2090c031902030a0f05010f0821070210020a08070602070c21150b060301080120071a1b070c15030e0309040b03070f0306050708070e010c03031d01020406020703050c01 74
    0x1101030352401e840c1919281c0000c001009007000d17820906140c03425560611141d40c480c074840350645424041c0d100c0c0c51103103203403101d8050b60030400700d403080c6110403050f0b25046264080c4651303500441c030f505040d88a812010000a10f40000418101d8054000180c4515061424034400b041e954003601e030001d05606031404040000105e5501c0c194400c2041514480040740c00018049503080c1a921001c040000507003154190044420754086444290b40c109100c03d03c840c0341c0c02280c1c00a4441c40ea84c480b0010345c501032182c07107038000000c1200c80c03142d103101c040740500d25404440c0c22503440100e05020400c0074800382d038a00040f6400d05050012281c0031030700f207070f40b400b442660620980c1c8820003080251400e000800c0035180e403400000226849051601c09031000344d40100002e0204800662100d200300c09001960350141e503600308540040c0c0b001c6000d4002618002d01000702c4038802a81100244018001000d40341c02500440f407171070a200d4102007090510f24181300b040704842 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 288439352 1250 288438102 288438121
    0x240501170103030e041d010906050907050a0b12150d060b01020127020609060c011112070806010c1113150e0c12040201080a022104150905210708070b010302090c03 72
    0x200c4c0030441c141d80026a108501d2041310001408241d108041e519044000d010b010043e0440c078441e144606c01c4580440c0d8940a2160841c0e080c0b01d000c812400134070451900e00300e02c3c11559041910310381e10b8034080300801e000074400381d2040c4081300c016a607a44407180d42d50702801000b55245070f03044401c10011341c03106a03005c1a60002d0001740b044000082107551940c3d00800d40d03640100c1386000b0070807003c104000c1000c940c403544400c035003120b04200180032640320745411441420b06a540c5e07200301c040c580d640c0020080e41da210b103030b000299104504031001c5500c00e691000c585003005203070051810740c036102d03045000f030400c0306103c1c000c0020181040c5005c3e8950703003065080c43d222100390340700c92612000f0b00070345096449900b10788102c0c1c1d00140f605400107004074058125005008000318082044481d50500100b86400595503510958a140caa040c0d0880514040c0d40c82c21615969542043d48180c0080301d02e0b20300c240c018410b40c106100c000d940310006044251031814640c800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 288440602 1250 288439352 288439367
    0xf06051e2503090c03060c180801020703020a020f010e030a08040f0906050f060702060f040b09010905060a09032a09060e06060c100b18040b01030201030e0a031b020424050117010303 80
    0x1c00d15888442c00381c10008161840c1e401160822020002c800740000002c0290748a508900111402510b0114190740180f0898030000d6154009090303001650f03080c019600c8880c02094140030300d10b030f00c00703285807002d100c0301c0d403410b00c1400c030155140e051035072800c6954010b0300300e1a1244c0c5070440034080d070307100c0701034100308880115105074070744c0c88920000b60075110b1202c29500c000300100d80044c480c11a2401751010000c00d0301d444a4a80d00d40c02404442d005891180b80095a07207241000400c82c607d4110304ca44001c114000e050b1030481e10303614241076566002c071010ba030780c0c1c40c4104513401c0d41c28041500584101c90080c80d003150b2400003a5100c161400c0c016042e40c2c0c8400295065441e0400b00710302543d10704010f4650300e020304140300c40901c244800c1c0d0110381001c61030124050007003004005641c0c1500c940e1215101040d8003190f0304084c000c120303045607a42c402072410004808001444130384d600c02c8180c1b5035041000040c207050802b80c00031155880a4014030009411050303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 288441852 1250 288440602 288440671
    0xa020c030d1d010e060f0c040f0b0405151206100e0d0c08010c020303010f0e07030b1305090114010b040b090607081902070e0103170c0c0a122f0603040f06051e 70
    0x7481c94580c0716440303040d03da42300750350100315601c0d08400d000908130b400c900940111142140c1280066154680980e1903201c0c1201042e03d001c0c5500c0020081d00e001000040c0010a42c9401450841e5000c0400e8002403031002c142d42c840304901d41008a09401d0041070440b4016201850655140800d44a47d5203158002c56442004110000d902c1c14440e5001c0c12550310010100e842001402d089000140000d581d20681035007080c0305100301d04442041d480c100d4010105062800f840c101800050b83c210f00c5400d544a02c0800c408004102c200000e0024a682c4a13103800d600011440060701c0d004030f80c1e1204030148070010040012904c5a21010011100548030943e03030031382032038101d003031020440b002607000762903000c04100b130f43d4801c4080e51200e128460700f80041004c50310b200560700c20b01c0000715843d51401e0300b4544a007451400355070000e02c110b1440b81503980715074500b802d4590441d801d10009900915103200c8444101e50f0940002c104042c44101c0f1044400d211031011141d003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 288443102 1250 288441852 288441871
    0x60a0209030d120e060a0c020f0a0c0b1806300408030402040e031902030a18030b06010c0317090d1b0309031b03170306030708070f06080a020c030d1d010e06 69
    0x1600d842c10035180c200d4032a50320315200356174041c68810190f000400c40f0500020041c030513103880c500d10000c0042c00200654000b00049841e5140c440c0d5140b090f44194421b0801454803800056a030302d585000d0072601a5500c1d1121440203400c1c2001c01c2d0082e2081000400d001030020301020802c00c5048a41043e010344001c964410311828061441c800c81040f0b0750b0010340c00c3d83c003202c07641d40400504040b0b03000d51390b11440103010034840050322015001c041c1000307a02c1c10104203a50b000300440d0390068841d051a685038a071002504d400340c10216001c1146400070030100e48003641c0302c44d00b88200080118400b151039603d44008010300d8860000074064210703801380c451103503d900e002d05c00a581c40380402500a200c40004072454100f034a40340e00078480e17481c0102e000400881c01c00c050b61640c0c10b02301c10716481c015003250311a40103480c1c540300c50303800c00c02e01c0d08262041c4003c056120324040301143d0a44d036900d00c80d101c410740c07000c0d884050b4034001d1001440a0045080341d040f040e00c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 288444352 1250 288443102 288443117
    0x7020f0105160c0905060d032c1005040932150301020a020703050f01090803130201050d110901080906100e0c04170a030207151407050a060617060a0209030d 69
    0x181d42030300c40c850306080c5148a60307000108018020765014103a8003500f00c24040f6072075031414003440b45414540100070414243c3c0f40d40c803407503d400c0720030946403846800950410a403c08582d02e401c51000e90800a03400041c01d020480b800c0c01030461742c02c460520700e85107855010407102c000340d03401e4104403424045804501000c1103403000c18100a8010000c540c1c1e100c40c0c0c10040c2d512140d80c0b0003200c5034003619400007807240042c030555220070b4001d200146141d1b41c1101c91114458612400ca05121003072011a003010f10b68031891500f0030071000e01a0740d0704003500c009440c41c54001c2039070072542d0181d000c010555100050200403501d4001d0410340795203c600130006980134940000d046e41241c6020304182810001d94080d525000e5001d84051035214420032402c0d00d0701541c02d0000c510003404919403410400300074204036004500b5200c2000d0340380e44107000e84460b68492103080c0050068503807060f20a110680d0403005200d000c40c41d040714000481d8032089440c40324024070090 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 288445602 1250 288444352 288444379
    0x120209130b01081614310c0909180206090402090d05062a0c0604080a030e01050a020307020f01140c1e07031d040504020108190e0a050d020c0d080702 66
    0x502102160450384100c0390500ca40c1c44850303040d40c40c0303c4012481d0b041e00909400103400d600300b0a00325125a8050581c002200c0c100103c50f1920700358810402e0140c1d01b0643c1c032100c400c0c8130b20510518503460740e100c0a00f02d01c0d00d40b50009498000b01e14003802180c10083c01d005907101012101c80305400e40c2c0140e29038005200241092280341c002608502580c4100800010b00e8003650b207038003145002600702d4041c0029140200c1c001d00c140094940d0022000c43c02182c19003000c0e015207076003454086800c0d1030000300a82994010741e61690b2141d0003006000e2401c0c1c05100740c1c429003ca0b08001c02070350b960040c0d0905090f40290039030100c142d0014074912121a00728030303405014200e0308150b03038072103591a0080000900c8040d40c010701805405803203032403a05014060080d60140e5811340151102826440c00300181402d05c10300c41d40c1d400d1503041d1002c1c1070150a030424090b8004e858060496040a03007001d900003801d501c1010f2524110002401c2442541d15030740c0c05850340c58401c0c04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 288446852 1250 288445602 288445621
    0x40303180602070b27030a080a0b042306060c1b01020307080f03041127220b010f0e0f0112080d0f05040203010e060601020d0c0501110c07030c060207120209 69
    0x3030540e030141c03160707000040754070074820046080c0340542c07040716036000b500c030020708200c454624248079400345400421039a007035588111001c47e044100104c00240c40324012001908440c0a101d00034225000010b1003c58922030100b00c940c000d009035049032404003202c2a0589540307804039070724240c950101509000c0e034802c2080c1c0b2006a403040003a0b50f5803000480c41c1007030790401c4500b00d5148940250f94500da0402c510145016081c1c000f480f04801d81024072158142030040c034030b118022340706d00c80f400070814603911540b1302d074010604442d19506011841403640011703048441e21041c0a4240107800c46000425811921000d481380313058500c1c0d1800c030800d44143e90720f0044079400c18064403015081036000901a5100701e000f0440c2d91403800f4000e484010882c0c4c0140035800c20140c403042d45008104101145110340d00018000c101081c0e20351040c1c1008844070410390080380b040c000c0051204c08078000d000540010665149005a80301c00720007a15030003409210040301041c0140c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 288448102 1250 288446852 288446891
    0x9051c02040507080109060f050d0f0215180f04020306010f050a02030f03070801080f120d09060603020907080610020c060304030507031b06021306090e0c07080c0a1b0501050a08040303 81
    0x6034014401c0c0402d0810341002410b9040a0203076004103880d00f100044c00c02105204001150001b07861016000e039681c80380842c00b05032004c10381c5c02c82c8030380c090340103542206001403140c0119141c14040495a800904c68008803d0f1000da000f280304000380f081c80c1e0380103141041c02e40c0903860483d42e91924054201e080d4007590314035007000746011050188280c0c001030314a040e1000082100c8104581c8000305644060110038103921060403c0842407a101070b0300040b1115015032070115a295982c1d010400c40041164404002003860b01400074030301e400450100441c540744001c00e8010140380002d0041e100c0644020140311001407060704043c0a14880000b00c44610f00c0d4181207410b5007070803806507200c0c2010a404030684800031a445014201140039a901528092175039915004089020f03481441c094441d11414041d115021000304184194a8820029605c0e11240000c081400c4083c0c3d802245c14403000b400725050403641700c90300341e900641503c2c01207140154071840b0b02221 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 288449352 1250 288448102 288448159
    0x3020429070f05061b120c130807030506101707051c0506250512010b070203070b0d14010609060512071e021501060903080706050c090a090b0406150905 67
    0x502c001c0c4441014031801086140c450512481c441040c40b0301a42d24864501c110840399040e000b510001c2440100d4040141600c150100e0b0310724452600c0740001403602031298000c840d190310200810000c0ca4585404000810b14001a00e5032040076085654440d0540d0040901404144143c1501d011200545080e0583c02030255140d40c18902165400b0034404c540f03585508021b200010350143c07140003217806000400940c2c660740e9080680440d40d90b44021002c0c1c0c0d052081c19804a0075000102c0140800e00344010000b031040c40f100303440600b2001c16030011090040242003040303200d403c0021108004141140241656140c22040c0c030200c49050900c840c441c00118000489500040c2d1041c0490140c2c1d9072814a0ba030303843c0308682e0b1061354003000b8020b540902c00c2c4000200180c0002b9000101d15400c1da0400c01048041100703c103940c1c1c812040c0f81c0e152800034006051512403800500301c07003c0300c0320b514a040100070b0300108581c803826024260340100030350441c00e6aa0380c410710 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 288450602 1250 288449352 288449363
    0x604090504080f03041a090606010c0b0604140709030c0803090d140f06090d080105091003020909010b040513021e1c021309061b020303070212030606090a0906080d0302042907 77
    0x30380c103007810000700d00c11050151000c3e2106c1a070108141c0c1900080703891003030905079643e140324070702c0b80c1c2d4403c65100003070705507500a9110060b20b6286106014040d216034182c0e66083d80c02071071818490070780491540203000640040007510074036120607420b5010740340c10890f69160202000c2c2d12601d010b0882c031900882e40950020321818000200c2c03070701c0000d00c0380d40d1660601e0340c848040040045091750a0700e0000f000000130401414007022259101d00100f0002075a840280041804e0b184100c42d5040c0034000754034050114a0100d00324a405440b04900f9490600720202003095100090740c000c100074803400307030032046541740d00070700c0141d03041d05500344001c50003868050040c00290b0418402d115a50900705c00c018400001d503845803100d03070b00070243c100e0a0f410312800c039407028003281d42001d42088600850348401c6065001000402070005146240c03000c95401e2614001440080600402040107a89035141040880742c3c26112158004804140c0c0b501007845a82c2e0300620 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 288451852 1250 288450602 288450607
    0x90b03150301090303021804110406030e21040501090602011b0302090406030f0c05041404030e010320030f09190c05040c05091206070f260c0904020c030c16050604090504080f 77
    0x10964160041c1145689607035440281f180080100016200305010700d0240710720522080100500c290040030b01108007601780c41c01c080d03180c61080c904800d54208400c60b038500240070040755902c10764840061180c0c4c0f008200010007402c0f0703403c01d842e1017508801090f40110342551b096403658071144c011503111800b158529501d2804070f4042d0803500c5180e00c1640b502c0380f00c46450f004030300414840c43d4190356058403002460010340040c032420031220300503031700b51000740d5001542200640c060807031061850114070380101d0076490078a0726505800c40c00315188141c0c1c00070b60400c20010948a080710042401c0d828072008644a004012001e54409461400c483c5c1184000c280180907a050756282e00140c003d01c8425510705486107940031549a0360001e00c0b282c1219a0700854000e070a24290740d00d0720040000150981e000004910001e4000240080349404108044884c60030b2800f01a0364061038480000c040340154480c1107111360f2603000280422802074100c501d140c040c00c00c0243c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 288453102 1250 288451852 288451871
    0x91203080424230702060a2703020307050d02010605060403080c011103180d08070804020d020a03170c070f0509160201061a040810050906150d06050406090210050406090b03150301 79
    0x601501c2d500b8590704800c403094010306010050fa040103031142d005a00206050b44580c0f00c04401080c00e2907140f4610180e00062012109505407100d400c54041d5006640301d00300d0b070a14a04001c03501d10345006580c0341c048204203d0326031009072800c890f040032501d5102e1560300316a41c0940001085c0006050f0000208aa005100e14600c802c5c400740a040f81c030100800c440035113490405442800c003284071840003030700500d070207204501c1d050700c0941b0300d0558640d2503483d051380b00c011008002e4414000300d6403045501b4108a024000c00446586040b00751400c800300c0c040040180c0340c00e150000ca088982c0e0518001d400440090513003525280300070443c1c046075241a0018041d01e8031034003481c0030340d100c00565400341c0344c040c003400e00c05032015031100d188402010180300c4c150b03a004980d03c0e01d8a40420414401c4034811400b66001007003a050910420a400c2143d480c20300501ca003e000c140b0890794007803599000d68901d10b500951341d4583c840880e80f40d03514016220350541c281171402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 288454352 1250 288453102 288453173
    0x2100f0e0a0605070308010f1a070f021305092e02030403090f0605182e02070e0a051510020705150c010504060b1201200a03090c060309020906010912030804 69
    0x40280d00c3c000d40c6d134490182d0700c901906141c2e000718803802c80700c6000c00c807407102e514140100400465200f40c01500020203242c2c0400c0034520480c0c8140c0f0400d95076003c020b4540c106021102041002c40c08005000100f6410340000600056010059540c08000101014082c02e607500141901c03d180840250780c5800c001c00c2d40d4002d01c115001c1e00c0c4011360301d1100e420001c00340040d80e010001e04d01d03a10741c80307241c0b6422000c024442141c11840340300c5c4c000440b5a4540c06090041c1c580300d002141518003000d921500c1030600e02c9840c001d54414203440031441d0702007a204180c440444080180c0441002d1001d8140180c4180b45125460041400100100d0340d000d40007506082d5074603012054580f00c40c0e403c039284091035540ca81222181001310381016401402c4864203410001100c18003501d60004401c0b440c1c0100010a68850a07801036160000390382da13101c102464181011030601e408410000058100101484882400302d404c1043c05051000c803144d0344a0200381e5210510707000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 288455602 1250 288454352 288454357
    0xb0a09020a09090e0a02090a02190509120a03050f0c0a0204051602010e120a200a1515030f0303020c010902041b1e080612100f0b04050a060302100f0e0a0605 69
    0x40c4080307001028000342c0006180100741407001c11001170002c451082d000d01c40a910700824180750709900b04948803900401c107000d25a00b0a260b91400c0d02c1711465001d1102c0303085030708143c01c10b9030310140c48140040d03402412614081d400030400340c1c0f240c0f510144185070030701c0c1d407000035801800d0104010b4048040c45c001007003014160300031702166030380c22421350720f640c019041a22039000400c600c2640c240904d028035a00e0a809128200810580b09414104420b500d011600c02c01e606901002400c050301642e00341a0203c56461071941c07171656640803440c0d40e00b000400f49500030651802c0302c0700c01e5005240f40f58001d0310074403901e160b21010401e008800e071100300106070b402d00b41183c00c400c1811207012080c0541c03103021043d00c0310020007100005070000c001e45841040b40081c03522441c3d00070304070010381114000c079000b030f403000421098800c01491003201c50300d001003c01c0940d94240c0d0118980c455800d1070403d0421405048940f07115000c5600d80090840000180581d0301c03100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 288456852 1250 288455602 288455617
    0xf03020706181b0e06040c021c0201020307080a11120c0d050411031209210a060204080607080a0e0604030305060a050301060308090907091208132301020709060807120203010b0a0902 80
    0x3c000c148000020501d150f990064080c401d501c0c003000001030040e0800f607100b00c010300d420380100d48803000c4285081101072001402e42005035008401c2c441000e800201c07268000140c12010310080721900b071060303d0f900070341c064650b405145c0d6020414100c9e440c42240d410242c0044180602d107050f08020000c4030340030403082d02a208140b000b980c071304078040c166103011000400c0c1e9000281041c200d0480803104525a102c1c5016100340080003403070320701c010300041481d94040c04503440d000710003510407040203065660706400c250300c1000c03203075001c00c0c8076601035818280003c0070344442c00407905402e40ea4004a4156203050004401e00118101800c1c1210040340c10304000c1d603075440100d44c081707824800e1619100d0b10f00c1c050300005070310002a1829040c10518104c000d81e54204100f400c018000c00d4082642034a0924009964103008a001070410a4028031036249044007941d40c6001c5407013a0080c400c1e08544500c01c554081d0004c81415000404500b03103207440303401c103c00950165070b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 288458102 1250 288456852 288456863
    0x50a020906010c020618040209100e01260403080c13030f0c05060708070f081207180611070501030b030f0304080709050906060d0f030e031905070807050f010f0302070618 75
    0x1803041d40c4078910341d581c040e502038019070901015040c000341012010359a1b580c0a9001d0040c2000350311200e500c5408001f241d55100d40c041492000540800e12400340c24144141c1807420091400070301c001c13680c0059142c900005241d440d0710704090140242d0090341c00803c41c4030000805d00100f0250889100e00408955042a030b4880c20002c0718800d0450007042c224050081e40003041e5498540f880c00c50251014928003003000340000b410045c101d0314400403812072041011084d400c0c803509070141250b1300749100090034107408155585000d11501e8100342d200c14046030941ca042c0305020a9203004400c80c1e49550b16040e0341a200d06050144484491500c0b000800042c400034503107004a10203888004009016200c40f25401c540d940d094003403140314441e00405071410410700d0b00e11800c181c0359041e080764601d0040d09090b11a4400b01103544601410700c4240d480c210a080c5105090801544c41c0b000c41c0c406030b02902030507201821017880d183c405200c4c10183c1031941206481503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 288459352 1250 288458102 288458119
    0x10f050d1d01140901060f0605030405010603080301030b07030b0f0303030619090e0c0111031c0c03020c060c0a020c0301020408121b0106090c0e0103020c060117030706060b180901060206072a050a02 87
    0x15413a282201d441c0e1180030110000c4a80410101c1e008800450704180548004038401d626a22500003e900a910440345c03145142c00300820b00307038980b01d41540d215080328041c407004008000207945e40405061a0b21402c0703600c628880c400783c0641c42400908500c24280020601c1d151915111415280c0c0140495128040e054101002108603110a880d05e0000e000095003890034000501c200103a01040c194200940e840d424010801d075803003610107008981c0c0d43c250900c0d0081c1403c2070b80d00c00c980aa030041c0000e20190001003201104510401d4005844079070b80780c05130444148141180140d54605000800c0c008515003140084032081d40b40e809a6442e040011401c81c0316068103810642c00c204014440541c10038110b05031082d5000c12203061068586400d021280141d006180c00003001485040c070319480c40d04625030031400c60303a948440d890020041c0d181c1000400f003008121555025416005000a41060498200176403040300c41c020302c4e04941e2800b030650282d1113102003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 288460602 1250 288459352 288459361
    0x6040b040e011e061a0d0b0103090f0c05010909020f0d092108011d0423100c03050a0605061905030c1902030c0708190f2a0315020306010f050d1d0114 66
    0x80c405029410402100c07071600d1b0651000310280140603881030141090784561600c1c0c0894465042c0a007114020300d61145400d18000c0050010341c4a0350000c060107005001107a03100c0918000e0310101c07402990301240c0d1004514290900b0310b44a803d0403480d00318615020f0100307921200c514107030782400402d000c0c5441641d08030500c8072021a0001c1960214185000107264000004612207145078211030450040d80b45050950f54a04030b5540000d0392002000030800c004d0050314000d2030b05a0b0207c2c90141c04940e00c01d501d40c5046541000d1210020220b010b101070740e4100c81d12080b02d545030104a10700c580c4000e460740c1c03040d00f032180c2c940305020b000300c1c0d0742d2804901e21041c4a01404041000f001546da00c6001121054040c1c50400c0203c0740d18600d400003800118070340c600d08450024440c290f150203000c0c01c5101d0281d003511481401003290a0b60020401000b61001e03090031900c510f40000345401034402c1541107032000d50010680314811700305411408048140f500704c204103559 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 288461852 1250 288460602 288460619
    0x406090509030d0f3e0a02030d05060a0e0f070e03010c0903050c091014010903120c031419030506040b040c050c070e0c0d02030907080601060e010e100806040b040e011e06 75
    0x10f58034195905282c5800300c0f205610386840032080041c90321420178101200f802101616000704401401680000a50b910b40c04e050f4410950b00103411a044420310741040c4e032144900302c0040012100340d1100b03003c1200c045c002d0745d499204000040082c004115003030f034000d1804510388011030b454800e00315014040e2a160104912030900180c030500c0c51881c1299800f86d00d805007040740d041c4010088080049003850440e4107010b60f081c0c0351a4461115880c00900c090400000d61290f01c000b4041c0700722001c070481c0c240c5030401462a012407151541c0300050010b10840c2c4606a10500d00503c0444658100c80a000c05d080c021090b070305410b9554460040c60f01c4115a840b010b0380080060a4014905038050364102c8013030340840790b0450b103540082c0c0c82d0402c00e80001010905004005d210366a010000040c0e052007507440c10000c0209181c05031080002420301c0784284c1d219220110a07132141d40c404650501c0d5a0000d0082c42c0403601441b40503140308038600f250320700b03000022910b6031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 288463102 1250 288461852 288461861
    0xc090f1212050705060a02030c161b0f15120b18040308100602030304023007050307060302040605161401090c09050603060705070605090109020a080303180601230406090509030d0f 79
    0xb6001000381211b9558908100b0082d400103180c89007018080c801c00160700680e00d00488007600c0703a110314400c800f0f04005082c0001041d0b004640e80e041c5400300b40f00c0031100d81400410f0385031700d0a26841c02150401e0b083c0160104104007504080c00309034400d031000c119940179000e03034080e4aa869858071b030210450400c800c00c1c02140003590081012400600304a034400c0d4103c03800140c04029040204034a20130000c51460000b6564080c410500c040c0c40e09024900040c265820210301e482d252000203001800340c2d00288040c04481003110060000814001d000c014000c03008003d01082d03854111980352a9001e4040081d1034200001d80c142030008413180940c00549501d818402181e43e05c0d0040d01000300421155500da078010300040c0c850b03240c8000600f130803001464480c0344c44104440f07800c900701c020700705035480500100104030140e40c00507a00342d0b054520365042e8003c5404030300900510303806580404d180c642000100c1c9400310103080003482503081070103050002c2e0394580a0741d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 288464352 1250 288463102 288463117
    0x40c050903120d0207050d26070c020f150f0c160f030b130209160806030a2f090c04030203060a020a0e0f01030e010f05090d0c0f060c090f121205 64
    0x40d44850500c40140116402a0000f084286000b41c603040180d6110b60611789501000c50115541018032070182c003c8900655240c05c0340c0d2015401380c80d2031040108031140c600b06c003a00944c8154640d030000e4440401d56040c0c810ba241788584d80300e00c00e01d02580a42d020100c030342118003440c2d441c0c01c0000034034011707841215950035844840500710385460180c003102400d507101746802c500030707580140c481c00c040e584184481140c0c5140b82d1000398003d00041802056036100b5001180010001240340c0300480342c0031030255a12281d000840d240442e0203a060400c03550101c039402c10055600e0440004009903031098064921a4591003024400d90040c0001e42d4089400118541c14a00b01f020204040400502d4003060891980d81c200f42115039156094049985900c1007215181040100c400c020700c0c0d51034207501c42185500e4042c02c1241c1a80002c00d400d072900c699420365485042ca070070280003d0710390710101560341c0020944200940c141141c000c0745001011428030f0041054840e030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 288465602 1250 288464352 288464359
    0xe070f0e0c1e0409052a131511150103030f02060f060d06020f0a170c04121104060b03070201050907050f030c04050702070b070f0c050d08180102150f06040c0509 71
    0x280420a101000c501ca41074034801e02c210003e200010b54120f6a0041c280160100c41007011724000f861008003d0070100e5a6800a4800800884020148100000c0e0458200065049150000100445c0c0048100000f0304607440703809040b032401901303801214124bd04c203803140c00000143e0b98007680c40700800c94421240e211440006501030405041d041a2148582401460440d05a00e4050223401148006000581115240b40e58a1a680449800000064609083c9880c112608034800f00d0781100510144d1b40c180d02011035216500008050600060207603124035004000034001c080845055125101d8080d0000311070821f29420071500b4400b4000e0107001ca04002070001410010740824210b100c0d0b03071000118041000080c2c810700740301711100c0760341c2005424055041003c60300014800d207032420381c0d4400592114119240403070f43c0f82c541c1800300101c500503410010b402c2182c0c1c10b146110800c00940d00042d004280c03203100304480410503070300184400c03509406807442d500d40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 288466852 1250 288465602 288465607
    0xb0109031101020a0c1e0f0f0302040902030f012d060302092403060a091403030105012111030c04080f070f06031e0e160e0f0c03040203100e070f0e0c 66
    0x40781000321448036000d41030044a0904443d0b0f642d0300d2004c030f05640301d048906150001ca0650902040641004000009020440c0b50601c50344642c241031a200081c81113544184840c219107040c0712554400d103c4200810198210641164109404401400c000b5014000c82407196000f03204505c140d94014104645d5a274402400e110441e0310080c004204a450340401d040030341e01000340900c1046038500210328003501e4500424458048034404181c0c0d041030006001d2660702400e440c0c20101c0c1c0001482e041e5114511800c010088520300c00f0780d514000041002010450008204541c1d000c41160b203004489505a61202c45d10f018900b46030700b503000c0c20002c3d01c0c4aa00b00c000f142d07140c48072040e0250050007454040300d004440300103180d04884154481c2d401952280c0c0001c0050909149a034600101d408041c03c0000305140c0712487e002c800724056460810001640e101388400405c4003900301c0721107580c0d62440d803190301c240c0400c40f10042050050030100c1c0f0701519a0160721070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 288468102 1250 288466852 288466859
    0x50103120509030102310e063706170f040b06013509060106050a09090903121802040c020c0a0302091302060d02040503012d0b0111010c051801030b0109 67
    0x503401c0d4415210658036640a100317403919400120f18051b0101469005402c02e01035200e090031070034042d64010306031b450f002d10400c009519254511f0303200c0f40180c00941a1b040800b00341103616980d00c9108508580c691001280e8103400800581c0c0702d411070303100e44903955100300303500000150440740141601c003850b0228219502130710030000d149540041040e11140a0b800172182442c1f07649240d801c0040c40c0090062441c0d041c0010350143c48503260003032920f8040074010302110040d2252042d0660340d440d181c1c081c11b12079080390145444a00301480342840c00c2c07040090310591840f003a0b20036481e283c64a01d90342d00000c1d50001e120009084540d0f07807455a0200b10240000800950301c22800320711590041e5180d20041034802403c007001a1158108402d01d4210b4144010034021781d0a000101c0940c110780c02e000b509021121980807031844d03c01c0d40121101a6001589e000940c04c150b030401b0f00d01e40240180210200e010400140c116204004500f580d0402d180c1ca404100640d00c1030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 288469352 1250 288468102 288468107
    0x7090504030c140c120c0f0904020d0311010209100f031b12090f0204051003060605030c0a290c0a0303230c0c030f16050f0109050c12072d080105010312 67
    0x521100d2010068a00d4200840302086050262255420494025444564041c80e1140e07c44000100c00d5505060500d011360100d95040c10080024060018052001103003070701c00d404031285008044c0040d60205004c0001a0008036084000c1011030300f80110082e0b19514102d10340f000354002c7e40e5500800780c8083c910001804001d9041c1c4081c03e0a181890142c1c4603070050700c0c040e107108661480c00600e542010781c2202d50726007140d0b11a80000409080c0d66590f03c019106440701440e0420546e1801180204040f000c90310b840f00d4101e0208161303204c03034000f140c1c01a8450090701c05010440c217040c0d180a0a0413845184805420004040f810281c00c0d4070160481140610443c3d14110350651000745a030007140402880d1840500b161080003010b0200d42c140b8104c10b0000d01c1a0261035440a8031210303510020781c000c0c0c08403080c440500c0010890a03004082541764400c60700701c0c0c1441d00000200703003200054040011000051134040c1441040d0403282c1000d1804c4041c1c0e4911002c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 288470602 1250 288469352 288469373
    0x70611190e090118061a09090a05070507020112090c0305011a09041208040f0b04050d030e0f0c0f0d0b1e01060f0203031306020d1b2712030507080a02060103020307090504030c 77
    0x25850155541701c012450603c4600b00f5100078a2001500341c80f200c10710100800e502e80200004000f070b0802d403d020f0310343d4110040e10890383c0d090030141120100d0310061002441d002402501c1e890010b2400828080190f119110074640201c911082101e1001403101d00507007510f0007414403415240819646101e452000e070400d00c1451005a840f2042d110085402000d542c01c1e00d42d80c221000004210b0f806126031010300c10b5010140400301240104251210100e041c2503008162607c1700b04e03225030300c00354074040c641e511051b00d0300103041c1010b040401c2c1c401d140d91a0390714442c110002c16014007806890442c228a07034025840c59440e1040c00760400d14164080700c64a4090022030000403032405019100844050001c04103c00b081e00100300c0ca901364207918140034040b81441340d040402c044401903c1441080140d4070209140c01c480300d124111020f07001100115024410a0340030503420b040300d000300c3c111070000b5100d00c44a000c6840903103000f0081084010002e0024101107071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 288471852 1250 288470602 288470639
    0x1002030c0408030406090905100b270d05030405030139030b0a090c030510120b0405030903071203140f12040309030c080a0615050f0105030c070611190e0901 69
    0x1181c0c20640d4a00010b451600250092008620703461414044c50074244074103a8041150700781c240a0610380703104070300548507410000c4102c8001058000548406120340014520f0240134a02c001d01e29082c96034076500140241345c403a50915200c1000804002569600340c4400b0005103001007184030580100d1569003900b00c241601c0303084004890381e90030006c900418090002040400b000351008044031001001500c00c11420707502805405000b102074001c070340d8429602c0f0000c2c0c86030b091030f910f5809901034055049c03040010101d40c07603004070708942c0c546100ea1150485203540404410080c0685480c5040d64030090100e034000d03401c404072170354100d0300038107202c06d031740d504c036181c0c001d103072026030840e00c00c43c3d0018442408010007803049030b540c0d0502030f407030114181c01e000001d0041c207111004903040200110115a80024250482c0c4850782c1c17200c820080801480100396607034022031580c0c0f040c4071220480b110140d01841c0d00c040150001411113507035a082c41c41d00d022105080c075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 288473102 1250 288471852 288471871
    0x219050603271b06031b16060c020a170a05120c0715110306010c032106080c150702220203310515090703171305010921020d0203030a030c020c12100203 67
    0x4400e2401940e01e00001c00311500351f10f090410103052030400005543c00c10610208640c489150540401d186404036030804407035050050740d614580030b007100d41e4020a0324285440003c5014000150302160042c105a40700c1c00b03841c0300500c007594081046032002041070200480404c001820b81d17116000b4460200e02c242800291110340602508203a15825205140180d03144028003c0340e0080041d40400801100c020041d1002042020024028203200900480042003483c8038145072041c2c050090801100440d260b141c04c0c14400b5582d813507100c00120040002c01c441c42c01c016004052540a50400b0003005100701e60030040001600040102846008a031030200000d0402c1200318140000b0360602500d80c240c508561420656035408981400701e0200104034042c2c076018150a060641c14a0002e03080d00e40c00415001c000d0a0f900035854000024030300301c00c0c1e40540c0700008000482c1d08950900184a0900c1802104081d00e4101e40d4840440c0010072a0359800a40d4000c1084 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 288474352 1250 288473102 288473131
    0x11040f050708010501090f06230408100903230304020111031b010b03070e04030206150301090c0801020a080a0e03041205010f050c030f0c0301120219050603271b0603 73
    0x61000804551040d210400000c0a02d80100702541c3d02c01c2228024010220108440c2441c0c1440075220120111900801005420303510103e10300d05d02c1941c2c01004002c05031100c400910b900da5000b0401c10340c085021500d101c2001541200222003241d041440c840d100345980c9842e0015100c20715020a05041ea00c4204480d07084001a00294901c04084c80c0000c0350001d41c0d8000c0504015503600201c03110030340007007003102107940019500c1d008000c3e08100c40f000e0350100042405031264400c06041c003542124005241401503000b840c6030002d60361800b8032130f1903050340d0805582c010003800420341d0040c03009100741c4100342522010755105174000502d14800701c144105403001111a000140c1c80030040240c582c00e0880059408941c03141c43c1e46c550740c18180b41070402e5000260190254200c2c00703051030000f049441040c05030500814403130b205d00d0301c2a42d00b80511144075038406c2c4100000310049028000060095411541002102e550b040d50300038840342d60030050100302d894240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 288475602 1250 288474352 288474371
    0xf0d0f05090f120708070b03060604031209030206040b0901020d0f0906140c0601080627150c0705060108010e01150302101416110a061d33040e100e01031104 69
    0x19441c1d00b900c80e0f40e0900150031842e1500e901e0500b440080d80c44550f84410410802101d95108800c407010740354007003400411807042240488a104403a00000d410480003c1c011904002d050042c0140c001c0903070840b00325490914080700d8401d400c031030420101e0f1181d5014002070b4041e07148860400c40d00c400c03150401c078074001b01c1c40c40d0503020390185115401960901c10a03039050f001500002d444070000ca0342a030700003840503598134040c2d940400910310b41d078041a54841010116041e8a4014046840958580c80e019009000c41c007803503141e540c6811f1100c0115000c640d0414104d03900104240380320450000b09440c10300c05210a851241c0040000e01050300c4803588440c0c03068012885c0c40e0b1204262024031080300070395008442030002e80d601d52107000b4084c100b02c81080100f900d2076400d88800b0034031007011541c461504044d00d010603001c80c164040e92400340c0304844600362130318541d4039610002c1d980f0600750301a07801c920041400601c045a03444001c2450303c0c20180001591180c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 288476852 1250 288475602 288475609
    0x9090c051606060303090605130504050403031b0806090a0606050f030c07050a0b0105090c03150f04150816060306181109090a1e05010503100504020a0302030712050f0d0f05090f 78
    0x11001401c60b03141c1d40d106030610500da0701900744000340455062040c0340015825508040d40c1d02403007014843c030744071800601014031a801044d0b050031101c544080360740ca40c20300541900c0c070032100517000d4032070000055400b080c2e602a020880301c4a85446180600c0700c2c412684990004040d00c501410800c05003001440401a56a405015100030b81942d4103110401984036000307480710768000c1003803017409140940310030020f0204504075181608001d100d0041030180007031000310700222103851000a4400c10218000030034003003040c02500501e843e100f0680c11120f6a00a0400c20003103062101c80031500c5130300c4040b84102000c411030500c940705000030403d0320304075990050141c41340f5203a200744440702204225480e24280500180d0304110110350341380070000c0f030ba03014151510041415525401c20480140d034002c2c0c180d17004a51601a620b202c80612141140e007072148158100700c440300032520a4184d44599610f0503403101c10310044506030004004503134450400340311b540590f42d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 288478102 1250 288476852 288476887
    0x90507030b090d022a0904020f041d0c0409050a03080a060b0f0405010219080a1206030b0a050603060a09020105040512031605100e010b0a0509130f0b1b0a09090c05 72
    0x5002c400140300f00303000000000c0c10149490340806222040003445e00c2c140b00c15511112900e0421780703010840c2d43e92070001a00d00100814000e801900d00200565150000f03802981400c0c0780700c0c02c8541c80c24420b020300084594424020b000707a00511a500300183c45000c056410242005012400980743c2e00c074441c490340800a10084980001400c00c00d07541c06001c4c988803c1200074062420201544410290b0720441c0215000c001c1c480c010800011401d60281003e1a00b100400015103003e000340d10044c00d0503540144213200b0480003554a4034680246020b107035041e0341e2141840d16000a204c20200c080d2050300d11404140903900c0503500c84400d0107040c60250b4001e010030b00e03940c8925400c0714050900250140d05014240f866a150000d14404444064030051041d0780c0703403180847c041b11f541c0e8001346400014600136040c02000b01006025022180a0030910405419844140d03c603603840d42d800305815110410500e80a540000e00c1c054503030500501e060f243c14040600d10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 288479352 1250 288478102 288478111
    0x4021c0e0705090721050604020f0d090c08160e0411040c0c020907030c0c02060d0b0a0906150507050a031d10020102070614060a17011508010b240d090507030b 70
    0x1d5001e0241000b4500c1c0003040f250b044411410304080416100c0c6a85a0040d070003640218172540b100e002c01d005031103680c100e0b6041700442c941c0d50b407603000f0707001404050646400143c80b11a01c030700000c2207030000031441c5c030740001603014114000f6290007084820014024000d85410718062012256a140ea000d8100d50f10287c0e17075000c0282420f4410022101405040442010b140101440f0419002400041da0a80407900a61580d4542c0d070740b0400750100800705038210718003450000305500c19400c0502591491210829030305041c94045800e1b004046000c3d200354000310402c004a07024032030142250f0500e010720b4400b59192008960441c8370342c038080005070743c0014540103100492003500c1c1070040c0280d00b480c043c204080018008019402200c0783d07508402d039240059203007580461044204404c001d017800d542c90007014000c00400382014081c501d000c1c0c0412081c107109c0b6034081c0039080c0014490130000d100084000804c4400011143c41c45001c1e00070010854030559140b01e07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 288480602 1250 288479352 288479381
    0x708040606030b0a0b03010522020d0804080708030316020309010509060c0109140c04061401022e0f09021201050402090c1b1c170106020a2d050606010f0e0f04021c 72
    0x5c2c015150141402c40c1c000405500c0d0200d1041d60b0700641d5424900681961a0111890440301802d030901919030702c200c0e80616814801d00c040001c060f1004000740d44034200000041d980e207040a80c0c280d80303d01c1000301850004104004083d80d42c50218060301c1d2521502c1d000089040c450380e1002c00301e01c1800f00140440e4000c08045009151501840c2701034003020040340c102e51000e0001035600c2e07020b42c0e00c800e404c0f041c1c0b204000b0a05400303202603121210112042c0f00d00c8203800c15000003040c0c2d280d0107900801e0000c06200e80910705000f40340c05954007130200c860b01d948988a89146802070041e0810054050f84030909418040040e60151f40000c0285032040d070b03903440007400231580c03294034444042d4000b00400920760007040e60440305d40c00c062240d501446985d1106096100c070b80340c40080345d1707102005105028002414500c11802a210380d0b4008403800070640707850314039149941d44207141220406090505802408240c80f14820b4000901520155202900e00c03001441d000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 288481852 1250 288480602 288480611
    0x203070e060f03010603080906030c160b061215010501050d02040308040f0905060307080a0209181501140a1a13030c08060405070b0909040308180a0303150b0a05030708040606030b0a 80
    0x1850000c000b10300c0c0c07403000c0f00200849440c55030f5869a42c010320700074a200d40d0022000030420860301c0110b8990300c0790310704980e400c5d4000307180c5807680c8003040d641c0384c3c02842c4041e0202162000000c4400c500e0909074404640d982c40c0000440740d82c1e2164000e5031040350244400000030324508090000b400c0d28001e4454000d007040f120a085903001030140c0d00c2070380070420400010b0b201140f040201a01a83c031800359641d05200e08002c0f05a8910b20582441110f5119100c80d0090310341606030f409052038002c611001200300080c1840b80e006100070102881d0380400500ca01c440144082d858030f41078640c4459990312104000b032190f81c8110f182d0b801c054100010410f090054401030301c00309003500c0c00d0941c00d802280c24504001c00003418132840c800892302e031794031601d2001c035100350b56012101c4184481c9001805000080d00302c0d400341c0714961010603030080610035603211003ca9134a0504554075400102d6212001034802c0c3d5032959030300b0022011503004c3e84110b100d100450300205 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 288483102 1250 288481852 288481861
    0x1201020d020405040c030204030b0c34050106060306051503040c0b13030b09010c05030109020304141b2b030f030e0709061d010f05011103190206060a080a08030a0f090203070e 77
    0xb6506240240170406104100c2440000d031a1031405404c07100140200c0e80361042e80e103002d114014407c620070798811043c048803a0064405023850b03100351040000f8003805030785102c2601590310034014654030801c2d03190101d0407181a0b6000c1c0d41d0260041281701c1c0002c0e078440040403654401d600c1580b503c00d01a01c11300600104030b014903007180100000304a007403043d4800410602040c02402e22075500080414207010001c02007034100c107200c5d416107003076019921300c2400c02c00e20f5100300c3d400b179540003038840140700614841001080e003000f101c0d0750105c0c15680880e10780c080c0204080c181075a0361710003030064004001060140c0301e0054001695400c0c40c9400c00c0489101c02038400c0c0103260070042c0a1405504100003c4070340a0070712082590311000014118010740c49680c0c59110a8082c011855600088850080c030381610983c02d1581c995040d1502e034840002d000c0c21b80e00040002c2520104958040b8094110424000403c8060ba03400a03041254a40c00190038991020520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 288484352 1250 288483102 288483109
    0x1503060f0106020c060c0a1203021801020f0c0f0109080316060b060703170714030906041e050616050d050405071401020a110f01050405030601060305040b07090815061201020d020405 80
    0x503500103420000d00321056140880003582c1d10006282d507806404041507018400c1003c11103100c070700e91b001400214a00340358600800035000080000001080010f9a4281c8d500110f010307102062684058010628060244400301c942000360320704100105000242900050000e8031001c00103110b510890369840c01c141c0b00740d810141e4090303c030362420480b200000b5040900001e49049003002c03940b031075841101c1603c041e0802003c1100044c000000c04c000b1503c00b280c02da108a05c104001c0c0c0410b501584600b90710301c4407440050840d817100f004903a909401040b003111304da04614019260801e426017401c02e44105135011515648005805c0c8900310b00c0242c030510308442131000b02100c2401d501c41d9040c0480c0d0f010038034021249101d88900d0b83e44180111030150501404440342541d494000a004100c11907040e540b0441c40360100740c150744110002c108452910300100301070704032010400c4030702001800301c90380b04000ba4140c0981e0702080c0090904402130100040c1c0352031410052 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 288485602 1250 288484352 288484363
    0x2202061908011d06090a0b1905120105010b12060310180212031306030e0c0409050307060b0a0312210c0c0201020c1005040b072a052716090e1503 64
    0x210940b1150091491815140f4001e2948440203c940500da5190480750b14000d0220011070342e0040c0301084510b4400e113940c040344007120b1080c3c0d0b404141e0310344030090314202c85083c081c000342e0100801103001c540c4541e103180d540150004090346c2090170249500d208480d2110b200510302149065104154035110440c00c401c1e08074900510700e480c40d40c0c1c82d62100c082c2640603178400d0581d9404540f00c49030040000208c01800a801000b0706040c90a0a61703994211003011a0b400b818200c42c2042810130301205c80403240d114001d640000c014400130b03242009405100b00342d034500c550b50080c8800181c024000d83d6130300c588070103030305070b000340002420b010041d20f5640c01420006000c0000c66400021502142c160310b821540780c1001d443d1101c00c01080500000b003040e204402c246000361901d00101c21200201c461660040c44c11803242c2c140300480c44400424110100010100340b1001041d5034403025518141840c0c40d16800f00b000000300590700c4080700241c149108440c1e080070080d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 288486852 1250 288485602 288485609
    0x318130204094118010b0303031008060a11070308090102070209010f0602070b0306060703080402030f0a051005010603090506040210030e070905010305010e031e07031e02010e0c01090e220206190801 87
    0xf6070400b00b05000c48040c402210140c41c030f2507955480c090f002c8080c2020b6100104014000b03050b00d07641c0c1045c499100b0407030400c8c00765600901842d004201c41c007450b0302c22181c1010207035000c9814200c0380d841c2641d282e0b40003030095072a55020800100140d0b48d403e49140038059515581e000b46052041c024506405600050581c1c14100180311b0b95030f4400080e50111941442e1143c40782e51203101180c1410f92003800e0081d03611030280007004201010031a00c2640306041d90802182c0c0e80d40c00120141d035103c10000d042e9422540210f030160519601080c100502d41c280402c11801050782c0501e8034800b6882444810b40d114010301c10020300f0b008180038800750170b0040d41094121601e0002560700040131983d85800000d0800030140106e190712052100c1c0104c002c244843c1c240c3c040c0c060010540300d240300d0b005040c88440198000c65958090380c42c40044a07109680c0c95401c8007401814218180d80e051354101003c0059a80400070481d180499002d10102c801010002d00a104180c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 288488102 1250 288486852 288486941
    0xc03130f0f05010e09060a0506070605090d090b0a23040305030d050c12010b09040f0c0c030e010320160c1514040501050a05090a03050105090a0311031813020409 71
    0x1041085584c1e0b22480c40b0318900c03021a042400c2c1e03201e240015003500c0403030b402a9040000802e20708180192a4081c40c403604080050b60502d44001008468211942c055103441500600080e56503910403110b030b00300c40c03d4803018440200c1000e0790518841d0003a40c02284c0d13071b50001402e4090840d550054a0700407035035006050900800440010340d281050103000307a040c1c80030a000440d6903494009103ca0448031904001019481c1e40c010041a01d0190070350114280794000d1409501ca8410b0b001d03000c1c40e1101d80484424110907881081d4840c505500802c00880914004640e811807028002d00e420010700c64080c01c407290141c0b00241070240300035150b0703041c8002c002c4c0380d800c6011611080d1540c80c0c44c55403a0851070003d500a01c1541001e0010b40c80c0404000d140040050078425040c040d450780d81640d8030070782c191580ca1280d144001a18120702c40340ea0403034180740412402e80840c2c40e60150400d52188910b00403204080589104441c07070b0190f030440141740071420380c05003405a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 288489208 1106 288488102 288488129
    0x1514030103110117040803180c03070e0124050403020405060d0615230f0111070e0709050411130b0f0408060c091809070504020a03020c03130f 63
    0xb98000e0114144140741d440c031074000b80d140e500c9154003040c030034a56580c8180c5030501e050605034000192051001d895902d0382c0600988000c0c224448490303001d503241401c900e40c450409900800d0441c0b1004d071103040340b80c4c031030125801d50350113550114450302c8403408989510800c0030090a9a440c14503004d804141c000441021502c0c50507601c1e605100c06e0942107003140c10801c42c0c0354048a0701c0018047c5502800c890742003140c406040e84c110550340c401045298104450280020313560f42020310040c9494880d82560700d20304c41c3c00074107000c2019604040085c680c0151030b21401d000c180c4200c894102000c4034054845003054039128108102c8900300b40e002205000d118680030341e9400020742040000714441ca20300d0000b4100340d40b074403060000a5200301c09400c02c06d074003004040d0254108000801c0000301c40c01701038090074035200e0aa03414030b0722600098a100c009 = true := by decide +kernel

theorem cover : BRFrame.Cov 288309352 288489208 := by
  have h0 := BRFrame.cov_init 288309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 288309352 ≤ n) (h2 : n < 288489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
