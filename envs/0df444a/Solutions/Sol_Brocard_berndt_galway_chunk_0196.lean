-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0196
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:23:37.19574+00:00
-- url     : https://prove2.me/submissions/361bd2b3-1027-4393-a0e7-c28c85d102e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 35071947 ≤ n < 35251803 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 35073197 1250 35071947 35071957
    0x60f0403030926040906091107140102040503060a14070825020a1403040e0a060311010809030903070306151208090402030705040807030f020103051501080105060c0a0b180d050408070501050a14 85
    0xf112080c006020402c0350014000d400141001107020082805840d2100c0300c80e01c26070b03d000340003c00a100c00c90f01d8800a5047d200213103070160a0f910203151a01c041340081445011900f00c19803200085541c0da80726511a40c802d01e529810200500c401404004800b180312004608603c200014480052492541c0d00400c260902c000c5450310f085c5081c0d03440c9a02d0040150035800e281401c01c00c04101d4020400c45907603000e00b81003000b03031034104a0605500c80e04400f0f540500c46d080e00081006402d50024100a60017410096016204d4061240341e0802d10b001900422051201e0000b5140c550b00443c3c100d0038a090061415585030402c0d030400c0c400350f000340c03150794160900c00295600f5005230f690000b00c0030100d4645851050002c0d0070b4040601506010340c0c4045006410741c14100241e6409a03004603003550342c3d240c410204007601c18401c6084c00350f4020707600703511110760040d015a02500c05c8030026021060074071004440a410550840d020825040c00e215070083d00440141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 35074447 1250 35073197 35073263
    0x2a0c03030a110c030909070306170606010914090a0c020a02030d02030c010c09060f0f051c05090c0405011203080c0d050a0207030201060e070f08040609080c060709050102060f04030309 81
    0x40c0c50703140ca500303040d04503000c0b000b01400201040003c1441088040700f168480390782210b0211142c1c54462080717004048507007140881d011042e403243c81c0000001070551154a090381c4403401c44d0740383e403007030421000c000311081d8000e41c02030301003008803e068003e5061800c0c0d502c1101d003444c9294000a24000800e582c07103025802c0081d21001e0100d003801003d11320304080c00d003900000e00e0004010000d894400310302e400c0000040300c881c1401e200d58122240009403040c4e00c035000c81e4a450560041206039017141480c46059001c40d2035080901030a4126501143c8090604006440607075800c00000e280c9444003904100c1c001c4d2a00561060034040c4032000f00c016100ca6141c600030b0300311f074410303046826074414400402c9035003179011fa001100c01130305160a000580315440c24002801d101c110080000d10082150701d0903030700024100e0300c07440440e0390300d001c0c490b542c3e070040e44c888000b0350b07030070342c00d101c5090015010a0007074200d0b5650302d1145581d02c0318000b44c04110b101c030402c00c604038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 35075697 1250 35074447 35074453
    0x1308030c070302010606050909040303050a0e010c020312060a0302062508040f05181009090305041805190204030314071506180e0c060403021009090204090510120201082a0c 76
    0x72000d00d542442100041c01c110300340369281103c0b100001d5044000100000c0130103413076000140000e01c8540040111841e124000c0c000411450006510ba4010b6240d4408501300e01c0006682d40c503000544004580e0054480c91400c0390307003402194216610700c0c003c01c242d541805540006001c46005100501d14240d04d00140d40c104001c00202c200c40490003048900240c0c140324259a040b1000c0044900f205030010b06c1c10022b2501362843d00a580c044031810440d0f40c504080710450b9007040303115051041e000403040300325040c410124015404042c1c0014071400c0194040700200005001890198940f10003140802041c00240d80380380c0c1140745180401000d07204044820b024100070896004045c22040716504c000c40c0320390180d840083d105140f81c030721800040b401a140c0d00080d09a20000355030320307a00e42441e00090304046e034500700840c9100000007064a071001d00c041045505035520301032912040c402c0840200e0303400680a0882d598205100c001c1164001814102d41403005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 35076947 1250 35075697 35075707
    0xe061809100501080a05060612070306050a050106020d05070305070206070606080105070e0f120c0f0d0c0e040201140315010806030102090607030c05010c080907030303050c042313020915031308030c 87
    0x38407402d035503040c1c4c032805180d0f0001e08100000b031000700c2c00540c8060151001000c0c00e030301140c120301e000b0740347c0e0001e00950f1901003848058065070f00018140d425940031600420703c2e40000b1100c41c0320b940d00140000c1d4040c03280b030700180b074080c0082030141d003d0040410900d4030b49004900b1508191424800b148400c101083d440c20400c508803260326003102d003004075a244c2440c46407909040d03040d0a03c10b00142c1d078203601550300c80c0f0440c1c1a01d0380102c52030100035207503407410440700c07400d54041e03000c90b1751031490b1045a44200112885501c0e02e245000200520000560f810f010181074a5850b54007031007508155280c040c041c02c1c80c240a541c51002810940c180300e42107580a6003032200f040145010080b84d0b078400201181240d605180000fa40d503a01c0505170b00a00881d041851125584a0540d40c0c03582c6041c943c071a186012140400c290b801140d600c0c089118184660f900320041c2c1e5400d0b0302e01c6880303602030b644c800d5074027041c82c4460305075950301d61180e03204803110000c0d4400070403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 35078197 1250 35076947 35076973
    0x10504180504060c0302040506040506033d1a0906090103060801050a02070201090b0a0525061503060c0306050a1401020c0409030302120f1306050a09020d0c1703130e061809 76
    0x20f607084000b000d01701103140a080c00c022031003d00c0b960090501494000012401d480070744044451100d050003008032542c40c9501641b408000580b82c0f60114072098600403c041e28201490380c0107000e041041461300982c403061254031b401c00e66100341415901c40000503c00300a0040903c04c5132001030040c5e6400043c8005800702c803003500000c141e04014452003844035000812214a505c40c241d2143c01280e03070300840350004113000c200404640c2803041008032003425008080aa07071081d20140020503442c0d000302d040324840d10440341c0c44802d401081003017080c8500111075185061040c0d8000c1d0700f950700454252001c500084000907070001d01608203540c003408003500128620320661850518100d2807103001e81c083c1c40540301c00e0342c9802040900c070556100c03040d03403130340a03007884c03000300c114105410b01400034461411808103000d290070303038010084211060503c0030505a00e006042050803c1c0b080d03801440f40342c005014518007400101041100b61003203841100811440c038002da = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 35079447 1250 35078197 35078201
    0xa03090512030705071a0403080a03021b1b0f0a030c17070f030b04080f120a0f06121e060e060910140f0f0a110c01020304021507020603040602030601050418050406 72
    0x1030030003105402c1070241400041e0046914021a81030360503c40740d00d1140d44404c00c4611a43d0b0000703008520003d80c5501c451b40680183c0400d141c0343d5089510307101c100004c00d40340c4508007419605040704444052031031401460600f41080c0c05041440950b84035500c0c1c9400313840d95081700d207803212140c003811402c5404010b400081c0c12a40f1009008074074507554004002c0c006400140100e0000c81d401079002460001c0e03a201100e5a0200d9030b03582400c410510050081a0300c22641c21f04060000c6030440c442c4801d603060303561261105242c944e00007070311420100c0c800c800316003440e2a60100c1c44000380800c142c5015115002c007400f8070540f503818890403a040112817402c0b040400082080034036101641d154072008a06006840795502d2543c1c80c0286010a080b1080b00300c0030450f015030080560155204070720a84000b11903a100c200c0943e107a000d481402507000b117040002030300040d841e40117150411410304006080c01d07180e000884c001500f80300c10751400c0741e8440030002801014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 35080697 1250 35079447 35079469
    0x31107140f12030c0711060711130e07060e030f07061205090c1507050c0a1205010b2e030b03070608190605011e0c02180402030618060117030c0a030905 67
    0x78000038010203810090040c0e4901006040e52004030000c41d00e402071142500d00c018985000a015a5442109203040c11014400b44032a5011340c2d01c1d0384142c40030800a00c20400c02030030100041005030302d4001d04031500010000507503011301482050103262031080100c54040c0c02d40382c81d00314000b40044011011200002c2043e2100c0c5d0114010401c0b544031214114089052102c4071239407968141041e51030403001c0210180c0010701018000f42410641080c0c03a1168441c030001d0000c40804000c2001c09041c0640d850303240e80c01501c1100340070b4012901c00742500401c0c1008a0003505010000382850f9150340400080381071201086030810410120b56010f20380c052040100600b0180000c1030401c140c0100440000107034200c3d94068000c0b1861061150300030003509010b0b40305488140050000d072012030180c41904080703181104500e40d0404203500610041c01c040c0c0c03a00d00b02d104101003040d04003007140400c10001d281e68000341702507200c240c020340b25112001d19000034040d10600c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 35081947 1250 35080697 35080723
    0xf150901020301030308130204090b010e070f02010501030209060108041401020313020108060306130308070e0307030c0504150303140d0b093313110c0d03050103020109050405010b03040204050703110714 89
    0x1c10801400041e8003da10150814052840d01c40050064804140207051659003d041d042a020002401844a60311284100d5240d41e40d00d00380688840242d0a0303034002e01009510420540024840794815440140e01ca40200c1104a114900041c11400c9a0081c0c58140d000c181802c008001e5580008580742c02880070b800034100c1c0d180125000d036440e92404e00c0181000145004a441d00340700780c10b040045000141941c6170269681b4000c04e51046901c0f41c1c0380281d00f041c1c0c2992007645802840411690152552030368003100342d00c91440d59112898010750203556040079112901d84806245c0301d020340c04501900544240c2ca1a040482c0e108030003c07c0c201404a0304040d501d48584503040b040c42c1050100d18090ba01e2103807600c500802000c10303840d200e1608c05441156040d040a412203000b030301c50300b042d0780d10740d030900c1300b910fa00340517030000808100007080050900c1d501c0f060b48003d00d0b140c00034002c02d55803011011640150016140c881204000c011804024000c00c10340140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 35083197 1250 35081947 35081951
    0x10c0e0a0e18030405041d160b0f0705030f0a081506090f011101110a05040e0105010c0f02060d0605060c03091305130f080708040306060e0a060803040b0901110f150901 74
    0x2180c840707038541d9090014010200500b00301c2000328102c50400959028001c002c1c002e11003c10055182c440b001e4200b01140302c0c501c284401d581085481250342000e68030418100e910340103000029204030f0380300e52400c42d40d038070041200340120015100a411003001c00d56400400382000e1a014844501510070548030340f004100450b0281e8030101d5902c841003003824a02e0054003012000c90040002500400c50f98070006906441c5a074400000d2098034041464404a43d03200e00045840390b0000b030000700261030b400c0c4440007519001c2c001d011454241c4001094181c0c48402141032500800401c503071070f91021a1294151500c1040d0808050b1840030411051401001100b500c01340c0301c402614001c83c000f014000d000702c180890321500d400c10701031507983e6605c1c98082d00500041c4a44064626064045900385c0c08a00810341112500e200840c1080c0c20b101c4015010352000810a051009a02c2000c0c2d805100380030101c40b000507000904454000349200c0d1041910003403101303003564 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 35084447 1250 35083197 35083199
    0x80601140c100506101e0e040204090507020a150c0c080f0910030e0f030313060513120c02040605060a1202030901180b061008040c0b03040201030908070b0105010e0411030a09020102071205010c0e0a 87
    0x48403413162071441b01c01403800b400c840107a000864001d110b00c0d0401e44085082a0800100c030f60001031480c0021310603d103c0400c418094000c0c000c4406258603100052244060f01c0040351110004d0010441c800035000d25085d4008001424581030b414440042600c4101001940601b4081c1515410113240a18a1490501c0d2014049002281c00402ca82d0390380c80818101e084900324a100c05030f2003040c492034001c60b0b0401034051110000124800d42c186500803820341070031800e482b200c103600d86034091503a00307040b11000039400c002c00a03a26596580d0400388180840840585103c1c080c509001450401000b8440098440900401400700110502c40000d48090b100c0040724141141640c50740c90714801200604140f940107413410b0b0300810444188494408980d040352000d03203803190920400400c0c0f20903582124107081c106d8005200042c403410342a004442002d1051041d281199116403e84c08051401030060b43c85030765400c281003180b84c10508001e02d005084034100d801e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 35085697 1250 35084447 35084477
    0xc062309070b1e07050a0203030304150506010f170403210f0606110709050405070e04050f01050702010506060924040807090b01090b0a03020d060306020301060f02120406080601140c10050610 84
    0x8075801c06401c2420030f4000f800e84240031061014843c5d10790f00800396542ca0505040c807860130712650580d040d2803840d140214860f58003401c3e04400100080c3c4445044c0100302c110110300303101c0140107a0910041800721031542404508103040c01c01e00d0b40c030016501d00201c422a00f16490741d001242070046401c00000070704c0700082c400046544800002c00d00f40c3e01c501d0300724288001c80d0710584840000b5410300080000210380401d0055815000700b00a035a50f81b000c17800c0e51002c2d1201900110101302c1510b950900e9401c6101d4002e840c203440354000c0051401441a030b0250340011300350f401c50001840341070110b00802c08208002d00c1c00284560400058a80742e00c17680c10600241740d800101d09580c20026000140213680010045403a90f80d2800090400750741c11031400e0060080000001980c0032290030340d0252400b56840302031541e42d10b001903c40800f07000a00c841c90f01e061001d02900070040200b9504410080000b2a050400a09100391aa0038040c490188419080400d0380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 35086947 1250 35085697 35085727
    0x3020c0d02090c07051006030804050405090a0803010506070804080a0b060907020a051b0f0a0612060605120103020f0303070506090c090106020a120e011701030602071703010f060c062309070b 84
    0x3c2507460714210f80c2c07415035142580c546000b800a0200041c2091800010f000055000e8422901c2c1600d040c0b01c1540d8501e40542c03641400c400c000c080031420300040c40b06061001c0600011485880702510749038580521a2034111040405c54030f444908007041580c0c28202001c030303088a441c0c00280403589047d074580c2d40307441e004500d08102c00c0341041d5030705c08dc2d650035081e04042c002c0500304007040c2ea1504c2c002007010320104c50803c1c959051110009140f44690304030381c6400d150009200507642903900f0403c6083c1030030384103941032200b0300104c804140c040c821540a4a01400100b000850140034803c08180c140e0000c0259005804540d0102d02842c12051900c201442e11074507014050005032341c1d50031041e420b4140d55643c3c6d0000b0041089650091030014001d400300b40a0300d52104c070f84d1a840c802400740c4000c03046018410040c0034050100702c030100f403090201146121061041c40c0502070f00b28241d6480307491000c1402a01c40061000101803c400700d9860b203080119050b0714a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 35088197 1250 35086947 35086951
    0x10b0108090303071803020d140601060e06090904020d080d020712050901050304032a060e0601090903090e0604180803071404050d080904020408030c1e03030708062806050703020c0d0209 82
    0x1c2c0b18080c92400c4403c5d06645001011710340c000d0a40303418008070b081c1058140b15548920b0a288a03440010501e175014480000340014010060780c07420029805112502c600038004980121641b407240d00000e107100083c3c408001c510100681703d2403241040b58103090301c40d08030b009020701080b465007984d80c0070f01240e5116801d4205251000b844101d041e405059102c401c82d074514802c14520704120040d04a944002801f5044494a0340ca070340c040b0b41121580e240040c041207010070100038000541e2122a4000b40c01040005c5542d43c00d241c150000e049043e045442d0400001040b01c81c1c1c0c1c01841f842c80c04004682014106410b042c007141114402d14405854802c0201d454009503850343c0446001c1c15203001501e1300d82110714126569207512300c8003030091340242c1d0300030740011900100f5684035082642c0c0f08183c0c0d84902c0203104d8509050b142400406900180d414200c00701100540020310305907842c580d50320a18140281000420000d00d803040042c80150009070381e031210015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 35089447 1250 35088197 35088211
    0x5100c0f0c11120d030f0516080f1506040605030406050f010503030d0f0f060602010603020a090903021905010207020a0605090a05030a0506060603060307030605040c23100f030b030717010b0108090303 88
    0x103400c444100010781115a412400341061003070141d44103403554946c1145415424a030024803058031800015042842504080c1001451300b20009006605005006422503c40364401161011100c081a01a807154110502240b000018041003181501c2a40e6001d01d0300028030b00c0c03c3d4108000242c40780314080e50031114685410040c1d200b2131656102d000c0c04288080e080080320340c0c88402078081c20091000344d20441010100044000350340c040c1e40725440e4541d000d450000905c140403800b076240c140041d01d4565003444800c005880380a0100086c1c0000d8a4a584603081e07081000701c07180140d000b031400303a000b40703a442000400015000e508240c08031046501ca580b600c0c0400c0c40d04001d5840a098035040c81c040c401031140b5120f8034400c1c0d032210008032221000130f049202e0180302d916649070300414000d9941000754450300ca8070540b0030b402e00d07010504903a401d00092420354150003000c0e20701c1d01d041c1d0035002c2c20803d201c0d0080840c0c2c03e080011075850004107483d12400010b10744 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 35090697 1250 35089447 35089463
    0x30e060a0c120e0a03060e060603150a090c12030e0a0803040303050f0f1606090b060a080c09101a030910060b0703052b0506030c040e07050d050102040503030705100c0f0c 75
    0x2490060f4000c006868200340c014050b96400c039980d003460b4020300040e4020b51014000c48010620904020a641d809142c00131100000340d1240804170004242c3c10380d0680310b11003c0000490172070040512054814020b581e4000314005503020061a1a9554480fa017903074020001000000d40050584200d1081c106505455221109810a851081c2c141c030010460803070044400b001255407186220a01412044860303035118000e0003844a003500034402035074045030b070344441c0f490304a8601c2d910201d41e040380da00450b0ba40111780440380833070320030f266a080c0110810414035000c008040480594a0003881a18500b04903405140709404000d402c00038002684c5090042c2c40c500d8010706014103d05040085c0e015019130300401c421b0758194071a01400010100303e2606010b0a00e80d0503400018003809842e0204120119000100440382ca54080c84005000d66041c009000b8072405000502400e01c0b4541c0030700122891040203100740030702040f481d40780691192a5040041e400945 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 35091947 1250 35090697 35090723
    0xe06090d06021818040611040f03060b030c120c0108100e0c070303060e0c210108100207050a0210080105090f070c080a020307060c0915020c0607081b0609060103030e060a0c 76
    0x400301030b210403111481d0b00554041d02840b60030382102da41c1845240101c5041222210050007e0054440c61144c0c40c1c2004c4450b8092010030196800200320000040440e2622501c0a021500c000c8018103c0c60a13508140700c941031360750b0010550341c0c0c0006005680c60006060070820208058040d02c041010705010540d2010980a5031220000d00880304425980d0300e824042410175030701112114a807201545031100a00d41400c0019058960007800b41901006a80c0c1e454020742100e5420784151040303114400c09611881800d0f01c1010241d5500d0480c2d604110070300c410030002070040070240c0402410084040d9200c20315110769948008200d540d500d074010103c0c40c41c0102c080184c5014503082091703220a8200c00c860f000c6030003080c540710014a955a00380c1c2c803002e503415402e41008003000902c002880d40750040484503464003140c065002c07200076103450040d0032108280181d21980040c0181500b00c180d95048200490b1038a142a40040700101000e100640c0108140d5a6484c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 35093197 1250 35091947 35091967
    0x30109150320151201140f180109050f1605130e09010506030d020a0c120602040305030406080a0b0a0b0a0f0e03030705100f02030606070807050a0209040f030e06090d0602 75
    0x3003204000c64000308501c03255a402000607204280e1458203c0c4202030032007403292010660b00649100c1c0500031507140072a0b1810031640fa86480107030f0705507032020b00c000a48919585075140200e0603621724194060541c100580e0108942001d1700648000711501c04001000c2c410303440000c2c01606900e401e50f22051b9181c1001501529a00071810b14800842001030410056200a1240204500b280e400080700c190681c0c490050540c0a0002c600104081c0304d54005c420144940b14450070b4014a85940ca0b21110300356046504400e00103a102400d0002da20568040c1c03030091603040300e203000d8a40c80c001641c03549210b60414201440040c2c1c1d20850302c20300684407030158480c0941501e50b107000d03910300a178540105421812469103800001d10100c140e0384207403413256801030f249a20309441500c0e50080b5822441c0308864030300c0741e40c15500043e1156030f05a8081c1d44181e01d589013050003440c0c060101c0014410607801854140005d110582d1014811031a00e03030000300050b0380d140700d12 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 35094447 1250 35093197 35093231
    0x20060406051c0617070f0807060302090d0501110d20090f0111250803030c09010c050f100e0f010506060a030b0301110708040e091207020103050613060b090f040b0303030109 76
    0x55040b041c00351520f8800107902041090620b508a60782040d10403081d25500d03100c0e06500e60380202c11466004050511806000307074000c0c80800001007280c0404a048c1c2c1e00c00d0b0948083e0005a80c00d0390000c02d100c0d44d46c0149024a0b030903a40004002c80c41032685002c18600c40c0a01d07652144900f007504400c2c070741170340101741030511806008103640b000c0840b1501120b9018098101921108040100160070300001c4283d0340106100c01040f841e080030b83c801140c0f014020481500c50703005800c50200614010082d0201000d06071f81e001c144040c18002490a00980040d10141a41080d041081587d64a011108403e5540c240091f40b6500200401e0041040748900300150310002800c0b000e1040e1400500708480c0707005440521503450100e899124040d400202115040501c00140150f0003504801d500c014094100d00d8031091852080d0242c6202c0c0c0d000000d03000c40010030800b641840c03440c40b40100d10690b024000c40c040880443c1d6640b0052003007040c83c0356103003401c0724a04981 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 35095697 1250 35094447 35094487
    0x804030c0f060605130506100528020a0606080f07030215040314010506120a120302031905100906140a140105190f0813020904060b040608030a08042006040605 70
    0x410401c0c03203480245402030007014030f400340511411107521032030710071607050060307900c203490181c5140640c072081e41c0292842d03004618094402c201c200c040148107903c00e8610075080c00b9582c024283c01000341020002c50b907498214220079041541e0700002c60b000020b86c1c80c02c9a074190f0ba809000e44030b0124402c514055504010309062000c140c0803405041500864019130703045035401c510f00c2003445106daa810040100515003502c40c11104103603070180c1d003d140c0c0400602081d01d0b0142400c000741c400c03140225403003485100e002ca070500c143c5240d881450050a03c2d80e20100d014900000014a03541183c401d011560380c4418803a070f405d902c1941681d850110280c00c2c184800036101000e40b02c83c810460040c000b411301c5002070300d042c2440d076840e0100c03038000d84108190b86541d03c480c1c000e031101400068000c0d446510010b040e0b6030820061000402c0caa48024540c1841c0c0b810712000d450039007080c003020b00000c40403121980c824007194101c80c00340c1001692103080c804081c840640c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 35096947 1250 35095697 35095703
    0xa0608010213030b0907030209071b060c0503100603020a021b13050408032a180d02060d09031101020a05090d0c0e04080304060c020610091503020301020301151202041202010804030c 80
    0x460b00c01d0006402d5002c42e01aa407048810100710f5594480343c583e2100c030b07448042e42c418603003004070746000d01070140c8030f520021b58000c9100440c3c5c141c4480068800c84407200b000540c00204000821004052950142c861803900f5464400314410085d52591908518a0844e41914440215031f031901d803e01c040d064807140a20013441c0504040360340d81c10881c0e01c5a0300514203c0c0180d0680c4101c000361944020700751005041402540c1c88441d1398420701d160b00d4004d24080c2c0002d001d0f0795564050034001d0304082004c41d10000d01d29008111404448502c50389a005000701401079403c41c1c140c1d0500b02003921001c42c441c08a0401c15161003072907010401b000c0c2c49409101c18400d00d83c0c021403003903000707500912074810200402c1769502d00031141221114119901404032030220b400054032484407214107020503403250006800c981c42a44003401d0349000300440b9100a0700401a003003072050000c41142010701e80000310005040190f4000d0400040100043c1018003603284a101207070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 35098197 1250 35096947 35096951
    0x9230f0f182701090203150402060c06010803090117010e0406090312020301140f09040201090306021e0f07050c0307030305040608190e01060513020c030702090c07021008040c0f08030307080a060801 87
    0x1410111000310b21207820485100400480038511940d005000340213a440d0301600405542e405103910004225000c0c0c0200e80c0260208064aa030000030800d450192281e0350244d943c86150a001625441142c003841c0c0d8151010801000101425810b0751382c0542c0040020510300d405140441d10301c0030500000320b81c1480840003181c403c00582c01022224820384405180400c00c0e4104040080c00f194001d00040e6081c200340300154254000d0b0007069031941000c080c03818180306002c2c0d00c1e0040c2140ea070140e1030110303840091000c2040b80d8030b003a1900350702422000e4155180100b452040c0d000d0301d07080c4042c0c0004554a40c00d8104200080d4007880c03410000303045031080d068064070315032150511a0740d45015242c5003400701d1080740c00801101005501e0b10103240d09021140301e0040001a0720607042c8610b41c00b680780e1807221840e450403036440744560701d00761070078400020341c0313401650b801c1e501d1040500010344004203c079000003845c14001c4483d640e8005d4580030307014035007220b11654 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 35099447 1250 35098197 35098201
    0x3040b03180a03021005070302180f0103020f0706050a060504140a090c0b040603020a090f050307060c05070302150c070812030106030b12011109030708030f070b130203060709230f0f18 81
    0x140d0110300e40c890f944c400b0700c0900c95911f030400110140d000303680b41a80d0100565101c541280380c50101c03440d000006050250612103040e10381e1025810040c82522007580350002c12403030308034a10400c00a0403080b50208060303556940c1d1026941c0d0010191024242d542800710240207010f10075400401051030203d50b51a2503140040c060f4218441c50f10200300f042c0300100d40107200ea502e000039650064002c0c088186450000c950200a40d07105031594000e0100100250f259207035100d10f0a40440181641e59400152061800d240e0340d03c16400ca170040700310810041c540f070044a0440e040c501e80450940b02190000f0508104d0251036070a0390710301420909044840300c0a8074000c9011400e4403103ea9507142104c1d21f911a402d0461f070742500422180e00058500308003160060b607540710341d04070610b4075800301e0728040d81541c2181c04100c44403c2046400c0c05503000301c00102c10220011041003100e400b283d070f0181021442441414a5203030030300030b0f40311002201856140ea108121143c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 35100697 1250 35099447 35099453
    0x4090501030f05061305031e040e010603060f090504020a0506090102030c01090c05042307050a0c0c0602030d110c07061112030f06010f020d1b0606030609060b01090f0803040b03180a 80
    0x1c081c5450843c1c10380160800101201c03180307001c840c8030b1504400903501d483d82c4001c0302003000d5007030072018106020512010850300c95038550603000c2d00281e20300156850900908480000f1240d0100c0005800c0404102c010780325000c001080311f03010b942e441d85624641c80140d0850080400c03025007980780141e01c2d414001802c900d182119000d442c108644e500b81207030540d9006180802400f48041d803030204d282e1611940041a2900e8207140c4084600841d940c2c0b103076100800d9102c400183e0004c1449903071a00640301d03610315140f0480f450303440c000021064076151402c5210755414410b0303030010314821660602c914102c1e1050281d07903550764600102c00f503212000c2600e01c240052500805030704147d00000b26a1391001c010b4441400c4183c00c0301a031080000007240454480340c4407100040020441d00500e040e982c45860040703200340340c45000402c800102c0e4400310414000950402403410048101e070706940561040c0d55030395581000c905400d4441c042555038600c140e0001000b8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 35101947 1250 35100697 35100713
    0x4080a061a0d02010c0807020307030506040303090507060c03021e01182306191109060304030807030b0307050f150c03040b0301090b01180506090d0b0702010b03010b092701020409050103 82
    0x1244003440340d48106a02030060180442e04a4002400714100604480104003c0303406040d00504c0141160459504c0e5940d4070f046c0070080d20118003098645201c0c030104a03050080b04083c114614091b070403100e032034030002c1d55451454801048217503884c00543c3c0400081d0031401c0590180700521a00118030b161101d011040e900c54800707540fa102440d0500d4101c00310b41030b4014a41c01118005016006443d40c0003400c2440c4e04890f4400204500d0a268443c100030714825406626002c050b4a05140b0180603111104007440c801c1e000386600f40300d603a032a903803480707039180c4141d44031102d800b00c0300c10f052179a202e01c1905049500c0f01050000e6a9095200114165020a20240302080d8904011740d400b402160248801c00c031240818071150510b0b40281c85900d000414080d606000c0744c541c1d107a490000e031200c00050351241c0340c0c00c2c1c0c41c3c10309010f04c0b184c0c0e510640e0300018078a000b408002c603240c0744400040c0303031070303002d80709400c0d2110709406540c0074103100c2c0c9003003245503528540205 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 35103197 1250 35101947 35101961
    0x60b100203041a04031a07020c0409030c03020d111209060408030705030304020a0b040503060406230a0c09060212090108040c0305010c09030303050c07051c18030f0501050108030f0a0e040204080a06 87
    0xa807040512002145081d00d20142d07000c17298072102c00308101c9590b4528002000c401803803a01144036141c00345080e130742e843c0141880d00b800f13501e40c1c40090000707050090170501407000320390074403000901c002042000065480302a400000c0f100d03482d0700c01c01d80010805c0c0305650180c801e511010817010240100440118081d42c42110230840e2180d9814800081e4040c602c00c040c1e06800c0000014049132094100c0742e0400000480c40f0741d80c070005c402c081e030301e0071040e04c558081942d80c0d02c415250a80011104001d803981c2e000400d810400c3c0b42c0c40d003040d072250010140c10460000007203007c1142038121900035591140082c0030300e941c40341d4020840c0e83d0a00c8180d0009080501241101e0135074011280159041400703491107855501001503030b2801c499a400411401010b9a2501e20b181052203020b941300302c8071500c0c5090b00c0d080182c01d40d81d040e040a5120b030810018140c40790b0780c0a04a502d1900c10b410b100345920520000180280203a0b4000b42940c0140200300d03003013044981c0140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 35104447 1250 35103197 35103209
    0x1509070c05060c18090103050307030e040b090f16050906031501140a0206100f05100e06040810020301080d03140f0601030f14060109060f09050f0a0801020c150109050403090b07060b10020304 84
    0x955036013030110400004000070f01c030140c0150410803481c0302292249a4039000e00e10302520124030013200d03001040d400703501101c4290008504d1400d0010302d5909140b114403084242c9052030030000800000b400303a100c0500f01120490031128104003c2e4040c2c02c040c9000401150440e4940000c00b0000c0d443e004202d868007051940c2007804911080790325240c00030340c1c4000d020508521052441590750b030403240b40c8550301000038040002e00303c000b001402d04106d00349001688a501d8501040d18121801c0d09400905081800c070b81c1e4406142821030360700003098144000d03d9118040142c0003060881461043c0b54100a507022112980f20380c0b8500804e4280e903a524099034880c0101c9000c100d441c00240003801c1020200081d241038501004000c0d03000b040c00c1302d80c46d41ca07160542280e1220919018640104801c0c02503402035201160040203869820700c030b185400da60003080610603001c1c407001c0750000704d102070030320600d030f0700c9040d881c01e01401181031484040006962604a88070340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 35105697 1250 35104447 35104477
    0x5040507080d050406140904060f1401080f0c090108040807020a091a040509070b0706060b04060c0201140403020d0303050403030209040c090f1a03060103090201120f0203060f01081509070c05060c 86
    0x502c1d05184a4821502115056502d5104e016038206400d8100d6100c3d05049074420384a080205d850a120300c40b42c0001c0c0123030207980d4042e1550130009806588000c0c01c109840c81e01c00c08008076103286608541000d8000d18107201950703521300e1302c10101d020740d103000b94100214120121350f21940b580800c00b081802c0c401c1c000014001e40402054030400c50340b50485401842042241d40114005484018855807011411641b960b25011068002d40c1c0701000265103050002c055581140207a10610303405c0350100d140600f10b801264903401d03d00300007410107036180c00203014144240e044d101807100060091000f40c0c24a24018590802409000c6103943c118000080506800800a00c40400044880d0559803508010750041c00711040a9061000c01c400b405030780b036154424a0b030305144034540182c480c00c0c41801d005030303a1482d482c864140004402800061001360101d02c40c0c005049482107150399800104980180b0442402001d43c403400b02480031065444c1e0103042c4108418407a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 35106947 1250 35105697 35105713
    0x70614090a030207090c1103030412030b1009060f0302040b0a090303030c02030901020604020f0a0305030f1c020909040f050c0a0902030a0b0103060501080703090501060509090312010915090203040203010f0504050708 95
    0x1915212900c01000a0244e030003030508220810b86600250b44d0f9034854105000082d18900b0183d066900c04c56080300c118024460780b5140b0b9406115003032090000ba01c0d42001c81c49504e6020300361a2050041d402070203c21048501e2291081c1c0446000c2d0801d8882c06448080c1d410000e05100f242d8041100403a0031310242403141d500c0001991442c1070141d006020949458003402211080c12038541c3d04980251000300118404000034a40c07480310050f081d039992441556081940d00d481011014180100700400340381d510075010b00d402a4000103200e05188051420310328100800d0240c070703004003032100300103200c1c0815809148211071020051004084210044084465038013030140401c81460200d03801c00c0c4280d01c4441080d2003a000014503588502c002040160210b8000d4429400001d82040b40208402c1460062040032001e110031102040c51804034016030040800c4a50701200103000e655094024038048200f5040030013050502c1e0800c55103c5605010304500d83c413070120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 35108197 1250 35106947 35106961
    0x60301050f150f031603030c05060906010b0901210c020705131104030b0a2004051f0f0509060706110304121d10020f070603050109060905150f15070614 67
    0x6495842200410000408140b03104100b00600000030003a5801d8420844400030034000484550081d60217512400d170855043d00d03003d450604002d20342c0d94150404001086040d07943d0302911100c080900b001c030b10007440c1e00103508052010021001e129400c0c10311003040c1e0390700412060242c400c240d407039a5203040c00024040540304521041c0484d40c4042104101003a100e140d070035000f03240e1003400700c0c1104031035070058010340761a03142010361b8a0014041180d45403400202c9081c070080c0c640c400c000340d09414050002e4a00355060300a00400156000c83c540e06c50301110a110ba00480c1017000301c05002501c2c920360801c503004c84072511886984a00240528031500c40d50324000c9620013180c0e00c40042c804000e480c08016815485480100700d220281441300f4405080241e400107640d624007980721040d00c0076580035458252500e070a010032040407044200b43e80d14143c400950344510380020170021440c601040701052408122030307007002901d40214000f0303590900c0003801c51b10b810b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 35109447 1250 35108197 35108221
    0x30c030603050303011202010507060504150509010506030a031808070806011403061003020f040b040f090b070309050a02060a090b0d0905010b0a0e060f0102030c160e090d09091e0204080606030105 86
    0x400058020f40c0b0038001003206a0090b846da204561041c58060b007080c11039515081920030685007110503030300c80d072488810704c7c8140c800d155010641100078042c41c10000e02090315020b1260b400340c06c0158412680c0041500460410000d00b80b10040701c48595a500e1503503164482030040000415459001006925001038414020f08844103503000c0307180796500b000000c2011910064001d61280c0002c000c56441d485441007045903a07e01050805161810640c08400100720000745450030990304045a0001080740b181030f4141c502e01d0f621601c0000581e043c14280d44100c90442000400001a07502e41c2c10209420b0300c200028080c0880b103204200b0410300a016500e011520000012064907219414221268040c01030301c2c504401140f03941d05140c4080142e07030101c45130f40400c21a1080ba040c641c0c4c0c0c0318620001400132000c0f0000020310a0000c3e104034400e0715101e850500c902070864403442c20f8025002c03811540e4542c0d8010b10b0b5102c800485084c0d11039441c000004042151817 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 35110697 1250 35109447 35109449
    0x190e03161a040614071104020d0b0405060301110405040b12070f150201020307050306280b0c0601090b06161109011503050603070f090e0a06020d0213060e010203030601110a050a0c0501030c0306 85
    0x1901c0749841c2c41c904182c04d54490300f06003400d40e140c1003840c50302d06580e1502e20040501499030040405c0041c000d038140001d541c03018207030900aa1501c4840d900c107ea00c80c041e0b1301a548101e0b00070034111075280000300b0494401d5010002c40c0140c010001d440760700540c15004454540c000340d5190b0281d01d000b81d0803804203c6190012800400c002001e600d01800120030300280d030f001800c0700325903640c4281030003011900560501d03807000580000381c0c0000c11940e801800d42580520071400d401700071610501400303041951880d00f601052081005840b11001007020140030b0405030740e9507000c030518540c100c14032040801d00c0c000100c2c205050208150050300c9000320071541d490703e000c1d078480052100c400307004060301440140c2000506135000601607150b41e408003584540f060407151a000300b40e41d10960510405205c0307050700b6600170050701e91002d02401c184100e100d00502041c200140c4100080c064010005244104079840d4009400e50701c080e40c0800500c03503841c0b01603003205c0103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 35111947 1250 35110697 35110709
    0x611030301061d030307050708030c15150103150905040803040605130c030206130f140901050303071709010c0503070302060f15010801090b01021218090a050408190e03161a04 77
    0x2c0006100f4280c0d1000000128070314000d02117901e80100c03038071071a06081084e040380140ea0000a03c1203c0c021080001940c00a60720040341c6041c1000010181a80458640356062503201d000701c107001f81142094200801d6080e01c24045450645071294007540300f240c040769114504800300300407614881d10140401c2c0c1c0810078001d000c1c00c5400300021504005400e1600c07107548000843c41e03100c40302001c001041203540c040b00380031904080041c0810140c020078020f074402e10801000c207034014412244841e46800300c13550f0b19a0400121103240c48100050481e11002078080100355000a01e1172191034806503942207a203408002c003440410b00c1c1c0c3c4c01c034000b69426006224284955014003404601401120001034402203021b1042d00103030080c602c0786d41075440142c003a084c51034500f94044070b1100b0402841c50640e50f014400c4c0aa41c8508018070740c440308002500e4003c0d5950409540f0040c02c807007501c440b02c0c00c0180c810515001d0350500050007c0e1100070540302c0300960b001c0c4e0b10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 35113197 1250 35111947 35111957
    0x20703061404030c140f0f07090e061b0a0201020712051c060b0706151d090601060206250306050a0b07050c0607020d02101215060e030a020102100f0207020307060306061103030106 79
    0x203801d071034030501145d45006030030803809001c8106110f00c03002c102e40e158200160000d01411071500c0304000c21900d40e00354028070b42e0050b008003d40001e48170800070f145104001d0b603984460811504900a01602d90014120390303040c400030203201e0b04030014201b13a9130b2540c103083c8010700341070a09e0f00752405031248200e40282803003000300140c0160000c0800d140300d5250000445da407101d044010b191444007800d19100d090741442203450b0300303001c1c003400740603a40010184c0c0e0510045400c009804c00004407048071032251180c000c940700c0d408c848002c2c080241403000721500e54440720526840b0160841c0c080c86080402011400c041c0181c51505400408000389032491350240815801d580490305d04101070b909880e1040c0b5024820146c881f010038014801300340c01e050b03010341a1901314040611a40c00b41c00e0300c80042c0e0340042c00c81020105164045428880e200d28400a80103c0c10000e60500800e58041007650749980400b04484d4165900031240070940015612031000380900c8000038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 35114447 1250 35113197 35113217
    0x11809030e04180812100f120f03031503080a03150b0d0507120504050a030306050d1203020c1e06060a0617060409080c010504050a0b0109020408030301090e1c02070306140403 77
    0x22905078007203c01110003403180c00071101d003540c401c55031354070120100e1422070000040c01410f0b03240301d00b0340c0302070b00d90109910f4640d0700b03191228034a0309a5541c001c114070704045902c0c0070544207030014504075445090030400c280d180c0ca0150b007150040d034038280019290000e0200000b00c40506802214051a19a4640090351a51001412004048800b40300e44004100c0190945d07108451086000e10702400c25241c861600605560b4a94006480f0f1840131200f040070910841008138642c41d54200141c0d64606020b00c01d08000141d008820744e031140e501406003a09000c1101842071800b1564815000d1310317103a041da034003030310040c510800d80c03001701c00102581816440030b02c845016051960400c50500f910b0781c250b8000f22000c85036038108030020b20801c214841c4107409000d40050650074035040c001580e5030303400140300e02d003074042d1694040f6481d08002d100130185491070350700035410040700e01c20103542c8003220310084070701501d013034030b4103071134a00c03149441d801140e050356000481 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 35115697 1250 35114447 35114449
    0x9030e040e071a0c011407080103020a0504060b03060f0301060b07050304030b060109030804031b0306111e0a021b0604050607080a02100c1706011101150302120a020a03080c160e011809030e 83
    0x5410a050740c1300c80c0c2d035039070001c0503007030305200c994520450140d0b55501556065106200402000b07900040c05682012828005600e070711042da079002da415a0402403d02d5080c00090241065511055284000240110a00c01d0210080090783e00851010358282c80c4d4400449408480c2d100142000400740002c0c0002440ce456080c0700d914588074004c80f458a0307484c3d1038112940c511b504880c0030f03030000344a41e0b0541d00c504000d4074010140c6040d824040754800281d1030b150a8601841d5508a90080f1030440d5100783c25100503040240c070709612500d030352a0a82c2c10303900034150040548504585003021059900500e84420183d07138405211100c3c103d101038104401508550500a901c48071015400c0248590100f06420449603843d2520798010b1204142c040c0e045002d40b60095040c500140e10344142113012650f014128541c0e03200110222410160754421242071814034800000d501010300d10510b0503500d032010380041440d0860f0f0480300701c440c002c03c0100407079482400c41d409 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 35116947 1250 35115697 35115749
    0x101401050a090807090c030c0e0f130f150611030309120307020a1407180e070b0a140a02070e0603010905060c0c010902030a0c0609050a03080910050c0109030e040e07 73
    0x241c0c081800d0016070b15403201502424903445400c5450002d0380c404100301560386c507014002c0000100e00707142d1020100c0901007000c241d584501c403801000c1186201c1d041c0001d030391140c90619482c0000b0044000760b0f004c4105401ca40e4030400d40080d400011400c680c501c08030031280100c807218010403a100318461140c0143e0001444a010340c0a0741c038a0a01250052000b80744110804000d44482801d0007a40c41134010f008640d1400c080c64107012444009002413010144d680d00c071b50b102e0300c0e1040c41004444009040f0060145188042001c41c0a09e40015076001918201040700311555551014182200c000c1600607200707030320035400314040c88a00c0f0001e0043c1d034103c900200e14034099801081c0391410040f800c6406444004080080c03643c0800b0a0780903107070803030300342130400c2c9551510007a60046192161041c0e801250f05036025010300125042411024000e0210b00c6c402d0401516540c0404a0a8010703400e000181559a10210781c0344c094510701103035400b10003081003800744 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 35118197 1250 35116947 35116957
    0x11707240c0f0b0a05040507140a090203100321090b07020603150111010903050c0706030b03060c0d09020a09090614060a0612150e07090602030a080703022b0b0910140105 75
    0x842c42e20910010010414141e0f407284903900300200030505051501d4036503c6c05506074008014032045480a40c0b8035a95000a0340490304803400258903501c0b00600d0f22107078000c40e40000c4c48403601450390200c120803d0700c0024142d14035110f941c102c0b81c0c1c44001a04d1880f07907601c001d40c002c004000003407001003021310b0891030300418905100710b1006034486030f0840e8601c0d401607000c610041380141c80039100b0024007018001c0d51405001480340080401d03540e18000d40098040540896601c620792950340c0300d88116500280500001d80c0c0e201c120390002c0c050800140c9009082c0080741018003820240c90b400341c80c01802c1500316900d01003007207507201405101b08030980c0e1110b1040f0101c0744c4410155010341000c0c0003e03002d9041284c0701529215059001c0c1080d5002031042c0c181280c0c0191041d07070700100d40d003003f40c2d6075a4160f5104201850110a0807103000c9110045515022194040310007264280e8039901d03940c0303400d0107003050007260744225810405085060702c1c041d407107880548 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 35119447 1250 35118197 35118203
    0xa050f0c0708010e070807080a0b0103080d020f070605150a150509030c06040609051c0b1b070b040b011a091003020f131401030f0b0306150604080303011707240c 71
    0x248078a8560702c0030350a5646039850300502d40d10100e402d001d01002404400d004203000401400d0304440b81d0782d00054083e05100c0581819400b08511100ca940c41c1c04480c2040c5080d055141e40318601d04c0c1c12402083e09503003005d05900b081c01c2d0211182400d00594081c0c0e00405c241c001003454840b01114964807015001e6014041e40c0100d030001e4843d8000781c4043c011f2500d0f4140e2450500c014420401e40aa9190540504000e041c5c030201d0010400c103900030701c414401c40300d50814807040070072034402d450009100c00c413002d041000344150a030380359058441e00c0e844080310743c0c51540d02014a00070021032640c002c13400c1d1343e607070803150080c1d000f0101c4040481207141491034456a0790a0f00c201e1390b100003884118125040110b680c1842803001c116800841006105c17503803004296240d1004021000400e40381b40b81c0d00403540c80c04281c40c01080080304807950f0350f849058111401d00358100201d420320a000c00821711120341d0a03503212001c5514521f03511040303254011281c0241c500c2d425 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 35120697 1250 35119447 35119453
    0x80c01020c040510090609060303030b0306040c21080c01140903040503030405040510050904031e05071a0903040816300303050a09080301030f140c01050909040c05030a0f03030c050a050f0c 83
    0x6000c1c1961b00418000b00f5038054001002495402c2c080c0585049283d19442904103408000014403078016200170b48400264612140c05c8503540000400307005c10016000d4400810300440b000015081511030f4004888811201c2d1101002c80c2d54034000d500a040d0300da0401e000074050750401ea404540c0c00b01004011141196807007001c101e0928040e00d054001504100698060382c42c200c4002e207410b4210f00d0154905891915400003c11191710f14401d003c5a070401316440c03140030026103001d0301ca014182c1744080c20720001c0c184403001e40e1180c03010010754540394540344400c83c00107048150444001160400340e565040b0000c043c000c05442c0ca20382c1d84c418400109118001030340c0030303501c00c00c050350000525003030031020403010b54035060740350384480704201050f603011081c0c42c041c11042d2801c4c030054070380d441c18004620311500015010710401540109014034032100440300c5029882c200040c011207a0200ca4034458400f0080105034100038074206a0000d01c014098425400d040d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 35121947 1250 35120697 35120699
    0xd0f050f1605030703020c1503060111120408010603020f060309070b1309090812090c100c061803050702010f020105010e060607081306030506040c050c06060603180708030310080c01020c040510 85
    0x201c061500350076105036039992001c90305404040e010015004070345012101040d0000e0303c035a003c0d0740d80c030000381514104591503507041e01c82c44080001190801015052075261a21002d55a00034000c03440f00780d204240300d416050850410004507406100840050440c880c144590307049540c6c031119106141d6250b145000038400880d03c1000f201c0d6104192480c2c2d103d60180074910110405880c0b02903a410004008085603075001061025900d98201616104e4881c10080c00501c25400100c40c0c0140f4012048101a8808001d0107014801d0700c1c0c0c0000659400012800c17100240a488140706162000c25803d182080245c10414460760b910791822040c80303101d0806007101d0b031010000c02e444100340081e030f160501482940303001d9460038a003414050501666180000f07003140c5e0040c54000302007103c01880c2054034840032000d9085580c2c035a62241003507500d50040701c4160390007000c103402280212001c6031001e00307110141e00404001c900c1c41c040200411340900003100038040110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 35123197 1250 35121947 35121967
    0xd0203070312050405040c050a020a170409110706050f010f03080304020d141b100813060b0307080f01050106030903271208040806130305040306050603010f090b15030d0f050f 77
    0x2080041c0104540d03e00391118078081c10b000030f0710010018030042c06014458818459400540410525001000c0c80c14048000b003420841b03100366003044408504006681010914040080a01c00d114100400056a0750f0b119840010b80c21f00648803444100d00301000803c0c440406180c000340018040c29030708100355202d82a4081c1402d014405410030352460321050056004c0c8403220b0f80070381d6403030070300071036640001c0c4001401408207084010804c03500040c009a0703800750300405805011907800d03584443e40183e0344c61480030b1100343c0390b08240000c50141d00c43d010340041140e158071400202c099610429281c0480c1451010b2610300c43d8000107113080c260310800015a02505d6803aa44a007070000042c1068401481c052580854800340304c0001d522030111011a5004580002c880c1c40c2c050000303014280c807000040c0014146001e55003407000c0c80c81082e02840b091722a0100654602050640386c503000c400803000306038260004411540031f40014540320080101c5d40d850450200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 35124447 1250 35123197 35123213
    0x13050115060e0307060201020309030d11090301020301030f150b0a050409020d0b0c040e010b09100c0309090207030e030d020c06030a090507081204061205060307140102160806070306050f0603060d02030703 90
    0x1a2285002903000201c0803003d00f070a00680380540806e100962a510300ba0041558074400c400c01c4030700c042d50b60b40481d124062110142e0b0b040c910002c0003550f981d603490800c0a8803010406003542c25020001c00031604078002e10078018400000b800e404002c1c0e24250411000b4402d00c0e0090b0b0f009199106030b0000030b41d6403295284142c2c20342c241c4a40301c41c10a140940d28082c142c114484040b820400c1d6142595281d42032007040c00caa140441002c0701c180b070201c500070040d5004051407030010403408109a002180c19114042c150f0032504400c0360b03034030101d0b40c452080e200c041d04903204001048840001d600f00b01143c900410456100c0c0ea61040c40c20300d400603d00c8180308030760012506110780360740016000c180000005081c4120300305000003d8844c100d0344a40c0f011038403602d91510752640203210500c5010400c040c0340507465074854041342c851504580340000680b40c200041000d103007541d3b1510514001820301420350b91502d01b40240040e6044050717915200310b00e00040016200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 35125697 1250 35124447 35124449
    0x80715090b07020f0106050a0515040e0a0c0e0913060b061303080306040501170c01050a14180432090120070308011202060d0f02160b010815090613050115 68
    0x40001d0a1580b51201c002800c054911100050990400c10100190355510100f5425224220303809e0411024002d040c007000d00ca03680c0300208403104a030030011015507591281002142540301d0071860009401003204000048030300d00c081c48030744500c5d0000701d01c0580c42a0b007000700242138035150989400c050030102d1206e90044405400000400c8622300701406060300420300b142010340c04c80750560340705813103000200445042203004141c1e00740440c030440d810310070100300e8401599a0b00f5072440001000358a0a00140224102210250613500c003d10510702c480170002e810514025521104000c10005041c8070515901c85010480d8845019002440102620769655035500d0524000c1c00700881603008905a07009200300c2405600e50000300c9411800420340044c04c1c0c2e00e0740c4840b80080c00f400c107501210403c01ca41000c20043c0254106040e106128100c41d11000b07902d41120340200c04440000c83d9410100218910b03801e202125030105202e84004240741c03246a038004030442c42 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 35126947 1250 35125697 35125703
    0x506030f0a0606030606150906030c0c020a060804031107050f040e030c01020a090e2805070c0516080f0303100b07050307020d06050f062b05030702030706020606150703080408071509 80
    0xf44480400c00c20820b0700c1620000c0044c0e140794138550706040300c041c0c4441800c0c071035a414540c03905a07072450a40b11341d07040e00328280d0041c82c0002d140d849035030090a040089808034003140251b1440d2182c103030001101021510b00030071701d102046498040c007014042c1c02401400300e100070702c4120a415000c0c0081c0030303c09003da9541000c01e10703110240c21118006007a1070101c00402d00200154400c00007161200901e9400128083d1914501250798600b00400070f0500d005d06c40c01d05484e596030900080480e0180400c9410903801020901e8407444191291448040389403020448003000324050318482e1b00403015203003001c041d0b4000c1542c5c0d500c0b844c0211001943e620422001c150303c00c0c1010340144082d03414026480384801c41040200c0182000c0702c0000050804800b0080704004480006174058150f808aa0740e508020b0740c2c1d40820780e9090700c030f0304591b00c8504441614a09683c03250350123603511840c640300c0e40c441103500d912102050b01e0f020011030b0040d60702146402030700180346c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 35128197 1250 35126947 35126951
    0x280e03030708061305150105031512031b060c0d0e1612031202090108040809150d0905150903030406050c040803160c060912060c031b02010e0606040c0f030506030f0a06 74
    0x64104104003811038241003052004c0d180c0801e01201d064405440420b00c1028204150341752a0f001c1c505100758142c2c00246d42c4502c007480004000754001c0040c0c1207c8d10220320341d00780303e01d11024613078407a00220f500345002001885013845800ca160000b015049140040e1801890f0044801500c07400300d0700403200d410896805a420154004000d22107000f0f0b000c2e0071800d114148000030305481000d080034098400115202466555001d0000c41c2d00301c8011101d0b40e00d88882101e03201034001144262054059200c21080c5810101605032180400c00003840c51540c03603644040c02058080d013a8014964240000f01d1400340800081042219000801d42500c0f5146032441983d10150000c0082100751413003001182c0e0701c00e40701c040c06a072200020400c03020404c01180102582c0503061080f59407440c00c150080d4042d8400702c0c42c2e160840503903103540e440c041448141c4a04116a00000b41502648105584654130550300b01c1001001c0c2d40380c59100c200c106107044080541070703c00340d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 35129447 1250 35128197 35128201
    0x90c05100c051605030303040201120b0d03031e02070b0c0d1b08040b0601030b03030403020d0203010209061b01050604090807021009051002010b010207120305030403080406060b040308090301050609280e03030708 93
    0xb0a04100d108095401014448007403800e040100b42c80c2d01020b40001e050007030745404018980d8440d002a081c035000070300482680ac003a8140100908407640c41400f04074101d14191400c03404a0084685450f08416850600e49030311340400c003e984100c40609095a882a429540178130444030014148c442e55100031035801c06042c4650403042c081d100e01c1c10726261509502041d10040b00f0b0b0341c00c4980407211411845801c1c00441d0291188280d41c40d03002e503000850610f41050440c00c07038030240c903000c002c20055a50509000484440398000b90100700d040c0009401894442c0f2140c4928140780b40800d80965100003148007480c0c0c0d9002640941d448904c1038482d9641080709500910b61741081484025003034402501c203100241014040000000006003030040d5900f020f001016840d0765107985944e281004145a0050720344e2030f20075402c03c00401c410f0315001000b035000b8110792600308820701e4981c4000c8034403126040c1d0a8402a00e813000c0089540c014805144100b503162981c0d0300038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 35130697 1250 35129447 35129453
    0x30706030b0103050907081e01020408070909050f010c080f040305090d0c1e030213020f0f040e0708182a09040b0402190605030c0d020408010218012a0204090c05100c 73
    0xd0343c2c0007003041c201c0794001d0784201310300903000401400a402c230322a40d290a811320842507002e88942d03005401103210b042c40001c0d02b600c5075440b0054642c040c1c000d03680380164108a0a00342d03880304541000250052004c40e000e82ca804031380d55081751090400a01d41805840440c14100a11030180c1c0c10145d00c0300708025200203036060180e1240c01040044420b4116400214615042170800c541c0e2640840c0c2192980403d031f04507a481140c10081d0758a4540e00d20710b664070650220741e0f44001030510310101b1600034128115005480090300501045041e41400c0002c10b03145846c00019800e520505111648807801464010703070040881110900d4140107200e0000104540140c0c0c6081c820002c21840303606c48280da4219580010b0b050303480d020301a0b40406801075402c42890307940300080c0c51901541c040d000c200221401c3c0c840c54404820186918a06031114071101001d03040003c0c04401843c040e40038850b110b02c01e40c00080d4080d121000f041580e0b03203802425001c40c00f10b07100710080c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 35131947 1250 35130697 35130701
    0x150e0a031d0f090a150302060310080c1534080c0715020d030b0d06140a0605010e0d0f0f050d0807170601090501080702100c0903060e03040e010b1305030706030b0103 73
    0x280d005544600307500c46070102043c07000500070003426800c0ea0702e4407a2904c25500b403034404000c540050215440e810910407441c45c1d4a1144107042e040c0c0303d02000c1014600309007180d88024500d000c1c0441c1040e0307244543c1c40d000100e601c1d1100d5114008001401e0381d00310140300c484054015001a40c0720b00f50307800c0d014507094450700031f80e03401c03000c100c20006500e500043d500505803062902050f06000b0f03002103004003140c0300f0b0040600e41000c2c000301c203400034031030a280f240324406024031020340e841d4019514510040c0c24aa0030041c2d0000d003d0110310310404401e0590710440b50000c02c82c01c00d454250078029085c80c3c1c0d000040c1d0600500800030340c010ba1624006803014041c010320301708000081c1c040300080c42098180505a00050403003402800411071201c19000213001802c05460010800000303030000300d418a141c0010503074407050006c10b90741a590b50241103103c80e4204003000d40950466100311410b0710500e04040b40301c0d00c0034041d400041801d52004100040c0507000541 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 35133197 1250 35131947 35131997
    0x30c0e040c050901090f2607030203060c21010b040b0f04180605010206180c0f01020109060603030201061d0f01140307090603050102041a031003030513050306040c0503150f04150e0a03 81
    0x9a81c5c83d581c1c801f881640d9804205840d11107200c14107400004c7c0c490f0a0504100d00390b03101030344c940114410091000c074904001c080723650801c0182c3d242000c51039039808d903440342805545040f640611080c44414040c000400c0c04000c04203e941c04d090b524854240002e19480f02d81c111240c80340400c10155804009094000f12082c0755003541c04000080d0b80c0c1c0d1424041d0490348100720f5003a0b80d81d07169000b0b60141aa041c2c110f00248400c81e141e080c0030b8003a10b003602c540c0300c6d04603083c60710340224495224054010503c03c42a15002d0b40390550142e17a612805822070340c50301444800003a0007c4600c2010019803081c40003503100c504c0d10950340441000d580000171414402c000300000d9010b400901416a43d15080c02c9444810032150359030448601c0c0c0029405200b110140300070b0003800c011800c00c58404400f103031210000c140e0040041102680d40b003070429104408a03000422a0351a4440f661990b40d00003401e9411f400c2c1e052074540e48460941c00b10348010010304a244103012050707 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 35134447 1250 35133197 35133209
    0xd180b15120f03120c1c02070201030902090406140705091e06120906100504020c0d0c0318030b180703020d0b0a020d0c0302070c080304050d02060706020705120a03050a05010e0403030c0e040c05090109 88
    0x86c1c2485c0c912030200d030380c1d145030000c1911030990001d204800c6a01a9000551060300a44503030f002c0d00c1c0500d00200107081400001a603a04010000744240d44910100c950f060005400300c100040340101c0b85e8030b000303622214035074001002d00240344070300207016410b40b14250700340041c6110700b02160304041d04212500024001c0e8010004074a01940004080c0c009292030b207000c50501d409070804031b0305802e031080101c41c40e645810001080c40440e01819020310006084031000f0f48414146594590f000c0c4002034001502c5403403103012444954aa650040c604c0001506d0407410312440d10032240807182a1010960101e044028041106040006880f50030004c52515041c5070025003030440841e0024424600083c1001c01c001e695016550700b564028211805c506041d084001960061040c0d580042d01d42400281450541e01545048803078040c42d00790301c0d40742c0e0b8070101c0140c08000c00850922220f84a1040711b40c0702c0e84a120b495021696803151605046800100620021742c001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 35135697 1250 35134447 35134471
    0x40b0a0915020334020301020d150b0301081903050d0203040f051005100b0706020f04081e010207030806010302030c130b0a03140105060a0e010c0c09020d180b15120f0312 75
    0x604c401c1c4410400300b40108a14148251030610f28031102c40400340002c0c00940650000c0b07074041404c02c0ba500020800307a48080c00e041e61a803502820b035403030f000074450f4080319030080c1c02c42c50403e004c68411005031406458624078060400c0103c0c002ea034026501210104c00c1080c034030052001c1801800340b4054410030a000700c0c14070080901d00351600d802804440c9030000303418410410a54101c070804000344003456121390340d0702d05042d251507040d8a08a8904c1c51503038550111101171086035101c560640303e00103142c80701c0c4011030088d000144501400380c42003044035800c6a00c4910710009010240d9282e90740e000d441ea0013401d40700295045008001070b500144016950241901c0382000d1f145000d01c801c0b06000c0040b00d16104504000d08400804000861407412640040045c0e9088500a0210b890103005c02040c490030840054903ca004001144038407880122008030880e0080c19541006030001d011810042800c0f880203899000052144801071404141070f40b004410280b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 35136947 1250 35135697 35135707
    0x1115090d0e0d0209010e0601020703020a090204050111120a030203060105070609060608010c0c050a0212071a0403050c100c0b0a020f040e040506090c060307050a0912032d050405040e0102040b0a09150203 89
    0x42544d912045c0506400b041a000015401d6407007080000c0081d90010200c6108598030500040290300500540340041c0d0190a650300000c400140340c07022031060b2440078034004612500300c00030b40006d40744070b04000d010000500030038120301611811502a171030000c0d02030721300b021103421030390403019180034000040707160b0002c100013040c490000d98050b60240300d1002c585c0642800c100c4c0c1900a55400e101d88504a141c0050388070241040e01c0c81041201d2040c400c080421181101801d050b000094030000c1c02d400180e5068452500b200f40c2e080e0160a0054440940780d40750001d802ca50010030b1150100030074008200003580c4c00800100180c0b80d80581c15020031100c3c80001e1008051007400226682000e104900305e0008150450314142c02082c1c0b85001050490042c0440303c00c90112032180c0700400445002c18050b980a03280e05240c18504000c0c440075000b101e840f1b00d0366541c00d00c00080e81000c00001444c0209030399a0b2020010b0900284011001401c00520110f52085c45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 35138197 1250 35136947 35136949
    0xc060a0b0d0b06030c0910060e03120d020c070302030d03090303050606190c0507120308040b07020609061503030405150c0d090303020d270315110315011115090d0e0d02 74
    0x300112650350410b440d0035a03641e80f40003091500184c0e2255a4124101e40100565011019240c0c8161002030f540e840c01200c2040c10903684003551400882e0a5004104c00c45030030480345d0003040c20700b04c82d00a403007649030b4a80021342400704082d80c030000710b0b85820b214000c069152140551080d8100c8500782804080040d0100100c0c41c14058001e010341c1010303600074040e08000d0351008001c01103249010035010b19000340840b0054400b05d0390951010007103080a0300100ba841e104000c224014601599091695076407034060707114654043c0010840882c640d03c2d50400071510300400800d46035114140f8181d540380256854030001000b55281091000940c01306881200e000c81d481c001d200e182040c010101e001c600c041d000d601d10101c281c2c000082060300038401e00307001030300c3c1c00030020440300c902d02e010584001c40711260700400e2140382130a55030041c0e0301c2c000000715050865600c0c401952500d00c0100085c1c8030000298000115440100c2e44400c5090388600c06486200c5e0195843e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 35139447 1250 35138197 35138209
    0xe030304020402070f080a020c13020703021b12030d0b120312010506030c0405130b010210060605031611030f120105040606050d0917070f060b0904050a0602090f040606050c060a0b 79
    0xd8002440b80f90001191814490b4850185500c1a08030306501e6803828000340186d966840101030750300904019140302e882c004944240c82e41550541c01030305d03110702d0540381c040d0207003003100c00c07254422142005491810030800c050100c200401c1000111102d503042000005280900c46013103a9008001b880120250130000349d0455000f80e9080d40caa48403584141c1c03440c0240c1e04540c2d0071000c0ba070711b02c0c8030155103074100083d07105080c0c0a0360761405200c0d11580540f0031034068000410010400f056042d80c000c0d80703000c00405203240ca45840360015083d48d00b1580859800100b20401081c04172070801d64420007401420201d4042025030b240001c068030745d019512490718140d960b440840c0c240116160020100800548000d03a00c403464907003214880418082a80c1003481c01e00034210070b0500e81580341c0100d402c10b0003811100a569200e80295001c840000d8211564852816160301e560252038081c0ca00ca0300c03030a489801c09048249805001010044034600f0f100f05004191200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 35140697 1250 35139447 35139451
    0x80103110a180207081b030702040506090106090608040c03051212090304121101110d03091406010302011b050a020904060507030c021b1207180c0906030b031009050a020d050102040f090e0303 84
    0x41c0c05a103903ca1350905285501407130203840c07120380201a48000c0000c0200003040c60910840d0100f0464a81d0707014040c400000b401031310081001c0d0709090120501582d05658000c0c0b049615540d01360f240d945080c1000300702d21110800b124041740c0c40718400c40c3c3c8000c25600002a01c0114180b510717046c2c2c0c9514401c1320b24009440c00198060b1480b469220301745e40c00e64041040b0840b1410406500014000c0800c41010349200c1c8a90104062020b03010511904980d016540ca00e00e51827400711040b920703546c2000440f16440b818910b100161182141e20b4441c41c090a4000b559107403500c8081d054480e5041114110740100300242a03808080a03540540031007680c42680740308080711030381d10300b002d281c01c414041e141007a649500f81d606a04041e8000c001c030b0340c81785c40382d030b40c3c410040e0f09580011031078a62542040d032650783d00507019807014034854020421078060781c005401081d06004040420344550750001000e200388820f04c2d5040c401450064810403582e500c0c203084980328000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 35141947 1250 35140697 35140739
    0x8090c010e01120e0d020d02100902060304060b12010c0302090909061006140c0f0a05010b090c0301150e180103120e06030103080a2a030f08040206090103050603030c0d080103110a 79
    0x2a07001240950445030b4028030301d0950071800c0310a108681710300a5a1149407076500d00040c0b0480c15031020b80e47e542d000e611762850b4054815030940c0c8456a805000d005a54415030704402d5003030705035401c04024021821010740315240141d503450f0000921602c1e56004084100c254007040070f000c2d0280e140400402121542c2c03404000240c581c1c0285034203842800300c0c000f0144203000e0411034124001c10304001c8103125100030800105220306000c6070391000c035040d1661400510040080f10810060001104a540390409412040700000b4200d500c002c1406412402e4043c01032007013100444000c1c08044035401c0009007080c21000207030320791005010041000c0004120302142e203000d5031641c00c6904030000300d40100d904004000c42c0380310100310f09070000303031183d29030040c854050705002d4081c9801510f060f01e0f20710301a00541c06000c0103400150180720070880800d05900a00c00000003000d1607844900039455400c1c00c5051006038010144900b000c451304011340c9a01c02100860f03940c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 35143197 1250 35141947 35141957
    0x1205150f030c0307060206090106060e030601180b10081902030108030a0e0a0305030301061206090506060403020f0112060f03050f03190c0c05090c0a080a090201080c180d050106050108090c010e01 86
    0x8900340109082c04078030718007a501482008408140e5070740114406100741e5400e00200f0115545d04401c54000300c0354a20160550850401484030030144a00d05403101440d03a80803404c1e061944c04210041c800600c08000200b1003403c0c88040300c480d1003902800104800c007941154180954242c81e0700c0fa01e607450046c0000c41d50364100646512045100554111056a44940c0d450700060710844000c807900f14003918022000c10000302c9803243d0340c060400078159600f0142140e0034410034007e9109030606100d01503189a48250160040c0d401030201d5851001031140341d458130520308140303117840b0107498109116544c0c140d007180c41290101c5d8144c1c50301741242442d5050a40940d02580c000c070f50030904000800c000403504d00300070540c1050603a1401c41a5075071030300a200326101c1060007400078098034003040d04040403c000d8a8960300305900003440c7c4169a0004405114911044500307944503030081159607040046550b0011444018114000341e280000306090b6030740c030311031b41804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 35144447 1250 35143197 35143219
    0x4080a050c07090c05070b0f040f060507271409011206021b0d02010c0912031413080f100b12070308070f0b07020115060302040303090b03130c0e0106120515 69
    0x1000400a42c030007464001d004108529444030010034503440b240059500400c860081141c1100111001d032041d03400c403005090143c25559404080e00307010700300d0300402a04d40c0c6070390344c1c2205c1401c404403450030914078640858544900242021842800503204079043e00040040310180100301900581c402c40050382c41d06503402c0c90701c0c1c0041c561842c200c544034002c0040e00c915015809a00003154546400303020035601c2c07040e490003a131034540040000e041141ca007400c0384081700103003140d100e120700c20301503040d120400949071009031080c4413040e0b03221320700e480080c0d4194811041c130a207055854110040c404202c0550300c0880c0d03c801416480001070500a000382c204080071015030000114045041c8800001d000e420407140305898000c0312100011502d009200b00c0342241e84c9034032140021441e00c0c200301ca55400007488d00d845c050310b00c521000000d81643e9800003401880800014550401c040140940b03c481e0b150070115141105000d00b0b5840c080c42140503100480d2212061 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 35145697 1250 35144447 35144467
    0x10807020312190204030c030c03021c0203030a0c0212030d021903020403021c030e042306040209030c0d080c030a1701060513030803100807090f0e011a0d0309030b07030c020c03010504080a05 84
    0x244031765880540101415031022040000c104041d5044900803100240c2b00e408201c1036609812404400a506520800c541d180e454001c00c00150003600003020368124402c400307072030340c03e513404a1a000d01107540001ca1000500e03641442c580214098036045042a081d580401c0c1031100a041c0ca181c83e540c100188000c061140b240b80c0b1605038007500c01d000554042601d0380450134448003d081362030098001807240c0c01c01d0300c20340b91820740003401040a920900144800303002056416a000c2200300071203c0782020030802003501150326a40c0c00031056012013103c14481d01038201900300326042003140d02840c584404d0000341ea400c261030700e03580c0e11507a0954034204201c1d8019403090064480000d203401d1a98491380101c507040c94280305075403201c07004a0072036516642c0c11000d40301540c8511507030b003000100020124442c0c00d000501c036441c0e494440c800320040300c1c00c60009440b105451180713a4148040c0a00381019802844a400d05503100000750040c641c400041220204519102c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 35146947 1250 35145697 35145701
    0x21c09020901062a11030606030109021e060409050405060105030712030f030e010e01090c0801060b0705030f090d080c0c1002011509020307090504020c0a0c080307050606010513090507080601080702031219 90
    0x41e1071403500d004c3c0707860040d92802411262080702590300c00d0240320002882400c042c01000d5000da401821040f040f420400c0d8a100c00c0c00124909410460a0201089401c001e1080078040c90080000709025031424080614010141e0802c00c3c106000e00840000203400420b07400f2811542c1c140400c26030303880d404003401020ba203164a0103942c240101d2005100e4003441c482d082c0d640c1e580090000903100e0380c609109106841c401030141d0310801180031108041005400382000082009200142c180c84646482d08884480c100e107401c40c0080c15a01d150130f145a403050b800f280001e22850680e9070141e102001b03988100daa05d1600040090101d920a0807030401814009004540340c07801d4400c420743d41c11803020300300e490050300100401d151400005032541c1c03e03800f1000b481e007582c2d903c00440321030300040c604551261400001183e005c0880c01918401c0c605991561340510700f11000411040d4050000b0f0207640041114008078003040541907804260300714016600a001d501d0840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 35148197 1250 35146947 35146997
    0x203010e12072904030f0f02030c030409020903031c050108011404030e01110c040207080408010e030f0d0902040b060706090b06120c0f0a030b010609140103050c031305010906020409021c0902090106 87
    0x110f9101070b042004064000c0c8019450307542c00d17603c00200b80515242a40e1780e105a1500c03049640c8140010801080c80303400806070420007030300740e0f820301c043d0503d040400f20040c4030f04001140c5800c01400180424440d002d21380001a845580764101920003800100704030752282d0400080404181c211903040010811014000c3c0085640340c0560a020000d130b080350007060659428034410040d201000800e0314a0000b10800c1c0b03030b00e049410346404000b4203240108a800549501010328a907450f40302900d2b100d401340f4404030701ca411501d131514280300024001e03889000440040f0051500024a00500300010b03550b0b01c04401030f08001840115240c5e000034240c5403010000f24506902c02c814104642440d1005c88865804000650503542d003201c2207180c40c401440018130b521160383d0007000171070040000081c89402602e4401c140da0045d0440c46003e40c000880b40c0d01184016170280200344052000c001c0c00641e507000a03a090410b01c296010000300001d80380c404403014030114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 35149447 1250 35148197 35148263
    0x11010c1a040c051e210d08090109051204030303140114060c0a02030303070c0c08010e0d031107060509030318010902030c090613060f1a0313080d02040305060f040203010e1207 77
    0xf04200c4020140204181c0100309480d015000741016884a2142c1c4801c01481010700d00146c02040f080b00c008a0300c51000070031460041d07407a148483c000c0744003171000041030301840b00c00d565100e00350305010b0255841c040c00080d409140a004002c01d5141101104005508480d41d55440c100102168036024984030003a6040c0400010300604940140c11002080c0c4607618403401c0e80d5075000c0729401c8809068140140e60030044440864501c25032100342010040c4074101d0410f0642d0b00c4220441e10211065103c651001041c0071400d04005c815403030700d00c0103c0090104102990100361118035420001d40100401c0c800300710181c0d03440484103039070640034000700400d50342c2e028940d02c5090346209051707129980b01d00500d040130b010000c030307441498004118404050355943d294282d5102c08030580342035030b0a00c8040001003007801068051111400102c0f420308080c0101400c40e01c0300c400e0302d13030103611498801d184040143e0546500300c0c1c009154402c003450100d80d840c00310030f03021710300c3c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 35150697 1250 35149447 35149459
    0x51009060e01030b1312030b010908060405010e0f0d020304030206030c040503030304240203060f09090304080111091c0b0112110405040602030405010e120702041e0903050711010c1a040c05 83
    0x70600e0140c07000310904882c05103000d40d00c541c80e405030380c21000d08950001380207256035411020a650080d00001c0804a062400b242010341e9004031500303000099408803582d945070703400d000841e0010000031040540820182c40842465a0061359070701c00c4e03200082c00740d2070100024050080d80415076004200280075280d8a00e024500800190b42380c030300507422400e4013000a01d11130b0003482924403510307001d824840d20115a00401461203c010201c0c0c0241c40108008588000280228280b0020301142c0c0740d00d90401c04200040b80e80c201202c1f16400304005451008503902010030b0307045038ad108201c2c0100e1461030803d480102418a066030300641001c007407108000003540110301c1207001c4c8000300906142051410b458905a54104140c2c410a00038174016241070360100e101c0042c107000080356511519080000e680e40140c00f5404560082400f82c240301d0301c032040c0c81e034a140901e0840340f010240d5a4101c00b50100007954152010b148000404220701441401d01510b402841 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 35151947 1250 35150697 35150699
    0xf01060f1101060f1508010b0708040303030504051614030c030105070e0904060e030316030b1008010501030b060c0d0207050a09060b041703071a0a0606020106080606060702030724030e030c1005100906 88
    0x7070070f6152170b1141d45800020620000005c3d20042c003030544441551200016240514644044015140c0908162400d0141d100404180304818000c00000e21001103000151440003081600348a4106240d0b40264100010021420344c012864104114211800c444584480c00d200009041a51481242e84000014400008542e00790b4442c0c0b58042d90b4103005204206043c003100b2510003100c0300215094000511556000c0e81140102e01f0010f4103050070140200f60040c81c1500310b03150200560014001406281800308161025040485003400340600d0204444160300c142e128190000c42d00061244500310300f4000c0f100c285400000c8003924044ca409112704403813090f42c100d0989440c0c4100010300702d00600509003101c40c41c4002c0c2929695180c00e201c46c6510844007281d25005280c1c3c046178600403005408078035054044282024186010003070115136510240c0c5100394001c1c01015101080040c0207086000c0300c150106d6a43c83d08414500030a03002d03049000b407a400c0c804 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 35153197 1250 35151947 35151959
    0x1e0703020d0b01020309010e1c020901030b0105031212040210091707090e0111030a02070c0f0602030d060501090e04020d170a0e030c01030203010b070b06010e04020d140f01060f1101060f 82
    0x6400001c0d0034100400c0a01441c90040ea680c1c85880007040c0403d14811a0034564034145a0204071b1403886000d4a16814040d03001509103c000d1b0011604401600300500843c05c00304281691804142c16081c03a101d009181c001c09803c00600091003640441a4080d0751703403045092500900c611907402c0d4042120354501c580700c916a000e41040949050001c040c0c059050050160210200c407a075440c2d41c54801100c0301030750109000755181c52703034110000b90400481d032440340104200c0d405503889031014000c0405982c140ea0015041080c0300c0d800b403280640780540e043d00164101c61504140da100c1c031340010304614030005590300b0b40380806c4100441da0130481d54030000350110305541e03c3c14071a500540c00c0b800300713010342a0580d1090144900080c043c2541540141050505911038104840054280d0b4402031041600a03124120080039261032000240c00c60a1a41038030082d41c1018001000c01021404110410000395504060f141c002e61013040a003005001019509440300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 35154447 1250 35153197 35153201
    0x3081b16080606010f050f120a060b04060203030703180b010e0603070306110c1c0905010f090503010c0507020f01090302090c0702150d05090601060206040503160614090f0d0e030c091e0703 83
    0x4540c64041000c0c43c107564411403044003147d10031080701c050203080c00b107211101c0e178003460010703c1641307100d43c0c0700f42c003090f180200000f07000105400d500450350786c0ba203000024143c03091482115513100300d4020900014000d113011505440090030007411a0b46c4d81030003e4580b020340d0b80042d001038a00348407080400c0d0104000e150f401c0e240c00c1198083c80b00480a120007072141000000001c2440c4003d04c0b5039072080458154110305450002aa1521080041c1c21200c8141a08001c100c3c0010714008500703154048051000c401d09044c08140d14540203e90451002400003950b00000200c03002195288400000306004110104e81c45a420703071000c0000317210540b40c0e91560f2007947c00024810788001699441103920002440c2011700c038061071240a25413400c1196601d441d50070400005160105142c400c82c041c034000c0038092100500305052a10140c880b008028103010000243c2e1800101e02c0540030b4103039180d140384c0c0e0b0707018011001d9921b294418400d5201070000d1211180e456 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 35155697 1250 35154447 35154451
    0xf05070501030c0207080607081e1005011202030702120d1401031209050307030503040504021e2706091e0409050a110301050114090f1503010e06010e1003081b160806 73
    0xba201001182811481682c0e20800740c0b1651801c1d80c007100015524603c1418401d401c01d12a10b21045000c2e213914250311181c0d0111050099003103011f80c104010b60740090030448200740408118618200300f800251503e106038180c0c042c1c0000016084a1a031643d80008140300742107145603c00d503140d145c44861601b8180103480000c0003410701007640d1802140c02c00c22640c0c400d00440c074003403800092101940025480c5061030b0040000e2411112500c4000c0100d000011948000750400021062054400001c407500840046c03090040a80b141031074031038008120140c0500484107803001902504201b00028403d01030791000030200a80b01c026402c807180308500a000d5a030f00c0d030f041c030144008036019040c0c2c08075858001c1014142401c5009401c82515224100160581000700c0c0c04d42d40100641e40103980700703000402441d50b01c10441038211a01440300118545580c1b1100120f019007484850800410240b071820340b04100604c6000b9811082c01188d544c1c0c0c0c41c88400e40b18642 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 35156947 1250 35155697 35155699
    0x180f0f0a020405010902030f16030204050a080607031a03030a03020d09060606081510080415140c07150203102c0f09010507020d120e03070203010504080309070605070b041e0f050705 80
    0x1001c00111718065140242c0c0d12a0081038002207696071110303c035080e443c00000d05078007410740c200004982e6442d40c1c0700684c0680b5010000705114204001c004040b508030b00e13030080c06030000c0410106190b40c08021180520704d50b01e0056118029000501e00500715901c00030b24661408000184098110002602c40c80211415400c0d20400038180001040c08150300c0000801002c00240040c0c011082c0061440701c2410004155001c0100c189c40118181c42071214a2404204002040840b24200030780200354001581541000c07800b0180d1140315000c0e8015100056a41440d22007404821000e040300c0221810300703508007040000f0b1103800540d1480000d5081c4000035a2090001500344498440b5035604511010096241401050a000c2c550074900041014001580d0709008aa0180c0d0080c903003640d45c0d09000c2030f040d2030a00150320500500409102e880702041c101404641d002da0010801c4c07942c0c0d03c0c1d10310078042c084045d8900070180300384500c0341001d1003000250b11050b2a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 35158197 1250 35156947 35156951
    0x908031306021009080405010503090a240c02011a06030916140f030a0c030602030603030d0203090c01020606010906050f09040e0a0609120504030b040609031803030806090c0301030b180f0f0a0204 86
    0x5210f40f044030a480e84080701070b104d407104003c01c1105511540046038803507241001d6680744011961407901e21848448141c074001d0040c13030005a020440d115101054400f80000c0041c43c12030344115095014000e501e81c41004084001543c0703410078016144d0bc5c0f000f403211066110344550000106080e40c202442c0180c007500a411540e00340010546c3d00f494101d03c03540801440d40d9903000c00380d80020041c982601042c402c0143d4100a1300166025100780001350601162040009152003402030503d410854104400c00605c0c0d0008103e4045c400e0900e551952484040c0201d00a410b40e0440c000c083e00c200f02c00c140a201e4140d01020081d8400d1000c202e2452044208803400d0140717000107086803005130007050009400d58404c4661a01c42e044c03100342c05010150340d2400345020350007a03012550901c01c000284c9481c44444c2c1d400403120035094110750540e00d404a010000030001c0e0104200c604406542d8001040302a00040c80001201c000c518098205500d40c060b5076000ca000754 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 35159447 1250 35158197 35158213
    0x602060a0204050603041203020c010207030c1401020406080a05132a090b0a050d11040203010f090b030105040f030309020f04020d0b01020f0c010e060f0c0a033c0f090803130602 78
    0x4400c5000319000c40b440144000e04503200c0352251265188141d244d0000d041d0308001e910020f1a0078000381800d18040d46400907084c1c0709050000c640c00c00d6098402d0b0a074810042844502d42040030b00303070003140c4a04006030541c0d40800340414003c220350050640110070450f2005a4035070384600707123840c3c0c000b41c992101941c0d90000209545881b55640e501003108001803269003070400803c0045809840340c100130f00c8210b00410102e900c281c01030f80010074001d100f448a424540120800581c00b54000c00c0307249419124140100c500060042c10581c445410905641d82d103d01d8450701000244115501c012078280d910003030070b10601c01401b5000f20300180d0100300021606c2d40c1003900607100c4403191a550800c1082e02c4e40003881d141c4000340c051007409d4006208001101915200391540c00c21410003601d8001c108400f0841c541284403410b0102e080082c0c01e10312201c4100550409400310a4505003c3c1c8442c03e86400c00801840f01249982e80a101840000101e41d0070340c0a80d01d41c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 35160697 1250 35159447 35159461
    0x301090c0f0e060307120b060403050a0209010608040f020d021809030903010c0804022b0507060206010311040209030a030e0117090703110105040b0315010903020310060f050301060807050d141204060206 89
    0x40e401000aa0f0b80c400800d000007201c20707008081881d1401c50203140060203840d0100019040c1d00581c00c1590381c0d9010101c22002c604143c500d05000d061a401c0001e064941580e40c80d2528114003002801420a10380c20300171910b4a00500ba40b000b403500705d070810b40c5003131024144d890f0000210203100758286100d5803549809004414011074000d40b12030400b0441020005145584425980d4003440010041020610901801000c1c168903805405154914201056019582c1d007203184107500c100f008003003580d0006401c002040d0f05007802140008203a005940e26a1480640880072940100b0400d0740c010100e02c9a0580c0d110380d40703c3c801c410005004640310b000e18065120008800c2002c0380c2c460b6030001f4401203110781403526000c002e450354003090900c0d8061440b4214240c07903c50074452020382c1030b1240e0280030168000c101051908002d5581c40740180b00382401540d000f40c01030701340410045c200040c403a080048910014213862a180d460380284904d4005000340c00c0441c0c14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 35161947 1250 35160697 35160707
    0x4060b0301050a0c050f07021c0807050606011e1107120807150507200c0d03030c02010c0509030307171209061504090b040b090106080d02070f0504050c1e0f0301090c0f 74
    0x1204c100303940d5460420440018846d010b5000c44820b0f680041c0d0002c15008404070040703803100c02072140d03141d551209250b00d411842c0c82c40c0601468103015480d48820b208400c83c43c43c03500b403403042d031a054503042170800000f42424035a401c04000b0311105000c1074140710300c4a0007402040d01c40d1100c05405400011280200c81043e140303c070004882010104003003410000504480e0340c0c1509132242d041c1042c000501c3c00c01c4103042100070907141d099040c00c90b40c0a110303002c006880ba003040b51600b07a0b6080080e0302c03441101801411241d81304102110910101c0954040d000a10601c0f483c500300048030320707912241124011130500a0700500491820107000e40c041c1d4a9100c3e07104091501d6964803141c1c981c100600810640d0360350706000440e02c40402c20407015011940241211506144001c24084070355084103005c0d80c00c0800380310b801080e40d0205c8000c030807050801c140c031601801e01c005503032041545040e00c800d0b0110000c00c03606101d0780440114822600e9550728582070660070740c3c0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 35163197 1250 35161947 35161961
    0x1060c030207051509130204080d090602060702070503060c0c10020f0c0d180303030203040218010906050f0d050c040903020304180203100503010e0c19050a0b0a0f09140d110904060b0301050a 84
    0x44c4042d414000000a401c0090001c6e22501060328007605058a6020840c90605403a00c00000204020b004002180d014894281c0021091010344690340c1803030046070380d900c805803480c0c3c15202c00286104c0341d00c0c41400030950707440ca544419580d5101d001d40317042460b00207500305085800748410f803208460140b420940b454248611500c040780c40c6440940c025000100240c1c1c025000070031400c205e540202105000c3c00381d6902c0010302a01340400d100e618001b840311107010b2503100e04c41e80003113400055002c8051000b00e4000c01c1909252071704038210300859020700030a800300144525010b64580107188110304200789001020355a40400d800d03540b80c1454810280c010882035410b0342082100c040d8162400d610b4a202d203a03907000490f40700c074455803050100b0400030400f80704c01540035001b5040300145203803100031a405c00c0c000c0c04a950880f50740c0303440b8070808005c12003005005d09a12584000040812039103151a00b0f0030070190034103500341c03440fa52805001580380400351040d21 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 35164447 1250 35163197 35163229
    0x80c06030106020714040b270a02070201050711210f160311040504061503030201050108160312050307020a0b010612060503070605070b0402120a05030a0905090f0c0a11010501060c03020705 83
    0x5482c40c80d140c10781c24442803107030708685c00c2520f03810f147e407954950342034200c00e9102c2d04801c0009219100d030640030028001d4880350802d401000443c02503a8090b082d2001c0782d03007158400348000e59803000580048265840c842c140340d0b0760740a4140700d5401048204c10802d914050f50010712001d0f200520401081c00010141c0e4001b41c0c1040d11800c0561007260701501c1120300240111100702807130501d42d0560301c04c40041c1e45400051101040c103000d03010303400d0050013412907046d0641c0d80d03020018003d980e11030b04104011002176203440c401c002c0703221850340003d000195541c40300d10080c44500d1000894003001d0400c4400101800c00085d075000311410b607074a460424105d0740e07498030104009132090b0f0b80840030010501413140c06020464182c0e205100965481c04804005090002660b1120b80b042024204202c48401500400c0d6405040e20301c080340e40e8090300b4026a003a0700fa0f103d00100540c68000041542c641248810328058026021204910356981c20081a000c9641c100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 35165697 1250 35164447 35164453
    0x100e04170c0c0303040b0405130207080304020108041704030303061706090304050d0807050706030603020111030c0307060f150303050a030f1b11070801020d05010e010518061002070b0310080c0603010602 89
    0x11940c056910380607107802084001aa00100181c0c0d0010f0702c0d40d0401e401245102c1c0300040c08000500c0c180003a1009004d0700e500035800d21055803618000350100910280c140804500050304200554410140e07103c03c45004030746840d102d0030000d00901c01030144034581100070508405d212000100180b292404030300452a03d0300300740070702441240c00300003103a110200f88030f0700000a40a00c0075002420555030009003051030b60000500c00c007241e00240056400400040c14400c2002c02110051070304080301103040c01070101c8032001400801d181041c480c04804c80031040640c02401002030607226039085c4203001c0075400e400c0864105800001e046c07141c48010400f1680280e1840d5a907e0070385041c0d840481d84c810382607081e070707101034800c40030143e40300014810080754507a1540542800c0c3c4038110300840510481c0701561000d060346100305c1d0f900340114038244c420024600600070380400b10740c0341d060410101c50485118003da6601d4041e400500c1003504014080d64126000c035402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 35166947 1250 35165697 35165723
    0x602012a020708060c030f01050612010e0408040e0a0605040f0e1b1801060c0201020d0503060d060b0f03030a11010516020307030503070e04020f0c2e0b0604050301090803100e04 78
    0x81258806030000e4201035020788500000c200505000d86842031600c0d166080e070720b1414020728181c0400c16000346210ba441405036480f03010f02d0a020382e05455440010b00600d444130709201589000d60f602007841c0c2c032014010041040d101e50810012079800742d5082c00054080c40388402520004000300d1350300d5002c3c100c0b00b0000c0748a0402201c681901401c40d144030001c1c0c0e5034010038480241c0004000c140400385150865904101c400d07081e090b245006811810010000741007503e211901802c2d6540f01e6140e141c440c0c1d01c0e03d10380699410014201ea80c0d035040410050425a9580c10406541d441c290014094501d10103807240d90b80001da0185107040030340d40e42074a0b150000380102040040303118101340326403182d20050090030095400d1940700e62500c0009d42c507110704000401803c0300d07944140094188001c1d0030410001517402c6c003041203502c000c0492800d01a07a07008551540c09c18407543e050210160003103014a080390740c0c01c03402c0e58542150000020013600c00400800340864 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 35168197 1250 35166947 35167001
    0x303050702031615120b03010903260403090b0a020c04050703150b0903060103150b1e040c03060602030301050d0620030108070e07050a0f1b0b01080f010519090503070606031a01060201 81
    0x511100c034000710701c2c400161b00c2d290703101081c2151010503048003c14490070140341d00c1e00542b030400d01049115500907126180a940040a07001c0340c1c4681c1043d2a00407a00014440c000d0001244203180604200620314100100401402c04035030306540c00c285e041400300d8161245c0f42195a000f0014000380810703465a030701ca4013001203000c000014190b540802e48520359918015019204003800380c20304041005040008559901a42409240c41c01c0307001c00110740c0100035281150b104645c91070f030a180e141400405040d120300c1a9443c07090118008844020b00030103141a2800841100c002c60349914030441c84000594040340071850920142050074810703800803001c0300c02e501e0715140007951844548840364407610115401c0c44440c0040c00300038020800b910134130034044001c1c0301c41d05006040b1410306440b6542c10303801645410b24241809010011192069400380f010400d2964a0802401c60900a503500b4400040500001415481402689041986801000840b0030b10301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 35169447 1250 35168197 35168207
    0x7050d0c080409060609060806010c030818030d0608010906141003020d060b060705060402030c030109170309070e1e0703050c0313020f060d060e0108030c03030f0c130303050702031615 81
    0x20310441d1071150412001c20242010b0099800400c60345c1c88200304c5609000001e414924014291410000315041040219603c0000c2c2034001812908044070001300f04c900608502c510644408102d003002c900003003883c2e055010200d0341d0f028560400c500c000c816110104010b00340e60f142003e845069061003d0b20301181c0c441e90444c4611070000e40c090000300401c1d090341000f20203850540040c0d0800065080c1030010240c003407800c030001c001000055907242802040d80c000400300c08000b0001a14152040140130003800c080d200640e411720b00410b800e20542c0100301d00c400c034180201d0104401601902400e4000c440f00742c0e03541d0540e07440300302d0510030b1080c0c00c2c403d0780c2c85628000300c545903840c0e12005000c0161a1800810b1081c20014801d40591041e8810328003540100700003070030341c2c1010069a403c5180680f070005d03c0e0b01d92000685041c0501441400301074074042c030001c101a004801451072a20950984003180389010201e0709400c01c91155440240110303106801c0c2134811 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 35170697 1250 35169447 35169467
    0x801090b0c0c03160b18010501060504120606081501030515060f0f0f090a0b0315090307030f030b15040801050612030a050d0227031009020607060525050a09050102010207050d 77
    0x541280c0c103124a81c4559184c0040c0041c05517a4500154140001038410720083d9a24281440081c019540340c968014814815442400e0651402d540003130100301031a0460002080441c00301d9120001078056155000428402186c20f80700d120031015a440c2041e144a1182070010016010030b8441c80500201407200340038564400303152030300741960303954094845000d0a0341c08000102a6180d070103040c03603c16545082e10340c941c110700800c40703002d00c000222000700ba411301e45800340d844855004d40c06025100821684800883c112100004141c40508200d6000c2402032142d82c8411080c031206001051444481e90010040c01d040b0300e000c1e0005050b031305200700c0f00510703040c2080003e4000441c0c0075070024100558103107919462070100080807042c04003000c100002c215a07030001d42e0503c108a030003400345441d000014101c0324140411a5402e00b07001c0000e1a40c1e400c680001c2280c1d00402d4480c001c101d0380440030030300754814400d4951440d03000d8003e06800741d4092054612030300c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 35171947 1250 35170697 35170717
    0x80402010806040231060207030b07030e0f01020c01020306210c0405070e03010f150b0a0e130905060906040606060e0901090f0905070e0709090207050d140f0a090f0801090b0c 77
    0x304681801003c400f00b9102080300000035814081010217124070b40000707158402801c5600c202e20500109080d801a00c0e00007d407400c0000f4020140c8021a0911103100e034090305951011840401240064000f14420f100840322064414140980c03500900ca00d00c070131000e103600040c101556410680c1c00300e40c101e5001d00b01600f1140101c0000781c00c0d191502e080c003800307036120703102010b502002c007c800c00600500c41800d0705003141c0c07540003400010b808040910480c0094101e60003141d85074082c0c41c3c01500070040d41c1081c0342000380c26030348200a03681120322038070300040060018401d102503010038000a001d50501d91030400544050084201c1c4402c1090780c40700340d0000150200000c4009042500d041c0002d86821207000d01201c0b07169100104040c0100202d40c00070704041030904c5a00003502300116000d11071a0101010300680300d40d07071040e20b0300140c072400c2c1c90307044080c3e60110360102c0f2802e85402d0f1141c90385130994004000007007480e0303d5540403800818150000d0079046032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 35173197 1250 35171947 35171951
    0xb041713060c020a0803090d030f09050d08030609150d060515060c0a0302012007061a190302091803041a270301050a0c050f13151e0c0308040201080604 67
    0x404092140d2841a607a0040303000c584881c00500031401c154001a000742410009142443d103801d01052600c03010120080811003411007040030f0038001c4103c000505009881c499141e075031031800074150f51041e51643e1146100c140081c00b00c1c85200b81600b02c200c000340421003403459503910741c80580409001010b031000b480300040c0198a40708c0c05404a01000c00003490a06014140a400c4401040c0da0360312104e1004440407003ca000b20850320380e80e0384108005a0005505990400f1902603000140c1c00041000300380011407040800100340c90084400d40520340f2000c40c0d07952a200d8032180c000260300180010010184000c5440d9500341e007a2840e036203404080d5080180100a0700052b1800c00380100260030141004d20601da0f109000c0c4c3e604000140700054064001e00410f00240d1003d0b2002460b034812040c103505200052400e03074051785543c21000382c040e2110120307452012510300c4241c2275111461281f150b01c2c00450700360300c4c0c0f400c0540b51a001185d14080081905d50459 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 35174447 1250 35173197 35173207
    0x41803090501031116050c1e010509011409040504060b010f03020310030f020310020d0510060e0918031b0a05010b09040b040303270309170313090b0d020a0f0501030b04090b0417 78
    0x400c0b44119089158480d5010f0440301c8156000c00804c0148c86045400e5034004052804240e60494100c0303000305800d080441075520390300344014241c03080b0b20300030f0f0b00103080a0501040124503003007190010801d0300c40c910500c89481084049002c01c0310154220044003c08101052004c6e0f1000661400036060310300040404480005030b1344098840254140d0303890411420402a15107000508110b00e080c80e03201020900041302d421001c1c14275600746416030000c2100d0070302003003103071071304a0040341c901c0320102e403600c010742c4a44203100155429424100074001626029160511039607000304180d50b50b480300d0714201e000f4000c0c207041c600082807100e4503980c041003400c40c0c407920f544a6542e11502074285100703085201c2e0100d07494090ba80c4180300d200141c02d0701032511810303903503546400070360320004030700160340c055141c000070f07400c140396503408110074429140f08016a202a01c05100d1840701009200466038a00c1000d0310513100c400200d4000303400c00c6020000381c00e500503864100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 35175697 1250 35174447 35174467
    0x3091315030c0b04030507090e030a0807091a0c0c01110a080708160b0402150a090905040f0204060605040e09070302010905010509010c0209070c03020c030706021903180b04050418030905010311 85
    0x1000b240c03c1404844400300c0d041003000300411a41d0040c08094005104801012448640e00d02072a83c992061110003000142d6044c8917035850002040051b48030302d8811300700c0c0e9111034641e1200170504900e0003030502c4014554098404904220200e1000b0100c0082c03d44600303605800c0f011046038003200411180b12103030f95154101d248180160341c07940780313410b2070301c1080302107040020183c85280080c01016501904107074081d04841c42c1c03450118165a0380d1411480c0b491080c0e4000b5403003494150049a46680080540265071b20000140c4803500c0c2c004046541d00103620000303000800c110740a0110307512620160804003810b040c40003280000341d000507402001101c00d50300181200070b08400789a4100314880c0b141c3e2094025245250070003e000b9110000702d4110030b40e0540380380f1000100f52180201e0191100c9003100400300c1610b911910255074041e100f120710441c109842d07039116101c243c070b0040d0040e50544820b9036071480c210041d0090b02454502001315002405100c0034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 35176947 1250 35175697 35175713
    0x51f020114070f020f0a02060301050d0501020403080d020304020307060804021005091c0b060a0506071106090d0816111e01120915050a0e120d0203060d120f110309131503 75
    0x40c0490f07485510070401c00b00c034024907120081152441c80c0d8000a400005a201c000480381954010340d42e0b16551341e00303410035a000e485241cac4001c00307905002901a180040543c0510b0284e4801c0301640c03285030b5141c02c100e8018034241c8010754001d00d6484c61003611070040004003070071140544040740c01e80d100400c15500590500c01555081604004c12500386010010b0300c4c041c0c07508441050034030b00761703403602d81c5d006030110700d80c0c3e01030040041c03000f6071550b5000044c0c2c8002d600088940cce4a1555203015501d054803030b1400c603104903100c00380c401d8178a000800c0c044480e20740b40038208180e03052030044500c40081608a14419a205800e0020901c0100c01c6980d941074084041010300380070000004840d54100c2801703164101d03042080d4048086011120a03049000c009601c13600d0381c00c0041d82e0012050f1008182d60115541910381581003100c0f5004402a40c50b402c2090300e4081e40e0f240ca900c100c0400c9507004c1c980ca8500c900c01405584000c4a01c40140885003003181c9a0740d603616 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 35178197 1250 35176947 35176951
    0x9050a030305010305010e030c030d02070f021504080601062604241b030209060301090f1104081c0f170a0e06180f0a0c090b040b04060b07030801050406051f020114 72
    0xc2d00c40005106001d030034081c100d10000d209000b1403502c0d0031865800e0b00c2c0d0141840300003000b90009080d03003d002c040c1c918502ca00b41c00808002e29544008800c241c03590142c0b02c1c00301070780a40c1000007050303402071000700c00720040100b07006c5454050905803542d000005008030303251801c1c2da50310310781c1003000000d0314408002d1100005451850680d13400c00d8600305510201010300400607520030786c86502c06d0741d04450480b0700106140d0480d000040160080c800d003154181c5000c600000c0000002840c07a0003140350780b85100580b02d00501c211350501060b0340c95008a81d62181c10105400c0c6034064541c42010240c0006403211594062340c00c09805441c888501e502991002c00c0340d00007844040300c9803514034024106c1214036640e5004c1c500d100e1140000701981c8480c22800b98886030440310b00c0d91401002009502e88401c8c000046800522050740010045000800d00b03080c11f00c9182d06403203005091401c840b49002e000e8070305407071135a5500110354a07181c56485021000c60014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 35179447 1250 35178197 35178203
    0xe04061e180303150501020a0b090a1205040302010f092301031b02070f060207060f03020a050705060c030a1805030412051005010807063c030b0303070b0901050f070e04090609050a 79
    0x1e10500c282d0600a040c0d0720352180300101c0300c00410080007145c3e000242150700941c4442650020303171721070b001542004400040904901e1000c201c000541e40e1150041090b05d03c04d803510034081c0c80580d42202c020955000f409009c80c0d1001607040100084080307803103103a10515010410408505400320303110a6030400f9405a0b0010b1402c2c0101c6032891000380181a41e0303c01401c85529104005100c03142036003040080c03543c0024622a05d9215901711096a17420204540da1400c190081ca600c4c0c0d84122001c01700e40340303400c840c24160440180b03200c00e0290082d0081d400c0c1070402c01c071010365070942e4808454a2085a81010500740e013030181c11b0091488001410907103251840150282201007206815125580c0300740a82410200c43c1c2c4001304041c00c580039240176401015402040950211649488041340490410028004a62260900e00000e0000b0f481c0e207091110f041d041965501c001c603400d51509801410141d0000b16032034000d5101090f1036000e0b4940724201030803aa415 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 35180697 1250 35179447 35179481
    0xc090203092503060c2a0206040b03090606040b010f09180b0901090509100903020a120302270f010f090303030209040908070302030705011a0a050402071506120c0b03010e04061e 78
    0x1002407103101e05c1550210141c3e81414802e000c02c540d44070001c50a21581c40100d0b402520041e029510303400159805082e036048440d03640d00704000300ba0354680c0101c401034031460401c3c0c017210081d40318503441250f002c03c5498400c2000d08001c40001c40c0c3e4520a640881d40b90f40362450502c0340c0c1e45103c000e008000540c0c0010781420640009800e140c9280d85066034241040c03c00d20019178000b41681180f608140c00718200426002d08034080d01c10080c260340c403c4003039548103036200a4030030302000701e01c1e0403100c82c1d000b103032218019285000c10010310b0f070129104035001c00100e4041c1e002014039141c000d100103000341d03c0380e07100032040e040220150f006074404243c140030490244640504648200300b42482c040f0f40c0f03c0000c024034000d0090a0182e80c002c5030043c1000400f400c860b610f004a2030302032007519206c45203052060038000c0103552107030300311200180c00d03403131802181c1c181c4203494580780040c0c0e100e0b21000d0160009441c2c807400c07402c4c20940c42403165a20300c40c4000c201c07403101c41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 35181947 1250 35180697 35180699
    0x120f060e07030f140a0203040318140a09050708070f02070302040204030b06010810030b1b07060501080c090f06010c030c0f05010c030501090e010501050f01260705040612090c0902030925 82
    0x2005044030344a1440042c4030b850080514504c0d51102e1203c4d6000e40c144401607901da585103000c03181040420380d051100c0789203100c0816842074843d215103174820300380c07401b0f44c3c22541d4165010640d44103481c2c4101090542e0b01081d032603071081c1c13207402e010306a0340111214070380e4039804a01213904c02d604c181c0d8800c2114060042030360380a41c406400203c40302c10300d003000d41107488110320b444018040b0680003500c2100702c000800900c094800744ad4010208104540e5518919502d901c03444080f244540d07000e20001c1c0d50349810641043c0074410603911414482c02c695400d4412614500054501304800420500050380901908851400560380415254036000640040e201c10940011003a4105801070000d0b465007032140d86140c030f09203401b4003444070906a501d090369460f1940e0f00c510f0109004c02404a0708000240204c81d0281d8549a000420b107002400711b03500798000420110303c2ca41e04000708141038002c0d64000741e80704162040c08481d1955840300383c456140503000500764140c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 35183197 1250 35181947 35181961
    0x30504090b180f07200106060809160b03040c090c03090203010b010207060203030c030606190809100c1e020304170a02030c01030b0904080a09050603070201051f08030703120f060e 79
    0x80d510045105584038082d80c42c038501010108003005107246a0030514000264049224240d503181d500d4210408a40c94040f510465000c0c0406000d404045a191f501003101401c0000300c0c601c0d20102c0b190000760041c24910302c107800758000f0300117961064400d40e01080d0101c0a22900c400d15030980c90002e080d145c98410701d0b0130754031000303000303415904083c4040140c550003008813039111600c14070003a42c03a596480062607a000305c15040102210100d040c07101e05421564140c05282c188048030814040e4109080c240d8412250b1103001030b00c1c1030010314504103001491031048419006583c14552282c04500702a0024414a0f01c9070f4401c24a41003076050a00403440012001e2070305107c009508400b09005481c040c00090880100007820809a481520501c02600c00202019524103003194001d000c2c00c4e0a88203010b41c000c5000d005018010701060a804a9070014040c0d41000d070540c40c00d1364010b6000344103031461512000310b00790090191080001a004c0b0301c18050190401403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 35184447 1250 35183197 35183201
    0x4020103110c061503011a010c0f060e150c030601050a03020a02280209090f07030201050a03020403050303010909140f0c10030b0901030c060f0207140402030a0902040e012007020d02010804030c080703050409 91
    0x101d113090082c0d1401040003940841a21040c095040a00f04402000c00c1481d04105850f407681d000780c2010300d8108680b0b284c410202d50003940e0881c0000000064071402200755035880b09560460100384100610707410f10b80290007a080419450068400308074108407110310070400c566006c6081010b17240d10b00114034103d5034460f040021100103101016121416650f03502460002905001002c070f40584040e10980480d00a50740c0001079903120359460f8101000382c400c1c08400c403101581100001c104040c0042c5a014460f4003000821850f0249018071007a1904681404100754548203110400d445031300b081c40c000c6210b40400f2a041d07240200003882c00f02600051070440d0400c031010410f602c030008d1400c0d11210b003150010307a603446080414008000111000f500142803c966001201043d4001d01114000300c1c2847e69034100c085c036401032449141d000941c4098124030810155115004055001e8805d007421701e001003482e103603201c1541004204030b0002d00e0000d0b05000d121064 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 35185697 1250 35184447 35184481
    0x5070303270f0b160618031e08040219080102030c070501061a040504051801050915010f180c030204030213060306060e0402030a030e0103020409021b0c01140a0804020103110c06 78
    0x746028244031400e211404450740c4003441560302252000c0b60031065600c00c5000e0b4940d20744e005508014016003050a541c002590400580100e0300d451341c501918200301355075070741c1c1c40029a25044696602c4d401c003c1c0c69001303103001d0040d44001d000b0102c0c02c036000340300440c02003101010319502d9100602d032140c25a07409400c006910920880c000f40303c43d6810701a01c05030f034000c540209055517848101da25034920100c01020725800c02003800704a0304081a0310750304c7e440da10590386007681c80e445907032140c10745845400c1100303182188e0910745402c19400500c02000b00e10780585401c0da660001110b585000201403d0700d0b0b0340f050100108040b920400c0001d10b540b40d840da10303500c0c1c0340d00026281c00368204003800f882000310215205a00c00e50494002e4112200119100d0494810801001c28541001c1d5450f1161104035007882d03002d80c020704190380085822500d0540d00180445680780094070882c145034607040c2e000c260090107030280081e10b41d458010b00f80b51038002c01c440ba80400b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 35186947 1250 35185697 35185757
    0xe09091c1710050109030807030e100818030a02030d0b0a0305011d010f0b060307030b03010b060307020f01060b09060f0d020708070807050616121104030501060b19030209030316080705070303 84
    0x703042d00700010398000101104498104801c55240d5005040640b442040002256488190715034540141900000d01c18040c540d40801a04140090090540d580c411580505c025a00c00d01031741c00c440c41c0b25040248607200c041d100d000100e60700c0c1e1310726094500c0380c3c080c184a03849418015046510910804850f40000f03031051054044c0200407403401e100280c668400c150b1186070028003514250000308101302e016007040c4d0740745000360009448502c1d000100304554201000060070150b100142d9001500040030146040800616000f040e0300441e09400419000c0c00b41e1404911500e0290034054041c07564140d03500c0503031070200d0806000420000c00c0d520350300500000c01d5407100401021920000b03000034880245e584c1d01400380030300d03800240381f9820444045081e205c600b001c3c1c26807011400c8014112032803e0b01c00d4003a4041c00b080b290b0980d1082c0088011880c182c0c070181001b80c0a89400c500d4000b0b561107290038810160005d6010070000a101800303040311154440c0e00d100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 35188197 1250 35186947 35186971
    0x23d0212090d02030a0f0e030f0616030b030c030304120c0b04030302030a090e0f010b03060a03051e01063c08030d05040b07110703020d0618050703051501060e09091c17 74
    0x40d17055000c2c0109400900c00c0d401c10052140e0340d900b94030100301c20851100c00b00d08642e442d02d060710183e0506031150415000081c1801004d00440c10300052004001c0d20040c091428241415800011460a04400ea4602d200001d00084900d01e250040c006503020340c1c0a035035118a011005802c06401e40c0c408420511000108034200b10399240b180e05407030b40341c040e03140d603501c3e900001014021103070805042c80c0a45039200513502c0401c0080815040c00400910200341e03540e4582401c840b00054244400c000012556510050100c42d200c6e41d0b1507070510040010703120315041d40345412040600300c00d40c1e80c42042c4024414515001c96010200c3d240070003d444200c041c071904c030000d03480001e0140b4601141c00041040b15080f0000300101c069407030781600d1b00e13414480c0d0388641030300c0180c0e0140152178a400b01004e000ea50f241c16035585e510f4080102141c5402d00070103000041c0030003594020358140c0c20b011040c1d44c00d021080111556441b100402c1024214043c0c0d0018120000a030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 35189447 1250 35188197 35188207
    0x6010b04120f060b03030a051209060402091801090c0602100b030106210f080c030d0b06120609070e0306010f050a09180b07030f0f05070f023d0212090d0203 69
    0x1540c401c2986406951024552942192a00e822030141c02c0c04c0c12956810f01000c9a281d60240c6e02c00c01a01e140791600440b42200d032510f003411a101d0000303460181d080420700b00040d94403c00d444038903641800c0300000040701007044d182c0140d800c0080d0041b00040e0804080c00b6141d651030700800d1903049044008025a51501c7c44100705a485406420303091483c64082c4000d200542c0d03005030385260849034040c2d99840400d401502d81e0310840500c45041e15080ca030214a0a0140a6582c0c002e07968814110680741d00082041c00c060040401c01003107020302c035907256a141440818001d081e600c0503415501d017001c0800c0080a050f41150815034501b00030079104660051504014030f400c000b44603035079201c2c104c0c00c40280c00080d14040c400c3c0c1c20008003c0b51802c0c2c640c04180f1526540c1d81e0462202e040c1d07803080f0b07210800354034018204441100321400d88040b001c08807442d280500c010607020b0122481381c1c82070b17030081c0720035592540c1110b01300721442e182400320158002031403010354900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 35190697 1250 35189447 35189459
    0x30f041814160f020309030a06150b07020a0b07060e0d08010f1706280c0504030204180b0106050f070b011509050a03150b1c120e15040311060405090103080c06010b04 73
    0x410884840c101040350b010700f0000028000c1c0111030a598001d41034648000c054202a070181014410318103000a04c0d0b0b00c0018074404250a845140364020101350005190004244868101060035204d165a50309002c4400004000c020001000d0b612031002c15071500d40c0341140355072182d11102d00c4802500d9a10079144020072160752240f9a0001214032281a03900c0201808040001d42c0507940780a00c1e20a08075080b6002d0801c4902c22202803140706000c0c5103420b5401c4c45080000c00e20002100140410707409a009000700c0040c00120904100c015181c4012000080e40003050440007a0070104910f5030210040024280030f82e07941d01410f203195660038001c2840203484515035079903607800c0203c2e5240d0802c9108008400c04c1c4100460180c105000448401140c0c1d1000c60b042070b01d00020347c00d200d100442158101d03980103080500e5520340b44038000c040302256034803810070031000c1100e540f800b145a010710b014030000e41e101e906100d41c8903d007500c1a04a41c1000e10203200810039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 35191947 1250 35190697 35190721
    0xf0d03020a080c0111040b03040b070903050c04050a020906070804030215190309050a020d05010b01080709050d0b0402191203080604090b1503070306020d0e010f0b01020c0909030f041814 82
    0x420b984030210641d0b03400b2201c40c01d0b00400a101e051150902c00290024044626801440c0514011041d9204688900c00c0a5441804620000700b0030340000d075130f4844500e4684e01250f8005000c40e00549443c090b40b0020b0b22a81c070000048524000c02304040c0309604012050100d002000400140790144a040321840b980c81040c11000701a01c0701c00d9201042401d214040d0b42d603a0181100c0107042030f1345010350103403942070006400920f045000413840c501c6561440c0803a000980302c0340c140c0704251165003224000420507a0000c0141c6c044a118507400c5007140e0040540ca904011404600c0c07800500e00000608000d1281e410640380d070003c101c100400315000440b07045611003280a0402290408545034005000680302040d02550b06e105074001d60702c03815640c00204100e200d003026a00840b1502490240164054000346580c3d04005a140f0740101419048a0520804412512059025401112447e0076280c00c44071a4502c9018041c0b5002c00412900c82514109299401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 35193197 1250 35191947 35191963
    0x6120501050f0d1109070314160f030e03070206040902030105010f030504080a05090d05010606030b0a0501020a1104050403050d06120c05032b03140903190813060f0209090f060f0d0302 81
    0x100c6003449514101c01c010072260411244d14010741142032070310b028100a4002c1c0b002201400c0b80c021040d002a0180c529044202030400050312030074004050018110000c10b01a0340a075111b100400c440c0c2d0159542d40d018100a001080c000740e500c0d810301000402c922880fa122800f8541800240400038084405aa4030007505141c13082c0c031500c0010005103903542c8002c3c00303440b5500c0e0040c0416055030542109003041810780e81280580d030740b1001281d89495079800a0103440ba0310050b1102480c158005c540c01074000e2401a0816400c40082c2040300d00c03952214005805149030042000f11a201b444010001100581a100060700400c20305548480090001e816080040f254890099102c9080751800043c040c078036203818109030344d403136010181d8074080a80c0b10030b411180c24416140319218030800d50101815a2841d1fa0303842c042c1c00c0003064421020b4092041c43c0298035541d00c003a02c51010b001800c90141410000d00001c1050788001c28052101e03002e0304000309030002030040e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 35194447 1250 35193197 35193199
    0x30c070303090c0e040f11030a0506010e04030c08030901020d050a02040311010c02010306170604060509010606090b0703090e13020f040203011406030901060b03131b050f270106030606120501050f 86
    0x10802e10300602e440c0b580700c6804c3d0450040c0030181001d20043c00700412007052114441d40c640c900b2492078000305551410004002000d82d07110200504c1100301c002180c607007151007402c000814502a41d140942a00204c2d01c903031450794046900d00b03030004a4000d258019450320402c40c0f0309404e644400212240c41e0416605100002d2580021648203910040040c81c0041200d00020841c10714203031990000e96007965041e05000c0841c81012043c400c90b8100e0324a511141c02541c0307040b1421401da0414101681070000e21a400105819026003052107400d80c1121782840402c2072040140c510f006125050181e80305000610580c00c035800342040300305044400981300d13a41c0c202c0d9680500482d400c540c100c003802005214100c2c21035050402c4182c4648107040d54034001c049030078141070261090380d9026070140304c810090b0401206a010311030b13001c1e040c0420000607216450b00c0c0d90b02a80070384000307503494204000c29540481c000030041c088500038032983d4035010002d080402004003032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 35195697 1250 35194447 35194451
    0x31206101706010c02041505041113031217131505070906030e12121e0f0112081b1609020301081b1207181406012a020d0606031403030c070303 63
    0x40b81050f030140d007107001c030203030b0003041403004403a12400c2e28a80415031003030070b0090f401c00003100162940c01013a203203500303904013140004c28690303191a11402c211100203018001d204400d16420400c00540310301c40c80b56400c4418814080f0310700b10112810448400c0b030b100349420203000c0c0140e4400d500b00f0403581e1526010920340062034800381000b00410942e40c5040c400541d5120134001c0504d5582b1800745480b200000748040004034038034681c1111f4114481c030860005026121494501c03401c0d1502460706281002104c00041042c8000702800c5021a40241c1041d9050821003c0c0e0f200607110114055055500d0404030aa407900c0c0d0460313102c0231452100c3c003540107031900c00480c030703540020804462206545034800b110b807820f1603e02e43c0709030b4100362540302c10a0148082e207014000c180c0d102c0e81c0018203544154100841400c180d45014240903020001d07a440100d04000d0501420700015032519500d0036002e000807000b050207454000703004000103011080160b8422035018100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 35196947 1250 35195697 35195701
    0x106020d020c04051f0807050a1a0d02070f02060c010b030c0a060e090601020109080301150201110708090d020406050a0303050d050601090303050f0307050405040509010903020c01020106050a05300312061017 91
    0x943c0310710145c561444e20b050035000001403082c40029000304884060b40d002c0030480d100c091101881d40e00c1c0c00040504602000500c86005072079000b410941d004a2200d64880d18540c001100d41d405104d0404541c0e44681c11407a07503140612803024061801c036036041d0300c54500701014003502d110310300d454894a02c400000304282d000303400070003174298807280c031542c2c0b0768691003942e502c40790518005c401503103016014111342c1013407411941140c0d00082e400381050710803000c100c005070305d801c4101c2e08640c64070030001d9983c0b83c2005450240d8402d0301c030f664456182280300300441d807005242c00d040080803842007002c80d400408545100b83da10791500d82c0c07541c4440c410346e840d101c0c076844250010702d05000c000110070b06600600c0c6861003503090700c1906060360012402c2c1c5200f40610742e44100407003002c2055182c032000c481d1201d103400542050081340701c2c030301041d0502d11104070342c66500006411800d081c0741c102c016603c145c04403100d040c0e0140642c1d0060400e04001c003510303d00106100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 35198197 1250 35196947 35196961
    0x50c10020318031306080a02130504020304050705040e010603060509030712080a09020d1a0a0c0509040207170706020c0d0306030803040605090f06090321040f021c0b040f0201080106020d020c0405 86
    0x145070411200000220f80d0b075906102071200851080b8450400000d04d90380c049581c0110b940204c98188252025503088242000300f0400258005401100c807407280a40010303580c0c0300c50140210034400d50b000024a41c2c82d505184007515001400c0b42d441d41c008006030000107482c1c0d0f220201c0c0018a181040c4c165480080407001040e20b860041d612070b032445083c402700070b03030580e60390002d03c1c1e509006606031712040b00301d40c15030b025680c20300c011810511050300e15081070307809001198019484505500403c080b0034050f64401041034030100d030001f814078141002008080e01c0c0c0017192804004c0649181c403109031a00029000074016a10781000c649003010800c424104411980300307442d52800c190640a66a43c00000c0800341c03d040c000c0740c4020110301413010b610aa820200718102806a5820000e0300401e00c02d0b40d50604042140b140040345e01c00714000e00c9584148510480d140090002400c02c8205a11000c215442005068a030360350100c1e1621407400c00361030118080e20303641 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 35199447 1250 35198197 35198221
    0x1050117100e0304060810080102030906041a1b030603070f0f050a080a030e041802180708090f070905040c0b0310050312071a070e04020d0f0b030309030604080d1503050109020a06050c100203 84
    0x41d003c000d2300d40c004811b0041105001c03074142d004500c00c18038030005031000d1040000c41c02040300c1c0102c0040100100c1e505c0c802d071008c000d40c2c1c07285006043d0b401843d107403004281001f03001e0700180100e0281040a1003542000805400503000c0c5000800e00c3c5651640c004189400714005240120b442d0030491007030710003110b40c0d6614254000c00d0190040800051030201c01d108880c0803000411401c00714041403c08100c1a0044002001810505041003074182c0a440060401c860111040030001210318900300554050b204000360608818a402d0070940380c0b2524414a110781d0b581003150b8400107004d000713610741d00900c00300142050b60722940c5c182c80d222034142c282c0d5000381c00000d203407a419540340d0001d8026054480300300490b03000b10702895a030b405038042c4140c1560114011402284844001d428200c4d40032202242d2488100c2d4141004206588125034aa468091000c00c41c0b51a2020314040c044a190182c00c0c00a03003140560745901842100f06035075400000301d210341c0080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 35200697 1250 35199447 35199449
    0x90512071a0f10090e0a0303110706050c030103050706090609031b09050a0207051207121209020607030306090c03050402010f05070f08030c03040b010e0603030711011101050117100e0304060810 85
    0x2403201e06581c9002800c04446a0046a003401203100c0400007185110103403180581988450004000c0f02590350b43c00e45c010020212028101001401014000380342401240c0c4541c03510210fa90303c0e5455403030501d10306005504008244002c51030140540c55001c407042084a4101c46550403a141d0b4100009001c0140d03040119500d0a0100700205480503800524582d03116100f12024031013040350105d03950181d800028002c065046541004901c00c948085403141043c0c000200c280081c0d0008041d5440114100c010a440e10002c20000340103103d02c415104042c02c06100c40d203050380c002806c0d002c4510240040c8400464a4802c0c000d00c0d03250a0100c50340720a0f01030b80c80c00c010034001007a800444048a1042c100d04c004103543d07440f4507081d40038404c0074009605000c40d940e0354011450f2003c2196041010f5082e40003c0141c0c24051315000300341200c62645c1648040340d1003410040c0001030400f805080032039501c0050000001c035404c54200b4079000400e52540c03480d0250f81195 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 35201947 1250 35200697 35200733
    0xc0d0905070906060909020910030504050f010c0c0303060e06011e050f0c01020403050f0d080c070212010f0b0906030d09140d08070c090b0405130b04050c120606090a09051207 77
    0x4072480418004100d80c49003040e00e86071345a1102450340e61b81a04240d1003039101940d0407009607964078200300d00030f410031b9030028406d8054441e400044210a421108d680e240c2e0000201c0011702501450307050705c0341d0b4000d4030550b030340100d003444e001c40003802014003505600c0b04d169031011403105461058041e10f1442070145d15082d603520001000c28040d401c1070000b540c99014407144084007445c00180a0000002500c1e80c6060b40e484803400b1303013140c1008200742c1c0c102305110b07070f0700810744401e01c150075034052840000140603589105000c5071002c01403002c0e0096100c1c5d58201e49072504019641c088070503e440c03184180021071b01058000c0c50100740182058130100d100000c2046108554050300c0d044901002507500c0c0c0700410058417425203e2000c01c429095024004c9811400680e600070b00503011981500e120502181030aa40440300304000d0300300e601032180a20708000c1e596009000d5540c2406500c3c8181c560b9030f291800c091442001c11000035100080011001c0f0b0071030f800034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 35203197 1250 35201947 35201953
    0x2040e01060b07020307060f0206130512070b09010501081f05060301060f030f03030b03070b0415090f08071a03060a2304050a050a05061906050702060904020307030e0607020d080c0d0905 82
    0x40e4070100ba020503041500f080f4424017500501040c46071180200000b041c1280e8000d2040c2d40b502290315a400c070403800c05545038001c00d40300424020982c030042c014144528090206403500444060840f0411703000b8410340e4000c17a0101400801807000550205403103280042d0356203c05000034014a1035078044810f401c08030a0020500c921000120001c50081d1030034001005d8010406448400900034449041d0080c070052101111085140c2882d03030182c10600c0250341c5030410814612002da0103500281d1002d0000d00c021a040303146010140b040c0a40e460860a00c000029a04000340c0070b4480300510900f407805180070f06001d500340340e00300944204114140032480e10003820040700c7ca00002800d2901140301030a04010141c3d45800d0300080005407428407004490b00c0e4096403003641c0c060700138400c80c03a031666544001c0d802140b098074002030289a8402d06410444000d00300d90664100900c416601c5800c13440c241d07407203504a0f400130b80d90f800d002c0714000100143c510181a40c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 35204447 1250 35203197 35203199
    0xd0f03020c01110706090b03040516080304230a0506090105040e0406060e06100206040b18030c0109060c05070506060d03030e15060102070f081b0102120a08040b100303170402040e0106 81
    0x5030041101c03105240280e031003083c1c0e055586007982e03855206100b1800040c05000042003120301c90000317982c0051150382a0b4440d056204811032880503a500003140d15000064200000f9501c100e10100708100c81c50070092800050000880c0302d0000d00ca914000d00c80020350240c01d80c81001140d01a2241d10300c0c0a095040c9828641c0c01418a800348050ba80f9003c80401c155213013402c900e10355040340c0c1d030003481c0c16551580d07404103031303080a0300090f0f0002c15105002c28010707043c0050f04982e4004000040c4074020340c00d059007a50180382000051140400055012503000b240d403540c88901512a480c1c8042645821802460b41400c0e020b028096141410300451682c20484d010745e200b6402c54210316110080c0d00d603081e11034401c03101698080780b4202102e102d41141c9104200d070500541c3c4800000000800302c1d039200d641e011001030460000c100401c00d01c8958290000100010380c0c00d0141145d4000d8000301e20345101d1142100342c40000307011565190041c601144008000380902 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 35205697 1250 35204447 35204453
    0x114010605070b060901150e04060f1d06060703170402030304050604090b0406080f0c0915060a0206010f0602150103020405250c0209090105060a17030c0d050910030c1d0d0f 76
    0x250040361040f903045203810301041c01e500d0010403641c141c07043d034072890300c3c0e5a80c40001034503055106004290069210b800001e032001c41c0511310002040fa910303c2410720580811081020100103000d14800e81c818880c402c0032a0313020014603a941c022a21703e00c4030f62039a000003440e5024aa001310f134021000035000c1a1482e0b241c00003502c8103000d176800d0103240e46401030503854030141c1d0110025030340304003280c060300d18115500b1500014101100c910072100c1e41d0109690b60302407040600036900180040013201080c10030359008280902c054000001e600907440c40320306c0c040c80040c0c8243c0e2110041124056001c10000c040120003485059000d400c48024146401084050348607003080000160191418002c46101e660005c02d52107981d4100b2401c42c51090100d040641c25120030f11540c2a030003400c000341000548941c0f05c840d00e540380481007058050405030a00c040505050350f11740c445400003035032901302c2e42101810f114405a407002c500000d0482c800604014031844480c014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 35206947 1250 35205697 35205707
    0xc21010f0b0102010506011d060901090b0a0302070210170c03090c100e0103110304021c081314090c07110f010302070209010b0a0305090a03020c09100323060a0b030601090e01140106 80
    0x240c0701081e00240100c2e42d03040015103034240c401428500140c11046000102d2608900801712203074141081d1031416114944920280c06c9404d0803408203500080640a46c80d02d14007040030b40e491450f103020155881000d450100c1005072002c164014003002040c840b190500c10300d906540050102c1c0070b00000c01100400b0010036240c614003181c0b402d4000602d10111400300c030312403600500003c00c0345d000ca02d100084030b00c8450040e01c1822003800000c0107104c86040c4403005080700c401429082108004002400b1070207880c56450301001c2000100080303c4c401c1e0003480c2c410807110030304220020300060f00a4451407000943c0040314100100d00c00711160007070302a100090b64100044d80c0c030001c03550ba4800881c0300240c05070f03101c1244c0780c40e54a484291070754046240003035015100c1d520381d2904070006400c08a246000103000c2034001081c010420070390700807001c040c140040103401c1c2c0400d885503010b0040d02030050b110622080f52000075004880661021401002c1a41c0e6480000b02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 35208197 1250 35206947 35206961
    0x80d05040c050418080306011b060b01120b09060904050304170601090e070602031e0706050906040201110c150c1e07230906040f0905030a0e1201050106020c21010f 72
    0x1c0c440c0c40c00240800e80d810b1511442d403500c00d154011514590850f1101c20f804d40006003903e0400c1806103102907609401c0c1d070054070b018442e82001c49c070740b200c0e0340c00508001c1c4c0e8040300d10000340c038180c0703c080c4a0707403001249500302c5c2d41581c182d4902d845900304142036101d00d4102841c00b60560481141d04080018004d04031842540308010149400e0701c255100d0017284229001684148051170841c6800b0040c200e42100b9503004600d0711415580790015601d040b02e5145603131300210200000e55801ca0410040c03100c865014105440c003d00c00601710500002082d03601e40703004118003050704401c0000381010b025000c01303004942030807000c060b038505032405045605814068070788108021985903044284004000002d240d90364000c0c00010064003288010180c1c55159a04c0440d90600040074425400e994091020840b502800407003041c4c8000c0d4166a132609004101c256808612a003810000b15038242c4001065600340300b0b040d070000364210042d40f0700411911484071650003c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 35209447 1250 35208197 35208203
    0xb1203040806060a0302090403050f04090f02040509100506031518010306050402100503040506180109020a06032f0a05070c0806070503010303030507020c030a14030d05100509090601030f0201050702010903080d0504 94
    0x10b40295240d0f4280018000144002504400e0150200380024014000340041355510203000d4102942c0c2c01800c8141d0359455007510010354001000d001c0e9041106130964011442803c070b00005d4038140100710140702c01820041a0b00408504256580c0d07080f514881c480c0d010350100c503455071070b0308040d4028a01a82d00300c2c403031501f0707070310307a04910740034605680c819500a00540419954659694010b114600c0341802556032a40d140b801640c41d0098000034200c5070f680000d15400c0b09c0c020026065028400880c0400582c1000c080c07601154119600070702d861800980780c040724074250850015503003151002d0b00072a020000030550003c06907049a020b40c2e018842502c1e06c0d4001c0c0d0311a00550040c5406800001494004c203004880d201200505101100d00d04040e10100e10202c0b4001e5400511015248408004914010f5282c50704501c00102610392945140e880c4d4a2540403820028103000b0007155000540e8013491022000b0f40d0001e1400d0f03918601c0340d07000001000e0440e000c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 35210697 1250 35209447 35209453
    0xd0605010e160801262e021303060906021b0a0201031103060f010c08130f0f060207080d0e03030d02030a020306010f030c020c0d1103070b0c0d02010b0618040b12030408 74
    0x3010b5484010014019400e59180e40e6a10b03420100039184c0c010076100c0c40c80c0300301c0e040c404c03a80e1030031020011904002e803071460014140100c44241c0b030b01c2850740201110400d005000400d4001d400d0790240c01143d40c4044005490001f520300000a80955041020502c950b1410503810400c00716450101c00d02c00d9804121320303180b08030440c0250000760344550b000501d18010700804e5000d158008011401880841e05112000c0424030240000d030300a10011a4140010401d5200c0e81d07181c0800340070302c0d002500d003460400c06415500c4d12604065410042210000b4820381c40900450b4102c0040d0300081d552490b01c1110840079500c1030301c00c5230005158010040c1d050344244078590100c806603001d410001040c804010311510b00490540e0425030001c03008540380c0d02080180004d000308040d058603102c20f000c0190821246030780d04819a414003001e100c1301c4d03440204461464000005400c00703110740002043c02407000c8a10726410145950491282e854000080e1040794404021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 35211947 1250 35210697 35210701
    0x100c060b0a0f1205010906060f03050f0d02030a0f050d06030b0103150e0304140a091803020d03060503031e070b0c03010f0807230d050a03030510050603150103050a0204050d0605010e 80
    0x911100911078414120800742e140e4060003012030100c01c4202c424001c01c008a00031a06072a140d08035405503208104000b08030200b0001c0000074040794403018a590058034048070310391703070207034a80c0700d03c078510000c01100402c210b034503074080c2040d10040c0f095618200521922480c02e501103850038002601c0301c860201c50304200160a0184502403580900510f040900d0310f10503c04800007007002c141d2021050b5808954042a8421401c0040440700c207515100c901e07040c06401c04401180980401d420450284041e4800104a0300b200c81d450203004c1c03a810000402000720302840748010a48840342d403d0001005141014605990000003c52002c90b03944d0b020994400d0300c0e1080c1190180c05224180003641d6003804a0003105005e0400790380c6102650f141400c080c40c5050803004640d4590900200381c0201080501030201a00c90728a1414809400f4548500380809941050389400020340c0180158040d100144000380000610212610b02070015100234007030b02c50b00750000d0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 35213197 1250 35211947 35211949
    0x507020d0e0d032102070602070c15080108071208040b0a0e01030e0106050d0803040606030b0901090309060f081602031c0207120201060b1206011e080901050709150305060f100c060b 80
    0x1d8002d0b0386681a01d0b180d548021070b0412011084e02401030080c4e4a50038080c50000c0740c264002008460301c1100315098560401c00b01402c3c2043c070075080010402d801006010303601d40002c196045d80c1800304010901c101c14980030340144541d400c0f4031150400440d9884101d034200314518800042602d003442000e0503004c20300e0032101d492050f10340c010055079070600810703080c100868005024182c0440c2480d203e8441c8042e030102a60000c0603690340320400c00c10b169001000501608107450310055100301450300038030075680034051074076207844142002452402042141c0703050101c1440c031a45031800003100c0009401004040d1070017400244800146407040c4201810380b040c09140d5400e14164041560642d81c000340707000d044c400500e40100c159029070091858105190352020460324041d43c4060032748ae800b42c100c20910030354810500c0349003590a4040d4030b11606150004240c1e4581002500e1040d0962035640c01101d4506901c0c82e441c4d22901d103284160089409028901d5200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 35214447 1250 35213197 35213209
    0x92004020a050904090203010605060f0307080c0a08060616060c020f0106080313120f06060b04080d021209010f0306050d05150f010b070303020f070b0a0b0f0904080304030e0604090507020d0e 84
    0x103001200050b2040104203418a06580803400ea02c1c000703400011550b45507000701e026644100c01e002d03526000802001481c039840390754603134801c4204000078100081100d000c0c1174081c0140c8a00d10443c000b00e66845200d01501c5400131903600810284a103140c0c1c0c10000c1e44981e05c0e000c00003059400d1030340c0400c445000000b1141080070800122001d40d1070302c82c044049101100c002c031150b00c802910000800e01c9030181a01400021040554640c501218540b4109449086009541101850700b80c603494040659504120070300340452504580c2004034000c110540105620058903840c203424010001200d0b10f40b00c04071350b0300520540300c414401f0b080703c400b4420074210400800c444e0000074070a402510232802c15001103410400c0716518002c10887c05c90300d6000640d47c1d06200c41c0c542c60102e8404440010540e481d407614100b0b0307250b030740c0c003844014009030034040c0051f8025440d0f1194403c64004205a9000304030900384070a00a44a1152219400c0017600754518011186040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 35215697 1250 35214447 35214457
    0x5010b0a0e0307121e0b070f1106070806040506030a170c01060e0f010504090c0824070c0305030a050408040b0a05120105100c06051008070b210408070f05030d09200402 74
    0x584284ca0040c9031554a8900710340c0842d11000130348103440002d20025450a034094081e5080d510741007510305940b00c0c010240700240103400700b9640030406024401e0f030400c41c00c039002107040d18049015650f0001080c54400218401011070100d180f2407180302881d000901f0b00f800c05100240035869407207900703072880e03401982c00d4010180300d1001041640b40913403000044610402098401030703540c054041c1440e5030100500c00c00d85419101300790100c900e0592a0340100e682c10110202e0901c2d40f0002c0c0740703020003001c1c1414207681d50b0101e4240300082060307800500394003401559a03542000000c2c05031704014801e0b420b00ca84440046030724030300003002c12240000c0d0399505000c02c001e074848001400c0081c003c0703100c142400201140b040e1f424440e08003d00340218003140e845000700c00d0001c11510480b00d0502c480c0c5204c05020001d0140c6040b104801c0d00b190f81c040c000c54a904256007548915404404041d2500c00d1341010013180035845041312403070245101c0c40d01080014031041c2d02c95 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 35216947 1250 35215697 35215709
    0xf020316030e0a0218040308070206090304060c0606050312040306140f070e010315080a030909020f0403030c05030f0d0501080d0c080a030c090503010c03140a09110411090405010b0a0e0307 83
    0x41400140d00461003580002400b4004400321010b010054001c0b92441d02e5440552818600c14000c0000b40364100d00c4090b084041480107016901e00350700300c1600ca0050340121002c00c41c04400020070301c440d41c0c20a0000d401c000b02a9500b452002d00000050341c03081c48200d5181d801d04440209140882024038400ea1040040f40c1043e55081e004851841c5041ca01c58141a507859000021248400f0080c1c0600f6069008118116041c18040e01400865101d940315500401a10724807040e800705840c1101e606040c0103c0c003410614105055000d95000840c1c5090003142140f242c00712904070f1412074048805682580c80030400444181c902c21a016000e114100b10220031a03101c1c0d44500708e00003840c0740408105864800107400c0d52a000c00c048002502c81c02000303003000b02103100d6900205480d40030015103c4641c0ca415680341007003011841940e40d8000301081142c801c08560015600400800c425a12018891140e8202180c29400688403103080401801e00142c2078041d1a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 35218197 1250 35216947 35216971
    0x3021005040c05060f07050601090e10110d02030c0f0c0304050406080d090b0a02070801050c030402120303070c080a03060b16050c0d020306010909060e070f1a0f0306040504060b150d0f0203 83
    0x400d0800703004c0c05511003240040060010084140401c80c02d20025004e010008004603603900f03c015070380d1600010340c4104d001c8610340440880383d600d409003241d6003044260fa0260b2240d40d42103050302c0034064a40c501c042e486000901000071310300030009100342c8a041b20100034098440c40d5540c1d035200041c0c0c00d13001182040c00705200b1840304a018200111007441280c1c6070580b901240c0e800c0d9401540c1d180c0d840b10010007800110700d0f020342a0940e190441004500311324000000034401c124109000c3c0c618180040c2a85c1710074400e8104601800d00c8601007596030445002d0390313080413115581640c1c1070299107002100f0f8542200d00401d1142c0080050491b80d0030070207108014606040112201c5944c5d651101c543d0030140404001040021801c280d96171602d2650354000c144421404a003280c00c2003005051a184002d1381d802171420b540000e103a80c0c0d1840c2c660001e02d410a00c4651010403100b04039152525103000340454840c001081c05510040007070b5809a010940b00700f0b0f5410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 35219447 1250 35218197 35218199
    0xa0203251a061801150c110301020a03050603010b09040218040203161502060c03070e09090304030204060b040602010b030303040b2e090209040b040212070c080d05010b070209100609052202031303021005040c 91
    0x18400c1d90010480c90142962040301f01100340001e00320380c010303240c2c3c1000c00d40342d40070050589005c0c8110440c04500707480c1d00005e441d0980c0020325800051203100000442d050110701591410003080700000106614000510340701c4050f8030421101075028401031040303100180382100244140c074012a015211900d10405c2ca0381041012000201030301d1461000b8400040543d640d401003c00411202640315075403070500303070000c0c203580c400168079003e075004106104c000780c20850303510b0b8040110051488020b42003941031000a40180c1c110b14640000c040c0428482c80341d500502c0e100d031303040f41d0070000021100c1c2408240d0258003482c8560b00e400d500001c0800d40603103030b507030b61091185040134038110b200110842200d034283c01a5410400c0810321508504260741e0301900846000c2c2120310032450300c03070010440480b5000c2d46000c0c000e440c03c6a8000c4000c6080f0070425820320500755120301d80410720810b5111441001d43c011702c6658150542e0544034031070346e4003664002500ca4042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 35220697 1250 35219447 35219489
    0x19080309040906020c0102041412070e0627180d09080303010303110a050a03020102090405010909050a0303021804090f0b06010810060e010e0303030403020607140a0203251a061801 79
    0x510b5141d000f43d4002e40c00304070024910b1001c3c070081002c0c04c10303c028030900c03407105002d100c0d01004c600720565043c0c4c007451742170224078503010110f940040c04560440090745050714003010300a0000300f100515504509100c1301c00d80064401d41c50390258803c5813209405000e044400d40a14420140c40b41c004000500209200c0c0e4822920000c00c0c07000ca90060340703990345483c07900544403429001030b54041002259880e0500a02e8010f01c4000c406100051560f12500d484030183c80005003410707800151030400c00e200600780140204000d10802141030203043c55149003850102c2201c0c40318011000400c070758022070b0402d0044040b4140041c0c0982424416120181c031003400605100202c0c054505950702000150b109910079400f8112508051001403c5000c0d40b13201043c401c3c0041c8101848a613002040d02c4412035902c41d80104224403c0c241082d0b00d035000d40c0075240e019902c020300076029665691501031242540c035504842007140300c0c90b103550028015108408240c0801c8240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 35221947 1250 35220697 35220701
    0x12030b090c0a090807090225030e010e191403061b03130305070204020705010e100209011403041a18060709060905090619090903090f060206180a0203060103111908030904 75
    0x1003040e10b4181203090540b500c03004ca10788412540301000f007540024038400d005900c815044181c5500fa4081794404104d590050807a284841b6094100101c60f045603100c2d9403284c2514110400001e1345142e0395444001d4441c80c0403001d42200e0183c450440402d08041100d224421900705c59482a41076032a40c011848449040031425010003005204020144e6644e00c0200503e13446803000040d4101d02e015403d00b81554800310800503441441501d1036039803c03100083c640c14124000c10b50f241e40318901003401142154400c21143d5518013002070040c00d46101c2084401d03500300300c9405546040045a01d10040d00a903400a22150410865030038803100d851b4001d0402440250080e06040b10585003050303e6002003201602d500c013500600d5000000000a0090b4000c410082400c209001c0c1d80d901015100c44101261340e01c007055150428400001459030003804ea503c103507500d0070001010160691850703c92004c518010100e00d1034540103d04032006100510305000e050410000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 35223197 1250 35221947 35221957
    0xa03021201021e030105040c080417090102010e1203092a060a0e0301090308010f05030312011e080102040b03100509090601031101050903060412140a050315130906060312030b090c 79
    0x1100707640910204540d1002c0e0b07041031074021580c204883c1c5a624280410042d6013070219070805101c14002400081140002c1e0705001498a00d0210340d10006000100d00508902004803060700803800d200c0041c81580f03000394060142e600440704c0e90b03004a5101410f0119030f07449400d90b0504540782100f203060150140c0950141b03030428045165881d0301280c2521002d43c0200d00141512005211521701c00d220b43d006001c05500440c1001509103140ca00b044c41801a40305e04959000b91079010803800328213070054280320000307645031980c407541c080150700159420000b02c414003c02088a00b001030929104120f0040181450392850322610101e45c95403040c9030411004024105154038200a07240c082c2d44a1b000c084140359007214010051000d000295034540810025031401a6100082d07075080710304940c16004500304c460000d0302d00c10f40c0803005c01a19091115180910006510500440c4d00800030355a6150341804201e0440b2107850789268030200c11004101402ea0f840e0142c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 35224447 1250 35223197 35223229
    0xd06081c1202090402070b0a1d030909090c0312091e01050d0b0406090204080f0105060105040e0103030807020a060e010905010e030301050d080c0106050d05100b0108070c06021305061c050f060a0302 87
    0x6243c400c1c0b00001c00c0a907403101d401903c020242c1800c1c00418641c43c8140e804a09103000741b00714810044c50300369100d11074690704500c40c88503c0089010442d080c894a4103054000b03003214030741d07284040707068565002806090b00c03422001304001403099601040d0200b55105035a03081c68454448010001040481011600300c1d6507003d003c12180810310041024009003802005184c522034201402d4850040200d41004410301081000180c0108082d0569230306041c90415980c2c0c801080748be007005030b84042c162a0804480402c0c4a4040d8098030056002d0b01c02404103191012080d40d4a100c20710a55030041040c400708004183c112020b0041030703800c400041255980c0d10b0018020517082e1909607000c0d0815113039001c1940031407040031002c640a0825034428a803821020702041e92100c4040c103015000076030141303800705100e180d10140c28010500d50300c0364482e0381c485d80012421005103c5242c07900b4040b61600810f030210301e10403a00100144807a50869003400507140c110782d600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 35225697 1250 35224447 35224451
    0x201140c0a060c030b0301051509061302120709031202010509060601030f020c0105010f0513090b040f0828120e030a0c0c03050a1a060402030613200f0d06081c12 71
    0x8400034180f805103030301c1d60001d0742c0d0101302c00448904050071680c000d000c40c00c890035400600e400a45460703419035440b000c11590100b90f0720540060b00c0c0a8030600241d0143c0b0b1a4040070045017507008041d80007a41d000d50700720a01000136002c00c1e42215000e9170310000316806500083c8496200b6001114608091007016091085031150301e401c1d9802a04120260b00c9098800e02c80c0d420102241c44101c59091400c3c040342010f5110061ba40300e000d400909600c807008401020710902e04201c44100ca100c1c88241c0400103000c203200031010101401600091808400c5415505640a1b90741954881c00103586019001c12050b5003c03400800300b140c40e4181c0d581d002020030014044c1e02e010034044c50646411054001000000060040210348a139206005000340c0e92038440d07544c601020355510004074021843c80003d100c0503000d41c0c1180d044000070f400c0c000e000c281c0d4003600fa0381155400a00030301d912840105d4650b410011003032580316100340f1031040d251040e402c22010800744000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 35226947 1250 35225697 35225713
    0x711030303061f140d050105010206070216050607020f0d0c03110604030512070201090b0a030218100206060f030c03010e0a02090f040308040b0406060f0308070302070b03010b040e0c0408061306050907030201140c 93
    0x184121541084440085d800d685000400c59540c060110a900003428409010162000195004a21121f0041d580140000b0544c0c1d821510b90340703e01041d0240003801f20032940c5440c0780084c440141c40c0800c4038101308120750700e10781c3d041000582e800d40c3d600401401c45c0450001004900c0c0d0002c2c5400c1c2c0c100003070b500380003884c1e032082c43c018806840769a501681c0c2d00c1440240203030b21036510100354003d44404000190076a80401ca080d04004121113104c0f580704045e001030318100c0315051045e0b140d40f80c5008501814000100100312501c00e0b90762940c076682d4150800c0810000321806400300e04200c0009d4002001c0c01000c5522a1050700f0000c0c1880d20b03810450450801c6420403541a600082c102c41855010000e8a0040c5000148503141d903040001c811550b0050744648c10440c240d28001c00e4000d0084000d07680034020302c0f01243c5003494205c800c0d0221440c41c05041d2586483c080120305103140100d10740069076010307102c0050719070307001100f40110b602029110200d0b00400b03038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 35228197 1250 35226947 35226977
    0x1407080f0904060e040c06020d0f180305010c0906120c0503040f050304080a0803012909060f0f0d05010f080304140d020f12060108010b0603060d0803090a06110711030303061f 77
    0x41003001510344443c60584e1443d103890000e00c25600c5810140a40d804008070a48942d404000a1020462450215100e4001c0c1005250a0783d82e03400c001c045508211200c039120b9840180c070800c4030201c1e65407462910701410300204548039075000400050040000501060540301103592840c4a40100d0b4505660b0f2400c0c80c2c10f26078040307422207031020000010042854030381c0d0b184105810f454841109110049545c800b2031080c510340a004510214148041b514464103482100c010140507030703503641c01c50769540010007090203126100b03904910040384602c4004143c40680c0c1506520039000341c909001c2102d500b401903422648852602c64411447e21541c6001040d921441c00505075541040b070b9060039150391a01c054050a02481005090fa0300c06501c0607180b90000c0480d596074030307503660890800b0144080a050a1304026800031442510030003429140d0041350840784840080080540307038032065074031562000d6600840c0001c41160140d14003507c0c5103003880314400310100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 35229447 1250 35228197 35228201
    0x408040807030b240306010509090a08030108010b01030c05040e010513020d020a031409010b0f06070311060103030507020f061606051005040c020606041506080f090c060706050907061407080f0904 86
    0x40c008940144054040c030401e401e04c101115150a41e81c0080303010444c101000c6a40d921051250034450503464001c10300441c0d0078001c43c90419042401c90ba52980c54890b182c1c040c1c242d590311a40000e240010940000b0300c90815a02515200ba440740c296910741400c0000079880c000040d44c40c1603003007000e003009134011f10083c11902070270348000c01c10016071070103402031074001048410b40d13904000d16110f95544070704004004600c1200c142d9112ba08901301150044517420b541100f40c8601e20000c030074560080042c24805100320364a00b6051210313030070f2094600501036400d401c9500d05000d100051503d4000d10750003c40600036000807a40c400000381900e00408205000d41c02c102d043c40350071300302409034031458410b0070f10b007140d070718548800108928802003000c24496059000300b4140300081c01f4032851250010905070319040356041c140014032050350041d0031403182d03a03400500640607003000c3d07062620700c00046060004a4840001c10303444a10703800c02d83d801c2013044142558880c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 35230697 1250 35229447 35229449
    0x403151e1803090f05010f050708040509100e09010c08010504090201021606050409050604020a020a02060d20031e070207050402070302030d050405030405151c0908160b0a2306090408040807 83
    0x1d80e003651120301c6581000307042c0c240107030000c40c05410030f540d0500550760402c1d103031a2202c8041c40c0540c1c6d1801203081c240110b0095030401c42d449421501801540200484100d00340c8109200c40e49403510f4604125080340c0545a5000100f4100c6004000d07506c1c090303100110190040c0180c03407168a005040c81d80c14601900301e01c002c070f075020600b401004140d00c00c05030710813001e03942185007140c0c001000c0e58441400c00000d01c69a00058004448803060b000702400c501c0c11003074080c0e512105460841d0351703007044498410031b40d54000701070410300419103c1c601600558001c0c014550420090202a40c041a015810b6100402039552407202d40c0c400d0a10550054019544450400c4100982c10b240042200100c51092000803155800c10348250000850f1201c001040d030001e00e04100540140c2c9100d054011510442100b030040c50004284540b000350300401010031641951b1100d800807141d54582c168102000a482e41440480c1d0f0341c02a000790300140c1000d81c1c0c0c4208c0c500d44202c0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 35231947 1250 35230697 35230721
    0x709150503040c03030509040e1c120b0303030103080708040b03010303031a01170a15081903020d021b040506010306090e01050604050105010c031d0301110406170a0605030c2b050c030708030403151e 87
    0x140d2b0390301050300c80e0b100c0040744d0040c0c0342444c14451900042c0020740d0703030302041c080a410740000141d05001c10141e2070844000b0b02c03e840c1040d07141e682d00c0c10f02070300801000340540c10507510120705400d15842500c0b4100e030a06440781e81501c03500c030005000d00800280c084080e400c40040d10129000104000c603060780a401921881400510b241c02030400c12030507803030720666000320b0b0300c1140c0c07000c00c02503800035440c182d0340016182d07501001200500b41d00da0103190740903d020b00720000c048040d0881803042405640c2480039913070320801120307140208903004d4005500600d9021a00c031903955000c030070070740050022920b0012400c420400340e000f030f0b000e00701003810442e480075503056541000d50b1040511404100181c43c080121340c0314242d40c08035900c95091100041d640d80081e01440101d0b03140400c10500b2801c1c14035146594280000d01a8484c2c410800001881e8000104070340940e071380801c0c8030b0402e0401500e00780180c40c0281c541d01c40110f0703401140000070a01d00c10b041c02500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 35233197 1250 35231947 35231983
    0x1509150503071a0a03090f0b2401020f0309010302030a06050901060504090e0102070f03050903010f06150806040903022a19180908030c0906070b0709150503040c03030509040e 77
    0x100c0c0508240c9854019840080e00201031141d05814049100035036500c0c029a003404241c40d880c515050484410b1004010b003600e03044404d102d178418584042207051017540703101a81d2703030500303c00590b9190307400c078140800b0358410058800307954130940240d500020803000101b84a9200d60010f1511700c02600120000f400c003042c10403404005010302c01029030707420000c500e405180d403601141c030410164041d0500c100020000c0680c1c9003540305407051070040204100309a02d6080d481e940c200e02c00d40a0300050403200200e4207038a494481c8031105a4544c0040c15080c1107820460251001d10b040c0b860303500030180030188240c8a2050b015150640e40e4007064145007090300b4039480711080404d0000251800030b1500001c0c0c21401200d070401038a0354000c0c1c48121030350005149100355940140805801002c1c08542504500c00209407600050142d202d41c4510b48111524002200e000d41200d003100001c10100b40190028440400702810115000400e03040c0146000b480c1e01520162079 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 35234447 1250 35233197 35233199
    0xe0f03070503030f0f0f01060f050d0c02010b040e1212070c0f0516060e100e0301020c03070b010f23060a110609060402010908030418020d150303020109030801050a0b0d150915 77
    0x402825503240e40010442e0b404545d03414040215110150140181300a0016a1601c0c54200d03000e14180c9a0300011424213001c0101d064000070301030200c10381d0644c01a030600e44480d04040700030440c0190004d5907003400741001c820264201d96544094846011300030091180c8010804440408405078060b000804a400c0e2040400c230010300c4590000c0d080007666042c003500e5681d400c1a451111856181105030f01000000080c020300c01c50444402a101c0000c180d410014a508600c0c12560100f0080103282c1e520080d0105502410880f9926a0f20f041c0c000f0a4500c1c020740600314030003891420025a848141c1c1651602d1800c1c4d81c00d600c5648943d04100866030b00c0398414003d070010b00e0146081510782001307a44486032100d0108040e91b004983c01646881070b5111801901a000c1103c0c80a40da07824044e000304194141a000152084000704040c01c041043c00d0455140820301880c080d0404d60381d0340140107004105420651000001414040d140507140f400000f00b0b038018520707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 35235697 1250 35234447 35234461
    0x7060809150603031602010207050325090b0a0e220f050c0114040501030518070b030a0b010203120a0906090602040b180d02010206041407150807020c0d02030607030e0f0307050303 79
    0x12110040c61040c44400080402a40352000b00a0b104500e40a0226207055074031840149e08204007500401d80512802100061140340d0015007141c5855486548003066251000c0d04203035180065115008000510100001000c041d1640e9115400d0103120541072a0301c003006010550301d080035034003503c2c4100c03c54140300050100f1071080909082000c81d210300c2081c441541d00861048605160340c60300055010000403030381d1092050000b042d61409500c2c1d04581007140c200341c484004051501c41002d100d94000421075041c0c42071085110010382e9500340c5280034104890044038803c1c1c55407a59400200c0e00d0010b88050040040b0464880caa001140314840c80440c510a2084440d072540e4030160340c02150058002c1d070055803c070f01c00c09104151501e0300c087d66009200c40581003010034400e0358007880c0c00340600030036401d440c001802c00080100c40700b440c640180d4140c1041010a074014020f5114a910002c4030040d80e00f25402200403d06541200b8026110354100008210740 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 35236947 1250 35235697 35235703
    0x303050604150506070302030405130212070207080604140f12040501030c08040209070507051204150909090512030601020a05030c0303102705130b040f022409040b011107060809 78
    0x1100c4416201040700004100c000b40e840031031440307068040e05000402505240c428411900600000741c00c0c10000364182c60b2040c020f5010f2000303030500545400102e03c16500c04103441080345c2403d030060445441e03135121165200030a2401c00414400e01101e08c904503414007051500102c4000e015417141c0c505000503050f2058440003000b000f0f0076008100041c0e07240c2000c140c06c034550f0300c2c2c50b584680c0c46103040c6140c4000850059480c0f8804a8006a1003903000d10f98040d500041d41d4a0701001d9540b61081d040d2040f02034000e201e50003440700c0c036141d503805102a5500c5507051044888200f0f0342c2d00c5440c00c0d03900141151100340c000000300700c840a40032144400070402c524404035464076919400d481464880e1403400c0140c0c680d00808c06000301505c0c0001c0e0340740c000712070740040d0800d840d10b100e5804004000300c3c000c540c40c3c0c40360418a051a8101410000d91043c0360385010f180600b00f100919007480e0141c18070440c60b590640b551020007c01016084a454604985c1012408249 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 35238197 1250 35236947 35236951
    0x50f0a090807060c03060b03090f0114040203031207020712060e1e0d05030c071509060b0609010f0e060d0c11070e060a030209042102100e06040507180213090603030305 74
    0x5410300301410300000510708800c881c2070b25081140080c013640c02004c110082e04860b03110f03c40940b008070a202c0b419502060b0014005200e100800028401031410400700c64211400796054000340441c1142c01086e000e41a0700c0203151064038109501e41103613000c90248004150798655032100d80741e5000d1410031a120300c1c0d40c541e03c01c1e403034000d504417026961103060102c29010800c000c40400c0c580c5e403030340d400d84180e598890707070300c071040191004001c005000d9007109850f0541000c0002c49941400001c40e421030760180e60b00c1c0e036840f5055400f030740c181c0c0051110340c2e001107040202422400141c4241c440008150355104030b00301194004070725011550704482c1c01050100140040d5aa80310041003c8aa060301c0400c0e859540e07041020b00070580c8001c81e8800018100300b5255160b000c500700342240c28200d4100b00f02002c0711061655a10b00300c40082195026010600c620100c0c41c06e468200081240b0241c0b610004102103001c0342c20315484003400a0310f60805004241c0c05014041d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 35239447 1250 35238197 35238211
    0x61b01060e0108030406120605030d12151505091f0f020d090b1206041d0c120105010819080c011107060e010b1302090310090f0204050907030503030402060a170901050f 74
    0x5581c95061040300c58a80c4510711aa20a008504020750402401504004020440141651044484000d014117099030420500d01e4140c50198103a10064024003030300300340c0d00e991600070103404000e1070a4400b680301c91425540042c283d1100d006945103001c0d04503001010b9603600d400d0071038081e070191801d049540710806005a80c0360910006607010290396841010050700d465545030040850003d18282803020f86000540c030f0b4413044420002154590030741c3c1551024400d004220085080303030400e0051141c541c00c000d64404080b806051202c803103a006140041c901801e02c20034a0840303580c14581d00cc0c03000701083d400c061120303078890b80003100c40804c0284103010004000444501000807007044d10766010480c0c00705928204400801082121010803200c15141080f01800c2010a005c030710950400000030801a8003042a00403254024001c5095848a908001c46600401019010841c2d603036401d00461800124407401210001e00004040c10a440311000d0440010050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 35240697 1250 35239447 35239469
    0x7080702090f0f06010e0d060c03060602160302010815010315030c03020102010f1407080907090c02010203060f040b0604170307020a030303092d02040f0f050103080408060106210e010b061b0106 85
    0x84101084410f440744d001409181a4503003510b1180012108158008040d04083c90102c2d405096501a4440d0007901d0700c5808451050450400b091541143d6000090005504501051180146242003400004d0504010400c00042c51080c05995960384c01a0f610507184801003066517020310a40d041021159814880741c2b00c88820340404030009800403003002045400110f02c20340c1401800060301c0c8800e014080c1600c4884001d000c2d4100b540c000d80706012100010742c40b498644034200c0c000d203003e400392341007d140030840c00d0011503500f103840480c08200070000060f52503006c518040c1d4483d84001a9144503401d05403045040404a241941c0c40c124107945901141011881050390485000c01e51400254040000d01402c807060b25200b41494008010010701c0b001074425610200c08031443d503030b60784404603556046c5040030200940c2001d92401d903807005801502c50441340c0400420100c20050101c1c80c0c59102ca02c002200c006106070070b152403442802075400515181d485 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 35241947 1250 35240697 35240701
    0x1c050c0403030c0201030906021303050601080f0606100912030c110906060d0207060b030f0a0201180608070e03010b1306050312030c0307030c020f030304080a090602060403090501081b07080702090f 87
    0x8951024803450202800380718020450404580c0300303030404001c070750303210405640b80d002550641181c1070040c0400c9034103001300d0001282802d4005890248081e100c1c0003444203031190000d110640920980c85cac010800d1414001c990b00803029031040e60540300f50381d05035070503c02d07050000c441001c2111441c480c0c12050180201503840c9015100034200030880186e480301c007480d15034010184410180d0b011b005007240b00320411004100c03408964003e8071201d0b0400c1401a13016950b0525001e40d0000c60758180108002a106489040c0d80c0300025000042110000c0005090100071b08014030110b51107500a002900341401034100c10740c0c00d811540d0030350400326010030950000410280c00c03d540c03030b0001c0f50190710800c0100d5950103803000340c90340c0b82001e00300101281d000512030070101b102005c000a00501c005030051146805a80d011001030506004690f5841d01030603070022548244a0302e00415040d10003010072500c1241c0040d555105c0f13105000d42c1000c010440440d100c04441 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 35243197 1250 35241947 35241961
    0x60f0d0c15050d09050303060f060705070b0703030f1a04060605070302060f132301140601080a05070e130f060b12130303060909080a020f120a030b12010905031c05 72
    0x1081d034040350030440010620010440c1c07940101d4907881d001500f441e000b0402c0c8580400114021281920650000106403003841070030b110700d260081c00d5902017101003084000c042e000d0258540b00b8038010458231441405003055a802d410000b1008017505030704582487c0a100b00001404242481c40c00c109107030710060b46802c40140401003100d2100001610150000c3d601c003a081c2d405440c04185640c80700c4100c010601045000c40a0762170700b40c40725041e100341a03504d0310a150503590f181d85580c95000b410054280a00f9150a001205510030340f623680b000508241d070b02c01c0d440e0000744024108803040a44629034400d48031102d00700140d64940e10001d207125030003070301c86060394864401d46c42d0071130040805600c01031155180214103401c011801c4004c1442440b2507003101c050300c541c10070885d100c418031040c000300c85404102d03540b03c59000b5081002c5d804402400d0000e800c601d520418251a51904100c910707400001d2803000f400c9040d1984413a02581c500100240e01d0494 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 35244447 1250 35243197 35243213
    0x9010602010c0e0405040618050a0308060303040311010507020112060b0d0f050606041502030c0307030314161b0c0314010207031107030203070e09031b0606040606020f0703140a0f0803060f0d 84
    0x1ca0304901a035100c0000900740b02c0140c0111410f00e010380c80230011000c1030704006813624060708003100000c0002c8007040035490000181d905490700301c0700c4240649000001501e0311392001c2c40480c1480b0311380410f035505c03018500c20000100319014002c1d90350700e0210510300841f5060640300307680503e030a00380000c541f0b40a00b2383e010350b080001d8003c1690f211500030307031860040700710400c03032840700103202810558103400040c4264141520f4400355225004035640c12036500d05840300181d520100d03452a158100a000b00c200c0c050904403100a0f280d4903040c0c02c15a01044601c456034001641000b0903a200c44a410000e2440c006810b82c00d0840d03001945450203482141054030017000820728007042401100c4c403803915603440907202c141c082c07001c40d2a001c1c220f40680c030503031805000003001800400c0e100f60b09460b02002d46220741c10756952603001d02d00030088501038401c9000e04000a40039112107503260f130140d604241c84c0d1901004010184480388003890040c0001300f00301001520030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 35245697 1250 35244447 35244467
    0x30e070f05041826040801050916060e0915040603020a08030a0e0306070206071d0303071a091b0d08090306070504090516021c050c030406080108010501170d0f0509040203070e09010602010c 83
    0x8004c194584028a03000c49050007150003c180551908041c03100e8001c0005035450310161a503890041595561820390700c140c503034185150412000f0001803d801201040d6601074000140000f03520364072a000f1030400e44854200c4d1404c0ea00029401c406290042ea8060305684101c00802e07007071800c14002074903040044c0802003031101c9541d03a401c5454a0160041c2862005000c6070b881c0c05a500381150400e5980d002d00250520410201e10411004129440306a20000d034048080d1504030a0221401203100150b800b0001848203880f42d42d82404142c0c00758519598030783e21542041d65001c22940c014001411545e14100f2000300d054001c940c0e41c0c440030003455820910f00341c5078816500d5100383c844020045c0400503020454580007164241601c00b8103000300103903038841400e03100301044901c00c0402d03036008140300031744584105080b0310800b4003072809a0411204c41d020405036007003581c0d0000480c941c10150241070600c0031680380140350b41e10081c0000324000c00003074651400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 35246947 1250 35245697 35245733
    0xf0a05030a080c1c051201170a03050f0702090f190204030b0c0306010c210207080309010c0f0302160306090201020d08040201050412110907020105180115050d03030e070f050418 78
    0x81440c83c0b00481c284809083c21464110403070051900c0b10b00180315901a0420100c8803401d0740002c01d11070861601c5d00228005000140013218140e1030580d0381c0d41000c207040d401440d0400811006803500d440301809400324000310300e818100355580b580c000c44071005002000c0c0c330600c403c00100d200300840b19009500c1000e83c6540e51640801224903025091002d414424084103000c010140d03600c812400d00720941c00d9038085612626001c0d00ca210b4059258000342c00c40c41300c900410340c50101e22034000d00c207004903104825041d6812002c00c00d9a442640d20072f40d68a041815960140b160380714182c0d1610b00309005191513070020303206020310b001d240044080d21103180c00704010314410003861400107194202c1072400d403400074080c0104031a40c0c0a20175619603c0c084005050140b60401484a04854816400d00c002e1000040100c0c80c00e80401d03488030011025007034180862000342441c00b41c424200c0381407030280016652208400a251120140d6540220b40130703c4184110201c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 35248197 1250 35246947 35246963
    0xf0e06030c0903070e061002010905070504050c0c01050406090605071704080a050715060303031401030f030e0d0219060201230112020d02030d0305010e280b061303030c020f0a05030a 80
    0x7526400000301c2d00803040c8140d01485001c5001c503002907506201d42c46a50100c41c0b80c250000907080490a80703020660050456000c200b003400301d4039041d04141e07405181c404115040035040c0951a0a4410599042c0c40c010383c1c851031242440310070300070b160b4042414104401c81ca03110040c1d40b1110b41c002080174002180c0484c012003070314810703005c40c1e1b1030a07007040d000c10300c205004400b400101111310007100400d10b400d00881c2040300076038806040302c0c0c0000300c1c0c0c081d150194400f036034056840c4a19991104200300c2500060382c4104065103000385404122002a041c0035019007190006180d281c1040c26a0031512260200708400c40c3c1512444014183c1c0c200c800c0c40890026149450000d505019510904000541c141e000340c1c100d403605913007246142c850b070220301c0642140701f12586071702c0d05818020b00c0c4035040e82c12a5554180c050a400e2038107044681581025205030021000120801802400d600e01801600f00503101207407004016442c10300000e54882420b030b8010b103240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 35249447 1250 35248197 35248201
    0xf09010c03121401140405010b0f07111201021308010615111006080303150607110405040309030b07030605010305010b130e0408070c0b0a030c030506031207050106150c030207060f0e0603 82
    0x503115840140c42401802c1051050000615a0203440f600900402019042c03c031004005450300e0f00580d8102d0326419201e40c54003448940c117001546c0704c0d00040c0ca0501c800440c2c1e0080e030720740720321101c4c90112000005840e105200c0c0c01e185841312a13408401e0583c1451010b00005040700d002c41c3d400c0c025820b160b000414000038541c00c0c00c1c64010703da1030740c914107640012201c4004c001940f140203403074080700ca01700c1104108040c6001c0d2007009421303001c0c041c02071a060704140c0d00c50340e013041c00b0307040040480740e890303a50140b203400446010000940b074110400c8030b540c040c00741501608132161150300b058100c0500320040c415500c01c0400210180c0081024824040308603055103800200b01d890580e10fa080e0302480e03500000b4a000024035103451911641e200f44549400f074800200a40103283c2a03510b08a034075044604203540035541c03140b0010700300c0111805441e42c45072980b00c214914110f07041c0641004425408402401920160844280d50000b200001c80c0811076001d5100e07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 35250697 1250 35249447 35249453
    0x43031203020d110a0302070b01120f110d0605040302010b0102070e010e160504090e0105010f05040209030a11011205040b06010801060503010602030909100909050c040e0c090a090204020702101806050f09010c 91
    0x689001118640a884001020540241e150f0000c014242c059408c071800741e40d840c64400e800108804c00035000b45503403051000000d008001241c0d10400007400c03c00031440b0f540b10001281c4055030b003140541c0d528040f0751001c0d41c06002107402081e085040c400c0e550715007621290f10503001000740310070000708503070101803900800c1618040c2880c03040401ca1031000c0a02140200000e0242c1102d0106000c000660392403c1d0080340c25103070016010b4414000c265564406010360b90580d13a0620884109042c061308080c1704144c807542c018040d45880d410001d0001d440440181c0080c42000410401409050740000031944160800e61b505000b565526a400203030b403055800c5498154200320045092010000f064001c0c801c04940803c03410742c40741c51b1250365610043c00c00ba00107900000156650705994005040140003505c054a8541c840c0d0009005290044001c4042114104666400580c46940d03801410590400928000d10001c1d140c0352801201c42c0c450410040704115010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 35251803 1106 35250697 35250701
    0x80a0207120501050a18030e0d030201020d110d0c02060405030703080402060f04030302031b0d02100b040e1609110414060a110102040807081002030c041743031203020d 74
    0x423071801410b022403030540410a83c2555800d001c46070482c0350600a0001d00e20462001303903682d042600050045503040c3c4a15030031940607500300301c0002c60000448013100d0705418941e9a90352a03200080c00ca100b84801c0545040c004034000003019000030207402c440320708a20080c9072007030802005603109030001c281030060740800d00c86111111954059900c4001c0903002188030f80744201070342c2c03030010400c1c41c01c11030f45c0d15003e0821203540b0620407000741c001c07001c80c881d140c40c3c40d040041225400c3e402400344103c40001d8180c540034011448060a10034000003175440b29504d40700315403500d2540c400d01555000f03c00c200104011184220b030300c29041c42c0780140c14a41000070101c02000c1030004a00e19106540d010581036119408080740b951f141802c1074454421040f885080312014203413510349008900c4c0c1800000d680707050b201050640381c900181c032200101c0304180 = true := by decide +kernel

theorem cover : BRFrame.Cov 35071947 35251803 := by
  have h0 := BRFrame.cov_init 35071947
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35071947 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 35071947 ≤ n) (h2 : n < 35251803) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
