-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3320
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:05.510434+00:00
-- url     : https://prove2.me/submissions/f4b68d60-7f5d-4c12-8ab6-b581cd687b4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 596942446 ≤ n < 597122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 596943696 1250 596942446 596942449
    0x3060509030717090604170a120518010c120c060e06040b0108150103030e100c060c0201022205030a030507020a0902041806080d020616050409050c21010b090d030905100806 76
    0x140c11071445042c40c280070988060755468100e46c100da0000005d00300070350b5070b00490360414922540040480d85c40c41440f00845800c070015200170102422044c0700c02e4100d00c01510714010901c001021038586034042d41c2c00340d010b040350300007440c080e140018094110980d0f4500e842e20075103068820760a1b4500400450604200064941c00795103481c04295241d9a000342490340c1c00030007182720f848a1030515040c64801d00040c54495040202489504d014050281c000c1d8032260050a88044603032400c080d00101c15140400c4030b8015004002000c0580c80840e141c1e04103040481e44a000c0e1000000c2c0801940064009045100c2110000c203c019103214100c80c0c09500c032511a8029454518101c1e4022825070382c8402602c0c810b4607940d42030f00301240c1c1ca20494100024480c41c0205008502108402030002d4255a41c4030113038071076030302c140380c0c00c21031092184d21003800e01007100720390b94140380c0b014080146c4a070400383d020988820000e0440140c8407000b1001880843c10030403103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 596944946 1250 596943696 596943713
    0xa0609021005120112020105070204050a06050307081b1e09010f14090403080711030c01090c0306060f3006020403031d01111005100e010329011d06030106030605090307 74
    0xc07400d5909005142c41c0e60504403007144030051003000d10200c4581c81d03002c25079001c0d408441810b0b500910410040c50300b10400310041c02d29010780380c005c0c42990700100d01000005084100346000d0714161780b0300c034003040c2000032409000880e01c03204101511182e109803249603055028050100400d1174960402c0c02c110004c082c0b506103076100b0300d03031001800040b03074124070269004120b0746401d13281c04030b205055514500c0348101d144415880d0090706001d0005000400c4107592042d8002e020140c0d4518809000c1b0a085c0102c00d01c00520a960300e00005480502c03452403071151404052070007080e1103c2d800ca030850782c01600403601c0040c40240c0100c4000316005420824245561000c2040000c0c40c0c1e03824401c1c00c8104440c1d95036005c2001c403641c0e0780804008103601180c24440e903859242c9801c40c20800b400210200701040c15030400d41081c09013090503909181e080710f9000d00710040c550103000020341003603015541c810020000ca01c0a010782403080e40014011989c2e0718091400504 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 596946196 1250 596944946 596944969
    0x703030f031a06160f0804150e0409030206271515040516050702030102090a0603090b10060c0201200a080901140f090d080f191d03060f07110a060902 66
    0x142c650740d000700c1010030b5540c4415144124406480320300010168a440c0700b12184807000034091100210300060002181d02070014051080da4500603804441000d01064500502008015030045000143e0500200e0543c46505004042c0c0c0c0003017603051014903080c82c20306000c500c1c44441c47e13810020b00502c04820700c4040481a01c00708841d1610741c40c9944110754144c1080200980000d43d04195075003501034802e1140014001a0650b5803040054000e15845604a0300d00d0b403c18006110b40740399031141e400300d07403407520b5601c3c400b0184d50044030700300d0b00c20803161501185000361100401c01040501409882420351562300d064060000d007940070054a28000e4102c10403150444801c8031041d2020010140d554008520b4503107030401d800d0049008a0715010004140012052404004810b0342c030065150030b0440c0903803455804807907100c44401d582561201011945851400c2e2942ea809500341c81d0241c25240b5084043d4100101040241c8109845600c10010351070320002040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 596947446 1250 596946196 596946221
    0x40218160e181807030c080d03050c04060e0402030711150612011806020a090302180a1b050a0c030e0a0e010e0a0615270806040605090309010909110c0703030f03 71
    0x8180c607810102c2502c84800501c0541e00120b000c0e012500001e0030072200001d190700880d0000040c0c0c980f020f55a881054040810000341003401052450b00c1fa00111001c0e100d06a4038001c1d040240400c0c880a540701610603820040080ca90782c0c0c07181404d02c8030b6100480480c00140644c10500200309200b040804951b1050f40360850042c0040e8140214800296020030b01685a04c007206058503144415400690000414104601d202e4040ca04a41c454175440d2810080340603030030040c0d5024081c4110315008140c0400034682d42c04e00607404e1001c00e0b4481e140c58522024418007213100d960301503000c8451950040010b0180c40345d2208641d070303c00400c030070800c0783c1480c000400342d1440c2d54285890074440440d0754845500207a03592301c0421608645d000380000e588142260b510721080702e00780d42c45460710b004120001008400c45801c1e4005940340c500344c03814060b03907000908400d509403a0142040111400340e901c18801301c40118040d850309003800e0302c1d0074805070580340500c1c082d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 596948696 1250 596947446 596947459
    0xb0a030e15060d0f020a0b03011509060219030c050a12030e01050a05041a0702070803031306140708011403100906050417090604060f051b010501090c050c0a0803040218160e 76
    0x100740c0c0d0b16000d0b0842801c0e504102d038440408a240040391b0300981c0740d00183c0c016040000045102c0405400d5910700c0946a501c8902c40703982d818007283c95031070010003440303948a41200320011a2180d6041e0b0010303030161080d0f810b00c041c20703520515020302d141c55400c04203488041070000319800b03100d00e03030384030300b241d18140b01924203559600000d600c100000b00b888100b14000c100c1207442040740a000d8507849040b01d9403820440740c0d075000403241a2088900c0d600f0000c00314404148510b149018903003071f440b000081d03404d0041080754036400e540350320b0301032099201d040442c103180d0086040040c040c800c0011142080c2c1022080d54840034400ea40300c4001f04600400c035107804084508070760b00352800020a002d1850211107900c03070004030302d002c940c00040140c54401c0c10b6100c141203400e41c032020000844000c0c8241e0302402903807540f1a1680000c04500d001c145d4500003182d10510040c04444070301c0b00500d00c04400e1105035500e1890712106d6204100d0740360072a0000320102c02c04c407800c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 596949946 1250 596948696 596948701
    0x1216080c0406290715050f061021021e04140f01020a05060c2b06170705010c122102030106030b151e0c0a0311070906030507030b0601090b0a030e15 65
    0x500c1038403c1c0f20300541a0140b0000f0900144841c81175070391400c40900d0010300c03482c18006490000000192401c81c4111901c3c000100b0b043c0c007d2660309841756550800303e425048000741c0200940200351210038000a03002040c041c01c01a0f002030003d00f40080b1000320390903400040c42800555031a8490656005206000114000003143d50f801100001183da8a0f094071f1100c4101c09014984001f03281042d4410f52420f81c5c107900301c1d40940328064900c5c01c0300c8042c003818a507646103c3c4038180c0482d000441030404a5070507648100780f14841d0412082d200440301344203201c480c1104d00b01e0080c41e408401809000d0b8103004d403a23202481201d00400f000c0400f01105181e12440200650076610f0414030a1b4004444003a01d00300a448030075502140030314100903010032034007074410b001030244040104400510344504010340381c000d001000e1290440e5104410540054802418000180d1000590411840c014243e015060307030046500c01c64802f00e1444c008501c243d607140c1340d46c1c4104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 596951196 1250 596949946 596949989
    0x501050f0318100c08150108060a0506030406141f0f030812060102070e0a02120f0c030720010c030905012016060b0d0308061008010b091216080c0406 66
    0x580b60000920260041e501e503030400a14506886070f10b070705844a003000e640980003900724a0701c603c038800e5568102400c02620004540c0b141045403419442400c0c007100b4400b0b0306050024540c041c0c81898009150a0046254040c1c2d83c81120303034a4480244001110307000058013004001485a0721307401c02c1182c00d40d030301c007003888c0910110002c0c2200010002000d503803080103440d0041c80380300c0c00c05480341040591003010f9031250280d00d500c5003035540800c800b949450b82c1c6500c1070715104a07007810368403080012650b81c240d139920f0740d0741c603490506400c400c040f00b0701c540c1c110303e62641c40c0060441e0643c0350003800e407244913000855044c5401d106080721481001292109000700300040b0052209243c02e200030901168041e4009441c1c4c1c0b032081c20540c020004038024841180c00c0c2c0351044016004135000b070000d00807000070040600c6a103160303042c0804007101101d840d009403185210011807589001150b90b000303141c01d6010340015400390600780309400140107500404004034184e4035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 596952446 1250 596951196 596951227
    0x60c0406050a1b061b08090d030b03070305070806010312051c020313060203190b09090a060c1b0c0f060e0108040b180f210702091303050c030c0304080106050105 71
    0xc211000d1103400a85260340074443c420300084202c8003045504280500d040c01c6000384814208000454080103000d4015401222200e20a9410f100240412115680b0450240048020840e09031250810100c0084e0b424400301d0041d1050000418040d80355040600f20b6252000c8010140702c030410a41080f000550385000c048407079004c002d60f9030b0f221040c5148032580500000f81c0510700c0403042c02030b5210b805103208090b51002905100c1000390038104034007500203a5424409a1110a403080010783c60b0300f1103070902c24203050a031040391500404d0303007007410004000c50b90312070102c00a20900740d00c42c000202038034070307864051070460882c8000380007080080d10240c0300c0100c4a00003201018868100b003681000c804c199030813281c540c810a581c0c0c1c0003505135036002d50340a60002c8001128074007501d21043e0000c2c020040c40c1c4030700c45211904409003009031708005003000b40c1030144004100a011170040000110350303c0c0d00d0001d5035802c403882c68201c141006010402c0032204a0b400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 596953696 1250 596952446 596952449
    0xa030509193c0603140604061d041a04080702040e1c11120a05070b0a0207020d02060703030902031c0e12060c0f040302030d03051e190f020d050907030c08060c04 71
    0x241d022100601c01c01100c1c0005900c0400c24400c0b8600440c000b00b201036041d041040f261070710888074641a00d82c8000c0100f0303a0854000c000d1821160414214203402c0c4084007a002405015500300f018921510107001290456050b5103903000060350b03c045080c24853781b4080c00c03501c0c010f4a51206017040aa002c00742860000080101002520054110074440711081112132114503681d904441006449604040c80030f03211640c4d5200056a8103203640200c91101c0d074010152540b01c1501d60801c181d5400c5a40183c040507601c41d6103030010b0b1001c21181c8078610800c440c4da40c403107803026002800012032070b00303281c000d4014200070740c07a07030000117161900004c008410580b10000c0c041c00060303038000e07644060740c54410101030352040e9806502c00c40c010348400c000c0031080c41c0c1c0c807100709600070019151640b484111000410401c00da07588095000300d201c1c1400f6162002820b0940d00380c81c0161109000340c0c0000c0001c10411901120f41710040840c2e0000c1c02492405119030316090195 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 596954946 1250 596953696 596953739
    0x1080c0a02070b1204030f0201150314150f01081014181c0e0a09020c060601080a06030606030b18070806040803040807060e011505040902030304090b0a05030a03050919 74
    0x108003918000d0092044201900d4404443c90b10345140d0030018154942c03c5c0e44c182d0208040e80c0300a506d49106001d0030050030142c103c50782401d450365035081104141d060341041700e4050101d0f11500105408440c1c0d01035111002c0711021035060103402d43c1000e91a0160540e501c2c6400c00005032500c440c01c61300d0784070817604118410b0203410080c15007060303a130001040806a2840c11011005d40207808031030020360a80d1903103d21382d1a110303038104038031440c0c25040143d40050006259076105d07420155220b40030f0540814115541c0d5214000e0302c06541017221400d01100030042c4142d000000d50250754840c500510906107899030301601c40d40c2c00f91010b80b45001c00000541400781e0b01d0301b12103240d035001c0701c104507030580c403910396000341841910114184603183c800209440d140c000c00d00c4898005009d10324282c980404000200315050301103400c5414560001541c0c1c2e03042c404180700d1802922090781d2660407008211040034407880700b4008039040d06007032100f075a880310740c8002e5015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 596956196 1250 596954946 596954971
    0x105030a031d150c060f07111b030c1002010f230c03040302120d09030905040c0909180b0705071505070e0d0c0e10030b1509160e03010f05090f0703020108 68
    0xa0250105410350041e41410722440c3d40010a0b039034aa500040203841180381c9401c0c0001500c80c0c1800701e80f6440a502c0c5546142e02030320041c8900c10998044540e8650000c1c125402050500301250401e01c00000c43d03000750f5540d028070b20705000e071405110076503498088121558610107100781e0300e050001d0101034845a000c0000f03010507000f0807501c2051041004415161200e14040b5405080c51042c11800182c0a800024a5081c180255010703044070780c0307a07910018140790200b401080902118803110500030040d02c04113052a040718011074140ea41d09179103011500b4440b8201c1c50000c400c6030243d140000f00010154070040031421400304407000501c3d10380f542851007200c0502d41185403107031400020b2180702d20110000000b10381c89406d0620301aa20096503041d0160400d480da600008a48001038070080400755055201034941040444204590f0200e400c403950400503030001da549000b4003000d028108a004901c125400043c526a4215800208030b2500540950070307001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 596957446 1250 596956196 596956247
    0x405120304061404080c0129010e030a0804030b070f020a0f061d10020d0f020c070b1e0a0507150912080a06030204020f07020103060e0405061306110a0c06050105030a03 74
    0x5540d81160b61a0015505401d080b03090074200b91000340d00075001e400d99586040b595002c929070800f05c8c01c0b1116508040c82e4124180b590054074000303000b50314254075005880303400e4001500c80e405003000c0e5001c0e0142410134078101c4cc01401d40301d40841003800b95845080d040c070003c8c07034280e04103221903030001c00400c040141150f12007c100f1094044d001d9806100c100804030341499000e03140c003d00401040c440c100d58244804100d03c21041e094400383c020b81400d1011038280801030603040e5080c10150b840c84110780351041d4503040700ca80b4100190300084d0100c10302004c1c85103810109078002c02003060740e00f960b032070003407094a52010b9000c0c0025100080c40403455540550011500a842555109847ca11800d9940c2c45a941280403e2411f030380451400300c8174505910450340700303004000313903210700d031480c40e40072142034081b42c0351516140010700005003e00580382440b07003034131100385c0010580f174503a0940d04141c0009000f44e0068190402003944a40b4440761a020804000da081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 596958696 1250 596957446 596957453
    0x26040e0411060714060a050c0403021e0105090d03170115023d0501030218070c0602070804170604061b2f0106061701080d140a1e0914090405120304 65
    0x1800355210140c400b00d15036440d201e08100200740c5d10300c14100c114003080113540340865600c0301d000d00e0102070340062800182d19840580c251031094090341c1414020704241d41c050000c0d074503d0503c10304071300003001c1204151b0b02910702e4141e640501004150303100351301c1681074025902c80d40c440004039442c1c90046544403070705100b8480f002c41e0081d40201c181d14515440b00401500d42803004074021a00c9403090005c800141d0f0703a0501170a040d0703a071000d89802544400b07003e500325a800f03031480c8000700000120444448810200c010329140078210710324040c01c05c101121414140040010781d150403600040794005804140e07030b000e0710000d082410801090000e42030741107080e0010356180c01d10209110740c101c000c03040c40c0c6034000a0512180e880300161503d8003202812000424501d015040036811100080c20f034503003240c0362030b0b007550505500000342282c000040c10045825100140321300441c1a0003811203c1b02580d15072329030706065407025501c0310000440540d0220100224017003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 596959946 1250 596958696 596958709
    0x30807031a0301051806090307020603010e1504020307080403030c181809050d020c0307090b01020d0e031501060e010f110c09040302031c0b040e0c011e03060b0726040e0411 76
    0x211000b500030842c0d0301d840f0403c480115101040301a0b2449141e0016502620003c02c4940d401e0380500342d20304591130241212822040a1f04182580715294208141c079212440914440c54841e42c5950703060030581000b804840d0705d02e04950030010000b8200104850070044501115210f501c42c00403038104135403c1000b48903245c4020140c3c0180c408554550303030b000030001c0c84043c9c1102964842c40c1e90303115003405c90b4000420b00340560052040ca90f1043e001d552038411140010f029246c111f1400c14003001054000d802c000003041c55000c4100c1d0765640b00801d0710300400141007100001c1c1402c4d0026a4406d40140c09900c249400000101014400e1090300d0790f00f40c0d041e820b4a01c822407400780202400101184901443c6000f00024813503c2c0050840880307032040e16406015629001c203c541c041d00c140c840c80a00d5140c51000400b290120000c0030744500500c04444400d040c0b0f900030444200e6209100c2c08500305000070302085d146850469000360340402c61003140803103036012458 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 596961196 1250 596959946 596959991
    0x1406091015140c0105060f0d0c0605030c040b0a020d0306143d020c040f0501060815040b0a060507120305040b0727030506040b10082e18150903080703 66
    0x50a410100d10010400f00c1500014040c2c01c0c1100c81019484c0014140071244544113006803185158002c00c01c2000e0240c0e00564000c4149401c00c1c3c07a080c2c403406200401d620450802d40168000080b9028080d494401d0394041d04405291042c0800140005001c408083e070205d40141c18800c080c00200b5010340358100841940045d541004003903110294070b5504105031140950f040c00c04440d920b500ca031003490b060711075a44031700e9020341325611031101d80d9015880c0150090381c1c41e8a480e000755164002c160051034695120b0366140200d242141c2c0c400ba07441d55100500d4144018000020100d00446503c690145402c060040741c0b02845810106000111008020321910201c103010000c51000c0c840c1d4012039003c025070300d5204e20101c00740c0c507911603411a03811a0315580e00c1d011103018040c461107118040c45503140c0c0c41045c40d40032030b1072400144002d24551500e190030000030f00d03020300c458108a00e08200c0c0003150784020345500030003003e003010107640711400780c4140404c0d1032001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 596962446 1250 596961196 596961227
    0xf030d0f030f150b0331030c14010501090209190f061d13020d0509070605030c0c0309040608010209090c030103020f270c04062307030e0607151406091015 68
    0x1802079030390f18113421681c000e40c1c0d000010420002082004071520110318031059a8240c2c1140005040d02d04651031507400204942403c030038403984508120900070140030f4603040702c00607660030a40301080030081031301548402074842e402c02001810502d01620040314003904200c0149125000403001c1d80e4405154641d100103c8110349075801c9035075014010030b0364120f40130812611080409a6181d401d40324400c00a001080001d4a440010000e4494503107003008503420003681e000024140d403131541150815a6020410580c5032038008007c607041000e8415140c0382d075046802241c20b00f103c9030b078424054003620b02c00360300328001c412000c00c80e00c01d103007940b8200341010300000c01c840e0f00521a80340040d66030782c2c42e4040e08070b403010401c0104c01100c3e2424038002d060703942601e5a00c60b0041d8070303134000340901100012614210142d51802c2c00603400040c050007149080c1c00010300a403e0074002c04200040080310000364240c101503030300c1c0d04509040d034044d0040c100c034400300850612 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 596963696 1250 596962446 596962481
    0x30301030605071403060904080c0f060c0a03050708392a03040506091002122b0612061a060414130203070807030509030d0c0e0f030d0f030f 62
    0x14031410b544280d0060f492959480980c02c054902000c0070f0000b500e8840e0311030b8410000c1400144100002d00c0076450a00a072060440c0d120a680d0410b20221003010000400140680c50246e26201d02607000c1410304001880303040200c0c0019110112006c25108144ad44000c032000c818000d034550b481962007020141c0c1c480d03101410201c40d03208120b04510180d03090000d9413031741c1808001e81d800c1e00c01c0944400d013009891402c201c0441c103c6011141580030b00e07810b500c50120007000504804030154850011084070300d200583c184140d41d0f0381e0f00c0c00c5240c040280b00c0600c3c80028081b40300c4d0080070215503481c0009481e5070800300e40120942c016000500002c4c2d940711402299100307402280d1049441e0001e0603c00181d206c101c0d11500010800700001e041c0c58083e500c1103410070071030001c4a0422901c040c0140c01c444040c540c03800410952500e6020b10b00e00b215286a42030300a601808003400c0614000d0801203010380e40360140340d01e58074003090ba25920b07404910002c6013401c41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 596964946 1250 596963696 596963699
    0x809070314031314220608070e1006090b030f270d090e040b061306050603070c050606010c0c14060c01140105030d0309241416090e010e0a0506030a05030301 69
    0x415600da10090b082c00c2d5440c01d91200046500300b00090084503403011706038440c0039240c02c0040380300d0740e5000d0300005800d50303904c4003243c814400c03c5180080c0804181c0c00d0300300c1c1041614082074501d554014410048009800d0180c1201041a203401143d0f48200b0441512441000c02c0011035003058541000d00400a00d9545207000404000c50769146d00c624402d25242d040d0b0002480742210050000005c00c40810524180041030341c414480308100019101d03140c1d0002186039106560903800141000c0c101c0c0c00307004040c00340b20341000c02400c2c03842c50084265101822a403142c07044e0002c2c01e400b60042401d5803030703000480384101c1020008000882c0060554aa03c01d4280a018024401c00325103960090003032140300740ca40d80214407201040d58030f40385000c001450100f072461080e11030310102014a06150503600a200e0288052011501070b40300400428450340207148840c03503400108001120684140c0e04521400000709903941d40c0303800f1038607080c2e00300b00050692000100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 596966196 1250 596964946 596964983
    0x5060403051c18020f12030706090b06011d010509030a020306040803041a07050412020607080d052a04230a0603060e06040b01120b0418050304090b0a0e0708090703 72
    0xa02c49002d120200c4048070741c052003030008035040c640c1141c07107102220304a803015241c410216091400002c00f0103644038034150404d800d5400c00c80b0b040b921240c50307100010400254000c0c25034820020300e8188607200044490307000308011401c41d5814010b000030605010b80341800b984010380d4001d811103000d400c151411120a03802100c0a41d1214135960942600c1400d00000d42d0295080360b50f400d0802c2c1c1001000000b9a400c190304aa12940401c5900d000503910009044400401e920008552401c110711444c0852001401120311440040039104480020142e070250b4203040c02c1112050424426004070010b6034050300d61004006c1c00001d011945034203c0342c1a07503050030f5a2a519103640c0e060100740c0d00c8d801c81c00e1f40030a0030400f058004641541c440078051400400104003404081c1040c440c002c6690070603201600300140c140184001801203c000744001d44850400616090714600c205d000a800e110402c070180010815800d8100200b0b4041c0da00031040034810a207140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 596967446 1250 596966196 596966207
    0x7200109050a020301060f0302010f050d020d111803010203060a17010b041d0c030307030819110a0306230a2d0f08100e1903050c190b0a02090a06120905060403 70
    0x2e0b4100c3c400d6090001c04162081210903d404880d410303140e0340355420a01c0000c0d180380c2c000d6284403003041e60900102c1e4406000c4d0043d50541e62400419607640c0041040008503844040c800d58080e0f8010401d01c10785442d10030380360f81100d2150018003600907142031814050400c0140c0113600c43d00b0442108201580700a4412000302900c00311603103044290705150b2607001d85403001e40803915800000b180306905654600d901a580040002e01c0050405a0384468104282d4500081e82e569801c0c0b0281c0c040c0302e6020080c440303040b022030304c4131402c10006001003254010307c1c280003044c03115480c00148041c86019505101300000d030810340c40c5c8004260600145c41060b01c5840342d80a50814004a449400c84100e001e8004c1c0c02d54035003624400302000200e40b002c60811078104041d01164a041c03020760b0355040c00580c14441c020260516041304a0b01401c81c1b40c216104204140c403d40c0c1e2100c41800300c4206003000c4182d10b05c20100345004019961020780759010b94030401c000c160b07008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 596968696 1250 596967446 596967463
    0x3093618010e06060603060103140108010203010f170a110109210c0b0a120c0903080c01060504050702070b04060e040b040207060903110705090606091912050c01170720010905 77
    0x40c816000000c034a00c080c5400d030307001e001c0ea1050940118000c40c011341001c8009550102060601241c00e102c039258107620143c0990021b010303a50f0110051101c070850000160050001c034500d4000f921a4568040c0c0329081d070080107054101c612202d56499010705110002401c0110031241c001e44910720341903103140c18800407541d50703c201001140c1d10b038541c01034a4602540da41d55000101c210307500c42000b0000d43c42400140500400e001002800450041000103820340004c103902d807801040c002640e501802c2c5105542000d80180400c01d54041507508859581c42c2241031074410101150042c100c2d000141d811034000510700041c0099a041403480620075665020154644510340703481e80b1013130241d503130b00a01c4c0b100845c00e01d1800c50003030480b00b00d00030140081d41d1266a5282c484034039950141143d02c40c19000035051040520068824400a082c031284901306407200750070702280100040144400c00a1100500000b000c801500b00f280d00b00030032904c661410f05950b0350148 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 596969946 1250 596968696 596968711
    0x9011814070504110d0b0f10031d03040308070305030c04050a0936061d01020c0a030206060a030c050904050a02131d0d0c020135061908030936 63
    0x50100020b000c0c10107126030614040325114060500207598002c002800031500720590085240160148903540d00658502e600c40a890020b07602041c0090300d403081c4202c0000306040e41090004101140e4070f5400c8039a0241d01d441e02c0341e587ea480c05043c49081c0240e40083d40c120003252408201c4503142d9000d6032069680d0420800d40452030642c2c031440c408000c045096407610b5481400004901d900862171140030201044501d8a044103a10708980058030b0603400c0e40d21030704203601031580601c401900000103a45006005045403070750401621540308040c040c68510380041c00340401881240c140790760040280b0000000002404040d1414040e03c06074000c1904d848400b400340011031244824950700c900a801c2056001036900c52400311056411115074038440d203940200c000c082d4034410281c150f07120746042210611003000380c1080d03190341140c407420050042d41c2c400026540f44407000c445440068800500100e02e07000d41502c0c02c0c888440101e804c60341340040100c50f030701c600710 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 596971196 1250 596969946 596969953
    0xe010e01080c041116030504050d1101090b071208040f0b0a020316090f0605090d0b0c040e0603060601020601290d020a0f051804020d0b0918070f08030d0509011814 72
    0x1048101d407113101d40e8000ea00340400c00c4603a041445e44110707015900070308160303050075540d10110f0012040c04c82d08803114a050003070850f00c1d40e00b04e034046010b080502139890170f00785c0d15660808180c02c02551030007844103c00016003040a100070039030000d6409039002c6454144409500045d4009441d03440c1d07140074030781854080c0c070321801d280000c035030b852001c04000381d282203429101a80030750480354005041c176030802d0200361912180c50007200c0c5181d600340c2d41c40c9485004d00f0003080180c50315120f0f8108500b80911a80d0000725207065a07440e1006640c404500400c0038101c500462905000840100b2210718180055002d0075640344152a054411803840300105d5051060031101d07446284a214078805070304040e400307072410091400001a0704a401300c001003d8070000c540211148210880342e072a144810b104013001095001090424281400d0726552240901d80c0d1181d421580c4800040034148d0075000b207030088500c0d6612903128220b82c10640c1c0c1880840c5030041c050321 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 596972446 1250 596971196 596971213
    0x151e0d05010507081b1806190810121109070201021b0106141215100b032e061d060706090503031b030705090f0d06020a050d0510060c0f06060e010e0108 67
    0x110105c141581d01c4800211403804e0400a8010303d40c1150a6a05801080034000340300311814821016500600580740e1410619100c081c91240ba01daa400c250060403140b841a800116060364128070401c084034901d5059960710412070090044d10358034588a03a0340c031003c014031174040d4413003429503070490080004841040c040c0051501c807925501c1055009103200c40f148603020790120b40012404c0018081165610860b81050300143d41461805040780c2880c0038010005951081001743c01c0c0a0780d074614503210340a0035a1550b201d10301d00f19240a4041d1415a441c0002c0b00c60056001600300708da03660300d0074010f945e500300301c074030070406c680c046c4042c04030f201c41c503090b01c3c4900d0042d900e052400704c4403014003004142d4901d041d508504c0c4000060005466400035110b01c401c0c1d07a44040d22070580500420980b403000d0190040e0705e080c50018042e40e940042e0881c01260000000442d1602d1458001c00900300755001d140380c5071a050011501d0020075a0260488200c00d0481d500c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 596973696 1250 596972446 596972461
    0x1a01020c04020f0301150c020d0c080c0414150d060908040e0705070c03021002031903151e0521030301260105061f09260114151e0d0501050708 63
    0x1c2c403924a014280b06400d0004000c51b00100c0680d0070312424514081e6a00c4a80c0e9005c034049000040040701e500c20840020b020841040080c0c0418402c00c980130b00401c05465181c2511010140c00b035030300c500e00c030034105640d0b031a40d41d0358030b1416a108804025002050a10900b01c0c3c2207402a05881803d410220310518403a40c155000c03550003040e01c107106451076007000f00b0134202403c000258001405900d5800c802d14802d49140d907103035100421041c014100c5081000c10301c0d0844da080d80c02401c1d06070780d554110100c01094507815184850009400ca18a8a87e4032414220744414400040003003241072018612070760351001c5c119406030b80c080d10401582a80c8044588035009030b941d1042042c034400c0d000b84404100103506110090035118290f01c5002400c0054000c000d1169001c0704046c001e003440f881d8402030015101c0710040c2000c05050110240d045113a0348199510501c859241a001c0400384200d01e008104500d882400d1134840c0c00b8000807145100443c40400026000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 596974946 1250 596973696 596973701
    0x3030906010509091c120c03150906081018080f07031b030206131509050c1203031612140f0405010c26041e05030d0605041b05070203101a01020c04 65
    0xe09000c00070704082c3c5c003811210201d00c0d100084030300c1000b42115600000d503003144200380076014655030100e00c02c1c81401c1e5280c441031059200f001c0c0545000010090440c0c04248001d400048200c045281c481031007190143c0003111030098803500000400c117150803c6070b40200100351082d19907140030040301064181d0b00c0071402014015801090000c0d9480076104c07010a0024410703400c564018800c800500300716085907030700321090742c807504255845117042c00014504070100c03802146103107441001081601204269401804240d0343c20440414040d086a10100d40b0144d0f50305035072601d0741c141e218000d0300343d4080c1d44a51078211306c10707a0b280c031882c1a01ea500d0150350703c4c20440d07040890072000c2c404000340b0a99000d0714a640a03960b401c1c5012000d06040d0240d402141c83d41ca1a80c80e040466400741d114a1155141004d441042500115068a007044509009880d444a400801d003000c4030b0f115280502443c4c14450002107481860007140d0290a03801c480404c2e41c010144803c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 596976196 1250 596974946 596974951
    0xb0703090b03070908060a061701051618090f050a0c0c0b0c0c0a0609050105180c0306040b04031b0311070509061e010c081c050c0313080a1b0503030906010509 70
    0x50030062040c8070062400000b990007500a2503c41009a5070701106401c000c02600d0021845446180810201d280e55140d5207951039028000c00244c203052a501e003415098003402e5090003c800c143c0c0181030000503201d0000c2074180ca0a001c0f680b81c031072003a0014030048490b081184c0c584946121a144241c0300e000d40b481c1c0c8004840c000f0b40312402c200382c040d00880c101c200a4480d0000300b900042041c0114030001e1b120720000714080c2803406007200703c141c01900d00c0329580c2c04101d01c0d060f6980c0010320590816001107000b01c568440f410304542418000c40c503440d4002211000504156010032a070000c00100320503200c42c551180304012044009581c1781c1c1d8028105131020002c240146000b0b2000361050408007001106960f40e01b41d5504400310307005401386e1580c11140c0003103143c01182c1c0d1000c10b000c0303e1440d41c03420042e0f1318004426480b0107440c00c08049070000c101402050303008605046191106000040c1d4508240d6a6104071800c9425004032000004c3c2814142842070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 596977446 1250 596976196 596976203
    0x915050c070905280207020f030f0706030f180c0509070e01091703070b010603090605060105360a0906090b0d03020a2919050c16020f1908060a060b07 66
    0x1416850101c0398800307000b02070490075030480e4003103401c506071900084c4071080446826025031214541d00401041149810074517000e03401c0400582d00511007c10a0000e44126080000d00e5012550400d80208481c1a60f100d0050601d0102010300003c0002802180d504442002041e41e07a240201c4090031084a05030110306c1c0d01100340a5400000341009003c8007020480b0b08040d0240c481c541d18080a900c40f20110b82d841020700240000740c01a264010303001c1c200f00f8600418800c51051176440c06000d81030603241c86481000740e0a51240303400c1e695500034600c61a603511402078030000d111612506400d0f9290190006250608402440d85241c1540141400740521b03210000c0c039440d03a580038440b20b0300031a01c80540320754054201c1d010780307100180c245050310546541000c0740c1001d0141c1c010031b101403080e041017200303000321880c02990503145842ca062342d00c004200344210700030050601089403640803525580004840c0d03c2140d400074280a226074800300440184201000078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 596978696 1250 596977446 596977453
    0x61e0a03080304141c110d21140a0c020106050301090302030301060507080c010603150507021203130f060f0b010906090e16051c02031501050f040e06011e0915050c 72
    0x400200715000c000e1580300303000700c03000c0700d0020011586505181d84003150380c072114110015105d40c140d00001044032802284014440091500c0010b0060881408011607014849404c44d210613425003080c111605084401c11341410b00702d42e030700098040c070700b04900158604140016180380500404040b42d030580c02a525507401c150044610703901c003540030f5611201c100010300c4101000d00c1123100460154003800c0300125102d03010740036581c0150000007158031824003080f400791460110780d005031500c550140440f04600d02125a02444480600f800c2d20f00180c81c00d8010036034000504210b000d9907119174581e201c42c4140d541141c14091a8014891440040e00b003420980140300a85602d0400b5414a43c234001901d82c01855080c02142c126000b2050101024075500460103e074003d0800703d080079920048407001780114854400c00c0b1820b0000300e404c0343d0240091014906041d03442d8580f5061040000c0c00d0f0100500c55844010600d01e011550248500c0588507100102c502a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 596979946 1250 596978696 596978699
    0xd11150105100207032103140702060109150306090b1f0b0d02030a110c0d030f0c0237080405030d0804050c0d050313031a07050901020a0b0c09060304060203061e0a 72
    0x2482035803950707189142c0540c031880b4800b1002c2030340034041c0440c14a1444694100b0905010001c06907242c0703000002c2d100610105000302180c02040280c1580d00e032040020702000c0610613186074013003550019090b14540060507081c4040c1c2c010003403284405d07503c20a9000c002240f012a103a42510950090b10b0041c05942c2c0d0130381c80c40e001160030140a040201d03501d42c424501501c941c0c40300c188000310781e100c01f0180300d010380c05008401c0b80e5100940d042002d51410342000c1e4403105e40c1c04a0015001d00c1c4108034034405402c018485400304031a840d11000310503850130310b180d0341c031030300506201e80b181340b80e0007074010320803903c0380d11450703200c00030340503013107503002802000030310034400702c4d114007040c0036202c062610140c51400460088100004000c0c680f518000900b202401003403c0007401c114200140c0d0b000070b90150900c1d800921910250307100321261800b07020300c59103150701c107200105200034410a6009940160000c0f40c0b000140d400d900c0c80d41384110031000755540c020004160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 596981196 1250 596979946 596979949
    0x3010303020703060515060d02030a360507150903050105060316090b01020c130603060b0306040503030f0c07121106070903120509040f02040e041205040620010f0e0d11150105 77
    0x180d0407804207070344100100c10000c0080d1080c0c11070403400c0e6234581c1c00300030403461401c1d80c0102d681100740012a40b0954180d503201004200184281c0024001041c01d01820441c2c10820304000b0441c2140d4004050b850704030041c00f40106200c15540f544c00d00300400d01500c3e02040f041c500d401c0e6031240d80d0049180c2108030014160103000c10b810b50142a0440300c040d02e59401c4000d09500007940000c806086241440445600d448280d010340e0003601040000744000040744d400034042c0515404660350305115003403278450b032140200b0100c0420f030b82000381070700107002001c40c680340002e550b016500c01200312081d40789844040d141d55512450322203e94011401402000c00140002c074201c81e4903103c902c00c1e60b225074024644840c42c0ca040000340001c101381c0101003c1c141c5425498103150001c0100304221a03d0203080800240c144280c05a400358002101400e00580034402009031000c110b03102c8860038052004510088840042e40764041031080040c20101d0340248141d0a000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 596982446 1250 596981196 596981201
    0x1020706030b01020c180115030207110108180708030a110609100203060f1519050a0e041a0d0510050109020a0c0b04031803060204061706010c030c050139050301030302070306 77
    0x84450b8154007403100c0c45c00561301c4046d00801b444240300210724095241c240c000850f0382140022104161040c0207100001e140040018604003003483d02c048580c4540c220f860070443c079030b0f59200a6102d44040020003103400310103089000603d8459030318004440076040d84902040b0381c518074941140c11090682601d546c06184c1000d4050001c000c0d003035040002c1400780d01000310303002c9602c20100c3c003031090819090303802e000c60005280c00c50600c03221000c003070310402e0102c41c0184142c3d02d5940810907040c41400015491800504a8000040c0c030308000d42c0f00c0c1007540c055440c40703040000218a0a43c14000c9034107000183d80c0d003130596050ba845c2d074036817260085c00440c20010180201415540c1d0012148043e41c024100145c0c3c6920b4150081d08030a9813010b8103106000c0f000800c110390703811643c008034264141c00c00d40608110352805034010034506060101619088040c0a074000d001e0382d0032048602200750000643d60021810b07a07050009200060069010940c207200044458 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 596983696 1250 596982446 596982461
    0xc020106170d0f0e130638090d020d120f09120311190b070f1b060911100207080618120f07080d1418071202010207030606060206240102070603 63
    0x44c0b03800b4120003a10400a0941d001c000324a0003d43c2e15184244400d012040d01d40040c408894040120f0940844080c100c103220001410000c080c08210074034161104140d018040c0c0c1c1c014505401c0c4842071820303107410102c00102e100020042c0104200039409000c0d0301c02682e01c85e00020302e944d80075680480740c4100d044403010752800b801c00b02c1013000c281e940b265280c2501c245044080c038a44244010f01d480302c00700b419410080e901c00d58840c42c110820702c0c01480c94104a021808203120b080035410305110030803d41e041501c202581107809d03400300701c0f071064a0510094a0321a1508442d20305031032015540c00e8229042003050360845001d4a000740070300c06583c0c1c1424100403943d120b0070f2094100c40381000e038090f11522103a2150f0440204294000342d03600c22103c840030041103143d900c900038000c0c010101c01c0071649200303582c0200248402154484420700130707180c40d20310080d01c40100b603480200108c00350300b211400303030445031544000001c182c5c02482c2c420301d0048105d014104a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 596984946 1250 596983696 596983727
    0x50f0601141e0c01051906050a06030e240105040c0206060f09090a060e010c030c020316080a05040506070c05090c0304121422180b0a030f020411030a0c020106170d 72
    0x2d4010140c2e0729072801d0090f010801d000c80c00099186091444a1480d0644804960040d072070b1290030722095644000e230105880079031400294401c5200240c5190801041c01c04000e1300304e030322a129000d0340c07400186040e100103482c203012a0510003000e0369030341016515a031f840282e00d00d603200d4034100542c51660100440c011aa10201241c990208480030201004a1a512004c02da00b840c2e804d0300070040610010b2004500d46050b100110000601152008202030400210000100d128200b980c0203041c008003050740e0b8800a02d1314099580c01c0c0c0c030441d80200305036000034050070142d034107580c4126040384000c840c000706a501203030103051044000d00a4103007070080041c91711008601c1b0003440960500101d925007011900062800031081034101e80c4e0070860b42ea00c1030303101d0030040002c07664803001140c2d000040b0701c0080e02030035800050808800707012003004009840d5030428000784085800030401543c40b404441d80a15030341241d042d1640c003407800358001520500c41302c1e00313050a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 596986196 1250 596984946 596984977
    0x3050d140f0a141309060e04022202210f0a0b030d080403030f0f050907080d050f0f0910050a1d0a050603090a0204050705070201031a1c060f0618050f060114 69
    0x400c1c2c1c651a2a41c1c228140c2046041d9404e00140700c40a442d20400c0d0141103c5900031000d0300e040da00040b001540c0102c808115a0080344074002007409070140e52503600414404c900001001071030101e183c10071900f4036811044000824900c08617446080f21003031015002d070003180042c80341a150318401800407810959103d200b44a10aa244604404201c804a0104050a103c8811440d1503e507030406c021542100c0c69505a160b040300480c3d00f0b000c200c2c0011900c802d80340a01705514014000c240d50049582101e020080d40c1c410000d100540d02601d4016032284ac016103812007202242c6003582000d07103483d041c0301615145e8007465100d8a01402c071815003203e5804241940e1003602d40d100030500114480c81150b0301405102e900b402000242c2000b40850400540451a03a10204242d580c1011440c0103005a81e040707c4525402001c0030300009999021450082d6600418400140d01d040c0c0480c0800812800c69801618140e4420920071454040c900f51644000e0001c8041d21 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 596987446 1250 596986196 596986217
    0x2061305090a06091b0207050d020315041a0a0204120204020f070c030804062601030f020112140a1109012a140330010306020a03020408011503050d140f0a 68
    0x55800a00610480c0e41c4000801c00a1802024000b607800b030400d816a05104548003a04907035002801f64103c03003040b40c402100b100140003003401c0c50b01406034070120490860801c01800360100002075000701880300e0300004d50b1083d442c00201c0c0038a000300140c601a00c41c8031400740c41c140d0007038080045041d00040c9000f0007a551a00982401e034800c44014074081800c00280703407c022403c00da050340d018181241064809803800c1c014050000600100700c8101c50030559101d1060f096102800107010000b1440900c003844203504101d5043da0100e08105404a200c1c814074140c492180040c0c68114003402264024004802c0d4508003080b0611805507603004075500d0074078501d1009802c4095640d868210900c508400c840902565840055400c1122008019084a811071350042c00c0140c660300700c0c0000f1400381c8607a5000071029800d01c0c080c0c4514146424118084901ca141100c001d8141d602c7d0a803540d109400814104082c24407a05c1c0c0019118001403c0d01e0300145026020b00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 596988696 1250 596987446 596987449
    0x20c1503150a0503190309050f150703020109120c1b030b150420180303210601030902040504051e06071409030304030c0e01080c010527040e07060c030e060307090302061305 76
    0x556038000d03a0740300d805e03a1507000c0525400000000c0504010f54019134524925000710712000c00000b444401100c00050810034107100303601c0603480d25485011403c400301194070080c0080400340e400c0d0b83c1080d5a480009208460f000e0f02c00c00c4961002d40d211542d0360302c5140c0c0d180082091045500300d0344862104400324000c02d0380c84824102d0440380380c0c40c0c0f40c0303205c43c85000080003007545001c1d80c0200480d4000308264801d2141102100d5508101d030743e14800102d002c0d11803201d000b9002820003040c041000b20107d41002020450400c414030494118200360756000c0c01d580b62000300b1041035044101c4010342008240c1e40300d010f02200c3c94196170b65121034800d403040d8048051541c0c000c005021a42d41030190b4115a0402d2030300c1410810070754250076505403081d202107540503107500000103030340f201e410515071b06a499081d1841c1d0342da2403401500760440750504500140303240054a8043c078080080c2da0060110f80e50340c40c3c1440c00d40c6d0a009140d8410710003001e40d0401d140f4001500d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 596989946 1250 596988696 596988703
    0xa020f19030c0b04080c040e03040510051204030c0209070e010f0e0102030408060124030c05090d1a0141040914010e010f0612021f05040b03040c06020c1503150a0503 73
    0x420b03814884650300c0b46003052860812000400451103681000d45110544400104ad84c3c29101d04980740c071180d14209005480030720403030740300c01e030002c2800b001c01052641200e035044006e4003da40e035018964681c035045651251110303219003c91600d59a0101440c07203401d12101d900d40600407649015140c03040603141c00000d07480070903002e51650074062160103840350b41800703113000d040602103600d00450180850040b48101802201516812801d010542c505040092a8034102e5041c42d611840c0c01e4041d4003810091100924584a440c4003690f00d1f8003818a900d2488400c20803032081c03c104100280c40c94140550b6604040d080320603031003c0a20807000f245000b580001081e41d421011401070310890b6202001408101b03610030b025840c2c0845400c1c00a00002520b15800d07000e0340192114000e42d0048502c41d42c0100c104001c001e4003240d040305543d07498080314403a000c180304201040f00c02500c45a0985802d00c082010700c048002c0c00100c40030020000710100d1349400100740b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 596991196 1250 596989946 596989949
    0x50c0106030b0103050c06030403050f030411042301140a050d050a0215040501031a0120070b04090b09010906030f060c092c0a0e250906180507020a020f19030c 70
    0xd07090b207001c0c01042041001c00039000d11035800e441c180c4c1145001e45025145000708010350a86101c00400102001200f40e030011714000000d10800c1111b0100c40011180700b043c600d010b2900d004a0008202944601c0701444040b50041200382d0309400d00302400b000002d11035084450344100b010b4280142d4448014122218101403841d8850340740000041c250b9402c02c48500d813582c100c951400d01d90342c3c0706445801088400801000b200180003029152030b880d40e002c65281080881d010075408800d0300300310700700703c1c003110710344200d90702e03012420111070300d61000801c400750b032400302070000d03506400c0f041504c40d42e410501842c1307941d081410404070b84249002440d448480700c0229104100c07250303030303003001424100700a4044c04410803a5507041c9004510500101c421180c0c204408080c0b1400241c0703403540017844182c5e1744a29034008130f420b0744000c01c0d00320b00303080c000b40482e8400104002c2c5250010594a0b4007a130800074418100c0c02c410182c491140d540d480440030411004c1c0342d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 596992446 1250 596991196 596991203
    0x8030f0d2c0c0108160e011107140f03010615110f010612030810030203030a12060911210c070f0812040c050103060b0412080a0915080402040c080f0c0901050c010603 73
    0x380c90341d410615082c00c1c2412009440c1c18084d0312000e03c98030707161030700c0c000f01c04180b142021100d414220740140c9040c41000303a105942d11034050049800c14400001d2804004241c41103a480d180200401d82a03a000c1c2c02030a8141884080464000388604030481e03100b103040c020f6940b100303280700401d825541540c003c41c003e40d01984a0000301688902426813010351030414041483c11903000989030b100d0000711104000000704c121806d002d49501540042441150170821000513114280c1c4a81151041d00c43d640300210000641da204035115521a608a40d8810320304041030380c80481c040034405054454407002d0011200c0102201c08a901030b600415000d0203651426000506866254114071038090080c04100005003441a80d20800b503808161991924003c240840c0e03034000300c1c0c0c0180750b40d14464050081582c2c002207002e024a0081e02c052000106040301609e90400958105519030b4030300000039103241706d0401a000c4040145800c6260045040103c0d0a6950310f80064 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 596993696 1250 596992446 596992511
    0x3020a032a03030b031504050606010224040f14030703030b030d030e060a0b030c0a2c0c0912011805010506090105030a020303070b060607060501061d040608030f0d 72
    0x140281504408a03601400965041291004000301078120244421500405254584001c0740807640c0504c5044003c0c0e15040c000103091a09050040e5070b00c0e010303078110707025000b0306264100d0600c05140380c00d07400d100d0b4001050651101e580d0031400811580c1c0694000343ca0748100c499100302031008041032806941d010640040b2031041500b80010a84c480f0305141c40d1102f0780170144008104150b00c20b0180e000010611902c0740840d090080c250943e0703500c0b103e50140402c40030000e290203518019041c5103030743c03160042c0035980116002038071850b03d44207080c0036103030240c40c0400c001111000c10800200d0350444801c0c6092400d605440c044400740d444104024080c00d14070305440c01090220000c106104268001ca40c80784078010b03002d41100314060004000c1d031603410440320319a50080f0200251b45e50303040000d06035410914000c0000384100a1100c85180600803030090b44e00a0b006540b0b040160907014031540d0190030007050070b985840b09500c214250901e008291069042c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 596994946 1250 596993696 596993713
    0x10213060807300b04020f160309090501050120070801050106020a0219030b010b0a0212070f051903050d0f0609020a05070506010e191a04050a0b1003090b060108041e0302 75
    0xc2c2030300340840d0750348a000f403102c0c030302c11105038055900d80710400100d180042c600203000c0220f4040d205248150181c21400102c000c45682c1d100726190f0450b020f41c0c0c0d0340c00b00a44400156007950070078490300b030025003508003180c51340c0c981c0c400d40050702c100002255017240c0c0d6059104d0035900d00b40d12110140e005421031600791300301581c0b85002507941d2008020413500f1640c4000400350107001d480c0d40540d000c20b145c034081d4000c100c0103610f20301c451803003074503541c407482c2481032801542401c0301c581c06405402c080311013600c8410004940d041c4c0b20b680c104003030388103958001c0040204004030a40c9810001981d0303000c61008021554090356aa503540b200c41c01c0582c508141a484501e4041c0d26500700711040415004120303c0d44010003001c540740055001c1d6018800d84c040c62154060300d0301041c8207864041da48480308811058070444100310011106404903045c81002a000200c45800203180390b04c2144200e0f07015201c0d07052907000d035859a4107100d4500c1c4124040300540d018291 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 596996196 1250 596994946 596994961
    0x180a0821011e06020c03120c030d1404210206041104060f150f0f050a0309030c0b09011a040c08220f030f081b0703031e110d0506040c1b02030102130608 67
    0x30b4000034107094001400c811a01001080c3d5569041002855009000c05c0c00e60340c00c0002d00c222900d0060241061000182901e00e00b0b404800039182110101da01100b00c512031500000d4030410b214407600a00080e1b643c9448440720303081544021580103a85060104000812017140743c0036006203500b00341c1520003007002038000030103000c02e08244940148d10300c0029034003204503121a2649d207004901a1800e01d416522980c0507030009060000349401c015030070b41c05510585403401c19000401d80d00030305a003400111042a9104000a2480c10001d11409001341c2010107802c100e00406502c62000c0d00e400000b1081030800720001030840c600b58401c036911484554125008402031040280c100c16a400d0324801c486c0014149501c502d07426400c520140c00c0c3d0340061074210703000c1c8900c540464000840782d000c00c007401701c118500800300b02a800c151103030342d1415180e91109002c0f19203283ca0001c03d81904141240c2c959020000803500c0c422116001d4010101e58a504d07550b41800d10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 596997446 1250 596996196 596996249
    0x913020c2e1e0204080f07090204050d0b1b0f0a0801052e0903050f030408070f03020d03110109080a030506031903080c070c0b070b040308180a082101 66
    0x1035a1075989203038a858203940110402503140e501440220004030350707100780540b14200518601c81042c081c804500050012000b003004415001c14800b520001c903203d041000c101d0049024150704401d4154588001a45c00400d040d000389959040c00c104481c0d500090000707601c210b01c0c0410f007410104900004030341064510340500703c11542340070100d000040c61880543e00c0c008101801c8580c0c000c03c141280246440005103810800b43c0d1210031031684015603030350061284001500c03d0410000303e5a28400071344040c0c0380d004060b440d601c507291b24202c5041d085201c50510301c1d585c8000306400289080000c14000d074550b180030a80e8940381082504001214610141c20b82a440031000081c1d401800d56501c908036141c030a455039140c1c2040c00000f03402da040074440c4400000c0301c10621404101d114859442035403050020707070310181d09403041e81043e2012a929030040b000e40c400144400d01900e071590075942d41c0840795001041c0040c548900b27030700440c0610442d50310440143c0706003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 596998696 1250 596997446 596997463
    0x40f020a06050307051204140f0601170604210203130315050c0a0c2009010b0409050115080103170c032d0a09210c170c04050112020d080913020c 64
    0xa0519600f54030f40104007a05500c10360012541c0c48515200007002c201074551000d10242528040715503240760b07401040d6544000b80220460841e210114030342c1c1c140c002a516100700e40c8198107400d03104901e6141109600e081400d0f105601052255203c15441040d5100c0118050801a000c2c0d050360500b25046803c094101d1700000e108001c810245504608004400c41e44100060300c00180d104820a014180241007a4010280400000c860340020041e00907901c3e10401004a079903205018112004c68040403004a0000001000800c07542040300c1c1703141c040e610300c0b01e203000d1a07001300754151303800300300a01d10003003040d642c10b10a011146201c01c06801026013551910301c401201400d221920b11a0303000c1d00c80d44001610400901040514589074000e2401d440580c881e00802c07006604402c24140c10322440065484030f14250140a04031100d02c3c0303140000c000107070240013910b1148002900c005030104040e1020b615202e21203000460124001a29084104056418075600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 596999946 1250 596998696 596998709
    0x10c0807050304020904020d020a330806150c0109081912051e27061b0406080621031314030601060504050913020d030503161d0d0f0209040f020a 64
    0x344104001038441417940d0303400c190100d0703e5401d604500e100080040001c2d41120b01310002001c160703440441003000004200002038107148284e070301100c04132030081303048509641c802e0018507500352500d0703c1c90040c2244900078002044040030f40e154400720f94000200c91402d1410702c1d000d20031003a48030040030008000506d09200b9402e000111344408900c40030040c8003450000c0204d280000c030301c81d403c2845059911170b400d0300c1039940301003130b21450112000d80104460194000111202c40c3c03c8a043d106140c0754181691114818482102900c2152400c02c500c198840c00724200104080c29524614030142218030b82042c16040c2c04c44803011505000e0f038451001406680c0c1c01a00351401d48d54169200922035481d0390321030b007100101d6000030f908100949201c406069114000310b00c1000c07011000da00340c000790b0208031402000444405072603144102c860606180002c0182d219a000e9000e80101a495400141c002e0401b40e40407035241581185081c00c50600c070550b0b0303000700345 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 597001196 1250 596999946 596999957
    0x50c0d031e1d0f010e04090c0620031e071a1602010204030c0312120c05040320010206060f0a090f0e12040f06120e0307032106120803090f060702010c0807 68
    0x1c6040e03002c020554440e155902c240103090b600091079109200c0305d03c1c03407500104184a0b006140c00c000881c6100c3d406440005907220100701c151401003110200302d40d40c007100071454811110a18035440749144d880d248607210401c80701c40031442c00030030300031080c0c404c1090071050b080c1361511080c5030141107018400e42e40180070410110301c9400703500b42220340150120703441c8140d82d4422034140044418900d40640b07891032540171194840c2c080d1056030722604102c0040d0440a1148817200e00d0001d0031401a800311001a0250400c9071801d0034091000d8004108a41c9515091054a1001015050440d0b03102c00501c14010301308424103c003a5104030280c074003401c01c0e8800088004601401041c458030000c3d80342c48040aa0003210140c0c4000e040c0d90b244c03182850300600d803003002011800c00f043c0781800c1c0c02001215200d81022200c0c040c4144084000960b80d8a1082e040141050264007401104900078601404824841e0420b60700000303010101c1140900f0144000e04030303408016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 597002446 1250 597001196 597001217
    0x90606030703020a1403121c060501210f0e031b0607030c1d01090b0f0702010311270a121406010e01051c050a05030d09020a0e04120804050c0d031e 65
    0x2103c645404c0243d520540c0c8181c40d0034005c0010a203025031940e1000c001400008003242c0c0160906500054a980390708240032140e81c5200454200d41108510320101000420000b9004206d900034000300300c2d08280420703c8101150481c2c05d58102e44481102c1035aa103042c010750b8001480700c0c130742c800101d05082040e40305103080102150102215410b020001104030b101d160300502403c4010504110840d6440d00075003003441803900445012404a070902c0c00604040d8030000c2907400510000c00110601805007603504d00000310800f02c950003000307915000c52901d0209030980100ca01500d0340360100c6d008a0180c80c54032038143c0c000111400d1a00041c810b6a0368000700362803043c20560303040004c00c1c4904241d414011200c0e001070051200240d60011070040d0740000d18910300803904050352036502c28100340000340803600185560f404094508510340207800700c9800c64018001c03607014141e401e01040101a2080c0180c0c00314a070301504092203400c0e441403021300b01c40c0b450802e1421 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 597003696 1250 597002446 597002449
    0x1b01110a05030609040c0317191d041802030609012705071815060801080c010903110402071412131202130e03120c0c12070f0b1302030a0b09060603070302 68
    0x24080600121301c101d11110105081c000782e0544103020350340041090031800c88019400b881031784041031821342c11000401c1900f6181c011203030034047d4926012000003217401c810401000b0900078903032100340e034500d68511002d618108401c5100744155000024418603180200100c20356000760405842e800784200000680701041a10407280c1500e6800f83d0000e00c0c44018001d0034001e00d800c10181c0703110720005130b200d900c5080d45040310701e00c60039161002544070045903400b00c5400041c12060b1203416204c140e0500d07070300070580c02c1e00038565a0200c41c0d4401d6103500341a4501c092880b80760010851900da807400c0310141009111418503801d1880b03485d804240b880784591900c0c3c1103159503001d4240002070074811105442c5021509062030301d0540da070203010380c01155580d015449180054080320403c1d03012680c00640141007404210416aa0043c0c0380342c0080120100e0070601060300016103081101e941400d10520800034949009003490346040c1000f885584254060308040025 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 597004946 1250 597003696 597003707
    0x9010b0901080c0705030d05040b090106080304050603040c1a0a030506040b0f01033b0618031c180807050c0f060a05091f02101503020a18111b01110a 66
    0x80314401e0804039915600c40310080214052040054000d0100155090804541d1340c0710f6842a031050719400010381320003a000d03088400394003402c0195031080009104a2800002031680584640241881c00303854408855114145c05200b00d4200004219407032442d0b018018140c4c0700d04140c4040041c103a2000016100d1300030f07041214145640c43c1d03201c003110004690041040c1c021000c403000a0f40e442c0000d1802c3c107611400004460254202003001c00302411785c0510051103103c01581415808009010528401040351242543d100301141c844104448040ca040d800b82112603120080c2d0304201d42055101c11015104401c030f455030101c0c0e5907561080d50320003103003071421940741d01204000c00d40a6101040341c192001503800c0050348140d000072283c00080da10380080c082900c45c03c0780c544a030812400000e502401010b0140920000c4089000700707140030610126103000786441d40c05641d032040f20000311440500242c0c5000450074000c0c0d9018882c01c550ba18640300f2111401840b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 597006196 1250 597004946 597004957
    0x105040605011e33020d0822150605040510030303050a0b09180109061a010e300708070e06030f0c090a020726130f0b0403061d03190f0f090e0a0917070c0509010b 71
    0x127045081d500c03620810403503000b500549001ba10811141c10700100d4008003520b50b00c41100004e0901c80010020310844c082c01c01c1058000d00381c1003031a143c4004284407022021a204c44542d603031490900440c200340100304104029a941c031992203400800181100e640302145801030b50a80703014007042806541440d01e081d03c0302c811345c4d0070a803254040b40c00c0c105282c2c0054103602c03c0f031201003600c04107041220300500d402c40032201c0c50304000184d261100c141d008510341c0490300700001380108580307400400702144118800700740807800240041c000c0b0807042105002080101e41d10854051a1403805c02030030002c40b84107502e506c0c1c02a500d1403803107580070083c0407580364441c00004007854100392440c0d48a05060300c0d194017200500703070b10000a04059400043e00c98102c1091140180341c40385c4002800e940300000703d41886107801c400340e4090000120b280d41d40e4050004941180f081c0e446000e01403144a42d030b4007040c107005d20300100e0703600520b02c1001801d00400020001600f20350 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 597007446 1250 597006196 597006203
    0x7020d030506150d0209190605040e060a030b040f020907050c0307060b040603050a030809160e0609100506130e01090606050706090503070f050105040605011e33020d0822 75
    0x7490340d20400811800e00d84408400c02441000c41e941003203804c1c1c1e030060000c15000341d800810090454044020f6030000d0301c149004200100000d0148031041d541603640310001030845041c507a501e0342c81c010419070171181078869410004800c3e04601e0f2010721641c000e503032440c000f800c01d400d491209071a441000c10040000341d84111402c43e41c0c84503080341d0b0003144c1100c00e8a030001803900740a0100c0e0b0301107940600e070340240c11a1554624030705030480d04ad210b0921408100365564001d0200240c0c0c00742150b00d060340b00030400917036a51100c004282420a208440885a241140e94403035580d043c0c024141076801c0140c10b00486520030300f80e402c000d41020010036650414100a801e62085003809400120342a0402c03051000540003e8041d030700c04c0d4001c100301c1e80d990303000c02da01ca100c4820040300d40030300039020040080c940d020b001082e5600a0b0038014521032060415264400190110241c0c00038004480d5580d0401d42086d0307c03c1498048420380340341008002500c0b10301500c002c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 597008696 1250 597007446 597007451
    0x408090a080604141c120f1415030d0804140a0204020a05090102060906072708010501030309140301060501091e0510030c021c020307080d020d0c0908070609050a2c0f0415020307020d03 81
    0x80080c030020340001c0c2c071780400003008008c0c00380092040001c3c1c8130103c5803490015403416181c0d03a281070004601300c4c01e510315510003d443e2202e035900d4202e00c500c600c68040c40d1062488040150f52948005c0a51702d07016100d45651381c05107030000e4102400100401c0c01c640010003001811504142d100742c4058100140c11007005094940c65480b47c03603500b00322040d40c43c0800210406402210314001d6450700824503940c040e0040415090b1211800380c2030004036460310803c100001d14002d000a20407550700402c2003921180440c4981c50a074445500082d02c0340d030f40c8102c4c55010b002c0f100c1440800b1162800d515141d48003e0355030b100f0505c000f800d0fa400000d00c403c03d200698103407000d040f01700b5000d001008070444020310f842c607036020300e000c0c42c05400e00c0090254051324042e4122440a80412507481c94161540c078040c0809032000d1540c0c14404001e014070724174003015841a4403600d107500c0141010708201025210041c1180b10309031040003801300c0381d0380000703104440c0d00051802 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 597009946 1250 597008696 597008717
    0x30b0102160e0a0e0d0f0318060f05390711031603350d1401030c060201060b0702030309040c02100c030204050415030c030b0408090a080604141c 64
    0x403841c00010079080c40800e1446207010507144052400325008840003402407062040342c3d003456032100b4a040c0180302089400400c5c541c850b00039041002d030f01c00541c084640711a4152640f0042e5621204401d0905940328100310b810020168541007404842c00041c8117044511898040c04032880040c0c0d560000101c1c0d54820070101124516003110040c06544200f42000032003080050540000c80e40e400c0c043e035600e00d010705000204681d9004221a2083c0c240b003003840c0303442907032014401e07242654560102c21180450307900d1060082d40314010f4000ca25203055002400c45015800c0100040030402007100565400400d6907000386003260f001440e20002c2100b6450500d0010f8020012400c00481882454150307015000326041903c0610604100340003803200c465250100401156107850f0174404184201c0c0740301d6020748079140c000d2403c00c686000500c1c480c0d0360743c00100c06a00080802c02000100034000e034505800c0380003040e006941c2c0c12406501da10003204401001100d901 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 597011196 1250 597009946 597009949
    0x120120090a0f031a1906080604060b10140c010f021b15010e0105100306152a03050403230a08040504180b1b131e060c0b0705030c090315060a080c0d03030b 68
    0x200c5400402103c01b00710360384c2d440100944804040341c0603200c82d071902c07000c0e001905240e80c8910044455580701160704405070440c00d9a80c2007a451a8070030f6586504c410400d20840c8000c8c860b500101c0c100403900d400603029140303002c60500e4021000110503004200501202014505440003101d01440c2484403800440081945078060311300010b280300052f003e40d421120402714640c0d041c0d100300d030030700c40d038800c9070012a8004401000140d08100400202d4414400c40180b05000e284500741c2ca06202d10071072510030182425a000440050104540c1c58144200f0180c0104c40312820f0170314603241c59500c4039850082c11401c1c02946900640d115a42d0b03102110850320b903d0815042c02034aa0000e1114120301c001d800089405511340802c11900419401001503806000b0401554a43d442215a6000900301554082c82884154002d550503c8509a40d0344840f002043c50320300001048070104280c0e01c800f505421602c20b41c841ca440f107a43e00781000350141804900c1a0b910750 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 597012446 1250 597011196 597011221
    0x11d1c02100e10050c0904391103030703140f150405060402070f0b0105030c0613030201030903050c2b0c050309040218090106080411010e010e120120090a0f031a 71
    0x1d101e1003d080c0b07080f0410a41c1002e40d03001c0c1c2011401954104400503003440890740403c03803072805200c0c0320003252843d403440302d040c410306207180514174000043e0b40140c15a64910f40060301d0110100341ca5521000c4040c480b145a03035030100400304040304504003c0145500c400c5000511800345032981d000440c1615290100c450072a8003a03401c0c0020b10312400c1c6044001000c0c01054424040d20502c1d0086241943c20340700072820340003c040b50340d861580154000d00c2d24000c02c40c1404030600c210281c1c3c03102405408001e19040c080041d02640c1c090041c040080000c101c1d40034850300910301360203e5800019110a620140c4006070341e150060350180c0640e4609008070f034080006000403400c00c2d4401d20040c004d5201d0342d1404030002c549001540c503145076a0065001820162b0404898078111180140c0e04003244d00008480b101c146a0440145103290b0b52152560005a48086814120301c00c1000381030071052112071505556542d401d1655014400801c00ca200c03010821145540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 597013696 1250 597012446 597012463
    0x32e03021c1b030503070b0601050702090109090f150207110102030a051209031e1c050f04110d0c060e181e15030601030b040b0f1b0714011d1c02100e 66
    0x15203a02c115943d0380740072552688040e030112030500442000c120b041d4007510540d184143c0c010b1a805c0c80340c0c00c1c811030710010940c3eaa81170381d010004030340c000c0116104109030035012482540240e629413007400c080c10015030700202c0c28115442000512940e581c0241959050140d0780d15a40807911001d40003403645c0524590101100079003202c04000380c00b08401030011560100784a0511080e40603488102c94088500701940c060800c002400100104104194524020f020209c800b54545502003079600981007040030032403102c1c10054a10305801191008152529441c5151404c980343d00490030203600300c10386681031000400c100c4c100c2150b02030003084000d4100e445c07075a541d0030b0003501c10700305540c01ea820030700580105602005100714030307100301070f05650300f00407403c0340d100007115500c05c00d42601c1e04a00312076011079912080c0a9101c012040725140c81c501c5444281560500382d9000003e031400c020741c501d40382900d8010070301f00310b0303001b203100009400580fa0b04014180b2024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 597014946 1250 597013696 597013733
    0x141905090a020a090b0f03090d09060e04020304051006030605010807090b0a0303140d0507051315080c09011404031511121501030912020109031b05030f0d020f032e03021c 75
    0x100721b000d040380d02a00a1441402c1000480342603011072070301074450b04050301031a80000c1c943c070740411042c10150019074000b84503c085400801c5c035010040120740d8a500210b40042c0c55200400c81c0c10020000713030011b4401e01c0d40070004c45070588006600c49035188030040a001e20f10708501c2d807400d41401941e40c500b0143d4004e1155191100e00200658011481a040c0a4144070080303040d0054101e083c1103c041d80c1c44024a43c0c13100c8032005a241c12440e0414100711020740741d0300ca8102280040c00085110348282c190310b00c503070007580781603403100e0b03801a1b4160310a00c240d05000e042c0400481e0003095004075400300808c03050040303002c1c0c20503140151901071000c840340c014590550107021001e0003a0f9403080c9550401d162120f0000c01240040c2540c0d0042c003031510001d01e4200205050700070040010300e44008241c40303203100e030011102c03403e051600804c4001001120725981040c945813050070581a0300b19400500590761b42d500068140701407203408420404480c10390301d4a10300b07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 597016196 1250 597014946 597014969
    0x16030e10060503070e07120e0f010c08010905070e1302030402040f02192714030106030210090303030609021213020f040515130501050306040215070804141905090a020a09 75
    0x5103014044094402881018000d00c5201c0000941900101809000d180f15036603028a141407101c0442c06424058610760f00d0b0300610101c1c18642c0002d00c5154203c14031901e9034019589050320107821204001d2000c428482e050980c020540e842c001c259101802007200140c698513140003140040c95000ca40000d0b0510009101c4042c050310b032a8003022828681d102c1c3e980340090605e40e13484042c9603a0100561031812010301a00b4148649616070442c042d0000980030381d2a000102d03150358002020010882d01e0800740141945030013960007400c0081001d51820164515001c02944006c6c4030041400c583c0f6004011592510100850140d0003041800703107041c201e201180c0040c80301001c41c41040c401c10000701f02c07001c50094034100e1f0001000380040341c2d0307a5000d10550040c030b099041003201c800c1001078006002c0b1ba0281000e0900c2c806000c000d0300c50041070045001900c010402e400c500c1c2101080746907180d2103803591026176044090380f0380d2000b180c107482c2c201460b00034500c0e520 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 597017446 1250 597016196 597016213
    0x130b0a0509062a010c08070c150f02040515040b0304020418050d0536012303090601090e030316030e010902030708030c07240c0c170c030d031416030e 66
    0xa03464001c8402c6200000c0354000c01d4601c0d02105405c81ea880700c0e00310042003001001400540c001c1707034115000742c09401d80041902a0107480000c854000d200c102681d0350101d002d119506007260345164036000014000c0c602800c1c0b071440c130154000204003c0c46180c0391881062440d441440b10307841941d0110441d02076019481018020350003c007101c5840a1060303009581130804050f211400300303041e00c003d0402d0380182c001143c0b2180c81002801480e4032071009408420380d90300003507205100200180000e541010011000e48046444541507640f0034418804d82c140b6145104503000910b080000341c100f03040751010301400c1c01c804040c0d8075000300200005c0c03a0318040001c3c62000d900000352000e090316401e40c648140707038000c04d22086200f410754081902c0e0048416039840340c041d02c0c50124841d51001061036041e07043d5000175441c0c2001c450083e072070400304400c00c2c101060b8203082c02034030440e4400205440c0300606a002d02914009104915802a44a0358500c18004242c03241c66 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 597018696 1250 597017446 597017467
    0x130b1309020a03060e0c04050a03080307110304030c0302010905220b12010e030403020a05060f0a0c06020d090809090c0405011d0f1c1e020916090e012702130b0a050906 74
    0xb03159a00ca0301282180c2c48000440141c0039101300c2d01074908c0249800b441d80d041d511b0b0341c107040d000240000248550001001d8011504102910066110704240300209013548001070403030419500043c01510308200814246001c0d1070300340ea02118592001420503550300c0003545200411182400741d52801c0341036500d0b440301000800a0303038001d0b0b0320401d40581e030b081440140c0c421100d200203030701010f000801040f8491103540005900903080503007425102d120010840f4040b400c12a648403002445103030310304040690030f038403e410300240c0342001c1c80d10002034429859031034441e10189840b445030580c3d03900c90348142c2407560040c0c120802c00030b2900011205000b11002650310041e01071b51010161110360304119416400713091103c030358880080815079050908011000d01c030078054007081d00800031800340d000340041c8450042c641c000340b001114021146c0c0003420a03600400102007007104059901c3d044448031424266900e0074038104484602641010350384c484c600040801d0398 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 597019946 1250 597018696 597018701
    0xe010c02060d06050f030a0309150905100c1109090c0114120a0204051806150304051504150b0414010506070302070b1309060b1c05130212060a0c05130b1309020a03 72
    0x1340c8206a0b00b1410f0554070301c081507903c0c1c11402000f0b00007101c401e418040000412803150a1055604000c24455107980024000c0300c42c0d0022000040c4082c0b01e14001c3c0100085014142c1400f614040c0c1c090400501280e1224020b98140303043c000d03845c3d0030b013041340640011260f100c56002c0b04400107007020320160010394410321406104200c02c60002100421481e1440d00a038001010406000c1e4007204120b0f807600020400d4540e4061441710700d0841e03d81c036040398400c510070100480c07d1900d240e81c21040711302c80c40809018902d40106420360b01100c200c8141580c004660468954665103400ca203043c006400010a21030b022900d034050701c4190455206403100b29030103024164469200c181140206038481d0181883d04c030622603001c3c202e51255800400c40b008200e60b01280760080b50a0811800c881c7d245944000c04010007100e55103e81512000306140882c034120304001490b002e0308040c00f5400c0e820b000082ea41c0a070a40c0c482c800402005c036200c0a54039494602d030040e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 597021196 1250 597019946 597019949
    0x30d060501020c030607050a030c030207050d0c1401061d1003020d150c0512040f05030d0c110606030106061d0d12050304030e0a1d0411040e030711010f0f0e010c02060d06 75
    0xb6216040701c0700716501e000320b00d40b445000309070380300c600f41080c0365005c030080c041c4141c4c01c50926500b00581001f060003031050b90102e912940780da150004091800a0600c400c60008018507490104140007405018444258201101030605d50588445910302c400110f02d034030003075005503003072050410815910306641c0704d0010260104801100c140c001c8d642c91003210140080c0c0b112000000d40011207521410185034051000c40341031124000e6040708440e9400140700124002c0105144071103010800641e0210701a4024414241791010150045040c01d80780e041d01102d41d812150a07803100b40d000c40c980d42e04009480e200440c3d541d0082e019600c144e41c03d6000601d038602801d52428031100040c12141c140c014030764501407020300c03101031210140049035003011000803405160f4490180310314140000000c0d5640f02200e241c03ca41d00803454003458103010604400c1c10b2107076006a0241c150440c82e0922064032032102c0c0c01229503072480301c8025400000030864040305205072b4070200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 597022446 1250 597021196 597021199
    0x90703050c040501050a29031003020301110a08040b0c0d05010306270308060120030c2503020a0b070503090907020c01110601030f1e12030b0f0603060f21030d0605 72
    0x880c265890701c20300c4140d420034040c042d0001c90b0001d0800440703c110314034840d4a000074440003100824074281d0182e0b6407085c1d070016005a401032090096240030310030542c01801407445280380404120014060040007007010b01505c12103030010b41303a900110115210100401c00c200a42e60f141c1c40d01c0c1c00140080040003801e0800000c1c1c0702c0b54440900500c64034650941c030340c2901959a00300440300c0003144582c0041d03850311110750030044101000600280d02407103024045417904102211079181008410040a4403c407000b0030260302c031880820b090705e05140004d6520841800c25520318031429039070310340092001c402c0000d02c503404254208108001d03030311061300c0d6211800140e60b8490a000140110300503000000c009103440c0c403050162902c126004030340d00b0b040d40742c484400391285d4904010a0311a51800c045103003204284605887c1100c1042c1141042d40c040341c00b8502945080740601040900820440106070300c2065600c140d200700da40d10030b00340c0c4030100540424412903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 597023696 1250 597022446 597022453
    0x270310020f04140603130803060109030c030b0703110a1e0e030604060e0c0607080d0b270f0601080415090201031d1b030109150902061303030e09010605040b040b18040509070305 78
    0x6607031314008040b0317401100000d091302c410640a8540d04030a42c005401c0c1c906104c070110000001807920b200440095014140142c49858a180c010301541c1083c150f0780b501d03140800c4422122500040100c00007071100146c6042c26000070340a03240b040c458522181e01d88a00d070300301b00c1002140d4000c54000ca40c02e800b50f0b030342c44540c030342072010074000c1100040c060001400210307209009544601034900c0002c0075844021440c1d0082ca882205020301c0010060403035081100581050110f10380200c820f00e0f02003030925294031400c11948440c00360400c43ca0701c0701190300c00c1d6032094100c40c8555540c24051a03010f000750480c255102c4403050b9041807a184000011100d2506120317403c07889801c603802ca01c0030025948290000e09a825040b40d008a044c40403900b2410f8040c2d00c40043c500c65182d40144040f01c03030070482d000f10705078418402c00c441004140030401c20b0350b0582e000c40703c0d0a09055201c0c2d400201a54422024080311500549444100038015000003000011a4001e0307083c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 597024946 1250 597023696 597023729
    0xc0a0c09050106090515040506030906040309060e060409020307030b04050c0409201c0609020f0307081f38071502041202010809010207020d050c01020f03270310020f04 74
    0x4541555801d110301400306104e000200801d0500c3d8480d5921300c0302841c100c44c9130686807000241250815074401303159610460400007095041f8034884050503103420640c0c0f0812684001a04030b01c507074044c4690050700400450f040700c1c0a0b4000c130b071811100800510281c94200000380c0135405c42d2085850260818100c2002001c2c60028141000404440986090080704100e08018000766192180c0b903600c0c2d100140028031440602005001d00710310940d6414842c000500d0a040903007801e0030001c1d45002101e0300022a02d40e18102c03501360710074100c0501e04074070a00d142450104154a281240380445480c40300e440e00400816104d2070b0400d403e020100743d9030781203009500881045d0032030403a8640c003640c041c15406902418200c005850308a59078080340345010311500c120f945074407072010b8208540e0144500100044407100a40c2440105200b00065080100d80c01f00510545012009142c500303005150441d01d04d864250341e248100001000c8a0344103108100d00f00c908000f4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 597026196 1250 597024946 597024959
    0x30201020912100f2f0408150a0f05070f08060f0d0501060f15020c041104240912030801090b01090b0a0509030606010c020306060f06041a0d0f020a080121080c0a0c 72
    0x900c1c004048480045446a071040404c5d032459017414100c8508940501000412035000c011803001c02401c4101c034034403400c00011410545a000d090109114200400c0081c85544488191000314951038042d5958070340202240020342c4c407032076158002c450300301c03014103100d0150461005c48451580d80035903a5030725084809400031144017680160450070f54207005241c182c010303070554141c5d8855a89001d03a21107000e050b09441000312440c001030606054011500700b4440f5008000c44c0f900c02945a12607540103196070700c14000c850710141e64051074807450b40700d0041c0c10003900003607000c0d641c1c551403010054601d801c00304070039110b4800c0710001102940f240400c05441c46e800750003482c01d91100e00401c824074040030940c0b80c00c40c03024000001c41496481c0180d0342c00c01040e40017503075011141c0394541501d1030b2500c0c200c02c66004000c091500382e4088500fa0441d00c180c4013610403408800051000802e480303101903c00030022614040b40c10000c296403221764455810301050725501c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 597027446 1250 597026196 597026201
    0x602090f090610030e07051309030212040f031506080d08090105130c0308160c1e121a0403020f010516020d080702070b160f1a0c180409030201020912100f 68
    0x110101d0b0082c00041c040f4480c40e0198012140d10311100055500c840d4031070380440c808041444e0313034040b0b4640307030440e0109058051103400000480d01006c286041d050418042180c0c8043c4801892440020081e52107071016a0080b40a041c1c26401d8807002d0041680041a40d8402ea514030f0f0507510349008540c010480720146103c1c030f913010303212400c021316503210302c980c0e034025288000ca8401e40501c0c500008414080480280c101000c40c03038000e5080d00f1130258078644030f801c00d880c803081404200700402d01d03080074652603070622401c00006c3c1e0b039075140482c240b00316905542100e42c00c040601c0302c07a55504043c03a0f0421426422a01c0b0807032801c0e01215841c80555400d400750304243c405126416000005107400230b451080306c9124031b69070381c500311020b90080c402c0d2600180c800c1e031030301581800500c0e00e400c022480e282a06009502d10240407000005103250300c510383e920000400c141c001e40590300f00c1c150040c07440482000c0c048000d0b0b11030b130365141c1c4480042d26003141f1030031140451 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 597028696 1250 597027446 597027451
    0x3010303110f030c0c060a03090506010e09010b1203070b07052b0b0301051e07170906090607090b0a030209040b22150303140703050f03010810060f080303070c0204020906070602090f09 81
    0x1358001d00c20b1207991385c284400c85d484259004209030b00e071a11403022840c104881c1c1e0091150340e43e02c03c010f04d04101c04c14215000301e113070103214042154540c403003000e0010540d00d0498028040c641503481d569410388940c401c00caa410303051001010700c505908060402c440000b08408400d014100c0704008050032034500701e40044c80c0322800c200304410030401c075207404d911407443d0804030784080300e0024680003580c040714012010b40c04a010440240410310440d6042100c5041c2142c0341805c1c21417122550103201492800c02d81d0110b494041540c41e90085105078401803c4450000d910113607140343c08640c0f500c074075811401c1c8a492021600003280e401d048070342503510b84200e41c8000803076244c25030107a80306904210050114256480c07001e0015030003054550000c100c800002a81607083c0c40b0b140d03005000c503070100c074010010b60030088201e940c030505500d84007805001610003e0000d0042b038005035046000890034800f007242960040c020400b0480c2c00b102420400c00400075001c004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 597029946 1250 597028696 597028717
    0x92301090b0a091119020c061303050f1501210c090b030c0109120803060d0209071d0a0303051b1501060504031b030305090d060e12030103060c090b09120a020603010303110f03 77
    0x400402c600024120f910300d05c020381e10300c1034400d454001d20003c2c9554000155000b514020301d00100204a4208260703441c622426011f00300c1a0384244080e03116480c1482100104141e501c441c01c4030390342c2c1c400d158244e04e03071003450f0740c250b1521501c4d020010309850700a41d0003449040c80d0004c1d51760180550204440e11504040c038034040a0b51160700d01d41014001300e07042070124400d4001680e8204a02c0d1148001e940c03078801c035000d02c543da80240046102554040c2e0710801050011983c000116011000485221015607041014051410a1070001121420f2110700041091a4841c1c018021280941103201456002910032100308031988070050200303204000c4151241440103850700414000c113800161580c0c4000c4950038034041e01e0040d1001140040148208249445000c011406030300d403035000181801c22511082c407640140b00e20a41ca0a0760034541e4100070812111030660140c44e45172a56520b10b0081d01c450506044c8040e45e016070002401100c100006440500b81d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 597031196 1250 597029946 597029981
    0xa360312111009050102070602070f02031b090412020f0f010c090902091806060f04090915090f142404061803020a030311190e030c19092301090b0a09 66
    0x200b02203004000c040c40841242c0554007881801c02203041880900034050040c0b21a0703c1c2d402c401e01c10581001d04540721072014410501c0820801e40750ba500640d407003540026080030300078805100f40d180a02c3d012400c10f21b840b6958400b418101c041d0000340c1038400585450b00d120780c0311051141a80031f00c0220715006201c0d5000440c3c0316800c0c0c45026008040a00090b2400110540d2807441c0d51082e0402d004254556400c40100505d02d040340041841e0354400700190441961810080407260390081c080b01c8402e00d6022400341c042c804105c0c40e560f8100601c1810121b50844aa0103030202c0d010340b80a441e00d6880d268100e01e160440b804181e00d40d0240c107184500340e800381c0007460005115107e4007403e00c500030700440020b2030075419220740d4680c250a090b280f410145400540c5400f1402090032205001c40a41c0c91420181590304036400494000700144244800403c102003500242400000005004d0703c4d0754820280c100055604000450325988100141d0703003e840d01100400c1e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 597032446 1250 597031196 597031213
    0x106090518060f1002011e06080c0120010f1401120512030a0b060a080a0f02090f0904050a050106060c050105090d0e01120f0626010509030a36031211 66
    0x88007580403584034a00502203d80c1a0705030300461400d044100540740581e558250b072900149855241c943c1c2d003000f00b01d051280714140103900e03032504811203ea034103000386034200c2c40c5851070482401c0323006500b01000300900c8921028441c05000c9108005050010341d0001261800c0c010070b0107100c5580001c0240004600004500d080782d1008180404241c1e07505078131420f55075418002c055945259a80f000700307080a01c00c800c12075400d08070b014205841040103464680301e10001440c0130001b22540d115a0b0348a0500c2c5003080554800100b055182a10118540d034000c400000154002e9008101c60764900503c6a5a05c1103042281c01003440110601c000d50711408403d207458025602c0843c144181d2a2a9019203555400240b500001c6012000180c84403800d800513070001e5800a02003414014580b60700c82c400d00e0451005c003c3d000480b12051600e0310400300c0f840303410251000c1021092204203481d1001800101c44110746000b50000305da110710940b00c80b1600c007101410700f24 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 597033696 1250 597032446 597032479
    0x90d0c0b19080c0a0207051e040903050306010e04060e0118110c0708060c0a3507050d0c0e0603040204110f0a080a1a010917070e0c0405010f080f0c030406091407030b01060905 77
    0x60000c41480c4402040048d4072a030f00351160700441c901c0d248241c9440352a801e003600094404c3c0f010044040c021840c045042043e10180e80f00103044a2145e8038604a0304070050b0220040c04420340c8507044280c0001d4407c500300f60001d401e4044611410030303034450342c0304d02541c2e12261060440520006000c02a070031010300780919074030b60840700300c940d000120034084a800c072615000ca401a02142e0007040096140d544d502070fa08140c6c071a45000c0a01240381c5000035114000580068080d541c0c3c0c1156801c3c1810950403035a4510b00c01f1046070302c070079400c00020045d030000c5030412081414111031080000c0c13200c0388003010400585819040a04041c90040420000303e0a00058881e11800040c5444a54425409407002d44042d0381c1e51810580054050564100d054081010450070000c126100041309034004100369082c55894030395007800b030041d010500c0080d0005803014803000e105030b00041d00c2d404891107058200d203540e90b1414240e034509418450b05070400f08001c0e030380300d02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 597034946 1250 597033696 597033709
    0x6010c050a110631080a0309090b03010b2d0409080a0309150903050903061609060e0303121906060806031002130308070305040315020906090d0c0b19080c0a020705 72
    0x1030b03007015110f40e041411000590003810303008804d03001903101122540782c0322005a1158000b4004a41c02803900394000d942c018078020142c413804114551383c8400e81d10750b40d400e40115000b1580101012841d099150050380c4000680785081c410700e00281c0750b40c00328101030140c2c4802a40142d11036080500440054000d4088000e045406d88940401700f1014a5076205440c8014042c0ea64541c88603401020b061800d0302c098030845841c2c0171911a043d075554018092019200b0340d10f000b030ba00c4004240400d2860241f00000c0038004e050b0701c00c001c1064100001d0586000014005020017a910a000e441c1020282c8546426400061090000d03880039001000040540d54510320116925210340003e1382101f0350480000d400003c0810038045864502c4801d103003104011460082030100041043c42025051405004644114428001a01c0d8507400801480c18450f43d140a24075000321161030300d010040c041020440851502c107540410b5440840c80d580041c4605410513041285 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 597036196 1250 597034946 597034973
    0xe160f0e06030a0605060c0a15051b0f04081b011b050304170a0501090503120108070b270a15021218042f031b07032001020403060e031206010c050a 65
    0xa085490f000001001c0e201c2d28002e20004a40c7d41c05010641d21034030b0552820302504200f41d034401e06010a1003032003010304080401060000c0c0d0119640d100c00e001745001d500036a4068100b900030540e8a9000c0c0da200c0006441e02e01c0243d85036007850600e141886403030415200b000d0180c0e4010701083c469458040351008440c1840c00456040e05c0c076556034a800e460f0074610490351a04003054120b18025480905805018401c02030303c141804d04201208a01031200c1d40d48507043c02010340010b002020f00e2070500988081e050398042c03522030707071001c590011070314581d0014404d0948410000d6810740c00d03203002d46150410142c07458405030030800980801104558113512120f100301030441040b078506032010055070115220318062178104012a040310b0071907004101006030f040080d44c040c1e40560f031010104400940b60b000c1040315402809103400044c5564a40340c204020b0a0002010307101412089000c0c060350f5480e8801107a1841d1200d42c0186603a0000440c84005005081d03e6075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 597037446 1250 597036196 597036211
    0x1303320a0315030501090c080703050c06090609120d141309091416030c0609060c0b101d0f0c040810050603030904051e070212220b040e160f0e0603 65
    0x10240b01152a285501c002c0b60b0040301d0b560b42d10310681c010004041c641e8801442400082e2005629503140e1035159440b01d100c0e075120b0440050904459591003080d204d100001a0500b05090403403008990358400344551500494042c0860346d201841807011907041404000281c81010b16240f0100b0141c90700301d00490b00c124603011244d200e1002004500c4030010300c008030304501461418110b0100c503ca41151003009030f007107000e0041c260082c41d854115907000005001d5961541d80e00103032008560031154121000012004821848500c0103000703408040404141f83c8801c05524030a21440c800c2500a80000b0714034040110580c0c00303164842c4000c0e02307032464181e50200080c1110b80480f480500e0500c00580794074100704191400e940010300b800140038100f002403248805000307030500203054040a0f1400102102d908000d00010404d194855031160745550306e11481010072600c9041e16018a4000004079214016800c402e045a4480c48581401c20081c0540d0750700003000306 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 597038696 1250 597037446 597037451
    0xc0a0b06040f020f0a09050306070c0f0f05120c011503050c130e010504060912180504020904060b07030c0b151008280b04060902070510090213051303320a03 69
    0x2d051809a43c0010021041c1c1c00b034195a468011503000707080c404c602e420050080d070000e001c02882607000105a1080ca070041601c95140c0d60034500100c8005c0d440c50001e0003030150200030140742100320041c03e8070704030350002400200345c0342500c80d41c071204600c8042c00550001d050b40986041006000700200034a80010030340c0308904c850307142591400d171003c81c3da01e40e642680c041400312540c10791194a441d40350201105010b00100710f907503091402801e200b15030000340c2c0d040e50781c1ca035840761004049418045840324060304001d051025910030580c0c5180102c000101624911880b02c81074000007810000140071005084a036250010b000d00c1300c0e91030240d002c419514103000001070380b9800000104101d8800c1041c401920b80982c020800b0350b005112110010f00c010806802c0b4030a4140c0007d03c50550f130000419980810400404091401041c000d0103480b4482c4000528000e89031160000c06002c03006203045031500f00400e505504440d80349941c10004020100d03e82c82d450003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 597039946 1250 597038696 597038711
    0xf0b0f01180f083306100e0904080d140103081c06080f1f0b01020a020621040803040201030501210609080d2a0e01080c031f0b0c120c0a0b0604 63
    0x1440507500d02d507002541568090084010300300882c0100070002c02e048003030380a10baa90740c50301c030145003800b4050a2045202182c1d178010580b0410702e080f003445006050344070b141418285409580d00840c03408a400e814040741101c280e0560b10914103d80e40200d18a107080e1000c2050380201c0822404480a1030f03d8280000b8034007400c202c020880c41c50354010701b0861045140801001c0d2984190a0f038031402c02d82d40c0040c9a8000c00d41c100c00c1074064820580d507822403200044c009501e00c02c50f4000601850500040c44541c002070751140c0d1003030300c00308104e90702c4555501255074446030750301c0090004030030240060000c2d0081e1158070f1040080f02e040504203400c18066400510450816500c3c11144400030500400488207036020381c100f845210441c900001d05454004003a22101d030400000f24511384000c8000b29810b0b40049801842180c6880d04c0c0e1505a10518044c04d0700d00c104040401d031618a5021214101485402041760050342d40d10894140c41c0144072a0344103581d40301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 597041196 1250 597039946 597039959
    0x3030415030b0a06020c062a03070302030403031418060a0e031c030522120c0507090e01150803030a1e0504050d020d02012705010902180a0f0b0f0118 66
    0x324484403030440d2404100400104107005041d0600d600880855000301c50f4040346480d401f0803109001d580d01c03901d018862648409064011a883d004200c1c3d210002d00078082c903602001030410340e031003a903a0550802e00101e40b1401c5024510300004541c0016581030440e20f04180240428000d81c00c00c01c80001011000070b04041c07158818070004005002040040c56051184544c041d8021036082c0c4070120815541e202c3c100c024000404955000c030404024034061850307101d003650b0101c1282c041c00e4a5000000141862004003100c079820007a00c001c40640e00c24510342503034840c000a50075030b5281c9400310003402945070b01801140e5070361508903030f4910034000e03e0b1040780140010903025085541c005d00d458841c58a0300116450161044031426440320711506080000400c902504480e080c0180100040c2400943c403004219520040440850b00785109911141c02040300801420b03d00c02522124480306520612004d645803035980a107107041601c01c01c458084242640302d65 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 597042446 1250 597041196 597041219
    0x18090302160f050f040912030209031e031b0606031b06090603010905090717070608101212020d0e060906030a1d0a051c08043003231303030209030304 66
    0x4000000b00b1168810500a81c1408001c60603c04010b42e42041004500d803500240c0340042c5a086080540024000009507402c200018081b411034082c400030710310540358555698001c3d005c0d9160b0000d81c21000310354a1001c101da6114110140c081c24168141e02c40e0700701d40c3c4489101b4540d100500780521750164441001550180107103c100203040d007050b5075803034508049907108203601e66484d0403050035100081100b05c1210200e02f40020300b9210317510840d0f140100307074000460100ca4420000d0500207c485110286a06030702540c446044280048518070104040e00ba003001d003c0007041d070541003000066600c031100d010001000307089001100f040324103040f00d8100e241d100c040c51009202c0b0900c03001290794000ba04c000c4c45251888000380c181d007401040a840340090500002100d604008070103061000b0300e2469582082e00e02c009070007019902510805031042d201444005100083c065000b02841d020810707900a1580d01200a50311400045800d07001c18007000800100301c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 597043696 1250 597042446 597042449
    0xf09011107030c1e0201120b01020106090504060506100206090d1110090309210b07030207030c0813260c06032208121e150103090b0c031f1809030216 66
    0x2035551907075264880c2084648401e070070700000100c404200e01c4e10010b0384c0069005415060503540800ca01c05a140141d005054641c4256211b6043c00100300800849034809c0c1d01c07581c0c0480d0820ba50800c01542260355641c01c0700c101865a00c00c5815040042c01384112801902803102226100c280e00480801130703414400045022030402d810500600401c0030200003144440446005400c249440d90122030002034141801c1c907500280240915105050740103206030001c101590381c0540740314074945031646115441015120b00721596210b11040041901101d44000403d5101142d10800c4030607071000c0c1c21440c1c0c00c900c80129070742da10a1031a104080e40e0140740390f40d485403101605081c25003c0205940400b030400301e10341522021914041d0340081840d0180075000024500690091240c004c000e4254100c0700d0030030200300c2c2d204c4001d6106110f80303540314004a504031001c69004805004882d68030051460502040043e0b91190348480c0c06031045598001c0600300f040c001d02480e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 597044946 1250 597043696 597043703
    0x3b030a080403091a07080d090b1510030203161404080106060806010e030d1d0d020409150e1902060307050f0c010f0e0a050c060c0a120e03160506030f09011107 70
    0xa00308802d250300820301c08000c05070341c060600c0c001401152030280e480b6406005045030740129188070032024543c080c0500b10b600c0006d5401906040001541d49c2c0c011803005403041d000410050f010f98440d0080da4020600c07002c003081865940881070b29982c1d0501c103071000480c424440010440c1302400b425006000326194100340c0d00b0810b000424151040a4190003940300c0107142d0600d950002c41c20700e088403015081050340c2c0090f000517903010196030b0041d40c064105500790003481084c40e05d14825502010042210503d0303908007039250003a0b000c1c210040000c90300e104001d400c0c414020b47d400702643c0340c41d524000340030540d011160403103060801c0320380d541d0072120302c401c44034426030a80c1000c0c1002031002c2c01d01c0c0c0e540e05580d40584d0344804e004200100e45c6012820042011040309a4030049003c0c20703c03955030b0010812440d000000d4803a00c1404091500d02404000d82e00a5650190000c4d16560f9801c4ad0031180c2d00010380301d030032103648c1c907540310004010020240c00c02920 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 597046196 1250 597044946 597044957
    0x3010503010b010c0b0a201b15091509010b0d050a0c06110c060d0204050a180605060306060301030b040218181605101d030102040f05090a3b030a 64
    0x40805150849002d00c46a6050001d01c6101c0b0b40801d42412890341d011010003008910100080c000000d00c4200f80c201020165000c608440c80b0311900700d00003048640d841c00c8034160301c40c0d039420081c1c448094806e07040541104030441054bc0f201c49406502c849844008640351a15401160b102d0601110070780389038014485010401c41c00c0e40701d03540103048520300b00c40800c04070861281c6a980703020340288211000a0b10296150003501510300074031008000c1aa2207a1b1494011103c600d080030300e1080b245081000b05540c90040b00380ca0250101030a03032402c5a0a55444044030040604140d90281d880310401024000c1164454801c0b030b0200c0380c1d9882c44510794015883e11484627100c0c0943c108035031040c402615000341010324100301d45410000900141a200f503451662100d482c0c055000290100700151003402400880d1000d8444550306e6481d80916012540030400300c0c2c80e85016030001940101100d40c0103040d1000e48141c0c00103042c010700c18140f03036a2018400c60701103203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 597047446 1250 597046196 597046199
    0x804081c06090e01050705090103200d060e010f060e040b190f05010f030920010507060c03050114090603060606090a0e011403060907122009041b090c14210a020301 72
    0x2c000780294480c402903600280020f0a080e40090030031300544204c02c1c10035a035000e1081400c2c2e2a6031481829921228050f540d0b10815000d482c044c12076130190545c002205000041c0c005010a101c90460710f40d56102c032020240740c002c11000d80111402c2691002000003501410f19000c03013071078020501c04104041c200c0c90100090400380c00300e4a041e0a040c907206640000c0303030040e2103901120040c000f200d20422030000050b1014042c41a020308014900340e021400c040d00360744024140d070300c0421981440b000354020081c104e0310440340c09800d508141d02060403030074420043e0039007480050445801c03688440c040806400d099000703040103501001655054101840f0b541c0e08a9001d5000d8620302e0f00b82410303000c4d40150400c0c01800255400c8060f0450074146254000807100201010410300302824005a40c01400035085150810900001030b161000c1c81049a4084549c0300c1060340341c0c039600e49903440c2e04842c0d5201126101048124914406000e005104102130100103880c0d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 597048696 1250 597047446 597047459
    0x5010201061a04090f021c05010602070e28021c0f050c03070507030804030302040504050108060603060106050301050a172e0506030d170402040e10061419060804081c06 74
    0x151200d42c0882c242400460048000c1104603040b101601c0304c0707840c0898520101c07001d21001744184142c80024141c0c3d444d001d0a004030503000369040751165030844003603584a161402c04083c003640c240307044000760188003a0030203855101214141803e000141010b200074800004400b00c510030617111581c4840e07510344100d161144c180c001f003180b108542149004080500903201c1c0100c040c0030f20005d980000e003007612a40441e805003070043c02c240311650391100032541e1540d050f52014880c0c09118004224a44100142da0407250018504089245054083c940c2d0031003040a01c0031a0103200c805948071504c0720042c2c20301c3d030800c904940c00309150782c50317007070817200f01030105031080c1c20080c550a8840d070b20100090004058019101c26620740348001002002c074142d41400700d0140c80c0f2070120100715644450120b44e11800000c8000d403210040000402e52132040360042c039106201802928400d101c90341e88182f00e245250f00c0c003003144915581143c0241d12040415494200900c0b14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 597049946 1250 597048696 597048701
    0x301060f08090d0e06030c040503010f02040302030c0d0b010b070f0c060807180302090402150d050c03071803080f130e010b07060b01030902010801053109020f010215041e02130605010201 82
    0x8100300050081541c6443c401030014000c04800d0340728043c003002041e00b4489980442e00100303001002004480085103540c8041e410501c4160300c07034000e0711181c030b841f0304220f030041c4800c0ba84081c00f00d10356070a000e460030954010710004e40704901648001800a0381c0c0c0c94040001d8038135500c8102007840c0481e40101400d212f40c4d11040c050240990400c016292034010f13940003641203444a11500b8410001c504070302549000e03040313250600701800250800000150300880456a0f078490b01111443c5031260500644401840c1034400c10020203140483d42c05403458081c03000b1004841f40d610b0201694010080e0042500700740d0000d80d010420045101d41005100207007000d110a8019800182903410140b00701b6000c0c14514590355500300707201401c0004088220300c41c40c2c0040407500304100030205d4080c100d0045101c000b2402c019070001648010086991050103019551580c41d201c00c505011102c0031341c2c407034002d13644005945602000308070403540c003400034002c2c0ca800002800e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 597051196 1250 597049946 597049951
    0x105060a0609060203030c092b02150a080615160b061318020f03010e071205160315022a0a0606090506010e0d1a010305030301062304050f0d05030301060f08 69
    0x14818070000c00c000711134020054075803000100b096144c0300e603d110042411a920045020351740070402003420040b14407d4580f0200300c0c0242c5800307106c840e0300c2c02d160b0402e1050070035440204640c0070001d4002d01e050400f01c0c0740440344480082c1000d107406401d04820404990855044003488108800b0303007000e9004ea4091030351900300f808180c1545d519034540108006000c2d00800e1260704800075600d00f5000010340404040489079025a40c800b5a42da0041030300044405004030a80c0201c904090060941502d40051786c4031548500b0b403188000a60111040740510300c8a01c0e034002d405140d0441e14074442d08043c014100c9011186021811204160030140346d0700d2a00003441203e903400300b0041c1c1c1d00c03502a80c0f1103045000e03e05001800302c041e400920700010609001104001000c0f01860403034469480b07400c0c100554403201100440c0c034030449050204144420880b03880c05100441c1580f001900b051041140d0f03458050566000340c008101203045d914200341d80550002d142507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 597052446 1250 597051196 597051209
    0x1060e040b10080a060e0903090406080105010812070501090210080a0506190b0f0d02071a13210512073504030f02100903020c010e18010306020307021009050105060a 73
    0x1194401c03100000d008030080540d036504000e9000001201c0d40300e1940208060700032060140000d00e818040c0310703607076488030040e540a1401d24100040c013003014000c0b18181c405030b1020313004600002c0203002c0309403c260320a585540d00e0303c1c002000b40e260b0110800030303900d0030743d05c49000e45006400365090300c1020b0161402071910448000c6901002c103450002d40b095040308a40e20a1004000d94090240c5d95a80326400e00c0092600e04000d09445c2401c40610140745601030399071550341501540e14200e001822034650410400248005045a0301c074030b5441d81800c60400412852001d4404c00446131003010030800b0f0803024540d4924209040c4c5680c40d10304c0f00380c007084094030400700283c02900090a0005480000c00b07051300038000c0c2d641020030050704028403034442c20300a5a0390a040741090100e0381030300100d40c860515001005c4010350402424080382d29564580c002540014079600440c040c0303c120004000090050462147c010000414941803460400c48418035507440701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 597053696 1250 597052446 597052451
    0xe0a060509011409010b0c0c1e12191211060a291305130803040f0b010902040b070b0601030f060909021201020307270f06050a0e04020405030307060f061d01060e04 72
    0x1030f55503030f5003d00d182d06441020440f80d81361700c000420285094002e4000540c03148003c10b040d103007042380d4402405401c0c2d08403010902c00810041c0c13186c964001c048004004001215504041585170f1001c0700c0c420814a80340c819424000c0b02c0a0403c2000c1d990141040d4031818145030814100001c0f0b10134181c1da511072520b0709140030000e00081c410401041c0031070340300c1c40000c0440004400d04400d9680081406540e0314092030541c080c8554180100c4000b0810030012440940500c00d607815288403200f080c0ca406c00305d4a0300f60b40444000c00c5a4105078070f9150940c9045a1402001e0090180100c04104c11743d82e07204001c8803100c1c203514031445a01c10310420840e2544030514031001040c0768001000f0048409a606111406070044070b40c803085400b0010341581c1c41002007032440390f5592944007840c200c00c1000b050f44154030401e039041c1c1c8148017010100e0400e50000c04115003500c0d000801560340c084218114542481c4050b44104d4900100400b43d0000e190001c00c2e901203030b08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 597054946 1250 597053696 597053729
    0x318060306061c0902030106060f08100e04020409110a060306170102030f01030b0c0d05040b180a020a06052b091a0f0a050402041805060603070e0f0c130e0a06050901 73
    0x11641501540f45004082064400c44030200b90184e801101d034603130060020b00c070150702ea10001d41000307225110080003800d00400141d080c04000703002002e580d80603500701d8a5480725020040a44850a000d0b43e00924500c8020340b41e50f200088040140240e46000c9007007441d220030000e011100100f0100664010002c0010200100881030b0550360b1104900c2d0003521001c2c000e0081f8010400350f109002e03d814103110034401c40619007440780250321204461011141d0f58192642c03031041009404c20103014060010900480243c607405445120314141e078141e03140d00350a50303100d181844000980e01c101245c14001c800c101290740d02e8003010000043d0034400c111010b40a80140007040543d5542c0100c2d0031551290440405a00f00e03c4100910800509000342c0361801910458030a2242c2400019940e189060040c420128042c13860025511400102081c0d0703c01c0c0440c400f1044d001e1008540c8150703940001c3d01405007980009040ca04040a01190100c107030030442c09008200c1c0c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 597056196 1250 597054946 597054949
    0x1e060115090e01121403070b06130b2101140a0603060b0603070f0c0f0f0b0114010e01020a170f220f0819260705060c0405030601060e031e0318060306 66
    0x280b40d8110380e58413500043c00c02031401e0141c18003640d20f0070289103010002d1841c050141020040d4007607602140c3c4115101900d9030758404951041c06c0d0250404141a0704400c0e13441156000044070740781000100b090b418001080701c0d03030030007202d0a21900c0d5442c072041c014401144201e228440d0b05a40307039455800c0030003000e050000c1c041c0c5888200311100e001c4804010840411815841d407190300c030102c680c00c81c40d0001ca00d00090150364000850f00d004801c96601c02c4141c4486580103030050014121241c80c1c62010092051044444100812220044018800c01403441c062448000e03184c086110072000400c5809030b20000b0b110125541c144010040424401c5880b602c000b00440e16040520b4100c860319004110801850075420011025001030001802e040d07220b07005486850b5282008054031303004038011540c0540c403040050140c20301a403942d616024000300ac90300145e441d81201e200e03085039115180300381d4001040b104082c0721341c0381c0b00450000741280d045080d403420b0030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 597057446 1250 597056196 597056219
    0x91103041110090e0411060a021c03020a1d181e09120409050a0e030406020a0606090e0c0907030b030304120b06010903050d05160803151807020d030b031e06011509 72
    0x1444c0601d008407022400b0400710241e0360f100c1c0b08024000382d07251010594065222510381303585000c404180c9403280050f80c443d200f01d8502d506141c41d40764800e4010400404d5048444440b99042018a9000f0344400d24201c2c0451082240d05104019000c081c05001c034174201c05004003203e9406445400c503640816402c2d141030f41c080880005142c1e940126440150031044d80012a5000004020803842d90218415003480d006070030500180313640c0d07a03844c001c0302c5a02e54540c5080d0410602568286094042c02d904201d8a10b40810b160070940c00190039039100e90301c02d2180d01d050004600400003c001d020364450701c00d0078200001c82c55a181c090303d66556607100005c025000900340c505400d007a100300d60441d00801c2040c0c40f46010300e19040c807401c0b100840303031080744044448910450002c1c00c01d4451480c2d0b40c094160040c040300280e014103070300b240c40d65250040e1260070250000310382c0c5021203182c00310700500f159450203e02003892401c1525030401c00100000901c00700342c100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 597058696 1250 597057446 597057449
    0x40e1b120406090f0c06181e03080c030d020c01020a030e06193c0516051602060405040903081603090209010b0a0c0506150307060e010806010e0a09110304111009 71
    0x2d600420403d050380342190001d01004d40c002e113034010000010440355440444258008813100300684910f0b110280c40b99912008008840d41c541001c8090000030ba0706c1025111416946089a06000c845170b201803d907001469441c0103694041070f045c0c046913140c0545d4901188075000f0f002d03982400404042c2d01e4010360320004c40b990b1554041030100f0424030010b0941480002807002c42842440c0f8900b0384d152900e040840c507801e000c08610700c09040345220b441e405058503514601038a00725000c0b070981c0319540c183c2c0d10003400c0c0300000e0152254058118101d1091f40c641c941e925002c00c80c09608521504c489040502d0400c0c60401626904d1b50305064500d070386001502c41c07000c80310844d00c0e8000c036200140b0b5409210180b21160b000c030b000301c200f00c803021030990300c0361034645408503413540da406c0c035840c0040d50141c0803501950054990750300601e40503000e04882070b1642c2105056401106d404000d080c0004200024007410168501c0780c14001c071803103006051840c40061001046 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 597059946 1250 597058696 597058703
    0x30f0d0c1b061e0e0a060506060906030106030b010306050d030203030405250330021c08101202010c12020c01030516050702060f040306050c120912041404020405030102040e1b1204 79
    0x141e42c803c0c11080d05256030120030901d11a01444851a03403110142c481a03146001c490756410100455190315004050b1044030002a081a080d07a01e0103100710080c01e4400034140c1499900d08021490307483d400d100c840c80a02a07001566681024582285031800d0a940084102a00720600c42a4481c0d00f05000440340c000407246a40d1000b07803d141c140c07101c068000070840141041e9140c1c502e40200e924038142041c02c10b5019140501d41007903e9001c400c4400701951000058244901c03144c86504101320b41c010314201400260a80d9202c00034030001c3e050302d0140c0d0108045421547c0d01d40035140c3d11280b41d90440d41d0030000e281d03001e01070380034006000344298400300b10740c04000c0702c0209440081d60405000c6c0003e003441d900c5105039900c051100d211140003a000501c01b401d00086840c0c0da00c1c400394013245040d00d00b0310000b850300c2c16071800e00d1303009808120004030b542d003d00103000502001031441c5010301348013020500300b45800350322400801d014030801d103161003200c4e0000d0f0700641 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 597061196 1250 597059946 597059951
    0x1203020c0a080309040e010b0a091506050309060a23250207050904120c05120a0f020102031b1605011a0109060c0b0c0f040e04030c020108010603060e04020d0305040503030f0d0c1b06 80
    0xc01d00d0386c040c050800140a2a04003c0310100003603c0501500020705540b03640c0710100e4001d4542c0421101407008a4035115130f5840440820b48042c0d01d40d100441c000700d9504410071030546405103050100c4191602c0340c1c0e504c440d54402c40301e4984030030000c0c0d290381180000c0401901e0080800c852220023480a04079228194180103024000e00300c001d42a940102500c0c60a0034003060a541ca0704900100f900244a4080e41803945d0700520031030b4019172007080c64441070304181501ca1131a81c485082c00304100c900a1540d00042c40134081c001c08004160201e0700389423915000108a003880350302210400c50312040200c00700c0d881c1d03404030350016a00c400042d9a540e00b041e602c4e4092040d42d01006a610044040105169002c602c009901d03100340e032040c00ca6607880404405a8850b800f4003c2c8026101002c200140741c0301078aa60294424117005060070f503140b00080c110b41118405101800d070014400501d105940704440240039241010b800788200c00007441c03180e114a0100600c0281d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 597062446 1250 597061196 597061211
    0xc0c0b0c0c0a0f06090f0503100e030c0a0c051305040308160e0a0e0402040623040e0a0605040b01181e0902130c0c0c0f030206090123041203020c0a08030904 69
    0x242441500d10194000e40650195607030f07607a000052076090b04c5a03100041450300d0210340c09152200a0382215001401000e00304600d14600d8010030000c0300c0081148420000300380c6010052080c81050760041040380600d42c41c05082c01071550040b0010b1101525180c100310029400804480d0443d60b0071840c44812080302809948209860180c1d41d80b01c0c1e000c000c0020068441c8003440c0c4103620039102448400d584850541d0280740c00410b800700b01c40040036420315810281d21211442406900312441a582515000c007140c0c029181920340210303000045c0f0078034003c0c0c01040e04c0980c00010070000c910030000f4150140300c40a005a02c2251030b8550101555140c1180c0340303404462000c01c100c0f50070324540c0a0419511700d2812107400010300d0001881041500304a012a034010381580c0c5800d0200004640c084800400c000c04102340c00e480d5031a1941c3c810240000c0c004480920020070072904004c1c0c507000840c0d000d588200892101400740d0400441038440300c4200340c50105005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 597063696 1250 597062446 597062467
    0xc0b040807060204031518050d031503080316020d09080a12021f1e06050310051b0a021e0f0a081b03130501030b030307031b020f0d0303050f06010c0c0b 67
    0x140301c0c4240c003030300b41800868040305129a2000b000c4913051001d108003c411702c0c6101041403841501c070b000c2d003542c1156041416490203508002681700d142c42c0903803900d03a141e030741300442030b0000d60344004039a100c1490300403140e40401044004140a0800364100c0c3c0c07802480550b1842c6032900204030701d03c0b00181c510b580d4000c1202000101a10401c4c0c203110304004001c00082c8130100100203843ca0b008060158400c4070300c203080981b08040c000d00540c4510a000401034038020f03041c3e140744110a9080041e043c2400054003402400d070b070150440d10000b65904000d2104441c16891039005040ba80741ca0f6040007031844001544001142d031111595411980e0ba40204121208280000100401d000902e415602d0030f0760400d172002c22074a01020285070b40c9004180c07005010072000200745d418104401030748180e043c401012010440c60650208103000324204044001c0303526503080c00b01c808504003441d40d0114007071a282c0082401c80c0c540c0814420684104407050500050601c00e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 597064946 1250 597063696 597063713
    0x30e0402070803151309030203040e040507050603010605130509060d11030f010c2601060804030507020a030807150c020f120d060e0c04080111040b09040c12230903030402010c0b04 79
    0x141e401a021540b6460950f0092801508072a0060b102c1c0180921545c05902d061080b68003c980640c012740c10142099486212803c014206464521036400c5c002020b9403248021030180540d507640603201d4261583c0301901c0c0c1c0c919045240300d243d40004000143c1c440309000e00a0380d82004010403c04070000c08203092905507500f0111035401d01d515085400c0d08607520305010f02180c00f0f1828091902d0b00300e0003e081d001c0c083c00e4002180c003004600801e100c3c80241c00707101c2c0000c0c8000030442d81ca0341c44109a9000301c104890200c00c592100384d601e1490300c20b0200016150000c0d00e0703001403443c046a07d0310400714903d0940800801e030110a0103c0764809000781105203404c0c0600d040c025400340070ba82080c840c41c0110343c280320742c0c0328042c8501400d80e82258030f002c00590822107644100405008009106030400030301c2508100d41c050140643c2d00b40080b003011a500c10b01c140002d868500300003e1030043c10744d0041081c000181d0b48040e0704070344a0341002c1070744250b4459140a502 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 597066196 1250 597064946 597064957
    0x1606091113021b19020603190f06080f0604030801091802040518060109062111040c030f20040b0913091a37180503040906120f030e0402 60
    0x41041000e41110840e920070b900410141c0c07000040103409400c45a41603a44002c1d10b024415034454400c20722006061600240d81c020130b00101a0002c01c0c071f081840c40865100d00e180a02c041d85410742088401b01c14040100ca00b005c0d600134041500e0f2a40700904a25010f00c11000c115039502c4802801500940600c800c0c658001c2040c400ca0134035200e0304d8504503180c0307017079040380c06844c0c00080e00342c3d19841101c0c11980c62030707401c120300700204100f1407901084c0c0d8402d0b02d00654605031440c1a541c0c0e40b20303500c074900e01e6403000580c04103050300070b10803207940c4040c42c80714042d24564100304e2903140c17041d46c00b2101e1003052169a5200d0701c1c0401d005d90055402003003501e08107a0070360304021040c1c00e455035680781141c01001d50359031b2080117446012441804101d01420944014020680d04228980022400e0700440c4100a00d96122800e40000c58203903880c0c0c0000c0740130301202017580204001031121001401016130031340c44051890700d01090003000d11003106880c214580300d50301501e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 597067446 1250 597066196 597066199
    0xc0308160c050f0d0e18070806010e0405090a060f02040e04080a0903050d210203060612040309150302131e0e1306051801060b030c070f020a050307060f0e0616060911 73
    0x3440031030120b459558031050342013400301042500c160303440c050902075105004060314a01d210000d0304d881c10103542030100071b82004d04120308000441d090380c0b0350307014842c0540e54510040c0450083c0342895030864005d85090340c5110700400c000c0106d051007101d02c9401ca070304210000d5a440d9114419034030304203968002809400340748207428220743c20901014804400b0000740000c2822044e40308100d2104540c0c10340d10103020301001e01080b5420442d5030740140300707052022155071610404425070b40d5501c0c2c2a00080c0e0001450007a040ca210541c2e4000d01c50b109001d05060650f0360404804299030140032010180c00740040c0c1d00a1202000c44d00e401e8000c0020441c2d030900401c4003550880502044c0019820100001010315044088902c15101c2d0304500e414100301d5610103e01440703004060740c0c00700103018003052940d800e10603c80200020f0312075103046108406c01403c604040d406c5a88140018004801509083c0345210551a403242c0c001603454480e10300103861140b0ba1040c00e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 597068696 1250 597067446 597067453
    0x30615032e0801060915090b040908220503011b12020d06030f050c151c0204030215120106020c030d0e0301290316030f0209060105120405061005010c0308160c05 71
    0x1001c00e41c40034400c0d106494800d4000e21609440d150103005903200d02d401d200c020307a0100340810540c03000e9401400003c500510200d02400035880752000c9800000e90755042c0386440450382c0078000003445040c01080c05a0007406080000224114445054000712041c429421114035203440c0c0790381214070039050030000300902038481c148150710242001d0101c1d06031007540018203540c644029000c03440e507202d001c6a45030545105140c0c80e800d003184a0a40e195400744070100050f43c40890b01140300c100c100d001a03c03200300d0043d1802440041c1c2c400c13420b54110101c4800b007a2004244480842024203145244081c4000407078010401a0416901e01c85004849118440550783c0040c80b41c5049003101c80351189080804c82002252100030080300301d03815a58018145540040e42c00ba0050405a081c00b070708452058001d04125822034150300514200200c1c8506280b681016010138a044050a2400d603030290003810f021303000228604140c0010b1030f841d44900f044d00022507002043c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 597069946 1250 597068696 597068761
    0x4060b0f181f0e0411100e130c091a1207050403080901031a09130311030a1209020f0d0c08061e0619080708100e0d0203030403030c170c0a030b030303061503 69
    0x20a03506641c50b20798806c03500141125540c0348510001486110700400010f4603520501400c001040740000450074800105400207541e036440138403c0d240c0b010400002d0741c544d20890003846d01c410041003102808403d00060010680c0346055441d10f51083c240000c0065014140c120a0040b070b048495010700400200b04811b20600d800705c00c1648280c1350b0380909800303011480d480380a0009050001000c01c4081f40c40c41c041c3e90004804280058203880c6001104000f1400342410b1324015200319290710b104000c0d060080003800d074000b0b0040141c01010440d00c1242c8601c42006d048144906d210a4405400c640103a605d00700074075624088480050703481d9140d0b0b4441201202e41c0600034900030a680d01104c020a80a030300c00b010f907001d5465a034880c6d500307800914526040000b04036090707206a51034400c8840d803a0080e0b48803070040d41c440042c4440203040d28a0020401c1c0250010b00501690b0b4450313000c4080d4600c2a042002c0c4c9954a00c0202071280b070019a9101082c2c500f07107007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 597071196 1250 597069946 597069953
    0x5040f020409110f040e030d0f0212040c060206090102040302061c24051f0f0f05070501021303230d0e01020a0b040f02030601091514061204060b0f181f0e04 69
    0x351005000300307407a2441300154100401084440341c11020425820411002d1100b844035408100c541129100041c20a1074083d1901c0030f094003207804607024140144117001c415010080c0300e51080c0000001d500c0c040c21036022504038081c00403848040242c0d4418401e075400141c02103450a205520780c8440d00640d001d1080340c0c011148a041d004042c28016029444010030322100c2940e81d5413214000001c204000725154000202c44c0c0741003010600045001440030300080c6917081c501c0c1021707440b06056051806040c900141589041050541c80110035500070070580c00441c03503030410381803d2251400507030a0a030102001815800d03520104003c110035203200d0090a8001c2d401c650071680c846484030102c03040c0c90000901c05410352020031070201000b00804101c1c00150199041c0313112464046100d41d0247c03801c4441c0c070780365020282c90782046081212140c00854010151a081082031888a00c3c05403505011440c90286007101d2050b28250300003c0c1050340d04c20710603182508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 597072446 1250 597071196 597071213
    0x1120c050414010c05060c0705120703050301030b06120705060a02011d060108061f0e0c0f0a1106061909110c0f03041a0414010804170a03090c05010203130905040f020409 75
    0x81505000714410501010f51150300071580702c951000003403900d80c0b1004c41486046d003181c10708035424406e0000c000c1d820f0310000058115140f10f0344520340c0b203504618040c0c01084000781010301880760056002c80b01d0f0800a4104100d88065a030990380c0c800010049015101015100041d0300030820030340442440045d182c0d040b074074480180d51070b07625640424403105844d8840c0e1110007401900c1405010a0040b5035a000769658601a00d007003012908040c00d40c01401010010505658080500b03100c20301407254031041c00c07124404144034035041d840050071035000e400085681c41440c94041000081220030f030002c82400c880ba0740300002c00340c507669032060145c04071004004105121590310720064600b0b640d6009a40724800c0000401114502001402583d4008003903000415a80f40c1c03c00905d1454180c0c1c0d0041002030707541c00c0c44e00d1841c43e561300c0b240c115442001340d556400c0c01c0b0519072013682c0041e400400c040e02d841c2055106911004070295029180c401c0c810100b08290 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 597073696 1250 597072446 597072449
    0x7240c1b08070905010b091822030c030201050601020d0f0e130204171605100827071e0806070c0515070306030b0603010605090a3305012d0c0201120c0504 68
    0x10101400704d83e885010100c054040e01806641120300c03404204c82400401e184507901ca40a40c000c0d05100c94007032000e0745030b1980c884055021410360308503081816070a02034250b1280080c0020a02d402140c80010300030311040c0010340c100301d84401c002015503200c285819074400304800642d2220b03124041080c008058000c40e50741c5100d030700140b40f00c00e0214a4075104407038008240c0f4030060501082554060b1004000712445101454640b00c40030300c0480664002010000130f2100d507060083e20b100c1c0841c444482d2420014040301000541e00009596610a0507454a01d540301c0e60b42c40c1c50303403501340306000082e01e0140d11810010745a60680c4181c04480c01040700007015201c4c1d0301450301701d5100f801015000305540d000204a01200d4104203110001d05484509800041802040045414603411100d09294908115969000c58004c2d420150342d00305488d584c802c65020700308402d964040b0400c1c060030200340415a80900d080c1099800f0200d41407290f02c20516004085604c02d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 597074946 1250 597073696 597073709
    0x90c07031817100903120c031d03030709050f03070614040305120a0e0627150d02040311120c10090801140108071a341407240c1b0807 59
    0xb03e9aa00600103068054083d0281d0180c980ba22070740e8030300e03440320060302d03031170403000281030720341022411b42c00c03001400c1a203005004011759241e06005e140240300e00307130a0740b145118025a0b0400c081981c1c0200d02d01c07007101c10314100b6000c030462500c078103410341c000d41c0e20241150180428082a505e031003001002903100d00e90b00c551003a400101044118010b03815090110010380603c0300c18044880f4002100c440024982c1200d01d4411081410301d900840c02030220035001701d030800c1002039000d0102c6414604490b400c060040c640e0409036584142c15043d07119950b01c5003e400524041c613b100e000d46417010003403040500c11401e20411410a20483c88140302e445d80000310780c00c151a043c84103080e0b056145140281c2164409000c0f01c20071229190882444c507074410404410a1417182079110740c01c42400c3d0a180304800d0300b08101a400401c1850803106548001e110701101e6032400045402d00100d200c19030300b0a941403d64490b100300f2882d413401d20104400c18000b07020340071201ca = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 597076196 1250 597074946 597074953
    0x1020403060506060304120f09051009090c030203041a060607060f0c11010204060509040b0301020f041e120218072a050115050d081e0703170a0605090c07031817 71
    0x110f99040c0405403108840291000e0b04070b10007084203910446020741160805d14142007482d445030001a8400b0782940d402c404a4480442000320107507600642070322012506003103043d40f40a80f1a1120300400c000300301c500140000c00a00581e4540b0180c4200542220b410820405013a0600d0300801ca500c0b81e00c00401c40080d140021301205000721003d80d080c0d60707212420801c8180c1400054803078401c08035410b540a0101c5610107d030400070b08018001da03800e0b103084508900a01c0c0040300d0603000300300d040e0404520349002d038590020f83c0d0781908035402c0d441081c1e0364000c8201c80014200b19040c040548100300c4c4154603e90048414156006500070056040c481021800603204c40c17103a2500301c0384d445c003600f0205800c6c070060700b11280b04064007480300303070010401d60032075011080440100e10030042c80510428030440c00d07540584210010404030382088000b9407010001425212440c10010344541058407a600080c1c4d5143c2054011564503140d42d0044184520304100040300d12 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 597077446 1250 597076196 597076201
    0x4060b040b03120a0309050f06070302042606132102070837020303070501021909050d0c0e0a0e0f060a0c0c0b040b0c0c061306060f0303080c03040203120c010204030605 74
    0x50003080f181d192036071640055103041c0500358281d001d05443c0e50140d550303014030b018820307010700c05210342c0b0f00c203000641e80182da0300c0c1400d0003518418071040c025141143d0031084580c0702800028025080003983d00180420212850980400160541002d14040002c103020100751b800143c250300756a600e034140ca81e0b40003000c03000c54141900a40204034400170200c42d6150401100c0d2200036240064243d0740340c600a81c5501b401e9038414007006410300381c1c01042010082c2d0002c0890007515040b02c00e520760f03220030780320210400070074002c6001c01400500840d95454180c0d03c0740000035040d03000d0740c0c010340c50250816100d581c00c90703400545605111203404041d1003205002c85c0c80f40e00c0720800105880f103844545420000508114401d84100404501c0c0c0f0310030801c5500c00c04840081d0310000c2c20386c2c540a01030702c6240c0e00807000c280403600144000b0350003a00545d44160440809038032030f9507500002e898080c050f4690f00300d040307000541954490041d0020400e403070113241c0c00d10480c3c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 597078696 1250 597077446 597077449
    0x206010605070c052b4719091112030a050f1c05130201090b0c0d120209061606050702072d03020a171903021f02070b04060b040b 57
    0x1845400e20043c0074405036a814003ca10b0a240c45040b804580d02d10440c0d80700302c940074103506008a10040e42d4280c0c02d0802d4664030b5001d85101941035945180c0954543c1c82c100c200c000d4201c0380141d0004107044080010310407580411680141d1607001000d1000c21540d050a41e010360b02c4240450040e03d08040364450002c000040f65010b01e0f1540d00c036842d211203149014460b0304600c0ca0b01083d030b0024842202c22542500526000c0c2c81403217140d0420a0041c400948101b4582d0f00140f00d403002400001c1e01e010740482c8500f00340d500f074140f0004000e1150130346e4000384140546640e0103580421b405c2540c03c40c0d440c643e41c10138414081082151a010070680c0c0d240481d21031004500d9280c066440307540b45000c0c2c43c0701103092807110340242d181c480e400102802c007660008006c0301c8040c0004200352804002c10100c100d800e4070f904a54a102d910002d45646845510b010800b40c03070b40340310140850a0303046440568012401c44001d0400b8a0044007606262240c60b101d2400d107552442c45 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 597079946 1250 597078696 597078707
    0x16060e0f190e1005100f02062410050c0105090703030f0503090c0103020906090a03110a14060d1512080901090509070e040f060e1e0c070807060203180312010602060106 74
    0x642544402040010345010b800c0050090010910154101c005000150035120404400540e05a0751980c2d009461000e00080c54224010701c9046c008020364012000340e118031101c0d85c0244000d45011141201d00a01034400c1d128220044a0540c0b800081001e4507802282a0050300d00c03a55900171494041c88045949000a40f000d00b07464004510750b40031507004c1d900a114405020b00311509000c0001d00103008420b25600a0b216210a4440da090030700c1c0118042000d04004054600380d1041c0c003004c21181e014290b1981e5415544e4070760350499104690010300113120011304107160203032502d070805654004540c52804518452408a800e180c1517807020711425055807441c0d04022a081044041e180c003103200d02c41c41d6074580700480c41d100b07495030180c030404004401e01e042e01101c1040c04100c440c000c02c5803000d4007042c00a003001a58240440c0ca00303503049000941c032030310740355102500d007000120219920f100c0003540e105611030401080c0c0c1262010340a68129aa80d11006d42d038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 597081196 1250 597079946 597079969
    0x40806090d05181c0f03030c180f15030219050d0c09060225081515030c18060a0e0f04060518030f0c0115080708060112030801060c0516060e0f 63
    0x40d1100c0f03203034031404500b4254072030382c4450031a0044105003941520341c1074a81c44401001d40002ea26031008020040d0001c1600100711803042c94144e000e07180a042540c0c0d075190740aa0840c08514800b89030506100f501928081d40c4200e0500500007070300c01b0082c2c40c40d80080401c0000c1414080d881190500401c2c0c4d010440d04c1c1c680291804040400541c9030030803000c10b104881016295000c221914104880b0360703070145c6540d80305940e04102c0d08192040ca846040039100e44d11401c82000c0d140c8032020022105000948191a0b94803105d00182c6461881e410074113044684034200110005028903082c09180200310400403a2034101c218000904074034014002980100203034650311072030500805500e0a440e00001e240303003004034081d00d088015807005585600c01e90003440102ca05004850050622001035641a2050703036001c0c00382003051148030107100f25042c4a00c10b02c01c0600101c1c3c13400c52100008118a9214100a0401c604808840e400b42030b0300c5102e4003241c140307400c3c10760 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 597082446 1250 597081196 597081217
    0x3121f050901170a0c08030a170402100c21030b24031311090103080c1c090902030403030e12180a1d100801090f060b040b1509030a0503040806090d05 66
    0x510366803c0c414003600d40c01072a80030100c03500c507800045011a03400a402c80c09020850702640c0c0d40c00303038070000610728518814a4041c100301881070000681d5100310203a10550a41400030b03548243e4109880704100c45100000c0200101a050301120381c561310660a10742c0444e810806e000400c110400d141440c2d400310b01c080340f81003000c113070348404010200034145e100b0702c088290b0041160120741c0c2400b080c0d0049419507804038140300e1510703090007014800341403124806268071601c43c005241f0f4440b4894211040d41c00000b141c1454420381019900a10080c1102c20050201181c680c5a42c09400401c66118030140000d5091400d411035008548030440ca25480071a0380920b4060414042c2100c0600e0f8807152001819030000c3c010314070a6402204c501648a00360b080ca0410789486444561080e8600b440e116110398036400001450003c401c50251035044503030100313190082d0305c1805042803101090020b4400000940c0310702c40e06602c1c09131b892064030f800094403940180301d07012 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 597083696 1250 597082446 597082459
    0xc0a061a0306190e010603080a020105010b0f040302040c0e030d0806040605120c0f120604050a0323070312021b0c120309090114010c060903030b0f0307060c030c0c0803121f05 77
    0x5a220f4084007414984038901490008941103000d039141d085580c030303520485000701c004c80c4241d940c13a028416240103000301f002da5071821409895281684c422408003d00c96950383c80349000140c81001403950091000c0d0445481e040300392000b40c00c0080407511640304e03900300440807505040007011000c0d00e50002c0001c0c2400725180c030401c0b11400780c40348969046405000942e0482c941001181d002e00d02035005451110f841d800d0007824449103402e40720791500310301070620040e261841120714043d0540761000c034564020204070041e1080300d01c030ba000d803c1001c00c0d201590801040760031040c4003c4810030304d0442c0035401e05480f03000d04003510381d2200c044001003101c800c0482d26000e50380414508074200655070340e00c5000720b911209040e00003030b540d100f0b01303642402c22189000104204800500349a0b1030044010003c00310310340001c0820a07014180c2b020000704a071810058080041079945038024403d94010b0807600310360b4052030300c0f408101d0000108182e100001501d80c060602c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 597084946 1250 597083696 597083701
    0x141c03060b04140402120c07030306060c0f0b0a06170d080a15051c0519060c0e0306072714090c0304080702060702191e0501050c030d0b13020c0a061a0306 68
    0x24444034030b07540f0100c1c3e42054007002103e51003c50ba00400b882000c05604190701c80440b420024202c0c0c40507000001440b010742e020f000464070450300302004640c484024442a580c032000000039251943c81704485104100c040145040d01013440054400c40b99600302003982c403074000800b0780e40381c1d0390654803800c1600014081820b05a8240d40906104940d024184006a4682d03143c4800d0801500303100b060380d400d140800400780100c41c0903108628100c2c0c4801c0c24100000c0d141c1e030700034111030203110350b401c09002031014000c2c2035190094134030078008410f651021291041c0c204100ca091107001c00c8000036003c03031510003d49018640120403503062107619420310056502041c0141d80c4458079180b03084420003031a0b1040080c003500c002c403440b00c8056404111812510342c0000b03041c0441801481210034000058454403074400d040450080c0403980419021041041079405260001a010b0541c0c1c2e03000070a00f09803807082c2d404201d40e80300d510885c014009030721201585900724401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 597086196 1250 597084946 597084959
    0x51629100311031623060a140d090203070b130614070803150405190e0102090105090405101208180a030b0a050a0b030102040e0114030703020904140a141c03060b04 72
    0x240784910041c00307403c55088150881e119420010b00e036104203440c040e032400403407440140d804920082c40302510b86c181840b548000c060519006514004003454002c188800701d112130b6042400d4154010301554442d03074a901d4940160360048110780f1804407a010b00241407486000b0721207204040c0e11940d418200f4a80c2c1e510f40a9202412800c1e5444e000b0140c88890b5440b4440c1a004500003401581001c122074220000c0d0381c26001150fa05034030500802041c0e98100c41100d06031502250006403503502c04412a404050540044000000c0d030b0800108202d14480201428041c14070148444200711081200d0390070303980001400c45410390041a81d00d0300e250000c0d5045827003040003103549864200404d08a0f001a0b00c011081f40c61280104407200868500f9068070308207601600d403040c21900070a02120018100601c660000b6801840500050081c030344015403110301c0400b1106188507d50380c640044041010040300c40e8000002c540c008c1c41017030f04841c1088030341d5051034600706 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 597087446 1250 597086196 597086213
    0xa0816140d090302120a0e03010e06131e05010509100b060319020d0906110a03060906031a090c030709061503090c090b0402070b07081008031c05070516291003 70
    0x800c100d00358805d45d2448281742d20518094403200d101c5070f84600ca1210302c0c0d8205802d4680040529180741c01460511216403131300250f0799100c540006481080c2801c5000700c01c0300c4080712002074103079483c00080c00280070000c54016a40b100000302400b03124800020410340784001d031200001150070031034200307007498260081e02c113140145500081c4500d00383c40b4201512040a05a0a50ba60000c0d141c060076825200d2803002c0d018603031040020b40d09545d0780302c4108a806010308101c0000400181e2880400c00c0b0001044030058151142d072507030f4070070700d0018221600035a0005a521000081e24034400c1c0303e4840b0071900a0030803401a03140000220090651400454100d42c081202c0c1000c69103110616005001f19034403541d80303117000da10310015410309070001c0c82c05800810900c95003001c820f042540284081d1400034207921058825a4031384030b8041e0700c640ba5604c0c2484101403000030440d040034401452640010001000d400c0881d101048800c0343c00c0e1231034a40e0900110342d400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 597088696 1250 597087446 597087461
    0x9030d0f0215010e0a0c0801030503040b0c03070c0906090605010e0f01140f030405070609170703240c020c040e03040f031211030c010902031b090612120a0816140d 72
    0x81c0155040c02c000d040c07440d12007250980241c5802100d0780306201552009120320f0b100f8001614014082d07504643d100303903d038421485071000400000c120381e42c1448043c4220b40446a001a1011085660761481009094107200385420b0302e01d4071000007103e500485804404100c020656515400c0a400544070291a9882c0000c02201809400c07120100040254000d9004500400c840e5107051300050061149401005d06140c00b0001050310000020b448415a0352140315030b1a186090300d0170f03008901900d42c07016581400d021502108507008110000c210001351410711100d11b060803650790ba4440c901c101c400b54a4410f5003040450340c40b80c10303a0341c188054504105107501c1c00c441c45266400c0030003485003c3e59a8242c04046107003c0102984414018001d11700580046002811402c00203000310b00510301c6a00a06543c0400d000d0703072280d610807102c15500c8181c1c50b8001010480101e65090b44090220051a1124062105090101046003000d85005e5140f0070700c201501d1007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 597089946 1250 597088696 597088727
    0xf0304121434030c080c010b0402181e0609010e0607050703051510030b061c020a1d0105030c0904080714070324050108100c0c02102309030d 62
    0x98458065031120201c0c010540800620084280c03903141d0760b800000d00d4810900180090442d00c5440300080d00621444680794104012989440340a02450b000d0400f2480c0e0581c42440002c10025107009400003c0e5404d40555400d070445074896900601d0603c030207069503000105220070000d40d8850101d40c1c0341d1300005072009081903140d9484601d04660b581044400e0342000b80a0a20301d0b0051210650200c0b0540108802a1445d01c1d204480000600348901581e030980c05c110000b043c00c4808007501e5405020a0361042cbd40e03144100040c41e2107841014000b00040000500b40780024507a01210001043d011081d03c89566003c00743d40011800c0b160004103c04030a825a018400b61004502641c8510034404c052041500081d06003020342d402c4d00c0c80c0c40c006200c1c500c1d000800340c41c5860522400503614203443e00542e5410200c0e00c0081d80030458604604080c1c0d0700440540f404119100c1c0307101d415490a00b0503055004a0410743c0e0180c1c010303801c2804007446009624000d450 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 597091196 1250 597089946 597089957
    0x70914040f02030f0108100203160c020316031209060203070b0a02072120241801020f0910080123130c020a14070503190602091017010b0f030412 64
    0x25611081c10903a0030440d4503440d02e0f220b000040088030070a0000080ca0182118218950724000100100b20030304c07208010200135440a81004548040184143c0c8034008000c4107419503992070601c0408410a000e080016090040014080c1c00081528140e0f03511000320f1200d955a040018029003004074192a07031800504aa0a9108001d0103280c0d039100650f01c449140d41c0712144054200390381542ea2546600c13200000b07149002146000c2201c08070b0304060b00e140d0b1035141d04500442600d43c1058602e520014031000004d11a43c01000300000540e0401c40b66440c0340000d076100d484c00d1040b0168400309002c2000b9011300001c0582c0e2240000b400c1030082c0101c0f4480300300700c414020312480541e01c00d0440f401030184004840018801d000010100581407a004c03944900a07803214041800b42412900108a51501607034a0608041c0c10354101120900004104418a025405029030358500100b034a42600003244c1c44603485803040303895600c4555540092800c803aa18008002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 597092446 1250 597091196 597091211
    0x120d020309070b0406050a02012019020c27010e2205120a05031f050d0201031802040e060103031725030e060a231611070510200607091404 61
    0xba003500c0504085e002a036191615200c980c00e019007110541040d02c1d0200404518002061030316008a401440d8014000545a164040c01382e180c030b08003040b0107a00c03200c001c01d074807040c080400303034900c021715100e0001c0d00c181d0b03903061601c0c00b4090980e03840102c2d41341400d17a08801030540007d086036510031411911704081051b14102c294021400d18800180000103111202c00a0141280c3c004034044a4401c29485c000008404171080e0740d0003814140c5641c0c0c0c1241015808480e0b4403280c2d000b500138004a8003d84909032a000240022400306401d40c403d07601c4002054680c0c0d11134100b50030750b8414a81604103070390a880c0e00c080c900c020140c6070802007807580c83c00e1160034050000303410301242d1429003241c221240808044d034014a03480c00c07020440280d100d03500900d500240b0b406c04910301e545d1906010f040c565203821586e00a51950344200481342e000811344041000044507400d0b11580810040d100c000a49144001409d902c00900404c8000f802040c16042c00900001c0c000b07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 597093696 1250 597092446 597092459
    0x504030201080c090d08030604050a0e1b01030603141f050609060d020d0c090614060310030b13080a02030d061409061e030604050a020a050312040b03040c120b09010e120d02030907 79
    0x118002130080306d00070008070910146003014007805401082e0580e0501800320080b43c1c1f0b5035125024074004075043c506a598111a90280d4004006543c00c2101d2080f498002540207075105190042ca000030780e0707050103490b6604072a1041a00525004203c000e050b114142088100031204070280da0100042d2600340010340d082491400400e140c2e60041102c52030300085400e00d903800b504d09400340d1020000c00c40a001c241c0020000e40781d219413040100c1e240d031201d010b40c0940f100350040c00d4040000d1000740c2030350000003421404920f05000d011141c1c454444e400c069052002d4181c0081510b0041030b035502e0320007031441c0c540e003040c00d50102401c050700009151040c240c81c240e8507500404130240540c188071034814050803099009000c018031680d6480c26501c01d61144009155010001c00c0801040c6180356000700f0700705484034495a49410603080d9400309882407078056181c4541348040300c00c0861140da543e500008081e040c01c59110743e5402a40c8000c0005c5417a00441c4400f1411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 597094946 1250 597093696 597093709
    0xc0303072303100f0b0a05031303030e0313050a050a080c011d0a0f080601140a0603020c0c040515030c090c0f090a1d0703050c070c063029010504030201080c09 70
    0xf541442414040b0503241100c2c020000036640c00c008007083d0200030500f64190810b00f01d03074000141d400302c401c0c0c030301030f40c00e00f03d0081c207400c4003c112a00000800c01d04140034445258140c56040380c4032031039241d5403410403c01482d01d200b50280d540141041000d00d40c0034521012405082000681a00c1904c600150316a00e4513048404188014041445420400c20005000d4000300a008130500c03d4980090742c940c0b4075211344001c0540010745103401c5a014001d08010000180060146080c181064000ca0b1100a5040d0081c400c0418031503507131400d1101c06001f543c030000d03540e1415200142c01c002c0f6078002ca01450300186080c40001e01c280d41408040c40142440e01280c0306070a024400605448018082c91070682050081101141030503910004840d02c508005200d4100d03802000300da00309500600e00c0200a0a41d904a0314107a130f0403070b80c8686010500c1c06248507140c282460b03010031107004c03940042d105020038801035010b0986503404c444c00d011410305004203000020308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 597096196 1250 597094946 597094951
    0x1051e09150603010b07050c190e0a110f040801140103170d0b06072a08120c0c12011b0c0b1b160c06110f1002030703060b0c03040f0b0c0303072303 65
    0x2170244005900700c00d1100c1030101d8224440e044450052841e941c5080d0300c4806210301451451000c07036008600740c0d0f041c6a114540d42500200342e143c5540500c1c2c40440c15070010b2040128950070104410b41840800c01d50f141a20303881240d200c2c03448100c2000003000d80141119030440365480b05030040c10f6485002800c03000d03100340d0001820113090341a070400940f031103108054030080154144000c19000c21b14403402000d0070340341350700c03074415210041c500345960603829040303624020700d145100010b410060f07400305400d40441d07103c040c2c2d410444109001e0b80e40038003483d42d820080b5000d1204403110740714201c0341075225030400c2d01210b0451002182d1070000c580c189001c2c3c41c2000403d801c0b2490307615580000b0b000e01122000021000c0c0c44070340c6009101050307980000018103160090b408140500b814070803503901c035030007100742650fa507006004500300a00306141c00245015410100d0703c1c440444e0f006141513445451066640b484014004190854011001070311f94095078059803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 597097446 1250 597096196 597096209
    0x5070501050a0c0e03060c04050405100e180d0e0a090e160b041e0501020c040522050610050d080a0c030e0d050c01120e0304050d0c0308031602010501051e0915060301 73
    0x2481c41d03c82c24000d060103085400d0240a034004404101070b100d00d070b00c00e0303500f11902580d010650b0b540b000d1518000709846d0f04102190b0a00c4400d101c40c400558408965000e1008210344104e40c10380c8007690408042e070100307503002400420510100c41150014540001d00030200e03501e000004482c02c07130582461b0003510a606000c00d042001f50504000318420144940c203114900d414400000c0d1544541c203c4035000d65281e40c003090441000f110030b061400c104110b030000d020002d161694580d00c0650b290105800c0400011460f460724901520099178400351583c500782e070485056072030070704240041d800d00c035602c5921002911480e005003c07540c401c101825120511400241207000421a9003561a140185030003580342d000048605583c0101e030180b000d40740c1454100038200ca15000200f1101d00442800790041d0300e61070f80031408500350024005682c807041407100000c0002c1031000e0003d82d528107a21142082c450f5150030407800d00d1616819085400840c85942c400c0c0d0051 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 597098696 1250 597097446 597097451
    0x70501022704060e0a0510030b1311030d08131b0605120f0105010e2209050303010509010b07441c020712030e0a060905061b190e0105070501050a 64
    0x491114158924404088412603042010700d04244004048020003042c1c1c11300596200081454034171600c00c7c4400540c1e000c01d04100354502031910324146903003414100c5502007209121606450301086107840040c0550b61003e0554510a845210700d110304029034079001600b40b2080358210005441d000341403240c80340791361203403007608100c00324900a103440d0414003136400521603070303901c0319010b00b59190031110000090020941c131038642a90030022016586806013034005c104001c00a941200c50889000c5c5a580c0e0b2188041031602c6000e200800b40700a280454180700d40d0000b00460201111360020041046015203020004698500d880c03a00740c08a0220108840c603803d4461400c00c00e1015410b020081e625030100841e04101d4100340343e207590549504410406c480d009090704541c05004600d80c07404c1c0030f43c0342c0d28107451803035520032244482065120304a00301c8030355249440007488400c22000b4200c800105850310181001020804040422001d011710f60007000b509100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 597099946 1250 597098696 597098737
    0x1015020a021e01091a1c0504020f0108010b030a09140d09031214070f03050708030a06150e010f0c26030a06060903080a03050c04030b0f06010305060406080a020607060207050102 78
    0x4010240c0018180b0060074540030303500b281940d030311058a030100c2d00a00a500111001446854024010303620130f80340303009403c0740048040000ba00000d01403402500c0300c20054001c00011900040b0900540c03501c4081000400c0d0034000561001c464580600b04903080384245501440c1440201e09100c4009080303000c1c28401c0c0711000c0c6001b8800300160401c0c4200c41088070642d030301401400e1020f080002c0c11103c080c02d0501400858520720391020000d543e910380100500024100350161003e08580000202181801181f030000100c1c016181c06c101e051001c078044a40d440387c03d000711b0f244007003142da000400d00e284c90858850070031910719684924042109400300e60722948207004200705c8050170400b107840388088500c507594a00c3c001c22151b98524520f940c602c560360004284503540403c0203801c0900c004258041d5100f40c0e414403e0b81c45c4d110800090318440d00412101e500800300500041c81d01d80300800101e441b400000d03003092502e40340c99089800c602e8032101c1c0707800030000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 597101196 1250 597099946 597099949
    0x4081303020604030b060907030e070611031e0a0e0303181201110d09110a05010f0f1b0623010e160210140f1308030a1a04050705090103060807030b0f1015020a02 71
    0x101c0716400120b501d0100321802418192b10b07603a5405216981c2400701c0030f045401808800d03c115400e91500c6044200c0e9005540200003041d4002c000d20f00008004c030404051030b18010003111090141e2302030007080300c440b02c000c100c1d10107043c0c4102c502540d070390504070844410312000b41c10240d00c40c0c3c000140301d29903400e026008420459410b0312a612481c2e003407095a030000641081943c1d40d11302408954003c410650741020a40b030000d0b0902c521042140030042d0941121002d032203260410142c1404000450115500030b0044420108840f0005102601042c60f0303101c01800a1040b24545002c0300850411607403421104500503403a08104210f60040c2811079030400c0305042c055085000c1030310340c00424040500350055190f1105041e550001190035020310000005104100c641800000075180741c0c04401058003103400c1402c0014400f10104403d01200e400115849a07565220031540b00d20303200401c1410951074407003021500b600c5000b1642c5207400d09070024140302d80d5500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 597102446 1250 597101196 597101209
    0x50c070605121302190906090e0303070914060f0310060e190603051b1321020d020d0204150b090118141003021c090c0510050304081303020604030b06 66
    0x100000d09001d810400e42d002181e9550425601c5074202e1501c8403210810701c0011200014030060084a046100000c10464030541c41001141c03100d81c000c10404810040043e00d07400125102c030701280048100300990091034040303043c6400001e00d400d19001a60440e5005a08180d42da51064a4095800d020080c1c02c0a54940300d1103048a020b5210382c6803210315036505495001318010191540b0200e00783c1ca1180035408003c654061805403910000c4061031031a00d203504c540050202c3d45481c20503000e0b03560102c01e0324140c001c0c02081a0a03201e400384540010741071360498002d40d4030010204c6441442c00c086010745500c3c1c4105a4038014100014241f10a003500314002518000b805c01049600f9040b00d040c080301524003030802d0940c0c2800307034000e02a106100441880700b010340710b0022402d80c0289001c900c20408204c00d10786032030a0086582a4280b1680400c0303040000c01e0110b440d49000c1c09030f48040e840010f25998036580407a0301070300242d00480304110280c05205d458070b0105c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 597103696 1250 597102446 597102449
    0x100f112710120c03092307030605090307050607050a021015090603050a1106130509040f052e0e1e07080a0f0303200d0b01050702030f1507030203092e0c050c07 70
    0x62405010303524158079407042e04640c1b40342031103000103060007030310721711100b0f020a07801181c200710100700d24036141811036140d900080b821120740c0901e4001481a80c0540c094a951140ae40d0080c40c0c0c50185246900c020409500010301c10055108001000442405000041c1d4400e101929010880c1c0c03400c8903003e021168070b20f2017118140716001070b00c00414841012034000305c0d00048251200d003006526110060409004c0d40140704c001202807113400001c088102c00d4003d041c10044590581504403084404c06d03d4041d0860403041c044044484001c480e03600d1400269084240e4520100c1d241040f4400100d4000800703e48080a140c4c041c800e40c944800d40303041c408460040b0641d24100c0e0302c5880820607100b5620342014210342d106009035888203602408490408ac010810769130390709245c421214131800d50100007070400f4401d000303903801110b2890040541d90300d000310000c590212103401c05050410301541001e4880c06000da100c0758841b40d10b40fa0399032801020a2401c082c01c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 597104946 1250 597103696 597103721
    0x40e01090204141309140601260319051b06060103050c07020307060521010b070b09151902190906090603060620030c030c100f11271012 60
    0x60004000840d084003812146940898540445010307030740101e4014007540c400078000c124200c602c0b5025032030000d81c1c0b43c180d840780b492700c1062a643e81c04a030643c50404110710801d800901c42c414081e00c0c0713245a04a101e005040c15418211540b44803618102440c0d50310f40994404c4050240359605440f4158015000303e80386468000303c0e402280c1da0351014800c4204200000400e10002c90680030035620065403124446040d59440113500160f0700159015600f000711030011803070400000549070340c4019580c42e028429070710381c000c9a07124604010040d4000380c0070080760000e0b08072403006440840c0e0503105d150080381012401420034090b5000305041c145800340c00d1203880d80080d00f80580c0d001c1c006004494020b0f8084290440c020720044650350b00c004100c040310607002061143c0e1810030500200403101a510030340f8183c5411404443c0006400c000032040141590085c40c0345014250b611001c0301006000304000050084940380060300d0911410381c404110302420300300445 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 597106196 1250 597104946 597104951
    0x30510020d0b10050304140f01020c0604020f0f0a060804170d0c020d210522050703110f0f060903070f1202040e120f0a020c0405240306040b0606090d080f040e0109 72
    0x43d03107001030810311025001909a140d01e000f00d20f00190100700d01c8001c0039582c00250344860740c0c4a151640e4280c250740c220300c685440c9600d445a41807a0090707410020000302202c90091404070141ea040101034070603560300301c034101190100b07440b4100424000790f00e484002402420391310000c3c14007021901c12010001c42100000000030400d41130092911000d100140c940c840c0c2007010140000c2c1800003c01c61080c000070310a100c00410321408403030007400d0310b0315445403000420000400900550381d00c11640d076505040b41c208140580b411000c0641160516a15401a40e00c541c0e510380c044100c1804170b880d00360460406000b8101402c0c140d0005041c1c91561045c1c85c100d83c000c805100d00c90300808a01e0b0824107108000300b0f89801030140c410851824041c100b1004504007000150300101c2c21190007400b0304000405a118030b4000c44189110b8860300b04000c0c156110b5003c1d25400900700115401144052000309070341c484031044c82e6a85c074a02950300028001c140e101401062 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 597107446 1250 597106196 597106219
    0x1090515060315010c0c0603061a0f0a0806010c38041a100308040e060a0b09010206010e13060614090702070e041b2d0927020a030510020d0b 62
    0x4440d40103483d040b00460340610400600800103c60003240030402400300c0c6150180020340075050b9000e182a580c942d08001209a0b02101440e003038443c00ca070960150504114104000f031040032110f411100c1490541c035030107819192101001c0d802d220041070b0780755411110084002c0300809045207107504908100f0303441e16440fa414200b08030450074a000c208400040c5030080c1445000c40a55031004105072600d480380302400514104a4400e0301551901401007402e0324018150345584105a004100326804d2441e01c0001c10740140003001409c0c880225140020100d0003140043d0580003111203500026400b04903814502514010039500704070341c107100c00d56086108a40c42908a0320210300c1242105006148048641c8102031814a01006000c050072540d40480c541704406550503481d900c03a80d140e41140e0035000143c28406c020b1110b0b4880164207180410341c10700081400c182281c0d2034841078100103840783c042410740c0c1d000030a00c85404842c407541000c0324060f070f0340d4040e07003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 597108696 1250 597107446 597107449
    0xc0a060b01030b0a321201140606070b060f010203040f0602010504060b0d031205040305130e0601110615010c05010207020409150c09120b092d060a1803050f0f04030b01090515 77
    0x184001240d002000301c2194080300f100c0704141030081180140c42c6d80b2200c90300309601d40c000d00b003110b004440c007203800020075940e00c1c10038203454240350410000c2031141c48440030042c403c1c80c400e04840c1035010a0000040c40c0038030011610041049400100340d61826240c60300440c0d90b003418003441140000680030200390b015403001c4003940f490342e0006140d00c1e58107081e00d00e400b4a80140b48461180e0901040c6c041020500d6030180000384c07900041410782402403911000100c0d400d400711220030b4019401c030361145115400d03142c050000145003492a4000c42c0949102c050192128651017454a828441e14402c03441c044030103142070300b411401c00b20542d1802401c0f1102800190029012501c0e1610500c20f40d81c800040c80080e1980c2440107031156482600a001e4402c1d5018100014200120302c1c0109008020007d030b8440300440c0c01da8081d607080d0080d0060b03800c40300090102da0f1070b4aa8000c0248040e502039030041c03219625191210050782d0004001c21040c411001010115 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 597109946 1250 597108696 597108719
    0x806030102071713030501020406030e19031b080d020336030a0e06090a0314070e010f0303230c010902120c01090e0a02090306150306070504080a12050c0a060b01030b0a 74
    0xa01808003c20350784c800c0300004e000e81503d900e42015006500c00039000401c940c042d8400079104601b071050350b0412041501031040542d1607034024000c154483c10f0301e822004040803640b0071074804c08800307003015034051881d8100c0c2c00845009000420880304800c07000d100315280145e5200161510410841016459860307009002002d000d0050080200700d403070b82d52809603402101c028240f44c84255136070800c200d01207004e8291013a103004845012490301000f1440905035a480030320b0a80061035907404490034040e01c040c4140c407400c0e001d48550800700e61001002551348440020511404d41c1c010440c207205000003e00150303029981c1e803811030342c0198502048400b0010441c5042d0307034022114007e031140645255040c000c441c10072a441510b42e1100391609004c0d4212070680d035903031200765220b02c04c0d40a01e0084c1c1c1e00c1620700307000003038815044581252182c500746082050400300581f5103c6401c0702200c0c525280d0b0081c80480d6131600c55071003071a20484020104c140b0700140c211a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 597111196 1250 597109946 597109973
    0x20705130e06090109020406050402070506150a0e0103050c0a1d13060b331611040b090f04030315060f0311040b1306020c040b010f11070b0c0706080603010207 70
    0x16403455018052551000c0c0d0000c82100048410b40d81d06150034100c4034001d100c04502284211300d0b00c440400c1905091023640c0c1e9041d80702000745600d45400708900c141e094a0381c3d403682d100a544c84049031204c980310aa900943c81038004004d2410020201700e4105607a4000f81c1a44c43c496081c0c164420407602429003000880944000c0500681040405016110070b00c603049034111103040000d007012142103c0d0300c007040941019000200482e02201d00c0707014016844a001c200303003000818004040840164002000015842c5c0a2004502524002c82d00c46c107048560000708000d060700740c06810403002c6000c1d515200302e070030883c015141506020261040540c1e491142541c9200301c1e0840e0041d15400c413910380c94061080c0d0400c9200018003803003005020755070039107102c1e060500070040fa411050f11103041c00754080d5030403606903120350342d20b0700d1500c2003000c0018070150700c50051a076400c4180182481509100002d069014060180c2d4026031040225001003440c0802401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 597112446 1250 597111196 597111199
    0xa0e030316020f01090f14011b12080a02090d030c1a04170f0f072103051b03070507060906050114060f0406111006060306031e0c060332061906020705 66
    0xf90403590540102c1c1e568403640c0101004d03540c501d001050301500900b001c0c0c1e912000b40c0c0c0320300d00b0904100f0302d0030202442040040c03a941c510711510103214040c60816502c002500c00050401182038009180b07000040340035000b18a050a001c0d05206803042c0e07100464440f1900c541d518100f45d62130300c10607a50402c24200c0300c980414800406238807241100c00f08681d481402d034851100c0e00301503030071042c1c0c0c00603880680c204145041125000c0d0049500c90721202909990382d012a04c21290140d1000745040704200040080b540000c0c02445003840150044000040c598144014110444400b000562203070005004410442906108450660790345140c1400422042e00d0140c3c80c1c2061004200c0c126402c00c90042080c40d0f00d03a0209003124090700000b001051249081404070860020190200c0d55060003401f984c1d0007a0020651001a60300200d102420800c1c004000c00c02c00d94000307111210741c42409043d2418115030400100000c0700c00092a02d0810080d60710342e058454203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 597113696 1250 597112446 597112459
    0x90608030307020c1908010608030327071206020405040c0809070803040509180106120308042010032d090605090111070308060316090c1101020f0703120b150a0e03031602 75
    0x1800105e4401c014200030400b00b40207110940e225100e0316129041200c0c10990800718100281e00c8100741c89111450a28040183c03420b50f01f030056440180c10240c00030b5400300d0f001c11000032561a144111180c0302c0c52aa165500e504009082c181845d000d075219501c0d43c4c7c010f20046c4501d9035010096600020300f1805030015180308160700c1e0244c0090b902045c0c1030402c1050500a0541101c200f43c49544100d80c0c661104d88001d0345003240710320826040d6009071a8092803214980641c1c460081c51080c907811031020a000f401c20320050b034880c0004100e140c5c44540e078008000e4140102030308408010001c1c032000c10783c20343c4180140103103403004d020040307110f02148080e1400e00005c94001050f0200c403000325211f14107070000d0003034820743c6000503010301203008040c40d061098038071110303400e034426240c4491518100c86141400c0c40c51141c541d44d40d000440b903a03842520b0740c1d040307a000c00480b03500c0d2400220050107a07004440750f01d01070b0b0410451030101c0d00441c0400c140b050740c1103401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 597114946 1250 597113696 597113719
    0x50609060406120914061e010f090c030608070803040806060d110910090510080d08162304080606031e10110d0504140c0409110103020f160c090608030307020c 70
    0x228004e4070a0900241c5016030308181e8507203620000c5501440b0780301e40e0890207007100e40680c0d2150121307401d01c2012007525410105000442c1246c1002d11240c40c00c0c90040341c565203540050b8280440da070b20000c01a4400101045046014850300d98400c0040303911480d682d40c141c48040f51192180c40c014031512000c0c0c000392405e0305210030076001c0d0030b000fa0200214546440000c0040c8030030f01940d490740c402c2c805204019441307101c40d58403402030700e9904000d064007c5c0094580c1411152180c411140100c11541001c0050000d48010f00e4414020700321810400709140c14404465410101000c02840c1e4100003000041c454243c130300200f0001810300034400122a060045811002500d8104001d02c400e03c00e0320428400c1c01c3c0d24603404c0d02d691440d52810001220324082005142c540d40301540120b940c0603502a00c07682c10b421459514000030784010310b0004c0320800044880300c5285205000108852003050302074500c00c00118510b00f0180c81c003a66600c5202d5505100309440c041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 597116196 1250 597114946 597114977
    0x48030a0302070f0611071103010207051b040605030f07150f1d01200604050f15240607030320070f0b04031b080304060c0305010e04030c022101050a06050609060406 72
    0x5000c0050342d0000c001700694201c074000d06045074010441502d140d4000c107598001898180308a0380020740c4040105060380c4c0c046044c100440e4400d403c950b020365640070005494900f03111850100c0024030180c920319041032100164946a0308000f42048142c41d0030041d01504040d2090074a803070401c501d01d04805600040700c8001c80720640c04442c1144054000701c07180300040c884e02071403103001520300804164155a40d0b860010141c5c4401c14244800f01d452544800c000c0281c1d00c4c01c004162103030b800f004010070313915407021600b10700082c2e490144c06a00d002c045541801101c04a101b5450110145c50703003d841c0000c00f03409481541000c1c046810180249420b1080e100c42d0011103a10441c18148080705800498003540c1c824100110441c031236209101c1c05050301c48211080010361034a46084803256805401240c015007060b0309510010441100507003502074520000c60a0f18000421100380c0300d20780d200e00e0180f030381408019015a1044240c4041d078800d0714200c21041000d40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 597117446 1250 597116196 597116213
    0x207060c080d060b1c0513020d020607082d030403050304081c0c050a020c0901030507060c030509031b0f1e0d061404060603020a0e06030a080903010248030a030207 72
    0x10000001c10380303404400601c0c10040302c090084070740d00d41401c4440341d00b0f80017120141d500846003031014204c141400303001458800304c0540d1503400641518204505079460200b40d501c11481034190800d0000c2d480043c23102e414805040340303800e801450845c206550041c1c502d02016000520045010500c000b170b01d8032340702c03da444900d400759080c0074600c01c4070030103082c6902c1192030b88018080c84650035028100400064103e0380e0081c01807102c280307021800c03941c162090340c0c01c03010000d04001101060341c0070482c5003108141c0c010790380c42c584002d00401c10f5108070107400d03a020f001030402800c0d09295162014101c18815921078550080c10b2070014000d042d0a662030000c01d4200c8180014001305174400e0041d20710a0f11a14020390b25000c4c011890071003221000e60590050046100184500b0003a21056202070000341c1007240309000030b005006800705074441e07246a0f1501c40300f0a00e07604202690039000e541c41c0047c604052400c1c41d22171080b08000383c249900000d06404002050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 597118696 1250 597117446 597117457
    0xa0f09020a0b04090b0102010b0f0f0307090906050601110c10030e0703140f01240b1305040203070e1c020906090421050c16140f060409020c01021b0703030207060c08 73
    0x34112100d080d00c0c2d000510b07094106001e0040910302e8400a50155401440340c440980c000400e0910300d00456010011b01d40714014020740c15000300e15002a8512460080034401403049a02003001e00d0003034001060103800460085d05940005000481d0707469084c601d00c41c1400c1864045500841c0c030f4540c5103008800c0e40f00418510307642100380218003000c00c0d11842d500e803010092008552024644800e0210f06030714152443c2002810421145c100001304850150380300c50a511b5035403000024120380040b034801011511201401c030291900f92460741c40401b0b91550100d844000360041703000054001c1c04a802a401c0202140078814401c07000003000444204801c04507100340001002a00031941800c641d02ca008098102c0701080000402942e04040c000c414144d03240d02080030030000f030200c2a410a50403c000f0450b0030913400100360070703a21340001590310303d90004030340080c9481001a48840e0030001061000a601041c41c0003161030301c7c13508601416090400d2400dd1040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 597119946 1250 597118696 597118699
    0x402030319030e01111e030a150e070e041104090e0c0603011d070906120f0e010203070f090b0a0c0f051903090518071b0503040e04030503010305100e03030a0f0902 72
    0x4400100140300d42c160000d41a0294010080c08107002c2c4115009a43c0600c61503000002c48031ba0703907146560004406182d200760a84400300c2c112203042081c100008150308001403481c210400c0000b1140c101402200d0108161020045981c80c05440c03d070034000ca000d4400f8441e02d0304880c00005508005070145204020041c0ba0381c0d5030b40d01980c80b036500681c0002030f1144210b0001074000c078040d0010000b120340c207448103c00401c047c0070381801881354005c0d040850340d98103124000c01ca002d1007d981b091544e03840c0e20740208440c0b500501402002d90004458190410a0050f804d50003815181c40680c840c801da540c20380940351550900070301000305000f4143d0302101e10306043e4402c062a0417500c0031f41c2c2a000310403048541800c050000c1b1000c01c041398024072500180040b00d4503142249008400703582c00c0035150031005244210a503801e9000481c0400140144281484a14002000c0c01c604000601d54181e0b256201c0c0002040003414603512080807020140f560442209680e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 597121196 1250 597119946 597119977
    0xc0d020601031110210b0a1202090a090807061104230f27042012070302150c070f08251202060c010203130b090c060d05150909030c0c060f1204020303 66
    0x200707403001e9070090000b6210703244034202960002a1407109230f100074145e9074024252090070707030b078005c444805422144011101c0b480c00308805000f191151052824200c1d0082400f0b40d01ca00d010040e100c0e110080e0b4003513180340c03010200b0b2402c698455081920b0000f06a88007503e003401841d0680c290b5506151040e450150310040100b00591981400c40c2c4400150000c03501c2d03603075402808101440c01101f4041c03540060414000752510000c1c030700500c9036010010340307442d111a5280c0c0c100980c43d848004035401d48030f002e10081800b41718418107420007074444402450181da110700c070055640b01d4102c845d14003030b06420079500e80908840340750405c00020b41d50390902a400708045143e024054910b0003000700440d40c006404620380301091401130080b41003600722440040208405001c410722188000f10740000b603103400a00f18460711b0110043c0d0f0b210f03402608140c1c2001200390398030744a49003c103c0c21070600c04c4031066403007039107031425415502d513601d1001c41d240d0b205600c1d501c01140e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 597122302 1106 597121196 597121247
    0xc0c0f1403130801060f170d0e0102070902030408030709092d06031202060a0c030c0914010e040f1d07060806090405160306020c0d020601031110 64
    0x40000162442d0244462985107401c5141d4002c0e00c1c0e82c1d4495104222800410118000030402c1c00200d00b240340b0386a5041e61104009203c103001e001c2c100103012001d03482001110050802c80c04c046580f418036091500d061f4104480800000300c0c0e8401c04501625140a900e000c20302c0382060071040020501c0003401a10f02c031803040169943c8101c00800710f04855640c0ca03403503055801400250a180e400700081e05c03d481049018141040e1078110195030121245003154411706140c0303801e00307101e1b004072100300c0900407090340a81007240c00c0480075803076849601c021400f03c1d0717101d42d52104260459105c460030310800022852100000701b450904003000ca9102c2e00c18016200390110204051001c8041c680056034180c1c0c1c00301d0010f84240702040311801c0e03503083d4002002a50f14680e14140c00510b60081d443c05034412102e881d007490701070800c241008054801035011039 = true := by decide +kernel

theorem cover : BRFrame.Cov 596942446 597122302 := by
  have h0 := BRFrame.cov_init 596942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 596942446 ≤ n) (h2 : n < 597122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
