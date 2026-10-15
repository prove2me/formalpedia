-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4922
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:10:15.605239+00:00
-- url     : https://prove2.me/submissions/b8eb4750-3637-44fa-ba61-b88fb8d8ee01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 885071942 ≤ n < 885251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 885073192 1250 885071942 885071951
    0x24040803040905010b0f1603030b10111b49020307080601080307030309020d050307050a030306120201081807050a060f091e121a070804330c020c04 65
    0x1020100e840c1c0d040740c001c1180c92414540001141c000745015980e0704003444c0d02d170b540303403403c00001c3e07410546002d1022400d2603182c0e14588210750b5661070842250b426501c8588098005064041c01d10410500704800c91003050400b06141d02c40207000e445260016040718000c000c80a40b03441c1d84105880e1750406a225010405140441954a01e0100f03100703500f12112551100b4071541c1340c903800d01a0f0b1103658028010300d00864400c0d00841a040e00203000796104400c1505c90b1415503115003000d58169000c882030104055140c03158800070404038800d114102d240b41d000034072426016085d1441000d0805034038400c01424000000101070050281c04d12607030b0b85201400c240d1294101c2d601041103010001911240011a04212095620070140c0710317060000440c0700e005940019141c507221101da6150320624031f10414054200c6440d44c454500c1e007860311443c000c845d0545e903000480620400102c10040a14004003051000c10200d994030b0510f8040b844c182403141c0080d03115051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 885074442 1250 885073192 885073199
    0x24092405070602090618100306030b161b080417060c040e06040b0307060e0414150d2901151d010f020c0603010320150d0902010324050424052404 64
    0x111b6003000b01080c41502d4400586071400c009900f250110b110141540381c0d540c000030250070007020b441d0b040c4682818200700c034919a0747d0055491541e060102c540e24000541403151003440c02d60240c1c040315100050502d8540740380b1440b1280114801c0000750089100403803619030310b0b6086440d003c2d00103421904040d643d40c400504003600c858540d801949010000c0b0716100501d44074034402c1c401418103055000c481000e1102d100c400003800d8805281e18203111710941c1c038548180d480d00740144030785491075040900c0d1782120f1825840700c0e810b11030300c2d400c4c1c016451103010711031341c4d001ca003401c1254143d102850b05074140440c02d1145a804070000001004100b0606640c80258a45809041d8503404040510a00030405070750210880014030100c2d00c0c941c1640c011044451040c58080703104902c05010503c1720101e4142e10f0045540280207204a003860300c258800481820700c0c00d004140194800c4a020700b4501503c6c0c05591071009841c5078460010b5078846c81c0800140480c1d946a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 885075692 1250 885074442 885074467
    0x60904140403030c020a0c0302120a0c0e0702071d04170d020409021801020d09270e01020714011808030c0403080309030a080c09090f10240924050706020906 69
    0x2401c40c1c003100400d142a2003400c803603100054034a440c0d0750003800341c105075045408202d030240051489400c14400c0d08041d000180051000d44004c01d100b07280029030b03042030800a818041160003006440865900003514000c68030002c42e000f0b41c006020041c0000d00c03104a412030305c500c402d1652500d000050001d500c404070341c014100240c2c40c651000300300412200490f112201d6009810000300c45200501c943c900101d44d24189084d0b107240080101400e420070800d5624400d10089584d50101da10030a0101e151048010700d51000000c01032585614803200d6100880e0b000580019004000a64041c00c088100c0e80a5a04040c0c41622440e00d0f059450341d0b13520074941c2000050b14507010030082011041038480c400c00040c0450b0307141e9210b54109802c03040007000682c00c91948200084d00c2c0058400a80c4425102203912414030000003000c4d02036903180d40b00710000c0344082c01e00494811302c9490340c0407245c007901d415a03441c50785d418108040c0c011351803019402031002603118074511 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 885076942 1250 885075692 885075731
    0x60f06030501050d0203060615131d1b04170a061d1011030601050901170103060e0106060806150702011809050a1b0f0f0903080310080723040209060904 67
    0x842603034051000b607032558180140008107080c001d400d54080e101154592918008a9141c000c03c60031850901d50105001d42c070540a88d40241101c0f507225021a0030600840081a03010b400d41400e00361480003840280d940b03103e50720030242407800c00b0010b414140001c1c046423008a422100a2110b8240141c9502d5446140608121b142c822582d10b440b10342d945008414070602402e440c03500b035503120001501c159106c0e80b4110704018200018180f84092640704a018500540340010141b800849c01c0b421039480342c010a0500c810300c0108a00e559036041141414010501c48589030107161005032282960010b004e102d2902100d004140807601e580320500c60340b040d0f00d0038440030b03c40010641d08051031018260000e0344003110101851b020f136003040103c100c1071528503082581c0351560101740e04261900c41e520070701d00408000a040802140001d0031454040d01c5003240711000c4405000b004800c1140a96004a8820065501c6005031503100d003014000f40980c40da521b40031039968 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 885078192 1250 885076942 885076949
    0xd020c030423010c030203090906040f05070e09130b01031b17160605090105160201021207030e0a08060601080f0a3909080304091e0204030302070e07050a0e060913060f 74
    0xe900b903020b1403a080d0b2055585401c6580c0540185250244140a2200020700140b000350042d0325020010b482c2605442000d208040541d1109a0403121004000c0131202c080d011840400080c51203c0205104d022041d0440e540404c1101035030f90800036080303045841e980481125000340110344521880810209450305d0610003c40e0f00b15114401500d1500a58440500252081c4000e0080002e20003e680c4001d005004990069151400040065000601c2240060000008501c0c03e08200071000d00bc0c00440313009e0802450702d0f40008090090007451040520191000b096280c076456221101550910344a109042c1c1c5514520410741550303d0181049014000710700905881409411f060314100340c00380d490a8a0b0210703040213422014016407107604c101110203601604d51000704000c4d8860740150403200d10b04801240019170040a80e41442070800038481c07181d5202680481008040b075615460780c0000f0085071700c20141c0c0c0342c14400540f8020022514100560484088 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 885079442 1250 885078192 885078239
    0x12301030b0d0c0e190515190f09020c0c030303011d1803030a05070e0a03020144011508130b0c091801180902062512030605040e1605060d020c0304 65
    0x900390400b4186044501c00c98507c0d000c161013143e261410b10f0700003006241405016010418944c41d04140c1c0500344840c1c1c080905103a00207107504a40354148501d5040c0303101140918103542c5405c42c0d100d449030403150300444016845000458020103000b2030641500080101c0ea00c0b4a0b018551500401098600e10041070b00d80c2118030744c504e40a4440c40039242d0695501a82410085880b40944110880300030810882010441c10341e000c3c030144084d01d01301203021841d651420303000020040d1405204001c00c08030408210120040c2c0a01200b01a80009030150303c4d07030f61804400e424000c215803294095201c00071001100d030121030b5181600c216038540360040300d61114890032075000780700007904110184680c0708100301030b4040104899801003a144500480d42c1d0305107460491000380b00100303a0f00c1005200c1030406200d0001e8200445000307010844083c041e04a4900040c42000d10803180015503481501c1ca58058a05000706001180d45440c1c494500348000082842d407000e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 885080692 1250 885079442 885079471
    0xb060109081903050f0904110a18060c150f0e06040b01050105090102100b0a121412030903070b0406020c01061d0702012f19020114012301030b0d0c0e 66
    0x400d11004507042d800d4500c01e551a5668102658042e01c440d00403207520084411306020783d00c40f40e211030151802020001d1503065949107081805801801c840c0d86d2281e40c0d1980c400180901c0307822802c03108030706030003a9500080e41e4218000001510b42e02c007041500609183d2110405000010340c140524880c00e00f0450582c0ca8a004464500a4005960040c0d001c5044242d030030701035507c080181c040240400c890140c8540c4810b02c40c10980f5001c441d60702051041604120302170102c1d4000d02038086405145041030300d409696402000d001600c01c2d032840000c1401c001082c3e040b03560700440701009110b010f90f904100900010903101394114501881c0c00500301a2041c4240700c03d82503108004501c80d915400c0c03810003d045210700c031a1111040003202401d21048000318003000955001117200010868142100541030b80514090711150010b24500707260340109448244007881c000910442420000b400891142800781550b280d11801040c0054210462031203000300141d60b0304d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 885081942 1250 885080692 885080699
    0xa08040210030b01020322121406090c010f030c1205090a020315270c0409080901121103151306030b0403080c04062a1401050106110106140103020c030c0304030b060109 74
    0x10b041d1108922214016001001000200c040c2503d2010181d03484502503201503440758800108020840e03020303180300c8110b5200002580081106a6110140d0005041c500c161840013808118100d040d0030103050711560007144240c411000341d10250340f124000d008074201241e502e501c0b640d800c3d01c140c1c000d0107140002088826484000c2e070080d902c000b60910f00b040c03031640c000c5001c1d94141a549281c003803000c0c0502140d8031405101c0c4410300500c64150384819445c005414141403a0030305c4440d505100080550724400f1040d01ea001000541c1c3e0225070b4101c2000405410403c0c4115612a14060001c070034400c1c2d04032000c0c4110711945134200c054030354020850300b41c012881410009035a0b190a80c0e0178640754000c003034410f455101c406500c1d030740a51780c4038094040600c415101d69550781c010003403540d01c000ea49507002c2e4040300800c8070074101038480441c6111898602e06048c0c0000d40d03200c0506080040364129018101500e8846443e4948250988003c1e1b40f5680054404000407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 885083192 1250 885081942 885081947
    0x601141c0804031226010905090c01021e16030b040201080f010f060e060f160302070906030b0a0c14071203110f070f0c17030405092203051804020a08040210 69
    0x6000507400400701ca0420b032031951014009601e00d21201c0c20090500c4030358541c0340e99071205160480c4c034004913080945c18003120350211100100591b100d40d0141f880a403450f41c01103068102c0031401c408410001821101c60740c58a4180c5c482002d4225080200209000520000d140128801d90702d515258881d4040b07074024200a0150451492203501d0401087d0f000f444860030b0018064030312400c010240040040903001101102580c0504940d0324080550502c1000041c0c60700400800009045172208402c00030b00411003181e165541285030740140c0141036140901c0240c44110343e0794070507868081074081032104079070042070401d105003170b0354042c01c400c1d119030f41280703440305060100c50380751100c01c894801d4040d80c0f1489115000b1444a40007a00360b209210b0350401190307038610b05814814615801000760041c880600340305034411000c1400785243d030703030903150041e1503501c0660704c403200e50403000c0729a510610025115042c41c1c0c00154544c0b0803402124080e0510003c65002e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 885084442 1250 885083192 885083239
    0x1b060f0f02030105061c06050a0e0907061103090405040212060415060b1207121e062102030c090c0d14090c04051b0705100606030e0f0705060304140c03060114 70
    0x14079034048014004118090040d00b007030000d41d41d035071b0800716030241c3c0c610110b0001280c40e085802d4542d000e44c20482d180804000c164001d200c00e2405214608105051980341e00998a407103100700d84580215065580303103403100da085c541010540b049810185444035a54405c4020140903c0c1042400070b000d0304000e05031810480c92070031140141d91005804c43e5084100c90781c0d11025030390b0701c00103200c0101940150700740007001d0304c0004142d402c00003240000c410104044600100408019005031404a001102240143c500301542e0312804442030311401000c070010290391030b1244400a182900307089038098100300c1c00303403051040170005000c1a0762003110042c0c3c40807201c015044401e21040006c007101c0e8099425070b0054681182d484040d81c0d0154810400a5162082c19490b40740901c580e400311000366000b88842c0d0728100c0421010301000b8406010781400c1c0c0b91410b032100051110351074034100182078442c10f42e102e05604003103a00c0c410159006c0e16030405003903001b882c111071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 885085692 1250 885084442 885084449
    0x10909030c320606030a030e04020d0f0b040f06080a03081e07210c080f0c070c0b0904150303090b0703050405030f0609011b020604110f0a06080a0506060a0c0f031b060f0f020301 78
    0x1806e032500468074180c40440d502c016543e0000e500708840800058076200d90010250b1110b00410b4041502d0204400d44018880c0780c1441d900c0d180c400c224001d00081c061266035890b041102255980301c80a5083c18200c25541c3c8141901404001a0710b91000e004160508980080c225180c1c02e500318108442c0f00615000224482201085000b1446200720303034031124440a491a06480e6074498503292296400701501c4000854072180307a2529018411001c3c040019042c240e0345545c03130003001641280300e111400a000204d400625100d0000c0300e001d003802404940d01030080c00d00c815a036007022200001c1c40e518102d40c0740c2410034420155400540b1070344c02080183c40d01d8803030300f019400795000d0541c007070400444020144c0341c0949940c014070141d1502c2c0d0052034110b2030001a60002054648503a400f0441400260f07008240804003940140c1100d44038030070b510341070760714480801d1402e62481d10802e6040030003415411600c05080441c00c14030a2104a0a0642c188d000078003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 885086942 1250 885085692 885085699
    0x20d0807261b0f0d092d06050d110f0a0e0f010c1119060210060e01030f11220213120309150e0a0f05040c090608010909030c320606 58
    0x888003402c940480c00c000700c1c1201d0401600c04104100c40c11520f401d5407020040f02240400701e04100c50303081d80391341099603281c1d06421101c0c51080e00000f801400580a10000e1041c045005801c042e10b560101d810b2164007601c2c56a254841030750740006411100e807620000b82040450411400c0405c0600d01c4410182c4444140c540d07580e48060007003194690340c503003120300060001c0c0840c048809034030051040342c0103000e15121040f1607809a441c01d030403405900010400410000311000f94090f007140e0040c0d128150200307541e0024403428005601603000e00c60b4403c1212206050380c1c01403103151034404958692aa031980c0d46010a0700c40c0c0e0003c0c0204d400000c1c01c1060115003142c0a006050514190303440c0c02c0200000340e0008039581007500040c65004041c070450401c0e10900038180d1090030301110480c5000790040003500c2c14051407080c1d9498003520300c1010b00034091a0b40084d4450030b40207900300b0b483c24042c04041ca680c003010200008200d20b942c19100815000c0c003648028 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 885088192 1250 885086942 885086947
    0x60f2a1209060903030403111503091207150536060f1305070b0d0507031a10090812071208090d18120c0e07090b1e07020d080726 57
    0x2044200001c0d00311a00941d0070010400c001c0c03a260b9828030040029601c0340002d075016804070b1080c0b00070040d82c08110100766004200340410901d00141140529049490b0203075960150318216849d40300548075450341ca828074082c4881140a42d10f0000e8842d1000140d041002c103440341201a09410303200141d8030742025010518200800d1152503010400203070800081c02240d491a2400d48903900400b45660080746040d0340e000c290041d07a4210f640e038682404518030b2a0120f4481001c41d0020345d12981c1e070241d040d00c02600072154080140042d6042d102004111044200c0540c8a00d030110340c0e0044030300d1301c01c15007030080c071825008246140013800088827039042070ba40c0809a0000c040007196220700040c40f0072480078100e00ea24407501d86410003900d4880c3d009541075019040c3d10600038240f80900010310342100740d60542d402c0d040000c400d40384405480c03c86115402c0e0280d0000f004a4140f424080d4080050690310303c031305000707030442c039004980341500054001e6114816508 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 885089442 1250 885088192 885088213
    0x201150b030a090f0209070c1101030504021e0301061502030306100f0801090b0303041212110606012309030601120b060409020a090207150c020d020f0f03190e060f2a 73
    0x1107030321810b4004d2041c500d40c0c50084040d00043d6a14408070b401400280701d84a000e4200844201e000158800c207090030b11980c242a070004140060712000c184030758032605508031899a00b50004c800030314009100005140c10b01500a4403980110346840c0a100b941d60542449417286260603c8820307640d075000c4050b42040c032414080e141c20041d4592511043c003011400d0742c2115880351615200e900144102c4d40760f0100034202020044404003250040c0c000c00c80582d0b0440820000050404907880760725004512410aa0041c002996003620600001103902001d0465455180340a564031020565808007000705480c0e509000a420645001003000140e105401500c6094840d4107a190100c0c640d032008400c50b5869108080164042c004001101e50140000c0300e4201c01d02c6e002c3c1c4003990205a60b00e43d00c0c4610b0b40c2d18000c5110304010208554801e02114440d484001c000903a14452014100d0302c1d50020354901008261144109040d460310b1503440303038554203180142009010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 885090692 1250 885089442 885089461
    0xc050a08070b030702251e05030d050d090b040b010303200d05070201023d0204050f2107090606110610090e10050f07081f030b0402220506010201150b03 67
    0x5001d031020340c495400d041194414141b00703039903180303550700203000c0c224035140040c81c0090310040074408042240c0e1062090b41c84c041101c80c00c0c1d010504000d03554100008820004222103c8040d201c01010b2013403100300300100e85041c1c1201d020303980e841d401003c0c80306031415440f11003061044030340c440b03c0f034203025170b0007100a012500e005005030f500443c1580040c01c00901c0c90344004815240c1c03000c0340c003079000480c40c6600c01b504020504504180c200404a00452081a07a003071090000c03154540c80c6008140120303500049031000e0320001683c80c100440034014a000c1c00e00440c1444a8240d1039410000711148102c040c07100d80c0c0500e92070041110000c000344940c0d8805400ba00390010808085030050070b000303503025000448240707402c1000514546014040d20344510500e04200c01300620102e00c1c6042d2a00000480304d1500c0390f200084008001c00c41c1044440c055462024500c0c00c598400e0b48034503400c0e0002e008a0030b4005240c02000b8443c041c3c4034044e8001e00100e443c0e2403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 885091942 1250 885090692 885090697
    0x150611061003032001020c0f160602030306130e1903170c0901081f1707050a060c150207141b01111b0301090203011b090b041508090a0803090a0c050a08070b 69
    0x21040811001c04c0c82c3c10022182aa8089a600c1102ea840152504407038003041008803d0b8000ea41048a004c90411500030748034070000d440944a210071070080300c0821299400a0700d82d40d580802c603401070450140c0d44040a0106009601091403403008140c0d181140c5502c1d0701c103800092100385003042ca44010365203201d024003c07280c3c0089000b00c4200c0190241d80700c9000e0b00c0f18103408008226401c1d011450200300d904003900501c0740d078504005888d041200103550310341c84040020ba000c00756060100070300030f01001511a0184144071141424041144030094145408030b980f9076240e100195182100e130101c52540c2e030320091004920000d07082c880010703010300a0001c00c00c9941600040d084d00c005504402034265010454a4216000082c0b00010101c0780002814203203003100c0c500060071580d0001052041072400241006810300240304881c0e40120300580301c3c24405041a0b4410f05a18211a622101400852503240c0410400e04aa0410340100125410011041103e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 885093192 1250 885091942 885091967
    0x1090306050703090c08030403020a0914040210020c0d03030b041503051207051f0e0706020f151f030804050f03060f070c0305040f090f0b011d09071215061106100303 73
    0x3d640c4058090005110070940c0300142211001036440318250300410204408940c000315112746071202001403d1007038500d4540c4103404580d401440d0140788016070400c44c0e0712560f250f00205401c0b4907030405401d40e1064240110550b070801010f03082001ea030b02401414000a4201c1d480102c0c0781c90540d00c0d10303000b420180e00c00d600356084d034030500401544c1070004414003046103031146420303000400100840b8000740141d100030a42032811940081c0c9500c5d400d401450780c400700e1000224003115180c807074001464881000702d001952410511102c0e00b16015a52141b032658207641014507001032000e00441c1d03040310032071154a81c5802a1600c207012142102401010b02002800e02500c510782030040c18500c8010440302c2034032078080c08450301c0c0452541400b0341c2d00d1211038501541071103e021400240e0f03c0380712907110301100340c4210079071400781541c141c01d000c00c4845400a004840084410544440c01c124241450740754a8007000c8407800070403c0480310400100c0d2140c209410381 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 885094442 1250 885093192 885093197
    0x11030c03100e01060911070308130c0303080411030307110307050a0b1c0908030a1b05030c0d111e070506060a08030703030b150304201215040203100510030c0b0702010903060507 78
    0x400f80d440e00220161800c1b030f0140681c0070804581d44052541000c00154451b81e00014188a0701c0382c1d82d200406402c0c140406410040900001400c200c10300713154a1075100004c048076154085450100c50300158008014000c1c02100800a1b05080c01d1400c0740c16101e5040c1400e040c02d4101d0b924060390340505180540154039100b1040115440000945c05134400083c040340480b00e109890400c1c0810399190000c11070200108651aa180c009542d403a400441c0e021601c51100c14142c16180a80a2a0b03e0402040d02182c0c008109420082070b5070382c8150207039107281c2d03108010040184098480c1000b560400c004050000b8460f80c009000488000c0055a480340c0004071124140c0044404903501e500702e0014002c5614424440c1c03805000848101c18884200d258050729171304c85240c0340310201280008a811981c0a00a0340c2d201040e10001308200c0c81c0100d00340030748868a00c4140c1d01c2c030070414400324405a06900716140180c040e12409419817555544400410009100104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 885095692 1250 885094442 885094451
    0x5092107030b010605031602070509130c0b0307050a17040816151a0f1009090c05070209040b25050909040f0b0c0901030f0b0f060705030c01020301090911030c03100e01 74
    0x700a540860f010300240c0d601d060322440c02c90254100c2551609050040d5800803004010a0390b851040f0759001001001051400c2d102e8900700d000c0c0022038120102c2814003004000140341d000b00074016403211a50b43d452185002280202189015a00502054420080142a080003a0510080074401c0f01510381d1103071000310102c11120746045904e05120504d0301c1c10014a489090101c10354002c442200f660400400050103100c1d65110780c01086860711000a580d43c020815211815006441440755240c01d00c0c00100c52401212200c404074003490f1140b45d4203010514000300e004580e01c0742458a001c0700e04000e8010f070000d004441060381446410005900380031070f1400b43d000c03101d1981d12840c2841c0094159038000980404907803500c18500c00c1c0755660b059031004040c0c01e44904c0e40e00c100c0c5081180c151301c00c0501c1d0141d550f00000000a0010071540502c43c49401225001591510a401c050b203c039526034030b5641c146d005d8036491001030348a511800d01955844000107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 885096942 1250 885095692 885095699
    0xc0a030c030f1b03050106090e0c220b060714070b040b0d02030c07020d0f111c021302090901030b0702070b0c0303070f110706020105010302190b03070302030c12010b0304021005092107 81
    0x31500b40d013045070aa5100c102c2040724003000d006a102c241d541c40094015003910344007048140407814105c120303840f4120b440078012002a804412104006041c0964505440c1400c800c8640b10810240705449244000078070302042384141c5090304c07000c40c901480c1094010310f58002e9003000d4030810017008200410b000503a80d107104581c00c207100b07083c40044c1040300d0404494080c180b080b018000ea040c9004082884810380a640001b03138111046c10b0582081800321000b0700601a04541103441003002105001707540050a1041a0aa0803104000d849200804080c0140c0040030780940c010b0010864190141e01128125401d51800380c1126882d4001145000581d9200c0000740c3d40d10801030056041c1100b6114118481654410000d8540082d031079080c1b0004281038101540400401e4964881d1800c5603c2503640d190107402a50b182c03030440310704d80d01c1640c4c100e200c0d000f50000c0040c1c080c06182038841c400030051400c030200301c490482c05050502c020b40d11429005182011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 885098192 1250 885096942 885096983
    0x608151909150803040506040501030e03070618120507080a0318022106090c0a1a090613050f03062e0b030c041a0304020d06020d14180c0a030c030f 65
    0xc80286804180401d25944038905120558401c0d046024a0341040006205a40b41c000c101e0781164000e01e030015900440e00100c0707003103000303002c001402d850804001d8040e1100340d5240c8c0c10b682e0b0107190920f010701030700b210964151254500c000c00301c1009000c1d81520324000d034000581801004080b240c44c1c40b050740001c0070000c0202c01100c0668000c5e800310324448040191941c00490b14008120901500c400208030281a2240080303401c03909030b02400702c80420b000c0c1c0d4160300700a8030882d22000c0c4c01041c201c0044050240034000c0582e0034140d40c041c5400260140110403c0451403000044100320400100c4c0620446003595480c0d038001550030701c160002c40c031404004050303e031614284400f83d84a03c0b10b0101401000c0018002d000141c0d4581d0381c00c0e80016404140140d96100000d00c0c1c001802e002e0040445a046c95030810030480c4521035208004c090000580d144000f02c0410030920740032602028120305c2c8400800e10006214200302d0f1000e41c0a03101e181048080c00e0100d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 885099442 1250 885098192 885098239
    0x60d0f0f0b1506070c141504030501020d0f050f0105010e01031409061b0a0203040509040c05030a0c060909061a07030e10110d0815010e0609040f05040c09020301060815 74
    0x480d59540c0001c100400450141860040c5540c115446840c28040d0380345c5030824082400b0f40031800100201400e403d5842d43e804640c407681111016803030315039074100a0700039000300b070030801e21604200342c10a0000c2c192040350312030304000d20408003590910004441a030909501103052603518507a246c1d0408107044200d03c0382d00c051000304018605a0712913410319406c4000c0054443c170030300c065502c0c15004802da03000c0c2d5100365152a620703a22800c0441514142e50f02054250046c043c1c40410b11042c40b03008010740b00162a080b06441e9280c580c4005c488251142880b50300c440c001424114007494014418940240381071008040302000003049070b4510006440802c0b1a00702e81140304500344031030b00f4112280c2c180040c80349071030308441c440b01d00e10040f000d04001480c42c0312a46c1d41d0f142e101b80c4240d50b0028004002c00088018000001c250544040d079081c02010f40c00130f60030b4414000c51313041c0e907110f99528803ea1130348141c08084401000034642d00c00c010441007040180d13803141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 885100692 1250 885099442 885099473
    0x1208060a050d0803060a080a0b07030b1c05010c03060b0414010e06190f14030f040803101e03060f020405031e0c1512090d0509150c0a0501091203090b060d0f 69
    0x505544c0c0d0511008010800f2040c0c0e01c44043c542049807a40045054400e0440d03024895017804a200c0c0450380004e0f413600303034240c1c92400c01d03005c459200b800e0101c15442951a40b074252010020103443c0d81c1d14035100d000e10311410a10040a81e030b015025441422840040f5038041c100314100210030034141c5580b07660450f03030f00001d0024054260036550040e03a8013441022000701c2e07899810711135051544007e0041c0054450840080410011049120740800602080c400c019016040540e41c4040a074280300030344440e41403010031182e0300d00b14401c0383c0c200c440c014014005464030004c54810310586528644450040e50009041c60f2a500c030074121120f820035185543c0e41403060800803200014000b58403e500030340c071113030a10b43c001c0101d4a00c0c40c0c048414580340045000303217100720b20404010800d94080c2c131100d0f8080060540003261180d10a090700c44284101c10400c90031505422005009250f59001084803800c04001c4543e180d03003e14800703940c440090319100c01400300d42a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 885101942 1250 885100692 885100703
    0x604022823100903080405150c060702160608010b0405040b03031b070603110c0c0405180a30080a0906020c0607120e010b0303030406241508010906031208060a050d 72
    0x1050107582c0342a1850841d10420340c10301e51480307410f54451183c4d5000b14000d441c094000c0c0020b103814600c81105942c0ea01d01c0f0581162042d01e0007480003505e0703024001d840800f040c00940b0119071140030b210700c20f05840d8001d00c000d040038038000c00c210240045020b26500f40c00100f0446203920000041941c9400d00e0070000c115062410200400b12000c20b03e061081401c28400d100d18030002003220051510100c4012a40b0f44540031043c44003041010314868910a0120781420419024201c07a0124441106440c01103000c4840080034010700000c0d800080007500016442c00d030652181c040d460050b040103003049407141640c0c1c5005825228500418051005201850090701a45100e0710340c1000900a401030b03030022954130302028000a10651325a40c050240150b03107c0004150143c030030980c1c0c1055910206401070b03a80000e20103000480134400440c18905e2801800100d940c0034545a10b40c4401903411541000d02512a41e03201c402031100190b603503030700b9030706802d050b0084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 885103192 1250 885101942 885101999
    0x9090e0a06200310080709061d1f0906140108040506011502150a0f0e030f04030327240c0f0209070e06040801020901020705151c0209031209030c0306040228 69
    0x40c5c0042c9861107503400740c29042c1c1060300503c02c1d4100d0001904400303d03591b89075081c41c0ca428807100c0558a60042d5820b1040a800300040d070325203140c003c18108c48542d00700400d004446e800448030410100c4000c0c1641d40910010813070f5045440d4903109141062042d00c0d02d003614010506400c070760a44030205450707115562800c0014891144880c10740310400214070f018001e5680d45200c1c01144400303010b00201d503580300c4080c54180713810101c0148450406030190b4507500040b4844165003050a100545240300c00001c80c00b41d115804031941004104a610003036900700801310a00a14007020031004a03000d601c0c81e1100d20103000030781350410001d030b11030101000083c0f40c060994040f6204503441c100440d0420746580454409145030007407141c01030303c55844040a0f11a02014070740502c901c0a00344862500e05c40548001d00080303081c0c034000303002181055030301c5009407030196010504031a9401d0034840307141b48410300459440b4654020b1359802920469014403101c041620100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 885104442 1250 885103192 885103199
    0xd0506072a03080f0f0919170c030403140a020906060d1803021f0216021005071a010f05120c04051e010806070e0d0f030309080403200109090e0a06200310 68
    0x300070200394001c1e04001403070075038640329803080c1c3d807842c200f120f80761f0424450f0641010b0002c43c0e00c05191084081040c0f07540c8a0f03030710003950f94075840791205a503005007404405000006c00701d1b4030822144c00804c04103540c1c030f580d01040322540c40940310f174040954800c41b080202040d02c4086030007900a0700500381c1d80034488891003484215004214049104011504486e1201404103410750b4040c0d0701da1018008000043e28180305061000e0200030401940075001590904028140c0b0440e0755941c00490741d510900407080c2000c041c4540315000341c840951241002c0c1d020590010500480c2c035024804110f52140400080c2c000b001940c02032010072a0440e081150345008400c290b60082c0380d42d0340e1b62641d645411654100804040d290030840382801015405c1c0c1d00034541205407403e405240443c44001690459684c0303001c505038520010b100c20441c403846903283c1c0214042c207100b213402e9440300000d0051000f107001100b841408000e40504070405144508810f0b0401c0d2282c509 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 885105692 1250 885104442 885104461
    0x61008010e2a012d1701120201030e010609020c010905010c09030203070315110a02031801080114090603120712021506151602100c030e0d0506072a0308 67
    0x1400c440e203011644041072a030101c40008100b9414807003031044100c0081800b000483d5003016800c2007100d000f500004419284501031100c02c1c10316029117030009000101403111001400c244541c040319001421000c2c05075009802c0070502c105030340b0001401c01c1d01c60a0701c104036044601c00302c000c0e0790b50fa40f80c00100b140c24070440f4106441c5092a0383c1c01032660b0700117a43e40c5040d000c01040501d49514800390408150032001d0003200d160592030301d41041c03060084d030300d07001400c1d051503201c5105085403665008078030fa241030750764003400c0c08804d4402c42d0138002c000c07001608080d094401c000c0310f000c44241032005820090700c2000710040328103104034001e1508040c654841c1a0b10168403e100740799071141e400005220309405501e46403000300d400342c2c8201d811030002030f40100100c1c100720b6400c0c0e441100804107a100342c4400c12070300842c200340144000c0c3c1e214002d003141d00c07090201e004203010fa00003605901c0d14480085000790106495043d884a00104038082800e0f001440308000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 885106942 1250 885105692 885105701
    0x150213031112030a200a03050702091806060d080c03030c0403050d030614100309020a030803070215131410020408010f0b01030e0c100507050a0b0106030b120606061b06100801 77
    0x442d0500c690103242d4003040e80701c2c0300c0c0354242e10074414030060f02890f540c054002100d140044005640020425041c0a8203a60168100302e101e54040400103181000c410003401c204c100600041070075075107513020310910410314075040d15064800d000300240301c00308000641c807420017440000d443e103180d46803e0f40f0b0140c2c1c0310840340906080c810140034011440580401e991011240000100e0076200150010408000d0103034100354403000220034000800c006501400c116800c94a515500340501031441c901a148860700d96043d12000c400300d501c1003146120710b032000c010703200c03c00702d01c400c000126805640851040d946603210585100ba940c401c04c5c00303881085c2024007600140b840c030503840c2c4090f105800c6c45450b62402040b500c80c8100261f0780926404030031985841c28030700704200b0440c070074071a007800179003003502c941583e01f08089201049070901005206507221482000b507541c0041c625031001d404500c41030380c0e01d0366081296a0007490a00f40f0003450b28204114182922b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 885108192 1250 885106942 885106973
    0x14011703040f0f090e0d020606150702090411010908010c02033013020f0f1804050316030c05010e12040b3412081504020304110a0f060f020a0803011215021303 70
    0x6e80240080a04881e00801d8507580004100d603004420120200e407a80540201c80f4007039003141a600402c400c1001d01b084550b8201001d88680e040203039140c55090a03294842c8540005030010702c540390108004500340031050039a0b118040f000380c4421810315191a0403034a4034852090303150f00d041503041000752106040c00c1503440301040200603010600701782400c0480d00340010041c0000e400d200e0184141c903902c0001341c8a0000740d540758240180000600d40c02619503519041c1a2080614000742040d8408000c00703215040502c1d00f1780389003440c1c000020740c02070403a0b4509207003441e44a15809070150310300d040e4880c0065055042401e00000a64000c0c8140010101803210304204140c0080c074440c0111000740c0e2365a2a8501010641d840002003a003005004101060003d401e00c0090141d80f01640c0d06442132408460403669017510039401341c0210381c100018042c00c408841c54030603084c020303041c6518240f054000c4074100d070700249a0320101684c80d00d050003013042034101c00742d12 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 885109442 1250 885108192 885108221
    0xd060806010506031807051504080c0d05060f1e13030806010315050d060f0609020c0f010911120a05060a051602120a0806010c060e01020a080a14011703040f0f09 71
    0x541d0b042c030b0081101884080c103e8030b43d000c1da01c0c00c00004514100400da0161401500040d1144c08855040301180c05c180180c1919010b030304800c002d581404c3c1e00768981030743c20a00400c02d80d100c00c2030b0800b207404080c00c42100394184c548000010520050400c0c055802c0383c009c40607030911802d00230014840545414101420519400d0f8001c01c0100394074180d44040b00d048060031664070f0000000c00c00d1480c02c0010b94200303000001d2000c001e42c0900000340d100001e0368540d4078810319850880340350500050500c01c29180d060003901b058502824401880411240c90000e942c807154548801180d0f22070240d602c0d40100b08e075442c00591025481c9a181c00105540c444841c842c0d02e050207490408001c00600d00000740d06c9a00c141c070200e0b800368108600700540032080c104103004c0c0d84500c0700380002c100c145021031018070091090203080c1a07200009240c503400e015508104407901c0f0741c0c44281e4403041c4404180e205012562000814000039544151864035030b5800580341d803100c54052 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 885110692 1250 885109442 885109453
    0x10503090a17340813091e060812030c1e0d09020f0a0f03140319110c0609030d0f110d02060105120708070e07120203070f0e03060c18040e010509030d0608 68
    0x1400c0aa10483c100c2456100610680b00c071540009101c9000c0c40750b108541e00c6080216410000e0203c24203401881c01c6550305202d5581c8800e20321780c2c0d80c0d10540340f84100c21400c00000c1c04403850300014015250340302c1013242d50741842408200741381d008403001d0003400341c2c0c50506008514103007162070451581925103000c0c642ca00a403804120401d44000390503250690381c42c0980c0070040c0110344943e01039400d40d01c42c68604a00c02401951000c0003010f2071712581144d0030b140e28081d01030310841c0c50000c0040c020ba605079901200c02c100c000001009102c446040c545e40700c0c9051091120402540c1d0040c0300c50740c03500d000c2144103030000c0c4000c0100c0c0c121320014021024082000011f070b46048025a80c0d5445003c4100c81c14200402014025403010040c40707200c56001c080800385030010764615421034074520405454101c160340c103940c400c000300040c00444100c00001000c4181c02000003481c41d924050441c20b46404a50f10080e6810014103203111800c14401c840c0504640d200406 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 885111942 1250 885110692 885110767
    0xb0c0609060105011b020a030c0305070e070509060901030903031512020f1e12030d0f050711280602090402040807180506090f04050f1006050a0b18010503090a17 71
    0x2082c1400039415180109185c1c034188055403078400c3d20800030355019228000c02d60f9030f400e0180e200c070907501440c4118400d58006c200414810303030030385000703910081840789025505070040d070040c40c1d084012014940c490041150f01a90070b080e45000300142c4013014100f08041c410071881d02804141c02d4821500c0c04030109400c1d4291290805006050720b0001c0845003501d109440d6000b540045c00c03c427400d281035014000f241d60411801303691551030f11000400407000a0307440d80e0544c2c804030040c500c0000941d40c540540701d020140540160001480c084500c00400d080c0c2c1d10640119415510022040100302e82d403005040036050048401c02080c1003050000300000806005440d14000c50f2000c5004c0c85018800004040b080300304440031a0304a21030758000d07000b14401e0910550041400290204005040390740b94042010420301c07a941d02e00c01500c041d040504485d0080c400c4004940c001003110700da545092030041c1656031222a00b111032103906d000843d080120110468656 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 885113192 1250 885111942 885111947
    0x615010306120b1b040305030c0c011704020102120d1515020c09090a060b040e030706090309050d2a0b122502030304020d08160b0117010e030a12020d060b0c060906010501 75
    0x3c2e5000b10304003001c00e022040401d403191080c0030700d80024089002c001500c100c0da00300001d540e145041c0c282c03a0302303c00c56460004204550b80403640039000d6042281c0b0a440006818014180402c41c1c04002903c0103980035581007915032074105002c2513406880e86002d50340c041102110747e010894a4800c2490b1418403561552482c041c01440b998032811500242c3d070b902c1d0000700189d00b0401c1100d0f11501e5500b0721074040d007940d1070142c0103c2d47d0030201180e2801c0000300e10141a0700429140d11406041c5c10a41c24000c4038011541414480100411000d414200a144500c4103002c650300364140b880b901c40700c2107a0051824107000d03410810342c1c252600802035a070f0064044030b00e511000703d0b03030802101e50b02c241c48002e03415807804001c0c00100594213070000c0c180c8421622400000108412807401c032108070005c8403032903001380600c4100610445901c2810b800304000541054030150183d0b054840e01c1d000780c0020540400d4203002c903401000003d9020914900605541d40343c43d001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 885114442 1250 885113192 885113213
    0x60f160e1f05070c080111160f0b0c0703030b120d0c0f0204020a170a150e0a060e0a14062704030306030b0f150108010627030b0a2a02030307051b061501030612 70
    0x724000c604984000d0082c007512274440c40055130041c54031116132a10046494007684401c1040300403901e07201500556003803042a01c011b810107038005241c5201444420b9441029091088510400300c05070000161a1400a86240311362a29800c1c40c84010308001040c00390002c0c4000c0146240a140c0c161b890104451141141d00940a16085841c1c0d4501d1a0103441c0d181c0003540440001803e00000c0f04859000c00302a00b2202c0f4031602c00c2d1034200401042140f10100180c5400b01d842c07000070549a1138000a420510a040005801d9903a655008138518120b0301c8808220803002005180c4981c0d480c10007140d0402d02e003040346581410130251018982d0010031801c0315041500784000c0c4910707082c03140595000442447e01e4948240540c0140000e132480000c000500d80d01e0b480c032440807c1c240184006aa00030318115614024200c0751a001410705d0903080c0707801000003800c0042440820b0107821400310a801c1c000556001500ba2010f69108006044c461803145010500481e030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 885115692 1250 885114442 885114457
    0x7051209060c01090809040f1b0e0d0b09010504030f020109150515031911060703050406080408160f020915091b0702100c05060f160e1f05070c080111 66
    0x11025103400d9504042000e50080410780d2046618041030300040c045640054160314804170b4007481040303003e9110b00306441c030a481c2202800b202e00120b04181d070040c1212405a00c02506800c110840340d120408400383c1541c00703c1c0641d41d10400c1c00b040c142c2c050106441c03054140000e0002c049a0b99a50301b280c4041c08149004642d514040f8100709003e0030440c940090080c00ca504050188075170504058020204994801034107001c2c5846050200580e403095405440d110b0030f1524140d006d42e584100104111820030040042440ba0000a5162000c1038000d00c2d0700001795501d40305110749903c002d8040c10030095181c0b1442815542d80c0c0c15103602c01e1064540603114400540611050b00a02c840258060004001c07003009990140d10b4504242c003076404c03519291180c06110a03500402d803551501c4614810740321f44100d015400c0c07042c44003c06020070355100004841e50042101c0007440600003500042c000082c13000301500d4402070107914008000c0d490309800c0301003061140e0b29 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 885116942 1250 885115692 885115723
    0x309020105030f0415230105030c0a09090305191d0103020301150c05150c0703021603150e2e0b120705191a0703021902060405130608030d020307140705 67
    0x200003802c100ba940184425910390030420301c44d1b286102c400040101c01d41011941507030ba8400005041d103000590075000241c080c00c580d806504100160b00030706031079801070741448002c01680e143d2082c0300076250030011013a69030903d14510706820410141d42495407a04250041c00117001090000b20a40c00c4031302103082c500b08003d040c0c50900d00b0b00c034220300c110014110000030000200400001030000510a030300b515405030310541071204011540c00003410200b80b00c0f031007e88150051303000f481114038040490302ea0b40402c203400800c0c4410242950042110301c2141990f070301c3c15006042070000d003100c070f424254100281c22a958144d9201e890712070380c050641102c01482d545c812002070082403035800d41e84a1342d205030308490b9106003030841c010304c143c1c034284800005040705c041c41540e0041005180c940740c00e007000010700502c541e100c509540e03044001201782042000300110b004c0c1a101580302c1c50410006040205206c60f6454075078070030880074000880c00310300340c5240125030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 885118192 1250 885116942 885116971
    0x603021c11090f121506090109112505060702010b0111010204030213150e0408071202160311120610030c080f25051003060305010507050f120a020f070c05010906030902010503 77
    0x10000407004588109200139901034a9409884403021491403442181d00761941401660380d05051000c032060854040c02454041c0000c01100041c02c8a20550383c1e81820f840d1001517041e01c0d0a42410029520b200142c1e64070050b92555580005010b031240c1030b200000c5050600d035401060594000f664250161503444007040020052071003030302c01921041c05000300038a000d2401e49500e07440210295413110711405018501c03480000d64020111000d07034200c103240c1c5141c0e0f456065054001d4029030001c0b0030006000040070403c007580c4507119200141604070f1540c1001c5080313000700c2d0000c14894000c02c07120024800000f0741502d2864180d1344c4055090b6480040c00d4048040390407131b0341d100340005007000c60203a0581001007920b001d0002000540c41e10f807801da442748134440d12603000a03070901014420004421442d42d2150800c00003502e02082d080d410700003640045000c9800e2001d04c034040c00700b968448511405050142810030101d10f00b500060540d0100908481020105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 885119442 1250 885118192 885118219
    0x1a1206060c030705030702090f01030519170c01060510021513110a0e1503010510120507350106180518011a031501030f0b0702160603021c1109 63
    0x50808035104040301c90190303915034890b4a0800d40b40d0b44812001d034492480d040200700c2e040c0e218490981240e41c4000181544d518002c05060104000305056441d0300043c080300c000e0300880d900a00c1154100400054001d09220030084044202c1c00c2070011075000c0c1c040c60320f0104200c950140c000701e4200d403004407031160786020032628090510640e0081d02400780001c190703902c100c81600546503c00c4081c2101441c40506089a80c202c4232400c0303a1103510070811408507048050103030180294252140c0c0e44e2145107103038012030580020030f0403003000162510354030188111032040c680d002000f445158030300001d291042010300c40500c500f9941c1c9000c100f1610f103d0141000c0b01c1c41a40003803043d01c0f0003049214440d400c00c6c4005000b030298002458500e81c4940790705040e281d00040503a18400c3c591202c14006c08002c04d42030551040c100c800038640c1815039100001c0082d42d80143c5e60300d40c02c01c29103002c020000500c42009050840d05051007252109540545c2ca00b5a03241d90071030b42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 885120692 1250 885119442 885119449
    0x203070219050a080406030b04051f0b090a170a0308010b09010206010b090112140a0e011e0c11120703110d020a03080c0f040306060509090d2703021003050a061a1206 73
    0x1c0c03035000100007100c00175001440d1501034120b4602c4c031904450404c4a95141d9114108904810407d0080381c20241024003d0400e05805003446074809490080a9a104e1403624900415602524220707172100d4055802c0540c4070940a000d0701205011605160032940080d5480c1c030103010f04504950040b03000c00d41d50348914606c0c0c0d45406614401d020440703281c4d58000c04150b050f140a5800d81c1084403aa44100301406210310328841007410070303100740740ca00311000200803a4000e2800c00241607809034420000304070401c02e02c3d2841d24480d581d5a050f260140c141071000c00041019000542500002074000c40c03080251078050a0110301d9a0300c91012103040d224641d000210480041404810b2000710341c05a4151081504e0100075500c8600d032284e82c8040400001002601d0910381c0a4820381c001c60014004202d130200402e0340d500c0f94001207044268400d8070001a9540302000034500d101e0186400500182941144000006611945034480c0e03182564585410070040340003502c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 885121942 1250 885120692 885120703
    0x4110a020a11010302390c0d0b06030c030d02030a02010b010c0f032d020703050d1b0602090a090504120305011703251a010810050f060d03020c0307061110020307021905 74
    0x241c44003003071402542c10740801c070213a688441c6c0050301c120914150000b40e60000340040c181003008007900c4c404c40d040c0d03a455019840040406400d801740502d0b08280b41c6080010005180d05038002d15260240300d40001e0840314070030030340e5041190410b43e01c0041f0f0603082c0701240141e0149050300f1041307000052149183d2003000d000040101d0990740f900d1256000c507221013524441da064565072030706184115180c80c00c4118140320342415032a1040000c003107500820811070064080c0c1241e135030381e6030b40fa01102d00840c0c041d20b51034002c00715541c10940c1886540c1c003415100030250301944820029540e41d006009121412881d5400511161014101c1d89511140c0c0403410405006d0441e603a036450b03d40a104c1d41c442441040e1131212a0304880c010103120740c0300b191140c03120356900400c0041c0355103110b00603025401500c0e60400161403e00440000d0901620b40740c100e4647d95060340d1a203048178000540302c0e481441444a42c070340c0400c0f100d0340a40d80110304241120f150a003e030402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 885123192 1250 885121942 885121957
    0x304020d0204240e0903090319030e0306150f15030604090309030c0914070201020c12070318090507020d2123190605121f0e0a0f0204110a020a11010302 67
    0x6440748000c022200f9540c4080100ba20441005581981c48003d0125581d0180c0e1080c640d242e0091b01c4a00d150020080f41140c45500928008211030504800b181c20100156002103034015018000021401c002d1062401d43d4030540e01d10141c4510700b9244940d500010300050311590f1038405250074144a906800e001d1a00010f50341030042c0d4456889008142c00d8062415174003850001800850043c0f0a030384240799131030060300c1c886c140600815156400060224144000158a4698496513941c6080501a000b1000130316044c800406803800103002414403c0240703178041d1340400c0401001810742c130011b0500210f4074641501c90103407004000e070403000d0100b50002c01c0000d106813844c40d00e43c000d8180e9004001c41a04e810520041c1282c1240c1a050303548586003503034402c80350485a48a40b540c01b02c0c0081c200810b401e46a04040b0308040c03da4242000e101c0f04819032a0502c43c40003000d04003040300303140003a03c2201a441d50102c11026240368940341810920364025012540072 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 885124442 1250 885123192 885123221
    0x231e070302130213170c150f1306030e030f071e020904050d17060d0b0601090b07060504120c1a09030d0921031a040f0209040204120b06040605060304020d0204 70
    0x11856003010b0802500107a03018030a40d60100b400040c840d0204c04001e01d442803060191040618038401d201070800181d040c00b2241e4820415400c4010b41c007009044100051500d101c5254030b42000141034800811408081e504100074440450006008480708107500200007590401d109640750400340000d03102a41114200c030030042000004034014220a1283e218001c500d00205204600d9080c00c0b9101600700400106070804500c2139181c4681c403400c1403500c198500d40381c1c0303c1040c036500000002c0f104d0039200c1080c0806c02083d820801d803020303820b01e0104d0031001d0f25150040000441d0480100c40c1e56100049540100140111102d1060002c4c0900c49501c03540303004204030182e450304814500c40301e017007200d85501c6805501c1d4541120340c0000c10301c0c0281001c01c00103104241c02e03082100e900f04140d054a4031640060001824140700361400703c400c5040a0304114002410a84103600c0c0a50500807035580c0c10989401c1a01a551004084c0326480402c000b40400b5418408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 885125692 1250 885124442 885124459
    0x10e0703031106090d0e010e0f031213082103040c031b0e070804080301060e0a031205040e0702030f030a0b1903050601090c0c020f0616080a0c231e070302 68
    0x5054201c1018030018101000f2500c499842d0030307803e601d914500c071202c00003481d400066507107076101d02421105281c0090400d01d86500e0400028038001e8034a18501c3c6440011660608480c0801c60041c010880000540020340c9550510004d41e1088403c100b801c600100c00714080c46801d40c84207010710350103100300c0c2d0224001a00c202d1502a58410301c40c0191a043c00122134a00c40d00c1082d0040e03900010407820340c1d08011040d10420f05246010b5001001400b000001c40d440300e00e203601d402a180c494607a00d5050003120070101c00700030030324019035100b0031401f45822094070440fa4080741c10300e0300040b020000c0c8009081810300c003503016299504441c02200740040410994101c40f001401000382d9252820152600030030b80c94082d522005600c415021030a002004001c01a089201a43d62a0719541e4118041e040700c060304000580504908c400c00654039003800320051038030a05040b19a0380307450160340e00074041a6280305000c54042451060042080c0720103164000d01259 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 885126942 1250 885125692 885125699
    0xf0405091f0204051c21171602120f2b020a0f0f0c0206030408030c16030c1b23060c0a051b060307021e0307020d11030f0c010c060b03010e07 62
    0x40c041d402901841e8030600799074001c803c1380326031040c805401781d5021598890207030012011a005020000000c0c05110301203043d0000c2c0c00704d80d6126407060050704041f84014403070007002441d0507206182c02600080030072281424242920540b1408106041003442604540b207150b035900d03051041110311103002084560005800041c1d128000000d40d9030140d0380e2882c442c003103d0b000d103120b00c0139400c4002040400c0108010400441d070240445060514100210101003845000f2407030a400041c80c0c0380c0c0c04002c0210f1407413011258401c0f007503598001f5017440e080d13082a0100f000c40030001c0500c4101c00c101925408182c41340e5001810944005800c1d5003000b81e1500070079071429034190f02080003164240780110a9900440081e40182811540d48540d80c0c0d1422101528244e01c0c40706005080040c0d40e8140c6580f4042e01c43c402d031a07050070f4882d092501d000f0320340190703148681004041c50900d1741c0c0900321951250b0024404500048401c0201c1e005081030b0b01410690b000d05d00010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 885128192 1250 885126942 885127003
    0x2011401170d0e0a0b0906070c0e251260270c03020d0b042a050d020a03090c080607050306010507151a040f0504020f040509 55
    0x31040c0011100303980050755641d600b01ea03e2007018035aa0b41c00780d001242804404490400340c0f07600703000a03024500d0500980c58046084041d50b100c00c0c1c42c0180141013015851013507203508816411006004d0b042d10704a00007600b8003595503242e0070000d03525a0503103e07550340302242010001c108151440360081099a030142160308009002c0e41c1412440c2000c800e400490a44d03244044c2c410055000c00c0c1845094046000d50001440602e06202c560440b10400e510840c16011880e40f40165140b00c0001d00c14180c0d00d0b100380e40d5208510f4000c103507080b0b410000428501036006600d0a00c0c03d1048030040ea034078014460680c070090b1011500f1003403d034159011103d41c6001c0c2c081c0d1b011440d07641d0343c05956010203d468000240d000e202060165010340060a05640720702c03070f1072203000602d4504404a49015000200241a8403509620350400303124800d0182c1c0f001e14244194a016008601e101e008540d2441c001c654031b8001664680e410b004113030407015411a0340003000044c5441 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 885129442 1250 885128192 885128219
    0x17040602091005091e031e060f0129090d0f0f0302070503070f120314120109061502070b0f130e01031a0f070e0f040207062403050303150102011401 65
    0x40c1d004541d01949002d1480c000c5080d0f41805a0040c83c0b841115401101d004541c1919501c5503090310404040c0e02903d50514245503428102000400662500c900814050340040c0d01c040c0944054005903e9900c05050810b41040c181c4c00c2d645e035171900e90001040220807510405050820b48000d51005c10801c0d101255a06000354200c4070303c1500c60082580314102072090b4401c03850010004c2081e0034504a0740181c6900070305001580d0700e44409078008641c0901c0c44480f0300c00c2440014010f5480912500e4052b000e40042d17480222320a01c80655101400d000b5401700c02004500d00b09e01c80503160490b00e427155111007503441c0c5542d0b5098041c01201c00e01003198094440c4c800c0ca00d0325444000c69600c241080c60b410300c103070b4880c030b1420703520350684031001500040104110741c0d15448500042c85000e10801c40000c2c0840c1140382222480043c65a500100c0d500301c0c1c082002c240c0000941313411481081c2548685044080180e0061001c2d9a0780c0030320950300800041c04c1d00b9010003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 885130692 1250 885129442 885129457
    0x5010e1509061314150d180209090d08180a171308030a030f090f150905010c2f03040512010e06130b0601020106060f0c081c060807141302070317040602 67
    0x1070a91220002820401c17201440c542c0b0050107041404820390301d50726504032004440352011441d81ca48002e070040f80030200d0445502d0b003d036220724181a003040c1e03c030540d2507000547c5407000e84007010a254050300ca04240c0c0016000b840100c010031146c0680d00102c8100901007801017100c40c0d03450054986a420551f080800f085ca0406068128980b9004441e007003a84140418500c46240d85c03000c0f440c01c80d024914402c203030b442c20f440c0700050092040010403031103601c0e06540300040c8065180c9001d04903000600c4441803416403000b001c1c001042d10b00b0b80d90b00303d400c4002e1603181c60509004141254130b6403070900c58481840324002c8021083d00b043c034016403241640759a14030042e400d0310014402c900006d0440e0030711503981c501c100080046140b080b4030192800d0701c03c040b8000d101e031041c14040581070b5a44010030100d40108000002000b03540300568101c51640b002800704221048240340c001d4001409a0815110740340c0040c24030444052682c16050a0800078000d410040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 885131942 1250 885130692 885130709
    0x180501030b0a020c0c010305090114040c0503071a0f36040605270c0c1516111b040b0d0f05070918120311030c0d0f02030105010e15090613 61
    0x404582e15031100e008480c0403018101c0100309200030707400110004c10b40240b1881c1d2039540d4041951102c503072086414020b0b8042c03014840d606007000201406c050f00742d0f000b006400c44207103081800942400c00c2e07c448506510249468040340805000181042114100f0400d06694155060f00b4458010b80700c490080d1820410f060700c40c4c09000ca445032042e00e50010841d44038500c0e03aa8a1283d0049500506081c4424200b04114a400d803070704203044521509070500404011100302110040c00c850603441c5840d031514001044400d440d0140850041f210120074807202103d40c039150480d240800700a4000b0084504030700300301d00c14101ea190122424001c1e5074000941c01d0050180708100d15607a802007103a003449075100740b40b1145000c21a401c1c15112074940030178204441c0603510502e005484103603507580c030140c00d50403240821120f6440501c1400148041c1c0d0b8171641201e402a001e80b0000083d03a1030007120303000d5005200e107044d4882030025206100428900c0070702c00b00c0e0b00c00c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 885133192 1250 885131942 885131963
    0xb0307021b180a0c05041d090114040201170402190801020c0d02030a0e13110a05031f060f0503100504020f12060306010e130c081002121602071e18050103 68
    0x110700b00140a14422054024403480ba40401c0c15002281c4c003640c0c903490b960900510b05546e40b004040f512981c0e44001c02c01101c803908100509000380100f81300c140c4c0d0360100e5010b51800360300280035024442c0c4000d85c107841d0f050020381107460708411a5004100c080c1e00c81c54065070341030000e010303621500c0c01d0003282c010a105502e940e03000005854030604252038201d0815091014009141686840c0c0c4c10903e0300c60510004108007680142540c15140d541c4c25503d1074500f11480e0000541e239508031070720200140c204075603680010042d2034a866454030668944444007601800402034211a601c1440001d8400b44d08030000000c1101d15641400d02240359200e40826840e20f009102d250a0f403c034200c00100c0c2405002c800e10011407042d41d0800b81d00707454090891900c0114561380000381c2c0d00082550352210700590341980709070810500345a00b81101c500070b484206c0c922170814511250000c0c460540310005079900504403803140140c01081c1064114042d102c00c0c031082d1602c4000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 885134442 1250 885133192 885133243
    0x12050c010c0b160e0d0503070b09070b03040201050d02070c080610080c061e0f0406080a0e01021918031505040309080303011508040602090409050a032a0b040302070b030702 76
    0x141070141e441c41d4100b00c0300b00e140e96036482030b08000c15110300e400f4200414030b06003004542e0340fa02404540d501607802503440325028a07101d00c0408001d080c5000940c440b000070424501c040f011030ba4000c0d420301e400394842e041c82000ca80a40524003008151285841d00411003402c00215184a000981d00b10150165143c0d012512600d0b000740098110804002d5001030480d14070441301001e400400f5540f0300001565103c42e9504250808800660f981d414407413400720038080c81080c114040001c610304203041015154105403040c0300303400d1208039030040c1034101c004420784004642040e203800e10602c9415460000740000c6400314041905408d000c070b50741400200340d030305840084ac0540001000c00209807030082c070003002103400a400b003049612549440c0030b807884080c80740000b4413030148107242c041c01003c50300d544901c9801654088914a160b40343c0d42c0615250480706000741d03900c8600302207062040341c0c1c010812084000050000c500da0002d45410301c81030011624824022 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 885135692 1250 885134442 885134447
    0xf090e0a09020312070506011e15020105100f350a1103060906010602030a2f0c10140d0e030915031b03040c06080a09021e0411120c031302040612050c01 67
    0x6540014205030b00c0440140540c01c0100260895a12840c0714448100e2ba25100805403941240821005075111003c6c4580c001442c03003220013070040c41d41e420201c20b0908001500e034001c02299a400c603095025405c48460300720724495880c0e000c41c020760701400300f2800c0c011282c00b22044664013a01c9600f0000384107038004144203041c0d0301c041e0b0255240520401007240c0a0b91640000301e204c4800090000700c1c0700c80c469400c03281d00500000b81810f50901c0d02007103800450845500700780107940403525500e4981c1011103000460b0300000140c40105c0c0500c8070700d51f018400b40b041d00000100b032200c1c4102603410145100d03080c240303801c40100780c0c807491603a498001524028240598001e040c00001c0c02074070300e1684032000000010701c09480d500041c4007102140d02c00b200c1d902c00c04000340001e05050243e6030101749640c0c4030501d0f02c034142d400c0086104005203002603020b0301102003501100242c0d0540300d180d8004006001071912074101b881403c4044100700d0b400d12484c940d03802c4550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 885136942 1250 885135692 885135697
    0x71412010606090e0a06083a020d0c06060902030f010e07030204050315090c0307030c061706153601080a1503021504050402070501330302010f090e0a09020312 70
    0x104150f5418041c9860a08074440c944c1e00038100591441d1542c00c00b0403e26020414804503240d40404001e6807840060300105e00030f5002013518940d907401042c244174903000108a0801d54640c900101c10b0030b5036043c0003004007030541080340060300000038407800801c41e2454605982d00c003071500c4030355294aa0141d080307104500c1750940540107501104450490002115485004201540d4008041900090805240e900102d03a403d0740b05005215036035000806182250741008485400c0c02d04200003001a90b0980741c100000c0c40c001446202c18005015283c0315140e040b20000408008001c0c154110400109113800108920000386030750101d4000c0500c0420320007401c1c0b550302d0954003480411840071078401440002004000b41c2da03240e620003882d0f02030180e4000217603002407a282449180c180b2041140405800300e034034071303065a44011101200d50908001c440344194403c242c0341403000e584103521260b590b804020310bc0d02c00d0703040041420f10071001d5400111a0081086090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 885138192 1250 885136942 885136949
    0x102070806010b03041103060403021c030e15091e07080105150d0204050423060f060303030f0c090a0b040e10090204081504060f240603110315120714120106 69
    0x41e8454801040150340c034100640c0c00900691543c40c80d480e0140120386030100c02e95086005034042e03040350400205800b86515024032500e014031001101010050390754003490903225112640c4004030300c4480081100524100b00320108416805c0400c0305103444402911030b1070748950034640043c03a00080c2c00000d1a20f01340060490041e540c0740d4013840001c12008204440440c0442c0c40701200007010f240400644c11400e0080040707103071100349112284c1010340914080c0e030040c028020020030090000da07001c1400c4150680b501da000c2d00149140f043d1354000d801c501d000140c0459090302c50740b03004e8890400001a4030400755124540000c80c45541714100391078004d44d02095194200b20b03107250f003080c00f40002040c203004202c0d004044038130441078070441058034015512a40d0083c841000140303007074202044445400f00c00c0a00c035202c0203004103029100541f00c11050b6442d42480b034818a0150101d0b0055511049242010000000b04921490055a80c4801c0c04814003505054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 885139442 1250 885138192 885138209
    0x90b04030210060f12052a18090604031d0a090e010c0e0609010e040207080c030901200604020d05160303050d0f0b100f050d0f0c030e0a05060f10170102090f010207 72
    0x40c0303160040c584c1e05880c058030100c43c1e81c0250800740c1404240381031f01c800d2007040703045c1009660028208004040c4403d12169050314621010032070190008100142d0154041c244400c18840400041014005160f44136a00a8220401140001842d8004150454581c1c002c0040d50112481521450b1042d00e820368009000c101079400e55104042c0c0140d041c1e400f40c07000d403c000f6a40c2d03032065603802040410700107034000710700303802290707401400f4034801001051540707100d99218502076101c80c4000c0000c0c1c0034262486245040003002c0180d901c58840480711140030303684900d4014040da00c0402080d910500700540c14032071210a2240c1441540000c1205010450901c8291018006440c41405101050080e9911441240100d4101215a100026258010f0140030f022203240d2010b143d40365014580da1000200f000130031a4028103c6180e0840a03500c3c4801c000714500c031a0449140d0040e4000315445084054019040c2240102c031103070340c841d9103200126544c103c68880d9841 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 885140692 1250 885139442 885139469
    0x10091b030506093601050a090323120408041d010602010605030f06011806080a03170c0304050d03091104060303111516050d09140d090f230a030501090b0403021006 72
    0x4641c1e0800c0c41080c0351456045130074148510440582e82120003c440110b107032038a4002d05c00815034458901d0001d5480204071141c01081d001034040540147c03a0883c11850b2900c011500340302120050707034000c0645503980c0c13040e404010505004910203216550140d03003000c0002c10349240c045102c00e40201d0761002045c80d40c1c030303200c0c07504100e0030b80c0001c44203032075500c5e80c02164180060025504081c003e48464aa0501c00450301444060042c07100c00400001d05c14400060070200350201d44004502e00800d600300c190520200814140e0081c540c4285401c100108058101602a1000491006a450306d0040a0240059200c11246004814010790745020b507540904040c11290541c03940004442865590b940303110341b22800260070a9100940313001e10142d100d00394801031b0180003045055103244c4000410440e19040188010203826807188c0d0300c6480e201c440000943d089002402010000d0500200e5050250f13019001402201ca0428826620303000d5001120070a44030a003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 885141942 1250 885140692 885140731
    0x21207062f1804060815091c09050405070917070603110f0405011d0303040b0c0c0102010c08060402160203032d090a06050a05071205040815040c090510091b03050609 73
    0x1942c4166080c299030099039240c0c04101494100546084610080b0030501141800c01c2d41d149031004100205000708416140c070b06215511030b404030100c507003c0c0c0300815141c41c3e410040d10f0341e000c0d82c1c0060382d01ca000c1902c92001d0b4800041e4081c1118141d44040251040c0c0c4002080f0500c258800e08640c44400c00c4100059485000007105001548a03c842c110303500c00c00080c2140c5c81170388600e40c0078402040420000500340160340402c0c1090000708102000d4103005041e01000510300c911581c2e01080a1804003100c40c02490015030040640e991805581801c5103034107600c9044001c0142402041c04ad645c40301c5040720416580180080609890501c040b9400c0d80300005c1e000c20040c0a00444002400c44880f94280c00916210a600c40b81800100c0d86020060b8991106407103800040c00049000c5002a1043d01d52828012401c0d40d5080b0320078881c14555880001340c04d1408085912400346008946d000704025501800345480741400c1105081d415944825160060740c01712 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 885143192 1250 885141942 885141967
    0x29070f02030703170d050c19030c0c062901050c031608070f0515070207030b061005130b0310090e0613031e0903051e1903021207062f 59
    0x526015100034111441103480703a43d021003096000001094441c000b1515014605d458007610758462504650242419091000c04141208604c008000e0555440204984500c90885c00bc4080c0d0442d0080c0a01c080507003100404000254803082010a0301400300d0041d0b2003403003119035590b8030000a504000124014030180882c0e078100300c5150f00700708003490000d410348210b240602e0040010703000301840c116002900107001401d040442d0000c00b000e00002d52010000f603040142610081038014500703801382c0360b902c100b804039078017000301d02c1000800747e00c0000150b202d6101c00440c0e14840782d9078001f41d030540760708045128898020b00f002488240c1d80d060001009030103442d00c90799000700c20142d1002070012032040400500200e00520602c00c0410048001765542e4149080740181007640c8c0c3e40394560400345040320070001c03600405051007000303020300701d486015a0315035511042c40c100e001040d07010031030380c1c8040d1655074280316106034000b20010a148110301615280c5030710082c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 885144442 1250 885143192 885143213
    0x306030307061e1e060503030309030703030e030c011d210a03020a0306050a090b011b0f02060307030e12031f080717012c1b10030c03021e042907 64
    0x1401030440c110f88500c80043c14016a41000d6000800c21080d030a40200f02c0180d0f10039811043c001d520030014080490800000c4aa03d5601450000360820000800c41c2c11841980003400f91903003000220030190310708040700380303404c1c40c0c480840380907680e000344490300d204d5000115041400140030303c5e640180a60000d101c0703643e1074500002c00036190030004a440c14107812441c0300d1580e80810108550b00706c0300807554a134072903240300a4512540e40c0d0903040411160000d005100210214035202d000c1c0d000080340c000e111040d502081000444600660003c444903070900181880200c034002c01441d81106685401018001d401d0500c410343c02b40791030b0004d20380341c650b503210f040710200f8040d0a20900005011096008924020a0480e01e41005071400800d020009440c003852070340c90303001030f007051003207030601081000704084141c0003401419108456405004115203069400100400c15030380c20b94040302c0c40441e13018054106540c0c4d4061210429003c00c1404d001c1400c40c03c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 885145692 1250 885144442 885144461
    0x250f021e01020c0d0315230d020d0606122306160903050f10140709090f06120f0201030c020c010804060f090516090b120a06090c0b0f040e0105010203030603030706 72
    0xb500e4600c1081c03149280c1114051640700080c0e444080d1076003010b4241514005200084c0d40d50044940c0382c420300e44400e1804002c0388104464481d100854840e240100c070419002401048050355805000040c0411300300c046030b040410b0903050040300941d0204104084c2108001d106c0b0790f441e021540350024143c084c80c414085c2800000001880c200002850703c04075602600a0218010701c1c1c6051714803400843c9446400507041104aa40c03100c110002ca404050002c2150284e001e60700300108480c1e081014030b404036840080a0100607045004200d1003a80e0801c54051101d00490720b038150022041e00007040c882c00704000c500107403c902c44041000364001124a001c9e507401e441c00c40465002940c070341c50307000100100c10303039842201070398078080da2180307507612000c0c01154072218044801406140c0c2d480158050000c2c119a2401405403071484c1555000c01108040d80ca03001440703910000e0307100e00c3c00462503501c0031040d80d008001c06030046083c680c180e941c22002d40740b00c85 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 885146942 1250 885145692 885145753
    0xb0d03120504050c030d030b040b0f1302070320150903041a072a1e0605030609041721090a32030f120708102c250f02 52
    0x11002e141940c0c003031095603250021b54400181d18505207041c081504e181184040c0700d880c04030071003503c50310340000c00c2480c6040e900d00180c3d00c2e006403a0a40e400e800c281000807100301c843e90605628400043c040b0050740c8800c00510007995002c442d60745d0b9100d14002c86c0345c045c5410f070b601d00060306840081c00c2c59500c140301004011144c1039004031410420b03400d038514840b80d00c00401c2a0107001c0d4040fa5554000d510409115090102c091300c94400580070a006420100000d400d100c0c0859208540c0700da1400b03c943c3e602100c400080080c00911500c2d42ca08a102c0f002c41d00103440000c80c0c1c00681e5120800289088601d8091080556001d80711b0040082e224540f16201d41b0030b00003814201c20200104d6110403071075a04d91008003000f0060301c1400072800610400101c002403d008075642111860740448a2081c0e60070038050b03403240c031309440c08994248110146a04c08004040941028000040e0207544084418a560f0820040540c04c2070450a48050002f0380032080140d845 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 885148192 1250 885146942 885146953
    0x2040e0a0b093705072105100e07030b040515011413060f090f1214030c0715030207050a0b0406110711060711030613050c100909020706110c07090b0d0312050405 71
    0x702c2c902d405452040f07800900290500024140050360034494200c0c54643d10000c1080f403414090440e040709090280704000d004640c00540c10ad4465000b00c10001c1000c1c10500550500e101004d0029054040d60b9020501d00315008002d6410707030f070030741c0d041d00000604c403512145048000d03a00d131801001c81000700035890b24041031007284094040c0c0200030215944840c06510305051601441d9000f084902d40c000f00303c4044500c40006640065034150b08a8009110001900b98003d10446200601034062106420305014841561503c514010741090010380a030004844643c0300d1000c008103540940603045c0d0303090418030081c1c110503200e54032400e0f00d89403000000b46480b0040f43c0c0501c0800c4120711240c00c001060000c920900810b4580075084540d1000c060000d40d501d000b00d910803503001c1030401c00e01072142c010198140c0404251a40c46195640320b03910341005000740103556080c81051149800d011190310380240d0141d80e60041e46411850060203440c01820903030b203d1090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 885149442 1250 885148192 885148291
    0xc110304030b04021305160e030715020705031615050304060f11070303060510020c090a02190f030b01020a1a070e21010e0c03031207050d02040e0a0b09 67
    0x800040c000385014021030241440d0510402000355498209120202d00f460300b448900c1c0d6407c1b00381307101c0791500d0801c0c0301c200901002281c0743c005940d011f000810150034011003000d40100e00c030029035a09a09841500043e07450005203560144034440e04542800c19002d034181c17060001d150490b00c00d880c0802c020b002d103050201a00d4400401c8a00305200141c5002019050320505004150603a00508008940300019480d0103021412501070301e400000101243d0080e4121241035940101c42264807507002c00c002c05030071541510001081c50081402800c0d800000d0180d4842da100f00340754410000b040c098117800d80007a1414003844841402f080040e82d80812800307611a44000000c10511091009401c0d651400a180c140d81c000000c1350f219502d001c4120b07080700124225030000c648a020080322503101c0d081032000c0103031000c280452050b00c04180d0324007981584905000d654620420824240010f843c0c0c500c1410211440c1031031140b5500c0f010320001d0304290240d861615 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 885150692 1250 885149442 885149477
    0x2030a2a1101030506030c0f04021b1501062c060904090c060302030618150603090a0506040f060c02010c12110f07061d0a08041a040b13060e030d05030a0c 68
    0x1030080040314202010095400799507414440e0300da210704101c0080104080c0140800c01c417184050310240100e40018031140501040c1c0101407640f21503104071900080c141d01d600040c01028080d12001a00c4a0411220010084048203041114030040651811008108103c0e903004485035a085521524648046034101c41800c0c000c11523034501607501d280c40c6040114140d0002c00f10340c07000c03241c401070210b1859001c0d41d603088010107468a03aa6510b0701480d5602c3c0584000008105104d030074200000c11011000300224544a04414400752602d16800d0b4280d802c10440480026203200d0015140807440d00f01c60150048034140c03a1a1100c460852131480e1300400040c0d59282e201c84031118400c02c4c54801082c20701525001d06101d1140b40c0d51114076218901c40d03d01d00c1c203412540003490035844401c49000f80b501e070725003d86d118032a80c0020320006080c41a03d011442040e00420b180c100450081c80901180d030394245182d5a880484d001400f2310340c80c91781004400c8020018011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 885151942 1250 885150692 885150767
    0x80c070312051009060605042615190501050d03050a14160501150608011d0907090513140601050d1502070503211e0103021002010e032b020a02030a 65
    0x40014070f6850000c1c0c20940d0341015500541d10400c03c00004020820aa04102c407072000d0b0844074030b00000320801d50b0843e5920f0545c0074100d5508040b9030005010140b103140c40a440300f0f1006071800e104582c0c4c6c46041014200402402502003a001c00c1b0711001c15114a2111044002c02601c89060031960100446c580c2e03144c0e03404880c141c0d1360343c50600410902c4210840100360502e0700554030b604201d1070f80780810600103410006000790300840c409000610a000181c81d003842c3c10401840c140824600008006500fa00c0c69503142400c00480b40001c21118141c410280c4080300c02c80c51541c0d07290028440008060b1165400c3c002e0740f0000d041032004002510039865400e00d0500c0b10b40c4c6103021b80c07102818006a01280f00242803050041c105081d0440e90100c030700060082c28000c0c280c1c05842001e40c0e102240c04002190795010044243c0d808001c01101d0100c02410f900312718840c200d1040004941c00740e0300501c1410143c6100d90915061aa036402c0d01200c0865807018981000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 885153192 1250 885151942 885151951
    0x30406270905131b08030f0a0302040902210609040b16030b060f0406090801050103030c150b0d140c0103020309190804170d0e190b0d060503030c06090d050a080c07031205 75
    0x15411107051005004520756100d910304c20780c60800410074900f20420741d0740d111342209040550404110311140d940658155001040700b41015517036000c2d10070021500c100240a20425807030010b01081031400c11280301031103150712804003c0c0d6916000740000741d180ca166180c0b4101519035200b0806900c8482c0a0080040c030a0020317511a8248000a000c1c1080b0b60840b0180303a1603e070040000c81d82c42006444400e8108016003015101c10f01000d028105281d44680c1040e5010600f0b0b081200c21103d0501c18101041a160010300074801101648000e645050160748204690042c2d610440d141d1100180310740c1e0041d103403070b9584a8160400040c03240005140c0c0010100203003041d0040342e400140001205c503014942840385050f80f10340c1f0507000d91444107601050000380e99040d984520041c0030000e0489032100102013049607a00e42c1100c0000d500d0088021003d0054014410303506100d80302d4849000b295030341c685164094000d8081503003004280e1069104000c628424507001c3c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 885154442 1250 885153192 885153211
    0x50d0306062a0605060609041d0723090703111b06072303091e0a020a0b04150e0105041205010504121e051804060303020109030f05041401080a0902121b03030406270905 74
    0x441920023412410413404e41e002d0075420b62103401d40c1c6034403204580320001844003162090581cdd2141c044c210010002440646d0310b40d4000103000c905208020b105960011661f41203400c2c1d9a52110112200550002c46e010602d5071084803103882054503000d03607806a005000c81c0d144d600c0a08200720b07002004800c1d160241c010121440540c01c0a20951001c0c0c02c485d0382c501d252524011a0700704d9040c4205800041082070351104c2034580c4504221001001d40500c16035401c182418018020301050b40c2c01c0f58224210038684124134020711b01480709a52003590380c0314001d080c900541f02c035071000040607070070103d60a00780c29039601d034403410014500036400000c0046580c54041e050120503000d85042c01030501080000003900244c100141c03000b032801440d5a16516080e8004c2c1042c3c0c54020b6002e1141c040d803994880d4000303508032207200302014111900002e07006058492240c0d0145000040548900c0398052510412003856221044001201c15030749407031b5481116002e540302c414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 885155692 1250 885154442 885154481
    0x810271a01060903030e040e0c0306090115080a020a0312030908040b18090613090807050a030f02060c04150806181006030b0315010e070903050d0306062a060506060904 74
    0x105100e100095902600c01c40c1401c100160441d18007030682582044c42c644110340f1442e08a21081052080156112024085800905002d01401d010300201e00c441c0800c03188009000078464000503468540c3ca4000c1c2c103a80505055071100c01c5004400007051007419101c20603040002e81040c004c00080900075000341d03c9442c204281c0f42c02024048145209000620a01a8581c0d0b4035008901041c1d141d040003546070000d207000000c0380100540a05103000d40380c1ca020605800082c01c05400340c076a400c1c0c0b6aa030340c1b2100a038400740100d0180a00d0180903031207658030710340141c00c5542c00100081c401715401140d07940203100c0480c200c0d0001094683c409007044640c1e0940036060311380d072048028110084901409940905052081c1c5003043d4044d00071031451405000580c010796040303021303a070107500c40d23034005009444184107c07800182d5a544401a0b400c04541240b80203072002025588210152103000c0507010182c00c481d401081003000d54442d44c0e41e03201c1c3d00101202d2160310003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 885156942 1250 885155692 885155723
    0x213170c0411070b060405090f01090809090702071206020f160c050301051509220507080f060a02190c050c030708010f060510020a0b0a23061207081027 67
    0x1511129407000005040034403c035030002d4904021150304c550b00351800034590351100401da14010444400410a500e030160a038280410a001450400420380d1030b400180c9a119040380c0e0391034244954509480c250b00c60f03100140f0b01e81c00500c458030780d00c0d041c0741c00e10580d076002c000d900072007110440e000c800018040149007401e00072150b10141d401026440000341c000810f00401c0018050203c12138030304480340548003030319032464201d900101102d0b44103803035030030060380c4000402580010b0312901c40040e4204115000302c2da60050408002d44981d1203108041da03540600c04030855841c01200510310b060f860403c40c407001040c800e000031503a10540c0d02100c040390706a0300f05a000d00302601052424a40000302d4020003684481d641000780e07216a0100c0082030030300050148950340a8601c4880351140b08078a01955040302c044000c51f085080c0d181d0781729501d2084000c00d40101d2003810030126550321212801c4403690448801540d803080707036284005100c80845a030307070f561000d05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 885158192 1250 885156942 885156949
    0x6052808061509060d0f0c1703030c0a08090f010c091410140a05070f0f030314010e1611121c0c020a0b0613050a1a01210213170c 57
    0x99000301103540c09006642840c51105607901944191140600350410200382152074220001c2011500700c004520080b05610b040020105035104504170019000b01405034580c020040301c0c010f02c480c81c0700c245445405001500c800318001c024084502a500944800c98028002c40001ca036040d038501340150f05012600d4501890f1204c0203004542484a82500f2904121540c041e2500240b4040d16002c600300304507042c0c8901180140741c488540f801400304602802c0d842407462013901e061100d08201c00312001520424441e5440c1070300d001012420490b1811f005030095465441d0940040c8442240f851501c004600b400d20484000100121198003100000300e021203c01030901a00c5040c0100071b5032000c0310320010f40291429030215002d40d4444201414440340c1d01400d00161411204000040000b101150003070304030907131580207640c0b14001c03500c885030504121100c0d4130000b24064009400c040340c9040c500d1400e001c041003d44448984442c1d95110500905588100e00c051 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 885159442 1250 885158192 885158269
    0x91314090105070f080115081f0f050a0b1602041802040e0a12080403050301050f01030e190308010801110304140708160f0b1204151b030605040e070b0711040605 71
    0x3500c0400c1381510060012000d0104450310860140c40c1a42341916010401105590009103464210800000c0003984820040100c412940c04541d0b80344801c0d511010341d5280c2c8070302d5070080c0959480280350801884c0503071001800100540309480022020760214040b1925540810469440000081c013001044c1d81141d040b41040d00d0540c2580c00c00c0da40260043c00103010391441540e8241020510380d00c02e42c01a095100d90b1012100a8140c42c0724200c058004460705500154501d0300220382d030b0310140600703c8904a020215440c4d40e1341ca403104158891110722081207800b800100043c0100100036180240003091401190a45464504092244140d20800190fa41405030342408904c840b2866480741e00000e54908590420171000c00801000203070705581c0c5c44895000201030b9060b40914180e900c02c1c1d800308080c1d0000c0000c0384d5144850f1045d40d01e000d070201300240000303c00403061801c4190180c8007140041d260030000c0c251109040c800c075043d80b8408c03800344000c50031102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 885160692 1250 885159442 885159467
    0xc06110d0f050906091903320909060307050d11060c06010320040c080601050a0207080f0c0a12020607020112110415030c03050114010f1103190206160509131409010507 74
    0x80075140c600c1116206da002480c8005001c0c801e130304540012200c107101c45105522140880a4801c0400981245407070700710325040350003002d00e4000640d031420006240d10a60754000c0c1050039a40b100e80c2c584054400400b003903070b082082440002d2032003504100c403a0296124059400800c0c0360700e032051551201121203a44101e082985110b00c06030005c0700250011428a000e507030350b810114060f0b145c03940990000d481407244a040c410040b0000c1200c3e0181d81084031211503030b0f5501e109484500c40c040b030000e90b0190b82048044010340c01201407480d04603440e1004602068000000f805581003135000d0843c403441100c208079415070610400c28184400d0608009550400c0b01c0259000c940102203818404c009515400342d03805203444458055102c0100d90b83ca22903003d0801300d0000c4c1020030300140c030590020035491030b4220408200140c0315600d09060008207410011080341d0322543c5480c0e1a6501d0301c52300302c00c0f20317030145500c100d00220010132241010031000723005181c0da00c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 885161942 1250 885160692 885160711
    0x180905192604030b09010902120d021221091507120b0d120e030f0106140103060b18040b010c02030114090606060a0e040906060824160c06110d0f050906 67
    0x124911030284450191002d43e80c000741c2c00350b203950f100414203005041040020790310054020703100790070b48000103800f08418041d41c04d40e5140c00044180078024000c00d1000c00d052503d411a021210020812595014001208540c5140b0085100b4680740c4419512039000940490560000c483d060040d04180c03401070390800d8100c10365032211024454143d0800c420001203541e20a020b66041001440c05134050b0003c1201540e10340b03400d40146811343c4054007090804000155000046041d036005889078191a21696030980c00c01000f46201d8803664144104011540090b8909100341100051a0451020542071100c01a4903180c4000e15140c8540420050490007a51000680700900c50030340e00801e038212603181c0000a42080d4000401510440c1c40448415018868240c0c4108050200e41e865880c0d1000c40601035241c11440c40108804040840c0010070b558094608814602a20b504220942003c0c0003545c0507420041d401540390414464004000c0c043d02c1d81040d10076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 885163192 1250 885161942 885161993
    0x70c1505060913050c09040c35030702031504080d0c0806040e010b03030f1617430302010605030102030a061d070e131413050f0f0718090519 62
    0x1640c4d896035030740000304018090141080032074100f0241c0f050220241c8581c0c51591072114006000b01e461403c05840040b100b01d41c0a400c003030528000c0200e502c5590042c0c058488002800500403035100003034400c035040d040801a5000c0c0c0361252213000301182c456541c4048504141041005451101200700707050391400c03401000703a5400000716880c440d0500c1d16540c039501c54150018110655030400303001c00c0081c4240071862a040d5000303007403010843c80351085440c0f0300a640c0b01040700303009010000c01403964207000760310000c480940d40e00f0310a2001152031078a51b0f020900703981040e00c4100c0c07030584611050000c00e84400c8507021038088411054864070304800c0003803c10140070901030040c0035102035404110704582203514040150141101682070003c50003941003002c441c00d49003030144501403003034081c01003000c060b061411401060413500306820fa034800000701c0d2200c44010380d16461900011014004a1105803c000d010900f8050f00e00700214024140740c0c43c1d1110b0000c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 885164442 1250 885163192 885163231
    0x2070c030213050712090203030c070602070512060601050717090409110102010c0201110315010c0804062a1101121d060103050c190603020d06030b04060b03010f021809070c15050609 80
    0x1610b00608400c3c03031140446c12210784e00221703045201d00c0308100e0300d038000c140c0c1c08a0704c25000a01907084990643c0c00c0c0060703800b940482a02c548042d035025000030001c1094801094801380d02c1401c1e00319200069191229804c0060212905000111000c213603261214446680a101c0c1807130815003400244002c05180d2030b403000b14400240740030032200c0d00405c4403031503034444c41c610441d03035910581803a4ac1c1c94940c5005040a090f0905100c0c102c07003000b8482c4601042c8140c40c8901c00e50101d0039149070400c203c0107460042c2b542c0750387c0000720381c1e90f90108200c80d02078550155181040015240315411420311764108402c9058041c0524013003640440d41c642200300000c02c03110346240058480024480f0000075124036840500380c03031448010711092002c103502400c1e04060440c001c01c040c06100400d101680101e5250210800c02440110074501f400014564081c00c070f0b01d0900303024425036480c02c03400101815011000c5a13110200510340c01e08003080d40d004095400c034010810803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 885165692 1250 885164442 885164447
    0x81b070620090f0d03090b030705040305070b040602060a050402060906071b060807020604061505060a1101050703050c1c0e030f180a030c090c0c0c18051302181902070c0302130507 79
    0x200d4480d2540240c204d81801004d25101e855004051700d0903100c0c0325600d0801c5080240150094001600d103030080c07440c0002c441284004a030125501074028150239038403803e80d1401001c00610a03600450b0030010214107076901c000401c0114840e00c00004030100d241c42c0d0407842c04041c0c000c5000c2c000000248841140c0000364168465444880401c50701003200f400106504241e014079085000802c4510f84542c11038220b40300c0c1c1c1043d00081000da40c8205041301501c109403044c1c0c05a66040020792012640d0070340751040000d1902021521441c0c0d041c05900c0c2d80d0080720580c1311004045145050011503504403215004203c4c2c2801143d801c40e01c68401d485864480c05000c15601c080c1825040e010b01441400960800e121078602075a80310a0700204410b00a1000c1c05031410001500d4280762050100006401600c3e400c000710b0440c80b0521404000380030a940000c01c0003d90041c24a50b0000308071042c0300c0c0100f1404e40c0d28500c1448070411071580f000741707010b003842c08102d01d403503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 885166942 1250 885165692 885165709
    0x901021c020403020612090c04050f06130606050d0906020408030a0527130923031903050c0a08040c03150c120c0206041106040b0309070f05030703030f081b07062009 73
    0x101c4800d21b81981da00c40c81c060b2441c1612400794650014240000c21543c0031202c02801e03c0340324143c0b468115442c280f0188800c032603c5010301c0f07001c10000e000140142c00c0307075801145507600c121001464103444649851841d00207110780030002c0d0000411070a10000041d85840c0308c080c0049a001441d00040014840072180e60110202561510064180044402c9a224072581c0b440603034112101c08214a443c0d90112441000b0640450150010a44684a810b10800044060504102805500700da4520016100b681c3c45240000d010000c10000d03444005902628800069580709520000d0100d03400e0442c42c144480c40e02c41c0d1102807035004202a5031065000202c245400030720800240c007401aa04000042c610100400501910014415003594010600d151909540300209641e4541500008002031400c59440d0f60042c0030719a81500f0124190b920040c01d0114400b402c140d0b045148161121a11401c02c480c041107100c0111806c580d10090706072401d04801e0105040d40c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 885168192 1250 885166942 885166957
    0x160e040305160206091002100b030a0803061509091501030c050a2120030f28020a030617010912090f050609040b1215060612010b07060b06030901021c0204030206 71
    0x6807480b0b40b0075070455448200b15040d00e1002003090850410040000750799240300300c4140521072400606110510f8000f03016848164460380882c07441c2e583c5424801d243e8400e100d16640d03a00c061142c0a030395a035100d5420701c203620361004600010549800107080d1781d203000c4031405102d001c0259004182d8041b07184d101d0340221604114111807004000801400103140309039089040391407802c04262044021b50061745020003040003520790b0492448034081e0600c0b220044000018181003000c910380180402c0d1515040000307000355110014001e62004c80300b0a40d0340c1e5034501100041244241d44002200040d02d44110403c3c101003003980c008600d40251407252101040d1400150348035008030070003180141c41e15039080c041d5940b150744c804200e40c001c2d50121041d4001542c42c100141075815550b07001481c0e0015910702174409165a2103513030280c0f0104c0e00e552618107280c40e040c1c0194060744243e0b00060341c842e4001c1c5078003500343c0308031120010240100003c01c00759030f030b03401610005c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 885169442 1250 885168192 885168217
    0x90e0d230409090f050d050c1b030a022e0f030f0b012003210103050601060201020711120307051c0e0102011503020613091503060507020a02030a03050306060d050108160e040305 78
    0x200080c500b00004d25440340035004005100e0305042602c0d241c2d212010b000307040000d01c100c0e002c91660302003580e5000681400030782c16a015040a001501d0007002c4007031300d03c01c4520303410030754001ca0080520710580c1410360000f080d03d00c10701c0c0050039030601c6400d030550303041c0c2c0d03082003482021400200842c6110640c0358101030103003035003003005006008075120400d404040000e00048030002c2e0900c1d82c02448140c90740c1c021800002030050040c021601015072141f00107040d01072540821150081034143e402c402d2100744030800000d4420072109000c241d400403001407540c45c000000707124400c00c1030040d045904002e40c41d01c40a60130b22010040c0c0360b044a00c07507195105198600c0044401d81c3c09900d0300350400d403200c1501480f1280c02c50540b40a040240004da60b142006e81c5d9030011504004d415038021131100380030a111304007550700310038000c02031454a9842c02000301910400c1c2c0000b595900304c4028001c0c030303403002006400105810503250f42c1c140b903c1d8902500501603c8081c0300c0c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 885170692 1250 885169442 885169451
    0x120203060109150f031a0f010b0301120c051206060a0f080a060c05160606060e010302030408030621010626071a090a05040e0105150f0307050d060204090e0d230409 72
    0x1d144483c101070724003038199801000055030362810f0810b210501070380780d901e0760441070011541443c8500825410b940402011034656482d1600c81918680400d505582460f0351080102d51b55449102a40f100d9039090300070031140c100101000701240541e48007240d814262030301040740350004141140040e070403080018208042c610203590610501141b0751651a400c1c91050070003042c2c0d07210005440855036218900140100150105e1000380e5024086550500020340c89141c00c00c0aa8403d201500c810ba007002c810841c42400d448481d00f2070150030312101064101d490802e44040d07901c803800d100400320940313060001e58201e44802c0300520800310014400040340c03541103025000b04000f51040040070150401c1d03c3c020f0030300303807900d0380c45105500c1c940b841e52030402440c002c002001030250004502d040300b0009144200141200c50640038000011904614801d0f041c003465280080c25451030b1010307004200d15100c805405246100b4040000d904c4805000e440070307141c80020000707 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 885171942 1250 885170692 885170711
    0x9091506123f04090b030a2f0607030503010509091524100801060e04060320130219080a20090f0306040b060103050c1c090c120203060109 61
    0x1522034200d80403900341885000701500b0340030b1084079512081d030b05880442480000790380c01c003034050303041e41c90741c02d4025010b02080c03182c086203030f0041c26400801011221f4552817070b0b4a844030001100c2c00c2e040c140f41b01d0030201c0b4024014030201d0054003000c0310100e00d041e50aa8014119000c1070003400d0248100e4000110039403400c00540d071145002c04250440c074135109804185502030400311581040b001035220110341401c5011812902e2a03031200340c0c090382440c0080300e0300c2c505c0c006500d40c0300e5190217000011a030035021040090711003c4140148100312400c0c410300703007030742550b110100c0d204020700100c004000907824400f41c020320388101140c90300030b591000b60082980c645050b1070054901500710040c2c40050113101015076030402030702500420103445050489002d0081031551000501a6109a0140c0d501003050111582400340d1003400d48a29020452018801e0359a85031060601030441e1008004080040711007030301455542c00700380c0b512070611590144a0303c420110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 885173192 1250 885171942 885171949
    0x60e0f040f0311060a151d040314070f0b04060606110303060f120d0207050108011d0112170a0e01090e070f030b280321020a030c05010f1a0a0509091506 67
    0x82c000000c03040111200c9017001c2a10310700925140d10030b0310f90003550600000d8010291000404020b40c0c9004148080e60756460588511010700c05104010382d04129500015500501c070214082c010400102140f51a152400131200c494010105001401500c02034100c400000c40350301940075202009204031000c0400c800b8080000d4440c0140a03109500e030008da400128801180e1003641c440005076a56641844035490395588940c24012a40041c0300100c0c5200c0040e180f24814918034011904042203081ea41d01304100d0000000d034002c008c1140d030740c2d1040300034016006101ea0301d800c0f402c0c00040030309040380030a4050280340d02d407948041a40d48011040344e1030400380a0703c403020300015044415a034000c3c0030441b1484100522400e00302c1c2d0014505410007080c0d0014034040c0d45c1900e0985003004c0c03800381100c081d0349a130704c039150301d00f928002c541c0411051041e00c11429030100400c55192100e8100c14020206241086628a400203202d100045401d01e01c01d219101ca0010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 885174442 1250 885173192 885173207
    0xb0c1f0b330d05040b160c0215090a030317010609060e0d14010c0e090906060307270c0c11032806090b010602030a17040f0b180f03040504060e0f040f03 67
    0xd40100d0300011400b61201e003916001984280d2254440340100d035140145000c150001005040014090b44009001400d110f0485e20036001c070b0380075481c2405030500004000ca003980d081280013402c82c0c00100c0032103403480c0d0701038050221400c14900050811600800b44031301c180c0d505200e56411040c2e0020b0101001109950801c16070082c00300862100c1c010f0700e032400100040f40190410f5000035151440403503202e0240380014081e000c4645025040c04d5660301440c0f83d030b6082e20b020002001c01811601c42c1c128903062545460900c03212a040200c40d040d50190700c0e600980080b0f9002038500056084e45c03d280c500b203c0b0341102010306013070407001072030200e10080c2858402000403400030b40000207082d2405081c1d5940100514a9032140d00205041d80d0082c90404005004000078a221100c00c1e0f1122200d61020041c20900c0116880e12464240c021420f4100180902035401d0900451000d8000300050a000d800c141c010601034400081010340820601115041014443c544 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 885175692 1250 885174442 885174529
    0x310021b0f0d091e060c030512041b120b07050c0f0f0703020f0307080a02012006190f1505040f090f030801050a060905030c13060b0c1f0b 61
    0x844081141e03024005680b16807200000011074000040010145403e42c4002d88120311080c1103200c06103000000d07145051403810032428400d0620445000410244070f142c8140d0203884240400c101340140780010341019000082e05184010004000c203000c1071103550070542621788150340355614003c05080101e4020221218003031100245a030940004401003540c0c022601e4254082110040640c0d0b0719041c411003000b40c0040107980c1c00b40d800703600e220b000e0070750891400c000749902d005010304109080300c0d440301c115040081020121014070481d100c0701c192040803c0900c54003200d10158400c10700c180d43c0b1580d11a402c003208005a5041842055484021b9a9503040c5c649400f4003c0c100c24040c0300d021f0803c00c1000035101e071282450030121070015000d4200360103280b085c4030f54254841e243d42940383d2900000103c804c0c80d01c00600201d00c0ea000a02110400c418541c0380040880540705002e60134000b048003140c0e126070316040444070300484c02d034900b201c855031030b55a510340c00c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 885176942 1250 885175692 885175747
    0x313051905210424051306021510061706042c1015030602070203070806070e043b011e0605010219080306240a031d030306031002 57
    0x18803400c01c111000440c02c841181111514488070480d2451012601803031083c2058005603803809042c8004610400c00814100c0c9003603494400140344400e8141040d60096006a202c0c0c0d00201800803040f5003d600240c480c1d462505461421200030042024007944004003140d91010070f000b41e86551040741d03030b040354136002c103035041c40c1c924101c425100c01241001d2601030080c1c922503800d0284101404000801c604240c1142103440d640000c0d008290220703018802c050300071400090400c00c0c0c034410340960351900e1403000404107110030b4403600d03102da10f440c4450514807440c0740d900001c40c10010422105a150103036600581c540900b100104174a008107408101d1085c80d4019001001644d100382c00f12000709440740f4480e408141c1380d13039025103440d20500200342a071810a891416504a40420481d10f10001407811030b070303034001c0d602803005c0303640e92807072040410b981200514600340c010065421450300802083d100c43d13041c000e81c00b1142d070009001444002c14107a2030b9600c0d00e41c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 885178192 1250 885176942 885176983
    0x108070c11010522140a0e040309060503070507021306230310151e0501031406031c020a0203010f0207050c01020a0b040b07110d120b0402040803090d0314070f02040b010309030203031305 82
    0x100d005c1800d0b11040e410140c0106032442c070104120308594521400b440d45a99048040c5240480454513500094155001c02104110f030300c0c0541e4401c0c011406054110000161700c3c0e141000f10703100400c08040c0f254184200f00c00c0690659070206008220040101c4c0201d1080d28150602007080700e95003040120510041442100980388c400d00c030180e6000381c030100101030006502c207190f0307034007150410750540c010800c28202030703066510b065980006004035602508541c3c0000d0035942126040301d00c1c140c0c0400d5050030f003c01000100807441c8c084c0040c254015460312032000f00800200050b00c1032600c4404190704030303c02d650418241d8010401e0b5001c1900f0340780020840080d041524540ba402d02940c0384041c50284201e408450b280d9008500d444001310500000609806040d000e103e0346c00bc0300c1141d04003290003452600c0c070417030000a41403514810030084500c07a5490904151525410000181d0004101d039040008041901c2d040d044900d4003603d001104840c07852025802c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 885179442 1250 885178192 885178199
    0x6060305061e0609060f01110102130b07052b0302030615030106030b0310180209090c0409030915090f030f141c110a020a0b2212020108070c11010522 66
    0x145000d41d0903006100710041c0050b00d8560404c11109020f469996010510400000340d66002e83c0c0034101c1c0080b0304001500b031003001c42d86641e8601c0c059101c2e41c1c4142000451504011050102d861401030901d18512095520a03880c200005c02014110905900101140d00d540d40c030010140200b5451444607a00e43e19001c0c0200900b41010096002748218041c1c00c58180d1103006800080301e01030400c0e0203119440d02002402c00006d0a0035015000e01e40d0150325a4403640a1450b41900940390903120510700560960a07088c100071050400c00031443c140003007200201c00004494101c00450462103090404100c0e800f4104641405440b130504d031846066a100507440201c0202d454983c20f04c00214441074456100d000d00030350107500310074280070b102d240c01c0241590804043c4600c0c5c80e5905501e070f800401c8901c0d0868040d03041ca02085108540e48640c03a80c3e4041c2052406903100c0b00c07281d907090410007240070020706016011400d6490f410300c1400c0082800900701c08039000555 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 885180692 1250 885179442 885179461
    0x8060f161116050f09160f0302070606150908010506060f070503390c102613060c2105070e1c02030607020d050a18080f0105060a06030c0206060d0606030506 69
    0x502d44146402082e4000c00ca501c980780c03007400c1901c514a89a009504010040d80031035908051803150010306500744800004620144510343c081c0c10040110341142e02c401038050407080a0784c0c0281416030404d0108056a00d03000251a014a45240780c80e0315005580341440c00c0d4022040c0142c002c0b10305041042844824540041c0c601e40c071214450138088290349010348902d190074089400008184400a0b8140318404802c0c3c59050048400580e0b094245030101010095503100140d0705170a440e0300501ca00707031180045055140c14020118117164440594840340907040e50386e000c0da5500000d6055000e010f9410f00f500008041090340d404001a1011405180c08168000d1140710009000b0500018404541010070b848407400c082c010724040301c04c05203908116222032046440001c410504000c030800482d1a0000440d00785080c3c000d01c8055081940b001c1b08060902c880c1030190b0750003040345500400241c825621000719418604050070550340010024441d190402c415902c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 885181942 1250 885180692 885180733
    0xc050d08040b1215030703230a050307030f0215070e12100c12050709050a030803060301090f0305221a033d09021c3305010908060f1611 60
    0x144500854601e00c4c109205040d901c1e0b5042c00010030010484400c000108040c0341c0e518100c51180701112200220766807042e003560000b4400701d01040805034890b04040e01805015040140c500f01810316103010507008000c940d9403032086001e4138040d4000d101c00e0800b4080c02020440c0310605101410080c18028107034500000301c030035468a070501050026202d52004022510f00400e004401825911a5603865101803e010790565a440240d0005801074945200641c040d4881d540c5804908500186100b141d1a000200303042801060010050599001e0b150f10284900c0c50f460343d80c1d00c003d8007071800a07105070440030104014280c40005003284500d10003517100c46070600d46130740d459038042a0b0040c01c10b9040e5041c000c060700b0702040b00c0c50f4004500340a81d10811207605c8601428a0f160440706002006004905c4c0014080c95800405c07003401041e803c00205114504105000190f40c400f8055002e022a0b8462405601d4843c00420b0441182d58058034881c03041c0c258040c0c41d44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 885183192 1250 885181942 885181951
    0x5010b1c0510050f072604060e0d020c03031c0e0f010203100b03132d0605070e030309180c0d0f05190903022107060e0d08060901030c050d08040b12 65
    0x144250715607000c0504140c000c00d401100d8203941480161901c1c101a582d0a1302e80c40d4098480e06d20125108055100e640000e0082c0d00074000020fa080026048604007580ca100c6e480c290b622003100102c142e20004102c580c02c00d2000a08403100300c40c1902c001c0030b402090790212a500c02c44000300200380042d0700940c000d0a1100800000c240e4070740c0c44402e2800704031803954540e40d01c4403d03040481d0007440c0fa0f400d826010780140e210000d00003541034841c54181416280c0c02e517240104080a40c0001c05d020222600710300440c10103441c100040c64030704044000d080031101001c00f08595980d030a09817100d41032850400c2c415001c41c04200802401c084810b114100c035a80498503a9907a248102550b40d90190f001d45102a0040e00c0d00d000045005683c20f0b201d5000c00000000c900c00e445048104000c040103001c41521106000f009084007500e20317885440f6010040002828102c4180300b00c400c141e0300d4120400041c20300b40c1550150364041032004000141481080c0840310a0500c203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 885184442 1250 885183192 885183203
    0x60616080318070609060909110f03090a050105090102391c0f05090d1112120c160503030d050c090904050a1b0f120c05100f030b03010209130905010b1c 67
    0x425502c81007200c505480e44a00008101f101c032040c42908600d4104040101c2c0541c1800d00e0520108512591a80110350400342e41e0402070341c070400c10000b80581600a8802c030025030801313280f4020740c00075084c0c0ea40d0340e040e038014000302d114001034030300300c82d4088461041c19101920035283c80414034070b954600400c00502ca80f401a0400d900500940e20b080501034040141c80c0401e6450004c03950307884c1308042d4803411380d00440355000b008010307a514003480c0c011116210079984600c1460701c0c43c07c486521034564418400c0c00036031400016900c054103c4c0801181c6502c6072060380046215642940782c02000c080104020301000198281071a840b6500a02c04c0540c5403d500340610440d000b110000c83c140001004603c00e070a50031068640111103c00c0745a030b4070800034901007841c0138414042489014480580741d0144100410741c08240d0080d4901551940007813070b43d002200c000c0c00029034440d090020f021095001000c42030018048054554542030003140211003500110740 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 885185692 1250 885184442 885184453
    0x906070203041710090b01080c1e010804060b090907060e120a1e06050109020711010315060e01090e070810090e1009061401030b01091d1902030a060c030213120209060616080318 78
    0x101400e10780510358520b8ada22041e10040d0403440700441d04c041d400760080c0d82c001d80f107030360710703c0a9519140540e0188c01d81d0801010b80c2c500d4100d0103002c01c1c080f44455440384020080e285040390780401da11a07183e40c00003c2d10840402d43d1022240f18506000240240c0c0c9000004509500aa03006040c8540941e001144600d100c00046056907003044110b808120540410000385016562001c403400b0f05041c00101075441e001001d200d088211030110009072024140080c0c80d0305034103114090040f0460a111665078040c62a075100000c841c08218a5603c00c03402051010030351111036841c038010801d69095a43c0c0c00d000001004c01c0c02043c40341403412040c1c85201d1101d0407000100d85018024001d038034805031340034980300f022881c2641c141c01803000440018a0318030030880141c00b01d032001610303090014104503424003682c01007101c0400002440e80580e4810030300c0c0380d101104940c450350b24150840340c1d484082d04030303c0041582c0008001c0c08030755414120548802c0040004549 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 885186942 1250 885185692 885185713
    0x5161e080105071706010c050f0a11090714030a02071b03060b04150b0a110d09030b01050a0608130204020d06030503030402040e06040b07081f0311090906070203041710090b0108 78
    0x2401c0700d00540f2500c022866401c080ca072814000d6903040c0c0c0c0007505041c0b10110b05800e03115907051104e041321040f20f5400001c0c12004025001c80f03032038900e20b0103642c804100d10300900094804603a08a08404008010002800610b880e40486d00620f82c8840010502900d80165501e44d50007802308940c0141041506000c2d07003401c0c03090100280c800c01e06010800c1c640040320446038000801c1d101000040140c2c0310034034208204000c0c4c04031403540c900076140c0c91410032482e03409040e00010f1140500c00c0080045135031200390540c000c403248129500244183c80020028450b00e1072002e411340c20884000709010001c40a58883c0307000307440910840c00d1a26000740c0301d401c1114001e1803000300402040c01030388150441e5500645900f41005040100c0c06410001c403100e500403500c4c4001c4030340ca980035080c06014150000c45140c01015141800d13a00a905c1c5d000e603004030084910141d20303041d01c0920411200003120100c1c0c00810900b4000c0c14070384c00f02e842c00d0003860f19510802400c0f1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 885188192 1250 885186942 885186959
    0x11120a03052707050f1305040503030108010e0a15181403220312080403050d09200d230106031e120503010f0501030905030c01050a050601090501080c04030206030405161e 75
    0x110b0014492101902c031181c103040400c003460840f100200c0c0c2154103216181e413003440b18440c01d8080c82c0500d00030340d220740c5400441420f44c0ca428240e01200d400029404001034440464500071440904c40410621207594000001504801d4050070900030042000701031302010000b008111550405403079a6000404184814051031000520b2110703402100c1c00100e01c03034060180c01503c07920f8814900500c103240d900c180c43c9031080517235420000401c0c3d0340c0201158008104c40401c10f54096080785621f441b07200701003011440c1d48100c014103d040504050b4294810000707543d010300c44c0b2891010240300000c2d0aa005038044400c4510180350f081058094030a49040741d010443c841d202904240c0110003a000700b400031034440c40140500c4030002002e000c1d891007805080380008880c60600300060511440d0b60009050000b00c50034000b50313000b13050403181a41e030151011541c13502c4502e0201e180c207021011640300095642e9011491074402c1c0d0402400134450526080c1994441115 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 885189442 1250 885188192 885188251
    0x90608030c03030c0a0210060308181f1209060e0105010e1e0a0f09120e0f0a0503030403060507020a020307060806040f020306010f11010204090f02220803030711120a0305 75
    0x30b03803051001031072050b8440001d006007000784c030684182c81582c4a8501c01d5030141c1c0c00031038070305074003140d540090048460180c0d1403c40450f0102000207107040000300101d03800c103080d000c0080c0d104a486111950341c00107104240d0040c030410a1241e06e42c10796000381402e0285085980c09200482d03145a0000140c0c040c440c1855000b442d26242c008049009181440f6582030341c0380c0310103130000490f4000401d0112606141c482a620707208410801019041c044152171055202003c140b00a45001066506680d80300c4000200c42c2c0701c40805a1900ca401d8000a51600c12450040341c066407000700325010341030030b84051088000d403402d510141d010448049000509920150485c28400c1100c49080c0315107100052505071615020803e5811240c0046003e1b0340016100e0b409090741a60000d400141d008180d5055040201c80c0d51240b002400c10400c010f041444881401424001a05130811031400182c0c0e5551200d070107405070808880310013421000d9030a01d01441c000984 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 885190692 1250 885189442 885189457
    0xf060c14070f02090604150e09070302120f121303030e150a1d010c0209070c021927050108070611010e19050606090601090501031a0406080f120f0f0f070204140109060803 75
    0x80001f090401d0f115184080001380b951140380f28a820000250312810900324001c00164050701c0110360761844940307082150308603610400030410641e40d1401003821f0800036a60300d8034200640d500350f50000340840301503501504211a0010301c1130281038001d5060b401003080d020b850011060300200544104040020194114405d00002075249214195080410b440180507940030b4201660084869085800102e150f554000c1e444282c0760f00d4183d0b02c02060900d41d41031161b58142a01076881e1842885064140129140e0001c21041c083d00800c04582803c0c0403908217000d481410a4600c1440d0303000d40d02401118013107074031410002041c1d8400c1d0307410303147c0f400079030b01d4200110f00070120910100c89980103c400a5600d40d114015075004001c0f130320060542d484d8201c0311383e00b003c005d04c01c1051105420032044403400301c41c109462248404000d1a07440e2040100035243c5807107035a02c0203600500d01006d01c1007005111440c0c0d4181c0390012010441c1b40c0e2500b4420b680da110340813 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 885191942 1250 885190692 885190721
    0x705090a0504080f0901111e07090213090b0105040b0c030301210203070509090708070305060406060e010e041533050f0d0212010b03030f12060d0f060c14070f02090604 74
    0x2084a600340c1281c8010001c5c458189000003194001d214810304118940141400303a51030100100e0003868100400409001c891100314501448510b040c44000c4e01840786e15101c0d42c03180c400401aa009209580c000c00755000300c1035075100700f2828039841c0e6100b40107c0f4211501480c142c00c0501d0703110401050164041c0041140605040402c080703082c0080c80040e1310f00c28000e010170003030000e00240c0700541c0300c0d0004091900305440c07d00c041d5840380e00817400d1420048010043d011303019a80c20382242e004000130050703005000c68400035084109111001310202c201100c008001030110280240032540c2c0d0130751881d220010090840200e1000560000500b4100000340c82c02c7c2060b0521100d00c1000010004000800310b0308623013002031404007581010681e40500804940e0702640b00d0070444200c590603c0540d9040000c488070742c3c025044946d580c84403140140030344c1031303403040d90715008506864a086150003d40b0307550b10b8078228007400d8880b01290b101c3c01e1600500e800000120b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 885193192 1250 885191942 885191947
    0xe060a090812120f04061112090105610f030608100b1c14010c02071a1308061302180f130f0f0305030114190b0d020415020705090a050408 61
    0x706240501c900029205546d040d80d683d4444c40c41f40000001015481a0006445141c0c5082c0241da42141c3d4010024902c248240549014085000e0f40d80c40350421355550081c82008850307034100255100c2e0401058000c01d10300403001e82100d8480c5583d90203507994070b9407480780c60480120242c4049114000065000c001020046041c94100110a10024018040b030382071105058111a81c1c100d0207030340200d072a6040b4241c1c1a000c0c0959508481a400180720032490060b0342c803405203034525000c04410300421707515500d145019440004000260440715581440f0301c0c0b0200400c1d510344102d10501c5210030018415a00d44001449400e00640150003992003035910b0580b68003040085038820680c5c03c944002402441c40c441201d402565681c1d125070409a18215400b9503000141c401c56805003a8200034602c54103040540d44130103042034541640705100c00190040c1e800114181c02c60722030b42003d0541c00078025048034801c0750300302a0307621042c210f00c0c1101d0050380c014240f03c208 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 885194442 1250 885193192 885193201
    0x70b03190b0303030709030b0f010e15060d060611010e010e06071812060902040e19080a020c130504060c0c0503040302010507030e0913050d170f06010e060a09081212 73
    0x1440320305600210a03201040d500c20410010341194000c40300a408903281d11818800d04c02c0104460b07502c104034800d2030400d941040340b15045100c0041600d4040c0c07070b01482d40040354403100d00366228810300304014404152180d01c050030b1042420703501c42580d80303004c02c0382039294014081e400850380c21101a0400703444452040700c4080c20301328a100a024904400229171581c4008100140e00400d400190701b005441000107030f03941c0d40807964180d401800403082030400030002904069000451a6407840800816410010200a040d41c00602480041500513450b0015817146226050411860a000c1c0f01660050440c20000d00303194018401800103500038401070401c1070090034109042c0c0d15110014846403000c80d44190b01c100d00340000010424100402c254020280c186003c8020310b010700020200001000050341190f0304d8089103242c2d01909107580809000f4208651307804d410800a450a440c510481c00588250301c403070340c1000800d00c00c0d40c15031514500c12075081d44a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 885195692 1250 885194442 885194461
    0x92a040f12030302070c0f05011d0105181207060203070506090d0c15020412080a0e0907230c1207030806091311012d1418270a091202070b03 62
    0x60607812020b241e420000303400400e100384040070045c41d020290306452800c00c1c000505501d0b02c2e000d030700b1055a0803c3d9800107aa009005c4c2c8151801e0800c2034058005a03200068481c4a03100b40381509004000d0082031040e800b000900c8414002c0301207489945890980302d903904056400c00d00010010503a001c002807445089010b0110140800750a261311028042d903070004450b42110034190008103002e2281d0000c404001e1304030100e40c8001c0301d00c0c0c9048090480308540d480e81507040030070307441103103c491644255000d0f03208100c04c45240ca400710210420962210390154045408a00091218030341050b103680b20382d016042810f10f51590b039442e4194920070b1460b180c18001c6001c51110810901c050400e1102c00f940a00d003030705d400d00b00016102c5101800f80100307002c001c100162404c1c281d072480c210401e80989082c408a160003100700c400c4002500b40322400302d030407010b000500d1221f810101030300380180311900b4038503481c1c10180d0ba540094841e0803d20076042c00000c1c002003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 885196942 1250 885195692 885195719
    0x30c05060a0215092406130b06031612060e0105150403050a0605071b080a140301030203030f090d080c010606080108010e0601140315090d0f020a050303010311010e092a040f 76
    0x24130400f1104a06030108107001c610891001d034050f007440d01410040300e85001c100741000744d40d10640410210454502044031407000800c9207503044e004c01c01d040e940701c0c17191000c0040e5040a0384d08002c00c0e512510640d41040f428440c040c441c54600d5410b090340360b580811a000c8a610200a01741c041c0c45a8070703040034000c004c00a00501c4800c980600440d2024000380740e00d184520795180e0b4640200c82d026025020500030407140c1e030010302c0180016100081119040c000420900d83c82c0e104020004507800804071008001ea000800c148054040540015059070607586824406c0e80e01e4901803400c03501503501e00f101943c032010040081c030410000340c14403840c0c00340c01d4400c03200e4001017040c1074081c15075100485a00c000c095002c00755010fa4080092403161000e04428443c41d121030f640e9000601028114a16665040d10035038000c145180c05d07114003406020003460181c4400380300410103074011140c40c8132410410384040e102000c036026141250340e07034070910342498070080412 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 885198192 1250 885196942 885196951
    0xb010e10021b15030f072c0d05010209060711090f040f02150d02072006030105010f050a091203170c09150306040e0102031602070e071205100e07020304030c05060a0215 74
    0x85400407001006610b44001314854841941078411a00300424000c08581011071030f11180945004a0284040300307520700f20740f0300c600b00c4510015240e00c0c140340e40288520112035078006070000e403180130080f6401c1552403010b400c40d400302c040da07a10b058100c403086040383c006010f107079100a98001481e00346108007481c0702e5003140900304645031001ca02242e000c00c005444a481608010f25400d10700710b010150881d080c2c40f15401d5500d0000007a141c40080403412040c001c0214444020134814000c840c003c20105004101550300c0c1c2c18040c01c0e100341110910f01703803074044000501c4482c02d5001c4640114000c0c0c0010301301c00044441c0c0e250b0b900301805c110351190300c804155a01000134005540200700b80513454032000210a0043d10b81310555000390345904501040100450b001601504400307510000401c0540c0d650a09010b0b482058211a0400b0048810b01910980c00005042624801d030b0103100400d03100e0040164a0044a0015005a102d2150740c3c010501d0902c150340c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 885199442 1250 885198192 885198199
    0x108060d1401061e120b04081608040306020a0215071d0307030b043002070312230a0e030a0503040b0a0504030f0b04021e03060c1b0f010b010e10021b 66
    0x10404014550030344a00d540094010841a045066181d0312044440700030080c600c1c2400d005d1400e030340d030110100070042c00900840d2001c030326001c504c1000d28110100e282d200c1403080c0d50366202c0c6018002134220030140d0005215414050a0b080ea02007003440c0103034610344800345650440206048810800070fa039076014000c400340000000d80600c00c1501852046c004407068902d4041c20f0802c4800c010143c002030b801c0d42e03010011041c1c0109000d0203076500a07240000445110740140caa02601118030030032940218a00d8125649840c05465010425550b05604048503402c0603660041403802030080d0f041044200f10041200000b0701a040550620504159072900c81092041c0090b40580b01c8011400c104421454818841e00781184040746070105941e485011a0340e030301000f0010407a80000040c0e5146501d002e200c610310f091000e4080743d2b401481108100e010301000303240b090100f56034a0200312540f9154100c0c110384551580140448031101c968261402c8008003070b81d40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 885200692 1250 885199442 885199463
    0x2030a0605040f0614010801140409020f06070605060102010501050d0c150e0a060c030306050405041112101812050a080708061503070503061302130306020f0d0516120b0108060d 78
    0x415032030b2400380301da000c5030048000444500d4a2504d503040c40841e01e00e1410498140014454a502c0410a4296590942d00043c42504902c00320b80601d603e0341005604c05c0010460804001c01070b004036214900c02c0c0e00030b00599a0f103005010728034040340d00041c28450943c00900418060310821721181c562494154251032010000c682c0c0340b582ca402801c0068030b1109084185609030084200405007914100321b14507041d01c031a10b4281c100080075120754080c9900302e03242201000f1f0a02016509101004044200300360402d1140458070210f8040003c0040140c0a502034010382e07411704026110305009036a9407070100c0d1150345c018542903204ca540c2c500810700c414020701861040d01280c4645590f4240701082004d80c1d12102010902d40c0c1c0100300250ba00251143d00340c00303c0c0e5102101684810580d0f0600d4100e00542c00303c481c00d280742604015910b405a11503031010102e03038a80b5030a4a0400d8540c2054405805220380441d00341070109038075050524020036018010200d106 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 885201942 1250 885200692 885200699
    0x606110c0f0316120b070203030c0d1a270c03070f110316061410051c02010c050604030f0f02010b0d0f032f1e0a03081009091506051e0402030a06 64
    0x107180b041650080c031012510513442400300043d0858042e040b65890000f541180380060340f4190600c00d5138880b03071495440714602000700710480d08918981b24024210f0343d94080141c0c201100700d50360071418998802890104a11003c05c0e01228064510f544e00c10f02040c427210026100203101d0000a01248010000e0081805101000444c4070b07102e0040440e80d04030010740d2001d0081d016200020004040d42c0c02c00c11a950301e089000320449420300c481c001e215a00042c1c0d1004c0106002825900030901007000705540480380400001c61034031480104110040700b02e08842c1844201900800b039080300d00d01040b840001178010900c2464078640107070b00354060058074122140710b000000401c0101481990090024122002180452486600c0322070340071079807001130750005400c2c00400404176600c0d041e128513801c00351801207030038400f4200794500482c18a80d4056002581490b00901007000c1c0f50070100380281c00c0c80b400f690f4140c80c0040c01000000c0d44040c0c000c0c0207040e540c00c00003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 885203192 1250 885201942 885201973
    0x21f0909150e060910031b030519021005041202010c170c070f1a03061905090906041b0308031f08070b030a0e01050601120218040501030f05010606110c0f03 69
    0x400c503008440524204900c0e018945000c2c0308040c1010b40305441850400c0710b51a5a014401c048070381080366080c01c01d043e00d4132041b02c0755440d000640240140b0344008046c1c5083c01480c05614803d0360b10180900104c40216000e00490080381022501c0702400000340d8441c01242110600849a02c0118280c036001e940031a80241141000c540000e03804002201800031074100a10181001e0080e10300c4048203070002c1d1200410041c400c196900540d058482c903881030724090400501140424140852060350701c0008884c100e4050740156003140c61060360f004030b20100d039440b01000b400c5440d1000c1448469441110b6075641420012000801ba8010031412008001c003e8003203580c0e080505120b0141c0e6185d24440150f40e040c1410b00c06141d0b0300c4051071b100c4007031102c0010785646130215071404100d5404501035106040c400040180001956044101403080c0e000f00030141d525201a00c0b0f80004c1400b403000da8002c04040641401d004640b03c1007110006c01751601000402e911 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 885204442 1250 885203192 885203201
    0x290706060f0e0612160905040812010f082503110103110310061101050f01063b58060207141b27070e041107021f0909 52
    0x4a00e204208824043d4508100c0b40b400c01c00585103005c0c004120310350042c1350000030035101e01c004050b0f6403400501800300300380c207980b45c04c940701096000310750b580d00801c40f00c2005e901034100c0a01480d80894194213940405010800080300030049952540c1c64103d007084441b4400c1707050640320023860200000303400041d88a00f40c81e0070500b44031820181b000349061154540701129030301d00800e00c940c20303440e5181d00e03045501c40d28049907078202081003503c001e0035895450781540c01e103034601c12880c0e00c09284503042100503035400010910100d1025076285100d82402d1603440c2c02110400804082c240147c4100740540684007095902202ca0241d007070325040070340703d4549c081200e0040001500c10300e800545800000c1c0001403411500403941e0301c0030955544611034100c2c8001c0b4540000c0440720065180c07441e015528580407130301400c400031040c042e03071107585000f10b841d90342444141035079040f0b60003800e07010800c2200303500924451105107110042c403100040008500703409008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 885205692 1250 885204442 885204449
    0xd11030912060712020405060702090408220e090d0e120106180903090e0106020601051903060e150c0412020609010201091b03060b011407061d03130f290706060f 71
    0x40c4198a0b2100005046180030501c4001c1343e4010881042580c1d240403d9a40d013540483d003550713180c0c5603450030400910401c032200040701c1000c1528110003440051040c01c442c1d0300b041903591a520001d11649a0303031824020004a0400c9443c00c500f0f0a1580041c50462603550001551588603400004c103c0390003007c241201340c480d40c000d410903038845440001001c81000840203941440b10181d01c50005000305c500960103000307030104d04840f481200b0019500840200004401844842e4442c1d00c002d00307140e0402144404200c0c0300b8001421030701200c003020030704441c02016038200141a07100042281c11990be840800021500c000c101c640c00030040d20308054050b2071450508195120b081019051240c1d0440001203450341500f01d0349071980c018000580c40b04220449100a1911840c480a9100129441d440725000850b02c00544401c1d0001a0010ba81d0341d612411074140025840300c1e002c500501c9100d0025101c2c00303404498820040401d0306619800a0f403c004113360 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 885206942 1250 885205692 885205729
    0x18030c0a09020408010b0102030415080a090b04050c1206091e070e1815060f012102030c0d06080606031509120d1b03150b1b010905010b1002070501020d110309 70
    0x3e8100b1895909214144903e0000e002442c03c007442c0c0111482c3e4408078900850600288200181d80384a8075407000c001554861440740a50410b41402d940d6000c24051140c015080000120300815002031803a01c5403104e0030007481c83c811031023550200c402c0a5480f5491921420801088059a41619510402020004c00d1881500b40d426078a040e01746080c415071000700c0001c0c005e0300c0d240d4503480008400e0a092500f8240c0904e0703c0044843c1d000341ca00003d0500c040700b4803100d42401c000801420540c00824800d654980302d0003621020f094480036419400103d80c564086c0c048900160310510500c20341d0884642007051101c542e104401d903a003081e0751420440b543c1040320105200046462a0801122076601400c40c89013010f409000780784c1c01d000c20f50040402c00b5200034440001800000d000d803040d0303403400f180605181407401e8030440b01c501d40300900a1000584a0407580168010309000c802000c1c00e03070304404a80c0308104240810084144203031140481c00002c1c02d07480 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 885208192 1250 885206942 885206947
    0x303070807090e0702070501112104260c0103051e010b0301030210050a0801061409030a0828050a0f0903240b060703140a09170109110405060618030c0a0902 69
    0x854002c00c10025038000d400e03c0301d00700052101d010340c000340d04410385100b800e20700850080841c2c030500c3e182c071000c00c3c0c10401c1100b40745800e200e480711002d00225003d6403d048442100300004280144685424201e207521090303003000385611980219401490401c5220352040705030940f0000e1150076040380c0001c1a00000400847c10072040d25404c901c1e0515003982000f42180e801801c011040c450f030001c0212500c0035601c60010101102c03c1041e0003401c407405200c0c00d19010640f5040300803001c64040850500224007105040c0c1c3c29112801c0c2e9485500d020036289080d1154008203580000300880d4010100c00a182f48480089810120601d510000e042150100c2510704541c1c000c0d008080510035200002c1d0050412004280840080340d190700160000301d40324203e6521004c22566407000e800400001944208415805105042110b020145c140416902d01341c545030b4004004226401024007007440c8140c101c02d000b010754600018060000b101003245400400300d0a500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 885209442 1250 885208192 885208201
    0x40912020304080d0801150c0501020f0a090302040b010206010e19090605040f02130b0f0409140102040b070c060201140103240f0c020105100528030510020706050a140a09050c0303030708 82
    0x1082103401d48040c1c0e1620f4005c0d0740c100880c1256840f0180d0030070040c8181c09100100f000f6003074064616000280b442d41da180c8518074402040c107080391000342d0040e86400d500070f101d5440072070210705039950007070714580a4488694010a031070885105910080d0341d0902c03800001c5480c060203024900481d81034005103a980104000000e00c2d840d03015100d441c0614500864403050940c85543c802214001040551824041c1400c144040b03809565407000401141500012003d403102034020000141c00d80d0300d40720268200d0380081e42c1800354043c3c60b001003000074442115443e0801201d0703202208a0500140c400c1605c07a400003250000791200310131140d8a42c24820140c0c810780c58001980300711310380800b103080d560131121001801500441844296034094261a00840c1d008003252981c0c4844801e04000b50045241103910ba070410000ca044842503000d01122110982c000d0170203610740400380c500a01e0b81031012a45400749003184030701a90240050361040c6030907143c039078007840e2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 885210692 1250 885209442 885209459
    0x90109060303170105091801020415090303080a0b130e030c1b10020a0b070f14030415060e07090b090409060905030d060b0a09030209060a080109150e0102090915040912020304 77
    0x1903081032102c3c40d000040150f951500e84a0303401403402076191040070407242c50305004e03202e01c0c0c20055910410551140303026600c0400301044034000c0d541c5c1c040940320002080c060b00c84180d80682d1103d44503120f50540d95050b40324880c1013586004032403401360590300c402d0810310a0500c0c0c04a0041d5103001035581e04010f5054541c0300050310240404103c0d9030b0b22003d00c194050300b05003c0007041e040100c41c0fa805842c100c0c401002843d05e07545c49241610309400700082034090404541e040000c00134480d18440081c82c0620600c0e12061003050900b903100c0d001350000c64500368011345a0f0240c8000c80c1c0340d0310078118950f0154000c0e50303880030415103040c00e8464035800b803840c0d02e0081105601c0154810441c01c292541103078070300925215400003a240d1502c0741c00004055183c404e12038100030714400180d00850100c2420300040d010a4145c038201c0c0030302668550010000e100040e60441922400c6000000040c000074940c02c5580f03881d111989001e00c1b078009039000050500c010031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 885211942 1250 885210692 885210707
    0x705211902210a050d020f0906030103050c03100b090403230f090909070303090b1c0e0307020406050604060c060b120d170609011d04020f060a030c0909050c0a08090c090109060303 79
    0x4100b40e111031502c824841c00411a11a45501d002c0413540032981c0d03a11341120004580f5214130003440103031656140c0c05d0407a1140c01d90500c0300d209210340b4000c1c0110312100d01841544100051000200d80c4d0782c0c0e1016510302030002040312003030300380a82a00d48201d4a0020309550b100700a43c1f01d07102c80c10310060116002001e80030001545c001e560810000303921144c10003e031a01040742d90b850b680c0b01d800040c40100c0c2542c00460031801c1c01d02070039480300000064030495000701d03014451195503c3c1400302074441c9024010025070002100404500c49070001034840f10041c01012801003422426404d240180c7d04d00c0c1d000441e208a41941e0110184280c0d401032070480f009909545822511001c520b001781030001c3d04d00300301e0001029035660800c2085103ca01070403c65841255401c0200200003104a41c03003c100842c00100e841e07500da225091048642c201d0f80e91030f01032441010f40306800000c01d5130103d445513645c410101e8840d806410300801e2008000b14074542140742c05800c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 885213192 1250 885211942 885211993
    0x80a050f12040320030d030218090115180b030f0912160b0403030b0406030615060309021c05120d05010f0501020c24070816060b060705211902 63
    0x6500881041406900d48402c480440e90302507a0010140700b1258500c08048a03400310581c140190b600d00028580c00d500240368072107076010103891560854081190000c005e0052110000c40514030b8045c09010702400c4203013110316030300407100703035524003054003d41d0040324018201c102c0482802440302c020442d01700210341e8400ca140c100701c02000d200100900d417002c003410000a18000c1001c0c14000d510900c100f01c00580b007409426140c1c2403650180c5580f50450304114620000001c001f880f900c103800600d40d0082014880014440548006490300b40054600f0301070366505400c480000d000800e001c2035100301c0440d10b580340400d43c8410303030703400e911880c190f42141021000c950345074000f0395001800488170b4041001905400d0380315014070400281204400282460090035814a80301982c0c451002802a280c18505101590103000d130000d0030b030340c402408082141149901f042c1d14480c1405402c0c2810071815144804080d0b00c000080940c01c002a40c0b2151100381c022001070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 885214442 1250 885213192 885213223
    0x120309061c0b010c05100c200114070c0f300206060a0f0e070f1814033c0c040501030f0b07031e02160b0106090905130209060f0409020307080a05 64
    0x11307043d43d413901c5859050182c00181c265a994006540c03150140001b4901080c28031550b00c0f601d40444031581c003d207c4035480910140350070001070a443d02c2004240700455202d940890354100a80e00d03102c944102d07814003400c08000368282c01810380040300c9004882c3c03869006105900705802030008804007a080100500c444900c10f2001ca40b04141d025000728251402100b1601c02183c110b865800d00005c3d2000340482d10000101000e04e04084c03202e0340b0044042d94028101000c2e0074070002c24000e011030310a000c507280005d081e80075507002c09446003944184d41c845c42247c400203040f100240c104942c0d4403486e2024400784020503164a80c010b856041c1000035000010403a400704d000340403405043d90700043c60000100c560310216141d942c0c4510000c015585444025000501e0f501852804501e400001a0201c113490300c035008031500a80b000110b1784803c400c3c4a40800e90403500303a0026200c40740600140c400300503140040010801802d107007141da1420f41e0514510002c00d181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 885215692 1250 885214442 885214457
    0xe030f13090902060f0d0b090c0c12040518040606050a090c08061516110d03090e160903020609210d031103061806030f030301090f1112010302120309061c0b01 70
    0x144c507464126141119070166080e2030f103a201152002421a0440c810382020001003407001ca8599030002e008080940015102c00e580b4992510314a8000e501c543c6503c00c0590780310b0400103509900d115041802140003040f407a442d000412404911907002000c10307079454a400d9106036004c2301c0c0c5034002d1400c031340c261251083e0b100078644900542c62040d811050000c1c84204224242a4184c4081c80203000307800881d1042c1406005002148200c0020034005400202510075418000300748881d85e4490001305401c64003400b83d507400400385960002a420100c07003034091014028091440c040b0010503041d40d1341600102a108042c1410510700018401d110444d59151401d84441a00358510a03481e92a540001c0c6003080341c60660410340400000402d401000341c011020710f508010060050f00492040c05003a845000b0281480480a00c010f100500e0130704400000084501c0450781409494400611309034030a20880600840c05281d4201644103030281c0070f0b00232800d00302840d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 885216942 1250 885215692 885215711
    0xa11070b0a2c0d290408071406040804260307140c01090815040501090f030908120a1d12120403021305040b070c0501021908040c23130e030f1309 64
    0x2c02100103c9002041039906501407a0803083c002052140e0420324407103095182824242a440e550012030150f495002018881d46131807400510a40150380c80403d070f6190a2038280009500841940b201c0d211003624801c1380b00480080014105190191041a80031349005044a1505450180d0603050001d1600c0030407520740d02180b00710300303603142c0501c40d6803543e16890400c0c010402400001d021029500400c0d0034140e10801c1041a40d601c40119280364003001e001e80380d1f030b000b03800d8a54002491078224442d00030781002c80200000e070150084c0501b407401d103c5181003a841306e07150709044101180c20400d62902c81443c840341c3d9000e200030003160a003902c0c0c01402c8800100707130030144510200c1d500204002581203811052001d8205080301d1a42e110052000d1001c0c1c0341910700c0e255126001c502440e15581208003452410b0800114000340800c3c401c01c180030b180e03424140c541e0f801d0780141102041c80101480203035442c2180e512180c1031700c1480310710b036560400c040303d901d0070440c01d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 885218192 1250 885216942 885216949
    0x9150a0e0115050d03111006030b04111c110a08060a0f3e040302130b030606120c150d020d020705070e1303030b04090507091b0809030a11070b0a2c 65
    0x51300181e402d0710b4090980322262185c21301e020190948001c080d0715111001050100061580b03004511481e100d06a4a0301c540030024a000f03086520804085040481c400151001145100400e405402e05600c19603886c003032810403070115000400381d61a11a41440c080c0300b031217034100c40813074800d0b0411101050f02c80940c8042ba0160b004842000101d10761081c0072490094a0040d940280b909540d0180c0c3c0c01e064003e0441511014064810314020940c280380c031085d041002c82103040148041003d620420030382c1080d00c0c1c140e07007070100100f044000c1c00300d15000920b03a4000300c103400b42c1c1c0c4d800039240052610302d4927449008113880e9101401480d00051030b4008219425181c045400d03644400001d0042810100042282c465408001400f50719a082207111100c441c6c2c420404c64404402034800036011180403220703400c1002000400c0c0c0c0540507440886030200102c806213a1038011009032a40044801c40110764241c5282c171a0102c0d0310411030401100002c101018103016022 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 885219442 1250 885218192 885218209
    0x70501020f0d0318120c0303060b031603021b030712180e0f06220c0e0f01020709090f0b0f060a0603020901051603021227010203030105130509150a0e011505 69
    0xb21810191074000d2030101c04ea40020310300700c003904203c50840c10011400054080070090204401103400d0020008007480d41c881a82d100e40703c0741030080c0c88111881400c030000d40c003100d107210544401408114102e40c0420141000c24850181c1c5140a094503201400310f20790f0264104000804050510a41e0160b0306619045145001400130540b65072000503040440000d02802d014143d00e0014007148045c0c01c542e0104c0001c0c0c98070a00070703140300300340200101c040382d100d400b69000d15400c20070308510b82e0094003105d01445449030402e0b42a9207042042109890f0b190111080500341322482c9082c0c0210f8006140a0508600d0f080114002820034003611900c2a000300015143d4402d25000303020b0558070078941400f841c0d503070310180401d401e13204c040a810b8080040c056101003d039400001280d042c0d5400504c07080f2174900101184014080c0148010b020340101e80301041324811f4400e4181c014140440c001c101c0a40000c5040c0c00c6800802e420001c00e1514041004280c0310b9070030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 885220692 1250 885219442 885219463
    0x426030118290604050d230309151803010c120e0d08010b1c020a0201020714070305060c0c01110f070302010e060f190b0a080307030909050403200a050f060702070501020f 75
    0x3900b811080c04480001c1c0c1d0f500455101540242004040404020070400c842e420001042d00d6004014012001d0740d5681c05294005030b040a00e901a400c4400e4420b000743c4034203041d0a802e03210320440303900070a0a454011a0b0741f000303d4035035142001031012900402030250108801402e10850110000f08a0941031040400341d41b03000441c10480700041c940142441c6940d03100b9991002c0c4694000d000b03620080c1c06917040103049290307000800000c150281203d07080401460292298051480d4030b41c815440585d0f15940d401040303000b01c0102007d44106200d4001d142e0b100c030b21505019007580c030010000c1e256a0440010001c00b400c03445031054010b18046144000304610100c4500106000c441c0240d08c0502000e00081d0340c8400402050590321a81d0b403030704c61035510301b900015a4020b5a0080110361051407030b10301d80c04040b86540c03950603110201d0700203041544a850906203c82e0b082403160708010200000c441c1c0400c0014000d01087c4020a40400c503140c10a456054550 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 885221942 1250 885220692 885220751
    0x40b060d1407081e06040c0e10080d2a0302060403110307020a0b030108150708064b030321070c170403030206100b120426030118 57
    0x903285014000d08a85044030300c0000802ca4102da911003241940c0d5011119120300d280d416907440b0310348404049501d81c0520307400448420f0441c20700d510032210480042614803607445941e00000d91a9040149005107801034880002d446a002540c41d01400407800ca00c3da01d10000e030800c00004e0740011406d034840c0e01403406030b640c498001d000500714440d48002a6001c80900c102003800703190305c80254100c4925904464007500080f078007002084040300d800c00030407080c80014015040004800c41a249040c3c5c1701d00d4409920b540400701400710040303040e0142c0702160b1196810b102e0506c1c10b688010114000c42c1070001e85c000521641210080070840421040c1c041180385004052513880b035940320040804030070721110100c1094200344070a03001441410003040503191030b22508015a0700d8000902d25004491002c00e82a0b10b0103482122000b24442c600c0c285140d61a02d140b1010850384901c0e0750b02e501d0100c10302c1d564400c01e9091401e01389001c840b06203031109080307030340c0c0100102c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 885223192 1250 885221942 885221959
    0xc23040b13090221010e0f0106060f0e03031b1006091b030908090d050307060b010e0a0618080d02012310030210020a12030605100806010f1d0d050a03090b03040b06 72
    0x148046036001910540d108031544e2005403500c80b080e019000000c107400c01c0360840e4200c18200310000d090318114890800032800680d0800c2c00f2500c5241d5441d00c40c08040c00302c1c0e140081c858444580b0704014880c140441d080018628049550b501a600062a140c40140540c144071010360900c1221502c2d41d501b0305603030348031100800074160250750389032000821041940c1600d050a944030703444500215130b5a49404202d025641c0182c0a003103c41d03001419050074103003070010070780311010401d0190f94200031403440090301c42c00070080c404c1d501346c039540080741014041000c003110342d004a182d001d001011008100c00750004003400c208a070f070111403102e061618403100760f080503000c9802820403048580c0c0300c01c80c41d0301500100704031001a00c0e030406040c04200d0889170000e007520001c1c001207480c0343c401c060500c10010f207040b020b004400340d51402c0c0c08200040b01400c03685c4044a468000044c1c100500d0341201c0d007400284418901e203407451030155203040350300d0b4004051500c40c5081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 885224442 1250 885223192 885223211
    0x11160611010908031e0a05090303010b07080c010903020d020708010612030f17130c0e1e1b1306031407020c150f031003050d1d1c0c23040b13 62
    0x94001c080b0460300007107929500d007050241400b41c40c5041c14158240c50004000ca0420016840b038036118004c0c00d4061811a401c04403644c40030344c804001170310703246400c0c01150606082032242c0402a40300381c000b0141c1078030bc0c060190410b041c035840503078903900d8503400300240c401d414030703050350036070b00d40f40a8030a907401503401e490808590404808040c400750400180d032900c9804c3d0030100c0d000d1481e50312407a0f55100c040c0352140c03040348e0322000e010301110418050550500201c1e0014a864248860b00c04a25007181c002d800070200a64500b03800350b0b042000369017600c203000514090161007404d910309558080e5540c031000501500070035107005621113400f040c000342c41040f403511210560300d00b8840c860000b0100b0a0000b65924022801d840103401d008080e08500c80c02d08034020a61184a10100002e2180300344d4070b0602c20000110400016850408503000b4044100d00310316540b40768060860340c001c0841c01540a03e25101500000e40c0d540b0820110b10b00300500c011030620791 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 885225692 1250 885224442 885224477
    0x13031101050408150603011a1008180307030503041109130f050118031e030501260c120703030e10052d181c0c031203090c06080106111606 61
    0x31580140802d000398480c248062144813012401074800710000d00040c1c14061805444200c412003d41e40420414000c10f0010700450703581d640081c03c140d603160807454002d8031500711741c0600403c40004600004001c1002041103034100c100500361440704861130800c0d0301300503640513100d0190903400d40340c80010030400250402921583c4881102400481525003e03000c0201030b40c200144100d248810305d0007034800e01c680d070b0403200401900001c84100344030f1100b640ac090316415429004161104805440f07010002c27040c54002c000400c80b051450500600c9404a120118840e22164660800070713944002900c050110503c2607111884203c00070805030310100b2600792204e080800c01c5581c407590b00f02103102d07042c42540c0010000d55007034222000004801002010010410414400b045080c00000d29002c0c0505001504804039102d01003280d4155110b580090550001480461b5004056408442c0c020300100030280b9074260030308030301100340941002c001103403007100028103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 885226942 1250 885225692 885225697
    0x101214070807120308090c06161b06050712050f070308130f03090801271b030c0909060c0206090a0b090705131401080a0f030c020d0519171303110105 66
    0x9450303402c44500b41d94601030050307541c160070400da010070060000148038040226482800740300003006a4a08026020010188540c6c04002d6855440002c200c1c242c0f401d641e05518082c210907280c807511140070f494a10549a4402003910070488184490f040054042c000e540030720354142044030680d03035110200c0341409210072001c0c00c108110000380c0d06154010351401d050351005e100074012490700a40e55030b03040c0300724250301000f01c0d404190307a07012072400042110381d11401c000241040747d503919030040c0040c080c0c000c902030302c0d0360b01203039010054548903c4000700010f00180c6000d18145900d07a86812403030301c1c0a00f40008610029000311410f00001c0040d00700101417420701c0d080309048500904940704081068081100007244454000030340603541d991088280384040c0c0560340444461683e80803c91300548921086e8000900521000c0083c606051200d0181d1805090140b001c0c00c00b40c5102c800000b08100038130000c02d40807414025280c00059842074680d40e40012200792 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 885228192 1250 885226942 885226949
    0x1e060c032d0e09011e050d0309170318090402010e130b03010c02070f060c020904150906020705060403080109020f0d0b060705070816080105070f030c170c1210121407 73
    0x1008116000e51041c0e0405004044a442901c1014084e80c03900d0040c40c00841034aa130f809140111001044980b81202c0b000e80014480c0c90100752083d602d5550101030358920301c2090b02c54001190000c02410290445402e0010859a0107005e08251700044c3c80c0d120b1060341980141840c40072107e441c07400341c0042c910650701030000c000020000030001d448003158060500403412842d00001c03507a20400341d0300d4680760014104121501c440d030f21032080010700400c9483c3c0640310a48500030900510260480e580114054203031803500c0d02c3c000b01031103016046406070a1050020704585050941910101c0510720030000383c1e01790401c00213403540a0388400074502d01c100840403a00402c0401c6001c0d0318138a1003070700a00d00341c0384e09016003610400c44000000611034071011010520940085040c84000d080ca589400b28040c4200384401741105d10103c01c0b84005001100f250812030a6548000075222400605040c00000d643c21590090050070610807094a030002c2d074420f203e800001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 885229442 1250 885228192 885228257
    0x60e031215120d03140903030c091e0a0e0403020c0901140f041e0915020306060d0b0d05070303180902040f090b01090f0311040c03020309070b0d14101e060c03 70
    0x42e0160a41c3c010301510312001c0742440100c403200400da28007400002e41c0e0103007500001e15030620200405104140040b000c5210001c401c000740030b0910744542510b90041d010100100b00309140906001c1d00e807103c500a090300640c035440040003032252004086c00140811180e04003a0390503680040c01030103180790181c003031001020010070751110b550b20040800b0302c258506410240d100c0f0300c940481c0012502c0d43d40001c000c001c140b107a648142d000801c1c51000400e0255400860f40b9820f241206941085001c142011030302c05e464558102c21400501c1d070703a0070551506003403c0361210410401d100da80c18060300c4842c00c4138103a00132210f1402400341c0e070780c60380303203d540c1c80c10035401c40701241c80714038040c0385025046001d045c400d00840b8800c42c90000104030300d42c58261010742540c40b916903464125600c1c84180d03540000c0910440c01801c4150458184500f01894102d040c103202068403140514004100b0402c2d42140c0c0d412030003034241c02c000701c050140c03a025880e0580c03040b0102a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 885230692 1250 885229442 885229453
    0x300309030703090803031b1b0312040c0b04030f060f06051008151509010806010201020d1d15161b0605040f140118080c15010f03060e03121512 63
    0x21200010151950030702030398030201c40329135400240e40c4901c800c0e41c683d070003140104901000e0725881c80081041480040c9494220368004284500315004242d010026200603003c1c081804010034151024066480125141515580e580010400e42c0680108240e40b1100d8030620a509944004000c01005c0c10803810920b40410092400c0f90480d242c3c2c0318460800410495030400515402031004030340025803500781060019100c511005000b01c0c110f43d0204900c0181d130009005400c81204100080b140312400141c01030300700a5410900301c980e0440301c003004400c5490100018a100c050b080140060040740c00d4541034002041000d4003c50070101408100003a15100d03410060180c00300e088841c911503d0b60f42a500190140402c0d01c0e005900307003011645143c000c0410b40e0b1070038100c5103420908080309400800980c030040400014000800c00d01c0f4490003100582d44904e000b175894a41050001591070f4409028014480e0000304110b0064803044014800e100384d5104448 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 885231942 1250 885230692 885230701
    0x20181504030f0b0901090804270f060302011d0612040f020303040f0e1506030c090a05030d02010506130203041a1e180c010504031a1b04091a09093003 66
    0x2c080005050303049480d1254000020b00c803000602c101c000403644a98610f2400f032a0049032241115251051509a0601c804020806101d441040000d101001c000b01e034171495030001418400c480c0c088503a83c02c050004128499031403000329030160745040e06c2402c581c2c0700c0d0f040c28210320441e120025090b2000142c0400c82e0b684010159007144c5000900b25211380c1c92141c1004205419621540c1203007051021a1441000f00b018182c0000f019066505030f83d41d400000380b13801740306503d0f00d0240c1d64a8040c0006410b10a4541c10315030015503066240d41001d0b0f48115080d0000d0304503410004850001c01d241c80100b0701040400c4a04a6580c1c842c0c0c101030000072901840000050002e2260042907580f039401001540d0440b90041000c81150321078404010341c10030018110f610044107490b8001c4103144a0b0040c1000c0c241c54500011120700100d01840e4510401c1c60881c414074144080150a20002900c4980211502c0031035188045000c903800c3c0f401c12240000311f24460210410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 885233192 1250 885231942 885231953
    0x506032a070f061d0c090a020a030e01090c03120903050307080306130e0601080d0c0309050402031803040914250e0a0918150212040f02181305012018150403 69
    0x804c4154030004090324200600c1016035600581889540c202046200041084006a01030080c5901604011a5402c240500582101d054900864505550001c14409c0c03007a081d90010503140c2c142044000c071425612016642c1c050044002e00c6940c0000018106031a000340d50514440285800e2040b00315404043c1c1d10b480b400d0044160a108610b912195144681d1a4040c003c3e09515118001400d01d03042c40069800140b150a0800090804001121007040103000030a8800d0f00020074a0142d107540c4404c040240141900d0024203498081c08100408050300b50000d07428000400e08070040072400c0120307a5404100082e01d0500c54031085038940880304180344c4100078003d8403426600c40075049005055072500319215000003d00080d6104c1110072002d40010b11500449c010f80340b11454048088503640d000042c041220020080e007405074040d155004056503407400101d080c07001f05809001683d651044003c0e0905040d5100d007135038036400e458512207480e6030310740303a00b0700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 885234442 1250 885233192 885233201
    0x901140a0309020d2004051501140f22090c08130c172401240504080d050c0c01031b0e0a05030a050606010f14090d03030b130e070506032a070f06 64
    0x611700307090315100c2c0381d015140604ca030900c0380125491681c2c0311411030f001102c06010340e404a2004450070058000700070b20314005024922074165004603c03507944809c000549007a039000020060801004d100c8050308100c0e016840890318100d0b2408112606220908190940c0031f140512440d4a41000341c0700c010031401d901800100d01c046c4032441100c0d03c4c41492109119815900d80c201000c03030b1200b203203141050801e4140b0b00e041d40c10291161605802c1050b44126080031540008511440082c240202900f42001342403c0002d081c00d00020394002d040c1c12021410489444403c1920766107207424400a803c0c0502150726055240c540f469035810190341c0140400d0202c09142d600512900510402074501c594841c142210300040c040404030006c02202031545801ca412030948401e141c83e000c42d41904400316050b07883d004001c1c144031490b0013007400b0360400c20411201d000808560141030061310ac00402421004001c1420303070003940c00050245504105003c28009250403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 885235692 1250 885234442 885234473
    0x21203010b16060c1e0e0904030309081c060612020703210f0f02070201090806070f142106130c1d030c03070b040e0a050106080f04050f030a1806050901140a0309020d 73
    0xc140c50341d01741e4185c0c00c1d220b004e40c542e202c0c0c4c0d202200b0000030f00044d01ca90080000d040c42070152a051030b50346007107a0401d1a0101c0703a034418030b50300c5204228490f80140c110310046242d20003185400c07001d07240105a0080b400320b41c0409115000700c103182810580c0642400703d00c1301410040f0090840005e00a5071000d070341603000030402c3c2804101d44001080708d0f4002d10ba42d445104900c00c0003081601d4210b000070201004401c00d004940065080d00742c0b20500d00d4080e600c1710170354035100d0100301c20124808444200d0174908409160200c4e04401c4c0d45180d1751904034565000514080020320b0581c1032000306805000b5208005101c8407039001500542d0704801c00d90005949205003001252001d10880300050190400301d4034207200860b41e5500700e80101c0580c1c0883c1c0710565a02d00cac0d584409150000507030b039074480d080b43e05c0c60350a8403c0030b400755103010343c60098143d000802d85412007a10640e50040003030080031f81800b03a0b00c1908402d50103020001080014140030151010115 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 885236942 1250 885235692 885235727
    0x70c0503120f040635041a1005120a051614060a0906120b030d20160e090f06040309030501150b030a020a051e03060a06021203010b16060c 61
    0x1100c0e040460345a03402d450901842c070b201241000d1400078219501c228441d00400300b07450b0403a070407407100b228004410a1044041408040741071901d40310701d00c076008904080b000740c66902404400f01d0300b980c4038070407038404507214001e008486158504100208400500030711075902c00c041e01210010f02d15084504260240c41d0070200c2c1c0c402d005040c03144160b5440050308041341400820b01946007250000c01241000440b80d00e03c8001c20301e00144031103800d01046860103040704100c880050000c240c0704030005042c00d100503180b118240e841901440f00581090030009111540c200980d00c07001c5221402c0707884078205420701410403282804140e03100c2d42050390036100d140c00c0000400031101141d0b01603246540b1a0300b0702000750815020320b010054208480070801e034002c2402e030501038004001c00e5490614404000b1103089503805001590070013070300e032682048010b00b50781c1100d59805a15a4031058018000172120340e1010040ca60f500d081c440d15070a5034010160502043e000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 885238192 1250 885236942 885236953
    0x110d050c120a0822080d050705090a03150e210705100c0c0c091a06090f131a12060c0a03061509060801171c0215040503030601090504020f070b040c050303070c0503 72
    0xe030300c411180e020000c009017408104010031810444107500c51540b2500d103261250802201304e0010304203450642c42903801d810440c2061f070100341c0a12400c0401c2c20240020030b1203401c01007004c862403002c807000418101000c503130701050000030f22103d002c10355645803c00407007c0269010702207403259001916100001c000215400c00c070f51041c614441d4400c98100b0604d0b95803801c0107160717070154000c0350700003415200c241043e0700c3d0001c2d401d56198040c0d00c08034070201c1e003140001c030303185c11070503802e224042032400954400d0010600980003180c800302c850f66030750380e000207070050041d50340110f980d50740c0505c040040e00e82c0f21103a102030300c3c41680c8210b12a6600c204c4030114805d4404043e0f40b0fa044403040c0c100c000160215036827450001d006a641030700c4281c1003c600d2403811a4140c407650030000070018035690000d00c14002d400e048a04609141090540d502d103401426002020841c0c040040b900f44850130596000610004040700d60704e101038035222030721300c43c0d07882124040d2064 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 885239442 1250 885238192 885238231
    0x3040b13031d010504090e0f010e0a08040b0c1f05191b03021b0304080d120603030912020d0506090a061404081905191e110d050c120a08 60
    0x5201244616601a070340c1c030790511180b81c4540510a40c00c52054180f0504000020720b8500d0f070301460b0031440400e005401070b03100c0040d08030700b510300d55002c8002c01d4000c04880000030300140c0603603003980c0300041c003d621010a40308081c038280c01b000c81070000070115007400c242c020042c1c20403885003510f4440e842290958500d020142c91626000322801c02206a003041c410f4480d0313000c1c209030314122001c00b003441a1302000c2810b562041d00038540d20b0300000075160a05400c400008075600350f403c0f00300841781c40d54800400c01e0443e405031080d240020f100d49019555074401400b0362541201c01d40e502400c1850450390b540c8070905040342e10a042c040303a183c04d0207000c00d459100303d802c418503601c3c0c19448020460b14104015221051140c1804810030b844888400c0d80f11140d6183c0321100702008150a407820700903066a0501044100102c10b811040c000c1285d100101b00c60810688445402030200e0401d4040360300442401d2004c40c0411030503a0288205014120400d550403c00c041c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 885240692 1250 885239442 885239461
    0x1a061305040213020703030603060911031b090403030c02160e0a11090d030c0507030b010609090e1902060f09090411040501080f0c2101090b10140a03060c0e0a0b03040b 74
    0x403078020354800d200d55003954003000c2c01d4006156181c03192800280440d200d0b03541c8412150b8800c01a683c6442d502407a403c05d040400000c126801030090005403004c503034000800507800100300904064484081c691013600030898090260300c070912074144a6150031814400760000ca0f04002c11508248400c003903142a5030807075202c000007610401358044942c4003502c0511388000c0489040c82064000004181c0d00c6040704c0c00707007100365110700d55946490150829a4244405a00f140d000f8864040602440c0550010034590648441d502c9080364002d6158601850111641000f041e1040108000c003403c1619901402203604000720798076102d100340d5460703145d04c0ca003450b58001d010000b0b8034608480041941202c1209080716584422503903400c0d00c1403c4000c554000b612024000c00e84851a0124050004041d11800341800c100000740248002e120161015649400021f6014840e102540e0085406400c1d00445651181860311643c0100d405440b04284240420142003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 885241942 1250 885240692 885240701
    0x506030d0311070f0f0f05010f14011d0c09060a02010e0d020a0c120606031410060e07050f09040207050f060403120524041b031413051e07031a0613 65
    0x2e0004920b076050903526a502420384100c26019507169890300807004c00a0b08100b8403010f620300c124000b151500c0e820100d50107440405606103084021003005000c940c5242e019140b242004d913402d1a03064599042d10f0020744661003c00e034014000040c00c41d01c3c19015005468010168030880702c85100209003240c480f11080c400400142c103113036003040828020100080d1303140c050071001581c1c0783d41e0360310718480c0c1c9500c4030034001941004442c0c59070072441c0d04c500030040c012903502099a280040c002012442680c00581d048440442c1c42c00c001e441e240c1c180d59480c0d0384138084420049420b0803040c0c1e1000700300da08900007011040414043c00e850701440e40a8410407400c21030001c03d018413240c0f031000600000750442e541d07060000c7e041400c003c00c00c01140d00b07902e002402e46e0014603400130005004103461499203c4005076000500c00207034880916003034011805103000080d0800781007011075071001c0c005122503000c8a026686d071040403070082004480f035140441841080b0010344 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 885243192 1250 885241942 885241961
    0x31c0506010917010b040c0306030b100605161b27091211010f110301050109060219021002030c0a060218030109020f060904020c0f0a020306060109140f0a090f0506030d03 75
    0x5801e12000c1221502c3e5800c0a58064a1240080780d81c488200c08034003100c1c0007510040c0000d841e140c00304280010884496041395006105450181c10f050000c0c0c50b42c4128400d030058030281c00d207440180310555001e6400f8000c141c4a0745030342907442150403003a445515100f030381c80c44680c2d940b0a000700c0510407480110303804006a0080303000c0312000d544201050f401c60400c1d5403030b810384c00d184135918400c0ca251050140d002035240c0d4184800141080b51a8000f00309542c418209500c00e8524a25030124183c0c0c1100d02002c510b12040d0101e04500606181d0b24151041030071100c00c20400707801410784201548000c00e80a00d80b00e0800d42030707a2040501a41210175a008105a414180c1c02841446030141c405444d18003030038405440d01810309600c0c42181c00c810784c00320843c40e061256682140e02440c03e40b6003281000c00546620320703030b030100500c0341d07088100d580456100c0011400040040b948204143c000042000010700022190030340b290041301c0311107581034001d1080c4c100d01e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 885244442 1250 885243192 885243197
    0x120c060d020c01141005010804080415110c04140c0a0528080c0340060603110906030304060f14071b08120d1d01022a1b09060f030d02031c050601 64
    0x170345000e0041d20348000141042c0c40c0203401304000700301d040010040d482100070360b56418800c1904007080d1800c2000340c80c10680700d10704006442c0c480b407154203d05030b00814403000b49940d40710405015101481074407010082c0d00d50200b00b0b81c068002d80920440340e2209038881010903540c42c00e07a010a03100841c0d0308510b0801c841d800004480864250400491a13003074441a080d9804140b0b2029100c4500200d804944454051081000081c0300c050401c00a880101e514286080042c1d101e00450103400108584608852846440703212803441c069038150840399140100e0400c0310304c090500b29401800304032071000007038003480094035040900d21030f00e0a90401d48010300c040050012400b0b040c2800d05c3c0501c50300461f0f84284010030003007a0404440b10703102c00d0302c2e04c040400301c07803401d1181454000b400c1c8404144103042510120241c115802c0c0665a101d2000645860f9032411450301441800303110020b098000000b00004281c0300200074120b4544564541520f5080b42ca01e0700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 885245692 1250 885244442 885244471
    0x7050a030c0b330d140f0f03040b040308180a3206041e05100206010501020714010e012a0524011d040507092c0607080402120c060d020c0114 62
    0x140101803d107060804000103020016202c55900c8011003601c1c03a041248050304188074108480c40b04202d46010b1402c0b80c00a5820310380b800031203968030b015038800504500700020b10141c4d0052441c0c031400300b00c580180000c8603107858111540f0b092044520551400d4600c8010704002014409014841e02c4014210b6103098200f02e551080807810108003107202004140100307050395002a040300c0c0e0800740d07004100719131606c00020319003183c0b035000c81800000181c40c02c180c2d91348100805070b0040b081c28800c0d0301320f07030f030341d0309070815880001588202154690a00c3c0800c0b0010030b02003a80301b140703140b50110030440e07209401641ca0038454a030ba000c40d0307050300403011181400e48661160040b4140d81406540c2d00d40f100c2500e001e600c051a4038028103a600b0090480070b004d41554012480041000c1e16010f0b80241c0f09107000f90001c0c0c403842402e101c45c0e250b0181000140051031000d8046c1c2e0301e45401c4001c11002e500b2808002c9111350905034508180e8500e40c4429104000f0001c0006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 885246942 1250 885245692 885245761
    0x3021005121b0702090a0b180412030c1e0c171602090c0c0f070305100203040503030a0e011d010f0e0c1f0201020d090b1806012907050a030c0b 63
    0x55055942d40640c2c8000c07050141c0d5015950b04045c0601c5012880400301320b0400b450100164000344028000f11180541d041c840403c404d441520210800d505000030580c400c90806d8800d4092008552000070092903140d4130903510420b0307003015521403141805031031403001038041c0798011601000d409100142211004d4506204246d8010300a16603852a200c0310400b01428001c80d221504c80030f80c811502003081003802c012440207003c111101b1030560401d9642c4684034440582000710b501e4503107450582c419002e60120104c00609040f00c2845202044040e028000c68500314003c00d103441e000043c048000f041e904032500004010810758070101e284800ca0102c40c5104000310340d400d20205034440c007944222138149028401d03101c050710b80010086c98103506080381005e10340000c4c0042010b803000000c15980060072031031141010034120b1903096140502c140c05045481808081c005164200390045500d5000b290b00000b16915289500c0e18141100b5402c450411040c2c40301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 885248192 1250 885246942 885246961
    0x80304151809140f0903030403120903140a0e010e1203091c050318041a0307120201111603050d170105270a05061201110f030c1608040302100512 64
    0x842481010030410744216220303500c0b0030071603040c07040d072909202ca4801801510710008a01d00d0740f10300766400a615624180d5030040c4407521210f000280640c503a81d409080500a181d00170034244190406078694070340c40e074000d08240041d040c1c24081803508002c1061420041607000031000c04000031440d0130704075000c0c03045042480b10040c009241102203540042c03030600c0140250074102c0d90b402c18400003d030402c17085940903000309070200d040704100f000644002c15540d00711020b08418008019980c00142d8003440681c00026060051000d08108074a0780250002540d016008480409031022030684448401c03101c03072107003000324000402c03281c82e0040d41e0f0381040c0f0f9000c0c148401d100b420f24403e0400481030300c04024040c2c4400811400d41001550240a45000b1000f8000f9071284940109103200d200c01c180200c0d0b200100003880300141d48115405502c40e81d1940131741c410b0500f417000c2d2030b03000303400304900c105216040d180060384541c00382d07202c4403e44005807090340c070b6282c2c44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 885249442 1250 885248192 885248207
    0x2011b0903020d03391e021f0302130f080d170c03130f06090b0a060b0706050414060f04020a0b28021908090901081906090303090b040f060608030415 66
    0xc0d0300345c1c1c410a071180145426000142d55810404c10150034030b5420324180354414a020318011000c078450701d4900c096510f480d80c51013602050034000c0707200141d044045020740310380c40d040200c0711ba05200c001184c0c44500c0804007260480419100c03055400001143c042412940d182c0722450403c0215111070070041c01075800aa04c4a0f004500503081c2c0c2d1281c5411010f074506490182e80c642c240010b004144419640c00540600100502400c041d241e800030301898101600c0300755598000b9080144461045a0128031141120200d01e059a41000725500072241280500192000010f4620070002030314998410354844450a205441c59040080c800358000401c41c0b10f40b0540d20280b201c1c0001c1100910700a00f85544c0d01c522800500c031183c0410b034812151580700d40098280e92041e40d841c103400b00d50046010132001002e00381103001e400c0d0001d000e4201c4914000780002c0014190f03403140303024818442404441c1c0e079120f100d034076400b85214180d14908640707a0585001c0c0700715003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 885250692 1250 885249442 885249467
    0xf06110f090a081935190908070603050a0e0601081b0a0509040f15020f07021f080408181005030a0f0c0203090126010801020403051606090b0a05160302011b0903020d03 74
    0x880e41244c3c0d1003d00100c89100c54501020401200007150318410000c10000d1000010740c7c20540729143c82d22925642c1c9507124451402015924004140c00d410304d0b4000c03c070284041006c481d4a03585481d01941c980c0c82c1e442200a0404d69510000c20f00d04240304000d0807560003c244201c10f540340c0e11051610018808101c2e5004c2640b02000d441145510240440d844110303a03054681c84503106000000285980044030803422200382030403554062620342e4810340c0526425143c2c0400310090000c1080e41c801a540503075840c03004103620798020055803140321184000d0000002c0a04014100e521120800e80140c004000410195008402d12803220f1200109407442000d42180c0d03039030038002a04550360030303500040e0810030321404011640017140c030f0061484000c0e14251000d810039143d0300c1554111103010512001c0c29002e003054451320300100c0321403201c040b0a850000c1c0241010420314610007614503060300c0c0d0501c00d225200c1a20350140520a20800c95141964401071909 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 885251798 1106 885250692 885250733
    0x50a051605070b01060e01050409050702010c1409010c060c0917030703020607171906091e060801060e0a020d06080d02010504030210020f070f06110f090a0819 70
    0xf5510342c11502a03041118074400f07444016503660040d0ba0042503918506820059500c3e019080344100d01c001c1c1c0d80340c142c031843c180c0c0d00c00c809015484400b40001c034081c3c013020000d4007591c05a00d51100c1402c0c1030807210341c0c440030020161501407106840d40c201045074810150108003254121610f402c0075041da14004101450241c2d004008403006000f0b004400d03c050003d034894000f40902d807209201007000c0541803aa0a121520700703280740342c540303140000c0403101803003000242c44601040c0c84040e2109282c01d00a900910500841c4640c0c8000c001002c2c1d030304002028102020346c00200c1c0c1403400707040c00b07802e0070342039020080118010001c1801c0039860104171141264402303664241d8030680e06101000380207140c5604490300c8002500c403a0b6040c400040c15403a5012a200c0009940700e400130764594842e291100090101c0c0c8504100142c0402c3d0700805100000 = true := by decide +kernel

theorem cover : BRFrame.Cov 885071942 885251798 := by
  have h0 := BRFrame.cov_init 885071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 885071942 ≤ n) (h2 : n < 885251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
