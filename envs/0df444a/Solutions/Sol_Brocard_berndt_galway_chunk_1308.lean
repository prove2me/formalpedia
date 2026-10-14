-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1308
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:17:39.942979+00:00
-- url     : https://prove2.me/submissions/6a0f8a46-0ff8-4fb1-b5fc-b6215bddea6e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 235071942 ≤ n < 235251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 235073192 1250 235071942 235071953
    0x80c060403030c030908190215010b0c010b1e0d03050c1c030c30200703120504110f030a02040f0b0a05010809060a0c05070606080d110303070c0b09030c060103 70
    0x184181c1c0690340801406603400c1e0100d060761541a4042c0076104280000340c1e5861108140d003a030380b8104c0c0101c500f507007600380c00d1007003a0300240e00c640303000040429110842c610a001d4540423079012104c00301c030550a0010341080345c9048050a0184030605a070300101030140049440e0070320b00000721741130b070301d2140b4116030095030007011007000030708050980f48010b00511022816502c142d00c0c40d00c1c00e6820604141600d40b40241030414242c0380c00e8526100b140e0311042020869200d43c840d030381c5205c1818003421411000c40d0005a0b1854841084080340e42020b2142e440302c0101e55410081141e140046c1c98070b1041280658050b14221a011140c286070740001c40c0488155010f44c25280d80b0001560100f00888015040d0b40240d400940b2542d0641d2144e00d0f0f40c00b1034102141005c0264a998040314002e400a0b079296200e24482c05844d41c00065110b1000103550065180d4075103000014180d001c000d03002807908102c01c000c41c104020500556144069400c1210860341e580e0901 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 235074442 1250 235073192 235073203
    0x13050a0605100c12030203100f0305060702160308040902030703020d02120f150901050d05030f0301030b0906010909030507110604050d231612020301110406050a09081b150403080c 79
    0x866210300d444800c04042c5a00541c079191120360414041e1403001480311040d00a035000a0490740311030421403020415280c07010b02c00d8041c600820080c9450328042d40040d01c1d05a81c103203030303603c81c91500c40b0400000d10424111000d4a028a20150304d075251402c00fa40130b8000c424000e21010b002007001300c01588201381d0144198150480120240c80d07101c1c0007481d07060010142d030f801000c3e0000601441c10186401e50303010f8407540842c5d00c2d08100c9030150800b40c1080c1c00071202c200b0744000f4400c1503a81041518054002d640d41081000010b40c0c01402621642000410440400100c40740503035550301505c00500c030180c11a100a2641d03e86440031140780c45040d0909000385d50030340e41c1170b50006007080980400c45085802c1500f090112813040540380c07022a07066407202c90075040c0e0f44943d40036200410140d101c6503111140d40a004e450031009030400d492650043c038860904c1100010724440e824010f0f549520b4404c0c0805a2403041d01c190b80001d03050503400a25280d07580d000049 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 235075692 1250 235074442 235074449
    0x1404120506010510270314060106020c06191b1203140a0501030c06140d090b0702060601080f01050103021b06070c03170106120b030c040c08070917030403080913050a06 74
    0x1601d030560b0f00d0700c04024694800c007004900080400c0d075006a0064220b01540b446002401014002030b52076948503036030600c0f00f00c03009180d001740300108541c540401c0103103001001126070501f03041070318404c498860408002001000030300c000f4041241d004043c02e000854200c1c00c1c13521000c0341800090080c1a01030101c2817650800c1000036889515889124141d9034001203506400c1d20380041280d8000144400f651110f200f0000c100c0c0c0141640301b101c1c020751140140720030f50714180001a04000b001403003581800035000801c11403180c03510f50141542c6d000d00f0016251003502800800c01e0402e000d1014062050380c051000d03107a0005c038440181c038804e0365002e100014807080100d41300c03c01e10442c8041f03601c8105403402210350303401c40c03070f62250003804903801c000040002500b502c040081c1c000c0464294000c1c0210140d10003008009032014032103810301940c400a12070360b288103038400540500f2011904000e141e80301811081c000e20640c0042c01141002c0c44424010541c510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 235076942 1250 235075692 235075703
    0x71b0230031c05060a0e0a05070e030a0b060909030403020a0b0301080607091202010e0d080d0603060507020c0f0d02030a0506090714010305150405090120030f0601030b030a0f03140412 81
    0xc019a80318040041120710340007900800103480380314260b100c0050034001d0109544850310010100745581103000e440d103c0c0c0f203051000315040c01c00e0f03040030382880c100700400c40c0650081e0402c0340204641e02c4549030032480603640300382d150350b80829190440c0655000251320002c41e6000040c0262000c01071810b8580e100180c0e822174446940070340300107426105400e241000c00c202c07000550f014040c81100c189000d4030760300081c0c540703988948942d440f0454100800342d446505005001840c825290311208500042130380c145200001029070b050030f02443c8c41010456060011900c05002e1580c21030390003012140a0b09003508400d0326540d2a0280b2903c0720f5030003008000c650310900859014400f0198614140046c0c5024013010302030083c000d1100d0341d206c1d5031240c030307241303a210310624010301c0104042c2e10390a14203102140783c5000740240341050304201d6511207940d00410b640c00501d17840b1f01072004035100c078074040e5084c0750030640d010f13400302c0d0118002030140d051136080308031284500c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 235078192 1250 235076942 235077019
    0x110705010e1f0b01020a06090b09010b010306080c09040503070803010e0115090f0605090a1806060813020906060d0b0d0305040e24010f030603050a0804080d0305010302010503071b02 80
    0x7200265841c884a442030082880c5005006140c42d0203500031016000188103880b006481502d4031010745403040030440c0d40c1003560301003082d0300c0001e2143e210705160910b006e101036803901c0c02d501e0740e4004d6031a0280c41640c20760301017810027038200100c03144660300003031094507503030f441c000420340300d0091140d034a030480f0061a501d62684280c0390001a1610700c413658000506000e42110700350400d0f17038a19003104003100c000c160352910000e4100b60201030800820402c1c00c11000400303020700502042c14006403059460010390b101041958042c4042c1c1e00d80f0780742c0e40e20400c08030152a10104413030300500b004030058141640000180296540c84804a600e43c80e00d03c13001440d90501100e030850328800d0640101c1c15841024800c6480c2940c1c94045074182e200d444407800c140080004403400000040c00f040b440740c040c40720054080050400300410340c55900003170000d00c40180003000700440019003101c05058811031350700c1070350007601200100805903401d10b480c284106450300c0c1070826 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 235079442 1250 235078192 235078211
    0x3040e04050102121b180f1518060408071a04150f0e01020a031e140f19111002070206040e1302030705030c131a090a1a0402032205070911070501 64
    0xb07056100c3c0c511542c0d140581ca40400e61b5511128540e00c807038056848042c032041151140e503100e000c5951368884140c59590f5440c20000d0940c28082d60840701d0042805102c00c0210313802c04110703101101d60b908521001c070721700745014110604c82c54000301e000203240380c0c201d05084e80c000c0c2403040954003910391440074219800107907558107601c600203002400d10303c1c9501d40c48860303044032202000315040c104086503c1c01503030441c03030300300715003d00c10181c000c58480b81c1801d81c207102c104010310500b403282e0410034004405442c0c00140124001d5140c0015078901151910b00890380100300c0400f1008082c00c040303200c00203001ca031a00070b038402e10501d500403650785404101c5001c0f8407402098950100ea0145d4444007401e421441c24680704134461010300f0755103440d0002032050300454000600181040c190f9961410441c01160042c0c0c41841000580006210720999450200c0304864840603286846490200c69410981c8400e090610307102c04140c0312009000040d110f0402403201218 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 235080692 1250 235079442 235079461
    0x80702010c031103061e0402040303030b03070605030f0a0207151e0b091e1302090103080307110d14070c05151201080a320303010b03041406060102100e03040e0405010212 75
    0x20074030410180c2503420004a05245072400813480c11801142c460400c00c51b5510004089800552081c0e003c241c840c12500814134041c00403101520301c3d0b090160a50900141100c01c9030002040c0e08002c079400506142071040915603041c2c014103e200c144642c005d01258440b00030091042c04113800d050450320600e915007078006c14132030759105d0003c042d007081d1007680000311100903101509801c08880060050385503103241c14042c40c0039000c450f64900780418000e02511700007945405030740014102001c3d0320f600c07029000c50b6a004a029035103505041c24a0074035545d1a40c0000e0b44124005916145d0a4075000641000c0c8660702c40310502c0c0e80d0300d020140d210640c10100030a0401410340c41d06c004020721558001110711110790030000900054510f1840e8400e820044c010440482000308000d120b1707604098800050b00640400d06103400080c1da40d03528050507442d00d60300c138411040101c1c070400544004140319450710005080500303040b4000c4d805000840d200c401c41c0b6000407040344 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 235081942 1250 235080692 235080701
    0x13060906030f3e040b1209210702060d0c02010605040e060103020f01051c0507020c040501080c030a08031e01090c0f0c0c05040b04020708030a051f03051f1506080702010c03 76
    0x5807942c0100704980030040c0041c55090400e000c081d21000500d143c1544010201400260100c07071415640c0c0c060710090780c22141d030020b21401e00e40d40001a15152070700540c828041c0f6556000c001c607280c0d9490301c00a1640d0003080f5071005135a150404185020381d05401500480c1d00a99082014134250490035848200c2400081d4000b4003045074241d45501c2040204200e5002080c100c0f00764008071420002d4035402d5510b40010390086041541500e814410140100302e00001030112109542c0440e403100002038024000820101c001601c080b4106440903454541090240d240d41e118119000208816810302c03000840c1e109100d11524040c25103443c00c15009a6903000f106c2c90002000081d0034900080c9402ca40c00344080c10002c1c401602550240c404000081214034000d0b0400c250401204106001c11028510400c042000414074104d001e4441c01841100d01b010482da80180000000c1c6807000440f6200011710a90301c4500313280071f02c405030700a00c044581c1c21001c60030794 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 235083192 1250 235081942 235081961
    0x10e0a0c051b0a0803090d03050c091e1c0503070c0b030609010306020c010207230c0906011409031c090609050604060e0112150f050906030f07150513060906030f 71
    0x1450401403440b842050101021811100504482d24401d6941d1110003031740040d00c0c20145540b007502c59411850700b41c0101544000050300b5031f4200b070211000601c0c0c403100b6003400c4010030030f1490910015122178604103541d0304004a81000d0b00c0230352902a030769034070002d019241d487d041100442d20380c1d019012a07005141c000c10f016440d03402c680341c00c1d00951180c40407000541d42003109034002040d203858003c9109840148175403c8014219150030300744406c6056104e846c00f0001c1100503038110b0b02d00280380350f011429070b0726607038500c010a103803c44041c151000c2d00100604107070090340c840258400d40b00307e542c8900000b9a50410b000d041d000300d000320000708007003580188495101d6035551000214041000c10070001c609a05581d6401a801c00701000413007410a2110341400450742e600804103400030642401030f0310308141c5070a40d030b006210002510f00f58008900b1f114000b0794403001600c0220580c213950b1503d018141215510402e00800e041020455118143c0c0c07084420f071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 235084442 1250 235083192 235083197
    0x603090307050c0418031103070501052e051c111503041e05072309040c060e0306041a100b0c16060e010c11060f180f0a03050a11040e1005010e0a0c 65
    0x60400300e46d402e6604110407112048503100c240b1415002c03400074050700e40100d40b08440b0f00c1c0b081030340385190400c1c4624406020501008224204a10f49a5690b09980700d143c0c21800003e81009140140300071584055055200e01614049070720340311f0200c000c40c002c40c030581c84040020312915204180306150607025165400081d07080050300301c40c480307410302821702040c1686580003040c009002d12000f91b5060f110254594401d0007000d41200f002c04800404400810445c607140ea18000b103401c00600002c0510001c0000c42c9160b1000c0c3d14070340107007a6030710384c1d6500d91413a200c0240e51303680c8206090f60904181a00080c510b03000c0c403011042c0c0300d01a51100c0c3c100d42280c4500d1849021055202c0e00310f41e0800c41564254044006403560402d6010104610a004410000c40760002c1250a02c03e0042e0241000041c5000603200314140e0300c04d01400c150005000050000c101803e0228100c1c0a0300303034000c14600d482d81c06541a00c0e54032460790482e80320f4001740030480304480e565401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 235085692 1250 235084442 235084481
    0x1401080f0f040b04210e0306010f0b030c0a050c0a0b060f04020c0a02040c0905030d050c15060612130f05060a060b09010f030b031c020d0e04090206190c020603090307050c04 76
    0x4240320480155209005814038501000c034400c988040c0308481210f05c5c00601a40310781d450625003840002d0051030541c0343c41d074696007060b80c004020303c0701a052100500000a5080465010b042581c00d20004071050306ca107113050f42052880344200700c0b0402e10500d40211803507018a454400c0e542c0140c0a000100382204070303076003440014440c400140d81803008002c6c00040710b607030400c1020300300070309aa595601e402041c45030500d08201c000d0b0380c1a01c413003240100091a1604001d44011200c0741080c03c00544820b003416000f040c19000242005840b172020f40140403001580b02c1c00b9a0b10343d60108259596071039005143c1c080c01d1a07850000b5644044d15008a101750011100d401c0021b06403001400d04010f00707900e004000d82102d0150f040701c04c030203030f4103600006200c03950300007568240407c400c90790000780107100e4030300c00c043c250554004e00c0002600c607450600c0e000d580074003490794a040c401c0f44182d0304c0e04400e50881c0c0602c105404880982414007501004055004038a0b2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 235086942 1250 235085692 235085701
    0xf070f03090f0609060b040203160e090402030d0804060b150a02160f0504021b030a0e21030d020f1b0c0406060e15160507030b0f0603012c0312011401080f0f 69
    0x3c01401c5205802c1c0d811640720507908429545500c000c501035034051924503408280207001401c107620032408a44a03030500c3c03042202685022680703400c50100341c035003480c2d565994a1b1030300040840e1441d490f084424844241c0ca140ca2120080007003142a80844010410412480403a03000c50300480c00000074070081040141042e030050907400e4006004121680c590780307001032840d00501c81384400202075005d5410507090005102078060707100c405500082448003800d6030b407071155030914403c40350b000610020340202c65003903075945000036240303a81c84240002d185a460300300481c414410f0380741c90800210103000e2000c1c11400c15001e001100d032010004503610490308801c1681d03410045039000c200009800f404030724083d43c4210700d0b1580900307214045003062000100801d0007a8900400c1c2006580c0e1045130303030003180482400c51502c58908030304506501030b149407280040d40b07010011503845034401155901c070780217030383e02d0250365030b44002206681130591350030040a040c2008117 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 235088192 1250 235086942 235086953
    0xa03030b030c04141012080703050a0c080a0306060f1b11010e0901080a0b060103050601050d09150c020718020f190e12060906090c010f05130e0f070f03090f 69
    0x240450350090903110102060000700302078868524207100d070010040704004200040c24409005801c40030200204ea0b2110b5030748000620505c0300c09070901001007080c0c541c880c8145891481035922010640d12a52a401c02034090030643c0a80c601041c00c4c1c01d9480b0000740700e503001c0e10314031f010240c04240603135140e2565a80d00030007104090400c142d4400580240e1135100780c99008000440c01002001030906281d5440d11300502002e04040c01c100030702040383c0e4804151200c41300c2507000000d007054145000d60b02c900480704d01900d95800d05808880e00c5401241510840f1125200005c038241d06140c0c1904038480d501e40150328200034080b14125010704207507411051410b0600000c0076001030001404003030002051206070f0b00c82000c100c1848000e00400f0f07041403c0c60000d06490260000103001102002c40004c20400040b4201945c1d4150034903020080000c01114040c42c1010b04e042242e100e800c99402c0042114100c44017401c81c8079200d6944482c0c0c1220308469038407075550340d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 235089442 1250 235088192 235088201
    0x512070302010c060b030109050f060906060f040b040e010f06030302070b0f030711030408070b0408010c0306030b0a090302100606020c100504030b130f060507050a0e03070e0105090c040306051509090f0a0303 91
    0x43d01c1e4140d985c0321500c0140c40134803900c2141ca0081000700310511900340307134515116004102d800f03103400403810301c40c5517162110000c1c0218400c50300400c5180707501011500400c1c040380c1e1342522390f0030104101d002244c40c1d402103041e24000d030b09170740d00543c840c00d01d503001d4400c9000340f103d00e2204000142d18540b041200e075180115020580e440e10703560300141490540d4039007024003010f400003001c10004e4000d119071958044982001d2180614549420362840001803509260039102c165000c201842880b10002469406a08003d02c94503560b00940d41c0c03c1d204109805030038051602c0d04041c0c0280281da080b29808001d8044a540c0d01309100c2810102c1c1c5000c580303c40c2c10120060001d402406054071611050362150303224204580010b044407200780e45507002c0e07044000203020101c2d030b200c085815250180d03040ca8a42c0c58002d10003a4501ca40e50014110f51700e484d091180c994141111142c1e203100886100043e5110101803580740c1c0e800490b005403980c40340080364002030180c0c11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 235090692 1250 235089442 235089467
    0x30309040c0c08070b0114030c010e010f030b04020c0105150105070c031b030f051f0e0307080a052802060f060d030809071e03020310090803070815040f0b0406051207030201 76
    0x918400038082e0341e8406095410550341245d41851030401405040c003624815192910200c004082c0d94001d040042d00398109400340718100400c4d040c03088201c40c000e03086041e04650160086540c1c01400c548075000f01070130754198040c51101c003119005988954107070340030b5981200300e50118602d56078a2410032412101e210030507000842001000c20305580c0500d00341d5005030042d01020a40381c4d0110580f4910380d400804092600c4a903990001d000025103400300d522402070b950301d841540c8140d46500805040c0c225054460720352003240c0c21000ca80701c2030311220303030203c40d02e988400d0b108140c1d416003181c1464000702e42e0450362020901c12510180c1000c00d800c180c40c626a1140c1d6048a40075004562048100c1c1100c0200114141040154103014013100204056070380d44d0789d001800c3c48090000410805582d01089955400c483c114101800050040001010707180240014003116a6a5885107241c460000748500381010910403134102030002d494070508582c01900c0308201b200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 235091942 1250 235090692 235090697
    0x30b010b09330d140108120706020f1317010c0813030302030a0906020c012003160c1704060c02130b060f0d0212090a0212010b06030604020706230a0e0705030309040c 73
    0x710380800181c01001410000c64184001c1042510300c1104204c0d80c00c1a8028102507000c40d002e00c03101501d5406071082964002c0d80580c0d1004c54518081e0386000d105103464110381c0b0f807500081c1c41c030b805141c2c0b920b0803600c1900a1002c4d0b0741408043d18512000c40304803c85001480050001138440c0d03009545c0000c40050001c1c0d2200d245d12260100d81240003c11000e81d9681c00e001880d0482a80c00c00c000d203800c4030010700d98070304048404210b2102000348800e0204e1020350500300001d0314294080c00420f43d003602c2e1510f594030801003481c0d011900c288d010300348421082a00100602034002801e801030005450241d0f80b0940c241c4580c41101d4454a466013800303141400f901c0603031a18010860b40c801804004610b0040240c130385900c0c00485501e80c90a1546d10715a100d000569901410413580180c03906080c0c18000080c115440000306502d001c000313819540d4102d060f0250081e01c4910040200c280700c15030481d5609a83d0194560650091240c0101887c0c103401c0f40c0600c641c1807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 235093192 1250 235091942 235092019
    0xf1d01050904090b1603060801090f030e0112020d06060e0d0210050f1b0a03030b091005060304060f020a0c0309080102070803060f240c1614010c050c0a080304030b010b09 75
    0x80c2c13161541c1600954001d0740b1803809500c41e046042c0c0c54003601019180800007042421090380e42c0310340089d84910024180010020200b42e168000c02c01c40802e400c039101c0035562404500070500c020015405014041401400e0058680c24135404050506501501c056503202602109079141d0300944801d110183c0304012412664441c800bd500c40000c1e00300c014140d1842034a400713409d0b20000c1c449107025500072007c1008200c105503e000454400342da40d9a80c80c0c544c1d0030080b020307095101d4010110390000411444d0107910091035080c15000c1c1d41c5143d0a00e4a4101c000d0903807203070950181c0a01c4050020501d1840e2106803140c44000081c0b80110514111048170100c0184220038200110042222292034505004004002c002c0754080b542c02800c007683c140042501400482c1000b1024414004014042001070800c10000740050002d990361021213940e503100d4002190746416090001900c0d80308441a0b41c2d0b03100001b070021400e2500383d080f070582d803a0320501e401d0116424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 235094442 1250 235093192 235093211
    0x21030609180c1c0213020708250b0f060108010e010b04090b0d060606090e0f040309030b07020703061b02010f0209100c0f06052e0e18010b060c07060f1d01050904 71
    0x1101c0c4448203c181d43c51404450a0950041100c2ca41040190821490040000c4000100140100d07041e00b841c000c0d1082401c04901c1d00c4041750f0204281c01041c813074071801880752880c040e100715407040304245d848030000d0b030300d8288044d030202c000c0c81030f840c440da01032005010340035864000e005031071005080c6030108242510380c903055924942c4100c000c078a00000c02d008000c101c504442c0d000468070990081c60900d95001400050103210240c00310f00250b01164016100780b007040d0007550441010b01124022280000c00e01c800b01c41e201c0059031a00e542c2a00103106030003a01c00c010f1004105035040c1507800c100766442101010200d91190400000d0000111688551070041c00c000004400f40341c0d41c0c02c00c1e55043d00e1666a100c1000d2404001009100e8400c45038035840901c4806000400c50b0012105024042401180b54088000300b090310720844001010412662640c0d03406603100d16008094900740342103410340008510429003070407194040e00041c01c0d880030207003000600004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 235095692 1250 235094442 235094449
    0x80d18060501090204050901060309030206220c060306150305040b0115020f030f0d0c05030411010509042a03180305030412090503030d0c030501080c130b0103090209070221030609180c 81
    0x1d0f042542c0d11a400b180c28040d03800d200303103a030380948400e0408025511141d00c1c0a03560b03100007088186070399460309000da010700020b104416150b902407015800c0070348070310b005005048180112600d41c0303614030148410501ca0300819000303640103440b103101a4208030043d145000c1070a405015882500311149800000300010441469402d4045498800c2e140400c0240c1c0e804843e80b004115040c82071202040c1350000703031042d1840074208141e0b20161000441c024000000c1c1161284220307680140c038161007002a101c184096aa003081031208646c5148002500b17143c0180004200303000050000748800c2c5407514140040c04d2805031076640b5070000b842c6030b10003008140800d40b200e04648800f5003500956024105010141c082541e10b400441c1d641031101d91240031043c3c86600203141ca0340281c2c072064000740c0161150000340b07041c000c041e65501035606c0f00c80305a00b400d54690100d08482b0103a0b03000b00d8000346841d805444590740801c00e4820f0980000c454001d06004101564 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 235096942 1250 235095692 235095701
    0xf040305010902010e0103110318190305091203190e01030204150c0b01060207080a110f040204030f1b060c0b0a0b1018171507090e01140f0409080d1806 67
    0x500c50400070501c520148001807040d40030030186414582480181030504103a1300a49620050b1103056241381164043c4c4c15280c4050054203442d5145007000800c1030650042c01030007114029110081030384e108112241d42c0c0c1c40b4161280c840c089502d031038980c2c3e85201e6084858584014540075042c1900c481e001c0100705010b100704030104105040d44003c0202d00c114107401401c090000d400341e0351501482ca91112000140100040e0411412080c0765556600c1d0f0300d094900544215141d5442c6d29001404c05004c5406071942c43d4000b140350160015400080181c5150307903115401e011a556031440c220f10302426059201b926000450180d4480c2109445c01c284559070b25501496580341c213803140000703074200c62202e51500c0020410010005103004500054000a03030311030b07542400460700039032207402c00c101002050000081410318200c18590140003250007011641000e8200003c80300c0500d0010b100c98014051030030a0040c2d5400302d081007950300c1c00302c0800b20403560f030b5200f1035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 235098192 1250 235096942 235096949
    0x13052e050702030c0102010504031e090f140102101823060f1005011b120212030109020a030b090420040204050414010305060603060903040e0a0b0607050114150d06020706020f04 78
    0x490100701201503103010001c50048000a000800c0281095140280800c6030300b488000038210040d44400b101d8815001800145000d075801041e198452000126038400c250b00c0500510410310f000100c1d00031071244d142001c0e000ca00b4105070b07001e281c3d5061584024441c26284a40c4d8403602890f02c80014001b8501c00d00d030409003e6001e00e00702807000500041c80c1c02c03c3e810090001c02884a515000b4202c5034015003055001045c8802d0304022443c0c41c0c0c1241c1d94031500d42021000081000c00d80c0c000d00030b4021261800d21500d41940b0900041c0c0e00200c4010b00184038001b40441d0320b03002048158a4018007502c058540341d2103e0109081d19408100403091080040041050002c2404600e82008084014280724101203d40540d80c0c0264011640c1d18032148011a0754a04154003440d001c18025194031f407185014140315000303280c91540b501401c807190000440070308907000b981c86900340081440c00c0f02541030715884000c0d00440000c0752100d50800100400c00c0c248c40160005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 235099442 1250 235098192 235098197
    0x614102c04150e09030a0503010308030c16080c0106060509101202040b042301020c0d03050a030b0d0311010b01140d050406021b1c0e0109060c030c140c0a0b13052e 72
    0x250b900d05a90070341d00d0800104002016001403010301030880d40300003102d04580e0480415a200d44401e41d030b4000c940300d400c1c041d0502042c114484404c0004260140043e103070382c040208929070359030b04240d0350f07485445001c981c88150014140d4409020f000d2440030b810400c0340041c200350b01e61049100650190300141c1e050a0000304101c9450144000400202070038070151a00040c8c1034041001c40343e120350001c0602c14082510300e151442a44083c00c2c03000c000340f070001101024140a00001100101e894083d42421410a4154050400b003501090346204141c507050b001482d4800903c40507004540c415020080300108040341120303401c01100c00e8016001d5858104003141c5201c0c403400d14082882110701d01c40525a030040d00380c0084035205c1c2018441710340c440c607081b564213500280003060810049142107428500046000e01020140d42d60b80d001926600403c840340a1000c920b030340c0d046c0c03241c3c0511460420828540000000c50031034a54590700303104070384060080c0f0442600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 235100692 1250 235099442 235099481
    0xc03060507020c0f1f0c08091809060601080403020303010b1b01020a0f021606090510030e06070306060311040e16020a0c030b0604050f0415020901210614102c04 71
    0x180e40c07900a060307400911085400511700d0388480120117040c0c0c881d000007003d10144200c2d403028040e104007118000040100905005103c0e118104010b04007600d9841c5a4410780d40058403a501400c0702c54011b0360140c0082d03003140c2c80d00f810400903503c041000b070000885071071140c0c0d181c0e409002400303007810540c6411215490085000385042000b900260078000b884100b0071555420814000640b0003e40f9140d40c03041c000e80040e0054000340c842e98800d4454902005030881d4035501445c00d840d0b05139424421700441d443c88400a00850045003601c42c0c0240c080b0341c1440d0250f28078250780e490b0b801580c1601d4800e8641c8042015140d0098540000c142c0805c9040d2820b40b06030f50340305540001030782040c200741d211420401c5040c1541c000a40d4001850f07c00c0343c0c0285220f500d84d84200940300000c0c0c80015404020f04100d116501611704451300300e1999192285604050301c12903a0380076200760300744202400100040585440e500701d4070a02140755142c0340159641c1140d41100e411 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 235101942 1250 235100692 235100713
    0x9040b120c0108160c060906020f120406060602070518040317010303020304031502041415220f0801090f03030902010e06031e09030a0e0f040204121505070e090c03040c0306050702 79
    0x1400d0704002003079807070010b009035482d909417904042d006000a4100b580050004079515201c0028070600b070303035100913070b9010502c0d000481140329618441ca10554003885000e80d80d000036030340c5031568001c2c80c1e40203481b145083c0f103120307801a0440e4041e0003460425514001d5418600d290b000a0b002a00140c10006040c81800b92100668022580001046140502e014008211482e00064641c81040c0140d508558003190809460303021441402c00c0559a202080c0c0ca5001e115520401040042a0b000001c1c1d0764410304c41c1582d100d0704480510074519059504a000b44502401241405441034581c409600d07860003944c03080da0380d0102e8410030407070604003c803548802490a13045174001c2200c2c003004d40d480b03200c0c0300a450040d10075250200c4101c00040190095070032201e080e100801e030070001d01009000c9480d07081c044042c01c200c9500d804130b08998600c91040c95907000740303580f008140043d9004000316030041c0035032480402d035900e940d510000d4900544100300107074440000b84 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 235103192 1250 235101942 235101947
    0x90509090703021215060a060504030303020c1c0e090901020a2012030a02120619061b0f0807032613050c03011a030d0c0b0a0506120102030403120e0604030c0809040b120c01 76
    0x45030001b40c121240708609140a2000301140304501005080540100300a0800c4104101650b490305084800214201d03100200901d4000c40c0c0200b50310819030307800400c40c006010300c04c5404a04850b502c0c02c4120700042c07000c40c4203010500c2038005511a602031040020128000b440c05540c0d00903001d40c2c0d540b4480c1500443c6540585201d1280b003100c210001c5064403584550200c0f4040d042482e005900000240210300c4d080c1000791884101c0c80c43d803c01c10401c8001003610500c00d1300c0b0000d10b00300c113131982d2080c41d102820000082c0c05113030200304082408c0342d5040300c592240b800c9134010300292000c03a0a43d003c00c00c000344681080d075900119803406104101841e41c052800040c4100a038840384000000a42001980ca903114007084803500c50500b00c010100500c4000c0d07540781064a00105820100034240a03110320380980008091000301d0701601454066a900c041b00c001d83c0c80300070342640241c000f00d9000707a4400c1004800c3e110701c021031544141c0d0348090300d80803134007030000f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 235104442 1250 235103192 235103233
    0x712030207021509090f100302030f0102130608070c0b130206070f0309170c120a080a0806010315050f0f130c0302030108010b030f1b060f0309010207050f07060905090907030212 78
    0x403d04000302c00d00051009840c0e071044c4603171201702c001c1440310b00e80360304900380d003001d044ea007001c4d40601445e4501c000008054008001c207142a0303540c041210340c0c40c0d0003114191015242800040d006446042c00b081911810310340140521044808140c0240c0c0002c001ea070290108480342c0030017003031300000c1c1500085503000400030b005550310045404200d241d12000d41004083c45200c500e26041046c3c902040900750844c2d121175615980c4a02290241c2050700c22540d507030010b07060500303062000012800c1c000440310040c0180f400d0100003020030180302ca18100302d5400ca09240041030f290000d50185203418413043d01c00607038a50500d114542510702e50b240706400703a880210500140c50000900e00301d81c101e10054510010020ba000602d18450340081c0d01c1082c001000b03020300448194010b00041d44034104a800e00050411140e8856a040c440c0e01c021a40c2030604014a0800300c1d4030581c0036001070203a80f24246c0769800282c1ca4400810301c2140f80e4451004c213080d191080c40b4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 235105692 1250 235104442 235104469
    0xb0403062003072705060c03031f030b04080a120f06080c060c0619020c0d0e090f01080c150405060c030304021203090306061302071421030f01060c08071203020702 72
    0x3800d91a5140c4100e0150605200c4d8481401e064414200a45045506002c0e5000b40c0401040036a4484500300020b03580d4100b41d8604015a41c00f40007103040d21002c24070384003181e91000c468032941c1c1d034545031100c41c0d80009511b1001d21000c1d03c0d18846018413440790198150031540d0008449061500c4503140044800310903001d11400c000900c00c0c031000085c160b0340201d0003102404d00c8072410700440040e01800c0136001040c4144407003450006d402c015001d145131000c0e02c07813880c3e40d500c03040040d400307020038030858840340c225088040850170b00002e5040c0d0701000626851070242d0302c0000c5042d56001840d1021107030004410703c021403070b00ba4181e45036a650700004504116a08001940750800a440540308501c011514a1010200d405035100a50003c61110840e6409551207495034109084829000d14031090b18003045001c030705590090701e0b000841801682004410744040d000903000b60380d03964092000000150003010080200641c680d005a01c8190354410f011140e5100d46 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 235106942 1250 235105692 235105751
    0xb0316060e19030b061c050105070314070915090302030601080601091508060622140924012d0f031a01050f041508010f0510050a0806040303090c0b040306 68
    0x11028111000260108810f80b508451491041d84510000071081101c1040e541240c0c3c5800351903a05210041d03011034450455910207000c142450500c0a008040803507404003c90081d0600f4440792403100e0200703510b40c8581c1003a1b40256180e0b00040e1400e4026849050681c5c0030300c0041c02801014090451603840c1c50841580031424207130160f0302c5400041815000c1c4080100810310451041007503100c0100308801044640303800042c0c00e40300401201c140072103205510040d9441c550405020680c070707181c41c0d42c2d42016420f2101410030030a651542d2203602213204420790303c041d0034045440c001c0c2198001c0242d030f03134550b1805840801e00151014441d40f00b02004000320b407a5003028a8115500311000180105025021820460343d42c0041c2115071030007141c600a11056803015003e00015091200300503562420050441c8560041c420160010b001080c0064042d400c00ea600341d1194824940203604c84601c0c0307100f500154402d80e00d4540751800e118050410301000e8110301c6a01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 235108192 1250 235106942 235106959
    0x110415080f070806010327020414150418021215060603100608070c080a02010b0906040b010f05030c1e0702091609050d02040e1204030b070c030f11010b0316060e 71
    0x164064503540280b106052185580c00518180c1c8a0b500500c130011980e40d2242c0030440c078222500c04049560000c90045e46024501000c030484409901c0c07041a5900044a980070741c04140005040f25002108000c6204580840181e88071035848002c82134201c010803034404031400942c0f1940c0040d007824090a020028003011080ba100400c00380e411504040703540fa1504a005c0f11481145907001d48008404107200c0841a4190043c4035500f00850341c4039103a445000c100821504d102007080d010482400101f0700707040c0078202540d4004400c1c0265410001a04a01c2c00440d88080c03c80f121752a00007041811072410005540d00710340c0c003800c40c0c072210400c0103002d0045241c40c082c0e588a144500d01d03200855442e9004402e4540594040e2a0b0111030951006140d0301702c1d00044400c04101c500103410700c1d03c144032140d45160144ea07281c0c5429201d444c20f558020b8900d5980d4059520350800b00e0050f10308102804100c8805554061907610f40100101f2040107403510380d1103084c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 235109442 1250 235108192 235108201
    0x4120602130e060f010c03170403030609110c0613150c030506100e0102070522061e080f07050103020d020d18020915150c03040807032a0e0a090206040911041508 71
    0x120a03007091504c000b03080407100504141401e8440490702004c440400404008010400d035040d00007000f2100101d00038041c00c00781480040d5113000d0a8403038481607000c80d002a84805040740104074982c004c0c2c1d14002c03040e500d10680016980001000408684c41e04d061120707505000c07103408811100c0e0b00e41042c4450203540001d4031802140328130ba01c5807000303e1203201c02c40d60034802c560321203e90030410000c413030350f940e540c2c0317044a260129982c004e501e200b40054030032004101c010403101000040e0400c241010b00640094005002c2800410350078407480c905808039200d5a10340c08001055041480c195104110710540000d1509485440e070004000407519407000c0644c00384552200b9a032a1070503500b28501d5406254410460b503c110880041808000d5001052500408074203c050003d000c95002202d1424821105540c0700d0400041c88014598080000700e48000c00d030b60f00d416980c4000380203540b048214115032540000d420448c503003007d0108942110325081403400c52a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 235110692 1250 235109442 235109449
    0xb070e060d2301140405060102010b0418050c0a2d030f03020a0b0c1c09080c070611100c0804020402090a03060c0e2704030f180909030f02060103020303160201020304120602130e06 79
    0x2440c01600551b2104041a5035038000c1d080403042d0b5201501c1084141f64031f42040c0c3c4859403241e01034502d4040c4034444910760502550230b5064480f098000101d602c1c0c41840d500900c0c04500d5150718001d0105d1010000071201c244004000e4069402000c0348070407418954003c01015080707507001d18081000c0c104801950328030b46e040c80c001b5040003901001e01d05081c0303600d2041c8450b00049010342c044c0480d055800070f2804403c054050100c994030b10030410f440c3c0407034540c1501c00d008195000001001490a900203007001a800781c5801c1c0703001c0da6943c55400795460020f51320b011600c101c210000a0400030044880841c41c8110f11034044c649181c1801d002401600140030009100c001080c11401008a00301d01d00100001c14006c1c1e685010200c020301c7d14450131000244036550a401d00c0e0310004000341a2500240071f14607000d60114020503074851804202d040d404248000110510a43c0c0d201254070700500025035035800510b1f10020001c080e4100a150080c3d0701c040c802c8548 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 235111942 1250 235110692 235110719
    0xc030c040f0204030210030207201c0206120c0301180603020d030804020604030b04030c12080714030702010e2401050102490c0308150d0b070e060d2301 67
    0x2501618005031040c5031091601c040e00c0760340c0000c3c0d00103139821240c0700000c0e4140d0050100c0b6024200c00790388000300034440402565122401648454a14003400d0303130710030b1003030907888461001f01002e04c0d0000b24614184c0306c07003089900c1e00d201c010100c01080803c00600e801c0c404200001c0c03080006030309503030000303041e01040307000901084101c2d80010115107400044901841c0c01c86042c031824a041e01d002000d2040d224002ca0300b07400a81210b408090058603a070b40034080701d403a00d462501350a02c1c1c1d0455900001c040170b085641721205164009000d11120308806030118540c4100840c1110040000f00103070720a0b41194011943c0c8815140c0b030300c460900024685850000728071750000300c500d40703124200041d004128541d040d100041c4e004020040c0040c0300e0307155481903a50700c2c85000354402c3c9070a81c15801c841c401e140d000004032101d117100e13404031700c03401c1202000d42d20001044094210001c3d9070192940d441c10000805a144040032a564400d011048958140482c546415 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 235113192 1250 235111942 235111963
    0x2202060a11010e1e15130c0f08030301180209010806010c0c0909052109031c020c181005010201020a0e040207020d0503040e0108101505040e010f0e100e030a020303061513090501170c03 81
    0x41303452419a00411642950850083c44238a080654560310f515495859a10030f100700440c20f5000c0c3c25020303d22070300b40261091014141c6908117169920780040d1441c0b01290400c413451000c0501c013117800386082c460007000c1c60161000380094800f025041400ca100195450450103081c0700c00c410641d00065000b440c0c002c540304a140540d04103005914040f10303103060340c0d440f05040700c52510381034030320070f10a01c145400a030410f07282d9507410040e4206d2095034000f0700082c88400c08612a0b041c5900103002c5a40702030b01d4940c6501e030988030b03e8150b4001d5080f05c420307100c0000041150341802c10440d61400030a600801004050010b070000090607071084600541d02c413544541302000a610141c180d8440710014041704810010740742e110220310038030300031051900c06114044000002039444000303a0350029859030321240d081203540c8000071318064800008000c1340110f141e580d203083e00203194058010a0035418800c100d507210f280480f1500041c4d11003c0f404200355000610700307400c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 235114442 1250 235113192 235113211
    0x2100506030a1202070b0331030e0f0d0b0c03100905011202121e1c0c0b060405091c0e010e030c0108010905100f03050d03052202060a11010e1e15 64
    0x8000b80040c007681004c0319a4000c9000e4031b0b000c0b0820082004000308440801201c0c0c8817003002d06d0315051100350507078a40703101400095220b44110364608140c1001e558116001f0080c0c03007801c0b0a41d96021044108840c640c038458008800d00c540c04a01040070360243c852600d00740180c0d810400100144202004044e10643d0000740f40c1082c04c0003400a041078441c2111640c1c4100e11406440f5642c0c00c03080000c80700303080040805540306114020140006034490100b446c907841e00000c01010b04000380c100c2185005103074040c0d80ca1a030851090000350714680300e46940341d0310b4000142003050000314860181c0c000659140d52a80d020481905445403818000703a55200c0aa5240340000c040e00100c8400c10440303408400c0c401d0009850b102029659030601059030f8030700006110800032111040d81c0594403428500510301640a014510030340c0c03070206600165000c0b0303e401e44046840186258200d4031905942440c5210b014940e1034500e402080d40c00002800940c46400003000050b2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 235115692 1250 235114442 235114463
    0x80c120f030d091103160519120821070903060f05010311091005031603060506030a02150f1c0f0c02010e0a060b15071406061c0813080102180102100506030a 69
    0x8200005180b0700308140b015044407406c140780c0c0e081407441d000c0ca015644c441d50850303641e42e0415072050032300c0066480582c4a4514110903990b49109a084202c00060b00302011100381141d1512a424070b00c00d00031692440360311440c50410b8011680580e2005800c01d080c1001400440d481e030403005c0500f00145c2e8002d43e10366990b045041c1c80e00c032680055038503014500d404103004100307400c00d2096a003e90402c000c81c0e2551410191b1f16018641c0003900105a01c40c40000c10800c14064800741030450000c500d0f00d0300c0900004101008211074011481c1e640e000b1000e800f8440c070032000407002d280020401c0240c007000440d41c0d0450b40000410480d02c54a4100c00c64039850602920078003501c402c42d807216600d150202c5060054040228031303100300000280a0318240d2100c44000d130000d5000d4540301240d4540c0c20127a803088080700c0c0c150841640000b43c000091001b8440790580800c000c21800c41200024180020761102006440c28441485071036900491a041f00c035030300c64090306 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 235116942 1250 235115692 235115711
    0x1c050c070c090204260a14010b010810080601060c060e070612150b04050f0103090b040b06010206072303090a02150a02010c0302040305030405100c050313170312010e090309030304080c120f030d 85
    0xc2c54900e49140042680d4400c446540070071505400042729407400340c076040c1c51540c40714117884075032015115448580d481a0010450130303008981001d9428041c036030100c0c00d216400b507010301d404d00c1ca0380824009140c082c8403060314150780c400c1c42040c444080b00b00349000e18100c403500060203030b40206446401c14001460b01a8066404039165640c803001911540ca882d080c00692040e00700d9003d8094041c1c40002201d2901c94910036080581c00c0fa030084103161003920500a64000400208262041c26038080141e0b592850140c811401d0b00c03c819038a001802000782501d50340310303805082c1401488140300240000c003c0d1026990241c407510055103d40c5411280818407070000340545c00b00241ba94080ba00f40340e0030708140c921040182505402c240e0131250340e807242500d088a003115800041c010400c21f06a80c5402020500417030f41007800d08000241154015030200da45e95004031440c0106040c880c0800040309205805440d166840841e410345070f00c01c45145500d0140d8506146 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 235118192 1250 235116942 235117019
    0x230a080c0a120510050306070503091914031207030e0a03170702010207021908060f041509020f03150a0b0604030807030c021804053a051c050c070c090204 68
    0x14402000c000b0000d1182e03003410740c0f654081c005140a094040d00030300000940150142d4100d0307014546004c01007100322000c0092941025100a0403100300700b02d1408c06820703440400180a512400300c0b40d2240500b0000805001c6946140000991f034101012000202c0e07000700400120030003800b14010540d4602000301e00911440300000d6220001107000d10300f0405803411081034525103000c4588585941c0324440d9549400c5170300400c04282c002113482c00440a070005480340d4400740c0003013000488040024101a20348254088114104081000d42d00c464080c28010807025189285018116140c94144d131081c40d8018007401500e028a00071502c83e16035000c1106d60f403ca002070f0f05d06151501c00d0301d070804822500e030100c2c0c0d42c1c444d80e04040c0341c41e0441c0e189260360030008021214204401c0d5403039040458032107511944850668000c070098081d15215982e52802c045d61480e86203441c5c500900b15400c0b1406207072051000b880a0716007060300d140e140c1010009421503800c1c05025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 235119442 1250 235118192 235118207
    0xc040e03040f030c030303050903030f150102010b130f0b09040f1b0302060d0912110c010e01020a0b0a091e080306010e190b0406030f0b0a260d230a080c0a 68
    0x81c00030480020000c2403202c100540c0d019641b203a5001d1080d42c94105100703540b4001542c103604400c0c408804685a0074240c034440c1418001030001003030091743c80000a00d40c880d100c06800b6415282e22881103006103d02c2101602d40086404198504040e00c54080c8500b000c0802840408a80d2066030305039014001c3c40000c1d81d006140076500d81078640d0b408040c0030648000c07036159112105c6612410701444074181a60301010003400060241c500445180010742e0000341503004482182c400308590103030051050b842c1d0000860342501c075140084894050915500103001c54803d02c3c2c001901c0318003141d070440024070b09007000300c080d600080d050303031200205212034200303440d40024a144003d0190048a000388c13010080c010f0705074107103400d50300941030703050303102c50610014404500741849a4580c81c028003124040007408003003143c90f00c0c0358552854013007080c030002020011225415212440002000e4a0410300100e00c0540000d00142c00a00541404200c440300b56220340203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 235120692 1250 235119442 235119449
    0xc010c1e0c1e14010c0219120611070f02060f0403060f09262b0c120c030c020303060d0f0b01080c1003020c0606010f02010e030d29060d050604020f0309010c0207060e01020c040e0304 80
    0xb4414041d5031108e80c070601a0414500b00e540504064650130130a1113802542d034206d1f001014614884855401c0110552001146010380301e4184808004640e00d8410680041c0120400007071505803402c002060071207200c012205440310554400701a039540f015141341c060120701030703403c0159114002c000019003012602156182440d0203080c01c0d0b001405021002d0034440c01c01804c8885c007002c0701a25903402011015901c20408190325042014030003e0040c014007280c13950014603035620100e92030a9100050680c005410741c00d051800c18a50f100120315420114070744200101c100341c54204c01401281403000c43c0803e5941a030003034000c81d0381050040140c07913403240d10004c240000d1100c010b01003808c05030444210700c0c3e465888016800b0113001441e40b42803480411803080034050043c01d15030066004d128400820511901460040c0502c00020507080d841c404002c1c984500c5500c21030400c20000f4035003101d41d07008503100e0803143d4213031404100344111882562862240f82d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 235121942 1250 235120692 235120729
    0x10902060c0d0806030d140d0e120d0c08061003020307020f06070c14030c190611030f19050601090603020a090f0e0402010206010b03090c010c1e0c1e14010c02 70
    0x703225140060100d4194030060301620b50320b050f03407642d0082c903070f84000822403940407e60481243c0c804804503009052010810b480120b5038081100282d41000c111030b0541c440703480c01095140d110b00c030a00800414201d281f40200c82458075000107801c00f980aa034403001e15500101162005109005c000042c441c510202c413914109040c0041900f000968192604c3d5109241e010804101000303d968002603140100700808440d021507401e9180004104d0394182d80d0280014500c0380040654458004103c0100b054940f008184820030303204065042d200703150108200c0782e40e030417070300707000030780c1c070246401a1101000c40c4140c0350700c03155800070726038084407110000da520700521f000b83c4114405e909032415644d032110311649500041d03400311030940209051000c5540b144a1001d1b50303d0003001c50688140d80355003924810043c440301038520b944142d005102c4003400322008d00921840c00d000d0718406181a401c103220a511070020380c10007603c1451182550385071802c4074225013104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 235123192 1250 235121942 235121947
    0x30604090f080310050402190315030c1d07020c010f030513020307090218060c0604120512070903051e060a0e0705030321010e0f1902041208072604030809010201090206 74
    0xb03040c044081c1d00221000080041c0f0f80d8000300d96800c1c1070007079035850902c1c1c80702c5039240340c0c840f034059014180520240048078140c0a000010901c0d150f0004002d101e41200031a02c5038200311480c5044070001d05000565000866103561640d1040c803404060180f03160004064498259a0203d00c180741d0010754144600c48001c03d658075242d00034800c500c498009002603980b0f000030710030940158034a4980d10380000000401280310a201030355100d0080c40c00d589404c140003112035140d001502e11340001405100d0500400004010000e400101c8141c5400700da1500d083d01596801c000b042010015101c440c3d004109000b08101c0019000080a4945441c82e4201d406103a50340c02071840080710a035400003481606c42c00550b40240c80f580c082c41425039030214410090710942d03111404889d803c01002030340040302e01e006404a4880c002c2182d9900c40750a1600f001c06440c08808021007100a0b0000c1c258003110440e0110b03607005d118035441c1d61342c11006034010018204040d4018000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 235124442 1250 235123192 235123223
    0x61a0409030e030c0a0308030106110a0209070309020933041515080105040908070b1312090824011502011b0504150e01140c0718050702060109020a0207050603060409 73
    0x4000d61050b905001e07001c81d14000030315410071a88066501c0081c2ca00c94041005004880c41a900c080c4111030b8042284c482401590103d02c0155049030135500099561702c1d4002146000641260040c4e20120440e100645000c503910910890140300c041d03041c11080503101d117880307542000c001c04100300070300a20340da0381e2144a07082c0a80e00d09007200103030000e80080b40030311300341c401c4402854004600904040041e91104050a40030b4030140901c56050140c20024035841c20b80c103c00ca0080d915110480d2815400f9482c00e00911206600244c80713401901100103500c5c030382c0b411a032a9076101c1c1d0001c40c1c1c9410903401018946101c440b17600340030700c0100c5040c0d00b250041003110054001c050603d8030380c0d04105e03641240c041c070301400281c0c0c0400304810140401d01030015215480166040d0b01e0f516900c036885001000403e044043e110030400c0320081d0140078031801481e4480b030640c9800c1b10143c0003903c909aa0003035901c601804000700d080e0b901d03540e111030041907000750701e040a41c06 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 235125692 1250 235124442 235124447
    0x7110915092a0d0e0d02160303030209061314030c030f0a030f09080712020109060302030411090a0e0102160b2206050415020d09050c03030f031b1903020705070e13061a040903 77
    0x504c84c074660701481210324000e40548006101c80103040240d000d0b244460965800301e02943c00ba154544d030215041c402e42d000c403010340040070300030081c1044c0e012038610904141070a10040103004c5100341c018000b040140da0300850422101c0d17500d480e100c0300705030003000280d074124400e0300960800d2088030306c00320b10100d2100d0b0306445035001741c07600c54150380e49290403030991108940040003220072805030300040c1001d920054105400c0000070440c0c0144501840c00c90b040130f540b0006045120041605000c410084250400c3c030510b668001f292174558140c41034040003030700820180d9100005018400305200c4800750020304401036544941101d030300005064805001e9549018482c40760701a49400021100389030802c40e01c00d4156942c0d080b51a00300c014040340c0d0100c01e201041680107110016020383d090103000d40340140c49001c0e231300741146040c01681001018405020030b0001e09140400c1c4c00784079591000d004140321b06c07072400001d07001c0c3c141c00720660800e0400010308101034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 235126942 1250 235125692 235125701
    0x301090b04240903021c05160f061d150c0702100c0c060f0f0e032104030b07031808130807060f12020306010504030f031407110915092a0d 61
    0x74481d01d0816040c505502020100c0d030f8420710040c0564444140e080101c81214045403802d50706003041e40c10007294100c2da148581c1c2c0751000312a10b940202c2d100003000742d04d12940c001c40081900400c1d2029840300c809550758011380c90003640030100c2d0002031711050300d60116100caa5010700700301c0030184104400b034810f0606207800c070380e0b041e210709022035000d01c24480c0681400250ba1100c4110101c0302c4e0540309861544205a010300864100b8228a141c0c540390350025000d440055a0712451418100580384019080ca01007500741804c203d005841c50840c1c0345420781114240e99140450b0025102c03512160f448800300e4024003500242c0c064121441040100098442410010001d43d44c403040348411911603002c0fa400340014408a440c0c1801085442c0c82810a402c100a554000c0f45090308480d004076000007c508600446060400e02103400100a00592000c00740c1c0d240011601200101448244c0c3c4004075018000003414901d004c0414101e0b081590b9188208040000340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 235128192 1250 235126942 235126973
    0x20f040f0302010324120f050d020d120204050a061101091212060501090803030c0a181212020606090612010603060515040605152a01020d0f060b0702060906090301090b04 75
    0x5e10340004004c4a039012044466840082ca6a00d10120f042101c0132241140c0a0425103020a8501d107510008004002005402070a80c004001000c1c000d40d00810720451480240700b03080c0144001c01c4161031380040b60302651840c1c1055100260420031481c0188039500c0003401003805a1101d0745510f0b080400790590401c0c8540600640751180300542d0740422174820030049038000c000142404505402502031402c441c60284400141c1c0721070742c0d0700c80c01d981c3c000f80c40c4907044003038142c10400d034643c0c241d142c819640050321051428000080c00c540c002014907014070b001c003c0300030307003c0429071241c1e01a503800342d02004a8203003c0b2850b203821110f00b41403405140380c0308010445107400444526522140805945090004052040c0003000d01c210348054220308054014826001e001034604051045800511120040c00c840142e4a5661081c0d071000030401042015880d0b40c800c440c041d00040d90030a40c1c40d248080070030300610304e02c1c00c00b4180c0070503001407008010381e070395061000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 235129442 1250 235128192 235128197
    0x16020d0206120103110406050306010506071a0c0405010906170420030307060605090c030609130515010b0309060610020c0103091b0b0c0c09062d03010c051209030a0e13020f040f030201 81
    0xd117100c03000380021103946005640c1c0c10f84c481001000180b07051001800303458442c0b901c80324140251804446102c0040d10002150400820140000d590005203039006020500d0302004482c1102c4d115815190054030140076074100850815031802200c1031700d26690400303000c695440200d814804002e160a0040c54442c081e0080031400d000281401d0740e010b02801403500c1030719211030642000e021454142250341c2d02a1071112203190318440c002d20b0080104194859a07890165403050134968000d212610520300710842c01c00140e40050120380120082c03d0014411910303007800c0702000c0103110060002c2800d4500410f4094030302015140321214401101e1062449034104000d117801116130310f8100440841401c030b090340d281c07000700c108411030b40e4120495a060012a080d80c5940c17024038041200011131100004600d80380c55841882000510f04041d09603000170f01d148a42c0703d90341c0c41340850b18850400c07003d00e0750494000c404410105a03a0740d03501d000c9900303a46030f1403005070301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 235130692 1250 235129442 235129463
    0x10609050909070807080d140703020d0c0f020607080912060c030a09140604030513090b090f0403120507050a09080a021e01200c0103060530010b0414220816020d0206120103 76
    0x12000003027642c0c40f603541900900340e034080715501102c0c1040d943d6000d0300d81b104241003001c003580b10080103000340d40c01200500da4500d070080c103200e002c1145110f90a1141e00010400030300d240050280c9030011078604010171440e9450806907090b00000244800c0c5014100500041540040040100401a000301d1154513a500070728421a0452a8050b401000c43c0c0300042d0000d105002c480e030301c944279082640d0000440e2400d90304686049880d200030a0700001e1080c0800d4006245000405a20005000203a01540030441f0781000c800000090502681d401d0140c1e03000303850b904000c0c10608004c585201c000303d90b01b030f03561a14000e0103003c81c4c1740403008030f11800d12411040612241d03000c6d9041a1804802d55445441d0401d01d40c440e55580f1100c0c2090765130340d80160306001805a5a10320075043c6a0802d0248082c0000081e600740520220240042d086800740c0324407540007084850444240c0c000320700c0e01d82d5034840c02548041d000070031248d0750044a5900b81660300940010b02e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 235131942 1250 235130692 235130717
    0x90506010b120916030221030d09050f07030515061809070e150f0904170d050610020a0317070216060206240604050f041b020a0b06010503010609050909070807080d 72
    0x98590580102c001001c0b405110284050305181d55002c8481015810522200070350711f0b50f95003103801c640700c1c01c1069900d80c4001d80c00d01c0f8040148910440b6010040c2030308500c0c50b0364143d56400345000c40710f00745403983c00146250f918800151003900b021564900c052420011703050711280e0310b0044201e480003070004944a02429200b20762201c030064580d0030320080d643c00700500104014000c54510501c141c0d0099028848406000c0d0340c04241008aaa030070540c0422075405070f403090040440d8051206500813a80c0f10188007000250712403400360360744130308208030f042c01c4640c010320041001a500c009041070b40000c46034841c541d01c400b8505511100c02400c9240c8415169455010703006010500107031a0002407000d4145c4000c0c4001403949078044c0400494001020340350240c0c000ca42c10340c091003200e022440d48588c003441d24a203950706282018208441ca8002c90703008480d143e0000d0403411003080032034007400540d4201c40ca0107a90310b640035911111041c5800000b410800443c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 235133192 1250 235131942 235131961
    0x706021f05060f1e060c101a0904020d03090b1c2f0a0306031202060906070503100605030c1c1b0504140105030405070f1401031d070603050604090506010b12 69
    0x2140100c4000f400e071240384458404001890000100300644a000840202801d0b5600c40003040c210b4a8680600729071500c8802181c11126684144840c09030018050301e015920413083c59440341e8103c40e1287d40140c1810102c611058a40040b00d00d0300001a07100c0100700d100704031510340107901c1024814941c3c0d949014041d0a410200001c40e10b0b00c041040d6100680c0ca405400c50f407201d4070303001911603960f444130346c60b40e02c84050181c0940c01c00300c1449035440041c020198400001c1c18003601c1c50500c0c01c0510500d40d66031141104010010000c1150740c0e1b400d10485480140c4c204810150228009920006254009001d03008001c480d01c0004c501d8060f4003642c0448034490a03600c0382e07a425900540e410752005004480d103000c0c80030301003203095084154a0241c1032801031020011000c0001400703c481185030b07000c0c0c84808140134118102c000401b00b041d80d55610300030070151210b40101d4068a0001002042401080c2c00400c1d0075803220040d241c6091007007a04412a100c20030712 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 235134442 1250 235133192 235133201
    0x209010c060216051002040812040b07080a1205041109091209041d0d090603060501030912140c070303170606160b06030a060203011206060b04210204020c0706021f 72
    0x105010900944112010580581c0034040000020b0640c02c18541c0a590300b5080500305403188040c40d901003402c2c00100001c00c1702e201040c0e40e03685124031f081d080c00309018180c026404010002030700095440350441c800c2c40031a0840117245800e000d14249450b10070692002c0c2220580a004d4180010301c844400264900c410484040d400d8175018032078080c040548181030200d03451071480000c24034121001c01c6450610381c09035540c1c048141c10070350000e0aa80071a4000d0381054141103844003c2605c6990500e1881540d0900d10108038649913046014010310450310120300400200005040c3c2000003100356104091b103180a41c0d8405003000118090707008804030382c0400504450004084076407240d080840141210103201740d5a540d04240d900c243c0164200b00700c04511001001241d01400000e00351014025080a00380b48002c982c2e0141c19181c42d6002c400d094401c82507407255411103011142d45c0c07007903907001502c5010180d0746031304d40b68000710440c1c076032548000c071444240304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 235135692 1250 235134442 235134457
    0xd030f022802041119110601050d170a02100606050702011b050a02090903070c0603090213060b0f09060403120f081005060306010302030712050403020708071a04090c05040f060c060b0402 82
    0x21605509540354090000600a100c0742c02c20042c1c2c200b000c5162032a0400f0314031000d02c0c0d07540e2046c030340c040601c00260420106900c150301901b200780365040003400e60310044050100d4894010340b1401d882c0c1049281820080381000c401d49400300100740564410014103a090003030721820078506496000c0001d1000e02c410281060b0808000a00185001004560800c485d9001c0301d0901800381c55240781281c0541c002c03c08240d86419080c00c40c100401b5020004140320030801825142c1044842c543c0300d060308041143d0b00004c3d05c51016501c2c6810b89001c1c50b0840e0402c0d0002c80c200740041d0107040614402004600e50000181c2c1c039240942c0014242c440c0901104c0c15034458000642c041d400c082c1002040c04074500301c0d08048a07080c89407501c00c42c0203500800215140500e1942007400a80040313024100c18070201d4181442e102c00c54041341d604500003d40380c1600041201c0d140113603004640400f15100740080c1c2980d100c2c2c900c6121501428040003541d454800700300484c45942e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 235136942 1250 235135692 235135753
    0xc0b0c1b032502010c1505070324060e1809030a2c0108150d050a110126060d05070602010b010e0409020108311a130203070b07110d030f02 61
    0x100c2c21207007400d1144074041e81c62040c10328081400c40c40c1d075044010801c6010b1011100d40d00c0e4200544d559241c0135100c003603c075501c4c55500b01d000d00140c1c1d80f41c0081c076000d55028490b0001c09a1055161002c40e200d00c12000c03112039005042c40e0400d03a440358080c55001c4c0002c3c41e861900c00d255078284511802400c4424010106524410010341c0d9285005044850002d190071040c60251035156a0090151241002c0c00e4407080e50310b40110315020180341d0303504100d0130703006d030300340f10322448201c0e400c0251032a05003025941d880001888031201d41034000c016000f4031100050141c1c05402042150000341c1f1940311010070001404102c07000140043d0000e841e081c00714620401e880800c14802d40d0000c00b42c504030320902e41c208605907403d1000c40740c800041c00401686029402513680086210110501800c00c0e0b4001a91300c2d01e280c00740c00c2e6403003c00942d02e4100701007010310406200b4040d10200c1e40080600300580140000c072104409401038010300c25201c04106150b43c161480386 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 235138192 1250 235136942 235136977
    0x8010602100e0127051018200d0c06020d0503100e062e030608010203040b041b150509030f01151205010b06120103050d0f050304030c030c0b0c1b03 65
    0x400c028002e03048003040c1840301d560b0741441e25000f401c06081152155402e0f10728100c401072030b14000d40340c10703042c0000101441c40c10062049204505038820011500025500c0f00807180d480c000d06018401c2101c1035000329013511820802103d140503a04446441e02540d0100c03030700601c00c0e10144421a4800140042a5018000c102c1c44410058011102400440d6001071150070f82c0c07403240e1544918000d2100d400031030030846606019150251026034002d40c1107060503500c0c20b10311200900000c1c81e00304651015505646601d40540c0242892083c1765551010340d10090b08a40c814440c1c140680550b088006207042c05000354004c00b0356441d802c150710340c079020f2186154000d44400310381c07654035501c0000e0b0076541c420144c03204480324012000d00b13524628007103103880140c4028009100e88544400c4e03802e5000030990340d215808d403e10006001e07541c5401c1f1511040e035040100466990f0017842018000c61024148010319418450000c98017602c510307541c0d0041444a40726010174 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 235139442 1250 235138192 235138213
    0xb060d050c091206011401051207140d05010605091c0c0b160507140f0a030f03260a0e0c01110a1511040909020102010c0512061908030a020703020307050108010602 72
    0x40d03005a50003142440e24908000071034000a0b5080100c190485460388500300600a000d40c8092000c0d000100f42001c0b45800e10041112140303180080202040c4004c3c44c00d031080c1c11484204035981410000380401c059a1a8000581690000382096001e440d102d181002101100c3e200b242103c4d4010400520480c0b4080315112141c0c440c05458a0011700c030012a030016004001c00c401502c2c2c1d8820b4450201881024450038600181d481c1d032152060380c1c42080841c031360f554401c00c0c803501490078400c003182c407140c0c03540446900804080744404110030401078031040c0d404075681072402030030369000342520001120031202c18002044c0a0300070003554000102007ca52018804c452039000c10285206007810584c0d4000fa48000d91154503049114219a0b083c420000c800101d41406420462a9548480c0d11400282914000e10599044410401c2040c0e0017a00030101c41c400c0b00d80c3e4181c0340700003d440384400c0c03200304c0c060b10940c14089901e6004a0304030b41a40c026038010041c2030301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 235140692 1250 235139442 235139467
    0x5100b010306231c0f14060403050d0e010615051c05011503090f0219180510090b130c09030605181f1b030501180504050c01050c0c062109010b06 64
    0x9045110307901c00b10740c240360721240f8050391100c0313030080c000c075003403c000203d50601030240083c00003588500d8208504000000f60000c080e1804403950300000120150003602660040000d6001400b00e0145440310042a41c0c0c0200106400050980a06041c245d03040640c402d445c1e0078092582440504510645018800c0d81700b584810300650000011502c541c0100364442c04c0011b0700104000c400c1424050075820a5400301c071180788140800c51490320f8442100581d05c140545013400e500c80c600102d182d901c0c140c1010640172280400c20a10082d4500903101041e07a11085031070f43e01b058009102c040300901c0880892401c0c0c00904000c140400200e09410b109140d030f5a003180d070754000d040c1195442c0c203d0300390640c1661000113042d41021038185110700050b041320003c0d8204410030000900103d2210280d0400b800c00c1d81c1c84041c0c00c3c800c0c5090104030310910790450004150300550800c0440c0490911004e40c00c000142e440d40e003a40303401d03030b010300b0b45898100a042112148541 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 235141942 1250 235140692 235140749
    0x30c12021c0c020601053303090102070501060e0a11030c03010605070c0b0d1514030c1002120f07020103141b0901030603080712030c0509010909020f0f0705100b010306 74
    0x51001e114412044805004011140344100700030050380103030014071241c04c000d00003450720404424102c88842030481605a00802807154a25006001c00480d0348008250103440307045911070001d01200d610340c04540c100c03840848490180504000050103031820820071a4040c801301c240302032035a0700b085410b0750903a01800d070484c0c454003031110010740c1d0044803000e414030000e48600450590750361110182003614039000a80b980520f803118140654000400454200c0305845000d940900e240c1b050f41003001c1d280d070b103407000400003a0700c03500700702614000c0104138400d03242048500500b2110558455040f201c1000241002c041c02c0c03e4241c0d0325025068a40c8145008104152a607403100a00c2d0000312080303802004002c1c840300310b190503000315030300d0381c046c2d26015003021981d0000902c00c150314810303500184c1d4000354040450800c07108840740e403441c80c1c2140d42c0c0d44840e403034481c0d079030b00081d041c501801d0b00d481030000c1c103588203008800454920b40203040754450302c0c4c0005079012 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 235143192 1250 235141942 235141957
    0x110102370804080607050301031b1203030b01030e01140103021002030406090b16080708070501140601170a090c060c03090509011401080717091b0d0b07110a0602030c090f01030c1202 80
    0x1007606200c00103945404001c0644190400d681c0c103520ba503d1031804a8240c2c4400610703081511035640c0501040d004050900007103a01860b000c680c03052a0f400580042414280c00107441d401c00d0015554402c1a00525040301c3c400d0700c4042c84000d000c0d42c126282d0040380278080c00981003010420503008410054000c9100140701200300c080300e952560040e9101500032039000c200810030780180182842007038091402c0c0441e030b0400e441d2420000382918aa90001c00710180c216003c140c0c40111580403c8105601c04a031058454442901500800489000702e0000d0209807011543c2d0801c181410b04880004880748108070345900150b4041e6002800d40c01007011840c129030759080708149190240c0308080242c14030384582401e18255006000c807050240090b914408001101045130903440042d81c54641e280c00b02c91340c3c040382008801d880160903580080240414005514000c02400c0c00807541d00c01e01030720560054042c2d07001079174084046003440030b00d01d489810301d03001403122 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 235144442 1250 235143192 235143203
    0x50a0e0f0303042a0906060807020f0f0c1302070f21030921020c03070b1b030301030c0510090b0f03150306040b0a052707030506220f031b11010237 65
    0x1500c17681c00b5000c0b40e02641c000e1000940010620001c0c0d6014000380300c9584026000d003401d88a00b060b0302e0794641483c2200ca00805c0c85010b10a80700c41d965064078145980040381e004a007105007840c0f01d01881407100c0c0500307070914104080c440c03030292080c4080750717521412100f13040d218840550350444905030b01c40c0075402402e0700c03002d282e902030028001a01c1d0b5810f5042c0c07039244240395910f4180c40406410719540c41000140b0220348601445000c846085414903800f00718440d0840b0500d02c80c3c2d000d03d140c008041854040c0204450166202c0c0c1500c801c61000c45802c0400c0540e110402e0743d002d08088801c4002c10401d1907160406903000360124106d40c500c0c6004d9a0004000040341c0d40000380d60842c260600c01c1250034805640c1003501d002c0b01486001c80350f048c0354a4124100030007400c442d20200404d0416018a1124030794016407152100c50200d207040518601c0c12803100c9030f006018085c540400000301d00740c1c68011600302e08649000c0002072006080452604000360f48 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 235145692 1250 235144442 235144523
    0x7030605060f0d0b070801060e4203060f100507060b0a120b0103060c08070f0302070f06110306030601170309120c04020726040e06130e01050a0e0f030304 68
    0x2c03546030002a0307103403144190b808160600e0410340040030204180c0014040003a9400d8165180d40d600c04450845903100c51024642c40c4040f441c4e222031491420210b0f05175440e44c50607100441e1580241d4450303441500d901c00074281d5801001049261a02160003007141800050082a416484140103100c050b000428058817a0012172030b8003642082211003040c00301c018000c010711800f0300110000c807801c194143d4203000f207001e008640d050a0003420146e010070200f013400a040e0790f0201c0150070102c100021916040b030780700d40340d2088038658000d101d20000000e0140e4840c2c01480c010003100095030070203414108200350f01c200c070b03005250188509140ea8105540703c1c0300034012036116080345045032413020410010320400d00011484002c0500c403c000e590307541c103075103903003d4800c407511584d540607403190030700505810302d0300c3d14507602c6c1c0801c000030003600398000c60080c0203100803230340c0740501d07400c4040c1d403807004a03801000001e40703800001248103060520052010100c08160 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 235146942 1250 235145692 235145719
    0xf0a030e0a140109020f0306091207051c1d0d08041503020c060a020a300c03090516140a03020d080f0706020c0a020906040c0206060906030c0d0501050711030a020703060506 76
    0x50036004001c00c8402c01c0c1d5442115104503c3e20281015000c030095001d05118079040e12056280ea2128010f054811800254041040010b0140072120040c58180030340d4a40300380c0c40144660f41c0f0680220b540c01032050440c08500e02140c01031340d02507102445500d003d040103000841c070031005204038245a000e00c19025589805d01540e4411650300c0b40060715091101d00081070403d503c8000180360b5000d8946000300c544030317584952003e0019101191409500c030003240104545034002d8094003400f0242400780019810340001c541e0747c640e00c02c520503601c004100001103148402540060800303880c00000e205c0001800d40c1130b00510b1a6410000c0540b10802a030348211050f0010350404141201103107000308a40c0d40004003510108045c50900002075030f1800080e2802e44208884000500e80e950200040048000050300c9407a0044081c074100b0701901060301c3e03000105250003c1850041000030940d607230f02c0007a41c000c1070f245242da01c0e0880209805480140c000c8424840070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 235148192 1250 235146942 235146953
    0x90105090627120c070509040305032410200106060c120e0d1b0e0903070201180b0f19020c060a0c150207030c060f0213050910090513050c060f0a030e0a 67
    0x41c1c044043c50310003598440503031030307810709240ea19040184950446014040420303805820f4a5102c040b00000c0c0742e8144614046031406000011680d92100c0c9040c030407940319612034240b000c03102c94441028801c559101d845400e0384c6140c068800043d80042e004404a03404501100c03203490b4a081408207100c2c8140031610510208002b900c0280012803034040c1040303000e0a0100800300108844054141b070b5030a191a07204068010741001566040e8008980011851000405040802c00e507100c084207080d0456800104400a0130250320741800c80d09030020500120540300104003600e080030200c4265140c440440c000d542d03680c190f4030145803c1ca050300c01070a9017802a199484d16000703901c0c00c1310580b558505e4010340203006001d81082c66410f054182c082e10002c40e01406030355103071143da088004507540140d21880c03e00041c0320320545600b52960001e0b001d1802d81b444410508107000c5140315940000300d000504125600d51680321ba03200b036158804600c00d4610401c80c540b1035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 235149442 1250 235148192 235148203
    0x9110909030a0e06090913020406090f0902040b060a05030712060312080609100b030109020702010c05061302190305060109021c09080d0e0106030206070b19060308070b090105090627 80
    0x11000d440d88001150641039410001440c801001159079030f2408035003d010641002c0c019004881c2032a08000d000115035036500f0220181241080410401110a031002c018206d11601a03008514040c1c20a20700d0410340100c1e01466044e8840c0c610b5501c0345902200c41d111a421000c1120f552982d000c4002003d008400c088200181c1e540300e1142010b03030810180e20320103003501240d1320340341004001030a42c0005880c11581c00c10700040c0c88132490b000503241031840d000d004025000d42030821504480e134041c010107103402614540c0c9c119110b500107038048529808080c0040e40003400400208281da0000c1c01100001c00c2c072051080ba885e82200240e602c0180c0c101e5011001003a41141c08260b03100304401c0c0300310040240050380c5150041408d80c45503080c058004103009000910382c0140300c00a440c4110049010018140c1e00d04011030280c215076011140d80300d001010070201e0405026080c02592144080c01c03082e00d6608a699115003242101d0f03908a0980c1113074401500b09015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 235150692 1250 235149442 235149451
    0x201020706061502120c12030a05041a070206010e10050603070e0108060109050607080d0e0303010807030303050c3a020c010608010e0703032a020d1101020d030c02030706091109 78
    0x160321035446160050070307980c603904021241964085500b40840d40014150013070b8004000f4240d0300c101a1180328188400312040710400c3c24000103100041885030300ca58400d902414440035031440c80480640d09010690b03411005078086001448052070000140c4c0e0441c4480c040494075a5403440894841d0304100c82d0000441e10542e4240c40740d58110a2039a4081c80900c1c01c16156410700d00060300901070780001070a04080810080c0070301d07503980c3c420980b000c44503045980340c2d0380d9203000b244d07220b8480c0000c0740040e080002041d10728501d80d040d68031082119084256200300b00034005c40d80c07402d0204a0070842203d900040b40c09010788000c2040040e100008206242030495050075101210030307003032407a40118000c03c0807da2010381e038072105180c10805862030201001c404004840b6000180d80000281102c2d01013215450200050041c00c4c2c09640100191590560460350140b40c1c21001da0070400503100020940d901000c02c080c41015400c800210900c042107038a102201c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 235151942 1250 235150692 235150697
    0x9040b07030506030303091213080f0303010303020c061c0903030f2c2e0906050f010608060a06020d0e0d06050f04150e07060e0d020907032003010b030c090d0c06 71
    0x340005958140100341d44400140c0c025442e60400aa1840d60b841b1071651540607801c0200e1500d00c0d440702e2255210003026003004894988070141c400544135030081c4822000b512a200318041c81e41000015901248100e060308c400310301c3e8031b1403040041c6c07015000c1242015a14150485641868031400540c42000d0010308072501d5107400100804900400c190b500d6800300d030025040c000280341e102009079040701d040071180100d124070b01c00382c243c0060042c20242040100b0101d1481d00e00041c4c1205c4182d82d91554586a09091100a0b07105009000050700014442c1107520b002d0340a10380c08060140103800304c0301e05500d03000211401138a0607420194007030240800e05c102e14114000c0d81c140500201b0a250100076200d6494201d44200382c02d0203018400c5a83c030740e64002c0c401c1e0f81c1340e4003e41031220904d0070300f4000700100042007a8a0325000075905403074030070305c3c1c42c81564140c1d840c2000c00c40c51502c2d502c9610015170083e44186901c240d000d1050307400641c4001c1040000e02454 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 235153192 1250 235151942 235151963
    0x2040f0b0a0920072607050604030e090a0b0a05040b1306031104050601090f1e0e0a09030f03110702040e0703020a03050318090402030c12030d0e1c0206040b240904 72
    0x268541c5101400281c0c0c0804001c0d081c00074402003842034001c01740300d18000d1101c0c1111100c11a89000e280140341001d81140207003810042816004291842e91034000c0b160302a40303590b9038020130221241b5941040e0055140b400601050420307511100940d240207119083c58540300c0100400d4840e95002224500d078408165003050605002e83c607001442400c046d0100c5017000810041e2091a00ca070798007072101c400380241c00808040b00700021b0715148900000d1841c0c40031250340545a00101140010b0404c001d80407628401c0c0305404401c000c450400d89003450a0702088045c1942c06000c5103940600c0c0d0340040142d41c0c11307002200440c801c002031525100c0e0841c0745101c220054001c14003405881e010000183e401280704400f815040f01d09040810912141a2560003034102d16403c89150182034001d0002c00100141080e40d000c1455541d0b1300800c80482e1680303401d0760006e1010400c140415240c48000c41014540b078034140b000240c40c0da1410018581c3c85050b181568180c120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 235154442 1250 235153192 235153211
    0x3070302031c060e071b0f20060a050f03040602120f07110a020a030206071b060908010509190201050f090901060e04050717070f02190b1008160302040f0b0a09 70
    0x38494019042c009604040080ca0701d0105210100000140402d080016000c986805540307005c1d056180c01d6081140e0b01c0c1c01c2001e0385003101e0750107404000d100300c07210800b084e0005490700c00c00311521242950781d4039042a81045104826405c082c00c00c54046400b440014018090340d400140702d20300301d40c803c0016090208020f0856103c2040499031500400c240b00c0140e111941000126039040e00c2207585c640c040d050940505800e1501c044400c0ca240300c001032403941c400c6280b01690711413002000a5100c10342c205030f0b19010b02c1c02c1c040e08842c0c0c03541340d00050341c001e20140040400d40700303506240030301500000e80640c000740c000001040c006141c1580c81d0400d441115444043c9052114185602401050994000600350010084100300300c0781d44c4c074800c0c0021602e44841030300355900b46083d49028910003600f119031000225141100250049000030307041c1c60038600c9180752010a00396000c4c8006814910030350000303180c487c103501e20b040d218006108010150078100056030801c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 235155692 1250 235154442 235154467
    0x702040f0c025a070b0f09040902100e030c01020703020f220507030f06050d0b0105060c0106033206010b0d0c050c0a06061401090f0b0d0e0f0a050606060304050d120209030307030203 80
    0x140d102005401d90054400b41700c3c2d2483c290480310750540e441903503601d610312600060064001e2000c0250071844c3d60b01e401c4821500060f0a1000d0321007102500d182c003285d07400499039101d4a00c806503001e02c2000c100d0010707080013040301080341404a00510840c49012101003902c030165426000603a40303c0001003503200920505010782002c580c0c01d02c000f035032500c0318480d254042c0a0700348a101c000a03000c04000f001d40c040d4000395071110048440007040c0030244c1140541c00e9151101040d65803e1003880b61b00402e0003410380305608845814480100348100041c100c4c2250340c0d06100b020440a8100c900800202d02600c2c420140415542d0424800d400c4400120000905002202c0c01c20302070b400d80d1400d20b80541d401c3c0700740d2581344c1d581c6280510242c23071540559074680c0943c0300c041d4462640499009000c0e4020f008992203a201c41c424440c20388011940a801e5402801a03944018402c000c9144103280301e030700150410400070006801d55000300e01c200d0160380005600d40f071051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 235156942 1250 235155692 235155853
    0x7021f02191211031e13120b150f0916020d0509100e0a0909081207090e0c03090a0506090106030c0e04020f121f020702040f0c02 57
    0x14a100e0490944207000d90320030044545104201060100c0d868000e0b442c5034080080c0c4510092114988010b1202d10802d514181c0c00b083c1801c820300320800e000b00e8101c007558103410a06900030203034083c4c1d9035002c0c0030f4410011500101e43c1d00007201240d013100c1c0c0d03880c0c4103154010584032a4920410b00147c03806403030319151001280c14050b0502c41855281c1c1c0f0b107001004115058200440101c100c400041c030110303d42d80140c46107a2500100301d06100c4098017802c0042514402c80610b500d4510050b54900170611507c4003a54101001841d00a0b0f143d0196030058040320855111000b19652503040800484015189a5554500300705200301e01e803800004084900b08030081e41000c3d00490b0814900b810014001c0c1d4007485282c22041e41001622406007220300c115000000080d9100003039840301c40203034400c0d0304140c40596114403030701c00c901c0b054403d90010444500461000b03000201410b1800c2d0700c120709065000c44503e4a03002c0325070480544407000740052680342e126103c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 235158192 1250 235156942 235156963
    0xf0219060f0e0a05010e1f0203090a080a0c032409060c02010c0306050307090509030c07120c0602011503140a0501090c030606080715050d1b110c0121020306010507021f02 75
    0xc180aa090345081c0c403880203030f005440b000c2c68034203525183c5501260340343d400c00e00b000f004c004038903c7d200440c542c04030260010440440f4072048150f9039040c0b487e90b52861903005010380054480400000d00b180c140080e50118490010706080f034070001e05411900310860075201203484a0181c5111507084c0308010500e145400c1c2042054108808265110900c4c040c0d120342550340c10104103025410800e5900814000048a50303041d101c544a582020ba0f0220071600010f0b5428042619070040c0a200c0d11104031051200c2600c5c60b41c2c0341d448512400b0059100540925888040452000e000b0a01da113402549000b078094514503040301164080c1c2d0003841c1a0300318503010b0051010181381090781b907846103802e5440d8400707c111040201350050440e1008803c0d0070700d419182c2e420a070a0142e60b0300d480c040e6082c0301552001998507080d41c1c655040d81c8802003a030001e00c1e240d240d01a41d040070061522508001596010501c0c01041a0b203800d440e8500b0000204420742c1084142810b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 235159442 1250 235158192 235158197
    0x9150603080f0304030905150a0f031812120204031a07051c0515180403030b06091305040609080c151e040b040512040b091504050a050d0f0219060f 65
    0x56140da10380034054000c00e000a04580c0000003c1400e2611a009080280c84e008003a12071304140d030400c02c8440d50290012001040c001710003d00c00600070300c80c4a03c840845880841580e403565108100c034601c1d0300039001440400d0300c004a28131414400380c0701951140c28070341401c800702c0221102c141f80081a05080010400003550080c102035425a012808820b005ca115280d072182e961400c1e2240c40f001d070300142100030b0480005030a0381e00078045c50203038408000d42410f10b01800203520459001e582c218990404040b6a0300090340b04c03d074003d00601c00025a80610b030746145941c0c1c003800c5401c0c080c7c0d01c03032160384041007045401c454001c1d07885582c0010503030b0010107040b644a001000501000c0d180d60002d424040e09110341c0d5182a610103001d646c0f00e44072000380d030b61900400f0440b4081c1460007142910048810700701c80a8440c0203040c823184504e003600f04816003900200890701c129000800c200181c0700c1c460214500a003030202106001d00780f0800821410324031059008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 235160692 1250 235159442 235159451
    0x30302010b12070b0d1823010504020105041a040801060801020c070b030f0f151005210c250c1508070e0a030305030c0f160b0f041208070e1002010915 66
    0x22440c0003c0000c11114042c000b035445180f0b01000c2c200a006008170000c0d0030340c8804113541040030040030ba461003004e0b0000400c00b249014140d500b00c400c200c60003804a0b000f044280100115011400300c41e81181500c58689911075210b2400c0d52a80e51051249a4001c00c00349180f20051040c0300c040c20019050b14214a400001c410038520086c0c03400e0004071510000c07420850380c011000001e100040c200d030745d05a8100314000d1103a446100c0301c042c4150f84040b42104078034880c034254020400703030120b1414505185d55600301e400e40910121242074180100e100090300040c01e940041c030b05948000c0202c4a602000340814a000b0000f00c1040b0501242d18216501c480000003a01c1d018a4065280e41c1c44100003500c0e48210422803141c01000719580031800c1c2000400709541c2d00c02e0941421070388a0500940d00c411082c0c1d030051680482221042055108426540d44032441d440c115960681c1c060206281003210410040141d459102040a11242042810740304401500400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 235161942 1250 235160692 235160719
    0x4170c060a0b0d1b0f050402070b19140a020703090501110312040201090b0705070302030f01151202030717010b01140c0318040b0604060c061b0906050a021e010204030302010b 77
    0x140c45410040509502603555640304500c2d40301c51050803000c80d40070001c42095030041d411070f52240803a2060115018056802180c90705060080e83c0710164000c41d00d40751500d440c44012a00c4504200c82007400f41d88040d0544900d08061913a8056040d00c1801070795840c080c10010002c040680169060046041000f4010030002017161801da06a010320350181c2c459100495054095074001c42c90040b01080720424004042022070442e4800c03000c44100030100c0945500340c0d112030889030405220303c81c1c100020303040c400100c40d42500c0181030700d01d4103451f0308900007420b91601440c001c1c2e0703544800c42401541c0201c511b100079422201c0c2a0b05003600603110369500c0c400c104a001c420300295150100503100c0390030500304a40010041c40e21241c61700401051000902c0040d140141803220b0303a0b4900500300d803522403030005d641e02d006030309081c9002641d042d80060f408a046104003040c00242ea41c5110030320340010030280025985038618140282034504810b0400c2c403460b000030780f15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 235163192 1250 235161942 235161967
    0xc030708130f151410241e020304080610080d09050303031602100e0d14070b06040504031b03030c09060201020f04090e07030f15060b0315061c0e060417 67
    0xa090590201e043e50900e400c56854401402040c0c01070943d1041680610909041340210303801038440b07038007086c01000c0d40c4810700da41c0d2041894001001c500940b0a11b01d2200d00f01c411010000c95a00460346010342e0323007646a14100044509002803800041c040c00100700601c10540318108500d000f0301e455041c52b00007612440003401e501a007a80050a0380d02846c028800f0136020050f1960400001402040c0303d03031500b102c9072410700010782a1030020021002ca005650410b0b8002803080b00554541c1c1c2800000c020107402582400045003003429654041094807000500c2503401241d28200003401605001e05030704450290790041c01030030504150030081d14220b07410388134045000c114180105003410110741002c2c0c0100c81161019007401810382c462081e000801c1d034204803165942e03840c03030b045010503201c26100040d00b5000c1c10305c0746040405085036819944411941081009140045650801c0500c2654200204010070300602400c00b52001804109403403038041e50304a403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 235164442 1250 235163192 235163213
    0x2915060a21060b0318070608010819170c0a0308060d0b041106130f240503070807050c0f010e0111070203060127060605191d270c03070813 61
    0x11002419001d41d000645245103030012402012040e0103183d40f400c1c01c090010038103031030700440c85040c40744240000324948215000c2d4101c030081c5e40039081e02e9001d030480b0710010300e2800d404d4580d00d83c0c01209815000200b001010390301e245a00401440350149005481510000c05880c410103640e4031040c0401c0304105195841540090781c0c1c407004c2d4540c0c0004855000d054000000030031842030104804540d60300341d0003a10f22500e048040074000d8604909205a4001c000c2c000400600102d00ca8a0003a038085400031103c0c1040d81c01d1000340030740c0c82e10388031001480b81d203281c0d1a0014071401403003e101e00d0b00c08200301002c4910b0310003903802082e983c01041c4500e0103600300c048060340c903946080c5045170f4080709090301445141d503103200044ca076401525440b2007810081000700c60850107030102a00e204880100d45400d0401241040f4401080007ca080c5d101e00c0300c0d007000403051008111074410241403510540387d08008070010551a001005c070080b03016161541408501c0c10b41c50b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 235165692 1250 235164442 235164467
    0xb0a0512060103200d06080a0b01062307060b012136020d1406160e031605060f0409090c060809071214190c1703090f0d2915060a 57
    0x150f4517942d0074500055401462690301c191442d000c0d00d01c2c0c801c100506044c40d14122071441c0e4446000310140c20301008040701411031655940401c20595000403c0c03a0040b01040b03005042c1800c0303d10316052072114031a05d403940182d030565540c07030f20f50443c4030b0102255600c04007114001e042503e5088a604202c004110181c89411880d41b41400c101502507a882d41e0145107090b90070609040d41040341e28404040000d0201b48100400344c0a418001407501e50312110540d079100307042c60401408003aa0040300400041d8104220124240072a0300510098138403d40440c070740c2500d002030041402c03c02800c803c00d60f0300100350400c41c828028200246258010714681403040403044818600200081d40c190440004007800f01402003000740f50f4215120400080c0c001144130380c40355124400c0600e078a9005118003184195401d160303103108801c43c42411110102aa401d000d4003130340600d180c04420100098040003214150708034120902142510034a00300a4840006801d003054101d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 235166942 1250 235165692 235165751
    0xe07080709050c07060603050a29040b0c0f070b091c0c03031a0405040b070f0201061a03040201030905030c010b030c0405060d0b22050a020a120302120a05040b0a0512060103 76
    0x881c0f11441d58000315100d00b540b00204020340d41c2d40703190130b03030b2100b1a9203070541d8414a000d0418040c0000100c900c01c25118641d03c02d0010fa651f5900c45004003006012460781620074440002d855030b0b107a00604246001d400c041c0382525204185504d019403400145030a540416602c00fa42a0444001032110750b040c200812404140d4000d291921802d80c43c00d54000e040c03a043c00203104004200e03030300a201640e180795412146840582c2a9011407151402c10b00074141c40d400700380110350103150010302c14500856090001e89506285802c03c1031101c020f655100001480740c03604001e0203032095019075052160b441c00d440080c001d11103c2c00050880507520340021a100c80252100c500303c1c580300d816110300105800c055945201180c0124014011104080b480b06c401e24213800c0304950641c004d102c402000c03000b600c4a40c22081100081c0a401d010205144200c1c1e0003400c880d14081c1d035160b45881c00c000c02c4100c0a4800b50201c3c0c10705192002c4440d070001034682d40c40115080c0c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 235168192 1250 235166942 235166951
    0x50424090513060819050717011e0b0406060e03030702040902040f0e071401090e010e04050f060109020909010f05061b0304030c06082703090d0302030405100c02090a0c020c0108040f0c03050304090e07080709 91
    0x400d44601424080c0d55460032820ac804100700c2d050450741c04820b40500c02e460400402e5225501912400d4625080c260b1550007401058010f24094010305e425920141c80071540c1c5201b0084001a00c0c2c0d00d40a040e5981c02c003150910400300d40d02440c030030028003481e00d03003511840c0051340e0f01858410300540e144011900005001d2001c00c0181c84408505a0100d075030039a51021040000d41000c1c000300c2c400c06a030300000459414003400c4a0984000601c05460020001400400c0c21400c1c1d002d110f60740400d01c40080450f100d81200302c01002651900d507564904004500e41c0c0525281d82c0c01c000a59a698070701032000000241c0b00090003c0d00c044c81c04c14000d080603880d50080354011a84040f4526481e00440d902c0902c41c4e001a02c2a10300d039107151240d2001d80159010300c00700c3d40044c3d03c52080c1c000198072035000a5000360050744446003504607501e44101c2c41904e1380003a1140d60000900304141b40d180d11407903440490310b40c05802014200181241c5030b06561042c1d11707100780c8a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 235169442 1250 235168192 235168229
    0xc0c090b1f0f111504050c01031d0309042309010203070e010c030c2301050a060303030e0d020a0b0a02040314010510080f03041206140a0c09060504240905130608190507 74
    0x812164811030100364681a080c5000d21b00b05c2d9440968a280781d00203814040656184903080549000540b008005181000814403e2100410b01100000d01034821040c40b80000c54a40c041d882c0a245c03100e001603a2031130403210191501c122504454100243c80041c98080f0b0307480411504110703440003042840911221054054014200504101c1d519150600c0780d4203445500590450784030ba01c5c188024008001e4094542c140c540210001d41c20210780040012243c200503a170001c00c01c40e0050500c0c0d16904d414a019161992a42e401d0b03550f44107200d003000c15000220001c120000040c01648006501143c41e4000e51040b007200d14140c40300daa08010780d42d00400f83d2025a081351150a140110415020b001c80fa0520400b2171004040450820f00c03400c11503003916290000503441041040c0303648164440c2d1b034641d800b0440f03104008101996510000787c0112044107022032034a041030303011405c002c43c5c0d0b4103e5092030081503942000400108503a01140c0000c618040c00840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 235170692 1250 235169442 235169477
    0x5070e130e120a030e0607180b03060121020307110606030703030c0f0218040614010e0112020414070e0301140f0612070b210a0504170a0c0c090b1f0f 66
    0x280d02c0300103002510702140d110f040d241d05500c0324070002017100c22205142c903080401d4400303003d580f0303040e840c180c2002424481700c90464015500314030189050180c0c00085a442d0034103020600035808416000014400392a0740103280f03840380840003002c0d003214103151002940c1c6489600c001802e2100e110058024402c000c45000642c0da0082d100e0540503615040c60030702080d00f250300b210064500090302d00081405445181640c1c0d140340d0050080e42400303080400700c803170008100da00c980c4501aa0301d11083d50b56456001c0c103040d485420829903008201403c0d07441c800b4490180f00d4141d41003007040d111140b40b2903003000050302c07803a000604004230503007808207035085070520590015035101d8042d4040904901036810b48004a01c3d91280c28000c1c00f910740c01d40d005005550102d080300e0710001104000c2c054030700780d1b0074400500b10860b541c241400b801c59000c41c440c5955402c0000180c100106465418141c101185000d941caa000242005400e0183c0c0001c10803000c001000290 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 235171942 1250 235170692 235170703
    0x606040b09240d120f02010b0a0608090f0d08011401030203060d0803090f01020c101b08040210170408070218011a03060d05012c030a0c08030c04030c170105070e130e 73
    0x4102030040040c515013414180003100103019060006000281110301e214410703c11019040700042492000f1880c203101140d08810141c811011801082c0c0912101c41e01003041000c4200140c941000d65858925001810410101d15905250040042040039944c0180130000c5607400f4500c10388a03100c014116140070030f00051640380d5071000480e80c1e9070080010f2aa02003000c0700d40e052260700040030950015400b9407410401117083d140100b00185031032200190300000d140f400e2601e038061240c0c0551a0802a10242c514100010b405804d50500d5011860401c03c2c0c00007242040d4944038503021680c6108030b444500c1d00d00440405c40076554000c0b18200660803100900c10140c3d0f0001148080317141580806181100c03804d0f000420700040140d86983e2a217885880200b00d86444501e540d900c02007c0e048018010040400028004860703480502041d0320038007503e65403c6000c50840303001902c07000501404401002c2c80b40c0e0750869100b802046002e01094240c00010b4062606 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 235173192 1250 235171942 235172011
    0x504090b1b09061c1109060a030c030b030a0308010f060e060d0c1407060218030705062205210706050f070f020a030213090201090905151203090a14030606040b09 71
    0x52880e281c4d400302000da003e0707000d6240b04011010360007031042c0d518800c0c0c040c03041d007000b018451086104d010303a10901589030241404244c0c10250000070341004030004048010034543c400501c401041031600c000175214a0910314062440d132400911a8025210070081181d15503407813211851103100340500010000310300039141c003000d1900d44080e4000003094100244d07030b02031030501440c7c000b80714021200054840ba14095180302181c0d00f1190503040e001c01d0450140740007440d6110466014981d40010103082403920581e21414101546c0e9441241084410300902039131002420480d21911b903c0001c030324810100c0d102048030704503107a20280d4021450a203041200311240c2052004a1007681c0702c01e40e0300d48404440b4111442511501113880c04280000164200003404400d25440702080303905158192002400f052a590081460745845445169143c1010800c187d00198120f03024042031a081d000304200d0000240900c102c046101400e240d000c483c9030308109070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 235174442 1250 235173192 235173199
    0x190b0c040801140403020f0105150d020420090a12080316030e01060303020c010e190e06130911180601080a0b040b06070809030d140403080901110d0215010504090b1b09 74
    0xd512400c1180383d122070032182980913001e512141d0301e41c9401882042c4c820101404040e070126121403d00180013000c0c0380403030b0416500c13076603007000c1d4034084140d0714420080f0390403039520032924052220441c0c03d5440001100143c10306c08000541d5001901d40c0300d03010b071000a80300c5d5000e02c8120003801e090704001400354640322011013419404201c0181d0042c080e210040d0721a408001d000c100315101c1a210f0032449144002c1c88011429a2009e4112030000e0011030032040e80da00d01d0088901e02e0104031109074079a546800c96052100840d03802d0901d0314400c3c2c0c064941840042c1c140c080040107484884d640d4138201d9080d40e9660710039081040301602c610b0311794a96291061140c0d000d007004a00c20700c9445410038080f0701c10f40c0d0904403c9481c00945080c149103650b02c001503000000c1e07803130610503030142d0700752004001c100e03071440c10b40254010a10944440c10705400c13014180c20450050b0304101d0004007244440d401e6942182072660784203401c09519498458500400701220790 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 235175692 1250 235174442 235174451
    0x3020d1b0e01031104050d0f05010204030206040608100501030e06150312040f03050c060406020a08090406090f0212090c1e0f06030106022104050d060f09060c0917190b0c040801 78
    0xc200d03030000c03824035110700c01c3e2020056203400c1840800640124031070542c1c4003002d9014200003c2c10001c03900c084074400c0c000941003039200d03800503c0c80d42113a0090740c0001d07200010420310400000e5084010802820100400300c82c40006c503458400061508400f801c000c1c00e1010991010071050f40400010b90704191a06d0b199012000450f2a92100303450138072803442810101d19000d0204c5048450035001042c0c4600d1540d80c40c0150b801c0543c21f10f40c0300b592108006100d01d2203004440b150b5820000c0143e4610b4802d130980700140c8050481c0510351b204825014481c1c0b03030003c00c4170b0781c02e1080b0006c0301e84e841c1d450009001124040c46180d000304020000082c007130340016640c10f41c80702c101820480d00382d41c003400c01e441e4010791050396403103a600c0710840042840c59012508856040001064404054484009035584951a90001401c00380c0c200221100c6001e4400700c1c89800c1c026100b82d620042e4040d8841195040c00340014884070702041441e5080d1048600a1450350000d01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 235176942 1250 235175692 235175741
    0x61308101d0607020705090c0c2b090302011b050309180f01060f0503040305310f050906030d030e0f010e0a03080108030307080f090c1815031504020103020d 69
    0x4028141c142050750303150700341c280c00d0840c0d4240030400c80e1190344168000c049051400040108407480a410041e03010002c1080800d02401880640200190304d50720840d00f12250351800103c82d241d0242008009035040c0500c01030303031b1224050700c1c07000700300c030500c4054501cad030424901b0b500c02c0c9000329038030401611621082d44110240b640c8913800104100c113960780ea80324240e0302c82100350490000603a08100140010780603030082c0031102c0c50b460452480100d108418030014425070017a030b8044041b407402300840d046160409000e00400e98908000781000d901103580c408141001c04180340d29500044500c180801c003219010501c10002d01030445c4809041e5114241844141c0000c0c513954004119650700104480c0981d4955403140e0b91580e0f10048508030314006040b41c0003d0003100603607012a5192105a90030000b860746030080b50811002181402e061208128040d0f000003240100300e046019425501c980c081c00c016aa850600c0100f04c01000c04c42500c14609040c183c070340c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 235178192 1250 235176942 235176973
    0x10306080109150612050607350114010e180a1509050a050105101709030d2d060b03010b0f040509070c022107060c050321091911061308 60
    0x350101d10340c010b4100541500e03050000c2481c17103400d50260203a07011002281141e03101c0c4444072050b0301000c2829592900d4003081001c4804540c03500001a440c202c01484101c80c1107110481c00030342420206842c000740d030b0100700d60b1948400d4900780a00150b0010780a00752940080100340b9120003484009615028198010141901c12110443c81e00d130001c1134030b003002d8038004c2e00001c00b503d403040040c03e2100c0c201340001d002800318210303000500000522160b103000c0c00000d030150514902e10b4501310450445629070324407004804500700107082010688000c1200d054a40744001d66907148191208132000340300e5076210030703040f1007001c0400c00101d60004100c1000ea2003110200b101300007081c410040c2c0740c140c0d50451a160070124017084540d020340540105a0311036010b072030501e50301c1244004c03202031621340c0340903111502003040407052050101201c20840c1c10301c071b4140f007049519000c8080d60b150482e18024407001803645c41422403c5540401015000200e030711041c1408200d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 235179442 1250 235178192 235178213
    0x405040503250c0603090f0206070213020307050c1c0801031502090a031a1503030d0f150f060810030512180901030309060905061216050c0d0c021203090d02010e010306080109 77
    0x2030f6545240c00502181d0750703110b409003005003038001203010010469502001660f03400000100c0e03100e02e41c503404100a48050011f075104e01a076841d000e44078030b47c1c100c0302802d0049045a0350b0821880b8003600113807603004211030b41581e40101050b1451040d0b18403000003032050f11380701507001c3e1004d8400001c01506840c1c0c2280409918481c00403170f120218032260014040c04a194550814440500c4140d459404003508000c00080843d102050814580f282c482e01d421440c0c060710f41400c10b000207030f0070881640d000450b1010111025140d40c48403522140554180d104400c1c000455010340b0703840c10030070582650300900140d0382e540d480c940504080da080c4a900f002c150308030301c0000c6134580b03002a105d6200c80003000c501181c0d100400e0107101c1d00c00d25080024010b040c081c1d08031079001048039501302441c40e142e0007050703043d6004018102082e0704031031629500820000e455900c03001f95040c0c0711582801c29400c2d0744031000050300508081c0d001643c15602e0450001c041c406c0001c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 235180692 1250 235179442 235179517
    0xb030726090610090207032109170703140a08010e0601110610050111010b030309090c1b0a02090a09021f1101020c0604060b090c0f0f0403081b0d0216050405040503 72
    0x80d90315134502034001603021302a4042c003c650f405040d07545d0350b04004171001081c001102d001036500401c0d5100d22449400e640c424040d0303880440e07580304141e003040044410154088a140c1810b003400e40040c03000c1014020701e1034500051001c65441c1c1d016018404d1450000b006a400619207042c50303000030441485158009a0b10b210700c5424001c06114903da03d040140c0594900380743c0e08103000c5481c4010f0b0414030501420440442403d05040e44401c0c1641040040c0094000c0c40c0100040ca21010b403074170b0102890301200d000181d451120009440080154841010b070209009031f5811030117806000d8954000910b84004000100c0ca0520842c0305160070440014001c0038803000583c1141c42e02040c6800b0042c030800386568102806803521110202c5180546039a1040110b1300004c255070701030300c2c4002c8520a1040300740101c100d404141e100810001105076030b20410381040744100c60042d583c5401080911a0a20403980314510100000c11089011101d0702a0340c6807400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 235181942 1250 235180692 235180711
    0xb0a0207020310050f0a05150d1b03020d12022401170a0b070e280b16080f0a030e0c091503010e0f0601030b011706060618090103030509040c090b0307260906 69
    0x100000c43d45003550440900d0b940d400342c012810400c0c6642c5d2803021881c2509032b10a41d03c88424000010b9a074481401942441600005002620140d011340340954200342800c542d042c0040e49481c3c0389242403054115160108001081d41005011600b05041c0b20005410003010500b0018030301e0700440b03d90043c080545107401414011b0300c5d0310340840c54160741585803114180042115421070030207440e44c1036008071034047d000352656a000b041d6022450040c00b0040214281e03100e582c040c440c140c510b000d101c001d8401c10750a00d00003400e902005155030600044a000300b11310b601c00351f000b54610f032610320840707140081c9002001d6840c44248812200340d6220790000c40c85403a2001a4411994240014010b989940e01042500c1e00300070108c0c020700c145003880212668951151038000d41c002d0f2141076488584009100030b40e114800c1940030702ca0804000c010045c82d11040f03030347c00a07141c94154000e240030150240310000c8008104031488004c010b02c4074103000441c40500070362142 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 235183192 1250 235181942 235181951
    0x3180d0606090c02120c060412120f050609180a0303051314010902030c0a15080a11130801240b070c0f03060f0f050118050415090305070515040b0a0207020310050f0a 73
    0x240041403910540f41ca1250341c0d0800c00209000900b24a00c590b00300800c2c2c10150b4ac0840180c841e0404c03100c0f000c43e2403c40030348881c10f0041030b0801e001d00d6a008041c0c1000b100180054820301540e4141d40500242019a260001499151084481d410b4103911001c4541020000c1e50f40c28085c0c01c50740e4090380300740290807101c1c556150251480c0101d0321032900b94004404019826204140c0044c0060302864642020020301a1980001c044042a00f42010050b5003030100c11821250061001501c0e004032039003d11195803601d000d002114074a20301241d451507103140c0400720b8a20740d0b0002000d18600790b004401c010391500301c4800e400c03443c4010031290004034040700603581c00380315038003680c0000c00400c40c000d44540c202644c850b00420b803082c14001e02800071002c4075501a020780000e1001310ba100100482408408440c1224054401c01ea0410707451706009050098014038840c2c0d40015402d003152405d00610100c0030304008204450306c2d00e040807080d480c108440b552082c0d03240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 235184442 1250 235183192 235183213
    0x2211914010b0d1a0603011103040302150106051e0904060e0403020d0e030304050d06091a010b0d06090b0105040501051303020d0f0b070c0803060f030a0203030d0204060815010203180d0606090c02 86
    0x300100f450110f801c00200d071600a8090310307802c1840341c040e05042e0036540b0350201c2d042c010082c1d001540200e00c61340c0201120702e074106942c40ca03071506800000070001c08004940c41a0007801003050240c007080742e0135a840100e5000140200324542c0040e0107111103030100824180c000c04c00303027071346096a2503445240d105041050303140c3c82913000d12035102443c8c03041c040c040784403640701d100568892154422001403041004550f82c40c26032094001c040f00190f072054981d018094400182a540001e1055400f070000182c480d0003140161410042c010480030b030031030000d20b1400c00460300640100320124540c00c020b46040386018080c1da0b0012040081a10300703200d010030100c0c00790401545802e42c1c40340001c200c0c61506e00b00c86190725224200c540c6025960501c010040100400d8005030b803640781040240140c01e00404400500c00089000742c0703da600442140c000d00c003c9101e00c0382c5a54800700144c40c191502c40040e0141d80b0307000001c58912000d61004a40304810303000c03a40041c00c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 235185692 1250 235184442 235184449
    0x50903060106170a05150406090203090f01090f0b06130c050403020411070308010302221802010813030207090203041e030306090f0c05040905061203070b070906090302211914010b 79
    0x7240c080200b0a01070903c00603080c0d940c00da0202e41c0225050481d0035803c00024001030655650341c02102c50301c1d900000340010280f040000b020b40c03181c078000a1100e6411600c61401c817100e0008060320110b220000070710a81c0d00c0e0700d20b00b02d0407070003a0010030102011000003891a0018001240134514005410802c942d5910a03103180e80d5142d07a0700e0186a00310b500707000450b0102c0f0500c81d0380090b044900d410074420b90180c5104100c84981040c10440386000040660384007800081f11a03505001e1980880c2d400700740300003600c040f0203015960303440302e02d01100604a402c405070102080007240104265141e040314040341e8035110244590714501d41c800c0101c44050160101140d42080104140030341c03500302941c010401414070050101085441c0c1c290380c03200c142110300034100c80820041c1d9070030100101c050716840c9440703150b690035640498a40560000540e91074100f5030815406c11008120403824100030000903514420301d032806c0b4080b080340040c00e481c2942001e01a080303904 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 235186942 1250 235185692 235185707
    0x606050a0b04260708010e150604050408070f080d050f041b0b04060c020301021201030c0f1413200a170a050c04060809120301030c0303030c0206190c021c050903060106 74
    0xc910b203d2100070382c48007180d203401140030020000950b00a07a80c000507042030078410703c074001d40510b0107815440944090384514030002001148658500320520000c0745085003901c044c10303402501924841494103204e599805046100d0340b1107070401c000c12006450040307019001b144550500162050000454014024640038580c84803000b4402045403c5c071441d030310b1884500103000145082191010040d244009030002e513154500202c00308128510f40e412403004007a044502034a255519000410640c44c01651113040c6d41c40b51103800d4881c3d0b80d00c010204003044005680d60360344a803040502343c400702c460002c41c220206800506a522103004051242c521100e007103141c80e0508000f43c1d69280040c145604a21620070030f55401080c110013107019602403441040450316501d001010b89003050013090454022206001d000c0400e950b000c07540c0000c0382e40c04224071481540c100c4c5004014407440e800c2044c8100c804c904903400c50001e000340c01c42501507442c03c1e078862100f5101d80c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 235188192 1250 235186942 235186949
    0x405010303021f02040b030c040f060c03080711100e0c10090e010519150215010b120114040b040f0203040c0f15081026070f14090601020312040606050a0b04 69
    0x60708280c140b440c0264080f9109074900c078250400600785505c030303540c1c085a41c004860030140741c00f00040c140030a0101140e100c3c010b15551130002d41288240d0380060560f00302420420901005c01c0b04048401810f1021030465808408100f14040c0600402956601e420b0346490060349500740c03204460b48541012030940d102a90119056441c00c1c00b8040608800c0e80800d51850740807001003022650030321420f02c0c00c58158010042c9009164003121a00c00c180d0150420810400420300c100c5a00100a8111141c40840c5549014007102140c040d01008000c1035010b0300d441246e00d5085500c0d4007560046010b550041005508e80c01c1c6464044000d000d80f2241c0b16071819550303031651141d00541d40c403840b20b52100620541c2c90110424107041211035031103181c40303404030300c0c568082004610700804003210124841440d200342c1c00c501c108139490442c0141007100000b00c03543d000304211600c2440440e001410352819007880401014075004803407180302c10074000030f8902caa2500780e4013038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 235189442 1250 235188192 235188197
    0xe010605030a1403130b03090105010e19110c010c11010b03011103150d0f0326010b070303020702030703021507111503060d1112010209012a2306070903110405010303 73
    0x142d00c80d1600e400e0685250903d4149202c1000a602c1c062107980e6005c00902c821194217441c0d00740b0400e650b0960f18142c00c501c880009080400402480041000303518500191002a40c42141500c024103485030f6003817428107609001c02c5113403060740402e4104010144d0341c000c01940300003104040c01d945034031400e48101d40381400440c80403200700584100d90b90004000c03c46442550380e422001c200c0d12002580030503a10545501d565510380044c0000c802d800c061050303990305100e03480f83c00740500b100140030150301061a1046441c00c009207030207150002c145520100e0001401c9065034881101110700c0340071001d0100b220700f00265100b1030820b40599450a5513280c60500018010b5580c05032490b203a41000144961115014205480702a400240e9202640380014040c00300c40602070182c80440d0042c0c0408c0852250181c924550081c102c000790140c03103150645040440d01400308602135a014480102e0300031f580c000c11244101d542c035a8020100e0104001c841003444050b02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 235190692 1250 235189442 235189453
    0xc100b091b0309010e010906020d0b0d080f0c0c0901090618050c1207020118060f1a031c0507080414090618010306021621140a020c011218060f0e01060503 68
    0x44070144409140d200b10100000034240041c040f001e0b00351503250406860043d0b0008008504102500138200d224109680c1c071304030607100c1e0f9204901032240c500c0c410325080002c1480841807400b4092203001c190010050300300d550319000b902d00107015502c11103ca0b4a0042c00401d4094100d00800d44200701200d1024188404601e1741984d41a00510800465585041107000400d2001d00034440768003a510000c2c1401d21800700c00201e44801070f440d1003542e4032081c07800c4140c4d40050003041d21500e5490080610a00d03031030980722401807040040c001600454040707071281600d003070402a010211803101e003a880703400034060200e00402c11480e42c00213640051000c0b07100c07900149400544186841072044503910350052108480341c803c403c140d00c4820b10301800c0c0c0d0241d500c0a6402e4030350b80c490320380740d542d000281d0388010301d2284906201828040c40141c448a9016a0311003540701140509c400d1a4030300b9200401081400c0d8280e41d00d411104072403a00144215029280017400900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 235191942 1250 235190692 235190731
    0x1080d05180d050a030801030210030905030702060a030b0315091203011809030522080105150102060708090705090a0209030f011a090408070f201014030a09080c100b09 74
    0x1035909401d800260080300d0354540c00c00056081010144150095803008010350441c4100600c551508200310100741c20650758030040b880200c22500015411602d0554611102e9801d07400341003440d074031030f6241c02203d0421000209007040c9500c03c01c000c000340c1303c10610441610311240020700511500301d440c164100c5140403154410317240c041c000e0030a681402c4191100c0005d00070040c204083d062841e0404000c620000d021702900040400000903402160800003507407068020b1800707041043c1030000c10460b600a12107100545005400500d03245010002d6a01035030213459403600900c102c119047e5007041c10b105a81310100c403c500c04241010b800104035070510003a0054640550421894000600940040c109a40700f10343d00740f40c002d0f072041d86034001018010310fa4091204104c41c0c0100b80d030f0041421003018090048580c4a44402c024200203082c0c928000742240382c0080c1d680c1f40356030000b4400001c4000b10700140700c1290990140078042c4004c0c1e0700e104000341e0030040d03135 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 235193192 1250 235191942 235191967
    0x30421440703050a0207050405011706010b0a05090d06141816030b0c180301061202090a140a050702191407060903151d011406010e030d0804020f0a0e180601080d05 72
    0xb0301c1340d0305491048546158403000001c0c1251001e03803000030f90210b510710a2503076800c1441554010f00500146904004240402130010f1041c03071559841740020080030020412544d0000300b40e5410406100800d01e840d08240b11401562044068540704401c1604082d1010502d0352007035907440b2003c041141c403039181c1b05001e034100240ba442110710040c24000d007902c0921840c1c004010502c0d00380e5824010b401030102000e00602041800d60405880404520310491210340110038030000081c85d81d124442203040c5207205500c80354035100040c0401c00c4c000903d409201944042e400d41304504c1e5581d2094401cae1860313100003003007241000c41007400358806034008002e0b0600e15026031800e00150580908564411210000030036100381030221559011280c125020f00540c014401200d1902c40600380c0d06004000034032842c40d0004a90413a10342d400404001c04a09466040c103041010b480c13070036086a042440360700d03c00c0b4000015081e10008600c0701200e402d03143e1510303102180c10035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 235194442 1250 235193192 235193197
    0x20f04050a060b130603110301060f0c020a030f0b01030b06060703090510170705040812070b0402130b03031c0b1801030b0a060b1605010e06060303042144070305 71
    0x71041150707076001c00141007203a8070001c002682e05804041d410604214000d8111001514443d100c4d4a092006021b400d402c0b0600742000130b014200780302c031140c45100040308803280c1e4100520400c84010307082c003040004c05d0881d06032403041c11000d5683d901e42040c8000343c05010030190000300a0881000706c0c0c24180e150541510491806452103002c14071801c0c40740c07406031212000918001000c00490005000012009141d820901d2800e5a9616840005600908061b20407080c0700c0104103802ca050b40300c0e00300ba001c09070549849481101d0030414030082224007800803420854020340c42c3c904450515180040d83e400c0e00302c42d0342140c4591182002c000c284c25403e954810021404400340d03000740802c2c0541c2c0095180000007480d025094440e160401c2c1c3c142e03030040c424808250f13404400c0d41e0941d108402c55035981401c0480207240e001008401900c03c410500d40d03100351081003003400c9210130005190415005e5281c600c1810b03440c1804501004510503c00c20b00007030b10a400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 235195692 1250 235194442 235194451
    0x6090105071407051503040b01050f06031501122d0506220216060905150106050313020d060903090e0c0306030705060c1c0e01020f070806160507120302031b0304020f0405 75
    0x449800c1e81d2a000410f41c0301300c112907142005c20010040001b041808400b803405001c080c1c5414070100b81e018040f84590101400c0c0085c4565100000a0785911032192030a803041908400d1289603406c02120018400c1c100f40f04002c800b0215011107071041031b004040c09a8405041b00b00c21056260040311907240315400041881c0d000c0100d00c00d00d41c810f8011810403406800001007250ba10b20f00a4644114400c079500b105101c43e00420900d41c0241c01d0f29800450481c0c8440031045520001e02102640840100300c41c0c5028032100038551b0001c15401a01c0e8100040c000540b101907141050380801c541a95055000b8181404103050100241800c0d81101046840c004030424108450140d0078800d40c0014a00c0c1401c49410341c1e0400002c103040c004032020301411800c1401050701c40e007000b0030031540e0300c140168692410380714004884106401002c0c01c101741c0081c8200401030352058030f10000c0b08400c00e49004068540d032041320702803035008245200d00100c103418030019000c000d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 235196942 1250 235195692 235195733
    0xf07030609020a0b0301030507180b030c040b01050706090b0714040b090103021b010c0f0807090515030601020a12020c1e0f011805100302120108240411040c020109020108060609010507 81
    0x440018004c0445001d9406148510040c2130f5540c18018a02944080b6a42c3c214940d41040d120640d5134034007007103890b0402c40a1310081055400300005965500c00c428000b00ba182ca03140e901018011052003290240740b140d600c40400c00c80240242d1a503010340d0060003a10b140410030b0400940c06a0300900c80011144101996017018419842c21190119120004a00041c40c00700d9030a44c0105156030100490405100a5007442c000c203039101500101d8a081d07a10020100f06c0584c020096695280d9102c00c0b4070f400e402c90700e44025103400c60070502c140200c169400145190003000900700c4042c101500410700e00d0a13040044521004403807120450100e00f00004c5040e44500b4411481128103440250b540c00c0280654400084164410301481d08080c640b200d15902d489001212034079141020700c8203441e00e0070714605955042448130782c464074000340c8400450b01174101e900291b0003626065aa0fa03130704018800c2da40701d88082507000660810034840002d030081c06030850070080c3d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 235198192 1250 235196942 235196959
    0x4180b01140706090515090706050d020d0207050a050d21020304020f06300708130501020c070f06030e0d020607180815040510090b040f110a0609170f0703060902 71
    0x107000300a984426000da94443d00c400b030500c1072090800c070280404000f1110411146000c4010076100c5406000303c2c020040f0000d0700b03180680203038054940c580d511220841d43d622151810301d0391402000c00807981d070b0203441c41b000c600c03c1c042c100080301d00741020300555685110085c0344000f54801441240e004001100f8910fa585031940500b680e505e00041c150152041c486140c0d20496442c17144501e4035140b0001c01128503405203050760480f0391a01c44802010702881d200e0301900510128941030311604d5800111000041c41240031103035039071010418600000c2c41aa102c1300f42d1800d860160380104007147e5114809d540f6007000f48501c041001802d9120360081d4101070001181c0802501060180001c0c403c052101628510343c0403010098241a03960300d400c8000002e1000d480b032400d9230401c0040c011a2030700c16a2550000f00000070341d5459000281581c00d19011392201040113110104811400041d03441e02001c50034020080d451075a07540d000a407115010498001c601c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 235199442 1250 235198192 235198217
    0x70311010c1b140a03050a06090f06020f0301050f040c02070501080901060801021305030c031908030612101b140319060b0403290705120907080a15060b04180b01 71
    0x7141c44403800c081c0c2c061000d40ea0b4602c3c1c41003032160380d000c101c80244600900c01c4c040002802c0012404c9500b5030107480481c0c002d030f2a041c51402404250405002d56000140c0711700d60050000055050325421240320088903005402d110031a0241982d041c00340c4d2000c50288600d602620706a94400340320000030441a03240ea5049099800c1400d01e006a82c07140042030080b45000e00507889150400d030020811003249410310009624108401382000c000000072840f00d4a500007002d80e02e1040030b044aa58942d6139050200802c041c0600e8004180a106c144201d18031444a0b09580c6a4041d80907095441c1c04e0100d00302140c0c08580700140980c0c603840014100003a102410055006454101000341e528212513410701128040f0281c40181f00c04000d41c403a0080140e8542101820002c1d60300e548802d0883c0c0342c50202d4100000b20f116108010040007400c10040030702101003501030150076030b61036902aa030b005501a411072101e8041003061126080c1d400f03c40e42110514080110b00c0740e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 235200692 1250 235199442 235199453
    0x40f0203010b030f1e01020a050d0506040b090115030b03010c0e09060604151e05030621071802071407080a14120304030c031d060409021e0c01020c10020705070311010c 74
    0xd03c09002e0704040c42c0c1c3e0007000c4c2d8171034100c03048502c150020340c504000890000d25a10404034021403080d5503201048243d101c5a1017000301801c090043d00c11961104070607810b00007195840c0c400030341011840305640c10180208080d85032551121018550884104144c0c0c03400100801d4000070107020004515003050414081d04e070240d140c0a2a80003e0344c2c52a0409000c01c54030b00038440c01300248005600c403902c03a440e0320806260003100684a1a24050910701d081e84120321244130480401c510302c070940d00510344d0500ca180110007920b81208502d8071412603104014082c0c0210b0300c03030b0000c1070000b032410080c24181070a48950640c1c4006012441c2c00503a000d40000d41e21024020416030010125120403004040e12070000d0101030004107180300b980100c4403066004034540a90a100c12090409600041e4009031030340c5011828074002d403c1500c031109103100d000c288039424240d034404c441c41c198211000d011820b0541d00d0302e00000b001080150304211189601101144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 235201942 1250 235200692 235200703
    0x1b050106060503091903090302220f0c11010911010302031009090803040605280c0909020301080d08010e24060405060a110c010e010c0b06010306080307060203010503010606110303040f0203010b03 86
    0x651191900da084c10040c143c5080c18280070700308503641000c84500400e030010807401c01c0341c2c0e044131042800c0384845a0207000000301c0a140881505101c80054455541d03004000c0c8124a96103d03030b030305912035a13220300380d03214808040d1045100c02a841d0700e42d44241c00443d44008101c00303034a80700b0b549004140442e1900d10053f1003c0102105100c10080c150043c00d410180c450305034007800b00100840300240758010203031601c01c0d684400070120f60303000310305203001444541c2d001c545039a50340150350340f9030b240169060009480400081118098641a18044c990030328001c101c00001d25410300201d08155842c80c4c1c005400d00001907581d6541c001844680002d2b9280e410140341c00340414038050745006180d0521510201001590b6481300c4c0701101103801212041254a4800050f0000c01058102d800c25000000d502000d00455400940c12660f0a0b80200f180d240e44500403254a106040740340110340080003c80e001c54034603c441954580020000280303080c0c3c100c0002e03d0003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 235203192 1250 235201942 235201949
    0x8070c0303030b0603010e1315060b030610050c07060e0f0405070e120708100f11030106020d0f0806060703080a1d1f15120302070803030a02040503061006050306011b050106 76
    0x495912000d00c201903040c021069046410f580c03803400d6504064001c640785400805500b062000d02e50a0000e00c500d07500799035100840e2003010400d0a81305c800e6101c05601c11101d2500076020240c80e00d2469101e0421201c800f80a4805000540e0409104440c41d500110015510450095009406907500d104450180c1002c0d2030b902100355510b014000e101440006110503500f14031010012981d002c21242d03000c4420392000903400c0200c29540000746a0500411080040030001141c07043d00000c0c20f1740f009600c2e403504024429041c0045540110456100b50011418407050001070f00403081d003600700c50b80e1107021540107170108900150b10201481140941e100351104c07590b80a030030010350300d1100c000b00d090044819801d03407031840078494440c691201805c80b50300418580b00340240800782a844059036603d0a280b40004007035000350007032a03c41c0c01640e01141d505030700d59942900b00c030341540310b150555a4603401035601003c450582d00185002d02803001c000790b020301c1010080d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 235204442 1250 235203192 235203203
    0x60810091109130908030718030c06020c030708060106090308030a0b030610050f010503040f023105040b010608100315020c0307060c030513111507061503030e03010606050f0f070807 80
    0x49a402c80d04111a2449082400100310314045841c00800d1500085991200c460f041410312000620100d80400d241e650014044020403540460070a50204501c01b031400103c0440d20303515210b1010548403c1c081c41200080351640c541013001a0250001d5540030b041f408002900e1044240400c0c00c10f0000c880fa40c0c1028824a014406071034016065800c0400c280703455829450705581e90f03d204644480042d20440c0d5007844014211800703500c16041c4004510380300401010078600001a00b0207840403a07613422002c0002c1112413040514500c6070410340880200f491460b180c001c3c08081c150040c0c2c5505408000d00c1c210218108001e20700c09115a20015001504c240010111500500004004442c3c20031450100c3c40c05042400003903403c4954250301412418104054407802000420040c14201c000c0321001c1c22030ba064049034000c0d02c5c1ca203642c9444104050884256001d40300114000780b00c1d48104d400408054040d40d400803a03c107241c16899182c020f1103411900c82200d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 235205692 1250 235204442 235204447
    0x31806042405161203110a02070512070b04030605090105060d15091e03020a110a05013501080c03070e1306050408071b06030c0306060507030c02040b0402030112050f0a05070608100911 81
    0x501d185d051088010700c07018402c881381003548410000752201c2243c45913034820b07203031a40402690102845150000c2c10000780036580c079580c1c1d00c1c10001410003150840e12a51034107000071081e0404055800784140e214100002225940d89a04020680458142c1e07680e008014010f100b01180300d14100d00c40c0c026002043c089485e86082401210714004440c007031840200100440c0e41c20040010381c0328040304000011000400c0e0001c102c1c13081d89100480703904440f00004d512500428a41601e400c1074050328078a54449100700b0340b46505513400071001c4455042ea00110751998801508140b140501e245061060344406a01441e6107121007004803914000300242c94040c4210f428145260400f03007c6145081e40181040c010580080d050111a49549045680e103502146010400501c115140d5031201c101100110084204480d84c0c400d071101881c8100001070041c2035154890000c204260500008541142020703280300552030300c005010507621030502401034603007501c1d00030b5078 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 235206942 1250 235205692 235205723
    0x3060901140627091906140f0f0c0f07050109030503091b01080c0c010b1002010605010f1701060f021e150105041a01050a1403040503180604240516 65
    0x101101e01c0900b00522801126030705401e40100c1e010320052102d04030a10841558810b040f807401c0039501111500c580d83e80e52462410400a54040d02485501d030310b822005a840d50058000d458042d95001c45403a0010b0028007800b2544004203032025483c0e04143c02e1822950762703e030a60b0810390f022400f040010040280c0484200010045100c032010640340d00b4404030006010350602804032120140700251b10300c90003400b50031002113103c000d40391801d00d958907040207000385035034040ca40c0000c150480400010b4803c0040405901c2c0c1c03d02185c3d83c6900c0c05405032040d49100404000358050b40400303040c0106c100d071884607a6010000902451000400c5107441c012050704400d00c41e030b10301000b400110f070702c465405417101c4080c00e000d40d980780b2502d000e503845007826841414105001040004000000c009000d0750808c002c808502140c03030504102c9103018070701840300001d0f0030031119414004511000d84482e44903042081c0742ca08065002088942508001e40301500e1441031034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 235208192 1250 235206942 235206971
    0xb0c010f2a020706120513020306090a03020d021b0d050c0616020901050402030f0a0905030418060e0702010b0d08161a060108090d0e060f04090e071a03042f03060901 73
    0x584418610340302a010480c240640504450074101c110170080c2d070346900061450094504618510307800070202c07012403030800001c640e00c8450700e1f4101c00601500c00c8107a019400000c614241c410003c91201d8070034050300c1880346491905501341c4851265000c1c1481c680c0303c12008140b8401607281b00a1748100c0381c014400a0281a84514080c91041040194000c4140c9135a0340200316050040340309012420040d18500803500248803c107030b6144ca00b40365103c07030b42c80f8208607010308182a610343d9034000141d00b200c1d01d0030704140d0469440c0300482c0c0090012401006030031013548401c4134198450700c511881210803034a007403800103c071040c4041d5607004900305900504c05001001d194080e190014000d403040e04000c2e00503003000c0f954001018880c4240c6000d81100d46081001c0c401100c01c007a40c81f0001c0c1b08001185c041d4100044407036107010100c0c0e05c5650440c404020720250040b2140428080001c603100c3c03e441810102c08a6400303001c1e0500402c05040081500003101140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 235209442 1250 235208192 235208261
    0xa060c0503131d010614030a020306010c061b0215011203050a02210a0305061e13020c031201151103032202041a040b0a03200316080a03030f14010b0c010f 68
    0x11406000f40d801b120800e8241e41c4080f40e500507040c00015072a40c6a80c40184d4140d094004d0042c659420b085142038810398901c6d0391310300000150b08030b801c100c460b17402411802d0f20a00a80e110780c092440d0100209000e0001844515900d2044132000c0c5400901e00d41411140e44021082e01d038002030304000207501d4000c240d0401c10489034007410141022070242c004543c0d14203e402101c070004002141c0c8507070b5060b141c0b4050001c050340d03665100703000220071150b82400389480722a81a684400d020f4071904030101c000d406200158030b50303200d03c8210b0b201009600c50300f0340076550a1000d1070060303d075400f035000811024580480b92101308010442074958108841e405034002a0041000c070b0400d010499041ea00c00c4044180c128805010134200910380a000405c0c15102c0c10001da1884000f9400d40c1041c0655070411036003c01d14102c60a03a407c01100ca80155500310062044100d11001800c50300c800c48000a00c62a282c105003064403004201041101509541710091103111a43d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 235210692 1250 235209442 235209449
    0x303190b09091e011107050102030109060812040e270106050f030d02070504050628050301050601110a0b0a0609150503010c05070201050417030f0403060c110105060a060c0503131d01 80
    0x654003154034099080b60703500d070902c01c00004414103402c60f03490440c03c02e502140d0820440003e043d910300b01401c005010754000c2c0714403605545070100008108202161201c200c0d040040c4040c0b40c54906042c60390f0308507000d07014291040d888601500c988500b86039180c03500b46884000f10311180b03030404120308104000362050082d0028101000016800b080c01d0050302c41c03c550000d160344850b408504030322000683d4010640e030b00d85a109045030540800421200218001d0150f80c2d41e83c8011504501c521030402e02c6584444020400900c9040c08981e11018403080000c61580d04c860200907100d034003a00782c10b205406c9206100c0303400c0c2030240c0a40031040d41401071034044247e000034141d100e280704108240316034455440720200c0c140105c0b00344c11003000e03107da1119101c0c02c08a000300051200d01000c20000110752682241c18040c0781d00c030300e030001c00814101e850010700740e03050034079a1021a6140820000b1165601c45408020098002c03030340040514142074640c806040c5041e007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 235211942 1250 235210692 235210699
    0x12090c01090b0a120f02071407030b01050609060a0f0c050d170a200a0c060c030204180b130c031b0903021008130f060b210d050906090f120303190b 65
    0xb105854064000071303040b02d0294a010009104804407a104000740100e04004190350729004954030f9106001600105072400340008010607642c91040054500c25400e00f070b0f4020900380009131410b80104100d228020403403d104001901660b00c285c24845013006000c00700d0240001c02031965140c00c0ca42d5401038a40c0e000f00201c03140c07840740701226025440e90580303040b4002226250720f403044426070320345903009e4002e018084542102070040d401c00d0294008026252000c0040d001d5076004544580c0030242062040c850604103580280500040c907100703068441c0101c400c491070200d02040d4080040da40e040d1010304610400140c01c0c03100141004016074601840110001e03c460038841c00d6202d421022041c1e080d00c0c00b9000742800e6182d07580e1040214038054005190003110715101407032502602c4041e402080e094400e8022000c0396a0403000500c11525241441c4c0040c2080400003042030810303084813058185140e204598541014040c0d5000041500050060825008044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 235213192 1250 235211942 235211947
    0x6020c040902031e07090623010309020f060906040320400e030d0b0109081b040504061d03071101030506010807180515180103290612090c01090b 64
    0x1038002030399070501a55041c1e940b089600807140313420070402c0f20784018511004140a01d6981c1c40402c2d4990880154020701508608980c40b00c0350310a01c0b902c203040303600620307814164040350240318164110001d9203400000800c40840440c151400384c6024a036440030780c0c01641106401d001182000d03880c1c6841c1d810b0450041030380c04003166000c40c09440e02c80b18054003489040c00d0340c409042001809200340c00002600002c2e402c098011000700309080c0c9801c017640d9514400180d607a5209248164000300009000405d0300c0c2a4001c1c540050254802140d009a41c0292941c40c2c5010090185154000240c20040006038480041695424201001240f814400180c00124018151000c1000b511350720681d203188880040003030500070f0409070002e0003403903010f030300c2e648010703a200484004031010501c0340d80f203030044000f2090681a8098400c054802c0d000c03004800c07500c000c1c0c0c0070900340a06da1445480441040c4540e0f040002410821034500025001c12082c0c1c02400c07039403008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 235214442 1250 235213192 235213211
    0x1a040911040b0d0504060f02161109070e062109150a0b01090303080403030f0e0c010206160203040b0c03090d060b120703021e03070b03041a01090608101112040c06020c04 75
    0x202c0c0180c40c1d5088108502041590300c5141520091214028502c4150f20105460b2420010f0300c00d07140c03940384511510800300c0600001c1042d0347c00304aa40307100042205180070400c1c180a4058800c040c0001c500340d04c05170f40949905884042240c012186074003001c1e0280b410025481700c16004426407504021400f00c001c0001d000b00b100340005811706c01c206011508152099004c0d81d80380004003020450800c44000d603039142c40d0001c00c202c0c014440d020200365800d140c040c0d50704404410b50015494140341ca00003ca41e90050802d6018034001403004002c01e8032903440e061001c0b4822040000c0c1e03102d00e001003000140310011040710715441001c081c00142c076250b0301c0c0d010f500305940a56201100401c00246065000e03048544400c0000c828842040144140c1d51041107250007241c90780d86e00c40303ca240c101c2c0c00f240b146004070342c0844c802c10100020350380f045140742c2100052070b140841c0c118501e0318800007034070304451b14a0101000c02c040f550511411040f000200e0341400415207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 235215692 1250 235214442 235214459
    0x9051c050a020613080c0f011b02070f0626010602010504140609100e010f0f0b0108060315010618170705041a061228090302011d06041103071a04091104 67
    0x10040c1604d416107080c442e4403040c021340509507507501c0440c101300c8880c00066001ca501825442005041d01940349002e04070460010448900307076550714510b41143d603d84a030403181c1040e02c4000984211420060a01c1182d040365194060441d0f6000030810381448d140c40d0349400950900948283c00c00c6044c80070480c8080364100c0e0b00d1074140c034007246021020000038010501c0c541c030001c440d8074001801100c2d4002d50456031880f80241c031010040c1d41c482c020b042d20744e40d0342c0000710610003401005100403805140401c03c00710388440058003c5d41c0301e0311050100403074401785111681c8800b0040195141500800c0440d04424400807a00300d007034800301c0e03224043c0740010301c41158944002041010040320440204508142d1600c4454480f000780c00141b9900c1d0003a00154200902d85010b100d0f010f0555400d030045000800132039469480d0b03402d06500725001140e243c020203000007406102212038100e80951402c01c1d1f65602e18050400c412a400c0780d081101050043c00100600c82 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 235216942 1250 235215692 235215703
    0xc03030f0309150b011e020c091501020706030c02030403020a03050a0c09020a02030a11010b043201031a0a09020303040b131e030f0c0306110403050d0c08090103091509051c050a02 79
    0x14000c0e1000310b00b1011003401a1900e881b170310100d18010318141c1804588542c00260452411030545983d5400e8072150340c7c14401c00c00b000c3d4410b002d80d0004008000301440396100c90b601c07050510590f4241a20b80d400100c00f81c4066109035503e900c260058403d100c40e00c040c45004040101c021480c0c40308121002c0d440e401840c202c142802090429520030b050300b03401c800f10124008104020203401c1003540c1003111000e1203400c910102e240070682e40c5549461115040e29040404100245242d102034608500300500c29a49952200d049000685040000e000540040e000c400e403550311481c4244414141d644c06041c80021140800c542d15074803686032001e494002214402e0101c4074100350001312140d074070042c070702490000d0750314000100c1d20240090300d125a040e1204072070460011607800c020f400001d00800010490450103601907448501c00f54400e68003044490360300c84180b421035020010540383c0750803a4010980707160280c00d820226401c5401e000e803c1895141d402035998 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 235218192 1250 235216942 235216973
    0x30f0d020715030f141e0103020a0504020d0e07060503071d18090f03040311090903180415180c030b01050c0a120507140d14040b0306041a0d0c03030f0309 68
    0x10b82c0400c80d0080d141d4403c3e0483c4000c128820000e11070303940034400c954042003084075a0000d542042074000c000d841c1c94030b5414100c0b41c000308001c259034104010400203501560001541c2d640e1038042c102d541c0400d00c00840201034640710142c0702d00c0c00c01e80140001c030f01521000c0b00d800040110145940d90815013030f0540c407220244001a035906514285404107a462107420740c4408940001003096610220300071110903540003a940e121180c500c7e40d00d00a5081406084246803103003207407820560700882c50180007582003c0081e44d81c541900a1031941c19800c0703e100d40300c1e46002c0133283c15000d802c614080a282503850209085900c50b280c50b020b91009021250300a00c41da40e0078840d0b01074030002034104581440d40d00792103a600ea039440404045002180264500e20218540ca0f0b040d90100e4414200d1640342d940c0d100c04100040ca4601282482000000307444500d940310620064011072050101e00c2d40e06065090249c105050340551004041c00c10b004072000400c07144019560 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 235219442 1250 235218192 235218209
    0x1909090501270210031e090303020904060308130608130f03021624020601080c1c0605090604030e0303180d0309050303031608090c0307060c03030e07060e030f0d0207 73
    0x1282960300d0031030301520300c01010540342541c03000c800040341000c20081107118401c442030703120346410400c290181c420200f102000b998590703400000c0600c2a8224140c04c520038640145800007070070019080b500c9a400549680c0c4021403142e840b0310000704e00001038041801d000307a4600d0040c01080450030142c00050406030400c0783e51040500821001c1c9040c0c03d00b1004200c1152039580b4007038180441100340b51004034a5414102c943d0000c14014180c40710140600341020040081c000c0303400001c40d5103810b0420520784c02010070401cac810310380100e041c180500180d041c01e04009018441c1d845240d4440e4208000c1110b110320f003c813850310002d10030741d40c40d1110a001e00b8140e030602c2c02a80020b4041c0800030030807001410108541e541000e007510341c10081e03243d04ca0350b03540d82e030200900b26806074801c0105100d824081c01c4802040c0340300345000709665005c0880301d402c040340d80d40100702007286600d10b03500c645824030585d0460040c1b58020600180c1c4103600030759aa10134800e0628 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 235220692 1250 235219442 235219451
    0x705030a1407020402070b0403020c0f0f0415080601090b0907180302040903020a05060702370620070303021201060314062404030b070801050105070b010b0f1210090b1909 75
    0x1181518070203861100d034000f8030454441240e805e01590108040702c0450041c00703421017100c10303450214203c40310807401900d10003107144148140300003031501c0800044160410600040c00e00070404c405406031440c031034007080c01ca07500018010300d0344018115500340009a2070f54041c100b61001040304490301100c4c00f0a20100340e0900380d04000c09288058214090703001084049600040c1580c1d56109003010b00e0344503689a401d10300d545444113943c6005645030400000402c1284d000b40c0010070002c44540341c0c0d914003240405165000c14400c401098000c242d01c50006000030100d030040182d0304052002e01603070051502d040c2c4000b030105129142c081d24240b03000071000e034030182c60b001c2013102c035580702e85a0510100c5220210740d484005030b0410300124480d40b2580a07251240e90200289406900788030300f8644c0c0b90007039400808900424010300da20103000c200b985010b0f012144141e15607900302140c90082c0c40c07609040c207004801b201c250400b48200c0c5c80c4042c0485010160005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 235221942 1250 235220692 235220717
    0x3070609060f030b042702100c080d020c07120c0810020403020f010c030522030501051e28020301030b15030304120807020a080a12020f0d0c0201080712050a0b13020705030a 76
    0x3c0003861403110810640d0348040207001c1b60101c0300310f0032146030700880b00c5190f08a440345080301c942d141200700070315002003400400b8402d5941d03006444143c9851007960002e076201d1100300c2081c95040c030180c82285000c101001074140602c034558075031442d8402545007034110340124501400c0081114100704d01441d210040c50300c1601991600454800809048a442c0c00690a040348500080d10a54600004124202411748200301c3c03008150400310143d07030b00e1180800d101c0d0071800200c2801c000403140c00c1d01c2d203181c910085028503c0768100d41000d0914201d2082d086088611751400b80d40100001d1142100c0040174003019944510303003d41e506528404520b030410b50342d00001451181d10704a0301009000010319122480550840f04207128031035416640740c1d100400800815401042d41000d54402c1808035070003251810f011041c1c4078070300b500c001110b10485404031a1513460752182024a4441044081881c910f1015420a8400d03207c50b62203103d8481110b09004036000e111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 235223192 1250 235221942 235221949
    0x7030801080601320901090905070f0f0b070804050910150e011d0609040608070e0a02160303020c0a0213060f0506030405071202010207030f03020102030a0608012a0207170c03070609060f030b 84
    0x941c1074041e091003150359507001c020014201030341045406012b50500458001130101790101140c240c104070b5803580345040349101c001ea000352000d4030748503010000441c45455069859000d881d040c00b81200891810154100b020074081c0c03440300300b10840810b120380341c0e80224591a0300d000c00a070700c1310282d800310000d52a8414a42a40d4216080c8040015588404514441210220340c0c15810598402300c0308412071140d110035800c5403c110030501c020a20a90280a40c000310380115803220314145c00160f040e5124096003088103854004c18008600300050030401840d05035416811410960748464076503c0d103015508080000c00c080c18103681c0301b080400011754000c02840b480402608009020798005c4403007c0d2890304242d00080e00381414440c3c1220420dd46100308403501406034010041c072205100b003411440340d0380f00803801d0b8607641103400400502000a01a0fa56003000349070400d040c0e648200c050050020080100e683c010600703600d1001c0d80e29002624040300c0000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 235224442 1250 235223192 235223279
    0x908090a090903080c160543060c0602040b130303020c01030e031b0a080a0302040e070e0d1119060207090b0405071b0305120f0717090a02120c0603070507030801080601 74
    0x6011480f4182c4103003041070160142100802c41504003840b801300710103035040740f5442306503080e02203400403000700042845014400c400f14801d00b0054a410b5507002d14021640189903009005140700201300201030701080303000142a000c1c20180030003170306421191340303034054001c0c2c0c03440007810824584031094041c410344c00401e45c000011605c2d021402c4000780250070902a0b4102c0c0f05400380400c8255008107280c4224402c01400c40040081550710090a094510603c41e0010001c0310800d206010030013188010342800c1d80284500740c9469000c0d820b07039800c0e83c1101c3c041e6180c101402043c03540914800809001c00090b9050200580f42c2180e00b84110f0b151601000b0542d404d001d00d845281c01c0c0c403805030546503608003000100000c0c0300d07102d01d82520a01060b0b444031140c03000608080b44203802c01041c3c3d005842a0030b2083e40481d88582c01222014001280029000e017019040345840c0d025000c240c0003400e0542c10700301c29505c4001c80b840000c1591490b00486001450340e0382c1d5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 235225692 1250 235224442 235224487
    0xc07080c0703050a0812090606130b030a200411070c0b0f0c03040e0628050d020402040503070602011d1603020d02060705070602070611160b1b010908090a090903080c 73
    0x122100c4d8500c50a00c204950032241301820501860008a42c40010004010340211b00040501e00103c010380c0001c2e00034159544480c1c1c243c050440c6050101e544440540c0383d0410340700200180c1c46a401c2004101e82a0340301143d0042018096000401d051822480c2980c49591003507030380e9400d0014045807070240d45176903181c1c0c0c480042e0128074115501a00c90250754160f60790741072507140303c211641c0130303155164a0850b17180c3c01c0810031080c50082c07003941c02240058001454142c440c0003103800d1070001c1d0403040c0540e440f0311181131141c40501d40680c0001507140035200c5080c08038a01d06c1b044035280701c080d200d685c80c44104001d5503600d03c101c87c800740d8032034119001e00b42c1c0d80364080c0d03e03041148512000b00d4004110141061004215012550609404c8001c95800c04290329815001000508446a100324002e10718a000b4440d1012040c000c04020f030300d8080d114100308013100590070010046041c501d6040000ea00036038080d4108800b00c0c1e010b925a811401c6144a00c0301c40e00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 235226942 1250 235225692 235225703
    0x8100308130f03150e01020306010228060218100203040b03011203110102030f0106020f0307350c010b0a0501030c020c0d0204110a170601080103020603160203300108060c07080c0703 80
    0x4000410080700b4040005030254041c0240074440b07170941498201e002c211078040c09030f040b084561102401c1241034403292041c86010340d07120300c404c1c1c40f044102d070041031110200716185090321107103150800340030790128240e200030740c0b0389410281c3e60742070350006100c1c080300210000741351300403d0300550040406061010085440345025180c03104801000e01c00d180c098024841c55180502c0c000c402c8410042c0c1000a03110464030f2420a0b6006100002d4121144441413030501d0b944102840105500d042040000c074100e1914001c000d10a4525840581818a08105611040d80210b201c05981ea130848411a203581180041000782031001958004008000b54100030740340c0102c5081a040610400902c1e550707164001507421840a01010f90301000c140f00244403c00560055080300f150b5105890420306029800c42c1b603000010745001c011088001050b100b00201071519004198000041c40319050280b00440d40b4421300001811004001881d41c40c02c2d038003004880e00071580003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 235228192 1250 235226942 235226969
    0x6090c031e15060e03030702090403090305150f06040506031612030908030405150a05040806040308010815010e0106030207050c09011e09050702100b1c0606060f0810030813 76
    0x280018010015140d244100268400c500410000c0500c030b4401003169a41d0604811400c001c019645141180d00f242c1e450705c400c029120040e107c480006000c0c0f84a0b8a03407007000740c02d42c6407060900050070010081103040c00c0c01c1040c00404207410f00c0c1c101005507000540c41d252000400d041051421450f40032881407240040c0c124804445a45814041d039101701040c1d40768000e01c0d1b02e0744a91310403154030240b420032940ca20307066400141080c442031700b004c900d00b61b690340e00e00c3d04003d0200c82c150302090740c060042162000074004401c4050101e6152401981448810280794a06000c0c4104042e03002c218541040403c00200e80da12000030000485980e54412180582da00001000042101407900040c45611801428040d01b03560300608100104105100010400e40c100703543d12128015102c40d020b01000306011759917000e80b034003040d40c80c100980602200d0b0b5070b405040820080c0403c0040c4140c00341000c50030390b90700940c550b995800c2e1008803014032400b60800c0c58100140c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 235229442 1250 235228192 235228211
    0x60d02060c0d110c03010603080414120109080703030509031e0a02030c070f060e01140304020405040c03060c080402041a060f0705150a20040501080a0506040f11030612070b1c0609 79
    0x421549a05074503c41250028000003042c5401c2c4c0d01c00d4031006010b000103101c18050a20f0500c044022094090076540c040600300c0141820f4807100c01065030351910000d9a00f090680c1b42c01215400f02c01c55000f58038101c00c108034010b650800280d481100c400201d10509124402d1080707030b00000180c0111481c49844075403107056100c041c441c40000ca401d0f030748106802d501400d414180303203504080c0c0d6803e680d0343d40c003440041c020042c0101c0d00d01445250100020700b640c0708460006410780e450b25643d207481c1c030511044031100c00020440d60139901103800c140d501d00d41103030380c89584040c015444200902e001441c04020340e00609510b01c2000411094404071351003001c40352060f01c84998490807503269107045100d14040c45001560210018030b2044881d0804ac3e0811703406840001d040c008201e2140c100ca945c9a0b8802d03c0040000900516141014616000b1480c92002d011058900070300c240c0030340b00707441e2045030b00e2043c1c890403000c0c1c0c405a0b020b0001416050418400242c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 235230692 1250 235229442 235229447
    0x3080f09010c02120c010603080c031b0601050a1802090a08030d1406060306060c0a06110d0f02030106021507170c030106120605010e0d0510020c06010e090a0209060d02060c0d 77
    0x4540152048586a00241408005014480c40d4260b56009025840882e500001150b84420a510050b43d00c4640001c0004d807100010102c2c16460005181c40d5040e4080d07021103001a010000000c0e0b003c14018001c0d6a19a44408120b60502c0c03205030880e0034420701034001e8014880000e5008180500010305008080010000f43d03c0c0d01d4410000e0024150044241c20350544815401010a0000400360b04100c80286100068a03049818012955a944041e240c0212400b845040082004209807481d8014080e0b00e2181400540c00d56042044c025070301d5000d040c0c0e58800d03055102c081500c25004007903c00d043c102c0d5900352091454060054030040d8028411240090400d403040180c042c454440c0c030090b910148e54810b06501d1240400110020f0100295814043c0b000c66840110310b80c070050040c50002405003076a5072620b185080030400040c00310a0b181c211103070050042e5aa00c0f44076522410485100720711140c1400481c00314040d02024002d284a4844065446074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 235231942 1250 235230692 235230707
    0x103031d10082e0b1e210403050c010e0304090c0914091e0a05070824040203090c0a171612060c0302160507030c0f030c0b030c13031109010b1c0e01110703 68
    0x210341a80429607006940400c00d644914954a1030606e448072040c0c2403098085034260300640240b8003141000006140a03013115413070142405541c1c000a4100000581c1780201c40d4500014106403425034680041c8a1949114400c200d1046004c400010a07c445140140c041c42c0545042c805541c03400349007142c000e11082c0c1e20301012803285000a409034a841c1481c3d044503007120544060310a080c003c0c00f0194001511140d41b901031054110b089031a1040048014000001e544035004000d20712142001e0011070181e2040503480c805024041564840c0c80d801c5e64043c2c2d00090b09202440c044009000b90b0380c0a4400e800e640c05940240800000d8060a0b28090441c00c1c21266407602c0d030002c48007492000030014503c089040042c850010040c43e8048000c82c80c41e4504032610130690343e0703074203603030801c982c50311016550f41c1d01da0803d14a92400b500c5030001040c5482c048050880e04401c42103130041800303868bd844410400c50a40049070001c00004142d9110016403a0141016 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 235233192 1250 235231942 235231957
    0x8060a020a0912121416110a06020114010b0d090807030329150d0e151012030e04050a0902040612140d090620060103031d10082e0b 58
    0x10a6807038045043d0a42020303c5840030303482035800442d1521a40e040d140d00599841e0300c050144180108201200c0141101038018400d000e002e00951644007008000b010303580000c011a072500300e60100350703404503403013038199040d40702815229503118005c034000d80b0780d4a20090296101190030410503403d608412000c0e1340c5001e0400c14429000040040c99210001c0395501c03100203071010902003850001010010b168900224003a070103003501614040340d00d4140c941c7d140c0d04400300708000405554010203440980140540102c441c0c40c010000e00b681d0b80400d00c15540c078404954203001962114031129405002840b4040c0d13141203c84040d03244000c06c0e82d261445a2400c1114100828030a998082a40710064031034180300d801c403841e84110000c2e0302c00c06442d4070b4560301d640c000c00440b40254407035982e8643c02d403c1d40d004401071a00b40242c0d58000d813802041d03c41155041a2001d0340314044001911030816003d080c80c0e90b403818041c404400e030f048001d000c51600280002800761 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 235234442 1250 235233192 235233197
    0x1b0312030615111b0301020c06070e0a080d020a030f11060a0b03070906050607060504030c0b0c18121c0302070c030506060f060c06040b0a0b040f06050906030a03120902030708060a020a 81
    0x30a00141c029140102402000d8625810161a140400c585543e140300d60044c05000103043c4150900e0b00c1e031410310251084808540340000c0d80c101d5141c810712000151050360050302c80a400a03034041d41d90308440301c0003018403494004040e1564410803850f6900842038045a01500340f80514100820750044103d01a004009000c22504000e0150604840340900441c0c0750039607540381d0400601d00980210200100340c400407002c900409600750103034250351540c03035840c402c8170b81c00c0b45044010f9008500400c4440040070015801060600398031020b481c0712189400d603500114000d10070000010f140e6029060080240007000485910548090b1403114100c0306c0b5604010040c0215050000710794040000035002690580c69113400c40d0385d801c00415440d04040004064402e4a481c41440550fa54020441440d19040c8207400c900140d0103044020b08907100141003025002d02030316201d4503008007400f19242040a0700080c007019094070f4a0303003442d540075000b03036005482a400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 235235692 1250 235234442 235234469
    0x9021305040b0106080907050306010527010b04050315040218040320070306140c0703030e0c150c06180304030f050304360c121503060e0d08090703020d1b03120306 72
    0x2000c000007d200415100000e000345143e078a4130040254500011401e1003100c4249510001c8204144d52480e01809010484903125800c003800e1500d814010074000d04107221401c180400342e00c0303070031540d40700946402c804042940c403810151824103040c08841c0c01d010022a41900c01080480c0c11000e0b01d108403424040c0d00c94062580c040300d601500d1202c1c1e01c00b070401035280024081d50000d01850415010740307154010780340009540c00175918041e02804800074609100000038000907901040311080d002203000300d402c400344d0382d00803030100802000710005150240701081050750000c011114a14115008081080030f078041941d2009042c10352000b40d50700461054020280c000c80f040d9a4001500c203e840840c01510320f2150b42650054603002c04800f00340d031b6014849001480d000200429024280e009208078401049440550010300c411f00040c1c1d9810341072610300d5040b4010302d071100c010b40ca07100c031510081d51000381804c030f1360b4181015140c0c064012004840c456641d894 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 235236942 1250 235235692 235235701
    0x1f020a031a0102060106120b04020a03060801050a15090c090305030721050903100507030e07061d010806090c0f1309090309150e04020309011103100e010b0a020d0309021305040b010608 81
    0xc164021140c401c0d0b001d600208014070903d44242580312106401040200301a40144081401c0368001a40000003940b903c03000e00008009000d10b0390001200007040081e030402c0e50409043d0582406100451521006d540002c1c074818840000915004802c3d2a40c819085c41d10b4816400802080b40380725883c00401641540564140c0c0e02c01c001c060301a00c00c4580300d5500500510000307280e1024117a440c50004102e12041000c0b202415031511103644d20080107002d8103090b207081d81118108032100381008025101e80900581101d450104207496413418080404a03000d10b061601040b8101c00c00080c8440c81500840c00036402900d4004000c1e458951211070b024440c034000010810722000c400407804d00764000d580c84182c00000061b026050340d9503145641c0141c0d013601041d00c03c0513040c45003002d0120200d0040020101e11031130040038200103900d8407a084802d006269640001c1c800707540312a81040e8080300c00d40420006c900e4540b03414001081c0030b014001c00664100b0008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 235238192 1250 235236942 235236971
    0xf09030c0111030712140d1a0402040506121e0903030703050f070c020f150705030318070501170601170109021b0105070215040c080304060f0e0312030402010e031f020a03 75
    0x2402d44200800a545402e0158580d40c4d48004120350031820810010802c6034900c0319040541494241280c01040000050380b0101e012038506401e07a2140b841044100807558900e8100d66103407042000800050391549034070035520004c1c098200c100107680e410040340c0613001c0011842801151030070030280c3c4a18810850084040300c0303400c041000e00284c14007600e043e040921048100800b0105d100002c1c11944105400029040358150b00c08410311038610340350600d420641c4120740080100354039120009003071074080042c040b0402c50120200315241d102c4e850032000009a840941c0d204c0d42c2d1221068000d5000107844603a078852618042140f0714103004160143e943d07a401801540085000001034000290044840e0000e0000014038400b080c0068030040c49a511207112074449007001400003099120b0003031084e00308401d00301400c0001c40a03690015020701e88045d0400498000c41e140581155030140420b040e43c003400355482c040c0d002440e084810350703010322400320044000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 235239442 1250 235238192 235238207
    0x60e0c070308041704032303070f0803150301020a030209011b031e03020904020a1106101511100906060305060a02031e0705090916030e010902090106051c050c13140d02150408030f09030c01 83
    0xae00c1e02c58100d240501041d0898042c0d80c0000258601c05402100c0d6000203003241d0108030f40001107074000c56801815078008000c4010a08008006220281703240e44c01003005044400075520002c0c40152040000c2c4241d041c1c407040c4c600a44219961940703484050490002c040d09550940308080024440d0042d030542c55040b00ca40c043c60326403030800050159580303a1040d04010407841000b582c00c400050b039003c0e54603554051540080c1290031030400030304160000b01a484114010801d003c841347c4210750119180c3e9200481c41443c1d01c40b560121124030943c181d10768004070702d40501444058107511100303203040580382086510301c5403a50760b080e90715030307070029520840e400b004000d640e02030401040c80c2c0250181d526003c0304520090012140d041e540c402081c840813031500d09c00d80b40201c242b400ba140e403e540c10310300131000d40061407002504000070b005103a0039014152454842e404d4034058001e1900362515410690101c0c100744e004010030341c4c860312442620412950080f2117 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 235240692 1250 235239442 235239457
    0x1015080a0c020c10030e01110d0b1002120a0e12010c080711070501120b06070b04050124030209060d0c1502030705010605010504060207120f12080604060e0c070308041704032303 78
    0x70490551451807800d8004000005513031b0025500d602480540c00400002000c43d40805d00b000600c8142d00014086031070381e820314500642d804100380d020070000e2981910240034440c40c0c4030080400300130100e03094045161312450b5940c00c00220703040d10340d003194000e885081c80340e40700c0320742c3c4070010805035980c46c0500c0790301e010603921102d100c0350b1303030307040c0c10100405c03d000d014035203003980a42d9254512003044805451a07550b49894441000c0000c0c01e11010700d03059008441000d0454001031402d0b60083c001e00e03c0782c2540e80b0b0010422046488540c020450201e6480c1000030030b0001a4480c1d2048000320b580d07528000000c940c0e50302640584080d90910381c010100941001803d41031050084000e0790000380c00301c4000e0010706202e04100840c44140d81c1d5004900f0b101c810b00040d2501070f040b0281c108401d0042000c05110319081e01d01e040d070141307030a094030780701c6003003103645c00c50862030412010340300207000301c240a240c007001c04407485044149129090700580060700c9028826 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 235241942 1250 235240692 235240699
    0x40f02010f0e10030513140a030e0405040b16020a02030106140f04021e030405011e1d06070206070f11070308030f090c0a1a0d060603050a0b150a05031015080a0c020c 73
    0x310070350b08080c885c0c4d01495020840d030003035039992156500c0e80701c0c85070a10703040e40e50683e00c05507100b8201130740002ea500103503a003920207002c2414a6929801c0c9030400815040301c00d010407201500c254403c01102400e01c1d0054000c100d030b2516040000c0307484000c0402d050003544403481c451140d0603e482264147c0401070003210b403180403c90381644660000d402071b0707070035900c03070650359a009814031003c0c4904910050001d0210441c0341048176004005403220381c0f85e04420708000030f0325008140107602c40da491801d001c00a40d00031042e00d56980315404450f162240b0400481088603400c006e40c0140080e041e0145aa038404000e1a42c030f001281001c0e03000000704a00300410225075079051a103a0b20110050b080c00050908841150f60310b0344143e000135101e90a0191140c800c0c41910240074098a4072040070503001030300112442400702d2002007010002c00180c8032440620702c00050b02200190041c4440c45481c001c0015000340c3d0b2189000d0300d002001c0c00d100d4000112041040c0015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 235243192 1250 235241942 235241959
    0x61106040b1306110417030712050a050f0c01022107020a030f050c0610030204110406140f040314030304060606080906070315150201020705010b180a0b1503040f02010f0e 75
    0x1551240c14145010b04415501081800c8030000614640100c0550211203198103031103a20b444004400007600d110070051640040051902184004052200c03101e042d040c6240c2e03481100070f0849480c03007200c12154241c000802c8403101a107040d002000301c140155004405a400034203610403001003a114100540d0140e8440800a40150782c01004401141000c07410064009142d40c01e1050451300c18140055a14080c401c6207054410030079090f04445103a0f040ca03040c600064a040701101d107c001c550310108000c01641e004408550185a210000da400740306048081941c80c0c0054800b200c600d030500b0004502c0d00d100320301d4640320b022500c0c000c000ca5200e0010590050000e00e200c0c91a04408980116904401301d4040d561070348030364001039603541d03142031241c21614140c0c3c0d034500c10f0842c078802048140c0701c01303002c40d00500400c10014210310104002140c1010000044c000e02001204200030300c4442c1c41e018402034000c0e02e50405036182d00008460030f06602200780d5110000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 235244442 1250 235243192 235243201
    0x420060d050615040e10050111100f0906090b100602011a040e0f0106030b01031401020f03130507031e031101110702100c02100e1008160f02070302061911060108030d180b0f010f061106 81
    0x590230080c0c2d2020be1282c00602301e51180c407020f00392011400300703896004030401404025100c40e014000188454030003000720b190591042001c00043c5903907240301d203403100000d02110100b4000000b40d010b0000c020401241e9070300d0403400009091005445e14140d4070182004a28107000b20340f5008210014036141d0381e44d451541c440600b4461043d50180704100c40800007030011020403110300e0154200017504115458003e16034001040550a103904144002c44c070303600c0c1c000680d404147e0480d40821000c000000854400018806c083c0d4042e0317150f8900310311749800c80321155860400740c0b00c40c500e01050400a442340f5000341c5850008072194002c00a01501c54109840ba5110510544103038607501d40006004e60860501e80328040300656020450542246041410f0580b100203414150300d0040215228080c1520303e05042e6220b0804118081380300b480348043e15401203980d9110700389416a410031103003d001d440b80c440002031010500c07501030071081034000603d000800807581d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 235245692 1250 235244442 235244473
    0x613030c0803041b060509210c0609060706020d15080d09060302030c090409050c0913050a120302160302103c0902030607080420060d050615040e10050111 68
    0x20f005032111404c10b0241d03c50280c121214800904180c0c2d201925406154108840c3c0011700300c0c0045010080e00541d4080a40441c0740700c07140c201100c00640340d020a0340070448070300c50108024005403000602c0d003a0711080d40d00ca0456041001c9184080707135100d0603a10307030719000ca1354400007095105c04200030261003070b001160311501c901c003141d04214070937000c503044d28503082003110a40c201c03c8510007142070141c600340c2e100000e01c2d800302900b070303154550b01e40754194810040e1a00c40b06024440d0180e000b5012a21181c9030681d8041881501e420000d4a49075442c1140300322508040c008003503245980800d500811210307000313003c0380c00c9000e241c18410300318905034421aa02e48110340c015a90521169104805075211040d203460280b87c40e012500d2078402c000403014036004d61207255103a03841510169007030064001111f0300e0300400540c074802302c0207800516000016002c2026001604002d000d8080c030140b01034100c1c0c6403401910180803103844501580c0c401c1c10050f40e00b80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 235246942 1250 235245692 235245697
    0x60b030f100b0c010f0e0a0c030b070215070e090a060b04060c05070e01170610180f09050d11070807150f121401060f03050c04330906020613030c08 65
    0x1a011031841d40450341c580304040e41d50020381800384030b80d644040d5140190480e02846d0f00c801c0141015020f1440075540300c2c6010801070101a00000c4003000285105000b00b04090004104008280d41858401c200901001c54010018000c908010108a030340616010744402d885240c4c03403503402c1a05061080314212039900d0251003a20817020001848048040e000d03000e454103c500c00308505c01142014034141002d4035100c0721003a0300b07004010254503485950070030941210049022400c283c0104090404040c0240550151045038140075420004281c00f62a0020a03030707001c42d0b60384010350b403656894810324502d20f0034010014521352150030002d510348054103100032640041d2111f48211056000160700b20b540a000600032942c0046654117204c0c4103240034040342c6016102102140958450ba00051080308124a0b4581100208007203100140703140040c2004240380c01803440d00c0620074140540585000706541102c03010360800e41c1500b648604802030388540e41d04c0d400d035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 235248192 1250 235246942 235246951
    0x408180d0b060f040f020409020a11070e0a1802040e100605150d0e0312100302010801140d02151209030a09060c0507180f1802041a0d080304060b0607030314060103060b030f 76
    0x83c0d07076170302e640b404064502c00303400a4030040000588801941c0c01c06003440290601d060300740e60040404103c0446807201c510744c05440c8103030200388490990750300310880300c01c480000d5010741010ba214201100c0010a0801000c403a402880442c0d41c0e0014030600c6280c013681d0800401c01003049501e4020180c04c104640304461088034078111300001d06c008010010340d2425070702c61444604205540c0c0c415420750261141d03e0105658002640004a4004e41c06000030b0242009140c00f210b16079007502910315403049011200100d2401c03c000645a40c4502d08100204900090200b0500d00c1803060b0700e0820340c000024460142842402003a03050503034081c0208a4468080700955002d5024502c0c0400034101c1040040c0700e584108030a443e000c0d01e282101c40400300132142940d8505440c041140e0700000803550b070b41c40d603090a4000d06003006a65411520000e15802050790682c0807602e1068900c05404182d00c4043c011400e45000344114650381c2401e20108080004043c250b5800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 235249442 1250 235248192 235248199
    0x61c0602030612120316030513030e0a09111c02040e150a180507080f06150f071b08121201060318020a0b0a030501120203120a030605090408180d0b060f 67
    0x2490f0625959a28000c0e010b050054140808401c3c80340e15924801c10b90400b91880c24103203c2440c10304041400c181c00118084e081000c40c2c013809515441b1404060054140390340d00380480e84290400502d00d03403004400c020343c40c2d40341d03280c10240b800c00e109440070345808000010041c0c4502c6841040001d891480903030004407480e000860a145912510701400714800c08181c034644040003905080004201d042c04401c800304100c510b40d10207480e210030303a4140b660356442d0a015440122035001d01500203021042044854652254160301c907002c40c0d40c200112020340ca80b0003540c2519005146013900b184c04000e0061105a00903004610a01c0c01003002c044459000e400040c40d000a552003003c0301381d000900103403010380c103009082c05050f507000c42c14148912580030a680702001105d107109107102068031003145109801800051100a002d034149050a0420904552010551042008261b007a011007414000c060000e85504521203040540e18001400388100820398612b60 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 235250692 1250 235249442 235249459
    0x40b070b090f031602090702010b0102100c0314010609170a03080a0c0c06090309060306050604052107150302030114010e090a02030c12010f0602060c040f0513020c10050a05061c06020306 82
    0x2c0b50104050a49003403c6000085042100d00510449602c054011800c690500c891508141d800180d00d02600c580098000b42c40c84100c00f0880040000341041c1281107900701c00001c3c8941e1040202c0203940413813031071409410b42e4040c122383d40c00069500801041c40310f0700294003c580380c1c1c01103110724000e00f4085005500c83d96500216100b8070000c9003c1816140180a030079410720882c00a000203691441c41c060801000038030502c2507085200707518445c4003c03558040b40c284440702c01003580c0c1c000b16202c00051031000e0043e4100b40121210001583d481509643c4101e510200030500036008442d0b5480c2c210904c8043d5200400480c0c02d180300304900d0205102503038030300b0b0007080829494010740c2c0c00c08200a00700300001d400c40030818070a11041c4203a8101c40d84940484404946980c00d200004a1400c0a405154030510700ca0242000c60340070f0409a4000a10612010500f0861a506d4034200040c1b84201c3c4000b03900306a182c0501000516154000c5070080c80007843c0c882d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 235251798 1106 235250692 235250713
    0x7020105030f0618040602220b12070201020f1b0106080105041e0317090d0f1d0f06120709030b070801030f030f14220b040b070b09 58
    0x70070300061003c03942ea95aa803003084000a41034060382c4603803516051100080d040704280400444040104901a40e0500c42c1c140a96442036400c0342048440070300140501002450241599800c01c42103562081c0500035010b00c4640e074000441d003a480b22102420340d40290b1100c22960b041c8024440084c000c600c407103c10442503020082d4004003801c08407071089103090182070300741b149010300c4449a00070800d00c00b102c60310b0b06c400743e45100c0f58000711800e2000c0b08505102c0030100c4d20b000c419180c00401038031201002004203040403074840300c4044030f0000350744a201080101c1001c01c10021102c03180d90b401500c5040c0b8280300e6242d501c81c401c9240b1080c00060030072440b400b00b040314074020b04408500c00c2800c00c000307440e0034440f003001145003159040c00d4500350101c540014400c966404803001d40b01e420030000d0402c0901d640e1200c0e0b6020152555145000b880c3d4841c = true := by decide +kernel

theorem cover : BRFrame.Cov 235071942 235251798 := by
  have h0 := BRFrame.cov_init 235071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 235071942 ≤ n) (h2 : n < 235251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
