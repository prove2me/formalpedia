-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1602
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:48:09.335061+00:00
-- url     : https://prove2.me/submissions/4b6e9dd6-db5f-4d8d-b634-9b751a74c9c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 287949640 ≤ n < 288129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 287950890 1250 287949640 287949647
    0x3030806030105070f1101060b03070806100309020307180e01050403031b0c0c0603020a170109020a030e0d0e040e031e0306010207151409040609020d0b04060f030b010308280c0b1303 80
    0x417000324820b00208049445401c00c00790021405403240c409240c0d1240b0740242d0061180905466982c00f8040416000703a160784280103082c045600a00101403151070000440b0047c1418481d41c590236a40e40c407a0001c50030280601400743e0f00a59010a0302c1c581c510100208440c2c400d882c0c002d01075080c2d22400051800c0340c081088400ca030500589907000710905542c014041520b0f84950140c880010a40590f550701500030f0f040e050307600304110700c1c0940b90641e0b03840349039108034082540714012444a00e802d4001c80210890340301500d086c41c03041c2d80302120b10f1003a010004011900402000350950341000018018040f4004184100344440304c0070380760b840d440c84105080e8100003281b5585403150b1704500018103a20f0000c66480b0721070382c4154000d0408030f80355032145007030080004900450a41940543c3c2c0c0041c0558034030703440c5540d00000c80d031000002a640b019080b410040031200d060701041030700c1240e2540c489440d00cdc0e14007880004001040d88504e541100f80207004a0b03070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 287952140 1250 287950890 287950907
    0x406050906090c090a060207030507060305060108180c0d23030f0a0e01200105160509030c01050d09080318010f1505010e010905100512132402040e010f0303080603010507 75
    0xc0035200082c2c80e4441910750103040c030450180b00c0e0044021540015104d500240c0c50003224040d80c140c50302e00703450f00030807000d40d00b0503a609070006041001140c51034580c40c019084101c40300048801c904014804141040c0d0b8140c4181c1e99a0001d0701c00c0d50386034100060910311001000007451400c100d010180e82680620000f1200300011411041c02c0c40c5d018140510401e47e0f0120707021007240003002194003a00c070484202c0f081e00c03540c0c0340c81036250303006400b9200c0080c00240580700700031100c001120b00f41c029000780c14005072a00c201101040c10007000314051940c9400d621405217910104e41c5c02d49000603440480a884c2c0121641d1200c040e8022000351b03402464403c64041c14480101c48114258225660100c0e92012002020b500000100644c400d40600010903a40d01c140004041e0b4030404040c100100c0c01d9425003240c4071076800311101400030310006050507224600040f40c0c000036080285000d006020a006254002d048a030b48684e045000b4003592514400c000d000c40c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 287953390 1250 287952140 287952151
    0x60c070b18040515041802063007181a03010b0904231006110a0b0601050706060609030b130c050f01020f0a110a061805100e1002010b0f04060509 64
    0x11008101c04181c00005240320401c108010028021030802c62050300f800134040c00038a100707624000030050461100b84003440c9240d0010310090402c56100d441000341150010017240601010040c2c2c98810007500c003850140c0c41a0355080d103070244079004003013400c3d0303160132500f000502d801c0310b44589031f400b2007168152009103e40351b80301c0c100f00001c03c01914040b103021400100d90091010390780c60803880c0714400c0c01d016410303042c0d1a030780b60810303641c0d020328401c0c00714207411045140c0701194206034401d03000007062400030b1802480c2c0c4c48200440d8020381103031000400302d44041060101c00e01e102e540041c1a41c111070340c3c3d0718041e528240341000c94840e031801101002010070071a0b009005400b80c604016081e1410500603113000307404103499880a51107208074a02c0890f90f14070818041e4080c1d800140640840c0e4100410031002d10250b4071720b042002144070310714495840760b14802c1604115600045104041e900070006402030002c000c034040c0d40f8003541008a596258409a0051f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 287954640 1250 287953390 287953409
    0xe0c030111040f06051c1a030c04022104030e09040605070201140610030b0402040f0324020901091202031c020102030906010b19030513050609062409060f0a030c0603020d0605060c07 80
    0x508241c5242c00704286d007298a203405902c1c00c40300007140d480c0d45c045103012400c2101590b0000c01008108000c074000c040b031592a5000424451200a071502d0140341c2090290038032004221009000444110301103800721440d079160000d00242035024050400c10341001c5040b07202910700b00003c601c019120480311010142c44e00055038041d15260b0440d0040d004500304150f14a03100d007005142030511040088a011050f4410400003c1510a070351142c06e050751860364403454a1050780c280560114145d134940202c4070791003408c4016001120103005690005612481c003c2a0385041c042c0580c091032010004012141d054a103c2100400800c030341d050004443d110b8215140031a020450000e00314400c030300c1800314030600020f4952150110b20200b03000c07142c0c04540085032401034107125030000725900101e01c0034903140c220381c9003408010b4140018160341e80c542c1e8000700ca880e4805001300341d000800c80014071481c082c80010b040180e84880c58030841c40300b00390361003840d88200c58a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 287955890 1250 287954640 287954647
    0x601030f02091503030f09010806030c010c0b0705210105100903170a050405030d020304030c0f0812030a02070606140a0e1902090a0f0f090506030a0302280203010e0c030111040f0605 80
    0x80744030900300300d05004009011030b521006c0742d101003035007980012078840c04520082e000428501d80003400400a5106a41d15403100180b80ea6089800c1000760203882400320500ca01180e100e00703030352551a018900f00400500d549040d091042c00c0e007118071030b1410845054010b02c017103404150420728a045150707503180c1d1004a03550840d120b0185420495060241c1c00c00e2210580e400030141090780d00561903170298550361132100707105014901c114802904100e011090741c10b5410b0145601c00d08412001d4a800c0083e0360300d404a88454010380c40b00d410910070400c05041c000300d0382d8090100640c00700c020f0304004002c41c0c0346001d054080341c0034580002d51a085500c400c50388070010307d8000c00668506480e03048039150f1001d00d00030207a00600d0080021190b1400044520b0101c3d01600035025043c20701502000b0109218440d03034200721443c0d6203a0060710248500805044d070319000e410700240100805003541c83c2201c0c406200d800620044c084003450014403000c80382d960610595 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 287957140 1250 287955890 287955901
    0xc0a020a05030403050706090803160204020f1209010f0e0a030815190e070219030e040b010302040b04030b010e0703150e0403030f0c0804060c080c04090504020609100f09080601030f0209 82
    0x50450391200080c4680004240041082400200c100940b42030351141070b050380e114500d55540f40551600710440000b0010b1001c050700f0035500403c90041c6030007010f0718120700040da0f4618624182d801301301ca03030f550300c0030040c0c2508140b20381074a420030308000c0c02c2c0d28200d6440042c034440001d0244446071080d02a403034199540c000c25a4803a0564010400c1074907a610b14481d0100b004861080c094001c231b141c01042c5043c0c500c40310710440d525440fa04185000401400010001d2030301003410300d40d08000103c0c52045000181c001140710b5244044150b042c4bc2c490079108074050121010315080040303c0c1200d101c42000c9030256000c514510785560303602d0504802406c110450b00e0842460240801241c46d4021142881580202420700c810308040000b00c07210801144e41c240011020311041c00300c142117420a5030000e000912540c20701c5070344400280b194003240d4014000c58600f050201405400000c141c0091081002601d074035807441d00c03005904500e0074002071065021000040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 287958390 1250 287957140 287957143
    0x30606011710051009030b060a05150c2508070b040f06230307032c030a0c15110a200709020a1b050322180b030f151504140c0a02 57
    0x1d0040200400031320303041d28500c00140142c0c005000541da60480c2c040000c041d0f0501c607086408891015051140001b6900340d0b64801d50090100701d9824050145103060741710044c4503002c4900302d040d443c100b0661900410360314107102c96100d11712007034091008116084c46030420008548250a20384c86448038a441d180001e060725100311110500441400340e0568194800303e008071441f8140c03400b196100c0e0610f014041c1d9805a5030b4035500821040341d65600ca8201030801602c11401d03000c015180205080c203881b03d24040c0d03410058081350900c411a4088480c0c10050010142d11000026010065482d0354181c0211111307203070000385980e0075500c50117040c2d811118200100c4140d043c00d19110b9240d91100c0c82c44d49000b8007000b203e040003d01001c0070310403111100c4100c210030900041c1c2d01c01812583c0c1c04280d05000300006c8a0400c00c0c10300a1165880e0118201c0701c492420111801c400c7c00d0160f0814052841c0c13210112054440740c0079140c00040882030261038003080740b0100d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 287959640 1250 287958390 287958421
    0x30f0f111e120a0f050c191d0604080105100506160807080f16020102010c090608060d050a1a010f150e0d0501020405060d0203251211040b16050c0306060117 69
    0x49008884803403c200d911101e40e808400074190303400d030500c61515030541c0c08850b4010440b00d81800c003000101d030015030303008054a0340100045c001000421a110300040c1c803581190340030355400e035110307010031a02e881400d007041d0140604072011424420001400d103645c0c0801c40008104040001e401c07410300122105075040c503104450143c0e03031100c040714404603043c0f031948220301660800c104210524000d43c5500140ca07826a0346428555540007013142442c0c400c4400c1d2014010b03000c0403408110a0603640c62045a1600402201d502d42080a0100314407a440b414505018540c85085281d01a1020300c040c0d6040b1600c40302c40c050390418a0080c801c0d548200c0c0d0040c03001071403400802551700554450304040c9140801c07417071040e6400e419940700301000c00c005104200700c00008801d5a000211180f000c114481c102502d0f001000940e1b400b00391040600d5000c8020501040b10401c01c040741114150054091820400006030080c29440b00111403103050b403000131810308000260 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 287960890 1250 287959640 287959657
    0x1504031d010318030c05060a2009210607180b0405041523010e030c01021207060b090403110d0e2101090b010303030605091e040201030203090a050d030f0f111e 70
    0x34a820f80c02ca510707001d414003010140480d1140513a40c00206c0302c2610344207649246034042da00c2001c0030009220005680d000d10049980015907691010110310300841d89159600b50100400c4c10b8148510040c00b20b40c03000f50b80300c0f4064040c0ca02401085820000e440446009032008101e041c1c040d840d40c0051000b5820081d0090915402003c2c90420142505607185003030301e947c40400442c01c1416102c1e40c03040c81060142c0d21040c80040280c000d00f008001450160500003606010392002415007001501c05a000410b401c9031100c00800902400e450b507140c50610003003084944001c144c840c171221741c1c0c010300001c4917103c14541c8502900320409095000f4086601d079a1a443e0140041c6094000c160040320301c4800904800c081250823100c3d802d040502c20002e9481e0740c01100a9800208410100e00940030f1b40d400168003084569107081c400e44000c21101d0101081d0303802ca41440c403500c0c074a1424400f85504210640d400c880c14140e02da0807403441c14014048031909031140200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 287962140 1250 287960890 287960921
    0x2030910020c12010c2003180d0807031218050d140c0102040807080c0102030309060c03060a08030c0606010f17040b040318060f030b060403021c0c0914091504031d0103 74
    0x80b0181d502065102c00004a803503183c45003804610306c808204440040745035a04e03a4420480d8a45100642c032000d10380000051042080010700c0d074404040340c00000084000c14a0341001d801c07000a070340500b4040004d58030320358841214a85507903964510092651060028900c244c0c0c101e00c04020880b0440103a503c000c1d5603036662000b14a540310414460848507000740c0701d0f0411558404000ca0380903032030102c020522030301c5082b052156584003400302e40d803000c0700c46c40000d0709010501c064520039a0030405080b0616004002500c000750b00000c0300e0402180b42c85507840401851441600150010302410301c554541c502920b101d10340f0001c81441d58030703401000901e03030790000703003140d000c1c40980e401d1044000240c1805014000c900002758000f505031a40ca01d00c00911b2810883c160007052042200d0b643c0700010822034500d11884103240d800141000482501040b20503200451700e02415418982600d00905008040000701d001d011000c1000d04c450b840b03034114110300c0520b0310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 287963390 1250 287962140 287962159
    0x601030c1107030c080c0613090b03210a1107080d110709110309070e070507150b04060605070c05030303010510350f0a06060509010c02040f050903040e0f040302030910020c 76
    0x4000c42420700901c502e5001b480303841e101a54038141724040d1000307000c1082941c000030381030042110260185442003501440754400d18030040100a5000b00c9003544261441e03035407401c0f0b6a005001000491403841140d0100074200010000002c265100d1500d928041214100c14114241050b42343d611410036141418020419010070000460190a80c50210f645050f503d50041c0041002120a000030500600c402c2e0080384801205660569070904002140c502000000d0126000c58010f0000684041070340c0082000c1403502d4000352504070001c60a640c035000019240044030580742c8200011070010500c006005000c0c2070b5840d906801052102d0030308090411041c0703044540341100844000450341d060801c0c41740c84203546107641c4580c6048074040c015113035076540103400c030781040c0d4504120341c0b40000c1d4070826001d02070b000040c564035443c26038204550540a0032150101c035060061000003600041102c1c4030a00a4603000d202d000780b001305900744034415502542189020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 287964640 1250 287963390 287963393
    0x10121e020301030812070c03090b070f1b050f0f2107150e0a0617010501080c0408010513050c0102030f0904090f020d11010201060f0305070e0924040209010911030601030c110703 78
    0x40041c100c51744400002245d03541d00d44204980c104440000540820b0700203074180160741c0000010b004540c02809429140300c015030b07507118040304040780b008030309401a000340041d14080100721003910003105d00d403080a0341c407070000c1c10101a200040f580c05400b400300e1000c441d800d000c9071006245108083d8a5200b403050b0203810581142a071511440d00a00c0200e100c03402400c2c00075025180b44148038042e800c020041da583d40e0050218150890b09100000342c514090148c00d2058029501003111035003e840d01c0c03441c1c4518a42428150f402c140a00c61542c2192029201d0a200c110b50200d02c0021a04180c940700c070305158040c2d002072940500340c06121035402500002002a8002c000c040d5840c1a021840c6042d4080104660010344040180114002003203070004120340545810500030704000c100080d0140381c1040b0040413004220540c80c003c2e0f600d42c011b08150606121203002505054401e02c401411541415503800c07032800314610800518280094803002c50705040d40303a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 287965890 1250 287964640 287964653
    0x1020f030606072f0108060a0b07110a08012309010624090504090809090907080a0f05150117070503010605011b17270f030712050c0301020a0801050f10121e02030103 73
    0x206484d0300e01082ca10030200d80b85041100040086580144205040c03014545d100440e000050340700990040c008a00451160400e100b0040b5056507886100600c45901032800c00d0700074003d280754016490140308001c030401020450706030329031000384150348504150b015921031007203410054100b840c1628150030000914010110140c0481c0d80100c13a6982007102640ca046a0080c81c81c180c21032a19500011031a0780402e00756446070003a1080d146005131098100d000c00d0348183c1881141c61030f011030250301401440c02a1030300750028000181010006000d51215521094144600c68010010b0002c00b15402505175a0404120340c0d0349000c0421881543c1d100e880c02c80c08007582d44512030140303000e28000544032000380c040c1c90861300d45a420342c403904145405541340c1c05910011006580c0a03c028205130030a512180125418103040c1300002400c070111901400445011180c0540c00c0000408020b102d118049401c1802e10607040c0383d40c600d0540460b40318000300020040065 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 287967140 1250 287965890 287965973
    0x102070614092a0f0d0b2814190b090106030f0c0c020f19240e100215060406030c0807080111070c0501141908070e0301020f03060607 59
    0x1441002c4401079140000c1d21401145a000c01c2824083d540b180d81045080200300d040d003103000180002030078450b68a03078403e2207000711006100c4000054501000f614155140b80c05078941d0303841080802c400400002d00040054501451080103a00203c512034660b04031100c00e00c03000d0b140070041d595600c1c002e00600310b82500c80d403d160400c401400c0aa105005a491a40c0c0050180d525174020105008080380410040c0c45501e040c14000316100480e03505a010803c5a04d0700003902d1404040000c000f0500122058441c1f418030202400c00c650001d030a942403280454860b94a80f10b0000184c0101725903030000f41441800f6000250030140401c56030100d419900081c0140b001c075006011b4548540c02008080c0d026051040c002c6511500d114903400032014101e515011261100c40c15821070316600d400082c09070410881074551040001101150541c000c1d4100f03001a40030580c06d020041280f40120702c045600820300500c0c14007400010f40d551b60089070030941d489103005221 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 287968390 1250 287967140 287967151
    0xc0f0d0f23061e01091a040f031b06050a08040312150909050616050706050603010207060207060209040b1203090d0f0b0f01140a0b0403020904240209031204050307060503090102070614 81
    0x40c0320b00411032102c04101e61050f03d480c0140d46290b900740c10003000702c20082c6900c0b05852244c0381400301160303030204516481d01031030092460001358103500400c1440c450590f0015001c0203424006540019002180b20743c01540c14107080c0c2c20340d048004d01c8002070071341a0b1962408000001d000072142a154844500300713000300150b8003680e0f1001030784843d00c0b0904c95440c0002c0c100704156004196164402908280c00800140c508003850326982e043c5e82054a054503a5a070001c2c1061080c985882032203d030003c00c4c1c2d010411008420215520790040243ca50700421041c208001002640001070215592080e44c0540606048903011020364007405040311000c00c082c0102c105203496003062086400c0c80c04400c1c41d00e0304540c00c2c0b11003204090001c89844107100038250410404281446806003030b480d0050321071b0445820145031019a40d031400c28a0070800c02401740d0b4802040d0300040d00c00b04e007085a601e480f45c0c030f0034500a05c5201c0014020f9071400140400c400540281e090058 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 287969640 1250 287968390 287968399
    0xf0e03030c0702030712021c03091a04090b040c090504020a030906020f0c060f131e05101a0402070f030c031b1109010605121f0324050c0f0d0f2306 65
    0x5451b00c00340c84101042110281d40320901c3c50450b1000e001500758441094071030315041c14081c1ea00c22501d600f000c4440c6640ca0440720124042c80003c000d842000000036080b40c06100483d06040003901e01b64450203440c0c005ca030005040c0380d10380d002c2e401030314205600000c2150303262002454224903412040d060580e43c0076510100e1150303038404100e1406046075031081c1105414a9903500b40300d8440011140c440e851440701100461818408121842442071012840082004581140c1001141d6042c80b031481844040c010940340b00003da0806d071316003004005190281030580d64244c80e0b040b041640c00d8102d680404000c105081030b107000c8415a1092a241d0701c3e000140c03464044d90f880b10700d100040307030009000c11243c0800001b4045c00a91611045038a94503042021095006c2c1034400ba01c00014038010303034056110f101c0e8848101102182002200040f500b103a110f04556102031645911450f903141203580d004e00c03407280d41201400c2510408072003000c603000c0101c81040c840d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 287970890 1250 287969640 287969653
    0xd06030b0a05182b0306080a0302010911030d090b03060301021324030509101d0a03030e0d0c020907050a030f05010314010b01050c070302060d0603050115081c120f0e03030c070203 79
    0x3c0b00021840f00100c0e410b009602c1c5031680c2d100813041d100501c040d00040548656002816a00a00041c2c0001c2e009500115801005003001c03500511041d64203400399118656010000b9031140010090f1420b4044495407501c8210000380a809010001c00c1c03100c60b5510b0000d507881000c800885284958500389040380c0914400b82d044035021100b416068002c03000c00c0101c0e40f050781c0306407890179058804d2458411440803a03840e01860b454110082992024020490310b81000305685100542c07505822000c525800700320700000183c03010003401400704504400d2402034000751490b032006401009950303980c0c00c003910440081080c40b445c0394680080c00c07029512036000c0754444440040101007031ba02e190700340803403540414000050130b50382d404040002a003c0c0180002060400000054941403058940c01c01e82404407159060341d402d912030100301c0c2c20003201c2c0324050304030000142c030a42c22840c510203800d203120a0b40d21800000200b101080c4030002030034101e4001c0d000c0320324 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 287972140 1250 287970890 287970931
    0x1c05010f0203100504020307020f010203070f0e0a030c0317090303270a051f1103032e0e0604091e06270b040b09150c190206070e060d06030b0a05 64
    0x480c40b06a403910450203202c0c00038803079414190011600a0301501c125071000d038044291608a07001a180d1100081000e90f500a825a1254400c035180904840146589145581d449100c41091100604e02c0c44052581d8a04642d144142d9203403d00c0501926036505494181c02c00c066541508281c0c5403090084200c114241503556406840c0c01902e034011b20341c841c0c9001440c00811012006c100558401d141036030103007e00113035008241c0c0040d1001c1d5801c2d502d000c003540149043d4200c908005481041100304140d0a186420184c15100000c02d2443da0502a00e00d20950400803803c400101800042201715400b102140c50526030410421440e0140f0f061482c44154000d480c08800b0350219000c102210142500076140000b111100d804185d9280355042040310300400410002c10103504001c00b841c0c4003c0a52003600c003078078240c500014041d051346e000110250082501044c21015034071076502580146400081804480c07a01480a10107024211100c078181c00404500a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 287973390 1250 287972140 287972171
    0x90f08011b0311070c120302060708090a0f080706021201050f03070602250815090c0103090506070c020a090f090c0b0f0406050c0102131203031b020d0c060b1c0501 72
    0x7100c080c0061440003081034403050071800b07800e85490321070400604008420020304a00c074868020f002c1105a00c180354014100a403c3c040002c003030780b041c05581801c110074400080381031640c903039003c0c2c2800c01d000d040c4d0506298502030302c000100074a10002e0101001102c00300414103d8a04480d07010b041001e480c20305d0780f981414812240964802d0501c0401d10700228052020500f0070000c900710306a403403511901d04182d14404403280300b075040510002c0d01c01031118400440d8282401c0c071960505948032650dd10004200500304107000303161904640c0c801400400a14040105000c500c000030751840007002002c0d811190640d00110004421310158240c0c3c00303180d0a8000b841c1041e00c0d242e425981640700c0d60074017405550030490709001038a00c1e010b81e07028190001003001484551703e80079080300ca04001e80000b540c0407008080d0304540c00a41c01078480c0c19464503004500c003d107171140103050b18031140b43c0d1264030b1550003140301c1c800c02203800380c03107000340e009021140c02c005002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 287974640 1250 287973390 287973401
    0x40905210a090603050a11071203240504050604111b0c090907051210020310031a1005041d06090f0d090602070302010c0f050d0e1009081902120d090f0801 68
    0xa001140d030b004410007240e4040c3c2c3c03016a20100c02c09011456102c603a54511807940318840032503940304104803400c4403990501c280d0400780e580460301d040e900000529043c002c406445030501c03032030700d1307400141003510303190480d440c092000802c1d9a141ca004042c0c1040500051a801c040f600c584048403036240f03002c458160080b074041c0050400181400148013071240c19a43d00070180c811603030228034110f024402548502c210000c811441ca05600e407410025101640d201d030700f401d100c1c081c010400810040101100c00c225400140c10300c10b40042d140161a208035144980038440411030100c90101e00d6100b03210042d403c2d505041c600b48000c0d0f4181c1254007411006902c00c2c5428001075000346020031906000301546032100c421a5540f83c900820320965500155580084040034280700261500403001414034903d00384c24202404c0e6074a81700182c200c188508000340400f0354031101141c0d042e1060803000d40f000b5546200001d014a10300348940a16030001c0c00002880f00810302ca075 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 287975890 1250 287974640 287974657
    0x1140411270a05130c0311011d030d0e0409060f0609050606030103051c03021b1006080a170d0e0607020109020108012309040c0b0408011508030412120c0204090521 72
    0x2110081d480b14000c000090100501c551500008540e003080465800e800d5a00118480c180041d5051802000104a0341c1c03850400401d03150003401001d800d03500803d003a62290401e20304026042240303000500601004103018092502d080e00030048002c0b60342141003625071215040c03090341c581c80c061001c0da00c4240300113000d80e0020070800308a03c0f00b10000c034492044a25001d4108412080ae03016002400c1880f404954001504010120114080d043c010106a400b620540082d610b5603260449222040141c80c400000e130100e4800746640502407880300c1d41c1c2150040e1621100c007a000709000744040e40403d03410300000071248007481e803007007000807041c50b661f24480882c018002441300103001102c030795040100118264200360f019000500d544000400e0040040f42151620040c1c1e4201c841140c00400042c0080c0f0840030201d18100d600c010002c0070b00840f044111880c5028250095000d81480c40790307014808000742c1000d1003010300c420000c1070310020141c0441c61046518 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 287977140 1250 287975890 287975959
    0x190f021803122106131a0117012d0906080a11100507020d060b0910030b010e010806010b0f040807180b01020d1b0218070c050f031305100201140411 65
    0x1a0721901840f00c5441507007109024050f50004031040c1d90030303001c0e070714001801c0c1c0c0b00130685801c0d41c01c84c1da0701509601c1c00c520107200c4080b40f541001c40f20b0b034007507400040311050340308034500d44482c10314059004002442194020800240c0b181c842d10344030241600240c8100340c02900c41c10a07440e160140344005c2c1111744911380340000c0e075401d02c201c0d04070b100c81c2a83c000e50b44944100c8a41c0b01e0000700e5100e000c1e2084010320325411031074000840740042c3c01170012614910f006202d140350000d6400e040d9404039003820349402110112070070910407074112a0043c094500001450520002200907542e18294213020b0b00703640d80c00483c1d85007014801080010000c0c0b03c2072010f880358801c5520b0030b85c00034250481c1e145218841079410b20083d286400000d0302c18100106210092186141e0419504040c41c0340c0310303020b403900030001300ea8007a180c0f040d11020301c0c0c1c110090003584540c03001d28414902454514090400c0c800b50200e82c80c040f809203818482c075114006803003030340825040f200700b03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 287978390 1250 287977140 287977177
    0x801080616051e0d0504081e03040b060616080f0a09050102011a06030a091406100f08070605030c2214220b0307121b0609050108190f02180312 63
    0x10302824810b07030010b508040f003401009418101c1d0002d005030303842503004650301a69078050482240310b0070342e04e034200c0c100c106c3d050042c480060000543d943d08840c0c00c940d401c1d11000d103d85842d8480c802090000e04402d03000841207c2030807080068074118049440d10520b850b80e810043e4207942c0c0d907402410032521585544035681c600300d000345400c152641d0700060300c1a4183d40e00003201542e80d518400c240e1000007004440e40c820301b2a40c010703003a0910803c2141b4500121540d071240b15016000900c503000c0001545a018041618041600b600c142c4004544034142100b201c003450180c043c032003401c00d4001c02c071420000ea0880c1220384001c4000c0c90820303189035032002064100521540350144880001304088010f001d00c102ca0b0055000503203420801d600d10300c80c100d00c2e03071025051041407030302045aaa0003603007d95100d00d040c0300d0740071003444141c1641c004007030000d16866501e00c04161301101d0120410081074088096044036840c04800540514070301440040d1440002c514 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 287979640 1250 287978390 287978407
    0x51002040b0d050a0b0d1505011a07150212010e0603010e0105060a180905010507120b030613030804021504080d0212032502151503010f09080405120309030d080108061605 75
    0x1d62060354495403003a40050001c05c020b0010341c50700c901400039a044070b02a0b0402e40440b41c1882014018520700028112007401c0d0650314100c4c3c043c41401405410050305040184107041d0100c540c2100e94600e82015980c5414520308402c1c81512102e0003503192014107080074a05204544c090840103000c95440c61410b40203810000c10140c0203107810380c65141c4a40020350034046d0368040d000c04d40310080c0341c103d00d00c2ca48048030000054540300782d0020003441640c05581c1c0207a030741540c052401e203003140d885002068207210102c8480082080008000803680c1022071035041603842d45e0300b03586d0206840c0340d03070300454003083d51065400414515902104401868030b05002449401603a8414840070007181c42d180080f50000c100d00b05108107850503103004e2040b00e00a00100200f0000c84840362510b104e1030149010b894010160b000f4401240c01c01002501d0000400500711401c000d140d070002045480c083c07240d1a0584200f50100301d01402c4a040c1c801080754640d41c0741c0c10040745 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 287980890 1250 287979640 287979667
    0x9010507200106090e06090f0a02010905041d0609060a0608060907050d031803050703030906021b0609030c1519050a0f1409120105010e0a09200f1903051002040b 71
    0x1d061020415942c03071a0010700f4000b1800750303240800d0200b0190029291002085050911520440c1d6094205140000c0140e8008a42d182a1641501d002418031b0040032a203e01e086c64140c0a00e20748a22810416005070010360035200780b840c03400070f2251554509041c3e1340c2c1c0300b054998074440c0d0000e0000b4002c031301300f0442070080103000c1c3c6442c41d02c0301d444a0b4a12140d080301d42050365140c009943c180145508248214010022480140403041c00c1e4500c145803001381120440c407800c1c000480d9401c030380c1c2c100019044010002c0040c42c00c6103c001103d9803652103114282c058107000f58660104c0c3c2c0c024001c0d0b40c1411916102c54a0440000b0b20440c0d055080360030b06900b50409001035003e83d00d8000b0744220030307940d07440001030f20b5061401d00041d443d4010b0030690020b0410782c1031300006091803600c66283c6942e1202e03141440b1500b0006240c909034048194000340207020208034207210079846000c80e40a501503403110b1340c1d01da100800b0303481503000301c6558980804c4241a030002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 287982140 1250 287980890 287980937
    0x1202030106051005030103022d040b0f10170a090201080a05100b0c1e010c14030a2003160e0f120703020907030f0b120a170f040b1209010507 62
    0x4010000501d09031a800064200d004403240795000401c0400140110300b0b201d126803042c44014072038100d454880c0000c24000400b00d0015a0183e41c840070b00281580380d00c2c03800006035000600c07009180b0701c1d14400500c1c0c0e042e40202c11000c000c1000114010300390612501104c940c043c0e40d00c118603500c11100c68007800d4054900400c82096080010308403554030302904081890304c0141010444c001703241036504c000800c41840607490a1001000ca5400014400e101c080c003c0d8030036266540d03010b890000300f810742180710709503900c545003107a411403c200852066140140703094889205840458801c88041c050b541c00078000c810b103004503d4018568520480c0c414100d03000301d03031240e005c1522550107407015808241c6441c0309541228140c000d42562a02c20342e407503902c0210002c0c98903915410b03664081c000c0540c10f400859509804411103240a0341034144c2e03a1b0b80d0380c0c0e6003402c060b950300880030822100d244502160707407400180138590013860340b507880b01800c180c0039200703040d40386 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 287983390 1250 287982140 287982143
    0x201230d0f24030b0942160c060e061303080f06013905100c020f071e0f030308100b090d110316080a050c10080106050702010c0602070c03031b03050412 67
    0x4150204020b03441c0c020564880034949902070003030030052010310b070014240c4610490268259005c20002d000f01500c07c50300001d4024641100c8110a9081840c0184080460307032240d405841b041140c044000050300051034404d03561a243e0703030b503040581189450162182c5000854072500303408a5500e910000595103400c0c0c40c8018003ea00754a10440480c21050450b00c3c0c0c1c010162241c00714150f8851103a10085500180c5802c0344280c004685902050049600e03500d2900203840300040e40b0401c20010b8407003030b400c0e040019102d06004d065803000306caa030b0865100c0c01101048a03404003007540c01380400a00580142c204030b659000c0c001d07038081c0c0c0250705031042542848008502e0a803040041c81078201601d14001d403424038078104000400014016010280001c000c1584600d800303045600c14038255071a1034640c40125040c50a91b4000380200d03002140c04014010b650381c4540450748280c8511241d51407a251620b04542c11000140201d2012b0104000e541030000ca0550b449 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 287984640 1250 287983390 287983393
    0x3101706060607020a090218090c0a0203070f0501060b04030f0b0c07020337060b0307060e06041e150503060108010501020f0d050f09030109151401120201230d0f24030b09 75
    0x119280d5601b0012a0484183c100001000d84050032860070076807a2940c003e41d40340f4400345460b81041e0082e6403840760f0751000b000e01d4608268041405800c1d404040508040c001c016581d03039407410000003c0c822004161450062800402c0b8803640c48411175291a9000e40a40984280c0400c06400e0b00340026401e2000000c094038807511300c00c00540c0750301513071042078001110b4400c0b0b01450b18240381c81e003040052080c0b0340000c20b450b03130b12882030b5012200880401001028000081c40c40301030290301c8802080007008035500240e4102025510444007aa51415035a90740c4004980c1c2d04900392200707403103800016080d10406c1c445d0b13008010710400c101020f46400c0014011908540080d50240c0b10034a0241c0d41d10031111050085c602c2c520748114180f2425410032a2592840ca5241e20083c1440300485600c0103c400c1e40841c0340d9814000b0b00700c240c0f1070740454104005010340ca012074903084d240c08141001100c03500d240785240c0c1c000b0380d103070740f0640d0960f502d1100c2007030041c0c081e290a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 287985890 1250 287984640 287984659
    0x608160608071205070207030303060504050403051b0109050a080901020d090b1b030408120306181909060b0405070810050301020f12060a030b0a021b0c030a03050f040801110310170606060702 84
    0x2e1024900035517000c2e110b198000d203c5240385080c0282140c0702134008510540c02d00e000d100200768002c0944030180fa042003091301002000701002d0041c144118000c000d0700544070b201c0d062015000c05005140310a8080e50103003d103100b022030307800030079010b4100c0c01d071420701c03000299940c2c0703125043c8600d40c4441103034a460f403904026403801500f15610340d98120000104005c509180e40c8190321200040030305002e50600c00c807003080f5500c42c0c001111256989540071002c1c400e0380c0c0c011a131341042c05801000035041c5050300901c2040f007210b011000a061800005071418140700b113410000031001c0c203078105141b200072050480c4000c0d11240c0d00ca8072441011000c9141e18107403e000f800c40703460060340c0b84800c0ea110f90390b604144000c00311980003c135600b00700c1d8402007030043c400c503414506181e80d294034152004850049030000c0d84a50710309441c42c0c1807182c24800230760051416040d00c12001c4c2e46d5100c82d1044126000a94159400101c04569135052003c0904592407000780180c52 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 287987140 1250 287985890 287985917
    0x1906050901090507090e160804030302040b03040b06010306210b0402011707020f07050109081b0105040f08010605030f03030402150c01110d05070f110a020f0f09040b0a060816060807 80
    0x281001e800141c0702d00c2d41c031030500c1049500010300000130551607081009501e000e0005850500d101420f0900b4081400001020140302e541210b014010600c1c0303c6803a420203041001e08240c6c00c64050703001c6841c1680106030031600382d4060249854035040e28450300226a500861010050402c03418444150b00e0f03042030006800005215070305c85ea00070000b5503241403840c0d04d40300321a844941031001c6a5023b108442001c62503170080c100e800f065080c19084ed4004075030134801d650144900d032880c1e0001154215041d044001194030031400c40314210703c031700040340c0c6911081d43c00a41c003200e03400300c1071030800e82403020f40001491140006510300702c84d00e0140d940c1e40f000800c3c0c1c41d9255140100205160407010000140b1410316003405136075011010b25541e90020603010303108000c44d108002c001c1c0d81e032803045400050098100701440c00c2c14548079003004016600c140746e4505103500850300102c0010242001c00c400d501316404039152820944150402030048c0f420407250650740303075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 287988390 1250 287987140 287987149
    0x30a02030609030d0506060708180109090609150b04051f17070e01180e0c090a03020316030311030a0905040c0203090a060207090c02031c1805071404140f190605 71
    0x384502c03111030245035940c05910700402181c1d0b00600461095406001a07804545610103540241080b4810b81101258900059030365607100d610200303045003010008611380050303411403480110b00c02d80d041ca54644a0141620902440c0901900702c000401068452880080200d200c0d5805060403100140100490148100200d0345000810a4610310080070f590181d801404021005803045200d03080280c4181e011801402510310301c140400c292400d07540f0032185500555006007115512400354207404606c102510082c3c1c08900c100680e40e480702c03c08021505a019a03a85951840d8100300400005003010350341107007140700501840703205855000c600006884141c00a00b02686042d108405440303035009408111340080c0181c80d408080aaa0310100301c0500d03030040b490440050548680410741080940f0728400e40750001034541c000d081d01d07035541c00155000d10011f00c121104011215043d5100c01008204100088000f40000e003040928032240c0c40c045402c07a0b9810008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 287989640 1250 287988390 287988403
    0x7080f032a03040c060c02010806040506060d090c050111160504020304141e01050603030408120307022d0c040c0804030e152701030e0703032f010e10151202030a0203 73
    0x340c2080002080c40f05010103d010b00b0010b00c92490b200c214100b660340000c08800700a031860b4000ca840d0f4021408954501082d21000c0382c02c0e103400c01000d0b1a504243c2000c46491080310b01007600d01341e40c9030160602107400640c0782a4101c080b64840d04d4401404005d51004005407046c428040c110720320a04240100c84004070380061428260040340c0c0b4a43c212076018040610a600800c0308001e110804030700d042104040100d0a0b840c1d949889040e400c3c0f14500041d0101088140c1100750ba000d280544408200f803070400316590303440d4160600089032091a580f0002c5400c0d0340004000902c620301900100d00c0207814800d942c0c42d410701171603054100c038110100314821240d405030040a05030882c138124009203401c0c46030390b4120101c00e03150501e0303000140070400210340e00c00022444143e40011108214081d038481c42030012054001c5c8840681c0c01708500614004035100350003400f544100c44250040c02e02042d1902c4020031000604c0b904c1207816015981007000903030b5050168 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 287990890 1250 287989640 287989711
    0xe0915130f0504060f06140f031510030b010b0a1d0310020a0e090a050c09010f02210c0d0f0f030902010311030406050924070309020301090f030306061407080f03 71
    0x1180909003898514185d5260b0b81003140190319240c0c00708240481080300040180c41511040c10014144011030b081c001142d01241102c07011209000c1012640300520b42203900503442c01865903200ca0000b506881055425000100c50702c208404100b402c240642c2c1c81d86008088a0b1141441110203041e030700a410307080c0104190910804a50500c884c074641e01101001082119103000c000c2d112003400350800e418100322220144800060007003181464a2030303498a4412070440260000742143c0c481c90f010011070090881d00e111050041c9500d89141405e82c40d103028003814000110010b004d00300041e41059100c143c5040c501341c50000443c0184e00480c400302c1d4500d07100129234580b0809082110402580180c0009140c540e040500d4000403907290100d019011303800064050301c0058005807440c0b0518000004054256016204840098654440550303488804120501800380060303c8500108054074043e000200103542c003403202c05140b941450300300e40b12a0360f46401c002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 287992140 1250 287990890 287990921
    0x20303060f221a031204030303050402060c0334030207060e0607060e0705011b0f0308060d0b090c0f0f010e040c090b04030602090319080d09051c0905100e091513 71
    0xd80c0b0f540091031000301c41d00088250000d1a0000c00a03c91000500c500d1002408050340e034001f1400b1035481c0000c80d19400580021291a0100c414182c0624060346000c94003010340d8050402d461034401c0c400f9141c203a05600546002c41c03500c6810344003100c2581d04160710010410411700003c07400d01ca03500220340c0c1980146156800c110000d000c1c0c02400b81e02c1c0c548080c043c0036500006192020880047e5414500300746240c80d0400823a01c1c10018000041c04501707418100b200030304000584001031030f011155241c06400c00028400809414034406001405003c1c00e181c0909241e0002210806c040c60604900c580d0303a44010340030381040e0000c0782c40b9500016190168502040140440100c1c44000e280c840320700e5680d046c3c144100c02d0424442070329412043e050140a05c2034003540707541004aa2017022420b400206500340070301480c2d100750034562a101c5054031031100100050b02c0540041030b103445683c0d460300b500200101107a4442111030120107010054043d505005d0031003030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 287993390 1250 287992140 287992151
    0xf03030703080f070507121d060a0509010810051003021605070e24100f1110090b0109050408070807110d08040914060307120c0504060e040210050a020303060f22 71
    0x203040580505000d0140c0c420000180b12071b0010032000704440540741d049040100020204150003070f543d070b800d0703207180b5807010012500455072034200f80145000c0d40c00340daa14040c2e42d601d58106030300c1c00183c040c042d04080034000249900740294002c0c01040341c0012203030b81c04440b0350b55151070a8202d8114100e012000c0040c084802c481c0951041d00800100300c4d0070103052200003041100c41c0d448003010400c001c990988a15034050325040068942c01c1040d41c513a2009810074401800c03120700c0c2143c06a65003000054403060512509009039030008603103261102c1c0e500e42003140d0b001020140c5144542046092003941c2e24101400102d210700401c2d611a458040031100300d03004224a00312070b103e05402c10a05a50104071102500c00300c40c041171280c0322504112120315003907044160440e1038418080b8440d0300b00e41d0034500c100d200700c80900703000e1000001191306000d00340b400c1025a0091021581d6807030260041070b070312000174003142010a0700c2e40c640c0868200018060341030f2036498 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 287994640 1250 287993390 287993401
    0xa0c0312020109030e091305161805041e1b060201090308070807120c09090e1b180c0306010e0d0c0602010c050c0303010b0f07080705070503070501030504200f0303070308 75
    0x103038200e100945940000c10504400791009088804400100b40c8107800c84c0c40040c4d6003180e02e4a1103110582c00c641200c084d804900310850100140340a041c8401e081c0c10194080003405014051040c0d60000601031010009840b03107003203c40c1664119a6495003c240140c42c4a0300c0003000014841a400450f140c03d9609014289081c080d10080800554004210245410900d4020320941d500710016880019000440742d00b4115000f11380c1181c10800d485503070241c00a040c172103c06100300c894030f034040070b80c2c1040b40d000d0449000b20401e201041c000340001501c07030051640500181002070f00c4a501c24000354040a40794000c0711890040a0103000a40c0c0c24420400c6403080c1d41040b07072030000e200072003a03941d000520500d0341160f00022606600704482d002d40f07242c0d580c80309405440d60803a1901d180c489004d0700440d03001c1d1084120016540d03110f07004490240d60840030111441c03041049104071440c601001030f0300080c0c8450004402c1e141003004012a034082d94030b44e981400d04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 287995890 1250 287994640 287994653
    0x504090519030c0b0a1b180906060e1807020a060c0201110703030212010b0f0d0f11040b040603050903090612060415080d02010b0301360f0606060f02011103061c050a0c03 75
    0x10b0900001d0520b4500c031b95600b07560310f41d038400c1c811030141040c41c0c549101c03540654076200950095802c581c14041c00003921604040681e003a80d0b42211f10b03116105c0300000880d8901c0c01103440d000142d004210142c0801d205520181106110784008246240d42c01c0c0e001609500404007100040d0340000e000d4903402804c42020701428491100901c2c015410031201080d00400c40c041b000303e5550b20070090580c489903c02e070b4200c2411440aa00e5940c0c072007024172541c0080c07241e00c001c24100000102c07000c0000c42214442c100080007035040109948509031000303002840c07a03800640c2c1f002c3d090314200c03540080e82c0c004e040600003041184001880203003920403400d1454042e0b0f0400300c4100091f28002540c6100442c141c11100103045059181855001c501030080d0070810f00781141000d0251a41003401510007584031506019142c810480c201d40008160035158401032001c52210300d001800c00c0359000302440c04500c2c001003910350900300800420111044e40a45d41c041081111 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 287997140 1250 287995890 287995913
    0x60e0126060c0406051303050604030305040201090807030f150209040f2007020d1101050d090f030314040f0602030c040503071211010c110625060e06060402070c0504090519030c 78
    0x41880500700a081000001c0514010381c01075005014010038840b9065a011140000864100c070407206581403504000d0000d110588040c1e001402c004000700d41c11000244110413a5444400c0302e004901ca500d6540e103800d1182105d940a075002c002c0496141d03a05d00405104120100300081c1c80600b07040f40c808008400d12041000700c8041c010f120240c0d940390000b080c2260000d190040038040310004803558400c072052001034603d00000001441811003003602000d02c60f0b141000106074040052031f03880b404580c000c0084811a0b1100300262141d0060740d04814130440c0941010740341c800090608100c2e400c4080036001e1120000240b0600f441c01d18220031080c01c10700448407682c1c403000d02c91442c0400090040d500048c50f001442c6004500100206402d441e20001e40b03060315008001d02802105059030344521804a00302c0c0c80c26200308c403e000d5100c3c64007401c06240c2000d000107014544000d80301d600410900764944d401949a4640b05131007540e03240440c1015207491b910300003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 287998390 1250 287997140 287997209
    0x1050906010501031b021e01090209040308010911030103080a0c2415090b03030a0309020d080c100f0c0c02120304090e160f0b180406030204061418100e040501060e01 73
    0x1014442da0840c5c0300c1d00440d21000545447c1c2c0009101480800c2c3c1c18003401506e14000c0d0009000000c0005042c2e105070114140c0e46001c00902590411502180c01c502080c08041c1011601704611000d00380580241168244581e03074a0032080042131014840013441707002458803030740343c2c544c03d511026007a10745009400c165608020080b030f040042642d81c083c0e10b003844141565051484150350b180303c41c40e50032680c0b100e5080d03543c1040c001002d850304000c009021450f42031031211802d001450042c3c2c0e42001080d078580400013550707001c005002f400814050041e000c10400402c14003042e000351101320390040b004051205c13905904a0300c4064940c030841c40007003102000c2c01401140400c640a500001908000c050340d54030000c0d00a0205038402984185007040c0000c600a0010808910301c0c0200c40344228421280400000164100c9511411071200c19040c003900c40d40004041d00316010b0f4000081d0244c45028841500c002a08080c44003030000d0034001440c2074180a844120 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 287999640 1250 287998390 287998421
    0x2030a0813031b1e0c05040e010b0f1009030503070803010f080c061804020c070906051e060304030f170106200102070b011503090606120c080303041709010c050105090601050103 78
    0x4242d00c000f004403424890321003c4180111404041c0310b022450040b40c2d54a054658084007503d10b022841c66106218990042e41414082420f0b90b406100310500c1ca200030b00701d8242010f080c410041d48408120303580301409441740c000300100f0070400113417584d14410140b1945c1d03541005202c0e134208003e0f500170455980f00d82841d040907200e0000707507200c0d0270030004495103c001d840c1c0082d02078007401d10300b02c449218250300015020200e400c00021500d0035150b603009540208001c04071540c03080c010b581c00500c20008280041d200316445040c0303c031249800c045046900003c1c0c40e602c2403c0c1d011000260300300318412141c030100c056018602030745000840c5801c00d1b503075401110640500c03841c6002090501c00c203200502a030059400301e58494000c1040a4903030b482914000601d107070954800f000c810b8042581d500010880e070103244c200d0707250b4102e00380105120146a0141804504000f071501388500000c85c01d0240c5402a000c0d032025056943c1000001012182d8031102d04850 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 288000890 1250 287999640 287999671
    0x3031608120612030f2b0903030f0207020105090f060702060d020d050a0903121a031f0c0e090a02180a03050d08060423040203030c1203190207032a0506010602030a08 73
    0x8440d400030464200d0120082001d03190703001d00141c00120b0305203031070b070102c09428284000c0c0a902e060380003161f2603101e80ca0402207208103021a4040f4010042c0080c0440c1c800c000311480303840e01c0000703c034841d00002c1c0120b15008035503001c00d02642055603c0e160940c1c000c98841d04901e1180210741e03010480342010042880380d40c6004040180b038000e000c13005030b0f9541c112102e82001c02c950544520b80581200c100304c9a0b03007030480c5405103c42080e12003030b2424642c8000c0c1c92007070034001d01d14103000340701d21655100c0c00020402940005150182c2281100e00c3c0c2ca0143c668500c0800110702600280c4003121844030302900e0310384014890b6109510342004405070180e0503441c800043d140d882d4000d003d9850b440440d00c0c5201e182c5085400d07208040d801121024100c006520412801043d822101072012040d0103074011141c0040126410700c4284003010500b0043c440345005004070704036214403d446843c1002000e80182005800000e280c071807044d00300b500d042d040340c58100c250b6107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 288002140 1250 288000890 288000919
    0x605030d050909040f170c011109031c09080a03090303080a09021e040908180a062d0e1002010203070e03030424050c0d05030109050f1311030316081206 67
    0xc28401c88258522803d00f00d0040750034412241810f000c11035001c0b1140108000b08100b90011f50003a03241f284180d82003900a00da80301802003902c3c1340140203002004440703140a440c48501c0ba66815030b50400410300310001e00d0003010001102000e000f42c41d503826a50560074014010b0000605183c02d80b8101841c02e40140c0300e490340340704010140307451070341d10041000c0024050101c60300054a007890200707614062021081c085082080c013228031340b50f440c1c0d070780c01c098078100000d4134440005000c1001c110111805061840c41c031644619017200410060030019540c504452040030050307502200700010b0640082044a05070002c400540c141071030512102240c0c00001550081c030907140c102c13040481c2c052421b0316148000c0b54140c0c0c502c07204905c0001c010780c1003485242429070800d00800d259285116289000d002121a4407000e02c8032a02c8501c0035650035040075170580302c03c00800703105501020400001c20322031003103d070359101c4a08284240b20b102401e000d00c80c0158454040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 288003390 1250 288002140 288002147
    0x12030504141932010b01080f1e150402030702010e01060603090b0402042703030e0c0109080d0c02061306030e071a04030b0901060b030405010b09090d0c020d050f030a050d0605030d 79
    0x1a41c40e4400691282001c0f0565000b041c0030401011141c1c08403a01441c4019850640012070300030400e0f0f880c21041e5441d03d2050781802015901d034804440d0740400d0071130203200003280c0b50303200e40f101070f5110401141d040800d040303900845282005075507400c4850b9040000303001c0d010042c071851405200c080d0b0360742c50315040300201810082c8515a206114a003000d40843d50180014030420019440001414082d02416410b112000c0030b001c0d501d0712400d1903024202d0242aa81c1080090441c43c01601040d034071a1b64924047c0c1c0c4c8500140441a040b01c11110000013500d080d035400302d60b40c40d620b82c0e120f19060301c94005813040b482d03840c030068ec1160b000c03056a04882c0c01c5230303058045858100c2200d0042c4030b00d80004d051030704004201720600c001504120381c004400d8a0040d1541d545428198403070920121030300014010110345c4015140881c20004000c0c069815100301986c000800c9186601840c82e12000c5100414580c203011a070303200c0e50004010990140200c0c07100a90010b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 288004640 1250 288003390 288003433
    0xa0f08010501180b1308010213030b010f0b0304030c050a14010915090506190b0901090b0f040b060a030c030b030a0c0602060903090f0103021c0c05041806030b060405040f1203050414 80
    0x910302c4200205e8107014001004924900804001c40210341d0340c45918006808020240419244049a20000030b100b03100c0091b0f050494400010b52801c6803601d40c8e04407120401400f043d512441825840001309031040d0b00c0d07598610030b01000040c500c02e07d1038000d1003410b0130f42100d04514071780081305010620206120307a102100c005805030444800348500000c0c03a5405403982c000c44044008201c010503070b401445100300880b00310301801c801504000c140d80302406402d411580c2442041d5500740aa0440c428654441c200403841c21081000f1a14000f01c00c5030585100c4202c05040040c0c5406001454014500e90003561500c506c2c0f0700410340d00a40f0304220742c10503074000b895041c040b9011751180f0991405141c203002e85407030807000501c07980160003580ca445a0f039400c801c01d850410701c01d10040f65806130b0500c20b0b030ba55110800009040061054400c84000b9042000040f81a003000a0900b615180061141843d080c00c91900007070b2031644039150f0002184d01d0102102d13580d903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 288005890 1250 288004640 288004649
    0x60512060108070210050405060f1302030a060f0905011404030e030d020c2e1e03090b04060207081606020a080f07080a0e0c120703140604020a030f02010201020f0a0f0801050118 78
    0x40182c2d81c8a1401c100e00c1c040031000112401441c04052004100d00401c005016100c84019017104e911740745950003001d655200c0096055211807100301c00140b0b0740e00552141485020002041180c1d51242401e507180d0000b0200417640c500700700f2082680080314000700740400da00038800c2c0c2c24802006551504821040c6110f09010481d40040f80708050804641080140b100701c401012500041e00b40400313803250300c100d0006482c070140300c00d01c01d1080d044640c1d04000c0300c1c00c690b1a261900700081d0b107d40800e45480c08100640c0e04400900d4990710368080c030800c40141e80c0c3d50034050040c00d03904090884090600168280280290b11828a980100c11220000344a4012000d441e181c482d090b05415041041c020030f0000044000c46da9004807402031000c4100440c0014089445000480e030096108040c48814004140154130124002d4410300005281c41620711110b582508805c032018000f644980302800b00b1680000e1480c014082170900d40340c2c0c1041d0805081019919008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 288007140 1250 288005890 288005897
    0x70e01180911060408060f07020d050901030e0c10080a050a1b1107030b100302030f1207030f03060308130315060321030b09090601030c0f060e010807020c150309070605120601 77
    0x340400e229000e0146650b01c2c0303000b05030b0355440fa61136240d1511600101d4080f003888078240c00080041d400860703440d40c08240d940d5a54a402e01d04401500100032159040d0107620900c1100c90b281c0d00c4180c0c540107094904d07200c890441c42c0001c1000103544004110110050504ad66507455200700481d200701545203050400181400e41b81040c03900c42070354070180ca103da200b418049400400c1e030744075042c0c038001e8058030790106003058010380c0c3e00b841440c07014079a081041841c01003803084180d038050011a00e03020a82d10342d01e89640c0702d142c0000e401e80e400300507a0070041042003070518008111035040041031240034a1074807104841d450b64048182e0a0b02c410031202a800d01c179900100c41c0f90001010041030b4140318480c40e5031010240001c89000e89404400721742c5000c80c0c0750030000c980c0c41d943c2d900b9080081200444200e400030f400001944500f1050111a903140c4103240c1c4041b156100d9903440c1d01e04141940c1ca006810361040f002e019080040402d060001143c299200c3c2d42804e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 288008390 1250 288007140 288007151
    0xe0f0f0601051302070512030601110106081507020a17090a0905060d0602031b03040b180609030405150c0105070e030d1817031210060e0a060c060507021e0a05070e0118 74
    0x1590710041e114040300105980a41d04046040da1f0342000658041e01d400c3c0e0300c0c8400c1440052284c3d080350110302a0001c20340c0000300381010380f40d100f185158004410301c1520384075045075403203512170490140c003000050800318100305541400c40d0414010801c01406022038101500400d10700d042d504000f070450340d000000100348404110000e110091001507041c1d4078035090410491300d2009513581030103c403074881c002d540b81c1c80000344a8080c8079400081c500d041d241004201340b100b10454a16905841841040e825600c02e21619100c1d14080e215020021000810142003010315041e840500c201000700704a5036000f01c5030300058511201102e03c44a00c1d14440b9032840c01022801c003801103004003082800030b1280b43e01c904070380d51500d43c5020840400100455800341e40541000200303145121400318a26030042500034034a401a14001c2042c0b03202110000d20341804182c0079407040b9024010850308116800007001190700d000c09a504210712000050301444080742d4142e10399 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 288009640 1250 288008390 288008419
    0xf0d08040b060f0118030c050406090e060f15180907091505060702060c0604030c06110906030a022a1b030111091201060e0a0b1e0616080705030a02010e0f0f060105 72
    0x114601d15407194610170f200c4c02c3c2030380c0780303024103184086009060066042c00c000040401d8a40217000c3c41405080180040d60b603800e070145030350720006248070b6904956000051498544400300c0107072680a04031b00c1594a84400c20510b42152680056107243c070300842d001001c00d204416405842c2c0c22103c1a42c0c6201500003d2041e018298101c860303400b030117043c80f00f0140c2111940d64218480d02080c000c0b110b02ca88800064007440c0300c019046601040014107504d82c0c0d600510042c64044860400020015511162801982c1340980d00707a0000301f00c426000f20b00009400904c400301c0090024840700d01041a260003540c00c807030300032250619000c0c0f555000390040800384c550382031040d8152400710f103000041c001030481d10380a01c0c280c140c04141240c642d070410103444d034064001407424440310341505034483d445409a0b0a02c40501c0b2040c0010801e00061010b1202d5900200d01c00c1d0b1101c0b5070906110310500d020050758007000c0c45200c54840410601d046030411280c410003540344 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 288010890 1250 288009640 288009647
    0x90f03070311130923071d0402060c190302061e010f0512070816030b0a02210a090b0c12071704120c08070c06090f3506090f0d08040b060f01 62
    0xc0d240017400c032401d0482d80b0308070240035540241c1080300e4404584915503100c824072090030b0b1040c50018440390f41000a000b41c00d22500415080d58842d003201c154003038146a04c10040c60149003100180c0001092224400080e08400602d14004a90303c0841d490030032002c4648546100f00307400f0b0f00c40103806a5004800f842580010694081941c4090b41021420280e011090004549055252002c2405000c0380d2003035400e90110300d824107103c00018010040c04200040000036004c0d1105c10150002c1c4e08241c80328000d40c8200010b030313103841503881943e0500c3c0c1c006000324204940b0315a51041c407120810324075002a040340c045c609090381030200300c5032041d000c50060038555000402404000950078071200300c4140d6a02c0c18140b98a85801c0140c2546610994a00c1c425056407101d104a503034020a00b0722025481c1100c018a03400c85941c00c10f0802c4507890f0b401e4109000d10f044012003440000d422507018a844900c1c2e02c0e141c0e54620340090007400540c00361102c00104c0d9010f900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 288012140 1250 288010890 288010901
    0xe06040b180c0307030501060e0f12010605030d050301030b0106030b03030d020d060510050c070801020405100e041d0601031205090a09051003170a230f0307090b040b090f0307031113 80
    0x1450107080307031103203001c540c0b2103000c1d0320070b8460100080ca0075000082ca180700d0b2445c0d590301000205440d41e080104003c100940340f45421080a555a649001683d5030b010004400314403010703150561258036604001109010517441340303007454140001e40c0c01c5947c0c0403007110084a0002c40c01038540020348692801401e05810150f0026945803400e81c0c0190040c001d40741112100d0308541c1d0b06030310350038014240d014501c18550050308c00c500e51030425000b00074180800c0009407000402c481c01c00c80d03002c07440902404410458100c1801401405001c0004640200440c101286007000c0704011860001903441001080d40da1400420100f888610801001f1904055490155074814040c5215035000340c1c0310a011581146945070080d01c401034801d07100300884241400d10006402e0390f2400d5000a003c40c00f08a031440002c85e006004002520140c2400400302d0f8940c01a4010b100b41992a480c00e24400e0303004900420024030301030800400b501003510910500d50822118001409 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 288013390 1250 288012140 288012169
    0x30818030717190309181104030c0501080c03040b010b1602030a0305091e090a020901110a0303020304120314010527090a021021090804030203030c06010f050a0e06040b 74
    0x248510004a4003000c21902d4105103101041d1400d560b5000d220303512a903e0038000a011400c0d44000304440c0e90800c160440c038030407003800440c0910540034049040c0d840b54004580130410f21000340015640007407419801800503480d1444c5007401d4441c4900d1a10504c03499004c0000080d1342e44042d004a8040190140e01400301d40540320540790281c1035403c106807036809102008991030400707110351420201c82c40d02600c511000d0b02d4055444019500545000f4140000301f20b0580780900b04009500030503020350f80058070b90500703241240035000c200204004150501a103d1380e40d00307141e40e00c1d9046501c100d69040f8016030b40014201e64062180c0c0b0781846c451010104410340002040d440c0555200b1140320f04040c01341c0d0015039188010707840b44814414881074042000d22250f000542c0580140b5405003010358039400a4030311750090611010726000300004000c1120f1150625001e021308a5110b01100d040002c0445403520040800384981c0d190201d1607181d8039621203502e03030b51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 288014640 1250 288013390 288013393
    0x1e0f04031511070c050906011d0402160c030f1e2109050402040806040b09060c0d05041505070e01030c0306050102280605070903170412020f042702011209050703081803 74
    0x1c0400f0f040013100409148070b0503004a0865001404642c414400042d010102c3c2c0b070310801c02159070050000035080b418403940c10550041c0e405c00418185402200214848d2a035001c8114051420051503612042c134920034403c0044220002031486109041c1d0450042c41055540c40d400412240c0e890a40c3c409501700344000b4001c218000d000c5002d0f0321503400744004104540f16180c0d200c1e40c07034000320744501051506005001e2022495000303290000c0c024082020840524046101203036020340f0f840c0080703940d5460144c0c043d601402012206a91307402c04007d0f50349070030000b030f440350b0b48041c1e2200304004014000502c9400d01c5000103049030001c40811407031410107005400b4072940e00056511400020301c9840f5061860201d07402d0303e500403d1b008100c0c0c1d4550030710a002201c031003481d40c042c0c0c440c00880303004030201c0300807005803400c5206401c4113855400003600c0c0300340388145500c03d5030501300d42d9000300d10006101e404403503000781540c0c0d403118843e5445042c1d0980c5030285915 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 288015890 1250 288014640 288014647
    0x1202010810090e210301050a1e030501021c05090c0a15020a050307030221130302090403021c0906110303010b0307051b07090609141501050913111e0f04031511 70
    0xc003000504c1602406030394048190b04501c080b0000250100b40f14166016203034000034460103003400204060206040d21744002152259602070030390304403504a00006030740c103203505a4009903014140d00441c0810141031039904010114960180500550000c402d1000240b000c0302c4c0f08001d40c176034068121007501c0d181c40c1c040c0740080d203501203a146442090001c50224000e020070364116440f1500d0440348145551441d030a2101400008000303400b94003c0e20305140034001c0d40c1c50701406000f22a66141d4415003410009801410011074140042d481880140b007200c0b6688122078009100741003030760300c0b100f4013040d205181c0c4d8003000c03c0f002c50007020b100041484050700000155141c014050000d5800007200300d0f04100c003200da008a40031040c6401030035501910040040050240015000c440007042e40c0094801807074840d203405000081105960041c040c001100c1c03460b041c10b0528141c402006c03403985001d54040074140412196680d500705003940d000001b46481240138588 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 288017140 1250 288015890 288015911
    0x10215010b0403030801050901120b10030218061302090105030a0e120403060e1c0512071b14060702070608040809060d181502090307170c040e031b07120201081009 72
    0x401e5001440100c1c0450210800072030145090003545060b81c6030700c1020003940f011038403402403070355001e8070003540c1c501e6108010002d601e0710244a42854040ea44030784039403d0100074084031000007010350f07114610610030076000f6a031150443c2d400c01d0701890302281d94018080118140150700c000851400c0303000600204001c290b4100c969a901c0042c00e45072007184000705c0149003e03000d0846070004004122084010240c048080e801000611780749840880644101c411801a0b182c00d651180c0002030040d116042003201540c45071072840079001c403501c0d001d8080e04108019100803d01c94020683c1c410b00e03102c1c5c00540b44858401001404001620034081000420030b007001c2d02d41c520484880e01d45030000d4001c95912200103002094094909464000c0340d01d4080c114000e03d02480d540c9041e10b6641d40200300400d02000e0142d551400402c0513030f083d00b0749002280565802000003006469440c40b54080c030b81d5020b080c0714200d596080d140111000b035070740008103240e1502c5090031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 288018390 1250 288017140 288017159
    0xc081b0105040311010b060306060a050c0f19050c0a0e0601050f0705010516120606050a03020a1215050112060e040f0317040804080f010506090402040b0604180b2b02040b01021501 79
    0x5008015000030406800501b0922004e40300c111445500036408010754880e06101c2c00c018003080c1c0c80481501c0707180000440722070504080d4201110301c415410b407214113010013401914072600c0c080700d144140e185820040e4428101c0181500d040c0100070504101c0720050070101c800c079541c004000c10152400740100040102607142420020303140d4001480401043c0c441d02003521984e495280c148818104114041c0d406030f0629801c001d1004200d0000d1000740c06414000310440107110700d46420a80018810301050900f6440503080c16020414803040013140350b00a6040012140300c40d03c2ca04042d11b084402c0900501016000004c100c203210003034000d032080d030f030f580010303a2421451401d41c0784c03d030364056036241ea10034248000b1600506e01603000d02e408801c080c0c40641010380c2c412080c1d85800004090001c02c0e07444012130a4186446950914049400881034002d11100308000ca08055104802405030b80e4425503035401340e008200300740c91040d01c01700d0303003219685958882 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 288019640 1250 288018390 288018407
    0xd0504050d030b010804050a060b010c02060715050916050d1103060f010e090c0913171306030b04060e06010e0310020c0102070501050105030f1c17010611060702030a0c081b01050403 80
    0x101c00a850103625000741e620071480c143c080c582103001400a40025155080280702803107020f41844501c2440f5401a1a04005005844d005452a50b900e4205641c0361060b900001c0251120340c0101d01c007562042c03c2048413409844082c1c41c42d4412202c0740c981100070800400c1c0440e89031040710b00300310443c0c0380580c04c1c0c2c1c1640c440c40742d8190142c036508140c1d90f50313040381100c443c1e100500314002021504c00b07580b003000041c0102010014242c81c2c000200150b03100314540708024507402c80900070140c00d030140042c2401f0980b820400c8614100d030303405078510090601c90404c40102c040e200a030b6000c000200103039050010841d0f03034804a101d03081c001c0d071098600b12019400c103000002c2c140b070f002c90030300c0d100280d00c2e001d801e01ca01d0b01003c2c003200c207202c0c0a102040c0b283c40340503402840084096540a007100e5107a41c034022006a05892905000802500441d407040024040c060340c00034501c52100e9102c00da0710f8550380c1e00440e0500e98100d41484101940ca4401000207140c0d10112a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 288020890 1250 288019640 288019663
    0xd0f080912041509091814030d020301030b0106021c08060402090a0503030406020a1506030f08070303020c0601030c0602060a11041203020c10170901060302010c0f02240a02070503010b100309080d050405 89
    0x100ea4009682d001724a00b81ca0601104901d190350401c01c031004607030084014020b9500000036685003040e980c980100301c0c0c00a800035a06003207a00014003900340c0401412302e485070125040e051503a2200c90051407601d00911642c0034030f0300401c21000c0c175164125640080d040040030349860726140c0c00001d541b10000382059820102c1c40c001e50800303000a10600040e02e070044446415607449444d403081d40d40c041c01c02102015402c1101000e60003041c484540650320030401c03d482c05c0d00d41384009190000141c8404042c500d810751402c14144c001040b60100c2e044520005601410341c1016410400c2c4c6600d01078111054445070f225640d8030215003160403120703d8580049841c0c0e113420900b01d4640d40030082c0447c0d8a865130354046880e1034541006584028030704030301186500003032030120304040322998400202042544c18a86c0500c01d20001d480c0540003000280e40345400202c2d1110702110850505036948540c80034801c0300d008481920081c008180000d0a0500c0c0055650182005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 288022140 1250 288020890 288020897
    0x1a09121006140f0603040309030609030906030f0203090a110103110c030403050114010f06082214071202011b030e19080d051c0507020705040f050402040b030d0f0809120415 76
    0x440c4071408408000d211403005400209104070140a104e03903076001a20a40a03c491041c0000010b80319009000d0124820360728a00514500403001c1d00b03468140c4100c14005005104101200340c0000e0b00c40d2405400c40745c030026041450005800810141d0402c4032044030000d141c140400c00000140110392042000300060075019001110242083c000c055994554407410005584204801504000c0204604160300c4401801a40303019030148112a01042482201e00b100b03c14800f040081c0416985050102107550000b00b400410700844403c50040031075810900d4800d01e01c1080608000c1c200307428040c0c0000c00540e04a200f0702c1030402c2440340303420b0450b00ea031145003a01c8070b001ca500c2c0051603032841c1c05c4003100a060000c01010441c418448000342c5a035480c050000c4c94580500b0001c0c01d42410700600080e5a0381402545c001c1e8480640d02403259441044c15203455442c1c0303802c1a058440d601150b0402800b502c245410450114010501028a201c04503200c800303030302d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 288023390 1250 288022140 288022151
    0x151214060906010b070309050607050604020a09050912071401140f0109060506250b071205061f0f110a0b09010b0102070311010e0607020415031a0f011a091210 70
    0x4180540e186401c03a964001500290010001004a44040d101e198480e0811110701a2140c0c08100c03542c01c0310724203131060341c0421300303000c11b50914491041c090204554144000d1604210301c0340c2c1c48081c201c50008002e0001003010601002070070f080b207400e0a19009000344101000c3c1d00100380c0341641e2841d88800c680c400064060b1885c480c007000ca58014040e28180682060508110310f0200d0000c130341021000f000d24001910803600c0c0e8400c41d1203440342c8006e04450411038046800c002e140300e015031010041001d6803c0c82c010103490406280c40d000a0201c0034007000c8424400d00b0441d1100392044041d08401c0041401100d445080a90003c01010040c03000490355601103100180010310114107002565100c3c16080100030b00180a00d807804180d68042012285000000104049000340074020040c3d060301c60f4406c00040402c2d295507003024a11301d18900c0042c07298a405107490300100c082d1141c0c44050781d05a001c02040b802d0801c0b03011030159160b01002d00046000751400c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 288024640 1250 288023390 288023423
    0xb01020d0e0d020603130c0f080d0e0a032a03061a1008071107050d0f1a04030503060f01030f0507020c01020d0207121103010603021e01020705010905090f07031512 72
    0x118414624003000601c1c2c1d0250030583e4080c4005a4006021580032508013500791020908811001000702245a95110343d585440001703070619a143c0c07000070800000c4100c0c42c22650324002d02c1d00c00c0c3c0307030003a80320420421681014070b00005880e0100f000c1c440a0340d000824001c003a400b0015075044d0603800c0503100c0380303001000200c0000344216004501c000000c110315038403816481c0b1323442a1003400c8801490b10390700040c8290108200456550f250389500b0001c000f090a8042c400c2528405001d440781000e550162241c000105264000c3c842d801c0c105109a1080d00500003078020007000300454144028025207660400030b0307a40c058840ca0780c0000c403851001600750704541c03541f150800107199569400081005c240786a030f516640381d020100143e0b44000b46030714501101214401030080040019007001c10a901c864140b280740780f420031540e1990880d060740404843d040b809580c0e41c1500903402030540080496600905220110b40e00c2507100302d000d580d5010b0154402500d030700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 288025890 1250 288024640 288024647
    0x100f1d0f270d14030610180503150a1b0c0f02030102130308070614071205060a0f0806010609121a04150204140f030c210f0a08040504050a0e060c09010e040f0b01020d 73
    0x2500d0690b08546c00c0c03100c0c00700c094805c61840024100e44100c14140c01da8440000346468021030442c0d120102030340c107120012900344144e41502200c0c04031034170b0410740c501c130140500c40e5100c0041c00c16200407143c01c0840d0b400b035048174100040007850308222a102d0414481c55003205000300c81c1c0c50f2070f042c0076241c1c100082d21418840c205555540c1c01c1400d041402c1e070007130000130306403581044441c200070900d20502c0e01e07a40d0142c18400b00500740c5601d0418000c0c0b03480080d03403083c041040464030080c00306282008844481045c6400015283c0322403a00308800c0d4900e800c1d181003540f010501041040c00b0882c40070100d40110740c45d171b601229400c04c154403100d10b0308080f40e1020210000824043c41ca00c0f140c07180c11000f00c140d584040d007221406041c402c00c030408844000700082c0902c4a840c00d0304c10705810003481c000402c40d0054244a01e980d0f4103001e8820241c000011a80c00941e80c4101000040380c0d9024105001e0303079642081750009032460820890240c0031701503082407450721 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 288027140 1250 288025890 288025897
    0xc021603050c0613170604120908030f0a1803050705101407120c080706050609090d0f110304030507080106060e270403050c06100f1d0f270d14 63
    0x4000d030191800429002c100200d0394401140034600003074031500003606400740d00000c446a101d01024006171b203403070300e84240550941078151090201c2c01c07074140702141c80001943c030000c0c660b180c4035541e440603080c2641e128002c0e5814140800c1d1408010042141c0030075224201d860030348415800400814082e14406941c0b407603664924002c0c001d90000c00c0c501d07410448002c001781000c16003102107856403180c550040b50160f4880e921a0288481c0f800c100b075419522480c6400034003080c4000e250b00a0407180c03d03442c110208180c036009000c107200203004480043d80d10004503400b481d80c0721100d07030203072120b03200d41e00c007243d01010740c038000342400c50800d1040130791100c41c601d00285001c0214144072029009070101f01040c007007410f003c0c0f020445540103c44404907164000e10f8440150b400b88841c0e080f002c24040c0c14807403980b00802e0240302d10303080443c406850505540300a698203140c005c10940307010001420511512080001c9401c190940d804e948580078492218500c1d4003d10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 288028390 1250 288027140 288027143
    0xe0109061b082521050703020c1224090601080109020d1704030f0f150b0a06030b12120c0c010507080403061d0609100f14060108090f07090c021603 65
    0x20300e45410000600c192000b44854140300308000c032296035984003e56407081402c0c0445044260500c10420503a64071410940749882c0d2070090320704011940d00a40340c013068051140280c035003880e290341c1c21000340802426400181344460b0112400440303400d01990642d6210f80344e028450020803001018013400b1107254014100403821003582d52080740080f0a400710442c1a08280008400501c171003e4118500b4090489616006014101044540da40c50507080aaa00c6d02103032500320380702c0c0d2000e04100c0314a400c0001e070040c86003002c03c1c8414154600c1e00982e0040d41b8654403102e070b2000c0581003400901c004c81c2d00b05103086005654500c261314000d00b5050040c8801c00009156410003032103a9600740307900c0c0c04000c42802107440d00f00e0540e41300080740c21010b48011900101e200d8010725440189003407100e01220324400420041c0600200c1c100b103020400120340c0722040002502006070030b012101e1246d640c03100c0c00000d2180c0080e100050080181c403007194a01d800c046000d99 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 288029640 1250 288028390 288028427
    0xc071e020f010809010609180506091f09020301020f071406090c0108010308030a022710090b0a030b030f07120201090b13050f0f0604080a14120913020403120e010906 73
    0x40407240015641460018241e9615640f142c01c00b04000c1d0700c500072102e2039000704458000070002840c003181440801040d02030030358481e24110720154540f0080e60b40703402101d80002403440050000c03d000e4880c13812884040c0500280c00f008000d50386249212288444040d01d245440f10303e9101e854003010000b29001580003030040c07021502400007103812944809006260181c2c0e8a002040d090199046820300d2550070300785441810320341064402900c03180392807501a420125030030700b10b0240300d149a007016179600744c1c0f0f401c0d030300c00f0040d00e04110720010031541c4c81540d880350301000b0142c81000300d0026101000000d10b5041c140d00b5a001c0d00e544801482001c1d0600080c0520345007010a4154820740b4001c01006640321b0302d0081c80582940c101404258220b81052418000c84e4446220640c1c4142c8c0c608400000c4034066a0781d035401140d6840444540c0551071019000f5604003030050b84038100e083d1a17650300184003040048080c0c0310100000c1e80c40005599a502e144103001d500e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 288030890 1250 288029640 288029659
    0xf090307080d1404060c0206060d030c0b040f1a0405010b010f0f08100b0c0f0c0307080a030e0a03020a0b0d05060906031b0411130f0b090612060301090b0c071e02 71
    0x80e000c1c5024121038803024000158500c80c80440442c0b501081e03c0c03c3d40c41e41e642e0f94020000541c1400880e5004000351204560540903940080c003812000c0c1e4041d09002015001c20100b19614200800558000070f10340648903000c01004494a01500c00b01c402d5880e2a00b80742007540985150300d803106042c2c0711040b150708072040c01d4819001c010024051102807440104105c40b242d009040d40d1400c0360000c100c00c0c80c07242d01c014070f0019142201c07840b80d400060304110030b61001805010f45607040c50181d440c101c103680814401e84058000a6209001d54070206070f414008000d05201e507030002c424051b40d05c810f401e1103d41031b0180c1e415901074001d181c5036130018082407001103072451301a01c0011307079010b001c441d4401600050144502490030031020080222104804406400102000c0707107089050340000b41c45202e054404060360401c81c0010303800d59404e611010304150804040501450701d00112182c0d0707407001c14115803511041c1210143e2004232960000c00035400b0708440d09 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 288032140 1250 288030890 288030893
    0xf05160f06080105030120030a2904060503030f041e030204060905071704150e161203080702150106030c200c0a120803010e130c0e06131406190503071d0f090307 71
    0x2c1d48e800109003040da01d4940301d0380c54241c0b003185c00200c56015103244030b1145a6400b01004142c81d8254030407440b0350310a2040d04052050001142c0840e400244442401140a000f5a0403920103a00c0030754030a150260001e200c181541006215582a954056000074201c1d0035002501d0295000390004118503045080701035664070804480318a0701c202c658008418202c00302c0b05000d80c2021070105201001d941c00c2640107000c480e000380c84c40c009445603070603898042c10342500501c1098101a2115981c181f4680541942621819450b0b200400440316002c0d15035107074112a2070f280901584880042e1a024010324607402d03d6201d5007003482d61340f0384070342c1ca0507010010306946146401e444200e00060780e05191580141408200300300541b500e503040015001000501520180c2402c1c1e426507500c4001c40d100358400002c85242c041c6030b048010480d010f01c0190010f03505440b9092020509160441c202409409010340300500c960744c0c2c42501ca501c940a4901964960091020b02c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 288033390 1250 288032140 288032201
    0x115020a050a0b0c0f0c1c1b120c081317010204050d0611040b0a020705040b12210f0d0207050705060a09060c020f090403050702030d020c0d0f05160f060801050301 72
    0x3501301d8824100b00d828017124405030080b540c080c4803c6a000d5202254a441e000311443d480c0e43c00301c0c007506007081d600700f041c0383e41070211105244c0100420500340c850b400b00c0e8018500910303e00c0e04107200549a000b240070707090000000d401603e0176104a01d0500b101080f0500895003541c40180080f007250038150780700d001401d214000c890b291002030001151904162020346281c0c1500ea0040c80d6151501c0188000c451034002d913680112411490720018501c0010041511800d00b6a141c01d006035000ca02d5005000b49100100c00b40340c005907815516210b90040c285003402082030b035440302d80d01d07010001d8601c1151034040120750745200400c0302a0181040040c8076002408101905680e080040c12100080f1022404a000465100203500302041604440500340c0020180c400303a01c00090080d05803004002d104a81c010701c3c08040250a00070000c1d40d400c8031150500840d203d13142d088194265018400008848600004443ca030500034071031103c105a080980b80c80350740b04e080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 288034640 1250 288033390 288033413
    0x17030a05281e0503040c050108130503041215060e01120303090f030302030403030b030a03050f071401090308060328030e0102010902130b040f0603110409170309060115020a050a 78
    0x1010240300700018898003a071901086401c8a841e59805007046500100004a40405216801000014000c2100082c1d00760300c818262142401c04404d10750714003910618480d403c0030002c01c0c0f800003140c002848034500c3e200c114658800c000c800e600080030030000040707440d13a101e10301600d1405001001034114000901105502174540403400a49940703403598a145148000c80000b5070010401081c10b50500c10300300490000c0707003d4403c030805920300030610300526041c0c0811200008420041201c0c03c2c0020249080c840300910100301103042c054030f04071040300c0184c0280680307141e10200200303142510014180d001441a6014841c0d28125101e10003000c115055658a64030b5001590300c00b0090b0a00b03080300ca4000c154024034500b0300095848683d10240c2c030710f0038802c05100090b9609135003401100140c40004060302c450401c021a100b02d410000f141d61400000c0c00065007000c66041e058612100004481404000080740d50300301c0f8a0000d803031034211812040000d070400b0001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 288035890 1250 288034640 288034657
    0xf0f02030f06040c050a050402070f0213020c010f060303030c0513350601090b0a050a030b09010612050607020105070c0f02040c02160605040e01080c01050f0309011407030203040c17030a05 83
    0x11511a144440007403031a02400383c80c00e4a404504e500e0800040c50907102e0340340130348021345080d030400c40c0320b40e22480808030411000303104240c083d211030420340540e4141d0700c42c144050001c0c0b21940e20100068000c043d5030000387c0019082031000d55000f80118211440800300c01c000e0420302c1d1a02d19000038800344000c0b003e0f40704101404010b5440d21101c101124440440c5c06000c19503d0320201c007088580c042d8680d0300a030345000041125642d400d03a0901100e8008083d503080e50f454080039070040210740c025494107901503004505100c0300140343c82c42241150000c110b942c540c40800d4800614900c4024114190b1102d460300504084e000703040410300600485890800f0040c00b40c3c1c0302084c80c0c115400044020408101c51021000154018101940549840074a00300000d0807440b07007001e0440100c0000000c510407020961001d5503005090039540c017141801ca0004000e54011b40e030544444440c0c240c0450015003180e01025002d527a003001354a404181c1009903003542002c0312 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 288037140 1250 288035890 288035893
    0xb01140d020a240807021e07090207080307091409060d030e0405070507020406173403062f09121203010b0a0f050405010e04090222020306010201180f0f0203 69
    0x1000c4016150210104007508401c100341100c80c2c41e41c01c00c00703030110580404034100150801403019036500810f90b030310303464031009100b070324840e00c2c0e040d8a10300a2558030251445200080700703010300c11828051400b801095540d0340b641030340c03000e084c0345285078411413030350102c014004038200b480c0c07480c2d100c80700a101e4280740e5410031103400001e04072001141c1c00340100707000140a10862901e880741c5000303480b840c0da10340c00700e0011400d910f59405408503903810701d5003441c01e80004401d070f448a011490120b642c850792210f03142d2070284e01a108a4880540b0302e85080001d058807000300b0311f690510709481400506004610040040450b4200b025055034007500c3d800143c20325500c0b00a5000c0d2401c4004507075190428840100700905094924003041014407082c08560380c80755000c2130304401158046044c101a00008240d0402094103940748030003031203041107000080e009140304003c241c00801c00c80314916120360000311242e60040c0105c1c42001c0302d0300041e6401c207880030b500d0700280 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 288038390 1250 288037140 288037159
    0x308031503100b030705091f09050a0c0314060607050322170d020a0b0a200c0d1107050603040c080a0501090c0f0b030a050417161716060b030f010204090b090c070b0114 74
    0x14080409154550442c81d00b40e51110704000e00b4040c00d01404330814044e242c00c0124444040590103680b201a098a210f0480003c1c03900501c00100b0503156000484803281081503044185580c15401d14820340c28800c101e01d40c05c090f451004100014151000d0700508000da444d42d44038920701c900100340300b100d2640c40d183c45124544105130700003100410500c030b6a80d800020f001c06d2600840c2e0b401c500801001c50000500f007100802c0d0501215800c2c0c2c0c00d03d07100d407210301d810180036015401c41503440c031407001c420084c0030b415005a100940200c0801009980398450414543d0141c012400100c00c00c0010543d41003056021551140c02021110036038110a243c0c13020684c45100105250008800b5802c180701e0104180500d50b021200110319100054144818070620340750301401c0760380e13904032102107610305108001b2001c425800845d643c688411030440148801100c3c10b000d0309800c00016034210b003413011500604d40003800c1d000160b281c0004c407462a404550915000281d11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 288039640 1250 288038390 288038431
    0xe0303040e091e03120649030f03050c07060507120515060a050c01090c0b19031e05250f171b0c0312150301050714030115090308031503100b03070509 66
    0x22003007080c0d510301b6032001e003100315040405204011081820100542c0401004000089e000100d05210344d10509010525607100e00032034007240140c0c200a0242800c09041243c00c0c0d5210f01c0b50f080824600104000070349855100301c6160707007400307030040d0040c03020043d40c220740c2d0191000d0706c1040ba0440002c40c0c070001d6030382c4183d21a00c007075001c0140d20501090042038070a0748103144030101e61a18003000350f0044580581d2000c108e42e0380c3ca49005680f203001c00c100604241803020340e030640c0b00352044c0070448107100034034500090001100080486414540c1c0180b1220424003e0300d482080c001d40414090103010a03912016642c241840100206440e903024400704601c59101401da88954030440003c2c1400d5410042c580c1003040141905620700b11a4042501e05441e01042da03e260100d602e001607552602c5900003610b20400801000490355100c514a100c02c4400e4040d141250500c0103c80700750b41e0307401002540b64110000500076414906031a42e8000040e180c22801e580e144c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 288040890 1250 288039640 288039679
    0xc011d060705072601020a0c151b0503100501020604080d0c050c060c040e0112020a030602090a030f0c29030a0f0b0d0f020108011202130c0e0303040e091e031206 71
    0x115405446001849814a092104c2c80f4901d5070002052138000c1d45804c2e044440288000d24200c2d006040040c0d240b041101000c583d40441d041d450520480d9444620598024041d41c100f1507542d20a030302c003c100441d56501c003040c2d07240980d5200450309c1c100a820454400600051400e10003000b03c18054850003980810015005441540301c3d25900c5080120361891030307205030000c9003840b00606810340180c03184109441181d0b00701c4001a110500c100015191822a13031004d09012008510b00042c086902d080c0c0080f10b400709901030800a201500b01d403102c1c130030551601d085034280000b41292031144c106192341c00e82c2650000301031405070300007111000301c2c58081d0350302c02001d07400760112758000f1645800340208214408419281d680061408901d0038100e101c0c058541d420f60164502840e031001c030108001b41036a032203c0c0c540b0044203500707a0465812100d44202488444408000d90740050400c6446001d5440d10307100d02c1e0b07031602100001d094250040c44000000d03c0c050070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 288042140 1250 288040890 288040903
    0x1d030403050c040b03280320030901030b060f0a031e06050d0f05070e0415050f06060f22120c05010503040b010302091008010204140411120f040c030f0c05030f0c011d060705 76
    0x4107540d00200286c140c0c1030003040380140101c1c1c1d6121012021280010110010a503140140240b83c00f00d070005841020400b03501031400800360004012030368115490300b5400c030118200000b24071034040b00c0008812000d0b2a502e100782a0040808618000466944041c0303003442c0e4055000c507400c40c2c0e034400c80561100740840e002da9840c0484402080300704158000c15410803440b401011a9041c0040040e01074421320308100c610960000d0600c01c0100d919040c1600c4025030403490020703941c1e40b40c1203180c180a13024200c503031001514002c90b01d176000c0d030140da01442e007018004613142e08541c00d100c0d4802d8041c010039400d0032100340c002504c0741c2c240000d0001e40740d00381072410104509801c0c4800d0340c0c40c0041c01c140d1824103100b8901d1003c800306903540e0003004500d0f441c0864455080584a042c01500f01806003200c0d8259907052182c20764048048884c00d070215202e54140f004210b40311560b041c2d680b030000300d4407840c50301c405102d50959a000c450081140f46030607010381c0c41c80c0c03078440d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 288043390 1250 288042140 288042193
    0xc11030631080a0f030b0904120302130b03010b0c06010621110712050d14190209011223060909151e0103050105040b0601020a050706030f02040510031d030403050c040b03 75
    0x13291640c401445a5040c0a004902603090b2103203030250405a54802c4070130f00190f140d60405501242050f440540c51200c0401404810340382a23482d40c4402c2c4070003895000c000c090449200304800040c04910480480380e0b141c00403030015203030f40000182000034000c040000e4285082c02e01070000440d038101055043c940441c0c680780c2c0c0d5506a810144140e8580d00f1209000c9840182003b60034080c61410a06100f81e0410050703036031611030300580c1c0c54501800b0300840b480c584240f5005500400d1141c01c0320050305c000040740c0360b03100020028610703c00c4950714000c0e0000106c1d00030b1300400e02400c40d08907044000d003075040540c0c06010042d5582c240c5c41a45d00f42e4486090009010380c0821454000c0020302c050f01050820f0303122140d4644041c8151410195940c030b41c900380381060b5043c0e4001d0440188111000394000e44001d001c4d00d004e45591281c2d595031400d041190100104503130803a03034808050300c40d40040c42d007004003e280d5400b8480d01402049500400d03441000504444007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 288044640 1250 288043390 288043397
    0x80102160c060e0306040605040c0e0a02070c120f1401231504020f030f10090c0509090702030412110a05030304030f110a050d110d0506070c11030631080a 68
    0x42140c1401106444594001d00903c10000e5641c543c940340410f910380c0c015004000800c00341c8580c0f51203081c50040d94442209c00c0754140501004032070a800034402c80e405096224021500d440303400c12090054280141100191010f480014003140710401030001c1c2d280000480c01c40303580320510108084942c019113503aa0204000f0140c590a01c004003030007065804508240180920419610015200810100742c0700001005102d0000c100f0014003003442d41400518403000c0c01403c1900300300b6900f445003801400040019100000b40c40072541c00940a141804c1c05440740b8a4154954a00301c1d00a204502c000c200c0e5203040000308015445000241c1d080e03005130501c005010380300c24486100e1034012004015683c0c815010066954211150318845522400000d0800440c140000d0960092034200001d6a40200411a01c980102c150040d40700032030b002c06844000c200c60084000841d40366041c0022000849a16101103401c000b80e5018419103c41e203151b00b000c008100007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 288045890 1250 288044640 288044677
    0xc0b270d031a09220501090f02031507120b0109031b08060a060f0e0c0d150f170d080417030a09110303030708011e090501030807052103010b070606080102 68
    0x3503152041c2e0384400c5001d401d40d4440a40c00d03001070702d5100c02419450180c0130390a00e400c2d000400303030070b98407442e50f001d8002c105d084070a00e0000560494040143e1003800b810500c402c41d4000c8824151203103445aaa01000044100440c40280780264903281000300841001c070004040c29001c6020030000b29a0b10851890040703e03d00e0508020034142c3c2c0c10341081001c04c03a00194008904c10384001d134480090319a68810f40d81d19501540103541a0103080200700c0e55180200c84226060707426100b6681d660645400310b5101c0483d607040020519840801010402c034403d2100c0c603001807080109003030402801401e512950001e40b0701c0b003111580c5515510422080941ca41e0940f0300690103076007103207004880600204014807903035030122a0409221070030071440102c1ca000d402d02c1032040200b0351316410402c8054001007800c540505c01c0d1070803007000b00c20000c94048e0003403d00c20340030b103140e0034540b0f11440b80c0c10420007212201e460b4400483c415400f030001d03103080c20816950040c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 288047140 1250 288045890 288045913
    0x1060801050603160b18041806050106030e1c0917010c4e0603030909050a06050d08090103091a060102011116030c080d230f0105010c0b27 61
    0xc41d90040d0180e031007035208400403500c3c800349161880c2112414228251039080000c1c2d840520304000000d240d00038544928501da44000c1c070100900c09000e81000c002c26a2203071421b8084074403040703081c40550b0200d06e8010441780001c400000c13008a529002c0201030f0b4902e808214084409844865039440701d00c00d48116a00810710010207000c840c00071405107001002c44540800c40c0700c1004c1c68100326404400843c620380c010702c50b09010b0f083c10080d03141c0d00d04005194016a000c0c4591a0703041030045810350300e01340108800c1c0c940c010715a1000300b030555204034183d402100e4036410f054545089a0101e280c414480d1a14002d9040d522900d180c000d0009086803c0310581c94141c601c1030151071003e0307121803450803506525041121584001b81045a124000c0c10060300b4114203052110410034402d00511010302d18291440d0321a80302d003803034850107100c04d0041c0f50004128510380008a190001c1441c2c01646c03500c0c4140000001007050750030139a103051b00b1046136208030b01c0b014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 288048390 1250 288047140 288047143
    0xb270a031a0108240c18120309040b0d12080712050103060b010f170601030c0e0402030a0c090e0103050a020904021c030203130f0807030f03050c030a09050a050405060d060e070e0108010608 83
    0x200c1144884201940f141099614005001c07001c0d114080a074800714101111070040c2c4180901c1c00b4009103607c801714801c6195a90700d5002c205ea45010398182240240141404e001c400c07016544509a900101e2041c1c0c42220300c040020b0580c2e08009074294809508102840350a0207180115804140603d0303850004d440c416581441c0b034100121401c1c0035040c045411001e681080003460b001c1200c03210420304817044540044070a92040c4008240514510070307500c40829030040740c580d450f2a03070f6158020b201000c824030014040c1e411403c59040180380100c0c016a0051004200244c504940e80b400109044c18038801c8025a000081c40810306190528680003030904064100c4158140760315a1380700e5403d440002c181241850300401050300a00130750b52080c00145c1101d03160b001401c4020305080641c032459010703165488020455042c24040c2030b104040140007003028030b009176600720081030500381d40400d83c000e0000104481c0d035000b4440c1d008095120020400358181200319 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 288049640 1250 288048390 288048403
    0x20723010b0108060f10180b0c060906010f060e04050705040b181c020a14270406060504060305190203030405100e030709060f1e0e090102070302070b270a031a0108 72
    0x9100d0174401c1910391a41c0d035900080040000a454510403020318290300d001c10407140e80002518040104029404070070020780301d4070408518044820a03640c40001c501d490059000720320000d503005400f19185d040035000360360400f1092409500d02980c0d04030425140c1c00c09441510300a811804043d0203141030380007600a007801d10300010401160342e0005680544510a00c0f42c40745045c01d0540403661780751221401d030341403444101c44103d55001501a0030100b2a401c48034185000301c0401c0030b042501c00d00d415039034040c008154201308543d55000362903140c84102d0f8148000c02000c2580d84414281d0900c018480e203a00262540307141c10103050096540041900340c0c034102007081710b607911500c40001c642031440500ca44841d1200400c3d02902c0a40100c412040440180711100005500800130b40e0f0290303081c3c0345c1d42c0d1340700e0110341020701c10305440c1c204c42c010b0141580c4031014400b4100341d03d50b00007044481810743d41d580e19606840b0040c1268280e0040300c004016034601402039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 288050890 1250 288049640 288049651
    0x111207031b03110f03090d021009080f0304170a09050a080a08120a180f05061510051804060308030405150103030f1b23010b040e0c04020723010b0108 66
    0x303001c52050040884030481415140c481015103c4512010000d02041159805a0075400c125075a2030410300281e40c42180744134040c0103114000103102540194440d880d511903000020924103440703201c581c0020b410141050722443c601000402003440d6120050a4449040d101d80e8442464981081004200344c3d001d0149600041d11210000c0c4001080710800c90b0001c2038507016444030141d9a00401014080d00c007110403030608803041c4210818000c0c802407242007103070010355038544001e5401002100c56600081c1d44012004246d001c0c1c8040c01c2d0480d054081c199800c02060300080a85200398030941d0100000401e200030300c50148001580801d0800c00d071103641d40345035802890400301d094407404004c05c00412441b0005c0c0001c00800643c0c000844080403001d0400000d4504601200000550310b0901d403e24a030400c4d000300e4080c00054800343c10a031551105000187d0301c0904221040c90380d02c07a0181801303e0201e10000c082a8010000be6948034440c000f400300c50004c1d09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 288052140 1250 288050890 288050897
    0x210506040b0402121b0c0d05190c03080609070201111206030d050406020a1502162406050120120d0f0c09050d15020c10052a03011a0706111207 63
    0x4c00b811150403050415045004450981810395082c0340c800300d503004000061030b04e0b00494500b1840b040e4000b002d001d4020130801d102446074842882580e216264942c000e004c5900e40d80010320710f242194611750b014280b40004a40c516190b0a1320310f0941c44011104114903208052140d5410100520300441d50300d4240306291604141e4081e60f1074070f24040090952041d03e2202c2030124080d0141c038012040c07409245149411403401c9040138112100603108203017503040c1111a94140e02401c41283c0060f1a11220f002c1301000340b5400e0030071004e981e4903034800c100a809103900000d0081c140081c1c0000c1c0000c1400710421920203403908200b612040100b4480e05010603901c0d07506d140c404540c0320600080707008043c0346030343c081d0140c40080c000c1c6019500c0c40c196154500c1c0c1180c1d10a41281083d1411001c40c5410081c6e58001c25201d4130130102e0600061110030386110007819444000b09480d4100038450792050144e50090300c811030180f0010440600340413042c2d240a80101d81c904 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 288053390 1250 288052140 288052147
    0x140c10050301090209010c020406030302010222050d1b05090c120106050a050a11070f09090507080109050309010f11070b0c1506011b02130504050102030906070305040c0e07210506040b0402 83
    0x1002005070206004160000d0750002c1c1081640c2c0c0240544410300c0d5020340140405607403800d001e4000d403c51110312101000340c40c40309944607460038a42c01903d40040401c551200e207a11800000604068908401941d5690100e0143e0b20060303400e102d44009200c1c0b030303030321143c040c0310400603081a81b03c081400414040d020205400100360350f41980585001c14484460740c0e80ba83c680722680d800b00340d0380104000049580c50864100c0c20610b8010011111400d130785199281c200c42d44e6a0740503249820521813203e0542c4101b4040c003082445190005c9070011440d07010b8107064060b4001041003000041003c0d840509004400c2c80b007504135001a418989100007a00701c00c440c40501005103c115004021540c0315280e100f00007500c45001c00031450140b4010707000b5402601c140780b29101d00000618074901ca402803500c01d07540111408001ca00d4900322484a080140803002800000300c0310b00c81000e01c0b078040c1c07500d130003002402145904005080c0000c03186241c071070070300850040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 288054640 1250 288053390 288053419
    0x61317010203040b0c0904090b0a0209040b090603210403120c0b0603010e070302090903161b08060c0414011101090c03020a152f030a05040f0f051c080c0109140c 71
    0xc150b66903210b030392545d4030780c0d44540120010303004042c044001403500c0e07407035000d0105424556000d4281d100c010748080040c02c0b0b4040030403111000442e00e130355040d4012240f0042802c914007140300280c4901d010142826160394603581d0f010184462440068051040401030201c0015103079048402076000300013064040c103086441701d949010180c0580c0703994000c112058002c004071036202c03004880071462990b45181c40f00c81131b50003445600100c280d141000c1480c540200e0113030f024113080b9408514040c908403134000681e544d4080a8144048840c079403125403801c0c098442c07240d200e2011841c2ea14294410496560790070b030402d40c4241204a05640307008d0704003008200d18a4202000449006550000415900c124082c50524000403460016280e00a400780c02600c419403078a290341d5450311b240403007103184c9100769540b281d56503903030040c800003032003079052228091070061b8030702032000700154255081c00380121803c503800350b40710344038102c10711400054450442c1c1c01034114905 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 288055890 1250 288054640 288054653
    0x3140d090e010506090d110a031a0106030b060409180204020a1e0e01021018141006080303040807030c11090c0405090f1017160b0a02011a01020d0e010302070206131701020304 77
    0x170310410350302a09a103802c500c180000c0d00740c0703494060001800301c4000c5d42c40b8034041c848500d44d800941222800300c0c0c00481e626010b4000c94146c42c8020748000e0500f45170100c0140034005030511a186400d40c1380d07801c8056183d074002402025840d8892110000b0714280c0125000e00c15004074080100783c0d000009280c1e808203c8015042c1580e0000c00c3d5041c1024020039a51201d0100410322503e55040d694040c10101c1e02b4507860421900421223140d03242d03030040d03c0f84800caa00900b0100104003040000b40030760302040a090299081d400c00b0001040441c4003008240e54040d50160045001c0100c3e140c614401ea0740300c00007882c45126400d021180d8a0040485d004920303080311024603492900c0d030100607224100070800401c0b4040703070741c2e0389100440b5404096904019400d20828001c070b007041301c3c861002d681041e40103142042c408001201c42c4400491080e040640030803410b07003d81c1e1b441005c1d001e45c1c1d00d114100c4580718a020000030000c100600c90310f0075070340140b08100105070f9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 288057140 1250 288055890 288055897
    0x60e1206060a050f0402040906060e01090f030b0a020c100c02030d0f11030a110f030709140d05060406020a03150b031f0b27120705091b0d0c050403140d090e010506 72
    0x1d80d4810321001396600010040d010701d8000401031850074400142c807c1d4448400000324800380c8542d03220079100d5a20100f0031780f8a0001418000e464070105052115a600900d02c03141c1070403d40c1c46401c03050044130159143c0c01d42000042c1d201040120341030398a48a1403604008500c810020b41388414400520b80c080105010149560744140d4185450030200f2100e504182202c5560b803031424200c05404100703580101c4181c0d002c3c50140e200d8909102251307120007504100141035950340c03a47d0700b0010b580400341e400c2c1015210303104c1280f2003014140580250651500094991602080319452200042e02c0010f0000d032110081040b9000314080b50105591000c071f455042823110a80c1403403040403143d40d9080f00210840200003040400c8c0d940a980f81120010700310f45a0801c0310b1072026008076180d81e101420816100112901e5011180048441c00c1450070540d5036103c6520000d45c0c03407a8101e40c2e400500310b0b83e00319a03200211501503c8280340216455050501141d070a01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 288058390 1250 288057140 288057149
    0x15010c060f09151a0411120403020106050a030501060806090309060a0503040302071d2a090108040519140606190b070615120b060625080d06060e1206060a 68
    0x19980c00860210450316000038850075002540072600307107066201c48006040d1804020344014595a1160784c91816000341d01c0d080b02d1480c00351303040480310841d002184001400c11030940d941c50400181d50b0f00c5c0d1072000801107018100003e01c1c0740c58004420300b8a01e0003007140900da00108001d007240d542e03910130303038440000c00e00d84151259100c0c6401c0e490010160090420700c60f038086c0300c40c15113070360016142c4105900010f682c4400e845455038086000403550030000ba040601940f49035510030040389502c1801801181c540b800107007a500400d0140c030380d040d201d00075040311545800404001680e007006044c0d03008120041180e021100c22400c41c004c603811804009101c8060000940102401d078852800d910178883c1c1e14440f41405507954141202d10110a41c0040d202c1e00d031032301c00e841c601c01c1e49105104031040c015502e0340c038044104d00129603c07127041c042505805130a2041030701401d40c035180c0e82c080d000c5607410402e0003103030035010240c60707441001000b4181d1503001000742200c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 288059640 1250 288058390 288058403
    0x90305030c1b030403061d0106030308060f041103040308040308011a0d0c23090f18060108090a060e06060a0e0403020c04020a050906031e01120506010302060a0504031b03060515010c 80
    0x220701c407a0401001c910b040c0e010310640d110108022091052580c0700c2c0c0340c90700b9003050024104034007044050a030b82c11444040d000c1441500040e03c80c0c180000c81880e0000010000a00903580801d20041ca0b0429a002d03000901d000c01000300f0541c202c80300c80c0c00350000e82004009031544102c80d01c42d504c150f640701618281c65210303a45140b402944040105d00211803104118882c05d003103950076401a9800302d108000d48815160103040c101c0c221440210610480e584643d2801c005695902e4041c02e49400c070701c900300042c400b06d44640b00b8401041d0448020709603c0c101041040750b00310294205060090b8071000b8000082e80000e00b0480015003540c0141e01c5981540040e5420301501d030407560040b82c000308000c3c80c58000041600f1030f403465a182c22041c5d0321060b0a182c168944100185582d000c1401031000d4038044026108d03045052501d14a05030b160382e9800c01242000d5404004036400c800d050080041c24001c1540c001000c140554400c02c490700000c05003a147e01001e88103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 288060890 1250 288059640 288059647
    0x2c0c0304050a060911030f0d090b04050f0f010221030109050601030c0509040c05041509180c0903030e19090b0102061f1802071707050f070b180a0f0b070b0a090305030c 74
    0x802070084507042e205d8100506a03a0843c00da2170f2016124184088990001a82d182012884455103020b56013511000ba1480c0c2d80b0b1401001484241e01c00101424194440c5000c030080242c40329100d00d501104c2d9048880d26940b50403111000e486e40030304254181802c29001c0c401031988081036400d01030040701c020640c0111000151000e1150703030405040c148207500502000d940040c103c03c1110090031682d0007004110242d40c0c22942c030504404009030200500b007000c81d1081c40102c1800c81d0007445816607109800c00181000450783c4150a0292200c0b07200ca203d42e0180310f41580f152428a141020358010054001d1182140c09050380358000300030600001c1c4240d9054a1502c0c1d0f009045260801012506c551103030400c0c5011a01c502c2401d51125a000c4c01103144000c81e18100200743c1042000a0003d5003184801c1c2043e404c034400751400200a185484032078001d05511303c60f81c0d65505c0608041e029144002c1091401c5400c1000c91000258003004407544070310002c04682d203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 288062140 1250 288060890 288060893
    0xd02061b010c1d1005041503020c1c0e09010503060105130e010c030605150f0a050d18031d09090c0609030a1a1008012d02042c0c0304050a0609 63
    0x14034841284100961034040d484402c55040540a402040d0046690060a00d0001004900c01020166000168051000b0402007030840c000c05907048040c100035003020014004e40d4036084040c0c0280c00c44220380c0d880030526507003250034401404001c1d60600b0182d81400c011a658040c10b00c112800761141029074800316200e40e01079228001c10b0300083c00280300003280100a440300d4001d140c440d207040280c0707101031517004085440b00a22440c14a042000f42d05082c0c3d02d5400c41d0480302c1900d0740f03032007032900f40b4a40c100904a986200342c0720144a480b44010034a00081d03110681ca004000034014046844400502c0c24030b251021680340c0da9070400307000802d0030000c0000c80200504820240000e0100980c1d0601d48546110908080c03416a05c102c00ca09a440325100c50140500f1450340c110805040036600900101e007031409032034903649004000c007180640003882802ea0f022101d44554016104aa036006462801883c1c11800c10341c03186919001c2c2010000c01c510303602c450020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 288063390 1250 288062140 288062167
    0x912021008090309040504050114010b03070903021c021f030c0e0306010e0a06030210051801030c08040f0201090b0a0e120f061305120c030d0b030106061413090501150f020106050d0206 81
    0xb1018413020b003052000b0f05040c9000c0c2c0c041e03c415508414140540b0001081e09490346003924403039013107542da15111a20f1502400502e0010422561103c0140c100600258840328140a0141941d0008a4000c4528200101160503620a030401c1088007540b5030950707503001426506403521504010015101c02588100514a40d07100a400551032110701d100250460060100d4100c2942809651181040110102c64051a0000200781d660b00450301044030710312030303501561041c140b644103941c581b4a80d0807242c000202460008892114070009401e01249400d01508110002c240c280c04d090101c584811008046810411100d0010014080200403e03255040c0c4100555039407480000202c0d10b9a0000040d8850a070a28015003440e040522880e0100d548540d04c03022048001d401c040290390161680300c885024482c0c0203d015002449098000c005043e240441e0700c40c2e4000c05084506100701c0c40303066924200d403c05c195112202e45040b460350403105940e86a01c0803c174003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 288064640 1250 288063390 288063397
    0x13021c260f091c03020a060501121a0406090204060f0f09020f033111040509121602010c050d02030307022418010f09200307030206070209100b030a060609120210080903 74
    0x490f0300495400c0c90000d141d00400e100303103001d00440741486140c0e01e0f0f001c491011910075800900801480940d65000406400c00a4103e44a40d4010580d5030103500010180c0c0d2181e001550b42d4040074004014030407111103500020250721006502b0a00c0b5120264018080144440a00414110b644408a0802d000c2c00203554503001e00210b00e007210b050060001c00807800760743c00b032494500411011500010303000d507881d80800d000d80c58098291950000e01c0b50100c4d00728103110a82d0f001000242052041c0829135032180e006544910781024000c0c9085d031900f41d100a080074010401c01103449450744903900040c1d07528101503140421a0507030041205200103030840b80303040350745020010115801d4184103003421182810200900c105602c52200e80300c006d500200421040005040c60441103501c909060003410380540c1e61380401a0f03580c0100c4503d04407554542092001d10307084040000503025100d040c4050003465400310755280040c45020060205150008000c0396042044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 288065890 1250 288064640 288064669
    0xf0804021810080105010f0f0503010b1e012109060c1b02010c020a03050d020c0301060803040e0613021b0f100618110919050306010b0a080406020313021c260f09 71
    0x70815987d481e80c400703c40303400600522075007280344080041c035480c050040707030890b101c01000804a5507100c10040525601d124010327051250a1000301c6112201410003030800050310404a0f0b200c105260003000c6902c007a0b10360302848280718130b51581412000702100701c558203081c2101d050006000080c0d10306080d520050443c41881c040405403a0b0100c1c0460110000f500284507a50f100d0500e90344a01842c0100301c088861a80040d0007484c04000d0b42400c0e0b4548000149010140365941403404d04002d00e01c42c0c650300000410b2001e0000b04030b0010016600c1e05d0400030903081805c400c0074403d04041c0c40320001c0e2180000341c8200c62010481d41c807424010940c080d102c0c020064825040b109215151090107a040000f80d02c41140c41150101040c80ea92511103503075550751003000790800b6000e6031400341c200400000585449120742140e01010f03003419500b11142c0381c03100c41c0341c0d10020700c11808040300c10000c0310820315070203440c103051400c3c0d200f6446501013000b140500102000e07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 288067140 1250 288065890 288065893
    0x20f040303171812030c1306020304030b0f150f030c040e0c01030501090e1c02010b131a010c02031c030905101d010c120e0109020d0804060f080402181008 68
    0x800100305604001421050380030038030b020740103694100384400640c151441c100d00766044060600c04800c055070085900450719080035060400807a035502480380d103504900b0160784001018400e11518143c503a900500ca9244030f251340c07078036005035121a000004038600a11038410781c5102590140190300711204003400030020304844e03942a955a90100d141540460b10309030000c10000407501420480030f0300403005001c0540542d01200d600b240000711201103541e5140d1035503056030b0b18591414240340502c000700e0b07086640c1d100c0c808210745142d52107060011060518005880220713021507200d880720740102c032595540e60164007420000c81d000703110340204c15045070414031660000b00c0300e240c0410035880300c0524a0516017280c01010b081800714000900004000645070420101c06c04150000b01d80300100d6804142e180b1550481101c0814012405011181e8420a2040c0044907480c043c0801c0c105500400c54031307540241e0482c9007140c0100080d1a105004042d030008268200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 288068390 1250 288067140 288067147
    0xe10030212070509040c03021305190801050109021306020a122a0503121b070b0c040512010605100302040e13050a020d050f12030412111e060a050c120118020f 70
    0x250b008086074890540d00e44107600e8115110b0b00e0714400d00c01e46114082c02824070000b14100010820040c09010b50b04002c040040d802054940c1c0131700849000f801041009a02d40003641006a8041c44682044085501ca8042180421089003140702440c8141c149640003110340c008400c501c40442c2d64200c0003450f400c8219041000001c024601d01000308090055521101000750b81c1c0c82840010307044a03a000d00c204404565003460041e0003412280750249444c0d668000300f01e03103124004903905680d5455000b0040c6040c003802c0c00c1c1c0801c1d541e02e401c614060902d00020080741e00035043c0c50ba0075000c04001e400b009400c212800b40d040d0000e011406410301e51408954800a001c0404034900401e108d6513508822281a41c2c000d5502c07605c002550110000c0848581c0542040196203118420b20840c850340c3c1442d080c2184070f040d030301411952401c0200351080c0c03280942508107508080102e04a1203c0802199054503500450400f400c00c200b00e051019001f003071090b45201e40c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 288069640 1250 288068390 288068401
    0x100e27120f18090105030303070f05040f030b16020105190218034206010f02010b090c0c0c030a0f08070f060f06030b060f0303042607060810080c010e10030212 70
    0x20b01412400b00c1c00d41d1206000e40018021038080c203102e5541c05600c180f01003000306014581d00460140b1780d25003603042030f03617442c1031450035941d50707009848004000c400c2c8080705905040901c5083d07064002400181400e96010720071a6041c40e01100032a4042030366000c0c0e10b200c0800780703650100141114a000d15006c40010407003400d012030403400c44c4030544007002485024100540c4003414400001c241d07503000064a080341c10000c01c0b42155a1002070034159650148207034024424072101d2034440411664080c0b51511426245100c1e5105090003400245098410543c40740d0000c1c407181c03107001510f455040e00a91034401040c5ca03042c8250a00c500034594461001c690040c2e4054a142c0c84140500000020000c00d0580541003000b083c0009102b5410810412074030b9075102401c105094029401d08015410440000e81000c0500c5170455060080b030025248890213009a00c0c1c0580c0060043c1c035021220780d02815800030301d0111740e406981560b0040780100c402c02c0447c03928 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 288070890 1250 288069640 288069667
    0x9030319200708031b031c0b030706090803030112081e07150902011d030a050105041a1006050414150d20040803070803040809120105100e2712 63
    0x1a4500c0311090107285114151100140704011108450007851611400321007456141d0701101d400c144a00c820800c0005201c006501c4041200f180c1400041c15040e4804140c18051107038080400c00180200621a1590101c1140d04546c071400304149542d404c3c3c9401c240f1401155082c02c59002c034200a44160503000d4000c0c01001d00c20304001c0c22001d078038100030003140c21040011f070018080010b1800b203071180d440c200959100080407259510129620700e425a4012182215690240481c001d10601c400035410340001c1140700070441c090505100800c0d030b0240c0c1c440c85500d03c4090540000700c0e02c0d211282e051540020040c3c0350344c0ca4241301d8074005400c00010048003403111079102c020062002094505540e200e00142d450000d091720b0b0b403180c8e40c2000d0301c141c0c0c540720b0420418020755582c80e210044600004000f00e03071444c1c5154154018000e40e4412080d50b89070b101040325000104180c0b0510b01504505003104040c00002c040c5440810403114050176800079091440e5000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 288072140 1250 288070890 288070907
    0xc030f0c0301111c0c1107061107080109030512041707080a1707020a0327030c0306110909040b04031202040b04140409170304140d120e0a0507050609030319 69
    0x10305500a22040d100f40542c0d00c0c192080d0040b8695524404940000001440e04100d82c402d20b1441c1c001d48581401300898102446944442c001c00d50741108a16a02c809200980084c50820000c000d454810b44016001d8407501601640c0c480305200020100211080c0071b51811007080d2000c0e8646845281c00401c0341d100d804d099022540b2600107584c01c1c0c0034000094401d415030f0340a003d0700d6105a50075101d110005444100100d0350156601c181004000316000940c000e881c001004d03841c0d800d10008407107030000407080c100c40421581b01d042d141c0c50340d607540103a4041003100082ea00c900b01221500c2112104441480c00020000b50108c0a903000c3c00513a0440c280c10a0108882c40401c81101c0da003060050054035170303461100c043c01094018661090043c000e410744460003c140c1402c003092880880c002c510520303d0440c83c1c080e644140d41584001c8401082c40c44003640b90560340d440c2030701c07841c2e1080c4170020301800182c6013841a1850003c9904946160150030301c2d0140c41c0d10b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 288073390 1250 288072140 288072163
    0x12010b0a0e030105010602070521030a02160b0301050d081606090b07030b060909010915030c09200909061318050607170c03010501031a030d030b130b06030a050403020c030f 76
    0xd03610800c4070928a010721031a41218001d4009044042c40c14050241801c09c400c841052440215643c0400c030000380005c0074403a0103603010f004404503048040003145030f9070f0014500704000b40b0060280d62500390041c200305411844560f100d140342050f420804070000341c0100320b17030704044094040041a041040c00364041d41c50a00104000c00706110003401550710103131340300c1c583c2e000412001c4410346c854080800b40c5241c03120036507240d0321400c640d242640e001951465980c40000c424241c481c2501d030101106c8016545040008030019446080160900744200740e10000907000309007070380c0426441d20084115040918841c2080340c0c03a02800c5a60102042c8122158070201950800f014401d80c680d0f840b040c2541d003010011801801d15205515040551100f4002c103a9410403818042d07214650b40440d000d081074081c41003001c2c1401000c4041400d00d40c000005543d100107072a813015000000040540e50741c00d00300d140180d1039a200f6014010840300e024045d4000c6810755409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 288074640 1250 288073390 288073397
    0x12030306050310180f05011113030605060418171b0105011401030e100e0304030c0b190f0504051e040501080d0f050915030403020f030a0e0a0b0a09050d0812010b0a 72
    0x712000d584502641ca01031085078071041d001105800180d540d400943c9180c0c046c0d000040d080311840f660300c4103036001e083c1d4140c1049000c402042041042c0c003a40d0390014040c1d405000c2d0170400d05a483d10a0000e850040501c44890901c100315480c1d482a1441c200c01d40c50220600740d1030310f458034000c110038083c4000a40c14400c80f183e941d40240100c00000c0c01480060007035141903d420320081c80740c1381d005000c0b80410040040454a6031070144040c0c0f0740c001280d03903911861219400a40b14060980051101d081c0610111a0b0081e0982e0103e80e810788104a800505c00c01c48503140c0c0c500301c415903000f813030600007241c0388500060301c2240850720340340d0303207100b4620707d03000c1c1d9040c0209d03440c140d44015039048000200e0055000f075038019109004689031218409203140c19a002510038200054454260b00701c20b240c5460000d00800c580c2c55410300d801c00b1010001c040ea400e41c0907a50150f02103600100030004c00340111240094103600d5540c1550319040e40c04016800009880d000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 288075890 1250 288074640 288074653
    0x71701060806070c0f030203090d0c0501020d0e0a1806030606120506010b070503070201030b040b0d050d090f08060720060408030106030e010b1f050409110307080709061407020a120303060503 84
    0x280034000340b002d002c1d20070b07915403d00c466640d5543c8020310700c2c4030300110218007081c04132088176210701848000192141da81d090318039042c1400207190140072001c54003000079030180b548064075241c1400c01941d42c00c6924001548000c0b020a0140440da480201080e25012000880300100681c482c240c4d80702d03200b51440ba981ea2001d030081e0740030719140034000780c00810a40300198080d0b8007140c030100c005080410000f00d05070002e0001c50312240709503400e0700803066843c0c6c4140c0c48040000a0300b024507049403098180945d445e42c99000601e05410300c00c102001c130300c0c2158020703840025100064100d54480c0780c54506007800da0400e203d03827804a03080001d074030388200040c00303103507030800c00a410b600d1240d081142c03050030911003074018000c2c80300800001c40c040c1c9a034000c12400000300d810103031b5242040d078001081200020981d0042010103d000d0020302d5002d25100071001c54266010740b0341d4043e00001c0c1d84405140d1040100d55100c1070f01e0030425415401140c11200e0031030a8520 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 288077140 1250 288075890 288075899
    0x20f07260609120a27080d02030c1005040c0503060414060c0f0306010309020f0604080304030b0a18170d020307080702010e0c060a08041e0f14010603080f0a1107170106 74
    0x240c440064a0107080c5800a4148400004580307000d4040d5180b54600301050340c4e4649170303a03a0f038494070b60b00e10804030300155010701c400c0c0c800300040d035403a000c039100071442c001d290014141c6500c40304820050450300c48003c01c040c0200405054007401008094405500b130510305103503444011010181c0a009500000390b2440e003000070785a0741580d2180242c41c40d910100110010240b0413401c9174848044a213540d02916040081d0014140d0743c4025130751603085007840c0300002c100070f01e888041c50078207840140c3c205018201c15034440e4054032900c541042e00003400600e01603170660440d95071010041000c80c5601c1141e03507005240c103400800c006e90f00c0010300350300d074050180c2031a0403640820aa130a650301c144601e90f030042c0a030b0b4440c04082d1060034841012292a10b095822001c880e42c41024040085e00d80c0c4414440704008028451541d0394200701400342c0916007590034000715802e80d0150152900c100001c1407101503440c503a80310445446005200a0000342c0e0350b280440200303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 288078390 1250 288077140 288077143
    0x3030304030c1209080106090e10020c030f0315061303030f0c0c0612060801020c01090213060f030b0414060403080901110301080c0409030203070803070504211a0601020f0726 77
    0xe0003940c01da0340320401990b503601c0e800880b07201294030a040002c0b0400014921100380b0861000e052003030710108480100c0441070b4601600118042149481003140d84481800013045400c06000050080d840b03030b440010b030080e0009100340054101400143c0c10304608224a2039400380d038400d49808203508824801203c04031040f2600a106080441042c03202d140100103926039440060400301d08a500e504055080e6001558807509980d11403074644214030b041d816070040e528030358800704000352404482401d19070a81c4005040300704102d010a00703012840380401081c0416404981c2103042c180340090942100311a607805035440c01c0810035040507841c0450f070480f5a8100100070940ea11000c00c001001d100e003044042d40b208000030000181180302451045007a9201c05480b10b2805001d915007031300070492044200084110540065400b0100c235040f140143d80c00012580c171840140d1510340c05644645451188000006000d00480d0302121009022954488074031814110103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 288079640 1250 288078390 288078397
    0x60a122105130521070b0a0207080f060106030506120a050705011b05060610051219060906150809030d020c0f010c020601030f1709040606020c030609062703041508010e060303 77
    0x300d4001c140c4500400ca00d10b8514105141d040e080d9644c1d50328039144061051400c4129486010303071031808541b81183c240c06010300c1c1c0003000c00350040e0203590744030782d140c940302c0324140078010a061f0b503407000c1003007034039200e01160221350030750100e80c000b9105090090341c843d683c0c0300d101d0011782d00311004e0240b802c5040048071030f00d6009005049a48802c42005841e80144090204204041c80310003040501c901c0200d0041c4081d0302c00381c10125250440d44103840e015042248214102202040000da003110030558480f1240303402d1910303031900300c840c1d4218418525901d1490740041110380400001207480d60301210040000c200d0040700020a0b40c450109100181c40c0200aa560b2004a03a4403405820003240c819402d500d44000360b0001011030380b49070440c030010781c484048100345050030010f013500580a4030040c0740c9460240c020508005044000300e4001c3c859640e4000280c600f001031314003030310f0400210010038a1042000340030980900c1040604035043c400f080300c1d0b0034040100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 288080890 1250 288079640 288079657
    0x902130b0414190506070b04210c151e02130b030106090627121406041203050703140a0f06030503070b16050f0306040209180c030702070b030c0909060a122105 70
    0x40a0170000261108008880c000344280c496040085c1d0224110042480c018050b40440c0c0760001203c4c00c1d8106080bc5c000c10421103580700d450b00245400e207080b4001800800c2068040269448813205500000303081c0591044240000110000c920103802070518001d5402554a071051074840421040c11044a40041040708011440c14009503c010401da80000c0c0100c00c031350340380545004000d1902c00220340a0f140c0340c2084c0e4040520350b03458040c46410001c3d40c9000e1000041410307928105440c080c100b81c1c2016a5801c0c4503011100c1500400c2c0115085000d0700e0305c600722420428a1308070304407410750030000c040d030b24a0300c0c6e94058001d850b17a40c980d440d1410304556400e41408002c1d0302104c900d95200490031861441c05148200c801d100f0403c1c1c0080340d4a90a0940d8040e24102d55500004841c2c6014810840302c0c0f004001031360400e8008a039460071a0312281c000c50181c83c541d42009082c2150804004240803036048800500c070f510383c00e54503025850500884860051901 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 288082140 1250 288080890 288080899
    0x1c0201110f030a02070c0b040e0f06060a080f1306060b0a0e01020601080303040f0f060509010e07090903020c19120807050c0a0e0a0f060b0c06060f01050705070902130b04141905 78
    0x203d90007030120381c0540002c0b84034600c81c051481e2641c510301e4550704640d0000545803989400c01a10707a0234041c11640084090302d4560801c4c44e04d0801a10b8890001d20301c002014030300c0001000030f40e032040b03210112600004100103541d1502d240d45110750241541f10007140d2200381c00700340d40d407000a8803412201c1300343c051411621140c1d2402a04140c18909990807840402c00781c0c0410460711400d40140c0c4000000203840f0503130759003a0f08252071984680311151400c684107010070740210b554a611300d0110be86c5c46031498010800307000c00c0202d4002004411035260590304102d031240040c152103016008880e5940d40c004104001c0000354003d0007901001c1c0004902c451310a40c1080c1c140305410b031808182c1c030340c41c1d407a4601503801040d1100000c0e802682400944c2c10818000c41c80a442840c02a1604600d91549a5240303e94442c100c801c66002030074200d1010310101d594094000380e120300d940c85659906d2030f040d01140141c03480c85000040d0004c41c01408100c02841190b401a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 288083390 1250 288082140 288082147
    0x13080f0c060f0d1107140102120c0f0a0825020a031101050c07060b010c0203061014030c0904020904110901060305010608100312050a1701030507080f0303040203101a031c0201110f 79
    0x180f044090400050003021410702801448000f07000c10020240404c1c5113000180c031044406200011064003408132441c61000700300c101542c04d07180080720044004d5042581c03031381c0c407001c2c0b80c1e6456070041a864006c0b5851a080d015105a001c0303020b0303140d01d0003075554142c0500d178800b1250803243c064500405003041004685d0020365079410543c4599414100289400280e4000c24140a4115401c100003441c54205201648150401d10000034040e0010114900d802001c02c808102c0540064412410b41e800241003201803050100d550601402400503560356203000f4014240038003451011600c41c0c00001c240e001c402d041502107940095441010f86c0c4829400d9540780e11403c03048003080030b04841c8010851126116900075445540102283c40c90308004a08060607581880865041002880b0250b078001903103034607000030700e1000a0607080201340d20b4401ca61094603e80c040c0110046a82c1080361490100e41481d241d40080c0004002180b103486540b041c45009240800d0070b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 288084640 1250 288083390 288083407
    0x6091005031f140f060a12020a03020d14010f0b01080a09020307270207080d06060504031a0a1d0a03030509031c020a02070519230907120213080f0c060f 67
    0x103040080200e0421000141c40948880c0c6480105040741d150960013610b40078005503043c08451400203158a9140c0710f01c0d8151503000649600716403201911860503a2185414080e9001c0020000080305008000300420b01d111200680355004c0c2a80c046031200000410f0500c041c010640031690040140031103a0034940414a404851179103803003205051046000b01c1110b82c801008854041d0303c04030345411508a2581c16914290000d4082120034482040000e501044c0f040c00da860036010312160742c1d150204480100b0b01d000b120082e4500d40b441e2003000110100d80d1901440c042c1e034050003d90340f03002c07820740e403486903204075459030440030420075160800d503001d0f080c100d40303030f105407082a9669070000d4101d05400a00b401085d004070010003090030407103500a0a8003e1022010180134a503001811503a4020056014460a501c0448094682d54101c8000203100b150711105942c460381510f40d00e211001d003120b441c2c8101400d481c0c80340791201c155580c0070b4034101c2d601d1802c0c601d07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 288085890 1250 288084640 288084673
    0x2d110703020606040507030222050307090c050d091514060901060503011409060a031209090b0d08120405120c010204090e0c100f020a0b010b18040605150f0c0601030503030609100503 80
    0xc0046c401c159081c0820a20502e0100c0c0104600340f40360303035407909a4181000c2604000c000d43c80340340c401d880d29540c10540307900201034035540d100c400d0000460f05440d00b01001032078018404103040619000d1003007290701401600342e01500b4140e03460a100d07030b2141c50035a0648801c0c020300e0700714075044501c00c00d28a08000103692200300070f0700c8210300a41e41d585008501f5103c1500c2c102003541c408007400f0703040c100e12642a600c0c0d01103d88002c0422542c039604c1c642d103e400071a0440b4161900020148031041003117003a4021054102c1d581c62020b00c0d5003034001d41050080d40c000790305041001c1080f000000d064001080d00034002c42152029106c2550300c08441441141580101141000850050001c0e04d0080865262580d0b5942007805e18001f0f41d9102a200c9200d52318180c1d0a002a031a0ba4040e182c090f21444a41c0c0c1d958030442c0030042c00d80c012009180d0703031071080030008410001e020001e1402007805030786402c1142c0b1035050040d00a034144c0501500340e880041c91001101c1c6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 288087140 1250 288085890 288085901
    0x4020c0703050d03090b0f060a1a0c100c0f02060105060306040504021c030c02040b010807021b01030207051e0c120a031b020d0605150d08040e0a2d11070302060604 72
    0x5005003124125540d80d91200d040003c0c258107507022030340d078007580018002602842c561100005002400c240b800d0400500060700e107010b10703030800c00c000510044c1d1040710b80031650462a0681100e000201c0c8201e070f9400392401150050000700e10114820025000241040c16510000c01540c00d41e80c0301c3c020f0100a1000600a1342e00003c607119868000d07030b80c2c901030300b1918000d40c1c4045800440f801440300740e03960401154108480c003003c008240c0d5010905100d442540707800030a101d0403850048020380111100038005000c0c06a81711100c0900790f40c040e40014080050f40d826842c56800c0111000150f08117070050b800600c54040002e2145140c510b60b07a140d0402108412203a8003c0303511110f2036002210865614401e1125902d410b0b08504222501100d410b03442e502c860307035086024000c030b2060380036010300c1c54042643c10035184c1121080702e45064003540401502000c103d4125143c501020950b4500b1483c540d101401404039100c203a050340050030b1503261074007030000900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 288088390 1250 288087140 288087157
    0xd09050d02010309081225020a120e0303120f0901060515160f080307084b092104060e130609020a0e030118050c10120f0504060c0e030c0402 62
    0x1944d400c078410000c0c004c0c50141030a904005108091441e00303a520301c8001078065030400c030b69004407a44008460b400074400214982c0501000c4a0a140c48810f48100703c1d6414480da03d40400b00345002c0b865222584284610400803400d40c6070348414072810300b2160b1034007903c2d81080300c015420f040b00000034010210b403210b04001d2660b0340c40a80ba080c0d088070282c2e20071564010000103001c042a4031400e1140c0020702c0c0a2607642e03c9546982000d02d40c2003c4a4400c05101200c02c10901802c0d4020400c805140700b9414000c136140080700d250312402c0c60002450000e40b04411000d5541c1c1c848152000c0e41c2c100d44130340f0a0300c4031801c104940f0f44100c210340068180c9400004c90704007880d0000d0041d02c101502c0f200c98400c4d465003010b080d11040f56081d00c083c000c40380b0100200300000350524843d4404c1d0703030052002c841a41d0885009408801002c170050401e620100b4841d80e991120340303c0d5014281c10040303d440c46c00d04031755a407042c427045d981c941e1001060340b81ca894154001d110b81c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 288089640 1250 288088390 288088397
    0x1716050c150c070614101202010309050609030301080601080703020a0e151e0102070905100504180b010e06010f0c050d141b060f0603210901110a0b010609080d09050d0201 75
    0x184031915804061082182e6102c029003020503404100002c80c01900c26034059000b80024074500f60b84c405145401d2482210b40f0840b0346808403042d0f9008ac1e1203a0b9a25400500303903040c83c58802c10680da240d0080c42001214820304000140542c030101c0c0309001d50b40c0c0100350240e060300d4804209451000a0416440410040d241c40d00c2a07950280404140c480720702d03d0a0a4802c18001a08001540d48036812a40c101400c2000b690040f0302403200b551401c80e00003440c0c2c00c03d07a46a03169081036500080ca90000ba10020403510681490184105402d030f03500907400c3c011200c1114a8011000300401c180d0041c0540c8034075034040c030598058a0012401141028401c00103468001015040141e6681090b000d1146c1401c1039070310b0951014094009040700c0c05c118101d440c0f0801444040180034070007045049032a8440d11b611086c0740030040448003901c0d000d06264004c8002803058a01190b40d0000000303003820041084100c24185480300da1400d894401405095158810201d040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 288090890 1250 288089640 288089653
    0xb040302310b040e1903080105040e0a060c020102130f03150c0813050309040914060a0b0a030615050d060f05070f0c15061e0311010206160c14120702011716050c 71
    0x107513a04105050000c44800403c603015041030078041c01c0f020060300b05600990401501f8001c100300080c00b5000580d00a400080d821600e0304201d00a0041d51040c00500000340c0c00083c01506504044042d240100d014140071504501b1510403180c203610101c011801c0c0348006040d40704600381034442c3d41e001ea0140c903d0081c04600140443c0c8221004880f200000300403458900d20400c12198481c0c1d40c0c1c071040189401d07001c002000852144002080d10352107000c4014001000d13081e000c024a030181070000010103a01d03124000d015a0503130385401c640340c1400201158420144503034000c00742d0311030140340e40c070585841604c08004200406407648454000074001005084460044c0b0184600c040040c00c500d003d2103030380d413200b12a40c110b622180903c41c20150815035440c80480d941031100009101e03103082c004001d00c6100401940c098410b910a40b81703034002c01440341c40d2003640e440415080c4001030442e099000c0d94008251038005500f0b2400c81e015500030704e40c410350142228003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 288092140 1250 288090890 288090911
    0xa0f08030612011118030a0c0e0703060503010920040504080f0d02070c14100903030f0804110904050c01090b070b060d08070b040510060603020306130f060f0b040302310b04 76
    0x2524190b40c6054060301c0009001c0c4030414800c40d1103408010708402814101b001d80c0c0b80e00c41c24038124003d82d5602e80d101c0c9d011030800c0340240d0060008020150003405000e42e9803c1034805141c910045181080c080e4420101500d028031030684140d92040409003040d090460000d0550005c54080781c016500b008060080344c0c0c0d6488441c000c00703003a40540b00c0344c10300d901886134001c0c0320500001400141c8009100103030f0040340c000414002d92030940b607965031341d050030144481006265504500d0310406e0005001c1e02182c404100c450a0701e0300b8884542d2400315450b1031250b0f071000350458003441701041a03440c02c000f4031043c1c140100a1103090032682c0d100d030290140d00383c50442e106d034080c03084401038031898000c05000f00114102181540b910b2004a0030781c208900108075070503511050100c40a01c03e6001201a00301c840311035042076201c20501806610500041c0e02c1002c40c0d81403ca5203c1da92070041c052150640d2100e03d40220741d9945c1d901601c0c050340c8065000d51a4901d501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 288093390 1250 288092140 288092143
    0x302030c0f0403111203160b07141b060603150c0a0c0c0b03091204121101120e011a060310090b031e06060f09090a0818100915020a0f08030612 63
    0x405035016903116006400328200b004403208000285c02c2c290742040c0081c030200e83d1200309030107806821001d0070125969600040b00d200319900f0800d0b42c40d200103e888081d02e00d40c554908503030000301c4d048804580310389003015981c50104d0a5040c50380d000000203000c0100c0340c405004141c00606100001c600907987c0c0d03e09110041d0411000c024000c8100840c5c00401c010300d0500c0c0c030b03003d0b0f080d83c6403a04101654144c81500e500213000d00020782e94160042e4802c600e01e0301440e036040c03002c0000070502d03c042230190402000100c041c21011012000c985070002c00c403401801318440c0ca04a09142554440c040c0004c000c10b1a414000c1c095071810181c0314802144024241d100500118940b09c3c040221024020a2442c040c1c000001000511000010314140b0306403c0381110361148220480026101d800801064100105401c0f040e03070f01d41c1005c41c1c0b8007030310201844150550100c00040742e80b41e0550002a068899854041012034440f100441d0800e40252080340340341c10110505 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 288094640 1250 288093390 288093397
    0x509160518060a050a09051804020d150f2a050a12020d02030106030501170601030b070e06070f030c120e061b03070203070b041806050d03030510170a0c0501031503030302030c0f 78
    0x740f02285000401c4410140d0002801000d090201d81550300328407406022201a00001c1009009051402d51403090108000996081c1c05901c2e005011613030b00300082d0030207800c4904690141c400304009001c1c00182440d4507802000c003070b544460524240c504120740b40706510b0840c031032996080105071092501d500055020b04140d0314046183e500d82240c845070300f804181480c01e560019401400000c84040201c0c0d08540b4914000480042010014040c1c1c420a80010721a15458804408043d04481064006405210800c5003c18801c0302610900c122040701c03a8024810894a001c42c0e6a500c42c240050035580101d030309081203640420718209103074000c45c0c0258004103081007075501450000007500021001844418a4400801d1075900303084801001d064481001440100315010200010814551080301c2c00450032074194441d04164401c2e15854500500030640303501030b0007a40d00040601c07007c02c1d24549152400c800a400c041c000303100c10030003005241801140e04000c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 288095890 1250 288094640 288094657
    0x20d0c0602010c080105030c090a02090604120b060f100f36080c0f010c0215090303040303050d050f010501020c10020c10030f0b0301091a0a0605100810050916051806 73
    0x40381c0b904601c010300950344c16800540f0a52140e0601c03562038645510054000c144882c1c05038844008100007103041c09560030110400307510b1101d500a000e8041a142d0040c030090780c140003d80124030900180005591240c1c1c041201ca002060032144101c824503042c00110f42c0109003003944150303400080d40d5801403458000c240700c60511038484240f280b05c5440340c00701c07001c000702e031807403800605400803206010748504404800315906503000b42c03c60740103500c020244da90b10341e260f160142587d0080940028118907000015164600071100c060680e44140c004200100000040041201ca2008800c2c1103004800204110740c072025209540c0d60543d4070f010682d0741074403540200312442200640e21986c103204000c0b0210796800c54540c0303614003524150b50306968100a21000d0104c036840541c1042d10f0401024074140d00c224401d01410020b05002c45803a540c004102c0660710550300d006c01082041c640710241030003403004146601e2542810344050886200003040368100002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 288097140 1250 288095890 288095893
    0x30a02121501080f0c0405060402040504090b0106090909020616020f04060f060212031506070615030c210b0712150803120a020c0c01030b03100e0706020c0609030316020d0c0602 78
    0x12010310000381038081e4094a2040c00905281460b451010303559003040700c140b0700440d03a900100d2a152503580448002d80b4014000703100c00c030042d01d000c03810510309228910001e4440c820100f07a000c0706004d48809260000c2090741850303650340308221100c1343d61400b2644084400c114502c1521180940d030010083c4403602c104135850200040d0808441510340c004d081c504004009840c4246041c14482d040103681305612014545450001000351480c103014802d241440042084131010305072094518649000042010016031f030b54298441200042c484403180340081c141c03d10451005440c20001d4401040700108130650011180c4540c000300c0041c1c0000950110790300c041c1d100b25410624003002103150006120109884e040d140c07807802d040544848161956640c10048400b001209003002c000e203581310b0100c00d9071540c0910448015016181b0344850030f20b003030020f454500c1c4000c3c0c086c5140185003d85807020841000b8200d902c0307281c0c9880d003230114101d01b2910020707190540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 288098390 1250 288097140 288097153
    0xb030a050601090f020405210f01061401030c0201020703120e03040506030a0c1b1707031215090b012d1103030f09011d150a020438120c09030a0212 65
    0x8034050191500e403941d40384c02d40c1c01080100459107480c400400d0203055039000840080c540c000203810001c51445a003d40d43c00d003800856107070b019940c085d183e13501c262030410001882d4242a402d07406080c00107004035034000d141048501050f0010500141d064042c0ea01d0710b500c4400161207a0416560b01710b2a607034403451090b145400240f0394071641040c7c040240c04c20700656441404180c1d40340c004400c1c80010404030b08040c006d854202c4030262006060000c02166291601c90b124144100b111850414502c00c3d07441d4010360142d01c3c090018a2080010490102e513488915007880c1c40304c082000d014064401c100b0280042c42c0681d441c210030413040c0c2400341030f1030b00b5143c070154001d00d84006542c1d11501e12400045800442d5600141700c410f503900d002d0020000c0c02544e100541e110501d008801c948807582c2110380c00403125425000301403a94418a01c0b90f402040d000c200d81e19120004900d01d071611502510700c048000b011101400c800d82d0102d83ca030014920000203650210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 288099640 1250 288098390 288098399
    0x509031306020114060f030703060b04140103050c012709110c012301061d0907020f03030a20030610050f07020a0e01051e031b15190f02070b0316030b030a050601 71
    0x70013896401c40380c1220188500c06844d00001e484100b82c1c40300620495480c200324020b515590820f800c82150310740b007003c1e41d6947e41466521004440d02c0140010601d0000500203050f4441d1090300d20031180d080c4034003500b004513205c010103c031200142c103e04c0c18031481712145000d02401d044011040b42c22420610000400e51002030180c004805000300c100700e074080046035151040b4041001c80d500c3e038880c0c603162400e0303090640030720b041200746c00004204124000790341c000ac003503007826121203440b2a50109060110340070950340c1640c41080c0a51030490588224050850440c1e4100204d15084041e4001554460598000a0f81101c8000104203524200c1215941002400f850307040c06075070040083d4480074a1072504520250490140849495011050503280c1480080c50394800600e01c4000d1210040d21030007001422484040081341d102203048011203410300070700d42c156200c403000074040110207440c86040581d61000d5403560741d42000700901d400e01401c050314003541030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 288100890 1250 288099640 288099671
    0x105010c0c0b0d20030c030411120a05060601121a0d14102304020a1e05030a0f02030708030705071a0f1305094c060f1205010b03060405090313060201 66
    0x501c009081004000d2042022005146c1c04072544154040e004405110548000071481c0c90121016440b5110710f080781e100300136000941d40c1c0a4802622295031401101803241c003500c24030a460001000d415000551909241e524403d0091040c106912250912205a40b07001d241d0f60324505a5602c88c075146072041c01001484c00000099180152540b400340c001c50860045442603501010743c21415444d16208039690001400c0010190340000c0c0c0343c0e060004200740300740d509a220f40620407000401500c00011902c0c0c0a610a010b48146e500d840ca9402c14022182c8107030301001810008049a640d0600c02040c03030310262100d03159824100310500c911928000c0c03159201a52000382081550703e9410344100340b00400155198107c24440c0074085a600d03100c0740500981c540310b01140c250341101e25810003100c1c6540e2402c00e421042c0140055903001c0c0300c1e8100d0b084c030400104115040c81c0d00326992004000b01121720700340c000c8811070004155507000c00b0040c0d64a41c900e0484016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 288102140 1250 288100890 288100931
    0xd20040c030b06160c080307031107050a03021005030a11030903190906120e011d030a17060d0f050a0b0c0a1e090e130210030506030c0103060e0105010c0c0b0d 70
    0x1081c641040b109455001095a40c440e91390074041c0c02842140c0d050400007454175203c00f41c0000006c0d26180c00c1d1915029042c00300300d040a00c4180114240842c0c80c0c2042051501102d400422a4800110700082a03406500c0a0608036005c2d4a400101182d41001001940220b4145004540d034039032501242e60307103080055000c020070585410800ca501d9000c0c44051407003410a6001550100319485030f0700404402c10711041c2c031010418804402d9a0110150815000035190303094450780c2c00c004811681030031195940c0c0442c0d200c0c8072034003040c0b0b13002c0c42c45040d5210b00d04171100201c503511a00d042c50f0301203070030782403501000914000c1e256000510003000340d81411404100b0030500409804003049004000540020720300240480004d0100c00540755005000c8201812a040000780a00f5080350784a029200e0340ca031120303565100b80704800484280700c0c02001641d0030314004480c1011010350984811042101c08100c81e29200010b06141e0880c6000080c0f030300310004543c08100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 288103390 1250 288102140 288102161
    0xc0606050a0617180d26042a030f06020304050a1401050603010c0c050616020a060e01050f01060e090c09010311041706074b091809080f090d2004 64
    0x1940e001c5020010001036141179400050408200202850302100072241804828040c0b0140c41c406000c180910702c400320b21650445102800c0c041c1207881818075405161100410120344503400b80c011400b01d502175038120748901d081d1640b0506549406080c030644070b208150030b075500c005015091134248900b0451401e94103102848030301d0f03512429291000106a858194013041113400301d10f20034403080409070b130300202c10020750460000c2d45000341812603040a040f4503100021403c50301908070780950750002400b804141d83e41542c005025000b01c10306905040c1c0322950603aa0300e5040c00608068801000812b89050380246603d19110380a401b2409125005204d2484400d03101c4150750208038005648040c1c01c0c2c2d40000000e41700c950001c00000e9510f4900c048400d6500503c80f00480707001d800320340c1c007240c403080200341218821280140400300802003809451001c1c2d000e040c0800c0002c026030b00e0700c032054a850b2640502070390783c2c000c1102d07401048111031410748251000700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 288104640 1250 288103390 288103411
    0xe1009020d0f02030c0d03050a0f0302030919110616060516050301060c020d080304080309120a09180b0a0e0a1104060c020d050f030f0a09050d030504060c0606050a0617 74
    0x18086900071403915052074a024004810b407078051419520100921805d18001400b01180d96449007801400c83c2c1005803030200148100383c5240000307119000b9240159080009031401030700403810340061510304203007100d440354541c04004003650380a010301080c0c40580a41c401600103840d0031001c6901c01041c0a2aa0030f0614203c0d403407541c09402d50707064443c02d051042420f80e6030300024428810908000341075900000030041000b00c114091401980843c0171500400c07090886154a4040d04038030800060000d80104488003010b1103407810502284400154144400c0220b140314005402102c1841c4d04070040c806505558842c042c50580440c20544c00d1500b060002000d448850401911481c010b4445030305021050004141f0100580d0460f0780d10340f420b1002d00310942180d42040c0101d4440c10780081e950034906111403040e985551928605420014182c0f001c410108081d20300c43d030348030740102c2d0b0f603141e40c0e032601c3c0584001d40380c207082300310f00c850b4008016038020141e40c0c88 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 288105890 1250 288104640 288104651
    0x91a060309030a26010e0a06030803040f06150b0d18020d03020606010f030608060a110c06010e0907080102070b0a0c0c0f08040e010b0a020c010e030c0301050f070822200301020d0e10 80
    0x60684c0001014103589600001c0217064980d4031210025020680014252031400003d04c41048074030708240500310b205120501808010071500303c06101e0521545182c41c0c4104544180c000156020092110121200801003040360700402c406034540c243c00c802583c000e20520550f503802c101c068189a20750728040c44480c0c181792040d41c81d80d4010f8400203505813a507400701244407094007695032044041c0103d5400b503075941d010450302c00090b900550140030303031803001c1001c0c681030089408164100300c003101207484a9490400410810001c901040303111145240000c5a40313200b844410301600300079407540d043c41000c3d84c01c6041a032182d00480340030010304c0a040c1d00031401200070715003420918aa810340c500030a003403140050400c2e515500c3d0a081008407521030f000c490169003180e0f900382c3c0380d42d20020102d19000b000c20b80941c3c8000a8071007c800100010020a000380603110118051000d02d00424203a800c01003c1401c459180c0031140b04004041001820381507060009110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 288107140 1250 288105890 288105947
    0x5010e041e08040506070f020103050c0f0414030309100509210c010c0204060b0c0f010c02030703021506030a2010030c09030201120912020a05160f091a060309030a 72
    0x7401040c024118149404107900300344603112081c0c4005100141c441d594465071032034000344916580d0b808a011902d054003003400d0f03484020980b801c48a920307840c00c0c949030810b0612583d00140c401c4143d45840200041d9045441d07401c421964801c00d51540c649030041c41741045585124410170101803080f074150680455000a2038144100003802c098020100750700105014144942010b2011800040d140c954060000340700c135810fa003580d008118410041504036243d100b2030b100a00103910200d403030143c03000b001c64541d0700958000c0840301079a050755161300520380440034807801e001140b01c071104031307081580c10b080031201d2038030b420040340c0c080500140144110340030281c100301841958640c01c000700d5202318010307170b00002d007071042d0101e00800035540c440000d8103c03824000e07681000144130a511034a02642c840e100c11030340c4d5504215000b401842c40e40c1a003007510f45200300312115034407100021030254880170050350703440c0c00e81c04025100300c42e03c10300d59400d0401e6002048 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 288108390 1250 288107140 288107153
    0x81504021e0a05030d020c0301060f0506190c02030703060e0f1c0309020303070f0f210504030308150405100f060503011202040905030f030a060905250e0415030c0905010e04 76
    0x1050030120701109a034901c1200114080000741c0e00084e4262103121070701d02480d9000200e904170510214000e010203502c9144075008141c00b48289038010070140309015081c03036880804a490311680c94114815019500024503120f8030b80e000f0b8501e60354501140068000501840c2d0a55401100034001400308116401c0c0c1d015103200d640c000c050350f07582c000c0210355040c8100d0340595080702120b0b20444540c10581e4400c050003504440c0040780b04401000002c0702141344c4c210070092748483d42005c0c034545090f1286000100115211032085074000020b41d554411b40d40510041031820814504000b61b4500c0c1c0ca00311340080e402d000e000e0004104401059074400c600c40d41c1030354007181c0f101c06460814a18007602184146080340030041002403c0380780d00c040c00b00c03129510284040c0e1625510441c0e00340c0389014440f44808109000078501d40602c0852007142d901901c006080211000d14081d4208281c200f15400e0b154080e0400150f0f0240c000c0d01e0140c4100d075162503e07810941c0d42c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 288109640 1250 288108390 288108409
    0x110f010807030c11060f090106060c0506010501080a0608010e0d081003020d11040e12030601020d11060a050c0409110903160e2a040902070218060112020702060c12030108150402 78
    0x1001010380307943c040e4a81e03030b1190a4440207000100112101402c041080315060030003155010700561178a40002100c0344a030416004254101001d040c1990904004541c001c000610f200c941c00c4d202c5100140700a801d01c80d079402e40707855801800243d50314150040544502500500040c52000c009102682c0c5006202d05d8540c1e0200f41d040c4400400030110b005000c45507600d90590140c07030844012403103498011842174100768259061490390100aaa58030500c50030007030300340d0100c0c0000301302c00410f61001c2d41044101050318186a0754456a0382501c03000c46446010700000704664486007020010140d0441c0c2503180c00c1e40250424100301d42c2010000c2c500d0000c0302520070185006060003031400d6008036030002c0550f8035500c1da01d2142c0a540052412800384021000421400d03421003500f42c01444160340c0c00b00e26400c40d402c1c081c0690010002a6030001c0104403d00c0039007010044403c1c0030a003080340e0b0b034896260400060915445c4242c0c00d00806229040100507038601408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 288110890 1250 288109640 288109651
    0x1081005040f090b16020f0d08060607020103110409020d0b0405070f18090507080610110d140904020d0b121507030c170708160903021e0102030f070f110f0108 70
    0x81010b0044261000f03008031020180542820406100102600c010121440b10140e000c880f160305807005003a580e010541c1615000407401d4021980700d242480c000c1808900514002c91510340c0c00100120700da1041d4040e46003030703a0000700701c240d8140034000c0400c0303224201c0301080546414080071305030414400400c010405400d044808542240464074060218008100800e10303089101400056054410602c02c000302e01458400ca84200b804845079068080900728024111700143d844100515405130b41d03800a0046000c152101e201030304010103500e40209601d10307241d05119018480700c2c2d00503819040301042260b29941e205140c0e80044440c9400160040c443c1c0003198006105000c08450110041c248400d0552140306580100010350320082d803074040b110103407904511444000c0d00188a00140881e2859020000e4140141030040c0c80c40d0001a2000c00d40700d901160080325030704003084091090007060784040400400a54041c03101d500140000781010600500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 288112140 1250 288110890 288110899
    0xc1911030a03021606020d020406110d170709080f030a110a081206060c030a0309020109090b01020a0b0c0c10090303060509040b1302040e010c030902090f011a031b07050c040b01081005 81
    0x804188203d100d0742c1d004c14498129000b1521509038204010103544503200e200c001461400b0b003901c80c007a002c41c00d03003184455912a0f1030110728001d842511050004c00840601a04840016404e002404032000c900081400303542c1c0c4041500c0b01501c80703c1c2083d0520010ba1040040500140b5030300d040324110b103004202400141d40d03040028001c0c0c420407900010074000030507606040d41d01504440c6829100741c90781c0302c034152100c0f845402c55284141c0240168456000c3c0c0c000709028a101a4000c0100c1002c03a00c0c00b407201a59501e080c1591072003110460307444544030189541440303981c000d41070443d0a000e40c1e003025104e01071407aa01414414482041a080c4011544d4907480800100401d90081c045d809003003d0141c018000610305074040d00460000030305148800106a060700c3d5030f6020780f0036081001e110070340f003908014011040d035551034003268191454900034008041c070a07001403480c2c0040c1805d22055035008080326042c81004010700c10b01c84c0f00c440f215400d0300c10995 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 288113390 1250 288112140 288112147
    0xb130c06080402030a120503040204060e0c040b090406080708070e010e0f0c0a1806030b03060109050108122b021804060f05060a030209040509060609090a1a04030e04050c1911030a0302 81
    0x3d0403d11706010003005150003003002c1d0700326030b00200554400d6008403003c201c85a5903914040c00d091044800d044a10b50401c0103108040000f40070340030103c00544009540e80d220210305190030010303088500700307a1000d0f0b0100038030144c1000722409450b121240044500f02951880301c00315014082900c0f24001080126001d0300c43c03010621030169160404000c99540c60000d40100b040940e404c0c028015000085601401801164101d030011001000d410102012214064020b2540c47c0c12a5950112210001c4e1031913114101841001000603039940a41c6000721101c100300f101c4502403424040304200d00c04588507548200c07070090b103c15a40b4844000110002e03c24110050b61041c600000c2c80490700d000134000c1d02c200c00c25204036040da100c041000d5a1a1003040d40104100d07040040c0110020030500f00311303003052103030a0220320407c4a0000909545080304c5603c0d05000c04504200700030201030b41c2d00000011070400320f2040c1d9500e06c4564072407058142c560107154000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 288114640 1250 288113390 288113393
    0x1c05090d0f0c020114120f010911040e06150d111b0a0f0803090f031611010203180d02061204031e11071e0b0c061501051204030806040e0f01090b130c060804 69
    0x60101d4400c44445211201b41d031410040141011000380500c0814526140ca40020421401c003100c00b914401e003000b01042d0380341001c1001c000301050400c0403007a01030004c8101400b8500407058011080f0580d291105511100c0b8107080c1e15000400f0700030303840450508041106200350490322500203025959903a50008140d140404002a400303a07071000042c032543d04c4540d02001c040c4544a20115000e403542c84004980da4000c04056250383c410f01700e001d40b920314140c10035000c00d61002e005c4c182065881c202582260f141220141c011440002c10003204040d80c0410200c01c141500b02240d80c1c40400401c0c0d03507141303454010100d45800010320b064042e20a0b0401000821941506030765070080070161585488007075460140c1d00d0201070000721190302034401c0d01e40c66600412461540d640300d0318119480100a007038207420940e228106180c00c4400d020002c0003006280011134070b0b840f82c0ca0640085100200010220812140820001440b0030031240032a4040d01c0d0410301d903140c9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 288115890 1250 288114640 288114677
    0x2d05040204180503030f0f06060a050a03060f06170106111f0e0a030c0b220609020f1306060809010b010c0b04080c0303010e060123030601030f021c05090d0f0c0201 72
    0x800c0005001020303462014041000000c01035110746d06200c2420f4990721910100c0074210030030340b16594069010300c5408203092085000d80ba40050030b280200f04155101d24aa04e00c03c01346c1c01c1b81c03001907601c55010080030387c082400b5004286e00d2801c1e034120f04001003003d46405280c407091051902031a00c400c0048060740002c02103c134020240e401c09003143c68043c21546c0c6218044428060280c000380c1100120b600d408a50304070410601e892880c20750360031004044400742240d00c120014805507050b21060144031000000540c0080e0a500f4007902808802c2c00405866041e81850b1511049980c0300c0040c82c0b1003540820500003d4955250076112401035100c4075806101c040000600110f0b00c209039401408282c0362691400f030040b0748841c142c6c0d520800d0083d41c2d40c041000c02c81c0e55111768001440c0e69092840181003400b98030700e0b4001d805440c0c68845990b900d9034140b103038070901403018401090841c00c00044415514038041d007840d03200100a41070081d1103203c68000c052 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 288117140 1250 288115890 288115901
    0x5091903150b030609010b030a02040e10090c090b040605060711150304080a1d01080705130801020f03040507050d0b0c0304020d0f03031b0203070305030105040f061703030403032d05040204 83
    0xe22001075411000d0310308000d00280321100e050361080c81603801184010006102d044281c04c0301402400361030f01c4507024840076126200b180c0e10644940441892004010b108280e00544290005c024852400c224a8140c42c80d440c84544510700d882000c0066564070b00c111100564400102d078885248079001603422202180c00722201c000020801040000c1c4400800000310756844440c1080f40c42c040100040303031018589800304d20601d002c43d0400703024202070414001e0002d040c000c0662110b080d50b003a038100722190b01d00004007200740402c000046c00a01c01a100a403910b10344840075488030344100030003501e20401c08100101081c00c2d5183c0744807900e4000d420200540070000146001070040126860030603074132002805400000d4804000c6558231a0190343e01c6085900307100070040141a48140d41403026a20100000d0007070307140d5600c4458011140180d0744910b81400d000e81581c1903401e50b051803010800072000d00c50415544462000314800c000521562a072001c18001d11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 288118390 1250 288117140 288117143
    0x10e0606190e01060801080d11150a060b070b0103140303040f060218061b060114010e0906030f01060b18150a031a040f0c020c0d0b010e0a020f030f09010b0a0605091903 74
    0xb040070001240203500072800504850390138080b206156201c5a0460708000501075101c0d580c0c1006c0c1c9144095401690382e923403c8506040300042203950741503003504a0380328035004c803200c0e40f45e44010401d001010f03032040f00740189180038528516066940d40020b002c118001800f4550204020384c550241501e480b8403040d01a006d44e60b00c8010b01701091486044080c61030040c03140200101e00c84032020001e5a4192068441c0b000071b00c100c0c02040f0075402d006100c260035100300c8903442400c520074040c50008020361b0990170354030601d50185c100c0480414032903501034514141806a0407005100703ca900d00c080e07190004003000d03008001d03424070024105943c0c0c81801c0250300f0395445850b5114a031140d1040c0c080390a10020b000500507956003203207016194522a9004101029901c007105030312280000b401840d01500e0300c000501c0f0b8200391440c0030449400e4040128004e424417590024170f40480300c404c02c103864854000c1030341c8110000d50b40074074201080642c040010645210185 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 288119640 1250 288118390 288118409
    0x60105031f0f0e130b060d05030c011b3b060c01060801061806150c08070b07080601081e061003020904050c070c05150f03130f0b0a0509010e060619 65
    0x959440d150040030030243e000d0702c12070380c01c1c06001c1124031542c0802254000c1e4040c40340c4509640e86001c12152440b40902624a8041000002ea4400c4203215000c259007100148140c02c1d940118001c10740d1102c4400d51892070b07100f4180703502400c820303150381c050405042500d00582d039103034000c80c060380501d0300701c0307040e56003001004a203201047d0800800e48400c140010b5411007a070038130700183c074030601c1180c0301c16080702010260305100f520071600443c05564400c0c07501015503101e01d90a80201e81d21000070303020400f40411581d0004060303400c100c003100c082003452040e00c55030319034004c0a03000364803c404040a0b03017605030298041c0e82208030000c004005500c0c00d100d4203803707603004460465140380100d00126240c5003903851000b01440f490400c0e424454095443e440e298030140146c00a141c091441e9030000344c00618040d5aa403041454038544c0c14412498015140040d0a08201d40d04101110b40e0020f40046c500b680054101c61705520b0f0448d0884502d0000d8944c2c105441c0c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 288120890 1250 288119640 288119701
    0x92e030807060501031407050a15140301080c01120b031c0210020a09050307050607050a08030a141501080702061311040f050c071110090e0a0b0406120516050906010503 74
    0x28484640d1059048074000c000d5060600f180c00d808684407007e0340682503010b24440c00c00d00c202840040100d0605400e4102030174011000c0642c40380c1c80c1c01c00d074040f030b00e40da00400400d00256844420404500e44d410024400312004100003620707028840240c4405d02c0d06031104907100e83c42084091419054000210340d0b403141c0b44001031407000c0c03c1c000d2502920a82800158600304803088030601d0342c01c0070107400d8a062603603403030a90740d001500d080380641d03ea50307000345c1440c00d41120302c1c016072038030800c2c2c842442200c0000d40001c80041410055410050402046024100007650881d0b130118040011125000000340100320310181840708501c1c1104120018002000401d002070260b505c000c0c8144e40360f001c00460300313244401c002c00101b18210420200900c0b014181c2c000c9400c2c040400e040309070201250807034110f64480b05415000c56580000e2200030310100c402407034200b44820f0b0190501c808900802c1c405002141049000000130f944400d549000180c241d4000c5200e503503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 288122140 1250 288120890 288120893
    0xb0c011d010c020111070308010e0c09030d09080d0915051b070806100e25021e0106050f0f100e030703050a080d0e01140402040c020f0111030f06092e030807 69
    0x2407840c40882405981780803240c40303855081d07100751000c0641c19070316004503a00300a503880c0a11000352404100303810900000300703141e40038040050440e0b441e0b600e2448041ca840300c0d092421040b0040c00c014407166807801c4c4a42e401e591116546281282481a07880e0700c1120301c61402c01d4104418011405064000705a0407008600c4034096441c90916121a0f6140c001c000083d0500ba52041800340005400400b90709507205e641d14002c00600640b0740710341100012007440740f80740c000100d0b165901c002c00e002c140350408405407889010750308503103414080c40c00305406e00000304000c018094941040701d00d40c0d0f01000208055a400001d07280500328030700e80900580c10012141c1c4055090856403400d0791014460341102070300400004070240c4030b50302444001c2c112543c0000c1180a049400985488240680040e00003205400fa542c1e242c008480280c0d8017001c2c0c1800c2c45001018144001520180c003a03203a5800208503090381085a41c05103801e00c107540c3d1006242d0000441c80d0070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 288123390 1250 288122140 288122143
    0x31515070803101541130512010204180908041707182703091e030c120b072d0203030f010e1b0d020903030f0705070902130b0c011d 58
    0x40c00c6507007180f0700032104c1c0045941951020000000050011110300c4c000e1030034072441c0100146001c03124407101024550610035811a40002c2c0c13100e00700030140c00c04200c0d50400484060890300480021400c0500b01145414a1043c110440032410341f92010720052102c0c0303e044500030041808118202407080d00f5050319000c1c1c51142c030f00490040044030710030540364064035aa2228000da072100c0c03400700d00c0049015881c05802541000010f40000c41e214040d6101542100c0c0d0001d004007070f003450351030030000b800516080b0702480d1031030181300360000d00e120640b04e802c846203041c007054130340740c80c0003003000644030b900105190400d108540036095000300065000c0d40640105d80c0c8681c0c2c0301c104c080c0d4061030a5078080071007000110091240b07680b0302e01400ba58105408050316011545000030f2640d04280001919104001042020000c080089100900402c8030941c14038400d024a41c030191410700c224071903234200003030b44e07040b03080c084d8001241084400c80c407000d142d004c805160b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 288124640 1250 288123390 288123421
    0x405030114041a040b07050d0f05010801090507051f050d15030b2d0a0f060f080606030706110d120212190c020a0b060607050f030d0c08010b031515070803 68
    0x25200d0f07000e204081412102d501c45881d214075042400c030403041c1c8480e14101c5940d4443e50407011100d43c0c0380098103000100c1e0003480e0080480400100781d0039501c0c00e0035400c03c001540643e02c2000880101200041810411880c406040c01c2071500c4607041f25422001c0d0a2112201c00d040031020004001c21010000c0c290040c0c515a0040a07403101ca807110900007081c60396094a80c0310040002040a21640c02040620034114070100c0c01c1c0b40c0c1e420b41503c3c0d60810b6003055486812020030004a424100460401008130303140c0f004454625550b1a03489000d02e000038400c2100205000068480c5501190031000e44610300381014900b034901100d54201d00c081210600d130500540d080d03031510001e1460010f907040250715140d6282d900810405500c000012103280c02031410f4000e41d1401480680151140c401c1c011403501c019010043c400362058112450380c00302801802010102030103042c3c0c5428042e40d8400384c9400d216100070060040c2d0100801d0003000008200301c042268000c7c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 288125890 1250 288124640 288124643
    0x1201080706030c0f0206041119080a02040c170c09011707090801060609050a05190f0815010e0702150703020c12090301140403121107060c0804020a06052706040503011404 75
    0x100960140c0100031121446044140c40050f4081b8011401041c5010a0f000011000505c401c1c080c401c40d004401c142100d130381c8000002e0300288001b00c25414503006201d0100301d20b00d46100a03c032008100e0700030003000b900500b018040410746d00c146034096060100c4c580790808040a10380b40c5507030b000341044458020303100b00b0350a14000242c01d074042c1c1c0d200c2e000e0701c000401e1841d405040905001d5041000045200b40c1c000c00e070f1002500750340b02030204001d02161005405105002c009071030b05494103030720400960343d44000308050145d0100d242c82c04070140388601070b415202c19600b10301034045c41c42c0c0b00c443c0d4001c90b04801c12100480e4014451894103400900400100d44c1c4c2160002e24116006002300d010010034401c094919448010b05565542c0c030035040141c0d0351900c108640c0b80100040104485a05010075441c0201c0004014141407401d0351400341e021040d8641e494070800038401e00c074084c1c00c540d15140c0d5050f00703803409400b0140003000360306040303070b011255010203440 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 288127140 1250 288125890 288125897
    0x1080d0f03331e03061406100c140d0c0201200606060706091e110409030203091905060309011401060f0918090b04050f0d03050f0f06061201080706 65
    0x5110426010740216901d4501189001d82e40c01c641100d49071400140c2d41e44200c14140e05080462034483d01201403040c0400c4080980c0c2e658110b00d400d50032508000c016110095110b030401105a59034404d207ca500c4203480c000d0080c143e00d140a00e01c80c3d014621800c4140640141032040e0b59001e0b8200c20098000d80e82e10500c1a000030f072102ea0001800c2100031103412240c001141410014003e2000c1440b4204c009016400d94940350040c90383d90118103503071400c1800150074080c106030b40301d0501c94103ca040090031910360f4065075074810803100780d0290f030b101d1510003106650032140b41c0051030050300181d40e03440c00b0a4124002c00c1091000e0458094080011805501c19404e89840c404162100c400090030081a00915001c441302c3c40143c0d40c98940000016810b44032250046216000038001007009003500342c282900401008101031070a001c1040d083c07001c5c8112608101c603440110740c0e58a4080c00b25846114070001c1e4a00301e05d48130000205aa4001b07264011a02141da = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 288128390 1250 288127140 288127157
    0x30a1103010f053601060603050a0c021c080c090406080309010f0f12050a0615031a0f06030105060307031d0c0306011401050304061a10020c0a0603060e010e13060501080d 75
    0x3190b00201c03002038030060000c2c400252184114540700c107a44070400030b03440c1c071096020401e803905030030f65400750003000000303031504280850041389001e0843c2c408401d001401280110110f1440c110a0074000c0808129501d40400c2807581c04a084078007062001c0c0c414000c041e1121406a680e81c41a0903282c0066010b0072003102d43d52040904420280c196030710700e152001107440304000391501400b1021100d0f038444d00010340c114400542e0f0580070058034041036041c1108201c0f1091221a1140d9000f10301000151845903030f2042247e044d100122111500c903219404103d0007031410400801c021600c0c0c130305c2110b2900b40042c40404614049044903600e03a252406494a00200601b240c0070400c01c0c40400c0001d400340d0407541c420214003507441d60040905000501483d0350f85204070150b0000070344d29044c2c4c204084020090040c90030244444c516100759200341401c1482030740c00246801c00031030700b03000600c034002030b03d1071b0400307402d200a507150f918041d150750103e80c40d14041840700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 288129496 1106 288128390 288128411
    0x2030106152c0a06050c01020c0a031706010507020d060b0f132a0e010c030201020f18040507170a0b15030c0306031b090a020d0b030a110301 62
    0x240d54001c1c0b4186036401c03001121120b0807202c04602003000ca02989a10764048620888240c0c2c070749030f40e548215403071450090146221410890142050540500d079100ca44122684c004181c20900c42d200c400040d220381c46034041c000d40043d580d02e142400306070079502c85c02c94924064590010444400c0000319030101070340f041521191b0740c0d900040e03884444c110b954210740842000c8205400d00703081c0540801c01c50429681040612141031003014801c2d01902d0410807030540c5180c50341284214000b50480c07102c1e102c0e0040b89000300042d01c449c4124a06a0007600380020f1030000d403501c80401014041c810080ea030881c5021206030001203101c401903104040329810303541c503401c0070340405040240da60800700c25402050b00c40c5045942da11001504141d5200300184da8004a00304a03010344103906a595060054403034060500c80e4514035201140301c01c400070480b49511 = true := by decide +kernel

theorem cover : BRFrame.Cov 287949640 288129496 := by
  have h0 := BRFrame.cov_init 287949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 287949640 ≤ n) (h2 : n < 288129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
