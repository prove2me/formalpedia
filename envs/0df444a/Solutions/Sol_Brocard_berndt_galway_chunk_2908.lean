-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2908
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:06:22.755977+00:00
-- url     : https://prove2.me/submissions/79ed344d-60fd-4791-8b5c-961f664a8af9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 522841726 ≤ n < 523021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 522842976 1250 522841726 522841729
    0x6030c041109060a170a0c121a100503070f03050f06190806100609140a03080903030903060a05070323040303020d02091c0203010b04090314030915070504091a0310050c090a1205060f040206120402 86
    0x100c1403a012b0f03110310a10348002c10940c111001c0c0d4010107040e03640c0e41c000d11885c803095049840c05e0b070f011211000c100c1e0014645260100d141280e00c2036050030038800558540c0030a1a01d4401d481d62351179413035000000d014003680102c409001780081030300c82e80c600c41313442c0202e001405d940c0030180c034424002890b1405a103013002100c01219000d422207500c1d1030924211001841e05030f441e00006410b00c0c0f010a0284180029042c140054203a8004203860340d6a099000751701200d2a030b4100c3e0b0f002c1c800441240d03282c414039504d82150000424040c00948101070031950807203c0075214520340050040825803002210384024280d44419580b51200c9550a10f003070342c0400c40480c0944000100301150381c4c00f44c041c0c4100c4111101c02d001a05100780503250329044148250b070140e02c03290b00f05d1010f0032a50440703600070035502040c43c940f0000401160408046401050319034507070055400821000300402540440c025440c001d49060940c0015118451984049099996000031a095 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 522844226 1250 522842976 522843011
    0x91003110705070521030a05091309080304060c03050c090d061503080d060909080f031005090c12010902030606070b040503130f03140606030c041109060a170a0c12 72
    0x81a5100c15050344440191a21a0307070303200c242c0a941e010300a21941c1d940003031003441d408032050071070001a508051194504a03401e42203e003001da40201c110690b280c211a0610880d8400d40c05408041e9403454141400c909641d6180f24200406152204010815405800b0b59070fa05908031018031030301d040c5091480c06000c0710b01004ca8988040d2200001f0000104000c2011f040c1c4040c2c207000b03056490b6905002c6031258000908000390402803080d22103a80802146e01c544502d58410b00f054a88000c5150890100c5980700901c20006920014195009080303005114003c000e40ca5031070002c0204006019803003008142641000100b0b08001040c015500e0001c0e0850780320003019551110480d804c2d0540c401a1911410580c072084100ca0101d4481e101e00c0c00034006252101551091000801c1081041c078003e01d0b081c400e84101e42e90303200003014020001d030b07900d8a0030280b600200c5035400001d03100245280ca004000091950030121100c00e01054400000d102c05245000103407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 522845476 1250 522844226 522844241
    0x20a03020a1b050c060702150406020c0102070b1201030b0a09140313090e0a03111926090a0506090411120f060109030c0b03130609060e06100b0412030c0c0e09060604060308091003 79
    0x40c80c01c80401d000c1480b4bd0b002595a0185409130300711582c403a07840d2607003400341c42950500e50f0b280316640e0042c0302040c89803c815030000d41c01040041c50790343c16200da420040080c0802c220faa003001408000200c440d00d4120040c0500c6017082000203480c181c06d555070750000d280103090140e40030002544410074401e8200741c032440e80303100c0d5a1340020326201115000c001c1c40c11019151002e51030b407400305038005907072100602402e03946d4000d040c641080516009412229400703522401d0000440344072001030501603d10038400031040c21700c000f044480ca14010b2269040180301031707080002c100461000011142e0b200f080c51340d2610f619400700341c00880000e010b000142001254000c0100d03651062800855810941d0000e0f114000d9203082c110765441015807030407003030005200500c20344140000581c0b20f804d0104071008284d5803070b0751a01041c0d00500c0025650000c0162024090080651001d81114200000342c01c642e2613200030702a400300345004c0d20340c1c402c0d401802c0340a540400c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 522846726 1250 522845476 522845509
    0x9110705060705030405061021020f040f06080601120f0f03091212081b0a080a06120b090c03010b13150902040f0501020f03040602030901050304080409020a03020a1b050c060702 78
    0xd00a01d00080301420f20f62082c2c43c116641d102c0c00c0005842210342e10344040603240b600040c9142d8001001c0324104a004002091703a10404403440c411031541d4900c0f035400314078140ca10110f81c0501c0c00c2592418510140e03c110901e0409090544c000b03041500d00140d41c0760700080c08580011641000c5418201ca078004e0000d1480001010301484100f4031a0046510745a403010203541d50740c00d5038944400c01c1e11070316030400001c0c040310401900071074100d544030108010009859540303807503031008032a07000c10640b038401d005418008204018801103000307400540080c8650001480410011019180140d50303540d540d8581c19850401c5030785000003441c440340e0664440340c0b110240d144181c8680700719405413140c0442c030569250044291400c86040d03801a43c10150300300010744c0c09600041049400e03100403c400304a900c028409402c40070259a0010303143d144034400030f801540c21002c3c080c083c0101e055070400086000403407500c1c100060b182c541e200d110a101041240c2542d06c200c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 522847976 1250 522846726 522846733
    0x315121101180f0902070b131e1103011a0108150105091e040906020c0c03070b070611070c0f0302331b0601080a0b1815040201170f10080106060909110705 68
    0x120400250040c0500c28080e1f01043c245440e2514000d951231103005004201030070034580c888d554407046542100040c05120540d05d00400e2900180c212030604219110441a0842c0b508040d640700035180da1010906c6602031181d00031100291503805101405403058581401201030070a0b00c05003501383e80b1014006008032200c0f0b24010010b5002801500c0f0a4415440008142d180c0041d0520880d01d4840302640f0300080c5803548000f07044082c510014580e4100300d000005a9135040c4800200311210307004a01504510401001c00700744443c401e602840e840803c0710321440030b61039030245c081000301c0035075903220411940c40c030f20008a501d805c2c034058840001a0700c4004907510000074400c0740480120781d2192000fa03a065589a410455603200c03000c046204501c007501690024014100b01d00c0450070417200284808003203039400a0b40c40c4401c14030002603040303603050000d4138982c0003e000781400c11354018401111440303861100303900d45911001c2152200b040307841d2a9045800c0d0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 522849226 1250 522847976 522847979
    0x8010203040b0609360f030309060a0f022107030b120615101205041b06050c1b15030c160b090606060a0804030e0a150315121101180f 59
    0x503016290b001c03110315024040311000170324481c07180c070484405000c3c00000c2021402541a01c800d88040000e108500c910800c032420000030303403c0015602c15841500108074510b0000d03108415500c00e103c201441a00501c401d001400c13001c04120003203909200812401d41e11283e04402400801c0600341c0c00c40400301008412800120341c007849220000421080201c0a0080c8150712080c44400400641150501c8034070440ac4e030000c0f500140502d203501c0d2050085c0084a50002c41e662042000c584005400045408140b080d401d10102140c03c9101800002c40801c18121051072540c03000c9800200281140541d281942c180100d03803c4040f5901942d03283c510600300301594110700d03d104120007d441d91410038122808d40c4aa5078a012041d100d41d58152052000010301d030380d2100181802103840c4a0ba05803803281d8114560300840d400b4005400000c2e51205500305021010850700100041003074113000d203101c62000c2c07070100b141000202e12500715040680000306c018800400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 522850476 1250 522849226 522849233
    0x80724020703030608210c0a06020307090312090608070e0d0602070305032e0303110f0a0c330f0c050d0201050f0c0901090504050a0e01061e1a04090b0a0801020304 72
    0x14045040c800d440802090361940e82c150360b128070031b0460040b40e0f10b000f410800c00e1190440a000034202c210b0444910741129070380c0c002130b604105c45010010f0007410b010400d0056924138000a690303542450900c45080c24801070100000400d104280141015400c04a44030341004502240c0c011000315220901442e000b4001c0d4010307150110464951030908a1003000007405070040004034a440160900d95601511040e1482c95403d016010340841903000800a100c88175100307125029040b0b40c40e0a0844000008200640002d8000314145516031541c41801c0b8804824525061400a4070341c0c00c0402c84494002c1c140040040c02084000103080c3d805400c4207005a1101c0310184550ba151007061081e0f00a00400034002028240c040040b4101580b01e15000701d038040c0302055240c0e620002c6825102250310035603110220440100240107851481c0e400b5001d803101c203848121002c00a203219001c1c6000b0700c40c1d0555141c22070030041c1d40383c5074140018402017009540300d150606 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 522851726 1250 522850476 522850481
    0xc11011b06020a020c031f0b2b05010f1401030b06151902120f03041b0b0714011b1e0507120807030c050406170901090203070803070c080a080304080724 67
    0x1585001362140201c040308900e000700310007028000190a1030510700004a6100c041e14621803000d030801703511141d000c0c040540080e10b16a02030844988840c044072443c099007154901501c54103040d00c1e180d40007062060703803600310741100d4104148003616201c91000030003040742c400d11a81c1980f800100c54400410000c40142c8412181d000d84a00108802c11007110303104029842c1c100300c9080000078000345080d201c04e039105040c0407501100940b12501c4403c2c42e8802c1c3c200f903400307241242e40852030300401d00800c8920100c1e5404000340c9903d04030050072240903000c01040016618143e0609a48220306640e541c51300400c03040750003c0000005480041c043e1205030000f030604002450540c007a404a40840d40d45070b8409100000341120840c4c440805030404826548030f03a0a40050b941c10080080030700340030782c061507885119291900f040c03101584154a2600f1540c1000048bc03280c00aa96106801080043c0c0e225800d00c0c003201e418000c2580d001101050a070036110010155 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 522852976 1250 522851726 522851737
    0x50c210906060108040f06020307140a09080115080703030f0e0307030c060210140a0e0c030f01050609181b010e030a0c0501021002031b1617120a0207030c11011b0602 73
    0x10310076509151180001184d25160498015094400d00103105001070810b5004542c410418a03041d460700d1030094070100954010580d0b10300080b070b81101030005100070f00c1483d010b801901d90030101c2034a0301c414036483d46083d110140500103c1c0315050941401000080302141c4000e05a4242680328a000100c0301c1d91800303500010722483d101402000054454622404044440700c00740359120f0f442d5101401e0f80c250300030610b0045952401e0700f40c0382000b1410b980306206002040600d085030034008150001481e9804100e0b5102c1041c940c4000419180400c40000c00328104800f50f4200503202101c0030b440041d010304c6003414890900502143c0e28050365401d9003901d0b5105221409001603003c141ca410194020b01182e101d0340c218004010214800c00404550001145445881215907108001072040b1400074003802c401c1d80c0030301090350000003000304505101840d10300034200401c0c0e0038001c01d440300c5202018180c2c0c2c052070304000c1d90f003e0601008440c0155242c000c0294124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 522854226 1250 522852976 522852991
    0x409051006030606020303042d0204020c06011e1a09040905060a0903081320120d050304060606050301031e05010209060c0a06150627050907020c09070f050d050c21 72
    0x9003400070030110f1011040320301594100c2a01d007890141c19442c00240d000701201107d00400d09c0181c000141c0312070015000c030703454010250a00d90300d444500075020f11985000b00e500e034007001040c0720148100e040d071044489213a00081d01d4813102d00201780149a50380c0d000e401842800c04004a0085580043c0c1c403151180d40ea28440d600d81c0120400e00d01e42082e401803407454000d01e42030398040d403801003205030b2100900074034400310203a1010b800c06d84d0700040000000c03400400c01c0b0a12113540103000060281d440c01500d55851500c801c568201c03002c5400e000305400c24600810b002003501541d03c1a58014260303651b0315910104156101000b0030101c6000781003280c1c2c4403c04c41810100401c548403629404080029402e01c405402d00340300458603881c00106010030346449104119100f42c403103400410900c81c64408005904000800110400c45000948019640e000081c0c03804030110030008240c0e911030340401e8105003d03460030444030303061030007070202e1028003190124068283d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 522855476 1250 522854226 522854231
    0xe010902101d09131406010e0916060c060608240604090218070203130b09130501140105070311060403171e0613140903040807050d050c01080408040905100603 70
    0x150030240d9102c02540118041188030b400120740c1410859000c030f074080c4602c1d005458070f56043c0d603444c2d441c0d60159502641d070780c41800144040260203410582004891004140e030100d00400e4101c079441d40c5c05181c00300915415400d0411081d80c10038005800c0c20820385400840c0c0004c0c0d9020056282001c813180e0301403802280c00350900744100049280c001d800d122401e00c00300111103081c40701900c0c640c2184010095561200c1c0001102405003202d41d00c60741c1e82c0c51300c54041010111540d074200040358039100041014402104916034010820309205480c1d458909042c3d07410b00f011540b40506006580c00c1104056000040c810701548518907007000341c88140ca1925401500e440402c0c6e14004035004c10501e141510642440b001400c501141400801e08000c007030101c00e840000e900d50000ca403d002e103110a010031009002c4c140d492039a07155030b40d1941e5544005900c01103050000075070100b006e10580030100d40280590310001c0c0001c0c20003003560704000d8924440c2000107803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 522856726 1250 522855476 522855499
    0x7090509010b04150501030b01050c010218100f1d060d06080c04110a211e0b03010f1a190807080304030204200909060a270c02070506030703050c09040e010902 70
    0x2c2d01d4803131120808001d400d0b02d911030382820010b500914500c80a18148641407000d21001300003400184503443c100c003080c06c0400c481304c5c01c1c0b00751410203400c807500b03100d500d40516090991114616410080c42c405094000c4078400115036640f0032500c0d80000c5504114010625140004800d000e080040d80c0c10040c03100c400583c4000740c0213081020000030460380c46043d480494050700800410b14201c0019550b484c0d0b03661601c10a601c022465203551245000321403441d0070b02c50491034841402041c0074083d10600072006803842e500b01ea6201e03204190241c10000d1a110440d0f015100300300c1244c0150fa1a1140035950ba0070901c0f00300c0c071660410b82d03005079041c981aa0032100c0d4005d84a058100060790007000750914000713000940202008100145001903410f42203a54261101c040006078178014080f4269482c0817450002d545c00400208419110390040380d62007561440d0005035a201d03040e260107103100d0200040d17445030410700341b0f120035541940000b1501d482102d9400450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 522857976 1250 522856726 522856729
    0x130e0f03040303051c02090d05060601030f061203080a0b0901030b31080702010e060307030603140c0f1002010b10030204150c021e0a0306110a0807051303060b01050c07090509010b 79
    0x1c0c0315502009001a200b4440032940c10450004540088404036001d4204407520300890321191038003106980582c4880140319455816105200071404424000c0c0a494100480d030501034041e02002020846840009206180650b200d8108120020001607455a4905014040745410b40d00701e49648003640c04c040b030303a011100f202c41041101900702404c0d40c082e501c0c0c00c1080c2d000401c081e410703c181030090030321a41c0c540300118810030064400107415401d43c14011030746040312403001d0290744004405101c03969800e40c030359000001104d0042d2a00c41040b404c034051b02c01040d5072604141c8920002036401c1c1c05402400c10b5070b030b0000d4501e4138000004000c850400c0c0354140a90804480b01d115414114405200c4030484030240074542029981d80d039400448180941c0c1031038010011809100c1c85a02c980c80640000c0c0030b03d01181060490f20107426840781d80c1c03000622095540038403146590084d02502c403500300200c191146a84d54400f000040d1104a416600951a024040106 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 522859226 1250 522857976 522857983
    0x30103020108160801030201080402062b06080a3201020c010c110c090f090c0307080106030501111c050a0f050708061c0506040b07030b0607030c050712081e09130e0f 73
    0x900d90613525980b0503480c540040d1460b4034041c00507070308980100106c111040120081c40c00c0c41e520400640302001084000400710344041e00800300c5030300b208020300b005c2aa1686140780d89981048400404a00b5009036403074103a1410251b03c203540007090001021030103510070400d0a81513140c03d0522000c0d503088a440c3c042a05401d0ba000f200703000440c542c03496910100c0e9100c142c1104907200e01c848800001d1a000082d17110910b103039102c0c5030510800900703000e400401d1003511103413401c00e620364040b020b00c405126040c00506559500080645000e81c200502c0caa1a03540100a2030600c098000c002a50441c0d41901610301c0c2c980c00717652442119000c0c114a504400a0407094032a81d50b0100c0c00100505840704150315904401170a030f4030381008060b207a01c80c0e141c0d00710030b06541c5401402c080c615400200c0c94180100f080c2c0100c0d02c8003040f944030a0700f240141c4018007010f8040c958034003d40b5100c40d009070705c0e0140341050141591004c55401041d80481d4501c11400d04516507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 522860476 1250 522859226 522859261
    0x2b050412081c0216033914030307120e030d060603050610080c0d3b010c091203050715050a0603050712020105040e0907030f1a130305030c090d020411030103020108 72
    0xd24a0508503500082445803100d11070300c100046c000d014048804004c0401c110001521450a0408480700020402d820160010110008000d1030031443d00340d030b024201800c1004a80c140a0321400b40442c00d14090084403a10368140c1406c1011545510004005100c00c80b00c0c1801800300c08050140c40d40620840d5110360780c0b48030702a140230144003101002e00304440c010b5070106070341100c5c520f00e0203000802406035002c0c803010200d000000d440c12420f6039200c989010910140c00020b005807208a41354003070003909824000d503116441d14042c6506440c3c00c2c0c03d40304051401c1d040c410402082c0c0c02c02d204032400740045501c141c0c0c8940d103002e601c50800400a001c40c000300020040d812000708180e500900031800e0b03a80d401d940e0b403111004403c5c0c410b0201c5d81540380b58100e07890307000c000d180740c1e800922074090040e141c003580d503001d01503201c0900007140d0382e607001c14014115075641d81601800b580c080c000f4052000c01842d0005913410a010803030208007035000040882e400c00c0d01105 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 522861726 1250 522860476 522860497
    0x30908030a1505040204030602130f140409050f01060f0f050102011802042309010506180601080109021b0f06150d0503031302010c0203031207090501022b050412081c02 74
    0x51540c0c4a08103a080140b04618110b42401c8240d100060590394502c003a10055000f00720169465020032075843e1190300c640c210200c003070450601807090541d030100c2d44c1c900b154207540c0001c001c0402d043c11403400d05445402d9403250308107031000c01c4103400e03c0074000c11200700f0044002025101c40059091343e030050041110300e040d0811910140c0341c07941048000d0f016403480045061320b40740c000c000c080c5040382d203d982a0f441d002400303518108034401d048600c0059401c840c071414442d000801850303040c400c94810603000b01d01c3d030050001c1c00300f08940c1c1c851003a003220080480c4400716601d44038202c850340401341e200070468507142090f11580042a03405400b071451540d58645541c19a0351200d401d0707041007201c248850050301c0400003884404000c1601d2080741c603040ba00202407078816080907046420103082804100041d460f61408103002d1403030380811420848003165039000710340c81032000e0340c6020300540904c607000c80104060341c0540d00403191910702c2405281a40310342c20050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 522862976 1250 522861726 522861743
    0x1090f0c08030c19081201060302090906090705070b15060a0c050105090304030221101103040506010602011a120309040204030c0e0a020703140306040f020d240501020a0b090106080d0e100309 84
    0x103190403048070f00240e40c2144a0171905090880703103410320360391310740903000b80f00425070010307100800d8a0400c1130700b98040000c994014541c84d10101c01021030044403001802c115054022a54a809600390078207850303000b4103182d86529080c50020003030713030b80a98103075165440c7c80c001c20070160003c002c403020360390040c200c13400010690002d40181d5250194041c5a4054174014a0454045011740001c8110b01c444198880c10903007002e5080c1b10041e44a5420341e03141208201c81301900c084424010030084580c00544500d5500c00d134218424648007583c0319100150203c2000681c8511400b074900062206440f82c1e16516074400f217224110000d00420015210f1a1170150248001e640c420009440172448040101c11501640c003d104000113058660203200e003ca11861040301c001c0380120801c0d0183e03480c181c0080d4440c144a1070181c00c0c01da030780000400c2070100350846030060415000300c8200301c0700510010142c440c80700b20240305803481100030380ca10340b00c2c1c010050103a0700203420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 522864226 1250 522862976 522862993
    0x306090e0307081803010606050d0b18010b0702060415020a0519151802130f0c051e0304290601080108031306110a0c0801060f0803040f030303090c0801090f0c08030c 73
    0x4651094010203410b540c181500e08000c11340e03403000c0c01010001c009603110107441d6818854201c007a62203821415000d44155400800e048990103002811903047d03405003680c60140703002051041c4a542c0221403c1552440114495540081ca07100c0450088050310103500d00040c1e030a0a4003a004c1c80905102844203101c00e0440d5176030302500d81c5d605108250101c8a14590100f140d8100c100c1c0700341000c41e039070460100800554001d00e0441420351506c640740080d600035010f04113000700c0740031486130317004000581000b2030811a80001d8079600748202c124103220803519910fa03000c03500c2e140018907a40c00044c0360200001500c0541150714480743c2c1050400303c3c1150700c98240010b14031a44555480c81002c2451020200060201800003040c071b103040144680d82d5560a070300c84849a8002c100805c40511490340450950780e261402152500c094180031544c07500c5600b0030b03035207075103840004800c0100001ca00381c461071041103040010365541100d5522030080943c14400398009100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 522865476 1250 522864226 522864233
    0x30509100c02100804050106140a1401140d0f0b060307080601030c05220509070f021c12020d0f050c0915160b1006030b03010b01051611040e0c010306090e0307 70
    0x4011041a118500311110780425000610a890400c40920100e4010402e2000f030000a015203805030518070580280c0a4150340441c41d2084103100d844c80040b1428040c1609a00c1812810061000c14000603140c03400ca15150300241151400d19800616141d96980700d0300f880415644a40c0709526a10150b41e900c90043d006001c0a01c0e1000800c0802c010b48001a414280c4010050070184c05a9098608141c10720108060140442c401d0000302051080956400038a03100540703200d60703140640f640f84550540e01425200301070504d9600100d08040d5071070700c0d0f40c4032040e1071590020910127901d4540b030349c425034464201c005e034109008050340c0ba1448218801031620740905400d04d90f810003035480c1c50401d4002500c000c200d25108010400980b54103000d41181d50400702c3c0200007a5000d6030010300703244036048034014041c072203030300003000e00c1001041e80081500c043c0051100e14845e8481a44034102146442c0c08030346001c60104200a040c82055100c06000e0000c501d40f20440d00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 522866726 1250 522865476 522865489
    0x603010b031003051614090c0f0c030408010c0f2d030b060904050108010b12030f030f070c200a090908040b0c07091509050a1e0c050408010204031b060804030509 71
    0x2820442c6048000000100081d420000310000c540e00c001950b00c20b07424410b05202c2c40c1c407640e0120b442607840307800f44150110600201c0c7d0450700412046070303407009400b81d11421030060b90300109055107004940e00499802c407080c8070300003010b0342e00c281000ad48450340075410742410b4900b00c14100a100d81989242c0640d115000810006240074146800b400000d401d1f101d09800034020f507512410240803034141807503144464484d00c00918140b0401006c049542c3c0802484415110040404039207a180280e08000300c4136000030f0081411032903512030b00001c0e013407189400d020f000020700021b0031014034811848440c2c0c3c03040d2014540392401c403402605810103c40380b03101d0301901c2c0b000640d480c0f007446005580c0d401000c034807080619043c06941100ca00400071204c1c641003e45611b52142c10000c000c0581829401c0020300d003d2095048603e0301803500441510741c800280401401004041908104c003140300b440301c4d840c1c50302c008454242040d14001c0201d031f07007809860040e26010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 522867976 1250 522866726 522866731
    0x905130b100b0d02070b011d070c0c050603091b0420030402120604060903020d0528031e020408100b13020c19080a020705120718021303080406090807050603010b03 72
    0x109000c5824540316402d20006500c180c0d422507120f68001400001c20664210721030040021303600d10040c3c600401c2d044624484010a90403c10404a84a40820010b14401006068041c0c0150340701d10700000c541d43d40c0d5107507c83d150b4000480943c528102d26207405010101d21a090320100c0350011504100042d1304042c2c422a031115149034000c4045000700021031190f0b01804020803408250b050203400c014019403804108401040b9100c845101c901d0340b0090190744c2e000302024010300d100224005c20f880d072000707801c6814219821300d0480c0325401070015500b00c18140d0340c0084100300c113001202c281080003500402240c098005010780342e409808418503610a98202502034001078980c0b11021070b04545d04180804c05035100d607410032008010f800155580c0e10310029408006a982600e849580300300400700c944500b00070b0454043d600c5c120300c020044c14403103840346001a100c1c4c01c14040c0c080003465514000404420009a40c0e0803604050300062959092078004401c59000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 522869226 1250 522867976 522867991
    0xa150503060d170a120204030b010b091302031513061a03040816060f0e0c031c09080d090e161407030509030a060204091505030309010c29010f0905130b 67
    0x40780011840000c180f84114100030241c0e5a40d10709040003500c81e0b2442c0e08960b117058070512092000030601180c0740c1c1520460102030b07455100280001d07d40083ca5034404d001360740080180111020030845034100000125000c81316600c00c00d0811084607443e200e101c107121000b8118016080109000b941c106009800d02c928140b0040b10783d07212301c0740304030048440d541c1d1094000c4084481b071003103c9108000c2c0001d000f491100f04002a81c8003c602603000c0c1c042e400340c105100341c6000b0414000108094026510001110040684240b084e40b10750511201008001038280003040a440f0045216859100c804107400c10400b4080e00030601c11000d0010030401810150b504102c801e49052103003002503919403c0a0200083d00c1c0151507140c042c0050300d005101c1c0da503000c0282ca40802f0b080c64403c881100c0350034444401c01d91070101c03041100c034000840044905182c6114140c8402d0215109256940e41ca800211001140c800d0145800d60102000045510300219008400d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 522870476 1250 522869226 522869239
    0x51e060904030c0f1217060429010c060f060602010c08070c0b04020d0510050402030d140d0f1407030b041505100f03060f0803040305161214030d0e030702030c0a15050306 75
    0x416070741741d035401c00d2030140b00c2012642c041342c08000701040c40c05840c1d01c5031003914140f01000b80d400341822161405030404001e030400e00c04001d4542d00c1401982101600b1040900c2021041e00b900380c0100224007e5800550034400044a07480c02a82d0580c00394455942c1c2605180050b1900242c602e00a482260b1091a400805e800300744100407000361b01c1508000041d1500b494410180f92401202da08401c2c89a858041d60070f8000d01010307210000204e040c00704098101304001d100400e40072942c8841d0140036801e015256506d83d114030400c403400e80f002c004105141080601c8101c0d035209107607000c8220900305001922842c58600c00c0c14080c10089505600d865a06541d1102a007041e01c040e840410304100f4800204446452030b50456060b0140c2410400a1f515540403444050210b42c4181010139620000304100e070103410398804208518414885a40e842c0d6010280c240d00c00e00c5000403514481c50618005000c40387c070610541d2400300180710550b07203900018003040d400328 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 522871726 1250 522870476 522870503
    0x510031104090821090f0c090a140708040b0105030601050a06120e0601060c0b0c030c070f08120a090b090c01050307030b030c0310021905040b09090903090a0306051e060904030c 78
    0x1d101c50301901901c0383d00b40741200000c40040008490b40713401030810601da405400e0207000d03404081001404080b0640d030b10307415641c070809072201501e036138070390040c6980c3d02400b0130140c01c1c0e0045031140079501c5840080240c0c2da0320790415598900a00400f90711100f0030317104111107406081c0d0550b148080c01008121003071091115030401400340d0003500403420500d41a41046100003803598410301106c03400b03081d1b00340300e0300d4000140515440141a0604004d0705000d0200840c1641c0d42a010390902101510307140300c0c01409820020011249075095202203000380320041090280c145043e560541507580c0c6000407800b50100042c1c45400d401490081d20003524148201c0120780d011f244056a00d500741400d01c41c4040316469007408000051100b13101c0c01442034121582c1440842e184443e6171681d0720b640e81580704a41c151544031851880000c100410b07504403a114024034101880742d44c1080b075580c030284408640082d4042101000500000d0080829400e0780340552001d0401c0f4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 522872976 1250 522871726 522871733
    0x90402010c0c0b0d180c0e0702120c0709110c0a03120e0303040605090c01020a0b24030a0309080f070302130903091703070c0b2701050906210703051003110409 70
    0x10b5609420081c0b003403c000803d0708581d2180c0c0207100c01d08203213004818060015460799108222140140c0000c980d801c80443c16441c0700308400512000e6142110340e0360440d01c84029540c410901c5a4041d050400c0d04c980c06070701e041d906454005400201401c041c980a41d004c0343c507079a0b126818120581d80d40920200c1c2c2c0003c10141d40b0807403084a0001d00c0d828441c0c0d40d0b07458680404c459070704541c402001c0200094501c2c18450308500c10003d1805840d511000c00f280141100c10895054402c1d01205024150b200a800d400c07154410b040e60400300301035074100d803a0f241f0ba010294200d240d00c03c40328040d0140e40d00c01c0241600926248880070b4443c200310403602c861582410155001150880c02d03c10030584120041020710100c500d4031074443d664030060112100c2e0007c0d91217a285003c0c1107640110700b02c4840900040501e0f0b590413110042c81d2809900910000301007481c90000340e00d1a000340704003401624a0007847c03010519503503d407902450b030070480a0704540c55441c01d0001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 522874226 1250 522872976 522872993
    0x10061701150e150a1206080a1a040809150d06150e15040308070b041703071b0201111c171308130302090c090f010e1f091a04060f0c080405090402010c 66
    0xf0398005135602e5445c01d00d01103288080c0e0f10240c03c200055013100108400188a0b030b0703003c64100c01c3c0c1d4071481c10f007560380303041c01100c0d40190084640c015041c9105216128403010003400701090000c01002403544840e6090b11020360344c80070f60003091348240c6d040703401d00c4c200e050700014440003c0424a043c0e203982d00c2c507910b5002040c044401040c0707001403004100103203110549005402002074254540000c005000f0407090034200d621954004501e07096902c0b0384499016548032000310380404441c9038107810003020080600c8000340030585884109801600305500405c80c0d02c0540031144e2081c0c40d1180560f01500ca00c24000540340000801a00d46075861031003000c0c91420315481c0c0002c6401d01c04041c1c81504218101300040c085030584c0d40c1c4101c8044034000164048010001200106540940d1584c01040094501314202c95031410b03084000d10695859a03502c002c04c07800c0c1d0314180d440c0d10240074010b2141a06001c14003060804003a181e50007030051500040011a58469605 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 522875476 1250 522874226 522874237
    0x3172a0319020c0904060e01150e150a0e070809031b0a02090601051314030f1b01030e030408030d181209060206012903070302070b10061701150e15 65
    0x580c1010451090403044145505441c078500d0026100292003480000d00c9000300400040c0a95030710500224145400d40c400c40040c901880c082c40800d0311226100400c1500b15504c1c19125a40030094540d03080c1070000408407451004918601d444090055580301d2005100302640e00c0144581000c2c800d501003501248400c3d04058800c8000c2401801384030800100f15505011040000c7c1a0003518000c1e070341304641c095002c0044900c61080003d0525590f450075111510036101d1040070415009a403143c41c0c07400b62000c00104103101d040607240e000f0f610130040301350024044401c0070321160f0040d180c0b420383d050440b03101d910340341d851400020000d41a040000d0540d4800d2012580400c400c078050014103440d00601c0c02098100f880200e2a010f84408540d4044042400c080c001c1c0c05072b0703015a44c00aa00740c8245083d45100b00001004d100f01000075218004128202014441c29816900c0d4030f2106404c42d607000c0010b40f00d2509070704006400c502d4075880086e0403541c2101812 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 522876726 1250 522875476 522875557
    0x2306030d14090d12051c0c080402010c03090503031b01050604050106050a030921030e0f0f0714210d02010f0b1c0c081b040e03090a06121503080d0f060317 68
    0xa4680340801140003010030003451b088010342c98055038600c440d070400e00070343c3e0056091a002521501c1c5141c1252402016030041c0d030544804079040e42e0304a01d0351a00b0b0401803840000304150b544450030401991020303c510300200381b0403c0041031140c03082d00841c584600a010000b8200003c0c40030f030004506501002000a644180c0101c02590074820010b204011400404940301180041c1d6250074992090800042c0100c807200e0303090700d030040190340e081580740000c1c1151100c10640394030384800c01c4417480154038010003141200c640d40310300c040c0c070783d40500482c0c6c00c9959141040401040740380140c8407044801000a140c91080000009580d000391084c24a03100b00803e00c0180d0705446030001e12a002880841f035a038980c03140510407900d5500c1c1044002e030010498078010403162078446600c2c2280340740841449568401013088280d049400c221304030a80d03185800712111800010060500c00110018840100f405002042814180c03801d004010714140c0a0404107a02c0741c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 522877976 1250 522876726 522876737
    0xc050106150c050f070605040611010b0a032109030b13030e0909010204090e070b03071817030415031a062a0c01020c101b0f062306030d14090d12 64
    0x4000704070f0103201083c1d402008000900c00c1c6824602d02510b0360169000350720400011070a241c00203c0c094000c5548804082c10301e000a903200d00b4103040060040003030240020101480003541031042c0c2c11070b0704990308082180100e454107600800340d001c8554041d0200708400c9614192603803401c80030360248040034001a51140382440364821703540c0702240e80e0307080c2d0007094003000214110021a90700c02c220b89024106e101000c142e43c5d0504c0c02035004407042c3d0b04140300603414030b100000240152482000c010043d9444d0880c100e058540d16403402da6182c1e90301118200d6801d2040107052180212148141510000c60840b051807041034080c15040d44020704182c1c503941c051040c00d2280c0030548001101c07003180782e00503100d255020060303224002054860420302101c09203404106502120074061200f071f4455001454103005914880c2001c000c02003030745454002820544248107844e06008258000724440b8190010b0100903004400c480900f80000c00e00d854640c9a4002e03074940 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 522879226 1250 522877976 522877997
    0x10507090e0114150705010e1002040609090204030819021f0527060f25020606030c03030c0a200604060c030e04200306010201060b0309071719030c05010615 69
    0x14100311801a403091000000e01004043d003519003064080005000040c401d50310745c0c1307620b001b070f0042c5521611940c0f6170141e280c8412844040342c00620444580b1f40c2e808004035184d851441c124880c601c0020980c01042088a00001c2040f02c003580080c030750300560f20100c0c00074842072001100944036425140d501c80410a44c140f00701c1c03414030070319200041c08400a14010040713507a442c001d08100a501118400990105400303030160304da04600ca010352000029100c0d020b03580d03078800d40319240701e40596007080c41a41000005e07207044140200080064071140c0d141c9181f40c80380c0000a50041e001007840da0340b55100c1d24010300007800300e96580010b4401d03a090042640c0c050880462045d810160b040c0340d281041e000316407648000c42d01403641c0341ca134140180d00501c426400000d0124001c400c00003032000100b8040d0403103a2010705a40600b40e0a1241c035110744003044a0180081030b00041d50202e88180155600c0c2c5100e0000001e5841c0c5401901d01281c540d50460750015104590 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 522880476 1250 522879226 522879239
    0xc040c030e19081e0f0a0f0e0f06030a020a03180305041a03060a090b040f05010f0819050303070503040c08070e070e040e120f0d0501080a02121c050a050c01050709 72
    0x500c0c40180c00b6400d00d030036051290703102c00702481500c401c03a0f00c01d00703070800030360031540302c842100e002c044219030a90b902c802c60f0710094080010001c4200120300040c02044a905055136000041c0e40d00800325461561034040b0580203411440b071810425584102040d48040840c64170742e10603001c0d0b103c058a851505018943d4221850300d40c1e002c07000240140680c2d034807094820700a03074444d91004107601d150600410000c100c60b030078810406080100004141c440141c40c0000da1b00e01a090b24001c0406200f044d0ba502092100100560b108000003080288600c028580191050754a0300716580e44101e00c074500712981d0422180c840101040c04450f503084441e6051402d404da070103002e80701443c4030441c0c443d040420024000b902c001400c0d000d203003500e4212000391045003020403d40d40c40b0100c103640e9a0710504200c0c0180407903a514808580002151042c43c01103400b06c1481c0502d58a0449081c0c015102d02c0e01448000d000c20440c00c10f0070b020b8a07204944070b54824202d10300d008c0703 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 522881726 1250 522880476 522880483
    0x100f09050411030f19110603100f080a0309031b05060d020324010c02010e01111524090424060b0d06090c09120206071226010f03060e0c040c030e 64
    0x2480601c260f1160b44028001d080200d9160317420340328140c0b2046440d009041c000100052090455807020000003000002000c1e0003464007901c840044040c40d00d070300c0702c1001d95928441d500c05008a0342c849003c1001442d24100020000e541d034100c0240c0643c0e5801040b0150411505941140e401008000101070200f1f00000c0c04030386807960710184000b0034006850b0b10f00f1540081d0411000c0032800070582d009443d41d101d10943c400c2200c4940c0252080391210031415103884680840c2d0440d0120181448005084412401800d00c0d0043e2030303a139118040e500b041c1440c42d001c102100c05e00701c050000c43c0b140301c00600b421441e00e0303645d180c4018400125100d5420030012145400c6004a109030301c004c1c072906558010301c1c69141d010f81d6000092903401012001400e0b12078a9104200a0b03620604200302101c07013100c846861000306c0c05004040740b09014054030644290310070408681d89402c454008c004620a90300c129001c04041819075030460301040120303407502c415448030782c0c041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 522882976 1250 522881726 522881753
    0x603101d04030f0f0c1202070905150619180e01140d0c0612020705010c260103120c0819080603281b0902030421020309031203100f090504 61
    0x30502000c00380303855a40075004429001d00c031420454249900f03a0618003400c0300d0441e85070000403d02100d04d01c48802582c030285805012517050800000c180441154401102c0a8400608650819039403840e51284d0001ca401c1c180b0801c804c0c0001841040200d68140015008180f0114003d40c1090689040c1c1d088403003040303001e50201b03d6184007240b07602c441038050f11a03502c0d200d90031001d9511144081c1c042c81c440500207519080003a121035800003048131007000404d40303a5411034128030702d4401040c003d1102400401c990300c05448068415001c5040c840d220b07001e403504000c10802c141c55540108545440400c446d0018450585000c000c4c1c0c3d4104800003600307160090340070301031882040440704014000341441404000318400ea0803001c019122141301103450f4645400c10011301000340452002141d02c400641640c90320100032608031a90140040c4810040424210360710303880100038801d140d003603603008183c00112160740310061440310b0000c209400e00b4108003540600c0c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 522884226 1250 522882976 522883019
    0x8010221040b01060e0a05150901030513082208030a03270309140d150b040c092d050a060210050f10060c03030b0402030106020d0e0306070507021c02060310 69
    0x3080000090160400c203041d21950300d07000b0007840d116400700e2600d000300d41101743e205043c80c0c01440c640a07038a01901c00d4050907a8140a640c80300440f0032001c0c03200caa03019205d1103040002150440720303c902c5885e406840d91041c1c5e401940d030250642540c03c01e800e154006900c030074081006031002c050882d01c002d0362540e400e51072040b940d0080e22828031440743c1c01c090106c0344c1c2c002240340d903854240c034411a08048100c0050110500c0c0c100200703840302c0564429442d040d42041d80e41d00c254025400e6a0b80051000044520b034000c0c01c0c01072030140040200916814000709031134466010341001000150010851007944820396000ea46c1e00406078040203480d1003c129000c0e00034090b8100b110658106565154840e00381200544040c5960603042030002000161311503000031402c8880c80c16998000f0300d0b04481d020107482c0e5106642c07610009034240006005032410403103401c040f00b0076250501c0c8803502a400706a5503001204e09501c2040171010400c400a41005001c046029 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 522885476 1250 522884226 522884287
    0x50106060e131109090112150c05030f0a0b100306140621070201060e01120501230a0f180305040f080d170402032b110102070f060213090501080102 65
    0x150380002c10402022604500240354450000e948419403600458800b40000b40c482030b82c030742e110411780d091080040d500700d844044a114642840245208030800c41500c2c0d9181c0d45940ca48840b61040c0040140101e00c0240d5200c0c2901e086948110000031180c4440d01c01081903458410314020442d5581c00407070203071004200c145900c2035800c1d80c2a00300d030080c2c5602c84142d280c0303107012401401030741c1140c800c4d0300541c000800d4101c3c00400c80d14101d0722400090051482040f82800610b01c1542501071f84207401001c02c0e801102078001c5403a01c1141100094101941c52001c03141050b00602078011440024050040350340395160300c8090303d0480002c141800001d0701c000c2001080b2098544446c4010008c2030031580c0c180b19041e010303034030320801511594001e11030f0f07086582512006130124182c07003003d50582c141030090314152500000c0055400c103003500e61001a62001c10300318611412a00c0208841800b8811903011f82105000143c07180818030440520f00b140c52704c007407c80d1a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 522886726 1250 522885476 522885497
    0x31104050a0911070f08030121050d0f0201111207020d020a080a030b06160b06040b010311030c0f09090c07050610030809130e011811010e0603040813120f05010606 72
    0x450300762100d01110307100900000c24140340095510340b401003050013440d030521004c038072084c02100e00195050b901007001051060140000c030100c0c0c42c52405e40289950002a04221512b0185103000b04510a178000495101006440d84440351720444032004204210428029181d5042045040031281800200344c6015541c070303408800e00a92030352200309905d40121510740d44a0340b082d50803450051404010403450f0349003044038807004543c0507001d5440d05d0004181c030740c464040c40020b4130703020314418078580342c03201e1840680d88410380804005108020441c0541c44030004180300e180c10400840c5c40310f4480c9420380c01c120002d4003000d0a485226014000300369403030212013041e0710854a20720fa9889400c4100058072070203407469a69480d0117190200c1d20b41d050800088540725030034900038001e1240041d55000300000c0802d400c120141b00080c0001c09407401484407880155a12031041e070344686c1c0d640017108013001103581c5441d2861110822000340115001340c00305060000c1e005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 522887976 1250 522886726 522886729
    0x30c102102030708310803060909030405060703030504050c15040602010608030f030a240b07020307050a0608271e060a0e0d051c2406020a111215040b060103110405 72
    0x3081c3c041e00030103901ca0348480d0788080174409840030516900c040728006034207450341003038901e6400454090f0300234002e00b00041d8102401000b110240c2e00c00030843e5080c02c050b0f072011802450010800ca401e4451301c052541b099896402c8903841480326000360303640350305059000b402e440301603006118651060004485d00700002d0182c0c0d44c42000c2c00030014240c42c0d10b4040040e440b400f402184140d045403500402c80c44450070052030460b0080d802c403444070b952641803059983d954410b01002074012008542c2000c8150114140394090b50b01100c05920f00d0441d05040445c480c40078024800b20405461144506000081d0b220340320840421030038000a02c220f8a500d5030021110821000050500382c80c0c0000c0901d0062244c50340d410800741a00301d0070542d492484050040b95451040d500080701403000514402030b66210002e5110395511009111034903050300303231094150107008201c50504140e541c80720f201d5070040324041d8035818184005000c8602941d0083c85940382048248141d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 522889226 1250 522887976 522887987
    0x1801081207020127151103030406090f0c180501090911150c010908180d0c030803151806010908070509160c080a020d090506091e030c1021020307 64
    0x8052203420341e0381c1e00340c602c0101e40383c0d805440d1340c031003000d480881c3d08038102041d0002410342d40300000911078043e0340401030f900d01e105203194a416a02c1000040c000803c0c541000d090390b44604047c243c54440c0341d0310545c074050590010301403440e68101c040f440c0207103402040d0061407620300070004603905489500000e01000c0c1094002c40c0100f031642000e0200c44201c0702c9824420000700030300a55440c00560315805240e81888458204081da403003450060305942c1402c1c0e1001c6071002703507441c44c0e07588000c0f508000c040e1406e29200031040403468685002a15004024000b00c086601e8410005070503000290412841c644c0300302d400707002a4455942060708928541088d8800c840c5c1030004035244050083e00404602c00807600d1b2030155000500044482c4070b0b6210080003d13110002d04c88240141180c03154081c2d01e220320700c1100300b00d10101042c07440380502034030300d4076140c080842c86850420f41c550000450362180703070b00001c061092800d2142100710065140d4104400300071b24 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 522890476 1250 522889226 522889243
    0x904060b13090803180f07080303180f03031315020409050402131a010c05190b04060507030b060f13090213090e0a0c2304050a1d0f0d030b0a08031206180108 69
    0x1503451317614000e4000340030044408440703100001c0368101034480403000d4403908203a4840c0401c5240203240354050350b000c00c2c0d1400c00c0a49030015400d59892200343e50490005200c251600305000c2c2c103c0881600b40d00082000d4011030304045510300b003d2060040e0b50b050462840e190b5454007104440c2241c2da008104144602460005890801c50030f0407420b000c2c540c902062544104a5203004111060390010b21944c0284c02c00c10559440b414260280d40444180c241d00900400000c14408840302c0580350715008621402c0600340c54003e13600c1240e009540c03c100341007012208200521050207204030042841c0d000d441c02e82c0c0b0f15601c40c1c00724600c5000b42c1c105001842c0e00c401000c4032408542030030765002401030040e1306040c00c02c000204007440200c10040c000d1a1601c0030303600001150410300600100811013180f020703208030010540c90788080d5008004903400140e0314020406441d00716001c6160342c1050a003031040140c09540b2078000c180d85141e9100402070741001081040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 522891726 1250 522890476 522890491
    0x1120c090b07050c0402340b0a09050f010e1b040b0f090c0d020d060e01121a0a090818010207170c040504030c0b0403030b0f01090f150e0904060b13090803 68
    0x2e4503042e07145001d42c00c1c24000010260001d1020445503d01444424210f9400c00050f820440c003d409402950025010141c080c007488059400704a06200592010184034090740c1602d0a941100110600307680e59941d00c0846d5078013440090b00300c4400c25001102440c812902000314481c184045441c0000800e01da2348141441000504c049000c9011907032843d07107140d02190b0300d041e01920300c4002c09550091564540103c00007080109640d08021125500591044101007281e005a203060300001c20400b4050f858445100c00680b83c2d001404601c1c110441c4601004150320009184c08030560003100390341c4a404076824602e20100311540d000070140d401042c07a42c3d49003001d542d4012008402400e800d910b404020034950700d0f034410058510300b110030070008189c030001111000480e0098a501010b505c10400c814400700c1c641012941d82402c1288451900740000f41d080001101d0542d001500d4044041692410018035100510020f10411a0028070346400880d40801012741 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 522892976 1250 522891726 522891749
    0x90801060906080c0d060e031b01050705180d034a010c03030203130803011d0f16030b030708070b18031f150801061d1501231309090201120c09 63
    0x21703414404503410001ea000b03408811203030b5a000d6000b4440c070010071110040c0c0154a080046107606104100311091443c1081c080c280c40d1039010108a0f0403804800704905000d60613098000040402090078210008400041c000100c15125401d000c410094058507070034910b2a88011a82c21950028405070140b070016102e9890000755a0715641c40d413400b80950402000004440003209900c48201e4290381050171152240d03400c4001605090740c15041004c041d00e0b00c2108907119a0000109040c028100c40280d652855803070b0400001e50041c1c4245c0e9000501400307006910403500b48500020390081404042c4054a0340f119039070740150301006522080b400e103049024101c0c0e9809071000354020043c045c2d4071125a4140502059412441101ca200080010000b0000c054142d801a15001501c20309001c0c2c0e1000600860300d103040310b00c2d09004410500100750380303603805040c4d030036000600c494042c000035000c0002080c0c200c002c1801e2002c3d00382203c0d071140c030810840e980031524 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 522894226 1250 522892976 522892999
    0x510030209180108120a0e1306050118270b1513170304031203092f06120106031107050303040318050618090a0e01020c010504031103040e060105070f12090801060906080c 75
    0x45a0301e410041c603060344514030f0340d18541b50481d00d80c006c50407250f00341c846030607043c00460cc00001c80ca030f074840c9440f00d80046400c0b04007100c140ca070170000c014101c5030010391040c5003400600100a0252484000c00c008210340314080c40360002c81006d049054101030548108180c103a0762880b45000042c0011098480d0040c4903019030400319940c1c1e4064001100341c1004648880d04000da8400311002491074442c01d0603604001c07007100c803030900108980a03240c0c281349080e00600740c3d03580445888541007002d0300104505002550240c0c0c442d039034010b1100300d00403d20040300c03920b410403032080c60308000c81e00e08c401034a0300312130300d100040c0d81c181220b41d68083c581000785019420703031202d54000106280303500c80c10740c0400d100f18802d88882402e291142c2c1295601d0041b07024080022038142c01056196014078082c0480a1107560300d4000e209256442d8030a0f00070008500740403c140d1241489501402e0280301c2c082c000491003046154034200a15030781c3e0480210050050326a41c19 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 522895476 1250 522894226 522894247
    0x21c030b12250b090a09050402030c060c03040f09020c0d031a030703143702040908040603050411120d112506020c0102060c0904020d06051003020918010812 69
    0x102507582003107800c00e48408926403001c0103003041d2204082c00400c880e640d004118121101c00703441c007010000e04100c02d81400c000031100100805001660b0520807219441301d16514000141340304079a1902a6454604c1e00f1100300e85036105401011100c0e00512182d0040350001803036504042c80703032a0101d1207401c210111015040b940200a03094000c0c24070200900ca000d003103555980c01e484c2d0490304805050533030303084000a80500380d2541282c0702c80f00c12082e0030b071490401d01280020300010700b6603400e60794002d050f072041c1c3c04440402d480d03004010a000ca40b001200c0780500c140c0d8101d036400c204003c00b685501c0c1d811005800c0c01203004007190b6243c820400d0040010700441e00103007880440120080f091001c0c07058030700611804282508651020854a0088040c004491308000e040b1041101a4216042c0b041150b6034945001603140e8840078244900780040c0c0300160f494008006001c0c04200001d0101541502c62004001450b80010590180000e10b600d098135a10403d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 522896726 1250 522895476 522895489
    0x150f0806040b150a020106140d0218092401080d0903150905120304050708210a03020a020102130e0601110f0703060222030b25021209040e0304031b06021c030b 70
    0x404003c000d0b0004134401450a030158840700c1690b100d0b411000f8a244104c040090301d01500100941001b1040301a407410300703c21840035001250036065038444010403a90030745039003180d03545904911a01e40108185841440408080e141c0e61405000c43d07421600c170b8400000003070198204695031003803140140300301440414101c802c0305809907a00d080500f41b05581e00b50600650810340521110442e00c90105034040100c80a1044100d062600c41001a030007904036030b1a107010b55400b0884803070030b00c24100881003d400e003114000d1480c14090001401442c0500c51003010f5402014401c468540000301001140da1024000d40c4e240c9401110107a503107180386030807031041c00840d0302104002c485d040751803113421034455246010262503000060b00c02c12008440c050f82220411a1079078100000414800c0000790020402d203103041c5140e45564020740c001c4d10101404407041c1451007030391056000810740c170b00c001c18104401074200d420022040b20030805069441c9024100382c2c803030f038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 522897976 1250 522896726 522896749
    0x1060e0916080a0f02070c030c0b0c0d030b0105040b0307093b1015083c04032703060e011b030218090f0702100509100905120c07150f0806040b 63
    0xd480a42d100c0c074440c5400744440e58223000450f43c0d80d64130200800c11641d241c0035500014803503c010111503651817006c3d00100303880d408580c1008002c10003c84c440030000c0041d80610300326525000900c0c54200d0210004c203000c4c0c006402244411800c3c0c0000d0402910840359000c074511140c0e00d40c4a505214241d201e041d400860381000364070300c20b818540c0020100d4030072410200d692100406155145801da03810b071040100c908001c02d20301d03028800e03008009a101c0e02c281481103107420004040c03000300130b96035202804c51200803018810414940038008261aa460090000c001742d22647d06088001d00c0341442090350108030300c5107104d40038401e404880e001400020300f60030060040071800c2d400701c4031500944203030707998400030425034403805200741000c901400041c10485021170107003014080079515449000c100340401c200c0000240042c541c0c80c0c0042080c0d52600010340c1c45014120a40c10511040f400c46050320b030740100d2400d40c0b003002100e0000d41c040000c00010305100e41d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 522899226 1250 522897976 522898001
    0x20c131a0301090b01060e1c080304140708011505031209090405010b060f250302030f07030c050d1e0822082704150503030702040e071a0301060e0916080a 68
    0x2001c00f0a028400105800c6040c0c960135030715804026541000c0c060802d128001c002c060500e61201c00011607212000765411922a40ca0315201d04650000c0903c1e210f01500300e14404c2e55100c2c1c02a0780c0115882c1d00c14020303d02a0060714202110075401d6065001e1900000c4c011040a000201000020f51040b888050001c142d10f440d5103200048914a0b00b141030a107160760700c040040d0121584004000302480d80c15401103244c0100d6845968841d00050300807024004a15807800000700140803241d071500e2213985500403070b28060821040d0641480915041c002d40c0c03011300015405204000095154641070251081c0c120718206c0c030ba92040c0c841c01118441400f01807207445010001e440900881180c080c0800d90700b001d440d0039441e0031407103940c0d810b1340204181c80041c2000e80064218050800c00da9103a00d0b52654580000b107100101d003600804004014400c0c20f4000130301801e441400d9138100c865141c04580100200c0d080f403000b0091150413000140103541540001c03415111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 522900476 1250 522899226 522899231
    0x7020a0f12030c031e020f040308041206050f090a020f061b010504050709020c060406051e0403050a090603051915051201090c0519090504050715080610020c131a0301 73
    0x1081c1030640e18240c100e80440c1c00a4100484250590b2081c0036980f40020303c1c03880c0d9070109800405400080d80014a40340300c2c0e4801384400404514031a010380300404002010419802036482c18200b00e90f0000d2803001341481200c240b0400300c900045810180360b0640c0c5a0011025007000503402d4051003c58005244804c841c01005600640006004500c42c0c01203611981c0c1700c0004400364014040d5a0140303038021400a008900a42c03c016044003080781031410285911740d490a141604440075404500c0009180c101158403520f54402003510b89030030489030500c0300c0e11102004208002e0043d06440f440c07a090441c1c640000c0701d009250052020a0700309403480801d01074500b4082c113582c02520b03e000043c880c1410002c040b0010009003450307050b2400c14503004002d100142043c0c480384100701c030215a03600148000c4049040310b8441c007681d8a400d004101000711094001000c641001807000300d02d46417460140c981d03e500d40c0300401c95500700d00c441120381c1009004158150b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 522901726 1250 522900476 522900503
    0x10b0c07090e030d09061d01050702030a081009060609030c0e150402030603160f060306140619030e0613020301050615090f010c21020f0d02150403121d0c0414070807020a 75
    0x10003988000b2100d040f440f0001066820b41f00080d080b58003c4503900056082045481c9280384101c200907488165407440507030194860403000220344040d0170240114403565000e000744400030a5000050013000001d0301170740b0703024010b0908a402501141e008680201c0840d10b2590140440c0f440002c0c91190410181e945d0110307200c10301d00c18860b071070200385808004142004241929501d28a0242001d450b10212005120031400c005248008041d0b5421085000b240288100d034004c00c080749003000c010000e4010142121005040103214082c9015000400c400d840c040d00c03444002100c8105291703240c0b10060380c4001510340000c1a803000903a07900d0a240318401d4880d0520095030841d4400400701c0c80e03550ba00c89500c41c2000c050f80c030818183e401c40c50794040b0300368030901c649000c050801d9010b406400395808820303104c0008914000c0000011000c001c110700882c0100d40c1880a012250845020060041c0a030402c001d035090004030828020800b5552445e8011145154070303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 522902976 1250 522901726 522901733
    0x915030a0305091002010510030f0201050c0601091a030c0a0603021e04080a06180803060d0311030c07050f010c0f08030606070f05030c430b0c0a0506010b0c07090e030d09 75
    0x1940304083d00361150180c201d5a0408510502c81c40d4440c49200301601003090031604c1d540458045a44221f040003020006141420428011203000f0588414045814902c61550310015264180200e009904c51086001c0b5640e0703000c3c404007124010700300140e4843c0c2d03080c0000c075541a0304071441c806880000c0d000070000c80c00289071942c14021002004584904c0100640300c050008020704038202c01e1011958030301d041795407c52403601c81c4c1005003481000c0004681190001003400d12950040304040000e82845d00052214480901c1c00d41460300e002e5640e0801001c1c07016000e08907000110004d00c06c1d46854044480c4189c015070100c1c3d0000e5071f4600380380d4a9024400302a81401200510400c144001061040800e00002111094040f02000e0307608900b01210041c0c400c4110700300099240034060041c50350902d14005086176410318201503107403030010b1f80031070080d020030401ca2000704004a921b40a94002d5203010a961000740009441d6000d9030f80c01e003601c20b1401c7c1d000d0041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 522904226 1250 522902976 522902987
    0x1c141005190c080a050c0c01060e01050a090209060d0c05090405130b0702120a05092b050d0e011e090e1303031107080a12020909010909050d080f071b0b10061d0607020915030a03 78
    0x4032031040343d60dd41800d44070842c45041e8012040025000902404105150200c42d0803d40c2c8030403243c60000e08040441c80001c040d5403081c1c5e29401440e02c500b020005105020014540c0300c0d450340000d11681880659000a40c40b410034103404001340031841404513036480044040c20f5841103417280d840a91007040c5240d0781c0000c00108c03a98131800000400403406403001c526142016155010396804280c03800d48401004e13007008007044100c1e90041801c07080c1106a50040d0418408030b00d00c1d40403403801904403000050101e182220a01c90540064a034104030f403078a00c860300d001c5108010381d50b449406400707030b8040642c1c0b10000b800003103407040c6140c1c449202140600d0841e82508407004003941c80c0c92058800c1c0500c2a060ba0008200c20f008003020b5803c4805e180d0a03884207503c90f02c6c2e00900101c1507440c040584840102001980e031f10654840c0d640e0003106c03054081c2c50703421001800c1d510640000034002e400d40b8002582180803890004050701014003541e046003c0c51400410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 522905476 1250 522904226 522904229
    0x6300c0608070f02070506030417070501060b032d010b07050f030f19051e0c03041d010503010c0206010b18010309020402070506090d0306051c141005190c080a050c0c01060e01 77
    0xb1003c4a44414013440011407034100c03030015100c2460368a881c0c80b480042c4020401c4980e01c00c200704100c1000400900c5040000d1900000054403401c10032180520360390a0583c007100e00b2850321050046807441c0d040342d81190603003800c403a43c400c1d051030064108440c50040343c45500010031860680c0200030020500381c043c3c0d400c08503031001000c81c155098040c20000d8490456111420300a10082c600240814001c89085a0929a59410025002c03c2c0c200d6020508202e0600400090409002e6801c0303040550000d03055a41c103128030710b036007409002c2d00841048041e9403014a103034060b60110039880d0b0054400d55585541741030055450b80141c407000d81d18070071039101d00c180c14800c3c0700302d5050f01e1004001801d50f40ba0380380d04410300c0d016640246c5000340c0000c0c07800c0d60b4090802007049000c10b140d002183e00c0c9030840c0180743c1400d01008150515080103c43c1042d6a4801211a445001c8902c00503a607111600c801407280510b010300e0b2010341c03a124020510a250600c2c8c00d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 522906726 1250 522905476 522905491
    0x171e0108070609060f1b05010612150b0301020405130911060a17010f140906041404050f0c0d1a040f0203160e06100f051605010906050402040c0306300c0608 69
    0xc01e40d07942e0b00d10898500422424176000a0200a01c05000601050050341881d00440c00811520b450b4403600c5403400700711a08403034614518903401c0c41a005401074405421007140214109403031315000c1b0300a81141d480013414144c1c0c5030800f0302001001051840c290b00c0152030b840d10742c0700e080c034007030070b80f400d03005100404803c0f80000140240000a600043d60ba0310032140803200c094209010751007101a20059025403111001440c0040c48044184520b026800400c1e0014420649a0601c500020780d02e0227200ea0361a0003001c280380d44d6400c520604920300300036159985091000714100000002503140c0264030340903044e03510100c0c0c05030a80e0003e0448039995280d180410121041880340070307010a03d9203e040383c0450040c0c01415030b042c1105200c4039062941d40d201401c640101000b150010340d900301384419420540300d10441c4d88210b05040240500f00007a038800b03040d0040c194109d40303c44402e00c4050754088205c0010b01c60f8003030080041c0d2a100d8401400070001100d290 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 522907976 1250 522906726 522906737
    0xe13060803191704080412060e03181003180f02060c060a0b0109080a02030714010519020d030506040203190c0c0506040b07080921160b0a090201031b171e01080706 72
    0x34004450150b0700ca01a070f5005c0c0c0128603141c0341441381e1401d80405481601c105d60351b666881d000c90000c0c002402c845481c0d07010a00442000405c000442d8085a1800101458002c500031040001060703055100d402c000d56105100c49440022b190f4031410188181034040c66044c8211006650040341182009032120241c107600e805603543d550f0301c080c07400395050348002e0081160700c0e83d4401105110300c0605d4010320344440c0059405c030b0f08844a540c1d50042e808403003090320055061082e10741102c0c040301c064ac45c505018451001025040400106140c0d603503058050150148141c40c100c20751100a40300d081c41c040c20004c0c210402140c01c0700c0800c1e064000100b0105002c103000c0e6000800d1900030000c4000c2900344c0b0f0322074008008040070b090804007800c01154004000e03d208140c41003000c1003125003803000405403504407280b81c0d6281a003a038180380320350700003c509030307910703d80701124603550384038901c80346407820150201140f1a5610002315070040c0c0402d81d60256a403a4441 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 522909226 1250 522907976 522907997
    0x30615051e031005090106030803100e0a0603030203180112090c15080f0a0b240c0d030b010f080415020f0c1501060c0b0402130f0e011b0e1306080319 66
    0x12984074121a01015810340001250102c00d48480d80203d80150303039540005074032034030b0b03550b542402e5001755414648204190303000c01844000c00d41c8154402c0141c00b003404410b2565174065582e015030000c1c0c0f00d014402034103041c1a03900c2084607800ca81602c80060040381c00d07a041103004140305000e1981403401c1180711503a002d000390000f601486d0070b026513484030b07030310400c1c000f008140100d4044d90000b6000f040303100d105c6203481340e0030400b103540100c4c503a180c002686903840c05603035500582c141030078a007072404a40c0e008405c1550b440950300344110540d03900d140540580c207030302c0120042e091000c0341c842d0004440d40013400441316201c04a480034829002c50203603451091146000280d04541650001451040801d41144c0701030510660451454560700540c0e0420362001a401da850440c5000c0da00e090042181d00c983c0c4034000f0301442c2e10727080000c1c49481d10301070040c011103600502d040c080ca03190740f00000402c4e41e9819a07480740b4000e2024101d001d0413511050008901100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 522910476 1250 522909226 522909259
    0xc150203100b0c0708150f09060412111009030c0c0608091207080c060f060a06090339181407080412020705181b0a020d030b060403061505 61
    0x803603006464075070900028901d00224042c040d4001d00703204605000c0d00380001540765040000c81e0f80c5441c446400611840d04c000c210003003000041c202c0d40c8640c409400d01000c51403013a455803141e406881c01c0002181c401d8030007464004170070008030441d03140002d58010700d5488070300d6080081c8121020580d003666131004540e03040c019248008030303030054000e03041640d40b0700000b0304882d889440701034202160380a4440c00c020b401c03580321180c4000304040181524000d0300d004007400c00741c18000703551703800d648580e070f40030541640301c02000f070f0301d07060030f04008450f61608401c0f8075800c2e0140301e14640715100065556203a155000f00e850070601c000f054403400d07000051180351151360b920144d40c3c5940f0391022418202d00684294080c80902040b542c81d000001d600082c0300c11195a042c0c2041140b01c6000d45010104030030301c0c18144040c1c00460b6011507080c070400110300c0c01061020440001823014800c0340c0c80140800d14024480514a094500b00c07803c8820460380f13413552014920 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 522911726 1250 522910476 522910481
    0xd02070f0e071b150b06250c0302030703080d050a0606080f0406060918020f010201020301080a030e1504060f18151b0203010c05030a050a140402040207061b0c15 71
    0x19014842036000e0184080c109030a00d0790b80c000510325111040720141e500740030494070390030401d032007802c2d03020381c80c08115425015600245005981403403510280039609240c8070034004650246144211001040c00341d004a1540a190018240d400b950307681c1c41c000c4280e6000030411030300203091000080207100148568070440b440c5072940c012030368a40d140726602401c001c004903021580ca03980484c07032039a0b81c821249854204065040f1044880c01000560300d01c103031500307045a00402c0140180180420700d03014895150410410606682000400c0010912400780540101043c005507444d8461800100d20440361a030380c0c00c43c0c121140071445403d1074010711094011080d0200c4016110b807403503100104940304000c4003850164006400c2d544c6442c0f004000400100622a82c4800791040c0c5401c00940041000499a00700c2a28040c01e40207001030710a03a40410380e40244803035030300a91119001034000c206415007840001c0d05050040307405550b031014a9442c08104045803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 522912976 1250 522911726 522911729
    0x1030c0b04030f03050309210a030f050c160501091a1501021605120102040f0303030b0a17070311030307020901030b011820220b031602010506091f031a090d0207 71
    0x18003c080b00700e251802d6429502c050000c840d01d100782d08181180b84442030000140000c00c580c141d544500614000381038034640d20007061013510b0b20041c800c146901108540d5641c1d0703401c1c0d40098080841c140303540100101c0c80081d10000c2c0e264600d4403a0102c4080c81c034800c0041000c04030103107400300012650f47c18016024034154606000c20301c914980100e01502d107641c41c80003d858681c580c0c046420401c12580100c1c00700344ca84a0040b01c0f85042c0c544003002d4800d004101c0b1049040d0010b196507502c543c407010380070040e40c0d404114603440c207208a5040e01d402400b40070065039a480c2034814101c091081f01c849083c00700c042e44004103540140c5102940d0003400d11004410071003100016400a844542080078450790205d440d10310650543c0141030341401d8544a181020301c000079041a0741444007103900d0001006165600c41b00c041e508410b070003020121000310f16117403c3c00405203030405041101524000031031140c0c18014248610310800c19035115200710b6209907a02c0286 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 522914226 1250 522912976 522912983
    0x608090a020405091615022404080a030b0d0506010311030a05150603030c1c031503051f0f0f0219090602100504030e10020d020c06090f090411120601030c0b0403 71
    0x680d46010241c6010b800c42070700242400c06039000d00c101440c50000389202907012510a0b401c0000302c41e00280c041c03002c980c01e04030014140810740111204c00100103402400200303840408102401454440d41c0f007a2510100034010344520480b07400c050f9513490b02444111035500d28040d411409042c0850f02403910b1794458020f040b200c2040314181c0200f1801451a40c1511060282120502c0304201168402415031704618811441c400e008056034a6540107841c10703400d14604000082e000661301410308684c10030034030701920300b600701c4000d0032180025144090a10490040c1c4603003950060460381921350242c4510f080401003600e00d0480d501c203140250300301925610035104140c000d039501ca40301c0d20b0140500010680043c0e480e950fa0440400180d0003c20350906240e0100300c0c140340c0040482d201400d082410700010224204230316514007c0b01e05801140412011484402d555a4000c04004818100c2d5400e01d5503403900744400d8038503501c0d0407000286107280034129000d5980 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 522915476 1250 522914226 522914233
    0xf0702060a022b0e06011e050f031c180509190f09122c091906090507091502010515040903050f030c0304120c02102d03050106030c09050604031e14010f0501060809 72
    0x4d48001c002020448107c282d40601491605c0c4048030bc4141808408205907202c1000070183c081201641140035044540100d5502d8240078100d81c041c0c032540d075820340d40c4e40085020050840d400000c3e005803400101880400180690340b1504040034444d0380f1703500140035280110080303d44040ba10741fa05c0058002000002081d01c61030f01b000c6000081600c208049500d51340d45d103c03481120012114407000841303803842032060010307283c4191100c108502c02440b107030902030380421101182401b11031245558501d038000b0136000b003090f901000f003d03501c0b298907454880c002c0c40c0260310440b011a20b036687c4e40707c05000c29019031800703035101e500a042418a583c0222007520450201c181c0c90400300700343c05454803241a00a020302d41048256000308185d45400005801c1d902c400e8076074030a121a0b900c0074802034841209071800c4a0300711403210031144800b00c0704070003040c044002400e0a50300903000050b4001c1500310844600c0320032401c00c042c0c3e0361200e0498401c141501c1640c0c542c0c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 522916726 1250 522915476 522915479
    0x111009110d0201050c12190206270f1207030e0d0c0b07020d0609050c011209020904170c030a0306140f1311040504020705070e0f0702060a022b0e06011e 67
    0x2481c20030380d0301e25407040c14114980090703020503900c1e001188000d14094140050202210440d203413040c940102a4002007855060101e522503003414080c1c03008240000003403160070350400801ca0400f11001c001e096030a4103c0c4940035084541c1310a40513004504c0b00744602c086401c241c110001c070150803002c014066400c1040005299205c40c1040c3e034081d450361500c4000c41c11520410700710911500080081d4200800050800081403004044552505842c2c0000d600c03664503590b84158060414601c9003625496214540507800c050702403440b0209003070032103981541c8005c054502200c03400d5a0548401d0421407000d100468441d040030355980000440e40483c2c000980386012825118206502c07140418201c2c1c01004c8251741030741c01602d00b000110400d1903840d42065102049070114a00b12101a41d940c2007d0107445002d50700003407410304102c4450300d4813080c8100e41d11a080c51171203001244050181000d01c091140100d0b400014292401d883d00c0422196a401604001c1d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 522917976 1250 522916726 522916729
    0xe1803070804120201020307080a0c0b06031b0f030102041502100e010c120c0e030607180b030727030f06020a2d030207020102190501140c18040c0c0501090311100911 73
    0x80311840350485c1944401c0c0300c0c030000180d0f818090100410307036940d551800c07a003078140005201c90150805000340c00248418109007005060707460f07050015242c8042e02d04044010a00900c1150701001c4d07450b01c2300130340c044c425031f0108882e0090b02501c1d1045c04460308001e00d0b5400c849462100c01e004c112031441d0b040304040140c01480d4201c00d2424549134914000b40801e08001d8200c6201000644451421100701c5000d0101750103082c070155814103514002c0c0000c0d1503075071144840d00c01c0903041c851200c00f01142d000000f0295a10860300c610700d2405150800281d005203810202140c030300d504003030304090044409000c480468402054810205c5020340003075201c62416811406280041c2200c0303c1400c60100c28148610b000103181c07241c0d2003044100d4200075100922415040122801a0000710a810b260701022a0002003070000c9000646551030061001030255083c0301d40c000503d0741001000c00d4150011040e200052140c0910200312084580010130041c40440f48942d039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 522919226 1250 522917976 522917999
    0x7050a08031e16210e061e09070b130f031b140a0e0c09091609050a03150515030a0f0201020607050403050312060a03020a090b040f09020d03030c0210060e1803070804 73
    0x4003c2c11104d8070418000e80a403c015601e03e8894030015030b100009100e02005050f040c00f503408000d640c01e018505200700c095817126600d1140b0300003290081441c044103400d0b4010903000304018054071428a46e249492034200b08112410340400c0904440052655828440d140414000070483d040084c20f141000c902c000014160240400c01402030141c29140e10344558010a0410885a071110074440d00410101064000c94010080b0700c00400014000c000b15a0010500b01d030042425541c1445000141e05426446945885040101002d01103c6030301c90200d24001c1e820b8503002e99458030b00791001e1103a032000400f035600401c0680c010f1111070400310b81050004003078481407503881e000500850015000031100d181c0e0b43d198001a49400d00c42e4801111200009001c00c1d446e41d000209030881c200303006414076864101d03081d84a4030911520000e101000000c011058913440c1c41c10070907a0860b010710f100307541e0203502c0c800c00a001003034407010341d8031004030b901e09410102010075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 522920476 1250 522919226 522919247
    0xe06010807080a0e0a080c1612120e0a090f060e070c06020c0c12030c0c0102060411040b0420070501050a0e0a03140d02180f0f0603070302070807050a08031e16 70
    0x6080c2e6030320001c1d0b07013140c01400410100750162000980715031030300c10258140040c07116145080720b41e04100b04803107040f2003001010141c0203412001448a01da600f40c1d02c0f40700700003125900024505000c00d02c0384095001e03a0b80c059803140108121740e200c03400b0b95460075045d14101c0104019418100006144c1d03001010001001d1068691404800000c6000d100389200810a207070000300e1042c845240c01c03c070f0301e0f04240091004207450b08041c0c4851000e60f003003001d031500803170b1210154440c13500e86811000b00c03442500c01d10540c0048000c0c260095800c440c50071202c6500b40b50200b4444a01c034015140e01c070310700401501c00d12030300b50f8058441991001c95007401030018403003401d513203007148050008800321100c001d00300505d80e020030031004d2a01540c18030034800c201c10401c651311080c0503294000107600300143c5e144000c0c10181090b00400c40010f04601c1a0812081004501000b440c0958107803006100d44190618009084030700480d20040f11440c00780c280303c0f4062140e4020310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 522921726 1250 522920476 522920491
    0x603020609041a06190f020a0308011502010209030a12021b0f100c140a03030605030d020a200303070606030b0c03130b04022805130606020c06070c0503030c010f05010e0601080708 79
    0x1491400e518001c00c55517004044003040204514108880c0385412017181c00b0560f80d2807001c1c01d4004d180d5031b0040c000f12418003030084800244840c040c00c060007581110045480101201d940c900c280c5403d102d02c410b16942d402c014020300c017042511911948a0420200f030080000e40e0312079014040c42102c03039000016404014440d0800804075802d01d40002d41c418510002e40008901824041c051310a150310040c013961080d40200703a191340c04550354452683c0582d03c01350400c04000c13800301c070149810095a050100040300360420140d903210a00b102d101d0385140c0010b543d0160ba030003140c0002c0320411189401c0e244540000b84207020165030062000b098090302d2254800007520004110f40850140800d9510a010130302d80000210320b100060300080c0b020b40c0c24844020b4440785000b50844c00740d0300c0030a610702040b01c2080b128000e0400502101e403154420500070b8040e0910954120490380b52000100361040c00ca9813281c032480c0107840301802034444c0e41080390a00c0d002032194 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 522922976 1250 522921726 522921761
    0xf160302040b030c0d0c0302040606080405060403120b060a050319090507120501110d0b03010605031f050c0c01110d0e0a0206090607030e04020415110303072003041a04031203060302060904 83
    0x800b090b9070307200c43d24445c40d8010512240c03154150b206002c219002600040103016130f400400000903000103400341c1c41a41480c003028495aa05200009090080701e42d551141d404551420103d0380300000d18811054400610710001c2e181d002c1e00100e480d1100013400c1500300360828005a2413902e01814254851b000014240e1701d1210f0051441c0c1029030070224158640c101c0c000c00c0d01e803d020302c50251204074041c0010101d03941d05081c16006000068a81944402c00110b100d82400c05031030443c00e01074000d110f50704000561440c181c1c4050039240e110740c500104c000340d5680002c0e00b83c41070356020b030844c0e141c41810703010010340c0d4109410850412138a101441c903036803264006400202200b010766605032241100103061000c4461441c901c540c8144100101250b011003014100c4444200d042c20144280e0600d90961080d90081c01e440c11140724100072100b0050020001c4138010544450003800180d0708905640c0c05e0b2001a50140051000603030a02c2e003035010441d42c13000b10006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 522924226 1250 522922976 522922993
    0xe15040b0309071203091e05240c010203090d02071a0a081f0602060901060914010e060d0b1509070c03080109020c1501090504061b0804080904060e0f04050f160302040b03 75
    0x4813a90383d00408411000544114020000002d501c1c42c0075041c843e282003014012420503001c20441501205084021100c1806464050003085c0417101c1c03040280c1c0003903603240790101c20a5031b04c20144903200700500c5001c03000a84074114009400122060414040c600f803022841191000320251030514409104007802d06449008883c8400601c110740143c071840c504034241a013190b980754489060541800d0014003802801450541550740a60a1005680703e080128a181041100c000c0905501006210b0354030303043c0c00a01008401144c55692640c1c1d599402c0710501e10000340103010466100c01440160900d0f0060500e242480301101da00b500c03405002a1544002c2e0300201c01c1a0b5100e050005200d103a02800d260403c000d12201c505029107c030040500600900140c4410004a140344280c1c0d0780b900f1020003810320101d2800781c1d00300007000070a214000c0e102240e081c45004c01450000c800843c607104911400d4001c4034481e880c640038407018100d2080202d40c1350042500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 522925476 1250 522924226 522924239
    0x80f06090402012604030f0c0f080708040317040f1d0403030902030f03071103060c09090c030406092001021e1207060905030406020706020c0616030e13020d0902010e15040b030907 79
    0x420f140c4da0200304d41c0082d203400c1c9030038040c14850505420108125021300a000461851801080450360120110b0761303178100e604205280d4000e03500010000c648400929485616801c040d205640000401c040010b950300a00110410440e409240d526044000a0042802640300c01d10f02400a070680e804294503450b9070381154810030701200c21910700815025241002c03c500340d80001503002461514125100042044c5001804002a5030313002001a007000300d603401010440b0780c08401420720184c1003480000e085200c408040c01440303440c807d00080d0070070407403807810b4a900c0000703400349204141c12000380c1d9010390310588280381c6032148030b030024004100601c010701c1107a003d00109424518003d040074800300d03401c1d111703ca05000c0d00108020364000b1a200741d6150400d0006a10a140440d4181440320224610148042140c8124018a0300b10304207080c403da031341c649040154020000640b00c400a4482c0c0fa200900c824808507200000840e0082010070440b400700ba40e0f8038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 522926726 1250 522925476 522925517
    0x9170f0f01021809060d140f1e0c01140423060a080105011107031a0a0f111c060305030f07020607050610030606060807121107062901080f0609040201 66
    0x4031840380c1d070004001028035120302c10501c1118044412042600380900000d240000241025094806603c00030340fa17910208400405014600701ba03426504071820620107281007568050302c0c90181a450900c00c2d8800d401c0c150892245118041c18035041c0b080c24070820751400c915495140400840862a075264000360800301c5450f034940c68558108800140720080d040c4104046600c10882480011680c40c41762040c0d01002c134000030591b8070890f034180946030010306c2000203031a250b0510740c03050044000704400303e840c007002201a1060340f55141202c0c4144070140003900144200400420b0603401030103071034001070002c0c0c1404180e45400e82040c0b070641d0900c8040c5200d22040080140c4c80c01128024101c038188171015150014010b0400340454004441540d52160700101594500c01503820068015004004084072038200303c110343e0030080440c40c00a0500c600c8602503204035030b00d501c1101d54808190b05a11940c052051070080540220b0602466010149111140c070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 522927976 1250 522926726 522926743
    0x110a05060304080c0d0c03020a110f130501060305390c0f030301061d0f0d051c0c0c050d0c060305090c09040b040b0f010b090105071502190305150109170f 68
    0x740d40c40c90361940744804492600d4100020207086c031031441e001401007500416180307104d42d0095034888003540624005164055002c01465204004696050210309980c1c80181602e2540d02d00304941c0d1180d01400041d0090141c03614030200000e100030b444200461038514100fa440726115040441102d4021b06006081401904e20f9101000402110f98080c010380103512810945404103141742c1c020900c1d01039000320b801e00480000407460b08001d010024000080903900042c002c184060304000c00180040e2000d1340d0080c40b201001c11a8944182c60302196030380710b11240c900e1b0f407030140c3c160003070320000700442c90b0360042c07580000081d00c03154017103446288910010002403905180c00400032001400d50308020580f8401803011b030200500310350005009082c21901c0c0c0046242201040390085101c200603800400c02c0243ca200c4a501d810b9030001e00e4400b4041d130355803800e4020000448030401400194480e0703041000540e49848506004200c40c15130f181d12551500c1c00d880e2404d00d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 522929226 1250 522927976 522927983
    0x30206070305031b2107110105150f040e06070f02011419050a110414030a120503060109080c030d110102070b100911030f0c13030f0302070f170a110a05060304 70
    0x204050000c00401300c00440e030200514604103c00140b48003540c0034600206150744603484040f0b41c40c180100a948402240e000003030015140100900c900301507440c004a001c0c240742409071500c1d1800740903e5040d079010200508143ea190402221110354944244055541c2e5040507201d001c07400403454807401030916121825004c3c045000b04030f90006011040040c548848860540e450310210760840d0f0a50028a0140405070002401c01003a8180184000f00002c1110290f035000b00c007552007a0001d8850b0341c2d40c0c903928000a42c560711040c52031139168101d042d0507100170b80680111848034805c07100060030100d0070340d105100e0b0503055601a103400d540b0301c800c00c0480070b1401901454401341b4480c2d4114200032603800495080a080e14110100c081019040752500001600c015504100b0300c19a4001600f0301a44820544c000c1074142c1c0207182c00841c160110f00200311049402c1801000405055141c10220f5054481400d43c00540301d80b0028665035890041c40c001c501 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 522930476 1250 522929226 522929237
    0x70305030609010605130510050c0f01051e090c2e110717070e040f08120a0f0902030319020f0a23060f0c0a0504090e0604030f0207151202040302060703 67
    0x10706008111120390140c3c4000108041040003c40e14000d24140d0400c031901500d0424000d904100280da030350107101041092441604480100c4600540010380561340300c91030320f544c1140880845004a01c1103807800281e5200710340061141c14030344550031144d0742c0200c0b246081e401204500305000c200c070100c1da0024a4140840318020f00034401c6000074841e617401e04c02c2408009d11165200c181ca4404e00388154600400034003408060f0030150202da500c81d54203590b5070500c422915403410b06850300020035107003d944800070300c50f500c504480203800030002c40c10b0203a142d41c003c1520032129008005c500641003480c8184a08001c8000703031901c6a90400000784112560b002050307007101d02042c80b54000c0c0c043c40340c0402100803081d082200d0201096a8404070708046d10184100e6101d15801403405004480e071020103c0e446004902c80d90383c0302e0b00d41c0b0340d0010032640c400e114014114004100500565514040e6000000c40c2c009040c026040c41d550750001491600f054405a02141d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 522931726 1250 522930476 522930481
    0x4050717010e0c25052512060f050408030415020403021503060406170d03240b0a110304032a0e0a0218060703030903180605090409030c02120d030f02091804080f07030503 75
    0x344014002c608000d41e002c6d10503000e1480d1440410968400c24800b883c0e418040c50a004840d0843d40c0e545040302c0043c402410140381000302d40e4812038040e5840e4454000f074510008079030003102d0803250000d220509080d000b1031041d1641e4006010710740e11540d95240001c00154400403140c040346c80b20301610b07945051617000760941d46d505040c40e240004103203848940c50001c0c2c801e6004d5612160015880e004c1c1e441050714640000d0280c03074505e20000c40c00100f04140e0803042c100c16180800d1580740310b0381d0b4900c611030700c4120380581d46003250094001400d0004075800340684402e45440101c0d451441c00c04200540c0c0042030a400080d202c10422042c180c00c568003520704c1d440792038102c55035440c0c824010128090765404a1203a84c40300000014548200c1134281d20701e800a0856480c800842c040503582e220101c45200803900341405070b007007982c26100703464540e04050200403000d0070001d040180920020002c0319038420900280000c1042c17100a02a098826240c40340e4a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 522932976 1250 522931726 522931733
    0xb0306040827090c1b1b040c031802090613110a0305131205130806100806090d1b03020f0a050604170705100c02030c010f060504050717010e0c25 64
    0x1000a004040320707029a1000c1c0d4085520350746402544820401042c64a90f5202d81d080544031226031001c44a1b4440c059100c1102844800c82c4842050102c50400c1f4284038240300307a050301e0040b21615175041c04240f8120142c01c00c41482d5610940040101000842c0421018116031000400b01d80f034034004191040865018030407681c002c80b41d40c80b1f0000b00c00380c43e030351183c000d01d01303020b841d00300000403e4420228100d6403000014000c040d0035103480d403030009004043e00c9058490103407148140350100b01c1101c4080b40360320400d1104d07529262070245641d6198070301c400002c000c80442c40f8904a2500c00d54082c031040450500c186d01604880c00d05040414000071203034546070800c50208043c10004400140c410b41c02d00c058840880c86401c1c1e054140c1c1903000340700c41320456500f0020814010b070150f50101003542c1c0100c500b00b000b52154a0300301e480c446140080342c0b40300308100050141c0c45024204e503a101503084626442c240e04907051380d90604980390000483c0d0030b800d01d00700c01c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 522934226 1250 522932976 522933007
    0x2c12010c0804150506030d0513030f050a05120c0a08090d050303010627060e012d0903230d1119080a110a1119090509030c250302040c030b03060408 65
    0x29101030300740a04c40d90a1100000781c555003101e45402c248040000c0075001d03401c2c40007403000115080340d8004a480784a05003107444960350f407030031076850088440390900115080160765a824088004200200c4581d43c0c44070700713901c032450391940060520400da00046007080110702808899807030803503022059440540740c02e00c5030030b003081c1d11020103006c0c0300d4154080c8400c280c46809103040d6040c030f00c40300c0c01c1901d18041c00c08030008105510140107125a044005401200c2c4503091000c0070035041236012000610403c44ac01d05908007040340c44503c1c5c8100940841e02c040c1c030050b80c0c0d00705550614250000592003080712401804550281c4243c0c000c010303070024900f07032005404540030039914845440101c4003002e2040d086000f18070610350400e00c855020b00b0755403e0803c11401d044050075543c0d00217100c8003149124680070080b90542c081284089074070081e0310800a5401c5608002c01340c404080744104065a5540e0030350342d41e0b070400c1118069800b4803041c544e20003151003007820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 522935476 1250 522934226 522934253
    0x3060b0409020a1e2c0d060b010e19050907050d0c0e010905030d0e04020d020f070515010f03030c0b0c0c0a0f0b01090605061b0c0d031701062c12010c0804 68
    0xc200980c00d40e584a465004a505c242c00c140300c80c601581300801612060080081040c1160030013141c104182c04c0100326071025000040036201c0b8880081507504228800020400c505000c01040104006178101010740a80000c003e00305141040107101d15074003111417450030400040c1c0c1c41004c2c86900e5802001c0c000103850240e000d4491002d01ca44060401c800e039801050049500158681441150b40c2c10707502d5191280c3c0d8515502da030070b4200170340e0b0b42c0c410469a04504140e000000381c600c480f16050011694180c59694504030144c98000c0011030041c81070702030341ca00f0030000300c100c0d07024041441000d1059a880704a4012030911440d0100b050b00120581e80c40c0c0ba0041c021940c8083c10b03103c0b900f440c2c0c20142015121611014148540c0100f81500b0050451403501050781240c2213040038001050200940d82c0c0c0e030802103c03400820000200d02c01581200300c2c0f90340070704d135408490000c80640600c20b80f0810700c10b04c2d07003110846802040050120000d000c20084241000354 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 522936726 1250 522935476 522935507
    0xf0619060b180d061104031407060503090d0309050a080703050d0c050306060d021c0e06070e040b09060d1103060721090b012102090a060303081f051003060b0409020a 73
    0xa041c0341e40a100d58030042d110342e603042d105888810b1882c2c1042415040b0745501030f04484083e071140c0d560b150184000c01c098040340401e024103200454258466810f4078850742c0d410300280f20141d4030800c250f0040170702880a4404d401034440302c40c04540f8007401001c14510999500341d48088001d07180e801c551960070b030707401005010002e22040d66158019540048e20382c0900503034601000d4030f18050341e1005120014003505111109110640101c0c05e5841a02161a0301c030720b2000c64401c01040740d51b030b0000150b0000510003c1442130800000f4180341c02e1007462440c400c42e0000000a21385601100e103440040c5d10080e1070a60194a01081001038000c4641400030030406d60322200c40340d605014914010125a03101c1c07080e0003a1000450004d500944440d03001e050419920018245602040d004281c0000c04180d0941400c1c840e944c0302c00c50815841002801c20040154150544450500300342d00c5000226083d610400180002e000903040143d40f1003070b52401074555a01c0c08400e8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 522937976 1250 522936726 522936749
    0x612020316241106070201060e0703021e0c01240503280b07050409020c0706080f0402030a120309020a081b0109060e010e01090b13060306090e120a020f061906 70
    0x100900845260141c0b00401d01601d00d42c2d80603111a030840f20604052150202807262009000b0401e0301980548241d03504a100507031140d6489005806078840c08203007842070040d00e000b10780541800000303080c10341c3c0e0900020074600102d00e51100800d040030424032001024480802c014a4200042c00d90f000060f015410b039240030010b4580300441c0340101902c1c2910b1400001c007124400c0d02210043c00840740210340714259942d400f9600c0d0719901880000c03810b084041130100c0494121544030740d03070090080180d030341d1566600802c0d07040300301030724241902c405240d001a540c45800b20080d00902d4001c14024030344184407000d811008102d1818080d038031030107101c0140e20001403e041c20007820540d0340311740300c080100c072070104940c00601680000320b0803920306a6071204207004c8030b405960500403e078403902101d0482d18a0000c4145a601c00a141c0700021200d0010340140b03041c600580745400207410fa00d03400d005045480c20070f81d80c400f91003018500c1851003408064180500c2c036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 522939226 1250 522937976 522937979
    0xe01060f0e130e07091a1c0f050106080d03180303091707060b040501060302190c0201021c0f120b060406030f140c030f0c03060d030806030a170c190b07050d0f0612020316 75
    0x3d503101040d00070345035000346800c2040788004840c1800c2c1100d421361100c000b00181c0489c0c1420b50007012103000d03503c0c036800f5130702e00303015058440c0c02030345411350070b1400c100587e01103581c06400400101404840c04e0003041091016001004040c180c0c4c18051480802d0f050042d07410800dc40f84140c115406240c03051025203815854030528995044203810711400700c1e056800107038903080c1a041041d00c148902c0300701401040e07124441c084038200341d840310201d0106641036441515440c0c642180c2000c7c00b80710400c0030768482d8100c00618282090001030340c00c5440108480c50030211034000c2c00345000070a000302c00c2c0f801c481082c1e018000c9180e440c151706000c07000a018005261001d01002800804910030f59000d000c403921035a031101c1002d04c500e0340d801140406402525800d82700c0d00892110f2025104035810f14085294043c418905070398406400b69450380024112451a0307603103d070790018a013070034404c01c4090070b54007880102015062040600c0c05810100034100e00c01070b032a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 522940476 1250 522939226 522939251
    0x3020901080a09110d0c03051009020906030f1b0105070606030b1e0f0612031b07060e060c0d03051306050405012007051e0309030114010305010c090e01060f0e130e0709 74
    0x60132100d444085903c0203044040b401d0000c04038034550005061350041c141496142c401c3c56004190581c82504c41d131640c0c0d980c583c1050388030b550710464000795820142c3e20b5002200007201c0343d07841000504000307044c2600d82d21203404564980e0001c41d66142c20300301b03002e5540448988003142a602c1d000c0043e103883d01c9010301c6000b20000d041a030003a000300e080380070400f009109480743c00811000851380d010000d500d4a40d00e00d07440c403071000414602c1c0ca01e8a240c2c10042c0c01c4a21002001c0002c1c03210880c0c0180c00c400a000c001c1001440354800d2050300001039aa0051601580c020400403560203c00003140180170040305681c9500c803c03c100742c000041010800c1081c0c0c00341c5c009900744020000040509502c034607461243d040d40303450048030342d600500d000d4038160781c05400200203400043d001038500084c54020603c42e84c550704010000248110140e110031000c42c6422480c0c003400101160000c030000811006068549110104020081004c200204907080051060f80d5a010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 522941726 1250 522940476 522940493
    0x21072105040b030a060314010c08160e12150f0a0506010c02370e0a0c0201230604060e131a061e06070c0305150f010501050909190c03020901080a09 65
    0x80b52890040b004400580e4840380c03544000c00641c0c100c0c551801c4049078604450003040d0320969a408134503144041810510308011a007d0b40c810340d20340d240761880560400c40c1038017013400c01e2905031166404602655a0703041e10349001e00c0f08070364409581c2c1082c150090035100010940d5040107221b100c480c0240c0c0e504200d050b081429031901c80011f80c94400100e20148000500c0c1080d074083e51000151500d03441403051180c401c1c010708004580901504a0985143c2006080e82509a009141c1400444081e00d5000b0000070300000b0155a03d400150103144203c0c0d0b204901c040808808080c00100402041e0300d14000060003081c0ca04031000820070103182c0000685034442088000c00740e01c810040701ca040b41c005898003805540e030f1504980c4c86140716140303406651a00c02060811100c103d40a05885d416107a947c02c00034250184480d00000070400700300c498200c5c40000401c1c071035120305a041701080d42c01507640c4040100162890101030b04503c8203902c0d0042c0030020400c01c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 522942976 1250 522941726 522941729
    0xc0303030e0a050d020d02060c0702060304140a020d030309021207081c020304050603040f1401050408070f0f0605011e06090b0a0c080f04090f06051807112107210504 73
    0x1414001107040358210784600d0111104001412845156003031160030b5000500c804030b4000a81c01c40d0100d07607a8011a01e49406100c80c0250880c0050004c40c000440c2c04144c10604a07894040702c203c1d404a40000c4e0180403501400d4000ca5510300340c0300e041d81401c03500c90501c81d9008008202081c075108103e517607044200300643c0078030001c0007a0424244203208480c0103200051038244c40e07080c14100490307031010907001100c2407e4070300c8501390621810702070329104035004280c903418001d6a85800522076214402160500306982601000503180c1c4201400703845103c0a924160b0039616080b254603c840e0840014040d84410401c050114101200d001d6080745c0790030024180c207071500c2d5904e401601d0066001d45804140450307002076550116801004200f0244503035680e501c140800b110800340e81230400c3d110306000070004ca0081d56070300031052a00045418404a87c04481c20200d40180c100c030000e007002651006102c10313101000300451018143d200c61a00e1003401914902c501e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 522944226 1250 522942976 522942983
    0x3030806061210050103050108120f0703120f0b0405060414040210110f030c070b03010506030a09080906220f050105030a050a150803090103140106050d150504020a021b0603040c03 79
    0x80000a4403a48a1074207544218062202080b05424010540100c480c00b60003010b0000e4504000002c5c600f1000600b0448e00c1d941054080c548100d4002d031000607440484160288943c0c8200480d00644a00c60840200540032001a0b041040d03170800081c0c030405807003288214201907035604600d20008134241c010354101c42e690b40084c61b01c3c0003078a082000498800c041d0090450b60400310002100400c0c4101100d015201c0b42500d900b000807040c00203004140c0c1080051001070300b6070880d07911511050b8001c18499040184902c00224568011075140d80c5410000c1285c0c10402081e500240252444440030120305003420002051800b0003028034540351b4460300400e98152040e40300550010740300b0003070700401c0c2d2a0600d650780c80c6d0000444d603002a00d00702c012004c24141a0015059580550310603103040d580801c0d0101130a1a030140d4178052003503040c0011142c0e0f0300c5c401055800250303000f4000811200348810950700c4038002085c02013904100300400248001441c8064951 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 522945476 1250 522944226 522944237
    0x16140d021801030308090c150901051e0d0903111b06030403170c0a0206070810050607020a151709011a060325021606020f070509040807150b0405010603150303 70
    0x14240005142400d00710145a8800709100010040c03507406040135204e80704003012a1210803101381440110180301c16400c03c100b200b07100f1482e6942c0303d04010907514044544622215040c10143c0c1803aa200c070300003a840070ba0b108104000c01d90090490422a103000c03026103907802c10218180101d0304e0601b07aa0780b0a003c0040054101800390f1000d001240c13442a0b11030301490150100c4405030b1100e0400000340c800c030000211303254800d00c000d500c5142150a64130220b880c10702480341540080b0002c07030b4001000c0750046002c0f040485590000301e0b054fd201103c58480a0b1511041400a0700e041c0313159050500c554240c040d80111000034400031780e000c554130358034000c1c82d4800c100c20510286803404415131103660264009801d020819405040d035a04660310407050f81c0c2c0f01e0b6400d180c2c074247c1d041400c08111030701c1e01c08084c6512902825549242160302e0b65282c41707c62a050b41300d4842c95613960440710a04042c45118050040e6080810004541c10f49803d10340d68a484014104078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 522946726 1250 522945476 522945499
    0xb1504081009170307020d030516020c10210f15150c060209030f0c0406090b01120e15040f06050106082401050c030d02030103020f03060105010c080a0e0a06020a0201021614 76
    0x146644074a1076001403403040d075444e800d01c5d402c002d444010640c04500000d0403d00806e1aa024a80040050b05d410b50000c0164070204018017805010420f0700ba014040f41403c40c01d40035040c40511810324516600000d2a00050044030013182c0380484c070040105440c0b80203200c64118480500d403100010309000380c04000c5c0e894088040d219100100d6010700901d490224043c0c8001070150b041c2030308441c02d00c12503844012820454081660a03400075000c4101d079040b103072555000104405414040c1c80c15011a900c8a47c03030714609640854285070031040d000280320451290300c1c05013a41e07141403811814080b05001000095061200321910407081c0b000080e80079000300c070401da02580c20b50791680356192500c402500248026801590b5a03040e202051802142140c16071b0300503100c12900c12480d413511034098120710140e0040c40ba2201e042601560342c8a07030380c001481c15500500540a50f8800281000d074010cc184241200402c0180200200c440394403a00c00001d0383c1090540c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 522947976 1250 522946726 522946733
    0x30207170a0c200d110d06090309080d02010b100e0307051c0209100302011b061509020309190c17070f0e01030b010602030a0824130b1504081009 64
    0x39609059444408600052100801c0d40002009004034001e401a10003e0001941d0701c40b0350380450380641d8484c410f80138600010b02005602280c401026180c0e51100980f960340070b0403102d0480c02a00401e246030700401050804211301c841110f410f00c024001101000041541045c9050000d01400080070100c01075803401c100420051500411000c40c0d06c0f0390180c00041c101500e542079001d0f60941c0001000707a520008030710210baa040c0d6030305000c04221590140030b80c2e641072084840b01d84031030540c070742ca28664981e0f0700540f07a883c00042c2d4904046000b01e26020071442070481052450f21004045810b0005040441e000381a40c085914074080100d82484029081040741c0940c4900220b041680c0c80c01c050f040c0ca1080e4404103541c0d80f10102640d582c051038918a0000d510070000510200645085903021084c2038565104001507000190b0340850ac02400303c50203640b4461002c042c070341202011158042e4803209480c250400b40d144d0b4a0f0305100d05461105904c0d0320300300080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 522949226 1250 522947976 522947993
    0xc0a030f15050c03010824010302091e16171b0c0316050c01020c0114160305041d09010c2111070c12050c120d030c0513030c0f0e04080a030207 63
    0x11290084010001880c10b40c4010f21550400e000304180c600c141c10001180c07400700b061001c0e0f00000c3e603500280681c0b80d83e08001452800502d001401c80540c000c1800b888692250765000d204407540015188071903910040401008150301d06403150280140014403520b81d60080208000485040d984d8600c00350b054078600c900109600080811031500d014854089121409210240c0c06e0b00c3c0140364031001118904406129009240c40410104803200400c0503110034080c800c1c100340d410541d4035003031410111444110101c2d844420410420208400e104004901c80325040a00002c0003100c00401028006054803840644d51345a2008c1c100d8110140e070001a032119030230384401e0300e81400890f00c04d24144125070303600c101c03c680344c2d092801da8104459900404020120480d8000c01100a071141c2c11084082c042c0400c1484442080020900003a50246061150b10341c03070100d01c80d40350081d560140d034030f560b40c030828040080c2e0398100f220f2410465290158170749049041c503002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 522950476 1250 522949226 522949253
    0xc1a03011d0403050c070803031f08070902070203070f0e1005010305010b0a0e04141015021209100909060801060e01050609180c30060301110a030c030902040504031707020c0a030f 79
    0xc01e44246d402c002415400000114441d000b400c079400311090120310035035440941c2c3d000b044125000840144100032455000d40f08941c002001c9907417403a526030401c1c4482d04203030000040d41c0c0d141c4040150b003841080c11640200402c1ca402c00456251080b48035141c0110403084017000b0410040c01010303a00c5030041c180c03000c98064003000718140514250301002c0c061007840204030700c00d924544940d0022980d4241e001c0b48405003072400304141c040000003a2040e15020a02440c03480c0031442c5007a5110b200050075001d0700000b56070f810a50715514209050780a18401c4500300302e10001e90700c40d006140b50366840501400742a4680c3d0400380704501400401c400c6940c40174101036030107d0160700d1403100da4055030382098240c40e020181400d841c68030581d0140303100108034483d9458403e50000405495501d00058107500550008050310401e640c10b07000280ca0030709400c10421444280781d044101800100000002c20f0081070718112144409030495201010050520039032400303028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 522951726 1250 522950476 522950497
    0xf100e040b0a03081908010e0402100f030e06180c19050609030f060903031006020c0109270204080303070f080f04060b0f03030c1b121005040f0b040c1a03011d040305 73
    0x60300c501701c000d40130303c0034240c1d007811200240078a0700015046861005180c01290082c080001c071107283c64094803100401d0b14250100359485041c850003c0c024016203005010180c580406802800340c141d01c3c10340200d00403841503001c0030184014010703204c0e2076001c6901c251001c94952205400290610146520440d000e000b20710030403410300004030007148915002c0303000354403443d111402260303903601200482d40400c0500209104a59030680002030035070380152003104a4840c900410203071380052388003075116030000c81440f00c002d070130032580031205089203000c404501c0d1802c010310070b14801a00c050052662405505c110391254510800c1c00107002d412660350392402540d2540d03d619560701142c4100c6034240200841c82c00b03071100d808008034039005000401e05140750100400024008940c1c0b02110340441c800510a0340700d1520481c010156664503a25010800c628042c002c1c00741d0b07401c0703d001c10041c00640c4000780c036030410b40c4c54040c0c1210240d03100c2c6004d840c50720075404c1c0c03038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 522952976 1250 522951726 522951743
    0x6090215030108060f19051f08031803030901200a02041d0c03062a130f24080109051009051612020405010c02060c010f020a030b0f100e040b0a03 64
    0x88500c030052200950403074651501302c80541e5105601c502480c20141c50240d2a113580881d00c1d0760b50049600103d4200101d00e603c0d85903030308101050000c0c003005074003411150300007280b00015503c194441c801c8000e0194081d500d46400351b0002804d42c4640e210306506030100c1070141d0541c1104000d001c02c1981d000d80200640d0301101b9100481d031508911503091440340044c3c56680b424040383c8280130304c518101e002c011119082041c6149505040300c99070503c01802601e080061020042c80100300031103450100320709000d481031090324030320503054841c60144401c03040340368092221070464460420010f040d403100131081e00e9945159121300070643c2040c0c14440c005088401d101080d1980c1d4460546444030803140034213034040d903c00c150101d003851030b0880c054100b850007000d001d1421310000404440c4801124102d812151460000a0307490420198a040c0040346510501044880e00d90440419000418510500d074010303000b69102c1c400408541c0752410500051030b44003154 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 522954226 1250 522952976 522952999
    0x31008070f1e03110d020102251502030a090b161203050901061e05010f0c06020304060501170a05070504020a09030c080109031701060c0605131209090e01110412060902 74
    0x40e00070301d192a00414001480307100c41100700c8a01d1070122012264080c101981140b61801080740482d5414004e905600a0b590807a00300c1268400403c00310030545107031200203041c581c0c018041742102c6859420741d44100001080d03903420100e010700311081801d600d59140b00300d040041c400011040018956441e60500e80002501030700140d110b020300000170040d035551104c220589400e04c0e03048108007164403406200b294071804400b03a010029082c0040440080c2c0d50302000c0342d00c01c450966040ba41e900060180300703000880c81540c00c03241c500070300020020781c441c5502c0302c00701c2c49014400c40d800a584107904e40103019080042d074101c207201e00e1440e6103101280c040c220003442180001d045038010210a41904402c0d03045c0d810550701d40010080701d5644000402014251074003904902925100168454001003800912644c503201e00610700003540c0f041d01c03502003030041a42d041c48804100c0d80711f80d1090303c1c01c03514010340d002c1d001c00301414100c000304207080c006904a00c4183c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 522955476 1250 522954226 522954239
    0x30f04171306020f0d23041a03070215041e14030c070e0705070b0f15040c170a0239030c030a0909090b0402040510080304060c110a0f060503100807 65
    0x2401c90841d0540d800351508207921845064540c54880100004a800d00c66003081041c000d0b682440c1c4280030710030700c5150030b40b101c01040c00c8840c1c002504219160000401981c2a1b040c009403800800788030485455007419628903201c280b5900c950bd2603a280c032914401400380100040340d0400d11041641d58540003548040e0300c0784024081c65811b000d001c1d007c07500c62403058080310f900790703001034140c551703a207800084162002000c0d141d003940150713103140041c05607680c1c401d014020b60651154644182d41d0080942c0280004014410720fa03c142720940c055101061b08403801c60002c080c3c1500703100b401c400703806208400d0240421611000c950f82440c0e4200200a12007007003107848d0142c44550b148402425103a000c0801008041000301180050501d90005a009035105920f400c0f655107480c0c102e461500030303500010010300041200000d00902440341d103803800041e00d4070081360742850755504d0318600a01c9000b080010000009021000400d00711018060311703001ea800e01c0b0754403e07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 522956726 1250 522955476 522955507
    0x80a0903021f020a0b090f01110301050f0915010e0301110406080403301a1e1203030f010b1b0a05070303030c02011a060a21050912070305030f0417 65
    0x1240184104030960080c180074254003414030215500400340101550baa0761032814019242071b07040e114a410b291030f981000e0003034a822070016031103d81c40750300d4802000700062070707100c030309000708420010301914000c0750310f030000d1040b020b09100035203299440200e8010200d480c283c502804000c500404e4540d0300c021640c0c012400707940d50145140b0840c100d040c40306040000e40244210001d144200b040d595000424120b00e540344080640f8131500100ba000016821071004030034145079148076914280303001c001428225801141980f400c500840100780040c010701c00c400502041100d000d5424054465142c3d000d0400c4e107400e006c2d58a0659655801c40c042107022905001c3c801c0c0030720307205204240c081c01c510306101e50306011150a01c0300680c1710001000030000e1407040b40c0c0000c4040210348110091801c1d002130389262a40c209400c3c4016410500c0ca81d0400300310103004240c3c02002e89030001d61202d0041140c0e1214600512003501003052000c082201068804000880350b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 522957976 1250 522956726 522956729
    0x405040f0201030c050c19032601261b0409080d050f07030b0f010f120608030c07080d090311060d0e030304020102012007030819020c0304080d09180e010603080a09 72
    0xc1c3c8040c80b1000120006407800c0c061110203000a60000550f018440f207110300082c40701d4060f08141c0c50f9004100d0503502d52003021050b8250b0b52944c400100b040c2c08040910b81c0450800d0080001280c12aa925503143ca0380b005590300326140e0b000304883c0560b0b482d886072400f281e00c4856660754005850562000c0d04c411100700303000f1116580007580050082c050300d002a5001003143c507800003010019500b2641d014000f00070007942c01103030300360b80702c0340e1090700702901c403d00040d5101d140c500c04440c50924240c12100040d003102c0b02440c0c3c1d2941001040702920740c0708081881c840540408503d4074095200000907840c00c01d40c4980380c2c0c45002c070045000d64000e038000d00810b40001e2221007222903c0d8403500e5014030422103540800e1041200940040014400c0761844404400c0401a07030058250b04a8a4100140820140c441082041682001410420011403502103002c1c80621803e5a0220450300c4bc245082c00300b80a611840c040e41d032040c042c0b526550a100000d01c045502d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 522959226 1250 522957976 522957979
    0x180918150916150f030510120f0b0a0e06010b040e0609090f030706061d101502031608090a0609061b11030d05040f121e03020f06090313052403150405040f02 69
    0x32135003416507621900030688108510f105454542d89042c0000703010b9009180e040da80624107400d8200001d41c5038080c917000c1c183d005000701c1d0451010204030b082c000103074400b01c18600100803c010381a00e481c1c00715031103003040344c45404030341e00c2140d014289080980b114280740400160501044103551021090f41c031500d017050500780130741c102c074000610305171404a9800d145034004c020924000344051803801e21441501d041400300040007032a803503080760450341c40318046000c1404e4100051300034000c086900d030101216240c42c0d00a01002030b8440200d114140360301ca000300b0302c4003116698144500180440303816064501c401811038119000b40b010b103807080700000031039422038a641802c00f038000d0b041c005528200308070010040903c8800310b041d4042c44401e14001c010a209885c825442170000e50340e40c4041741c0d1844d9041ca82600090b100d0b25401842d062402a0231428091b0300042d2803034955a80c846421241542404107005035205060604120422003000a4400d01e00d10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 522960476 1250 522959226 522959237
    0x909061409030901090311011b06060828170c030a09031b0501051c0e0a0605062115071e020f061003030c080a0905040218091815091615 60
    0x2961100151280704440701c03d80060f44c1400b00340040380d506180c200d05034505041c41c0508072400c0c0d10050070308070725007025200190303601c0081042003c14842d04160560201c1025048040407080e0101071001c100041d09410320081400001856182202e030440b190708100d030348803600d0f400010306040c00b5002c01c8403131400300e0601d03a0241c10000100d80903a9016115541400400c0d24bc1d207515022a84400ca40d82e0748940d030001d0342134014020344103018000c1c2c170b01061904e018002d2122010440b403000600310f89480a003091294040f5684030106161205050b041d299040100d50a649142c050542a00044200c039001600020120840c0c00d03070006403005a40d610284021600c964070014011940301c01c002c8000541c4400142040680da0034810420340c0c43e80301040490300722104c0100c01181c0d00048805500e0084465540b001003200b00d420500743d032028980d215001500710362180c0001da0040713454624240101010000c90380307803051000b0303581ca10b440490310000d20030201080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 522961726 1250 522960476 522960481
    0x110304050f1c02070e0a06031b1d0106050d020c0709151706060d080a03091b1706061c0201020703080c1501090b06070213021b1606170103140709090614 67
    0xb202034a15107001c500d54000e0b180103031810b201281a804000c000c0d441c1242e44030004800140c110100003a0412070786c07040e151113410810b0b075400d02c4150851100e07840030100c0040040c0c3d07510070100c5042c51881c103000341e1500103100016182100c80c1c2c200b0700c4014100410901761003400010b5034200e9190305442d0340ea103e50046015107420080d1039068001d0540e241200101c0c40340c6d402000355100d140340005007011f154645d0714481014540c900f001c60714981d801c002c18501c2d011114115039610340989002e00307140c40007405000280203008072070740c1403010940541e8001c0c04000021f58018001c10765071003004100c5a111007a40d4045500d50700c480f0000b186422040c07055105182001d810240380201903000c00072650320ba0034110b40101d0b0200b00444d8001c4c400450583c5d40c0071054010038126401922008804190360042020440c0c1d00141c0e911042d00c114000d030450750040c1d410020105084030b428101500ba8002d05001800d214000302048100d620002074000800c60102464 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 522962976 1250 522961726 522961753
    0x6020a14030108060403050c070807080c2b14010906111306020a0f031206080d0905010e1e100c080f0d0b010e01080f0a1d030c0d141c110304050f 64
    0x140003e004240c80d961001d00040c00180c0070b4002131401c010b402d0211606a590340d01458544103d940094945402c10f280003030250070068140080400c0d9168520a002c840c03010705144080c8598000d0818030b031480158580360f40a5001c01c0c0c045400550a10500e409440a001d00b503005034101c80d80306000000014116202181c201d030f010303622022a880100c600d803021075400d1003c1c1c0b041d5005994500000400311003c0102080178141078892418140c50800054440f141d00c1081e9070045603440039034101c1da203510004e12910042100e50404140d1f1803501110454510314000f000100009020b10112680707070054040d030004000d090020413103c500440d41c2d0301901e0075450205250b0300104400310b21840c00715512a411601c0010303050350480e80206030002e0b0b00303c82c1c0c81ea03410004811401c1329003072200300c1c1c5040080c101036002c9100c42c03004075903078469050361602443c240c0c0c10440f89807603da006172040300034500f18140c4034103250038201d450b08140c002119032031140c6003840400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 522964226 1250 522962976 522963017
    0xf0a050c07080c0c0d1a010b0309030f0c15010f0306060506091e012a05060109110702090403020304090906050106083405120a0b01020f1f020f070f06020a 68
    0x18919000218209400c03507a5000d42d5420410140c5828011004068480d8888600c040b11301d900505403851000c3d903041c04400710a806030400358100780c0410030424822340000c120340300f011410002990b83c03000c10403101c0c1401c0032500c111440c000c1c0b00c000061050300c0d2000070710580b4064a010400e8958a40801c07ca62040f020490380281203480c004100400b031a03070494040e4810304040c9540703e606044e002d161f91200d404204ca0302c41d8260b4030b90501000f00202c6001d007841000400c40201e11880e10b4010340607040000380300d0515000014101403080c8280c4004000c001d800740816410b614002015207400d0085100054a003400601091101a40740c190803500c00841e441c0c00400380110301e940b50700030709460107000c420011038a0300c036100c0484c80d106140c4130310002514040100028208454204000210313400317903a90242c28245509404000b045100c401039641360820490500f5009030b4001a05111400d9070b0401800034640007410103945540c0d524511105c2c10070030075007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 522965476 1250 522964226 522964231
    0x513060e041e17030711060906011e0e040c05040b06090f100c080304050c030607050708030a181a041506140d060e2a060406020d080709120b0f0a05 65
    0x203000100901060204081c4a50b8801c0108188441941c4400d1500c8129094081403000c0791030300d0001040201d8940c1c0500380042c4c1a012a000c0c051a003401000b42e640e4402c18000c000e445d0b0350303103040d80b030710361815203e0040100109040c4815503d000e0901c40e503c0703030715442400d000e542000d01048042c5043c1042301c100584c0149284103c0c80200c00384503027081d0013a40c0d60141301c1c0880c414070200782014050340c4940d200c0c400400a110f89401450f0901d0401781803101070140a10000b0002800e40c02525030101c0390300e2001505d202074402841140c81150400760040d126090300840c14162941700d0781c8101d0041c0c100f001c42c1100424071508845680c030a000804c588640142c1e52858509e94405905000e5030010502044003a0150308180d055580da1040041c0c001c6030380d600d405211703107140d46400101d810030b04080ca4520301a40300c030303070200802e0204645480003440850045a003403000e800c80088000314001d20f0728140c0c0345120140c030b080c0396901c492800159480c0260240a1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 522966726 1250 522965476 522965489
    0x30c05012a03030c111005040221030f0a170106080f090610030308041b0e01030302010b010309020d020418120207080c1c030c030507020402030a05151906050d0e0f07051306 76
    0x3500d10703aa440880051030100f070040104003024074030000c0a0010402c0c0041806281c00018487c105031041200302200050120499100012144c509120103c15034280c40442810aa43c80d00202c42c202d8568071816003501d02c2c01d203614008101e0320381c00840c95200d105800b88040d807036203a040380e0340c2d9103a8088074030b0f41c060442500d01303000180c0b00b2103140343c0151155424041404141c449000d0400c07054121116058641d8010001c0c9071f42401004400d00d000e080411450a5540219136035010903000640a40e0722490b10800820346d9440a040b59071300200a03100003080840002c1d202c0b0700b941302e001d03583e11a0b07080710540740c6401c40d8110362441d40702403658809111550140c0d0500c120070b50903000c1c084c0a00400d009602c51b030000b18400d41890300000354601c1d240310f0043e020f142d07541c5082d0040b03001d045209a90040381566005a450b035040880d1181520309500c1c0141c122110425072500480401c000c40b08030004240d4141e440c116410404e404103141c10000b120140d12440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 522967976 1250 522966726 522966797
    0xd0c0c0b060a030b0115050909040303090302070b0708040b1c0c0e03010606020f0304030b0c04170a0611090f0f040b0d111206160c02010905060a02063102040e010e0601030c0501 78
    0x4000c2c07400141c112a081c086c9904105050038561000207848034412601900800d8550010000300365041c4030240141034a000b205040c104643c6400b003140c007442c082ca420f600700004882503d6071312080388541d542c0c200c3e0300910441640c40d80007080c001660103a40d0003982040004100603001003504560500e810006604141c69611481100f060241080d514020104808902e11400405400b0b5170125140202800400ba151400c102c4060303403282d0420100c1840800e006942d20074411201800071035001d4202d003e4400002c3c02000410f050503400380e1101900402c03c0001c14454100030b104844c000d0811140d501603a840303280c1110081d108100d40d50448a40398050b01c0d114172002e0062408040032610b81001c14640c0e030003020342e480583c0c02807081101c0005800b814241c05d03198040c428102041111560045402c00d0000a10940d2184d507542000d80c400d51000d410885c110301150b000b965282000080c010080c00350383c1c000780c0710060040d0300710388510f50b004003e000013209 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 522969226 1250 522967976 522967979
    0xa0311072f030c13111207120203061c031209050f071703220e09160501030c09090207080f1207080f010e0c030a110d0b04140f0c0f0d0c0c0b060a030b01 67
    0x7000881603220b130365000d116603200800580e820901d000380c09090380300c07400d481c440d081083c0c024046205404c4100412401041001881c0d11011080600801c03160f01c022540490b40c1b4041e1610300e50f180f407501c0744910f0301550b4800c0c45800036100d0720020507070080d185c10503206c008059000204041038103036940100404001181c0032135001041c1c460f144c0d003003090503444415075101101c094075031807840d502a507401030656110480c610000c000134202002260506c40001d44802640d00c990001e003035010944200344a11141210321103524200501d50300c11001d6001c10350f02c20142c1e00480020fa00030b00240c034a4070241c06960584a000c812a01c06507a07051412200764070042500302c4030b6031504004e6040b80540c002030465405440700200d01c00565505200840d040d94503003903070740518141800b5003040e10342c5032940c21426100c1069600c2d514150340500ad403240001419109281440e0213280c6903202440442c2d081c030800756007141c0c2d02c5d420100004103405000140030148200300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 522970476 1250 522969226 522969229
    0x60b220b06120c1b0607030f0b19090b0f0a09060807060311070602070f0b152d01081b0307050301170d0e04270506011d0910020a0311072f030c 63
    0x1070110a1a0b40e00e1142500010542c51818607500340c0b61b51021a0700c40758104e00f18507081c0030f80d40c1c0f0144140d4401100ba001c0e00b0012101c010a0300c14545541e60301c180000c01910b41400c0300306040d001034840042590b9441011740245140c1c450524107001d000008590785110f401005605080140384500305841034440c1d400a50252200715035000c0104d042c0710000d004c4c614901d09c03441078000440b000c551041d09014514080303007010041e4516018141c1d00e50340180241c00c054103801e20300460035544600c9071030803081e010941500105000b03c00c103c40e503984140114180c602c900070300c82c0d1900925403642d43d500714410f18040803540d8107a85c10725900749640840300702c07060311020420a4008190483c0105800c22082e04d03150811401032040c01080700c440b050941140140c440c69103891801161034211002c4445241038000946c0c0c2c104611030703007225001204442c1c1c0f46075542d041e450864440301341c0800503140d4080c1301e144a201e00120800d0b179040c00c03801030040c00c00d03c46050b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 522971726 1250 522970476 522970501
    0x40b07032a02011223010602060106020a031b02062704060b0708030703110409090f060509070f0b090414010e04110f030c0607140a08070303051f060c060b220b0612 72
    0x39108810554500701021500380c10125021100b4000007805c00650400c0380080c200141600308400399030000b550107000a03030220424030324500607040035440000c107100003001c40c0b1442d00f5490204181100390a4810032001440d1107211048804000855a030501904039005800e00544025018800141450302982003910500c0464003150710389600e60510f101182c0350038405685141d00b04c01e910f400c211213880340f103401201420041070194a0304900c940906001e026405e000a00812407500c5522280c01500303121180c94a808515a101e440c412202007044a05071140341c0000384800700380c20315007018404107201030f020f0200b8030015030603c42560701c444022034121080c801820103c14041c880d1682140c401c00e00c403a541c01c100e040040a50b000988907e903030100c00201d107030f00060940c420004440140c200300010340b1803801d0540c001c2c0070241d20140c101b08080f01c1000c00800d4580103408000034030404001c041200418408240101004003035080460004200c4110100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 522972976 1250 522971726 522971747
    0xd06021308010e070e0a02030103050d0c080c0102042d06080c0a020a02030d05091504050319030c201302040b0d091b030b010302150307020d030e0c06040b07032a0201 73
    0x8140054056a160320305802c50f407141c1070301c19141d004240c00348802c00d415084e044c2c0200b5409410341c1903504540b2180c1c2c480800d00410b0b810700c180044144100807007801940c1155040030001c41d1926510880d0004527100c1454039050030b15030b54410b1045d051108090b5080d1b516a40d2030108681d6152140c0c9035550001c05880152b120f041006001a501001145039404169996603120720b60402070120410b50480ca1705000d0401348000d03c001c0c0c4000500e0300c400c403070100c07040c4e594003c00c0c1070654890740c0c40d64014101c0810720784104031fa0018426840300000c019031b891000d0310380c0d2014401c100d00440c021440703120820021000d1000050304814060b40c0280c00d440120042c0144010100d41d081d8421580c501d0454010410740c5404011134803c038010b0441e252561030410402900c6800300d0103400c085c1680c40e144d1240e0960204a00700c00b44101801469443c0d44541c01040c0517044134000720300141c00d101c1c0e1140c007210842e1031102002c50082d55410034050a600544920011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 522974226 1250 522972976 522972997
    0xf21200703021509091e130f02041806050703090506060604031e0813080c0a0b07030e19090e1b0103060503151509010303120b032406060409050c13140d0602 69
    0x3406041d009586084c141c80c0900d0345807040300e00502501e0361068400c0c1e4010701c800c40c140035800e14031f0042210003004041d460307030484000840c600241c50204040f910802c1c083d1a1038903140400020a03016400702110b240100225040d55070740d0810030907113110303070700000340036200f00183ea0803040124684242c5041c070540e011414141c0f00c90703801044841c6130b440220113034403220b1030038801d05210810b47d001d000b981e100c840c41c002c6541c81c081c0c110401081c1e0240210300c404d0a11005802040b50080507101c44001400b40c0c40f0900f03800303503443c54200304581e40743d0711110f40ba500941c0a8460b080458801801030140102c600308a046d02e032038001e04d003841e03e01e03008900f0342442c0e64101030540a18441e448002490304641500c004031140100c1450003544041c40944c120900095000c1112101900c2c1c2030720380d03542101146060043d0344c4500480c50402c020b000032001741d02c0c05004504007024911504e1aa01c601c4000195022200280c000400303034211400309009400601c5200e85 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 522975476 1250 522974226 522974269
    0x130506150306040f290a0b04140d140a2906010f090e1e070801180207050109020307170d0f1d0423190e0304120f2120070302 55
    0x43c24504405035600e40304144002d0007500417210b010300e42c2c0f50125682da0300554501d226213040445400a034480c034061070079103c01411a0301c0c200e603034114030303441303415841342a410700010283c00c0c0300c2d079500160100f02c80c3c0040903944820300d0100b440005902c07403540000c1400ca521384400542c8c1d9460182c0641c0d04018400d20041505410101481e0040f4204185c1109050102d172070f07502007041c046d01c601c0070040801c00400c881000c2c0c42c00381031402502c0600503601c0070b032894600d0060100d1a002500350041941c00101c01d08802c03480080500f0b510700f5901d04108862046036081c0200c1c001e0303030209110314200302805c1041c040f0b41c03c84510103000080c030080305140600721b10340d11700080e051620b60a02000b0765041c61417211558a09003160910059800b40360782c54a81c000d9005101e8000080d03041c03141031203d02e2030401050b1345c00040c8040f090807000c050340c00170840b82e91880041024180d0a4060104c40d0801b4002d81c407004000d001c216056a003000580034203030100040526 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 522976726 1250 522975476 522975491
    0xe0a0b0a1206060804020f18011509031a1e010303170a06030602030a05100f080604080304110a030501020a0e0f090411010509041503021e150a12091113050615030604 73
    0x81d601c034480180c507240e120145285044d10400c00c0e52984000303520301911852810500c40c2d040e1112140c1560361105108490204040c011202c4400e1a880034104080030782e0b0142484403a400c10b18001d5480a03602c552118520079031144501084c40010300003070012080305407881010803c0ca421045250780030940981c0e80d01e6000581e081910604007160b918810b01c0f0080e00c2c03548203030f0002c0c0324003450214101e18220180362507800082c030203031092000000060401c02f801e481c60302c403038500800750398005469007403041c002d401004407500850080202c00c800392400c480000e1400c00002c7c0201c205030740e40d54522505000c0b00c138038a41400028402d00d002d682c3e41d070060b603519990a01d42082000d2560040022422040d2100b008005009000070810381b5503290742c9907000030250b54641d0316440807500b100c001400c101588185460601080308110054440e23411a11045804201e01e806905411040320001d0741c135698000132808550110f4501c80c40559480781c0f00410009842 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 522977976 1250 522976726 522976757
    0xa020405010306050a0e070807260d09030507231011031c0b06040b030402011b020d03050a230d0b01050706090b04021002030a080601030b030c040e03190e0a0b0a 71
    0xd88082e08202c4501c0d85031803c0195501c07983c4189105604501d00070710605142c00d844907120300b000d0154031409200c20340010000c1900041c5401c054006030100c4070328421202d40145400f88502048980d8011004002041c601c8004411441d14440c0034614207001090200300409251011100c2400300c0480b0f03405202c5810f0010341807201c50352280711007518040e4842d0080711801200b030313489441c3c00e020a014112041003666030269080c20b02240090745a100a088243e04440082d030103c04461480c0070580d100014050b04c0c040e940742c1851140c02030301c42c8504440500b00400041105210881031244c140d000074407899070605203507150001c44e48910094459001040c0e0308080c100c1305000442c00e0541c0d0840c0c20800302c0c8091424070225240c001c2007085c020b0b1607141015120304c20502d1903a814030410303402540041c41000405101d001e0785483e9000303007000800e48004517040040707550040340c1801030504020300b2100500d0074030743d281905821641c8520b08210315a0807a0516 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 522979226 1250 522977976 522977981
    0x702150a18060f030b0108190e0703051009032c060d0237050708031303050904021303060b060412141213080c01090e16031506030902030c120d0804050a0204 69
    0x74140c41d0b03842e1444900b072490050185d07004107019a041044c541c0c20440452100100c3d003010044a4402046c85d4446495444c90641c150300080c0c25801140421142071103154010b41c0d0982c440e4403040200c203640000f5045000911000800c01001e040040b1780c0c4d842e18100821081101c0c400050400300b4540748000c806d0390504228903601d9000200c00c0000c444840b02084040c582c0c507082e89414403640d070790070003400b01a0a41d60120a02e0148a0800d8098815100d2021000c5d0045481d040000d01c00380d040245c07071000343d40341450044001c4546c1007400884040e250300341c032510400b00e000d0b81c60952070201e250304625980112010740e0020749040e001031031000c404006400c400c41c00c04031624142204800c001b81404482042048006040300001e0b6114414040c2d4010301d12011800350042c01000c803501c0b003200e030340e180701003815034069010180e003600a80880f105040c07040142702c85000741080c102c2c45503000440c090316913885a0051a03101c2d00c1030003560309261140d80403406 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 522980476 1250 522979226 522979229
    0x250509090a0f1e06380d05040b040209010501030c052a070305060a050c070c0b07031206080d020601092a17070f1e080a0b011106040b1603020702150a18 67
    0x220090030343c0e00e000c60900301d00032000604892440341c0c1ca4800c00c1e010341c0d4602d0001c41d03071901940c1d41080384110b943c1d203160300745c0c0d200340d0350300c2e80904c039a10701450b04c1f480d402c0c01213804904c00d064550022900d544248503011075600603440b40351500d030b4250104211005802d80c0e0f0110900807145580d4400b00500c08507001398400c0d001803009042501c0b0301d1081d01c00c004d01e014000201400780c100404e807003814200803035000001c0540c0d101014141124001e00703c000c0c0480090800c84d0010b812880010071802e680d059900b41c0300c0690301c841c0d0070825641d448144a4488030b00e00429080c83c000b61010310b01c0c0401034240090701c201594002500f28408a41c120040782e00c41348290b0031641c101c51304511801d000d840d0401e01864944001e88108005080030348a2035441c00000c103640d001d5403c03c4842c092840454455140c00d18084100078411030b500111403541d2074660781c0c0d460081c020381e08440d60003041201100c844605020143e0401d880010402c06241b80300d600070160b8900103030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 522981726 1250 522980476 522980501
    0x4060c080906072103050705040303140903010614010e03030708040e0907170304031106030402011d0d080403050304063005071416051e060a020c0a1703250509090a0f 73
    0x10f8004e861484c2c00800c0340402e03580c1303405040c00c00040082203a1b004084400352581800e1851122100c113246000600854600980540c6040710100e070340392120701682c40c48282661200881c8c4203000070705849000301d1500a140314018070090081e0740821807030551221300201102e440c1956120f280c4441c68052118405070f400010301401444030400b20100b503104151180c17032642c00d00303a00003400305034072640c05072890076002c1c022110750380c450344003800041d0070075034454441d42c40341426a120780c45481000301064100c201414a41d1380f040180640e1440300e030401035528000044800a0900240420b040041810040c0d10316030300d0401500211f9401084d000c1809034030b1405e01d14200480d800c01140740d01a848a141c80e04c00000c81980c044424480580c803440200c2c2068506600010003c00090705103000500046551300914070454500c028071041d038815450070241014024035040001c1c0080140d01503d04000d49019001030007100300050301d00c224a200c41c111106020800c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 522982976 1250 522981726 522981743
    0x607120c0803010b0c10061d091213180603080706180206030112110105030c0904110405090906090712151505060d0606020c030c09070809070e07090303020d0201050c04060c08090607 80
    0x1700051042185001ca2030101c034082040a080121005070707031200141c000c0f2401c2600300050200e0009000403a03210740c8080d1020707180c40300b0032004003404809025000038a03100c010191030020b42c50280800320380d0403e42c06031a1251540f180d0003c0d0940300301100c0010b40804150006885038801503008180c0c40b02c80e40310705038280c58200d10b83d0500e02000c60403c24140140140c0341800310481d1b00d81d040c11039001410a030b404004c1101c40c081c2e0390105d40c0c41120003040100511001c40c84a120b001120142c036101034451044000c0304c0516040503007a1111451110707072207010382d40130203003000c2940c0018030405c0d600c50018370160b05c154280d0032640c0d1140030810005070100708800206208501400d880041800481c0109200800660412101e00007048814000b0f0103000701a000d142e451408624210502400307a60b402c0c0700840043c400c0b5040030381080e1062080e10b010b00c4190740451301d0140303003e800b04d41c005c0c0381007404d031035038142084500c1903591444014081d0500c103400b1f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 522984226 1250 522982976 522982987
    0x506091e071b080414030c06180a0b0304080304140d02030706020f1c0b0f01031404020d080f04080a021f020706050d0204050315010e010b0406170a1d1e010b0607120c0803010b 77
    0x145d80c4d01e01c506980146c041d90000540400703d1b5200700550303c0380b007180c0f00c14401d81306039038000a07101d900e59480103219950010a010a1050301c0c070095100e60700444034003999010702d030461750340c9113000060351005030024001c24001070060b0b0000c1400071941c0c01d199082c41001c42426100e148034082c1912110356a100f00da11038182060b119100c80c809003020001c404d52441141340301d00c00184000e2080d039004050a04200c03208041c2c8400810044c03e0710b4841e5200c01100d40e5030f1000040581c0320b860300300c0c401d03071a094019104a4800308242c1c060440c0c5031400d081943d81d60400a500b44c0034640074080890b01c0d0710f040100b00721680003034291070701d80d515140c02c40c0411001a0821441035200b08418032416030450350031200b940d50f05d41e940e211035490101c00301c02060080490044d59101e40200540d4001c000340c440200c0b14080f04190040000941a80c22115900c40154100c1400d11442c0042410100c0300003121b011030030041c42c9851140d9440c030566009070800440141c02103607 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 522985476 1250 522984226 522984239
    0xd030b0a0503032703031315090f090c090506070f0201111f1a01090503030f0304020a0b030708090606060405010903020f0303071e140304030c0b18040c030e010506091e071b0804 78
    0x1050390031080580c00b551070001f5a08000b00b407152203003d507221040032940360403160303440b6071501070080c08006003000368152a0b20346400a00042013101c0300245210070040741c14238000088070300346640b1201c2c040c000351141c0c5c0155590440050003135914050050440304000b141622100c1051410f10001441040310350207070b032244c8031480513030304100c240c7c00140300c2524000226903046404982541e140c0c0e031a4030003c1c102410030b03044264400c5000c42400411030300b020788940130700c0e46003090b82c0aa544e04018001240281d100d142d00050480a0410160812620707540035050301400380d900e407a00039201e00c00c4004400c1d9440f0345101201e020402800ba051280140071071031500550724051550300d400f880b001090140c086080c10010780700206240103160000c0e0b800001e80140071200314054041c008082a403041c05a55007408001403044c9011010307540b18041120740e00924080041c1c8079005007900501b02c2003803000c60079211a0090600c030203500018803950b000b5139101d06108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 522986726 1250 522985476 522985537
    0xc020a03031406091b07020406060e0f0409021f0c0b07020a0201090f08150c07020301060801021312020303030a09020d06060e190c08150a030f06050a0b060c0d030b0a050303 76
    0x2c5507034007442c01c0384103100309580c86502c0e00d5004085000d0f58002c00c0300c802c0300c80d2854800c3c4803009500510380304c400522990040444a00764000f164200326500f0048144810b0750b500040c000e5000c0501c50303286401104c907801400c07191038107280c044909155583d803041d034610107859550150b8405c6080d4411503034411792403030207015040075810400e443c03c40035580d00d540481c1d4055036003400c140055a1a0200c0b01034a00464008000b40f00e1650b030741514038001e500c03200e28611482c04e54080850440325030301580346483c0d4050010f61941d81d4000004009001c4c601089078001881c0300c1081c0802c0190044d0400342c8441c41210b10181407c000c0d01c403110101500c01c0100600f00780424051f02d40003200e0036842807816201c02c82c0038018000180010710140c0000701041081e013641400d001d0180c4c00640304524217402048006006c800300b0106005002909500c0d500c21840040d0a501c01c5c0c1051035110790203014046200d40f00d10002e815074009846103001d196051040c1c403041d00904 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 522987976 1250 522986726 522986741
    0x50105031212131415240105040b07081c06080105070f17180304092f03010603091a0403050711090601050406180f0305071e0f050904060f0c020a0303 66
    0x2256800e02e4992003102da8110361000411640112142c01500d0301844080d44801501c4054002a00ca80420060b414840c48805a482e95a080100b2224000c00520007188045040c016141c0604181c40c00601d040e0310750100c44215000e00c800d04c404c1c2010140c1d000311001c0c00245940c0030079003505007007a180c21138600604403070402503101c171960310303654201c40c2481d4000f82d00c1141c0c1109680f1469030f1004070344212413008e0366210002d400110340342e550b030007800342c02d201103170806080c00c03441040f424181d001c0c815244206000c000401100d40a0750292207001c0c890030600c4103407105141102d290b500200c0e0709030040741c000500d0008000e41029101008001116801c1860038400c0000f811405140600d0f0144969551030301c150a2820805800618445847c450115201d00c0c0803900c07802544a802070071004101401d6244a10403801c0068820070485c5c560414a4402000540030014005171046561b80c0d140461802c880c1c00385640354991900107104a0340e0603d0b008045070101c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 522989226 1250 522987976 522988003
    0x2040c02060a0b0f0f060a0c1509210f0809120a09050418080a0e0d06051608010806091b040e0106031103070e010305191a0403030c03060503010219030510170105010503 74
    0x7400c01d01c80c00da80d0055110f11700d1100351001601c540d01c00c5403e40314a086040d019047d05599058800c40f10b0310740d00a9000d0b1031180c895a04a210690140c002c0c1c51150b024110109444d61b912400140c80f0b02917441c0d100d07081c442141e240a81a541102c2168010030701d013400100c01c08414013a5017410b01840c10302c05100443d41c040210f840d21114421300078184a40d04114480254240700e640f007503840441d842d0840000c00c420b080200d200e4455210961081c2e001c11284000000c0803000498003510401c584c10217005001d014512030035040c040002a50b43c410395542c400c01102000b445002c1c0910301c107141c1000b00710130b00c004140c901542130b1700c540b440511100040c0009640420401100c0000e60036011541411b841e001400c948584800000070420300100414035a060b003100007401c0705914200b003102d844030185800e0340300e2203100340d50b0500d00030450030b400c42c030030390140c0c0e0f00140c00b5a14052181e140c08001740d8a40d900d100408450391140010301030341c40c1c1400b000440e840f4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 522990476 1250 522989226 522989239
    0x3040614090312040b070926010b121908070b0a0903120e100f0b090f040c05010c12080703021b10060602030a1202131502010c0206060906060d0b030a02040c02060a0b 73
    0x1c24003c460100440240000c19181090020514050103030040320007410083c908410388038151044400000404400c44400b5070800100d0f00b1141002c24054201b0010b9401502c2c0710001e0004074140b20a40d107000711110b031402c112020203d0042141140100030407034000c40c9410140c20003c22084400000402e258502100c44c902618001155079511001c503901050340f2513a844190001d01c0071000b2250016a1441007004001e9110f0207113104078810695480f01c19103c000468415043c40f5009080b12410880c1e428400e0040f5011035204201c0e10f0054034040081c0100912540d00041e048440d81c041c00f051a907807280b0340900406400c81e0302c025410000309200003030802d0155107404404650010319000905803c0e429400580603d4903010160780032500020f0007401403400d0720006005400c0400d05610704001c8080c0034aa00400381824400c0341020034008000100b001503040c800c54803004010b0b1264041c01010324000d030060f01840c5800610301d070a464803c284a4031461 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 522991726 1250 522990476 522990487
    0x9040b07090e16030906020f12010303080c0415050309160f08061509010b0f070f14010c0c08032d07030c081506040603020711040603051b0409020a050d1502030406140903 75
    0x110031441c1101d03550134900131500b4002d508000000748a0b8400707044a1540015440b024002a0752009040ba4805d41c2c4400044d034a00c894020740b4043c0c1d009440d00340a00c540c11030308140c4074101441d08800a00152013045884011a1024241035880308603d41e401c01e2040005000600549a020860240710b0f505400d00704000745820005000c4c3c001c03c0a00495460120b900090070b0382c11541d4000001d00c5840010300340f84a041407551c1490400c0d40c00c0900940706a4030a0340100300c282e40c01085c4504649032820094900580e00c8a500c011802e854806c042c000000240c50740100c809440000b140c5244440061007000c00424444c0c412014042c050000d44034081120304071082442c005072180640d181c0250001c0c01581d443d80e201e4206072000c0244040428002003106445002010303124500c1c00744410307591078903006903005402c0401000b4a04041c3d2034807110f28412004a480c00308003503980c1c1c0c126007007a10181d80303081e582c002e01120300c40c101001301c1c1c000552500450500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 522992976 1250 522991726 522991741
    0x6020d29091303300203100909020d02061c020708090a0e09120a09081c0906020d081314030703030e060f0103050a030e031f0f11030105030a03050f0909040b07090e 72
    0x4110a1030010108440d2000440d1900304a1644900900b102840302989090001218010750016200141c0e0105000d0000990400c940300703c050066001e071800400140701d40811030550030403071070040b00803284c0e00030ba880340441c0c3c401409200e01c02c0c0b511e103450300548400c1c02407501c50307030b0403d0900d2000f142c24030016a030b00040d0368409400300714842d95503004208040743c4d40c00040e84a0800362044580c2c804803508030245c4441c4400c030503075400c50200c0d52100d0880c1c1d607003240008031000c07881e200082844c15510480c0c14201c240503000b41e900110000d0f049500d164070040040c0c0001e0354401c1040f128840074040190070007180e2125007034650440d21001c5d00c40d204140000d00303000b03003204c1c500c52546013844803540d200c0c860858100450782824408000d401080070020165103400d0b141c1c4440c2c403c1e58140e9041e5000031300140089622a58280c841da4441080440e03828024027907080260384e400c05142c8100d100b5002c001081c24000809041c0001a80003515402c41c030104110303a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 522994226 1250 522992976 522993001
    0x1c0212010f03051e030415020d080a06060c110a052121090910170102041707080304050111190f050c1005090d0f060e061b0a09030f06020d2909 63
    0x401201c13540c1c181c0c05400843d006882d600c01da911140400c1d081070108040786802040b00c0d03401d9025910340700348641d282c14540045825038000c01c00400e00010180021842490010040040260a641006880703034001003003000e2051100c0c0c03840818200d1000c2c80e00b418805007040c1c40848041060300c00c1240d28040c5a03019400c080c80c000d000380380c001a440504152450010314230803088503014028090018080d510501800d00409011404050304020008044040b2a00113000d1401c050418004540741d1300c00d0040f0303100f64840c1e40526201120324041102a0a22400c1c1c1c0c10811059072800c42e081540009000c2e1040101070352200c040c41e0000e0456901d404c0c03c035484419100f26207083d0701120290880604120301c0c000500a900c0340002c1d81ca40102c442c0703011850342000c004400e08032807003502202c000007020b50303000300001209500c049540c3ca22440c409070801c10140f1601040300e40ca00b00601c80050443c0d00412108200ca4840184440070750701d26010346441840c1421 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 522995476 1250 522994226 522994243
    0x1c0801060207230901030503090406080c1003090819020d080609070c080c0a1a04051507020706031107081309051509061201020f03071d120619021c0212010f0305 71
    0x32503403003100c1c3c140d03841140f031504008000341282110351310780c142583d90f80c01620941c0c0c00780386405004204d503500028000c0d0080e100400c101d0307003000154021005841010000c40700c20900f40b01007048010704c0411000f20341c01c40d034002c1060884915000b045e0104c0078010901800300c1038180714075182c0c010612071034281c01040c2c0720390b1003100c0403149140c51004170000e8440d00890241c0404801507a0100f80154014022900041100718000c9503c0d0000e540c000c1c0540e012030001c111442c002d030008500b40306208070040c1491400d0b1141451a070205010100004817a4030038051400700e84a5603030400403101c5050402c03500c0ad4040341001c9400380a0922581403901d200510042c00d4040f169a5502101747c0b58490130710509c041d0135004400d04088888145160445840c03d224a107001f102500a0007007500e80c41d44d40e42c1000d0032000c13071001c80d05950200a624240c0b14401030b030b95401c4201100042c4e480c14540400d90b0b42000c181c110ba00504128030003000412400142e524 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 522996726 1250 522995476 522995489
    0xa020a09050c0d090c150c1203020903102c1606020303060a030303051504110705060c031306090c05211903081f0e0106030515101409040f020c1c0801060207 69
    0x24244e00b25040244042c140d40d03100441c0050020581542540c4c801a03880000e481100c00700c44c1d0244620064007a80650400150194031070703a0444441040754020440301428103800504280380043c6450400d200310202000541c0264481d0000400101003000141002d1000d10300354203103100040d0303200e08144005810143c452012032517003684401c070400e0800006208100d03a910a034440b01a51700401710648490180f000001c0300c100182044911801a044050125110780d54900303004010006c01500c60740001e1002164030f46481e403280c18003010542031850321242c02805140781c40441151f1001c4602c0d40c0100314002038111400700e411222003036208003560000b0300101103000b0243c0c0200d200703220500000607000c1e05039100c00d000343e65040d040104c3c0e02c1400d0034441c1140c0b01400b0400000d6000358a00340f48a40a40580201d034001403000c202d0504801c03290300ae03070b00810304148030340d00044032a1074100030000148404011a0a00c414150305d452406502c804142c402c55 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 522997976 1250 522996726 522996731
    0xa03081603031d0c0a0902030708220516090e0a02030304060509011818050a05040510111623071d04060b10080a1d030d090c170a020a09050c0d 63
    0xc0d800c060207a00000d105141c152030b0b4040002030b0041407540c8005070303a6400c1c000c541034000415580c405008407071048420303440340a01038403040d544522113407561108803c107003420042600004c4040c001c0e01c0351019505600440181032045440440f1220714044809074401c11464006031408010b483c2229070b141446525295582c0c016100d462003281100341001c0d5000300032580c20201240f441380160150340030801551241c2e203030b904030b46064038040c02e150310514103880058071940203000c070481d0402c6620b04041f10203090080d41c41302450101c6105003820350800d04482c0c030b0946458040880300c0102200c600e8039111041410000004000c07101d8110001000e01529030441003000c0d9020f400c18030300104e407070401858070030b09941048c0d810741090307810030aa40c4801030010a803054040503600d03216656404000030080404210745919642c4400140380202000e001c40c0424844d01401240d0603520400c0280101c1e5004101308900d4402406948405001031f59200104035000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 522999226 1250 522997976 522998017
    0xf0a0c0c23070503070314280b07030b0a0e06120c0604030b0c0702130e061f060e1309030903150504030c0308040c0312030606030e15040b0a0204180b0f0a0308 70
    0x9500740000b58004a80620901c1800401c210510112980d0a0150000d03a03a8890060005a511441d094424448031521150791000b05042005e19500051103083c000794030f6003110007241c1c0512083c2c0c4050000880d032010414942881d486001380d0002c2d4101400708200c103e07000584030f005d103010290001301e6040028115014503c01c881314030b0380040004402803075503003902c4081e03c110038104034a40210000304000515614550098010780b1441c140c0c0c803810900d080710b1004691103007070307030000803442d662103960b16038455168890701940d036015801d0306500300101d8141142444a044070b2801c4200f10200740c4c0f008070350001641c1072509103d6070300c850a0124038807100340c001030014982203182c46056501540607000b141c00580b014003a401d0303001030702c0e0344a6101150450f0f02211400c00200010101d00d003040d031100d4050f80050506440340d10205100c0351040407056980e554a01341d081078501803140001c2060101d40c0c4081046c21951290424021100e181d030462200622 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 523000476 1250 522999226 522999293
    0x8130501020c01020711600301060207060507080409051e0a05061315060e0114030103030e0f0f101209020316050a17030702010e0411030f0a0c0c 64
    0x1111280b010b054020341d2954101c1c1804902070600d542c0d000d20a8a60140340640b05070506c158484491103103111245400300005241c80b0b40d810440300417018001d600e1601c100c0c09100c5007042d44482c1d001c1e1840c1c1c0341d6041c1040640f03400b04a806c00000d10a0500008000030440340c22142a1070a8403004141074545001c0c841034520345241000042410320108814000c06900c502e1280c4012180300d403004152980d540e0880d910b10f0301d0121181030201d405c0c001070340502c1b0715420503081858168900700b008050700030310f41c100b0380044001070a1242c040032145001145501c0c1090102c6000c0c07210801180041e006180d824a0710060060301005501610b0059010ba24810303006005c0c3c858040d540d4241c180090024020b9510035003941a002c12200c16418059402845510003140f5003007940d0015900b40311059000c0c2d81c096151941c1100202c4070b42c0c0503502900107801441d11074109280004207454903031042c40100031143d401000450300f0380f02c01100c40b0780d090119001080d000742 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 523001726 1250 523000476 523000481
    0x3040308371404050c0306011406040e130507182009131b09170a05071404061d0702010b0613030209060406210c0905060a05060309010e070b090909010501030308130501 74
    0x61501c00442c1c0032001c1200740030300403482a000c40e000300e042d1507490b82c0720711801d00440f10319501550010300034042400746219810340950004806e05100c42c1400b0583d95080c900806900142030102008a600b00c4154960283c0f001c0007468400e0846200c100c416280c659008410446200b50a800460400901c483e884820f10750081d00a048015002c490040c00304a114030561040501211002442007030104900a026620030b018007882860311740781441d000311041515620503681e048c001080c0384a001665440404000c0020003460300040c041c1c00c4070310000c2c42a000d41c0c0300300510001c5c0980c081d05e00d030070749604882c4c7c0300e116103920011400404441c0c215040d084039000121071244115194048036a10807400112000d89030500541560403d0340e01a4201c002000280700c9403406001459010388a0800020100709138082c0c1c1e031504445074030015a6403400900e50038a4103110700c0d01c980c0721310094020301c140d514640d001403003400020403000140d01700075043e004100c402e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 523002976 1250 523001726 523001741
    0x20f1216061a2814032e090f020108070f080a1e020a02010209090a0b0609060d09050d09060315081c1e08011502060915061908030304030837 62
    0x2400941102c0c90001540300850003a028141100800301800a111300041e03058985200340a80a08103104003402d04045045113000b194459440c0d448000d00060010703c54111028010344400c81818010700014201e480c8c0600722504100609054030b01e215040401e103600703d089010001400d03036058408100500305840c1142c0544c4c000264901e20701d034150054030403200111000301ca030351a43c01e1010300311180d411055030054014450700e4042c0c0b4100c4c001e030000d030070b00d1032020416000c190346050510480c40070410105804080900115900d4469034000602d1681844d41c0d0b1400d0140342c9a54541d81000c00c0b0b000e404802411840c1441002c88840d0b0131a10b0b030520902d44150000034180c00b40034000d850702c03a5100607101107074900c000780702406503090601514009448100b21103100500030500c58004403803504010400244070052002400d002c0055612800e00f40f400a10950015040c072807414902e00302c81d051401c0410038100001d22401d00d0044581d242c601100c05403000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 523004226 1250 523002976 523002979
    0x1f030209011502011d190f020405040c0314030c0c0d030504180507120212040f0c0b0d020c0601060e0603072f0a05060106020718020306030a02030d020f1216061a 71
    0x140c0e000015403010041c0d09600c201ca6a400911884080b044559080c40e10000c2c0d0f10070b135501065051004100c00c032034640409024001c003800a103800c3d00070070241c580c20f8804032000e0b041030108200788a00005c0c001c00300b80248001e103260103441910301d42c1d90500e2000d054416002c4002800405000340c0440303008049107548021220056000c680041c44201c40c10f001080d200d4008407214000ca1080301c203a0302680c0101103940e212500d4030603113041c2c00a4110f0f200d0b522750303034045540f942d803a024002d034040081026035070300c00c00c4182030f003040010780c01075051040310085003150342d683c0d1040c0c991189240c50490b01003494010307080242910303c07003003494600031403070030303002c03050b00800d400016174046e000302c90381d03030341d80783c00803696070550307100b00080d00c0c1d071249400008c2030558000b141c1181c4000c4c1180c8100031f85400203030420490303040ca0350150b0f10140d495542458248000b0003083ca07201501c604001100000303c2550b900740000410003035031500084842010030500c4640c8410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 523005476 1250 523004226 523004239
    0x604140310051e0610050d020904060e1f0e0106050a0807050702040606050316081006030b22060821091315030803090111040302180c041d0a0f020901081f0302 70
    0x40c0140c983c0c0c0200100b1a5450541d002000081c28070300b0011070b0010f07152825a0380361b10b80f101810f528030080d00300d01c00c42503001e40c03220030024401d0405140c03980134607080f0401d0561580c1c40c004900404200c1e9119031040800040104883d60304801510030205070350918280071340e02d0380011100c85c1704143c07000303512525040010038101d6010001d0340c410b01c04034080e49801c0c400e83c4c80c207445100c022664a030141704c0d1032034140400c42c0301e504080c550401c0a40074517400540106400c01803450494070100165550608000a0b9020003000d485c00c40ea020b4100e103550705142d090007503445008105400b9200704881098007034500c1d440444a442da8451035030b10640c403480e0080040d801034520000c19801c1c2090451070410030400c8408036680184900c511440580b442c1c0c1c00204c0080082c03060090a000c006a0000400b061149041c0c904688613054580314100c2c804a440040c07a2070f59092060241d04040d0f41c001304590380126605030200d00b09594071102c45407030b06150b00300a400c100f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 523006726 1250 523005476 523005481
    0x21b180c07051606140c0a030e130f091214040302011d0607050d0225090f02090303040f0914010b0711150708041502030c06151c050c040f0b060414031005 68
    0x70030007242080d1000c555402c001c01e1408040015107008013980001e150300910705010001703006102d41c01276848007400010014200352000401c0b43c03e000c12441c040354071740c1d1844003041a03921580c030350f0b040241054501c200b0700e107019604038011070000034103011341d50078a12030890903400b5440001c00c00500c05a034030352051030300603110101c0c01205400340c81041d207044149000c14401c5841c0c0280d4150b4600042d2411a200001d440b20443c2a603006500b0858902070740c41c02d1004002805a10b01c0740410185030001c010f085900c1d0041420000d000900140700c00005202103c00e100d410600e8041000b00c13200008514844007810280303440c0b0b0018014080040d00c9014100326814400b0310314001d1024070301a604c900ca100c009d801070750041d20018030907000113803061000c01c4001d0322452392150b440f40714001030951b510b0f0550b5283d01031443d000e21850300e8047c14025940080c41400781900700004130300745010384e0041e12250800140c0201da1501c04201400c40040da0900c180042e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 523007976 1250 523006726 523006753
    0xe070b070f0b04061a0603070f031505030a0c1701050727091a040e0307030503040f0f170315040c02071203020102071703040b0c0712080403020c0a0602010606021b180c0705 76
    0x41c1055003801109080d441c900700551b142490590344200e40c141c48650340201e24000440042054180614050031626001708170760b00c0402c07442c00302c588102c50714280305041c840741c0c0b4015000d801540450341c0c1043d0400c0000344e40005107580e5070446049005503100c0250302c1d0307099400d150300800c2c04140307010381400354020140500c13242c115041c0c0301088103800b05045540c5030f01c8ac2c0780340a0b010402c03c00103d00001c110b0300c100f218490080c0102c100c40c2c1900d075541c000004c80522310072084000070091040b881000d50050300c641c0011501040344103101140607440c0c580b584100d160840817000c40d4010315000303404840c405584a80214810380d41a02c203202ca40d04284c5055409416000001d50043c8604081310b54107500460240b481c0980010700303c0d842400140205e046024540131920320307890355021500508800c1c0c001140341401c1480081c0381240b001c0c1500148420645054255102e0f011044c0b0b01000300c0950b42c19a9840307090542403403148000040c03452043c110135850f035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 523009226 1250 523007976 523007981
    0x12050c030a240b031306050108010203040606060f02060a0c0908060a0e07051c02040506060f12040615050607060c05090a032604150c030e06161103010e070b070f0b0406 74
    0x401c0d1018040000450101c04207000c1044004005514928004140100a4a480a583c0c846104405101c20307800076035440c82038800030703072014680342c0d00481407004015690007054050308292400f16001a147d443c002d540d5a009010200203603543c1e601c0f410940e12480440340988070047c1252143d007405c610040003865250f8400e0400d02608101045600d480c2d404114207415001c40080c504000d9003c110003400007410059102601700001c000d281d0707050001c0c03d0460040c005c051840d10705030410a0544d11009945030108481400c240016986c00f070503102c800c0d07000b80c40040d60391006841a1030701c0c4607140300558440d041c880d0010402c1400400c0e0595203405954003c41440350305503030f074a50f004a0040c0000080c0340740140740030902c11440d1140303050107450300aa05c29200d07004166154003039200c882e00070300c1824450341446201c203901a800704040d17008200302100c4009158850005000380c01034005c0016185042c00b55942d4400d00103500000e40290905151822000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 523010476 1250 523009226 523009231
    0x31f050c1615271505070906030c0504180e0606031218180c0a020f0606010509060304050717010603020103050f2203020c04050106030506040b030a020f130603050d030e1005070212030712050c03 85
    0x100000551034100c40500c060089034010305050304c0d944849808c240003038020380300590071001048000d00c030004008000316507050502034070030301c00950114120030141c2044c00c020b00c140d019901c2429941c4007611900200c400311040b01d03032100140f08018000400034526044500c40044180c01030201450300c443c01014420000c4d0210744e40e81e00480e01103030722010102c4145010640500c0b6411550800340000c66000c1d10442c156520710340c5606465010301d05400505100360b649040500855030103200c0d05403c11014a600b002c603260007905420301a00791000b49000f000388001d03403004c1500800400418144c024000c0c0701c15038442000400030b080840d5210710907410580c0d03096040c200442c03801107094028040b806a651100248080d800000c6c05989005c0d94170580040464030a006048000e15a0350780841c49211220600d07217400c07851400c0200c0c80345014180a1181c1c1c00142340350810b001d0214180e00c030740c1e5400050314407800c0d402c10104034034146020008150100c500461 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 523011726 1250 523010476 523010483
    0x406020d080708040b04080a11070305010b0325050607030207030605040b06101707210f150e010b070f0204090506090d09080f0c0909010b031f050c161527 68
    0x7840c0d5680a0484030385800b550007902034000000030170049081c074401004865600e0800380d0400103882c501030300e00030181d8001d8903142d54441c1034500520b0709011200707400c854612445041d210110030700075000c4191199a100b0300d0000f840008060007032000200560300510304100d50b00e054282050904422507000f8030030f000426500070024000c1d140740ba240301c00d0503910045551071030020f83d401c21280a40141d1565061840452854540107011108401c6000800c0c03000503010401c1440c5000e40021941c0500e61005108915106080e981e18076006440078600c4d003940d0000c60001e00401002410070302408040103600c0100142070114a85580c3e90101c205981d166101e885488107883c001050b0001c1c0c2c003010b0310349081103181d5000b0384402d00005283c0702603800603140101e5244144150500650764034130f29021445820b6015204500b0f0700d1501420001c1424a40201c05000700240400c2d42410100c4040340d0040c0c0c00038404468a40402c0880019401003440494044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 523012976 1250 523011726 523011737
    0x30c0a0912031d0a15032c0a05010b040b01050a030b1908060708010501030e030904050612012405040c120c1215091b08010326030f010914010303020303070c020301060b0406020d 78
    0x1d071039604050a04e02c04940c0c81002444005158030b01c100d015004442145190406c0c407e041c85107044031004404102004600a15609079245491802d45140c810307076600c038a16020001c09141d030044221400c0078580e1500050390050307000080c6030034643c588842c0400c0144000400c840c0e00002d60f65003c0e0850f9128580e0983e0303207e00442c00d980c1d02e08400d00d8282c20501c007a42441c2029007003950000d1000740f010101c45140d034001401c43c1c038010a100442480600c554050095500001000d888240c1c3c0c11300860b0f00d0074001a1201204400181e4195910810b00c0c501e64802c400352013021012090600442c040c1d0705a0752207401c1240602c0c203080b460325258413007882000200840d1841980c988440c40d07881c2d80c03600e01c2220f000c0d192001044020207002e05292203038a000303502c17076a0411061005035040c40410310807240128a408168500e0100500101c0e40010950354080b18a14040d00601c1c0c0f2071000c6405000140d000209070000810b0220f00e482e00464423102140842d580d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 523014226 1250 523012976 523013027
    0x303040f061401050f0d02030c0913352209050105150723030d0f0504110613230409050109021c030c03120b030a0317100605030c0a091203 61
    0xc10300042c4280305880d84684400c800c421181410100000c504c0c1c00103060762910510388011400000c1d007110002c25440740d182c0c2c44010446100c5140503e1028010100d40d0b052203800154880300005002e01100340d0046450081405907540409100f1000126424050756425801c00602420b0043c144a440e5602030b05000b03840580a079103c003500700c070303501d580f01c80c01e512125903040114001440d94041004001a00d43d25070045c1c07070b181080a2000503461400d4100000207010410100c3c4c17103205c00f003200d4071034a05903071201d40560f101c01400015420010340101c0c0d000c036112100366007007420060000280503040d84084011402034a48a1126110307455020569141d008014086041c000740200440c3c469200902400d0a99200041e44043c900000b4034020203102e0450015442c0c0318030503070000002108076040065a1500f041d69420010058040d010040c0030908441000c102030f40d10070301c1010503c00400344a00c940f045005503040003050420281080410400e09a0b403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 523015476 1250 523014226 523014251
    0x302011506030b220605090114010e01110309040c09080a110f0415060305150418030e100c0206032a1803070608040f170406170f0106020a02010c0302030c0303040f06 73
    0xf844050748401800358494038950580c130512448031840e03e04d48166102404034407500c0d90800a4080c14441c82c2e6056043c0e0030700b0004000000b43c850860400c140c5402035134140320008107446c129401107a01240041d41e0f400301300c4020a00d58441e1240c2d03c80c851450040c0700903080550003821007a41c00c29583c4244000b8002940c440d2102940c4e0f5000750401000729600c40e0780701c1504681d035450002021744079500000d00341c5031800c1503000c1202c201049807041640058249000100650302003140807401f4602510700c2e4140d000103400380000100113002642030101c105c5450061200036200010342060025181d0422015000038070401d0390100503902d000640e00c0e044403000c0e0f543e82c80c5a6110b907285460107280c02c504680515100d00508141024103000e080545a02d9884012012800034550307803404015000c0b00070074000381c006114441c2e0104514a41d1502030806015444517441c0c00c91846c40340e0010707424a0700001c0107100030042a081c0043e903190145000f44483c000044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 523016726 1250 523015476 523015481
    0xe010f0e070f1202040e01050102240c070302030d0905010605010f09081f0b0907030506010e0f0d06050c0c240a0c0f12020d0504080306030607050f030a180f030201150603 75
    0x141520311525240041c409510451000515100768940741d21800340400d6144281e030401d400c000100c00c2084010310030b5513810032180c1032110340b0420114100c010307100c44080f9024064074101c1d010500260040a0500070401c540080141100812551846080c40303802000d1a00503d400505130009004800b40305402000c195226500035000150b00d041480310b0540e5079192501c403040c2c56130031800d115510700320307280d100e5401a00e02099a14120f00010b04a0007003068052040101107094442501c0c1e28084107a01907112400240755202c07030b44164190f020b001d492540c2c901c240c1c2924080b00b1000700420391802002280c4070800d4507940c3c00481614000c0307003100005980e030400d4075400d500c5041154038600f04803000501e0b0040e2004240b00703481e001c0f18255113105002041c4411030504115103940007400349407450800c0762920316a0214803003d40310746401611011240710f00e11741c5040b5101d8041d03002120000143c01c03407401178060308902815054194841800141075406030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 523017976 1250 523016726 523016729
    0x1c0903170c03070804020a090c030f060503150136200c150601050c0d02060415091e05101d010501060e0a05130b0603010303050409240e180105100e010f 67
    0x20800142956903800e411074004c900200140d90128000381d0004d160f140e40c2c840c4840340d0303c0b140d40100d03a040c107621101007502c0c03650b448030303009520100043d42440200001981903c00c40340000c1185080c2401c0c1a00b0104042004405c0300300100e640503500704954400003c1c414003410142407400e402007045054080c0840444441d000105c0000556504144080c1c5c0540141051b5040c8081890100c0c640940901002c0c096400036090009100d032800c0301904040b20020300f8000c402c0155200ca030760700c11510300cbc01c0b01c0f49031110706441000707020f0101c40031081d01e40c4010411620304a0304850320f42c414400d07038940d03546000c001052542c4540c2d20007501e01409041212650b00d48810702074541d424207644c1d106070780d13100c0c141a0595601c00c002d40c000c40c041e031380c0d00d500c030345c00c1107420b4084400070482c510000e01c0c1c4061484080ba074009484085602044120801380d4898070640355080107003d00800c25440c210420600092625816043d1481032280150070380e01d600c10300c0f0501d440d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 523019226 1250 523017976 523017991
    0x6030b0609010c020301142a0f0f160803131112030f09060408060108030a1103040521030c0106060513050901051302161a01030b0a0b0a1701021c090317 67
    0x8100007042540259941c081a41c4082c000060341ca100c0d0744041e026101c256007449040d03102c216a24605030113410b0844660664144051030f0078010683c91002e80b180710007100d0305a00100d0320311021030744e00340c40b4030400d80c02406040d03403490041d4203042155251413080703c0034500c0b00720011150520404800702c0640340d50040d46072500b41c26006195400c400c00c05a807000c801c00000c99000418403482d8000c03d42d0720011906c1d095140720180110001c211f40803e564010b120401c03250351407040500303d010504480f1030480041c1303c1182e04500c1900c920111960078900001015540320700217028502c1700d4a80c200c44140c40303004200da0702e082031040c154000c1801441c800c01741e600c3e034010600410700c2c00071401003100c1d660300d003c501d40d011a28501010003c20040050140c800e5220741c1c00203003060104101e84440340080c0503124203005040c440440b900c0f40480c600b200754112203001c80c600c15200078550182c45040301809541e50304030f0008000741b04620141d084c0c03145107801181da = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 523020476 1250 523019226 523019239
    0x3050c1305040b040905070b34030804060603050d0e040b060a080c09060c07090903080604050402060319020405060c10060b070803010308250b09060f16180b04180606030b 75
    0x1d8881008041d00343d000740c841d840b40e0348000c035600048042100c00001c02000340f0701c1d0746610b00101c1c10380c0315170890140c116a003260b6910360706200d25555a120a25545810241d0140d204c506008005000c0e6820003041ca01c209401101d1440d0049001000640111414004001c2c001d00344101401507445a20100300c902000c9002c5001040c05000c040c4005043c20741048510104a49060b010b075100a640c55503500c012007d15510001c419070060041c0c034148000c1c1810782c007050040c40300610307460701c60899400e88400e140c0d943e0125001001300520090320f910020200d03d440300d06003034220000520381f041c0022952100401da584107600202d445045070f1075500c6401031a8002000c9800c4030401404006c0d0700303079103103000900482c040d4110010501e0f000f9040b0385881005400e80ca00340c21031034104040001c071000c0c0b02c448003a1502e45034220340354140c0421085001c5130450310000c40041400308034480382c031810030320403c407098044c03180135540c80c41601107a814544150b00540c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 523021582 1106 523020476 523020479
    0x30c030a05060a050f100903020306330603040f060f02031312090b1917010e07121e1e050406060501030609020903030403020907090b12010603050c13 66
    0x40341a00c0c1d020805080000140a0312080076500b84a55011031418046c1445450b1820007954090121001030800320080c2c0b50149010000141c05000300700e010201c404882c0c3c0c403d202d91800b0b03011514548075501c500d040303122038a90903212152900c50100d1030000c0d41c03000354803c0c42240c0d110b6143c2e880602d00888a585001c2030401044454501803107094100012622096004003a41c0e1052209107400d407600d500000703040980c071059000000e1020020404d0034400c0120b5a200747c1001400e004103403c913803034a081c00035101c0c0b9010907908940d20b030f81d10107524040c4540e181900103020368004019140d04075001c8451640300c0f84104042d5030540a2080909a004825030800c030402011903500d000d103110191040c0c1c02c00021501c5180501d5144018110607507003a41d0702c0c0300d08096410402420710801c80082d140c13000007408041140141c40c031a0032000f1100000b10f = true := by decide +kernel

theorem cover : BRFrame.Cov 522841726 523021582 := by
  have h0 := BRFrame.cov_init 522841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 522841726 ≤ n) (h2 : n < 523021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
