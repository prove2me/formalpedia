-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4618
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:11:44.621626+00:00
-- url     : https://prove2.me/submissions/25bff14e-2f79-4e8f-a156-ea6452af9719

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 830395683 ≤ n < 830575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 830396933 1250 830395683 830395691
    0x1d01091a091c11121f0c030e0a080a120f05070f170906181507020102040f090203060a030f0f140c01030f0b0a0302190b0c1005060307030804120c030803070201 70
    0x121402c0403155100d45560201c8503a1418400c1d5640c41074051680280610850364007030410440c4500b80140c10102c2131911150ba4901011082c500240c0508141c00c000309191211581600001040400509600c01021840c0030301c82c4606403000217018000700612540da003a540e0705401d81d407180350300075010303074079101842d041200000b01100b0b0400300d010303044105241400090340d00000c0b510307009007014600d021038141e4440344618000078002c8001c3c1801d1640d081c05061a019402041512240181c059250380c03609100004c7c7d1005980c02e6411010741c03007040001c282ca5401807207065100e4000001c4921298072885285076030002000c000c0c5d00251a0b071132982da014420002d00820b0501c0c103005150390f0000103000e9800360321001e4001c1d80446884100303444101090f0b8003508018200c40e4032403412003101543c0e03030b1001100705d4405241001180c1c1e1880c001a00400f1241d00c01c1503103207801e007440c54202984042003000c43c2d984801090100003e218903020b50f100d44000d0b80001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 830398183 1250 830396933 830396947
    0x23012090306010f080a0f0602070503071b050303120a0b04020405061201050103140624090d291306090201051201030f051005160c02120a080307030e010501061d01091a 74
    0x1d41407402c1079000000001c04807408106014001c0f58101055400480d140020703030320750501c07001a100e031003001000750100260b05400c124101004412003484004100c07015500c80091540d40e01c12280c0e00b000e03902800c1c0004181f42e25603004020f80d0b10002d48094101640c03100483e03190b400c03411591000540e480014895564180300b40301c041081036480e1034540c244280880d2a8400001c82c00c101415a04010b007030880c240c01c200c0305e074140068200401023500d800e0040040d0750007650380204040270a03246800000d030404040c0684218004641d145205545540041c082100104d040c02800c0c0729001c8600003810100f0300a500510511191081174038000d41007495440043d8202e61800c1c1c1070180b24031380000c2c0b503482440242400f88042a05000040c00f001c02c000d08040c0c0783c03084442a404210b004005540100b13401c6c3c0b018418507044206c0542651003d0040c070000840180c1182c074800e01c40682c0c04140395060500344165520761202c10300302036038600c101503195000500b80e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 830399433 1250 830398183 830398189
    0x10e070f0c080f0a0309051b040b030601031a250c03120603030e13090f080703080106230a03020c010c091805010518040201110f070509060105030402301209 69
    0xc02040301151401105941071550707194424003030b00c07608900801002c9000c2c90002e0180d401000b94a0300403003202c0c0490700c0d09010401d0399400710112400b40707003404070003402c50074001a0141a02c4d4010941c0b50130400640c001942c82400400804604112550445101440c0e1303004015441c40355544002641d402d08000d01043c6d80100c41100c814a0841300b040030036403040307030121010700c11070b2003a1081a800c0003d50103000c5100e4054034140500101c84100400700f401071401e1446a150041c01d41c0e6601d605650300c1c02c1048200313403072540c40c070038000007540e07441c00030980002d01d410010705290b41055000d084558400c10007001c204180340a000e402c0c02c3c0d1100300c160070341c0c0326418405076040601050146a00c003480d0f07010000e00402103030440e07001c1c402c180c521038841401c0340c030400e170030400442e9160110300c5841c2c0540d29000115003c0d52041e4111ba00c5180c0142400381200b11008a01c40000c080011400040041042c0d002c504501486412107120000040d80c2c1c0b07c560039420 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 830400683 1250 830399433 830399447
    0x60402010f020d080106030510091b0e060703121107060915050a0b061e0f21010e0702060612010e071205010501050a080a0305090a03060509010c0f080c2709010e07 72
    0x180700035940700c0c000708121158440d12081c1516801e18000c103807511600480c01805000d0742051035020b05122014808014040d0450200d4286980300c0f64072140032800d0002c24424100060b000030340d4420140f034000b4054000c0b0311610300c10140a803034021261181e4044429000085400000035100300391031000c0f9010752a04103a15139030030041d0b054010005140da06c12209007813000ca002c20401400540035506460b428030342114043ea0310707050807200c240ea42c0d0b0768000010b4400840c40011410005e1000c40511032203080c0c0040400783c0351003040000e0155000104002c0790348440100c69507800902200006017910402c103020b1140c6890b000d400c1d06d105800543c0a0584e0810802440b80000345000801e5054102290b9400c001008211006010382000c1c0c809410441400b110390815444a038020b2060b42d10080b40c01c1010f04119540340040c0c40c500c0180320300b1b004e41c02c02202d665415505040b1442080501d0050b12008a10a0002640062074407801c00b000c008106401541c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 830401933 1250 830400683 830400707
    0x20a0e06060f0a1101241403120a050703090f063614030c0d0203370f02030d0e0a0902091206070507030813020d030f030207060f06051c08120606160506040201 70
    0x11b15a1280e110200c1c000200f41b0300c601c0b038820401140401c0e0030082c1c40c10701c401d0104810201070640d5a2904c0384000d80a5440150b00701e00140d101840095851400e035000740945280b0f554802003142c1c940d1102a41c0d03102101030461081c56050300c4440080485c10003401070000001480c4690081400c050825200c8100180102801100c02d801a540818440381d86035004640c071402d100e11304426502c15440c1d071095071403e40780307444280c00c2c02811700945000c0c5100f2800c451011811940442d54403024420494104c10240028000b5281c2038001c1c0a450401810262007080880345080c03502c10705803244004108006610300a2550040c0025840988050150440c0045030f000c04c114140c45040901040510f20911000354860740440d40c550350480018042c2c00e842c40c1444004000500c5007511622108885080a5011003403280e074550b0400c500c10708000c3e90214900c0c2c01000102625400f05040100010090021009980f91409036000302202d103001d20014104003c015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 830403183 1250 830401933 830401961
    0x1508010e075a05160b0133090311010c0503030a021b07031a0a0e1606020d021b090a09020603040b01090515090610050f0408060f06010c020a0e06060f0a1101 69
    0xc035041110904040c1d84102c10103503490819a68500010284640041c014009154482002c00000c510800340d2941084041209143c081d03100ba111101c11040460594000420840b40c8100041003241d1921060103c1c1030606441c50850741c1c0c6c80f282154412a421513140d42d0102d030960004030b82034241404d10110b1300007414281d003140c1324401d511850060082d8001100c1d4009003203001d50380c008400e54008071088844249135644907801c0c01010740a03850051007800b2503446028800244a40c903174403812407420718058130005010090100410701a40b0b2074940e2035920068880c0c0c0011880f5600912840d151541403807800b90070755402505540400d00d41400380d0700e165031400c00c200c0d0040f40803500586000e16540e0144c40a000b0b503142070080078004034002800d198080780081c800d16149035182401d41e10700340191202e03804c005003c0e401440d2110207200700d2118031206074010800034030681c1840f450280110046c4d120188190000398074201110b1072202c24000c0d0844043e9031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 830404433 1250 830403183 830403317
    0x5070f050d061505041b0e100504091113030507030b06060319020706240614070c03300f12050402060307030f1b17011508010e07 57
    0x2002420402481c6000303003240b0340d02c030070360f0f0860b000210082c801482c01a006111707986100c0504211900d15000030800b040034104007000d01e184c860108441d016050b101c0d00e00705400c050403e801004c60116079118401e08100303a102e0a155440341c0801107204000500d4458114a08407014040140c100ba001c0c0c035042c07080c40560381c0e44010540d1402481240140c40f1192800d000001c1d0442c51030000d251000048100701c505200c92160082c7c4030181c9401d0042e4441500703010480c46044005040c501400e03006000281c0303030047d16440c0d069801030381c881a58291650a03210b80c10b810056001c00c034008031034030500380c00090750903043d0300d05001003180e40b07040e8004c10303410710008009000b016514414504020703000d50000d11104964013804491100030100070340300740480c1d030f820035901c5142d000000303a0340c03072000102d01c2c005407030b070303030340000761740f0706203100076242c0c005451001031022001481088a0030481064004503000d10303103465501c2c0d28103510020303846500d000120b140c81 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 830405683 1250 830404433 830404439
    0x3041202060f011a07060f0f06050a050d02190f0603020a080a02090a06030b06071a0f0108030f04031b030f0b0f1636080102090f0f1807050d020a0c05070f 68
    0x606046604640007071912142415010303800c001e851003405e10080c5a180303400b00e028403d45455011032003111011004204a03900c490070486890410700c1565030013000145058018105600c0b21002c14210386c00347c11703940e0b80b0343c08203480980c41e075045032001a40c08181000c40a601190458221602d00000c50ee0404140301040c0ca082d040e00543d424140c82e00b05008113500d541e4101c4440c56086920140100101c03054000c0100c0207507511894208140004100000007000326054142440400341c51300d1b10703556035210041c40c91100542c43e050060800004a00c2403070703280406a1007000100c1582c81e2044040520030b0000d0020000c8500c45a1079105040c0c02c40e9440703e03c001e44890013100342035030311368110651010301078800000114400005844d81c0540141040513402c5901000d0801501c0510540d25042104194000c414030406d400f5825401a05c40e080031840c40c00c01e24201124890f2003c0c2d074002c024580000b4050310b00c030703000e100b4180611070242c5891601e10340c0070340c030f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 830406933 1250 830405683 830405701
    0x180c04050103080a110705131401060f08040b060a0506030a02070c08060105011416060e0a0510020712050a022d0c0904051e0c150307390804080105010b0304120206 72
    0xb400c13800d5414083d003400c10304010501000b0740d500400e0020850303140702a11407150000340424543c851002d8840c40700105545008026141406019035a075640540c1c5c2d6441d0107001600281500d6040888074038007141d40d40b242c0e03006600c159000c03100540d58050300d10b460351a8502c10760282e0302d42d0f0003841c01807107142c0c1d0004146809182c01c6048680f10100300181415503a066580100101e00d010640c0c0c5601c02c0100b149126140640259240380c4010100c030000c0c1c1c401c4041c014600c445041c00c500102c0e0294001e04903a24592045581c1c020304d5441c1d200d0040d6541114000406a00e0f50200494134104420201e854081d42e090f4141e05040d42d07405d5581d0058035040041980440440d290100204510507504c03100600b10210500340480c2280305a0003545c882c00081c2c0d51060070202e007400b05400c401d5121181e2840641242680c40880c503803c0f101008469410003040001085402401003501038096001c6007503907410103140007103488100c14140d0081d900310004000c240d00e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 830408183 1250 830406933 830406937
    0x5180904020f012732010e01050c0a0f08030a06120c09050903121512010903080606030a06030b0a1d0d0206070e0d05150103020f1c020402160803180c0405010308 71
    0x25000b03003007a540f003042c20443c940d100e1340c055403c40c1181c5681c00c40051403401c84415405400340004015402c04070550841c13295180309003120f408a00d0548000905510900090074a541c00b68281c609505681c0d9a12051070904042901e18000c040180302d4085120301c03d5a00610241010354140110350b901c500304944a4803c0788102c0f070f66500012207030390003841101c0241d80300130000354440ca0101d02010300003400005083c01807044481c03144a450f014403801c041560162500d00403039a49038200486a0b100901054a903a11050000f0009001c51102c60081c0c1d407410000c11320142044220082404201c90f00400398061300741c1884c0c0540105007544c00c5255841c110b0191045100480c0314520310100041c5144980e2181d00da250750030b42d4a09050341c0c802c0b00d861540e64102010800444507020b4070013502c406509151005103480c0d402003111510240d1041600d0042d501c0300b0301180c10854a040c7e180200700201c0403106818058200e0070300c0c0c01c543c01c00040d41541c8030700e2428 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 830409433 1250 830408183 830408209
    0x1e080405091f121e1406070201050714030405100b0a09020a09050411030c07030807020a022e03110a03050603010e07080a260a08040213051e0c04080a0f080408010c0518090402 77
    0x70a145181c1394050080d82c0800b0240168402c048500d2400d0041c0024004c00040710a00c001407100c26103a80c61000c2070f812207003d035400200070a40d111a410b4000010113501c4d0304540d000b008144009003046580c009041c5a0f40c1584421088c1854041440151034040345202e034500c0e020000c000c3d54a42c0581541c000fa80c0500e044480ca94600c402645441d5840d2001b96210090303000102030312458469000340c0b880250881c2c0c16071001d454041d010b403a000181654001024032000b11031070710a03804130b540314000070008079400498a044034144810358009070b2441e00440059800d012140d210021824110a10b202501080c8c40c810245400386155140c1003141c2c580100c1d00355078500502850b080341001040000b820038003010b00b00390700002c010b21071054204001070b1101e500e440a1b503081307915200144c0b486140351b5403000703c4c800160400f203400003400d00c0b01094024091048525418403603c0700fa56030f00b149011078083d2090034800610480f5000104401030300c81103801010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 830410683 1250 830409433 830409473
    0x12150114030705040306021204060f0c0e010c0213020a020303011a0c0c100c1a0901110c070b0a140a0e1201050601140f0d020313140a1e080405091f12 66
    0x12070b1200c4400b21031a00c11030340050b040c0360000c02c04006804014061034010f500c1407404004d030310000301e4110152502100d40ca0301042e074200c08104594010410090042d00c01410f803d0b01c0200c1030744d80b00480c0c001103150303001a8004801400700780303007544414094242451010b800d10698030009a62100b888214030b010b441c00d04241001180100003491005501c10722a100341440f0a604000c441002c907444040c66007050602200050300c0d400b102d00318400341010f095210f040040b0f200035640400715201c104003203500000a01c0c104a0042d04c090030441d5100380000340c000041040125010282c440c0c0760345800c040c042240c1e0400070340740c0358050319101c258954282c8601c00c11940180348800072000d00010070404044c951505502841d4401c2010307416240780001c0c45696075441001c003c0c0f41d49000100d811a5505c0440f600c400766110704206842c158441d0f001c2051100c040d201900003020f0f48414405803402403407040007404000410701c0b9010741030303250348490b0b441c1c010b0303040b072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 830411933 1250 830410683 830410687
    0x5040b0403150b03030705010507080c04030b010302120a02190302031c0f0c020102190302100e011b0e0f0a080a02030d0e0f040f02070206030f04150b060d0c1808010212150114 77
    0x10001510f800038800480000e0640b912204a400c041d0f0107003201f2501c2000048010000520803210030050300c06407500b1641d0503042e603080d5420700401c210100c00e5440c6903c260241d5900590395070044491500c40c2c1c91301181018610b1040c5071504081c1d0014140d001142003e20422035441081c0c600300040c02d2a084ea04114217000607800e003140d022500b500c5120055944003490340000c0d003c104540030620810044026107141c1d4201d407000851a151440c0c030f0761816694903c56100210720910090406102000040c00616484c0c2ca0b50f1060f016900441c1400342540360500403c004104039092100380214074000088901c0b04609515205030b940d0001c41c91384c05440d606a0b83c80f141d003e4100c65480c10800000b440d00ea204a4007243c1c0c08040902850026805000d001c50044020f080142002d000e42c9298016114100c9003000300a80780000e1203109100c241c038040205190b00005030f840d200301c903012840b140000c040040e09080b80c480310400c1c1c1d030b028031407148044401032016 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 830413183 1250 830411933 830411963
    0x605090c18040203071d0f060c0c190e0601051308030409050a0b0d050d140408010c050310081606050903030c101b080606030103030522180605010e09060909010917090f0105040b0403 80
    0xb220462061071f403540140001c00c00d44800c140000b035894400200311106c000c911800140d04500140314012880f08030042000f0072025406000070342141c081104d48002c0103a00d860505183d50425400040c0303803503c0d0410301c000c4400511682c0b903080000d440000102d035041d01d9265881c01520513a030204000701501c1e00e40744c01414141c8000e4070011000f03206c03d004240e0014101d1300180c1e903807107101c0c0402c1c000080c942000100c4451415909050440c054900801a2000d070021902d0640600080001c1008000c09001c8090f103441942c0e00014200d4603403548190854800207520180314100c3e040c002507136100ca05a07811280c3c5031800b03030f50390fa18507140300c81c10f100100520500e580301c43d800030504500c3d11129040031840340c0001c014a41d561001114800381501900e500190b012020950a081c5040c030f45034007002c6c1074008600344a07103a0716641b6410300132500c5036568401090000c0c5030b00c1c2203405410485424604241814246248020386215600c001814080e07001049 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 830414433 1250 830413183 830413189
    0x2040311060c1509280b0106090f0b0306150307210603080306060c0c0d0c061701120f1103030d020c0d02010b3307030201020d0b030d050a050705010605090c18040203071d 75
    0xd412005d21014203640c440c1c0c2580340d04c01ca1584c000c004030780c000071031000405e02070b11507050201240d0f0a0720008070b0b464904150790111b9030010300031940102e9007281c0c4180704200c00c001540144101d0781c0d400540a49201c0340d40c108180e1002541d070150402c1410001304041c0005c0c4d0790419000c54200755180e00c0030103800c0c9002c0000c103030542c205402d5010b0109000f04102000c0c12503000303407100c1c0d40c00c1079010070351940b03c07000740079030041d03401e00c5810307500824603400c0d003410858802da110088002c01c4a000902d11b0b0080c00041038203d800003101d0042d07403002e00440d01c488020740002e100080711500080d5600c0080c104540040000e8135003c0c1844840ca44c0180b1a04030081c1c01c5599a2030501b0004e0103075101c3c0d815160041d0809681c0d00c0b1500340010b0f5585900f0840c2c0c1c84506000011504a510350720100702591203641710080402c60350760703080c0000d001e04201420300d5a1100c011036904028107141003038900c00e03841403040140250b000844010310088800001103012071300800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 830415683 1250 830414433 830414443
    0x1809010602120418022b0b01020606011e031e090302070b0a0c1707080a03020c0f1b1509040213051f120509032b0e0703020612270102040311060c1509 66
    0x70102140c4000401b242826022481403c0c1d490414060050301c02e40c8005980d5041c0c1500c880380001d05410040030354089003029450314009515000c07561400c1d00040029081d24880026181c80c1d580c41c5100c1050b804010741d00040c059040c1490500984c50f0014001504502c0c02518113010340700402450f401100072034000507031102c80c072178894514100c020001d40111a02032424400c40a000a41c0c0c0ca0018102c0c0740d15040501109030400090140100020250850301c59007400740207003043c0f80d480b4000b03810950180955115640e1a0a0406c010450b000701c80030440c5407140d20140134203620419043c0e150514050125250312824205460342c4034241c4140703507145040304500c00a503440c10380c0003203c4035800002c0c820010300728a159111082880700a500c030300108204500f02003020f00d840d500501c46210f0311000c100c106410b848030303030081d401000345941c0054103001300410b010250b001b840c0c040d500c05081c000c00c3e0340c5080e5544805203c2002100d554400a0400581048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 830416933 1250 830415683 830415697
    0x408190210020f040609090b090c090a09180c0f0f050d020a09020d051803040509180705191508010b090d082710080c2d180901060212041802 62
    0x1c0210f50f00c94002e040d02410350481d004400005040c440000f42450150081c1c04072084020700b84045500d4801d18990a6440240344581150356518001592030b9031b889035100d100004200305402d200c00345081c00e45d202264009510391078801c10180000007140c012141a140142c8400d440b800d09400041c1441480b44e2280d20302a000044019000c03005402c0540a03404843d181c10031205404480760310ba008a02901d0381144200000030807512030140c4035401280200140c603845c03038580c00401e202845006115640c02040c0f0310822000300d44104030300c1c02820720310302548294104880c1c1c00d090300c5000700c03052262498210200034400c211003114603402d03800d140520b41007007040b5039050390713100300c80705a1080424011006095015141031440b440e0800e01d40f92414520b5211921070700e8504c03100740c0c041d0fa5206800f100f0070500c1c00003400c0c40c3d851078640045004495040040b01035058100341c0031034200031004014401c022050f18140c07003408140c5000c00c941214804001e000d815 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 830418183 1250 830416933 830416963
    0x803010b0c100605031513060e0616091412101d0105340504080102070303022503023f030613140103060b01171501021504081902 57
    0x58152580e001031220320704101c02c1c2c410340e90741241d041d8101c40b4144034a54040d0407035031401a4191000401e1a8809040c941002c034200c040e888490480b0407002011801d5449801440b03428000c40c19901808a0fa0f4070b03040041c10309008505040d09945a1540d000d1032552070f500a00840900c058212246c00e603c04009c11103400103102082c0d00c2c150b0b8076110719440d25020079492146242c01910000007d43d24100000c030f0000c410f500c0e800410010b60410405010100f0781200a000506145000381d401684404c40960440c003442c01c0000b00c6403400700c02c188142d001039004a41301103000030064110780c070400541421040c1d0300308041c842c01e445040c06580f007c0c603c150409580500020b030381e850b50301114885440c0460b1a880320242c14180000010000511141c208141640c010300d4550700da106400310840b0740a00503985010001c00c040800701981d42c0c104000025404003140340e0318581020303101d840c01442021140f108114030006101529402040a403900fa4004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 830419433 1250 830418183 830418187
    0xa150e0a0b13020d03120c1b020609060d151706043804051c05250204140a0c023c0f0a20010f05180f13020d0f02040602060c030a0908 59
    0x10b417800908108000c015501114680f103d960640c84c801d2051044100d9003000b491fa00308240e408000c55500500e04c8258003140801ca00c500c501d496000d94200c50552184640070305c2d0400c22a0a84010010416412540040104008500301007a60102e00c00500200500d04510342e06428080c00d80c6200c1030a814082c9052000b08400000c1c02140c9113600010003c4810b0511011122403091192650750949940d2040c0c1d003550544540164252005100088680c00402c074540700c0e00c01180c10030301280c2d43c2c0d905004050780610002c070f02c0702c1802c503541111003240b6692500c0c0040d0941e41600c0140a07200c0c01c0050901001500c03006d603d24022151701074001d00d0248901201d0f2290744004d034a02d900c42e00441d5010360482044031119840b0b241c04e2400d0661401300f0790401d01c2200754046180091320105455541a0401503010b0717010141e0380300d850a07449419202981110781c4450b104010400c603140d03011485a810001d880200780e85c948845145c040035048085029225240c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 830420683 1250 830419433 830419459
    0x405150304060b01020a0210080703020d0c0c030e040216140102070501020c100e0a0209010303031a13060f120209010510021f1a030609030f070302070e01080a150e0a0b1302 76
    0x500000d54400c40c400c038810300c12155664012600c03542000002034000c1142140b0400385409041220b911010034900141000b58148c11314040c0e81076201243d0100b0b920303d100c4010705500103040e4101000542d0300354078003c480c1029001e038031000703040a003045108001d91942d52800390112500950820000e40d1a004000c0d143c6490708103007125400002d180c1500c107244050301007141d00001c0d80007805404107a01e151800e82c090207816000d0190360900c06015041340e40c41c200c07041c180009a02000a03503a09003003040c6460261608200d80701030036070301c00c0310041c0d44440786c040c152602610f02d9800094000010382c40c2000070511000100880000307003500724400e910a0340308103c0200c501d0740300100742c0f00f855115a400d83e101026a00200700d840a0481d541e0300902070b091107441200c1c00c05540e604041c080c0c0c502a004151160000803114080c400c04400c0c1d2546841050010000e0410541c2c1d010b5903100540001041002000001000d0031085001d14030680e070050213901c0d00b004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 830421933 1250 830420683 830420719
    0x15070c03061d0106141c1a190608071a07141513050a1b050301020c060a050c0f0a03050408070501020705010b01030e03041202120f10050a060b0708090906060405 71
    0x20b80c41810036030403804400803002c8030b030140298411074400e00c0c1c440a001440e4802d02011501d80142c0030010164007840d1000101883d20311006160410413402c142d041c01005030103400003400814141c0ca0500f4402e00c070700c1e2000300c0c14000f21001202000d1400c1d0b40d00c075692421b80035a10000d84004400404a1180c03030b004a00f5518014925a2003a070503565000c40180005150030040c1403a401601d942c0300040c810042003842401580c0f40e201130302d0b0f0340d000080c00c1e6030081680f90140c4c0c0150041c80b01e0f42141d4040c0d01c0d01300c01c0044426003065250003840c0c0c3c10b030150726850800c05444101250a20640104960103140c0010082d51354660505189029221800480740041d141061640070001c0101c2980d0a803408154901e00c0003406400308116040d00084070b0007330b800381c01084401c013001000b5120306a40f400c3c0011540b0b1030001403940c1101c0e225840405014410400840014900d8044441d445002c4070310745030503218a008942d081c0140c2d04115045404a0b0551b02c3c0a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 830423183 1250 830421933 830421941
    0xe0a020c060c1611010504170a1101020307030c0305091c12080601050f0f071e03020d020c0603011401081e13060f060b0301151812060e01051515070c0306 68
    0x510140803544161560340b101c150521840c5050582c031001c0e14074402c00101d03d0200085510300c145401814076894100000410550b4070340160168400d40b080000c00c24008443d04480c0800d002840c14411152400390045514080003003c0203030004e00c5206940d2106c040100c81c3d0a0800081203400c82450f2112041142c882d901d0040343c10302c00040c2103980325a0031112011f1034041018200020110503c01a07007054030215408202c8805e8031402a0b0345031b52021501b4002d070b0080000e0034110317801a042524030160310340500c0f0204014040c90b900707490280748442003880c001040d5a100f029a040c80140035140300c401c41c4c410f2040c4940c11148019000d801030151004000e1401d4411031a03040341d030284101900010280010840345e80c598840d500503032040c0c100f00003008040351103143c0356001038100c842c0400720540b902043c41098801c03000f1002954000304905e0130002e0344600110190101d00e40301c2e8940d80e0740742a401d0081005e442c070880d03001290256050300c9141c05c0020b8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 830424433 1250 830423183 830423197
    0xe06040303050414010501030c140f041a011b0308070c051905071a040509040b13050307060903110c090c09040f0e24040b0f040804181b03090c05060c070e0a02 70
    0x40852850030804c500c184071b520b0417070350321403545c2484a1070080c00305080011200000d41c4800c0a11441c0c000303403500d00401c84120b0074242d003040c03811035420000d0f00ca035062820310301d80c940700140b80700b00080e003241c03407641c00214900740401c0c4200035107807040c5400c034040d030708250940810510f802046000641041520b148038241d00000f448503810f070000c0e00843c17040355400440d01c0c4c04100807420107141c8a0700400d10b84080400c80000e521410300e5507002c01c00885d0300550f01d8040006141c0d21641c11040d525400f4090542d6200041c0000c0d000c020142c0070448807500040c2e5140a60b60b42c0c2d02915585524250501c80080001d131403a0f202c07184244403181000d10800307111340d8081500b07004c92049612032106541c079190005004054280200111282001088081140304500e8658907140503030840204a6a400d14180d640707003010080c10030300341800c1078407980005903050108800d0f110241c0341540c68440c90b201151401c3d05590080311404000d0081c004100d146400030502 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 830425683 1250 830424433 830424443
    0xb0702010e2d030702030703080a030f0939030b01050307050d0c0e070c0c030b1008070609030201110309180f0714090607030908060c0904060801200c010e060403030504 74
    0xd01c04000c21803940720503202c40340350b82c00c400119111214a22180d110b1410388585411a401c250060f40442e181c96019002510121004142c4103040d6030306010341c40d03030100864014021070642d41e8130304804040b0308043c0b240c51110042400c8403840c1038548420340d20380d101c80040405549003400c90701a0402e0080d1030090042c4c94000c196420002c40342010294080168018185003020a803c03550002d404c00040100d400740c0e400100d00070000b800301960058003d6400e034100030000c08020340c0b0941c03180c5580c0e00f01d82c10401460b40c024031401c0272682c085c2413001648402940e01c0d400c1d032107101801644034032049140507028407050101441420801c03a4543c1715100e0f81c0c0d050b1741e0a0380000d2040c0e0100d03810001d102c580c0c1411806855074920a08242800c1e545902005090000840e004854080c021400a00b1840d107401550010300321900204440030f0840500e07184c0e081207444044411b1000200140324210942c8034a401034418000e980c802d082c10728000f004bd0105403005e0707a07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 830426933 1250 830425683 830425691
    0xa020a2115060501110105061f09030c0303050d05100819031e02010605030d0302120403110f1c020106060e0303040605090a150206060f090601020606120f0109080a022a040f06120b070201 82
    0x585d5440500c1524000c040060040003500905110f111a09148825803810003a4032080003000901880e040d2018510a442d07083d00e4016401010040760740091014003000b0b0f03201000c1000e09000f1502d0170090040c62100380943e80c25060a55005000d45d04401c4401050548494025410f60040d0150b40045058800341d0113642e0007101a8000c584010940141010200e80000d004100f0344580c0f5505030140c40c00c540d940c0f40d10604115842028070a0b0809401d8151000742e428491400a442d45050071013955003c2c01c003095580c05035000c0d04041c00400901e545144c0d984a141030010021001182d0910300d11803802034450b03400b035440c0350244c08007245600c11840c095022600c00d00c010f034001d00c07580d030740c1c041004a043d8050020340d40c00d0003505101c00c02c015080c051a043da9000b0348000d80d0328501050004e00c0c24417203c1c01c4002030541100d6065242c1d2514440a0810008882c041016006549a04010070f416031100480c2090401c00e20108580c1003c61803083c003803600200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 830428183 1250 830426933 830426957
    0x19030f020f21071d10030f0e1501050111071203030603121d2b0312060e06130509100c0905181b03010819050106030209090703140a020a2115060501 65
    0x41d81042e1844140001e16a00c020b949a13503081842c3c0307010890f07103186404511080036548070310441d2540e0030801401e40040d080c0103038410f80d0303010300c81c0107003402c0c03030320482c1c451890400a845140b94050307441d6070180444190141842508440095074000e1107100801180360000790410038000b50707081d0440800301d140003241c9030176030191120780886031111a800c0c1e04584414500302c9000002c4050082040014403440d8851080c00c01600c00c41030329004900b44602004407042c102d04000b680642040d0400640320780119044190300700031003000c41c0303c00c010b80c01600d004400da00442c1e0130034401565580490088440baa004042003d0000d0203030b52428107401e424802401044126805203108031407807482d080d11082c1740d900560000414544039800100b10441c1074400b8403069000010074405d0100c1c584054014040f11001000045803560100e217107202030740b00c2c140920740d803110114101174190324070001c00d560000712001c0010002030f116000345154001c41c0d00040c440d032010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 830429433 1250 830428183 830428187
    0xb041406130f14030f041a181003060b0d1e1a0d080d0c030207021804080318030702040608010b0102100606090b030901140903210402090109020703050c0d02010b09070519030f020f2107 81
    0xd66508e00140200820984c51030103000a2130002d414910405948000020301d0030001009081455502880807a1300007100c0080b1803a01941c0015204584c40c06046c460034a503800c81c00c60301e884060f0b4080c02c82e001c46061048550143c0b5050701c005508024402040c1607145c1e009041c9039100700c0b925202c200000703086c08a082c10881f401482d041d03040012607c0780c500414080d8084444c5811680350484a9004c2400c0c1c40e020380c0034070526910b40c0048001581c06000c0c504601500c10800c0294602c0c022000344141030074411000031050000100b102070800707401480c49824840c034500000c4c100f0304842c59984e41b01c0090400d80300f02d089103800b605001798502034000d6800400e0b6070016404c1442c0480290f000c2d107011030a000c800c00100a03081d905100040001226800014203801207030244403140ea801402e500c01c020b8204500003c0781881c0d28202441741041c94001810544015418024450300701380400d0040e000c2807050440000401d00c80a103049400d4010560301c0e41c280c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 830430683 1250 830429433 830429437
    0x10f0522051e03070609080406090e160509130c1707030b060d0c030e06100f050d0302030d24031407050406030203120d0f0204030b041406130f14030f041a 68
    0x140340c0d802c8100c06800030118510b04041c0c50800300103036403402e0601d556003002c480c00c07600c0840c1c41c280e012900b01b08141d00414414010019054000d18515000e100d980003c0c02004449081c80400700c1d40c0e009a486101008401003801e580c208001d002c01a40130304005612400c40146404090000d003d841c400d0041400180e4098801d03030800200814640150400c0c81b032900c1016602e158011280c0d008001c1d042c000c071590010045401d003400a1180b5084554001c140070f102c0d12000c1e140007a41c00001c6440000c601c40001500c0f92010340c894107904042e00d076800324841d581c800841801002d206540d00c06070b80300c0813520840d6880b02030209851084c400a54503401841c04901c080c082d540080c51165024140040c203083d06c0010760f0704903001608160340303c0d90004100800c203d5400e4409569030001401031a00d0f1428420311981c0d840320762401043c5e0031003404284100000000b00000000c40c5c5400e49484001c2c0c445c00360015002070bc01c1001c0303030b951510030309545446002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 830431933 1250 830430683 830430751
    0xf0319020408070b0706110406051306050306060301030803060406030209010611100501121203020d02030711010e16120c0b0a02060610080402150f0d09050d0e0405060a050d02060705010f05 83
    0x2503c0d0040c03800e22201c5481e0000345058820540364801280d106100100400140c265a243c0c6d68036a8070900c0c81c20246d5480e900510140902001400303459035415090700c3c11a0b92148034140d981d51202e02040240200ea40f00940102c3c1900010a8aa401a0300c0c0304442001e502211911200e00000000b9240300b84201d200c02011090f200b00465100c0d1a011b4500c42d043c100175150004c0c4e00c4602c4100da00844250000405070306400b16280401c1c000c17201204180001443d501005070000d4101076003a1050210061070010b50008015003620003074000c0c5030f04071080703890f5a62620069200c0308100e601c540b148044c0703003202d20041e01030151280165000340c400c4c10f254801214003c40b0341d000301e06540b60b0fa4014000c081207000c1c2030080c4124244500050706200380c2c0b4000c082c0506083c0120207104e03a0911041200e103449803c0c5800480d28210f81c1050b001ea440d00114905214800c00544a5400e100100901c07681e00d8001c0c9024001c60700d01e40c1c1c0800400e05e011020000b01701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 830433183 1250 830431933 830431949
    0x625150e24060117101d071e0903060f020904050603070308160f02030d120f06050f04020d090c08060907060e0d0b180f0c121522080f03190204 63
    0x54070541c1c1100c42030000d80c0200c040c1040e515142120960b020001000c907004018044004014419040d18a003010307400b1a00c1d91044000d400e218502505c045003130410320107503880300d04000580c1485104910300450704002d00b0440b80b45543c050348042e50160359440d00443c1080003044842c240040c00300101c0c0d800c981010304002108000c600c0c44916a5001d403180381300c0e0404900586e5052120900d80d19150315451030300b000c840f01c0b4405482501400350780c841c0c940982002251142030280014810072140165106500c8010000600050340f0107005035104c8400421225030000310305004101040441d60309070b9a80c64100c0b41d0035026011590400001000702002843c00030b080d03034000300d044016031802420a28124600080c1c00c2c0d041c40542d002c0b8580c40c1060503c1005145c100a4050160101010400f641c2c2903428026020000440c9000220103840320b259540d030052a0380301980c0d81da680c8041c0300c80c03c0c0d941c0041d1101007003980032031000c004052040c4211021503c2c03031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 830434433 1250 830433183 830433223
    0x6010806040f05120a08040c090b0a05130f020c070602010e0109150c03061e051e150a0302090d0b150405040b2202030312010e0108010203150625150e 66
    0xe030303a6050018030301c03080c1100d45200ea44002c0084c005141d000e4001e4215135074554040d482c090400d014040050b131301c016506840c00410301604d846203c100810b0398400d031090b0b600103508000410050000381111887c162000c40c8000c4011000319401040307594550080c458034100030915402c1345c00d8000000d1204c5c40d003039111018a101078005210200301400c00184035a80d401d0010040f401070002c205015110002c140020301d01052841081d070f481008000119041001103014210740144011012401040d0104481c0c0709030111050400041c00e006030030005403400c03403c903c000b610724141e8035090f0407521105040070301c61648101d030010481e04560701d80c08501903404131a55400001040013085002c0941c800304010062200e54141084081d0b14100d05404002c0301a0490300c0b2070b034010424040c00e4071a140000d410382404985084d641c1d0310f030034510401e180d08859901219400310074a4010301c15940c4100c5903505150030300744201c80c0c1a042440e114541a8107201c2c0503c03503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 830435683 1250 830434433 830434441
    0x1060807060318020a0e1f0302100e0d0c09020d050a09050c0108090709111308030a3009120e030109080d09170403050f0c0f090609040201090f0f150206010806 70
    0x2081d0030510541d03c1030b00d03040111500507004269a105680c00c03000d4030324000303002e001d041802010441c0441c12030141e054901c90440c1c0c001801030351021a040c00300079101c074442c0e41d950380c4d041e01a0a09079100b054007030542d540324401406900003405500b503081c58500010000303400c0303000707000b801540640a8125010140300550707a00c003010700701d54031034881c42c071001ca0b0b46030b038903c140411054400142c940311140180384401e41885070b003016806810502484150580000180c0c41d56880041881c545200280c00350400301c0c2450102c080c01400d0100d84824000c95000000c107c0e01d0076034a0400540091007414241e42d280c010091007140200b2088401c902e0360f80c0220301d2144100504140f6051003040c81402c0c1d002504142d40310707080f000001c0d01110040040c06000481910001d00c98101040081ca9424000348203d010392220000541103a100e00141006802c1c24405a8031442c6c83c0c0703c445080da40c3e40d0050007441503a588090b103800b40001403040c102c41051703009250a6607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 830436933 1250 830435683 830435687
    0x10f0905030c01140d020705011a01051e07151a18010501140d060f06020d02070f1401050c0c0a060c050c180714070609080304030305130206030714040e1006110106080706 75
    0x1000000d1a13038404024840d420300110300380014040140940004958014021100342e030181c21007032070905202003085071090101e5041c00002080d130341c10b05c43d0341c0c482445081c01e4038214040840d1400e240d29140300c1244c80c0c483c0038095210000c080da040103102c5840c1050440f041e90a00540d80419909010002d004111070002c02c4602c0c08040049030465031004004032900280d0051005600240ca54961699041044500404c800700c282c0c0d0303107180ba16007484184580c601040d8100100003c1204000300304101168200b01e000d8020006a96103e400070074089080d50211000d009002a1290030714212018012007007400e9a02045501e42190030303074010307001d81a0710b100c6101c00d012520100b01b440c820300e1070040c007800020340c2c0e0345814a4020b00b11600284425218401107914030301588681083d66842045420100c0b44c051400c801d1480300d001e076910288454035600100701c030411780600c0d8007084070386944559001c0380c00040034a007a165240140c5c0d0099001c00000c200b0f040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 830438183 1250 830436933 830436947
    0x15071b020102190f0b07180b090301090c18060b130603180b0c0306010e0619031a04060b092e3006031e050709020d02190c02010f0905030c01 62
    0x52050044407900890000a0345142c4440fa80c2929000c04140d08001400000110f0303d60104192520880d480101c45030b00b040c0c40828001c000700e81902144002c61520254489440d80b03400081188860340c1c0d0b00041c41a8220600d041440790341085030005551654800340c500085075050702000c1c0d01d0070070340c04500410b80e44004000206c5000d1108020032042c1803600d0003404119061981c0c0d00e400c2002510841d0550411401242d003000ba11281c07072040700c4849940300141c9000700b50314500590340e1246040608145a0240c0340202c000b5030700d2100b600070b250350700003961901c0301c0203256005e102030500514040c14840c0d5042c00600c1ca95403040801003009400500e034403d2000c00300581d1001021203180340a900c0340d407404180180014a50313408501003040000341e0f081080c41d83c0daa40c45040c1c9226644100d500490000d20381c031103d40648000a8141020001c070281c40c6800802c1001e0b01c10040e400300c4c881184c145240c4c1e1090743d0784d1013030340c0d0080d000b49424044900112208 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 830439433 1250 830438183 830438237
    0xf01181a07170f0702070e09030a12060b0d0603061821020a06020307020606030f010e0706050730030e120f0703030f0501291206010f0309020301050708091507 70
    0xd0900c002d070408214030522030203080703da460000a0301d80200041d18000c407541005160b1f030404410005c1c0d13840e0000c21205220000d1400022a009542ca0240909000e07001451099404110722411202990100040780d00511051104c404075444130341c018010490b01500c49290024155103131940d104010810010138412101d0035540da444240481e0015601c210050308400c06102252600b0046015030b410158000c01210210800c0715969200e1031150400b4031078040340040a200318100300c0200840b814640c1d01c0000c040107001c01c89030002001c0320002c0780c81c01b1f9044002008c0021003c2e0391134051400c103854407462205500c04c9801c5501d0803800c00d42c40792910589040e081c09094000d02c56650200c1d90040352161103460011240e80212101c00280074031a15002c02d26409500f000081c02c0c5031680a18210086010305000326000e50150308100500c001d0940c4045211320a014101c240c0c4c0d10f4010760a41c801c0d03011001d80380040001c0e4522144290688041e1000d490 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 830440683 1250 830439433 830439437
    0x60a0906050304290f09060c04091109030f03041a13030f020d050a050d1d18180f0607030b06030f01061d130902010e0a0305070b0706021b0f01181a07 66
    0x100c542c0340705041c920a0b41800304d03130818001240038001044c070228002900030448038040c1c09a483c010740f203000c0c180510300c54104c0154550b0340c42c41a101c0c00c2812569070300c40190036217181c0038410b942c15689500030720070845c41c0080f02040029a0303c0c0b035000d890008019580c4110690703e582c0360007210295150060368003c4500240c40000b500400a140030304d4482c0e809410903400d100301c040c108074001e0904500102c0c412008580b550740c3d05808601c2c5080c02000030113140c407070032400300e41450224007407041c1d80b282d10b0341c1e0041520000341061082020f0b079010f0120303040f108240101400705a03188060814020018081c4c1c3d0300070034000c90701411102c44949155800400038000401109030440c1e0f0315038030000141956030160501400311804e4500340030b040e1a540d100c0740c1da8103030351261004404003c26180c0400805070111103941110b840e10500b20441100c81c40d40701d0946c20032910107036103402190715205860401540c1c900d034000c50041030b01d02c1029203182d032200c0c0c01065101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 830441933 1250 830440683 830440703
    0x41a030709120c0609060504240e0306100f050d080a030c0e04151806061d0406350c1309020a0305190b010602011e0b010c02062205060a0906050304 65
    0x25100700c005032450b15090240703001050a034a480c070080c00d00060340e04040d04000f020402031002002c950b4180d125101101021100ca0b410500c0c1118600709202c941c80d13140c00b8180601c8400145c4403c40015101645420b004040e034400c00c00c812507110b540000c202c51000d00c407004d030702400784d8403e400a02c80c2d420b020b103030310004800280468480c9c0c201076414455900c1705004110451054200600d0800010000b560601030081c00c814030ba07480000f103030400c9641c00d9055032a5070b000701d001021503004d01401c540c180d0040da540d19886940c440c1d100d41c600d07610a02200e030000b40c00c0825000c09032011a10411842c03000b0007a1007075041c2030b03030001c0c4600c100000141d001c02c080319030080d030284640c8070142146440c9a5824042e44000c08580c1000c004007140b14400000c660526401e000c0010079021031001602d200a050380302961101022a9205111032500c6c80840c03094a404411007240361144100710300d900030048507500240001c081480300c03c0c0100002c44d005402524140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 830443183 1250 830441933 830441939
    0x10030f0c0b0c030408060c130b030a0912030b030c030105040c060c03020109080c1c0c0507180902030d11010f05010807050d03110f100f02031e0a02040803031005030c06041a030709 79
    0x907040780e0101118100690000038100a015018804c841d013207000d694070185800340c400d0202c05898038a015950304420000003040300f000b000c0c3d019044a562118003141c1405140e04094014815126254082e000320302c411480b41c90188101071046910544800d07043e0700381501125862942801102550b42c2c1d14600c2021940d0a00900b60207900304004007152441c543c000c140c40f0300c030514040b061041c0c1c81c0040f0002000802d4500980300000508c00018000c0d40408000d40b5107104041d40502400806c48201a884041e1640036000320340280481703460608403000700c900900c508500d0380c01140741800300f4600710008102d201d01038901214024440c031012410040003254800d840d50000c441040c007070446000312250350168800031811071a0141d141c001507014251a2428a042080022071200c50395041e5000f9003100003c0304c0d180d01e002c1214030312407001170051302e210744280c1040c9103c030300d0500120340543d805083d0110241d01003a00400850f08050203180520119502c04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 830444433 1250 830443183 830443199
    0x8013203031312050c030d08010915180c0801152f07180c05121b1e07050115050607150902060d0207060b10020c0d110909030307080601050310030f0c 66
    0x30310b0192036465007602e011441c5281207860201c030041300c54003c3c4c01621418200c0b580015a07a4116078085801060040e242c40781c2125001030358001d01c020883d560302c0d0142c01611613000c0b40441555495104c2d0030390301c1d0140800394040303000310325000818010b0400c01da082c6a03c001e0b01e4001c22100c1c025400e51668a0460510056801c05a080568401c0400d1405894001c50000340201c6c10850700d00013407455001a042802819249408482850724507a80403044c229403a00030f5080c52500d0040c1c410501944a500c10602508c1c03039820020410b9406c00084240003c03500000c1105182c4111692003190b0b901010144190385a0381d41d07200c20260300c556004160000c0c16141c01650742415140c0f0700d048441048846006681008420100b00e40010720301000030422501010f601c81c1c40e01c1c1000720102d540c1c0c642d03504085a24140103d40c0c40001c0510302070807e540b075030031140d600c00004590a0000300c03440001a99146410000702d50b00c0010301405500540b0424501c41d203400d0b807 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 830445683 1250 830444433 830444467
    0x8211e12070314010303140a0212030702030405010207090e0618010b130b130e03160804050a06030c0f0512040213140c0405040b0126090a0f06020a0801320303 70
    0x451480d100030404001c9002c0d07051044040f80f400d000c4404109505546000746480401020080c414000164248076035000b0080340c40c1807000400f54903500d141c0100025203d40261050902501c01d9620200c0c10310310501034491840034220040005540d010074100340500c00c079080a2603075607100c0c03008003c0c0c1c82c2c01070403141106407194046103160803103040c04500310712000c08054251030031030300103460180481142c1030000c0081c50b04401c502c030b9040030341141c499540002e40c4603140c0a00018407030b4040c0c01241c80d01c5480d480d01c05090780e00b840c05032050f10403005d08400415000d00010014680740c140300d48144460840000da2031620003000e09110341c00daa000318514004030b805c10082c50940609140d0312002c0c6005542e09180b8054070351003190108a902c58400e44034001b440c4c030b400402600c2041e541040c0002d070042483d081c000000d5000e00840390001c0e2081002007000758045a00d000c0780d18900e4800081040c20b0340e40480381b180000c000c02d500d40001c204285813007081501e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 830446933 1250 830445683 830445697
    0x120a090806010305070e0c090a050432040b010807060503060112020d050708100f080a0b04050f0a150b010c0201020a020d0323091c0309120c09110c0708211e 69
    0x505c920390411100d0080f013100200f0140c2c03519020000b1090035203851281d50125601907a01003104850748500b203040a00f8101c00844025411000c06000306132018150b00490090080f2911640c8914a081c1c80d0708040c054180071810410128010b54481ca020056190740004010304002402d00d001d0203507002031710388030000b43d07100f030501c01c1c0c80e64405202c20040c805000300001c481c3c81c000c40ba83d105e07403401002424040c141c100150500c1b00030b001504246001d6800c3d038a031070306103240c0105003804201c8620a0304d0f01d4405204c5042d4003c0f901c0807070168058009001407042942000750300005100c0072400c00c08012000c911403107040d02c00c090349282e000e44490b04c41c5805020720000a013503000c201c942c00c0070f48406c13101080d0480c0032a029035070b0b59401e80308810340030b0030040c03c20862a881101c0a42ca000345000300c5000e15405072501c0091003056400b1190303254500d5a54410780040ca450580c44039540380138441c0e42c40c0043c4801030541201e040fa1b5040740000002301d801070a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 830448183 1250 830446933 830446943
    0xb0c010219210c0f12020702121b09130b1b0409061706041a0c0408060f0103030809390607050f10060f060806190305010e0f0609120a0908060103 64
    0x246246840b024403042807018482d184042103d81005100205003181e208013907014811800c404040c1a5001c1e012604802d40107880340c170034401c0c1c522a09035a0795850126440b4105824200a00352814902e803500941185d034440241e0365490b141c082840d5405494928900b060604ca0340349400d441014000409420700000380c40c5142c000e008042c590307200c0721b00c40c07c0d404c00010040081c0b00142c5400076000301c48600c80582c1d0358a030300f0103003d200d180c2161455102e030900700032464000c801682c0c103a034400e1f56100101e40350a014242d4a6031400360f80950411014080d2000945901d1481c50540b4101c450171030710203040d40443c800d42d218030803d56442c0c000f80d6403511501410400da00035060b00d0a42040078918040c01040d00c524079004000c1000000001710364259507400c078080826048100300e00c40d44d952441e166000b0100c03801040c23420300440ba0354031102a07010404034030a1900c2c8004d404080c4081c00600324503444041c00b0014810f0a0b07101044410081285902842c410303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 830449433 1250 830448183 830448197
    0xc1207180324050c0f250b01031101080f0c0a090509160801120f020103021c020c0d030f0903200f060705031b0403260f0a02030301031502070c0b0c010219 68
    0x9402c0400880b490720415811505003800d002c4074000e000c040f944203c0080c0251030b107881200306a40004011160fa646c00e0340f05209000c4180f14400744004c0c120b0f84201341c50002d180450005584841080f140010034940b40380018014a05c284001c010503071262030301214141e101c0c7c00040d22400f0070340e00c5104600c9180c0d5146100b40d00310088602420300c0c402c2d015903074000d503603580c80349001503c0000d04140d008907c040c900d0080c0031001060600c8a00195251a1080c488941d20742a403003068002a0070a030881c00b0740364503440344581003038140d560116501ca880794501c041c865441010a02c0d807041c4000c4034402e41062103824000c81c020350b0740a0717990501180da007140902078030740d012070403030100410800a0100c1104488500346420314074105400310701c141c1524028109480720302d10300010085041980800114140c0348500d001b85c180c0000d0070040c804a0090040003400c115909005100d48903109010b000038088134800540303040d5009041d0100000400f44880100b2a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 830450683 1250 830449433 830449463
    0x120b060a02280b0103061a0907030b151806070507050d151b050d05060301091b23090414011e060e0610020c120a0204320c12071803 58
    0x942c000389560004845041d1001d4010348802c420303010107110040810369101c00d250401d0910b0740c85200c84243c000c0203032074245813400c800b40240c40340b91113042c450503015100c003c0d40707206402541d505c14480c0c01d8400101a0482c2401266480039205840500c01c91030005620341c0d0703001c5250302107840b500160800000c9001e20030291003e59103241c00000e200742142d425a41d22a003595203400d82d441002c640e640340c003008a8014656810090301c9102e00c082410a1400b0382000d05045a001c0c3c07549104190802d1615403c00300c15101c000d83c0140e408010801103407900300c40c00d400c0f40c514000003c41a561032240e40703141c008a00300c0600c89450703020070840282007860b51580a1740607523480401d01d420080c008e44880e0001880c2e886000300c1084584214000c002c006849a030187c010003502c41ca400c5a40e4400109c50402032044080920010f4102d003804038443c010b6180112050501649150350b94500d031008007502c080040046600c0704038200070714208000d5001d5180c1c5100245 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 830451933 1250 830450683 830450713
    0x1503020a0b04031a04060b090c1b01020309071e2706080604051c021f0f05091207020915041404050105090309221b030e0118080703120b060a02 63
    0x540741d0041110709024041000420412030440490182c211021016581d0f1031802c40300510107030b44055044021042040800e021040081c40d000081c4038281c03249140c04400c041c20307480200d80041d82c1d508001402c00c0700c40c80174126524010081d003403140d2516111034001e440a8908080445801d02440320047c031014548a0880034000f850090f00d500c3c541521000d0f0b89916100b80466959030301c0070410b6000e40309200903068043c0b00354041e41d0a140005542018003603018080c10828079000114400820025085540620048400b42042d0030754003002410718005082618600b0100c0f5042d07400e5480d841001000d04074803c2201c881d00701410100e00711000100203452981c000c12401c55169203001a204d4900d426a07110140b03400c0c03012460020b001d000640b1100d24800d918440c0c051605134206007103522584000704046001c1018030f01030307983d0014015000071810410140070900c02e0314000700140ac0c00b0408a41401010041a80c551001e003000c00117030030a8006e810000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 830453183 1250 830451933 830451949
    0x204180f06060815090714070311060c03012324181210021b0d0f080610140d1d03070209060d08030105210610090e1f0902060c01150302 60
    0x20070640fa10805910b4840c0f44000800c00410b005071051004100203010148180c24405c2c0802220001d903449910a18019024800e001000c1d05a4011000050100014041a24100d8021940705442d11012405040b00281028221504904456110041540e6003001c040d10080d218510943e60300410140d44120503140c011944520712142000d040741d00e000803134a00c001070614005030f40700e48100b0000504107000315180e80500a03403000d03212468001d021a40d0986003600e80340d00c269202c5040001c000480d00c041c1021403000c1d040c154502d100c020251800b40d503c4c2400092060040340541c0810400802610b030720790000505100714100f085109030404029140c0b0382d1102034a42e03500c00c00d030005000302c0380691580075090300407110203001140040805400c2e40c0c05801c000b903071148001c1660041c0c0111a060023401d843c0004009441074219031708144007110001c83c0003854001d41104541039a20400501034504044030a104034a00200810102c0c11800d10f181706000c412 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 830454433 1250 830453183 830453189
    0xc020607061404141605151c11130b0a0f1b0611090102010b030703050a020906060d23070c0246030201021e030301090b0a09050702160f06020a12030204180f06 70
    0x1a001c000d401b0005030725183c030610300c450190000103031a4404508250b074003821070203400c10f0141c2800d07004441402440010320103103540b419000145034568141000e544038540c40300300090a4029031651a92043e0412101740150104980e010169910750800303071703001c154002220b4140010205d80c5503809216040102c00117401030f040302407a5441d0f882d01c904151001900802c403450008407556110390403100d040391101020061f81e280004586444590b8104072074440300d110010900f201c0c0210b07120594158000c18003240f400030841c04409041c609043d001c3d440039080d810066a20300c09401ca400c10070b0301c20382004000c4c40c1d400024078080b07240105d00c2c52020000d41060781d8540200489056400040002c28074000010118a200d81c5030b0380716141c07180c0f03000280100940e000c02d0b0504a209001031050805844680106078280140b0900000d41c1c00440c030480062000d440c140303504c04007403c1c014103103a515802d00d483c900c040c000322552255565085d0035524102d104500103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 830455683 1250 830454433 830454463
    0x9160305100f180e030f0d050a0b0904030e191d06041b05030c0403080720040216150b0307120314180609031011040807050f010c02060706140414 64
    0x441c5203040022084600075015440155540707508101d0a442142c1000401c070003900101c0f07070b035030303c0600c1e91294582041c0c6800741d00500f44404522081c595024104502400a00740300a80d15156015544001341c0c04216070000d20110901d51846d81c1910301100500c04003900c000283c1091403c2c0c0b404900040102e4843c030b1502101c0b81e11158001c0704003007140311608080ba03803034581c0890520300340190b03072004109180019071002040346007584035041a4154080c01603181c40d290030031040c2d01442401c4041c2002500001c00416440c107000304050400e01000154164144042424810345801a8ac8400c016100304400c041d403048000c04802c40034840d19003032140082000c00e0407064102100d02c204400305642e021030303034144240152080b021000300200701300311004200320b070007a00c00c4a00a0043c100002454107003a40b074016100300c140e40354032141d00940e081000642000000ba07490740d65a0280d080300307101b290186405217024001e010020341254035202d1911518140c8008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 830456933 1250 830455683 830455711
    0x1e061e060914040b0609091912020d0903020303180d0c0803091009030f080f0c06100f060e0a2106180c091418030904050a1b02120706020a0c0209160305 67
    0x408a140b0b184c0d142c0c0c100b48100e03091b00c1c80c0d41f0780c03840c442e02d000b0071094080d4109140b510990f0400051409c40201880355030240e4a8903c00740b2400d035040d55041c84065099001007020340c5a004400c8200c0c168101c004003035095085550f140d0b03880ba080160401c00d40c0d0340c400948925076203421401000c40d2011490301c0728109045a0b25000e04519110300108012804240740809540c0e01050b00c1161251504968087c5080151081009002d1040c4a11100041004200648292a400c0c1020400b806c1a0300040ca4080260030110000b184c01500e806820310280004555000c0d20000031104805c403600044a401c1c00c48a84405a009108040c500703921411041c40e143c4c4001d030700c800d40c030315042c0c8241c1c840c00301c2908510503940b11640c06450103042041c0a040c0e40e01000703e09285204940400c0d00a04051fa540e80d42881ca0004841c014000400052225002014204141d1410030003000c1d01d9404070b6034074002650b4041d0403944207110340c00d4080c0d051082030b5101c0c4d82500c0141c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 830458183 1250 830456933 830456941
    0x1906020304020429150c0d0206040c1a040e090a050706031a0904050a020d050f010c091d0f0103110d0210031d0c0f01270b0a09121e061e060914 63
    0x240c2c4042d4098854001c5e031226298083d0f8038151019114001c0d403c6054522800b04204c00030345a04049a084400320155000440c1e0503000e910f20120384808203031b80d10b29180c02d08090b01021800105802a24071070403038403000250042c0034450052080d600c000c40d4102c601a190900031651040c084d004130007020410011802c0040c51076032a0340c0680d0460f16a403036a04100e414410b90120490f61036017007440508100303900044200031544504405508201e050540400004042d10850304c0138060400510105020f80100705d0080002405a0810002903010410b84080710140c6404255190000c4400200b0142e04e034200c0304c4180090040d039080c0030700180fa80103820b80b02e241084004c40030310a11041a1140070721340c2c1c451102800400f60740ba1031405d0380f540b00c510180006240c040c40024a40e01542008031010b50207220840e4440e921801c0b091043c4803001e090301ca49403100e0f031a08a459641803a07460580b8076520208150b4185040c080075182c1c81c2503009000c0149100304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 830459433 1250 830458183 830458241
    0x906050d020d020415031403070b132d0b0c030a1410060513030204050112050d030501060f03050a0b090a06060f080f16020f0111180609030a060b0319060203040204 72
    0x94102c0342d04490009001c6a004805424a940c1c0d03040285030000803030440e001060004040d049142c4901501c40495039520a14140b107a20b01000030420800c000c0d01050b000c0702c1d94020040c0d00140141902c440001e9140c42000240560344400040c000000b8004420329602070140b142d018803045c050a41000700068044440301c1c8902c0e4100000440d0002209000118540055400600c00e000740d5858003905896038240d1a030895040c45460407000003140a400b80360704a404603202c83c0404c241481c01940a400c00510154006549001c840c034143c0d110b070045401002a04030000b00603041a10140c006250b445103003080c40003182c100807480158a960300c0d8803070700005c0180700003443c00c10144c1c034100814500c841c3d01d50920141000e0302809074041c10140030380500803040182040c09000745072241d0640a070301034010607403c20202c3c811350003480c42c418010b0102c440c58074003e9850810440504d100b2291260004180015440c1030300420003060b940c00c600c0a00350240d2645 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 830460683 1250 830459433 830459449
    0xa0501031a090c0706050405060f01050a03030903150b18070807020106230d1e020406092901231c1e0e120c0a020901170309010e03030f12010906050d02 67
    0xd10072068000007071460500e800c10344d5500c690060042c0410f04007480e05903150070040b19201085028640006280d01d00103000404491b0151079407065682541c45042008102030000c940c4c160b210f00c0040c184e0b8540e510300245d0303424845d125884608200c00c0c0240076201c007818000840e81400810701281d440090100c0c20398002501032100c50081c1c8011031340100d0940750140c400d2b8450f00704480702400c90605808164400c407420000780707445540c2e1804950149405034020f50300050505203000441d90030a070007280504101144083c4240c000308064844410841c00c52000301d00c0280d0030781c42c5007400030564108082840360034044d03041258207035203050702d0030030b0310f5100c841c00c1e010f4041c140a00c024040d07103654126600c094100201d5983e40c1e00729000ca004018000001401e00c0300c440c40e400103ea407003800b4511700b00f046001115480c280b521402c1d07250108000c0d00315a1441a001001c050030391803420125503161510407022900d10b0790080d400340610071030850040c3d4410344 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 830461933 1250 830460683 830460731
    0x70e0603010503120d0608010e0607030c02070e0f06120304060e0906040b011403040c0803040906080f210a050c010c170702060c030403030f090c0b040f23090c0c030403110a050103 79
    0x24980c5c071791440200035405400180d01103091546040401b1a2610b404100c0900c01c0c2040e4805004461140408a90300c8105110308540509488042031032a020001010b4021030000c010349994009924101e00b998002d40c40540400c03408400b02c2089e0a10880c0e15601941c21242003080855840004c0c0c40744001b58803503201503100000090801030707485a8a17015007410b1049035116138507209a2001010715000301c41140c03185c0c10030340b50310140c0011034143d860310410003905d04540f00d5180001c07a820051503002803003010b010341e00402034244101c00c0120000e03680c2800858980000900b80c00d40a40700f0011501300c84d0410504000c1581160340007641460001040c064140b801c0b001402422002448040a114005007008901015006480c482010703800b00c1c66950300700140a408100010700401e4036000c0d01740d082d103000c500e5580c4c81081800c0e05440d00e500b1381c0090b410342d803080d001201d890300c2e4800d04002c581080000c0c070010b0310003800c7c10440d06022160f41d02303400c1204a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 830463183 1250 830461933 830461963
    0x20606131802100c06110306040f050702120c03040902032514030f070e1309050606060c0a0b040302070506031f0b120a0b0a0b0705070503010c050a0504121a0708070e0603010503 78
    0x3558032035984034483c0030300f110b03410282c200140b046ca03a0307000c000c1e540241c40c02481541000401000c241003442114010340294000748821140038565568540044180381d80c28001800000780441081c002075211fa50001e664201a800d400d000b08240708490b81d5860400a00191a481e62240001225005813500001c0b200c5941c80e124110b400c2e030140000c4c80c0d04501a806180c003004810f0f000100d0891003603082d15500d80c3c90740180b1890b030041ca0103250859200014200c00708001c50a60740e0051b0007441600c1782c071078885000c42c0199005030f600070403513442c096099010640801024028000c03d200151504001c5d402030040c10402134280c5042075540d001c410226510b0044100007041e240c00003d89030a05801e001da140d0101e0301c101030082d401d12125007000c61003803086480d00456605c03554103150425468a503044050b103001c036401000b4491030007110341c840e00c80340e21031505542c400c400751621410003400c0c100040c41007400750b0390910040c0324582d03000c00d07030300c030b07405642 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 830464433 1250 830463183 830463199
    0xc0e060406080916090c081605070201030f14010b130509010b0318150c09120715053601020d09080304182a0f170f25020606131802 58
    0x83e0200c513040c1080e03410f41c0b420441c080003000410040c143c00031403004c451303034466054595900210070020070101140c240000c004102400041d0b00a500c1651454030079800012000100f035145143d2800031380000b1800340001c6441e0504220403a200c80183c0307419240c1d02c3e10b81d458980a08624000913083c0c0e0308030300314100c04200e01e01013080007110415100c10011018100440100c403d039010044190080c0541030328104042000960581254032440d5151071a45607a070048a09401c0039500c00d460405c04044090700c8452980c0b1441e41102001d41310640505840001e803901e5a052801014094044010450a2000701c26202100c2814100c4a09100300d0741c4d40d0001020100010f8000281840c59a4446c1000d030001c40c0c83c000b030780c2e2180528060b0070042901c051362614603044011034000b00080c10281c006078819000b440961300c801712485000b90404803004240f40801c0103034000c0381040f19900c0c20440c80f0361145038040c0c1c1044903940a001a102290b20740201074016414 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 830465683 1250 830464433 830464441
    0xc0812090f01030c260105040b060702100804300816020a080a020c06040e0403260105010311041502010b150a172e0501030c11150a1b050c010c0e06040608 68
    0x39088400302d0914983c805c94224070700c1d105140c012403084c000c07140a00c0c944100ba01d170038217154080390f11080d00240721000031100303244103e4044400500455440521119061071041d03040d10b0b9a10420f410444110703240d03841100100701c000010301d814910100c1c060b141c0707103194001c0f840c503a2568010b14100c1c1d0750b10f0032034810380ca06007010303524a4006000040004940c11510745c520f00441c401c4da1800400d02d005402c0040c0909202003000d0481541c1004004640c0240d100040c900b00c0d405441e41441c1c2d985030a0b00031041c24401b01f00141c0d4482c0072680245c0303007200b08030750602d0081403580c0c18018a900020001d68003082540004407541021440f05400c503807031030b0b4005a051207207003101e00382c41c0d40a25901c005482658080ba0070600d130701c00d0301d5004000d844521003080008007644421034400c41d0180c0c0000c1c3c00001a295660041d800c01960300400b500981e805071038807076441402d040e02c01e0842e02d102c0000f6040000301409250250b86420480703045520501c2d0000c8140c03030b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 830466933 1250 830465683 830465687
    0x150501050f19120f0510050c2b0504050303070e060a0507060e0a1704090f1112060d140a0201140708030f04080d06120209060f09011203020115030c0812090f01030c 72
    0x2c0703e40000d00e0000c0018650010040100000444548a8410303240345585031030102083d1001038901a1711401c041c07002d60354443c07200c034520b1442e003020280c101c108000c06c3c01c50300840740305850036a0303203070000002c00c410142c0080f0a03000002c0192a9546400c210810007015401600e8001b00047c2d01c0f40801b115040081003003000d40d81d08000541841c440c511004280c0340d21600c1a58845820030201002a008500c02c1c01102c40c01c0c01c14903450421315004100a01c44000c1a46902869149010f0045083c07100c5032800940c028005140307940c040e00002d041c03480b042040d02c5520310308102200000e40c0e1941944d4020701d0b02c0c160102681c0392481d1003a2140610003495503440e20340400001c043c03a6852019295600030307140d8a16646800c800e014a107803560b07000c1c07500004107400410048030400c480c184002e000c0d2000003501121030f040d43e4940e0129500a0701c00300c10500e01071003140b0b03013401150500001c0c060340c10b103004030850114203055075440040381410755840300801e0b568 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 830468183 1250 830466933 830466979
    0x203030a021810020d08100305030912100608030301062d08040816050102091003230a0b03010f0e1614090604140a0905010b01020a0308040f02040b0607080304150501050f 75
    0x2c10040c24010410901c2c1d070001d41d941040400c880001e03810102240c51800070600507020343c1d8000014615011a2006216a03d0142941182148900c0c0c000f112a16500d228150181141c0c2001d0365032035140a10091411548500e4104c0091004841c41c0346900ca00c500c4111510380c9080c9074425640c0c41c01c01e509280100e00340748070480c1d0000c00a8040140643c003c10184608582c500519201c52100b2402c5402c54170446104006451200510480490f601540541c200c0d2011031904200b0f00440c3c00d54549000b20901551103400041c5400400c0c00140030885c5081c4030f14551341d141982c2c17192040f94044900e400b45100401081503078a41c2d420403a04440d40760089005802e0440c0c10000600d15044291460352a1480740b5a0661002c503103c0c06540d0540d66a840b15141c50702d95000001044d541242c1c41952815102501d440b044040c003c1780f401525503d4a81c0341500340181c012421003854030b109031401c4010b10495807240d043d500c204a01b41d901700b0100c00e00050450f100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 830469433 1250 830468183 830468227
    0x151b090602030a171e1608011a030703150506180906040209130b041104030b0f010b0c0c040203090a0b040503041e0303080a021617090312032205071a040815070203030a02 75
    0x1403030070b4000c0003c2e00d000c0c0f034204c544801c8199144407d44c0e81c5d8010381d4910001010350201c0b4040204041030b086e40c442e400c00e10710201003495006000f6900d80005800341e000c2c02d145464040c03007501300409440c001000c0c40d8828002c0c2c40035840c0c07600b0440050100009442499440d6540e421103201984a90780000c1620200f26a40c40d603441d10b0b414a8100401d044518190150700d800000c540100c4000550309500110f20041003031001140400010b500004c0607120326115031841c20300450041c14803d40101d002c0e00107035965504040719140d44c003044a0441c1c10070740d04544104002603021220962020f03042000588030203120704500ca80c407800c0301c005004c001e03011101c84803204c210001090450700c2102100c80d8000e0a100d820441d000071541c0002c0302403070490b840b60200c43c408000c0507040c896001d0f110703040e840b200200e00c08202c1c3c1103009403021000c5028020000100b240f5110101602c07a10141c13880d192100039070b01c2c030004103180c6909402051109004820310401c20740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 830470683 1250 830469433 830469481
    0x120e0d48150518010b0d021003091a0f06130212060103020d09050f0106050f0d050d0f05041a0315010318170913150609120f151b090602030a17 63
    0x40d42c03c000ca80b081d900200007103c0d00f4030b5440d04602c96081d10388032070039480e2a60f020780b0300d1054414407141070b0b00400f00164280c54000110b80580c000e6201010054071038205202c620f640340c106101405076004444041030360306c510400c01c940300181d06103a1545d01503000d19002d40da030480d500c89078014040700c0400502e94800c24101085a00064010300165003040d108000d03000740d61410890001101403010305180c200400c1c3d8940b80b84640402d070702d2070300c450800c985060741d1116007499565904103e94078440d004400d0040310743d000c02807500b000f0800d00c0c05001d0000004284001c03000c2c00700008010500881314071001304090310554000f01c43c001c00c02500034001c1c5611001500711004899032000c000c0401003903240c040c00403103003515001c2c1203d002c41207660340d5950107140300e1401921200183c9280c4540260107014011141000c01380740b40c0c0729048040c0c040c01d0080c194002c0707001d54000780845a4550361002c0c417072845101001c4c941c1065140e601c00820103101a400402c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 830471933 1250 830470683 830470691
    0xd082a011401051903020a0306051b160b07031b11011d0102031807081e010902040903020a0209010f230604050402070803010f060201090f03120e0d4815 67
    0x94014a0450701074101c80c000d803048400050300d20105455003555000080d80094803d005001050581c0d02541c2d10180d0510b00d0403034443c0240e800d0090f5041010341d6030720700b80c0c180000d104000007a00b41c1a00f01280307003010f024580d04149540880240403d0007002c03c030301e07003121110307901c425000500f00380301502d080703a010300d248601503010307600841d0788810610300040360300c0609200065540c111071112010b000c8402e4403450640c0b8010319100b4541c5070b992604081800740e501e61190f0b503006842a001404401c0052043c010710550590150710340c030390007800804c40701d05180751004240081c14001c908025140b0001a028011600324a4104c6e102040e00405c0010030700065050b80d0b481e581200200d41c0d110340032400d95090100040060b1206101d050019001c4c540b13000c0100c9401202183c1281c0400f030603880c1102c030b00003003400a80050207060400c09603200703032115124202403161400549001d901c8a0003441075182210707042c10504602440750300c40042100170072001d403c0c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 830473183 1250 830471933 830471951
    0x19030c031206092a0906050d02190e01080f070e1908011104031502180609060c0d08070f02190f0302030d060b070b09061302042f040807050d082a01 65
    0x14000142c2060141e8000321084c00c000140b103284201544541d6264041d0358146082290b07035400441c80291259020700901405204500d074184100c2e0303565650034a40e00c0b05070001400448040c10035010680c42400707002c291640301050b01084030007542c503a180c0e401c0c0c2000004401000b580401803070b501e400c40080c0c12004079001041168001d1043c4040f80440c02198022841261200100b48501401984003803c256000d0011628014035560401a40030440c41c140b2280d81ea5000025694104008810b41c008516400c140640d100078401c0f100d00c40b41c00b0500d542611405484c90b910b070034070003040510030403c440040900240070302241d81e40720b81000c06500106011600d20111400080540500040861007014001105002c1450300e0f024080148007150aa5200b00c0b19030b082c0200140e500070701c1f0203150501d880202c0d903ca2503c1003c0341898040d41140b03202c0c0944c00c02e1400030520320b806032003060300301109040040c40010400070303c055010b1854011542000206 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 830474433 1250 830473183 830473199
    0xb1b0106030b0412050a050405041a03030705010f110c0709180f0506010602101109121618050a20180a0e0f01350a081201090e19030c031206 62
    0x510f000d40c1c821112150000c428150075030b928005c0003021400920248030411061405402c12140407414004080880c060a0f01080c115032000710140c40f00c0c5c1d154207020043c015103100d0041483c4808030000e041034000c104198031203201d0310070445647d80b2450085140c900c0904545040c03171707000304550030090390703131406039159239003480341001602501010007002450760080d030288021003040c56103460800c5081022a0614403181c4030307103104411825241c440c0c1c40c5080d1000e00b0b070f81480c0e00441c00b84680e0340e03001d0f40c0006059540c09420300c40c1486410054901c00d5550f83d0622007850707190044614403a02819083d018182e20511070f90f40000c0d9040f90f031004501908404076025030583c0c840243d240380003c00401116044c002010890341e4440c82c10366011510b0407942610404091501c401203070b5044250805c4400301d41c1d40040210944d10311568814103040006400c000c1c1c0c1c1300d46000c44045045c0c0f4064240141245081c0800d80700c1c05400124800081c010401d0540760461 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 830475683 1250 830474433 830474453
    0x1b130e0c1912051012020111070e01080a050f01270510060308091c0b1803190314070207050607170904090506090c0a08030301090b0607060603060507080c070b010b1b010603 76
    0x558900c3d01c0c1402052940c01e06115080580b03c400300c0b091144c0080e54011912200349002401190140076808980320501544850091181600404140415003030940c2019900e20010700140c0c9071054041c0c0542d42991090311030040440000100203031070810790b040c2079100c040d5241c0245046008400c2140e140058104c48200762041250f84041d01c451101800c40e2180c040e0055144000241500c6003086410002c0064034007943d00703008090740700b0411014011034050100ea11410070300352880380c0c400400c1e84112140b006054061414020521610030f000001d400d00307030407944400906408030115041424081c004000d5009035003441916400d068039410030328000c54100030420300c1c007900300c90199114100034501d9a460541108020010742c10201c1c2c0101d400e001020200b002482140000c40c01040d006c52a0701e80302c4802488460014156450b5003001e03ca56004a010404001d0540d100000455640d0040c0d150400f12a40e034554024555801c0c402d01204119000c09 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 830476933 1250 830475683 830475707
    0x909020a02031b06040203150705092e02070e010b07020604030210080910020909150d0203031204050610120b0a110d0605030c010f0c0609020d0206070501051b130e0c19 74
    0x400300f02645400002d458481105640207581070380b00c3d81c01e4211522942c03280d41c1d005212420039034034069004010070380304106100c1340c04282840200500c6811008049003030070520741c2c800f84c41c44c941822000100d600041c0078038444120003056510071512828126000740d030b0020021a05000300380b20046c440350741291501068004c110000d00e9400d61802a203040300d0005200444684d250070b002c0083c2e24541b40381980c0168003012510141e14140021300b0284040f80102c0182d01c0c260908a1402030042c100200d0b40305213080c10030000d03004520000ba020b0380411a0800b0781c44a41441014182148082000c03000004052462502c0c0b40c3c0800704644041d010383e54205030743c20055509082c000000008203003c1d080c003500055195204400440c4010132000b40c031202da4005c62450740007400c04a400f40e44d5441400340c0c5002c0c0207480890044100708030352401c03002e1000c10700b544640c1e100300c00c490031686003ca0b1030802c000f01030750342c0ca494071403000c5052160f01000422150b044a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 830478183 1250 830476933 830476957
    0x1c0c0330030b0a140315011e21081b16090b180f070c1205071a0c0d150902070602032208040513020c01050711070b030f0114010909020a0203 62
    0x101103805828080d001c1c166000030020000407205141840c84a00c8418811080b41d041c06021501c610392a14003900702c3c06004402c884490f0002c1c1c0e292034842c0c0012640000754032038440201e00082005c40075855010b284c0c8200030329101c00d0503504d186100902c0d00d490140c5405603440c9042e60140c00383c01c0f0022504e1008080c082c079100307641808801e07900b42852808a4400d1000115403140d030794035441c1c100c403051400aa0401807074541001440380c1c1480390340014400a0981e00344a8003240040780d4807a20540f01c0000c1c2445003202130f842c413481d4103a010003521540003581c2c0c2003807000900010f2014003015503580c1c03040d10f4132000a510440781b110405200280c440b05074103d400390f40704440d900042440c50701e420601041803d0b0f04002014804a03001c0140070702608081c007071306004a0854032680f105100858200b424070b40f080e0003800d89600d05004215002c00f007084050b0464048041c010001401007004941007103864100c03188031400080d6810f0003960000042251007544 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 830479433 1250 830478183 830478263
    0x6011806270905120703091d071d030c030a050a05010c0504080307060209040906020c0105010317070203060f070c0c060908070f03020105070b07110703080711010305061c0c03 77
    0xa01400361540364011070a2400d031040c6003088821000d0394020500240110200c40d080000c01100c507019034003d03003003140003c44200342003200c1070009542c510501002d00282e410f914203048001c02c5c1821040203404200c0540a0203a140c0e14140018003a4050203425295038031b41504105aa81e025144200d6680d8649143c0103411031140040d034082d40c2100c4040c40c0713400710984403040a90000007040ba805951902c004000800e076100030030305600800004203c030341c0341d4101071030031000840c0801c039400f10401812006039008101142d220003200c0d060f14140e1100e801c2160400d46025005140b10b0389072002007201c0b41c01c05441130881d00e0480072038011a4403241280c1d0b0f03407001480001e001c50820720402d80081c801c0c8580d80d80c0143c0920307107139110300c101c4090103260a4559100b501ea0000000380e810074004032900074100403000f800e01344070303a04220010581603180c00e190030b0110401d8203850000c00c22884100b0b00103681191000c0740c00404100c402c82c052054001c1000c1410b04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 830480683 1250 830479433 830479439
    0x12050c030a0b13050304090c020a02152a030f070305070516050112051b180a0e0603030301031401090206030103120e010305090705060f090a06030b01180e01062006011806 75
    0x10781c84180652207400c032100c0f0303200d440e01100d0b142c407039503003c50b1103000030300020070320503000d20401d240f0904603802081d8041450060110034a18640e071500b80c00c1c0104400c440c072041d200000d90031228105021444500c08400040c218090701043c160310b44000a072080c14540c0c818040e0800034080c6c0282c42c19604402c1a0320700c08403161182c603010070700503c960000207909900042c2c3c031401b800600b00080e60080c03012891503000520000da10b003540b00c0c41044034144050000060080c6008034030460034007100190b81c07800f0510001707011100c25401c0182c0c40d582134001e03c12681d80600020745a58680c5004102e5004800020002418229209503603610900070389001d40121005801000c1c01d1400344a41c561015042010304082004508942e0f00d682d40c0d28001041960380014290040708001480088620744041102d03e2150382402001c00210007141100e01c9400c108001e4013505240c10000c840c0d520303164107103005202c0005841c40000c80c081119260b0b100c0100f0095071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 830481933 1250 830480683 830480689
    0x1080106121107032601030302060a0b03010e0a03020708070b0301080c10020a0602070b0708060d0c0e0720010608010b12060127020a020c030105130302120f070b01090f0f0506010518130612050c 85
    0x7030300f41f20140059000c5004a4409400b540c00b40108100c05030020600b0b04c0400005850039100f81e8080b00168012042084450707400e0010703030064201e0038800c03071955241a10300e030740e01c403011504d10f0302c124502d210f1880300d00e0013000b00400d807962000c0190340b1441c0d181010000e100c4120380c20360216603408002019450561101166a039000c5008400f1b01e003054200d6291080080580040c031400e50014410000e40c000c00340d0f00c1040c05000851040d0a169545003540c40101e000c1e2b014000a0080c0102d410001c940c03181511035116050680e107451030440c076504c0c091044000e40b45031000031072a4250f54082440020780600350000d0145844181054451070442d140140040c2c100a80d0021100c20600040140314211480cbc14100384194503080e03d20b00703081e4042d0b690316030f84903041880000c8900404034840c648030030401c41498070b900041c0051103014043c1ca8a0300c0c044908c0002685d50a00c0034182581000c0200102e603140d00c48a156540840401d0302ca074401e010000807249 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 830483183 1250 830481933 830482007
    0x201140702011410030f12030e1002031509040c03110613060c0203161409060622080f030403030f0e0d0b0c090114190807090e07090519050108010612110703 69
    0x2a07015800010140c51b0341c40d403080d4030f6426400c0c0010141c44010b1000d200400f0056031008440c10600107a0701c2c144032100054242d9604000c4d400b80920b8000c01010841c4200719008a90308000c005c2c80450100c40043c40b9486030044c4034140c075071409800b2071703815400034640c10036920a82c225140507582034440600031560344222403041025650b508128204002d140c1d03006a03000e02200c1c200000820340e440381c01ca1107026070002140140e400c200300102000003000400309400a1403409040d514020614501c1495241c103100c51000742c180c032a21040740c045142504005040c01c14101010708075a40c1d400001e000f4002990541181418440401264842c441c151241804081c5d510070580341040000c00b40404c0c460070080005101e080503503041d2084c0b0041c0d403928151410301c03082201d01c440482140c0052400750b20184141e0340c02143d000e040d05d0302410140c988034481e5001401070725503240c00c44070700e102c00f060180415400c01014246080b01c040c45154500300460420a10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 830484433 1250 830483183 830483189
    0x10140a09110d0204060506030c07030807050a050405040b03030705100c180b1602120303010f03030f0e0306010e090a05100c1116031b0305010c0822031e0201140702011410 75
    0x70380c0c54405084070302e4482d042184030361000d4004030300107a036040010200d8104075206150003900140d10002c00d80c0c4204819441803207814140c0c1040100e0000520354011030060500441d958505803516940c02c000b1703100c030141d200c0b04550350440041102c0d80602004800b034804608240d44030050307110002108010381e0348403041d007810f00100c401481807110f0740003416038104241c1e240525100100313000450203444152140d8540c4c2d03256203801000c080307001140b0000c2050f40c101213525594080b45450448100646500700b0b500c4014078182054400d40004101e0b00c60440c12490a8450ba0040044803810b900d440803009001d1100a8844209082a00c10200c07142030500000d0140d180b01c403080c0c1c0d100703070140c00d20341c3d101e035103417400c4524941403080802c100400304031014031814078410170307265900e038001941d203119940507024400c003801800c1c500a40d0503880760154800d600c068088990380c884910fa41c1443c4078068000c06d01c960100101034400c1000400b4450211010b41c11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 830485683 1250 830484433 830484443
    0xd021c0f021c140409050103020f010c200102030903010608010506091f0b070501060f08030324010c06050a0b090414010f0c0503180c031b030c0a1406070609020310140a09 75
    0x300281203042c128603101d0b140c0380b41c18000c500e442000440c001901030000b9003000e91002401d5411401000206140f84180701c0c10060070214000020300c070304000d40d4280d4081c00a854011100c0340050b0b0840c041d0882c115010340c0791010000d40c62405400640c018901521000707859121111022401e0460101c2d9840d44110103c1c104030614688006003c1c0c607010314000104c0701d440c1c5030318940e504d409a20100c6d55502c04028441c1103a031030048075065505099102c2c1d054491000042e04480680f0360144c049540c880c00140d0031040e039004400c0d5550010030400081c0352a16100d100314520b078190b0915903207080c0e0200c80c0c0310b05030f01c40d010346a00c0644030340341556038041c0150403a0361802c40300f181900a000311a10992810001308902c00801c3c803841114128007428189041c40c000205c41c0301c0c03004640204070340c14003410348800e202000d8941540d50f0781d2604207a006484245002034040c800c1c0300840800502940c00784180e01200c946030b40e41c1342c80751102e4505441c00050042c3c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 830486933 1250 830485683 830485693
    0x1208060d1b183c1d160302011d0111030c070e0c250f120203090f030304120609051504121b110112060f0803070c1508060f120d021c0f02 60
    0x3d1584000691a6409965441d00011aa440700b086005888070030000082044000c42040c00215090011440c0003100003101203142d45503030002400b000c14200380501d80413441c21000c5859108003803410003400d41c0402c030307940d0350a08048240c0d5145644100004032000002040e103075a030307a40440d407559000362201d40b01a0820041c000304d240380c07917004075640d01c8095210b00016000824442200d01c845c3c000d0b644480440d030038403c000481c4401c540c440d800804c01482121980307914030040c42d411000c00075540b00ca40c0741182c9400c0625041c40504d0100da400c000c01c22440302401824500035545d4800d888010300102c503c8041c14901c014071241112003401c1c129445551188401c0c617000b400403503103c0c2c2e1000c001c20084c40ca60488101c03074000180d85418412500b01c0324005203124050140f441341ca00200614041c405010148070b1100c0103a0311002d5542d150ba00b03500c02500c4400e844ca0510740d0b00001c2d54482290007954581c0c0034a4010070b2500d40203000c084498501030700545 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 830488183 1250 830486933 830486981
    0xb0604240503010810020d2405130e0601090b0102011e050a06090203010303051e04050d08040509070e03030f0a03020708220603060501020a0f0512030106110106080a1208060d1b18 79
    0xd0040d40003006040300a542e91a10000c0e5201822510000702381c0410844641c1ea0503c0300703210300c41da87c200710754204601701594121180b50000b45581100c41020300052a41d201400403070241c10720074510035003034030fa0444420940321180c1c0a00e004005502e000c00c5250740d01c0c04540d090780403d10026011810030320000076881c1411452401400c2c8020705641340507110000039481c62600c0c1e03130548400001040503c1581018901a81c01003c0c0d41000744000c662180040c1e6070b4405d058201810000103d414a413203402078040e00c4c5490780c00b1044580312071101c0d1007441d130000100703c40b103010300746000c0c0044e50702d00030f20a0100362881030b8041e1100901544400340c82d05000c0400b01c6052180c408042680c080501c0592702904496840003140c681c45600f603400c5d200c00d03401c01d400302d03001070700030500160b0141e40240200342e09042040e2607944044c0002c40d06500c01d10050040c6c46114000c2c5001021440311900ba180b070026a0210107040305000c404940c201080c080f42c14115181c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 830489433 1250 830488183 830488213
    0x601150c12140a03020c060906040507050d142a041a01030216060203010308120a0506060a0804060b030109050c0a080729160f14060f01060f02010b06042405030108 72
    0x425407100c4a040902e0501016084503080d503001ca40f204000a9004c900181c2c1c0440901c2181d8000c0030b018020582411b00d07481d40d644845591298504c81c60301c0041c40410001d5071000e68102101c8141998903142441003a082100d84480031604401401c2d202a411450584501c20700411040102e406501c1c1d4100158000c1d4400c0320889207a5a49a4980d0006560b50004502951160322199100d0364480c03800741c1c81e2500038006a8599040500308041c0361249000d0f2280d810321403502c41d809403140d00f001c0c002001c000341c1007a0036509001d02c5038144140050200003124040e51012032995607150703c1912400c403070080980450611807a180050140e00031030b2110981d8200c0a440e0205501140700c9220184204448840001040400748001e06005034111140e400c0503200d0317407400704a4480c4070307601401a001405100c403440c102c42032007540854417840000d4030140c4e640d9160031000d20010101c00720000d10005d00c05001031400e04c6203003a40e040710301c01c600038a000c50b0041c00c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 830490683 1250 830489433 830489453
    0x4020a0201090821010e0405100902010e091f23060a0201180b0910020403021315170a060f06030309030b04020d06060e09060703181b09060b0c0601150c 67
    0x4444210340d2219680c03404a01142d006000c0d000000c020000039a441c044c00c4641c2100517405494003507204010030010a03008500c255102c1c003007000c005401200e500c0142c5040050841060b00700030080100300b00c90502d407501800c40401043c103000c6447c0d072480d044220000c599541624042c605078420345071704081c0d02501010b0403600010401980c0340c041546c0906c00914103544d0884110b050200caa103007449001e82101c03c08500b5854541107030049030626030124480070100b070703540701c003001c1038210785425002504401c040018401c14402c48903940d081c048074152465403801d428030300c0794240d900c074403004c5a502d626000001895078890000341c0500410990b00500e1441d0388500144081c0300300c1d400b80c8100c0700b4035145800d106480718500080142401d00f45442c0c840c440440600302031500e82e240d640040e00d40403440b030b0141000044c1c0026444101381e5410007001081641c02840a401703d208600b00300e901d1a0f070ba480490201444004862001c180b0071a07100f0b0215210f025 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 830491933 1250 830490683 830490697
    0x1a0f010813060c0c12032003181f060e0f0103020d14030f0a0201050a091e050c060c03040608071b171615060609080d0e12100501030314070b060402 65
    0x7a40011000039030b15508142c1c0e00100c0c00b42e0000c0d0030a0303902d008010750800c071340404001c82e150070032584005054842c1580000703080000804008800991103102170020440c010f00d41c0c500b50b54412100d0003205000e01c440c10310b007002c100d050400202e0110b9107150348512a1098008803840741c2d10315002c0c014001d0075590150f4104040ea5800c02081004000800c050415003020594629011000a007162800b902000c06075040030b141101141c81182000c20041c1c145002c8440b00d0b94519100345003135003100343c2c1d9800220101350768002c024044064001c840c219283c41000703a035400002c441700810038072004180340010346d001e13020a42c109410706030010380901c1c1a01d0180c0141c5042c011011303a10b0200c0e5002c142d10a1810204401c5c010305e0004c14003030508003516420019a95141c0401c0f100c203d040024601240a503555021280b0551a40070419aa124194038200714081c090034003055010401280843c1581d0580c04126810a41c012412010548403001044003941c0001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 830493183 1250 830491933 830491951
    0x1150603090c1d040b07050a081f03050a060510300f0f0c0312030209031506040b0d11180c0702091008010e030310080a0309090b0406030b011202041a0f0108 69
    0x40d01090002204580079036200c1d0f084441d00c40b0340f806140c45940361a004007000c003040703804d1045180941d00180126004000301c100032010050080d081613202c10540d102030a81d2054414000612801d0390040d40141c8054100e0000561a01e50400300d84802981a40405080d80d5800014034664205141802d1040a8042c0b880708584c40d00c000a90010740c0a4403800d050207403c00421020080c41d0440d0500380c10198100540100086d480c0d03020000b032071120303482c0000001c12a649a62001c43c4215005010340030b0380c40d00341001c5003519894129240180240b11008100c1038000340744038401e0103000c07880c42c81d109040c0e0902003840170191204040450024000c241c2840138007851119a9289004544a10385070f44000c07075031600c5a202002c43d03000708402001186e844030080c02594a90500890240c2a1001090081c2555400501101107520000c2280302c41c1ca03c1c0c80c081e0a008450070320034603022802e0008c0c400008840c6a0b4800d000040c03417415540901a00e541c069040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 830494433 1250 830493183 830493203
    0x5120c19060b0a06020105070e152704050c070c09020403110d170c0d02070b070b01271b030506421209060108030304050d0c0206070f05100b030115060309 68
    0x1202c0800d003049490741029026035110820801a079030b0004d141d800c00d600485404203100d140c101c0b961900d1050140c01c506920310400d242440d05480c11000d07040c440b0180c420031007468400d0b417440e01c80e0480034007211400034110380080e480c1914020748055036080940c000301d91440307108120324800d16420443e002c0c4810304c8100294001040038141c840340070b00240001c5a6902e800074104011038118101c1d290040c4070340e10205130b0554815040d540811202102000445100006480b440b8103032240607081280040c182e940c42c05030b42c0003c1045071424022500d45c0d1040103c0c0c12004140d00b04c1210100c0e5152078030f8401c40c2c441e660710703060300000032a036051f2005030b0714140d501c07440e4001034a0407690240005c0c00c03001c210035030040c0b00070b13070146045003090307502e08d52038074181214101040408040303401555a804202c80080785d10103c1a10000c04070f18005484040701e8290444040c5801c5078603100e4141806150342d209240805507000a040c054103074010320007280e042c0d80041071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 830495683 1250 830494433 830494451
    0x60a0309050d0305270c01112514030d0f14120c09010905060703020303070c241d120d1802090403090e06040e0a15110a0c05120c1906 59
    0x10030b01100c00ba984465501003a245484a01c010300e07249946070000908a000b070780a06000e6010521600050702440d1001b140c0c1c01c41d902403840c2040c900545907211100000100141e44848580c600721118541c07408900e00c1d205041548501c641c0d500e0714042046201001045481000070150300d100c0c0044082c2403580d1200e000092034003c40340141c2508000461212641c1c20001a400910085411518090159500944a00000e003428050021044002c020001c500c1c1006111003401e0003940c1c94010102403040103000410380341e40007420703038103110f03526003401080511f0601d1115000c0d928024010040b5030042c04805c400601d0f1901480507140140e440100c6a80541d00076510495080c6c103004407aa004500500380900c128501140c0c9201f920000ca9481f0080da00180301c087c100c851395201c940907002c40040ea44805400261820205800407204c140d0107004200702c6071006801e4201c2c46051140000c0d80302c0d03586c854101c440507a42c101c252045030034804e000110707480c0341c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 830496933 1250 830495683 830495693
    0x1b02041e0f090215250203070504090f0303060f05012016120515010e0103060c030902040e1501090e030313060204120c170c0108070e0d0507060203091e01020606060a0309 75
    0x948904055106500d07222401c0c10752138101020b40640c0c0b4a44813080c90802c60b01110100c2442c444041c030b4401c40b540045109540e4280010402428049e10911454144e071814a41420720b0003422404a45080400b0504071401403000c0199001a180d8200520b0754480c0d5080305010011542e00c0b5100b210410f0410510a20120340100145401715004410718580181043c4088000b506010400c00c0100504035014200c1c9044035042200060700f0421042c081340038049069000c2e40042c2800700800345000006256843d10215122040070360340c81c0c20450003501c4410300100301e10303401400070070001d661050500041510594006280c07035614140301c0000e0130b0401c0f098412100200c810062410405030041509415001038007045445400107018075a02510300003c00400144c1107050303846058018003c55082801c5070189039403904025621342c410008a8040d2201e04c80080c12001c100010003000d2005802801c2169141424021a500f10055003010942c03078010b9000411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 830498183 1250 830496933 830496941
    0xd030207061107031e0e0604060c0501023f191d1501050907020d0c0312140423150f040305070803150102070b0f0f0c07051203070605071b02041e 64
    0xa12940759001d4000f0803d0f00c01d007031052541a100280154452545516a11f00003104c0540706503091462440c001b40c10200e009028841c441d2440c1e01c401d0746800c2d482900c070008600ca603185184514a281c000309143c40c860142a03a83d400c070818290b81111105801c2c0e048081b224a0244401d50008580031080e4580341502c02c04c0000804803200500582c18101030090340110207000420b410b04003640001d1620048840c082d0800044505840700c03c222078000700c0042040c2c020140c1c0c10f0515081c4280042030061a805801802002c04a0040d20100344c1300c1e0010144d00220304195600d49003041100f1000b0001c400b08502004050300041c1003030081d6000380c07641103c074103a5520000029143c142150030688840000b07114032407003540c0070000c41e00e07440b0040e041140c0311244078a000f4541122904511350050b003452043c1d8030614000080c2c243d55004001c103001c01d4440c030320181c8031520800181a0071111001b101d6002d41411f8018400ca5014180c00c0c05180203a104160121 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 830499433 1250 830498183 830498197
    0xa090b070309020a0f24120c02060105030c0114030c030c0904090b09060a060b090402160f1a06090601090902180301060611060c040b0403020d0309031205031e090d0302070611 77
    0x7007075480c6402029414041032150181c19041c2e0b80c001810b0402169044d181e43d108103400c144003030f421020603041d00c6101068260751810005010000c1b803100040c2d26540c0074000c1e50f00a1240703000464807507210310030b58001c6100409801c1e2071a10382e401d20703201aa1008001c284130003401c002107282174640380324501002c7d019003950760f018100004034506090000e400303050002d08141e000e00548204000f00c1d9142c80040f0b8005941e82c80300e03070a000c0c41c44d00b05080540500c1480364484103108080241440d802c0840703001c0c0200e5540c080402c103a5000c241c07001030014600c0c080070b200ca589258000e140034840003445090b41d8461200003803d590349a04080c00090301d401c0e40d4926908200409500301800d241c00e141494182061010217020360300c400781c429409441c81c081458040e1250401440e04040b0348480090700000c090319a0b0710964000e8020200b0f034143c0e04044a01c102900e005003500405011100c015032022400b94112800580c3d0300d9507141410882c0c14903100051500c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 830500683 1250 830499433 830499437
    0xa03050f16080f03091e1903090905040b060114120a2d0b01020d020a0f081e0a0c1505090706080901330501110601180b100e030f240a090b07 62
    0x103a89010000c01c6d00303040d43c00120100c84400c40760006112400803a4480c1e5000e03001d170881c5201199420301b00c5400f10541c1c4001400f924060030300080c09014640070344154002e0329a201004403081403003100b44140c2e4204e040009142000c600008017640100344030183c007100b46d021540d020803d03030201440c988403c003e125030312000c6030182d507014081d08001e14410300191002d08010b880f00c010601c0b02d004020483d48000034001d0342c00c001d84041c40d464041c00311103030303899400482005d0803416911000340c40000072a0444090a2128000c1921801840020b0b01c083e614090302070301c0c401c201501d80c411035502d0314103407a4907100405915180e450f10108440000d0a1020081e91551311500160b04216600081582140c80001c4080c11030302151003070000703000103a10410003000d070003031019800380143d0090100b00e43e21151100684004905503203145510040880c0e8905004c00800c00303a49100707815940710300300c000c50b955003c2d03c0203501050a0403641d4429144260840341080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 830501933 1250 830500683 830500687
    0x8031206030606150403060207140d020c011e0f0c0201050f0a0c0b0603010c0203030c0702032a0405220222050c0d0e0a021f0e1201060303030e0a03050f16080f 70
    0x822480d00300302003608040141c0703244811804244c1d800d981442580409414240c0000d061010050b83d040aa1400c145850942d0710301045800001d40314010a10342c00d001840019a603c0200a80003119a5078901616280c901e4019518180c4920b6000c0740b0681c14040203000301e513038003003850700240b82c0923500f0760300c48581c5039035454042c41c00d0001629181c000c2c0c0c50021121070307032a0004101d13034101d03600c941e895441d02000c0c40003d103042e040d0610098181031860300d100c1a031940c1d54080301e04245c11207081c001075490060303030000c40c00e058130019194020242c20101608250f01109620007110300c140d004a058004110107940c002c1c0c40540b101c0c1c10000e44168049924402c9050101c4907201900c42400140c0020303003002d02054000b151101c2045218907528050b00d1580d07030049021302100c20460114001d240204494403041c0c0c0400d050119140d00141c01140c02c540b020340c140c4645051a150380c0b10070815030440ea200c2c0e20a1308215130490041075a8102400216407590400380d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 830503183 1250 830501933 830501941
    0x907060201061e0509130f0308060301051303021b181005030f0c0112050a090f081305090103081b07090f06090c03152306030c0c0d050307020a030e0109080312 70
    0x242100c10a90182440000343c044891a09a518004000722882265180440d1319010395100c0700005250008020309070610120f0200368000130f81c80e101c1d0b0b908038020000c0c0e03507a902c80e400801000040041c0143c1014407200000340241d15254007074000a041800401105491050810350555405484840d0444100018036003044030810701d011440c003034106144207400280c41641401c80404486445400081c0e035103605504c404c03074031a0400300003215007117542850842a4808409594251141c034070100e0607040c0a982681283d0703224880926100321104040e44052041c280840c55000c0c1a800091540b11030240200710001003100190b0907207003058200881ea45512000240340c18a0102c90089244190754021039104141d16042035200e5441c4000300003070604081d07407001c00401400140380034003001e801d003180c03020112200400092001e0300e990004407100c0340180e11006408000910a00d032800030a1818108805160b454410107400c1d84c211507084203050307002c10108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 830504433 1250 830503183 830503187
    0x90c031406160503011206020702191a0412021c020d03110d090b090f03120a030902240d0f1407020a030e010926070302150408061e070c02010e09090706 67
    0x100d401200d404241c0300100400080a043d40c04144a41c21005480480400500a140c1c0440e1200b035801401c42d01661114800800c4000751801034680c000c1400c0d00a00c10152000110746c183c800c58000c1e14200052a4208000c07040c03113400315040c0c0044203104100503110808010003083c0b10340c550902e210b0810824510740041080d0983c1008a0450100100891401198000e11080d01d000c145c10100c24003080c50b0042150b5003030303a01d41c1d0008400001c16819406194403034400c0721401c08010100308038402e441c41310051f0503400e07082008420003040c000d510805040011741408218160041648042c8200c02c45004026800c0300c8085020103a0241100406aa00b400c001c041b60741000d103200c1d6441b1003c036060f0700c4c14070b001d171054040700001c20010b0f0045a00a0200b24080201c1c84000700c160807901c110b5149120b0140419010003a502d500007a0000c1c800c401c031069625840c044401042600050341446121112142d01d034540300b00040c4600200b40050501625010700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 830505683 1250 830504433 830504443
    0x1c1403190305010f0315140c07020307120b0112051606120506030105010602070b0a050f0307090512010b010e04021615022a030a030b03030c070e060f0d15050a090c0314 74
    0x3455040515002c0140481044800c8140540781c20243d0000f81c420006242801461817040341d0050401c04801c00c4603416030600102002c51082d000d07034180c1a0748564030310905c0340c90200106541901c00061000e03000c000d0900c0103160080044884104181c000d4501903502c0340c21481c0010100300c0442124002e50103020b8105009600800c515071401c14025103032030b85070003801c007c4000014521100c900c5001500c491002550b441580da0600c14000f40543c2d00c40d21496000c0c4240b02001c140042040c841e0001c00801a162000e000c92001c0410009500000a4001100d80d480c0c502c0042200e80e065131000320010034005980c0c0300802144044190307942444601c840703000c840803a00c004048103403072140781d240c100840c00c5000c1c10f0000e800c6000704410103045205540c0300103002100340070041d01503141a82d1081e05904d4a03410b0150300b03a490340700500802079040802c000c00201e035000c00c3e0710500407a00014003541c03e54421522080c43e502c16070b54810123054080031fa40f81800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 830506933 1250 830505683 830505727
    0xe04020a0e040609060b0f01090303050904060e1501021e0a08280305091c0210020a03111c06061e080a06120c080d0302091c0812091e0f0c1c1403 64
    0x6000881d1201240009c050400e5400010708101001c00c003490b07240c6490304501c000e00403254110f9428503200c202d904400c02d56084242c01403160152900702c4450303451444403a4085240500365a078401d8880721000d51106604820103041c110310a000100741c41492010b20075940d9000c80c0c603003060307030306c25141c41180402010441c0001c82c001c28007a400041521605040d16030158580a0410b020340c01061254212250350000050b44207180a0111042000c04404070080041640f0782c03200310348548440155620a2281c00640da04160007042002d41c0185826004188582c07107030307081d14106c20404c0080740c400f9615076090045030418400c00c40c01e8141481d08604181e454000641c14017080c120003151181000c013110140140c040859403480454201d2580500388440180e0380d4080c0c51419107007401c4e04015400304980d02041068402c80c02500401483c0c06810820204102e20607411681c3c2d10204d07031410004020281c1c0f1400ea011140c09075880d03c080740d2808118050541e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 830508183 1250 830506933 830506939
    0x903101803021218010c05030d0207080703121401090e0c120106210b0c07080408150906331f0509270c09031615120908040e04020a0e040609060b 64
    0x100c409440400c07205902d4103180401d1030726101b00078050401381d0440c454581b050182c1400054000c082c044580000c011241c0700342d4400c058111200040c2d002ca0718041340003005ca0b010040104006070741d54019a060551060550308114510b0f0f0004612145440c0401d525135180c02d0104000c03014404100c440070303d040c0004980319010b5071240c42c0084000e0481101003c0820064180a0010140c4010745445d9080301c030420010640344003688001c44032600e0a20440c400507110004a041d0099655000810300c80c202d81040b80f0070310740743c03203100c01c4c0c64201c2c2c2c100c260400d107881d81455a0418004580314150307600c20030410310010075071200103854102e107d005082d1150841d4200154860401a40c079515510400c00107810801e68042941001200c0c40021800410b0001101c40141c010b4842c0e090244040c42940c09840320030034060f007100e40a00c81080b00003201140b6643c4284020240c00342181c42c1e80c04a140d05000b40c0381070399036036507030031721001041510701c10542410000c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 830509433 1250 830508183 830508187
    0xf1c0906030e070b07080c01050c0d0b040b010815010314192a030c050d09150507031104030609020a0f0e090c0f06090d1b0b0306091f03030509031018030212 69
    0x80e1008940c3e5101d02c3c403413102c20200c001010300038002000c0503204d03010b045a00170b125500b00245001400e0f0442003109004134a0030084404624041c842d00c641184103031228466503550340450400700760702e000407e0505444100840c2e0361580c0391030072441100c282c80d060542c0a21009280200e5114100c07510b440030388914448901140d9001d0071b50a61101d190125989401e888210b8681c0038901c02d0f50002814140014204181c0f110480d0048a900808125603514208100d003913891011400303054140411050010031402d802c004041c3c0d0010307107140301e42d81d520070400e00300704199401044803900305010320003141e0040c0211003400740115503030102c06043c0300028580740304030071505110b489814585010040d440200280171aa11698002c1440c2c0d030380b000505070f03802140e001d8030130a180e40000d4400c0c88030000b03040741000301a03020014141141d4060b5101c1d40443c118540c588500c0c6040102d421407400b51041034190f40001500e940c0c2145070191800003c811058028041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 830510683 1250 830509433 830509451
    0x11060901051e0c1213110f06070602071103030f0406110303240a0b210604020f0f1b010527060910110c0f03040f09020307020607110f1c090603 63
    0x306095100705501c2a904100c2c0a0721000100485889200c0f00d05030b0442c3c051007000a00742e0f28842441d03646000700100c00b10040075108103d41c8042112407558040f40501541000c01c0a56024000c0b06104410303640000b01c80c600003c0c55038114242c103041c802e100140510130300303a20a42101940103014021429410007111000046849a0b86202240d041d10000122540d40c80845002011202141c9560300c4039a00302d05c0d03896624544800e9841d01720030202e106420300d4070844000602d8550790710300b00400c1c641101116480b004011202108000d080c0109134000c2c810345009180c00c10400088400d0b000c41c4402c20003203d03000c00180c1e00054100f0989a001041049021040f401c3c00507000410907c0b200060207501c484e070905200e480725046207a400040100306860000d0b4070209881c0d51780e002c507426440215041740050b008003001c660702500480c0206408280380e0240c0d003503a0b00030f030449450205001800c44005055401811209420181840c047c2956107828400601 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 830511933 1250 830510683 830510701
    0x624090b1902010b0901060201020406031103040f03032c060a0b0d0b0708060a0803040b0c0c0a1406070f020d060b0405101a030c120c04080c040606120b030712031106090105 76
    0x1418402403000d04040781955815100f90311100e60380c0c0005000301e4541d61610760090003900300e80158004a403400c40d01400c003054000c02d8030300c626806450b038486007407a503804401401502d01241d14400d58071010003071103c9402c85500d81ca010400041286280c80400c0c034083d510031254550044c8644042c12004c542035041e055030002e60b41c03c0c0443c403619000d0101c3c030300c590329600401041c04040740c040f8081a0800c001c1040c4554001110074021143c010000c07641d040d0f201c0c0002011501a03201b42030304080c0003500d1158015a51800c241c0d42a4000c51156040340d2401c0310220313507502d801080d515261241d99002905440f003039810354240b1804000c0702134543c5400c0501c1c280800014203100e0b40008951402c95910303c55440c074109110343c04065002406103c206000c1d03000c592019040c10720031001180d0007640c0321900240c9500344c0000506040c940c60760980550180801c0368052410041d0b01c091281c1c1d00c5140d00350021520074205500502015400d034140818000d0803c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 830513183 1250 830511933 830511937
    0x50607020616050c04150e06090708010303030c0c1502070b011703070b06040209191404140f06130e031308030a05040605030c0c0a120210050f0c09060d0624090b 71
    0x103a00d5140c0302c0c00440340360400300d142506450305160b11a007000c04042240503418400401c40f0800c841c8068107482c2d40f020448100030881d05440015141001080840d10a0b0400b00780c002150400e0000741281e6140e013010f4402c000096080a03800140c040208070703505040070b0050005402c00742c5000d04490540c3c3d1284104100a84000c8442000c901c90750349981c1290f200c0b0500805908211004070012140c0b0b0300b0622488050729030010701203070035040a015900d06001800c0c425041e030750f100340000c1210403001c5c0440c0e40200d10100c410075080c4075403003580540056080110303250401840c141d00302d54100d40240c01e00d5001841203c0304075402c10280c0781a6201418107030703100c3d40d440300c1c0101c05002d0080d41003454130a412081d01403000c0000b440c4e00b40c00341c5074295280e0541d20415a01034680070b0750242d00d1100540f0019a003007212a0180841c5000200020f142141c549151400c1c3c98190304078040c40c546615105e030310300740001d191102400250a0500f0203d103401c0c001d030080c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 830514433 1250 830513183 830513197
    0x31806090a03020d0f090906080d11060f01030609150c0201020409150506070b0619060f0305071b0803101701020309011d0a080d060305011b090816090207030e0d03050705070506070206 81
    0x40803e1a200822003401101104e000d0001f400c0c0070801955642045d030f07a1102c520404501056100100142d02d49000c40c89500c03600041528002c107900c0d40d51400010080c0905c00d40725922010042d025084079030288200001195002503181d0303040c0364140341124040c5581050b035901703030300b01002503403070308819280040c1d00148514050380d503090105684007403016090302c90011510000c01c0054211070840299081c60350100041d60b46c43c031007942c0801c00541651508940c2000010020300014000e40d8021280507110413026600ca8212002070342c0305020704135a94002c01000f210610074030403036a0401001980100f040c0e03803010380c503440f0310948401614100c00001d401c40003440c544c101c18000c3d54014000c00180d80c02015a483c003c080c0c0c040c65002880c1048006802240014840d2a40c155140c03d07a001625001c0380701c00942c0060021410300500407503805c074507a503c882c01c40c01d103402034680315a03c00607854224101406c41c2c0140c0e10510f024040c00c40035884080c2681c40d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 830515683 1250 830514433 830514437
    0x30a05100507050c0d050c060705070206160314121e010303120b2b061415060d150b0415031a100e041d060c0a05030c1608031806090a03020d 62
    0x45602c0780c001c121000d104001d07003030425100e0030f004590078035442070003010300340c603244c090f100f141c1c48680044800d0b03c228107000c1e521185c2881a2a628a0100d02c1903007210311a080c10720300c1c1d041004d01c103003040d040000d00f980c2590302a0100020700c3c0e080003180560951080d09401d180d0b04542e4050200242081c0416203142e995902550301e881e51110100700d40f5100a07009801e25403410b522070005100e41007240c0503418540240c07003a110145a050280d000a00d10028160300a42440b4040d040240518a51038480103045107103205044034601400c6a041c0e0340e030b0380d54200310313030b11503044c82c440c280404040c508001c03004184020100031440143c05c492071840700305061012900c0c007414424442d40103180003008580e05a0000011034034400d4401075400940d44c1c011140c65600800e241c10010402c05c01c00500e617030200368002c04480d207c001320500d04401680781c19500350802c84908281c00c102c0030f04080815000c10010307520100003c0140032103030303240d58005e446000b40c0c01083d007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 830516933 1250 830515683 830515691
    0x309050f0306070c030c08070c08100605010f030b0a090213150903050c10210c17060a03020f0307090c0e09090a020310050c0c060a0b090609071d01050f0c1605030a0510 74
    0x30400d8864006c2c07902d100d41012100d03407120b5544c1481071600b0218071034812544100c1450107202c1d034aa02a01c002c4400507120380c00c0000a034042603001e404400101580b01c000031034041420712013403014250034107400007412089424404104800b080142c0103600f400f180aa0804c002440003400c405010800c2e62078440115020f43d0959041658580000c4a20204c90304c401128a10354030a1403d42c0702135454004085000000062b40b00041c1e0744140c100c0d403100424405800e05d0107036036014020103011111020f5440489008642c02101001d00040101c5003a00745443d05a001c1d540100e060030242c40309001d070303174002a43d819821446003001910707a800102840c19000c2a90601e040304400e40d245490403078040c0c001021510480781c840c45001010401600380360b2020341c0b04000e0341d2030b88503018024506004148030500b5096040040030404040c0031403040c005085159958002001060b4004001c0828030b000381e0000e138046d0344910040b4000c654000380800001d900031500203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 830518183 1250 830516933 830516957
    0xc090f030201260a0c02070f14090903130803071a09060411010e0414252c060d15170a0f0c080604030c0506010801090213021c05130309050f030607 65
    0x83c03482c03802140e0a516840b15007040030011a9030061200c016a690965040640b0b43c209550b50b00a82c1c021495060304402c0900042d06040303038a25000080e000c100c80c241b95611a0741d07102d809003600701407555000443c0034400c0040c1481c41c480172071071507010007046141c00e1042e56601c0c180108090006000d084560504d0303400340c0758260410b14050002d0100400800d00d000c11a5410b8450a65400c00c2c2000c2e0030781e00c0b00c00003807640740070341965408560342e5845440d504200810350401005500307895540c3d2155440030010800c40c23407036550202c0d10581c4440504007040d00c40c3d200e038012018a03e00003000480104005610b00c0d40500c620803071106500f0881300c0580c03079030002100c80c8140000d100525070003000328407000d441f0340120341441c0e803210400c50a0b030302d000c28000d41050306400c0400c06078040b60082c01b0400740c126400302c40d000450309500300740c45007521180e607075161307200542d030900d0340c441011009001c0980c0c01c2c2c3c40707104064000c2960358400902e90804c10608100385 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 830519433 1250 830518183 830518217
    0x10605090f0a110a02071d1303050a050d050f0402030d02010635060106020f1c020d031d010603110316050a03060b010203160b0a0e06040314180409060b01030c090f030201 75
    0x405020400059503545a4840c0f04019540d00d40d103000e41c01c1d10040c0e804815210f5408142110712605e00723005e1880340914140c1d020740e40b54004c1c8084809005050008002051461290522603103a203c428001818140181810564048285011641055014009800307400d00d441405038020141410081d0a80500c0701d05040e01c0311404058050500006115640003907400d0201025400382c0e0303200e2400e100003148402c0c183d40c000700980c001403aa1101d05001703500450840107880540d0401c1214a0401400c540d8540c000711254000084101c8041c14100000d680f00d426004c140c109440c140000500342c0d085500c070003821240c403000c0541c8540d1017401038a401001c001e000d1251040390340740c030701c461880440d201581c141c982083c001d80403030009070840c00703290952500041c04d501400c0c1e902859110505c2c4094024402e101d07070400d03031520310030340400070b014002c00076031407441c038000401742c40c1048080410480007410900440c00b11900c3d032400c40e642401d11270403d40d0807c0700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 830520683 1250 830519433 830519441
    0x30a0815210d18240e1f03050c040b090415030512070b15010f0e0a1e170f0d0f0e04020c0a02040c140901080c12071206050102010605090f0a 62
    0x504040d4518103421920031100181440315140780f0f4407618500003020044001c401c050f48a03c204141c04030703400c0c0a507850b61400048104c5040e103040700180131014081818081100361000b0100b105c0b641d040d03940e42e80362140a82103000c0814142c038144c81c0604500c000e00501595a204a5031080440044811b50030310302c0003154000181d50711001c40014201c1650003042d416602500180005041c0c0c8502c54020300d02d030003050712800400d41f10214103d45800c524522103401c02c0301c040001c02c8403119031984c503031302002c02603101c84024103181c0410000030203210440a00e50204181074803400011a054244c0d11071441c0400483c5080c03001140c0025400390116000b510000f0107075056000442e02c00301c083c0c001d8800344203207000848212242c0035100b45040c564041848007142c43d42c40741c03a0041d01b07d40c0d440d0481b400d12071500f60f10b4000d508281c502c200811103000341400007410502485004040c240001c01c0160b02e8000072440e80c40d07000b00740140041c03250000031400d4110f544 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 830521933 1250 830520683 830520709
    0x6070f0f0e03031201061d01091a0c070b1c0b0f0306061014070305070b062215050315040512030402060304080c01021b01021c02190804021c060b12030a0815 69
    0x111381078243d42d64081c06084180b40c11420100d050000030b481c01d0315400303080d001023118401030600c1c52a0054042d00c0d00305411001c41c60102d0b0103241d40c00205d100d030240141c14040d02c41405000c6071514200c1000440c2d18920703110b03014403803000c06a00b181e5004900258048010766514114000001040f0307000801184803034810000865600c007410740c480d010b020110301c55801c6100d01d49400080010303541030700d07091008565000200d250440c0860b003207149140c000c0441d110b038481c1c85100007410207441e00030310311a10200302c0800041c00740401c44070175080000000d561031030415802003000c0d0711000f0005030403181c2c0080d500000c21400d5044800d14002d140c0340814500c44408144d010f903001c1a611402120321070969504240581f00316180300000c03044000170340088100070b50365a40018420384e441030456405001a92010040041d4684140302c000b80314280c0c20700704140c1c0349000d60300700e030395500170300490152540251180790000302c4181c80c2017007001414005006021040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 830523183 1250 830521933 830521957
    0x80a11060307090f0815180601060f022a09180a1e0b04060c0e0a2102030304051807080c0c0a030e13020c070512030a080a0b0a05040e0a030206070f0f0e0303 69
    0x2500010f00f205c004180ea840b29040007000400d181c464690341901d2115a5a804455411900041000034000c1c1d000d941c0307032181c50068516503058440c2030394180da80341d280c41003403035409032200d40350b4a0b28000e003e80c095212103401e600b24880340c006c19039503605c0c140000d01001d07115501e0560044004100a10580d00210444141c0707010320307088000e04440c1071844003042030124010103c1c41d007100f0450640b0340e25220240380740100c1c05080400c110410080c0d030180410007010444d51258881e1507010b40100802e0720303040c14114001040c0f010020480300d02c105090041c0c101d00b0601007680e2140d190980307060b40d10380340340c03200081803e81d540030403032411440000c0074111004c000c55440c0c04c80314101c03881e90020f50700c806031940302c0c802c109a000014120000142c2202810f40c0032044409000c0d200c00314154840e00481c0454540f480010000c0e40840f4400c420180e04100e900e51002d09403400c5d5101c480c500d54050240c98941c020301090100c56400c505294034108142c81c2000008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 830524433 1250 830523183 830523209
    0x15090f37053c150f0c091306090606050a020d0e0f060337060b040b03160201110d0902090a140c180a060f0f02010204032003030705060c13080a1106030709 68
    0x40710b455690b41c1c1c2c94102e40e50140c4210001840b035554407803d54405c681d0200c03000e140400708001c001440848544419283e13603140004101d0b0130140c483c1c003020301116182c55582e40605038002c1d25203903410044000300b0426007503030390085e1a4200520401e1000362982038480e11218222043c50403c0c28440d44c4851140900c1400130822104c0ba00203142000d108014039034450f01c150a4910030340c06842048201000070441e40d15014041c2101c4804501c0001282c0c01010002c40d619072245094411086e2250141c0301176140000c490703074204403c0e000c100807030444d1003040d02c0c0145004140d4400408003195214603000c040c544400c079402c00809088080f0789900300584002d07010848400000d2054601e07840da240144201e03400d894000011105001c803558102c011304030405c103126054001448040001503081240d903008880309003c160f00c84203c4550300901d09220781c040089035111060080c0072071b03003a42d500c1192050270360f4040d507240c2c2c4040043d1040009035000c3c103e14600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 830525683 1250 830524433 830524543
    0xf020d0210051b0a050a0b06241b0303040201092c0c0301060305061e101101020a08010810090312020702060903070303120f02070515090f3705 63
    0x8050002c04229410022116603c40b08901c010f0341c03050392540013869540942c9817540412070384070348a984100010b01d02440110010700741000003c10401c0550008004144d895420b001405d940744d031452240011411807070300e0b030002800c5041503c69100344006c40004011421001d05980b0803540c40000c1c0e001d068140703901042c20580c024800c0f240000e241034049035881c0b500c0c503007507060384442e01c074104801d19040d020000c0410104c9001c2c811710102c10200040c01500303001034940d840c0c07079413210b1205625060510f070a0120390003504c001140380150340000a42c00281900060800c28001610b03000c652021a0712031144054a9905204044000041590141c01500c0ca04c0c1d492905000c0066000c20f0329059003d42c140c01805034101c3c15100136038030350b074102d1103902c07441640450344040580d03041e0b241030100305000620301d10b050802c0c43c1c40454981588208202c4170041c0f52074101d040341c039603e071a06103040c012082e00505410306120540310115021075103014400382008011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 830526933 1250 830525683 830525687
    0x80f0a180305090a050103020304080403060b130e0a061121090c120f01060e1005130902100c1406070212031815010e1510030c051308060603280f020d0210 68
    0x480348000d1304c100001140420300307501c41d009072402a94040700403801c0c04d01315a00d910103000e5005103590454903801c901d03501c101e054013402042c528810702400e081909070504800f542e001000d6000f040c4010440c1e200011401103400390000c0304d420341c11501b0385400320103034113112000400d40e5000000001d44000e140003c113440e4440040c0000070014690f40340d9003180c00d83c00403610700484418103401007145087c822031024044080b080c0004184040b0350000707150075408805940011821007400c000c01c03510354800f80199150000410481ca0440d07030003561000b1143e0b1540d02d148002c00442d101c101c12014480c2c092011400361085441c140c015000030700f40900c6030191000d60748000c03d403000d884102c10356840300060181c02a850071000306401a00e1000e404408100d820090040c2c00d100c1e00c903054002d0404400540440d0400354101841c00c0380f41480a800d401802e40300340454501c1d003012a0319107034003644540c2e0902c99400010184440810b01079001000c216240d030981c0c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 830528183 1250 830526933 830526937
    0xd060f080706020d021c050706090f0602091305060306041e0c060509040b0409020a051c020a1d0c16110a090f0605010906030b031902060721031407080f0a180305 71
    0x42c0c01942110031400322140200d070b844003900d01450100f0074200c5800c660320f1007800201070040c06082d02042080c4155291750403800d41c0c0d00c041c1c07441940492800f81900e0a183e01c0e81c0c02c0c2c07400c05004c2c0b00c6030611100181c3c8902c0090001001c4400f4444620014080025041a19500142c0000c01310765616805001235100284640c416441c1c00c41042c1c00707141600c90040099000f801044c8450b0070704090000e260031041c805030b0a01c40c000032480060307a03544000340103001000081184d01d400d241c2040140c250141020010903c107110240880400040d01e4089a40007185403d98000e00c201081e02c01402ea040015100d003410031039103010649800141c200c81342a680c2d001015543e5604404466008844a615800c10303601c01514415440c01c00030060300041480b840d000503a81c400c129502e81d405860302e0480141c2034004603580521550034446000002c038001031400c503a0080000100518402a110009001c1600c44880307500c1102c0c0089018214100c60200e4103001c1d141d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 830529433 1250 830528183 830528189
    0x2403040f03030605060f03040b07050408011d06181b0117011d1b0a0c06110408060403030e010c050706151e0509010801110a0c080d060306050f1303140d060f0807 71
    0x210341840c3e400100e07820410704850171040031b40141c5056031125540c01030340b0400038280030104003050001140c001c00a20808503060100f100c0340c1d200c80e0080340c6041c02d010005140020b024503602030300c00b59a00110342c040d03880703400300e0002d132040000c0c00050310505004d010030101000c04000110300030020701941c1110058442188101e0703900d5490236202c000302c0c8142d2000c2c00000f88150314000b402120000c0905110742d0002c50403602000300f0b14025001503008404c00d40c03101c0300380010302d6007501c0351a042e20721310002070010301d440c2c1c2c070003614034811440c0c01000250f9a002c840d12801407465404003400b00d2581c1c84054040d00c85005c19a0a850b000707952080602100005800e0014421100c0800c001c0700c40c2801c1006401091360150610281900c00100422015440d04068481e40001d03520a05000441d410a042022007502c002010180c0d540d5040381040c003c290807a181024a4491300d0304a0780d14007a0a245001034009a0b0020050b0140c1c403801240ea654080b030b000082e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 830530683 1250 830529433 830529437
    0x30b180f0c030c1002030702040236150d15150f02010608062719060c050705060c090316030803060102010b0d0c151e0f0305010f03020f2403040f03 65
    0x200000390120140c4500641c1039140d0305501450b0850924203000707049800c0301502d40192428010a50081000d0740c3c030581a50040d01c9940c03191131402280300c4210518003520f40001c0542010003000714400c003418003030007101501c02098064000c1d81940203c142d10814448003070000381c0d07030090f0220b1b0780141d19405001c25400d0318050600303441481000e088502c03031070040ca030b281c4910300c00110981e00c00c3c1036440c04441944500006e0030041120701b00714603000c405100a07084030300b407020840b1146003211003002000c2281c01c0100d0f0700014282d0700600c8034103507240e542221a0000e890202030b136044950490110074004103129114001c0c51060b4001e07002800b05000e80001c0000000440500401e01d400001c424400141140c1ca105145d000509108510250300d02d654921040c2603101240002c0300550340d181c0707903035050140500500200c240c0c40d0459065500082001100c80c00003800303081c10503050710303e0000c82e244008000d8402c3c90400d60380d08250403d4840c1441c44081680 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 830531933 1250 830530683 830530693
    0xa03020c0306010501030e03041502030708040e010f06050301080d110c0a03032f06010b07030306030605090d090e060f040207060603060612050c030601060512060102010b060c1e03040506091207030b18 88
    0x1138154000d005032041100b58030051880c01d4241940f4007000341464554504600c4248590400076560341c004101400b20f03104440169890310242c1c030050300f03064000508004083c401040325030400980e82c80b40f0582400c01500b2019440901407500285079003240d031152041a0010506401004182140e090301d00c0c20514600860304010461030049005c18590b8400b00042088ea8840805450418420320300842c1655503911100b0544000345c5042c0010f070880c64452120940100301c1c0c1005014104400e5110326000300041c217264010f00103640111740025242c02001075561000740510351061b0200103842d282d06e0360140000446400b02e45c103200e0380c000301c0300314034002904038100c640903a00c403841d19044800540a0503c0500f806041d9900c0c1d07404002d007961000c02034070001190318000c04400340210440310503061a10509001c070780040006012540350181260a1541c4c00e0754030000c074000c1255100d16105090f40f024060001040070700c0380302c001503404041103058510440d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 830533183 1250 830531933 830531939
    0x60b04050a0b0a0806010c060f051501080603061b0906040306060f1809050a030c020f03150601200316260702040605030d090527090304060f140a0e0a080a03020c030601 74
    0xa0b009224103408003000c034401c60001513180d8030030001c800d18188101e501054028018103071f0b600f070380e005407200005010502840d0703007696440261160700980840060400d41415840b20b0121840383c400c00f40020000661b200b456128201141e00950f40b001081180664410b849031046280b17000e9141d0325004a072641c5159110390064913440c6d90444041c0494000b1503a0a07a24850f034940d080343c01c119003200c0c40210381d900380540c601032410000c910030b1503c1c1a2000502354010740e4a00c2d003072401141404040d04100000303850805010b280440c2800346d05040c060004201244d0700c038440a04040311411101c0000054444e05200303030307402d00160f40c0300c030200f42e01c920440c0e41000001c0e0f50706004000a1910140c5121000d2049480b040141481d42c44105001c8040b580c2c01c0160b0710000381004180e500c07a41c44990813220345031800c0c00e5640d907020600a40300701030300706040002400440c3c50f940d981c00482c0d0018420002200d0078100780d454065100e031341640c4035601c6402010000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 830534433 1250 830533183 830533199
    0x8070206010e07180305030a080106090911090f0307170706080a140a24060c0c0509070c080c0c130e0c030105060109030215090d0c090c050f12040213060b04050a 71
    0x14606075504600300104580e81c9210403116840200c410720640300c41034a0000101b134082c0f00502002d00191f0b43c1d03c03195814200302622882c890342c0304d00c401e2841c107180030419030410802e990307502400302c0e5400c0c01005d6440c0003d01e0000540c000c1d03116880c68075403200c061000040c800781100e1180c0c840711903a070fa550b10600102c03140c114064460000e68800100b2252440d400808003060007032151140c06102046010403040541202d0080783c1d0500d004805d0080c01c0c0c62140040c54101c03a1501c0521f841500180700e9100160020310610011801ea41c200d00c007405440c07614800a03010180b41801100b40201600d12a907481c9000d0080210202842c1010f0040c40d11845041e1200c0c00281c3c5141c1c00d100410360b01000306080d03400b0070300c0242410390398403150f610300a0140e440070203000e00701072810b0201c5001c060000c0500c0340130000a201149180305648030044210403400d03e80e5164000f042c0c0c64440d50544401d00f40c507202003c00d015040e840a401501c5054400102050301c681c00703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 830535683 1250 830534433 830534443
    0x5010c1d04060e04140a08160203010f090f0b090a1203050a0507090503060c1c1a010f0c0f0f0305090301050403180e39040e0121110f0d1505010303080702 68
    0x20b0f840c14410500008010585029040c1040c100c00001c5032100f1010b82ca41c46000d400402100c0c40a00b000008a025031801740030b411035040d9483e8041003c69101c3c0d40e0400f2007140460000c03c03034081ea400242d81c3e0360040c06010440d6801500192010f40410001401041c04075042d40c0c40c2844d01c070200700d205118407881070503203002030010022500c0e140300c944055080710642c0c80d4036501e140410b6647c00c1d510300841290080c0140c80c030f408612010000360280b10100c012400304840b03070f110712002c9074044141034030664101c1d007043d04904850030115014890340b4211a019030a10043c0401c055120580d05020000d0a82c0600f8080d100c050b6985054010303600c074083e034495807003002c0e0011740d0002c00401301315a0084404c8101c040d80c020f01c010703401540c4862040c001160040011015103010740c4500f104d4440442140c030181c1d903a03559000c010803506402034008403081c2c0080e40307400b00c84507444ad4000c07500a501a1410402802406003408200c000815240210b1412800024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 830536933 1250 830535683 830535689
    0x40f090207020109092711030f061909030c080313060509010908030f0720030a08010603060b120c1b01020418090b0f060613060e0102010e0304050a05041805010c1d0406 74
    0x9101d1070340d03502c0e0070b0004010b44110b02c005001004031b01d00e1211a4010b140c42241003520982481811090340e4040501702035401034203881a401c5501049003982a00300c0300e81c01d261a0440009500006003021600502e0a070801040d0342c10000a02104110420069204603c0303950203210641e41c050740c240c00d894000100038030360403088c0082a0141c03802e203a420362068070782c42c04480c50118800c032a40150440103540c5a6a000064005c811542c414055070240c80d40b403c05005161030842404524403450700307600b40765091b040c0400c00300918101211a004001c96000d0607808401d84140c2c004e5010b4801c0141202031307800c010f01d60b0700090003401c07105900210081899900e210b038a00c030300317a001008035a1100302044080703098541091f40c0c0002e0007160783d2300002d020b040703c006421100b000d400200309605c140002c001d10340e5a20340300c1c03040c0c980964020407600d900705450782654200020080c46035003803001c500a200c0e0700141e8200031400c80d24844c5c503248502018001241c0c2c02e40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 830538183 1250 830536933 830536937
    0x30721061122081e0a0204050c0d0f090b01180f060f0905060d03170a0f02070303230115050f0d09060209031b0303180f030f06010612020f0438040f0902070201 70
    0x60850200e10130740c01003241c003410b401a100942102d5000030100d96040742d00c00e222075800b041d46580b4030000d11581101716801c40040142000a80703d00c043c0640500c1404c00e90340c2d10860b9214565121b4004c424030040799041801401e4448080c46e201d0314040c040d0074111840c1100144a525009124142054140d101c25041d0800203c41d0804000001c0c440380819803a08e01015450601f03200034244207000c0d42d00040d00b00d400003041e031001d410b0342c3d0150703519034138010060004101c05c0c081c6484030221070510036514296803020f41c02a0080641001e8864a0f1145d02401e1011300d03001095510360072425518111a100b5400c90540d40e0315070364942680c0144501a0041d420403000c90302044d0080c410b0301880031041c002440c0400c400e42c00019034202c24010024590481040030b489000644150b0074110344600a0115000302e00c24000c01408000000c40c807103516004480000b014030404c00a0590005000609540b292290580303035101c4100008000c140c0b40300395800d0780c2e416 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 830539433 1250 830538183 830538193
    0x20a300207082404030e0604030503031003140a030e100201110301032001080c1905040909050f010509030f30010806070807031a0d110406060804050c060903072106112208 75
    0x35440441b41d020f1400c1003260010310400000c4007240c000c1003e10310a0316280f0142c0c11842c2140f8090141d030076402401c0d915079001065810000f50807141a41d1a6481500c5181034a02d180c5822405049880748601040c1000000403040c0320b0381e007401d113050300c100c2902c00d000054042e0044400c0c4408881444840c40180840d8440100e402940c071003201a5240250800d505c50790410700b00ca0905100710b035240d002d010382d0484001c003800b840f640107000f44083c0d800e10444125898040c481c05800c0da106025000100ca0214210103425a01c8204d00c0b10803005c82d0b845403191a0b4a1744160b0b03e44021804040001d11404d1281c000d0310301c0c0d5000e030445240c080c8010740038041e10080c4104115406050301000001540342c41c8110030041c54142e88150b41c5040504280d03003011400020300d40640000c2142007219100007918004807182c0b1035003034242c1354144000401d201e8245000400c62810a80003005201051000e06080214500d61045501000e901c45416001e50300c20060144c200e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 830540683 1250 830539433 830539441
    0xa140915091b0421020f010f14033c090606010c030f020f030c07031104200705011104140118150e03030c0109060c120507020a3002070824 61
    0x80c510104000c114007102c1906164460000413811649205000358191511460209601d0030b002101210082030070703c45000016610000c1943c0c01d021140840702c00000042080498942d80080400c4004100e620041500741401d03042e0000701703540c4080525121002c0786603900040b0301303140140ea05845407080401039076030544039050005804070a600039844070b09880d6200b4401010b001001c0005400300e1800d514080d50b41d600c2c403d040500591424200c00360f5850b80c00710f00c002c010b0000a0040c0c80700c545141090150410342100c0720810004100040d0702d00c410030400001c0706090701c602150019091241001c10034074490b024a01c1ca4400c2120406401081d440c2422040030b000d0301e1038015460029400d50305400000c4815170b50310500d10040030f41c09100c0c0030003070701d02140900c000c1c20103c2c802581c03012100c0c0c0203882410000b1300c4080c480440c0e03d9940140d006205410034510b9981e0002c1d40390351043c403c50f0030500a00301744919105620f40c0c0e841448080f04078a1445440d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 830541933 1250 830540683 830540701
    0x306080309040f090b07050d0617030d0902061e03010501030b01020d0c1101020f070e090106080708070603150806070806030f010902151e130311010f02100908090a14091509 76
    0x1510f00d00031001c0300d58810030480800c11a003000da00c1041d558544580e43d5880d0079090084816650200c0c1401c0c00d0446910344800c008003c480c107050842901241c01201400040c0c1c543c810304100d61040c1c070450300448a0099200082d5049441c240c03403c102c502055401a038440c0d1104c0050000100000d1807480000e03500e0300d40030203280d410300c11208192000c00c0300c02e01c1d14010360401076040850070104100c1100034014040a042c105d80904880d901c1c00c40900e9480b2620b000d042c040c0341e2038200c500c407402c109084101c0103110860172900c1c0e0f41069100a46024800d81c1e00f98042e00036a8100341c1400b405006426076164042c100c00385040d0444080e07030441d0070400d40312080e804051050038442c8941030151903503a0707000e1020907440d461440c01d0010700c2e0941408c141440704451040302625004614103c400000e10404521554180351800281c0714100d2070030742c4250051404188240b00c542c000740c0b8031605941c894101e8480c0780070055151005140341354420329080000c0e519203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 830543183 1250 830541933 830541941
    0x605130e0106170105062701061101091a090c040b031506030c0924180c03100b030a1d03040506031f08150618010f09091109150a06030608030904 64
    0x10a2903000250706902c4403101240035000e00701c0031800d030303456005221151520300948072885201c404450340c0d03945420080c410514051240c5002c0c400e0b18140541002402c0d04490102075003c012140340d0314164401c0715039040c0544104081d8450014001201e003854820b141c0d0341d100080041465218141c41c09500b182c0051845801d030146031001d12194940441c61801004007028040c010140510308400840000e20814841c8520581e020b41c6003a1280c103054010030440072076540c9582d915003a4100f40358503449418002d100000b004560041a40f120a81d2910780d000c0b039081c0c141c1c6084480e0789010364001c075030380401e04001085105003a9411640c5148281c01e96000544c0e5800c00282029250401e0f028610090010030005241011080d045405d42d100c072042d80c3d5061050b0403213500f00380c0c0600103d15a6440c50202880200d40b40b254228030000d100ca00c45161846946841c00c0030340c00501d000d0111002c0201341c0728024002c034000c0d80c40740801181043c51480800010b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 830544433 1250 830543183 830543201
    0x50d020703092117070b040209060117010f080d02011118130606051b030c060708060301020d061514030c0304020d0c0305190201080108011802060708121513060513 72
    0xc421076110015400030721014581d2001c1884401082030500c134141452101001e11500129a8040103c440003840c050840d07900a90162080d606a42d144801a0303a82d0580551008000000c0301c0002080c03082036a002080e6246c3e202900d0700c1c01c0d03030100c007603080c0c9801e400100084401400f402d01042d07280e4070064115940103107502c00e14104d14060001b110200d8000600080001501c0d9885171a0040306070907941c50040110301e03005c9280b00701c54580001420039401c0020810106801c0d5409406483d01c45d070203031904100032980c480c48640d00b1000c1e0416200802d40042e0f01c1640250900c098034400c821003c2c01c0c501d52750b01d660800c8519450010103d6201105020201c0800d1041010640890011919031400085800003504004c0146c1c086a030507030504142c80b1013034070171803598000340780d05903520b42c0c07101a2450035040718091403140b28441b80210040103000d01c00003014980d018400c0e12200320710f0b001a2804400d480f900e0140c40c1d00031420700d2901910000c968000422 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 830545683 1250 830544433 830544437
    0x120b04020f0a050a020c01050712030e01022104020a05030a031d01090e040b18011118210d08010b0f0403030c02041e020d0f09020d1202010603210809070501050d020703 74
    0xc1d0840400000800760070560950000440100d00f101e18960104206081e044013400d21508201c1155070380143d09200444e0f1204050325801601c036000ba094055458865603442e440c00c901c05484884d50b12001c00b143d041c0d01ca14006040040c007424003241c039103030291f0165600794041d00c0c49116030814a440303411160401451500002d40328080403040e500442c4100e048030001e0a1802c1c8081d01d8400c3c2501000082c0d03d00b0302c00070030100581c422900400c110081d1880300407a081d0020f24000304500d490340740c0040c03098894483e610080340440140c11151180c1d040d507600c8100118a502544941041c2e0a20420081c40480d0082001a445c580300800124809040c00080e080c01d038001c2440c020b0441e008078840c214030000d8021900746004881c002c00c80002603400081b50b0490901020307020050720400c00881c81d10039001600515080040141e00f0012108514000c5140900500016131001c0200398104404140d1a0845005958260801801e844541c0c000d5109403002c4007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 830546933 1250 830545683 830545687
    0x100903080429011412070810110f160b0c0403052d0f062710110d060b03060a05010f09060f0306080109080a1b0b010e07090e090a120e01120b0402 64
    0x10b0028030803072078580a04215410f0090500701c0c00103104481c104010303175101c5600031580a21600000044030b0040d11030845003c25070b45c1440083c000f541c03185c1511007482d031000040720804c4000c19408280d6044c8103802c6240e081c0e490041800c01340c05075000050039900001c201d8403800116005844d5210100400c000034844421741440c940241d6403211134903601301c7c000700280d0800b00300800181e04920b94176041c5128000ea11552030381005c0092100142d41d41d0488604032001100759521900b580100b0000c3c0d50300d881012005410469103140725141d1410b02150f00e501c59204126a2021138803020340150400701d0a4030062404160181019501d07040094002000d0081d10390381343c00703501d066075140b1400c400103194241e2428260046104c05001c0400586400301850440c0d0100611030f9541e00d85400c1102c69622680c04400301070050428040780100118003981c2c0a4850b0164140c2401c0c200b00548048d10800c3c145800300d50b4050300f4201c400a1900301d181c09002c0200014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 830548183 1250 830546933 830546993
    0x8010f0b0d0b10020c0a0614120c07050601030516051c020907050d0c05040f08281a010e0a0e07050d03050706142e0302100f02070f0b0c1009030804 65
    0xa950000c0e00940940103034042c84e05000c0c5d5080c04041c0c1000340a6a00d040403084441450201da84e01c1910300c185480c401100008422412346400d03100f4155100d03007601c1c202e5a590a00c070b46c0d55040e01100704201822440009980e00e4290340f8000e601180c1300310803020741100c0c0c0070030000500013410001807000070002c540306200b992003181283c40807610386940321400d001032000104415000900940e00c04401080001140c1c1402d000205041250030480b440603d42080c4082544190000c45407001d00081051100f110308184100c0201008100c60702c9109000c583d140d18601c950ba8200d03840c400c1810200348680c00601c285802500041502030200e41d58010008045032040c00c54150201c04e81d4805560001c0e1990ed840d400c83c00c002c85074296000141c0600070707000c4907000d1044c1140036442050091000d040104001204003468540d2468003440c90303840107082d503045010721881e101c40f4410078480c42c00c180750151b9444030b050f80c2d190303279950070f0380c101080860511183e18068 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 830549433 1250 830548183 830548189
    0x10503040f020310020a1d011718010f0519050105061b0f15090f0606010f0302070330060911090d050a08270105190f050702120a03020d08010f0b0d0b 66
    0x500c081050008005988201b80c0600800240b000440148108040100349156a0b880411b1152a080d064045081516002007480d400300107485081c42c694288000359032000c0c1294051072155402c800c15440641c90000c8100c12500240240d03a4008414001e224081c0300320412040407c0b2501304840c0d00d1000c0d050b203185041680740c4000d0b004034003442005000342c03003403240c001921032290041000307007044400078148c01d00c43c0e46400b0400d9808034290050611440f4421561401c03094482c82107140c80c94000d6520300215250319a55007846000204618984907803044030060208103800c3c00ca000c010042d61001c2141c0540d501e229079050500461076950080108a0070a19040415819002e07007403c100641c00c1d4190502400340142910020812344800c204207503881c003400341e0418203c3c160303054000c0c2880690402c00070808221414000511030400c45d0181d02103582d4080280400c40e00358800f40540119013045010030840c0d024640003800700d04401600129401084c4004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 830550683 1250 830549433 830549443
    0x10902040f0507030e2406010905180417040501050d090c03080301140f04020406080a0c021e0f06010e01031205030a1815050703181403070203010608060f01061706010503040f0203 79
    0x462070706640c45003400070f41505441214100c1128001134042081c02d000f03441140d403001884e035000352001034000340c44c50b80308a5070320b009410010070100080315148200840200c0450703007204d49180c2110804c410450080590703049a1050f502c0d81d141400006059001e4003a9403811124401807035000300015118001a5000e03048110340b200346540804100002e200602041c503004a104010620810350302811069000d100604040341040f26101c00f2450400405a045086821030940d810745600c08201120805032000403160140d8850504504401081c07000500c107109681c0c0b410074482c040c0c0080c580c408400303c800030b60804611400d40714420b00780012039100d0000800004000c40d540324058109501f480c04101062640c090b000429404420181c500e420203103030f0042d5034400f081114801075001d0300038402c490351454001e81d10b0900360f655600c080914000030594a2251107007130300101c9000785070708980e00ca0310015a01580090000c0d14080e44103e042c00168404010b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 830551933 1250 830550683 830550701
    0x2040f120c26012405040b0d020913031106061f09150f020d020109111509040c0305040c0e13030e03100908030703064406040c05090115120c0201090204 67
    0x350310403040c41c0901800c591000c811300f403084601540c04408640001c1884054070000d03500080c440c0601000078900180c144802940b00c208903040105151860201e840b00d580309850f880300080c0740380c20032511000115140f40d0003c1590005080032111110710001810490510988023074490342814400200c403110b910204055014400600d81e0400250b50b901843d40b00030020314400b80c0e01c8442103002c07943d1880c81781090748081c0c0c01e00d03601c400441b40c1c0180020030420074081c1e904009009041e00710740c295003802c1088000140040039980c00340c07280049401c04110b4103810f6030203860341c1e404158895050300c5161044010059a4031821040354010815141c403460050401403e0f1021500030a00d4003c0815140c0086090411032501d070501c1011141c0000e0224031034001c04074412130544000b072154006200502a105214905072582914207003d03a0303881c1c011a2540314205445800002c001c60310351100b5107407903801007495252503c00480c0610240d00040c05540c240f803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 830553183 1250 830551933 830551979
    0x309031101111b0c030a14120403150e030309030d050a0605030d08101208040b072a06080a090302030315010509130b0405060d0215071a090f0c0402040f120c 69
    0x10143c0c0c25452401200c00c120322042e00804601c503000b070101c3d46a80c258100108281e580403840d002101d400d01400941e02c400483c1c0c0317a1166034030f0504401c0402140c034240d455a20740740421410581c04001c40e40f080e0303030b82c3d00154079141484440070020500100f0101c101a521840444c150ba4244040d00000714a540ca016440c01d103031030700c1c50700114250b010647d40c2981d03132140030005103880151411201c5407000d4588816050619140351994940000c181400c08000e4421500200c1080740954665a481395519507034a281c000856441d01e401402685c414800144005001ca00c07445c10ba81061510300e003003038842e1010594000602001001035a19580354561034100340c801c00c2c1d40080c0c101c0b40611809090340100f94001c0c07807080c0c48003032071301c001812506118212000034503003c15481b410440d4903000c1c1e68192070300712030750886029000e04404441c031031400d8003c0d90291080044448030151030401f1044031441444070403100b020b1080d80c0001c1d055100000016518104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 830554433 1250 830553183 830553187
    0xb1c26120403030b030c0a06050309011d0d180b0f03101503020c1507091a0f0703050903010f0608120d09080a0908060a230603010b09042006070f03030903110111 71
    0x610b0080c098400d00000240281c4c040499030074595075151000c1c0464981c1e00f006035a0b500c4200c030007409840220f1500604081480c1400c500e10760000344290a4921a9160030100c0350419040504046500c1f407604064418880314006503060380003150480451043c0c40a03180e56862852864035950402501081d40030502d10600c11052008051185415150140520340171101602d0507215010b140700c140003a50249002e18040e40440e41c4500c00e4081c0c140e11140170f07150080141e4010311500d8081e508000185450300e81a02511050340c84040160603110404810308501ea00901505014940c5888101c40410202070050404c1d01d03071070f80c6841e05c41d42000060b80ca03040000c3c24401d80141f6065940c000d48031001540108108540c0302d00c0340030780703176400001d0240000e02201c46d84030751751906020410002e10070000580e031014442e244c0c1000001c0c1003001501648001620b1032083d1420b01000030311030740c01005a94460f081c402c5081868842071400c4480e40084880034ae500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 830555683 1250 830554433 830554441
    0x51801051306030609110f071e170a090b0309070311040209190602150c0706050c040e0f06010e010c0807020d0201090305070611010b060304030c14011b030f0b1c2612 73
    0x5801803080386d100d84074180307240c0380300f03850003a8251041c00c0c400b6147c071182d0002c510021032110440781d20982c0003c040c03175a800384140c0e421003e1703010001007000701d101d103500000c10025480942e403207040407402400f44289191a6007100025000c84180e00c40d0b401c0182d2004c5a0728900d00070401d280c10001c621282d070604170040c2c940100c2c1c0c2c0780001c45042c0e01d42040620300034442151552680500c022400b511803001030348240c0101d811055403221f44004000c844904c980b2050302c01d0009989030100540304a005558802240a001c1c00341c21080000c02c01509210052004081c030616040f8010f5580b03441301800c2055580103000041d515414040841009004012074008211001840c601f05076034050b0485050100017043c0c0c07510149001113a1070700f03600c420103601c1880ca600140e00300d036420003030003804032050400c101c1e45082c0c22440300f4184200701d0103920421a00c07511000c01961070310340d1400345503501082d810300c1040a02d040f552401024006200c18139201d07070700e6410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 830556933 1250 830555683 830555699
    0x6022203050c0108061309080415080702010606090609210c0312030c0504050609090a0e2508010504031b2901060e040e03030615090a0b0901080703020405010518010513060306 77
    0x400582c0d5504000701c400600505c0c1c1e507500459007081009000005030300300f041c98080294001c44d84104299288a628032144940041708180f1403446036000308076032501c0f10350a84210086018900004a034044140022000c100c00c90728014107100018500b2481036840003000c00c03a0390800c550005805001e035111a80500805042c44603900304070b81400e080c9004503104d401860701080c1324403544408201c2410080d072040c280c0e1140f000541c0c04603200030078080f0901802081311744100040351000104500c048c403600b40a59810394480764041c0b4a084550000c4014510548002d00104182ca4a03520718000040300c0075804030744100c43d9854554041c000c9915541003601580c24182100c0c0c81210200c00c40b81d0105d02100c0e00302c180c1131441424074890154039105034111465560114028034194041c000701c40382682d80744000d071394503801102607001d58418140412410701501030040f5050300c1604103004180b50003400c009090300b0400d000c900d6580721501195954070305100000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 830558183 1250 830556933 830556943
    0x10241403090d090e010510030903211a0f0a27020c1612050c1005041a030f07300f050f01061d0105030a110f0403050123070c0303090602220305 63
    0x4044010085117615090100300341c180100700301000c060b80d0b200510201401440128501202c642c6000c2c8280e6652000c2401010f1041a545d05801b0388032881c2054504400d5a44080c00050030415117a880c209801c20310594011040c00d20800042186481001500c040c00991842c48000d05890116420144460350341350491207040f2a0400d03000c01203980001c140e68910402c2d100d81428a0114800f102da90266070000c1c02d00c5480c00380d51441c080c03a108080c6000b17800c0c010b00007034182c5402c1410346442c00c5010105c3d40d51440015201c000041d0341c8074020fa422121100480d003008080c203924101d4904517070340d1946000f118010b00c080383c0d1001251303404603c2885240e484001d000000381083c04001d2025001c207448640010785d0b51215400c2c0e881101303400c902d868855840b072800c24040c1144202900000829040314403990340c200403491b004028984441202c4034998508601420101320b081d1101c0382c080208542c0c038901042c0007a201d00d42003081006003400c519182e8145 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 830559433 1250 830558183 830558189
    0x9190608061f121d030c060609090d0e0d080c010c0908030c031204060204080105010f091109061804090b011403011b022d100f0510241403090d09 64
    0xd058005626050030a078154800c140e64050400e44603190200010f100a49070110b000f0071031072080e25481218180000c0a0450029800c00b030b03c500d6901c42c000d2000c10b4030b00f100d41e80344541c0b080c140f54080e0360184110383d140440240c100034010603182c0340d0072503552010460842c260340d81d50b20b1140341c40e8001f020802502e0010051490700c000c52041e1030b074900844480c886107400c08808a801c005070795044800810381100207019079030f1f403001e10701c840c41e1503031003020000b41c24a51361440d281440d10484504e405d004100701e007040680d86000c2c2034410000b40c000c0d005a664007019010850035140c0c2c1340201040309188030148040b10a2600392a141d4040c0840c501c5080c440b00d50701500400c4d00c400034458400c42c24121040500d00d1a514607211420195500400c11440741b00032554102e0580d0b09080c1307005209527144c08076240300c048a107220f03490f284008410350804103100610319080c1d1554a15017030016240308400003006900035511401c843c1d012003c024102c40d0455032007801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 830560683 1250 830559433 830559439
    0x20360c0918090607030c0c0c08010506150901050315040e1b010212120412020a0b0f06011e090b13090f0c0f020601030b0112170a02070611010b0f04110919060806 71
    0x1e681000450703150740300c20150202c000c1c07507285e55800c00020700c541464a411074110102806e02d50b40c6da01514000d1405440c9140070342c441541e0883c00554603403c862144e84180e64980c61642d640402640c142c81c01c1c0c210700c3d80310340c8071680a02040010801450154044096441c514820300006407501c0b20303010502010344070503c140b0918400e000d1801e03501a8200104404103050020f0480c2050300c1101d00800e80ae10074418080d1413540030009511483c020b0f2503441c1c968403400c04224540d03c0e607000c04d1002824050041c4203c5d4807000140540243c0910001c6000e80c07955601d109662240e0003012050340c0d210725680889501c03040000790700c0d80b180050b04d038a50454443c28040141400b03040411040d501e414420000b001c8100003112084503078081c0c56001005000b51600c2c518404c2500180e80080c050000c0380d4107114010344c120004100211500d040e0041c00042c5c09070201e4006184010722010b562a151a42402105071180000944072424018082c00001d000b07082e00e40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 830561933 1250 830560683 830560729
    0x6060501020606150d0f021b070302100801140d080c071805060604030308010e04020303041508060405010801110717070b10030611250203160602070320360c09 70
    0x4501903000d000c90b00c07117502444010400b510f101c0031140123441006189000035070880ba01382d0100a01207036800583c1d00c2255041041c03040744c0001c80b030112081c02051050042c2421883d550729208008114003885904260b0901c052100040d061544503030128486021807031200050314007501c60180e200720200c41d410f05003820350710000d161110500900155503882c101203030565808005850042008a418142c10102d00310001c00f4080240e90b807500a60410001017070029040c0554030200e07401991003030410806444170741e5440d0b050180e0805010b400c1001c0e9003c1818410814411101c500c0c0b0784401518500d4200100d52001c1c00c4040340c43c5080c0324440e800643d44040915000040002c0745d04590a4000a410151509444114a2486000055010b0b00410810b00b202d008200310220907400400a0116054001140f0390242c0d12040d064007008075000b1a100c41c40e501003040c6509502501009003224054a03c000e0004010900010514004120003205600401e07120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 830563183 1250 830561933 830561959
    0x7091b08091207082215030b030a050c0607021f021c08040c050108091914010b0d020901030f03110a06090c06051e03090f03030a050901200a0e1c06060501020606 71
    0x30901d006004004100340c1300029810002200004404d02c44421540c08100c566921007820005031503c1d1b0132080401e0038852400031a00d80869010110303031300070000d410250984401c00a0715400341e181280d02220720324002a80b076100d60307041a07401d0360b6500180747c80d4031402d0385843c0000001c258601000810020040022201c41200b42115000c0c20107013000d886a507071060a00554121000e61002c0c6043c02c6402d1180c03050006001444c0c40008201c210000c1c0c06100c00c081d010000030b0b4004200300c00400c00260018403c2d8241402481c09250305510004d010b400c20f5488041915402d03101c40c0180180141412804005d04503820481d00e021034040136001c08050052041d54107120100000d074443c4030a01600500c6c0c16407400b0740b0384c0ea01d041d88006c80285401d841b40d601d690320b450412404821041001008801e00c004500d0810768070010488240c8450303c011038100c2d10b603225940c2a01d503d500e0383c4821502c01d5501242a03810403000902d010320082c0418400c8028811807 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 830564433 1250 830563183 830563213
    0x703030908030403210c050604030f1206032303040f0f080d05030105010c02040b040e070308040f0909030503040f0320060a0c080705090904080403020604081b01080c190207091b0809 80
    0x8505c00082034114001000080e107040c0c45c00c42c601c4101038004c0c0900010042099801820a00510200d0300c81d020006505143d140480b002d070300000b004900038001450f1080ca001c0c08959100c1d20b1117040780d113016168120441504030586c09030b541e100d44c14400780104041442070b00c00c051070502c0c00b42e0940d80f40c1b5000902c03051440c01c010740215503402030f6440340e40f50703608829200002e0305c00700c03a2a644c2d03030301d40303014039900c01c0c407c40041405881001c1507103d81400f4034004160107645503030031a140c0381c541e41e900300b00450003241030102c1031400d02400300c1d612081080a0000c40c000d0081450408a58025034050410102c00c0141400401942036000f400340c921806056030303503006558652800e00032074480d642010b58400e10204000450040001c0c0c000000c44603c120011082d504400540340d1100907695000800001d002e2001e100140061081050500348110780d11541e8a110200484008501d09092041c26080c1055116044a007140c0c00144480062007424506404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 830565683 1250 830564433 830564453
    0xf07050607030c1d0d0302070b0a0e01110705030d081504180515070906030c050c100603150501033f0302040524030a020f190f08070309121b08030103050703030908030403 75
    0x103a110fa020345020754207047c82001210050461029803551700c2c2c0304148054200044526142d00041c000e117800c1c446240d011456104440001d4010405401240400e84035050001c081808003591481024020341d560700550050b41c00040c2c961003004803a04100f8140f9000c0c184450b4060b00345003e0080d040e0b0b200c0340740c60481d034541c82c0c00a00195400000c0b1220b10810945407868800c40749c070b40314022203650000d001c89200d5001420079030442c01c1c412040d42c00034440542100041c110b06c03d001209484801948000c8010011204034001c2d01a480002e48501c05000030f60302003024026030812401030700351200c1100b00d0b01001740c220b2111210b540300c001c2c1010640c0d07801103022410750420301d00381c40f0b1003007108840c107500d2a05240300410383d44000d01c201c400101c40303a000c20052400f0b441a10740d040e421989240100c9601c000030342c0d2040610603e116284e8460742d081011450002c05140030758494400f500c8080d00e50305004004001da034200703011541081104000255104a0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 830566933 1250 830565683 830565737
    0x109061406120c1602040905060105030f07270902040f050118020702060912010b0a060c05010c052a0c0d050105090714030303010603092105091906020a15020f07050607030c 76
    0x501c540c0ea600120207150f0700f04c03010309002904141000500e5007003100115106050303d00a504803803c10f0a000c41e1241c2d01c94942c41507034503241d4220403c05550100100070603040300c85800c08240e03521154003090031a03a045612203512943c4030014000300084030001100c034040d44000b5424040d0796000100c0d07510540c114544160061404151600004c1d0095202d2500040c000b030071440d6a484081c1800718030320400c850552030310000c80708542c01036007900d103001c50102800c980103510103d0554040121503003d40688185128003065643c0d8101204145206500219560406030126803508846800ca902d074405d01544040c05078400100303480c1164140d10b00450781551504007a100768907104a0508149804e00c09059516000002031001650a845008035100000c010150030301d46030282c240141c010650004c0841e01c4044070742803a04181c03a00520304103d05464001503800000c1c1200c480d0081820400381c240c044c81581300c0020306007003d4200d10700140200e4483d00c8028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 830568183 1250 830566933 830566951
    0xc02061e0d0f0510210b0c07030801091806020c10061d0a05040305072306070507290703020a1e02060105181e04031709010b0a1d06042003010906140612 67
    0x110f0b0314100100c04179800708032a004040c6103e0f0303040111101d0310940c003412054010886030000059052900d03c1050001c02101190183c5540c01f40c1d03400001e98009424546544111517806011040910441000300314104c080042121030b046400c0c8100c400910003004c81d80703407804004c00300741c00c40211541658040300c2101c0e02c0d00c0030503a5994000c1020f5484159100c0c6104010405800c24001c1080c0f501900c2c01040c204c1100c0c0806604915500b00c42c500c0805c80e50210b15528000d40252507081010b0500c8a03110320110541c058039980e404d10440180d020800400c02401c140b108099141142c070030b200c5031460024060080d03c0001520780d883c92144100140906100700c0c08007102c050500d8281585007006041c071070103461800c203007e00c116407500300020155210709249100030210804030032a42c1d51034040000500c00252100310440302e00c52850308604403240114040d00c040000000e096080c00030404000e030124002c00e004500400808440f15804150b05601c00c102d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 830569433 1250 830568183 830568209
    0x5070b3001063b130b010215220b15060403170702041e0f060b13150e060f0c062d04020402040807030c03062a0c02061e0d0f0510 57
    0x10070f0040442802c140c40072415001c0950400319910001c400b1091282011524101624001a800b00441c1d00c10540305000d42d002000000c2d070b00400d40c020b260310880c21686041e00030054420105010342c1200e04880070f0b04000104107141e15115115940c0100c1030350143d08040c210781c2c5940081c9240c440801d161580411010110b5491390424001c45000581303181c28405141c0320750019000d69501d060545040001c0840c1e41d0300306805031810401c00c2c0403280909480d0030543c07100b001c0b2080741d9204104030304145065503210440203204005107540c650360f540110018450500e0400351a030300d0180d00c0301c01154003480c5c00c5400755060795941303160b00d030050b107a510018000740724940c03120034680180c280c00000c0c840303c81c82d07480450740980002d1004440a41121403a4560085580441d141719400c51031000d10500d145401184042c0c40103240c01c4254920703242c0003e11500906204200007490503000085003d01c0c00f480f1000c500501040c2010003042040000078040c1c41e0300e00e420303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 830570683 1250 830569433 830569457
    0xa0e0c2b0e010905100c140f0d0603060902010212090a09050a020c150a0b0603060d031d0a090603031709030f0a020c0402131404060e06040c09030803070801061d06040504090f05070b300106 83
    0x40c0c82103580e00c89c0508820415141e0340d1500c440030b40b44442007a40075010781e1a8a4500d40600e200711078064900030851503144d4104045040100301c064030842c0020340c20b00c21841551300070014010106146066444945860606807068660b803226007801003109102b805401e03101e1400080f495039050030071042084d09005100b0505484044c0e46502c00d2400000081c1c402569003e50b003980c1c006e503603000c200e000b9290600151007094840301c0e81c542c0104007050b101031901000d0b0600c0b4180340f0544002041b11000a01a0303000b02a01d8110903407110410056805e54003c5c44001d040c003990180706051601840840c82c080080045016039100c1c002c03041601c0c0700b8aa0b0001440d030001203a900c0c1d00700485d0052102130240640c0c008182201412140180c11200103240900700400c0c0b50716050602c0d080c000907050900f8109c2e2403800018280000500900c842000381072040b030455161200300c0110401da06800d640307e805802404280120341030412201415103030306081146100070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 830571933 1250 830570683 830570707
    0x605120706020307020f19151d130b15030103081206100e040c051608121e0406021b0d08160f02281403090a0e0c2b0e010905100c14 58
    0x3c4a00e1041000941f0808085900c690704030001a10066176507400303a24046d4201040c6900c414082c400f944028000602c00006080d60802c6012190140107481800c20451a48006d0b800c00e8204480c81500415902c9000107070030281a40080c040b10340c00d001080960340902805241d182440c0181c3d2182044c06400303010f60110368000d4041240404182d4441c00c0040494100d102d00e07002c544640341c0440c414012100008842e800e4042d03104d00940c85640da0400250301100c440c0c3c01005144180010485050000d00c814483e66200c1440504e404103800c042c1240f003003107540900045080c10f40c4266400a0441c0d5810404641c250390007158000340c7d00c043c4d400c0380008241d1106001107507940d41001c00540450740d406d50f5001c0135a6210038444c40d51613802c54403142c482c1c5092005010319000700302e808054014a41e0103103010032103d850300701550541c0710320818aea9101d0004038108001042a1160046441801c1000700800e104c020032a00f00e00f001088050b001040c0203c04070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 830573183 1250 830571933 830571949
    0x80d090201140a03141806070e0f131407031107020103021602270c1e0d0e070801090b1003030f11010f09121707050f0c0f030a030605120706020307020f 67
    0x5a078800b586440d07807807000030040c161060340f102c008801d08000c00c0304000d01d0a03224021640c045e001c1d00b81940d070918200da00c0e0075a19400c1c3da200a07c0351595949849100c1404915055040c000c100da1980210a05845030701504140c00c141c540048045840c0002065420180e42482c0150381c0b01d04d80e0345192002554900017a5000001c1040420756060185541c4500e004920f6580360740e42d0f442e4091405070256808590020150260301042c43c010200200807008101000190705440c2c84003030f0b403504005802107030490b03540741011802d20005801c030903800000400f800400034255a8020400300300c0d03d24420a10074012000c078528503080d080000402c1c03010f203041101c5400c50030000300f40400104210b0100f181010200700003910022100d100d240551109450004024100310b115801019141c40c9801403180024400c1f5060004145840da180c1d4041081420a0104050401800c8409545a0040600b08001c43d008010b85501607012141407050718484008544d6207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 830574433 1250 830573183 830573207
    0xa060843200307050708030708041215060f140411041e08011802041b020c1003060b0c0a0201180305060a0b0a05030d110d0e01170a0b0d1101030f0207080d090201 71
    0x112410315201d1108410000c00341800e58000d2088a6034144e5418030783d41c40e0302c0b0f00c59000c0d0075488200003d20100c05c07120080e12109104d03006481071948070a140b0011500e2940083c0d07000c8031110000c100d0007600b5001c0c44d5802c40704a03401c00c00c0c003240010260302840f0302d01c00d1801030418900240368290214400034001c051001c0240815082c0e01d40d071021050088074224851031414003072058102410b1401440e99095800070869040581c04110502d00325440082c1095100d40300811851440c02c080c051b00750a030030081064000c04e10004d005105461980c2085252592041001c47e0b8001001608048400320018001c00110007041a55210303410941e01840744040340141d19602c891140c00640210f402e50b01c2419904408a90000e0060501c80c0040d846012440c15008408486038110300c1c507900c009900c43d00100801c28015440400f0340780741c09413101c2c810555070103000d040f003020340c450070031440e080807903a40c0081406503103082c1c1c00c0302e943c0306407040869002e00300c400c3d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 830575539 1106 830574433 830574467
    0xd080702010f141e130e090d0203030c030703150506030106390215161415010b03130203073c030302030901050313020a060843 56
    0x403038514032103004131240304000032002c21600000081c001c005455071a6803a2602c44006030800408000807019900f081082144441c481c2c0e045035071182840c180000c03003001718001c03501c107050343c0e0304038030340085001002003003460f003005120b00c6404046a08181901c846001c40079958143c000c51100300040c10701c0c0d1001840c244511200c400d040c842020300305140998811140540107a0a03190b01040404420b000001441040411a232018014409500d4294540032500c0000c0c14900c20390102e50707d402c21580c003800420010400360080c140345105015092030111141e9014010403107a18040301540c01d0562210707811250943c000d035040030103450064900380e00042c2811120b201558801c0010713600c2d050843c0107032400d955005142d251405c00c01241c0a0301903640321100d2805205112081c5000e440f800c80701d11607850030909100c1403481074a4028240c108007034 = true := by decide +kernel

theorem cover : BRFrame.Cov 830395683 830575539 := by
  have h0 := BRFrame.cov_init 830395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 830395683 ≤ n) (h2 : n < 830575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
