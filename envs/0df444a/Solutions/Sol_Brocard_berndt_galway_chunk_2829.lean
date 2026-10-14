-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2829
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:52:10.032096+00:00
-- url     : https://prove2.me/submissions/3768c509-75f6-4499-a62f-a42a178ea875

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 508633093 ≤ n < 508812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 508634343 1250 508633093 508633123
    0xe0106080a03051b060621011b0e030f060f0a0e12070c0e063109020409080903063405090402070b0106080603030a0210020304080705070906090b0604030b040b060102 73
    0x40030143d00100814002e86803204c440040d800c42c0401076595407040e642541d02000d9402c1d038200100c00301d01000004100040049000c5015070240490100002e200c000090405010440107080c200b000c1d421040d040310043c101480c0c41500d50310003110280c07490f040c094590214481c001400c00110726071208240c0069524160752030700ca1003040f128415020014201e400055951800c08028000b04500d003850012424030b89200c412541903d010400c0215902c07100f0380d01586807441101c54052003001050f40d68611041010300c2d00c2002403040004000c0e0031800c503001d25401c18602c004012a5000e52806c00c11141d0035641c50144003a925001b503c042200428800803159040c100d034550307100d441c8580c034ac940c00e042d186d110f034054840160f4130640d075000c0c10303545076070055034450702501c0308a0070703c0c00301d0391001e051581503400005035540701c400030310440c60a4850764058881c125001c0d840c0c40e00d035540322011000020800307001d10314404002101c9034020b100c01e6181441c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 508635593 1250 508634343 508634353
    0xd0e030309010c090e1315200702030c2b030309021003020901030e030a050f0c070b0708070335040501090605090a030e04021206120f0601060f030f0510090e010608 72
    0x84030700c040c0201020b1420720300044181c500090034200c0e00030018000c0c10b10565000003240162036075004108001400409155140010394400c105002c0049120703005c82d02056448042c0d00406190048600040c0c2c400d07282c00d0080780140c0c280880c070801048808a2048005d215420240c000703045500019401c8405295200b03000b5500d54010080614240ca00300400b07071555140c15924026076101c113012400030030129400d03c0c00c600103442c110044038101d132819a16403580d0f8040341c2102c54101c0d00c00c0303000f2030940201608000203e01c46803c5040c607184c200f0142c00707004607040c54007041303003801400071021409101080d0810040140c10030010720031814403e403040c2ea03600203e08c068001440e039040403841071619008417a056030880b2200b0403281c4961040005540e6141c0060303e841c4201c250890016405100c05802440c0d2a10340d5243c4a410344c00c080c0035914001010b44244e440c0904201d07850403031850f860103548480000040411b02d2110403801400b035500315000318452 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 508636843 1250 508635593 508635601
    0x10315090213090b150f040216051504050706050a02030f03042906031902130b030304090f0f05010506090907030b060c10091a04050d050a03020d0c090504240306020d0e0303 76
    0x540040e903505114800e040c04d5951071840c0300b1420300a8641840d440300c000481401185416000f0b801da8001c078688820460400350768107454100c000b42c1080c040320b206010801400000e02c80304004110b5420309a1500300359140094031380c031507210158002c031808000314050000b255240c451110692814600c4002150403000401c14201e0301d4078424407814280c0005510340c0c0341c005000c5540900460301c2c42c0c2012080e50046c20301515010b03010711041c000003c2c40d242d940290303020307038a2038000002c0c07119021014409940050300805c0c041d150800c080b049540311450541e50103d054540000d00750310020010781e2907c90011420aa4815080c14200341007155100480d81d034403c407001400c40362072a10750f403091907080b1005445c0c2d400580d0a5134595001b80b0040c1740022091030300600d405251000c520072135602c2c0d403054000440c0f146080c050760509120300340c05441c5202416800380b00e5508209080030a82c00010040c94010038450303c03001164008501004418050300d40340d1030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 508638093 1250 508636843 508636879
    0x19030b210610060516170304110f0603040b04110402042601150503070312031b110c01110d1202090402031e100312030903121803091d0103150902 64
    0x10354450400618020000410441c4100600940031110705407542803c0c001480c02c2109403100342c2400341c1d07003000c040c500f107800c3d25030781001103203c0c80c810b440a036015134091092104a42081503d80e0083d0000c0050102084080b25080d51280d441104d100940f149a804280680140d51018400c00d40d54850714170704240080414540c030004800800000701104a0750354040d22500c40c07550587c100038818070114070112801d81c1d1000c940d007004607d80d9401c4400c010200c3d00e2041103000a039001c0e60720302c80314005000740c0528080074070305512080d10b103504264481c0c45405a540501c441302d1490000300c01c407601a1110144020400c41d181c0c941090060700c04103e120407401e04842420015165000100411701503a03000300c8040841200b06009a00511652905806210380c0c1d4a9042500e100c0d80140c0c42684115491440002c54a29010344804000d40080c411b8203d0f040500b000030300040c0d40c00381160307003290703206406078400108600100040000603400592800c601c3c69404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 508639343 1250 508638093 508638139
    0x91003060b040f1a071113060f091d0c010504260102070b090708120702040f0f0501061e030e060f13120c1401020306030d03020f13230102070b19030b 66
    0x2040ca13103d4441c00660300d6420000c070304c10312030700911441c403c244540407810505058025039910000010f07107a9100c2c056090a6110f9900000c112511402003205090308840c2040c95801054002c0602c3c1c1e0340c0000103051401103005003030000001001c00f015107000a180a8040e46186000310356642c520f00706a861000100d17601482c0d03105240c1c0001b10001c000400b4468500c40d2000a0704000d000c1d400c010141002849092806803195010070701080c0038031545d402461540c071405d0107018040249806014002400810315141414001c3d0100340401c1860b806000b918100b112076503900340c075481900d8082d1002d0030032080389000c0180329402130303810303440c1500412092121a00c1000307001e01b42c3c03104582e0950140c0044580c031901c02d0003500600101c0c40c01c46086410038218201850b03001160394402441c0401c192840f1001610b295001c421350701081c4083c0040c0d0307060288075400c510a2480000409055000403030300d00340b1991280e66000c3c4002c0010038000c2c0c500401d40d0340300d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 508640593 1250 508639343 508639349
    0x30f0207050a0309051c0602090d1a0105092404092f0f10170c0c0d051b01050103030507080c190506060901091b050904020f030414070e0c091003060b040f 68
    0x21484e94080070a05107000000f0702010703210900c50541e0340e41c43c2d40d104000383d002808001e81050960b4040310000e50b44229a01450511442e030359030641c5498200000000058100340044a00400a0940c0103800c45043c2803070038141d50200c0c04626031318085040481540d0a40e012030f003100c1074180c8481d052150362640c41c1080310760b0104100040b003008103540841d1204004109070700d20780c14104044030704a03035021080694040c200714504880300d0901344003e50300000a6000190345440d03400a9603450714019065008002a42c1140e13400f43c17a81c0300d80240a0a411004903241c0d041d40070411503900daa1911042c8001051046d00c4c10603507461003551004e1044d1b5002c0c0c000700d00c0c002144540c802c10f410f00c074400c0d5004205140306a5a5a0202003d950420740810100c140080740c2130055000c0c03072141a401114050720405d05003031618a8010425001408090040702080102602d10281c011980c1101400c0700041c1a001000d03140c0c058000200301250024000c80704030400710407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 508641843 1250 508640593 508640597
    0x603060609041b0e18150f031002120112030906140403050d0e040b0306040b060d140f032a030708160507060f020d0809060106051c020708092b12030f0207050a03 71
    0x100085440400c80c1e680201d07440300e17020b4000c600004444c070782e6440d02401c1115018244507051075501002c28103003a5244a052070841d00094800c1d4111000300d8901e00401c0c11494191483c105694002c2120030617201e020204820103103039207103030203c0b9000c03a001542e1040840343d40d5401035802030718610272500d015110354940800c440481c10042032a602c40c543c03060b8801001e0f0740301c000701b21442480c2041501d41510301c55070096810310800000034200c90fa40011515041c0a52581d01c00da800d4800100d0410f0a0300301c4c244041000000395040700c0c1e1f1140d8417603101d0040101c1d2000585034500d01604e03d02c640a8005080c03a081501440002d0003603080d101030240040c000d0701e011109559120306a03111400404c0810712490141003000c441c01411000d2000c203030508002d0b600000b800355607a003800212201e0900d043c0c0c00148143c0aa60100303040710b0341c680b5925004e06035070800500b03000012048503c0d407510a82c442d04005403181c0b0210745460040c10059a9002e03c1001240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 508643093 1250 508641843 508641857
    0x91f02031b2a0a0b0d141e100303050307050d090501090c06030f0b03060114010c0c0e0709060f0c060f02210603010609020f030a0c020c090106020d0305060901140603060609041b 78
    0x2203218201c07a42e80310a28001c0d01500d0058904402110182c1c02040078160060780e0350030b800700a0041105042c003c0d000c620380c0490310f0850100f6000780754005007204081d900d040200b04000f0341c0000c140ea520810701e05083d600c2d50810103210340502041e40d0300404551809214908100c0f0400c5004140c03030096508001c10294500c204003141c000412042d071551058004208013240030b043c10f19007000600d89810340310f00c640d5504410740e0454010801d1a0320046c02c20008581c4190042c1c000c1000385802c88014900e40d002905d540c5018401401c55030729016101c49080085d0101c4145905000d02d2071840c4102d8a41006400e40c04e4807030901c03950a003c40090020082d001b5640c4075801305812510b503490b1a00000010458402d02d90150300850f105164260740c1c0300b00b00340c000c22003034024191262440300c00800f107500c0104500d100f2880040144110f160b4200d84100d100400e0340c5256403174807100b00142e100d0044c0c050880d40035052250481e10b102c140d00b040742440c00301d40c498107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 508644343 1250 508643093 508643143
    0x130813230604080c0411450a031e050d02010204061b0b0c070c0b07120f0201090305091012090c05012604021e0d1412091f02031b 57
    0x6028411845443d140354842655104140741c0ba03481038441c203c0c141c1100c2d00c0c1481008111191451220960b0814022540304020751040e441d40340f040d110018128003503007803001c2d001030700c036010b075001c042c142180b4109141c040c0c041003440c3c01c1090744c11108440d698141c02000a02070b40c4680a15000906c81805a010080d07001401c0032407258407882d0001c4607541c0c90070031003523034000b00d20580b00840400c130001890500c64008021407400b80030210342489200002420f5003141d070b0504c00840e8501811140465400410783e803070400b08a80c501801403801204072040e11040403070790740a41c0307020103034010400900c0c1400100c90013070b21040d043c2c222466170740d9000044d0548404002400d40c00060042c5400d00038440341400b1400f15400c10f25008022400c8018030b290b003100c0f600000e92400c2120a030402c40f00045401080074146001c600704007058440004031500c1e000401e06401041183d4024010b5464482040304074400000409590310350725070b400a000b6403e051001070b52 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 508645593 1250 508644343 508644349
    0x2031b0c0f060f011505041a090a0306020d0902150306090415090501060e0403031d0a02220507080103021201020c0c040b0111030a030f0c030204120b0601200703140a020913081323 79
    0x40c1e400c40d00b6840061800ba285c00d00484029405002c0310ac0e40484e0020300800001d0b4584058003559088542c001040701e543e106001d03040144c0121401400400d0040000316035450b030700207501950051481c90320340c641030354000207002c0458000301103508100021a4807211055101d200f540a40c1e4144030f0410f00e09036456400110036101034450300440c0c8082c0c054140501503034030360600c14032626400c02100340c04c5021070b0425164803002070079403001042545010302c440e031501d0321480021031034202c0070402c840c0c1e140080d1020390b004035103800d03456001d40c0c0941940490106000e043e00d960b041c079120001c2c02022165000c02c003052030103291a0580d8800d1090384e0070b03079040f10480555060203868000a44800406e280c0c10000900013060049031502044070f140410310009104243c19460700403980010803680d016181d014418560151b81c03038401d40d5811040f81c05000b030850515048c110441e02c00c3d1594030383d106440c00000500402200b03081d2107003400fa44491501780111000b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 508646843 1250 508645593 508645597
    0x3090c050d0f02030c0f03062206181209050303270405010e040b1303080403120b03070602070e13021f0908031603020c150d0b2404061202031b0c0f060f011505 70
    0xc07a05a40301000040965003100d600b00c0c04c110039071050f1250100240d9601c2b043c0ea8030b20840d03601c01007035094503004016038003480249082580c00e01118090419001c681c0d00c0c048e04c04440d2110100101000800b15407003694061404003038000e20040d03840b0300d801c20103103500f5101221001103040014000d0704170603100e984503540c1680c03240150748464504584140d407401d091004643c0d150008801039408102580c02012a40c015106040c03400400f0500740d5001046041501c0154207103000507680c80380c08401400b00e1081d015002e00440c60125040d000c0f0760468030f003034800002e1071802d494071a541c80313401501c6503080300e091425000c140002e501c1405d114545041c0f051005030041e2403107410020680754050505640481991845440344201014680002200041c103106196005c41280d0031100d001d1415071a500342040c2c2622507050103d210000c400c004250010600f400340007030742c0c0380c201d10b00443c0e032142041890b110780084203104141403445200700300b40400c0d0141003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 508648093 1250 508646843 508646869
    0x30f0b010314030715050405101a0a0e06030703080c070b0406030203012102130b0d1a0f09160b030705090637020c100e09040501021c180303090c050d0f02030c 70
    0xc0034102400718100303060240001501c12030300c49c0141c0c0c0340800720002c28070400342900c64040c55507049450f16010305c0301e00c40e1142c21507258030058004010703060302d0006003581141d0703000b010f496032820b0300780c45182890b21940080c0703030f000344c001000146194190042c5050317542c503202c2c2c110401c004050031740a410341041c000f0741201b00251507010702105507000b00c9518002400c80391100e2515610300302c07000c1c1e01c50303004d41111800005101c80c1c00caa03007060561103810340000f042c84125030201c508201c140c074400c001400c400040010035a510880036581800300c05415141c4414142c0e2070406040900a090304040901d0031401e0b4003a4001d000c04140c0c0303e0581c01400e4400040c5c0c05110010210030080d50620041c0000c0d010107031a00f01c4400d126074006c50006856000f681c111540c07010a070028000720b60304090b8070007002d4030040f980d0896241e050500141d03001640c9841c10454180781c0c001d0380c2c404141e40d103540a12107098440c0e403004d4401c400340d43c00d5844a02c2005040483d40c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 508649343 1250 508648093 508648103
    0x501020d03050402091b0d02070b09060105010c0803130c0911090f060405010903151d070608060d08041e32150f0c030f04170c10080705070c030f0b0103140307 70
    0xc0210b0440c1b80c20404c1d00709110001c450a41c035264175509100160780c44814122814a024000c20203402014404a809400c00b480d10300a0705004e502c42d4003035800003401c101880d01d10418040100201c1c100c0b00f43c010702446c9004d104210740740c5040c2a05410180e0300502030720072550189070600d0100c04640903160140c45000038181507881e207440e10781001d003c030391140d40e030b9896a00540340105440c0b0424140d5000600102e82442802003c0da030780078220900034100601c8900000c0c0c0d07217406236026118501e1860b10181011b103402c070795009859104241c1040480055001c166000b0807006c11300860000e082c0300c81105d00107201c3c0d9000f840c0b2901e031000c5000c0c401055100f41520040038801510400c4905060300e280409000d940300394085a01e541c0032100d0702d03580c0d4600384803001021b40100d8252002181140000e0041c0d0801400c13402041800207020040105050810002d1900180703803d1a00d019131a0005203aa001e00080c0d500301c0c40d100d4841440d60740001220720303d96200c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 508650593 1250 508649343 508649359
    0x14070503070c0503090a092a0c0605070315080610050a08120c07090212151206040212070b07080d0e0a050703020105090f040207031e02030c070b130f0f0501020d03050402 75
    0x49071003112075211200381240c050100300721072002d80e661b049484000c6c200b42c42c00010603400f8501c40b9440808245d00c4084006200f10304502d500380c01408148080d500104040307416031b21220120002c00e083c1010010460000c10046002c2e400000c019100f040c00328002d000395600c54082004002a611995000f030b88518400600c548468000d0184190000704443ea1a51212a003200b81d80001480c01c0100140c0310800442d004070342540e0400036000e03030319200c141109010803503c40300c00a01c041d0103000d200c003540700203010030020040288405070403251100d01916184a055108544121507581800d01c4040d1109001c80c0c9030500b0f50780200200000b6207981e0040d01c0540080f400c0b140d20000030350312166580c03118001084035900c03d96412507080440c0c1c0d1407610f14100400001d0440d88107210700741401e800041d0200030b540448081503140c0c180b00800002030740d19500440180c00c1083c10011700311101c4c00b05101614001d03000e644901c20807500c00c0303017103602c1281d01a51049d04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 508651843 1250 508650593 508650601
    0xc09050414240a020f121503010c08040305030a090c051306030b0c09060a030b010e150c0d090810110d060e040512030f01050d11100c020a17030306091504050103030f020114070503 79
    0x20a50003050042d115085084c01e00046c80240c40800c20111b49014800407900002c2900307280070320844503c03407510700300300c4d202d803c05440043c09400010320050050765a90500000d0105200180e8000d050003000071080807002804640603100314031080360344821b00d0300400c2c0103110100550f054020090b001074104000104220060140000743d03d040c845041441401c3d034842a0028514200c20001c0c2d59a900c04508524a04411814148208000f8103000c1c00101d4001c00e5441108960b110041180440750f200c0041c07602c10710740407980359450306000180e03404059540314031403400380040d104032000d040203036040703032008440350004030340d0103070051003d0710b810384000049501072010003200c4400b40b400300d410020b008881201242e489400c800440c54412900005010310104101d045841131455030307540c1c040600070b2841002101d002420b20300300b10303c00286030b540c01401401315503034030b0030041c2405c01200101801035007040302030854107203000d9055002d02e0f81e5030b40c0c451031582c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 508653093 1250 508651843 508651861
    0x40f020117130b0f1e150a0b1804060b0f130b0705060106080c03070c0b07050c0609061b07020913030c05010c17060103020a170601231305031603060203040c0905041424 74
    0x1e100c038000c20700c0b0354100041b584400e540000603101c580d007419580d00fa01d1180030000c468040d021031085091980074403105d000c0e2000d859101c900008030315155940c60000311008501d913044489828070208050007801000601c190488085441b4a0200d40b6041034500c603610041303913640003080100d51100c0006806c02c1c14150301580c2481c0c03181c1448640c0c40c20900f001003d456038049540701c0c0d01400400b00b0340c0c044542100c01c4030303030002d0f00d051145c0e80450940c0e000140300c4031900c00758250703000a0501448000b140d0f154894003c000021086001a10030080396440c003004006407800a0a02d5000e442118000c048603202c0c800c0300300076903240600644000f000307541000004850000c41401c408001002600203410054590807404481c5007003c9441d4000e0744641c1c0441143e2202c29032003900a010713260400805070303881e038650a003016500840e40c018564a46410200f00500c800154541d45514040c000e0f1810380e8080c0d11800e008055144608903961503940100318011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 508654343 1250 508653093 508653151
    0x30606070c12060605011d15030912130303020d140306040c051c09113a0b0405031804020c0705010e0a0509100911030f040f020117130b0f 61
    0x192003015992072203a107030704056440282110b000c980458030340c0400e0000e9070b00320103a68604800ea40c11041c6e4140c1290000d85008440074203005000d0001004c14003111060200d0002c241300a0761144c5d546000c40c0780c0e680750008500c41600140503d0b9110400203110300d0300c03c80741d0403098507564107580304c080400000f08031118007032040c0001008412020b08410544550008100c100014400348c503050074002c0500d1018050720411460110007420203030642011002c500e507040380f40390120140082605100d44040250264006408000800c40000024140410511100f804030306070103003844164019a0003190941d041441d040c401544190502c400d0340400500711021b265035840840d5110400351031145050044038800d0154140b0750090610941c103040515141d4075007030300402d8a48401502c001c009075022240c40007568891100c0d01030940c040c010004082c101150081414400c2260464040c09c06200207070b5001c95023141c40c0e200b090b011500c1204110260300204140d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 508655593 1250 508654343 508654357
    0x40809060306040f05010b0a0306080c210c0a091a030c060406030902010909050103060c14041a0901020115060201060614030615030c131211040b240c010207080405011112030606 78
    0x106942d04c1a620480c5194000c25000388080a9025aa00740e22600101a03515a41100c90300380e0103120300202c60348600c07401c000c0d03e000c404008460303070903080441410804d18840f142d030700c2104c80c40e000c1604096603102c407807021070310380c0b44643d041c15610506464040451842c1e500c00c80c2400f04021071402034002c661541e00c149021800c1076103901c2c010b011544280c000342c4481c3da0351410b00c001c240c0c002480d040184004c102d041d04062415099007c24000f01402140841c004110315895034000d40100b00c41840c0c41c0815021143c0b00e000003802003040b03100d01d400040d101003040d043d110001040b24007418000e440140c0041080c0c042840c55070018103130145e2250704111584003203060301c078800c0c050009200d9420300301e0700d1410a85034915072104514491494000446d1443d03940c60b5201c2c6080f1103804125800060f015506080340c01040780610965000088140c00c00201c18020030079200262210729010300040340381640d6401389860901020f000f000815410f03e0880054900f13 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 508656843 1250 508655593 508655599
    0x2060114030f030f1e0309060c070f06090b07020d0323070c08040303050d062403050406020c01091b060905010807050c122704290f100c060605030303040809060306 72
    0x21841502c000c0c589540c1c0304008401d4040c002090070350440f6400b07200900d803004c09500b2039082d03007094484142c440310054010703016a403001582504000204680002c583c1d00008200426042030a2100440d0710448071240140103107070000c5482806842038080c1c20901c5a110034000d000030380c001200c11300c040c0030b107002d200340341040b04005050707080100003551084c0c0c0c8664032107500740c2c081070603100c154205003030070389508105942202e4411485500482c4610340810740341c444e03080c40d100a210b0303c2030040c100c0d42004400d6040c888060220034a608114070348243d1540d44000840b66035200e070040340d0015130510042a040b51140001c0c0084520b420300b5181c03840300701018901198403402d05189004090210a024051010241c3e14030803c203079800e0003850120801d12200d0031950340d88241e11140c440c06001c194a4050f10f585044a000d401307580b082d28039480240165410300c0007110850306000c00400c0505003c02a240940e50080f107003400c1c520008100305080d04001c00650b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 508658093 1250 508656843 508656853
    0x5091008010608031b070b0708071b081b0d030207270f0b192d12060b1c030507020103023109150315020304020a0801020a020102280206011403 63
    0x9035a0020711a000c01404020011a951a02a60910301c2c22070340100c00329840c0c0010501304949175000302180c1149600040702a600c0d201494003d002562a0204402141030000041000c3c480001c80c0c0a210b552000720310710101c90002007210300b06016800400503005004104200031124441c41c070038500181d1501d1034049892171040c116903401503038000040e00c505802c0c42c3c0c1d080050f0224000f10401048201103800c041c8903038100321803a0092404030085624101d81c00d000e202c003400c06808821184540c40750075041c82c002420001103528404e1082400d00c050711010300402c1c1c5110f0380d1503168a421f142054006400139000f10500a049031403404404203000e1729403584590317069a50303240a1815040c08400b400300d072180010100811a0546c0c1403020860556005140b1a402c02000d603481d0750340d01c0415a80d402503840b41d4007a60003c101022003503010b401429440b154a100340c20080204401c0445600760600c940001d6008100103110620503462111200240074003150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 508659343 1250 508658093 508658099
    0x6050c2a0d02030f1501060e041a010809030d110a14130303080a0603050f070e07030e030d0e0106051c110103020406203a0f0207210b0405060601090519050910 70
    0x500302481161808000e170341090050001c980c2040c2c070000d01100c2a5420441c0000010f03000c800c8002184500707042c0801140010900790341001210660000344000303100b200c0c0c509408078420703000071002c00c010070748001210071086001c8081d40c80c10060111503182d010f181d40c80c00d40e00880098860440103841b04c0300400419010419003d01c84401c400414150b4941100e10031a40000740040301014100064401c15007000401c3c2c410b4500800c0000600d6030203030310510300410345680001c0e0060409801081c041c1a04c0950100c8107000c1c0c1001e64030809100c004404a114074024480410860401080755502401c000d5145c4041c61045075152440030441030806586040080c003892182090512884402d6102c1660100c87e030500ca00c50b00080034019417144a68001e48004500c1c6100100261600b9a407149146810612415079801e05050194440d841202c07514007082c80481e0010b11b90070075400c0d0b00d5540740e40c28211792082d41801c0802005190192050740400303140c080c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 508660593 1250 508659343 508659373
    0x3030a11040e010b1b01020c0a08030a0905120c010f050415020d1104140a122315040c03110306060906040e010e0f01060f060f022e0606050c2a0d0203 66
    0x34007900300142032607145e90100365100d008401c1c041407103800fa40180710040b2110b074009102d4003060f41c040c0b00d0ba40c607039641d8480040101456480a0000d10402d40e8110807440d90360300500320903600c28000e003c04ca0030990010181d41095500400c00c90225041c0c400c1e00355070340c2c081d00c04d6150348500455010255004c01500f60002e8220346801e2050010118091429800c80e4004003002000b001c89100b0b240c6800c405868440d200c01204544011012110201071018141041c0d001c02d400106080c641440149080341e40012241c01d0401580600d051400103072151262000030440504ca40d503100c24800a05100703100180d066481e200680d01e2100c09000e5500500303c000000200d140ca04085240302d010340741c1c411401e1114403400981c481e9408a01106464041d030701159100c500051540205442e00100f82131039840c0040105096500200810b11948000300b10341c2d1f04440010f22641010012900181004440210b80c4090a10b4001c4811507030004094501941100342c02c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 508661843 1250 508660593 508660619
    0x100e03070815070f0203130f140d11090c0d0606200102031003021e03060114040b10020a0303200c06040c0b1303060b01180f03050d0f020c04090203070812090307060e0303030a1104 79
    0x80c04800c540348030078042784003200840010524102c51000006a00d62a814003c00c60614124040c003d880005801e0300b2001003140c041c0c01100100300301e2640e8840e00100000554480c0e4154880d401110780c810100500a9070702a00d10f41c1a2055801c0c50341e0300300144a55185041529148561203081040d03509003c0903000780031501014100101040400c011074007031000651148014a02810900360300040034400305034181000203000c034000c5600007442140c0c1c0000100c090340003400901c010000f01c0d405010303603c146100c0b00e0351600c42030881c65a005010300c0361826890b090042000c0760440d08000c2d06120107041c034950402e00940b90001c482000d0b0428204a080e00108104200040043c03a20032030f0f25149c80354450303d0702c000007515041a4a0940c2c4143d4031841d04d0815542c043c01b001008003180001c40f01c106803121044402a0404503030b10b4440d025165001403500d000b60285010100000c01840c0703141c0c2c43c070b08160001c1407205021070f100001840045112200019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 508663093 1250 508661843 508661849
    0x5150a2708010f0e0106090204060f030b0609060309031801020f0a0818030105131101030b220b0616110303030402031f0b0a0e01091811100e100e03070815070f020313 73
    0x100100b081d0072404c40050039500907a122100341e51041108204807070b401400d180807901145004502003403684001022070140c440c09960000340041070002d02c1c5000030081c109102808002081c88540c01e005a0715030009090050940c0c00600d501400580b4002c01045140000c60020070304150460100342102e400300c1b0800c0700c9010720307841042400b11a040702e04000e102442c05006207910840425401032115040c441c0300d0f001018440610101a00002c892003400b501050316412a407030380c0301001103010425110b0325031030b0a010546084c00b00482e84036070b40190060003840c2d088040e544035034540810107800540c2e11240f481241c1d4401c80c001d0024802c0c094404c581f941465103060448400100c903080b030840105d039810009034140071020040b0801c81c1d40b1190001100403c0e18000c10320211a070340203121070328100b410758203c803032403000b00010b40c02ca407840790722046980e0b50b80b02d1100ea601d1200c441e80000900c070703d100b42000c02c00e40d0261b02c1524202480010701103190090350f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 508664343 1250 508663093 508663121
    0x703050f12041401030209010c0f0c091104030512070309150c14030306011d010513030c030302011b020606101b12030515010c02090a0204080709050105150a270801 72
    0x18006610302601044003007510034440300d4092038940380c141e4001000e0320364448a030515030041140d003120307802040041d1100d03412041603500d046080c40c00b07299a05840c085c00110f1843d2070502c00060f0807030815901520340c800001e1014526000b030b403900d1500908812810000320210100d13306034103403a510001889034a03000d0445010349815085142c0059030144070382d2050041100d1607902c00e01c00d41c0860781d0f10800c801b01b0201a4012100752080c00c895181104045030004108150010808212402030303008109070000c41207850314004418142c0001a88101c02180480c54501e0480c00340a0040c10b0180b940043c69245400ca142590026180c00c03070307080d0000840d95014022154000380c1c1c404809079190303800e00041c0c2459502c81001e8000d420100010300007940c15411100a00341032401c4580715a5160081000b40c402401014041d00c00d10454a01d0940a8010b8516403003190300c0300d4030346204030904041c11800d00e20101480b180d0302000000c0c0030801f84610700341e0102134 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 508665593 1250 508664343 508664353
    0x60409050f0105121e100603050703021201050f0114010207150206040302060c040b040603050903130f080c0f0d020405132a0f08030913200405011e230705070305 71
    0x10481c4644610705a01c001d01880030800885891000400d00d501282080169040c0e814004030480f403030100e1260504c110540303010404020f2190020b01c003022030b88215030f0b500540c503003151028240e50040e911072459280c4500140915030142110144180b0103104403401140d40310140c40d41c1c280700721114005a0000030a00c824554103000255120300215500d92901e481c1c13807400d174654031441c0314403010144d42d00d000c1440c00d1802e004803074602540d002c0304090513807254051483d0f900b040c0308414a51144104100140c100320720252003044005090a90030072194081c040500001045a100030024821510005003d200100d01d0551103a82030309616400e4120720481c03074040d820400c0082e02901e070030003685000208544805c3c805840400416020070302c0319015005400101000c0d50801c1c010101011100c0060012501c1c04d903110b2115440b2604003d21880b00f21107808001901307845801c59070f400c01c01513001414010801c3d0b900e00071190302c410b418000030b038000311229002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 508666843 1250 508665593 508665601
    0x405130203071a0f0f3006090405030d0905070b0a0201231501120b0904060209040b011805040e0a0f0501141509071404080f0a060b010f0c150603080307031506050703020c1203040506040905 83
    0x6000d072110381c1f001054500c1300741c900740394481959030f001d0030f03107042c0b8035035200e00030300b0304019040c400480288004103540344c8035100990040d0192507a1420b056403da06542204401e02940030382602403558903444441c0c0d40d9405004550301500f10100901280d00d500050140c4d4075140c22140c4518091000140c031240c9843c100015214501021810019820070a40b2120451001c0c0390440c0c508603400146040b800c1501d500b4510300e0b4001420380e06c04501580c05100c070640006031806030480ea0343c0181e0b5200881034030305107500c01c10b450304250001c0000d00c0c0c903070081080e80640c42c8041c0d1102d041550300c140031480e080109504801e41e810641034038040003000e008e03070303000840c090030000020040d0050080c50244004405440910620380009055640c1c0d0702130307000b454200100964a01c0c1000e005000b510000c219aa50440321400024640384204140d0b0185585503010704030488111007040707038208200004000314042040001015a02d010080c170061401c03000100782450 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 508668093 1250 508666843 508666927
    0x30304060c020d0f090e0615181c050318031c0513120b04080a0c0f050c090a061d04060212010806180a11041a0405130203071a0f0f 58
    0x10f001c800410301c002007803c1d820740fa0700102d04a0a03104002e05000c034a60b42d0310002512814103003d1607103c110f00003080c0744404880d085505100e1000d43d400406207200d00342c204107182c2c0400c00900ba980060104040504000c425582d140303900400301c0e0304100d503a09405005d17280c0c0c0d2240030003041c00064200c40c00c69072054444000d185000c44005107a80302d4032006a0303010001c0c40101024000545800b035a4042c400c017901341500300d4a2408017540c0c0d4940155910010380354684103244800018031031035014011103040e18242412400a200071419071548148081c1007107030115000e00c00300c44c050228805040c001c00c1400000d00d0141062440d1440490261010404540111040e40e000c510051215040c000080c3e40004400c01998040c1d504440002c80850b440b5040c00b0500051304920795407440c0c940d008400340c5080075542c800c0f01c212107032110501d042d611000e0011120a280d200054440412407054441c40d20f07102c00c080e0b402c441903680540d0032803000c6011000d40c4e60 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 508669343 1250 508668093 508668103
    0x1207022d010b1c0212100609020309010b0d030207120203120a0e0a090b0a0b0315040c0201051902070c030209070c0501140a0e06070903060b060403020a0e06090601021903140c030304060c02 83
    0x82c2c07122a0f03021000c03109445407003015075000e40103074540340010400000400180fa200e5820704c1d030820006031a00e20400c080d51040d40c0c00103031b541c204a00440503240a45544003103950640042410515010709021070341c114a5082e030f454001d104007150f018144a004000e44003103036607601081c4507813100b0000f414541c2e0308801e11041c5400071080c419182e004008041d60030030f0705a19207990f152210b8009000c42c0d042c54940160400d400c2c84461a015004240200c014040c1c0140081c51503003803904900900c140034118540b5010100090304120407015001300603881d11a1b0903210b151503071802c0d01d811440980801d030301a02002003802003403080c180081c04200290409003800d0100621103a051f00019103000e94452a03141b10783d0303c030000c1f14011a0f010304000f080036512034082c1d0034010300b214414003034101d18000a2039984081003814820560b0541805d0f1000540c41c01c4440d40d00c000703388804414100800007490000700041c500c80c9108140226014003000d1009041c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 508670593 1250 508669343 508669361
    0x191104050702071211040e010e0c010e0607080d020a021203093d050a0e010c0302031e0c0a05070203010f110a091a0f1602180103060608060c1207022d01 67
    0x41d00003900034415804090145055250446050b100ca6481700c400900181280b8004c1002c1d58a05000ea01044e0400702c1e0302c1c3c04c600d0098031a4000700203c80180030311841200c00042550300308000410307108205130701a002203822481207511b00c6100c00000b070a03992043e109041c003644542a5105041020707246414070300a9440800343c0b08a034103081048900c016408100410745440000d005a0000e9001c001c1c400c0141c0024800700000c0350000d070087d8000e41e98183c410488003074200030340b0340050003240640005542285840e40c11001140c07260010403080b07038907548410003451030504600400708090f071450441680d88203900c1016011603150340c45142450000d03840c00d0f20750a0b40d0170030f0b1140b0f0000115100d580d0100c3c0c19142807040c80f4884001e5000041071070145510ba245603040781070b00d103e18010885c0a4075182101e540f400c3c05c41390400001c40410581d9080d10b01d032401c190308110280120341100e0a1221059228124654800c410420007550904000c409014a1040d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 508671843 1250 508670593 508670597
    0x80c010b0d03050901030b28080708010c08041212050a0b1306030215090d05070b0406091a03070c1406010603020d0c0813080a120603050a0c0803030f0609091911040507 74
    0x5940e6594090800e004052815050551f0b5000410054541ca00403030000013483c07600c040d6001100d14000e940300320300d000e0302c0d0380c0b44120f0b48081000101441640441882900d521245603226540d008000c1e468902a0040040c02001303240e5150450040a004803600700c1e02061801d180024000001c0f0441010020f03203007001010000b40c1c444402403140e4000c1511110303940c00e10b103c003045150740d107020001c00d03e1141200c00a003000e0040e020f401a41d0950b03a0b000d040329610369450070860420104401003e10410105515600581c8007902091058010000705110041500d0400380240e00460100760009000c03035140d2110311072000306014604043d406c50400341044190382c3c4101c00c00401d8031000003040d01d15103000740080d81d003c1007606410f200450f101c0c42c04d5a2540408482226400000900454919030105c00d480c0700b020501c50704039255451100700072600c4c402401d1700d04903000e00c40c0d20101030411000440911400303201294100203100c1c1c280720480b10010100f6007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 508673093 1250 508671843 508671859
    0x200d0e010507020a0905070e03060f0114030d02030405060d0e19020108010f0e010b250f0302122d0d020711030c0103051b03091c1205070201051003031d060304080c010b 74
    0x40144e503020000c100f03807229020009107683d83da0900f510761071aa07040d4150305204000030032268000009030a416655013400700d1f00e921408209140c1d94010658036030026802c10320050105003441d4002d07000000103120007042152002c0710060500195140c1c0c0034100403c2c2c0e9451056580003c120f6004003c42501500d00174900503100f200c0c00c2e810302a11380c50040000d60400c003110350615071140d200c011310401d040c40c401c900e0812014000303001c0860150050030718003094407501c803082c0e603098080305401d0a40b100c030081d020441e41c0c00c10031103810103200030302101003455568070280a204d4400d401d0100c61140c418101440c11301c107409140e0400d8101300800444250035814103156000700b07505603841e40c132414100c0d0304100104019810101850780703100c620b56809854012003490000707003041070b51a1960100c1c03d90760202d4100441103440a4100002403080c5058902100080c0c00120201c40c003200154981c0c1c01036900f0380d2a80d5000c1900d800c3c1100030300c603a8450001c1210128 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 508674343 1250 508673093 508673107
    0xd030b010f12050c09090f010810021801050714030d061403010501030519080d1433010f05093c0f130212070f20120a200d0e0105 57
    0x1890144032040468255490f4008101201800429910b0021004110006c1d916001d055082c0610091144d000d45101d103400101004c155403003110b6503110715400303c405205140e4015112544803e004650000c0e500d508030001d00c4c03050000d03000c07007140e0f44400310b00c02e40f5104004810300030080002d84030342d1403c40100700141d80083e030408031040c09184100929028284003081e03001d0031190303000701420299007200740d4540000040c843c0030010b001c1c02e0443e001c6295440e8501c11a9040d240040d8045403242540d8041c074101101c25001e884c0c200d02c2d0540040100302e002c90303109c004c10340210500f00a07199610341b014a4034520b55081d129403110240c40d40c00503500040c0000c0c06030054060802d050081c00d45030f01128204010a48085802c0c1080342000740140c2c44000b004000030305120b149107401078480d91001c3c2d002c0c0b03120010440e07000c198149401551000098a06010104072009204002c5100e1001c01d45004005410f604001e0b81e005800c0500558003d41002401c204607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 508675593 1250 508674343 508674347
    0x1a12030f04091e06030f06060b120106080606040801110304030818030306060d020702030a030c02031204140415030c0b0a0f08090d2f01020d060801050603280c06020d030b010f 77
    0x15404448481502150981c8a561004000c00344890000320341801c1c10344c04814001035030980704902c0d10036041003098070350700c101d494800d003d2002c0001d504126a4010002c0320702c1030f000c41d900840018000341c9070a945058003400c4480550728200940c030f010007004241508840250b91101140008140c00d84031580c0d0700352288002025903204020120b0780c501d40f40c2090303040e1000ca030360150031a04400141e04001d05000c4032400f04038800d100d910300c1c05002c6c2e400c003010f840c04c55865403841c6036491004410040640b000d105c1d4440b402901150000115041803903c6004041c07d0002c00e40d1440e88050040c40311084200c030350148a4848103120400710002958445c0c0c038020304c0e0411018024055104001900503a0352601402c1c0d11b8407150095410342c0200f2243c3c0d503030501080340c2039440c03880c5400ea0b24200d88e040da00d03030060055100b40081d49500b40300c4015081c3c100f8103c021340355a8112086205403c1000141c1c040803079010116014410b65082c07103000d0038004902000c1d1080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 508676843 1250 508675593 508675597
    0x5120705030d1101110a0e0a09020903150901020706060b0a020f0601050d020915030f010213120b0612150408040504050619060e060408070303051e03010f05010507020f03011a12030f 80
    0x340c03004014400020f5070b4804002c5d07000f640010072100402e0741d03c02e842c84005010b0002c0c80251803050310311000018070200c644c802c9407442400030300a403c2c44040318880c1d8400c0346004080380c01c1c80d5000c10144000551500c1003402909900e2a2140c4402032448002d1901d4040d5181e20041ea2190006010310796032106201c0e00958115084c10f803589c4c50305000252001540ca1450300343c800d000c4001144101900030705000b60002c0c044c00c0700e40e940d13207101c00f1030504400f4000c0d203500400404140c040c00c000302c0014800c00718804032007607507000071000751090303c003200c5c184d4941801203800c0c40030f460b00e8041c2540090b002c880c070000d0100e0030342c501c5246081505c2800244001001c1c0300742c143c0c6843d000e607001005094290f4049540e01e040c040c002d03900410304041c240a03103000c03c003000c203c01c000782da05175038680096046503030801c0015502c603032000704c050340d004070455601200c0b03a07003d0081105050300e40f048000e460265006000104c1490701c00c10016400500231a1a47c40302d40703007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 508678093 1250 508676843 508676863
    0x2010c1404050f0d0f17040504140c030606073f02010e1b0f0604092a09090209060f0c0d030b060f093d021605130b040b0d0302070512070503 62
    0x2e005a4a01c4403031808091180059071700501ca20704a8052038000c01600000d081154000d0303c00388182c1c4201c0301200240c80049a003005072980074804507009041c400c006e415054401e175030607a801c54154182c2c210341101010040300d281c81d549810080704644a00b011541045c42c0000d105040c021104240c83e0790701880d400d5038041a014043c10f69540d01130a00b40c03280b9026103001d80d42d0b40c94941020140c50103d0020407810310030900300c0d2480c1e0103420401c1d55951785548405003141040402c00c003a50202e00303115488201803010b0703908111480000e0414241c00001480d44940e0110040c0a450110f03001904c02c500c188140c0404c5024042103913080381084982c40c00344a03c0001c0598560780e1004803001480101c000e01c07009030803048030090000c802d5005c4811541d0209101510703400e241c0100b9400010500e0146020029074010602079100180045044246d84000c2806211007100990040e880300e1010080c030304011812000c1411201c0181402e83e040c100460355441001c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 508679343 1250 508678093 508678099
    0x9080307031d0d050a021207080d030203190c030905010605150f09061905040305060f10060503100503010c0306030204050a02091f030213090b1f020c060a0c050d02010c1404050f 78
    0xe40c0c06180c118401042c12510b010050200d0854996810030990301d40040340c00b2402286408a0301032140d50010365103089945810082004002c0c214088010790005404e80702d0140101032000b500c0f400390b026201c4c190a403541e0002e54880c060600c5404d5800c250b0241e03004051068a9800707428200044666290100034610f60f03d8103481c0118040c0c1c814901950301d14440c040740c0440c1168410000d01c01c8030b004404684e8030b601c1c0c001c001d803010001510140c018800400d030412141d070040b4044c0d0b61211140c04544e440541d43c0011a003076034071400201000aa60340340500862034244600d54210750300c2a802c5083c07000e044041000e03400100012408031000e81c1020003098860f030101d4554166410045501655401c0034201401d1440100c034425107042000b01003c440407541e031050031340742e42d0040c441e1007180024030003a50301005090381040f0040a0180c0461410003000714503448036400020100c100308070040002154076184441c3c0f8a0422003003046a40d01341000d41c44090803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 508680593 1250 508679343 508679357
    0x91a091b2d0f09030f0601080624030a06061809051b0d0f0f0201092c0702070504020403050d110f100c120e0f060c0a0804110a0305100203090d0908030703 68
    0x381a030807018402401480184820014840480c07041c4800a052003c0c4150112050781104d1041e403034a9000c2401110103070781c020000a21501c0e09080c00300740c0b500884404180030000f602c0483c1c00c141c102201070304c200d601c0d801c00304820000c1003586103100c0140302c41080800581d035121034882d45502031204250b024050606810781d21420340895030f40e4841c003200040080d80c60110072001d540942680451a100400207500c9200c4824400c0001c80c80700c40070300c0c01088d0210b80a9000050500b00461180c0c4002141c40c0c0c44500c014405940264006e00b481c0300032180045c0102560007100445410003250704552030320010b840350001c460001d0224814035461801c0394a240c2404d01c03500400d080c10380b8200810408a001c0c8405034852055452940d601c26543e02640b0030b50480da03000a1040d80003d004c10700c8800180300d02030000300f1403080709940c2d40b5034510740080d024044468680c00014071080c01400c119000000009040444802d840c080c8444c0d124050b40002030140085 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 508681843 1250 508680593 508680637
    0x703030503060d061d10050606040b1905040801110d39120c0c120e030d12090204020301032d08030115020c0405010b040303030609020c071806091a091b 67
    0x103160030030300411444e0308017044014007034115a035454050800300340905103040e0110b04a801d0090031102074500e4000303550314055030001e002248515100030f0703c04100c1c0510000c034004030203000c0c01d0140d450396066103440340843750b807038421140315544205208910805507041003400b40c076080403401e020034000b221041c50000c01c0e01e40081c40ca101304655441d042104608a40011019648a001b407403034100c0780c400d5160540da865441c00189a040d40908034102c0d4092050412200200407118080360003402c0394041003c0e80c0080c0c004903101d540710308480c80c08000c0c03012142401c090880c03e10000340e5498039030001500c0180140500500002c002c0030180380200b08030802603501030000c110540c2d40d126000c41c0f0360461301045000a00f040c500080401090007038601001042c0007420b0340e40c0c80c12025900010030b014a1100858413440c0000c2c62010a100d610030558a400c40d05100d5015001048800e41c0000e110310b0303140c8001c001d000c1034000c9401c192251500e48005c03040d01401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 508683093 1250 508681843 508681853
    0x105251101090213050f070309110f010c02040f32040314120103060c0f0e06040e063d03092102070b0d1a180f040f14010507110703030503060d 63
    0x21001c40c043d4201d41e441d0b121403410180765002c640b2a458846d0011400d4958003000c40641d01070540280c004820900d0804251800c0c2600860a1005041c0044c1c0e00001c0d44c0454141d400d0082400c080507601c0c41410310f96003942169240440352808100f440c0b00c0501000f0004150183c03015040100480765032a0200c06201200c0311940d10070b000d0005981d50745840d0001c1d03c1168514400240c031405964201801a4010020b141c002042603080c142840110720302030344014000c90740441907a10b0180d02c07100784401c10b5458030350043c070603040f1019500000701002d400c014604c00c0500e4003081401081074280300d0740702e03080700e00c019840e8540a00c1b0704926003a03030364001100300580080d801c1c07852102170344000746240004180e21118510b607820032071900c424510742c1a0f4845c1c130800042c2c080c442100810303032091290400201d0442c0360380360b05a03004c0010501241c4c0c2d030b40d50024011031a41013105811510b000000500c020f80c01d43e54001d0050002a0605004d03400c00015041046 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 508684343 1250 508683093 508683101
    0x60a030308011a091905040605011b060b03030712030b01030507050309100b0111160806160f050a090e0f061e01090306050a06050306040f06150e1303030e010f06080105251101 77
    0x2031401032802c1e07100c00c0c001598445801d11703403081c28491894001c00260701e5010f2106050200800110380020988607121200982411403100e645400200039034400140400780d0003203140781541d00051042901c40015003140d1025104109101007881040400c00c00000d5844000360413110201c2c2402110005a030100051003490306180a030481c1803031030008045c41c12044692010032200c5584402001c01c006070050b00001001462910f0180d021a000750020143c490700d03440d10545141d03807801c0a0050000c25a00b00f40c4c540d0902080c00b2031854500702d210ba5000f10a481d0b503400d1002c860019003409078500c4010107503030719032000440703d000c1a13001000030840903056525510b020b180400200c0320a05080350700510b40305003034284101031032119055481004030285251a103800e000d901c2d4040d008200c08140d25422114803c0f0021b018485020300002c1c0042007082c18a6141c5017034138802007d9510400d1485102842e00506c118007065080c071074140300e444e1008d400c090f28050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 508685593 1250 508684343 508684357
    0x114042d1104081006090e0a261c0c0f09140a05060a050a021504051207051e0f0c1c0605040f1719030b01020a1b081e06060a030308011a 60
    0xd1808034001a00c444080b0740704e6454103401500304451512a00301d8011900e00030984041903001c031680100240d400400e810042c803000101c500741005a640810443d486212501400700300200700f5034280c043c5005110910300241400714a061030090005c2c13180390b00e4400e20f03100001c4800c81c0800c0b41c40e03610954000d010301811080c4e68045040d0050499401040d00100500c00c07502c0c5004030b01c40300400704d4000c6e94802d0140c184002803d059182c560400c00095a076030255114800441c14900b41300b4400701d1400d0064000260009086410b24001c1e40030f0078018003407446c4c1008001810581d9800303850384200001f81549841c00c3c180d4030b0b1060711600410030a01d04541e100325216140140030100d0302000300348019000c3c0308003101503a44840304107016900000a050005c0d000200b294181001d040100041d5070f0b07643c0f880c9140161034240c01d441d6504115103410105402d0165a521480580303152900310300d1039400038003900c01482038014100c4034180243d80207202d94102c0d800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 508686843 1250 508685593 508685621
    0xc030c260a02160501090503030907050a03080d020304020f030102071a0c120a0e0c100806041a10080a020919180b06030403230a03050f01080c0d0303090f120203030114042d 76
    0x6c1100302d02d49155603030300c145c6040b440b40c800c0040000b22480d02d241e2100a076580002110304164201c07502501a400203003049038002150720381c4c0d424135242440942440c900400390100301d141c481c2e03401c9201100203072003854152010410110480e07a03038203045401038061940041c410340803001d00c0b420300c07000c11019584108850180060154030803455801601d04860800c0780c0201002201c05140c0d8038455660001e502e0060025814000c000640e401038007120b0151800941c2000503151441010341d0b40100e4400600a00005c40c00c2c20300d803905410007180420a466130540080d501e03010080006080050410254031241e0482c0002150344120088803034076030b504d0f80e4014014290466041060100032000042d9404001405040698000d480582400d102c1e480c110007810031007900b61629034400c401e002c00542d20801040300341c042a4007540e103950510024003400640c41c02c1c1075210310f041010101c0012220348241c020100310744c041d070a40940400c008400340c600c0641d1010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 508688093 1250 508686843 508686851
    0x62a030c01110d05010602070635160e0f030604081315050c0c01021203010b09120304080c01021c02060c1b070f05010909060b090609130c030c260a02160501 69
    0x1442c411000050190106040310512607681c81e01c9081780c0c1c604061044400241c8200c0040908111582d24070341d000c4004840c0b1701c00850352a0315094000300c1543c4006941c0000911722502d941e0001040350b00d0b5a049492802c01206800001e945070400340c40586450000500205504000070a4100600d450141c52840c081200800f41c20350b0881d510a042c540103100c01072115610100720300000c040445440741c01c2d42d0a0900340d908680101c2d100540141000351010280c18003040030708014013020b0b0040c001034030803074002402e04444010001d103141c02d5040545000d070700420803030352204035100401c2d115024040f051040b003a42c0d9403030720028000d04102260718080032118038107542080c0c1f03642d02c2403a40c0b6902103040b507c061094442190040c0926100307450000028480d00100403c07418045c6070004100d412154613450003000700360303200c0e1007052060300700030031280d800240140500030f00ca400009241c121030042a102203141d0000b0707160341e0150500f05101c415500034000300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 508689343 1250 508688093 508688111
    0x1c020d110303120406140601030203100902030702010b030703050607031b0e060706061d042a0311010908060a020702132c071a120a020406390818062a030c01 69
    0x5c02019094000744c20345082c000010ba0039400307070003120b0040e10014400c0c40c82528081c402002500003a004000310b54980d240c40742e45036000c005d5140550700a0000c1c1c20a0b061207800601190104c031a11524505600c8034084502e0700079003103140c044003d40d08030f030751800a4a407440040105c1d0304490143d8506005040903028854030041c81030307204000c030340c02034128040b40041081100c5003038007036070303d8441c2d09000003001c015800e0700b5408181440480540c491038440d00301201145c0d244002c40c0c8c00303e420750651800c511100821000500c04025a40749809070f01004926081c03141c000702402c10315020210000c10000c40146681d100c02c1d004000b02c41084a4540d00a2001d101c0d101542c1020030780a0400d44200c1c0d003160b1007915101100d224021002036807910201d00c00c0f146102a03103042c0f012110302c1c20546880e43c407480907a03540703601840c10f4080301e2050a81083c0501c4080c0417000076031a40902d1960b10036600c403401c07480f40d006a01c40915611a00c140c210b01035080c03c0c410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 508690593 1250 508689343 508689353
    0x10260f1008070e06062502030f06220f0c0e0a1109010801031e02101701090509031b0c0310020a030515010e062511030f0a030906140d060e061c020d1103031204 70
    0x161401e03074408c40035602c031140b004064556864003aa1380401c00303034691401095482c22030341019840c600ca000d400c03280041d241c442c8404107080754058040540a0350401807024401e124491007864520000340c10a840000020a0240140001000f40f10020034100c10b5042606403d25000e900510342c075805500c40d0740082481800c00c04850036401040c0000c102e0800b61300401748681c01000c015401c118a000f44410f0025800c000c15200e4050b180100303115031003d03c50102c86800c502c1e4090307641d00d014040203086410043c20860400307042080002035030391000401d06004011a005601c4040d1000083c41c4000940442d4007490801d1640c40200085140c101040030801c6096456414804402580301d40704801c000340055200c1000f0301886008802044030a000086000c0c181940101c01030225040341d084551148802c030b00300181031500352420340940651618100252503d03502060440f40b8a19000300150408628104542c500708241d1b00e0015074800300c070046082504107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 508691843 1250 508690593 508690657
    0x82802090916140d03050a0917031306020318040f02161407120b0f100b0d0603110301020c03040902030601051201270212040210260f1008070e0606 65
    0x2030b890302d0280c1c10300000303962110070711548242600582100650b040a41c1d040703a1039030059410a0521101c036601062840d014692201c1c03c5100f03200035541c0d142004c440d0300d40c00007180d1003601158001c214410103a8140804401480819070300441d4002d82d0205100103401451030282d00710185225031002c1c0689541e0501c02814440151000a919110032000c031114105014001c5d944c1140850000f0403202c0d01c441d40540d10100d0140c6aa4442c13030800c1165016070541d03242140c4820062060000342c800f4107016010031002103160442d80c0b80707110f40b43d0040344186101c0361b0380440003a456034081c108450310140e081042c2c0c0100d40c2c4642025120700148801d8402c00407801000203072215091081303640e060500210900329039503a03030030800208603000314a010440072140b0001040044000d800044949100c4a487c624040348204442c02c802042464601c1c002e80041080190108115041d43d03600e1244030041d1b0743d02000325070a80f2520408a28407054010341c4c140b003010900d2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 508693093 1250 508691843 508691863
    0x80a02211501020f070b03060d0b0c0304020a05040c1209050c060f0c0d05040b04030f021503070c020111070f1e080a0b01140916050c15040f030801080102040828020909 74
    0x69100740e5002a98012a920f41083c6010800c69200380c8080c0f055180f02405541d000c1c0000340701c451891740307a58494a1000e003e50b81d186841c103002c02444118070b48060440301400c01540d007000303154942d0a00400d41e401c14448400c00e5551340c40c80405001040c85840c2111001620240d65403244010ba0441035100c07140d08681e6010309146103070918407400849084401030340d049400e16003592141c115115802030304a074000700007a5402c0e1030034010000b5511807603803078649461a1110340005413940a2103100e03203001d034006540c20b118402a80c003109007501c1e10074001d401403212452220030740805541102c0f0f60303403150000310002c000740342c0038040c140e40d003180b049904100604d080c0301403c901a98421100045c0d910060380c0f071403043c0f020f030083c9031a404c115a5441c50152030f090b60084107403015540003030304a03000000c0c50780085519006183d000003c40c9801c0c80c0c285d0b642e80720080c00b188200c550095031040d03100483c0395030300165559001000c07075003075040c5000a6942ca04d0680 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 508694343 1250 508693093 508693111
    0x90a1d070e10030e010b10110c0a0e07080403020f0303010803030a0e0613080901050702060c0102040311060a05090f0a08010f060819050304030b060d080c01060519030201020d080a0221 81
    0x100080c034503500c0303500400c1c600c0d08007070503081e05202c1c4100b05030080c3ca116007220140f50b58440d0720b1861540c80d07001c0241c04459640390720003110301124642c2e003000702c2481824010050340c04108800080c0c1020140e00c0500342c50b00020940b038034a41241001510505080716100c04400450003840100c029801041010b10400c0f220001100c510344442003111600754004885088001003801d0800404001d881454a030740352a5540d400107040b40c01001202d2030580d0b02003801d00802180f03c0d844100c555007210743c00e0900003510001031280c032034805040c1c0210b40e400103e40d0345481d1100c450b4040c1c426900240f211a4410340140010080b51151880740e00c207a0400110032100c2c03641c5c07a00859017050285103000d003543c45192600101800d001e401030320800b600404903030094041c1c916604403c002094041c6000100300c010301c0d054103440d548240c0c003401000180e0b00080c1100701c14a00b410b00000fa940c1300903450000b0b02400281d448181b03600d0303d600d0185c40303060008a11480a078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 508695593 1250 508694343 508694399
    0x60c150c0315010e18041b030507170c21070b0c030a0807050c1519140708070302030c0909070309020916170c030f0a0b06040306060302011e05030a0b0105090a 70
    0x4100110b036080c2c0010815500100c0030314451080242d040301d40c91b0b0042c000c2484030415007061007104074125046c2e00644813034121880901c1001d0540990300c04401c401c43c014045810b100c00000c14000f00c80100b25900c0180c0725800c14901d0342402040300400e038855105031601ca69400e000c0d00d84e40082c0c0d03002e00049581000444440c000c5054a4461b050140141000b038074021681d00452000340000819001c60b0317020b01c06092290140031032183d14554041118200b41001412101c0d002c1c2c0600c0505006104000e115019001030324a041c0080b02c0d28405910b40304d605500414406102a4010742c0c540d040000c0f64066040ca01d80d0905142d4505a5480300f402c41d2010307140c81500c4603400a4000c1000c26901954410071640000ca00d080000e001e580d17007800200258850783c02101c00e56101d9408109660b001003945400445d5110603d40c20032014100410a11000344030050070399651445e03c400b64402c1c0c09407800000b000c0c20001d0106d440f01080512900101302e4901400c40c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 508696843 1250 508695593 508695631
    0x3050103141b0f0a080d0201020406020d08130602090103020714160605030f0112150c020105010e01060e030c01050d09020d11040e0f0a11060d050a0510080d0e060c150c03 75
    0x10019160200070a02c208092509a22508001440d941802c0a80c1d000300d43c92008501d958050100c104810340503000141d075a464900c005c1d003040a20762208041c1701c910000c201d0440d400c2c1081010181d40301d00c1c01030760743d10341a0040e402400f13034560141c203501d040314040c4059100001d49011440c0401341245107959901011521884219010540c0ca07010f0401007220485400c0041c1d0000e1242610f0100012020a83d204a81c803046210300146c1d140c000420507a40d03400c001ca030242a8502d05a06002d101a010950b00e902842d07030399040040010300c0e0981e012080d4406010a80c3c010010030184016003060560f0307824182c0e82600c901c1c03a0a103000c50104002881001e10340001d405031050b2003007900c900c2c001059058845802220403c9100070340e05041c41a80e1145601c2d00d4000790b107083c4525a9040301465420038415075111465013100075800c24042d1480c0481124401d55078210905640d0410158454180340500c945050203107028207600078611504545589101001c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 508698093 1250 508696843 508696883
    0x270102061b19050403021c06060501080c07030806030102040b070506040507210807030c081b0606040204062c2706030109080301031415010b0406080f01140622030303050103 76
    0x4010348107000401c0400011240349030000c0c07595145401410101d00702a969000b013141c0c0c1072022080d04855212074001c1d41002418420381020f00300a103000c13082454020100621841001d0020381440030708000660350399025012640617100380d06a06031503075924648582e9071101a5422105030080b148007003010303800030006804001c4a486103003044910303911040c00c0c1c1d60103800c05a0400441083c40703800300389054010180c00030f001e1340b40c00c900085000c003117082134809421188030300c0c0104410859207602c007060945585044503001c1d001d1300e00388052107840300341c520841d4112401d42202d88500c00524840a4603040d21140d20360079580b1030f010942294002000100309600034401400444c01c185800c00d20348840c0d00481c1c14022806904460004091344180554803001a0070304c4001d5212811075000518003c601c0c2c00d03541003005a0601301d40d0b038440640100804104281c4000084903c646058902c02203205e1040d202e050090280c01d090209480d075005074030040103128 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 508699343 1250 508698093 508698121
    0x1101050403090b030a0906060b0a020d0201090b06012106141509100c0204140901020c0d02150609040c150509040e03070f060e0102090303041206051b030c0a0527010206 74
    0x40e490394590b181c107400c001010b050b9030005043c01d4040d035510441e0100103040c0703118540103042c210801c1520f41240b418028601410780e2031270402c59041040c90b46c0000d0b041c0c500580c01480074201444000302c80c1c42c650424180e0b64101188043c20040e00040c55201d010700b043da42c05003501c101820160040800c00180709100009400c094001500b001d000d00c00c802648000d0b1005101140c10241803016000e40744007a40e518200380d50000d60b00c00070701801c01880f80b00072200d0014045a03060b0441186104a00505c0305000b501c100000404000d4000d180a000c6d0281402003e4040300c4881c000302a50020f10f031107400b5619048040e01e103000c000042c1e407a5a98000c00328803c0c0c04050b0703689d00c051b0800c00084851507400340b00a9400707540620281016220001021034405202d00344071050300d10151942600c01000ba403101e030100f003070384c00301c07070f0b21141381c0f444a0394404490a003101e541c450001600076460407080c202e61114581c4080600100d000d030700301c80040d182c004101b5098 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 508700593 1250 508699343 508699351
    0x20a240c05070b010e19020c060a05100506040b03090f030c0c0910150e0f030102070f1109040201080106031a040923011107020f03120a050c010e03090105030a0513050d0f110105 78
    0x41c1819000401c84000c55400d816840048180741800c1d81c000c00313004a059800c10958008c158000c00c04100c4220001d114465200c003e20014001c05e9181c000400e555103d05c1c0201d0080060000002d000c044041100400410070101183d07078501c0028050740c1c54503100a4058070030440003021503d07140600c2c202e5070540d080d1039a0341080300d50f8590250b80c5060b8100c020f642094006100c1091035800b03101600449001d00c0e0410380d407004511700300d4221a00c04e0912072060103200305010250340e200f00c61070f05540003030500080c00d0a075600d5090344000b54881895000d03040603d0b035000c00540a03000442d0280601c00621540c550885842c00e039218007003101c0744c0034030501900000d8544090b03e241480e001170180c400940070100050389039409442c444020460004124041003402d125041c6440005806942030040d0080028998800a0801081981c0b1203020854a08205100c17141c150b80c0041210341c004e207801c3d00034003490ba4102004004ca034028240c01700659040c0a1039100d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 508701843 1250 508700593 508700603
    0x1b08190801150816020c120d080a020c0a030813020301050429070e01051b03030901050103051b0d0204091a2e0f0509040c090606020a0c05040c0e090601020a240c0507 73
    0x30a41c4c480300e110303c00398050b002c2c2204603c46c540c3d412800ba200e0515400d071900310000905280600b403903000c1c0606002520b200002d070b204000e0400a0b150116082c2882a41490403507440d40341c82114a03008208a40081e5265203072030103110400925030b08842000e42d90942c030103036030000e9002001d1220001c0b12403402007845210b0a036440e40c80741000303016a04da4080207001380402c00d10481c0c07458000f211600712a0303546000510502c8400c100012030f816a0701d815600b91003441700803d0f074043d800700000303001d2903c0743c4c609d81c00c0004e0ba04001c200361174154540425850110310f80120018880304c051440d9050308214004000c1c1c035101c2c5801c1d034860b85202202c0038070300010310070344100c010002c1c1c0e00700111080100d00940300e0f0180e1350040c11598010035184e89107003050404039100c2d6004902c81c9203001e02c40800127030020049040220200c445205035030710000141c0c10322481c810001c1060300100c07146c030882902400c1e00320044036500c00800483e070035400203440ea80708120001d06 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 508703093 1250 508701843 508701857
    0x2010305072c04090c03111c11040507090506130f080d0e090a06030c030f02150a1d0301020903030a030518030703080f0403090b0309011406010305161b0819080115 72
    0x2e4109000d01ca20210802620014040690362510f414000c800e4108076030006070310407284043e01e4003486d040440a1014083e4003080400c1d0341d5006074071a10310440c0c0c0659102c07400502c0721800b44d08000000c1c40082c040e140c0d6074640741052143c10f01103005d0703507103015400d010105d1044c100044500c0090103d459800780b52a8000402c84400c20092200000c19101c540110001d4039106c2c07054011482440b00d04030380d0280c2c1c4100f005910300196864002101809a0300056600c00d20b900e01403445070580d1486901c4420209029101e6000c0c8a505480001340460400394503a12042c0700705001c0240f2000200046811902c038411800c000d00082c0003e00402c5454034555895a0014030074200046100d40c2d5050480309504111105c0010703941d911503003203001441964840d1b00c10004d10b01000985401da920a2060748910303410f101b0803121016a0b2031400740405402a42500154143d498240581e415a40011030034810f000060051000060101501045101026440e12001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 508704343 1250 508703093 508703147
    0x611030f070f022218020901030b0406110f0705120a0203030c0f070c120308090703030504120c080303090115090209060915160605061c050715091706040201030507 72
    0x105070088141610201284203914005984070203241130b8820058440c00c0d00f41d091081c01c842140c5d140c451161224407800c500400590301d1030600b81c1540e901003204503031034a039414442c0040001041c1c0c6c45200c1c2c0300184a500a071074690161401903c00d0302201d504407408d05000c00d86000d0050303a0f0000d41c1c014404191484010406850508602140e05042a80b552207031000c0d182151b010b08080c030031103841340051562142415030700807103402c0102115072940d9001001403085216003a01c49041d80034020800c0084140d05006007540d82c100d035203a00b01101924001c0c1500d0701242ca260070f0100c0d0005015009001b9542003100050130141415401070a200507004240105104100204641c080c0c0380030300040e860300a80140000207441c5482014030691045420744406d03041c008210060001300b0000b000d070f050790840f084084801c010000242c4081001e5000189002050416a00188800606184128001d0768180081d0f1110b06050380c41c004184141d11402140380498 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 508705593 1250 508704343 508704367
    0xd0e0f0705044818050319030f0207030f1a1e0606090127080106050307081f0e0a030201051006050301060f080601020c120714100f03050c13140307061103 68
    0xe8550b14206000c148228012210182c0303c44801d00c1401c0301042c1a03040c0f02c02032074469404500640b20590091100000b0303007680c020304442d2064003c042140c0301064101d840c0c400c0c81080d00442d8070401c1d00740034498500c2c0182107480c208483c1008000d940000848200c0f400c0c0720041d1200c518504014075445000c14001d1a9000c101514180108504c003408007001c07503928000108545207494141909103001c440c00d6941980c41580310358000c4d2024008045c0200c0c0d403040860981d0b1604481c08143c101e064042c001c3c0441a000c0ca02135060003006240d010340000e80b04840307260711402c81c60380312841540d00e40030a004035400120255003604050740255002034000700140101c074901400b620004000000d000d005142c2904030103002c21a441c400b141c0c400405100719608032048070700740b9000f42140d40c924902420580c803107000c286408840e50450f10f8402008020351492910f0350f01000c840351801c05c425000b8841d0b2800000c0480c0b01d04002c240081c81d10003e9460b04c0c400c4108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 508706843 1250 508705593 508705661
    0x31b0c0204060b0f090a080c010e0f0a08071815360c0e040b03010902060f0703090305031204110a05060307030f02220815040503031b0d0e0f070504 65
    0x2040341c02680e90840407640340f075000054031004c0074100100781d48180c0d0300244001c45082c0d07409552a81d1007010001021380e04008001c0d0141b00c2501c00b00c84000024002402d21400c980c441c107064005c852001c240595008440a070054142009014130302595807811854019441003285502446d1071000e0018500d041c1b6803044240391103146209041c0601640407244040004008210100078614143c14140528540050118000c001024480c1c0202d1568030074040542c1d04103030002005000c0500410f604809550000c3c00c40f602e4181e00030560b018542d080d9000d980554403d240200f4038074001592a00742c0d00c010306150700356100c0d00c2069020b0440500310041458090042e00240034000440c4c50300d15540021401410f842c3c03c503e1400d10482071001c0b0b40070f082036130030040410b000100300c0c1d0700603c101040c440c0703151507181e42610354040c9100d150012801c24400c1e052240d000a41c400703d504008081d6100942d9500401c03044405079149075660065949050400f560a011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 508708093 1250 508706843 508706867
    0x90403050c01021905030a11031006030b1306060c060b0402090312090411030f040c060203070507031b090f06030b0703090b04060e07030f14060c0705031e0d0e0f0607031b 75
    0x742c02d00b141020740b0300e444c2e0f00c41e007080b00010b1301c04410404126600d0080e6034521002d44621441c500f4040b868501480560095000307260700c85180415903295046038880519460300f08001c440d4480c04000c003182d00a1701c041c0c40680c2000140721082c50144200e42c600407000b0000d1641200441015159400a2008542c01a03031040ca610a45003100010341c8240e1660134240300724503080c540001280d0107a0040b008650043c02003500003a80059540300340c03900a00c0c088032202502640310b0814040ea005400e086090110900d401c80d0250400d84c00e80b03104a800c030b44c03603a5580c04200c0864040c808040d0440314048041030200701d19a10a000ca842140151107182da240c2c0c607400303405c0c0410581207409003942288100514014441d454215401e0010917282000070b46546a072070050014466201c100714800c80c04d40c40c1031078100d4000c20311740300c0e040c803844405201c0c0b1510f4800205c811000c6000c3d50001070303011442403003105c040019004540f0400301070281c04071440381d0141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 508709343 1250 508708093 508708117
    0x11401050435010c02010f151203210f0207120807050d0f02070506091e0610060f030905100618090503120c2101060e09010303081305030d020c06012309040305 70
    0x1c10003011402c0c00c0c01202c2c422811600046030100500c8041400c98442080b5465031018200d4240000888103007108416034051424690600792001d04010b039000c3e002a512001d86040031602d00080b003500601075103405034002c114003080c035a1003900c003400115219000501c0401866000c240760313500c008070742135510600500703000550b5600c529003002610740070300d0383e40050b04405008014803403866012401c40086c1c280c608082c08010300e80c1c6058041c01c2c040c49520010050024400c2d4032140180e40c01008803200140104a0807006003554041c00b011011400712074a110003141c040d000d802039019005611380246190364140542002d45000c42c02c03141048008080d0542c020304100c02c404407002ea040651420b00040c0540c0e03031404016000b070b40c2d160010008070743c01c4455560b00c6404990a403004c007410380340c801d046105c5c5c8010b11111a10110707100c0e0f640c140008440f030694000d0701d0156a04100a1801000c03d207903041403960041c400c10004001070304c00e00140040d10306030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 508710593 1250 508709343 508709429
    0x30904090512180a09020c03032d0408180a030f0204090309030c030c06173c0108060601030e1b040c0504050d150c09121103030f030f0114010504 64
    0x100c04108465100d490410300907035081d40204040d180c00300d103c400820280700f00714603015004d401580c80340401800e140e008218081b2841400001460480c000190f241cae0003141854a842d010741ca80d00104840310340d01c15000501e41c0b13941000d00028007500d4100704a400c10341460741c200700c0a03040d40d40c2d00b182000801440080058080355100d80514400d02425801c14200000103200e0301503982c54150800fa42020321401c0703e180f100d1910b048203081100c6641c1c8594000200fa414050390f40d14140c08001d0300002941c0001107000c0b4010303c001d070703810300042c01540c8523a55501c0f1943c02e5440c84102c46c100449a42c0317000d9101000705c41c11402c00e123040580c1c50000988010b170102007603907032500751104103400b03240b6441100707091441030400b044564249040c2c42940070071a00f006001406c42103c0d0100ea80d02081601c9640306c12880c00d0f5903910b03014a802c01046800c0c498080103001604004c981d0b507000b00140c03410b41d1041c0f00a159958203208000c45450f080700320040407880c00d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 508711843 1250 508710593 508710613
    0xf07180e030909090c0103140402010e100e030d09090c05130905060a092318070b0d0f09050f0609070308030f07030f052404090b011707120309080d080105030309040905 74
    0x156a241d82c804c100748005408405030380c00014081d0f840d06042070f0350707109011081200603030300407040d80b04840003581c4001b0145021481980c000032500c280f545d143c880c1c0014184420b52051040301134032042803050000d000c0c8000d05403aa4005c032000b50810b40e0880c00d00340550350099000070f5003c280203025450382d0f41e480c1100811600005006a0449a48202c0008064a0550b0581c00c0041d0514484541140305040f40e100c81185c010b000c86085c00040c045460182c940090500c4074240c4030400c0a00851b04c3d10643e580c110503030141c024020b030340000d44940b00100e0b0f0a800c60b90041640d40ca10b90320540c004088510003002002415070745c07120301c0d10b50005445801e1281000c1d0941a06824144c4c5d200c00140440702541403003a428095507000040500c0541411249020700403034400000540031814480c0766003002c80200070090300c8070181680485000102d0b013000c01580d603032032216a0f045070484424041e05803d60b01c1040004800c2c103050784a81b90b8940500c090750040c0b08 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 508713093 1250 508711843 508711849
    0x6070e190f090507020606010801150309050309060c030910020303091b030f0a06060f05060c0304093303030e1c1104090c1e060f02070527180f07180e0309 68
    0x502a003002c4101540d950030000c0458041188541050090901e259250f1401c040c0a00b1307003802c803010004050310b0351000f008205003002940e9407110020310080e02c44039110f903400d94075000110013902c6443c204480c1c402550010089034060340300000542451980d907a03042d011b007a0580312440c1c0620540501c00d0001d40280604a07049118250216000749080180d400550031b58110321b100301c0080010a90b400d07000400c0303804445a1302800300b40f020345a804c04400c010744010f42d2610400b084800145004000c0ca560140c034130a03100c4110b11107605c018000801c001c4a110b065501c101d04014020481d072544800041030000d00205407021319a40b007a01ca91601d41c402d4443c80c2412941c44080850b540240000d0105480e25147c4d158001c0c600a585800c944900740c0240303400c43c591a0335583d15200c4008035000b00c135401815043c61406004030b00307007800342c4403010b005001d0408120140440c6800481d40c9030002103115140c1c4904003001000100000d04e050702c82042100340700c1c8c07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 508714343 1250 508713093 508713119
    0x601140d05040c060e0607060c030605030a08090405010b030f0f0a0b04060e041e03050319020405090106120605030d21090203060c1c020f2502061c0e06070e19 70
    0x660215008221800c0a10b050202d183d201c0e000710041c40001122640c00c0e44032030094810313030b5402420202d5003542d1040240d0080c412074003c81d4140c01107030480300a00840a000340300c10030058904006c9a13903140004441c40c0410744410200b850b011000c00c130a240301e44405c0e40c00502141000649418a0000800300d0700198410400b5248540800080c030882d002010400300103080d0036010440166001050341c8401840c19508402249402c1c01406107a0b06441c040c10025002c50801e5031645c0c4040c20705011070040c451a1030418030f0100d8207081c0401d54a2a00902d41c603925484800e40790051444600c4041504003141e8464243c4056a001c000542c01150540b0405544031020b0500b480c2e540342c54032024079414010001c0942181c2010103e17115440300200015000354020240d040010000303901075071001e008030b910701c15108a00491030541c0c130003001c1007000c20102060291200f90454013100400d500d109007ea060030000e000c0844054500300c1c0406807078940100c9040a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 508715593 1250 508714343 508714357
    0x40f030f1506090609050f040309030f0314030406050a29150c01020d09020319110105071b081b0a050901053606010908010b210f03030c070c05090106050d05060114 72
    0x80c07074803401308200b01d25003842070390b07040214203c00c1000344ca0726480140201c0c41c40e100c01051008805401014144140c0008144600940100e50350b42000d0421030f003c0d06090703512114442ca00f03c00030700786c041040804000595071a000052a004400411a8003813081c0e812004004003000804003840c000e1000340b100340005440001d4007581c0380145490b110401d180075044003e240c50386004a40c155200301c800d01000d1a28994440382841c010019213148007184240c200c00794008074001d0303400300e50f000c05840a6400a58042c1c0d2a50407c940d030201e030300c0b6a50b004a00c02c2c006010a0610b5007040403036500c0004403060b03500684685024100081e503607100c000c036091090040569000c20ba1400400c2404020300c8840c25070400107501d11303003e010700d040e001d00000703100d85e55050501a803502041017409030b83e2246401080174540d40e100c92011507800045e08004600c5180007880d8505840056070752a050000005100340141005482a418420100c0c0b1000640c1c850800510603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 508716843 1250 508715593 508715609
    0xd0603050f0715110601090f110d141308040e0919030e13091a0a0e010e1e0d02210708070f060f02250212070303090602060903040f030f1506 62
    0x203500d1920350000c0030804400f40110810550340414400c0c0070000440078199203500d040000c1400446800000030880c0030311120148802050380d8007800c01a40c01070000658084000c080c507a40c2c2068038000151126005001d480d05100074000700c8038545415612204101c01ca03100940282c1d02c0b080300a1186404500042c001c640d402024103042c0415442d02001c0752040c0440001543c5481d891402045074901042129001907181d51054102c620380c04400c1c0000c002940c1038030042d90321481000144162075882180502d0318a0300014100b080c144203a01070010042c1ca130410042c8800e524070750a603904402d02425011507020001003011600ca090294104580d519040b021350b0b91940b043e002545c81800307000d9242c00c1c0c1000642141c00e03c4071004a0001980c4009050680c504030003206900c284e1002008042d002004481035925940072511300c2e030f594000d0741c0c0d920700c50341c000c082c401d02e483c0004000042c042c11004503490f01c50b030201d801080610b1020402c541d125400022 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 508718093 1250 508716843 508716853
    0xb091213140d080702010305060a0f09020d0506120a02010f0c080318160b160203194202030c0c010c0e040f02040e16090905240d0203120d0603050f 65
    0x1c500300000303111600c0c040540c0c0c1c040058101e601d854060f030154100103814180c44100056040d6140104400501034000c0d004c9090794503080c10340000c2d0003281148122a2808012550034074004002d10f0700800018010890072034694011603004903892900010b208110380c1c01c10025420801071486040c94400004020b9000d4503c6490029001c43d0303886543c00300c0d2414003400441d0012100325803850400555000343c94400700f403800038000c1c0c50788901150b001256017008040201101a64040b00f18840e500056540140020881242d4003001100700803a403c020302144d00919804130340c0351112420604280610307800d480d2200012000107032000d610900c580307010b00c41c149580792000011824541041f00c102c00d00480a0010307684008444401035040c0e126200e07407800b90040701c100b4006c90a085a60010301950510003141c81017440c0e6202036507041c001c0d01c0c044200e40081c01040d24422444d8504503540c44030020b014900e49452010000c140c0400400c0b40c000030040080c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 508719343 1250 508718093 508718099
    0x70c03090b0315011404090219180e0a0c110f06090609010606120f02041a041d07020a030c05160f0e0708161b02120a2d0b091213 57
    0x5000000c1908890345541d4203006001c05083d03048100c0a080b2000c0c2440300f1540030300061201d00340034030360068590500001d00031011801110780043c984102c1d45401014985400c03e5600c80c07100f070300603080410400000102118030325000b0507406403041c10810300910014411a00300204a031088800c2e510110500400b518100103007503115080742c00801800c2d0501c50f00400592440000000050711288044852585035040310002c0c100110070341050790403150140c1c6950428400c0d1a04410001d0643c002041c804150038413405803540a860f00c82c10b2560190b8010380349000c141c074148100d00d0318a401c20320080c0410050800c900140084510700241c4003c00070f0300400c141c040040e001c1c01e009505080341d03014148401d15040c2080c504113000f20400c02c018103454081d51105c5c12000c008031500b00810f04200481c01145440000e19480b81300381140700d120109000c0120307243c1020303004220302c04985c3e030300201d10718282e03000030002079407100c4107400440c905041880144010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 508720593 1250 508719343 508719347
    0x8041a0c0c120c0c060304020307080106083306040e010f110d24060804050c03160302190b0d0b010203091302040e01080706080c0a020331050904080a0e011106070c03 73
    0x24000d1104441c02c4901c1c1c440212415625401080c2e1881d000398004404142196000d0042038040c0001100811002d0b07501d010880ea00d070090001d400008680c401000c900070000012061001104031030100b241e10703030380d05001c000c0414076020f603410355035049500801d90303207401813407404000107500d1609c8501d40d81d45c0c03400b00c4500c91390b0a40d80b00b00c10080e400c03c1c0303400c02c2c00d00c104840c444c1c18240c107699540d0502e0b90504030300040a42e410700075203001e40c05100c480011482aa03000355800600c45540b600341881c90f0f0001e01a0000214050040081c4050702da0401040f212043c4140c83c03e14003648046a0700d210f081c04110103da4020509014209090341901d0050107010010030455241c1040940140b001420240541000040900c03109000304102d0b01d5504074030080c04420034980c1e51041c07550104800005a242d00203a001845107080075031103026035040b00d007a03498046044070590b0f2007611904500d050202100c00302c0340380c1c1400e1008610070105503c803180c0880e214a00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 508721843 1250 508720593 508720603
    0x7020405090601180e2e05010f1502150411150301030c0305011b120507030e0303070210050a020702060906030402010201091e050105010510170402120f0102130f0803030708041a0c0c 80
    0x214101786414441a00134000190401c2d01c1461541c0c00c2c10b4181e183c070060002000f490b11940ca2140c03c00d4000038500305c0d9260035808403a40d0b081110070b20010708804a03151600103c0e00c010700c410010103d400301c4c03051b044010790b010b0010401042c803541d101140001d5003007607000b5100f40e2800301c42082444820b0154110315030900c010040260749454014000c4031200c400714200c250748000255440780242d1050000815010850780c6902c3d110400a559421003000d030f1402c1420701c0003003250b1034024020b540c56544c2c010308080c00c1444100c03e005003034000420030b0341159281c1c001d400c04a222aa400a00ea8041618400401ea01d6092290a60344181c1c8100d002d00791505001c01400c2c0d01108239408849000754105540c2c4460000403003180000019200c54020580c082100460541c010100d0301054100741e01c0c069698100c1e50301d00d05040c0304024094104200181506100d003076013030f40c070900c80e41d04425012142000c040e010300e0226802200e2200000f650111082e00f080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 508723093 1250 508721843 508721879
    0x1b0f0e0102031c0e0f010b130b040209130203151e06031e130302060709032d120203120907030f120210020d0b040f1a060703021903030903111605010e0607020405090601 74
    0x20700c2241d000301d01058141c0c0c40c3c0416104189e50703c24020065946d07540490f0403e0000030070f07403070340f140c0301c244640d0003940709545100300130018003220300c441d090800207100c04e00c204406501c5540990018041e441d0710003003221141c0d500c2c036004419852800c44500340640b41d10480b6260756585490041e203801005461441031100b8000200700103401100304d07103103504c50041d900b10a550901000f4200070044103004203900200b040290f01b0740d9000000d4000700002d824007809a48484040c6515151035000151001c0010702c50040810354022120150542a1045541d010310001c80348080f81c203d000010551601ca0300c00031080e240c2400740e081604c030400c40400c9a00010749035400ca012001d0401030240740086040810725001f0b000145081c25203205121032600c1c5441d00500a20030318000f10302082d48508100c0c0780d42030010317004101698250150524030704041c019a03800000502c070075481002000f480703005031108e0041d2802205610010070a55050900c50a50300b04d080d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 508724343 1250 508723093 508723123
    0x3010302180f01050d08070606060e040b0117040303050601021f020a090509250c06050a090302011404080406200f0601081915150e09030a031b0f0e0102031c0e 70
    0x60030b015103103494202050448a00b1150342c85080c2040c901800d19009406015048900d840f0000a504e44c000c0e11031242008115810082e80711840c006460500030b8010322543d6546140c00140001d009074481904113030705004940040001c50214200300056a10b00d910030707600410304601290700024154080c09007211071201600c0c1c041a94050b04d0072035890030310074591b90613003910480d0003000b4000c0d245030400401e10181c58071420f55405420030402c00c40040d8604082c0600310700802c4410b41c015030340001e0003031500303243c0303842190241401641070f5180304002e844e81c01c40d000f0820880680c4100350340038101c19890302d0500c50034000318032216010003011850b01400a00c8002031101c1103072000500240003034288140d080450440d40044002107600070900144c0e00c0e000001e450701428590741400300c4c06001c20b000000d0981803041e1000f191408080da007146000e1100d07400d01c0c05041c4100c034205440d49800da10400c54003610400002d03070f122805224078806010280c03040e0a64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 508725593 1250 508724343 508724389
    0xc110a030c080a05060612060f04080f0a020106080c0f01090e090312040f0209150109032301021605061e070f120c030606230a050711041122030302030f0d18050303010302 75
    0x4107201c0d00c8d200b0040c02a00160050800a001c0140b4201038920013032600d4040c030740f114045180a4000c00403402111070340c4c03061400003415454000e854640540040e0b442d40001460034200c81c0e4240c501610300780700e5020234811451103420802d8034038400c900810611b9151040d0740180f001554000e4888402c0c400c1030321169405da6045503190049992000ca046ca400317800c2e00e500b04045010303110f190510f5000007178a628441c4282507101c940303406103055079a03a84030b030404403a804038002e90040d410741000000801490150b034982901001070301b00000005000c3c490f03002298841100b4401103a55400700b071015a40c0984100e80d00c44040d03240b64081454124010b80a002d10030820b800c01400007641e0f4100b0416450051104401510502a030103006031a8180c680040c240c880a214107100010300000c200490302c82240c2d015009103150142c001c1c1b40c808203601421403004e0f540e840d4240a1507002d000c0d0300e2100800d004501844d00c82d41140b0420480030b0010450004203840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 508726843 1250 508725593 508725619
    0x51203070b15040e0c1c020312040806040b09010e0706030f0906060f0f0602010203040c1511010218310c140315010206060d0c0b090406031401050a0e0106060c110a030c080a050606 79
    0x5904404100d800c06c41100b10140260f0701c0080d20741503600401c114242e2011900141d4001d0009003680140c1c814001030107240d071803040e0745082b2558590700c0c01c520380c49140c04002480c002d5000031040d0080807008528440c00303844101c19556503030300c03000c200322401d80c0030020105500c1000c80a015240300035803460034151101502004036002c0d1104070741140c018032640740d0181c1c0303515820a425070000d6444141034010808103001050342c46021b0b0841d0841004901d40c011407004c84618918125110500a0159180100074610f100410b000c038601c0414080300c204c0000e1840780c008000000000055080024140000036100138003c5040080d0301e8005090004404144c0c0c21840703a01c0d48a07a001000603005d488240c0c005020310741e80402d142d8200a064005900c500c7c0f00c240c0a004103506400300305e00300c0380e507441100009104c00481c5000034500010018143e140246824002d50300c9441e5601e5295040d40201d8060b84810100c0381040003d010840d4840402c444480f40440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 508728093 1250 508726843 508726849
    0x207020a0306020906092d40090c0302040b061608070614010801090b0c0a02071406040b0301080304030611040f050d020a0305060c0a0305010f050a051203070b15040e0c 74
    0x10641c0001000c00f5004a03011115880380d009503602c0010042107003071580030114425a046082c5003000f01384400c0404150030754100384211042c4030300343c403243d04080d403103101080b410b029207100300c4411950311080f40c90345100c181c06000c01d22400b402e44440801d14510412040340c020052181c05070105004410303911020300d000120707454100c130f00b071503441051740390030f00080c12503011102088440c00c00100b0f200c80154131400c800d901c62142a81c0c95100c030400e10846000e26842d010059015400a000600d020250001d502e031001d0311141c10551030311504400c681090b00244559480810b0800c22700041740a0403852040b01074103545014107007100035550210074000d20b801482d5411550046407102507924000b542c000050303030f0701030610050f03030341e9103600406000000905080010601c0040f0525450884000034203048500d4a01820700460309012440510280000d01004001c0b442d004400d5200e001422115407121640750100000c8420704000c0c00e407250f00065070041d20351 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 508729343 1250 508728093 508728109
    0xe0f040c03030f09180b120c03033c1905120c0f120f150a0e070f120e0309040f020c070902030c07140d030e12040e04171813020702 58
    0xc0d402d03103000c0380f03019580b4a080d1941081c41d440362400a0124201500d4000c0d039074400d11200c20212400c941c3d0050481d443d660b500310741c040301607141d017042000d403000190018030306240d000c00581803019507a240c4004401c4084900003407800c246d00140c0a01d0f0010310b00480700b034000302414500d05006090f41c0407096244010101c0c2100500040c180a03622055025180e51512031007006900e881c5c0740c8100c145010090711200c2d1101c3c01501c100703100b03207016070441040d181c242d90448040d6407602401c0b03507103680d203102c2d03c4180129800004903101d40c0e4051000c8031a04130004603a203030850414081119800412043d4035841070000020120b40410352100300d903002c120160320707030319030750b003540941c1c400c440d070041030600c0c4155401031550004c0b40025921140e80c8040052082218849440705008541d5a40b8850201f000340320682c103402181d900980100200024070b07103c549401d80c40d07030111400d60141c01041d21409890b01d00814000020100040103500300703009640852400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 508730593 1250 508729343 508729349
    0x6040b0304060513080a0e01020c011119080f030f060a0902070503030a09080c070e010f05060316050d150b09031606121a190801270201050304060b0a0f0e0f040c 71
    0x82074a0f440030035140194a03d000d009540c00205965454102c0200504010141c034603090240c021880c00429541c012400c104624070704001829001e4424900d0000c40ca5440380100c40056050101c46c0382c1054003805584039022800c0044000c1c10003a040000c42903a9500c0551700e50700410481c00014004815260170030002c1d540030540329590f19003c2c41d20300031502400c41d54400c1c0500019100068840c0604075030000c0180d004641d2144140000c905c802c941e042603404501c01c404180a01c1800207080720200804000381e20448865201d294200c16403003140c1407000030540055520f000d021144d070644d80303070101c0380441e842c0020181c0a42005203901501b0f6076075040c9200500300c00e110360062100c0081c0f50000640c5450701d0726840d0001e5019101c0700d90f10344010032029006045e40040242d840126001c3c000980e5801140c55a100800891380c168903020541c8a6495140d10800540910103944050500b001160101090020460070001600d0024000840c00700341402040d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 508731843 1250 508730593 508730603
    0xe01090f030810030b15090105030114161b06020405100c030f0f0c05011515090b0904050a0b040905061602010615141308010906050a091110110f0303040203060606040b0304 76
    0x200c3e070760308110083d51400c60703800504010000410418442102d0078071042042d801c44006100c1d90700c1c0c405040c201d41e04010001c050311480000b0418442c80c4070a1030525103e03070b00c1c0c0b860076202030b55421220324115032811104035130081030034480c52500010320a004031b80f40c07a0201c124466034030020245440054010140a481208040300310312908425480da0380040c020701000030a204280e07035143d0305124842e000c0502c0f460441c00c0b98820307002e0000301e40400c0707061401e20080d01c0030400200400380140251646d81d034051361032a01d0710301400590900400141001303260504a10115002d00201107046904d01903003030200e56803020030007800640d580f91003403154212114641603442449421544585040720008119405401002150b486074006100c80c0c0c0764004802c0584a900000130301d2000c0b030411161a600700313000d9903a501440d601d03044502c040c0d490040d50410010150704501500b00208000660404004c42c5030000c8042e11681d190501d06000c04503140005003008003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 508733093 1250 508731843 508731857
    0x609190f0902030312040b0f01080733080402042003010e1515030105041a030303040311010f021201030c080c03250b0406051c0e0c0f0301021216030e01090f03 70
    0x60300e440c469211158050b805001c403560307001c449202010400d000c6900301c41900301500040d030311801c041e604604075003401d0b000b002c04e21300709916410b01c403141c0065059504c500a0682989000c022010140092992544015030a190040c40151a0504903c210310441e6401a10204001d0307000c8a0456040d02c1c5036841d82d0300c03a29142c01c5001d406032000d55100c0782c44810000380c190704200039812240f0840c1e0402a0340140d19042500d8980340410725031613002070000401080c02089141204c8110800004180c041b1001c041c040b60000900c2881d03410105006004200581407004042c2100e03c004040400e82040000e6407103445a9080814548a2075446080c0175003581d0756006e0079824141c0c40d01d50342c030741e00000c100c0d4106030300710443c025000d22a00004107051042d1714070803000c800a00305400c0914184024811100b22650300f641d0b0070004d011b18541c8040d070160103007020392080e0500c0c800002c4001c0030f0310002040b80081380d141518050004284903130178111386506040101e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 508734343 1250 508733093 508733111
    0x90f090c09100522030b0f040501090507060504060201060905010b030c0f091f0807030e10090503120a2a050403021003230612070810110f0a08040605060919 69
    0x80c00c540281c51001c0d4012502c0d4030740d81029a00000030f00710303002207041c00030381c607003001c8996901459251101a1002480743c01041e0310b0a03060180070f0340103004900100b80449596103181c94042c4039070007900040c00200702800046d60a01170b41d0000e010400c0c0503c41541844c1c801081884080c11141745944005060b164203102103094860804000b0000d1203503070840c1c04104170031594625000d0005940700005004139000e0320809034000d038041c0003045a9502480c040f401040c642206680c40e210500c450f405031120350000502c0707010540f0010a0036035a903100024036101c014480044400030568919419910a080c0c40889030121001603590281d03500640c02404103646200c0081c41450700500031000301c4600303601607003060740c0ba00d0300c1e18031607900540c483c1681e003c0d622507608180410000ca81407074001446070452140c28034a014070f410070107881d5030320183c60400411a80320400c01886880d00ca62540003005460381d52061a102c042c004150040807040c0d41c241d61703a000c142d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 508735593 1250 508734343 508734361
    0x5061f0e0a1d01050901050f090303160e010e0d1110050a020a0204020901050405190510020102090f040903090e1f05040b011707030b06070804050909030f0a1d060d020d0f02090f09 79
    0x10707040b514031820007000306051205065020346801c4600920041596011904084001089900c5845010406403485102d03400440e000058000e0403410480c0c4402d82c03200035941c991049a513580302d440341e002ca2004003020701080d4500c441c02042848030901000705116008244045e0850b070440740140d8403040e220058a041c01240c120503084851406420300003110005410f003074850850b450450f144942c2c2c400c034242e04c82c201480307401441d1042000110304194110042c40d601c6803c202010ba81c5403135040d8074070300044803d2000c894a02540005030060256004081c04080d07038248640141240003034030300b001685801260400000009001521990105420001c000d04030f507582c10140c14500d00d01c0c3c2250042c0da2203404070030301040822100208031810b200c40100801c0c00d04420b0a07081e101c0301241000c8040d62883d524001945e40e8401c0300401c08031007203400050711800c2072210300c0300719004c1c207101c1402540704115550392507842c0010345800303000c12102d045150f44c4002c0340d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 508736843 1250 508735593 508735631
    0xa120302100c030c0e0f0a0302010804020d050109030815151219150905060a0e1305011b03021b070f17030705011a030d0e060304031407020306010305061f0e0a 70
    0x44010703240741001c00c04010b98550000c00c5001304660b10044005000c1c401c104808242084141c0c0c08600007008200550040542c60360150008006003060310168490310300351200b9800850010b0190400c1210580340145165409203041e2056503820f01c1044a04042c1e00ca00b101b24000c40c912180024901d01c00c110145048011b201824000410090301d640040c0d0301c9409a00a210b084c0800220740b801c00e200c1d48000c4545c025a0b204503521102004440c4a107014001d4400f95260002c203444042c41e0f09100034800d4907640e005940718030362020b034456a00c2140f8161041e8010000402c1031540544c158016182e0b0034441c54400902c40700704601c0c500c00c800e00184154205000000056405d54890031240c1d019030581301c00d40b56009088580107504042c01b6403114082c40420040780c801c45082842004054405140c0042600081d14208090b80121900e90114007004012142c90f006440320b82000c00040402508006603c0d4440d4030081c22100325650ba8820140d1030b000c4042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 508738093 1250 508736843 508736863
    0xc170613060e250e16030e03070b0f010e010e06030c06210a0e0d05040b04030f080403140606031c050912070e01030b0601020d05040501050702210706051b0303060a120302 75
    0x849a2a0040c3c07114400392441000282d40c03000041507000550039070401840344a4140c04299018445241c201036000384041044e01d2180c8c8014001c050004203422074150080e480b80b103e005c1190b1411800c01810441604041840300400060204603100062501c01e4401c0c00ca03003c64031910510540300060342c0c4031111110040880052005605c0c2176401032080c92026026184805100c1e0815101403050780724806400104000400104580c5104000c0f91841544420318143c2e032270b00c3e601d50700d03181d04000b103000c1d42202c4248000b0b403034100300440f848460812600003240c035960b406000d600540c03500d030b03000710341a8001501805041c004100503000c100c024006950710b0b420140c18403a011a2110b0141c07241d07502600e00180100280d80c11144140d4600e45411302960a100804c80c20502030746040d0f0b50005007030798240d0180054405000c5a03075902da16174101c01100c003541c4904007400076580c0c10403c240092511650b07541c03415290420100c05006540b490101d00d48030b0101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 508739343 1250 508738093 508738121
    0x20106032018042607020307090501120609050312090c13110909100905090318010c02090c0a030605120a03020c06090a0501270f0512010501240203090409080301030c17061306 77
    0x80c4018030b4a407605019184190087c0c08448074262580c1504086030802c4c00340e24400d400180b82e0500080c5982c12180107103108030305507420300b64100b200ca0303041f010542c0c162406402c400313600c14031404c0c049000110080521420f01820807014112a510301c02c00c05428043c0f0240c4001410079110a07501c0001030401c20b2040049240c020280c40c3c490704a500c9400350f2500703002400f120380d03215065806030039400034904d06603621001844e0140794004d0240e0010b040d2903450000d507507615500701540515035100900201c0c1464a4020709152111f60b0311446481c092017150b000b601e40c036086005480007800c040c201c0320808402d95102d6440341e41c920310702e00902403000c14038404030710a05c011074800343c40e2690080c1c0300c1b443e420b01341d5000f4003c82040d000303084000031038501d40c5500810a820f0038010360b480c04602c80085815a11aa8415685244000010810800301c81081d0f002070a64651141c21030b46064000ca8460601070545501c6c150900308a105029155120021000e428 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 508740593 1250 508739343 508739393
    0xe030313050306070c02130207050a05060420040908070605060102100f060f0b1c050c0c2b0906020303040803061f0804061b0818010e0d02010603201804 67
    0x418034102403441140220790003030140201140f68140030300342d10071410b41d000b441c85504001c0201030360700a4100003402d6501c2c1c46890b48800101c0da050100038000c03401408405c0c05490051096040e200c0f0b022001800341e441c0c20040d402080c58a01a100300c9648a07030046003544880e00100e2404513039642c10250985031081500038410300da8002012130b19480607500b4100d65440b0144220f01400c2004d141150080461181185140d80b009500c23b400c4402c0b107003044040300310140307440d9411000e09502e1410780080d00c4072411814840d43c0300916481c0580b641400d100c4000d4490001a1000b0180c00b00480450129a114104d1036035009a8042100e41300380201c00080c92118117440640c1c5482c54504c21031031280e4a080d141c58101c0c00c6880301c6840e6160003030710095147e0180d0a1102c030f03540e9800c200c809071800703000280341025668004190507084d0f013419071001000a0352000c4800030355190802c15180c01c4040b01000d1008070600405554905124140700c110740340c460014504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 508741843 1250 508740593 508740607
    0x40c021e010b0406091806090213020c0307111002030a08070c0f03020c0f0405010b0405090c07061d0f0319050901020106080607020d030b0904030806090901061e09150510050a0e0303 80
    0x1580000e02040b0200ca003440b0842d5618460411501030b10714251103d9071982e002000702e5202c2d000300f14011310140c054600c904400e580b1508903081a07401c1c42c0342e6000018070310184040c500800034024011241d0001034124484069943c1c402d049080c01070041c1003000610386401001c000100d11b40182a6090b0062907160081d142e0303580141e40c038402c1c803140d1041c224509003442024141c1e82d403084000d28250800c01004003c01004040b400e181c1d0040010305d0004110340289601f040d44221041003652501d00c4190400c0140c141d054140e500a0018814490f2410101c415080040c00e08954800030080103d0240039641c0003000140f085038240b100c282c1d400103030400b804c45180d5080103910880307410014200400d41e030240c00155601e0104519107810302e15135811205c07150001230020358a111005007440303221022503140c41c00d254204000e110b02e00070712070f0382c0f60500e10001da014103140010f01c80f1490324030150100030010070285840da00441c5140d001800007803c90303840d00d107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 508743093 1250 508741843 508741903
    0xc10090e0f091603050706050f091e031005070518030f06040302060105100c0804142412060628030906050a0c030c170a02281805030a050309040c02 65
    0x3050b21404a5803040441c903d0414446207804800e4a60010140101c0c624002c4104c55640241d505e011041008110301c0740c01c1d60310784646008411043c8c03e2152015905010581040c03907145042081a0408080203201544034003110740c0c28140816180025a202000c00d103049005c64a12215104d62024032041c076400003107190498800712091700038071031402800c0b250b03da94507000401198050106000d0256440ba2400b025035018142090021400072809810701150304982105100024100000c000805082d5801901650407a03d0701c00c903404240f00c0f01400070300440e240703062410103500a6120350848172403540c20980c14001400c1002c1040024100e03c80b015001c01d240110701d440850189c08501230181094072881515642c02034100003a5024a070002d080c2b22022905050039000f0064000d981c1c00503560b50312640c8034503072515000100c46d810862203544a0484074000481c000100c4190702c6007030302c02255a44000b102a031400100c280c4a1126031811404200988 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 508744343 1250 508743093 508743121
    0x60c1305101214012105100203060f0607140c2d0316090b09060d120c0f0c0602010b09010504020f0405120708010c021c1404030204090f080f13090e0c10090e 69
    0x25005c000848214550303003c10381c1c040e13800c8641c000e100d60001202c502c1a103400d40d000c4c0d41e10900160090301c4400141c4005000ea922030b05084607114018141c803804120100030000507030405940c03403003900c0074807e90341c4000740058031210301081403071031520002e88041c8003110300709030081041d20240780c594018001900352403e1f9203000b0200702c1b00081503440c01e051105500c070740045148038946c103412821215960b6100e4103440081102c501800003c1c4802d0103017005142c00d41c0001080001c940800c002e5a0043c0c0c48184140d0041c4040c5e0750f122040c40c1207504949003124030748a200034500300c05003040c07001c0e41b010141d5460040700004141d0042500300003000d1044400c0c3c04908680380a07500015145c0389480e074410240030502c0142015805180004e004000380510310180350354200066001c40c40603800c0620104903501c649003102e6481001d004400414032124081d400903580c1c403102c60340c0d841c0c4503941c4404842c180a005094400140146003208446c42c605400024001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 508745593 1250 508744343 508744349
    0x80708010e010c0e1002031611040e010603020f011b0209090106060f08010e010e09010f05090f01062c040f0c150e030c031c0306210302060c130510121401 68
    0x694200050108207000600c00e4440440c2141c03680c01c003401e640014440340411114180007548000c1256507004d84001c003001160a00c01c0000880d4941c8407070034041522445081204103030f04114041c401a0349954003681ca1180a11704801c200484115800e8181c2c4244c034081e40201441051110000041d0484002e4400d1900d98181d200d1380c5080450790400244240a00145000014068944600c038440d40000700e00c4000b00381e014800f006007088a5003510f030200da079400800752402c0740364203004000c01802006034132400c0c020121306551030f0b1098421100740f45128038000604002103424000e03001d907003284900703400035201c1c0a030030741c2d8a5004000c41d0100b0800052805a0320340041c0603100c03c40003070b0103480c12013041050340d11110790704030f400001d154031a40c1c04125021041a0085601c0c00142c90a2250035103003800780c01c0901c003800304143d59004002004450b90300e1402d101c1100c00c280ca000d0545511000d088030402ca00380a60300707800d4107040094034141c610448203416 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 508746843 1250 508745593 508745609
    0xa0e04030201060b1804050c0c010f240803030f0a060f0612110f0a0e03030904111b06070507030c030e0603010b09031b030a1b08120c0d02071a130e010807 68
    0x1085440e5040a0100c1c01400c141005c001c1750b4040320f00c01c604041d040f030f54002001c82c440b80d003071081084030142501d200080b4401c4c40c41d50f4030400340750f190003101c481160120600035a21a01d080941850b00c0740301c01400840c681d407046000c51507000c02940301d04004d059a2200b520482c1d00c03a43d009101d0508040148156030821410318602c214910440d0507d00201d000d031490921910402e481e1082040c6032940d0601080c0620a07850300c0e18011075424509180490355501c0445400c5044603507041c40c80012984904100200e07640c00c071048400c05500341c00e01c502042228907007294112448098150005c1001c40009084604400500b900c95012400d6a2110013210b0580480580781400c0590552241c0a2040070805617041c2c3c4e542031003182e007c00700007500c1d80d04040ca004940344001c0c2c40c0040c006042c05103400c017030111603103c90062025003101458001c41400491400104c01d846040c005541500c040302e0350080e900800c050100002c80d903940700c0290f9205d5210707218280ca = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 508748093 1250 508746843 508746851
    0x60e03011b210c0e011b020a0324060b211611010e0708031201080c012c031b0310181b03060906050402011e0801060e0f0a0e04030201 59
    0x15685810300407241503285107102024044495101114a41400e8039242c0c46210000711210814007030740905403449401e500c4600003650f070100010208414a450040c103541c4c954144e02c01070b501e848140c01107a4010f000030410702001d00c81a01d18141c1d203c42c006040d440c2c04000a28121228081c007a400c0440008007050500213220a81140d42102c09a41210240c1a4032100c54004e0101aa58444a00000418400c295000b41c504030346600004000e42c404510f15030b03d56210944d890240c041600604100002100041d1580240191240803180c603601061500400f0005109500e00020200c40b400f40c0c001c0c04581c441400e4000303550080c09410114034120b003c50080e1240409026416018100b56485030340c282071011650504c0d240082c4000030106229000d10801180a80da0004183c10248005803002421403814200c0c3d4104103500c0c0b0f184c2e6002100795044512034281000c1d24400b100000300b84c0c51212906a0b440780c200a070200e5000c9081e400a07214610a400800c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 508749343 1250 508748093 508748117
    0xb040812090c0a1e06030c0311120a0e070b07020103110c01090c1e0b18030c03070603020d150503100b010e0d06050a0b010801081902130501120203010501140310050c070c030c06 78
    0x824550402c034040c070700742407844004100c906e10030341c05180e40c1c8115140020b034502504071500ca00fa0301c0b005840400d81c0d0aa003d014012046104a00e50728550b0300003480701c07034a03161000216006a40010307044c565203104000c81c40c01d0107011203110480fa88002c12500040c1c1c500f0030302492041c001d04107040c50039078040121504841200003600c214000f260b081c000f030383c2011101d41c491414115014060103031640c20680b800c0009502400d034644002d610341440e481440100c89410301102c0022041220401154074041201c20710b001515401140c111402c10050707801c040c1c001662504221000e070f0400521145a0190740900c6203c80107001c00d4807c2c400440300c0590a0043e40510703000501e00d20400d00c60a4009202d40d480070340102c41040a503000c0301c00f191001d07803041541384242c3c90715000710310302841140d014000110110850004500129541d00c81504042016a0350740300401c011103044015280f8a943c4290494400d41c2c8030b1400b04a80900303482118089407140b0010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 508750593 1250 508749343 508749359
    0x1519080a0b0c04060219020402040b04240302040e01260d200f070b0d1410030204050a091e06020702150909070801150f210b180c04030b040812090c0a 66
    0x12004c842c0b40d5401810104840d400d804001652440100d034015800c0000207181c040d4003002d00010029038400c6544000030000200c05543c1100c4c0e44000c0510400c82440121240c0e01c41c14151460015071f00341041c090340840030505a410400c43d0184140c81140c0d904c180d1225038030000012003001d140651422000b203560740c8201418034801d80d00304032800e01c8030080d18001750034240341c100400306e03204407101003034424102e09850303020702100300000034030960500e80a03560304070301c41c03850030407000c40992101c41c0c000400000241030f030b444401c0c444080c01855015210b545400030a0080c0080c0301c0640d240c402c0c1e2050400074000c1e1000c4d000500c0d114000c102041c1213440d0660180078038068090304035803d00d5a580c0243c02c0c4014141409082508151110215850780c4800212100c4210420403856002410703035940389410320030807010754a54803c0d2012030354040f400403100d45492030301c001c050040c11441c220003000782c1e08205074101c000900c07210151007526074010454482c990 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 508751843 1250 508750593 508750597
    0x7171609151a0a0309030c0c0e04061a01020c011202040e01120204050609070f0f03060b030a06030b01080a050a0b0402030c1c1509081b0c10030b0906030d081519080a0b0c 75
    0xc040b00107003400f070310380582c2c000c1c0c11144106110345400080c40740c240c1e80b2503075419080e400080801d20303500c0c20401040080d200762030035141e400980050600140c80000c2d51807889642d002d042000d000503d4504138800d4040e41e0250002020031101d03981c48614940001f03c001c1c0c400ea20072810240881c450f400c005c040c43d805068582e8525840c0044038905a90380f055014000040503550ba000003109850000510b02840c0100c5011a07501d103141818007841406800030079440e08240410000628000350000c04103500c469040d010756a01e000003404c2030052042c040e04281c1510340751b6507050511b1256961588a00800360644548908100c2100d2443c0740c0109036000412649041d0302c1c51050039101a180c07003045030320050820f000308000f013107450b03002c0000c0783d142d880900d141d1401ca031070141c0c45001030b00100f0012100c04401440c0d02800b0b040c40c00e204401c41d0484100fa202c6403003420080856180d280307040c4d46c3d5000025079516a0807001e07141c07003480202041102120b502 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 508753093 1250 508751843 508751879
    0x50721031116060b0a0501090b0f040e0f090c0f0f04090809040207050a06060602070501051204020406051c03030501050d02090408130b0a0c0b07030902210c030a030305160207080717160915 83
    0x16520700c4040c1002700c0c0503015880004500555081800005810320355500040d100e50100000c10b4401c0c02d000340218a000303c0c4180c82803140c000b518041c40c1680304e0b540b1145006000b10703008640d03c24207043c00e454a00c00c140c5a190000e0001500038240000085c4500047d0f100e00c4003004569641d54040340c507842540500d1303000440c104161055030404803071a5400034001400000c20594a00015000004001b521401002c42c202098280b54240c41402d0052406540f200f240101d07681c0000c46056004000401c00d5201107051607040030b801c103110001c5c06107440b12560707c003800c01000c0c0014035001401c0311020615000524190300c2405010403c0354054440340c41069454840101c2c20340018481c007440c811224680b40310394040004808880c00790f140000e10341048215044105030102400096500c00003007040417500c000b0302c03901212800810111181c0d81c5218040c28021000801c16104190040c0810380c10b105500030181d140c0d01d0120500c0071541c0d40a01c001c0008028 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 508754343 1250 508753093 508753097
    0x2041a130b1204060c02032b0c0206060306060405090a1a16020c030c04050712060e0103031e1b020f061b060105010306030314030a02040305030d05090d050721031116060b0a0501 78
    0x41c01141c0080d030203170044000c1d000b003401520f06204110742102c420010301101c1d03030401c000303000580746049528441c4100e207038110310141100b0701d0b111000c02c2e0307240805030802740243d85d10b100190380c400c81813111101d461fa01c9050443e01c01409807000240610603980c0401b500c0030071403640140ca000180450368000050003901c01851224101301c02008028015020b01c04040c0100c0e103110440d00c0744801500400419049a5040d0f060080940c1003110000020800c08001d44000320341041000d00101482c00144135007414610114409903004c007070260b000f04000c9042040f400700302344600c1051700403400b2503810340e9a540c011803c0d202c1d2032102a0100d20a40b8900065103144001181d100e410f4001c09480c150313407555400c0c91075010740c5825141d00e542d00c0c1030100d40c100502404040c42c00a14005041801c3c42c0c030341c135440d40500703031801c00001450840d040c0c1150180e00074441030800740c1540c507103403110440c0614210300203603005c80349075180c42c05021003403811041003c1501d8060b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 508755593 1250 508754343 508754377
    0x5010302130f021608071a1b09040605090403020f010c0f090348090615050306030c0901090b030609030712050c010e07030804030b24040b0402041a130b 67
    0x18000c103400070030a031228202d0640e0200409081882e6034280c00600ea4807404409039502d08604064110000f0f6040c210406240002401141408000d02c0c0640310071901d03132259160703000310000d401400541d00164200d070008042106050b00030501000a82108009101c00000041c4c101e55102042d8202404112400c3c002d001049860241514007035440140c4004110705442806006070400020b6021000d01c61103001300701e090221300c900405400e0070074440d5906100c1105800c0516207240c00400c900803000030841d68040202c810003100c05012210b90713586807101d44024241c18412503001e4030a05010600303c140c0001241c00303c0d0b801030b145180401c40b58200b2a010f038003070410400d09640318401c4942440c0c05000700c000441c03042184550300c0b40f031464580c210440c0100644144007904203203000d40b401520198540707000454002640c1c4801340b00140084c000c40d00700c0e071070714180ba0303460513107442c04c0a008040c80181d01c02e5110a407035031490aa5031034460074940910142d84 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 508756843 1250 508755593 508755619
    0x615030d0f0e0607260301060c0f020d02041113050d0507060c15020c0616020312040b0a0914011a060315010f0c05010c081b0a020303041e08120907050405010302 71
    0x100701071103600d160441c41c00c0301040424500140d03407504030002c1034401428040055182e440d0103654220110f410b450520b06541c54400c0c050085462400003405400c1e140170b42c00115640c4000d82e060f0f01c0e5000b8420001016509a400f040d80c11013441807400345001c280205007403415601d02c1506560000003014494245541100c03460100e400c2158080460030b614040e50019001800a400481004024500d07003521000c034030302038004d03584040d90010000740e070360585130103211984280c210102024584403c2c0b940310041032400c2003d400d605c00c081031303040040c60640004448400f0800070b080340511000400030300744411745501550b8641884884281d50050014009100346070a00626814181e00c48609698520110038001409a801c00101c606030203041d075010450600ea02d401e004070740c44080d40d20300c0050009403800d98120f129030160b002180960041c16400401c0700d0f00c80032030b50200004d848042e903604d281401505808036203800d207403103041d0499030002c00281620030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 508758093 1250 508756843 508756847
    0x50f1603080c04050a1206020408030a020d0e090f04110307090f020403050c04110d091a150a0602070b2203140313090515010503060a0e10180203090d2105010303050c0615030d 77
    0x2106c44821102c0382c4d0280400100c0e0442030014143c0c10306650050082000c0c00c1100038004150800300314410407003402031003001d030b0740c00d06011b0f4031503070202c05606100c00700c01c00240381c8040d5034041c400907800e14280c880d400840380c02800407281300c0d504503a14402c8840400055130640700d41080d0320182806004144982900400041c601696a40d1000c102205005842460489010207460300c072141e000342c00e00301440c001e00180003030720141207100c6c00c24000c01c400344505102c00d8014050b000b2010826202e125041c00116404110380c0140001d040c80580c898010014501c10402c52110002e40011300d40078480c071031006603a004024038049801910305420261440d41c0007041d0f00400304045070721000c4140220740d0014545684c40c40c240310164900818003c0100c414014001e112498200140701c0801604a0410003101d00c0c0000a1102c0809003800c80c45503a4208400001815000402890044980c0d003c3e6095580c41c0007030f020100c04143d400b01c0d00b42d80810500b0381384e64 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 508759343 1250 508758093 508758119
    0x9020102150406020715090210171302030312090c03060903130e0a1803200a0c05091e0703020316030b0102070303050d060b0f0d0e0a0f0b07050f1603080c04050a 71
    0x580f04000060400f102074960041080400660b1042d0542e070b50102000e528008504032102102c13403a10f0422000c80d103041c5012107074040c0c205081c07000000c84510441d43c2c140280c0c0e084080c1080802e085141c8401d4081d1340c0c11003014224000d015900c0441c44003880401240c4180030b404141200d600c0c03410560510040008108031504c503900c001180750502c10b15170300d1405600950702c04104060b0a507126807a0440740101c680d80d9400103001310001201540140100c0314200c8840e00303e6502da90718480014500c00c043c15001c1013030750400c207a45806038051401083c00294209052100c1c100075002c030303540070300d138640503a01251003000002e105500408a507800b2607004213045035501130031403540d0462052000c6005000c5041c2c001645148a0b0701c0d92840a8001001d0160440d10385000c180300242014240310509000039101134019022121060785103040307941d0f24800c071140348003520004e00e403c40c0082e86620100d03090304e40c904295000d460380101403010a03490b14031f01031116 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 508760593 1250 508759343 508759351
    0xf050a0b0a1b20043804181202061e160509030a03020102180d021302070323070506090303091b0a050405190b09160f02010b100306090f0902010215 65
    0xd0302c503600c44200040d6103880c91040c00d4140ca0018031150044500700001e949620a0032000d001040d0380011640d814170b1a203811400c0c2c0842190409925034002c1005801842ca0300090120081c42d6141003101c5243c41c10b125288580c20b40c0c0482d1919840001c40e49100c002c42a42c40c0c0421011440c82001140c6500202c20381c0d0070842c1c60f100918000c41c0c20410301100a42c007503540071602c0810041145800c1580c0d41080390782000f240c80950001e04a64060390340c1d91a51903001c036070842090301a01146103284030030407403003803606202d101c84500c0380c0c44010700722103c1c01403a0105012100000aaa0098800070090b004402c40059081401d460005070154005403403800021151620322032076003e041d1030921030348150b51501c980000da9178041e8019028031410707008c0041c94580d02410b005003203000d2410b100c065152400880c0541041d50000707510021141c01c1d201000d41660240c000c4500c100414040d901040b0a16412905c540c400a80541c0040800102000c4200b041c2c5502c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 508761843 1250 508760593 508760627
    0x91506040c0c0b150a0f050d0f08040306021801030e01090b070c0201050d0c030506120a03020a0209130c2303010e0303072706030c0801120c0504110d090602040f050a0b0a 75
    0x1460b4400d440382c0d401d2003015a031603840442690850700143c1440443d60002e4103c800c0d02c00c14141c0703000040f540c076103100c0340050080904005140104444201200c005680243c03080d5280c90b140303203140f1024054800a0790129207007450f44000c50364180240300380b02d50058080b46040d643c5a0b010b40d41424442000c90420404200c0f0042c030300d1700c5100d91003403a0144e03980000d141c5003082c1401144441114860309662150040300002a030005407400300b070380c0c183c40c682d01c20741310282c0310704203c0303240703c001042105200c001090070301605502218040b08a000504d080c00c1039002d044c00c035a030f0300324014115041000050038460145030a800b02d042400303038641031400c442110106e844010340000740013a0301d4007040c0740a140d20408090250140380000007030352400b0303035034001451598420103024941700c69910080b00135020982c3d0868680c694140a285c1081c680f44000758010b01840a0080c0b9150010401c1e08100f0016001ea5600000191910703104410507542d80d050381e590040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 508763093 1250 508761843 508761857
    0x92217030f15032a190e25031d0f060708131a0408070b01121a241207030311010c020c131808040308070b0703020c030a030e030f0f07050105091506040c 67
    0x82e0b00d0321440e00c605c8a4507118440c0b0000301d03013810400c115071350300500030706010428401e56000d6045140300c4505501031038140040c40304c130000c01c060b050038001500800b8600503030001005100000c60542e00c20036540d0323603031031666640103109400c0450341c0002a00032000800d2020800c40400c6207076801500900d0701c6824900340d6070f078003018040260407110b5001c20a000702020041c26803040400320f204080d10345002e203041212558084980c100f00001c010510225000c151101c4807000041c04018040c0c6813150344a00307000d0070401604410103115840c10501200c02440491441442e0b240200310b110071036a1003d4503030150440e0701e440d6100c503c05518150004003680000e0004500c112000c079100d81550510904c2040e0091208003030500402642e01d07454008001c54040b41d0690030001500c0d843d005d4500c0c6140646011400f92600006003002400140805010154400c00c001c1c041ca80c4e40807165600c0782600c19000c41c5112603000403a242d4174007500140960760036850507070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 508764343 1250 508763093 508763173
    0x7020a090204030f05060a091a0a0e010c020c010207080115060c0c08060a09030e0d020a09270318091406060d0b1008010603061202092217030f1503 65
    0x6400c90740309600c11a00b07480e0910013502003060034040c90381d0002d50100c0c1040701c1030907901c2d8091071521541c20300d00c46d0500b56001880b090425840322041d840898020040d0048411019568200b94880b00e80984140000005c10a5050240c0d103a0518036101c04512a4a0b0000a80303900c1100c610446100400ea41d011503440750411469100e114002d0010490a0141c2006407540e1406601c8070f0140900508090160f20390180120459a1640c400202c00d0419001141c401018203108072480242c81c64407020306520a8004510611201303522848a44c2d070595941120100c00f0701840c84100c160004030303689000c40150240d05516080460717914041c000145c0c075501800d128001041c854801807080780d5042c411203020300b001a41800000000da00051411600146505c0d580c443d80c04042c584650204000d40c81c00d5401078043c4420305804070380399003a4004490f2940021014000910140c0c01c48200ba07180d014003401414085840c0440484c40f903c04440c0d010039550070404039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 508765593 1250 508764343 508764359
    0x80d050a0506011e020a080a0201090222110a0e19051306260613030e030a030c030f0504060e0f060405060408010207213014060108011e05040207020a 66
    0x1061049012110004042c038042e000541031048044903182801d064034811202c56400282c07229041e60003030030300c944481d24074800324058481381400940050300d01f044000402030740b608901e0b03680c00c10942031101c16011000c485143c00f480c5c25010019a581c2c840003d503061940c242c9000810004030a98003e0702c074000301c2d100c883c9501c041100c996852500300240640c4045560000c4140c80802411004035452a561020702401000f41c040030380310007c6c101402075054410103c40039058a61002e4241405400303e10700e54415008100d590359601d08140c420012a4140c510743c0d21030b000c0c03c1362110f0034000064a04041290814020040810181d840201900040608c0e40015a4962451603d01ca050f807200e0028010081d408243d410004d80058403502050700d655051540c4404294490300c0c541021825101c40e145040e54641800003c00340b224800d0b10700380ca5040060b61380e94404082081014448850703404600c0061007640b6003500240021800207103001c00860f1200b1310 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 508766843 1250 508765593 508765601
    0x3040e0108102405060c0c03070e040311010c090e040510020f0a020c03071202090c120a0218010e0303041806051003060501080a020705060a0b1201050a0b01200c0409080d 75
    0x40c1d06551000e0011482c2c0259800b42d8020301900c8802880b0900e21400e0703044401042c0c0c0255031084030f0124401c14401c03010444480320840040c01c440506a65911601c05000e080e1410380004686000c0c02000130014090a04442034580d0b0700a09140b81103000041c0c0840500100c50a0203050340003041c465a078005410321500800c00160345104c4910040c0c601050700c40014001d8004280401698171b0341424500c11903015129000c2035907611401e480d40e40701d041c6603064140030020502110000c0e550141c00d0a500d10b14891713075610780c040010340c0c442c64240c12140d415841000180401d105414030b51010038030090002c600b041c0ca54001400180e001c044500c0045d40d5408200f11540e40242040d8020319841c10031442c04450b0340f10161a948014600204240c030340e02c5205154031944080d0125030500301c020402402c00100c0749021340032142c1c1190002c0c90345c00422442e1719025043c403103803100303050052007026078050078040030f00b80c4044292210401406400703041e20031406 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 508768093 1250 508766843 508766849
    0x102160b03010f090e07031101020f01020a0329280503070b0c12070f0318090e1e030c060f040305070804030b0604150b091315031a060625030203040e01 67
    0xc08507101d40c100403144031641c2c1c05a2000c200581041c55a0300c0440011400f04181c94000303c041840d00035140044c0d2030500d8000d650311070356100240c0d07400c6481c2d05a1240103c4080400c03600c4078070300203e0342c9404094080041540c440244800c10103e03c03010800e00545182400a40c0c02017aa1500007070300b408865448840310400025201464010912609000c100015203c505000194450303500c2010369200080a0211400c1921445004801108001c0101031010301c643d2400a16850b142c083c44404011407402d003039003600c070b41580401a2142084444014003055840005855540300003034401c0d024428204410804510a6001040914001d400d0a82c0c0c2d420541c06110888e00c0d0344810f136462400c20403050040022690407184014011a030447d406510311080030000c252008417900c420740b112200100700005c4409002565068110780460307607503548148441d52080e004070b10381005000c40c2e0f03c00221701914040403614002d20440341000d40340d000d0341ca0303520702c00c1e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 508769343 1250 508768093 508768109
    0x8090f0d051201060f120f060e0103030e040b01021f0902060702030303090601030b06030c0904122007051306081e0a060f1406040c050417030d02070804031b0b07020609010216 77
    0x24100c010390b4400d0404500401d02072400090010044100401010010140d4051282c8039240440b000c005030b00042c01800358210341250b5035031359140c081d00b01060040b54500940c1007540d202060341c00401c0740c2c0c40440c460440000294007004a0800424814074101e81c41641886403001503202040a14441d21320f0000038001075055041c0807140c654002c01e4248a90721603086d2070480e45440b86410b07001035021902d404a0100810261918801d80080100251403105445500d200019220b0700b110420f9031000b0500481e42d041c8020780c0d02a0050310503507031180246100b51450100f144045468007400c2d10f5006940356260801e40d0318003241c203061541c03950000401000000006504460111400c2100b042481e10151030f034002c92003020b0301015548240000740f481801100c840b403525800456940050386440f840c80e80260100350f5581c403d0f400d2820024010f4180c090a640040b541141080300580c200090f550091802d10f0450160504c4882105030203002500901216 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 508770593 1250 508769343 508769347
    0xa0f0e03070317090105090a030e0d0b0c040927020f1302030916060305090a03230c0102040e10121707140c030c27060105040e0108010603030e060703020d08090f0d05 73
    0x1803e005250204098040d400d2070b4540001e2180011000920481d1154542407800040c0d01c00000078401c0011410040c20064100c0100245e0030310b540020400d85440c00c0c003c104824000407000039419000006d01500c003d090401c0c0058903141e2031800c0d8000000b0a82500c1c120240022802d903002902e21185540c44540241c09034031071b01d210000900355a00d070401c96460a10902a81c55801c0c000c09401d10510802d18891010900c60380e03413401c55101c1100350384001c000d004a0003944a84148032001c01880c01060f2034081c2071500c1001c850003105c2220340d142047c1c81d11080c1840c01c280306000c2d0034003000700c100051401200341540c0c1b002200903140e00c0102105050a180c6000d041c64482c012940e02c0d80c6c81e40400c0c0080149096a05004490b00d6542000686440c807482c1c002429298034200001307001d81c41508104181e030b1080d903c0961020304181804410f00440c0d4005002da005102d400072481d210b1040305038030284000480c0c1c4580b4000d0030140c00c000035000c07100c00007800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 508771843 1250 508770593 508770617
    0xa050a0b06070c1505090d0b0702120a08060a0f0510030c0201021b1f020c0318040b0d0506090f030f09061c0e01020d060807030203070e040f021819060b030a0f0e030703 74
    0x104480701004c40000d030810a10349412036000130000082c0c0c4000806204544011a01061080110245501218500c281d4a42c003402e006000900101c41c003e00c1104019400305004030450200c41c11244080c1440c3c8100c1c0411200781d01800100040700308541d42404000900d8820000416440035900c01a00492100540c41c5a0540b89600c1603024031740100103050b501c041c000200c981d024494000340744024400750000b00500b201d851140c1d03200741ca0041c01030078000302217500ca0040c100d860481e5a0ba609008a00e83c5074050140380c240ca41c64103002410f0142020b000508840d449030598000105002c0d4580088600100741100c0c5070394040b5035880d0301e0480b489028041e02403036000f441841d1035580003035582e1845000d1124013035000d01c0460208084e20820700b800030790080c010400c024407003540c030600c540b086401c0c010705082c40301030a060000a224450645400314042891651490224000743c0025500c0318644d60340e84400021510040c03010b414910f03c00d6862038240c100c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 508773093 1250 508771843 508771859
    0x3030a03090b0609090304050d051009062c030d0b010509030d27050312280c061b17092e0e0d09030605151f03050a0605090a050a0b06070c 61
    0x4000c00180c044c081d01800e0104040c400800d860495504650039800d1000f1882d00a04194034403001c0c81ca418206032505d410020250043d916000410320118100c105901d0b0001e9000d2100489640e160402c10080744909104d8011380d400300d4043c102203127040001c1000c280f5161408800c40300107040300b54015030814540a024030207040a0301d2540d1030a051034006501c802d54800d00a1581d800010150f0030b086503401d0348041820f0560011020303000d11a005003101d012517204030394451030119500c0ca84502c1400510402940d80d03203807401c0701494900126810400342244a043c0300d2600b6400700300040303001e10003112880300503c6608045e940050000d4454102e0405155005500c982210755807045520048030b402020108442d11400500c001102580c0381c055004506c0d02d00340c10742e444462881d0500c2d800355944c10000d0b13940e140c81c0d50301215480c0c0106c5620082c0100854003003c51500490380000f00b00c81c0001d80160901c0000b50340f81e2040e4401c40c0c1d078144409007044160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 508774343 1250 508773093 508773113
    0xa0608010c0f080f07020c0a060c12050711130b06210a0519020d02040308030c071a090d0c0804051f030c020105012607030501060f080616021f090203030a0309 70
    0x55042c101502c2e41500880080e0a440e0020701e40d440f402c0015002135940c07442040384481d503410280001d10032644500c8004c00a10964009030760001c400d10101c0f201c030344242d0848000640202100c24130305030311402c00490215260032091580e4541152440031b58500c002008016203540c14040c41c6c43ea00f26a00410754802440451040d1070702c0200200c0c1030403001e10340800d0545510059a442500e04500028021500301611714031011040008004035513008054080c0205e8580d00f080343c6006081508030002c640203c025081b080c02980114002c42840c1c0c01144101038150403d03442e640480c03400b0002c1020341c10000451101031050507054400d20700e2030740c41c030b1009100300e60414004814481100c1d4010081c00b53300f40c61741250703010a11031940590b40c014020702000b40d03103841d00016402d980c0103d2070300e40038207008501e004503030b1507010301066104d40141581b4600c0345008211400030441f83e51140d5110031380e220050381c0500c028030110181d0303140028018074a061801c4c0d85 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 508775593 1250 508774343 508774361
    0x302040e03030609040f0c120b090118330e060115030c0f050a020a050106080c03070501050910050f0c010c0512070c0317100503010f1a0102030a080103060b0604030203060a060801 79
    0x96003040083c0105038a40e40c10039540a038001d00d41c00f401300281d107411010700449a001ca004c0840d800c016000300f210340c5843d01e0103419280c0080c058903030b01240040300c0c0f504120004160702d04c0d481402c20840700900390941181000303420050301101c00c00ca424151103522841e081a50025001071102d00b1030b4090020703e501d00d5140c1048102c000b94000342c0000010b5044805020700800c2410301544200b0088000d20f5001d0b000340241030741c40d04216910706001d5240c13031281c007031903c0c0881c0e00d51183d400c3d2050b009008005062500301884c0566030741c1d1219142004000782040800ca00c50402d0140d80e46a03030140d61500e548100c0215a5154400050240d80402c41030201c00408a40c0c8080e42d802e000000d800e000c442d03501c501d00742d82070388005544079581550034004000700d60b551991242c8440c800740c10000c3c1c075101202c4012a221301c9181140f03000302d003041006101040041e4400b4101850241c8558075003502d81c1c00091500ca0202c40b10300c6d81f43d4543c0020320500c2030038000c80c404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 508776843 1250 508775593 508775621
    0xf0303111312021f0c020a05030f0c060714031305090114060702090901061706090d02030408060a0207050313141203160f050a02180a0b190b0a020a0c090204030204 72
    0x1889a000603000700d12800388a030600c0b242140d4151819541c074128070075200410190054008184d80388050f04100c00080b081e8401c200309880014541030210f0100d0070054508050b0118010880c204516600010030544290f03144140c4072083d004200000c02c803c90908240e01481454001040502141600400207008000701a00790607100c5c6425660f1403a030407035100c0c6450340c0d9098181e00500e115800000603101108002d40c0344000860460b0094840c4029030303043e0305417408240e030b0b00c0c0b2803486080550380c01600040e14101c07055010b02400c1e4414401e9a00e00059000410704510643d040040c0004120755174070b035a4540481034000c540d620f000030b5802d00d1814003034669014002c40c0f000e44005e0105841a04002c0240220020160300030b0900003203095441520380c0808040b01c0100c51285081c1c2159514035180d4000100e5200d11607680600314240342e4800c1031034201481500c1507115021102c000a08040c031040301a2081207401a00c9614500401c002d8a51215421003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 508778093 1250 508776843 508776847
    0x1c05030403050625050429030c090f0306160c030210051501230d020d060905280608060403140d06091506080421170906010302101803030e0406080a0f030311 69
    0x11a0b40c20000341c400300d4682030031580c7c22400a4001c035041100f600c14110b55250300000300184142c0440150071141300555403c2e80c4040c0c014245179580005440c0d0b56800080c210541d52074a03c00d0384440003c911034415581b00c2400c40c054401918019076450f450522407292014103543d00041810302c3e0601480d000c00031080c120010240c520075440c1c0c5c110641c0d000186407075035502c81d070400e1000b000801401c1240385080c0001224100d1500c05542034644042ca16100e004405d006400c241c5080501808281d1141e507015102c51480f41621440040180309020141d102842000d005004007035001c01c1d180312034802e007814482c0a400c810b040c0300285081c0004100805e41280c1c2420384400c00301083c0c50f502205031078580318280c40b02c80301c942d40d07810859144004550f847c1240e01c02d41d10302c11038140702501948c51552442880c2481110013038204003007486045101140d18000c2c1c00000c441d61141d54003424031113000c1b815902c0c80c0c40e02d18114101981403040010010b5034861040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 508779343 1250 508778093 508778161
    0x20105010e060105071208130c03080702090f040519060b0405090a050706021209060c010603051002090a09060b120a110a02030c07050907090605030a0f0504120f031a1c050304030506 80
    0x108840b18001454000c10487c1400a00648804107210886540014002400b142c1c0d0b860604000e6001180803400f441c1c0d0400490b81a0319150009030203141d1110103804104101c1c20340e020607032400c6c0c4090302e00f181c640c41c0345902c40e100c40c85502d0240802030040d085045c06802e066141c2038031948500c08541c032040c0c400d1680036146064070017410040350309641d40c500340f50546000d44099000544140511038500c5843c454903401440044000e9a40108595076548440212401b80c441c00f1001e80b0204840340c18600c204000a500520004000404111542604406810403d4000090fa00c009210000307074004006a00040c0000c503204110740ca020b200003043c02c21a4031995050040100c0403603c0c00145400038990346251040401081c5014105904d005a1004003013010a02c0c8100c0111014030038094240f91640e502001100882c0e00340070300c9000c054244407941030548030385d40319001403000c0c0014001940584010002824819002d0340611034005400c00300e8540a8004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 508780593 1250 508779343 508779353
    0x2010b0f0a061b1704080d032c070b0c0d020c120a170405151b010515060904060509041b06020a0309260708060712050c03180f01020a020105010e06010507 68
    0x40d0003514501e140c082c24243d4010388440010002c0355005280c41420f141d95282c84048001800807101804121350100c5003041c406d0f411958001784030100c2002080c4c814904864000322080c03046040011507500d0b0b950f0704244030590f041046803111517084500504004c50703042054000440081700e11004908019404039a100001e0703074002c0c10720011002c0390350007024071800e407001444050a501e9810070b9604070080705a000c01d03100c40c0b1700b00c502c80800682207814824184a2034840d03c0310946c62066000300304154106200d40e50380141c0300c1c0804250b9840e4041400d0003107100c0c81010740d0710003060708001c1c7c1d60383e001d4125004560110240b503006c03c0c2e02511310b02c1250410514101d52000c00382d41c5a00c500420004001d552054400000703507510006442d44c45071806a807001401107002400c2c1c4d080d00e00030748050000d0f020900c003241c00364113094800d44c107840d01e02c4200d4504041e84a14142681c10074101080580d5445c401080708500050703041c4c0d840002480c0c0307285071195030b5840c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 508781843 1250 508780593 508780609
    0x1a251b080d1a0901170f0d080406050f151c020a090501150528030b030a03020f0714130209030102090d050d030b040b0907032004240e060301030b28050702010b0f 71
    0x405e031000c6105100c0c0c0e01d035507400313210784502040ca9000341c80c00b00222170006031991500b614100c4105290000103400c0403540c9281d41e000b0315403114510101400c4100b00156040c84070752094030300021411410041e174514440d00010909001c02199561500030700d090f00030007051610003030260400090b40c050088004a090103d0030038a542e40701001d10300c00724000e00c5000340c2e1540520550311200c0c21701d50001007200402002e5000c0390354658513010a0b14408a11000d9580c004409000446008545402401c209c4002800050811011a00046514288500640d02d582007481d0811050742e00d40900f044800c416103003407108042010100b6011440100312804066440407031148494540c00241907030f00c041030649032280d80360805014958510f10f0105c0e160320040600500c600d00820122609040090000d400c6030b00e1500d450706118801413406002d013241c0510b15020440d10001c01880712030880c00019145040354003c1d00b107036078008007070703201d070074402c41203802e0f59074000c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 508783093 1250 508781843 508781849
    0x62a230312100806040c0b0d0603021c02330708130b0a0f05040303050f210a022701080f0901020403080703030606020d14090409020d140a1a251b080d1a0901 69
    0xc40d40c8d64901490840d04010b026a400080d030002c0004491401c4c8015806807184a0303000711441107124442483e2100f0303103420004081c0000550b15411071070410120003500065002e51001850301300400003c1d0303100401d03500f108a100d000031500c040d045030b1151041c5100702d0300741007031031410f400e42e20003901a000d4401015401500000c160420111004000840404001c1c0503209814504128000381d0800740310860020b00360380c0fa4403030082c1c030131125440e81c0906131204189070b00c50034104c50701c4442c01852680299002c110010001d02120001d0000c54043d5030000307540b60912000034105007c0400800402c40f506c140810080368403822500c0d4560101e90001c0d0313049207403011a030000200000584280d2a801c024403a0640100e078200c941072065003102c2841e07054079019000c141c4152000280c0c01c9044440d183c4e207035882c208000308810f003420920300b00c07000940c0c0340d0039070407004808031040c01c1d0200714202416007074010745620400680140500c0c07003400002c2000000144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 508784343 1250 508783093 508783109
    0x507060807120902040f050c0c0c04200a18060f09051012020309070b030a0b012307240f0606080108010903020307021e090702010204062a230312100806040c 69
    0xb46030f410855445900504038200700200610071303454040f0b032000300c6030040c0840d0180780c0103040c0644510f28280c811042010240c43ca0180103580e4862a100150007c004580910403d078404003003401e00442244018005542c0344102e001100303d0052000072250b2100e8022803090962651351900407584140811468100507102c1c2c3e643d410700780c9807620541c01451052030000c20310410325059088041500c00a8071802c041e4012a0803c00032803585100007d0f18120620036000042e10b607803111300c003103000c1524183c650302c5600489011941e14103c01c52096a980200b00141e0b50060283c40c010401d5000803c074280c40351300d0103900c91042d071000034880d038040269040680070418060340b03c210098403034859071070843c0c0b010303000358003a026000101d504040360301c500c0c0401ca03a60300f00c41380040411a403007584a594049540c0e0900064201c4000002c1440c584048108082e03d1401c0b1090120181400e11104158801902c0d41042c8159004070080001040c80d035000790040354050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 508785593 1250 508784343 508784351
    0xb0702151b1b0d030c051c030609060b0703080f0703090204110d0510051e1302040f0911042111091f0b0304030e090705070b13020f030c0108070309030306170a050706080712 76
    0x303180c0b107814107c058400d401482c0c6000c0012049640c15481101a02c001860400040c2d8984202c2462401040c00041c0000c0c0b50500060003540720740311280c0c0020341c0b0704002c10005107540c00581640d0001251640b449000300d50514160083c0c0902034002c12442039240005083c0000b152502d05514000b076185007019088400c4c90300e03024250f060030060003204640302c41d1229004910303c2c40600c2036084881c140b941d0300103400a1071040340c04480c800ca00d240481102e20407040110440704134241ca02040811052600362690b82c121031080780c10300c0f040010170031440e4048070f8085d003a403c2644408018410400020340240c100d01031542c0c1150054031558400d802100e00c0d04c6160401440c02c4014000d201c8000c86080103060854821562000c2c46001034017419039a00e46002a00d000902c00c5000c038203464003951203194540e009280120f44107440d4441c0102c64044191118801d500c46124001400010302c2034001400b810701c0c1906882c00d003108010482080512a11000d50355 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 508786843 1250 508785593 508785617
    0x80d05250c0f0515072a0605220615120b07110a1203021b0109020a05090606070204060305030a110a0308060114120a05090f0c0a0b0702151b1b0d03 65
    0x96084201c0480d0f03020048810000100120744010310040e501c20012403c14803c003039801b07049605d200d13082c0220f888502801d42164696002030440070300314240281001004222508448149083c007070b000d017038049500c11200041d4003401c591a0b00070348881c1c031403480c4400090084008280c0143e450300c0c0c0b44411700900c45001d428000000001810081075009445506030035401a00c400d25403134174000c1820402c1e10586007070f5140c8080007503004820200c02c1c080f515124001c41e40061001d00000d04045c030550109045890980064403280d0011036048101503004d0610f0304101400c2c00584541c4056503000f80106001403c0b41d07048c4942d01c14a20000f0001d07109171110207400f02000e41040c20120100c200810095074121881d0056400c4904400f400091fa6802d06101903c03040003180f82060170005074000000890b4081c44c1130b06044d080c0c00c0303188017030a41019054500350880700210082840d2424118000210080356a461801a40c5404507481640d0309030410500e0540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 508788093 1250 508786843 508786853
    0x203041202100302090613090c0e0102061906050d0b060406120b0c090312180a05030616030905010213060818010b0607021c1b061206050a030206070311010207080d05250c 75
    0x350745d480070b4101c01c001c21070724030000220425804840d03440d68104450711280d4002c0f00c2c1c4048002c00030340960f10410105462031081c11f031042105030500400075101d1b031910000b401b00c8040320015606c4150b000103105940c076051080900820606214513a518110b42c0d8646441d00c004024401000010403520000c0e2800e01a5001c0300c050303c4402039803640f01d0307001101d003503120545450059000d0100480c00d800c0014209014040e0b0210b1307003210704010302e011009030030041e000316840d5409100003440001d0a21524000d131469444142d0f0618085a9a032807c24010b59240d94036810030b040c042164940000300d422503034054904103d401048041c0d40000d4140071130061040032888420600c0900e00401c40c000c0c1d8040760380b5600b01000d1140e2600c00d98501c0d008080e80f002d18104100300620303102c00180f41152107410302ca011010b5001c401c2d0308a8204050540354680c001400d45100001881403941c8040d172400c440c0c48000324081d02082000d0310183d2030307046c820381c14110010700c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 508789343 1250 508788093 508788097
    0xe0c011101140415050601140405040b01090509151c03360b03090d020c0306010e07090e0a0f060b130b13030f050f0607091d040c1707060f0203041202100302 69
    0x100c50780319951501d00301841c1c130300d903144c46280c3c10844940c68040441da00358031075511551440000548107080c81e0915007080010140341400d1418010240d000056945070280072034850248203100f006403c0008003400140c4001c01080030310451640d0100000980041c4025521681d2050007010103494210900340ca0801400107410340440c2c980001e01c608001004510491884c0e040d10380b070707000100041c0e0303070345000001c03165054000c1d100500644c100d11b0109540520f0a103040f24981303644090044a00c0b40039950394480c1501ea44002c0b08817003403400b40400402003028000c0c94180640140b005003980d60007403042c14a40080e918809103814080351003c1c2d50080310541c400115440d046503030f0301d051503594110380070380310001c2c025501030049141214a0550303034042075000d2070701508003c4c80c010b00403910300d001104d008c5011400c000002c6010081c11004010306820483c01505034542190200215403041000340402d1681c2d0f5503800907a91b054520b00080c15540605401074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 508790593 1250 508789343 508789361
    0x40605030601030f180201021605090c032806060206060603040b1501030e011a04050c120a0225030503040201021015060507020a1e0314071202010503060301110408010e100e0c011101 80
    0x25410701000c1d0185a2444c2d0040c007502e07100340c0848080c0e100306540519645214401cad04c0d4020070a0001030041003a1900550380031b200100101d03a070104608407068003024510101e030501da41d9450502c40981c0412100380c0220080302c0041c00e61030181e8458000c01d41c020006659110801001c4401d6400390300003112262810b0700a109905440322011060207100d10182d20840c20080030410384042101200c566450802d00101141d86201da00c0b0080d5004c400c02d100d5100f114145080c003908940b8071003408621a81d00c403a50380c2090300009140c140c410840d20090307071512505064040d0052400000c440d100e003000c0d5254415400040c41000c3c056011724003100517546c1c07640701424603002050030b6131710840212000214000d0072940d9241c60b401b0300e015140350703040e14201560151018550040004001007090000c281d41102c040d041030740001c07813982d1600103017094407170305100514043c1c1038030008020703840309200c07e40e0755003d1140403141032128007816135080301c0e001e421007901 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 508791843 1250 508790593 508790621
    0x1903110c03011e1104061b240603050f0705210709050a0b0a060804021815030d020309101e03020f040e09070f0503030a1e17040f050c0a060504060503060103 69
    0x11504610610354221184072400541500c0c2c8030303c45005034a01000d49096900702d60324444010b4007d00c00602c0c00c541154103491040050b0381584904c804a500a01441800400458010300e10324090340b42c90104004128542c221604c1071007182c55402c10030246e821203902d441544e44c41010300a04140711600016019401c003000c104180c64542c018445940c0d040e50300940d0695036450031120900c00b039500a51129840c60501840180d0f400800d030420b03a4030209040903c1d8032000a8904641000f0b280050381020440784001e00d40300200c9521005541846011030b01c0507285c3d5480c0d060701000d03c10a05501151880031030749080d05980c050711084402500c0381c00c0201c005961982103110709028000851004035680c01c000c0142c81800c0305a03200c07a52000342c860b10110120388100c2d41c1400304031030500ea00640104020880740254003621f101081c42e40141801401c222514056a0060806d00e600b00001640300007180d007101d120789016900d03030301c41c0d400490141014441580c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 508793093 1250 508791843 508791851
    0x150d0b071b050705030d08040c061805040c02070e01050607230304030f110423060d02041808070521031306060f1707050114040504050a090c0b0a0801081903110c0301 73
    0x10010009103c4058030011001c07581a8610342e5022605980b08940050001100880c02c2040381c0c003039034a020340558510b494115843e00e030380120307040700e4070000000010fa0081c00c040144410300e00e001c80c05004192020f40c603000241d00d4070190a45056103022250705140620604c42c0001d00035907014503400120342d0039000c998101400400c0711101c40512451503d00d5145150200e85442c0807480004407082a0684e40d900401c96040b10505059030041d8842100781040061440c128001610800791a5250032160501c107281040790a60702c148695100f420401c5000307000d066030b40c88017001000d00e103580c015160040c090100c640c800d0b2000441510007240d00c414903030061742001141b0044840c501e41e0303400119500e81e2114800e2454120401041c071050406030001680119010004039034014950784020070000581d02100d40107001241c606030103640030858600400400005000f03e4400206e401c44440f400781008090049544459800890034003400b0452200100208 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 508794343 1250 508793093 508793147
    0x30708030606040902280201050103021e1201020310030606080a0c050913050304030303050402011205040b07031a132a05030a050403020a0210020f190c061b0f08070b150d0b07 77
    0x380d84034946d92030035940800c04007002003180c4144243da04070307600280130281c0612100c10341c04014442070500d0b90020044110946106024002540590810070450600c91300d1420408100d4100303410030046904800748060108001104c184159a01220060016240c100c803060b80c81520310387c001e00324000410b00009054265104500c218000e0701c4050b5810105007604003110001c0380c004010400380c0c00821510f9100b64042200740400d004100d9181d0741140004a50741944016071480a0702d6500d450030b600a20741d0701d0b9001c40c2c00340710005265808201c0c085c09a000007040701d08141d40d564001014103101b00b02c0f43c4110358014002403100720910703074000d407038a07a401da43c0da490748900e00039840f41184c0d444401811a41100c585e0304034134144982140c1140c820080540300c4200c84440b180803072501240c20300c031940304851243e034a03106481c140110041c01003070b0403a1700d00e40c51203d107015280e0315090320000d0f03400706130f90b11681e039155815100c41c01c038060b403600412030161400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 508795593 1250 508794343 508794367
    0xa052503020c0a080303190c02031216090602060c09040c030f020a12050709081c0903170a020105072a0203071a120606030c16050316110a090c02030708030606040902 73
    0xb0004101580c803000565104c6442580d41d100c03e45221b00303005401d19450f074460385194080c0302c1e024081e206a03441d056004560104a40059848506448481039020041d68200d20480d0090109001400552521034045002406401852801180c440e021801018401c1c0d21256a5526420085403a468150401040001c800d034003e11000e01e0310012401c01070141012504480074217005108000070780141c911019081910320061003104100803000512940d11506234001180703070345440718070b486402400d40e1806000e00062040340d1440245c0c54107a00003030100c000003076004040da84090300c0800d00d4030710341d503211100224071886c00308203420001005000329001c4400c1c0030070644a8600304034042c842521000070f000307020010f00c1c0030f52211000481d00c96000d50141c90910640d40e0310118a6810702104890b01158031700d0320b151a00d4008105805806594070800c0014110701000e99284200440502521008400110740c0d6803860304480240880320400d645540f54045a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 508796843 1250 508795593 508795603
    0x14030f160507080304080a03122a0905040c0c020103200a030f05060a0e1602210d0c111e0f032b0209090408160614012105030a05250302 60
    0xc07101d60040e098002000070f00042a02c050b2440c42010b0a240d41c0a56815190202c4111480880507211098400580c0b003d00c80c107203414141c22203030150f8040c820702c020840911500300900c41c5103020b0b0302030310440d880030b1101c3d0300560a0800190300001722084a6401d484e02d5000c508070074000605940c1c0a52607080366455422106060045807102c2d000c000100308580035044481c020b2030001740ca060210030364240b80140c00c0c0151100035180307070080340001c4208002c000c4521400903c0024140c060720580c00b140c04c1c5403900c000c00500d005505074a80c0d02801c0c801750441004020140300300810b0009462054040c0101da580b0010340026100e020b8000b2400b1040300c2d141c0210402c0e000c054022202c403031200800c82c101582d0307903540f24066500450101d0800699412245001440602c2400c0100c081c0c0f80411207070b5072421a45030300601e03040a20051440240e411840000e8002085e120718908506080d07403640e142440d00d4038800c0205410480709140020034505043d00411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 508798093 1250 508796843 508796887
    0x201021333020a051c030627110c0303041a09030910031a121c0804030e09070314130c05180f0402010203130e0108060c0a0507060b210106090b0a0501090314030f 71
    0x9090051f1643c4105203117105100345074140d580c00d020341c55058850507983c015401c1c403805490150401c050070032428610781040f01d08884180d0b81032140d03030059000003c0c659000560000461901d501c1601081510031503e2404090640b00e40c000c503a0b501f43c2c1158003840ca00d015001d440807119010103aa92180d1205070a0044540c0310120a0342da4401c0f10164862038140d1949141c41c40c08005000ca0000000c0c10201019075880c858904440c030111207500032256592003081840c030509002d00981200e0380100c0c4564198269540703071500b0703510320640c802a200101801030f034480c00140e080d8883d881d07140b4100d2154440224054100c030303104506070f031004400c842d150395951481600c0d511410390705c0c2c80403540a01c00c00000900e250031003a4a2440030700041035030031490150506420940c04800e100c5d0351500800d11008141e44251000c0300c1045031301d5440c8628110003e440707640d841c007000d81803218051038100340f200d00b082100c01c45440c28080560b240100c000344401c46296403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 508799343 1250 508798093 508798097
    0x15050306101107060f0e06071202010c0518090405070321030e030f0334030e010b060306060a0c0609020d060504050d080c0405011206050901060201021333020a051c 72
    0x30149440c081d200d05020758880210000070301e2990708280342070314044035001d00c202c1008601c010000e001c3c0c0718440603002a902c05c09c0d016503000388600003c1d00f51800c02982c001044001c3c41855004541030b0350003028001c09440000003034131a82061402d250454001a202e401d0104440220018411070098404010360b0104444860341c0410381d200d1250303002000d2001e00a0010ad040b59100e070301c440c030700c01d10322170030040a94040c3c8440146074200d4500c1080841da480143d10310581080c01605900300c000c8860503d1458940300044240c0160070803e02000100c14210007000840d070f009040254006241c0000d0a41e54a0050050700381100c0c111110700810045080443c0034882c43d42c06a0f4140c1080780c00c040c103000045810804144600d040c0d640c07039010001300364813800555400303446203a001681c2c40300e070000320070b030300d058580e120340702565610000389038a414424040c111380101c1001d100350301e40c3d00340040740b41000500f4007170100e0103401d1882003044010073304491400100c2e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 508800593 1250 508799343 508799359
    0xf11032517031605030615030a090f2105070210050a0507060908070317040317061c052b0804060213080102031e0a0603031704050a0c0b090a12020f0409080415050306 73
    0x3d6042100c003800240e07440f94000445075810440641d486000d1a07100d504d801c40003803060201e840e100340ca2021298156020918071041107141815032201003841c9000341050fa181012035804140482d1107109007c08014000c50241740441c403e00031101510740084060280302c58a0505418030760040008801082d950031402d01c640c032140d0b440740e209903096105c502858545a548101c0d413000107090b42d43c041c0101910055600e0b5001c8103456a40c0644000c20a4517203000c40c44541c41c01d007241000001f10032419030015268498285603010741c0c012009600d420442e042d400180750650000310081d40084100001540d0203410851840c25642e4010f444c3d032035114000044500901010300003941c01d0144035448010466000d4000d4482c500704d5075482c1c00303900c45601c150742c10b030031441c0c42680010b5407455501e042d10500c0058544443c418000e45010360004211481b0140c425000740d4a0761802c005014023041524018410540c01888101222000030642d07030007250325500c14000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 508801843 1250 508800593 508800631
    0x801060504060f26030f12060f0d020904080a1e0c05060604050c071415010e04141614130c02072408010605030c070507030b04030f1103251703 63
    0xa0110f0440f215420340a00403182003860304140003003001076103190b2200708688916503484000404800070098140051410440104903508000d596450700c60103c001041c00907039a04e1488a80240d88068001e95035418241c0545141c84401f078408040550700c6424040b25812403d40440c01d44207800362501580d4500800c412191305544041411009010700c00001e00203890041c000c0f0703e4441254541c156540f00758111501c241c000320400712660342407200b08484198079204015030031001c1c0840b15500300c00c1e60314402980c03241c820000c0c003003c0e03040c090351610058404800b00015091000007034401005c1d50720740322881504d580340021b0100c00c60320320140e611400881800d54031200640d10f050390031107594001030154078143d042004540d000078800c01680340214402c124103542c2d403034642406000000040181c0042c00702400c2030103210b8002208540580316000c104000001c5070b0208508900004400188820420340c240e4414180d400055482109041019074160403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 508803093 1250 508801843 508801859
    0x30608151e0106120906091e0c08030a02030306040908160803160306030b0402090627060f0904030822051e0c0109060905090a110304060b0a06030e060103060207031404080106050406 80
    0x2481014006144014844c00c400142c1d0005482d503801104042050b00c096110b9019440c801920300c550041e03016201c0c0100b00100e102c034001000074001650401d03000c440040e40303e00c00241010300c01c5580300040d50422101e401511480c044402c1c0c4508601d00c0b078076060086600c242c804a940c0d01c10804082001c911a0140c1e00642e54401411081303a01c81c2d40c01d2244002e0040c010a611400d101d4407440d904d030100c110700c400a900e04001040d207080c10700512044551030390302140940d443c0d20410011a4002c419150002c0a0264040c44804060b41c0c400421603c100000c000b8010100100488090320840032000c42e440010343d0200c4c0091001034458031104d219400c08581051002c101c2441c03d4564168003422650340850444035038100313940c49030700c111821201d10355102c400c00400d0814242410151180f4182001030008200c0541e68425052000030108d80c3c0000304e6504061042c00050b90804002c0301451b03c0700e4680c1d101038041c0c002c0b802524011440c0081c0007520360 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 508804343 1250 508803093 508803151
    0x60902011b0c0e3603070f0b011e12111306061e020f060c030c16060518060705070803040507050a0308030f0c09060f0702011e05091305090303061003060815 69
    0x565a51189180085100d07260084d07031881c1c254107501060202d40085180c1c801d0080009204484200c4990306010616252200c0d0319036880c0c62541d80e0109200c03282090011000c201d40005541800406400000e04007140c0c5010001d03200b814030000080b01074100380e141803060a00d900004400000c240101e946041d40030300d40500303a1044011405041d800340007181c101c4d0001d10034070b1401c18680e6480c20841d207101030403940380c0c0c2d45104101c0c05070110308500d0101c0030881d010704420300700210014568003600402074282f00e0004085410003804014007401403d015082d941555a20301700541359070001c0b5200896511040000340300c801901040390340c803076401040303a4280f000350140c014540e007022400305e040c002e14002c0c1c0144800103007a15400b0b090640d845503030b11080741e004e004801c86400c0e0482d550900b80020b201000c2c00200070341c2d6001c502076903022242c0040343e400310300cc0c100079031180006000305112080c0c074942940600f4465040c2850302410210040c0c0003210407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 508805593 1250 508804343 508804381
    0x9020306070c0c030b01031a061807050a090e040b04121b030806030f01060e07030b01020601050d06021318050f06030c010e150d05190e03040b0403060902011b0c0e 72
    0x5400540006125900460034010340343e000d20450112141c0307039034804201007000e8006039980c401241000610250011030182e0001301603c140002d43c0196030030211342d0300003a240000740b0401043e41c0d684030b8401e150050080643d01403c02c02402d140c10181c00c010b034151003d8503032181081c04050442c0c06101c0e610404102c91400006035016600c04403000c00c006070190364140500c400707000e46004c0074011000942911042110706061150000d8101c9051b6008c640c107541106c4010001d5a580c50102c00006411420140e81d412102c03009410010007030f003201a041c9480007801440c07081c5540b0240c42041700700609141c2d41c076001e082550f2441c1801c40c6900046041490942505011803c1c2d568800c03441a480d003000c040c003070f083d026100115050b112089010022456039007041c000c10195042031800741d4a401d003840c511081600c220300019152603118028401164420f200c102d4180c5440940070000c9003803071400048a410900c6000c0c0300c240c4080c0403e595251504886000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 508806843 1250 508805593 508805599
    0xf040603210c0b0c091c113102070f0203030c0105150a050609011809061d0a1e0e1501030803041203020a0c0f0507030503040602060901050a150519031b0302030708010902 75
    0x5030303560000441c903a60321440341c046e0007415015010000c208120303a03d20b207180c0305a00d110141316402081c000d0700780031021140020b0025904402c0071080264240300250307403c45026a8612060402511000c14003100179018800018098150001035000da03010f08696111340040001c84070800c000d035502401482e034441c0d01080042c030303a5030190388203503005060842402d01c000d0740c44460b0000c480703e55109010606101600f481d55500f4102c886034002c000e40b0007001340c0b68000d60b03007600d8000c2c10150708158540c0d40c42100425907007084511807091101c041c500d0030350385030701e031060b42030300300f511708690014030110f2840e182d5020340281c0c0c0c40310080e6a14426040c407540c444411076420b2050030703170701070244803000f1000c62001d02c001d00140c4640d80041c061401d000d5001070841344000c0282880f140382081c203203030000c03100807100d00700c0c0c004a90807004049001da5122150b01140d000401295400780308030450380380038503e801124001c074140c50b11103a88466150a84001c0d5100940c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 508808093 1250 508806843 508806863
    0x612020f06070201090b0c0f010f0501080d11100c0903050c090c0a03021c1107150b01022e052502010b0a0e04030c170403020918100b0f040603210c 65
    0x441070078400c0c050b0250500524107550015030700e6803083e002d07500c9917058080c0d0350042014126031400c00d0058031821801040e00f0040e6614180c0c441c2e0b26000b94803410010800d8210007980c5060040114952280520904100d600646000038005085920044401d40603800c060002c61900c1044e071072144100d580200d1903d000201c0071002036000c0c032000f4442091681d04084590300b41d201d840c1d070031180503030b407560b90b5078141c00c00720f5299060403100300320203041c07039103000075a40c0c0881c9480101c820205480141500060601c001c3c044d40f20359004081d1500003040803144900e1910001c2482c1802d14000d0842004030482c20307071b448441515040310315410204040144003000d40d51040c02458200d4070207a0740d0780c40300e100001203c10072440540c00f150500c15481c00c000c03143c0d005918000c21680000c8062401a107404d07030006245809544c4024010f850303200c20682c0c0c0d0305c0160040c0708000868980c546440d42e1a500520160000e0303420b20ba8200c280d004801044000c0c0d00324a42c94 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 508809343 1250 508808093 508808119
    0x20711010807020304080f030318030415030f0b030a030207030201140903030418091203150509190507030b0d080c010b040b011709120d0c021c0905011103070503030c0d061202 77
    0x145030400041c0c002c03011480304000004240005204144c28043d0f54000b40d83e40382400d60b240030305100180000c0c0150382042000b0841d480381001d03e00d140038001e090215002c8400d586e800300404588203002d801d805248031000405901180c4842900d100b42c071842c44c40d13408100b608806004d02d6421540562003000113210050540d1240c01c80c03182c1444008c50090150740c0d41107100d0b049140518042501d07405015124588501c01c2400381809481284441c5041c04e100d20100c83e6202945170203036500c5c00400e50451194100041d0400043c0111b101002280f0b0064180e41c4519880c2025518110009241d46800e024040031640140d5500d00b40d594901c0c0381c2100c525000d0202e506a2080740422850100090041d041c00740d14403138005022103189030080e040c4400220f1201000035840a03001c1d8803500040198296502841d2012130125201c03c010710794450264050031600c404000c11464032442c1c001882d11480c591802d020140d81e5001003812020748100c0294810000c8002e0307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 508810593 1250 508809343 508809347
    0x1214010f03031407120504080d0507021c050a0b01261902090a1e06291e0f07050a0302160503030d0b01030b0a0f091a1003111225020102071101 63
    0x22041c214028007229151108171364441c0220b0318403805150101c2c6000c5410021060180203d050a40c000c1c1403241c90b0004aa001840c641040790b501e403183c10040700d8240c00d0100402c92000c4155200d0036910440d612503207251081921481581200c003070720782012481210110342d14085400d0001950301101c169420000e601ca8014429426242d80b00c0100100300900316188201894000380082c02b24100303032010300e40440704512800d84646c1e00e01402d0b00402c80204480540c1011000300580f80400340c104101032082d4400144894008901342050001c003141c1c030303c40c2c0d9220303808032040032440704403441d0081014840d641d40745d00107201d155849544c0d41c00c14044c0c280c05140010301c40031b0800024131200708a4020f644000350501080c094402d00e403042c3c41ca01150b9841a080004050000900c82d030101a1200109034450944090383c411078020356010400d100010195841c0652903060300e600307103940240c00010490022444035006100b00d03064240c11034400307641c85c00f843c401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 508811843 1250 508810593 508810607
    0x2041e05030d2601031a15091501020a0501090803010509090a05100b0a0e0403080702010b01030e030f0717160c17030a03110c030f0c0d031b03090804030b04031214010f0303 76
    0x28070000699500744001003d4214140c80d020b1031140c40e14400c640785590300390080043c01000c0440d01100f00440343c0c481d59800d070401d68401d82c54000704c004224a40d0040741444508440107113258241121541003001c2503000d141610b600f0394400d040740d500c060041d50307144108540a4080e80080700e582e8140107260300005103d030f030b0141c080d0203181e81c4d80001346100c407000c880c26000110030000341320321198203014198080b00300b480c06002481b00120a903890b0b10a4800410600e1382c001545000c01400e0a07100d800032402010881c3c0303400c20f0120440e510300e004d4208485000d0001004990400c0342004181511000d10045043c1020f03488107400501c17100c451a0381e284030501031b00b01d04000c10401040035a00c81094aa1100d081c068042d241a0404100c082414108661318415407107421000340d45580074178000c0703402a1181012841c51040f500090480a14141044281504010030061138044904100304801804002188040080c02441c4081e039011b802000460311481c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 508812949 1106 508811843 508811867
    0x212030f07062d05090d0f0e1314040503040306060b03010f05100c1202010b012d0f0903020d210e0303040b1e120f09030307300c020102041e05030d 65
    0x40003604e07231840450b0700f601981d03410122511304000390b0040320303c42030781ea01081c20381e00b01810101c5d01e0340d00501042c1c85030381c00d01c0c400040c6030f42080101c1e412100c00c080041c501500345020003002201d00313141d000c100891207800201080449484141010717103500005821640c07400094101c0c50401d0100480d400780e01c02e240740c44a6507041c500c0c40796400b07140000c46503908600a90304640e1580010350080d0041013544c00700b0080320400228001c58584034910007a43d02c90480361807090007485501604140310810080e4040d402a10051460b40079041d110107285001c0205d580100d440030703600d0481d09003402080c0b002034110a82003400303200510700e0751409c282c020340310844050400480901d00e00d0640c401c500c3e03e92070700c0b0500b4240d010600c80504c101800034041d410078001d119248219160a40e8a617200324400c104842c03024000c0c00680814070030550315421290 = true := by decide +kernel

theorem cover : BRFrame.Cov 508633093 508812949 := by
  have h0 := BRFrame.cov_init 508633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 508633093 ≤ n) (h2 : n < 508812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
