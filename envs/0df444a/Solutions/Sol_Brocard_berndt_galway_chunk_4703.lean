-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4703
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:28:02.659502+00:00
-- url     : https://prove2.me/submissions/92074aff-e3ff-40d6-9891-1186f48e3efa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 845683453 ≤ n < 845863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 845684703 1250 845683453 845683463
    0xa050313080d0e0604050d061b050705010e071a0a0201200c010c17010b090d050312040309140105070b0406021614010609021201050405060a080d02010501050103052206020309010f18 80
    0x620b203801c40d1180504030502c0c0c034081c1070b1503c1c1500b000c00b0301017031140340700c4151035440d245c04c0c1100d000e6811112042591a15586640c0c480d5001d01e402400c0da2520000000036078406441449010040310300101d0030306039044019034550030f40d02c0070f07070140881e0030b008150140d0348004480280c2c4018010907181451a000308065100740a007070303840380600c0301102074405402d001030010340d96a00090094200c0142154011030f92990749501d103502110740000c00070300800a000401d0f80001c4500c000d424526a0a0b403031882d1100000e005000303e43c80a44000300d84404107051011a43c1194164054410341030030ba140c1d10b08007a00a4100c80b65809002d6280c0400025038601600c29240310f56540540003034207929003c00c000207446d0141c40941d0001d10810700040aa40802a40810b44071580000c03600750325200025089030720051201d4484030119000d245005203524003141016070004006840c2d4070b5100d982c0d40104021010b80308554a0079401506030100000e02c2c2c0c224611603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 845685953 1250 845684703 845684713
    0x19090605010909020c0d080711011a091008060415180507030b011403060a0b060f03010e0121030e040c1e090905060301063002060d02070507140604170a05031308 71
    0x103454190103c0c403c5e030102c00d03c1d5401600070341001e24450340c89213800c0151071400c0300b00484408a00c80c21122010402d83c84100000d440c4041c0e82864214194000c0e003e40f50501c4251131309001c00d89400000300000c0c030b066120310340111840841e0b401440c4294402c1841083c3d08020303e4507550b2090703940000d88645c1800e2000150050031020081c50502015010740004d80314124418050040043c040e07034090740900800b9a00f0407801c2c0514000c1c4003806600d01ca6506d003038007660100c2da2440f40030009015004070303c408a034202200002c890000c0e5000581d84102c01c00848028071801101c4411060b807017418a040e0703901c01105015510550003c01c41038403160105800ca540c1c510640300028500910312041010809400c60400c000d900c03412866180c3d030303001450a070300c81c040304a2103a82c0030860506012003009608041c0120000404003881d1040c0060042e008920031503a10b00418400103003035160a0103440300e07160748001182e45408498030742d100400e4650003451494491 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 845687203 1250 845685953 845685959
    0x50712050a0e09010f060c02151215010f0e0f0d050d030b12060609060603090c06270409021e030312070201051605040605030c0903010e07030818010e0a14190906050109 74
    0xc0410703032a0485e20136800441700c0c5850514191202d0110314416a88070400c40c41c107018a00300d400082c0950200d10f41c03c4a000e103000141011036440e1801418100300b0a500fa030200250819030382c119842044840b03109d54490000080d09400351080000d119004c0c40070341c0021550160007100074550300b1105020b41c601e6030303040700d07a86590413980d840d0b00408060124001e81032000086d030304108641d0540303102e0351807100820314275401543c001d044260742c28004018285142a000304208003100c007030151001e560005142201d4101604014281410764407c0ca50303003c108640e00c1d50400d071000d80282c600024068002c0c1811164072005c00214482040420b105d44110360980f20103443d0181142c03500c0118034160342040c070b11550950b580e11006522014104040802035101d0f2002d00c1e5200100d07402d8100301d1070104011818001513580345102640c0c0e541c0c2c8801a251202851039101440c14001000810350301d40c440c4c449040c90b0008070300400c681d00550140c510a886140704196 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 845688453 1250 845687203 845687209
    0x51309050f240f0c090102151501030c020c03100f060302030105040f0c0b07050d0c0c0b03040b091e150901290f060a0c020409081314130c120c050712050a0e 69
    0x4403c031100710061003d0400100080120809400040302c180f04840c002903007003051041d43c0b0310607290080205200d81070640c056a05014150711103080c0d01c0070f05145202280800d58802c1c41c007440010315a101d2115040030403c60344940006c5400400034005c9062a00703000540600e0402c060340e202410030008100c010070042140c4a007a809002800c261440c90002c550680312040125462580604000b0b2403e5405010314001c4e4050010304809060054086103400307056401c0003000990114070414100002c601c11002e08800b41e175003c01036440cac000080c0108082d050001202ca031782c3c40d002e0070201e00e480603444040e0742520202d03525941d410400c0024080c01403500d001858860b401001030515400c800c1d1050b02c19250340e400c040c007040b2580c082d01071070b0300030800a00307103072000724854500000494044c0307003108230800c17402c1000c0600416201d0581d0080011035200c0c2458104144198100c428040d0441008106488110301c0103015501c079900c290700054001880c424145 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 845689703 1250 845688453 845688523
    0x302090102031c090c180b0f0a0506030c0927010905012331150e010312050405061209010c08060307060f022b020d03020301080601051309050f 63
    0x14205070000c50030a46002c1040b0350074603400d00080c0e811030b141c04400000400546041c0c002c1c0c4000e1582c40d40900c0400281c4044485200702d02c3c1c400d50a000c030f00d003007a880302c004801c1914815074540e40d070b070343d40d80003411107500c030f10f461081c0c21a0558903400403142c802407001c050326109150460580c1d1f038526050007503802c00e00503040b40d00084442910510b1a24421010400b4081c00c0e000b0584503141c2174002a000114820b00c01d06d0840f68445045803151003441b1401c0e5014627210205810800c00a031042c0c0d050000400a01d010045400f00070301520559004100041c07800baa42d6a00d00046605a013083e10783c000550b0800c0c80020310303140100115446050041d0007000c80c546061401c4404044048500c0190b0051a8140b0320044540c443d100050141421456046402110003403030011352410002c20544148014040004045942411151b0407241d0051401224005400a20380b901c001055031141d58000c4031480000300d500004e0800d8203000c58940c122100083c0164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 845690953 1250 845689703 845689717
    0x1d04031e05030703090212070b030a0c170a050619090204030b0702030c0d030b0409140a030908060f01050f0f0904050105012102010207180b10091a040e0403081f0e06040c0302 77
    0x400c07000c0c000107034564401c1d44080314440c0010701c200341d4281c181e80050305021650300080e91070300b0000304104c4180000d01803190640c03900d107402c3c0d200d03807030781048040c1d070407000b5102c0d11041d900c07a00855555a038041e01250359001074446074880b207550740801d00c0203510500c0b00f140c5807000040090b200a00200030b807220390000501400320080e200400b01c00070500c08070083c0c1d0195440c40b101008c160b2551581105201c050f0084c50701009900340502500e00c07907072200440b40e110004128007852800400d50445030203a07110b03942030385814000362a004051510036013150111080005000301500700030b04036955030300303440e4180d8480700400b1007200000c070010380540e0000c0020840e040007101038407141c0602460014540582c07000103001544900e0308200003c2d03030000300b48980030412007509418102440003914182ca001d42c403e1007980001c1020b001c0c800ca41c00010b14a03240035103074600321889012a036103490744640700008120b400f6500640140e00c1d1400d1801090f003e0720071901c01c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 845692203 1250 845690953 845690957
    0x30f051302042c0a060605060301180c090e0411040b010531030210090f0b0702130c03141e01050307031a09150103110103050f06011d0303041d04031e 66
    0x11240e1602840301810407012000d64441c00c0c1049111114910007a04018001400152050a090342044400e94915030000340c4610340c10001002208203d04a004554030180d0010031400c2a185082d281068180c0c001a2040c2c440b0341044100040320400e000b1514003100c0411040d00c64000440c2c040c01003d40c04010006581c0d10700c0c4100c01e01c0b41968601c0320250101c4041c090f12039000c01d413159125110315000c42c1c4a804e0502c00d010326084100c01034008482c40c207007007001c80e4000410340f203121202d0601017581c400f0781d01401c9209421201041d00c40d25004505400c01d983c1100f10b401e8845124a00c0c50b07104c1d000070030649400315001c8100c030340201d08251501511a0709042286c1d025212100c14130540211202c1c05000c3c45025008502556107a00f40703001c200005020f0311402003072805501c1c0c91070708001140c0e800c6010300c5100ea07244140500004640000701e40780d40b15581004078012035000c03481100d4810442d9942c4514400c2e0345e02d65080155044c4845d0350350421641d240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 845693453 1250 845692203 845692231
    0x1e08040f0e070309170c0111040602010c020f01110f030402270a0c05030c3f010f06030b10050a05040b0d051512060c0d090b090d0207060e06040e0a0e0609030901030f05 74
    0x3800385d807100041c11702c01190b8800001c909a5004096507651300c158011070243c0d4448202605150b01032001c194400400da000b8800d401000800303940c03038032807400c00c11000840400070074150344802d18640719841030105241540440ca000c510340e01c080c02c4071001c02c0c141c00e00002c007503017520602c01e40780030b200303000d400301d0610801c0503003501c00912a5100342d4008030100442c6684005440c201a1260003981902c00c10754140f20040500c00e0307103034118405241c00c0c041006801d403908014030500e10040d19040b9101d182c442000c070345034481d6902070b40303e180b030110b451507510880f40c3c0840d01489c2a54000c0218503540c0e0140b000d04010043c4000080e080100040c1d07454034000014211444040000141c03041155505041880150764041290340301c4101061060303010000c01e0050032660170020f003500300c58030000d480c908c507034023600d8540146900800c41070103440e0040343c0340c407081d4001d0b03500614020550030340c0e94001c4112103000034184214007000711400c1c420580101c0d00d0b162803007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 845694703 1250 845693453 845693483
    0x190807020402090301181a07111c020309040c030506091302060d09080f07030201051027020f0f0406180f0f090903020c09010602071e0506071e08040f0e070309 70
    0x350480302c3c800e034140d502c0f0080c03c2650083d00c03808600c581d108141c0440801c043c401d13210440b00c0300030403034818420f110b84c03407402e000340019808a129001c00ca1141268401c0c100c12030550080e101503940242c10403440700e8120390141c02c0244210410b4400020560703452110744100e90850602a4006004102c0c401c900e0a0710703040300007040d0080c4201490400c0c1d000404007170790700c41c810503401030b590b407814091a40162401e040080800d00f00000322441c3c0c00e66590390500e1420032000400f075002a032010142050800d0340c8511294111042d203032075440f5000341c060050b00b02011201c0d0490b03c00851225806285501601e5801207000c001c01c3c00e0803c640000e0210500540540c400c4081da041141d643c01030080c0a0106d980c00b43c0b420030f160918441c03100060043c8a23240d0030624900740480d8079940151100d450f040b21b07151024503200e40c114030041942900c007800a0a001401042621520399040b08072820440c00301656612983c2c100c01300d880f0307600002d02120742001c1c50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 845695953 1250 845694703 845694709
    0xf120c190c030c1a010612050c0910110106150801090213060f0c050604060c1416110604182c0a1104111209070e09060610030f091419080702 62
    0x1684400780320742440c1d0103550700c070f890b11384509005040041c0316468120050002503808100300c841011010002d2110341095115500c00d0302031041c4140c020108030303080340c0f145071269010030307415030450008104031034650700005800b1401c04a00c4021421890001400c9400c43c0b080340c0c0c5900318011410038545c2843c0342114582030b45181002080402d240c10b00114000f401180e00881c4502d030300041400000e000a44910b041c030881c107400d50020f02c801d03800f1072043c0d24010100d0b6404079403080804002000184540540d070085030014025000a100c00c82841d800a101800182e000c101c50520f504003190400080c44001142900000c640c00300154481290040c1c1110060012034450840b0003d0a0345800c0030b400000d11600d41d005120f40013100f40700020213000400480354003890110001580e800e405071a1074000c1851515003e43c540c42540f00000c8852140d000340444052400c1003490a25480d00d030032042d0061a00314800c0c02140350b10103121551048009007005415020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 845697203 1250 845695953 845695967
    0x1b030302030304170904020d05060a0f0f1203021e010905070f060e1504080a0b0402040e0c10080a0b0a060804030228020d020a050616060c0f120914030f120c19 70
    0x72525604400d00c03901030b0a98503400900f48c0300400890016940c5080d200308452403005a000284160300c4800c1800754503000c03d250416182c0c2540550b840c84111701d000c03498055403400910304031001c6041880880410b401114440d4028400c89120710b807103e002ca02414500c1c42000c3c04030701c461900020714100516610710070060041c1c0182402da8901205060007003034481241c610b0305180c104001c601d0b103489941f0b180b009103030081400c50401000b0506240d180c200d0307007050000e07040c00110103074025002000400303800780188070090781d201d801421090341a182100035009400003030700411221039051128015400c0c84c540802e105800f80100120200c100343d03001440100c0208598903a140185181e03074885a4100f52800c2e5428002c00321000310404108104015a5440540d03a118044910503000c08800207404403491404100701da840404e00007550202040c03540590707403610094403200c1d04100d401c001c10350307075481c8200f018441c83c10101c40c04910700d140c004505c2d1061030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 845698453 1250 845697203 845697233
    0x30507020a0204110c1b063c0414010f0e010c05030d110418020c1b180a0f0b0d0b040803180708072c0a020901020304051c1b030302030304 61
    0x54442414442d000309040e510640c403040f420100010305004e1142080107039107480400400c0c0d601141d08200c0018101d1f06c6620000300054511235010241128104c2c4045d1190f48000803480d0600d01161840f40f082d000b61007215080341200340543c04550150101c00b1010710259640c030301c80c0c180c0000648041c40003000555a40c4018016500d00d00300078450007000703051240c400e82d116450070800711102040301040c2c40031a0300501000000a0000846100d1052108503c8072041540d101003280c0c03403ca5849298042e141d08103101440310303590300080d450640c20b10148181d180d082c0c14408002402030008012458500001c0c01040040c0007454000d40c010700c64403503240700c00d2041450040160803910694016000c10081d00c9030038201211242040c542480c50320342481e161a0b10fa4074000e25580e1680e4002420313068982c404c0c030803240079100003040e004e00c90700e05002d41d403140c101503041124070a14100c802d100e10001081e24100310380d8907500642c5580d40766a42da4604138480c607 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 845699703 1250 845698453 845698457
    0x70c0203070504020f0d240602031216110303040f02120c0307090203060303040824181b03030c070306050105100c051903171e070e0a05120c0d140606031c030507 71
    0x40300c0e540740d0741014064800014640906085130100511f542101150903600c1001950f000300310b040d800b04100c1205070b91209000e404030500c011070700401d6404c18411019880140000404c0000700440720f01d20500060080d6400c20b2990f4490700c480341c0d207404140d0901e9141c4e02103a8100445000c54008560029015003624181655042d0141c03500038020040342000319a205101d081611209005a00c920003d451100c0800e8500407203441d0382807040c2c1000060103491680401d600e0402c00c40d01c403070041d0011283d44594034101100100002e0040c0c034850142c0711441c0c40300d148030341819114150000041c1594210769540c50883c004480790481c148415800790b5141a41e042c076610f80b00c2d10725002c804500720030808032000c034200c00420203030a20101c41c1c2002e0381907d0f001c40700429a8029590842c038607040550f0145030102000b0a55404100844000200100945802d66044240007154a0f540b244002c0684030207020884925100f030000480c41101c8c401c0d0084c0307400203164 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 845700953 1250 845699703 845699707
    0x108030a2a0b181204080d0305040f030509031501060908010e01020901021f06150c05010c1119030e0301050108070302030d0801051819050c0c0c0105121620060103030305070c0203070504020f 84
    0x800d114500300041503601848550020408111840c000d00447c40108140c1c64204460f10f0543d481d500b00240068003d801c00c080480e105519031030410042200c11410746075115150b94074040204a02114040c5007225400c2100d03050700b5500500a03600b0611050700a00641d901d041442031000d041c2110ba0104641c503503c001a0082d0301440c03441c80045191b0396184c0300150b508203a825100304000040801c2a03050310500d80daa0003040e820740c0040300c1c000340710509182d42411070300b00504001660781946003034000035428000140c50380849209400740e82c0c0100206e01d080e200030b10248682500b00c0d546105010804011180b03a50b400b140b003501c84007c40c0c0e0711802243c129001299010546000001c0c003e104503010856984842001d290a0f0300e0a005803441401c078041c0903012036036407040101088900b500461130b004402d002c0b506801c44044810f10b100c0c1e03403104284015000329240c0404600300c03078410300054230440c1d0058014800c182c60441400000e500000700c000c140c1c0d0003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 845702203 1250 845700953 845700991
    0x3060b0a0614090d02011e020c09011e031e0b090a03090f060e010c03110318040b060f0d020c07080a060606120501122004060f030b0109180303050903120108030a2a0b 73
    0x800d001d287c06002c8964014071a040f0800305002703d420701a00b29541102c00d00352514502514600034405072030303004885140c01c1103c6608007038808040d03130004202d00e203034404100d4541030009410400c540030340d40c0d10045559138032494094401502a250004010381c0504900b540200609280207103c0e00d0711158428410007818119041401240e00d10a0510468106407826028101203110100d4901c0d1602c06400c031130901ea0300c29442800442c40c3c01251405c0c0d00c590030300100b4007e00d10700c0c0c00d8880ca030703100d45404130080c0107d000b1036020034100104a0a4400584a8030b4145d81ca01c0103010300e141401d49420b04041050b44080444080500c50500103481d1802071390300405c54603154090250851500c82440041608400d9280b8902a080c40d03801c0d076084200700f486505410300181584480c95418107610a0308032040800041c072000040a4000000402c46000c50341d0782d07011900d9800f440c01c0340100003034144a10700714200a145021075440c0245580142d100d800c4140c00e0b601c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 845703453 1250 845702203 845702237
    0x915030d08091014060f0105030601050724020f070b0a09120c060b04020c0f0f030702061207030b19031a0108030d0b010306210330020d0b040603060b0a0614090d0201 73
    0x213401e40c0952010100c0b1410312041d8102402c1c034040c60079090030f09905518001000030302c0c5000e24030001c8c004c1c400000c40780c9421035600c40150280035003204250741d070711200c1912081e0746e403147c0411142c0240704800115600c52904c2480c0403160f01c121881074060105400316030010084606450044d40c1d812056030361342d500e10007072582036420070161170341000c183c80083c1858416040c2250341d4000304400c900681d41c0a0445286601e6024140d0381500c902c2021001841c040e42e060390400c03c214002a0801c0542c00003004036881603800c100488108144024500b50a01c59140e11b80e00c1070020500c0007420303402c840826401894005012030f80d81c00c014102c10b81407400c001b85a2006c50350402031507400001401046900322207401c040d001d030184200e0030015403d0040c01540e020542c923040e5801030304400d9143c80002d00030310515459060020041000081c100c1c4038003803110300060058040c5080d2100704062403034541c14408c1c0c40e000d0007110a0b81441c12030400c81c0300502c0d00c010103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 845704703 1250 845703453 845703461
    0x18020a0f21060e18300f0a080a06140d02130902150d1407170403031416080a090201020303011a1204080a0905010908030306041104080304060503060915030d080910 72
    0x300d40542900c04074101010310210040280d15800031303940045000340300240c0b84030456410300a000e141c108482d50051440c0c2c07103d0088405004c034440000450089a90f445100d085c050f941c036440811620342d98030080d55407062540308503030300075401804075005441e00d160788141c4a116498003160102d01c82e07000810444000005202d82d00020902d02501c092a2040300d00e0320080f60362030388160030b20840140005038007180551604520000003800c040c400c0c1c00042142c44100b900030f0fa9800c00c1c6051183c680f00444005001445410010310300a80d02e0088a031540e806030059817441c0d09008021010895481d0740d40c03040307001003103110040410940810b105a000d8a001a120b5159500003400d245175544500d0411a03c9401803003088000710440e50440c000700c0b07000602100b0540d05000c0b038003803503004200390301011500141240c2c108000794411141229007a9031030390b4084401040c041800000c0e034240e4130168003007843c0b60065240c41e810015140c225403000b03141c1e0440300d0540d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 845705953 1250 845704703 845704709
    0x804020a0f03141606021915020d1b08011404050a1b090e01140901061b020a09020901030f0603170c150106030b030c010207141e09010f18020a0f2106 66
    0x4446103111861a500c091059104c02010540b10034207061421078000d5887c0000162841e024549075040300400c2044080d00d09040080c00d015921400b120344054014000c4001c0b8200a42c0d0000c20b1070209440360000714107a4940401249030007201509101c01440000c00e05001580c5e04c105403001d42e0a07207400f4500e85172140c0d4441602c030382826032201d004001030744041101c2d03284010840c50f030340c1c03401403207415036507945004448402c42596403c1d1643c00402d019400c05212580820051616002006001b40a80b0140b0240300f81d401e246003100d000340700246c890140e011180e580c0c9103000c0c1c014000d84482c5c1c000c8910101c8151032104888000f07900140c0070076070741c91031111039007028891115140c03c00d0015041441c5040e00c0752920a0b403400e101c80c402c00000d142a02e644540500c90b181d840009810504c99685803003850300c9a44290048104005507600c0c0350301c070003405000304c88108189540b15001d2810146d0143e07000c04080c0c5e5803403140410f5034084030b42c0040328807802c802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 845707203 1250 845705953 845705963
    0x903050c0604141006060e10170f1506030910150906090519150303260901050a050916150e030109060b040e2808040b0d09030914030d0804020a0f03 65
    0x200030540c40c2c5003481c09513812840c0100500340141040441e810503901244002c060310070840d004100c440459000c880c22610341540d100840500000e40503c0141c01e04c5500c04001a1181c0e02c0000e0402c400c9000844000d09103600c170741d04040c6417200070740101d076a80e907141040c0905192650b0504064811503041320074025996400c000801c00c0070040e80e0041c02010070b0400c038407443e4540740d030750400781404054140048012020180e4001a49102c1310700d4410740100990305004070154044e010035079032443c40c941810701054010380045909081034141d030b4501e442c410b15020031000600c07006403810090091054207042c007902d003802903e0f1241d108000c00100010104100011680445a02d13205588841c040100b407500c1001c0c8540c80d412504801e401209140c1350a00c000d01c03981e003100d52580d8000c42c0d424240702d100d80210b15018400d80302c2d4050b80b51036482201c400e00d1880c0394968554001b402d0403407101c5c0100c46041d0001d00141984042a44401d0500b425003459030040b22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 845708453 1250 845707203 845707223
    0xe19030f05011d010c0906090b1207090b0705030714120304060b0f061803070e0907060c0609060219020d03051017010b12100f0c0c080a0915080a0e0f0d030903050c0604 74
    0x14031a81e10039086e10140400303007840f1140c90b013425103480841c0584a0f4060211182c3c40200741d02c68010601840140944e581c03441d5140040e1510b42e80f82c0d00442011503080c500040040d4091501044400c80303000780312112411aa01c84d00d410b80a404500c4519400a0400c0d941c090b05440f920300810b100e8800700400c3c600c41590311305041ca400369650282c801c4102403014072442101c045a008111403180c5054101c0c00305504021000700190740004000c0c910000310541e0308462004001e20045032030b029108079200f20f0308140c044d140122413203c004000c4c3d501c140000040d0103c0d020890240c180006018054080410f0b8004480b144a40c107a42c010202c594500441d8003d0856001c1400340a1000000c2140041e100020440c401800c1e42d078085581200f0754451002140141b52510317480f40007940c030350400b0b07005007002d0ba824040103007420948082d40f01c0015003001a4030b81e40004042d05500410200c0080100d4681281001420808031000f40d01c208003480c000c902a0315600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 845709703 1250 845708453 845708471
    0x1403010905070e0d122709090c080c03210c060f10060e0d03030b01120f060929010e0604093b0c041a030d0e010e19030f05011d01 57
    0x602203003d00c1854510a40c030075900070000550f180c410b880043c1342400d02c04000c8809040c003040d20244003190040071040080001202400c0d41c2042048078010300c001540d0390303194103185864130b20400c030441e003640c00480c0b600107031241e40f1240708118004181050414419849580c20480142e80e1860718105e0300041c80205035810010380003d14050510300c40124181000c6090b0040c0204090181a501d000114559008034030b141d0606d8140b0300d04010500c07000f110300c0014055030049101e00c61800c2c0e003440b40c1c11040c0000e1130501001112520b10104100011a000240040d0320b942011082c071000802490324081d200381481c003041840301c076070982c101a91001d90702c0b038010203103003071144907030700c01010041580f81510b10103803030106115074518054ac009210003408217815104042c5240003855101141998034802661200c40c114031050030030a40341842c1a502030301e00f0a0030303010400603a100d00d640003410310600000c80e030140801420142450114011100780e5107a095034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 845710953 1250 845709703 845709707
    0x1e08040803070b10060509150f07020d0c0608100308030f040311010603050606091b0a0302130f18060e010518040525031205160f02030f10020418050c03040b07140301090507 76
    0x4040502006e182c1141042c1c010f0000848003c281a220062181c002900a28a000038003c44038029005814107030a5003092501e41c14484903481001c00040103400440c13001030848040c0003c981d0050340704c5046464125090a2040c4e002e00200d00b801550340d0040b40780b2400780a19401980200702819482c80d104003400700160000380f44a000c40544500441d07002d00b10000e56100003100c0c0342c0140c480000d0520070115140d260400c802d40c1c40c003c20300040755080000035004028140304140801d503640d402c0c501113182c0078054150700c42a10f41801d10700650384518598424006d0040300c1c00d160003214201c680700400c41078903031b00015a507001d0051041ea00200340c010011031400d5440c0091035810041e4901450100a00b005c5168000409540d010850a25418a16000d9078000c0701c1c07041d00a0002d601600c10b0145000c1007599840d00c159080c0b05951040e03691800c05441c41d0b03140d658a44000030010500d00500101400c1140c0929003003020b94082d20402038001114140f0102c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 845712203 1250 845710953 845710981
    0x705010b04020c0d110a15020903010c03060f05040c052208061003110d02040e1006050a05010509030c0d14010203071713020109061107090e0c0406050901031e08040803070b 76
    0x4500840c01000f0b010044540014110b840801505d003000f500c252990845e070601c00c10441c041c008078400100240300c0c0140c0d90042c800d0100450027005482c1c0400d10a805503480c0c1c0c07040d5121044000410003060420b83c000b074046500a00d05586890080e009003040b00a58854075600001c0d0044107200540c0200419a08402046410100b00303146135140ca11020629040074018580b250101085482c0d40c1c000c008a00c1900050b181d2413111000c088000304800d1081c98402c0d4070306400026a5400742d0101c51070104090060014031001d04103001c2460110b00c812a21038003440305c045007912080c40503601a03421991001c1c44070184c050803039141d1002501c03081c04003800a01050050f0f07002070303500d8110351040c2011644004844c40203800d01c0891707032003807095a0a0100b00d5100007000705140050702d0085904010850721101400a114402d0200a19401d000381003409480d41c140d0004001c81e2054540614168070360703445070f0454000c080102e810781000c2d01804451051080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 845713453 1250 845712203 845712221
    0xa080304081e1f0b130b0108180c100203120c030103031223070203220504150f18091a06090c1e130506190816091413060803070501 58
    0x1d501d411086094240d03070f40b1040024401030851122070f03032481596001c0e8021510b040c800400283c800d22011400002a00c0412620390009561000240400c400b8455500315800e02070b00820680c000307a828070080a20110002003948424400c4242c90503250200522035407109504075181e500d50318024081c0d03c440d24060540506100d050141d060b0703803010070110b01c04040070001d0662119001a41541310380110740c6986030322100044d8000300d5210400048070b401780c9003005403410020390180078004078001d8107080e20300c18900b0441080001482265185031460014200040b66540b92a0850540302c0d44503d0400300704102c0c5501e405000c00342d2081080103881e1601c3d03407201010706600b0542003140f40c42c64000c100c140b034071042849028058040900308541e03070848145c00708151032000210000042c11a00050382c2c0281c0114142d0741c10101e41c42c0c840c1101e0030818034950b0100030018403034118684800d0440703206403a0184000401c480c2e000385a0b0341c25941072182c2074a034491 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 845714703 1250 845713453 845713483
    0x91b0d0c09110a300f0e01050a02180a26032118060f07031e061d1803030a111c0c020d0306050607020f0607050109060f050106020c180a09020a08030408 67
    0x8605154908030740e80048889403084103000941740c0720703864582c00030840c0b070f004051950b2a0408012980c0001c0c3e000740280350b0ba230780d543c201c1c0d1030141080100c0f0740b0385030064904000c120000c000c1d601c803004c000b141081510310142c81c28480e10021601030005807c17000c0300544444401d000c00602c01ca03c1e50403400711040007820362441c0119100c0307200e020140642041503600c494a48805011907284119600b100000b031114699070b0020968a42400351b840707400c20001c4020403424231600080307441c10404032019501f503030788201e03883c8020035440e0307c204444001002914486540c180821000060030440044d541107400c20091070148001c1501d41403514001003030140f07a89003c1540c41321941200c410821541403404680d150050040041813503007030060250400520f500b101a074076040307100030081e580e641c4100b2a51980099440380d08a4031400040440c0c00423071280942c0302500100100d8222810b50108400380381c0766008210301e800105040c070000342c00788091254002c0c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 845715953 1250 845714703 845714747
    0x5011d090d050a18030c060e030304060c0b040807021f140412060c0215010b0702090703110315010905060c01021309152312010e0105091b0d0c09110a 66
    0x216000316612040000418184080819603104030340c81082124100301081118451a0f941d0780f50241e1801e50a000340d90100725140a09441410000182e8089a03580c0c1e82e030401480503615030b04008403005d802607074490010000b081c056203c040d5201c05d0924115081085e4000e444801030039800c0d074140c8019500302c20042003001c0c079200031303162903003d07000b40700017408180c000e030264034020411141da4030b001c00da0310002900c122050058032003a402911601015502d00300206e08440708120309081120302413001c1181a1000b004203946814181000c02d010b9840f280043c401e6013046000e840c203a900040c070b404440e0020030150f0700505440310103002518001d50300c2124070a0345e0190440902d50820702600000c440307000d0380301c81741d0f0280c85259401034812255020303001805503544a9820100030824030000043c1d201c00074002c801020120b00c200008000b50141c0e50503041d100c4142c03080b0f0200380c100451060706180d00c0790023034040c0c1d40c160102c0c000d0a00861602d40071181290 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 845717203 1250 845715953 845715961
    0xc05010b030708120c0a12090303320309010902030f0a02041b0203041e0b0a030e0f0a02130c020c0315012103090e06120a0302031314060d050714070605011d 69
    0x41c003c503802c8070489407035803180c0c1000c03092450306103401d50242400c200c420707294207442c0d000408d2070141c0380265030382600714100300d5400d100010103030410700d0050b40100100c05980d02d00805141c00841ca200046225943d41c2c0009150050700803410030342c0d412030800d60045192611a44800e089420031184000c0309074200a034480c01540700c1c5820040c8506503030030807002c2003140310001d80000c84039a501c075070281100900810410b50010b4042c45243d054100c07510000602c0800154001c1c90480640102c21400019142c540b07490015482100108091584e041c4220040d811010f50b20300c01640c0760040c103a0080c1130034080e03103416000700e840344408a64800c00b4a02614244c25810341d440c1c0b0f5840210305020700d80f01d101e9070680180d9031014101a808001403200e05800c0d8082a0141e455801e40c603544100b49100541c0b001c01000701d04404852a04107640c0034469003040c911041141035810280d50107840201c680a55030340040c46101c00200801c0018542031008040e10300d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 845718453 1250 845717203 845717219
    0x3051e070e070f0c060905100509150604150506030c180108090d1b0b130c0801020c03090f1507060603020103060b031603110c07181a030a0b250c05010b0307 69
    0x40050164820800100142c2c3c007201d005020045203d68011070030014500c00382845500c8070015800c500da66070500001c203207042c0c00014110b89140315500c03040c1864581d030301000300400080d010900036001080300001c003541c81502540c46240c29040da10f0380c0307000e4071207100e0707000c0c969503015030501c807a142c140701c2000000908940350300103a0501002ca01304030105002450221440104141e0660042020081100d0301c0303150503038440d0078070235650754482040300d00341d004000080c1445d600911034488103142074142e4002c502d01c0504a075490701c080b0384101005502c64041a82c0c000d807140402c00440d42d043c41020004d15900d000710317045052030403080c0104007103401c402042544623030003074500441c41c400701ea8840301814101d461103a92070701e0045031100f41415004040f45054150116005500301100080000802074850031103da6504962800041c0c8500748801442c0030715000b401c1c001420722140001ca803100703501400140b912909496a5042c4c050180e0007010f401c1240a07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 845719703 1250 845718453 845718479
    0xc0312040b03150d03030e0705090106232206080f0f0c0c0c09100314070501050f1e040905151831060905240a0e03090a03051e07 57
    0xd05219050703641ca46440480105036414550040d6000a10600d100c0c1010740540c0811034407082d000944548581d5a0304204411600342710314404240c04e900e500c003002002c074400d040f03c1540400c0e09810010f501600740c42440d0100303800048000c6203901400055040b40c2c0159005124100003185480c2c94000c007805070101a00c0042c2c0c10001080d0000188070174400b40d240900042c2c40b08100b8640a450300103860b1103807209485442c10107150500c100c8011800d03800f643c906071651480d040c000c03403005c2e00c2c59101440e4107480300300100355030180e10032000c000c100820041c0d1001c0743c80c0c02d04036010064014181003d078850301c030b180b40c44003681980140850340310054000c0f200780c542a819118070100d00070940350038000c500306201400c0007103550060070154050b43c1200d00d0722244020841402d07401d010480890f10706200010568009900f015024034400b4003668140342d00030001c18414203072074000b1551500881e680b02e040040b03409034000d401d80b04d4801403d1551808250389045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 845720953 1250 845719703 845719709
    0x210110414060706092402091f020a0503070c14010f0215090102070b01090e0f060709051903061d0d1b080d180c0302090c0702011b02012604050c031204 67
    0x3005081c010001c1540c0780b00c1980e80b0a07030415000e2080281c90f1500c449405422180d000e014040441c40d1600c6190600c00d450340040080c140e440144960803540c0d0184030100f1045085104106000001070030900140922510032555044000d0410480c0d101d503082c4851618104030304694842596940012602c01c44180c0d01e05100c0390b0345070720075500d001e440b0318980900f88090513000003a13a44403550103001140b050398150380c405214000095215441925207170005440d182081c401c034a80700038200c0ca0b010400d03103511800ca83e00d54850050f101d00d0348103071145101444900114050070311007050328040034540840d07810742203501310110380e00f10640504501000304a03650301142c00c5d800010440b000d0100d0012050007441d0071040b0401c24041207025203402c0010841c200c142c0010384034010f50507100da100d0401992220070788000310503030980c100402c810700b101405501400768003072991303004d446407a64501070074418034040d02410b00034003d501052000c01560504000c0c0c9090b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 845722203 1250 845720953 845720969
    0x7090c0807080414070303180e040803040b09070510051803030307020a110f03030c10200318010b28050a0b1c0e0610090e010501030b0726010f0602101104 68
    0x303071240c0c10002c820009004103d1064410389174040241600085205d13000b600b181d400c140d010f500c50019003103e0000f650002c0c0058010310118000860000d142075214a040080fa01810340c0c600004640b500303850101d801007800000c5a40000c03405070405050b0560580c0118030710700341f0701402907480c02c0c01080540301c80c1080114440594400010210064000741125114040c4240168850840003402c031007080c5041003958200040003140901c4540b694800360a5558440c0344492400481802c91200c1d5a589141c3d401983c4640b04441c00380c44006c80e9080b18407081003113010a200300d4001030300c203621041c01003005000f00011a466211006d450b02210300000320b156024046101402190340610340800c5518428198801e00701c5035515014002100c08111140c00c03140c082c00003804d03090381d090005082c54060300080248030030005582100149064050141c0368080e00940c1510107910410020140d0403c2400d00607404850b040140044000075003000740308074410301007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 845723453 1250 845722203 845722217
    0xa0b1206010f1d030c0303210112030c030e030a020a0e01060311030c03012c0405060a0b18010605131d0a0e1506130e030d06054209180907090c0807 65
    0x10f501d0b2414403281042d000c003e03003202e81703c2510a0480d0320b111501c001d1601e0300d9400c4800080d48941c054503207004640c05860307908c2c610b0302980b0119880c0c10008111901845030503002001600c0306078001008140030301c00c8035542e5040000c02030a03186128641b601c2001d081c014800e07882441c20803641112009a486807418104a603041019803402c0c900c441620f4505040000344040403406611aa41582c1d041252028803020002415003a054116201d58007000600480c1c0c082c1c4010001c42480700c409152443e5500818014803a100b091011144030ba101401944801c83c000d000d1503151074000342c00180301151a0116000e8001c0215125100c4e8006a10001d1034540c89402400201c0040c0ca648040c031001c0000504402c0c1301c0c20380504095840100000038410404210010700110010485c6001c03484407043c0800d0100c3d02d21380f00e400c201707110680e40c40c2521800203800f10312440c4910304e450160a030802c3c1d826480039074180d0400b44802d014550085040360b2210060410308 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 845724703 1250 845723453 845723507
    0x6030804051009080d03052205061501052b0b012a020f0603090a031e20190b0118050606070f0c0306060f050301112a0c0a0b1206010f 59
    0x481c520f031541d00580040c054424101c3d01168150001c910450940000d8480703038400e1542551860341c1004040c01d20b0300048003113810b003090820000b4055005140a5050014002d15140340d00e5021000044181d1703000c40e070601c1c5c2105405048000c030320900b0034440125800d03081ca9016414820b980a182114460b03900456441408440340c1610140ca05038491034050502c0d80e68400c40c40003076003c04d9404000700983c8000c0148040d40f2200c9540d1a400c209041840208c03d4031036165080d020b008420f541d080c08031951010400180c007401c03040b2559450540e50205c0e045040141c04003131414102003001c2ca880f00313011281c0f616405014000e6400c1c3c4d0f424020356401c0341750001420300e806c002002070652860b503000016540120003c01580049480d841d01314498103000074100f8a00c030740c606001f01c0501c10140480c088a1040d1844000c80b800000c1c00c469540c1c2140c001040c1c0400e19020b100d00d220009a4040401e0810300d61407420400003800102d0060b18040c403400c0b94044130 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 845725953 1250 845724703 845724707
    0x3050307080d02040f141f020714060d0c02010b010909020405010c0f031e02060a0e150c0304020a09020f030414010e10050c0f1801030c080403140d060e1003020901060201060308040510 81
    0x4800038040c1707800c0c4481094071200101000100110702c1c82c403440c4540c082d00110514202907036211809500200b14540c507200803e6402c0011000d000d80c412014084044100300034000e00140720b4555000107800b40c001400900003404641000e04014410b00003407105903000b8240c07110f03540c0c006030010350701c507a00d15048500c2c0c021a03c0c40314403041d0500d208108160000b82c0140110300201c82401203441c0718403160754505401d00e008089904101c0403e00380c0d030b90100119009030020306003078480e035150341540041e80d114a5403d114900e00008010500101c903030a00c0524101c00024440101c10480c00ca40c0c48229801020016595402186001c001d4a0032204411401e031102510382c0f50442c12000513864481034140840e0408101000036032040d4000781c07080c3c1d45526415030010566504440341d400105142140c150360740008610400c3c29928117201d1814006440138042c00c610500c0f80b01001a03011b0010740e03052100500002e44841d045d10f050b5a815203106040c2d880c2d201d0b003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 845727203 1250 845725953 845725957
    0xa030e0a050d06060e060d0b01090c1b050c010e0612060907120f02033702070305090405010b07050d03020a120e100617010c050412080d15090c09080703050307080d02 73
    0x40268003410b110100400c00825411a0b021200401c081c14403603078500007170010601c044a001469142d0940040c00030301019445100741d246203240491520b001d8613061107009007070000541307540d032010303500811941c0d02020b9049800015180c207070a00300c1000440f027500c00050081803107034002000295030103201c1e030340903d03c2000011003400b0310325107188900003d500544104540e0400d514009070382001200300038200400100b000a0502440d0024070000d4101541c200e0410504015907036980c2d17594021680039100160040780d565100d890311500c2d00c4810300c0514189801845160000e0390410004090400240c50100308101c4050307136182001c041203100d0380c003d0718100d0081141d40000054461001d5540001c01424409603001e540c0c0d4000d51040105405c0b06201c1c440019400b14007070a50603100950200c0c0042c00072001c1003484101d0b13003040d105640c3c1e0300140184103a10441c65802420900060b0406505540f00c0b5a244d2183c0f91025042d4500040e080603d030f511581 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 845728453 1250 845727203 845727209
    0x20907030e0c060415080612280b2502011b0f02120309010b01090605121503150103030e030c09010b0301170f0703050c0f06030f01180605090a060602011b020a030e0a 73
    0x110f00b55403540c44282e908202c0385c01100c54000140d00c0c100160150900340300d0703184140c1009005024614540084180308140c034000c03c1800059041c0020000b04851142401208070002443c0d000f00041c12000e58812144a61421681015a01840740d0354902401000b841c651511040351806e4680907841c01e120030902d00f4154900008100d42c2c5003065000000c01c03007090f43e60b26000e0780d680e80d044807240110ba42c0b4030094511500401c0340d071020b59000d102100809020f40e208110041c0b0000c00c0c940c0c3c243c0c82900070130103040c11301d42249010321410590402c01c0b56800d48650401610301800d010500a18180940e0101c0020000e101013080303001103c800400c6070090b946902c0c005403104000b00d95203008400240c180035013482c042055078400c842002c1844882e03841d0090020034070301c1e01d102d540c40c400e0b0f60b1240811962a50303c410386c0710305c040040200b40f00e89084030084c03c44190303c00c2241800254202c4411042e40400c1410701250540740600588040d00001482900039038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 845729703 1250 845728453 845728459
    0x1804050615030f01170a1a101517100e1506130612050a18020d02041e0504051002031b0901030b1002010911010e0303250f05060f0c07020907030e0c 65
    0x8000c0003d0b40140c181e0781816950700b8800c8102030780b00a08800c0e651803501000400c2c40320080b502010001c110f50710a40c5c004081841903641030307070744e82880b91000010140c4800190a40c1e49403042445107000e0f0390f80181020041041052174042d03d029141000340140390021a5540156813607035801d0186d40e401880c440a42d100c541e510040642405011480c1e0b9149900300000100710703000c6440303103210041c050500070f002e0070016420800300a03061101241e00680d606078a079061840400000e000d0040f441c07002a441c100f500700b581c940b403002084040b1250040040058100c0d03094541507400040014154682c03c400f0010380c0985132441c1c89640110354004000b0401c1c1e415027195040a001d0071007040100101d1004540c03a001d92a11b10380c140e4810020401c12a080c100b0310f030100c201381004004005400d94070002d07a1a513a80e400e44441e0702c8402400481c0800e941c14a412a81c0490350502c4c203800c55010414500f4000e00d41c87c181a51160a04032418041c04000c02c404002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 845730953 1250 845729703 845729707
    0xf0d0c1a012702091c06110d090203070b04151d060d02030a152103030e100b10090311040e0c090403050c0f060408040911070c12020103111804050615 66
    0x38036903a5240c1500c2c907a904186040c14118010820010310864503540005803001402e40c101e4021407038548060101220080d0f5586401c800310311101015040e000d1030300c900403403201d146004141c0f0b0b0811a420040e41c1e140c040104200300c512440100007440740605003180d54441c01c403940088200c9446021750010000980590034035203175401103100b209594820003030711221020f441c900c0c40c0c2c240102e404082111000152019032108601e61441c481c1c5004181200a5100f541c14008030744035602d00280c0300c0e0907001d032030f20704001405000341e20340c40c0140b03503645140c45002682c03007001005402644d9a130388206030340d8418009111b10b11009041300c5160f0405190042c0107612840c0c03000203d0140c08540c0103c0702003c540d9500850f084000b05081a0500e80103800406210145c3c4031344440802840d030014dc10024540b004000840c050704031009070340009020b490f60b2006030f410220081210f90f140305451805825040b5050300c001500b6a900d2020810300326818000343d02c10500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 845732203 1250 845730953 845730959
    0x50d0507020c010908010506010f0305060d0f120305010b1c0b01050c0d110105060402041211040605030f1006171e010f0207080408010b19090c17010608070806030f0d0c1a01 76
    0x354a4103102e803c0e41c44840d507583e103030042e80c220390007510240e001410f803840d99020103219811150b0006001000c560a0460a0313484c1d4902d146107440c11240e4010000402c003095130180300e2940103201e840d800700d281940c010314115040030044140350425030b50300070103601c6910900540d45108a00c808940302c4103005e070805030612111140605582d824140000e030315061500980341250403200800b1700444156442e003003603510307801c01d40341c20966425001805a8040041800303128420f409094080d5000700d01c102510340c150000b4030508100b5040f284076042c006002c0c4408064222050300c500d964810150141c040154085c1f0346034000f280c0c3c882400344c2e45000b8000c4400080003000030b0031682e000c3c01522040520a001c1260b17141804101400071a000440003020500e020340400408001e01e0381204c400382c01072000107003800d0800180d290803074201c0e80c11090850050088003213200c4065618580005100304100c4040d200c541088200211207a1010f0840000400d56071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 845733453 1250 845732203 845732207
    0xc112421010e09010e010e070b09062104050d0e130c0e0a1805060a0605070f15090605091b031f18030c05163005010f061707081507050d0507 62
    0x14191071000702c41d441c117000000303c035105104040c3c007000140301600c0000e01d8407402d40b4050b00160002c54021030104103401c42a40d00200f0031842c004000e607040c6140c10704d41805403500400d60507031428040d07014044100d5950ba0181c100c65032845403404a859028584100e0f5160038007541c00382c03c087c22640c0400d801001114041c000f001400080040b50303244410040503111500c00c00d0040b44007001030001040440a84070b010b280a43c003072012000700041004111100e0704000c0d500707103544100703124808109007c5408400008541e1541d020320a400094440251700720034898200b9201c08858038503c0341e0065500f1148000000c03400c20340e20f0501030b00d00b6801040880e840c0c0a4198000c1141569102034030170348141d01000303c0720b54441d00580c28010885080b91041c16024804440001e070240640200d0700303103c16001c5040d44c80c01c1d0052840740c00c10104034455420800c2d007031144040002e080304c002490807039a90300a40f0b441d8020f8440d80f183c0110800c145007804208030000e0f03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 845734703 1250 845733453 845733479
    0xc1808071706060d02010f020a050307080405090c0c0c010e2b12050316080c12090f0613030516020f0a0602031e04141e0d030c11242101 60
    0x1c0d1200c03100d07021034203516903620785a0b941225119400b2030103000c29805548660103e800443d028012a1001c0541c0e48500789540c0001b002121007400000f0148402c0c21f104010a82154465884c07900b820403881c2e042c1d403100440c0c04000d04003c07030004503083d19500e02c4000700640600350701d00340b00300e14602c2c42d1002c21150b40b141078404425850001c0302da1032081045a10610340d150441903820399540301216119000341c036000e83c810041c4145940a80da01c0c98650052806034010607101c91310b00002410020014045610a0f5051000201180d041001c4421083c101504c203407284404e48002042e0329605a84150004281c032000700740140c00000030500040d5800c104039141c5411030034502c2a00c101c1c01020901d40421643c1c1140307090584403d0340211b8445808000c0610b0740000c00d5442c8070b000d005500045040105409101603184064a425000c1d00c001140701003072140c405111800100180d549003001035200e03120840341c5a005170382c030721540115106503902d5a1019100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 845735953 1250 845734703 845734709
    0x61719110702030d21050702100203010602030a32070503040801110414030a030c35040603050f16080c07020d0309031e0b0106050a02010f0e01061d06010507060c180807 74
    0x3a1140007514030000d070242940890100703100420350645c45440404070302404010384114154460b841d402e010441c508d00285001c0e00581e4019600c40e9041c2d03500400c149021003500c0c498003c0c070304840401007000031501079a070540c900b4440d5202c1085c5080c600c1c5100b5a80108519468640b00c64100a8508001d000f00e45030841d00b030080e9944d80007015264480700000801241004031900c0c0043c82c0c52140460b000804013507400d40c0e040314070035400401803409400b010b02c1e8001030140b105903018418903800c0501d420040e00c0a103420501c0b182c01c40c06003941602802060300c0095008003800303044503030065001e400c8102c4904107240107015200e550000315155001d060640c28a04d0740d000d65240d90b02e0300460321150036480c10100b621503501200b010700440d501c0e1082c00052160394009c620b50204207000024443d46081c0708040074040c80412203190f00b4108043c400d403603900c02c082e1009260480710000c1e40c11444101035844162030b075152140d050242c04009411031020501d0401c0f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 845737203 1250 845735953 845735959
    0x1503150617060105060a0e1c03110d02030f04031b1208181e040506030a0c080f01050711070605090103090609031e05071a0601020f100e0d0504061719110702 69
    0x1e5128044106468031400d00442d904410280300d05404644030700c0884d0700d0300c400a4203660100403599030175240312500c1003041c0e021400c2c241045214078000c2000300c805612910245007000860312291204e44110300c0060401c040d81c070181030740c1580418110340240b0b9a296010b03002c3c04141b52481d1180c0112000f403500750070240c1c02240c1030070440c8602000c031480c0898801d4111800040100034200545015054400d1a80307100001d6040c01c044800740070b001c2c00801101c281328002c0b0f82034410090894042250b0140300720100200011090162103d50a040d074a0b0b040c5900100c0080c044540c01070a5582400c54500074541c12042800003090a0f20380705d50059441032044e81d05d407041440041c450b0348e0f0b240d08000381d0810481000d400107014810b8400c5144450102d5260400d407119204a00381d6500b008146a84c0401155580d40702e0740c2803090070946400c0c00604655160034108040c087c010000a096141080b6800800760f0503080801c00a4003a4030560365680040c401240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 845738453 1250 845737203 845737229
    0x1308010e0615060d2c0c1e0604060e030109150c090603020c0c041a040516090f181a0603010b09010806091302060f19120c140d15031506 60
    0x21000866400d0402e0814024003080d140c4101e0521010003010850b00f00b00711700070880b031440302814a031414481199206401002032841d840d00700039966440003c6c0d00c200244003024268540c480310305a500301d8815082c04800e039510b01c000300340908440310000b00203044440a0780e040300384a502100c0800c400343d488501c030f43d1b141c40040d0101e00c42c22208442c0e07a803040781d602100b8949a00043c0501903030b081c9804a0410100100d402c2e680161202e0000308901c1806449095000e6a404020301d110b4105410003468002c42d005000c4003444009450743e10b90703c030300b180044040c46100710140c01410b42603882d81c0d504c0c1e010030741d90400c18a1314001410f103030114011b031030007400f0a03000700142e0031411880c0b440c81e420000f00754012103406a40090a01c05e00d9110703180c00a03030340103824864548242b00f0345800d0140d41150400c1302c690092010910442000616003020f51310200e0342c905001814401084640104c07610544c00200000c41541d1010041525074100b18111206444000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 845739703 1250 845738453 845738461
    0x90d03090c1202150c030318012c150408040f0501050903100917130302010e0607030806010e1315090c0f0c02090a020c010c17100803070609081308010e06 68
    0x102a22032144000c1c010401508081c00050304200c10090b44074070041c400740542488030b5041580c0e40000460301c1041d04040100440e04412842c0041c454001704020040107007214203210b070240a001400c800680c901c012a07008280c01c1200c7e06c02080403500c01074076451b043c500400740354000c1c064240e40350302d0a50b000515500481c26101d0031b600050140c0841c00c1003800c1c260080c41207400030354a03072103071005100c0380d1124600240081910b22021033204c0e821400090a8049261006409098100070007004640d01000d04e0b50000d4092811003009a5080000340340c0b00826072282c8902854110002450b07017411000c501166207468060203100318600069496034a00c01c010300100e103070064404c0048c0b4209503d075030302c1032000038010306048190300010300b101d060341d41c1d10010808840e81c010300c40011002155010603000352082c1e006003811002c40c0c49000d0444014055034440c000b10080000f10740a44160000d08681c003c1107039500c90b000e60207018020b40f41001401130401117 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 845740953 1250 845739703 845739707
    0x60302030d0c0b1602160e0411010521060f0a0e011404060e1f120602070c0e0601020a0314070b04080d0f05070806011803150f11040312181508090d 65
    0x61002c00b40c0040da012500c0d035800031070003034804041c20408114000c6506c0130440d01500e040d054007401200d00401c509150070710300360310108400e4203454140710090212907030440c46800a1800181c500c40d8149142c0c071404040b5a100c03414840d40707503100303000c1304010402c001143c0f0111f04030740000f01150544180d003800d010449815003e0b9690200442c0001b03040744004000c40c000d1009040400007078540c0c0d0f01c0c0340c12003441400780215082a000520b84080c80741c484100c001501070002c6580e000d0403e180041e566006c00180201407000d00b240809040303c0340d070700780d5481a402213072107825803910749001111030b1300900300e100c100c070314100080580f52390520403544100615218200d09886100c0103545617100380340e003140f20345040440800040d82509104140c488101350100320805c0c5180c005055900000000c3d8110800b48403c0010801e0305034681c10b01d010508201071114182500b00760310720500c2c6c1025003081c00010703806500540c008406841220880b00395403c941c0d4141c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 845742203 1250 845740953 845740967
    0x120504020901030b04170703050a180b0d0b04090f121218170c010f0204090b0f0d02090c190c0b060d050a03030e150a09020a15080c070c03080d060302030d 68
    0x8040d4112104030014000106075543c4140c1003800ba030441004201c1d42c102004046c0c0c007141007200040e00109800481e41e40180740800300100e00258480c1182c20031b0058002c9008185c04600b07800d445803410245a11658070000d58680c002e270340340100c6501820010030005c60440507a0000f03540c201c06103400f034242d00c01c82200d11480852038141910a1300c60030070084100403034003404101000118103d030802d116a000d200c0b10200c0260311a031400e00c0c104121100c60b0815401384480342d400000caa83c03040401203c10b80c4c120341c08040c13a190b50300c2641090043d00400c5503826030640015440030741002c26110f4040c4250b64990703566482c1401c1c041e29840744940100f030303503210408040010307020317400c1201e042e1448002c40d406440d442220030b207104002c1e1480c0401c9641c83c0389001c2582458402400a410480030001010070000d41c01044024000c00d4004204030100b2040c0400806040480042d074000c0c0d903903034880d1300090044009042034403049120b40303d0201d428080900581c1f03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 845743453 1250 845742203 845742211
    0x2070b1206060306040e01090b0907050d03021515090709030c051503061003020918040c15050a050703090504050c0d0f0c05070f11121f1505011d041b1205 68
    0x998100c00e512180c0c01c0c0a000d420203080f20394043e031a42c980100302c00c424030a41d2030b0240504000742d0a03041101d4014280300041d08030741e00414507901c203c00401e40001c0ca081800c0781c1140340e9032850361200e40d0079a610030100c004d40e0303100c0582414071000d81c1d40140500c050328001c01040c80392940d80c40800c9090516910b0144480c1000d100207203491900711510ba02072201170a0162400d41030748001904060400034010844840c00c0621040c03150801d105400b0b04960030019401191440e4007810a005101c801c10401c9400903d079401c241c80390300c02200901c0c0181081c440c9040c405000122900500960341c0880d00e041e5101e0410b50f814000c0c070300c0398007558985c2841e05680b0744402614821201003502c91507034554060004e0f03101d22145c10f6080718030601808a40121441c613401c008400500510210f046c2244180d812445100900403a0000d013040180200200c0c241c3c20030210403406154480d1800c1c0341d03400b90302200610400414101d035a080007014032034a40c0001c40d0301c2a2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 845744703 1250 845743453 845743477
    0x1002070c0b0a2007060201180c15050d0f09030f020607050f0903070302100309051b0306070f110607020f2404240c09090b24180301091202070b 63
    0x2031020000180084000e002d22a254a00040804440b400006040904802c1d0028981c07240608004031030303080c81459000c08001480e07002c0c10003280c44003c0078a134503004807261003a16464003d6000e01030700844a102c40052418000c4040d4000d60200a14102e0b070180c0c0842c0c2d10710900009248045451440740640c0d444075402d01c0c00524480f400c64000c0d680064140c8144840480940d840d1440311341d09410b503139008210f0b80c0b03841c42d00350700b030481000e010001e004000c0d030201c803581e8001c21345a42c080e0044c80c0480111440840c220b4940311504284103c0d40140c0f018002103d5012400042e101c5070001180c8540ca810050414940c50200601c08075080290206002411307090100e0030b0380c0e11510f890412004031040102c12964512101c1000c030308041d004000042050155886e110320450302e86000c0400c100d840c0b043e00030038400e442e9002000103a600020224030000e02003207800500200311f002091701c2c005080809014411015109500c00010494002c204981d609035201c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 845745953 1250 845744703 845744723
    0xb0c070b0711010905030705071703040f06211e05010602030406020307062a080f011a0313020a1d010306060503010c021b03010f0f0912110c220c020708100207 70
    0x301d00868807081d20710840c503200e5407030713004007400306078100003070b104440c003550190000728a4601c01d808404520b1049034142d4006000801c9108a13441010048070083d043c007290201c4403c3c1c001c1c0301c0c0400c00c0c5d240300244c0e00c0c0503075420031000d521014810045a00004124998803884d007a607990040313101d4000184d01c200308040010304950000d5038680c1c0302d064102c0c0501c9030f0038110b03030302d034803040b0110303c0001c00b07034010043c01086a0180d0303401095400405491800880d4403103043d40301c010701c11655070f00340040341c07001c40d02c030750200f03100600340c4c0c802038401401a04a02c03c00b1200c203100a440741410004041210b00d018803901440d281545c0050003d03000900450350050000d0075419850755950a00c440194032600030f00e5913500704454005034220941c034000c050384a02400c040708100380c1145940410400007964420301a080b1a0f00ba190301011240451440481200080c4903062450441406400080c0c202c1030300c50360410f640c690884d2072a480e04030301416002501074540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 845747203 1250 845745953 845745961
    0x2106030b1509091908040905070f02010f02030705030c071401021801030b190e10080607090303120c080a020c0a021503010602120a08070e04020d060b030a0c0e06250501060e040b0c070b 81
    0x9042000d21345807040b56000e0030583c0d2410008112081200c801d80441c000741d504032031282c0d0a00c903040c2045e28603c030031415800d003035600400c0340c00020955204942e0004105051010b98020844035081020096640c1c0c50745102112180d082807681c140480d08080c00794150340303070150b480000c4402c0b001400c3d07001454243c9013892100c014001c800303142344100002c01c0c0b0400a020040c41441d4030f03296940881d14610700200543c2c0c2c01c04403486031a181a849d0542a0342c010340d01c84d0072015450016032241c1d01c0c241c4080c2400c4000d0b200070b6010000640307096a51513100083e504841898082e5105229403500003400361058401034000514034000040b1558002d0641302c02d00c500280006082c650040d120354100c1f122174110810701c0002008120b0001003078000c0310b1a072010780c0390186020440001103002ca000c1c2d00c0001045140311610940a08090484414010342003c000d0203001d9882200e00c00c0c0000c151400e541e52012000003c02e42c50004007240c0c8803a601080c941000d81d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 845748453 1250 845747203 845747233
    0x5041d0a1112070605040317120103020609011404030b01081203010806040209130f030819090804030b1e150f0409080306040e120703090e011d072106030b150909 71
    0x1e0107002160740200300c0c400a54200000300071902c081c160a484550340c4604505209240240b840203c020f803010403c50410b00c0ea04078003040d41102d0303064036400e48501000c00140d070704002e030846401543c480403d00005000048480d94100d130f00d110103540141e4625a29210361380300034018005079502640c041001400c00c9210a80c1c000b40c004070009550000c1d540e0180d05c10701c20003040e800189180140700e04148440411a405a10b00e4000c11030f84686590701c441d2030150b8440540611440030006487c0044281c4207001085070600907041840c101030b12040040c02ca20000340290245d60041e2044d0410380304144080e90428040d13421940c65004000190522590030a003a0054002121101e0180c9000d004814401c0c0c484490603030401c41130051042050344000303000303e001c407019030300b11110101e40f94000800d80303410707880070000760320340c03403030000c10703c4050510a00c0d002c1c000051182a14a403809004081c5440c80c03039035070790b00c200002c1c0c090583c0c004409410501e800c902170341e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 845749703 1250 845748453 845748473
    0xd0f062c070e2103070312050105010e04110903030703120b18043201020703020f0613033501060e0415060507030c0203010903030902210c040515040603030905041d0a 73
    0x10000c00040c1d49400c0140e9244203c0d40c44102c6124940c408180c420800d600021009140340305203108210640c03600d00020100b00c04481124025a0348501c9001d400c0c0f01c4108841c03402d440541182d5440b060384c50018801041102c0140019240c180d090400d454402c101100c890071620140c00744e40c90301d483e400c01c1c0941c1c05801000d085031030078074110381c170380210840160000031400050300c0700720f6800d02034100401a810b010190708144104000440314400d00c084460301440c0081140041041608a4031405c107808c1320600755600c0e9030601c0320080c0003100d041c4e0300c3d00e0b03880303440e640160424002aa40c01c00709222050710300d00c4040c41040c0c42000502201402458440342c078017610b4001ca42140e502003010b03000030b40c58507110300a50921020000c098911076038120351340c1c0d004018060b16540c42600c41c0703110701c0c1c075a070210b50503002500321250070780d000034070030029148c0e2031801901d00740f01485428004ea0500e50802418403040381228980080500a490880313082e548601c082 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 845750953 1250 845749703 845749727
    0xc0306010603020c240a0f230417030a27051e0a080c10050106021644010b270a090803010807060e0603091e01020d0f062c07 55
    0x1520070942d2017a03a501110104062407a0029203404540c10000301760015145c1000c281c1d00c0007400d1070208040b0041e00d81e8264202c2c68003081c440440d44503403800b14190260055403c0b0703005008824490102115404603218034800f070424814220003691409100d0003042000e80181c02080810382421620b6180620f10110300301500e004001680e21a105500411144412540822000e0b00400c2d101d01c191405041580020440c4408000d0b004001118601800c90901c4c0481101c4c103011014591600110045840c1600784460740c000f4001c4c0c14892018420380c9600b4074000072454104a6501d044000415111002c1203500fa8085450340c5009402070605980d6054540045130319000914064080b12015190301c0345012002040210042c2c40c0e07611641c0d0400600001c0100010700003410106020207280060b002c15803640240240194444110305007a40307603c441046600a8040d81d403000e49032551520200901a400030000c200300704005c0c03c18000c035107610301401201c0c3d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 845752203 1250 845750953 845750977
    0x120302100f020c0a030207080f03030f2a0703020303040b15011713080c03030a050106051204061a13060e0c040e0117070504060f09180510020a1205010303020309120c030601060302 79
    0xd441c040c0f5041c1441c2c002026030075401600100000e02203403406202c00e02d030781b203075410045080d801d21444000750341d04080c0154940e100380750380c440c11071300018101c882c2031a80807003029110302c62402c002e0344951040300c0440b0142d00380800144c1000150359104440001130307507a040f00d015044103d07950840060011310007500200b444c400066211001084c0203c0454003030358880c1000010401030f204103030444010300405010720024217041c840d04c10351043e0041004907405c030310002920401e40340a02d4107a08411030101440300da04c1c65400440440d070444054034404c0d9100d181c000541c1c01307540544607d03041c180004111100412039031242d00c0e1a181d0960b030006030369000103000c4030074940c401d044107220082c0c00c0088520310703c504108000020301c1040319102d10b594a030307190f0aa134200b5102095003c10007030621841100140041500c4c1c0d002000196140d0501039075030b40000c824188281e9841c800302203481400b0541c03c2894001800610141c2d08012041d40039400884512203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 845753453 1250 845752203 845752207
    0x30a11070503070803071209081c05070b01090c0207050d0b0a09020a09090c0501090b0c070315020c06040f02280605030a111201030320061902070b010603050a06120302100f02 77
    0x40c841e070b010711000005051000c001d5a031104c907032900e000c01d824039414050a0002c1d4010802c02050041031019442d038414040600c1411446c8040e1044e00444074041d020080f2a000481d41d80308950000042c007800383c00715440155544d0030080c1551100800074107485080000c02c580c517045402540c02ca510040032040f02c00e4440c1d680300704440301c0102c1a1680c0d07001c40410032165812402c4180a004810038407450101102003159856000c1d1100078a900301c2585102a150034642c19a804003010b20140e410a0400b0304011340144032140080c1e10a04a0132055030030484c4114250100c0c41d49030b9102d01c2014500201612181c0000340740078041900c51085442d2005428020aa640c840034041030455046040c001e0003040d0441d01b00f440d03049408a03a40c9803034000150a41d21521000da80b07561008004a800043c0c06400301c0102440813480020075200c1d0542c00052003189000820003029956020400e058000c4174405005600580003070600c0008a03003210f484940c80140c054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 845754703 1250 845753453 845753459
    0xb03240a020417060f16081513150f060c0519151b08070206071b060609050f07140a1b2f031005070504050111010e03030f010e0f010602030a1107 64
    0x200b20f04602c00d03d4040241c00002c01c0204040803140c400e5007041e83c514100f01c4004520002030900a000781c48070524080001e05600203541d5102158616000c2a0040c01110039240040c102c08034180034840401c40304840101c0c00b01d03c02c6c0c020f030002681040090410b81c208411000280310b10540c265280d1445100c60800e01a99000d21103540c0c0d28803c59240e10711072160018400076020f0007000454000720180020a54000700122000d80c80c3e815801c8030243d5031509000800f0503a02988080b03003800204406c0b6100103020f00c0c030810154a0350408554a034407411107910400f4445408100c9000619013801304400e4000c002c240302b40c1844524101d0301e006180c0324a40c600749a0781081403989811414242800101c50001c207005007807285040510001e0300b107000e01d0144c18100079003c40c0180c00c3c148250440c10a2100107410382e50b607402d00c0214025958424000c070a00b83c545a40030130040d0300924082412907602c1ea0140d414004c0c0d58204480d90303007030082c1e068850701c1029008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 845755953 1250 845754703 845754719
    0x30c1c03021219080f06030c01032a02061f0513050703020c10290a030212070902130f050108040c090e0a0512070203010b0a030312091e0f060b03240a0204 68
    0x345040e1400c01101d01c4140450a4002d008890003803592103015800000e0040d81d80300048c0a44014100b402d0201d4880c6410b0840702070a104004030305240f840a074100c8081e10b40206400f40202490000e480303130803031500010452692103110361600030035a03072506410541d043e030001e03810524030f20f001352501d96403000140c84c01808681c1404c1c04ca944081008150880c0c4440d60045440a14400c008001c9080000c1000c0802d00c0080d005840b190700b120300075107041c41079a014141d4800115120b2a144840125121003401380c0001c40c4503450000c2880e60207040c0d51032185a01900f6511824142880d940c003a00440741030100d11310030100c48d54001b40040c000e424510f0364a80f03140d516802c847c01014251000540102e0044200d90b00074404682e000c0d502400c2302c9051000460680ca003031a0140c8585819140030914800c0080c8138020044035403d01460300b07001d55020710008401000f0980c0380d40f1a440180d0700c6079854082c002c0f88150318410194080020031005090075a101e482c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 845757203 1250 845755953 845755957
    0x170a0c05030a0206060307050f1f020a0209041a010609080d0c0c0f18050c0306180903091c050f010216030c06090f1511040506030712091407080c030c1c030212 70
    0x2d0703030015030400010000281000c100c1c203070091404071004000321100c2c030041155840c58203032884101e0300040581070701d140200106000f9a44c0074250a1041c42d0508003ca40454410280342c1c41c80e00724000040c1d001d103c0c040d40415284d000010f410803030031860f015140d184013114100c03115002003038000ba0301a500d8104c90010055400e2742d01c3d002c0c03e1050641e040300c40007840d28510081c14010310005440300b00040c8407001500c40403101540720040b620340355000f40021298403040940c80b24100c040d159098008192041c000c0b00c4030400070b401a2801d074003d842c20b04100d41101070f40da0002c284140180d41d481c60089038009078030b00031511440700751140e9401c10b1f1070b01840c0140310002480103200d616841d856000c0d90500341420100010340078403000d0308500c10444010381c044510442640301d50340c1c40e07510042c17403441076041c01c103940e4480c8202d101e2940540140d46019809040102d419251400001c042150310078200000d0b0840e810a06400e60445c03140c00b142c603242c0380e00000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 845758453 1250 845757203 845757217
    0xc05090a0e090c04110915391002070b0a05012907051b0a060804020f0609030c21010e070b0703082a090f010302120105090a0207020d060b01030b03030403170a0c0503 73
    0xc281c0d41d81b0782500901c0940c0f160310024500042e8108200c500040e0054034400008054018074002044180d64002c2414003403108001e4501071090319040c0003507968010300d085131043c6003c00c01d960310000b40d4411118248250761920704140380c03854501c440101c07040b1041d12034940642c02c185035034076076501d0f1801040e4403001003206003245018a24088451000421203880c100d805454250302160203042910481030241c000855024071581d000c0c007000c070341e02401501004c4018003030f001c40c440b01c40c01c2900305003165180003003600561402098440c01d0390ba41004162800c3c04984c1e0844141d4802084107003056001c4500d4080310f0f40290780c0d0a403000b003584140b81c0707501c02c4100300540140303000d0105050600c10454203030164032400c80704c1c0c1180d00c1114442030716502c00d100c1d000a031042c0d07100258880d5a48450004115099105021240c000c0c0d07400c0011000f54001d00d0f03a00c5c49140005803450600400301c1403e03880034401001c428205103041555503802c0d59a040c07858110030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 845759703 1250 845758453 845758481
    0xa0309080301081b09070203040509060a0b18130204030302070b031806070809070e0906070f1e0c0c0b09011d041b05030f220305160b0c030a0c05090a0e090c04 70
    0x10380e51903049130389040315150b1401c1104c883c6010b00304990042e603688940d00c1214010030100002603010790707405095000414803c140e49565041120400030088100e03d442881181d1351700046c80424041e20960302641c0d07043e00200091801c0202a01c441c0e08010035001d019030907800c8080c0d413070205006090141d025502d4501d0036040c0441d0807801c103185038000c08000300e081c100700f28605500244040d0081c0c404d08002c0d2705c1c294600401c03503a000d040b0044030403130a10b26010f805060b0b030244941a20030f000381c2001c01d110391242d0501c08140308101503940000e0303081d9202012030502d008100000d020040c8006010304050400c0b4444d0010f41014501182e404410010301031000784800350700c60180c5111400708074030f152500b030840040c0740c0c002e820410302040440300b0601140c002c2000ca504000c0d2050300d032800e1034a122456108440002107503050420a0501a00440c199105151700810020301c9070305100110440c0e00f00284807000e20b120f08050710340c950301d4504c02d903420081c1c80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 845760953 1250 845759703 845759713
    0x4090302030c0d0507120503070207150e0406080a03020d050f04090516080f1b13090204150f0207060914041b0905010e060c150601020a14010b01030b09090607050a030908030108 78
    0x4002e81d0b034100020300640d2030901008100e00000a25044801000d9000b00c0c14056140e4580b040300301d14118040c3c00c91b800010a002540744c0d1503410000050501c80211014040b6a4440440c42d848000c41a00200136030312174165440420300031000383c40300c80090002c05081542d107103400c40075900c4c1a5a5400510901c0c510790700d42981c402c40084d4460601e04481c200350504c0086280000202100800c49180214403003002e2090b465258000304130039481903484980f651044903141a16190000c08280d101008001740c5002141190485110303481c0c031041c01c0d00d48003a45d01c4891074000243e07801030f40c075007100f00609507103015462501d41c90381d1414902800d145c0050068401c0d01507c5205220911455421800001d5003000b01c0108180c40c09042d128079006034079005410a00a08814440760400080e8005501019905030300340e0703042c00200c4518061044101c004d403009506034200d0030000d402e680c081d500a0042007000d282c00543d2000540364008950000e07084116540c000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 845762203 1250 845760953 845760967
    0x705090613050114040506040219030b03210405120d0f03020912060a0902120a02031903200a0c0605040602030a080408220e0c0306060301150903021002010509011b021203060607020409030203 84
    0x14810547e0000096800318a070003110240401011000b01da8001016142c00b0a0b54142d1420b11242c406140c41078076843d01d004814007016502e80190045e607001d010501c0105041c1b81000890048100c0162107095001500e4001140654020500c0c136402c42c0c0d08081c4022004400c000c43c41c0320b5502da90000600780c1c8030f84108a02d0280c4a090742e0f44907840044041301694011400c500c009900443c85810f00c803945c82c0a039658a03841c0054041b040454010315441c9030040303903004200b8030906452203a244c65070402e40300e0380914066000143d00600403505414001c4000c190054040c880306400c0c5488203500d14030748907120890f050703000704c8034204001718050242c1d8503400c001540005400d52500002054040c041403103207a40d030240c1703240e400090318001c83c0c4540255401800305d0b0348031841a40060302810050790b001860b0740c6005d0780c038003179040012450700010405501615a0040703443c030040c00340c0c202525080c0c1c042010040308006a65034410120814803e40146440e000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 845763453 1250 845762203 845762209
    0x81306030f0b0a0f06050309010e070e090c01021f02030417030c04090510032402091905010206090a05101a040911030714090406020c0c040905010b030f0106080705090613050114 78
    0xb02c0100c3e005a1002d082400304c4494801c03213a040d200305240c01600c6e03540b640c80c428003410020344c829019005450f00400e51700103620701c007880f84401a003142d0242881c100120b80d191150b1880880804286070520b10f131018640046411030301601c0540c481c112551417a090590054030040c01d43e42c000a800c12000381d440c00f80550000b2203030b4800d85880d1a50301c0c4c0381d004e0313000b640d4140700792941140b03031404500103030b8140d030b00c1100c02070440280700d0211800408000342a01919015105000000e40d0914001800d00b4442d54000301500e071305921a16414003401455000e0702d55100d03800000da420b91030720f128a020450150300e11030101c4103240700b4103040010f290005440b1804409107045903846908280d41c103d82c1c07100c0d0041c0e46007020b1100c80e042c11110b0741903590040c14001e0300001d0100c15001101c04c00310031016640c24540a451050880b400b40c40340030260b80010800700030515280d1000c80d8080340103486407030503580d195499001c840b4260071031030010b210461203a910341 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 845764703 1250 845763453 845763461
    0x110f042a030608030f090a090c0801180e0c04020a02010902030a0f030e2b03050702120105010510030b010e1c050609031c09021807050c1506270c0304081306030f 71
    0x3045605081040c942801040c075120b2040e241c0c6415000000541003c507521070440c20f000802c5118010400300e64001d0004000e42c0b000c0c4a03c9915800c00c000045003000107105441d8081c1441005200030001881480b000c2d4001070261010341d5603d040150140e20240030309242c0910462601c1c080c0c009516002e850402d10414441c051120301140200a000c886001a107200f00600d40c00c0f8030800c42d2508071160f208250b4001c1d000003c1c95801070081c031054224a040c0c0b641160110011038420000720112a400c03031203031340091441d042882482c2080c1101464194130701550b8007480000b5107443e49400001c1d40c1d5200705034000110001d0703840045884082010522106200002e020340004191079108400c1208016060011428680c003540c00c584080310100e003a684130000309072440384c45030411900c0b076009800c034010068110180e4050b00c07a500d8060388024442e40c0700e14001380500c1d00300510032200a401044503012200c0c103800d0b003100518050780c0c003085000010713402100359 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 845765953 1250 845764703 845764781
    0x607020601060206010b0304210e1008070903061e091208070e0603011701060f0f050a140303040b0c0c18041a070206150301020d0908041e060804110f04 67
    0x6401240042c422594041000750450711505103898036a116030521360101209484805a226507140a007041160040d1108114400440e410181c2011100d01680e404c0c20407100034001401480c0c0502c0000c038540e0046403078949040316020704030422290001142d034025020741c0c00e24402014400c1c0a5070100540e80d00c810b030340c03511590340d040364404202c0390300040c0038245000222118030603080303c0951140000346170f0803038000f00155447c501285505030b2030003424081c24015070046011030110300201c02d0810080c00440c54586081c400394110f030495445070740140151440c0d100301340c0d1010584036040c0700c50025081c03036045c10300e00200000401c014007103c0d90100310401003c00c0e000720305503901450307101e91090f65910203400030380203100e85800c0c00b20807458500180140503080c0003400640c0c8401e0245040b0100c081c1c9800c480c420103126a82c001040301c1c1c000740000f5008100c230300030050050b0001c51120079003c005030968030100c029000691140010140403585d0280b0403c40d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 845767203 1250 845765953 845765957
    0x12030306030b09070513090f020904030f20030f0a05041205010c030b18010915080102040f05013b060c06090d03050c04060914030319050d0b040506060912010605030106080a050607 79
    0x83c4c030304d098003060584840c190740782d06044d603e1a680d424058890700c2aa0441d41c01008540e20b4546490051315040f00c102c4c0c2d10000508050b10511085041c0300120b03500e20b01c510045007003c0ea00e4018a015902c942011410028280400140384c20301c89914242588140e0001c03944042c2050002c0450300004d8a00744604a14100000550710070407000f41503407041103001c2603040355a210829101e850780d100720040d600c0007070001a008880c0c0d0014054072800d9a400c5a030740c80354000b00051700701114500e98003203a005418008408004407101c0744003c054081800c0051401d132542c02c1100c2129124843c3e0403882000c1c25145d454030860f82c0c07014990001902740744c18220010404c030200e000f401d1040201c119201c90960341007050b80c0a407150070600032a444e0f842e59005000b5003201303a0509040d401c100300d03800076107058014203220350400360810303090141d09820040500c1d900114005a950384e00e1002c5401d440a0007441d02500345240101800c080a02c2c2062070b060006103a202 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 845768453 1250 845767203 845767213
    0xc030c060507051c1e091e02120f01093302030a060306020408060a0b0604080d0804051912170c0d050703062301090b03010602070308071b0f06080a06150f020712030306030b09 77
    0x1300080000c2d50400d0002c5003030380e04450030401d910110342c40d0400e5910400d00ad2080c014203001040054000584545c030600c10a800b030010690301402d01182404944020104104200002c0d92180c0c0a10792211b0f00450100700d40c0c2e0b580c0c55400c00c0740e1264110020703d030048070400403900554041e4042c0e0f08003d40300b80b842c091901d141c5e03588400350080110200714401c0046814000104038120300302e0800034500b440103e080c58480d01440348084480080303104102e600186100c524145132060400c20411340c601102c0800001c0102401000ba000703043c0c1c0d4000109201502c01c4022449080c0c201003240b8048500b00003610940c925803003000c07110b000304010f0142650100710201101e60100f84a034803460075203800d0605148091141c0c44001c0101c1c0001461851601c2c00001c449507612081c8284d04c4540703004003036038280c0c0145410346660761f1024260500c10b03c4046851407035841502c0e450390b1507102240c641382ea0001c00340c0019450314014414002c02c1018660400840c0004003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 845769703 1250 845768453 845768471
    0xd110d030f11060412030f0b1c140a08070201030e0a0b04032703021c020d061505040506040c080f06030a1e050708070303080708180609150105010c030c060507051c1e 73
    0xb10000f40c02140d400301a1203d015480c990071a802004240c1402031100780120210400d80d0b140194027038041d2020045111000190b00c0081840d04040c0c0d0020201890402550010350140590b070445180700e11645d04017101040d061070717116005d68440d0ba6600d00b0302c800c45400398060143c0d40c0101112549a100400042ea03429000350707079010b1401c0f0100705103441400058003100c40000040c2c54281003200422080c5152007204042c2c5400700c2c0d0801164903524244412074a1103010500410500404620091400c4000c0750f40b00200904440101240b5640c45444441c90400170311001904c1300030008010007802200301a01c00c1600804846195403070007000c0d0710303001e4022002d100100d4042400565030380343e801c600c0c40c510307003c079403190030b015100e640d540c0003d03069003c01c2656500080b0b00c81d032041180d038107200e405541e8820090740c07648403000240400f40505052017410810418094154200607810203070040000801e086000c3c090b007d2140b046000c0c109452034a8009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 845770953 1250 845769703 845769713
    0x7020105011710150b0a02070614071a1b0c010b0a0e09120f04030b0f0402120f03040e0a02040e011e080610060e010918090c080a0b04020d110d030f110604 68
    0xc9035040c40046000c54810801008008298070640104100c07000000d480c08886e038000480c0300032110565110240000e070900e403241c40703000d0601c0c010031407403400c1c50000743e14100d00707040c640100071071110b000380e5148460300600d194400f00901990340d455004e466480d20346150300d8002400c0752408000c680c0380400042c0d0300d17a128101685428039000c100011005603004c1940c02460340304100d50000e05004500921004041b90200e10079250840c05190309400030600c0952490b02d0001181840d0a05111600415004103a41515642803000142e050100320b5124001c00403154221004072100d107501c415054103401c10070700d46e8429400d11800c060740c4080c2c282142c0c060314210010004000040b00e034035000d540b0210b001c150100742c90002c48139903409440039901c42d2000e000615903034011140c941d44001000342494081d100090090b0400000300b490651050b00c84030b404114410020f02d002035540420350001b2405400c0c1c440c42d5405c205c150015060f510010011490030ba514 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 845772203 1250 845770953 845770963
    0xc090307050d0f060c0e040c03060602030412020f09071713030e091f180f050118200f09011d090c0a030609020412032a12051908070201050117 63
    0x480e405190020b0103482401141c40a810083ea804070080c003940600a400400703030300c2216030031071059240038207450b8900c0c0039101d0314013200e000c0c0c0c01440c2840e11f0f20b1200c10400303104100983c1c010303080c2c081140d4145c1d5200301d500d100d45500d40b5082c18224034091248004100140060140c48802c0604130100740c0100590300302c1c0344100e03134042c4580c1c0c5007824800c420500e00200b100020b4041c6011030780040ca401c00001222500104001d2005203424002c01c1c0c540c207200d10351300e001040040d00e2202096400a08041891002c00c4070704108d0580003070300350303800102c2040c0410008500401d89680c400c0c03074141603c1c4129032010200ca54840091000000a084034803450000103c0c05040c0e802034108500030b02d0300d42c2d011500e0740ea0328404a1800b00e90054120f0010380c401142e12820503070b0f151554a49040340c0288540701c0616628071581e036802982e41d6052110902c2500d040010340c2c9501c94a8103a13550b42c000b4581001040a42501c006800400c02a1403030220121a1a00022 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 845773453 1250 845772203 845772209
    0xf1302040911030a0308010503370501110409020919140f0f041401030203101407111c03020702041a010215060d12020d170705090d06060b03130b0c090307 68
    0x8000400824a141010868802d200300340e4250052400ca081415084201c2c03c3c100c0f0003d40075030b1700010b000908005050306c46a01030311491a200340c0c1e01040c0c0c0d403074259505042d21031f100000c1d0003a66200c080c03043d03801940c015103040e5000201c440b16410002031145150070a0701a101c28241020780c18045401c2148202d07004805030f100c61020b40d81d400c2c02000030554040c0c01003200390741040c2c808120750800d000681c024445d59032010413000071441801d40030104024682115111302e00210f03a100c00a0303c1c0c1020354401e1640c02c00002c180061014040d9019032401071b91400c0f284140825900c51030810000d290f5201c1b2041030503600803580c140303188803031007a1418a90b50702002400c950701d0020017a0800074480f9411200c80e40000e8170100d2101651502948030038142d00c0030b112642c0c00c5403600001001407100c400c55081c41c40765844458030841c03000c02c8040e1a1144000550400c540001c680702c03414078044140409411a1034000005d60201e0740303440301100209580d105688 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 845774703 1250 845773453 845773459
    0x6060f0c031206030605090d021b0108040f06060902030a051504140a020f070b0109020a08100f12110904030e0a080a110f030f0109120e09101503021b01020706050f1302 74
    0xd18002224403a90100300a1641702c03104210605103028220756800f0a04840c401500c640c54086c00750b160300e018071500c40c900503925400541e95507a201400d040c8500b10450382d41d51140404100092180090f503c200d007540350000745844d00754180401e644a1050080c002c52620a006000703500d10321360168030501618002d41c4e1080407403c0c100315481903038806810103440000100e940fa00940041040d180541e03540c4d00070352a8500c0480c00702420b80314190180c501040d04100300b0340d03000c1800740c400d0b0144601852020898001c0f4140e032030200c81c1107001848070042d005507403800005800c00340c203500c4000d2420007090350f0783d01c0e81114044001ca200704109400d01426950070440b2114141e001d42c002d0080c0066440c01a20315650024404d0110364403644078061410018980ca20408041d0f20100b4403502d440030401c44800c0d0042600304243e000c0040c20654014821210f100005c15400140d644d0120700b00071040b41c03000781c03081c0c0b84640c4040612184400f220748044802d5012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 845775953 1250 845774703 845774717
    0xc0703061e1a190911072f09040204090f1101030c050a020303240307060305060307050105090d110f1009030606090504050706081f170c10052a060108070906060f0c03 73
    0x40b400000f07100c42c9510040d00075040c0010b20b440288024054821107204984a4032407030b80e40303000700d804442c000704404060000d00305005250b28000004c25045400039000280c04d0b2040c3d11442c44120844000380c501a01900000c0c10710759051051000c2172100345130040c10042e840400949900c0043e001e254540d680c0c0004000019180102c008160001003c1351041d1b40e5940016010b0b205c1114102e100b80200300c0002030a5000740215154444000c015014082d039940d00c1c0040c0c41100c03042c15400842d9240a008981c079862100c038465103a540707500005030319518103241075504030780120034202c0c104012320000034000a13041c0143d80d11410000e9807a61034040190012900ca00d02c3c41c41015005c0c00004d001110a200142210110b01038482c4c282010341405040e454005a4000150042100c40c0740042c0c0c905500c1c2070321040c000741340072189a41c0d0700e4600d0b120080c1c100c25142c1c0c00c12282000a550f1512940c401040075003025442d407800d001014060000441000c0c6c140000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 845777203 1250 845775953 845775979
    0xf061116060207090606080f04031101110d0e010e1b060d180c0e070201060323070305010507030501051c02030a200a0b040609120803060111030c0703061e1a 69
    0x5001812180001420003041a6600c140003036542d440e0340b040c8540c0d28900300002c9203480c41000700c2446114182c2c4002d00c1a1280e0750f044030058040303281000d00d03558800e0800007a1851900420303140303001520103d8021008080705085401080700c100c040d91016014100b444a02004003a000704200e5040761151410711000002e09000c206190199280d80440410003055007120b0003070382c150b1000300c29590303510b41d42a4201c40c5903003c058450102e48220b00c00d100e074442070074094641c0320415100300c1c0c0d96a80d50142500e01c1a00d90a0100fa12000144118140503800c0c5400e80c465000112a44d0b08070f401183d154400031001034044035a02c0707007902d10030464070140000590080d00c00c07581c00c3d90f80c416140645c1c02a0107981d0000340d820b800068064414401080c0c00350f00080040d01d11f03200e0100544038030101000f00c007240e010034004851900c40500c41c4200442c0a00008162403003546120304402c03801109950002d442d0840300601c6000c004a001201601510310031000e881d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 845778453 1250 845777203 845777237
    0x2030105310509060703110a0e1e180a0e0d0804060b0d0b09010c350405070302091006080f0f183306040c14070c0b180f01090f06 57
    0x45809074440c601810a0248811100b0001c4d100384502c0c2d142d6010044907100340a29038551040d002d55100099220760084624902622008084501c8030480c0000c1c03905a404a218148881140d01d030070110001042203141d040c1c060344400000c011301a184441d610034000d4124240500f020305401d03562840d125042d1030313007101124229080040c0c040f50b450305d04240d034041c040b544602c80001d8181054000c0c065005007141800d4210002c40b135168100e40c0b160910b8062002740196140c3c0324181000000da00c507650605e004a0400c60101001810044090f0074805c010300540d41c803003110310400c8403a2070811001a00310081c0004800303841c50000d1340a18044009440381420001000825071440103202c55440c443c001c0c01099606542c1c0ca81000b00b210345100d0300031b0200b00e00540503c542c0114500401101d4400c003081502e030b40d110190604160402d49285034a150340620314205498070345d001580304c0001b464000d0016040064505a49019218040078044101c5001200c25 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 845779703 1250 845778453 845778529
    0x21b0607080705031908130b0a060f030c080706080402150a09350c01170702101a010201050f0c18060c15100801090305040e180105090309040f02030105 67
    0x6a049903801d40c44898a0030000c0c2c49602c104e100c00b0302c101d0b02611480350399000f810310302c0c445d0307400200024110070181c0b952015054000c0003032210580c2d90303101181d400400da410b100614080c0c3c0300c1c103040b1800c100f1070500c0d1204982250046c44200010000165a015001d41c490851b50794600d0319000030410a8851824a402a0107401e0308030520030384200021303088890b50203c2c0c0c00214003c1c49621031503601d40202254907400500e640740b09200c40d075074016015030410107510498100b0402c510b1040100c88d44c09082c02d008001d840d44105d12580d0900403560841a01c2134240b0641c203001c50040d05610070501c80b0040402c0039501d000c45551808155541340c602c6806070348414024040c0c00100207000c940c001c900000c00c600224420905102e403154042c0e0507110180350038108008010803034001070800d400002032460480c0070980c28000e250141c1c03803100c000e5032140c42c2c40c01040140c0d2400000000000c0c03060004002c0d550b6803007201004822041000c0d04da885216005da10a4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 845780953 1250 845779703 845779717
    0xd02120708180405010b090a050411090904032a1406091005191506080c07030503070305100b0c150c0f070206070c03021c05011b0f08101d04170406021b06 68
    0x100b41382a00000c2d481c01390030002c020005048451044803502e4400f0041140c005402910704070205000340603440c1004681d40d50002e0107801c1400002c02145102072404003004a81095001024130034410481040744400d00354000c1405803ca07454101c8140d039a84403103d0540f5401a1180c022a00c214a46c0c105418009100c0c4c0e07052081950f202c1c01481a0b6156200701b20001d5080300000b151940c0080645082d1036040d500c052454841a1046002d0f10001d0f1003018108140c1c00e000500030115401404610f0310400600301043d610101c04000003030007440002040d10130090080d000780500c0440d406160304a40c4291183e0003410004107414554000941001000400115182104c1c0e5004c90f0588204001e2200550580700032003a24008000c090114145d2030341d49104038090016903030702c620405e4440b103c0c503988013500c18102a61a04100303085004800340f109000301d81c1007100d41000c500c005585008c2c605080255200d02e46640503c00748000325000003140d80b0441120300e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 845782203 1250 845780953 845780959
    0x100309031107080c100804241d0a030906020d020d2d050c060601031506120902091003031106100b0703170c0d05060405010e0112020102010e1e0d0212070818 69
    0x1c6600c41052680d11004003c9440c4501c100e24006500c5c00c0c0b080c80c01510443c1d000d0000c1515440d800c1c0540714200d01c0d03651741c00100351100b000d00501400e200d00c50040088000041c051506c1c107082c0070700302d8040b540104086400560221030001c6d0000360b052407001c02c070b107040f8142058841f01d054400b07000365084110021800341281150703038048050b00481c070565066403c20340f41c001c015400c482101c2c1004010810001040200030f01075580c508000e00d90410114941c840d903800248404002c40c0c640c001409150300030310a0651050001d0205442c0304001d00440c241a100e0380141104c80c030406094020004104081502c40c041802e409102c1c1d41c0c1c0d41d512400c1c0140304e4035554110040c80300d00b9074545070005c1d03003920b003034000d40d4121604c1d0302682c512a42800340c2c40200010f406c02c160b05543d05c60003140b000030420013429808590203040e8400140030201014100000c403060113085600550180c25206405000c40b1740b000e61020405580700301d40104140910032501010798 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 845783453 1250 845782203 845782213
    0x16060b0a0801150609050307140d0b010e0702100b1e01020f01020f0d051501080105190b0301030605010e18060f1003050303090604030f03060e0103150e0a0f051603021003090311 78
    0x40107801500f0101c14051807901c101c11103515908100c680a04600c105541588622000c01101105984c08441c0c148082c0c4500300103020f071384900d848940e081e48146030887c40c1c50b0401800d41e605000546164040d10018446450b4400014000b042901d403001c100300a03c1001c05104e82c002c1004181003140c000003035441e003001300200580c40d00400301c0000850f040078000381440c102684d2072800e40c80c0c1619241e880ba4200f02c1400503161005802040c0582000c0010801d0000341e800b6500030352040d03202060640c1041c0034854010405040002c0030654491130f44480c1c800480d81c141c2c021408152041c0598030512201c4010120350f001030400d010000902140d61800304000c1c1c80355000792164880d014000b14118111110f6110b00308003520290010310000300c0715908501003000102e000b1400d503009040c114140601d18504450743d00361310045504000b0288610043d010765054002007240c81d64000c6948580329111500c101640e801300201094010408120a650307c030303003210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 845784703 1250 845783453 845783459
    0x240c0c111206040f0b010b090612070201060f03061b1b0f0312061212090f090b030102070503030f0411041104050409060603171c062105152401030506030316060b0a 72
    0x542513070b030009015114a030391400085500040042114404000500418a400c03901c501c0c0032200c1c0e0002e0b00300e42c115521098000fa0490055428101650040d04005010006061a12065000450807005102d1000c5400509002420425914540002c440c0641080c40c1c40d080301c060380607a0004080c1864850b0214194441c0c03910a03440611030a0255a00c034034106080d0b813940c09500c0b40802402090ba014894982e80f0342214842d20300103400982812010b0340c405095801c100c45180301320503540c08100500c2003101c00701003c00d405450810010b03080d5001414244901e006090166450300c5001d010019254000f100035500064a41904070b03401c41a1545a448581c02c1c403001280c90f2120420740700b0500ca0f981c00c580703002c0301022001b080300000385030000c0740940030b607424040d00705840d0001c1c01c080945841500440c583d002c0c9245070840b803599140140a1182c100743c030b0300c01000020740700001101c7d1243e122540300002400113181c2103016040c070441e203d8015100075400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 845785953 1250 845784703 845784713
    0x2030a09030210050603071a04030f030e03061b03280609050a0c050301081c090b0f270a06140918060418050604030f0504050d240c0c11120604 63
    0x40c018040c42a800c0d03940100350180180c081d50802c1d0307082135043e000200300b042210b440205050810410340780f9170341090b80da40c4500c04050003903c3c00b03401203149100800091310f0305014055215603004082c0d012401d01050040680c08010f0441111400f008c142c80700c043c0c0120f403d02c05050140b04180b040075183c0212030701500e415188040c88070b041040f56152a13002d24260b0303040c0d486000c005c083c03040000081601c002d100745040000e2090202c00812084035010003810f80480718280360360345015050794181c425040c006203113211030074100b002c0c01941e68840181c041340c585150048105803102490440342c0f00f01071400b5800784641ea107040700091011041c521400044604020852080c04101e0b0517108031100105142c02000004e80001d0080c980c401e2580c031a80f804030f003042c1e00e8901117442683c01c00000d0b9403540c4a07001544402110540d035600d410f1100409105424940c80041d080380403900c0000c08440302c1c0e803590807541c0c445a0025680314914402c0300c880341094102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 845787203 1250 845785953 845785961
    0xd181e0513020c0a0807020d150b010216030b070f1b050c0a0905040b240d0305090307090605010c0311030903030f03010e01090204060503070518092e030c0b030c090402030a 76
    0x198078000c14015450034844003051080d1204105198060815011180e48400d4507a0141d030382280c3c4131502e14000d8010508014100b4504481c0307210000b402072411002902c1c2407031241404c8140c0c0500003003880016110314a15402c00400d0a101d00034001c480c60a49410103031188040030003803880980004d1220010b202c580603801580c540c003078a0349070712241040c1c80c421103000d800004e13003101064103440f03550000c110b520181d142c1c0c0c132111991240048d00141760980103900080010030400c1140ca0103200d100c00402034800c0c10880c0324900b10000e0500c1007190406400e003c1849581c84502c01c00b882140d0442000405584c0d42d4003034034108180e10f80080c000c40804003000000411510014402c40701950304035282c890031560782c54000c0301da560103070b403020034401a150b5180000d51030b00d611903400f807003001c04104074840941102d4004903c2c584444000c03100804c80030008035610304c0010054895041e1840e41d00e41d6280d8040300ca40c400c41c1c00d2140c0140c800420846000f4075684 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 845788453 1250 845787203 845787209
    0x1d040c020c09100b070b0c0403020a0f0602060906040203071202060d14010303110601050a3302010b01020c01081510020f0703081810081503010e01111e0c0d181e 71
    0x180401c01603c1d0a6a591030036001409941050882081903101140e034840310707242c0c00800d03146c209240c00e0700ca40c08200ca05221354400d14240d083c1902c14004250140501c5a000d0306000080682d443c150700080c1c0e0724542c1e4440c80c0030004500301c2080a544658049a4688182100c10300040c50b140000f141c180400b44000e40c0024440030720b01030b440002084460407940300900310600d050071702d81c0076001880e20080d402000040c600c5602c01128548440708203903e26a000040c07240126000642003000500036641000302c4e010410085002d10102d144031080265101c0b10441c403010001d078503066040000c24000d10032444000100286038006042443c00d09290183d00c2181805200007a068a000080420380b14400120100030942848490310001400071944c800d0b2500040c1c02c4400202106001260024030343e01315510b070100b02c00302544e00c4091546003580b000d2515454040300c181c81802c0001001c6c80118041c150314151014200c01003002000301e640001e41588242644 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 845789703 1250 845788453 845788459
    0x280e0f0c0a0503150a0b060702100c020f03070e0c0a030e0f070609060e0f040c090f0b0d0507020a0f030e0d020a0b030f091b0d0204060905041b0e06060a1d040c020c 72
    0x441e010400e8200803940c08580142150604402e485512202c0040c140c5401c400d600a8414011a00980c0c3d6489101e1000515500d03040840c051a00601034180011080113000360700040040000b6030038200032a50051040d40c040703840381083d90045002d0841142d4a09280c8201110200c0c09000031840d201103a085440700034800e507071010107417161008000c481c0e074005440d20307400c81103003465000452244202d2603c020615103805c2c560500f07265540090381d2480002c04c1c8000e002015100740c6404c003041e4001891804030070f5465078010450203100074204201e441c1c10b05019120f9083d8418500c1d0300a00c0c3d84042ea0b182c5001058035002241c40c54034105140b000701c2d4910202060b503035200c1c1c0c000950f2881503544241030041c81c00160004981060b90707001c00052500040c4680c5c0c1c0030303c1c0714090a00c0011016038003210008003641014059000c020240030455a0307800031200400658109040e02d20104010605150070001e02181c0145c240051510074039400f041e692300300d00d021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 845790953 1250 845789703 845789719
    0x20a050a02010e07030c170708060702100b15070f08120a051f03020303041e0f03050312100b0909070e0904060b15070f03030519110a09060503280e0f0c 67
    0x3000d0f40c0d5540c4505102c003030407003608182c0910080841a007010801406442110b050a6031a04124644801180c0a20050b0840c2d80b850011000c60f004d400c0141d60300b101c004a6004102021601d0352091850080020b040c001d83c00d8200a0b1410949100041d011051415880c06454034005004101c030440103250718580189402d03070700590703000d0680b900a402941020308200034040d51404003c05801828080b50000500c403440c0c3c1840400b540c401e41c080d540310300074000400d615810107010881104040030003400441d0480c0c081e221030384030844046400f80c40c3d41c2820f40741640e95405551308020b001d8104028400c598102404089041d02e00d010300c81000c00100d186800795040041c4224a42d0b0a81c0010902c6500044d41114040d441050f0340400345143c4012514140294240d840d00460301c400359a800c2a6000300404141c00d05038554a84046035001207111801c16007040d68440ba408000c2070400e42c45a1002c105000869406265a51120303544400a0614a10035989 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 845792203 1250 845790953 845790971
    0x5100909051605120d030509030c1912080f0c0703090b0a0e0f0409050a08030a270c141c06020417010e0f0a0c061b060c08151005040e0c070501020a050a0201 69
    0x3070051303034a09888900a0030300200e050f9401c07005000040c7c0301c224144020300c19110500310510030b00c011110400c5403d0403a02c180d1400356510940550f200080c41194810003840d0b00299004a6100c06101001952110340d131405442d00d01241c0c01500d90740d000454290190781c0c000c010005114000c42e124110742c09840304200030748000e410000e0003034200b042c400380000c1c440d4019503000b0804881c0450221443e1444a8050070850b000700a45014098400d0a00081203d039402a10804001200402d006004204005055000d400c0300d03415005d02e0030144185036050340c003d01076840040c220201c00c101c085003c0c18203c2c00103203640c090805007051002c0000341050782182c3c403900c00501c50b490040c040e01c0c1c0e0b1680d00040d01ca5902c07104210400520988074962941c5240d0322016401e04020010500c0140000001c0c2c1c0940f10f4004081c40d42c80d0000d054500b1200b110081d03040642d6040800c030101d000d4180010090b40c00403c150390b6160f044400384c00349180c01d41c000c0140b544 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 845793453 1250 845792203 845792209
    0x8030a0510081207200907020a03030605030a021c060b04180510090b06150421060e060705180609031002071a010f1401170907060e0411030105010305100909051605 72
    0x1c0b1003c69144a5404100402c0050482151808504240e68004050000c00d0f40822010203086400100582001c5a0300c0105501880b56a01070001036006241088559000ca00000c40d071725500365550312484042d400b08900360700801c1140b8006801441403000c001c40c9000311160a03c4100d48a01426542844242c901d208a003002508a103400790981c0fa40828056080704c401080081503004002c089011003e8050310074044c03000040c1d54003060010b0034108101e40c2860340c0c4445540080060042c003680c004256802114007802001080c2e44000c0003c045101d03003686070341c044c003958621440c045a107034003800302c4500030545150760003c034001c40070703c440302400380203c000c12a85052107800c1305c00f84c6200040703206040196030307a80b02414030103001601b00d4811690b82e02801d024446070f5032103855600b1200b0240c07020f108040410020311024041401054101641c03600000c503241903806000c1d0003000100b00c10060008242411b82e03e9119081c0c881807102915500069181 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 845794703 1250 845793453 845793463
    0x1b080601021011160305070602070f021c030f030b031f05040618030203120415090605071e0503160216030803060307050f0105070f020411210f07230708030a051008 72
    0xf003505403019103001002c030030380d0641c103c800d0380540802c242481504002036807403009003404c0d40203050000e542d40161040040554425032840c070012800719000380001e40284002c1c0c00680703582000315950035610086440d00c11600c0b5480030b600c404000001d00d03020664849070195004100c184100c00d40c83e05d90640e140d1402a004005034000c000481c581582c0e0800382d5041b505c06c201d90b04406c0d4030410101d040c0c501d0300c0c0d42501d4495541c4240700c501908000034010307443c100002c5048031f44044c08081c029020080484c0051119050b8115420344207005607000300c040d00380303000c150503141d0074111519001107071040d01074401c1d42008103092030107c2510060403016500c0b40d1a00302250350340d034031500c0e035668101e810644400742030181151034000b508030320704691070702030101c0754288410b09150b0010f070510506aa0034418420b80320b602200040c18a864082c84615800907003d4801607441a2200580003680c084248840c6d9030840c1c20090044204503200c5030040d450710007664840d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 845795953 1250 845794703 845794721
    0xc050c07090b130911041d150c2a01051314030405130b0a0f2c04020f011425140106060f0e0f030303270304050d0204020705011b0806010210 62
    0x12031850000f54080c0314a40046407940e11403003103540503071000c00101b01030356000c4d0700e1081c1c42d032003090140071500810003460b803000d030348841e0184540c03e01403064960b610840d0b9160000300c0501a00071118680040d4001c0d2031031035130008000d40e140028404e002445200812070702a107851910004850000069900356200145603441e0200c01400040040112909240c2c00403030011001421001c00c2d42068000c0c510304181880054070310744003000446041149006c0350424400b800050b031101111702580c00c100303003040d42d814210450f8011041c010b25000c400002000440c907080c0386403600501c03a60070311441c05050508020102ca0b802d945d0140101000140c82c0c1c1495404640300d8194a04104005003401c0c445140c103402180c2180d2044035068105800d050628002051072140641038009080c0514201414030001400c0201d0205010b4440d54020600d0001d11500390700040301180e2801c5803c0380b041300c0300005016070b241203650b54050f0044842401e5501700d05c0c0104004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 845797203 1250 845795953 845795959
    0x705030c0306120a052e06080a020d0c0315020d0b100e2809051501020304080304180f09050706021c14030c12191109031009080d0c050c07090b 63
    0x1180c1ea46000d0041c291000c0d00210303e079104080305400130800501c4400c0c40d84141408090115864a848144d51030604045031035151800104005000000c130380480d40ba54100c4014080181505010610030301c0740d040980804101300f420b815414841c7e0050070b41444e51001800010b03560410020151408605c00740410b242078070046445c5400502c07100c03d044540d252410150098040b403509040c81d42003c0c407000c1d0f4401c207000040c1c9101c1e42201c03e2690910003107103000d0900500c0c07600d0b401a40701d000c1d0311110340084145034038110740121401d41c6000b14100000003407410401e5440c4842c0c0b1070000980104866407082e1680c00b00350500490303258403006840101c80b00e210005902c020407042d2000e8040c04a030080c0300707009188074043d01150522485141c07200d195070044030710f081503020070b29004004942041d00c0200b40d080c400c003106800014000d07400d003032420322442030501e545050307464403000c60750040d040000361030704c0c00074a011100b800341c03500755038402c50b1294590554 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 845798453 1250 845797203 845797207
    0x9060a0207080105360f011a0a08030f0423180f0a060b27120616180527010603020a11071202091305070308030f1e01052103030a0506090705030c 64
    0x6200c04e040000001705d94158045580106000d5182070846411010450118203180d02c00040361500e110210040c000d0340b80034500d42100304517016054030a52065140703451141d0555078000d05070000100f044200a02585041c0c101d403100e958040b8011140d00f41441400c0003c03070180c413214441c41c415141e00341070051501440c4180d211507a500c07031003015401d00d8072494a0f010340c2c0741c40b00844a110707400401044035040540b403000362403000d200a1000c0012184185a4900107640c11804440702919582d069110410010a21040004a000740e01100c0340000030850f43c1940140000d49803a610003d102c40990340c0f41317440303409603ca041010841a070341280075140c412051904443c50310745040e603001c4195107040c10319400c2c0c0d206030340355103010041140d28581503c0382a4880440241c014103c0c9000204035441181030150700d00540d2454054042070001c800c07000d140c5640c0b901125101e282501e04100505003c840260007810240d0105150500600030349002e90f4801805038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 845799703 1250 845798453 845798521
    0x70905061b0307302d050c010e0d0f0504080d05160f060c0f0e03060f070528090b13050420070609050105090a0f0b04030509060a0207080105 62
    0x801004010318a05100c0c0000c00c0401c001900340000e013421401400001004d100c14410401c019110319440b400900052150054078507401c04442d0114201c00d0301c09451101d90308000f103885020b41054010741d0340ca010f20a201c40000000c4400f40d0384402d699402441c1e603503180071100e9018901c6111080d0340f0031050403001d20701407409001c5100c0d6040301e45070455510303250340d0b0000b0756020054072650b030340e840314842041d4002c0001e02d01d07282c07a0501c04040c2000801180e59043c004003881600c86030800441c41c1030b44035208983c0c41c506464240445106403062130015000b80c81404802b01d607407040002000c02c42c02060b04c51b604048039665030781a16200c01d205c09043c1420f050f07000c1e8028110003200e611030610250002502410000a4410003071400074211980a8100c8050381d00181112000400841075215016446020b40400b9101c1e881c082c0c4245c01408803081d071021021540072402680042c41800300c0300c282009000540f100c0c03c2148040040c02d1941000c01c0c0505109 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 845800953 1250 845799703 845799727
    0x536061303050726070c080d030e060402010804060b03030d0b0a0e011505180405012606010f03020f04060e090f01060b040b0d0c181e050901120b07020c03121207090506 74
    0x564040d1000000c15003072042c4000c010300c103607000c058203d82c41b140baa4003d01c0f4841041100080000190a08000c1000c20f50310300c6070f60b60b200070710007030401030f0400c0040d08020301c0d40c021550036907024048989075600701c6102c0c00a807070f41340780c103038018070000d0000588011100c0386c0d5412503480080281e4112113003002150130b60300040a03032007041c506556003002d58035603101d254002c100c12404c4010507031141080705540801c01e090319855a1195005005c20075141c0c209000f100c1e4111015480320b00c408010a01806c3c41340e2102c01500005e100300800000046030203c4a200184000c108064a0312051a405e0266004942c04480140b00d2030a503040a98000780428919044c141c80b0300685040c0e6480c4481e80380c0000c000c91001070040b504940d8050326040c0a40012104804658180581020008440705001d170558845001003110b10340240013030006001c010741a0b91102c1d51440c07416003103901c143e40c0d282601c402c85000895a501c5061030034184d0f000148a5880d10440111b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 845802203 1250 845800953 845800973
    0x3010c090e0c19120507170c16051b0108090d0903021c12020c01030b04180204270f0b07030b10050d020405120f070b040b03040605360613030507 64
    0xc0c00e490404003c82c4551089004070035804128070303500e030741107a0001d2410200b91a40076103141c0a00400348030141e018149000400d6200703001c2c0700400d0301c2d0030fa08404145450800b281c0603000d4040d110109001107480441965038003002c1e21784004907118054a0fa81e5401d221001c1400154030354001e1005113012512100c1c508904140184614944e4455042d240b60b032071407032409680104400e02095030140541d0113000d4044600f0061206910b0705c1804190803004002d100d40d43c0c400040104070760f0000000f138501c4a160450314101f03041c0c80c01c1c0e0b14070003103100190380e01c140d0f01001445107480b07030241070802d44000d4012010f4040d05c90042c0c0321034110001d180f40c450380a03c004500ea0b140d13150f032110b030720300b100d00205203c08405561a041c0b2115400c1209090020007043c031015084200700c030b800c103511400009240d5144801f003080d08000811040000307100445800204441c4000d4aa130070644000b602e5860321003408050300c400423040d0060218a01780404804100c0c0101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 845803453 1250 845802203 845802211
    0x102070c120605281805300c070504150803030f1005040b030a060e071a031e060303031602070b16021206281112010303030615050d0b151603080603010c090e 69
    0x2817910b450340b2807641d4450a0440507080e45da084c0c0d1402440419110800360400036500d40c5041d0145005101038070303036488085500078a40520345824513184030800040c10040140000c0d8141c0313860b42840e14552400175130507203442c001385400740004074003880e00b4891428000c1c1c0080003000c0040a039a070303c00107010780ca2921413040c0660f010014030b414030306400e0700c4016514058240e4a15003e00075551210120130074400d41c4e031030308041040315140001102e400241d94080350307a090103005012460b0039401c0e002041c1c00c06000c620f10105c6c41c0049241c0c8020b9100312404500d0306003e50010f59200000c5800d01d001c69880c030740e1400c11002e101044511000380c0c100c0400e000c503d6202100c240c0d448581c82e0101c0c01400401001419803511405000d000c0404240707c1e10f03a102c0e1001001ca000741d00a045a0540e01c004079405645c5c0c0c0094a00c001a58595054468520b071039125000d00880700f06801044a8500103035448c5810321504a41d1100c0341ca4000b078140c10241502d8a40d10010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 845804703 1250 845803453 845803481
    0x140106180306020406020c1906200f1501090c140f0f1908091902030a082107050c150c12070912050307031d1003020c0102070c12060528 60
    0x1200c0072010400d40d00080c0040e10864004120342004001031210800014400e000361981244040c032003581c0c07048040030300404440f4405425583c0301c0d04203080c140c1800111501d1320400040242c02e886014100b412603031044000c11000801e000141ca0461300305144400d800c6080044c2000f0380c1100303001d014850b000030751650a14a115810b05458045801340602040d0903038104040c444d010000c01041394075841c8004088030f15035001ca640c4401401000b0180f1002140020b29900502d11006032000441112030031800c2c400c0c006840c541c819688000c15000360000906c05050403580c0c00d0007200700880c0765140821011003980c241c90060000c208101d5041c2000803070005110f00715031164021400383d560341031503180107080c5080b4015400080310f241030354000241d4503c41041c812203294103026982c5d1966121081c024820030200900c4c92510b1080812412420058110b40c02e216560800041c4c07540203c60b252543d00020480c500482c403803002045812030b400810070f0080b80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 845805953 1250 845804703 845804747
    0x5160605040b25083c010b0403030f0503150d0309030506010b12040f02060f0a080105040b100e0d05010b12161a0703050a051b0a0203011a062209060f090e01140106 72
    0x3a103070b0013229800f2034008851400c0c020304e40c50302c45d016a489150042501140280ca0503103580c1d0040e280074504100c11003800b40200002d500c039034a510170a54500002402280c45020500c0d014200302650700095034a481144000708400034000d04440c0c41d0114114400c0d85135681da52001561a480801280c0264050200d140706041076800341030a40b42c2901c811205604040620040380d12981c0003501c03031404401c186403500d8001a00b05416801a01d00900c4007500741803103805000c220495a070440e01061700100c18401c0403d06604907925041088401c40e0340701001001d45000070364040c1482410001c1c100040d0040d00100784441e480c0c200f050030f01c02c002441d440d980c039600d10582030355086214074404515080c41001850464003004012201d000787c04150b541c042d14076030080c502c10110305d40c0800e0b80400c000d0002030000d0401400380e603440d1030480c0398203d241e1048551a50500705d80c6101101c045c01688500e10b22280d000c902a840c04400b201d50004c2000d2095644900f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 845807203 1250 845805953 845805991
    0x140c070305071827060e120c2401270f2313110d0305270a060206092d01060803090a0b1309020a05160605040b2508 51
    0x2c0c0b00140061051098441590402400c00e00c2510082c200e500e0310300042681d0346094200001009061a4000200280400c440c469240c40c2c03950700740b52840301900104013107101140c00100e0050907402c64890050400b0300c66007032200d03400c0070f002e6010014034401c103c0c00703010f001f80200850740c0003091002c0b030b00400405507041110b000c0c02c00610040d8044500c03811511501c0302c25500700a110a10000040c0640c6130341100c0b18801640300e00c50302642d04004249482402602c0650703a145203202603410740074001008000141c00034034000e04010b20001429800031501d64400c0d40c05201030a03854035220f1003040f100802480c464070066158101440141091080c1000b5103d004011a40c8868800c10020301900a83c48030803485400c0008120310f84110501108403111600f000d030f01c1e0550488251100e0040041c501003810600b5a61010b00c5800d410203405a40102d804440c241c07200c010400303140f12814800c06081c403003410f04621062095400a40c44802c03003900d03404440c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 845808453 1250 845807203 845807213
    0x151d0a02090c0421060c02030a021e0708010f05010f0510020d081e0403020610090e0307110f13020405010306060806011d030f01060303121109011e05040b0a030c020c040b01140c0703 80
    0xd03141c105450500300b82d40f84c59040100f07500c104c460490340347c001181005410306000356140040180c01003a020684c0c0c401071002c2080044001801103c0c0080c002d0001128440005150074440e20240c40320100c070018035403d01a00c1e0754900d800380e6000c1c02c0742d0f1070581c4040c0c0e50080d0282c6203072403100d604012200c0900300203000e9805940b190740500458284002c240101c4d44e80c42d04007004461400c12a00b82c1c110700042150041640b00003a05200c0c01813000048445149201c401e40103100c0ca544504a100300740c0c010403e840e82600e0400416403228012220702c0c03403c07102d0743d011aa20151101c190301022040030480c100050480300302c5682d00c5805800d4583d01da108402050428105050841040c0100b81c80c01e044086000e040c4070086000800c0b4443c8407000c4d0715562a20803041d181540b1400c200ca01406121040c9540d4100d902e40c020000d100300c440780e01c0140600c04038804949414054000303503043c140d59000341c1c001c1d4440c2235040342d808281104943e124544000000032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 845809703 1250 845808453 845808479
    0x8070f020604031506060f0507031d040207081c050402060906070c0810020a0305060d0c030b0702011b0c060f060e06120307020a060206091603031b020f030109151d0a02090c04 77
    0x41c0300d04600784a50100042c1c040c1541c43d186c02c9841400804901c01c900c00d5488000c0d91450703501880d0841641560030510003200c00300356013880e00607000155070740078000000010031215045d000c3c041651103180d04440b08031641030728002d42c401010090034030300382750070360141c0000c9018178403214144d0354407503009203044211461207031859008601c100c50640c040c03040e01d911460039140ca25003054a5a600d1102048902004011281c3d10f004503803000e00c00d6100d503030028603109003044080d210081c0609401e1141c1e00840c0c0c2c2a00b0b2200c54481040140101d000f251f0161b0680c1034561100030800030380ca248490b0704410f03131005111003005a03450462010080c806500604080d00303000c0715a42c10440c0307417a203480b85840b01034000c00000380d110300036100005c40842c00c02d0845007240b0000e90003229000b0300c80d0f030541c2403440c418113001201700411a1400c0c1400c0820482c0c8052135049126500400c9000a5401c00881c41005d0308108031500e1380700ca1500811840c00da10f44030104440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 845810953 1250 845809703 845809709
    0xf15090309050a09020c030d240815070201180206030613050a0c1e050301120206040330091d0604090f05010c02010b04061512060801061415030105090408070f020604 73
    0x41c000c07a020801401c0c2200c010003d4042d6190642c81c04000018590f81c034401c80680c156480d981c7c0c02400003a01511001500510190741d01424032662106600c1c1e444140004448040802d1300108007894014842d09080c42800d002400c0140c0c0d054080218540000301155041440310040e201510780301d2141070b02c21190030b6400181083e60040c000c0a440c1c00040c4e04a490408003a01247c260f00542a40d0446540358441d0710705164030700c0800c075140550340c030050400c9084070082c41d1003c681420740301000780f800c895441017100c0c0307141121410f04510546818100c0340001e030300381c2c0749801f080d994803881c090030100d4662459070ba01055480f0119080d58265511801000d0351a428000c001129a00312001d0182500300070313000c072161038040740365014048251010500c0e071500743c1140d00100101d0300200a81075561515900404503940103500ca80d00d2011880c0c010302c2e4001c1a00c0c140e840249c0106000d80d680d9171000b82d0369118000c21381d0041b8505e8101e0f001655041c0041003d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 845812203 1250 845810953 845810957
    0x10c050f070f09050c0403081b010603020d03021b191e17150604050408030f060d06021b060f0906010510141c0f09031d12070e070206010b04060206040f150903 70
    0x304a103010900c3d4211900540941d1458008010401c0481e8003602581c002c0301c00300c0d8100c1031140c8549909401003210f648002d410840d586031010925070003294062100e0b801d400400190052502007120741607200c51030101d441c46040c0d0510a81c811f403e204510500d0113800c01040b5070b183c0c4000340603440c0764880c1140d00da0100551400b52660702081d10b030080819a000e020b41e080c66a107440490100610201d0300d00440000105144c0d9054408581c9582104086503140380e140b415502722072164450380154403071a80426402683c801c002c13403103440d403000504196428681003189600f082540d940400c4940c80c0c4c00c55400c034101004281d40050a907400241d0406850072b5400c2d0382e413009184101c40d18010f0240c1c0440c0c4c001c241d103148000b018044001c4214141d0001d500f114030307203001035031510440501180c4c02030728002030350159860f0740031255182e031b031030aa02c8903034401c3e03009a00043c4c01a0011030000703030803407055200192141117540018441941118103da112107410b40c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 845813453 1250 845812203 845812229
    0x6080616031508070303110c010210050c092805060705060a0b01180e0f180a1506090906050403110613020f01030e0f06060a080a031709030c0d0e031509060402010c050f07 75
    0x41016044940e100c7c01500000c09001000c20260010391180b1004404541c25038940f0000f500c451448011100599401410408900e40000306000000c100c0d000548101c40460f10220310b62400c1000d0380c40050344a030041c200c42d038449130504003402c0424859410301012603079035111b9000960f0750394082e01200503980c09a1901c06c46900d43c295003c1c0038880c0480310481c8410191601040049240d9003191213590f21080d222a010002c12080e88544d000c1c5103030407a880d0400007250002c5010700d000340d031005031404030201c605454000907650030300c00c52800c034100c0c00142050700b0010310040050500041103080d0070841803c118400d400240303a504441c1c01c00c410b6190040f980030107064000024110100304e540c0140c01000560350040c400c00c50640022064001081120f0140c0034441c00d980402080c120080d0070031000034205446801140b008059480100c18002d1140420384000e0201f5103c0d0b0f001035817550904c0e03405640c207000d40300c03030342202640c03c04c140b000038070810301046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 845814703 1250 845813453 845813459
    0x301271101110a210e0105030a0b210105040c0605041503181a06090901110a050d020403060e06041502070308150109150c0302060114010801271503060b040608061603150807 76
    0x9003480c80342c4070284041c000040d0b45080d450b680081902e510080427000082c079101d0742d100240c0140342225403034a1010074002e41d601c1114041d085035004501c145c0600a07055100d100c1600e19000314050000325034220554100c0d824480d401494010790000702084503415962182400d82c10042030404d030b128248005d1101b54245045021340c000d100400810045c6080081480140b0855001004110b00444c0c80d80f00d012144e41240c00841c0d00c090704016100c06c01103100d84400045400340c590041c08039840d10b04a409008460b105a4143d07110f00441c0c0e11000c050604100c100356181c100a101000031500d00030400314600a000f4a031683d004480c036a01d0000c2c03401d13005030401c0030304246902901d000761345c214401c075054441550462480302c040140441040081800c1c1c0d10a550501c5c0e80d0009050043c00030300152401003e003404016039010520003610810710603d40b031680b0180c0040e40c6c0184003902d4610b07000c02450003003070001c0100003000008103140c10003071040c1c000802c20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 845815953 1250 845814703 845814743
    0xf0b1902180f10020309040e15070806030d050a0c0305030406140403020c040e0c1806011404060503161107090506030102120c03151c030f050f0a030b0301271101110a 73
    0x202801682150b08a0303c80041c100003c0d00d034055500b0b05406247c5503c0164446041072081902e440d4809180c800c803450a10801407065202b600e606000b400740e82d900c144228440d5080342d501142e00d445128411402d070741c0803500c84d03100810036540783c2d55031580c50703038103444000b0880c4c05a40698001c0c145500c0c003108101c2125090034140240c0d0b4010b0b40d060000d51205c0c040703204010504001c030682680c0c0e800060344e00303021181d00c045800030000303404550181c01002844c014603058603805c603401d0682801360745200c1410036134800780d4010b4130708001a5541e038000c0d960148010300054286010110941c90205080d220582060700203c1040482c1c1120500882046000c4411950031306c820500300b180c00341360300c0c1e0140401c110681c071810118000c90444034016880c2e40c2080da00c0c61a203100400410341e40245505c60350030a9030281c041104049800507e44440b40941c2c1104d0b0160307101d00621010880a0f0b050000d4000c07040e844070004d011011080d801601504c3d09004100c0712 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 845817203 1250 845815953 845815969
    0x6060504050a0b0a050906122e141503070f0806010e0609041a0402010903020915040c2309030c0301140103111e0603041a0a0c0801120f0b190218 64
    0xe0580700714030f425001c0075603943d460007040c116142503440d8569500c0d498041842c815110803000081d100c0c01842424200700000c0e0404072034100802c0c0d18400440c00ca0301c6055852104d11012288000780209464801981d91040100c0700142201c004075034488007062601b00c240d02c40d1649030040d40042103000d03d030040c5030358045400c40d05280a45031a43e1215006000c1000d1480076846c850006411640030308600009550000e28104040c03602082c3c10004483d00c50415006904044030004124015823000c00003003200c14114031080c41c041040c0e1b11036082805120f234140310b401803101c80d44c0c03000e108021a02184840640c1071307604505040152071040e052041c000d40020110b824140e62410a50004940484103150389480d9810091684495030541b0001d82d50040240400e010700c40d40510700d04220f5441c1c01d0203e0781c1e241a0040c01001ca01070180115455081c040700007055140515809000c0f002c00c1d503521010b0707400030812604848051113801c0e030380340b28070f081c1c41c0780c2425 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 845818453 1250 845817203 845817211
    0xd030209041a0306040b040f0501110c100c090b070f0b010e07110303070801050909010e060108030c0d030504050d03051801060b07020a0b03062407060510030b060316300606050405 79
    0x19850444841c0881c0d541c1c2c4c0d00400180c034030785004010404014503501450410764000e8020b01a03600a110024903552049200c04c07140c1c81203800c20204046180905c0c240081d054030350340e40161800c40000d0305a40320400490b0460484521640003864180080d4003824440e521030a480c0b80000b4042d003d4030a07140c400c00345034404d000700903001c0d41c0400e14078155001612060f17a10348900d002640940418050043d0502a050003c40c0300e200c000080d000500103081110004291900c1c190212101640c2c041d02c650011090201140d02030b410441e00603445248407400b81c0010301e01d0f50300310b0745d481c3c0240384405070026001c4254074000c050b44002d0090010840d00d1030400000040543d41290741d841080e61800010f2a00d2034401010ba07100240c00c000c040c0300d10700e4800c40030350404000d80000c840148001c0701045440c20b0000d80b10708140c0e082a12202c4a9041c04044404003400701041d8030180e29451054609110b00ca00b6040b0f158418003000c00c629061004120540d64014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 845819703 1250 845818453 845818481
    0x227010506120106050d090f050a150207030503010509060d0203070602060613020301320402130510170a0509071203021e010c0507110f0604030f06050705090108040308060109080d03020904 83
    0x20120107280048400b0081c1118010300300705903908440c40c2118040e01c100700003d448086600303400c0040c0400480d01040d8184641e801d01000502e045890702280101030300a000140b0034030061007142411030006802103001028141958617950001e407900915401800068102c10113014040c02c01c8040190002c22882095046606040d07814031404c050401c9042c0705254014000044840456400c50251000d00f06664428001c00e140f000031206e44113448c0200e1910350410041c41c030030104102190101c00c00921562115804d100c00b920001e840030316103020310000000d40d81d40d04802601043d1085c1c001d401c404806105003403000d2801c2c54040c1d002d0341031002c0041c486910908592209500001d84889903140070007007110700b590000141d81240c40010040207020019180c4168184038180501c100e50300c50b241241c05000d88100140403a03054004103001901070b2007070541c040010715019100d6540c450b07a091074401c01800941c04264001508681410140151201c00c00c440d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 845820953 1250 845819703 845819707
    0xa02030d1404030f12061802040f0e3606071e0807050f0c0309030712021014030a0e0c03011104060306120213020c160603020a090e1006080703090227010506 69
    0x240c50207004440d081c8401030421043e248001200d1502e540040094501c00fa4011f0f00300003000d048100a40c010700460344c0050003000c0024243d8100c074074040c880c034070303800c110500c01400e001d09900c1242c84800d070711690300c103800030b21050754420840300c0e1042181c1d540701051820b5290082203900d66a07000c0c802000b050004000c0c2c016000801ca409039500084026035801c00340545501354025800c209034140588440010091006110940c207903008482403803001c1d800100640340684503d60003030407035206100082d41d0000a1384041d03440b0349a0303005d0b0341071400382c04c0000b400c40d00305d0085840140400718050082540c10300c6903501401d01140c4c108505441d079000a1290a400300d1117520301ea80004283c207840b1800d21681040140500600d2a62902c1324000b6010390080a2640c0c0015000080000c444015442c03560262043c21340f8140c5c1c1c0c0c0d00b454411941604010314140130300d622810180010f840e101c5a001c0e00c106030180c10895086049030040942c181039004030300c500d4003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 845822203 1250 845820953 845820961
    0x503040b070605150d17030a15031b0b040e01031b080d03090b0c04050102100203040f170c0c0a031e11360405031603210516090f06140903030a02030d14 67
    0x4020540441c840d1b0b50f5040c54a0356074029115018100306c0303103400030b01114400700004118400c540d60200d040c0160909468946403100f0b000700340074a108042050344054010800b1138818161401c0c17200c084910300b007210b5140c2c0040c42c40c10f00c0c2e541c940c000003a6600e40b03401c10b11416500e040e4100c00c1d6405003d01e400e03d0710000070760341c00c0b07045209070341b007580000820108040000f545200c02e070b02c1580c000003480200c0c0d048606803c018050715050180312840c0c1110326003010f0718826280c0c03007224680b0440c802c00e0003d003c5d408501003240d20441c808080000c81c1d0b10506240c0341111800301540b000e0200314140100382d001824006070f07052484c07082c4000100044180e030141407109420740c0c0c6001003420103c88100c8040203440c41105002d1650f11034600d581c0100b0f1040030a8100e078011002c03041c600316880c80b00b0b44620042c00c80002d80c14010755100d08141e048504000d11250700b0581800002400c1d0f5000b010748501503131000a8545d00036055001c0c4002d40d920302c1a0070070141c50 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 845823453 1250 845822203 845822213
    0x120e031b19020f04020d09150501050301060e0106201603020109080a0b040807050c1011010b030d0203030a020c1f06050102100209091b0c101e061a03040503040b070605150d 76
    0xc0781080c000d1103942c6aa660381100c0d15164190b85c800400a041031001c1a41c90a01200040002c16005d8005040400125030f605050207510105c42c0c0c1450081156840d006084440e520803034a40a01d8959000100281041c101319508a403000400182c003154a1880007501405035544141040c0d04030f58448004101a111940e0b130042e0014001d5a6803c514030b0880c0c00c00710b50407040d903407107071440400b180015030180c400c608070308085000308010303072140c02019590852400c5130001a40200001140000340d074019001100101741109c5207484402c0860090600640c4c01c102c0c00c0750750380d004120540e4100210311071380030702001c110318210a800204a00f102c1c0103103100710b411039425520211a18030380c00c40d01e2b49040c0b0021f40740100c0030b030200c0c0c3c0c001d4601840302a8180d2201c0f2550411556a4404c1e40f048a003d60403440144110f0760140400e60001017045d10300e800280800070721948000020801c080c440c0b6000901c510303040348880c0c59050b040640702d001d0b03242c601d50803001071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 845824703 1250 845823453 845823493
    0x7061724061306170108010b10120e100e06060915040b0a0e100602060601020309090412050903061f0b0c0c010c06110d0b030607050a0f0e01120e031b 66
    0xd80c0004610a000d0008408900c0714868030800308030b030a82224000420303550152414103c9002c1c002c1080060340e03148402c0d42600c0441c544a0b40c402c0d140c0d166180260b006001301410031038808030100c0c1c04600e444403a414031102c2500b9204007600c540c82c078080c1c000709100391a0b100d40c040302c020003142071580c0f65036002110082a10300882c2d031130002d8001a0340d410744410040040d032040324180d00d01710700d461010545038070a10002d031140e2404905c8a60021044d9490358402500075040760f0b94035200c009005880c040b50900b48882040b083d2882e803004c0c41114814030b00d007ca000180004214502040c1e061540400400c40c0148502082c050011841c80c503041c0b000d1820a2074401c01d0300b4020010b0070025019400c3e07200001c0c070040424040e81045d0036041084042c0c904a0b81e030940250751354802c0310403050000d4550724801e0380c00b90286084100300c00043c0343c51804913080b1050001142c140410320007080d4000306050b034400c043e2614140100b0700c01405044144a5888019007174 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 845825953 1250 845824703 845824741
    0x311100c0c0609050114010b09031b1e06040503010e0304240503010303120b040c260c030f040807080414101403160201020f180108220303020306061b070617 69
    0xca0f8031a00c0c0001448002d4010031590a44020800304950f520038440005078000c1b205203000c1d010b01040d5418134030130304030985000c0101800b101e50221a036540000170b001280c50a039030024040c031011441e901d0920984d4403034003c0c2002550303500c2c240070711410340c106802041380982140c003041f40b40d20f40c0c3c020141c0b41103a5050074280b090040342038a42003c1c1c02e00d00701003034015251134250340740c030348d401003e01e065409051400c242600010030a4a030781141102e0f0401c0390b803400c00100b400303000303100030b0703958042c2c040e0456608002c8141d803607000d56030251f485081000da02c121214558640a08002140007072820607071001d590b61003903000180001000702c041b40720344521b041c600d64000c1d0120340001c5003080e01d035075690084242c1c640a0702c8807211010300013002000000c14500265058500c02403259041f40703901c4a056a00320060b41c80200a19040f08051025601900e108030341e14244c0c43d4030001801410341080401408041d0b00e0003d8084107880c0018030030440141c004541003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 845827203 1250 845825953 845825963
    0x10917030612030412030c141c03141b0c03160602030a0506030c0f040b010504050d0501150803180d1a040605070f0e0f13150801020307030605040b032e090311100c0c 73
    0x4800c0300d606225001003900c1d0b6022008d07000b091201c0d81803504001c6240741c0c0d94504e031401c1001d1303d241a505105c5402c12210580000b401d8141e11040d81c41407070140c61001c5031802120315111214450b260004510f50003110456004014031161a4a41c000d1541c0f0440c2a40141081c1d64407000003094456640d00c2c41d40105d81e1500c04094627440740041794041c1c24058003648c04e401c0030b40381c114020200e211900855410f48040494003420200072111100711010448c10b40d03904400c10007120b0740c04c4180440b107801601c4000a09503d442d074819110354000c1e00700041900c0c1c0072030050106104801880d003003003814401d14030242d961100e581105036007611040b04150301c07480c0780002004c0600228034660015500001d40820540095220703a589139400d000d40c40d0388601303000c1a501d50003c0c540e419040b400c44c00e00103005020f40c10440c6484007814845141c0306140344030464200c01b00036000907503c0088900459010841706106100001c0100040028500010842a06003e000b01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 845828453 1250 845827203 845827217
    0x120312110a21020f0c070e06010c02030717030702130f060e01050d03120908070f1202120901030c03090b090709060506160f0548010815010201091703061203041203 72
    0x1850750b00b64141c40a4640d000e1105075100c02c0d1107486950b61215100d80d104541e8140d0000d85654070601c1e5410392194040c000702407032030400c2c4002102e0200c80507540075901c414406040940e4944008421210140b40300040500405103000240c410035040034405025050041015450380400383c1c0d05540c142c1381180c41c0c00c0c4e250303450101900032030401130041c0380f001c1106400d22084046035101107104405044249401400903629405018507210100f281031103012041c0d4041d42050300043c003140b80005526040d03640724a141101541c030107406900c064000d020052035403107140050441102c0f0076040c000c0910300c10352a01c0e400b9900802c4c104002d00010204081084003161070050008c2940103100e10121041d0500000604107401d48905102c6a01c034140b40e400c40c000f0460103030f669008a650b4010300040304105d0018040c1150350b110020004100004074956042c01c541e20855524207241c010003004602c4101070f00b00c1908100700403c0000c1c41c0c0d24078080d1195044c00c10308 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 845829703 1250 845828453 845828507
    0x91407230918010312080f04050703031b0218012108070f0807050619050a02070b0106050a09030c180b1c17090d0302011d0a05060f040c120312110a 65
    0x800b080444032610b0780c0e00c0c1a25001008001000001c558003180365038420398166203c40c0381d403482100680303010b0b003260448101070010070b00c90a43c034688490040c00300200d1406660218003c2e0650201407041420524010712108009502543c642c44587e040030001c0703c269143d5480a10401c1401001b00a01d2400101003000c02e0f8284d03007401da000fa003510300350702e072402c8031100d403410640400914500e03060000c1d44020191003920074041d00038000d040140e007401da00ba101640641c020409200b880c200020000d8010b40141001e0300c914103441702e00081c4400c01034195400e0141c40f03403284000e000d02c170310141e02c42c0c0942d84981350000051020082c01036100d0a95101e0700d10407a82140c008001942855015000318003e03581c400d241c040c20300810726103151140700c9020000c0080c0c0100e40490500f0441d0100709800600580aa00d030940d51001e10062415880c04110082649100503070790300b0900e84101c0145079802003881c0d20384245030400821205003404440001054407501c0c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 845830953 1250 845829703 845829709
    0x20c060f0903120d02040306060e040f0201030c1202041e050108070215040318030501090b010902041503050415232a160c0603020d15060e090901090b010914072309 72
    0x401c940043c4500d6a8802200d0301c1c1601a45c05808150b41e418140400014040448a280d900c40c070740080c8070b04c101540542c011405080e59504a00821289615014840e81144001c1006140d81c001d0091300344d0540070000c00800c41c1d40e0025062012002c10080304503004988a410414000031041007581c60307180607103080280b4420b0003009452640d0100c10000b05602000e0918010115441c0a07a0307266090800e80c441c1e030042d2101c0025040d81623400500a4000c0c0781c00903c07611910605c0081035000350111200da0002c4c050b8003015600022800300a0380c205504003d0340c666094890780a4501c61510011003800f07403102d22000290b841c81c000d582e0010940031039003c00366814003a030b9094018040c1d08040d10201c1d4483c5006010542c41026503908000c50780580ca0346c400c107004520030400000c81c0100318010654032072200c94001000d882d4640d01800801000140d00440303a406504840c1c0000e002400780210325816101c2c031044c4203465240400c0c0c007056181d4800002000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 845832203 1250 845830953 845830963
    0xc01110102070b1605041d090115051e0f0d0506191404030c020d1203050901060b07020d03110717031201050102010e150a0f06030507060314130f080702031504020f01020c060f0903 79
    0x8142050b911000d040c0c00402652000070340554048c600a001c504510748100340620340c2481344981c808400041d200c1c1200950142c40c850310301c01446001d01c0000140807442c0e0064481c4c04a6041c0c208000700424410301207100c40381c051101c00104022070384003103c1da43c0103102038000b5007481100303600481103503a031010603890680c1c82880c035206044035100160240a003640d0b07000065080001c04a03021900c101543c0d0095001003600c2018070103502d041d40c0302454008550080e014051021403c4071082101c5030044036085c0c02160b580c2014840c000d11400c040e0042e9045904117400c40d42c01101c00910010b800008241072002525003c1c038920060400e600d107259281c0c2400340001c28043d0100700340d0129501c8d91011b122101c20507202282580088030071907075040b82c801c0b00601041c5030b100510304841c031500c84245043e4003600024505807001c20101c17a5810100e08020860a14402a0322101403c0c0000d03d41c0c490f5580000d40c103070180c6a400c581503240401ea0405136501005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 845833453 1250 845832203 845832209
    0x101a07060903080105130c050409020c0a0807051b04112a0706211407110102160b061305090a0219050a1706090604030512060d0209090c01110102070b160504 69
    0x1401c0011100038680a0325086003441461b105040c40031a00555040ca80034881100095568043c40e290030414248000e40050740c40c8541c0780314010041c000511190b00a21005019074000c00e1b541c100964800c640110000802e401613003006491000c01d120642550b104583c908800b10031415010903900c10703803403d003c60199a11849000040301034025200d00c900d2502d5050340ca200c2c014004080d0309595440400d0440003800c500016030161045410300c0610a15000261811b0750280c2035071058140c40c07034196a0050710005014840c0340c100e036034912644420809000e60312300540303d66142e0448280281c004c000380560004a0b040c06c0180002070f04001b041c03043d4441d2280c4041c4048031b601c031100c018034824000881d400340000100c4600c200c1c0e040d95800e1034151000d003130701c00a40000c0d012940046200b0301c1400181d030f808000c0b52003242c0c1d07a40108500e0f942000014a012200312641802e41d00c10082c14021805000b01543d12500350f0180ca4500c2c600305030200d0f03c1e841258 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 845834703 1250 845833453 845833463
    0xe0313181b11121e07080d0204060e1008090309060705070806010803091908060622050921040317030403020a05031206010e06032e03050a0f0b0f101a07 67
    0x141a50030241d041034a20074010160382c03c480c241403128250f21007030721406402416010a0340016040b450492000b00300451090f0398050400750b68900e1201030ba0003541014000c01c0340b400003501c060811680c9a086d00e030091501810381e0030039054941c0c49104110000303025030300000d542d6050100c10481c03030008228400403601c0030b43e5181040c5481c0d401110704203100303031084a81400f4030386945000f1807c0c1d903401400740a19407269420130001c2e5400795400c041911072034940c8440080b140c45018480e00d1540050120600c48104440301d181e908406120321000c1404140082403150004022654034005903070390300d407114102680381154440009045100000f112007400c01d010340d669004400a0b200d500424101104121190000701c0300c040d00c2c1c0307420303170011072455214281007910300f4480b46207900d1181d00d035142e050508001000c02d940d14926211514104014400c900e03900c60050156609541000903900c3e080820030f2190300d0700e2201d041c11280d21113444608a842140e401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 845835953 1250 845834703 845834741
    0x220b0609030709020306120f06010e04060e010507020d030c050408030d020705010603051f05010f0303080a240914180a030809010b04051e070e13150504021c0e031318 73
    0x43c21000040e6204548480c012404090308102041000400c4100504124068125a8241084030b800c0c0c11006009449494494412990740b5070b00307115850240485901500100c08415000790a94040905801c01c0280402c420000d905c5c02105076152a88800b002580d03072aa5820304501408442d04003400b80d000c0e0951215003400905082501e24030034810074080360783d94201680104455200150100f8990350019901d100c03a07502c42c101c40ca8000d0b00140b01500d00000c05011400690003010b03840303079101500341154403010200c55202040080124554048142c155142c002041000781805098008210000c50079080107084d00c4000d4020030440c9044c1203024420084406c018040e6206100403840300d500c01c50302c1a02800b0b0103000311076424251400000200030f0340d0104141d15983e00300120312035507180000c01c00036940c442001c035101d000c200c107030044405043c041411a8402c12910b219001c0c0b0700b01c4442114044e0456444150080300100d02402850000001030200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 845837203 1250 845835953 845835959
    0xe0f180d0c0c1e080c0316050f03280212010e0c13020d050a0b09100e01260313050a0605040f090209031603050616180308070f0b24220b06090307 64
    0x5104840080f00c4e690300485034508102c00505403200b902c3c081c030001d20100c081d414403040c1080200c14040500241c01c440310000d6561a02c3d0141003464103000a003110f1400e00400c1d843d00405100185c4541c0c0000c00440070419591031380e595000300e040c1d002d04000c4502c640b4624441d81070381c594103203241082c8603038036081d50070000a0492410140c824003092021039004000c245001054072600f5401107101e03420320904e44560180d240844902154034812400041c000b030025010a81c0320704c40b418801402d210030040c0c6c00010fa0003000811200740800c011041810b2002e001315100502c0041e504c0c6051001b10741010101c1050b2000145090400020854002036491041120440c400700c200301c0280708413010400f52807001c05107400c1c2e40013440418164001010130354440d2415001c0c10314142e49075406c0759001c0300c02140416205000080383d1604d40041001810211606140701ea003c108840c00e0891344c401000300b0558680c0d45800640b1620202c0382c0124004041f02c038a5a5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 845838453 1250 845837203 845837249
    0x31d0a080406030e0607080103060e03161407122109080d110c01140f180d08070c171b281a04060f0c0f0c0e0f180d0c0c 53
    0x44540716102c00245050702c032200488002c60344600607a92941e482029174a15158140684440480304401d4001045032410300d034001c5000d01407440c03140207071030030031000d9844031400c0a45580c08104c030102398030424400038062122100340c102003c40b03603080a4050f17a81c1140c3c3d075007850b00300f03554520030f600c2241041600440e614413145e03c03130012a00c10302c001100449607200d41c46220035078403030103000441406000d0006090341003864103541c4104030300000052441e01640380e050381c1e99140014448280447c1820718406454007401c0c0000c040114040d06941d6122441102e00d5241d45260b01500d650f240342810705032202140c3c0f4007031a03c29803881c00c000c0814611665282002c410225110342ca500c030306035011217007035880317003500d80b09100c50075641d0002710a0112a00e41e446180000042d000e44003000c060400300c08840c500f45415900d1450f0582c010380140e4460103807104049103c0390005050f05403c2482c50005013150952800b0340951405400642c4401d00c000301c50000c40c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 845839703 1250 845838453 845838457
    0x7150c020a14030a29270601050a09050712020c0c041b1e05070f06052e150e0a120b010909151d1507230307031d0a08 52
    0x9802103400700038550790340342500c0590440141c640c0e010b4001500c1c1c0e00c003080c6030321043d004110407210003548030030001e10710700e4051208642c0c3c1100003000c481c900c12540303d0a800c1030388804000c0c0040c440c550501000400504581c819403010070707140c100090328580710318141c210303e05480f5015500c840c0c114640b543c8603403100c2c0e0701d18001c901d04540f42d20640c82c444981c0c804406152205075402100d001b00740c101d00000040c007000c1c0002000361130002400d0034880c580041c0101c00015190404481d41140004400b030200301c10407901a10002c4413603000186000c8812040050090341c460920589110950506095226014030000039861891285095500f88100e098088581c0c0320b190340001c0380c0d1200700181c070f405e4010750f80a0381418a0f5000d14020407035845402508000800310701d1403c099076040001002101c01840401e94101c6800e030b8020184e0051404290140c0c140400e00c0c0c0001005602016121402d062415900750500c3c0b9001d158103050701d0b1454818141000a5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 845840953 1250 845839703 845839727
    0x20f0303071b08010c020a0b0c07021807090e16141806120f011e090c09080105090f160b031f0302090a141e040f05160602012405030304170715 63
    0x2c0d5080200c0c0604d00c600c082140c0b28102d46c84071003c9501c3c0c0b41c80d4000f664581203cac004076040b58200300c01c0070250b000d00c0350040c454800380d43c0704050542050010703000000003a0410602c40b010300003204806402440d001c1c200d03c07e655149849035001c0e0500c00d0040f07807140d40d064112000080d00080f07004905080c0e03100f4141c3c407050918a983c1d855240a5600550303011148041a45009120348a901c0d00240c003640030174600421910b0300d072000d10b821200c1c02d5551041d2036004610640700a40c05004528140400e242d50600e084c1c50701030506110f20005180000443c101031740d642030600d034030602c03d01864002d8440d020600c2c0c450b0168004105615149440a203074000140008030240c0482c0e00c0841c010055070b04c1c3ea100c0340c0c1e49800600c926101202c0758010b00d9105501c6a90501e981e1000300003c0d4000b061003041c00c51401e130803003049111000344a40d0008180243c3d1000811501152655810301030401d0402c11401d0500c010f80d041142140e005404060312180d000800c1e07081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 845842203 1250 845840953 845840969
    0x1020f1b0c240d020409050a0c0f1b03030e011107050a2d0206071a07030603020f03010204291201030b070809060402151612110f0606060304020f0303071b 68
    0xa00c41c044040015998030b54601d010028100620400400c54040241210300b041c0c84016040548a030007500c04e803841140c107403035031300d81d40c19000c019541e0110360342c00400381c103041a180d40c0d0100203030717100014000d00026091544401101d1988502507011000f0203101000b001c0c1c90740d00d41d1810b10384407a0005819130702c0d00340c068410420300c058080d100d401300c541c03c041c00725000340f241c0c02d01079941c00081017524171013000c08010248503800e00509114041540d400180300d411441040600c1c00321920850103688148014000e11040e07503440540051352040442a05070481c42c01c852a12460380414860f01a40c0000010030a011080c203009040c1078507103031000c0e03842e660400c3e9107200c200c4003c3d50200e514031040c02240322080090441d40c15407548484a841d080c0ca61500f41c050b51082900000c9000424145450080c440004528080c40103090340b42414400940c16000141019220b000c40c048200d0050b50204100c8240640c05004d000819010f01880c0f203500c001d41c825004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 845843453 1250 845842203 845842213
    0xc15010605041202090402030a1703060a0929060c012f1c24120209060a122316031104090305070f02041509090303141303030e01020f1b 60
    0xd15280a401510709940460301038403c200340715020081400c0c3c019006a03050b00031a600b20b40850300000c501c1d1340d00f071000e840043d81d03403d051040c040d1550290f0300c10001c41d032501c4800058081d240103040a40008881c7c002d600200081c000340d442e00c61074220300d03010b40c60044480c680c3c4030f24480718165440c4844440303801c041200301c0180c81d840742d14240d00c0e034840d90a800311605400d0364801d010003000c2580c010b0302240d110344545802d00b00c942050076079807811b10b8400114a440c00c465039100000352000c4400e81c0c0340c51070210410006c002c0050001c1ea0200c0d20808c24410b21503c407a0240025003141e80a030301c807032104603403140540000d480c0c0e07000b1fa003080f80f0b260615000e10307903000e0350568078285403607020b0f00c40c0000340d00c150100302d920030740721140c600069032880c2e10003001d1300818100140c20305d2185009130403956544000001c4841c1c0c0c004001c0f100b03e074000c84405598060030f0101e810458800c140e070091050280c0307400e1070080401c04811026038010340142e00420740003100c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 845844703 1250 845843453 845843459
    0x203010516054003060606030e1e16031101140c1b06090604030b0f01050a05060405010f09030b0c04030507090b09190e2b030501210f080c1501 63
    0x1c4400d18954082008200d04101e650624107003811446804010511403600380200340ca80d105000307055030150524a000001c0c00d20500c15240f0841d00142943d0508000071181c15464546a490048070329a02d40c81058081c2000030080c491000c4000048110521103a2649416019070702c0000e400c42c00907444541c2c05406200260440b03034176020010051034100207400741c0d03400c0c04c800c850742e00b038100c04140300c00b4a0907100c040181026521644e051030513480c0c00c1e4028812860160302803032060400140400881e1500011103040d03450038645048881e903061000d0320341007110741c001402450303044108028481700a003c0d1050300d21410580318125a10144001900d0400024aa001d031000b004104e407007408109002e0030401040e00403800704290403d550800c42180540d0a010100e174035004000c40e0360800f1901e070301200741400c0200d5410a20b1003c000170422890480000d548160710062041421281907a5603010000c20798440321100030903100d54400c582641c09141c480004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 845845953 1250 845844703 845844721
    0xc0c0d0e060d0e070503010212010810110d050406150f06120b0306220b07080601030e190201230f0a020d0801031205071a090a110d030e060309010219020a02030105 72
    0x80989038200821080c10708030321050b510000d02006100783c80a215040e000503498900f0300140004510b046652a00c0e9894074980d2418034030f1001d50f4100c41172400c079452202031140d40960358680e070072031400035555550b03103080030003403400740351040343d54404800000d0340c0202b0880308001e840007580c2d1040a180036501c1c0b08241c0c1e400e44441585900010000780101c4420255000c05080d00c0140940c201025180e08865000c1622030070000780ca15020410196014044d50141e0302c030b140000c107008020000b500b52955581400241000100d40d20000150056884508148d082008060740c401402020705c0680e84420403c10147c0500341a0103d80ca01404c103117812a504040c080c40481c42c0d40d0380c00c95140d40080e80c110b840602d40392050140103a01601244600045001030981c05d9a078100317090000a40d504040c8100728581d80640000e5000c0d0000040c4c410a80301552651280742e1102d0281c003501c0d0604c00ea02c003403501032100c00da03400110001558002d50080009444000d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 845847203 1250 845845953 845845967
    0x1030221090c040b1302070f0f060b03071d1f090e0a110901060503040f0323030402030129060f190c14060c07030c0c030b0a020a03060b0a020c060a030b04050c0c0d 72
    0x3985c002e0032283d25010300c214030780061045501c5a406105c265066aa49440b0244194800e540c202c0e0703140301da042c9505007000810301030010030580c444101000e40d6030f840b481400a040003405030f04191127209000801c08080701501101209000c10000690305954424101c082507560031203403c0d0040b4141009250300d41039541c1592034130b10f10781c1e841c0c03241420041101c50882c1004081c074024152940100003103141708015400d8250340341050b004041c00e403400714195201d415000c0302e040c0f8500c03040d4940b00c0c0b0341002c01c1d81c2468a48103a040300c200720780240e0146032603000b101704d58002c2d00b0346d000908050140c4900324101040305031542496030f9000c111032803010041c0803c16000841d0044070071003a03442c4595030740d50140e80c5a50b214040407905545822001da00800c40d40690754240c02a48051720007a42c0040c2030001d10325000796031303030391212046020300030008024440a119400105020501500c248818149614101c9030703079000500c501c1c1c00d8000c480c40503c5091080306 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 845848453 1250 845847203 845847221
    0x90901020c1c0c0224030403110f0601150c0302030d0c020106211e1509080a03140c1204053a0c020a03080a1b0804030309170a1101030221090c04 64
    0x740b1020f80d03580a5003800202c54204000400201042003105801c41c5480010b40c400c1d4480d64607181d83e80034400c1002e1510005d0208a02d05800c03110060107041101d201d810a00c50403890442400c1c0b0140c02c0580c11442400014900507041a0000700031907015006241100c001ea0ba058034900c91821895451007940c49c0c0061614401c4400f03402a00c01490015032410f000e070100d00600d00000380042c04840303148400301c03000d440110b560980e65405100710203000080c1902101685020181200380307114000480d01e545402001190a20100300914414010b224501c2400800d40002c403100284045050034840c22058942201c030920404001000980c00341c0303111300c00d508654820804d500300030b05401c1003200c1c040d102503508044043c07415003180214070032541c407411404d0041ca420000c1d04070000c1c60000f08a00108080001032003411103800030b108940010340c0341c0c0103e01a2290760300912221180070700310046008000b0009020310055000c4401d0015031205000503600540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 845849703 1250 845848453 845848457
    0x110d0f06050f0d03050f3106030501090c051e0705060702071a0909040204090809060409060806070509061b12040e0a0506010e01050a080a02041208040f1e061d090901020c1c 76
    0x10143c41200b18017900070b03007100c50f101d40705071540461400c10f0702c05244504005d0647e00c01d9032041000342a40620640307024003090070050151103a4044050710900c038118202c21520742caa88801154010003083d19000741e480382c2555910304203824000e503203c0903402001d65400091400b00440841903044840400c8003804440c2903503182d07020400240302e0480c0548a910b002c004408065807100000d0000d4140c0881c001203080c140b80340e0fa480c10000920341c80601104010b081c0080d500d403029580740c55800e4284070750318105014807d05081020300b000310001030100b00403403c5900303003110511500010404005c0340c1c9d5024011184921b04803101d50204000300003506100313204400e1981e00c906c0d021409807420f580ca42410040c1d40c2c01090545264202207000e220311030882c0300007030082011510f81452500d6005054164013a584034040070b00000784003190320252100801d42d03090030010300011062811400003400b0f54055014142e40b4081c507100c00d8484064071156154402803a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 845850953 1250 845849703 845849707
    0x80d110a080718120b060a0902130f1202031e03040902030f07031a010f05071b0303020f12030f01050f040e1b040b12060f09030c0106060f030507081504110d0f06050f0d0305 76
    0x3d45c50300303001c442c0302030141600681c0d100fa0100b00c282045c0000c051040b220354044207450300d8503810300c1208145410440c00c901e907000080002d0f07500000c0c40c8031040702c83d40e08812196900c0e18950b1031803050f5408007074918000310030400107003070342403440c0d00c0746815880902604009e99951405001d00800741800304080110152000c0d00c100702506c801d42c4a004032000741300001900b08103e840b194811401030b403050215240c2064180003000401028209003821802c02d030800d000b0004050150500800080c41c05c0c40c190b503240e80180c81400e10740c3c0191aa0103c04840c0c0000c002e0b06000b0403402107090442103a480c1c10103005001d56114901e0141805440d941b6100398110382c00340c410038540c0300074040c0e80340741d69082c0304034801070006403500c80d03a0300c4280c000070303007681e800501203018004040c0400c8414200e10800c0303150500200c4001030003d106040e03040e29405412442c55115140610201c14400d10743d1280060355001c56104c42c400a540081100000c0d807840018005841 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 845852203 1250 845850953 845850989
    0x11b030903121b082109070302060a1407060e07080705060d022d040905010603020f0712091a070506060d03020304030f050703080a05090901140a03080d110a080718 72
    0x241c40188880700c2d2031480e05880d09152020040000034050100781d0720448005141c41000111300080241c64015080c0300380c5a2904010f6182c40b1045484042d024600008012407078603c12444082c3c229030b005405034540c03102e420407030024004030004411a200d500384c04525000d001072800100c40300108514907040070307824020041c0d00040c6444902c4403480c041d151000342c0480c0360340e02c40c440e00c0c0740344c40c1c031140f4110041059a006a00000c20706204000d140840f07862101250a107580142a0011140420742c4c112036070005039001c150500451292442d034402840b00400e4210b000e07004541054546100704441e00a1044005001d60b00c00c1004000043c030b2000c050720228000e40640341d115035a81c4804015030700c03008403100065000107141d4145d10384004208d02604a03410115010300c203803008200d108003540400303480c40d100400c44403a1050325400c0003a00401070110944c40c0d1400c0480039000c901d090360070b200415051503291400c55520140724044580300d0707800c1684444 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 845853453 1250 845852203 845852213
    0xe0102190c020301110f22060801121103060a0606020c0a0b03181f050105030d0c2607060218012607111501030b091e030406030e0a050a030e011b030903 67
    0x21041d90100e0700341d521101200800307400300e07003e001000740d0030141c40e649244140038400c2036241b882c818601000b101d00300f880241e51001403541074403400e030340d0030722420500e041000c840e81c4401581c81e81407280b0740c01c00410790322680004041314215002c654104d12020100070704001c0da4002c14503850400d00000e03425a41c40710941d40050300000035110f501d01c0320000300b0b00c0a1210200960159100c0d0300401985c04c0800c50780c00b00d1411880e14103e01c5419070f8030b01c5c2942a050101e1603603c4c142130241411030040304100c1d1b0103d584400215500c0c0000004000301080e81520a07000c541041140d00c400c12030244668100340451410498071781d10408161000401d80e400e5403824807640c6442501c80c041090414041d50007000380ca80c0500c3e100c484207151100b1100c004c0c2c45032214084c0c10006050000a59065030041d08002c5013010300c0500c0300d450700e8000100980741c2c3c45040d03281800c2c982c00904840035083c1c203036100440d1078100b40d604e8044000c04c4000800298500c41d0801c0070031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 845854703 1250 845853453 845853467
    0x41a132a081f1d0303011e0510020a0219051201091b0b040e07030b040e0609010c050903070e090a020a0303030e0606010507081602010306080d1e0804170d02040f0b0d0e010219 77
    0x2543e03407030285402a451495641c9140c000b41c0003610174085902d0500b940c45107004504000349001c07070305030741d0641c2e54001c02501c8a183c040300070b00954146441c44848003440d44101c0117808040e00060240601a404601070100b0480c160b40104040340c15880d0fa0444503a4502600c401c481403d10700f40c548001d00c0c0300b803000285144105a528210b4a586917980d0003644007460f0414020405402c0c0318280600312001c84400760140b200402982c1b0058501268000440b0110490f840386a075500003528241104400001d43c0150341c100003004050b059488080400c030050121003c035541c820065a02d0b108101c1c024203601070601c4401c1c1085005c0f0341c2014a41c0c410701d80030410b16941d0b11000e16000d4500e5580700410881c120b011240c403440400001f426041e40342a0a960400740c8031000030822100400110480c002010b150001058045500030200e20b947c007030350260b98445040319904a013160303904040c146200e800040130140240d980202c01c800018100300e4022405072402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 845855953 1250 845854703 845854721
    0x80705040b031f0b0a0e010203210402040e0105160e0a0e01090b04112106090402150f091f1206140105180405010b030403080a0203041a132a081f 64
    0x11642d104003d2a40c1c0c07031401c0e41c0000800740000d6960310b411281402074a84c0d100c0962990443d070041c070814840a4a007110001038a000c0e40d03500e2015141d030300125000e080e01503500c40c1c5540c02c00c400c1c4107021103800c1c1710102003000c590350800a0890341c000c1012821982c8100e4000700c5403c4014002c00a550784580d00404000384005a6402003d032401e40c2c90b0488856040c2c051100710400d0a4056900411076010704101e0710903810f458a0750003e00786442e808a5250204004518004002c0c22402260f000c07900091042402804e4200c182c4e000701041901d190024a004c6103158a8026a000707010650302c1403500500709010940044505402550500340d40c0300180303403c1001c9443c1c40c46000e000c0d01c24440d04650b207242c5418041c06119028201002d02841081040b000c9a000c410340c10071034401c0b451101c5c060701c0300000c00e4055a142440500710b400c403600e00b9030785014083e03110f0040303031046c5069035011035132101c42c1500c2d41d65001000080a05e03040311740c000461954404001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 845857203 1250 845855953 845855971
    0x1050412110a0f0c1a0301210c090e010b0a09140a0c05040b03010b0d0612111c050102120a0506010203070c03140a050303280b060a03050a1b0c0b07080705040b03 71
    0x150003640b21210010b5007450f040d2240d8401c0302060141c0e241020080141c5030b0703a00486440c55150031141e81c100e401c500c090b0b42e0380074203800c06402008451540c2000500c45264280a80103c5010340340c0208000b0001c144035000b2000005110640750142c4070056043c00d034198400d81e25800b880025210031450081000310402010507080f001c0c501075400f17000046034043e180c3c0300e00380740c26040702e080d500700220041c0e000c004800080e2950480765040ca105441c90b024604000b15081d41110901500901a50011845103610341c20750b482188101e045000c00e02c050303140d407001642c4030700c114140542003050310071090002c00c140041c1010110340c0001160390ba2216516a00e0440c1c100307540d170011440084050740d4000c41e0980c80014141804401007040508500003d00300c1e1141102042c241074480001400f036000b1903000f210356000349c030300000e03030700055200040c411000000210f50036008900892007040c8600c2c40c9901c0b56070951a440d00d0541003000c4075641d41c00017408518 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 845858453 1250 845857203 845857213
    0x309010f0804020f04150b0706020c1209090a0e19080306010e0a050a0b0309150f100b0a0e0409051606090e010902030f180106050d121e05040510170411120105041211 73
    0x605500447c01040c50364000c61005844586225000c1c0c14140c4042c07804090b80410300c4400c0c07055a0383e50f1042d4000c20085400030b801d5202401c05802e164031681d01081c200d5181486400340403240006500c0f40350300342e9402e1501032540301000580309150040300d400c1502d5001c1440040c1d08000159006211102203030203040d98400c511900540860703502c070081280c1020f0140381e0758000140c40250451850345414900d040301d00800307000d50030401600c41ca4550b29010240f0100740020f41d448013010f4507202580d80c881101400c482103910850f03620100702000090101a584250b900403800000700310307030710344402c5040a2105120300500c0e019558a2900060942d503106880f6180c0348102450540f621050101500c41da000c0302c0455607900c80a650540101d82c401c0031a000e440040781d02c0d00c100e04404c4412607400101521002260b08154140014031003890001d800d0f41f9070468850b610b5a107014501400d07100c00351401032109003081901e8a40501600461203250001403c850b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 845859703 1250 845858453 845858459
    0x40b070c12060903090b070b0a0b012d09140f060a09080a050c01030c112d010f06030204240b032d0901060503010e0601030609050304170309010f0804020f0415 70
    0x11140d08010201d03005075868115808045e040441c800082010f400d5a1b0309002e115103038034000e0000288000016a66051030b00000d03030240582d5014412000b40c0e20070102a04000004072a9401e02c40d00041401a800007030410b1a5409404400f038000d0801d0710011260018400075401251041081c0700c43d6000c04102803a0401c4400b41c52801040101141940600058201c07080703020240c04201081c3c40714488028000f81e01c42013005000c004940701540c0c150300100e0381218402c0c0d0201ca5007040b400c100120b440b42c000009a074021a030820190314040c3e00801140b243c041e40c440d0b000f0f0090820441c03c0702640c0595400103884002110900d413001401c0e00d200c255204d0850700447c0b01e4240f000c41c0724248112005408207800030400c0405001d6482d40d0340d801480700074503203a1918800f8003001030901c00d907401015010501c1c0000801c02400726241e411030304540c0c0c0040e0400c0c2103507100900c075821a9004580280203060040100024080a0b0150b91040000c10f009070b0000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 845860953 1250 845859703 845859719
    0xb10081b0609030d020c1003090218190216111f080403050d05040b1005060c0c040b06190c260415030e060703020c06181207050c0a0906090b0312040b070c 68
    0x28524980b455006e041c030a8030800400c0182e0300c00c41a5801010300c1c0c1541c510040c1c43d04403008042d01508407403940f040e83e03150940b4900e01c4903592094040d0740082241c08014001844142d0424031601c041c01130000050103120340c00784003038082d806410b010350050001c41c2c0200b40d00c0d07030814000d02e001c602d080fa0082c225029980c0c00ea88c00c5503244060303810081103d420a00d40d1024100460741c1d40d10307021481803020360340c4880c800001c1c4255615056080107940d400101c0d0000401582622039240c1810400751407190480820b561046010f600790032301040f510140441d0b00c00f00c201190074282003a420710b1800400000002c02c2c51340d51100f00e111004100716551142c075940c0c0d4056501c7c038a8151807810303d140503100d08240300040190502c2e0a0300880c0b410b07000851440055150300d1a41080c2c0d181c50201112203403c01c0da1460085200c4520350400801d407900c0c20414090b903460b80c81819568600c4a08042000e0402d000512403800020010080c2500403c810b42d0a26110745403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 845862203 1250 845860953 845860963
    0x1109090703051606020607020a030504140a17031e1633050106020c0301150509041716020f010c020a05100212030a06240e061e0c0a0b10081b060903 65
    0x1001c0703010f45410041010540c1001600d600c240326101510b80607107a07640140c80c80c0901c1c0103c0c409002c0701b011401c000c1d21240c060034006c080390707a42c20071020f85509505840c2e038441c100502c01002c030140e030b075622228118115000b03014038100c4454050038503100c8004038441e1203c0c03429482070131070703000308000840300c440410807566480010340765142c540c020b8a818902039240380283d045c803410100c075041141224080307803401d403410142c955071440c080080c1445060221381e480000b0030f030a8078810050b900f44c0901c0d40b00395400b071190800c901c015a070810340e5070002540501002014441030074000b00d8490345d503440b401124014031044001903032a800491300e0101599a03290100601e440340c40d14131101400112007a646414078240040100c000304000500601c0c001945151a42c8502c0308001596500641d8a8880d18a02c0503580c075041600c9054a590340c9260100f4044000900044111070542006029501180c0103c040079860030003601e600c1481440442d0240c0c0307007404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 845863309 1106 845862203 845862223
    0xd03060e0f0c09060c0705041103090a0204090c0504060e040203010c030c1209110406060309050c121b03120406092315070c0308040b04030605010909110909070305 72
    0x2d03480181d100340308030b2581007140007400e1000101e01207002d9068a4044a0501c024004107031102000e000c25521100c0d0b0360030044800d001842c05501c0068030320b00c41d100c200d8815940788001812280c0c0d03903000c03614040c041410441140340030700c40c5100d0410032741030401050305078200c010900c00b130480140c80388070fa0ba02d40080603c050315448502c42d1a00074414000b00d80c941d4130050142400d01e0b0102c4540c0328400c01716117076150440d00c0500d025628001000300c01056124030300101030740302d00142c050080b0740941d5001d085140003080903041d40d4482c681524035200b0718070280410004011080c4c41c416150201c035964000d4104036187d840484540c4900307140c10044200701056200401c030007800103001810404010144c02201c0c0a000c0400560781d8a451000981e12138850090480150014880d001c0c60311011907a0000e007d501101c0c10030fa120340e00d0b42d00d0591514 = true := by decide +kernel

theorem cover : BRFrame.Cov 845683453 845863309 := by
  have h0 := BRFrame.cov_init 845683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 845683453 ≤ n) (h2 : n < 845863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
