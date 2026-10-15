-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4821
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:50:48.716199+00:00
-- url     : https://prove2.me/submissions/be493140-86b7-4856-980f-6f62b84c7d7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 866906474 ≤ n < 867086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 866907724 1250 866906474 866906497
    0x181e030306031623041e09050c01020102160f0206210411010f050d2412020301150806070f02010617030c0601060e0f090a02070614040b010518040b07091a 68
    0x106482c0340300040080c0e0766102e103e48016010b90010000c04031074043d000c2e076a1340070384049804d01141c1450401e40407440300e0f40300d1040da6800071307008000003030240c80781c8040300348000d40c1040c583e4031086120540310301c0010b140000040c491380440d103560f404d95a0120840c0320b258455148900307150801241210100c4030030100d01002c20185d07000f084942d904809580d1384900b062600501c0c5801824000790214066a030070035585843c6401e81c101c1400740041e04101460080389105150a440301034100243d100982a4148500300340001d00c42d034040107074130307040840002111082e80104000d401a2100704120080004601000001008440501012a07031182e80e500c4044410500010603280d0001d9111001402441e2009202e60403007622000140f0f0304106541d0030044440d10880407501c00c10030001c00041c04129906240100300603246a02da503543c00840c0c40c00b07003800a000800c55401d200214124510801402020f0801c82203101150010301c8100c003601d40084540c4003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 866908974 1250 866907724 866907733
    0x9060801080604120c1113020a031104080604031209020901062606010f1409090406061805061f0314010b0310050d0203100905160b0301240206181e03030603 69
    0x8401c1c0000580380e02c2180c20019100703000c08100000c039240d40c0c441e4010f6840020030290074855545118240190b50311f44040182e55541548002e0107070399448032105041c0741c0c02d0108000c45003010540319482507051400015852038034011000605442c0c0002c4c2d00460040300101351550400b0095880d502a010002035a031143d8014548501040b40e003980020400007c1f5444540500191300002229140440c24080201c0c0460a100c3c01201c5c165401a114501000038295120041e00e003080700080610052400d04085400e692140c0e000040b0303c000e10500200e80c0d4440d6001d09071044018548140750f503903032150b036030140e04183e40846242520900000d01498030140c0e80e00043c0e07014000d46580901074194400030018414191524060305c061811801003e09170a4081c0110b0744189459504041c20711032400341c807101100c005400f10a10b1b8071040c0d0000b40d080d40c00071a41c40d4200c2d100400030080343c00c0045e032002139004401d050480044040000c8007070352042c001a4201e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 866910224 1250 866908974 866908979
    0x180f03060204091404020d0809061b06011707141e0907030b041b0e0607080c03070303020d151815080f0609120a120209031609020304153c0c09060801 66
    0x42c07056010941c1e00075448140101500005803100000c0c0c40098001414181402135904950f44004000c11508000350800f0006105410303480500ca5401c6030ec98004240c07d07400c081c0345010160048551510a401c028000051603002e20a0030700e14980260181a46041038440580900400c0c0d00b124819410155010a8a4420f540001e0f41013039941d41d02e80d00800358014426281e00050f07041d15000303030030400b991048400f000200509880f96600580d80c215242015088504540140841c01107080c03042201c401d84564808031034204200016a58031008a4050503116641c05400c4602802d50402202030300400c500c0c0c841c5218805554444140e07140034002c511841c5042d5003c0740c2031200410801440b580030304010500a0111001cad580c1010809009030f0340c59000d84440c0d50000100400c020550940001035030100c0710905c01d605078070340007401111106ca442d131051200c40500050701d001d21049142001c0700e080d02000503442c0080010440e01e15405500041070424000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 866911474 1250 866910224 866910251
    0x4180911030d0917010f0e0307050601081203010302040b030c03100906140108061807030b0c0703020c0a0f140a030606031208090a022407330902030607180f0306020409 74
    0x52071940b62459030f554a81500341203144441518035100b480284d0350318000d0000b2082688150400050a01c0046488020515000f441d01c20160002d0f40250041010340315401108402e45e07054a41c1102c002c40d81c0e404000c0440c3c901424900315503071502c1104030f6801c0c1001ca076800a90f0710b6016803418800c862265080ca516a8001c0c0b2401c0d40507440207001a04800743d0703200000d00030500c00d05442400d0f599443c1e901c0300ca1810b9403010f84581d4000781d00070030180c0408c03844001c3c07201515001441c40c0343c403a480040c000544181c1220303c0300ca007224078040e07490318000c0025550200040103c40c2d100e080c80502401080084000300c0c9042c00030807a01c0000103400c1d0f100607801003014000042c80a1020745044145820040d0000141304403c0018800703005441d03c540c00c2d1590f84941008070024401d50881d1942d1001c500e4a054050320250b1070105a596000300141002c05c4444510b00e1101840c110b180d100303116039001e03010080304008454008004540b8040018000c030000c2d01c19 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 866912724 1250 866911474 866911483
    0x170c01050a1505091003110303070b070f0905090f040b0a0e03030a06030201181202040c0c02090a090308060f150306010203161110080c19030e01090f0506070c080a0e060418091103 79
    0x2c1d018200101740c0410800103000d00c9612400790406070940c3d09000d429500c4608500d003d807144000314450f0f0001550556019071408000d0404482d610014203184c0000c52207400040c3c030140c030301280000052400d1020390071810701c1d901c80c01c044917501d107092110003000f80355a000890016640041c480c4101007804080c0c000d5a004101c08100a4082d508000092100c10104400c2c48044003060025075a510000d6102e48200b10001c02c0701c41d880d14000380b0a102c01841c1034464094076012000e241ca600030f4514404603542051607490301d8910050340755004100040c2138502002102d923003000782000d01004190740c2078944102c0492540d00a0b1003034001251082c0c0c080340c05114a0960b000c10010050031050305050010341e085006030810700792940803101742d81000c4c414041c0381c00c00804100065109949242144014515590324601d030302c1207255060800c9142000c002d020340e0352000b01c1e001000c120b140c0ca044611041e0041003c0c214103c0c065840541e0f040c1c00f24110b040126 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 866913974 1250 866912724 866912731
    0xc04120b24030d0c05010b0a06030b0307060f17040609050703051501060302180928020702030c0409050c1e03100f1505060406030c11010c0206090d020106060c170c01050a150509 78
    0x2c010742407105040400715038031661244151241d40d00c03425404c1c240d481c0d402c0010080c20f80c0ea9804100e00c4e03643c4050500e00011a4003910401c0031021400000710b42c04010448200300710f0485845031b0311242441000b0341111f5402406500500300000208440081d946403822060f4108290981e43c03040160120701a58021410070b2030340030746032181031501c1000150700240700101c1c041908540b103040b0750402001c81e8424038040c3d001600f6810b515081048851603031045805200100181ea240364840f00d04002c0140503ca0640c80c50382005002d40082441c1c0101500b100d00711703c1c1c5001035901a04402c809c0c203101601c1e040c860712160110a088506403107000c0d0040d03140c5850f1010441c020455080030400300954007040c489110800e020381c074420040c5a0013006642401080300e401c019910035032909580c513000d8200030041c1c0014015540c07640016034a011030030164005040381c8122170649500b5403808080204040d825441034080b0344261104103034040d00c0e80d0a00110281c1513 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 866915224 1250 866913974 866913979
    0x519020a030e060f16050c012a0204021b0316020f0f011d040204080304141503130809122407030c02060a050402060f040b1e07080307080c04120b24 65
    0x110b10107250b043c0100200384500030340340000c0c034000408404204041d400d0804481c650481110007050303680c4000040c0d50035102c055506038110146000c28002e0007030220081c000d45c0c0100d5841940d042512106805a00020940350355200c0b10a0030f020f0f00600f90b4080348154141c450a58a50a010780b9400d401e20040e141c50510f400c0b01c6070962816600f08a105034416020080850000c0f01071010740003c1a0508180c110b8040d05d1040142c0c41f4400302c0c840300000b9042c0200403441481c400c1c803c01c030035007042105544800e91004180b1186c0402d503461841e202d46030003000d2100c4042c000c25040c030544050024075480d01e01049081e05d6010424200584c890b070007164140c04154030803500300d403000b4040341c54126a03442022440d04543c0c00224524000710f0b00d1110b0300c440b03d084c2c502c1d055008400718900143da507104041400041c0c070b100100010007000900b552009011903003e06050988111542524540151554000c8071141e410320614280c500c40381d4640d00d0f408040e070500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 866916474 1250 866915224 866915237
    0x21011806031112120c0105040b09010504150e0a0b0c07030207270b0621070f0c1e110405010b070213020406020a03270f050117060307050105071103010c0519020a03 72
    0x804008004070510446003840c041c0c0348504c020545010003c1501e500e040c2c00106142c6014202010780f045c008084044a0f410a01040300044103001c200b400c902d4425070018240d4030700713102e1924004807090001c154208840c14492070b01c07110300260034103e1181e42120006034030b030a000e09035a0b00d05003940688000124074101c3d40251070700480c040043c00360a0905001034001a0491007240201048500d0200f4003400501c40e40102441351416190510401c07a08003503407541100d141c0c516841082d4440024000d04001d43d41301d09201e1448010b1052055503100c6005482580c02400c0881c0708440144004901c0046c50003510226182500a400c00c0216510305072034034003680400014101c240c510010104250f040030902425000c860000d09505040000d041781160310124800e42c0c1c0150b081002d10703a0001040400d6030028070b0020b848145500d40301042e400310012043c1d055003062112944641d2103c080c112000c00c5d1b4113034002e000c03605001a40c407115581d01c00f42c001006c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 866917724 1250 866916474 866916503
    0x50c010b0d26070b07320a050c03071403030108010b0a0810020a020a0f03030c111b0f030109080409050403180f030f0825050f030421082101180603 65
    0x514501c000c6403140e0180024070f019600d907550010148216a610007084484001c0003256104102c40700400102d07920380580c5075081b8000c6141401101081810401c0005040b2800c580520a80c0e0003507034028041d030f002c0d0301d8088402d6100e400c2405110003641c078200c03040410340b5140c0030b40342c211005400a01a03c00c03520344240041d51150b11840300354070401042500080080c806c0c007912500070f80d400100c013161644000c040202820144074540c0c0300c6c15408040c030762400010301c4601d200301c4801e0301c075590600c08640500090324001e4031904001c1400100480c407508906e02c601c2c403070b07038908007181308400070241244140d00071441c1840269105000080d44094542c001c0c1e03014400050030107248444208006154a41c04815950050144d1040007000c1110200500315076019505140c10800e00d049454020760860700c00f841d03100c3c4110180903035401120507413007207440b4400c40d81c80508041c4102040a102d50505d800c1c400602c1800e911040c8160019a03034080700c0c4a0b80e0780c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 866918974 1250 866917724 866917763
    0xb04230a061d010801060e0613200f040f0803130b0325051c0b0d020d0611221208030705181f0e240711040903050c010b0d 54
    0x8400910009010340d6800010070825103680c604411a00d8590310baa281c0e40c109181582529007075800713039102034a07003001c0c8103896545402c4111501004d41d00003c1c0c945910541c00000c1141d118215544980011080b42c000820307401001502e5044110340d04980c2d503500d4255980c800ca0400280340d401c41c50050000c0150080216003161481c9110a00c0311007011200d0f000c04200000301010500c00a20f41001d10b261013415109180f0f15502040f84107252000324091140031000288200d0000c0711490402140781d010b15903040007100c0e165200d0140c58002c9a02030b0062144800881c0c028400051805129982d0081554012045030654540c0c030750507070711500b10011513501d1501201304a51030762113040940d440c01c0b02429101c0c0c00d07412842d5028020701d148002e41b90190000584080c0145589190a01108800703008903079940d10500f0070b01070b10110401d1881d8000e050400d40414107601401418030081498020001c44005808008040c00e40744030007410441074825041740d90 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 866920224 1250 866918974 866919041
    0x907080a0605100c120c020f1212030a0b010930030c050105071214090a0b06060d140403030c0810050114070203010203010b0c07060206010b0d0506270405010b04 71
    0x140380c0403001c900319859100041c00b9010300080c400000e00d2044002082c0042441c41d200b0101d814101000c4040c60340c0c02040c2c0440ca20b0301c045000b00030802440b5032a50b010040b51a00b00c0c0940c40701034807400c2ca0b00c40480a01041c507206800502c072610003042e51103800f200c601500898851110101c0b0504000720b038401c200d441c2c1607050140314031454000c01c84c01c0c0542071040c3c030203a8070703a070b484040140e407441201c4500e07244140343c2a1003000c005204000041c0400c14981201c04102181e5401d0002840c070301c6142d13800c104590410b44c0314465849001c2c04503000303d2007918184100410f203141200d081302d00b01c5038401e000090090800c4254040e0340c1c000c2c645070400020754685507950300403d00ba45d00030f900256150030005400046100d0a0012001605042c400b60440b035251550042d0a03024441d0341920313003541c81d40440c0007039607081147d541000c1134000483e100030b002180a0300c44203007158141d980e54280306251456250070300c0340d5104085070703d100b404044140a419404c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 866921474 1250 866920224 866920231
    0x1a0f0717090619030e07030201080109050c070c030605090c090f060108071101111804060501121e0e0c031b100c050f0a05031e070809040f110333090708 67
    0x1103060400050110761100e50003440c02250b003d601004148070710718010101c03108080980215001201e0600050703a000c282281154a006c030b0100f4075407101ca54114051040301002001d9200c0c01d000002000129000b16202d81d200400340c1c5c180c4001e54051050310007085902c046004000030000d0050340c0540b0700c0f147c000869281414420081030307031985c2103900d40c0c2d08010054102044c444c040f0019a4041842a517050b181446a18075100c00a05040d0750b504886103025256a10000d0690204c003070024800e4403018107004080301120620b84a4605409280c06400340c2c10400072410080320300158044000703480e100c10300361030381c100310360b000745100c4200d940c1e0155480021610008104007004140106c02a540d80ea0b1102d4000101c1860500740c51b00b000d906201410214403004150788028400b6039000c1643c192610b01400200b205500c13207401031101106003e484c80c1d0410b001840e50700c0754140c5d240e405608140008101500503d1030350f1114079280050f05492294803540d40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 866922724 1250 866921474 866921513
    0x71d01212d110d030206010e130c0b0909130c05132306010f0f090902090d020306010e06030c040203040b0601030c0207080d02030a030b0915191706011a0f07 69
    0x520400810611181c02030709840220360180000c1003014070030408410764624a0484041d07044041641c0c0180d100c0b90140304808502e01d00800183c9200040303080d458030709a0150200400984400070f98403030f41c2001c9100d6000b5440100002d020000500e03060545540001640300e6943c0b4110400413000250104808101e89580d0194552503e841890035001d031401c100c0c0800e07240c0140018000c0f0303105d91603d0208580e54520b202d2954201d0320311000e40d002040003595440304100410040c4a98100082d0103100c0d907800020003d0203a04082e005007400c40c2aa003072003e00f10204000ea000c10b9070040c01c1e000d0850b001c07404641c02507200060012a40c01520841036079041420f0a2844842655015800000f440d0040c2a0715104040d40301c442141e4034011400d10f03008040c010b400c01d41d0910b00800784030200b64491507920346008d0060903507038411b02d1044890b5070f9440e142c01085c0300708107501e640c800500341c112141c00309452500c1e500e104900c0c00c00495071030704030003a4003403244401d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 866923974 1250 866922724 866922743
    0x210127050a0b070e0d060c030c080f01184d2d030109091b0b030703090c1509140d030c0b060a0e1302030c0a050a060e0a05060c071d0121 60
    0x184c1600e440c4400c401c03550042d100003a03100300742000602901d44260b440b2080280040c01c009101ea0600d9074141507a040060454922881c80085001000c41c64070740358403814156290000c0e50170f51058044801005c50562034103212007100341d2010507002c40e49079000401442070b10743d40c44101961611314900d2100a20f800700c00440c007108658000c0c2c220001c6191900700c10f805010324943c00503e01550b4070a01b590340e516100e40e032291030202601e00010161982c940070180030201d087e2401401c0c0f008407204008071507800183c020340031485114858200340071036144901d0030250103524035405843d60702d0340031050b44d151150718000510039035000c0840310f400724008942c0b0024071b2140e041d464200d007014005004142c94035030403890b030038810101e54000b40050349860002d02d040350064240503008480c2e55001030000700700c58200796044200410394040b41c03a00080d00c5012180301c403a040340d81456014000340400303824092083c10000d4010f00e0105411020142c00d04203004840c0c90307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 866925224 1250 866923974 866923997
    0x20c190e130f150b09040803010b070606050a080304180c090303110f010204030305180d03021c0c0f0c15031a0d1b0329040c05010e210127050a0b07 65
    0xc201d891004074183e4100d40d24100005050074244109001a003084a080d00b203480c02d61340305034841c88140a6007200b0f040108001d01000100d0b00104d002d4100208003110a5444104582c0d582c1c0240c8103018202c1e1054400300107600d450311800c10300c00e900d6560180c615065803400d44403050803005004407031203024401d280d900c41c2031000d0000395100356581c584d5a103921041c00499a4003207801da2084510480c0034002907000540e019000d04001032f101000307414100d00313a51580d0241d40142182c0b80402144040040b0030a40f00b00b912050103d034600c50707201040c214202d4010707070880c6044060035a1408220703d008900c00761124412145525101c04505110031800c0e0140e108803031242c005081c081070178103010002c03402c00e007681000340301c50318050b1a0b04112024611500e41880394140541110352616440c0c0c074001d0b212003681c03c10180400d050742d8001c4c26110589040c1e0700c07051045002c5802c41070182c0f04416000801003a0b4805d040c2c0f80c681008101400000c284400078925 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 866926474 1250 866925224 866925233
    0x2030a080c03040b0c2b020a0605130206191b320109031206290703090506030f0f010e042609040c0206010911030f070f020309040603050d020c190e13 66
    0x1e1001503040d05c003800c1d40201c0000c40e81800706140c242c1d1140f0316200c86075503003a0356000400c401126003010300032840e900c452005400018180401942011000510040052800b4250381c0302c00582da503400d41222680081031545851000010314207c4202d8000b90b000c100c810701d03040c648001441120701c0604908016003118003101d4210041481c410b058407013003402c1e05ca440000c0c241c94504544003c02d1754103038aa205000a001482d038400400e202d003d1600c00c11899014110203400d255603810400c203003691a25003100d02c020b246850400126050b014110b01ea80520745c499030702079242c008040c4c491080d0050f2200d00c4072654052160582c0b0ba6a24000c83c1d4001c0500d4001d400e0550411155401b0358032245030016564904005003c00f89070510700a6510190302c1c9070160300448484001c9040d8410450701c10f47c8103051400c08420300c5004070b04040c003144582c0843c0c802c1d044100501020854045640415a149d02d20030840540d00c081e583e80d209520101400c401c5069a03607 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 866927724 1250 866926474 866926477
    0xb2b060510020609060c0412021c060c0804170702060a050a0c050303190b090603031c060308030103060f1d030315131401081b0a14010302120c0309120702030a080c03040b 75
    0x400740181e000009010314503100b40a0700c1d0300b11128050443c546400d00c808442c4040c2d00140003800303905686041d000fa0300e5070a1b00313600881e6000006100302900315000600302041940e041c0c402e050200c2800b09070030300c1101200d10a55020780041c0c1044090b010a40703880d00183c0124051000a88a680c001041440110321501c8128191903155801c0c80c4088200c40070103803124003404088080c04969a4000151190442044103598a0229050442d8044d12056000612002000c0004010803407903802c01c0c8002003a90307404100b00803040341d20b24243d000c2050716041c250010804031358141100c1010041c500005840124454407080c1d884040740d00c13101642200ca4040001800110760034068000c0784031020380e000c1a0440310900151011500380f281b401000300c0c9407031100099000360141e0b8007000c00014502d41e9450413003540496030b403080700d00d03407400e000d0381c0c1e1100f528104030b4003503c00498000c1d00410031019103640c1e80030b51394003491040c15140310500c00040d225042c0b40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 866928974 1250 866927724 866927749
    0xb0406090225080706020309150a09060b040513170f1305040b01020d080f18100504030f03061d06120609010b1825090f08060f010b2b0605 61
    0x2001603440c01c8520781d9003991140790005030100b5511060a401103014803041e140c0b007503006000180e4a0f1070742d020750f92a054042c41451200c01d030b400c0401c950221240d100e0840c0c540a200c051164000110403c001c036481140c0c0001c1c110341da5410203020424045c0e5045080da00301c094a0b140805600b000382854202000e00090491000c0c018030080c249030055000f4210207000500190541c0c56018040345030040240740922076110002e01401c0c0a03680580c0d0340d04036801552091401c203110100680404c543c21380124100b9946404403901c02d1041da030840d0000080e500084166040c1e5405107030001e014541e00070300c1500c1e640440f90f0248880350090302d06400026104043c0d030180603065144201030b151008540c810082d251010070418804100080e002c4d004410065009a40c048080e80002051400540020456040c000f070f103907000d41d0103142804016a41c03215607e007240b0400304450000c03840142d0034000003034042040365015101204c007203000c03500d07480411700114040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 866930224 1250 866928974 866928989
    0x1082415041107150606020a020d062a0215151c05150f0a2009010309021201022b0204080d140f070f02010f09210212060109021309051302060c010b0406 67
    0x4804d100d580100510a110061206001901103032500342c0000b44c1c40404c0c0344010303241e00d485040020403058164034425a40a60704040415100c4902c7c2c001e40d80d040c408900c0722800111008a43c484003c500c00740301004004002c0c070601c1d944854240c0d114040b03924202c0e42031280720788210744002c0e0303607400c0d500ca62902d002e5120306107003142082d802c0d10f042d40815880120318110302486401658200c800d00e00083c01c0101d11000c082c404580300d00c2d502c0d075625110354408211791680b0a181c940009500244208070941004030907010750807841648a00e9840d60b00200201c02141d001d25584402c3c442c46440b018102007030b80418196660000303d08035105262044c1403011507070031103000800f0344c2152410120840c1030495402c6009141c05100302950800d00204085503601c4403d20b00c450401026900d00d540d5581c1d10f83d000c0d401c0350405001c41d60000c800468400514030500e8401c06400011601040706a000d024040e40300ca100403a05549403201c3c070b1000e0700c5034012400280440f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 866931474 1250 866930224 866930243
    0xe011107063b1906230c160f050a03050307020106080601080601290a0806011d030d0818030c060906012301080a020f03040b04030e040204050a03110a150801082415041107 75
    0x2001c904248078101017100c02d4500303000d00502421504c1d64041e50baa00b0f404107a1030b21600c0b8207003844404401c400c070005101d44900b50300d078000c00d580000030b1030240045400030b0010316250b15406d600c070b041c240507840305d980c85580104940002f25404c0d40548215001c208610b1140f607520000da42d00c07014030200811085018407a8135640300c1e41c007e03181001c00a041e0120000b00d1f0003ea102c41c0c105110707004008241c1c2c0420701d810501002580285c50a00440e507580a50416454030b800c1c1c1214003030300c0b030b001d2100000354152144074424241161240d1030010491000300549070a0b0b8060300e03912001d5820b2002e0074028408000940c01580641d00c8948145041d00e002000f0210828041d4080c9006110401142e02e0315414801541d42c007943d81d0714480403071808541960495406003108044090340c0c0d02c0d401b90001500c506071030300403056401c02201c101d4080f983c40d1400340c81d880303080078100028040d003011100600c01864001c10115004200003e805040d8014141c26145001c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 866932724 1250 866931474 866931491
    0x90a06030b010b07030507030c05010b12070f1508040b0705130605120601020f0c0402031e0106050d1a01080601050c120c0f0f150c0d0e011107063b1906 67
    0x1026031210b401002c5903884140307080e8681e03800030401e001e81c034001028410741001c60420004290000b401010b00900600c00c0581c0781220310b644d660981c0304150100d0b01da00c50209103504590341c2c2a20402150b2100310f5241c07615568400348403402031144007003283c240301c80440104642a114000d02c0690748141c0ca07006203d40c44108040042d041905650002e032184a04000219410700e0b008002c8400503100c0c3d513400301c041501c0401c86150b50f40c50a048002189884e00079014003100307202000c0404c81e5031415502d003050150161441030200c1e80b0207000030140e6102c2c00c000c1c103d00241000340c1c0d950020001d840c0c1195041400d955075540c22079290581013200400084039244405001491022070400241d4014a8080c10500203410009110001d004054000c4c4000a900c1c4000308810f501120640071281c002040451b1600d080c000d00c0f08140b01040d00f040381c0107003032141d01076080322004040c059500b10780f00c0f400c4007030140a6458805c03485004491003124001c0310041034010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 866933974 1250 866932724 866932733
    0x5060307091716060f050405030118033f090c1502120f030c03071103221205100c030603020d0b0a27030e120a032c01120515090a0603 59
    0x7501c044002d0020790100d00141d00c1411441401000c94000e030802031401c007100a8129054825500038903090342c20074504101000e0b0601841e22020701940d0b420121050600d660300520106444c2c00003031007020719424060300c400070031078052002441c100080481141c1e64460281b240303a48000c1003c0b0000a41b160f40396014410002c80c135441400407842c02c1c8403854502d50500015041c10b407010f4020000410243c020074036600c0c0b041d01d090440e0f4444900041e20070032003035981e5400e2070080d50f49000113800d581101980a585500c04050a03625000440850040040c80b860404254135064000b0151301d4890010300e0300350080041c942546004600181920071107a54480d61002c3d140c151200700c80800d2005400030390510300700c0f03150300324040050400c4034840419001801107200450416403c6108030b01440002841c0500e032140189502c0f95074480641e0441c00700340c90790030407a08100544e114661042a440303540070318020031408038040701c4084502c00750990382e5070000d00502 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 866935224 1250 866933974 866933999
    0x7090f02041d010f052d0604030f11040c030e0d0c020f060703080a142503020f0c0606010f090b090d0c09060b0309151902030a060b180f180103080f040506030709 71
    0x6283c1520121148401000c09640d03412589417103030744504041d5842412a954081214001d64000c44869422b035036604000f80450725800c6442e2003a80b8000c0c0c07101d0654001d002d41c0407803041100c05091f87d204d14400a68207035091090881e44031410b51900b6003150b445002406003140640ea034541545020702e4000c00b11004d4000094010301454204402100800f00e1b50001031400c01c0010341080303600314190302a009100903019000e902050b500e80d111000107015100d190241e84080e5041c040346026203c00105005620203004100503141060234008101002507114400c1e800300b1640e070703080c0c0504a0301c0c03036004144000000400d02005101c00c0280903035982e040d9003a1a03a90a0174644204c1c01388082c22110107058010000071071001d02648240c00400728085d040307545041000c61140f040f41c8030b205841c410b08040c0741c2001141000403404480103061490845164215241c0f00382c15008070706e5403185480c00b00004078483d190b0354091030051029403211020a070070100503001c1c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 866936474 1250 866935224 866935229
    0x2040603060e01143d030b0906041439040e100b0a030905030d060605220f0b0c2505100507050a060c02150f090f0a0507090f02041d010f 60
    0xc01d811441a0b542541d6044032800e40d0041c00c99880e051400c1e01c00004800300c194100c2c5e07809610b840d031411a072694064103c1c1582500850720441641e4840d403c200841d084405120700707200036440010302c0e40d481c107540207840f5102441c0c1c07490350911165020ba21b160700d0f042c0c0705c80c1c102c0380810100803e1503404503203034100090b05400b488c501e04095056800303014503034040b4101a150142c020600c10103000b103990000c103403e414011561a44000b0b0002d82c05440712980c48140d1041603040d0401d9043e101094606065401502910f040c0900340550030040e00048580100041c85504480d040c40f00b03032503841e029070903180c05890308041007040b942c504801c1b0180013040204200203a0085001e200c0664024070000c0c0b0040c0391082289000700c45507240f0f1000b6000b0b02806888d841605001d8403481c220070841303d202904029080d183c1e206613000501301d40c411030003480308079000d41240c42103002900b401402c00d551240d00c0404515904520071250b035000c0014001785e141061803401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 866937724 1250 866936474 866936489
    0xa1d1c08091b0103020714011506020609010204030b01030b1e250903050d1202090d0f05070510170903190f12180f0c051009090b01211a0402040603060e01 68
    0x9012502e10b9040000c0041e03040664105507002940c40104514003610714080040180204101000c45841b150000d003103014500140c812080003a81201c414001c13101520703444150f10750903910355541c4108440010f0a04183d03881c11082001c106040002c03d00e00c03400f100000c0e0707040141d0440c240d83c0d0f1400204024420001d0780102840030070b10005075428044072515100803d118980076400c000d0052072280c0398401e40310704800081c0300c40c0b41e00d0300780c03094000c6083d00c6400b07a0350400c20640c121954480c5000c60f154520210071030300030f01000b90740080e8174400d59280c10104004a50b54221072075075540485c100f178204410082d0b100c1c2a110041003441410005581d460b100446500303a040c0c401009100010107a00c1009500040342c1c0040c000500340180951031000042c0030710409000b5003189504c0e15200200301d40c4508100b0460284200401a81a000c07941702005072480c1e0300d003a040b801800034903000710f0701d4510040000702156a00003d10341c1c01c0410010720140e06074000711 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 866938974 1250 866937724 866937733
    0xa0815011d0d030e1302091e01020601031202031603050a0f030b09060d110a0b0318010b13020901110a060501090605090405120307140c032a060a1d1c0809 68
    0x11001000c216100084080849081c0b886220030701d8116504032a415846400078500c11001d28000000d80103014406001c5508075241142421000d6000c55070307080c12401a4001382c0100042a03d000c4041d2001042e032045e0b80c9040420507050b200d00f1400b110480020300005003240030254092950400400d1520b0207019510400740019810b86000e080a88a403102e00036140800402c11281a400302020f45a001c419954030701c2498690402c8a090805044840d564038001da018804c818007514010704034020301d464400c64200035004040c1c900d050083c0840800300003c2c040152060640c03207240c0100f40b542c10102c0c82001d5800d6944824090240d0354140700c0001e03004200c0d01c00301d0214400c415242d5035400400c59500d101342581c901c80940016200c06080400300003443c100074a5025404408048088a41d43c030111f0004229150403490114103001c3c0c05411142c11404c88a0b64060445002e68883d070074040c155280a040c0204040a814403980103004203901506100250 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 866940224 1250 866938974 866938997
    0x7080907050f010207170102070302150112030c08160b0421090b0328020d060b0406050d0e07051c0b15060a0302090a03140a03030510080703170d020a081501 69
    0x1240e4940d203a0085a00c600a011180032aa034800c00104c00203141341145601c0c4450030404181c000d500ca10702c00d03801400b68101e00010318102004450480d42024138280010400c5d840c111800380c4400703402c4452039410440d10907055005c4a101400070702607030090390941010301d000c8142d60901c0703070807a0151031041c4000b01c00c950000240700482d80c00c090141e07640c0e40c0b43c1604980700c0c602e8440e52035120350b811040c0d001c40c0203a540540000c0d11500d000300329039920750642000d01d0046d846903c0016204003e040900d60b890340000d1816444201110807894844c0d0016000e10821021800f002c00d154039403405200c8413983d8240c0150250044410003441a40800c0591151000304c400741900068583d100d5120001404015508101da1409642e0303030141c950380321038040c3d80070340000382400c0c0401e1400286c80c140004583d0840700415540e4039683da41100000c1901c100704909405100070707414a5543d000034900c0c46150b03076420045141030494859640203c2035610304004042d00340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 866941474 1250 866940224 866940241
    0x1e19051e010e06030a022b24020405090705091807170f070f110f0604080a110714131e060e011509090902030a021206011a0705060129070c030b0708 65
    0x1d442c5000d8050347c22000c0322400c055016189814200c0d40c0203810140350b184001e00040588800c0030483c080d840f021195100310503c2c0903030065005103903006183c6000b107030915016500501c00e2030809080e80740c0300400c45040c03c080d040200c507101c012941c181408111240740b41c00107903000340224258141818245401051001036621400522020380c140c1900c03c031040160803600860f043c222005440e0601e0080d466070000d00f03981c800b0510b000d042e04220b0401142880c240c1d202021402c00240080d010400b080031082581620b05980f6080d0320b0f02d14200440021035500e01d484041099440d1400c02e01300003005a020b44c01114074224651030403030f070040c032142c1260144100414441d180d4000030b8240700000c0d500a41c4402c40307508607e000300011950714101c0d941121841da00d041d0704205c0800502c01e8001c024003a410140c014803404140705070103524a0400c60341d086032842c4103034400741e1a80c070800c002e40d50710341054820402c1000006401d50300c40c0080c540b051040c2004003e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 866942724 1250 866941474 866941483
    0x19030303051b0703021c02010507021c051e090a0e25030b1e0306090d0801170a050a030302030a150302031b010311040905100605031e19051e010e0603 66
    0x1000c054a0750003042c010300d40c0004100303101010340b000303d541d025940b42c0a956408050350709000106041c049020850043c42294070514140c1c001e00f00e440ca01c54401941e5509070241d01040c0b010500500300025142c51902c804080e0b02210b4540c1e90381c02d1020001d03604c2c00c66101e40500c6c0042020881ca41402000000101403120820080000701080950140107441c241903000348001c1038480d0f590700d07030401c884901e18081c1c040e00c070a0740362030892a840301041e08100c00031541040041002d580484601c0101140c20400e80b201c3c3c0b69155940d509213500c1401c1170300042c1d00403043c4401580c13244582c080c0c507900000145041441e50340030035100c050a034050074a0b159889080b04407640240c01c250183c1c00c60f40c032400e41d07903034641c0c800c00001c00090300c1d000308210b6940e8022641134001c804490180130840e42c40080c110848030404c01c00309008201110425070500c466894550340e00841d4000c0300d081c16401440b06612001c402c0c9540d0507400700b5a4642100c081c45907a440c04207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 866943974 1250 866942724 866942729
    0x9110a030207030e0603280e1504051c0903060606050310030b070c06150602010b030c0d020d080c0706031d150109091a0424020301050f010806041409010b040b19 71
    0xa0150320342c50075040c1070382e0750260010740c240c200b0f00c000b0800602c0301080006140000043d40c1c02c0c261100001103142c2154060041401150f01500000022601403007840340e115201340c003190028800c4c440c0f4a0141720f0000c000d0008103448810034001c0100134000c840c0640301d280303041d6040d440d00340b030440c4ca00c7c041d40c070010b85201c98210106410510404181c41c400b90480350602900c45d60005503011281b45101307110040d440e0210b46070705440c0c0450b43c990314503002092210607822680030010401c40f52041221256010040406520780922030000140510340300000c4a80e5101d4507000c04841c01d142075000d1381c000c6104800f511905503615415180404000100c6041d030386032808612030300481c01440c1c40c0c0120104001c011000d08070540c040380c00003102801103603041c01042030b80404e01800d0760110030301e080200350794442c0007082d134820b0b4010070204460019a4140c1c02c0141b041d5881c2036103944483c1045058281800349940022003074908103c000310000903c00d003480c150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 866945224 1250 866943974 866943977
    0x20105030115030f05090c0f0402030103170f0d0e06010f080d02060103060f020c0f0a0c0e1005090c0d0e060601180b09040e120d0f060b0909131416030501050109110a 73
    0x514002c8100d4070951050f0841d40c0c03004003c204906198a40b90b070750b09000110b10b803041078400e00c5551141803600030b4134101c96102c54040c10b0034203d28000e16884d0860304070300d00d0640b02805500c003507107a28002e40a441e0000c0b00038102a505103428442c880d8445e410040003070b8485030307142214079800114030703044130f030072030000650030168010300000780c82050005240ca04c1000018007101101082e206011403043c205101d10b169282e441441e4002c6c119189040d14680c4c01041095003440501c40794800002c2c00c440349011801d18203041160f400064070045a403001c0c082001c2540c005a401d1004240c454442e80e4641c0b41c407103413101c031344521321125000350b403200c03901e0711a9030040006540b082450003d041e11420418100300040034021030440c040da040c206c0000b41070a1103070889603440800380100405079541c04000c08034809805086030f40c41d08800c4031042001080c80f01d01811020b810904111a2450034094255a410b0300300b6410340c4c0c41c0005683e10a2400403c84280b100107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 866946474 1250 866945224 866945249
    0x405060a05061f05030115020c0d1103070e010b030906070305060319050a02041e18020916090503010509030408010f15031b080601060c030f0305061507020a050612160c0201050301 79
    0x10a00425000c2e81d400d10010200080b040c403180c1201e4204c005181612250801210107003038042017243c1d10005500302a4000750001060f0001c0b80d4a81e0303864003203c0c070180c101c4100640e6003000d50000c6100740d20860307a08001106114003610706000594000180b840c1c01c1c002030510b100000d4860140c5408281c0754504000003408101c410f2120792a10f540003031003000000303000840407001c4c03d01410341070341d52464100ca400805186a01d60000c480c0c014044140710768400301c11401d19841c0c207031418103000186034002525a0240116482005900301030360701d8600d040070190030346180c0356014066508159000ba0040314414410701140e4010608150084003020106902d480bd0b400500c65801044000f10b280d64010008000e511310a0b41d540c0795184441d0005c90880f0402e82d030159000c484600c000d910103c1010103801030b24001054034030b15a6403100042d002d588942d0700001c494800b541000025540d407031030001e054249050030022841d1a034002400762005000c0d01d403e1102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 866947724 1250 866946474 866946481
    0x5090f0f011202031507170702030f0d0203130c150e04200703110604050d1709070b0c12071b05030d08040602030a09051605091008030f091903031e0302030405060a05 73
    0x40030407041000c0e540711002001941130461008000362407404c00821f00c1040000818295440081200c0300c002814080a040c948450070520295101400300510010001441004a0750400d001c10082c00302d0741142e240100d59030ba01400c841d4500c2c1d0001d101e5440c0c00001040f0040342501c5084040070030306940e60781c140701d140a45a1400e6245003109600c181c0040108000c070004654100c4106a200c42000707144250885466040807940d503800c0e5080004100403001c4a10064030102031050b040d204500d1481140c01d030341e0b8124510a480c0c201e8070031124204c5007100e01401e0b01420050b0041c0288040301000074040c80406440107015076400030019000c203580b5400038820039881020344e02d41e1b070605800d05110040d1405018411300001010070b41c05551350080b6003c450786000038500b00008080d58111070380010f00b0349a0001c04468880c01300c0141105400042d5100e40c49a10f000490b103032401c9400d900d18540f110070705204100b4003000c1540081c2c81c0b07a120f03100320340108aa69 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 866948974 1250 866947724 866947729
    0x31309051e04060204050f06030c0d0515060703180b07021008060609060408010504060f15033818010b0f04050a0b03010f0c030b0a0b0304020111210405090f0f011202 73
    0x6151041d0340460480d01c0061004101c0d0320f4000380b081b9401143c0c07e031340c0c88020300b040240920003640e420300040801c01400c02c0c5203038075030041ea610902c3d4140c072440042c01d2001041e850350103200d049000420f0340001c004284c111504040150403170140c90b50426100d0b9000c140804031304440391050040c40c400080e8a5034844088072401100946459100c941d6007217020302910098804491090400c000f10401000910581809941c0c40b021b41403440d14603102c00c0155000d540c0800c04201510f11150b001405440c000241d0348190b08420700d05251a01d18101c1e8800702c503070428500d0341040307100070940c0c1e40da03008889114800c9030001480d45619095030010171032084010703015403c040c25000000e49a0380114a1507000e42c40c18044c104074502042204041809903c0420304140045009540700d59804c4002402d02005c943c09000c410340003101002000f28103c0070740000240c2880a401c111107030a41040f00c50b845683e00f030038842d41004072680140520031414010911b40810355 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 866950224 1250 866948974 866949001
    0x20717034314060601030908031506190905010908160512030c0d020d1b0818131518151514030a060503060108031e13151d010203130905 60
    0x101404100c84254070502e2420389401900401010180c1c00340c800001c016501038010791414552000d042403441da9131030807644684082c0420f4642244040c40900005040502d0f007461030743c3c064a52a00c85450040010000e071071070b030808c0107250852408040d2103041407000100703035041140c4040d0310380b4540480c03038514010402014120b00c1520310b160813940d004105040d031b882056644801d2940d0744002d0300b001081a200040c07002808008045001d1020480d6100c1c070a070081180101d00c10a0100d4801c0e07408481c03203407108014a440030810040681400b40c40881480e405215411640255040d805417034031075000407240d03c003c60000c1f24460303c1c0107107441c0c4a89844035181c1c285042400010201e03802410301901c41c080011811040000c2950901011000c070360300341082403400c0303055a8001c4400000041c00000000c01d0145800e00f080030681a00e80e00c094070704c0c1041d101020882c81c03011456065400401c440203012506c0d540383c070241c4900e80c1e008071b95a21200004240c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 866951474 1250 866950224 866950327
    0x50c0d02030a06060807020d0804060504030516050105010819120e010225030c080304050d060e10020705030c0c09010f0621090f06060b09010c060504060608010c02071703 75
    0x255403000040081142940e8080070035940d0710382d2100803a0b616001d050baa94204c000740040441e4100c030006d00002d0f130740d40003c0d43c440c0c0700b07290550500300a0800b15048000201048800c0d9445100601030b0500810801074681003c210340f000180c040e071180001e0f01d041000d418204280304040c070300e00e039008110039602d0445143d4035601480100c801c03040c0d4080180070469801c1c50306440001c04c1900002950140d840061078143e107049266140c40007040200c41200c03903409600300c0c0007600c40003403010300320f8280541e02455944107914040340c105a82c00703058074460f00c02c0e5001880804008070b00e07041624100d00b0b01c070042102c01c0b600d03150340300b2195806407400c074140400c01041044000c202402c6521945043c4940f54440101c848035002c4c6074240740c0040c0100c3c0c1d8081c040362542d00300540090007070900103550b90319105207600b514a540b0f8158050f0380913103000c0000b0b10003442030090401c0024040d41c1400e62640110a601302d041a56071030388030060907207036800058510075010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 866952724 1250 866951474 866951497
    0x4031209050f011d0a08030f0414030a030b1f02070501032a090302330a031401140f0d0807141606020105070f0c210201090b0903030402040b030a0510050c 68
    0xd0b540101c051603010308000501c0e2402201599410042c4a00c00540c05002070b80c001001415540c41c10b550184114005100360780da02d8070100740c00d11180083c030003440b9070302c42640d0100d0b121034410f042c4031401440e80440c410310028420021a05940401d88100b518000d00c0c0c041f551807815007410142d00350005c3e0b41d0b0030400c402d01e085c0d04482e0300314203002e00300c0303109942400303400501c8003180c20083d41e81c1962000d4440c200f0305950a0001c044001c1485a409040000302c0c40209c440c0e101188400740c119194040c07441d001c11001e45440b0800f0200d0010403602c40b4400d0b0013542e514101809003c0c001131020120401560364010140a114202d4480980034410582c1d1110020301030002998020302084810000704112072003039154000c0d01e40c1105040d43c42010520320b015501400328011411550390300280e9000a4007200c04e80c2c0500c200c20021a124180340c010001100d1000c5c0c0034034400e80c00788448400190700800c1d050390148000700700081380d59450040c44607038480c0e400e500c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 866953974 1250 866952724 866952733
    0xc090c0521150d0506010b0702010915030608010e0d0c1104060e040503030708010f1514040b040815092103190e010905060f060d110d0512040614070206030403120905 73
    0x1181c242881449a100341e40480d41051001040c02c203005210f09a00ba010b045034000400500190003007400402c0381e03a1041c588044000d90f52001d000c4900c0450750000d00107030710307a501007281c03040c00d01913110881c2003d409060195071050015240002c81500204904e2810600120981d25580640002c1201e03000e88070940c030b0700d45001c5440f588200c56903408184c1d1000042205105900d42506564003501c1c4c290804038584010341f0004550349a003c1d54007400c03c008251041d0050140000340016801049951107252600459440061000d81540c2c4541c5821108030a598902141c1007519078a4960b03a4580e070704a0001440799103608a051801d02c095444d207400154440092035006030151021034a0b100c0002c418203100340c5278950303c43d030b082c01d00002240b500030390580c1c2c2c5000200118001421541c4007420000c814400c0300d400040801d013007000e1900710f0061079030010315101c0c140c0b91000603400584d650002800190401c541d8101c201c0d1200ea1b0b40d0301006409401c0021135 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 866955224 1250 866953974 866954017
    0x60903052a091e0f190506120307120305010f2d21050f01020f220506072d020303030c0a02011b09030b0a05090a0b07030f110306030c0105091c020d0c030308060f030a0c090c05 77
    0xe029452400000bc40001c2ca06000020024048072002080d9075000c02e8486d6880c03000061030142510840452404803400707600042c6000b000d02080407800100340c12140340d1082410310b20f08003203900954000c90b900410401501c0c0d070614040310080294052038840b0315102100481d90486141c008035000880026480c3c184414000b0036148030040035100b035088541240304031004249003400942585c01880800e8540721118081c10190328144000038502803060005680103088015a0000c914004428070074066000382081d0701514250f000d0000e82002705c40035035030705e00521000d00265000130100708802d210b500300d80038030700d5080002d014060050340301380160b43c8144c4140e8400c0c0b103000d44001c002e50181003642d14500c4010303e01249000c1440240c2d403090512034040ba800301c0c00911f800c00207203c06c0c90722009580a6611004e25151070828071682110308502203120b54001000b441c0060340d420259400d81d0850840881c1d07801c44028283c0e0a801070408641502c1a10900d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 866956474 1250 866955224 866955233
    0x30f1611070e0a110702010e120c030a06140f0f0a050403030609150f080d05090405040611030403110c1804030f050c010e100501060903052a091e0f190506120307 71
    0x3001d00440c03524000700824250300c84201d40c4c911403140300a020905840c0308180d14075048ea40c6880104c402000c2d98100225480040d0820f1030104048444540c3c440c18299440c4c000d0000c10b600100f009041078070390402c04400c41030303000e00410900c0321b607480704c00140c00c00d171080e0040300040c10040010700c1202c0740c504d50b0310a1211640110500860304440003d0f413600700141e04800000d00b9203865107070000480c10f00015200c010402e68400741c44600c0c8c16815800500298851402a510340e040d01800201c3c03113061040380c0007142d100e848020180e044842019112540066141c103000c40c00840094064035603005012095415502e0302c9120300f00c1e00004104040d492450480401c4940c0e201c031015070302004203020103015940103221745581d4000303042d01c12645820a40755840b02d1030200000030017001048412840401c000b4800c03d50118000d03801d1500072919110381c03a2145481581030500c40c001d803448081e21900c1f0030101e412601c4003820b43e22500c8841003070340e948150703a050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 866957724 1250 866956474 866956499
    0x10602100e030a0f0e15131d700e4e010b301e07150801030f150c120c0302030f161107 39
    0x300e1005a0382001014108200040100e80c02003846881d0b002403c2072808003120303409025580c59810008801100c018146050054203a90603114003412016042124074070384045012031b581c207610102c000744030240066004111000d102e401445881030056a90013040c505401d01c00601042580c0f166042c2803043d006014030000c1d00110091010540d404e122540040100c1c1031002803507508040760700b445c0440c62403908452900c08000500302501558805548400300065216030040e070b19800500b0481c802034490034240000c0003d110388902140c1c04203a0501c0800c030200d15046215043d0a1031b403001c1404107400c82c00c641c40c010009021034260340113040c600c01e841c4101d00340001c40c1c502a90050010004503a500c000c982d1840da031340c002025040c002140d98007552428088881810f00c0303000b070880c40c070750344e0011800001c0030070f03c08a0b01042082010180100200070400038000200c54001d0300043d14403044103d408030442e0504104500418180921880042c0300c600307482 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 866958974 1250 866957724 866957743
    0x2070219080d030c021207020108042103090308060108060a1703040905150f06031003061a0d0302010b0a0504141602010902091008070902040305100902010207090608010614180a020a17010602 84
    0x40f0200318200d400e10302641d403202141070702000b40c0010825680194450107100b50014450850482c2f101100100740c2c0b4000b00210141c000aaa40e14491007890340c000c4006803c64820300b40706000341403082c0868400e207550300400d0401d812002da60390f00a4810412a0000c1c99503000030005424024200c0c1a20000807850501c9420301d55000c030303164a004800c89002c4c5000c0070800307580c98595524500a42420445c100c281d0200280a00d5962070b1800a25059441307a030001844250b01c1c01044010905a00443c1c041d034606035100c1c45541240c4141c0d074000000500c03070320f800c40c01e1810803805860342420082d00400301e8401c0c013026001c4100280d041d1010b00058610740c646515422080307004600c030103001c0d81d0001d111b00c00360200c154400110ba50061041d244181c0d10384401c64155640d0782e000030b940342c1d90b481040005451155103401d401030101e544020f50502c100b0400d00e0400080e004003904d03030f07000599800c494051715038015244104480d0034041d69403100081e440308100c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 866960224 1250 866958974 866958977
    0x806040c0306050d0b06030703151b02010b030c0f0a090908180301020a0806221e0b06040b040e0a0e0115050108070207080d18090f05011d071202070219080d 69
    0xe10a20992070003402400251800602056045400b41d01d410703038240d201a0100760503000d00540407000c211140d001e1990710442c80070100e900d240c0141da47c000c01741104011411a4500150000c6a0350702140006111104907024202c0c0c540da1000140c500f501d560080e650b59107400c14144c1007002c1c1001802d41100041c240c83c100c5a1003034140350903807040030006000621404000752881c82c0203840d10300e1800021b1000c06030030f4140841d0348103ca06088100b17201110084009060340f0082c0175810388207800340e85250806141488480c80350059005900040d034112000a2641d1303450b034010111030340c480d0000c0c00316a2208610901000b050700420380050382d0a000035280600004482089a03400e10041481d4411500111240f40c000c41c25099200301d07207040094100f03041c0c010040001340c1d4460004095145c43d80054505040179001034503c01d00004008080d90004400405000000d1000d81c0d9402d480c0f0000d00d28201c000114200718030400c43c007060030324000442001a1899 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 866961474 1250 866960224 866960231
    0x603060c090f03030804080309190c1e0b19050705101e14010302010e030c1e0306100e0606030406020913140114030606040f02120f310609031806080604 67
    0x20382c90074000103009400701501140ca501c0100700020742d04070040d50300c000c804054604503007041413054044d042d03154094030107442c100700c103111404034103040600070f0644540000c40c0d40d2038528030320b449000340e020072800540042d00e01c40d0224000d40480d180c0075071000c00d444404046042c032000074095051131031040c64648030007428001c4644112140380b607180303102e030050380c0ca9640111a100740e00806140c250080720a0b1034003607212820744035803410700c180050b0b040f03540325020325180c150001c1c038001c0240201079040240c249444075843e0401019550281d0340e595509060020344941c0342d04507000340d0101901483e40d40301354440c1014104100d0038500c0d80c0d0380da94680340c41d04174001915a040d00309602240240c6401c1d0310a2110a00080c07001d4100303000342c0c0280117005802c80d800d440d498848820003e078620302c001c08225403808070f0b90440200184030b4222108048001000300601d944903e20801d16000b01e01078042400c2c081c54245038243c448000802207041501d000e401a4107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 866962724 1250 866961474 866961479
    0x8070f0c090207021c03090b0f0d0b0f0d120c080703080a0e010608100203060a0506030c04060e040510170f060109060501020c030d020a240501240806060d0c030f0603060c09 76
    0x81c0382c000ca40120341c0040c080014034490a10074681c070308040c0f40403014400e0007000003800c0700c000400390018007c1181901d444803031070071981050365100b8401a125050844102d081641c49480c4194803e13001400c020342c0103a458004e031010341c141c0750058803001011031108100740d400b2001920400c2071240a00840106194a0b820394900d80101c0c2015007141c0002c16404860307074055544400e0050030242074580c2c5501249540d0b005644031a0514000101030000c150444040852184103942c00c21451801d0f080c00c0704810402e0003441d9072060045242040e40000300200c1d0600d030340b0501502c0603541e6034000361000704100c0c4200307070240c0950131114030140f6011409001036050398000d081d100b01d0a03910150510041e402070484a59004001c10700e000051244078080d020329294110a0450380c0701107180700d543d404404003004040380070019203880f0346003512204a0b0944000c11400311043c001e030b020f480030204007604240740c00c80000505c08950460ac5250240b44c0b03526000030b8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 866963974 1250 866962724 866962739
    0xb0a0c08161a0c180a050d06141819050f0d0207320f01020f0f06060112150e1e0c04061806050910051908060f010e13020705070308070f0c 61
    0x2001c4030103403d88001400000d940010700c41c0034210f03001c8024041e07030400743c84000141c082402114180c0720300307650300c040c81000c2c601c0c50042034002c420803444149038810701095070396a002c1c01c0881e40d4000302607000d1a08101c4104012111401c0d00001d8985100e100b00d0000c0d9a01101e01c1107544866810101500e1001004c10321024141214562201c0403c510b040c812020801e8000d81e0442c0300d0101070701c510107024408803140b00311300303805040e080c1400c42c001401540382400d014030440c0380c4403204600c40601440300007100c010142541d00f964800d0542ca514010b603846440c042070501e01040340e912000350041058800c95114200d4600d00e50344122185203803401440013086040048005a1400d0b80b004200e0340da20f403510700c1c903140401610341c484011441c0031030086805441400f42c10326102c0000c841d2060b0a18029180700003480000d00240200c012900c41075a002031840103001c414003d20000c2c40d0000a801c1d83c40c1c4d0140390000e46c2e0003e114007035a04601c040c0000c01c000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 866965224 1250 866963974 866964023
    0xb0a0e240f1804020a1a0306040c0f0806010c020f0a06260115080604020706180309060807020c0d08070b0f04060515090f090c0916020c0a0f0b0a0c0816 67
    0x220203081c1e400c1400d00c1d040100240c40018005907446510080d00103003034006c0d202400b144554000032240c40381445e10500040d036150042c40c905200d41300d02c02c1d0000769070044940740d00100c01d10309400d0701c90f200d0022943e88401c0e8014a030308048180b80100320300f60044005602d0b1700008031005c030121061080d098105900380a12445071104070400d50310248101c0341c0b107402c500b009100502d0f0041c0d0f5079a42049541d441026a101c01c1d031100c284083c50b0b0020300349030013480c0c1401c0401882c6003556000751940d03140c0840740e209101e41000c1c20207100c4403100390b40a00381e00103007242c514200440c41c2e15a500040710300312440c41c201400184503140d981000c0381c1d440f1014000700707116210b15000b01c440c503c00501a007031600c94440140d1040d42d4004035140501c09000c002c0d200d030003800000a042000d0004d00a002c2d50303601108002c21001d01d403405041760350000c0071584610800c402288d62040d103a0380a03000003000700d0b10109800c525603a114529114045030304421030080c524070180d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 866966474 1250 866965224 866965249
    0x90f0f0d02150c03070b06010f020d120f0b03240907030209010608090f0a0c32040b0a0801050c1902010b090708060109030203060a0f0518030406030b0a0e24 69
    0x22648140a010050402000c020200c100d000310850500f1a480401851070300189019280c91400500388441540c104c6025010307040203102034029554030200c040c20314180c0034012840290307621034114201440c0d030722039044410000c0603039900165041c0b0066020380981d100c01c1fa2042e1040100701c00d83d0000801c40c040b0b0380c0c052b00b180003507881e0503070a0714039400c0101050014020540000d181c0d42c1c083c0000c1030200d100300c0380c1001035030603d01d0300d108c621080c903844022844159840701d064400040b011040180031140861020613110214801103c180d0084841d50300b480d0a01101100040290650081103141d404007465a89012030a071141d00d414107030004506804564864801c0e040389a100f90103040c100e4100e5600da007c68602903048503803018582d40c1d1103610320601e03010300a040d003090a580c0401d4005410080c03260b01d0344141d201d04814507540f00d00d80c503150f4071010240c00040c07607038800c00e00043c608440025aaa5015000340c2035030700c00114008540c5c504929001d80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 866967724 1250 866966474 866966479
    0x30605010e01090b0d0b04081b2406030106081b030a050d0306051804030e0915031027021011011503110f0301020310030803060a03140307050c0a031a0a061a090f0f 72
    0x11b41e2179584840516038041c0d0005c1d000b401c2200d070b09003803031102001001d41000f031440e001000081c4041078064100d9000e03203002c0c840d9040010410403940b000894203041a0000700510071a6075401c0060300e04010088010401c0c040c3c00c60182182e030f09503000e0310481c0c10554624912a1b035900026018540031100100071600000d04e6941600300f09141c16400402552503007912001400040c1c503000142030304250164460211040e40c0c16150030b2121a490744024074840c1040301e81c00590588000b18080c010022115250100010250081c1c9840c09443c400c00c180c00e5182d050030055110b080808600800c500310840c0740782c0c1814421203214500c100b0341d0300f049604503541d0b0f8000c0d0380080d2403942d00210950020000c104841c110000058440c0000c42c3c0d60b0b04c1e14a001070800080039400d0b0302c6103124540070404a1450080895500601a40c116007a541c02da080c40050a064100082c1e01c4194507000e203000420340300500b4000b40131140031080600d00f100b002080310015401030b8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 866968974 1250 866967724 866967743
    0xa03051f1517100237090303050304150c0905040c0801060e0d0303020c0111031801020418020c0f10020408120304050709050702100e0705090a050603061b04030605010e01090b0d 78
    0x50002d000c01424050040c0341660301101000d030524082e60010008100c5021100080366001c407290041004441120044031580da1102280581070800720702c8003506115000000400300704881020b45841c4004a900f00280508590001d00c101c03101d0081070700551800c1c00303100800c3c0c0120b183c141243c055583d0b0120010501d018810300010142c4101e051680034450b05450500a00420b2081da40b000700241e120310300014110036002c1d14081e2001c05910402040c0000d452240c4c143d51900802400035070b4840d5490300b40c17482c1c508400c200d0201405611002041c99070305030002c1c0200d0b054401191103004c2d80311000c00c524882900c005040341c0c4442d000300580e00c00794106d103900c000b0f035006403820004082c02480c00c0e60010900329581d40c100100030300c060301d8100140398211419007410441464481c0200e547c409020f13007a07000740040c2c2c07000c2500200d0071104070341c040c550102052000c1d5a45410a801c00f80d000c0c02403103801820300b400c404003410800c06282d0f40030740281c47d82 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 866970224 1250 866968974 866968979
    0xb011d0111030d0212070201110c060f060f030303090c0109051002060613021213050d0c030e0d110402070302010501150e090106050306040902040608030a1d15180a03051f15 76
    0x665000e681401c0d24030141c003040c0000500d62003a0700c0904040740e030743e840000c003902e88802e0003400c6400c10750030038500c401c040c4031403003140a00180b2541c0c440b24001c0e0048141d1681c0d03000621056070120403643c035100000400406000c0821050222202038840360365240d19807007005402c81c94824214010b03403090000880901d043c15880c10146242200140307011060000d542e450b83c000c860107403191004007048403c100e400c01004003031040c1440d204101c0c81036aa070080000c404607503036510949003600c491080c03100100440c0e503882e0004000315500c81840ca006070182c0024450180301901a04102a03100c0c00b5004d011034078a0000d03d038400c0c03682003030000e545603007024240d6070b0800d0f075900d0000d00685452003002c000e4510000215290742032060010030b170440e0703030055040d00d0309107203928107203a280d00c900241e03020125204c15456102c1a2250059125141500d6501c006990b40c008280100403464041c0c00800c4008500c1c4400c1644000341507400d070005485c0c2280343e10804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 866971474 1250 866970224 866970227
    0x14120901032a0807111c110721140601030201170925180606050d0b0d2102070b0702010516030c1a060109050a030b040210110111030106030b011d01 65
    0x14007403001d02d074526a00b070004a104001a8002c2602e07040c0100d400302e014041c1e501e4102d030000c144040003800070b009070000068a0f180c40c03031100348600280319000f8841c0409540511183c1c01921004008000104461038034401003211000180d40044071040200b0400f07001003002c0d41602e4041c0c540740b01181450625815030b0000502500b007038041d05070081c00390301074144040171000c04003400050240c20100180c8101c0e80c074090071030801c2c1c40d0420410403d5004401c2c3d43c0300091200c0d000032052008804281c62b0220003000406600140c4c400c400c0701c0f2071034252540c1c90354843e401c03500c0064685040d48118490040080d02141c002d022081411030090f03030404049109152407490280f0a03541c00c541c10400c890b12069004580f0200001c82d640842030384000d00080b82e0303000d01c8030b1450b00c80c4030300d1600203400a8041c00a0154101010b4025040314000c403a550300204071b40c0e4030000703460499400a00500000034100580f00c10070b507118640100c07484070180e110200c050a200d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 866972724 1250 866971474 866971481
    0x5071218090b06030c1321030f1803020103050702010e0303010306020a080924040602090d0302060703050c04260c03190203070e4606051f09140612070302071412090103 74
    0x103078102c00005040b0202d080601e0741c0182c04000308407006e16000311f1309841c3c003a02503c08a01c0c20420000625411a0520281842c2c001141d8081c00c0000361501c85450480c054050504440c0462000000010400805a0082140b0401e079030301d80300c04e03444000d00d59842d1407072a2100007204004444201d112207502c1e01b00ea0b0040d01c244001403809100703401107036066a9442043d03026800c441c0c1081040b603014016154802c0d5005071852034282001c5d440c51154050308982461039503142302428510300304001c2c0c2628a43d0003412110100c0d403880034588800b102400407402405901f1001502c901c2050b0290301428580c0c0c50035100c40d0941851018103002040f20b11440034880b0030b614001a07904a0058505c8000000842d42d14288014802e011642c111011411491003901e002419400141001624000018000c6a40f000030001e4007038003924860700702000c0076800b84000c46405034000c2807006d215010a030b40e40a406a03080d9185d0104800e0903211400820a620b05503101b40d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 866973974 1250 866972724 866972737
    0x1504081b0604090606030902040b10320324150a18030602031006140a05030103120c0b10170a0309050d06090501050702010e0f210a05071218090b06030c 67
    0x3481e950800d40c0d03940d8168152101c0c4e138001000f00383d4414011003941040d0041c554441c00540303050b500303d508040000d000603c0040f50034042d290000c3e0800d4085140022049010101c1d01e45603264208901107003070030390011b000303011450310600880d56035051607292203046a10400103030b82032178030000040d1080703209039902109040c4800008030005441d440a180100d1540c4609010300b1b04100c0d0184c0300c1000f108501d4641203041c882040b1403680301048a054a134000404907817140c0210064542106070f0cc00109a10124010841800c00304424442102e800c405c40b074826000c0110745a4a07111844005000141c2c40e0009010605014101d9180303144100300001d40d1004503200c4608640d001e48038040142d45900b0f1940003e20104080d001e8076281d01e022741411556600300720000b910045141840382008640380d482140142c1c2511585908180740743e14024a11800070440e5110b4800301c00d0540c03c0c00000701c0d03c1e0540780f07e814440e40028044030b203103071190b149002d52a080b81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 866975224 1250 866973974 866973979
    0x4060c050c060103030224040b04060e031605010504020406050f010914130905030a0206010611032b140405062409090c0a080304050405160f0e03011503111504081b 72
    0x401070308105600800000b4000e40c026409846900e054600c1ca21605801c46420045c0d04650028800481d80f0446090f03046070f489a030018820f80485505811400f44103412582d124880c17100009100040d084103100340d1080790204080c07521641001584041441024001444100f091002131444202c04d4030344a00108400c0c000920603101105403041c040085889400c0400c03800303085901003204a0250646040403840343c0c40d590401603a0b400b4101d403200d0480c18192141c4610f6019000b070803e00c8400704010b105161441640c00421002070b9030880da03601c03139440012180100e00102002509a00300d20b25041c05403a4204108584058505c914501801f0006516070b503e4180e200c000b0310340c0001540d102c500c0d0000f0801150380042a0440c5810810142200da5500c106805800c036042d0070210700558480010a00400481c881c1d04407840d086100842404500041d0303803c1240304598500380c541c5080490001c80c0628820038116a21030300803007005140c509400242420007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 866976474 1250 866975224 866975227
    0x30608100507110d09030b010504050910020304170403120e04020309250503160609060f050702041505040f0e0f0a0302150a1b030e1c0531171903020604060c05 70
    0x92803603c504003900c20060402207120208100b0801407441903080c01420100c50401ca6407420190881d2650101c01c05181415030000005041050400c1030440e1001c004901645494036490440001400103801c4004102c05142d08001c4d8523080c006c903440b40a41d000a01207104000c02c445a004a204605541250403100c1c0410340d600c0811490b43c40d40b820510120030b071880e0180240c15200e054000008009041070681d04058000c402c030707108903905450001c1c2c5a00d40c0301206000b0900d5070000c0d6441402d0045009026800380c0041c40c45203402004d480300708a550f55500c2d0780707008026000340960021304880001d030108118190f44420303510000309103494003c456203a0810800107290100b9542c0036288081c1d04100500a010901c2124070103c1070a28200a4428040c0c1002c82c1e014980501d040554800c1c4024104106803001c04002005a100c1c14803a21546a916002c5034600c20303210303003224007204010f0090040c0c0d0590007410f00c0b501d854403210302600d8003000450500a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 866977724 1250 866976474 866976497
    0x1502010f09060b15090d151b02030a090e061503130b010f0e0c0a020c0405060a09090f140303040b01090c030e1c0f0e220e0a060608060106030608100507 67
    0x5180641c800c0c0078824600043d41d40089800c21000038589010320f03140041c140040e04482d101d00c04800521600901410103001a0480c02c4002d800c0d5460350f203651800340403a8480a580020141401860980703803960b4040d1107404003c1c0802d02211000c1e0300181080183c040c50509c1001160803806030f400c0c1000e00555901c40040e00682a4401c100c0f54400c100d040101058006c20583c0114440115501e0003640036002581e500340d100e0103030301c165616004245659102e59010303004080c495001d010408040c242034841c4900c1071002d80c0d444856951800210501104480c811540702e090301010380d08092889006240707001000051603900c003540b20f220b8200300540c01e0170000d00203140c4441a0708100041c907c0b5583c4101381e00b409507110101010b1b40c1e03101c00340d036284140c50f02c01e00c45090340c5480303080c0036040a90801002d40100c20484e0240b00b10341e000001516015000c560f05643d0303620044088070b40da8032400109401c50441c21149926940200385c100f009407174544690340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 866978974 1250 866977724 866977751
    0x618060a052203110616020907091a04150513290316200c0f030109170a090f1503020717340c0e0405100504030f11070609150201 57
    0x80300c2c85031215400d900314104004001c02e03524415840c00095684509101c642031462594000c0468001e100d0407024000400151048070034100414850007032402c0842e00340c2c10398100c1d07031203405580b000300c1034042c0c0c40300b00e14003400c1280c941c800c4d4641d02d00f940c685407500f1404e01c42e003564a081c4000d0055070304061611000000385000c0c103070190b00341030300800409004c2c0070b1315030f000c4c1140005ca2209503521820500031403062100c40054490740c0002040c2d20000e0300400c24104000c0140c054018034072602107143d00034144c0d601c482d49801c19880c2d00da42c041148001e80d4403034400b0006100d80b800c500c041c03180c0c02500b0300901c0b070890342000042c800211185074000000000d01401040e160201c80f58401d0b00d0728000e8440b0a000380700403041c81d1102c3d580320107203004010002c0c03082c1c400300341000380410840500500380e10080005040c503180c010b0a00c281c1101d00c00000c1d06e02030304000f001d00040755500403100f194072010000c1d481d00d010383e0b58441e8541c85040555503103079070304601d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 866980224 1250 866978974 866979007
    0x9010908130603140c090d0825020901170d0c0f02130b0103060e040b0c0a020f060106120f0b01090311030304050904151d06071b0f0b01140618060a05 66
    0x407940e075520a640c540c10100018100e400e044200080664010140150781415004690388180c00359010480c580c054100324095100d4501030000c02d01c11ba043c103c001e031026496500b6035620846004c64940d0344c42801c8110049145980c91890300940c008001160040034030541c184d10482c034031181202e054000500d110740040c3c00c1410130381c4602c0b016255607070500c07031100070f05000c0404100509142d101d0034a041d40003045803014910000c0e500001130300812101d04510100c900701d031395541c2c40310802440340e22610755083d00281040d0141000c002d003401403031640d04041e03540c1e00000c0d2450300d51030342d4000d508408541500003008003250685891107003030711031400342c40c1ea480600340c4c440c680800c480c2c480c104184c0f03100c4c140d80b4940c142da03000320b049600595940740c802000440d001f51742c0e140e0501e180c0c000b4241040034110008100303005440d9070494507000b9541030b880c001c000910040e0b0ac41c104078221100040890003040340340280280940d081c05180090801011145100c1c48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 866981474 1250 866980224 866980237
    0x40c030b18071a16021203030c0c0606010c110f1f05090a0807061209050c120604030e03060c090103020705071e09050105030a0b130f02040c03090b100e0f09010908 72
    0x1e500000c2011040d90001c0218a00601080007110001140e0152151850041c041054005500416141d0556480130303550980c030510101584c1d0781c0e052040070814640e1001d003110401d4001d8a001841d19170140075543c0c51950080312440240d922542005020b2002c00e0b601c1d80d1200100781e01010b214085064515541c8054880c079550b0315190080003070b9220558422003003980094014490035600041c42c00e03400465840102e0820080d01d461400d28900f041c580350095900c12074050400d600213007071402240282c80d180c500291010a040c0c64030000c55013600314481c2003003514000e5101e80d0041484502801c01e8540c040d449407100c0c02242d040c02e00211100100382c40a110030241c0f07106160040c50202d0060901c0389581c2c0e0b4013041400300a0007100000e8007044107509002c0040e00b0200c110b070380107204000b001000e03000900148400d01080d0b8401c2018400103032440500074500d8103581c1c8540000106070f8036082031402c4840000c2194885540303d18410001640100c0a03010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 866982724 1250 866981474 866981491
    0x2702120f06070207051507030f050304060906020a050301030b100e0c09060c01091a0a02090f0411090a06051c020c060f070c0b04050a0b0919022404081c05070305030a05040c030b 78
    0x2411700d010100129485102e05481d6076407070821103d40007a810041c00031030003d44e814200d88940c0c403406d025008020000e005800d15000103103103164158400b0055068070f100e030001c05502e03154440c40f0b45801c122406869100c5c1e078603030082140f00b0102d00181c41c41c000300800300f500d040c584a0000782550303090f186c03c8a980080c030710f09030380007240008030790b0380a04210001c5090141081c0080d41312101c461580380a0360f51303070a0400d95201860121100f601014200d0f08440390780f072000a2103607100d040040750b802c84074840704a22114078001c80300c954500740300800c00d944410305e0003118100c007d40501c06003c2d186502a0028100c44070b91403250b4020302c080c00d011401410610803504c0020074180c5c142c4c210588207141d8480c1100d05841181c0c06480e21143d4100d0342a2400658222184500403440c0103c1d00141e035031000100341110030030101203040140100241540c5034003071707110014080390041c000503600c5c0e081644250341c01400351181a07030781d6550384c41c0c0d049840d50903140d600b07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 866983974 1250 866982724 866982733
    0x204240f03030e0306070206070e060403060c0807030b060c0304140307051c0210030b0d0b0a0608070305100c0e01050d110409020f07031106010f09020c0309030d02030309012702120f060702 83
    0x341500100f0008900000360050140c51525403002510388200404907010302032215522111a200c0a041d0b401450b4414410031031403101a0001e020b2400071541c0000207420041c0e140c00074103084042e03403651a074010055081078140700440044840c081c505581500c00d035600092030f503454034040006505254003d2002c0c0500e40140941313504000106002c1c1824542c809296446110b82080091b4104003800d00548425407044080d0139a80d00075902445803080210600c000030840720a00480501e04000704075203010181c46466400c460140400d506101e00c1c3c00740314554020700d034580300b2401c400d480d140d154000e00080303070084540c0380d40116000ca030042c100342d00480c082c0d02102151005111640c58145c182414260600444203c1e640110300214881d50030030950754101030050035030f110201000c100035039a8008580c1d1403e190308000000c03a074000001c04035225105801411003401c0055000c0c8503950210400c0300445108850034980c0c020401d01903180541c03559800340 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 866985224 1250 866983974 866983979
    0x12011503110604050a060807020703060516124b020c0c090603030d150f03030f0f050a0e010311070b01080d0906110319020a080d0b0a080f0a0204240f 66
    0x5200c400c03903a5001e54040d910402061000c2d40c1c81001d1a41203c05a207410300e020390740c9035012410680c1541c0020216800c00301803046458041c942154600e2296880030341d512400c070006c005681c115418034080740c10030406110030040b02842180540c1150b803001d00c1d2103100b29440c4288050b03080742c1d030390465400f060444009c4003d02101170090812034079101c6c68142080044d481c0e128600c000c1301150b41d0342120f10240c0344400301d080c00400001103554000c590300d09007d003101d00840311000c006043c40c03040380041d038000c109840d40402c0e155124181d0f03400841c010b6005010030096403182100c2400f2001c00212520304d09400b800f030b884087d06580d504034034003611945490300503c06000c6490302462224400005a1310044100045025600c02c081c07000da042000640340a8410b880c0090400d46989040d004501069005d503100850180d882c500b40f0303118813001c03109414a40019000d04094601070b00202c4018a0510842011021010035260005e0040d40306050100044804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 866986474 1250 866985224 866985233
    0x30f1202030f16060b0303120109050a09052401150e060a0504120f0203060105060403150b060c0f0c090c030105061e0f070b1603110d051306020d15060914040b12011503 74
    0x1740484c4c02c01c250011810160881a01c00200c0b1050144415a95442001812a9545410144446400c20251840061000444981d02016401d1200b11142c5c0900004034600510140b8070040680e6541c2c4440c4e191003001c000e01d42d440529441c0400c40c05020204aa00c1c09103641d400062050030490001d0300144181403d1400c168480d40c4115020700c01000891044092070821407601c0740001090354081002889a000e400c44103200d0f4480c900d08038901c1e040008100c60800001c0f01c1000407540c03045010441e505c024010641c0004041c07005401c0580001e243c0140700304407461150a2030070002641d08190895002552101001c2081c0300188030080aa561409201d150901500c00c0ba910745410a11424201c0d04483d9619400601e0b848003070803190b021242d000350195a100f004180c050068080c00c9628105d0380c840c004002680b5000c0c0c0d04000032500000981c24804000408201c000c0c06010900740c0c01514082110464103428410081000702c100058032215055080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 866987724 1250 866986474 866986481
    0x1338070f030218120f010203011e08030304081b010b061c0b0603040804171015090b01111b0a1701050129090409021c060506040f0204030f1202030f1606 67
    0xc209050501c1005003040c0f4403200c0c807206990740d4041e200410105a10416a40340c40480c810340100c40d44040000300e50400814100701855142c83c1d102030b00c0342e445081c601c2d01c070b101c2520300a00d09101000080b0418900e20103200a41c0c20540c00041c1d04561040880e906502a207002482c500d000c18015040042d01e10030541c00f20801d0f01c3d114110314195681c00964030031030242d0100080100c200001d01c4e00c1c1005548880c1d101c46100303020070100d5000c00d1028500901415094030f0802d1005241c1354480c0c140500d41d01c10300d00080c0300c031540b5072030b030200b259002c02d0440d40c02c44078001c40811140d030201c00e546074604103400001783c25071400b001000e000051303140d00307080d2601d00d806a4cd21888401d06440140000f1500000c0b165824400555440e903910f024002d4180209000c0d000d1100c40d0b400540b1448060310140500d02c0480382d5a0100e200e0790100622a45103864000003140903511445035003a0f8030f0040701c1c6031401c0800b0341c083e09c1d044004041c96010102c044030042007071600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 866988974 1250 866987724 866987747
    0x303030f0910092411040b0f0d060f030b0c0315150d090c060f14070b1305010906051009090c09050a1118030c1e1012140a14133807 58
    0xf0301040803528005e220340c136a02c070b80c0c4640040ca00000c64883c00083d050022100440c4040e42d040021681c0c41c200c01092404511041d1202c1442c100020810401c0034101d81c03080040c201c0c06810340d0000010003020700b210568888040c01c0c14045000c422b0f18030302c14a80d00f0f41c052210070240d2468554010704040070104600100194009041d02021560080e5500a940500e0403500c41c1c0d15034904203190900d0580141080d03082091007800c0c4511984540d00902054400400704c42e29001d030072040e03580b15030b00240305802020003001030b94442e60000d60000300407000440d540511044002881e0011303080c0c09a84401230800c40f155103020042c15a441c40107589102340b08190010725140e4960858055024421049107907004610030a010100c004000707004000c1c40a000183c0c030042e00048803144440c529180e0014030040d01c2844c110b1059945014080e09944159079003000f007890720040b2610000c10803040510504c44001040b5090b500c48141000d515000b00300810040131078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 866990224 1250 866988974 866989043
    0x6080304032102150403030507080108070501020a0303180206131d04020a0302120c04110d05061206041709130c0f08090d111002280306050303030f091009 68
    0x40204100086407442511500300401221041040340e1103816420501c40290011480b13048030104020181c055114138064040c0b07030388402c103581e280c13040c0d00d075114001d0041c00e025900c2110306070002886070f013190201030034146038815601d00c2a400b10740b0b0340e042040112201203460a0510003c0c1c500c01c0f6081441c3c51856800c032003420a500801c00c0341c84c250102170702a0005000045040c401005056481c80000c2d008003d1a00007007002c8001d07822040305074440c1c0f03007010b01207004c034500200b080c8462451070b00a45441e40300e41d56000303080400003104034103e403070070700c02c5031203580d15091866041c412404c40480c070449203410041625a0280402e82403150074005e000421f80c00041c101682c540d1400c040f1000d05070f4005407890003005040b21340c007150001403070381c2c01c03a1707075a90340581000070003030741074040c0c2071132900c00d90545100b8010b09070954003e100080c40c007009203980c907400851940940c1d06503903180d411380059071100a03065454807602c1d0321b424402c0c03004003082620070110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 866991474 1250 866990224 866990227
    0x121c020109110411070236041218091103070306060c2f0306091c090b0307180509150a0506160f0201050c06100807092f0405040c0e0301060803 63
    0x2150b40b4000401e09801d5900d0103960340d5522420588100c100726070201e40c00500e00880f2060321104030001c41e140c058030540103000e01050f44c50b1a01005404c1e0302071350340000003440724030600c6002c8030381d2845403072005102c242d0030b90001009000d92003030801c034a0b56410950350724607042d003010381a5000c44c1e01080800580c00d6154000c100303410041c92181141c0c800013006095240700790700c460990404280d5042c06440103104070400001101200851100410008600016419a00741c01981b281d000c0c420380400014828a100f000717003111021059400820068482001c2088070008503040031010880c0d0764005128a0807046080042004503034080c64011014982503910500c4000100004030300142801168001d10a44210441c510101da80368941250104e80c40c990b81d00c2243c01c64040c099011541d0306150081205040e01c1c60003404400050036080d009058070103044100c862028800400e450f9218068084052103a81d520489054510308060854100c0d9010b000261700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 866992724 1250 866991474 866991491
    0x30f07050c150a020d021324051219020c0c04151401180509090601170309090f0a090818120c0102190f0204060303120f140c18121c0201 60
    0x10005007000c600180e0900d208080e80f510010603010340202d904a06800b4008103820300b075019060034030000ca03168001084a84240c40c3c00b0003a8901c80560484002082003051030403031b4696001e40386d044800c916440032007084541e001e130200e1708021041b00007900301d81840b00b05443c16009040c030f6010140c440805081c40c240030b07800a01200c20340d02c0d0601101030900308260803140d40e0710303000300340c0545045d02c00d182444609854600034025140d410116490325010f1450000694070b020f0400750050750607440c5c0c00f08007942d94100408521140da12100504001100e01c0081c02c29401705421a01e480309511080001d40400100c41076483e505c100d03a401c08580e400a6091114040340c03450802c80e18507400c000821901458020f50000e04050300002010740c0540752240000070404104038040c81c03403554105949514529480703010141022030140ca0105004101c0310505042d821044901040030800ca4000c01d5000c04180d0401400d03201d944030041c0c004648407045100800c01c000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 866993974 1250 866992724 866992747
    0x60606020d0827120d0c1803020a03060b060c1c020706020604150207140a030818060412050306010905030a140115060f030c11100e120406050f03090c0603010902030f0705 75
    0x255910f1900c018441e0314402030020140220004c0c1305030500541e6860240105810250803502d10010000d10404044c0b0513540400d1001c2040d81e42c0281011503552964035801d002e00b010903a1260b101008211402c94684100040e03406080c40f440f95203101d1440c0540642800f5199110500f0754104400704400031f105da07110300c2501450458016111580d500300100c14020403980120180300d503070303024010b050b009010a485222100c4956000d001034681c0b80351a440c3c16140240890880c80070640418018405540d000006140c00c1480c1a580d000103450410313100c5d020754400d440f90090420782c2c902030040c864290480405000c0e21480d00f8001001940c40c040ca00c0100750f034a40c2544100c6104036620007095904104944101d0303d4048414000c0908241031900c41c420b164290800050213420384007110160f4407401c5c10056407107611441c60b44010f010801da402114903802d22030fa03440000e14080c00011070010307202d10b80303c041c40660000150a000c1480002d000400b58003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 866995224 1250 866993974 866994001
    0x30d020d02031605030702030706020312060d03120f0e0a11130e07031b0e070810170307030309020d050a030f020706020a21110f0d12020924040503030304060606020d08 74
    0x1440c00311660781d208400f03410000d007140100c0038002c1d032600400c17030005449607000000d450806c203c11a8044162a00f07000c00450800c0e45c01c0c0240824001c14110b40e000344035038002807507440e00d003001048000c201e1f040c040c10a07030719480c100e6030714000e11001555820300d05c0055420f522080400c1003420f240c3d461455640150b03104c010a10b01d550414070b10b84010300c0e0952030080c0007400030445035003454038002c0c1c4444011111400c2c1082d038020001800020540f6070646503000c03801840c500340c801d0300c084000c2c2004020a0340c10184042440e00043c00c2040b0704075110f4040e582d599000d200c400000ac2c1001c0c0d203903212204650208500f000030554400e002146a03404009046122a12213030a0b42c1009510207061800d0250f001c0404601034081040c90341d11600f80d990710b545203001a401070807070003030700f40d66508100b03c2899032001c3d16281002c180d00440d0b541040b03080c242d45a002a02d15842281c08640706601c4400400c0b00caa010842034100c0f004504102c00d99250544115004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 866996474 1250 866995224 866995237
    0xe0607020901030b09240f13030509041d03030c121b0904050a0b0a0f05030114190b1309060204240e0f0d0803010e1006090303020c0423090a02030d020d0203 69
    0xb61104c6808500008020014510706903d0940400001c100019080c8040b8034102d400d007511000c0080040c400c034003401d141c039044541c16142e4509159994051000030300311030442d02e452245031082160080410009141300300914101503135a4103102c0520b0720680009031020604e000340c040d8902c43c9111190a9843c007a80550300001e440d50f440386e464018200e02d007542174001c2c100810100d0004400c01000081c0c8070264028020f2102045802d18010402c407409001c42452101d1521182d1840e00062001c5c1002000b490440f140f44404134203e44001000b00c807202d90002c3e080042440f4013a011880c0c000c03007000f104004120010203461440248511442881b0021195030b80da5510309400c181560000c180d0b584035a1503500d4142e030180252150b41c95032110f800300203075003849008007074140ea5165000d401c0a8003091300b440081d01c0d070041410210144100e2810b00c241700441c216119010020041c403040019006050800c1c0c1c20800d0181150001e00caa220000d030000101c0e00ca = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 866997724 1250 866996474 866996483
    0x71e090b0117090a110609010903020603130804060c260909040c090e16240804110d05010213140a0302090c160311060108241f150e060702090103 64
    0xc40d04880380c0100d41d10310b41c81903268800075040b014080b078060009462150203109200c0b81c80f480f124442005694003070010302d240003c070300010910040c02e00002542d008682e005c1000000b00296944003120342054100c200014452840e10040c08000c0005a0001c54043c0400480600c50140c003a1107210f100101070254a0010100c1c00700111808400010107071401d003005407441240c180c2d51611008901210307000d034054408903031002100319081c10305519480411031021004002c0e01c04800003003081d0b03803a2408001e5003000e030711071440611106105800050343c6000202d03c0f1080c44406810004000f10101d00a12458a4a240b8a82074a40489058802d40c0e5601d020040c140705198403035504040720b0240c0001c05803c110300901004001056514036070b00c840700b00c1c0d5104184034105619100c09079881800700c000d280d0041c0c004c0f0701e6035034607000e446452010003000120f9920900030505654541c05072142d0000d1018541c140c1121528a0b109840e00010a00c84040c04080c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 866998974 1250 866997724 866997731
    0x121712060d0309080304140406080105090723270a0e06070e190b12010e060108040f030c020307080643121e05090a0506041103030c030301090e071e09 66
    0x605010fa12050000d0407a1070407030b56520740320403411124442101c0900e010714100440402c1441040c0541482042d40d400203204051402e100740000f002c407030a032114000c01c2854012030310307181c00d6a502c003100f40c4a000ca60071401e1301c1142115028005100c445098902002c2517840080032418680080c0240303010948115600002140d081c400b071181440b00d5031180001564002c001c0182205984540205003507030b81e0b5001180207034400300e4900303000406500018001460b40c0c520750000078001c2c40c10f1018200c2e00d0740802c1c035040560308000d40507030014041008d03c18165024150105c0f41e8a4840348440e49030040301c14410003288060f10b07000000080c0005184602121300c1981c10f40720082c44001c1911007035a0030b03884140708208600d4180b10010710700d0f250000d0008000c56100f070081560366103541f03555070f40360300150219505000030010720244050800c06075028102c401d800285056000307144500d01720a41d8048421000d90300084030010f200300d000001190100b51020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 867000224 1250 866998974 866998999
    0x6020f0418020a0f180816150903050d12020730091404020a0212070804063c03110c060a0b010e031e03040506040801050615040f140f090112171206 65
    0x403845d0a040e00180d400344107004103410b0f0850000c0901044405650441c0701454080c0c0c41103842450070300010700b6551016100841180c030460032070a01c544010401400c0a00325a40c0d07401441c10004840c8044141071042e80d40011031b1541800c81414a040c01d2030b0181c905145082c80e200c1c060003161080368045034281c4440d00a100e200c03129250310502076900c0803030346040f41e0603800602600001400807811181c0d42c0382409481e0558142002d1005913000c6056940500440800001d80c20103480300420380140c0041006440301c4a0b0f858040c20080c075003040100d0841e004107001e24100503159158031181d46002c146911503800030700b9030005d880910f418441c6181714507400213400c4880014001210789041d840507004602c00c4601d1a014090349580300c600780074034050802c241d00e2400c4100000c1c82d1400d66442200340142c81c02d202c0004410020f400030a09a10a50019040d82014000c124034100e00303d8800c0c0f6601203107828408100700c1c0701078000300184020300030b21240c0b002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 867001474 1250 867000224 867000257
    0x11710090606083a1413050918010b0607031e09030203060a020c06070819020a1202160302060f041505130204050a0c120b09150d06020f0418020a0f 65
    0x500003030803010080b01d92044130501a03403540900c0c03001c00c0140304034040340104000000f8028856000150b0354000c0400c50200285500340e02150b8046800410b00800280c0c83e114050080d12401200d0000740720071100076443d81c2541d1700c2c0d4410501c242020406000004d8101c0842d91a405200c12408030407500c40b1015111180e064101035458490481000300204068000741200400301d415a200c23911138442c15070300042d0039600000503103068403071085511801d0380640010b40c40c42c980b0601d012105c0d080c86089031303c01841c0101c802e1025203484141a01004425007115000050403100c0c0750a440b08044406401480c01c10562180085000851501c1400c0303107580e0003c0c410030503800d20510712002825215170740c03000b1407590344800024480500c01e409048101a01d040010381e030340900c2c0300c502031650b09500d9101d4a5150088007007074903407003e408004401c2c0800c81ea280d09000031840c9911685a040e00d0743c5004000e118400b50740052003010b81d4005041600c0c3d0040719111 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 867002724 1250 867001474 867001481
    0x8120c07030f06090201030614010c0b0c040b160201090602061b030a0204080d021005010506090d0803100807030b06011409102f07030c0509040c15050913020901080117100906 77
    0x10160046060400d00010721400d54400e4071450f100b628100003165031081c0301c40689c0b40400f0800c0c0070501508460002c00c811081103a0f00c0280c030041c0c40d1409441d2200c22107980c108524848039a040866080300f15600001490050030040c001000c1a06e0b08082c20100417021344d0039540311800c0400411040001501610701034142001038500360111050005d5a400840e45201c41d01c50070b0900000d29414080121240040040c080c203014440342c0e21000c145610241400111084148000401102c107008580c05144a500005803a0401400040c80c007040882041449041003020245030707910700c40684242c072003e003804e1844d8940a01c1ca030203800c01b6440c04940b071102885602c13491789404500388040d203206002c10440349403a102032000e0b2a0003298001e00c000c5e45814140086d05e5544005030390100c1520f059840c14a00002042c2d299191031402c8650703503000f081e12105503030841103d5002d031070351080405e028000d08800d030741c0c1c0707916680d4000b01c001e9070b4a06031424803c1641 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 867003974 1250 867002724 867002729
    0xc0507030213050f0601030513020d02032d0d1e12060306020c07170c0a0314120d06080f011104050d0c0b16050d05040f0510031407080601030c0908120c07 68
    0x14580030000b0740c0d40e450080509800c999040707002c105100040c0066001c1c1c030550740503071160210404040000c0d824840c0d01c840e004030a03a0b042c89507054012600180b03600e038407910f687c2c000d00f14038a8665000e100d8500100c1d6502101400710080c011003041844c0c001c050024039051401e00000c10b080107091004003c00c2c0c1016001900005d102c0720211300000d2007104440f00c903c0d803058000c02c19403959843d2007600701a1a40300c0d4080004002152030318201400550700381c0c059800c10149403002d8030ba10b034051303031140d80307240d846074000c00105106105ca00034140f0800000e00a0540401c01c54606204900506100d01c0380801d00308140444e501031100a0030303012280c10381e04c84014a1101c5c1e51207c206c000c8074a4815580f190400c50b10841c01c4c0c074211540c0283ca2440c1504010403c112041ca00070460304265175140e4003c01e162410305164040c4d42a0303269000c1e18140702000506803405035030618188202c4441c1084110302c0041c0d68601034441c0352120ba122a1541309450402c0300b00d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 867005224 1250 867003974 867003979
    0x1230106030515010c15090c14180f04080421110916030c031e0501050f180601121116020306070207140d0302210a030615080703050a0b1c020901081c0c05070302 71
    0x40390782c03010014401d0b542400d031044000010400503c90700ac1000100c0c00150b29098802e200c1d0225400003000e5030101c0c0c12a102c4c04601d81095103840100030303100d190744114110003a00307200e02020702100e070200d6003d51a0685200005103800c51203d648400c11440f42d0041542d5a40341d944094440c0d0f00040741902c810302c10103002d0b14080019000b0301800e0091901c80e000a40940c00c10f450880b8403060550070042101e00ca50340c444c40107442001c7c85903001d0a0503a29400c0140e001c49510008222402852000200c1c0b07841600505182a000901c0c040640d8003d000c11f0243c60070088951649900442c0d040340c0102003840d040703040858075804039500b20814418a801c040c9610041c0501c000150303400c01a442d6200050706004140d0480b01000c54048004110110320941003150b225000c0140481d4031400380f0007207002c172818201444100420342c00b44e4001c500d00000070600600c0c10303a000f00300d100490000c50b1001c141d0403840005202c04120814100413040c85032400440c3c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 867006474 1250 867005224 867005231
    0x390304020f12070e09010c05041a09010207031502030906090102130524070803182b0e0303040b0d0e0a170a030f020d02030610020a050c1e0301230106030515010c15 72
    0x344d00c122403007054265866101d65003003400c1c2d01c0b81544540c3c2980c4c22120440f0022602182c121040c0030700e60300090b0402d0450048002c00300100d01c5c40c001c0e00e5540140c042c0010703520300c1d14242d41d03410540c02811008580c3d004214013118081d8000f1524240c40d02100c80f41000780021412035500400e0500302072003003401045100c240070604005c0e6100b0b601c40d012581360007524900342e90701c480340c03d680c005010f0700040010032150113840c0d00340c07051421814500880440d0f0b0000a1a58101d0384c03046202c104001401e280c0c0709a1805642124254007000307040e034036030541c0e0711488841d01c810300078025140814042c0000b486038100012403082520110f603074036240c20190005e54000c403590750041c5c210b4a0642031942c8002116040e0355040300241c19071185100c204821010020410b0020302c404d2030b010f4031160303401e201d41030001e6400d140040355030104402005040105a0002040c50300e17010402150b415000725041268509180503200c0507070500c0c0201a480c0405605e084080ca03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 867007724 1250 867006474 867006479
    0x80c1602090f040b1b040315021605061909050c01030c1e09060f1e03020903070306050f39090409200112060503070b180306390304020f1207 62
    0x502c4414601076401144130480c1680e944940320003420000204904000c810802000801c0905e0f06402d4810300c00b0102500d0015079101e655142641c0a205071440d0704914140061160600460201080c5200c014802542a0b8540d41d07240c0e1200500b00b810703d03403100304c120310280c0302e0a110300800c51041c2d005218a410f03000e00818880190192030b0110b110003800c01c1400703000d42034013800c01c803026240407000a44032504401030f4102c02d0a84e6014071a515010002807028085c1c01d2041c0c0b00111b0000c17484c07401543d080050100100002444480d48003104a1007055820048541420b40b4149a80d5007096021070020300380a0320142c84110241410b0310b010000200b40c4540c44426aa01880d094004034a54111400342c400c0340c0d4964058081040b123000e00710043c0c0940113041c0b042c0d408429841c80404e003020310071100d08000703004c5081842c0d1414241c11041e4402e295440032030b0b2031465034080c01000742c800035201070700c9a000300008000540c0d9000f0304448041c5107d0640720701e00d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 867008974 1250 867007724 867007741
    0x1b0201090c180618020d05011a030402010309170d14180712080708040b090102060c25020301090804080a120221031513020901080a0506060403020d050708121b070501080c160209 78
    0x101704035602c1c03850b203003410000032700c172000c1c0c0c00e4410a000812001034596210b07a40107500910056404885e520240901d12401c542414080c041224030214003056507480965070f1694144000e104141c2c60380d584c92901e00456000412034103540c0140c808440e41c0820b81005541c03402070402c010310501c00054046408030a41014194414080e0212182501c4c1e40318010824041c1c604407411120800b04101c03455541c0da000e2410381400500002880081c2d5160100154000c1e0070080242d44100032041c00c011a0540001d10340100d803003c3d191084251000d19503040d4820010383c000b85020000c98852010000c88551802000b40344800000c0041c164038041d4000756502030108861400080081e030a80c000d82303201e408014180d6240904507801c10010542064041c2d0b0700d0320594402007004101080300158441c0c048281ca40c035801b180082415084100311f849011380c20024007003044e80d8200c0b10442e00910a50fa005803100070861a4042c080541000690301c000001d081c0403050303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 867010224 1250 867008974 867008977
    0x140d02090d0c05190312030b010c08070311121908090f150714070510020a0512040b0103120e010e011d060f04030204060e090a0f030306050d05011b0201090c18061802 73
    0x192400c2d41c081c04007104c0320344002081c0c0030501c005401c2d0143c6045034030981d4403035030200895810505010030566456183e45e00c082d005802e0807800f2484420702658440d0301006088000c1d1054501c80c0d16164808441021490010034032005209117117001c03a05210b403c0c09451401810481110009400110780441001d000c1d5241000304104011301c4445110b170380100c84801350081c0061002d50540c10380e040080d407024482d00c01b006428010195048084990310b0300079030040e60b0441e0654114200030f88903056160601c1c0074003407c800d030310590740d03080800b0068102c0b0034240810041589100d010349140b54807030096008100241e40b64051801c2009403080d0307070080d40c08100751601c84510301d51507142500c0481d000d500c4400b640b4005030703e003001c00304805e109280c0400c41c10713991b03404135502c0c0d00134032001c07a0313141d465140c420740541c5241c2280e1401242c0d44000d01101c0910344401410380c0da50f000c0c0d5410301c0c90054034884410000e130801c900610a540710907100320004074255009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 867011474 1250 867010224 867010229
    0x9081b212b090f180b0909060403031104230303040f08010905070512060c070f060c0518030c01090e0a0b06030c0d180305181810060e0a0303140d02090d0c 68
    0x8074103141d11540c5410707106101050544264202850f20141010404a40c84415011401c002034032581c0d0b2040c00d8807160b03503103070050324200d000b40b8287c01c0c227180140c04c0c0d075005440c513024403c05010400510b039a401c1031100251324514415040580d580100c1d08500c01c94003e0394406910031400503c0c041d055201c600c0550062044c0d805090316681088020201c012101e4010341c0004049100e014141f001132070110702c150000b01d81800155604e070f00740d40c080b002100100b0780214103001c64074601d420b035414083c011070203070040d05007840001e031210006002c0e100d000c492450000c0c0c000100c59100080c80c03000140703810740300c0c60310b45e00d40c54460380724491595130f403420007101c4175603403d00031100e08566074152103190500c8000b00c2c2c122091044ca00802d58460b0500000c240121542c2000a004004403150205210300f03005004c2c05400760a0b115038040e405140080002ca5482100041172000380c0407069902c00300f0f80c890801901514003c00c0c1d1104003d10381000b0464070171101d008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 867012724 1250 867011474 867011533
    0x70609140123160807110304211e020108070e2107170c0f1203072a080712061503081201061704110922060c09081b21 52
    0x2110340e41c0030b240c10850000500c1c4800412421340104e8071190240c5015002c0c003800d201241c3c2056030311101800019403404003184a400b07100050000e00040d0303401c10b1107201101c4030903130250004ea80000c1c0300e40070007099001001202c0c03981035455950440340c21104250010b00c0715185c1d0302c2001c1d007600e4481d1440b81d01040c002030004811741e054041040b000321703880285030342c200d01103030002d0140034503031981e20062501040080d0310010300302c041110146101c0184680d03102c00060815640c0e848940c102480c140c3c4542c0c810829070798a00b088505030740d444500880c1040200d58a05903441c003540006003c03200100d841c01000c2110a049030498140c0d40d9011805444085000b81d10a425200608065000e0b6604110b5040540ba1a0b810545080c440700c4500e4441d40b6000103003603400400c603819501d504480010a600c0000d000140c01d9140c00380c10040c00319020700030311090b0b2121460041d030410f50303c20007002100c502040c2500d04242030f00d43c2c44010000141512840c185410b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 867013974 1250 867012724 867012791
    0x10507080325020601150503060631050a0f090f0b0d030203090418031e1206080a1709010c0f0303020702041b020f030a0906050f07020301060b0c19080706091401 71
    0x141c1c40c0c2c40015194101d542c01d04240c0419a42c40f4000c55040e23100500c1c0c5a0420400c000c8040c0b0310b04410704029555900c810110040300240000300701c0303002c1c242d0180b840350025200c103100c0a03204a415030221860203100048165a201459001e4488949415480b0001c02141400e050b0044005c103454001250300700705503480d4440c260b0101c0e41002010b40010048500061000441d003880554070805d820516551960070404c0b0341542c6541e0001070079604081407040800c90300c2d52084c1a1400360080160070040724000007400c618446e0b0019051a103411003080525001768129944660007034014000c0c03280d820308102101c1584011040107101d10301c0012195003010054422500150355a443c441d8503002d02202c541d0401d01c1c0082d00e82e0001c11613080160780074801e0800808202c00c0c407036100c4401c0d09a40d42001c2c80c0240b40c40c20842d1601030500062041400c03103000540c8160300145000741414803540260340201c0510066280c010340300140000b000003102c44a40e00207c06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 867015224 1250 867013974 867014041
    0x10f060e0603042003211201081c140c0601270b150c071518090504050c060a0507060908090f01020c03060105041806021201060806040c020c0f0105070803 68
    0x1202a2200b110090440701c514500000c2c2e00d510041114401306004045036689082c1c00c0308444005506a04441e6035400060300d4549a86400c2107280100004800382c031201c00340781621000b1004040300740c02003107404054950000140002c0e42c0d0f400c003e00013152019a140d500146100c241e031600110303884030911110f030034002c1c14002d42d202030501404031809001001090102d58001980040321405024004162904180b924030b0581da000c0d5a0401c4100070000b4402c0c204021b134010a03141030034241044042038002030038002003001520080c0c0e80e80014441251b0030701a100000f08218102001817051180c1c02e009054003072421103500e81d056a0881c01640e5603203103005480c4e0181c000d040100050f1506138007040700c5100580b01859800900e40d1120105d0384201070081c442d41c07070f050041c001c0c075520524540d840601610100856500c102019568107a4091000d100f2040074959000f81e034843c0c0180c4a0302a484041f01e600c90805060940c008038940220400e08071008891 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 867016474 1250 867015224 867015229
    0x19022d151e09100e0d211e090c05120a1205090907170a090b0103060914030c0102030109060512060a0c030f0e0703050d090b0a23030406050925090509010e0105010f060e 74
    0x2110600340740c079104d4031010200e807540750394030300d010f010b00c00701c807d503180c4081ca009100700303100c0440c080340c0703010024003c00107150580d803509591f00140d0061494055075491800005401101a17400c5511543c1d044602c84040b00c00384031f00c1c581c1c140c01a4003101404292034104003504403c85408400c83e0306540c0f2035454404443c11080054540d80056004001182103540700208050281c60b4441d22040c21600d414a194450004202140e5000004208404035846640050702d011141d4000c150220340c2c4c0d05681d0600548101a62551003600302080e80c065800140740c00720b456424002d0050400c40725854500302d1106994074060140c48070101445804000180c41c0b218420504102d038070041154240c254084107040044001050451240d41e900074610552240c9008651807030900400c0c0d0030b200d0300401c9809000d2042d4a918000b01e15000c6a000792024460300140c16554a24540c0c0909504043d8084d15441d190010803040b0018403c03405948003a20780c801c1c0b00c4101e006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 867017724 1250 867016474 867016483
    0x3080406110a020d120f0c08040b0604050c0304032f010204030b0f0c04030308040302010209090a020306040e1203130c0f08011508071802030c19022d151e09100e 71
    0x1603100058010182c0c210340c450003481d045c000c0303207100c100000e80088112507036001c585489010740c010401300e4082004105142540d10761042080e1024001d505001900194a00000e400282488a509184c40aa03000510540b45040da03030b00d0300b02801040103207aa03000b54801c0c0030607038140180b0000980e40002540744240a00244401c84e46011b240d80c4007140e0444019104800f155001c0080f998035a54402c41c1c113004010342c1c240166a400d141081008660b0440000304580c0c02c008100c480c4100d907a801d40e40d10400e03c44821620080e9450014080d20043d04200410b14001c0004956210158400e0550351380f50002e071614262555515584c440c0c4504c50b000030050001000020403400c0d4001e07641003152544da003400c0002c0c1c650754948038030040c04e036440160320111911641400c0385100c206043c13030070b5841910400040281b16103480c010305680f191401c080c1c0110308030300d00c0c00802e01e0f408111200041014100044056128070234140c114141030304000400070300060104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 867018974 1250 867017724 867017737
    0x191109190c110a0303111306030615230307170c0307140403051209040f021605010b1e0f0303070f05061005180615041805010306050c0307080a0209030c0a030308040611 74
    0x100414407102e0351344d01200a06452800c40504410a00024401d0005465000c001c3e22103510046001814a030107074112031140b10600e020850743c04c180ba8500d00070010344004481039484066030f642e035181010b5a1110354904000c050003403140c00c11920200e02030166002d81c51660700c20003011001d141501a4cc041c03804040c01e00e80004050880034807504004008000c2b011b00041021514115054103d80102d501040300c40c8040020908004003072151180d880b40844021521680400b40b4850449444180d54062030f14940d180c01266010020b540805070702c41e00c0c071503540c0b51501c0c0c500d8403400195145e071040e01c403000e40070800703160034101112110b03070310006851340b96117010810840f511103205800c800401007002090305070000c4801c1ca40c05540701808a038279451b514041d400c0300c00c0106400b03640c11061090025459100110075004444100c0143c0c0302d01c034503c002828a40d11221a40d402084400c0001c00c00d43c02100700c9204500036602001819843e10391106e0900c20003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 867020224 1250 867018974 867019007
    0x60516060e0a060902041a10030e070e010b130e01180209041d1b010305070f270807080c0a060215070302161a071d0114222303191109190c 61
    0x142004408d42d1081e0b101c020140c100c02c040300c1c1c1e400c2d40c856009140c038000b078024442d10000041c0042405000d10340b41001044842c181c11815071610941030854044c2c0523183c05610f400041c05480b0307030f440e501b0200d0b020000718035500c44400000b5510382d4545015103003840a000003140e1104641c0640710311031066070f41d138407a0910145000d1040b1000180781c85441c504e405403001c280e008100c03882201001d4102040186a01810107003001e01c1c00044504107441041181c400b40700d12a80422101c813101d45600c0c0000d07036034841490560190107242044180c605001d9820410b000a011040f841d0f242040703c26040f0b91124002102c0c070040a07400c1d2105000a4048060b00d54030440060f808507105012507410984c15039100141c2c0d03030954858044030030a106c81400061075170300c015860040e08206d210f20003034120f0003003925018410403000300020440d030a8001d202d4000c190440b143743c010038140319403078011024120030007803001e0305441c03501d440c18141d1000c0c007428280d1213a0344030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 867021474 1250 867020224 867020239
    0x10213050d0f15020a1d030a170d0f0b0a05180114030a06240501090303090506031005032508011103130c15020d030c0306060516060e0a060902041a 65
    0x203190a01080748035403442201d05628029121001c5180003401d43c00b050035a000150365150801001840032101e0582d032100003100c8556030b60296400180812015440b100302410030110700c18180e0a8041d84264003006814540040071803e01e03a481000720103401c0b1a4440b0858554007030007066200c403440c151481917500c0041c00700d5030020b003c500031440c000701294421201582e90b401640c04803220f0381d202114080e80c01484201c1d00540340c0280c0710030b203010003100d440e43c2c800401410b07880c0f040da802031000002003084849d09602c40c401510018003129807514882d80d0242c6406c0b018401c0c10812076464002084002d0103015540000d24840b412500b035440e4046483c400e004415000c4410400d0b003500003c540c0d2000c08290201034658010b006581c0300e40364040d058401c01d038001e000b01880d04038107011041d006001da034800b44a100d24420071606a25248000706a2041840030601c941c0d500030040007103d4002c2c1d01c81ca8403d45041c0821800c1200c1844c1c09002c036031207190301049 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 867022724 1250 867021474 867021479
    0x11221b020d0e0301180c1505030402130c09150f110708071e1203020f0c0d020904080309010e01020f040504140103080a0503040c05040609050402091e070c0819020a03020f010213 78
    0x80b5411a8601100040000502e404ea00024900e03c860800045401000c0c4c1c030300400210582e102040001e001e10f0411038a18034195001a08940c000e24060f101c01d50340703202c400342c010700c2041188058100500c442c13882035440100600300c05031070070b04680082e140344084900240c0100340e005c11121854024105681042001c4109641382d0180580030031740381000140c1728a10304e65403603e43e402030300501104400311400d00c1c10040e100098500a425445001006807100c8000303036032060304141d1f85901c94030b41d5416907016045c2c24003040381795030012400d103c1e01c103058801001154001c80d0304000300d031080010802003074400d00c00904030b00c074180001c1850500441c001c0d94064411200c040102c0e44400010b000c4500981040654075130750802c00046040c003800003070700316044480c0040c08051050403482c440e0001405542004440d08454042203024410303984c02c92540c9204528046008500a41d0b03004c01c50000e8006100d0307001c1d02052000d0620072529808540481d12507040d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 867023974 1250 867022724 867022727
    0x30f0a0506190b0604090b01020d030b06030a181b0807052e0c05030d27020f0f0d05010633021b3f0309030a0b0411221b020d 55
    0x4039125180a02c0740d140d100c00e40319540c1340300c0107101814070007000259441c03418000a2504645600c50014507141c102528241d07035410003500d5108404582c085140c14202161650114080380014403041e902c0c041380308100f06003219681640d07056000c691003280d50300e0030001e18000311400a450001d44c83c00b450110904000390002c480f845040c60542d01c60141d45403841c50f4000700b4404402c030750b00c50230b000060205481c6e41c1789200c80310141409040a540018082c12003d402c4540700707901004100c85503481d00c210007085036400000802580c3c1d07860780d9681118004100200d1040c00c14081a4841c1d021140d448511060036401088400c010308101c1c107034000050540b5038000c50302601c216200d50300180074040001b4600520b40c20301e035280c0449036030201442100200350400d201c4400c1c5510001803254449400c120083c150741c03a181005c1c9440c68130403111a4000010701600507065400500d940101d600192040041102a5140e03c01c4000003840303002c01601b10500c0391a100c0e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 867025224 1250 867023974 867024001
    0x3010f0c0905090903070c03050706020d05091305060f040c020a12030207170906040306020301090915110703030510050d031d0108100302010f02010e06092a01140d09051b030f0a0506 80
    0x200c00135045070326060f4030341c64040310315090380d20031115640400f10501200d03906111101d920900d90400d107080c44403031000503c0c030058910000e0001503895001500d036070b07211102c010b032100d4060010459031b485004020744403074a98100351101a00c51030340c02201403003403085075000c6800000c00b20840b080e02c000c0c03003210b41c40810b0060344200300744008400f00740340d44001e50003071407141e200240040345031419802c4619070007070043c4008d1805480c5a203059a1900b1102c050380d00d481c0c00102c03903031480a8041d424031141c11141e008410b81580d40c0030503400081d1600b001400c1b40d03e0400a8a04d100112046070040310b0000403007050311400c000550082c0c1202441380030314000440d000c2e09007a0f0702403401e03a04031039082c0301ea031004041404103c4807001412003280c5113100c010801d4031000000c1c002c10039000c00c0c61031061002070345c010180202da1052140ca94840261039001510103d21a8201d65840d00039209018038045410208800520700c02200e07886800f0b45960fa46580994101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 867026474 1250 867025224 867025231
    0x3060117030f0c10151e241b030201060e0a0506150f07120504090e010b0a030335010905091518011104150e0915060702061b0c03010f0c090509 63
    0x22441858130f440c0a0040600400d03540c0780d14a82d101c0049490400701c07450b506095004403c0c07082c0b4030581440310003144101e010307003d014a5881c02840c0c641041c03c441c40803000b4100160004885c958404043e4107400400440342244400341381c1c0e84400c00044120381c0145d850952040503403111801c001d0628002c0c21110140445541c01d120032510b03a56000303000c05805200050b80002c090102c1c00e00c0f0310440d41c14100d141c0081004644084c04100700f404580405401d20024401b00172a0640c0c115940b85140c00c4031014184030201550100c0c0707006002c0c0916201c00c2e080c800002c1c0b03c00c50000c1ca511048039540c3c50034005e41c40e0140e04442c01314003c0c00c0080555260a80c0030400d4141034014001400e0a80380400c0354004240d004101e084101101741c41151030800b805001c002422180040d050210f80c0f16544440d50302c009407003031040c1103114515028118024406490104162076800d00030360092111100701201c141c02c1b6108580e8400204074008021b010906100e02019807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 867027724 1250 867026474 867026497
    0x20d02040f050f06100306030b040206030c0c030c01020c0d05030c0a1d04020403030c02030606030c03030a030c05040e1f050a0f0b0c0c03120406020106050118090b031002160203060117030f 83
    0x510080c08401c40c800e6840442d44840000740d220709010507400d09001c02005900c00e454100481819580c5507440d110340a0710180c811000440482c2021400100301c0d10380000c1c110880c0e6950020200e44c5010f5040001200c031280106007804440c540076904980c824414440c5052516402c20402d45040000741035000c07260b0300e014004e4615481e0741c4003d0018600944501154109a104041c64150004c00080c0685c002000d00070183e00e0020540303258890505000c1050111080222243c0c01140c4c04260001284010b10000500c804240800740c00c01c810f2b41000c60f0345400a000d048041d602c01d15680d117a0900c0c0810012048102038540400322605075484080034000103454440c90284143c4070110000301040a42e40920500f0001d00082c01d01124072003203607498250a400e1445a41801a02e5030491811a50240300c41ca2899264900c01c40d1144400c22100c1c06401006130128002d10586c0c0011564a40c2e84403540040d4550718001e500d0b00c3c0b40380c81c4542c441e8100803e080c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 867028974 1250 867027724 867027731
    0xb1c020c0c03071815030b0105010c1415061014030703111303141018230f0303070e040501080703081e0705010f0c050304050604020103051906170d0f0804020d0204 72
    0x70190781e028041c03880100036161810f8243d180030070740321040701c01c8180300c1901024000c0c002c00001c2c0b81e14030700604550090800e501000c080f4109140c024009030031040b028040c0a5504c91038104520f17910b80500f400303850b40c801d00000002c0036200c41100c550721107a20312090001070b096521039003102d600d4149524249017840001c1072002101300c46504120b4680d030720700c00e9a03080060200005100108035150502000d04a010a08031540304e418000d044001e403055414080618450218a01100141101c1c203054045201c00d4a076001030340d05034005550035902540501e41800780c14180c0381c005015000891650b0344143e0541d00000b002004010f01c1381200740200c02c00c1c005002802d008600102d50f400d50720301c07884e00300c031403810140d402d0000a0042c0000304070000f80f41c80e8407035420b0800180c0354964913100b400d040244182c090007a4200301c0003140c0c008440d4082000e240720101150741c1c10703490001c01c3d901c0c4100406030700c001811900020b40985810600c40311014000707880003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 867030224 1250 867028974 867028993
    0x604020a1a0c03130602010e340b0a030b190b040905071107080705040609140414070503010903090f05010509131a21060c190302030a15120b010b1c020c 67
    0x5003150804ca0b18500c01008088080103011740a000724803408500c1c001404643d0119001c01d0b0b426880351021010000c6184200315040d8041003c00024041181100c0e813038a8480a004010b402d14010541c058810340001400303034501c205004042e60081000301c1e040c641002c400a000b090700034282403c2007211035102c3c022071030501045d80a810001c0c098131a650a0000740820342d100d0303501500707086190040d900034614500921542059000341c0d03d01c04140d49403c01c40c94984140c00c40c55040d4600b0030000c0c1010380259000c01190100304a01c12125034440040d10729004080a540c8c000007030003012210f00340581d1101e03504080315039240c6000410a00401d00c004450b0030808174102e040c2100164424080100c0303507110142094061414881038001c1551800461501c0e09240e004004500c1c0c0b508036402200941306440f030071520407541c510000b0041c5c03006030803c0e00c803c0e42850022442c4944c000031682c60003c800240e05e08200010b600200960100311015068001d44407903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 867031474 1250 867030224 867030247
    0xf0e030a050f19080901060e10140307081f050a020301080a020603040303060f06270812160f0f031709030313020112050c0306010e0a12030c02150a0c03110604020a1a 73
    0x320858140f007665144040d04d400071165007110040e1300100314291103074040002202140704041e090b1840c0701440ca0320200c05001003072170004203801114107401392401c0701c401103111030f005415009075502c051000ea01e4601c803e1040303100a01074504d840d04480d0325440907081142c021a000f038031034500042c1060703550000c1c20942c04075402c004001101d1602150320090981c1110401c02c9040d00182d0700a80340005c100d646080303110224000d00350102e80d100ca020440c8158900a54000303403980385000e42854406465009441c044001c45c0140f950b1080e400d00c4108090310841c0b084000318038503140d00c3c404c4c50401d81109401c0f81004001f084110410b03420b0b014450040500d0701c1c0d05501c17409d086001400c091f40405015020b081a50000c00a020780d004078440c40c1501810452505044d500110700f9007524800345080031704000468011080c2d0211100f21254047c2d50bc1b2020030350b06446180d11640300351406544403442e4881070160940010841001d021b001180500e071a1640d0304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 867032724 1250 867031474 867031507
    0x2060c1005090c120d08010612020c010603080d0c08042f040f050a0e0f0a080337060f03020607020906040e191101020604050607032412060f0e030a050f 67
    0x2e03000b0701900f0003c0c81c90520304140c01103950800240016081d61212804000c009040510601d02040800c11a43c4401c442c1e13941240e45142140d8003d2062985a0a103084140c0c801c20000050718901842c0c103803c1c0c0d1107882c00b60700981d8411048440000c54184e44140307000520345800000160101c601650380d43d07441101502c2500c0c04020509241a8204004941c106207082d1441d8200140c0f0601c4120017242c0000e8071544001000d07100d03210401c40b80031056034001800403c450303d01d00c110300b5a421824945002d100f400302440000c1e00c8a45403243c007401c2d440000d4100310148104030041c6040d40e120f0340c0c4070201410024002c81d4400780c480c80c2c40d801140074001f80c54032040490500c2444115001c4030300080c0020012810b15542ea2995102c00074800d400b099991580d4403217100c450b0b000110141f101d0401141015228203904104501c1c500f02110024079141440d070104040e4003c0078114008800990701b8032840ea02e0a0350641c1c00718140c0e1054540400c03408203800e11561 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 867033974 1250 867032724 867032731
    0x70609030f02041524030501150c0f02090c0301030b010f211b0902040602060603060c041a120103140607030e0c011805030111040303110703020a12030216090f0b01180302060c1005 79
    0x413400782c1507218070510540c0800301090001b00760500300140064603030052094410b0080303203454080f046190401141e9030403e05402903122124106201a102001016605a9004407034002d0641da0b982519110180c075071152152011410000030016002004c0594185000e4040030320050300c01c103c507070726081d80c640200d444a039001c0340c1440495410010780d54060400d8001300500d0a10b05005103040c00fa42c49896001c41107042e403104444a103205580d882050301e8240141544c40e482c00c4640900c0c00f0102048920648001800c1d60348280250403291414101400c004503610004481605849015614503920042d00140c4c0340c41c02d10845d00450507031100a41ca8908518006044100c0c00c014440554001300044c40540d507081500411213000e0300c14041c805d81349280503030404d01c0000b030010101040b02c00c0001eaa6042d1341245c0c000400100081265503001001900c00524007403180c0740c901c00c3c0384418401418220028050901c40400f01c4520f00d000300c5403503080c3c038001c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 867035224 1250 867033974 867033989
    0x2030c06071e080c0306040903021c0f08090312010e0a090f050c0324060f0f0907020604110d0506160c08031f0909050c0d1e08091002070609030f020415 67
    0x4400c0045880040390046440d407841c54598010b0130922051180d9000245c8854422a642c042c03031002c050080101c4034489100d240400140c02d060400949104c403401c0340300c0f001c1031071400003d841d100040200e4600c0546102c1d49042642040c43c41046500d0081a20f0481642d8140a5010908144420008500c100d00816030b0070516010305044c2940310b007442000b0b0b0400003c001c02d6485241c030041d400070050740e0190302d6510703a60000f60145200407030740340c001124030700340a0303015070214525100301d01802d40814540e00d071400740914040c841c0390107440c1d6089040803425480001e0450800c64425182c031030240c00f500d0301ca20310b41d540140e0b84601e04080c4600c0580c14890300140c200b004041100c010000c280080c4c46131903d03407601c0315183c1e03c82d042c0810100e0801600303002003040d00c6036600484041d08501c5c078041440e07605c92604a0301c600e04400b811070b4041d100180c0c2c00241d46072079807210689031035a40e411000014132241240d01540307602002c0189500302500d0801881d070b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 867036474 1250 867035224 867035237
    0xb131508102910080a0f093005070605180304080f01110f03010306020901180602070806090615061c0507270b03011404060801090303021207092402030c0607 69
    0x120340110440c942c001580010000100c5451a29503954500442940900d00b00a10aa5948648903004156a82d2540b510310f1911082ca010702034400c0c00c0500c03d15412011361982c00000200d041030342e4040305840c0015004105090003d5101d07000190018031a100500d94081180f0807141140c01540100d0740941c0110032000c0200400d000c0d2044d1810010261403600b5000000304a483c0700500000d80b0958000401003c2a4850380b0102071101942615840031b40d02c03440001d4582d40c5034400d6012512500700441c80001d80458204d008a608145e1040d400802c00e0074400349800040214180006031030310314000810a0140d46c0c420309084c4d85071140c0700e80da45810000044850000e000100f4803440030f01c4144401f00490b4103407201c212141c5410050b00c40000c0203020703c1c2c1c000036842c3d400c29007441c0030140c064000c0d00301c0c608042e01000040e6030342c103000c031044800303072040d80d003600315a4000740c244102c0400c9900700c0b0300385071042e80e203404d802042c0f661070140300b0395442c80007810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 867037724 1250 867036474 867036491
    0xf0c1c020105071a0f0114060301060f050c1509010605090618070512040506160518090603010209150d0b060c25030209070f1d150a0c05060703050105130b13150810 72
    0x1000c001a0251190604c03407404004d010020500710b000500882f400c1c4219245000c680f14060030543d14030417500d0088500d191117825a081502c042510550741e04c0d03080a0000c103240c079000309010721509024140482d030a20000e170281c1c40d080042d1540043c0b190030400c00d540400402d200074403a90007400149801c0c1029004400d03071034115203500b01000424400210080000c000c554070140b000c5a0800c156210080060300900c41c0030160340c1c2c0300c455150304844040001004d085641e12031a010044071485c403040c45110b22a0703681c1414240c001e075054202d00c1e0f03599040348180143c0d0b83d0820040540380c1d400304215000030740b076000115440a51010445502404010100b4031144c884070180c0700150115900e200c1e0151111200070b03001c01c800000790320038103040100c0ea0b004021a0040c0c233141c2800340007040e0038000d860040d0794990750361041119034069503003548801750507202000a000c0d050001012601d65403080070406400004606a08202410325400c101100203103016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 867038974 1250 867037724 867037741
    0x70804240e0108040209091009050601080c040b0901120611031509070f02070b0318070b071505060d020d0c0503120a09051008010b0705010f0c110f0c1c020105071a 72
    0x15003003a800010020031a501c10740d140d034420180c6401aa040d6800103807501c589075603e0030101401e2240c0181c0349005140c1040c4500060380360f040710091000ea441c0150000c052006544664692a4001d1552001003088050584100006500403140050003228400505545500540e98074040340400c0044400b50719107165242c2d00700c50745e81014580c00c1485071010b0b440701c0b81071058820074800880090030310003801c1c801d103c00d56012400d46407059201d48100ca6141c1020342d050b50752502d414a900040b541a200c0c4a009400c0244802e030850003580c00c02980c005a01e40454007049031610004460f101000650021140d0010b410380f00c04682c24000d02d00c01c2d09611151043c82010046100c20b038000e14254190343e800010a59a4110303800d00a01410380c10841951031442d1003125400241d10110301c0d03995a500c181510701902c682c018090b5920050744600381c3c04241031070715070f8802520b09003540d1900d1043c100b59081c4450ba131140910a5100045081c6801c404020005c041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 867040224 1250 867038974 867039029
    0x8070c1508090c0409033c0810050f031c08070314010b0d05071b0302030301030c080d090506090a091112060a060e01030f1b0c060e0f120f070804 64
    0x540381ca05010180381a6900e1035075504070101d000d00031390780c58004005261045a48622400d8500c11240303008001d92100386c6459484c10f40f0085c00ca0301300c010085030381d00c501c50f258003c002c0f0441c098405400c110811010340414010301e940740c03241070b800591210902c00362a0b07465816032100d0440b8645070001409407449104c104034611443d41c01404a501184103903011840d40450009256480b440103854121100c490000c2c400904c44000041542c00001181a81c1c414400f80803e95620502c0c4c95440c48845100008100385113818040c1d400e0140242410000c01032000004a80ea40e0041c1e044892800822840c00c3c00060802e43c0c000300c502c0002c3d00200d040e1543d200d81450104000c140f9002c01d880030b4101912442a501c00c1a1b90350040040615000d8103032044001500c8060702d100380480c1c0c00c84401d8208620800a03002c0401d0100808083c8405842210400d40140010b580180c41696007070b102484544041119000a8000f800454504445d1350040c4040007100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 867041474 1250 867040224 867040259
    0x12090c0812120f0c04180207150c0c0f020112111801020a03021b1f030e21070204051008070b040303021221040501060315060905060319120c08070c 65
    0x600704200040303801000c8800440d0b5009140600b0311103207440c0d0074910402e52250341d000d1960b603411800085c050140c5a4004c1c0602c51041c0c4504881c12000400030054a010b000700c000032840440c81c28012130200c1190104d10391051401240800544070000c04403107601080c0200c2400208a8005c000740260340326400c15000d000402440000c0d41d402595200c0c0c04038100c14200c1035030381200c43c648507280c01d00644410780c130644802240031500240105100100f400c0144103180400c25510040300394040d01c007034115101c3d40303402159001c0c0030103000e01925400400d21100400505130009101010182102c10606a50381e46503046c001c0c43d240c13190019040d003810800508404034111000282500c00a030042d074181d6940b402c0140c0100740540c4003a04180141c082d018501e07215a0008040c7d070359000c1c0412090710f9000626030b5999100001c0f08140100250460104c0c001c4a0381d205405418589407102000d203648030002f84c1c005520444107030103800300500c041100742907a00030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 867042724 1250 867041474 867041503
    0xa020405160909020f030621030d02070b0a1e090302030706111201090c020a060e10060308040f08060103170304022e090b09010c1e06090b01060e0607030503061012090c08 75
    0x1c0c003100442007117071444064100d0344074220110b0b00d00031035410b0500b503500c010022002c2d0b039140c5400c0152003000e03607c02d18044440c0c0941ca400501160301c02d1040300d442100c0e2800f890545220409148018075072400c055082d0f00c010300186001642a006030000c031904015101c3d1140c1c642c0c004220020b00c1a005444c07945d00300042c280c804c0d030b40054403c01d035981052000c10002000c110301d90070144000d6581943d05d041040220512034417034020310440c1c24880c98140443c1c0d581607480c2d1500000c0c00b0041c062030500400f01816000349000d56000b900041c00c02042d400900000e03da6140000d0b984008041c20020b90786c100381e04520725000401007030340341030300d8100c178403000906984500300c0081a4000c2d85660b01c01342004100c540d00f0096010300200106840750401d019800b5007445080001540c4ca600307888182061819108460341c161905400c5480c0d100400c003101b545000d19000700110241340b52142c0d00c66000e181070b080c4c041d840a908803418000324074144444a0312455 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 867043974 1250 867042724 867042727
    0x6070f02090f040b1909060f0c09080f030d150506030703090506060a03110d140d0509030c04090c030602090d06090b180313030818180a0c0c0809120a02040516090902 73
    0x4220f40101480d4002950b0b080c5d105403107170401c00e0f80c00a00d58001d0107003113586000081401e0f803502d90b01490704100b40741c444a445e07550b24542c455581d40000c0031180160401e2040c0001a92076400c11100401758145c442405070300e45000c00c010360800c80710000080d48500341c0b6070600030188542a0825419901c60045504540b10640303080e112144290040c026050010103220f42107204250141c1e142c0c0a441440080e000020455007220380030610138040e0300009501840c02d032007017200850f40808251a05403840d190320000f904482c0806401c914800f100000003003852103081001c500c00c0060304d03140d0a24035840b041d8400e06008003070480d4000c02076006a628180071200807a98080c24481e03031042e400403a00390103640e19040d075400c8041c0f0702e041480000c071040560300c038490b1307030904100740f001d050402c82d20040402e4002d030030354100300000e032070900f4038019020100002030b0460705109494ae0203d4210750040b5940b488400b260303070901040990084640b001060285400e5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 867045224 1250 867043974 867043981
    0x2040302010e010815030105010b09041505090615070c09140a1a042408010204080f0307020117060402090d120909050c0301050103231006030518070303180506070f02090f 75
    0xb030010494072842606101301c0c1000100109504050103451700c0c40900280815699242c000d02160007042040348294207011041203041060086903044480051152000b52903080501c08140040200a4083d0200700500404141114943d200901c007081000814402019640301d6565019003200c1b4603d0510041c0b0341c140d01c0b0b0003800a13030000c0c2210b00050380e400704851000b500c0080c11004a80c0c40c03008200207a622019400380040383c10701030031b50703445076860820307a0340381d109586000740842c0da1803070404907031900c40c000c00d83d0004020b80014544003440001030804803085100710f41c5410000304140b080ca44c0655aa8010a070328401440309051050b08034805e80014040d9504060340d075500300c2409459100e41d5088001e12184090441c181000311801e94150381c012500845d0919020801a10f2016241c5034007800c2e00700644421400d6070740c02c0b03413102c038540c7d0300050301204d08001080e1640c80307074024003041c0e02c504104058849c07207205201142c0c20007065220a400c402081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 867046474 1250 867045224 867045227
    0x3130e1e070e1e1e04090b150f0a08061906090e010606120c080f0a0b0d0f0c0b0c1509121b06010b13180f0e0609060610051c0902120601090f0204030201 67
    0x3104881410120140020081280803900a11b000f0302e01a02801a003018400d031500e61401240654400350b54440b54420240203001c001c2e1050b2040901c41d030b001000194075054641c032412440860410085903469455081c001541d5604004812503503642000700a2a5082411140c00040d104014480d0016001026000c01d400625088101000d000007840f01c1180303038096002164010b2460040d54035900b8549001801407038211413500b85070704045049030078a002d403182218500c005140000707501ea00b04c16020000303080714445108400c1d41c0c0d142e445142c40505200130102d2440c24820921807112440d0500c1a805000c481208004044582c00702c04a05000c0c2c6c1c0c0310101d4104001411324865000386400201030747c560385800d000c41103050003c51600e00648040040300c10741e8071000c08010320f210268001070007003041081024500d01601c04c80302c4450040e1080040c2d40762480c0c0200c0d1a400e01282d03074201903003040340103000940b00c070b21445610822840b030031802c09045a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 867047724 1250 867046474 867046489
    0xd0222080309013216020603180106050103090b06060702040902130207050c0f030304060807020c040513061a031b0607060e070e130b01141c050606040b0303130e1e070e1e 75
    0x1646100340c200001c08000c0c3c80e50151703100ea0b0b0036601400b141e0756032070103a01c80c00700d80310200244003d95082c18800030f4990312038061182056001050704940341c4400f002c000e295401034038120b0700f054031441841c0c0540c1d01c010611510f139418203409070395868149050340c00d001c50a2507140c4200074040e8080100d407400000daa081c1c90361400d10615545074014207920b03140c0c000c0161548982004100018844c0d2032031400c1c42030f0f11418051000c001031011030311506640c0200613401da444400e041820a162800144008101504640c5403900c0364640c00280c420500041c003ca40c0304407420000c2803817001c00c09074401c42e03524068030441d400f41d0311716082a50602c00e510b000e4070890781c0b2448a550b0112103480040300100064040083c03880c02e1612141e00710b4102d407150b40b030300c040d0b040d0b241804811504117210145e03030240c401c0e05204600c80b40490150181d09981d034641100c2d03290b0070022003035500034a10b6844a4a1500540c010445c51800001c48500c0d6640c4d9070280110603281c822 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 867048974 1250 867047724 867047807
    0x6090608060c1b01050108010c12020a0816050f18010206012403020915220f030809040c02010b1309111005190e03030724110d022208030901 62
    0x281d1580d185803400705000f008800165591040d4a45000041c0c1000150b124401d20006138a40005a076245e80b80b04080b80585e50645001c06c60b43e400188100c207410a9580d44149e0a08005003401c01001030040d00d80c000111904850172540342400780343da01040414014400c14041030000112805c11030403030707011002c1d8070b000c5c960041600c010994803010443e0304c841c03e1120780368440544140d0848130401c01303980d00180803a10400030a01d0f81c00b00615200303890b007285144d8035000c01d20f4113000c003c0c0001071b407480455581c0e0404950b542c1d0303801805540c0b00c40c031400218a40b180c46c20b206c110003e15456203889508000c00c044011904102912002c00320007051071f074004100302c4207442209114a016505004c00161001003103d50114108002150000141042111400d040403101304424a107003059060150644c1130000750010114010003442c01c0c2260315001c84010040e40c05500042c00503000802c2460055030700214902e910982c0310a64501581c3e0742c11900d0b80602c50f00b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 867050224 1250 867048974 867048991
    0x10e1009050c10030f0b060307020c090c0706021b0f0102070c090c20070f1401081f0b040b030103020f09240111060a060602070902070302060c031306060305030307030609060806 78
    0x1045030106100c41400001c544010152122201e5685008010001c0690b214600c03021440d2014080050600c90107992040c1043e40082c03c1c1d410400081044489008044d43c3c481c92041102c4000076001d4000341c80e001c5420300250b03008001b038050960030f1010314105c40a90342c0c414030a501c0403070751010900080b11191000000d944882a01c122010114440b440d007011213200707001100c540c400656107040714480c07900d001c42c00740c072003403042842c3c500a070b4030314005201310b80455a102d205104691001c100e00e001c4104043d45d6005050f16504268044001c4440200c01001541040d108400d408101102c00400a1908000a041000800d400322428889802c03890140d6402018070f103d842e0440310841e00c0c11300c0d080c00d40300090000c40c014040180114500050010080e000f511002d66164010b0040ca65500c0f2035040c080e0402081c448000c0001894080820b52070b104000c00f850050020716070302e1410140140c20b650715580032001d801e00d411802c000b41000481d4450b0080a00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 867051474 1250 867050224 867050231
    0x5061e0f07020a1b14030309100806010504030507030b01030623011802070c090c090506031603052e06030e030c0a08030402030a021c061b050306042f04090608010e10 73
    0x162071003285801407444004000070b0801c00c0e0004a00c0c043c0903181c0c1121191340c408181c1c51440010b05840f4000d80040a81001e02d950301c0b649810700900c551a030000d0103142443c20140d50f919158038140b1381364400d0310005405c0c0018002e2040b14054905c14110401074103106222808003c49508014455421820101e4442d000b034005160111590503800c11a1182e65030746a00e9400024030f69001d4010118130b4103840000c0c1400c21200f5207105400603091248916205281900900750051050030028081c0142c00c1120000b00d40051401440036580c0d5045801c02002800310380020003c0c10003544140408c800782c590009010304031590229100d6202d8842c0d03c0880d1400b1b002c21002507000400400d0707503a1106c614030b0740e2020b481c010281400681052041c469150803890401400240d0070000a46982040e420175036503880c060143e0700599510000b40110203204541d80150f260700090308100144a5002e1180944000c071300030400c20340d503801c5c0d441e900d000e00c15061004944 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 867052724 1250 867051474 867051481
    0xc0b07020c040603140709050c1204020a170c040c0315061b05010e0a03030c050415081f090f0f0204080c010c1103010615180522020f1605061e0f 64
    0x109002801c14800d0251042c028140c40c0d01e000c80c001034145e02c40a50368440d00d07000042617812400b4041c058400034a00c5464103961400304102000018030698202180010000b01d020000010071103002e2280094259040031a0803c1f00b0b031403209030300c10105810800c42801d42988140c1c064100d440c58140101441400765001c0a081e114000141c00d65107084a0030807268404100d0711000c5100b90340c20081c90000c06c40540d1180640e029540405c0c049013000c55042d03000312111a001000d040d050006200c0d6101854602100e5800180700c440e2981c03c19807444006020b555030800541c80c1c01c1d030600d0308024030940e59080c0c002c1403d04200030340b201a0188039403410105601d0f80c02400911400340c440e00340285100022165000092a8a08010503105c00480b00e00583ea0010b03d40c02402c8544201c00c015900e0400101c1034041d130070041c14022202a0303000340142510489000c02020381800e00e00d042000081088070544c1d0394400b1461010b940b42005540007034400d107091403944 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 867053974 1250 867052724 867052727
    0x140f100e0d060c0e10050f03071d03010c091d01080303371401170a08030601110703050a1412030103030f0e03150108010f02040605090906013510060c0b07 68
    0x1505840a00301619064040e000c0551005451303481c460261242c084a50500c28102c6d01441010911a03072268140003181c2c10603c03800c15145042d10940504030384801110001c1c0c00c43e0900c401070b07c082042c0d09030810041c8085408201c080d55500990300d2503600d04128141c0701d1000800031801901c07549007540b02c018001e980444189504200114170951441c13140000300282a008000c04148500000c0c4400c028031541c48850a540068030240c00c0640c2d40118a13040504140d06011a10038000c0f000d9004001c14401107000d80001c0c541002a801d10050544108141916540240f0304580d01085404101c904480d031500e4542009401e100c030484451402e848895410b0164000d80c100e005480704069058604c09070003000f502d200806900c0c12446030f8841c2c0703c0800d106010703103151850b0101200d5440304040c101102d0200200d00900f0940030140100340803882845443c28100301a40412688040311414003440141080c2d0302415480e0207480040547c2c80e55000101004e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 867055224 1250 867053974 867053989
    0x12020d0b070c0f030f08060a030807112206150503090601031103030f0a0806030f0c01210e0114103510060f051e0a0e0403110a0309140f100e 62
    0x20340c1000060f19007083d14030b00240050b8150018100240c0703202c001c102549031420180c01129072100700d0502d801c0d0544d4600304030f41801c8075460340c4001c46000310705418214450101c0002c44a100005041e402e120070418110034028400042000034001c201e90b00400140c09415660132200a6407240e100300000b03880d51146c015448a003040201e00741c0b600c00d8101140d04d004007021011341d881400d004004582c0c60245900701e9000905030840103d4032003181385074a00c640391000020a422080600346030030b494842c010040f00061076410040340b000c5800c02500580b0010800039070000c82c041e684074004100500b103001200c600e5842e050504010403201c050210500002e00000d0758940d00d030001091544905ea01503450030a091542d200d14460010848900034041c0510340d003450241c3c1841e000043c021001d12505406008919508001d0400c3e031030b01c2695039801c198100f108643c505199505840d0150000809802d8180d4074a010000b07a03241c24a00784400d500c0050009444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 867056474 1250 867055224 867055247
    0xa05060708131d0906160c020409020d080306090f0118051e07110f011407030c050f0412021c0320010b060c060406060e1006050a0e0603090106090612020d0b07 70
    0x755000d040009000b641192035908001038003603d1488680c1d80c0d614181d141d07081125128a4a05030018401001e40075015040b22a800030340005103041580c0c0c00b04049110420b020341e0300c3c0502008005061500d040c2440d844410500a0710301949824030104440101840110406480314001000303008040c5400055504c050404201820726090241210382040c21018050040080b0050f8044c3e05014008924206058680043d560443d04070002c0c62024464001c014040040c0e07105206110050700140800703a541d40888000d6104102c0c5140e0f0380c2c0044074000d10200300410200e44c00c41c2940020b41a054071140b806602c424ac0c5a00400b502114198485400314001e444160f001554600c101d01c56031040052603110b182e400700c154401c4511200440901030180030280c410b10181a80001c2070400d24143c840c2d40c0b000681580040352921156035580d9010401d840701402188000c003480616410304d484140c003c2080c61a403e40007600035410b5101040c0380501c294080000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 867057724 1250 867056474 867056497
    0x9030b130f030f1214162006150103090515150d290f041713090e0706051e0f160b1503060c0403030e01030605040204080109021306050a05060708 64
    0x281d449689005020f58401c2181c0d500066031102e03070304035040d00900c1941c0342554041304a02c1079584505503088010050920303207042007240600200d0284425880c2100c4040041c080c24140c0b400c01c200600903205036900c1c40c105410080808003041020039003014403411211203040c1640e505003076882141c02c40107402e4028081860303d0007444201c00c10720300d660840440d122000c545041c3c00180e0114141c40c42042102da80b8007040004e42e60000e003104054581600b00d0412020401050503243d169100b100c0c0705403681b400017031102090040c1c002900bc0c5090050400810103244400f0290a0002903026507000520384210f00500c070645003019016101c001e119486454440e04425055508181c41010500071910924012400303620486290755454100707861a00c04031540308000c0310f16810716a541da0b0218590f142c41c00148054120130002203040ca0300d92041c0300c101111520713062651460003d061141340c3d00c10f10071404480b801c803030309901c0300c1990906820500c6000184070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 867058974 1250 867057724 867057743
    0x418080406050a030b030a2d051b0102151b0706060306020703050702100824181f12020f060a0909060306140c03060a05040e150a0218010f09030b13 65
    0xd5082d6000004008001c1c06640502030340a04805040d40c400500100404d21040d000ca1400600e4071081141d203c1c50880305050082e00760364450700d08012692404a444001c8102440850b50b010045101000201c0c45144900d05d08a0b4100c1d88215250005040072100001c0007000d2001c190002c1c000303150000340c00c5540310b2862501030170691040c0c400728040c18001c480c20040e03d009000b450311605101d102c01940494000344449920011300800d80c0c0a0701000401d910342e081c400583d40b0451061200c007800d4001c0183c00b150f2810980c0c04002c201c041140c494006880d4107001056000066400e00d482d00c01c50038054500c41c84940020440340d1902100105110343c0360840d5050140b62941020703940c542040e481800d110454a690f001101608204514182688001c3c4083c40c503009603502580010480010090300761010f450301500490303552242e0a1584103039680107000d080c0402343d018002c2000d06004118480503010780c4c01038000401c505907101040e03000d20740c002c0c0400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 867060224 1250 867058974 867058979
    0xc011b17070c0e16050304060e150612072409080303090c040c080721020417030403060b0105030130060c1d0103060503030714030c0f1507021b04180804 67
    0x103052600728000581d42085485000261030720485815806114401184000c44c4e100100c151703915803001d0811520302ea942d130395141a0840c00e0028140f0900e00000402040c1054803c1114602000d01e42c00000d030032010702002082840310b4103112041c014904d07040c4100340d14906031a002e0b99580442d405002c00000c110308140085082d15284504a4080140130070403101251840002c86448000c240d105d40390074000039140c10405d00f100e1070310802514003a110034401600f05601e8148041c3e030752000c203091080000da4000c28410400a1806a04561400660840740c80c0541c00325034038503850942e0151440e02040d51200120b800440c103100030840715200500441c0384001065000c001e1342c508400a610a00803030007140c4008009606040c002e45580810220220741e140840c030007003002c5280745d8010300c08003d8454840000e0b04502020b1034400c880c0f00390080c484021504400a9400951901900c10f05440d8050310005259001d500c09505400c101c803402a0900b000841c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 867061474 1250 867060224 867060263
    0x309130615020303090708190818060a2003070b04030818030f040303020c041e0e10092405040b0f06030a02040f150b1305090c120a1a010206090c011b 66
    0x15405101171408545050b995105050344512080c4403218008000b0303410b00c00440c103107201504900040035041000c00700d2940000e14658406545900858850401d408082e0781603403044080b80392032000365203408569a5207280c4000000c01c010203000703a14020881c80f440b080002d9003511004011a584d03a540c0f174617410640d4000e48011401449603a44a1145082600403e41402c0e40c0c0e43c40002c01c1e15501d0809000f5100c654035410991148144100040c03205000d00001c907802100383c00c9886200003030003481052a04003500c003580c1403038140070010b105040f40690105070080322600a4a91000184c10082e1a01000e54054108090f206802e20658440b00c0034840044126898503603402d20700d80e2030f003d402d00c860260401c40e2400c00143c01d1400e035031540704018034402031034500c01130b04080c0902020b5909101141d82d4402103005010039445c0544401c400740020041c9142440310306580340a00020541004101d91200003210341800000007182c0e40420501030740403043d01c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 867062724 1250 867061474 867061477
    0x120f0c070909050105190c0c081e0d02070b0f04200411030709050307050d0512090613060f03050708090a151503261e090d020d0b0f100803091306150203 67
    0x240303e0303902d4092410301c1135981410b10440d02e03a907c85882d041c1c00501641c40344000da412850440403110095056105074560f004001c09d500010044010f880c2e40703450400001840000302021303140d0a0b0f10003800f0100d500809186045054021801840440d04020a000e0300003121202050380d008010300117000d400800440944a0550480f00c1e559559030810400c20701c105009006900801801d60f0031401d850024180c00c00050011480c125107c1010012a40c1c01c1c1e00501c0000c80b00e021210940390f050040079000303c080e140c0304a06041038041d0b15210096248028659180007008248605c03064220443c10b584001c0d580f03030400e5481c20044001c00c00c150b10200c1211801035420b92020b103400a0714103000000c03800744241a0712500c1030790140d1000310304940c4140e41c0380102006a58481c403151055100302000c1041c2d0500b50f1140165410160400c0c4110b8203c1d14144aa1000042601c02d4007000300e40a4030b100362030141f4000186413a0b00b0110505000f9910b02100540000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 867063974 1250 867062724 867062731
    0xd140112051506210705090c0c0706030b100f0207091d01060e09190c0e04200a0b0d020901031401031110020d02150403050d050f01080f120f0c070909050105 69
    0x4142d400d802915484110080e0084411541c0074580c500301252541c03070942050030040b01101200d1186486500042032a04110b84c2a00e01000028090420f03030030a1110b94010a002e05082c014099540005196a50341c11018400c004441074650480c1c0c1c402c000c0c1100501c010340c000c20070142d10103141c079590b8480500d401055800c22000054800000826920504882001d4103030060710301c0d07814446102c20201a10813442c02d01c00414414024032030f42d4055403140c00101501440421240c1e20708a0b01125503110300c5440100b00185070000d0b0844565848801740160780e41408001600141302f221220500358008400101c00c0051151a14402030821038000321002c02e90f040407070707841036501010001600507d40584007034410440881e00681b107070038001d060641240030320b8101d6800b2103520049480607070042022035800c0c00101c16104e212800b52511700c40340f401e451450702c01c1040001d541c3d00c1c0000c8082140801340000c3c0c028000214041c40301c0489070404601810094 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 867065224 1250 867063974 867063983
    0x80d050d0203280e12040b071b0812071e02090f07051606020c4b01020d0617120412050a050714090a0903020d120b120303040b0a02040503030304080d140112 69
    0x12080500400031710003982c0842d09404519440d200f903035629021954000d660040d80103a844d200481c42e41400c1c01a80d5016400e1603a40e5112a01404c0c2941d2540020079800381136260486101c1c0036883d0071710b80c5580800d4400307500203070781c4038408115050301ca07a00b1010742d480713852017241302004010f800400c07030203c0d050b08584074aa46ca0068000300b94440716080781c0040e01155440c406400ba5a284001140d07a10004845030500c2d004076007a60b1049000e0b008071503440038284032941c001010202d050310118014603600c0034802ca0703102244100e0162170000300c01c904141c8100030080006074402c0d94418240ca140300c0e40c4038031080c002c55002407007610540700500001c00384a81841610500380e09540248019844c200095400c14040007580c40d2a07903d03004919500d440b006195010113041c0d4004642e24981400d00d0038160b00060020003180d4010002042955000826260040d8100401c40da48040c00c062160083c025400204207403a883d0780000b40343c0c00781c0000546500d004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 867066474 1250 867065224 867065233
    0xe0f121c02061501031b120204121b0b030709090902032e0612020a03060506040e160801050f10030305160c06032f040b090334080d050d0203280e 64
    0x907400645c250340741c10400d01c58460407180b220405512418511a0008102d40018a80360b1174a001e0303000c03117982c42c0095075614021410b140c0600e40d5003076900000c2001c0c0491500754100540024001c0305a445585003103511982d9a40566800f48142d026a05035900015421080c099183d0311000300200300e4070380280f4018000500c2c444903005081c4290f402004919290f05644d01c507401010060905034115546641c0c4a000040421402035410328485004d4820380c030b0a9030305401e4400041040035035840c0d40c014000400240103070301083d030794507007421611803403422181d081a0b1003007900a000502481000a00140c0585c8400800390101d0002418400e00c1c01c03001c1740a040340c90311650b0301a801c0200b04442c481340c4000c1c1c4001c80c401030070782d07030040d0740b41b00003c89032051001c102005564115494900704100075082c001030903540c020304204107848034080c0c220302a180d002c0c4040350700000010f4240342480e242c204194440040c4d00c45491191903111300800c45801c001019100303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 867067724 1250 867066474 867066511
    0x40c020f0d140d0e03130803041e0f0605091201020304030c1101050a020c01081f090506091f0e1510020a0506150d020402092b120e0f121c0206 63
    0x1042e024041141d0351415003030329020202480c4402011200700300c045030302051110143d18180560a10001d1194000554641d81004a000054003054020701e00c0032009035010084112030301c03200000c48002d802c145d51906101d5020502e100c1340c0405502d040c1d4400030401c0304043c1c014508400c5a8007070b41001d0500e80401005555902c10400c1e4000541e0011505040541c400d40510b40c1c0010100305c0000f5074440b0300403a607000390702074003e0152135880b00100811402c1ca401190703070101c41520345e050030036020b40051000d010b4500540d0000c10256000584142142d642550481f00203048030407501a4213000030340340d446840741141c0d5401458081404c03007027912961142c4540041c07174081e20100030307070810000751312100d003d035000f5600f8141a0340400303441d00703207501c141c40c52100c0c900c00300010314088290300c0e031182d881801d04c0309500614843d03899441150006200a1303402e00400003401ea0310610b81505c08500080002e030200c107070b400895000c9115805a8070b0341144014022 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 867068974 1250 867067724 867067727
    0x191203020d0e0612150a1403010c0306050d1709100806010e0f18090f01020307050a120903090905061f030207020f1516030e0a0306020c0d020703200a05040c020f0d 72
    0x112000c1000d80c0800240715004c1100000324a1980000303200c48142e054010580c04070b8070244007580507403122011803880c02e006080a007d11551840586010402c140c10900006d50740c0020440181c0001548000c6548443d5403100729041c092004298103021294108014060807048a04900084503201c0c41c240780d0074201060801c4100c01005d91102c00101031820070340700c030b0040100c6c803244101051100c0009003840118002c01040c1c0d1040d03030301d9070610000707442c0628641c00005414038120007440469403200300c1c0300c165041c1000100d003a84492000550201d0700070440d03035040a4035620810700035019402070448600c00d85240d0350071046d60040004101d8082100c1d04519401c0280380041c43c068450040c403c0d01c00e060200324180614045032418090f80c1044a0b100d0f800611004490010010090624414401095250305564031510421001485180c0c400b004c0040e16605a48001c175000c040c20303024004028500400c48001e564884401400c015401000b20088509 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 867070224 1250 867068974 867068987
    0x303180f18110a09050a060906020606060304031101051f05060f1803030d110a030f02090a0311010908010f060f0e0408030c0a110316060c020304050a090209191203020d 74
    0x100c0c825668160410300c0c11002420189403591021099580c49150401c0050b07200040d1541c29010b546140c103150500f070600600070201d41001c03092200980b02044021b80c009051584100241d406a4483d100d42c80c0a61305505030001c803400d65400c0404000058610818a2080401d0101c0c1c00000d540e581090000e188039040c00300100f0352007000017041003c04404411541d03000502120f103447d008030443c030202d50812070007103003603140003400c40c407529454001d0800c810f030008401c5180c9088070001405540e80c521000702083c11441110401d0307805404190300a1001400031b2080f1a0b1071081c2c00024016406211601e59100b180072034076140d9408624031a40c0e010310100d16640303d0030708e84410745e00921041d00030400490b002c82f2048000384080e1151118a0b200d6200400082c0f80c410155010550381c4011917005201c02c12080d902c2d441e84501f1291210700c0169180400c1002c40c0d1200c150b442824030310101702c1d1001407500803c8400e00491806a820b031032110801031002c8078103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 867071474 1250 867070224 867070229
    0x702041a0f06040e04020f0a0e09010e06160f350402030f0604080a050304020d0c080102030a0b120a02010507060204090c0906090b040b03061207031e021c03080c0310091104030318 79
    0x49800704c0e00040040c10038407003100c05100c3c001c1c00d420f1030a40d41c2507100341c03c0c04200d4101036103035110070740141a40c3c0100030713268003d05104c990b0200480b030391034010400080c0f0540c1c001005250039202c3c2d080c0814010303000003403d280d40500c0c1206444c03603201200d40e5055800300e00074811031084400d500c8010551034021a4421443d5180c844140802c5680d604040c01c01d0740e1113650f140c3e0490004201c0d4000800030612180090b84910389110b942040301c0c0c104c96100c0c003406010701b0b80c5206010112300c413183c4650908001f0b8a880081c20a903000f800703141c001c0107000d4034101c0420f11054101c68040c00b1203500da40c0e5803e5440e15240080d00d2400b8500c02c410340b03a40c0910210b40b00d45401a07070000340000400840344103d50300c0d00c4403400c1c60b0104202ca0107040301d0718086425820300984094242d110b2100d042003502155030b0040121500400f40085801d001c0003140d40445c0c5080110018108002c0034410350740300c15001c00d90340d80a88400c401240c481c0d01104003250070401c00004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 867072724 1250 867071474 867071489
    0x606080106080a02040509040f140c030718180309080f010c0903021017070302030115021f020a11030408011a030105100e07030213080c1c050613080702041a0f0604 72
    0x9991078840e003034460a0303015018511040d000c2c00b01040680799244c01134400c0e4090180400054881e007040c08a040d0b403090100816044641b80300040c0c0c03000a082c90440e05120030b00c402c04600042d44100a01c1c419611080d80300c01c44444409142c0d008020f4000e607036124064441d001e01d500700b26801c0701c3c00c1c40c000380b0100c5c16460003000985090814a02149400c0c10040981c150050b142103040c1411035141000c02d038040014006070035042c001c4c0c4692050340c00101000403030f03000c8541d0184030700202013400540000c2c0c40300c8031074899064204648000e00440303499607125514540604410795035001c0da080c1000124000d03141c140141c40c000c0391195601900d070740c2040c0c0c1540050400601e50310a143c0c00308100c1c1440d454400300e1070000e00094025200c0d20300c00d03070200408a240441a100740c0d13032510ba0700702e0201e40302194240d0410081d0284025034103080c6008040742c0507000010f9809482c14a0301d411804161074000c5d0f6005041780e11000990031300d001c00106e401640151034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 867073974 1250 867072724 867072737
    0x1006020c060d02040806190605060c06011a040b0a050a030f0605090a0c180f090e0a0816170a03050403080f010b04061b4403150415080f060a0606 64
    0x65036042520040c404103920b010054a0304d51200b03915890301d4001d44180b2181c00d4004c0d8400711400305886a440603020440fa0585003c182c0881c2c10354604060080140e0903404000c281410490380d405c49008200048980740c403420700810143c8036400000460300801e0500c0c91544084c3d006204143c01d440e4000c1001200f601c55141c9000100201a5800180884e00005040035080e5840940043c4440682185000d040540d08810f46441840741149a44000c40b020f0003e6200130554a03440800241155905020b04000381100860981a401314900262244030251b05820040c401e0b400ba07200c1d0406621000486006142e092046024420040c4814040d0070700c200043c800800040004c60311403802e540701c0031704425a06421190390081309040b034031001070000242000585080b4440200c802c125401c0440d8031008000c01410400d0b034415a10aa8480c0c4c40000b050100f007000a00d10380d201d0061070303075450092410803184d100c0c020001b1b030305044e00d006100c1607503400d41d6440c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 867075224 1250 867073974 867073993
    0x12180b0f0a030510030c080706180b07020d060f1107060e0a020609010e01140a05040314070501020703060203040f140c030c0909100e030d090302030301150e030a08090a240305100602 80
    0x302c00800014140d8072100440e09400004079000703d2009014080c4200078007030b403614102c4083c0c840f03919000042c0c61900b00840400507954403d06540c215501503070801082001362070b0a8009000380380401c94058504803000c004801000d000d40310042c031980081101180c0184215034600280d04001d500510800c540040355204075420f824151060503d401407003a1850300b041e6170f802c5a609440090b00c0450100244281260301a4142885c0b401624506d070516000075103404080c000527007840d4000000c40c040129840f0140c210b00d8001c1a040707484600384100036240e40205d08950310a1003003c4003402d052819117292405019503000620711032a10880754800340090141c0da41241c0000c0c0512007401000d40580b01a45120342d001d55503c1d810050300d51100c444200740b10040180c504800b5034140c90000300d00041c0307a0032003036080d129165080099a4858150050712140d01c0700d912620528400b5450050340050742c0e1000d0006070798140001580c2e9046100d4000140c0c0603a655 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 867076474 1250 867075224 867075227
    0x7120c1103190212010204030c150e090f2406030412080105040c0504090e031c050f07052d0d0e0105060901050906090a020a0e06040e0609060a0f1a0712180b0f0a 71
    0x113840da07814848005402e150b502d0301c40c401142500c3c2e010081410b240c9448074840c81d40482c9408051404560903007040c142060741c1c5a4461000780b011103aa810020611401d82801403000e81010004140c40d40c2c9241a00d0402c1a0305200010302c0c0100e501c1d1030000c6154681030045d110500c0311a56040d04040c80c10002d0800f034046600c05140e030340001c0000301a5400700300410381c800c09040d0b0b00030035641010300301010203010041c4200200601071141000c2c010b100ca503851400e40160320704d2145030723410340740680003881220703e407880440c03404400e412021810341185100b08001c4460707488580c0c2c0d60061261540048458175480ba210700001000000c00b54050304c0080450318001aa201004012410550064000441600d002410421680303060b9024a0f4481c80c00c0d02c04e01e05507450401c0e28103040703189005040044580c50300201460740c094083d90784e100d070400607034089640014000742001c4035031400f00342d54613900c0340b0100340d010504003200c2040d4000c007c3c85d80b03056580b060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 867077724 1250 867076474 867076489
    0x110d0e010203012115240e06090610030e0706020d090806071b08040504050f04060e0a020907031d0111091e01050d0903050904110307030f05060d0f050307120c11031902 74
    0xf260440b40700d5030050300c03090345885640e5a04215000c09106016440704055005c550391f80900400125a41048010744900761801d0f0407060549001101600465040e00a0000e000e2004618441c3c8500011050390000e900c4001080075150280402c0c1c5540300c050302d40c0403c84404020075000c01034480c41e1020b407001200d0b19402022454181502e80b00020309440080d078224030707400b04403c248001d00c5a288200024042400c00405178950702da4003045100400a20803800c0c07503a24400100da9080d0406003000408140300204002c0e000c403d2102d02c1a0083d19460340a022010310001000a40880f4042c64550503100c09041c550800d9070040580408641101041000d0001011980300e500034841c0503102900220340780d02d40400300604540c0304088078000141410140070740f945901c00c40b0006076421154070044504503042061840c41031500041c4114a8401c00c404111f90250380384400d64400c034591812480110b04055503005c04d5554075544125058010005190035075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 867078974 1250 867077724 867077789
    0x3100f0c111b151e130605030415020c070801050412030e070806010306020904060b0703030507120902060712170708010503060609091f0e03070803011406120a0c050d110d0e01020301 80
    0x4683c1c524120034041c803d4030a441d031200b400d40d02c0c02c000c00d83d01ea904101e203400c80d0160010386425401c0d0b160030f84891420ba8a124148841c440c3e0000d100c007071408050010310040c0502400a00140c00c00d4544139200301c416068540c0024030780706400d15013000200382c40301220100c00c0181070b030342d086403140d00003035118204090384a5a181e0000440350045c0c00640344940c06510002a41c0c03400000c080c11891a000b51218498581080c410059858205680d842904044580801440e00d10152548040c1d02111000e400040080241c02d59014100906032202a001d444140d1603640c11301918540940e8110000d4111409034081c003c00481522501601d030340300820080c90b541402402c50340300d01c200351052040000140000803050780c020348002819590380c1d2a1219411008404a102401d0089480d0711a005012098480c40546141d40704034101001034044202c911072459000032540300101b801c2550110080318188240c0e4102c95403c0d942448040d40203008032942405107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 867080224 1250 867078974 867079009
    0x60c0501060b0a392003060915040f1424060901061d060310060305090d020303040b0a0908030a0e0f010504030e0d0c1d09070e040c1403100f0c111b 65
    0x1181c00788032200c0c0540f44c40b102d40d8014030041019004e4000ea140c21095070380c03192030003540601d00744071140c60300081000c03840344c003841c20b0040341d11940b80c038040c0c4001d4010003a06018a0103007101c010f0380041040e21492107081301481c070600702c164140325030000c111036066006107404010450701c0e00450001c116003202c800c041c080794055100040f03240c0c0050f117a8044d2154040e0091002c60b070144203840c1c100c020000148002d4004e20b01c000d660b80300040009080d0341c07420010615201468101d038460540c040103880c0c8034602a10004000c250844001080e88100d080c6552160018410a402290150f40d400c092552440600002802c807043c11a1030804001e000120305080041510981d18010b181c01c2c46401c10700001884c101c2e403608544020401481404001101010003004861003080502144512000080e040078000d8010982c05420054801400801d66000c0640729072203840d144200e143c01c1040036a905069040c0d111001c40f886007554007854041c00746400e21282c0f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 867081474 1250 867080224 867080297
    0x50d020102010e0a1103150606180a09020c0303220203100519021602031e03030613060302121509030403020607150e0a11090f15131104060c0501060b0a 67
    0x11100c0d452402d54485010317a114041d0b05124a924a014081d02c00c503440300c010070301004d06154000407418810380070035000e01346034503c1045061f04c0d4220118010312201c0c0003152541d489044550f22503208541018641c2c04107a1f004c581004901d802c0b1040c1038002e03009200c86030301c81d00e0f6100103142c042d00380840340682050700c02410758103000400d00e60170304c0e040c445204080f61052514040381c210305015107002c04c40b412004550000141e82c0e2000e4115490549240c06500b500004c140c87d42001e5041000c2200500b4000000607900301c0c09030607106034401503554600019205d004e94080258046400c20103a40402c45c0342080c00030342499900001415114982200c1c54020449812214803802a0f101d01c1e0610b1301d10380032a84080000c4020603507103041c0940c0031000e610f2001003446400d103c600140900c0680e4844c65103d0703a00d418155980d03448000162620740664401c6480c1c1d82090030210b07040b2418010b5071415621521000c0010201d05201841070b110340c424110302002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 867082724 1250 867081474 867081491
    0x2040507140d0905010e062202010903080c01051006091811160c0312030b1507050a150b1201060302010e061606050c0919051003020c071509050307091104050d02010201 74
    0x30700040c240030852080c0040c0f458441d1410a0940b5007507020002940c20000400c00011040b08491241c404a000c130110f01c0d00103840180d030030044540000d0009400820700da81e00e0328055201d94001d110500030b49080d59078503c030854000949015801481080020840d58074209401401d03000c2c009503200d40c100800900001070b03a040c00766041c0c9481981d14000c2091140d00d1150158111141c42d0601040c801100070914190a0b100720034152400000c1960074000301780112144591300134142084003000c004091b015100300c0c41201d21039201c001d00340d248408144141c0f01202d44c1a111f110003a400c2c0c008001440d048880040c0601d16004141400102c0921565208120041c000c1f038460785072406015802035000e14071443d18007580707002c0c4141ea070b9813610f800e1300d82c0d080d1502680c0c400c00c04136802e0602c40264012910406c2500091a04a410840300d0007610400c0c0c4c100da6010760388030120016108011125105002c04010500481c10801c803120402801070001048545 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 867083974 1250 867082724 867082757
    0x2b111903210c08121e0f0f0a020910020c0a050a03120e0a1208120109020307230403050f0a142a0109030b07091e0b19020118120e01091202040507 64
    0x40c00f000c045000205000100175032120008030380b0759111010300d60b1803940e24203194a4109a14090015840d440f41207000030441c0055404503080758401402010800d511581c0c00384d5218030741c5511522410304201f01180d14200808124202c0c2c1c0c2141007402076a04010003a02c281881c1403c668100790745d58004241a94004880e02010340304500b80c030303075801c110b02c4070024030003060701321205850042041c0f041c0e00c2d91009210040c001605103226202d10400245600c51099500041c014000c82c0300e4500c20b0003012030031a03000780c000d02900e81051030100c0e490b42c0f9103250021f0717444141d403207059040c1d1b00b5400c015071102c00d03001810b03d400119181d844840f00700c0c0048402000184021406000303c5581d80514040b12a2401e03200340c82070f00f0039550325568024440804000d852aa4032076a00600c02d40103540701c1040380d601c070000e403c1503040140c00c48036144c91700300221b440001c0d0041654403c4030084101e80240d1240d50000300641d00300005040041e083d5020071408440020815 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 867085224 1250 867083974 867083977
    0x31b03070918053403030804150b0301090b0610020a0b0f31030306050105130902070c0b04120515040308010b18060307020c0108090705010c022b111903210c08 70
    0x3605048000070008905955010000d1000d4081c44c09240358850400010750007d4001d0b801950120122040414010a140050641c0131074940e0541c00e0120803000e210280c1543e42c0909016600c0c0000c1d0407210000380d030382d042038010080203502ca40000460307620342c883e40319401446030442c040000c488044030004400c202443d50b05460300c08810300c020160107110303140081900f03003006400c1c9210301d980340d0070200503407140c0102e080d00000c084042042580c0c41d00064a02d100189880300d84440f44920100c5408408680c0c51080900440c49000c808040074451380d41a907405040b42e00341003608995030400042c400c02201500340240081d5140720180d84a18640d500926030360704090001000c644c006003441c1030f2030b08495424411039901450b1750401d640c064540c03081030101204220382c4400c807110751403100a00301048070104000b0707004844d01d05800301d562041c940003070a8980e00c10351040c80001d00c0c0170302c45150348880c0f002c01e0043c01028889414141014000341c1c882d040ca5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 867086330 1106 867085224 867085243
    0x10f140c010207140d17100308090105130321031803031d070b030f090d170907030c030501020c0105100311150d020c010902031b0307091805 62
    0xc0500940407030f00d80f258010800c20100e59001d60b126101c00c402803018001545a8100100b1500321240503802a00e540c040400380c24919a644545076100d1140f10303052110500c02c3d8202d001c0c40800c6640214041c00c0e1900c050030b514507202d501d080004d00d5840a2500d08507589111807030b82444920382a0b41400c0014400a021098055051161002c03212500c251803000c505d11046401030b50255803029004022600e90540c82a02c1d4000d140d60344000526028031094030b031100500081c0c104550505031481c0649070307224050480902d400944e800d0b900010001c0c8002c01c24841d09502000c0c10190300c90450540e950741052403803103040c240c802ca180840750046280510204e0b140c0c03040c3c0b02011552a505035413802c1c0a40712079003040c0c0c4603001d8600c001550280055a901c20b841c030007400340482c0c9090000410040c06000880402d608583d08440002003081020301c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 866906474 867086330 := by
  have h0 := BRFrame.cov_init 866906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 866906474 ≤ n) (h2 : n < 867086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
