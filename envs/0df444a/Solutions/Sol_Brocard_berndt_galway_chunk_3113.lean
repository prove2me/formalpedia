-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3113
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:41:46.273049+00:00
-- url     : https://prove2.me/submissions/bf65d3e7-80ab-4da5-88c2-e6a878423211

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 559712230 ≤ n < 559892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 559713480 1250 559712230 559712239
    0x6020c150a0c08090309060a110a05010f1a1203090d150c2601080706030902040f0507231306110304210b09010c120b0102190b1e0106020c1905 63
    0x1e00705803030303100700070b00c0c0c1c586011000414801c00614883e400008a9200355000340c04075290800481044130340c1101c47c40303013504a00400c02c003580403800c24003400c5009a0b03800000500440117002c1c0400f280350490405002c1d4a0241011005030000b00640d5072030b4109903051a101c2c5450320b024010307100031142d0b42020a04e00a50640841c0d03002c01c0364005400d0041c032401504406104010b8201001d05c112681030b8808002446040d04c44c1e00b08812031032015101043c54000900800c0a5a03003c488544c0040d901c4050880b40080d01c141d80042c050310610071505d0300c00e880b1105401d100703560145206005c0380c0d0f0034600e10010f0400c2103500500c5585c0c00c0c03005269402a030130303640482c8810152a542000c0000c40d0701440c040c40788200c00e000f2910f4861f00c10540b09040c030041c0c2110b03901c940c1076000750b928a9040401a040311a010307071050030100c080b46026045505402c0304101148070b0081920010300c0199000079203c04032100c1190813110301a00c00c40c4000c48201c4680009803c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 559714730 1250 559713480 559713523
    0xa0b0c0d020c010b03010c0c0b010918020d15060f0803120403050c03031311120c0f011e210b06070f08070f03020606041d03160503090405070c0b010b040b0706020c 72
    0x7441c2065105250200d0120003d101000c03001f001180e07440c03540034000c1d000b40c0c0c00000400103100954040541415140c1030051402000e40005001e44101081911608480940c62040910034400c000281108404c2540341c4c0781062100f585d03034080c440d40482850725600c04641414041d00a40e900a83c000c0c048135903130721301480d03211044d402260045503d00b0701801c20701240d14101c191f030001c20482c000206242082901000a1182c2c942465030501c0403484044907032684a104402c1c4071001a150000d900b0b100c007808021042c52080d1810f0054545902070503660b80340b10481d17806a0700030380d0440030408141440d02c024851820020325081030780d6052420107401066091056500322820029082d0004002c0c1c45801020303032507409a0020090521b80d1240042c14811050003a421242058420408070301140c0094034214045079940d80e805081040d0103030541c1c0034200301c060b82c44c10700c0d00d0014201d4a5000b83d810051001c0c0d00420280340a0b0001c10100391204207140c0c01ca0315 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 559715980 1250 559714730 559714747
    0xa0b0a03150306182d0303021c180b0c120c1c020301090507170606030105040e0102090307080312070f0e060705010b0d060509010608060f0f1b04092c0a0b0c0d02 71
    0x2903078031801d07000c86024640817036003030302d8104000c0c40d90440c881c4800b038000d40d21400e0b50210000c1d4000c0e940d1140b00f006050118000c41c03820301c904131025030407251385000c40c101c0e4100341d0000c6000500191140504100c048581e4100d004099041900049040e40358a1002c1194000d84010400440e4013440800000f0301c5040b65003020303024443c00e84810b1500101200844440b05040340d0160b081a4100010000c6080550200050f41c007040001420519072800003418424503504c0301102c0d610102d40c0700d414920403140075812106c5402c0554580680074000703030035032018540031880750202003500828400c082d0010940885e00a00100e20a000351030034000518054400420a42c601600441c05c020b001411078018981c0140417442a0b80d0907200e40919031000f40141d401c6c0344c107070340085101c80303000003d000a42682c5034080340c4030b460401040e002081d14031240030580c944110000810744003082c0000e201d50002c940322460350720030510003d1032181058240680340b0000340c100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 559717230 1250 559715980 559716011
    0xd0509030a0e011e0e010302040e01030f020111031206010806011413031e0309090e01021209030a08150904020d080c0d0201060905060d0215030601091a07030207050a0b0a03150306 79
    0x407641d1056114498129142001120001d0245806440003014280d281c00403a004403102c2001020515000d40342135211003100180481c00c6c0c0c0116418030506415608541e04480030000c150380d0b81e40258100f01603c0c145c0c000710f40c00606181d042c1b24801002c5103981e481100d406d80c0c2c100300c0098880d40d6441d1904c05055031000c51006a8030001e50341000740c2d8000d003414003658070540560f40c0130f18850410320740c00c000740250750203101159401c1081400c9410750808440c03044100e103000d03640710071203480080e2042c80001c20702c521490340b43c0d884c0d1805a4901405c0c0c1c0e041a0107540e2014101141d1505100360705c2100040b00e040c2c800da1051002e4140c2c150000e2050b581c00d1442801903480c0c5d40d051100e41407400000940c40034401c240c20f040c19280078040c0d507114805150414403540c0c0e46a1134882d13070006a042e081000b030001240014507070100f1030040102803c0e512014031900c0d01d400400326000311401c0d03008040e1181165954000d5139034081d40030355008802017010140032540340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 559718480 1250 559717230 559717237
    0xb2a0703021c02030f0d150806040b1801050c040b16021917061501120b0402040902070b090a030813050c03030309030c070b0304020604180f1d010b0301090807060b03030d050903 78
    0x80009050100c003080b240c404000e0324240f1344180021800d040e0306000c1040900507841c11fa0042c2100b4060004403802e08004090155008101c6150242042d020000c64001404090741540e0b05100034400d10000180c1103400300c1e210204034540319007000100c8566048140c202a6103c00c0d00e072113001141500b1035500301250641c0b001c0300841400c900000b515500200c2d044402c0701000c58021000394000c8641a0500e10400e00018000000c600014220380040d00322800450380030a1034810090b0303010311560040303a00402080c107603d05640061000303400038001c0750511610174078401080b0040040e0310360410002d060743d0b282c0c603241d0345403556034101400b101c00c0b40c85007040c0025003041d1801128003464028141900d0142441d001d02c509109620744a0a025502c50961001c000300d849140390388030070100c0b10000700250111803402d640481003060305c6039151241c80c0b07001071071580841e441c06612010100b0080c280000007810f41c010442ca400c25207040004008000c000807004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 559719730 1250 559718480 559718503
    0x30f0d02010f1802101e0f030c030e0d1b0b130201080610082701090302330a11070f050a050d0809030d110409060906150c0b2a070302 59
    0x2000008842d03107888007580c03902c4031124481880c1d01c1041000d0304001c0f01380c0c3d100080c641044034035840895202000f0580c00d20100001070060401c801c5a04d605010f5191400c0492506005c031006039107646031980115101c08003800b4031005013800c0d00188041c403843c980d80190114125283c003480c05c80003141004d104a00107500b01d800600f5900e40039003500704111495543c007043c0d6036008941c1d82c03400402c09241e9444a0921841c4403040d800340100e6410034413075406400549409040d040381040350f68400601210f03000c0081401203040380d41c8030317031264540d40080303040420219006090311a040d00500030701101031001046c0a4001480c0d4119486841101c10683c42c0001c100c3e01c0c8002641c191030740e41c204000074003140d4103a03003019079113454414600c0c0c6041c0d641c1190b00e00302d440981c04032000710b440d4034017040400300440c1070004204d55820f0a41a1480c0c583e52007071806001440300960140400200f201c0940c9030b44a8003501c0701420121f40d030b540d940d040107943c4070a001e18 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 559720980 1250 559719730 559719733
    0xa060513021e030c030a02090406030b041a010906120620120405100902010c0b07020c061908060a03050d080411150c0c1206070f0507020303040906240806010c02010e030f0d02 77
    0x740d00b001407081011079100301c038080300b25403c50702c80031a2500a98040340c0700d2948191104d4020003c40d1000302101e000f58852100100410800c00020f010040140d110346402858001c1c20028642c800454550059120200061002e890100203141580c0040f20084400022030800c000604a203009800303540aa0200c6001c2c680f60885041a104000d0009000851001c0c01000142c1c12030291a0045101d00640c0d01c0c070300d01c0b5000702d0b0094110801103519000d4480c558009540c206810030f4102c4001d5600c503585d00d01b10f07142c0b1666a11903100d0601007000c01d80016041c00301c0b0701005281c40b003000b06051940030044030703101c1320360300f004141d40c00c10f002e812000300d000d02c1c00d081c90b843d1001400c0080c20096551580654a0002000e098000d00604000201c0165001d000030300190891460003c0d00500304082590a01c0704031041d103824104007500348450b160812a072661041003460a50900e880350310040b00c03500c50540c18290113101d030304c48001440c6004285030b0610036072a030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 559722230 1250 559720980 559721017
    0xc0908120f0c0319090b0f090f03150a0b04230c030c1c0b040c05070c2303030c1e06040515071b1a130c03060c02011409070e160f080a06051302 63
    0x480c0d01c50540b0401c7c5203044240e80410040ba80d0f810801c0418404640080590b5030068950800000c488421100d20b4441c0342e0391a000c024030b2503d40701da4401c03010403038285844000720b050741e00c004910203803a0124094010001411301d561403011115130201819050000300d0816400c440078061180d03030107100c1d03070a2542e0b04180303602c10000e40d03003a140c2110000c1d80031880c04600c502c120304a5403c91100ca11003c4940d041d580b82040100101d60b400b1005286104030300142d105c5118032070201d0b0410350000b1303040c00301182c00055624144680d42102c0c0d002c1c0d132180c01040e240942c402c8400f410a801d41034000d01403262000a12080340c1031a8513243c081d80d20b0481d0b668807181500001000e42c2110307502031001c0f4569600c442c69111150000055004805804442d0342e4000c03903c0080961160b0700c140704511100300e00c80c2d040710340384d00d4108403200301400142c1041d03400d4500c0710400510b04009807089401c0c0d08440010f2001078840d000740301800d142c140280d803241e10703040d5007200c2d0300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 559723480 1250 559722230 559722239
    0x3030507060f0525050d0213140d0305030a0c180b18030106050105040e091203090a1401020901050403020913390e010302091f090501090c0908120f0c031909 69
    0x40c041e05101c0c00c041c1c0f125521480308503080210a911207990780003041018890100602030902c000d01030040c0d22340480300d100e4540103404086990801240340181071108a650000707400c0420384c0d4100c070880401044881d000c0c00c0480303486107240205986032807000b800003242c000b503038000c0202c1c0ea607406802503142244c038140340c02e84070b0f0b41c458a8005803080000304000c44c0301e1449d1030f40210100c070a4402034154000c1030100c0f82c109407201440750700006081400c0210788058007403102a500001e500300040e0a0019040d40036912010b40502d548500007030702c0200841084402c564010399020540004542e030100c0c42003101600d43e182d0007503809094000150b01d00d003004072110300120008980c00c40c0d003404100200501003c0300a0300110008030b10a00740b0010780007602845400249545c5060114015980e03649041002e000901606010150020600e0b2031018403000c0f041e070f0355076a28041088180f0800b0000d90042c0004100c8241c0c1d20460030280160055a69030380fa41c080e01d9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 559724730 1250 559723480 559723511
    0x61602040f0f1808160303182405061e031009030e011d0a0603020901110a0b07090501030203060d060e0c03060a090c0b0a020d140c0a26070203070e0606070c0303050706 74
    0x3e05001400028050012602c070f002d44081015020b0b2083c0340224007059071021140400e0120042220300d64281c551404215141c1d40103100300c43c41d01c0c0070600c2641880d1004c16001c00d01d20140349103801044480c2c480c01d8400f000b605111000101c001c00869219040040400743c1303940c062800100c801094a42003440c2d01d0f10220200001405002c0c49890018190000d40c0203e04650602c4140740c1c05102c42c050611401c400c80c0d004002c070142038078102c0c2006100010a400c2179041c10f2050041c41256107c2c2c50342081c44590040b40014115071100749140342c0000c4881003075261094404004441c151740e00150030a034407554801840b25160003542c409030042d0025400181d010500104219200741050b0a410044c12040e03880c100840003030a0400424076800e4400c140c1d0107200c8110100c49030f550348141244044114186461030380080c3e1111000c0c8034211400d203140c00031074850350b911421288910f41c8034880508a17603603840c018003182c02020741514100d25145000e059a90f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 559725980 1250 559724730 559724771
    0x7030915060317070302010b060307020303071404060f0f200f1002090607060c0e0d061a0102070803090405040c0e25090e04030c0302070b2d09030a02061602040f0f 72
    0x1404880c079440c10f4018400048103800c0b1200030340c210b6483d511014200d4481400440c001c0c0c00c039a000d95904d10700039030054051107a4201205104800b0401084001e41c0200450f50002040c94200101c07041e01c03d040b5481d42121010095a140e440c04200d818000000c05003c146a01c0c42500c0c0ca111009404108a020303200140d074012400b0048200061003c0e03105180840e01070a00c072902012240101e00c03041811401261060b80d01c0e44e10505582820750034004000c8244003d007502401d204542d0384900030040e41e240901e8440b40071034200300424980c1e00140212201e403220900d0107503400c402a060010915540398907800f1030a200034400c400748030503900c80e0008495103840300c3c1d400b00c0d0903c02c4484240d007103020700c5c10041104811080108484200116424080c500c4481001031a040c43d08040001c920300300400f004945001c245c06041c5c0f50116810b07600ea1282000c0c03541c50701c00002c0c1c003d51140c901121036400c8581d03540000d05000680408200c0f510342d0144500003001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 559727230 1250 559725980 559725983
    0x1080d0e0d11060a03180614161e090504020c0304050a06171512010f1b02060f01051513030308042a05360610020714060a090806070309150603 63
    0x6440c2d82c54003045041510040c12500e007146400607070681c8082c0b0300c4481540500d403c544043d02c0c0e052000604103060b0007070b41c120f0301c2d07201000c407000c65410000c0c01c1c5100c0d0316807404100b60141c985449081c09441104000e000c00b500540d0b642c1403040d051503c0380d015019041c450380803c1c0022400610455024099000c1c5050060031030719050303901c40c010034030b14500725449002c8900e02c44450030b00303001d1b02d0142e041200c00030540720010b014142c00411106610340171580440d00700014035049020550444000340e030b01c40b06001501e611440c0714450030042040602060600008140c0c2c0041518411406402c50166044a82460030165010034a901000b540006030a000070b203000940070659203c0d148110340782054000a054808458490762203040c3c8c41801004024103120380e814020399428030103080d0302410200b8003030000d155004441d0117001c0200d240580d41e4020207084000d80445401c46240e40f130200001009071441541c21500b90707480054840c03d25803e8011802a02d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 559728480 1250 559727230 559727243
    0x60c090b0c030a03180c0302190504150611030702090402090601020a0b0f011e0b180a170f06090105130f05070b1b010c05031006050d0239071802030a0605030601080d0e0d 75
    0x3035246800b040000d00c3c41c0b2801c00c0c3e0400d111127000980380c1d103034455003003c0d8000303108140303400d1301c1c0903400381901d02c510b0254a0f094104100c1080143d40d5844540c0d40564101c612300b50944403800101d207030403180e0100a040384011300501241000c00310002d4100c0e014014030b03440451074814444504c1ca440c2c440d10100b034106015002d03c1041c800c0d0b1609100c0b10180903008071641d14080889501c03a02c1c03043c81c4003034201880810401c00d0a01c07103298000b64190003406141400c90240c4440c1a4240b806030181e5110030703465041190501416008101600071a9110214410002282c10b102d11320b501543d032a00700c02d10302680c00342c0305581c46070040d04c0c2ca000006190036407d5486503c000c480c0300d140f507400c00040500d04151a081c3d0b00408402e000d06000d00c84018900c4d40c8403460025150203680321000801500402909482100d8014840503880352645030080020303150381d410043c0d00d80a05000407403880d000250084002045a4a03030048480310418442042000507000c1c049 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 559729730 1250 559728480 559728503
    0xf0305130519060f032403050c0a030f03120e030304060e0609011406130b030f03031b0708070f020d021807020d05030c19020a0615150302090904060c090b0c030a0318 73
    0x1c039000d6101a10246024100446c0c4c00708800c0440b044580c0708800c4183c41c41c5000d4003882401f83c00c1000c414114415100c5403001401d545031700809031030040004040021407400b1849004243e0000303026130b6554001c90380c4a04103803070080b001e49484544410320340309000000e6000303201405903828400402664202c50344482c4144900161051048031416071500703007561954030104616048a10150086d41d203c0c00c0c41203a08480100c82078800c40d00384003d0080c1c43c045120482241c0301c0c0c640c0402e00c00c00d113008138808200c60b0315608401035801580020880e41d82c0b640740401c1e1340b007212543d00f901c5058900950581d41ea00040c0c401c0d803000003080c04614010300c0c203010011292203540c0111007080c00990341d1401660000c0e030005441e9140c01070b041000040c40c1c0c0b00d0848900c09418290f00f4650040c000c42c6001800520251000d42c0701e100c1038001600890401c00500460b0141c1c42c0d68026040003540e50307a1200224000107454509094080c006d8a0750f00469560b03c1004070310b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 559730980 1250 559729730 559729739
    0x30b0a03110a0e0103060b03061608070509040905100f0e070f0e09120a05040609090204080d200d020c030606011b0305070c0e13030e100c0213090f0305130519 70
    0x15010901c40c003503000054200041180f0b484007002500840c82801c01103462404102410305000029080000300522040c901e00201d4000020701e034400700303070300e00b240c2c51714032102c0000c0150503940310107170580c0500a0303018840c0c4100e41128a1001c54640240b141212540b00389a0f0364440307120741e20004400450500038031102068240d0014070b100c0465020b10b2080709000d4140d8003131008040821400102042038981011688005001070038045040c10f2030064080e0700c079105205e2003410000324074583c600054800c1d05110925000400b10b56025030035441c0a5900e2400340500e42c4288584000500300c0d6110b2039200c540d00741000380c070041c015403035641a42c00d031700304400444001d020307104007040b04143c01c50114810345281c901c40e03420403410304029000c2403a030710016008400d040401d01e203483c3c01445481d9603580c1624000c140a0b44280e00d0f00050014070802000000c0460f030307041c203041c3d000d00900428401c07904102c18081c1d03110108901001c06010691030b180303405c0303400c12 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 559732230 1250 559730980 559730993
    0x10b16080d090602120708012702092103121303022d06070906110c061e0706050106091a031b0307031401090c02011a060409020906070b0f041101030b0a03 68
    0x81411600d84002c00c02c0304090f41c40c2c00981c0c008421160803011400100141241d01100c21030041c044006108003207101000405215801410100d070103540004000341c164441011104030007000c05a401342c078414401000341c40390b1000000d0b1056818510208014648074118101e440b94141c00500707000340d010582c104a0484e245520301e44114100c00f980c0384030014020140705446d50340d03442c4070103424280068010440c203802070600d0b91241c4001c1040b900ca80c01200d4a0034040410022424001810f06d1080d01c58003a0040405042400004550b41c01c003204c2c009590081e540c005520b0b1038068069868041255800c0c06603041d18680c5000b1080c003002540c0051720b9103000b20f0880c054040f2800c0c505002e03806106480e0380c40c00c0916520741d0a100d80c1a40c207103503000500c048008980040c58501440c0200a105680003400030295a5480100c1d541c2652061880100780b0740301c40100310341c170b00440e0103480ca046110031140d1151300c42e2145421065000342a000b6150a50700d401c0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 559733480 1250 559732230 559732237
    0x30403020103110705012a0f0807081308040e0a1409070303030f02040302061c0c090503062d0403020d0210020f030f060103020d18120504030302150907150e09010b1608 74
    0x1103400403020090320020031000c2c014a50748007440280740807032624100440140880040c120003c10044030390070062350750b01c41c6d0829042485407600400e07a8490b002121402d00541e0700040000400007800910b0503002c1c1c1072030348507090400c42003080d00c0206018102140048848070480c2e0041101400068026481640c040c00c03441b00043c10f040e12030340821860ba012811480c40016800d011202c614101d0040c0c12840c0c50601d0080c8603649800b01180c0d603000b020744112490a80310380c440c80c89185150600c0b58401c5850280c0a40303040c0390402a442d03d00384801c034001401009683c503890305c030074002ca810007107011400358910758a1920108800001814039410180c017000401c219402602614890440c207105501d1400118600a04405080c0702a0002d0000510041012a4000c2403020440e40d90004100c130300d507a070b03204946c10300019400c1400031461291070070501c6944138040891b1000241c4081e0000e988075030080580f8003d140001c05c22a004501e824002400ca0b40034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 559734730 1250 559733480 559733501
    0x105040c29031504020301140a05030c010c02040506120a032006010e060409140d270b03070f030e070905010e09010504050327120606100315060c080d0c090f050102010e030403020103 80
    0x28000f08801c5440001d040ea4402e80c450502c5840560030602031303190142000c4000c040480081c080c012080b00007a000e4500d20401a204681e1400010f03a26120301c02c2030020b04040b0000d44a04100f24034018241c00c00c00910a2400240031850445410b0000b40903030584120300490303a40c550b250410880580060a005c5034038408504039694503040400810100c0c02c055218181a600c803e600c402280c2480704149074030200035403040040700d030301c08100ca8000e8034500d00460031010101c0260040c041d0300e4200000c80c070810100040311a120351107241a20340c2000440c015445504110782a5602958003500340e8004000e41780c1540302e0f14845c5a924a501208224004a9540022400c400300c0fa00c164080e0005010000c4510f0108204c1040c0c443c6030401300900f41241da01041c416400e40100c20074000708a2042c410710169a007130b0303460300b0a440003e01017038415040040c03a4440c2e500c501e01040142c0840072a9540c01070003440740d41c0760300100540c10240340d90011000782100080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 559735980 1250 559734730 559734751
    0x302070b0c030d05011418040807080912070e0a0f05061f0306090509070e0c07080904050c0c0a0c0e0702030c1b0607050f010212010605250602090a080105040c2903 72
    0x4050700e400007600549001301a40f03441c0c025809254001e0141f0a003e181d090b24030112001c3c104000152558140d401c4590403081103516a1114004140c480840400343c0c1031a1080e54000171303200d0a0342c44a580f2800103010300b40207440703d154500098031307020b48049034042c48004119003100040e07144000d0b060010710300407502a50ba000b10b5411514282c1d207074015034010312005d20171000310b000c1003500324500001403403504103151942c002c0c41c0a061401403040b0b07100c02c0130500202c03232002076a59481c80700c1c3c1a51031a103281d16000c21103039658840c02180d034001c4400a0a51800481610b03800703d0510301034008110a400010f01000270f0040c3c1603070040c2d062011402081c42004000400702c0110001640c0e010281c00710300075148140c3c484410000c0400010b20550f0702c00141a490480c92902d03c030510110f89080b6001e801200241c9802411842002400c6101500028000c0c2d00070040ca401d03043c0c456a41001901d9202a6103001c00f03a41e4030141140300010b00115400740c5c0818 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 559737230 1250 559735980 559735987
    0x603170a1d0619080103051e030a0f0909020d09230a0602070203010603170d05010b0405010e0909070902190305090318090405121809090d021902040b0603100317070302070b0c03 78
    0x80c0d03c80300e5444011102000645440c0c014420400c0400c0002061440008400d01480051500541e00d10803032403da410004a4038002e2141c0c0c1c040e42013103016108000040d9103a1110960b82c074001c0c940c0d250701b80e902c041d0117128403c4541302010440c2c1a081910041d080f915a60703114100a54000001241c040d940ca01c4000301240c540720401c58009040480b0039079428005080e9010ba402c1a00200390b030b034104200400140c3c0c1c00014a03250010300742c03a01609a0703500b420311414045070358000d0304542d0001840050080750612100051039407520100001c1e243c101c8010740d41e0003118a400740321032015201c100503182200440303500c50b22900840d901b541c2c5a00d0b00720410781201c41d00c040d4060218108240e613103469040c842d8803c064400500003441c40d004003d51b9543c03030b003206da0b0b6982c1452180406549941d00302c070345020400340c0150f517241800c140030780c0808038920041e620010802003003684403014108030362445400d40d000b0045207050506104055110010003203c610040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 559738480 1250 559737230 559737247
    0x4150e18120a021507021203040209150d080d060e04110f030f1c031a13020309160e07230a050f070f0f0212030a090b03071701090603170a1d06 63
    0x8038028504103159501400202549040184135640c3c040c0455042d900000c10700c003c0d00e041402600c4c6d01c0358044450301038030380b82c10321510144102c4010241d00072050307540d08000c0c00f07507250003000e00da00c20601c00c10100b039403010384440b07100c41590000c01c0302c9a00e031214000b0340b0340301040e00200f04c40141036565400500245901d0400d451100070000d9001d0701580e00b00c90b4040c841d855031441c0c0c600c207119010700780c03d0000314131b0042d850300c10301c0ba1580403000c221550f40400c1b4605021400d5050720035141e03100c1d180062180e01c1116100c0010700c0f450780c81006a806001c7c10880b0040f50280503081c016800c80c103903201e4100450138102907506101c4840480d008044c0242e071180599148500c1d04520b0040c0700c1d00807a2030785420620703402040401c1450381d003d001c1d4000c0341c0861081c551251a404800c64044864884c500c522070409400442c2c00c6440f5802001241c6c820007101c002040c0300c410f060340070300880344120003260707140d44d000100b8068400040187c050041c01d451910120 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 559739730 1250 559738480 559738513
    0x3060607062711040b0616060b210610180b040209040f0c0914010207060c1a010611010b03120a0c02040605060c0a1103191b09051504150e18 62
    0x40c03000e0380d110b02c807609441d0300034003050210100d80c1c46000d0f80d040c421480d500c07020031441d1003600210311081e405080c2107030501c00680e0060076081c4004028806110ba0781d03280104040c3c1c1c001400072540201c001140d90030b05814074080c1104c0c1c503020400c5c0c1c490406a0074500800d017821020b40c0060b004c02c0001296600c0e0712603c0c0e404055103000151034018003400920907007503508918445000b924201405a8000504d80c4c11a0005d182c100d20004032032401503442d00429200d1110700d03046600103d009900503001c1c98100d070071080200054207461081507a1224101038035808014108403086043c0c4c80b07484142c42c00c500103003000c60342d0b135600c80c08101250700404283c205900014440e00411401e401c940ca0405001c400402e02c1c02c0c80842103d94000340c0440040118040840820a11a42c0e041503c010140c200b0104014601040101540e00c030740700c00c00c0c3c403e0345042c0200440c41c18039010304017034071138241501c2440d54486488020284c102d000742d05c4680701d20a0511441c104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 559740980 1250 559739730 559739771
    0x3090a0b190f09090b0a05060a0e1e090103080a05070f12020d230a0c05100b09010b18090919080904110a050703181706090f03040b0306060706 63
    0x5450101d5541c0103aa00034524000032200d03481c20030a030003016204050380411840f0544510303403000142d40550f070740007070410724440d03100c2078001d00e000c0b4034416035580000c004405a00300b5520a107042910b8454500220f0300040300c154050010001440854000c4002d41150510341c200f592030481d0941310181101ca070550103d411070710081d04a900c031513061001194000d4181001c0348400035108a01c1c6124811940d02042044041850f000f494406c1240c4003009070400d090320b0b000d840190242000e400c22102c558003c0901c40700010b0f515003000210307a41c90b45240301303105170b13003404400b081b403000806052001c041c881c12248039007910b0300e480d0121140d88505039540d0394810420501060380d10324400b180b800303902480303034440c0e1a4001086034110b5906152105030f20aa8141c401c60795400c030b0300090300645c1200001101c0b080e0016155001d030040404580350001519400d40c0d99104501822460b0f410610200ba01b6042034005011140d104a102090310ba680d0709070a00c5242 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 559742230 1250 559740980 559740989
    0x420060309160b0c1c0e09090606040501060c0f200406060302130906030c1401090b04030305030906090304050f061b010509100b0f1c14010c020a05070e040309030f0503090a 76
    0x1c02058001c0b01651190b07160b04002c141e10081d690411016042144c0c039680c80301d040082c010f0411121500691240c2c0b00110115070061440c011418130301070890b600c94080354124001c40c03803e00003117240d0740150301c2d10103542d500c41c1c1c002a241c010766442c203000e1103001401c0c07402c190b001601a01e00380d4850094001420840d074005845145070041c4e030745940d07150741c01410014544182440032860285800f070607074401d2402c06650303140d4000101c0e1540150380c45548141c1000c03c0201c20107034400025030003000400102e500300d071940f40000f9202e20541c4519a48500080c0d80c0c0b9895080c45009000300c012a4601c01c980034060000d19801c3d504101c40040d0746421802480c6041d0f40148602e02c0c01c988145c624130b08005021010421042d09055481c801c0d04002510f40c040000e69a10f01140d80e440302d000b448080d950360400303135407a4080f903400c40d8180100c031000300c1c4019040085611407038050303982101e13991440d2920b00c40d41d400c000043d01c050004008920064441a04020050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 559743480 1250 559742230 559742233
    0x61602220e15072a060609020d150b0a0c0f050f0607080a1109040b0402090a030501150803090901030201031d07120c06080f0a0f0905011107120203120420060309 71
    0x44003802981880100319280841034560001d000105a0001004403081001441122103040305440e070044e540905000400440c2044804102d583c3c03260050001000544801c1c45035001c41441b000d0600c61030300a9048241c018030214030624411041c9110700d50049a009080000a480301403c00700e6400706880c8a07030000050107400c1c0e0b8007084032030b40010542d004100072000b040038001280b0500c402c003841140c4808907450361384d8072907040760780f0000000e001502040d070b6071602601a00c81004040064451240d000802c504040101c6460820080455440c0d030b085500540040c40407900ca1030b00c80940b880d425010850400c91070340540811080050b03c40304da8070b0f12400c01245038110204000c916070a1101454452200c42d400580418004c1040504800f030900101080c64020b040c960030408071705090110b04000340355540c001d003040300354500481001c4c2ea0303d114480000700071030208070024012950500a020541410300b01c101611040100040c2e007036041030318000c041d07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 559744730 1250 559743480 559743491
    0x305130204022712030702012615010f0302040f030f0c050a0f0819031d0114040b090a090b0a06030207051c020c091f030204020c031603050c0d0e06160222 68
    0x50442e6145165050b4044441804c10444030600c15101d004488002341400031240306000700001140c0d09050002c0c080340001c0c0b5030310f07100600c40488149071100a0214520007003066040d8460300865060354540300214275840c1c0b855a4071824203222850965103205000380200f07203941c500c4210070080041c0030b85d07003c0c61403c2886490500321034038183c03206200894991000203800c020010311851400c01010300482c80100161400c4e1401d0884a140c58070000d0b020409082034800703031114940940e4209105603c44015804441d038030304509500560350f02c010042c59120760010b10b1100c0c031507025560032403c008980080b811060155a02580040340c0c1186117041c041906a0300071890040f0301d60003a1007402000b5010258000640500d4001603200002d49040044a0202c10001c0d103158808215080040c03190300140300444141c002d00d400380c0d400b20702c103c00070f032a4075000420007460000b504400329060640c980d0100c0e04140722030031381903024050b00310006607134a41c280e012a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 559745980 1250 559744730 559744777
    0x30203010c080f13021c06150f24051c060810140f070f0f050408070e01060809010204082a030106030804080d020303130303050702150c07110906010f030513020402 72
    0x104040300034100c00080c8038043d400c2d40981c0e06c44044130000b04002011181c07604940c2081c0300600b40c4540d5040ea01906003000040070341c01c00300c08004845c41035441d05c1020044106800c1098014010000018014012911301d448040900d06101c40342140000d802e0fa82e49904904100c1002c410002c1a0740d14003201404409001e120780c1d00c00c00710b52112205141550000d84040ca1494118080040a42c01c915446000b0f00843d800781c04010206e800d4a99076110b00c0c0d8030348809002d800c1c0007847c02e40c00304000c0d142c1402030b181542c0d03c0001078000b804030b80170800c00221203c2c0010b01206090703a5070881039102803054802860003100013aa07500d0030035109038a40009101c4003411940200f08100c3c00600d40d451b070038521541490041182e441f1400c04070f103001170100e4104000c800103002d200c4002c1d542d10041001c14458036211402103070030301c10014940e00c122034039400300b2403118100405034420b0744000c3e40003952032503404a901c0c040c2c012508a8002080810990420040181 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 559747230 1250 559745980 559746001
    0xe07090803070201140d140f04050d022e2406020f03070b0105040e0a0507060f0201050601090302010e1315030c030c08120409020703030605060d0207111903110406030203010c08 78
    0x5814031600961800031940c2c0001c0103281c0c0b0428581c200c0201050003444030301e458101c0206508a200000000d0034100e407041c2c0a030106407421103140c070039030980700e0701c803400416100c01200d103014010b140c07141c8082007800d03c070b04962003903600e803035440b4030030001a9448111001182c10006402881a042c00d0000c0c2c07610f4030088941d05c080d4003e024250000300d071140282c0c190754042d2004980c400044002c1c03442c0030840040123003070b40250240030845e03581c003c1140a001826138000d01660b112a0011354052400c1e010103800102d6049160065003040c40d0307001c010f20195900095500d00da5503c0c1134022601c3c2e0002c440000300d280007002440440700c005000f406100b0017038140001030911020b02880b42e8480c180c8502d8000c1180e10a140c060781c055001420081e100c16070368442c81800c0c0340250701030352007217541e030f015500200f076581090503591000070742400411040904545841c0c51031129100d015610640702c11000c001a1003e000d080741800081e22910000d003818100305 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 559748480 1250 559747230 559747247
    0x20d0e0402030c18060c0d080a0b0603070c0204051302030105151e0306040f050c04092a030201120b0a0b13080706030b01050d02030408071703060418121b0c0e07 71
    0x10311880c01032081c800c90903041412a885600d21904244203c038044001c0340c02c9004060311400c441c0200400c80c19141d8001040c41d00c0b0300b6030003608010340c0140f001003141501060f2000310002d0201410b010050400340d0001d0341041c20102000281c91086d030009003510703030446a60001d4065411042858145600c540c10036134082180c82d0178800d508400701e80c0c3d808008201074406403200124400f409407e000903a007a600161091083d050641030001030028403c4004030b1840c460f003aa550460401500d15050b41da05948607110001030381c1060000d40088600d455010451307000002d0400c0014004042c07001c925000845d126107010980c9003800100c8d4860010300d8101005e06500341e901408590f040742c5203010060302d030b803541d0078540464007031b001c1d0041035000b1000000000750800c0014511a2a00300d8040c40308010300d079841d1081c8801031074000c1c0035002d039601c60450305008070407901e50034860307045c00c01c080d040c641c4403610148041c0e371080120704520414854441c1e40207800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 559749730 1250 559748480 559748507
    0xc0305090a1e06020f03150f0307060e0307080a060b0f013209030a030903051c0507080309030f030703020d1b020d030f0609110301050f09090601090b041b020d 70
    0x410040c54040401500e41c542104000e10603846420342c0942000c1d070144203070740190809021902c40c82c1d801c81e410055802900c076140c2d88106941d0040040c513099204840c0b544c0090007401200f0b140140c103560540201078242d6050080c1040801c03900410015044c1940c014880410004502c03000d010700c040c81480ca0340d04001d505da0401d09880458964000360444804140000c25641c00302400b842c040d114a156240c041d030b1340624245640409000142c0303010780103031039800343c0100c4049030700004144446c0100c0c001384994008201418082d6520907285815245800040088040107610480740340c1c0210342d000c40c2c0101211035610400744070500ca04800704c1e5001075154080e6881c0d1145c0300c484c2c201901e541254142d08515045400104030704102400880d904424401031600309000d142c1c000c0740c000300c01e10901c0ca01802814000d0001e50040d044a908114850000d0b0040019054100d9114003400e035400b540100e06044c2991903070b01400360241308200c002c081d070402030711 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 559750980 1250 559749730 559749737
    0xb1f120b060f0403031d0a0305060907081c0c05102a030204030b0f0403110d0f1403060f12010603020d0b0411030c030318010e090f0f180d0c1a010f08010c 68
    0x89042c1c80224a000c40c1e0549426040060716081a418032000410150301000d40120000700000100080001e800d400352200303105403201140c640012640c0c95503030007808141445c030044403030b5003036000b000d011041c503004109845614424400d00c0c001d45120400c0080c0d040c084000c81e00808901c0314400520310812b15055142174999254208040c101803c0c0380483c280d000c01250416008650358100a800b44041d1003807030b550400090013107a0b8015410022070000200d01c080d03420b02d2007c5911030b00e00100004c544983c5c44041c0f0890203c802031511196599003000302c0940c0e038201003c3d0201e84208045042441c1500d01541a0036a0801440c0254005080074885550200944010150448003100c2c25807071840102c03144680d42c12000d4010b0000c04c00e01440b100d03250a80b40c8030b117218140e0551140c4460401c034035403460b00c4e1040e418a401a01a1010451080020b44070701d0b030140c1112410100c810030495400c2c0400c0e8030a01c0b0700040000e080111120030b0040b01c080a40301d05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 559752230 1250 559750980 559750987
    0x5031504030f110c180603010f060308070b0403020f070902090a050303120c0c070909110907140304110a03060c0f120e03071e0f0c050a270b1f120b06 66
    0x6034042c080000b111625414000ca105180c0c0c42e80c542000301c0040314100400320380b5a03418100b02e0030a41403060300c0c050f000c0d50a014408600320f0f6140258800c80358482c0003107141c80340b99100c088840740f01400c00c900314003030041304100e200300c100003420192480b400016503640c0311008002080c222503100310300942017072001c500380181c03065001d40c1c003150084005940b4000c0c1c100c0039041c8203141d0031007942c55141000b618103105000400c0c4203807903c140c41e04601d44e19807050594464802d222801c091500820000d00010225480c14502c601c002e48488441900c0f503403018151440c24500200082180140317000113507200c40c10028804810008102c18950200c1c425120b2292840182645010495011042c459222101031140e00007812501d509040c2ca4241c0c0b000002c1e02c00c00340700790384158006c2145400355003040c01e0b4024500640800d140b0380818000035005c55070015a00c0000b000c007001c40d4040c0c04a44070713079412440e5104103048102d03244000881c0c0016030200e020701c2051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 559753480 1250 559752230 559752233
    0x30c04050d1a071b02041d160e090106030b0420060706090605070e0a0303030515060301080321060112090201140a030c080a020f0a051b01090c05010206090c030712020a080f030405031504 82
    0xa8910141d41c1c05440106983c000c03031f42112040005050004c64510407600f1400711950b011503944d0640300d0f404802d02054030740c40a11800d84605000150a108a0402203800110643c0110b01e04030070345555544040c1e005400509545c201400c162101c80d200c101650801c100c41c40307107035405456810169429480140440c0c00200940401402c0c55500d001088500340c0d90901c0544418005040f25603d40c4c6610000d500c9070001010020720302e20742e95503a40c1c01d4141990b402c1c400d5038103031369151441c907040e00d01c03c0c06081c07035410503814010098400c2d0420a0310724010000c02c04030340c4000c590b100044000030301080004142000c0350f8030506c6005030350080d810031942d122040c1e00d0501c1d100e1800c0e00303402c80700b01300440030940c0fa0b43c030b840000c03070802403a07031003400c11a01c0c01d800341c5030150f564401c800e0b00c034107403d0100d80d4503800502081c0322000301c07042030904450019103540c0c0d841b911240c030780c0e250440d0320403401c0e00340e070020a0401007441d080000801d901170703400f40c0c0b02e0142842d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 559754730 1250 559753480 559753517
    0x30a2309100f110d06030506130206070618021f090f080a03050307090f180b06120a020a0c021816231602042f07050c06030c04050d1a07 60
    0x41521004882e180d50005440c42a50b80182c001200c900742140d80e20340480040800422440c40b04460600490000803084940540ca4070f4800d170f0080d091903e014a199510402400c060384c0a80c21100040303003410242c3c907000c0c2a40007e0500358000000b50003000300c058045c135a2584041c1d403000c4544070a00c0007490119103060780f0b9034503003401c94403520303202e00c21f44180d9401e1300710321b9044100b9840029001d03521044120403844254080006e11604000d002092142100c900042868000480c4514401fa401046100498908101400d03401d50000340340380703251010301c82e1041c2c4150a02212140c20104d00100c26805c6c02c0681d002d2001080c040d4100303052616010780340c4030115502c4141c50110902a8400c0e500420810620391101106021040382c00c070540600311500c014180e800314518100d48416030000d00501c2610300c0740c070400440f41d000903e0b6031a0010300380030000d06070f04e030100d040d400c65208080d60403070312100f480301c070740100c000900c8001044103408181e50980ca4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 559755980 1250 559754730 559754743
    0x120c0812010e010f0305122d0d061203020a020d080d0e01020301080f0102092b0f0b310215070c080a03020d02010614012d03200f0405011b0503030a2309 67
    0x1480107094a170240150b0b51042c06400076001c0001103107110100c244185014000d01e9127a01c1c6000402c640c035211045842d004800303040c01070240e40b20000d003d000d80741401c000c21105105400151926000200708d00654022200043ea16034011006020721042813001000c0c52419400031400c001880c0c0000d00b8031402203034200d02c0c0401c94034000050148070032482d41740b55001040020b0300315203441c146140800c112020a24060305007440e00840b51289031150607012000840102e0120315000c006210510000d10704100c9000c0007154000380c440708440c0005d08a0b4005800c00d50340c5410003034288008160b04508591406005002d000c040d5244545a0142031034006204a03040c4d070300104281d00380c40d10302150030f0540c400c1317070740740ea80354004290301c0200c04084070b650b160314203002c03480d40181e4030b0440c3c47d208180000d112039441204136404100880180c0f03200300140e0f403546421580243d41c0c884440d6114821a0a841004149108004010f64030508549004040c1d0341d101c11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 559757230 1250 559755980 559756003
    0x90213091d0f010b1c03090911041401020c0108010b09130c02371103010f050a0501180204180e031204030c020f09070815030a1a090706050a080103120c0812010e010f0305 75
    0x704141104c0086c03510417071070040a4216004108051880e104a404590700700b4415404501c1c2251802d41180d4804511900004070603155440f05900f4a08143e000e80c01400242d500205103c458450907541c90150580280d032540141000c1c102002c0c48009030203140500100d21800c0729030b00b050200c4011407000d1516080400c0040c9603140300300003405844103400741c883e414240000c3c040407a0840e44190b048411085901482181a914030705c00e038004c43c40780d02410101140c03e040c19810941012600b03c90100580c1d02d007883c100401400000c0c00c4d10f082c1d000420034041001141841400d0001207802240d0048035403605500051030540020203d40310700ca028585049203441c2000707600b90440d4001c2001c0305008001309401503440c800c413442c070507034440d100c8001036241c003600882c3c031000e88555480c1166801c1d600c0c0c0f5404600081c5550040207941055600414420301c0940003020351050241c940d075145c11802a0030b4801078100c2c00d8240c0c1c12070400c00c000364000400f2000d20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 559758480 1250 559757230 559757269
    0x12030715020d022701020a0308040f110612010509060414040609170a02030d14270a1a1e010b070b0a0b030d021f0510090213091d0f010b 60
    0x1990010200039000b020004060a4000301c0c00c024141400c0411111105550b00c1400e05582d01c00012130341c468031301030040c0108140c0c801060108010342103411066010b80e80301e50407410f521340131a00a9003c080204498a0798a0043c452032801000407030f0400800ca5041c403800c1031500340b54104210140000300426aa19415000c020207642c41c4c5010494600300261141c90741000030f5200e41c032145030325a00e81d00c1c03c1501600d405984064901039401d04032a01c10060700600c00000d44010000305056600c120400e4400103118603426840c1000e01a500d0191814814154885040d00d000d03900e005441a2005201541200c3d0680e100150004042d41c160307292158114020011000216010701626480101403a00064008108606c00001c04008031124403007400300d460a645070084500034050801c50400990064034035440c48a40e001c880d10760702c40400d000c5a428100601c21151200c641c034100032030034401d0000094901000384404074102c0c00040b02821f10000b905a031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 559759730 1250 559758480 559758503
    0x90108180c04020a0e03010f020705070e0c09041506080708010e0c0906071e031803021c0201111b0a0e0f01031407030507032301020703140919090e0705120307 70
    0x40304401c100768248100c018008558440c01d44400501105902807102e01175802c1100d80540c20040c1d1084640103904040604049810503102c1100f00c0c4018001e12013051040c030070303220f283d6980d103d8001421540711007650124603003d4050114440203081505114024004100055450350b1180c1e10415806400d41c1c0c4680b04e80c00100761340114074018043c03a043c0d03014081c10611001400220a00a48503200740c03107010700504a100209010094004090141c1110001103441824400030310505014940d5203500c1d5056181800b404000161034103220501400b609003400c9406c0074125003c800b1000349007402418101c010306100080c540c000004034881114020b000000c00383d5071000c0cc0d0340d07103980d8905144020344d2040e0320700c80c55013110100c18100024140300300c45005034191200850032062840548280e044030340c850780c01106248401040d084054245030150280400c000f0710402448041440d10189401050007558185c0102650b05400403d841070180e00031040320b0b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 559760980 1250 559759730 559759771
    0xc03250b010e090708010501030b01090e03041401050307030e03160201030c0c020a0302100309210e0a180b030c030d120f050603190303151212031e0e07030206070506010608010b090108 81
    0x940b00743c4e075101020b0395180c18008010041c95074200c5040322076514060005840030051540c49100e50320071030340304c07007030881c048455540500042d6900c081c0b00d00300018201006240c490079940018010140145000008000c540e01031050008a150500c0d001c1c99040b00d541c040707500d901860202910601104075200e408900c030350449411a50702414020f60124100c40800d42c5407840d00e82c0c84082030307042060001a0804e0340140e41110b0060310b001100200c8024580010b1202c1e0450982601031444d400c142500c0c10015a000415070381e4840f013000c4114101d2500321000c143c0b140c88058104414404039507400138240c0d04c0700c07860320503051442c403080c5005c0d4014075602161000e00341242100051035400e415000d060117014440000c83c11040b00e00c100c0456140100320441c000c075047d040200000c040d44040f40611140080b43c60321522074001980503000000c0449190b07100d0b0005005240d8481d01c00c9005006088809050204000c006403260100070002070000007a04590301b03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 559762230 1250 559760980 559760983
    0x60f020c030706020708071a0f0703021201050108090a1205040e0105040c081612050411040f0522050a0206030c030915091209010c0b0106120b01110304090b0607080c03250b010e09 79
    0x12207c66004510040c11450848044202074040b904480341d240ca440000f0001d50080c0220342240c05c00640d16052a82010010b5075800c4001d0b001c00214806c48062800140820340055030100305500d446884902c0e2100307102e10554141c0065010320b04282d0404c03201c036000819142c02c030001c0021301d0b0742028820002c9034682210403968001740d060000f40b00600c85543c801400c1090262014800684003503880d01c00e4035020303140c0034a0b44003a403403e0014010500c0615110720720a6007500c1d40e8114940010790349030000c2d5180302c1c04400000c2800380c569020072404000c1c0d650600d0001240c5042482651106110000c04000c4000007811090903882410082012075002c04039090341d50319000002d0088501000070152203150003490780c0a507000d03100c07100185070b055005515203410002c08401414000c0700d42600f285040c0b00e004001655503024081c0d2005050080d80c981c01080401d5028050070034000341d07a45003400d600b10104040b002035605640103490840e400c0c3d1120210315 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 559763480 1250 559762230 559762237
    0x1d041e020a351e0103021c200f0d0816110310050609010501230f0f04060201141014120705130902040507080702060a0e190807060f020c030706020708 66
    0x11070315801d011102002c4405030a4040065003800c1101c4906030360f409440d1001c82401161090150035900e00420051a20038000044a00d441c50340103054911903403600c0c0d07008020b00105202c0b03065103d5406040c2000d480143d001d02c01150341d22004a0180c489800740d05caa4060010903451030000724003885900038840342c0e4648003408031000c43c11600b83c0003008180079600716104034040000081e0365803003100000b001daa5007a403082d01c2049154211400359004548103000060140a030344050141030000c0c0004004a400205c0c0950300c10104a40301c0358000c090201c6405800301c2440080444422580d40c64030a488032001c18581504d61454662194420b540c000400c2084902064443d08088107941c405d940520986d25050404c0d50445000c40300701c2c005900260014000c00e0041d00305e140000c05542c1562402003100f190451908040042665540380001e103880c2080494032550541e561400d400b10704041310130080e2522031154413000b504071038010842d6020b104912048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 559764730 1250 559763480 559763507
    0x213091a0907050d06050609152a07080d08010b0712030b150d0e0714014b140a0c1a090c01080f04050a03031e0603031d041e020a 57
    0x50381e2003407402d2600101070f5030004901d2400340342040000282400c00ea0140c0d5801a0300405c0710a15050b0303804c03a00101e4115650995401840300c42c044005c0c0a11035108030902a4000503106c40c500b80f001c05850030307103030002100400548000401012030b005003554641c5500959014002060a5085014001046109500c007609203840349000c52800003c011600040c1c0b010300c0365180ca05103058035080103110f5a400005100c280407810744c4a01c0c951a85075018000019035403d86660718050001c459200d0106c80e10360a4138042c0014038401310383d021204906e82407115040300f4092003118040c00d400701082c0202641a041000b5040342c520b00401341103241b041031450003601003569071040c0c804c1180400c030010086030700303040b00146491060790044d005004a501603a0b08400030140025400003100a0141401d0030400c81c7c010a00114000d40c1c03012000100305030b49144031100001c10700c0c400d901e003e00d00c12510885015040059040c1c03000140c6528444809a512010401c40c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 559765980 1250 559764730 559764739
    0x1a130303080c190e040f1e0207020a121506080f0a14010e0102070602070c08120403080a090e040b010e1006080a0e030c0d03020316050306090f070210020a11100213091a 74
    0x448903038590321010f001c10b0000c00310f07000c1c0301c6c49902c051076404461034030300d000035050420142c040728000250000c14101c1c1c0b02401454569039950300808070740407003103400c842c44013540800b882284603600521010b40f40d0607000c1d085680c1c2c4190426070b20203102e03d000f46111b947c00c0d49040d20540039444a03003051031020007907540b4034540c600358009600140701142c13580030001002c42c41010020b054038100d04d035071389054601401e68841040c0c1c3c0d00b214201c1010442ca154011452405514100740140e00c40d40c845409541821050704580000818232060300c040d120341000290f9115400300d40040c2c81110002c2c115254820b1507080d41b18804030700555218420540141c5507041d8011445180300c40760004513021046000c0701da07803005807291740d404904030300410002c5400043c0140c1000540c012120071216080d0b100b8280c0c2c21100d81040842c1120441d83c0c1140000d00c00c40d8203400c2200b60451902841151508001110b801018003841d40c03014010500e070001c207481ea82401d070017032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 559767230 1250 559765980 559766017
    0x170c0f03010b19030b07050f040b1315030b1305060f060304110d0c0f0b031006050d06090e0d081510080705090d240b01090501050a0e0a06030203011a130303080c 71
    0x665240240f8541c03000712046101c81e800105110310840070307583c1000401c1c100d240f400c0d18040c50904180c000e074054001d41e030b041d10000602ea204000e0121340820080e10301203011002103082001044040007800348881c203000c1000955920345020200380c8000321030503a1030740c5990030489142e4402e049101d80158140d2140b80a000c0d19a511a00315024003101038a90341d1903a110300e040b03000541e43e5040004500405101075401074000e09017001c041c3d00005480c66079a58104165886010450001c3c1c01c40c0409100d5141c1c00300c24254001d48100c1d003250382d02c900d58042001c09028541c00b608029207500850261803146048441080c0b0080242800d0006820a00b24903240c1011400c03000c5071000704c04403092140d015254407450305844228002d840c000066805500801d070400400c42030300104012a84d940100e1000b80c8000da900584941c180b892450442c9800b0702d12a100940501000041034480d0700c0000c1030300e62501d0824070f1511101c0c1541c45a008e07860101101d04102c0c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 559768480 1250 559767230 559767259
    0x50919061d1906050108040807030e0d0809040c050301030b0f0910020a08160c0302100b030a061401030c050604150f030e03030a14070c2d0209090d030501170c0f03010b 74
    0x50100380c0c080c50b805102240d1941c0003100b84000c40383c0b244141c82c0400d1080000074042004c4201030300c030441c060704108025080d401c001034036452860008589080e008281000b207820a84103070480300c241030034010f25550441d01c410384001c034018084004011f52000040e40640e0a10040b41c402404180540d1101050700d00901071030300c110b980000e00300c4010028191140705185142c1c8107501600a440740741c41a002e6000904450381d4402d03014401d04280c5c000144440c82410222080303d00c06440719411840c0c03c01c01d591050340100d100320000d02c0b0500c0b4034000c4000a1b0800922824178201185440300103502901e420702000d01240000b20030482a00003581001480003c0e140c2c08d402203507035070001aa4440380c4400050841d0451500c080d0709800c83d0340c0c01d11480c00d0603041c82c05000910b0703400104521021a0440c0f2590006840844090b4060080c00e0140c0903224514110880c1620320790750f52804200010b12540c21010307a1703012904c0c20340c08121640c00140c01e019120820 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 559769730 1250 559768480 559768529
    0x204031a04021c0b1f0807170c030d170a0b13090302010c050c0c0f0a0e160e010e010507150b100203041814070c170a0908100605091906 60
    0x481d030607806958030403507a0248804880301072003141c0d03100b440c1900c9502d0315142c0c12098400b404030180300440e4000d0210b0031030410000e140007411240541c91080c9100015141030168514070315000e640a1080703840e425400c01e050881130305182c903100000d680c030840b40401030a49124240c0e08501e004610744410b407080e401c01204c240c003030b400a100700f80f6103190849551040c000c035182c0980080c1495441071814040144404200510480e26607840d02d2001022600c2918400d04460340074841038240383d0000603400c515042400e0021340081ca01001801c00d20590078006e003040d2640849881890f00c0c0d0b0701843c0305130009024034001000c1c0e208043d59a84c010300500310145030700308004c0c170958214003d800c08800c403a101c03651940c4030420103407a0810034200884000b02401c3e901401c41c0c2c0c4c0c1da006070007003904079584d4810403483c025090703007455041c56070450064140b8005101c582ca5689a042c0c0081c001075601014404ac041300000400ca0b42c1c024100c40124000c081900054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 559770980 1250 559769730 559769783
    0x1203160f0605150901050f1807020a140d080703020d020c1608071e120302030d0c0e090a020703531e0a1d06100305010515010503060d06020403 63
    0x229040400c05601c40c072001c24980454010740c1944000c4c41801445a8100300c100059810805885132407c02c890620520102e42c00715030540c01a44030403510380901c24074481800d11b1041103406043c0c0d681c20703981d0090071124024911011715400050200d00b004d0070354101c034200e18241081d035844c0d507903c600e040c41d030380441c0c03241807464030070303400b000c1550f0300c40640c070f0703801c0720407100c00d002e00545440484010202840c0c01542540414400c3c019254114010440013110360381c0c40003d0010418200817180e0000b91040c01000d00c14044100080d030812403510035445c01c200c40c0000411703150744608082d95200c1150f110954600c0034111410004a80c080240042c10800710042c2d40d510641010905800752002016940f103003c942d9081705a40310030426540d03012090002c03401210710b035140a03400d650602c14522418020428000c080c815150003d007104107a00c0200c1500c40000e0190202404040c820b008146205042000f190704490040d580701361002308900a03040134080c250f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 559772230 1250 559770980 559770983
    0x40b011e031506052109070e0c030402011707020a0b0c0405131508010e0607120f02030c070209090d0c0305030a02130b07150501030b0a0e010f0f020c010b03070b091203160f 76
    0x4030740d02c0c000c11542e0040d02a1040305001044040c0f10640500c17841c40313900400313003000a050080700d4020500c00340b203122551045c0e08140ca05903481c1801e03c001043c25842c00805107401400c4070600c45450b6000c140f603d0501e400c0304102000c0c0d00c900e0708400c1c441c840c0e0f41c407003903000ca0b60490070340c0c1552054014034500140b0481041400369900c800720300341e0715040406035543c0c20000004003014046c007556800c4440c403100014040e08088180c004036802910081e00c1d2400c08918070045162040105900c120100702605801c00f503080c1c0a018885c0c003103c010141311020001130182032860b41600e05842d4503c086040076603130340c20388603200d030b1041401362044800380f40c0c0071070030b07400b280070741d41c1281d030301c1940e40d026943c40441200082607800e0201e810365494a0480d00e100607070780184440384d202c00100580d101500c0107482d084881100c040d6000740c0001004001c4c0c0c580c07180076511245406d0325014000d00c0308901641c15481013a50300740c800403003400b60720305100000c0256110103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 559773480 1250 559772230 559772261
    0x7060b04020d0e0f070f15031b030605100311090402220e070f02060108060c030a090b0910061409071107173403020127121704080309040b011e03 64
    0x7518912181c0c07166550b006490804081040801004000c1881e0301f03000d8a8500d000500a40006500650401e1034100b070000283c840c1d40c107011900d006002060019200d0400304941c3c0594005080907008051030540700360b0b03010820822060803c030114a100807441d028400042d1100a51800c808056461350300140c442d96114251a000066260603240100001c01c135030f5464507c104969800104120605510f0384082c01c00a00a6590716001e002c540001c2d100c100e090305032920845d0f91030741c4072807054440340960946d19280d0044054000301145002c0860184880303203140b0703011280d0710541d804004c0007480b40d0800004184441c013403100104031101002c1f148082407145140515400c800d5909a208000541c00b40c90307083c61043d024205030f6144c09030205092003c0e0107542c8002403503175100c01a03c040143c102e040c0e501040341c506080f4105400d000500d85d6034080d202c0498096a900d0902c808542c2c014599042030000d0420343c003000c2025008020090095141805180d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 559774730 1250 559773480 559773493
    0x41a15041a1206060a020c0f0f040903031a0301021c0b0f0a150311123705010f0b0f121e0106030f0b030d020d03091e03020d0e03060103030c0807060b04020d0e 70
    0x381c40d010f001c9a012404580c01807c100d140d00d41005454503442e038a02d640065840c0c250311040e2600d003c2c48440a021fa100090260301810411780c184e5144240244203074810400064422101800c0364851514000b00090b020700b0030003c11181c50b5a1401c95500c41400c03c00040d40f94800404561000385998080c071425184035404142d5024000440304014400c03000035005070517140c224180b410303000e003881d20007080005018034180080d00c0e1608800c0e4440d4014800607918849410040071000c1c901c9140c030061500005c0980941141c00c001d0340c2541d8040b6805104240b02950800000c00c0c01e81c1c0b195035141c0018000b010500c110124960402c064481c50303180110b1034a00b502c8050700a0300150392240d10840080c00000400c4443c600c05050076004089207048000c02039100742c00500c400c0c406040701808135012102c003284243c0c0320f08010310000382d00807001e8008a60050286840705090b1401e040a00a00a181504a071011815a600c490150086150302c0d4200b8140e526 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 559775980 1250 559774730 559774741
    0xc1008010513020c03090a0e01031734060c11160b0301060c06060e0114010e03061005060a09080111070507080d0f1d041e0f020c031b0a0f0f0b06041a15041a12 70
    0x241d400b03140d80031000301154003600c00f00d003070310701040e9150a58000c0720300c4510099551100e04807491070a43c034ec0080c880300d68400c07150104002a54071203400704051806149404810704561005005420411003078070807034010051990003c501400d0304d001110b02c9903842d980c641082101007005140065200c10858490f8100460f195003d84504810f4040706800c08052000d940d01c510b003070302c0800c13101540004110600380b103001c9018102000156460307903141052440c0c40441c5c0c010241c130b900004260400650001c0e402c4035880001c0c2003030b034107070303001c441c001c1c4440500481c80d2078110782480303031682c03a03e501d48010050019610702e0801c41d61803855100c10172030281c080b456400c0d40c800c020807043d0320040c880380007990102c07000b1a055508140d41d0a042c200603088211a000203d00458042010b0b034050154004001d0390104405000003403202c000300448501503008144005402241c00060780c2100d0140a149180c440c07100301c600e002101d00c0e030040d410000074007058004500e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 559777230 1250 559775980 559776023
    0x3050a0c051602010807050906040305010515180609040201030e011401170d1209050a120203030f0a1103040204151e080106050402040501122a020c1008010513020c03090a0e0103 78
    0x55000c0c000c800b02010084080d0f005486a400160012003403110611074059942c0c0c0f840020300c0a98803440c004151f0341410314665001d1b0822a59041c45500e100300006800c07003c81419030741c010b00c100c030403406079115030005074028003644146209950030200e61a09a0f506401200c0c101c07035031710060401d09022020b00076118403d004901d000583c040180d01060b8100d0341090800601030002d49078070003031513a80c5130720401181d1034101c05038201004000c00c400a030006caa034840c1d8116024030071030a88451400581c800144024802c075964465098485060828100600f40c1505c4040c2c040103800200281002d40d480365407815800c4c0b002c00f1925041c00d000b95811600107840c0d06400401002c90304000c5c200c008020401510f201c00411140700051494041c2400c3c10b4010f05414182081880301c10300000c1010000d01150100401a80d126050f00e406482c440d00030060311983d00704040b6066210320b07022123034444403800c00852148004410b490480b8801c141e010107030207420711583c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 559778480 1250 559777230 559777237
    0x606120308250e040b0a12060e1b0108360f0f031b0a02062a06010b0d090302070b070501052a09060a170103081b0f030405040b0303120703050a0c05 65
    0x1042d03541c0301559500e0940e0082e070380c00301c200500400c0803c580c3e6414010448240307280d480b0854201d910303060b0600b48101c510176420001020406000c2c40c80d85a04080b080d6103d003800781d8100310851001484039990841ca040001c016070b200700c1c40d01005100320341c00400b01c0003c001b015003d908100d03584140c002540c140d039450204082d50800701c3c02401d07036a0240030034141494900031059402d00698880000302050070b00780c0300b03001d01e4028406080c00285680180301046078071010040c45080304103070694403d038803246c0c808110300242e441c0407400e00003e540555440d1601003841c004026040d0000c5108000c25060807907034254851080b070042c007541d1b040c1c0f900005c0401c155850384c1000d10081000c1046400d05200301d0410b030304000080781c0240d000783c4081e070340810b141007078840f035080920f81c91900400170411030b013500b00d203d6101d10a500c6041d2066a9852040b00c5070b4400780280e400342c040d1501c01298526000e5806030181204480214080d480c0800e11055140214247c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 559779730 1250 559778480 559778521
    0xf020a020c04050421090e090106091b020601140a0308181f0903150b03060915010816120c0302031516140a140d090305040e0a0209090f130606120308 66
    0x100041c00034100c002e00c0d13450117103c03040790400804090204010300152042402070b01c035a00001141c91524607108200c803c0e41e044000b0f03012781ca941207140707030b540011540c0c19210b03100760754100441d20704005800d00718560302c020f028040c08107200340b84207102c55103404500310540301d0340100a03512404541d882c00805240e80440c442c08814000308498a8804115000c03503a4001810b10720f040c0020b2030007104441241d110fa00402c0c14504903407052082a00604400b4000c25020030080321103182884030340105084101e60329004418130041c5000c038002160042c3c2910080c4c2002c142580c00c082c8111a00309030031b0f079008040740029118039101000565017140250422400704008c0300c0c4200342000e250150780040c01000d02d10351080c1b0496038540d109032075503681c8510300b4160b50721505004110060162060010880c16250040c8095120780c03c0488124159270702c0841100148a41c40c0203841c3c1447c00c00f011a060703100744030f0568014065251866240d88540001d2004120002c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 559780980 1250 559779730 559779743
    0x2060403060c02190f060614030705010e030a0b041b0b120f04050f0d020304170a030903170d0f0c020f061005041e021305090915040b0c0d0f020a020c040504 69
    0x1040011601c1507001056a0039148155000d00c0c0a64075441903000220030141c4040d00e00d808140d0800c81b0314450b800007006895040c07041c0c14040740000780c40e014948541030500c01104949070039558144580c4000c0c640c842e9034050ba84c00c01d0700385440c00c045003c4061183d11460500401c8141c0d0031010380d94a200c3c460101a030550302c000c00101c1405000c3d108032000d2040c0f444508110005002206040e500303030b401941c540e03103049400708a40c048a0684103030784c7c101c070764080040b0b41d00089420130b480c0c006204800e02c6815003090511881350141030410180b0300346d001c800107040c6800c88803074901b80c2c0c0d00304d13220000c50404007a1660001d541d04041500c40e0b09041005e403d15412022181d800c0314a41d01039a142c1d40d682005a0b070040e840130005000d09002070041d460580304040e00403510800400901d0885103800603137840c05040038120314105030029804c18440021203100100c41842401744c00707107071131404003e17400041c0d008001d8020442c03a0b40d814242403080d140309540107036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 559782230 1250 559780980 559780987
    0x301030f14010209090f0601090f050d060903120203070309150b2b14060106020d02030717131806051e0d0803060103020f0a0207050f010302032401020102090a0f0f120206 75
    0xc0d614001c084496000c03200554081c000c4240c2595035103034051280d032000240248034600180014590445508084c0016000001c20300142c5c4070104c1e844000c0d580301c5070000d1280b11505094580c10b1840100b4000a8000400c10008aa154024586140c030641146801c41041c000100c00e80700c112a1094020740d00068429501c40c850460b41c80c06502d012804400c5540c544410848a00184001e08141d010000402c090f40e41001500c0140d5028800b640c00c03c2c3d4a41e0300d10b00b191042e070f40101000c59001c15000101d4200c0103c41005120f010050b00120500c6010107000c1c140c00d21580b4415602c40c2105c01c80e455070600c4035a04990000c011001e12a200c0e81c070b88429030009002d49040550030310405903c940350100a003068a200c2c0c00400441d80342600f045603c203420350105040500501c18080703d04110b5030603a04e21902a11009011405540100d0080c044c5c0c0d01202d6000745081c0000425030910030070041540c0c2a152040f205c0d5440e0104150301000541e0004d40089040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 559783480 1250 559782230 559782233
    0xc03010c110607030f0e010f0b0a080f0a0b0403211e060617130606030812241002102d0207081611040f0b01020f0703030e010c080c0706050a140301030f 67
    0x90344640d07040d03845c5a07000190404e008505500b1100b0014045190503529508015140361500c4141700628070300e80141300500844078242c0c0c0f241580302009040705c1481c004501094091351407200701100902034441c504141c0d05c4654050107085402d82d0340c54030249403401c20b1094034000c00064030360940b6140e01b00100d0704c40000c20590300a140021114400384074100103000c0740030300380095020342400c035290b100408420100460203049900d0741000c2e03000e940149049803500010700a0110b9503500c00000c000d80503410101c030701400f042504d1a20703134149203039442e1512140c15919545102a07096a9240c01c56040348241040603103c0c81c818000b400c04442c51040706446103103c1c4c42610007040c0d90b00f01040640d124541c2043c449515550528042e503410405064440c8818004000280c5580c034050005001c540c94a410081c0160a000c00d204000c01203c028225040849030704669448009103150000700340340c2c0028041d8031f8100b80240c018002d9034162904184043e01a0100c1e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 559784730 1250 559783480 559783487
    0x30e04050603250b07030e010206010b040303090b1b250602070f03061806020406050d0f0b210309061611030a0c090902010e090406091104110313050c09090c03010c110607 75
    0x2c0600c4100c182e06083c3e07010a4509403100034180c0d46200381c55070020105440700290070b05605800240740316009100c10404254444600412104084a103d03034070800400402070003d00c07448444070a11460081185400c4051050031402c0c0168a94001301610b40c0f10490b1289000e1203401c0c0d04000001c0c3c1400411880d500c881e88044680000708a61812030340d900043c3d030044d90200021900100b601c031203659490281d042406946001005400c1141c4001003202d0303c50801900d0403516011034030140d04c001c00c100ca5144000038140c540354007400411030201c2002c44004c444d10501c9400d4418039040c0040c5190f2829070009119100038180f0094000808151754113a040085840c03094455449100480c2c1c0603500500002c2046036680c145902c0d400b11800768140590300d08021030b0761540e00e16040d00d42125031507140142903a824140945030401072615180c3c08240b403801d000714901d00103060318132484250000c0c070000f1103d07141a1010400b50806a4964000f0000140450b20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 559785980 1250 559784730 559784773
    0x4080c09070c0b010b04060f032a030f02070c030c051207290a050d0c050a0e01080c070b0f04061107022206090c030e01060b0f0a050d1404030c030e04050603 69
    0x851401c030ba01503007551541c4424100a0380894103440001406001d003540c05103c840d5410803030704048c0b041d022010f031241266003601c2021400700f007044000300c055038802e8010315218400d030403042d500c4085a0420000506942c4011525a120b040c00020a1305202071240c03641c041c0d44029003903180c0b400300c030300281080c058800300d0b054180c0e13140c5e440c4442c90701c00940903a00311603680c0b60f01c4d901c41c0e03070a110132148102d00c00400d015041c021403c0441c0c4c400200141080b081c60045400e80781e80c0001a8280100a40101400701e0001002010140c840c030251041740190400e2000c0071081000000502c16401c020750841340c40b00e103603945050072805429180100400004890343c0d0b030070b541c00071074103e9140c0400082d25400620909a02405000054035080d5551841e18a1081c1c45207800d1103440e00301c006000340420f114401142651042401d44500c443c2400245454540280f03002c001c24012400f2404405284a0a0500344280c51040c8400307401491584030743c041c0c0581070789 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 559787230 1250 559785980 559785991
    0x80d1b11090a09020d0804030203160302130f0207060e0312100e01030609020f040903020f0c06180f120703030504090f05040f140a050a081e030f061311070f02120304080c09 76
    0x20344031100f03440140c03601c0a009903164001e070381442e00e903402c500c1010704001c1401d1000d415402c0005090015944a07031100680c0f0140080004e00c207001c140280b4017a0152100140ca140d1602c1780358850740d4004130040406449501c5014110780d56008001800030441c0200e848481181006000041c601d600440c6001d000078050341e100c82204000505413440c0000c118011380062425014000701000810040740003140c0c00743c01d06d6400ca400701c1c08a07066030811482405404203114483d00d4542e03841030345600c0c08043d582d409849042c007401035880792241d110801d02e0062039a640c1c10041c4a8580030b030f42d000010310610016034a8074020400e1a80f000c0c2110300400c0c8484000400c10050a50080d2054000c43c5c6c0741c5101400414415050b24041604460100b007084480001c1c0e4600581c8082c003140e090300c4401452554200074072140f54822011800002c0e5642440705101801110078821204070700000d044208807a102e000d98400c00c0c3c480d601c0303101070320f5a501d8248080340d40700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 559788480 1250 559787230 559787251
    0x240e010c0b040c0501120b0108040b06011e0509090109090330090c14060c070303050f07060c2001020f180f0d0b0403030e0610090504150501080d1b1109 67
    0x11600d5481d240d2420105440c1203400c040000010840b0f56001162a9280d0004180811003c002ca20010f80300b041e004000804200c000c5000400a1707011702c4000300760100313528401c440c00c860024081c090703a2051188a02c519100c3c03000150940150090406c15070749643d072800e03a000c007a41c3c01c611191807038208418103240d00380007014400d014840d036480709000d010344852092501d91420341d400060b00701d4900559003000404040a000220341e0b0440741d0610744a80d440601500c0151540640303903008250504100104011310303030028900b0040500010801450ba00380d4000a08030300c6140d112100288061140c907043c07a0020301320802c81c02015041c181005c0030480040c11420071b03688102d0b44541014148000d1541c1485011401e1101e00c0050507141406103401c8400c41307180c41140d100a0300c1c0c800180810485d240640d00c0c1c409018010311007541c51f81601030b250b00714400c10301d0005080d0b45400ca120030084061060b419007000340d5003114034040003480b0010000805060f0134 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 559789730 1250 559788480 559788497
    0xc0f0a0f0b0a1e0c17100b0304110303040f141002120a0909020d06061103070b0604020c15010605040812040b032a0d060317121914100906240e01 64
    0x10401c0c2ca440c1e000b00c5541804002202060710078060080440315004003113503585d00007000714100150a1840546880004240d20307591a0302e45582c03030781101c22645406020109001844014000d442c06c10740c1e6800c410001c070582c00005002c20f070146200d1203c016031158483c40c2c99071034000d000f06022103c1e45420200d00d600c0d180b000c0142d07030003d500510310300d0b81c81c0d000b000480d6110304224031889408014520703128803a15000f41c080005000c1034459a400101c803000c5210811a18418411802104089694520f009821500940b003082210302602140820a0b4400e00480d001c0d542d1514000d4155250041d41130007043d000d844001c40d903000200c51404030040c26020b00709400e110100482c81908525012461140400b00c9103508141804107035560145508100da20101c90548450086400720382c903400f41503c551b90005250b040b205002041080804039016203071034080c2441416070306c03007840e18184081c52010004500d240351884102d8415800d0400300141498900741 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 559790980 1250 559789730 559789751
    0xe0606010f050c06091c02030a0c03030b040b1e0f0607021e1203030c0418090201020606010e041803020a02041b0c1709060d0b011202030c04050d0609080a050c0f0a0f0b0a 75
    0x140042c05e95442e1042d03400400349000015402c1c045e80c60200442c07014504100310300f4030203003811030110401800d140d2601ca84090b2034444d40d008141c3c002c40148044215102054945901e000c00c810307503400703102c0034003144010b41018800c54100035030260140c1d580c040500c59807000f81c1d20302ccd5285030740710180e424108a21034040015502a5291031402c595940c9420600c0c489503100b02031100313444e03080c1405440541c0c1c01040030740e8081c1080c20005100562400001d00501c4000c4250303020980065852051543c0050f124a101d4400d6030200003180720314680e0010340c40f40714406d0001179451040d800004030480361580740000311000e81410440c00100041568000e0601d81c030026a0747d8032440415030380590044421641c0b40801c5155040901c01102d981c8964007605004000c1035512004010250b40700000d103a03086039410362103003040c440041c1260300030342d900c600300c0c82601c40650180c0713404294030188592012601c1c408088603500c03d8003107a0000c142c0075409945500840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 559792230 1250 559790980 559790983
    0x1d0603010e160e0a0606120b010e060414010324060f17010b0705060f2401110304121208160e04090f05010e10151e12060b0a05040e0606010f050c 64
    0x6002e2000e0000744a00d0a09141002c250a00e0040c850702015040030010081c0d80d4004854034200210300d040416054242801607c0035002c0c4421950002c0c3c3c00280000c6007600120207029609003640c0a1289501959021440c20013448141c1412404440104000390040d100c8040c0d4119508055004240388030807031300c080758240d00520380c14100190282c2000018031030a0340c001039000307014049082c81c024000c2103400b4001a002c0d020286110303c40c542c1e000740394200240301311208a0f50340d5038807006040f41e0380d0011001158040102d12100344080d01907420300b403007401d0242d030521081d03400301c0c4211110b00c1c618480c81c2e041079440000102003103003003425007003880c000c40000c104585800415440e22207156030100c182ca14102881c2e9002404c601c04c034041318040c0b03660304c9880000070307070200c08030900e5403207d017444e201d041204080000170f0700b0000500d10211440040707140d13160140816101c4628031003095070003604c002405036004640e610209582840c004e400c207007074030b166035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 559793480 1250 559792230 559792243
    0xc02150c0a230315131e0e01020c070b090103091b030303110f0d150305010e06090d0e15180d05011a150304120306091d06060604180b030321040b101d0603010e 70
    0x2450344031ba03691010109240301d000f007089400d07506000b18074142e000400076071140914014000c14100c002140c48842c1e202e90000710503107401c0401010ba01c8040089212510810f2104401280c2450440e100d03840001003500d4a030320781c080c10f0900d440c03e100d00038070081c18800720259501d040c050340440468002d1080201f070054070307401058541007804013540380501e040200300070091042290341041c0c686041203010000078105c100d0b00e13505000205203c1c0c080540000341c01c545501c0040040c404150044030503140304814000d900f04031041448200c00c08221030390b40f10202000480d0002e040600d1142c1c06451a107000075081ba1103001c3c900c140d0700d0300c5030102c201703040304103401c0640e000500c070b40b50f000b01044860b0703850b280c602855200511200484400c401b0b5452242801d503031014401c07910820400c1c8801c2809280e021100c00040d102a1001c0e030360600d10743d000070a03081071054681b054030000c482c903200d8140400410980c1d9800100800c3d0903540300d801f104903004042000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 559794730 1250 559793480 559793501
    0xf041503140a0510060e03100c020a1704050f0f0d0b010b07021306050306220b0a02040819080d0b010e18090607140d0c02150c0a23031513 61
    0x108045002500001107080c01a01c103506841c5441c09020842070141c41e8081203642604261000041d10f02c00282802402d02c8007a61041c1403c83c080c40315036010030307901160b07071048541c2c000003c0c100301c41c40c05501860003003d40105104141d29003038607103440d4914051200810840c03503d40c0d955200c20300b07030a00b80e00035011213501154110441c40c1c121001c001c50541400e04100c150324010020382d603000c018150781c044000d20082c18282d49a03e203011540c0d182c205050310720070704006080400035807240c420610240501001d0740440d00c00c80c0440320240d50441801418990340c010b0090007002d08a2400f0306100c010001c452840d03c0351200a40c5900320718040500f140340c004112400c010004000101704100788051100300c01c0c440341a12210815504c0002d02025030460a91814084080345000707200c1075410032858101e900c00611a05050b503488500014000034085075241c0c00c015100c1c5000810300000303031640d100000040034480010b0921030580b000c4002c00003111108800b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 559795980 1250 559794730 559794737
    0x1b090103140a200a050103021303140f0109050313080616050a200c04051b040b07170d060609060c030207031103011d0102030103020316050f10050c0d0c020a05031c03020f0415 77
    0x21040c401e0318107041c45400402c0c00303080652409d603510180d82e600c1445400300401625081c0961001220204070f4180591100c4008109a141c5d074140030b59241c1003010b4000481c00512004900d030b030401700d407560152480040407120030014910654164000540020400c80d4000c100c44210903980005c0c141035078060041c1400108030014802950402070049030800c0303031082442d807a0b07890b203400c4504899400d40c55035100d00291801804010002c00200c4e1880c0001ca802e9150443d243e000c1703401c503052912440d000b9503484800b9100c14564400c05400b60300290303010408102c051a46d0544440d0080c000629140800383c0d82c500300b45880000c0089a501100600071400c0400400e0f5081190004c0e0109040c81c0000260701155101725032401403614420340700a090046084d0303141d002804060755404080381e040207101040180043c0e101e0039050400107240e060100d818005a01d10911001100d003000109502950103c04c8155040c0006c1200180c2440c508441c42151080c964 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 559797230 1250 559795980 559796033
    0x50a23042c0111091f090f0b0d061715060a0b03010b0a02100203060f060d0617030a081803030402090c041a0904390c0c080f1b090103140a 61
    0x218001d0031228040464003450100300303e400d1141d52141c1004c5c05035210552949900c9002c0c10003203030001125440400c044030102404105501c1c050702810500112000030010240d82d080d940c035607624060303460000d60b0003698000c074138030300780c0d258aa50260001d0810b0040d550b0f18021460b1a0b4801da0208441c0507020450444072941401042e107494800b002c25411824004000781c0c20341c00503098148a030703000081440e101c0c0c0168020300c0090181b045080302c04042c1510894896000c134007a000000c4030040090030040e038492001c200420288003c504581d07035503003030240504000d4410596038005120004404002c05101245041483d81d01e64070b4580c800113100c1a00c40d1440c01a2a404451550100405140004150040c0391013502c0c038401c108a00f0503180002003010142101d0300300c20010641400010747c141c1d207540c0b4581100d80307a4003903410b6000480059100f0b25171044010004102091400c01001144111503003507405a00081e580c44c1c0c07021020b052040707403603480795 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 559798480 1250 559797230 559797311
    0x703120c02031218011b210201150618050411030402060a051608040302040b0d150f0204170a111e10050f0a1e020127140d02100501050a2304 62
    0x16007034000c04500c2c08007040c40700caa5540041c287c20501c440000b40c280321030303400000c1d200b504081c044841c0054000381035034458600a2000c0854280d40030301c0c1e443c0d640c00140300c0c01c01e40300f0f0117090402d0002c2d40703081d91103903420003032194032138110780041040922260079007010049080c80c100d80325080240d5203074603510502094404490310580705a01481842001c58041c880f042541d4860020004980c40801a402c000b4040c03500521600c402c0340380462405e6900040c00d05030345001c0c070801e0941d555204e0801112024249c10860703400300a070306101c1642848080c850001c2135504020381406420448400302d40c1103442003000144140c103841e25080b5241285000000551000740007134120b8840d204002050f82c0c2d50882c0c0c002107280307107000f440342c1b04076a80b08801e41e02c001d0310104814844000c1d81c1e02d41458080006605e0310000103000e1a005034524103e0715038100d003100c20f0b041402ca143e016004440c007070b504a511000c5062a81c1c0d400001c1400c4010b2100b0703004181e071101c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 559799730 1250 559798480 559798487
    0x10b0a050c151510020a060902120d41181e0a241803020303030f0f010503010209010806060a0306050319060e0d090e0c0d060905180703120c0203121801 67
    0x7003941c2c060500c0202e5034000c3d0345c1c0410480307403041e08808007013851441032011038117002d01100c0700f5a842c001d4084100503998811600d021410103045001d0792910b045403810301700e0040b071120064401c2d82144240c0710140e004042d10b0000300c40350800b46440c00450108415080410f1918461a0705e541d0710003081c607011800401500301c03058000b40f10300c1559100c480060382c0c0d603440720038003010070164600c0707405000001000d542c4c00303400d5989904003481c8100166005850488080d181035002144a040520a64500c031300140d4800a0784e40303a400078402260311005100040503140d5402044030f0b141041900c217140286c0310301c0c2c401c22015060a20498201c0c0080300000e170030081881034040c2c1d22424000986003941450086502e45440c066010b100d002081c00a043c10200000b9841c2c940303a00c02403240784403000c0c010a48590200c0940ca07480c06000c02013040994041c180003152051448a28862000d070465510000840550589400100f0b407890240c0f03003d1340b5515070f541d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 559800980 1250 559799730 559799761
    0xa0608040303060801063b01091d0d090617070228020301091202010b09060a0b0f1204030206070e0d2402090607051006080d14030406180c06030e070608010b0a050c15 73
    0x1000280c00005004490344908001810310030200c0300d6485500702e03008030405c16140916111904c0c02c951a122f0001c0000d0449582d5210b5140420b80c00c200c080c0106410300c0c9198418481903001d0b1060011810cc116588a01b0b80080d003174081000d034032800141c40c01d01c0f503052064000c05644041c1201407c009013074615560f482c501448600041c424145c444038140c42c29160050215615460908404106805410791041440041c1e100b4002407580214080e4020b064a59800042d6080c410600c051103098590040210b400c01d20042e0429519010f41d40f00300e00100c50151401580341c0001e040c03504101c0007075480e070300400d44445251806124410040207494064a030111034248060900c82e80030107928200071000000034208189903202442c50303509a502d03080003c5403801e110091103494001c04022910b4400c80040b2044001000400c4645559580840e43c0c02c06420580d16000040c0782d0060213000d0003c035054800c20301c4507402c4407060086d42c0e401d528110880180c041d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 559802230 1250 559800980 559801049
    0x90d061404051c0c020a090e191202190f03030b0621010509010f0305030f09010e0901060806030610150c05030d060b0d06050f0d0b060a03060c0c0317060a060804030306080106 77
    0x240c44c030144001601ca1118920499a220030006926401940004e0030103800701000c40781408102100380810003907590a207900f4000e0b13800c941d08080c1080f00c1c2c20000d804204040c2c4141c1041001c000080d00c08d0704883c510780c001130700f03481c2480f00c0c0c0800180e1001c989002ca4568442c040014881800d00754612801071a51449e01101141f840c0c641076102d01c02c810b10080a038400007001103080c0d000f00c140d590300c01e8002c0c100e49243d60703690700024880c61040d51a18860b000c1c10021030a01c1c449524404290b860942204161100002c4240e541c2000007030101c4a074002401512598100f80c0704160003015528081590b58001e000070340101c1d241c0c0c3d04000d1088403010481902925240380d0b04c40050b0744010918207075151600001e201005c00c0d0b10003069203091142c4d44491681c89140f000615100380c80b880007200c3c0040c2040e0b0845400c50340c0341d401c124645020060544195081600036009041c0001c010348c41c0c107000e03400e40f080b640003103805005000024150240d4400361541e00b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 559803480 1250 559802230 559802237
    0x7120302030d05010b0f0f1b0613021c0c1a070507090227090a0e01181b062105040809031b04150509040f1b06090f0e0601090603021c05010306150515090d061404051c 73
    0x10b04d40e5a5440c1030615008000c0600d1203030800301d0150184800300c4fc0d80c203805c50102c660340c59486416001a41c001c05d503500c0b03040814028402030142c07162807689900b20060056450b503846461850082042d500000003035921080500c0040d040c1a1114034181d00803034000c111400704040039010495254004010421100a855a80922521140a100a000d00125094445080011031401030107155a4507000b440d9001c030b16000c03050400745222106039014450001f20200c04c3e0480d411a21803e034004c001c4400180001c0ca00201d40e0000600c9040c101000420001070200c9041d1560041c20120b00001002d0001e03000d207507419802071082c04114a8a460320744002404420705208400c00e02da00814401d40202c00c1000e011010199814104025a075900701240035203d401c0144030b80e81d42a08011a0604040c03a0111920708141411490244840f090026100c6134813800d4541564450302c1c030701210807a1110764015030003080108a07c1ca480040803060118100f03160051 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 559804730 1250 559803480 559803529
    0x6040309081902190b030f10050d1a040c0f06090608100602150402011e020102030a0b010207050a18110424111002030907120302030d05010b0f0f1b061302 68
    0xb100710500c0025182c1d80c152840350012007403001d004142d21032904880380c4414040200502c2000714008144509002c041948800d6510b400303104d00021844005062162034051035500420442c00458002d4400c1d04502c00307995070f8030848a41c01d8005c1d0004030002d902c2082c100241a0302002003600040710035050f22260b854600042d41d079103400308040703094056410000c0c09581c000e200240241e01c0c101c584864041900000074001c1d030007125521200c0f0300d007190b8085a5440044c0341000c0c1d0700080c1c0512440d60800400d4040d408102d02c05090300c13600c40c0b0300503a4103555032000d80700130001e8050304c2086910300d2083c81c0c0c042940043c00000c00150b20562a5241e02c0050710b4110003010076001652601e030701e09428207080d119008950200d100703240c41c81c01c16a000006042036084007004001a91300c0c0d030155041881000b10f40944100b0500c0700b65080810f001c01841100908240c410303240400c414600d0500004550005580c1d003004011401d40c18101950303240e0024500c010940d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 559805980 1250 559804730 559804753
    0x1b070b1b03100e4507030b220213140609151302070f081905031504020c0a02030a030801090b0f150705120c060709050d0302070608090709020c0604030908 68
    0x9500038a031080900600ca4800456040004e04210b01a050540c035010a000c180601d000c18080e4000a0150032616981d1a4135808200c0840d600060369405048407485442e40201740321510030581180d0400281031454070010307034454815105641c1c2c900d60100b03032004148a003201d40c030b0300105402d0007540d4200421070201c1045002c10103524044804180e9100030302035000082c016858003c000341c403240d00c940c0a00036103c029064003480c40750000d00c900104d00003126140002d680903840078101e220400001c0c0b400c1c0c2c01908452801204071042c1241540000f842d044110500340c0204910200501007014035006803400301d8001e80d4003000c80000907011519040c02401411090701001c00d811040203000d201c01d0880c4008946855100d10300041d12030344400003503660f180030500c2642c0c00a024108581c80840a44e01500a4482280380440c00da4050800500c016007901401902089000c00782c405022402120401800329251a1401510008154004000d81c4d8040c0c0345105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 559807230 1250 559805980 559806001
    0xc1508010e071106041b05090406061e24050706050711070b0708030a0b0301020c0a12021605180405100e010b0f0609060301090b010309020612060906060f121b070b1b03 74
    0x2500130303034401320116140c24050799944168480e900704548c4403c00200b03010a1115079003004003582c48207078200348202440b2000f80303810700030740c032039040242c0e15040d940c5038654503c50100c480c2e0300241002c0d450401e07030340d031841c0c102e4408032008004075904c81c100d2118030a003044a4000780403852026880d00d41940c1b9000c4050100074810607045840340d41803052901c003901034804000307445c81240d0315400da6203441c15850b040d40380000010312504180101c1100800c610b5000c03140d002d80418044141303410803041c8140c00410517204d82c030075070800201401e00d0384a910012070003500001003120043d4104031903011450b1030240718150621200c0400c1e84c885044a04403500310340005066406000140d001d003204050180d8804030200b0a0781c00741207c0390b80300d8415201101c6074203c23a0b81c2c0030300f000b90900800d00c5a00f51140144003070402c5030800c2c58119003161944c50110190b04400c1c0319800c0350703444074408a40740c2c4000800d0000b881d040c030801d0320507501e00691460851801d0042a07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 559808480 1250 559807230 559807243
    0x307080f060a0b0f090a031703190911100c330b0901050d0c081b090702010c1b1b0b120a09080d0902041d07050a0e040b0a090c1508010e0711 62
    0x134200000054403641a90f1141000d40040d584041a040c0d4400c0c210b01c4400a03030001c440490a1610030f00c1101e0060500d886456070842e4000c2004000c45400710501004030408540c403400d20003c07080030030104808038036040c1c28000c003891078816150f4051003110081d1000000400321401d010ba008007a50f40c002b002410748106803801105803c0c0e50a0245006d40c45a00c04250380c0907a0201c0c440026981b0f410444041d4240e503508450b4a071031138100e007240c404508010002e00c1d804101b24031210300c03002e034480c028041c48002c5400e081400d02c4500b424040da10284500a00049441005d40503000b101d90110b1459800c11101204e600c035165a4070810758501d1031103a403800500c0440d0785561040701100c40261600c0c1007409200102a920f203400e0185900c103084910002841d8843c030f040c06446254003e940b900309890380091403000c4c02104408132110403141c6404244c20310320b410350624100c090b0350340e04025413400c191550f505202030100010082800c600000c403d100040c1c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 559809730 1250 559808480 559808497
    0x30a050604030e030a061b09060f0e061803060c030402091f0603110d0f061a0a0c06020904110f0a090e01080a170918011503050112080309120307080f060a0b 69
    0x58075003c3c2c41800090510b014004002c014a01c2c00344a542291549844034082c0640d580702c040074640c9500055a04d0300300e0390407400010f48030601c05089414070101500c90f54126076003941c540d030301c0100000d0500c0d800303d4145400c01408000c000640c40d000f056503401140700b401d061200144e10b04200c4d515005409005e0030b141c2c8035241816240110000c8030150165080d081180340701c00c103540c10140c00c0604c00c00c0340b02d04c42c3e9a03e4015100000d0201d4590306615162011410210781e1504043e41003400e52540c85070350781c09551648044030000341074562000010710340d0344005000143c4a420700b030f00141006001140144540b410000340c143c121500014070004e01c401044140002c0c0c03052003455500200180007058501107a405203506030740d429180030014043c1c05004070115142445002201204c03200c1000c08240f007034004642000030402903545070f007a0700304201c11a03402034482c3c8002542c20320801c0200320b200b448194204004590880c802c0c0e140c44428601030040a50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 559810980 1250 559809730 559809737
    0xd0c0603020f120405031201090b0618030a171c020304170d091407090b0f0a060f0c0614070f030b0604051504051003060e01140603010608040f0c0f090b030a05060403 73
    0x880c100040c1c10310381610060540c040d00d110ba58a424600700c6c0c0c903a00090f02000d9803440c0320001150001090240010300ca001410701c5080c0700c00100b81e907510b07800040405030940580070808000c2922210b00c0755900e500303ca00301d0b90b07400c5410b181302a52042c0141007000710744140b00703010018043e01140d003501c01740b06080075100c100c4e00150794010404e17800b00820f10000710b402c108000754046109130403500e60b04800c001401e464810f11041c0c10b00c44d0021944084031103001d2280c14007403440100905807038580180f02c101c1590f65642180c41948092071400c10100c00c006000f54011380c0c91500e00303100c3c901401010b5501002c9041c500a80c090f4500c00c3c3d007101c8800c84078203072030029100200b100400c449422500d59a010700141018040c0c2e0360b482d0903400000c1160f06541c01410f0011070301421040c40c0d80c1ca070500c11180010090412a00184001d15420210b841e070501d540280c003454640e021218640122401141d0308524128066040b8100402c04901e010507000e92007030701802c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 559812230 1250 559810980 559810987
    0x1a090d06050c1b06061201060302090a020310080d03021801020a0c0e07020c0618031c0f0f120c02010b13230411030a0506040309090e03190e0402040b0304110d0c060302 74
    0x3282c0307110754043c05500038800d03106078200e030b4000040011510300510040d258603482641c03902d5042c1c01d07190640000781d00190307124041000040554004c59100c0030b0f4440c0c130b90100751126030041c20301900403000c100294010403006217a1081601ea0000302509000030079480c20240c0e220403903204284110090100c1040018052900922200800481c0241140d0744c450b0003140b405c41c0c01d03260501e1a40a840f80d089083c58000320110002030701c60440e2946000d50034144070072a0fa6425600faa1001c0054002801c1030180c1a4011440c200b01c0c95000402c071582c051007808240e8004d003501c03512140c03e04051801580340140609d901d001e0b200904002681c6504041a6003090141101c0e01449451801b8003400008941a0702880c031981c1c41100300355803200304509030742d200d403082c0b01c030343e04100442c1016003040b94080464106508002040c4007400c400901281c01541c4902c1c00300100100300320800c00c1501c1e06895054044548a540151a403a030020501142c0208807d059000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 559813480 1250 559812230 559812241
    0x210712051c0c0c230712050c030619020a14040303030e0d0201050c071b0b1c0e0d0e01110f0706020c240702130f111804090b13020a030c0803041a090d0605 68
    0x140494030740c0c000c40c03500303c0d0b0003180c6d254840480541070400594030344c0541c0720810b02514003c182c86001d0305403500e141e51000804100c0b04001c0d0322201c901800d02100c64486084000910042e00040d40240c034006041295070040c2801c18491003030100440e451b1800300203540d944201075031507079a003081c8458941c00c807000e174030300020f031158010f2180300b213000c00d04902080c4110350100c07502480440a001c0b842c0b4110142d6500c4803909240808103089103005100c552182e581048820440f03021a52201103c14901e4100401608220016000090000240d082056400540c0e0601c0801036610007201c0d10b1080c49401101402840b0700c03034007402d404091144e500108545e41d0b07502d00c10803895094009218203603200030354000440e80c802d01d505080d8545403042c91200c42e0840c54a142d25a00c5e104141684104084e0484e80310f10024408008103022480c61005030016000440c2d0b1ba41c10004d5280e180ca01d0b0155030243c941d01000085015120f4070441c0300b06076801840400c103074688 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 559814730 1250 559813480 559813523
    0xc0b0a050c0307050c03070e061516060509030421151d100c090608100b0c0f072c0408090f01030b0301020c0604030e04060503210712051c0c0c 63
    0x41c90180181848040741000c1488400f041010380e9410480498001591f01ca61528610f40119100381e4058174003100280841100c10050180307003004000481d5a42041c0ea580c42242d8040d20204c81036030000c80c042c4654407414001c540f040c540c03031440030312800640d03464a83e45124210160b5402d030306c0380e000d5800148038003218490007086100f43c51014400803065002003440e08511000202440c0b80020742500a111490080c418504890046401c00059552581c006891a450744c4038081105014034010b0080c0390240208603c66980c0040e1b0410a00f0118075100303100800c1340c00c070403e100004001ea0201c0c2e048480654240741c0c68040c25005a00601032040003079099400001c8101c030518004c07940c2c6116520035150500c0c42610301c0144421203400e4020503401da48045a00c07800c000744e22901c4510000c44008003841c2001a985002505810584c0d51021410200c0d00c44860989149035030529000e00e6420440c9010090740188651800a4041c1101c200340c80c21b200c04408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 559815980 1250 559814730 559814737
    0x10501053c0a06030c030b040603050307060b0f0a030c03020306062d0a15020609060702160303030902060904020f21041a340315080607180509160f09030c0b0a05 71
    0x700100301001d90795503003502038080d0400d0307407900303000914000040110345818842c0005a0740c0000045052080e42e66688008100181c001903002504007100b51860ba151070a25016512840d08818054514410305203082c2c80685101c1c4145850100c2254180c3c020b031040d00f6081ca0740c0e040c0303d845d0742d000000c0354110440307421484840b6400110742e031142c1d80011354640218044030803a003030f40d5500f010403616058000030010700d4059188080011920a4010411303260004081a2610005400040490303000d060040c901c000c010444110fa05950100d013400b94001c3d42212040d481d041e035821600f04107035001e8078841ca0180c07002c03400071082790034007000031400414124501c05825030200c0702d02107616500070002c1e0501b200d80b45010760408a2104030b40f5010300801958035504403c0d5821414904808051781c070400001850341d54610341e00340504074582030341c4a14001d20b10010310049040201c40244007034801d04000140c2c265441c90f007202c41e5070540540750240144112003620 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 559817230 1250 559815980 559816099
    0x70b040b0712032c06060f0307140a0803040e010807060804050a0b07050910031505191217120103033b01031811041424010309080d06050301050105 65
    0x42000401d80820200e200c043c4c240000c1c02c0110354072580d443d800c010000c0082c5100783d4058006403410000d00d00641ca081c01c443d42c00410602d50079843c0e60300c80745950490f034484000c84821100401c8200000d01a48000d81414944502c152800f52206540d0b01300242008205108800018200328411002e880500300010024600000f8007000100600442c1e54540c50030142c5207000541c5140c00482c070101c069000c451a07900d64906a00070301d24160b460b6040c2e914019000c54081300020f10340003051401034200c60521349504604004004102c12400a00e00c4120564010042c5100c2d102c3d40b012015030400c00584d600c1c42a00403400f5210782009140651030708581c445c1003051001c0c09001c0040151400c00c0b403c101c000036510004c00545040000f024403900b25812600100c011640404040c113001c960760229039030b05030440e40040a48420035640d580c09108602e02801154010402281d03200001c10440001015011749501b001c020108100304000300714400b10300001d40308 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 559818480 1250 559817230 559817261
    0x50d1b02120a02010e03010212011202120a03080703150b160804050616060f050115080c0f0c0610060207230409080f0a030608070308040e0a0b040c0201020408070b040b071203 77
    0x801d080007910b5a94400010304030b01050110b01d501c103042c2014426a41c1030149020358210b1a440d0003180d141144d12408181c0c0c0041145a110100490030020202c1d0907119645035003580c0f401c204020115408000d8518520f017039003004021082e80501501c180c114082840d4038200b480d45895025072203140d100760342004010500043c05009612070605040c0590702c00d11000011429220031180240114076001225818400406104151840d4848030703400c84507140080845488910b504246c1303150996512500c04c1245901c9650451303402480c450000705642c41c108110001a814490040600c125420044891350743e1039803c6000003c0d0418065941c0c3d5130104865041d550050000c1c001290400100166602d000241002141d400c511a18201414440c41507500000904021400e070346500007820030b9540c1b442a0b101201c0140c000503961468418101c1c200301080d4812500050180400c11002d407188080f5040c1690041000802c1c04c85071038150000c00030403207100c003407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 559819730 1250 559818480 559818499
    0x1030b100f060c030201140903030115121b0e0907050d11070614040c080703030f0f0c06060f06120b030c0d0302191a0a0912030507020f0a050d08070c050d1b02 70
    0x882d0740210308000c00c1402035000b441035440b0701c140010042400d4070f041d10658000c000411000210080e000c0c0c50701c20a143c80d100280902400e102550714490440c5840045842562009600441b20030244201a035040b445403034021009002809110007440500b5180c10f2042c1d00461458100d802c4150f2000c800c1000d8520003000c0105081c0c220b8088414410700c00020425030800030b00e0b00204c81e416512010410b82d61402290061603800c5104140002c0074140c20004006005000c081e0000c14032a200301c910300107009081d115001c480010003850b19140815039180410052030b14a006c0d1103550001c9000e180807031401c05040307000b42240401041c80c20400c18401c40c4904500c1000e1200c80d40c54403108a2001200c3c00d49100500d40081110b10320f41c402d01070f0f001240e1010060041d141c518200e81c484900b80803082100315103580000c80e010b50400e801c840d4080e080070700c03854007402c400e00d195101e59541141c8075004003400460070340550650102d5595481d89680588814038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 559820980 1250 559819730 559819739
    0x5090c09090102121311041d0a031e051204080a1e02060103151b0c0c0801020406081f210602040504021c0e0c0f040504020612100305070e06010801030b100f 69
    0x1e402c001c130f103100d15a42c06008a100c1d840f050309076500403a00101118540c018010030880200b140d1040c040d0b506030014800a40880280025904c160080d1200e00d0190400c02c403031522030b034107800b01d2000e01c0014800c0d142000483c0507001d601650103200c00c2d1752842c0840082c0d0301ca0041617061807003041040001410b6981c0419403504070703031281074a901802020744210301070f5040b10705000c8141100c40c1203c030030288035005180e4a24008c1e64a20121600d5840c400c2c203990050b049440800c51603014001215401740154990903081ca401440e04d88c18080c02c00b0304c1c88800f9426440e0091041440740034812280e0440340101001031085582d6580c541d488101165050102a41c0303501d0140d40844903000410410b5010000504802c05204c51804000042c140600b050360000c03400e100c42c80c81c81041c0074103030b40189150320121300d541d41745180141c41e20f4515040072401d0080d880501130545d800001b607506482c2e002214045a0303884580e1001020361541c45141d404140e00c5000a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 559822230 1250 559820980 559820983
    0xf0b01032108070f08040c0302060f0702090603060411060729010501020d080603060c0c0118080912030f03070c020d0c0f1508150f0d060e0d080f060f010305090c0909 73
    0x400d40100444a804000c40da000a07191500b0480e88000880c2004419656151050040ca5400340c895081940603680340c1e0081181c41d0091011400d07100380008445066150001146510079000c5000b00000d02c0c0c02e955420003c2a2a110b0500640300400c91800300f10221076464021a000c01681b03a00e440c2111400340303120408e2161501500619918011252080708210f1203528064020b0800d500e94078014400b40d44010803551082d542c0700180020a480103480480b0701d80103204450729513500f1400c100700e03400e02180304e1a82d90f00401130f8054403070119003525488230f090b050010700e103000c81c0080f0b0029189200010030595541501180266901b001141a43c9803d41000c100b03091403070080d10360000c25902d100e90380105180d40b10851800351342e108031200c0040d2944103003108980c0c940c002e079103c24400c3c0c54076400c80144a0b11041d44020b4066018403042d00005050074040081508018144420703410903032180300040e04c0b90410811742000140243c82c0c1451494028444d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 559823480 1250 559822230 559822253
    0xd0f020307080a1407050d060314060601020f0a0b0103020103021b150a0b01031e02070804050a060c02041b080402040510080a0302030403140606090c0c010902130b1801080304050d0f0b0103 83
    0x1003000c51442c2d03002c02d4100ba118400d812610402180e66402a03c80300c20540c2c10760082c14002081e240c490070301000044940410601680b4480010041c80c10103600280c00c06c00c01c22286103d0364015104000456103481c0b030641102e40a09006981d1040c40400136001900801e0a2059108801550440745a60038810303204880903c020840e0750f01c800011825a10100c2d01c006a02e21803075006217040038580e00800e0f50340d00c62001d2a250555810201d440303241d050f80041d010070310f6203440c2d806608190007050b42c03400e90a1007190382d0000100b006070900303070080c001a00079651040020450300842210101504440b001c49c1c00d16021458025a00e0382716000403154075084442c1003003480c000050312406544000d110300010703511189100000c2e0404008000290b480e40340e00c2d400758541c0d9030b5806414010402c080380800a040c2848821400c0e01100640c50a160004021b5500c01000f542c2c250f40c4111460000c00d0601e0a2503102285074900c040c00c2c05404000000c100191490f14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 559824730 1250 559823480 559823491
    0x602071a180c0604210b130501200a030209010c2a0801050925120b180c01020c060a0201060504061202011403060303040608070512010b09191410050d0f0203 69
    0x1c01c101c035010400039525669a0b110203500b0010034801480b20080c036444800460004c42042c11052110740c030343c00000001076903e0409040f014900a040c09400e02940c110110310840c40700e61010580701318031491252611081c101076012603000305503072140490b4030580d50056008505803c000c01c995040018485003a80e05c81c1810b28000381804040c003a040c49151840701a241d480c203001303801f51442c8001c1c900c91030b905a091078089412558241450340d124001c8401c41071a14004800d150408000c010fa03000c154410000d1051680c1c2c0003400005250041c0d910342e07281e001050302030303002d0324654006a62083c14680081140060b80c00b907040c4503030007643d0301e40810944880d1580a4802680d401da01500108410712046008000c40c0790040c4040c9000307450848500f001c20005002a003020f500d405002030400d100b072402c15410700410b405150658902440d180c0b02500907202c0900c131030b0242da80d40902036506402a0306071800c4603a111028040786458032034060080d402102e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 559825980 1250 559824730 559824751
    0x6012304060503070317191718061f0b071a06011812020607051b04060515120a02042301020115120308180a1a010b03041203090602071a 60
    0x24088140d20305030190200b107640140c003400c1d00b54216112111110102c8842c142003041c10400f48022035202c0c0002e40304130307080da6920181102207012200c660a0040c02c501510003501d1a000b00100001c60301c150429120404e8039000d02906283c202e50a8150b4803c100c03512000c60118244445103070740c1c001044409009500640c0c85100543e1503000e514005c101d07040943c2c4042c40400c480410001c04c442c0000c00c054107168443d91102d20708161501c1c103040010b4034075030b480e100b41800d01400d03018140c100c030240c1c0c050b0768104c139405141c0034015100a5400c0d107000818510400c65044501608084460142843c400001444200c0600000c2401586031400d2012411440030340c000075140440141425412030b80c070101ea500d1009002201079140c2100402c101042c10002000c2062081c039a00508900300174501003403600503440184850380130400c00000411007584040314018038200002c2d61911400c008009002d0340c0b100601c1a418000c405040d815140c01d0288100d40b00b12 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 559827230 1250 559825980 559826039
    0xb010605040f060e18010306020705010501081b0105160f0f0c0806071b03020c120c0f04050601025802010b010f0e191202011d010813030201020c0601 66
    0xa8125180c1c815031160541c201200141408a02c0c8203840c0c81e0a0a40d004010610310441a800c0e0b000c0769a0a92080b10744543c000b401c1020894203000702c9004222001c0503000f41c05004e007079204403c24921009042100010722600c210b08030507204440a604050f00740810307441403801800c1401000e10a43d4951144034001550550014030300380324181a64800f420050701c066140d050120b0b81d0801c8095003d03a019642c040d031203440748414180015002003000301081028003215080a070700981c0281d080204020302e50743c000458440b004a1801c10b4006820080300d0641c82e40a8261120290a00c05030122180d15101080b03000058a4640c8100800044a016802c030341f002034201340130440c40d00d201301049004003140d03883c5010140824039103041e000204286114035402040c0612803549022083d5607000201d500c0100300340792440500720440c800a001144018109261501070078a5201054400e40548485001003c110344995844541c0030b0402c4041d40c030f928449202c0704 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 559828480 1250 559827230 559827239
    0xb0f0a0f03060620152d10030201051b0607020d0e03070308040e07050f07080a090b1905090d08040b0c1203100b0304020f12070602060c0f1803010b0901060306031e0210081008070e040b01 82
    0x440706e01d40944020000252510703d5603005480300c1d00209240344110858041c01d07051400300b4400688a0b000320340c0070703001c004604e00018225010700e600450080e413280400344001203941044409465000303200c4070907135880d494100c88901c11100c204010410224030001048602d0001c1d084440c3d26440321801d00351910442c000ca40140d26040d89050310a841d00144d05018030300400681002a010405170342440e10b45285d550321991044d2145100000c4d103440350a4288558080e4400000c8040e1850601443d901071001840c00740b00380801c00080441d046554007c2c91700c40604000d01014512040c8500b0b0a031550001c0c4190740143c091700700060100c4d50f04800f04c8501070403444c90141880f80b04a49219800100c955582d015982c6140303683d1156503401103d4001d020b20750303002c039001d8110300c0c08050743c5001ea1340e0030607100d101981584c0103a940d503043c68864500c2d072501c681071380c5e030720070501c1000f490b10f6005035601d004544002c5041206540c41c90b10690003000e940c10a41d80e603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 559829730 1250 559828480 559828561
    0x50904021011071208030f0f0c04060e01030b090103080309070b09011d0a0e040b09011506090306051b04060f020139090b0f0a0f0306062015 62
    0x45400960250700304040c02111401441900110310341d2404071021140c0307412003901024034110003a14000c4010041004034900781034401e900031080d0030080c0c04c3c1d00306078811351181d0040740143c0040c00380b41491114564401c1e4004010b69000519401742da5a490030030005661007070b0350450317541c0100000400d12101c00e50864040e1941079640380b240d103004445050514940d44c0b01039502481f03080000400e411094155030103217008240d0000c2c542420750006003141d640b100c008811034068041008143d07048178107401200c1d0000000301e81b5a46081c5d1610300c1160304000700d009284049004116a58030441c03021030500150000c0158581c074080e054031660800103056601030ba1405901904040d20400300c0d004601400d0540c13400c1d071250076100c0076400c00c0c507614000c85000303e28100300581c0003062104051960604000440c00c242006103450240915143c3d01d11200c2c4500750b261404111110041100414813a80f07070508450112501c5020141c1d0504245041170700722201e1071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 559830980 1250 559829730 559829749
    0x4080703030c02121602010320032d040b19090c0501090e0c03150d141501050415090b03190809040b030609190804051c0203071406041701061802070b0105 68
    0x40020000c1e060490807201d00b0070305c40b50600124101a02c1d4026223150340d00c8a85900c41d40e41440c8109916407a212034040d03600900c030851410388c0c035442441405140340042c1102e03003080d040412980075907902055080314100030103403911801d20b060151000e200302c904082c1c1c2620000da907103010007692a4800171000105031440c0420040802c00710702e4604440079142c0803842c000e001286203420540780e840000304202c072014840d402100800c0452201f0182d51405494200e8040260940c88000c2c4a0301030a2406400361907942c0703090f40350311650200003c1100544204c0781180313420680c90552460303006074003c00d010b1400d1100d100018a400b18185100b001500b008050042040c6090011850202700549001104200104145d16a1100101c000f4000d1882650324001131051600d00502a8880f00001400403c01801035032202c08680445440e071071180c0d0300700d890020b06401400142d1054001d4a5081c1e20039012803005e8019100f00c0340584502a036a80ea20400d100720580d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 559832230 1250 559830980 559831003
    0x60405100c110c090709050d06020414040e0604030c11040f0e0705010207030b07030c1223060a12080906120117120a08040b0a09021c050f0c0f012604080703030c02 72
    0x100b00c0c29012040d400c180d00250740c1700c40103207058469540e031000800c01481010324240e80150f0009014000960368000c4000206002d030b40c10090320071a407030303802d03241c110280c001010000350114003814480c031100d0b100e0362b040d8000e004201e410002c7e201500103020202600f1818000d001c03000401d0340c00440d41340101d9070850501c08096449200441c0141040703440013050000781d1020051802562040b80b80d100d610740001d9400041110f80e5200b0242e0090846100d82040d0500340145000c4000b810301c1c1c6c6611100054581c88044006162401108428080c221080d4000100302d5600110b00403848004c009031400d058049001d0086031007203880840c0454200d81c0440c0014402c100c5081d0710400203200001d0107035066002505201e51100140000c03008181e1070803d100c801e20050245002d000014102c3c1c40c4282d01060506107400300c0207040c00176402d094004c841038030b0ba8404a1440c0c0c00b6100c0010f1270179107420b15564000d0729040e000030340342002e00e6018038000141100e014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 559833480 1250 559832230 559832233
    0x20c0111160803130c1202091014041e0e060103170a02030421060c0f0914030d0e1804050a0311030c0c0f0f130203060f010f0e01030c030e060405100c11 67
    0x31807140d140c054071540b02510039104840c0d00640c0700c010a1070100302ca000b611103203c8100962256004000d500400901060725440704101c0801201071111401c10004105640204e918850301d11301e000292219030003040320f14108008205107403404600036050fa44180301c415a040e441c4100c00c40240130395940d03000980d0080005221800303808038104040301040300c500d44001c105035103901c140c0d400c0e103c1c8100412000010003103035a402100301c1001d496207501c0c80c03154040c1d0310006542ea01d1059040e07414080c841c0840c0410352104000001040b41400030301c92141001e03e84140e8909042d0740603000600c032074910412020020080701c03007032a5810024140480380a0070071440301c007804c1600354400b070740c51034a80c2c468490740c844c402c020002c070030016103a15007a010f114020486c030800504101c0c600c03121800f03840d000380040211744004e1030002171000080f44203500407d000c140340c08051048504000030030a00003461f07282c0301e1400c0800d01c5550220203098510014428010025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 559834730 1250 559833480 559833517
    0x102071715130b010803120703092906010e01050c030405040b0a0e0106050a03054c0605070204060506040605040909081b01020d290105070809090c0706054015020c0111 74
    0x389202b0740005041501518201e50510103134107510700200210b414180c0540d030303050708102d200c3d81c0114264082e8402800c000c0d00c3c04260409180c2c0b00d200d1802100d12a5580308200d1445445450705003024101030705908925585540d005001034008a00101c00a4100340c00a1140455501055940140207407503442e40503800c201000b81108600d1041325244440b0340c407507101083e0780301010007030101c2d4888990307580a50041c001501c6d86504503d0040008010400c110b550000480b0110f50040e0000038480596140850041c03059407e03840c400594600000b1104506500414281240c0c80c2d00304010584c860030204200e0005aa0304807400b210003e80015500070790080ca80c1d98450010b403807a10700b850700003e400c00001d86061301840c4007c10040100a268070500b500b010300d40c5240103500420505080c1b44210309412061910300da12a40c55024103489044403000368406030b4032410760701045200c40203400603140d1003000d600b0302825500c9083d4180c220707041c450ae0804410310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 559835980 1250 559834730 559834741
    0x8161d01050907030f0501230406080d141227010501050609060f0903070608100b090d0f020d0215031006170703020c070b070c06110c0102071715130b01080312 70
    0x1402507000349020249900c0e10130300445d1005612500d8060a00da403c66100d49941060304c40c42d16922502c01e1780242d1a1950a0101d0200010507801105151611402200070030034881894021014003051035862082444174407100700b202030301e00b040340c59100100d0f0800c00880b1401e0358001e00c12207070401000c102140290400200414880903519019441c1000d25004246085a217500600000345c401e001d115030380000300001c00c0200300400d4070b03c1c00d0400860000305d2004246c0d00080171b03541d030114141c0454403120190903041390010b00382e030300320340481e600e46540d9071048441943e904801d1502094850042414003450002007103c0320302c1c1c2e951300d10154001d60049030440b071a0b22a000002507101d400030b0007080d07140c1c17282441c409014940030740500341007459540100140c100b01c40c1c001050741d00040345011115542d110703c0400c1d02051820703051000d01410001da0f210080c0400c0007180b03002e07801203a12441450780040700e030f0340c41d0b854a403203000781100c80c40c0382050300780845c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 559837230 1250 559835980 559835989
    0x31e02090a05090c121008061e0c03070918050411010f08130f02030712020f0f01020a0308040c08030a051e070b0103320a02010320071b0302060408161d0105 69
    0x81d8000c5022403102e160982d1703000ca004c030b100b80440d907800010039001000d0103d05000e01466810071600040041065110450305101c8040105031003c840c1e000b0002512441c81000118020b01d00000c6254081c6643e800c0c1380c0103024115000d07903048081003411b402c203501c14083c81042041c1d46d40d640407941c03a008070407018004114001e4881e510b95841d13900141c0e50501460004051a8070301c103507021000c1c4103000406261103205c9100d0201c0704907034080c07030342c01042c6105140d030b041c50007403c20f50b16071408019814075500125001c3c800030500754000798000d0000d0211003464541413818001681900159109800c001444c00005500400c0021031080f03a0491242c28140012566a01640340754820301801d001c424881c1d018004070b40035540c0511980c1300c0743c01107498403c504007804a144495128505006040c01c4200c2540048044040c40b40e401450340200525901c5982c1c4445590f00c3c400302091802071a4101300c0000e01d240310b220110540312801a90000680c0f0f01020413 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 559838480 1250 559837230 559837249
    0x1404061b06020c032a01020307090302090a0e1603020a0b041202100905031002090910030209070f030b0303040b0a020f0c0f010c030c0f0606090c0215010e04020109030b07031e02090a05 81
    0x715025038080c000c3c09201e102c24000f501c400c4265903020210384258082d41d160000c00068806583d91041060018135a0321120303d1094a40580714404140c0361b019108000340340c40440c14142c1c0c05000000c2d255000ba0030706220840c3c0c0221402c0d50560345a4112650038490b6200d11620355005a05520043c144211070003880407060030424000741d0355001280c1401092602c89140607800112031000d40f0f048454150094159442200c415040d03602240c40d54202400b01c00a0004128003803021612903002001e050704040c3c103407502c07583d48000e0690a900840c031000c001d4003030001364031099540050003241c2a88014440000140554015541c82d42070030400d80420100c0340c0d030300c40810920700c0c1c0104103034800c6030002400c2e0301c0c1169507412140034000c00c0045401c2958548580d800705c98519040d10310540c3d40010944483c070042e562490540d000802400c1da282c20000841d17050361154000a00700b1078180108004120140d040b88603142d00a944101024014032103424900d041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 559839730 1250 559838480 559838483
    0xb0306011e03051902010324180b040204141c11150909090d030606030603020f062d0a08060f0102060f1012050a2907031e0c0f1404061b 60
    0x200759098490300e400d0b04000102c66007070703180c44003465894110750345032003103c1c508400d04a0750561248003044110101400e4410809600205148003000c0310b030039801902e030000c0082c4110360743c664400039584140d0b4901551441030110511480c0307021002400c0d00380881d0f001401802c85d841c10400c1210140807101c80c003403448018000c41785a6190403040c2805000d645006020540302039030000d042e1005900480105402c1c51410801070b25040c00c84d020307110301191201c0c3c580b0000510b00740c41c180103003e0400014004262450450300b10801080c0e81e03c02540c8005107a074420040c01012600c80d426140141c2c840302c0010b4208d40303010492038104000c0e14507a003905681d5103001c42810200b00d02038030640c04c186580300c200610405c03103420586140020300041c00c1400315002075550010004814542c94075034950250340010800040386109250400c03d600b00324000a080e480e60010003c0420041d0704c01c1061848010700795400c4601551760130204134120304281b8421045d1440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 559840980 1250 559839730 559839779
    0x6090e090a0c0305060a110906092b0b180309180a0914160e06100f0507170d0507080c1e1b03130909020f010e0d050109030f120b030601 60
    0x10304200242465848100640c002c4000700794908100416408841603042007c2d180700c41007003640c00c60b13100d160179a0814681150f201401c405220410304001c0b00c480b1910070070b0030144107240d041001c07450342e43c1d00564840851202d0542d036641101c1e503e11a02d006598841c0d800b82182001c0c505103510203034010100240440d203020759550b030403003210ac8200301b130301d803500b05003c20700b200703007140c050072008000012800c0c085041120200350310600001d100810030208016020416019070100c0781941d6002c004e01030400404d501807000354002c41401a00380f41031030041a8118440c0f101c10f8090740d40c1c0410b15141220854442c541c1340012041d02d10700d103100380300499134040450701d8010440c490b100a1607a41e03450408a051205294004105a524015045025854144032f06a03c0e0000382400b49c103280c0d01c400011512040140010100e41c01c0000704010107900210303c3e42400e2003070300c40c40c8a20034405109010344034a820701da84c0543c0314100401c136012178840710655454035004c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 559842230 1250 559840980 559840993
    0x31c09110306190b04060521150709031103030306090f0702010f050f100f08030d05060a24030501050a031e0614070201050405060c1c0e07050604230a06090e09 70
    0x802c0c1071a0040381d603000240c2c03504409001c00429400303140d101003000c5604202440c20180085c0c412038555241e05400f05843c400d031648450200000b00a1410003140b100152071b00e203a00a01c120301500007203618124606625005050010659000c0c42e0010b184414079074628450f003482c2d440041c4404119074840d60f8800c1840520703c506030003119140110303509842d201074104403403d03155100411002c4040c0b030403c2175607800300c00c2d00c0c0c04030902500403c0c1903d41c3c000042c01c2e14510b82201641c0c0c001c80e909230b010065a181c5116043d107840d201408507a030303200100204100c1a21000d4144492444d501da03841d403110143e150707424406c8800180c591035003082c80c42c10300021607428001d81c1d5074200b4041031080c10040c40380d1104e54050b0080c07901c0f19847c00417503d4111341070303035580060320380c2940f02d02d030f060a20501010301400740090b600c4035a1040a0744018251194000900c1c40f0b008403200b03a0b041c088004415205943c0750320f49280d00c1c181c4030301e0160700700400d28072680c09902e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 559843480 1250 559842230 559842263
    0xa17151f023a03020c070803070f080306040b100203130e0105010e040203090a0c08030d18021f0c0204114b070503030a1a01090302210f010e01020714031c09 69
    0xca035800103030b1403980c0040c4c441c1d0403040b42e245002c0c01a0008109a80203001c0200007680d0a050200d400d507100300400c0e141c3e110203010030098800480a142d0008001640049070b035030020141c05e82464907848100c009035148000209048280a042e0001c3e0804005038441e00b0301d40c000356000494003048402c003074025145c03085428016004500c2c9904006244080030426026401d207407484450b465114000a0f40040c40e0f15003403d50907142003900702c4406840c0c4d400f5010307021542d07401600910110107064540102544118540328800f40904000c8003035150103040340540d20702142441c601000d142c085295140549540b81500400802c500c00c0052014009503014641440000c02d4241b58083c49a200c046051003090402103035040030009652000c3e8410b10180d1340d14500d031005050120103d003000450321510040b076003401100c20310600c056001b801c0c42401021041c01003c00c03002c1554a0784100c09007280240007002151410002592110f4a02c07445018444c900c120003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 559844730 1250 559843480 559843573
    0xf06010f0311040918121403040b13020d0c052e0509060412030806040501090e070b0f070c030507060905100f080709030510090c050d0506010b0a17151f02 68
    0x5881000d00444900e1485c030081281c002c1d0503031180320742403e00d549504924102800540001000508400e881401003040584c1491907a11050740203045c002101c2d041c1e04004201038101e105050089151008001d00301c0140c3c1c0403180c020b11141d40003212180c200c4801ca82d05d4004d80c900342da000000304800a4800035940402c81c44500c240c40d040240c0c5095020041220b5059100007003450404103040034200001c521003064403403a6903000c1c1c032000c80f083d603100103010f03100700148200daa9050100601c18001104000c0310044c3da51865600e03118010300080b00c10110450003c5449510004581030052550a906c803034589042c4040071750300d07100c1070700e40309415404440441d070700c001c1d0f001403109029a64020b004260303078041d5550207907a103440e9a5901481120f01c00c880114000101d2031042404800e41440000400703a10700385190039545480c551443da1348078641160840d41c25407042048811502540c0d0054440d6012080e4641152120303550901e140200380200100c40c405d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 559845980 1250 559844730 559844741
    0x2703030d060e060405060303091203040512030714010e0a060e0c06030103120e060a0203040315020706050708090d0903110907030f061503140f0711010902030102030c0307080f06010f03110409 84
    0x1500d20000c111285030002103081600702500c0a0f000c2d40c00c12080000030744002040300c8207040705403050600e0007402400b150441c001c903080130b540700580241000310a217002002c2c08140e4011605410409011320300716003212100f041d0640035070001c0b416800401c141d51300c649494506102910402200480001d2250380241c0003214004110180300f400c495100c00340100d98030f415a0341d98603100400b8800707503981c00342d4803008001c4405100408500c1d8040e0301500c55145d8042030a110314140a0000351000c0e4040f24628204c1c1304000f010307282188141d020b0021240c12824039075450401e01c0c1400604940205a501850707200c0707070000081601c9125030030041c0031481c0200c20b00307001104010243c1e21050381410301952402c00b48a280021722203d103410580c40e04000c150f9903007925805000d416030550203981548048100309540318240000c5200d41d01c40c0d9108070302035490088110300c1d11000d941c9140010a070142c070001d12406a8408542400e0070b010540c14950307030b140c20805490 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 559847230 1250 559845980 559845997
    0x5041a010905061606020f0a080702060f150a0807152c0d0303020c0a050d020f0a080904020309070306090b040b010e040f110409021507061415240d0614060f270303 72
    0x4800060032402c0c10f270b11500e00c40c0c2050851000d4240c508020200c601255805420400c000c2e04400c091019a07850080440c0209015000c1d038040d1661000d0711094000314103550f00110726681e40c0703128014598903031000c6410031300c1c00300c54200800c001032010110300b6800071000d041c0c2c02c000800b91020100002903049109000803c0e0349280154024180304103080716942da07601030290800010a68403d4a9064509880050322541c900b1034052a01c24107910160285181c200044c040c49800d1814500c00d90013541240701c0769a035040081900c4d08200d40190108100c140681d00150f070f5041c1c0464940e4005001044814003030300015130440c40490700c004403d50004a040130082c550051203500e20f40c41c81e43c400c0a1500c00000c5146288149070180700d802000501800c5000e1040c21601000c01d40c0315541d00d034135103805450010192401078000c0481c4030b640020942c03908904880510035400c1c026418031740401c0c9081c100c0840c20340702c1074055021040031140d90320200b01800814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 559848480 1250 559847230 559847257
    0x26070e1306152306120c040f06090501020c0d08070f031e0e03010f020c06010b0706060b0a0c140313030821071701081207080d0609020d020405041a01090506160602 72
    0x54600780b1540000403e40f1191107012201c0396031088640c2c0c41006645441c5040b850301809aa101c0c142d40c03078148a0303a00480c030119001d520100d40607911400340002d456080c1c003140c000c00c14500030882600d03402200204121410004c0c10300041d5219446440507100b41001c1040400c401e1508400d140c1c50b060340400621070707419a0343c00349070900500b000c4c0c4c01c03003d20131032400380007074080c43e1126070500070504000070001d510002c00009074800001080c50041d040d440301d0100200808040710715030203a41d22059600740c5040340c0070210440750403030b454000a10750940345a0303e4807503a41010307c140e89039000d1650901056011301420034445c54050352603c039040316410000000207010781051003da40080d42d140b8003000307842e04407402c140c0c100000e140c5402101c41084050a96a04201e41c200c0c0040b66244105446401410036078408480038451500354900355005280c90042050000d4480241041a400c1030001004451040114030100c0f42c01a12610280da000400f05a10b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 559849730 1250 559848480 559848521
    0x150210021606140c030609090a1a040302160b04180b0910030209090d0c030305130c0303111005060a0302061b03070305030a0e0a02030d03020a02071206020426070e1306 74
    0xc2014502c10281e444880d07080c3d0700c07194149201c102d2580c0c0030040c4020f00841e01c0301d010418803d0100700b11706046500180c070542400c12020244228034040d14103c002d4030411403000941c1d00d00460320010f4400c8140c4543c01c1919084032840403214860040c1d8107642e80d1600c0d20103944410740e100344181001c1c4081e007e80d03865071040c8840c40700014a900c1d02c07134000d040705502d42c5501540112815800d841c01041544600342480190700100308020541c080c190000802c1642260320786640051104c2551421402504c881003612811200c1c00d0303125010319428401440d001018113800c905031f100d6200c255980407081e903c2d40d0b2140c40150003180000c010444039000c00e001d0885100c4c2690003402e1202c01688c082503a808403d001003042c10780119881d10300324400c000d480300920018501c1e15017900710782400c0c0700a510a016201015402620180c1803160769143c643c00440741070000d000252500304074090100300a4440c0f40340301c400300414400720f0038070302824490001c804a03a040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 559850980 1250 559849730 559849733
    0xc0c030f03060901060c11040c0e04051e130b06060a020f0303012409030201020627070618050910090c0e040c0e04060608010614070f021c030f0203030f011502100216 73
    0x20f030508164440d208000422804400046402940c5159101c0c19200404c046454440680f00c040240103082d030414584802c00403070301e0749807d0007079200310043c0f404850707603c906109415008184102400d60354043c1c0c082000c80c00d2840040c219100c20780306603200144240e089509503802030b84094035000c0a10804407005105e4081003064000c40d0405c140104d00e1a40040d49907800102085450707a00028024070b546c04040800c25075204410558010503142c1002400004041080c8003000f642201c1c0401e580c01d1051040b4020010400426801d9240040e041302505101d0300c280d040048130095020540c9444c010300c0c106074a652190010701c80c00320148021680650301c003078100a01a0010021643c101c0e00c0f481c0100826803c440d903031401400d0550003030511101c002e41085c010b040c010412050703c012031043e18030070f6407480a291a0000304982d2030000b03440241041031580010451007400c082080007641540c010b54100008184211040341c0000d07140d243c41403000c40b900720 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 559852230 1250 559850980 559850989
    0x50a080f13020f1c3e0f0d050709020d0501121e050c0d1505090619020a02280203060a0605131a130c09090905030a051c0608030403031719050c0c030f0306 68
    0x3a030440034014141130402c0c20708020682d170365100c40d070080801603c540199203454a128400941107411114515980e0903100c000b980f00b400003c10307040c42d003c008114022110000601c0c16005880c100913074080150310b00c414001d0b4001181d071441a09070558098035085082c00384d0500941c0c501c80042039070200030058540061080b8040d801c06e81c1040320a0b84c010300d0b280e014429251005880319041c2c0030036864408048124071007003c98990044407424000401c25205100781c0a56599407105c1c1010b0302a43d89070f002d110b600071020038056004103019032100100549405d02480f01030030500115200702c18a4021001150b200d1644507a09500529444020290480c00300100d0390603440b102d85900803000080100100010344406507004114405003010609078204a450740d00c8060941d031354460300c001c42c0881c103c40700300c821140302862680c0c800c825a60341e0794141d602d0000303440001c00d80140034520407803062129410b001d000300060501149800c045176604d040020401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 559853480 1250 559852230 559852283
    0xb0405100507111c090f0b030919050a0b0c0706050702011410051f11030408071401050307050712050f36010f0f020a080703050a080f13020f1c 63
    0x14070034403c15420781510003000244164180900070004200301c0c24100341214118169404803400860140e408503014101c1d0008500a210080c11110110480030f00003450034454040070344150010380718640403800c01c004090788256000390302840d14480d40d4070402180d80503101040103030f540781c440c10a1200c1c0030b040603070094030003208800010710340300002e4214150465000c00d135030148101e1300078a41c01040302c0d614000320f00f0107070790b110741e15020160350720152407049440010380541000900c1d4016003ca078000c1c1c40c1969103c1c03a005d50703503c401d00c58a0000a1031010004104000d00081103008060500c00c03124060b2418042c16051128071200045074075a00284024051a04641e801420b0b95403058200c1c206244150742c4503030260305003000041c01030071000001510000300f6511000524002d061610b03041a16126800b082e82d50704000c840181810b182044540702520b09141100342100000f04184040c00c0311040801641d01420011100350b10700d00740f0841400100d5251 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 559854730 1250 559853480 559853491
    0x19030914061f1401110a060507020307120302040b1602030c1003060504060f120201111501060309150509102403120207060e0a1a09090711010b0d02030a060b010c0b04051005 76
    0x10042d000e810886080981d2010f0b60485050005a5100b44000d400a1041c0c0c0c5603550428000c10292401c02c2c4080d440e90f1118030110782d075800651164108901074426030b000d903461601c0b06814002c20108180350703108040422307a4140b007031417010031881d07581544c5d08e1505907984c0c1e40494414507202c00d10044e10007540250544200c1d1403000c0c403401003e0861400403580901e4443d0141d024291600d04000002d0900104000c0e000008141d564041c0c00041505104072261140141d000c1d0504d401c40d50181c40c4c1074055003100b03040e0002000503401c410072150003000c81070602d61600c010764405650680c82102c80080e0080007507603103a0103114000092000b410300ca1b05c008160700c0020411020742c06030090500b40341d0681a400030220090b500310141c054181e10b541d081980c00640340d03517402c0020310200c0d0300f07165044d40e00b4107008201520460380a8010030783c11120b070750382e00060708659800781d04006241840501142030648024040d1380141c2c0a020900030340d450321410749600804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 559855980 1250 559854730 559854781
    0x501060b0415091d1803040608250c0b090f0609010c180b0304060c11030d0e07080a0302031e1e040303020105070504050f01030902040b0d060518010e031903091406 72
    0xd04200c05024041c903803003420340d04100c070b62139a07a801e007180281c0004112805041d00c00130070049851030b00700010900408001102e203c21501821900505444800c88240017920340d04c1e1541c0000e00240c3c0341c1d500003881c0d80595007010002000c96240c0b6100b2290583c5507034403480024251038000d10501c41516015000036803007402c1030b51080d503030310019000420081e0740e45280110580b0a101c8848080592019240e8542490f101c010140100100c2000b15018000c80001d00480024030aa5240d0f0703da0007950a204a81c1c11880d14800a12501e0b12405000c012455100f00341c0c280300b0120302242c41c8082d45680c02d60400908445006000400b4400200300501050f503620440c01a103080901c2d0100b0381da00c0c9440880d0140c0b800c1008190499000b0720854100200ca811451141e0788020389410010211181c4a082ea403240074040d0542d04100501085e8902e0f0101322260241c0c0c80c1404108515035a8030401d10001e90940c031107882c3c100b507042c090042504541c003000410b0050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 559857230 1250 559855980 559855997
    0x405130c050a0e06070816060b030c010e0418050d08070206060924010926121206010f110a0c06120605031209040612140f01020703091206090501060b0415 68
    0x1409016031150380010003d00c0300c1c145000030656106011116000c0e070143e105516050101d211240c5110a0700003161018208a11a00c550400041003152002c1c169138180c0c46c103080b441800000e00744446d440420384885030104011400801030040d0b080210b907580285840c07c07160090520348003810261113965150144800c4000300300c801040042d1500440303048500050060701c0f541d0b0207501c46a002c810b24910907410f01e841c2030b0000a07030b02c1d071041611020000b5074010680351207890a01316040445002003181940715409801203030040e03042c050315180408212902d04100d4207004c030740c401c118050901c0310641c0410360700080908000d00340410303810200000d46400004a86045180e00071038450b80b160345a030132850003442c281c0d0303440000481ea401c100e4026000c102140c00c00384242c500b06802540c0c14802c0b5000a9050f55a500282e400c104031410444640d9406503074032511540c8841c0450028450b4000504801c0802559685498409120951b00d01c0202c000e104480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 559858480 1250 559857230 559857251
    0x80d120c02030702061b0604050708070602070302310e0c0f0d2301021605010c080708090a03080411091e130b0c030403030213030501060f090204080c01210c05040513 73
    0x10f0329007403903040b01d8454132081c1920a8580000324810304000c5032040405120510101080c00c134140c441d00e40556850585071002640d42d5119488001e41200c94003001c144080402149055610301410811034100d000c114010207691944a00c2131180e006040c40703142d14584124001e01c0038000307032a4103000079502d032901c0c0c08050003404406011440640e00320b8400b4020b40c1142c2810462040036968890036060040c000c00b480d404030f101141000011845a90043c0d06c410300c650194001410070070855507044440ca107010b40200c5900044010540d200d94401a202d80b20380700039403440310380c4021080c0a0541c0c0c10040c1015403000080c42000012501490355281c0c00119a1510755607500c903490110000d11681030040c489108480002c01000b070190040307c1103506403484000c0303c1da2038410304412403281c1c0c1300b400096170048140c590306501802c040c0c42840b0b000140c404400c9610004881900c000030710800c00100c0018040c01549882580413074400e110050030802801074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 559859730 1250 559858480 559858483
    0x3020a081209190812100f090f0501050a050a03030c030512180607111908070605040c0608093d0f060801180c051207090c05190201110409020904060f080d120c02 71
    0x101c0c5d1840d007155400b04001141d030004096a603009080f4240e0b190701c0140d0303032001400100b19424005548078206800000c9514110388050207455001f815000c4039842c541d030030303524102c081d070044007408024008446685411862144104810410498101803044440e82840c500510341001c3c03008034241180100c0740002c0b40040b00800c004000400c400c1410400078a000b0444024041c0307042ca8100070403c94007503102030449490341c8511645499004200351180250284801c10340301c55032091550014505000e540031440003602c45121054442c260281e60791035007011202c94407070030204a03000e0309100711424210b0115100c0da220900e030340c5001d40c1003141c0c85071038070030303190005000f00d0b07010705000d010020846164208184262200040e10341e030010115540d04101180c1400c2c005070040c09a00200408610486e01e01410b00703e500c40250480080590829901e10b00403410300c043c1610f034000f2b00505801400c1201e800d14004041940c4000190011828000607042c00c540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 559860980 1250 559859730 559859737
    0x9060e010c1b06020f0a170114060a030b0f030a060b0f09090a060209130c0801030c090507020c150f160b0c0705030706020d18030e01080a021303080703020a0812091908 74
    0x82c01c50010b100450500c240a07004141e8410401c80000910140564011010150b10500010f10f08420fa0f40d85101e030700c004600c84800f03900140204000c00c3e00034030a80c050403084200400003500c0303a100300042441c10f8140f0104030360b55540e5160140007464071518a508081c2c0840b01c0c1c00a40c508180400d8a0300d0f4283c0700113210540110701c405280d40c411200480344901c3d40c104204800b40e64000504901c400e00c001d0f18062603001c030201c0d50185500410744122055001030082d0396410b4144040c0d1702c001c522008403003105000112105000e0b400600800c240080344100700281400c04144001000c0d002c0003050008120070303030000d40003201755060103400c0b1000607110007100e82958050324401c2c2c8030001c00c66841275180101500700c208030309114000c1e031f50504590340e4400403004a104134854000e41700325000c020800101e802c8010180c0a1080c03043e98203071207940c0c0d03ca40c52038000294201c00c0c1d4283c181042134107031080219403070480f0041d03203040340c2c0183d42d107401c080b520 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 559862230 1250 559860980 559861007
    0x30806030a0c0e04050c0d0804051f200f0d02060115020a151a0405070503090c04050121081e041805010e01031b150c0c0504050601020c10030f020d09060e010c 70
    0x783c1c500014050080a104003002910701038520500b054040c500b406140d07200b402594400c00c614031a000354028013003100c036010aa9a01c902080604c401c0542c2241c01c4003000d40c0340a8410001c0c03d090405042c40803816034041900200040e5050517410565038090315850070840d0302203440a40801c46031121101810342c00c0d000080e0320420450301c041c03c801c0e807a8115800500384028412850342c044000c621990604060b1460441003904110984400b84100641110a04005c1d506d40540da00d4040e02c40740b02e01089032400141c80310104046031851184582040c011808120480085428442040403204204003035030406102d03a80756001804003038031000c510307100500440280d0070503401404903548074025060118500034950341442e0b0781110350b00c0b400600011103003014002c403802000160003901d03c0c02480030501000c03401c444484410951911a0b11034402d0640c40201082d8514036804900c4482c0c1341800e500b40c4102041d0f10016a2400004c00013407a0701850050307262 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 559863480 1250 559862230 559862249
    0x9060903031816060c03020607030b0f10030b0307030b040b010b030c04172a0a0803040f06050f0d050115090b130b0d020f0d020306030c011422080d0309030806030a0c 73
    0x85440c4032146845605450045183c04503e00441c3c140d4029441022503807107542101d009941c2d0070011800e031100d81c10a150030110180c4100d4152414006601c240d468a16000a4058040b000245042d0942c0e000344c0e0401d01c003a080c00140901c400b2601c1c0500003c84000d072950406d09403140142c4039522032000ca14030042e0442e40d04041c244001c9035040c00e0070141c88135800c90300100f056883c80d800b58051294041000001d003041022094038103d070508101c88001d945024400d0321a03601a0301c4000d0742c0c10742044850980560383c03040078041c0030200d030000001078131910003070319a12003504007850780c800a1000d4084460b00c41d403c28140d0300034500717480d2188070031312801019009a180083c450540172402ca03c60501903400365104100417400c4034150b416880041d181d5045064060b1003183d4104109070300703198001d110308540f101182c04400341c90390b00c81215042c01408216400000d03100e454900c207140c0d10010107504030104801418820080713981b03141c805102032184101c1c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 559864730 1250 559863480 559863511
    0x60501080c04030f0309050d111f0203030c03182b03090221030409021804060b0f04090230071106090a0b09010204090203040c0806010f030b01030b040f02040f0c080906090303 77
    0x2054800d4241c2e80003841c02070807184403008240b820500c55010802201e025680c007052848ac0080c2c0908000c1d200f199079009149507866216081d0361940c40284048108500782082412001080003080c07030b40f216030003110010410803100742100c00d0900c0340c81030800d4107100d440e8025036280c10000301c0b110200c95141c00326120001d1074505500940d800094810310204000310708400100114140e14000c807010041e05841e00010f071000d008031003d50300e041100340070a1103190000d500602244015003140000054003181c11846d40c0f5909881080c0540c1c10301c01c1c06005a04000030b0a0842c20701d42c09041c0600d06603942994445500e1000b420b074524010104540000c03c6d4121006000502e00c155964a850b003085030388172a603403051800d0341c41010000106460784980800c1038a074858480f01c03181e46141c480540e03ca0300940305036440360509088200580c0c50b4458650352040c80c40002c248100790343c0000e0711403d00200300419a411902c1000141076011040300e901440000e510b004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 559865980 1250 559864730 559864733
    0x50304080d090f0b1302090903040b041802070204050a0606120b060a032703080414061b090102030c0a15060603022107020f070f15110a1410060e0703060501080c04030f 74
    0x8540700e18070f002411245500b000d10414010690070019243d0003524070003c5911030020065480c840c621a00d00095410302083c02182c00280d0714001080b01d00d100907003016095000a4219117081d94039119040da01c5008000050300854076202c0c01441580c2045030f091040003265080c0320f107207050740826030f6507802840c2004042c8003c07130981c051400c0c444020381c042c1c54003526014007a103040e54000405010710702d88040c00104d0f0780c42184020128034100c919446480c829800003c0c1c090305500040c0a0044e480d8000c101c10b00080f40038802078514045c3c0c00301c5000895201380c1251003054010806040b0452601c00c145114104040c0030094650310808101d00702024024840c21a00440100054000340000351b041664000030440c0010070070f814056840407400313440041d264107c0300c2e6100c0460040104240d000201c001030b11034498200c9a428120b0321a80c0003500080c1c03440051010182c0d042c442d0304050182801c0c40d0301e560402d000815143d02942c48000c00306160b10240c0b80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 559867230 1250 559865980 559865993
    0xc06040b0a02040b1903050906070c110a0e090c011e1d0303040e180c0a12061505060a17010b070c0b030402030c0915030f241b07150606050304080d09 66
    0x1002044d14140094840030640c0c044030705c40040030480340011742420049a0b101d40d02145c0c0b240070385400d0301c503a128014a59602c166001c40d580c0000d6004210840004414000384e44192103009010f000c0c18a403e000300001d00161500607900b00c1d40500d42420b0300b001a082000c440c240c001903019095411060400203140d8400c5402c42039801e5a01c1c82031001c4a054003900300405400a400c2e510524003810a01c420003100d8484c0580306131041e00d004011071310a40c862400c2018841400c0d60f00f9490f440451340542c841485178001130501c0319091440c5194508203030140c000e0024192a01c1072030344903655850780c0b50181c94151040040403c08560303080000b9004010f0150405c081c2e803406c5c86c00741c000d03003080f40c2c8a0340c028041c0801e490300d20100070400c510070180e1501340d00910f1400101c0c0b6110213000801a4054041010350300d00b00c40c6001c0080c01b4482d21880c06100d41d00d000c5046041552400d03400241888014418880000d4194040d140d8003c0d03058000140e20000c0d0902c2c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 559868480 1250 559867230 559867237
    0x120423010e0c0d1112100605101b060e010e0d14041a0c010603171c06060807050a140409200306030a080c0a020909010e190503090423090c01030b060c06040b0a02 71
    0x131940549107400101c0500c5010034190620141c025080014640e0754050203501d031008030b100c0340050002d41c507100603140c80c1c82c03c401c480c50240800203411102c10b5400c0e0300319041e80110744c82030360005d4054a0310b19803142582170b61300d03d098509420030b4903100d88214007000000540c5403005000c940c00080041c01d42c4030034001e540103600180c000c4611b11008205070710004414048040100314201c043c0e03030713600450cc04c5a09e40d503681500c0743d43d10350b41104d807500302d005954101300200f00960040008103000d00003a0101c5100000c21650240920401e00580464541c034000b091041100c035540105010840b0ba404c1140c160307030740c10407008182c00e0a2010400951244d818024820f144c001540440d1001021004868805818034015503101c01050070041042d8410800c80300c050801c1e4100000c00700b400350070b0030140260414560500c110031034010403554400610345415603454040c1e40014030b4291801c9240c615840b56a581341d8100800240108202001040c0076100e10fa048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 559869730 1250 559868480 559868513
    0x20f011101020a030203271b130509060919080a230c0f070807180c0915030905061003022107170304030c0e06060304060e03120423010e0c0d 62
    0x21541e940c90f8500c00b074025007054070521143c4002c400d010300180c5640d001009004129401800300c800322100401c02601340d408040e0304001685981d8a158003640070700360007654100042d00003484c007612410710340321303907941101d40e08404000c804003c15103d40446400c0000781c64542c168082082c1c415034513208400c18002d02c81c200054643e01440b0120792000040d02c1c1c0c1c402c4d203d209565625855071104240155000d44112051001d0121080d40c02801e032064107007040c003401ca5644030b05005884942070b6903070110b41c60320b150008014061080750303440402d0b00c2e0580400c60840c4c0115600900c0702500960320350481c428599500c208100e100000c06901d5071752440c5040b11900f15440c1e42262008541400325000f010541044c0c000c0c0d0f00b84151409001641540d4442c3c0b9a20041e2881c1503019a86000c10002d06020712403440e4254030483c02511840c071b0182c5004942c1d00094105050100c15134504884201007490209503201d459070120b4441c440a94a801e241141c803418484 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 559870980 1250 559869730 559869733
    0x41a04081b0607080106020f0c0103021b060103350d0e0a02101805040504051f0605060403080403030e04110921030307020115150e04021612080a15030b04020f0111 72
    0x4505181a0005040f4401c60f01c69a40149076607a88406990360004e1041c2011150040011080790754865170250030040340400d82101400600949582045800c1e001513420410f0410f0000d900080c050802c03c038161242038080e0721602c04031503640d180c00340c0001054400c2d2944001c84800808000b0f000742c0f55001006a082c8030791402028045803060700c0c2c80c00b0a0055184001414640b9101d410320654004010300010800104c0c0710301c0c2000c88040d8031011303c0c2d56020202d001d442e42ca020b0400380d0300c01c0d0510740d660390031420090842010790100c544200c0c100000004000600001e4032020070064401e000c1d048001d00c1e80c20304500ca001c1c001180762101000300030b07180b50f054008607031080b030406112400585420742400b4030040b880321180801c10303003040303501030341000d90082148003800015141080d145039a110b2000f01c0c0300082d40e0004040105010503480c40d8428483c40c0c15400c2c5c0d4804000346590344a10303032880024030280c424401700d14042602d034000e507080c00c544001c110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 559872230 1250 559870980 559871017
    0x503041e1a0108030903010e070302062b0f0b041a2d1302090103060e0108151801020a08010f050a05030a020d05190c06090506030705180609030708030d0f0203041a0408 74
    0x101816038903000032050906c01e601b030030324400c01d013240810316605072a006042c00c0e00e803900420a140f16080c0c1c0d400510301c00180403402804041c024410003510703810510010420b4215401040f042d1040f1100c10082c21000d100c81d40011399407500210510382c6245515000c44100300e6a03000c02c003142c0045140c02840441d05446110350650090001b420b00740c030f041203a603840354508459440240503000c200c0c0d009e2070800c1401107160180941c0401c140c4d40001030307110781103259803d9802403c052804501c40500500c001aa400c0041018140654950302d105180c000025aa2500c4c0308002e40602110200c038410300c4018004070b8000707080d038a19240c0045541c43c2060700ba01c0948114400101c4030940454240b8085084900554a542e1814141402c50f060315064031600300080d5441201005403889503142071051400400182c8080c51b03c4104101d240d4080e104c0e40d8030200c2e4000c0c8104104000070740503809070b4085030701c600b1840d0030596640c902108207100d07410701d1084000140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 559873480 1250 559872230 559872239
    0xf060d0c12050c072409021201020304170a02030d0e07030204090510050f040b15031510060311040e01030305130305031305030f210706060e071e0503041e1a01 70
    0xc1c020308000106100400a60b56a00d0b0040707400e018000009040902440e0117418000c0100700c400d0b6400d604010010f24642c0c0c41d0300240351080301c007001c100c00365008003c02080c400040c142104200701140c6c0c07945030800c54800251248101c400c11000c0301d84e2643c549044001c10011207000d554080e1080102c40b1460a2041c1e8680728031030340c020030b281007000041d01005100038660050303500c0315542a03071b0b80703c10020f0599801040d000d1501841000c113422106024000d05601800c01c505561214a0400c00001c0984850780d411011a91b410082048004010707c0d2840c116501460a1601c0340144c451101c149602948050700500c00440e6503020190b507030044a04444048040780c0c003420062050b01d45a09443d10401d010110058943c00b568000301d006107000b5124080001e0b540e521059135010700001a00e20000240645140340c90300740075003148400c1100e203030600d00d080d881d080e07680f51080022801c040f02c0c260110603000c810841004090a83c00388001191045981c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 559874730 1250 559873480 559873487
    0x71b02091f080123090d05190507020424050306100e2a09010f08061e0f090109050f071e12061d0403090504060b07060203060102160b09030601230f060d0c 68
    0x4045410000c3e40135500464039682002600049582044d290141002c60208559403823050400f000010310800304009401643e581c82000d101d18007103641c0400150407190b10031610382d15130f00106d019605c01c4003400141c2c25802c00306021691850060880381c1e650182c2c031101d98003d206c10306d01004910500703c000d4000c0b90301408603035000faa00c10391200a41c0310102c503084c009813001c5800664412580c3c203a40b990000002c60b81d03801501000151100d1070101301542d000360b1140c0140ca42c1c840520a9015002c4403440c0c206400e403410501e1910140d521b48800c842c0c5808410501c0042c83c0e668401500da070300030740000c29511080901820313001d910350080440440e001c50000b20203010106142c0b0301840b0b49019241c440d000d030360030801c5030f40d0740500941c005803401d07066204a0b0751a40c910000b101512010f000d010103c952a00b000344180351501038180c01114040c1030030300072000e040b46c40c003011014030304046038003449000c019030124080d48038902404003040c0c100a50416002e40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 559875980 1250 559874730 559874771
    0x702030106033912020405070203090a03230a02010f0e1908160f0803180a0801050115020c03010504021f09080f0d0909050705030705130e040b071b02091f0801 70
    0x55401810710a08805044014003e4450040c8024a0301c4018040c0260030a5400180c4c004000c1c011a8544004c03040000c0c0000c0f02c4c2c0e8001c80382c0740b460417074162698800e0701c2c0c44401e40c40c030f94004141035405580043d00e4035403010300000c10002c00001ca5031155a4a100d03000d000341800603000001e985039540c07079446051408020300c04112542000801c041d03c890f141c002c44200101850504003030104525510002d003041980c0301e1404c01c8041000700080c0319403030081c03041c3c0d0b0142b08440702ca0000a03080128400803103100c1d926080c100809601c8041d05c00319441d00c1450b10503680082540309407020000380c0c020400038810f080502ca0000301c000348501c801c0502c0e031180209150388803180c006a910407160b24000800a00202c0c0403180160301404402e1803002d411241d02d600c4000c000b4009008640070b0b40d404070302000340002d050700b20600c0380088230030b0b0741c0e01d0102c510720b5004680341041c09022602e07c00001c08001940000804c00c1074081d0500b14028000d1956031201c03080c0949 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 559877230 1250 559875980 559876043
    0xc03090c0d150f0b0a090c08130b06010c0203030c0d092105101104030b0c1b0f0d05030a0902120601090c1d01030c1704031106070e090c070203010603 66
    0x10603001648141d20300003030710101c102e034000c030009482c01c41d00c0340701805015000302d801941c90701e032401031190b030740c41c0e41400c1d01914030114001541000b500c40101100006000c0b194501c0501d203d44002c0b405d4a01355603401202800e1141e0481003030700c0424074620840601400a010b4070001285040d844500081218801e50480c2c1021412805096403101580b100a00550004a0300c803402c0300e15410044042c8240721040382420340d00e80b1450691002142c5900c034403000015084208034100c4003031103a0820407801040e14a0031000d00c40c0d5601c2c07641101009100b80440090350040311500035004540d0301802c03104c21403c80c1e081d8140c0d181e9080c002c0112080c01d08050000241c0f0450058a50307a540c0b1910030360180c3c5400c0158000d088408881d002c0011214585030b0303a010200909014921a6694000301a00c0d008214100103000d071905082110200f0b0903080350362607910140d0841c2d42403140c25520009440042d00601882d80700034101e446d00c5c20b039031740c01c0002d10300d04210380b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 559878480 1250 559877230 559877233
    0x15090308180601170309060f1201060f020a0b1b0d0f1d0d180312020a0201120b03072d1706070318080a1427041a12010b090c0309 57
    0x340c48404080500c20340c000d98105490b40007000400007820003074841d0700d0480d660303c19245403a440b0404285a94040d107240d81c0e042c2c2000448100c2a0350481800b40100800d10b095404420401c10080d00d527414044042d010b0012500420701444140c0d514240f018142d103111503407042c00c0d4900710050a006c3c1c5840146600c0d08849483c041d040c0c02280181811600c0500910f000600d03050354690f807c005a41d040754410040400081c158001d1004c01d222660003d040360a07080c800100070303000401c03a404800d420321180721034030f80380050740d881600e16010b07103400f6440ca80c1031740010400741080a4449880d9080c0000350043e0f5074010030b1064014a403d5aa890b982c41400340c0c00e07103403c080c0280e0404d00326180070010480c4100508080c10f06440d1600a2008086a0488a030032010b8110400408000040080450503c1c15210900280c46c1400b03a2203050075411080548c0181c0d4a000e404040031510140100790702409204a004044007418144042030781c803e80c0040307416000a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 559879730 1250 559878480 559878497
    0xc180509010305070b071e031d120d0302070819030b0108090c030a0f03030905120310140f0409020604030b0c09130905061f08060117160605190c150903 67
    0x242403510005050726042801090711605d4030440305a035521801e4140c454030b1000441900b0300030550902c08400c1d01a50310340c29000c04a9044038071400ca00b08001e845201143d0b0003032181c00c40802c0c440c42410007810b005032030302801d04000d1007070f10818030b100650b00070b130030640034074030f90103030301814201d0f40030f80c0e4521080d5280f843c0d0a84c0c40d20b401491070f0341680030019040014039450040c0f07000c14420700d400300304a03107240c0d00e851a2401445101001203004001c02c00404d07100310a40f0300900c071802d04000c140b1000c0b4080740c04100c02482043c02103072039990800641d1980070444000b0751f8000b41200300347c80c03d072001d0803140d000440424404c94503507003114242203c0b4040c9400e8282c000c0090641501c0d59031000040540280684201c1e8101400c0050b6000e801d2100500800c0b50700d0741c00306500b020b07400107410100b4003006910345000c072001c00e00405601405a03064010042042c08803410f0b089010303150720300d00e540700034405c08001050f00c0389821107401c10401070740709440d500c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 559880980 1250 559879730 559879739
    0x7060e060c040b04180609020d06030b0c04060e131104080313090209091302031207051018030c0b0c130b0d05070516020603040206090612090d0c0c030311010e010c18 73
    0x1854407581c8642c3c064040c0c01c0c001800269862408440019804400003ca81303507a03501c00010390b00240b1525407515640c0c1c800b00309018031070340d549511403140d045c1c85142c00d06140c0098040486410094002c84603018858490525540480503a1003103002042d212a0b482c81718598170780c0040c0c03940000180380100025041c070a8026101f008400034a10060755495925403c5000e4a003c1d082c0e9141c4213140d4078440c03c0000b9801400c1d007a0140c000f40c16400001c1d18030000b034601c8051540e45d081c8403d240741c00440e512418141c05683e110f0000040360302c0d030071400c000d03d01402c40003e28a155a040010b1303003080e074000030700744005c604100744041c0d42da41409403001e02680a070071740d580900c6043c0c0390043c6880402180d02c640300925842c18190f01c0b9011034210781041c0040d0011001c04810b2081c000c80400c40c41030840c40c02e10309152a410103170303501484211644001000c1c44040360106400b00380070342215440c07400c000001c0000450700c06000b00064204014040c07a64107a044c00b09 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 559882230 1250 559880980 559881001
    0x1509051b0103021c090501090c141c0503040b0a1710150306050a2105010c170f04021c05190606090609060b120702030f0301030501060302120c0d140307050307060e06 73
    0x10b07040f181342c1151490b10358058101d0300140202050032180355580d400d0010006000e210203001414480c1e881302c1d86103559206100066840085442d01200c1c441c106038005a0004200c0d03054604001803540c4862844c1410382d0000103603019504d200e045030041100c00700f8414a61002c442d410f0ba00c02c0d90500042d90198202c0d0041d000c1d25402c10095402400b0380d8039100034105528140c105821a18543d030788500d4211400040c00600147c0020658520700040d02e82140c1c2002c2130600e200001c1c20030b540010340b004e543d40101300e2940c008041078410700209000e040141840c942d456141034000b860320b60010451402402c94240c584000401c1c00001071141d00280d6400078440391030005003500e214000c060041c400003c5110410081c101041c0c90380143d030083d480b074000841d045003140304221402641c0540060580d215500c082407941d40c40c52a542200c0e00161704401f9003405880d26403c1d4403d101024080d440005045001c10550754040d007418a0310b0350640b0215240d409100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 559883480 1250 559882230 559882237
    0x40b0a121116170f0c03040302030f1b0405150306070309020301050114030c0909010204121b060e1c0204060510080604060602060601050315040f0c080712051b071509051b010302 78
    0x84011140c0b0301c4030000010248808100a032403188112410034001ca4118029a0f029400b012540d40010504000718241082804803103011440a0a44520f210707101c0030b904160403204510a94980c00882c06811a03041052a4000060161451490312000c003501410401100301d01030741c80d14000045210701c40d8120705540038014050b100110090081001c0b841703021304102c12075582000001120000d5040641300144154140e82d9480d08000f4012040d909a911080501007a030407009010350300c8100c1d0b40c240c0141010408500c44040c008200102501e400064120301c0b001142d522407500920300e60301ca180f040390180720b25178070b51004a840300400d0710200d001c03480a2010903240c83e0900d214550030700780500001030b00043c104500c01980c4119041c4401b0403031304001c2c0007615600c51075800c2d4010030184107000500300507910811040c4045106002e05001040c030508010380b09004001501412005105142c0141400d5449009901400402c1c01c9000407407a1213500034001da = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 559884730 1250 559883480 559883497
    0x828020901151e170c160b0403140306060405011d03100b030106050f01021e011b050304031107030c05060c0c0621070305090d0804030e1305090d02030f031308040b0a1211 75
    0x40d185130801030710a81086010143c015a000c030418010100c0140340e031841b02e4480342c0036001207056400c0c2410094200c0034a8040110440390810400602d500c8810454040b14020710f444104407815442c0412184006103006906010f614181c05401c140c940114bc0c803000c01702c00802c41e80741d0307400400111207240501d01740540c010013500d08240e22070561902100348140700100f10fa400003100c01c08085c1d1340a0800012800c0071090100303055101e121110318084100051003000d0840c1c64400036503481c0d1140600c1a81d0008400040e02414071031034549880240c4016103880ca0b030a01d10041100d064a00301128040c480020b89107403190180178012410003000d00f628699440040340c02c508010020390a100e40440b101907031382c540e4020b40e81da00e2004000064103080c60350300c1d54245a0503058141c04c41d0310a024207040d4119802c1180d411144c84001d0ba50602c1c414604402d940c0615030105804280114085100580240031400d984580c0c06003040103c94a0507441914000c5190 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 559885980 1250 559884730 559884737
    0xb010c0b0708090a0c0b1804050f360a02040c0903031407170a020d090f03050303160c050f0f010518100b1219050f070828020901151e 59
    0x852040e070b00982c0180e4010324040181c90480c5001d03110210044110780c003841c0b10b640000744c84108010700d1401d10516000032a402e104074103118520090b418005400c01c2e503000300741d00181c2c24108520a4030625102d1b5001c613400c1d83e440f10311046440e04c0d414541030b8000c2d402c010741000018425600703241a43c1e45900c51081503071070002103c081c0d0b042510222980c0080c1c114900b030184561014000c1e408960340140144008010001c10056096000e204145095481840058004402e40c1e42c40552160b070201e0710107e0034011070f40580f448170050301502540030300300d20010b4040b41c8882c10b40301c1c81c4000c0c00141c984a12907990061104100300d915041580c00350704240246d0840c2203007810042818110b02c98603012130342170080c0b1200b014040400b41c001a8100101484404405801d201c040c0480c40e02e042c5220341c80d010303480365092921101c41e0108041c05070f01c1c19000740c01a0080d02030402580c650001000300c003403051048000c20310510103c00c80d0b80d042c502c2d858a0320300558 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 559887230 1250 559885980 559886003
    0x70b1e0c0706060b07060518032715030f040b06010c03140a1206090f0b09041e051c0302030106081f050d170304050c0909030703020718090606080706030b010c 70
    0x1803000200c0d81203880c0c202d41c0b403034407103d0000b52030712800b029243c03070381c0a80b00020709420119a07100401940c0d62922807070340c10500079001051002c0015912444000640d9520360040c480010f810342c3c02061141c03003a040c0881403104150040001e5885540b003170074041c0041e201c0d4001501d10803241300c40103002560482c3c0c503082203280c1e4405044013100d203081000008030003403404010342c1c040fa00840c040541c0e032514041c0b001414066800c07400e41c1604e0041e4942400d86810405000c07000a00c03400780f404046c0001004010000b41002001c008200350001c84129402400f07075201b0b108000000d002240422020840102d40c181200d03010142c1c3c1002c50316140a204e0056980b00040e2111410441c154902d902100d0045102e244100090001ca1030030004108040300c000d0400030b801c0d401844142e0010380c0000350340d000d49100350912101200500b48500140c00b101c035000b40041e0501000003410301002408006a41d07032600d09001e0f0841c0d14004507408070161901400c00703030038503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 559888480 1250 559887230 559887241
    0xd030b060403121707110118170912030a0c060506010e181008030408030a02070f080a020103180218060a1a1207021606020c0f101d06091203070b1e 65
    0x1ca040c1e500100c0300f0704000c1c6500031513803800c3e08080400c54500d800314244480c1c1111142c03003072280d8003205090100000075140c49884402c40080052460014204009000c60ba981c1c0c0b01d58601c0030503000e034070449a80e8612150000c000849585003128100e040c000812065801198440c01141028000d09014030308254238001200019000300d00c014103150000c108148207200410141824100950391029000d0000f8030388420707940706000c0400b401009201c22000030070031308045502481c003ca0001d440d50354501d00c0311040000250b00c80800b8010600c44142d0140d06c0d841200d00310307200c180483d0742c2d00840076a4016416a0f1040401c1041482c84840120003ea0740014562041310f2032482c40c1207280400c1c14181e080340000d6800300305240d6140c41d10108118100350180c84080040e034040030081e050102e801c160391520b01e00030464001c50b40b182001e540214600501000590604145d015140e51000304250341c0c07206034400003000900c8040c11140301d6540c82c0e01e01c0d81569111f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 559889730 1250 559888480 559888493
    0x605180c09181002131a1b1204180f1a0d0f0501060320011805061b0610090e0613150f020d050a18080a03020c0a0503030106050a020d030b060403 64
    0x1003190581c142061094034002c40c0801030318030103940d9078200580c0c034450740b644003035908410383c04600341d0181010216510240c0e4801d403101080c0c0140c041420012003032290b810034400550181182101003000179034410509403112044040d014104203e042041e4894241e8210210302d20046000d8031080030a81444c0c011554120300030200030100b00000d9499509550569200380d07002908540b80c01e076600d051812a10401209090140104c080318400600c0d0403003611480e8820900410f20804a0400003003248c102002d0034140e41c06881c01e514407001a070340c035000304022035141502d0030585600000301c1900540e0301034072104001000350344640320149018040d80300151583c2d042d0032510100d002500c0400e004810101d030500d40250342c031003158001e00010600c040917241ca400071074000c4040310450040b92401513610200680f00728030700142544010410300c000400000c8050b4008080d101501d071030350a840580030131070411015200b0480140b2ba0102c410032040000075071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 559890980 1250 559889730 559889749
    0xc0702010e040f0b03060907060f27080f1209090a1d06070e011101050712180206040803070b01270b180403020715020d0903120207080a030c0605180c 66
    0x41454007a25030450302020405442d04140a0800e26440f032020040f14030f002c0c003115034030600c108000c21115140101c02012864402444401c4c01114030000007000140d84600d035051364102c510385d809640da41039260703030340344420a0030740c940c0508090384014003108411500c852000500309201d81e1241c00b1890001c3c0303110040e0060180c900d01100710b82c018180032691240f40b490720b5280c40c0000303072000505036240306251802d0701d0745000d04028202c1d800c20316501005020075000600b50701008201e0001d062002d40c0650300c0400400c000601c510000001c1c040148214281105640e0b14000d40490300440108407111607400071002942c60b072141d1018134101002040c5c80c40d1031441e50254441d40308165000e80040e0031400c002d21465003540850554500103200510320607000c0c4c01c0060450f0401e00004040c010700c3d03408010414070070030441c0c003d8110f44003a2841c81905240244c003101014108031043c504200c002440e91103034910030a0074407442400b6044d000e0340482007000302003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 559892086 1106 559890980 559890983
    0x40c080606030f180f0c03010605030109030f080703061206020a0e0102030301050d030503190203010b040f081606030b04140108010f0e010c05090d0606050301020a09210b0c07 77
    0x100c40c101240d90140d0b415003500d24a4544030b03000801c4c800110b041500d0740c802d49001100740200480c0340358520404400030090325544906050980d2840b00c400b074046200910b801403054012000d040d07000001e0300c0d00003100da13100c0d5075000341c0310043c400c16208540c0c04200e400545811a01441e40750601f40025401c41d0314110001d80c6020b04018010100540400824141c10070381c411b104404002440664503980c4030501101d50390403034412000300c110030300c400040c8144007081d000a00100d01e0903449400f800e2000a902030003069180c5904241c0c1c400400000c1c004100045005e041014004181c0e80101100b00c000c5e500c00d5944040e0300d034940a60000d02c1500701d0f00702c6032403400039100610401c040341444401085203511140d019400010798071859580301542100343c4003120051070441442001ca000c0c100c0244c64000c120695590104202c20800000307006910b = true := by decide +kernel

theorem cover : BRFrame.Cov 559712230 559892086 := by
  have h0 := BRFrame.cov_init 559712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 559712230 ≤ n) (h2 : n < 559892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
