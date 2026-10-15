-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4331
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:16:26.557975+00:00
-- url     : https://prove2.me/submissions/ec4118a4-e48c-4b06-b55d-20d3d57ab56d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 778776978 ≤ n < 778956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 778778228 1250 778776978 778776983
    0x6010f0e1917010b18090316080a03050106051614071a1c140109020904110a020a023d0203070c0905070f031518090b010e04020910051807112512 64
    0x9914080a0210003058405c90b4080c2e2110116030038043c0f42d21401020010740c80081c0c071500c0b400a02e0030300340c075454010709014050318204a460560342c44a001e010611a82000c0c1c03211404051a10743c480050000200901c44008030450080d141100d40d10264401501034031541039200d03142000085d1409542c142600d04840c61a00741c0c6070a18850281d8099000654800d03520a90f0204203014030026104e44805540244411310f130901c18403801014081c0c031000300b031120b09090710400d03d04440206001e41d04c0b11203482e030394002c600244d10314000c40070000c00c1600b040c2c0e004200c143d02584039506c911595662480802d200d070400346c1c11940c1c00780e41c08518030a104024481d1402c00030003400b616454682c00140501c2e44e449031024858280c10200304e00384100c05100652400d10034440e005010018000101d601d03140000d02c10741c0940d89448148450000051a0940a919032003845a0500166030f0743c210810010b201080c04908031903d04c1811070030200342520b049103002060383c0d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 778779478 1250 778778228 778778239
    0x30f030203270d0b130f06050106260c090102030f121017100c170a02040e0105030601080c010e0f031606021002130b0904090c0306060503120a02030306010f0e1917010b 74
    0x1404e844205a140c40140403245002201d0041c000040d1200c0c48540c0c418029100004d00d0750400328000e2184031000105000d05001c0c11116000b200c480d420306410450002d503555035280e0030f800507400d6024800d840c443c040d401090b05400102e1212410340301d2107031800500300c583d480b40200c03c00e11140c8a9504080e910591150790400d215501c1001c0a141906020f072055a102c420036201d180c04072462440c468010804010500240214034003401e0220007170100c540c10401140e6684054114150411240c190b00d0b0b081034444000445480c40050160380d4000c02402c441c40c6861103501c81d07000140300b280c0d9242030b0500b042c4292500c541551407007143d664500180c1080c29046075000300e500c04c0d90742c20f40c41c0003c0c00d1204461300861080340003150a03480c200400d400d00350801401c0148540c1001082201a404400c890b40840e09003805501d1038020181207940350500201c13503820600c115120180314002c1c05410044400e445002041e0014025103907003615460b0f55059040b4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 778780728 1250 778779478 778779499
    0x60c0507030c1b080106080f0c01020c010f2f0615040b010e0108092b0e0108070c0303090c09020301080a050f0d210e1b1311090d020a030f03020327 65
    0xe580e20149003c0c803810342d0318082015499101c41802c50b900c07a8070541540e0322230307460f09903150030078000038040c03a0b400d001405903000b082c1e002130a440070102c0c181040180c2d65075103281480c0a000c0784054041030ba01c0f00070040c411280071a0392000705548c0074609200d2080681c0c294600350040b1001d2440c10307520a2016030245d401550340400140c4a0b02150240d10b14202030b8940340000301151220741074041038180a11040940b840480e05c03009410481403c041200890708240d1441d03a6650524000641c0c1c2810b003006400203400f030300302203180340c0001300015141d140040ca181c0c880e4003440980314406069024150f41d2114a115000130031155140d00082e02200a07100404020901e804680c80910804203070902468580600c020b0b1400d4000c10a5401c000d41d803940929819071003004030841c2d070a03220b0342c14081c5c28041d602c2084854515421501c44140d00001590710164070070b081541458040e40b281c2040c2c054000c1140f4280d01600d07000440e4114407070000020304040c041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 778781978 1250 778780728 778780733
    0x3081b0409020c0a0209040605011503060605030114130c050a09080c10080601050c06010608040b090c030703170403050a0b0f250c02040b060a021c0906140702031612060c0507030c 79
    0xb0790060000705810380924805a00945c0f00e250055120384d1158200140940c1003121300c002d038428440d0a01c041500e0200d0502c031403a0000c0803030381910210301012a04200540000300c1c4818080c0420820038203010391021060341080107000228800d4980d404551f0701c40b07000f01d986100080b413042d44401d0088046800350b0144480e0340c0c0001040c9031180c9006011020249400402c1e48040002032401e000c1005200a07103484a801c0f05036800075046205a200c0020795501d0540000f6041082d500005d4002280800444005503845419502640454106528060011941c8401c8403a02d100044c1c101075100304082480050034002c2894408100c4040701e0441c031a000803a0007a943c2c8a81a2641c1d072805c0c040c00841c40d0550040040440c15903080314180c5c9903d079040d044c0243c61a00340112a006042c0780f50b02d9081840954a40d0301600029160200e00050f40540c0511104003043c017840700d1741400c000c5802810140711091040303504445500c14400050b00251099042800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 778783228 1250 778781978 778781981
    0xe130f1502090319030305061215090736020702030712020609180603150c0d0f0609060312020609060f0c0a020f030c071e031221060605030403081b0409 67
    0x3542190904014207208a42c4003203460b010190b071046111205412500081581c940603065021605807000691018008502c81d81c3da20b0b840b26a416240c4050001554030308c0806c6030000902c005100b8500c4071324442044540c02c56044103e85900c000030703c4840c1070740030300c1c007c60fa02c00d9070180007042d05600d410050286112101c0701242d102604010310220b903500c0b001141114013070810601000c1c1460320030985860b00400185840e280ca10342004100406070051f9030404404c040301040845450b00210010801500104c03111403403c4008020307c8000110741004507450340031a44030761035001119039038010071540d50a0034041000050111844a40540b01c0a1200c1c0119501c640c2c40400560441d0004040088951b010481c100101040c401690204040c10406801401d00b5170700c0352195503244881ca14140310b12000c4400603c002e0380706401c120384079414108503158031a01e00030003d510a072002d80008410ba00890b142c0a945044002108580c0b004285080c2c5024030800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 778784478 1250 778783228 778783253
    0xa0203040c05130f0504240902061905040305010c02031911060112141b13060b070602030601170a060e01170a02011110060b0c060106051206190513060e130f 69
    0xa40303c50301d038070300d640301e8144a010300c074021442032408102620b408041021201303240c100000c41d81d4180104c002c00340e1103401c1200d410110a0500c0e000d100c01942007501c03c5d10541c0d100900940ca041c00140510340e0201c003610b550001d0343d0b190100b40031003c4040b42d074864014a22007268200c1001080400700c8290301d5000c040c480d00d80720200a281240c00e600708070f80074000034030b501ba0301c800041c842d1424246600711159a12030410100342028101580c0e405540001002294000f010681982c00b59540c1140108101e041e6880c501d89000e440000c1c00d030600c1510804d40300e00d00045040340c04580804290340c160740040540c070200341c0044891a003001c07600c0c0b49901136507003558090400c901131200680968045950b5038802400c540d46025030503032007041000030501008002121021f0141c1d001201141c1e01c0f141c0f1000040035160201a507800690300c507600c08107944810205070804d000b1200c0002018015a0702d0440280d81c00344410f80060542c1084465400006d60106110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 778785728 1250 778784478 778784509
    0x319030f05091f110c010512062107090218010c0809130209150909070c080304150f0507030510050a05030d110c040e03040906095603060a0203040c05 66
    0x1010044512004000c5485420600c0340001c148142e013101840d02080001304000d820f1800300c1c40c185205d43d0b5004106405094544994450249000c500c0c0044030324181e8613095200341c0b00d216aa64500e0802503200d0358100410144010b24204298000c200c11521190044202850300042d03404105245010482404509a0a1000360890707110400781460032503001c900340390380c3c00400041002018008090703008201e004442680000c00382801d40c0d82056114110700c100310389221184d0080c1041d86041d40d01d482ca410704102c420b9506405c10b038000d03006041d007070748095200c4050000940d03940c020705416a00803c2001d10151054031020362594000040d629064000c85c0010191011540e04400c9980049000d00c0b41140c0361040c280100b01010080000305c851104586a103020041c268041c5034000180100b0210710a1600c0f0030201d0590144080322150016041c9007212040b00703e0003445034a0010344070002c03610032a0b00903504111031140c5146454100f045030701c002c5020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 778786978 1250 778785728 778785739
    0x10c030e0a080f0a050f01150b0a050d0f1a010e03120714070f082514030312042613120302031b0309010807020c090c0d0b031002090319030f0509 64
    0x19902d41c040c80103620328000c0398003030300c07241030ba03400c04528102c49411203100316450021200109a45402c0d241c0c120755404901341d480340c19030107040d500c500a418201001d1400e0410b1500c6040d86540b04969040c180321010001c00002d00c011542c011401d07180d40c0e01507101000e0311192501d0340c8044c1134080d11403600d052040c40540c2503075007040065403058a8110000609011805d014440252a00860189084406c2c0311440c0483d1101035485015503585c014004000340d52424801c51740c003c10284041c00090401e407801103c1c2c10604903248140303006000145211018000488140150000201558501700040314003c1507174000d044042d403208112203039200c03640d030b401e203801d40d40d00d00b0255031034100020002d882030743d00800010454022515800c3c250b80c61008041e001860214a1601c0f00540d1610b00024480f4411036641807181c103010b104842810f400514840001343c0035540c500c1e0020800003480a80000700a000c51107840d00320500d1403058001d4a58090300500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 778788228 1250 778786978 778786999
    0x31e130501060b130e090601050915030615010e0604050109140d0f0c060f0804240e010e0307021e09043305071701150c020a05040203010e010f090209010c030e 70
    0x862508468041c3c0c0082c0c031a840100d9184100940000c00c50020021000301d0a55072410340c10315038540c0014080e1a21862001d404200091000c005107904003401800702c2d442410004400044040f07000c204a00140070b41c3c45484050500c4e4013074134116003040c1c50f1410400c5c2403041850503c0342c100740c11074014003800e04080104802d21002a05240125100c280b52402e0203c02403400003034171207500901c0034640601000504040010300c68084580111110f0030141001d00c01400c60281daa440c9503080c010910b031132000100060010030310890700000b41e08210140c4c0c40d03102040040160740801c10380c0c005008030300d2000c81d10003905031501c80d140c000d50982562420303c48844100048043c0d40c3c20401c45c405810000d00c1c00300d10b0f4451000400ea40c0b51140b0402c140103010000c204204d1420165230454032500031100c0540002070056499686944007651708110174442c51080c091140c0c0d0003d440c005c1032003100c0c1c1a42060751070305104081c07901c059031461510b0703e050b6003040701c005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 778789478 1250 778788228 778788233
    0x1803110d020f19060933050402090705130b04060f092102060c070e0c030601022e0b03030403020907050c070b0c0604170c070b090f03070f171f0902040f02031e13 71
    0x189200600c10f621400b46c24240849800c4122803c00c000c1002259480c040902c00560703141d030300c820b81c00303040762900c1d59076041c6491a540d128421680710b0301c200c000c040341c0440d1203078101390320341c01c041101c2e9075005100b951003080c4d540c051810242020310802c0c0c10005009820400002c0180700382e540111031000ba0381324440410900c08603200f010b115008001d1003100c1d82d06101f941c1004030340b000d019030341c1d0071840801c00703c240000c0100030b54290342e060070b000c094905000f5140215001440800c2c6032806000191659004108250403070044581c0411984802015100e41d680b50318000c11103039480703035590029a511900039081c000c05c03d10400c001184200142800b402408016a4580d82c2e64800d00c03620b5601c1e207c07402c0c80390300004400e110f91840c800500080740e0041680a19248100490600740302c1c09120100780065403008c401d1400305150807580109200340c0302040510b100c1039103481240811340b02106c15003d440518183c20b00070521140d0070141c03880808810000d242d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 778790728 1250 778789478 778789493
    0x1b0c0f0d0819210903120b01091e0302030105010b030c0d020f070f060b040f020f0f090d02032e020a051801031b080f060427061803110d020f190609 65
    0x1d00000107018000208540440c1440c0e0b0080d03c50041002d001010003540c01034a60500c0803002018a80d407072003a42c0040c0c3c030031b01c0f1400040c4505501c90444030000d485c85141da14903030000303a000350308100000407000c140c401103c0c0300f030f4203412650341050300000d400f00180d8030500000641000c1841802e0208040d80440c0b210f051160380006603000c030300c0c42404169105103100c0c100c1c0c2c43c07060080c098040820021a06120b2880b500c440c0e03108101c00c0000c0d82072007078040180d0103124020100300700c4003c52181112030003104900f540c210003480446800d9102d4441c1207400540f045c82082c401b9960400b41604a140504010600d041c40f014035464000000361b1711070000d0484130610003000042c1900c6504044259130900c80440c2c0d40722001c0070300181000500030b803600f0305204404c2c860389501100341441d0542448011401d1428001c001e0140f002c0d810443d40078000300d0861203400001e001c00815143d502900c031704401030003640a00e02c1c10f14000e48407141c58240c40c10020300203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 778791978 1250 778790728 778790767
    0x3030a0f0b06040605070c0b040f18060b0705060a050f040f020d0309151706190308070f06090303020408010c08160507030201090512131d0a0e0a05010e01021b0c0f0d08 74
    0x140c1d1780c2c41d1070311564144000441c00a07809000410000c101c10f024620f65a1151800d41d00c50b03c035440d80c4051860ba00a00a1070250f10401c002c2c0c0c0e000c25040300b0000041040750180e00041c4003032080340c41d440002c1c5030080041c2c07070050901228600d46001400c206200040d1540a0f041510910f80e94601415040c14200010f80004402c44890812002e00050300d6410000030b40e20311408280864002c00c3c41c0816001c0139100314000304401c0c0401c81c0d0b0701482803199501c40c0c024060b0302d2603450042c0c0a034026006c0c0043c65401d00c140681000d11510010f449640a52a1401070040d42c810954040d448803034160219520384c5410004507504102410340785000d003111076545c06207451081b0520a00c0e40110f00c2ea00034000d0000d1503103d4804196400c80a0044009022030b11850101c1ca04424507100034402e5080c031001c400000380c10340c050000504903807800b900640e00e00c414244c0398140d944181e58440d004800101050402c42c0c3c540c0620f500c56400f9914110807160141e040c2c505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 778793228 1250 778791978 778791989
    0x5010e120102090312040501030c0c050d03051305191109160e01020c060c0c0102070e010e0610090e0a05190b1e1810051017042423070801050303030a0f0b0604 70
    0x1c0011b030400c2556850310880c0c0114440d4901189141c52682e60903440e00400002d040030592504007049410000c07403c1590b41aa004084074141c0c88c02000d200c211000003042031303601000070754001b000c1c1c0c00d11603000d520485200c04250382c0814101002e40d484003941c00c513681144030380e4840d2196519800700030544018170b14000c0184105c0700e00028540302981e00314801c82100e81c0300412200c940101700c0d40c2c10100841e00501e400b00e150004541c0740015a100c40c4544030b5103428424444d5031948402c1c0504246059101d0840480c2c505c003040e03031400248190404c01149042400302e03248801400170520043c80f8000c2d88031410b00d44400a441582c0d419460240640100114501080042d40b10a11405d21ba0708080e1255003c070034a08006001900c2060740030a0760311036255840c08841d4241c0c080c10104000546003004034040050150740c4e000e40041c0902003001c0da401b07044440e0403180c0040065103144c0d02c101100010b420340d0201909910f890341400d000702e50311400504080d04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 778794478 1250 778793228 778793263
    0x90f090506040c0e010c030f0509090a050907170c210607050a0f02070e130c030b070309153e0703030b0423010501140c0106060302041d0105010e1201020903 69
    0x1008810041110201103c01080c0100b268001d007042c1d03085249585400d4250802c5584000c41050660313291007020700b0140e006098104202e060308540d0300c014000c1038141e0484150548407405000103035032900a0030403c0c4d109902141c030740d00c0c000742c65500b200b40c00c040c040c040c0382031182d010740382c1a826181c400100d00c0c04214159103a6020255542180d0b0a00c010440e962070419511903104015043d0352554000c4100b88041c0428441c001c1c0007107070300000c050403030310b40f00c2002401001040402c8641d40c1c0803000702d0104540d24080c81940c1b4852104c000c0558504045681940030320f5031900d081c5078030070f1185001045105001d4050315010303031400300d5004005401c01c4111040e4101c221080d203903070300c1d081d10081e4100c5102c5044d18021f00b000e00b0708101c1d1400ca070406015805106c0780c81c4d821300c0320106445038150080c00885160104031410300724090302020b05000240034460002e07a2101c0007606500d00700c0e005011480d001400180380000c113502080c2442803040b100005c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 778795728 1250 778794478 778794481
    0x60801240b1e070b0f10120f1b0f051003020c060606301902070c0b0901020a02040908220e15010e030d030515040209060d0e011b02060103030806060c1903090f0905 72
    0x50207602c01745034811041c101d8000172a06085120131034250358603001c0d010681c1e5040300c00801a105040080207003602a0b003207a8691740707070450280050319002d040d010b80384202c1d078084050f00074025110a003e44201508455030341200340440c0d5008201c003281c141400144c0d100c5aa0244045400c0c0d203180c10796000c0c50742c0741c00c040c81003c100e1540ca0006000f0310401c0050045003a0303003da41c00b61030700d2840d01c7d40c1d2901e40400403450150b034004040d60041ca4107449a040200103002801c2c1044010342440f0f0540b56886000702400d081d01c12040401e0102c3e0010381c03085982001040101014101280f02401d5100800d20b801107007411400429591000d008050001c001a402425400c032004e600e410414000b04049004480030f00d402e0b07a461700c203403000800081d0080701d4501807074459518074019040c0300075540c0d1002e01c02071b03000c1000c1c00045002414050200d84120304281c00810509504000c440c0359841040030950802840000124050160101e05c40040ca841e0700081403a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 778796978 1250 778795728 778795741
    0x1c0b030601060c021e041d03070b0f0103200607140303101a040902090303040329090105070e010f1116080c090114130b04020d060801240b1e070b 64
    0x800c44180c001106100d4290508001a500d8200d48282980b060420000300d580c02d00201e8040d000e00340714240140c400c0c920f508440744000028110b9140141c0e091000b41d12000e5006070451428003000d003555040600b24140060282e107074038070008000e0641c0385444043c2c1c40340502c40184c1c3c400400c06030030000074800030883d1404040c0242c80d8a1030b0040c143c6e10510303120426071284e40302d03000085d50089440001075805009403401550044803855220703020a00042d9000c1c01d46004120f00041c20010540d046414450381c2d10502d0300ea11003810002056006444255001e13903004100b110141c50341d803d044060101050300003400d9082498103091851030760401d402601042d000f800c0e15001001512703404002003201d08429909080000d41161040c0060150300301465002800000c2440d00d41405521000440384020000c0003440b408800360b0301a050500542d250020000c00c050207440c030031100508039041d00448002442114001c0c0c12000d811080040c0e8440da00700080006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 778798228 1250 778796978 778796983
    0x6011b050102120405100623010314090303040b01080d08060607110a15120e0307111521150915041404081918030602030703090b1303020d030e0715051c0b03 69
    0x6c1c0041400c0c00f8400340307041c1b0041e01550304804a10105442d4001140c8a06900950000300c804009000c01001468180400759480d8803e03142100d022058800006001e41c000c07491103400051543c840c0340540740c0c0800c000507134015110a03102e9183c09822a882030792240d80c520010500d44a64400b081f11042010344000d028441c4100101d0920424001c0300401000701d41456a00007034813003502c05030b14041220741d814501e08000301c02c80000d40208440303072141141c4201c80c0242080b036035030381c40e501000741c1c40100d10b088a0f0008015800719501c41c0120b031210070f0500002e48001428034181c1ca040034002400d86095800f03800000e5602542542d8551032860314140741455030703580701001142c552410041c4806850a64048003041400d440b1b50440700c078030794025041e05440e06140c1d105c40c1043c050183c080b40540305004026103058003e0045074601d90342c00e0003401510740f40c80d5450b8407940f1a14903e500b000380400201d01010300c007a000c3c0b0680c00c01c4142c00940c0c03582c0d0005061 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 778799478 1250 778798228 778798243
    0x601090b061206060d090c0605030603071212030e1906091208040302100e100504061515051605070b071203110f0304060b1f03020c070e010b0306011b050102120405 72
    0x6000301c0d8100003a80502030108a09904010143c0764243d54448440700074005080c003032001001c85c07003000c0300064607560110146000f56000c1b41920541c40d92849200038034001078000924240401e0390f80c605403070103503006d524200d80e4a0b061f00e10701c912443d00810700c040140021128103a40300c10280610074200c001480703030407040c1050704090030103480103560341001c40701126001d622400c0c10400d2090503c45111030101c115000d00040c100752a0131009401c44196002d20b0815503400010005800801c0012494440e01c0e0705140c01d5100f941c81c601d413614104280e13038a1041060010b005c0308100b008040740c030301034240ca0100c03a809004c000c2c25a28484038401c55610b0501c00c448034040080304694015030322500000f082228400401c148120b06a5540502510148007804282d015002098051852004e541d00c860f150441c86007480c10a02802d00c06040a000040b120750081c980b5600701e000c00c540895a000c0c1c10341d189400d903413000b4a0040091450004c7c04100602040b440703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 778800728 1250 778799478 778799501
    0x90f020a0c0b07020a0204050c03090d020106151206051008040b10060210050405012003010f0b070f080702151c0c030c080a1d0a05280b28020c060109 66
    0x552514a00e03000051074150000805031294841c140402c180d107000b00480c030740c8540e02510a004929000082442c0da8200311489030440c010f410120625903c184103800c15690201090003405410038406c96a00911413800c0d4422540c400002c5204da4070b55200c904024210391326074401d0320b42803070b00f00b0b4054809040010840c446603000d0102175004500c030003c5002410300001c1507511401e0060240443c2100400440f07030403901c841c015440d4100444c182d400501000d080e2a0b6a0719a0011a2045240240103c420044800c000074a9400281a0341d40000c00940101c0005210f404e00c5034042500c2e480303150680c0c0d0700c00007041000d0003400c00c01c3c04181405c101644454074054402791000742501e0035503554201100240c444c5070b49d4482004020401c0f286206020b00d0718903a192a8210b51007000e50000e003154851400d40e2801081d0a40c0c0b00d80c0070501030b158001b07000c28403000c1c1a1008000c3c2c00c86070460082407000d2000e40f40000c042c0e4000d100551411510800b100d00328440c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 778801978 1250 778800728 778800731
    0xd0501090506040c0f0503011811030f06031e0a080d060513061e050d060b01030e030a050315030705030d03110412080a030b04050c0f0c0312010609030b01050a1a0d14010807090f 78
    0x48651700c0d41001c2540e0440e01642007800003800403112003030040c030040e080000242c20110900680d035440d116445e1081105400703e4584455010074442a40300e880242c105a0380004480700020703844e58003504041000500200d1042e4691000945d000c03c640549001655203032001c000c1c8010498240c0c0c1588148038081551506010214030380000c00c800241520380c49038a03d807000d91180c1c2c0400400c1c0e0070300341565251240c4030002030255005450424002c00c4000d904030130b500c0c01003003003021a01c0050090002e12103c3c4020340240c0740b20001900d44400a020003d6045c03071401440c00714521410110f0f60711091000701804865400c003815006a00e810204112100d41c0300896000e414040320303050721a81c460181c4c86c5148149450010070300c0350100001241c58101c6014410781e40f2803000c0c2e503402c0c3c0c2c9600c1486003200803480303142200d86403911101501d148402c01083c42412401010604c2c1c208003403020007522080e030040c681640841c10402284000d480750702440c1004020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 778803228 1250 778801978 778801997
    0x10c051201090e1c030212010f0b03180a17030f090a0c230d0615150206011202210c13060b030606031909120e040c140a050d0501090506040c 62
    0x2403112800050164410032039842d503800504807800c03c61078005607045440505205000d50004020750491115a200c05c480d0000200391103505c08503c60640310000310241c01d550702c0080c400c5182c203a04c6038113255801500c40e583e01042d41c01074038104e840212a03d00f996403d213485107080061000308000902d400011808001030603901c2841c04480e80c2e0301c00c040809041a50703000c6494a98006c5590000c7c56100344001c00006800000c40d80004480d1040e04640c1d511600c0050040c800d10b2400507013090300140404440b492035964001c0c00500440300208800e4290991761407091305d03070b403c1980070044007420391904040400c0c04100b03107030080c0100c628004c03880c1d00da804041d081e903108450200c001107620b0001c803466149d2062900046c000c2c0c880074200020481200b04180c1c0000d02c0080034003055060a008086418071aa540c94245290400701040c841d00022005001c201d41040100c4d14030b10540185800f0b0201c98400080c42c0c100001003108a54002c140c00080c088404e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 778804478 1250 778803228 778803247
    0x602010b1e01090e0a0209090405010902010311070f1214031306060b040f0b030a1b030f1109030a03030504111806180705040e0402010c0c03110f06160f0203100c020f010c05 76
    0x3042008031368015101080a8440c40e82400c0a40620b80082e80c21200c207004100c28440305403c9030a42a00030f807000c20a0810a01005015120380c542c054042c09207440c2210019901025800185140f80b8080e002e04060071110b41440d8001d807980c003202a88d102e02d6105116051107020000d02d00a42007901d424900685040d60a00c0743c0304495010340040001040c4961541280000311061003400400d07410004000c1e00034081c0151600003a840c20710074030035155102048586442004004044c0c591066404902501c2d0051040ba040b90140440310034030b8136200c0290350a0840041d4283d880d1600303000380000305000d41010900c07a00207000744035030349410108490642701c11507000d01c03481d0385500060b110401000303001069000e48660000c180a01900902000c00b811650004450381c898100401405144003d417290503400221500091844880c0000c1d148081c0503200d010360720071410004c0b180e40c1a407401c0580c01000900010f03070828400c0e01032201d0942000c90078000b80d43e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 778805728 1250 778804478 778804487
    0xf0901050615090f0d03020708070f051f020a0204060f03021c02101103160606211104020a0e030607080414010e0a0b190509010b0a06030911090402190602010b1e01 72
    0x142c030780080c02c81d40082c02e07103140e413140184c1d5180301c8000b03400d80811001d0380c50025078620b0103201d04c4429015000012401c504000145003c550000b032454200000000983d0b205080c8492280700303610420795454010f84590040000502e5003005002c1068598014043c1c070611941081ca52600b21211040c0140d0701d500300f82c2c040e0034262402907001c1e2ba4014030249907210b484c40400c45440300c021311100700301c10ba40002d002c0c1c1300324060300001c13502d036101520007841018000420404400b8680f43c0141429805440285140c4ca000d01c040721070b010200342042e40544140000420301e81c01c00080c408407130a001c200c002ca9400800806a0000300e85458044410f00181030b02c19000108002d6800c50b415400c403020f806404003c6810081d034468000e00f10400d02d00d000b030509000c00603540b8081d00c2035051854000d02c5000452200e00d0410048141c001d1040b40e2101d8142d00c0d01004180500112000d40850b0f000043c02503107810400499210340c00395550010034406c0000c4060360320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 778806978 1250 778805728 778805749
    0x23010306180908040e0c07170a0818010605040614010305071407030e01050c0303100303090609080c040506010306030c120c0b040501050a0e03030c0d021606020312070e0301180b0f09010506 83
    0x16080c00982140b140c50b08041910480c0e00600b0039501c4182441040298030740100032251261504000b200c00299450607280106501e00c80400d80351780010320101e080442c0180407002d0355000040341c03501d0b07500181c00c03915290000411000420021030b5903581500c201c82d002011070520000c000300ac0700c1c0d001071a1260300fa0003001c01203c07613480301040c1d0281d81a03030702078034400b070030342c4d4480c9441d02400034210001e11003900041c400030000034582d80200c81003420340349038402030005584d03e00144806450060883c034100755032500c1c0080802c14180502014090250070614040601d040c035021044298010411a0000b08010401030ba0010100e58008a082c2070145118420300d00003421805003e82400325030041c040c04d04151b136808107114200380100300c10b0451040e11410101d85d28069021503054085041001c5072a244c06212401c5036001c009001140001c150703000d410415400c80012280c28015505101d4041c019885544d4040100d0000b0081c038540000060811600d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 778808228 1250 778806978 778807019
    0xf010912050c19050a02120a0636020604031a010f051f1d03060a0c0201050f100303050c010e1e0c01020a02130915140603060f06010903061d010623010306 68
    0x343d525480007084414000480c4040e001090a41280c065840c656101c081c0e0140c11140240341412100c40d42e0054a043c5900c400d040d640c9040001600501801c0c60f13440c41c40580c0d20090900000002800c01507802025402d136044100c41549000000d801000890300301a02c108007440084480c4050048020440d442d0380c40c00801c8102000110030150128506244d0140903c2c020021042c2c3e6980200700007148a0340204000d035144029090031200548092140825984040001c80d22540c05440403180c0031000090b03000000c10343d01d28060043d003050003102d44800d0b9805c1c81b000d040c084004040406c1c0003500380f50f2035a83c0040c80e031045142c0c1070b0b110240c3c0c94000c1014041181040c01000d44070000800070f001010001070b00740c0400301c2d400e03442485500c00203166000d609181ca4080c04068403000446401c40e901c810240c040f921031615503282c4010041041002401584001c20000c2c0b0a45d101202d440f021003984c1418041d030038107050600c00104070440412078441c01008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 778809478 1250 778808228 778808263
    0x2030c0a120309050106080d120618020f130f030320060a0203070203210a180803040602030408160c060306080d0c0f0309050306010e10050409020127080f010912050c 73
    0x1c8078a05030010200040007030f00561810790b02103000c180000c0d081101c09241d885412002e0300e100480c400342d03481030050f50341460551051364140b02c5143c0103010b01c1c5182c1c4c0b08581c100440345065160011036a030008001d06441c14082040c15041141445c901e0501d17044000c0460a0320762407590f13508080c1501a840e0360010001ea14940b09000740e41030310086a90043c501030b620310400100300c20a9801040107450446444044207940c11458491580705034241e06590325a200c0c4002500020015280c400b0104002c100011000c003541d0306040c85031112600075810034100800705c03511500007190701d901c0100c000310000d400150700000550b0040c1001c4101ca11840c0032640b022150b882507030540b040100200b012990320700128480d111a03c24011407603694801c100968a8181002e8003203034158940300301904c1c40e2500e02012004007407241403110f50f2141e00302d160419159081c0500d0f50b41d42d04034410070242540d1821903803218030344241000701d0041c6164640c402070941071000e6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 778810728 1250 778809478 778809503
    0x106090b040b0f2116050a08031e0304080d0914010c0203040f2c0c0403031d0108073c0801050d11061809010b220311040f0b0301092102030c0a 63
    0x80d6070854100c2c1c0c407103210700381c4070000201d500c0d03d100d00840f4013806c0d01c1100300403808154040b001095818004d8a5203100c0320315400c04a00404a60020348281c0311201c0c00c01001c44010341c2c7d4010384003a00d00c995410240c81c03107001c9000c0c0c00c503180b200d000800c5400401c01001840708403542e40c019903000030302000c081d882d5041c104400f09404c0b5560158a14010100241c0002100240003140d02945505540201c900c02c2c90f00c11169804656011403507520100c0d050611070414002440100e41454003510034508100c00e00c141f1342103550151580140c280d41030b09601000c42801003006640403d0107550951b60340340e80d82c00301d5031814080c91001c01d901d8401d203010074110500c014081d00f4072140d5611034445d2086680210351f0030b4003610300c00c01071258100441464008070794100e00d410348003207140310400c4043d24040800010040d101d0740b00007110b507020310898090070302c100e0340d2403041008900c4800f05074075500d40303803015500140050036100c00007291000a50364003207102801c0707 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 778811978 1250 778810728 778810759
    0xc01090b0d0c0c061404053a0c0b101802040f06080619031b061704021c052401060f0c02191e030303050c07031202030702031b0106090b040b0f 63
    0x360f008129000d001342d030030004965081c4001981c45c0380960f01940c1541c6103c031b800200c0004840303040280580260035001c90091200012800e0841c5030424501001c1c41c003481d80301c00c0064072041e640c5210052004078104070003002811070300c0d911228918191b080601e003104810031201c4a102e140c003804401000036089980c0c403c8a00d00d41c450100d002c5a0080e1a4104043c124105002c905600204040041502802202c40c0100c0c00702d208880d03540c0741c2d1242d003404005400348001d040303002c09a000303610001d481070003281407115100000e0301024003504800c650402040e44004203100190300e480c9980c4d54801803801c41907030141e80c0e001a032000510b440b03a43c1d4145501080d10075070400000f070b041d440c002c128101124004e1750140800d4842c0d207a000c01500c1002e50003000b040750083c060981c0c2e00540c01a40c0e001e9080c0c0103a0b81000b00d802c40d0b04031400f144d2945034020342d640305401d02400110307210312845480195410443c007121200400c20071034000c031340d00e8130901144044030030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 778813228 1250 778811978 778811987
    0x7030501090f090807080f0403080307050d05070504120f0c0902120405010f140c090609040f050403021c320a020f070602191104090203030d0606030b09163501080c01090b0d0c 77
    0x1035620042d002e0707492a00c8200142379410010044200e1420100131500c450f12400548080e2081e540c1c1000c030341d1005685440c4a0408560203c230b2030b601d1100b000450340494406810b41a4007003100806030700d81850035500310f8164070b4856540d1480c110a00e80c3d8004603005265200c8a41c00710aa84c1d440c04030002281d50242c00307001a03000d41861000f03c04d03203e417900158051482602203c42d03042c507150313a1130b80103030309003444400145a500103408124030b0543c0e08094840d086001f40b1904003801801d91907507025000020140c0e00c65100d284003400308128a00040178944041c0900f010007485011003107114000280000380b12040503041d03607407503134001500c0603070003800c990740c2ea8a40500c140142c542c91050700301007840d0205404e800d0a140d048948a02586031007003003148850441601c4000004124005005103c104a1201441e241120314000300a001c0000951f2428840324640303000707201d0301c44c10003201c0b034000c10414a003001a601c0d036280d96007020885120101c0d0448 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 778814478 1250 778813228 778813237
    0x10815070c1103100603030314160513170a141c1110050403031a0a030809012604060504140f120d1e020703200601051c050607030501090f090807080f 66
    0x10f5060080362140e600b140301c1c5601c51400c0b40d200b80c606112546a00d02a46400c0307408440705269003050041000c1b90a00c05c100a00d0003213140106002d0751a2504183c80c0d0318510041d85030f81c281d101c400440284141b0394910070308101c440c0001e1880c00100b10b84860040e403140741c000c00b8000390203448040074106101c01c3d08207c40b071040030091843c05080c001c01620b407072143c00100054441c0700b0345031030824039000d1050780e800ca2655454003400e280111170034246540e0014081c1c15400000a1200e92500300b140964010b540100e82360615003022410701c1d89001d050309450b4420515070450312000f14004136020040c01404e0b844140a0801c070300034001c080c2070200c0b185610310414100c1451940580440350099880608406c04c8240d0806040c0b2400000d0505501810040ac0715141000380d98040c0e5015501e8000080040d41e030308c42c43c000b0252014004207440308010b0040c0501c1d4424440181c03800300080c48284965100c4010a10070640054150000010b80c0c2c41452507100455 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 778815728 1250 778814478 778814513
    0xc0d02150309100b0109060e130219020f0c04060e161b2102070609090908120406050417030c070b060a032406140a090c1206080c0306010815070c 64
    0x100d41d2450304040003a1101c400034000001c1c680361442410540d44100e01110582d00c00f5194616440b1200c030400c50094144001029026000c215824807014800c0070128000d105070010702c080c00c4000019420b101028074003500443c646032041016151a03400a038000c1c824400d61224403420180448641e40d00880b903800b180f400c032401404004c02e91102150302c440301c60890485403d418012603d45000f13105550009000031400e11a42042e45c0c0300b0407280f4400c000351441c0034500030020000590403501642c41c2c4d55950100310078011480065082000d0f607616233480d510f4140301d0300c0498002c6180107842001180d000a8503074640c00c00d510041e5800680d01c00c0201900d003908006014a081210f00c000c0c24000001445413510800c2d413003281d802028540e180d810704d02d040c0c0081c0300a12201c0c003040680d02c804104490f0314800c01000c1c2081401800107556003405151624006a104103060781c40100ca00e00c0340900013040d00c1c1c000c031291030100910308484c24020900c81008055 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 778816978 1250 778815728 778815769
    0x30f0601060903151122030204060f0806090d0503181e061902030105011d041d0c1005030f01060318050304082a1f031104080a060b060c0c0d02 63
    0x440c1d1642c1060440c1d044034803541038120f44034000300c0c100e401e40d40d4401a901d504503081c00240c548907264400d5009110006802d60b00c01c643da50002000e54030540e1041d03d0b03203031582e00d0901011006005860340103029000501402002001c000c0c0701e8440103001070046e08480078104e103904401d102020001d14100d032128060340254a0aa44581d0700740c90440c6c5032680340e100900004058000c2d64100d450585410b43e907021050100b8145021458801d94409d5441c3e2240c403001c030104220340d060f03011074401010303414200b1003800055130340c58032103000384103041c410010400c3c1a1900c03941511502e28010401160b4140c004140c4484068020072a0202040100301d20200050396a4a400000340d94140da4400f440421030802884075001d400c03d6410440c0810172041001200b41d148244c034002605030142580548940c12a410201d01508081d00c44400e0262500600640c2e1004941003441c1c560542c1c1c80ca03540d41c1181c0032250007541c14180000035550b03200a8111200d648400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 778818228 1250 778816978 778816981
    0x106080f010f060f0f090c1106090a020f030118080903030f0c15070809060711030c0a0302030403021009080601120203011d15070f12020c01020c121314060901050306030f06 76
    0x11901804940d582c85201a152100010b050b107151101039040707078441000061054200004031026104085011042c8041c0042c40c03072151008018592007148020058161808030303204100e548191803034001c4c4282c0c1040d820702c0b5000317640007508100e507038005000c80c0c0e211540c8001c41e00314000d802906030785280c040f80b5458005c4002c1032501c0c0c00b0040c10424406551000d60540b500c00302070304c000c0c110740e10600010b40c0d11406140400ca201d00510b044904000381c05482c0c616040d9201022001604007103000c0046080c07580c500d210382c00150800013011421300741c51a5562405200b800c2c00920300040c640c095403800e511600e003400b1120b0b4800901603014481d60703a03c1100d40d11081c518641000000d0b1403512820a208444005540d01a1070b001c01005800280d0040c1080480c60b550070007034040e42d41420045040d8010703545103019251805018410345d503030340c640d200b6018100c5060401403203a450500700d60070000e090a24580765295035022914010b1941300b10541403050a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 778819478 1250 778818228 778818253
    0xe0609061e07150501060201060321020f100e0f01180210030609090c050f0301151403031902010b190602070312211d0a050a030c0f080a18060f021b03010608 69
    0x2c243e42c407040c40c410144500e90f40d82d0801c0303003207500310302c00078150582056551040300054800b5000d41310349441241c443d00765440750705082a5041c40302116150b07541000d8401085c0c01c3c0f116030507600b0480020480c201362103036040082001e10a0003803156405060728071a00f400b0b0340c050b801030410178500700070b40f10302880c1c0300782508000d01400c0d101d0820405004580c0ca4140100030f02c4003042c0358090401440d203c3c01040860040d07425961500050000c8595000c103502c1098481e4010341c00424020314401c144a80340041400704c114a5111040502c2010f80000d115801c072030384812042800d00d4504001c945240d003061050884108043e0040c401d018140c010154025a03000040810903178807800e00d0303032440016001042500b00d5022017000c01e00914800715480d00458245401c0c00c190f0348c034110554808180300000c90801c00281c00452556100c0354041d1802d804c00005140d01404065a11709080c039507403010b5003c40900f625951020b4020000400c122411a409580d284 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 778820728 1250 778819478 778819493
    0xf09121125060e09100506090d08032e030f080a03021903050105031603050721021305090d111c051902061506030601092c040b06010207060e0609061e07 67
    0x10300c9014000f55100c0a0800740b49015040c4d00e0044001c400c00ba210140f4140c240325203034200700e190690205e40740c4014404607c0039002544503001c10708074400e000c1d07040d140c1c10511001100e0402d400751003101c000d00005840070701200702c1d42c0d0003428040e140c030002c8908802a100720100d40750501045100700e007010780c0541206068900c2141590425443d0300290f5040302101e102c050300980c4503010421040c012007400401564044968050a12007038000c144482c600d4243d48014660310300070403102070000c2c0f0045003105210701c0d0484814a00003216991401541d2241c920500d0303800988040501400c00c545a000340d9040800105210703040107502c0e040300722654000000c1c401d00b003059a2410b081141d2240c03405840303241a4a0801c41c403c6444101041512681c0d42c4250f44c08850039211030340c1e18455841035143d00414a0030700002820030441d07074080d6003440b0700784034042d160750380b4002a50000501a14140c1c1c4458201045c11008014500038a040710303400903400c014444a07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 778821978 1250 778820728 778820803
    0x503060a03290f061819050f010f0b0a0c140a050708010e0105060301020406051903020f07060603030f021605012f03091009030c09180204050106080603010f091211 72
    0x200340820b49030b40c40b00549009200d0480381d00e035000207038444801603980c0e82002d168101062490b1215180c62042d2210126001070f69001001450240100503034220051414090108810103509118065802400082c3c000038020510031540e4008170020504101c00200b5a030810119540d00b41d45030780180c000d01c507448000c00c0d00d50819000903414241402160200c603003d0780ca0310b14150811079070340712076000c0581e51310406400b085a11585450100980205400349d42d0020321a8075515010307000c1d0341c132040103100755080001280301c440440702c00340c01102c0e000c1c208007845040582c0446c0403641d4201d000c1c9003000b24014a5426000c9c000b02030b01807002c040d160ac14204a610505840300c881521005100045500003406840d6541c2c00c44414442030f40300004601d80980e0014003682c13000d82203c0009900c0c442006900c2c5001d019410310640701030020003081006496021070101e80c8101d800c24000888030020420320100f01001042c03501d007034418600d091031200b4598603202e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 778823228 1250 778821978 778822043
    0x14060d20030a140402091b0c0a08040e0f04150c1206170f070308040510110f0a02150c06010b090109080a050a02010815011224030b0612010e06070503060a03 69
    0x1401d103d4000801080c40c2c580d00032900100b10b02c07506e90300e040d50701c0480d040500000d00c0140d030910110716a514104100c0700041c1c4100c1000752074a0500c144e41d806d001d0b008012600b011810002d10000c280350b51001b1205020111011070316200101040d1142e400742c0e40f003681150b2410000203000d0000e01210300e510700c0d45100b035650b402048240e8554032112404041d111800c20041001b80b07152009070a1000515428070701c110501c003041e0301303082110321510401700e070304040e003403000f14070b003140c07055014203031448819080032050359000d41c0d0384405008003200d0075000220507010741e0151168034020920103080398404005480c013292500d0b2125400c0b408a00d01d100424400e441d000103102500c80103039611007035102d8501d07a505c05895401c1e04413581014030b003034414a454100000c800914000c20103c1c9090030814180000d4110410302c8803041d074540f0320310410b0001d0210700a50002207611b01140c81340c03507a40c0020403140d004d030700041003e603001c1203018243d60000388010320401c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 778824478 1250 778823228 778823231
    0x9141207210611070c06030506150703030506030d030e070501080406020702090420060a080c0703090b04062001051e0405070506120405010b040b060904020f0c0304080307050709020414060d20030a 86
    0x1090242404004c3c010000018800c0c00304043c00c0c00118441da1240e0b912020080c0000ca00203a0111020b000d90710654013600040d85803001c203d0203027030400802a4039043e600e01003101259195409850b41140d00500c0d040010f480c000c1814445250141c0748507980080c0b05802e182000d01c0c007500800c070f1100302d10781c00c81c030050703c010901d240c10300640300c0c04040e680341d50490395a018440c20740e65220301422000d000e42d4880106064003a8400340000e0030154580c10182e1600110312040c802d0501c90b80070b040e0307040034104600c00100024065506e0948180080180c455151982c2020000d40006070884070114900c04c0c0000c0d851030241c0998003c01c0204080c0c40701e03909200c10f58000140351238007c4000c00c0840c3c00c40c1050740c010a282c5520442d1075003080303005103145003582d00aa00607103c07a8800304001090050520082000b03119210301145400d03c1e041030444012410703422944925000710311190314a88681011296414a540a601e450780340c070000c0480b90000d0b100495110b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 778825728 1250 778824478 778824491
    0xe0a0e01060819052a090405011407091404060b16031b060207110d02013603050c12151f0506131e231804060207050c01091412072106 59
    0x21071701c55404031001040000e500300c41c0200c0405120380f00358013510860b982c0d1340e00c0c2d49a00100c2010700c21940a40850340d5044449443d000d1607071020208003000c02e10441c60001e00f0800b0351541d4003100c0e01102c8454030b8003942170040c2170036115040000740030700c2d15003404485101000410340c0109a5a0310071150064032190001c213100346901002c80c002e001c2001541542d02c4880100125011150a110600c0c400d1075801c981b0b41e090140d81c0e00465060f4025449146140fa20402100c03040746002c0080c040c58070000312800030414054080c480002c91900341100003001e200d1603c018140280c070580d9204140e2210310001c0c0380305c0c4140c0c0304000d00c20802c00310000956150104403140e16140500501c5085000d4100d03050140b0003d81c44826800002c04c00410061624803580c09080c0050b250145810312034200703070f00f00010302d042120a140600c02880711f17400c410a4410700f504d06400515481c40d00c9840c06155400c00302c8076810040000750140c9100300040e124070f2203180280007a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 778826978 1250 778825728 778825753
    0x3030d06081209090f0c0c0a2d03080411030106091b0f020c010507110a080d080709080d080415060519050112110910020705040c030b18010e0a0e0106081905 69
    0x303010b0500c3c41d652040414011079401c0c000411410741003240e68042034074101c00582650b20f8620300a000b201c1c0c9641903002c1124650380c48201ea500d094000c100c0c05240016031364014503491006000070241c0d050742101d020703a91400d50116005d482c1281e0108240070240b8003c1e407403400b00d86100d2000441c000b010b407000c5880400c0f441c3c2145410786915041034455581d00501080d00e01d50a500584a100b002500b0802089041a810302c0707525543c0f01c608001070014030380405600801e0644c0d02080e6114240c039800010182c0c89a00040c03030540c1c40d0354030301c01c0f10054000b80c1d10840d405501c40341003a51b091092280310381112402d89500e00317040c007446200703c02d49505111341140002c0c07c3c442510303241860b001203042c2540a00c103a801958855001404444201e0510740019036502d9403800030f410006240794584464402c2c0300c03055071500c00f03a442c17000301c0100301102841d15110440b4011200f5040700c40600f043e201503403400070303045034810f00000388030005480c84c0c403800e0610f428 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 778828228 1250 778826978 778827013
    0xc0801051c0b010501051c1b090b0412060e01020c0d0801171b060c070914100909020f060c0a0c0b19080c04120c03021807260a1a03030d0608 62
    0x141c66404440748070168a010015242c940005403e40036a0b1000e50b41120502c4c01c170f10884061b00d40081c1d00780000265250300400d060100d801c00c52030040c0c10801400310404040d1030103151580000301043e5400c1392600107029004030301c496030b014420088a4142e607070300a145a03050310002c610210441c0b582680c0140d890b030740e070140082d100403015041c80e218240070b0020506001d12808a4000030744d2020694100c941c503285215403c0c6522041c4103100707100b030300f62800400c1c5030f0350b003482415850703000244a04003424501f4400e00000800d590884014850b052410380c2100040c000c1694a00c040030040d4000c14440321064104028113001a000f00055030003009600790150030b060074841d5008000101031410360300400b24030400001a85c4c0c08207040c0c001c241c21032010f6280e0130240760190420b600c580c20306122043c02c810120020240701140c40d0700c140074250203e894070b440d10000509051a464003074241c00000b80301030365400141c00c10000c407088903048914050043c002e110303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 778829478 1250 778828228 778828279
    0x4051801050a062303120a08070f0e060307032a030203090609010608071e0902030903070c052d04020714250e0c0c010605030d0908120403080703050a0507060c080105 73
    0xc13074103d1624011120a140e400012040240507085441420b90101c0c5d00d4541d8000c0144040001c10400800111742d42c440c40060b50b441c4c01d0300b00103003d40c20440020b0228000280658205a84c0700c14502c054050007010381d802c2c0c2c4694080e44000c420f0200010040c1d401111942850b01c50f000c04500c8184052280104075481800075018042c2800001c008000018680d0742030782c580098041200c4a00b440214010300740d5000851b5280e03090315000d96000b5190384902d21071800700069000034072030443c0d90792462200500344d086c00c11071107002030028003690718003078200080e40c60400126400080c20800402445a5910a034100111002c8004441e401175080c840045070201d4000e08146010b030007070310340c0c4400100b00d45441c1c001083c134080d140d40304000040d40c140c0c401c128074a8240038896224a4010196140c9800e5848404e01d134403d10b000142003000029105104600c0b8a09403001d41d0350002c410f03c00c42c1d41c0700744000e00015003030080b41d105140102544d0300d81c054102c0b40c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 778830728 1250 778829478 778829489
    0xb01080c091b03060d0812070c032c010c0f06061412030304050c0906120a050127111c0b011e09150504111608040614070c0911070204051801050a06 65
    0xb919680d220000d00c82010810807044400071803c0c48582040d490681d41c040c4208501ea40d07004c5070007a0350034000c01006000d001396401d20403c4114180120b40700d440100035140a007000042a00c4510300400741e84803000d8090310281c5400c8011882e0041070204210503401200c0035800f0074041540755840c1e01c030980d07008080b41e0000009041c01e08080001030386c020802080d6001039600b4001c240d041060200045076165960510700b01c0183c000d050f030f604400000002d290200d4107503600c40340702090010b44e980c030a1058103503071203090613400540a0041d500150181095a641d00303241400740c03070380303045003115902d4000c0480d00070701904c03d00002c0b03006d103010110715901d01014170000b03000031986004032030800c008040f1030b4145e0401c03d42d50031348100d40031503555103080d00081009034821100c04c0d40307681c100311b110080384010070302d4000c2e6000740303500190038011810312101d50f10408400a4210781044100200d80403459043c44003858110b0013402a03135502042d0404440545c050b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 778831978 1250 778830728 778830781
    0x30b0108090a060504080c1504200d06050411120a03021903052209020a090509071422120b090d0504080a150b0607141203041e0f0b01080c09 62
    0x404990740b0b030013142c0c0060040860750302c0c1964041d0618200013106050500f8030b400340c000c1c00104a10b01100e10031051030f82d80200304d8031901500081c4030b07181400c40038140644840120b424080040020408284014004020b0f02064115140c075075040700002e9015005030b420f010008200c440300002a1603050355414500320140400000d40f911102841ca40c41443d5080824070a210b44020f151f1450142c80d00c0c140c00e4602420081c41090051a602c2000b41464100f502c840c40042510070201924280903c00a0309054240030b00803241d000a83c045429a050002d101d48142c069019241ca00181d03a00080010001d0b5031910a84c421101d450707112851a0005c40c0d03400485d13802100302da96020030b401d01c00d540080c0c22a000300d403050307070a02c490718081005020300304002c0c00010600c540c4a0704500e000d07112049a581028000380c1076111495000e0300b004900d00280c0000b503800f4543c0000c558650103503690b076070b4505102074010704400300456117910b641100440c10114003000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 778833228 1250 778831978 778831993
    0x1e050d180b030402130902030d0e1e0319030c050601060f03050f070221073311070209150907030b040b0d212006070314041211030d0f0903030b010809 66
    0x80c1710302c455102001940159803000400016a020b114102d031000c40c80c0d81c1c2c065044d101d0070401544102c12403107160034010109402d48107031070202d1031400c04a0103490040141e111401d00b80c408540c0610000c00d580603800000c40c83e540c0102480f440171400f69400c000c540e03681c4680081a4034107403114005070703001c0c041d41e0424950948503905a40200010182084015580c0c413440220440089a8065002c410180258004100300e045100d5484d428444200d441a4514840c4524140a40100041d00014041182e0904001c200c1807020349100310700d161260f0024010031800352402d201381c0c01c040450b400c6141c12a03038040b071b0342d0300000c0240e800680c1c030400c0c2000d0040100d03540d0512003c001d01ca468030002003246140038008a014103258a4004401008c0780e00120000c03d012007000e080c080440c81e1190100c0c00e1400e40c3c2051881602c3d41c1480e03901e940540d141c6008101e0400360505c58122164220307200d121f01c02d440a01c541c000030001914102000c607003aa045911102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 778834478 1250 778833228 778833233
    0xc0801060809071e1206020c1213090906060b07050604170408120a02070f080a05010b01090e180f010e011a01020303160302090d2a0b03160c1e050d180b0304 69
    0x4079210110130480103103103641c803001880f114501c40c00507203c0703e40c04107080101400a01141c400440c0f046419440e107264001d80c82144007260180e510b4142c4d85498500800c80594801c001410a142d45c1603282c00b42071801e5581d4020854044a21844104070414081a10400c1d01c0640e40c04001411090141c05051685074000640b46000c51140c0c00d40001c07038000100c168005080c030680544404903407400c00609444142d10642e040051b40f100c00c220200d103100c020380e04041c0c410b41c9070b15041c9c40034003c280341c9000e074800040c1c1540b0304840c2c03a800010541c0900a2002810902c42c0100514401a41c0f2804221006c0140010803809201903034840e500500b020b02e001000382d07019031702c40c2d150039001103018030241000d841c81c0d4800000345211080f4500062003c610202c0c41e51805032064036240c180e00d000b28052052802d2070b4003c0210360031005c0380c2450b408205204009403420700c41d656031480b1a018020811100000c580c50030000d001c0000d0720f44425442c4d01c2e54407a41d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 778835728 1250 778834478 778834499
    0x1f0501050a0e2806080c0a120b0109091505010e030111072604031a0a0902030c10050d090f0b0709032003150108030309240606070503040e0a0c080106080907 69
    0x14071149922001d20820605030101d0785229030101c4000f0361850306454145140a45180009401d000e41000140007a4028541c010a00d03400c0000e803031000f00340e14500000503107081d121600720a0185090411002090108010850460f07400f40e944080b000c611006141c00c0711203059182c80d0050b0104401000f2501c4031075074204103401c061300c0e80d040e04004141da013500e4100d07400840e1000302c0c0c80d0034070312007401511501e50071000401042000150a60000740e0310280040c650713015000314480b001045000700259501c0c0000c60105011800e00d42c0380c040881c410f454400c8030505010000f00e0761030ba11540142c01a07035440741079200d02c080e502441080c0d80803402c11341541841004003010300d01c50b10015080c02004600001e40d228200345216a04001107840c4405204600c02e0541c0e40c01e0300212495a00107205641407a40d800950600304c0c118800c03500602800c0c80b1030300c01c0c0f211110031075101761518502a6181130030399072180301c2211001c40603103003d1844c7e80108014801c41900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 778836978 1250 778835728 778835747
    0xb1305070203120903070204050906090a030f020111071a0c0c19080c0a0302010504020f011d190806041115070f12030b0301060f030b0106210b031203010b031f0501050a 74
    0x441c0110b0341002c00c0031403140c00e618001c941344c5600d600045074585c118105805030980100122004d8001417410907003641e40c40302c0003040507042103909504043c16600030360180403d41901c980466445200e4107100c0310280b10070100581903100790340000e0303550803004160b80341005503030080d18103031011609680b40d55801c5842650b05a208205000e410362041180103641d40c0300e83c0000c00d0910709801006010003080e15814141f0101084041c542202030300528200391048600c100c508035441c00c642c8140c40160084402c900ca4517003400144140520030144011080311440a650102002140d05000d000c030010802c074a003c84e440001100e03801c4541c0d6031502441e00051042084002900751900c1303600940c00e510303800c0c07001d005102501c0680c2d800341c690350030840081c3c83da20f81640036000088803100c08080e915001803c255500b48003044142d0200da01203a12540c40d004180d886520aa4040c4402042e40000709480460803c0c007038100c0d00c05864260a003410080243d079440603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 778838228 1250 778836978 778836991
    0x3c060f09020a0e0a0e070f030b060412290906090a240b10050c1902030705060c0708011d0c040924020f030103060203070801060908060c07051e0d020c040b1305 70
    0x81d11070a580039071311088009001000030060b00c4c1c60038244041c000d03203c0c240b0800f400e01010f06042108013540c8440044608940c107030040e686c0c80c00701900700800458001f2080c4850b01da10380141c8038204031a61010b9000d05002000c0d02d13410f440300011a5a41d140c5484020b00200c1d070628004030540703a5a507040020f8102c95004075501d03d07490f0000d8080041181c00c5804104081990395a40070304002090405805150b01300b61482d5540010fa59100c540c407880344189070014182e80b81e4442030104100600310207001340036980240b880410403210075580303410035220701460700806103000c1c00303505083c82c0c22002d1941c002070180035810068814032440c0d215030750204601c14003090350100031070095015070303001078403803c00d810010411401a40420108004500c091081580203c0e4041c0c0104008400ca50741b82d2091038281c0c00e000c2c0d0200248803c004081491641d9038010800d01e0301f20030143e080c0d810030499641080100d8002c144c401360403070080e066542800a07164003030b540101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 778839478 1250 778838228 778838237
    0xd08030603030c010606090f1d01351b041407050f041a0307110a1523040308061908030f0d1404030306080d0e01020c0f01033c060f09020a 61
    0x28110343c100d09640b100d07400103000844100081140803c40c02509002c0c100500b0303202840d142d0054413054404060103180e00542c8a00c001030510404000315154800c480c0181c8202c100c00380301c01a0315802c07900307080d80c044000c4500007161460030784201d69008181e030300c02d0f48031501c980300c00700d5135904003825459846004000204e00c8407400e040c0100b0380e4400c007829681c3e915040b0030081100c2070003804500c05a22a101c480700103041280c80903074400f40b5070340000b01003100c2c01b10b085903000c4903440300c6051100041400145940300c10101c0c405c407030a07200c400e040061603103100103402040c856034003d504184001218405541c005048070140b0000c00710760021403000c1142501000d4804501081e510102081f0581d02071140d044080b00d6801c10b152000a0240080c0d15070703102801c8288036904000070202203a010b9070100700300318200c90384440b408000c0c540c04103903aa114403500503104a088408102404140100800c0ea031400f0316a40b145450700703c0761400794100348170380c0b170900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 778840728 1250 778839478 778839487
    0x411010509120609120f03040b0604060312020307051b0a0b030a0905161514070602091503012c04170c010e0105130201030c1409121f141003020d0803060303 69
    0x1582c94080c140d00446001014001c01d0030300010702c601d4003580e1401c2500013a01808a00c51440d12281a268000e401c43c0245015640c1d840024004000310380000b8035040b4210700907240b040e03001015002251141040303c481c1406244030540c100348001006902812608060000c20015000b460b081003840f200810641c00564409041c0f410b40c55217031358842d038080f0341003084202420011103140310038200440300c12221055040c081c40f500d9005050180c002440210303544519284082007005155010340301d517128201d80c007a040e440000b0103c041211000c4804072410074204e50301890780300c80c03c2c4416440f8004035040c6d9400042f1008115503990340302044030007080c01010320848400a1002d01d40c5101d100160071240c010f052001081240301d1040080340340740040f2800d0342c05c111a10807840c5240c64405142c29034800500c407200303000241c6084101925081005641d070a80909a01c82d6030740c2c0c2071044413081d6444041d60007491144820f020a4002e001503030411005015607240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 778841978 1250 778840728 778840747
    0x250909031e08040b010f0b1e0c0f0717010204050a0e090f0d020c15030603060411060c03040308031006050c153c0604060b070204020901020304030219060f0f0804110105 74
    0x35554040c003038800320b21070300204030400c6220681540506400c82c0b00d00c0c803c0381480300050391801034032243c3c1000d0b8045074088031040425816a10000f03c0281101e01c28001c207051035440308805d11640060a03c00d1600740c80a1a041c003d84007640d101820268000c0d280c203814024940c0c000c0c0c401100c03809071040e590f103000010321244544001c0c5800910750f9101d9075040c8030b41500a46240010514244184400d170386d8007060180d00140c20620400700025420000b035a2071252003848003540c44000707000400c008101001d5403069041c44000015240c1d544425252441007100391140c903084001c10425003a160188242c01442c0043d00e50310813540c031051504606040c0d015800c640c03480d80c002014400c0c240f0f00315548181c0c180d40c144403081c50410000c9541c0a00c94009200d0758020440ea034690340300f0415140115001003040e8000080b0f0541d1050105045c0503400c0003c0d8003008405d01e00d8081c81040f08100403e036100c9055a555031283e414003601060064104441008a1080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 778843228 1250 778841978 778842017
    0x10e0607110f060c0a110411180a090b0108010e041e050c040e0106140d050c041506030b10050909060d29091504030f02160311010225090903 62
    0x420520608501219050010410080c2e0807000e00b0984106010402c0c1410a0004254241d01d02d41c4a141942c4000c43c01000034060078441c80480c00c2c030a0042905110a08203800800e0506410f8844c1050141c42c3c04941041c1c66056484501003803280c0010014a000018410f6003d07004031410004800c150601041105405606980030791040d0364010062409100d04d40092007508003c000d5603150107501024404100d010b54418050340b01c01d0020300000348030b000d601d000c2c0104100074a04048400c80110a824022440000c0c902666120582000c88000c1e03140d151a881d07044c14184801d0801014140040246421141801003440007401052424403540d80f40381155603818041c440240b00e00e000248030b002d01390301000a0340501a50300c06516005030b0103240c00a5054120341d4280c3c6041581450544006001a0300205012100c015501088000d03400e031054001d04a0070800148500145003450002007801044120f01d0b50303120080280c841c2c102520940c045000009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 778844478 1250 778843228 778843237
    0x31801090f080904150513020a0507060e150c04050108190b032a01051812070f03050109060c03020310061112180a050913020f010c0b1501080601050f0d0902010e06 72
    0x19111107010583e20b075030b03103010f01609100d40c2c07420030404980c07881d180010720302444c004852844940e00003003400c486071080c2c085480243d0001c40911074403184500040e40d541c501c500500c0c0121511000c40d014407a50030032101110016941c07091140c172a612208504089106817100f8503581d1041c14546450900000070301d0007101c0003403182c0c06080813051125002d00801d40341000030030041d0341a444210065542c444806541d1541c0303019603080d20b10324155a54100c40b4080205640c00030401005400040015201e0742060008100000e401e4082e404159012072030f2507402c80b801d004080c8241c400b9441103540030304407001c4200342c01c01c1000300e0380700726035001000548401410b40b509010070340000600c4103840310f90081c640120000e9036140503810080c4039074228004c03468682e20418040c2c10316504074142124508000301010031030a5850300b001d01242c0c000307000904a600600c10f6500000342101d066242107004602d110042040640c124180b1410804400302519184040c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 778845728 1250 778844478 778844483
    0x10e0d17030c0c010f0b0f03070e040609020604050a23090c03060d080d02070c0911030f0c0a022103090c0307050a0e13050f030301030303140c09010309061407090501170408031801090f 81
    0x51600b495405001d2921180001f850080d80044010000040301d050b055034890341144002030135807020f10000e41035104552006a111000308404208003140700d0492103600c00c14090100381c900d1540c20302200500840d203507152302c2401e02c0043c1c489c2c14082c940e2903c0d1446a404a894080400e101400f01d8000c1107003a140f18804074018403071802540314451020311019481800c1d41b818401e0340c1981240140400c0c5c0340c06c40401c0c2038010034000c000c881c0e44d40942484040c0c2c42c1f860b004050a0303941007207800901e02d10400c2c0e000f050300e003400b0a24030281c44016003543c44490410500300c0c030403c40074000b140d03401c107420100c1d00401c4050010070000c109400c0a184e0342c0d490341c2401016500d00e001d010101c0c048a81c1441001c920071012240d1442c2e00782008108000360703040940007440002c0304081c03114145001c202ca51030b84581504140c54090b2165042015a5180d42a2222088400030076540c0e0801c04500e030b03034440103200d00c1d860800c1c000106010225950303407020482c1e000e508 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 778846978 1250 778845728 778845731
    0xc0f0b0406031a0a06050c10020f1225050702010e03070603020714120405010f032904110c030a030b0310110d0c1d011b20010e0d17030c0c010f 63
    0x140041d5501d07020b00c2020900726460102c0040703411001543d41a450300c205014400000303124103001009020308035440101c0e040442d1224003038070f080310300b940c044e4041000c001403400c0000d2500d015440305c84482e0601210521032602c51410540c0e072603204030402e81c1800000c17010307640c00e56000c001500180c1030f2070742e016845039580d01d00034051304040c140342c2041d60000315000f03100300102416141198024a4040b40c80781e032401c8290001c00105082c0303480750a078101040640c070351943e40781c017100200362410002c00075022181c181c00e0040d0188890641c01c108003945500c1e10030b40003400d901340004d068960700301000f51140704a4031116031610801e2400314001c3e100c090315110300448200d050500c0d4545452403031000b0444408800c016050180d803904240401c41c500340140d41440e4071035a000c000d48450503a90000c540102240c17030021b403109120054505148120b507480c180c0c0b1020600c801080d61080556541008004942d242c4061000024425003400f40d411818003c020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 778848228 1250 778846978 778846987
    0xc01050c012c1e1c0302093304030201080406020c0c091008070f05010527060c0313140d03050d090f030e03060609100905040524070905030a021008040c0f0b 69
    0x510380e08007a203103c01c1144000e00d103000c080c1220710104898110358124074008070b240d000440c1c2500240500021690000c02d440c400312040307100314200f0620014070b81102e20701055170310a174004900c6580030081c00114a000400e0004c0c7c000d8018100d051541c209444100c095900424028202102e102c681c000303480c1020000710310300b44005000307011507910b801543c42c18000042c14520814a50410242c15101d03407130342e41400200316201d00807004002ca641c0e42d140d90240c1c0d030b482e002200040c0301c1d580c0902d00082d01c8403c10b080200303690009800048d40300c0160b2800e5405d5044a1014034105032940181c00c00280307408005009648030f03886102d19484407500b81890400003d02050003100c41700c2c05c0c000c0c4050080300c00b5080b50321542e004039040c5d4552915608108542c0e4200303a0b0031205c02850380c2d0b20203051201a104040c0343d42d40c070180d00d070b43d0002c15544001019020f50088000014400c210744a4500b40d54806d024503129600c0b1950742024031103002c010343c440c5400180104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 778849478 1250 778848228 778848311
    0x20f04030803240103020a0e010e0d290609060f0d1106120406050f04051902010e090708180c2b0b040b060117040b010b0304020109030b070504031406090c01050c01 72
    0x407400b00d0f048003c0c44d045081110386640a13000c1d03130420031482c0c14402d036a180c0485954070524042c25a541c00b08138601d40c001c503a4503810340040e101380340c0d00d01d2025840010390765007082030000f0b10450b801045204180200d100b031088030b0305070754000c0d10200403412b0144001e0316090b0091049254000e8114001d01c1e060401e0f100322040900009605410302c1c0510002c92400a8907003802609908400b004c45020320040c1c41d0349800c80d0310580c001201404209086400a80b0184105110103a428500a032650310321344410b01003002c075074070054100740038400c1d580b805408a40c018120201484040382e9482c0c0c0761102400b15011503058240c441000499648200003102c05402c0c0021200e4500f022740c0e035401c004c40140503c8034001c02c0400000c00f5603100e940c49030300860300118055214200707540010160340c071600050358123113000400d240b50710f1800544c00340700d5403060000d46000100704004585c140e102c0090000349648401824032120013186407520320362020340d0800161110b10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 778850728 1250 778849478 778849531
    0xc07080f0c123904050a02030f01050105190513050303070b01091113171513020906060f0d0905030d0606030b0f060708040b0304020310060b09130506010e04020f04030803 75
    0x104025007180e002443c002c1940b49072072042240306200041003010712045074140000118140c400103501074104014072440104070b50080d4052010007072001203680c0c841005440601c508009041d801c440c0600d000002803241d000350180c2d08012041401055403080002d1554000030030903a105200e400040188196603c035020b40003400c071b4a940d00b4000d0524082d58056443e1045074480d044100da0520b2250007031000c5c03c4c000b01c40c40c52220113404c119603481c2038900d10020490181c0303000d10120794070b481e003c001c0c0c455030307180340321020700d003034203407884140039103444401241c0038030023403140700090040b9015032f80203030420740d400140882c41c9104000615502380420780c0a140d04000340404220810212810b4a80a0140543d280c40d6440420f107091808040c0c00895460464003140742401c41009007541ea9003140d40d240c0031032908094000311001900d50074003160410041c0c0d41c42d414241c001d04103102001c00103500f4166aa26070781825030080340d408504102c121403845218860 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 778851978 1250 778850728 778850749
    0x10e09070f0602150406090c03140c2b02010e0424050f09070f09080106060c14010506011d032109031204030b0604021606090303021b06090709020c07080f0c 69
    0x707024044030340924210700a51504030440103040900f049000040a00c4440d402080903640c0c090480140035035203040000e80c10728000e0f6202d510340074010300800107103801d49091001c80c454451250f0320351489040b1070014204a84100c2c1440040c2801d01007a80e41c80c0b01c0c0c03a8010440308490403207160542c081e0480c1c580700350081c0e4400c08408460b03042380d0719510400c1354460464104400700410569064504403100e0717110301003c0d070070010040b030400c5d40058084116441003000380031343c0540c0c052941c03d1750710445038240060032545105840384515044030031842300c090150b89120b80c800080403039500c10440d000c514030400159110250404001030011280090941810142150380e06a940354001e00811f2085401088049201010b5451060040d40c85541005625640e240c080d01a4100310000001c400c0f51651100c00b0744d6010802d24440d04000300589940350814280c00000d40014107428810702c21001c1c041000901000700030b140350b006600900c0c42108081c00c00102212 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 778853228 1250 778851978 778851989
    0x604030f0e06070b1b07202d13020d0e010e0601080f25210b060402070308010b0a020c0907111c0507150b06040909050111040b0f1809010e0907 63
    0x800c03c07415010075040025070750000550840800c0007030800d1084650350142c0c4a01824100d14102803c1da44030f0198200820f00b0000d58580d0084140155001400040340031100312034003100c80381c00c000345000c11310704030b118060420060a1244506039101107620034111003c503a952440c06609941c0e08001f002d0040400340002c0042d048240125911070003508130b070b40c06c0c40d10700e070610b603000b101160388135030141c03111034030008488016142224102c0c041d00e10036207100c01040d01145039800c15008503155240c240d19910038592078050780041340e502c4aa5204114041c49044000c02d41d15000713001e0013240e256403400c460350802002c0703a01f000b104089036422454100490007540390440c084c1c0b0304558004c0314400340269074160540140641124440d80010001404980c00355554088403039180914020450f42104048d1a5040c0c4035a01400280d5281070002e10020300d021801014110308148010007142c1c164404101081800e0b048000c424562604001c80740d081001003900814 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 778854478 1250 778853228 778853239
    0x403080d0b0906011b0c0b0304030e040c050a020c0d06180b150f010e01080a0e0715030b0604121502210403120912050d060f090603030206090d0503010e090f0604030f0e 74
    0x105000040c0005042d031285c0c04104e90301e5404402403240700e40901d0700501c800e11017a0f07900d24052034000e21a81c401000c247c0b180385000300503940175200e8415100e54a416400030500c5040f82d40c00c00454240d0410111089901c81c0d00100001c00084246803800788106001405420801500c5210003d180c0c0443c1c0945166980002113a81c05440d80c102d5000a0038401c4880d120312100201a114000e054411072140d6000002d030083c5070361001050b15150341e0b00300b1010410b20100022881588180d440804d55401e0b00707404540240c2d400540381400c280018504000406101c0210840020071900044803600304014560018541000d14451400c20000640e055923a0146035517410115010400049900900c8110716807251001c3c088050b43c029540b6501d003140f1002e052503002c1100107016010104001200020740f18102c03908649840342981e0800201c14280d04004200040701c1c4614440003410100600c00300b8006c0e4003a82c1d0f0041000c0040c00003600c0d1681d012103071070054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 778855728 1250 778854478 778854481
    0x228050d11101401030209061c0b060a1a040611032206031419020c010b040e06060109080d020a0f02010c1a041b0612051018050a110705100c0909020403080d0b09 71
    0x80103e24050644c2d504a80304e8000d51151000300751400743c01150340c080d00c2c82c0141e11500b03201a039403540b0b00c00d64040381e0089403148c035203059401c810000d500380b9520050071320042c002c4501500d0002040401d0030107d03818400c1c21f02c1d100e100c90035003e010503c0f60100304403e100003a4140900020b1183d046c00d002040d080c8540c610750958020f402a06e012940130507015a4000203411450000307100900901015034480002d0b43c40d004191101804949440f90001b800317100400c800000f400550050030f984481c54440e221003841c91001281000481d11000000820301081036007809044c052070161403416182a8401000c0c0400c24051a100c510082040f00e510981c002414001c068002c80d1646032001d00b03c0d5403180d207801c54220951040d01e0740d0010840c80d803042e0b2247c055440107100d642605081502d0610607144003a08a8000000308541c5090a81200502c3e0f0030034600803021591320014581242c03c5034000b1110131000142d1400c480c0300707a0040480480e021181d001d1503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 778856978 1250 778855728 778855751
    0xb0301060501112104090c020f060a0b0102060c09061207020102070c060519050d06080303040302280f060510050402041701050c090d0b07090306020f03090f0a030228050d1110 77
    0x44082070940201c00d080030741c01041380443e130002510b00030500751009210611b02544040e455829080c55441a4410500019500d0b9600d00501250080603000380c40c264451079040201540b041d904540c12540400c000c3c041c40010465140c41602d180d400141c440a56180c5014411126071000080020500440d824042aa01008820981c1d802c065a9074083c1c0d6500c039000d0042540410000d020100400060603000f143c450038100d04c4000569446901201d03590650549010150001038000342d0500000c0603640b00c0c0360000d00401d80a88060703520300004003a41d016800111248041c2c01c24214090824020350307030000c8a14061500304402080032986116407210090100c070103031804038a8180c0581000350107150030180555640b000c543e1801c180c2c1d8800d58005207544120480100d9040e404a41d180c01c5a625034042e00f0306040190042c3e4209081c04070b030fa41c1008601902600082c4208190343c04140540c41d25101c03403211803011810280c022200782c44072800e19282180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 778858228 1250 778856978 778856983
    0x703030501082103070302070c03080c011d15070c0201031506021f0b060702060a0c0c03060203060f1e010e150d33060f030b06030901060509010803090901090c0e130b030106050111 79
    0x170310821501d00182c840340141040038110741a50f101400d503100024002c1c4480b20190031100c8185101c1a0180c0046000c541459454041c031040d4a564244400130036041441030150f1a12a40140742c08586440b02d20f15441208030254048005640441d14068401901c076000e145a16418801000300e40c3d21130011629510a5010082c403407030000482c5401c0340d002d070f4618849076804c244414042c0e9220300e060002944252085441030314414009031180c5440d008101b195140d0100301401005488019a00d2070b05440310f1960002c110380f40140003c01210281403904030700c000124080505403c041100c2250b810110010b5505040902000c403901182c0c0040721510702c0c0001101040003403c800800205091640c0b044000041c00480441508a102520000c64260203940d07070b14909980d0340e12406c0c02087c0c11640c80c0c40104044d1000da1302c0b000d80c018aa06200228400283c0021044c0e12074014075106d0795910800303d10b4a040901c114070152001b0300b481140d80d054854071740d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 778859478 1250 778858228 778858231
    0xd0b040c092304090b010e04051c1b02130f050a1a09010b0d021306121104061d030a02031c032435070602061f05090406110703030501082103 62
    0xb4120201d100a41ea035122075001c0307102240c0101d80c9a0407561580c288034505001a20143c071181704d0342070300740803c1c21454043c07618640142c4401261640b00b402049404a08034000e03a4000100000180010414040c80c0c1580400481c00030781e524054070700724100c1d80320b8400c600259100500c01403260310b40756000c81c19902260580c68554040c0c0c04500c02912581810b001d4018641d100002c1ca95040000f130755000031103a0b8113001503d26081c8500707540c081d41c801c01d000500f40c03042960700f403440d0754200070780d1140240a80740103505a07000300f80303019041110500c844540319068030f05140d051090503400c00040c4034006458a050b800017078038070300c070b40a1a55028640c9008587c4940d10008542e442c068800c0040c45032507510307907555100e00ca0b07842500d0241c02910001100d1410756807000e00da00413410764840c0351505160510524860040c8201c481c240e4684180c0d400c440070748007400106110381d0b0089074940c103020040381002c1e060780d1420041c646440307041e800a1669030589 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 778860728 1250 778859478 778859519
    0x90b090708090106050a03080a02060a1a0f010504030b040b040203060a02091003052e1505070507290301090603030906172e0306020d06050109080a0303150503030d0b040c09 76
    0x212158880d58005401060103a0200ea809103c411b0300208210088002d0b0040302c44503002d80d006555200c2c01c103825620310080110500d240380c4084991450280322a481d4060180740c81803c19882c2d0303031520510541a40d056030b0700e203021001c0104600e0308214840e480706040e0340035403c2400220210b85d164039583c0b015000c1c0f41d1250000b4a008110074041d4014040085001540d04c3d40c4846940e003a00d6540602558032826030b5140842601400c05c46012685c807900030000c0e1490700c04101241d0341030440700700f0b5243c040c007100300f1b0102032400614040d10a58400289681c5146009403072003415510070802e010099891140440d8051450365101468400c442ca0104038103041c00c0c0359070440a0220f481c1820000088203000981d4054100541c9003d01000042d0300d841c01583d2060142c841c2101d41d030f000c1c03140c4d00b002900c42c1d00640321b0202e6810120021544520010b41103400c5803600c038120301da580350000071071700c0d00c0c1c002c0801e00c095074102400c60f40d00342501517000400d43c1114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 778861978 1250 778860728 778860737
    0x71101050c1522030c0b06030a081b0f0a1a010e060117060406080f0a1a0c0d2a08040606060e0f0405090f0d09031101020610050405151201060609090b0907 68
    0x1412209240f000da205000c00e0071890001c003415140182c90609000d8007643d2903d07000300056198200062520411504041c3c8a4203058800316a01d005040001e500b032003078003038001241e81c4001e0400500c18031910920b4400c1d01c600c4110001a1140416488070802c0d902000500000d80d820804500da145041c5511000300d030385010104000d0007a9500c0301c0c8041c40750522040c020080800d65035800c500c107421824580c6080310030b01e0382c0301c80b05a907002200074041006943c0000c06138000241800b0340c200300210f181c0c07400c95001000d0451074001c000325042c88100001c0007207038481e6002030220f500388a0385084608011564401d14008280e01455031000400c0100c1000c200c00240d14203203800300c42d00410074190048c00c90034280300484045a11005801c00340d030020403014414111a603140361800d1500042201510018107000c10420310503100d07410a803100e82910004091503c008261645492030080c43c40590b984404c208038035100990496a8801902c5500058280740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 778863228 1250 778861978 778861981
    0x90e0f010e011202010c050d030209040e0705030c0d030201090c0312020f06090304150e042c03181005121f050612040f02180112020103180506011e0306020d02071101050c15 76
    0x103a40c0d02c601d46c01c001e0050312a01c6001d02c3d0300d941c160002d200068040d01e092202c0030a801c040f81d61a4010302a46a05420402c83d0b900907003401c4a540b41c100d40640300214000c112500c50111404e02600266a101c001e92101e03124107404000d400b1460b000c0c034004061741d00d4030218440c1c590142d030043c400002d11601310402164490340c0c13910041c0c08010030402c0102320b010301200900c2c510075946070705d00c0c10350034095038800d1011090310603180402910148807500360080000800000ca032280c00e00c201801001d02d51000300c810148101c4100064449900080424503480d044907400303584140c4003000040d00720309042d44c0254005601c5109807000070f041c8d1000801c06a008640d046401030450000691304c1c0311448400c05e940d000ba00c08214160007094141000005484060402d030f00050042000c03001207101c240d000040740d4083c10a0a444e030751254180da0150844404c2d1a402140d40300c18000c15a5011801e44400d080151400108440076925030719080c01c401c0e0400d00000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 778864478 1250 778863228 778863233
    0x1030b031c14120c1209060403120f11120105120d0903060c020c100f0f1e121b180501020706080a0c031d030a0e10022806050403090e0f010e0112 64
    0x1001d5401c2c10407184a8203c2e18540390031842026003041c0d8100301e0340072510b000314a85040104159000b1380d0969161034180c08004240c3d0094107192a5801c20640e80704481c005111240d00035000007006001400c00c00e524001c108001c210140d07030154a69040070207401c40150b049000704040380c0d4481c0f4082000d0510085c140d0170500c15102b06504032080000f807180307141e0b00802d52002c00041d5100c0600440946004641c200300c481804180c4125410520b04402d018100c03204c104555603101040c004541090036031440781080d500350200b12007005103d40ca0140c00d0382e80010f017100784006c001c1140b4012006102100180c0000d40c0160b403500c422034524030a070481920031100c084800321131048010080c0c1d0b6648040441800240e0841980c0402d203002241c82c81500c02c168005e003542603584034816012f03108044100f92040740104010b0004140e0301aa504c514040e4490040240c91f000c618541000001d10002d0050720042c011300903015503503981415070740051050500e209162 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 778865728 1250 778864478 778864517
    0x40f06050a08030717090105070b090c06161e120c14072d0528080609060103030807020109050601060e12071404060e090c01050715051501030b031c 65
    0x54100d1a00301d0300421000c20301d00e800200505200b442080541503d0501c0195080300d030242d2402c19001800c104100400f04825805980c0c00c003240070306880150018400080395072b442a265455a01202d100000601801d401c0711312801e5038100390303010320306030176502c1940305110b588412080c07203c900380110a00c102d507483c0c90040e02c0305004880c4001d4444c56540c2183c0c000001040312518038407480e070340300ca00c0710002c2811290301070003c900c450151603050082d00c5045c0e075115942c14500303034000713000003040040500590340034003c2e0150354154200105010001405d800070b5a0401002c180041d03c00156603045424520380b80001c2d01c1c1e00e50028400c2942a0300505940c802c140c000705180c001d5114000d036019080300c0400c071aa039100d40004103104c084900242c250840f42d20140e4039401000100b034014420303908140b1000c0c20f90300b0b990468900b55001c06210103245410308442d601442510b10f0000100c0c0200440780c1c510000c0782c4440320418802c42000003040841d1003205d1503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 778866978 1250 778865728 778865741
    0x7081b041401120c0b0d050a060506070209070302090d0510060801060b070804051e0603090d09120506060402302410140d090f170c0303150a0306140a0608011109040f 73
    0x6611166503640303001411000030f03000135580408c809250101c00240b900c1c04d07804440038168041d091984a56983c04250029004104025004564004040700054041c03103050740140d080040004c51901300b505550840e84282c200500b0608100000c1c404a10918152021140211200450f601d1803140070780d0818241707007600d42c2001c408800d200c141540402c4043c4044071360380e150f09482d903480400a0303280750526006069074014030302240c00307800e00d9001005640071440b0b528000c413405201941185807103281d4110840011000c0c002d180600d9000001d2403841203003c40710740d1145600040703040113100e000381c0600079940c1d42c2003401c01c0c107401a100d00c000f181400300700b501d909081000503100100000c4622860000c220b8441465080030f5130850390000d4010750840d1745100c00d001c07100c120f030702c00f041d4000b0f40d000340000010307082d014080304074018050742151402c00c90900750903250715800075070107a41000c40140b4910745401c21341c2d001d820112400f01e0785140402408005106 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 778868228 1250 778866978 778866989
    0x40603031d0f0915120619090206070506010315050115090e04030c060e0a0303240501110a05160302010f030608280b18210f0a050c07081b041401120c 66
    0x6210042013038000c3c51151600c0b41c50b000703607052a41c2400e980b01517611a4400c40701c3d4034801c0b030b0b6030082841c5100c0c0b42e0302c0221103c0c405462076150005640b28586443c0c030907802154400c1c406103240403460050300502e80101105880451800d51810010707206c841a40a80c080803181c140010302450312440d031031445d00b83c1203981003200c08400a10341c0e071541c00454080d00400d04007104595a126254800d01005485442c0c008a860070580111a0b22024401c0c0d01894814005002c0c041075043c041000300345414188041040d185100241c041300140c80f0b600c09140c036009007080050170200342000c02034000007a0341982d896420300000000060703072000d40155044400c211341280102801c005d002e02c0e03c81100d402e0205d6113038142c4025520600b2480740310f8284031042e6080604406454840c0840c2003a074240388100c082145890121342c00003915500c011007501000c4010b070101c401c00003054405100702482022006015001881211003003008c4030440c1e03007448284c0c0c603124007812 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 778869478 1250 778868228 778868239
    0x70f0c1401050f091c08180f0a090b0d061514062802030c060f0a050105120d0e01030b09072c0607151118040f0504120c02010201110d0e0c040603031d0f 67
    0x2117485c1042801070700240d000502054029032882100d282901c07c12440040040903440024180400580500030001c4180d42000b1840c40040009145006040c4071501c6801c0040032276213031070600350107260080c0896005810410a00b0204011500021040e600c01510788141155400d1f08900d0b510582e04039989900400040c00101c6409400c01ca004031a032640601c507a0740c85030b041002640103030341511740300d5200c0d445c2c0d101e045001c0d210710500514141000142392280700042945c5000841d11400011456141c0701e05281d000c40e007201c11200b40c00741c11060f110301031000c101346201d43c20014101031040c10b00054500f416412850a0500002c9400d4880650120f0340b002c0c0d042c0c14031124469401d101b00b0700005030991054038442e50b0401d2003400c4d036079440307041680c6644104500b42d046540301c40d12000d500c0100401040d014020000001d030074680c807c0078078100140c400255200b9402d0039070410101c0e900503003140f01030303041c40030791a070114013940060004810a0406500702 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 778870728 1250 778869478 778869529
    0x5062a12070b010f08070806130618030c150c0903030c0f05120a0306060e1005090f2d040c020c13020c0109080901030c09030c1503060b070f0c1401050f09 68
    0x301c0c2d015160383c100d0701080c0c102015540c9501c441394694046006a02d981e9000c5c0b8006140c605801c42d411045600442c00021020b450052001000404441c00d0780407800518400b81007000b050821100c010a041d400c000d1000f072050b00900c030714901d01c005000c12942007540f1090240d24140f261207954440125041c0c07c0070440710703030002d400407070611000c24540240020024041c1081c00c0000304001d00000c3c454413030280c00e0700d49421441015420246a0418015039196110030b150280d04809074029606254005080d80c160140c01140c043d0742041c0e581c040080d000600d03a400351400700d50015480c000f00007000028004d20011020795030920010000b031010f804000c200c00c190070b0740e051201d1205c0341020768071a155071100604000d9205002c01241d182030f03403410301c001030301d14000c10025901c040c07480303843d0009502a144900406000342c204280740040c0401041d9010f012061507841e640040c01500481c40310074441c2e5070004071154980d4a64240e410010503a4000c901403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 778871978 1250 778870728 778870733
    0xf0c0102040e01080f0609190614040803180319030519050c03040c091404080c07030c0b042c040818030a03110c2209110604090e010605062a1207 64
    0x7070b49028440d081060041941501340010007245462084d08030f8002406004d05880f451105054400810b450309a6074481141c4031800400610340a140500b55541e01e0341401c4a20016030141503207000c0c0540e001704110f03800341c0c07802d60342d0601c28922818001069900c23803d65030034440c2100015802540b400c030403c10100b00c40d4011310b02680c00b41d1243e030165030301c550010007201e0803100300c0505040c011002400045020005100940075130b4107442400b41d80e551407400c009000d4000100c10380000c9001d0000c4d17030300f0340751140d4146000042d549501c3c14150321038032000c0024002511698000540c481c0400600f0f4500c5ca01d42c0c07000e021540180704c40e040c010850500130f00e102d03125000b4000c521038903203230001440e000b5018101c124100580344202607001419420740031642c1c0c840c0c1010f60301050f503030900908020603c04a000c00c80850011f000b908541540d00040e1003030b481405066080386003000604214451003c214082219101015161000e1061140030f0240005540c2c0308 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 778873228 1250 778871978 778871999
    0x206030403090905060402070201021923010203011805010b0307140f030a0c030e061621090f030801060504140d03020c030f1005010b04120803070306050a0e16031a060f0c010204 78
    0xf00c461090703040085407540001c02041c3c3c070810310080d0040c0e0100c203802856400c14800313446081d114061041081078202d03000303916080a1501c03440309035400b00040040700100d840c400000d81c8040410026581044130f0000720f40800f41458041141c014440c811007000081200c01012448103141d45034640503602c0c0010f40301c0101c0880c0040d05252001c9241c00c0e00180c00e9005140413a172900c50950701000484000345240d8a4000f00d200483c0301c4000301c24640b04a205150050711805608101420041c20080041e40712408008040004101081040803070402d100011200080a0562420221700c4c2100130792402c0d90502a00d03407190120302001410314440208200140180d83ea43c003c5040b0600844c4554407000a45807000d9000030754010085074000a242030014a5607110804210041115040b094842c1c007100c092084174070860000120003401890144407019010b105148440c542417030450140c0c0300819119050610700c425a021803488100854071079076251070112 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 778874478 1250 778873228 778873247
    0x40f14011b021f05041509060908060919050307061a03100908030c0a1704150f021905032a1b12091908100e07050a05011704030c0206030403 62
    0x90114410300d01410001c103a41074000c00107500100340500300e1048081800200a0a00c1400f08012080001003010083d90103c5050b0300101d960300b98000d07003040000350040c0825044204258044010041d401340001029480b40070201140c1075480c5540c50100d01d0750240080c0103013614108803091a00c40ba902030b0283c48500110304580708000b40040400480e0200300d0302400c0c04008100040210b408130340248004016480c101e1414501440410118003044d09c00b181c5240d003201d613004184401d405400c9104100510840c43d22404072200100318280c40690070034400040005014841d01211030540e10a030081188010036001d00d100f04240e01804c5017800f40d803d40300980c280b00100044055400703104000f0720349401599800c002d00204241d03442c1008501c0b082000c52030341400d00c0103080c3d00c2c01410022410328402c5034803a003061032a81119004001001c0104816039100482d207400090001510000b9115420200e40056820380080d402c1400001400f0030140e000f45a80b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 778875728 1250 778874478 778874519
    0x40e030a0c051b03060f0907030f0312060501110a03030903110307030c050f07120609060207020d03020c092523120403080c040e0a02181003090302060f0405120f040f 73
    0x3180c038458856020850020f9040999801d61310401c000303070345051041d16180d0003900b030804803140e0a40d213540f4100c0000d210801100010010b0220b25840e414a00541c00039060900340740c0d03801d40041c0b0340340395102c00c00a000703020503031030701d04803018980244001050300403901c0540f96959481e00b03000d0305040303000000b1115441101203201800340d022404405445100003020580c0720141c5030070000d0300d8009001d8400960030019070005039542c1500407a00c600c07035005418030304600c10801c807501000401e4880d50840f19412150084106207824142e02020300303014005881d00300c400b10400e014030f00d122649c4c207400550001419140171b44544210b04c2603582c2450340d41d41c3e80d001c00d040d000d1031207600c1c03a64402c54007203058001650081c0030380e80c02c070401c101024804000043c0d44607a0360802c08000c66559583e150070315070306001c0c0540c8044510000b120900b01075403101e66074200e681040c502000003140c13071001d108036003046500a0100c10044040300b41ca40c078a03080c0201801024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 778876978 1250 778875728 778875733
    0xa021305030d110741270906010602030a050c0120030f010b0a05090d1a0a0618090206041a07060c1e110a06110403060905100b01021c0e040e030a0c05 66
    0x500000d60100c00d000c5c08942403600c0a180c41d0503003004100005018a00c5203210a800310840c142c1c540d21400380700301e00b2603c0b92044900c1c490305030554804002d85070f0b51541d00550010702203280c0002c1101c0c80104103151140da2822121903042c0141960300303141c407810100503500380084124001840c0100a00141c003c081c0e40da4a004c5140340c414414040c010900a0121130040e151003004091818091f94400b9a078071120030030062403101c1125500201c0d0b599050501400e503240049101085a02508014000c41600015018040c601c40c1090070103004100380801c02210058800ca240e212a0500101880e540301904161240b40340130489000d9040000c1224400c0e001c415081051802614170a80141c6510010b4401c0d0864040b022070100700010019100d4401d1030000d40c0100003070400550741c0058001911341d0504128115440a6a00f40b07884005040f8824a40020300706151089150404200070341030041d03032043c40740404030341080d0081d0800e03820541c05104606 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 778878228 1250 778876978 778876993
    0x302010c08010f091a040219181a0901230306010216030f0b2a1809010b030a020d090c17060c2502040f020301030f03080903030601080a021305030d11 66
    0x2001c4803101000d108114455034180c1c010007003c03809510150030020b04401242c03000c3c505a010a090b81d00021011250101040885d07403440d50001e000c0f05502503182043c44262b150032886140e6600007240c490301c1c030500042c80080340c1c0c00303070b02100b90703a0710401e94809440c0c0211380004030580003111241c0c00b5000750720456880210580d240d00540354806400c0c51005c82a840d103100680f0000c05200d00c0028003050b13070303d003103512242400d0340415003010965104150200c848000c699011040d002c1c80e40c4100500122550300300ba00c1e40308207120340042e100c0000c545108003810500300041c0012034081d00c0420030940da039540c40001c0e1191411200c2c1912182d410141c1e511442c5200b0104c1940d415409648404190648009600043c008613010319a40182030403030b402030303100325500000d00030000d04068202c52542c0e801b150b441c01035030451509800180110400810601005600103910118074902e034000d100540300140450b25091800c0b400a4584001400c01405c030384122030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 778879478 1250 778878228 778878251
    0x9100e2e3909180b0102121614010e0a02060310031a090c0306091b01090509011e120b04120507120e030c1e0d02060d0c0507060f050907030b061318030201 68
    0x1c1c0958100c44240b814442029800f40100005000940020741103004040750009100740311070251144200c400e018003c80040c0340f40801407000088800049a410455806281c0c03401040c0340a21a1301501d20039035030360b90406414907040c80ba810082c00f102140b41d241c000b2402c070b00250340c41810750404480c0610303100c2e010175aaa05084071300300e485a00c408100c04925118408ac40c403038030018140011015241d00000765840d000340c1200740c090f030485490300402e045a01480c0d00611070b03140e8941c4507600d2030300d62026000c0000c2010f05a24900100c04a000c1d2190341102c03c0301c5e4001d400409001c0c8204401010708001c1803000e0b201c0d22414260860300c0ca048141e07207648140440f03c225a00304140240503074148045001d0b03a20010a20401d802c01c2c0c214003c040d880c5a4035603c0320350780d90340740ca8a50121641145004406440c25040080c42c240c0043c00005481c1c1200c0d480c007a0b681c4940020308030851004904080d28245007a03c0c00d0070312041c4a5031642840303500240440761501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 778880728 1250 778879478 778879487
    0xb180a12020d060c09090e0102180a0609150e03160f0f1206051815160507050309190b0c01090605012709050c0909100e2e39 55
    0x32000c1d500440c42055000000d8050380558501c980c2810040d1850307503250740350400c1340c1c03070600114080c0e5000140c110322540039102034002c120040f01d40250701400c00b40002d2070382c9502c0c05071100340544c1c56045100f460080401000c0342d000141140d4004002240101290b801803040d4170700708002e280c0c0410120030b040710450946989481048142001c0d407101c0d070142201034401e01c99032100c0c0241c402040018041c2c45a2061105210201340c24030800262801e080340721190200f01d418001040059400310841e0020841156503031100042c902c9000e1540c1441c1d402400350041c00104d0150032607040d0400c25074280914000c00c00b6a81c1e41c1002820246031059500803003900300d01501c10300800e6440b1501c0c0b075000e032045450007403051001c550742507800c0d20600c56691102c034520140c1036050013850260b0420b0710160100d5650b0040300341d4450a072500c0041d070010100504201c94415512240c42c04403880103402c1014011001c40000e81406040f2601190f0080000054907014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 778881978 1250 778880728 778880759
    0x26072d06030e0d0302070f0209010b0c0f0c1c11040e1f02070807020616050a030522030302061b0d02180a0b0403030804020d240f0c08010503250b180a 66
    0x30200a002c3c00c44101104034020740c0b20000c100d4080c8003404d00341c03000d603c4080c50140607141c40c0180300e81e610703909080342d441e011016850464681c40300003000c0326034959642c803200810403412104031401861401c1c00d0000c02149425030440d03d030040050b0304000000d0301200ba00c009401684071032002e8036214080c4d201c0c01030091310800c0104441001030030300d04c0003000c2c10300103900c0d01c60502800d035807101d04242c020340d010b8000070740c0420800d00540460700f4085038150000112a0104e2459034041e4913540010000e0840e031422100c3c561742041c6d140100c4910600c030050441d61400c1500e000c401e25218032400d9401029030781000304038a5130201c100e81c141e9415480d0990140d8640d03003000f0071180e00c4c980031203418404e0001d40051b030501103a83c00d485080380d00e0201c0c2d0500c04102072002c541d20380203480c00b0084860010806a240800d1030f9801d030744600c029046140040200c441c8040b410b070b2010002840018180300d200e0011440c01c21200b1003100c13503071089035650580f00c003036801 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 778883228 1250 778881978 778882001
    0x80714030408031f080304060207050f0111101d030325050a02071202010c02030610090531210c020901060806090a0f0b150c061026072d0603 62
    0xa007000880d4134141d0300140b500142d10103074000222291100c00c2e150843c3c101d640090050f900c00d100a000901d0308000700c0741540000e29094070481f800d110bc2940e555200c400011042c1c0d5036802000c28428201180c003440c82c0841c046035070f07904046a40013a280d450ba002c5000400c2c081160b0303603045200302c04844125030300e507006001e014107044c441505190100c001303d052104507138040c00182c0f010300503140b15030015014460114074240c210426500b0050184e1290030041c0300000240112103940d04403107030700404050480d8514507010a03208030480080ba5150b45441d42006a01d5000d000d2500d0240309940034512640c0e540015502e50390140c5281c0e50003400940000c801c12440d40c017020b0038069a440108501c00120041140c031400340164a03131251000821030884182000902d420404804200122500c1e00b8424420780408a0700f071a040c0045500e81d10000c401080150050140725510685200c02c0b9900c07070700d02c40c2c01c0c44a001059100c1c501c0004180340284100c1d880ba07003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 778884478 1250 778883228 778883243
    0x3130e06041b1e090e0a051b09060d020f09040213080c0603012402070e1f0e0c1e04030c14130b010e0402210a02070c09060f1719030807140304 63
    0x641c0c01400c16220540e862407000700b044d44500003580040403440c5a0190103c40c0c000611814401d8041c0300e4607105130440220942c04003c081950740f034040803520482c245410040c1c688840c2c81c0902010b10940100e20391180c00170411640040300950000112251001103c3da000500c50511003140024801c00408448107002c4081c00f070300007100303c003454080744140e6541607110215422004802d450300300b1100b907080e80019200250303801d4240500200e101c12903e9141182e030003460351041c1c0c07484942407058040e200d007640103404141c07805154000e051128050b100c041e820f2a09503000744161040c1c01c03560307407003154266030701c1040040075041c0c1d41e8004100c00c4400b8007010b54808000d1407840350380041c00890b40020710101c5400713805880005a80e513845420502e10035000354020364400f51070464204004800144403004880400d03440703400c411b00d040d800c507003450301103060350030214140f0034951308151340043c00710312030744040d20b0f01000901c0507c0021030038082103c00a0a42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 778885728 1250 778884478 778884497
    0xf1206151704170307020a0507030c0f050306011a07020d05120a14090f091f120605010b040e0712021c0608370f0507080a05010b090402010f0c0503130e06041b 70
    0xe81c1c5003401554400c0c010f004451047c5a00e0351140c2c170302003030795005841030140c0320b1003031103420816041e56004001c200d00030107095040055088058450b03041500900b074000950204544032030300c10b601c101d40c01c5801d4803c0e0440c03e2030032031a1940300c3c40c00c6600252031115140648048a829100d400c034002d020a06098410003d00c051036501400c0380b03c03c400151140701c6c10f400144612800782002031140703a40342c1c0b524507140b0142d8406800c040111002400107000c40742000c1c5000d540091140392000c2184042d0382c1220080c0302c0d100551000c070f21014a8280c12049541000c0d00321107818088994401e450401848142005c5c03100d0140d00303103109903525a640720740088030000350240c0400900941039684035858015035510640303094000e2100d610900c40284144446d1220660304100c0a10309603000810540c02c081d000420b00601c82c0c880410300104000740c860034040d45014a51141c3c81e1116269100402c4039a5807246081c2241102d4000c440c0c40540c0c14444640c5452102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 778886978 1250 778885728 778885763
    0x110c01030f0b03160819050a03050703090308030c07030e0f0d17090d150506030a030c0602071a01060302070209090a03090e0a020f1b0d0e09070f1206151704 69
    0x1405440d40300c0c458040d100d40c00c10ba080e40c3e05000003a00400d044885200e03061801140c2402c2c5040340f0044403a958102c80c16001160010900507102985440c000796200034516040e64501201d400c050600c141c007000f04021019180d008140e018065102d250b02101e000c0100300781541c0690500e50001002c44281001070700d00703000701402d4042d01303491905008103000854962454000180c4141c203680c000101c06000e140b044641010099019007010701781501d024040d0600d01030b0080016500140400a0224030b101e19504400328034070000c00b03969100c0e8000c002e07401500b002ea01c10703168140400e060031000101170940c0c0746d141d2501001c403454040600f0f20304800a0070405415005c0000c90320f000248802001c207a0750311a480364859035001403251420418858040c20303c801c0300400101591003c0303000364081a0340c5044000d0300002d0381c04945101c1c5c086120148941010030101c2ca6441c1d0343c10307658010440f44d69034540c0403504d80304082450f0080d107000d41909041401d9516 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 778888228 1250 778886978 778886981
    0x314070309031a09100b0325170607050a0807030f0603050d17310807081306170a0e01060503150a1506050f03220b04030306120206090f240301090c110c0103 69
    0x103500306e00a05843c1000484800f503034001c4080300903085018039010044c0004100039080069080c1c80000915013031802c0c1c04043c0c082e108550491050060340e00c0023641d0103100f0b82000c0b01e40c0071900c2e000d2165641c0c0e40303400740d0744020084a000100312244850b10f40d6480140c080c911074051104007444440840c0807810f04038040328036808403200412880740114001304000c046031403080000369540c1c8040650700e018944150014410000e100401960050075500c03078a401c01c1c141480041c1d02066074007401d005201c20fa014581500522100208201741b03c805c4511039044d15505004403402c0e070541e03284c0060705000d0240410018040258590f8284000e0355001e0400c011240c0400c201d40c0c07003030b41031040141c003c0b130f0b011002d0000c01081580c523020f558024044082c0101030040142e0001e03100b406004a06400348102c80507010b541d40e1101e0320591905d685203e0030004403421144502d2503030090003410031403414400c88000252090048007401c4007910007810180841600450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 778889478 1250 778888228 778888241
    0x110a11060705010e0d02100f0b06090915030a03030b0406210308270a120206061804050a1202060f07020d08070f020a1205091c050604030c0314070309031a0910 70
    0x2d5541d9a00c2c4a4522401020410b4588104040c0c00a1001c134110b090761506481400391808802070030b1030302040b80c54035510241e41d10140202d80c08000c9607150300100d0482c44640a049034036200b0a43c9003000e05805030b2045490300302c01e0300c0521286440f0110000010ba1074201c00c060003a1341816240480d02c1061465008442c1d9030300e0420764000300142c1d8920010194129050740c2204080c2e03403c00404070781c00c03a0222102d001804d5a071601c500003d10101c0c1d00a0104405a4401c0c0018108141441201c0b242c0341d205150098429034400000c0d65214216050304007060303004042802c86000003004130000e8950f50310202035079a00c60089070242c40c90b0100e401503105d20341d00d107800213000d144a41645001603440a80750802035041200159015041746050b4105180003808100042035059100e50142840756640506103400c03200403407881c0d0000072400001c6408010994448180001c407805110000417003412461036100195041c0c4078128507900c4075040c1c0418030119001350 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 778890728 1250 778889478 778889483
    0x30e0f0618030415050a0315080c133b0a201804120f050316050a021501030609020a050105090307140d170c0706020a030e30060106110a110607 63
    0xb070742056907503403444101658104009021510225040e00040c2c0c1c540301d4a14130b02940303824560388914021059031500b1402c43c40900030717403c400103c40011a075400c59010390b14801000403c02c03507803180c40c4403000004540502040d0075801028111140010407a001030740222420000b420026100808001c030180300c25048505041503000780514542c00c03c0c03080d030050045603009804148014088501c1e03190301010700800307106000001c03e052201c00c00c00100c90600c13075138500c8020400c2e8a816029142c080814104d800040b0030070819030806841203100b40c45180b80c5548038401550280684600160194170070b00d41040300c115040d95410044001411403801000c1c15102c1541c100c0e18000b50440010001689030f800c4c8004020f040f0080910f40302030000c2c4801541c000b030000695580d2144940303000508131409c2107607106814442582031050400003485020180c1c0c995109118000125000000143c001500420004140c65010502c1c269000e900c0342001010380098005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 778891978 1250 778890728 778890733
    0x1202031c09270e0114060d050c040f0605060307111b0904020d03030608030d0b0a0e01050618040f0603030f030f02031b070f0503041d0a1406120a06020d020a030e0f0618 74
    0x14802c00c4403151042c0461030a4480001c40c0300d080d00d41a1600340040a84501e0040500300d1503080440c10224004a103000101d5010400703214003510540030b010309811aa501c00e4000050110032904884282c45050501c4140c0c3c0d096400407610240610504541d2900040361900041c014504a49420000c512a040004100b500d07001502e155420a005882949580352000d03003e916000c1070b41c100420010540c80e8542d810900407815038000c40041040301e20800e4410b0a46944e940c000d00e000140ca410b0400c04a0361b6424001e00d03070f813a52200c03200400d00d0100702c0440e128860003203a12496000032441004c01c58400f0700c440030b501944080e0ba948044007070410000300e00303100a000500004000d4054a442c000520135160400b0341946c00d400c1c5008101c0315450004c200444d03003d1400c9a04114400d020700e90740381820203032103000b040584005a0141c4486030350b030182400d14400d69003003069600103402243d9800d104a0007031880da018a000454101c0c0e540d56528680401009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 778893228 1250 778891978 778892039
    0x304050105041203031e0209090609091f0b180a0e01151e09020d020307120c0e0d02010512040c092018130204090501090c051e090103020708041202031c09 68
    0x1035003d00413600c086c40c8180c000403003403298038040b58950b800000071940d0760440d081814440e070342d9880d021394008610407040610f80d030303035900c5602003480c0000280c2400a2800c8810340300351981c00459805601c1c5250508400c0543e505106032510340000b160000c69490a00d0952951841443e0341c00c801c0161146001c5031111f5180098540600401c01c00341c1c8a09102d00050201048800064a860300e030084180e1561b07402560124600d50580b200c0c00341c216030780012682489101b20100c424446901444200400b0b80c40b5002101e82d040000c20a0205003095203c0c01d901c000540030030140c2c213102c1c5441c0030a41c40000110300d200240508080c8000e42080c0003680c115074000c00c1c181c0d0741c0300b004102609060042c10b01321810b03450300914010a0002c0503400050341160b0000910300810340031000c4e4003070b50445100b503401880303441d1138035603400c01160401107004049000e030166140c507400400e5401094011850a80c581d140180c0c1000080780104503c8607620480d043e1515 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 778894478 1250 778893228 778893251
    0xb0310021b2a010f0e040b060c0f0616090f09050c0c120307140906190e0307031407080d1b020d080c210a090905040501020405030d120e030405010504120303 69
    0x11542084081d200a0084207030100b0b410114560442029050042002007150381030307401071400108034002c550014260610f04081500d0b03000d807180c0150103201700140c0340c80c42c00e00050900d10070705020751211110301040c001140c0c442c0c1107102d01074506c0c900240c2030102c66003641159a11a440380b50342818900072244140c82c003e8071030304032803a080c000002e00544030b0f840b401c6c40c3c01c02c41d000c4041070710f8613242c81e0100b4668410111014041c03011000da00c2c410a101e45200e101a0f04000e04840343c903900c80c10714186d034076805420602e4610901c0301c00204070300301007041280081251941250f14005480b80b116540c440b041c105d030f02588a22080000450043c09440301c03040060040c90703802c1c0c039260309038030045213241d071007202c1c0c00140300d204412644070b040101540c078048804101e50301e592400c0360181c081e981140350f05000340103211507126801003008034241c07015a4180f00244000d90b40a031644100d00520b40021001c002c10b1101c080025055000b0510070b00d800542c481180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 778895728 1250 778894478 778894483
    0x618130905060c2d0712030b150d060e0405060402011b20030d090305280501020406020f1e0a020f060705010c0801080d090b04062d020a02090a0b0310021b 68
    0x301c032451035494010500038640640054900301400b119981c40d010b0314061111102d81e40a03048001744015090411b0440d1544240c0000048034005403034004c01d0722840345541499008104c507a190b0707a00e0719900240701c44100da0310501554100340a40385548aa0b00111556103210b2032500c0c41440c00728142c4005640301c51213000d170f40d003428071000c54602180109400d0048082e4403000b0072034000401c0c0049400400e0345850b04c2c403c2c2c040304040000e614841e171800074210101400d1544040341c0000c4094001c0b4244811000120036210a441d0f21241402074240440c064000f6910a0f04482c00509100c401e03003070170b500014403081c1800081d54406003521811150000001e5509004011b01d28040020b1004010f460925105140c141855214180524481c0c4410402024800241444108801c1d440c00c0b80803540340202c1002018041c9d981c50f01030000324000c840d61000141c44058510a00643d1070008001d002900581c83e400d01c040e42109500d25a511829036030310300e403c2c41c02c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 778896978 1250 778895728 778895731
    0x2011404061d150106031103100605090a21050c1813020d021f08090102180f04020702150310050a1811040819120201050708010614040302040c0c0b06061813090506 72
    0x43e1800740395560400d0b00c01400d42c1c4500d182c0c50b0b1030520034010301511000161100007903c2961400544403240000000c0015410754130000d4170000f12040b502214070000d1011800c1400f880440e071011301c141090052004902000128600703190b40482d01c128490108031440078001004800160140d0b00050a4040781984610841e040c00b05a8804540c02c440c131a13031700081c598002c500344480c0045545604405400542c070030891684440e01903910f9506980354580c002d040c41004a801c1e00148043e5030058a0f00c5140626a81000546141600c260001d8550580c0e0803a000082c0e4881e003c040c09032102c99802c0030710140004034401004200000350318402419002d00d07607105061120741c07020200d80510859051800700000345030011003550441d065860184010b841d940b00c03001032070007684c0009601ca0308040903540b54591080030151540d0080980307050503284c00041120030305c201d0741c038030221888007010b403411403400380300350060090b244101040c0c0d05801c0ea01c0a052140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 778898228 1250 778896978 778897003
    0x3051b06040c06030506031009081b0607030b030705011b02010915051c14040f030c120305180a0c1215090503071406010602030d111b010c0f02011404061d 68
    0x40e104100c2400b8403405110002c100c00c0c00c041259081c4140460340f140e103100018402580c882186408012058085424800390310383d0803184220150002600d55200395070307403c00642841508450b0341b070b000c20080100d400503160341002c98503e001080f46441100001e80c103000c48000300094031036201c82c10f8403049140340d0300e05541d0030701d0220342d600750b0880020240440340b4100c0c100c115005071291040d0059000040050000403500d0b0456020b030003101c00401c0a034505100d000e0070f51301078100038001c405240851a1001200900f02e03950070040001401840943c030003082010300002c0c194001c20700074003042d0510400c15804e0750680740c64141c200d46a90001425405121840d00c80440c070400c00713405400e441d450108000c4d960300406102503078050351048401025182e02d01240c11005030320510900010604101c50300078000701080d040031aa000800d114403d1040c4509410813600d525003050544580d00c80d140101485a142031220700d103c03194041075036042001503100513 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 778899478 1250 778898228 778898233
    0x423041b0324030f141603110901091e050901020705030c0c09010b0a1707050c0a03080906010f05060304080c070e0f060f060408061f12150b150d0903051b 68
    0x1100312501000d0619460100b107407a2400e075000e000003031082000c0389241e82c00118651900c003440820350b00f043d28103601c0b00d0707035191805000010008441409960068200d0f40b28495130303070741c00c0c448069604091440c012001e0f5003001741081042e540c00070350860500340006040c0b4009940c2c543c9540e20052810265034403103041c811061410820541c00350041504042c140b48803590003a00380034003100d900000311242000a200c90784104142c48940740b001e0100c50052240b424090300b071a1050313500351001d0207441c1c0042507503201c030100c0b2000c442016103014603603075440d1a115580d41110300d0200f003d0007800400030f41483c00c484103601481506003d080b150502e80108240042c40080c2c090003001d00344010402c601c000315295030700c9a118807948001001017401000d06070740300d81258a483c0c911000754030078000302c2102e481e000d003a8140c04010486418040004526408082c00f0341c05008008101c00d080c41e68204245c01442401e02e0380c140410f0700c0c854108815014200740103503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 778900728 1250 778899478 778899491
    0xf07140c03040e090607030b0306160513180b09070e130204080607390b060f031e1603170a05090a060512060904080d180203120a0f050423041b03 64
    0x42050003503503007007801d5060402c4030508c3c2d1004691074160040504401c0d0002d841c0380c1d020140100201c0d040241003c6164419075241c901c04884480440e0754140b00f40e2504208130040d04140d103000f80103040700d0300c80d00c203500b442c07108015080c10399100d0307600515020700000134190700800c680c6000300d03186d80f06c00c0100c01c1d019500c40e1418020003440e14090404400c500d540648204e0b204d02919080156003801c2c0d5600800705566405803d42250075104001100301c80794101c00b8505c04401500041d01d15014903c0c004a00100b501e00024011150003052004058855401054070500e24105142050b07901c10020786016038603441800400d00009640c2c01421214120303c1e40540219180560f6040035100c502e0a4011200030100b12542c480c04600b012105c1192003011540c002d044801010441d204948160007155070840400c45088002250500900a5600b5140d07414039800200680f0449140360b505c04640c0c6a410941e600b40920003101a040360804040b10b680b0017081d917 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 778901978 1250 778900728 778900741
    0x302120103240c050d24080d17010e0a09050f0601030c050a0617040221030f0c010b01050a02060f0421090609060207050604090515061b0601060302030f07140c03040e 73
    0x1056080d21081d9120300d84100c400145130040141d039402d080c4403000145000302c2d00203130380600c4c0d881e42860310071020f50a000200d80000040703401d207290142d5030356600703030002c000380100781e40e02030150382000d86071040081c0381084240e020b2115180244112104401c0c500011414004c00781c105413503280d42c40c40144002d090840d0010020140e518207154101340503243c040300c0c0705014000078030031940680c50258440300000300428010108003580d5032040041511402d650044444e46455401e00c100c1340415030040064500060464001c0d0241c0da540601901c06100020070484d071082880941000d428130040180300c0408040d10ba884c203590030304402400707948090b84500d0440d400002d0502403920f821064900702c42e030042c0c0111710b41e03d0b0880d07040703910b6003034200c0290001800b04c2c1591360700540d403060412440300320050314951b91f00c401041781a44001c81d00c241da0b102059001c40d8105200365035140040c60b00612541c00c01050034078442c291ba008d42e200c0003400340c0c68410b0020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 778903228 1250 778901978 778902023
    0x504021c030c021c02010c020d0c090204060e03070801020901232701170106170c040b0a0203070c09110403112d010305010e04030c240f020c010507030b06190302120103 74
    0x241040221325420f01080f640c002000650500e600a0113910482200d0303040024581551001d8a03441c807040d5251520303894020843c08008074a180300340303d403010008000c0c006100f10b807044001070303440c585d40f0100182e407502860280030401c149a001000f03c1c000d4500f000d885510344901b404900d109450000b800145140743c41c2c500b50918a80c82d200400400d50801c12241100340c00520a4407035503240c011014032401164400c006207130001465883c026404070082081c03500c50480440311a49550300202100d001c0c220f1070050759020402803010490f10120140c07400c6004211800201c0307182c80b81503203644048100108105800846042c41da054043e0394003401c005000d0314801d03d01600d0007409025040c0c000340100e001c2c8102e13005540b00013420484001c00c4041c05102d001100c9a1510080d80b0001c181398265233040c02003510640320340240c10380010018030b182d042c45051049504000380f44800c1d20181a42003002c4807081c050321441a0003140200d0414604090810036100c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 778904478 1250 778903228 778903249
    0x15020d0204030b090d1e0306030c060816031e110c2d0a020d0809010207080a05060a06080a0f08090402090a0e01050103140717060d02030a060501050f0a0803030105040504021c030c02 80
    0x241075003017030104568040d440403c6140010240540790641c6801c1c03d001e900078041900040c05941000c10042241c0d43c0004031503000f40b0b0700c811140d5451044010450445100010303881180114440030401034030b564010105403021200c4c0d5502e0044403900700e0f403401e0032215034074005e0104a01e50460b0180c121244500038400c20000d440144085d500044260008910043c1098070209215035264802c005250180c0004011141c0c0380150381007990b59000c04481c0501410305090003c2200d8402095020009a1002d80c541c881e00d469a50060b582d0032042c00650040d070300717009000640d540c450440e4018940c0440d0011194140030005003510819420038a0050032031007401301550780b1480070450000d9680114100e912203100184400301c45001c00396140c4103100d5400f060090b0f603405581226407ca40d10140807250f01d050040383d182d0f40c4a03007600c80d0000d0004001d1b90816401095005100400c0c4000010280030022501c0d0b40a410643c009020981c0607011801c0810400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 778905728 1250 778904478 778904491
    0x171f0501050a0e04090c030c0303030912030603081c18030504030c060203030c0d0c030b0904120f0809071e05032e0624020a0203030a1701050d0b06090415020d0204030b 74
    0x1289012000c1c40040e02c4040c020f60400d0040366100003400904c130242d5070080c0610340c4280d48082580c0c0d2424001d014020b8081d0a603a061501905800118041c0c8140c0c2c0440c0d074400d540c24100070348002c0c07a403881e644018403a20710f542c81e00c5003400413005e01c8903e02050b5100781c4540d500d60341236060000c034020058101200750750017003041c4000c034108142070302c0a00082540124900403103420480160000146a541006049050000300082010018140d440b140c0c1c032014454405001102e00e40f400f5101520140c001180501c40d0540061601480c541750981980c4915030703036008289400f140c00c0c03180300b440b4255000d1200380307440d18208464603694030a05120700350412904c0301d03400802d00200510758900c1c406810005009019071003146400a083d07988034100854050b005968003001100740c01940c000102d1240f0b044030151200d19001b1082c580305550790b10134000030350300c090301c1a210230f1000d072042501d800c9580001c0c0a24001c0c101c1c0507803540d18601e0921400710b4081c0c4031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 778906978 1250 778905728 778905737
    0x7091509050f0f180c100305060909010516110c060a0918020a020706030e100501140a05030f060103020121090c05041b020a0b0c090315010501020f0a03091203171f0501 74
    0x14800001d01c40d040380c40e00003225800c2507113002400302045142010524045400608076110031b0740c46509a481030744500400c1d0392130710403a034900407401c8c01c980b01140d041c00c100d203d526407034070381c80d111703500c4c60110510140071141c0c0030030b0784030004510340c0110f0b0401c400034035951403c0c840e581e6410b21903211150018000e500748505102c000e03403075a40c02d000d2202015922a114440d819041290030080d010303501d000c001658456242c41c00262803062420302500901100040e54240060012040c0d02c90b1805030140e81d00303660044607420700e580000050804011b10800b0b0768403281c03040d550501e22402c00b0f0864a8a42400c2c842a1203100d01c070000c03000c5c52909000e4031141c01190005107543d20003a90941551802600d03800303030080890b02601482849403000c107901d00840b480307040c0c41c1e007602101d0311541013014040d03482d11142d0b402800604001410000c0b4a044120310540910034240b03280c20340804070015001200484118800d90940c10001810744246500c030350142c40d0030701c1e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 778908228 1250 778906978 778906981
    0x417010209191508190504050f0d1403010e0c1b10060b030601020a110a090207030305060a0e060a0320060d0c08010e100b03190908070c0e010303090504020c07091509050f 75
    0x41c40c40c0301c1541d02040c3c0080c4005580050740301d68010460f031844520013442000b0908050500c90703511217108948501900c09d064942e0405406003c504054040540e00646543c2c200b901c0001e00503400390141043d030b0f170244130026485041c0324405d041001c3c040014820a19004128001c0d17403120752045e208424104140801642c0c0484c12008103500074000c4411046000f010032482c1005078015aa118030110b07518040503810f80003076020b068110764040400d6190199115000020b4880c190b20003100c3c1010000a201c02d112031450710b070312000000c0e0200e800f0000c201c40b5840802240c24050351901503402080d048203449014119860b8105914030380b00011280300b01850140d40c04424000c00055500e075203005602520442110041c09890030915103603902e50080c81c0200d440700182030300490000b948650450489030580d0345c505400b80b524007804002c3d1b10107291410b0302d0156120125941549007c0c003004250300071002c02a0070701c3c200f201c408131000074120b940345414080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 778909478 1250 778908228 778908239
    0x1b060302070b1f030830221a01090b100c0c05040e0307080a020303010503061e16030906060e0726042a09020d0f140417041701020919 59
    0x100600d038000d8840a1480a40640e401d4281500d2207544c00203000030000070309150b0101000d51040c5030390342500b4500842105d100314020500c20101c42c1c2c40f4030418003100710031184902c544400c40e03040c0214851180d0035055400085244402d0308002000740d01c40c0c40c4003440e400c1400391204903044030300c1d003490040540c0d0386082500300f01d4403034588259203400311558814824000c0342c500592084446603101d041001c0079403290402d114403071090141600040b040d02c191503117800386100701400c4a0841d42e4415020b003c100510505200301130b62a41000c0002d4150f210b080b01401d0414038540540ca0f000c00c0041c141502d408000200911800b20f802080409800868001340d02c003281c21814060060480714400305080356841c40480f00000040352240ca50080c050105030314070601c140c80c6440c60705800c1d40e0b501601010444451400540460941503902468401a188551800d42c0c0c44043c130b00014404a01c00341c0d1030354002801036031071501e014805c0041051900d00e121507460b01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 778910728 1250 778909478 778909493
    0xa05061215060c150106020609060709092703020a12030b152b06080607050406020c0909030c0106140f0a051c02010e2701060e1302070f02060301031b06030207 70
    0x24022800708180880080c101d03a0390320098940b4840014202c43e5802049041c01c20940c00c00e21604000d8000c51001c0758003104042000d40c451600b64441d443c500d4a030141000080004046002202d40401000c0407a070b0300140d0b0f41416180207a004054200d25400c1612018200d0200301060501e403008105141d00e804081601c22400740b6522900d4144110150b040048030842c0c1201c5480103a5940d07030146100d5220000341c442d19400c44489a4886805a8092040340192005030740f01c0780c070501c0a81307002c0010a610008107000da034142015942071a0943d202500140e4820f001043c04017036505001a84001514084980e140528545004a0540000d041c0e2048000c942d9100308415a400b404045c0c0300c1d6080540740f005204410300c03080803900c144054145100e0038000001680328803405c41d02c503603400d0050a030002e0808420140000b50300500c0200d80d41e030280b000c1c080140e59860080c50007140200d201200d0a0640701548841c9912a00001c041c1031042c441d490106465 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 778911978 1250 778910728 778910731
    0xf0b0301020a2c1c170f0304020f01020c031e0c15120703061211030606180105061b060112170a0504361d0a02031504260403020a050612 60
    0x5032200780300c0401e22034102035242e40c4400000c0c0e80040c2d0b28114001075141408010314024005c0c0b904121040009480c08a07601c40d1003030700940244140081005490314800c8071040b100140121401e0550040200c1d052801d01c000c8645015100a080c1040007000d00c600f0021034021215694101030f6001c001c98980240b0758540d41c64040c0500280c0d0382402540400050244c44c840749a25050b40d00d40306810038500105280240151800300c0d440f07003801000000c0f40007032a10b41c01c2d0765030b080c1424016540c00191500035650314418189080c03181c00c2c00a80d0181110341001001024a030829009a88240c0e00c0541c0d03906082020404031507018054070140c40c00d181c01420000600071280901149440300c8039102c0b0180760080c80256026840713030b0804800c04030b0002502140404d0766071261034dc5171003e905500300c110520300000780a0480c0e5401442a644840f01521002864041821904180c0705038480004c09000390702c0c00002c0d40d0020107040324203601c0c102c9042e40760b4808490 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 778913228 1250 778911978 778912007
    0x702010e0c0d020a032d0507181808180a08151b04150c02220b0301110d020a0215070819050112030e0105090301090803040b0606040803190c0210030f0b0301020a 71
    0x10070000c5a41d52611030f9a001b91181181c5041c0c015400580c1043e40d1650000d108540098050388526040310000d80620324405400710741c40d0f48000e8080c0c5500056501410f0041d42180ba40c804c00d401c0c91b565403131200041d09503100284106030040c10642d044810181400b1017070001c6140d840c0340d900d41902110103484c0e050391015500030180c03200384ca0711009144000e40c01885c02d0300d030365100401001c0000d0700942d40a000e01014803084281400c0ba460318a0003d0304440410a00380e0900907600200004c860a01c101c1d07904440000805090345400c1e201171001600305801d021441005180000c4880743e100410000c551400700440c801c00210400217061020800b40780742207030b00600a480c81000050000e1081030305514198850364411079040300e41079180004540700d810400181c5084e954000021450450a6a0031111000d410505401040b080c0da6040c401601e49890075035540115440c0420b40007150001c1100742c80072601d89602030380c814450002e030340f07512082c0040070340d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 778914478 1250 778913228 778913243
    0x60a060b12070c02011814041a0a03020103091106070309032a26010f06090f090b180c0a0b0c0f01200a03060902040308070308160503011701090203060702010e0c0d020a03 75
    0x1441d82c4016100000c0c0491b050441200440f000120000045484004054100c6d010800c40301800f0052035262640e602254000704407001c00d00065001385d004070001801903291070079403655040055010343c00766004500086086508204011900d0100080070b03540314041c40c41ea00b19440d0511035009688141e001d0982c0c6044110103103100c0c0140b246c1c121807007500a2103034104002c129806000c0c2c40c46000155490814010004010f0344038041800303034065018206070b00c40b2901801348130816003200b02180951003160b8920b07038503c4841801040641c0351140c9032200f8a814500345100801d84040e641d040800305d19591516440b00c1071030001000d222515000514002c800910060304400841840082c02005110645018058080c402d82c2d400312039a440c128400341071040c4071110300218400740014001c4200d9112006407450606000140b98551500001d140100961710080544d5641c49803400c0000140300045007810169109140e1801c1d40c0e001ca401c9841d0341c800a445032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 778915728 1250 778914478 778914497
    0x1d0402030d0e180109150503062202030f032704020c0c010f020312010b190908100c0c050a150b06160206030a060305060a020301090501050d120f051308060a060b1207 73
    0x30741e81c00c000300c00c0140610314020425a1605c1110005040c016031200410400e0400022640b1740018002d200c3d4020880092484541682c40000c0d1034808500301d0303142c09a403210310840da0080018044145a1404019100030010780c0f181c1082800300d0018003450040191000420300040d8490780b2071030030318140303148100c00c00d0201d0071030250400441c01c030400d0b0740c00001d4884454014004480881c415540a1140303028142c0f00c80c03607188560840da421042c805040c84820758001c0102a02a00b042010344840341d0f01c041c14442402000c031754200d0001d04000445285214603400c8030b105035213040c039003010410795001040c0030510080c880d040020014414260321780041c0300840d402021142e02c0c0c1001c5d440000650024011503901900c1c240001400b80b514601d0381c035240d41c1100070f40c60390180381c617000c5030300080d128501c2052010410000300c2d413202e411402c0e40100803100c09001582130030325502003030340c142d5030200d51440f405110b0b030800d0012505c0000d40149040c01c140e40300c2c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 778916978 1250 778915728 778915757
    0x90a0e0d080709081b150c060708040317070807030c0206011208090d240f05010f03122304051507020a0b13081f0c0804050303180f0a08041d0402030d 66
    0x102d2200e90040095401014540170b280010510200c1d808030040b10601406000c0c00400b207138502410300301d200558040300108524a008004250f006030091801c5407540c2e0b581d03030800c0d5120f1802c0c1e4114000544402c20030004a615106101158100344050a0103525080389030783d034040320001c0900700000010700030482d6521a0300110400380e129501e034000d00c903031002c0b6000000b181c0803074945e02410b200072048189103600c5121705070340e462200505000d003542c4a0b0034800188080050502c52400b061089007200001c504d4001c0c03015082c03207a0740340c3c1400e01b44002c1c606640c0300e13000d032000240600001a03a59040440030b47c3d03a4180c083c1c1d200e540c004242c664104040d03001072120f008401071540301c5110040140343c3c600d01801d040c0840f5040040446a540c0c00b10b402a2041e0030904c0031070b200c1c1d101e1580c60301c0c42e01c000030b084580303507000542e015051040e0480226030100c0002020000c0181200d0007410003044903940d1307045c3d89456000310740ca0b0f44003034003180200203201015054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 778918228 1250 778916978 778916987
    0xa030605132306010903120c0b1f0b1804020702060d06090902040608030a0815031608010c14030c07081606020d15090b01320a0806090a0e0d0807 64
    0xd0900030058401c80d540d2141a00080a44840b200c0c903030001034200c40d41036240da141c018040c0a069403000700403451500c801082c0380c048041c0c0300070032550740341c40000b050300351001da4011244038245c59110101a0041c0702d0700e202e541d00c150343d000014410b45518042c0c8401e21020810250f90240e5100c00501c00122584658000030310300d83e05c4d0800c0410354503d0382d405440294806d56040040c2500c4112044c0d487c06280c0b80017000842c041c0000e0190f0b20302c95808010502c2c0a0101e03a81c0841c850140520780c3c95035000710401369915446964180d500840d100084400d04e41960718504080c28055a2441140c001400c411400135618141c0320300c1e1924440d003560000021500c4110380344075403000e44501031002d03141c0f2901c0c400110b111003a52155501c0010140c4400e054968005961001a2204000300a030000c035081c18200b291180001442c210305070703650b451020b10b044800c000401c0b5001d0131140d0b14601e4100c0c15030601400080d90390440200e403c0103501a0744040c021036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 778919478 1250 778918228 778918241
    0x50c04051b0c0d1d010c3320160311070801061212090e1803190210050a0216060e1c1e020327031c020c030111070506131415041e0c0b0a03 61
    0x20042c00d0880007030138800e010b81d401000140d40c803803000920704019890915090084060641c100315249e01e060000901449450100484480c1690302803560303030105608495030380d070289601d11552205581048001c194600c41c24009007442c00b10981456010310021030010a041015a0584811640000100b0070b40c0c101d880c0144642400900981c03000b9114401c40c030313081d8850303424030002c58040011030080d1801184510710011400e4070a8503030101a0440d440c502540b801000d03288216001848028000a0a00d0b203980005c61003000c24000b42c6495444040c08640040c8011010780044110004005100c0310b6910518110140002c2c00c24982c485500a81d45000855140303951300030521b15544801180204640c4102096401744d038400e64500400c1c507001600000d04e089000c4201a1219004210301c0070703207203807407051186070500d0100f91103601140b460800042081d50300d0342d00d005412400c4030301c00501d0643e0b203490843c1d140d4001d0581c10745000c2031541d0341e54440d0f40030380c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 778920728 1250 778919478 778919543
    0x1060803091c05070b040312021b01050a1812291503011e0509150103020f090702280b0a02070201020604060b49050c04051b0c0d1d010c 60
    0x2680f000c5d9840c07414013031a030701510048541007500900d054216001040c03c107483c4d000510350301059100d0000450303171680081402001e0260a150b000c100c4004510003401400c0d405808500c21070351401c24908040020490f01178105080030000101e0215030307000ca4100380204100c0004030f40c000c00082c003400b240020f2090300e0040700c00354441010b09401c02c3d07001b0503100e41964842c0b030705040e4059500d03400340806900422030701454841d5003443c803581540b0000030b2042e24005030015413280d00c2440002083e081009403810290140100d41c4180c07500568401001c5142000d5940081d4071030307900400103003005589488040e51501c079464405555102c0455010034048540c440802c01400244c5850b409104c020a0410220390740705c102104030b422170b0091458031890400c0002030600108100040303615410090902c11070800a024402d9105010b01081200f4103402030005000320b19100009940c1d6404203c6039030000e1260310300c00d4110b4201e1141d0044030720303801040014040403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 778921978 1250 778920728 778920733
    0x90d3f020712150908040b0d05040c0609050114030a02040503060403050d060609181a03120c06010b070b010306110d02070602180604180504020325030b0601030c1704062d0e01060803091c05 83
    0x810506107189c2c4400d100383d10401030651901d031540002c13503000c15140240c03808540d010305010407000000002e1a40f1064241001d482c2070b03100c4000c281898415207007100468004214002600d556003d520094040751078080340207403602280580b01400c03032449460b800e565241002da00c64888042181e0b41d5800382c00c44102b14031028036028194401100c20305140641c400106071485031000b10740120380c102002c480141d0039900d9a07001000c0c0e80142480e903010405c46214829503030700191a07014000c0b000161075415140c1100c0341190540b8181c0e1203070300104000c4c04511404c081d00b14109421f60340001d0360350380b5407003c03902d000d00c0c03112079030f0000c01410f800c9001d1085420743e11080d2449100446865100c1000550503901c1840b0034002040b800c0c0700088030840b1844105034041c1c050240031071050503030440302d4440201d8250050704c200c19218221100b614902403428181140c000030800242b03005011502c85c062002564030800d18043e00b00c01882408a01310f4030344ea0402d05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 778923228 1250 778921978 778921987
    0x31106011701050c0a0e1201060515040905060406030c170c180108070b0909040f154205060714012d02090d3f020712150908040b 57
    0x148801000c01c00c01451460340c209400a00300e407000303805480c41c40b240c1d5281d0003007006040f001c03c441008142041d0002d503590307481c0003465a40e0fa00030320100b0303940c1c044580d648905048407201a40c0c0001d00306030080c0e081c10020800115584030310303c21215081910350707040007090310036401c080e0384420380e0364801c2c10b22031520f2034041c100038582d0490b00751600710b030141d9a0701d241c03031000ca0086001e4651300030758100002c1d000c10207200301c100140c1e00c580162261101e000d002c0c0e9040b19441c041e000c10f42d440242014101c0b000c80a004003110356016001c0042450752401c021110300d003409803d00696002c5149000c000e00003000701c82800803100240842e0300041500c0c100746841900d40921034220101c0018081382e81d00c210b030701c0c085000d001207940845640769560703d02c202e4941c0030591000c450010044111001400d4400c001220a00d0340c200c14200000346080d2180d00510929100c000140d8001244a50b4502d1640d008201c080f40901984c00c0603010b5005d66403103002619070004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 778924478 1250 778923228 778923239
    0xb0909060306070e01141308100605150f0904020c0109060b030705150d0b01051b060619030206120403021c1716050301060c0c030209010b0304230705040f060302181e07050a030903110601 82
    0x303410711080d00b40346800c20001d9a24400c20507d07548601c40307030450780c004002ca41c1d02c0356082030040100d543b0180000d89044a04100c00e803c4900c080019500a50340d07a110780c046107011300080707004180803035a580e5500c4408085c0f540c076108500603c0380741c0340c0da6403040019900035401d4491000c1c01240090000f000f4202e1541c80758001c403542d602c2080e102a80140003048588100c09681e00501011300b8030081d01c0c104c50410744054815010b5200343e0980c8102d406510100b074824030720aa480781c42c1d1f44082c0ca00c407160715502074200c07a06034180903401c0c0c0c025507101080d28112051450980003099103820529022901030704065001a040c0c00041091b203031300350003180100e00c50307501c41c501190b098102400b60501e482100c4000d0304500020400c526050700600c40d003111049001a9469072940025034403548615040b114038550700c10002d010003281e9a0030f8126813199655507007031800b86d0b401012845811521002d00d60f40f440c04a051501c50001500068020411a0031558548 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 778925728 1250 778924478 778924483
    0x1026010e0724031104050f0a03021f080c030403170408120403030b1915120e03030106020d08090106060f1220041e03080a0c0213060b0909060306070e01141308 70
    0x80c1005071120482e184072030034051091058405040e01c2080203418142400c080107000e80465861a620828006002c40075a90b05089400035602e850b4a06103209607408000c0e00d1000000d20701f4010311801c1c401c02c4040303034200940010603401e0f100100e85580d11442c0000380c4d400380000303580c501450700c0308020815405074010405450704032400c04c50806244001d2203d40c19900800300c14603a072141144807e8002d2002e03102100e0044400300741722194490951450704241e20110059004540098925800c90384042c2c0000600c0d00a10000e4103040000e008001000826000c20030700c4403a425461205511841608404c58203511490606031055400c40d001070042488408e01e0a0003c60142d2152110303c00f100e030b00820311410071481c460b003556821707040c1405070382181038080c170381c542d8483c00d105190141c40702240341d80c0ca9a6100307080c03000e4840001c04117070195110009000761213800051a0000d1002440c08512510b400d5a5031099805030301c80e0711003214070400c000304100320701 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 778926978 1250 778925728 778925759
    0x50a090504081c0633031505150a090e01030b160e04020c0109020a0504021c0b061209061e0c090f040e120301051912030c0602091e04051026010e07 65
    0x10101c0b01401e05c000228090b18103005002c04101074004505400d58041c02500805801c5d480039180002e119a501c000c034294031142c070302c800740848001a248045c290404185809401619500744256045641d03100e8a4040544400c14490301030060180b040d1085481c50b0790458042c01c155101c1040349100c0307000c0c00070854104c1c072032407030101c0220b40c0741030510a07100740d0003a00c550308044450310450540200342d82c90030740e0b4121004212110554811350700c003d008107107110003231109246c2008806c01a040c24404c180011011030140241d034501d02c000c3e038809400482e07074007400c1c28000c40080c000307114a1200c0030b00d50241c0d22841681c1c580000156040b50025501000081c2a8004141c0707840424043c89040030140410440800d201d00c10ba10000c51107a040107103040c013141d00069001c8441d48810b003035005507003000c40e05800d282c00351607005041805d83c1c0640e14100080c005281c410502d60744241c000201407030345071030001d4121500c204445016500d81540b690f010540000d00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 778928228 1250 778926978 778926989
    0x50a170403170702040f11072604030302150603010902090402061605060a020a0e0d02220f020301090603050d0e060a030902040605040903050c150907121b080318060301050a090504081c06 82
    0x5005021482c140342806000c1c6a44005140c01c3d140c9100c607a20302701039030091004080c1c2c038416040452941400000140b0146000b90000c10303050300940714504c5a503100400103030190f410030b103101e00140c0301c510744650040d40c11190b00781c4805040b050807850b264894009000c0384540b03424018080450350041819005503030b00c4c40391129002c0140f00c4000040741d4001d400259151226109001141443c0f000340ca07030190110b0564444200c42090b608282c11460700c40b41d43c2c11003082009010444005400d4541c241003408003600c000003411401107131100c01c03d040d141da402004540e900da000d440030b44030040c01003084214a05004055030030803030030800e10744255407441001e112083c0c481480340e006e08001b00101070400700d0440e40403034a40350072180364148034152110450144035003000b419400000f1506c451230326201e054000251501c1c030303004420400040c002600c89008407401e03290100310110759030b2075918180da030310303c07070300906c180d03e0007c00007040c070402000d4014604942c0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 778929478 1250 778928228 778928231
    0x604020a08150a1e063f0f052a0f01020a0b1504150f030614040c05100e100c0b01060e03100207051c050403021305132d06090b070507050a17040317070204 68
    0x710401c24000c00d18546c01c40c40c08040b464290304006203043c1d002c40300e0903201d407064910141079251841c10301440768602d42168405080040b5040c100b1044a00c1c51080910091070648004d44414111440c00303000c48039410b003002c15a14036900c642d001400080f00036151032282c190303070b44040d40388488a4002283c469003070140c4100955609003415010b00d403c01c01c441001c600e0f22007040302001c9001401000d11041d8100e0769826668408540017070846501c1c5e400c04d200b8146880c42c50124160048828000008040b01140c0c40005041c008801501c2c0c00582d9041c640c1052454111480c01d0a0000c802c804041d149042e07100c000f80080701d10a40b01c5c218060254142a0192042103030038020403401c061041000c100c2c100384000b200c1c1442c807044507880c11342c00c030740a04080080100782c0384540c03210100d504000d0140313906680803000d46002800c201c5c20340d5485465280c10303031029104010380201a80c813040440c040360000c0d540b1203900102d00c1c21881510449800001003603105d01d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 778930728 1250 778929478 778929539
    0xf130f4a0a0614010503011112040c0302040501090903030f0203071b150501080f0c04050c0f0310030b1303110109030e12030c01050a0e0c1e1203120403020604020a08150a1e06 77
    0x9040502404c0c00d000318230b0004174100003034000b1a0760305480c0207000b84d17280480b500d00000035841d01c0c030078140030340b040c01c00218a91006080280030f58500b90355501c1018810000c220b0039550114082110104010305030000800710706119030564040300b2881720709031500000180341900010350710409005882600d0021411000b000101c07842100d60b100e0201c81004800e0040b00003000840c1d10650310340310011080d440b52103100314040b08071405812040700040d00f00c20305800c001a40744140e03803000240080b00056030300403d500a6480c4041c05001d0541e0b070443c000001b442580c10005030100204440d140c003200c000090001c400c140c0209014205d200052828461011032502da005108041845042d03800c1c05906803041742d03440d900e404144010503512204001090065001e07500405039800c040c01005203089040e44080c1d2281c0c8144c818010b050504008694844042c542c0003c90031500501d100240d00381060586c4520303d0803202184412080b9400c02d000f107440c10008500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 778931978 1250 778930728 778930739
    0x309031203020906070c0918021e1f11240606070f060c021b1c08070507090e0c042f0a0c150e0c011b0201050306011103030708221509020f130f4a0a061401 68
    0x1094050300d030000dd0480094006a43ca051540040031007a218640844041d192500e81400305c600d0300d01141d005801c00c04840a6045009441d10030210084030500d03125000340c2000492a0186007004025440100c1d0030014001d0034000d90b4000c01d01040300380880307045d0291309500c80b0501d0300b00c50b00c80c502e00526018070004410f10802c90841000110708101c0c02c0c40c1c912a8550888810142082103020b10700000038140d050903c1c40c44030010020541105030010241461081010715041003080c0442d141c21842c540501440c660b0282044c0c0d90b41d81301c2c040100c4083e0321058a4052500c400401d0100d001c0d0710a010920841d41900c6400c983c4410001d00f15518000700d20140804600d00c51f40c9003000040d0703214038500740c03000701100e100c0301170701d004500d402d010300c8401e094542e650112624540c946000b40120000c0c002000052040c0341c13032081c0603103e01e0700320800b1802c244503000c004807c0481c2c421010340040b042211561116498042c014021034140f207020344000600000f10b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 778933228 1250 778931978 778932013
    0x5120301050f0f130e0304090b1017150d0b040b061c080c03090a0b0c0c03070b120a0b04050a06210309031203020906070c0918021e1f11 60
    0x10788000511070440c50030301c4410408402e1105100359400204002c440180108900c154010781000b40d01542d111343c07a06103507204403400c605809004103416001003041c3c1b40c2c02203004a10510740260070105032116a90002c0b25001008070541141d003500d24041400b800740c7e0074174882ca214100e170340031030b0755480140180c086401c0c3e6034071280e00c0704030604d40001e00c0355000340450f0140102103d052062020010703000c25056445107150b004001342c1c2c0b5460500901201c120564142c006000c00340c80c185412010780704400b55032b8134000024000c41c1c1074200d130390044003003110300074000d1200c0d0a04202d2500148124070980e200018000d8040c8600d4034142c603403c24150301610b039208103600d5611a111900c40b40403034981016170800c1480d01941e11103002d0807516016501303c9058609100030142124200c1c141031035180d559074098001a03680c82e9030609004080302e590001000d00e0f04c0440d8141c0c001d0b850001c0726408000c0c1418006502c5240d800707401602c0700403600ca000d14030f00b40c0c14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 778934478 1250 778933228 778933231
    0x50403120f090804050f360f0f06060f3a0b0f0d26040f060c0210030c020a061a280302150903030310140a1805061503040f051203 57
    0x510f0781405200c00c1100c5e00c1c09518800e02d1582c05404003405141074200d9550750b03041416500c200300030140911a800b0766000c145a4800c283c02c44105241c2004a040304011000130704451182c5c0000415000700641032003620f080175940400240e59944440755409210038852200f0040c88103005c0300c1c60401000c0c005e00e103d52501522410032054020180505036044060642d05100c1d450b40726212104404400007c1201c10004951954100040c0c1c02c8540310744c2d840207082001001019016a03078400d55030800c10340e03e09000500000081e03050f814130389180340c0907001505c1d198804104800d00032481604e1301c822140d029814000f802c20f14030300070380030300300003508590404288010308018103203d0083c40c184090504000707000e0000f070700c0c603801200c03c05606a007070344040000800000300d030190103034120380030003000303042c03c0c6050300031000c0c026801103807621030010581740e031941c44115110b2080b02d28090303030740d203082d05002803030852804d801c03203c03481800040050303096040c0a49 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 778935728 1250 778934478 778934483
    0x1170c06040306020c070506040803032a19120f090b0a11041202041107050a030e0a120605061504030c0608100311060c10020d0e06012907050a06050403120f09 70
    0x1e0809095407114002900a00990710592280318000701d80c564518000d03100400042e07005550b60306c0c0c88180400d0400402e004e009041a40c18041e000e1000c040c402c1d59694060072100441c0d41c0c00031402110710b40c8242210803410b92030403604402443c3c084d00700f655898004e200c00390aa4650301c0080c400c85040d03410903200300e08144824842c4842819000c030010340010302c08254610350710507000c03007540181e000b204c0550003072504408054000140c1002004e00301c87d6001114941076a4204850004000a261965410000b11644d03180622460b0658443c1c80481d160381d243d281c0010858498050600410003040004550141ea01c1041c01070b030f40c0c0300c0744494944a43c00d0501110340c0003002107003420701880c61640e40400591001d85003151405001160404030040780d00d00700141038005941d0250301d0220a950303148180c121498110b100d00b40315580c2c40300d5062580c00c282c1f5160000b022241050300780002d16500041d900d08540501e6420400c0700000e484010444000740c100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 778936978 1250 778935728 778935739
    0x4060612050108030a0801060c051f05091912052b241206020304110d060b01030b01110613020321091320030709050904060e0606030604170702040f0e010501170c 71
    0x601008d0320582c1d8010300140314108450091050300030b41c1da480315a5403131310b0a40039600c030204030041e0b03001c0002c034040343d0018401074411510b50312070541070840711038044284203000580c2c400e282007500070380100c103444010850f403901e034480301e0703002400b000040f14400c2191421411080d00740030317103184100e0307403140340c40708944640e69904400b9400044c0f06031086500c907680c9041503101d03400c288801d5841030600280c01800400054100c1c0c2d10340303d007581080700e06d0155810194000903009e800c001c032561700381044171541c03000a03d00103a010007a01c520020340e1110488030480405000c8480707040b02c00714012040c0b81026030403119401e5035290201003c554403101d00400000454102c40d282c80c04071341107034030354002c01d01400040e18200e80d95a41c44a00213545d080070700c00c1980200080380507107043d09241d102c070600642202c98900220348001410000c643d510f5005a496442c3ca480c14400341c01620502c0d07000303100903c102c100030011300c83c00300c10b00400440d01c0d40c40c01800410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 778938228 1250 778936978 778936981
    0x153311030301050d1e1104050a02040311060c0a050f06090c1206270106030f02030706080402060d0e2a0a080319030506030307021f0e040203010f03020d060b04060612050108030a08 79
    0x1c11580d400101000c3d85d4404071340240614208809424103207980c0104009010880c1c503400b40b204a8000608100b040d0748144000c5c000140107a5111013005411070748217840d2840030f00502c2c100201c0c000010308030310038140310006521010903200e00c110410303000d03681700850382c50a02240d062200c20364003881d0000c01c0041c5040c600c035916030110030102d00718240da00002c0c0c1201c41c01c442c81d9801c02c0e2510749805503450704501e030812400b80a0700341e80c41c104400307003403550100d6428000d0901c1940c45540361280214400402c000e42c6a4007000c044141100600c4401c07000400810404074601401c08000c010440f00000000c952011400c0003500d90983c4152101310000e040103010154140001c0240740c0c051b0340c40e51071401e0b030f20801c1c1c0e070107102c0f0030443d10b00075280c1c0c0596680140030b180144010841806211181d600700da0701a10b1000b8a1902c0d454100003c101c40b18400f41d00500d45840030454030750242e002000500e11020810031a45c807031200540e40c0c082c040407500094440e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 778939478 1250 778938228 778938239
    0x15090c0203041d180613050616050a110115030f0302060901151a070c030317090d0c03210609020912032d0f0c03070213140604153311030301 62
    0x314503d500000c404010315141140c0c1070b06034201170040d590343c00804502600c4c0800d11505000d402d0300705c1c0c0408111084400f001c40050001e0003540c8041040c003404840c041543d410a411450440c10030000c1d0700c0d922916441d00e01c110b00664001a40144102000160407910512803120540000019910424078003134031240d407a01e140300e42101c0ca170010710042c80042d014000340d1300990310a44508440391410442c1310060040203225001d40d5101d480807038001c54004000101003505440c0c40000300b01c7c440d515803103400b00c03481250304a07483c00d0800241c0508039806802444000ca842c41ca06a20781c8510581e00c0c0100403910141c684a008510300040007042040e04c84a85052144d0a215000055880580050003040002d03040015444c1c1189012008802d64034040c10702080302020306114070400c0000101050701a65482e100c200c10b20040018603001801008442203602c10156510174403e4500f030316030741c02c8944004120781003074042d00030045403100600045096a01c0c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 778940728 1250 778939478 778939529
    0xb1f0b090102030d0509030c061003080706050703111b0d09030825080408010b0a060f120e011107032001051902090103021603050a0f020d0509060d0204050415090c020304 75
    0x50358014150f01c03080204690808050003941c1c402d4540201460b101c0031550b00190401000800e20101d07001881c42c213100240d4040280c0702c4c45074100704001503940e6801d0040d0001c0904601351401706c400410000140644004000c0b042090f03c010346080c01e481100c161428011030000620014041c010004a0901c00122081040036100c20680810043c0c6034042117078006e801007040c170f946610303c1c510a41007a500178002400a80ba01e00b4007803004840042514100a2030751945070348030b040006040c01c00350800908095850300c0f42d030b92014580740c094214010702240e0005611021100007600d1818466035110b440d030b80302c603000309102b4003441d140254840c2d281241403550a110100c4205a032130025412a44251210380c1d588075050409040300544180303000442d031140800c400a1980041aa040304009035541510f44817840b862034040c2c011504015003244c40c11415004c981c0014400030200c0304200001c20800012080803a160300c07850044104108419402c1c45030480f02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 778941978 1250 778940728 778940737
    0x5091302040b031317130909030908010507030b010813120c06060e010b07021f231c0c090b120105010c0f0506070e010905010e0d0b072a0b1f0b 63
    0x28020014542074455003a05441c1e08140c680122115103100100f0411410900c00c1c801200e410140e5400c1000d0f144100039402058043c034804075807a0360a6408041c00b40000300c000c1c00c2501d00038449840c0a01c1c1c020020882c000000b070024010501007080d284030006107404460b00f0070003c030a20f00d10210280c540100041c0c080f1003295440d003000070307900311516980c0d020300104007a10b40d880095004101019001e0040d020140301d202c40564015038008000d42d14103540140462045403458414840702d0041c00c51140c207a8640d40980d0b5084507030355000041f5600c580e104c0d503038035903100d41810301c860288120103050800c210700140b00d19806240010201c500ca603444d050510f50583e10141090301c16031700c0002240c0140201d045560300b0012020241c5170078a0400014101c0c0d20001d40620a0080040e00e40b81801c00030851651103602d00d0b5001442c141605200e1020405071a207144c02c6260313094031109147c5010480101140c0c1402d6810003da09080940710f04004003980c05501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 778943228 1250 778941978 778942009
    0xf0309031306050702010e01110604170c010905071a04140402072108010609080f0303010b1305190503011a0607020f04020412030305100b070302030a180308121f05010509 75
    0x900071400c0c549084100440030b0030150361265142d04962001520101c09105094103000b4040240c1541e4040000c100740e01c59001408030385285458024054203100d0344d072030304c1825402e00c010841804070018100b4212951050306061556200507481024000c901400c5003001100c81810040c0c505a00504111800307003080301c04510003201d01c9441207a050041d00b0110310044010042503402c107861310700800855014128502c0b64404094491105010701d1241c03036800b040816020060b01039000c084c00303003d41044180004a25a107080c200306204952003582051000c00700000803108901d51828083c05503820103c0e20307800c00c410341010302d10b078a0704a81d00340000900e80851a9240c1d030f445019840000340d40c144449002e510644176007140000344010841100040e90020468004050034908803103400341840f0701d500520900d80c4017410003500881ca4a0481001c4410030380a05c001006903a800f440e030364281200400c80e480703030901103501403216058508209005001600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 778944478 1250 778943228 778943233
    0x9060907050d110f0301091506051303031425060c05040f170124081b030c01120608060103031101050708100603020a090810061a1c0b0102010b030d05091905060f0309 73
    0x10340701d4040c2129178000740d02c10b10f80d494941407078130218180d41840c000541440c0c42d009150030550341052000c4003003440700404104080b011985c00b01800401e5880311413a0350b580c071410a4000445414003004c0036015604181780c40503480000340610700325411907890001a541c503e00e000a400d610200101c0c0d1b95401d075480c0c0b5800f165420204a00c2c6800b1003520640d010658204941c084c070740a580300080e804240b1040440007140c0e4000345410f052942440c1401d503c48400c081c0502600c1300f03078070075403181c41076400200405030410070502008002400810490b0f99910044444440035034040d00c3c42c6c0100300c1c0c1481038500c250000d044001490030112011035480040b580b810845034244289143d0b00e2409009101803090042050150340083c98100351401007601700b241c20036040d07084442d548906500c2564002c0d0481c01c10803400030203666441414280241084d0703c000d00042c40780a1503040c030b1446400d1800803c045d500041e100700e062810006241000c1d03400607203136040b1803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 778945728 1250 778944478 778944487
    0x706051e09030313030b070225050f01110a0b010e0f0f0103020913051e2a01200a110f030102070b0406050406061701060f05010504050f0d0602040504060b0909060907050d11 76
    0x201da0f0300392148019441602142d03042e01e0a940d0003810032710107202e01480309142c03850019408030080c441c441910b804440c40b000f0b81d081400183d0307500711508104199030064007540c4c418450214402da04803a4203036404500e07592444940304001204480030001082400b00500150074000200ca41c031240d031118246912059440301464011b0750008100d90350001003006045e01010310280d0049414420341d00c101ea03618010b518071001400d20f07158104881441d0b1098400e02014424910b29088801c6d181c040a80e401c00311154000300c07252901808500052a071141414030172200d8154100114242e503449680c0c0e1107002c1d08010f40150307072a0b500c40101160f240282c549945404085000000d03601c0d2511003108a014920350060b414030000b40010052911102c0400070360a000300e452603441c081c1407408070001d01072030300a01d80040c900b101c0800d2034901d243c002c1800c0e01040700e140d107155407003108118041000b211468005141030003c1071600401c0d4000c000c4440a0010b06405c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 778946978 1250 778945728 778945747
    0x30a0c09080111031b040501020a03080405070b030c071b1203030509030c1218030a021f03110f0409060b030c070b101508010905070908030301061b0206040e06030706051e090303 78
    0x2512103c03043d0340240c035400001d021551020319521403002094011082c200740ca404000b13911003104003405002e00c20345c04000381c1089020b00500002d0910511020744908007074007032015980010400300e915949000140002512034100c4404403440c6041103105254255001c034082c080140c0306031801c0c40300703101d000c04009042c09460010009500c0807070305c4001c3c44281e040c0d04241054003600a400404c03050002d41c5a906c0c03041680903940c0f03004c51007040c03010030860040005440c11381100d1000b2480c9144d04880d43e00400c00c40d21900c809110590b1224031240301e03440255a01d40c0e41400400c90300001802c031030100396200044109a0f001e81da038070440c0f0300096501502510000f06140010700c10b00040380700d91500b00d2407500c3c01c000e01505022641c5e95a10041c09a0000e01418580c1c0603003000c1912408240c3c03903400303402140c51300c0d510741c120400d100041d903007144a07000318200820740380d1003903081d00c4400600741610307100c20500c24440031980c1d002e81d2805425000030441e2002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 778948228 1250 778946978 778946981
    0x260907060c23060618072a020a2403050606070f05160b0d0507050a0206060405060a17010e0d050f16020406170c030706030b010c110109030b040c05031e03030a0c090801 74
    0xea0702c0d4014041c19007450403100704464045030494200000580d801444249907208101542002d25990300901c1d8220101c800350490500c0440258400300b400d1001c1501d1100030700a8582e803404405100c61068000026002c0e110121007035a040b80043c01084081185143c070040054010404d558400740000100b0104400c01d811510064000264580320701c0d5181c401c0c150710032003a04d0320b14201110100c00a48600029006c240f1468503400440d0840e0355075110880100303114a0400c2868a07200f040364040c0007821034400b8640191401a04400d01980440d001003a0041580e403801564048405100e0305010081c0d0304181d80344004140f0314001c070354035100100407000410464080208152404100ea00070200309030070a4001c51350760760860048151140c1c00b400703400c0400940e00048442412950000e0b04444080c0c00380002d010059032030300c003a15410f40964408018196001040001c05e181c6012030794001c0000408a450780d6109443c01d040c289001070b581592030403101d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 778949478 1250 778948228 778948283
    0x100c020609060f0a091809030c020121060801140f090303070f02012702040f020a05250807080310080c0d080901030b040204181a062b020703260907060c 67
    0x84c00b15144e0701091044441c5990a07841001c0091402d03c40312070241d60003808580fa0f094006c0c14844640b000030002c0302001c0800c00728400c680e108106050740e40354954003070080304582641d1041d5460200306c00ba010440c03610b02c0f542c050f070001c52031505c0c1c02c001100c8034402c0c0c140407030865594040070142912141000602e540b02c10340c0010112555004020446080f01045c080700c1d40b04024610625820400b41c5001da4150740ca000814502c4e440441105c0e000070100400c000c00c00105501003241c108041d500501d5202e5104480300d858455159030303003402c1a0b450750f010304410005030025102d90003e041c44001890086024040d14020400781d0f0170036044441c003150146903a00781810303d071081c80c1c003006095030220410701092001c641c4512642c0c00c0d18510042582a242000c122158003a98a891020086503a41d1490800500012070105100f2080341031603c166104400503100600032180c1c580038100c091b1403e2010f581001c00444200c80c41b43d034500d02015004140301111 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 778950728 1250 778949478 778949497
    0xe070306120b040203240c0a0207080106030b040507080303070c02061b060103120f0509100503072106090608162108040905060a080a0305030c1602032a100c020609060f 74
    0x40e0110f051510401d81021011070302c0076501c0d00840241c6110b1882460f00300e402500d0003030100d40d10003600a00f203042c80340c0c0b500554203540c20003000208128000300014451805042901c11158441c030800382c90f80310950f0448001001c040700b007005854220010903070b0200a03172481c00302c940014005401c00c4c20990080e903552090103052413103150003001c40200200c2904d0218036008102001a6281078244003004c200080480016461806103504002c0480c285041c140e51f41150680d00c40a40800d018058005040c800002800800012540e10107801d13044010126410000d0025071214640007000c40036045e0462500810010300040003c2c00c4011030100f46441c049050110211581c1c0c806517017640008001c0f0b0201f540401901d8012221011595441e25075445244d80b031074115401a6150103000042d1200181c0c40100d0208062200c4486488215aa0411503084240c01c03a040108400114160052800800400200500601a03400d241c00c041a11180c1d81101008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 778951978 1250 778950728 778950743
    0x7020d060507022e020c0f0604050304140a0509040b070e0d0f0c0b0306010c120e100f0f031104030201030518030a20010522020103200a1106060a0e07030612 69
    0x144a20b460341448101904004154240e81c0c49290001e070011201008020303820b41e960104d24002d0120003449003180908401040701d00c282007d0408903281c0d48180325404054031004040917031030410610603021190020302800c220740d1a0384a0014001d4014488000c211400e00d1402060f0b441c0042400312038001d001860301c490032481d00004030742603504420503091080c010803016a03445009008450b42c00031018000c2e818800e0207981c241d07501c2c14000d511220354034041c4541c5a04c610814000e0f50360303036500004518141000c1c1c0880e40c05050021502404002c2800594001d8104541001001c0705562407555041d01c810b041d508100240d000160000c0c00001a50300e61704014111201204000c101c24100780140c1000c40180c0568890842500351040080d6030003544801001c0d40752248090014640c2c4100308180ea1002c000c1c01d01007040034001d101e0a242c0000c64510910004c4c0c8181c012509002c000b5440202c0182243d0405894400114000960018101c000d5100707106 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 778953228 1250 778951978 778951981
    0xe0a05131428152d151203030518030901050c0712050607201903020a0606060210060f08060c030408040b04060305160c05070e1803040e090c060301181107020d0605 72
    0x4180059241c8480c0d040456800d000c0d01d0003800d407400106555040c01303c60f02c03510502e1110020000740c649401039805980581d036001604100c1c00c0e0302d104003a4403030b035010000380c3e9038040110a102880c0c0a138446a130300034040300c902c5500601c001c00100348113030204e84c40a036540e4820f10943c001d151088955801c0201032099407500000c0728100d8200e8441040034444101c0c4110f5540d00c440c51500c01442008505a02454004c1c085a00d079990041818040d440c0c540e00080e580b02c5c0240207007500e01d0304e006800030701d6010140c0404140c544110140446864031032034603283e500054815106002c0c00c02c40092080d0503100200001d103040d4802203001d182c040c44a81c1241100d102c0c0d0000c0c4002103041d000001c001088960036a0300050806400f5129030290311202c412032a1a01c1140c44001808201c8010741c0b24000e1142d095481201e218072122400e10913940400c1c415141d0303a2040081c50140c420858004070035a0001045241c14a251600020f1001500c1038082d184240d4400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 778954478 1250 778953228 778953233
    0x91f0905010b310204050907081501020c220204121103010c0503040218070203091206010f05030304060f03050405011512020f03070f0504050c0904060f0e0a05131428 73
    0x10382903075040103e034076181d8143e1414030038911640b50380d866044424020140180c2c0c400c1a4165000707043c001d84441f4403480c0c000b1020302219010341c1c442c9102d40c40c13000360710815880083e10b80c945201c09881c020800d00d159006950b200c40c51034140e0301e056024400030078405c0050003c0882940500207480d0741c14407410605084400c000c11500030040304000708030140c1c031001040c8290014881924040e0794400b08224190300582030b940707074051403034101c640120030002038040c1650304100224144640d202c00300340d580d10940c030a010214440f80d4844140900960203580e205d4002c0c0b001154031080c7d10f4a4448815164010100c5d012100c0b5a502c251f0400710744c0760071005402e0b4000c05515040ca50b5030140540a840307102e00c607984481c001490b1700f02c0701081d5021a2400381003440003030346800c0b868481031414001c1400340090807001030901c1009015690040303860912049440903541c49081c03040091001584440c0b044641c0d40e241e0070845101291202c000c03001134003001160780b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 778955728 1250 778954478 778954481
    0x507120e0c1008151c38060a050a0b0405011e020d0c17451003090b090c1806011d010c05160f050405041a04052406010807031b08091f090501 62
    0x3007007405c0883c6d074802ca652500001841c8801283c602d0b0390862002d40c0c0d200381c0022650285600102d400c00c0c132040c00026484102000b910540e00c09803a1001001d0070b4803002d030740c5810f07d465414016403082803010b850600902e0b550941a000b016003c40c01c607003444944010358098a200d044181d48402a641c0260300e0802003440080d8101c0013002141c1081e0150307008601e451030300b41c466155082d0780422180a81c0c003942e1000c0c0d0001a6140358a80284a5070701d401180100a00442048100704622406003462600c5488140c680607902802c20219203042404681020b051081d0018044080383c03040007103036212004000c0c14584a41401100d000302d609943c0190301582c1070000f800006021603c1542400c0343da041c0d00907865496040161500300301c1c4011003080305140041000021600041a204120070788a03400207882e1844110100c9081c942005400140c05112801e440d20505045801c540c0480072150885a00385250030f9601c041c1c160000103c1d9248025410040d00307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 778956834 1106 778955728 778955753
    0x40606210320070801020a080c03010b070305090609120105040201022e0f0212011e0e0103120c020f1002030408160b0a0302090d060507120e0c1008151c 67
    0xb00c0e20451700070b6003d600c007040050310302070001e110600b03450103da04075210b02e58418540149034900321707101c1d0002010075910400800640f4a41c1d80c408036159110036102c0d00000d4a401c081c130001e460042ca0340406280c140411040042c82c1c8110b54108601c541801000725024400c0d444000082c880c0312039401400c851207001080540070802c10742040b00e441d086403000691030b4400e455185200b40700040c050881404000304883c8617652045890f4800b512441410f103004001403c0c540121a10b1001644041402c2018034030821140c2020781151203e4410541098800c0a00348180c4c2c0021080c190001454002a110100741240705c030740010040150741401040148400640c018a1201c1c50504103e1001e000c000709080b001c00f600101044240c103111401610a60001412544026018900400c60340c03100b0002400c04031103045102031320074480c130b0a40e541c90131 = true := by decide +kernel

theorem cover : BRFrame.Cov 778776978 778956834 := by
  have h0 := BRFrame.cov_init 778776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 778776978 ≤ n) (h2 : n < 778956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
