-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4469
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:42:55.726929+00:00
-- url     : https://prove2.me/submissions/fbc75a50-a9a9-455b-b86e-3ca5eb3599d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 803597122 ≤ n < 803776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 803598372 1250 803597122 803597131
    0x80304030518090115110f06090703150b090109020a030b030d031a030609060f0709030614010911090a17190f05060c040e0a270b0103031202120402060f090307060f08 73
    0x1040c4043d51704281568110202105410f030602460290f61042d8500401c00c1d0801c4442060943c4e846040518586540364004d000444514076280c0c041c2c0e030001070510616030a01d000500140c4c20764a400124030080d80300255030030425888125658090310100265000ca4045640c000b4940c0c2c0c050100014107021580158440c0e0060b1041c40584500001c0d07840d04400301007079204041e21044015103400a80e5480100b4007418040710400800382e45034071904941c10b4001c10310281c41e540c43c1850b058451103802980c811444002444003110042d0417182c00a00081104c3d00744180d40311007104210340100460310304a05503072010800c0300c00d01039180c10914a18a082c1094281020901048801800c0200c402c0d500d45800501e1616484444441122200148400c5096042c014000042400305402190742141481281c455510845005450121082155803156400c05c1015032041740e030314107108006e100060741d680e011b108840080003103850b20714101a1441010385201070041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 803599622 1250 803598372 803598379
    0x40911090c0a083417010501050a210f090605010302100809190816230f0a06050a020d0e1c0206060108040f0f0c09020711030d0509120703080304030518 67
    0xc0c0c100c0c8a5000078006402402c00071505032040716400304428240c0240c0303003100344025030000c90b82001790000990b5204c0b403004124000980c0c0c8480040d14148a00c1d2403034030000c1c1e05a00f00b642d01d0846064542d5245841c1d00c03000ca5030140c1e0310806000e0b5010400196490341c0d03120010000c602d0000101c844021160078524002e1400541c05511540c10030741d0903482168204010342000700a20850700b1445002c258801400e0346418950007010542d940c2c060020340c0e45900c85982d0a0026002c00d14191850052154620310f07940d200140030007170004000c15800740b100764400c440c139014a4052140250044c0381d003051032400708410301c4981520304159080170080c404c12343d074059600399200380c201041140ba0135003807401525040f00c1e00302c0a05900b00a54010680050a0300100b507424007480315564803015003410180c5510b5840e5160b0003003001084040200d041c110107038004180d00b81c0a4270112a9a6114100c965200702c0301100080c01c009274044440001c3c880d64500a6001e8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 803600872 1250 803599622 803599627
    0xe1302010c1b12060501080f0f1c050c0a1410090b070804080d050702060108161401030c0210050f012103021e190b06030105010b0a05091e040911090c 66
    0x680001e4a41114110058482442e06402a400003000b01082d401842240f02c000f040003001c0c2803000040c1340a00030421240a80c484594540c5400200b6143d0500910302500d050080340d440d144c100005c409507402130000600615901660502c00440d440d40207484500e04c150032580c1c5581452061608010340c140360090300c0340416141e4a04560001c00da04058402c0d4443d4102240c1d01d01800f07426100450506040103002940418158121001c881c212098090366866100782c650b90742c024800005144c10030800c16601c20f4106180605c8a4010340c3d040140d0004100140e603811100804000321003001040407009541815900300c503050b14280c0c00340c1c0141d400940740c40c0c0d40c0c90028555450000400109a424004800005d485000d0b00c202d40302c0c64034200c201144c0484e071141c8254a007500009442420341c044543c00781240e51110318101490301000303966201c2046070134501d502c48161200700d45a40c0300da101100e002d42500c40d09110a4000c021910000402000340745405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 803602122 1250 803600872 803600911
    0xb0c06070e0a0b1204031709100501050303070b040f030908060903091e060304061a0613031208040f0b0907090c111b010516020f2106060f0904030f1103130e 69
    0x80f00c1910201281440036081c19290713400d003119015141c681031520724039884248a800c0500140103007400c1505c0005001c144ea8940030140c8034028244041c082070b40340d40006000500c842031054125101c0d0130078000b4203441e610002d2404d0700441720080e044d8400a80040079180c2682d00d146486580c4a480b80d803011034001092050001500c0103140a45880d90046140c5180d21801c407103800180895841e000e9103624040041e0080c41300303555500e40c02680c650038038890300e510ba214907005806800d1640c403d0762090342d500e100500f00820f6006550300031910007484d0040c1b4542e091700e6a18080b001c20100c0310141416142d11007482031600c03002080c80c41e660000705650104c0e081e41190100d003681c50000c214003000d00341d4510381c0001d02c2c01c1101107410844800d180d00e80024000c50b4050f680b81001e008418808000d4142d20050800004000034440c0054241415092920040c9240c100044900d59006030480c00c222003011380080c417601000c1800107a100d426400ca00d541d8582d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 803603372 1250 803602122 803602139
    0xc02031206150d1802042f090f012303071710030c120f020301050a24050f090403050904060338220c030b0411090411010f090b0c06070e0a 61
    0x2402124200c881e440300d03079001003203615090001313200f07030060030512100c01c0300321a219080c0b007001c80700d01d4100400340303a45698180031020f450310381c1d0015044490300d86c003000040d04c0c3c09840200e074414100190381d00d00300e00300c5450007031402050300391140c01e940fa026a50180b5000b01c02460700300ca28244140800208040300c00340e5080301d500c0d60b8583c0c2c9428080c02e00341c0b5900f800f480040e41540c201014444c5034003c99002a410720030362070500c240c09104c0d2401d13101650301382c49841d42c0080e010100074514903050341c4042e081403190030014134107070461000c44d044e1000c0f9401981c18042c03401d80100c00c00600d51510b031041010b514404c13140c402200c06020856409443c144114141c6106d082e44800020300d600b40305074105d1020b100c065524075105000c07a8007250115030041d501c1c0002000ca00340040b02e140640ea10468070b9a12440760001107540034070206400c820458940400105a1074082c01400049028006801a0718244e24041e00124444c02280d00038480700f00108030400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 803604622 1250 803603372 803603377
    0x230108010603110c060103051509031201150e0d030c03270b13031509031e08180102041a0c1605011709120316080708071d030307060c0203120615 64
    0x14030500b8001040718031002e54024900440401a040b40700d05e80011042c000000354004401840200007403003691404070158a034040c0820740c003070205410005120b400484403400c482d616803850010600883d02001542d035a5042e2010b50120b14040071034800c0c540e010344402e141540f0307644003070850114034448070003494451040b54141c0c0d00101361072603201114a400c03402150000141d0410f021807000b042d0007030454100c114049600d80c1c0c101c1c42c0c03100543d1009003100c1c4042d204c0c60016500c01d541d518400b80d044c100b10241d035600b00408500c8514917210900d810000180d09601c036182451580e140140315041100546d2400d20108020784c0c4c8051150304c0820b100600405a07120102580c1c50300002203403142c2b04500100c1000100700405d0404078012407a55603101c10754450030400c0c1c40404c0282d440340001100c401d208400d140d444a0400005480030381204e00e00140c0c0d45801e030032034454001c0c50300140c00025a80d005148c0c0e41c40c0b02500b0680c01c583c025200940c10000c5500c51 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 803605872 1250 803604622 803604629
    0x30303090609052509050705091c062d0501030b0103080703020703050105010b09010f080c030115020c061308100e15090c030a12090801060513020705032223010801 72
    0x5485464160401c220358200b89416540b08044600e00c81c450428003001ca00b5050301036071803600345030000440789640e0040b41d014864540711f85140444032001d020f85a4501d814065000d54440e1b0610005403440c0304000102c000c4525a8401c80c10a1741e110005030310640610903001d04010060001c07403014066241180d44c4070b5025651030089103801d038201055503001502d254a4040006600b00f111401000802002d90303500301c3c240300f101c80541d9690b03819141d81403070f00780030300040c0030803088000b0307410206600d40110b40300d4110328030004400e64000c449a580b0041030040400c005107003002030f40700c0b42e80311103402c0c00b03807803181c1e9455665890905240c00e9400e00c100082092282d003449081000c0a0103000d845190895042c100c8001d644c1c0a21400000c40d2070500080205040c481c3c01d0075202d009005102ca001d11355881c1d0007a40040d8815103407800100003401240b0780750508580516001c10300c9100984c6020a45180070014a040610300c4003100d520440903a4040c00d138a056 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 803607122 1250 803605872 803605877
    0x50720070e2203022d121c0218120a051b041103150f0301060b1608090901170d2d030b031e0d170406020a021207060c0e190303 56
    0x180c0c1d41051036500c0d00c0803411a5082d1504880c042814180e021400c9001144129482c07104426501410f1101c041455010607250304415800301002c1941c0b0020002c4107c25803040c0c00b030062045280c0c04903031000c2039001040544280040719800c00500302c0c0d1060782c1c203a002d01028a05911803540314140e207042c000101c9850f5661800c90350380e642c00712104903000d0740c0c690b80b285441a5070742c0881c001c2c4104030384501160052000f580c5814014042a00d0400d58030358100390101501c181c138102c60040440e07403404140150a003585600060034004d14540101c40c0498581e526003904103042007420808020707440c0f00075681c020340368070499000c2d20590040100d07600c0c0c1c82001c400602414034010b51500680b5503030007090020041500b00d4007020300c00e4400042c40c0d020180c55007140d000940245440c82000500440c40990151650741428016108001410310328004150721203582141da041d60f880400d11403d91003803103d05001401d40b003421071810345181a460110540c40010304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 803608372 1250 803607122 803607149
    0x10020609070b0d0f050705210105100302030a2301030c0b04060801061101090618051002031b0a0c050a0f030e0f01090506070c1707050112090b15180a05072007 70
    0x43c000b1a900c519185001d10200f0041030405006c001c1442d031002002922101035802c0061a10002c4540b190484100030046264849014801d070b010f50801090403e80c250354442c441e03c0c00e1300e0034142e404041c02201c2411030721740c1103240c4102c0b900300c2032300300c1d03601c11209000500089404c0420181074800340d09144d06091720003000302c0e01408500310002c0ca1942080080d001c04031078443d800c11401d1140c401da902c50801801070320b0403400105c1e07102d103400311442c500790400c458600040505074094030b4640c43c88841030721051324010300780c00e00322246091060541c062550008415070200f80c00c1704c030f030a03044041b280001d20740302c0d040c0103075803080c031000810b0702c10020780c0407a1074003d08034114000060f00504e45400d031544034034407486021a121074a20308100e00d45110710701b0311640c07280364550306071129861445d0b11308034068055001a1520128402c05503e0440c00d842211002e501040f030b45814003004054200110b03c0318045002c00c4d00403c2c11440101303000060b200d000d00c1d600b2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 803609622 1250 803608372 803608387
    0xa0c0308060d050f0615010305090c010c080f040e04060f050415050a020d0f0b01020601081f020306010c0506042307061409031c02060601080606070f020d020f030102040906030210020609070b 84
    0x100720802d2803000415603c01c0420420301d000f00030458910440c10444200d000160f140019000d079071040b00e403200c0a400ca06618401503007e5405944042c2c080c1c40c2150904400204031b000c140e015401c000007c4c40f4410400003000010302402d400420504002d2000f410107940d83e481a20340044c004c2c00241d02c913030029040c2d101e10b50580c0d0b449580014144026001100030800400b5841c98043c010702486001140092001580725400f262440409080340404132200d0000e410140078141004817149a41001c01d004000190146003d000b502c0f241e10100080c861045c0d0407462090542c0c0c012041c2003101c640c00c002c0e480c2c2506000442156074105000000e4100303800022a4405220b50044d1000f0300c550005100d03214100c2a2100c601e81e44404040220398000c800000308816041c440800050420603503400722544007914800d0814580c000280c26a04140c00000d4180c0d034610301001545000d2400c03030b4803c0c2c4940050100d0b810314131031440e241c070228003502d1490f010020302c41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 803610872 1250 803609622 803609629
    0x10509101415130608100f12080702061c020c06070f140309070e01030b011a09060417010b1c06050604090308130809060f0408010c140a12090204110418020a0c030806 73
    0x54503000900740036402d83c281c54401c0500b92240c1507800340054481118085405901061030b02d003901e10180f1034050400050303076405c905500c80321089822210a1000c0c50510403903a07214403281d08810409a242c403005000f107450400028550070400110a5003201500d801c00099035050f88402c011965070b9403010300c007502d03001aa9100f20710741c905801c0008240030403101440d042c1c9007182c1001151001c10b0a40d0030180c0a40d04100e80d00c28420002081404041080040d00c5801e00c8004140c00d07804e44001070078590403000309001b400309903103036030304101440c0b013115803100382203508204403001500c0081054000600151700da1003103e400c0010300144005440341d50200401d91070359460000200e00c2d140c1c00600c43e1403099070074992800c200310300602d190070082c00ae080c07915090410b44a0115554150031110b41001c6a980140c0c102584442c0107905c03115102c4406c559039140761031740c026480b0302c5103007203d0002441408003030070041c0d1080348920516010718000040e622880c001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 803612122 1250 803610872 803610877
    0x30c0d090c030b192318010c020d18140904080c0a0609031e120b04021c0b010f08190506060d0e0109110130060f0905010509101415 58
    0x151007042900d00002c00c2124446000c0c0c030840810201a0400c4101c2c58048140c03005000340f01840c0e210b40c04840d15511564000b60750050303101c0c0b040c0c8640540480d0030390841e1464091000140c0124040c507103000d0300300c1f8082440d03210050100310014503043c95080c2c80e441032414a40709203000f0f400315041c4903141c02980c0000000009039015007100b0724041000301134820301200451850b185020113403402503000342c7c8801c240d40b5520940d0176a500308000421140907204d0b8030907401d00190401805030303d10134601400c001f0380002d5501030f40340050b2404640d800c114040140040800c00c10801038030510002009980e404120f645030a00040c485000b00a41501c8192800c84582d500c400150820201c650040003078055500802c00111142e01000ba040c00c2449038481c401940720384e0b00e01c2125a8203e4820300020045e03103071030602030014119882440c0c803640701c5005202c1850400c01c0c40740c00c40f4550294488043c40d00c148c90030811407030b1039464410b000c804040800584542d04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 803613372 1250 803612122 803612141
    0x906072105090a0509010302010203030f040c083003070c030309020f15030403030c05092b02041b02060a090209011e09020408010c030b04021e0d06030503040603050901140c030c0d 79
    0xc0c00c126059030300303100904a410500d440c43c49001401d0380040c0300d0621503d0075040e40e0301079000e54510b94404a032440210b030007500c100c40b40b07030099031300003080c48060000060040000c1900c94803c9840b030000d41d6000c08080421580200410503c4500b5070041c194850050b450b0401044c0820030340006200410300c81d03074040e00401d650b0240044c141240c1e0055110394820f031820040009800c1c001c403454041c032800e5030340014080481890301cad45a180d80180c2d10b00003440740c020803041c03640401c06403003000e200c0d40c0c403102c4007403a00031606070140074907640018401400c019809071a00000d410360010303c00c80d4450702d440c5904181401c404000c860140408100039075440f56515221802030005200f0000041e00d4078010354524030342030088410300f2038051481003d128a00c017080e019a40001c080d0b500c10740e941c2c00004001101031005d00003e00c0d054400190303a21740740110701e080d04e082e640e50044a10144040090009921013926044500c0d001c050b41c032101080a03a41c010043e001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 803614622 1250 803613372 803613413
    0x1a0a1e05030426130e07030c08010b0c1009050304030c1e03080307030b030703152004031103030d240e0405060c160c03060209041d030405060310091a190803090607 72
    0x3c038045030513401c64541049608540600f042c641c5d441408804948841c13161070001780341900100042d0743d122001d041d42d04541d00c182d031045500118840100c03640c010080703030b845d003012500300140a0707054440c42c0202116070100424600c0c44c02d800040c0851400028813030030010001c10107551007036015048180740a8101d491443c1c487c2040810b0714151010420f2160400e0402000c220f250f040e002104044d0a05542c1401e045543d0b00b4280300321021259014030050204011021507070141542074550080e403c4907480b02c04450500c0180544c0221804144507030601c40020000034013a5488044181c4454981c541c00c0200c0c40c1240d400300014241155100700427003030022039802403500fa041140d0401201e010704101d8000104000b48480322038005101c02c1240d810020700455000b00e912032858000758403910741e9411189020050240304042180400480c00c008c0300c200f0030701100840041c1000c0c40c1056003580d900c46c0c4185640185004103801c0200320000c44031411101050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 803615872 1250 803614622 803614627
    0x810020315130f0f020f070212031201030b0405060f07021908160c05040e0c010914040b0604030305090f1f0c142b050f040303181a0a1e05030426 64
    0x9100d444080c101e5030a450601c41d261404040d413400c941d100f1692820b450391b0a40b400d1004035002c100c04000705c00d003800c2d054041040a950149031000049010318841e03444541d031414641000c0c1c1c50300100800c0410b10810700070070b0103030f03440e0005508072403680202540080441a880c0c501618041c070f1620038100d011111020041010310704005d000d1364411394042210040b042080c650780c1680c0e034142400b0407050342e41400b0408460804084400c400350000c6a0050f070b800114450340e001c1d0f841540000e0010464800c64640043c0070f02011070115080c15200045224100000c180081c842003400400d07203400081024040218000c0c01e42d00d0281c030000f8072050301000b000403005200f03019600740035001800c002d00590075030b02440080002a1b081234190742d0140d1b030407041e40c420740f68454030200e80014082c0b0455594000c044c0c0c600386003900c40444e100090000c042003101241d4042154100c2813419601c101501c3d800f68000c0d001c1103483c41081c0040304484c603080c418101c440b100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 803617122 1250 803615872 803615899
    0x50604090236072f0d050307260a1802030105090606120d0f0f0e0a0602101103160f120c17090115090e070503010203010f0f0f0810020315 61
    0x20030810790542c441c076405402d14000700b07940c01d2540b411200400401c2c61a540e004601d4500d0402d4518424001605054101d014540030300d0080000443c3c80040c400104000165620071942d1001596000c403101200d0b42040031148502c40c02000707a41d030281e40d030b46908410302c0c040316141d001680242c000c22140c10540402500c80030101c440d50302401d10445c207498003c2c80000c03010464815540d4141c2229401101124811505102c0c0e0040006103c40c001c0706542c3c4500582c0204960740041081500626042050741d09920000504030014001c01c4503103509004248107040051a020048140c492000c0c0c0c0c20002003920f005035141b90508600b65190040752880310b19900c4d10500c4000e07a45d80c410303a4280ca0000365448442449100100000c1c17089400c02c0c402803240703c0980f00080d8440700400c0c00c80e0403d074002e044540c0740b04400c1041c20007403043ea00241c000c99040c90182030800800d69642c92121281d0840198004001241c9507603c1a040c0d85002000f058480f07489003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 803618372 1250 803617122 803617159
    0x30b2e1b081b0a0302072108120912090303030103170408030406051210210302101503021302040b0442020105010915060c061d0f011109130506040902 66
    0x8814202c1c500c80d00c585000158035000043c0300101254541e005190050510403e0032110950000304030301a51100c10701c00004a1520181110707e16200d1011418603040160074a007100c01c208240305c0000c100b0000c54243c40210840b81985d801c400c96440c0f001b40480000610700c034950001d01d0500000ca000300e05103a202006001e000c3c2007600d4010651541c4000c11144020f0380314080030840700007454122080d081c60104681c0e40030b401a540201100e659820a454045000c0f056070f100c05c260a01c114500807038409041c2c40e1040c001c43c10700d401c0080d2840907100c1d50289106d02d60b17000f0340b841000300b0801c002c451101c5c00084100d40c04850501ca034440d00c8001d100701000b650800c070002c01c01030f8030742c030070500f000141ca4a1318400c41e24262064521803444142030b074025450348070401c20303103424030356007094444100000c1c81b1418200f44500c0c01c640e03181c501d405034060100400342459544400100c01d4031001000050641c589800103002000390f888003c1d000751700380c000d9040000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 803619622 1250 803618372 803618377
    0xa17030406080a06270b030303130314030721092012010c1b030203160803181504060b01031e0510050a0302060f0c070b0706020406030b2e1b08 63
    0xc200d41c445003043d8903152404000d854417402034444c58840c070083c004014180780b020940810004200140d101c8050010904581c41190342c1c00b44840000c40e14801c16a0041103603121a1500c04001c1c117508000344001c25044140180f100c0700104291852400c840320f0713014400d5164080d030a0081e1259011885030500034209400d445150f0115005c00161030600900250b60119078994180d40101c00300055082131030380040d01148418805270326486007000c082240e05000b02030550701c80c54200403644844001e03010305852030300403105184c0400034100d00160010792018020441600c480d004070001c0044d0700c10036000c001000b402120b00b8280d51b0041d40100d48422400c062a500d44c020f0203440f0489110007134101500b000a101c0341d821090103410810303010000d580451780e45140c0340640e500600d405803803c030350019041003015014400c50300c40800c15200c0c640410b0079100320500711202c2950301213080090f509600019485a1a00800f01017084d101e0003820000703003040b09654 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 803620872 1250 803619622 803619629
    0x3060b0109090212010317070804080a050118032f0d0c0302010612020904060906151e09050f06040905030f1c06050f131e0c0c03020105010b270a170304 67
    0x38031108800b0a0907a00c42c004c441c00c42d4580e1040c2070303850b480e6946a0a0307050110720300d0003d0700c0041c0152000220040000c10041800c1e6004012200031802c02900b15084002101c603110104801940000d070403240304040d0408110506200003841e0b091040e090240d0f52404003507015650200c1e00b00f030b400480501c8094043d600070003005807281c40c0c540d041002e10101961000301c4000050004d14190090f1a0552103104080703400e010121001c1d084210310f801141501101c1c0c2840c0031a1040001e07900000d050018040c059414600f00c52800c40030003520791405162600441000d214007003080311401100325001e1940c5039036444190700701100c0c04181440320341c2032020019041c81c0c00c110352440036900070110b1580c208e03107d01650080c41c1121201d03510441401000d1748002d02445241050f030080d03200c034042c2040e907140090131154140c009040180e020b00080880b2240781810003403a2440381252068507202c000011541034003680075003c0400d13000d0300005088008000350044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 803622122 1250 803620872 803620877
    0x150c011812020d0f0215040f050a0305040915030305070809040603021903170906300406061409070503061c050a050f2a0904022202130801270203100603060b01 70
    0x4900742d400c01c0340c0313149030300d0220401640809480d0315000c001410482e0081e00c40c04400722000b2055450751700700000c00030194040341c1d004c20100160b0409004a500084810718020011800c2d640c4c054158010360703501601d0514003140001d025203c5500810103550000c0090050610104c002c4181d0f54160008403000740b10000d01c0903c02c5c00d0b01007543c047c044002c040500300341541d406d10800400c400384103122100609010040e120b0380c50ba840f40902d00503140840c4150800b00b402c680d0000403000a03010b220300e04100044207034031000ba640c20080442c0c0580c01c1540000300716105084090010341a40550300042c801c10000182010101c0081c006031100025140003500200e030303942412000403c03101d0908981d620300142c40d980d0240c401004201c5d001c08840f0300248070440c0e00000012a6070000300c4084088900030b03040300924400000380b05501c10601030100107940303d0b042d45000402024014219502840f03000b001440401041155075503070306114018110f4040d10501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 803623372 1250 803622122 803622133
    0x1d0d0b160314012103050f04060c030f0f0207031e0206041409060d05060112060e0d03090311071d0603070506132606280207050a020a090b150c01181202 67
    0x207454001c07800342d41221a44c840d40f070070b030428184024003d0303c0580e00440c100b000421015045907082c0b00644090020303661898080c2502c1d180142c000c440f48504c90782030045086020003030950001c4c1400940354041003121419001000c03a00c041c01b102d102c000c0d801130b0701050100d4035540b0440c4a2401d078008840202c0e85071500d0051010318a40000080c016030081001848041d800706c2007420754034400c0c90005816485510510f0505601081d03c800203501d4a0505013490b0703216280710f40d200c202001802030a880c0258584440e460005019504d00e04030001071407680e010700000d0011b00f80509070550322044030a20704a20780080c003036031408070103010384812030030035a041c0e2400b02c0c5550001080c9640700c001110307410600300f4410181c0a08a039601144001c03860020b041608d21880003401c129950b4410032040e02880d03041482c4161801c10724000c6030b901e0080c09444110403802d06070340c0d0bc06820303c850141003072048001042c1d06000c9420f003000030521f4040448505607080c0c50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 803624622 1250 803623372 803623391
    0x6071809020d360f0c0e040f020a0605091c020607020307030813080c090a050907081606090503010c23090a3002130e0f0d050324011d0d0b1603 63
    0x10000d445900040f8a01443e00d00200180d514000f0318010750246103080c4115a507111040210300c41210202c4500910307000d41411410040782081c0038007500d04109040034500c1010603420304285c4207036003a0004c1d002440c0e00b50b49924040301c00241c4c001d02900d00407071300ea08002200d644240460310035480b41d1000050a014003184a00b8221402029040720b601d03150301c808003400010b0310802d00ba0181102c0020510001c01018200525020450034554903203007003d00891000e5120501903410000c030310721760542c402c038034a0380c2c013450345a50340f414620011a05101c0c000d800801e500500fa1240105280001006c0b41c2c8042c51158038100c1c8a101d0b248403000801c4400400070f42103d0040b103190a016910b8000448080307074242140d0b058941811020701d00509540500007148002050107170f40c0e10701100c02c610981800c00510458582c0303100080030034103000000100b0140c081c50104085c0c1d9003109405416410101c95001402c06203901b11005400b43e5110003c03a14005524 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 803625872 1250 803624622 803624681
    0x807030c080a030c060b031f05090d080907030f1a0702010f1a090103060e0a060203100608071403040602030a0f0c1d0d020307031104140106090e060109030506071809020d 75
    0xc08590555545481c07101c1a6100c41c046d11110700e203158940074210445038900c03480b14801d5411007448501040e182406004141480d081003260b00401170020200b1130316890024150040760f0b84030401041c1d401c01410807803901c04550800c5200c103000c14090200d6658150050381c8032001141f41044040c1510312a451044a09030b4055000074641c0b00400c00700d44cd40d4040f80c00443c90900350b644005003651142d0403607208540203450f10b42046410300105602003c419440400c0341801604030600c070200441a02000740010180e070307000400100c00406503001109170410011051110714203150b806822010110400c51000d0a107104038850303840c3c460b40f882c0e440d0350082d014044080c11038a9100050b14030080b9160419142e01a00190000c0070f04080d00800340c0d55248811642443c0301d0700000600502100d0410130640c400b4004503c0c0411411340044450804010000010400ca40006d2441c0d111a40551020400341c8101070b958001d034400c0388a90028403d01c28400580 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 803627122 1250 803625872 803625883
    0x609060e010c060c0201021c0204170307050622290a0c05180a270501060f050414010c050123010b1305102a030e032b14040807030c08 59
    0x400d400100051055004200d690b440300c0960006840003500d8000b9401c0c00717a201d5801c2e003c85442d06640000e0800c01019003c0c00c000c004a100006103140c5091500c5150741c03401c1c007900144507400080c1080d0311140405003041e0402e54041403803c4044030622008030b502200d036151868100b05c810000c0c4500600e4810240d806459844071804c2201d02100f04440d0103003128207680080b00d00001148a622550304034005d0000c2c0e0f0381890b1120346081140c2e040c3d41c0c040e0702039400d00010500d01c4000c2c070717080750139101941c501c0d07031000320b0005441d40121103031710381c00a01030b046510b0401200d06c0c1200c0070b180f00381541249002100541d80e64100420248643c074583c50b40a10f0310102800b0742c0c5800319462440281350316018403660b005520322032002c030b0030f0b616031400b90001b0f01c02c40007056040000d5100303200c421005046981c2001c1120b201d10310351200e00003e5600988191440079000340125501c00d159007469075200d035101d0102641c3e800700c41c0030545001140721710015a00400141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 803628372 1250 803627122 803627147
    0xa050a050402151c0e0705180606070b0402240307030c020a020303180a090c0e010905010e1f021504050606120a050c040915020711090a060b0304020f01030209030610060906 76
    0x100848003034450501209500700540c00d00308084000300b5107541304880d000d03100a00c541c2a0103002c1c90381c0b4100800c66086075407401117101007902c10400c025580c800c0c013540c138000c0d0400c8919500d5500c44c80001c00b90381c034955030a4004c5165000c150700505030000a9841a4030984040099490b40c00090b070365011107400c002e6243c0e05c20071541d031075440a40240d0b598088094030000310180c81c0c0d00b40b8011380308a1410100007a201c404101120b40e400000a0b004090a0822161807004140030078545031740c009040c200c00e900048100b492510030810501104441c0a1010701e07414549400c81d00c1d09000c0e03c689104170f0018258000250000c19480c4020f0760207401054100a5001844080d2800c81403d5807074001040c8405901c00460008040c0c20340b042120000303020064081249050700a82190f105528004081c003c945884003100e81180d01102c0d80c1078006981c800481c0070788909881d00741c15000b0038007808440c1111589400917202641c41e0103419a84032401180c601c1c14651 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 803629622 1250 803628372 803628379
    0x23060a09050f21090420070501110313110310090b0f061504090e07030c0e0a0c09050307050936010b01051e090d080c031b0c010c081c0c080a050a050402 67
    0xa0104000c0144000520700680f028102185074118026001c000311b145c5080e00c500d81000160724003c004082c443c1d0f00c1e1840550000030700b1400c05c0340e0444503000d04c800005244414080039040640d80800c81c20b003105c21480780a0003c40c140346007020380c40400342c0c4d54400d07490214002c1504c520302100b0361201c280071008030a0030301c2d144c03514039409418a41c00c0241c1500407500c0c04030100b40c80f0b03e411009481c3d081c444203003c4c01c0c140d1000f000c2b5000189880d08000c590740090240750303000310b989000c459044901c140140c81d1307049240c900d0f983c0b00803908408010b155400701c1c21400c0325a940100c0c8940b100030858132624900669131842406203009c840c09030307040e11140420000d806080d180501500b010140c0c80c0f1552070192355030055455501c01d50001ca00b071040d40c2c00082c648001d548280024001c0840f40c0ea0010381034880b0054000c00400021402120078a0000400784000040e8002444008c450190280c690403065844d42030aa0078000010020a25030080750300607130303005c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 803630872 1250 803629622 803629663
    0x141005121b060711060d0204210203030324040c0305010614211f03060e0d020f07150203070506150f10200c04050c0c0d0f020a23060a09050f 62
    0x120400074281d00111040724a00c5144510084c2038a80101402a04010290043e03403141003403c08815038030360300f400a074000d0702d0401b50390043e1800b0003038981000b401081101101500e44001c0d25101ca1004941d8100b0b24200b070701040242d250300302d941200c2e080c2e111000402c140c0018a042032107621030801c45c0c00c2c5003051003030000351007003403103980f0146400200003005466101045855801d07801503401940ba044000c0c28544288406004420240000d0560309070300481e003500c410162140c003a10a01410240751300c280240202c400403079200c002c5d81d601d850041070844185558401c014020f542c1c42c808038006042a03540074038400a69110342d0b82c242a04c000c3d54614201104034a070090088039440e407150340352402941d00070324144200b0703610b54600c65002d41c9410055030b4000104a440236040303500035008104030411710b40169107010000201c1c8000c51001c0c2800500103054801d5800704030113100f07070360b004609a501c2041030720b540318035000001c0d946221402e034114014812 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 803632122 1250 803630872 803630923
    0x105100e15090c0909191d070e0403051201030b0f16080412091a0702090f01030b01030f080415051e18130e0a080711180601030f14100512 61
    0xb00306501001c07070b000403440c0c5800c04003c21013112040da04209014803540002c986841903001c0c0b540328203e040301c903640080c2c0e44036035a5651044d40c852000310502a20104040c103102d20226400c264030b040d43e100306540d403481c2400300024229040c04140c201d2a02162160f01400b5400c0450446035a440b00e941d11107032901400380c11003480c6907007440241407000030101103d11032011029600100d2b50749840c2e840c014803040715001030496210411000040c00000c50780c80c2c050341901d03000100d0034106540b17486c0580452055800c088036580c01c1041565106900c60000c02d050f0803002403000384180403179609038850040004205d407090241d80c0b02036180c14007404084110101705000304030003031020221070a09100030800e440441d4006489000d101c080001018900815140d080515481080c1c45406490181c140d9041540b1026203a03e034280d0398101c0c1e8040880000450801d041501c011820090580700300c0307018103c01c00caa0483c01d840462401d0b03c81c03e44651521040c0c11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 803633372 1250 803632122 803632129
    0x1b17061017060307080f0c04110c07030b0405030d02180316030b06010c0f17071a09030703030b0f10022401080c0d022403010302040623091e090105100e15 68
    0x1000e15805119800f80003585990400035030303112404d05e5014007800381d030007c00c2c4401d44e02071401d07400d15050200a0040000030018074202141e82000d004810354503517180813415441540840200180045128038205090f04802d400800080b0225201200030300c00c0004915400d00c0054070244038000042c4455010b0035030365010600c14496206c2c4c4401959400707640d04550004415281400318555082001d4284551940300c8140c010103014588010240e540e0b03c1400030080415072074440141058452545000c12403200520300c080500300c80380000d607100320103520b481300e984034440b1600d40041c04003585410b0300c01c0d04000d04500b01207041404204000041c04913044143c03241c082e0710420b00f840008140f400040346003542c03540740d8010881614001e03005101e010361449444002e140e1240340d0180c51503002d81e0303540b103980d0b164919103d1a905200115000348105000c10001c446d040d84828480e12000504a1001e92101d4401c40280001c44d40e08282007901202c1d070a0074038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 803634622 1250 803633372 803633417
    0x10b1201120308180703060e0106170a05060114010509060c0a1b05010905090c040b0d200f030414030d230f0c1b01020f0a0c020f01210f1b170610 64
    0x12001300071548115502d0391002e00701c0c0c01c1031000c00c00f10b03590b4807000d202c6844500c0407101030b020071070f00034402d10300e07180c070345644414041c454800300d861121401c1003540d0081040e504c042134005d002c1a100c80d00513600e00c0d203d0201000840b0300f001d070b003206410184001800b03901130380d4069450140d4603081006101052a000d0014001d04c98107200000e120b0a080b030007841081500709000c5070281802c0c0d248a4a5000030007031440440b070a00c203114240414405403507016401540c506854901d03001d9590031445038690482540d03003003a100d00b03004a01440541c040342c08805400b001070765000c0706516144000d4800354406141008040804c010203401608603803401c1b400145032a4805d107070300c4010b500c560b6500d03020690681c0d64805500d040c0074601200e440c20f003021160802001000444901c0c80b400f0300454a5a45a0209900c070303503540641b84a6005401c4189821541103018103040c480002d1200d042031b44a000461030f0510300b000138082d0a0703075201c030352a801c000d075140082039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 803635872 1250 803634622 803634661
    0x19110315040e1b120a03020f1614010f0e060a0201091506060c152d0f0c0206060d0f0c1e080c0f060714070609180b030c04180b010b1201120308 63
    0x40001e0000300900c600520a05c01c4a078800c1d001001002002905542015068903a032030108450145c108814110020400d0480700302b46010b40c080f01e0162004c0da200d03d42152400e412070004110110002d0b0150b102c083c11500070000408049090f503909016034880380150780020748841c5451000403942510340001c844507000200d141d031101080d0700019a42c0d490305a04140c1070789400100c040c4941b18140316026004410b0066207602e000282d95580702400860041c00d80e0700010381800b082104100300d0681c40f04c4a050410340da1008400c0803080800d0ba4000480c150000041c5140000f911110074078000c6c1c0302400030300b0312800b001141d420421043d01c02c44511421040307945420710041c1d000e841d6680301c0191040c1000f00108000c40c4032030035a4540361805091303440c9a60001030b00c650307140e01120b020900f00040c0c000f41c40450012040208996074210012482412100c081c1600b508018030b40082caa0703a5115000644041c118043c01007503512000c40d5600b01e0a00c50f031001c0b07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 803637122 1250 803635872 803635879
    0xc030c060a05070f1203110703020d14040b030c030108151b030415140a0b03070b0301050d060b0d08090f060f0d2711180403080c0319110315040e1b 65
    0x144083d07038031250400340c42d0700c00403210040c4034809400c0c1650588500d00030b20062003c0242007024554020355600700c0714a01c0800d1000c0a80030721005004e14085a015010040d0081c0c1c90781804007481009030028010784000f40690040c040f8420110780c041485801034020f000070300d800081e2215940d0b880544142c0718010715810160340704000d4007404030190f2031000c42021914107502d990b0100c41c40d442c07005200e40c000d13410403c4042e0b103160070b40707055802c11542580403900314600134005002c41501d131a000252755024134203026690b0043d15503454299201c081c07006503001004072500c0f8207000c280051405100700c81d0800c1e401e900068000c41c1000600c503ca6010400d40380a100701601e040794030414003114190309051240c1200c103180c440c940441c1c41802c0c16600030b4240b07a00100652400400800041e552f07825000360f104c01c1e1000c5650402c02d8900303a0769540340030b900485502c10180d40842460784581000d1040350001c101c924064803102640340000c2141400100d043c550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 803638372 1250 803637122 803637127
    0x1082701060b0c1509010b01020c0402030c07060e07030b091623031609060b1602101b0c08010b0f030d0c02040b1f08070e0a0905041e030e030f0c030c060a05 69
    0xd2072066007000b480f032810741c40f008114401207940300d140c40c400c0050040c90746034180000204039980000b8039130701540c011200580caa940c1d800e105034881c000d452000d080c1c24242081400741680c082169400d59000703900d01e61050b6900408195540c48210002c014101003000c2003108009580c803203050030b41c0c4c0a4148090b051900000792404405000c90011008a044204085280c91090320028015000788504001802444146c0d400400300d010340034242a04000502510503180e2401c40b9001d0141100040403078241080005528051010650b18281111001d482c10015850140c0e42c024003e2420560f00f40d811107903001000302c00c90300310b40c0f0b030811528156070341c0f110400110303d00c20b02419840c1607600000c1c42c501c40034000c0814031207214900400341c2c960210000c242c0790f02d0003012510751210303d814003030390b100e01e040c00c000341d8103200724001015800a214080064101c00312580003012900c105d48498030540c031075626074009602e1402c5170a021024003040052401c1460 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 803639622 1250 803638372 803638379
    0x507120c1506140f010e09010b03130c03080910030b0307061409090a020d060e04150903050c030a0329030303010e060102011119170c070b0c1909050f0108270106 71
    0x1801d590194200c41c0d0003e40320200c0441e14100b2003a0b01d68090000d06c0c00001032407030380010813100c11040c01040d1800e90b0000c0003c0600034241d030003a00c460751000c4003402c200d980c0d003003001c0260003940c1075078420782582900b44c00141c0300740140c14a0020081c054041c0600e048015a1001054500070039100313014001d031a1569035400810f4403c1d07441e5400075031b40300d402d03060078011940d545d00401041140304d0144030224940c03071f180149030006007500140d94495410300b17a40c28050100e2070a80d9200c00680040301c2e0343d141d000614110859041c09030594510742c01040907000d051031040d05a80203000401880441400154111b98180000100394081c000d9190b09a4400500e0b50b80703440c3c0c50032824840310b5010508051600e02030f4264501404c00c06d900748000e11850f1400b0380204401004600c02040303040440318449018204101c49420140000d406100c6621525100e0283c148040d48154001c0042c54864032609400d00780318501c10381c2c018005201410050131541da00e03040031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 803640872 1250 803639622 803639663
    0x51c02121504060507020f060a1509020403030e0a08010204060e0f0f0d03050c1504020f06032e030303061a09100207080a11090601020109030f031a03100902010f0507120c 75
    0xa100e1000c0201041ea801d00d024280141a02d0016001000b1507000480c0104201e01c00316100303410842030007002c41d442d01d50f920840c50b03d00c2c3c0c41d04491314051000600104141c0c00c1056000010f00950340c102c2c0a6603034554207400c030b0140d4418040401d0940402d280c0c68500b500049885640c0140400280c842c2840818804811840100e0104c1c400064121000008000580d0301c80c01d407801c040c02c0340c0b07800e9010605990690b08150b001d21408000f040301442485410141c244102c1103001a54044202c01c5c0410302c1da900c030550200340303801000314801c85140400c0c0140081ca00c64285071150600c1440907140c9030711703e020114020048042400c5805000c0301080354080c101d003e2061351220100b1541240207005c00c1c2c1036a2520408200107034100201c1d840c04489030500241c0a0b04c0701702c04044091000c014542d25003d2a448460910105e50100d00d549000b070b82c400010184151054400e4860700101600b07200b003e11421071480e100f801c004515900c284200d00f0b1004058105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 803642122 1250 803640872 803640883
    0xd09141512041112010c1704031b0320060c07080901050c030310090c081b0c0a05100903230706050a180507060806040603150b12070b0901030510051c0212 68
    0x1252240a00029160145010001c4160a13070745140200010641030b00c024000a15a1100302500d4601000090a02d801000740840c0b100c564001c1c1c0035808094a00100500d0b400c84003c81002d05a002171802d0840000d61a0310401c102002189001c01b2920b8020041c0c00098080b030410000300310340054000c051010390b00a02c080d0881c0002581000c225400f0748584455000c1080386100800c03403800c182089540d141c0e181528407955561028a000e07003032103244000075100c0e110741442d087c4404400d50003012414042c0c1d46000c042040300c01e040141001c2d070b080c8a03c00e00000c2c000d920100e08281d2005803c2101c40c200010200668185c05200d1030000909403216080b1940401c81e0035080250590311080c21942000480d0a5595038084c00b59130b9004544526a504030755043c40e1140c0b1039010a8942e40350445510f00d580d100308070f1459000410080c00617007040041103000e44440c50782d4040d0f400c001d040300705840030705140040a40d60004213aa00c10184000c104c801d042c140710 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 803643372 1250 803642122 803642131
    0xe0630091f090f05100920061209240a05100503030403150213090213050301050c0d090c030503031807140d08130302040606020c0418030f05072603090d09141512 71
    0x1c001c0b034114501e09007985001251013420140700d58011518042d56509811a03001550400030b4440d40d4440cac8505504c5c02059070740840800d034040b1242051450402d803c1403251020510500143e0740711024841d262400d403140a8059009000600000b400f91040010440c44007000508040c0d903440f196450000d26030100c4080341d800256850109a82107200c805408103800900040c1000c04403680f6a20411740460750440c1c0c1d415035541045030543c16100119000340c2280e4480c246a00100aa02c012042032403462141135400101240b602d010b1080e400b000400c42030400d00591144820b90b4015107848031076103180c0c01c0100050f5990700ca100080c051590041030559030b0007007440103c03100d111203403580c4401d000351100042c0d8000380990201206203802c90701e0b051a0720f45000108030410702c2e2003440100720342120502000b1000b55100e070403c0401c0b1a42084040c0059400c91460300401c3c20140020040b46002d003071020b0310a0b0784112070364106190000c0112140c0c040381c2c0548 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 803644622 1250 803643372 803643403
    0x7270c0504090509010c050409020c01060b0a02010e0d0c0c090f090f3e04111c0b09070f0806010305070507060f0903080108070f060e0630091f090f05 66
    0x3070034444494a8440c140d03118101e00300070000401242c01c040c00c680038901c10030307506680010b11001601802e41082004010705401c080e02c44030441d5019020700503240c8144541c1c401d00002c0c00b510340c8103440c810700c40b580044200e50b009003488000000350200c0940a040340362901c807100001001000758051060007117803280900d03940e10080115200400e0072260070210b4446001c8030481420540301461141101c000649000300c030180070310380c0203400790f1412101040b008078400300c071107800215800c4400c50b030b0652250b5485d881030f51062603008000e000110303107900052095020b940308030780042e042d0601d5400c080d0f8035502e110031340340d017480c0140b03050741c540d402d4004050304914098050810790018010030340c20440c0c401144170182c800c4000300560100c8170072242d1030b000b084031200c440700205440288001142d840000d80e072050303004211200c10000a1396801d0124040c90031420321003400a4660030002c41d20f01034460382d0300c1612031040010b04400010020030120800d0314031103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 803645872 1250 803644622 803644627
    0x90e151009120209151f1b1a0703060e040803100501410c030c10060503061504060e01082a010207030807050106080124060504030f031d03011a0a1707270c05 69
    0x4010202c0070074682182d40c48a011747e0340030000740d0101d5440310280c0b250810941680c1e0343c4000f20040d04141e842400c07000d40c1d030400d010030711400700c0040d4881e000c0c8182e5040c1c1142c0d50f0313004550b204400003035000103643c01c6018020301d500886070040c01c1d90402c0881074421600407680c0e0282c0d4480018101264030020383c00c41410818003400228488401c001c122241c5040c02094548000406042c600304d490b01184540d580c6a42c04400989101c0e0b407030420704e60b1a01419030307032100c50701008a01106440d008292603900303c1e01c1400c0712a01a40039050080c0307035035607500c0309400c90303c000c0320385540300c00001c102007009100c3c00c848810050720050702d103880c00c1204800b10515800c408200002004284081f640b007248000c5616032601d001c1c40011200804000d00c610020000d55065080500046100c591080a04d412041c01c0b0b8a0300d8100d0317681c0304403904070a130b01100f040e69908043c80800405c04040c04402c112400100000d030004014064030381201c616007160f202043c0003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 803647122 1250 803645872 803645929
    0x9060e0f0c041d06010e1f03030906030b041b05070f2a060903030e06030604020706050411010e09090c010e0d1a042d060c090e15100912020915 63
    0x83e0051458081040c1c0c401c1c00a04001039a55440d000d050142e82030030314400010070951059448403440103102140c04000702d50300d0b4a0024140c5010740b0441e00040d00b807540910a910703240c030406603031880900d803000c8100d58044094540303411a00040d10003114400310030003c90070541c41420a40c0f00d00350b01402d100c1e001e41c41c041c8000300e240c10503010000c1c800d1050001a4000c0f030101c00030f807000c840558990f0380c0c10700000c0183c0308404000b01403c0c10b103810f010801c900b074495007203075600036200e02c20801012024032420b6401180c41c8400340c3d002d80c0b6580499401400c0804c1c1000d40074008000031146a201c0501d00c18140b14507090300d880c0481003101703010050494124070500c02c40d5a200c1d00340780c101180702682180c040039209030395034028241414040e00ca1240100f00c500d0324400c040c84c2000341f900b0318500b0908190700465001240054013880340d0982c000341c400c1c0300354070400303985503809010449500078001244029050a000019650102e03181e0710781070014000d1005d48103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 803648372 1250 803647122 803647129
    0x180627060e0d110d0c0f0206180306090111030f0601032703082d060301020d0c08061305071b06510501030e0c06070804140d030503060409060e0f0c 65
    0x400c441001c2040240c0d421000c80e40100e16009042214901700c4413484141c00c0803a42c0c1131540c48020f43c890400144000441100c600182c01c681048081c1d41c6030b551070301100c40c04c4c0c91403803091020b600010000100c841050428240c2c10400614000039109040740d000300800040990300112011811195402c05078028a070990241d80d500c0341c94484040030b00f8289181080300c0c14020320300c3d9000300060a50701c095040e150900c840c0e14061040c011640c0c8040c00e20303a010b450342400b0b14401c0b0a15100101a070050600a024070b98900b50615051000b0150002021204403034031502c5000941c006407220384071700c151210000d00c110030308605068610039401c644a080819032441140780c4403810885521300102c540c02c0c04d010400c42d01c00c91402d0b0410240e110000c1e401280850b14505000ca1304000d00182c9003407520b452059030050b010000c1c5030224030b0780200005c0c000c1000032030b9800d2a07003102000521944010415410000030a8185424000d058032182e000c001d01100d1441d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 803649622 1250 803648372 803648383
    0x306090804150504050619030920010215070905061606021c14040b010b16200901080c1012090b010b090a05010314070e01020a050303070210050901180627060e 70
    0x165a0400b140707060700d0303e0007240047c040d828204205e42d03680d030460040d0754020340000c3c050981c86805da00030804501005402c03040740070a8a40184185041e8064a6044ca0b00c22401a030711034a43c1d1007030500c0d1508001b1154080b06420842e41c501c00604000985540058041001d4003400ca1002e20040c40c060011148c21000b1180d0003010f080034440854005a032507415a1048001c0c42c0e6205c04a909080710f40d8145070b0000c10940001d24491503201d50760000d0621004101e03405c82ca00d0344c2c3e80c87d20356516070010b030743c040e0300000c40e21040c00d805002d00002c0d040200d0304003001c10340c0e035a540c035540380c4660260720031024203000082c00211843c000070041c025000c03d00782000140080b0600103600301000340710100340a08184011183c1c1c1c020040541a19480360071255a40f070301001c0251100c8281042d206014102800b08008003818000c490303941c2d150213103075024031400c0e444240150240300c4080e1221008004000103181081d0342021145000702008110200320071201440c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 803650872 1250 803649622 803649659
    0x50105040e0307020a060302031003050313140306040b06090403170702010606110a0b04020f030a170c0615010e042406022401030803010b1c09030206040c0e0c041a040306090804 78
    0x5420810032100141c5e91004200d00340d82c241d103401616a501c00d50342140c0100e07175400141039840049030300310044a569402c0b405032010000c0340000f840c1800245030361400c0503100200f800d0201c00000741c06080100f02551300c0342c001d1911050034078031200c5030103640c8000d0300c00c1d000503512140b05000c90b0f0b0f0000138040c560700e000310040c080c01c03c180e100e1411802000d00000d02c2450444141042c0780c0e000c1003540d2000760000718031142102c10104070032040d800840d80403641d010300b80014850800d041d55040604c6010385030822460020010440200024858500007540c3c41103040c0c03070740350101c0d09032000d0200c540007403494200207000c04159031003040e100c1c0140c5490000510014120506607411560400311050301c50b07071f14070002001141c1c1c0e680c0f2005620300d8840b0030803d0541c0000c0d502d001d00c3c0a05245542952212407a525a04086a40400301e17207040000b0403086402407810794500c0f02d0203016a04040c1c4903030f14141170300c00c1c41c0002c0d50030700000f04041c0212007640501d0040ca = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 803652122 1250 803650872 803650901
    0x8010e0c0a08090309040212010608010b07150b0103152702091c05070b071a09010905061503010b0306011706090a050705010f0516261303021c0c03030305010504 71
    0x15180215601480e4860031210070304120110000c42c540c15010070507940305c1d100081065444108100d2000c546000034484c840c00620b03d0400040c1d207180c5002116075803070300048440b041c440d8981211001e012804951410181d4800d5540a88200b03907940c480a4044005032491002d0b400e00f54020120b800e00c0024249407041010b1403050303903501000034940c62005000040c10001c3d082a80c1000056440040500342c005000c40401031501c912440028244020b540140c9038905498206e0359000d400902582c0204041402c0c88080c012458000d80020000b01cbc5480b070380c00c040707410b110302031f400303002200003040040003009000e00c250ee9000c0005001028265800d8a805a0340c0a4910419040c000c15401c41403465101d1406c485440c54051010085c510282c940000c14240350220790104c1c003c51011280700760a418100c03201d40d150000d10002c40f0381190204804034030340007010b4031404800f040100004105c81d85103401940240c1300000c5075894071040c0f109640700700604070407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 803653372 1250 803652122 803652149
    0x1d010302090f0f18070206010906080105070e0906030a02060403080c060f15101e09050307050d2102190b010302190b1e0d0212040c050405060a03060b010e0612070801 73
    0x841d80c44410320755603008411a403c54641e0741000201e09141c2d500007081881d050b80604000c4819000209603049a08801007040007683e2800c0040c00c0700ca003a509a800560912070041301407504490441c0c0090004050b07403400b03003c1d60b001560f580d00c1680125400c80001c0307120745282c40140b2600c0c1c0e104000c0c8000c039007185407181c0000d458104c1400303010700c11003861685080161090040400030103d580c40000400c101c0032001e0b1441681e403117082d02c81d1050794804655802e0401c01c08404036030003204061103868a01040b03802c40300e2105081d0442c4100408034800080195908800030300502514516504500520418071100d124001c502250700390200f0601e960881110010350141020004064a028107150540b00715840c0f06d03007540c00032030308484948400f1f65050140f031040e0041c04650755244240019104122851a4001d00349402080454100d030005041913005152030003511110303070000b424581100c4420081c00c20700a080005040d0401e00050141428222084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 803654622 1250 803653372 803653387
    0x604060b0f090c0708070215030a050c190e0f150c06010803030705090f010207082a191809080d0e0f121b031e03250e0103090f0209071d010302 63
    0xb0b1031000050080c09482d94002100010b001d81d110548071001d50091a006118031101c00c0b8580f02e40040d1030710500149014045640d007900380044450885036a04a6540080c0c1001c2c15100b81c065910a40c0d000100c7d2120301c190780c2e4664006d03030781e20f0511001c0305440b900350308001850080142c1002030541c0c8104180201241c100d000c0c0d802d17148085a640c500722500c81c004030f00740055503100ca21244220122905089110342c4804c00ba440060300382c0712141040d20800211103140344021100100c2040244241400328200340d0820b201d020010451500e180c1e036000303450b4820b403010790840c0d03518200c8181c2501e00b0301201a2120542004140044060340004041d01c101048100c80314044801c17030200d440c0900580d0000d5819034a0400e0b1003421441c41c420302e900446250500000d640716031986119920440d50f03041d801d0f07940d40b14007210782c04010f4004080f140e800761380080e02c01c02c1c20750050b643d80366418840e407059a103a0043c800e00d82170344c40745681201c000300e0500d4014412030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 803655872 1250 803654622 803654629
    0xe0105090a14070e0c070203100f0c020c0d0f0b040c1e0303141c0e0106080a0c06020607050a05030103120c0206181021020a0c1b1401091805040201200604060b0f 71
    0x81790400540411701d5600c502c1c520020749000100d090b00035040d4106660074070010038a500000c4040e185030203403961082c06004006a034203610200800d08400d4920700c4000c60a44040c059100703206a0305422066250281c4480c16024040c400710001400e10084c0708042c0d02540d20111a4000c00a0718240f4801c00950300102e0104c0c5a007911180d130780c12141c5000368094019400418450342903900c060618200014500d44500400003d40304500207d4025440340c022100c1c40111a41d0ba5429a4250381d6450038038107907a04001d003008402c082c0c0354056511140140803101c0080c2e80e00809840d1141403000620024a000d07046c800c224080b45001002242584543c40c00043d0040e641c40101100796441d11540c00054018002d1450700b40d0070704401c490590030f0b00c0811910341008120240110360040040c0140b621040c2207500b01c480b160a150001500a44141030810f003d059024040b11115802e030108c0c174050b03000c03000340705c2485001d01c01c43c8202181507540075a49900d01c00407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 803657122 1250 803655872 803655899
    0x9030706031e0e1906060509160f12090c17060c1314131b030641030105090709110c030405090403030e07060c0221060c0703030e0105090a1407 63
    0x4052043d1242680d1202000c01d20441407415a20b9103031102c000c05a041450003080302d4020103004601c0f03540801c40c0c140140104103410403043d0741d00005400181d90880311500d240044100e0311342c4940c07206001a207800d04500c0a40100301c2d0210000d40d54100643ca05800900004000903007080240c0348121841004001d5481c101c4894000381144d1002c1642d036004581600706151501d54040001415403141e0016030100c1c1d9824440a904c904101c811410303e0030320701d60344013401458080c1d10301110000910002801e801404081c40480110b400d5840496145041e5085010300b401501082c0c81401001c1901820305400d18a890046961300d1003a4020b480c0b04402d2200041c08140c4a5002100310750039813030a07100304e01d0351900d014180b5580e4460807889140485c080503c0561280b64103920000b41c80e0050581c1d03160201c0b416200d030710036002a010552111003c805c02042400703002c0c00b603050080203042d0300c0d00c1403c00b0881940d074078006e0409500710130030402081810080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 803658372 1250 803657122 803657171
    0x9030901140405060a0c1b140f01030207021003061a0304080406030e0f07080a1e150e0a05072904060f1805090702060703060f06140d021e0903070603 66
    0x20440039a603450580791546004583c00b0b1079110700b00003400754650380e1041c00c000250b84210405940700206241d000700c030785941c0c05542070701882101884050300d00250103138811601130600500c2e041c4180c003c02d050040c000e00140229032280d2041016440d0300d040d41d100f0180c0b40c07440c14110b06042d40d07039240c81d220f603100f031004054851034480c64415090200000c0134290a04883c0f181d6510704499455045030034003034810002c1681100d030001d00c4d41d50b040190943c400c00014500031070038612802014000c07030324459407007403000000016004000c020054001d03894441910089a01000140d10340010040d050721018441000300542207810741c1c0c10301030241001100e0b03096101c3d920b0141031080d401750380c2c400490b2091001d21070300031500d540120103d903006e00c4055100c036820f1580429502c00d2600007180091059009401e100107009110045130025261021880d28002082c43c102c4008404810000d0743d06c013a840c0401050004100c1824180110401600e000300c0740e000c50384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 803659622 1250 803658372 803658377
    0x4120e090f04020a0e040f0b0703022a010f0f1a03010c020717030d0903120b040213030201050f0721030c08280608070f0810110a0c0501110307080403030b01030509030901 75
    0x1002c2800c640d00c002e0580041c0802004028192a007800e0002c0308910650040d50300484401c00704003280c1c440d000f101d008120100d0040010031811702c61004100020b164691195030f6600102084000b500a016441c00420f0007c01c000d45000d42001c40317900c0f0795000c244268540800002c00d61380100d05c075412148115011034103078051000302030451045000c0640c08520301500601055088400075640c20241d04d002c2001c41c0b907200c180012031244072480c8a401405500800041d8801c0000f80420b6250021040c2807140958a0f1003800000d0b05110145d01da10b001c80000c00390f0b2511401c044003081d480e11400d14240710708007140400ba03410050002d5040c80441090130101ea8009400804103013040320744160341c5500011100c80b241c0140d8440d802000500700968040f4011441c0d001c1c441e0038080d20f0012a80419940400c031540201e031555240e203440d004c4030340d00f2009144034401c1030721146079034074007883d0060440c0c6951650a040c11f2601082c00302d2840000191135032070b242030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 803660872 1250 803659622 803659651
    0x3409120b0f0703140f0f09070503030d0b011b05010203091603020a0302040b0609130c020d030e0c09100b070809120d08010b090a05040e10110a0e19050405040b04120e09 74
    0x1142e0840103401003800154080c0c10340000d00c0700c400391004c016031103041c118008030120b4a54080250700d4809520509903d64001d0145022000040e40b0010401205051408c4803005d08000c0044504014200391101d0b540401081001c44050044100180300030001518032030941c0d00140800d800c1d0700000c0e010381d0b5221501d40c165200c500c00c03507111403001052114100312a158020191401e409900018000c3c07480040005000e402046a45510007020b0500f0741e40b004180419094018020310307001c1d00408000441102c840d00818815001d00c000b10b50343ca0341c40080c89804540121039151640c00545489905070f4080c4c00d00341521a41680703d699484500300041c03a145660b0001507000d0f18024150550803400210404900841e94041c8045c1c561010211550f010302800603021514143d1364203420b241040c148490b030b406946034140e0054030b80c00440d0488400701c40450390140301d0414803061080c44d1034207825420740c0c0c1c80c051041880440100d11409805010400903601c0d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 803662122 1250 803660872 803660881
    0x909010f0525120902090a061802070f0b060105120c040e0106090501080402041a04020c0c1e0d0b060d1a090705102a12120b01090e010e3409120b0f 65
    0xf40d41012080f160001d10401c02030820500c0580105107078841d040003005c0c030031100f0400c14500c2c025aa03145800c0320701c0c2403000c0b040d070b100d1180c0a00b004101a0401c542000b10340703426101c0d05c07825800b820074143e14580711810300341c1d0140ea40c00c0603009103044c0b000c8000f040013903a910594040d48641c2c151008203450b2201061b04003e9000703107110b40d9000707001050212900c040003611588010b4100c0da403074400312424000d84035890f6100592500030006064040c0811a214075485e00310030058000513110045407503082c984d40c1c042da1401c006820307140c00d108003d40100284000303840101c80c0042280d0240c41c000d4030f1001080c2c10420032985502c0f00c6101003080620f51590319411000e060340364018540028608031100c2010000c280c40c0208201c11544161070602c180c601c04074103c201c0c0d900340340d8078840101c0300800348401440c015440c802881228014082c00d240103005003207804a42c42e1000c0d15003481500000c901d0f001410552000c20411480707690848007800038140306848 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 803663372 1250 803662122 803662157
    0x16020a0c06050d0b0a120c240c050c031902122803051e04170102030c031512011e06081b01030207021801030c0f060f022503020909010f0525 62
    0x40040c06981d0003003d803207000500c5403103602c0c1d0146c00f911481c02286400e84644041440d0f10030402c10202490540c1c085a00c52401a600c0c004114040d02c1280c0a8058050019140c01c50000840b002074441c0103503482142482e1610080318072100018200c04c90110051059162650035840c8180f03501180c040300307060080e01242c1194400b07075100509558a041c4041d01503105106481e810840043d030582d0281c818400d4074001e140060701149140c407100301c001060112000340582c40381c00c40400c118807080901c14501550300d44070221002c0111404c3d6001161135960040130190440d801400c01d00801001c4021800000d00f401615041c503400410304640d080300480c1840e600030380010003400503859405044030621160f03601d01544801f0101e440820026030840943e200180f4006501c0c80152a000382203c110a10b03d111942d9400141240b50282e8560003640d40d28240d200c10340302907008259002022568402e0004501c1d899266078810b040e025030300700300d03422100201944 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 803664622 1250 803663372 803663381
    0xc04030204110a140f070201030b01050c060a050414150609100b040608041502040b0d051b280216120302010f060801021908060f040b060f0a020616020a0c06050d 71
    0x15006441045841c2c0e030018980600d600c07101d1040c001c1581d000b114100c1390b0f000c2c4126a8643c2c040c03514542408020360066000c1c0c4105c01e01341d03050140600c030f02c19440104009192181080640116a41c10302e818a040928103188503c03903150011070785c0b40380309031809401c6c0e60000002d0307a10000f07a94401c00c0000810030380340c12002e0222000500011190740c010411809103010300d410f0880703402c209040c0001c03840b8911803440394410602c010800140107a00080d8000240024030b9110103100d000265a603014200030781036610107109500c0b910101c00f45042d450340590000381484025510340240c18074403441900201500c40c0740400c00c0520230f4200034074602c0f1482d001c0c003080ba26000494040d40040d0f1a4540941091908086547c41011098010030000c1e002e0000c5030700780000d00025151640845801110812101c15043e15100040014907501d03800352607030703041031040031000394050364a000841d401aa000e8000c00c1e12040c20008852803420420303a100c0d1070034001400f90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 803665872 1250 803664622 803664629
    0x310030807080f030106110f060f060913050709020409060e0c070b18060c04030303290f0d0807030c021507170d090510050106110a05070506030702190807020117070c0b0c04 76
    0x3c00040000284a900b06010f40b117014080000d40e01290b82c00c0107000d64810341266820300c0c284484010880340c0c04c10b80c00d02d0b034005480b40102c80010381181c4403285000300a034001c82d141a40094104220800c51040501130a04023483e810301c1d090042c103090720341c0104c807000b600744110700c80482c18240301c41c20044030b64120903045d80c3c0140341c80020b48102d60801d21040c0d0100e800d00042c0f007190f030203226240314032140d0841c0c0e034241d01203103c052140d82c00900300310a4100307501e10111000f10f03000d4405010590306c00e076245548a000391043c80300a2005815441000800b0b218440004442c1803201061203030010f09603840f4440c0e800004003070105804050070314081c4801d040310b0b0300b1203500240c1c1a126030348c5603900c1852411a44598908110001820503004000107100c0e9180c511700568001e192441194000c03d5801c0c200b07484000320480031200d01400040720f00855800c4404030030f0b0200030300c80140841c03030031020107898011141c41c003c02501c0b8250004200d0412041170342d016 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 803667122 1250 803665872 803665897
    0xa0f0c08040e180d050318010903140d0603051507140c0a030c0c090e0109030f020d0203030a020c030f030c0408071505070210210212010b0f180a12050d030c0302031003080708 77
    0x1c084044801920701d6205540e041200c01d0b4587c2c0e0400407e00500800381810303410758450441030450500420690018191b82031070310f8070340b0000008520704010802c0240050750001e14107080c205c9003c1c00c02c41c168500303607805000503c28480b41140c0030889088058050901d00c2000380d05240110a01d0170fa0380000c142d00c0d10b00f100b04002e901c070552084003940c3c0309445200741c1c00102c0b8030580c1d69058200d42c100c010f074010000102c5964458001d86100341025040342e00301504a68109219001110800c805d46070110b401c102c542410000a4000c01100fa068000100360360781c020103034480c0b4400a03000f0310115140d240e03014454010310200b2a002030340f01280c40d682003283d4000e940103100c21540920207000105120350501c0407610346048802c0c8081c038001984042ca019a080d880d40964020070f000d1002443c1c000d8050b840e81c4a51042002d020505130882001e41100d52070540201054810300400a20b404060800d5007507030f0f044610704e503c0700a82c1ca80310f0302602c1075111a980 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 803668372 1250 803667122 803667133
    0x1d0312033112120b0a030f0809120f1605060403140f1006080c030c010516140a140d030c200106030602070c0806130302150411040606050a0f0c08040e18 67
    0x42c80b549281070700d14001640e540306269405142e540c016100003034286607006540500400019414001ca0030780203106071156820180b95000280d41c01c02090300100700781c0c000c803030030300318614040c41218840441c50010070701c00c40c207006c00b0402078090381c00020400c00a400b034075160b10904101055401c0c0c000ca045440c0342511042c0e03072014058901c94441c082c42620010b00d4a07280102d801e4601800c180d5545007003091b190500c00c1500101c0b4030607a81e070b1202e40b01d0459003440038881848014010084045040d400180c8545800f044030961002c151900307204c25000d59101e0308240c2c48903840d0b8881c5d51904800040b071801808103600017440148001180020001401215022035a18000b81c80b11a503c9849520340c44030030f1a401030045c0c000e503013081e041119110b10660018007800880e20007100c82c0c2c01040840d50507800540c0403800128294000c9940f0610b822859001ca1511844503a0382d075503003105500950041e415501d8100c00050105505000164800d404002c101d40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 803669622 1250 803668372 803668471
    0x7050c151801060609080c060408060a05181504031b050c221a0a06080403140a05090310061a0c0703230d030504020418020d0f0302120a1d031203 64
    0x146400c0062150211b03038003550034031000078034102003030301c0844001802410b40c1d9680c0171500c800500000303180078100745121f4401341042000304480f082d41a03640130b810310f1504140c100076040e515503117101c0525502d501070701000070303002080001030707140161100c1c00c010b010b8560805406070360f42d001e401300034035040302080c0141c2c81c250898941c603019551002e640d5103034181101c011008503009008544411341c151110041900149480d0619140040c00c2c1481540003d0600500c2c21001c0b51064131228144403404411241d29110680440400e141c00b000320385280c2c68001d907110152200385001e0102c4001910234204400c880e011009694a914911001400a11041d10306a000c8c030b14040d006d65011404101c1e501d5025002002d82807120000d50340c1282c408003500e01201107000392500104450300060280c0450382c020f458401c40150206240d0000080d03a8601078400e83c401550000803050001c100c3e90807842211044800010000001c03900e815003424201c5640b542d2040c62 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 803670872 1250 803669622 803669627
    0xc03031b020a0c060809070b07030e04020d0515030f0d03050a14070207090501052709010f02040b0d0e01020703090302120c10030c08092b0e030105090a0b07050c1518010606 76
    0xb0341a0360700c140d60705020192a03840c110b50300b81044801d030003594011601801180b02030310103481124400e2400d0808081c11a000c2016608526002030700c003030300c560030300104110807010b8040f4000c040d40100400c3c80103040f660368035004810034805143da00c902243d103401858220404100421440c0000c0d4100840000d54804640c0314a01c1c0e11450300c400410b0620b46030403040c521034000c0495500e0210032030b503032540c1c039540503204440b20341d80e0b000c40d480e0320040c9001410042440d403c0c4143c480c100d00f481c10055410f20302440c500345c2d204100c1c000001750400000c0082d2078055400000280299544601e000047c3c418242d107d82c0418400580c135905800600100300c0554441c10f542c1c5601c0d4419680d0841c04400c2e1418025015104010302001e1071604500d10552410000001e20074000c2400c40f54140c8811040d07411102004060104003440700740c001304280380c100d2401050244592700c440380b01350080c0c00300002a0110341280080400448012402c400801045940d008007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 803672122 1250 803670872 803670883
    0xe1903140f0d0801060903030f120516180b040e0408120a091101050a0903170d0f0509150417090402190221121302060705070308090108100302030d0c03031b02 70
    0x107060503849030070851000385100d000c50504a8403503403a0007880c5803c1d9613064640d40c0401c0350407400c000408040c40c0560710540a910300444c0451319074006192006030061110310301c02c0c2951030300300e81c0030f50030848904a001110300300d40c00c1c0e2088269541701c0c1e180000c0c41c0d2040c40841307113010a4040611806a10b40d501c580030280c800c2c1c407420b1500e8909001035845005401500005c104804030400c08101d400c00b500c410ba54040c04c4451803c1d001603414030448031942062440780c1d40d101c0c10050344240400c250910a039500c1c82c13a084a180640c1c4071020111001e00001d044003020030552020b86864060b9105c84003450740c9a282e0b03602c000c0c8025525044034415002e441d03201866030300501540000c6581e0028820044280e90ba5020b1410016101c0c0d00c000f241c000ba402c01020012a07000d1110300091445030103110366480241000615100c0f0151844142c0c1542300c1e010401680c00295202a102035418080c0d2101024202500103226100c01da0754490214a4440c240c0c2d80d01141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 803673372 1250 803672122 803672143
    0x1203060504060f0b030f091204030309031703241504080c0102060c0a090e1806010312030c05040b2b060902070501050f06241c020304021305070e190314 67
    0x804011655441c441c503e41200c46101d400c01c0781c542000411500c184815000da4008152812521f00c82e115824408956000c3d500c00c1e800144485000d00070401c000305094024061600750601710f08000c021403510110155032031003c0902d080403000729498a804c0708500440c039070301c0192280e6503912016214100b20102a0041c020f01002582040c0c0744015586840340c10742d145080350782801f003054204200501302c040642d1403000f4842600d1000c00071980a5882580c2c06c0c0848420400f0280544070441c0d02003080c0031080c88284400000d0105031001ca00228890840040700e0303603002c42420701d501104402440c18a4004210b80078160002c04405100d40020400c941d1001d00b500100710042d10401d03805080c03c03140e0716003052080c1300d100c485c9040100c010b01d031000d020b840d40f10381d698149403800019000304c100310540c9458038003040420903482042c070907803410f12001021103050380c50350342c41807510903030032170983c19071054442c055544040e1042a645040c0304c06030341d8080d00c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 803674622 1250 803673372 803673379
    0xb0f072309010206092806060905040f14060c1e091003060810020c1c02100213060e041b0809010b0409080717070b0411130c080a0e0c1c030c12030605 66
    0xc0101d245620001b0ba0740000b110599081600d40c0039000c6100c0e1810f6000b40c0559009440d900081200160342c0f1a0b103001d18401c500c2040505628540003415202e07039000202c03a90032010821048203403d0040360070503031a1070801000040141c130762060354010041c2c02a000780c049804010801d4055005800380c6111200729480c1c0e450348000101a80314424400b00b26411000b0007842e644000c815402400368203005441c43c052552803900c00704d810204082c85090b1850008218040d0407004800565070251405c1c0820715007680d0304601031420600d8041002a101c0c005410b0030302c01c2d40a5031100400030000d100240719802e0100742a000400c0c02c3c0e8855110281440d500c1c100c44040f141e078558807155150495540703480381807800d600c603030005811084a00555002b04014400c4001d0b1120781e85504016050480c2c0300740459100d88450301c555401521003034030680d240180710341141c0715111100b0101e1081e19040f070320360304440c000402d070746464104010040c0d0560400c6099500c1075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 803675872 1250 803674622 803674633
    0xb01200a031b0c0905070201061a0706110a0c0f110301141503010903080a0203040f060c0c1403040522090606081f0507080c0711120f0105060406030b0f0723090102 72
    0x160381042c490703041490018450728542808000001d100d0300714603448138490000107607050340c540300450301480012070000d01400000c1c192080103600e1144001e49100b1960346c0d4103145604074094400580460040d142d00800c80002003003164402c10360b44040c5000d0300078042c440290745845810751080d601803112141540000006013414499150070a40581d2981c5898503080030b40c0c4000e50010f4015107071200b88d040301c01c0202d009401400c1e0b1558190b03440060540701303801c0510009445540300103c2e50801c10007006241d07140c040280d803603004500f8080742a0b9682a680d8010301c5904130092600c2e0034005c0000c0c1452011400e0303015a000c0b00454404000c0381c5041c81c08a9200325101c0001c5070401c0d0105080340302180140442c14410507401702c0d01500c480004501a450842c2d60b10954044888211041e03004e0050b203404c51030960b0706000321801c66442140340c29000b007884904840030000241d0041c811804c0c480e07809040440149116440047d440305940f0540710180584242c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 803677122 1250 803675872 803675897
    0xe1c0228030314160b0c19090e0a0e060c0a27060f05040602151e0a0b04060e0405060a090206160804060f0f020a060c030e010f020306090f01180b01200a03 68
    0x2e0303089402c40702c0801504c190014807592002000c503c05401d00001e0602840f14080035a14010100f4036072403591641e03040d982c44e00e0029500c40310000e04092601f420014040048030001a002c0d0300001240142610b41c4543d0900300c49031580c2c40c1c820165212034003110401110500b15407001d407581c030340d22078200c03202c4c964041d2110321440c49044010f07440b80003c120361100c82d52a00f40c0011160914210442d680420314244401c155190f030b2480e5921701d000012494144644401080100003500e041e10b086d48600e0307103d0a00404103040341351115a041e0442d5556022100d5140300a91b42140b01013160516a0b03280e0131034062070001c200140f16907800b55004a2103951080e060f94000d040d034100f69680c0e58043c3c6100724498051544504000030700c41c03000e010350381c0445000c2c5001030300ea143c80e808004a00034090078503c01146000010b000030007120303580240412040e040420b14042900048038507410000b141400d840c41d2544626101c070001c50402d80741802a69620b841404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 803678372 1250 803677122 803677157
    0xb0c0306040c140901140c030a0306090e010608120901110d0804050c0f030a022e030f11090109090207080702040507020303070f0f0e12010e06250e1c02280303 70
    0xd20407401c01d1003c40c10f200d2031085600c5601c079005807944404819007003007a44640c261940d000745d4448404240c4410b0203000811041c41101c5000b40004e000740105481c10b9a0a500d540005403900c41d04032001903002c00036401136528115042070710049940100b19450700614401f803d4900b11440c0c042c00c0d0740000117144c8582c510030010700c001c019222007400d81d82044030035a1322011400a010000702e44645c00303005000071a44003840c3d92004940c201e1188681d004603442e00c0c0d0380d02c900d144140203106050345d00c084a0b80660309804070040e981e45c2d19040190b494007032510002e6005091008025619502002440c02441d96480d0030410650303200080c1c0f04101d510307441e640018079541c20a012481d01c0212a504032440c2e0380009000c0d4103007040a410304000321824540e005903c4154520003009000601c0308400d2490301c03101c01403520000031343c06100851284144102d11019100390354440020722000c442c80e20300c0c07850110000d000401c03c00620b100680200d40c081904000450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 803679622 1250 803678372 803678387
    0x180605071205030a0f02030112020a0911120405030904020711210303060d0f060504081903410106030501090c0905030a030503070c05070915120201020a080a0c0b0c0306040c 76
    0x75403003501d800751600c1c190402c65003034200400c1406080e03100e50200c120300d00e081c40258041d225011400d100074015005000c4400303007680c4401b104030325107c0744055650070300042c4c941da901d07038103107008403034450b0304080c0c0c40c602503460f02d0380c1c0c854070018018040202d217508102c01c807507041c1c980301006001c4017040403060001c0d28024220303800810008100b0319140b0114915280704108000722007450352240c108441046500700d81a0000203020320f00756404984411001140b843c1c03d0001000014940304440300140801e100c44410101c0501c8000600c44040000040319005190560f5030700401809400c1c20712542e000c0c2403a0105002e10144615000c0060360800380c024556506d0954044581e0742c0300a00c1e00d02086986d4041078001803050000f4401007a4a00c00400e8101c5260501005000d4a605c42050030080032800e10040c0d801080528485800541258803036041d0041031301c045c5071203280140790010354400c01040781034003030287d801481c05450401800302072540648020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 803680872 1250 803679622 803679637
    0xa0f020703140f0d18050f0625050c010c020a020f040b1509040605060c0a053a21060e130308041401021e030405010b0109050a3003180605 61
    0x40321001140040d210000043c5404100c0d40055031802594690b010111030408a5100c80403072580c1c0303040c0902c0820031418410400283c0500b0903070801c2d01450048451100702d20704008034060180c0f80c140e000d80c003500e03200030f01c680c002d01c0829078864000f51110150b41d401ca20aa90745540704020b4100392142039210b0f14090022203195040c880c0310740790364000620b881d1f0701548401d00458030380c036201e0191222000041c01040f000d0194a07045041c4001100007802c0d410303d900a04e602c05001d00d03142c083c1801081c078480740000c0e42c50380c2160014403c00e0f00103840300d041802101e08c1c0c0d000e60f0204d000c44420b401400510340320032038400184c189105011300002c8603803001c5404244003181c041ca480c0a000001481c1c03414010b82c00c050200c1e10f01c44c00d0790884c0044100000e00c5420f01560184540074a002d03c82c15003068000741000c00a4021503a1444941400b001d500d0071040810301c101e80f0140f90110040e00a29000f001811000740080000044040011b4020700600030b0f604103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 803682122 1250 803680872 803680877
    0x40b2401050f04080a0b040b160507080c01061a13140f0618100804050d020607080a0f090503030a02070c0605030c09120a0b100512120712180803030a0f020703 70
    0x10180000119603a801211207107126110030000003503809810040c010500d48a01c42c1803540e803038141400e0540720350090800d21401c80c04904484469070003c1203400e0103920080603910b03410764101c01c4d8010040c5420010340c202141d090b655200c0d200c1d202034461b00c140306400080d861b880b01d00342100c8051641425801038000028005545440409000d5085109029a01540c04440082e42450040b000400401d04030402e01c400d21030103000003146d920b1180011b1010b41440708008042420080003000305c65aa01e1071041040d0071900080c866035000011688c03282403072501175000b07501110301101c490388100c02c005401c5000300242c81c030450140390020b045c20b01410034402d600b0031000070411180121009040052743c0c03804107a000e1404007540b070710010306190600298441040d1315aa250307018460450394561214129160140c0c0805d000074410282d902c01e598060f108014104000b000e06008144403138000003451040c640c0c0d8009105045086101c4012841480c41c01b400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 803683372 1250 803682122 803682181
    0x19080c0303070c1710110d0c0f1d0d08041d010f14090703021606060603380f130203150a06080a0b0a0f09090b01050604260a06050f040b 60
    0x546059089002034075260802500e80c401070592a0f40d0440e0300e00b04540d0700c1b29401142c041004085446003405110190030801c04c020488100508a18080c5402e6540c11505001800701c03a01c2d0410000180ca900c0487e0f03c1d00ca644036180440050403500071180301070210300000814580407580e0b40111940e1504291040b19003105204151301c008102c001410f80801c81c14501c12074584010450300e000d90340018446040041c010103031035520a9010242130040d04410000c221008011041c0c3d06549a803021804140c02080c0c0c1285042c06483e03200c03041041b91001c0030025001548110180d41c0100f1503503c400b401c0204070b040758064880004c1c2148002188a00c070b0364002c9500a0008001c55122680c4d9006e80200c0380c03250300511070860711100803404000180d40050b01601c0101e61840c105420280c850701c00328101401c0340a0100007048400d07103018280301c4440720941100d02404a86410003c80a034cd0f901514201e441c1d0312400009000b00702018803044202c078001400d0b09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 803684622 1250 803683372 803683379
    0xf030d12050c1204050a02120303062220030405010e060c120406061701020d06080604023a0609150b0105031b37020c09190b19080c0303070c 62
    0x1040020200182c0c0801045640c81081850100e9842140320744024805590b891060010b4500644000a0340d68003e0060207000d54034041038041c10a448010304240e245045c0c40f0388040d0014641201c038984e000380800c4d50344207810b0010345c030072801030000340702c05220b800f1000c3c2c2d81e07402142c0141c82e40105001030080201801c0d27507590458092000401c0698848101907103044040946810aa50000708143c1d985040d0180d60003e00003100548541e01d0150007180b0a4604000d40103104441c08159528a2a441013090119100d4402c41c0a8030000303440c104005100148087c0c0e8440d10702403180e4941036a0b40528001004181e583c1c60845c1c50341031050114441030803c4403081074080c0301031803a80520b02c0c40200c0c190380071814102d4118524080704020401511214219080447d0060194481074201a002141b0001d200b0130724082d60404001004003100c0716900840384907212000b904481100c00c140c0340031704250740001001c1010199240315900001f4450709080c0000c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 803685872 1250 803684622 803684657
    0xf0c21070b010612020c010501091505010804020603070807170a09110f0f0405190509010204050907090305030a080a380118050f040b0a0303020607021002041404110408070b04050f030d 81
    0x8069034290f113513000d0b00304050310410a00307444091300503014503940d41c00c10217000c05c22840010300601c001e003400d003031504281e004640075210003080e9400b03120222021649480c0b29000361406000140260300c0c240c20f10011142c05072100900941d51035524464a088524201d20981444200100845188a150418880a40401815207401c0c1000f003c9d94684659240211032140d5074100005030b40718288000c1068080000e4012810028040000c0c40003e03400407c55024640a042c04c0c44160b655802e00000b03080000c40311504980b03c0b800300300d00404400c0d001c41c02034001e0600c0c4080e01d00d00d40c004462003540c801ca0030030455040034040050742042000c08038190000781010480210b484049100692140d00440050344590300f00044d2641c184854418906020001d615251a100d18800d00c5941c0c0300b0203920456070b0703480c100400d04940c0202c0d8000e00140b410b0300c544e19a81c440d40e8100c0e030458070603079006003156403e05069183c0843c00001d5508a07846098014504c440c44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 803687122 1250 803685872 803685887
    0x1401050a0e060a0906270204060906080a06020c190f0b06190302060c010902041103010801060503060f15010e130605030f03042103050c0610090c1e0e04020f0c21070b0106 75
    0x150307140f40c3d0b00c0300c0101c4407071800d10300c1c80c6c4100e500300400000d000d1180306100440c2c2480d40048100e900d00207040c00080c0001c00c0d101e8809800400c0580c460030b1499a1600305040c2c820344601c40703408007a4450420070300307111084100d401450703040420390f40c04c02440f0b1030000c1c01c40e0400c41c411314020103100511f040c0014012400b8910300002d401207080c3d0104088404803c40440000e10101c010000c42400b40030b0b40021704000d9000e00040e00309841480200540034005d0420039903020039024290348107200e085e600800c003c100e0001081c213103c5240040c40c650158500900610590f03920466000049030100e80a00b08401d0400340c07820900d145c0891000702c22020010200312011520608026540c0a0603052040c000290300d000c172444d007100c025203400b905000e04225021800d0004e001680c10040300390400c3c00d88a0002c500080080c414103c52410f200da01207031340c0012000010764070724007250303404a400b0340d0003108040f030300f04e405180001051042104018800c491040a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 803688372 1250 803687122 803687141
    0xf02010b0f06030a24030503070b07050703050906074407200307080f010f0609140105121e010c02060f1909020a150e01180b07200a031401050a0e060a 66
    0x88600d5841c2504443ea0381700358440d84242da15500c08190801480f1070412601d401030741030705101d807a061343d5560240c10341c01040021031040c0b201094040502242c180b02403003141680c00075442c1109460010000908402040c800304000000080000d450840448403c681c003c410740c01401e05550041c02007500c140350060705800381100000d0f8040c410081d04180210500000c13510b07413100200b580403103035294443c12099041982c5480009500d070401c1e030640d41d09880c505540701040880514040d0100c4060700b04441a1012503106203040d4080a030400360f80d0b082c0c0e90942c035011b041e451040c005441500004810720301815445006034043c05040303201401c4244015921415500a082083c2028020030751547c001c1d100c1d9a4480350860101c9001c082d005ca0f00b5080c1980710000b40140c80c0f000306840400b40c5401d066441e06000e0f58034550700148418402c0da120720300585000041403000d083c2e9802c2202190206642d0700503220f03001d122000074441540d403082d510300034003031044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 803689622 1250 803688372 803688401
    0x20702030718091203020a0e240d0911040902030601090c120c081f081002070204110703120c0813120c06020f0a0212040602120708090a060f02010b0f06030a 69
    0x180015040c40b803244071440d040c402640c0040c41c20341c03604003410003481380e03a914420180304002c0e5600301504480902800703403040c1d81c1c0c1058030004d002c401c140c0140141c514800031002081a00c4405000c1c0c004040340c0b88503a29821801c007141d414002075600a000095154015000500443e001035002c0301e0030901500d0403030b0b4400b002c40301c400304807440d417004030f400641d030b10b8204504128510b80f56170805101c81030362688189001051510342c00c400c9a0664160780028240042d50386d81c0d04102c1000d4800c401d010303074540712490090009a0400c0f40c030102d1a04060300b0400282c0184400c0e8810a5880c180c11010b807020355034662a6a41e510038030052103c00501301000ca500ba00c042c0c0351199010048640d100703546107000e0b14010008200c0100c4e40700400083c002c450307010035109882c0d00403040181e2602482d10f8202400c2c02124041130b0031241e0f40740c000864582c010511040f0b0030042d0002c1181000200a00a540700e82c100e820b90050820030104041d50b0099004840106502 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 803690872 1250 803689622 803689633
    0x303030709031e021c02010f0810140a030c0b07120e130203040201030213030b070212071208040201050d0207030c060b040b0d02090901020c0a0b0a0c0f080106030213090f09120903020102030d02070203 88
    0x9500103080c5c4c2d880e8011014402c0c07101529070003156008000c100d041c02c01c600302805a8600a582c1411609045c020740100c0b2000440401058882a4034a03011795407100040c1500c90b111078103061070b90001c1105940e038403210160b00102da0b00070340304000c2c404070103041020001c0020403a40003a50010300120b04041c3d00700004a18100b01d100204081c40c07040c00c8030140d500302020000e107000804070030b612001c4000c00c158800141404409610940d040c00c0a00c156900e03400181c40d54002c2c03036852044640002907580401d0350286c094172925106902c104518541030061104450402039a00d8004489802071009403030b1040381c0c03903406a8100005071130035802102d0a42030010140c4c003102c2c0c1400482c180052071342c060180c1c60000919141c0f15464003560340008000c1c00040c0702ea0401c0c1075002942504013203c088561000c3e1019403030601c4040c5010b44600014206e4200607a5038030810100512881d114100c0307881140e8050f8000c604100d000c010010096100460490749403051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 803692122 1250 803690872 803690933
    0xd2906031902031602010608030a02030306041109060403050607020706050406080609040c1a120606030f070c030314270f070501110708010c0f0318150f0b040204090b040605030303070903 82
    0x480c0002d501c103030a1414544c089240c00a4040e0030740d103c542001203190030034416280b95540c00030544e030b4070070b100311008200d03040080320f41c62040c412020003e401c00380004001c802c2c4100001c0c041c3c0a0307661542100e0b0100c0e9a002c04603142e003e6400388030000385400e00032030001d282c0401c000e904140580d965401e40360766003251401141c9059003403c4085030100f01c0140f881c8090035074552014081e240d0918620f007040d07016511040003041c0c0070074000303004460f405140c0319a02030b0303030144910075808a5a082540138840c680140d000344c3c2c09510340c7e2403240c641d5000c0106440b0141103010004100716030a203401901c510080d8920713044c2d01d124918000803d201d00340102c0149000a445d598601c0301402c100034142d030560100140080507200c4500c1c001407031080d40703145201002500059192810318400c000d8188401ca180e0b1050000c20042881807c0e07030320528030325500721400c0041c144d1f01c1c070905489000495024010a291107020004100f511a0f001903604070f1040d4000180407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 803693372 1250 803692122 803692171
    0x615060a14090f1c0b06150a0c0614100302120106260a061a0109090b1008041103061f170a081308010f050a05181c03060e0c0d290603 59
    0x61641c130200d01c2410741c222503084c000035004060b0050419034021180424002d0652110f02c1600503010401443c3c0400d40c00b4810280d001d045000b80f410401c40d058200100481c169000a020a038464098201d412246490512442d400c8a80d50904549406208001181d51000007014003c00d40a0080c0341000203003e0300c01c06001d0008031041114614803c000106406e607e40c01c03115040d4645010a2804d641d40c069028a4040902d032072500c0707a0300d505d881e914503031220b94000d405205070703414031100641c451140d41c44170070030080a641c100d03541c0360214000e4030b0901d1500140e0f00072880d50008600c212004100300b9080070011a486607440a90307a0841d024a204520850741d01d80138001c1c803a90394003c031034200c902078903802015200324281a4881c50296417030034400c003202106c103000c01d0003600501c00600c0c03203041c0b11103103280c40d4003690303e20361110404010082c940b021071a254400301e000c0f0b000b06100e10440c0f0300b02c1e101047c24060039500280c010050505d804008280c240d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 803694622 1250 803693372 803693389
    0x50c07081b0109080a110f120724091205070305060a0f0c0f0f110712140d1e0807051b0a0c0f05060d0515030d020615060a14090f 57
    0x51080042848964406001900c0703005011114104010810300300003040c00092900a001e8100c61455074080d10840042c91400c4015200ba070810300c2036008541411000c60954100c41140090134080410f08950015600c14010f0b120081b81491109000f007141409038403074450b08c40e404461449445e134503170a2400504443c40140941c44a4901c01d18917020300035160f10143c0c078185070250342c0c060b182c09005040368005481c01c00100c00d00000d502442001504002c06d8107034500100c41031a03003010040090882c80200d01486404005980644103562351b8100e10b46807503821200290310341c01103406800103231080b000c01c0f0702404940c8140740f500418541141d56100185680d50852810000c12120b66115203040c6104000800c020340340c110880d0041c100c0c1d4200000d642d620035400700030111000360000e406218074078821072240d400048c900c2c001e008440e03040c80c0000200c01000070a1168054013400240340b24021410b05000d5000b81812800040103041101d40d400040f0341041d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 803695872 1250 803694622 803694629
    0x1002070b041118010e130b070c020f0306040209160c0512070b070206270709050c040f0b0301030f0f030314070f0311030108070512120d02090901081b01030507050c07 73
    0x8038944000d0104000880c0740501641d1030560300e81c45004564695200c0300b0105106501c01c050350000000d043c55080420b0228090344a0540c008038101114018218079180038105d0094146510381c41c024600054898450b60b030040c148020363b501e0040864002458a5003003040c820780e1030909000070790a004461099034409080c94032200d4a061070840d25402422890640d00325500303000c0f1000701c02c480c0200b24a112200c1c501d02102c07401209240032080d50202c400603107028107010030a184403009104540d82c072440c0f040503a859071503a94031440300703100050914018030b2003000007500384910544440c1c041e00740015103110900c00c1d41d007448001c03640740000514080c128114960144110310305c00d00064406410356041038007980d907809107406000d1181d20f21020382c0f03016003004c0104207401c00c420540c1e140c9925100810317030060f41103003409a100c2c0201d8400410004000103441001c24a200414100c03003212100640050101a0000c001c00504110300314901c00e0800000006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 803697122 1250 803695872 803695883
    0x130804030c0b07030e0405040c03080306010203071b1a040608010e060429010f030c02100e070b0d0605010e0f01200f0114010504051e01030b06061b0d080106180b0c100207 75
    0xc0b00c801c3d1030020603843d45d0100d2280b0442c0b40606002c0803a034200b0b5400d080c0c075845820781d5582d484000c0181c0c518003554000030072480350840070b54401d2580410000484c1d000c80d0060078080360550700390a407400b40e8007a0304c00041036000104040310043d07455940000b400b900000740090b651402503803010700c1c80b0a00014640c5501c01c41c0055a004e46181031015203850f041054104a00d03000f529008011010700116484000d0440b81da9000e1010744014252400003903a42c483e40030074003000c0c0205204040c08103029064140c3e090920140c0081d0211050b91010454150b1742a9400d5021303000010601510a001c0c84d108040001d2046030100e6103c0c203040d103020b61400041009450380102000d410a001d02c81907201c88101320038050549911255220305550351170f010903090f0141c12585070b00011040300003080700e4404a60380d510354515588401143e0303294101501e210039601d0b81c260400c00c11000030400344401c071000c3c001002e1040184c41401ca8880b28181c05c1c1e8001c00b206031030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 803698372 1250 803697122 803697127
    0xd03020309090901020f04140310090c080f03030106270503060709080f01090308040f11060a080717090304060f030f050108030a35090c040e0d0323130804030c0b 71
    0x3650302d40049210741c04080c0e07900030740c034003089060031a43c2806648280340550100281190b1960340c18009003521401c00d000401c07007003500c2d040c8410305200070b108000703640c0100081c110b1030220110450b0b05031056134079030018024007160190071501060032881c000341048500456103540034030a50380581e0709942c0303614899042c4102103040080340042c03596660b1500000100080d00700004903401600710011034030280351814035650306840480d070103030300c00781c00141504410b80089441d4014901a61102c0080e659070100b220403a0080e215441150700600c81040a14840c9000701c103d803005d450701003402c181c01aa007200b542d80c00c0e000743c445600007048400b00c0300d80c0030801030310708201c00102681d03059244201010030407401d2258403440303143c0340005400d00d50400015804903000b0b0000c014401407a0916526202000034040009013050301e0700002c030030304904060900380f940e8100c02d09600c501e0080d400c5000c07211303411070351141c0030700001001c140c007200000003c00c10009081e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 803699622 1250 803698372 803698387
    0x50a0c0507090203400c0b070506181b061b0f01090323090d0f120e040606170c0315030a05061f1503091721010504140a0b010e0d030203 60
    0xc501c050400c80c80d401c0205c1c8031540d41d20481450103010113032101d5a04d000c0e0070005420700220b11612900140e40b9000b00190320320410200040041c402c14074060102d4101d175540c0d01c45078a030341503103034a100c40d583c0d81190000f880c500710009184112040c400034102d00c1405080c1400c0003448a8101c0090f503450101005064200d41215110310040041c602000c08400c8140c0d19070260080c810b000782e0122401e001001700c0c890500d2002504524480c8405003007810062800c0350000005006500300a00010102d000e10303881c420160481030641c0720340d03949466480d4541c00043c121a960180c03040e1000d5030340c4062005078206401040030b0025444c0400c0045a0404030040a80000101e88400c209115032003881104941442c98081176902c01402c1400b01c02d002849000e20381840064003940e0060040303500d4526240d00e090600e43d603a0780d001000304803524141e0b4802000400c0c400140b02000540c40490422414109074401c094a0703000705102c1c004200040b4050b902c0094003a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 803700872 1250 803699622 803699641
    0x1b120c120e0c041b0f0f0203040906090902180c1b0c09040b2203050a1101110d0204030507081207020907090803030106080f09010e0705130b060c0102070b160807050a0c0507090203 79
    0xda40e00903035006000026181c0080100050619a00c0c40e041261b0400301060244c400d200312401482d400c5011301800f030f103c290613001000041d0b01203200c2d0300328410510f00c05100c2d904282c804c00108200506140020220340b981d003040804050503401001c014130300035500c02c107a49003da0f00800784680640751030700009040c888008040044003402801200009600c13004071802454a440c0059001c0d9500b10194050024404842140000410200100c100f260f0262040b40e001e007045404c4559a80c810300d841e9554111008100d1000304075400150504481440c1c200f0001e107000000c00ea5141070290640d0800c0e040003001469043c14000030300c001c14070443d0841c107404002c0100b01c4a01074075560302d80c1144501402081c3c80150320a400075139910a860014000c1c08640d84c1c0d0000043c8a4001d521074002100d2841941000c130b2160b013400610a00001100c0c0ca991515803200081500c494101084071010420070000030800074038188240d1005021042025880e8284111030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 803702122 1250 803700872 803700881
    0x2030102041a07120e06040501301b090308030a0905030d050403031401080c03060411010507050708070620060f06041b111002180409020102010e06010b0301091b120c120e0c04 77
    0x340e04103c005d51030502c055640104540480c0c0c0309082ca0688403400c2e42d04030038800e02c3c0c0b940c000c03040c54003480d201c8007001d41a0481c580101101500807a0480401c000f41d039070060900014003407038020b10008820501990210b20103a010b40f04807801c0c81d9074118800241c942c101d80440009444002d0250310006241559000d400d0340000340007840310742804240e643c200180301900d002249500c3c1d01080c0d01843c01c4581c0d40c0d13040003e83c0c022031b869406803681c51324284a40400145483e6200d64511441d900203160b0f40d101e040070b040c0e00c0d00c0310b15050074024000b50640d40d0169407a031068064107011408229110b43c96111860150541c06142e07051111140f0f40480c101d00400c102c0f4001c503c400e80d4000380c1601103800080d140582c2c00101e00522140c1140341d0a0311807640003052001c0c0000c00355040b101c010070140a031484401c000b20100948400310004569a80055602155260041002d410480c03170803890700c4212108c1d41c0309486031743d03c00c040b0503045800364a680303040a004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 803703372 1250 803702122 803702153
    0xb0f0901060c0215090310092301021207030c0518030c0406260c0f04110c0601270b06030601030f111314040606020d0f05040e0a0624050f0702030102041a07 69
    0x502d4201102413000c641c854064035291f001e225501d4050401300440e000002045540f101c181940c444581170006000b58828030a12104d07440400000311020300c60700520841898581c0c3d04c1d8148188000710707510000c80c505405034140030302426021a41c0381e03441028018082d0000a502d0304001c04004945807000d49424411070708402e10101250720303403240c41e003000801583d00080d042c49a001c5c08180d8026070344060450b015140c000107070b0008a070740714110b0310708800f01400c581041e41514000c40c0d64030011781d030304101c4c180006500d96000b80d1210f00c00342803065000c241000070040d05d0710700784d0210380c8010508060070003e0041c0d140740040000a00010f4800f0803003241010006590b0340c14803030601c01080001c0e4640341c44540f1940545000307003500401c2c1c900d541042d102c1c207806030550703006440301308104501c0c10007904001c0c20350780c00c9c5040e5501e6580c6003819030702e03680d147d640c41100305070b80543d02013100142815074815081292a5000811504d49103146400740e0000c040c0e40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 803704622 1250 803703372 803703409
    0xa020d060f020d271e1406040b180703410d0306060507150507120510031205120609060303160804050108010f14060319141609060504090b0f0901060c02 67
    0x704180300103803401005000200381d81e00980400c0140e80703850341c1b1546e841c1c901d10046005180500c420080c07000207050181c84184100b032110718142403456a03c018070b1202074101c070801e113800c822220f111092180ea20204400111440c1880e441c2c00d152842d101484400c250f0258541c460348581c944980000360515107410b528207174075903c0340700c070641c0030001c0ca0b42260783d23600c04a881107000c1d403103800d0a4101400140700a00e0022502490303844075100a1ba25402c80181c12182c540c8200111031041c5070710100380010381c50f1002070001c80c00d0000d10498040c8410000100c40c005000d10121800344504090340e61513013032074001000d031030043e48041031300c0141c0b940a000d107000c010a0450150416180640c0305d581d080580b03c0304c4600090f5800810f481d140301e41c0141c42c0000009403203425170b02601d000c14000300004a4000c451485048001002070000303208841898109448449000344169180c4e0101030001d04242004c0e84800b01240c840038068045007004801506c0303e480c0301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 803705872 1250 803704622 803704691
    0x140a0618050a06020918010b030f010b1207360f06030e070b16021002010b011d030d0c02120706020703030f021504140f010c030f060806090a020d060f020d 68
    0x103581e05555030200e04002400c0319004900e04d049903c58070120445903001c0aa642c0565941d0004c07203480d58820b035448501070a1090000c14181040002c0340c61a07810381a141e6050303516808101c54a00214989080c400c85c100c0907400c0b03150039405c40301183d80740a240c481103140b07800007426042950b980094141070800c3c0382840a40c2c3c02040c038170115038140020036900c00c107000b02400b40500c0040f00940c404000c403500240254150b200300d04010080c0ca0315070508504000c2807011585021f0030341d500d0350188180d5401c4030300c10600d00c07811502c003a201e503100d440d400d03c400f805c1c07400c1174001e1001030b0b104141c10000e065116094210006d800d0020b0968071008841090f0012801403015000e040d40c280f4480d072000d010010a190344032000c008014001c00c002005000e0040107084c2c42c1007a04240002c901ca45020034100e00a4540c0401858025a95428480b1003940300c07505442c556501d480804075400e00d40010304086000e0b90000590b00d924000d002c03101c0c1d410300410620807512 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 803707122 1250 803705872 803705921
    0x20304080f0c061b0f100b0f0108010311150c0304061710081b13050c0a0e0a0b030f040f0b0906060a0603020c0606190f26031603031503140a06 63
    0x43e0340440ba002043c101e95007040400b44086203203010040200907500744950907081c0380003d55640150300e6484101c0f9088817000518004480165080c000509a40340180e50001035140c080e0074a2400c81700c0d000600e00705070301e4190150840e00a580300201249000c0000034920088804484c0d0242c802c1400c8803003103041035045651518920103000302c42ca180b072032141e5555910b00c1c00305405001c8503170920491411070000f005503000325668901040e049030782092680b5014205000b60b40031004124217540c3d03160b5003a15503041c040d0043d950800d00d1005840480c0c0c1d6103120a01c5140c1741d00c001d0103541804000e2206892b0ba03903011408052050001c07203d03140c40403031043e40003c0100c402007580c20140d440308241d000103130b20140b140091440c0006010401d05290f000406000300b10350402c141c42c0004507224031a81c0402c4141c0310750b1002442c000390084e0300c40038011400c0c14501e01201d449617035000f5500c0c01d8074940d0a490b40308000420402800d0301480340d0322207100000d0340343e1402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 803708372 1250 803707122 803707129
    0x40309050d0507120c080318120c09061516050c19061b060621061812141b010506030d020c220209060307050a0221042c07020304080f0c 60
    0x70180500c108a6107130150a2051022001d51100501201c40540342e9031488049084208421100f005018031664a010000400041126400d0402c0a0f02c4145c032a51140100000d51260406001c1000713000c1c84a200601e9441800103c4244110003c0400055080403c0a1900030107a4409846001d41d400d02115a10041050f103c002403d2082d00c02801d81c034014000d800c60380c00007500c1541c000912204891950b4020003028010f080c2080706903100850032103842e102210160007031070041010300320f56124a103c0c0d0052100b041d481818880e02c001e0411700c0c0d1000300d042412680d111000c0c0f1080c6d213421711007170701c12040c58001000307030300d14407008a02c1d05611840d55000e281d40921040074452440c1c0c040360503242004044e103640341b41c40d500c042c0140d0800d244500040c8183c0c24082d0903203204041c0c00c1085400050f8040c01d143c81c0910305000a0f0098510080034909140c03044484540c541320903004881603006503031900d007400c01c06840c000080d0036010143d802611260040c0c0c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 803709622 1250 803708372 803708383
    0xc0308041d0c09240d0b0f060c0c01050c070522050a0b0a091104120f050d2d02030d060b04050f0f1804020d080d0f0507020a0c0e1b030a0203040309050d05 68
    0x7401a140b4407130f10800c1100140da564000858199041c00c0055030744c261903419030002e84803d0007100c00b01005496401407220300d00a404001026a0085466008940c05480a016101e05290454050b00d0f2101d02107000c2d481c90a6201c1d0141c0201390842003030b98054058203500c06115034042105031021301c0042e504c45014032807004001c0d0388030303480c00c0d010403640110340180034900c80a130f070489000d24083c0e11262540000340e51174081c02d030051140c41c0c03182202c07507554840c80004400310241d59243c041e421b0000c880e040700750702c410419080c0c04a9240292001415941515522980380000340013480d00d040799414401c868204201226658000303503041c004440198007002a600c501c0402e24008100310080c2c00780f00e011542403038030659900310680100321300ca024881c40d240c2010a03a0780700010003004080c00c0031104140700e9152049005540b10014107030704900e0000c0d031a01507409500c10b45200f400250000204410306170441c1c90b80c00140030a940001410280c2c3d165a40c585 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 803710872 1250 803709622 803709637
    0x61401020715053906100e06130e0f010f0605060f2506020c280b0a15030510140c041401030207060f050405010b01081612090c0308041d0c 61
    0x4030011006107a03071902c00c109640d400c501c0d03c210680071074001c05140d001c41200ba041e001e071600c07946000880e401c4c400310307109004180f200c030b5080d80c80f41054000e25950100515103500074050340820300e040350250040e1024510010050010070070310110b19801c4d9480d8020002c00c081c1820000c2225440b450304807850784a00b08903960300c1d00a40100c03040741c0c0b14404480303411070f410207030118107101d1158000c110803150380b011a00b00c1c0c0c620018904d6501c040c4000710310480010110840412081909268840c548081c0000d440c040e07801c200c000c0100741e4109440d0340e4407070f44214196078800d1041d15003591845030356481900d03041041c01168841c50040c1c85001c0784407800011164026010780310101c0e4410310600c048070421038070000403c81101c040e00c156090050681040d409008001d0083c0c1c280031504074101500b0a080d1116110034005019142e5141c00c41d00114003085800c1001d9031190200c29515450400180c10445102c0000c41c0c04640c2c150520001100030320844100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 803712122 1250 803710872 803710889
    0x70e0603130501020f04210206070f0302070806100806090c0a06050a030e0d0c06200f0c0f03040b04060f140417100f0605041a030304050409020d060c080a0614010207 73
    0x4940d55801c04420407041540d0081c919070021540111a40158000c4e0045d40c6c10351404808240080709110041d013007050004c0d400189c10040d41001c20844815a49014040e0048443c659034480400f4580b40c02194190101000c2030350038403d549080c0101d54210002c00010501c80480c0c100040b00d00f13641d486810184500050011005402a0081c08196208070165001b81c1640100500b201594001c201da031a850319981104014454100354242240c0710780b900d081000307024100e40c0701c1d44691440e84580c8142558210350200800080014013661040203440320304d040e5010b48003520a440c04810302c40703506036074020401450103803400c60b9440132000c0410500c54101c182800361024003c0500d03424004003038503920b09038118408485080e01c040000c0311030384105001c08200e00410a5040e0400c00003000307a4a0315030001101c2d280000e015240e01d0b8600e980f000e00311801c403c038000100e14104200714201100b48110001404511061010304800000003910b5151500840e00d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 803713372 1250 803712122 803712127
    0x3090d2d120519110307020c06090a08060c070303060e130807030e060c0717190f06061d04020a0e06060328020706020c06010902040b07030e0f100305040309060305070e06 75
    0x4051045594010340034145000b00154208400c0f51080710750300e1520801a0307820700030442e00615402045910800895002d040c444480c6c908102c05e651200d0300c076652142e1100d03000726aa110a110030350090708801d030b02a0356142107250140a0390b01c1580620821004041040030300d407207444160707142c2c80e40b0032401642c64245103016540002c40c00c59207a0001c201044000002900080320b90a540c0300c5000c0907105c1a0841c4801d5544030b8034440c184400e9950441c3c40c0000c0c1c654046040e031140700e01004140c454980301c980d080204840c000718080c1511500f44029802c14240600c040c1c81caa42e10235403a480d10102143d80ba00c4098124061a02c01c0318610301c5001101c840c08000880030071055544207650300381180a900004a180001e02441d000010810202e00c200c0d01212110b5000d20b00744003050b2415075181c0e240144241c1c20150f00d02c3d00080e50340da00494903600c0d03403c0f030f1400100d5040070f0130024020341791030b00301005051034001407101190b0004103900058401301d4141d903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 803714622 1250 803713372 803713457
    0x6010312030f0603120e01030501080d0c06020c1207030503100905010e06060c070503030c010207110901030215030702030706020409060608130209060d1b0303020607110d14032a03090d 81
    0x800070022680080d21100c80300300500d80c05588454a5441b03410b090760705105a90300c640c540358868855032892400b240f8480ba41d00001191500a803071404000346c20355450b80440d030403401282e8410141100018400000c202d50b00005015000240010030410001c0b50304000440c0000d040141c0722600c1b511000c50b684614207020840080501805400c0e00e071a1007082d84039a007c0d41240d0400c54400641c00030843c210300301100c106040b00e80041c0300d10400d0703501e40f044c59074541c4040d00e054118007040001c5404544036000900051950030720018860341740240040555001425508080c489460400e004d6601c0c0076069801c02d204407814152001e4929126040c1c0b2041c20181d1200000464008181500412114820941604e03202600380000d1901a2540d80f00080400410402041511480180c102840d4481c0b03010004000d11078810107850030300c0c0c06502c3d011440c2c900c00400c0008601060102c14105500e90500040268102c01c0348204030484140544030b5100d94650b21 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 803715872 1250 803714622 803714651
    0x80304120f020d060b03010c020f030316050415050a08090309181008060901020a0e0613030b060d0816050c0a0e06040905012304030e09090606040c0e0a0e0609090601031203 76
    0x2500c1d03008101040d0540301e40b13024030180803100f01c2c40e07100754a80381c0b440010718004100703522141801c0c03001e18a16901c0301c10f081e507040400c1c42884e00704503080c030010501030340002e542400c6506503161180c5422070440020800f2800a25621283c2c2007440740305120b40300d20702100c1c60044800307403a00003075030b0341c1091100b440860b5014003150320400041c0003e8043c10360003801510226524107103c49528805d004003442404508886a080d560080000c5000503100c1d5800c000c00425040d40364241d134031007030441e40000c0503448454006082160411108000903600d6203030650b040b4134560314010040200c007030000c20090103a0b80310000d0710204403003035005a8221103160084195602040380700780c01004112822404074007000400c0311607241c8034880340e2084256800800315130341e600040c04094072003c0001424000004404030844c2d6524059202600c84c4c8143c0305054580a01040542540039146828603089a4014008100d20025008091039141804105030501c84c458 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 803717122 1250 803715872 803715893
    0x90221010c05162409080706060608010815101a030f09011808070611070c0e0108010207080316090b0307020f12070b04021e03100905010f05150d0201051201091e0608030412 76
    0x610b004d82d140542000401c100d01006d000c025002c0c403000c11645886180c184c41d610401c1c0200034071307503208007059030000170000e1825521403101c0000c01c400694980b2003000c62403010101104507103002c0204992503040190aa500c215a1402071002111a038907034000408035120240c18540001101000d020054114480001c0400d0a6544c0e507c400d0404851103102d60040c2001d100b01180001440c41050090702d409a400610091075621440801080c200a9600007014880c003850300050003541c8801851080105070050300904c89000c401d1410300012682c04202c03014203029480116040700b60103a44142d0503a0342c084074104401030b0022080803031790340702e9040c0305601003e1120700c016004125554864070080c00410035542c1e41a0a55804a4290380008603504e2284c0f4a1f15190485441b030b58010f050007403500e01410f0346100281002d0b000751801645500004808541e03111051240c8070080700304001a40c02c0c52040394403131003184640340514803540600c6003402201c4a8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 803718372 1250 803717122 803717183
    0xf0114010f05090a06020c01081f050909010902041a0a06050720030a1407060e090f0f1e04140606100f03090809061207030e150613090221010c0516 65
    0x4070781c04c259920f0310000e42d00e038180514240084c4120000c00d56038421666080c1c00c0a00b03212140c604107080c2020300549400003481e0319165921081100b025880b18441c51030310400a41060401214180601c03046004960068040220802c402d401184884041d507270a03009061400720304495120000b40351404040d8003a0041e04207034a003295111002030078208542c0251a40380c0803032407020411003a108101c0c2c1042c43c880c441c80c00276507042500200507a100c5001d5860544500d05038501442180702210101c5020031a4404141880410482c80b03902a07021600106542008507005202c000003a000300e080c50307120110041003113988010b903645904054a19616014580c4d4655107400095820300c0c0424509100c4074814070703021902d12024500085c400465850b0388c800d0081c203468980c46e40803051360f100201001a90342d00c150002ca01c8040e81030302484116100c0c030a0850b03030090140801d0200c10810f901c0c144a1100d00c00d514503810068030540020b418034186402e104030b14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 803719622 1250 803718372 803718379
    0x50c0606190510020d030b2b061e051005040207020303180312071101080a0204050d0f0809060c0303011a04030f3002070305100501141903061406090f0114010f0509 72
    0x304080189a0000369817030a0801d03643c040c01144a200d0911040e0a0401c013403054106843d010303521003001c07085095240c0780c03141d02e000910a448184140c903100d841104c414406890f1801e0199002e0802c8103e00980700c00c4804500e0001c8540c0026541c0c071403500b1108912440d001020129130b0248a000441e620a600e5150b6032125480e014091170724051106011410000220342540d4a600c00c1c0d03815540043c200c5040c2507610b49070541d60445440044910340b500700285c4101c3d440384005810024400c5009603103d50406000c0c01c105e517141d62941c003000006000800200300e443d000e04040641100d11581e184245481c41e0b807441d24184a00300f080c00d0712880c410501d50b40014107404490160042e00d20150f038122610307050314000e200300710f154110303070070800500c0c54015401c1d04281d1070300e1203c0a040e90341e59150401c1d40e2809441040e000940780400c0910f04080b8202030b8070480c2c84440340440e41c104905041400c0c1d000c801e4604001e00310035502c144d04c0c0600100c03249008001d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 803720872 1250 803719622 803719639
    0x1305010218042f0904020705070b0a0924030c020f0d0905130207080f0c0312161106040b071202070606080303040501060e0c0d0c05040504050a050108010c050c06061905 74
    0x4a21210011080c500c054000c0d0f250a042080000740414207150b042d102c20207440c0101d007140c000f189103402044000c1d42c401c2d030800035040080d00c00c0000d00001e100300340c511522150a20f0014081c52125881440c9220390806076204c1c031135400ca5201c05102840c200000d00c000501c40c120b180c50500341c04842980300d24031048440c2900150458112203003265180c030f9060741c034595074059024140c0002c006050034481000750f001c4c044086c05115101a040741e040c280b9501c0f1284498009898210b038060b080c03103003040d1540e803050040c2c10780030101004010a044c01e607078602c40d281004090500b04642c104541c0c1e0030180c6501240e5225030440002e0051139142c0c1c0040b0340340c0e4815181202c4541ca40301c00028404828a0404d20440f0b5101046040903425031106018000382c0110b4003c0044c1004080f0745540c0354414140240b200400c009031035810911003d003115048000441880818406010407280c0040e000c1d40c13029050300c0e0b000840d24000e01d001c42519058005c81c1c1d000344e21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 803722122 1250 803720872 803720887
    0x6070f081318060510031e111201032001030c0203070204050c0d06081b0a030c06080c0f190e030c03030706021309050f090105010501090e010504090515070f02070906140913050102 79
    0x11500844140d1398220344099840d130403040c050b4111090501a881c10450402c91807444600c0c5503c0343c1e00e860006562a8946201c11900078400c4d0401d8100311016408030f03c0d075041c3c085052140c640300e0902820304001d07280030018065528000c2502c024451a100c000107000762002c00103459261160303160a11185842c0d0701d200303448207000c400c5046000380c0c5103060002440d000307030000d003103e41011901e0740b09401c11030115801c0c03100404001d1521402c100201e1010402d100400249801124202403c0c81203040207149185404074248a6409074150041d40d9070048102c0345810b500c0040169260410240702c280258264407071401e691400007080349500341820228400d407000c81c02003000b41e07210340041d1940c01c4140a0400790000783c0300140700c00e007029417001031100d00650880d088441c5064140d00c1e240d408a82c84000103c1c00e03880031000c1501089508064000c40d00c0a010036418618244580310000020901ca12140c0000c9507902200810840101c1e801000a650700c800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 803723372 1250 803722122 803722169
    0xc060c0e03010c3504020607210c02011806020d032003040c06120e060a0c050915090316121112010f06210f0201110111041503060506070f0813 63
    0x10408015140707050440e00d43c102c5880368486100e800c84403044d4004440c1c860340c00b400b80681090301c044460661009589004041e000441c200090b0131350f884401e010194400140b00c0c1547c484800503002c4000401d0082d03036000300d05500340302e00c0c030301c1c000803244000a107144852158281c0b140e00404000180001c2c40804184c600c281c6002c1c0e00d0f07124a0480640824080f100700180072441c5800510204101d4105908856034802032032070b0040c00c1003420000107481401c0d2181040c00c000300001e6801c9681030034010204070121550441207014a491115000d04400784401044d100b1445001040c594866201c1c400c101c440e64003c1008201c04440103004114034003c4070a00b410b8900c00f81d24150304190b294001e00d90010303034401c0100c02d0303600540d8242016124910b4175500c42081200d00c4541901610080c060503020024140005c840a022030b21207800c403d000d840c0c100001000704001040d82c005150f0b110b29500d50703940074100030700b54007001504400e18102950f0917450034040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 803724622 1250 803723372 803723387
    0x30b181f090615051c05090c060417210313030e030d0806031614060d061809170304050327060c03030a0515061902030f070818060a090504021602180703050c04060c060c0e03010c 78
    0x125038000300c420814cc611391845901080c0400c0340c0e00f0010400019120000fa14072a000140c400e08003400120440400241440c051404000000c3e540200300030302e40c41e00300108015135940064900300350382130146004240c00d2a05400e8042d080000340c21507000e0940d0302501c02802c0c0c4080e900080761729210310390702521110030107446c075040103880c980031070a200045034041e65100e00210324000c0d4081c3c0e0100101e0034075401040014001d4003403180364458000400b058502040616541d1800144440c100c80000d802007483e4400000040d1264450000300d40110301c5000c1c049500c1d00d000b80e412465803190040a0103a508042a420f040086190140042c1c000074030010781e03103042203800c2c40071500500300780b00c00164100c8e070100064107003503000300f481c401c1000d1a018582c00f036401081c1c4504140f00c60f00051031160041081140c0d05210305d640000d101114180303810316101c1c0c005c001143d15a400750086070b50f280038020940c0203000103506000060001d01c8002d0600c5d402802c0603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 803725872 1250 803724622 803724659
    0x5061815160b090c0910060c03140f0a180e0106111c2001110904200304080403051c0c0b0603011b0504080d030b181f090615051c05090c0604 62
    0x3481000c0456005240065400784244003105031000c08a00e001011209980e03002c40a81c144080c014030220600201c000406450340008801030b07442c0c41c003c000605008440171480902809c0370402d22208040030b1410381110302c0c80c40d0031900301c4490701440341442402c0c03070407003155564503800c8004130b13400500d000e40342e50100d808100250b1a034030400d82039401810520507001c0040111070f00034580350348804000d40418076540a41c080342c0100d001140d100303403410380d46c0600210707003041004800c00a0601040c00c0842050900d052000302600b8140b031100014184801c11002038029103096008848000c40c091400c1d202c2c1a004001402562050040c52880e01a082c202006180240240d06103203002a0054518100a8594064450014210100300d810704015504105104e019040c0030b00f14440f4001107081c0b40140c900b0040201030300c5c8000b0b02c281401110022100e07a040740032261600000840c01d07503900d0b01c0141c10012090f20180e4402404a40883c2810000141c108003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 803727122 1250 803725872 803725891
    0x240307020709050f13140f1603021c0f06020f0f07030c1506050a170f030301060306150309030e090408090409110a1a0a140f0a0507020a05061815160b 66
    0x201d488540ca1310324600c0e412540d2000c000d903101021130000f085592102d8a003001c06007603411101d0041c4e0994100105040500c840d03075514034040c030541c41c21307002c083c01c001c911064081c0c42c2019659562440208514090100f90b0301196504010001000f207442c1500d5103c034855540c2c006103000b5121801520080e500e543c500c0c503102c454484140b0500c420303035a000700f4070441c80c1d241c07040c5089090100d81d05450140600e41c1080c2c00c400b01000694040c003040e4402082c0182490440011014052740c5070040500303140c0c1407400f1079042141403a2400c001d940100786981c1e1307401c1c80391040c0701d05808140c00616100410051024002c1d0100002c40e08484419040355039480c0c5030405a408410960b0701759080151350f1440b8080c108030160808000e0759942000c01a0041e4001500f1041038a4041f4200143d80002c40c81e2080b08000603007404c960349414a0314075282d0281000703410002601940c1c4036400855060141010703156400703121030b04004d11404a00d01550385030015a644041c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 803728372 1250 803727122 803727131
    0x606120501140f120c0406061e0320210c0d1103042d02060f03180d0207150903291302090f1f0306020306100e0f240307020709 56
    0x2c9542c001d503580807060304020310b07404106580d941040f0b03004804101840c00e9124170682e041240d12640a000010110340c0c07910031fa100c41404040c0003080b40510004109860480c211091052030400c4000d40c050200c000c6845170030006190102c1416618164034510f2204200401010501c0050400da680c54000303101155694405100c0342c081901e0040c41145644d103141803a58405041800104c1c20711400d42402e40d00d83c0201d1617076481040c4444e841c00c80041000f800c00c403980e900042900407030004150080040c10001c2d15540c040c06a108030140340c1090300e402078419010980519008103610350f20420810810f480300c80411101008840f005001038210f00c0010380748161141c01614144013603554070781404001ca802014600c3d020240300d07050004032201c050304005180705101c0169281420010800c40c40342c0242e01c0030070451a903415070916110050304400c00f24056900e0101840c64034000c80c0c4070440790300071025401c400f100700004a6400030356101240c441540030270 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 803729622 1250 803728372 803728379
    0xb040f080a020a030201030519050403120b03060f0705030a1d010204030b060a03030509061c0905060609090a02010507140106172104080d0f140706150504050403080a0506030a02040606120501 84
    0x292607100c4031002039030028000000f08007650294112035408a5807545407010f4a00b5a070300b00c0c0403504143c4041c0e000804082c1c2c1c50b10b00b4442c0d407180d0035601d030048008140354905400d645840d041c000340b04004000000c0049070b5660f11a03008480b028a00034040d40383c034140c10b0a10b40c003c1d0024401a50017510420110703565080001440c410350b6015510b051502d0501c0c000c2c0308095008401040801c0014900303547d0031703010352007501a210301c1940a40803034140700e01003000c0050042c00218084d04101c2d40311b80103030780010480d0400740c3c0c00b15040041c040707507a0805004000035440202e0380248044401c0301c00c1c1d008103034010456160402410301c0038852100b1000f6000740c1c01480525403100502012443c01548100c00c080418545280720744c90030f80b41603815030010751085540741d4a4000401076064a00d03a004046d11003a10108600e1a06480042c81d421016003c00151a600d0011035041d0310305004d02841d143c0c000c0c01c144206507a5040051102e108141700105483c07600c400070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 803730872 1250 803729622 803729639
    0x6031b0902040b0a180e13150b030c13110c100509010504150f1e020403020301060b0f0403031b1b170c10030b30120c0a24060b040f 58
    0xc2d002c3e2000041d2240c200803125100340c542441d005074040c1001e48901d00012110781404805200f54100402083e203c6040d180c002500518a1030240030907081803012880c0da200010103000122088559a060310074001c2414002d08002c841c00c489400e000a61001070b160004000c084500710f490100320302d0313032001c0c4014200d0300c003584d0040a6043c020b008000c40f1040d60402d94114044000c00200903004900500e1440c804a540d080f4854001c141041546420301c20b20f002031150124103454421803850400207403185010060900444100441040b940e0140900e0204d5001100540440640450755548201e921848046c1d10203c2c0c5141c0c0b1080c008200c0f40724403000174103002d01540a601d400d501a140000b00c213604408d16001ca0a1034422080040c0e0b04040aa01d88007a2030000300490360a1040e080c2c10183c2d0910100003a21603a0300001d045909640c100c40031207414500042d06000d54034070584292403043c280400441c003080280c000304102c80708100e100050710b5444070789 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 803732122 1250 803730872 803730877
    0x21c02030304090c030e010c18090203150d080d0504050606090c0c0607110a0204060b0d0b01180e0c0d0e161d130807080304050709061706130501020d06031b0902 71
    0xe4050700140800c00c81401140c0000f043e0f03512908010400c9009542c005086400074030f22140002d030aa4240021528004248405854002015807651404412142c0000b40240c00b0a0003151030782e414400780720020b42566040355203100c092001c2e0410b42821a40c40d14143e400900c5400494081001c4104680c122840306841001524182e520350100b0380380c5036920142c0006034058420700e100169254410240030f82034050419480c0c01c580803801003111b11400c0300c10305012409030b40c3c00d0b0401080034120220340f5003885884041c1d549101c81c09150203001008020a41007841c00501050301003004486181012000c092203580c65000204180070007424007101e0550401051280c5c65000092413941e0107060858a8101784e9581c0f0b003c00d130300450301900d0b581c100d048188500c804501901d0024200b0720203c103018240030401540b111750141001481628013402d8900b0070600b034050350010002c0c0c440c2001320b241d59043c01038980480c4469032076049003080012a0000a0384203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 803733372 1250 803732122 803732179
    0x30303050405151302210a060f0c0e030a0f0201050d06080a02030f0309011205040c12080408061f0b071103060a0b18101a040306060609061101060e0c1308010908030402 74
    0x41e00c81d440460340d0244030031191100030001103103c240000c6d18001808014400344180304220003d8090504480b20040b2000c3c00051401c02c8145c480e0b01c0002d0358005644410342d6000b0815401c0c80d041440103890f0340c4a0280d056880c075051290015000130b01240009110303000b50300b0b9408903820745207115100d124210328035001c20303000045030741c00554039445641e2080c4a02d40c0e88a43c6600c483c903507035943e038010b0811151154001014044805c061040c00d400c2804002d003410b0454014140c89580c040c0790080814440300401d98006010500d010a41d0050000e010f82c3d10600303021282c10040c098010545000d0010f034114141d50103a03402829105034214480311445c94104900720303002e004058500720b1000000d02001c80482c440303114103001000c098503820031051400c80b010700204420f0002440691600d80200f1003075100f8042c440c2e20041c803504040d03954001e617001c011448019007124143d50719004408041011440055010f9070084513000844c0c07140315002c0741803082018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 803734622 1250 803733372 803733391
    0x4080d0e030d0305190b0f130c1d060a0e010201090c170c0d05150702101823070501080c0d0608150615040b030a06030b09060a0e0d02071e0e0103030305040515 70
    0x180d480f041015071180c1b100032802400a04001601d200041aa00801c4100d5010964500c04804007603000440716003900c0c0300f0022048903152070b10014100b8040c580c03044042c0302180703c3c0f5807034a078400e5101070801c0341d0100900b29400c1c0c4443e24007404a41d0400e400c280c9220f58010300070289040c80307096902a5001d0010103004d2941d081c80d0100540180040b02035100f00d068040a4000c1e500540c00da20303048010400c2c0008003410684510a4542c0504800300f4007801a4005050041420810703a9401e08002070b40340c460b056244c420b4030400081e90001d5203043c5000c00d551801107007040c4000d50f201c59140d03281d110241001740d070a0300c051340720b0041241000304000302110480615404203112500050050b030701d0301d4074505501c0448048035035800260400a801c3c05034490016100720322802082c662104010103961400d003802468031035a08884e00c0c0d0030000300710b2402d0011348a084042c0c542942e49180140c0548402d80f011989401202006c980e400646140c0034480c1c116903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 803735872 1250 803734622 803734651
    0xf030f090807030309060c030e1b0d08040e220209060d050c150c010605010e0603010315090606090c080a02040f0e1f1511060403171b030106050d0e0f07061404080d0e030d0305 77
    0x70342b1180700d07110b00d00d01076084920b8a051501040c803440c0500020610100302c0240c6103010a0804c00740c100c0a4016a9044161014070000d601c800e0800d41d4002826666190803010034108a4603100300c3c00b600c1544801c51004070300c056102400039180d004180380c02400140e44407070040d107100c02d01c28001600036405000400115141e02c10580b14121410380c0081c0c2c210190300c0c1d2001b40e82c00fa4100484041c1c0301d4240349151540504290b5124850100850a040c2405d850764003083c030074800d414401c503400e00030500000a0390051801a00480803075900b035942c41c602000340e40c25003c9610301040c2d1078142180c40c00000703e5031622071a07041d40c0c0c2d079080c0344410f04100c180c058043d2110310146080025090380c00d00c0c1c000294082c1c051901d5440d00d034900400b800081e80c0e095482c580740368001c000c9080000c28002101000e07206030f410b02140001d14040c10a00d1801140d001520340e1280f4580d442102e80c101c1c146611018041d0291000d14042d010140e00703498098410f4442060355 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 803737122 1250 803735872 803735893
    0x80309070905160f12061e0e0a05100515211e010807050409150507030b040f02040f0e220c09061e0306240b04140306070f030f090807030309060c030e 66
    0x2170f80d1461030000c64007070005005032656410b501c00e51400380c64494000e80100b0911031018460580d55100518460901061401102020b00708113140319240c040c2c241d040c0140362000c0d034601a036460b020f03080c8241445007041d015811568206803202c01884403101d43c2c403086261301540c150b050702c00d014010f1101524000c2800b008041440341603c011400c1014054941c0080c0034a80c0284900e83e00440c0b408446400c000480d030003025105201c901c104006c009035800c12181320111032101d405014503940c1c440030401c02889880469108506602c82001049600301226081d1160600c0401109407145121170b402c17015800104a24038151004100103450303a000003e2442543c100d003491b4050703000c01790144210640210880040104003803050590581030b15020071002c50040c02c01c0d080250700501108000028402010349aa20444c42408690483c581403603100c611360f03644085a00b001002062008412900315080030554030721248030f07000d98003144c0070500103000f00154 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 803738372 1250 803737122 803737127
    0x30c080705030f04111f110307050a0f061806090b06010c02031e0f070e04110604150323091606140924040305031305010f050d020304050109080309070905160f 70
    0x1005008645c602040154080542c4848131084080103042c0c603240c0003034242c40c2016000c0201420021040da00500c034460200f1400200c80c18006d40003103c6600440841c18020040c20303125040c4083c0c0d00740c00e40c0c488200051948102c0000d4021840c0307500c0c40e1600d034011102c1d507004a41c080d42c076502091100414400260f02c014141c4505011541da40b042c1010300380c20560340c0d40c03010782c81035440b20400c0103001c1c41820b00302c3c01d10400c0310007174603240c10960b050300c40582c4600c101c010190380381180b690a0405601d112075440624180c1321103131405000040ea07a500c8081d0340d680e0f5070039981001901380c1c09500340500645003400c40c2401e11903444240881a0040080c8155015600d03094030001c80390080208059400750f809181e0301d0100380c9000c1a07013203040d4005410440140c0b1802080e41c1c0c0042600d040c01d00c001405640c9450342d05105000d04440c07280039145500000c2400000c940010b8254110741599205010a070784d50415510070b40714404c00280890b0800c15040e40e1540b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 803739622 1250 803738372 803738401
    0xc130e0106180302210a02100c0213060324060b0304080702010e0f0609040f152c070f11010b0405010605041701050105090412020f030409051522152103030c08070503 73
    0x5001c0411a01210000d80016410000203c8103002027010a91a9019420000c540e07000c24000c103a400d1000c0b51450b48c55488010541441d4801e107480c01d1582050360086802100092102c910595101d04060030310a040754410802280032454a00d9043c2c51403c0074086030351203603030003031103642443c260205000c06002c122503040011030f40c82d2020050048010300350006444002002c4002e003101e410486007060324019810b622194035420001503a521090364030b0390814a207401201c50344c1c501e58541c0546070103082d0741e5100382450004500d07254080041c20844034090984010014035201c0e803400c03a20f0a000743e580210000d0001030200d0200302c8018143c1c17010f841210289041c2014040c01d54000380c000c0849603841e803041c0450702940240003509001c007214030105400c0768511800e2260810080c03114000e80ba40121400c448032000101c0081015070a0040c0203090002e44d00f0345a5804c50741100420b280240940906201c0e500951044015889142c55511940c18061185 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 803740872 1250 803739622 803739679
    0x140c0f0403020d0c05010e010c0b04020609120114040203010f020a02150402190602030a0207050a180c1103040807030b0f06090f060f0d080c120f120c130e0106180302 73
    0x81104000010050702c40350560032000c0d0040400c6803019003408001400c000d00c0c002014104a000c50f0214082581015000e40065048601c02c0da281040d4002c5081c2a040c11503070140c651810400b000c002106100c0b1a1180e44214000c1000c0c040401850089000c0c965140c03006034032900c450700210001d00e001c0303908a40014010404000b2001341548a24155089480180c002050403000c2940422a82c000350030100c424034001c83c1400da17080c2d50001c1c2e04110a01c441d4540200c40c0c0600d0040c1d07450302030301d01306409032540d864940048940c1e9005030300c01145d1810b004000100c80c442c1c03030b405860045400078408040764840745082180ca1030050001a4041040880d41b040c5641c0d190840c580144603405407603d88200c08041402c200010004100c0c4440410040030394a800d081281c4540f02c004c9100242e41d222440b4030b0045009000c580c41e1000e43d4510041105484030070f013141203401503601d005422802400809182c81140f07c000e40001d083c24030b2070400004803100c001c54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 803742122 1250 803740872 803740897
    0x50309280506010605130503030f0a030c030e0105090c131b0f180315150503120c0708070e100603060b070213091502030a0f020702101103041505040f09140c 69
    0x110303241d888060820100782d200002003140065164001c1c10043c42d0440100412070146040203031030030300c000e240e2055842a5080640d5483d81d40801c9010740d20800400c3d2940c0c008200910341442700e255205100b04100d0b20607000007242242c0002c080c0a4810000b104124003290099414020740754203050320900d9003804010311455101110b0120028021405203155603840410345070714000710340e0449030b0780c0c0f8860b10004051202c1d8030002041c00d0300d1036200d03c14555600c10710740f9880c00e0410541003808180a070001c000303551070300c44210f14000c0d4855507a01c01c600da44c070030090701121801d11480c5141441442004091700d132004054045040c0c200000c61820000d9491500e40010000d4140b080f41d404010320003441180c0c46541c0002c0402d0b20218a440040d4000602611403401e80400300182ca4040c0c0f903414009000341d800074076020150720020724807260f0182c40790304903005074030103907034408400035800160340200401c1900c0140b03a546540c82e0f4000c3d080d1150701c41080c084c05c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 803743372 1250 803742122 803742193
    0x705040306111803012c03090406030609030801080a0f02010f11062e030209161112030417031315060510080a05010f0302061602030a02060721050309 66
    0x220300c1c01d01030400300c4180010300c00d0b9501c02503040c3c12038600c40b55030070a000303a00d42180e4802a50149140d070140250811800b0f82404403007902c00d10b540b240303401464200d030408400004100c0385811200c25988680c680011503a25518030700d0303031040011f00103005200250b034081c0141d40225a01d85000312640ba080a0701001180130b00c1c9010b40607511403812008170491554040351500b54440300c0e50ba03a9822500d541c4c40c43d000154001d030054007410411200c080c8040050307000e070328642c815815803000c1d0b90181101280030010b40c2c200300c4d0300f80c1d01c08942c0042c900000c0890710407248541200c100c0c0e06894105a140c07590010080044541c1c607503030780d00c800308480e034800407011114152a41d640c2075520341071444005448069204004d42a192141800140d94046c2612111041d154180408441e81d0001a2811100b0507010b50020310001e069414011b83c5c4042c0d90103d06010400440044803880440d05c9120468000b6182c0e003002c40038440040703201410b96041c0c42072948411 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 803744622 1250 803743372 803743379
    0x904020403230106090c0504141216031403091507020102150a090302010b09040f0201080a0216080a030515010e120a05030c012405061804090c0602031b071d070504 72
    0x2442c600c041c8082c054005000c404401010300d090081002911a0184c280501351800303074003070035500541c0a5000780402d800701842d550b0b01c84609000da1138403c01c04954001003501c1800712280b0440c001980c1c02110300c3c11410010800104540e80c442001e0200c1000d1211449410129003181d40c007203045002e0b60b0041c2c1d111000b140070042c0500d40d02e01700007640042501c1d006c0c2c2114000c0c400c150040c0b50450400c000f0510f81082501110740a003007502003075481c1d01c40400248182d441d0005001000c910500500c440030303029000c0703e04661400c007c00c1e106c3d43d02410742c00a403c802140060007594290846041030f01c80c0240011b542c40c100da040e410182d0301c0e02d0454005c42800c3d1002ea568144448602121981800601c9140c02417890003901300b03408201148140001540803003440a0050f8a94946a02c1001c070035800600340420b00e078031104000c0d00c903030065500c08060f03803010314014030458000c14140111482208000c2850340e806011840141004100c2c409200e418480003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 803745872 1250 803744622 803744633
    0x1b0316081e0a140d120b1c03050d020a12060e0402150a0306030609050c180f070302031009020c0a2307030609062a0f0906020c13021902011505030f10020904020403 72
    0x1d59401c1140040c0c28102c041e03020040101c02d0442100030810700f00344d2211031603110000420703c40d40110948001f5501b180c1000e881038880e00d00b041800501c005030040601340d021562240c0b00c010b1a406008843d83c60040461140e4240da0295020f20003166601e0b456180c1c1006082041f10340c10007280f89540d035280c0e80308580f039032002914039802280107102240741070382c86110403000044104a503404c00b0385280100d2030006100c9028181d0000c0032031403079294040744000501c2c1685c419980d23050b0381c00003103499421101c001c403090142401111100031a201034006600c9000c0001c4c4206460b5031560300207880800310594205d076503180401018030204d0003604011400c1440c4081c0051161401400a4014030035a01040100d44060100d0f903808105800340e0750b401ca52007840d038000c0882c03c000921541c1c6030221846600f0307241e00d039541d0701034110001c20500070a541c961156100305058858050001d80d1041c1d411084004141a01c2580074010510010b000142000c0d281d0703542 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 803747122 1250 803745872 803745893
    0xf0622150303030209030601060c121b020d0f12050c0d0503150a080706020c01020102070b011401090e07090501020609010902090c03130c030309030203010f1a010e030a051b0316081e0a 81
    0x5900080d00080c1200d034070300302000b0740c500601441c43e001100d50403d0316041040c2180d00030b801c0400030cc020000810440c10000c0c016459002044e03000c1c0040c0318038240d002c0120301101202d5088081c0a0301107030782d00130030644403802c58240c0a40311561161008440c60351000344044082551204100410b4491a00041c0a03008000081400b01e040c0b20000e0b10341825500d04a0443e0300401503140003c0503428038031b04549070109481000c1ca60f03a00140d9400e04503410868541c0c0a000c10413220540c00540f0504a4400fa000c0c0c07071136900c45141d910b0031b036000d03d8000f0703400469002c04900c0104d04040155404124090384103080c0d08240c2c1c0d0382480c00c0d8960300030b40000d5940d01c0c4c24004e614003845a940c0b00e800c030700c030104175592075940351028481c00328104506100000902040742d407006c0c0a034207001503004040d680000c1e0700340c140e08030032200680c00d107010340f055124103009484008006070940715840c006205c403500c0304403060340c290301d0b00b404200740d07000746016a00044c0b01a06c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 803748372 1250 803747122 803747129
    0x3032701051003050f1b12010e0604060615020f061f150f0807030e0705100311041509050102030703091211030604031d0f0a0e0408070c0609030b0f062215 68
    0x1090781503d24605109181007100184100c0c4c54103c1c000030f9075900c0c29189548212031040d20002021000c8040c0c2c6401042000400d14003030081900f040100940c80e407000095803190b0821100901c0c0b5604102e1381c424040388103405a83c0b110021804001800c80c80154a001001c000075803652502500680e006824108401140360110342c2c03409160410082907001c1c1040c941006414420301d6441daa039032041c13090750300800c402441d40c88003520035000301c070445018507d80c6669aa40d000e00d00c5182e00209041d8000132014100441c0710f40c4040102ca424070740507500d9407080c81c100b025640300c3d0700d0340040440360a5000c0c401c00c602a10140015445140640c50b028620030003212034203001c18594912901c40c080203008500c00f0b944162440054958059002940340d84e00e29040d0030500c500e075005004140a018006101c50380803a42d00b081da446a01480c000d500d98100d03001d1110320a68045500885007803404050541c200144800c00f68451000318800072a4000d04800441981 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 803749622 1250 803748372 803748391
    0xb0603160305101406101d060f0c101104090c170403030b0a0501091a071502040f030303140f0415061703090114040302030c060f070204140906060307080303270105 72
    0x240d1501c05510301c1c403c4d140d04000d0b0840d40c100314a0701c0c1d00060200c0c1c0c1580e5200c02071101c044400381100708000b08180034204050100c60b17460540c568107030070a8000e10548d4000d8400d502e010300a8803050f014060304c641000301079506150405a0503c06480703c50000300801280c5492344c1c00e94803000e59080d0156000391030004621041d0814040c2401558008a040c0101e00708200640c220f00a41240326485808603181c40314898900511461b508102c1000054000b00f0007095503501c8244800c12203110b62000c00114505035a0720302c0310f120840320f01d58201c80c0d04000a0200300501d00c40345100200010006020740c440d11140050101944108940c0d800490340541550b0000d41251400224680c160301300f134910390000350384002d171490890040c0d90104c0c1c0e040400b14414240c451180e0b0050060022501002d11340c00806801c903600ea00c94851903002c10310032704001c18914291070410700698a0b40d5200c083c840c1d01e203603142018610b5000f1a03413103002c6a20342803113094012411036 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 803750872 1250 803749622 803749633
    0x303091517040623040b0109020f13080321160c03051b1c030504110103200a0503100b0c0703080306120604050319080907180b03150a0c090b070b0603160305 69
    0x400c1c004d00b18015014000d0520b2080180004141e60030001411240ca0702405641d540e11f14250700014010382c41c1c1c1c1c00c600512148041500310010016120765020b5000411565440c900f14600910041c0c03546820810701000c1c44030614030401311541d099000b03051403450a44560400c1c040d080a134041183c050300701c004841f00b000080714140b56411402c1c58107010b9401e15450b038a0082280c98a018141540d588000d08012090b0160318601900140503544038080710328047c141c2d500840f4408928075104101140b010241401c0c2d40c80d20030f802d00149200341c03c55480c298507030300282071a64004807c01c2c0d000e00c04c0504000c1e0910940c421005552100640404108208006401c06060203116020449143d03000103800d0201e035284459280d059400c0c05010005060001009806004074000707801d00d400c01e242054007130202c0c00c50800942619060440b284859405003940c0c28030204a0b80c0b01044031a403ca42d045100101601c500c19403419000c48030b100150320407251500403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 803752122 1250 803750872 803750891
    0x40e0f04030e04110d20211b070b15031204030b092b20160605090a0e040203030d020403030809060f1003030507050705030601080a0b010f03030915170406 68
    0x11440b0b0b925001ca0079076050000d840c10003000b24141c000c50100340840c07541c8000600620385009580f0034064020080d42c3d07603640f400060074840f214655600100c400141010a40c0144142c050024106248907008e0074603900d0b688014224001408001100c50104074078500d955050004808044c040341c210381e9640c0c0340d80f6007403003100c0005102940c650408071f401080c0705035103e05105006d561034240344030034035519016500e00d84144035940d0081d01c90405c0c019805c20000e00c9410940502181c0c4e8011a690102107519225890b011a04400c003000c040000b01d054510903a0030520080c240c03410003804e03510703000498000f64030540004143d1428088070b200144880d0340c20410714650012680351610703054005204a00c0700070100b05001402e071003030000500141024000007000c3d9961561348501241c2d42d62030724030003034a4044905000040492110981e03008480e45901c1d916981482c0120840001c1c003180301c00002d021408003d60041c1148404492046110f444c001901403003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 803753372 1250 803752122 803752127
    0x110d0e0c04060b0301120609120807020610062f0d0507150204030b0408160c0609080f0c0f060c0a080f0d0b03030c15072109060506030304060e0d0602040e0f0403 71
    0x8502000d03009078038040080c0701d4144014122030640c1c011003907002a00d80e141c5404002040d442c4c0c4c1c0509504540c1003030b28805a0710111007801396681d5404c90300c65480d44802903441052900c00c5401040400030491507160141b00c2480c11941070a03245942c46003c00c0e040e5040203076502859001031000108241088071a00ea0326000c42200c160850a26045569040044902500c050702440c00403c0e490032407030b0b26640002c000c0c1da01002c008403455690300058513504a0303004000050107820100c03813a2200c00100205900c10052804140409441c28007803190710158019001d40a541454000300703000900130000c0080c0356031625a1403001c882c68130110350000b404988030782c100308425201b050000a080c000300c50200d803d580d0b9601c40110943d908980d43c1250204092010011003881c445548841e461500582090107569541c80c101500ca00c030354001d92000c40c04a05642185045c80154045c003140f14110041c0703000d0322101c00c000203142c2242c4d403201c03990f07211081008041c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 803754622 1250 803753372 803753383
    0x106060f02070812030411300a11090702030f04080a050c09010308091e03070e0412020705060d0f0209130905010e03043611030f06010807050d0c03110d0e 68
    0x80601c040c0141e40c1c01c015034180c881d5601504004000d03004004a024401c04408500c1d080600030120004450000f800a0801003880200920402d03080302c515488980407500d04a00f40e40135656100000029040005103c0c02408a20452000b031100200104032840103001030081000240a029400e150a17403820115091441c0a526072030010800200c0041c165068040c0803100c00c0b2090001d2808010804422441958580f20700351000440c0c862504515000380d004501d0200c3c1c5070390480303007640c3d81c7e2a284640c5420880070860070240c0c183d07650041e0303550040c450303000d80303400034080000302d2101d011403010b54123959072918030341000000d00c1440c000c0074001c0c2c041c604062400c265201510714404030903890024a8020301e205040121800c051042c00074410801d80ca82400310010507002210f1004d00f0304000004075034550b02441d001849542265901c91404007e813091402408441d107003a8141038491080f44c000000990280c91141051880000c480c101c0c650601d1410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 803755872 1250 803754622 803754647
    0xa020909041a01060215061309080415080109020901081b12041101121a01030905010207290a020f0711032b0306140a12081c0207120e010f110c12010606 67
    0x41d41b0a900302d020b20100c00d03c821750701010441e00c4407054160b00510101030703c07200100400c0c00800150101d041c412141701d503545820590785045007681c0724030051041340f16500c015408501400009595030b41101d0401c600202220ba51a050800e000c45955446200b59000c55001d211000d0707400003540c1c4240351520340891407070b09001d0840d4180782141d0702655000328504140d115000748050180c25011035581503400b1100c2c120006040d161060450b280300c0609008162810100c0d2110502d40291842c4414030060980f074006c40356140f481855076403141030307054041c0400e060325842807041020b28400542c1078800300115040001000ca81540e0072401d2400b03400301c904040c90b1543c84195054448006500526010030b06040559002d161107414648801c0703c1d1002000600303401605003035224100072802c0d280c2004080d2141c0f00410740a5000503805104c80b50010320030031410072004984e00c2a02e18166880002c40c030061449142060940e444000c03c002c0c02c2d41c0695201c002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 803757122 1250 803755872 803755877
    0x150c06050c121311060a020708061f0e0c0301050418300c0b160314040f020301050f190c05090409110a08070302010906050f0f070f0203010b0f180a020909041a0106 72
    0x1c5a41031341d66880c140c8039042c41c0c0c5000301e1020450030542402041100017611400045480a10b440898405184030300280010210034290000800c0380c194400070b8010310007181441c2c1560300380f42c01d0000034284055045440309194495501056510252414002c00c810b4400b20320040d003003c8580d40d0341c5170700c18601049843c4c0405404500e440c180c980d00041111f034001c0792860009001c4004e4601100d10081c403950490034002040742c05070008108501c2a00284104d64803806000741000044642701091141f0b4440c2640e44040341e88051092800c43c2007082c1001501c0000c281110a02082203910303a135010031030031080c6440b038503c6004050300e500400a841c01d40e40024080300c142d101d814140800860726800d40714101060398824031151b00c60940795a00c5041140001e003610406a02952800304504401d08003c04800c2c0080005003006d2660048140c4000b03824400a140b002d40560a000d00b00440da41d804159000d84c0c000c4c0d400854841003042041c041c0601a8031417010f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 803758372 1250 803757122 803757151
    0x403080a0c114011120c0a0e0d020102120a05090a05090705070803091f0c030b09220f0c0e01032904032609100c02070f150c06050c12 59
    0x36039003d0078004000c80d15061444401c0c0c0349000c61811003000884102200506082160299510100c0602a01003109005a244d0f840d5801050f21500c00d540308a000182d2545100f907903070500d0590080b0580c03061040301d45d2104560300c130185030740040845a000450006d00700c00c0c180b0708980c00340003528081380e40ca15142802e0b180030303210b88240e1034010945107000c80003070320202c0c2c00c1c80429011000d840d1084002a80c0c000c03090300400f8480c1c4c0d14000f183c41c1011901140c104012000d103d1801c645000300014502c0711140180c810f1000215140c0d00407050250003d451144140010400c42ca0611010350440c0b400c2e0103103c54004041c41214084407140c0403400ca00411250030036018105100da001c0c017014151f01040d003803030390b440721840b0000c11f02c042040000344d600a41416507004220981d0100000c0f0317180e00300ea204060744100902002e209080e5030039102d03c240f01b170341c0c00d101c0c0c0001602c0d9281300a660045609280301400441d030415014144200386d036102c0d03c503035200032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 803759622 1250 803758372 803758399
    0x3040b030a051e01180e01050712150b0d02130608070e0f040204150c03030e0304050d062c010c170108030a080a27050708010519050c0403080a0c11 65
    0x14034000102607420040c2c5a401085840c280040d00c1030980900c110f66607055a16131001201d00170003542c1c44188149002030640d02104188030b10f900078000350b41d42466043c2014002c80181042c01072610001c5408900014400c0d0385400400b420703942e1040160301c550180d010b08540c032145038492400d100901c010490000d60041d1142c1e0384c004122064030725402a040400d00900882d00040381c00520340160b1821290408030040d1868800e5409001010301c88070032a13181c4c080da110b06500481624a001c0c0004c0d0207030001c2c040104a1101e140301c8051740b420180c940d9074140c41c000e006956400c0076a142c00e5000740480800e40c0c4620b20003009514100c042da40d070b88245951041088221300114007140c28981010025181c400d19030381150822600b01c0381c520207002d00c121842d100328580041c0180c0306001d9180301d4040c640582e51112091140103026043c01489a0030517541044040009959080034140620450791101340030402868010151420780143c2032007507200040c40c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 803760872 1250 803759622 803759639
    0xf01060602100f023106021b0409020d0b0106090e0705130603090213060b04080f0f060126010c0e03010b0d0503040b070f0204020c011b09060906081e1014030304 71
    0x1c0d10340c07040100010f01ca400003190200034000e040004545500201d00390580c8450301441010164128410070380711039440e0001c1e0398031a40c01d02001400000121105c80740d02e0103038001c50725075001070151800b90150382da0b0903205500c240c01c65408034827210790612800448072065030744400d07142032040c68028807100f0780b450341d0030511078001010784410402c011525170603100e800d02d42104406102003612410101c4180d0424080c04455100700340758248540b000103040c01c4050281d0015110a900b440380d40e100c9080c1c4007102d074a11f10080210490580401d1007a24404182542c0f007001c40c0031010105070940701c40d81c070203c0c401d440010f00e130b0000c9800481101c044540001303ca0b95140c0052401c507110b5032808101070761007840030943d404c00040640000d8030520011441b0240c4051325501516014040c2c0241d40c0010080d65090007081e0007840d0a0b908410107000e02072000d112019204008581220640e41c1300e5443c030f40030040c5001402c542c2120f000110302440c181030070034010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 803762122 1250 803760872 803760883
    0xf0c0302070e0a0e060103061a03062a04121104050f04021e0d06020c060901150e041707200102070f0b0f13030b0907030b160806091f080f0f01060602 66
    0x2d00c99400100008281c0514032075202d428429901c0098615070b41e520304001c0c0c02886011000d50b1194812880032002c1e2070049080340c46400710481c40c0740c0d149000000100903030000c943c40c000001040201103540c8502c00c2c0c1c1c0700074a40c440ca111040c4401040e0601c01903a1b405400030724240405424007005a68141c24801d00344a8155010808815400003c0300e961000501070006807002800303034940caa01080651107080100700030710070070386003016000124607a071017030240c00414000842d000900c00701c038100c841054900400d0400c2141d40790200c040765000c01c400d403104c400e20340155195805120441c0244001e07100b0003205450109100c9443c031480301c44000d000800a5a00d001c0d12000f05160080c6030014000f03202440d06051065490800d40805e403011203e071400110201d40c041c0c0b2a0b0140c4080f903a03651860780700e8405002032001d000d0490304a080c4240c1000c60312002c41180d6100502402d40141511801e0740b03046e9080450983d501101039061410a1102c41c0e0000745 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 803763372 1250 803762122 803762129
    0x13050a1503110103150b0a050c060906010b0d02180a1d15030a031b06050c0d18081c1d07030212010e06010b0c070e0a06050111060f1b0f0412030f0c030207 68
    0x24081a104445e0941c2101119150085030b05c1c40740101d80e2140440c1d110005e066118402d004807503040e2550706001d0398613074003482010484e00701007200c0301d050810b5401508400300e410078020040482c280004881c01490b070014802406400c10460f407800140d0b0b000f80c2c000b10001d140001440701000800c0d1103444a40001c1c051003e00110700481444641942c00d50350b030056010001410112070025042d13001c13030040495141004540e84401c1e00f41458030b100d6952000c40c55203480d4a1594146095494203144002c0d503a8448410b0120344099108064030003801c03001d80305603811031040103a018883d84841800317038034180009802540c006202815140882030581c0c561986c0d0146529011144d0411001c41c0800e40c18400c10b16001c0c0c1100d400e44400b41c840301d40000c140402a5540c1c141200d10400300d001c0c0c4804680d01007648a6480036400b160300099241c4220400c4515181e0f1040e44810140c24480c07a0b800d052540c80880c118401e4003500d480c1d800aa81034030001e540380607a00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 803764622 1250 803763372 803763377
    0x90105040e03040905131b051f05190f09091b0e06310509091b011211030612030307090b0901090e160f140d0b04090213050a15031101 59
    0x54401d010503004000707441c01801080002d10485c6046454890741801002c2c04945240c0c0c2080b10f0300c3c035400b400c0c550a0907548050806034001609103c4010340410300a604014018204002c84001030240c01c0307000d90400644540c0d44495480100502c810700035402a48450318100100118140c1900c0480c8400d071540340004240807176000140b214821064090b03100782e0300740c03101d04d0030035074034815a02c001c1c880041d80b41c4001c2d924001d001c026a001c44003601c2c0c6800c40aa442600099010070030784020040c50100004507004841604503a0b4030350030800d0704003000c020040e881c9414a8030b000c010b14150003450440c1010308001e002d032991405510380b01180410780582c9a482441c01000902c5c48980300303081410070704560040e90409031244800214510303a201d0205000e001d0f8000030100c05484c891a110200c1e01c0c4100401d01115400d40c42910382695070050ba807180401d0a0047d1a000300081c24101690b0b1b1604071510150102118800d0b80010404a1066041d10224850a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 803765872 1250 803764622 803764631
    0x7050a12091d07090f0f03051b100c0309090c030501091b0c0f0213060e06012a0f021807020f070e0c09040209040f1a010207051e062b0f14010509010504 67
    0x43d5025500c07981035410031551298816400650840c19865002c2283c1c000d00c203580101c0d019070f402c5e04400c4040d10350300ea0045201c5689210141c0303c0e141603030341c45003e17203041f076010354a41307660409584090703c0110001c0d40740e00c01030101c4103640c802c142940e18148444280000202c00140420300c1000e4040c0ca02c644d0013020b0300564a23074800c00301901280c0d1b601041201d07220022801310b00000c1d6400741c0000e1202c1d0400c01f0412003001c9001d40148950384500e08a040c1d940c0340200c600c2a508102d8108504c0712040102084181c1d002d401202a0b4002c1d2101c3c1040d004481e1404090b50703c040c140340136620038000700c03841074003c445480e2000c1c1c0e80580d0b1a40d00700c0114003d0301040e89090344140c901035440c0c0d8540d1640b4a40441d1403002d80c00d4424242e0307603400704a4030385020845011b1100b280c038581c120340c0c544074008042c01031150660100380e400d0f0751400ca19841e9440c2600e0070a94403607200449401131880f50030302c88000311004140c20350400d8045002208140121030169546 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 803767122 1250 803765872 803765881
    0x9090a170310091b0314060303030129070b0708100b03070c110d0602031512030d1805060f1608090a021002100203150a0e13120e0607050a12091d 64
    0x10b00c0212005816645018040401a8503ca20154081003a6400040d10306511104400c2002c010503000f028003d00840c116400c0200440c5503410f0740c9424040407030040d0480060308030b0200034056550042d8036500c214035041c8070240417584014496280c802c8030b20818080803008605890f00f1500030b00d044500c0d01d403a8a0038480001d09146015400090079407503508001440d0019407040c60070402020f520b400c00c0b4140b101c003160404040510380c0082c400b50000c1d460f07680c841d00c803ca1210360307000d80c0ad00140c0c030365604156080d81c210704d48a00040801800d03101c6604903200c2503516251130f14492800d03001142c2c4034498003000034442e01505540d0000c162080003043c42c06600c550045503a82440c0c402c040000c05c0500c1180d00820f0012030020700c00021619551250300407141e40200d07100540e0b5090b200b10f0030880303a402031280c0020f124596450b01d101910160307100300000c201540e0305090446820180124410400c03011280500c102d0941510310000c0b00710351001a2140d488 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 803768372 1250 803767122 803767141
    0x70c050706030b21060613020403030c150b0a06081b09031f021e03100e010b0f0c03070804090504020910050307090e1509150901110304020d020102071701020909090a1703 75
    0x4d907182d60046042c8021107801410002c01d0345400344a0841d1000b04144a8089200c03c3e400ba0b0310015010a540107450000b0484607811100c0d2198842d0001850300c02c00070015070010600d4102000080c2d00100f00410f2841d09822001082c0414031031506080e60100000d95a09507150186803007400d50601803000d044c140c040d24801100c01d080c40010140100d841b0546400441d1034884040c0c200e00c6c000b401c0c07403440f41d980b8185e5119000e141c0c540021410300700c1860303116000d80315140c0700070050600131881e028054400307051003c40118035410305004012007044007404580021041410421041da00040c804c4101ca401c950040362000410908500300400d4104000300703e01450308201c0d03184070203c0d01c070041e80c03105011b143c0c0b1074a581a03c68205c40140b400024070340803c00c0804c025181c02d03503240d041e01d441481190030042c1c41d42100c90f1403440503000d01d40c0c02da4020a140c40d40f0f10307003030f09403550220210004007104029603d40030882044102c1325085042d001010a44104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 803769622 1250 803768372 803768389
    0xe060702010e2b050606060310060c14061512060c18030c09040f020a090204050604061124180a0512070212031215060307210204120b010509070c050706030b 69
    0x2541c018006851454076503000e0b080d0802c1501140d041c003401c170003d0901c1c60f24406590041c420001e1400c030460030800181c4620000c04400d0380c01821955400c11202000c0200e1841254102c2182e01454401d006000300c00c9104a24400d0b16000941000101d003080d5060781c0184050165441e41001c4040110b800d000c81400341d26040103400040100340f0008a00c40094284250b030403801195407615588100d0040d13014071540700d1410801000641d1044000d1450920901e054500380d4624191024091580d000c101d542c5030741e181d081002c0401c00514068280840101a0090100943e10b158481c80c8298003501c04e03480104044095460f081d26128000c840c050403207656166a0710030b11035141007142c0b1400b03960680d280180f264241401034078001c008036103642c240c0c02c064040c41350703c00800420343c850083d420301001404002165001d000d40380529428034a13541000d0911066000040054040c8039220710500300103a8005071500403500c0c039107400146100088001020f01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 803770872 1250 803769622 803769649
    0x20c012304031a07050309060112061b0305011404060b0322020616020901060f0206040b19240503010903080c0703020a060c03020c01050105030d120f020c1e0d0e060702010e 76
    0xc0300003203408010841140a03440300005003085940707041e91010001c80303403448200d410454580120004100c4110019a85010940f05244c003103105120800c49502d86145041c1110020341c48000401c5600f00003030107d035610b41e00745e805110f80d5043c00b00f01c01d15440042d00d540c1041780711000e051140400e917a0094400b5500500345540c42900000100c2c0c070000c101e109074803070741040c0c0000030064020900c00d90f400f0b0207038004c2c1c14a0b03901c80d2500044aa402048401c04940a84401e0300c1c0c1011032080c3d80304080d0360051510300d5817080341150000425a002a8000c0c1c8c03510724030790040383c0c01c103014941c40754030404d940b5038070600341c0340c128101000444024070301420010b80e12820b54054016005111101c0002c01850307a0729800c040e42d0b483d41504400201d03544240c590307030400b00c03500300b1b084040c0b5000016203069240100c031b034901440c0c41d0140804803108900400c0c041700070b10000680100c2c0c2c0c5815224103c54800040e1144601000281404103401c2c0b8549541c481c026030041c81c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 803772122 1250 803770872 803770937
    0x140d0f120f0c05041a030f0a05180d050409110c0604080d020d06030605090c1f0e0a0e011d010806013b09010501080c010c050604060b120d18060c0201020c01 69
    0x900d480c20000f81030340e0854000c0d090700104905204070354105042c00e0f00d110307141d104d01005035512002c4d24a4021f010180200c10030140c04c207415245054100801c8500300032617586c00c1c0e81c80e440d1884100031610040b048080c503400411100c0412100022020b801035040030341c0e1035440c3c0101c40c00400030301c504840c2540329800d08100200340211303a80028031590541007903802541c48d01003003042006034415070040800e4020b041d00401e0b4071454010302540000b8104888180c0c0b01c500e0098064000d90100b803544100103903180c44e0016454280740142041401864694104003039896500d1401d002c586401c403091241c003040401001d4021001140450304d085982000a952400307040d090041403041d00c54400000903075403041401d04613440e040405000d60b034480c0d0f625100904014050301d90300840d08201004402c40074000c0b106c08032001c1d1915400c034802d0f14008080c1e024507500050500c0b02e50b2a0a0b030160360049050f50108000b442c10751070100250b44c524216002d4400386070380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 803773372 1250 803772122 803772131
    0x1c0e060d0f05071409090a050a0e1c021e03070b07031811011b02011403060103090210030e0c0105041d0c0c0a030809011416110a1e140d0f120f 63
    0x1407000003503000d24002c41c1c640d0b803000000800d1242502c801d10500403045d03007141468000541034030b070542c00356410080b48000071440f52411070170741e403422070740d450081502440e20455003902c0c1d8042046001d0801d03220254181c0400c0c14017000d072039004403c00034012942110000d80e03018443c2e4032584040400025805400c081810450012448680c03101d0100d038800d0581d003102100142e641016a074140e485a51003408107030102b0035a000a003003541819160048100180d07981180014090559900003520030303070352001586009002c014803414007000b0041480441c06c040051464141c04150003109501c40c000e20060ba4810524205c3c10f5000b600c12074002c00d0f503c41501400b844440b4003d0200140403914041c0e100d030103981c0c100e40030120600700396181d800780700c001c0314010315401600c491500e151109011046c41080514010015800940c00c00901d1400700c0408590140245201c2d5180080508483d4220743c841c0244400107800b07118440d501e030014120040024014030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 803774622 1250 803773372 803773391
    0x20d0902120d080702010612021c0602041d070318021903081903060f080706080c09041e1b120b030a020402070b240a0501030908070516080c031c0e060d 67
    0x640b40c21505008030001442c1c40c0c00319003078500c14040d03072007940c9020f0241c502c80c030000c1e42000486103031380a10100350001440d803840400e1080c0301910091000700c060448018039140030411000008080c034041c146480341950740d41080208108106030b054a1800e2214150840c01c0081340300750344014031000000074a4040107070301b5040400081c0c0306071000c0c4000d0740c46608003e903842960207414078030750080e001041403501c81c150240d048000500580d107004a04e20203d415030b104140c1d605101c90b08004806c4003040c03a0308c185038082c03c0c5c1850080110b2415200105490800d240300603626440e1300c414025640c007440700200055004100b1580d4241600d004144100215002604002a81000400c0745000000004a0346004181c08403542c00e210054000b442400026100803100f03101d4000002d0082100c945c0d0150b6000903070050300d10700781c40549401400d043e82c43c000c1d0800040541c1010804c0e000441580349810079007504c00440d400f02e40e80d4001c24540c03c2003c3d01709010030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 803775872 1250 803774622 803774659
    0x140d050d0f031a3703060c080a022a0309030f010e0d14030415090206160b0105120c090c070503071118071b050f0703030201050105180c0706020d0902 66
    0x101e214003080e102480340c6099161048a82c4015580762900002c511400c01900315240c44010400201503c40f03c070025440b02d1131209102c41600111a415990410001a02e070801e0314203a0050282d1401d600c0c01c5400600d035640c10105061003001c111040c6030007a40c040c03062044d1030348248041c003201c80c0304400c1744040b4060080d00040c0c40c3d107401541880c9001c0ca1184070303048075804e1030503034061039511150742c1d508020224407440c01d03c0a5541b140031005950302030080810740c81c5c520500078480340d2400c020300c1d40394042c0d0005201d80660054450744c00000b140100080100b1114003120399218040040207101d200801003403400b00290070000c03c003900c00070101e81c2c541030724505030a6116030441c4444150694040c0c01051000303a2562020b040d549407060314501c910203503558290700502062030442036810440141c0d4680005000d6400c0030000a5600d8000552404d644d04000780245007601c100d40f406070002d034001514035a459540e2700150a8107902400301c4002c0c0590b40b042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 803776978 1106 803775872 803775887
    0xc141c021c0b0405120310090e0109020a08070603050906070801030b0709030203031c0b03120f03040f05030f03040209060d02031b011206060507021513140d050d 71
    0x4110110496820456541e00ca00d500c42c40b6070a043c0b034020f082c1456150703040360540080c42046038503040b040003c0100c60f1f40c0032000071504000d960840c0541640f54010790404a5a1400144420001940c104403105540c0400260302c0320061282c4602060b1080400510403c0060020400e007904075030300001c20f42020008103a40c0d601103802c40d002a415600d80c07440401d408003054401c0c0c022451240e200718081c0c114140d0301d907414065401682e0300040018004800030b82000444400000950381040840b034448500004d0780003a0f82c802c98040740110040c1c80030451074248242200348061307004000d0944104050910500c20100c14074182c1002410102c00e0031038812803060b10b0150a01d5a155503071450140148020303440c4185000403c00310030800d40b00d0458108820313009548030300d0700c1d41c4da45145980000701c2c0100c005030040c0090085984d0190840e4100a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 803597122 803776978 := by
  have h0 := BRFrame.cov_init 803597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 803597122 ≤ n) (h2 : n < 803776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
