-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5431
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:50:37.843571+00:00
-- url     : https://prove2.me/submissions/fe316ec7-96aa-482b-8425-ea6e33f2deb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 976618705 ≤ n < 976798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 976619955 1250 976618705 976618739
    0x412030329151615020d060b1909050901270f051e070801050405070e130605011803055d03090a0201030f020d02030f060f03030a050a0c020a 62
    0x5102001e040c280c90340381c0040b0300b0380303040464401c050601d007080b800d0001c0f00701c0100c0001c02198190001ca020078010740d050340c03440a003d010501030641d640c0048000c9504c19840c4541c0541c244203000b1000e80030b04242c3c4120303000034002090b50303840c0070590911402030a41c16545007c4c1017203e112803500600407800846114180050b0b54105031081d0468041c41c484181c40480180041007a0310760440b0100d0b0440b10b050300e001c01d0303560750018100d425200480110b40d201700c0040044441f90000d501c0340040c0c610a032508400e031040c1c541e119401840a22000f80144d208060000c5550103008030030500c9481101203180044001380b0605649108006110b202040508041d18090200c00d807001140010002c03103185040c07288409031680306011000e41415292030703002400002e82d07412a100145220b204544070300700104201c8000d50181c40640c80742046035104145450040201c5011040316181d051070444800825101007020030001c1e64404449900000d5175498501d03c040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 976621205 1250 976619955 976620011
    0x915090a0606111902040903050f030403020609060105180402150c120d050606071110051b010f0c0512011e091416020712022b05031801080c04120303 66
    0x41e0103418007200410b542c4072480c900c401c942c04904d00a400b07100c0d800300b0011890f010350f00404d0004417801e085e0f682d032003400c2a444038020004100800c0c180d000c034581e8001d6945c80e042c0c44199036038008120484030003280201181c0d0201000c9001407070082024100091021450790420350352140b0b19040030001c110080f500040041c07019541c038500d1180703640c041012143c1e541402900c3d11101074014050b40b02d42c0c001c03230b20400320001c4503000302c064403805650724400c402c0d82c1c0a003032011400717072103140003044015041c103254000d11401001641c1901c16140200b1b26140c1c81c0811491035807074007410506800a41c1075020906010074000e844102c03103448403d030700905110416003110a4061051000c64201d02020f100d4907000341c038102c1450350110b900700c0e5048403601c0e1018202c2c0c03502c480c08a074404000c07100d80421a010000c0c116201444480003000d4410000641d01c1010484020b2000f010822082c8102140d00410315140d174080d14001031481d5201c2c0b4102c0100300c0e5040303500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 976622455 1250 976621205 976621211
    0x304120605070c0b010b07020d0c150e09071e120c03060501120603081b03040906060207050108090c0109031502092e0212030f180601120b010506180915090a 69
    0x20148403050240503080a0301c0d00e0014070a070340b10348903540c615406008800125000207040301c15950340482084030b0f203400c420041d5a0303695800504401e89070908440001c0341004040029515020074154801c820076115482049868010040c0b405046a0480c4c1408520103448211400c01d200b1141620754545000480340d04020025000316101c80760454203504000c0144001156041521f074074190000c02c42c0c25241c919210717241140966000f4150040c0342810016200758006501401c4031020780322036089855620001d07807a158042c08107030115a014a08000146d42030841510400241000600f4420000d0020700d0705900414500500c1e96140800180d1160510044a502013a0b00090009007010a9801001e0000802c50038607644914000340d4a0b18054031000030400b07054003a40c081350384422890521141da00c3c41030340d00011690010a80741800804c8aa145414401c5080a00e141e03800f0407114040040c03014032003041030000081c491302d0344e5001c2805050f41c24404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 976623705 1250 976622455 976622489
    0x90916120c0e0f0d051b0609031501052d01050306150a0306090e0c09040f2904110d020906100306090606020f0c060f0d1802060a02060406050f0106050f03060307080304 74
    0x84400040f20204602c255620071001d80095000a01d82c10304452034080d0b04500c0010130b00107403940c0112150036406015003000b818440d040008030300e0507114100c0d0011200300a0680003504081c18502e403000f250200040115036600682c080c5521540040080880d03103001c5203c0c3d20341c1d40050707a070301c00440d84401090040c00f41d140901140f40c000c0744000c0001b07c03c9000017415403240a8005002c602400c02c5080600c44101c500114a6800c0c00c2400f801880007000c420700d042e42180c007542e6898101019210038a0030207058011550024028019074482c2400c1001c00c040b12a250014140c0d5000700091145040c0100801040c80343c01400410480c1243c0300d003441042258644902c104004285031600c040c029250345020401d40092066404840400009040032019500c120b010a0f0484c04503400240e0902c51482884d040c0074549540d444c01d060b41a0030700031407010881c10700c4020300740300c0050b01450303102c1700c02000c6903080b40d954603003141598410b80020803450700140d01d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 976624955 1250 976623705 976623709
    0x15040f080409090c0e1b03090f030a2d1218050610030203060c091f18030c030501181106090a050a120516050d0b06040b040e060a0b0402090916120c0e 66
    0x20100c014112a4176102c0103150082c00480340c03040900200302410004804284030340c00402c0300c10302006100c01226a1041c07100c0e4082c0165022002c4803090300c1c40512244600641b14001607041c41c031a0700c401841084440c0548003030b05103c030300080490808020400860300070840e59000348008400e03464072a041d030040c981400760040105403c95405c106514032034440f00c00c0050806055281d503400c403030a0302403c40d0b001100a0040c140303104540c074007000b0b01c4944402c00040b20f1048008000c0354070342075540d82e44645003040290420101b42c010303200e5800d24070024103c1e504020907140b04030f42c4410001c1c80d140e003190000500390202803000810010100000030b000c0c03801c0a80d415030742d841c1030300280d64149215002020b07052150007043e00d80d00c95800c40c5520150043c014403a22000900041d9035803000c43e01b0130005030502031190b8a0b82494800c5a282c1c090290070b044056039402ea0008e41013002600c02c4041045c41200420080d1a0b0311456101d81c100340d5541c2003400c0d030002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 976626205 1250 976624955 976624973
    0xd0513170a030b0f1f090e0c030106091d060105090d020402160606210201120b0301050403020a030306090207020f060304030203090d060b040606051c050612070e1e040515040f08040909 81
    0x107401c0c0d006500031110784c1155554a10125411841d610054030b2003680c441c000c54042201e68441076100e4070710030501c8a0144040c01450503600b1035035a211001d40d403030b10384002d8508035040c81000700601802240b01940b080c0b00900308410007810102150103603601141c202e9005458448028804640c0d500800c1028042d102c02484c0c99000d854040e00303c0124041e40d003442c540000d06028030803458003094240c9401c12040c40000070001c010a01d070908000c1e4950302e08007402c40020b403030318001180c03c40052003942e0480b50050b0000d04000161414040c45520160094095100611041900382d807241d586c13005461044002043d800e10308000d00c42641e45070340001d81440824420700d180242c40f0141da202c000b08100c0081002d0710703918086020102e019003030000c0390081480119980e04c41040c00741c0070308000388101c207003541c88ad402c05545020a44004000da0424940c41d900d108056400d6500a80100c45030364110b0029075640d89560300c99030200c011503440d290000c0901034030344 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 976627455 1250 976626205 976626221
    0xb0a020c13020a020706050a180b0702090108120d0902030a020307030807171204080a2d02060c09060f030a06051807020d02010b060d0c0905131506030e030d0513170a03 74
    0x50015803d02c61000c41c040d403159121b0250000300100400c40562191240c0703c2900560444411038200b10346034171a107031180d030000009a004158540c0005080e45001440d46c41c59030002c101181030906d440c12a5010300240041607034184a00001d010241c0c0c1c05000200040d84606c00066503001180341840c07020741c0d01d0019284041c014040c0c01c48031030032524010780c843c3d8004c4000c0d81d00c0d0442c0c603094070b140b00c010300302d025110300ea07150311124404c03078052001d4501d1043c1c084030115901e030b8a0703450251007a00741694204d0028000c09401641000165402c40400040401d100e41c4800205483e08509080004101540024410744640602c100d90415400b840280907600303407000842d0140c0304424000c0e8440d5581d030b100407900381c070511f03041c800340c44000c0c102c3e185071404000c1840600800c104010303400e1181c400004886009204132104095a24061414032030601d01203001440300030142d069401c000e0880000144c41d4040110848003045c0b41d142c0c45480300c1d50028101c070424 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 976628705 1250 976627455 976627489
    0x2063103092d061404030212032109010e0f03041703160f03080f100312020309030f010204090b0a1503050a0f1506090504060807030204092a1a03040b06090901060b0a020c 75
    0x28030300301c003004c0010710448003a01d030151801c00070405207042e00c41c910b03c900240c1694440c0c0d100c89048074001905e126501a85c1048024458842c0300d41c565500d8054840b00750289610070041040184004500c005060302c900c0d003680c1c2005c00c3d40780841100d2510007400c455401050001d801019080001c4035040111542081814a880e162103502898640009091a07900c04042c02105100f081150394030304c40030301569519890440154013079041400359144040c00d02d400c0d03d41c1400c3c0443e03c40100c41e00d000000007603161140d4203038000c29000e0115143e25448240010090081b406520743d000312080d6900e816a19041c03004125458030b4000031710450803e00100044000010303040140c0c0d40440d0300043c1c0700c2042c6044400060316039400e000c005601c3c138030300c5115182d49511008649022400c0540f0040626680400744011100107102c03c07503110200701e05050141802d58070090150002138241d031101c0580d0400e40105800c0760069201c210800902d04084030f6181c805401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 976629955 1250 976628705 976628717
    0x9030b07051911210d09080408010b06030402011e030902120a17042d030b0c030a0c020118200402270a0503121c05010902070302063103092d06 63
    0x8504110358039000604413040b4491383c900451001c2d0702060080302e03000003100c00100302c049118681082c1e19000f80c0314503503095203043c2222a8a05241007141d00c1141e0595402d400080b554100c01003440d0940704003002c050356500c8002c01a00c901009140d00d20345000180300000c03c0345000243d01d0444458100d9564080c80100300c0f00d080011800c2140780502c0f1490f03a0310b80000c200080e141100e510180848142c4001e111911406000940c0203600801d428044a0043c070026400d9a807112000c0c45d5004001c0010703c0071078001c2c0310312481c106810501203071141520001905980210880c03044103a0389082c0308200b0200591260b491040039a6401c01d018074043c000398942022008060f008078000412900c822072200040b401c103062540b08000d1540c40325540c00c000c0d00710000c11009481a1804200d91003070b0807400b594102d900903a0040951000751403500c59851100d011014803580400104503480150154800b4581d500c10040c03041c0305111200c002051a980710b9414051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 976631205 1250 976629955 976629977
    0x90e06060d02101409060d090b09070f0504020a1e050c0d23030613020d060302091e070e0301090b0f090d050f0306010e0f030a03020c01091401080a090309030b070519 73
    0x3c0d50710410b820001c0900702014004410184c0d800340340320300080c00b03600c002e00181150401c0c80c01e83c000d00c1e1143c0101074100305552491203841d525401030145400800210ba0100302314a05900106101e5580d8504819495030b14200340140401100404001c07840118640040e404100100c8101145518001d08078030f4152458000415100c00c508000304000800140280c54440c0f00900c0e03001100821550782c0702d8080034000415950204038480d01c82100825088035075406000340c01203000100480d503844111040d07400e0503200c450f0030307015501c40c1c08407008901012540e40c4101841c40300942140341c171440c854140841c0701500420701c80d0600c4441c443c0842542902d50000003030903c1b21151440000092004441c00c110315031501c2003000d21802c255000c51200420002070f22011543c41c0c503580180c00c106002c18180c0c1c00281101c000a1a40d80c040e00000c0401380030303003040446141c881d00c4420b421142220240f021450000e03040500c04e004160b11307130303000c022441c100340700703103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 976632455 1250 976631205 976631209
    0x320090709180c0512060109080609062205030d0c12061e0e1e060f041d06160c020922030521071e140d15090501080d0c1a01090e06060d02 61
    0x3001716042c01c480e441e40130000030000d07401901280c0180c005107084800038607003141a141e503103a0407a00d41d0800550703c0c06c80448203591075040400070768814055424602d505216100401c1603103140c04c00c01204850084002030b0078482c6c50b0140030520003001b03110070100201014154154032207007090100d4401c1040100e280e000c1e40d0356030348210220f1141901da4000082c0c4200118401c0e031f500c90b241107010402c1780c1d0b20440d140c03085040c0509980305665082070942c0030401c0100359a0214640c041c2d0b80005181c5070016540c469201c04101000c071446412960601300800000c5001c5800000c0000c1d40400c0200c0d03401034072440a030a19807901c3d01c0c1100800504e24580300482e00390b0303001c400d400f445001e402c4040401c0c0204035001c0d01e810b003d80004e40070340b44405440395080c0d0b0080c0041942d0400f400b5013816140c0b003a00410307281003800c1d4116080c1e10410010b9030710943c0d0000e240282e420f080c030128002c0800b42b0303001c82c0841030f0050007420400007130130744d9224514131803801c001a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 976633705 1250 976632455 976632457
    0x120204060b0f03280f091b0506042d0e04031d030d03090821010f061715030a0b090a031202070302071502070911070c080609070320090709180c05 64
    0x1c91088007240315008502c0b200fa11226945560011401c5d0420207805c081e1145a07101e200c0640c040c2c007814561542010b10700340d20382118000c0a402040800c030500512000c240031b4005420449809411800704540fa200c1304541c40d0485548210104207001c14581d02640ca040054404000e09085000060000b643d529520b5a5041413644610740b03d4103001d022000c0d510480d40f0000c02d50302c1c3c40070301c0d1004888801c090241076202ea05001300842c0107482000c101403242e004950f1402d841d210080003c1030102d0b542103040d030500c211402e0341d00091408200b0b9000344072603801050682040e1a0140c010600e00c0310b0303001c00034414481c04022a90004c0d240c2c0890340305400ca00044003e04408a09101043e00304500c2c0307505280154a55901d21001400d5241c0100e101950050b154490951122019a00345141d030344072480c00d2020807000200421030f080229000c82850b0007482c04201064000c403003010100d5168502081410604500c0c103803000e015120030000c4400b001005019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 976634955 1250 976633705 976633711
    0xe030a051602061c0f05091609050408070f0b010f06030e031e0f04030807150e150c04030b0a0b040c0806010f080613091b08010b0d020909011104120204060b0f03 71
    0x1039011561500080d511410200c1d0049040640d03403064224001c4d131407401074102d02c041005568070303040005200150225101c80c01c17001c0c603281503c000d85002c1c0b00741c0190401034001c0d501140200000d000107900841d140401c60f100300c0030803e00e9854502075030340c1607480303a2101042c1410a594000c1101011084840710b03440c400640300c440d0000704441c40f1600800a040220880008020060152a00c060079505200d030101c2c03082d80c01440000010b90b0072280d0404803d50000c110194100c1c65a020540c0c042440c1e08181c1c103042d600e480700d05661405880c1c07940141d503a902c40510904107402480011a001d00b444510b40c10304000007094a22400c00b03200405c8940300100e02542d0301d12000c0e07501c41ca80d0701820700c254507007070400710080b0380000703620407400390b00501c002411101030143c0c4e00400130050100003008003075001e100b82650300420b015099582c1c0c4003049500403246010b48040d124083c0c4007010303107141e44140000c0743c529400131141c1c2102808868400340903881180c0d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 976636205 1250 976634955 976634977
    0x31b011410091e1e0b060405090f1b0a09060221040510020f01050103030e120703020d0209070e040c050306031209130c050d1404110d02010c060b0a080712060e030a05 73
    0x50100c200c01c115490740d852100d10f0f484014103090124600e401825144030480c01e06007020048510380108000c45071045100e9190040e108000040100140061480c1c0c8040c1c40603800303500d11484c3c002102c083d80312410301c00100342012410b01020380e0421921403010a02003529032103049003000300941d80503d10541e44103081d000303410554644207010400c030714900d001c002d028170358503460302a08480710525114010500c110035445060307070005240c0202e94001e4140441c00b8456000c0c8030780000b005280c903003882a12080108651079512800c01d66181550301c82e03450341400e80405090650042c00403e00b8107081c058a019640d40201c144104d0101c0d0400058400042c901542c4d140580381040b4009858044076400c001040190300b841a4403c0350400d00c01982030041250700c5083c2035005e4002041450402c000410f00ea01220321004001c0101c5589682c403148503240c22025006800c2e1401164200c508102803801202000c481010195080425009000f4614004d070342c4051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 976637455 1250 976636205 976636211
    0x207020a0e100b0c1b031203190219030605210c0d0c03080a02060703060501050c1b03011d03120603010902010f1d121c0201060609030b0612031b01141009 68
    0x1412065102c00d8010042048001140d152480224544d03107a500202d81500c080c521485000041c4c41e000c60016194a00303c000d8500f9902e035248010300200b240c9a6600400340e003000011007007910250840780028881e41c000c111581030034103114003005036800c440700400040c400418000d4001c04c04039180070702969003411031562400d141c01419a03548c00540508400221803603511741c0419002d11881468405225059880e00111214880c01154060ba41c01c00040d03008500d64403110b001140720010700201d070145007980c100015650860090070903a01c0002d03215084d43d4843d170314a900013030440082200b24883d4001a0082000850110800200240c040c2c088172080b0071104074020003800340028044c540080980c1e410341c0744003d0328280800c000c864100c034414003421080c0d80513540c40040b03561031030b03440d811031081c05801c0d158010413003c0c0c5040741c41e400700003601d8410045288070440c1400c0d000d60300d00311804860f4101896030720504114520351441c3e403a0381169072a60b400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 976638705 1250 976637455 976637461
    0xd06140609060313120f09151b1a0112030305060a0506041a160f150c0909020c100203040602070b01080d020d1d03070305100f0603050c12030f0d140106030207020a0e 73
    0x134403110030107610020001070341c8404808030954401541281c1403046c0e1614489262140140e050b01a0b0b6110b080b000140c8502074070900c26100c0b050005800d1080f5025007481c94031119400c01c6070400d070450303c6103c403000d803950306041e0705005042c0c20010a85002a800d814140450003d200d5170040f00c0200b04c015112041c2c0300e69200480c0d117203200c5505c003200102c3e0b461400340100002110b040c0c5011003001c14403103040324948101c1c1d240145c1e80e12110156131031302e030320040a504900285400c41c0103d0001c0c0a003000503000940c8560b01c900f01c0103941d400b00d4907002c100003030180c2084826501070500201d08503000500e004d03550144d401c0001003804030580b980441140f000c039003901802004000420020002241358071242c50000910030040c0c200d001500b1240310b031001519903809101601602d0078000c242c1440d5907218011b40386082440c1030300a8072079000701d0091810f03d556072850800c05034500200ca003d00724a103815450001c1513000204120094002c14600c1b24560f008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 976639955 1250 976638705 976638721
    0x10f1109041805030a0504030201030b011107051c051f140903030f060406050303070506061309021513080303010b0d05130f0b07050c0f06040203061005130e031309020d061406090603 80
    0x40c502d6030700c00c2c2181d54891218400500e5500688000ca01281c01d0035403a003201c1d8090b058171552094410001c015031031410003000900c42c4185880d958561902c0549404078030148019010015100014503186240d6a5000c0482c1e105411909044039401c0a12100e007501208994005c0350b900300801c0d554440400140080016511107641071000050140400c039020820500c500303411110a00200740c00c0a054050f070f1202c0c20001d41c4510030041800d07640450f00c02406004a001d0b41141041d81c0303c072800e51440e0700a80000c00c203e54082038160b5800454010182e11448140d000c1100758081d41d02d0442c42090020002c20340025680040c001502c541c0c1600c030101b00e00703c100c0e500703400841011925040d054800340d0090080000054106850316404402c07190003810741c3d09900c444849000052201c85803580c0640000c0200310280042509080060101c0d4480169519102452001203454980c000311105186588a500c10780d1100c040d2501540199405030703403a511198 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 976641205 1250 976639955 976639991
    0x60601030510170718051f210c0323010e01020a0801050d020f030601090603061a03150a090b070f0f030b03100b030a08030f010e071107060309032f010f110904 70
    0x3160400b0300e20803d010311003807101d41001e4000d43c507c10017a080410f001c04030754805500b0707004111050009201590754031460144002030b80307000e0740d881c6955035107a503a0400c200141480c0f1014480580b10401800c1030203108001c844012100214600a01c21001803e0b0070b4052042e00e1203600da00b0708036000c0d51228150703801722a030024107450503580c54141a800410300e601003035038134524158072035203212036941c000e00e00c0040c014020494810a80045c0541d907000130089180151075901c9000041c2610300500e005142548070303d009442c1c3d074180180320036090824902014204082081c241d10040703101c0707200f101d60740e41c0410a2120000460b140118100c4001d0001000008015031354014960a0f41070359403101c00c038040c5440303124007110240101407107183c1382e401125007084040d00982c003180c00d5074030a007885684281e180d054820045030101200d4088040307052801110442842140304c0e940ea062420008000a2011582a4000c504101c2d0003150f0301c1120f5103884100170 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 976642455 1250 976641205 976641209
    0x9050f01110609012027060c0708011407031b0302030702030c0a2915090402040908070302070f05062a1c0201060e070c0b04030f030e03040f080606010305101707 71
    0x1204507405418422a018000c05d0045840e8000400380c031215074660070020704442c5150801e034040c20b01034500468584400744000c100c136034485030811880ea107120f41030042000510884000041c112910b60101103100380041000082614000641240340c40003e601c1c0d04104051500580b02e544004080c0c0c518415400c0107140c521074000c07440100504102062208000c03140101440007050316140300048050700c00e40040421588a2070080c00c11014559005000030000b20f40501e0700d480300c0c030481c1d0001d18280c005070001202440800c2605510600400c07040e01e48901e400e080440024030303008120842c060b00a00aa01c0b8101070b0390800c502d044840e955000d014803101c001c80068001c080c1841142d001913552b03400180c0300e41c041d05010364003540001121295680e10b5078110b0301b0480f40006402410768a842c0c0070b43d200010000350016082e0200484001410400014a0280c00512142c101402d09003004802e040744071844080380c800da0f00c0c0207c1030158044903404c0c00c5e9070b9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 976643705 1250 976642455 976642487
    0x507170d0e0703061104120f030309020d1b06021b01050c150c0c0c040228090b03100602010e280302030f2b090206040621050106021c0f09050f01 64
    0xc240740280015001c1560001c403807065501708156105107200c140c103070160f8852400c43d094801c00000204403940c4000c2800d03072180c50001080b40c92a400201c5003400032005584810768401e00c00009141ca8440001404e040e000401d0800c80b0722072004210707040e21009a0401c2004628245098410080008103e011400c1c4507201d1a20ba00404056000301103101c0312407180c04c01580310390802c0d02c05c03105c103d00d51242d40039264045600c0c181090000170b501c14100001c1020005642858401550017440d00d140e0410900303107082c0c0d0080c01d648c02c000c8044101c6e0042402c504090042100b50380580d61804101241d03c00c1c40e0400b6800c50044c4020280003400020351594001003c043c07402498240d02c0707100481c0e0701141d05140c00c8a00300c1800a40002d010003051105a015140b0000b20450515402d010f001e000f1840c502a903c0030b0380642c01503072001c1a01c04441e000c541900c04000c03001e02d8004a05100043c000740100c400d8401c0078004c4140003000525640304800c841c203041c01d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 976644955 1250 976643705 976643711
    0x111030a0c05071d0f0f01060806010819050403110f032125030c08090f0601031e0f0c1d040b06060f0f070f030f090803030a0b0102011413030e04020a0507170d 70
    0x11441384c003403100d0011511152200c081000044510100d0507005044c1e620660300c2e0740c00da41c2c4a01c0192034501c4084d280c0d0314145243d04019003908031380d0050303c1c421032007551024146105004c806103401c41d11036449c071380794009200c001c2e5001a62000c040e5040c2009003811865150600100d0143c4001030105248640d40310000c4c010079095002035003928841d85d44d4030034039500d10b115143ca03006d0035407e0860f260080c030700400210740800c1c1410074030710220740c44101008290382c071881c204040172021510b402001f981040134501d1991040845050038101810514280e0341d0884e001c00010400e0384600c101050001d030204c015016220400842d4020340d5980e46a070400c504604c1490108500203000240c88115003841043c14008452068005604548866443d08054041b00c441d0904541d0703102d440111140071086001c2c099102010310b070510340c1b500d04005000410002109002e00c1c01041050085c60f4010200d410154028141210301c2c412018224580d11070b40000e2600c0c40c0c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 976646205 1250 976644955 976644989
    0x3030b03070b091008040b040209090f0d0315090501030210050f09130e070b0a0516020f0406061707050a0e270c0901020c12061801090b10140111030a0c0507 69
    0x70754000a0140f2441152600410303000382d002113070700001c1102c0c001e03c2002d18601150040c00d095001e00c0d007103110032081d102014142c0030683c0c81c10707000e881c0c60360000b6201ca0015031661810410b49001d48040e0a09100e44c1d030550b0089080b220851800604101002078201c4c0b280e20035a0a03104045001041881a482440f55060150030264080c101c079000b0184006800c2e0544400c42d6a0945030b40c480600300490005c5804026581e01c43c140d8010b07500354a003900e1036035a88210030280c28142c0b00d001d4440c5060780b804070072140050081080c070100300050f1107030703035046071052010480032150030f0380e00d003040001541b200703241c04914207400000c00c0c01d0040010340b600181c003003400d0a07400c44a01d82c4e40403040240200340c2c0a6204090341090703010984d280d0358280005440d0002c18004140c03501e6561343c070503101c04101c078040d030610007042e01404040090088107020000901e0144030248182048684a1094034110760070f0000103818001045024804a001404940c5406542079 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 976647455 1250 976646205 976646219
    0x1020409021902060103020f13061d0906090a0b0a050606071203020c1b130903110601060c15020a141b07090f050f0f070c0f0516090c02030913020703030b0307 70
    0x508184070a407000b51000c840684418400903c01d4100c0c0d07001006001034100c0364090010b00f8150110042da01d82d140c80010a0801c08400d44807009862005d2208039854510503a5003040809000c01c2001c1d000000c0cc2000320714801041c941281c00300301d00140603201c40d4001405441003a00003084042c008801000139a0943e02804898070320200342d84010907603110030081c0105030096650f00203010351044010b4a000c1c0c0c80700461074442d0429101c7c0001c4000d0319403501c0f00c01d91200000615003100041003024442d503a442c40710200701c00b03500301906114080c028200c401051100890081104881c03800b0100301e03220004254010f0780d00c50b546811307200002c1c04014555030042070038480843c0200d11400b804620a4150500162450b1075a0004403103121201070140c0307400000a0510700440c1003441032000c62a810401d038000d42d03150085001c159940500d444084d0b4109002d00c004a0726161081107240c002004010b9540146140c15802402880915a018490103401150306 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 976648705 1250 976647455 976647457
    0x120305040506010602160b221205120901021c1404030b0a0e0703170a090b0d0c030c0306120b0a0e0d0206010602010b190513061a090f0301060b0906030c0c0102040902 73
    0xd94021425902e440c0e0301c49405030b03614014100c414404907202e00003000030764200c102500d600f20044411402c4180480410300216001340c200b8883c14240400d80c01c20803504203c0c4071105040011540d007800c0038000080e4a5414103403070030540d200c09046500d40300d8420280800c000c1d903003105080c0c8503920780c01c003000c400c0310850341030741c20741d02d0070305041c0d44244e00050210843ea072100a111000c442c2c1c459440c03080d0041d410703d0090050092010400c40c115102500c600b0f9026840041c1200001c0c1006041d982c1c02304a6009161600303a0900040003e0141a908150050481321140e142c94051134000c05c0494251604d500590481c2c9031002c0d03001c11194121581c0e5402800700000700000c21511a4031203500303901c40f01241500300030600780a0284441c0b095212030010714241d403210201141c000a01d101a04080f00240510840ca002d50b203103518010309500800030305040090440c140e12444028500c901c00100014030000b1050080303d0302041441c0082d5200c968902c500030103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 976649955 1250 976648705 976648711
    0x10e130b01080f0105240405060d09020906011e0c15061202120d08011502161e08010501030b0f100812040303030e0105090a0212120313020f0604030528120305 70
    0x6150200491812003500c07607050b040ea50028524555041d041c0c81c0ba158000780005600030108047c440003800c3d581e014003400004c0000040030624105610402c07600410040c11a410700c40260300e5038000341c004030075400212070903040421341a2031506103210f11f0140134002caa2001d05056010490000c0d42e01009103241c420b8500d1804003a01d068203e4542124103203010002e81c41d0001007040c80075040200462800d01d006a80060902d1041c4451307018550b0003410820500440220490412190b1b89008201000c002c1125504540d6510710200000e0820050201e00d030000c9180d06d40e00c00f401070001c004203421a4042107031140c45070019002440306a020230700c0d2400d1000e1685042c054907106204604c09440559499030820515001c038044404003440b90f00c01402c1540b608900a50040e081c2010340701d140320307480c810090b00203031102e07445000c0e40d0288001c000080001510303c4090800307008008101c2d140080d042078810407a48090440512407111038411a015032247d80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 976651205 1250 976649955 976649957
    0x712020331030203030403030519020d14060f010c080a0e10030c02060705071e03140c0304030510020708040303080a0b040204030602090306010602070b0d020d0b0a031b141e010e130b01 81
    0x10341c403280c014116042114251015016800070400900064401c1d806154801c0c0b007410000d81d032440031041002241c000541c0c21800c140d0700c0541240c59140d8001159001c00201e420988440c1168002082c000e60310000502e44200170809200050203005554071100c00039140c2401c40800c000300401400b800700d50440580034040c0403481d03d601c10001c8404c6590087c080600c100c160400200000714850b1080c1c040000407090020048450310007850790484240003140c4aa0642c1800c0d42080030072039030342415074410006140081c141409540451350582804200c503138603148514054840080d02d1980079100190100030410140d0242c20b0361070f001c0d02164003d030380b0b403403081c1d9603204580500607060400340b049499415047d001048001c0170200c01058050441021440b050181d4008507412161040309000104030a08148020490f0b40084525040028080740020100b465000c048000c1d29440440507401100480804280541003118401c5d141981c800200b81180c0340d80c4c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 976652455 1250 976651205 976651261
    0x906080924041104090f0201050d1517060f090d0809011b03050406150f12140109080306011715010509010c0f0b090c090405190c0b1207111b040507120203 68
    0x2810b1810644145c85503e64400840703090780c07003541c006546c242c1140c004e240415441e564422504200d1012a0004003111100d0ba140c4840394052903041803402060324424900c46070800c0082d41c0300055803400720300c0034240820749456840503a03002d0309502400c0c201c00d0341c1098800d17002982c16440b0500c1603000f0300e420003101d604410b480800c60718910030350250000d10355041c0580b40c100b141c0c18000e08d201e1044c15160310003a044050035142001419a60010048200141544c11019002100c0100d031040641d61400102c0180811200d903c814104080825440e59603400342d030000c3c01e0305400c0440003e0072a100d14060480c000c1c1151844402c2c01401c0b0100c4c800d003454840300780121ba1101c06003d003251202482c07412244006420ba8a080c11202d0008048075400000d008403032660300780030740c1c0b40303064907000e4010b8803451642c482c1944800d06651141681113040c031440c072800c49000c5020b4540c1e110403108001c03290f618030b1300c0b584000140040d01901c1d0700e07003d00003806010b41c0c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 976653705 1250 976652455 976652483
    0x1c030216050f0f01121806050714070c060c061e0506010e01020a1a0a091e05071d0708040c15030b04050903040308030f060315041a16090608092404 65
    0x40310b0095000d00700b403600401071003004211580142205491407202850001d50446041c54240101c8010502520815034607414810503070762202505901080445c1060718055003640c0d2000c100025226001c04c010700c0d591408100442c50300002510b104040b00c51881c0102d01c04900010103013615604e0200c1d000d600109801d50010503512005034202d100482840c410b940c80c85c01e0440010000c2c41495038400e044400158181c2c1c1401c4031440640000144000da4609545021035640225682e80b00300088184d40d14903550b00785a02418034942a4115103a5103080041000290000d100403d01c94020740540303903041d4000c080030302040b5814840c1d9200c0035552510380c032a074040135000d860200005044064104142ca801c10000340840b40c602e060069040303e03245055030111001d0307001e0300404101402d04000507402c1194000700d030850311040c01000e45030054500c031f00c1080c41035040000300380e240184041c4004640b4000134296000c5210849107071341d403007102c040710800d241d6152 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 976654955 1250 976653705 976653709
    0x305010b12070612020d0e01050c040f080118020d230c1302030606041a070c090e010b030705011b0201231b030f0702060c10090507080706030b1e1c03021605 69
    0x18000b03c1e070780d5454560440c4442c80c0114042d40c8092484c04407280c6803510580c500d2001d1240a22030302c2d000350895100c0342400ba03201000c0015a100e2402c5a04100807888003030030b540c08100703060340d0403a0b146c494541c881c80d01b00d030104201946940002e00092403d02c010346c01143d10005010121034045001400340c00750000c034001620202c0e0000811302060200040046020303400110400307c10b07080c06a41e688a290036000e070342080d42e0a070745850a4520012003401450740c0d500d4114090b10000e402c4c0030008060912829042a4070b084640140056900404500031022180349015030310109a4207919000d9101c13080c40340f820445000c030401141d4000c4250754440b205160076501e810783e540c003000510f41002001c090107001c0c038010840d0380121485a54070541c440e4004e00800307850940d005090440b550302c06400c1c07604090055610381d803511400701d1600d000031001c0385180700e050041180f4a200c5090000c0703200b50700a5900600d03400164580c107544084411001c072a4030340b01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 976656205 1250 976654955 976654963
    0xa081e0310030201050702031c020d090503010b010206190e010e160e0903070b190c09210c03060509010b1509360711030f0903060105090f01140d020a0305010b12 71
    0x40e07a8010092040da041c00158803400040090b80c0c00101128500110314190440001205c0c102401580c4200072005406420042c1c420003448100c1c0200b110302d00900000c0c2d201d03d4000d16181c1800c3e4918100010507015a0108804447e214000c0100403100e244066650003100010303424110a10400101c40c0b180c607200c20300c40e44450700910b0422500e03541e060000d100103003440701110950798010b42848801e02c184a4403900e00c0d036900346150300c0d2810b4503802c003690302002c043d13000100f07400f1008030707800f0601c0b101143d62040c0c0000381d6698160360580182400c0f804550302020622058010144035805801120802c0b00d40c40d200303600820210010f15440030f501019200c0401c000108a40800741c40c5034425918200300c20040901d0101505503800045201039151010424150605040104a014240940b0380c044103040907401601003080520071310750b0f4420440d800004503258140103080c1c5a9016080030b15490f140d18086010340313001c0088034001d0140900003810044001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 976657455 1250 976656205 976656211
    0x91502030912030a06150f2a020f030703080f0705010c090632040b0a080f010815090c0d15050f15010f020f07030308061005070305040e040201110a081e03 68
    0x140003050350b10044540d81140d604000c000100c020341d40c0c2000039407091410103c0d5039504007039a49810360ba94004000e070040b030200c6881c45141e44c8031104000c0090030040b445010701c0d01280c0c040105c1e020840028500940e5401c002d00c2e42101055887c00200c0c0d05001d8500d080c4504002d0010300390071001150145403d10408001990b000b01c022a101481d440a40070b0200d01c55070308a04c2c080e2084500b015a006034840258244001800301f0310b15807041d84603130800c3d07901200351140c4d4940050b0356a143d18154038240340125010104000101c00c02800035a944041e0008406c1c0996041440d489076001561000d924204030010b8903000001c20320034810071a001c51860600b00300340046903a54901c00621080d4802d0201c02a031240302000710400a501c60790b520413103841c056040c4400c403c021401c81044c00024410940040d030030105480513200646449501695035000413502000141040c0429008514200d010700100c60020b00f02c01d4691040c0402245c104c0c942860705200c11 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 976658705 1250 976657455 976657471
    0x170c03070b1e0711160b040603020f1303080702120c1e0117160f14030c090a05040c080708150307050d06020c190b0a0207080d0915020a0309150203 65
    0x20032018000568420070141c22440c0c00b001200000c0010707600d400c240c602030360000007050819946102c014410050700001c403003201206039429103000c40c61b40f15409940500418581c010581901501141c3c090304c00000544410644440c2e490901a240741d0021009034040e4001225048001c003000441c00c407000c5001d454500b08912140b99042d088045111040c10040c58400c40d1059044002d9414001c03445441061b420180d01d1a019040e9403550300c0d68024800d800c0050311448003481c098070350020044a49613a60002c40e00043c91864003900310607801071400c14440061644440d407948a0312498075540303d140c540d21201d98103070145110f40350741688013020910184c10b0941043c030741d20b8481c08000d4203000c5080c1d10b50f4100100f500c1e810003049941e16100d424020340401654110b40009002c44c0741140d6900c035402e240c8140744c0240c5815454030b0b60441089001c890401794802d04075021512400e244400a002c2d10900708103803a001060300e00c0c2d410031a05442120700407060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 976659955 1250 976658705 976658707
    0x3110703030c060606141b1f23060303030f04060908070503121b040902090402040f03080c190b011e050915040f0b06031f090f0b04051503061302030f0f0a170c03 71
    0xc034102d241c142c04030f180f0701111207001ea820340029400c01868007020079000c114012070325a000b84106480000f41d010b500c2c01409d112414070589441c0441143c0d00712034052503603101c03a078417410031030f01805000740000e01c1a000001d14509104011025140ea0828558090401d44440144c0e040080c1710034a913038069034042204000011041c2c2c010f1148080240c409810a65984441d00341296031764000d892505e80068001c0204401b0b1040f088030045e21258410600b01686481009180502400350241ca4800100c3ca900c4400d4891400528000701070b0505894078052100035541c04001d02805030b420710074812400c0b00e040c0200c0c514032002074081c07410342c2d03106000e0304001010700740c1e000c01c80b405c440c401242041041c01001903840700d40002103140364004050204a8400410701d0703820016900d981189650086003441d0860a14170408100c1c114900001c0d0510032040b0300241e240c41140ba0740c030300c10040494114146800744034008110031070b4817801d40c0c40e441440f08400d0300da00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 976661205 1250 976659955 976659967
    0xf0f0908040b180604090b090130020f10030e12030f070503180a0308013b1f030b1501090e0a05042910050607020a03080703110703030c06060614 64
    0x4184406810b00f200581c4201c15000c480802190080d8402c3e0400aa00350300d811012400d81440c04a40d0700403c40b040407546d50b043c41207030340001e00400410942459140c411800d0a661304d2001c5019003c00042c420b038a5400d03d1503000e0014200808210b0b19400742a06c0c8113840107a4100351b0780710303602440015100ea51054022502c6e0380c8002c000c44041c00100c004a00140d0040016000031031098403030003c01d50400a0440e44d18000c00700420483c0b4400640050700d440b47c0c402e140b070103010b200501156444145815030104c100b0301c0340007090200c0039000004c1c000040b24060098608450050700294035100440341d1840318050b22180a03080408641010b0701548403d5106008e40141101d03400010200780640705550060403400d680c11041c811071050044040700144000c427081c2e480c00c3d80c0c0707038041514200700303120180c081e020124054040c113024120700c81c201d00c0a0fa0a03520b10a480c0d1038081c04c920302550003910300529040010490a02030485560000214400c20741405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 976662455 1250 976661205 976661219
    0x3040807030207081005091b013e0313080a08031303050403060218121903030504170c030a030e0a021f0210060b1c060e13110907030f0f090804 63
    0x35104140031000c41c400e0501c00507860b08184201c80070301000d9032010485052061040780f9010000a682c80fa0101070001c084240e030700300c8030800c4e06d01151500305255021540412500150b03501110030f1043c81ca0f0131035001403a0120003481c3c9144009110340406849540d0b140e40c558028000420401013000030038941550f18091104142c8a842d12529181e103a640707520a07a008500e51131340c0c14519900c092050320380481520340088009004180007084080310b2070a9403014440601459a0741c00420188024000c0702039410700d007091016540c07951440b6080c4e403a81b06221075000a4a4142040f550210100d00d075003015400404200060031400307044407104045003002d6017036215000c91107102680e14042d0000424800311980e4452a08209031040804078800700d80f01145011000d1000a6080188a4221440700d1101400000c9840c0c03500c00c0042c1c881180361311020300707420405015815040f8044c07150b9840c00c203005030b40309145404151140e10308000c1c40304405001c240040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 976663705 1250 976662455 976662457
    0x140f0a03053d121a130c1505040510050405030607030203011206020f090a23121b06070f06091509170a0512041a0705030c0304060908070812160e06030408 68
    0x142001c2c50382030607540c0c0b40303406071581103103c046415007043c104240d0400014a02c182e4070044e614a01c6604000302e950b11001c8801c0703030042016054598480c0002240b156094a0282c6405801400307110607412002d00641c0151140d40d111344030303d0001415562290081d20304131181c50424825030103a6551741c2e4082d400251000d106100e040c4080242590740c28a81402070410b900c910700d51a0005040c60385400700c003281a801180a10039950445400181c4d0088801022000103880f6198100180051003118000342446e4040390f424400c0c04000e511200b880341c411012900c121480602c00317000d80b0040d00c0c024041c0b050701404248004043c1000b414100d600e454aa80b03010040100902d04901c140c0d01991991142c80d0144801010103510720380203491801d1050851034002c903e03844078440204003d045c140c0391000c607010000301005aa40c882e0f80a1a80307034441183d90080e24481000711000803d84030440149a42280135031107225646034040c6c0106d20703590352902c80c01d043d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 976664955 1250 976663705 976663801
    0xc010f1707050d090b01030212011503020f0d080703020705040c0e06180a05030304030606030b0a0b100c0302120a031a0604180b190602030a020c0901180507140f0a0305 74
    0x50000c104081e80d801507403803240d07004da10722480d2000c21740e50440c014404d0403503145481c84074581c94010341100c494902c3c11080304684e81180c282c40b0301e142e0750010607010304010310001c1c02040041032039000c16030046090300907914140c030100a694158101203500c20b08807201143c20080c1001703014038189401e524100184809050b483c040d5584001191444d405503100750b40781c43d920b11043c010000103010b02a0443cdc1c0740c51051080d0240c01d000642406910f01507038003407119a014280406000703002401520035140510b58407100f50100140103029141c102030032401441144407036a103041400d1b2002c0d034001c070711903428100d56010014000c02e541c4440a0b404014017900d40c0c5c600c00c000048402408c00380d809913840d9619040040e02d05041101254801da01800050145d04281e0080204901240e0000300e00783d1210082a904841d154a00401030a0000740c80d95281d1103100080003803241c2d60343c0c20032240e81c8075906c40307201c0d9070110703c01586212488192405643c1d0f052005003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 976666205 1250 976664955 976664957
    0x7020901140409021f03060e04080f0a0201182102070f050d0807141f140f0c090306010b0a09090b060712110303010f05040b010503250c05060a0501080c010f1707 71
    0x4283c06140c0006010050309610320344c42c3c080142d10410035903418064000240344a41c06c495a509040c2c0c0c610505000e1440954850361005c1881b1803c28400d401c600152115401c3c1443c81c0600740c2002c03c1d0b042035187c0200c2203652200d400d1400320f40300160f1101200d00500d416003900e401c020402c00f2030042d444c026203034080248031000c00b01c4c5a101204d0304c3c8a200700014142e400c01c002c0c400e80742020000d40000350034605800030b42d240078110b81e0306d50720041807412001d440c0d07680b200e20203482c00358050071034042c071600001107071032118140104001d003400c1e2205d0030002d40c2c464181d03068030307030304911356800c000c00f88080000281004800000e0014505145c80202d895001c40c1e803075a0000d920404240e2103056040005d41810301c142c0c0c8035002c080c40c215295191084429250b240e030031492051054405141305401403140b00c41c0042d20340c0c8442030b41c026042c00051100507280a0050b90114050340d00308004942c000e0105410f95840d546800851041c001d40700045010000d041034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 976667455 1250 976666205 976666211
    0x6031f0c0c02150a081f090f0e03131e061b030c0b0a0b0f0a080c01230a0809010501171f060e041b06031107020d020609040203040521070209011404 65
    0x40180d0f22100810590103010418540740c00f1802001001c079130014181080151840e0301800b114800b072039464050b00c089210106e0700c82c00802c00d40c1c0c000c00a02200a005000c08103009030540c500402e4a800c441c1c0d8a80c01c800d103900e0101d4030b012141c0c2c0d41d1003100003042444441c02100d22807503440e84915802400c2140700e044281c0c40f140e1300140221b45050b0b9181d56001e0901d01d500d03055504048660056804900d41418036a07015a500303881106541031122084070309540300000d00c803002c00d0000d01d04050b40c4443c0c6950b009071801c0415030f40c9030706139400e000000c00d000c41c3c0306020500c0c1342200401841e043d04c40d12245080c42c4200c10b030704440300b0344404010039500078650302680035600c1000344007000115422064a0310126800010416040c07030050740480c281c202c2030f25801c64044031540000950ba00c0010005e102e400713071098029002100300000c0c0440071402c9445800d8860301100c1c0c1d101c07520341e210742c40d00c5070b80402513000d6403420052005501c800c01555076850058000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 976668705 1250 976667455 976667477
    0x20f0609030d0908061003151523041d0a0312180804080f2a030106031509201c02040e1006140904080d0b01090f0f0e06031f0c 56
    0x1090501c150141c660b004a4490030341045030f240e0812206600c006585c14035080d03c0e0669589003404041620031170140c43d101d0784025400c0d003100164100424102d8034007105044c14030041e0226000d6582c0c254842d52801d07100080d48201031000710400102c90f00600207503003050785c0075550f0720070000d036401015644034412a90312a42901e465540c50042c0c40407501d451804444a18100d07080382810031f15000a0007140708242000c41030381aa0103036169060400c108400400e0040000f5880a00308140b114048022001d4950103666014000c15444403110315290241c1110112030300020303000007100e040d043c041d0b0718240c3c0c1c00041e00e1004001054440d0420b151600d0899803586421506980b604200b02080d50444540348140054510705c40f907203415140e00710940502070424090a40714484010343c2ea00c03e5980401400241e0928881c00380c59000024400700b05025020806c02e252b008a22245000900e00c1c0d00e801100c203d200340f414012040c3e50203022060420307401e011902c420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 976669955 1250 976668705 976668709
    0x150f0301080304051c0b0114120322120f02240a0e0901090e060606070c05034804110408010c020a050106050f0303120702120403060f060902030c07020f0609 69
    0x114000c1c4440740007140c0300da00b01010031030100b01001550300e00e074020750f480c000090b04200c58039045422440c0303044144d10506c40403560301d001d44e407502c20203408000303070308031114a5948464600106110343c0c11410b5885000414200d5001c41d03010780b614003030218802c01440c0003c0412408410021036010303145c0000c0d10780ba915041881d101001c160800c01c81c09031424001e100e04e005002c0c2c40070500006a0b001d4031f080d210b1310090141c5001f110001400405d01000b409684014100501103612000d1014500c804060404071404030911049140d070079960100460145001041c42c1c0713007034000d59521f0800005182140d0305103003550050100045014003880741c042040c0b21078010303040040b00340c80c20500b151007642005109540403c94540552800000e85520850086192910b40c8584405918200b45a00b606070202400200070040242c642c000c450f5000c20103030103104c01038482d10440180c0c04111485a1400428015100945410500c5003001007000c1d0040e454410a600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 976671205 1250 976669955 976669957
    0xf091505060313140705011209020d050601060801080f0c0604120c0b1c05130302030703300603140c01020c0402071a04060204060f110606013b030c010309020906150f 73
    0x815000f0150301461420500c120b050112401010901c042c0071418285400070306200103000807100132651350f4018034215100c0383c5281c22580c1d048001c444d881e60352004000e10b6a03030309018080c214041c40c03510f14201440000c01003007c800041c00c45040c2410715180c0340c0130b696403174002d454120014900113100710103035008100c1c440360503200c2403807241000545400c0d0780b00503040b080c10041242e05800802d41c088240c4030117640c103184c10310800100c0440440b80d03400c90000908110100b82801b40104130580c0318208036803003400d08401030302107121150380301d20001141c9400f5030400c4244850a141507030013000e8032446015403c000c402d15403d00c4100d07540450382116520f60012b024421690071040710110a50140340c10f6440801051100f80c4401001d00a541400002e021051148050b0000420049440d0204a00d0840c0d14500c0180050240e10007034000e014140b04415954400c0c007a50055640282c21007415494081c20700c11800d10a4202c0c86259409014014a9003101300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 976672455 1250 976671205 976671211
    0xa170706140a0c081311060d0507120b01080403020a14030f0309010e010b0603100b0703030b1e04150518070504030f03020c0306070302070b0a270614100f0915050603 73
    0x140182a8505120800201c40891141c40141321200041003e40c4003030480c162495039000210019609045000c141c1900804082d1030100d0304048c10000025440112403560900750740080c084030b02901c1c01580c01c0c0500b520050011381010350b0800c040b0f0b9901c50320a6104910b8400c4a1800c1400003803261181c00941e440e0880d81d444120f00b141100c024015002a540e08882c01c42c03860518503a07042620410388284213030340341d01049017010301d8000c4e071190b1100c11010300103000c4d19400228000314141a034103001d1096142400001e22412041d9014090703410290814202e5883c411f03038950488002030515080003410400440000c8021030f038222110303c01d400902d46584850300301400c00f90018140b4040500c14040030340800c0030b0070060354010140c0300c0002140204500301c2e840f2035142034440300d000c01c0c00e02603500c1006420b40c0105130306014402c0d5904151600404542c2c40c041e2031051101d8240c000c041840b00b01402e51200300355030201c101402400342c0e1000495601c0d0011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 976673705 1250 976672455 976672481
    0xc010603030e1201060e180a061a0405010f0602030f03150607031107060513031e0b011d0a0b0906090709180606030f0c141305061222050a170706 64
    0x240c15400410304100e070083c185441c0d10402401440e040080051403500c000f0002c0048246000c030030440140d0a1008117101e5410030018000950082d030180396100d0240052401540b500e000041c541c208044a001681c1856000d141f4200c42c1004440e0300e908083c0c44010000d0407915112440c1c0d403a00300500c140344c4a40c80b244001b003996502c86042c01070a07480300042c003030100034440304020790711590002d0f6644141451a040f030040b0a103070481d20010001440c50740b65000104200204290204009540d8188258a40e5400d02c0810503102c841c05540c0d0466040004503401c3d1a040d002194481c10600c2c0c28403055955900c60700c240d581d8160908a103c0d5940307424010203505008414001502c0102031140030403202000385900c0e0b003100c1c140103004002c03510a2a0b00e2024800344010600146000c0e261403c4140b41011a50b0507038400301b651644485ca10450350045c01c011140035001409030841c1d0140c0e480703d071006184144050500e000401c44c040c0011500d100e048007410341e07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 976674955 1250 976673705 976673717
    0x15071706030607110c03030d052212030c1e030b0a121106160611030703050c0a08010b03061c0c15090f0909020d1a09100204141903080703021b0a0302010509040509030c01060303 78
    0x18044000b4042030381c0341100ac00c0082468030000c2049150f44082c076062601d40000d40300c0d040038046071108050f40010550700d00141003218215030503040410014000c0741c08840f050341c0d4801081580d44410700040c20400300f00f03102d10f8180b6100e009400441000c00d0503103c03603900d0355035040841c0c800310501440800d000c014404003503898031400f54000200c1040c1071400101020242c0480c0e01403041c10100c030000000100d142d1130740e803010003105012208010000400d49400621612140907980c8000001744e0380c900c0140c400c801882c221000d252410900e117040220510280030320290030b0b60030641d890b006000084001101c84d0401c00c1c1114810702e41d0602a84a40c00d02640f440c4100ca018010f000c1030060a0980311031100c1d154040764100b000d00c0113008206120022a40301520311310300400d45e03400f8146c0104001011a5542c00c90103408402d05041040d002d040e0300000e030001e10140b100e00c400d41420f034059500200100300700e03820000030903640c9095803081e42044001800d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 976676205 1250 976674955 976674961
    0xa0503090105070c02061b0c030a061a01020d1202090a1a1c0e0c09041403030705040f0b070b0408090d083106080705030a020c15071706030607110c03030d05 69
    0x70310a0b0341e0022081d1600110751500d54002508a002e40d00220b040c40c00850106c0055a40400c400410594040c084c2da00301103481c240240100a010b4007016414400d01f100c0302a03620100c3d201002c1d12064540ca5000c410003100d1000a401c05103c1c65081746e818076021441c100608600984a2a60341c0c90701d60f40d001800100c01480366115400c1203107410141004101c40020504291407141940c00072107a6546040801c006a61001c5a01e0903000000510003090340c0000100305031041d140140070742c9507494112900c5803042d0900600207850200102d00002c038584000c1040703107002030000f6503907c415140c4810713a61007641114082c110b00140b40c001c0a5441c61010341508805c240b95020034581300380a80900002402101088400000200048416816901c02d00301e90300c02c80d1b5810710510440c0d0394441c0199802c20110b4001a8001130b03030056468158818580a8080c140130b07141d206d003e80c0c481c070f008070b10004140070300022013900341c070100041c080300020f0110203e5181 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 976677455 1250 976676205 976676221
    0xb0a0b0915041a090624030a0c020601120804031103030d0608030c1b18130c0e0601173c09010b180403091401090806090604150632060a0503 62
    0x912101c03410260141d07000d5050780d040d6078600b5001e50005043d1044080300c280081848100c00110340d01c122110380c01f00a10a007102e0a900031081012542c0840d1610b0343c03201081c400754444044020013000c010402400001c0340000e807001000c1000d0100d0f400c01c040b8404c4581558040d4010002d280d002003402545043c04000301034000840343c0e1100c1c4800f240c0c0c0c000c40c2c0018014141800140902008903a0b00c03400c04d0400c41c11160071808203584103850f4070300301011910940d01c084c0042c1d0401c00076203c00c001820054041c0c08440540b003176103152030440c6c020115011412800429803229a0140c83c18404881071064054400001d41c0c1900d4200300a0001060000800c103000ca110810000940045410301030795030032001d82101582240040310500d1a507000b02c40c046c003810003480100304c0000b80f01d90190b48501000c44400075100b801604403581e43c42030918107000703030101190100c185201600c4000c188a0103603800b180010104090364485030b102c0d40001c8002040184c48 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 976678705 1250 976677455 976677461
    0xc0322080d1106130804050f06120408030709061d0d11130e010e03070b0c0f0d0f05040203101505122d0c010801030807140c10032f070b0a0b091504 65
    0x804d5210140c02e884103519120304126008034005c09000301e0b4005096440d6507242c5d000e40f81c030009072180e00069841d06140072951500142c581c00f000c900c0c1c001000c00d140e0f01030503e124039481c00c88004500601106c0400c000f0f0302c2c81c1607058540b00c140424031182a10781401100100183c03690214181080454442c01c40f403500c4a009080c0e0002d0102d14000b603010007a8680044142d0101a190305584010280034415070116450b8640b07032a844240b610703400d8110b030348150f000300c003981e9000a60200040540311b0314a41c00c00001c0e035003c01405549080c0031600f409041d03581c00c4480b041d19203501d4408040584108585a18581c0c3d01410300c1c0000700b0140342c1041d4286002181c6500d075640d410f5550166142c0202110350200700b4550f0310a040000412003100100f10f0700e1103620085001c2c00612242d0081d24281c035141f4020380b800004943c44203624811020328518011454460381d0f06200040c3c0b040806580318845181a51384010041e030181c0c0414080c100c0f2204200100012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 976679955 1250 976678705 976678711
    0x19020a050a0b19270e1014060f0c06010806010f15200102070c06120b0a031211190b0a0f0b030709230c0409060b0c0322080d1106 57
    0x1140422079400e000c001c25820581e200a141154451488a61001c0941c1c0c851111854261400c2240b10640140d01000641c141120340b612003020007901d5142000d41da140180c00b925004041c880c0c4480402d0603c100203185800c00c0c44c4041c0d09004078000640c0c01c104080e8486959540081c005020114001c911807000b8844120710a1710705082c5440900072000d15900708a114115119490f02c000007034040302c4240da4000080d4042c41d882d1b080140622082a540c5040075151041c0c05046003840e00030841525084507403840c0d0f02862407400c580a105601c038801c5603005082880c00441414103c0040030f81c8203600c02d505500d041040c0030200d610f50310003d044241040050031290701e010400409440d6440302c007044094201c0b10200a1580b55000b0803d9036001c1030410a500c034126001d44162485d00c40c0c00d0220558a5104031302c01e014012045100307070010030002c049802c4011103e95130082c03a0bc4484a500c0d6030350314013410072100c0415140850001c401c1c0314030511051191541c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 976681205 1250 976679955 976679959
    0x9060f022b02010c080f0403080606040504140901050a1a0f150406021b09040b070e0301060f120c290d06150e2806080a11071202060105090106140a0c0519020a05 71
    0x24103107002d00c6e100d80d485501500c05418040c4141c040b500f2071311500d08440c050301c0003a2003031040302c4101c400440c8230310381140e600c040c03946024040354100c1854041e0103000c006500c608280c500141c41041601c44042c0e02c030b1940840e1020026000b41141006003008003aa9000f0304560700344052103040c2d046004c0030b81c80c0300f0310201e01000001190440e406030003201910300500b0981d900c40100740113042e40c2d0040d002502c3ea0200000f006210030b1035440c60203200d905403c40d020744da070f50218022240104550320490340e010584003d091000003900809001c14004079240e5628010b02c001c2070789075503400002411546a010076814603484404015448101051042c429081d898030481d07003030f000303440c10052400040f884400300ca400c40140380b00c6180546580b41c004c0c4c5440b01140b03482e4100d85000d0f0140d00000039903860088035440c100c522646031865540424036504105500c070020510a0020b640021000b00c0d00c20001440e190908040f000c054101500410a00101a07844a8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 976682455 1250 976681205 976681217
    0xd17010f050901121727191802090d0b04110f010f03020c01020d050906011e0807030602161704051824030f030c010516050a09060f022b02010c 63
    0xd6482d80c000c483c2c1120349126460121003001d18202d01d01c416165101c50000300d01041820340480c6c3d0404124082903081040d42107802001c091000242c4000103280018400000801c610f90f20b002503503a04010b88000149000081400101e40c954405416034581c09500300700420407101c4590107140103804c41d0103c01541c08280001e01003240000c541041580128803815016402d406603020b52403c21001d000c24608603114a0740c0312424400c1c0070007481c1c0a0407121a00c00f600022009840c00e80300500072042c119191f8001031751004a990b00005403005810340400c0000740c000011070307010603c581d0786500c3e040c00c22480030501100705c286980c0300c0060000c0754640040081d01c00084c4440182d10040120020341009032a03050417045000019010786245019405240304041440c44203e000200345030864860180070303140c1d004505940010b1111a005001d40c500d142a18411200355110178202e0f110701900007000182e4040400c104681020b4080c01070150612a910f001d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 976683705 1250 976682455 976682459
    0x519091a090c07050c0f06070f050c0f06070c0e18010c0e030705060a08060d140a0807030914130e030d110c060f190b03070e0408030403031d0718020403050d17010f 72
    0x50300c031511204414490355030b040b69086d098580700190740f0a10b40107a40454251500d04140307482d211814090362141d00304002034080780ca44a020381d141c0d0703034216101f03020b0075080105003c8100d81c05485a001600380352503441501e0750900941901c3c80003551040350900c2d1101c28140ba181054101c036100d020180900741c443d0303a016400c01da1200c0101c868007407000c0070b400c0003e110400305105041c3c9000710b10000003031200640c0101038661190b91404041c50780d6940f140088481d13891015445099031118002600c40c0c0c0d0400c6510038490002d0361314050b180c14038042128a1201c40020010000c1030040c440300e014081c8035400140c00d001c000e064601014a805141c2c4a0207400300800d035a03100c001101d8400700116806410380342500209418a4100300029410403101200007a0620381140786005d04d1022850030348504c0c10082240c2420f000003458101c22081002c29102e60911000010440c1001413640b203020b00d0319001c03c1540d43c0074116400140580004204244803142 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 976684955 1250 976683705 976683713
    0xa05060409020a080d020705031c0503040f0c0b1c02071e0203010b120a060e01060605250615140406030b0c090d02090f040c2c130f1209090e03040519091a090c07 71
    0x20007503000f165850229541e40da14130b0b1000c82c3c2103010f8405040e253f0100d60216201c041070000b00494260011000032408001d1301349030580c4185c600090040c54484c00d00070503203800000c1120901c0c80103001003000c03429507001c1810211040300c00c5004d43d00c0b110200051005501c00c144d600d0310b20300001d01105040c1400601184541103c0c9111010220030b00803202800281c990441d5a0000040c44869518a00e0001440880c0a400c0c040302d01c07203282c0115803910303100309402c595002c0344662a91382e0300031584d80607401c0001c8058201c241c41340c60000580d5074425207072140e158012001c0440c00c060601280041e400d41007060305640305a60402c82d0035103154403d01e0b8074074800001134580d0f103c04044000ca000c0c01401800c40c00d16541c00420480724a5800144225541c0d8080c2400d980380c20b50300c00d6070034546101405400412091029007080050000e40083c1400e000079403a13035403001c07001210203010801c402c4030342d2f0840c05801494691007854000002030403803030130581e090725 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 976686205 1250 976684955 976684993
    0x3e0102041a031314010b12030913020f130e0f0106080403050306060f09041514030a0f140c0303030412090f03020306160e0312250b0a05060409020a080d02070503 71
    0x60780e03103000800440010000021003004450300365014840788040c140030003c01c0d0292844481c00d84c4102c0c2401c101c01d10500f4000151182034000030070900722001d0004131140258401d42c0c406525100400112034104400c000c8080202000010043c0c18908901d00c941981d4041e0008800c21503810203201c08aa444029a030300300100316842642d070500248805946d10035003540030380003400d2800a40e4050030801e411000c807400d40000d038078146904d1003055211100440300038070718802c94030b07682d02103054428a032440c2442242140c2e6090a0140000e140d038000b140c3c05c4590070315450101044035030090803036000f000701148602d03540381180e001030340f104c00003825584a0160340c102258894401e202c80a901700d0050240c4144a0110305244c07410762100c3e03040441c3e05110440c0c0c05000000c604d40c0400345e900030f0545550f40d04c5a42c1504041c0101a00a50784582c07650700150150713a4200c5054010000310008000f084983e01000e4104001c50740040d100b5041029075074101c00c0c03440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 976687455 1250 976686205 976686239
    0xf0d0f150308090415030b0a050f091009020d0b040b1b0a1209030c08041203140405010c2603010b0d14040c05040c11030c0d1b213e010204 61
    0x620b400303031a03041000c0400e0041c0251420003c42c01c000e10400400e11141445040c000e50842c41e09210071398070001d140f0311651054600c66041d9005006108041d42d09a02c56603003584006e00d0b0800b150455190400d0140068a0640b200c100301024000803040444030065801241c03c0c00a0500185220161106800c02c4884400c0c5860308404403c052142110b4000b855110204ca900d417a10340d0b005141b10807416400320046001071204121840f00b440c290703030172544140d5031924800241e5982134410700d400d0b40c0ba00c0201111040b411100c4070200007660180c03c1c44400c554070740e50245c102400359040101c0c80b902c0c10300c0050a010108210301010800d070744080e607003c038103070082110449544080b15000740f203600000c1164081d81c840840d42d540c2c02c00c0d0696a218014141c00314071078503d55080001003642421403130390b4000380d8005245d540303919854100360f10045402c0444881012050101d00d170301207040d00103a206090b4106281d10309080d132100841c1814100001906240030b21 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 976688705 1250 976687455 976687463
    0xe0403080c090d05100f0b04060305101d06040f11040b0a05040b060f0c150702030a0203040333091b050d0213180302060609060111210c030f0d0f1503 66
    0x44611042e11144901c0f002070760301c0403c4981583c0c1c00300910004010003502c0a8109092200c060113514241c002d880c292038000000d80411004004010001d1202d01c601c000110380684140601401c2440080e110307501504a00c81c1c110708c5454428614074980c1e0303c4500c034500c0c11441c641652580b0045000369203080d00d0020b10614440000751044c081d55690351106031001915000000340070440039650384069410603440d0f11800c01c240d89902078500328400603841888100b000c1510030410b00303801c00000c01c0d6440060300e1040070a090300310b0000300c1c640c055200d010040802c1000003070b0a02045802c1095080a428440010f4200a0508029202d0000c000c48a00340d0081980503021611440745820100c0011386006502c6100441c1d14030700c40c08614001510a50044c40f040d08001e00c600c001e0030303280150002580281000040381505848140030004803040104018038600d4140c200403a10384220b02180300c00c5d0f41c00b02c0c0680c008242400c500d0148041c2e0341c40d044003560f0b44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 976689955 1250 976688705 976688707
    0x9150f022802101101020d140a0905030d0b0d02060c0a12020105060102100902030c18150910050d2111011a0f0919020301060f030c0e01020d0c1b1502070e0403080c 72
    0x320f411101002000d90120030795200046082c89015036603c01c2540d90052060295150b548003d200c04455840b00082d00310b4100708210b200d03981c03035640102032840005100f00e00400d0581c010403150381111000260a038030011048080c4065942a4101c00340e461000340700c14640903000035141d0140014014245460305032803c1155410310042038079400140609000804e44130707200140741001d988400310782c494404c0c2803440f41003590000e480b8540392820b0601141ca801c1c20320100004084081d144075410040024820600b05450201c20b0310541d80c0400c2038504407002d600712411101d002c020302ea83e402034600c007620354040c0e5024802c0c0032a070316206d5680e0301320254023500780c1c414070f030641d03910010000c5a07607074114074102055940c030341c0d0401144000007010b80b040701004000701d01603800500d00c5645180309181e0441d0040c800d003030701c0701600480006114079079866009900100c0f0804d000c0380303d02d50704014802c018000000c4110603820140c501502c0514080d1102e50743c0c0308 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 976691205 1250 976689955 976689979
    0x1c020712060b03011109010908010513110f131d0708073c14060315040f020702040204030b040201020d08010b030c130b07050a0c080102040513020a09150f022802 71
    0x640d9444002c12460243c0248124910402c0f45a0a548980655804a080301c01c0100365000e052042c584501c0000da42044007100035140d8092003000d8200403540309042c980090b60039182e00c80c030661030030700840021805030326010b02c440c020802e450100c0c1040d80030000c01c02088000040110484505540d4050030220750360300045600c01c41e48115840f1028203000707600c8110144e15100403501400020440d656101c406c1058610040c1c0703081404034110540e45003207180c680e014030380702c4080c50001403600d01e180e03003c141680c00c03640c401d4070b0b1081d0400c100302c155601800100340410f4540740c060555810101801098000907220703812000c40425044004511800428094000441c0083c1c60744000c0c41c2c0607a441e03489840c211000380c04006e0003da02c1005009031804d4a82c003d02e400c1d039103c542d0382e03884001e4020096100411451a80001e00c420007200094002c0580799a43c1c04000203446019280582e03050211682264210804988001035107001c40c1a45d03040300e91080850b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 976692455 1250 976691205 976691213
    0xb0a0e060d0b0d03020609011107151a120303010e0106080f040f03300b1509010804021f0801230906120a050f0a02030705040c0905060d1b111c020712 66
    0x80b0306002d494122109002260925400146803803081103048020b102c3c1000c104d01428840c004d09030000d146441c12400100c07c1d049035002403920150341c2d06200c051a559070000785490001c60200011504000014040a4070708420320713001d80001d050041160a00c0b00d4040c1d40d44100400c040d1128000707081c0302003018450644000600c2c0810250540060542c580035045c904200003000f00515003102c07a112820000c1e11959a1203030028598245070011006403802a07000740202d074403002505508403004000c0480341c00c010140da03118000c96041044480820206109140c040c4190440c001510ba981c1303000304c2d60180c401c1c1e49a480107104d20200b240b9150008000034100d000706000855040e000203800441c8a000320200d42c1d0040e0703288140401c0b181503503e1800083c000c40c400340b1190501c01c0051000109103d00019400d80044003044141c9400060800107030716000348001c654420020090080510301602d10060b203181f101940d514043d100c2e1010300c2081d800050240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 976693705 1250 976692455 976692461
    0x10b0705070e0709170a0203030406031a0d08040302010807111e03070b09010b0f12280c0f0501080f06090414010204030c12170c1b0f03010212040c0b0a0e060d 70
    0x2d140455241d0b9003814806005803602490307002d81d0401c1d205141600c0da03800c500080320380585802401441c503290411000701c0203007110b4000700c0d2030280c24080c000e22540365a100004203e0007004c0781500c0e0341c214800140040741c041c01c01400c00c80490b4214480c5a004910910502c00e014942c1a10301003005409043d40660380c0003800081510040195091040d0054182c8080444107641c3c080c10003800c000700625001c9004030305502c08140310740004040c60700c0304e450300c13400e1120721300d8a00c04e0755481d50700000981254201c2c2c0c155207020051035802c60013040d000300c6001d5084d174003850203601180795240d00400103807204010a1a5920454081d4111006140c0041c080581c0300c0c0c452403040300780c2c4071550b002c4400200c1d14141c0c07a5500301d0b480070744811110540213004240848010307103000440e11742c0b9182e8003414035110810070795000d00c0180800c82040741200f50303600d424102504d013103550754840b4085460030050340b050796a0044a103001da442c1254410b84030f00049000c6001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 976694955 1250 976693705 976693709
    0x1002070c0905150a270b1507050705010801090c0c030c110604060804021e03070b03061305130c08011a19080a150e0106120f171303020a050a050603010b070507 70
    0x2e10380400d001c00703a07064056520900c08140e480400c0141c0d035144901c4440071140601c038884400f00c1442110440d02d8112000080000784026009007100b401c4c29450340c041003040b03a00307a01814042040e540c100d0750217401480300c400200400d082c010405004116060801020807184c5040c0b8401c00c0000c40c90140840009081c4e240c503191121405040e03554142c40c240d100324076949210390480c0402a072010001340190281100d10702d031000300c0352140c1014005a0f4450300541030310544907000d100315442600c140c69040f0f150103c3e402d0040c200702080e0004005c0364100803211080148070444110314000a0f130704110359031080074440e5003070a5250043c04c0b035409600180710520100c141d410080240c4a08200110b10702c1c020118201da1052003111085264903601a01042c0f15900441500b17010350750441200350300ea0000d140e580d0254911f0040002e40000600541c100604680040e01c1e06450b101100c50400740010030a000c1441440350b442400100d12081110500103400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 976696205 1250 976694955 976694969
    0x1d04110d1220010f15050d020a15020309060313150606140d180b04030801121205030910062402030408060103020f0a0906090605040c030216020f03190b011d04051002070c 75
    0x200d41c0000000040c001c5240c2d9451703240302c1d1040116a41c60f24000714000a42e0040040ca42d9518050303881c040c04400c0e00752003055000500c210881912001c0c0254492942c204402064980c646801110f612860080c01d10380c61070700406005485e00300040b6121481c40e1420301e901c522a10b081301d005003064504000c80d2250a083d41401c00c803079a04c5c080e0185210703450b4140c2e941e07215400c422001102410281c5032203448044642054094001580c0014034078090300d42921280220400381c5010754410040e407000202400110308000c1c010f20503a04851016515040c035100300c540d40d0390030600000c0c0c820320480e1480c4000f5030300c41d10040c0c014444500c080c1704265890300341c000180700b80d05c070340ba006904029101c04010f01c02e1080b0740d9009442e090314041281f1036001d100d8840d000001d069018814844c00003020440080c1400c0198030504502c6210340c104501c400b011002481d43d01001e491a0701448001507000c182d010005110042c0143c5078070309410801c10306038050744280 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 976697455 1250 976696205 976696211
    0x903091807030506100203030406110c0f06150303042d08120306031501080307060509011806230106020a030507081312110303030c1c061d04110d122001 67
    0xd110210091610384a072100340c400304856078036102070020111451280c040160410000200001c5040d84401d1800d4090f481040c100781c10149400e160403030f01c3c0c071207001d1a8044420004920955451800d000d01c0980140d8180342c940442503400b1383c039608850140800000d8411040724400c04ea2400500701c00c6d08403a00088a9900c84406034016600c0f98000d0040b003134014400990f80c001c2c1d5040300d0564005510b820b180342c136070200502c0054444182c9548a40c030a4a01e48080500b662a6500070100002c0580d180b50007013070a5a901110304144212030801008125004586022a1601420f04c07654990042c58244520310588640d18200703c1c280101082ca1109120102e00240c8504107001859140004040d030b07902040b83d901000301410048001c00040506207895600d4a944c00403a00341c4d25000d056001e82d19249850810751102c00820090100d0890b44861000056500000c0f035403054440300c000b110045201005e00640080d494400b88244400d103c480c10034600030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 976698705 1250 976697455 976697479
    0x414060c060103211409060a031b1716050306060d0b03060f0f1e0c070f0209070519030204031104090f0203060a1d012309150112120314040b090309 65
    0x445801d0010328081130482c455180c150014a00606024889203041c0410781e06001c528030030408990700c40d015210402d6110001201030048003860341d9240d1710151074441007106400505011035200070b000d1900002040706d2181c12540000c200c9130081070503203140b90703283d000c55142c4003d400c5000c8880c2c0c05118040402035200b00d043e132150302a804000300d200c8607841d440c8217980a921007248103083d444480303000c604880c8020000304a40780c8036020f84400480c07145c0000d41c41301d004648800c04030310009210480c040c50100624507a96560508605003421a100c1c84624803030403201034012a5074090b00300c1845980c90402c00c005038020111102494841d90300b401030000240741901d4610b03200b0041c0d14200c1d041c01070307c0040c800c03501c0d0804414100d0030a003002e10000341604c07166014030a01114a121043c00d0280641000c80000d41c03e070303d03245010320303813010914a00c50816141c400c4c0c0303c000f0500070449540040e009984443d49446d4025100d0841c440c0c214926481840d15901c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 976699955 1250 976698705 976698713
    0x30f0306150306010e060a030e010f2012190207050a0f03351510030b01020705040c0c0b0c09210c0109030c0b0c0705132009060414060c060103 63
    0x540c440d84040e00c5046200001201030403440c04140c071002c2c0800c200d4182031065061803000341c50008481d140104020452030a25802c444c12030301c40c00c800c01e89440600d07454180300b8102401201e40b01c4485842e00746140a1951480e0004c0d00e0710340f4207070600b20320f040010307001d806032881541c001d400d90700049043d00d44440d003840c1814045000c80c12103007007034403030200d10414503405c0c003600301d0300ca00d00c80021040c01e403c3c0341c0c004104071a03510050513801666151869202705c00c19a6840000303c2d02242d000280c504030305075003c40d10981c108407038840340592111324103100541c0901601c034580c496511021071030203004031003904040054054084980c41408118580303090340140d528400c01d1100442c0c0c1d4011900016000c5103612200300094401a402002e100407058141c803060f035200c0340094480a0760601d800e03502d1b0b40380c00c098104568886628140988801000e510700070040340801c0240c05a0300ca02203005042c0da150040b640c5941d0101c416400b4044c1c20f41d0a95a103e00d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 976701205 1250 976699955 976699957
    0x31a09070b2a0606150c030a140c160609081930090906080a0308061309020316080610080715050d02070606180e0a1403090a0303030e0c01021f021b030f 67
    0x201d40f480354100c0c00701c00d02c0e6002050b04641283e03800001442c41c000c0b230b800d07003513611240c031940c50f00e0700042c04c000b0302c1180c0d04203004801c512000d00903040350780c41c94180700030500a5160048402508010308003500909990800c02d19217a2041321011b018222541c96141c0c1c01c8603030103070302410401c0007511a02079071100244040d01d0380720b003003048a59100c3d0031180d5241e82080d070081c041903440c00426410314040c04c00c9002a00c05100214000340c0d0f581c00320f82085030b085090070f500f102d00e580910020701d06000d01a4013624108810740e289107800040e50742e900319485820011001680d1580106114108440c0340080c501015561540c131460200d0040041d442118030505038030081c203403100d060b80148040f542a010080076900225140c2d65031100e0b0f00442c40c4810301c01084400c0300b036165044401c00840c0030f5180003a080c885801614105028804082c2c1150041004e4105080d40e00761040d040d1540b0b5540107888001d410624400e40b00000d1785800244408a140f01c284d0075550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 976702455 1250 976701205 976701211
    0x16080a0f0c110706020a0506010306050c040b0d020324180c0d1d0706051204020616060c0201140912070b1f09021c0207020904110112090507031a09070b2a06 69
    0x40c0c00c031101c2d103994004c100e854000480d801820f9070844401080860a1900269003003c0807070029407074207036290080400c503803100301d41e403a4098011080102ca6400303961110381c00e0402100c03c1c1c40d080c1c6298000b809084035100c507442107440b5034010a807a50101000d4411070001e022081010280011200070f0f00a801503050509101744440410303120b1080040e190203030340d106201c407810340301c03a4200310468201e09002c010072024a580b190104049020760074001d44c10b50000140f601124a83c1c41c16043c00525070000c903848043c2d2110b170004400111041c0a80001c3c0030314081d10355080b20710418000c0450000440c41400340401d000b10b5660050141014200c0d11341d0440c4c41f900241030903401450703c0654000280320000d0003280049241d42036101052511810800b5080340391011207201400030780d2507620054050080151184042c80300712500040d9141515100144654450090248248201300440c44001c030480c41d08034014001c020300022416500401d100d83c0d1344103011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 976703705 1250 976702455 976702487
    0x61803020a120e03030d09150903050c0f0606011205060a0b0f0408010e06010f0303210501170c030a02061902100c110c0a03080a05072307050306070816080a0f0c 71
    0x45040192101c3c02500c1014150f4000350145042a043c05a0134000345214001034684808880b9990756080781480307111880c0d4401e8680d1034032644000102032502104404d8843c00d544076005105250380c214854a040140c0d016000c12690741d000e01180b04004e1a51106500d03050104035101c80d269828041c20680e2659030080118900c1241a941d03507810a00c200032440c600144103102203071049428036000640c040310210114013680c86401103c40981c070001008002034850100c1c038005114038140d00d103048000341441505600011468841c1c1c0a08010001e001180d00242c64028000103046440003981001000140c01020300784c00403802d41103690303005000303061000c6d01c1c00000702410349030400b001c90b08044802c4020742c2c4507071001506444644114552220005003146100740586641000e081d800745028241461b00b0350190524041c89020f00c1000341003840031160b610b4490306072800d40c420b0707118124007400809006005038210750611142d50066504030307030782070703d000c0d4a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 976704955 1250 976703705 976703723
    0x9020901090b040f39080c0a02011409031e030103202b060b06130306020a0327060c1403040303050c07020405090105012c06190e09010b0a05041e0504061803020a 71
    0x40d52107005803116510b241d45c0850b40000c04110036031202c40141c20349103224000098031100c5a8100c0d6050601210014490b51000038103d000481000e80600d1941c19820320a0555045684000780540307010f40c001860013100007514030550711a811124015100d0600d107400800e030a802c0c01103002e41b00c0003641e4203403d00103034114905101c0110b490101310307041c1c450550360444d035808020b94800003442d0201500c89011840c520107004203516100d00340c1d404e208080c1440d00c0c10100390b4011910710070910410b107000340c2102146204a0364843c0e858600043d481e9034528a400c114040c80101941092410040010000b815072145043e83d2101154030407900342d001048941c002406803401c125410400031490500300b4840000c5170700c01505005185c5503d0764000d95203c0c0c0304564107040350b910703080200303690b00b49520644050324065501b170201e20400051510903108000e070b8010704503982e40001d000d00c00305501c034207128030113641c0d00318002e03609042c02983c3d410004810740300103807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 976706205 1250 976704955 976705031
    0x50306061021060515030f0a090210030507051309090c050f0102100e1203091501060c020907081806090c15032701060b03180c030109020901090b040f 66
    0x15141841c0c04215419070346075035400208402c0040c2c46100b280c1400a403645614020850303948480e042c4d0000014102c071035440b03203049081c01401220291800c0d0407585004864000f5032100025011901c0d0329090200d030390307200d0340c0c3c0c1103500784904010981411001800420070f09000c0c0c011150143c00780c0d160f030300e40a440d4010040003003601400709001d6407001e004040f40319100d030081c000c41d1000e60203035143e0030203002c1c14843d1540304641c503140e80d82101100084074807001d600319001d00280d140c00528080f081d07000c14400c52000c1c09000600c00c2180000c1d0702c80c2d81c07a02c0580f5220404034161845030401680107607546c1a4220000d01c1122b1a60f043c048460b40ca00a41c1d106511846050b50414112407110000001a5044441c69501c0d41004181c0800f4034000794051080130040e05070328084401c0030340c00e1003100181e40b84664101065500940d4800e003904d41520104000000c42c407051000140050500c01031203510075080902a00f03421245090130360003028000d550700c03401d034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 976707455 1250 976706205 976706209
    0x60e010807050d0902010c211d0109060318021513091806020a18060206100806040b06012106150e09040309090c032a200307020d02030a150605030606 66
    0xd14100e4007000010800d000351038500e0300c0c030b8003d05a502d00604005640b1b44c500d458111aa0101e1160104001d1202101420055004400104000342101119211a030310400201795400e14800d41013090780760343da20715084a481c91005907071075000700605a408200c800850b2a23401400003078410000f414000203503e1b405000d141c00150101a0b82e0b212040b02e5602c0c0c1e0000e4000108450801c00141c1d600d1030240704140001c4043c00281c0c0040045140c05215518441051303009a030180d004441400002008009a5600b1171001d00301240201c458a81c4120ba166031400181c0b012418140300041d1096a1202401191859900c03c2240308200060242000060390010009403a4140410030002242e00000c40e5189038a0045014130752451400802d840c07046044024006100780010400d4215070380880c2c0c441c0000d81c65112514014910381c80f4019948041c1c01014041c5d41d9104540c1c4c14410340b8082a03102401922503030085240754000c1c00940901c0f4045d208540201d07181e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 976708705 1250 976707455 976707467
    0x703080f1003030c02090a02091507020301111c0c0516031e0302071a0a0902041e0e0c010c1b09020a021c020601050a121502030c0a031d03031f080105040c060e01 71
    0x2594044d01c0f0512107980690a201c1500790040c145014164244145601c56a888000c0c0040000f003460060320366103540101800c45003440c030304004a03102005520480440c1502e11550005160000520b9100c1441e080d03e10f032113444070074240c54680700e030340d00c02709138006101410b03d501407005402d51403d184800d500b00e2040c080d0144c0840103041c6005c40c1d100c10f0b44410741d48034009070300c080f84a601035404181503d004008503c5070300e064102055404035180700e51800320821074010102030828400107001442c8454001e459404410301c03a5110007010b805007401000281d03011950b56564100c0292186a00e2a0300251110903d121700c400b00d03c0020004d0513510000d010008040c0303400b5000c60710394085031040b24800f92010301411400401e102843c496001156060f03a00d03078450000400301da05038403a051410301e001c50060358030a4000140c0342c1c00518005104400800443c00c04c1c01d00d500b80d40003128640c24002044104030140c0c1503a001c56203192a208010303000f050040d00c0d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 976709955 1250 976708705 976708709
    0x121e050105030706051911070f0e0609100b090402070b09010c020607020102040303050901030f0e070f140904051009050a0b10090606050903060a110918100f0303020316060b060703080f10 82
    0xa2040c00300f40340408034038804540d019654140080c41040e41300c4030a04004141e44411501c4c0c9c5115001c01101d9003410318158000300403608180185411058214203051500401200603004140038040340c69541c11100703cad64100b41280d80900c3c2201da803902801020360044010300920000c02e8000780140207a4064035410345030135090004d80c6004400600c401107050040c56268240700070500800d010707600c040c0c840d04140010040c148080300b4003d500f011001400b40c2145001c00000c100049081c0000900300c030303c04a40324405003026803600c4c600e404060074012249007442141c402c482d6060b03084505092083c40100c0c0d942100380c956000f0450704941580000c4001072450100ba070085a1132160031110f175003000c143c2c50110b030400c0d4107011400302d2818000d003800b2500c0a00c80c4008010106c180510240c2c0f0f045a5000f074503030280c100c14400d5050344403021000c02c005030708405070410f0043c11040d21030141d4100104103036400e80d40550301d10b0303100c8085405000c5100ca0442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 976711205 1250 976709955 976709957
    0x3070503060f0a05481309150b0d140c1216121a0a0801020717090f0d050c091501230c030f0403060b040921121e050105030706 56
    0x80c1a40e0b90f854080c06002c0003004030201290032089080e40d407101e00c1c05411100400748203283c003a42c54210b1072203890a004c24040c0700300e03400d100780c491002081c00c4000c01c0e1400e089010980788107030003200d034445215070005030041202003508601c10745139a01041c80e500da86000f101031070326010008070003072081f01d501c8290711a82c100000e00c2845070480c4039514080710f103498415440805c0ea80012035a0703400c445d145a01030f003000f1401d1440c024071800090071800008501c0d0400300da03602c100515201c4803080c41c1840100c3d50413800e6650450814001c40090005400c3c2006854481e0f00d5040c1180d59a01c42d8442c0e4020a5410354028510001348006850360341c0c64500d440400c03001c01c02c4d0070090f810308601c200071006403000c0c1800a400d8001d0040007440d02e40e411840c1141c10b07034180c02c40041c043c1380b5000300305010451000100e101d5100084040031001d00100003182d00282c45e81da000040c2d41082000c203170b10030304005003400211001200b0001644c90300d04264441016205000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 976712455 1250 976711205 976711231
    0x30f04081c3b100e0118140d03030204050d0c1e1a070602090a0f15020102091509010c0501141501110303150316060c031707020a110d0f08090307050306 67
    0x1040ca0900b0094000310301c0480075841d401c4611450001c1e208140003104000010300c4035031082c100b560020000103840a090302c606001d542015024010050720f01d17029481481060308000a0600075811034002d07200c0600451100c4805080c0840c00d00d901e4490311031b03d0b04008030295040d50001420405a40f40591710300003003c1c150100c40c61903004100c094130071a50030400c0f50b030680d9921280f54000d011250103503418038034103140d01d4011f00400c01002e041d0390042121125603518400c83e10346810000d210a5268810480102c4d1800520a4002c009618180f01e1a80d46000d0719500340c410785906000100200400004450404940805c0070056200788049000410f114000440039140a411100720054410f02c1d121302c00d10340c1d13001c0008922401c16080505500c0300750761001074a207050b500038508220100a5980d0989403000d0080d000d0003031014a25610116840e111640103221980c400500b800e194920703911460301244a441524000500da04000c21414401c910f441c0d121 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 976713705 1250 976712455 976712507
    0x30307031413080106080a0317090622060c030605040b030f030906030405030f0a0c0213093906021b0d020607060e03190203030604060f0f17030f04081c 67
    0x854295008036200d0154a01889400f041403402442a8001801c0c60401820040f0480c04c0c0039000d800020482c0f04804032000030440b20070000507031940c200d100c2a045043c80658500b80d46103d03009100e00500480c1010282214180c1c503401c0380d0150b6004440410142c90002c00f01542d4141008007038103d0742081c000784003540761150266038428020070541c1c2c07806210403000c00c07444d404404031704080385020440c0410350505420f03041e150707d07403c2410444803441d5260743c80181c001502034100c1c1c4501040c05413403e800000302c454401da0840ca95482141c40701c030069290307401d11103a0b40f03d90f82c032000020828179000d102100210f4001d032100c1c0c5860b205440d44001b61240244002d031b18070080294890003005004440114030065015640301e0070060100020345109920818083c983c0d1582405501c0350000003004940e01d0104e170040c0e8226100708141540244076026480808c08140080d00781800308200c00e01c0403211084604a11071109d0aa03021225a0741100c081c40d2000c0d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 976714955 1250 976713705 976713737
    0xb0c0d080c0705060717010503030f0403020f040b0405010b0403050f0102030f0c131d0a0c020a0b160c0206160c06020f0705040504020f040e0c041a1e0111030708041403030703 77
    0x19400039401404079242c84901d80b1007628140c0e0581313401000503000b42c03003003c9007038048000d00d02600c003c4000d103152104000f01c44c0c10500441c003001e40b01d0795000c44101d14541c1c0f15440742040502c090020b00c41580d4a000c81e0206030803c8c4000c1d111f5008090003c0c1c0c0304041842180d12800901800f00f2290f15520301c4501d0b60303001150450102c0704030740000f05080d000390003940d64403400d1760001c10071450001c028cc4240c1c0c0307000180c0c006540c0f003402c00c0c0002802014400340e02440740c0400440c212090901180c1d180c00ca084042d401c014001000d0b40300c840f19000b02c22540c0e010342c2026810a40e5254102d07540c141300022080f182d0024202400305243c5a04120740250009008400006180000808961060303440344180d0f880043e04104a0809008040c524044c44070f000502c0084407012944e45000e11f100c420420380c13020200340c0c1503805050a464440e0003582200d07140c0c8001e1419110680c014041c0d840c40d444841507443c1c0503d0000102d8523055855940e0000e04002c180c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 976716205 1250 976714955 976714967
    0x1080c0910170717071502031e160b01030501240f030807300e010309030509060f0c0303040506071407240609020d0f050703060503120903030913090c0b0c0d 69
    0x1807040d140582c4000107215205104000803c480d130380082d104241c13a180007070401030009940e080664100748801c03250741601000c400d80e210004440396544240007569000da1419403840100f00344207000001c018414154401c21a424030755a840c40580b05410030503a900c0411300c10003144900e0a94284000f900502c0a8400180304842c038078801c01d02c68002c03120342c9440409501412440c00c41d81c0c915664030440c2d07014009030030709040120f0022510010880d22031131241c076000d0a0300140c408008900d000c01c50304044540c20540781c0f00d051a282494803601c0030349450001503a01740c0505044441101202e008a40c0100800d1010010058a00c031900100300111081070f03455000161404d81d600081c84c960414080c0020508014071469003260f601808074810185402030030b0246440c00107480080c140201421a100c00c4078000103855807080381e900c69000245031142104c100c2d959000501c000b071298400a101e20380710508001d0314000c55108003019489400001c03c01e500400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 976717455 1250 976716205 976716239
    0x2160b1e04110d020913031713061a1801030b0a05151216151d01170c040f0b0c0c011409190807032109060203041503022101080c0910 59
    0x191101d100003d80b80c0019040100c112091480c16000e034010204055001d10800c014000d21076560a8038100340031042c040c185000b0b001070516503a00e1080c1c00c040e502915031084641b0090100700154240389038500004001c2c40200c5e18444810041810090140149482007200341804040001c05200304922030071844113000c17442c001d00c151040b442d41c04900300300c05008120183c1c0c0c000e5591402c0140740614034404e48205510100a072195a80e000483c001c00707503001d042440c010740325850341f2107070762285600600c080c0d80ca0300c1c4002150b90a9402412940e41702c03102b59155465030300b0065505903400640028100400c00c01050f003450103698a401d250051a07003130f0100781d155140f15140404941041d034042400c0074030040c0300c013008a1003181284081c0b40880402c0e280c079101959030b01480c0190a1021800d55051690901c2a070680d0f410030754050301a034512002e00d0701c42078140f800380645034a0340a4810703400264204a040940652140911011090302d040441c800081e401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 976718705 1250 976717455 976717459
    0x7030b0609030709020c0c04180201031e0903020a0605012705100503010203130605010b0c0d05030604093c020d060b0103090b0106170a0504030215040606080102160b1e0411 76
    0x307001c0300146840410803030003c0d00020400603611801038485e145419403c0b01c03a039114500b03080e1440c00c220310b01e14010101036070a08011401c0c140001030803242980f111380511900e4500620001810350020b007aa40d8140502420803459885401d100a1007540d144034001202c4d040100b45a4030341986e0007541e20814462200ca4180d459400003801c0ea803060300d81443c4076821000394030522009225407030051002a008503e400043d0420a849410440c0690184640030000401d10f896607000201c0c829841422040032002c090030100031038400316402c60050505101d058030700480c1e00e0003c20413a0700206800c8840401d55900c2c00640b001c014998101501c1c0e066501c0040d505558443c003801140d1903078510494182c1c1e16a10400f0000c0072a11124240001c0c030000c03a07004280d00030710b8075141c284011595668104940035201c1544481c0d11076200050020000a0040800317142900c101d000031002d40b111004d116030000c0000304a200010f4520205001130840124502d1402d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 976719955 1250 976718705 976718707
    0xf1805030606100909060f050f090601020a0b10030803040b190203011a0904090f050a050d2a110303040b041e051012090b04080406080a0501060f1103040f0f0609140907030b06 77
    0x354110407040e1180c5078000001f24880399010704c118540341004000280050702c1c45107241c03404100013941e036001c1071000343c80306130b070000890310f1100707400100b03c051034202013581e590742414030b01174808540c00c54500201e14025220381e400c01c490b900840741220000c1809090f221500d44102c2c1d001d034043d40c47e1940c095a1501e40400003000c2c0b140c051100c6008102602440c6800d040c080d05118440925800308071449000078103019880500b51400c2d9240f4582030081d104a2400884103802202c0041e410310010400203000e44040c03005000761218040c04080c1505d114540002e40d402a0282e03a1b800205500d450f04500d10403040172134a85400c0e50301081c0c6003516207a40c0c02a61041d20280c1d1342c201c1c001414030502e0b8000420941210500004000c1985401e000500a1715418103c40408c09040e10030401d091040059801a15240c11048115540e451108000d5a100e114541c00720300c2070f0100144100710002c100780c1c8000060b081d9100365a40c1c15044004144c000201f0340e105074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 976721205 1250 976719955 976719959
    0xd050a030f060e09031306050325050c15010f1d04030f0c1703010303200a030f02030d140405061326160b0f0a0603020d1b150f18050306061009 63
    0xf02032011405412600041e40e5508440e020302088609a80c0040003030000800c02c5c000d5401c401803040d00c1d02d6400540301c0d40c00e90383c10181100c00b031080010104040c441e03491a683c000100c40c1c9400e04039008515100710280c1d54614540301c4042d540f06241003903484200040100b8000d542c1d902c1120114504045150741380d9a81c4040442035035907c1e0032505010006008040c0c11214000b0b00038404400d503030f04a409415000e0781c414000400a080224078054101117500130019150943c807403100c140007925400f0b0980580034401c4600769002d214045c04201001014014048415004805c039508120481c1c101a103680304840e010948003000c0014404070b580718000c51a010b8030a00364a1602e040109050750658070143c005a10f031440c0910400050755038005200b42140e01003030380400e95401d0420000c0c00000f503400f140b40840d0002c0c201401641c0081c0282c0d5522150315181c48030903000e60300e00e42011640c0112a010b522500c0410011301d17243c1c1c42042030220526004801c66 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 976722455 1250 976721205 976721219
    0x4090209040501020319020403050d030b0307091d010b040209010203030f1e0a020901030e0712060914120703120501061d0d051e190221010b0901061d01020d050a030f06 74
    0x11a08441c2640c0c143d60100c01e0242c02d00d9015070600000d40c030a00700354241819500d404c1e0b04c80c0c0b804a0035409065a400d80d243c500e450a00004008148a02003000119143c2c0c0004001c1281a0840441344d4070f003040031703c0d40740307454801c0d9440e9900680c000d50031035a90503902488080042d241d08a00e0315150105c0a0418070052100c1c45041c040c4000b513141c1144800143c2554980c19200c0c0e0310f0b8203c510248000341c01d80c2a03403000c00c0d40040000c41c3d8081c241c00c041c1c49510107280c1075000b902913004003180812a4000425605210342e071200141d044014140c81110420300900000503087c100107400e440715000308000c00c06005105109442d91a07841d0351800c012608814600a10000044500b8109014804d2410100050b51504100c0da50020f2a03d40105611818005d040360051440410950000100c0320000d0901142c650b11118058900d02e412a0642040c141c5d201c1004030f194800300d00888106181d03204c250801d4440b40f02035000d0301c49151402404c5a50f001e0004502e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 976723705 1250 976722455 976722469
    0xa050411071b0e0c0421150b060d020a020307122a020103020c01060e06010f02060f0f071707081b09091b07021503101508010b0d0f1d0601120818040902 67
    0xd203c0301c2401c0c40d907070f6186c0100340c00000700b0780420101c1441080c0800c0d001ca284401540e403030606160001942e0b41c01e80001a2103402100c4102c1c0d0414800300703554cd2203e40000c01042018050101c251030106901c0c0704032510a4072503100d880103003603900708141400e07400c0e2015001501c141405802d104006000300d08603903095004082c20b14090f0248131065810a04001c0501014405400140b0306864103a0040303101500d800c03141c4480c1d00004840b14423401c00c0c80812058180c00300354500f0442c0c00104021401e03181b413100960910700ca00007000d0000304403150040301401c0e098640d40c0ba41960614540303c4461456180d408010f8030380181d40b0b14103403005507c45081c4c0240c1300d09001c1c2610740c29036a9034100d42200e103001d4503594909508100024115020b40250a68884156890401615009883c81c000e50706200c201c0e11843c0c00e056081285082c0e440880d540c9aa90303403070083c0f800c484100c1c042c082840412002034034170400c00824400307075006440841c1c10981a0b000c6030314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 976724955 1250 976723705 976723711
    0xa030507080d1401030c05150910020312010308030a0c0c0f02010e13090b04050118031d0118120228030f020d050712031106040213050a0b04050702010204050a050411071b0e 76
    0x303542c85101c0140100b0a8000200020b8181543c231501e4400c0311119203e258415050058418040c0c00b248090340c40c401c000311010f205101d00790381820f5035a46851407268006035071480c40e0b54240094106d15501c2440040c8001d034008814807440442500190351207240c0c196103581140084034018071072203490041c1f1080300d200b03060011040c909800c04038219484905015090050310003441d021030340c041d400710010102e51581e5054204058010b03100c5c5011103006200940a002c000200d0302c1c81c00d101d00340d005000f611f58100c406002c4c0c605140d45800052080c03950709101030140085032180b0b506000c1ca030b1019010b500d40c0405615031301c2c039001e02c0350301640d0075800101c05003040582c00030201046216a0001b0312040c1890f50009600c00b000f50130004280d81e030b400014818030115004020030140180003044982068ad1000b8040d5019000d040c0c000c0c244100000707901e0400c1e1180300901640b1803091030170884180d4504405070041500903104480624003c611560f0700440180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 976726205 1250 976724955 976724981
    0x1d0a080a020301050604110f1602030a120e090c040b071a0115090b0c0a0b0903071b080d090f05010c0201021524040b180a0618050403030506060c0a030507080d 70
    0x128a954078410142981c000a004074000d5040c080b00d4102c032140f0205440b012040b031a803458843c1511030128910b0f11601c10081d606101ea00c00c00307418445014000c0e1003880701541c92a889405550a00000800030f0b9017001c9001001c0004104c4c103c1904058a2510320900315000349600c01e6020a0398204280c10003442c1e004207500d1842501c0e042810100101000c00b0100e0a020769601460380f1600b045202400d8071810380e0001d04902c10500c2110030455010981742c80e403c020101d2101590040e004600092058004140045000d88811021584084108468035003010b004480f00c031512a0102d06600c034440c4180100381440f10050310420b1111644100d145208010300710600c0284001402141f41080e84115a00c81e0044200b4410003480008a039888030b001c0c1c41e00900c410b41c40444605114810302202e05030b0364014500540c042e543c10b00042c1c40d040300b0040548030309520303c0c0c159409030102c140001c1c0903401400015016a103da81021701410300310080da036040403146 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 976727455 1250 976726205 976726213
    0xb19050114091602150a0e01021207111501031202031228050106020a0b090c0a06080907080f0604120e060d0b040606080c04030209060d1e060e0a121d0a08 68
    0x18000c2d00b03009850301c0e40160f40700900400185800070194440c42c2c0d00c0702d2030500010f000300044891403036400ca1489035800000840d9108018440c4010010040c1c0341c07000020042c401285c4103d0000441746002600b010645160b43d10391380c0c0d440e255a000c1e2126005600040c01503000183c44000100d20443c00c0440070015202821291003440c14401001c034086490040148009980010181101a406400005580c5a559400d49850700180071907a00044c25400820910b030710598140c010081e241c22070304c0880c5c6499801c0e071514242445d52160f03070f01590024000c1900f00c00c40d90170700c061a04050154080079800325160ba4810403070340e1640d603210700600245041500c5140c0c0185101c0c03500d80414100b802c8095418451448003901c20310b1007001281b115178601c0082c010305a0700501011220b050081c0019410741c44040c2a10098070300641311619041c041a00e0200c6036108064502840c042d070010303101c4119024042203500909101d0301119218603110801400341d0f24018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 976728705 1250 976727455 976727489
    0x2a120b09070c26090607060605060f09120304030809150903010c0e0127180b2713170a030e0708070f05011b03051c050406020a170709030b190501 64
    0x40c1d0400f01d14003400c0e01c010444030003c0c0010f40321a0b00751420500f04540c00703a1380e4205400c20302c001c0e2060350042503200e1b130300103444491a0600c0004004c1140c00780d03409803980c10001116174590003544000b420a003c108400d034121300d42448843d5444080034000360428034000c002c64210b4440741900c1010540000a03c4030542e044901e50f85022803903d804860059003d20040c1061078910802611a0101923a4420100c070398105a00680c000b400d203850407000c007509840c00600c40408210352031442004900d030100e1548450304540d8004030031003008141c01010085a0707000303400036003c05540742c00d00c138080841440100c0041880000030000390303003070000407580502c65034006c60600070f11951800c989140e1180d88003a80d601820080c1d20340d285205000720a090740801c5a40040c030b008100000c2000690250401c09116036510f400d081c502ca203031108208043d0707004804203043c846c04100060307403c107009a20207840450b02100034010a1a1020b4070420307044801d0452a101c0f00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 976729955 1250 976728705 976728713
    0x40b0a08060708180109022b17210408090f0a05090405010b0108161b03140d020a1403010b03060d061e02040e090c0a1806050a090f2a120b09070c 64
    0xc1508904c1040300803c07500c00668009440200380f486e0100e59003603a0714007410141c10b060320040607160842031181403000b24104060840d8422014503a00300800b00e003001c0c0307464550320407500c2103900c0721a640c42c10780803008001ca052000f22075141c3c80029450b002c0754a4540140d101d010300e200710300114403405544005002210003c0c259124913404000401c40941e0004640c0c458441071542e81c850020710741000c4407140c0c0c00d01d521000e0f1950000d070503044a40c450f8018581c91005030744030901d013160340b0301902e0b09101c280700d0800c02040501c00f20b1154903162a441102902c500000030b004032030003143c2c071020000400c1ea54034603a4045810825410f8448110380e0000c080d401038a020000300740040c104c0f0101c1d0040040101240d44490708401c41c60b802940508001810740a0301a99004804054610b90000c265103d0600d42460340b404604481c4503085030180558001010701c04108940c00b00c9003001141960b40c982d8401c100540366003190a006800c5a621140441d007103040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 976731205 1250 976729955 976729981
    0x3150d0620090a050d050307060504030c050601080c06191701060918090803040318120f23100b06041e0e011203051603020a150213091505040b0a08060708 68
    0x12540c00c5460041002090b150340c0c0041d0320060f40c00440d0752844410150030314500e94024528001d103500e1400042c0802c1c036400c00c507c0c10240344220115a9030307a0300c440c14952035810f900c0351107403c11407d1085129250424841d807140d80c402d464820010481e481d07503030311101030a1f809500481c1d1038107010302445280d562042307454224160300b0f00c0f410086a680107880d00c4000c00103402c100058030200b0603900b42c2c0c55580001c060b0030011200f820f9403801c080300342105400045611501040004221048004904400c08200da002d8200d03514803500190281c43e040788d19540c0b00d1020003000c60300200228540001d074008070110142030741041c070310041d500030680041c400d40c036008107a80c0000c1d50000c11103124035900038a0340505289480c1c168900198003600500c10b4401071115107082000740d0142003440e84240d400c01500b5a02d072146c2e0110b48001c2c01c030107a9240c070706905100c13030309203a04107125030000030f00018100c40c1d8410b810f504254081c2c07100300c0003a42d104248900780803840e0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 976732455 1250 976731205 976731251
    0x20c0d0201020418111306030b0915031e07050303040b070c0602030f071101140d0e0106060f02060109270602090415180f020c010e0a0c092003150d06 66
    0xc0000c600d05410a000e00c2002d014401481070b6640d110240080120b41d64001d0b2044031854035422a43c1e00d448040203009400c05031450b901900d1381c0030001d0f0b9a0384c0c0103503802410138030141c0078101042440c031360114816406550090548035000c000142c54078100001c01c020451807225a0312686135141100280707480d503214908560007848010340743c9512200315003140d0740c4664503409d400044001600c00c040541c40e52400040080307400400240940c000b800005100d80080051586a42003683e1005070074100c0001a40004014801190342d80e000005291002d140440c1544c104400c2c0c00c0045951700341101e6040d00401c18074543c0c10113000c6c40311401e9000480e40940741c20f1214952901d50340101c003040c550384036400e0340340c02c0c401c9504582c00300380100000d00500d040c8103281c66031098070050444410300030002c0001d00944070703c184045092100c01c1e0a894503812041c0d440d9a40014204450b80d43e2451001c546582e2400c5540300354034804d40000c104140c1c0c07070f180c52240705074030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 976733705 1250 976732455 976732457
    0x13060f031112010b01050301090b0f131b08091005040609140703062d050714210c0309030301031b051003050708060a08030a1202040905090a050d03140606030403030e0709020c0d 78
    0xa00c183c4d003d81c0c000c016a0b040d5102030340d000410007032200004038102c8172002c1d50707500100310724010102c05026030094624010030020088520000420447d0382100480f4803486135008083e500c0d150507140e03005035421600981011400c95600e846510300f84040031203941c0c0c1c2d40d00191042081081d180501c4a8042d00c410300c50815140c0100d03000004013120035241c8880f80e1300c01c0040c03192030003000c0702c001035107080b401e4035191107900f07044600b001074140c0c00c010381d003920000140c4076109c4241240c1c424000d8401950441e4690b81d1040107800050103644070310304035800049004d1b1200007165112054550340800d090a08910291484001400b12809400701c0c13a428465076000200300d5401501500d840d41000c0e40700c4030090001d004a421000e000b50906042c80701203180007850401c50707802407050702c403000700c1082c0640c00c654203c58181030303007024000050a01e1a000b00610f6126001c0d0a01280c6c5580c03651141e800d041e020317001304042d0b0381d01103503042c001c10080000010615203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 976734955 1250 976733705 976733711
    0x4021002010c08181603110114030402060702150409110d06080d08070f0302041e0305070e09060a09020f04050907080d0c080d050403020a0b010305032d0913060f03111201 75
    0x382d00d00043c01c2c00c2e0028040305101041c1c4a1091081030100103500078003018a411080381c5403030786414181407030001c0b902400600c84002031010b9804903003c82c0c3c001c0c4c2e4010100d515060360f0790f00703200d071b4801d012505d40d41d8540c0c188000200e010302401071840300c40c04079180d20b54030342c1d0390841c100460380950070070080780c3e010340742d03600400c1e4001d84003035008411414603682030303400384100304c1c040c0c41144c0041020031f20380440c8880c0214101c1010050ba4825400c2e124015201c01c84400b660508540c460150381c003640106010200720b0344200285030000e085d00344074076080b074041001d4603000ea801a03003d5006010401a812080c0010003c1403c0ca2408004940c11070719090180d01070625000c1c01259503601080c1051300070040d00500c1c0d64020640e51466940b41490703a03c94000f0b01940380c0d103aa003000e45424004078080c091020540c4503802c2c3d410706841509001031b24074001d91140c0426624080401c0c0e01004154000c0214803418040070100201010320089400d0503800840580c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 976736205 1250 976734955 976734971
    0xf271f1e0e0d03020705030a080a1d100615050d02070302010b0622050306060a05011107050d03080f0a0213030f230a02030f030a0206041202120d020409230c070204230402100201 78
    0x1b60220486840309200d02c0c10403000d8071a0149500145040048070604c03003004c98280c6d40005010030426030303480400404009081d6501500c610074405034810308000f0701d0800046110700080c2d400360418500902c00000e1100e43c030701c00b1075010360003280c110310404408034a02a0004201c0301c0380c006008181c002c0d0145040c0f0501040300d22451b03006a906110180780c0e02c0d81c0440d020481c1308000d080c020082111071040e814041c00e82401a10081400c0c9200070029110960a0003115400409249031190b411301c0c54603103003901c3d169054100c55054494a03001040c00d04c3c59154541412150054405180e19204062521051a1111101ea0014407008425540108150340c2c05500240b001072102e810a42c2241850000449841f48940100c0d140700c0e03007a007641c0503005542c07a89500304804503054980c880d03c00419040c0a840d01c2880002a107186800700c06440200d20103030011604038040400403409065500c044204842d03a4400c10081d46803654000c0b03800e403040e0008006200c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 976737455 1250 976736205 976736213
    0x7020a03081611100c0f020705010503310b061003060b0405220e0c0901060804050616020703020901090212010f03030c030c0305070501050f271f1e0e0d030207 70
    0x900400e000c51500d10074620b10075150084600c00f45420100e4103554890b8a02c10760705008200c0b441180000500203084000300ea4000220102a01c03c140c4603182190b81c0c8800b000485001a440d4034551140041200825000b05100d500805d20400321380001c5d2414a09001c12444080400010541401410041c0a40d03540849040d140c0640c3d1400c1c070050403010f208214a0b180a5020b811454000520f03443c46012a441c008070804503582036036030340ea1314030444084401350b9002e0000d40001011410b041c840700d049040c034910702d0042d6003d0320f56030780004624140c00d80c00540000c0c0c0001e041090f000701072000d40c0c054080d0059542109056440041003080113030700c0201489450b009290074503024505482c80e550707106000b03004601c3c2c0000712030302c800070a071100c00e02d0605141181c029864401202c00800d40b48000404501610608031402040c0603581f070702c211944c40301c4989001106200d06118415020404150904180c8006141101a0300000b0800d441400550005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 976738705 1250 976737455 976737467
    0x9010501061b081603140c01050405060601111b01110a080405030607090810090f20010e030f0c13061d071d091f0e2809020d200613050907020a03 64
    0x49071098841c04461629217004d650207105144c4840c041040481d02999058054011500c03452140f01520f11b03a4881c0401512006d01080700c91070a6000010f508100c0402d001461303c1d181341c14548100c020040344509824105581001d641844000034180b1007800e0820441c0c0e001401454030304900d600d080b44294848030f40c5a03290192680701c00500c401d0000115540781e180740c110490307206650340c09014803822880c81c052240030844440c0d00344502e18012921280707004640f00600480030282c010815040000640d848140381d0b5244046401c001d0500440d841900c02407103100b490070551005070010075400c4070301200203118035026425894100e0300c96000a00010011040c0c00308422071440c1c00f4003608050030400300a07041140c140707248102861100006540c04015181c24080441924504580030b500500780b800c00301c0011710915065164a51341035003106102c0509000600d1030342c801a03045c9031030b0200e00b070144035a18001b00785a4000d1214002403680c40042d0360b000d0b080d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 976739955 1250 976738705 976738717
    0x20601080606180a0b04020f0901031505130e0a0506040606241d010c050f100b06070c050d080c070f060305151e0303040f0b0c010b0a0e0a09030e0909010501061b08 72
    0x4442018000c01d01c01186500401305c4010300600564a5880101200c4a1071f00007800441c0081c0c101340c1c0140c07101c1d030040041c1f01a40c0000e40a500810346070800440a00040313203181c48c0b5849160051004240c1c18481940a213103d2140071609070718188400520150000101c03001c149207a001c80c032102e40048680b20a9801d10300c140701056034040040e58622012034000d0240e02480c992a84588008580103003266480c0c141000300d03100782010300032140155400101071045148060245141c2030405081003481201c015140181381070f05581401da140c0c0c0a45203140a0300c0c01400010b406004856100140d00403102c10450246c0004690300912950311401401d5400004560344050044801500802240c00d0711140c3e113906086540d8040310002c0c02c07a51802e10700c1002d51408200c003104070303681070a4008081d12480040700c010050310704d0840c04d2280313008070172900c0c2d00ca00c00034510501100c4000621036242c404c0151060fa4406081001840103c5d50b010004040c5810b0f02d02c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 976741205 1250 976739955 976739989
    0x1005011106040b0408071202060601091a0f0706063b151003020d020a02030319020c1216060c080901060e010503100f15080a061505010504050d02180a02040303020601080606 76
    0x40c284c3c03128240103141c0c0c40307014000b0303090001200076003800a40006190740900d43c04e0340ca6818041d540c90345d0f09402381e4048418218204e081004202802402c800b40041901429002a001e580c03560030707682c010179450b5401c00001082c0350124200c220340700c0071002001054074000c1545407001c1d00c1012076960b920054414494040c40d800340034803980c184c400010004c14110750382d01521401a50340d80041b117010b005030780c600309202d400721054029030302d031074014000900a401d9846160040f6410491590142c00c040d100014089207107801421074010003a1166520341c10000300803400d45d8910780001e4071405402c00100034a031000510040755120104000502d600a90140d8000d841c40c003401d042600c003c550045240b40001c1903c450482c803920080000c03140b0000f40424005941c440e01d07000ca031042c4420000b41c00c284207010542803004104c1c0302c4110b04051001310907081650307840c070810b0b40071a0030320401d9010030515001d04a40c100030406882c04c1c00014091180f003a203641 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 976742455 1250 976741205 976741223
    0xa051b0a27020a02150a150e07120204090209131e0b030f330106051803030706050c04170a15021b24071b0b090c0414100501110604 58
    0x140c2080180750000302014070003402035598080c8444020740d85c40c96440c144c10005044400704002015030311415240b04844840620f0182c81c03c000d00000010080c40c94050140c110399a4504106610041c40600320128005854044103000d1110365030140d4000c95684d4038241c00d01c0c4180e40b410410002140c031400011840049040c0030a0400c000310b04454100d104080f46c2c8003d01fa070012100c800e4100821003120091040c040c9640d80400a226520210740d00304007c00c803c460107442100c10000240803a8604803603a03586600b283d8088840c65090f10b40460305102c4420003400000035008040001c1902826a4489904840f03988040300301480c0c1c00030300309c0007000c0900f036400400394034003090740c003502c21402280c020110341c1206240c0071802d81000030503060051408130102e0500c000c0245060310700741d40700c509042c00603050b09510710442000254640c0d6900541c001c00310340300c2d28030042d800d00c0d00203600d1301780c4c4d260452814407510720718510f0500300004001c0d0340b04c0e401100c40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 976743705 1250 976742455 976742489
    0x901020c061602041806180309292206020102040b04090504050703080403080a020106052e0203040b0406090918031209020604180b0312030123040204050301020a020a051b0a 76
    0x525402030055000750482c1c24001201d07060781d40130345e6420809000d000c061141c190b00c41c0216103000c10342c1c840100400c1e0403402c14088803100c42000f0400320b090362010007201d10403440051007500021070702440d07486000503c00780e08129628100003841d40d0700095050900b80f81d40240207000310300403011070940e510b0000b801c1c86801c010c900300440d048812180c3d9a80c403810002c00541c000140c02d000b541c2031460004003030a00364071100307240014890611a842d00c05a4a8030201d10300e001100443c4814440420704074200001070008269030b03102c2190303880c54103a42c40306035540c084080010364842030142c40441e030403807a040105c105d120310000c0c01240d6880050b40701d0246030007801d181c001401c650710030310b65950700102d8080402c0381200c00c50b05400c4a201c440b44000d0180d142d148146e00029001c2c0c2407050700c09034044030001c0c00036041c05d45820109007260403d851110043c0d020700203010900a0a028400b01038442400c0c5036030720784c001c00124104409510418008044002324 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 976744955 1250 976743705 976743727
    0x706051006021c1b0c12110f09190f0c0e01030f060602060c0a02160303120f1e0b12030a1e0801030c0b070614010312030e0f060a1805010f0218060901020c06 69
    0x310741012a4017001c0c0f0038001d074803286a54481110108100c40314081c4280704800c0e4540947d00e6200c49900600740c62075070b43c1300300c617120180c0103500596201a48031098620665054002d1034507140c0b0b0b59844403810420100010141c4110f21802c000146c0752041c10b010303156001c107030a944002e00700c00d21130390b070212684203d01d01040b0700c401d07000d44094a6008400c0640c454100501900a03d60038446001801c2010085448500994041c071400d440040c00411068104d4884a00000d0203514a0140008090306683c440245000003905501c50f09010455010030740207580c0395450b00d1103580d03040d03945101440c10940251001e00c28045103400811040c0c1c0c110f0040298070041c06507003541d4034500a091040700010090200342000c074040954980001e80c41c81c03006901000b0146622404104002842031111841144140d402d014000c41d80074000c407a021880342000594810724081907903440107070004131510a2408002c1d102d0182ea00042c1586800c0c804c031401640c40d100b00c44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 976746205 1250 976744955 976744997
    0xc0509210709060f050111240c0c060f07030e0d1704150906060f0510080609090c0d03090614040b031b160b1603020702030607050f0f0706051006021c 66
    0x10050000314280b690101e040044000d200e81101c5d000e0700c800901c8040e0300c00755600c0704200e100741d08910111000481000c0d2510790225040803461085520b40001d4850460802c1030448942c0001d1510341c3c1840142913140c0300703560700104007801070020341c41c4540f4018140a5491500d16611540e00c01003010320002c80041c4010340c1180c0700030418042c891170700001600e12403040390740071022081c2c0040d8a05112a5041034081c456540b18059550201084802d80000e0403009407481030807010f24041d11113241c104241c6020ba03c2d400041c03440d0800041220615840340e6140701c0b801e1104000410080303083ea074000c40011444a24804100d0040320a40500849101000913403034452042c01031003103070305005541e400040c0c90f002c031013145d060701607106029000790954000c03030005034010311520180810120a040541c40c0410300707200c86690740c00000d02a030340b03d80d842040c001100c9100c00720300010a19400a05541c000448515060600100d528403c1c400c0011703400814803a420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 976747455 1250 976746205 976746209
    0xb040203031314130c0203040b0f0c0d1205010f0510123206030604020d03050a090b130e1b2d0d050906150d020d02010c0b010303030e010c05092107 65
    0x580c58801c07041d40c0c1c440c051100403e1004050088400014003480c1300f000f4040c0c8801030301a40c00961400b464080d594440b41c1c0005502e070880715082c0f2140010031403e02090f000c00829035038105810285c0c00c003407421544182e10940241c00c1e030180c1044151614080d81c01c00c010340c0d0401d150041d0341c0a016001801c83c7d0000010700b44503200c50b035030744680e080d020306488800001115401d07642d11070615540304000d6074040c0d03005007084074010019220740024001d110f080d140c104040c80e65400004101c1d0005048100700043c8a2803c2c00350303000d0f8645079640240e101c0b00d200140b500c24001c80341548298200c3c2e03110b1149185000041044100100c40081e0700c100f40c45a03900060b00c1c051009080654000d00c00740a65030201d079101e101c0e40d62418042c44010100040d41d800769080001e40c441d4100202e040c00030722403000c40030400c0b0001043c0210300940740450850080d143c03407802c49004004410a02c2014408606692202910000c00072400080440c840220300d40680c0b900c031880e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 976748705 1250 976747455 976747477
    0x915050a14090703021c1103070f11121b030c01020d0f051005040f0608060411121203150109120303140c07050703170c0a200105032509080a0803040b010f0806040b04020303 76
    0x80300d5100e102030100d80023544100b440e0740e035054402c001041d044580326254900400186d0040710006509600030000f41000540c0f540300a000e0300d4260100d40c150741012079582a03595010a501540c2c0f800c90050441180e8055030070072552600c1c0511515807d854010140200d5460002d2010002164811000703000010102c443c0d61401c1e203015049040bc3c0b4044500485d003084042c40d10480004d40306149084600456045035100c648503458405204109810031001310400241014030340c04074007250340030b5507004c90807880911018054400183c900e80c8015410402c8802191011802800345c03603101010540c20701605d00e13031507034900031146460b03075171301840b441101008007081c1100a2800b07c100242c21000102c0c005460300c0c0805c80f40d454841c01400c00e010042d407015040500740c7c55a50805004060303c0c3c1c10b40c5881e041c4643c5048426100c000306100a1114142409004181406020b2005802e0800d903544652024000500d4001604041411580c05201703903044007060b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 976749955 1250 976748705 976748711
    0x2030a0f050409061211062701140c0d020f0c0f2403130b060306100302040b0d08041e090603051213051806012606010c08040915050a14090703021c 65
    0x255901c0d1004505c54490803035002039079295007111350420f04140c401d007198155150481201c1c0c144a64081700000e54064100045e28040504140011020300301c060700f031100900c800c0b190584042d00e01601655940c80c03c1d0310210314810503a545204008400d601640c6080c0214008a404408001078070070141c4500d0002c400c00a00c2031103602ca40c06014081c0001c8140d58840000b499290581a2580c141d0a500c00900740f002d0300b06904194512170000d4440400c0e03808503250000c03a6002034100281c6408451001e007420a602c0c000d10018010020b810400a0701d155101c1d40d0701c001143c00030f81d405074041003503507143c0182e401640040202428807140c2e41500c1402c0b600707508041f0fa0840c0427a156003000200d404404810030000b40c00a00320b0280350301e50100545181c1102c0604176181282040040b03a038543c24003803034403140c08501608503e20b0800d0208454185660002034410074892010711a941d1407802c40e80c0c03c400a402d0060380d440c0c1c00380c1d01c202e05c400a4541d520200d41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 976751205 1250 976749955 976749959
    0x40b0112110409050d1409090a0c1b0b0703060e01081e0a060e01140109020c0c1516060e0c010206040809060304020f0d240e0703060f140405060601020d0e0102030a0f05040906 77
    0x80780a0040302d009542d0729a601c1840782e030706d907054020484441c3d0814000c50008031003d406900c40040e181c400c1c142854082c4000c0c12801c919007000c0c2c421508496818140481a40c146c01080090322a2103141285581030451031551031100d040c2d0924190098100c1441c401d200b44103400d41070350449024049603218042c85406044d4180100c90485100380000508100e1031003034501c4501a80090030750310030600c0c00c01c030300da940540880110030800c201c0c440c00316200c0040004840e11641001c0f400a1020000742d051002c2c0440032070654000c0810000003548040440700b08000c200d610b680c81c0d48807800840c890508407110b00703401420180741c01c005d0214004290100803c42d9031442d031030a035561001c01c203540c40109031300c80c0b0341d0201205000040098102103a06260410001392200e04184821504401a03d090341d16070827060900c001540d042c00741141c00700050500103000c3c032036800001d5407032069026078010845100d030381e28071107407080d82101d004201c01002485803a07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 976752455 1250 976751205 976751213
    0x6060d11071b0b0a120b041d1b0d0203030421020409050f06060f010903081e07080c0d0503010e0c0c1e030a120903090317071208150108040b0112110409 67
    0x10842c580300001000c4411000030b041e0400004403803145001e0798600440000380100000905404000d0ba17a002d915000a040412075920101d0072400c0280020603500c0e010321440c20b0464449104280a000f86550940158174008100c034221180b1480d90721441e40d00a40c035042c20454504000d51060410006106101e40058400381000109050342e180361a44020441c4480d82c2020413804586c0c071050810104421501030f00003500060799210034002520000340440d03100090403241404041480c1d400224100049012800d40d070420b02d03d036504064000745039000045c8a01c505140018484126034014440c20340d503011100111000c9048100d65651039400440100b4001203655180c41200b4100740222a0450b1301521074003441400d50710380001da40780b0300030201e84d10b150400801001941041307103021021103581e2103003a070b41808062000301344c0310081100c2c100486c0d1014000801c218404207811212200000441b035041d81c600360382103007540e500345035200d07151107101c9042c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 976753705 1250 976752455 976752473
    0x901032d060c08070f021b0a080109030c150911090a0216051e0714010c051203010608040605061e0609030f011e0507020f0303221b05090702030a0806060d1107 70
    0x3a425034643d0300c0c199540700c1c01120a021921022030040e40842d1001d0607080c00ca40d0840322145010349134500e810b0b19800c5c041d094400c0c40e901180040e416041140600c030030b00030f08685d00140c1c0d001c1071154020039200c0070b000800003520944509000404100c9040b03517a4103d4a40c048402014030020440c2c0c1001901ca4030050744c914545044107094080546000c03c00105480f900b140980c0440ea6a1004550440c0300040072102c500c10302c0b035412440e602220145008094951b2040c1c030714903082c03504009555015022a005144541031426001c00c4946040000402503d4160301c8890341d03c0000c2c0340176407401001c100c5500c0c001d075200214445208207028440629030138881c1d500c03410402c90b9145409640f240849d00240b020944d03440070302541c0c8415107803a04600807449004e40729680c6001001e00391050300240d806040240d418075001c0300703170310000d240046c0d030914541041c0a403080800404c69803082500003520b0740048103581c08884000490450284c5400c580e1401a280b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 976754955 1250 976753705 976753721
    0xd24031101020a020a15050c0619060f0302010203030a0b01031508011b050a0f18030b012c06360c031906210302070509070203070b0a0b0901032d06 65
    0x442003400d00603212a500010741c500c0e0080d070190202e1400e6152440c40d80c2c2c8148075500c00c03820800c0800c200950400708001e5580100350b08c100d00c04c0d41d43c500070102412182c1d16400500c0c00070301c5400400140c0e80220580b0390103400a1004501c0140030300040f40141800c0392404540340000b10040703003200c01503002c4407800d020300c19540011109128141c032140143c4840000044002c0079030007440e4840c2080e002c0c1c0419400c1d4900d041307516a6111925007500740c200042c60890086600c0c1035200b0603805030384d02e02d0b20508042981c10035202103900c001d42d119107903911001e152200741d0401d00c6095038030f6031895402000d048900f04540f460800e64015200303d10000d03201c4c800001c0d120303000d00c6080211403413191000424080510041c2c2440816042075007540a41e0000240b5030319024200e510658003940035590340d46182c40d010b81a1013018109e008014600030035182c0c1794480c040c4180c15207810500d02001a005c880000000d001c0d400200d07000c0d100380010a00c10440540c11200d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 976756205 1250 976754955 976754963
    0x3150213080706270f0501050705100c030e06060a0f09020a0c08120124050706090320100606080c0306210322080f061f03020a0308030f0f07140d2403 66
    0x2001350984842450709504d0040c006120004201001a036010f08020300c19140300b94180c0e08010031000c40c402c00c445a40349014082600c9828140709403c0034002107034001021920000e00608104608080e6105409590502da80c002009510340340205001c1241c40e0740900402d40d2240002184500158284680c0d0b102d906850411114800d80d4000c070b4980c000e5603034907641004243c0d190a0050701d5122000d4003804145010322202ca403c56250501d07446140300245882d80702100c1c48804c464966108600b003140103402d208414815008413600a501254214011001c0c00c5080454403401d40c4880c080d84800150005c0d81c822a02c8100505c0d41c2044400c8101c5940d8031100c2d44414041110010942011000441a10100c0d61950b2140301c655883c5a80e952241d0119a08810542040d9504500401004a41d4444d88061680020700c05440c180500301107801900102c2036400d41c0755680d00c0818000c00580e5190310240c0030348e0032904220800361181705512003050940c0000c3e5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 976757455 1250 976756205 976756247
    0x303031a0405102903070807051612080a1505060c07080303010f0602010b120a0f0c051806040b0d0302100e0111030a020d1401141c050d17010f03150213080706 70
    0x207249400e002213841c4440040c02e414610b0b0348074071003210360050042001061207400e000b02c81c1e0802a50840114041c403610140b0034000d880b02c3d000d4249440105241c86407410510a0515000e00f0841e036000c5880a644c06525100303403811050a10400d6003042035079200104c000078040c940056044c0c12107085800030400364020f28144801ca040041100340e00b0b90008510380c1c00102c4070881c400d4040e00403d80d40d442c0b551108002034a800302d00c5c510461005140042c01507503c1d051240c0141064202d500030070220560b40c020f900c030900716480c11601d0707951340020340708a2420b40120804660b4450050b075245880400200250400c42003001c0c1c0501d0304000c0d44000050101081c142ea20030382a89104200c4402001360b1140d50405a0b801444a6080c0300c0000364200b00d240d41030711342500d0340c0c40b00b800e201c03140e140004016070050302c0e41540b0550800208048400f40d00d43c0d0310704007001590f140480c80b004d00c060016944002640c0c81035400004e100ca40c800c0c010101948040050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 976758705 1250 976757455 976757489
    0x71103190b0606270111010c050d0b09091225121107060509040c050c10020304202b0b01081018110909101419090c0303031a040510 58
    0x3c00102d000d5454200403000407030180e088883c038903e040345120780c8149802d5450303850900c006800e540079030200c00c000c10400716440052114a0083c0003407250265618074441c035001c0d0340c0540d5560000c2400042100c0041d240354854140f40d184041660a40481d02400e0f0a501d051000040003906003400200c2074010441c8a500115a5070200d0b0019a80d4071308003442802048001c01300301d2007140610400f00a0807807255428040c800410008440050300d81c5450304081022030010003040b2030340001c4204030181980d884400f04071036201e400d0f113016280c050503010010a420340c0c030094601400d90f0300014491078009242c82c000398807000280300180f40034000c078603201d102120003001e900c001c004271308a03410080b046942c0544d81c80c0407107078408280c1800d00119105c404040c90205a68820400c1100c0e50001002180c204002e0030062043c098032031251820351800001c04041c0c03150348403030b51054204030006c0c504030014810821800c0140c01160040b07aa0703c02c4002140d980e01d21 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 976759955 1250 976758705 976758709
    0x30812130f08030c0d050907031406070c0308060a0e04060504021003060515031b0f040503070e060108060405060a180203010906060503091c0c080409141f0b071103190b06 75
    0x81548040e8071061948482059a903200803e400041200302030030414010005070740418043e0500444041011f8000c003419410002d6404031413542d41000c0740e10180c00e000310164401d428541c050b0f05842c0091040c0c0350800094502030940d8001c042d1001242c041c001400780c0d50303001c180224401c884041c8215a80c0f101502902c101d0b1207140e52050070b104860303180241c20001954041842c0d9001ea2a403180c02103604c0040e008101e4600383c446000c02c00b4011814200b0100001c1c2c04454001503251605000003003140301c000341480e010750303162004544540c940d560004041d00c100d99407110780d55200701065000350424424400194107000d40024200c0c001c800f1a4080c1c2440030240c0f4982441c0d1801c0940e02651100403810001d41c201d010300815824405000901425080494644a03556400c003e03032402a119580082a01c5203980881000c5c078481d40440d0707501d050042d2200c0b020704102f0020b0b4450b040040d0180142481280c0842c4820135074100c135441140190720036110101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 976761205 1250 976759955 976759981
    0x204050a1401170a140c030f030406020d031401030f0204111803012003060d1110050d0b09010b1c11070501090b090c01020a1e320a11010f18030812 65
    0x80b0406413500283d044401003007030000d40c0c202050f162021034000300400d0020a18007205060601f85e035401c0414184400780d414000f0348240742007450148154000c1882c100c1c2078000600c0014081e81004110000b1074030f840d040002009030700d0304156100e201300302060305402d807500750f280c0c030035440c2294070011550a01c201901e80c0c408e040c086411591a82d09025591208101c02d40341d100c07038945078500d00d030780d200700800500210f50b544076160000070341e0002c1500c0204035581d21450803000140244c80924007543c0b030700340d1814509610041401c0416008114034440c18142400024407902070000542140398124851807045a140e0340c0c03800b40e207450301d0024007000d0050f0442042400850701c41201201c02007840c00400300b210754641c4e188640321200d1b00c050b101d5440c4c580e90554010a400c52101402144d42024005511183c0c1e114100f00309840d0340d45040c42901100303c0032261144002c01e2548010b4500c0c2c1900544031b090030301181d040000c4200c07404000b4000240c0110f4062 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 976762455 1250 976761205 976761239
    0x30907080f0a021c06050c0904060603051e0a0e010501121223030709050d0f050127080c011d01150f030b0402040e3405010807120908070204050a1401 66
    0x80050001503242d039003003003025956100324201e803810070100750b4040f81e80d500c21310340689500310a481d03a5024510a02c81518002d03440729050514090401c0960540c42030130307460380c00e08001c0b1540c0958500f4040d80c01030660301629105036180200110782c18510041e4400128020011101d4810106000f103809007440445005000b204100c01200e518241d400342d0380011139030a1550074607490b1070105003100140c06d020340790f0318180d000c0201842400c5c410002111510788424403840912401041d40b651903000c010140c010008a007114002d00f0740c440314840c0b455860615006810f1030410340030b001c01c60004507848042840000e007500700f000d0140c3c1101d40c000a8261940c5d2540c00300030090440c0b00e4610720380c4c0540d81848251100c2c406140c80780056055203014505000c82c40060f0686071a04541d0610440c0d40a2118564000140350100340c001032010034242041d10340090f090190002c002d4100e82404107205035500c03140c104089201403007080311440d030f0340e84009801d0000d2035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 976763705 1250 976762455 976762483
    0x1b05190503131e0603020c07090c03051005121e19050607030b0306011406070c0504020f0c461a0f09160b0703091208040e0c091e01020f011103090708 66
    0xf00c0c2040248034041d401400d0300c0c045240c20b5800e245d6a400c51601a28085052200007035610000c11840240c010381130700140606a4040f500fa14400014696130703004c0c0e000e406010328942549007840c50040004980849c0c221013030140b9400140b400b60f58480c010b072800c0000c44d040450300f40b00e80c00e00040c43d03030480702880440c1c20003070740c0b2400f8814640d105281c00d9036488403200002c241e03130f1200e000804000c80c00c5c1c54025034030a8442c5645041a104081403064148148041c0040d09101c20340300e800c581d1490550226210b041c0c0001d025281c040c00d0050a07410341d142c1c40100940286001c9208648140c25480c15a5407030340303880c0d128917580f00306111004001d00c080c00124034502c090005584681030010181e511141001000112003100b111500c0d0001401c1c010301c50800340084d08030015039052400d02c6138000003d0000312401040c0401d09041117000511680308100483d0600c41d594000c12518140381440c80d442c1c0d2044034080c203d44181e40b800140c20400080e141c14180d58 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 976764955 1250 976763705 976763759
    0x60c12020609211e09270a0c050d15050114030f041203230103051e150c0d020a08010e13080f09010908030f1e03071b0519050313 57
    0x8140c09480c803a190782800b01190300c0280b2050030500b03013002c40c0300d44035044954903035202d901c410204100c80325000c1c4a5800c2141d400c0280030b2800d400b51440350040c400241c08500d854000324101e900d40102ca41c0c41070011704101e8151581982c00310108150303142030743c4440401110301484081d6100c29100040c504042000080216034003d13070809e80c8500528011841c15440341d000e82c02d00003c0300076450a43c1c0c02200400c1000781c10800528900170615002480b50200312a4985808884a03010001542e8500051400141004440d4861070803d000c40d19290040c000425480d0309004210340d620903840810601c10302d103c00f0301f0079954400c3c28103281800b030710228400354100e13002c0b0310705000b03c017100441d205005001505180301d891541e0340d00d0b101078403400c01b0040400b28068036046400c1060020080e0301c04444c01181e0201d00210100341c0042c90940e191203e01c40b001d440c000e03010507001040100100003007050300f0038664100f0714551a513007904074070781c07001840c0d480d0014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 976766205 1250 976764955 976764973
    0xf180c0d0303110f033c04060f050a02070201020609010506280801050c030718140913020307081b030705030606091906090621020f04020f13060c12020609 68
    0x5000342046112500c245004a15660580c4140c182034001e42c4c6140d1000b10301104000f095000e6208032440302034000c4a5041c45074101600c02400ca076550b80485000154000150030310080d50072410b45803040d60030400003031901000c0000290000d40f012401401a41c020403043d404c14081ca40c0600c800800340d400744080040010617031030742c2421074840c0c000211400a206003082c403c4512411080030400e540e441d00e0b11700200840d0418461341c40f0f030704a41c0020301c0262002199142c54003425143c028580d2204044403940f401d0b0128000e500d842006804a0194004207001820180504a0404240e00003041640703d0005008007900740d40600002070840c03905090960300032061252595588150354070400c255000754011200f4142c90340780801c43c410b5000c140c5121940c044074160344500d0309a00041501c0c0c10080074a01c03c0e0707004900b001d8036004040032900750038004079503004181e40e03946000e044040c1070b103000d0711400e84403110564218008503881c0d100d00004400307402051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 976767455 1250 976766205 976766209
    0x7050c0c01080708181e0721080301150e030d02010e010b0a1202040525090509060d1218170d11160312032405030715020319050708070b0f180c 63
    0x485a1100c05005d417040c42801107140d80c1054411004085110181000500300040100c000d69580d41c280c49003406000804007241e44901500d0644141003091210185005000c480305910a501c1d030340c6c140509800c02594540545c008689c0c0e4201e000248010010042040758101492081007440d04480c1c081d40c00514265005650195080d1030042280403500c503501c1c0524400241c1c5008560070345410b0000d803400710034085d40040121001c3d2010380b0345903680345146010000303407418400d0240310000301504001000020f415041c80d085d20340c0300d401000b19039034520240c99101140b520881c01c0d01d107010103c1c42000149600e0f4515035a140707940d80700e08e0042c059840d2030303040554030000c107010b044140080d4903403032070055401c1d201c840c2800101410003900d03510138403140d01c2341200000c8607030300070003a40d0800443d4601c49044c000c100384141d8040c0320707030900241b20071000150300382003000030f100c00d6010301240284900e50f81e0300c4126110895100f2060301c0116840030906000c02c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 976768705 1250 976767455 976767481
    0x5160921081309050910020a321c0e0f0a030e06040308160218010807170a0b070c030e030a030e0f151c0e0105060d0f0c0e07050c0c01080708 62
    0x400c0c4524403040c0380005400d401004415030390030084032951034101703116410004010345141c86c9000c03941140f90921966019200070002103545154580a260090460079005840101d4000030171300a5914005491000c0300e480201c08202c0c45185000c85844c20b07146d0014000c0c0d090310b100001040b0300701150301d00766500f22400080651201d010800400044d00100240c601000303048480d4592b440e0a104005022440c0d52900040513589001002042c0000a907030048894800d01080e0b51015020b4160810440c120050705150b07210051000302c03075108800d4100c0d9400b039924910f02185070010035403101099500500003800c03400354440301c0d182c40c50f2a00303500500244044d46c0c0c41c00c160303500c6110340c0158201c1c490850340d030502d807032182800740118004901004000c11441c0340407000500034001c0034202030103410a0414000c20010001d034240301510607415800c50510b0024802080b03903000703404d025002e02031101422000e50081d82443d0066140f43c842d00891358424003d0051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 976769955 1250 976768705 976768769
    0x130806180d050318100e0d0311040506070305160b07020616020303010e250e040e24130c2634050603180105060a03050a080702040618051609 62
    0x10076403400112108180400c03c0c4807280300301c0540405d40120000d591411f0040120310b0310b017414200b660300d9010302038a20894094030400c4a41e60340703c1426041c2207401d800b0340840310100c541d0640108040c0b05001c02028460001075080f103466a90748200043c010300e43c84102000342c0e200b070005101c0d020516550962004104210030032451150110340e41c0c903000c3c0205240031840741c0c0c000c9021402e1038042c200e00f40300000b0041a103003000000e031055421a102d2480d215040c0340e0080b4062a03540710103100c90541100f00b0281d0300e03841e03c0c0d0320741c80368a03580c1064001c100a9242c2c05503041c0b01088008a185400810607501c200c401d80c55100d181689960b41c4403071070046004a469070311400a0350241042d85082880001166107550842d1310103054548200e0a00030100001000050860f2199900ca1407440d21a8480c3c0302040c0a4003241d00581c002c2542d00001c0e1114241c66844203210b61148101803481e140c02d00402d8031000e1190080c280040740010203103042c03041c0d800700001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 976771205 1250 976769955 976769971
    0xc030b0c090409140606060a020606040b181501020c0904021807050c0d0c0204111c0e0304121a18030d09150603051006140904140111130806180d0503 66
    0x2160601e10340c002000c07034001c0b003421280c00d9600d00e5a0b8441d42c00400015910507001c7d1174841c075280594002035a5008001c1c005407040380c654001d861f054584d00c1182c0c03d15038550f200902181099420601008031203103201d80144602c2e40b84a00902e41395039079600540d00501408411039101c0c90050303c5540040c074800500c50200880507007907100b0040001108211354483d800640382c2e10411081c2d9250300046206064240003022080181141800e00c3e02d2a107400090461040340d01242503016aa1180c002c2d0590014060107008040a040c0d80c500411000414159107226100400b01c1c04842c070340d0031640c014010301c6e21050306907110040d007600545501c6403465000204a09480c800d13001290b940c1c0045802030031900741802941c0c09062000d9918140ca0f02c0c03e004281c0580c0020005860880b0500b046030105400f907002007082c44580306035a9445903c1300c1c030305403907243c00d10401400b031040000241180c4405084441ca95003610f01070260019100c2c01192079401c09000d070b103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 976772455 1250 976771205 976771207
    0x10b010c1205070f08160b011203210b04020d091a0103211106042109081b01030b0d030e03070b090603040b040c08030705011a0f100f02070e010f051c0c030b0c 70
    0x400308a401021b4400354650ba03c400e401c1c0c41042ca001e550550040c0e01c41d04400440700d0010300002d802c80480d9a4401e4103032135200c01641c99a031541c1c06041c0c1d000005400a100007031100c4081e000c0d400200e402e50248907103c0080c450032a00140d552424400500728081e40480000c0e5074424980800c030201451811030f404420000a86050035010790b002c641804000c81070b410743c00640706101104902c43d05101041c45d00c0d00490948a020400c0c80d6034100c55214851002030780a0b0340215030000001d0418104106d0714500a0251031103014140e21900c10301c403001136160220f204841c201c060242c612801d58480703944501e5035a00240c41100d451001035004550501c04102801104c1c6c0120b00100740c1c03000090b580051541241c0c88280140c01b03082c091485a01e515240c4c10108070a4074040c0d034503114141040f824959140c1069000c040c64200019250721900b65400545004543d00c145640b014038130700c082801c0e400c0d40200308040410301000414840003000d136024a4054050b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 976773705 1250 976772455 976772483
    0x512061306030c09020a021504030219060e0115050f12031b0a140c130506010e0127140301050a090213090305090918150702150a11040303080108010b010c120507 71
    0x1003070a4408941200321545e902080d031428281d41000b1006510318441003045c094102514008c0d114400c050280020305c0d1900142420042a0b41c41540704040c02e5000b0810800e2041c0c052800c1030b064030030244240794800300e8051a00d48840072200c2c402e41c5600651509a0346c0b003413202e1016224460b070600e4000c0c000508041680b242000034114140700c090040321030f0700010070078001c44050608440d030340b402042000d00e903003083c8100c04001090030308000f10200c000c000a12240b51039566411071003d600b002844103841113448e10061400c8009008a076281282103040713440040d030180d4070040380c8032042200741c03d5501080905010b440d109203002d0316000400d0111609491003004090307a00380071011721100384404040303203e01c00d0100e110b43c200502d000350b80b558500003c10a80415501244140680b45c0c00065481860303551552525034904001e00401c10034454103c4550030300000c02c0303456104003c8100020340c092520324044000d0711003140c203a0032151048941080501704 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 976774955 1250 976773705 976773713
    0x90203010204030b01090e03030606040b1804180227062b0c18200d06031406010e0a05010305030f22030c06030e011e1113031b0501051206130603 64
    0x402c040d501504045800354507020044044408040501a20350030a0050203801ea03160411a0700b204c3c11440c840c0c0c1c4a240c2040984010650110305580c0145060b6000d180c402c0c0010781038000600032102c160600600b104a60382c1c1c3c2c01809200500a150703034000441500d03107948000751031809038031240d00884080c0d0480048105442c0d0982c2d5110a0f428100714513a03004540c0031000e880b101080c004038030740c9465031070b4200306850260060600880ca00343e0609103a40000c0003140c10140000465800d181001c0d1582020301440001124007000180c1082050280038103c0e0b5215008619081c09034400007400c0c1c01400324600c1c1d481411281d044c0c41201b101c0c190000e140142260790400d80350040180451700080242c1e04281d05000c180080041424074240300d0b02420540802c2d00b040c419110001c900c00c0d038031105000c01d9807000c040b0610459007102040388a01e0703080300c0c883e55110801561540034108102d0040000b900002d1807074200650a41c8100c0300e2000081000c980f65030b9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 976776205 1250 976774955 976774957
    0x71502031b2802010e041a1f170108060403030c050f0307021c02010c1b02010c0219060206071716030204210507050108190b01020c1008070f052703010902030102 71
    0x2081070a030b4880c0c8203040340c940110080755000075882284007050b4446a0019000b0440d1006261140355100ca14902d0741c185000352440302c50005050621003480f9140e0013106400f60540b070300c005501c4a1030750742ca960226a0b09816506810300400c0b01c1c0d40e890303030b0440162400e2004030301000301c00c6c0700103000e40030a0000303507008210342d0b00985144141c0c50f070166415000c000741c0004680c142200c2d2029070360411191540c4030070032140c00607980158001130b00c240c90140d13002508207640742000601200c0700e200500603100c0ca5426100d80361a81c0d6021100c10040c0740b01c014074020388902103285040540110040c920340f904003d410156922420f080311a00d60038210716218030045184208442803204d40007500b02420708102b80d05040440c850141c8007510492103840d922504403a0903802017102c040030080007002c80801e48540701d8001c01d0074000b03a801e40081014158032406c3d9600841c10303903484003c460f501107494085c040305400d01c007030200c010725055582c511110015031002c0c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 976777455 1250 976776205 976776247
    0x311031606111b0f0f060f071b080714010804060b03060c0d0b0603090d11030d0204150206090105330409111207060e0d08090904050f0f010b0307150203 67
    0x40c90381c2c000001c0700861141414180040b103a60703030610350782c1d030b0581d503884203503c49034440c09482d10300030128070b030b03000c2400d0f480380e5518070403850000720b083c2041141504d00940c0c69201c4560349060740b640c0300d074840d40d128024000e0171220300c110444100c142d4401c80081e6401400380740040780d0712050354082820300106031243d120f0040005050050001c603402507104014050340d50303518610781000280d4840b0242e410030410800f01c603040010450003001039038041651113000b1582d07241c4c2c40a182200e502d445032440058003030080050b0036a801031181500c0f440000c00c401000b009407040003032015020b659480302d04048000d901085890f148600ca07800c9100d0103034040c640c11050100001c61680c240442c8139940041001e2225541c0250500d0060b00705941c1c100c403440c2ca61510f2225401400c81d284d4105030140104414400001500404401d12200b940d08403424410319500365000603902c00e0305030f80008401c221a5580c400c1c200e42c14002441928180030401c1d4000c400c051b400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 976778705 1250 976777455 976777457
    0x6030a0b0412110a0f0615080d031d06060a050906040621020108012112200105220240050702060f0403080a090c08070f1d0403090311031606 62
    0x1540c020340d0040d00700c0e0f2982c1a0100000040c654181079546a0f120840c10072001460380e62180200078621024129a002a003003007025101d440200000013001490751261000c2045040b82004030700380404074209004c0c07034018221903079050412060201c00c0c2c038050003007500329555000c0001c501042500300000e12421000b43e402000a074000104085410b80080c1103140c9550440131440e40c0300d07103050000d0f80e03005c0041010f0401d003034402d45071507001c03038441c40c01c800480c2d15102551a046d4006131280308011030015402e0801c1c208500f10b0520000d000303401201048100d103240b98000286003071100c00520b8460b20300c0c844521034242c11030689640b880a516075040c40b450030340500c601a4441c10440c0f4001940c506520300411068001e084d00c0492552011074405008010b401400075154020803154155522010000e408501c0d00c500a440081144c4c5038607801c450310ba0781e80c0166015a1003201490454a81b4101808a210340aa251007900e00400700e502901c11588000d01c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 976779955 1250 976778705 976778723
    0xa09210507170a02060708040501061505130602030301080c0112060909050312011508060f011808070807050f0102150c070f080d0c0806100f03021e07030f080105030601090506030a0b04 81
    0xc902d442200055490140c0b09200c00610100f408250300044041c2d102410340307014050707600d550a203180101541d8201c02c014070000464481c0f01500613009204071b406547c040c3e2205a610b100403a100d00082c083d405054125580c5406958030580325450844000c0c3e10000e03000c0d6880314903004450000030704440301d400102d034030144020300b41a443d00409400002a00d43c07500d01070000c0011000031f007060b2244521072180002a4031030810903a0300007c4090b04961103482c1c00302c040d82d80d042413284111501c504000810242000c010454144006070018180c000054000d081d4154004080b0741d0b0415050010a011071003651031804014028140a81c0c0c600e420709800c2d040c3c6140b410a80240910203052140e203450b8804540482900341c900a40404060007044000c0c0c8a00191052100d52504a420703100c400c81c4001c0c002c80e403190315140f003040102d20056031803079801d00c130780c52341504000010000050240c101c16400300c03006055500305041e596030840e1b8084265815508094 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 976781205 1250 976779955 976779967
    0x5010f120504120f090b04181e02030912040e070509011e0804030807030b090a021e070606140108010609050105130b1c0f09081b0f06010806041a0702060a092105 71
    0x31300b00956640c6484c1c00c0c0340c00030745207003800440c0b16144294803440061207031a03400712840000d00d521011010700d2002628008641e88e610303800c069001134400080380d0040c800b0486071001101e00702da0450740c5120710120165a0041c2c20303115504014804c905120300c009101442a10b0307844041001610b54640a00f01e0030a410300402d0780100428800c1450715044040190b50360361201a0341c06400d4520141c0d44444c0110501c0000105096003201d00e10040381d140104640398018106450520102c80014850324004440340c02d028800c400104418440c1400701d940315000400107410040b0b1182d0b401651100008025403124100c42146030011060b12040840b901980c2084410084140181c40306600e42007101c5c07003035500e07003010b400005c06240006081488034003003402200041d030381e00350380d203081080d1950011101100c00070b075150b00154a405400c081d490186446500410059440c42604402401140c1081c0c40c1c48070358401c120041c080c580c8191150610907a581f680b01d603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 976782455 1250 976781205 976781207
    0x3030501050402091c1b0e0603060a0b0108070305060105070b04080903010c090602032a06012606010e0403081f080a020a1d0c16020a121406040c05010f12050412 71
    0x41060304501c0c80746004000710343c03485d0f40d00b031940c640c18502c5c00070701059211146005501a810344007050084012405c0000e03000c1269960340340714010640a541041e590740100700112a00c02c44a40d010500302000300d00d0742c0c1e1103a4400d42d80319034181400f40ca084003035200c0800907281145d0494203000000f980315541d040a00400142d0071480c10b0512641d400c09901175164041c94201100ca0a00444229201218240010706010401b01900d03025615000480c542021560015420a03030110002d2041d0000042c0705040b108408541c440c2912a0f1341c04440c000c001a040c2d452000710b0071040b84c0789000b00300301c180c01440108010800d01000348180642503131154400c80030f024400700c000c00440102c0306035541c0f002c0f04030800c40ea14090b22a5880c108403500a019400044040d00400c088510ba0b01c616201402001211506030812200d03d030340351011903005200443c8000104400d50003040c200302c0c41c150a042038200150704100b10801c80d00b003100d0a40360403160036141c003d11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 976783705 1250 976782455 976782461
    0x14011d1b0a180605060f041d04020a0501030207050a0c0e011d0405060604110f0d050f010510020c01030b03030702092d010f1412011802040e010e060a0f1113030303 72
    0x918024000e40088034091800210200c0c454030645a001070002c0140040000551014014240040c1207648500b603000610350740317402c1401034001e005221040c8a5075403555901240c82154020180d041072070038900110042e400c180400c69071442904031140002c0c0c80303410180050725424000c101998500301c43c5000e0301c10744400004071380e100c3e10103110108070081a810b500c00b02c26280460540d0340d83c1d403420320910481c881184400d5001c01c2d031076425615500414060011420781404990300c032002c0140510340014080056880342d00c03c030507554000d8219404050005003901d003040e000d46c002c180000c1c01100c41d42d1440354880780700c141090002c07441d041000c44007042c003003040d81003c6484580d030b010340c020051b5005455000701000d660780c240c8a001700c20060b00912860042a030840d04403c01f400d0101e100d20b041000f5055001c80c14440d19807003169000090038142c41e1403158400408501e00d69074101030b1240ac2d0003c1d103a000e40b000b0285c07151b486142c1c0d00d045185040041c21 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 976784955 1250 976783705 976783723
    0x51f03061d010e0c040509010602100c0906120506040b06040807031203090320010204091a1e010906050f0909010e04060f150302060c0715090602060c09090103080714011d 75
    0x20a5468030340900c21403a07045415a003150381801820307140d800c4400164084c60b80000d0303003c0312042c00401c0750b5034003142c1e1441d012820b203001d00078284180c0042c0c0740d01106004000000f83c0b200240e040c0e1010bd900a180c00440140001440d0260800407030500d074030580000e03c0135441051b00300304014043c101807401c40c42a280820213204543d400410078107101d00d6a21201090301103c0c3c402078000e504071030051404680800900140305091103400c3c40c10409c8031322030070922a9541040e0501103104170000d005a5810751201d0810000361401d8000c41401d000e01307041800080c1144e140c102e0080c0c007900c0315031004071a500c1e10b8070f00f5070140c54030882204d040c1d6003400314a0b0204e41110400000356541120f0fa26128520300000c0d07817a10b041c0ba400a1510748641c101007001ca0740152205003a40c1c1554251102c581c1c50001003141c41c8205c0012503000a05100100003081100e8050000301d481902c805141a0f401d00c01039003510b58196800109042407036030842c201a04201c3c0a41c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 976786205 1250 976784955 976784969
    0x80a0504030506130b04020105030414101d0f061b090306010e18121b0a0609031e1d04090218070509120613120e0a080601060311041815051f0306 64
    0x4c11808a41d603001040030050002810300402001140c10003810420030190750444d81d044850124510101b207004c1c003090b05980b43c0c0c0b442000d03030a40a03c140424038102c203103000402011191588824064100b205455a000680040c000d01c07a080e58140505402407243c510481558200304052546904008050303201603400803080f03e003040380b05070594001502c0c0454045540c201e2094081c02c00c010302100401040c81c0510400402d500700040900d041d50071080c07542543c0f082c4000343c0d01c050390014584210505105910403519280e0421109184007505502c11284030000c40e120401c4152152400304902141e001054203201842100d48007010000b404541010140015110782c241800740c2030030300000344140d0702030141c0c030003203604580500000c0030203a450250b01d40300d81c02801100d0000c1d0900f046503c01c20540300659007034400e044a160000407903c0007610041400038544014001c026800140641d9100c0440b5594041050291000c20446500408030b5007980c00c104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 976787455 1250 976786205 976786231
    0x5070603050c040f0b0901170f090f07081213270f091a0903190e040b0f03150709170312010801050c1804020405032a030d0c0618080a0504030506 64
    0xc1380d440c2c06000800c17a20303096980356803407951000481d4400c000c00f02802e450080607040c40120442c2410301c1e8130030145030055032502580e0042c00b40e215880c91040340c1e00303030340301040700c1021420540040c06c801800c2240802019075981c100d000001000b2003000c00a03503281c402a00d4125540504da44951031504104107180555681d603054070703a0304d009038500c07002000c0021007003001023086400c81d54040c030b1078050f15010310740001d00304403020101c94016410088000c00350b0800c0041080c5042c40207000c1c0840b07074208490101c03000001411a0200f020740c03000000c00740b92a010311100950b88001455031040e60410341400c1f00f0040e030204029a02d02000c108500c4114000e8601d00740b422891150301f2a8942d00050190245402c2203030b050080340715182040310340091800380b920200b24100c4485141508054440c042800c480340802d4100c0b01200004076a5031040c0690403500c4a40c18200325251201c51164001001c604082100041d0030f1051000030060316521030301d084840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 976788705 1250 976787455 976787459
    0x20702091e011a0d0c0905060412150603030813030203090a030b01080f0708030a0e040603080d05010503100c08040308071710140a03020a1401090333050f06010f09050d05070603050c04 81
    0x66010f900c40c40744448079040d50b50b1a445030032407066a6039801031000600e01a181c0b80c8a403d40e5403a080b40d0b100c202ca50855002400018034504c0c0900000c0b66050b4a500c0c03030650307803007148502e8000c81100132011404208620100c994444507150040c501440d9180d100d5130422501d00d20307140000c00103410550110304200415540042200c040c1070051a0103400c41e0070380390115000c0d10058000034034541d40454100d0141c2c155a105d01c1c1214030440803142054686400f400442303c501c030805001801e19000100464000c582d9070360401101d18000c64080c003955628041c10000b074030460307004c2c021140f08005401043c20202840a0111802c0e601140382d98001101d96081d44558800c20b10030507803001d01d50380200103410083d41c00030b0b481c860040030103a00c000d01800240e268070a41c1126503040c081c1c03134240d00c10070380300c0c20044a40302c41e1515082c006503101070314890494108951181c01081da03407504800c12000320310a074002c0110508190300601079540080181151400510003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 976789955 1250 976788705 976788749
    0x60f03120e0a050f01050d110d0b06251104180201090f0501080f04060b0d0f12080403050d11210f011205030a080a021e13050108060a03060f020702091e01 68
    0xa8502200d104540302c1400907801300051307a0901412044201c11403601c130380d407981182c0c0d144c0100003200d410320040001145020070030210f40100034404404040b14008140c1e007075020079212141601449858101890010000d026603020915062860b2412000d600855030088145d50207448288590280541010b000902004006094003800102100800c0502c8181e5009000c504000b80491608403070a0909600039411601c0403500703104000b18510307002c3e10861402d80226455034039146001c800d603160b40060502001c00480f006410011400e00d0001900741e1481145800024400c42c540484051000c0030160300001c0620070002207440024004011203416031080d00b40506940c503040daa23071009001d114900e04ca20580640c000d0440d246240207040e084d07540107407050401782c80b2001190002c5065800c3c0c0d4104030441c405200103000d5400c14000d0388503d400c01410311449800141841c5020f48910340071181d00742e00d5014000b850701c2d0150150200c500d2500300207107401c0d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 976791205 1250 976789955 976789969
    0x1050d080306040e010e071802030609150307180b030f0102120429010e04051c050a11010222030b0c18090402010509030f011d0c0906060a12060f03120e 67
    0x10000e08184002000440c19511a407000b200004c40900030070242074000a413503a68015401410712003c4400911403803540d96008481c420340014100310b01c1c0f03480b40c100846c070710054404c8a5516000c0c03c1070210b1590f0340302c2d000c200e2082c10100041416040b01d0149800c1140e5900c81070f22503401040340d001c00c6516540419000f550020a0094014915201030328003e0400c5220210070391090001900d040c6d4111002c2c0141e0140d030599079180e1419400e002c1304006010807001150707060080c1050280180700244400c0c11034070016280a03c3c0c0d13000001c01c3c0c1d9011281101d0740f403010505100388030003008001c0d4400d000646051074165000c26010300d403600c904549200d58864000039086910400558080c41c60180440d0080c808080c200d80c00713818071300f0400c0b0400001c45003d1058200c0042c0040e03104d100588040f03016143c62007800b4583d4020000a03060003503555a40c030009419101c2c6500030801507044d600c1032811071074a402d590405100f030b501041485040340c61a5581ea00d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 976792455 1250 976791205 976791229
    0x3010f0501081305030301030308060901051c03110c0307150e0604031707080712030507030b0f01050f03150d030c03020732042909010941011404060e0105 68
    0x108014506603980f0200381078000160354010100d01010000004046d001020603008078011a41c0740512303a2900203005000700c08900120010542441003030100780036140321480394120b8030503285040810320100e80340002d182d02141e6104c0f440190300b40c01c03507406022240320304411103055203481d20b5611905811401241102501d480004089080040d1402141c0b90743c1d50040c48c5000400d0002c0c0090300a090498040c03000c6410b210404203246816415280c441e80e0513150b80e414409009032580a40d04010113404810340c100501c02081c0d51940c85002045101c1c1d030700d51180302890b14000f03043c8080d69000d10040b80000303001c1521200c00d0210007020080c1d03103801d40000c0040b140080c1c09020003440740300344500801c0070002c0b03801d41c1303141c8201e42d00300035140c10306541d03618482c4d40c0c2254005182150301c52110440c4e844c40000018100d03660304404901500d4402081c4818008908207a2090001303a244c0b1100c85c0d91410700740984c1c4010708841811007070135850480072a102c45161 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 976793705 1250 976792455 976792457
    0x70509130f02040509010b03090c03010e0d030b030f0f0d030f1a0913060221011d0714040312030b040f090b0a020a050f0a03050108062208072402031b03010f0501 71
    0x203414080301c200142d80c161001040c1c001d01d80150380d6590820021650f005540d007581500469610610380c3c1414000c00e0464407000c002089500e00e080000c03001050302100700b80d414064aa90b211202000f0054010580303140000f03010341d0391020071302030220346541b14018900790501d19100d040c0003140100c5115240261a4042030380d503423080803a4034070660800141f080f0320101c2e40450445c449410f0800411480e0718407032107030343c81d410040c0107900070a80751410088406d000030540e91003171000b41103008040c1c0f482410705440344d44c4e0960124144030480c0c0000c1d44d4045102c02c1e440c140c02003c1c204041e00404001c51451521a0810044020314811036590005050a107c0341300307008072a040d0010106884d155401480014090302080c410b50150348100c6011505002400701900a0300b86882c0b040d0360300030305603501d080807500041410741d1150b119032440180148804040808840007000040c2d030ba250551010040b440c2001c1d040402c10b07020320061010100d034034130420941e682 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 976794955 1250 976793705 976793711
    0x11e030303020714100209040b0411030c30061806030a110a170102030609060616020d0206120702010c1e12050901060b070f0b06040b09060f03030d180b07050913 71
    0x3060030003100c9540e900403c0500c5104a48880c5455201c82c1c6c0a401900004c5805018141e0283c0400040d11403074101c072208000c040010540707451048000300601440c504d0b440349800e4035084110308694180754002c40b41c1482004212041c6410901d60300c3d4040b41c2503004406051030300c00304c0e5641c5503202005106400701030002c4103958a031502100100300307038030742c0b404003400c1143d1a41c040d42040e16924040d68001700072034498940345059514594480700114401800c9408000a01802070400ea07000207082000c1a4a8412103009610070f400c40e0300089055450807100078070021280c0f0403c2c0c0079425560784060b441c0d034842490190051011008a2981c807a454203d004014541c0300c10000100002d446c3c003088411800c1080e001e01404009000c0d03501c2400340015911129040b65012000c840015524540a009005182e03400740c100d13030922440740c1e140300c100d0780c55a0701c1410450807042c5800400c1151083c0ca5840b1150b45481400d1950342400f188011340d031440034038800d540f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 976796205 1250 976794955 976794967
    0x24040518030a030e06070c02010c0602030c090a0320100504060305040c0906030b150105040f091a21060a0903090b070501140c040305160b25061112011e03030302 71
    0x110040c090408900d055940c1e881c18060064000c010382c0c0a40b08050140000089401d8065101580d0313441c0c0684070024507200c940c0d10107000313500040c0f070b01c2c3c803547e0180511815a1610320382e01c0b02840c860350303c1071004005020401610394404004510030398400c0d041c18802a4420241c0e02101c2403801d020449031150318010b00d00c0003107a00200c1c42c0501d44480082441403078120b0600520b04a002d2003c103560400c011a0a44198000d99a90001c519410009200c042e03000c03501d4040d44c0312031588203060710400a8500e101018848100342d2801ca042d040c1d00c4814010690809102e00c010070112526039006000c031000ba100d80286800c001c1207500602400703400002041e00304c0300c0080342e14070345040044020b40090005481c588a00003800006c020007001f0380c0c085e114800d0310303d0f0600c0c502e0502505542d88146000446041108a40001455a0250800322410188110b844a040d0f0340762049481050303002042e95042c00103001d04070a542c0c1d01c24000e0340d4042c030300940d84207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 976797455 1250 976796205 976796221
    0x31b13060e04050c0a140d3305151c0b130f0c0f06020109051b0f040203010f03020f03070e19091b031434080a0f0b240405 54
    0x105500050403041e148040004200c0c011403808072070102200c1464805440d95900600c16148a40080d002614040054041001121068034021f0310541107546003100c42c25112441400e80b080010075a183c00c2131100180800c2044240d510055a44a5200c2d00340e84000c400310000c81000f400c2d20b890f000108540c0e03036402414205075070300400c1c0500d1821140c64507a1409070075100f00a204110800c004c01e0103441030080c00e214a070000010285204c2c1402001600002e20303002ca680403014580c00811500d560015500038041c0e811504191031450044c07004e00c0d02d01802c294442d13040420f05100004e01c1c5545c041c0c1000138564242481084212414024808008043c0022401021400110405203e00d600343c80c403a1101d42078106804030352030b5a41100a00c80324080130504500354042c2400c131045d80716262000300101e60300343c3d0703500c0450400c01e1440050ba08050000026420301007500d12803604207881498030b540a41d003c0c103400c4003034401244058402d0b0b40703660120708a1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 976798561 1106 976797455 976797461
    0x1b030304210c02041a040606030f180803040611090a080102030601141e030603070b16031b0c050d1b09090201090806060603070c030201020d060b07050c031b13 70
    0x102c00164200400340ca24441506071500c44440f03c2083c0e0382e55030242400601c0c3c43d48002584088045041e425640090103041500e080400b41c40005480441180e43c096003004000441c2c0c800341402c1c2e40c81e407080341c0800360b1114803020007040c0301e0010b42c000d6008800988604d06d0a4030340202c0038060b0700401c900794030304e003086401c1044aa2403d02c020f50384420f00038217441c0b00070749034460300d549034202e51ba40c2405503075081000c404144d0012001d0040000c01d012461b05410290340e1540c95980c07500940c1c2c0036602902c2d08408000b40f0461020090b200e840c0294070082d12800c0341c0c0000c1205503400d90010350032241c006140680412200c2c090744000e012140317541e0b01d5030800d84c0c1c0341c60401000c0301159820403d69000d01058482c0c04081c02140c0c2000d9a11461130900c6490103104403070841c440c0e00990855000705034052003012460350300b9200e05410030790407000c180007 = true := by decide +kernel

theorem cover : BRFrame.Cov 976618705 976798561 := by
  have h0 := BRFrame.cov_init 976618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 976618705 ≤ n) (h2 : n < 976798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
