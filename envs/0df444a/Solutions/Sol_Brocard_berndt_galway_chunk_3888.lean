-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3888
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:58:44.315521+00:00
-- url     : https://prove2.me/submissions/fd3af3e3-d3a9-4cd4-85e9-072b90384fff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 699100719 ≤ n < 699280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 699101969 1250 699100719 699100781
    0x60b0d0905061302061c0209030f100b0303070206120702070b04060503070207050a1206020d0f090c06080c0310050f12010203072006100e041415070f030e070510050d 73
    0x240800107a41a1000703c400183e403040c0c121a54168030010707000e41c144010a9050203802000d1145515003e00c0c100c004a040d400941548030329045003060140c07074441414580c03244102c207400b0b0b4200e041003001200c075044000da0240c1001d0075104881403641e0f6016104c100d07401c1500b04400203040041884401c990400041001d000122016210b80b03207030010081d440c1541c0c0c50700030543c940104013400790709115408440b50507940001806010300707600e0107800380b0026020309004260b8407008140199a607606803072244500100780100b0701e08000802040844503c24a64080b020074401104960f0a00186014040585402c0003106030081c1800400003104c10510f02d603842182007040611210b100c0074100c4d501142d4000140d00c4500303155002c0b69412200640b40e2045140c001d1980381700c0041144035601039a102040c0c905540402c4040c0c0d039541d9207142140d0b12039141800640f400ca800300c0c41801c3c09042042c03418004100741d00540f01c408551810042d0303441c4844140c1484 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 699103219 1250 699101969 699101971
    0x30f0703020d0305070909110417010219020f06040f020f04151a120106050f0f07030f0815030a02010f09080f0a0507050d0515041a041b0609030f0b0a060b0d090506 72
    0xb1504090291345010b1030000e11401c1d0602c518600e2a85422448007595071400c101c40181030586200e808503800a080a4040d51141d540241a01407042c00400c41d14030120703000160342c41800c043c0c04030741c5444d240d808a20f110081d0a031703409662000100b140340d0711807090360725100008452207140392604100c0c1051055000d804c0076022410020031800000a100440c10746005003012515000001c8181006024581c3c285982160028220301816082854050a0201035952009950b1005040302c00c803840900c0d181c1e003551051582d030b801980100405c510b050f18030b207000346d131b0f845d90f0701c515a14000ba1505440d4032900002c20380014400184195170140800307030b5540f00381e010187d4900341d07a21100b00c58502c022061401060070000c000e003001c1c050300343c1e003100880b282c00e050424000c00c0e04c0c0400c42c4501452000000110540141c3c00d1000700c941102c904100400340e502d41203103140e0000c000047c00c90b66400c0105200b02e044000e003602540c181c0c0f0000710004580303806450998 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 699104469 1250 699103219 699103243
    0x504170601150c210203130801150b040b1b0c100905100305070518040b06070b0a051602030a0c05030904090b101d0a1d060a0b0f040b010e0d0f05030f070302 69
    0x3501e01100c2c00440c1e00c0d004a078800040e14108402444603100c4220700310f0183c612001c100387c42c140310000700c4c10341c150404180c0000c0300a1500b4081d6803030011110511407882030601d00441070140b02c06540748106c0144041040740141d1320070602c000f00151305100310208800201d54001c00500c62400d040300d1505032050796040412207801d061130040c0c0380c0d005000c50b4004044010000b1000d580386c0740c00080000e80c01804094444005180610000c4070441700a03016074500400a40b403082c8100214480203000d8014510700755180400b100e4403021110159047d01c0104021030040d00c440c400c0b0b425082c0a524100c0150409020456000e0241d40c00200750595044810b44191800c001d03040d08220a200c002451140c65020a03103000180b0a101e0341c0d030300410040050f4051542c000c03641586007103035800485200801000300312a4070700c40c010300286014410703080a040c03c3c58191503890041c0519072000803980c0e111840c47c0c2c4124000e5045203004203400b8101501003000d0a045a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 699105719 1250 699104469 699104477
    0x320190b070321140f060f101704080306030c0a03020f0f06040f0b2101050f0913050706120c02030c06130804030b09010b040501080f1f020c01050a15050307030b0412050417060115 79
    0x701b03000c0b00080440141201941c0303d000b0440c0c0707444c0411701a4038410b1100d010a03185250700d1a040c2010180350700300302d40107402401500b03007903020351500340c000d102034a40c01848407446503003200c20700240e001c070410b049030001004c010104100d29400629001088000c51596881105480c165001500703244080700c01c450800043c040c0b50f03110380c900964070005840300780c0c2c96078078091114a038101030720025005000f41c1e04085040782d8009a108aa4600300d101801000074111040f46d480c4241c0200c00301540081010032035545800c801a801c02d030144038405e00b042e889494201c02c50300e090701e03840281d039918240580c080c11b041c080e1500400002010b800b014800c040ca5540b5200800c40d25852446030030b071040100070715581a5000105058001c10040c60305024600003000785d200b848408038481800000d8910300000c42806682c2c0c440e100c809540c5640c0d036410900e058005c106018440e003444041044010f8210300ea0541c205030005042e0f55141c100f400486212070b1207560104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 699106969 1250 699105719 699105721
    0x71209060e15011d130218060108060d03050409110702030f0a031209020d0f051603081e09130b1c24060614160c0320190b070321140f 59
    0x813500c07a0128071802ca40c104088240e40e103201703d06008070b11a24000b98030204141d003c011014005211a101c3c440a0b240d015035520b5544c01c1003419400c00c00c3c0100016030820050049180c190469040d5400704020389081651650000741007100020602c0034641c0301e603a200d01416407210b04250040c10103401041401c0c03161300464000002e00c40040c000007031144d55035013001810044024204010449080300030b80b20b03d0075065a901418440030104440c007080500ca561071030441e00c00f220010042410004402a00e82c00b5115004045a000c0b000009158465180070014040a4803a00e10300c11200c500c0b51002c03602c060300303881601841d480c044c0d0600850b9004100e0758070403035a10400380e440d8640300c00d61030307006c8692501c01407a0098868000040040c3d0f04000c0059941070b58400c80c0034400f0005008544004040480701820348000c20070201840c1801030007610700a00e0030020f888034607103104110703400719070f1070342d513150b0340c0f02001e01000802061264021503d1180c00010b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 699108219 1250 699106969 699106979
    0x60a1a071b090501510e090a1d0309030a0201080406020c060a0e010c0206071d040204080304030b0405070602010e0303040b090c1f120213030602090105160c0302010305010605090315071209060e1501 87
    0x1c071700c081c41c500b0000c5246401c0911151409940040c1602000500d1f40d4860324010002801070000080040d0244401d2000c00e8406003004c0103440e140c1c00c000c1c000b001d02d121260011603c010000e4019101d2301d50800c4409820402407111038400c1c03044810200742d4140315044282181c41c0c076403515007190004c5042c001c0c42c40e03000b003098400d0803005500390034076015000000c009105680c4205418480003800204211020341110701c181e0190040e101300e1550380b041a0300380c940f002198012500100f0005002588480310540c0003046541155003040703a82020031404641001c011210495607108040700a078410020215903a10080540c10032540c0c40c00783e01644110b0000810700c60300800d150013581d1049060710076240700f004000000b10428108184c0480d41da01040c3c0c002818000045a2107010304212070000c08054010080c0c006984900803000034007521480030400b185158216100880c06190902401035070002079201000e07442c18603207200b0318881034003a0701c0e001c01044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 699109469 1250 699108219 699108329
    0xd06030c090e120d0b04021903051f030f110919150f05060d021c0204050307050d05190314120919031403090a060212060a1a071b090501 60
    0x10070b64255401a04c40300f4a0040a014003a00c00311983c20074400714100c03145144250b403098000185407001c00c120f44a0060107090104240140820f800703042c20108009019580300c000c0d03450007a40c0686c0c03040801400501011000d991104460074042c5941c08109124840c00c240a058024401d16042c03400746030020082c1c00303200342481400c0100e4001c203035090640460780e00702058014100c6413600510002c009400038041c0500900c203840340494681894411490160380100043c410b210140f04041340341c101454088003000b40c03000c81c0e01e10038400c00c0c0c054441c500c12202002402c0c42c04401880ca00300341d40c480d88200d500342c43c400f01c01090304629030000300304e1507080c0c880d680d51341d0320b00c01441c0ca50800d0380100f003a8800078800e00008800010f440c0074190882d00d200c0c00e96a14882e0405601143d9601100040104111000600040e80388403204200c00100945903542d08104811500d00364480b07880d8818650384643d0b032021240f041c040e090840c903205164400d440700030b01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 699110719 1250 699109469 699109483
    0x81b0313030c052107050f12070f02040e010c0509010e090739121d0105090d02030c040203040602040602160602030a0f0c12050c0c150a030c050c030d06030c090e 71
    0x2a040c404052074080600200b8044036580d200c03140c04c44514002801068041c55208980665190040b908000c040103800f01d80c1d508a072200300c00090034104a0b80311813810380c80365803007203038419078a40941a40c2a007e000340b0110312600d894054a1794860710015111104c8084c05501c01c03800e0004001c40c0c0307030704020b003580c100c064440b112031203049012240349a40d1020044100200030b4400942c108211510518269070041c0d9900d01e20f01010521700c40c0c81020190004c4c04683c1c1800b0030a031034100b200c84803469600090469404203043c1e0007007400c0781c0c000c5c1c80644030a0f40018041c404641c0410100340100c0c2c24104010096281c42c84c029101d025041c00c07070f01000b00c420340f03440000b13110307400964000d5000350007041202c074941000b52682e407060304082d2041c0114070700c80c002e6160051041040880d88912940b0303006440904900410702c0d62240010301c4414040807c15403010006009203803006072001460720f06505040400b03c402d03078400040c1a041078140d071503110380495a2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 699111969 1250 699110719 699110723
    0xc031112070e01180e3426040b0a2a030207060e031c062c07020a0b100f0902090117040819120b0102010b030703031d04020307081b0313 60
    0x5035101c0900b24004075000084100d01e40200c0520080c00714070301e540b0640300745c003d01c0c0440109428040d220454207110395400420060385102610300000c0034042d5141c1c60030001c40c1054000310940740d05018a0f42d80f0140c1d0140c880150190030000618031510940038050450005015075224016422049003000040841015008510141040101d410440103000d0402c00d1740e882c1e180a0443d1078180000c0c0e000000454188280001d03c9001801e900040152080c40070203103e0344007101c246100c501418941c00c5100d0709034402d000c903035003071002801000021101903009140904881e6501c800b074200901ea03600c1005422440c1e071304200c0c0d030503010480381d0444555940f81e041542e4180182500400303c8d241c5028120350040d41f0400640711404144820040d1640b048012400c0350f00c2000380c00d416500038581440401c2c003408102a109242000c4d8100794405a00844e0030303a00184c0307140b030201d1202c506202d20340514901614481103034206007802c3d840c141c000c20182d55109440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 699113219 1250 699111969 699111977
    0x15131701090c21060207060207060f0c02190c1a2113020d0302070503030a020a051c05030c030a090804140414040b010b1602060c060f01082409150a0c03111207 70
    0x10038003c61851081c442010303604548219110030a50505002079480b442c0c044a10310314050743d14002000754810b00c0c82c0c4002503401455884444007040164184404007980d0b9403001007400a0101c1540c09d200ca45040a010507540b1120311008000310b001b40d072462808207200500811031a040c00900c0c0690803901180e180d0416212030405909003503582d0451038241c00001000d112098002a40c9080184514100e43c001c03144100c500c020014540c115000041c0c0401c0030480c2c10740c44070007451304907807000d0000905032080c2d40c86600f55485540a191491030410002c10203203881c0c4038102e10740301c4040052600345400c0e03039006000784c01409629090078002c6110b4035200079043c00da0040c6c590182c44950354004106105942d480e04070b920780e189071180c000205000e44041102e1546050a1452a0322428021600e4416400090501040344142490046000c270001c901c0b0703000b806041000280700038561700041c20b54070380c401d00e0100f07a00200214100207408201043d030000b003504d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 699114469 1250 699113219 699113249
    0x24909090e0c27150a060c0f02010e011b0309031401020310050907030908040b030402121b1507060c0305070e01020703020d3003050105030d090e040b0615131701090c 73
    0x142d28040c0092440029031015000800c021813610215032a00c00800d00f210190184c5540b02c0341101d2032100c01000400100d0881120801035002e80814284c0084c141800f054281103030341c41c10704405403810141e00103182407804000b03100e21000720300724420002e0000c0d0300c0c5240802030109000c0c41c0b40724142c024544c83c4000b03400148070364000c517840799200c00b141d40c1d10395030f400c440c0c9265003060350241c0c82000280b45880440c0c0340080c44102c440802e4200c103031440250b0040143c1e0310701d031002c41c10380d0340c1042001400044a0784071340036001c41503441c00206800c280c80001c2040314901e43e00d60540d0320560080c00560b0302c010015214179071100300086042110049068051002c0110b00d4940c5030002400e020b040c6c043c0c20040c140c2da015000c40740e07202c03188201120150020311400c6804052400418003040070320314a10b601900c0601007020a0141100c9600e2a0b4406017040703500c4402d035201404010b036082450000b40c41401c0081c016a2850746a8180d9680907119040c03907080c0c082 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 699115719 1250 699114469 699114499
    0x528020c190b04090204031502041a0d090b0a140105060c1005100317040603140103150b01031d2b08011503091a18010c024909090e0c 59
    0x148440190500c00001910b43c0c0e03451400c072000e134006000445001c0c110525150a5401d03503c2501c0440e03500200050351040501c0440e0788a9104101803031480d1744a00d114004a580d14403800c1c020744890100140700180100300b48020041078000034803c44c4200034006100c100003070102d044400d0480d00240b40e07100e40c4c080340a07580d182e03440240b901058050005c1c070405004060070840f11641c070107218040c01100ba01c0311b010400d000003448003d0311010f81c01c107030714190b1001201070018100050740f8000304c012031065400d080706100785540070014924000c2003981c6000c00c02101c840d01408101d03070740400038141c0401406003400f4480030300050900c0500c60380040b40306035000291003550101001d80d902d0100d90842ea040144480c0056907040c01605103d02d03411014540d020b02081c9542e20303e910b20707060f0500d00b41e0305540d0400c2c3d6081e04802c102c4001c6000d440c005100b0301c074140e60120014024040302e60104132000d103003007440b003020130000c942c4402400e822174503110341360018 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 699116969 1250 699115719 699115759
    0x6081c03060e04050307052b030e010207020901081c1d010806010909060305061b16150905010e06090607020a051209120105070804051905030412050106050306070528020c 75
    0x10398407110409a40c1e009103c00e210011000348041750040d810b03034a0382c8052281081800300020200f411500241a05002241c400d9100c1d400e15540c000001d8034000086d00025020320003a00070344115040030000c580c041039000d51500c1040003c0c181942c42c504030050000300000a9100782c0c0c107111154001030f01a80c0304e040200090128504c013003203025100d0600c1665424201e5001c5c082c6a1210300c010640000782083d1108541070401d540030344411961446003010701000c03510f03812502c9480c844009002802030344d1600003540c0041c012854160380f080e10703006002c0c01d04015508650300345008540003180049a204e520810280d588030002c01042012a20101c0d1a155518080c10f0042c10380d481014240124050b03000c940540000c030940da00400b5600c04010060303481080100006d0400c900c5607408240200c00015155540b1400310341807010888104000400001d0020030408441c00c42c0d0b00c09000c0080130500d001c1401b007000c0e41d03448030300c10241d214000c1c84840c100c3c1001c072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 699118219 1250 699116969 699116981
    0xb0f030a02060301090906140708060901060c0221010f0f0203040b0c07150b0d1e050c060f04050f030703080a09031a0f04060209032805010e060609070c050a0f08180406081c03 77
    0x141610340055240c07029000300ae5034410b0702d41e0741c4103062074800000d0382c0c0d110f1900300710110b400510b42101003903c0010481034039070b171314000c030302654036040038440052091049849000000303034007603503e1034a4a46100340200c000d2200050220500090001c1000300401004011207001c0001d800860140098194008903900a00180040344072500303251f00440502041403240044411380d420980030454940508a124502c40c0703014402001186410a003a51400c000502610103058503038488020980c000d02c0a00d020170404201041005000450f11f805140996041d52003410151404404d031040980044c2941d0b4000c49c000031103540138041900c171802e504d2860103403c003c403e8151680d2a030711609036080e520340303041c9030145180800c000388035100c000c2c60646580e8500b00140d680041c984401d803058856581d50744000f45260b800e1b5508240180c4d9410307200e00c0710071a001214066001c505000710306001041000600004104580043d01c146001d118150301c8012001040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 699119469 1250 699118219 699118241
    0x507030e09040f0201030c080f130215030c1207022803050c010f050702150103051e07030602030709031509051024180b1c0303090c080607030b0f030a02060301090906 73
    0x80000d00040042e800e000c40f04451003a00c06001c41d05007840305403450349045030b003482c601c4001000101c0345c54002079102d00091005206800380350130700d0340448943d00204c804a00a100c0054000c40c11020800c0391a0701400c07610042a00070009121125520b1500c03c0024026942d000c0c0d41003014052000d40e004040340d20000c0001480c155803030006820151440c00242c02000c1c80c03003401e8841707a4540b81c1603a0704940205036060070f55540c010110100c010400c440d016a14022001070610300046000c1e41c0b01ba84c9940c070303050440c2000001502018070120b403492502401c5230000b40c000c191082841c0c480380c4000b07003000c901001419007083c0402d820722200054440486c14008000f44842c0b0501c1c00c0360104420b4130078105000c0c0890070315440502c0351054220090001384250080505184261075051040341e480720b40300c0c0343c00426554440826140d141c41d8100c4c0c00c042400800c6401d00324020443c1e48080e4001c104a031106000344880113840300724140502c095a0031200940b0707 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 699120719 1250 699119469 699119479
    0x3050904091506090c03090b040210140a020a0c0e0f0f060415030b040c050a24020715080601020129010c1103120c07050a0e06060714070b0a09050a0b09010507030e 72
    0xc21044030b18014038203800340190652810a41304151403081c801c4000d5240d004820541341d49540e02000201007011021000b0412004140c40b900101180034080032061500200280350300c3d803801c4004202583c200310810f40851041005003946e03105110341008152a90204540f180000304000d045000001c1904c00111000003040240f00b20519224a01440c04803592079113078400c01510110310300c1072000d12020001c044d05e005209079100f4108100e98011a401141c1d56012090030003070350001500426000d004225140d6028040c1c09001028482c051a84c40c02014100d4003910a00b005e0701e04202005c0706000c10064124011402c0c4d941c0202104c200300e030150780d042c49552290180d081c0134020050001160304184c401a4242c4580340b001c840c0b5a6030310410300450380c01032002a101c500202c0c11f0686040010b0000700082c00511082da56240107484001d401d643c11644420700401c60094100822082c490541c3c0300c1150034a407050340d4000500b411a2a60740c14155183c0c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 699121969 1250 699120719 699120743
    0xb0601020a021e0310140c031f0b030702011401210201030e010509010603020a06110c0607080d1e06080c0a031212110711060307091a07172a0a0305090409 68
    0x79070a40c0403000840880c00c17143c1c80300d540212502600da60041d00314807000303280d0100d200307100d05501840d03003c64800d0801891070400040310100b01c032694131141c2c0b060000018400c1041d030a000e13a0400c0b03000413580380b0303082d450701c1c00310381d030a07002c041100340b20700d1104511400716882a00980c103141501002171215060000400e4028111440300303c1c031440004500003200341c010399000b1010040500039140390303006841401100c1c1e00c11103049031900b00400030760107103c14034882d039254001d0040590f100c031000e222041c01219080d80119145501808481c45203503200400e8100780ca601c6145a41051560302c01501c009605a0001300118104041c044164101c200600f003254017840c4949125a010014440140300c203540040c0001c80c0e804081c00300304240820182c42c441c0b079090351841c14650b929411035507118441c05001401000503010740d510340c617030700a114480e214107220f200c1c0741405c0b811955541140c40001d081c000085103140e11a6540c0e4030081103580c110301020301c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 699123219 1250 699121969 699121999
    0x4080d1104030b180609061906120308070e0301140c0a0c1709041a011b0c080709050f0105100c060f0b0d0501020a0f050c0d120612121409010c0b0601020a02 69
    0x210103007100c1080d10000c0d0f03011362840e080d500207292401944d0000203400c0c0c0da1108651110f82650f54841c1030480c07500c2d2400080c014503400a41c160960090745c07220200c0c10600301c0140300e000d0b20128035200740e0600e0f22852184900440198100903855812a640c0507014000c0e00c01a0807080b0113440944102d9070120702c001c1100c000c0c5115102101c04000e140302c05549000c0c0c00900300002d030300094010344540c0005012807501c4030a5070144001940c15a9110f82940c6081c0d4540c2202160b15215030034000301c4031451260030301400c8100c4a03419215101000240b81c2c7c01c04600150030181c40359402e400007400b9602c024034002000d824440190700074100340340130754400d040180010344002504214203214105070f0b18010740003401703040c210300c1c0e020301200c0544420030004038855690304002846e01d075900c0c150701c0c03092050380071a0481c49032182c09000d9403c40700034070019040403c080314040e030740f080e4409840395120460200c41d03192000100d01e828140c40e40290020f142429120b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 699124469 1250 699123219 699123233
    0x7091703251a0403030b030703030801182405150a0f18080105040f0302100c02060a02130b0301080703050d050703051b0c090f010906060509030a0b060112110d060b1204080d110403 79
    0xc403c0d40a0380342032002820700410315548160f9480050002803c000050116283c483c0b041591111254008210060300c400396120104600f4840d000040305614200200d0400c50480399070085c00082e56800d1840084010300041c00c003080000411a05103140d8080c140d011060390003a0860f0130003007015203071038641521003404035a81500076124088032045001898050f001c1180344690240000703844100e0000c0103074101015800c0316203542c0101265802d4031002540c024281c0100510300c0d1440d60810364203002c549042081040410000d00000c81d4201040315450004152050034011000e03016a081410402005a001c0d80700400d10800c0d0a040040c3c6042c1d440703010040000e590744a00070f440a10030700e2410358154100f03002c440f01040c072840a40c4c0d484901030400020317190104601c0e0b07040352058010045d20300c070007180b038010415440c4a072801500503407120314a81003000c2c00c00c0c49640c00060005090700000035081c94900b00710303085902110220b80000b034a80ba1a4507000d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 699125719 1250 699124469 699124471
    0x50a050c0a0b31030f0b06120f190f1b0e0903160b0403141c0c080103050c041a1503010305010f09150b0a03020a060807091703251a 58
    0x90320035401c400c1c000c40c10310203001c102da000090300c040d0380707840043c00c0c5811052040c40450103402d203030703040c83c1c0000032a074103500454a207031080080c84168906001080302c1c620b0700d44c021010903032040300100c031403070000211100c00840303850a001d058441444c0c6401c60980701c500c010008480100306a013540c0b18000600103807910060400350a5440c4c410f040e03a039004d600c505880680c01b0124610102c0d03114032200342c2145c00380c64642c450003401042d0950542c0908482e8002400340640c601e10b03040c01f84104c25051000340b8000300554550388503141d465401403141449280d81c0c01c402200c071110310910444074000604081200c05103002c1440107500244801e9406500f407010000031080b00748150285241d111001121080d2a03c00c184018a64101104d411048401c0c0c00b0000d60348801022005091681e200500c91400c014010414804e80e4814000c20740222444d85001c1004001c0d240f4030450404d405a4200c000c481d903102c1c4c4107107124050040050cc003110580303a001c0328811 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 699126969 1250 699125719 699125743
    0x141c020d051803090f0405181f0e010504080a050a180f14030705061c23060f241c0e060103050d050309030901030b0102031c0b010e010c110103020a02030403050a05 72
    0x40000c000b200340350700c0c1d120f009012079101ca004104103081e0305d4598000b6400041041c1c03841d0300045850310b1140760a20041ca80c07160100700d0009141000074901901d150504410000e0216061540d100c000900a40c100308052000101e42030510b175101d06031510840c44000c0103480080e0365400c030b4003018040e901480c42d03ca842080841e0b09420002445c0d41100c0000e0401d504e030000c05200c80003040c5520500b0307407000b0b884045114200c0c450418820441d4103140c0000854282841001003c8148101c03060142141e0504590200102c03001c4001400100d146c05541c7d0117241941007017501081d0b8101d00c2145040c10b0050030003000030307a01e4140d0380709600300c8031360040a90054649001c101d4064181c0d030701c02c002d25400d951003500403018895040c01240d0500c2c03c0d80704060500c044c020a15817031a1fa8400001c82c02c0d60344124502c14040081c2800302d00c1c4030143d241d8501d800004c101e06414180c00080d1f4450262081080f9001143c014099500c1d403d5949006d0b91103c50511f00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 699128219 1250 699126969 699126991
    0x603080d0606020610210f03030609230f0604061a0c07080703050d031806020315010905040b0a0e04020d02090a06080c0a050f0405100b07050f0105100303141c020d05 73
    0x1012400034000148240601100350707045c0c010514244c140500c2a410890010442404408200c0090600d6040f0038031603110f906c000c50003504010890088440340c5a107044d0421040044031640c0c080c51814640044800c5500c80036540e554021801402c41369000d900800f03143c84168520b03000010107895480c83e03d005a9a407566241c50451f0758030918003001e002c076080541808004c80c003a0744104d1040e07080703104c00c0c80182000d840e108100d03001150b00f80300540300e0b00c000d04007560b0312550003806804121003c0006d06942004112190064000c5e40103140c0c0100104055603180401e00c1c0030140c3c028800815880c0015003007000d4044c504c18665603115200101c83d06260170001d42e01501d0014060b0341213003415034200030145c60080c0030300505d810750714000b150b400545401041c03800c0c000d4004090818030181d0041c00c444000700191000084c0070710510000342c9c0043d51070254005904010348510528401081030050800341207500761001a0081590b0100d4000314403c0302c8a41f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 699129469 1250 699128219 699128231
    0x3005090c030f03030a090c09020a02100605060301060903260a0f0e030d12150503030d060806151c050111040f142b050c04020c0a1707080306090601030905010603080d 73
    0x4245a038072801180359100941090000648885c40c80d4042081c290080b207100301c0144e91800c085040360300c002035500058201a1508014403000d000b407074001c080035a0b00600c0d640c03400c0002002c1503418000103081c1079000702840041308031902d0100ca09080c41402e641d941c4502040078000080b00780b41040401c6125190b111186404210003c81c00a10b0311036095560f040c014a40040017901d02901c00802992404952510b007000a0300079445c2c00400001c2030703418111020319151000b00828600c20800c18145841e40344d41c0325030710000c80c400889131002070441c0f51040c0905400450401c40c4c200c0410300260048054009100f2982c5200e0301400100c000028402034000c4000d800e50004240541c1030980f03808541ea412100f801502541d01c445039400004099038840c1c2d0710015254002040c100a01104914181440f030120256a1401400381c0d510b12150100800c20f42c815010a000036420b82d000c1d80169840b940d100d03000300003560f02c0f86440101c54124012003180249000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 699130719 1250 699129469 699129493
    0x4051206070f0507050a050a0b071b020609190b0d0603031b02013e1006080f0606040506040e06040c1a090114130f06050c0c04061203300509 62
    0x464450302803200c9a55514445107031202c00d90305507000400403640c511501c00000003282c002d1044c054407512038100c3d108a41810300009110f21410740d98400820920300000300140d40d00320484600e0f602c29110140700c088646240d111507900780e8000002c00100085840d400c8443e940650b05036403180d01d0307450000c842c0482c0c20b1841540040021b000c01d404039549e10910660751020307410450441030b030041845200755800a02e060140c3d00c03210b5075003e1100c880d40680380e809120050102c001c02065500e0445c00031598501c0d002d401c0b68019592900450900e0f00d80d900140c5406000d101205d0003400d05151041c075404e51031058a0a03001e20000080c20703411440100d07450104143c0d6043d150b80002034190361590311a03d808a00760340301c113000044242c880000f8000402d51900c8807a1120040200581005084c00d1141d22542c9400e2041c02008541d941c00350780c40741c05140420601342c60702ca002640c02064000c03c003111182c04c40a80c0450015000300d0b10031288441034038040d03003901c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 699131969 1250 699130719 699130723
    0x121c0e090c180d0606050301020a0504030c05060708040303050c0304030f080702040b09150f131d0d2f100e0307150626030403020a2c060307120201020309060f040512 73
    0x600710b200252000c50b010218503c0d008003c00100d07800b806000420303541e2040000c1c2241c2c072203102000803600100e410801e1010380c1450500401d01521001e1a08070b96a5070b00690f441907000040912001054106424000b08180e50203036034042c280074071038911824080242d82082604902c580d0800300356021a007850f1580600034180418904440e0190100b00540600d206d051b44e50024052003a0100e260600e000303105040c041e042951040b41d51000c0510700300b0540103490020b01103003280c2000c030481140846c0c2003606030f012808079501848007402d0b042070320f4242c1c000e204900303091440d00080300200c010304100e44644142c1920440c4400210280c8110340301351070303112400c082a040e01c039100b80d030518400010a0252482c10f61203600081614000750000c00c2041d00480d0304504200d400e00c48100c804901d2401a1020b15010300005d550b1010b0b80610500240c595031003504590080081d6030140c03100428058039520504000101a08103100c0d0620501841800f20012000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 699133219 1250 699131969 699131977
    0x4050a090b060d0506072019052b0f0c06140f0a020325050c060c090a08070803030f0705040e0112140105130206160b24060315190503030a1d10090302121c0e090c 71
    0x10b07040c0c103404ae04a500d40588030101c500000c18180105100c044000401a2103901120200c032206c0101e0303402e1240505000c80720050280c59410b10410500031001e40c480d000d0f105000c5612544031010342c04540c01c89890180c00102c0c015841501c0c107101c00714045001038809908181d80c005ca446581d403400654400b034a1141402542003080440c1da210340761a0005ea10146070f0820903e46507548082c2200003c0076030060a220560680c0c041c00c00203245900300c81d4141d44402407007541440c02071014140f8082c200244100e400040047d035a0801c0700741d0354103441e0400e092a900d8600511440c0b8582c041c0da180150061191201c6c0075149003103c203a81c019200d0354600f82081040034107000f40c031040c50060070344d40808002c00145995040009000c0c810f02c2d070f074440d0605468040d080c9079160b00c86984c28800c80342e2245001d412544440d1400403250100d9034100d00004281c4141e080070440364508072014400c4610750155904540d844450040c250340100c0e4907658540800c02c2c44c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 699134469 1250 699133219 699133273
    0x19050c010c08091b0901032a0e07030606080c03060f010e120105040b0a060303050d02070609020a1e1401020c06030a14090a03020d030b091603060504050a090b060d050607201905 78
    0x1c1700401440032865200300f10102c3c55040c440d252078050244000c52a0940316486003501207091410851a035a050003a20f00500090520300951300f001d00c540d1020707000003070146000b540d8107544038941c1d0384034002108550801070402c0304000000c1050303502a181c1240c1c00d9400769000700c0402c03500382d00d600c100c0c41180c0e01940c84500700701c42074000d06d01035072243d0000e0302d410b5103594800e00560707109041c1c070000705840000780c44050240301071440303001110751152079202e152200700c01c1e07240d0300070456042c2d8400481c0e40f240d0380d60340d4690440c010081e50a80021104000040207004880041c0a031492400382d000c0701d001d50400c5104800f90342c488000d55410a90b40000701c1d849034030381070b0120030070340c41418013040c2e01c3c0c1c482002c01c0440b501240d017000c02e69202c844010901403c491487c1c3c01240c240c801511818645d12099641c00003e0031034403c04c526405502418908d5112040307181001e08141c1e10060468000345030048644c905c02d466070f00a4900021b040c145258640b24484 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 699135719 1250 699134469 699134479
    0x130c0509070c0201230a030b2403060103090c0306091118010f0509060607171c09080f07050313150318020a180f11040e071419050c010c08091b 63
    0x61941e500440740c5d80b4140000b005901c4518580c4204100200c010b0101c81c85195000900744400c1d001f0844a03006d140003900c0000c6003858100804040c1e441100da1015007800c011447c052180307052034003910243d1000e000180303424001c03002c0000802c8a203003900c40485642e185440c6100c02c0140c051800c0c0301d004041c05907204104001c1c00d100d1001c690000e802440a414844240c88110100400314030129800d280003c0400e040640308003503040685001c0c004005140300ca5031141c40600c1058645041404003042502c2040410401c84800310115030407240b4003562034400c19865030440d800000400d00f80000102c0c2d035815820100c08258004100465a40c0740038034110403035800711940c0410b00d4a9505202140345c4501404491074040d61840da50341b4904840101e0004000c3d00398010800d49900c600d00f0746000c03400742e40c0c203002000d8004ca610300c0800000d881910454447c0082542000700c13041026400004180c07041e415502550640c03200d0180d002c0c8000d0040036030907446 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 699136969 1250 699135719 699135737
    0x20d0501050909071505190915020f190204020f0a03020d200a0c05210405090a050702060411060403020907180e0712020c070305070e0406140402132003130c050907 72
    0x800b200d8503060741c00000504095280c11a01f080b154410315400d1118070101c0d801040802944071202014540c280320362002c0d012007032075601e0304d60310780c050850319800114001d880072055584a44c1151546190b484c41c56554992815021f40a50808118101c0765441c000500b035100d5202e801040c0307a904210301c40c07443c1000b10308040e500000200c80035a035a00c107400e03210411030744981d55140c141c0e001112458640d49020100705026900402c03240d61b0b2400d150034000034907000104160803642c40042c00c0c0d111706c50140462001d0141743d0018dd441040181440300d06604200d82503021010780010035425911200501e589a00c140d401c034002884001000440000560203030141151400a803140c0650f66216145066806c0d08107441d540202030030301081140620428242114240000c000e61401d83c002400d903000c2c110031000ca40391202c1401003a00d0326200055042048144101e4680c2444200400320710010401100d44030480080401c1910b00002d84030303c20001641d42503c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 699138219 1250 699136969 699136979
    0x1501090207030c0506180118020312031306060f051e06040b07020d020a09020909220b0403051308011a01080c030a022a100b091312021006030501020d050105090907 72
    0xa41c060081503003080114145600014020701001c0e0044d0071100419079010740040403d400c48118041003a001045003149000588011940032114102030054070340369611100300400e40c0045800c0280418074290000ca10601080085800d88600342c032007004a02070001112031900d441c0603400d60107001404104031407c10b090080c41e85906c054007411a00c4074550102e0400e09164102c50012500801e41404505101c3c0805504c00c000d09001c5130540b60107182d003034580880301000707072000c040e090024062500440c01c8600074224641c1b0304040d00d5441c0340d454000c03c0c10140d042550026401c90101d11362250f01c030140201c910441051239522843c0b9001e00941c4500b40c440080c220440c031982c80d41c00c5007a404144152003201a00c1c041c109054000704031001180c405100b101d0110038443d82003056940f00205a0344201c0001074885104420389c07410344600c1c40c8405c1181440d00210800006402038000c150150501780000c0e41c0b42c0c010040c08010449080503150f00440c0c1c06c201c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 699139469 1250 699138219 699138221
    0x3011e0203180a080a08250503040f050f0d0207090b090c0c120a080a0b04090308070305060a050a03030c050c01030b060f1312050102121b1b070807170f150109 70
    0x24115100040b81501e840a100c00b242c1819807074142900c0d0004086480c0c204a03030000b80c21640083c1003c40902c0562039840520b48003440f0380451000c02401000003803c10222019001100e500b00044540104549051a03958000e00c07542000600504000290a025501402a00150040038203025903510307850f64015804c41c01ca00940e0744a500030816400600d84001c00314510f0ba65142ca031603181ca002c06106489620381034a016a00c4c00b20303800301003a80b02e01200d170446c941d441d0100709611002c00066011103e138218550140180c2c10000801d5000303035139041154812019180030040c1707103005500311010320407050341100c410400084492485c500404009440000c050310a41d195400c41c401d0801400c42200c85a50010756200c00340070180626034000d1182580000302c81c003d0b06d0305540d034002e02225041c2080d4400b401c00400c2000d01c02807010303268040484804a50f2050303009181c010301c9996030100d0140782204105207002081d9411006c001003000065070b440c0c86c00180c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 699140719 1250 699139469 699139471
    0xc15040501060f0f062c0f03100c0224040305041a0d0f0f050a330504020c070e09060105031e0102070c060f020d050304021804050a060603030804030e03011e0203 71
    0x80d155582c40d400403820000e900c03120005400b0036160300d000c0d60300b422400f5119111104c2c40904449203248078243c0b120154451030345000c815a540d495990807000480e150424140c40040107a0030300d43c64a242d07a50005071404155006504517842c00104810032303180c01016900035001510420091040d5003103007002401680c01c14200a02e0000c0080007a800c45554031245580380c0d0300e4050792180002d01d40142908084401000c02038034684224005440c0034005000440d41800b20481c5900c95090703500400030070f80a041503545000440d00541c0b966503501034403007408681c202083e030110001880605982c80a4001c101c200d00c0d03c0354050f803d408003408002c40d59000c0080200185070842c0c0ca4004003201d84906010802c0660013038185010700121a0803c84280200310260b603401007200c200001e02c00c03c0c00c455441c0c9041603030503c08a5071002e80f046017442d0001082560001c03000b44501d010b5074440b031800e4842020503081c0c820085000c0409107959041528070f0100c2d50042d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 699141969 1250 699140719 699140723
    0x40311041d061608011d1609030b040b0f07051608090a0803070c0e07050a05090d0f020901122013110d2a050901050a03150f030b090c0301020c1504 65
    0x81d202004210103903107403107801c56108148036040ca241204182d00460010701403c1c2520881c4001c04204c0040c0e100e8110041c40b07500042ca0b0b0b0040c065034103028500c80780240d600100071404510342414820300302001941c4c02aa158081c800107003d491244044e074005104d100881210440103449442c4942c102c3d6454035400454041d0000c0c0f00d1104000502c0301c20300c64419207001900c0c0184440b181c0300000d21000c1400740c2002100d41043d8454211540da210031075046d0a0450b071428105400d4503001c10080d040304070500080742c5081c0e05c04440d040144180c0c903031000c03900a0009042c03020102e50070030340c100101580119080f4400d401001142000c0c0342040d003000b43c0800c1900c2a600755444005402c10150700c4840c0650301300041c44c02c2c980440c280645804031090000307025103c0d14468104155440c04e28244181304020f40100800001500440207500c90804181e2464140c03866140c41c03080da21081003034101030080e00c184585100c0980114114002c1c0388403070303420091013 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 699143219 1250 699141969 699142001
    0x1917030c210406240e2e090e030406090b03062b05061303051909030501090c06020c040504050601090902010e0910080f0610050402220e0a060b04031104 67
    0x1001220701003007100303440012554010003058102820701004440c0390222005660030500c03030140745a107036083d6800840d000e150b004d40b92540c034244050480144103111002010140a080f007551808500940513180310b94400c01241c01440c9043d65a841341b80b00303541c080350403161b0030454100c9160195500c600003501d415254801c20414204c80c181a0084600305500601088107018007003142503031000044040d0420100300e0340b006440e5000d02c0318007071071007419002011001c5200d100004001d6038080000d11603201c480ca0300042408090103884014850100c1c845800d00e00350092074041d40d0003070040c011690030510210042c1c42c0048043c0e041c82441c1e01800a65100d00311702c1403003007003030300c0341000014103002c00d480c10300c200807001c182a0387c002c4060203901002c4880001c1281c804480040c6e86080a90b0344542e401d085400c03000790329060b9030000400e020350b6150b581c0301d40c440600810000c5c0e21241408614015800082d0040e0500090560541403c0c2d10a201411804030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 699144469 1250 699143219 699143227
    0x20705030d060303050c010e0316020d1712160201020a200a02130e011107151802040f0608010c1407081b070902180a0e04110120060103051917030c 65
    0x128007040e2030040c1d00880000d00f00242d0355010000a110310442403021f44051407801c110240f00d40031007500c00d0310282c0301d010041c08400c104034a00302c03254505a148e610040c4c6401b100382420031920700442d283c01040080e840c807907a09901c103108132020104940c40d207000c40c20710714607144c1c80300702c1a241c0554503100354800c840c00750350b070302c0e0030300e0f401e9074001901060304800c842c2c48900750350b00d02e2040003900909000c000300150040e20002410401d00e500000e10507a12648040c0d0315030301c118040d420524084a41e2002c01d441c7d00110241e032a078100a210b41c444032002140c03400314100c0402c5c0c10303a0003404070400145e81310b401040400c008031b20b400019010b22204608044141c1d1104103800da002684d084c013062004140c52003504100c600c58602841e0501d85420a080184010001d00b042202c841181c6c0c09003880715140002d00102807110f40c203035041c03c1c0d40e802d802e00040d10188a00711441380500301c4d0116140446034020103c40c010b00940c0303001e0000b03402c0a4050090428140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 699145719 1250 699144469 699144487
    0xb0f09070906240c0c0b03060105120c0c0c0307080a17040f0803040905130803070c05120c0c0111010603030504061b082a0c06160f061a01110705090a02070503 70
    0x10148601034030700c6034240b11092850607501d00e43e0208000301901404007400300c00c0701143c000e20441d4112851003284a54982da0140100d0b0b0501c199034100c05520440c105100f854400305006d003284d40da407041160f82402c164000c0541e201114400c0b103015500842c503410000b04083d4062010300c0c0d0f0600d01c54149921507080c1350300081250000042c40d032000c034040103400001c0c01410f40248441001d91031b2040a82c4484e112403000a112000344651804840108a82001080380b0014000e41103500c4901c0c4210340ba440c1c1030103010044c00203400150803001c1c68011711884085076450780300d49181914244c030079207806450907030300c280c05e104038144030b00401d000b0001048100f01d100c03003260078200002d07030708401b40303011108203a0543e01079155079046498440032a0110150b442e04030030a042c5a1070a40200050401b00074103141c00d0240005480600000c1c5188581e4241c17281c440e00d107207208506903200d52900c07996a1000802c000b00701100384070340c01808282e0080060324036005c201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 699146969 1250 699145719 699145721
    0x30d0c020c03070806070801090e100522080a0212030903040312090812030f010b0a0c02040f1d010b090c0a0c0f06240302010f1704020418020306010311030606010306030b0f090709 79
    0x40c0d4011300b2550003100030000b006a0081c5002d001d04a0340d8010403800c0100140503941c1c40c0b40d61565800c280c1d841020840c0c06151800002d6441c140c851032001c195064900b0496507000850303d44054483c031580b1850140d608416a0320608401008600301440d50720340110701d6070118010010b01c1240003010452490a20544000b41d2805140c90307030381e0400d03000d801c000d0b000583c4079100c002d60600c803200a0a500040b402001e54040720049841294407152034018280000003540310040002e03c00b00143c1c040d0080300c410142184c2c00700c041c5d80d0b0707076038564003e20441200e2800500d8030350385480003503140c440c1120f040d07000b850002a0342e4040c252014403d1014062a010482071503c200110342c0e001d540e0020390301103440d241040c1622000c04842090300540000d20650f01c8080030b04040c00f0584d940100755030003c046034155656403c109500b03182d4003da03107011f8018107000906a5000340201d40881c1c3d8490980700260b519544106186080613084815034007600100250342100307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 699148219 1250 699146969 699146983
    0x109030b0c091203131d06060d0f110703020f060a051605030a140f15150913140c071505010b03060906040f15051e0a0515070c0b0702030f0708030d0c020c03 69
    0x9031140c0900504d0600c1c2894100b007100801b26800b80c036804003003040c01d0b105c0d0700030380c0c42001c1c45100104541e14020b08203805491901480c14081d40086141814940e0001e140008210340d5010347e2016103510b03414000f640c6040310013140f0040000c2d81448014031800085038051000350000503030910b8200d032107501c0305050310b002c49142c03c141705100003921003443d4003503d00d004440320340700300011041900700b43c000c8403565840350315814040341d550b10380c0e5001807895400000000c103462404001d51040d0340c0010005480102c00140c01000418031840380038182c800c000b82c01815030392540e040128000006003040d07042a282d6416840b250034900914100906600580b8040d605204c20305c030001d0045490f0102060215240c4645a1a5000e449040d10016a010350340d42c103003070181a0711031084000003082105072101c0061540303c140c01400d40640708030180d8422000c0d8542e4140d403030790740d03000c0c050280e0401c01185e0704900311980526685655030044d5059030644800007810840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 699149469 1250 699148219 699148237
    0x92a2102030405100509070512030d06080d1b050303161e0201020306120105011a07080f030a15060507050c04020903010b0306010b03220503030c18100e01020c0109030b0c091203 78
    0xd0048103220800005000900f461010741100704007614000908075510345407403244c94081d0600c2072465050755400d0080341c840358140c207010f0003c0c541c2c40c0240ca41e204058602a40000c1014402e921440c8080c885000c080c3d41141c010760460319140382c0003802007001c1480c0818400318030085400312016480c8560f039201140c00040c0c40c0c0ca810018007583d201d50403405803450345000014030850a80340d1440c9651001c1135003154648107945030000c85c42c8510002400003071000701c104000845107800200c860b244800002c0c00513035441c1800c0c2e4441c02004401020b03500141102c4001c0c0c1090b0380541031105000b00042944c4400402107800c1c150280c020050000c8004204030380d0905441600700c00c004658011505005181c64842d102e000c041c1918500c2c0b400000e850760010050500c000703000300300030a0891aa0000d1002409221804006030301600030030640c5206507028042ca803044036040315001115650700c81031070f0541d5210308941e0b5400004c1c002038121a02e020001b4201c2c00d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 699150719 1250 699149469 699149471
    0x6091909140f0a0b011a0715200c07030602031b0310030201090b0721140d0b0405060d031b02210d03360206210103150b0f06030601031e0c09092a21 65
    0x1c09c600b20786440100280c000c1e20010310042003281d450750400184c500031070703801c01c07401a260b4484000d4070502050880031072020b071801000740040c03600c1031402c000c2124401d1701c1e501012551503030075a60b24020707560041c090180c1d00d13500c2c2400320284c201d100c40d81c001d41e10704000c0c06c50a5064110300e54000a20785509280c0d60b030003401d4903090911949400c0700044503d945480784580d4004e040100000c6a40d4801d11018006002c5403030f0b040308800d4802030b280c1c0304022890780150319980c80c8544a24400040d007401c1440300c8020640507001d0402c200007521000740b00941900e405c08400d490001c0f40c00410400000209058212004803499008001004254514108861b0020001c04941d440b04c1ca00018a2010360b20b81c052507032010301c01d46110352282d031602c0c01030b8003c1019003201001c11386090241e0002ea070841e40202618280c80c1c94420442d61645180c070222503400401011081703003c0e03a4814802e121400f5a4280c01fa280303816075443d540405c0d003507440c03842010106111 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 699151969 1250 699150719 699150731
    0x1080706022413020306240307120807060905010504030f18031e0807051b010909020a08070e0d0209250c020d2616140d0806091909140f0a0b011a0715 66
    0x141014414401a200c0120012720ba107074100300e44001000074444008055030800901041000030f150805c10125070004000c005501d03050070082d010b84450b0880300700180c074180780e0900040070300b4200c1c2c0a0701d4008040030503d900a49240030741007a5040203490b58a42800000e001810800c18900b40c0d441415661624014840003d44600455003240d40303040e0040c0400c00c40b8640c007409031a400b46040c5130151a040f40400410100624414081c0d000072041040101c100c100b00c1c1d05c00d80d400c560340302c024210380e00a0000c03611a0f40a44009520059860320f050200752080b01c00420801d0340c01c015031083c03200ba0b080340c009900801c40e42400e1310781b01c0c210074140810071084450b8940394401810006404403030043c0302000c002c182038429204000460542c203580c010404040440d050104580300d0395044c01040d607411500d4180c2d0a102d1480070316108480401c04074611607105c00c8040d1640d09107000300620750300d40c0c80100d201c100d0501200300810700ca041d03100e030340c84c4200b0000600307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 699153219 1250 699151969 699152011
    0x2070501023103050c09220606030213060501080a02250b0118060806280204090209090919030509180a1a120c0909010209090f01080706022413020306 66
    0x42c6240e01101480e24407500c1040000c64000b041c0c90400c414205c030b09404980d980e82c82898840c1c415144d1041240d030b10b021030380c03c20440340e01c014203a178001c84016102c0000c003c03031807007503171244e02445001500100203d8400c0e1074940180c4803a02000d0704840d07581c4e80c990700407480c44000380d0040d104406400c00400c0b10306442d2540740080324a0100a02c001c1e4200010b855031840c1c0500201c6030f45200c2c020254298400d2030341003507180b90800c1c09550f69907488031010084d412010405200d11900004906801c40c00034580400d40c0350b000300c550f10400039442c142c505400c07082080f5040817800d00400314451a800381d042c46100d040350001500032994044003650860380c89124001e40f0a9030b0200c00e11400002d00a031032150448a016059442e108050b0180c0100710b03071517400640c254144144040c0c0e01d10068141c525032412222840d540d124100d0b9180341c0029907843d202d80003854055191141020b0a40c0710b01403541d806084c500590101c2c0c5810700445030014034031041c0e0a5514 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 699154469 1250 699153219 699153277
    0x21c030c03081f1e0806010b0406140c0601180204150309060e01050c04150302040b070f03081005010e040509010b030f03090f0108060a260d0201020433080603010207050102 76
    0xe00070443d2003030440200c0c06020b070258110400c2c0204044d498001c04010401003c1a0345040546041025074101b941d6644089031b0b180c0160044a0125404e9102d0307401c460311040680745800203200c000c0c170f241d9203006040c0140781840041c3c461503075020000822880c0b000c0c4441c040c400003907640014401c00504002c2c2c100d6129107002d240c0e03030341042c05204050203100300b6101652030b5a800024034800c1c0304420360080c8510791044c8800360001c80c4034001d005100c3c908011107130103610b5559042d030300e0106120180c1028003820340030600c03a040280150606034040c81c0c0c40300d030301c000008034103c2140c002854038204030aa041107034800501d00303440f414510400100e860003820680c0450414000040c01c03901c80e8043c83e500100da0403803216030011a200da01c1c1c0b108450303009845081342e41c400028082e500501585c2c000307503074030403c95154052840b40183d940701151000c190042e0859011200c2c1000a48025890341d0240b0034440031030000e100600c045407450160450b924100d041140c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 699155719 1250 699154469 699154471
    0x16030212040e180309150307020c040603080a140322020112090b041b030201021c1806021b01050705030d0504110402041409072a0302070e0a020a0815100c021c030c0308 74
    0xc040d001845a10f010346c403440d03200300c02841c0c010000c03501c0742c0d2580c0080b0724082c1d0f41c4038140d500c58140300c4000b0510000c1e4004104c200200d55031805907440c481c041400e984400d458649214030320903920b0b80517004100720308885510500d440301e1310406076840c1c42c00365a10100300395411050346081c0010003800c071142504842c00c803502c0e41d0080b483d41c1c001035198400d0180b420341c042800b4010b03288140c4900d51b91003003000803030713030202c016516490000d5031040d504200410341e43c259062034105e51301138415214890752250013075150181030401e8802511014008903603c004441c0c0703080155440f40040d10140041c4100b46052041e070104200003844080c10745400d200750072400480221092280009800d03a000c100c0408618501e003c072301d01070881d406821030818420a00200041c5c81d0001c000421035230b528500703213484040400d254000005201d40c0c0c031004007400d0700302d00d0b4020407405d40c2d01c5000901d00d02c42c1380703011024091105003045046001403801003049040541007001d039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 699156969 1250 699155719 699155761
    0x18190c0e0f0906060f0313170304050105010503150106030e070510020f16030314071106180102011b0f0f021f020c0607030b03030d0e0a12081506030c16030212040e 72
    0x80b0302e00742800800326105204580001040c00c0300040001d445944500c100000c6590100d101c0318030346081460040c280d00203513030469841d420080000f441e40350000e00a20461849075080503541d103000c40c16001880360289001aa00800700000f8085c3d86030800780c1000c0d03506801810440c1c1174114100d08180003400e5600c6000c0ca0b04e4000cfc0301080e84800f5800d00810440310440d43c0d01c1043c02e2213101840c4681c541a400280040d40d0540340211603010070300c16200380c00074000700030b40103a12781e1112888a030707900002d40d4803e00c1c8810648100340c60707000c5540d1801910031040c8c0c980c0d030702040c1154050104031200e070005a20150010308004082d032162961508004401011000036101e01ca014411070300d00303480d0b00168030745850511002034010303400b01030704403404040c42c00908078a50841e02c14440380300b07018a40055081072401c8a104401a1440a20b007500301e040440505500003400e82c21807143e05840c02d10710040000034006441000c4441060b45044503101a401d10480c01d0b03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 699158219 1250 699156969 699156979
    0x5271c0e091810020c0a060c1b0f060e0a020f19030512040806011a0d0c090e0f0402011b020109030f03090f060503150d020d0308061201320618190c0e0f 67
    0x500c5c103d500e004180d03100c1e415401400031030603180700f800840c0c983d61048242c401b1190404a8401000910002400d030580b042205000c2c01d00320804840d00c4254120002c3d400920721071605d100c3e45010060410444541c050044282d9103d44409107011384281d00a0280200002c0500c843c910800825006191480b20244908401c102c91070540c0100c903501540c540c1c540b0f9000307020038001c0e02003101800950703482e02ca0174544004201c05038403064600b6030200d42c00311400c01c00d518103103a8112030603806840c0ca1402c240307160b44940e0340718042e0109800f0880e1001c070100342c8074880c00c5001c00820491360b41580700d082c00b20001d20320b4402c59031090f1040c842d003102030303006880e14a54840710340c1d05800e080d03806e513581c1000300701d28032034504000110754a0300000840c85142c40c1c00e41c410703101c1140002440b0f01d9410b60b031001001425510b45602491500c2060051014072003082e5100c01c900821118051901002905071030464404078040703141404c400c503030341c10401040049411b045803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 699159469 1250 699158219 699158227
    0xe06010504030b07210f0501090213030f0510020f19080f0a051003060222170729030117150103031b080c0f0105271c0e09181002 57
    0x40080c045100d80d200040c80510b40c640080c5003e4002c12251034a4403802c201d2110f500d58019250004201e0410b03001c10841c81c2030004107105030584203940407551032040002d09181940c66103100c2c001800710443d51403241c00c49440b8644d0b0280060445192003c241c16152645801001420b495681002c01040498410031440014003220a0740000c2c0c80310000601d61074801418068420307640020300700030b000003580d01c460b800b08480420303a100700c002c2e980c080e5500c5800c03005908405180d403445179407011405010352690206010b0644030100b1000d0300100380780b4005512074000340c0c8900c0701070081080e44030800505025042488603900205000d646c116035025099213644039a00d00100c140c000d02e0420890100121002c600c1001d017142c0c9217458109549029181c21100501d0714000c0140340d0202000c8191040050a20200944803011680001c5514241000303400010014040740e41c1c6ca0b5621940e82e158010296150302000404100c0c1c44203150150321105080181e03c100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 699160719 1250 699159469 699159481
    0xd09050f03070f420605040603261b0604030e060c0d0f0207050307030606090c0f09030213020918010608090c180606040305060f010f0e0613050619030506060a0e 71
    0x111907200340341e41c4801300034004c0310800d100c008403101c4e00b070100100f044070444201d0504004160b99030b580000e04010310003241c03540d00717010039a80740384002031299a0111a26100385d464003418151040407440070f034105600c0e0380c18180400016030f0004043d400c903105010031301d58410000d00b01c8a0050740c00500d403104001c40160740c3c1d24000340c04802c0040f42540211854803c0c010f242c0144401012903640f10b4680c20420020a04c03881101300d2180781c11800d00d911402840c4d81681d0003099110405e10311711b5038080c82514161100780c0e0204a40c20400c039407050b5110714000701c5010341c61100118643c100f401c041c0900b140603240410f154850a060ba40b6aa20508882494050241c0210403925990701160070307030040343c0000f092800350600308911080e502c0e01060407510302c2c000f006002541d6600006400701e0980703c054005a00800c100000b50541c0c0103160400d001504401e90801070b64189011a03c541e04200c900350405014010146461145e6102402d001e21055004c2d0403c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 699161969 1250 699160719 699160733
    0x3060c0a090906060e0d0302030408150a061703030711010b13140705043b01061805190b03181f0b0306060901060c05010e010c09060f020d0906120b060d09050f0307 72
    0x10541c19110391b6502c1c40b4030040600c01d009860003001c610301100c0d0f8001845401c5031050030200c544072100c0b40b80ca03400140c1c5441d041a06007240d0301040103940b558841c41411202007a81d020840f010390349800381040561120000000580425207002031030502101d06000b6020000d0004420080706000900205000e6500111040301101410070020510b50000108100740b540d00070454036440d000040042e00000754002c4158807203c686500c039180d4041200b00302c0b80d00f80e4018000032119061143c1d43c1c1c0d1600a540000e007221850071520108000d0307619128004024811030141d0309171244120040340126040d00008170041c0050b490004041041034105118000400000311143c0061001c00c3d0710900d108000540240146072114074003414480c114400d0200080d198031440c10300c584007040400001c0740719541c9031099864140100c0e440311400c0c00c0c1070342565650880740411b6a50304000c0c480000c04010100d5101c1150400c142810056018180c4540040050074001411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 699163219 1250 699161969 699161987
    0x3110405060c12040806010f09090803010509190e0f0106060507050c01050310090c0807110114010308030705040e01260d0f030f06120f050705040c0804120e03060c0a09090606 77
    0x80d40e680361203200095140e071030501ea01100f08111000020045102d030b002245050580703000c0000e050000d070380c0b4001c0f0000c07103a69031400b900400c1c003030005100c40d14251030320a4120b00900d8031034074405400c00400c0c040781c1c4100a095056031014080e034901020078042c08000b04014244242040304c5900d8098850320b10080365810000b000000500003155a040080580074441042040c03000d51040030708400426101880490700803440c440306040305005580d100c440500100041d80d10350758600c14103800142604040c08400c2c080801d1003d0b40b1400b00b4001c1100c03940317152003071916039030307490220301c050f105204207030005096600c80d10341156418107030080c6462300003000c1d03e81e4040c0314014403041e000740e081c002c1800c2400050080b904445440c0e01d000c0d0098070421640c4608020468150750952000b05207040c0008000c9168545000c01801d0b003414000319590340c010009051041c211108080004042056140c00e075001c6228800f4162560041008505100024000044c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 699164469 1250 699163219 699163229
    0x60908151b0d0f050c0313020f01020f0a0c14062d07020406030f03080a06080c0103020f0d0608060a052a0702030106030204021b0c310608030a050712031104 69
    0x115020500150411800740c90288500c114030b601c80800300c94030741c050400328800000c2e00341802c01290f448244c440446e401580400c1520301c10165690031700060040a240c02810350003a900b250f144800c1c24064805004e20514003442c0c0c036810401d40710759001d488c2605500500c0180000030f40500070b0080c14108646049203059541d031007100c0d40744039210b00708000350002e040280010030080000900ea201604c80e403100c0d203556541c041d148007250414401c002090b0f0061401d50000d5002e50b00511a803001c01c0e5015103802c1d40403000700c3c180c420681c8900240d030f00020030840e4945941c41599081007007400d0040840080c0c1d41d503410048103070703c000c5001103c0083c40104555095016000641d40908103545550000e0010b48245880c010350170078078007c03c0341c4506180b80510300a80000094180010b503400d480ea80030000080c10b9408204040e0340c2c18021801244c03c00c050a5501850303501c1070340d1500c003071a11400c4260071503500c000340b500300f01c0c105603800780e0442500c044c0c403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 699165719 1250 699164469 699164503
    0x9050114032a130b010e031b0409320d0318022112130b070b04140a2010020105060a0b0a02070b070c030201030b0312030a05040206040302090718060908 67
    0x880310b8509141e07100c01a840850340a41d4101c901c1d403800c5100e4014000c120400d813a0340e0311040c00002496101c0c1424010101036412000000c030080c6003030340c0040134643c0284a072183d454254503050f803c40300c41e0340550315189001c0e1014020340c48100101c40140c50300e45400d1140c0f000100c4694a03000407100c0091051080c08401d043d0040052040700d21004504201e0300040000c0311610801d50002015082031410104041030301500d401c103c82600c0e510684150305070355191151200200700b00c5540c409401065503000102d808144501c01c1c03070f0071140d401c81c100c2001c4c0003040000c81c205072955055904020802001d80e031403007230f800100da05c031340c40b065600e0100c0348049040540c1900080002480820305100f40000d5460640a03a4401c0c3c8040110344a01d008240d039801c160a480ba00e03074001000062090403050300311a8005101a10036400c1540b00d80c0050310000045400a00141099190b145200240740340d4400a0071a070400103080d50a0109a544a04071000000740700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 699166969 1250 699165719 699165763
    0x503073f06021b060610020c10020102070503130e0114031005071e080603060a020301240e06030f09060106050f0d1a06070b010f0b09010f0c0501060504150905011403 73
    0x480c011808403040c0941c0301a04541d1039140c0f001079030500300d0206203124103200b0400001d40d603050036816003800030b00784d400405008144400700006100c0311400001155020700c0188002403041014248003c249806c41a40d2401c190386070000c500142e0051650340400070308852190ac0c0401c19010310301d05a0000b0515a46640701654031806007807190b0101e01004013640a42d50703001445901642c4120183e44954566590780d2090b0b0000380502c007480300b04510301070305492461094114080030b42c03e0140300c1d084100000f0710250022110031040224903070802000e00c01c00d2121601402943c2400780c186524042c00070150b000d81805642c80b6550303a403001070040c10001d100b600c0803c004151503034a0101e881d00e1100700b00c2c28814101042c0d203c0c1c4011401624850a031244000c041c2c0d242403600c0d007400001c6417400c016072020b6a89541c0c403000451161202d000b0b2161025040c2d8581080c240b42c83c00800c04c60704164010155078400b1064130b851517601040800c403e041e03c9084d4200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 699168219 1250 699166969 699167069
    0x13080301150e102a050705061e0417011b020c0105090301142e061b0602090a150e090f0a0209011704030309060c05030403020604060f0f090c050307 65
    0x40e1408035502e19803003840242c1d100c00f0584d0082000e0341c1c1000620254a002c250040010104800307804002c2c0650007080e024000743c14100c014154903003284002485078484403451031900d9115030001c00701c00e800795007071800c0c40f4001d025928584445508111010220046c004d491300100c0811030f040000010711102103a4007500f10034030400c0c0a00c0c10500e103041082d840d02485900544e6414205110f4480445c80c02c480c0e170800040b0b800985841c09103150010706072281c0310b60244110317100c907400d00000450740c03500b0030540e0180000c01c084418403910174101907c40b03103040b00b501c1e2040d10960200199046d80300c04030798215900010240e12103c110b03005a543c0c45c0e80c581112540464402000185603040c0c06c8042c0c01130040f2410042c070340400b00e04940603c4201c8000d009a48041d001c034001484982c000c04c4a940c408034005021a0000d1001040e03691031641520220b019172014800b80c502404003000400200d41c140001265240060a104140d0195411039040b60f01107030031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 699169469 1250 699168219 699168227
    0xc0308160207030b2a0703020a020405190504050c090a0e0c0f03240a110f070b070912050a141908030402010c060615020c10020307170426061308030115 67
    0x40c3d9401420740310a4a420500810300d440140c15010070100302c040145044504507044071301041d01603000e00701140081c0c0a1001a03c000340080b50200401c228040d080c10007031003141e0140307200e40040d103644030076182000002100a82000e2280380f409109440c1c07054006800008140142e400070702c1e0f0100200000d080c1103e45042240081c140d80d00c4281e5030200e000110b2184541020402c100c0c4504400c80035240500c0c5401c0f0081c070f00c1000101c02041406444551106403441c184054640354440c640e060718040341300701d907940c1c40a003149007044440c0d8143c044441e80e1400800c00c075181ea400c0341846c034203000c1014107a1031001020405592160840a82d8a03030070407006d1008542d916680000444c00d44902c50050107005511025031400300441c00c00c669a590055050101da074840e185a2840e54032140074500c0d007040f0004401c11101202c800007041550345007094003440605038207042c00140403a00802c802e8808100240401d42601c1c152004d0a00304408600d0f00d0100792 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 699170719 1250 699169469 699169483
    0x151d0a020f03190c0912110d1707030207081204050607170703050706140411060d1b2c01020304060e01030b0a0905060f06070b13021c0b070f0c03081602 67
    0x380540e880003007003111211403402110340c501c0071403a041181c4115204d048403407003890700503504150710501c07441c0040b83c1c3d803042e01c0c609001c0c01070020608900681c0d440328403102c00075280c111400c01044560505405005000040081c80003400c0d0a9511403c01c10740c609c2103014039031040e100840c0800620650b5540c1c2c203000c1c41d903007240990300c0360203003000f81154000701d1007251203609000c50440d400340a0b00360346000310341c40b1f1100308000b00303044108032058102102070340a265640020702d035009212003441807100c88545420501402a02c05804501d0410444511840f550362200d01a070360b0000c1214101c801340c0c9000303030b05c040c04240100c3c082d08564140b5a80661001808500f151032030f84454042d42007100c4192030100303100d0038003166001e0030101130400d00c104800035807901422001c2c810390780d1000f4003514082c2c0c48030030001c241c10319900041c0c3d000300708001003001c523540040e82c40c20a0881810300d1a4103090320b5500408081008100341d891055070140888441c0c0200f14607 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 699171969 1250 699170719 699170737
    0x40e010f0e0f0a1e1217070f09090f090605010902220b1c0e0f06160e0a14010201290109050d0b0a110409020705031c02040b041e120312151d0a02 64
    0xb42c11000d40100000b8102d0265000c6e40e290240e2500100303605500820344401022000c2d07d402e4103042c60f05c02983c00921a540d403d1160641b00c600b5040060303c1840b07140e0107822607007801a10b8665490010314400304500070044c040c01c2d912414040d000c555820b0b5a100c1e0825450f000a0784800940d40016140c50f200c0d0702c091748200d03e184a8004e1005c61010701c189242260100c0c0603c40c0c203000c40e8081000300313800e900039002c000300b800320400d903d01d1038003603a20600000c142c0096034031b080200114074101c0104080c00d2380141034071561b80b09034850001c100840798156900f070191550340009002801e9000c0003965a07623408800106141560000c3c0200d20085480d00d2403070501c0c07a1203500c401342d00316585800c0408004a0106482510183c9040c0c205071804c050815051203d2001c0c1103140c603046d030f16900b1000801c580d04509010707000d4802c1d44d40803513188403402e80c102640c81e00c43c0b609100c484102c90a0202c2288004082441d06150000c0d00c1307251941200800203100c5c01c50a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 699173219 1250 699171969 699171983
    0x103170909040f0201030f0c050a0804060e030426010903080a020a0c150207021203120c0a02070f06090303120b060904110d050709080d090b1215040e010f0e0f0a1e 72
    0x1000140310903c084502c140d4000c1c0c800b4004514a01010801c440081308041c010a200b030200b030201c5031080d100d05611510500000864540036244649546c206074010032190140311080352420f21080c00301c64000c0100c0c0300a0000112555000e00100c100414800c000e0b64003040302107041c0d208080e1811040d401c90b107101d110000903c1030310302950040005174010400c507c1030030000b42c400401c4481d19030312840f114001c2c1e1201d50560009a0000c2101800c501c02ca0001094040e10001d403c00284156247c10a40b2440c5103000f400390203110010036061413400001100c191144012a60302c0e4204580020394030492042d5005103004204511004034940801c103c00d441e00401c01005032580c50044485214901d20221080030b0b240c001c4803001071080c407550100c000c5c883c82054110300d047d94410030740c004240200d011100308410004c5241e445940c1082d140c4413074070482003c0140000a00798050762442096912030304418028400120480081803100c10941070002040d48100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 699174469 1250 699173219 699173221
    0x18140a150501081608121e1303110d02010e060f0f0f121612090c030f060b041a0105041e030b15040507030c0c0f0201090b0f031501020304050303030103170909 70
    0x1103444010300090107810300c60301c035051021403107940d410503072000c4408a4005140040c02d0070740040d0550400f00701e4003001d51142c122900c00064410107042c02050416030005503e1842c24560910106407a0050045060030030170000b60b40d01c140e2007180110240c3d003041c0d40b050144417841c0c0314415070100038225180410300c60815043e0500500100300508010f02403a200c5440ea4002150f04c02f9104010483c03d4540c585412000c1d00522802e50003401d03204241c556944410104444118084920342d9451a45000394039061198442ca500c045012078511903100b0000303000c51007107008451082c1f6184c6800355882c40841020b02c061940a071107074145081020f41104915481c0b10468415820100081c900034401c2c8101c40c00300000740c1e11f140184080341c0b0f505081c80d20124090b0704100e025200846d42e0940a001020b42990004945940786080c0007000e00d1030712100d0156045400c01c2004100d6a41d00009032130542e90800d078054150000801c8604451040c9034005400ca58010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 699175719 1250 699174469 699174503
    0x70f0e040f1407080c0304110604210c080316060509121215010806060a05031e070f020c06120c0c0f0a06020a121b0309110307030b070207080118140a 66
    0x20b007000c4a0b00e0155001c21459464007141130b2481a4110740e4840071032030600000303000c2003c1c0205030b02080c5020304100d02e032a44440b0007161468018418401c4411300002c0701c4100880050722800170550340c1e000d503081c206c4019508001030100d040142c41207480b1400700b41d42e80c03001c0c1b04203040d95440b881100d42e01c0c036108800341000c010481e55181040d0000c1c4c00305d406540a103d04507c03400c00101000d14000c0b0342b06c41076640b40c2005d072003190a6122429030307055042c03031504614014030f000c0c1c450701c11101d02c18000a00c0d0114205025009000501c00e42d612100b196074420f40040100303d4031a03e40c04000c42203890401c206800008034031480b6845000d120075a4001c2580c00c18503590514100300004540c1c1c19200321214100b11050815030521038248a81e0018481c907204021002e1011038010000e4a00026600140c0d841a08030b0184038100d90100261402019420020f004c41d10245803221088801c007800034000e1244400e405800c003800380216054198441d0500710f01c01030b60 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 699176969 1250 699175719 699175721
    0xc0306062b0b0711031e03150a0801021902030c03030a09140105010e010e06011e03020901031805031803070e16052101030c0f0302240c0a0f1b03020306070f0e040f 72
    0x10303290350303020030070f007100006044c60084215000c02448094002c0b031b41c0d00800881205071700040144002c0c442d1101da100096841210400c01408044000350312021080013002407401d80444441c2913604c00c124900841354044162a4030a00e80e0700001440d40c9a81003812000c9060020344986500c0c05002007418030403510300381c1c1690b10000765810036503680360041d524500c0005446420320760312202e40070414400d40062030b100341c040c0f4011582041c41201208803460501003250941c10100360100000c402c1002c80c0547e04044000700072051030034914074490780d1b0140c0341d0005c0c4400c2c0d032403c4c4002d038000c800700c070050042409a01034003080305008120500c401e01013142e90889402000910705c21210032802a00d0f002480070034010100004000d0b40308410f860300055031024000b219008100f03005100d1028050b0600d03000d0705004d4a004d9070a0748020300c0700013804000382814400750301e0014203540c1c17201c1113042c4104000400c3d82c090310500d00c401a0241d0090a0101c880e10380001c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 699178219 1250 699176969 699176971
    0x9010b0f1612020d11031e040f0b030a0f06031208270105090c011e0315030f0b3403020304030e0913051005010b22050d0602040e090c0306062b0b 64
    0x40c2d40e081d1074084070a0b00c402c95845010401030030540d0300c10301010400400c078a619031000519800c02074909640d41011100c00440b0b03610602c1c074010b010040281c000b8039400350402102da00c0f070007040180d0850b500e81c0000541c2030f0184003008a040d001880f0f005400a60341302d8610503271981c580000401c5001c902034441162107441c907014084400829500841240000000660207154020000c0318100c00624100301d450450780803045000000c50b003410850341b10140501c01024140c602800f1070b103443d0428a5030010b007140307514a00b821041401c541486c031100240b501595a403501d050445030000c15071101c0b54450400c0c0c09010502c030b4400c010017181c1c1c4c070550035158101582c0401000304c500901c00c0c0402e10001304520702c802d0350102e09000026016021f0022440d85540100d8003105400d03108803401c50b4001418001d082d0b9040445038011540c10080c0066006000429156040508518090b400558801d111096a0129001444400707a00117203800c171141860340200344 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 699179469 1250 699178219 699178253
    0xc0f150b040b0910140d0803070302041a0a1209030c0b2403031e0703110115050a090903020a0b0910110d05070903170307052802100b09010b0f16 64
    0x100c2c10440540740d0a0004041d4410341c4a07103100b8900c1440c0410303074075188075492011a4042d80090301800012640405036010b072205a50040e121410310f41c109a2100c200410940420750034048540100d50100045034140b5075070402181440c5980b506888292100000030301c00c1d925102000780503141d144501906003101e00d9481d59001c045c81c14103032a88078000c04902d00c003020442250740308082000900c0d80f54401e00e4410030b054000400d26086407600000204008180102040349140c0140135601400c1603000c2000194125500a5503420703150b03200600320f40c1c0c0100002c01c00e107401d02100030107010f1407606001541c01c50301c0c1d501c450750100c95005a583d1030324001c60440d03841201c01c14150f076405200c0c52801480407850841d15000101a0000c10100b041040d4042d581031604038450386451050303515040d00540080d00700b1030f00c500201e80d40c0d40383c020021403659690123030a044030030f4042c11954800c01d43c0382c1824503124030f04e0305400100701d44404900300501d12a071405016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 699180719 1250 699179469 699179471
    0x130b01031e020d0302010527060c0a02150106020a0c05041a1005040b0409150f0803030c030a1b0203030906090303070c03051602042c0303042103090b430c0f150b04 72
    0x9504442e147c000c03c81d0502c0c88c05594013400009440145410040c0071007002070040329607094001041c145895001d0b001880180c000c0f403c0c0c4400c1003c050440f1002d040200c80510181c000700e08240700b0810300030807940c480c0f41444c10360b0121034052000c03200948800d21000366a83e454001c0c113406410081007602d40c4180c18000000c0ca20002c010005c103841010010350f1440d1030716400b261258201a08448140c1d40c0c440b00600c1c0c00001c1001d890300920281c014549074035005d000d071820014010500d04990b0001c01c01c1101c0c160b445050840102d9260504c143c440c5e400c001081280c6640c04002504145042d011321010100300081001140e0395404031051400b000031b03669100d000c2541c0c0100907902c1c0d11038a15150349550800078027007040d0706d0001a07440850b143c2c00d5852400f07a507030420104007400004030391800e8502030100481822103844028006250300c2507404c50f40c00884040060400c181d0b002c1158000c1004203452304401c02181202ca64480c0c1401442403002c803070301c0741d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 699181969 1250 699180719 699180751
    0x4050102060a06060503070f03321609270525170103081602040c0e0a060903020a051216061d27090307020306100e130b01031e020d03020105 62
    0x50b82032401201c096130141d40d103140c1541c549500a4502e82842d081e20818503417502045484940b0300783c1424010000f0304980c2c5540f1003c9412803407141400b502900b40e000c4580710301040107810120f5001280d030000c0c01d0001d00c0c0e0580050745507000800500c12706150404007071007024580c507440c400382c41541608202c008650458203588060f02c0c4140c0014a0b40900010000709014102a00c1580c0303240302400d00005c4164005022240006070002c0071801c000103800442c1441044000500514240b10240d00d0458000501098492040c607106503042404070064001c18015150071031403112200c20303c1d50322024003174004c1d2036903286403242c0c691031040c5101c149070000c0250401d0030662298a031414410044807090310005000105c1844200041030058908005041c8116000c0d0350303d89034a8141001e4803100c10f00500442242c025070040302e004255201000790450360320440e0011411802015981412554100a544040301d10101014150190000d5129600da01c00d04082 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 699183219 1250 699181969 699181981
    0x60605130510020a2a1d0a09060905060907090e0a0b0f04050c0d24180f0503090319020a060309050303130314191e1409040b0406030c03030e01020624010e0603010b0405010206 77
    0x904000c45140c02600400012400040712030f400700c0c612314020040030400c4515521810700d48181516070a82d075078090758080000369814410b01c11490840005000b6a401946039590300c844060101080138444d1b801040c10420204958032a030f407005046403582d21070900303044480c001c00d005503070681e00c210048504030050900c203403c843c1064044407418100c803a00e41d0380e0b00c1c0b03201308021a1584410403207a02156401c1001c0170f0040024a402000429030344140043c0300801d510010070b242c01c0c5907000e000124041b045d00c1e070046442d680c07120b0301e0301c0c50304044804681180e0401c0c0c0c1800c00003107140c0038010320044403108842684403004190b509440131300c0c98100002c00d420014410341b50025031900c0c600000d05000780001c001161500b212400207085075803550080340c03441c04841003001010b81018000e00c08803424000f40c810752804842c0b0448a55400828440301c0c4201051005941e0003110800803062000d8041ea880350b031103410001941c1c0c130074003030709016100d0b403400148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 699184469 1250 699183219 699183239
    0xf080c090105011409180108030424020607080907030605040609060b030d0504051011031303051011040b03091005040b070311070807030e030709090501050a060605130510020a2a 78
    0x10480b14180c0d41d450f80d103070310512008a0307904280e950300c0e0f0020310319481c41d5513801910182c5020b84100d602540da92880c20020882504c5001c00001c0c0180001100402003070b004125550300490904106040f1380d9100d41c60b90421002d030b00014246490701007403000740b21855114034801d038806e1a040288020302401c140da83d0940b04842c038005102008140036038109612000380504840c100945812414480030b0b0950b0000745041c030340e01d540c0100c2003082c000200f106040741d882c60388e020040210902d142755241c0c8510b000e00b00c0300384030000118540c070b1001c22404000d01540c500070003181c00c0c24600066004426204c100c0000e080140700c0c108448074000320f41056502009443c42e150300c507507054a40584010903580d041c0240840028101720a0040c416114882c100014451400c00081c2c400c4481136000402004418007590719920092001c5105440044a0711809401d000d40103d20700500810003e184560050340e2105803d24901004002030410070911091030b00c90315030003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 699185719 1250 699184469 699184471
    0x21204090501032f0f03150f0403090e0f04020607021c0f020a0b0a02030d090c1e090513030e0f03101401050907020a031e0c08030f1f08070603020912070f080c09 71
    0xf0784c025034031300801910340800380c014100000740903540e907240300d0198541c45c80d40c110790202c0b03001c0403601000105588a0007000180074400c4880302c2c2d03420079200424552070300400c024000d07070300000c0074425556140302c14110000d80c42416001ca00c1e587c80d05a52003d10034204034010800c0c240e01041c1d03154801c06650000c41641e0085061140440220000e8100140283c6040c2032000c00401c2c031004440e010f00050121302c1801031070030f02d005040021608000c01c03082000c0045205030000940c4004d441c0c0503401700300d85010140f000c04000a00700030041010f100143d1402d0200f510512400d80070390f040720412540600c007035686c081c0c181e890b49a0f2500040009000e01c59212110310040921110781803503142000713203141c50b5030b103604103648107071031000042051070f04001540110f00000411044000c00c03100d5005d143c607030031650320b001d6405aa02819000b080403021a2503d00c202e84c440c049110459484950b9080701890140c11360180f10114040c03201140541c2c00c03d91a61 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 699186969 1250 699185719 699185783
    0x901060f150f05090102031e090301061508010602010b0f01201009060e07120b0711010504030c021e031c03151e14030a020d24050105010f02010e03120702120409050103 74
    0xb85d40350602344c0c8000030b00312806040fa08e03e003050602c0605131a4030709203d000c010300074210820464403084c00000d8140c400c140d000d03000316070400010a441d9150a51070400301502170a054594080c001d0540081e500d04410030b440c20300c00c54000c04150000c6030840c0300400c0c0142410861080518034144e102d460501400803524540301d0b14400044410041e5a4800160316068080c01d134404a42c5d030035103400b9102900064004019082507140414200010314813003011480074002da50042a200ca2200c400401e0001d011203500b29414040d40021441595a100c0c3c910321a07100c507090480c0395103000c003009142590380c50115030381107403403400000c0c2c040080c003e090003220340c0d00b0842e0400f1240d40c200c0306491482481800f20450385200000d10760041b8002c80c80d5814440010f080e100c0c9041401c0c00c680c141114103005100120031078141ea0941d1450005550340c0440c10307480d09101d9180c14824410010703000805002c15841b05040e280704111442d4052000c64501d10390a10341d09071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 699188219 1250 699186969 699186973
    0xf03030c15020d0c051c06150f0c12050306090105040902150c010603020d06140702060403091223010e0f030f030604050408070c270b1807030f090507050301050c03040b0403080901060f150f05090102 87
    0x511008d01c0c00341903492942078242c034080c55040310310307941c14807044881440d40c000f04038007006000e82460178140c083e014142c00e4804000000090b00080d0004000740c03000c0b500e4110010380e280442e030003074100c0005140c0150405c45501c4031454000010005500321101101d42500071130005403010505034080c2d90540c0d201c5400314144621075001c0416404121800041340f910115583e4200814415080481c4000192900901d040078142525002c10b58520380007042070401440700242501e810000607140007a05079034614181030a0301c945035002e002d00c07000c042c000806829500c0c0019042e800c10002d2800580882d01410550317a0041c030300c036030008c0903801c601c2203802c1c1d960020741e10500501c0d012a000c01c01440200894180e00070585503600204000e00c25414240a829049904840903514514140e200d0400607240644010f08010203207012400c02c0109400c40001380c40e0b85060318100030390302d29244600c084c1040c00324010407002e903900f140c0e0f2406241624406481070700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 699189469 1250 699188219 699188249
    0x2a0607080105060706020d06120623100b03040f05010207080720010f1209120903111806100519081602010e0304050d1a16090f03030c15020d0c051c06 66
    0x51090065000400c00c0d00a156681d01d00055910900c80c40c0038401e402aa400280014502c2c0c0050031f070bd000348040058516400188004940e0300c0800c0800c803080c1c1d000980d01d949451070310f20000384205801500039800400c40301c090112440c024500f5900c103044c4090202070300b500ba204000c0b8412001404119400c00341d5480c54003501c504083c22094090000d0600001d540d03200210741c103c103400c8002a0311110501c100200c01450008802044070180000109010300c0310200b00010400da000e00c1c500c2089a40301401441590700400e1600f9006c0081840c9440080001c1012692001c80c4040801c92000d01030042c8070b5143d5501250026514043c145018040ea02d03038440740880e0f402d003685072041d811146401105004940360040040021104400200b801e180d0303801503d00700d0b1a1900400000780c018000038205c85c0c3c13040c0b803010648030205658000340141502011018103000440e070599a10100409006200b00d4459805c504407440312000c44000780611103070000c1c600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 699190719 1250 699189469 699189473
    0xf211e13240c1202030603210d050f10170a060b030f061015020f0a1e0203060403020c011404060804260d0e0709090803060409082a06070801050607 65
    0x1440c60400140101c505507480300301d401c07080c4144400400c10001d45960750650084103540030200c4482c50440d00b2041d0309604058001948521111200e600402d2070045034402e003440ba1001c2c0c1d6684d0840e01030400043c40c20314481c810910089604180b204822140407440c5009040d001074000580c6005204050f5036035950340c01840c030603501e1179040c40340200c00d420314441000087e1107080b5070182001c0e030303920b00105c4103e510142072002040d504803000c03000d40ba80c00000c40b40190398008584254402050301d0714000c0000090000c1c1d01801440100014113030000b800d041540000c1e40d40c50b81c440a6040e50404502a9005210020741c504000c100810080c0f8800301d0b1800000034034001d0280004c1954110782e102d609018142c5032540084a1500c200b03204000c01050041024005854960740301c0a2a11004009602c600d030f6414000040c003c916040d02e890700601e86000d800c0200030701207020042d51440a030b0089106810028243d18420300c130041c100e0344080c0c109801c12140d9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 699191969 1250 699190719 699190741
    0xd24020a170705041509050f010c050d031802120a1a010b09040905010e031209070b0f0f0d111c050a020a050306100c0506010303081906080606040c050f211e 69
    0x10b0715020822805110200ba11010342d044003410703404907141e0b48a403629100501200700034400505051088656002020502c08552800070182520b0000f0f040314140580348034044d51643c0103500004104240820030200040444895000d107010b240c0d40120114616000d040074080c0391100c030421310018a043c01c20b5001030f40c00034824000400c0c4014000112480c0d0f030000c2400c0300c10b00441c1010312640001c01c1c01498007070250813202c0b0b0300d4404180000322051040e43c0d00000902e000044a60500308258440b90b042c90fa000c200550711102820588050141026603180d03041c078000216100c1140742c802c49025000903164039065540740f90401050300c81002400b810f00c021080f400c400600144140c50103144aa100c182043c207001d0154070303140b8200311001c4c0c011840c0a4081c000075200050241d4005401c0700c4c0030402902440d000c071228007501e440c41c00bc0d080c0100c4c203100c12804512007a0081810740c1000b52040d600c0c041040404c01c1d0348186500080c003483d020501640c54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 699193219 1250 699191969 699191971
    0x1d060409081c11030c071214072301050c03070f0207030506042616060b041503080c030d0f050106020115141c0f0308091e031210050d24020a17 63
    0xc441c0c4009041104583e4207042507004440b076040700040025088200150b03040110529021450b140410003280001410603204d400c0014041030b91140e4440f680c00403611707c1e10080c07480100203000d0fa081031005034040b40c0054031604041001c1c00c45100c50144002629421690003400500d4551103a4940c00c040340701c4500c1d150031040c141c00b4030188012004004200c60030035071448018082c1b680c04c082d021a40060610340c461410b199032a8203034482da8404106076030b04452130b15941d02c1d603101c0715891031141008895030141480500011060198071a038125940d50300240100c1c2203642c980a80115980075024000c444850120401c0c2819070510404d083c41c406400010081500c4804199100c0e031001c500062080b001c201c001d02040c402d0404105007101d1007240194481170058036409102c440d20240b01003200051841c0382e41f118010010480548071400340e100c1410700c513005141c0082480e944500124441003504540d1003203543c0040301c2e940e41c500000c142c8030080c03aa910 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 699194469 1250 699193219 699193267
    0xc080127094d093c0a05010b09030307020f0105090d05011a1203030a0b04060f091e1b0e040605150a020706021b0409030215012903070f05070302070b041d06040908 72
    0x10b11562044e003c1d00c10300412007030041944141030700346082208030080c0c4905820411807002d0600c0080a16280001512005641111070907001d00c0407000407900c038054100e81c1548091008015014020f040d800803c003003842d95150018900444203020a5504410100710194010400204c2511469102c070070b400d4001807012a10300e40d20301511b402502e154109210321980e91492010340c440100c0002c114145a0000f8040031241d0010342101d6650b0350704040510030010810031003070f80c0766809a0081d240041100c028030040343c402075065000720390610054860306102080940c000602c031810400d00c80050b003429a8071206100c00307840c07070000c12010344c0701e014481c0415460f5600c1c0180a000f03d00c05400c4140c103441100740140d4008100311a24400400501402641c03107200e087d401c0e040c90500341c0d80c503029071500303d142c0303112580070600324140030030301051907002c05450b442020b02d5440e03034076400d4698004100446030340700c50041c0002d40c02c101c008002c10b0311800003c5c0201c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 699195719 1250 699194469 699194521
    0xc0612040510060e0711070e061302070c0b0403022119050114180c0609060306060f04030b07020c0405011707031416090c080127094d09 60
    0x161507500642c1c141c032000d40100e00380d0099a420011125408510f80c45100034603401000518501a4610080c00000d40610301030252441c10342041407a5804450769681d02646071000a07032744000f240042e801500040307104040c0030818117244826075480140e080b40090151440e01c0502022140d56407007403d0403221035480350400c11081202c8a41184194440c81c0c04151060410041d20700b810304003c01640700f18802e03c1801e406464810a4035804074040d81d01c1551002414060005805282e000030260320fa04410041b5450380031845283c080b0041da014001a621100c86040c00d0035101c6000307055620084041010a0f0006803410919030030034180e0301860f9420350022882c50007500031b40760042d11444001e607040d03400240340f801454904803490901c070204280403052107511003524007560315440c101c0e042c400032100341c04505c0003446000c200e17010040c40060070a0401c400e602c101c1e800c00315148541062042000e0003005c1d00408040203a5281c2c00c018040031a00100d040f424 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 699196969 1250 699195719 699195733
    0x201030b03060709030b07051c0504050c03121312122111040e0f06220b040f050f060405070f08040c030218040506010609030f03050901022e05090c06120405 69
    0x640c40030b01845000e95081d90b24251402c0c110305110800d40e4002d4180c0b8100a81001001840320030032030303026809030700c260700440c140d22641046450300085205560b458007445041d085004140d40003403409170415480d144425070303142030b42030024527020009408036001c10a1150450700c0348001c0a48040c8151400300070b4818600514111020100d244020840000d014031409000102e11039120190721412441ea1901e040481e010b800d8130303203620b00c44259200088015080c1600441d215803c05481040420003601800002d41800c1d01d22100c070a079500003203009410a806018801d4501d615115440800400202c4e80e03208024000e0310098070340303980480103a4900d0802291141840089003450905041183c03c2901c1039112100381700c1020b1013000000c00d0252010001501820529150005e400050b81042401289070708046080620405011040c1c1101d01c22407411003010405941d800129656488110810951180013031007a9003c03104d90307401c42e9901c02d100f8001e071922 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 699198219 1250 699196969 699196991
    0x9010c12030e07060201020c12030601090501050f0705030a050a030c02060f0c130b040e16090302090106051b0d11010605010206010315230f15030a0c060e060f16050136020103 77
    0x20040f041e0040350041c0d400207010300400004001d001209003201c541c992460034544006004980c01c0d20903141400750200740f084040c0903101c00c0d02c0382590480c00b070fa0741c3c5900c90340000b4030550110b1080f00220303190001c05c21a0a10004642c0d02c2501850004e2540b034481001c0304203150084c020701c0204800da40e0f0f010441c2582100940010895035001c40300e14100500b100d031380980615021010007420071400c001580d280707191181140c90900744280c6e02e598528002c03107620a40044035035188607842e0030300c0b0420ba00214204900f10f2100003007046035101c074012600c4502c00e110241c03116040100e65800c54181d075006c1c02604260f01a08488014804142c07010700701c0440d10003800c401c2c1e5200704151b0b600d00c200a034009079002c90190444d4030701c40e035038144d190105002e58010880150b104440780d4858204513001c4410815050740c0700c1c010708003060f940c50400d6000301d800d5401d105140c0502e800302c0c00d002e14403c0c90852070401846034440d1420b070703810314241c050381055150030881c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 699199469 1250 699198219 699198223
    0x6051c09050a02012705090a090f03080115030605030a110d0f0f020306060103062409050303040906150819020703120207060209040e06130b06131b0306080309010c12030e 75
    0x10903588940e015002107803580c000500125900d09596010706225059a07118102c001100030030713500b003280d00c1020390b255003020700c005101c1d0a074000e20b003a26280380d420601d500300b50154105d50901113054003003d1035500441c19034140e4415903801d81d020604000c00504c426a8200300190050b01c02d0092419603221882d510420081c1034a40b00c00c11464107065003014840340b82d03c4103003801d05100750381c0b50100c0380c0c040303030790030003500c031444206000b0382100a1146a80000810000b400c0300d031070710f031640b207130344010b000314801c0c880d00036920840024554041d0f102d13035102d88083c407155030f00e1018100140e0041d600901c8128100b1065a10b4003107403400e54400f0781800b60042400507103444041c014081150305401004d14580d21403400c1140740820102c0c0c032201b41d41c1c890761404a42d1246000320703000400c0c8926a102d4507040c0410850511444a40d119451030f81e950f060064640d129113007600c91148450580c0004e01c681400030118074680c00280d581c020901c2c00250b0a2030012100d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 699200719 1250 699199469 699199481
    0x30f0a0b09122208011e0b181503011404020108060d0312061706090723030f1e07170706031e0c0906021002030609010302120a080d1d0d020706051c 65
    0x2e44543c121903800d0310f1420f500e0750302809411180c000300800c01c1600440c041c0c41c1141c078901400c03a5111903403200707136450b074410841d40380182045403c05030501042402c400c0307900d400400e029618040c000d0302c55100700e9550500031901038540c03047e10b4031510144070b590862a0004e509101031810211700e1a10300d84283d500425041e4900746140591140345402c05101a100091a03403202c0b20078801d000481c500c49841c065900105425450303614042030420504030704110f000d0194848411100c018030280c1d0b02ca405405007a80c6255032202c408420b1540c1100030006207910002c01401041d009500000042d500d910b02c80d44038641401440c02130320b00203164000020b100105c00c0190940401c0a0007480c0913003c400d6040d80341040c0401e941201c1440f02034410200b9400c5082440c4040c020030222982042d0590380d2100c818081501424030b030000e8420307040e00c817101000301c0d91000c0b0b03a0088000c0140e000d880640e1803c2c4084450f03800031300f040c0040d007940c00c60036102040a44110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 699201969 1250 699200719 699200737
    0x8030601111506040f2901090506030a020d060b0c06060112381e10030908030108070f060c020108060409050709020d060e070201020705030316030b120a020f030f0a0b0912 75
    0x2045071418a00784001ea0b1008940c501180341000c0700001203803034866541140c51804c2e845143d900c6c01d4000100da4000090340000c2c1c000038000140482c81c507a6400901414611001c10712046640300802c1d400d41c400c01342980303002d4100001282d0558403070111035054480883c0f021803400300e65601c1800295034104002105a0941200400f0007a812081e07240e510f011980c0d0901180c0002d00d1005006200701d15074490400301c040f030b140d61802584854030f02608042100d80301e68555020301e0361490741e0f0240108a5045241c000391441c403402c240b006096069446007901d03100c0c03006101c068440c0e1078084500b0700a0000100d0f41c102ea51020f006001001c0034041207280c030701035040109245c0503000c501164010000807000c2913000040700c2e0400d4121100010081e02840114001c1c0801c603031709580092a900341c0d51119400150004a06008403180209540500201665010f50b0308c0041e80f1a00f1503c04e000c045081034001a50004c24802950050a51468044402d921034070b29 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 699203219 1250 699201969 699202003
    0x318070302131418190c0909120e040b18100b0c010c0e031504380103051e0607110c0405090a0506010b030c0301090c02030d050103080318060c03040803060111 70
    0x702c004881c0c3c118003160000d80200400001050702c5007060344407030340900012441c3c13007450000d0040140c401c440800074150280e0403c4103541900d4840004440c940300d00c0c0c001010315102c890240f600703105a04040c800200700d0066103100b0070141d000280b0080c40c094403141c0c020800590315070808014260002e14100010301d941c4a0301d005403c030900c000c04180a540078a048240d0111000540350708550050362107118811031050301c24070211007602100744c041c10726602d22160202c0d0310b506c82c140c0b8807803020307038000100d4884604481c10b9004c01d0b144a661203500490010388c000c9001c00200e0500006132102c452194010805071242950007222a6020101c0300d810310034148030349030152125502c001d10310304081900340340500060150f402000c1d9a203500c071010a008100720f0310300d40c40085c8144165330f900d04181c0c1c16a00103c8911580c1300d440111580072034800326280e8850740086d50500c3c1152070355100d0142a07000106072506100c1e204c0c0c0f505140b030504001000310030400c414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 699204469 1250 699203219 699203231
    0x30212070302031f210f1704031110020706050a0e0d050c03010c021603172101090e0111070803100806090a050c060a0806151905180f06031807030213 66
    0x40d10803008080d5408490f0004c03071048180816400e4058102407400002c4102e0000581c50414140380316141400030181c10804180c040755210100c040c00c12039010309c500c801d003452900305001c04031040002c20401a0007508040c000c450094020f016502c029140070301081812101142002e01e400da802d40d0203900440700304020b49000d00492455500b5480a0407011000005240038510079000c01050385c98202c850800c04503602090326401c844012014905079040c4403030400c820421b004200c1d8844c20450481030303424050140308241d21103036503039510f0a00c450716031100541001d883c0080205164400242040e03003004000d0080d17018501510000b0560f20f072180c5000b80c5040590b0240b082800200001c503000078030710340c0c13201c400c2d500e00301000e05040e0001154810b2038441000d81c05404220780304594002c010780b030f9604007100800c1e010040031040021520908000a900003c20400100070b455582102003401c00414102d075038a0b030b2250b000841c0d00725a0f60301100c0c80f99440d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 699205719 1250 699204469 699204481
    0x3020102161a0a0902180603010b04052403030f0724020c2404020f0603041106210a0204270b0301020d0c030b0d0210050a05070515180c0303041503021207030203 71
    0x40e1440f40c0040180e40b0030008035015901080c0c90040714407514010701003c800003801520207401c40031940343c006008010600e41403104021101950307100034030310203403500c1c550003c3c1000000c82d130708102801200b0381802d00a6032424103002c01c07403102661314044080c000808801c03034000fa10042c8003c4000c0c181822a0f814149202c8112445035040c5940d450148070150301c99000b107010708a0241c40c4981e4075138a03800c2c140320141c41f034402c40340c1003000000d101c1d03a4144e104825a020701101240380300e164440c000003405900460081502e50880c5c4a2103200014070a08441030542000d5404642e40036000e00103400c903040f070440440c425485d4519981141e038140715142c1c1603d0201c4061030300c00d90780c3d004240b51201160107030042c050005848202c1c54010025501c107250b026048903050b4401d6840c2d2103072400300380d4001201004e110b5480c01c3d0350034040f4203540d52040190007141098500841d80c14204420b203204024180e08004107440c81060104451141c41161000744c1e803420b0070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 699206969 1250 699205719 699205763
    0x10e15120d02070816060c0b0a090c031103010f0e0616020a0b01090c030e030703020d0318060f02070b16021c0306080d020c030f0a0209011206060b0a020c190302010e0d0302010216 79
    0x624401740c1007070a800e000b4030341c01141840d40c040e0003400300f0f00706075a01c408480003001401005000c03030000240000c10407a00c0400284810700540090080f1030300d481c2154180c40b0458032254241c0c00000010344001c09078404801c200c001841219a40300c0c0c65155100340c09030a0f00046551515500b80c0c000058140c06100c07062100306006624060164030020340391415070080c2000c040e00ca00113000c09024030006004001d80052003000700300720b40300c09440298080c4404694183c1047c001440d101c02103803c041c0d030190310740c01409a60407907100190094455005232030502d0359510300030038000c1007041540d02002160b0001c002038051a41010320f04980355040c0e05503076004003000320058403a000d181e030445100d020b030003041c0742c840c2c9040c802078242c3e9008045c070340c40c0100300a040c155000901000d20102604c00d260722002c00d07008000200100c2c04080e010800740c10411015040020151004034001c0c4001400c0c95084e031200d043d0f00012480944050031115080f840344010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 699208219 1250 699206969 699206983
    0x10e0705031e07030209031506090f041a1b0a0e0f091603090c05060a17010506190e0102010605041503020301110901020c130e0312011d010e15120d020708 68
    0x42400c2203819490507501e003002801948001e0482111000085030701240650192490448000c0940303a0602c00c138845e00345500c0c0104c0e03002c0d11841c010408034003855141e41f17205001d50703001844c288040402c518860000c100c05861301d0507182d000744c0c18040321608034015052108965403440f82c0030805800304020a1141201107203c0d0031030005110003c4c580140c1103800301001e00380400c01e4242420710b21880b12403079121580021000032410a01580f0900320440240c21404103200c030b036280e000b409018002c0724070740d08664003482d041d402002d000303100320401d1410504c00441c2468031030020078190703135259003008424090040c0900c2149000e0042814050301c103074000d800c021010300000d5407070005005e5079018041005502da030401c50360300500e100b00a003404482d81c840303148880600c0c0f01e1091140240c3d540704140d02001c1c09500104d114102d80c0e0703022054003161511403403104110050441c03941e1091204641d4210702006021034049010144c010f0045c0c0303460580400d041c110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 699209469 1250 699208219 699208231
    0x815150405250f080703090503090301090605060306100f03110d02120309041821170108060109060801021e0c0304030507080d17010b030f040c090509010c030b010905011d06041a03010e 81
    0x7500b154803410807039015400780e43c0076200741b5000c240910a401c109040d44a4030a9540e00355007802907403003d10023642c02c1240076482c00e81c102d070381c02c2d40c8200c07000c2c00800c10340c003607550001003040307080011501c1400c003101c03071a10040040f40c642c2c000ea400501d0b0201c03540c1041c00241c03c003058062252925100752602c1d2503c2266003064021140c2d02c640c56604035004020080f07101d5400c1069003481207020405040c3c076000740020039611054141d545400901c91140094202131011490f4070060003a20440d00d424141503142d0040c4895540c20398100c40d07150130309440280400000b08604000c680014a484030140c00c0a0300c060400611000d09001c8000c03805030080010440240454216940440784900081c119216464001c3c03c1400650001e11024180b405004a8020650003511060b0643e1010013000c3c0503440151152002c0d8030400380422420100190300c601400380d00d2049480041280d4507003a121101000100111110f28180780004401031154102c0d82410340c1d0020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 699210719 1250 699209469 699209477
    0xd05070207120203061801022a121c09031107030303050103140307210203091206071106092a0a0303090e0c070f020120071518081515040525 62
    0x4850300440e0791141702800c1840d4450f511198103500320002e5056a013800950440b001150070044283d04c0c1c0313113601b004600e03c64018078680320001d00c3c101c0c0c1118460407041010b040b401842d00240790081c1403181042d0141b0603039440081d03400340d00b4040d401c0998429180040d0725410350600f840900903110b281d421552081048070041801c1c1c031356200845490075440a403070802c00c002281140908400c0503041040c0c114941400b04020810900ca420981d540d54031400440d10302c680d0782c02080e161080035801003108210501c0c000c0110300f42808000010417182c50800c008520030007102d40c81034000131a00002071200d00544010f06405c2101c002c03069051031a141c841000c041944a802418003c0803118204103901d803094030400904803a0036101d00301d90300c600c0d40b00d90f44100074001d0001010b00f200d403a00040480ea20348141d030024001041c01484a072842e01180102038001c0902c000c01420b101101d503101e0207402e1040c0c801c52400340700d603031511201040c2010405003007020700c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 699211969 1250 699210719 699210749
    0x2030f3f09150408010501060c0501050f0601081b070b0c1902070302100309150e0c030d02010608120c0712030c061b080402040b04061a0405031905030d051b0d05070207 74
    0x4140c0c0c1503034100c04007100c1d414150001c0b2880c1012030702ca103030702010007542008000101241c00035440c2c4569401007000384a0b65865404000746400704a41c0705000c1440400441c842800400c1501248108481c801385442a075866400e01c1341000c50384007981c680c00186120524044c841c02c0070300d824040c00202203680c00c40e40051010f000c4007009500301a5140e0b00b9100b403000c1e250255103254903850f01004154401c1d40c040e9114480724884030b0203446201d00c400842441481401d0848441101410308040400660f00a950100550040c14402e5290205020a909c2d0301d14440a200e030710b81c01808002450719509071100c0c1c1030656078642954004081003a0001403a9500a40c125000100308011000060003400c1c0380e0004d811101c5008404440c1c00c40340030080c002d0382c0b400c804892610528a40d030b0452650f00c8c0364020a213801c14001114500302681185170080e011404e500300340346181f0f03841c26654000301c010b01d1485da00c5006006000d501809644040c190b0f602c10102c90b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 699213219 1250 699211969 699212083
    0x319030503010603051b1303212309151306030204210519030c05010f11070809010e10120b03070602280204141509130201080402030f 59
    0x2031404144100000d1640354000608940400c031800841e4407112506a0b443e00900c03030044403184800e000844440442d201c0601a500c01e0408610103020141d5038102110800030040070303d510300c0c107240300741030740c0502c03c06185a49256101c003081408044180e1030300c1000d061000001c0190b80300740240341c4100021301806000590b8040380740d02d001d41c0c01020018501e840d83c0b400c0848a92041c4034a0704542c000c00300359018942880d0680200000d00805041c40541800c0301c17000341018040720420031030000040c5d0404090101014141401110384030100c02140e10150078a401c0380006e215001c0c40382c6c80508502c1307a4404240c054004192560912001950302d080f0f00d0100b200090340ea000f000381d01e080707045a0a0207154007030004c3c0001c1501e0002501c0e01d038405e54012411150580040516007001c200a5100d800170615011510303509400550b9124000344c8180c0e018041d0b02d0384090300c85400c2181c9840c1d000760120791100c2d002d042503000242902d1091415a042c8212074070345e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 699214469 1250 699213219 699213227
    0xf121914010f12021504090b030c0f1c110a0e0f0f040b071d03030f13080d0c060203150d0809030111070c090b0a1205010506091f0b03060607061a031903 67
    0xc3e901d03e0103a40d00001154000503c00300c42000740899403030300028000c1079a4816811228881c1802e8085550341c15060040043c1c6030312020350302d40c00c281d90309443c010607261a0204500756000c2e800c0c5002c440803280c0803500c4200290004e5130b04030640c9040c841002c03001c20000b603100c2040c0b6112034283c14039030b4030b48440085c05407115042102101d010200301200340800154080c0040499030b030b800b150040d100c020f80092603603030b548803000100001c0f10074001c12060f0000c50550340700028000d4a568480c02500050b00f15860364119544081c0035444032240d800d00c50f070045846079110060a0b080600396010400c403040d8050007881404006956401000162610b417000400c4078036400001c2141070007141d02100d1042c060b182e9103401d014040d8400d40c000c20041d1000426a41e920300c0041100708081c86da10000c4200203000c00c89518480c001d10303041403004201c1880c12059407603000a0324502c0524680d01c100c0d00d00c10b0300d242d107410414500c2d280c0f41c0e029000005505520054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 699215719 1250 699214469 699214499
    0x20a0b0c091806011808070e011d0c0706020c150108121c050603120703111e1c0315081006270c14040315050a1a01050f12191401 57
    0x300403840b418081141603004542d04011210400d580007103082c0e0305d4507803070b944030741c14854030a024864100100b501c20107018080c2e207598000148409580780c0080000c865482400c040d5442070b0700f40680608541e0511540c0c01100c1405100840355040061060815020a41c0301d01130140410401003110042810780010150401c0c0005056507440d01080c105015124400c14544000811500300740c1c0040d0b000c02032100750000c41e054045103914000c01100e003000e850f909075002090290840444042c3c40c58814420324011aa00700e84003020381c0395075141e400c011b42c5600050b00c4402900200d114800003811346540c0d002407441e4100f985101c0904945660701c00c40d0310b070340e0b042249034052198420701e0314503040c615030b80d190b80742465401007403401c404240c4c183c24031005c0f900f008128017880050544207074545488404600c01900c4c180c8c4014110513a0050500060548103041c00109101d0a6000f05003806410311502c40c0d4119404010001e60103440b0074010320801140121035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 699216969 1250 699215719 699215749
    0xf030901020a020c1009420f031a09041a0106030605040b0901050603010b0703050f0a030c1106010302061b011806020909010e010b040b070206130f0f0504060b0906031003060c020a0b0c09 82
    0x40b4205804010301c0c0030400d044840c02052001c0800451582003e01403090784c1080a17560791310008c00440d0000c506413458101c25414104443d80824000c0c82d06120440c0c0047c490400c400104084040c1c1031007441c001da008001083d9102c00403c16402d00b8000d0361b00c0510f04982d1103400d0760604000070201c1c00113014000c44000042030140c20540a54104c8404d0320300b51203125150446010010040e041149014000601c15071110312904000103450b81a01d40c000d1004c4e0821910101c040c480b9031212110000664031503140c041004151100f81500364020f13800980e8406520050022180c2e041e0300052035180780300c2c0100003122005003940e06849d50f41c0c0d001680c501f903900000d07011740510b2141c42c0c0404601c0304001407002040300c04008071620068540c0b486503803441004100c03241842a002408801c0100480c2c80c03a1801c01154003c140200d0304404076180d84840c02210720305c8504030701580c8405020b0b0f0500c40e0002000c0e9002c1808614645230101610100d01134030305803030007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 699218219 1250 699216969 699216989
    0x606131526011403070914011a271804050a0302070602070311090705070204020d060504051308040e040c0f090e0c060f0d1a0301090503030402152109030f030901020a020c1009 77
    0x703200f4a07681486200e000f480404018040050a182c10341c1d9104001c1c41010005d5418852a021420800c03054400b40000b42d104241510b2401d401401d6a00307050f500d01d5400702c411002c9a25403141c56519900580c0140c0c010030065809182c045c3c60600c040e084801558460b80d02040081c180303443c0d00c1d031500030540d8a80916150310b0400d8a40e80121f880003540140041140325070840d460b0b010204032801282c0c00d01860711001864000ca0341c00d2200035107001001c001c00c0c04a02c0300d0301e0406400c64490140c541540da52505680035900481d00070007881525032503030070700880c0c0c104603401c0802c1084641516080a2a900c0c40c985c1c41140d0303440710680c0d110203401500c0c0c21941c501031442480500240300d40c003030030301c0d01c0ba45a0748200c508900c5841000d0a01d0b5400c0b00060684202c0100806140010b071450740c220702d664400149030740c44900c0b082001080344c006440242d80a038406100141e2a14403803074003e400c0c0030100743e1007401529074041c03c0078180d078040b1100341107410f030403c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 699219469 1250 699218219 699218249
    0x5010c0e031f02120c07020310021606021e0c031e0406120b0d05011506080f0103080909090f1b1810051c05010908210903040905060613152601 63
    0x10190b0290061890050046102c0700c01c02c10701c07100c000020040c0600c2201500c800f03004c5c45a824040b40103043c280700a251103820010300142d095030040100a0000148403205990121452015403044050380c0040e00003240c008036114401e0009441044101c040c50304040c10302d40003c154400c90018400b04545500b01c1e0309880d261524070101d4030350407600a10000060b04441c014a8580317204100c000390002000400701c0f614a50700c40d05a030380c4980001e10307060000040041c040000391040415014806100c4020b00c2c3c04c112800401e03105840e207505c841034210400c9805400c5601070031809042c80204140c0d00f0002d80d18000b6100200c9072026aa50a2380a03080d9001586030000d103158a13005044007405210805030501d4980740d42c1611014000b504134a0000d88291414000c1c0d500a001c01d204142c03268100c61307071181c4045e059a0415001481020300301125030703c03c0e8400072042006240c0d05910481c0900c8541e00c050340d551034003101c1182d0b11242401445642c0221a82403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 699220719 1250 699219469 699219523
    0x90106051c0f0f050f0d0504121202240403080106020a0f061e020301030809030610120f021206070306051e031b030f1e010c090506070f110a1205010c0e03 68
    0x40310319a0010380000405988240c82e240540c1d803104588080c9210b0710a038541a07107000d00c01d1f030499055440a1443e0b40d412940e55482041c182203000400c415070080c0c100e0340294082a10b00021031103000607034180c9900f05420f0142c0494010f80107101150008071018000c10302001c080e003e40d82e070020000038040510742114004004087c3d40c03c185500000c000024000c0030350141894480c100d051300c03401e8a500161225020f840e1190070066000c807841840440d0702e00d801050140c0c000340c8050400d018800b0740030309040e022901140403981d5004e050005080c00c4c02090201000c148241941e501850b0000f60b131020703081e0b1105c2c08001410340c440c5103501c0c11300520b001ca0050100300d9103042c640304441c181e8074100d400a00c41e590720b00303400c1c03a03c41407041c0e880c2c004452024005a2410036140c0321000c0010305e8407810b450000001c40c94007866150880b10a0040200546402c45801c1ca807406c9425180110000030400050041c2c41d0499500407448281e0080d003e01141c8181c0d040c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 699221969 1250 699220719 699220733
    0xb04060e130b04170a020604170a23040f0b030a060515040b0f13170f0601031203090f0210020a030e040507050307110a0c1d091203060418020a030602070209090106051c 74
    0x51591000c0d03401040c0102031707070340014480b8000c61203a03041e106c2040b081c51403000d2070f025a02c40e00001038a801b00078021040003d400110040080c41424901525075000355454007045d8410b40100e0fa002041001c400501e201d540082e203022160070820420004440300c0034000d130b010b5065400b50028100f2085c0312058103d56890f001484807200c1c050352468080c6546c2c0c03048403046918001c1c02c5000c1750baa4004151141039a50000c2c2541c040f41d120f800880040404000c11070f400c01030380c40454090713035800a090307142c0c42c0c06074001d140c0d00c502841c00401c80c2c009c0c0180640242e050100f0b1005864005050700da000c14185021038024040582c0f807440c100c03018102401800043d01d0204400380480c0844070f51604480501d4410780b80e42000a0780c95101c061b448004460900100300030b86000c1c0c104000f001008400002c20f103080d0340000387c0d0091194002c0b90b440344e00081c1241142002041581c1c08064030000b00181860100411070081c1c80500d060009100e00440100308000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 699223219 1250 699221969 699221993
    0xa050a1e091404030915051905070614070e03010b0f060913060f170c0109060f09030b0a0e0c03121206130905060708010519090903020717010b04060e130b04 69
    0x181c000180205442403108000e032001c1503409034000f543d0442c000c2102c132120b52130203401042c903540702842d001500307145c403040c884004250300402c0750810004020075143c2c0142081e114801e0340180180c105914050b00c003801c030a0380d0701e00a034104803940c54940c3c0d5030390f1801c0e000e131402e481017a074948034400050842800c0d41c5c8135540d00351411030041003802c03542035400141c642c4031190740980703013107041981d40e03414035040c40318002420100280442c07449055400072001c401c0c00c001800545035078a080030a00c04481458801d581c5410320b4000890421044c10480800e4024002020300503010501d10702c82c4c0f04510140c508088013103642c944640e0f60300400408020000c00c0040ca007481c0054850034207807500e0001a512200102da1494050407018841c0400c51212005030b241007528009171640c24401c0e401e60140640c005580305040118661181c2c0382c400018100400c2030411044032025008804117842c62030402810400701c0d181d410001c1e80008a42c000c581d9245080750113420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 699224469 1250 699223219 699223229
    0xa0213050a15020d0305060609040e19050622031d010507060906050f01050906031e0a1a160810030f0606030203100f050f07020d0c170a0809010b0a050a1e 68
    0x41c081000040d0382001c00c144140d2461558266426018103501c114282c850943c0c603d940000100200c0c4e500c1c0c0f4107544461422000d240c03d079420700700c0114010000080808050340c0507040b0104001014005c801351107011024204c0da050540f8540c0c8000381182d000c00200c04007142034098003122680928150750495074021818401c1941c0c1c2e1400502520040e03809001c58885940042a181b9003c0c032041d11484001d0700416400b6080121140c1c88019141d907a5510b0281c1000c01c00032606c400c0c01c07911042c0300ca22074a107090401c1045250480702d0b4503210810420060244800080d41504e0501204d41026554000300d000b801e0410007040300b0b90000b9814801c1950505040c45c0c0b81c1c01c0030f80980c86c0710500704101d0782d6810b600031000c8821170f1102d005130031014030000124020142c10203078034042d00c41810041071030702e48074040341d100c14012804100c000d0204000c002003405200c1e04168107507a4000c002d880d00c00411285409400303102800500d0351403c418034014642d400c1c0c0104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 699225719 1250 699224469 699224479
    0x6250c0c080a061b0e0105270d030816020604030801050904141501050a0909080a03090516060302090405180a02090901020c010f02090405011a0d0216021e0a0f0e0a021305 75
    0x840645001c60082590080b2070b040001c1c600965135106004184294420006031209840c00000c410b50707004002007000c2c402230740c0c00110241596034990a0820145901c0390700e55240761f0400f625403811600060030240e08640c04402040002a4408c130018111242902d42c110103450f5890803456800788400d004049100d0281b4440c0600340401c1c0c0c0d50304895099400b0038425481d07825007820b0311180b03000500f0000f42008605071040c8070740d01203800070740144240e03900c2c00d41600000d8001c05003944003800094021a0b2006145082d106454211010304164a0900034405130951102c1c00490040e101c1c5541e54005400c8110070740403101d0400d1010020403201c0c00801c3c244009421000d0307024007842c540f40010507070031009030041d14036071650380241d0b00b01145052217801030350100e0f44c0704400000d00040c41e40180c039615508040ca4188401700b144001d015014804485030543c000404c0071b80d00030302045000d62500400740c004243c0b04000d0780d0f80d80803515050400c51503500240d046 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 699226969 1250 699225719 699225733
    0x1050a030905240703061a0304020a08161a0a0e090901020409060303090e0f061516080d0f14060d11040b09071107060c080d0c12110a0206250c0c08 65
    0x1d150b40502c07403860b052840c801c208840d107441901703d04039a020302a6040034a41c0c0b45400403482103240285501910080c000b00c589600c03900880d0509200c0c030400340700d080c1040c000b403000003121000c02a0940c200c8558505001000e0002414400c030441540e00a40050000c10703240e0000b074044070086c00c3c048206120040e0b507441c00420704c0d902c0740300b86000d0454210200302810090141c3c5806040010070401c603001140e101c0007150703842115500502c1c980002c0e00030004109201800c00b0007001d010014445160a441d90141c89548140101c0000008100011581d4043c18045000c3d006001e9415107201140070800404c01035407403942c428420000c003c400d40c1d200c11210700301c4103c003050700c1d000ca554080554454501e02c0c5c005003245428011181030b2607441d8040300003481e40d403400f0150008248001c00c112084a451012a186c0c0018001c2c440c0703404101b425084280301c00b9280500c0d4101408140c0318000c2401102004009080c10040c8180d60450302c2c058400354061310a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 699228219 1250 699226969 699226993
    0x110c0105250c0803040603050a09170c0f0d030b030c030d020d030b0a2301300f1506022802090a05040201050d1107200108041220030408150c0901050a030905 69
    0x985d412910034040003e00380030003d003850055008461081d079200c52001144503e910301107440e5040031041d4421441500790001140c141045199140da4260310009200200b41c001d00d42015400e440040c00b950103030030f40c0c09480364002403884503d4041d140000700b185602000030a1072980d03034001ca003120080c0045500203144100045a440c000b46c03207000d9221f0000003a4207401100e880f1300741d500200780007109000d1030300e074100c0309500c403082c2400150040f030a000f0040e92090354001c0001030b4000b107044410344007a640c0242d5a02c40401c2e86440944041d0b002817104403000342080301050319040400c085901400c265038840c500d40d4014000809420080901038012500c10b881c4a8003481d100003452429014541c96001c047c1d688045a9990340c07583c0000501d42542241042056691042404507000b03640e04146140300207103a032a03203012071f82460701c2100c0304011140301150092106002444003101c0c0c0c001828244940c80706003490060b0014600f529000d40180920049900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 699229469 1250 699228219 699228223
    0x603060e100b0d0c05060702120a03200c030303040813120303090c050108060f240703051201050316030f03020705270708060a1205030c0708030a110c0105250c08 71
    0x14090074414000c1001e94006010456100c0e640600680030340c944600900050410b10300600245002419085514840162051070001c0d01042500010a5902d00f1101c003c00c4441078209944010014060300b1840400242c43e0712020788014444103001030302404100c515003400004049007404001428800e04014014046152040383c110b803826001003007941c001e00429008d15405411344864010071014018030840c600e201e03064000354440b4100d01031501600501003240309583c0c45031180d6142c0407103034120f401a04104d100ba04520b50840480b4a0807007880d04498001c501c0312100d03980e03414242c2c184900343d009a80c2118448005171140310725462000c0382c40400300d1550413135a5903814202c500410598449a11082d1410200410f04d9808040e02d80e0380e0094058030300c1c1100680400b4646502540100d500781c0011070356108654002515070861894640a030090012800000f8081c0c4201c07111548906c000040e13082d071140141702040c401c40d501180480040b07032200071440d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 699230719 1250 699229469 699229483
    0x4150b0309010e060103030903150b04020f12010f05150304031b060905161404020c0312070e15120c0d15140a060309020609010f02030d0212011a190f030603060e 71
    0x1010960900c2008154240f00081890480c1d406a460441c0c450031580c03044000481d03030410007000c58903091520041d41d100e10041101c04900c401c1180c1c3e94001ca000c070f21080ba0160710003c030303960b241d0004001c00d071280140c292103049030043d07003556640c5d140360a0711071100f03080b01c080800314200040d004014103039205130681c034041c00c2150110003032030415000b44446405101500d5030700e0051000300d41004d0b0050521a182d230001d82c1d08009103c5001d48117050304076074580020b1245600e0440034103283c034100f00000f0005558030b01e4205014040414404090115180204c000a0030003d00709940c1c0029a00c03103031300a9202e04a43d0f52080500c1003116100c266200780c00c04100080c1c094024410800710325805060b0900707041c00080150751001541e603400341540010403412988120384c3c03000300852840140208102e50600c0106480c2c9644400720901d940c030200103541c4044142a8100310215561174800d20f07280c02c865040340038298544c002840b1504044070b240c15200041545 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 699231969 1250 699230719 699230731
    0x40f0b280c172a010f090605150907142109060109050c0c0c040509070e16030609020903060406200a021b010903030807050a1b1a07050a17040204150b03 67
    0x8800c0c00710124040d5032943c8a190b0601c03010b140d0b0a1583c0d001c040e0811106000042584000107502c8200c0381c3c6403055942c0341030102d4a1300c0d42c4604120030620130510203c0c4510059408802c645003118020309480690f40020004e0400400d80b0508045212800421610001d44041c901d05001100325a902001c0c001d039140d031403e000c00144002e80303840c181c6488100800050100007100000c0c800149800780c5001c2c914000d80ca00818001c00c05243c51b8000c1221400c0e45141340720180006080302c103e504445400760040200752800d940009400f030308035400c10000110180303d82080015100090311640c100f40c1701090058031580c000c110f10b5043c4249000c02c070700e11600c100046403031001e507000007008a2070050100d005148101d02502c049034030741c2410046424404d00f00c118081083c2000ca855440913400c0980300000d5070383e096005520f13810102d082003da100098051041d40b0072a07000c005c0820002015503903280c01164076a82c000071400003103501d50b04031425544c01141c035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 699233219 1250 699231969 699231983
    0x90b010501020d05040302190503060c0a020d030203060d140a05190b060a0605030106110304050a030c1430030d051e010e150108040302010f1a040e03040f0b280c 71
    0x540e9400415203c0e22a9a42c0e0390f0b2901e45410b641c02c0068403540034014035100c42e04400007080c542c03001c001850244040d01c150646601180380024a13008070214200d04050051007442403c2d2180328003410800d030300108120007003a001200da0f280c00e4448001038820300c03076900388207041c640940f0041c00480c06420054100c2d40c4000600c180d46035240300ea113000840c05c00c0100035841c1704490f1070101f0320602060b01c3c038150760741000480d4480e4a820903262101200010404210302c58402e800704001903803e80c800da118002c05500802400051240841c20b04817007406a64090003207450310750440c1d10400042c03e04031380c123040001950b5030b407040c1540302c00000b05124589000d050b2245200e203404980c0180e00500444174981c0c06401101903640b211100f500582441c0690003e03040d4134003400300128514010842650074412002d01c1c0c58000704820702650050740e18110964200c41310a0347e952508454041e0240c01c0310100380e40e9620382d030740100420781e4084c2d4003842d11809214 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 699234469 1250 699233219 699233221
    0xc080c01030905060c0318030301061709420109020309070b03040804052202070302010b15090603060402070309080a0507080d0e0108070e0406090e060a110306060324100201090b 78
    0x80194101e41c40302401038404d900c400300140c0c0310f40c000380055900409554440140b60302040d0070500c2c0da0005c3c0c0142001c0351001106600440e540341d2520350003211140248041c00600024240c50b1094804000078000c0f54072001810468010402c2903001591a80c6041580c5d00d54514000390010344542d415030290060020388c0c0342c1d0302c0c010307a0700941d04038180903c0c0c00c0c509020401d905440e01c8008260f5804440b80c00100310b124405802d00f540070743c00225110144e5000c20099140203400210540410300088040740c0305c10090f65440f40080d0340041e0358003800c3c2001c2d01c0f402d08540c0a0001881840000000c000010865604031050a8201c448480c0f11501c15541c0f0b019001c0000d0015900200040072203114486042c0304800181c000241c09442e046810240d503580022000c5641c440014404d18400d20702ca41c6148000300d03261207065050000020b43e0303500c0058101d00710120450340e07032810340b06903d0a0014201c802403015800b0801070318080c0c042d0001d20f4080d10340400000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 699235719 1250 699234469 699234493
    0xa11030f151620030304170406120203180d020d0909020325120507030902010210050106172d04020f040b090604150305151609050f0103020702010201020c0a0c08 71
    0x780c10714414200404100c0c1540c401000300c01101d881285041080b01440402c0700e180c1d0080364420700c1940c1c20000c1d66881c909420540161041c644443c6100c8808100402207035034800e0074402d07100410007015039251070b2440e8407480c006c1a00840405c42c05429072000c412070b00041c03440c01c030b8000c03901c0d840ba8030741d607034013020040340030442e0341c00c1402001c0c0418448001d90140100544411781c01c0c80070101c40c050308840126032003201c0ca8008680c0c1c40c40c07520700b55030301080f0b06d40100c207101800b40019810907030001d00490041b040b884003161100e002c6040312480d858140c07405082501403801c06202021030b0440c030710b000c0c9c8041e40982036111039040315003081d0141d402c034108080c00b1100c041c1c0b550b1080c0001000692841682c520b0003040100c0002d5090000e10f81c80d1942c0f44085a003824441f541c07401001c020710901e42848030400c2c003003106455050a40150394070908005840b03000900042c2d01a00c41e415040240380903a0103054200038001040b2000d49801c181110701d000c0400c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 699236969 1250 699235719 699235723
    0xe0c1203130f0605040501120f0e010c031a03151803030405061915150c05010f0603020f0102070608070804290403020c2d0d1e0b060409080a08180a11030f 68
    0x60f001d21000070340108070034421035000c0d1740c00001c016004500040e548000c1c2c1440700442c5c40e20020032019075190416429816810302514103089540584003945d11200000241c0e1140c182920340701c0c80b0f090703100240580240c0e04803413540071685c0b030680b41c1c1c80c601498040d440ba40701325841d10724490b410b841c00000c0d5400748a4840c585040443c0120300c1030424046129041108010504100c4039034003542c00180c0030300a106200034526000f048141c04e500c1007001003050030840604660141404011103503001c0541e076005003180c1062403081e1114100301d401174100011484805510f07417440012421012040f03072042e4025400d0b1070110002e40c0812101300c000300000c421044200303100c0c0c10449803801f10102900c07030041004801c0407442d40c407040c20403296150080031400800084040c821a2000c41d5441038085408014000d04d40c2c3c3c881e41640180001d14080200d84000038403060343c14030103041c1c1d00e00800e0841d00c59207003528003c0070b180c4032285550300a0103414464450301c480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 699238219 1250 699236969 699236999
    0xa03060b0105040834050105071115070f020f01030912050a1707110706050a141605010504200a0f090b0a03020a08101104140111120a0e0f030a0b0a0e0c120313 70
    0x141d44040c601895a100e0003042b038081110603034414a5064403120408611000f414038900c00c6601000600c11401000b849a1041425505150400b948440002c001e00d00d0a494800b4030b041050320f5101181d0111642210000040d2103042d41e4800d0060940c0c06c0042101d42203100011a1301664031103034110399078080c00800c0c0c00031420300c0841446003030b03600c40a0100c0c2552140706000c0881e60740c84107803c0d82c0b01901d0a9854a4000c07400072110b00100103100c80000041c1c1d0310000052030310000071480c0621344a000810f0790354040708699680c603a1403010096400400b9070503521b85420141d0344036164103203050740b4140350244038100328442c94166130403100755001c40107030369104000554a600400030190018060f0600204204018401520750b44800741d0b9010159200d4030309120350314459a0300c46110340d100b60300520004000d5400e07507500c061041400302c2e0100d11001c651785840c590000d020780c052400b141529201c400080070348400201010440c404030b0341d034104a030890311 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 699239469 1250 699238219 699238229
    0x602072010020304051002151602070b0c0715030f0504081c05150906120d0509210717100609051e040b040b04080909100504050a0b0a03060b0105040834 67
    0x42808100010714001034285505c819a00554a10181e1008248e680d40ca0032118080c3c020141300c51104590b504000120150824443d00d515104c140395000d40c1d80d242a101e1150500c00e44d49201049900ca40c0003004482042c3d58140903500705480c003003001c0d800c00c02900b0080c09007142d4007a07641802d03001316405003051112454001d64101c0520508400040245820911012290240308000c02c0304030002113030b83e511a901e40b14004200300840c940091882c031404c00c20828452081d00110b2000b00311440300c90001700a40c4a400860b040c110280b98000c3c109207030800000306040a0f03002544500410846400d0428091665010300b00c03090301d018100340c1c0405c0010b00060001001143c105020740800c0b410142e9003800242201001c903080e1381704c0c0c0d410100c02c02103800c250140c0b50f00401006010700504d0100380c0032501d01c0c40c2c180703c094403007900d070107481c4c070030b03900907000c4401510413081510001d020900c030494100028107020030034140c20840000c101020300c00c0360f4040e21 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 699240719 1250 699239469 699239473
    0x6180318180c0c0503070606030b0a060e0a0b030c060a05130e0f04030c050106030204180204142202120d0504151407060b03120c0d030b041802011b060207201002 71
    0x21410304050300c0241041e0406900388103c00c0d456101048040002e0016184965404140c55055241405031440c01034076281056090020600c9103002e0031000310b03880001244002154000000040d240c91442c11903507411036800200300c180340d07500038000c0c040102d1003071800b2a9155980c0390b01d448404200c0e81201859108804680003030310503c0c40c502400d01234000840e0781620b0f030700040c0841e9a815212042c0208021841c0c045080900440d20700b2018030340180315524040c0b12644218001868010460280c016410110340d0b8815400c3e16445030f2034201c6821010200010700158820b0003005482d074580c031400300240c1c2c401d85803a0003129011890908010040d074440024080d034001803581400303400654142661540050520b020f07105008141000d2125070203805c0343c40d5148910b02441c01d090110300c265041c00003100d6a42da0a207004824042072115101880e8200355001b001c0600000e404001d00c8040340809604d2130500550304076400050701000035001c40000c15801503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 699241969 1250 699240719 699240749
    0x80705060c030a0f030603150b030d030b0102071827051b06370f03140105060901050c120d0c080703050402180a2c070e072a06180318 59
    0xc0781c89900c141c4c15811035428089841622a81e0f400322040d2590840c0304007a41d80c10780c0080518003005114499071450078200402d00090000035140e04e09401a107010354001c0c8100d0070080080c0e031000a40c400d06451386400000c0c1e95609c403104c11000d5105695506c100441082e0200030340502d0f0181d1040204134a00e032400740c0908400c0280f0301840b808000200c11600c20264100761256458601c80d5510380b8070b1749240c01e001404035030b580840941c1e250b0003900148106e85a10b421182e9103442401e00d6610b40300782161280c80c01c0841c0032007004250b0007091000150301b454101e01038511180d1124a1180d0303070904100d08a07402124041c0d844107010b002c425003000c00305405900f00c1a64107002c507450404038090710754541d02010034640620200c401c3c4034000e00078030610000e405410f080410604108000405100b000010781c15000b402c2c80380c0061391080c515a100003950300079024403070500c0c0b4040302d09400c04040019808601c1294101500da8010f1000c602910302003079004000e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 699243219 1250 699241969 699241987
    0x317030c090d02040e0d09050103050a02091c06061203050309060c091c031b0c0807080d0f08090a1a04060e01020f0a05070804030c0f060e061201030f020f19080705060c03 75
    0x2001d940075803c1c1c2c3c01668a50341e01540c0d81007402a14602c0c0c030241c58164009142070001000c817034005010410061041c441c000c19aa034125000d161010303207003203103c068030081c24454000e06442c0d10512600b9007c1b041d002c10140c01601541c4103041c41c5040d1200b60b52036500184a501c0f803400c046a00802541a20f09030100c1d00d500004803034001c0c0f600e1450300d91904280f02e40c02040b51000e44c0d40040c3c0100c10080702c6070820420740540b454001811044407441c1c0041c0c1407541c501d60b54010f10044200081e5000c6040040002690f00910410b60142a0300380384072581e10300395401e869003401d0191000c00302d0414000c0b81e1043c500403a0321460240d0b5982c00300d4480e0480c03001122544400c020010100300e4950b4008080c01448054040051a1101c0509000707154a4410b010721800d02007a03442100b84180c041c1180d40114030482502501e100040d003e0104600103548105a49282e0035102c10355a569010307680000200d0341c0f810740342c60821209000741901a0b001d64000c00c04108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 699244469 1250 699243219 699243229
    0x10f1406060c0709050711100608060402120c0d06050403080a05070905010c053a02120d0c0e040c0908010c091503020f040f080d030605010813030f020a020310060317030c09 76
    0x40c1d040c1e4400241c49900d600c1d100380d0400d17a0810745170100000c132040d000b03030034006061040394a80c2405140401140b4548400701e41c8542e030090000e442000801024101490706202941c030a62004140c8150001245040c100034202aa010303800201540000303550888948030b0603005000a4032595400751070800115501340c10024101d0f85805402c0e1010003442c020041045202d40d10303c821110050400c00408000301d00a074001300310341c804040968040b010100326200300300701c100302281e402840b0f241500c04441086041c0e030000e18111088020990082d42007054600b01c0b8003d000c920001e02045541c1c00403401080b0001042101120043e03000381d00a0024880d9480e086081c56500d00b50715940d2407456021100907044030115000e20ba900d0700c80d1801038082400e00341ca017420b102055000b01441c414001303040c4030481f01d0b1a034005001300001c0a60fa5070080456005800e001a540c3c080c00f031303d1008076a00b00c4800001103260b40d0003010b1301d10911640c2405818521039508100c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 699245719 1250 699244469 699244477
    0x6020904020412050c01140f0316260f090d0e27070206011e03030f030b0402040f0807080708013e0325030b010e06030c120117010f140606 61
    0x5503006508102c0000c40e00c14900d1418091801900130303105001d4030400141100711b009400d680705650410920000810301019690400131001c2c010b102e8550030f4005a40e5030614050784081d2038036040290079000b5544000300d02c20f0035400c19500b0161100019540c0c0d0329000c480c0310011800c0d042014581e0f051403241000b524040714010b0846042c000c1440d80034810031b6039980016013003000184a44102000c2007011002c040301c0705081d441ca1510000e0004070b45c1e400c0442015151038604443d69500d4058a001d000700c1c1c80710b600116034520341190384a409120b191020f010f02000090100c42c10b1040e5540e1012025076091a0204012540c1d80d8211501408a02c01c0d0600c244100c0401414082c51046c0c8100c00034070300040000b10443d0240104002e414201402e180c48214243d0b400350108a40c510140c91141e180c0e1140c8080310b0407401144080c11032901c0c2c1000001d5900c030003e070312003010446030008100b03a85544480b501651000c01a0303441051908011454a09085000b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 699246969 1250 699245719 699245737
    0xb0706051f0e2401090b0c010e0d0909060f0302151e13050f030a030f050c0c1807080a02040f0512100c0801060e1e010507021210140c0a0206040602 65
    0xc5200011008804620341110340c114011140441040280c104055003946801408042c00c8078200d503da0b000003800c0c2c604d60300490080034404255800102425040b440e4214860300c1a54681004e182004103090405d204590304c0a0900d4000104414011075240541e41c01070b2801420b5208280c2c00303182540302e4a031360f525003c0b811040410340440c4a003d05424411495488401c5140c06d040045503400c00440f54801d070803080015001940060303c4641d000c0c41d41c20040d4455600c0c1040c01e00381080c03041400c0e0020000b111156046e888507400f5446030805485140e201e0311240c074076104a0207036010b1081165801e5206210a2400902402000e9a10300498004e000c50b00d00c40400c1e12a8917881d040840e1651006100454010302015010181a5404000b591401072981114618013850505004001440e6000d6440d0780300c42c1002403014400301c440c0c00b01000320101c010103072680c2034410180b0400100700a0480c240854044800a50040900c0e4483d0345950009620181c65 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 699248219 1250 699246969 699246991
    0xc0d0804031209090b04020327070e310f06200d0903120c0507060b0d080301150207061704121e11010f021e0a0201111b0c0a0b070605 59
    0x1000000030980840ca209032107580c0e0b540545030340741c008076138280c070009042144910b006000f001081105800c00c2d00142300d40444c0740d40a1166440e4450510051750070504580d510401005070540e01c811741d80740000da05040ba2100c110780103c0354103107400320502c0108180b02c01c52075040450020742101d8079844510703408a4a0120710803d03006c00b81e0101c81001d000c2c98552000b03106154001030030100040300a4004c1c0551803158038014014401e0000c020800d507903030225641e40d501d404c810b24440960081c0c03030554030758484010041c90b40034142d09030f0052041600c0400c4907441181d0072101400c5100c1e028406481b6651001000c91100c18903004002040204104e111080e6140d1018482542c41c1d80e0180800e640c5030f50300303458030142c0c2500384900410820b99022441c00712040360241482e0025240e61310481c0403070240100c54179111f5189004030b0500c018800f5074000d0740c40b400000084401c051803540a22058001034403c40460301001d0061300b01050490300440d6002540c010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 699249469 1250 699248219 699248227
    0x9090e031603020f0f030f040317070212030711030313060e0d0510020403051009050718111201050f0901062106050d05010527030304020d02011707020606210c0d08 72
    0x7014404144540d100b54016401090400d24101c0c2c04d11028200c282071501662410350701140158461196101c0140310301c001d00e520b401c0d45039566050390b508581c0200090100d520640806540380c01009080d19614465036480006180010448003600610b1710600881450502c0a45c0c1d0b4001520041303401441c00c0300031a000507418040882c40c0c807558140180c4070382c11810010f00e0030302100c100c81000c524102c8480e012402c00181d00007140c0c0005049010410411442005094100804e50b1404804142104125007410f06241070f00c02c162041d511000c2c0d031408000d5840420b00c034400105413503990004000d10000108424030581281c041070950351500825043c12002034180e03001c2c3d540304240030002d9030304140d8101a4142500c0c009000c4120b0040548038440a040240300300d801240440441e400307008070602c10301c01e040100301a1b26165030003030340390b2108880582c4207640e2030511070545161042d0402c200140003000344491040b01c810700c0030403400c0c0b00c02a00c407000240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 699250719 1250 699249469 699249487
    0x4061508011b0513030b1e01030b01051206040312050907080319080c0403120e18090105070228080723030706110a05090103151805101509090e03 64
    0x15044001092910000202c05a07001440c0c2c03103090b450040780c42007083c02c0250002110140f1405029a40c00c544403607200c0e00c804036100c581c111000c0d041614882c1c0c0380000414403a5036103240e81220700030b0b66440e02e001840c0c0255900d880081310001c001c695105c46104055405a014a60000b04c20040303600c82500d0b20201071640e0402100e002241e4600381c444170040d43d0126080360894982c02c0c106050500b076a03907030040a21000580000c1004080c18400243c2d03c10a41504280c0c2e110484042401c2558504d8080c00741103031264007510a104000101d81c040441440e1507245100354003005204540da90b45c212b43c000001030710000481d8406050041c50020213000b10450755004559947c000e26100040c0e9000c02d03180003114034203025240c085501302c000c42d04580d80920340050702140d113515200d4556026006903c1d0140e00300c002001d5010b05030700841c0102d030300010440c00e0540e102c001d02c0000030344d500b0070340010341100e1007040055940c0d04a183c3d10301c1c815080d0b904050200e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 699251969 1250 699250719 699250751
    0xa081501020f0109050f120307090b090409060921180501051c020408060f0f04150b010c05030c030405010306090c020c0d062703030c090e0105130e120c060a140a050406 74
    0x791340240c40b01d070003010590014100070488024400840c0c00b50900310300e042940540030341a00d12803241080d4002905400c0340d6149e038010540681d0081c01084000c01c50700f0011074005a5605022a80752841c001034409401501004e881c1c0703841101d1004001c2c20000119240d4003c41c011080d041c2001d0000c08001070b10b400036001401d091002400c080c0392008154a40c17400c0a80304031005010401031001040d00384007040704500c40d49e0b00215401082c1801294041201032024219000210350f042680c40003100410803290240d800340025070f01c5804003001c4030303260300b114005640840c20348501400c080f524890b1281c00b1f00000510f4400007110440410750300312444c01c00003200c0921070101030b018403652006010a240110313642c0d040849800d5041018065544200c80014071240c2d02d80c8150812111480000e00381d0f25040c0d41c40c0f00b402030540081c60000807901850000945401c0c8602c6400e4820001c81c80d0100b468075220003180080c0700141081c0c41c4070b0f0311151002d006081d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 699253219 1250 699251969 699251981
    0x11b05060402030d080c09120f06090106180e150402060f0d1b020d210908040e0426030f0406060b12041506030201050d1116110103050c0a081501020f01 67
    0x60005005245000e204041c18501d00000c0e000c280b184035003e001e0303014240e900f604c4000d18280c03610504804d5a812051410280c0c00307021446210b201c04000070004107402c03d20440d00121040c52181d1224011034080c0c64400000d01816806040840c51008085011035009400940201d00d880e080280410315030b44182040c01c12513407100700000c1c076000d060740070042841180c405841c562804130001810a01c50381031444500c000c12010034690501540101c0501d0340c0250410707070f00e0340c0d2030070041c6148600321000d03a43d180c042c0081c2c032540c40c51002140202c540e0680080d1540d03a500d00017078242e0780041c3c03050300c0301035941101050740650400101071800101d10050128a440d00e4a1802c040c0791000261809051110410040c0d13000320a4035031040c5c4000000c10365808003150300c100e9002c2c41c08a8154071304c00304d2101080c041101c1c0e450710005002e03a01408181c1d50842284420b104060a08001440390800140c404400c000002d080307500503c181c1d44c800d814400a11b0079918 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 699254469 1250 699253219 699253223
    0xa060b0d0503071101080106140a0f02030d0e07030203241602030f030a091401020a0c02040b0609030717061b04120501060b03010b090a17060f13021f020f2a011b 71
    0x61340000d13000a40c2c010242d580180403500e400f08076288028403105403030003401204d9051149506543e403440c0d00038021386a4460f1150b004100e808516007100b669680305100585c064014a00300002a40000440c4c1c1001020340d818583c060719000c242101e0b01c0c04000c504000c50005100003c01e180d0407000a5000e4280b8200124840005003401030942d000041900d4060784100004440c55810041c038241c0e0580448000805080e4000031074128455440e0613549402007600120f0101001955640d42031500303401c81e440ca0351030748000004100400d174240001c51043c4420403110083e400d54007442841440040748480d5207584080054000780c0145071503000100c3c0c07014081c00d18100b000010661441d00510781c19024100f40d440b43c4000c0c00c140c2c60881c200002a14100b0304403c2e004656a000d005a42003035065058184002c0c2541d41190050085040510040400003003500000c0d041a96125881c6000222007071012810001e0704d040c450b070103000708501c0044020841c0c000d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 699255719 1250 699254469 699254483
    0xb0712021305040c020c150901030b13090311030414090a0219030501140108010f090518150f010e09060c0a0216031101080601050a08040204090609120f180303020a060b0d050307 78
    0x280c1850300f040300343c1d9140d003900c0c021948900028038141d030303030300300a101c0b00030503252400d540b9070003180120060b01c01c04241d03070380010b06412141c80c1a60558029404980a65210100c07940805403403038880c840c81c0310b502da14030506407808109280c140c4103660440780441c80140b03008110485003d040090005200119036207800410140480310b1201c0d0f1fa860007440c00301610b606183d0b10702c50360443d42c000c001c0b5841d80d0fa0002824412071010403414104d2441c103c070442e200c04034440403004001c6404404054030100009100102000b52a00401c3e4080141982d5518204002a180c00030300820045100d41140106415414024040a9030141e044020403842c2d10300050705010740501254100402040100c4200d60302000e0640c120303504840100f5404000e0130010081c00321030750302905010002c01500700040d00455540122210303a1241c5110380c208910540700c068081c40f0290160b000f020303a00d000546940e0080d001c5842c014154605903030240c0f41c4034655040310784102c40c80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 699256969 1250 699255719 699255757
    0x12060f0906181e0320120408100f060b190e150405090f011a0c07271a03031c06030c03120e0a12021c0b0c090f04020a020304030b071202 60
    0x84210802e4801541c0c90741180c940c40d01d901e543d00108150341d43d403a10135100041c4044400171398000d118007030704a20444c2810b500d468070384070190b449084040d801c071221307441c280c001000032041340504000c4801c1781000c6402d002d101e00d182d4103800c04c0851507504016210301502e90380c0e6109181d241e00000440d2002d9226401e2000344503403514040c0c03410000b540c10b90010031880d44224003209150144655480c2c6440024007603500e80a410b82024090f2103150411800300c84084171b210004c428250400d02c1074002025549090748500111290990000c00c4141c2260a100c0d83c210700302c65070305400181640c0d5903100c000c03500c082c42c1c00031903550700d4071502c485100d50f1082282c01ca00c01c0c1101e01180c01450f1404a4110000d9464024001e9005405014400c151070343d101c0c668540007030f5680110300c4c1c05e07000c080301c55200ca01c020384121441210806030f0705151013901c0b04080d60340c001318034103401c58a82a900c4000200f0b0301007000f121601a03115503080b4000b4009405020002d4880 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 699258219 1250 699256969 699256973
    0x90606020a06050c070f1b1d09010b0405090705011808070b0a081b0d0911090405010606031a060306060c19060203060103141e060301020c03040b1905030112060f090618 74
    0x83e03e00103404005190801e10880000c0383c1a00c2c20403c0c219801249189141404001ca10101d40c050b48640c08050008502d00c3c0da441c0d840259600c00e803220380c020483c464100040004640090720850502d520084080c08594001e540f00e2400001070345980c2e0483c0d540300d84041c030708180344d04060304070312020503501245500104030a400403081c03d08030020341ca8038188c0e4000c0d4020142a44034041d11046050144070b4102040051154042c1c65280c0c0307450f080c1849806400c036403251b000024a45120f85580a0024003a006c0c4510010141c5242d80c0701c202c1001207580107107001440c5405501e048502100f5241c8058248078132440c005602c1c0d16040700050121442036071418620703407000741040f41454030349a40b111303c2000e00d10f641d1600d454070000b107402400340c0030720f268031844000b401050304618000a440842000c04865161040400080391180400e01c17910b01042034440040c000a90f0540001c0a4034946681c0001c8162840c1c0301e440035510184405004400400c4040c41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 699259469 1250 699258219 699258221
    0x1a01030932030d200403030e090a022a0f01020f18030111070b041b060e0d03271511031e0708071a0a020c0a0303090804090603080a0801090b09010605070c090606020a06 74
    0x2640030440c0a0482c20f051541e1400b23000703035021000301441582c40030b0000d10000c0c2d042e819075140d0034840d07a00c0034501d440c044c400400401d60400d0426248105101000080014001c076240118948082400c01c0354150202e400b80d902c4400c01a0725540706e50002000740c882c800a0980d40c2d015132402c00150503e0b082c0b01004010290000451035101d402c00e21100360403848103c240d0f00c0603120880c0e0420641401c461614801400c41540c0640780404420380d4260002d0310155000c1a00c081425100b9072402d403030000820084800030781042c8034001d5400c00d80fa621051614800c01c41274a03020050b910a402d82d4008001110155000c4880090715013a00e04c40d15800514541e0031860480d003500c2c1c1175035880754030f903008040540340c03140102008005000d850040204030000e0020b561245041e0082c1d40203c0620000100700c0000029198860300039284141005019010180d003800822112540304560540e9580341030f50300042c41507110b12039240200394660240480e401d00d450820 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 699260719 1250 699259469 699259511
    0x14060a0e190e06180615010507050114070c0302190b16181d07090b0f070503040e1303020609060f04031215030b0610090b09010516050d031a01030932030d 68
    0x49895440001000305001151b0380500c04100c0900b0515100c000070304c1c155003d0900b1880c0040100c00c1c2400b84142245c0001d0a4000c0390300c01c0e020f03122070781071401c0b80100c501c080110142410317510794041160206d850b000003080c3e850b01d2130207804030344043c0036041070284182c2c4201288000e4140e290806010021255041145440d201044500d03028903130b0807901a511095118880014003082082403c00c1150000d100c000500403a6180802101034103c0c91070f81e0503000b6002d110001540c42c01c000c20224412592946c45c0c26550301c0e152400c44454034500c0312002d07481e076038605c0020304040a030362803c000c520078000c2d88401c2c5001c0c170038444081485091401440180300701800054010000d990b4640c0e828038015448001c0d8055846111064982c00703852402200c420f1300c407041e4141c1002ea845a480d15100301802d540000441c01c41e5210f0380c019091030030850030643e1401c050007001031300008884003078089050b40c0c0c045034115400100c491520503a1580400f4074001c1c1c2c01450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 699261969 1250 699260719 699260761
    0x908060408210f0c0f0904050a050108120a020d0806010e121e070b1603030b12010c09050609060307031a030304140a1706040b04170406110114060a0e190e06 69
    0x5002c10705203c2202210624083c1c001c004001d0041010000c82c803942080ea070400034020414081404d0852641004000070300a00e08140240d1040131901d10a0780101c52003050b042d4001c0c4041c410548084940050240c1000c0c10084454100c85196480c40440503c0e114100b0180080c0b000c2117002c000648107000c0c1c84881d5070001481040041381d01d000740c0380c18070748035a0761150002c405e1404500924200c2c50345a423140d004031200c10b034041c05511035070100010b6200d80441c10349613000c1003a24050000340035408102080056403541c420780001e400503004c00314007107580b1941030000b41150040d400503500c03440303003004809a62402d90416001001a60722007a0342c1c401065005860315070080003e0100d0b8240d501090400c901210040030307904071048090303151515244002d15041111701c444810790b00300010342c223038110030000d0640900c0c0020400030301c10b442c00310b17500206c0d0700003040c42070000384400c03a000c0041c515018a0070315980755406440d281c40d182f44880d20001521500e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 699263219 1250 699261969 699262027
    0xd030b03031b030307020f2806060806071e0309020a090f1d0c010201060b09010c140723010e040b0913151d0d0203041d04050c040905030901090b03250908060408 71
    0x2099042c41a0004070b0319103180540d08c1026081b07030b03500f010f01c040c01d103560000b40284111801c1140c0568009900b8074140303031080c504850b2905c4084210b0540e03074406800395210b50255000c000c85601d0341d00010105c0c064010205038800240f04110386c201e541c81203001d080e0828400780050f0360b070a204580c081d11845116034201400403000a020f55081c0b500103000c07482035004000556010000100186601c02003411041c5441194144040e00c0128250100701c00091251591410b40120303a0000405001d41e900d5980d0360850307034241c0300e00c8281525106103103040d1030004411402000f501d0300807500ca286e040d0603980c0c0981e141c5a101c8403e5401c40d0424442405640600c2c1891002040380209400f40ba8541c2e0030320a003090627a060030303680b151030110200200800400500788039542602c3d031901c1c0e255102c240010307522040396483c83d038003061121084181c802d10340908290791b80d807600003501d6883d02030291401e1400d8a06a81000c000715a40f5403c290b18504e81142c1c0413402a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 699264469 1250 699263219 699263233
    0x120c020a050c040e0f3306030a020f04020f1204020a050639010911090709030309031e05061e06060a170a1506120e0309030d030b03031b030307020f 65
    0x40c0d080d01da4044400241c03045841c0c075007100340210100f21130400c11604109681e21030740034541108100c1e03052142c0d41b840e0400a0f410412040b00c0300c03141d0707120b0301014001d04a005625400c01c690400425003a5074016824800d00050292f860060702c00700c030809d1003202c00c0d800c05004010b40c1507101e40c00305203d49020840c0702c0841e25000101d00c8410600c41004243c691410316401c8031080d44020000250320708220081480700e011007da0422005583c41040381d00c500204458050300780c000a0007140b403a000420009910800001d000f41004101500040c4180e07942424000180c030054400c040f03a0001d070f0426000ca0000310341200040310100d240224881d006402510b5031080390000e240c0f4a40000c64620b55908601c480c511061110300503561600740241840301c0d80c0d80401e10f618a041d140e0729550000000716582c02e440107005140491a1500c00c0b00540481d0140326054001070285050140c003120b1000c030168011030185440f0328020400901e04020071304400d1007644202 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 699265719 1250 699264469 699264473
    0x9041502040f290d0203090705220507090506040b090d060e060702010528090302010e0d030603260f0f040906180e0c0616020103020c0f07030c090212062e120c020a 72
    0x20841c1d1aa00025130096180d941d0210481d00f03258050b031280303400010524801c0800220b4401c0101007101440041019459042044400e04410700506800446c100020700c541104580030b440b00e10401410405141170b10390b580001e49820344000300d22980b210060250044e020f001d002e038818241048504040005400c1c10940303000510070a00c0207643c0c0c604003003450320170740000860700803407000c4688030f90150318020002d051600c401d86040201d4441105610b100c82640000903081c500d540d420509901101c2d019940000201d0032044401c020010b40301c400c40c06050b0007010804404004094940b0301e5801342c621030030859060381c0113403441070107983e17403003064888141d030703d100c044e0040f285440142c0083c801c000d03283c842131080ca275681c022003400041d0102640d100f081562104c5903034131140c900341d014034244100b5203400781000481d203041c1030310020381d408220307130744c51906801480c2e051090944264042c40090948500084030040701c1c001c411213020340707100810803c00c1603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 699266969 1250 699265719 699265799
    0xa0906230d0506041d0c120c0a21120806130b0307140d0c030c08121e1e0c0115170604150b0909010902030d0c0203060609041502040f 59
    0x341c0c0007415034410104800342c07115030084104407022100701c3c40000043c0c10455440300001e9005101c1c045080003002c502d1008140078024030006050700408908117140f0401410801110f2075013007040c0620400400e107041c40c007080c1c00081d0303201d140b101c0c00d02c0018000440841e1920780132481c00c1c882e2001c007646000a420003110741400040380030321084000a003030480f0f0003202401c5a1000070021091141b28650601182c0c17002c1301704c40d044d50905080c04e02c0c602030800e00050b4580c2c3d450141404485050003415204c46000403065094040501128543c0081e1020400c503176481d810b0a1400d040058082d000d00140d4540000d1403450740b80c504d41d02c0038001d0004240c40423010f0a4000800c05401500014000030100f050078903001c01c09500070010f141d002d0740b00b80700c1c80d04150281c9001c0d0040e85a183d0300078000e0a4980d494005200d003421001c1e20486205414850754070190090344041d10192000f00c0c024080c0b1840c00311009119103a000a0111078000030000740740e40004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 699268219 1250 699266969 699266977
    0x100c02011b0b15130c030b031504051504030203120f0603070e01150e120f1b0a030c0909020307050a0618080607050a0f0c0507060818010b031b0a0b0a090623 69
    0xa0140e071100c03081140041241c5029004c1c081c00a541800458040e054150b00000d4143c40107500302c0c0c103410070b69071007101a60720a81c0e020740b2030f42110321103480d8600c0d5000c240e0f80c02402401101e1505400c1c4054101c80c020444001c5000c1c1088400e00c0300c14941070010300d0007071816840745409035040806c0c2c6400050f805201d8070900c012000b05080c9a26044002012140c1e02c0d400d998038105010312940d102d00f1000c054440c01061080348170300b18036189214505498100143c900fa443c10818480001c1111060036a070601c0b4495002840e941e230301c0c0500c40075007034541d22072008049000c8400c25204064000ca03d19401c0181000a840d510105139504203002d8900141c204440d09030641c1c4003001e43e14003030000e024400000c078a071074101d00858000c01d10030030180d0722144001600c40c221600303008555807507000f2107000001c0402c41101d036401e41a0061800c480103988012901d000d500091408020400002080200700d03048103940d81d46180600510041d5400b40300400600d01c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 699269469 1250 699268219 699268231
    0xf031a01030c02070f030503030907090207030806010305070c05060a020a1704020f0120010624020c0d020405150303180108090a050303070302030709120f060606090b120a0b100c02011b0b 82
    0x3954008040b140c43c800c02c070180003400b050350612903054913400c0060f244c1c0c1c02120303480380e10b00c144107000410400520807030b241d064040ea98042c440e02c038600114043d003c0900381a04010780544030350007207801403011900440e1007910040e0f0321074143c4005410201803503400c030362184014041101588036221910203000c3c007464401d1984080340d401945403d201c1c03280070101e42c0b80c11004140f8800550b25002d8005640c0c0d190107100c1d100c5d92040b40d584981ca88900d401c4080307484120014186500061340214006202040c5d6010782d8000c203141d500413900348404070640620794405c03035070401d54160b0030515803000303000b41d1002c3d500e805a50b480060a418105580080003d115900c03900050018200f403d020740e40358100d504002542c8006864140c2e21645001000140940503404070000c4070300d444241405c01c01c03206504c545400005080301300710350311402c4031425075541032001c1441c001203884813008481180001400e5500244042841e03000d00480d031008251301d1003055500c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 699270719 1250 699269469 699269471
    0xb01091409040609080a08150a06020d030e070812070b1308072a03030509041506090302010c02040608240a0902010806060706060521060c030112080f090a150f031a0103 74
    0x500ea500c1c0c084010320302040c01800c5072002180c40039003070787d21050050242c0381191091040080c840700b044001800c6100c0d032000343c2e2014024404c001e000381c2207625050304070b100b40d5006954400f20f0314104440e64058925a42c00080c21404202c3c1c10003529401c030510242e0711400c07032000d07074910740e040c8207410018040a0807042c129900d69001034000f403904070407041d41c640b1555a8070b00901543c000000207449541050035144580c1038410352201101d40703980e00e14138043d1540d0015600c42c03038402d01c00c0c0c0e003041e21072030041b82001e020030603c4d84134540203001d0f49100d03005604d43d0312000c2014111102b030608150078100540c1c0c0c840e944941040c02200e8056950301240350107401044c0c075901240c3c0060541504c140e015a402002c0859500303148140e64407507848402d00d000510003401902198600d20411402092100010b444c2c820307100032001d0300e00f09100c0005020030009a0250310070030000303020750601c03941c0448002041c03101c60505110500a0703100d100070094511320194105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 699271969 1250 699270719 699270721
    0x803030106140403080a0c0b1303021b030f1e0d030207050a020909031b030d141303050703020f0a051e0102090109050f2701050102070e0103080435100b01091409 71
    0x200b2490402c035001940c1c0003c8160fa00c1e0301c0030f400907100b0008824144c44c255140c0340001c02401c810800007403555855800703060310f281071001c06190340700c020301800d406116111310942d00070410850b070700c11480d80065044117281c0101001e0700c0c010703881091904140c014083c0301b001640024082c82d056078115410760556448808841c514003540c9405505900004800c4800300008802020381c1c00b0b08010510020040961461480c00162222100814600c82d42d1000c02d110b14041d200c01c602c240306640340351841070811480c004001c002580c642c0c00030000c80070b03001c0c6400341c3c50851081030030007582030081960020b030a07480140326141c054507010500b1801960b400201101c0b51459038648a0760348805101d4041c4030ba42401407031302500c1b03140d001040110b503000398141201d0384203207400e280509000d010744480e41816014103414242042824002c401c0c1101c10030001c05410048c00c10880b100807110540c0e00d40d2040c0c60621000380e40500c88040840d4001d0300d004019602c8001c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 699273219 1250 699271969 699271997
    0x61c06031127130f080a1d03150f1e04030e1807020303162106030209010b072d020603071715060919091103010801064a0109020a0201060f0803030106 66
    0x20004d5441c014112400040c200359040c3c0c1003070099448080f950f6840c0107080d9110185035482c615900352503806800c01d00000c450404240442d680801400e4100702040601100c1c80d030551000c0c1c07401c90100b861078410380542d0404030032181103e00a203003806540c1c140050069120701c006090700e41058020aa0b90603480e01440f192802d05480c2e589207507450a0b41c0e00c21400030881030100302d229500c403500002d45001901c06a480c0550803400d0908481401604c50740017860700c3c201419074103086090080507a40c0c0380c000d584228040e49441c02c0d001e10060703030440015001025030754072002c000c0c14100c0c40d44982c020350700300c01001c5d514000d00d41c4c58030f280c6c0038a0740d2450340003224190400e4081d4060349d1402d0040d504032180e10000380b200c10703150904050603c0d0501c0002568082014014502c254134500007030064803083c0401120484008a80c041514240c0104810710f80010b00049559030904c90354000302948181d0f240c070641416100b94aa00c41846060108000b11041c9a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 699274469 1250 699273219 699273233
    0x30e01110d05090f090402010503070507110915030c03070b0a200303090f060a05060f0d08090301410a0209010504180b040c050711061c0603112713 65
    0x2040c0d5080000720350529000c544020b18039404034080f503004e01380c2d868281145040500d51140110343c141c5896086036240c40085520b6004804140e4107a02c0040410603e91a00010903020301d00241100c2554a4113206262400043d1185c1d2802540494003c2010882182c141d500e59801d903c0c01d051402c2c180d048090025056000c41c84040c00000140060203500050b00c100000340307070003501e007a59101d003000000c03254122500380c0c024580b4a1640c1180c5418116101007506c00c807203007406d215101000c04e0031a21040144000e001c10303060700f106842d0f20131486001174101c520324102c00344a22040090b0041000d0110507601d500447c80281036802a426200903100c034405400d40318010002d4040684680000240540e01d000f1040030b00074410401c441302c01d030300600b100c1e070310902c50310520001d0b510681002c0107141c4210b8510f03182e442c45000d101d0055010320000c0303a041d01c1d52400c001143c100310581c01e1011030681c0e61944024a501c0c0c0f0329034448c0030200040c007841d1150a00c0700b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 699275719 1250 699274469 699274487
    0x10203100b03090706030221010810050709060f051e070b09190201020a0b0411030d0804110402040501051602150706090b010e04020a0e071202030106180819170d0c080717040b04030e01 81
    0x15103032381030100020030350720342c005600a80000403450500040d00c40c000260340a90b294014140012140384100c03a01d00d01490003401c490f40f0b541e44800da074001450340e6503c01e40001d94202d0700404103c0601c4000d220421940840512280601c0343d0f00d0320903800070790345040c1507100405036000e22000030b0500410300c2039428507032006130a40b40e407210800e0000f040c004049404a0b03001c001d03a8000d54031810544203403800d03200e0603180d041c50041111120b503003055203908104e0344501249070364102c0380422005807050f548110400311703004507186071515203008160041850064024104400360703907000003042c2120b144407404104d036140d2a504079100311150819000040c000000025142da00030348411481c009120030343c4405440d40116130715540c000851800e0300310186551808245604901c1010010048003d8540301010035240c06481d4983c0300003003c550300008024040f03400c4860303e180321001641d40182841c0c15a0380100c10003002c2c2005c0e003048021030b00d819072030740610111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 699276969 1250 699275719 699275767
    0x3021c020303030702030a030c1416110604090609141018061d01050102010c0e03030a030b12010e030405010f09120f0204020706240b0403050c09041a0405010203100b030907060302 79
    0x1403680c0745000e0070003a50301d074401200f1f02e000901e030800d01e04c403ca1060780d400c5451518802c1092034080c9120f01107400d050b0110701a50500c01062526a05a0381c41d0028402002d40c3c01020911520740f0341d001d011074480c003202c0c0c519072001000b0040e4242e184030400d001e440d003101c540c00012040c010141d00074401508081c018020380212848040441080181203a200740d0080c03112800c581800c42d01c01d02508501a0075a109200011070f15000c2e4114051003003005d40088010145a01e09600b55004003a108910740c0001805100c1540d0140e580b021030300450614542a03031400c0349019208140780c1020708500590032407c000c561343e50b011101d401c5e8014106215602408403418032214001002e24116000788400203120038180c0c0645040b00c3d0410051b00c800070004090000303a2000400c00c075140c401d100302040410020500039400b0318002c10006031a40380c0042841400b48140e0000c0c03042d00d80500410031144800503110085e614503240258843c3c0c010303003041d2403415858a007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 699278219 1250 699276969 699276973
    0xf0c010f090606150f0f0e19030302060f07050706180602030f0604050a11090f0105070c0312121415061608120a0209010914031c030506010215010f03021c0203 70
    0x1000c0c0d595015500603000442c000c0307000308511641c2d034030000c80032030b061000b040c0480c220305d40554a490140f10409280032076820002045098000001d8107505030890300c84520b000a00c0a0080c903a0401000c0d41c0080d80044002190a203658003400c0f6000e0a0070080041b41c548202460003086140c083c0d0310642d004200b5510707810103a0710b05011090480d0050300591030000056140451409110703402d04100122502c0d01c4401c009124841a00551003818000c0402100c000070f4900400440214050f00032405c089140b480020404200010f021241901300444113110004049003650014110600100c400345003d01003200380c003650f02c260100000254800e42403003040001480c6004e05070031a074000307560300c60802049000b0842c19900050030390380c081c01403d00912804040c11001000c60340310b501f000360b60100c601d00714942c80c1e00180c0c44000b0b20040d56010800b00d1181303a01d519068603258142001c02e0120040752001a00c99000425148107540811102580894000d02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 699279469 1250 699278219 699278231
    0xb011209030318030c0308060f0d1e050604051b0102120d0e0a140a050c0402031017030c160e07080121080919210b01060c05150f0a0e010213030303020f0c01 69
    0x24040c000140c5c5510030340c0401c030f40400045403440c00b00940080000f000304000b000d141c41d91918400110315000000f200145a00c04d50041a020031515104610510040c504a8160308406010110001d0282d05542c4000d05010076040c9000940d40ca020288100250034a1340d68280c919080b130818028241c2c2817030b452021303d840c001090b131403441402078003120071012035a0280001c80c4021103406014100300e140c06c0c04001c2e00d18084000101002c012a810f100314200d4490400d00341001d111168190503408001d050180513143d0ba0080c954240071045614022114404100d003640f4140107442d1541290100141d41c0e05451250a0240c0312100e038084480c2d0006070041940030742c000015040f4200b001c2d01c04244010b02d8aa0781c0049065016440d040058401072486c0d0700c226558012041c4041c100382d034005480b48a4248041d80040b14100a0450000c072284485000203a0340108445040e032981c1e40a15000c481c0d140c5401690340049820b50b40301c5000780d92031540035500b040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 699280575 1106 699279469 699279473
    0x30308090a0b0903120f040f0204050711030c16081b0603041a090a1202070602060f0a02130801060f0b04080a020f130617100b011209030318 62
    0x120484103588180e9844000820b01180c3c0c15507942c0c0040f80c0500c502d86a030030301a030000d070005080842e0341417035158900c0038010074401a0050351541d0104484074410302b0501140142c850503a0b844030a810840b684a04c010340c41c0c81c524201599021a000101103806009461a4501c041c40342d001c06c0b05002d41904014021f03100f1280d5024204001c24402d10030501c15038003240945940c02491612007400744040f40c040c0115480a50140034098001860580102000c07136184102ced40c4444c041c801a1142c00c0304042c04031204640000c1c0d50805410420a4403441d0400e407985a1b01e5081608850045110304580356024080c1c084c0982813054526000003805447c0340c480e00c4c034580555051350078540c000020724040041000c1c103010140318502c4460007a40381804502c00400000700301801c032400380d4251941e148070300c004143c0664401c2c00c601c4044603880416817164 = true := by decide +kernel

theorem cover : BRFrame.Cov 699100719 699280575 := by
  have h0 := BRFrame.cov_init 699100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 699100719 ≤ n) (h2 : n < 699280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
