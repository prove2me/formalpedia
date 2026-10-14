-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1692
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:14:39.640783+00:00
-- url     : https://prove2.me/submissions/ba9f2e1d-c523-4a08-9be2-f900c0c2477c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 304136690 ≤ n < 304316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 304137940 1250 304136690 304136731
    0x1e0102120d290105161a0a09030801060216060e04061d01230f090403020f10020c01050c0c0a0b0c130312020d03150b0706060f0b1905030411010507050f15 68
    0x481c0c40c0b11008540456000c0109280c00061110b03032504060203000c03503203c003450088250002c0f410858101c0c1c0030540d10382021080541000013940586007a01c001c162424405950212000d424006e40b4140305640070121a95030302e0350081d00181001d07140301c6040510b07106407030440d001c0a004902c103d094103104820303549541a40540480001000f00020030604020f0202110b070241041d4214026204040d02542c003c02c441e0403a61400c0e000180d81e132184103242802c4a00181005642820802141c0340080300064860182c54112100f80c1c066143d200700744050b882003900a03601140c22230000401c0c4844a510a500b201880d001d640c0081c840c460228200c60000b4010b59114404000c240001e843c080701819202c1d01c203503800a401515080b501c03202540c00d5000025030b8200140e525580d4022001d032040042c140e0608600b1401d00c1e80e02c0c24414100140203074104013000ca47d10f01403090400c00d80107058149010b47e540500c514031140813000b0111a004200710446903001e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 304139190 1250 304137940 304138001
    0x20c030a23120601020f060702070f060c021315031a0106080a020306150d0b0a15090608070e06030a1d060a060f0e0105090a0b030d0504030605070801051e0102120d 72
    0x100141c1c48180076925145003422035490045003d807900e0304600c1882e05482209100700020b034010314181d00180340d4a441d0210600031081d05401074001c01c48042111030058603000c056a003109510f01d00407609180c201c00001540406174400340840e28030100c0360009810881040f4180d521079510380515a68414816041c4c1c8005e0329215000b000d03040103245c4841c501c0018144144901c94081040a44480020314100e4036801c1902c2c0001050b0040c51056041074141009015509280c3c0c410318000f070018180c1c102c0303d81668001c41c0000000794850242c0c1d4002c1c254002004080d0b804d000b109029180d0700c4104070744038150246082c1005c58140d4403942e100b0100c3c0c01000035000c59a00f007409100400001600b80d5011a441d0242c0d040155007e00103500028400c0d610706881e280385050a20a4941c040c1550003441582c90040c00340b622281c0010101c01c1140f001c6508020003400102e2421080e110082400300020070020803a1000c0e40044414051050504808610208040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 304140440 1250 304139190 304139237
    0xa030c170403020a1202070f09020d1a010c061107061e0608010b06040315060317030a0c0c1a0403020f070803070212010c050702090a0b060d0c0f09080c22020c030a 72
    0x64056403040111100140940b6541d2158880e14410b40d820588c3c0e4001c42c1044150a41003548125004110529052101d200d0301407110391020340011744800c0390740041e219415045024000d251110035140800c4080002c4500e01d6070300800400c04081c02e407441009510138080e900b161542000c0c40000c03000814020362030744a40080c6110300e000c1c50359841d244d100301c1050f915200c0503116040000841e4802c0484501e01d00e60311368095803031503c03251400444040c9800c001c28881050203c0c404901c0a90200c2900d01854044041649030341c101a850301c80c00d007403650f08505c81c1c2c40340403410040c0880500040c2c0c2c03080c1c0d8110072000c02c0440e42c45c01d80e0072201200c1c00107a41801b48002504d850f6030059040104540002880103150b404291503500c030320844540b203a1901d1a4140c115840340440d1024055072401c0c4149504001e42d080e103401d400c54049218015080304068030510015a022262500b688110f640c2c0b080e1901c200d0322600032084a001061480100c1e0841a0000d4a42d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 304141690 1250 304140440 304140443
    0x106030b090402033007060902131b050a020c0306090706090611030306010e18090705010801090209030604080d0b0409050c0a08031204060c0c0b150405090a0203030d200a030c1704 79
    0x9010300c4138002d02d51000200d1030b0b2010f03044c0c010214245c02d1036002050003c0020500850010605d41c3d258014010305130750301238100b10128540100c0191808130400b0051150302071340740c038035503c1c1109841280340007040307107900b07916020b000c09001d21034000151400c01c07640161581034245a45090648800841c20188143c5400801c00a40305612520180c10740b140010465141c0c0304c1d840c1c920b900f04400c01c40790b01c0100c1e130000d0130511071980c004e2400c0b401420055420b5142010b007001013501c0e414003074001031149034003298521110390702da044030214000c0030b0400c20200340c0d5130a20710b990780940d40f0b13010300400c58502c02180765480031080340c8a0140306102540184c4481d035605005100300c2200303c00b0464888030b91700002d202d0b0640d140c021090070b8103201c51200058100021141d001d0950400c40d8004010740005860201c1519120091a4000100c000d5074440040b103800310302c0440041a100005e200a50a42503405009100c01c0e596070034a005a02003102103c2c1c2105980 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 304142940 1250 304141690 304141693
    0x70b01030204050c0c061008070f0308090409150f020306130606020d080c070b180f19020f0315010608090705240307031508070515030c0415020a0209040b0106030b09040203 76
    0x1800035080c1504004d800c0440c3c8218180780c49844400c040c01e19200f940e039000440e2054500304840c040030007258011340011140b0843c2d080c0f0310740c2c03808410321407e01a68015500c440000c2c2c10301c0405c0211300f50644604400307008281180c0c52000003940304451b5644207184401002e202c0c003840d4800d140a840741c80e002003145261000701900d1440c0000d02c4810759040411100c8001500211028040c0241c006a11070303070304208401c0c0741031401e6440d60b820194010b0a0704a02c0c880b01143c1d1420458047e82c0c405159100340c40444c1c2003401401c02209100030900000860030752000c920f901c9030007003005443c0016100d404110b98800c01c0c030031a01d500c40207c42a10242c810943c0103603040360311401c00007010403464800001450f0f050380102040d4101c0d01003040241041440f909962000c03000e45881d52406141d60941070040e80150070045040381741f490b030518001c1104540039500144210450f28003854008001442405032100003410901c0300c1b8864241540c48500496000f030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 304144190 1250 304142940 304142963
    0x127110105030a0e0a0b0106022509090203010b04140f0c0403030f0516020306040503030711011503060209030313230402030f07111608030a02010b03030408100b0f060d09021507 78
    0x44a00d600b010304a600d1540c0d9545860f00c16070f0041000d40e096900c2085020705a42c0741c183c0203130a11f9203103803101820311500e8415502440c181c1c20004103544848400040c1f0005c1800428010a00d90040c0ea030058941074039840c518080c0600507200f6400c2200f800c00c5590350301100c2c0c072907001d1884000c0c041010008103400f480e0164015200c0381240300c21002200025800091619009aa040c3c070359800c0007090203450b1b0750024942030b00006050003802006081c0c14003172141c0e0b88a2101800e4154081100e8040b40e0303051085412402071a801070100c29128802d000144400c2ca0500f0b140f1001241015070504203030003981d00c6a180740928484a940d07102c0103483d1f4098000c05e00722103000310703e58010140451403c070009881070900071502c88650b14806400c480450000074401d40c021f11003000341542c000b0741010180c0e6041000b08100c00c960002c00d10001a88407490b40c0700740049800000b0902035882408064002c0366011110081d40901500910a82c900982910f0020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 304145440 1250 304144190 304144223
    0x80105100905121b180c070f0204020a1d06120f040204090503030c130501030e030d0911040608010e0c0904230114040f0c062a0c080102030705070318050a2310020127 73
    0x800544540f48c0035010f9459103520950001d800c80e401218454082034580c03810a00c940c3d9050010b80b440ca01c26148149492034400c4500e280d404000c0c0481c040741d160340000f03821919550000b02110354400e0459489090040b0b5904140d00f00e40380d013141c0c00b000007400140070740c802c1c01109450112400034518060f21078140b1805403d14000c1038483c2e0300154554040741d00c0d41c1c85140300509041d80009514210510001d0801050800b11846440d40106000118000081d40b14204100207d15006101031012050141500001d140440c04000c0d040005002c00c10340d90448061090748210700440d128081034680f4000500061091000c00404010013049006103641450040785a401000d681d02c1c089170980e8802c81c0c0c0000003138004903203c41055009802e080501840f040040041030030035010850f41348281c8280c44030b0446041010081509a89665500d0710b005001d58a100d03100d40d00180c00f030320300f4058010101811102c403060040303c8484c5da42e10785a015003c0221440b40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 304146690 1250 304145440 304145461
    0x105010c020a23130b0907080709091406030609010629070602070f0c0902161104150305011b030e03091207120501230403080105100905121b18 63
    0x2400e10407030b00986042408203407406160100c0b5240545040c00c05019100c4400b4401090070b030070b480e41c480c503040c100d80300e81d1030395001d80c1203030310420b0ba14011b000e603601c1d008200e6103559540d008400300d42c0303004100300c4206d6a00c41481c0c4504c009404403401d5031580c140b13082c01c8520a1048e0031616a540c0030414542120030b202e406686210300a070341c1000c103207444441c1245d10140d41210745402d1840148104603020444100510b41c0c19000c60904240f182d1280b14003070900d400520b0502d10307201e01c50160745ca03588400581c1e1040610009032035181d192040c020101d01c4410341600c040d40c104208003910034083c0074424040d040196080c412080705105015242c0441c40000740a8440041038010705015011036190280c00040f4180c0b00300120030729901395000c0f4005000c1001c00400010981140725036044500580300e000c1340250388107080303d04c0341c1d0b0f81c0c2040d984448100d89040c11140001040e65811241791101e051162030340c0e04125a101e11074010034580c29650b000281d040c0d56 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 304147940 1250 304146690 304146707
    0xa120e0607140c030c0f010501080106080d02120d0f0516020115050a1e05030a050106030b0f24030c060d0b04112107230304030f03050c07060504050f06070c0b1b03010501 75
    0x3c000440b82040064501c03581492a0340e22090400da6564004001c0e40c0307400d0150348001c011f609c1c040c0010500c1200b00070340711072541c81a407040450010f14640d9040540e4000d400804443c2002c0105042641d09d00a55a40a011000040d0f08080204a020100e1403140301101c400a1030311200c0d40c03600413401068025260300000e0030210b2100010103403001d000c4040700c00c1c441d2000184150852404004501c406400b04042c2e07c009010031803040d2210b100780f0f912107000030ba540d41581d003207000a0314180100c8680c0d50485d03c0800d5440c030340c50f0250806600f983c400ca9080c05a143d09001211803401107140e4010000080035611504a005103c0b15400020314501855803a000002001a01815102c11000f510b0000200814141d00403420110341000d450103000300d041400e4071410134002c0c47c802528507550350021504012040003003400e6030250701c0036142103240041001d810142c4041041d160344980100150499045500448280b50915a0341c1d003103034200001140c82c6003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 304149190 1250 304147940 304147957
    0x501020709090212070e10080304210c0504060f170105070e010807020708070f180605011d01020a02040510030b0112050604061d061006031805030415050706020a120e060714 76
    0x1362880c520660304000c4c0098009000d1954110204d424807088564895041e588405402d42003808140000b00c9415400188100f4404100202e44c0144c204600a440160301c12540030385003907000154204040300d000c0894010859400c20011209500c41c240c41c002c035842e00c001510755034406955802003000a030400e11907c1140e0585403a410b0302490020a40c200001c8480c00040400400d088000005881e002d49a0240034982c500f100281045030980d1082201840322102c50103140d200b01700303003010241c0080040c01a41040b10443c034611000b40029100811014008034107030401c500d40c820410381c004010301540d621916064010700207801100031000c0e8030300c1c001c001706008010040c02a00340401c91a105468100042c0c100c400503041800e0109003c0078500106601200361012210702e40300004240303044d11402c9400340314204005001c140302042c0c80d220254403803801c0c1c141c030042c103508101058280f203a20780d40320001c80b05080003415080040054080c52030140c10b441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 304150440 1250 304149190 304149199
    0x5030f0f070618140d020d05030a0b090a09020a0f0324111b1902060f09010203070213050108070e0c1801020309040e010e12120705070201020a060c03140a0605010207090902 76
    0x104042da1a40161100d03814200301248551952005119501624541619080d0010601e030502604043d45901042c11448144000840010903a0034503030010322110200414052803481d2041d02c2d440100500070059005484042000c81d10300c5841547d4025603401840404d090039042d128101040c0b41070058450039520740f800c104102110801510507841d070301403142012540078240e20300d8070503103c1101c61141c0070000600c01603250b2000b290001201198916590040d40b00141c2c5548910900290050622010100907140c1540410706950741202079541c515078a040c60345d000ca609071a1100d03ca5020400c4141d03010100b10500000101030043c2c81c18202c05400140840f2100e03c00000d81c2d075142c1c03c03600c1044c0000c3c86230480c181150880b4900300100b5440301e2140003c014003840902800040b0304056a000300f14402e54142d00c81e90130b000d40300c40b000c0000c2c013074481410503403490140440469503016644c040d803803d0700d00c180d004007200d52030541c42401411a03e070090760030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 304151690 1250 304150440 304150447
    0x207050a0f030e09090309010507141504120f020102070c05010c0c03150204030302010623012a060617070501020d030f090206040b0403032c0d1410051006090305030f0f 74
    0x1030741e440c0c841200c050180e1200042c020210081c40b4038018014058011781e042004031400d907a030480141c442d4030345c102d0b0064a003445420101890010b80807400c275480316905081008200c03220022145051032a52511550300319a081a800c1c0c1c09003031801400c03000c0f1071005022a5210b6402603603024060105d20000981c0ca0715441048407501035501c0c01325400280034014544c090288100400f1001c0e110310340d04031800c000d000f90b07080c8001020f04200341c0c2c90940700342d140078034122480c6012002c9400c0c0461070314074201c0001c0c40a4464060030b1640c40750031300b01ca2000481c140040341c0f0103030060308107502400d0084000740030301c0e204203207482da0702c4606502580726080036201500c520101c042d5101d007541400352078100a03408000642006464400d000c1c040818482e0850764165511448013540d8602004204002c1ca01d101ca035110302e641000c142100b5801840c051000f00340a000d50a40707c43e01160030020501011b44140d00c20440005200c540310001c110503165404540e08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 304152940 1250 304151690 304151693
    0x307030f03031b120b0d0218040819030204050406171e03040803040e012108090d0201030e0123090115051011030c070306050c09010f210e070305010507030b030304090207050a 77
    0xc03042941c1c0f04540c00a161940012000b100754071440b00c4191003103412500610a9500046801015041e207010803040c66002c201013000080660300549619076501d288080440001002504540703d80d03032081d0700385000010044958110b80001000c400090007401c202c0c041208582440700d0176070495440100b000142045060000d040500344841c036011855250400416016181c0210320035804c2107001c9003000130f408072003120000d05040d198050f2280607400180e00905020105083c0d035401d000e80b44224403882d035010361160784407545540958840c1c0112070308984000c11040114062400d003404686460340940c98140c0d0303c0d25041403251810643c060640c1c104032140840d56204110500c1000110300403142e000c50350f03407143c3d4185070046000800700202d07080c0c0c140c103000e5960103491810410204c0b0402c44000b054051141107801140c0c56a160b02900c0191029460980840c032400c1c4030340115501460014015070426040000050084d484082c040b90ba40c0b0900b5402030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 304154190 1250 304152940 304152971
    0x2d0807030503070501060b0406170c1c0e011413062705100b1503010302060a120203090a1a01080705011b060c03050405100e030406050d06030b1f0e060307030f0303 72
    0x50240d0300c541c1c00b540d1030340310f585030180c00d44d4015041120000b40900050004070b030701030800b100e040c80a01c0c4540c495280e802c130f101c0740c910807403040130340e5120800c02000c1c40b0350b40c94000f045100350401c02042480000c040480b2420001c0c4c4000090a1401d0007900106d100d6400040142d5171a240d4441303c0c04a070318140a480413245801c80c1c2d550081c0c2030740c140417030081c411010342d200e05440d64404400080760041c07041c4014007009100d40400710701c250f1614032402c47c0d1000c0c1c1107102011966814492411543c0c1c81c90107404460500c0703120f000701c00d84401900020b04940c4004003c0c10b45a040c03000540d009114101c0242c50640f040c615200410700c103000d10664804503482c0040c4500302414a181001c0c800081030b0706403030400004400c13682c0000100d4049030385519084e03490b4545a0503442c050301041e403005d0101c900003020322104031000b8000768500c011001c10400d49540d01c0400d998040304c21507489915401c123000420106140e02c081080c2e25100b490b002070950b20305103050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 304155440 1250 304154190 304154203
    0x20100c090e100b03040803180a0309140a05090708040203032205130c0f120b030312060f09010b070807080c0f0c040c17040f021807050c06102d08 64
    0x40014034181030802021681c00c001e50b400103028400b0591240c2010401841c03032002500091400c0170010024640c030807002040e0701403003842000d9803140915403c1c021300c1c50b44540030724128101080780b2240c0c1c514111001104582001d800080070380e8600c0f6094407442002001aa010f00040090b090201c0c000886001103146032940400a181000184801400e0001d80700540310b1a1030b512111141e00107406441503c000e16001148402a8001030043d150741c1400940610000c140c843c104003025400074425401035818001f40c41e00714040205100082c032468404081c200702d08400304484c0c2c0000c0c81d0941c000c0044a19290602d10200d07c2e2409592040d0144e8100c3c024245080c41c00740520140d02e90300307281031103000412580c24084a500980018074540c2000050030442d100e4010403848103612100b490381602d4080c00140031a406280704450740e01418000402400c18032080e0029111207800074410215990301c400360140e184034020500203240c0c0b02c00960710710104800d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 304156690 1250 304155440 304155461
    0xa0504120b0703060605270f04020403030e041b0c0809041b0c150e1f06080106080304150302040b030c0903120c010902122e020c0607110d0f2010 64
    0x280040380707052140101150304d244c10000c200402044a16002c05022505c4201e00c5010b1102203035860740e1071b00040c0701100101c40103412a002043c004103041d0803203a400c4000c003080d41c042c441c0d082d03031030f280d18405007680c10802c0200e4284000540450300c0400544038804002c1d100040e09004014440c080f5088010500001401c04c111101040301d00f1a0a01e0f49203007448060014010b50324500d45c5449022903c003100c200107900b20212400301d50814802822884000c02502d504d81080d281c495015000b000c459490090903c000c00b4428400c40d801c541c5201e0f1300310b007541c032200581d601d1540250261603040c499103070f0300c0c020300d115003000b0034401c40540c000103440321080c81031104500041010302025044010040c03130310721a041d40e070741ca50514101d40e2a0b200300319500300d000070300032902c1b03407030081c4990410828250b800c125503003d4200c40d14120355018040d5803084403081c61071081c440000c1c2c2000001c3c0c0d231103070700380340103503c52413142054481e12540513084008030380c25050b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 304157940 1250 304156690 304156703
    0x2310050a1a130f061205060604050f010309141c0206010602151509070917011505010e0a120503090405150a05010e0310090b040b0907030f0803060f06070309090506010c0c0306020a050412 82
    0x20f0400c2469001545602402440c1005002d246407071800600719006074820715020340b0120700402810382c4a0713402641c10380d62059001c00100da0000344142e0f1502c61400028880c0800145070801d580001a864100ca40503402002c8210340698462612000941000c0810ba54280328070682d545e034105681c451303ea40e5441c1e007032191901c02c105031010401c0e1400310b00c5074900400c1aa610710842503da064450030309105621600307103008076964a51907401480d498480802030000c00c0008070040143d180c04480a1140c0d45903000c5850f4a0041b450700198010000c4c1030800075540510000c0d03a01c004014140d6047c0111010464281e0702070710401c0310081c400c0380030042088062800f05806c40c00610081010343d080d0b90b02c150070341c4a5954007601074100400000c205a031614801500300401400305519031590b8500038065204a0041c4c0f00100d00349000039075a544030710403000646da000171196042c2c03459515190004d40c04440f9241c10801e00304000308050001d0303603200003c0e41c8600c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 304159190 1250 304157940 304157969
    0x2203210c11060106030204080714061207030c08180a0f050718061701050903070303090827031b0d02040906021e0712090b0702061308012310050a1a13 66
    0x200480c0c00d100c2d05801a1003414814802807080d0700303000a801080d14106041c40d21083c01d4080080d80a014802080302100c043c0002c03c07042c4c03a80358000c5200e44070641c0b90400192a08503030403000c01d540c1d851000403076001d8040304010131048442c260100d4050019141031030740365510b505000003051202b011081d154403080000701d51040183d4002e00031007000b0410b1341072250b0803d8491296220103400c040c1c6400c800c509002c6450200d9121102c030044903090550110341e80303d141c601050000b407080c0103801225140d8040c03501081c4203c80001c00396aa2810290b00f040000d0400410647d00303a0750900c41d20030f90a15820014130b6a4110782002501c54400c0c1c0350511050760356040c9402042140c0804020aa00d04825501c406070304607605a00c071080c40302c05480032402035000d1541c1d58288500c0c0311495024941840309040c07422885150f40ea5054007205110705140308107604402640c4040260703d943c041c4104000c5556001e05d40b0340910041550200c0c10346400c10051b18a10380c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 304160440 1250 304159190 304159217
    0xb0a0608060109020304080f0a110339030301150e0a031112030f0d090609150b0a05150316090e04031206052e050708030903030105092203210c 63
    0x1045070600401029030294134520b0190f41d411054092400c1a165203003011440c0004603000300d400d50503c0c0b94000c00c0303949444041c0211600030030403009114500f0581ca09a02c81d20320480c4c8880c1c0300c04d039444015407469103000c0e18030000040081107601040300b4032a880441c0d5a80c400d4030b0000390f00415001080d220b039801007050907003031810b203003c20303600c2000460300342d252038000d0301c80c1040410400203004105003060000380904150042040e41c440100c9071882d042039014116040095400c003c1c0b0b251034106100c001e00c0c40540c140303140a401c0c00003032507003454002c0201c011400e503c0d01c0f829203541c80c120380510307900546086000c15114410243c03500d1480c46680d009003804c403115168104406032182c4070910f404400007100030140c0c81101828025411501c006600c0401c4031754030320300030380c0d03660b202c3d0028090b0740d101c0e07188040400c80b5000d50f289400303050300111300c1201260301e442d0303025a590081c81385681c0001d44c82400407108001e00303200784482071b08240c58100000050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 304161690 1250 304160440 304160443
    0x309060708060604030c03021005072a050a0b0403020402070204111204030807090b030442050603070f1806090e060601030e030a020a0b0604020705030f21040f120c0b0a0608 76
    0xb040d907406240240401c10214483d8200072080ba074040e60020003034500c0e180c04844a00c90300708054406009600711040c440c03046880c1c40081111032804189280e150000c000c441d5002c3d1254004070b49080c0320030304c09441c0550040c1111440100000740800400c50413541070340001d69543c400201100130041410f81040c11140e01c42082c0c50300400060070404074102600028101810394240082030f4001c0c50110000082000080e000c40300c0e0706000544210411140007803d0245c540c02e1101103a01c50800040f1802681d15200b9240b40315420700600c2c40c3d51010041c2c0c24036001d9100c0d000081c5555941c41507200c0590700801400651401400150580349030050304c0798998810415080500d5020070310300e00e00790b840702c001c00700c0361261000200071380207030f01000d000c0340800224041108a854001d190320080403255a0300f440040024903c0380c0021500a041e4a03070301d68813000015400703541203980e0461400c090140034281e072036018850104070340018400340d0755002070220440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 304162940 1250 304161690 304161707
    0x40504050619050613020a02160b070507090b0d120c080a050c0c09010302150705210a08100803040635062e0f090305011407030f0c090501080c04080303090607 70
    0x401c00083c40141444400b1590f5244d8105005203c5507005c035a980700d0900c207110409505213210b0403407514648528100c801a440b90800701ca0503c195040068044924010319914070340042c54010240c2d6192600807140e05000d15070020048814080e00c001182280504150031a40da2880c4d100e121280c2d407149481c1610b007401c0d100b80c1924004000682d5400b800c0c2d41090761500c2403e441707000354546a440c1022854103401003600400c403002000f041ca002810280003c2d503941d1100d916242c11800c107407405405292440c1e0000c01080c80580d0084038040480c0c40940c0c441c070014a860f00c0103180d21403141003a1642c3c0c401c5a4180251450200178100b041c20300403103016504d1800c04042460280d8102c02041840004c00b1405405400741ca003800066030010028092650102460310269008903601000700c1c1c50140100501207642c45403101c042601d84803a0301d201d0508005447d1800024604400c1410401010444034402d102460040710130385d005140f181002040580800e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 304164190 1250 304162940 304162981
    0x228021206090703060216200405160804031412150103360c1a031e010518100b0f03010f05120601091107020904050d02070b04140f0d020405040506 65
    0xc0c000030074410b4040300803802d001140e1340320100680d200c2c401005100340c245526030262540e60710303801008440e41c118140628030341d81110b081240340c2d00c003101c1d0501d613445807080703074002814400041d002038081c011011240e60b400c6081403c1480366003c0b0382500c0c40440b01004125050810000556018019035807000140d02100f0b590b1106010a0961101003061813800000c12521002c1800600601c0b03401410004690f04e011900c408a1661180d006032400c201041d100700c90041c0703a040c8000014107803140144603c541c242940c030680210b000c060301d850652541c0c8031001920003040320050440e070203444c0640741c80750300d0000aa48640203036402207002e0440c0c1426042c140c00d002c15911b0540ba4200000a051460800026840d0041d243d000350800e0006042c001444800144003a2600241d421194000d40b82e54800816004500c500c101c010713070200c901200d500c4c14424101c406100500341142070180f07a00050140e41041c0d0301501da40d0804428000032006008110202d1b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 304165440 1250 304164190 304164193
    0x12110d1407060207110306070503010e060a0501080a0209011701060c0618030903020919020d060e0a1a040c020f0d0e030d03020406091208070b0a050105011d1f02280212 74
    0xa038180364100c05184540300005142aa000404104005401d4043c400040002d01151184e00d84800060074a9000f800788988500804000070000c1c54070351842c1c026154183c1d81c81103603403501e0000001a4100401c0b090501426100d210107500d6a1091f0a000b09920303070320b266180286081410864003200760841da064031001c5080046600b01003040101c81d4140c0e15000d442c0c0c0c400c1218203a1140c1a0007071180303a8000500d802c285800707034000340c0c203990881d000c29665440f02490a01207546441450580b054207000348042407920b5400f104d81c2272a2170040e1032a10443c0d082581c1080007000c90f590114021303032015816400c041044070110480c2e402c085181604003031014082d22050300c1100c5181052100e1003040159400079200e0742944000c0340700c42d03030800300d4040000d05001d00415001500013001c99111014004065010110181c900399101e01f41202c00382e1310040c00c81d020310a42c4034200865094844201415500160402c0c8101010f9814410003154010702c070b1190381e05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 304166690 1250 304165440 304165457
    0x516050f0913051005011d09370b10171515060903010c11101e1a0607060603150c051207021603051e0d14090a0312110d 53
    0x154640420068010b88000d04050401c10940340c11440d1050880103541980d04040000505000d040c0c0f421501c40200c165200343c41c0d83d101c2500c0e550b05c0703051001c07000540000d0186902500396078603d00021000860364561342c2c0071521001740ca60380641e90380b032101824400c01c20184880f00d40c1402c191203140e0150171220651580782103601c2024050740409900c1d5003d2030a0f550b1400122a00420094001d0100404d019006007920700c40c5001120b440c043c0f8400461041101c0c440d8a550314604084920392141004c0600018030705580c09468480807880090001c1d5a10b10250403054803407580842c420b400d41c07a01c2d4003445038840542d200d440c106056140034942000a640324220210007050203079885910480c07804003c46411541ea405098011041c48404240d4104070002da03071811070a070040c0c00716680d6601c2e49401c3d180000301a01e140c6402c80009200900315050001d00302c0c3c510340e880380c0315081540e60444021011994100d2031166400c410700030000000800e0420311a1f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 304167940 1250 304166690 304166719
    0x120504060c1203150801020a02071712090a050d050a060b06030c09010804020a0504020a020d021908070b180303010b09031606020601140402130902221409090109050604051605 77
    0x400d6603000300030700d41040d565a0050082c401d80c003038013001c00742101c0e8240550303560f03071058002d605c64003c0320010f002e81c10000c00c00e041c038465550740012006000f016540c07002c8003102041d400040103598008424580000c035503507240d40d45a002c900580c0600101221490b110741210100d04905000300b00500030403052000290940c4e00c000c40a0908248035656840001c1c00003285170000c0360b015102003000440300d54001403e0b100c00b080c0d6021103422100007031203100c0c5020200710052011608001800020354507191041d00302c415001074411041500200c5802c2d03410907004100b001c800460030100514003000142c04100054008011207810032500946030807050166500d01d0700c038048107482d5500c881e0304440d60303440103c143c4400030b03448244200103507000494201440500700140c100d026500d4200000b11485801c0200d040300f0040c2c184840d0300d02c001c0443d0115566504034034041141807081c0d07442544100041c10b41e6070f0a011340b100b84170b03a840d04000c2c000e0b009943e9105 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 304169190 1250 304167940 304167947
    0xa090b1b06070f12020307030f0c0e030c06070f1106040801060e0a06170a080307050706020301140a1d070e01110d0917010c080411030f0f030408060c090d06090213060b0712050406 79
    0x355100c4c640480540c2ea550341c503000340c000e0450081c5955100d85030458040502e54444034100074075200314103035410030410300200a05c2e0301880c3d0003d4070281764001c200c000507004a000d0851108042e001c50304080e0349001d41c90031103110b41d1104041b020300320108100111107106446c050040c00e40c044442070503d211a030399039501c07000e0040041c507001021444103409041620320251f8091420f6603250785824504081221505800b4000c010401d004102c0c0b01044000c03810051600480600603034030301604030f50154814034541c2c180400440c44a4410f40c0600c101c0c0d017070f0019500c444452518007040c11100c0e0080c040c1c50045a494107800541050740300c204140c001e9004650303480182400c0001070704180c1e40c012030011038481e184043c1140715002c40a041152002001e403a07159460000c694118400c25000b15408080f0000500c0000c44d50380c0114001400a001201d08100a40e040f20443d0306540140e4a4603601081c50000c0180f81e540341a006c021a107012400d041c50600003a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 304170440 1250 304169190 304169207
    0x10306081507050904060807081e25050a0306050f0a0e0a020f0a1508010905100608010303260702030c0f0304050f13020c010216050c150a050a090b1b06070f 69
    0x18465800316004208010300c0f0300142c401901004101b080107035540d000c015500c01d00d61040d02d8140c00ba00584200300320110260302090400403029000300c2482041d40c102e00b0000c03e02c02000040f030b404002c141c1e40c442e50158000b40d0b105100025050800601009840350001d01745c02e169414a00499110700780800c0741d0040d00c2d415181e150104805000103001c40300207400200b0841d81c805010800340d0ba004022504035100700404100b1030b00e86800d520440001c0d4011751010680810040001034403840f68422107004440182c1403040001f007403c041101e0a55500e001640702080501480c001400f45900062800c0000c5103040d1a000c04544c01d1a00348100510401c05404100414035aa8040f600ba6070301e0f0030003c6545002549040011105001c810380d6140f00704143c0c0040f50406411515070485004004e41c180140440b080383c180d03200440702c004018030034400160841c009405001040c1108000e01d841940f2503072964a0710000508041c10461850800b81201c4e030049001e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 304171690 1250 304170440 304170463
    0x7031b0e091c181721070206030f090f010911181501030b03160801020d0513030e040e010e0708031905191b021e0405100e16170f01031101030608 64
    0x70300190a01c3ca0041e03001401e1980310300101c4428a00584400c00086003464040c605198840f1112035907a03448041c500034028002d40124017000071540c0f4940c102c2116501219520803504550000000282900c000080458207024000f480945a140c10001d50742e4081c08500000d80601c0c02e0014241d0300030a09210078141135035000d02410580702442032140d4007001404413032007a5614412035000358001d50099110501d4000032a4030500f845400e01c601c0358140d550364010b05808020007004141c12110301249650342d408003110207205201d6400240000e60145894070613501c01d4118459620761050200203040100555002d480c040001c4003221134504018070780001c004c0300b03003180c00b2a8806903026008202002c048000c0348264041c10400769014450b6844040b100c6d1209881030065540002107800007581e040030018200203960881d1406012404049032244d0080409507002d100d51074003074005006102e4035000440c2c00302400c0c0790820200c0e1400c0d50003916040001d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 304172940 1250 304171690 304171697
    0x9020a02060a050402150703170c1602150d14040605060603060a030f1718011403010f12051002040312030b1012020307121a030114040804150207031b0e091c 69
    0xc20b01755214040043c0c000c44500071915501c0b203071401c003e00300100f42590002208160000070714286145003d484003402c4040701008036070869802c04c401e502951800807100f40081c09440d80740d0403d0302038030702c04c0860f000d816401c50800d410714506541000303004901454040080c0700c480e441e40303d00c0d0001c40350403545a660040d002d00e480c442d0a0400380400b04180c40c04a9035141d01c8a1000c1002c5d0300d030400762105d401040c0d894105030500d000c244140b5031800e6411408000c0c1c003201402906507103100e2400d17241100e040f44080d400302e030002d410aa403d01407048850101d00c0e0103100f82c6c0a4003d0407a418440000b2400d4001c241c1d85001d8640c50762180c002c00801d812074010826014154820318041c41004000104c00300b0a00c0160b695601c80d6003841c001c802078202c6a000240030700e030014801381c6458240000400c429a071804e89004610800340c001001c6090960444070201400464100140c0350044552016802030030301d08140c3c00418810300c460315440032a1000e40340d20b04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 304174190 1250 304172940 304172951
    0x1b03140c040f030210141b0d02010e030427050709030311030f09010c0602130b0a03061e03020d030903150204090e1f0b04090f0614130f1b0b2209020a02060a 69
    0x88045070031035000c0080c402c0104010030074840340807c400c3e10381040d0300590200e9180c1d060f104012404da07005040a44419001000306000c0d90040c0551100203102c460a4111051040030851044030421a00040000d145650920405a0211030720f1100c58402c8000e50400401d0f8280101d00d10400d020981404184a012000c000031901558200740720100140201c0f0398620300700c1410741c00104170300002440c0000100c0c00410034030a21100c0751192030080c20082c10740d1700b801401110070500340e06120910030f0010008107940410540440c07801c1000d62107901e0030190300d0540718100094100c5400c4580a580701401620120010340340455002c0b85001c10400410300610309134401600000c680c80d5400c09000142e084035800c11302000311010107644103005e00c0710091f001c0e00020302c4549001002c10210b545c562012406415020f0542c00450343c032641d65180364012540d00111030700700c070041d502114840c10703014010081c0c190154500b900701140292280b07170040440d003440b136803417 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 304175440 1250 304174190 304174219
    0x803070302180d0f03020d09060c08031b03091609060302180a0e070303020114010801060806071103040e010311030c04020315060c1c05280c151b03140c040f0302 71
    0x30b040c69000030303070060000d44030091030b030030310600743e0520300781c2540548901d50702854110710411020b0f04480d0700341d50f00c0701200b07880e94030380d403060780080c29409021403d80d44079800508400300450003020982c1c010302c00d100c5102c8055005080c2c550040c1002e40c80c2400410240e12152140e40940d0140280038100e6965802c0c084000d0160340c0389080710b03104101c030120805070154820381c0ba1074040249001a0380e620354003242038032a1800b0369040b9422140c0452005402880c60995241c00d00003540e0801c0e40b02c0c540300700d601720240e00a90309c2580c0c0c2c000c00700540c1011701103408065801d84081d81385182c02c82e040e600600a9005007405010001103000724504180102020300c0d001d68080d07110854000001005500509522008481c1001080e0009030742e09420840b84403040d07c3c2e50320b01c04150784508900c0c1c0541170300c20502c15103d40c1001421140d410080d885a00e803034400044000f499412420b1800000708281040541000140400700240540a08a0760b04660381c41c03054519 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 304176690 1250 304175440 304175467
    0x200a0c050d06060801050a020d15080a080705071d040212060903092205040c0f090902010c080702040e0f010c090b0301030f2405010b0703031107020a0e070e0307170105070c0803070302 81
    0x31303520041083d440c14042c40f010089640040c24444046402481104040701800c544134056100d00081580556403500024480001500700c0354021400d69100030340d100309d2100111113074084094000c1c4c80c3c01c02c010452908066407640c1450460040070a807610801c0b180d980e119855880d03100d48140c011001300c01d440403d028810302c000101c244201d042c00c5c070381080600d103180106a03c001c071403000403a24061610071254440c0d0140e40320409000d2030f4035103459640c805030083e078015844207002d4a05983c204602c0c1c40d040e42c4900001039440c018100100085410f030013485844c80204010000705440d140b95100007600035407880b40d40c3c280c400075100141c8000078401007003402c0800020b021140b0303030302902d1040e002e0746050241c042e001082041a10507580025844070003160140101100101c00030391142103401d240491405481c0040d14240017a070000240c0511020302540c40d450070301900390041400d044c4032004043c1d981e2021507500000b013460040550110b20103040c4084c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 304177940 1250 304176690 304176701
    0x1e011b0e0d0c12030f05030403020619090b090f010606020f0304051201060e010308070c050405011d060114121f0302030d03110708041d06010e0f041806020a200a0c050d06 75
    0x140200b48203081c99503150345240e00c8194030000d80104200e01704201d4501d02030b00489208a5055024191075524410700450156080d41243c0d01300d0342d80d000307100000d440000c40038015403e910003441803503010000a0f09540313281d00102d04542200d03400c108020301c00815202664011201441c004070754050241c014000c90740580c2e4903400810001040c8500d000080c5006402525452001030b200c01c14007040e14405e129075487c074a0340d560306407101007050500503001941450300b40080540d6502c222482e4220500c0b203c400403250050242d000c9450b401800b64401d104020405175140d03800080d00c420401700104240340e2a81042c495441c3c03020100d0345503691000801d92190346030449103183c0456024650250a1490082412980101600d207007918004002e000d00e61901000d00010300071103044014000d5000722513100003602400904111046603440d90280015886c00c5420307000310204a8005802001807680840d40d185601010340380c0603a282a0103a402e450154020300c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 304179190 1250 304177940 304177943
    0x1b042702091c05010c02070b04060e010e0a1d06150f0c150403050714070b09010e0d14030306010206161d031501060806040c090b25080c1e011b0e0d 65
    0x2d403411102800c2c030607001d0410700280588000c222000b6001010782c0c0e40d03050341c0141d005604085c0400c10040307208901c950090b49041c5040c001c2c034004040400d110068603000503014410410341d080443d22001c2d122a0b00810454000071a02c08444490005e4410307811902071100e00061211007421040001341c02e2030752800500403840c43d00e410b00030b050340c0180307404640d800d0403840105903072400040c20105642c004c2c1400c51506406d0360041d1101e0340030081098101d401d903030100010075000c0002c407200c00c4d1391030040c3d41c1d00d1410314002418144010722280c81144085081d030700f1268803940c5000215009250b5111003103015002900c1d00d0f20116101004500207000440c5080e4046111030281030169402d00c82c071112241c4c00d48a00c6914010800e181005109940f903880ba50b400d019640c0c4001d02440c1051441717500e90341a40d0744001c0c0307903414540c040c0750402d01c4501100020515804444001c209610811850300036000e50b00303660108000c080220b6103210b907200a603030300509 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 304180440 1250 304179190 304179199
    0xb0f040203031606020a0e03011b031e0509030a02012301180e061e07050a1e030b030714010e0f1c030e10020c0f030a15020d1d061b04270209 62
    0x70320b01131003e94040400d21000410100c074164142c101401804091207103042d03101030440d940321049000b001c101800704004402e05803444a07640312482014012100c45010350350b19900301c80045d094614003951201080d1811003000c16240c14149c6083c103417040c0c0c0d400c24804220301000340d005440794080e8007501c0d000d4842480070180e843c41d054098100841c80c80125903580c0d40c402d6800780508481c0c400406c40e080040c541070301c6508100c440104803803d00189400b00034020034138021040d000703d0701032200040c1041c050760300109400b006c0c0300205d44501c0840501c40101e9440e0711508800d10200d03004001920405010b0100c0501c2d83c00e003d8000021407441101c021b65505e03801090a0141c07000790107032600c80c00c0c0811003141684d004911a510008000340000003035020074800c682480d503c1012280318004515400b80d169455030060441d802c00c03d80c21010645002c201c1703004040104410407000c0007001d060441183c1d91030f030800c00c40c1948880030700030b4410600c865922 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 304181690 1250 304180440 304180477
    0x1e03073c0f090209040219110114070e0f040905060f0403090806060a0b07030e0613050a051f0c030c060606081f0e1504110c01061509260109060c23070b0f04020303 72
    0xc02e030b8023000f1501c80a8800e4024881c1c5054140182e915000a660080015190740700b803492030f040412400c030000e00040e00009800b0720366150b00d41040300550b104442c000000b4140010b140c0e2140103003000c1c00544014041c1820480300041c000c0301c90b8820f2031540700700441c40340249400b4503d9400302660152482e0b42e0340403c00c0340300c01c4041d198051a44500803070480800c06050040c03076002884a4001100c9520090039011303594501806030440400c0182c059860008209000c0c003401441981c40c0c644c540d0034035030310502903880c5400c02000ca801c8402420000000300f8160141c1202031010340d0786006082c44046000341c0401038168400140001e101c01d0084015400041201c003801c40140446801c01d01c1104d4881d4203101300c01d0722205072a01070710000600b81007c5c501d00f1a0381c000281c65460fa86e540f40c2540c03800340c600b5021074a4000703041107400c0c0b040b0610010350170b226071080c0ba014003581c95065258024141030401c2d11200009801c40d1002c00c00c0740c03020400c00b00c00756035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 304182940 1250 304181690 304181737
    0x3060f0c0c100f060b0403020a21050a030503010f0b1204030305191404021804080706110702041a0f03010c090e06030106080303040809130b1e03073c0f0902090402 72
    0x50108003d801c0403191074204006a003990300b5003501d06072907004043c40c1d5a0b52610101c881d244d52888100d420f1200c640000078005034040001c01001c0d44203481e030315201d40c50038100400d14051a407294080c0e40042281c50496103c1840460740640e02d41000a01030b100c5402c40014079400581ca01102803500c2c410090303030902c43c01c040e8401c510032500d601d10782c3d180b01c1c0340400e0710700e0a0380d000705030900502c07030351000503401e070815800c0c0c034030715044142808403d400180540340d0540140d801300b0b00e03031402c0c0d50160030a5903c968500c0d0040d0000d0190444864004000648500c03908805540c2500070655690302034200000806440d412280c907420715080410321a0310070016a0300c250501c0480010300d0300b45005000340d041c0010211840d440c1d811204440d8a003444040c90740c54011788101094019020024210f20b0b800b8501c200c0882101c0300460081c0310500403403030f211541d8000b003000005c80303001d00c900941d8610301c409a15962500301050181c090014160031100c04103040c03a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 304184190 1250 304182940 304182973
    0xc030e12031519150309150504050d050f07030809120c03040f0603060513090f2301050901020711060a0201090c090b130605030c060f0408030a0201090302070e010503060f0c0c 77
    0x40c0521034540803141c40c0c01101c0c0802014031186002c082c1054000401004060b0998008010000346414046000700c00d40c1d0701c0841c01f041c0d210b204040c10740d07184140070920500700040b01c80551641480c515000510360008014001c000005042100100000d54980b1003440903c2031140e0800c1460745988042c10429142d802a0042e0400c0c41404500022107a2003402075000321040540403260040e0b101885102400f0101415945010140007840c005000042c0d00d850072800140c00d0909284e68403000f9003581e00c0500451072580c0184401000314000030600c1020385030440703070301c0e50700c0c0c4201c5004c0e030151a5003c0090500003000c1000181101503801211080c03504807480c40d005c1c0c0003610018211206d5000e515015800b50302031006500300000240612402d880c0102d050a0b0340350100c61555100010440041c1d44035240031781010b804101c150054514000c40050545c101400b090391030382c0080644207508180c4c00890030380400101103c0f4144000d40a40f0010920803000301c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 304185440 1250 304184190 304184197
    0xf0103090b130219120b27030324100f12020a02210324010c170d0608060103110108040804030f0c03020108011703070602071416050f060403050303040201030c030e12 73
    0x10303030186600d0004c00c01400c00305010700080d50207504540c024603400d5210000040c20017400519060084903441c00c1d40c603000e00d80309604d6040c0300000c560340c0c5000c00e80800000c241c103600b5281402c00031251482503441007054072450005244c204003004080c1421a404140b40d0702d541d80c1c941c400035803c0a0540d010610843d00d00a40d940d824401d903071442011038a11003210b0211070440f680e207070703452040d0240b0119048078405241140c0080496240c506101e1141c00d02517044002c000740000011010340214002042900c6c05450036614603191a403240d444a41c105040090f8000000c0410945400350740103140c100e89100801000303071600504080382800709a01203440070000041002100300900390095262001c6d5040000e03d0307440001941203003008694021100e443d091180c0e5081101d12421240c241c0d0600c5910300d098140082c5020402c95103008920801090000ca480082240e40207503082c0780003d10758000540c210014080c25806054a0003903000840c21a02118081e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 304186690 1250 304185440 304185443
    0x2010305060913110f0a080c030f0a0b0a020a050f0f0702030111160f150510150e0d0b1906090902040e01090b0c0307091a040303020d09140f0103090b13 67
    0x1000340791515020451001003c8401c42c0300441c10880c1c110000311800341040e5490b00140c00300382c4c4200c007000000e031034002e10f0700700e528240d01c42d144c0904145002c000820803410100c0c007400244107281c0312000b651400510112050fa0001406402c26209904840d41ea2082c0b118440e1620812943d0364515401420187c2c80396080070034081954051408a8034410940300186501c840d41d40d603004141481a901a2006120035607050310072595801098071401c5800c00403a10075041031040902d148184030150308000501c1d61802c0340fa29442c424850b1140c21443c44075035680c0b80214040c3d40c99185009084690038103078001524540da8100c0c4810600c02c407020f008200000c114070f401c964420b0b002030300484550000c2130411607140c00a540000c00c500c2d20400d140c1d221030454541844289120965510005080040c10780c107000c1201c401c00c0c2403800ea54294689552444624a500841031141380783d003035014801d81c044d40c07208110a42c0503480031014a010070420300c84c0ca82c140c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 304187940 1250 304186690 304186697
    0x90204050a0506100f0e0402040e09120a300e03132102100c050106030305090901090b10030f1404060608150705030a0c110313170a05030924070c030201 67
    0x300341103a81e640200c501c10b140c041d100c2264104040411200086101d032504d06004464405c180e4a80b19070000b84090500307051034001c1400c05050041c64910340a1406401000078030091401503401203180556454070403d45014510100c2001c4d1803001302104d1025031881c0140c01c2d0541400800a050741902035840001c0325540ca40700e418002140c0491184028005000d010061806085035843d0351480c1c608250140780b039603101d6003120341d15041500412004212120540f80041c0c205014000100c0e0512040c118072006c248410b012603005414580c0f189002e9080f84d0617035100000c4075000180101e482c0c04c16040c0311001b01501c4c080d102d2940500c400c5c5004007000044001c1c00344105655241c1303150b44080550008020919018081254100000821001c00c0005d452115100e0040103039941c40d004444e10480e84200489015802c12818500030030000f20544282010035150341c448000d441d10320500c806859002d20102c5180412201c003400b10303510240f403d0b0307403003a203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 304189190 1250 304187940 304187951
    0x90b010e1003051002070305130320040204031a071806030e0f031204031101060f03080c100c0c06150504050c18030a1509061b0e040b09040206030c2b090204 69
    0x809900c0001d0103404050203d9100c4560980504031582c0180501c900a103461402c00d0f8a44c2c0d1840e080c189d140e8415180c0010b22207144512003101490b416483c80100c50451801d844c5075140d20664544403400121000e581700020000ca000b00304100b507484100c0c400c42c0c10309490b16800350041024000d040001d1041507140c50717041c0340000071220400306114280c1c407150f6480e030302100c4141526000d854103548440300024644048107904000d58402c4100d19258205141d030700b490105e1112030303a80303914281410710940d150004561003096400c41d0000c900340e05a45030184860103540c1c17115400500e000c00b082011002c1d8405000740320541d40b0802c6840e21500209a503404200401500e80f401b1420040c080c07004940c440c18a446c0320b110f02140d4200489124590240280100e00108401c9021900146414481d03042910421201c0300c0e140e00307160b0007203640e034000100403906044c030028841d4040c0c0c6400645852841c003401520140041140350407000c1d09014030120301440c20308 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 304190440 1250 304189190 304189201
    0x240c0801080d140c0c130515030601150507020102010b0306040b0612010615050c1903030f0b0301110a030507020a0b04030504060f110a0215120f100503120922090b010e 74
    0x400c019001c105541e440b00070b0201003203540441540704c41e080542c02d20a160100f11240c0301c0c1d0460740418507441c88005100d1501601900c041605015414480d400910042c009150304840c4680c00a05929180d80c44074032510040c1d004049151600b40d00d40b18000400082055000400303120b00000d0f40d0034007001003214003442c01d0710182e000e650b012800d881502400f240c4580d000e40700c083d014404544400109c3c820003240501c1c145020b0300026110a041d03400d400d420b02400301c2018082d002000742c60a803046840150050300d0a00d0101529040801c190714400c01c000c000c03140d0402803000c0b05080602c0c010303000e80d200307100d06c03804180982e0380b0b1841c071030180000c03200b6140c42c1c0010788000411a42082072500c20b03040300c20341c001d00500c408100160403c0b0814031400d14900742c00d200f41844a21940c1e02146580014801c6d8000150310031001d044038296400c4400c203079810388180a242e44180f003940586511860031602e8000c1940c1849003800c4004d0484e95814130855440d26034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 304191690 1250 304190440 304190443
    0x11212050712050f1b0a06230105060c070e1f0e0c07020d14030c010605090f10090e0307022d010516150912090e0a0203061c240c080108 60
    0x3456070140c802a00d01a0b07840865015034014a644850462a5840c184210b52840fa00440c11040f0045a070f1080410204110039031207200801105034414503a03070303031100c8a01c11701d42505008550065202050705103443d20304010040c09420840703d071070f10070303e0079020714604621200740300d00340600039040006240e0091810306003d607846044062030030990340c0a000d40f0005482003102c1c0d4800000480285a1050000d0131b2191204c00c0041915031030b003000c00544090140844044450f044140109940c030820f5190803a41c14500210b000e0a0f10003c040c20740c0100140a50441d580d10001908070400804c1d1415000c1003e1031244542d070321100448050040d9020501004082e13058580454420308200088030080744020408076101da1720b0980c41036401c030381d074004520303c58800d121100c1200e030503960000301290210701394503180c00010380044070700b51800407130800803030800e00b4002c10a06644102150107171200c030f5045001141c100604407240700400142c130640010411000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 304192940 1250 304191690 304191697
    0x9060f031906052707230c100506010c02130204030501020a050306130b01121503080403061e02090a030206071104050103050d02010b0603060904061806060303080a0c0c320601121205 80
    0x14500d4540ca601613481c203103c203041c0b0250205060010050f0030ba00e642d00441e44581480e14110852134550041500e40e6162410301300c08c20540d1803e00301003040d582da100d52100c807815012107900401c1001c0440c40002807044e5000903000d075000094280d40213802c200114090a400d45129101c40746000b040d904481042e282a4005204404403401d840c0c580d4101d000c62406d0105070001322556035403022141d030301541c0201d4078a40c45507078404200084038102107070900400d405601e015035850004120006a000003485401c020030404103014000c2144541404040d204010558481c10140c2d80c030500200d11740c0c01076080801d1940c0904007913080e2405040090445155038030b5075079a41d0003426030004212086951100e07030002294042c0200350003103000c1d884520050070300454100544030464031000502038003011303c80c00150351440030198882c6501a8200e0002c41c4402c50000070481420002d591042c075002040030740307001285a0060b8400c1c0c03626141055159401e545601 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 304194190 1250 304192940 304192969
    0xa110301020705120f0d0f091b1406180d050c150915160506040305070b060a030b04060b0102010204091401140a0b250212061504061a09060f03190605 66
    0x400100c004c950107603012002d0303d82d1000c4114001e007401107881b20503040781d401754807030b03840151110040000e00845000051041d500c1503402801e190a11100103042c0d0040d1007502d02a040c00100d00800c410303074800c0b032400424000c21215200d000780c00c00d1a0b540c1c2d0b2004201d445465217842002840c11913030100d400011300900681c50001d008182c0c2d00060b08110380601c0c010396500320780780015105000d542e01c40c6200c0d4a03600e0300e40c0c4450070f001e2201071004000c180140030924082c03000c140005101648240c1c441c1001c50001c0503170004034064000e40e800407030598100000750b04001590601e950684003020083d5070303104040c00800052110510502d10100010040c4810b51611642c0390b552404002c665810082c0550303002c40d804402084110301540c0005060010464614040001d1080c00715800e122007818035400c80200720808010100c1c0c00c1c4006100c401a455140c20740d403201001000d1380d6201c0c64105070700d55195044400000e40546468400714852415021000189 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 304195440 1250 304194190 304194193
    0x6061206150e0105070503040503060f010314073002091618050d2a0b040303030e0105060603061009080318010f030204030f02090712050108010b01020c010206390c0a110301020705 79
    0x7050b034040151201e900c0010107441c02e01007080041041d40b0f0805c1010f0094218000b014819031440c10020107104003030a1520303143d040500f04014074810032000c05029134520b0701e000380902243d52040c0b1300307240801d40290480f000004001c04c10a1700300c03640703420449584628200b80516000c182481e00350b80580f9a00c10311040100f17002c40d0b000f0b0b000302c400c12501201c2c1d01c8406c6d44050401030181959020600440d4002414001c056250156400110800c1c000740400e091410000e40c2c2400b00502c40c42c0254042515565958070a0701e02c00000c00d124002d580d900d0900350129001c0e9880e010040d40855040c02652001074424030848040325040500c0d42084822a030800010400c05030101c0301b0010358003007100702d85020f840390600a003d0080000307076205002c0c0000e810700de05000c06034190b4100000b04042040500710401c3c0b4045200b1008080f086031b100c03d107254000c4804e11000c950404920301c00b0101c00098a42422130048a800c5850100002003500387e108111004002d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 304196690 1250 304195440 304195457
    0x605030604060e12030109021902160306020c120d0e1c1d0f04021c0f110403020f0114070309051507051e011d01140603150c030a020d0606120615 64
    0x424020f0748142603c07020036095800c07071040b201295510350800e130418400c00b640020544094407500071024070700d44050011b0f000c80010b00f1070030400709100d0b21015001d035800080d0265080014041c802c99101c1821030b079602c5034030885200e002000c01c0241014a4841e24007060103400302c0f000040c07442503550380c80c2201070380c0b00f10808030000081c20501d42c0058510b8400b160a54030390004d801100e00c1d0321000002c1407001c0810008ad910704441c1912070a03c0d1401d8a45030740c84503422501071740e4065922854201c400001201c12095985c43c03890151808030f03203042015440200300b0100c030000c072441005100c0d8520701e00e90b1445054002003e039030026107140088070300300140c404414002c0300005860a080c000c0080c080560094030001a552000d0001201440c001500e03008401540200340c0d48441c8074242d20b180f02c024001c49000500800052101c03155138045840207041d40030203001c0965102c001400310034403140107401880c144071020403402d541c281e0b0b00c105080b07141ea901c0c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 304197940 1250 304196690 304196693
    0x90f0509030301180e120a020607080c0a14090307050d0b0f010e0c070b0912040b0d150503070302010507110301020d02040806060f01081902130e0402011106010806040b1f0b09130605030604 83
    0x4045c410004022401030200c00c1d500b450701c4c5405000c01e800c050b00604268500080010102880100752031354040c418803051a24660049a42c0c00342840d20414582d41c40ea40b100003803030066107511040d030203003807103030140200a094030983e800b6040b0a4034010043c0d88400c2e08069841f02103d190703407000d00600c1000e01084003500450781014421060b40da044c80d0f100030310107031540103401040031640009244181c100b09840b941e1031005010b004003580c1406e000002e85c56112600c8081e04029011442800780f154600c0d103150380c444014001c40d07031481c0d440c0d00304020750000c0c4200d0f0014041c180028105080090680300301c1a030580d6000364903039500d0b400b0019408940709442d80c01d0707401d2000c600003140c81541d0394043c100721a1501141d250910005001c42e00081e0301c00142e801c00801084161000100c1e1500664807184158817541c44c0d514945c0c1e0b56464004001c03c017142c1d00c8001039242101e50042500fa0760666110103c4144025400142e42040c851260164020390001c0c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 304199190 1250 304197940 304197989
    0x31603020f060c09040b0d060f020c070609050907030e0f01020c0c1507021003050a09050304030c0509011208091012051303030f0c120b01031d030406081b0318010204080304090f0509030301 83
    0x4486c1140281030396a11051a150f4404440415070700c1104036034000344441c00800c081241c180104030743d20b810818642420007107020281b028003004241a1500c000c190380c0c00b001e0041c501c061001c00021074a4840d180700d1180e0700d001c44101c0c14002c00e4400074642c01010204100c440725034019100d070041c0c980c0780c0f40403030061030001d1a0a0045560b400050b0006800b0b000500c01103000e40240910380c1d050074100701c0c0c5c00d02e042e8040201ea40a10054000003029181a20300086040f2000d600c500c04040b000e9644a030191880703840a8544405c000d5415505d105100b882806540e04002c0510b580400000711103002e121800854082c282c0700352190350740d4000d4210710b1810314010441c0e0008486420069013031625800b1039408c0401e0a00800c0d5015200c07590210a00701001d580001c150030490b1a4400600300d07006000c01581003c01c10402501103c004040d10000c03240c0d2287d82d41c40f20001009400c00c0695040c0c24080844c001450000641e410b8400d41d440910500c440c10030001c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 304200440 1250 304199190 304199201
    0x1050409051c0e150405040b030307020a27020f0a0905040c0e190807031208130321060b030c070204060f060e01080406060302030604030509010f140f07060b03031603020f060c0904 79
    0xa0401c06543e190300490b40f9400b00c03100042c80301d005401e8031141000200010780f1001c001c1580658400c1c48044056501c0042c428103c0740c8021180618100441140850f91030307480026100600000e011908000b0382c200400601000703aa8442803141c803982000180c0e600c01141c000043c40d20011610b0741e250943d240f003c10180c41d403000101c0340d5034500340c03400c001c0306900c10f44440c3c0c1e160b561060103581040d0700c2c0341d2101c202082e03c2d0345079031582d801801a28604240b10400080031140007440c00d080ea1015019111f1003085079281e19001e802031040b80c1c8000b0049000302e041c6000051008007000d206003d5802c00d48030051036814600c01150600c00040003560450389941c070000250300d05100e00c6010394025036070259203054520006d842e04840302482c0781000404000c1780d202c1d000e03d2060792503c030860707020241e60301d40905003400980810402c455040c080010105009900d10240c5d100044c0b0940a41c0d9803da540000d007600c800085800d00508002008a141d00345401c1d480f5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 304201690 1250 304200440 304200493
    0x70b040603022d0a090b160f0203031c1a191202010903120f09320102030c01060b07020117010608060409080c030711030c2403040c12080307080105040905 68
    0xd803c02403440c3c030008580c2c1c0d040b861481400c01d40000c403410001d9008096a02402000300d8442ca8403c07c0c2d280358404040842c1d01408030b4030914240c904656060048643d450724134a01141b02d44d10407070203440104903580000c2c99a41c10801c10040d40d090049181a000400c074561071012454040700603c8041600c0c8101d0420660040102c0007400862040c04d0707c407500c0e030715800b4414142a0252400f025034003d092140010351000c9a1004010301e103400c0303490160310b900500030f60240181d243d4040c9040e151031550030030b03001083c4014100080c0502c18000d0f82c0ea5414841f50507000c2642c50800c2c012080007a8402d00000c0150078281c01c241502c910440415103000c1101104038110f801c401e604540c0180b805500c82200c0c0b40801c1410000035046031903100041e4007040d41c41341ca204c0c0031007105070041c0100025080c402c03025500802040504140800302d0964501001e0395802198404040f902c2c075400440d0710706041c403075402c3d81039000d4000c0c200203010009000300c0b4640e4151 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 304202940 1250 304201690 304201717
    0x5090d030e0907030c0905062b110a110c0105070506180703061a01020d02281a040f15051003080c01061a0d0e0303040c0302090c09030303150909070b04060302 70
    0x80d001c03600c0e1078010031240b003011150f80029603814000c0004066450a44c40030f40b280c13105020315840000c0446014a0048010404101c94036400c2d42e94005441492000e140060300810040070050300144c82c1001c4011100a440c1303003883d104010745080c00b8029000e800303a849940011005040041442c06201d04030044400c0e090741c983d100819a007400701d0410f81c64140da071240032656010481031120118600281c440500c444c0251801c2e03029802031041c1c00c0d0303180700c222018412680c5a41e1800624441481c1003840c29092032024500d0b45507084819424003218165800c05ca40306e482d009090744040324000354070f0754403030b0611900400d10280740b555840b840000c248401455031800544019841d1f074842c9400341d855401c80d50810000495030700100b0402000450b6000b084080c2ca40c1142c2010032510b5600c403440a5000315000250103200000500c030854a80a402d01c0c1e6200080760035413019a0313105507a0381c0b144054460500024001e10007400300c40c3c02034000e004c01c0505044d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 304204190 1250 304202940 304202957
    0x504061704170f0c0106061106060102060c0d0b010c0c030c030311060606030103080c16030b0a2d1104030b0f04020a060e0f060307111603050601061b03081302130b01030f0c05090d03 80
    0x1001c035821106e040e072026010818400e000404202d0510415500203c240050a42440c0c2144246041c4c4030f20107941180c156500c060701c80c941e01030301c6a40516508900e40840b480c1d01d82c036014040d0714403408280d02003203452113118010580051010300c1040040c1c005411646513544119140c1c10048040d00716015010203100134114900c0402c0c004c50041c44180024140512510112811201c03207410140d800e150304e0129400241c102401c5003941940003625000b51080c0c01c06602440d00000d02c411076400c01d00810700510b05016000394003c45203a90165928401130f106402e20541d4550441c40c6403942000030716100028550004280c00d204138001da54081483c103000e100346001400882e180340500900001b04120344c00350040b400c0c0301420310300d40e2807058815645c00d640101000550300006108144d0340003410800384d805480361030a8640440c80b10041e01010481c0d03030000703141150031400041c4078010001080342540302d8600e8684564184524248040710980921810340c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 304205440 1250 304204190 304204207
    0x807050d0905010623030a0809012703060606051204030e060c0d0c0c08010506030a24060b121f23090f04031707170612010c0504061704170f 62
    0x240105414075120b68000a202030034440d0a822000614000818143c0ca400c01c1008645002400c400115002059142c0310300c00403004a50a62000780f189041020410030112400040015581600d10544060100d1034444000b00c2d4240601248140450300b58000f1601003405481081d03040c86014011500c0d01546a440c0e5240c11031029a1350001640e004611040c424105040000b81c88076100030310840c00c0040019982d088030721400b40040005074000092005840d005074110f127059101805450303036a5070442c00a8005000440b8180c50000001c0c083c88281d104661038500c980c079046c540c850400c0000044203049c0c1c022003261150b600141d41040d40c031b00c100320340b0034081c00322072201514080c5002041541c0241000d4240c041c3c22007480881908210440141280e81301440030039514a00040d010388c92074103505e1b503a9464848a004030b00d80c4038004000781d40c0551514501aa10300314800380b6480100d80160500c0e500c008060b19045e4004c000300040113802d111681042141e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 304206690 1250 304205440 304205467
    0x5040f090b071206080f060106080702010b03060114130501061409040b04090606051305011a03041b03031d01020f100b0604090516030c03090c0312090e190501051f080705 75
    0x142e80707080105a042c03c944014007818058540a4044080a4107070101c00c0d2400b140d84072018000c072010302c400078001940062007580041c50b18a801402c507030155a45400d03401350003403000b12090040744510042c0c6ea0f0200a405200e0488040e0b07650009014a800111051504410f10b030540c029280c0720040c8056880380903c880c401e000b820001603017864407040082d140c84852600e0b111504100040103030801044e507103a10014074a1076280d0f42d40d124503088848200840c035481540c003201c0c07800700a040c0e00504840200d100310025250400b990001660383d0158064003403400c0e4000e00c0342a0340c1c07041d0ba03002080415000380c0321900b029203400c1a081a1802202c000007241c403152a44044103034180034184071100c2c58101080a0851501c541d00071485500001c0e10798804a030080b40074900ca8200c06000345401c0e090f5111a00744900c4411141210080d940d12041c1070400106141c6020301e0700f0580203014000401d24140324901c00c1d10401c2c0c008110f40203108040c410351903040706 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 304207940 1250 304206690 304206713
    0xa05220e0309120a030806011209060e0d02010605030109050c0d0813090c140f03060409020f21060114061803031308010c12060b0901030906090507060c151505040f09 73
    0x140c20207940c9400358807041c46030154803848004019400b801002c2c01094000100380d401c20420300e0300e00011081b84449401802c603000300200942d1400c05103203800c842c04501d01c2e0007402558020b100361a40c61040501741c8402160103031181e040541d20803440c0c684504c000c00d03000c0c450700600f420301c2000b00d5050050801e17540244030b003644495003000701c1c50380703c000d10840252520707442f41083c5450510300c00382e001c010407450140c1e640300d9002e801c1d5914001d8401901600400704031610135000450f2412030002a402811845404008503292a0301d4040f0700f100440589041e09000a4000c0205c0300c04540141a405020800200100c00075000445015040030700010407155140d40000f03203d01d00394080c01500e14070b011014400007c1580441e002c003a0f0034600807581d85803508040c4e004140101f4000e140f44950b9500003009604800c4011100d405001c0420070f85180c50346000542d1600400c00511444086c0140124a850b5106e0340500c6280030700064007403450355418030300d01c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 304209190 1250 304207940 304207961
    0xf050d0503010e010608010e01060e04110a05040302030601050d020603040f060603021504060f08010501020d030c0e181603050702060112030e0907030e1b0607082503051e090a0522 79
    0x31800001030180c0e101900e00a4018050703032510381c441d58548100c1020000c41801783ca0100080800401320316540d41d0080c4541c0c01c0c150903021f5991640081c061300c55072051004030b009014041c000140fa250041c0004009038000d41902c0c5140d5956982d0040c0740d40403101182e460750307200804405070b11078107014884511564411350b0303038504044c40a444d9140d801444420810200018001a64081002130003d256402c0c0840c4060405070b040e19500b107600801d0b900101250090030305a8402080c00303000745a40100b00700c10840d0f00108600b41d440448403007015030f00c500d0042141049003985010114064500f01104010040000d14002030550340d5900107508c0c0c42c2c0740984410f0600036000383d000d0300e00359a030b045102c01000c22030602034000040e161101c013044c00c03100e602d5645a40c508100d41d0600f00c8444d0ba00600d4094090b4000001d5801400309508000c10301654003412685510002801003598514104c20031a0001e00c800c840720300810000c0041e940d21406001d46805030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 304210440 1250 304209190 304209197
    0x13081506041a13020c101a040e030a080c0711030102030405010b1011070915030f0b01080c012a140706021e07031505041b08010207110303030705160f050d 68
    0x40c1400e6042205950348540b90002074a590561840c1e656aa00c0c4403101c1e00f01418409030719520108500303400c01202090750b452503806c021105119022002d03080d1042da1080302c0c10090b0710303d0307009026500c0c000d0b1210758000c070f00954045002800c4c540003400900c1c1c85000b0080041c281d50f40842c1c2a600705440844007070b9100d8030360304050701c0d05005da0080c10540d450b1103078a03500307000d140d156509a02c4c4034900385580e40d0300c00075941c80050003a0304003a40d0403414200d00c2c0c00c007608e04a070607400700344107808035402007501c40c0900b50f03c80d10f0404150750f81c030b2101419401c060b20040602c20710005049940e40301100520700381403c244841b01c01800340da005030206d100210507400c0602100000182d66402100041c80020003800b00c4100c030441541c80050303959602e00c0c0005000034211242ca0502c0072100b40098103800540090090510420302040626001d6007030640d03a00007594034031302203241400501e10403621100300102c1d02c0c1c06000c2c042040030310b5403241c50610b6601405480003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 304211690 1250 304210440 304210483
    0xd090f02041d1b03010b030d0f0207150504030b06030c1302040f0b12040b0c0c1608010c020f10090f0b0405060615041202060f1c05190501030b0403051308 68
    0x2907107000c1c450b00307400542c11004407040000c112191a29402007000052441010003a0003100781c900750f12000c150310000c1c0490b4410460b40301c026011a00d074103030302c00051013000c2021a10700005035429171a0602902c50900b85401e654901c5010a4003e158540500c01c0704001076060307842d11100041c105e100d400050340c0300d08103400040d1101c03260304540d6401c81c0c20054419052003943c1030507032041e088100e5038030a072a0134040100d2403081220300085442601025400d210500c0103180880d1420802045445016501640c5400f1000742c60304190700300800c0d011301400c0342d40088881c18891009021140711643d503000090b0001d540c1510b89500a800700102030130500100003242101c41801420603140034002c1718840394960009000e4500400c00071b121584490a4803000c00401100340d5100034003032400b8000f80421500c403030a00c401504d440c1d106183d01c1c1b00d524140c9410800300c0da415074543c1c505540aa1000c0c4c08a4007400c1c51450010740d95000f0300c03000c2042104652203c12 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 304212940 1250 304211690 304211693
    0x209041e080405120106030f0204090f051507030506100c11010504030807080706150e04060218030307050a111212130b030708060108010905060108150613172806020904020d090f 78
    0x76140e03086030551942e1401b44284046050412210b5030550304480114403003039240b41809101407400c0000300944280d5201c0700809828a042501c07d400c01c0d502005655a42000c12110b00c204660000104034580c07040004a103c0c00328041c800303041030404a00d4603640399240001980b08810075110040e0110b80841088846d0140260660140785403640b410305009a00491002c01340000f010180d001810a4020f41c002144500015005083da91200420f04009454210681003292221800f00d00c0c007241e0320305141d01c2c01782e0324050030085c2280c92042d040c20840b940016100e0f0200c800b101e2000440070b1865006520512180d40c80e08602e0030000e0000d840c0c020184c0080c426141004100466a607014010036840750b12080c0e00d400e45481c103004110648036081c030031f98101030a0400411480d8180c084403460f400007004072038004403155078021444d40561031110491000301c45c8200422441e40203000050b00017000180b4015060a581048585004080358800f802c10038240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 304214190 1250 304212940 304212949
    0x603050610150f2f160317030a150902090306010b0a050a0e181816140d060908030117060c04030b040b072d0e040507080a020d060e150a140603040209041e080405 71
    0x1040c04c24181d05c40e03001c02d421907960f1060303410782c50600e9400440100c00540d0148642d0800c2c4000798108000c2c1c00801c2c0c035486420040d500510302c80e8081e1084000004e0360288c180101c030310903502651000d003080c6075240100c5000600c411000c0c0e1124041c0541c01151900080302401540a0215804900c22001100d82040307422020516146690201005030b034080c03001402e0516422600388003040550b1600000908800d040070300351040200c00412400103210240182000c0322080303402035900d01502ea82140308501006045004883c08240025500012650000301c9401c104414800c2c480080c10410080c059071000e02110300f03880c00c451354000742c80e542c48220544050140c0c0c58201c0d00507040d400040d10142d40e043d4002a0340140c1d900d280d2000c009440900f50381d1100d41000b0b884100343c4214240e07030340d1061002000020301c0c510f01d000411020f41c40a05040c0c107555403902001190b55006009650041c1144151264910180c0070400898032032444980ca81c1d00300000d20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 304215440 1250 304214190 304214203
    0xe0f0f030c0405130203060f0402011e02030c010c0f14030907140612130b090303100e07050c010f02040504181713031e03030f0209150f040e0106030603050610150f2f 73
    0x1023041c42400002e20002d42d91020424114180514803424200e5008c542245103204010340340101d03501c0e0118001007154044030040d00c5032542c0d42c0302d01030000c400030f86107010b00c001d40e400003082d40030000800c49100050400c0c070800100034007003070401504a50b542c4040000300d908801180e0044403200402586466464015401c07000440c21803820380104244400c0b10302601d02c030210394000180440b0b03c00c4003180e07250f240500092007084920003140c0b0180d003081c002d0324401c0741410051403601c817540801716001a00200d061552800c0c0710f04940142d07226a0110800840e26003021005c601004500413104803541884000c031501c90800400300c031464042000c0780c0b4010040703140705a80700300c460325114103281007807961403e14ac14041107030311607940164031540c80040001401d43c1c2550064003140d016109880e001c0c0d5030071411000c41025801207891003843c0307035540c00c0101d1042d01d0740e425090305400c007044000701105200601025031003840012584110440f15400030a1042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 304216690 1250 304215440 304215451
    0x10c03020a0f0305090c03150a0e010903050d020702010504051c030e030705030703022e050726030c1803030f0c010e011b050f0f03010909030f0e0f0f030c040513020306 74
    0x840c00c11540707010003030404100100d00000c068864000c56071420302405444043c41c402022920643d0200072030401c4d514044440410312440e000001d1002c61040c0600c0c4103296240c1d807031628191064800d28020b4200ca0026410403c040c08042100d4581e902e4151000c8800c10407040d403203c844c80d0080c0075038075030980c0b0350090300401d0040100d030b100010317400305880d0b046900c0c000305200320b0b480e40c02030401280400000342da24035880312034a81140040242c1d9003d080407a64420000084109640800030f04150002040002400c0c240c10070000c4c1c40c0d480a400501510a05220001380c61a008000019204940001c90300c400382024030030039009540000c02400794107844581d0441c0d90301080c001f2814402d0018501103100003100841d00d8110192180c0350b00c0303507101c01d8610000c0100c140c0450201d00e901408003076981c01094901030841008014046541100e000d01504400442905815108164000400740d071a8069a4401c500032000f00d071039150a801054074048000c0c12 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 304217940 1250 304216690 304216697
    0x6080f070905031b03100c090e160509010809150a230103050303041103030408011127090c0a0e0d0f0c050604140f01090b0a020d0210060620070b1308010c 68
    0x20200220b0f00d004c224031008010454500c843c0140342c5000c2420500d01c829aa00c100e0f2130b00e8003e0305107d4201e104403041d54500c40081a0980d10800d8000040713400c46991000b040c1c0500824016610400003c1d038460000e0b0103455101501d401031441c0003c094a045100b141c8072030381d055a00000c0c07030f100d040813501d020320650954555207600f5102e100c003034000b420205005a43c004507407800c104580003440480000c216200900802c115185c228002c0c1c2e0440c00000050760051192005c19607405040c02090b103201515403003555200e81c0d001800c810700b07003d1816003190640c2c2d80d142206a481d800360300c80b0301501e038480c80e040c0a410400d410091040c4400d01c024000c40c4010800e604034210141c031b06101001241c001600d0821440d44031f045000710005503030340144e602040c40301c0c07600000d03000c80742d1121480303111034282ca003940030f4000040c0340c449140010107904100b108031580351740c05071906651070b40b01520031940304000c6c18003c000c41d60001c01c500b42c1c09201e641150012030cc0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 304219190 1250 304217940 304217957
    0xd140c0f190509042f040506010302040302010e0d02040f18301412040609020f1c0305070c0f0f031101030c120207111c061805030403150207080406080f07 68
    0x38216040d00715805018040d802c0c1e140040e04021802c041c0000f10b40d5202001d5061803041c00c110022600c94a10040c040e60070000814000d5000b030094405495058594212000e001020312203580c804103002d0303034000e40300c0003401403100b850b1283c580d06000001c5c4000080342582050041c0302ca20307090b41104200812611030b81ca07032f200603401c8002d0315a481c001960900010f8010040d0050005041d20060f048050004010720307507014104151081c0c4072001d402d04510100401c80381807c61525201d10100c1101c40040d1291004001c0c075885980b250354825203c445507896400b0750307004454049900355042c414080054640aa800024a0203001244101d42b000f807801b05c5a160b0000ca4a030040b071240e042011040000d8100f820123040031403114061403540003200300c8e00c2300694050385032603616510980010400943c05401400851809241d40e0300c28544810031301d07847e1503043d42401082c000420340d00051005000ca640c0f200060700742140009070710400505031000780324844 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 304220440 1250 304219190 304219219
    0x180807060519051210050103050604140c0a05250201081b07031209060507051e040503030304030e0a03050a0605010f080c0312131a1914040e04020d140c0f 68
    0x107049a654151a944a00318080755100c1556103000d440304030000d82513260100028188800c40e41c0045440903a410710041c2c5031102400700300c1d44105801d6685103103020005005004080c0100105241d900d0300b240350188041078025480803500a2680c0c50400d285928199a401600150804038001c0d0320004950b40b1340c0350001070300c20341100406010090b9404070003107100d98040103186070011400e100d5032502c0800203150354400c2030358900d0201603070401c00940544006079001e5039001f80c011482c5d500c1d1031f00c0586411a04188070b40c0d0202c0300b0b42c00400028414042c442940f0312a490105040d418485105000107075130f00812040d41c81080030001907580055007000401c2d20031846130762081c083c5040c10014900350002040001000b80c3c032998014904c00500480381c3e46045414004070140046801c001500d86500d0708010501041c04440703a40c80000d0342085c801000007c2c6c800c4c19541d201c0c00c604660001d05c40a0308551106081800c0c0340d90115581340c1c1c1102c440040710081c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 304221690 1250 304220440 304220447
    0x303140114011b140a120e090f18070801150501081315060b0a0203070204060f1d270d030c231e0f03070906050306090609070c080a18080706 62
    0x11505250304000c0251655605807074052841d403081c40e08000040c1c28400040e44485c1e0303c204240c0c0c00c441a001e1240c01c0400a44203644410200d00d00a044418135110075040086141f4091f040d00500c01c2c0303502c1c14030070301c0c0340400c841d900070800e510010a0b1141c1c8104600c070301e030100c0c0e0300c0385051100b007074100440f46804158100145510082e10303000d0015498890b002409603030003000b80000006000890650004040c0c910305200302c90601009895004031a1781070f506100d0011565220b610789031814092081490380410340c100102c05090109a020108410345e44540b1002e400060400c18103a80c14050a6004030f99420300000d401c1807128400c88039a4205900307005c020010a081c46041c0062256001a58422895540b030709640d030f00c603100030b50040d51750101140030744200040c202d01402c1501c0c8507000081c440035507952060300344861008028401e20401c0207100007100014450005404101026661281400340000403120710300c110b60000e0340542c0c031900d420803400380e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 304222940 1250 304221690 304221719
    0x50d14030705040909030e0319020405090f0d0f02010b0603010b070519080a0f0207050a090e0d020f120d0b04060305030408070506070b06011b08040b03060a052d01121803031401 78
    0x184480c0000311170f0043e00341100c07000f11114805a25000790300c01a61030160f0310300da80865900899040100d0b481e114181c6d0743d580000104140650040c00004c0031040c00795440c40e2801c0c443c0d00000c2000071030900090300d01e074026000084280c1c40400c1c1c034001d001c0104001150900441c8071440c0d0003115890710f408078041d0400b01d4040002c0c0440b002201e034401d000d1100140300181603041c5184c0c6481003400500314040400c120b61290300c1d80642080e100180030175000e00d20002804005000550b45c120310340c00102c3c07051001d620340001e0140c030744a030310034003008500602c05580c8035410701076010704100466000c603200703040c10b01c400d4000c5160006501d4100d402401d104c03c0036021030fa00a044e0007154580034210300e6011030300040c442c442c075000318800e500889107001c041c0d403190104000d00c02c0054468283c880c22241400301400b801c2445241c64005041182440000400c0c400946400b011030b00b181c0502c2401040c10160140245601d4401500304007600d90f0401c083c1c500b5854 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 304224190 1250 304222940 304222949
    0x60a1d0102310e040f05010c020615090c1b0d030501091a0405070201090f0b10050d031d011806050c061506180105090405040515090601180e0102040f03050d1403070504 74
    0x51045828044101d4a680050001d103210b0301400c42a203030074180005440d480717000940d082c0d403c050403000c0061003c10090b105450000d12180404008020300003010700041c07020401c1231040050a00107001d04a1024517503040703800070685840c1c8400000d003940d006a0008a0710707030034810104016106120f900e41d0103181920001403960340c0440403405885000800381c40c400031014044280a200c03140c4a209075804500300c1e0390107659805010022452907009800120b11444001f0b40007520b11004003461310514181c5503551840b07038445461000c0f0b510250200e5400549a081c3c2c2d001840115408103560844400310a40040030540b035114510f010a81e044174040300f2080d0780e004805445103a0710180c01003085244c94075040b80e030340f14903030300420746031011200042c2e4071900042c003541600c07000c01403c1044088000e01401506041d121341400355001c0c4404030388019900c00e4800110300072002400449a0380602030107120035050704446c00c500400401c04440c2d0480120f50449 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 304225440 1250 304224190 304224247
    0x521040306021c1508010b0108060d06150302060c03070b0c0a050405010f05070c030f05101a041109030d02060f070905030a03080c0c060f0105030f07150c02010c05060a1d0102 77
    0x242000c402081e0000054030403200100c0c030302800b013075400c58103800303807002d44d950b04008004510350703200151072680381110451350201e0308a98400000381c2c0c64004062122030b5084080d98941c480e8002401c0b604580c0c00000658000300b40c440a01110a010541000040000b0317450085002c0b80101031b0b1040340a49030520131600030f060120f9203e04e044410140c1c000c151840c05507200c1c0340c60304a071150607000342c40510036a542c007580c9a68500c9440790109041007400e01d5032040c10244800f501c000f200d0b4000c2541c050001c035066403020302c040015001954040c050a00e4881082180301201600e403400f0000300c44c10500c09901e00080404c0d20030f8250802745200d985001d008401c0d842418000241c900900c41408402900f000003d03050300c1c02201544d2a840c00c48030566070b54403240c4510450310304d03422404032859008039140d6510070b006241004210b401f07070f12501d2030100c0c20744600c6485640c800350840c2c81912007101e82e0101c0b4404e0020b501c2d01061703050208407801c0c0c1d0119903491 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 304226690 1250 304225440 304225447
    0x160e0405010b12100b040f140105090d0b07260601110f060c130506070f02010e0409081801030e06090609070501050a12051f0f0518040305070f02030c0d080304052104030602 76
    0x204c40c02c81d101c50000305406100c42c1c1d40d0b980c139499040000750b05440354580080184020740110b60103071041e00c51089001e07103a4003001c0e0b1507498040c02c02d0000b900380c01c180040095030440d04550182c40c0310203052207070103a0503181800c2c2d00041154008030f86102c41a08860300743c442d210404a050354004911301c144984940c42200400d00300c40e20f60307100030b40c00701000031900104207003906840c51860013621041c01042858043c0029100d000c9401420b2820402450050240c0c8240c40103030200103140018100b5040c1e2500f91900d1b5041d58485001d911840070001517120803c90400503000c20706e002e906044880c14003400d0180440106c40c421511403000400003010400043c11104003841d13405c500f2961008140c8818000d03026a41c05080c0100040d11030302003880007540120750643e1014544035a81d1143d012100860b1022a0302d030042e091240c0495450fc401e1140c0d4034000c21049550703041c03a281107413402c036103450b07125003c501c0f12050384654200e00307050f01e007181d0704031502596 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 304227940 1250 304226690 304226701
    0x91201180b0709051002150702070b12041b031b080c0f0409051006151806080f070504030803040c05011704030807050708040b040603150f0e01090b0409050105160e0405010b12 77
    0x203c20509800640e0050151a102c0c40d403241d002507214544102c1301c580500315200c4640c01c0340c843d403040c003d250b80c001c0704024104800c42c00c550915031140c0540509550600940c011120303d1165074000e40f00010f405007180c075000c451911003002442510018219100c0c00c0c008104681120445a03102e01d42d200c001c0418840c00b840418007074444400200710807500c030517041c21404440544940003c4041541c03400301c140001148003694120389960304d99980e0003d4000403820010300110412500748070000c00140044003940c003a920072880c40e0b100300e04000004101b0404240e060000003140014040404d40025040e900b00040d0300d400d5554403068103140c0400c2c4100e038480070900800141c0082e540317905a11151000c0305c0c024029030100da8440c0c10031030721021030041c0200703940b01200400a80ea0f0960140007160303009000403c00d107056850725421210102e503810f82c4400201c0c0d4680c41654440c08482606804039010442d40d41800000715103401040e60311040406044003091 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 304229190 1250 304227940 304227947
    0x15060f0301091b0f05012d020a0c141008040c0b0c1204080f0f15071206080a110901170a0b06030c150903011103060102030304020112020d11091201180b07 68
    0x415044901c803600f00c04006041c060804003403061000303011000c60b0200e22907105800d180700d000300d1495021500184d2480d400d0340f01515405003001e40c03207803445910015940750304a1008014204608504450b51014403440d40e07e11031110b07003080807510411000503501e00c1000d09480b550582c2e6921160031302400b520f011200c0c4221031480401140020f03d030400001c03a4044000113100b95036a0038405810700f99a0040131030040c031440740030400182c1d03052240c00b0706850041240030204d011550f4500d240d0412038501400c3d5007210342d00d4804040ca08102c07101e5401815010071010b00001070000c803603201c82900c078005111241050104000759800c21880a034000d00070415460000b0380000c9003400e0303100c400d0301c500075424210701034a004000807c0d01c0c410303141a006945555181d9004440c00f0300781c2d40f08482c0869082c050011200e03058811166007010703032003c0b85c0c0e0f1081d0020030010031100313290451070710703030b04220068282c01c220b00405000f459110070400d50a4541a03c242c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 304230440 1250 304229190 304229201
    0x2031902010e061c0b0405090a12021e01150819080d02040308210604090210080703060b130603110304050c01080a060506030f0f07080105100c050f0f0106051215060f0301 75
    0x2a82c401800724a138400b0040c030b400e071601d42c0d900c1030108000c4601018240810b5410807100008503070000450300e0301140e2135a6000500500d2441692140a00b40c0c4400d6400308120f000a801a9035428440e08500b02c103d040e90050220b000c0100586100f10705018410f092420005110802c041229040b40c40b842c3c069401466010003903a4664030340318052030080c14880d50b200321010002e00410b102e81000c1c070481c200241c000e000c10310f561002e00415038000b400500220100350380c60500140c40d038442000780c0070204074410000b140314600800102503d544d0340099048140401c140000580006240071303a00e030003800c1282840c1d607940310800003040160f11403074002c0780003c1042030401e0310304e041600c0750591b240903a40c030740c981035003c803002c1800340079554022265a001c46d481e10f000e540103940003849042142d96002052042500f801602c648400590303440c0d003000e11030f47c602011910b640540f050010040781014001c40444100d0183c199800f440700c10345401000c1d14203400c01e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 304231690 1250 304230440 304230467
    0x307050a0c0c29040b090609130c030518060f0112080c030304030801051c03020d110304030606030503073309080f18100c11120f060a06060215040203190201 69
    0x90ba16030f030b452243e20f40380e40e5042c11681880c21450302881c0054588030a43d4242d4890038101ca0030300c4000010300c00c45900140406621a00304107503180c6d00c900c0c500408144042c1607901140c9070901d8003000c2002d10703c0c400108440e17048201048511504032100c0d80c11540d114030160400c40d21810650310502c15024001c00600002042100303042e0407a0b00c05040b80c009490441d1401c020900240b0000c229600040042c0c220620030091144100340150f8440d2450701640e143c03541d00c1d5074110803210706900495141e04042040c400b03001c01310b10010b00385a0200b140c1124100441c00c0201c0400c2644078140c034042d80c81c070604042c8044d06003594403018448403180c0d5a000340b2240a8520040d464071544900382c5100254031039842611030300c00e0a0791003a004420b21100e030003000905100d44024540700e108503010410170010402403d8042c1102550000d605403d0400080c00d210f40c62000c0303a20700030400140001603d0000304101c2201d80c400203100c400a41d480100c0700503000100c1e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 304232940 1250 304231690 304231703
    0x1b0d050a05030c16050f131e200403051e100612060c02010e0703030311070605040311190809210d0f0206090c010e100c02040c2a05030307050a0c 64
    0x980d90070410004000c0010121200480c0c09510801d020018045010301643d074110915842c580e0b6141803d1880031004402c10304041000004000c40507c03058560a16500840d01c88540300890821482c0c1307200198034960b42580b9103821612410381e25540d000d0880102000380c6c0f440d42c0c0040e003e0103078020501140005101c2c196948d03240c0307003400f1a40d94003902c251340b50220380001c8500501c12060480110750141c41c1c2c6500e1a18250028000740d420f01003020340800a2000188035407140c0d510481c404d4803407030b04031741c014032540d444c00340114801009124005d0072407020410071810785001c0311080780c400b9900c283c4460800b181e54901c2c041e004003031103803030300400d035854000c4030f480c00c42c48865088803025600d000385c0a645546401c90319011410b055003500b49424140e2030010703c600b490400c00701a40b066408542110000e00c0a000007481c00c00442d411040003030341c0314517580074003100b02c1e0140c1107a8482c2d68417032001902d0481407040c0040c1107003010340159100805243c110a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 304234190 1250 304232940 304232953
    0xc060c0309050f1c0c03020c03060903071e0503090603130b09100e0106180b0105130306050f090f0c01031d12040618060203120a060b1b0d050c1b0d05 66
    0x800180c080d1000310811a050302640380c0304602072400250158412450039a0701380c00700e509010035607003500c841d041581180030385a128a210313102000407e0146d6102e20086030b4035551800d01400d00010500340001d01100034104502041c2c1c00020b4502d1110104d0780c0b1581c0c2d845411f0301c42d03280da1004800600e820400d00c00c03c036031040c02081e26451b5069003882486030b0390000302d555003210f20f980580d80840c00707651005012a0003d612452145006041c001c0ca441c0c03022030131203014404c59000b291190f4542041001801c0c038143c0c00781d0400c030b402008045019248000c2900e0311100d03550380d410196070b00c80000d00c1c541c1240c2c03804003004480c025104550700840203041d040c0c1c400d0258070080780d00044c041013590b44514904046400aa01950600d811308000d0100a8400b5100c07404041d20341101192a10404009043c9a043d01ea07040f82040951910b003410010503c00c4030041c04410301140380403450214800e0801d004030040010b003621a400041c101610103071015000d4400c90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 304235440 1250 304234190 304234211
    0xd0e1804051b0105040f1802070804080706090f03020906190906030f0516030b0f0a021314120102090a05060706021605030a02010506150703050903070519030308100b07120c06 77
    0x4141c2e0b80b00c9955150680c00700b07034445001034070f242c0f14504c5a120402c4048400300862140308920411a0341c1d40c03a0094500350954494214507001508003041c103400c280e00800405402000c0c410003444090100d4404d1841c50300000c10004005040320301512036029403000085040d0300f6000a0641c508081000c81c2e1a401c099841c03d40d508801c0700c040c4100300789055190b1989d100e00048987c060300c4003c403581d520060407003e80340034200c40d1150303809201d500424800c1124a00c094140d00d0003801f4005031080400c03030180300b500404055a48100504503070b9854001c0c0400c261502038032800c2c0d03a02d0f00c9262400080c41444181000d00b11008400301c10040c02000510a400c0c0340c0e40203001a4a42100f08015011034040024410404008100000f40644090000420b0041c01e95448542d00e4012411040c83d050518100c01815101442050342001019070813008160300300c6211414540743c00c1a42c410b00c400900048081549071280a01c82e4061411980c0c2c0980248000801c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 304236690 1250 304235440 304235443
    0x70909091704080106050103050c070210050d02190c150507050f160c06090e0a050108060a0e19051c03020c0703020402090d080d090605010803070209162303090d020f0d0e180405 78
    0xc40c0146c0d030000f41800007041200d01003006807400540c00802e401c5101c000d101003a10150f22086045184c15000d12900344d50154070250182c04542c1a298412100c1003850310380c5190206c0b80314041e426103004240410664400107441e9250080540d5030744e0b450346020000c852145810f0b000301909200c0394085009584110ac40341201c078046c0401c203980d00c9040c0c014054500c00d0003418039540c408400500c1056045c0c01034204150900300342c48104c500701c0f0300994036000124065600307a2003040a1360900c240410b00000e607590034501107007880b070070b428041e490700340c41e1001922840d00842c4019299840c00d020044960780300c14865643c5940000700005002428021380316030b854007000195920002c42200c041640c003d000080c2c540d2010764072100e02c0b8034595130004025405901040706030072841808890190a80304035241d2400308039281c582041c66991500310f401201d4280e040140002e00a1304141203800d05242c02c84681c004a804001d8a040b41030107400d080d000d01091100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 304237940 1250 304236690 304236701
    0xc03030901060906080f12090a08030a0807020609011e050901110a0c11060f19030e01020f0414060903030d0e1f0504060f0b03030d0e0f06041211060709090917040801 73
    0x1207500041c030400b641c4610071750316000c40b10310819603a040034049503142e0380c43d58000c04494030024000c0510b11345900500d861500100ca000022035040014441d45507010803070306600c0180c8030028000c9a415000407509502e00c6c0d5061560680c6075408110300003429000650000c226907003594031010310150041a1900000e815186c5a441980c20107290602c1d20459030000100c2507624540341c0c80f032440b00b00003000d0712100020580d80300e000e401400c0003030004003605108148296101d0781001c046028000482043d68422581085000c0c07aa8401100b500c0340b2052303000d00010418084d42806062031030480c16441c4241d1115003040c0380d00041e5200c4c0e80605c2c00388004001100b0214003030700c2284c11009586a055100f4006001c0783c210641040344001c20a07820b4030b61216038800740c1498100c0564044501941d1102220304040e40601040014078800004041038108810003034014007960161407040e50301e6100c8282803000781c805d07511142e0042d2040d02ea0321590b40005500030407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 304239190 1250 304237940 304237949
    0xc08010e0906070813020406081603020a0510020606010c0501180614072f0c060309060f13021f3f1b0305070903080a050a08070507050604080a02030c0303090106 71
    0xaa60001107032150000107000b03440b81c1815203d5850036103d40321581109103a0701c500704d03130194a075440132840041c01c0c48951a40b50f5030110303034010603046104100040707815405c141d0003482810351810009500054190300300c2000e00300025003d8107801d007240981420254004d110048882c0c480400070310380c0c4480c140c0000394448100c15141c00c201110145201480c40c00e0101c00c45c4045248451a0201700c510450040304845000b6400400714080380c10031140c440c1c16800a81c2000008000404000ea04c46082c1c141d42102c60b4143c0e001031601d59004c4240d03800d0030b0401180f501e11600807045209194440ca44800454021217181c14001c498903100721107407001004a0390b56883c5074010381882c0c0914025042d0b00783c40d07030b41e0110010039005244804010b00c4080c008003240703880b80140b140310039035900c4550f910f401041c00b402e030b0701c1c010b80824100041080344802040c4081845074001b50b1004c407003591460070100403860340c040c03c082540d07103000000500c062900154005000c56 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 304240440 1250 304239190 304239209
    0x160308031608060109090e0708060103050a020f100816050d0509060a060b090901031101031d01090308010f0e04122c0f030111030a090c0f06080601030605060a0903030509130c0801 79
    0x1881c0c01142250301400c20b903002408117005010900100c80c01e900040c0358440f1200460b0141aa5140f505203444003c2c0c0c0705451a801c011914406e40c1407200880711346520030b5445c0222114100c40040c9000350080071180d80c21154050900003e1154040719844c1d804840280054100300c18007584a00054034510050f038509075001511030766a40640711480001025885141e2075a02e40d85e00c2601d003400c0542c1010340c1d80070030038181142c40454240300001c5c000009801406441c016020f5441a00518855404014100085003030002c005078003039404502080000c80c06103041c3c1d0100c0d54024071960040c0800324400c0c0c540341109620590810444030625802c1c54082454203c852500f4582c80c111000c0002682201a94015074985072144101c0044540d03610320404031120541c00c18000242d6040c10f03c8607640e807500440000c0c02007200c1d1140380640c41940541413185d24030000340bc1c410b021034641e60541e50014006880801218284071808940c0b2004000c00000d001ea03a00c0d2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 304241690 1250 304240440 304240471
    0x210d180b18010e030f03100b03040b0a0606020703080403110a03140a1502090d020108040507030204110c0d300f05010f060f02010c0206040f021917010c17060108060316030803 77
    0x1140140106500c41072801e002d90305d0304008010307810456000505503c14046031400c0000c0c1d200240008620850241c04200c1c181d0800b41161416245290312410071540314010510219042c07408480440c0e03480903004001d11055000b00f102042e01d40d0005e881040d51100700d02407008041a00301e5214840d4074039146004030400c546007280244001990404017a0003000c00650040c00015080f500410486860340d50340d03400a402e41e44001c0325401440b0b00801c002a0300c5000f04400014602203082014040300701ca040007091080500b4560007080c20803091071001489540408500108944184069a10f80f41034640c02c402920820340040c0c0f61f2410b041d60603106102c2c00501034503650140000d51101c0c2c848c1c41a01d0140030701603030b11010000712404903111808000004102181d00500e4074070b09058060300310354401c03160304c0512505d41c03103200e036903c2c02210180c0e1014007401d200011352503076004a40b60054001d8040c89000f0f40840c0841402440ca0142d4442c076040c117000c402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 304242940 1250 304241690 304241731
    0x19050304060f140304020f2101020a170610030c03150b03010f1703030a0f0e03130501080a0c140309070b0a020a170a020307170c070e0a0e210d180b 65
    0xda080c01c2c0f2001c002e0101d4144040742c01454000b504200a100042400856401b40c000e00d103206000c007024014640c0d40024442c1d071482d0481c0803d24458100c184412980c80d00a01140004100101d05002c141e034407a0900080c9001c0d038040c0090001d81c0030b8050f2140d88820800f00603910030300079203603072506107140010322041d60001407404444240181d411a1075031101345000d0421000d00d40050398840e000705646403230800140c07039040c40229038888803d01e4800007500380ca801a0079070400310700b403100303e0407450b07000079041c0c0300d1046161049540c0d5844200280c00c0c902150020004044001622503005a0014080907140c0c05080310301ca200032100650f0700030f84640c600000251f007007884008040390103000c80940602c200d10066180401500301e103401d0500300c0c0c00100710003203c0310500c91912000d11840c03400c941c800005284403820521100c48404589030405601c2100090300711021109030030000600c3c0c41d808042140301184e1403d0300710980308035218121700c840d4100045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 304244190 1250 304242940 304242947
    0x3140c0d1e031b0602030a0b040510050f0f1f140702011d010c051c03110414091032090103030e04090507030b0108010c020607020703020f0d0519050304060f 69
    0x3841035612045140d00c0c004801088070740825840e00039010f10804034400700907050b4000c4142c003854850702c0c0061307880c074000700c2030400c40d1201c5c02000d00803407a0078200011a65031001c2401603d02c00c541007600301c07442d00001902d00d424182501e400c14400c0d545d40700c020010514803000541c0980b1843e035003019038250010140a0000d01a0000e00c01290034800c5c1e8011904005030b0401c10301d45001810f10380c0c0c403090302c0c042c564283d0340440000784004122041d454071503004c42c12040d04540d807520380340a030801c1044031207015007841200701c400410407000d090301d0010300070100d26481e01082444881507034046046450240440074445d50f03013400c0d80c0350500195043e01d9140d2500802c0d100e15609000081a100000f1038a9105045004c004242203415250080400d0b200100380d00c520507000074182100a4180300555111503801e20041c3d440d010440503010098507451540a00ca040c014a8081e040d01c803800d03001000b000c00e4050220100c014402d54500d80c5407100c45134420300b03044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 304245440 1250 304244190 304244209
    0xa0c06090816061d0d0b011401110a11130e010519050403021c031416030b06070503070b04060b1905010224010902070c0315060e070527150403140c 65
    0x44100e030803150300c00c0c400c80d4015070f0000c1c0d0f250b002c12801d144020703da40205e401100044410350b4160355071001044103207240070054005a030700b80f03403400c252000c040840c5c1d0783d045c10280003041586581241d016588548140d4880b1849008080c08080403a1044500810054a6002204c0403007094603501134500c0c003400303000f981c3c164010595034181c07010f0909582c001c0c0100404051329452211030881c02d100f03405004070840780d4a40c54404c1d040c1c401400f114001120180204414880e18011400c0881a2200950440160b0500e690345240a800616070110250317400035400a10070316084070402c1a2050321030a8088480140d00b55442e0780d140a1548041c2d2148141d2800601040070150064041640f00d5202195690f441c2d9460f1017803050212580da1805990750420842c0c2ca1003400c86540104a0f03043c400e00d061840d50202024000c0c0850907183c10b5207001c0c982c881031321200c80c0e54150240c00b51a854a4035228a811010500142c0d080016440781c2419940e80c0d16029000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 304246690 1250 304245440 304245463
    0x8070201030c03110a3605040b0a050a09150312030203090c0913020616080313050c09040b01030b18030c030d0e0f1e010f050712051302090a0b040b030a0c060908 71
    0x4d6040010b174000807500140c08003120320142c02461004001e81c2003101081080c0050314981d21142401c5c04284001c0b591110b14161240300c91034401c0109031140f074080d0f400e6564841c00801c404400b00d903d0000504a503100801c0b021712100d030f00d01e425078181e01075802628404180c96080d44080c0420803000e8080c0c602c1c000b0800868600302c01860070710b00402c01c44070b09425030340d80c42d0441c0c3c49444450308115040d01906c140d03038000c0300030840148198490900201e07105c25070350a007900c4008210405010040241c1403400115400c12507680c0e051408083ca081180c1da10200500c1150f140e81005101e000b43c40d00703000c00c2240040c004240c10300082c03000340041c401c082101500b420707520558681b400403235585009a01d460380990240a10600c1e458440348003c0051100e808100c0784002c01d4511446244001180142e40d40c010423078006492102c042140703121071001a0091803014015603251107a880a0350802c503840703031400300722a02d985540b19855682e50040c0e4640000b00038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 304247940 1250 304246690 304246721
    0x30406050901031812080106020f060f0406090c0902090a05030102040315051e090a1406070804060c2c121b0108152701050418020d031b08070201030c03 67
    0x24499188100c01410302820140350115240181440105400303100300410b0352522407003003d13859100d821050050051030b0610091411800f010b0340c4a40302c0502429110f1159407032400b003024044c094000503100341d00019007290541d980d0350000002d50000a0950051403281e90000c3e0320b00c0e0610a0b6003c0301d40186030f51040005c40c00403007008010003001002d8071400c4000080301e0000c14001180301d0210700004100c1d00d1500e09001c80c150b0820b80040419a108508206640b070344040c546820580c0316001103110042d5101c1550080d240c0035401c983c0d06881d403590070300b03880d902c0810002100700707a620440303500380c0841241d01c0f04141400a0400b407a1503c110706a0b51154008582c09425030307580000c290140740000360003061503a5580c000c01400d0704210500b0f6000016280100803c84040100744444e801c40c0010200c0424040d01c07890000c5404014107004110301d4903140c50403008141102d40310f240c200c2060300201c85c280d0010345814000c02c0e0040c000d00c81d40000c80703660f01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 304249190 1250 304247940 304247947
    0x120c0203160c0e10091b0f1404080f03030a06151706031207080306010905040c02071205160611060903090916020c0918010b33040f061205150303 64
    0x310108141c180500846000020500c0003448200305110035004044440c850602c1520700882d070300c01d850340c81100c40880b41c184442c1c0212540c02c1403900c06130b107455050480e64121002e4441d021405690311121441c010300280540d2800040000c6100e030360000d0741009a2a00d808c0c80c080c1803900c0b001444085041d400340c00040100414079642c0c8038900404440c055102c0f00c500e4030b1160054003040701c58080201c00d101c055030b005400d51003d0076041c2c074100002801114004d58a640d076202c0c6a020410307640444052000501c4458609005800500c40165a846004140d8840030500130b81074094000412110036000c01144d00e4510020044e040303648607800720314030903840d80c903105080d841100c62004160f103c90b0364076840f80000410654402a15190386400d45070000c5c622881007100201c40d003140b504180f00032684250003040000c0d00030140c1c4e82000244525084020020300c91400010119445003081c001006030803824407141c0c40310890050061940342030b480e07160b002070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 304250440 1250 304249190 304249207
    0x121902120403110607111314090c060a031a040603030503101a0f090102150703050115020105131118010806041101030c020c090604020d0905060117060702031801090503150601120c0203 81
    0x3005e0066207028003c0d40c00404000000582007103c481031400c02c00391140c40040c02c501045614a070f000d112540035104641c032544c001181841550300c450706042e0b4071820804025040030343e4a0140c2e00c06001001020307145c0c00c02800c1900300700c51902c0c500e1581140802c101071004910050307009202060b07410018100c040148070f401c004030250441c890a02001c20010050788194090308098400041c103504024018002c0000e0407901009e41e07040c04144255078942c41c2c210b10899030002482d2101904000010b103890104002c4031000d60003140000ca0541d902040b042d0059100300c000c00d18060000c4015000c1d00d5421042a0250704100040c55480c100000180d82c040340041006150004c00007000013143c2148400742c41d01d600c80c40051240008140c041e0b01021038240040255241c094002940d0b03201300b01100e003420a81c5566104541d004e400240c010340b40040a488450350001310340d20010900725a0280010040da101510b5001a071052070381c4040726502031031424044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 304251690 1250 304250440 304250449
    0xf060c0602220810020a0917030403050615130c080a0504050f2505010507020607081c0203150907050c0d080c07020a061701140d0303090512190212040311 68
    0x8490550304a40c08010341c48454201c698145020442600c1112816080c1038010b031800e403591302102c070410310400c248410560801810021221000540c0c0b24400d10304442c01e085014903807006003240304190621151100d50f017180305d012101928040d040350084550981660036155002c00442e2508000c1150200c00d80c000b02d038424003c100f100c500306440105a844c00300600d11002c10380380034114901e45980c2d15042c000043c10240781140c141032890b000a6440d11030080014402e500001c0c500c540100003800c4e03a4610a0824411902c2e8074014401540c14103240b40800d201d503459000248455010b4030a8412035851000280354801c0450740580380e10401414513046402e0600c5020016512400d184010b031060b41c0c2c5403c507201c0c0000400c03a810b801a0020710f1003c0d450200e0511310b4640661100c40c040d058903001c24481041e04043d401e0849048624003c45c400044043c09803104082da43d03140211542200c01d00c1901850602c2c20740500e00006060150a42c5c910316036152 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 304252940 1250 304251690 304251707
    0x1c0b0d03050d06170a031e021f0f020721020d0e0409062c070e01080a0303090201050d05100609081c030e0f010606030c080601110d030f06121110090f06 67
    0x49140020f0140d8072150302000340c440001c201481640310a100c0020554040c03103503800b041e406851003064405502e0040e4503040303a00071081c150398052198120b48080c541090a464602000c115606e2006041125200a42d0404c5a01c6d6006600c40000e406200081440d40480b0a940e0076038840300c0001004054a10314005488250f140d4850b07841c0c80c1c00c050714120380200c2c0b0341d0604045440342c420071420075035207901040b103d0320101d00401051002144010b1255410b290024954001b440162024010001d1310410203180c0010003c80ca01880c851200707039080e81d201c1c05ca02c039654007078050b07880c0c441c0c074074201e500c41d403008100d842d460190308450780c0c400b148810b580501c07012509041c00c42c2c80552110001079255402c0c008499048a0342c03d42100b005c2ca852100078410403415548c5d5140161504101907480c110780520000603072092001c0c1c0700c0000c281c070529916040051303000b016100d1a512411600c200d01500600913564003045601c9204444441d51500c8400d0301d0081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 304254190 1250 304252940 304252957
    0xc03030506040207060e01090311070308040509190c0e040f02091305100513060509060f0916050c030a0c05060709150c020414130507060801080c0d0501060909081c0b0d0305 76
    0x90f000e000c3e510018004c2d009001c2000080c5000050107601414003c02320144000c01d012290070000d41070003c54120812074080e1803054910040a880704d501c0c041c03400c402c41c0c006d0300d405440c1102d0a0384480d4000048610740c14101c1e000d00040d10410000400c074410100415401414031548880f40709190304290340c8403409007421541e00d6034800c08215007400c05a4002d0325265998014030003450302d1110070f60807500a40b030450000450324045848003a0207411012054000002004040d104000720b079003500a610030750382c9880d0035407409420074280f40e2003107076180a00c0c0006000c15200b0364820303040701c4c00311276000d40061a5820a40394460007881c16a0000c2d11180a5403003d550f084c80b090180c034506440c624484a02d040207810b11740c0c507800c00c4042210010042050202c0003914094440044500700100e0780e25250072801440710340c0c80340c030b482d50a0104800a0040520160a04e040301d03400082c0c420102103840d01c00c842c1e140c04101d600400203c1030801080c451000b510010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 304255440 1250 304254190 304254199
    0x260102070b0708090706170705030405120a05070312020a050703080a1107120e030c0f01110a060f06150509030a0f03182904030b0112030221030a06050f010c03030506 73
    0x103036154842201101d0200d60300004240710034248904810108100001801e00b07103444c000d0041400c840000d03d9201800c5002008000320108081c40418096004010300c0034250750f1f81c400d01d000014005030014041034004c16408410840c4107003e500860f00013402c03d0b5289071410000d0741e4140d40c0f01202801440e24280d130788803801e184141e914001c01445004034140d0741c02403c1d10500034160041803d0840c000d4122218402d619200d20203041c2c0c4082003400d0070640b13804a46c080ea03140918295010f0000c1c2d09003000d01000e082c4560000342a02c000107200c80e9403806a00741500c540c401c401c6155015441060328170046100c1c3d0304142c400f540302b4904004c480361070203450440c16032540c100c90180320014001221240d0949591003415643e00942824207140d0740b90100786803014880c2d02180e42180d050002018800d100c02d0400d4500784c0c8e00403819150441241c1c03044d07002291066500f034527180021446180900b8850140c20059444014094055800324090302d800b401c1240c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 304256690 1250 304255440 304255447
    0xb06040509120d0f05010603090b0114010c0803160809030a1e0e03030c071e03110625030801060f14090409020604180527070603230c120a06260102 65
    0x2242c550010510b90001c524007140404020035910111081a40404141440c2c41d030350600280d40781c000141180c11040c164681441400c0041e00d0100b001c00008110400010811001c0750480a400c0d110380b9460b910500c1c15510070390081c2d0340c2c0c8691109000402c40021000140c0718a0345180c0040c5042403410f5051148040040b900d19005101800181e421102d400d01c200701084000000344040da4240050032495034450402d2104c2888555004140024a481e07014418030140c1c8040403410605108401e450309006103850028040c1c040015001d1051418851113241002d20318500c1a403001d1424112008100040000440480c0c02440c140f1000618044840d2001300365900800c000c9501d152148203003040041c20f8041d09480c83e52000d0020f1300c5c10000a160b02a40c820741000250546405203130b01744c4c403800700d4480b41a481c41900300a402001f541c0500010388031241c81a0030350f1145400002507840d01d028944042d040700780c6c1c17080300802e190407081803c1d4190000515 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 304257940 1250 304256690 304256713
    0x81c0309120302120f060f0108150607151b05160201090801050117060c0403050d1407020603070f0e04140613060305010212010305071203140d150611010c08040b06040509 75
    0x9005200c01d804404242d0204a889140131420b14507544034a4000715115140703404000601d5406201c03d209040002900002d440e1040c1c66441c0740090308020000354480c9850314000b600c6240380082c0c5007140741030584204032459080b25030911a04151561810600a415108102075034483d06031b04002c050140050024428803800c1c1c081c11080308103034581400110030070719014018000200c0d4131010031007007000ca0700108003120101034a1610040c0810360300c215042d1030141d514041e5202c44004140130302290400d00d0524081102d0329100400c01001c0b01304801c60703c9643c1c2a0304990002030000c0d905191040c4446090380ca54580000c944d03850740c440c03a08a8010075009030703c090f80c80005105100c01000702c00020301c0c4610704500e44840f40d581c0180400c0d2404581490303c480801c2c40840c41c1060b0f00f0441003540008141032407160b448000800c1c10b840c10058550743d500c1d24006801040c40740c94500d00c11038000c1c1c042a1780391100818003004010080007042c4038080c0d04292003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 304259190 1250 304257940 304257953
    0x10512010f0524030a0503030a051b13030b010e0402031e2a01090506030c04090911030a0507031401021602130b1512070f021906020f0a05040e060307081c0309 70
    0x7070140b031501c1c07070001c90800c2d540061030181889110052181c1d01c09000c085c0041d80000403213502642075440401c1948132030302c0b01c3c030800c400001c0c1c0d68030184000c01d115810500041447c002c4901580040c026030340d0790900b05280000a94000c4c0d0590000007200d40610000c074030f0307406848031a001f124150880070791500076819030404041141a040b000c2c9141540c1d100005c04080c0408540c0b8601d1401c107242190594032403841103070300d0b4540310754488082c40000c05450720000805030985606111303a28003291a4110713404110b4282403001d0503020050b005100307840c02d21000342c00225a0b84125000c1050140803048081c04503500d80c094254540c640e10400c101540070714604c5a01c0d6240b0a406413a014802000a0104140740407071030b4003694009403010a0b04044120303184501003c1c100f44000c3c1c4948001c003003c60900041400b80759a025000f00b04a44084814044a480c0d19081544400e19840340d1443c0e0b9000c2ea8021ba9200c49002c61031580e43d896080020b8031040b00c0c0d5825 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 304260440 1250 304259190 304259201
    0x1b03160b0403170c0a030c0c0302061207081b0406051305040e0609100902010c020907030e01020301151407021008130209040809011d060a051305121e070509010512010f 74
    0xc1410300c0410204100050342c012001058064000d25040c01034800446503184000e10016082020241100301807201d840b418002039034018000c142d03604508110740f1642d0200340d541900041e0414000742c0303000044808602e850b074612a11074078091500c54121034640061001b07000060705011b00250903561441000075032001e120240070a403920f107000c1801c00d8404020205880d080080440040c2c0c0d04c80b110380016541183ca81d2803a8542136004c600070f10003070415141562000001150840b0050f0004034828899510604454410034000120b401200d82c000d40000b02100641d20f82405105000d40c00040f0011104d0400c115400003440040282d4040d5103450300026400410350f0300104021512080140b80c00c140070180300880d855101c1c00c4407420030400f001c100d6402281c0300c141040000c040c02040c812036009120304454403000c11040d160901c0300c0c02400700300c075034a0201c0c90b58101ca030000c3c02e6021303507031170041481660308226002074201d55131402400003404051081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 304261690 1250 304260440 304260449
    0x30b03010209041b08180a030c0f05010f150519090903140a0503180313052134080607120207120801081e0c0f04060803190f0e031b0316 60
    0xf5910200d01891005e0700199000d800d0001180700111910354071440041c5000300c80d54545800b09200d019420820101c0c00c422030001c0403035080851101c006801d030340111801c0b51154003108201076840f400c102445500c000310100b450008a001c10000b83c0580c0080c208a01a0500c60350f4401803840e4508594406268030010540c04014080840b54000340045034614000065141a14002c0c494070569803d1182500c2039021074200c0f5808425104054004000b601c210f1302070301c001d04e580723000c00c00018440b240410314039014003640e451020b540808039a08007014094580742d9402c02c03030344d0b80004007800c0412038007005a000012050141c0e883c6821a039030b191215941484074203418a43d10410019a9903a0144401c12100c008240039288941c22544007100c00064000f0401030085640302a0042c0004190a50203290201c0507594000442d624603042402c030020540700c1c1011042d03002d130140c0c024006a0102110350b0402410114001c1c00c550100900300c1c810721400005812 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 304262940 1250 304261690 304261721
    0x5090d0f020d023307050c130b060a0206040b0606030105011b060914030702040f06140402130f080f0106080114040f0c050a1404050c07030c291014031c030b0301020904 74
    0x30345140403480d0080306001310b41d501d06403070b1620040d900c0b000ea4420b00624010720500c107540c07110341c0d424880c1d030200b4a04e8202400580d00c408100b0b4000e52501e02c111000e981c51700c0a000028a10301d460022a4162001615030424010414051004100d002e14007110026943c034280f0005ca034420110040400b5410f00840d0744100358410321090b03c40350110400f00c141408800d10540611540c4500901c01c05e560050f101e83d18400c0031440680c903030f0710a00391901621804076015001195151812100000034042e081e942c810301750803aa0307420000306241d403015003c100000e072600c1d08a110140121003c962440c0c940340011280da4640e03026000e9090301c0c0c0c0300c3c0d030799a00740381c02055441804134550b0780c108009a1006443d0420303a6200800303801038640d00016580c0d07800c000300e800320140d0103500360b07510304010b00780c2c0c24800600841d0000e100000ca11078441c500019200940d8144801e0251004000c41c8258050588180000c3e4195024417030819161154403510030702c05c80649 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 304264190 1250 304262940 304262989
    0x110105040c080c040c02031e0412030801030b0f0c030402010806040912021e010204240c0807110406051014030a20030a0b06040b09090a020403021e090705090d0f020d02 74
    0xb60141c5000260080d240c091400c0ca1a00040c040d00030050300d40030040d43c0b00824900d1000d9043c6100ea01c0b81c2e0700184030601c02e401ea50418958020304440c1600d2040342c280140f9100c0c00c4411081007401c81d21801410000c00c001001075124010960f08004083c002191407a01941c418044204540000d00160f0105424400303104280000110303022801008529050404d00c3c80c0800300a04c041c100c4584403a800300c403030564841d028600140740c0025006d9241c1e6524034205240501100c4214401c07810400c0125051070010b180c500c440310591154400280510310700e54140e0401440d0b81c50300b65540a5842500f2822070a040c00c2c010100461940ca1424402e20b004840c80d541d8110f0188906100603c0844d40b203404482c2c41410440315200655518142407010f4400c0350402074010601900c2c01400c04141d15a040400c01c0032582c06580350703a00c45040301e16014400101d544540c04038072000118442544c00c4980500144c4810b444110b26004244000340e18184581c0707412646 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 304265440 1250 304264190 304264199
    0xb0a03020402031812090f06070c0b0a05030103020109140108040b041103030a02161208030c25050318090705040b07081e0409180b010e101e091a060f0307110105040c 73
    0x512560021540c041c1d181810a07681b000412980d01c0c503222154000d07100002d000b0180081600750100418035031031000d030380c0c4810b1b4100070800c0d0402c2c801280469180f400c0072442400340d811103800342e001a0f4034000c0399525602c1d12100b1840140050320a2105544d0041c46a141070009151481d2560000d0403201101d458500060a6580c400c0c65502031030040b440000d00400b0440e034110b20103585803903e07040349601c01c0c0d404203000826460025500c3c0060b400300080840603145000c2009030741c4000701c0008052210f035020468030180040c0c02003200303101212890018203205802008000e04043c085240d2401090000382c0c07011142001241c20412000b0034041e03250881c040e290500d24010280c0d860b90107552060081040080c02080015044025035007404024a14420b07030084402074452300322008402401494011403c0410360f6400b0301403240d6001810002034142072500f4446503541400390805040101001399424840521440134041caca400707240120202080903151 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 304266690 1250 304265440 304265443
    0x20901120c09060303140c07080a0b011e0f06051c02030f0910060e06040522030503090c0103020c0c06070c03200406050f03100c05090613210b0a0b0a030204020318 72
    0x6641c0840010b070305102c010f20002e98480b185251240b240388041e0385501a0401c89801d04d440b80e00b03d1142440341c0003818003800309050159040b22401c203030090040c80c00f1800b401481145000c0e403941d007103142104104c040c0c420360040485034104080880b10f8116030806100380c0e44241c6041d61013100800901c51511028048011b0030000031108202d0540303400d03000c0702e40c2540180410300c107958450000d4808100d000600f19040400b40b20540c41680741e2801900c00d810944550f005841810072220540d4001c1c07084410440e00140201100703015601042500d03407180c001114180880d0800100007241e945140c590101d2203038140d800c41e4010400d10003190390381ea21503485080f056050b02074585010450100b00c1c1140080402c0f0035000060544261041002041e00040000b80440c4601000003118003a1034405800600701d00b040c140d01c41c01d80001c001c02070684583c100c081a6046800c2c0e0050050100142c4008961556a00001d089800440e50f0103e102810810f05910010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 304267940 1250 304266690 304266713
    0x21306030e0d020601060503180d0c0b10080a080f04052710031e02030102040512010203100f0605030f09070902120405120c100908071b03120206220f02090112 70
    0x41200104010940c00038021342c1d134103040c881c5130300f44100080407070400340b00c2c1c644101109480300116410480440d030000c1c800d00200c003069640300040404203000940c0e03400901c2c00c8800b0303403008100c810456150707103441d58000e101c1c68200d00400c10000610343c8032200c0d070a0703c070404924031400300004008640e072210802000e0714075003041c8204c14000140c0e201c2c1380b808508081c40640610041610201e80240300c1c40c4c111550000300310110804000b41500258480c102d14804200803c2c1c2e140301012403a90340b400b41001143e000c2c8009450344481c003e8180e80700895404071503035a540c841543d03080b03074898074101c5800781c0da02c1c00700720601c4410080440000551a400c51070414030b0070009899400d0310348003a60040d10740d6145801d101560702502c454980062212641070038102c041d40074200c8900c001c4030303590840125181043d001040152003821141d4040e003035154000a040842c84070b013941200c412441412010241c1c0300c3d10301c528040c14070700e24140c0240c1c000d42005800d416 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 304269190 1250 304267940 304267961
    0x2d07032312060604051026060a1403010609020d061e15260408030108010b0108040c050d030201091403030f0a0c0c020f01050c070906080124090213080a0b01050f0301020a08011701020d02130603 85
    0x302c0700e401c0c0702c425140c2c0340100c0211003800ac0c0f406291903050000030b0242507544d104085040c004660800a404103900c45011940e2880c50350401c000d1810101d011569640702d60003d0032000f100411070a4060109003510504810415010303000c0b00400550146043d18140c609a4001c801800741400074032904002001c2420941100e18082c0d80d9203a002015000f0b4501800a074505c0e1002c0500035007101161b144c5c06160600c2c819900780055940b500202e43c88851182603901107184180c95200f55202c050700c9550300b0f0003000341038082c400010298103000341080700c108258000381c3c1e020310250000d06400b003004601f440ca08840035080d100b03031208840c40480c2c0124203035070710811070303c1d010100d40c000e140258071000115244046500345a102084074025000b1240030400c5101c90607050343c0e0200c802ca400410a081070500301c0c012070441c500400c1c0b9640041c04000444119850741d5440e4100143c030f4119040200b0701a038202c07640040e91400d000c2e038240030381c0341c06015445000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 304270440 1250 304269190 304269257
    0x411120a0f06050111060c0d0f02041d070f080a050705360307061e03091502030405060f010302062b1d06090a172d070323120606040510 60
    0x6400340d0140761144001f03030500c3c144800020742c0e491454059000850280b010000440d00c2e65a503c221703a58448001e0b0070000c40d4040a00010150781c05281041e0303001003a0351781e051082c5d68080317642c0024200a001241440424001c10b404100d241500c0d1a6101618400d07100c40011084400c0e002e07181d01f8440c0d84250060141800700c00d40c000ca075942882121070990703c1e00d25070705005034010000160044d01d00413078941d05099640031a001140070310f1190085a4031941c900042c1030750840280002035102d40e007040030f1440342d604c602100c0c4c0c0503102c59001c516480300c603c0000c03080741c417045503081c1e4458a4001c6503649603014001c003648402c2e09005080075204665410103507071522800d10b181d400020a00c40090703414050110009504c0005040d214844000b0301c2951b904155000c40c00518003803500282000d506003082880c511151000d0b01f00035500c0e00c4821030940c01003405810003014080010540c3d20161550b0075503031941c43c1c01042203502908640c241824016004e090f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 304271690 1250 304270440 304270457
    0x30b01230c0f010b0d0f0618050616031506030f06170a05073302030903070605090910030206030a0f0b06030703141302100c050f0105240a140411120a0f060501 70
    0xd038680202c0000c01030392046143ca030803442407420b0030007455012000c41e0640342300c403641410050001821401184100344d4202d1450142c00111b06a882046400500c0943d481080201500a800031440e0300d01d00d410128000d80c90301c0e40c800c103100c8002c52890382c40e1320892080c02841414000c10014000d6003840060090b84281c0d0001109843c0d00918000c1c1c000b102124000740c400d0065901a50000303059408495a81c90002c0c201e401030305c400e91240148c0000b140414034800328010480b80c2c041c02d054110703a186415100100080c100840a450701c450000115540f0340c1c0095109042d90784002807410120206441c1c00d0800500041d500007200c00804090f907160030180b0040740d001d113000c40c8131040c103103001428032500710f070604025820301051141c00d5844034400c80f400c0c00d8103817036000a9082c1d00100001101184561b464100300302030003020b541003641001c0c0102114084240c40c00030b41c54004408a201181c0e1380d5005542c0b81c04c1c20400b490f0358000d62006203000d1904454 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 304272940 1250 304271690 304271711
    0x9041e0c020c0a0e130f02031212040c0503030909040b060406030204090c06030c05041208030703020c060f0403080c1c0e0c1c0209100e0621010c0c060e06100303030b01230c0f01 78
    0x85c1d0f080310013006404a184888403c0455404000c1d01e01c16040100d803813500c1e106519440701d840017040d0b504035072220720b03030002161904000041d100c24840c0206101c4150b280c507202c0201860b400340c14160025100d0401102580300d5004440d2124494088158400d00d040c0f0001d0031201c441108508202041008000c810340640140d1101a04a001541c0e641c580c0341c0f0030350080c0b01d0402d40c2c21481c010481040010700c4841070f51485140a03071a60768403607070703800c0340c0540c14450032071030f4000fa500411a40810844541c00384413840340250031201e100e405500010003000380035042c410000407400d01035085040001c0e506411400055500080030b0070641030b0407106500a00e003e000d0320000050210481c0080c2d010030bc410307111030003004010b22581004040d88034040094480c3c6080420401181d40c0000314036214983c402c500703100c01c81c00e59030120090104030411a0400641404131656290b01045940000103004251a51001c128100a0a09600c01c50011040e45031951310038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 304274190 1250 304272940 304272961
    0x270e010b031f020409110a020f030f1e1317010e030f09010503060d0212011d060108071203020f060a0f0b0d030912020d08031302030709060b09041e0c020c0a0e 70
    0x1510241101400400d8100b0341e403414020702555004480160820841c080860304013001450340083d40c1d404d498801c507000700380c59540d1160200900b0780044c104001783c45103c11100036503081d050741c1c8003580340c00324011158006040c55003080b10165902190301808520910654401610010186040001c1036040000e140140c4200505010002000071039039504d056441072001d40c01800500c0e62252281490300030000032020504c1d40810820a40010320002050b80c12204000001d001c05410004e05403018101060102c00f0f40c8152200715640d08400c2c0300355441041d081000080007030f400d272040300613200b1034080207000d031422080120200b54026551015181981009041c106691011804103031501e1400780c403208010061201304180060603d00c1c06008038119040540ca039103041b000c40d4000e1040044100b0104010300c1e807400c054009260300360a000111400140d80b009550070b40700a8480d000060b084140406050f20f4062076010107400070b694509201e140c590a0302 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 304275440 1250 304274190 304274203
    0xf090608070806060d0e0c040b04060e01051212070615060c0c050103020c070803270a080c0d141504060c0504060801050d0501020403051203060901061115060a270e010b03 75
    0x1c020000c1030400a005601d42408951940d580283c0c10041e0301c000301c900d15140e40c81030f880c0700c2c803550800518041c61719290045100307807100801e1200c410391800081003003080320180741c1d440c60300840070708125422503070b0041e01903e8018200030543d5141c0c1035290542c001250040710500141900410108491051a0302a0b070802e003030044c0d03500c1603440c8a030b20b00302d4540d101074890310001525080401486050070342107510901d00c072a400c2c641c4070810282107418040e803086640420800c1c00a0305c1e0205c0050401e43c0901841c0c5d086244c994002030402e250320021000e400c150805100c1000018810010b00c0c4d04c0c9441c0c81403c160070840010b1a807a010300c6400d100301e071103180403814004298105c0d00210b51007001c03540c01d8620120040301540088071014400d04000c0300009149000d0b04007001100228800f030501405e00c452260451040904103540052800402041184514542c4090305054682c0088803442101d50b42c0196200004a140d46e47d0600000c07240988000805 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 304276690 1250 304275440 304275451
    0x305070504110313050c0a23061c09080708030115110f12090a0e0106091809030e0d1401020a030b041a100c11060706060513050c040909140109050106060f090608 71
    0x10b2070000491420420310341859525501da03c008003480022340c44090140740320840340340024480003a80814108030b0303217014200000d02c01280c44554400030700c2c01c2c3e5008003d4940300c0c0c48a2800c00640b0340701c0b102c054000b60840c240400c0d10f000448402608a00c5a29080c0c0c80e035001041880c00d44001140c80f104002c1d1600780340380011680c94016980d0b03049042c00317042524001c600540e2340b108020309030320284c03040303450080814084110490041c06000304284c0c268554400c081d11040500c50050300904040d07c108500b02c07452401d001081c00107004400040d9008a20000d4290400c801c643d80c6406222855104543c841c00545035042c048501c003d05080807460641c46040c52038141d2000c2c00040d82c06000054440c040007803a03804103041d01d40980d0014809410304103032504035001900c4601c00e0000c1800b0820440b0010740240000f140300342c0a1000382140e02e00d4003429220000000c0344d4503515034400740003543d4041c804501611031846e110085d40d290240241150501404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 304277940 1250 304276690 304276711
    0x50a0516110f0d0c120311091e040603050d110114070302130f0305150f07080c09060403060204030819050313030c1403031f0506090303120703140c030103050705041103 74
    0x70400852405000480a02e070014041d64006000703560000c0c181c0d03c80030b81c2111415007900388404807510921880c070f01700f0f1100d2452031a2030010310400000200001074400145a03100450119841c3d90041a00542c03040004041c10b48503000040d00c1d4860340344031300c01d40381e01d41308074070780001031041110307810033070f58100140e492605680030b82c100c035001d8006010300c42e00c14100104005000441c05c4152092020200c1c1079290211001c0f0712080c140c85150000d40e000c40402e00150321400204400c40c00141000d18090b41c83e5030314401c0ea0065030054806150200741084505581044641c0e104050325200d8a503103443c00c407140180b070b8045009030800899103044401c110210a040064000311412281c6030b142c0034000307050246c01c045000d181c0c003007030540000c1c490429600760365400c507000300910705018032401c0c00e18010702e008240c1c004058598845245155203110b001d4007900c01c0782c0d080ca81e6076056040c00391415100d640718a00651030302d01c0d10740524402200781d940020138400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 304279190 1250 304277940 304277957
    0x1090312020703090f03050c0f10082e0b091306030506180307020603010b090a090c0212031e04120f0207050a03020f010c02030f0a0b0f011203110304180e01050a0516 73
    0x18101c0f1000740705d400c00c2c4074405050310007000340080040d000c41a0074045401c20b10705800030081c080f2444401140801240100740441c6503003041308041101c64030180d46106282503420164101283c65a00480300944002507291144c1086072011240c660a008180109071440d55201e6070b039032008050030781320007042d41c03110103401d003d20443d042d950f0004c0400b6142e517142c110404907540840001c1d0320030480007000080c1001ca5005a1405136920f801074220106221190082031f4001403070750000300807070a19191110840d00019000341d004a074001d0703510522400c00b900300252001d40c02d09651002004210300d070f0f2808040c109503981510304030111609000162080c422240e8008d51500500d11042501c540009401450501424032944552504020760090328820700502d0080045807850001007400303100c52030341103800c0004891901e40e1300c541a0080306812840c1103000d90b111805c200f24100240074060300201d803030070100901d0810240039a000c0ca40c050002c400c0c031240d40c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 304280440 1250 304279190 304279193
    0x70e010c030c020907080a0b240702030a050a0f1a010509010303110f0d0305061008061018080715110c100e0105120a0207141b1507021305100503010903120207 70
    0x34052400e00343d6014000d1102418202009000004200c4144400b103140001d0000f0910b400101c0c00c2601c416400c031581d040104003002000d9604c814400e030382521840106600140041218050301401041c528603048041d01d0aa02c1445400c0c880c0610010441d006000036995100500d0440f9814103002c0c111400d8011001e0810703500b0100c03518136000304c2e8514a691505030f00200d226010032105811100648001500c688038113481031600120030f9101c0ba1034841c000c0b1148840703a5114141c040c07107503a4030001d00b480c0180c07580200e60801d07954803400c20700a030005000c6040301089406045200140380208100c880300c060314800b0070030380c4a2030705100e034065021588035004400b00001b580c03400681103006540603040440b0b514008810800108101280b540d00803030701400386806014500d41000180c400100c603c0013000c204102e84801030382c2e0000fa100b40d01118a00200d050b180c509200d20807004a039100c140681d050188201c0000d80c4190101c42c540e141040060301c400b2507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 304281690 1250 304280440 304280447
    0xc0705030c0a080d0807210e0d03020a1d0a030f03020d090e0403020a02150d0c0c020a0504150b0703090b0a020c01030c05030702121b2b0309080904020703030e0102040617010b03070e010c03 83
    0x44201e584021107480f81c0e1000c01c440d80384c11092a400c08c580c00c99207007410441e8120100e00c1400c05a02c00a0942200d500c4801031020500e04120002403100301ca09442c0d444444417885010000ca000d640031100145e000b81d0041540300081005800000480c645a240a0f4580c600c00c0402449456880b0307003020000c3c05401075a91100161408014007500e240000d4080590501d01f688500030b00000010300f85094041c02c8130f601e40e0660071564a0b85801441c0c1d10316040510700314140410114081850281c0c84060303c001c011030b6000b4001e00380c07114009030440e0003170f101c184108401007080189250300000c9a800841c1c0c0614034a81d980070310b50012060540d2182035500d10b020b0014140c00091601440d030703c0c80e0540551b50945030f0a00b203010780c100c90086400901da00002d00240105242a6004d000041e000741000720701940f440e84d03500d01b282c1c420380003400481c0b2043d005443d0150304003040e50240c13447c3c6001130b1850406017405090903001c01282c0d410402580010340c1018072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 304282940 1250 304281690 304281707
    0xe01050d0e07080f01050903040b07021c06020a030605040e060c0313110d06090b0a090c0e0903070606170d210510030c0e07120c090b0a03060b0c0705030c0a080d0807 73
    0x20504241e84100741c0f156a40e5888103140b101048556080001052224401104036400c466601d03548a141510756424000310401d940c403264200b03160300200070007240325030009100d010003650b400202d40d800c103001c000840310001075004060b84484c08004241140c10b04a0f5049a00056400022001860400c6900c00c094101c0f035004004002c1d4002082059003200d4065072281401c0001540d445910f001182c5c0c4014000d001d00d142d9220030405030107401000758020101d0005d40e85009000d484071015646503600100b44080c60300741e401c0c0c54040a11010b00e60540601d45a00300e0b590403c1702c008011300c00801d1a030101d40d03503400300d101c01101201030001594013000011001c0e03a240180390804504564032004103140c0074090351450214032030301d4030210351a2580c40f695820700c03402c01c101b83c0185840a080c50f03034500d000b10b508040d0001030b1000d050400e0080011508101c00e243c00c0001640b56180225400d0750117014070000840c0c1600406a0741c980440c461703403900400c407602034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 304284190 1250 304282940 304282961
    0x18052104051807080105030622080c010903170106030b180606040806041208011a03070806060c030705010905010c110d080c070c061106010609150c060b0301050c12060604060e01050d 80
    0x1250400d081c0c002c2c001c2c100311038452a11511a6100740c1c0e624020b01d600c0d68000c44140b00d01c1071590101014204198210014050080600ca400d112440b50b8190860703981100940100780c200306c2e40040b40e25003081d02c4d03000d00145d00e81407040c1d00c00d950208601004540c21072020660450014402d62280020b407001801110308a03041c9040a051440050200c61844000074107410300201d900c4d12420121480c3c1032603403450070701d155240c12040300d961102902c0a40d00030010810000040c01c02c00180900c50301070b00002420750f4803450700a08444c0803400c0c00c0c041c00220402c00d14500c4012407109030b681c42c0c50a24001030b540c1c80c03580c1c942c148100e0b40d0041c0900c50004e00405d01c558840880d600029220301118050f907284d04090b51540c22030701c12000031004c1c0c002c5109050f840742c100074403094440c82d80410318210610000c2c1c29201c080714000c021540120349198038000402c4001e0b080b184c242d407913929040c20b00070001e04180b071842c0c3c014140140080c044440007a6544441c1868 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 304285440 1250 304284190 304284199
    0x30a0203010501030c0311100f03050403090512010c11210c1203040b0402030c0121090c030503030405031314060f030c0d06030b01080c0105030f04032001020d0c031805210405 77
    0x5613101d25050800d00601d02056461103120881b10110b400c001120364180080c90b154490042150b100c105c0103442d00030030803820000c681e200010692a04003125154800d10300002c1b80c1a405003400410402c0038840000c41035000114024a007040d00000c0c58a1085068400b0354800303140441520307000c0351410b80840104000100401d01020307503042c4e801103100b03c0c280c540012003000111508184201000d5400c1c03007050301149490100d9201c109650712a441080c040c80c0d407910b625055400840b403d45898200140d1600b003000030b0907619029080041042000e54400d002003601c50040c0e02520002c4003000010402100d10001510002f140680060180c591641707444a8200000c1c03194020521824012800b558014400d0300d10900400050702c21541c5c0b240c804030ba05280400c00009810301011507402e010400380000c00210081e598046810f1444103002000c40f01c0c0c0d0055507200f40d05001003d000148041900703051031175650070402d0003210b100101d000038410f03a40200d522 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 304286690 1250 304285440 304285451
    0x6091b0306020703030b010c0b01051011030315180c0301030602030703020c0d09030b01051c020d0f0f03020d0206070f0215040503040902070609020f030a03020d050c01151212020c0a14030a020301 86
    0x801c00590000c10301c85100e503800b407202c8503d100055440031148103000f08421069801802241002c905201c50788440c2c0c41c0c81484030301d08001c1141103138003d82d03900318000e24a0038030121501300300301c0780e1510611481e00c8001524000c100c80c00e03140410300008265a80001c00306035224801e070103490803009004240e69040002d20000341c07581001e84401c4440d4507045000184c1840c01402400000c641c01502c0002c6210036801c00065004400040740d004c8421800d01d408298680c9101011a200790000d00b10303850000000b900d0064000d200300200b06000c2510614940e000c03680400a15609a958100342c0325403402c1c500b580283e0b041070075003601c0030901400340000d5070420103125009680c0d410300c0212120030301d41c485100700c8000d00075912107504114298490401400c402124900004804401e40307049003011066900c501c0e41003405101101c140200c01655802000d541d00083c12241d0b81c401c00316140700c0305803240130707082c40c0d03c0c468950003902e080c00314600d00c55006008111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 304287940 1250 304286690 304286693
    0x1060e09061008010c0c02040b1516060e0115050907020705030f0d03050a060509011215050106030e0f060f180111030f010317030403121a090103080d0f060302060706091b03 76
    0x29500421039811664a0242d08000764281c0d061199079a080d015648400448500e0303024407001d00f071074100e0315800c000745000a95205c076440000d02148258000122101441c0e41880b4058600311aaa200340303034900744039000c070040c8050108044940540b884601a40c0b40c0c1d8040e401c0c030410783c0c48076405000c1d064840c181c01c40046502e903401d01c40c40d10100301c66161004904103c501c40c0c01034540000f0020010301100c84120988124144600e49211603e0300740c018500581d142a44540d011944070a419032059105216601040000d000142403074a041c00308418510005803a01e0401146000c01c1100801d082d04208000d084034024030b945c9040104941118520902c0281d4010600d5400d10070718291702c0e011a409103030150303242c418440d4119111401010801c4402000c511850688062519103089060085010704503050300c41e810410b0f5a0207640c42d40744200d0403c2d141140510059590b00203454506800113400910303080f0b14984040440d8400c001a140410060030000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 304289190 1250 304287940 304287943
    0x10c060c081f0b03010b1614061501051207030b0402070822060f05030c18030a030e090603071d0c040e04080301060906030c021c050d0213050f03070303050f090301060e09 75
    0xa0041001e8141c00c0701c91851141d244840c0d01407406001c5140f8000c0004000c1c0e5903a03440540000a4014070725032001070a030ba121700b09815800504c00d0303150406400c0080c4002070300c01c1440c2d081c101f07007030040c504182520422501d0318020449001d040c1d440160212649655050704c200345d500058403695041801800308a684140c4106640085032403001700751548603032040c101d104150b440d40d030b095840306607011b81c41d9080031120f0f00807840c50800303410465400300700498141d80203817210b0541b90401002e0008440c0000c045500079445508104641710006605060300300e03100f4003880b01a198014401280d01c100e90024040c042e00390184824402060f00442c1218280d450758180c00f9030395001507040d911807001150160b0003020803a40e24906840c2d4269900e00c1521301940350000780408981280c01062070300c9141ca010000034011801c01e080180e402280880c020413950340381d1b0790010100d12513061030a03010304011500303e03820744007500801c0213005d4030050f04001e4a003211025 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 304290440 1250 304289190 304289207
    0xf0d0209040501062109150219031514010804060f0c05040e09010507080106230408030405120106030c03031116090504031d0a05120c040213060f022406010c060c 71
    0x2584502d02d402c00002d8264080e140b560018041e036061451907070301ca112100000c111080007614405051703064050001481e01c000c01c0810058001400222102c2c20018101e401c051441203214000d118180420b030300302c0c540000908400d2078466001e58551810718094180400080b001c2401c20402c0d400017600200070300107480b41d0003a07200f0950343c0e582c00e050a8900903102c0d003005c01e4000c00148803483c4a21405181041c9444c0c2110303405641c5464501558444c1d40214103d0300007080c01d00091130180704500701020490003c0c04800c6c2103032240c2420781d030144002814024810251105480305004842659441d0503518160964802c480b1010700022101180000c01028070f40c3c041c00010758050815032000340558500a0030034003885060300708588120342600c10044001455039450008119038560b011101241c28507001e00541516039849202c429504070120307100b075036000740e44140780c0c000c0601420206521041e0041e600c1c40001d04d406010741d420014821406a00f01014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 304291690 1250 304290440 304290457
    0x702060f0915030105090a0b040915061701060803030105011b05060c0d0b061306030f02041205070812160f1a100807051516020f091003030306050402030702030a0f02030f0d02 77
    0x74440200c0c401c40c1d0702d0314507200901425034001c0084001c0740b0f02208541c8540f51035040503000140c1100541c540c041c0403080140c6640180d070320b85100740900788011445062504260009000c05da040418240d1207010501490381001580780c04690064213810640b0003081e0010195201c03802e1004d6488420ba204440d44c8802904222400c655820003904030362214400c2c0c1c10200c5494204601140a45800245c60006a4092001094681071a60358a15052049004100591601c4171140c1020b8451070b180349201c200b80080581c80c43c0003008041d609074070807418070980015103000703425601220b400006e1815000304114241a40c0c400c100241d402c400101d440441c0d5800800041d58411250209070301000e101d440704500312001c2d079a2400b8401000f038248000312801142401204a452543c20000102e01700107064241c81028042d00c8152070a5203180781c1110065500c0c07151007944010032600400e01480c140c400d00544030b151502d05035041d03446800c0b034009000794000a15 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 304292940 1250 304291690 304291699
    0x2103110c060304020d1a0f090d09030f0308061207060509030c2409031f0b0f0f0d02121207080310090b15031e01090c080a02130b07080d09060e19030503010b0f0702060f09 75
    0x2750485075005000640c200d0354082e00941464115503400c03100103101400c2c260300102c04181424010805102d494080c0800e50b848035110410441018509500100650b009141d8500ba5030034074000b01c510310680c42012103030b0a40c0e8a64000100c4e2806024080c2c0a05d0810502c00c0032500e001c1c2500300140340c0c04125402c4000e028004100958102041900c6a01030040d011030310050a01d44480710888600ad82980c500003200004142c7c0c0d5844102c0841d41c0080000400c405101c8400803175011784418182044030040bc02c0c0820794180035030901c0c621001001c40010f0b140e0440ea40c00f00d0314414441c1c0903d6140d6075030100103002d01003821610000c9003000d400201c030781c0068425917101515441c0162051450000d004070140c0c08221705a40051040201c1c00217641c1900501c0c80c0c00388101c00002d9054140c4a6060401d402081424002003404004201183e4000140c034190f948000003a540c0c0c4030841040c6481c1d104001009401203400714414100320b00e0f400160209031010355 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 304294190 1250 304292940 304292953
    0x50103020108160f1209060614010809060103110108060423090f0f07061413030b040b09030304030f0e0103091b030b01060819020708042103110c060304020d1a0f09 72
    0x1240c091040d07040034500c2c00050304c240084001c90700c1143d4400c6080c0d4070b480d001514060355220b59003518143c0d00040041410701c1540d41841d640011240d034080c44075800341c038041d4110740c2c660700084580744d03881d4100100f01c400300721156030300c3c1e0011a040c0001c2040d155050324443c10600f4100b421901201c03031f805905040e0079410b90102e405440c0d070b85020080d0103020304044043e1201a9140c403c510101420300010004421510038940a107000e181075210920b0715103803004031362000406482a581007401440700282d0400416210340d481800d20306138004803800120b000f01422100a840c1414100d070007928041c12402010590b80500150340003603030ac40f8820303660903500380d4883c1612030381500040342c200c150380e002c1d200e243d11400c4000c0c40e0942d18290000484039611200e80807150400da07c000701070f0804c43c8060700c88008400340c40020800000113035507000041c03002c0c1c001e00350004600100008a003810300c1c14203016a000410f428a410001c41e8540104d0b5203101c58407440707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 304295440 1250 304294190 304294201
    0x60103110d03020616020f060106020f010b010c11010e030f1209090703060303081308120a020c010c0f0509041a031f050702030f0406120e0706020c040f02031e04030509090a050103020108 82
    0x20000c041c200d41c00d90014105511510703900312881105501d030f48214003801d51007080100c02401280c0c0204001d60080183d2001840030500310380002c0d00060521208241c108000780005480e07a070380b100d0034240780718100ba25801007810090054500e114900441c2c00e011042034000000e44140c40c0300b03640820503941d4000013541143c61078080600032444a00020703441c80f03040c4402e00c000900c66004241000034400e003640040ca000e039000c0305016004944007041807424824407014014030720b401c1c22001070016010303003544903418405008980310207103c5014a9801c0e00100280d001504489640e41044611144040b0203aa510340f40350030705004c0764500d44000190b0703c0b601c5403501c015203001d00e000c000b43c40608007480c00442d40c9444140c1241c0c07400003404850b00901031500948209104403040108403049009045809031050084c05082914100c01c210003002010940d54142c4980c1400e6600d03005a800855100040108010000065410041c1200d2003138070b80c5c2c1e0320f07901c45 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 304296690 1250 304295440 304295449
    0x1090f081506040c020307080c1006030b01091b140a050f0703080610080105030d030902010c0506010308041e03080901051c020d0221070215150904050102030f07140306090604020c0f06010311 84
    0x4421307920005074428400c21010802c10402030144007101011a59803414020100301038400d658000da8501c0c0308407004004100d2075018120b0806008185010b5070303c086100601000c41d03001031a81c030381a000c105108418000c82c00c03194802c03141404603459101510f0010301004003110b141d40180780900e1891070380c2e40224569816605d004000d0480e1010100301100104403c9006904000890098001050090003034a01032760148540c0c80d516400e000c5100c0c800405080811003612903405d0030000301d03903004151f8020402c01d1805279507942c16070700032007025005401c59580c600d10000d102410f0030025401000d00d0003c50715150b000c2da80c2d06901300d190070000c640310701c05038000c4440084040034031142e441d444044480000d41e2101c032980800c50841045804540c969800020b20000340181d0004a5000c041807510044e08810b0b0003210202d40000303442c0c5405051044045202c0da542c90b0152040700417181d0868a02c2400b4074109941e4480a110603200d0032500c291040c044d080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 304297940 1250 304296690 304296701
    0xc0813050102071508041721060901050d02010203040e0916090b03160303120b03030d020c03040e13050d121e0c18050d080c0a05011514040212130201090f08150604 72
    0x30340361100c5d0142d644644900258038000b0103020b840c44420011948050300182020000c0014601c200030349141c017000340f280c50441030b0405803056030750018141c0180ea00001725010740e440031503121116201d11036503d29241c4403490000c0280300851022520b419554000121180100c0488860b100c856100e015503621380e000c0a4001205203070000c5040545401c55010034502408481c0b8121030110007a04a8020361008182500005010000e00340340160706c5801090724005480c981095036542c5559103401c0603244244060b01c84030081500d465809210b05a40b86402c0300c0c0d0005014094800070464034540b480481c3c546000c0c000d040f142846001c0030754802800c841403000c03407500c50700480d411112404895104182075200041d90a00804ec20b80d000c0e0b45800c0d0035a03050410040d00c8003c503421075800ba520510000040b083c209410580145c03005001d2280d44200d40012680c1d05241c1d04103e06111a40b1000584d004001820840c10038190600c00b2203900c0d07c50401c030941c1c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 304299190 1250 304297940 304297979
    0x60206040b07140706020711040c030914011b08040f020d03050417011e0b0310090602040f0902030708130f0512041a1305091003150203150405060d030e010c081305010207 75
    0x3d0280b14090014000b43d00810ba0f090081c20211407000c110400a002d075178180025600007512540003070204500c62002d03040c0d10302180c2c028048400708440510f443c140e596110420050300740c02203410700c030481d00c150b00ba041d0046c010b800d4038181400c01030101e51061107130790f00548440c1c2210016800601c43c01131541c80d1000450030b83e00d00e00c022a0060b081ca150915403501a0308040181403600c3d1203069107441c801c590140e204ea14242040308406030a5001d0485540100300304110b0941c0034511a900c10704014010f003000340c0d03a08140091003907042009000b0f11445640c5008003003a10094002caa014440700c1190070050070112045000b01408044a601c5111060041c0e10307001b02e001d40d200c51203400540004e5a070362210700900380038131213006100c1c1d400001d0002c80f0613030000220f016401640e0030b2110742480c2022450000c208000038040044036420404680e11030380c020001e81c1d402c20605500c540207050b0010b0400c14503c0380710701602c541f5a000400da107d0b50017000014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 304300440 1250 304299190 304299227
    0x1b18050712140a05070e0405180606031f090c030f1416060203040317190305010303020d031109011d0d0311100e0303151503010b1201090b101107080601060206040b07 73
    0x1c1d02c0b6400c034803020f41300c00780c4258180729003040c40700043d4959102e150701c030300144c0840f15848001031000e14103000340174003818041d40007440c2003000c00e0491040030140c849503550001c0c4041040c1403101e420440d41d040200400c0c1c61008490902c4504401c5000c50441c140a5810036050405000c807042c009100d071001581090004002140084141c84680035008510030325040c0621700f11200c0d0b1800102440101e43d81da401401495410803900d101000b49003001c200e544120400440240100400c0c4e604109460b03021141001d2070a01c0b00140d0203014200103042c405d60b1502402881c0074904840c07203403141c41142d00d0340d60307003501039010203070001c0c0060341c55602d5840012204002c010f0005401040407183c0401c1c0400c584c006500038540003c44580315070307900e0001c0300c0500c0103074084424141428407219656942000d13041c03480449091006d04c0d905995241030819807a5031060784103000c0c4400028441c0c0c1c003c11880c0c4101e100e00e907020b41564480b0741c1550301d0740c2c032590704a156 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 304301690 1250 304300440 304300481
    0xa0c090f1a090d0b1807230d1415060102010b010c1e0b01090f0b0f060a08070c08040f05040b03010618020703030b030f010b030d080702060601050c0307050105010b04061d0d1b18050712 81
    0x47c4008440c1942c03001c1c102400c00c2c4000c503540e49a9444207551400240c0980d44184410014505a01a8144c10031000d2000b071201b8500800001c0814041c810302800b205a0b0348031903603040440e401c81401a56100b020b1803a2580d51f00d07840d100402078052240e2503a81440095000c0385422507140785c80280080650781029541d12080b20b088400030310800902420314640000300304010301034801418030341c1e070700c403105801c04c0144803c4d904403034144e44c0280e050103001d0090005032407540d840e03014095001a2100001c7c14220003800210264a41500502010985800c4103412410103500c050301100c0b507110031508201c508039021200080140c128102142c07803584a034000b016403250701400c4904154250708c4450031228207901a800440000508000b0b060b080700703403144001c5084400d0f81e03c0c003914001040d40c4024501c0d008043d81c0000c51030220300104000c510700134250303100441c544a075030481000010101039820202150124801035814041c070b001f03000841c181c0c0c0c0301080c0d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 304302940 1250 304301690 304301729
    0x10e060403111605062208030c030712080709090519020c06010317040b0f0a140c070303020f01020426010908040b030601080f0105010c0f0302071d0a0c090f1a090d0b1807 75
    0x8144280d8006c26810140700c03400060180080020f08071201c800c4010799600c4201340b500b030400003007001c1c070301c810b0058660800c01c1094110107010f08a844886d40030500c0d680e9401e00f54105801c2d01c242c044220310100360131500d600006481416603101d82840d0b004a00031b51610070860103644198190039a04220212800039410040c00c01d01d642d0b070900c2d1035003100300300c48064260010702e142046540560f1080040c5607040000d00e692002c0e0310300071460681008074004000c484040f02d44200c020682898056200952100095540204080e929281c407122116980e2b80203441c00307400101c1790008145800031441c034bc05c0c12032700161290201254550380e220b1a02c9402041079096000350310700003900450241d03001e4111114011402c0b43c0d494200d180703c00301c9480303c209104101d48041d00b40202c0580814840544803440480c1e4a10400380c100c110f40761007003074034064200010344101c008026009407624018490300340102c134a030a035140c02c01d41e00d468601c40c4031080c2d03441505454 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 304304190 1250 304302940 304302967
    0xc1906030c140c03030402040501170c010c02030705030d02100506100806011206180b0102010f0b0306010512030c01110a110f070b180a0303053105040e010e06040311160506 76
    0x4514007a1800d0840070700364400c40d2036a05400c52460484290000020403086113800e1103503901525055020301910148020f400350303107621801d43c10781405030314071403a400e42d6000c12814008080060403103101000c0003d0094458001c408440358940c20a40412454600111042944038031543c40ca4603a0fa101e0b001100c076150180c51403440d455890201040c000900140000038011084004c81c2a4000400081c2110408000c1880d914581140c5100c1da6902290107411650112948541c01002c101c00c10b06500c11051254040d602e051160081d90280c240940341c0d080c40d5841d65034480040412454980d480552455466045903400b800001c005001501358001189100542c222a1501080f802211600309401107400400c4019503940468017082001c00c000c0d18591100e0381e500064008554240513180c400d580300e45400745180c01c01d51207511108091002c0b159141020706010f45040e40c9020104500d0291a40c000506840c00d04481e04131100601003c0c03800e9483c09012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 304305440 1250 304304190 304304201
    0x2060903251203230103050a0303020a11030c011b17010902030901060e1317071e08250209011a0429041e0f081905011b0c050c190603 59
    0x105040d0103401040404110907803615400640d0030740b0f000800441503c400c0d400040511341c0e500e00303080700c44014400504041307000c5a00507810f0902507280c40c075010095500c0882003000510901c008100c40d9940101500700c49900c00082ea100302030b50101480845e4401080425072481c06a5400100300d4440c40d5401541e011510f20000128203071101000814054191a46140b0304807441500060000b0403000340080f104146a8074640752040c1d40d1841801011940151380c200700c2030300d80080c84807003800c40f40201585035070a03c46100d01c0c440d0728030000d01000c041c0e0059800500216150a402030304100803400100d0f2181802e2406201c6070309103c18250301d070b0f0030350004010584500c500f08060405016084825020603a400d001c9100c15110b40d0b10a5270b455080420030085c190002c203401501a8401000100c00d1042c0c6c1011405407005141100210061380b841081c0b281c0c0c008180c000a074070071030503620040e01d440204007441da1212241c0081c881038040400845009134041e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 304306690 1250 304305440 304305487
    0x30a2f061207110c040f1401150212031e040308190b15090a0308040b190311032202100e0a0801141603060b04030c050f0109141002120309150702060903 67
    0x221085402c10742d003c2401d40c1c07540c0340710754640e0361203074084240480d403181124003602c103840800e403070042721b4030009555007a8690100c05982c00000814812458010380c054240c4141803a5502070030540b0b00100280320440c0c00490101000701d0300b10500c013003401040d03002d0400801c0c40c140840e03481101e140550160420981c03040c1003d000000085003100540020501e110f1030715142c030001d20750070054070496414038007010700e0009184412170621040da504000100c0348044890599203444001004011340690b00034050040302182941c410010030442e0b50540b02030410a50ba18002402e0f10400103841201e00c0c01c1c9000104a016200c10600005041c4d140c081002980c3e90404180780d4485d4000b80c039000c0300b85e0720500c62403c111003c83c4e8001828070300110000d280a1007010103031030f014a90b6204a101c815071950380c42c801c00c02c0b600040c180f030078115681d0800d100603e98070080012000043c2c40140c001428840c00031a4080c49290040b001e507140c40c40c45107540300e080c3d209000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 304307940 1250 304306690 304306693
    0x601050d0e0706080f310609020310060504060806090712030c0c080625020705010e041e0b090c04030b0a0c1106090a05070911040e0402030a2f06120711 67
    0x141c2903481000c2020340010305568075008000c2c00c101d4020800804010400d80c4000080c078903c0407070700001c501d01c07031010034105140c0c0312805103860003101038054a4400ba51500c2071130809070040c0c0041d0f0100c0211401210100845a03451000b207444000031140b408858208400412203080301e004241481032203841c0c0003840c8081c80da036070f6000041a80095860b41e009400708068940310326608086c034224241d0242400c4a10352000756100910301880d810090107446501d8103403126080b03000b40c003076481c40c1c1c10080d0640e010301a006000d0820014803c030400b46c042820050100d08a900341c1750030104040329652408060b030054120380c2c0d500f034100910700c05001004201400494080c0c000317000941241056130501030715091094110b154603d1502005030b400c00c18041c201c80c1220f04a0394080030b00d82e102c2c0006810441d5803d00500480d4100c80b581a00040c200b050043d290407801403582d00c0706842062219600403070b80882400e12442c0c010940c160b00880c4090822201c0d0b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 304309190 1250 304307940 304307951
    0xc0a03110f090f04050c04020c0d210e0a05070b031303080c04030b0403050c07080f1e010b0a0602071d190b0d02040c090501020c10050a05030702031e04091805060601050d 75
    0x4030300410702c1240d200d40800d4034102440108601400302c060440d60494055041510f9811407589802d5518402018004e841c07880042914600080b0f40074605449820001d582040380c034591210340c044c0c001c403800c0c01001c201050320381a5605482c0181e0b4401c0102d25058035030790703040d25203900181c03405088040500001000541c0424003d11551080c4d5038503442d03258180004d860700c591a00f103116039801c40c004079045405d00281e070500143c0c4003c0c4404038401d0144010340109503203e4115000301814002140302500090b0000c01c80321080f48010f184402e580304401142e4095a0802c040c4080d072468000b00f0000703403c1481c140c02c00030103003100341ca201d80c0040e0032250101410404111880d008019940e0107000d024000042a103542043c600c3c1c0742c50040c21845054421000c0c00300202c08541241c2c400c000341c4809820b040d0b500e80800060039200300c040d0b0483d1264030002400c02140c105142c00101030700c0d11507540326000301900c0c0c40b20303401074400350401c2c031660010f80e43d1134 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 304310440 1250 304309190 304309219
    0x106080c0f0c0a060603150504081918061e020705030d0f1e18050103050906060d0f05030309031905090109150c08070f02030c030a0803060f0d05030705060f010501020c0a0311 77
    0x2d0110b8081c0314854440050341506d1854081c1d83e003d800b42c14803102e140b07040200700108512208030303150075401a108020400f104281610529075051403428400b007120300110300650013038000c0e0180400041104c0764a0300044040380c1c0e40d1640d0007660b816400c40310703041c03c200e4020204203040ba001e13030905140d81010801c41003000c0c0f071116000c0c400102c20702201d200c00202103180c400941002e1806111910b40225181e5550002804242c069403406050b041400518401000a01c0d84201500c1c0d890502c07040c85a9240c001705c03040c80103208446421740126001e20200d801d42e00045c3c4502840c64645840c14640f4501d000d100010300c504070903d03c0010302d500008000240c410045010b00241c907005262514013118031044c000d90040600e4408240c0030700070790b41d000b10100c504101020f405c1000c5130045101d40c1c0c0080c15844089031201c20404007181c0e00384520307003060351000070303aaa81c001260b454448240603508078204107030a001051001881401e1000d01418480c2c110042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 304311690 1250 304310440 304310443
    0xc081c05090a021011061b07080309030304200f0910050a03030c050706090605040e060f0d0308041a0112032307030504090507032a170901060314060106080c0f0c 71
    0x220740550880e0004107514046113803c041309403a20b1000c0c50310108a81d0500380044e60b42c44080c2442200e440141e003201040000300342160100e944c0882009e442c1c0c02c205201650b0b0390800e440480f505980d840703070391135021035441c0e0880b0381d5200140500180c641070070a11550200c05060b020050301c10303210100d15a00c03080ea030240118420354076006c0414081c14024140f4140ea04048104500d51400300030a43e88081031364140c2d04002d03244802c40d1202c4002484100042c01c0c1c141d00048021454800d00d03410001c814840c0d4040d000750317044031741401c4243d01d8600d030900402035181c00515055021900c03556112042003070a10240101c0045808801c1054000500c01c80005100103000d00010109000e840e4025413141010f02c400c95400c411000080d140d0303407405e55041034051303000c00ca041c400c018003052a00507042c02d800c0380c280308841038041c0400d800160307440700300d0028058040342e0004481e4102c1d10356990349420340d01d0306500c01d080b641c42501840d031041400d011031f05180d6070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 304312940 1250 304311690 304311701
    0xb030609070e0a060806041212050f041101020a03020613020a0503160618030f030305060f04090804140906090112020a0b030f01050a05030c0f130e03130303020c030d0c081c 76
    0x8480001d0044515240b10120719201c0100200180c0f41007001c2080310b00800140103810036405402d14040180690085441c400700704000d420550421062181500e040c5801501990007402400030040f41c00700166581d20581c5001001a0f1020001034501c12201584000301880113082c6820503545e080040d00d4225810300488030620908410007a1036002090308961003072162610860602e1500d03540d40b10003010602605154541e0009052030f0f90308814280100d00040042000700f045003041c98450f001030080070008400f1050a0707007149015803106100b054001e00c411501e03801c19503010800314403c007007240c1100e00c80c58082003404402028501c52115050714404562400381009014010b1b644082d021380c21445986e42c1e180c450304002ca540e0007041e9541c09070510030400d108002e05810040054600000c00c07901e00354054152060201c03802942160085d1007130000705134403565401c610001084c0844a000300040421018162150401c0000c030750200c000700032a825140f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 304314190 1250 304312940 304312951
    0x260c1513080f0c01110a030203030609100e04050c0306070c2111100e0601170307030e010e0d0605041101050c03160303110c061b03150103052505130506030c1801030b0306 75
    0x204184188800b42d41e100c46140300c0407001e00006c1500c0000c64501948a12024101c1800f4408210028040d4860030075010002c3c4203105110350340b46028240f0030f80700e02135507032000d2190107410041691030b44102c4803d0002504900300c102c3c01c140c070107081a1740488002a600512115081c0200e85000503c085e02c0c4140e0a001c02150280100340c4850a101058000c1c0c0014500110344503100c1200000b0384201d40d9040c180311a04040313210050754041c0b4202c1c1099401217641ca080c60800a07250841800b4500c10049145d80700301507001922903000d46900d030003650f8400d02c4903454100034800b070784070450b0080c24002610913000ca04c0e107207030354001d0380e88411980c4554184200c5558204a442c0401155130f0200d046082c41c800c034000214100310841d04154035100410034031078050070b05800c007225084007455296003003003010309540c00c074103521010b2074140840058503007424021a0f22407010440d00034a00842d40c02c400c05030a28080129040540c0c6060020f1140c0301001094000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 304315440 1250 304314190 304314193
    0x1606090506010308040e10031205090315161b030c0206160618150903050a1817010e071d040b04080d141503010e0a0f0516260c1513080f 60
    0x49080ca22100302c1b030940a880e444448040000c01c02c0400d0003000c1401c4440b010746040b0783c0da00342000000740303002407a024800ea80c040380e105100950401c4c0403800503540c420780b1030004000c4984000b440c0d0350040c140140224138014026001481c09100a140301e01201214007404006038480b00c089030001f0043c0b4030840c00c0845620300780032070883c0310078500c01a01002e0140c9031a681d002445400b43d0601c4d0b02c02d0003507004910042c0064054541c000c3c001c043c0f007212034094030800141c0601860403c940c00c0c0d004941020441c0011840101c0d13003401081818003c503166a51559107203400100155085a0244000704401642d13016a80042c01614130920690038010a01005402d5802038503109038036180b442c0d000e01070041409810960048804040110f403070515508000c00348003c500103010002d030101d60703c001c1c4042008001d045003000815006600b600c241d8840e400000789601c19150100004140d84080017000088100d5485003039a5583d510400c0c81c000001c5900c2ca101e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 304316546 1106 304315440 304315447
    0x506010c060b040f15060314091f0b03030d0c180302090a0518030a0914040e0c0f0a050d050a02040b030c061e070209040b07110607051606090506010308 67
    0x30b8000300340c0180458903000c5e20341d002c01010b5004840100c0e02c0e0a501c44070034248500310034400c008036002003074030301e401d6002c81d82d200d440d009070031460070b8480ca1645855241130026103104045410042000824203101901807a14001c03104101c0040c0b50003040075070b4400030116001f04001c400011507860300b5401c41e200084c64281840b09220000700703103013001c0e88045920100c5a0320110745940001c5181000b01f5142c051780d94041035070108034400401d240107201c22040c0a03004001021145c2d5400c081101c0003174035102602e154010803504001d504090242d0348040c10100c018002c000e40f03c2d400207166000385115818811050784403003602e0180c07002100c003011307001485142149000d10700310002c0d100444409000611071011017070403407400200e4038014410703078580c1c60800e038018102c0701d80d81d0a140300542c1d1132910762a0b4000400c1043c0031b1a80a103025403510b0f80d6 = true := by decide +kernel

theorem cover : BRFrame.Cov 304136690 304316546 := by
  have h0 := BRFrame.cov_init 304136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 304136690 ≤ n) (h2 : n < 304316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
