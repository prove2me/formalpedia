-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1730
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:27:35.381638+00:00
-- url     : https://prove2.me/submissions/c424f742-6e6d-441f-884e-ad1c2bb25709

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 310971223 ≤ n < 311151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 310972473 1250 310971223 310971277
    0x309011202040f090b0f0f010504181b03050609100501140a02160608011815030204090f0807050105010e07030c0207050603060d020405010e150a0308070809121501090e12030a02 78
    0x40d0103043c124201041c601e1411040114800041404501c1241041c51f4800b207a0b0b001001c8070104d03122040300504040030000024000c24400300484a4980c80c250310b610140e03072552210384604000c0700c0c030030f88035202c07640e0004c05031703600f03009aa0200b100c0c0401c08699007108070184c5050003c40c8100c4240040c60705520300e400241354010008951040d00500c420542d00302c00340c401c2d0000070000c2100c512800114650301d4a14030019004a07039442c2800c0601c03020128004030a900f01468603074510807403070b00500911092091982c40f852241c080b640c031612034050000f02c10381c0c41d402480403500300000c025043d0f101405c482c1c0c4c40780c0c1002010740141c6403400307418002c0115803801003581c90300780d5030284800030740e4081a01c118403200302400060f0010050b1010990040030040d150701400b004684a00743c1c070f0300605824824404568178280d440001c0a05a82d6010028456503910800f51a82e5081c3c00b10421810b078010700025079504019400381a120003200800303950a0044074407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 310973723 1250 310972473 310972499
    0x210031406030a05120903031e0301090501051e040e101508060705130b1c06080102031b091503060301020f1b010e030a1b020d0605071d0f03030901120204 68
    0x4050109440e9050301090a502a0110707510401c00d6003e0010f80410340d6426031150602901069204004102000c07651070400c191469074840300c40d04465400c6103451031a07603800901c1000c4c003080c02d2031b00220342420041001c410144120007170300c240000000410001d08040b000440303561140d280303404210403003030003640308100d54015070003800d42c2010042410071a0040c803401c1807240401040c80c04c44109216001200c0d4101242500d1301020300d0945c01058030701881c82c220904201e0b01041400c0c06500a41c05940710b000c100150180c0c03c1c90686160044954059110380c2c070070130410091981000640d0b01440c000c000601c1c02401c040341d00c1c4a90000d203185181100c42c041c00b9920801b09208180040f001c80c0021405e1100614004281607402c00c8600c402c410080200400c540369201d602c4182580140284030718546010000c01d108000300590780007018126012020b410a010381d40103060b009405141303090303003d100654881054001c1074200c1607080000040c10034000c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 310974973 1250 310973723 310973749
    0xf0904140c0703140a05030c030703090c03210c02090703020a111c090b0f030105012f01051e0f0105010e0307031b0905010b030f0105010f03091b030606270f0902 71
    0x910396207802d2a07080080c2031840304008210039034020442072100c941c0150a8903806141115100c0e034a070f5850a049020b021a41001890047c0c05040442000f0307882c016840941d8600c428540d01010103001201c00982854029402140740070200703c28911a1b00104000101800c12140002480100c1031070010300c900c010001c804280903032100f840c0e0042c1200010004011450300300700c1c041080c02914401841003c0c140b08248026034100c802e41002030340cc01d602002900c0c1c2210821200c10f000e4001120001010032009503280700a241c2800c5150050082d0424605180e080c000159815904001c1441c1d16200320400000040c0c15010501c103079040350004045070624020116095500603082001552028030410001c41c02c2c45100c2c50440e4001d180c040d2404100c005e0560007811b5030000600001c11020600b07580e0120304020a04803407180380100312490b030b00c4400f80211400382c0070702c226040084c0301030300450740f56420800180403000760000e8000129030006144041c514 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 310976223 1250 310974973 310974991
    0xc020c120a02010201050601050a020d0c021c030e0f12030702090c0403140c09060108071704080408070f0f09051e0411040e100509060c091e030a080706061a0f090414 73
    0x80740d040865a080c0107054022500303007001410b04d61aa5006515000c2000d03007041001040c4032548199074920034100e541c507408003a50b12a912480c10018524211400401c0c001c0310300007100341881c24840f80c5c41d4008101800998142800f80c1e0030400b0591000d00400e00301c000c140400b00204601c52a24a00801c0308001491103080c450240010b81100800007414011910101b116442e0041b03c1c4011645d046a222000d540d00c0e4944182280125041400c1620074008041038280140050304241d404445a4488192b0340701ea5000c140c50f01120040c50700281e110303c3c000041407036500d00b90050311510700d01d90400503071000b103011a00610a40801d0f030344442d4442e10303e80c40c50300c200e5421960b01c4024142da03140c803001c8400e191160f00c0c4420b000c1c0d66810b034800005018003001711004003000f000d41d41840c0190a01c101d25030842241686d103603103003440000c0c4003803182a2098101c00046203003414040e44650088540c0c0040c0c01c69a0400e03154820031080a01600303070184030342108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 310977473 1250 310976223 310976233
    0x100b04080a03170c07120215070f0215220302011407092105070521060403080403080903040e04080c0c1503090111040308090f011e0f030b041a01030c020c12 69
    0x2d050040c014000301102210118459044c00360038070402049403462500214416602e00707150f04120300c1c2c0412407418021680e1004103210140d54001d0810421080d15822280030010320340c05d5402c02001901d04561018806a40c451502e04001e440300030207010340000a6070601c02c8218a5203034004880e541d0019240721410700c894642e48400b01c050081d604259003c4046a03a560741d91039519010b005d20840b95411001c000f00400c10b540d4003022180e506030743c0301e41001e140161070000103450840110341903900061540700c00100f40d0b4100ca42c003078100407454940d40c450702c0d21a03001045001290003000042c141c1ba8503411a0b85c011140f41c59052a0f80340740240003542112401650b008072858100401c001240d00c0c0c1d41940d9405c4400c0321140b950f5402c1c2001660b00c40800d2444194030a40d0350303444010950000795814885070692000c0c08a0b1600e44204000c5504039070250924403054190801954402d60111000324410f00440d180d030004a0001440800000005a507580c09 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 310978723 1250 310977473 310977493
    0x105090c091602120d02090d05060a0e030a0813080c0102031003200102060604050a02091e0a060809100f0b1201090c060203030708010e0703060b030408030603160f060503100b0408 79
    0x1200c814580e102c0b07001210301185581655000391501949403003050f41e164007081e00c00d0503461035070485014100040034400c00301041d00c0d1150301c40030203c0d010b00f0050700d010311804401c03c020044803482101c2c0c0d581d04c4106d90340c00e0640c2e229220306440c207603102603050040291a9000b480114007400841c048003010b41c0c07941c0f800403c1031540c000a03400f55041c0b260440c25a0b42c000035000d0708124211070101c1d4031b68940d0424002405007002190f0710000b8581200c0d041c00300f9911111000f44e00f0b6440c0e85015403540c406a501c00015600548903600c10715401c001c80009610014000c1003010001c20039040e2500000d803981d810030f50a0003e42d40d07942ca61070800c031185140000801803400a94251706c1c007598058150a414407071400c1d540841000100b52a20aa00c0100a840d0501a0f01c1c0c4905203420103105603007003120198000e100f500705580c1c5c0080c1651004089804202564032842d00342041107804d904060440d6491000c140d201140c401507110150000d451030304010220301c00c3c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 310979973 1250 310978723 310978729
    0x807060c1d0411121503011112060f090106050306030106030605180f070b0f0a090b070804030b09070503031801110703050a211713060e0d020d0e0307170f0105090c 72
    0x40280001c1e01c01c5151a02c40301d201e0302c0b50000d030340140007000701c0c0d40b40345e0392049081203079410102101581075203003801503540c020504001c2c14440224100e440516030700c11040c0314a480e5100c1c0c40982c49581e01c00104a4188100001c41e4411800703400840d0266580c0d90344025500141d40300200007404412020501104000e050001c0300c220008202451800090404500c035800e54101c5102000412003401809480305000802c100c5a075165600e10a0415460790340090000301ca043e0b9084010079011030700000c514055610040185280c00b0080c0b8a5541c00c5941021031411320480d10800c04419105009403c000e41c0183e0141250304858030304207240d140e071200312641d41058007410740c003150b501c03084403000850318030104240c0e61a50041c031411104041e000400d82401d2840c041d010001c0813500c5d01324003405800703c4a0300806a84142e984605040300716415074024001040101c015045071440b420fa00f20698003c100107a0002d820340d103044480c2c4580358052400842c0c181 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 310981223 1250 310979973 310980017
    0x9030807111501050904020a0b040f051201050603120c010b030f0c100f0203040303080c09060d06060914282d0e060d031218140106050d02100c0807060c 67
    0x9000405040150b0028480c0c0b03814107010b01545000d1050307000000d0443d03c0b9802e17418050000040260303201c55445401c1c5d40c2150850007031501402e1541d0001e80c1c820014010b0f5802400018050500da03900d8800ca010541c00c180e592101548d04d4001b00e00c0f450300d080c4401284080640003400c81c2c00301e6034090040072643c1002510805c5407000c02044829408410303141074a50624094019468240010718075015804200b54482e00024100300c10070100d0340203904541c1a51200c90204d80e9540109240c003030300c40b00241d0061250200d80309060364140800d03d508a1400131516030341d8884420240e11001c40d03081030b0b522103800c039080d04030070300c141c05020090082144008070b524100010595100324298014140b14105409900b41042504046d00084401c00701003c10040d900781441794010000c040200340d4a000404515800c040c1603800c0002d1f00034041070142880e01d4400c607580180c03104241e80c0c44209000382400500c080c020916001e0071992104035000b800540f00c03c9171 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 310982473 1250 310981223 310981247
    0x216060f1104120b043207060509011d0d061503141c110109080f0d2a051602130504030f080609010501030b0d020901270e0a200409030807 61
    0x81c1000784002c120a1140c1d000300c3e0b0b0525446610250030f42c0b66458902242c07018245c3c810300b0107119002014441d4455070031019030314004400c40b031070b40d5075402040d01c042c425a1710a500248076030008c060b0481c511925a070044002600b0200641010f48520b400c40c0c1a00d05d05140a8101a0702041444080e1082d852030200010260000315000225110380441040d14076090080c11000310400ca002036111800c002d41110065940714002c0340c0d424090b0344102000c0a00398039114201c204500418880901420fa101680c40803d900c03150949480d0490500002224203402e8640e00680b107000b80190f08984000001c5081c0c01d2514001d45903a110000381000c10035001c04000c1c1030303550501c200e411900c00703080001d442208c0f0b202080e4594001031000e9080780040000042c581a0014170100b400c0c1440706c2c400c11030151220b444140d4000314202c40250b4080400140817401c428115242202e804424504030406180498107651800c0c2e030a90106000f141080010707500966400c41d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 310983723 1250 310982473 310982501
    0x3040b030712050105210c0d03110d08010e0c0309031b0102120f1519050d0b010603050c070b0f0c190309032304030f03020a020d0c030c0902210a0216060f 68
    0x40f640c100004681d118107000049446c45200d010403003404042445030400d450350160030000b0700355081c00d000c2c01102500c0440c2c1c0c098441d04419000552207407401a040c0d0707221805003e11034560304030b01003460b08042c1c0200e4690104020b8017040282c04030b888040d0b5401140090f840c2c0010f0b2046002211000309091014140102081401c3d40c0c007a441c500307660401c680080400d541c0042003130200b100c82d0032150b000f07140b00714003c0c1480384045040b41220500e076401d2059641d0140307606842e00420700002d010700498000301701c01c080c4012101d0f50200c010014142068400034802103001e145086000210340e5402a4809059002a2090513503030b0402c2e00d00b14003030442c0700025a80c45581b01c080d084074055041e074020188280012030707490f44c000b00003103440d041c0350038064100c980c1403100b154000c01010000070500031600a480e0100315032a160485014455400301120000805882d00c0741c0d400c000c0c0b8044090b41c040c1c07850406000784000246401c0405045003101d4440c614441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 310984973 1250 310983723 310983731
    0x62c0a061106070306060c02220c03141b0a0503040f0210180f0602030a0507020a050a030b010810110306220c050c0705060f2209090b0f070804020a0b070f0503040b030712 75
    0xc086604401f55030081a41900c00d441620300070b5584c5452549010400c40c8141c0c00e2040c8500d003164075401000d404040b00344807980c02e454043c030848aa803c03600d0302e000c04907014001858050300904c05541e1003809410840000302ca1039000403050580c3d240c2001c003080051101c80e921614015030840a06005007aa18845007040320107550703401248880820010300043d40421920b501c0100b00051601070190404581c591501418005007406900164483c031685007640003024059048900303814110503256440f82c605002c0304a020324680502c00c980500084d03540d0034248128101040075039220b030748800448403083d040200f140d020ba03200304018015000c651003048201c03016010003600d0780c0c418038078601070f03000e0f8105294454420b407854a1035407070a00c207200740380301e1042682d941c07401e2595682c030030282c515040c01c1d10003030b4100485030710038000042e9801c01881500d0003445401c801e100301c0d940380c900e10350064106003c013a401000f070201040c4c0000315158402c003500b200740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 310986223 1250 310984973 310984979
    0x304061a15090d0812010801020a1404030b0f090c0d12090501020a15150305100507090b07050c0103050c0708041202010809070605030604021303151a0307062c0a061106070306 77
    0x30416002e98440a441041038114003001c200262080f034807071002c2c4050b4020706681da80217850003500054114800b1a14140d0f8010308051034400311419641d104686c106c01d52510101074a80c03c60042074540c05218081f48450950b81c0c00d440b141a49101d2180c01042501031580180346c42c0c1d00780e01c00c5055521008011000503120300100842e41c1144200003048400c0380d0026172108907580c00070303020703004e82002c00d490350381035402c0180304003529202c1d0528250f58803003200845c032071200040d080740c00008010856610940204e5040072002c03140606080c095280e8100035442030340300c007070141c04403a0000115600408400d501a244401a1408a2411001a00341e02c4000e0509104c1ea6000070742c000740d10208007401024541280c81621044c103018a214003c051103004c20501c031444c00210180c5160020f0340a043c1c1e20969519110207203c5181040c107800400c448540a0340740e41151800707a140c052030311004100c0c1d0381c1d90003440a80c0d075150358200316020740304100301414820300f8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 310987473 1250 310986223 310986259
    0x81603030215060316060305041a040f170f0c010f0b0628050d06030602030a15060210050402040209090c190512070e0a080601080109050c2b060b04020304061a 70
    0x4080a0125040242d1260361520002070801221041c05106958521404902158580d03c07030b5218038824669452002603026125021500448001b8646c10090106400103413141c81803030028055940d409092441c0c0c03800c07080c0d407504542003d0304030703a554110215040409015202c0d1a000c140c5226150500c0418094403003240e11031b401c800480e8113445400628401c0302103d90208031170004001e00303501d0b850060080c1d80184c440081140c28070100036a440d00b400f0205d000c65241da002442e070701e4030342e20002c0701a01c001001680c0c0180d0900480040b51108540c2d00d04c56450002000d6032004404044600002074401200400c501444805080c04151400e650080c000d41440008440e100c4002a0003e089402c00f41040c0a802d00014640e03805400104c2d4891280d0b0a654948492034140503000130400c9140020306594000082c1c03850111000c42890f03409950042030010222001c07900b680d03c1501c0884100c0d54030a1210b1074846055024030084100300c0f1700d5908400e0b60600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 310988723 1250 310987473 310987483
    0x31e06090b1f2705041103090609060601050307031d03070506090706050c0c010c0609060903020c03070605130920210903070b010b0d020702180703110c2d01150816030302 75
    0x4990307883c0c01401c2c5500c4804500103101c0c0020a80140180007408018044140c20382064070401807a00c101e102081c6042d41c0400e41e0b41c8200c6040c6e44031411940c80000450103400d4418209030303d140c045803010f103e10014002819803e000d40010411400d04030f41c03580c9402c8882d031016040110078021505a08000b040b01d411980d07092a00031050100d909181d0b00804062400401d614903020416080603000700389107103241801c4040d1002c01d40e54000541d0540300d0540401e689880c5150b0034890044580c2c0000b0544101c0c84c40d00c142d50118103c2c1000d02d03840304640e079000300760301840341c51904c06088101d2351100c1d481000e581445001e58510b4146131042c00380c0a4003400c04110200454250303810341e2501c84d001069103244001c00705100141c82d5041e035403a00020300b442404900e1851050460749000035010040807610a40a030001d940c480000c0102946000c61643d48565a024018024071711030101c19682c00310310700641e9519040352031003003490805500d00100042500421 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 310989973 1250 310988723 310988747
    0x1030309050d0809040504051f0e030306090907080303040c08010c0c0809090a0f0c03050901050f040b040b0a0906061e06031104050904080903011107050d0801030f0201031e06090b1f 80
    0x514407100001c079260109260003000400750f0046e1414081005004000901840d1040510052503480d8804000f8405035443d181c1c40704403070740c010000304265003084c99803282d000c1e4100041e42c281d1174079181d00600755801030b90b007030303031550f003818414401e440e028070981103044180d082110090300e50b13541d65400741c016605041c0c42810700000041c07130349800d07030404a1141d032018010402403196190280c0103000070341d03d0056961804002403400504002420300542c0c0140e107041c070664581e51195180c04c4010450410035844401c0c210016926001d004003030903a40314071008a29102500c00700d008ad80380d010204140c02c0043c00c54140c16220211400d840e400ea44490b8180e89900b0300404601c217620740660190310300006130b010700740a0400b4181040c440c4041e14000440900211000d04013800701408802e05031840100660203a40060b8000f106400056148c1051036418421200300b40d12143c0c0660702ca00840e121807400046010169481c540700690740f07459030500400d041e5843c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 310991223 1250 310989973 310989979
    0x601080c0d110102070803040b18060313080304030c020a030f0506100b0d0209010c05070b04030c1d0604090f02040c050306010f03050c0a051e03150a05010507050d050d0e1009030908060103030905 86
    0xa071902850f91007030024131301034000481280e9440340d48030800107050303100c00111039480305681500300b02da2618604603030203414000c190241084060f100e4840b20761029004405021840422000586420704541c0095014034521814094903041981c02c29500a02c0d00319180c0180d0000e00074880024140d41c01001075410040e00c441000004be0b4030740140b04070240581c410325500240c120710550040040d24441c0a1480955540d000305090603100c0100c181001d00d01302d80041d45504041e445091142c0c0606d5128856510a4002c201228070760701c0c117000010000000c000d15540c000c40d01d54000c000e0391404010920717280100c0310840c041c50304200108000014090300303113004000c601c903003040c2c079246882d524104100490f101010390240140201507201001a840d80200c058603001d41d080400790002c400c200700c084900d0743c4411084040c1c40c0ea100c100d413003802001c11102c1246a40f0a030001416025401d020706a080141d200180650200c8018400264041c00400c00c9920503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 310992473 1250 310991223 310991243
    0x406060b0306280306060306060620030403061e0e070305011d07051309120810300203010e0d050c0601050306071b030509060307030b040b030d05071407030b04140601080c0d 76
    0x8102d941c0f40e106480e40003400442c03d005020040c4007580c3e00c50400c5481d103850710181c40304402d540351400f00c054800d404140e0000d200c00c00c00b2400710340201004404100d9110800d8000e080c051084032550710103444035a211490510401030700b48210490300000484510000b0000c4d201e40740d0300c1d04540200d90103070100c540004203170319007500401e202c183d000000c5030f485142400f004000c200700b22070041d058502c40d50009014929460b0000440c426a48070400d400d51030800c048101500c080100d8144d17684911100d4910014403e002440403296039180c1e58100540700e1034030302141038000314441c2d0041c1090107031013078002d03115240003a180305c1d804032294550704040d6014000e41c6801c40c1c0004001081000044d815440306040138070440b010416690b2180030b0550315038501e6221408104104078101c0030410303a0124100303803820001110300075a2640d0320035152010540382100c502c00c1c0340180e03101482007448500d014044903002403885055910000d01102c05a040161400c254 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 310993723 1250 310992473 310992529
    0x40b13020c0f030a0f0e04050408220504050a0609050a0501050906011b0b0c12090105010e010b0903010902060403080c0d110c0f01170403080702250605161a0406060b0306 75
    0x414072284094000d01c000340c03504c0340c8010388050b101d80c2c0201d810800003150300f00001100c3c5414403503070307010316000501c5a007445064800001c1000041c240488010020000042c450369070340101441a64480404600c0b0707464610b010050b0381d00a018440360b142004014401a01c450340003943c00f0b04241380069840e40105100180e40d44949000340c0441e914104104141e25040024034425040b110705803816600c0c2000305088950a000e07800c04282a540108044031a000242800d010020000606141903500040e40c5034081d91040b03034658404900d030b18003190140302181c1381d00e0302420260000820b84000366118101c3c00358091161101101d10800e45e40710342d0144a60300401000001e044c10030341009402d4010031030300d020040c41440c2e09504508001808200d1031880040302c1030301d4604104050b41c1c580c000b040b200300b14800881200000c6128003002e881c80c080612040c208038101070920b5070503101d198000315418801001408580d032660001040303d95068942003040940c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 310994973 1250 310993723 310993747
    0x308070513090603120f020a022206090902030106120312020d0207120305040209010f031a0a0b0a1202010f0f050313021f02070905070c05212b0b040b1302 68
    0x3070030003410103590a04404200d100d0140d01090a42c5d0140b410628900c60202c3c0854084145c80d2042e00143c01c103404800c0182003901010207c5014040c1b4094191a000c5840e01100c00c207a0001700b2003a20742e02540c007541428807412016200105400015a620b502d001d08250000710700001241e80c0059540500310f10f80c0d05172200d880e40024894900a100700d0010003400055034242d01c52490701000181000181c20728104a07684011069449202003c0701c0e00304400050a102c001da031107030f40071060380c0d40d4426010050b140856425504a15900004141d00040c9515405200707004244e02806908130050b680e1100034441284144109440820f6500700e0385407482c0e0341407030039410000800382c002c2680001e640c00d4100401c40ca90701d10804642c59910024050840e402540744481d0901d104003201c850004d111048a00e403030004246c0c00d00120304440c01424404100300400c050407958042c1c2d00d03c13841d04840602240010b0000540c0142c038400d402084030f6030014801400034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 310996223 1250 310994973 310994977
    0x1061803140c010305180a08071a040b040b0f070504031e081b01180b18010603020d030507030f02120f13030606093611120a110a0504021603080705 65
    0x15401000c0d40305410001510507951200540803d01180c01c01c0000342030090041c8002c010b10040074014090b6071040c0e1500c4045a200d00c1054880a01408904006811000081c1d0080348125105450f03450f2908200d04030744e102405400c0b0700c540b440148100681c0c068191010b40780c0121035202641d808401014a0021451008003a4600424040b6a8603001d11150803450052802481009881195503451b4110500d0041401b030b8079001241c10015844103210307545000c3c0000041d40c944940000e20034060850048000410003d00c3d0f0702050350040c00d0292600f810300050400396107461010300a4050500843c01c0707000040348002c84038401056a50040d500311208002c0319865105100c090000c0d003082483c20206558140c0c481c0d0b410300c0e009084201d801036211085001580c5010302510360380e0010360301000042d03244000450602401d00740603c90259501004021030034021303071094940c0860b00c00c034414444e00c05040d01d20402e82506943c10305d041040c60340c03000310130744045c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 310997473 1250 310996223 310996229
    0x60301020d0509011a0103060b0a0e061b0c1c03020703031206050a08030c0d0903030c150e03030906010510111b0301060b070b2202130b060c030703080402120d08010618 74
    0x300b414101071190805041d0700010030f405065820030080707041c40d0015026100244602d80d001403040082190652180003000122400104154908200b420369412603641c50f403910304541d0401c1e0654045c51401100204802c110340f410281d180382c1c40c1c2c801039120001840b010f410700c07a2100e6102e52500f441c0d0b0028001d410b00402500c203085e103c6248035600d8101140120107031082c0c0140d110240e001354161402c40307030305a50300068070328a9034601c0c18042036682603901c07864a07006400c20503007080c40030f113200e104400000c0c192980b51404226000e0510305140061049100c844180c030040412030f55540c10300600b030740540d01d080b000401e0040c07031543d121600c00380d4040303000410032480c108614000c51940c0e6544050b000c0b08040140d0018182000a6010b408504940c00b07190301500100c411100061405017848155242c082c1558810311080300028130f008204011450424980b42e1020800001898000010b0801400f403400c10701a100074850b2000b041100c59920005100c00303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 310998723 1250 310997473 310997497
    0x70e01092d09020906160206070210170105090c090103020c15010b04150f0912050a17070302011107020f0909160303030204290d020f0408060c1c0603020906060306030102 75
    0x1408040341c80703501800d4800181c0c105070504610000682c60014020f40c0c4044600908180c40c1001540d241284c2c841614404c9030460020301c00c1b407015030f0780c46006d020242c1e0301c0c0d00c038002c030359501c9600911030600c1600310074407030b04c1c5410605c0300e001c10303a500f40d6180b45800e00380141c2e100b0000800510b0800c40c0004145d608411000100d8220b94510140c000c450b030b082d0036013200c41045a401d41d0040c415407a040001007014504015800c1c101d40b9003031083d4001c4003078070800742a50700c64200d00244140601103420000844d14101b560911070100300203030b403440540c28070701c2d207a000400c6401000201c510481c491400310344c0c1800c1c05d2118510385615050f00782e964983d00c1c034019000c0e401c10b22400c0d00c030002916180443c0c3c0f0302c2005503038180c8161000580341080010303850000350008214100c48040070b10000c01c0000040010502986242c2091034940b480183c0040003005902d070401400b90920030100010385400c0e4403036400c218102c900d15280e035242c001007402801038095902d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 310999973 1250 310998723 310998749
    0x1f0b2a070b07020310060509060d080910110c010e09040204020927040b01060c030f03020a0507060f2c030406030b1201090b15151603090b0d0f15050306070e0109 71
    0x2000103401d0014000503200390181c40740224400426002c840c01442080e40090f03498001a0003880c2000f15101c005108100c4117007091101c10124400420a0407483c1c00701e0520a0300c43d494540c00c110881c4070000034a09034074190700d00e20200f481c0800c046c00080c003680d00450042c000341d13035400e044800d48148124889907418440000c144009013680c080e1110343c090000401c805210703014070703d41d098058481d2144c200c88210210001d5000c0321030002000340c1400400c0c005080e502589102102c0e0800200b049210100e102c0c003018064240c840b482c080d112001e42511303034048160340c1140c2590800044641c204e0300410341e4003a040326200ca1715482c000301907007007004101c0114060240b86c0300c405880c0c040c00092011340365903820302000c501030510040381c0450400c401c0c8044a0311030701c2c04050305641c0d40c09440c000e4000f888180041529141d1180518140d4441d0b140301c014210003080ca100c1c5001c000c48e89982d40035081204101d411608540542d01456040005020b50440d602c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 311001223 1250 310999973 310999979
    0x204090821180d0c1e0f0819050a080f06031207050106030b0108070f09020d021201030b040b16020a0b04080708070c290405040507200d020115062708060a02031f0b2a07 74
    0x1502c1f076400b9401814207104c0081350111804d1003101600c4410240392507120141e01e9040740c062164400400456162040103000c004882c4204e002e4800741e4030900020808600350716040802e01e00580080320701b903001c0f0008201d08499035850a08484190a005a444040303c500340080d100f007130742c50300f803a401e2400000204000d0003007451080780641020400c645420301040da5807170f005880c98006034404003c20000c60982c50005811510403c02c03107141200582c0c407010240c1000c1d500b6038600124074030400185140c2c220300f02c44010403a00640d200e16080481e2074142c012030142500840c0da8500040c60b0b9070248484d114002114400c0440c01880f640c145592040510000750040d401c040030301080e000345141c0e8405640150315000011072070610f40210200a58210121604900070002680a410700c040c5009401056000da030380c0c6008055441c2020304c3c69514240c081100700d00300a42c2040701c00b03440b40b00000407040e6064040d04000d016800d50803003401003035809580400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 311002473 1250 311001223 311001233
    0x209030d0e0102061f090e031c0c08180a06020f280207050a050607020103050718080601030b060303030f0712020708040e01030219120204090821180d0c1e0f 69
    0xd075008030264201c40031551104110040e80e0481d41d8441e036540a0501305001d0900c19400015180200d030080b01d0038200c544003100b5003940480d4102d0103a0341d4886803050941e0380082500d41c844e5418030380d48880203401c007a10b40e8038840010007a00e03641e40491600040340c2c000e0101c41004817003111200b4103250342c2c42c6452540000c08074503005442506400161403c020302c640c030464000030491410190b00350015005804000e00c030004004a00d0008a2a03c451107040300c00b600d810f600411781c1c2c1d0704518041c1c2d909100038100f544282c0c018000c1280301440c0c1495103610448900c5c01818428a60745028040d018240006286510100d4081400188101720a040f81c4c02110341181214900c030040240d420107008042d0028541e41c081c50250900740c000081c480d2103094181d141001200b00345060130190b84008050324020320034407030b449030824003200161045102810581400380c00183c01c104c01454014048600c4da004802d400000201d406407135174004070380c0c81800941c1d02e80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 311003723 1250 311002473 311002487
    0xc0305150702160315020703031e05060a05121e0f070311030610180c14030c0a0e19060e060f0a08071214040f0204060323190b190209030d 61
    0x72400600c289950b080340303409040c2a01e01102d40010480343c6030524051440c000e580440000e0b000e060700d508800012030b150503065140064000c0f400219804c040041200c03030401036101900c1080b14101c211049540800e03000100040c8400b83c2c40e004031210681070a0220115416030300c2d00940c0d10002c10700c0000f680d500040902141915066922440c03a1813101c01b40780601d42808181911200c01200941e0200c05200060f051070040d003000301c540c0b812598000c41750341d418080c0105489114580204007114200b6049480d074070354800e856090001a9601c0c0b083c0010414240c040344c4054880c6c1003100d20241004030644d0765100c08050223080300c1c600f5216400003a59072001ea1080a5042c8202e1240314902c0405c1100c94590346c0320340c051880c241c20140e034065038030b4400000040c41a075003001c0d00449290802c800c4842c03d01014203051101e84030442d0007400e088404000f6101600c55940300c0e003264460b501c080707022110840203005842c0780c990148100b01d4030058094000407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 311004973 1250 311003723 311003731
    0xe010f0207050c10050a051803100b03010b120303070516080a0314071403060103020307050d06030308070905030c0a03030f0207080a11040c110606060c011112160203030903030c070c030515 83
    0x30441c1c46030403c06080c4500c2d400010100c1000500a011111001b44103030020040380c0da900340607601220f80340740000e0405207402210f4040707940d10b9554501c039007400e0103518405101240c600d1401d81005400c643c0324403004080700100b203800a1b05c1c480001915444446c40c81c0c21040040d02ca2100c404060f0040c004081602c2e0040c0c20728001030394152049110101160403140c1c12400c41d15034000650103500050300801c1803000030300041d40a1fa20301d102d002c0085010360f0700c5a0b054140100060111a09501b00e98020340259104002a495500c455400c590381440d2025a0703850490b422810722880f40c1001a460041030802424003070707420650070941800b15810000d60341c00b054251905a5001d6a0861503003010000070000d1419001401e1241e84050020030a0004840003e14a030721800c4500198105102031280c0d01c00e9404010810310000d000841c59820a00a056075901000b04a07074100c681c0080c101c81001006800c0380001c5d60306c038040b1244a0700b210103c1030741c0c1200b01c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 311006223 1250 311004973 311004983
    0x90b0a120b060a05031f09080903030319050106020102090d1214040801090204050a020c190c1d01030c0608010302030a08130b030a0e0105090c21250905010902040b1602040e010f0207 80
    0x180850180b40101d1021520300740d01c68818820880216211b010b0800a80305480203c4107114080050718103000039841102003907101c95180300404501d004441068000da0116072040c04924096203907490404103040e045002290280c600c0f04007203412008292408944410100d00016894015040222500e1080781c0500c019074440a07404101c0c0556802140c090303204242080d0101d11110b42c4030542405440f00c10200d0381c40b01840c400901104408112880141f0010018001c10305042d0024204c585840d11155256400096480541c100c2c003070a0340794002401e41007144042042002807041c5034080d5101d18151200d81d00404000101140301c1d401d0030002105003c001c2240c8802110042000c00603006860340038401080890b9017845a1296040244044ca840c80c5204095081e80340341110710f50410303140b48140d41060b482540c03402e00610003841000d0c21201039603480d414050100800701a1400040e002d0962502105055441d113000750021603401d030024403c142c001c13 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 311007473 1250 311006223 311006239
    0xb0a03050a0203040b13050f030301080a11060f040515090310051801090b16050c0a0f02030d02070602030a0f0201090c031506051816020a29070203090109090b0a120b06 74
    0x1101d40d82082c2e1008032801010308241d02c00080158034988080c2135018045d804030748512450b106000e1071340e8401e0b000104154481c2c2d05503c00c009982d00924041c84050303c40c20308101407a45200220b02890090f148620031710840c0410709140c89085e101074200090032a0b51628110307030380800501066a0006800f400c0408554160905000b55010a54445589c4101c0da50388103140300760380c0c80ca8007500304001003008034081c07848040245c628903034040ca0b8141040043c0c2c0c8105450451840280070964012950410141e43c02005503050901d4500b010004201e040000724014184082c0082c0709031040da101005021910100450030742815004001e150b45880c100003600300c00b21001d000703044030b51000803104941d101513803103289886d00444d02d40f100540d031038186c00c00204490080b020400701c00d11058003494042a0740205050024602d84004030300002d018540e0303801494255900c9401d02400e58070b4034080da00c018400300c03244441c04d400d60300e040c171040394007035808501c50450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 311008723 1250 311007473 311007481
    0xf12031207031e0902010e150f0409060e07020d1b020607050f010515180402040b04110703020f1006060c020405070504080f03040e1501090e06010219051614010f0e04060506040b0a0305 81
    0x110b106480c08542c051f1203a61402c078400c01041751040d485580c2000b1010140f106c0407180c042c00004e4006090b4120700441c2c0213003071034101c40c0c202c07400800140465000b104041c0d2426044816011a15624101c0300c0301c0400c0713800800e915204812000b0050300c61f450441041d6141035000754028000c203001424a03200901c00c0081026003220644c581882e0500070400501e0254014001c03074a000d0004180c0905020f0406e8864004c8001030b005038005c0c129440c00e440e400e00441d0813000542400b0031086003021402080c608120800a009d03503a5500480c01c0d80d409201558011310452084800c030300c10302040251250824801d4041c100f01d084045900760010003c090b520a8045c3e40704540c4d1450109a2804040f001d48924158000c1c3d000c0140056818980c0c000081c3c0100d000f0b000710404c4441c1d240d501e04056026002d04496032603400841e07a07005030007081d4210f5500c2d02e1640580c034800000d000b0106c030f0b408141c0c001400100081c1040b2440060440505182c40410003661 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 311009973 1250 311008723 311008781
    0xa0903080a150509090f0a031701080303100b0c01091704050111120715020903030406090e0708190f061d0403090f0317180d0c0906080a020f1203120703 67
    0x1a00c0011000520390b42441401541480c00d5050352011071082190309011811400703d08084448a0540002d655080d07080e40c1d8401ca82802801405414004d6141d80f0f0080200c840c900c086000765074282200041d01400e1140940200c40301c0e6421051007601c078564400c0d110241d5000b481018045041c00311810740b200d80c045580e1010075040061280350810b503549020513031a042440c4c1c8030556082c040c04c12251000c01c090310140c034051b1558030071503041c2008902e80700c40c010090b0040004140c20041800b409003400205558030070741c040b0703840d08556495001350265030003860322405864409055402602c098600035400303a02c0c0c91004070740300c40304040004028007000c0c4c520034071082a00003080101000340450882403026540382e0785601c00240c01d48500c890300780c0d02c81001190500400b0f00c0c92080c1402081d03180700030440d2180d5540400c4003a401c1c610150f00c0782188012041c2c0101e411301c1101c4120740e4a40002000d072400413001f40061010460010380c000c059090000192 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 311011223 1250 311009973 311009981
    0x50c03010503120c120a02030d0c020102091c1221020c010c0f020f07030209100b0c07080705010918020d0603240b01051215030c061206090604060e04110301090206030a0903080a 78
    0x10301e8102405c8880f004045220240e4401c40c0b001085110411a1340c0100e8400d1190f8107014640391700150743d03002d05d001001441d40c5c4809a01e07244514072038091000072407900481010500600341078018600401182c0200d4072404494604640002200000154198461040c00703240d40c886000e40061004101c4e69a03d40000c1e44005a114800501c0580781640d1150340c0403800304440c051203a02e41c2400c17013603a0030400442589900c102424400043e0600c5010090302003880c11106040c03400d20072800c507010119450b1174044d4001034441180003540c20100140d0707001164540e00c043d1000c00c50110301c002c180b072040f5591505561003070700d40c855011034840303807030700314540196031141103240c81042400801180e140c07040c1b989010301c1c1c5d100c80015091135000c21088540c2c40c64441d05009180000802c1d1521440c42c00505201c4002c460922a400c640c102c0c042c1d0328081c1030400800d005000343c4202030740c8440c01004205c103104c2280c120031004c40c420350310341307030036443e0700c2e4214044d9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 311012473 1250 311011223 311011237
    0x30b130f08090607020d030c1a16030207050f010c0c11010305040f082d0703180302030a0b040602070c0902031501020c0916090b03041407120b010303140c01050c0301050312 76
    0x4031115000c14004103500c0070242c0030520005002500d014055030001da42003e00880c2100403da05049007014440c5401403032602c2c03c501600c2040c146400e42c106040002160744090600d607000c96171509015041094002e50090302c4002c000030304c0001c0340500101d0081c0d90490302c4400200181084d94480d020b2140540e5002c2d040c1c4056101c16036841903660854013199896036009480d5003c00070320040031803020002c16030a990f840c402420001e04d0b02c19640105400303035101070020001a03e0010300100f08039041900070581d03844514011001e07104615014150840240c00441c1003004d650003580501c455a0b402c09140801d0001a40c0301c0c0c9a52040c2580120710400044c0d901807041603807100c01c1910b162400d900343c1c85441e0400c0903003041c0d0381610342080290b100c065418042080c44040c000402d007900c9192460f0792111032041c414040102049031054181150f1070352003056070316042150300203101510b407042c0300c500560401d10035a03110740305501c900341c0400c001c0011a02a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 311013723 1250 311012473 311012483
    0x919020c12070c060e010c03050f09090a0c09050415030204050709180c0e03150609090102070b0406020c0106080f030a0513050d052a03030f0a020a0507030c03030e0105030106021506010905040c0306030b13 90
    0x40881503142070f949c0d03401084140710f01101c01c1080c0e8010f41d40784102c46114102032400003a00256141d40101080b030f040d0002030165207090000d440c4214a1844101100d0f4100c40220300c1b9034900101721030255156100902c65052070407440d14442c0c00d41c11041d00e40c40d2a035180e0f250304400804050b40d80300185241c82035940c08501180080c00c14902e8103502c0b410201c00035291203039603642c3c2282400215020356045602291a2052000a010b004010030f020001000d051020740072a584078400d0310394000a000001489800d0454040f81e4240280801094a031050b07060b420616240c0c0341210f4040a01e581001c681c607111014a05200c0b0045800303170085090040741c04074401d10341e0003503407218203500c2003203100790000310108020000307144200e107850010b902e1841c010f002620101c9000303040c40300c00c1c0014486190b002440c00c0703400c1c0d482d0700c40003520748a5038016514038609800c2150014188140440c01c15003580001044070301c0380181e2603050359805500c1c03030912401000180 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 311014973 1250 311013723 311013737
    0xa0e16030c1d0c07020d0204110a0e030d030605090a0f0605090405104209051e090d0e09151e010905060901050406180b041706150919020c12070c060e01 67
    0x507003410320b50306e0100b070b00c0940b00040646805408166079001030300c0400000f0300042c00301d1424201030140680410392405d05000107400d01002400070100203103c48299940e440d400c20f01c0d442c0641100f4020640034140e05410f0402e810302d00e4076514044400e41d401410b102e40e00920388110380c2c07442ea00700400d02440b1810300700c0702885103e6440018100d85403134501000440c5031802c13071040754015003445501d030850380b0b0b0000d411000490001d0081c2480d0f0403078842d240e00c00d40c0000e102411004100c51401c0d0607503c041584401c62141c6a0399078120008003d5030105c54150039025a08070401d0b01c1d42d5150341c0c0d59000b0401a0321600000302c3c0094021301c010031209000700032020140d010803504056464540c0714903030060f0050750168a0882d02131700d004c1004081070140e103400c82249001082044490008541740d0000601500c02054070003031480c0ca42407003541601c0c2014001010f541c13905416400480140e00305020685207560f5010b40010070718000c0c15a94414036060715458 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 311016223 1250 311014973 311014987
    0x9070302040207030507050d0f0905011805030102180913020a0902070302030c060403080106030b0306010b0d0e1c09060f171501020c0405013302070e040c0905070207090f140a0e16030c1d0c 83
    0x581c8007000c07110dd104810080c40020849640c2800a05100100e49403024aa40c68030020040d001c0000b800c0310340050740c50311703924001d0784500007800103840201c00c01599581c00d92400b03d00e54807030000425102c0c01440180000c05a008011031304a450641c0c0034828035440700704150b01c03040280f08545003002c01b00814400da4082d5042221140242000d44007040103910440d00384601417802a4000765034501c0500540d508055400000d11746442e14200382650482c114940c141c010b07000e00c0540e110182d05190607842084000161200908180060350791400000313001151020310440c00c100c1d22000d244070400ea02100f0100700700c07503130051184515002c440b020020029201b92510001c9a20114102186001d114040c0c0015802041d41c10728050100303003100c0c10001c0d518622402c040c0240c03250144915465049444004002071800521060302d15104400c1040c01060754805000020b100301c425011048501c40003041d580040314000217102c41c003007143c421809082c03e01803c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 311017473 1250 311016223 311016227
    0x2030f01290111060903030712090201050a0e0a0b0c0a0c0501030e0a030c020319030e03010608010b0f0906130e1e07050a2c130309050d030e0909070302040207030507050d0f090501 79
    0x1c40c0914206040c070f080c103180600042400d1030401c07100812240d01c0001840001984004040914400040300304945507241e40005d03c6881000303148820004140c43c2c405444d516602d09000074462114030715503818200030741640b41c2107849800d40d04036a034580001002d50113030180084008012000c0d10b02c00a02e590240d0f80d0f0403017400260307058071411010502951400120f0a4454003d07100c441056000c03104050941c0c2041e000301d000b0740d05007502400941c854102141050342c04695414181d5111400300d840803901c0200107a075242448400100000003003890107a9800c03d00d1010640714201c40b00747d0380d4600920926800c401880f2042200c0040140d065a41c5883d0042800f0300045a0800101c00d280690341c041c0000341c02280c060400d5040101d184c014031042c0c9844840000c43d407000f07880500709030010b9010f10580400a11203500c14000f003809194018011034450401c0c0c14010425001103c040762140305003c202104240109a00f0f84078000307507940c1c100190b00300f03401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 311018723 1250 311017473 311017541
    0xc04030206030c0a170f180f030a030b04150b130b030114010c03021006080c0316030b0601111006060507020109080303100302041113080d03114303080402030f01 71
    0x5104200407801404d660441d8403035035406d0068140d80712124040c00c0082030f403000b801d545901d410f11507104a004034030150002c410f807442e00e00142400541e205440c00030030041c16010f11495115040b0503000f251080703000c1e015082061045107001c2203151a0762020010f4802802030103d5141c0803e0840b0302580308043d807035041ca110f44180d805841c070b481011400e441f150340000c500354000c1000c100c5c150500b08900c0314030304040400040894550b4860144034600a8039850401c0b85941a000d1003d00420107140c81c150014001c00c4507690f1900c0041a50300404c0f002c9000403003600740020a60b6000081ea8000c42c0c007101010801459a0f00b000000c200f160201182d480003403200c08600340504030401b00030030315440600079902080c0001030072100d0704080340002100c00d02402d51000003827030b201c94802c054480b06420310b04aa00a0703007404540c0c48141c1c41c20348619130300c8004240d07120031035500861080e021680c4c0c0311090300c0301c40e007a20725125400101c01040c1021803003a44010340e03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 311019973 1250 311018723 311018737
    0x507120302040902070b060405060d031b08040f03060507140703020d030c11031305090a050f132f040f020a020d0c02120a08190c08091e060406020709050c04030206030c 74
    0x80c010702e042c0d40d44808800742c1c0c00c0000c042e11640406000c2000c1410a8069950310100495550a0002c0c595402030804000c00002130048036421000b681003209178401c890103070811011600442d540c034603000026080450304600054090045004192956425500d44903410780180c084600d40c04012001002070280a2080003030520a8248002c0c080c00200003e04030051048034003820081400000500900b51454842c42c0608001c09440000011600b28001d10852404401141854500305801c07511a120b440c11982d0004040f4003179511021020209540602420601c2c0a610b4128001c1401510250308245441c5154521440d01807491a1000b06001d1070821844011858018041811105890005a00000c6101c841d05100d281c0e40c80c1d18101410040c9980c030b030340d0540100d040c06400303980720307581c030b4802e448101c074009840c040c0c0500f800c0d482c1c40d81c4c1c00b4001d40c0c8060612450002501d0300000c00d02d96580e04044030103513900982164a19210700c1400b21207036210030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 311021223 1250 311019973 311019977
    0x501021c03150302150d050f0405060601110321040219150e01030e010f0518030304020607030f030902090c190504050901120f05010203070504030c05370305061009050c0a050712 78
    0x80408401617440c040404141d010740e41d111504c2d0707041000710004036003025000c8055031468008020000d0b40c000307941da61050085ca0110800c0304d50481103480c4d0300542002c03119503418103030185146400740040900c114022035402440d028000e10900484000b809402405442c0340303c1000c1c05401205088103114040c5000140414500042801c5400c0480000c0b000b5440381c003031040041400c0090104c125281d000765140d42016400207a0038480d01c00c000701170001c04e40380150164041da004010050300a08400e84610306480000f245600c0318900818072114074210424581c07140301038600340c2e240030300030040b141d00f041c214244822000380d04540000707000e148980041c100703001440c0101400c1d200c560f100d90461400004c10042a0410303800303410648407a803800900d006c0d0750100b40741d04409e4080480c150b48498884600c0541014245204071800d00414018079101380c0c08564104004015175115140c58440520035071003003000080c070134031421300814604440d9261055040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 311022473 1250 311021223 311021261
    0x10e0603030418152301140d0212090d0908070311060c2b0f020c0f131a090f07090611011401060507030201200412140f03040801060501021c03 63
    0x90404040d062000c014050341c80383d1030f00c50403500190f00c00c07610750140c41080303c00e003219003411010302c5004005e0454107041000c44c0c000203040300d1420040b0780741116060019580d030100460a0202c02c0c7c010b60350011980b08003000801c4107071003031b6103003420340c4c03c1e0710050101030340707035031901d0100c000e0400c5900d82c4048104072603103403c24208891a41c904404602e07900c85034500814915007050300710b248051001018084084644c0890a50001e00f800c0340d03288001c504040c04900303416202241803960314a0824500c04120807010144980d00e01120b580f5031a5a0701c60072115615030a503400804030b00143c00c28003132240241d13a2550054108000011420714100f08104040000c0e400203021880028030300c01815820300404040b003e0401488602841d000e05100e002d104038450b0046a1940182c4181000b81a40c0e5000c06415a1b4040340c40b0410b2200e10107803281c0c03142c0f081c5005580303030803030008595001145001c800b2418058040c01003503c0041940907041410740150f5180032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 311023723 1250 311022473 311022479
    0x6050411060c070f0905190c090e0c040e09010612080307110a080301051e0a091a100e090108011107020108070c1202030301090e120a03020a170f04110103020a08010e06030304 77
    0x2070306014015080b2100010031003a032600c40101840b1601d5001012450700301001c201d01d0390b100c41200304170601c0d1044001030030600b100040b2288000307a00314960358030001c001d00200071038003000341c07003900c807404401030054a48007031440c00c070b81c100d101e00380900500400004c0449e01d4078010399800206ca0614060702c0b80c04010041c10084810022611400c01000500c01c80c10020b03030b10349030300103140301803100b0b8951000060822281343c03040d10f1003107485800490f0310920700c2442013000c800280202140341c0d9a21006002801c600883c140503000c81800000c0d1103030b05000300046807030410502440d0008540045409102c014201c400b03001c4050001c000091100004e541d111034030b640550703120f5040c25002000d462003901c001c503180c2e1006ea80d4101910144044a42d8075085060050340d40d92b104105417910070b030004030f03200454280420442402c0c600428940315178810108039180c803c100d00158103e00480000da0f00007030414006100e00744074030680d960000c0d002411603080c256 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 311024973 1250 311023723 311023729
    0x70f060908030103110904020f061605010e0d020c032a0d0503161e0305030604090501060b0a0903050106050a0e18190807020312030103080a210603050c011205011206050411 76
    0x110a60200e41c0228004010414442c440241c034424207400c6a40844a0038150002281c4d280200c0c0b849101e5100065614856071222401c0440154840001d109444010744016210034a03c5101400350040241481ca94900072400140380890709203c041c403050112680b01b9420303800102180c0080e5104800004604200040c140b101d04450482c0590320780ba2900000b0209006040400c0c88204100440040d40013015654040b10031340300040c0c1c086c01030a0890151940d81d000301039140000a4400d102a032140c030f900705680c05a002032064aa4810a00540c9446e501c10714954ac8a1100814a802041c480c000200740b480c03403c94140c0e0301c03403070190840300c040712504507180c890002d040011800e0504c0840d041410b83d45009080d50b1440d224084544128a45002000222500d80c010003c02100c008000c0e0464402007014580760710b096565020810156800f0450740c05000c00d5541450160768140c401300946c86540060079a1070102070a000f40045955180321034601496271 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 311026223 1250 311024973 311024981
    0x3080a0e07121211010515040f0b0909030c061005130c02010e1002130801050601021510120606140a230102100f050601080703230621010c1101140c070f06 68
    0x180503c20b00e94a030950110b010f40219112100b94005034100000c000c1c06440654401742d407658161804959410808110001001c1000100c1d90000c81c400900103481c80000140c500c1c642c4040031184ae42c8c07518038072041050407503c1000d40c00b8500050000701040d55400003000308400b80000305660040900c2c241c180507003140d1260045501145c01105106040c180c8001464004001c124500304500000d4403428403003c0d5484061406000c280002c000c440307124020700901214241011103850400c0c05800d85114410781e40d5007070040c04200f460401041e07800c80d084200b02501c5070b4142c01106000c001002c0c0c466041d801515101c000700543e6004400c1c003a404000f0000b19490010005050800042c00900801d1301d440c0d0341004002170b0f14000e0342003401e10745181e240740d520700001411702c60b07182807440c00d0240302d00041c00352050150000c0e540ea401a442b160940348170706105908948441d51a5840c604046010800f640d81000080c005280540b60895407092962a2201a1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 311027473 1250 311026223 311026259
    0x31e02130614030106050a08100b06070803090607120b0a0501031508030d02040e09061b090a050613030c1502061902160b04030201050c0403120e03190b190903080a0e07 74
    0x103600b900c0741d503140514003841844040e002c11146012068101450a070b9620800c01c000807225944064880450b40c0f02d20031f8941442d48010240da407442d240f640346840b10401d8a00401080480e522401e420900c2c3c0a0308078121405061803c165152000440140002c0d0b064001040c01c0c001012070b10100c140700600038424981d00240e03866140826000ca42d000c010300124040e0040020700541c500e40751b12419002480b82d080c180c403038080d500083c0c10312525501250b441140010400904200741d0400803c072401410b20f0a1680e60b40c41d900c01c50030740c2d220701c4640107801031030001e10343d4a55661580c40110350340390011b00b08103101c0680000c00603506000d5581c01d59400402c420154240180e070307803081042c0580d07401c240c959a82c00704000c4600049000703024488507007200c0758904100c4501510048041c225082416040c10107403800151003501d5130300750300d4074489182e1482d03000e04500071794035690748152075448090410062280b403694a4a070302943c000015203003204000c070226 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 311028723 1250 311027473 311027489
    0x8100f060c050d0504060206010b07080d02070b0a0606091a0705070816080d0e0105090906010212130501080105040908030423030307050408060612100b04090204091101021006031e021306 82
    0x45180500b042803030090095214410003008100a200040c2d000c942c0c14116407518484a84810303052030864040c1c0100240d18402038800b1844c4418042d04c41480c0707002d04860b05c0200316240e1203000446040c0058000c0c03d000d4030a41e2980000794692400400030139005800703680c45252035600c460305011810847e56aa00302e061400d000c155410f0081130400c04240c108540702d00e02000001e0300c54011000d400f44580090800110141d00a0202c404044d005a0886a0b18200e070b100101c0d010b9901d000b11070000740c601c400403c450406201e400d00d081d40056007e821760360f441e0740e10700e441301d620300c40e0102d601240f0310f10158a0404202840c000c2800303484450300c5508100403546400002800c151044020804c84100044042100100003d0149000c6120848000414040c0480800013074115140c960340340103109103011288400d140c2642590804030b80c0ca41070303005a5910740400382001c0d0322086828000020400d5041e50544050a00417550f10002800030881d601e80d403144c89 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 311029973 1250 311028723 311028737
    0x70e06071e030e03070e090604061109130c11010603020d0615030f0c14030309130518100c0e01080405030906160204020304050114010504060806010e0a0b190e0f011508100f06 77
    0x3c204d103000c0c081e001c06040c48072056049894041c2115645940150019044582d510bc2d02403c449400e0210303101c25001912850718500419135417070051140310310160028113440c02088a54078180100c404a903001842261604d5190f12900c000b001500215420208201d10002c0020300359004000e4460243e40c0704100b81d80b411450700c00d580344500c2440d109400c100018034450780d4460387d41d00c01d8211880d000520380c1d03408422180b100784000600c0614410072000c0400c00c0d0158111007003900c215a294450003c3c3d075030054031244000d450090440d007003403200c18868103141020f0262403510a0740340300d0400480e000305040381d000355401d542594541e0001c0b4800c94040300c40b60700402041c0c4042043ca407410000546492040c051134120350f000c0804a05281a107802000003424010641d0b0942c80f400d041d030200c56640e600c01c054041000304c00044203907040c40b052030704880008a440c0201ca400307007400c8881c044000c202d03441b280d100107000b00d0302280780b404040c003800040c0c03101c80d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 311031223 1250 311029973 311029997
    0x6041e1a0705060105090c0304110102190807050705090702100f0b1e01020f0303060a03030c080d02030c1b01091a1f060c061a1c0303020d290306070e06071e03 70
    0xe42402c10581091b4010500c032003d001150040200b00d0390300940140c26098007d900c080103d0515140f81c080511040a0801c0201801521801404034034424801c40b42a1a52102441102c80c0101e8005015800600c00e0075a00d131003642001900b0b4140200010b481d0a44000050b0f03010448200c0300400f40c190b0112034030f40d5804100640307803889180001c504510b480d10025000046502004080203030480100d01005060810345044000320301d02591246030140003441035800c00300d0040c0d13041c44121000780e8030b0001841031030010b42d0420300f983c01603400044054100e032009408043c0c1c21609480c00c00081d43e8031403049c40501169901c01c01c40b91090b0500100b9100e00c03100c040c00c00072240141e00f980c0c6d5200d2941281e889003800210314030f040c45040c140d00a014035001c901259050010000307001e040311030301c92002c41966400c185641600c200345503542108483c0540401c0c903542c40c5240e607292603400380011a1103014480c0011a4009090511111032403048000c6503440703000c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 311032473 1250 311031223 311031233
    0x9010b09012d032406050d05012c0a0b06220507030f060509060108180706180b0a170613020c01143405070218070f02030906041e1a07 59
    0x200b1403525600720b02c5002a0540d141c4040262504200d20980007841401102d00042600701800410300240702c4200031025003040d6020f40400d50410301074081d5a00c3c0f4041c403a0a42c00c41851503030b00ca5000b082c0354041a520491101e6016021a50201105034101400c20f203c42c003000020180d00e40c0030070941861100907080d2012491200307a03a500704582488142c98660030668020320034600480c441d00c95850400340c03206101e01288450040c44004a100c40d0000315690f907201400b2a942038569407400008400d0007038500c0d901c00070b851070b49481e1104c19900e41d4242c001030020030b04d4640d495280c900c0f05c100e074000d21050115944a00c070b90403648000385021540004030000c0725241000300d2020340b0143d14915162a006541140712102140c80354003510001580505914481c6851550840803c4030854050002a40c42558005000d10200c183c41600c00e016003028201030814454900d0340d00c50007240c42d11003031160780c000b41c2100d03099004000320701603190255440c8200d00300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 311033723 1250 311032473 311032529
    0x6092a0d05100b040b220603020d0804030c120b13110307090506100215130f080304050a0506060406080c0114070c06091809020f0415030804180516080c0309010b0901 73
    0x8144136a00e040302499042c0c4610400d442038101c43c01d029040d44090710302c01c078000c028940005c0d4124000c0b803522801c218442e001841607034010300d40110340381d0703407080c9a106420088a005064541c1403000c00d0b116100024499402c030310607000044103280d42d901007894491280e02400eaa161154144221402d01c084c00c280300340014400340010b1009044081c0e0003540141c414148002c00d11815030511400000e01e0100740d60005840c1d5403414181019503a41a00e440252154003031440401c0c6d1600e880c0c41100c1c1140d40720303400340003501c80980040d03405a82400c1e2040b0002410070a10001a00d1224030b04c002c0e1080d511443c900500381102c180c030003c600c078600c0090302c0c507081c2002d015a8a50340c0100c0c05000c04c45002c0348a0300d42c0303000e003201034013294002050040007080c0070661070042040728401c951844001c0200ea41c40041100f0010038050036100400c401c0404502000084401540e206500a00100310a000301004c42d01c0d0394026402607080400c0203040100700300a00003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 311034973 1250 311033723 311033741
    0x11090d26040f2112030b04020a090315090210030b12010219080a0606092d230906060403020906010c050d05090907031a040e07080106170d0206092a0d0510 68
    0x101518040d81820b003444040010f07000090400c8040709102210203100c0d42002d9861003002d4025502d540240c030024180700e10600088603c01c88680b440b640611441c400c8031403007034000300081a40e210012040c1c009200038080507402508081030710701c803180240020030080c001c460010b90856000c0000030020400030345400b07849030901c101003000759880f80e190800c1c2c614010880408814105114003003d540d1010401c0040d2481c00005200d908142d081080300c070208801e2001c070b000c0004005e401381d0215451684104103020600140c202003621036846041810810b41d074100948070700d0305d00035444d58443c00045000400c04c0da01c0c28200d69042c1c2004290800f8441510704440180e10080c1042406001e20390346e840c84024150100002c000410241000700403c40e200c5036180c8021007044940c0c1618800c450140103a9440020f001e44140c002c2d10240606200f580003040c04940b0102040c0740c109030706014144e565450982070b50a4500c40e8004082002d1206030749001d40e10100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 311036223 1250 311034973 311034989
    0xc081c060b0c070302101e0f0906030204080a080d06030503071101030f020c0604110a1505030603010608030a12020c0106090219020c030106060c0f050708070f0e010911090d26040f 79
    0x110102110201c001003400950394101c902c0c600384440d0490403101e503032100808a1078043c0582e040a074454000d441d99460030641ea42701c2d00030310740f103a4055041e84a18401e5115541c4280034100109080b017010307140d40c003812b46003c28000e960b602c600e0301d550481d5500395046a0302004040381503030903220b0709582d9a007492003941854208554170340c0350940100060140360301b40110f4002681d40240c4103028000c071000408d06020340f0000144160401c4440358003940c40d0480c045010301e40041541c28211107640c0b01d503c0221040d44000207900030014a0340c86649075200815071081500181a103003a080b004071040b4542032a00910b081c4026003030f02d000c0d0741b40410902090b58819001c1c002c450b003141100141d2134103803800520703144d0a64860440b500400c0404903680744d131441600b04840d001205247e1603600c80e44030710200c450071003030542c108004112032003060404003141c0d030045005207640118070441c07032318008600d550420140d10701080000c00307010401081080c0740151501e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 311037473 1250 311036223 311036227
    0x5030a05060f01060c0213020c010f1a010206090a080a050d02090a030f06050604050705160c03050d0215091b0f040209130e0d020703080d0b12070b03150915040c0c081c060b 76
    0xa46c021500c90800800505415600010421071a803025004898071121442c010005503201d00c000c0c54a180e065202c2034014000c101c0885c00c44440007070300c03241c07281d00f04100c0c0e131034030107503070030940b070b541e00c034202d18100103070240804005542c412000c000254000c8034120b050307100a203401800c6400c010103c900c1549000d040c014030729030160540c2c100d8216111840c60120f40707414001340520302c5030b00042051244144e86103080b030f404165002c0480000d05c4481c6d940d105c941c4c4994942841001c40c0c40c40000091940460b40342814100140000203400113140c025414089481a039400400381111911451000719010742000400700e0403c1500c0940b484c2030a6540d420310600c00c0303e501d075220580350600035106550b1044003580d441d58030400c40341c1880e9aa2a100e107907804c111140b00c2d0b1803414490701219420840c161902ca81e640e0801a4415242d0f0800c000050104003008810490041c10001c00a5802002000000e50350500603d0b011210461403058840f00d420008002c001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 311038723 1250 311037473 311037497
    0x4091b0f08190603020301020f0a0e010f270914040c0f05180604020405092d01080a0f050309060403030e0a08031204060b0621070e030c010c170405030a05060f0106 72
    0xc00001c05030080303140d4a4241800c66442041c20107000c641d00040e40c95403000410081c03105900c2d00910803038450f901c1c2c01c0b8090510314010b540440743c030311381100400d40e903080f104013400b10403241200c88840002c481c0c210b0b98035501110304840f6050b5039403540d0300051080c04140021641c20740000c004d42100c2804c901d0a0102040204195a03ca13079604a0014041070701641c958040e074000e010081c00065003413030803080c81e44100300d00f200701c0303a05104502030301c4041aa800c900903059451100c0203001140c003a94661804c0c50b94948141d807140801d108100643ea09c24004100540c007a41c1c880104981003410001c144100394400da1103588104802d06a1207002e0300899440303504082c0014a032171000000c54420b101c0c112912070360340350460380c0c0300c03216814003c042d010b180b19035911075007108007009050f614480284d010b8007040d403582c0f9150010703500c803032654003812810365050305203aa81c0d00801d207003005500049590b600007a04110b44810340e00529401002d043c0b0345000d4005c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 311039973 1250 311038723 311038727
    0xb21091609060812250503120f0103020109032010090602010f05010e070c032a06230a0902180106080106110703030e0409030512010b090a1221110304091b0f 69
    0x1e600304d40c13108610300110f02032225007454800c4042045250441d0800302020b4500b0544940c000e85090b81c1c07401001c03010075281c0310b0311289141680d5041c0c4916401d241075890701031443c00701c05422241070382c40c0815120340f40c9901b100c1c6442d50303403aa100c0d4036559080c007038083c0c2510841e50b00d408055141400410070f002e118034000e500040c0e0b070f040110741c010190070115903980c0d14a83d2030a107200d00c001c65070690301046401b8610a1700a801c00c12035010410006100b4144559500e00400c0d0300310702007000107915600c89010148001c144801c186100701c3c400d69008000d82c05071000c95100c02c01040441d41041c0760030106c2600d100035041c602d06690f00074001c1840e59000502640e40d5000040805000e02c080350a0701d44a0480a559586e68600290066000c0026980500e20706140010741035070350301d00c482c1c1c80e547c0145142c0701314100b44066024481d0040c001c10030041807049044449000303100070405070a02c100302048058825401083c403400e10000403041013840f160b8200c0883d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 311041223 1250 311039973 311039983
    0xb0405090a03050a020313060503011505030405070506030c0c060a05040605100b07061e020c0a110301110702040b01090e160305131a09160b040f091103010b210916090608 75
    0x80e0b0504016132155480d0300b081b491402140d80c070103207103043c4c11408600b59421a01860488103a20181c02500c6411482116603000c19640100030743c1c00080b0900903031800c01d0103983d10040c5410b03040d04046240601a00d4900140c0b05140d0a9035554184000c0c0701c414012590303c40a9139040440580c900000112107110f1300c00080c103001d5440001101c10a8001100c2149080c4c2000c19900c81800c00740d859202d160b1410b04484400e0161814001c50406014003a010b207a50f0807400d0504c0c1b041d80a010103000c5820700941044880fa00104000c40a00d0314280122082e01016159807000f003805400c491000d003c004082c81d00310b0b1203100007451501c145c01d50b2094000014503030f032642d0b500c1503e0300c2400ca85018403007220700340104050201c600640119204400161640c0744d0b211480700c111203802c0f5060350703a07040400042c020302089400030702c1c0f180440111390024104880000c4907400040d40d8146a94003c02c0500500c008080e082c14003400300d900b0104462071900f4041c0b6581c0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 311042473 1250 311041223 311041243
    0x140d020615010c0212030a030e010621060b030114040c1212030902040e030a0f0314040c03030c050307152307050313050a080a030c1101151802071211010b040509 71
    0x11000030007496049074401d8021601842e4007900c0d0072415400c1d43d8040c2e460344c200310781030b1000070324004002c42254014064203040300d40a00c17283c082035950a100641d0f48164000903940d5580358803840e002d6450901c244013140450641600e04d0341498900229400510790100046d01241c0c6a09004944060300c91409036826040020302c0d0341c1c0300d10114010303115070801c05040d8007001c100040e020360000d55400c3e540115a03400c000104000d1b906281d101c900745c502506808030b00b030050000a01030f0725035069050082d02101d0502c0d0450b902c80107091300b001d40c0300c101030307132a1643d01b800003110f8021020880a0661144460700d42200010194000145018401000f91413403a0900405002e074800c4160031803040c940c0d551050300041c014100014002c400600b0b0b04011045c0e184040c440c1011134002c0f021401403161a0603454259a285001a200701c80d40c204883c00000f010347d942e40400c3c003540c0c1c4a031f44400204441d070500711200c00540394012400c000030060340c50804a191852 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 311043723 1250 311042473 311042491
    0x6020a0302120a090b0313050a0528110111030c0601090b09010905071d21240112030f090527010b0c0304180209060c01060f090603030206390403140d0206 68
    0x1d0b47e596000803420040b007a40c0203001401820b00403c04e104c40862030798024891008078070155085c4a00712500045d8085014050080c03807040100b15610445406511450203400c0700c7c200148131980c0e0341492002e131b22010417a9079440c00c1c9503940c04c1601c1380c140100100346003082640340c460005041030709c202e8980103c48a800d20020400e60b03848005134041028045070b15559060b082c412681c40002040c0018074055403412400d2700c04848030550b058541802005030850040d680507910384602c0c032118414072880f41c0c0041010303180d20700742c2c03800301883c80c4000c21040100b012428030240c040e00540109070f4100010349909100000315000c6991080e481c0120481c0080b400c3e0007130090131a0310758440000103480003000b405400c0359098500351881d854070a41d03654580e000301c5d20103200c010302503000000000d03061144000000c031881d14408250b03981480c000f0901049644070a14908042c0000c901072091140f0b10503460950344958004010f00c00d81508081d6991a005140200c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 311044973 1250 311043723 311043727
    0x80c0a0e10030608011a040506220213050d151103130209040f08130e0f1003022e030c0e0301060608060603040321020703030b0103050f072706020a0302120a090b 71
    0x3107644264018002028208020001d001d080c41989042440f400c2410744954103000103e0720a2500511103001c460600840750b00000800c0f11000203904090070103025116a80790004e440e4a800c125082c041d03210f150209074468407069410100c64150104e0544204240100103448940b880003080c8070b501107612070040e50741e034a0a03520195070070700014802c03600443c0d0140c0003406246504141c3d10000c50b515500e83d65408119880780302200e4000d180280341408102600300010b0100e44c50035856001c00001044030480b0700c41a007450a5140081c1d9540c0006160f04d60010b48201c508400724000d00c000c0303203030010003409043c1c00380070584a03800001c089020035025003000c6095000456032300d00304030503c1e9080b10094000180276000b003802c01003501d00c150300c030b441890f2007007480b100b85000c15118140111210074004d400300402c207650032084180c0c1c081346002c0c40000e01c455401031520070601c0c94000c2c00c11901801000c0800c206010b00c80b0440d402003517000c241c2d072060314483c1d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 311046223 1250 311044973 311044999
    0x30b0a0f060801061409010e0712020306310b060301080d0f350a09050a06050901091b050a08060c040e0a020415090608011502120708070209090a03080c0a0e 69
    0x240055840ba28480d0700c2c01c440091900e000391520712520b801141c0c41e030196030380c4107030b407599809080782e02100003a1310340700301071000c101075018580165001c0c04410007904040398041486001c0c0085820068005c4000220184a40034114003080140c03a260b055503d00b10001d940c411114000500f400f003d141544c403914070034881c006990100c10030340702552a40a0900d01842c03a01c1502000040b0302400260808503a07001c0d00c810070b5800b100401c103000003600c03020300030800036101041035520780c3c2c441008950b4038491a0700006141c40300d450788500c1c00040040810035076006030116001442040b1480041c00c081d81c049600c02d0409013040c0d60b800107940b000344119040545400b040000c1007403050743c4000320900351085a00c540c030660b40c0b41c04201100c403100b00e08950040e030002075165004022038000e0078403513118251040c1030130f10316400120688021a103011207a4401e08140b000d02d90b010302115040314074544410724102207084020060000b0306a03060040d9217060200e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 311047473 1250 311046223 311046251
    0xe0c0904090b01090e0606010903050d0f090f0e0603071e090c020c090a0b2d1e06042403020405010c0b07140f0a02011b02060f0c0c2d07030b0a 63
    0x1011956002c10865015038440d0101c0d0002d01e40043c5580c21171041c140040e5655014010040642c1d402200070512680c08860888020740000035040404c008590006202d0100801d01030203000400310150f01481c0841c141490910250302160704046124100c0c55240601545642a10804000810006c41d0040181d2510303625100041d04000c00d81c040010703041c0c2642c8103100c0040d04450600580c0b0701142000c80d0b41000341804090300382c0501014030146040c1c1c842c8a5442e1243c00300403000c4080d0f0b00012019000740d400a5041100400e03a00540c007d179500d5041002180c1c1001c41c185800e281c002070128814050060103031080c02c020030388041c0142014901e09003401d140e255190717540303a1804015048503200001540c24000111446108029240b560070b0183d8002c10683e43d4415041c40d616802400303850702241d04009000e081807050098241040c00d1402050f080e400180f94104c10801003160341020303400ca50000d000055291480c5600107901ca0030118a8860800c4c0d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 311048723 1250 311047473 311047481
    0x50d1b0507140a080a0c050c0306060307090b011b03090303020d09080a0303020903010b0325300f05030d020301030215072102070f081c020d02030f07030903060c110f01060e0c0904 79
    0x24000c40000308032455107642c00710070480120f1003002908c2d45000c000c0141541c07210181c62203035140e002441c061228039160743c0010940383c0149498808500e08405c4030030700c13000f420300c1540062102103041c070a00da0104a12002d6408514090750780c1460300e4403550b11a030f8040001010550001034500b8266002d41040c03112140c0141030b038100347e103003680c0c54201e0720b8134212000c0c80da600041c0008281039a150443c41c00c4e01a00c4c0003900e42c1003048407041c00c940d03180c401100d240e01e03000c520601060b000c0000d042caa44600d02c0c01a07495055004118071502d0540030400350f40802c10403c00000e002e941c003c880c45e4042c0131074070214551031209900304051600314440e0032601e1480007502e9080010202800d9022000f003140704080960103d8896500c2810b00300564000c0140008010303001c00280b880d0f5000f46403205c1c101e6101d94411003500c43e03030444640041d4050850546c225003d10100040802000007003007164502410160702c60b10042445035aa034020a81807426161500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 311049973 1250 311048723 311048743
    0x711030a0c091e0203090115050d08042105030c0705210d0305070e060c01050f070305060319030306090c0c14010c0e0111012307083601060503030a050d1b050714 71
    0x1000d45d260728055219500814144001d0f0038000315070f41000030b00703040a00b144c00207075804c440200d10301410520349076400852170000300c860820b0048102d01203402400035100301c41001025101052070101040498112029100a4114000301c083c0d0034000018092904c10003501300400c2d9982c1c1c0c15001da80340d1440d2078a443d0003020010328508211010b50065204000c6604200001e8607030703007811800c13140c0894415402d42d0281840f1041c915502c0110301c0040c1c42440c01003821a280d5071f4010a03240461100f10100d001040b0100c20080c0700318003907030240c6110000b00184102d14400134690b4898068090500082e00b0b1031406643c400e401084c1d20f00c8100d54040001c0840582e00c15950714210f907280c0c00920748a001c1000c0d242607511100c20210407403803030800c0d500d80c0c1344512428031041c248080ca6650354000021300d900e007070000d8165119180c8034607407903210401080064800c091004501280607510443c51036401c101603c1d6002e8200004211115415405d2840c20300d0540b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 311051223 1250 311049973 311050031
    0x4090b0307090f060315020c06010302060c032a19030e0103020906040e0f0601080f0402060409020a0201180b191506030b032e0606050325030915020711030a0c09 71
    0x800c60440e01005500204c080700d1145004c03112109410910701c0803409645012622a00900c00400152030b00b080903207084268203064a01d001c400801c0d410120032081c40907650440030340031132003405109114030341c00d28050300c00c080c4107240c42e560000d05489001f0031050601da40802c0205807901c0d0101901c000c1c01541404032080d08040740d0540d13003188100c610070300140480c800100f520300021200350044d50b014105a04103800c2c1140c0074040d40003040004215942e5643e8840c0f41500130a0342c4440320300821801c5043d041901100d10019400c40050f482541001040c41440781041120b0084620300d103400030702e22800c4000a0f00b0084008030307941c00c8822107031700f010740c1801c011092031645810400420440c0c0c2d43d044140c5d03903400121b03100ca00150444019a0642c0544044800035501c03505d0001403104081d0f4850300100746910f0320014042d030118580c010401c13501c410542103203040b002004100620303a9511088030680c09882080d6031103a40d120803131030a24a01c40780e141002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 311052473 1250 311051223 311051231
    0x30c0307061a0303160b0a090819031a010c02060304260901020d0e010e09061504540b13140a0c1205090f1501171204090b030709 57
    0x1400d0900141151404121800b0041041c03800d8624001045074503840b2541c102c4d00740b9401c16182da2010031002000700d1031258580004c01e00190500f0000d010f60010303000a00b40124049030024211030001d40810401c0c40c49011203401e580e004164408240e81c1180c08036541d59991800000e030321035001c3c0c510101d51840d4462401c0c0b6140001520546000b0b038201c580807450301c102143d01600c0100101d01003001c0ca1854070030390030241c000aa0040d405400762035100c00030310502003d64026407081c103881240711003c8403d6035144003040d0402405001e218240544c4c0303d0400c0d4100c01c0d80500c45891a40400403c510038030b65040145190f000408680b445415103403203401404141e40510110400000020010010340c03050059151079540c842101d240b200c4039140040801408441d9540324000044650b5101001000503915124045c0c40a65151028101c0440e4003012001000c0e0809003000d100091880180c4089401c0c440001c9000000d0202003420000140c01220b0420300b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 311053723 1250 311052473 311052487
    0x50915031911030601030309210803091605040603080910120c0503070206091c050c07050a0308090a150507021c1a150303040b09010e031911010806060702090414030c03 74
    0x3690740e144440c6002c0c00030020441c01d80c40406032210024003000700401c400c09402c0c080501506506c90400000f00e0811100c0744ca02c1d155205250400c41e050045540003001a0408600c41c040c008001c181c04d0342c1c103000c5e00b03007181e0300d41e0003a020b00300046000706100b042c0c1240040c4100903100e03144c00e00b00410010118a00d41c000c08541c000c64038000035129007004505400b40024038250004c441c50314145050100c000101e4195001c1c0c6000c400c2d9100c1c1d4400403d20381c2e02c54490100030745c890340c461950b4100a0051100c46480c80c4c0c080d1030030f0044005407003a03c0350000d0441d60f9403a41101c0b00d0f400380b854030440904001510001500ca2200b817685113171074200380c0c1d8085000f65040003070310203440c08030741c101603691145004403800b0200034007002c0c0f8554022400380501d5480101624000e03008554402403c00040c04151032200240c0801c288650b04924059000323001a00c00c1071401301960081103a084015000411401c82049620701c0b06009100ba02c0801d0717114026203955600c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 311054973 1250 311053723 311053753
    0xe0402150f0d06050f1008010302060918100519080a0b04021815040e010903050d110408060a09031209020f09270109020306011401170a020706110c210405091503 71
    0x148600416003c5d05514944040503e01076070341007007120040c0d0760001240c1c2981e00344045504504800c58228507a0281031852250078260b50748615003500383d4035143d510b0a8104624284440c41400d020141700400703011001002c18004035254020456440e0341d1210f2021400440e201f41104000c081d04000b4080761f158031000c04049908121024041187d201e59040d08a6141480c01004101c00700400c107248000ea401415005203140c604c1800c2c640d07604051410190229070000361b841da40c1400d1400c150300308085000d40c0620050412924007194040350003201d80e0075003240b2030042c2d1800036401b81c00c5443c0c00d800400f801e18100306110098010079001e40b4141e00101e1007801544001302d00c120301070710740c86000c800503500c10315903003403d5100080b491000313403c0a51280e001c006c2100442c0040c041c00c141c210424181d1a50745055402541c10903d1484e400b00310b0042003001105481012800d98041c2d800448000641c0d864091840165042684200d50580584c0e0b0310070401c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 311056223 1250 311054973 311054981
    0x1170c0702041a0d020108041e08071a010501140c0106081603060e010902010512041b0609080f0f0d050a03060f03060501030309060215180c120c011103040e0402150f0d 74
    0x18425542802000070b00f50760b8083c0b40a0448003180c000c0c070b800c81d03540d01540c03003680341540150140000045400307400e000360048540827241034940c2c10b00007842400304194138296641c2603061120782000d079414240024800e10b54081407104141d404108009849002c0d40054000d1000c0021509800510040c516005c1410300c01503030424500085d84101d0403040c00782c00511641655910b2400c801c09440542480001e001035848420303807802c426010368111a40e00180c011500d50411782d51522070400e14100304c95503180740c260032100d01c0d000c3e0690005540001d004642c1083c50b110004600c0845c002e108a80c0040104010b2031000406d0280540c40300b41178a000b5958003881e1605d0700301c02d90360780b9102644c8107800c0710307000d0000d904a445051140c440c00110b8043d00e40e003041d91400205008005400901580c1100c05100c1c510344c0c1020307105804010407405103042601c0c00d04100c60503c03004101900642000b000c10010b1503201d401c0b985201d014a055a440384205a200e034028 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 311057473 1250 311056223 311056237
    0x8190b03121b1005010f0b0304120c15050108010519090f06110d05161103070c0b07080d14060f24030c07140a0b0708010e0601031a03070608100f18090201170c 70
    0x4046c501c070f010030280d40003400c80b442035400c10700c44010680c1c0000c049400303441001042d10705261400c42541611020b0003103d0003480b94400115140c207160385489280b000d891402c116051500f031411002981c52002614550b402200004502c8503260300c03010726108031010700d0015440c03c07080155a148410902180c00280e64407400710740172700021680c1d0703842100c3c009014039070440000c018120307070070000b405510710507050740f410402c00068034400d43c3d001c00100c00183c03600314100a824101060584458041110400504001c4c29010300b0901c074524500a81030307100200062040b5503a6040710141c9a00807401c5105051000c0426207464444000700c5103144c00102041665105135041410391f44990006002c070385aa20055000381644503a20b0517198014112210a0344c00b4403851000300026100d042c640e00d48403490040c908466080071000c003c020f0010b101403290003109850f20b00b441400080d00c04550700041e645115200c070b07800310101030341b4108140e540030600a0100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 311058723 1250 311057473 311057489
    0x30c01060b160f0305040b070602030609070201060605090607020a1502060a050a05160c150f02040e0c2a070e04060c0210090809041a06070308190b03121b100501 71
    0x152980700c0c0380341d01d958841d500b80c6a4034101e030a001000460114203072850002e100c0e080c0189080d0f6514011440398202c004182c6005902204218860600c9080c85610078010301c002c0150a051460192217802080c07641406070344089000c00842d142e011078540a8002c203101c414100040d410300a640d1507040785d1040b40d00b801c100109112001d40d000d0980180309030080b41e01208944d24003100c55628dc01c80c1510a01452a00000d03040d070349201766481520743c40e0303015035201d08002c1c5c4000800d0010f0b140381304400003000000c6040358002e00c03001411450200701402c441c0700307414151401c9a1500052a034070444030501c400c0103a254403407503425107107400783c44424428600080450348517240141c0140c01c2007100c100356160507030080b804d07070085d80181c014a01502c0089101a00223400441c003164150081c8014900040740107003900c4180003051000c012098003083c0c03503070f0100018008107600800c11002a01c0da0034051101340d8188812545c8507800160b051015007420310600c1c00e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 311059973 1250 311058723 311058731
    0x160030b0f0717040c030f0510090302160503030405150c071701060e01140114030705040f0905072a030c0f0b040318050402040f140402090d0348060b040e030c01 71
    0x10f100e80c10400c1c014407664100301140103003803030350310346890105510030304a89a024504642101c8400c1d880750048040c0264010841c01c0c0050300f101e0812000303500030754800e510a0000f04210f40c1c40690043da22552a2083c6445c1c0036100d02c0a4502160398202004046240c0c95203030100f201540068104c0b0300c0c00c045100166a100c4a00920380b03402150b1078005070301c071029040e0584102d0000c542110791403a01900c1e240d03035075001d8109012140c101c4416541c0301d500b07000415138400f07c0c1d04201c60300c0080c440c02000e110102400b40c0043c0401c020140011304d4810300038802071314022400c40740c0140a030700f00e41c0b426150003400046250410050060803103c04182d60405100750740c156404a034082603c6410b001e1821890602005555402602040b2180c0a03860b01f0003500300480c82501e41060a000c0a04610102e516007035403e040701c0d814140300808400f114404c80441074400290442070340c1581000c4000c1e00440b01c0441d080b600f0580040340b0103500000a0071036206440c0200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 311061223 1250 311059973 311059997
    0x705090106020a0209250206010e070503070912020a03171309050c0904051f080f010e030702060f0d0906060b18030318130207050160030b0f07 63
    0x444042400e0040000503442110355000500b0102da4160700160204105a100341140403800d8040903180340b0180140c01240041041d041685440303500010345041c06401c2d032910f940b00815922051080303103e4524803000320010341d01d9880b250406180c1201c05000040040b01140c141d5900c046e03152003252031a080005951401d034412540250400c040192402c0128400c100103801c0240940e00303c3ca0341e010441001080c04066400248403c00c09070036001d6580300d515086038580e00c080c3c0741c43d0708100700360001a83c4810450b0600e00e45010016200c421614905009042d040c100900c0a840d00c040030801c5400500500903c000540000303007009581814141c0b2401915006113040010401921180c58800c408000014100c0801400c1c0b84041d00d0701400e603080d2440caa407074050941003d00700b0100d170840716064480803a001810481c540d03912000007162004202003100e500e0094004010300c55160342e002107410503240402e9003040f00f284071504109a442d0000304000890354 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 311062473 1250 311061223 311061229
    0x30e19171204111207140f01021504050105040b0c090604150e0a060e030c040212010302041e051315020a080114031e0607030b030a0c03081b1b09010f080601050d0c08031b0705 77
    0x805c055071205003030404900344074030070300c5201c2c0b440c13007800d60650241044404a0008003007006200324014030000c286c908107401c1040f0500400b074114010b01008121804854990004072000c40d1402c16040d491020461421501c04805140d1a82d01c40c0c200100000c0c4d0540c050110b61030a0021404e42d003103204064100030880c0b25400808144081c0400100b025140ca40c1c4002c54a02c201f0160340035640d03440e05801c0071a4000c80781061030043c1c040c078020a110342480000300068107601e045140540301000078107499014440d0017454540c80001180310340741032000b03840069028054400745800c102c0c0c0d4580303600048a20000192904e11040c600b0f140014500c20703002d0704288036a1001c1d0a42d02e8810180d403010a0304101e8075403180e030842c0300d11410000c040840345140c00d1580d281c2a820b00b040302401d01a4060b00c480031b41840184030710280480c07072504482d422030780345803070241c24a401c00300c0e0342d900e0307010b140c8500010502101c140382515000c100d902d2094141c400c015255020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 311063723 1250 311062473 311062483
    0x231915020406020c040e011532030c10020715030209032803050a1715090609070f05090a080f060114090f0402040b0f09070f030e191712041112 63
    0x11000140d000713120214560910381e01c00c1a000151000101c1c20380000d4246e08040b400b00c1d4071442c90740f2823000510744c0130030f141d0f030240c0f464030a40d80c41c0321101050080065500c416000d1054440e480c007000008071715008010407801854801740d07000071299002405402500600e040b01d000740166807110b028454540f1100300340d100da241c203211078840140c40c210b58940000c0400018400da40c000780da040031212651501c00d406820f420f00d69a800d4800f4043e641501400081c0a0204001030115084c1c010784603251544e010b251160321619842c1c001018403980c2c2d40540d83e02d0041802d00ca040d04400f02d4110b0581d0b0a015144550001d0b034001e105180f90201d5849281c120b40201107001071030309420511a550000700444400b148080001301d25090940b40c120214600300381441324150140201c2010b0880340c0007501c810304841c200011102c01b5854010802c0044114151a610705030781900c40030a1841c807590080c6c502803804400006e050302040780304541003c03441103240c2001071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 311064973 1250 311063723 311063729
    0x60a0602070b0a020c191d010510031e02070b0f0c070c0b030a0e1002130f05090c070309090c0c0317090c04023a0501060903030203072319150204 64
    0x80207240c590b181c07512005a94021683c580118001c50070410341c10750380d05640c2640301683d0344251540502e040103101200c0c0c2114a09003084409000401542d610403c0710040e1060360b09010505196071002c0c0c1c80540c0d152100016450300c08100e10091000314004184981e101c038070030160035107074020f03aa0320070300600c0402004a08803207024440c01840318042e41d0131064108011600080c2e6610590a0441800c08007030402d50101d00f01c441d26940b164500b00500b0301c0003c008209040c840406d03804031009090790184240041d80404051191280c500100441c0030100106061000c004201403495401500010400601d07203080c0d426001e00c080c0101c001d18018040810804288800794102620070043c44503c00d4425a13581c039100e4038401c02c64035001d0803180c40030390b03042140c2c00c80d2010703000f80c010018036200170b000098000045a0505400015104030131154400c60502c03c0800160018035003d40c0145280c16106101d800314014401d804180700f007090010041d0803401030344 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 311066223 1250 311064973 311064977
    0x30f06220b0a0e0a050912070201080c1605030c0c0f04020307080610021f05040c06020a030507030507050c0d060203040b0a1503020402030415060b040608010603090201050f210a090b060a06 83
    0x881160140c1980e9002954080000e0b05001c4016a1400c181000003411294440c9058407601045040340c41072108001c0e48851403c12401c0503000d0300020b01c4200000c208d81400c490008010700580074100382100b40650003400c0b03959904021601701e03216001c6045082c0a4001010666102d15240c0290781c420403d0342da0780d03100d680d41c1400b0045420190841c040550107805150381e00700d950660841080050080045036a043c1880c216014901d40d501180840d0400b2582e5800642c0c8803040361a100c3e014500385480e0700f95070074010701b403622210405d644603013201c91380010000c00d80c01a51081e8010a240013150b92a6040c00082d603035104240c000f003042c2c0030030910061810782d02030341e040740c040c000620321410200d0007032080300c20541154000c1c00c000700d010402c0a80c0083e040e40540351604e014005207071107a00282c001e001d65102555070f400c01054074091180c0e00e0005814440f210540241d8500700001c0400061090b8003041d1042041d0000081081c2403000244044a081d0303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 311067473 1250 311066223 311066269
    0xf100212070f031416170f010b0c120334230c0111091002010212040816060527031207200a0506070e010e13052a030f06 53
    0x74004a88000b5003102d442c2c00c0c03540d42c00051300509040c1012500c58030816032850900a01c10001604e00d0000702c0d0380b40a030b80c49400401200381043c0c00c00604580a400015450384480e01141c4d0511120500904041d0310110400440404004003811440c00048074080d007202c282c5a1000c025100c003031400085552000036420003000c201e0701039030701071241912508140c21400810b0a555410304903114020006c5031000d42d518010398111a10100e074002145004000307402964080d10043c009825030f0004a0628000b1008400e081000c5901c08010001c900e4038508002001403084030319160300d900c4c06908040c02800008551481a0306000c1000580c4c078030100b1a03000d0030007404940798512402d41a00031003404c01c144165103200e80007601e0240344c400e00080c1500800842e0504200c3c80b811402c2c803540304c0380801d05540308039040111301030740c07610788108100010404c0440c203a0803002d903580b00c20f542d40700a0350107070101c4d030aa112a80c4a0008004e101d060b0381179811515680 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 311068723 1250 311067473 311067481
    0x1e0d020d050f0d05151002060103050a020f040608030309010e010605060f160c1a1c2703140f2203080301090506150f070309150207180605030304080f100212 69
    0x1d0009419480000c0800a1800c81c400480e80140d4200361103000c40001900340c5841c00f46003d15010502c4640b5200406180d0b2560b140d4607a01e14490101a000d6000310b20320a002c0c0c2c40700c0c3c00c100040d01400003129901c0c180520a94000c0c10100c0700340096500e2b000d008540c40c81e00604644090b000020564180a05c80d030a810484103d503404891000003201d00140211002148000d8007020501441c0c4806118880030460340c0d001201082c5240313800700140481201004840ca42d058007419070901c04690315007234468803901c1030b40882021021802c892940350050091928000e04d020080c50003118044217048860306010043c410b000038001440420003540c05141c0c411001040d40b694182c811700c00c0340c40c552004030081201c803400280380d41410342004100c401001c00d410220054450201c009448640130702a8591200311140c40f1141e0b4403613504000b0240030300905030380e03a075983e5251107651006405842c074282d00420412031502c480ca407007551044183c0400840785580c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 311069973 1250 311068723 311068727
    0xc0b1f060809030403022d0603010b0a0804060b0a0f03020a080309150a1b03120e0604080a0516140102030910230403120e060a141003030c0f0807051e0d020d 69
    0x1801000032002e0311050000102607581c14a00785071400420001c1c80e1180703404510710418031074040d60680169420001041904d585104546215040c0d00d4550302d10f45036881c000000e090158140c603400240c0c07400101d251442d01d05240100c9200306c43c04846142d50780d610b1500d0b40030340311849500094011300802c0c4514034000400000e2094907000c03150103001079401c0001603044400b50300185e040c503810120044603205d584a00000307800140034034a441d03a2112240c1c03040300c601700204080441c40500e1200136401001c4403540c0400e4107582b0340207000300e040c003e40003219070740c2061083d089143e422203024414600f00d00d10304441c849111040c0f6059280b0100e01810442c00c11201d00081d41e05220284221428040400b02400080c1405004602038030306e074420341ca02521018042c00343c880d421a03018000c680d8541012286805c0e1400c1c0040040091080507148007400144841089008200c030607925592127a007843d000c01504a00b0790f2803845061020140e0701c001c000d82a02c1d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 311071223 1250 311069973 311069987
    0x503150108040b1b190e040f181103030c0f030a030b090c0301051504090203070903030201050718050907050403050307080306041109062712010e010c03020f0d020d090c060c0b1f06 79
    0x36810640e401d242294a001001014000b4014640006c000b02880543c51030700c1d0044191105407200148001c5058120307003203055091580c0280f0241c6100450341072a1002d200f03940c0410740d100140e5550460f800f1801b0b480350302040070740d00024075040b041e40c0d075880c1142100f4002c1d8201e400c91421a805c20040c880d075940364244410b02d03080b060100145070100c0c3d0000750b10030039460303452501051540c0350281c2503800242484041c003140416980d03141c900031080c0b40856400b114080c00700d0721444c20940d150b1041c1c1d04081c020340000140d10b020300a41c40d0045025040035142002442140d50102d6854003ca03481580d001070200241490b2302c05095800c144800f400c01c070180c030504a06d0014144102201000007941d446c0c070a8866449020301c10054068581c0c2815443c0a0f00d00c1c910b11180e11880c0c10079001e055010980d2a019450365005441e8140d0140081403401e07100d020140460074000001c03182400104001019200b40300d84e0b040440c0302400c80c5241803410604199460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 311072473 1250 311071223 311071261
    0xa02030c181306080a060e0309030a0602160b250e011e11030c2413080f040b030f0603010e0a0309151209060b01092102091503060103030503150108040b 67
    0x451040c400002d10a00c40c45a58001c081080080c020225585490780a4641012054030075401c148054031103610041410441140d02c500c0c0180c1d2081c14000d024600000981d01030302c41d0506d030b0100844070140300d0408448641c40250b6103c001861041184c10880d0b05103820b000641c07107101100000001107648059800c0744c1003000c03c4c54103e0b450146107410882011046500c0080c0e074003244c490b41c403e0680e082c02e050944d02850710381148203650f4410107540062811034009480441c00391404281e0f0050301005001315964100322400812686003070324103d200707500c2d24a00010a007c00110a80320641c16299501e40030301d0194409040d84e003e03580c00c01071289001100f8290602486140c6a0138450600000c0b1b01c1c010000040419410340c020175501d8080214041c1d203a00c605a0454449504a0b4162403c2c0d070b5030b100f03030380d0f600b180040c513540c0503c03680001000b0550410091441592070702c100428007c504c02c01100d090744241d034003410314101600407915908200b0300000712 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 311073723 1250 311072473 311072479
    0x7030309062307111b1216030c090e0307020a0902031801140114010f02060f3705060d0f0809010302070f060b090109020304030e010e0310060f09050a02030c18 70
    0x320400340c02208101d25401512030710b100035000104101580c10030000100c0800c1c1c00b00821040200000307820070080c0f000c4102e0310a800011440c00350b00f408018070b51880f0a40800c42e015507039a840c04440c00450750188125603401e03c0e024049294001060fa039103140c0041000400e18500030f0000029070020307190503041c00c0d03940f02144881e8030034010715061b0702030f030010340e02158945001c2c0c03101880101d1140d810010509a00c0e40d81d580c0c0010b049400c500d900802c0b003026214a01c3d401d0119030703240a5990101030003c0512640d100381e511700c001a4800e4403051001ea520802081500703000340130018040d1001401110110716400c0c05003c00308018180107140c070843e81c0394032461a1400d0411108030392651001d64090409140c451300510384c1c62000c0d0300350304159401502c0d4041c000000e50400102c401c4005450ba0200701e6a01d0206040c0d504008240d25152064007068041c00b60340c10490400300442c07600b84481c42224443d001c0e56241d14100b48104402c01907602169200d258 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 311074973 1250 311073723 311073731
    0x1e020316031413090b060f3f04140c060f07060b04020f070309060c080301170a15020a080c120609040602090414070807030b03070b0c010e0d0302070302120f0703030906 74
    0x10341c4100303803004185000d15880c2c0303c41c0291415491105507800000018018101448840000c02e18030003a1911102080c450070240c10b014004205045460340c85460300c2103d041c0d540841407070400c080790095001d0302698101c140809030391a661307580039a56130380120040100e0340d00505028041c0500510800c80450441c507080700180a036001001c40485001d00014401c0406030000300343d030002c00d001c3c2031580c141c0c502521620040d0105100350600400d03100004003586038284a0302903201d42c090f01c1340500003550086034000b03401c05101c550100c0d107220003003a4a40011003e844c4444008181850aa6074060a04c00c4c0c0700300182080329059001e020580d0180e41c2c5000e10f20201e501e280c26007400d48bd08540060607c24054031440505280c014030b0042a200407895a003503c003070011180e074620800714400c1c0180070b480d54401050049070112808076a0607001070403031078000d600310740c01e980842c0c0d20031840c0c1c07045c1c00b12085208c004004040c0000d0094024584c0c0e2401420005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 311076223 1250 311074973 311074997
    0x9091c0e03060a0b031c09030807050c10050409240303030e0319020307020109050906150c0f0114100509150d020d0210090e0a09030212071e050a031e02031603 70
    0x60b00e007110030b5495009007511240003502c141410050301c543d000c1e04101d02030040003071001c09012001d407404041d040e030350001240d50601c0002c008040d59180068102c201c581c00e01e00005189070064003d2420b207030b050003008981b4004a42d02c1480390a5a04604856207145030742c00d2340101014448031a01d4041800395000000c02080040100c440f541c01550340ca00c210310005101c0c01181e01f05030f00c540088001d121303c5483d0b4404a692070540a0185952451207042045c58039207519684101c0d5802c04a921440c00300f4003902d0380c0900e00e42c41c10140110344540401051540c00c550300314081c000d44a2083c03039442c00d01d9502c040b603400a4440c8041e0303a0950080307171075030131502d03a40c501050000c0c0c0200071441031100d0300d40d4894540e0310108591503503950002d44421030741d0042c04e0f884901103640d00500c28802280c072110701c91019001c0c803c55581c90503a46980f4a280207401081040071041c0c0f84194062101c890164241d02440ca070609161800400500c03402c82a03080201520300d603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 311077473 1250 311076223 311076229
    0xc0f0904150e0702010c0e0a0b0a0c06021b0a140f030d09030e040507050310051207140f030601030c0905070804030e061b0d0e0f04020405011b050a020a06080405060609091c0e 77
    0x1050242080307a002281a0140704c201404030f80965440501910071f4248c10443e5041c003000b43d882c40f100901d09044201c1142c101034002e4061708200b000d044085004106942d540040c521040b40c3c4640e60400a946880341c0c81511411740b542040b20641080140c5034042c1241e0b445140b186101c2d003081d008000c2400d0100d011079200b110450081400001030003406a03101404000410044428441c24201c9040707041d280c1c1e00d948145c2c01122649001d00c4040e68500700c09511030301c40a800c031105980d69040a8148034214452401300c0c5107002c010944261040344075074071079a016211074400d111210284181d50b888201407511002c45030510b00304100e002e02180146118907070b140d00c041000f000401c4521264040480d100b10302c1000108441c1c0d80200c1d040c3c0450803e007203481480001800d185003080c4059800a5000c0e01c8803401060b00c94104030702174040c03030080c406ca9440e5074400c010702c0502c40e000d562254082c0e0004008031703100c81c41d2101411045101e4030b800d004160400b408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 311078723 1250 311077473 311077499
    0x60603191802091b041401030605191806050306010b160b010e060a0f0e0604050405030c0a051e0309031209060c0613030314010f060c11090a050f0c0f090415 69
    0x30044030460615400096142100000360858007020b810f56104155070b114285170720581c0300301e44225000c3c080c0d144442c0e00982c041401410042d14001c8200401e50038411a01c1240c00384403040d1404d29100400c0398480c0c800c00090741e101a004140d56424900540c610b81c0000d201d001005d0003030f500c080002803960310814009e04140c0c200c00e040781000000c020b0790010940041032503004110007045094205001550030005c21740700000d1548a03030802d14110f100340420380c41c0c244500400c1c2800c00000107024410090f8542c0801e0f05528140340403501c0744507214029600d50701500d091400428020300808042c84020003040c54140c3c0320b01d0041c208541101c28185440343c0d07041c0c7c5010b04d40c0602403d1003c40d50310b002082030358103218640c100c02150f40280c20130003515101c902c0030000d0383e027000c00d42507800811a0116180c12514580500790071101a0322004074a804110300300300c850300b0703110b441c4a400c8040b810301c03100400f444003c02250541d05460140d450700007a00d130b242600c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 311079973 1250 311078723 311078741
    0x13090e0a060f0221060105070c031a070306140427030201020d0e0f0d0e0105070602030f060a0509090d030e0709052e03020105070f03020c030106060302210402060306060319 76
    0x600544421400c12070100c2d0400210700d0705880c0100308040c0c1e09044500010015540d0103070a00c815160b2000403a00c80c007400b407001b003039007400020107c10b212228032408203c1582c082d84906550300ea0300120103542c82c41c0301c0c00400c0c010240d400c2c886ca107000d070030840f6200c0b0201d1000400504a00300f206511400100c143d016075030004000c0f0b41e0700141c0c091236403a024500020030064001503505030b0380d001100801c10800c0014600c1107416881402201ea0b49900802e056450703040c807110407104410240d414500c20084284001100c3c02c04601c0f80d0310480c07032100680010040c800054003d0070080400d000c00b801001d00c04103940c40548a00c074002c0310045110007c0761003198110282d075052100d08280c07282982c1c02040141c5c0e0020403030306000d41c80544080745002502d0207030f14001003454815415400c0400210f403659040e80a441601c841480134082c3c0c81d00110302038134014060700c3c00707074004d0005c00004009080c0640250b800140264544100b00460606e9001f1500420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 311081223 1250 311079973 311080001
    0x10207052d06130e131a04050c06032518170c130b091b0a0e040e39030a0f0201021002040b04140303093012030421141309 54
    0x34401d0040758050700c04280d22003d4010504003002c3d046c0c0395185140c03950300c0c003441c4401d10320000500700b01040c880b00c5120000070300416240c0c2024001407150703940c1c621400c4280c819010201945030f1040c500c0001e1080d00c5030006244509114050034005d461004008c001c0c412049070313040c103840305c011001240d4005100000c4a030a004108081410040d1a9070701000c41c4203603191500b52070204072032010181e03003440140d80d000000414060000c08107821107500a0703010380f4403c10801c1050541001014204190554241c04d145003d01a296182905070713021010a0002802d102010070103607005004440c40c1002c880182c0090f43d10a0b003000341c03400c40c040f404121006d010412007505100c110055400c0550301f2001c2203004a180c0a265a007014030040b0543e408152941c008040f602941a150800c0c044074401c2d01d6a071068604a074003c280315042c0034040c41d003204101e00c0024541d10345101010b401d503505a03d030800100042c0d08202d40301d0016a203200741c407d64903000c03038070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 311082473 1250 311081223 311081257
    0xc03031903181a0411090702100b01030603170a090305030d02070c05040b0108070309081603021b0906010f1202131202241b010908030f0a0506010207052d06 69
    0x241a90b200342d0a40b60403034901c42140c00000d840c100a40c1203807210142d4100c566a89050038829001080c0300960000e1070b240501c48401d901041a8003840360541092081c418050011400c541c69440080c0c000a400844603222941200013040c3d4028140391040c5070980701d4561381c2c1140d00c01000401c166034001486010010509100c1000340b800320b90810071180c6450020703101d048020164400c25603101c140c001000203520589900c500d5160080c0d160580390b14020350342e0b00e00003000c1001d00c220a80d4070400d6141107030150344070380810383d2910000c0c810301d0382c00e45040307407103d540c164015002e106048506080e44444e8005220140102d04c0b80c0d5003d00500401104100d0850000f040401d2042035044c0e80104889070354021460001400c044941c0c494010054400001c101036000014007450f16240441503019024545040000751145401666a024a031040540254150101d03a00112611910071100c025841020089940d5500041c01560055002130703903030f80c0f00b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 311083723 1250 311082473 311082517
    0x141006090503010921140a0509040e031e0708070b0408030403110c0a061d04020301091e09050d0e240307020f01091703071b060609050a02030601080403030e0c0303 72
    0x300c140352200501c4150b0007000303c00003680f81c600c00111403091500241030440e22072045079210320616103240c03200404864888030007200052055100c046214826410600078400b80e050100c11649048040410900d0321103c0ea5212010380d0892481983c081609202c040c2c04a9030400c24544954440c1000c0d5a8a25040c07801034074070490220007190361750000d6405100c0d070b02c8017031101e0f054030000c2c02e0a250784451482c0101a107003990034003c0c0c105001000000d81da03d0301350841c4030b14440e0a0640e0303521600c081c0000003150100f0f0f00c0038000740d100b40403030300416004103030403c20020041c4c2880369584100301001030b070291020702d22071035410010030031410303a80c1031001003001d07406107000f030200c00459120510788807022101c8160b100030000101d00b403540518404c0302c11020a02c0c407010104210705141c0010032051240000c800e0901c40007503400c9455200301d80c420712050316140040d8655460403001022607101800291003501c03520a0695070410180001c00045182a903500174 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 311084973 1250 311083723 311083727
    0xc020d080a14073509010b0306090d120207050a11030f010e0604140304181a010c2001020705331303081c020a020607090608100e0a141006 61
    0x40010050903015290180c2103502e82e0840d02c950750000414501000a440b4020381007007203110322644511813007211800c5403210500c5071091449000480001c010802d400c4003031503200c80c030440d02c00c81c40c1c0e000b402e00d1000d40d50090309444a0141c507807400504100c120380d545842c0914544040d6503080c0030118040306460104940c40036030711000024070107403c0711202250343c2e040c00703840200241100d4410f5020035004201340c1c3d0050101700a100020003141c12100e0013410041800e460000d8489204142c039401481d511a26541c40364003d100e4404044181c030401c9051003c40303045014040000400ba0780b039821b80050300c5040381103005040c0c40100350022400303c0c9625030041e05024000c4083c9000c070120400c4c110380d0002d00081d611020354140c051800741c2c034025250454800300d0355401241d8001203040c8942c110351101083d00380c0354002503581d00400c65401342507a13461071060108100500c0c8460700311942c1d84012800059110611030b5515040b10705000e004102641001065 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 311086223 1250 311084973 311084987
    0xc0b09090a02040b0406080c1e0310150f0e030a060f0e06090105071e17040804230307121b1d01090219080613050f06040605010914150d0c020d 63
    0x340000a00b10b00c0d003460400f00060f44e0085105901c2882100c02c005220000e0820031940c24042d121043c0884c52840729590b100e6030820707030710000400d00c070400100c2ea141000c02240d40959081d1205011901e00010440d65080422080364250158104800001d1001d02404080303181c0c0c0741d00810135281c0c541c0d8140c60035100a200c1c010b168108800c2c06030558200c0300400e042c3c0d81c0a105001159901502601c001382d14022004070300c45450304103c00d100004015106840703111a5400c0d0782201c2640b00240b18180c058003d80c5a00000000c119007100c0c249400031b0a445244c0c040034107076000b401030f01403c540741d000065122001c14680842c820b401503140c007400740c000b41181000c56050040d0503103000ca17455a0107000d50782011481c240c0d03940d69020700050054405000f20f1400b03841052007200c05464507406a4244600400c07558003c10b52042503843d1203002d5104030396082c081101c0d40e420000c888512400410002078980e6150085001e801d5080c0c0003070002d0072035079000034024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 311087473 1250 311086223 311086231
    0x20c01081009090f170307030605042c07050607050d1b03050f181f02011d030d0b042403030807090320060c0106090e0613080a050a0306030c0b0909 65
    0x110149003004104540740c59000180c4410000003d035400540c580060781002011001e00010740850030600c4200c0c040000394414202540c00f17018030382c2d0740e02c281310989603442d004d410400c02c4114181c20040003043c0d10801020100110350704281d841b401300c2c041380d00818064613160001e042110f0b580d0303000402910145807031140e140c20086103450003009c60007101d20141c0c0c0f405000452500d808820114007030011001414a00181500c2005588048c542c0f21010091350074082e15509140d100c18248500f40c050318003031071501c1c00c8204080000d000c5404050780c0140c1da100c2c0b0320491814404840110841c4594080e80d1505505014000010007800300041141c04070f42400094411b105841503030070201c0313180d0160b101c003a0008100f400b0344100030300d840d031a11000080384001d6402519001d2003000c159031460f214101c2c1840d44050035034014103ca8003c101d001201d40c8a40c0007020826200d00e03000402c20b032640d80d40c0920715400c5e40108482c5078041901c0907d031420020761600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 311088723 1250 311087473 311087477
    0x12060f170d0f03021804050a1b03020306010e040e010e0d020a0b0108060c0a080a1d0304061103030915040c03021801080105180c040f02120705040303110c011b0204020c0708060106020c01 82
    0x4401a004070051005030865000300400d6000f190b10240c500010040b0907100070000e0081c8254680b69055800a20084d03903100804004200407001c0e442c000d1003228062041030b036032410340e1000c1d903061001a00f0b140c0c030316400d07542d0f0340c448401e80c0c05002c2c401c200e4000c250347c4c0034101801580c1001030001ca8182c02c585400e40022080c07104441e00e050460b0008082d0781400610781d613460745004d0081c00005118484003114007000750412501100600c1540c4050729800d105950203480c031aa2808100c0b040c2406602410761903025008071600164841c0c45500e030401c8040e02e81d400f180f032003207140c0841014038103410b005002000007030141c00d50040020400081d101000c0005070b42d5040c3c180315030760181ea550b1508419601864044648020010b550101c1504022200500951251105a00044829092521b102d10204010206a805039201ea031210301500b07412071035403a5142c1c120381c082e50822510702c040a041c043c84008010900103409250315240d070103803c0901140000781 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 311089973 1250 311088723 311088733
    0xb060109150203070b0c0d050709051003060e0103060e120c01021e0c0703080a0c140a02011b0c0b0904021c0b0307060201060b0d090c03021f1701120b0712060f17 71
    0x4456000007a181c03580e8000300e00b00300981b5440c1c00f1483c0c91041c0c4250414041c144010044104c3d08000301c07004413481a55074076940340e4a00f104030112901c60184cac43c2d0340842c401c010008100c00b600000c0750750300c0500070383e416140d0040c0450354590190550118603500424a60100700e217401142c030505074800041c1e49041803403002c1c05d13110640c50100602d00e190114048407018400c482ea040c0c1168441d410512590031414003e5581d180c4d030720103c1c00990001d0501c038860045e80d1040021562001c140391a1509013204044540c1190a02641050b402d01c041c402d514215805c00c2c0d41c0d00c0d8481000140d440c1003509043c10060207070000010342e1b04201c410082c00214100f2070314903074820100000d946c04107240070f10f406c0400d540041e40c05421940034003d404030343d14040c0e9428410340c44509885100d0640410400001d2244845224910002d10040340c0070074506a40f090841c034008070014074130318031042143c101e03400c1110703a40c007008002d21641d08032800980b004081c1100400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 311091223 1250 311089973 311090009
    0xf0e0105130911030703060207171903020702010216090504112d0f03030c061906060f0f0c0c09020409050606040f0b13090c030e0c0a0b2b0204030b060109 68
    0x203150120407814904501c1c0d59042c0541c280000c021480300440c4000307041c1e4003040d90781d0030408042c2d009060195214807413140750a003017010010172154889000a0501401c52058005030000d401c800c1050b07040d8000d885400710304104040d0f40101400035204006414141070030b1200458920b507903c4c1307000b480020a005c208031a0ba50702c140105051090b40c0006240d60700c04540c00410094019170103100c041014015178201150b0f0a01c100c16a001c041c40011030062454180c5010348504804110360041503160144659046c2d00002d4403410b107410310ba000f0395105101408241d100b82d00341079011a00780840340c40740c01403a822440813a89a81094248215080c8034402481040480e1800140c5ca000d0070f407000d040040101140390381000380c0074502c0400b030080d107603d80c400c55640c040c0000c1c00f10303286007204241d42610184a1414140948001d800364040e80c0076407206103003001702c1080217001420740001d0002d54455810038000c2d05080001400803100d81d040404040300b090108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 311092473 1250 311091223 311091229
    0x7121205151509040207050106231302090415091b030608070509250207210b060909070905041b08060f0a02070206040312080105130213051003060b030106090f0e0105 73
    0x100c40000003150000000c94911400b040c0c5403148185554016001203a00ca040c00010750060003101ca01034a00340180740d03211005d20035041c14000b800e9000b44c40a03074940d6402c1c0d143d4090604038001802c0010510401d58040c2020f802c035078000000c41d51501030448034000c86010301e400803141403c091040a00f00b006a41e120300c240d0280d02c1c081d905c08800101001549111640b80e02403103010300b42008040ea10003034540c100c601444203003103450511110050751440081d010300d5000580c1a1580d1944820002003480140031008a44291000466100610710400c0e004500c100c44c1c079000d1082081d08400280c4280d8072010391a0403440400120b01801c12010741d10441244005075203039a9840010f007a0302940e08007414103010120128191b80d0004103030303416200111007403070702254500356a01c142e02c103e0800010b004082e120404c103e081c05030a18928160504001c15002e0300c5052074802070300242d000c940000c2c0300010401c80f03240f0740d5694801405400c1681c0782150706081c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 311093723 1250 311092473 311092501
    0xf090a20070305090f0303120a0b090112020d0308070509030f0f011805070909030c0803010b0c16081b03070905071e08071706040608010218031005010501020715120207121205 77
    0x1040c045c000004c01034a1079030f810b004540490340c0c90042e848150800729403041c0240100300c4031a00031958440085042c2c6040c0701500c040c164020040313484c0e401c0b1954125020309024100c102480010f00030844290741c14411810762410705402400c552603170f0201c440c07c1d58244155490040041118040410b4000c2004001e4400031070010440150b50f00e421244841d90480c00343c500003000c000410400020781c02130003030b032803c0c00440f90a046a800d09007002201442414615408030000c4105050b04d480b00c04e4114400409807100390b0364600c0d280d400d0703800031120b10300000d20217265040c882c11400d12042450440e4904282d00345400540604540410308111242c4848000014150b5981d50011005026060b00a41d00c462040e0700d0800f2820800f031000303203e80101c982c074841d0000a0f104047c102da005034000c03d695450702c0080780d0940c4c000c440e440c040042c54903030002d05801c14001816500e100c1c861110501401c10001000c07403040b062501c10403030800c01404009041996 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 311094973 1250 311093723 311093737
    0x80a0e10120522230106030f030815100f030209040203090708160f050d0f02030f1e0a150b031e0d17070f0e03070806040b01030b0c0f0f07020f090a20070305 69
    0xc80c0d41c16070810340b100761302d0784c400302c201d0100c03070340c20620b012080143e00255400ca0511036284c0e0340d001d0302e522035030704100300c518040c0b25000b406030305600b18030034803400705136424406070f0a00624241c10640804c0c1640d0007151f003512141d01c4060300304000e40d01004015040d41c1d0407840c0034181801c0000000340c048091240d184213044210110040c045071149a207a05c80e4000c0880c2c0605641c20f900380c0d214406000c2c84290f0040701000c41c0407000000c05c1000d142c6038420718008142ea5423501d203800400b80c001c07510f5094443c9082d000212500d0080382219100050f008003403810901000034200e00d200e40c00c50070071500090920011179000b20100d05940c03420700304907804803080c20103c2d291040c20f502c5101c5602c10350f0140802c1c015480d44240c1a24011038124095503a02c3c051108035104854600820034010402c80249056090140400c640b0003419140821070580000340401d5060312035034201540c03404101d4004007403080298010703100e000f207035040002e10f44000c0d015008180e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 311096223 1250 311094973 311094983
    0x20706050a02070e100503010507083c1e0901050f0a06030b07200d09090e07050901231201020306130b030a0f0614040f050f0601050607080a0e10120522 67
    0x1300200c2e404000350b200000c060070000d00208042d140041008204040680d5024810480c940d84602e04c0c4000ba9200c4000300c202c084107100824820303440f12041c2000814018162010301090103160558104083c040c64450700040351300e040120454501e88400360040340250f24050040001500101e1074584c41540ca06040100440d81064040310f040804010701c041e024031625481c8030382d040b00d008002d641310b50034200061035040c05103a60742c4d64603003d140d0b841001e1000400450004001e90000c6621517828079108500301000b051035004044000306260b5004070401015062920321004505c413005418880c84492002282d202c2d440250007501c50509091240103000c40c13500051502c896a02025100c2e15040c1499102403d07448411500c9003d050f804441600001503014142c50000b415240f0380784c0983d50713100c0554810031183d420300c0038103000c007151036a8510b80c614010005803110180340104a510034201d8070007c02c07030109004013020800103660002e4006c9600ca6004c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 311097473 1250 311096223 311096249
    0xc09030b010308031f06030e06060a080c1201090b01094701051b07030b01060314060d0201030906151811070b070c08040612050903070f06020d06030b1006020706050a0207 75
    0xa500c02180da143c22010a09001d4040c5d000000e40c0742c4c0c140d2040b88015488030a40f28075454640402840c5021482a2030180d44100505440742c5060345291442081c4c20000048484417031b6510055440d09078401c3e401c00356502801245104940480c41009015042c01017688000d00040ca0300fa4441100d0500501c00f852a81c0020b80d0007001220301002c03040104040e040a0a14015640c3c0c0302c6010032240386410400000d560340c068003070a00f55401c01c543d000c03c0380d81c40700d0034441c01403810a02a0b0415881340b0300c03100482e10611030058121700645c0d8a011803420041002a03070414030000e5003030b05151092078144158a14107036100c40360300030403945080c2c4990380102c074a041c00790000f4103000c400040008045070450440002c070801e002d024030903940c1e42215030fa281e0044210240440d000301c003041000070182c1d8010a003c0340752002c0014659140c2d05c480c0b40d48041141c04200f00c0d9041a0700b84600750301044104014041407403d2407425040c880700035140c8815100e50340281540c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 311098723 1250 311097473 311097481
    0x918060b01030204170106051807090e06040906150303090b090a0e060a2106060e0f16050c0109050106140609010504090911040207060c11060c270d080304060c09030b01030803 77
    0x100750100e800074a52143c401c0300d540d24800c030440c001c03e054424144240c2c099400140031400100a0f50301c035138452f45680c09039900d03007070501e44602c1c030081c0480d6100303958038403d4000a20038030442180c29200102020810700b113203000b4003103114640101d161311405100a120a5072110900f0301174481508800c250b44c0c445401080e5100590b4118800c1003100c04c0060580e4420354284080b01401507400344400f5031740f030500c0c40d05150b007940c08405a008072000102485500d5032031009039896440e14503d400fa40b40001421902540b06c1100d4a944a00e400c100e18141419801c4448804603600392030080c00d2000a0102e100318895203c0c0e590726881c2c8641413056110103400a40000341c02595900c00305c0c03074518005d182000d446404600c0341c0c00f887c0120440050070754410444000220701c0c201c1c200301180018550f800001810f0a0041d00c480c8403515200300f5440c4040c42510304584905103490020162100b0001d16000c003e1048030030404144410421070449401c8052150369442d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 311099973 1250 311098723 311098727
    0x807120f1218051801050409050a0c0f0f140d12030204030804140405070e0102060705160c06091503020c030d050601020312040c08070b070f031110090602040f0918060b01 75
    0x804203001510031148500c541d022141c0041480c01804030000080d102262200100400c1031260001011400c420344011702c4241400e5100c0c00049000b08102c402c030500b10b90b1040e2601c0c6168110310303020800d00d80c0402103040c0c1114804054a01c0d84010b00c0c01526000100780691007952000d0b0940343c0c01c5c84184083c6001c4c1d4102c070003641c0c0222840d035170345d6160100c034503015081881c0c603409149444005070300c8511907038519400240581c090a1503869600040392a034000c111001a100440680b0707000060b84040c41c803000b030000383c5855090f24944071848401e00a44030108090500410055810000110489440310301c1203c00107500d859510040780785000b1034590300ca60031604020320050001e101b2865044440400450300c00700c0c0c4800a1034054080c0038401042000c0c080b81100000c1d000e107514a8108a01c0d004a81403c2d40460500d001e544c40c0802c21f0b03610030350000781402400f88a082c440003800d00000140045444007031661280e16411901600c3c82d5a950203420140c2c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 311101223 1250 311099973 311099993
    0x1e090f290c1c0905060408250609020f010f05030103030f030f0507021c0201061404020c0f0a151d0a1104150608160801030c140d06020406020109050c0406080712 71
    0x5565206004014035161510107026404003190880c107490342d04804003281500d000310400c0a9100002c0c2005480c0c55840c855140c2000e500d070742d0b16940702200c0c0000c0510044105259501607040442c03005130038014855807240c0c00846a0401c00d10702440041c941e044004c032030441c2da00d483c3c012010040702c01c08500070048145003022180c1400d00b40003401da800a040c041d4901d0700a01d0344040c04a42d00103a0881e1014482c8070074124920090403010700d025406010300600170401e071400c642c08070000c031f42050482c01040b9001000311030340c4040210f40344035840c0b02c48145d05c0c0c42440700020100300350703403444039150041420f40c804207407404a4650f03400c07081c00c03140d080ea0800c54007900d0f900041c04048044480c0701c2d00c1d00142c12994521449481c0c1e490482c0c0d004480343c2c90060402d0701c044076000c0e414004980045030915408001406031004000804143e0300003d68040301746009410414660541c502c1141454001e001080c000f0030520111111b074014240840c1e001d151040400e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 311102473 1250 311101223 311101283
    0xb0c040302120d02010f20180307030f14060403080408070201020a120908060609060d080c0106050904080408010c020c030613020d02090c031009060e0103020105030a09020a0602011e090f 82
    0x25a4800481c1044400082c00c1c2011010f20b40003840441c40c1814090210389000c10618180300804400d8a040400c60004103011070040598030700020208010919160341a4400c40d10a01e1641c01031050081800d100d640c94016000a0700140c20702d07440040400b1405407001e0000e0800082503400c580c02007082d100f1080d400b08905905103011100682045007901c0781c00071a00a0400180070392602050103440358000500e84208601c4945440c000c1d07412414009244e99a240c00c041250703902c0c1c8030641d2183d40b00301c000c6583c1c0c50420840b54290b681511040041d94032030407900e401030b0380205c0c01d00e5200081e040d65555040e03007030001505a00800b04007940108190080c008154528002184a010182031404405645144200c2104d030544a8000c1e0142034400510056126000464100e5036000000c14012081c0d000a00c5011b07043c1d1010b00541c2d940c2540007043c0d007004140040f5100d140d0070400c034a10b0f580c0c40d40282c01604e0b00c1c00078803240d00700c8990042c08110f03162035990707 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 311103723 1250 311102473 311102479
    0x3030919030f05030a09060e06061201060b190908030c01020a1205042f06030c0d050108060c030a1a0414010e010512070b07061d0a1122050402010504150201020d0501080307020603040b0c040302 85
    0x14414600c08e406403581e1054510710f009400c1850910b09000e81400740d0700484850f1075500b4a4540e1400240f01e2640c01e038090b039020000c2e407040c00100380034100040c1010700100000140e66030454240601155013032984002914104020480031841141c60082c1d8003150050b1020548140001c442511419291282c1d200e007002c0107001602c1e140501800e07500303d2400c0f0800c6180d80310203049a44420850b80c071504a075041000844841c10303508010034003c50304800b800700c2c1d1f40300c00024050300e1a207a0400d103000c509000402c074104404400600400007594441105c85108002c16140c1c0c0a90041d41020a0f0005400040203d40e0780308a460400da10f14042d105210303500d9003a01d9500801d41510500c0c81803070740c002c00b8035024544021480030f80920802d0345020380c0501014040040080c0d060050a210000360000c440e1050181d010303032680010303a2030b01c00c5000141107400680040406030300510209005888404c00c03240c00c1508001d400c01d05030b031413000700641c3d4440c980000b50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 311104973 1250 311103723 311103731
    0x6120b01091509050906010c0503250209280510031407050a0e04140d09270c11160303080f042906040b04050907050f010c05060903030919030f05030a0906 68
    0x1034480d500103d540150391085078284115103c2400460301000c06007000760142e0801c010303001c00c000c0c541c04079129a440c03205064401c03003259000200038840071038046a10040440700b1007a000401682d8038030303031140560100403604001c98040c80c0c059060000804068503813100403000d80d001c000c12401000024805440349890380c40001c0044803c0e50704561a008040c086c405504001c580d4070f61000300ca0b6580302c0082c0c940ba884071414003000350821052003225003104040500d5000b45214907040361144c5d0000451b58415038904003440c0e2030042c205070040414000680d1240340c80f03800000b001c50a40e80c0742c0380c504081c4000203080a5841405051041e070501d4040c3e256481442104c0444040100305254000c2c801600e02c00c90b90a10b454010000130320040c541101c08615203001031400107082180c5503100c1c2d20300881034942d0000c0703134000300070000304030030070003c103e00b8208540b1b10b08a4036100b5a070140200c07001421502c24014040005610b0203e6544281d04c15500094184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 311106223 1250 311104973 311105009
    0x70215190e1c020f0601050609090403050c0d02010e0c0909060c13081603030f0e0a030303050a0e19110111100207030509030a0c0f050303090d0210020c03060f070201050a050106120b0109 82
    0x14120200241c40144c041c1c800741560706000410340c80c6c122174016000e689002c2d10542003221409000708124140007050120200c241c208004000403410140c000140c00d012040c42c05150400303101d10740d441200c3d074404000c400c40c00850420340049030400c02985130141c42000740f109103995006a03441d8850040180c80c04410000a04c041707900a46580c0c0e04206d11280407250000400c1106822004522080000038030a50100da84101c4e006c100007601310000782d0440c14022180003103240340100d1a039003020300101c0d120b46100c64200b400c044419041070113602d500c0700001600100c08a034081001002e05001e0800c580e203814004040e81d601041c82d180c45910740e940c0e400791210210391050085124180002110700110005224015020300d507805c02003043c440c498108110b001c1c5407025041c3d0781702044001d00070002680120014585408000d08540000708081c00e03180c00c0c1001000843d40015550713802e030f0200480030542600e10030041e21110f009502c45440504518540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 311107473 1250 311106223 311106253
    0x70204020d0b2815020d0e030c130504020a05010203160609020105041512290d060b0a150e0603060d12090315020703030f0c02282108070215190e 64
    0x105030341d08040c410407521581c4940300c000610484c2d16103500960300c4040322412460080304100d40590000342140c450705961400f10381d0002c0c03030140d1031502a40342c500380001c43c50310380f0054019083c00e200442c2001200403002c01c1c1da80142c5400b914084d81c2c4e04524055910038400c942c0a0100c00759440c0b21000c5007140244101c08212420a41d28605070010000c21701e0102040f098074241c4000c80045106ca604004140380050000c0702c0341695051808400e49990f1113000040030259031800d14180540380c05404900d000000320300c501410820400d0350350b1030501584110740c00903003c01c00b02c6100c01003920b403108141c00c05460014958031801c09003c1030740040801b24825a001d1200042c003480500a8031101240503000d44c204900200240049040c501c00c000c0c0002d4400a00022035120040307a07007818500e50641081c0f4000b4400029007102c50513070000b0071071006050b8203100c40c80b400ca8036440500b43d83c0110800000205201980c0c3c0c1041c0412145a0b040d0345402c0ea0389030071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 311108723 1250 311107473 311107519
    0xd0203070503150a0f090c12152d03030e010e03010510170f030909100f0603020717210a09170c06160804060f111206030c060708070204020d0b 63
    0x107003580346507800016000e54104214001e0443e00c070143e201c0145802e0401d81b001809441c0300c0340b0204459140c480100601c9400380894949000500e10300142c20b04c103180f60051030750080d05140d1951100b2001885085c29050b808598051500c06440e000104c0121280c0b0089540315500d9800c1006004400503140d401c1c0b01255503139804424925084100030351a80101401c0030f0300c5800c140300f49140341c18041c042941c09241c1e80c20712400d980d210030340401910703403540224000030360104012003041103440e00c402c80e9800d10b207070590400750700182080725800701d0200c0081c085504e501084034004250482d4401941c0940d180d5205607040d95804015008400002400c0c8101000310f4849541760b07155080301107441d505c200c0e0380e59403516400083c00c10502c0d940daa6a036558000d04e00e500c3d10502400e02403000844110b41403c00404061802030000c860620894040242100041c80c0c40d04680000d641554056240c01019004100500820107403603003040303445241c1d902510303617180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 311109973 1250 311108723 311108731
    0xd02210d081302090105040e07030f03031a0d0b07031d0d03090210090503070b0a051b0c0f1c02040e010b0301050f1008010b0f131104090e0c1009030b070201020d0203070503 76
    0x75403403186a4031203404007519244803070b0180d0403280040040c00f160038903800003c0058401c03c12076220583c3c0756503440d8400c0c802c00050b0000303591114100d50700004054034112038502101c3e0381421385413070303147d0500440c40070704040c05141c0d0b9074209044940c40c907803501c08020704500030f0b0b84101408280243c041c2031800000c038424074012020110a50140210409550b400741c000c00c1c0c0c0c031741083d002c800c4aa07c4001c854003405414015484480c020840d80070303581c0440d4002e40520380003030051146420b92000c040d4813810011150010028400301c011140d41d40444004c182a641001c400b4010b1449140a0307070154201400c0000900c24403101c2c0707000301500d44c00080c6117565024814205c401c4200fa082d0710940d1105429880e2506056158040000d040002004030b11903a485000394030503070100364000d8a90031a014100c1c1d05210030300d40b2801c241e0722200303a0070b20840000e116100c24000200102496800328015500c02d41c10b488101108010465980c10600b0001d0b1a42d04100c0e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 311111223 1250 311109973 311109977
    0x3011508010f090b0f1504060609081c0206150f0907020d09082e0e0114010501090b040f09020a170f0a05060f18070309050a0803160219020d02210d 65
    0x841902c84000501c503000c03109801070150710031600ea03000381115103240645820301c0c04000003403920047e600c0d40300c0c040060805441d007160309458813420306d081411403074040c00400044c190010f025500465640d50055440481c9103424907a880000c04115220403525004043c0c0010441c4803030300001c000b58004610784590a101d50ba0764030309a5180c0310422610100c0b541d420101d0b4181503d58040350508181c45000702d8030074000140c0600b15900205034001c0300050400401c400d503046031151340580b1408498500e061b0415040c40707652030b01c074815240907540c00158412100c0c8a07068110640000300b81e5107500d410410040c2c442d140054441054a9241001040c1545030551002e604020064000c00b00091101d2001140c110018241b20506440d042e807100010014028040d40302c2c860b0000360b40701e061041b8182c00e4000b2014917581075610490000110184401558204560441d40713444100b82c50f00c00305420401003030800402e40c00009001d8050030010407180105c0c4619 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 311112473 1250 311111223 311111231
    0x40501050105120706090302010e060c0307120e0604052407080409050108010c030e100b0f0409050f160602060406020d02040902030108030a080a020a05070803090102160c060e10141303020301150801 87
    0x4030b04986900c0c4d2031050201040c8103003002c00040d4020019440044001004281800a20303211075040d90703c0740c4000c442440301d00c40a9145a500080c080501400236107089042606220100c3c07150305201208448141400d80c6000311501600106e039415903204c0c0300710380c9444c0e80f0800400605001c0c05040c1655007088032405005210740301307201d071034200400180b010201c009543d90041c03141c400642e821001803241e074101e130f880754016290304920a50080c50380c13003840707001c040c1003144455001110003030b0720604103d882d60004016401640000006030313101920220780c8001c0c0701703550115915500200001650810100281001c0c0000740c42c0c885843d42c484246800720300c2000840804603074180841c3c408140d0727540c041c6034401c615200041c0b6241c0141b51883d055038601c80b0807505002e00460920413540d1054040403208016030b0020010094001e02030310409107a00c2400c0741c2d140205101030716005101040d0300540d0050b000704561510508110034000060249841940c20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 311113723 1250 311112473 311112499
    0x80f13140f010e150a2a0e090c04140301020f0702091503120d0f05090712060603060203150307090507020d030c021e010c030e0a1109060307180207060b01080603071509080303040501050105 83
    0x54011030b00b10061401c114002c495008440c034048030040d954035010001fa5120008440d01c031448c045018800304402a0b4483d4580814990204505090030340241d0040c4052101100800c0a0300e01080c0e0445200a0580e2112043c542a444c003d02c2e036a4540320742900c08050008480c02072480e45440c4a051181c15050103444094490541d01c600d10303076010040070000102194141c0c141980f088034041592a5261205c1d402c0e070300705403a903200854100c0400016450304000c10f00041100540510aa02c0d0803d006500d5040c52203e0720203141e01c0701d07002c81100c2d2090040d0a4416030312004542000190b0b0f07450ba00905c0551108408603103806600d14000c0400582c14110036840700e40704400c50140303820310203501006448241c0500c90740101103003803e41d8641004141c5c942810060f00c1c0c1002d400e013981500c4402031040d040c88841418400711351070100d449416550950500411a00140320484030480c40381d000c1c0b109400b020040c44200401900094101d540485450f07003480c1d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 311114973 1250 311113723 311113741
    0x60203070806030d02070b0c0102040b03010b04080d0c03050f090406030f060c11070b090d03110a1416060519210e0d02160e090a020d030807080f13140f010e15 70
    0x110130300510015038000d41e4104007e400510050408610001c009801c0640d5900010119002038102001c0c09001180078040000c08200400e0703441c02031300e440344001c0740540700908240b04130301c081c25108800107000318154489030003d20046078040026065040c141c01c11400419007074068400180c0c42ca02070348421100000c1413002d0b0741c100d110b01c3e0300d4580b01c10300308041c9400301c0c4011000e101c6c99105c170201540060201d201703000e000300d50400704000710b24040c0d8108080d59075000b800200464041c01125889010341d84032884014030561015407104095030103c8000542c0343c84c40401422035083c0342516048255407910322001c0307800742c3c801d110f401d0b6152184031254417026104414200500380c000c890341504104200280c421007580e80d008100c2d902d41e035140a0b40030400c100207004001b94000340c5982d10060f103500707021003030500d01440707401003c03161009040300e07081e049018201582401200c1d18020408000c022841d81011216150f82031a001414509079500000300d03045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 311116223 1250 311114973 311114983
    0x1217030105060901111903050304060606021506010f03140703090c05040c1e0c081b0c010c080f2224020d02060a05040503120a0501050f060702060f0913060306020307080603 76
    0x540c0101190f04001c0707580011035644064030203080c1e00380706e1750081038800d2010807034019541c0e003c2da41d07040c2c1e41c1c81c0509000c0241c0d00190310402c219844000101422140301e503250350024003d21308400403404a100c124050458820340d404500c81a80c00d002d00c842c0c00d1303401506200c0c4903e212031143d0f42e8600401048444110060005c12142c031341404a04004ca0b8216044106509003018404015160401b840d00150904142c0d48003814412000b50803c20401c00c1002091800001c0b00703166942e8502c1901410100d44074000001ca0b1009100d20107984801c000c894a160440034240da03528440880300c0030b01540e240090b40c1c2c21485110701d1010400c4c908041c070503002815580c4070f100c2d0000080500a1080c2d030f4600081c0b00c0c5281180341c510744103001d000032031400b00d1a07506090400c0710440380d4810341440361400b00407110040c0c9401043c3c1d010590310411032078540c2909004560312031580000e00522510b40300300481044044d501544c090181a134031080300b980c4102c1415521 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 311117473 1250 311116223 311116229
    0x1103180703080d02130807080c0103050108010515120708013905120406020f0c0a0b071b110a031403040305010507091206050a1508010506090c0307051e040302060412170301 76
    0x2c10801c80f140340c0d03110540080c49240c005017050891700b540da0a586040c0041e6420210035a0800305428019680c140145405489040c00801c007904283d1803c1c0703c0ca40010500c5070007441c0024104011300fa040c403070f94006003040002484003140500708151021102c0c80420402010307604121081c9002182c1031091800d60384070a0f1030010300c049540840000104100c80c070a8080240741400c0c2095800342010050000c001c007104001c80c6000142050010035035410408104480464028180641302ca0b6a402c4103801d43c09120b00808198039540030b800140841c21084220100c80340001300410480340900007c20550b1561b0344219041c2001d4810f802d155900d502a003000b048080c1d000641004000d04005502004030301088000d000310f900c09031590755584108051800c0c440b8060b503200380409001491441c0c05240500325000f15180301c04c6809038500d0840307102140004840107560003c00d86500c4036a0303900b0124450503180402c4900c810200064405c401c0a83e003540d0503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 311118723 1250 311117473 311117483
    0x809130e0d0e0402040b04060804150c020d110f060108100b0103020f040b0306011205090309011101050c070f03140d0209100903020319020a050a08070302031203010e060904050109061103180703 85
    0x441c0c0407114045944580c0280080da00641c204400220a01c141700208010a1261513400307541c5403904200007010001100070001c2c60030100a60080b90780030417044030035011070401c1d102c1488002c0070f00f8074001c610b450000451003084000b0480f04400104808a134071410002c1c00000b0040340114164010503010390140c1b41d0071b0109100b00b041d048041c581c002010f1406070320304604c5020090650f04c00303691000b030f250000990f0914550740014140d100c000c05000900803401d0102c060046882140001383c10f50643d540c40c4c43c10544103c088207904041441200c0d00d40e40b8206690000f940204485849642072007102c41e08036010303c9026044a80040141030725171040d445071004d91032114812a842070111001041c02c0d62000d41c04405880e500004001c210b080d03205251801001d613aa040a10030103000401c41030005080c0103030300c22002c0d0384002031511245020b41c050006800010855130138110b4111920084001a520444004c0041c00500603e81003c03615680c01e400701801c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 311119973 1250 311118723 311118733
    0x30301091b0f120203041e03050a0905010e062d181c0203120306010e04060902090102070506120105100525030e060a02060a0209191202040b09191113030809130e 71
    0x800a0f40c00d5000d19407080c00703864080f03c11000710011400c0b040c5184030480109a01040c8400110380c000e11080c00b9080c2070902c11825260b210015105015481c910b09500422904007000a59044058900343c0003c8000680f12115082c40480900040015038040c40460030480901d00079282c0790710715203070050040c02140c00203141c00d4400d9403000b4003850512480d0018810251030704d01c1898020720340c001005889030701c50b200090624920390300c0360740324034028028003070704401c1c059800e81183c40c111001501d43d0b1110805513964041c080488801e039104141d100d504440410049131424031079511304407604103100400146004c1c602903040103034415000503400403095801080316000007081c10a10400360b0031000581102a0000403d0b5290b180300c3e5030440c00c150040760a24181220194500d01c1c00b41c103243c2e02e406048440102407910f034000c080144480608a46800000c5000380d0b401d69140c0c1000e0b4801d603c803500480c0100310a14416854600354030403a0400711900014107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 311121223 1250 311119973 311119997
    0x306030210031a031518010e120a0905090f070e03030a0e0d0809040c0203041e03031205070e0306070e01112d2b0e090910020c0708030301091b0f 64
    0x2c0c0200700144a000036020b0024041c0120303130741000740c03015144e4804441941890242581c1d441c1100b8000424281d0b81440e000020b074075808265200c80000c1c01802c240c94551441d400c44407600f26034044c1d41c00814900622124581454141d44998040d489103907041c41c0318001e15541c1d1003040005000a4400d00103144246400400203188078010082a0700349101c4000080c00c80303403a1a03c00000d40e20014080142d0480043c200b407100300008114064038cc5540c6001d080c040602101100d8947c4e030344000340b9003d00502a031f204005c0050304071445071400080103040d851000384244d020424000c034050100c0d00000d900805101c00a14100c3c55a188000c40c0402900c64005420035016000041820030100c0d00f0350040c101061000341080c85c102880a803c90300b850203224010100441042090306000600f404107664865005a840074000d44544c00c040c4070307801840c100e000000002401d050190004458019003000d5841700c40260802511072061040707441e4003182406a1030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 311122473 1250 311121223 311121227
    0x804020f0f03030706151715010b0307180306150509040807080307110312040215190503090c091009051311100c0f12031b0912110a030f02040c0306030210 68
    0x2060031040203003c0341e052002d035039160801e039141c03e498944451a200000c028003c1c810b00701d01c03620010301d400740031044400d5145000403441402110b04051b030001c04203003400c1c40750483c0c41040c168001c6442d105520380c9020400f0b440c641c4034292491641c800041030b01c3c908105003d00440c0d02c031400d2894000d90fa03960003542d0704010031340c01c1403200700304140010b90004c1c8020480c00c041070740d0b48005072415104100d0054000000c2d41402c00f030600c26000d8100700490301c00311002960070026166a20b084041d131500e041c01213465004040c070010700c03402c00d01182008043c3c5818101c00e01c019914140340400358038014a0160200c100090648498184610451b0421100c1d207031040240341130b6210050095071100c011200f58510b40e00d0060400c1e070512525084003800f4184154000007030301c001b0036149650245110300e03402c40f243c40081040518100e980f0310006040b041001e9540d0a20600c41c01f20814260700450808031103a0b201880b030321030003041c0c0c0c0e8018681007440080700d0301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 311123723 1250 311122473 311122489
    0x30605060412080f03010806100b0c2116110a0504021606050c04090903050702090709150e0315090f0c030102120a020c0705120337260406020a030c0804020f 69
    0x180d80001040001c0c141e40a9013034025406001914010002c5050a5020b4022010303541d0100102901c1407201c008919400b1403010400311035000c4c03040310b10404d00300c010080d00c07551049a06400c403108441d810404071041d0190990003c0b6180f000640c0d40c6c10a21081c0e205034403035048020f5030440000700050a0364803850700101209207103801c19454401003012900000000e0700400c002040300b00c21032a002d44190b600c0002450040800e030320340070801c040003030140c80240500c0050010918291020401c2c040d0741e0b0740380740740503c3e542007404204e600c501e1700b07440d140407500811007a4845c0e030405000702d070010150308403410718503568014208025005850850804c3c00f54010011780c50356000e1a40001d52007600c0516603918900440d040d20015a4801c4040d0f4611241844001c0305480c403584001282c0b0b090071f2100072442c1194809440da000b1030781c091007241c002808144685640a081d80350034a071420002d424280805454200d02181e000f58000000042c00000d400c00c080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 311124973 1250 311123723 311123759
    0x3606120b0601021005090f301e1201082406120114010303081609031703060303160b1801060321050403060e0a0b0106081026030d05041b0806070806010e060c1006060306050604 77
    0x80c001407640c6264027500c1503944a00605e08811140500501c03424405001d90301c20090a450b403d20b50f81110840c401d00c0300c03401800244512070904104c80d88100c20340042520080c1030b00410072540e168580a400680203903025001d120030790701c01c0d003c0d4a01905000007902d401015100b13800f50751800c98201944014941d903014002071018403102040440000341e001c0c07161503400c0c0149020302c48209a80c800e01e100e00842c0c0c0c10001c040000c5401e081166000203901c004c40d04003688001d60590300c611699200600c10303440c0c0710001c000c46502098154455200c1d10a45501d666510000c440b000010b40d204102d00c24144c4082007458404000842d00c41d04c1196101044141150903500b980c11800d44000c11a4032001000300700301608014580c1c1d406d011030002c00306818110005c0c0e88a80041822050054010200d00c107680190000c080440001b4100d66075084e480030b6861321000303440d00c11588941400e0300410311500034029a8241c410180a041c28246000c1641e900d626040c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 311126223 1250 311124973 311124997
    0xf1e090405091c0e06030a0906150815070e010206150301110f040f050307080712020315070302071a0603150c043606120b0601021005090f30 62
    0x11456096495901440c0d101c1d10351400540307456198555001050072407003800c03200300011000902c4032070703131004140c035000702016000184503e8546850f20003000c0c11800b5a070510300705040003440180003e601c1d94108081c2000381500d482e011340561700741c40d9294045026230403042c0060b681c0c5044420407516400010f002285030740c4071185614684d807010808a00316440001d05021841819003040001c0c5401c0d801000d505140c8260700351a081d503030007640004030804210400b5554200300ea142d0751a0213a003d10f40c0c0341450f10004d8002c0d07014040c1103454041007490000c0c0902e401c003859100c0c1201070064150840c000b2600c1c80e0f00c040082111502c54818040800c040b403540940070290000c004240200760782c000c155040000d045c0400c81340142c2090014095030700b1100300d9861007680070582e08030300e46542d40140e0070710820030032503000a03144c074081000900c0009803c1100018800c241ea0001c596002c1f0b0304241703002d5495a81c20010035911a00000020382c00400800401c0c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 311127473 1250 311126223 311126227
    0x614220b0406080d0e06030907120305040b0d0507120b130207051c050a1206050109090c030b040c08270a0201080402150307020d080c191b02060c070f0b0f1e 69
    0x2580c00501180c4a54118000c00d078046000d01c40415040b9002c0e581501003220002c0c194680240400c0e9542407901500c00c3e41086406101c0406024106542c00ba01c96001040d07212605103c0020083c02c040714a01c00148034590881703541e00c2d481c426000c00b01805041c4103003241004a80b440030390f102000440b5144500c101c80e1040c0f40000c1036147c50340500c0d5450664484406200504030b1800780500e0480d10719084040000360380100310481124000e1102298250b1514810b80c0104200d40c003075504241007406003c141c03517014140c00d2080d182440c1c164060190311400711004504050030780c1003644051090b002560260414580c864402020241d48140800054079103420540d02c250160b440603003e5800305410003282680f0a0191890b41d00b4442c4000819100b0f4030004400c030b0030b000607680d40c02e43e000440b102c2d0780b250715000380884e6660240c0081456445e00d42d40b0424034201d01c04d80e400701d180101401100d440044154500f420612004c03c4220390b21815000c2460042007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 311128723 1250 311127473 311127491
    0x30c0809011101090b061206130b060109090e0703061a0108180f12120f06010804030c050f1213081906020a030f0e0f0d0503010510110307080c10061422 67
    0x200f4000c01300510300c43c0583e50801d081c031030b0034425058603030000a08550403000c104421100041e000250840d0420301c0d6606540b81c15005840d0403590ba004240c6040c00e05102004481c0700141c46000c481c03080c40c0421400440442d10240c10245a0100d070000b011000070840c0c51843c000b844203120b0100c0c040d1a64a00801001031405036aa04500c000c5040807c45410803904651482d52040343c40418510500d45140028031411000b08001d007802010b4010780f043c060100114065504102c08032865001c01d0072404106400c031a400580d003502c0300c42d01003007500002c0b840b003102188041414882400a54a0f403010f034002a4081c81015a1483c1c104040038003070040c075602a001401800c10140c00320902420515941c00ea43c051200400041051b42c503000b18a0000241501d03109403641001c4941a045d403203030060141c1182c2e008900800c104a0100c0e9840410b181e403001049010341d155131380b800d041780c403a00203540541d500080c1500303641840d0315014141580344000942c142c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 311129973 1250 311128723 311128757
    0x402030a180b010e01090603030f0305090c030708100e010b01020c1210050103060209040e0703020f2803060509060a0e03071101170a0629030a090c0f030b0a0612030c080901 76
    0x501c011064818420340c500402105500702429409446075402c00d1041c281161805840d030455404072508050340d80002404850701170000b5034440c600102914800c03607403200f1055980d410020480003030743c58040b070300800403414458149200010f8014100c010401c40820451240051011069014159005124125610405002e54030603d0016140e5050406200866959a0f1074440c1684528070501c00b607540c0e003070008411041110742c65541000540d0003c1000783c03202092100010b41c5002008020058010a02c121007410440704180d5501000100b42c4400d2a012240781d081000401c5c00300d0500041900c141d641030600480e06015040c44078002c2d03400301d45d803c040554401c02405400911081510b01d424041000d100c824100b02012a4520001d00f180c0d000ca40d8607201501080b036a125a00010054038030b545440594900717020301110001c40d6030309845490581c011031039181c0322000da60007680550300c41c04c4000d410742e560b01242e07209034011414441c00052130b4401407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 311131223 1250 311129973 311130011
    0x1205040b16061a030a0605130605010b0702040509160603020f1b070302010807050901080606090a0302030a03050901030c140a0f03060f170c1f0f0509040603142a0402030a 75
    0x4a40801d0030310403404904014040758058031950000c050380001c1142103580c001801350020750485070000302d0b912448002c000085403044c0042159007494000594070701960060315a141c0280e174140320700d9030340d00001500c400390790003145407081c03200c41c0c00d0044601c6035025050043c0901e5540c0d10709640b16034005102c181e141140c84a0780e00205080c421560300c08000d40d007200d41c508103113082c0458540060104030703004000c140101c10110390f041459031102c000318011600501642c400ba404c81c117004103660701a01c00580480d00780b079548840c580c803c00e043d40101c0e000c1507510b420100c07a5207040b43c54056a982c0035040548500004ca1090380e680c01c1d00004000c00c51090b0707a20403060304647d04040704134480d41d108502c00f054000000c0822261044038401d60728040c4100404001c050300c4501034503100d90f0700b041c5070403800300412203049500c10241d6032050442d54295003000c9900303082d94802e40400520b2807100b5920078075041980207560001d40071100440c0c00f21958103000515 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 311132473 1250 311131223 311131237
    0x50f061b0c0915150c0a0201111926030f0c0307110303190f06051008190203100e13031d0105070611120114011e030912050d0b030114041205040b 64
    0x10408403040c0074001d2a11254184041c4c0d50011110309003903204050a0700c1e081d100001905010501034840c01c080c2003030100300b0641c0107580010041d41031030b0418585480c44162490106440640402c03460410007003171340d1040302c00b07801c42800f81d0341e036082c0750000da040a8070b140b040c050b41c4018112580001c1c40554864902000403102c82c00c0981000015200100100c2404a152070402c2c05191122031311852000250306000480c1c0d03d80828211300f44484031111540588080b060007442004016440115100380c100752045444101c48035038851290300740140410341048402800001840d05001044014180180ac1090340d84441058485040c2da800d40c444002a940300605012100b25000d041c0e04881c00c0c3c10b5181500000c0c0501c80050380e1000c50035441041151070f0b81c401c0e084441119844a450310b0440d03c004005003458102d0310040c054107040107030b2100c1c10b00701407190160411010300c2586554031240c80754543c1c0d41043d80c05000300302003007101007071064a0000900c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 311133723 1250 311132473 311132491
    0x604020702031903031e0603110904050f070303020a020f100c0615030209130b0c040e1b041509082109040203092a0f040c020d0e03160305070906050f061b0c09 70
    0x846c10b07944102d80c05c00c8103080c01e03010925013101030010414008032680060010340701749076241c9407401c0a501d08400808081e03e5407260007800f20400d0f5021440d034401071301c2640c000f40e507126000200012980034001c2c000c0000c800c002c2000209046030824800c911050802040407901c07500811039054003102d0518290301ca0454501c00c1044102c5400d9000f10000c00c0716042c00e050010400040c030300941010030000e200059051020318400854005088e644412800d0410352140a0046041481804994011607140203420000712010101c142240c4201516222589003000000e4001508201043c41140040080c03030740421107a036122526540e96452501521040050920741210781901440c1402c440303106650f00007907102055001414031124180400e00800c0c80d00c13154800c5885159610f61000051007404115070042d0f0314034510601509484a05000c100404500910b80041c01004120406040a050b00700341d417140e5825107551100c03038000140803c6050343c044030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 311134973 1250 311133723 311133731
    0x5012708070e040b01080102121515070605090d05090a050402031009090516080c090403030506220b01020106080f0d0f030e0106170d0306150f03060b0a0305010501180e060402070203190303 83
    0x30a104607444e010b801041c1e030f4002580b8265541300e820a44e04009000400340d000328035502c1c03159658143d002415080c0a01502c0e40366038140c2030800140c4003d41d0b800ca028040e194000139003600c250210340138140d01401d55545140360205110007548020565820f56051010204443c01c51740505840b880c01200280044000410540318041c3d0a9004d031400360720808211050340c581c40440c5500507054100007440d95100c40c04681103860702c0103d8001c0c030359803a0901011808940c0001003200c402c7c1d000f00300194540079025911080f2903589046680700340902c100441c410380c1c00e80c041d02002d01c0d01041101c0043c40e00317401d66245812200301c0c031000e00d03c0c1e20511001001040410030051900b44249803425600c83c03001211500060200503811040b8002c0c103004e41c03c4040140140005e807655a08030032002001004203001301400600c050012800c04040043c7c2501075514403050b00d0780c2c0e03440d502c017007100031352013984220707014062131a0700c000030440750540d024624000d8401103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 311136223 1250 311134973 311134981
    0x200f01061e1d06040c05070f05031e090618031207030518040203060901090b01030e06040c1401050c030904052e0504060512061303020c0d1a070905012708070e 70
    0x205038040640145007a0340b858288030107041550050250081c0d4259070001d54040214000c41c2d16200b01c001c0504203102d141c2841d002c1010000090100007010007400c280101c100c04466200c1c440d0600f00e035032000303060241e542c03d100c5920908075141700c007d084980803c0400907100c0c1e5900a46001c1c2c0100300d012550001002c603541c001001110100c0d01145585440d00c005041580107014040b101682d818400849900035400720b074445440c2011580d240c502440e20719400040d42c0110f034209900c0020321501b6501400a60780340202c030740040c5050803916410700c40101030040001ca00c0300c0341909104808041e03501c0314000001c0384135010321054100418807080c0c2e003079940000c1c01420512100310000f5004601d4541044101124040403410390074100c3c0f6001d415113000364481707102e2552104010101f110303040952084003403010300b652070941c241e60b41c0c0380d984101c074003050262014141800070540788601080c1e2042c0c171221700e5078403001004d00d001d2040c5c002114901d1904144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 311137473 1250 311136223 311136269
    0x303050103030f26040302011509050103020310180f020f06040801050f160c0b040f0b160e010507030f08040c0306061e05060435100c110a0201200f0106 67
    0x90030070f110141042241d6512030f0703548841c14402990380c00c0c1211030050100b81014403c0d04000340f4072201405501c1d00741d0b110f00e21b0300010320080c44103d119110309550400b007181c6a0003400d110b55585210503046071001e84503070303001045202c001c913071210715003001200b2903070350002400141404c2c20001405180907070440f52862409040380020704504482240d02940c0510b850020320703803003030204c0e5440d1541c0c502022909a0010001c01d281c0802040000c000941c22450303400070103a41e2810020030130140199400d100d0401c0190004102c041000440e5014409007900f140c400c001208807243e5907101e200841d209904147c4414005540c44185500d004401078060002107680e5450180313840c6034002c0c00d07190301c085050f880341c00720011220030340d03160390343c8120100030403c0c0c030300c0c0075605c446140040101c3c14500000c5007040305142d2220500003904001f996060711036008480f1021800e213203040d0100c201c0140c41c410503540c804640420701618004021502860307402d5032311001c407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 311138723 1250 311137473 311137487
    0x140d0c0318081c020418020316110304090504030e0d0b0117121207050c0106060302090a0b091e040216050c010807080c030a0b0a09052503020405031e0f0a030305010303 74
    0x101120024039861800b02c2d10050454800e4000310b0707040c807504110365019501901031a408226003450742d41840110050036002540b0540301d4a1550619000c107043c2590802031070000c00049030310600051001014590006070410b0290804601071050303400042d841c412540411103c03112200300400c4502c06a08003280407000c000b000d00001a2400e14442c650f006814014601c2c0420790041403c0394001d104490800c0580e100900c441e5407202c1001c2d000c0d60100e054140189200103000a11583c0c0340c00391507081400421a13011a0b60541b0380c00c6400028090070f0342d010b0790030801007030007000390b0340051038803449031028013001e0402000250401c84001c5c601c206104503041000485c00c00c00c03040720b41c4540d1040e030005080704e02d0008982281099049482c190b840c2078280803882c07800030040102c2c0d1a80400d0b0450706005000c08800b40d004511400b0340580c03000c840700300d00f4a508803e07103050070211411200410a40150103140104115051f400f080c2e940006006059000d15 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 311139973 1250 311138723 311138741
    0x5070c1b0501020d0e011e140a0207051507081e04091508010c0203070512070c2601150614070204020d050c0a02010606030516031e0e16050d03081303140d0c03 70
    0x503d545c02c1204d02001828504004540d0251074540d81964001e06001d0103020f04051114501c3d1610350b0240c4401070340c0c4e00554084e5512403002d03500ca000a184841040302c04d801e030301001c1e140c201401c0380300e1901d618803519481003039000144030114440902e031141c14020903052000b002c03980c0c41d10340014210303200340c90860115081041568042440003a55687d107180003c0555900c04950901e409080c01c1c1e90480300707111103400030b0006410340841061150b401050020007402d440000702403034580e0030748181c00101c1c02c0b000c800c5080000310701c060b04d40319002400141c90302080031910001c0704c20803900d803680c1c02c00200d044800c0c1942407091102401281c101041360341801c8204d20043c154025898040540790303080c0c003240105c0310180d0304500710a813006000c13500c9054625529142d120340300701d401d401c000c5070004040c17802c000c0c14504150562a200c0c903503180c0a480305208036000c4025000c0c8079200c94916140c11040c0000c0800343c2405000007224540c0380c1009003034500c200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 311141223 1250 311139973 311139977
    0x1615060b04050d0503091801050108160816020319030501061112030c0307020a05010c021e030f2515090b091b1309020a080604050f0a050703020405070c1b0501020d 72
    0x181031212800e05800c0310705840d8222652403514000d882c045265100d0004080e03040700180960302c0000c594510000d069402c262070308907082c0d407160301a191808000700d218001a4040007c00c6120f4080d100c0c080000103e441540c0c03600c100140c0d00302e120744040c0000c0000a5650004000d0b40d40d000313840f4420700581e10041d1042024031703884240103020107030880c0481031000001c50b101600070003540d0781465100c0024003080203c1030020351204001c0400c0d1001d0348122151801c030754004401c9440031a02c0e148224140a0150b2094000340400c94034a2500858412a00c010540000b03000080003001c400c0816013407110720b086074524030003801d040356aa00026203407100c901d494140d10614030342900c49060040c0c0c8034505074040d001c00040650824200c07403003c55100c00114060b0b2249000d9000c81e0000c62030160082e640700f88545010340070f40c010801c10f00c01840c0541103a90801460310300482c07480b06544075046035241c00c03071408a444100510030086543c0512034005460f0f514 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 311142473 1250 311141223 311141231
    0x507020d02030a030b0112140103110d1e0501060305150403020106050a0501080a0f021c0e06010617010306050c0d0606051207050f120a020c06100906050607030c061505061615 77
    0x18940182d0780f402903501c03060a03d600c03401c0314103241e403003940c0441002c3d00c0340b4810708c0070140f8014907100000c801e01090f10700096018880c2580d06050140255855000d17114100300c2c4510640890080d51001048500707540f82da81c0000401c5040155891080341003440c8442420980f03806803c40305140d02003402202c009204002503a049000d0552001071032a01140c8101c00410101c002d01ca000309030151442c0c07001d0310070300c0044280d000c0320341100380d14125400c030b0b620b524040e150303102c0d03c44000ea89076180100600008181c1d4012070b03002102400d010b0304084001020405582140c0c0050380080c0c404030320403120218558407240c100d5050309011f854921050114001d51150354044032203004800c0c0071a16010303c96048030031300c210580540302242081c1c4c1914070b00c82c1079841030513055414094040351a140640481d501c2135030540307503580c84104c80e03a03a4901810804502c140810300ca40f600080644640c80142800c04003204019035a0cc0203141c40d0100c100c07945c401c6285c01b450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 311143723 1250 311142473 311142493
    0x9080606040c051206030a06020a02150901050c090d110a140301050a0501051311070f06020301170607021504050f07320a0909022d0a17070501030507180803030a050702 74
    0x200040310704081ca10444d1160503541c00011a280c6624194010095840000c102043c50b6000c15420040801002c40e2000341e00c1d6498181c0c243e460a50360074001c0c1204003c403024130310300714081c00500c47c41044800052100704000441d80c545a40c80070325820b500f900360002600d8288205540003254100420455040c00040313061200181525090320b0355403401d01c01c440d0466010b40d501c0d10f60140000c11001c585240a0b40a90001e01c107030080ca001c1e201104160300c40101d03841d407095202e94002d0403c046966014040400041d00c06d0350a806104204150201d050004501400c100c1b410006190700c050701c0d840080080c41c83c81e40c03220031090302007074240d641e082002045682c80107000c180d408050000454241104121810804400c2c80d440ea6461001070001e188041c00c0311030710742d2641d940e0840e081c80745000e2022801600700c0c0310705114940c020780c06150031861f5850402da142c640042c0e2703182c2070005c40d0001c030b4250340040200305000c08540101e1340c2c0003005101500300205 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 311144973 1250 311143723 311143727
    0x1050f040905061f09020417010b0d050312040218150f031603151b02010605010e040921020304050324011d0f0c0d0c080402010e15040b0313080a09080606040c 70
    0x20007a015240002c101890300340b02855410710080903045c030f00d1085644580e500c010080c01c841401803d201542003100156480c80d0243e40010505e0300003016500c1c049180c9000d0380001002801240c0c81904004801c880b00e64007001184942a0071050388601403444040101400000c00f40078403d0344103885080724644041031380d00840e58032181d60b00288450f040400081c1503248055100d2074482d10041130810750540200017124020b0b01e400c04455200130501c000e0350507101019140d030700e0101034000362003918507040803a0403da10503030341060703201c40c0002c1c01c08090b20703003407403601c0b08400d54405654817440030140100010707043c2c284919161000540328840060480c0d40810840300011190550320080301c201044000f005c2010b8040b03107001034100d0205540c281c1c0050204040840503041407400c030038030248112420f900301450704144c0301c0799900082240c8140803d0100010005d0002805021211304c103480302d201c3d03681041101c81c0303820701c0100807500c15400c161000b0212a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 311146223 1250 311144973 311144983
    0x1020406090506031005030d020607170708040221100618021e070f020a060c0b06090c0d0f02070b0903042c040b04051603061d0730080307030501050f040905 69
    0x11010703a0f08036125650fa41001c10606003070f500482c3c25001d5810000031166001c87c00522800f41502e038007030b1100200c44403c406103422036042c000f0030150000b260161030101c0c25401c84043c556140040584d0304c20b00c660411000311541c119240d141d04041c00155103e100c0c480c0e03507240b94202141400f14801201003c0c4101c07407462108480f0004185040c45101b60741500d03082c0c0c02401540c140c1e641d8442c01040b86211400982d21203001001052031442c014100d103014005151881c1e081c8940d240c1c1d01710043c104021082c200a45c204005c0d000684042071141c07040044030051611140752040c040d49543c2100d000d4004154400c0490700341801044000713030000d070805104901ca0780c0b9403804503e440020344000916030b0119400004006954015441c4c00e03000074035840d504810705026a99800d000d01480840311400e032148180d1004013081550208200692051250742588a01205034002d035641400a074490005002c0740c01c1c10406042000401e5408015144890b02d4840e01c1c0c2c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 311147473 1250 311146223 311146229
    0x3060d0632090303180307080a0e010909090f1401020c01110c060718120201090503031803210d02090105090d031107060e06070210030e0d0314070903031d041424030102040609 77
    0x10f05d02e00319140d40f00a4100141c420095000252035522414038001600c00054a0030f9540010050500450903050900880c181c6560086480e070881129560b400050364000402c0c600345d43d400e100071b41300548240141e03040710140440d029910201a80641d0030007600404180600101d04055030040c40403480c850100c54030402c015001d90307504d00c01254019030a030301075035041c44042518502ca0380c41c1c441e88070003000c0c1181190180e15002944040c584920b0001800e4000240b12450700c5542640041c0100d020516005140038184c500044503a0b110200650000b80301e401400c42c8507800304020340207083c0b2810803a560301c1349280000c1c0c41c0d00c1141c01c028010120790109e002c60030b001307400c0b1915070317a5081c0a88005448441009000b8080c0711410341085804a020661690103403000000ba02d2b050742c1d07a031100004065040340207844024030590011360303448030101c1d240040c140c401e0143c82e808000e481d041810303030310784400f20a0340b00039a1b01c40c4c1d104200400086400c00d03260411 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 311148723 1250 311147473 311147491
    0x6192d0b0f0a14030106031a0909030901050c0f0a0b0f0a0213030f0201090512030a0201050c03130b0403020a06050a0e0c100f030f0e0d0e270c03060d0632090303 71
    0x1640290402c22141005607070055201c495000c000480c0c1d840d050f410034180c10341c403080143c0b030143d40741c420072428101c10794842031107130030030818100654803880081102c440007204540a511244110758030b0806010410b4901074044c2c4144502038080540c0c2d1a009800e140040d0304200d550550382c4090240e900c03000b441da040d004890411640140455030040c500104040407003079400c507070310340c4a43c00030a80300019440c000c002211105000103a0780290101011442c540055903148890302d6006041a0254401c01c030200c000100d25006e1188101c01050010070507100c01543c1e9884d1141400c00540320745618101032005680c0021940c0c840b000a150100d480458541c0000003081c0300000c42400c2c0c0102c1d9403044440b074025219154205050320620940280c4007019542e0750040c80445860103100008039031900142e5018541129005180001074200ca0f0382d01002c4a101d00600c00c0b055842c145508066021001c0c1c619901c3c11584c201346036884c0a460050b00d900c8000c1454907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 311149973 1250 311148723 311148727
    0x6090a030e04020315191503060b030109050c0f071a0f06100305130c030c05180103050a0807081c1a01020714190308160c052706192d0b0f 61
    0x5842404800d414039107072000d4428040b15030403500030001e41c40940991f107012402240c40c0c8170801d109124144c100c1c2c81030900c25080d80d027004403507006408081c103100c200507401d001142c0300f8443c19000304013180c4503960b0000d0004020888803800c804c0104807098120b440002c1150540318640200c03c202282e103130014203079882c1c000140d00950101d90180c0380c2c1c40e03840340110801c03007001c80c104240e50040b02ca034000c580310714800321074a82d400d020007001034100007590000185031501a14600d80b007420028205132841210300d20340302000da034000349192290101d103604c214292484030031480038406001500e00340342401100c04c03042c80d005400381c00031201080d80e901c1851007480c091070b072100341d882c4e4132403521152010460300d0b400140c45035409a100000c06145c001c000c1d10651800309e40000f1880e03c580c036092a40c002c020016a0407400b030103038611686480c0003400000d4001000d90007010544001d03490441252610114001240000c1c1400180b05080503540b50344c1030110555 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 311151079 1106 311149973 311149981
    0x61d21120309010e010b060a11120c06060a0902090d020f03070e010e090d0c0c0902071401060801090b0f040c0b160b0f180d08010506090a080a03020a030206090a030e040203 76
    0xa6000781d0407c05001401d004607400e0032060926003d444102100075a24500bc6d840385203101c0d281d03005407041000b2403a003d0380c813a01600b0800411030038442940c0101d0809018048080d03c40c0c41506072080203542c04008100107041506a84d10940d652002c0110303e0b10002c1d00c130040680104a02035040d10302c5440c400b2000c80c1c00450300000c0307d207407020400003503001e050140c81d000c0c12a50071103401c075000d01682c80200040c10000900000c18180041d0398800503207003804c1040504140001320b000349500c80e0589a001c5c0b20035503134400c0624680d44001c3c2040c802002400c0c2001005030f00c0c10b0300c03140c4031b10900580f450710800c0b11000019039164071030645490041450000140441c2c02e010010784031000d0f02500c2c1800c515154242c0601c4c22070f00402c2200182d00c684510801c0544c14409a40c000e80c122000700954407042d030f170150021203400640d50013158044001 = true := by decide +kernel

theorem cover : BRFrame.Cov 310971223 311151079 := by
  have h0 := BRFrame.cov_init 310971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 310971223 ≤ n) (h2 : n < 311151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
