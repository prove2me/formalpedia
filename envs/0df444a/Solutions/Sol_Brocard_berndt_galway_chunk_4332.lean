-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4332
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:16:50.755369+00:00
-- url     : https://prove2.me/submissions/f979aa56-b541-4be5-92e4-ddd325a69df3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 778956834 ≤ n < 779136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 778958084 1250 778956834 778956839
    0x1f14070c030c08010c030212010b13030227060f0f06030405160e0a0b0f1e060405040f021b061902030c090d1b080c090a0b130c02030304060621032007 66
    0x1903252811043d18518402407007900d5503803808500b6400744183d10303843c10b0044401040481d014000400c825507481d050303070346038a42d0387d00040c0341102c420b00351b208411031203110301c19501c0c507100b442648040100e0780d14504411400c04039071041040c1c020603028180000124046c04400c000f41804c41102003500400e1a482d102001058203081e1802c816560074010303980303050724080110316a1214003810807280d40f0070450520807452003894046411200401022036a0f81b124000c030100c10240380d02c05030b0394480034816413500c0503000c07840c03216a401010901120008240554035a01c10008025840f44c941c00001d119078442c07024842d80c018140c0842d502000100901ca10224a08040309801c09540d01042038850808203402d0350b0000340003001551800d1654021911140c001e4440149032408041610442d20796002c2207001d80d1000c0b040200b04005030240b4000340c041c48601c1ca10807002040c0c40b03504420b2468006040c020112414014031140b240d8000c0c40c11f0034881112050366 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 778959334 1250 778958084 778958093
    0x34050a12180c090504171b0105010b04061e090b07062a0f0207140d0f17030105040c0905010804060c0e1302180906030d12060b0c0c01020c1f14070c03 66
    0x1403071200111030307000c03245a000800e035110307101c1c2d00d214075041110983c00e104404a0548203911500c0007402500303ca40903c40c50f10f00034030846001c0c220074100342d99520309054000e400481040119000c1d01004428512583e03030200842081360401210b0320703102c1016180001c05002000031440301071a008001580c58261000007844001068407081c1d007000780c0400403600d454840c082d82559004003281c0e1200380c1010b803941d08141d8000c07a03501007540d00d1940c40c1075510340003003445140d80102100500c124a03080c41021300540680c14090a034130320b03100020b8282c140040001c0c110039603620015844a008035070421422100500000b00000c84040000003034200c04158403050108800c100464140510340b41e0013004010014180340150040c21158205601404422180c0301d00780010028400340207403007850f1f00301001d03104141004000918040852031454843c640f5441d0082480c030032445049518101c0307107020525081c100040c200342d441007220080824400520020611 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 778960584 1250 778959334 778959371
    0x11060f0702010f110a0305070c030c12110a0f060c0219091509060b0712091220010305010b0301180b03030a080f13030906050901020c040f0534050a12 66
    0xd038800d80307032041e00f00241c1508940b100c0b1203200341c401e41e50183c2000c2000ca07004a0203020340b01e01c40e00255902e0340d2070380d440310350784c1c0c0e11503001c082030301c4450100b0342c00c0001c00702e0030b507403840300590380075401c1c0b454074400c8101c08615124500910070040009019521003100e80c140c070051070101078010345d55909004000700102581400c0c80d280800c0301140e400c040b8003813201103c000601c000d042c007001d0f88034101d00e600148100800c0c4501a00001004c0c0481e11226840a0241c0074080c003d82c0400d680152204445644504062510006001c2c0c1965503041d00c3c10358500040301e8416015001c005c0000304584201c00780d043c0700204038002030a91060101c2d11a00d5140d814040507120926124550981d0050003804501f1842c1e080c4070309072240c40504440c03901441155260492080410200e03084010f25113005c5d0345a1382004603062110300c0c4210728110000501c04010040c24404400711080c0c80083c0420900040c5050390710700c2142020342000c421401003002e50648006070000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 778961834 1250 778960584 778960597
    0x403030f1a0f0d0503030115020a06050106021e06102c34080604050a2a0201051006170a140c0703260412020f0a050304140607020d030c11060f 63
    0x91820441c2c40c20060405409109140c0c0e441002141180d00f080d0010001003008202107046100b425100000301e10300d0701403103009000a40181aa40c007424440020a080e004184070380d41d8086014464105071310700b94141202c00003441030078018042d0600007100c03150210400070b940200320601509031140560340080d91b201c40c810021801d0010305c00f0708040300d000108008523008030005072050601d600250fa21044202c030000c3c892000d40c1c1d2402d59240e020600380302491914030980c5101703409100d80d0f50001011b1003051820361600c10020000c5c4007604400110001f03010210700d09101035001502008003140010041b49440c1c0b203422419005200c091b0005194004005a010201902c10014660303900e284c0d0420303501c54442201f01d25854aa240441c4120031a03002428004d01860400304e20410195a640f440d0181c01c0210300340c0e01ca403181c401c1408200d0b07240143c1ea5021a090341c95070604004144901d80e00380082c0d22846400c00c6a0440d0000403411000322500004010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 778963084 1250 778961834 778961839
    0x90906080606040e07050612060a0302151209071809172206140f07030908061302030f1507110c060f0403031709071202131d070b120601080403030f1a 66
    0x721104540d58503507505c0080c400c2c0e03500002c04000b0300d00741440b030340070a40d80000064580c40000b581e079400b24085c0141030a030804030081c0890000f000b90b1805410a4000208100502800341401c6800010702c151800f214405c590301d0452038104544244182103188080031516101c100c9001031001c0220073700002000d41c0c85246010489030b005141e4010000c0b0811501400c00c8140c0390b026007243d2055400707a00f4400c94200c0000c08010410481c1d1266100400b80c0e11480704070300c1850f281c5000c100e2040c5098101c0044803405522841040c0c3d4801c0c1d207132030180740c1c1d0800440040c2c204408208050f4203d20000340200f241070b040001807084900c25a074a034060000b4080c010810b041c00d6070709140c1ca41051408010f0042c41c000214803507030000f08203007000801100f010703040381c004480c0b502c4c8103003400c4a80c2020385024084c0c28024032000c20528640240c40d0b5840d1a02c050041c1058113210458001c602410f01c42c0e404008043c403842301c1004008480d104080001c0341c5401107a2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 778964334 1250 778963084 778963091
    0x40303080a062103050903071403010b04020f190c0b0f0f0a1b080619030b040606060c050c210d03060f0602010b03061603110f030603010b01260709090608060604 71
    0x5002850501c00c010880d210031036211007040c0c414210f028a040d80c3c1c101981040014040c0d044107a070140882c400404000c000d24810300300b4a02814256209843c803035100d984144849240451840d003210f1803401d00e401750040c201d02036481902c1c09094680c01601c0280e0b10010842480100e80341e243c002d040c06907004040369581e221203000c0d43c0ca10b851421008440c1c207100d44901c1d01400505405c07080050080b11442c601180350640c1e94480e5000b510203100c00303014001844298410780c00a03003128508602c4640558030741070759881030754110f60b02a00310581071640542c03a4000701c00103007108074143c41d243d9500c900000c02034549405080307a00c00b01c4500010307440f40140b04084910034003501604140d5691010000b040d5204506003080c59141d003404d0f00004881c00007007541c00c90300441c1d10744074102007040c582110030225145052005071450304607070314202021450140501c8580004a5595a8089400443c00c1c0d102001960410700041105540416068800c0c10169000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 778965584 1250 778964334 778964341
    0x90d0306050a050d03030e030c01090c0f080c090c030406020409020f09120d0207180b060a02150a11090405070c081308060f010b1207050408070b0703030b0f370b04030308 75
    0xc0021082d80c071640c4d44c091140910440002d000c1c2d00400c54003900141a02d0500301007860301030a403541d45a08654080329000c060240b0484a0144070150003000010101c160300c0d1400324a4600300038226001101e00070000a082000c1e540490303001c0c00c5c50b11015521007140e650003140503006080e10601c07032803007100100350401c800200181042d503160f006103055850328130401084410b1000522503507131a680c0401054444200800c45565268020046070054900f40211100003900080b0f842d1b08000742030500a6040080d100940c00456001803580c907002c02c261030b07040e10950024058540444c82d010191140001e000c02c40e8800015908583d0315450a4980f200c003d004941c032140b024800317504600003092006522601d5814001d02e0141c49031790032850801c0580c801074511100040c1d1204259260007900700104069030007802032444540002c489107901c92403140341031031050302e4400445d9004407403440701c00304078010f03600c90b5201c403110745440e0300601060b070216103900c020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 778966834 1250 778965584 778965589
    0xc030b030c0d030e0d020411030708090d0e030a0b07170108061b0310121b090b040b060c10050705070602211602060403050f0706020d05061002161715090d030605 71
    0xa921402d43d0640e18400034400a100704080f100c0039500980e001982c2c0c000000d81079040380300a500846190316003012600c0e10740c1d1100d181c000c2c01c120300c00401c10660b50042e0240c400107840d00310320758000c01d04030044d51038180449803400c11045440100081c0000021140800b04109009040c84109845c1e10049003141083c1c41c402034540807140400784008200301a0804804001e05100d80d5000c0e00200c0121941c00303008515400844180c0c0d0b076071800e9501c500e854450045a0303d010b840d4641840202030032103807641c10100c94003019680b00e00001e01014819411030302038a510400842d03c1c1e04044500c0350095100f030b00101c0e650200d03440072a615070001d515000d182d0300d45600500250313941c1d80d002c40305600001200298102c0074440100051004d0018000840b9405000aa6840e12a040122045c1140090f80075908012007000d1400c25000c0143e05032821947e000040c0d0b00000d1403685401031130550305001a400206010941c81c2c00715451450aa00b503400748982603c6004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 778968084 1250 778966834 778966849
    0x60f06180504020a050c0a0303051e070c030806030f100905010b0604030b0c07020d06090f03020d03020f0f13051c06050a0b100f120c020717062e03060c030b030c 71
    0x42003440d500000100075920b8690020050f808580c42c00c5030a00781350703e0005190003060113003100801d445e401046004040c4286c1d540d00d6a00860039400a810301843c064508040d01d43e004d41004004400201c02d1b8600300484800340d2031001c1190f2014802011020003002031100c1201d0035420b051038202c145c50800242d0701a2504600010519100d07590b10701c4603944101c0e82260810118032560011603458401c0d680d1443c0112034629180c0c0b01450000e0500082ca110a01418414054200050b0070402075030f85103126044050782c3e61003000843c2c0302c1402141d000c0b40c2d100642030200549910003607400428244942e10601c5a501c80080220998514841c110b0700050301040d06260a032180f50703680701241a500b003000f00c1c03036014440c0c181640c9480d002c1c0d00250b071107036074100300c880a10007154904c502e0314409011142004145140b0044602d003c0c0c2a4040340c0e240740e20401d861850355140255446103003000300840641020340a490014015442030007a0143c00d10241010b00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 778969334 1250 778968084 778968107
    0xf0506030403200a24050f24010e041104050a06020307080306100509030703050d0f031401171c020601050109080d0e19050d0813050d03020c0607150c03060f06 70
    0x459040c840c4500900d2121503400c0003400d500d8030701c5440040c43c0401c0700c000c1e5a20718103545c0750751854080c8107070240303405461014042600c100190b2003003101d03a10220094400c100d00418a8031400d8102e039004031050040028190740c01442c01803000445170b100c0008004a4509441d00942c241d900d9034103985074040c100c8080c1c040781003000010b01914001c0c080000d00c1000c0e003000c0c1c0c00e00c3e160381d02290be0a81d10381c00803101c80d8031450b11800303102e030081400304220510740350034070a44030030305491801220b040c41410224803d00358000c1010340c00f031100291840b85000e2031019202e142600a507200c00078031400340400c04e041008540110003085c02000804d41e0b8031048002c103058018400000e502030801700c407041c1c110202013042c0e680d840c850a03145008042c12900c032104004c10810f65946640118030650105040e0701c0003d4010a80d040407440848003140c80d0110b40c20f000c00c0f1102541124081e9a2520309c00480c0d49405501c084103547c2040c4500c40e6180e115803080e9a00c90800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 778970584 1250 778969334 778969337
    0x120717040210050705030f040e160906030203060d050a2a030510230703050f010b0c0303160e030f0109060e030703090b09190b03040507090c0509150d0c050c06100509070305151302040f0506030403 86
    0x11908cc01154000d07001580c1048014200c0d150102a980f83c481c141907040d141118294446000c00504480180c2c00c5c80b12940150300300e48086296550f000d90b40c0c000305d040074110b0340d1509e82030b12b4031603558160b4a1070004081c3c0d07101014540b04034000c1c010042101d40300c0091207000000f00320004848142d80c15004114011880c684a0030000b00070f020f4041c50107010011650801c0c012504c0922a462954440070004240c0e0034403407408005886212a07124880c0e802445000003180d486082c0b40c08440211996990380d5008070301003646c5188214109800c100130b280c00081e005801c10055110b180280182c030040d40d00c942d025403d80d4544900040010380902041d51b4500c0d0a040301c0402d1102c0c1c444c003038a03000118120406a40100c0f50040206401040300000e203041800403591000301218031020060504000030f103030003005050842050360351000945070406442302810b84800050008112075424075044001e0340c42170080200c00100f54200007010b0600406813401203606 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 778971834 1250 778970584 778970597
    0x4060c030c050d090c0b0a120e0a021521040b0106030e010b0f1020010608100501060203030403030902030a050f0d0215040f020402070c09020f120717040210050705030f040e16 77
    0x4643c40700e00585070f1402c0c240d480030480300000402c030420303100414160f202e9803151140c01003590400c2040fa50035a12003016504000d01e40e80041c3e40e030554412141c501d5035803d6444220f010000303d03240344503a15014804d03801205000071310075400032040c12105250390501101c0008a0f10600ba034400f089032a4103d03035089155503003854210312503415401545030080214160f06513009900c1242101a4507a954441d0b040c402e05030240018010060340c040240103651400800a45e20f110080010701015629003044046690900840f0105604201101e50341d0490407460307600d8400116001d40544140718419070042e890700c078205d03c50360b0003403040c2c00d4842c0da0b0303028800a580000c40c201c031007151340d001c08121311040e0310280413110708040750151030f120850410301070541e0180070343d018410012034048020fa0b0141c00142e1040e81a00e22541d84c0d113844009460700d01819400400d94000800c0e061294441840500110f5146001c80809500d489003080e1201c2ea680d000027000401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 778973084 1250 778971834 778971847
    0x905241e0414060c1b010c080415110604151112070306061b02061204020102010e19020907110618070b070312050a060b03132118050609060405120c04060e04060c030c05 74
    0x41e074240c00e4030340b031704107040082c40e0403015a030f04070480e0b05c13070b4200c420136804000060014070f5000094540b2440c00310000e11150900303480e01007000824030360005500340c40305507803c0800c01b8070040c1d41484040d542c0d144c1c0941040180a00030b00424040c1070700041d600b0a4516a1580c00c2c80e540305e050740c01a08062405140003180e001d843c1e8014011703415503480307442410100e182008601e01e040c03054030140302c41016030303c10880090b00103402c4104000d0b600c8000ca281405c003040306034000d1809040fa040c51a404180c150500a8603804580388290100385802410b82240803010713000c480000c03c0100c0c1d0f540a034848100c90140c0600c1c10050001d0000501140c00164499103da010b407800c841c1e10101c14600301c5241c03403144041000108070082c031140c900500410080078240031222607080040610101d00103018500ca02031050300f0281d134800c42d5141c10b00001d0b142940140042c05a03a8031114510407418043c1d40c1115803904c3c01040c003031068800d100d0074504880c41e59410b8034204 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 778974334 1250 778973084 778973113
    0x10509042406020318091506070f080c070315020705250905270d0f0c030e0d03030c0f020c0105030c0304081b0106150905241e0414060c 60
    0x1c00e540c002001c1c541480301d8000d640c6080e0300d000000702101d5000759554002031407010032100c0300f2030b0304034020322001d0148005501c4e6400042062082a1205c82d1544c500d81003103000b003150b018010302100400a618010385002140401c10749008111035806080aa83e0352002c9100f0800083c2c5550000c40401d0f021611110302d94907c41400079010365600d03119050003086881c1aa07030080810382601030190a1100f0000e85190000c02c030707006d88140407a0200180003900003035801000c0108850b00d16003018000d850903509034102600d080003100e003620b000f4004103006405d03a00441c000000219507144001950b221480b8181d48060858039500c6000c801360304050800c44041a05005a6a07c5000c0104000d01d440420001007070407454150b030b010140009404060812281c40300600031511901400f08050300520790b00201c07030712900c500035014004c1e602c0d5121030794030400416103a06800b2004e40141c076640e051010481c010780003041414456100d08140e44d4020072131140c15034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 778975584 1250 778974334 778974341
    0xc090d291e100803030a06050f0402180f030f0f030903011b120b011202031f0b040e180c060c07060206100303022a1809010e0307020904061802040923070501050904 72
    0x3a42d04210011000d80300c2e1031060458100b00d40b4101c0701651148104100d11303102c29500c8034902c00340c03000c40c079140301e620325501c00481c1981c1c1c580c015500110141600e8804101500d81c68401c081954800b44c0b443d03215276142e0780001d002c60702c25820151103e040124241c200014400c09464091000b06d5600500e000740c10742c011a503060081e24607001000340c2450004522a85400a8002c0246006035045645e518a5004140460f50621003841031520b811006500424803210450100402c1205a40381c81414407035a0740080000c03681e101f807070300c0010b18003050b640785400340ca04135540c05c50301d078464000a01c0080e006a11030b030307400001400c10303000500704e0704c2d1300901d1184100c8400010950610722840b8103244180184100940e101c030a209064003164034401071480c082054001503201c4002030800f070030300c650f10320341424111361140344024000c4e0701a1043c0f014a8007400c0680c00c045114461034040031400c200c4408690300800d038401500c2050b150786003405403100902008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 778976834 1250 778975584 778975591
    0x50a0e0406060f0e1608060f0f0301060503010651030b1c0b060d08040314010603150203041b081e0127051002160b0c090d291e 56
    0x7240d40390004a1034801d0598a400603261068403a4910708000103a080c1c90a0303541782450801501a0074014259904684002d01d0502101e401501c40242c1001074014101c907400582c1c958641000042d4a03413110300c9404290600d80c80c04c2045a050000710101407240d401b681c0800341e641c0300004948001c9900e040e035485a6031034000b41e80f0030400082030808082d0354610441320000010907081001c4021096841001078507604a440f40c035644001d86406a0f002c020080080100e1003038440b5025400f03640219000815410000856903164000b940705440079180b00303c25a0542e8822501590440b0440760f0003c000c010310703130450840b8480c1d80c20050640d6050b540350300309001c00d44860000055444080d00c6542c403100c000d0b241c164540000311a042094a00620001c18040e1041c0072800d4583d40080018403280e695010039041c610a4018599007c0380005080040c00701070017541008a888201600700502c0119584101e01822590510300c05480d00866100207102025170342c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 778978084 1250 778976834 778976843
    0x1a0114031b0706020712020c12010e030706021b01091b05270717010905090c0904030e09040c0e090115080f0606190e09010c080c07020f040902010e120102071202010501050a0e04 78
    0x20085e140d500c01003040ba45452640060340000300c0340b4041e03d0205400825803643d00c008120485200c003406841e8051244003408241e404100e16003140c0740b4482c3c1d910f0000d00e90703000300500e02c614584200c07106c842030b8003c01c00f0b02900d4030100d030a02744024101c28082600c0c115850f0030350103800900b075540c4000c00007401c0040030003003405000904000d09020342041f1202103454a481c445927490103101c003548a02c1f510941e0140400300c2c0d0003070031041325040305888400c42c41d501c90405501102789030b070100505610020401107400810340c44a240d009100e05a547d2540c0c0d83c480440d6500e03c803582d001c0264000d080400c40e5440c0021100350220f03240b071504840240e8031826190049011594103106035141c000c8103c1403a400720f4102e51107801c0452450800c82a80c000c20450329241035041e0003030343c1d142044000e680c040c66043c60b901000429581140400b694154080d4104400031a00c0c4856034a9100d403150042c0a030034180c0701c020b402010a146004600104c0300f50140081d81e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 778979334 1250 778978084 778978087
    0x90a1104180308040b0f0c0406030f0212070e0307050301021309151508070f02031201030803070c1203090b0615031b070602040e061c0b01050d03121a0114031b070602 73
    0x20005440702104103900e9020b0f84401003c1d240904142c01003040080c445440d510404003048034100780c5500ba102540c8152500080e00840c2d007030200000d119556440307007010904410442c401d548000a103015000950a40d8a003035034500c203244c00d07401a800340c0d58800400980c00c0c4082d01113944100c500b00c50700009001510365414042d4185401c0082d2100081c01c00c804201c00150070103510303808804c081c4000d40c0361130400c180324028044103000003080200000301103600340d8401c3c200342498540068840021354260318000d0f00908440008070f0f120741d80740340046c0e65071134500040c07031500c240e500029285641d180c20600c260207000e995000c80a100f8001e00001c203d02d80301410150542c6241480c860a0030000c21861042c2c4401e44d4461480074020040000e4040010380c0c11100141c030910240012882c0540344820360000070203d60340741444c100104455964944403009003070b00c0705d071a1441d0300d021141c91888200e442c0749500c0210b4629801326084d620041c91903901504005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 778980584 1250 778979334 778979351
    0x9040902060d0501080d090321031506020303010602010b0306010b09190b03040507030b09160302040c091806150c0c270504050a1403090a031e052a010305090a1104 72
    0x5155412251442c8480d0b42d0760001401110000c00c01d40305601c005051800040d8510742e80c10039a1240720545448162039100c20714412400303a041000e40903a1210920070041c3c6912000795207410921a800056082c0328035111203050208130a0b060318210204189482556014007906801c086281c249031080c4ca10700081001e00c0c84082d41c025446a00071301032141c13850034482040c010103040e640c0780e600070b800b001c0c0e140712070020002e0031241d054038081a1080c52480070b03542c20586034401c5401c0d401101c41c0964040b040c0d0310400580c8d2242d0440390042d104040e003255010502e00303000740b150500c070b44240000114804401c05040c0656103100003890051661710540c3c0c0251400c0340d440d4000e13510502080a15413286d10744000380710046080400a1000404120b050701c0041c00a4548518884448101403584a0019000030880d101000d103010020003442c507a12041c4040110752240f80c055610a001d6940101c2c0543e00030202031030552111646001e030800f04036402595046013 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 778981834 1250 778980584 778980589
    0x40620070b0405030c070f03030212040e060909030904180605130308072304030609050601140d1509050601031a0f0106050a0e01230a09090903050307050310050a141011030f09040902 80
    0xd07030043c0047c124048032943c5140360181c64010898071644400105100030300ca840440440680d1014040f14038150740c1c8c468642c90350640c0b08240b00703e904982403002c03d80c002098070302d84528091082c10100070b65500d840c502903032600c0000c4010005420400490b125a101d0340c403c440c0d130f40c01c103125929440c0706815850b125074040d600845034591501c00ca9014004148055030040105030004035080301c542c00021307003484041200401804c5014111520308140758031a9654590180455009503100e040090101c42d0b000c2c040500403500f10b0010341c00001510f1194101c50541d290700c0d0400503802020b031600e4070301d14075003410031800308050020064a111760101110f003c41c0303902d43e5510612001070401c10b6a1b001864664180b00072980003982c020100c0c4c0c2e005c245880c2c00c80d201d80321315074441c8d040da41551145034801c0a0aa002c162040380710058901c201044807009004082007200b540c0074411840703000003d030800d220b40541002c1c080700918900c6401400080c451080c3d500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 778983084 1250 778981834 778981843
    0x7020105032e0303021b13020d060b0414100c03020709050903070510020d0c0e180402150c010209011d010807051b030f040302010e1c020d0804031a040620070b0405030c 74
    0x442d284503440701c42c410000d1603018804032445400010015600c0f00440c00030407800c1a0102402051a500295844080c24036074000400380c0741a241080d03565558a0440d80c2802e0150400b0b4460f00001c20114441400794035000303c031130741c03540141c9082494140082e00030701d4000c18100c1680420003174100002c50900c01803400706155140181ca070744032000d00500703c401030890641440000c0b03c203100d02d0ba85000c0030065229501c0d0a000c0340b9512403022907429020350948100710080070036900c01400041d009040000d8085c1e03204003801000c0b4180301c4403d050307030b41c00d80d001c2004203002c11b003014414030080440c24403c00240615a901c842100d14682c0041c881c940d0140002c10140119a48032050641490b401c4072500320b20290160340d0002e0000c541e800910403c8070109550800c03075114140d8004580100669046120070030160750315880407242180c2c4030b46082c58170300a0610040c881c0a03078802480340c00c0e0401700c00b55610724031080041c0040e0340303900c800d0040c0c540b078003001c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 778984334 1250 778983084 778983151
    0x80c0105090c100504030b06010504180912032c160807030209070306061209030909020706020a09050307060912060204090c02030d11030606091311030705090f09040203030702010503 80
    0x925850800a01401d0042d01d419040c0300d030030401c40c0c00500701e6228040c0c5095a4225034440066118800140da42d0311580d44440390028000b469400c04455a43c40080e41a01500e03501410f94800242107040390107407124402408170004045403404840c0403030f00020000201180c1c40044d00c054012005981a0301002d02540300c4070041c000c40c100113803d1134001c0380500742440b101c0d05105014049096001c800408079a6070000d00d0140352207061040000d00d0041811503580c051410f090000c0d5010848180124442120010702401c0004143c0112441941c40a00150420006044501f5244070545500b5001d01c000b040c200070320300c03403d42c040320300d1380066a2302e00c080085002681c0b560201080010400d008001c01500c80c14100c44000b90225041a000000308925100421414a48880c407010110030850040d800000400c007621040790005000c2c8446410000701d8041107038002d4050f00203010001c01940907401540d006000940c003a181e075003c980c0000344425045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 778985584 1250 778984334 778984357
    0xa060f0b0420041e030204050103030305070815010912020a18020a080a0b0901060806060c0d26060310021b10320105010f090b03150405090a0b040210030908 69
    0x1000c21110601d401e2041d07290b00010381c030408180728800015161140a40d2040d500340c0c107603010041c01c040d140101c040b005035a00600401c10ba585030700f4002c0040038110750000c041260701c0045075981440c0004070700f407000142d4030b801d00982040704c441060460300c502260005d80e24007000c50001c2a10716084983c051f000f20060701c0d04c5045600603c240000352149082d5440c2440091150300c80310f891034151040c0c2d00309455641ca81c5408140035101e40718000790117004101003d40e0507075001003100c681c0c80d03035031100d0f0344120b12007254070b040285e040c2e80d910340c15840500613000101386030b0050600d1203105202141c504803407441c1141082900819180c1056580c0400d000d001e00c604040c040340851400100c032240c03820700c3c00e0070702d1040c180200c41c18001410010340c080c40c41844280094103070302d070100c0c0c1c80c2e0034440c405500302c86900d0f801c103102310704100001d0044080000c0000711580c10411003641c94a641e020b1112a01c0d0301100c1d0000c0688440c0c804010803c42002400c00042e0b2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 778986834 1250 778985584 778985591
    0x4110102010f23010501090f091a03010c0908070501020f0303011214330603061503030c01060b0304060c030c0903240c050909010e06030a0b150d080a11030a0f030c020a060f 76
    0x4164542100e0513009903047c00b005041c140030300091440600191580c01d58002120118400001403440c104054264550b081101c028400c4d580501d00000f00c40780d4030100c50030243c95000590f242c101c0704a4101c801d600c203100400c50524000c007003603400790240500075410070002680354282000540d003000058002081c00001c1c000a5506140100c820844d400301d50030310500081d2208005030101589804064062441d0303501403044801200d00503000300600e9a030b90f0004551608101c2c2d090310064078003290052003a001740182d80e055012a500e00025a0450343c8004d86403602410680381d448104102d0035a0710010b216035003074514540c032101c2e22010070408008040350141c10416600322800103200f103d0700c00180c001d220039880817000034959103824001080408081e009603104220034110418025810700900c004081c59880d00c11b00a006041a60340388907001d20381d0f0000d508100c5003241107104e80d014a480c0030320791040e5034210381251100d0003503e14560360640c0c866078 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 778988084 1250 778986834 778986881
    0x30a0b010e16050403120905120d0e0a051810030503121510200c040c05030612061302040e100e030a0e0406180e030c0609060f1e04110102010f 63
    0x50788121142d10042800110b60721050900008080d070145101c0201034440b80c0182d20030584c0100b0014003c1c00c03002c1c100c03c1c54031030080f401a50355486182c62001158104c4054902414000c1c030400540341c014002c445074007040c10800404e440001c007000015000c1040110000314140020300844911200d1403000d0b04018401c5c330b91070581d518025204054001c000d4402d2900050a080c03110403002604a0400719103201504100e0100300040d405841c00c101040c00a0b001405180900c0065623030710317401148000c10039902c0105484501d45203252446440c0141380c5500b00004403102d040649000c1442d100302c40066403a800f40f0303901160004903030325102a5000c00381c5100c80400700e88c18401285000f0803183c0c00c101e10380044801c55107900c01006040c02c108116030782000324208607041c500d1701070700769519658242c51911403d50040c3c0401c0d1200103502108405208080901d0100e8a0329900e0202a80c0da010986055540b40d40f688600010740380b0a405c00d02a050b02611341024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 778989334 1250 778988084 778988099
    0xc0503030a09020111160521240115022d0d02100e03160206070503130605090f043b150103150509030d0e0106030204050103060207021503070e01080c040302030a0b01 73
    0x300e514800500651200a682101b4040c00d10b02104450003a6007000c0c003030012640b07103040510b60103800c218520591556042c00c02c40c500c0140c0c107014900d20400400d03602e030905180b100b07060702c02c0c940c0140c0c0800d203a0784c1038402c5085942940c18811414a92030702c2c070f1180071810140380313910301400b50f00301c0b02245070f07198820b0003102c5c1c4402001000d18544080018078051030710400501034010903001c90a0750030007504000b01d8617007407507103800301c61440d640310340c01030540d440080018010750103014401e002e41414003441160050417407481401851740c07080301c034011801001944004406c0540c4000d10344040c40500f8491a0002080c0030542c110704000d140c0804521425084502c2c04c8100402c0180200c00d1b42e50312000c0c850007040404081000c14007501241c1c1020398014600400001004107681c0140708a070310075541d004501c40540b10400c41c0e4082110203001103619441011540d61060030030540c00010325080a0419441c1d4012910340900d0b44405c0340e10103600c000500108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 778990584 1250 778989334 778989347
    0x70b13060b030601080a0308130512070606050a0f0504150e07021506101413210b0f04080301120201050d021303020114040308040905071b0302211611010c0503030a090201 75
    0x650040c2d00030300c1554500301e00c841e41d444007a4406400c00c681e030f0f004103826182014400d4a96500407080741c80380100e2628941e81540890030031200c19240ca000094507007410810700c0d00311039031507034a0007000d07103040280009090062424242081700090101d099540709208a019081c1d07640100001080c03801d0300d6a040c41c02410741c80c0720300c1d10701e019450200c1e8420104056440c1c41c0301507a88031010751a001c0c031102000d40150b08046818000d400210041269810480303004684044c070b107456014106000c84420349020301148400c00052105688075034445030140d00c10702d070403842c09100d40708440c00ca8000101d410b0007102d582604000b550307807000c10000f41c10f0403454010300d80b5146a40c0c0318030610641c41340d107403c01e031207800042e8141c2c000c00204400c10300003004480704001c00c0c83c000791110340e0000304042c1812801894001e4440400640d4400e00c644c50308500580340e240c4070700208035179840417107040148600d03034000002d8040c0040c50290003420303400305030703c034940c0f0014242 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 778991834 1250 778990584 778990601
    0x22205040f110412020604120b160807020706050912010f0b040e032704060803070501050712270c0317030601021b030604060c14340203120a05070b1306 67
    0x505000b45115225a2203040b94210790310031030480c003400c8040c40071880303a001c2e07503102c01e00c11050f4050200034080310311141441404105111610307452254800d46044105a404500680c00080709204842c003031401004c00d004010200e41456001108240c2950203110f000c120454560f80707002c00c541080d008100040000001460401c0b030407081040052503001914140285030b030006e0740340303501d07541c0c4841d001c1c00182094035640c20084c104180a800e081d2007110019668080c1c1011404031032003020f041c160440d440d071804502c080404030171103007601400d1f01c400c25030b01c0c40080001d1040784080032a1400c0c142103a12890103400181c00c003200f060307071040c03c0007140c4c0351003020380d8000c280c0c5507100341d0016000030300c0e00600e14202c50840003100b040e583c5800005564154480b03800c03c02881c0e00d01840e8180704585411494a0200c5002400a41540c071240d1000300503c07103c03000c0d02f1035184c00d00c1d20714140030342c40d210820040c4003501c40c082c034161003034203a80610104e070185442 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 778993084 1250 778991834 778991861
    0x1021c090c0e040b13110607080a0e0a0f030201110f030406170106050403080412141905011a01170c09041401030203210f1b01020406020f0d140d020a0302220504 71
    0xc8900d0162143d0034514002481c40032800d0005c080c9070200081001c5215090300050030740c0d92a242c1c6440c01ea00d40d031380680420030110300b4000d9504041d140c0901c108058070141d90401d220340e45580d00540c0c0c51a038010042e00076002d002c29802031000c0400c0070704014082070f0f8441000c070001802041c04003006030414420010108000c0c004100b4a0049800700c840440414500c0c041d1418008549861076405450784d00840d5241501d00391200c0032602118040e8008102c102c2c510014000c10f0020141140d01064840701059002440301c03400765031040e40904107518121150002034201c4804200f0341c003640701031100600542c241040810302c50301d41c030388030101c070520107072200207090040200c455001c440004601082039034980307503003039150400002551102c5e199403000e0340303400328546205d003144203090790b81c2c22092185000b22000000d8400b4140707001d4079503c05c0000303076105d900d40909058081055060681200b09032181d40c1802002d5007221504007030030030054901c844440302 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 778994334 1250 778993084 778993109
    0x30e0a0f050a20030c1e03011e0c08042a1701050f070309020f04020f0f0c030403031103191d090403021005012313060b120105092203080901021c090c 66
    0x30f83d90b4078009011140001d08680c410305400700d210b03c4540c181483c440250b015402d2110201016100011241c41414400d10510040e08c9d004021102038008450141542c4c0304010307207140304000d03010711351580044000324901107a250420064403282001c04401e013603545008020088080c0c4440b5070704490301d40340174480b840c00e0b90005001d020309850306900c902c1e40080c4c01b510740d41040081f6103911603908161501c2c0e4404001d15500c07904280300a42c0401c400303002e078101108011040750040b904032a012804900004821246504000c00c100c0c100c0c2120804010700d0b56642e80403030f00c0f0358403da000b0301e5100c403035200c0e820503070b031060b84440c00c81240c425600a02c0c00c0a4140e14086507816a00010519011419803010781581c0e80f00d1600c0541c009298260403a0202c4a541a0340d03056540e244a51140181411030b00ea40116000856018181590029201b458215004801c20002600f8a07500c2010300b0b08815500c02c02048041d41e40f00300b4030421004030b0b0740e80300500046038a40f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 778995584 1250 778994334 778994393
    0x70c0e070e150a0815030703061a01030204180b030a080c0c0a0f0501050406051608070f1a01031a190f0b12012f0d060e0f06120d030e0a0f050a 63
    0x7040da4000d242d00039050085071030018417615460081602c00d01001821034050f503949007020001005102c12208500c113916040d00d20a501a00896040324010006014841e40c0c044030a4024807018501540c14020074130000d0100da41140036000ca9107035640908036418054040107a008501d6105001000d8101e000f0800c0780e80050035501162200d080841e51201160b09646049024400040170580082031090a109036880203690302c178032448003c0031141000c016030913680310034800100a09031424005041d01c407544403c6030000782c9110184114441051710344140d9540d0b210a0f280140e58610982c55403415103904000d005900000300701c82043c044101005086103409140a2405100c0d0741031007044401c21075804418111007045400c1d105c0d0a55400c0709404c0d5520300d074840802c400300343d8074a41820207900c44076101d8010680c180700c412043c0c6c0503000c4e235400303081c46024514141c1c002c25440308c9907072416403090001d0800311410746400c01440385403175482854244c00c501c08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 778996834 1250 778995584 778995619
    0x6190f020a0e0f0a05150d1e0501060810180e01090215182209050307060f320103110604051201050108010c020303010312140d0f050a0b010e030a020f06070c0e070e 72
    0x80c07030030000901b003086a840008001d07d601400310348041301050303000704450790442c003069400181a0341442d41c42040c5502c800515008c1c000f400d0240b02d0051101d061200b04124640e4080400086048008502e202958000401e00d840703a00284039030a1000409662902084242005888045036407640b592450007e05040018050740b4041c0c15549585c1c80042c00020000d480400d54420781c1031100e1602c0d04000c0c00642505180b09541101c0383c10701d406030440a22200c49403111200401009a1075500c480c0d100c0c004004055800240400c030108035511850740070140780001703500104c0c032035141031b031400d084442c24aa074104541040c001840024440400748494030250f150070003081220792a50012482070040e00b00c1000c2ca441c0b1346c0681c01040e41c21031842403107040b0b000c004502c0e0280041d80c1d10401c811046d41d140d00324900190051500f42250815800044c00e41403d00c8481d50718010f11140c03580103422000c2d502402c00c84075a034415460107403600d00b5626000400d440311803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 778998084 1250 778996834 778996849
    0x150106020a030c15090803160801060c02060a030c030b03071215140f06010318030e01171006080c040b0c0312010b040506030103110d02100c050708030a0206190f020a0e0f0a05 77
    0x203000b003501c0107800c0c07440103806042c0c01c015003480c1c00280b047e03a0381c00c0814010941f00b004480e411301040f07220000155190180204400182e0040c005514045001c042100203100c90700040003419544d400107416500c0c200440d1000e001a4040407114144a092514039411811640391600742001a10980d0030030500c0300035041000304cd1800404d0b2500801603000d440244510000960503403429018144c1c0168401e40d010f10a80743c48010701900c0f070801ea1000000c0703407103030120300e600e58007002514406c12a00364441e209500c41414580c4500ca00d41d89a030100307108200f143e1011500d2241c00c03030b112a240d8010300000c80350071b2601d440c01d40400c1c1035000511002e0300a8888044140c02c0b038445503030140c1a5507008000441121038550301500c0c41003035940990311031280c03600c0130402100000c01c41b1941003054004025179616400215817018611203140d40f4183c031aa444d90021900b40060a03240400e910703501c802041510034030500b6018500102d100b1078900300104080e031aa403a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 778999334 1250 778998084 778998107
    0x70821040308031e0a02120a0e1b06041d01080d110a150207020a0f06110a020a030f03110d05090f03030703081b0c060f100e0405030306040f110309150106020a03 71
    0x2042076840359a000000701110071204c0031800404840410810701a8895000b0035003000880f20201d010b4488003e124200c40f0300c406180e0040d48101c43c01506000a01c090707800742030009107054a00b41e120704c83c6c2d8910004c807101c0d81021a000c840144500c1009125030041d00c9090300e40442d40c01008803009a0b2208001c074045c0105e101d8881c074424826503901102d400d1900540b140c00d81550351803034007040d084c4611030701001900ca180c001c0740c446c84c08900948c40c0c64000b40807510b56405c684900d45c28180780c002c224240f02d84412070f44480345080c898107454640b00c3d05c0752030b1584040b01c144071400041030212803080e0020003410000903000151280c0144c0b2014a010b01802d1079001d086140c400c1e80d0703181150307100300420800b162442d25000c6200d8a0114503800c0c03030311307610301c2c0081c14520300b42c1d0020030035042071002401c1c508186d1b0215400c1e0b038403101c010409030190700184070700d5030050340c044020b90441c2d01d0841560100d44203c60040450344001e001175003050f2401841c441222 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 779000584 1250 778999334 778999343
    0x9060507080403081326060a1a040e01141302011e0f122003150f10050901120e0c010f0503011208130302030712050d0e011b06060b0301080708210403 66
    0x85901172403100031140600c0030b0030740d0b180c0444003114002880d1240c02660703402a000d40c822140091030b80d9846003c1e50407200c0b0611004031041d4100010400509000040008a9961000e00d041c40079052088103005900142d4140d8016143d80001080720301041184c000c50282d603044a804d00ba80451550801c864a02d0711b1b00070f41d201c464442d0003070300082d90920f80b8000514581001f1420140080d4004c02c00c02d007108141d010010140200041c80b400d50f075601464001d040313149503009900801c4c0e44001450f04c0c2c010803103d2040d5800310b40e802c2d60420416808010682c3d22540c200518021b9940d10382411801c642c50301070308070201d02c6040001480442c3c00700b18120341d080040401c50145070f004054545045e11080551390030f9640f42c03420b40d080d2060f074032003415045c000d006000c00e002041c0e4900300303210840100102d150b000f912046032855980c0da00060b03405c1c0c3c4200550b0281030343c10041e105503841c0c60700c180e16040006212035940d440130032050f103040403450f0489040b04c1c0d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 779001834 1250 779000584 779000587
    0x5040905040311030f1b1b01050f0d05012c1b07051507051c1b0c02030f1213051c0303091a010b0712080f010e1b070f030906050708040308 61
    0x281c2c60308035809000250b0002c0144404174010f40300400308809007100f6403c000307408444500c2c0c01e00302c0e80e503110000b80c6030b81407000004001540f0f5100c0d000034803000d000307001b52600d4100364048079401c80c0e000364070812416196011090b4034080815414601c1e02c0200074007200350401403503005800808c03c9a00c0310182000a860702008000d02110f40c2a81118075054a1450448405801948040304910915104074464840602544590503688200000c00140c88200f040d0684245800c1d0000b42e80c50710464442000d060070070411282c580101c0880a5183c0d9241c4400e4151b80d140c6400040c41544480d28680360384c949401c0c580310142d00b40c580429088120300301041c07019181d00000f1400c0d06010000f04600141c4002080c500e8070404c4401c9003041021000c540010081e640d6154903840c0400400c480c0954082540d00072002c5211600f0441400e0b40103115a401010700f22819445955890189900b045142c00204818200549001080e54031800d803407103240402011007a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 779003084 1250 779001834 779001841
    0x40c0c021809160e010303090639080a0e0909190f0606031211060a06061b151d0f030702090c0c01110a020a060c14040b0702060f120403030e0d05040905 67
    0x10b08000e41c611640650501c8030b440d41d00c680c0011200002404143e003c18681c0d40005141c5100c0d41e581040e4002111101001091403401013801c0394418180f4040f940007010b4040200d010b9000400303000e02c00b52074480303a40d00d80500b8042d056400404c04111500701c10f070185d4080406860b281089580103411000752079291400c00014106500003820b949858a528140b454001c0394241107101100104c4520307a58021a107815184076000e010f0006402e07114070120003401c00140c881e0588120b00c001d040c0300d400c6491030b0441e003400008240d11151020200c0b0040c2092190002a6501c00003961508107160046090408041d141d070711008000a20359500e40000c3d40b100782a1505038032025610025913000075030340c50f00902c00fa50780c50b00c0c142a8400140c0114000c1030100e20b0040e0b401d08083c40c01c01c9952840c3c04c42c610598102c90100300d000524102f0a004001c5180c1500c0c62500070b0400c1e0500500304d03442c2070381d03801c816440381140c02e0149130070106603000ca8444940200e0140e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 779004334 1250 779003084 779003101
    0x6120b04062106270201080603011b0e04060e06030c09090c130e011401080606040c030b10030204380a0201020702030f0606151908071112040302040c0c0218 69
    0x1c2030b0b90291181c1c45904000ea5200710408140d0b81d60140900d40c14404007803400010f000041d104100103030b2038607240c1e03103d4005500450856901040080c00040c40340104240000c4a0600f0250800001c4101296540d1441c103441064040c00c03040f0281d1b292840c000303002c2070740c407070200c001103210720381c1e082c00558500750070040e5100d02074002d000b1241c081c034106030a6019005448081200b5401c1103c2d04040080d21082141256080c600510310303901c642e018803000741104004402003507280d08180144c0e4650360741c440400d05050750700580d01da1515804100079900060140380f5240045101c15011982c4036410451403800700f1020f9803004600402d0b802840742e80300c000d416001d030300700e4501040d0740820014810842540d103d08008125011083c4070303c82d21a458045940e601c41881150740f01c0e4242580c054024200404402654060140741140e500f402c4007000e0310024050045040034014441030130700c1c90038860002c6449a00040e0620036011041103000182ca0000b050b60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 779005584 1250 779004334 779004341
    0xa08010e1b120a1b0801020711130902210607020706050a0e0f0d060603060608030f07061d100f060b0309100c0905120a02090117100c090f06020f0705030706120b04 72
    0x82c2c00d69011076045611615201e0800714200c074162002d107041c2c0d070001594081c10b0081300e00c01a80807030300442185600e0f00308901c04420811001c8208ea560a0031001038403100c200029154650b180c1006602410030310030701d014001041e074401c5411881c3c04112041c0c005050f1000c46005080c01d441105218000c5041081082146903000490b1030a480c144451980305906a0707000300014004680c640541c0c0740d03203124440c4c04081c4c40108100c0b4401080c8070303920200c00b140c081e07220000340e805c5031b44505141001003d0010280350340d441c544d80c49440c42c3c0c41440000c1c450400168191310b403040050b915094004001e6000540301c00c440034026102d1720004000d80740050084000c1241410099982e601c1030380200d014080c82000420703011381c01c03120035160b628104020407562000381040000340080359481014040b2807074000c42c03005c40109440000d440d8982c010043d1b0b080070080c6618000d0b195000703500a0700842024044c25902843e810741180d103103840802d00d1950b400c04203009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 779006834 1250 779005584 779005609
    0xc0702011e0e010314100501110703020901031208010603090201080705031008010e07030507050a05150a050408100e150c2703030a05040f060908030a110109050601030506060a08010e1b 81
    0x2040e9118030200c1d08140c010314038510120080e80e0420400440d103c01300c203070380c805948046005102241c03c010540c41444103100306801441a102c0a669960108030112800c2e0000c440d811f0085030483d1482d40e0004886004120b90700d801d00c105801900060004840500048200203000000070b550000040140c2c004200c04402042909074030050a43c0382e09440c00115030034056050001568680509408181d0701c00a014100d488504041c590040c0d02c094502e509200050000180c0183d05200741d4000246034580400c00302030011000e81481074084414051041c000d0511011942000c16603e90114210005003500d89001d0000010b03200413202c96414480001e441d15501d910802400c12907558855a0340455101c04c0180e139103506600415809500602200301c0b0540305070103182405130034400001d0741c903516807200d50500000740c1042d40c8a510903000d0158504107800454000d011202c002c002e5281c801450710345800d001e0618105540040e0410500ca60381e10480c00074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 779008084 1250 779006834 779006867
    0xc0307020a0f1503020903121b07090614030f0a0b130507290313060209011419020c10090e04050c0303031005090604020a05093c120706080c070201 65
    0x140a50310740a041608000340500f4110900c40140741503580d00034001c0c2c500a54009010b80f0743d0401d080c603500300301d030415403513a08480107100d081ca40da00c00600030607002e002304110104046007031030201600c1007030581c1154000e43c8400d101c003210710408140c940d00c0700e5100d00595480d07183c8101c0c080c41c15850106c05480b60040050001d0f0301304000780380d921081340c03640090281043c50901c130030140c08116246442181588644d100003003241c3d00030440242c05052040d6503507102904000e11741c1040c90000590941c49070203107903841d010401014640c808a8940c814418070340301c000d0070a40e603441110340c0803144c4004942088801d0008070344a10020741104d49030b20b0481d00380080c044491085034064403e400124169040c58000c50b50f042d01a500c905140803100014002900d007160700c024800117140085040d0b40d18455a07a41014400200c1d00602e0400e4000b00100882845603c10321540020001c0140345d41240a207607010003100205600c0d031000340010380e44044241615034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 779009334 1250 779008084 779008099
    0x609210c180b0f0a0302030a08031906170f0606220207080703021507051e0c071a04050f040e0d1b0803180f012a0905090429040b0c0c030702 62
    0x10340d82555401101040800c88910f003007032502c04184910b03580c1c0381c00081e4042d04000807900c00308010000564000c4000d1801000b1441e400703425104841c400d80142001e0040b241c110642100200f007101540601c0502502060030210001903005000e0109115041c6100d9100080d410050741900e80d0710344c10400d190780d580020718000b07440d005401903580252000c1008200018400c60507140e0150710142c52003001004130281c1801303600b010340c00034454421401d01040c03c0c1c01404800011942499506032142d050000300301c080e00e00004200d00940c5401d075440c50742080041c003240051803a0405440d03407241200d40c200065900c46001d442c150001040c449c045401d0405070602e10302003003d03606201da068554501340d5030b49940d164699166078811201c24949084d020004400a0a0031343c0056550404200558011a010790f0100c2d28000d007500d0265640c2030b410402d4030f0012003010a45801d54480654184c0a8481e0360b66090206a11014500c10021109907580090644 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 779010584 1250 779009334 779009369
    0x71b0311070b130b0307020303040b1302130c020c0405090a032601120605010b5d090a0803041106040306020313110a0503071503090b09160609210c 65
    0x110441e510a0001c8009419248800200c5122100c245c0f8058801540914959100c82c0c848241d02039001d0000200c0b41040807074140180c0d0b60304003160040841c800049100750f1441c00c040e040034806040c41d80220f0618040000510010445421041c1c4c90304103c0701d54049000c0c2c001e954141100e082c80b030901c00000119003540101e40c0940440e01c200d50900540e0303202c141000b8039000740000210036003001c42ca101015000035070940a40c0340b8802c0300324800c03940400300300540d0b034001d840d2840d2568040c50650280d50081c002d10350082d56074001382b9540d640e59942e20b602d448010009008a04003203001d88081e82e0b90b10880d0300440e0400070a40d101e042c00c44008040c4105048100c601c4d00f2803401480e810308140410a049844c001c010340b826501e00680c9181c81c000c01c8a800301090358408481e00042c040e245010300940d120402868092101c04c2d0802044041c0d030804414440410010000b02102d00c011420400c0343c03441c8418601c4043c0b82c0a0880840c45d00301c0800c01040c0c6c0040c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 779011834 1250 779010584 779010599
    0x1002010902310504031209061506140a0513050607060b1e0f120c040203040c1503060b0a1808030c0c040b190e070e18060117071b031107 60
    0xc40d814001c45411101e480c81e4034003030301019000c2c103015500e08810080c1d4040d02d2180c0d40529441802401c09502c400c01007111403040345e2038000d0131180da95031040d40a40141882c055000030f001a0304029410140c02001107006014103151242000000141e80a0b180d0001003040020100601107980764180c518002d0090088800c8140c011a09810340300e42c9503100308201008018083c148004812070081400302e01e8413449486a117170722a8407a244c0302c0b030720365100642c403130b5005500192071a4102100402c2412000c0100000c05081441c14800b0011300c208490025259041000e841c03140764841400701600c0394444507107404003146d20b400020300403d03001c24600d030485041200b040020104140c90456900314403003018400000c0c000e0000042c0c0c09604020380e130410b03104c81500341000030031020844a1800a00b4504810f0003a1941c20608014164a10304100381c503910740084018000d40301d82005842241d9500440018180a840c01a045909038030540e40000c0d211001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 779013084 1250 779011834 779011841
    0xf090a0209191a0f13091a100905060a09091109091b0111060a090f1e02040f0b0f060d020403060609060f0602030c030f1305030d17010611031b010b100201 68
    0x8101c00b07120f08103a41564014120340d00c00c03005080c028410302e0000140c0f400d10015030700700c0491072003681d9a54a010041210000a10803025100b1074a00c554507000e100c96110b141140c1c00001c0403410213007440050742d54564034405035203540b6400601c05019081c8122880c400000301030f00f000c5071006000151002086a00c520500245d030014030011b40b000450300246000800c820541021010401021aa4200c01c20703840c081e0114112420701900d8a080b908403115210400e0300ca80b10740d070350440c10240141c0480712400c440400c02c050901c4c000c283c10110710501c1c0d074820400058010380b0401d40c0e5058a000e150802001c01c00551100782c1240100344501032000d0b4070b02640c00016400d84004110f803000050308019509060340c400703424540d5000b40007500c1d00610346c820b020134140c90400c001c81820f44542d40302035840580d180107001a070010f8006004004c125100d03140e1a0341c00000300c039120340390900c0000340403482e0035000d801491504840380e441030181100c3c0c06800d50542 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 779014334 1250 779013084 779013121
    0x180206030a0c1107060518060903031303020a051e0f01050d1406030f06090d18090906020304020405180726010c020d11070f0b070c0b0406030207170a05030f090a0209 73
    0x321030440c3c0f0b0031a500c50301c0e6120003500c603900020300108400104c10404040020610304090141d50400c1907000019086070064414001c5003901071800300b0641c91309400d24802424140e8005c0c1d10720200d20f185041c0b06481c04002402520200c0c04107405034803420450380b00010303503001007100ca001c2410340c4604a40030b0780d01e0361003440307607040740c91142c58041b4955000300d11940c02003140801c0840c003520818210500c000e0448000d110000d885030303841c02001c051038415070b401030ba00c1c43c041c4108012960302604070b029140702ea2003008036242c4005605410f5481483d00b0700701d9140d44100c0c00f9003c0c3c07a4040c545d070a550030030b012101b2140c0c0024902403004a1511800d0203080072030103555444c950b9110340a4400c4040008010f100da00e50002c14020740076103500e924507512420050003680c45507010000103940010100309001460000c00b80003059032150900d05841d049000b0300c1400090300144c0041c10020100301414000c21030782613600ea02405a039454a0300300c1041d0032076903000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 779015584 1250 779014334 779014337
    0xe03040801050f0708010302090415020307050a031a0913020d05240a14041e0b16121e02030c070606030303020306010306140d0803100906140102010e030703080a180206030a0c 77
    0xb07003c0b4502032100c1250900c50308603541d41c0c4034642e10b0f603020003400060141003030316142d98610b400c600110590000714400c11240c4c80d01540c54007171544c02400ca5250156402101002c070241c08800c0ea01c002c1c40d030303401c08615a80030491581d03900000e0580b02007420000c0a070302c600d0603000c850441001c0c1c94a00040b1407558020141d1b00c0220b1407040c0d800c0c035040e0442c11841d1000081c0010b1950f0b0700d554200c241a0801c850020b256501d40e19034103426280c00b048030311602c0c0d180d400c0a41c49031039440202c1d002d035401d00094052505111440d81840c0140058980100000d0ba00010000c00d562103140c00200c01d00646640b800d0140c02540180c80c4980028201103000c5031071140501c100d0f51500014080d6060070035580c58911660304050700a200311149d80c080054004080d01903040913011609084222144140002e802c445001e9141c3d0060380051141a02191f0000e00c1a0f82c00300250703101080318815003500c0c6c1c444402e03905000303600c0803000c011b004404649070b10010307105005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 779016834 1250 779015584 779015591
    0x305070e0d050a1a13061d030310080706020304140603060118060e211b01120603140d03140705210414060703020316050d0905030316081003020a09020c070302040e03040801 76
    0x480d1095640180c100c030b040c00c1c5c80c0019407146000442642c0221800e0764004c00f2801580310240055046501c01c2e1122410020704a00a00c1400c0050100900618290004502e0503142c04550100c2c1e2901c025598030840010000031200c1e402424070b4606440344041c00e000c00c0d0b0311503c0107001c403a400081c8501901034850740d030494425080c0e4080344aa901401004040c5809176200341080c6198003107410000410b0980b480319030540120b001540c410000c0c1c9000700d0200c04e509181030020101c0000701814080d040c03140304200c0358126040200c1c4d2410035911072807000c2452030b49420a014902113500700d003c10082c0300695800c2c0180340c101ca415100b0380d0f22650400c606a0100782e4414165101c1c0350610949140110028061401c20a03401f04800c50039071103d6080d50003c070f450461910306010690101e50f8021203c80d07114985294807246c3c5400d5802144086a49002d000314455001406040444003004000001c0d6401001401608400820161203030450f10442031250b09 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 779018084 1250 779016834 779016863
    0x50919030e12030307050a1418040515090a020d050c0702010c152003010302100906121802030a05010902131a06030901150321090b0706051003081801080916060305070e0d050a 77
    0x1444c201710f80031500801c2003184401c9c102410080101400b6101d90100c0c090380700c03502c0e42c80e140c070b0086601c02c00304440f0050302d410b882042c5409031040140360a281c0e442c104030b4140103030f1300840d5001942da0082e0740b11940290f020701420040040c0d000580241c0e124012944184682000440c142da2080d980a503008040020a65520103907000d20030214681d5400e4129644442e4401e00e040249860703000c00112060700800d04101c80001e094980b0794503010201d00794200307010603007800d0890f6030040024407000084020030110000d8032510461001021840d203107025003100c40e90500b01242c0c07500f031554924056010815100601511264000250321410301407041c0c98201c0b150a03074030b580340c814244d90300001024001c2100d41880d008a03004000729160001402001440b140d40b0210f4401030800504081d00040c07013070016a200008003800101d078540741208451160401280700c0d100d580c02900c00c10f07205007002d50403003140100301c030500000281800f01940100c0285140c4c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 779019334 1250 779018084 779018117
    0x32a011202180111100509010c090e0702031e070506070809010606020f0a120c0f0318090c120504020f032a010c0f0b040c030c0b0c01050919030e12030307050a 70
    0x2102c801004600e50742482810550081c3d4100d010724100b64161001c1ca5002e110603421034205448040041c0e5403000985003998210150318007500c0e81c42030104d4185440c01c0001d590348901c41140c1c0554803407018515000080c002034448880c0d00c0029101d203440c2071500100035107401c0b0b4003030b1002d41c240382c00050384a0010940043e001c000d0360182c41c0085254441d000d0900d54000c101c070030007400400c0c82001c1124200312501d1148259184028032030660400d812210886d001107081514000c0d2142c0096080094590850510100410503564500029640705400960117405001d10b00326210502c005001154510350450081c0070005414001101d211075030b0840100a08150030b02c9a000c6400350300c42d65802071180440802c940d40740d6413040030016050340040d41210001c60702d40042c200a000d1554401c244200502581da02021968005040b010000d414030201c01e0001d81540ca942c180c1c1c05d0003a0303525040701e41e81e0030039820040a55000c3c40507080004c5050155443d0708 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 779020584 1250 779019334 779019337
    0xb031605030c01050705070f08160501030b0f0409020d0206210a060803040b0d0e0d030902090f10090c120203041119060210020c160303080919081206032a011202 71
    0x3150050300800740c600001c801074a40307a02c00d410958891284100014114442909078000b40c130300340000d00306110090084184600340d640089041c142000000e90160f15100409641001c0442d40854142c195002040e02d0307002170100a9048180022401000107481941c0c9560024070090000d0039a1030822220885071240604184c98204000c01c101d542501401380c50035035282640014070000b080c0502c3e182c00b40d00130966002c01c0d1a50103180a51070200031040c1c0c05406d95240900300d180014200e001200b0700d0240310385456542489a0740d81d40b1800000c4c92219600c0c070219924109400c0c000d03187c1c51540b15241c41101140c105038840820101a00c040300d0f8940c00800c1084038400b6500302a4004501c82203c038403405e0440380250190300006c10046019840350f40d00c90812014980c1441220001520550035200219000030001402c480c0341403200080c460351522485d001a041000002e44c21081e5a44c4190070007902c5407000d11050004c8090f00d82882e01e04419041d50281d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 779021834 1250 779020584 779020589
    0xf07060f15090e07060f180e07030515010816020102070b34050909040f050a03080906181209030307020d0c05030c010c020607030c050309040c02030306090a0e07031205070804090b0316 81
    0xf19001540c04024050142104800e50002c609002509021303000d82c503842c5070381da9400b645882c5210814800e03c190140b00d165004055180014440d4850760006450058050010409100c64582c00c3c05154400c0d0f05032150f01d0360202c40d205290500452010305d1a040c803001ca12801c02010781080b0191040d020741d51170705c05036218503007030103940b000300940c0d450b00501c141d46d5404908854000107070140011006144203403134003451410840412483c2c0038009040c509628004101004200380016400103011f002d0b402050b80c0b030f204c0c039010905500070780e40000c1d0048a20340c0ea80b010004441a030001380c40090b01260f40894030341c0011202d114450310b0283d0009010030107500480d10a00e000a0300742d0280d030440e440e141714100071408480028081d400142c002105000851501e075510303980050b8040340600c540b0034105c00054865069110062105505203c5119189c2c00340003915400381e0400c4006441e40d9581110340d01800010b81d0b50361080c003031300d1a90301c1d241d440415002c05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 779023084 1250 779021834 779021861
    0x20910050306030a0c0312030606141b012409180309170a050607030c140c06010e090f07030804030201030506180a11091e0102070b03040b0c0f07060f1509 68
    0x82094540303510151000b5010301940360716002040c00070311220001e40c441e42e5416525521044024222030356508880c003000f4019029070401c000d120180e40e50110100c0010200e03414403a00540100714498183c04c1c02001c004000c000f100a515a0303004403051a60103200211a401c148503400c5070042d0001c000c5400110240310f80c20000740e405440c0e0701c0410840d1f500100a44403585040d0088810000017629030100c800031641c001560104180d44040590030700107d6613005855039814022095044c0110300002c2090341e0400c0b541070403070705034000d450240d03451341840e4050390300502040c1e000c0380c10180482c003981808002d1020012200001e400d480d2618040080a0400fa2106c0d082c40507050044080d159680621941c110301e4695640610b641c1030700002e424140d2507800041a15414410000801c0c0000c0c102640030128540b056034448488154040a005840c80035054901c0c1c40c0c0300a100c0c880b9a4406034454074010f506044040d941d0f00c0034001d49407110720114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 779024334 1250 779023084 779023099
    0x15090d050d021c110417010908031f0b0412120804020d02150d020d0501150212090108100305010e010c1407020f06031b0d020304110948030402030d030209 68
    0x1d5000c1d030264007420f480e4141908548008200200400c25100e0a20385800c6501d00000c00700701c10180e00b0f503000500d1010400a00413000c076926468040e02008004441c111041d445031a8043c00042d1074201400c10f50401c01d85031034440502000d210803401e412100c0b1045000c80c00a214020701c44503118581c024603c51080c0f0180c0c0c24459820700b400440080c44105200c020520920341c000b40410300b241c41c000042c1580340286a100c0b540c0405503000940d000081c0b900d40030f001d44011504147e900303080c20842c1c1e4031480ca40e014810398582c405000ca5192482d84044258103402030240312a036541c1e550742c44110703401020f103d0300c500203009610500422050b945414164042c1d0351001c0701404601141840e10259481e96000c4188410000e03030000c200001c126080d03000901101007030f101c500081c60300448007492064621400700c000c103072814a00c0300701c140414200740b14000c2c0100d9030205038802460300300980c006442c00c038401d010b401464402c50740301e03209644941c44020800c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 779025584 1250 779024334 779024347
    0x6060d05030318010e070b0702090a02090a090902060f0a021b010906231306020703260304030c0203100c02010c080a02182e0f1b150b030c09070215090d05 68
    0x1250300707541c03c50000003d9504c40c012034000210a0103072500030240c05030380320b66a50481c41080301820000301740600b8544140003130060b54a8015460060b02c56006000500101c2400004c4841c051481c282c00c21040015405102540c0400c42403c0d8241000359001c581179260015289000c290080800141401c0000d000c5000701c0000d00203c1d80140d8621450a91042060003111160f508001c0251f44010810000c204150901100d0f404100038412110141c142040c003940c800540082d08200b120b80040c1c09642d4284546646081d041a0401c035124019001a000c1c01e50b14075100c002c01e1482c0c0004614081d039000b101e90000e50404501250b070415004c105104c00c4940c0c08102900070981e08204647d00c41240c807184c01c8a82c0c62700081c824484000034070045032030340150054888820441c0000700c1f568015540035107a02c20201d914081c460210340784c605101110f5074440c4030075042c00395581e00851144a40140241001416699245e00300c2d92440b038030004400040082000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 779026834 1250 779025584 779025601
    0x9040809040c030b12030c070b04030f060903020c09040c0f080c1c0312020a090e090a032f100504020f1219060228031d070e04020a0807150206060d050303 68
    0x10b0914814036082c0011501003035004141070560f021041c60300d5074800240c8980942c01007150500400c0c5042e8010b19160440d81d8030320302c1b001d00e010028011904d8130034030b07401c15000780b0003902e40000140043c4280c0c078041c1480c020410991007400098040050041100b410110310b842c4001c0000d00080c04c240b80f0242440d01d108480b000540130401a0030b04d03629508441c0c002003036240070503601c811520f41024800158800080c1030794805501551410002a070010b500300002c0c00d04003480c03031104c180620302c2d005040440500d40414042c42c03402400030303000b60744100e02850081e14a141484e108070240316820b15980384041c101c0d03101401c1002e61860200980038000d100319005418881e84255540d150b220841c461003c0b00301d000ca0020800d03038140301d5410b20704001c0860117001c043d00c940707403070b1038075400d004611005114400090554a60b0917940004081c407d0403103010741c0d502d104550064012284c451b005015890100300507203401c2c42c650340f2135504071b03000c2c40c0f458503080d1a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 779028084 1250 779026834 779026841
    0x106051f080c0322050703060501210308103c0503120904020933041404240303020706031b0503152e02070b0c07050613150e030c0904080904 62
    0x2010358811204c00c1c0c84600d560310925003000c1c144540b009101e000d043d0314003441619030580244082c4038208100da4440e02070100e01840003909810000680e459200345010668441d400c805400c0480a80201c6031010040904010321b5241704075010f2011526044042d80629214051303050b8010b080e5600c200d001e135401442100001000140782030f4a80c0007007011002c00d851500c8108816641042d6440c28090041c10520300c0501250303c2d007420401c0790304003040e41d03580d803034000c581d42c0000c00b00e805a8031400000010003202c10480c5540e50341780003907482e006d9020700c0300040c0c20300c80e000c0446101a080f1a0440c030560f1290f6045a585012540c4a802c800384200d078030502c6a810781c00c040140b6001c14070740002c82c144d0660420000000a49010b0256001440d401420455041d000da4042550010784404843c0b0a40d5011700c40c100f01c050180e10303000350840d02230f8108071044c083e4020b015800e0782039050703064403940007111003001080b680844001c5c082007420401150240350650 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 779029334 1250 779028084 779028091
    0xf0418090c0f23060301260307230f030409050a02091e0f0a0305070501050c1e030a030b032e0207170a0e0d0f030503040c0e090106051f080c03 63
    0x800032400d40710450406038942c0000741c4a55000800c1c0030905068070074103592882c10503c900c1031154140802c4041c801440740c0d280924071811102d001910100c40e02c407841500c4012a529800c55041183d85002c0280047c5040040210640540500858a80b90f01031840d409181000e103844444400340c100285440c0015a080020783d845541d04583c1164884154035800303803201003041070144540a0021042c800d00419400f040000c100007079036000d417102031038950b4488040500c03403483e000c2403840e823410306d4000c2803000b01201400030181c0841000d5607011700103007845c40306058442c5484500c0b20041034441000740042d0344110703150880200d850f000185091882c2c0c0307840c405400e0440804000748000030703882e0b41075581f14030108943c41003206d281d0480403072541c404040c3d900442c8014207100e8088001414031608a1204c4010f0208079001c00192030028891030003001e860003000d00c070740d801158840c010300c030b082d40f00c00410a45440c1d003a065194103001c1d010503000203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 779030584 1250 779029334 779029379
    0x1b09030605060a0503010c1101060b07231e210703230f0408030306151303030f0513080f070807150315330302120c0d06051512010503030f04 62
    0xf20300000e02502c0c2441141d40d00c4a01b036a40e03030100c204008955003580d03803550001584c0b03e018020300c40403a10006522482030521300802621006207201c160a1052120040d10001c0003002544610100482e07890b00360040609200302e0340080d80e01480c0c0f01c1c0620a0040d000841140303001c1003840c41400d01c3d12414141d0401075082000d00d45a00342c1540c0103070131a24498002106110b2182842c03848005118098030f01d0601745a08444010504c00d035520018082050220032199101e00031811070341e01072141001c035500203480300341c016034032020020756406a11902c3e500003818040400c40703005480d01c003481890b400040711411009081109216400c00c0341583d40003580e124065500e0f40c844150071070303441108000e0381c2564a403151082d048028580100300c48003400c5d50888850344d000d2003400040f42c07919524407421000f001d242c3c000ca5005110207030030018850701c0700e014080c80340b0300010946060707803680181926401007102000300e44005000910001d003402902e140301c403120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 779031834 1250 779030584 779030599
    0x50405090907260c330906040608180a030819110408060103050d0e0a06110a140f010b0d11150c121905030f0402090a0e03070809041b0903060506 64
    0x84140d030b441d071501c032880d5156034561440d250380c004040601c000c02240f8801c60b80610b96451000174540b4030754141030300f15051981e03034400d41c0b40828a0b0041d40c101400103401c040c0c5441e1a000003030302a031030a4644c2600c000d2550001414000c0000d0300c00c24117540342e51101701e01e4940703204454080c1851908560420b842e01945404401d00f04080d0000b02103403801001c8a500d5400c0688c20030000a21380070410a11064000e03154940e048507000f25007003482e068042e0304100f40e59600308140c00c4002031881c0880250710701ca003200082d4504030809030000810001c100c64082154400b900c0d01c2c0100740b00100c809459841c40c004804480401503c2e102c1c0b440e08200040076820009020a062410100410301c0108445069200b0808129604002c3e146040140d02c15180c1c41000700024421040342d400290014829000040c00780040e6003120748481e8036140803842900002190f50140c0c0c0740c41141c1e01d05c1101c4100303120203141e46407684855241182c8408001e07280081c10540c00c1100f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 779033084 1250 779031834 779031839
    0x230112140a0911060f161e03020a060509011503060e0106030c0b0301030302100605031b01091a0306030105371401061101050c03070e060304050a0f080d0b01020d050405090907 77
    0x120400162068041600001d1401c41c01e1401480f44885803406902480d014041642070314105011101000f85000402400c13400354501050400192410500b180c0c092003e05410990002008000548500303014040c0796220010301d070032100364141a00c8000c1e001001080802c0b45540300440b21901000040f440e00c0e240e071901038140341c1c02d41c05445140320001c01001410b60601400306110380c40001444000d00d06000079640300030102002c04501c1c028101e100040e8000c0250000510341001c0c26104801982c0c0c2c5a40182c1088030524082d5082c00005143c82450760102091401c0c1140b5003088540c5014600d4420740c4a00090364202d0799034590391010705280341100e402050295200500c84031103d84540c2500d801a04a603043c84040c002e0203400c60700140058510902554400d0b00d135619424030502e801c3e007000380541100e00e4814403400b40041c4800130f07c10000d50000501280415400481c1e8500c1e034030540d42c0c00200d00740424042460324100880d08021020100d03640d664 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 779034334 1250 779033084 779033111
    0x1710090504140f010501050901142101020705070801020f1c02090402030414010c0207060f030c0302091306061b08090f1f030507170105060a08070207150c030801230112 74
    0x900541d800d403960780741c01c540b07882802820000e4030412880c0708000e000c194945400701d01a46410301450103444484159890341d5120205030700c05000c0c0106400030480b015071109030003540041010344442c05072200c00b09a02005000312070300143e007800060318041604d5080810440c5914040c41440d0b000c03c00103004d0707640d0740040c502403409520f08210300f03c1421102821195100c1e087d80541d0080c030f00c200010348c1c100e81d000003220400d00303000c100c48416081c100c0080c4142d0040d03e40c4403694226030a044c1c4c4050703000c1c005139049034076501c0c0d03581440030004000b003a00c5400109088010040850706080c0b06004c5e020050014041c00321a526084240c0525034052801c003001a42c0c0700200565694007858089003450b403040f13030f100035505260118070b181c41000e00500c14001810003040c0c0d018070801c000401003c2e0400d030b202c044407100d080203041b03a81c444410b50004803101d00115500300040315800000c0b4a5110180380340180d1001035605514800070b99203810740d11007004c3c124a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 779035584 1250 779034334 779034341
    0x15080c0f0403052d06040201080c0d060f0501111902040f180f120c15150308211006020c0d02061b07052e0e13020d0b011101020a171009 60
    0x110f102d40d02909148400c0c6a4980e82c2002e000c01304a961150910b40f00c440410109080b508242c0a1a00240703565502a071030505116444108400b41c0c50b0420004207041000600e405480b400d0b40e400009111119085603030307038009041da400c54211081840700502e40355024402088003c240801c9441e00512030540705c044020701600d0b00d07035442e5224401c2281c000300c00c0700410210b08024000b1180c0362a1502c80082d020618400d85075922400c104e01003003111144029540310302d43d180d550212280d45001200c1000e1401034054424000c5010390b9071031001a010b9900d00e074010700c00c0781c10700403c104081c6440002070760440420420014103104a00c61401550140e20003020580d207441d00740f02102e503204c0c911031984100c6094042c64403000009140440c1403900c0c010045070502c1000403e0200c0c914501264244002040b6100034240c0d002114400b8098907620342c64144080310b28280e101d2030790224000703080c2032044100b4010850ba42a006000040e90588040d111403654044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 779036834 1250 779035584 779035589
    0x10302181312020c0117090a03080a0b030607170603010b221103100303080609042102010b1e030c0904050706200d020102031f030c0621050f0118020415080c0f04 71
    0x68000681c84d41140d60040c1e07440d60200507007550511245444640c440d25003c0b0400300804000a1078003080343c0602d5504180c110610060a41c2c0c8a030810382400313040d09078000400406100d080b00094a50b14040c072a60007034017405000303d428041440086000391080c81201c0708003030b81d520103848020491101561003110901d9844040300c1c1142405000c101d8000c0040d4410b030703050b104100010340c0000010304100c2c0440071031203540740310110980c0944810580346410050345200200a80c002030b00c01108444c0690a40b081c220b14981030003806e001c2201c01400aa026070010840240304101004001000e42e400180c02e10217003c0c55414800c6501911005030b401105100f000e56141148600044008682c4071080349550b50390080760407948541005c2c000b100c1440f03d160000e070000c8007a045121481001249801c10580040e010203000b410344075980c65552848070b48280c4210740545090301d0481c119940d000720101e5048400620b07a00305880d040c03000c80030000b000300c041c001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 779038084 1250 779036834 779036837
    0x60106090603110310050f0a080d0c0606090504030e13090b01090504030908030406020d03050c07061b080c0702011b020a0e04060b010e040b09041713062105010302181312 75
    0x20900d481e0740101030700c06400e0035011111040045c4001400d100c03032044104c171400e0342e02c0e007403144896000516429650380081000e001c0c02810640d2190b11030a034558684c0305040411100c3c0d1203c159000300c030307400c40b4020007050449110b4041c0d0b2070052825940e42c03811800209030808a90354000800b0820b9001d5141151240c05010805030404208005010608010b41c00c041c6403c000075950400315081200b4107580b1408140440c0d1003c088564103900501d051080040c640e10b80c030001c84440000000142040b80400d1000c04d1950880d807016405035920f03004510309840304511000d040c070701281d00404c0c0d41070006103445450080d0740f0860003040c00040c0c006801c40090b18100c001c00d80a0b1149240c0040b02643e9500e942c00c2c0b40d0004d41000c02c9080002c042e0b04401000d203c0c110261924452055001900725403100b46070101c0c1c1c5003041c005602c0c00c801080310f01680c03020f0000035840141802900040c80b0749008850380080d00b24510300f021000380d200c03d040081c00208520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 779039334 1250 779038084 779038097
    0xa0b0408092101060801051003150f0e0a0303050105010302030c0f0319050f180a021e0420270a0308031e0406090308090a050601120503071a041a090613080c060106 72
    0xa0b855401e200d14002400c100c0000e01407845c0c05070100c2c84184c02c9010051540d0180f03400c0b801024603c2d402035821307080e080340400443d282e00081d566030f165051b20840019007004000f103115482402520b01504000c2c03015801d0650040d800e02050300000c00c0707000d00c03104090840d10307290031500409000b91480c1058000e1800c00042d015480c050804c4202600c1c0d0100e1401d00058549042012400f11940045900741080c40b000601901c1d006074910b603440144c0d628075118a59450003010480c2e013003e20359192401e80c1070074502100d59007141075882060380000b000403d03950b200559010b200400c010782000c0116004000101055400f554080d984032005002c0503040280c5a0b040000381c00104560f81e03080d9581c0b1398400301402606100e004143c210000c0180400540d90896803040da60440c04042c855060000c3e80c007140c05441c59514440c8800c510401c08241600903503c09015008648e5250711550501400075000c41c0d048408128030f03880f04905105143c080c00340380ea90792 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 779040584 1250 779039334 779039389
    0x50d0902130608120403050613060e100c0e0102010b030d0507020a0f12060501080303090a1403130914161707120504061d030a0903020f0a180603030f110a0b040809 72
    0xf549400e00601030413125010810007800403800000d107445c0e002c50030f944607452010311490030704098030348114421054400c06400800411903174014880c84211170b42e40c2c00501522600480c00c1c0c503101000c1903015048004280f07541032290004200c00c40c006031a001003c0d0303440c800300c0502d0b8110750118441b80c01c0f02140504020081c0203150051400303000a500390b0038408607946d02e90048010003001603071044890f015034a420700a980346a00340e8402e42c1001e40c1d5038403181025003203920800a24041100011b900041c602240c4040e4240c550780320402110000c25070300610706c2c098880401d0001e850741c01d0f881d09010340142031040e4030031800464440e5a000102a0350742803008041c1494109201540301039511801000480e50112440f000500c48d120103e446184c2d65000b40c41c07152803081403109418840c1e04000e0131244a6035440d03601041554044a42d41d0791418456007941240740b1140104d41c08040c029042802038140602e400c51090000d20402c1c0720081c0040e10340d2206201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 779041834 1250 779040584 779040599
    0x30c0c1b0316050f0d0201030f0f050a1b080c03060102010603060e0307020f012109060b060406081803211906080a02090c2104330510060807050d09021306 68
    0x1045821040c6402e82401030619001401912000c8602402a02c0c8107128806581c0309800a00c2051703074101d41045201c40c040300d4a80030344003c0302c02c0010310b8100079030100d807010031400c107804941e040d944d40b562a8a84900060705d070740c0050b1030141190348608001c0086815482146801240d02000f503554030594814013107441e640d00c1505050203001e080f582c98003200129030f80780c101c03a803500004080081d490180c5c020140244031980145000c603000c40c140b07401c8019039014000000d0030408010030402c00d00c0d520310880000f83c030b03860360700e02c941c804020205541a400c5031086001e000303034901010b41102101c4850380103140f9584540448015800c1c85c0881980003e00f0b551254038120715200c03048080c1e48400340e00c200c140545000036041c80101440b140e0704503001c1c0d41c0800401b507442d002c0003800c90032060480071a460107021842c02e407640c1122008071921922114060341e210034003910103821504000544076110142840140e986510702c8580d079100d24070001d86107040444 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 779043084 1250 779041834 779041843
    0xf03140f03011d0103051f02070b09031c02030403050d09080702100f0912052d0601030303050a0506010e0904290c0703180e28050a09050d030b15030c0c1b03 69
    0x548250101000c0045c40881c0b000700d2000104000e11207003102c41d2150700420300084c030805201400185580d401d006600d20040010301142100144a4008040d850090b40481c40240e0b0020003040003001014101d409541002e85003d0162801034142041d03500422307007260b129049080000d5210000c4800c40d0b41140300c010103048108856400942556681542c9183c1440c2d4505c400f290f550040211000c407525490042c0c0d079035015190039503540c1c03030050040d09056504122042c14240050340951203215082210130008104066585458507451212501401c0c50041d4001c2c0034410541d880c0300d990b4181c0240d0883c1f0340c0c2c59a80302d05080050044002441415000c40c00d4031080000394241520990451110710b2404914022004c1c80e03003102d2680c4c0181986a07041004000c603101d100e52180c1d400c54010030580b484a50500d90840407510001d202943c4440c1080c05450b417000b206015560004003040c00a1415141d0f80b140340c54110380703400700b0440d16251201102981000c1c072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 779044334 1250 779043084 779043119
    0x4120b0a062301111f020d0b060a0503090d0c050c010e060906070b0105120609030409050a090c1d090712030c050a020904050f0d080f1303020c0a12050c09130f03140f0301 75
    0x806040c10b5600717100301e000722101200c4c0b00803001c1d401189003030030700750389a0080c0001c0d40d000304015075500080c0710140641e04200c4a100c00342c007592154103003481c0075449400407580d1010241840914607c0103507005030078a41c0c00380d0400014055000d0710344a26005001d5103002d6071440e01550315190401c104281c1e15001074402d9048001840400e02c0000283c07401c0e00d607048004902e40c0d550702000c400800b051035004d450786484440002d05154000d44a8681c00c02641c141d20b003507139035001c4031507641c40c55100711001c2c000700f69500f401103403103178034000d0700d191240b429241c2d03070b8119130006a450f0780f0a88082d030740c0d5080900411014502000602000419800c110071113242106802e41046c0c40100388000115245250b070003050b02c01d115540248800130714802d1030f1921f0311542c8807201c0b0b49010803215485040001c48030361030840070044c400c50404980e8448900a96520710458a214400300e041c00040030075600d090200300040c04901c0b41d00c01c0001d840c0d62401180014507407114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 779045584 1250 779044334 779044367
    0x6050a050d030f08150a03140c1905010c26090111010e12071a1612090b011a0706061806050906010f0f11031b07050604120b0a062301 59
    0x40e0399581c000381c0c0251800c218a50a0f0074060400e07500c0d5132091020385400300e52290701070350b5101c0c0401001402d40d4681011003c0c907007240c00d11441401881145049507030320055501c01c4081c100829842030070a600303500d21071603c0201d1491000c1d219141c507040b40c9000384c85041d000c00c035030b00b82d541c1c00456501e80b000d081c0000d02c00c1c2c0700c419220b20f4035a40314a001c121002400154607091081c210f0a031302c4003002c8185140d03041e02c0c00855424031040300d05881c40000700307103070f0300b01c1c1c01c05590703004100d001a00500d01c0300460b481d20714103200007007e01b603091000802c01d0086001007105407284000038201d034074110200ea440e0041403411903600741c2101e807040c4914000c0c880c240c0da001c1d2a070070b84a0304600704042100010b18003510130f02c0c1401004005440002401684250381203401e1100300d40c450129a480b50303c401c1080343d5401280500440c00c1106460107001c14840b034800354021b0164040001e045440740100c10948000c034150810500e0150078500b01541d01070400300201680 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 779046834 1250 779045584 779045599
    0xa03110f07023309060f0c01060e01170c0f011b060203041106040b0a081f080304090e010e0307031d040c03140a110a0e0a0e100602010606020d14030a06170106050a05 73
    0x184607020f10606107048041c005100007003900145070326403208849600c0c4464098588458080c12450702038280d030700400c01c0c00301104000003190030382c040a0000d03141e800d001511070f280c00701003800082040c5c1e441d52030422802c2d050000e41c4108000700250300c0c500030f900140e6603103464244140d519800d52a46401070340104010814824060141e524000d6079181c0080b1603260900032191040000005542140002e0070000b40751100000078821030f21729000510007a5101220740703003207031204540d11043ea041000203000007485442550820340c2c400c80f84200c1e00325040042811190511800004a41d480d800c0340016000c01c8000c0da403154083d030040c4802120070900c41250b005024060041c4680c001c9203039030550b100e400340e03800b03480459640b40881c0381081203001c50a45611910026500c0e00d0004175103144045020311224481d6155015500002c502940785580020300b409049903440780302241e04505105005141d060344400480c2040c2402c08100640c0280d42c401c6124002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 779048084 1250 779046834 779046889
    0x403080709060f1d0a030b1302041d250806070903051501060210090507080d030207030801061407080a1b080408010b01081b0903070b030a1505061606020a03110f0702 73
    0x41c1305561540700207101200900840c010008610000840d800c002c10300c1c03d08604100c0c13540c04ca00c0c04410b249008980c140903904c0c0a81c0401207240c01c5075540e81301074000260000140400d1100c0c2610040c2e085144840c060391000c4160500101b91070003070008a540000f0014001c0400200314008ca1110460600c0d51620001a540c1c220080800315402d41740e0380040c2c18400140140002090780c0c2054800300c800b0740100030002e50110a044000c1882007002090407403049200d14111174840041610b801841e840740c4034a40c00c8081000d00300001074264500d482000b61210030114480c183c4551650b05002090b03003980d80c42058141040403403420006446803280d4109549801c40600c16510000480030a00b40020340d0003880229500200740002c545407640710364201e048181d18402c24680740d40c10041b241c0308840c01481150307801c40d4540041021640180403c00d440d0030002503044a122484100c0d401c2844043c1040c800402c881c000c3d03041c80d11080380c0d4041e403142c10701f00d04003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 779049334 1250 779048084 779048087
    0xd0507231e01052e1401020307050f160e01030308060103090204062d061b02041113030c1a04060e09071107090905010e030304020612100e0a02070614090c011103120403080709060f 79
    0x24545d100311000442c020300f90443d540d00900c101c40741c4a41010030782e00c584070320032441c0d56526090300076645020788607000050000d500c580306038140ca40c955507144168448900440c054050000e041e030b031143d034600c0002060b04107140f6480b07081110794511170440d880e45100284518444d405201402485454646505445800482203e41c120380009a285248400102e280903a0406100d481d4085401009028a0b02c0c200c504032a440000000d403941c01c0540180e00780254031525000c600d8044109040d4a4085129684610b031840c02402010741d50f14400d280400c5a480851016618250039061110038001c461f0011480d9008514600b45603010444612400040d08041280340e404074030118110307604d80000b0040c0b50210b8042d802e00d1080e0200a50021a080b154107181c568070303048403034518070250304c542d00501c060151160a04015070300601e40c0821600307a80030401800855840300564280128003c1d035032003000703180000300501f110b82c680c0c1011050242003c89162041d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 779050584 1250 779049334 779049421
    0xe210f030c0c0909070f0b0c070f050607060221010b070b0907080a14030d091401231501051e07141203041707020a08010e0d0507231e0105 61
    0x2542c00d440d5903030590b0303500d00e000381800c1c1150007402122285001c0018008a100d01030328490340600d050fa0364059580201100350444d1303120311a04075200b481803a0102c0e4655020300040403402107901c0724018044003000380400240c01c10340c510580030440c2014031581940e00f990104900700204803142c1800e00301e66840d900101d0090141c045000002c1c01d082c0c0c24416100000140300c01441890940c1c50404160b0018840080c40b540c80c0c50300c40000da005030768030840c0c05083c0600b4007006807100369611408400403014241882800c2080415a107803182444550031f400d484510345801c864904948130701600383e040d181503030048081040740c6441c101100d4001d980034a1000f40c00c1c00001c401c180c2d42c065410017a40c400301d40000000d0582d419001201102006819a030208860290070f0341c082c002c02c40d003e4409005510060400800f040c002c19042c910310741264031040340320348010704407402c48981014030b035110300038090300301900c00c800e0880c0000d0841c4a0f003032708151048000039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 779051834 1250 779050584 779050603
    0x2003040507150203041e1a16140102090a090204092f0a110303090109150c050d0c0e090411090a020c060403080712060303090e01051c080a0e210f030c 66
    0x1a0300449145082d1030b802002180e0042520b40741401c50501400401c0042e040507101d0300f201515800a5180011b61001c1211a41c00000103011502452038503920b03a82145040b5000c000d42d0b0801014480c0d503103131403150004050302103000d40d449007402c01c50807d07201e850708005030982681094007440c0110107846401000c800c044030781c4445507804119180140c88812044500000040c41b503102010342140d94418001c4030039041107400c1078204001c481140000b400040e20038010411080308942200c0301c2801c2c1403030300d00384000c0014001504400d043c0d408070341c60040400c07c02c1c401c0c10b181d01d2141e8000c101100031070034200d100e120346488000061004003006411400240214040d0124141c2c100b24140c04105240c0c413031a010749074503418050700ba25600c1e80000007034245040800851400c11022480d1001600d076554006540c121444c42c0c424040c0c2070b16443c1c290344030041011b160101c07501d0132085008040380101d08101030255844035540003002103000310900001c0340c201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 779053084 1250 779051834 779051849
    0x1b0d050316081c1a01020c0d14101113060f0e0607060e2a06090a060807031b080726130204090b01031a0c0307140306130905012003040507 61
    0x201c0744001e10709000780d44103c0c01101c2c540c0b420f0790000c69240b145640480002e00c2c100c2480c4000c00d400c034006907940c40340f1b5002141e201d108415201c0001d00400394592204800c403084410941c2c03c000000151220303041d82d14015103020444400144030507414100400c0227040c400d40c40d2100c54001804030912200e42c0b4015203000807132108110b4198804583d00481d2800e03240d01c0003030b510340b000042c11155030700204500710240130038141ca880c0f02180c000c00001001c0341440d81c0390440940c0d149400034100f03c10725507119417444c0600c5a51a5140260b0f480c1d60b101e0301540b40103a801780c00d0036007007851a0090741c0c421080420381c1d02c0780c103000740d0000e00700b03400504604011b01c00a4081e0100c0c490003485422800000010820190511202c1c5040030841091b150b0707070a038241203240000c60780040080c00b2546406034040c00ba40080d50040380203007024980745100301d052405d591492008540743e070b5607103501d842d1910090504110448503030004d0351a6003040c0c1c40702c0d82d40f12414040c0c3c45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 779054334 1250 779053084 779053117
    0xf031701080303160507051509070509131211061006080a09120806060405060c0d02070e0f01034206080a150f0b031c0806010504060c0b0702031b1b0d0503 68
    0x20b1301402042074688160b032140440d044540d808031140c4801d0400c0d0764900e198880d20b20301241c0f615000b00b0b003501c280750030444203504600a0301c40c6145440c501c1561420700050351180c0000c0541404082e00c00c1c444404504600c501e0444000c10503803000707000008652900c0020800100000e2030340542021524100540348c0b05c4200040f1b4901c500d40c01513610070400031346030044041c080351a000740e02194003658045541d4248601c80c400c000c803410007101c3d51250050000540d01c41c51882c40b4094081d0807040b0720800c441e01d0783d0b4075854504031620414105141e01145000d030003030741d002c0c00c1d00c3c001a04d0348101d00d5542d1061000250800391a59072900902075615640b1b600c907880c0ca5200400b100c40c2058003400030408810858100e0700000da0700300006071396500503001c450446c0c07202c0d5141d10780c004807601e41011490029100c1000c5000800050803010301030400c02840c240c0242c0a48000032180c82c5403560a181c1007003a074000c0c4900802400030a0010084d02d550991038141030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 779055584 1250 779054334 779054371
    0x100e061303140426030703140a030f0903050309010b010221180301090f0c0905060a050607140105160216360c030b120703020913050304120f031701080303 68
    0x5071000000340702980810180418001380340b28140386589900030b492003040c0700785050300034540d40324070400001a0100f89550700c4140116112001010720817014500010010400740040c8141d440302e80040d00051008402d01c4051003080c46403020322030f170900040010014240b81110015104040881c400c5404110240310607806041c0c002d0042c03004001b0805d1f12024507128240c400c01301e1007034403010995075011502401d00c0c0b1070701d4082ca4009000d184628544410818a03030f00c9504110b8000c83e80c00383d0401254800d0040382d02545040b8640f0341000c40c007280081c82c101040f074120100758884503041210242c048088403400b6101c03202400b0240b201800c08000d0b03010410014801460106009040c50341541b00c0300608000b05c0e13030320440002c1c1d03101e000d980c0d00d91400040c0d80804218003040da46650410484001c0303100304141c0f8107150b5900300141541d00c2e1040250340800b11184640c0405a0000014448081110400b0059410020700035035902000388180241210b0a0b506e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 779056834 1250 779055584 779055587
    0xb070305010e150d050d0c0b1f03020405040503280e060906030f06060403050f01050f090a0218071205040b090d090f0515220906090c020c1905090103030201050603100e061303 77
    0xb01030350139803c08111205003039841c000509104050005441060159000c241441c1a0490b090200d581009052528034190b408100051402030300031200340c0b00400100f0b41d00c0604005555507103a070070681080c01e089604010f49240d2406405500c17524040060b41c84a99842e0b0507603401460b1448048030a039200c0d03010880510613504058070b80d01c14008200d03a40ca005400c4a0f101c5e43c0000b480d08415210020000c0c0e6501c16040d00a6008a250080c044000b00a800c1c2d150312160350b240c592103210000c9003190489105039000d50758030000c6800c0248000c0108802d40c5030a4240c03a14000310b42c5080e40c1e54025014900806100700c00c2042e030003808452aa041d02c0c10030450600d56802904c6028040c2d41425403403150103645403d00100190410a604c21400040d8864000c0d0150707654413000c00012140103c1c05405030308210401017a41d40b02d4000a5000c0e52280d0000941c070304001e0100b600d000742484070408110305280341c070080400082003070b68001201100c502e144801c40e150 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 779058084 1250 779056834 779056849
    0x9150a0b011b050d091401020d080a060b0c010902040c05090a1a0702091602060601020304180504081303150e0a030c0b07120e03090a140d08180a03030c0b070305010e15 74
    0x30800415046500d0b82401400b040b0000280b5154483d02841035492560303c00c190300400601e400341c1c210000d03540c030765030140070480d502040c5010001102074a03209480b9258000c512405110b82d5101c80e418118101446070035070800d03e5080c11414040c42d240001d014450078003824001440c4900352581302d07892402a00d880942c010700074069854000e07140000348408004c01030040c4240c1c40070550b1940080100c4094448030000c0706a048110b0300600040d04003e001102c80b00c40800c040c1d9011041030b00c1800165102d90004c402e031140e810075a0042c1c1d010040000c07440d8002408031030000e500284400b44966000b0400100b940e00d80300c0c00e8074800703011041e02c040c031424100140301c0b0b800040001c007210b4204407403140001c1d8903001e444442c1c011484406800c003444001d14404185031002038208041e1040e403010220741100b0103e0b030300340743c1588202c01190306500b03190208085001c01a51103001407804105a601d07052200900800181411101ca0100301d007806550700e070080c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 779059334 1250 779058084 779058107
    0x11010f1803140c040c0801091805030309010c0f05090102100504060f05041103120412380a06090504110f040603061e06080f0709050c0d0c03060e09150a0b01 69
    0x14000c040c16075981c28025100144490192400d000b803e1000142d0318041c41341c03014100441d070703e41c41316078203042c034a00080c07024084000f43c18500318003840018400308029480b03240c02100200340003400380405003e42149854010070300205000504480e40d0003e401c00e104010f0140c04100e5440741d00703181c4010284d000742045030500304000c203c2400300360003082c0703201081038040b00c401c89217140750034109009501401c0c05040e9107001c040c011828143e04040280741c42c03580c03400c00708551014050911054001e609010481c40100041e26281d0b1081c1d0300100301800701808103150556031188000328101280d48191081c01d1520781907204c0394480b401441c0d2144041010800d815481d00c010180280390888190400720085003016002c5181c5140306004e9006210075030401c00316002400c0700418005c00203000380804d6041980502900a0400d12910001600da0400319800c0044c0c00003401008958420200d07030300322012554406600803241c020006500a1282c0100c0d5404040f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 779060584 1250 779059334 779059367
    0x90a2924030c0f0c0312160504030b1b0c16080c090708070c060b19050a120803040b07031b050903060108010c120209190e01081005160302090a031401020c12040311010f 74
    0x1c0303101d1209091ba61070076802440b0040690b25021301da43d104a5151003240001030036403003800b011659040c41c0081081c1c0c1a1a00711a0034182903014400510703060801c00125880d940340e42080140c0d42c02813001c241041400d45805030039152400029040f03200c01b400f2a020080f840c0c0008040c45080c0d80001840e03a8014096200c030303400030040c5440003030310b03006251140e031000c00006600410500005042648040340504603078a0f0348429180c41d2000b88007206054070390300612401c2400b00d03140e0314950029240c068441d0b040000349071400c1c1d01600842c40aa02d000d0340702e4005904031200724001002040b0144c0d403803034508040752807030503402c100e41200ca1642e8408a5550742015060741601c0165084070042030141c8211020384805682c0d40000c401200b000c0030035107100343c00034400c200b40a0304602040d95a0b644505034209070511741d0101e0795003c110841280c0c402d0181e80004041c100a0301e040a003151178100052100c400c40d14144a0340300c3c050314015014060215021014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 779061834 1250 779060584 779060587
    0x607080306210f03040602060a060305060105090c0f030c040305060711061803070b13121b02062214010905010801050303040b0c0f0703050a0b06090f06090a2924030c0f0c03 76
    0x510f844a940382c1080c080d142c05030040c10000750b2607001c0f45c40b850080741d030030100620b4079034a0502070003810745003c0c107034a400d010108503840094450400550080381d41214007a80c407841c6050103801d007440500710004101809106410b503078000664150003500403881080c1c0f0003240c0300c55901d50b00c50f001c0c0003096481c190003008a44003240041fa52064080d80d10076401410101041f0340304c801c1c403ca00180c140d902241000981848005004c2d09003092810072500024088022100000c6500c110300003031060010f218603590080d0144014102801c1006c403c4d414000080c2d05c034000d6009418200101290031208400c003005804a40c08240041d078041c40c1e181d080c4292030b152404010740b001a46200070860710f091001c0d00d680302d4140e0758071501c802d40310f6000f04150b0206c06014150360584603a5805a00c03440304030501c02c594076410491941c030381c015040c40028000103181c4001c0c0c0b03212040408080c20300004882d4044011005207a5880d90f01443c01c00600490700300b17041c0c6e81b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 779063084 1250 779061834 779061853
    0x50103020c010b210d0f02070b09011407241a04020702041d07061808060613020c070b031e01080d05160812070e0a0f050114041d0f06060708030621 65
    0x30342008960500d0349405d50b1000c944464044c0c0d1070301d40c01058400160b000080412440b003040005e0220041c0516242561082c403118810031504007070015902e58104003034490b01070500184824000a07009014040c24003203290650040e0310600750140140d0f0005118800c43d034035076020603407180c40b41c0d031030b800c507080312014460b603031800381c010b10000c1000810000d003002c2040c0254000c440c0078070001c183c3c641c1d8500501402e42588000060035075000c1c02000c40d5503206016030340280480464141d1a0b103008074200c4000c13850501202045010140144980c2c1c0e00030450a5070102c040c00c000d41e982e501c1c05941551042c0c3c0344005408800c01082c114645403900851a0082d20296500f400201e01c0c0342c10001c00306418407a080350040f00f0b1104120f0755005000402c0344400d5442400c1c03e06556a000d0412086008010700c20101c0302d80c10011a4002d040c0c955801283c01e40d401e5050815a42d01e1141c64880030341018840c04841d90084080000000000e400803001401c1e91600007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 779064334 1250 779063084 779063119
    0x17070f1809060e012c070e0c0a0c1e110d0309030311070503100509010c020f032b020a030c1b020d02090a020c010c020105090708061e250531050103020c010b 69
    0x81c072145c04150003003d501140140c40760024000f0181c0c2c40c03201e40d0300300d0758840480c0c4400135031001d00c00b00b00f809101094a400b062120615400c0d569a900041410540b0b525024524285e88420355204200c82020840440e03444100c420580342e040c01c10a418103c2c07110914500b4800d0342c480c582c14032410800540c20b84480c0c0047d070142201c0d030003e01c10701c0f2190100b80c0e2149600140e40c81d20307038400e00c0381c40c100070007091031403000b02c001c403142c48001e00000107828140d90140544001194030350740c100202c90b6010024144180000c250085407a10540c00980c20100c0440040e1040840c2d07400308a51a1055040b14030036114100200000342d1803810190280004644000040c0180c03400003521400106081d403180000010560101008101202810360064950315040350300000400c901002d4200e170681c41201b030f40f51203480710194940100c3d20107071101d1071340d800818518100c0c008a4081d0188041d110242000361f1a56051001240100096120340ea800180c403003041941c1c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 779065584 1250 779064334 779064371
    0x11030d0c030b030f0c010f0905090408090909070f03080906090405100807090c02150411120a050606060702010221090a18050702010203041a0403050f0417070f1809060e01 75
    0x40a510103000d0030428008150701c3d049000224841a000175600c0f00c003640c4030304080340c1e04400038185442c229880c0da0225042000441f070440341c82d680015034107458500b210301c45601040b001c0c01031460a041282c00b121001280c407004140610128071400303590340c1c6105031610510301410811141c5001000e44103044064030614400c0d000d4040003203403050090280303001ca40070381d400a00b2209424515840102c100a0050326442c142e81351850f01039070f40042800c0d911040200810402e401410018104600900814425041042605e00603600400e41b035100d51104e00c24614054841d01a10300700e480b0700d0440c290310035240c810100d43c090401030170508460325050204007a55554006078200e00c01078502800325010354582034054000c0482c0c41e0307070161003441d2030b03401c00500c140e03480400c1e001904190025612210008a00f00c0e04000c8040200b0801103022520f91a001c10504103d90b92405020510744440e0400144145900a00c05101c2510003c00580e0610080a44003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 779066834 1250 779065584 779065601
    0x70b0a021014070e060d0603060617070e01050f0d15020f0703080901050705031f05040207060b190f090c03111207020d0804050c0121060e010f0801060b030a0b0111030d 74
    0x106840c0c00011001c558910390b03014403c4100e51901e001d0300c400b07030702005000e80140c1024403226844200100024101c1d0160400805050035003d00032000b81800508020075908002c03140c0d1400b500401080e42e0311417600100d00702c141c8600d041c02c034403814000e41200b05000050086400041c501ea00d4039840c0d0300600d0000d0183d594070310385484d200402400d8510035121240014802e00200c4d620144803015080d01d06048400425416500d50220701079070030841064a0580d030310105100c0d1801c24210351089818088101d0a15074106403a0380b020403100c0c00b420380301c01e40c0e81e10b07440301680c0a40d0140003a402c601184548543c0043e080440f9020f0440700c813070050040301c12080e211b42c000d1440a000d00c2c0e0040103007104220070001101c543c4c1c000440d1070784015800342c050381e0041c060311551028000030003101d4500d41c107044500040a585601030078a40e0b00d0440204904560034043c4c82c0c004582a001169034024400100c8440d41d418000130000e000002d000320408160341d00803150b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 779068084 1250 779066834 779066863
    0x90e192304030f17010806180a05071805012c06190906142b03262401080a09050c10020d0306090c3002070507031109010f17070b0a02 59
    0x181c3c00c800c081d031503c284c20310070074200d9407140c0040355241402854071a62910000d00700c1d58452241c3e02e40616100f071a6100080c161640300e807009544042d8042c0a0150a0007081101404c40310750005014421400d26482500c1e14500450000d80d15029030035000c41207a1041c48086448100c1c260040003288244520b40408003a6065182070025a1018007290042e02c8015410b801e4141040080701c624110200562400b02c2c1605154031024100000f242c00c800740740515041510030703542c0c1512000180c441c0303440824090580e90000f115030384052085c4000c2550001403030314924207045c81e40900d620102c13001d603000206030700149515003001d20795424442c5958580e140000c031010310134031000080c0407194408901681001401c0401d08041080406c51071502d0100304a0704514002c0b22a40c0005d07104006104c2c051403a400d0692088a40c240319515004028040078280d10036100f00d400894504010141c007481170000600d110380c01d00b03660f40380c420380082d100c4405262114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 779069334 1250 779068084 779068097
    0x9060f180803041b09020d0c020706021902040e100216030306050f060415140d0603110613030b0403030e06311203150b040b0406090e192304030f 64
    0x10030400385104044034641010329246980c8071611662003003110910020b00c0d070400c04400003404c00e03217403000745045100700384000303808058000002d041c0326159105408640c8207284410741e0700ca260310390007001c0b03074100e40c0001c0300c500c074190702802c0c503083c0031140714182e202003000600c821044400c02040d0784241c0d070411645031180c0c20400000c0040e800143c022006110034020300500f091210520b542c0c601f020001c200c101261021580e204100300c01080785c0b0341070108104402c1041d200301e00c9004030350044c100b200200700c0d02c00f9102c151001919081d0048003050500d402a0703c1541c6c06081c0b0010380710145005040c103c2c0d20002580c5105c05810f1138603804440307500e8100d05840007a4003180020b200188047d080700900b03a100c0da5035164812401c0c5c001806510140180003c00c814001540c40d10324158028010b941d084d070184200c801080304201d80102d220701c00c041d400105000c0021001111720074401c1d0b0810340003100803c1684030007032100307158000b07607404510071039a50783c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 779070584 1250 779069334 779069351
    0x61e0412082a0c2b1a101d0601030e1e010605010c0f08090607081201050a0b180f0a180f1107030503060904060b040218190509010e041a1005010e06040303120b04060909060f 76
    0xc01ca80815441407000307020310711001f254400c131b82c5525039820403014540450303820044080c0c02c0c10100c0c040ca0035100740307504203100b0340b60306800e024040040c00700b4202115800282d40b109119030601a02c0180f07a2800003a5a24095803204250360f41c0d55000941c0740d8039180e01c0c4200c9450b120080c02460301c290031854000480c10032140444074003104111005031104200800c1c03015046042d900d050703211030048004500103034030550460300b0f070f0119040410710110a000200446444002075100701d1404c00c18000803a4000040300d4208000380c4030044185c2c0c43d801e050f001001141d2000364850b000141030001e44e40c610100340940391b012502c0c0e130100324841d0a4261115641c2c460a40c0000700700004000b1901501500703680329000713207485111b90b043d181e4141d400700300444840d1207000101900340055640425880f811400c06ea603501e1500e0300b1514083c1c81d0700c1440d0004074205c3c0d154840c3d8036294486421078001004120b000340301090b840e180c504054106180321240003403826400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 779071834 1250 779070584 779070601
    0x408030d020904270b250306030204051e160516060e0606060301180513020a080a030927020702010c120203040306051005061e0412082a0c2b1a 63
    0x95122507000c00f60710403041d0301e0a80e2010019400109684c5056100c4081080400006c400b43c0903404c40d9580c0024942d429807040004450340a07103644080c00700e00c0e00d06035800300000d10058216102d5210300c0d9107161403d01c100d40782d204029000b1001e2100d01b100c1c408000341070b0044002c100c4c4003030070703110140e48001c2809200c0c0001d03c41c0c02c1240c2603100d8180e080094590095402142541c02c10b00b03003840701e40100b40f0744013080e403110002d5400040910141903005080c0d03c0541f40f003c0840d6981c20341e04d0550344e0904900d0740c120400781e50000d00c2100316801280019581079101c8103511300400207600107522500944070a90f1401c0c1400f0015440c00b0311900850142d41008014a040040080c2080c0d83e641400c0703001042240d00700000b140c1c00c00c9103450884014414516269a0744ec00c0010071520203c02030080300c0d6105e24800e80050110200f038140800c1070a0342c018800503003e8580703840340001d103070366000485550690b407818002c00c41c107d800300302c922004280003070312060107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 779073084 1250 779071834 779071871
    0x807050d0c080a3212070f0c11060705070f0906080309030a0f0804031502071502030412081b0301090204080d0206010b03040f02040b180603060a09080913020408030d020904 76
    0x200244000b504200c8101c489005a1010002c1e4020040b12620902419640440004401040c1d842c00d24041800116095076400250780035101c0d1070103200907400c080d8050901982480c00420602500a60707007065220321044d42c1d1080d03041801c84000968406030303200d0042c10380c00f501d6002800c103400401c000a0000845042d10b101400808910000d900c541350401811501215600070400c800400700d0300032101c0c0b4982e0842c11600580c1c60b1014609101d82c20394074250404558014010040400d455001c820400003290806100c241d40b5142c4c0281320362819417020850000100000c80d00600da40c0c003800a0303505001c00c40f0f03003041144030b0030f0340d840e48244070f115040d1208100150005030084400d4503c503201400c0440c40c45000c20002d610720100218201e5046040400c12100b0b107010010182c210007400c00400416280d0b48880c440c612448410501800958588032100601030307040710010020b6400350b0341c5038490701ca440c001035400700c03951074415030030503d00240c218045403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 779074334 1250 779073084 779073107
    0x70605070c020405130b04080a020a1401060e0f010e040609020f0d14070608091002090415080129060724060b03100f06081f150c0c0906030206030f04050c030304030807050d 76
    0x80443c00c2c0e9541d0741e940d183d00d40c0c88650549d0450160035210f5002032604444954030941010010520b14101010122840b0004101007040c01054004200c0f201300c1d00c640780d4210ba000b00c1c010440b40e0300d0b400451340041e848502603400066165042060001400c0c144103034071260f4040c1d45807180c0d61113045410300d8050392080c00540043e40752100d4001283e000f04514070001d400841d0341d4a101300c2c2005d812089900c0008180d4440880800440d441011200075003400d101541800c111040451070601078120003e1840d1692074120300c0d0070012003080005e00d143c5070701c01e214a9841d41d0814020303400c199035001c903120510b000401c03036030711003040542519601d507074148807070b0340e4951555143c211030544d406020000003c041886081c070302160081510944580e880d0410f98680f6031030007000d0398800c1c0c268604e403010a000590741c0e401225045140c3c4101e10321161a0b82c1043c60034a501c5900c0c0340e605100003e800010000683c6c003a1212034010800e070380c00807c108000b51400c0c01103c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 779075584 1250 779074334 779074343
    0x31002070305030610022d0f1b040b1503181b010f05031810050106090f0506030103080f04170a11030d08011a130f0905072c06070605070c02040513 65
    0x5100003151030600c405c9402c240080c510403900700d09402c1d40e1030b0030040702c40c440d130500c03c0c20318600d05c22413400204024012080038138020031000c41c04004003205820b113544141d00c44c9407113040302c0c0307266039600000b1050703003203800306440c1d403810440c1d41e024620b00e0002d0007481e41d000e580b080501d4028200d43c04000c44206850f04003120310240c2e0100c0c0c0c280e100a00352031180c0c40810400d0710f00c0c202004400324021540200040e15410100094a92000c59006010303030361840c401400780f5240c00042d01e044a6224100c0b90302d07072450182c1050a4002da4000c4038011484003490901c0c0800003814241a50194807103054807000c84040c941c07204900c0459030042848030004102000c1d00c1d07080803540840410286060600208440c0d20030b400c0c5602c070301540341c446407060000d0340c914030400e60480d40c0c5c0e05004040d0304c008050030200583e54841070400d04210a03484109844140c12946070550110003080940f800f401c001d0400e85107404140e010f01e11740800120f07441c40101000034482e411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 779076834 1250 779075584 779075587
    0x106050d051903140313031e0512070302071704050a1d160e040c0203040f08010c0815031f0f0606020316020607060626060901110d05100e0a0605031002070305 70
    0x420b5000c21110100081c21402c10100b80b10000c80d000da01000fa6010b40711031141000c050026007001891500c0303180c0a148031300800325020b11000d400400f211b4a80410140c04482aa28400150024080c2c50130280c07544500317051110b0075805a02c010001c2d64003c07110b40c1d048030f80b10043e50406c41048480024612440301c0812101d000c6888426480c1c030301890070307036065100400400d0070783d010b580d181d4000d80e2020405202500790540e03c1806408060002c0004418a600003030084c5005001414461841c2130b039030030b107074900f4032540441101800c80303c101200c00b04884001480d02d0344103e14801d18017600814420320100440d405124039401a0305441384a400f005003035808400119406541c603070300001d402400c3c0b10000224510448242c89000340130307100c0c5081000003014202d0503450b011029600c1102c1074281d86003004520380020b210359440524555100c59900300528080c51641080841803494002c0001c6e5075054040d6200351104040b43d402347c1c0034207080217001c81d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 779078084 1250 779076834 779076853
    0x140403080a121104060f121b200615120c0f010e120106141c120809031b01021b0304030b0f131403070308010510021b06040305070f080106050d05 64
    0x114080c2c41004100b00a40092081090000924154881e40c4410007003021a4014070304603806c0a01110340003491708060105044030100d00d0401c550b084041c0c020311612174001c5081c440e049070040ca210b407a0313008551003400c02054503071704040c008001d14843d00250904409054022601500806020301a2490041e010300191410108090690f401000b14424000791850034042d01c0000c09140c0882d01c0c1503240701e804d025145d500341d030700703039440c03c411584a10008074039001e11310740050f441c54901d00c5500c0b4480020304500c154170306070b051046140c1114078625810350051940c2c007801c004e80d500e9646c0750b80b204c9440f400385201c082c140c001c803440001d20698802d0101039205c0d1411000d26a90210b560707507402492951020002d2039070020804104154203d81c00034090041103804a07a04810100000d54404510343c01c2024a600e030581c40342c0a4030f454060740c01942e804001d4410350358841081038020000c0e44104140b960800e000010b85044c03480e02820f09070740120240c4030491 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 779079334 1250 779078084 779078087
    0x9101b060c0c2901061101150f0311150f03060414160f0306230a1e0905010b09030a060b12030d0e1513080a050d02160c1a0a03150503010606050406140403080a 70
    0x50900268003240d505c6404150148c5000e0003403001622001600310411410341c200f03010b03560742031000b840c060aa80c1c0800f8462006003819215100501782146980c1c1d903821020030054604a8280051000b120080c0b11089051001a000705191603488105803414a50110107070f5406102d151074814185480c10b408000110b2200719594018200b0810155580150100e0052044080c480c0c001e81500a0007500400d00030280103004040d81c05060103c0480040d850780d0007800020b02031591f80084514580f103440300c9035030241d05101600d0b11000791440304400340503140d800c84181e000304000ca030031000c8405602805121070b0b03008202c04581702d5450054640c080c161580c2446028001d90208560030300041c0204240c0b0b00403070b140c2d0411442c02c1c0c01050003d41146049010500c1040a21022442a60351048040c5400710b4840341c1003400300019119900015015401c0a4000c0741c0a40c00c08024000c40712243c0d508462007a440c800c001c494301a5001c014a40c400c201704030600316 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 779080584 1250 779079334 779079347
    0xb010807141303080a02060717040b0109020c28030306050301110717040e010f090e010515150f0f04031e03020307201002010b0f040209101b060c0c290106 68
    0x2c07210101c000d001152203403076888071a00b02c03440540041e44061304004019620203401e40c449014100168610308055072242c1000303005025480c1c0c865808a1036132056401003191040070300d00049158010031510300341c00c020107801a02036020a00704540042c01d4281442174041004650442c1230034080e8555400c02c4540d107032842c4d260245418480801e800d00001c808500070007251020000c00c41ca8441c0943c01c2e142140c01280f01c0da49044100203525520080a05211200301c801d1415000c04804800442c0514041c4500d00c0001082c0003030500180402823090700e000341d444107843c285a00d0150b54040c6030000090041e082481440000b400400029107542d05c0c102c030f04541d612140c0c0200b849094540300c140c005079101c004620590600c5078169418400c2540c00b585422030440100e0050400c1601090030801c100048040000c452000d404055500032001c2c40801041140240841356141d4107669141082c242c1c11f40740140e440c0d1802128141c0e8455580300cfc2e1a120094404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 779081834 1250 779080584 779080597
    0x1502030705040e010e04030f030c020703110d06180209240907030e150708060a1a0901140304060e0d0c050606041d030406030f060f050a120f0b0405010c030b01080714 73
    0x9001e030912000c0355007003492088502800032940030751528600b50800410407c140c049200c2803504d0140340c103041a0780462000706480d040815020350200342e20105401c42c241e140094480d0386443c0498200130109810044418000c840042c0c450301d5840b0785405201f2055031400d41c400406400341082c0c10403c9800da0b01c9482030800042c3c500358448840e00703007002c08064040c01c060100c10800042c0e007269080c0d820031819a26800960b0a00d050308509131003003511658110808610000d007031b031041d4041c94140036044115600c038140741c5004e00250140b0003401e001c900603405003603034881c0b2440c61342d400d0350740000c0185859101e030802e0000a21155000007a8005004019100520704100078401030400b0b42c1c0001c1c2100186182104441c642e030000e1048008040b02000710f82da0340085a420340320002c08081641d9540c0c6000e80c6008035022008240d5000b0b0740400c0705001e010761000408090343c0d02c09011702601e500044840106c00c540350404074000164146407483c0c1c41015001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 779083084 1250 779081834 779081837
    0x30c0d05061305070309020910060c0f080c030c0706080615070605040501111308010608030a0906050a0e0429010e1e01050c0303010801052d011502341215020307 71
    0x80321218504100207441080b113600740829110142d000841c1041d083c0c6641c4005540e20b55020b590400d00006c020708150b01e00074007000e0b0481e101c00180015103088a1b004540c0c102203a607510f01c070040880e201d4000e4882da40100300303400001403103400d03c1c0d5002c013034006460000e2464818144d03aa034005120180003681c856680300b503004040c00b642401000010b000302410740d102c0f807401200c1801d680f29034022170710320b800601c00c03441940e03000341400040d20840c1c201a600c03000b03551421100002803455855000e41065000c0d000300506020241c2c501041c0e4007100304c000c3c1e02da801501ca081a49040540004a0500100c0da6804491842d6200c90052510b90315022100a40c02d00c0c61b00203070400040d40c2d640c0c501f0b1050310542e1080c40c0102c2d0b9114000740c020303001d4005d040304103001e05104003c41041c2d80401c2d44240c03803003402001c2d610030303560703451034a21020190907203550040b081d84604a8800083d000c6501980744c141c0c4240c090340915410005408465010040e40000e0000710 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 779084334 1250 779083084 779083099
    0x200c061803060a020d06051c0b071b03050706060501020d0e2b08030f06010c03020c19050301090c090509030c060406091b0b1e0a02150402120d051e030c0d0506 70
    0x4000d039a0500940c1d0254901910142e1920b00790341981c01112810341c4940d1180b07844201c0007040b10020070300100b069030040f91103401e036030b101c020903110346c4020007404040701c0141e1021820590040082d2a060b0f00982007040895188c00040e42d440e02e50340070b0311002c5900c00e04808424030f400e503c4240059540c4003900000249081c0c4504800c00501040380d10320380100402098031015101680d02110034070b07080002c0942d03a10065103030040c804440f40610110313614082d542e440311034070381c00408010700200b100d0030b03850900300403851090003000c0c15079080c003000c1007900a00005841a050000e8082c00040d19a540d4220041100e100110b841c2d10358845200060f01002080740b00038021800c01640d10020204040f4550f8403800d0003001c4003105002a101e034950014100440c0001d121445829072111300018201084451b0658164850b00008042c4180c2c800007400b4402084018940c082d101c1c0a10042035010481d1201c3c20074005120300b4235043d61a800c86038100b480600380c1c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 779085584 1250 779084334 779084377
    0x9090b0f10050a030804141801121a0406051501050f1b01090f0b0108070501050f0304061e020c0705011b110d0f0209040b040b1006211416200c06 64
    0x40380103805604c01d4881c58400318040044000640040c40f942c9811200e001600c0e54044003940c0e00c2d071043c0101900a0000300b248020041d00340d000300d0004449594403001c070b01c3c241c41e000000d07007400c5502c84010300e800c2c0310300107865000f0020b0314500f8444c02c0c1ca06081603031010080d0710300061340c003409038503640303c00f10140410140c1c495008598010090b40d0900d42c18a21814038090059200718104001000785441c188102400d894100e0351020010642c0e00588008070310f5144003c1e128040b461001446241000b8005400710807542c1c2a220f09100c5000c8015440d40c1c00100500078040d10b03120070040399070307207002c5400c03041d15403003070700d100c00e00001c01c0d000b0401801044404a604407143d01c00c0c80180035030408201c0c0d125081c0c83d0007051581c1044002480c40d044e44815000320603541e0a08000c144071368006c3c00751401c030056440810b150203600e50016040f003000380402300e41074021800340c520303c03400c00c2c1d078880d80703075400a158101207402403006d594460303401d8420b800c1c00031410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 779086834 1250 779085584 779085589
    0x1b080d0309061b0c140c0a0909030216090b0a0519090c052b05090a020102120f0d0504080d0e1b010c020625050d050901090b16020303030705031009090b0f1005 70
    0x20b003683d104240d942410300010351a080c109814868000406980200d04000c1190f0750000b91805441d03020b0750100703014250b45010303481c0500c5503014075001412801e000ca1402403562040e051070900712082100590b4520a018003d48490705100320000501b03010b00c00307a40c907504a10041c0c402441d00a25214013a083e480031210b4032020700c8100d42c20b01c103412046040b180a11900091400017402c0c00709000c4d80040e59403061020300103c1461b011454280140143e41901e54a000000d8103001c0d81c5418546000143d12103007031050018601203650540140c005008544030b0788421031503044240d500c0055500c1414207100702e0788890304000c1c0e0810890481c4d5000c2d00813058640c6001e007104580380080c03c0012000440d000c0100505c15103185a9020504c882100c420400042c0e54000305d14495050100c24080603400d4400001480440703a48170300290301c6480044045140c00c2d45803404541175504800b0301401191030200410031148603c038071145c1004500482550f050783c0c0d07001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 779088084 1250 779086834 779086871
    0x30e0322052b021c0305130605120708070221070c0b0403020a0b032d090c121f090204140703050c09010503060405060f0306131a060105070f0c030b0a091b080d030906 73
    0x2130403000910040b038164480680d0a010002500c01410618100035940c04510700c003000003000c80d801c2194044c00715a03054000d20001000710304100e10b124190108041203241544508812611003000b04000190030080c1803d44055035401480354144d82d1400940f0b02c00d0b034201070655101c40a0300010403040c032194044a5403524240d0109200d01d00d001c1000d5418440410441030003065442d99150100902240c40600720703070794034070610350001e5000c50380c4000c25880400a4100349070100075161084903e4542d4807034040ca80d000c2c01140d03290300c940d00740760081100150101c1c1c0144082449450b041d0031066000d03402903d000c0700c3d00d60304000240303880340594042c011050b010f06c0c0b0b00244106040c1409420120031904013560610f280024035900c07414401600010502c00100d040090420111008680020480c0d00d0750034100e80d0340c0024020324a003201d5164860800ca40100c5100c1990702c11140300e4409081c1c0808055800d80141560103002c4a01d55940c07490400c15514080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 779089334 1250 779088084 779088139
    0x1409150a02032502091b160c0f09060e0709080325060c050d0b03190f230606040e0c0f01030f1d0606030c090411060a030e0322052b02 59
    0x7205010640140840070358042d040306d44424030f01034403000b00c40c1164111800300000303030608105150107080407036541700e1741e0b0403496042510b14800641300c5c03003680221055441c001005542911104001d80c0c100300288540d080541040c40a40768035040c080760405c5007100040381c0c1102da1015516041160503e010714008680e0205a580b500c40ea0380c403a8031000c5200f40e0081100d216141800b90740c50800c00c2e0010b10700c0c0c1d949603017042048400421501c04004468110300e420a003444060b4a424040360518008c0d440c002b8042d500710000664100355120140801c030a0010a8004402803c0344103590610103440f8508034220440c45040314402203080d1000d0101810079004041c14000c1c5c24000d240715209100600010030b10003042094a8801110705a03622007501070309401405003004201014000071030514104055524031500014405181c412003a45880800600d4009038a00048001a001641c403003801d09010110044d80003c0888039100c02a07102c00e480000c254 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 779090584 1250 779089334 779089387
    0xa15050316090f0e0a121b0b060f0a03080a030504021c03020a02040b04020c061303020c0904030e01031d0a060f1107151401030f0210140d06061409150a0203 69
    0x34071041000d00d4091003040e00629151009204100341c0e40701c059681c151262001d40f072100b04510121141d801010091144c860101900340480b90174240a12019021626a401904810100415482c04c1103144058990050555007032051401d42117000b481c00a10898111034840308540e13000395920090702415100b41d00920507031000b44144000ea82c07916103107600550040c8003020300f4910200d19030764418184030700044040a0343c182280b51483e031240082d0040c40303034814082456413082103120301d00f400b83c90030b004501102c0340880904400c180306196036004541031200050311908840075a190500c004200202980400a40c5610000013200c000200074811803150625015241c48100e0500180100b5855a00c1701e00a540d48802d00910a01100da20300e11034a0150300c042d400d003882d40070510380361403d04819000628184c002c8a001c64405115522042289421250007903809001403041104170030755060150403000300f100641c001844500c80d80f00200505c0074102245 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 779091834 1250 779090584 779090623
    0xf0705040f0b0102070506161a0108150601080106120609020c0109120f05030627070305091e0d0c26190302122a0f1803060403080a150503 61
    0x9000421088640007074001e06414180000421941c1c1c0200740e00e021a18182d80440e69959900c42030701011803808001051440480000e0f40c0d00e003818130410341a00d03289012520003442105100800748001c0b01e00300c0c001180c410041c4500c0d8800e400340003200e007803010045083c513281c0301c255090b07030031411460322030760f55501e614424032924601c1264481d6040c1805d075100000410021f219102c002c088030b008040000519554450a0780303400b00c800d0748046050114100342500a000d000103a0f025002031041d61010740603a0f008002e00814165140010001206070682c01d07144102c0580040d02d03101c0081c601002d032810007152041c480c891100e0ba007035466101040c2c1c6192501a840079004140c03052103030842816100581540240d042c1440c81201103107501e96184040741801d078001c40c9080070542030340744001d540203043e9034813070b0320213603070184c40b052091581e2103800711b07800303030026000d000400d00a0307100b50b109a03110301c91143c040e100e003a21400070070b28202c0d0490504045030352 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 779093084 1250 779091834 779091839
    0x1202150117060609070e010806060904050405011a03010b060d050606270414070206040311072c061f05090a0b0c060f0604110a0e032401172d0f0f07 65
    0x814815194000300071913074501603041110004141900e0704c0a094180946140428201d948023016182c1c6900000c2c0103114919180c0b40041c0a04038000f80d04410300f4010b50300442c0381c80c06014446402402510a81c1803001c20400c02c80a000090241a00440200489221000d1081039403460040521140d003c00882c0828442200c0c13075010424030500e080b1003803180301c0d6404038446d500182c242c584100c0300e03e50380d20349504040e03080e4031981018410040729807102880c01d4000c4a0840103580001c11983e6020900c041c280b0b840d80712030801d84c105640410458080e5010b41428103003e48040c0b03074580c43c2c050800080c2d026414402a40d41300500700440342c10507803201548110141d4090101101c49034074070b0391786d002d000c8500d424040260a904015102040442c060404a99400041210b126120b10b881d200070302445500304013000301041c5007080003502d503100f800c40300540f003611408a01c219562178444500341c00640100f16103001103071810482c03074400640e0355029184091 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 779094334 1250 779093084 779093129
    0x7061b0f020303040b0129030a0917030c03040215040b070f141c140d1805100b1807020c12010b0a060c050607030c050d0c030209010909051312021501 66
    0x151400d4403202107600800810000846080005045440306e41c00d20a0812a200002c4d04501c03800c14400811a000701c200901c2c0380c2541c010864a50007052907455524080b880c49500c0d2100305c1e61201d40c0001000804c0040c1030800c8040845080d04d4405030409890750101d411540c02010199103010724100341c40d00344100041c0881e071840d0120010010b08960090149a007018108404280b105240d40c1480b41c0c815803040f2910013940603010441c0119111030000c03108003a12059803940308864020fa12040c00c2d00c1900c8039940020300d01808110205564610030b10006c2011007140034902e241601d9840300091a018003001400100d510100d646c1840f5010805034010710400c00170100340c3c1d0114102060494000e0900c0c0b13000f1800307088111050320b0364171402e5054a180c528040c80da4001c42d82c99030241000d110b0903030350780756456a248500c0098840c190f56002c00d00c40340c980d140c5c0005400a4100d42900f1003070040d41c074000600c24070406422400d9111901d440000c440b1001c030315 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 779095584 1250 779094334 779094347
    0x30310030b150a230a08101d0c040b040902040f0f0f0209010c0b0703091505151012150b040305030415030203091005040507050d12030b0109080d0804020607061b 71
    0x5000c2c0098014003141d42000560b00060920801400b0300d0711140e500796199801d410502c00c0c200180182489643d1291407a540302001c0c40b41810031881c0500c050069a02c1c103440d40e02e504400c1c00242510a007940c10000142285144c1a40c010380e6401c5000050312540202403880d4103041c800101c0020001188003500d010f260358034819031040108d41c0c840da030001044081150131081103071550f0f80300103003600100309044001d020301f03190603d1404114610f402440c03003102a07200d02100100c502d028449801001801d039070125541d00c4e00541c0c980c00580c005811003076540320703c5100d20382d25031101c0900c0d8041c0c0c1050385c05400010b0f050205e410211003415882c103403468218a14501041c02541300c161307000c281c1c1c0321a81c03206d0100342805010000d90021b400000d0200c080190913141041007a0702c100c8400c400300e401c2050182c2d95602610018049442400c081c00e9848041c0d04101c1d03c0b20b800a108034ce201d00107012240200c0c0492003a102030180c8101c003034090503c00e61000d08a03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 779096834 1250 779095584 779095591
    0x203100311040f380604030303051b04260703020d0f0525060311030c0f0703030e010221090f0d030e0709060602060603060c0f0f0706020d2409090809090606040305030310030b 77
    0x10310000e5030b40c881d1301c4e02c5410845040300c0d01031400140584502509186003440094003c103405004140800c81d41c0d15a0740329011203030f855111010b542405a00542c4070b01951201035400461450b1400c007103039640034550301451180040d940d0b2180e1400c40c40386420203c4801002c0c800c03140e402071150760b415100b071101d601180c41b00107003140b0745003c2001191007114110360100f18042550b02c10140660440c0d0245024000259200c40040d59850580a802c960382c550300014100819854900440c2005030306011001a11a0301ca030068140c0240442d505111280e120791000003400030b209200340340141070154003074074050030305004051504102a1820024210070825400c40c0102c000845050017603141110313444819030b04020f0006c0c091046c2031985d1604040b103286042d0380c4802081c032400c3c10151902e410715265000c0e03500702d4201c00c4009040c80c8041000b030b0154034050301c00785d070b010a0081100d860207481c1e17a41c0781d04582069442d0070000d01041c0003441002180d2152662 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 779098084 1250 779096834 779096921
    0x7020d0b18010b03250b040e0a0f0c020a06021e03010b0a0305010e0106020c090c0403141509010b1e0a030f03031505010f170a15080a050f010203100311040f 69
    0x211070b600f0300020340c5907a0506070b09010350424600c2c20054100b941e01a000608500d541e5a440f81d5940c41c444d0344800045644013400340c500500502000c98501c24a40c141c0d1181d802400102207a564810082d8030803800c0740c81d0b039072034080404503c1c9403020041d80030701001c14019454000710f00c0003400b0b8a80c1138215030071001110005200d0140d00290741c4030868000c0301c14481d15102c003650f064003271080da04042c0a03100304d11203004a60600189aa080c2ea0190303200c0305080d030307030100c18500303e0b40c4021840d54000388810303101c00e0000c00711152a12415000749100c03c5503560769140b403108100040128040b0f91140f10f0446080503009801000f40820700b044c040101e485040180041c03003240c10a110078040c0c00104000907494ec0c0071410100000c00800a200c2c0c80c3d98900e0342e1420380741c20407603161044080f1450780303000c1802541c3c01121426889103006007151f41c0c0c100e4203c0783c0030b013150b00142da81d100030315000d9003400b48103082d800c0203040b585250074280342e0340c0035035044a10400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 779099334 1250 779098084 779098091
    0x60c17160f0b060102070b122701090507091a0402090a080307150b0604060906051303050322170601180b0612150103090309050402090a0503030403060617011b1407020d0b1801 77
    0x841f401c05030003159086121143e4101044d511020040045007004038618003034210680c624101010542c40140d20601030001c807551903590360100c8054510021b01810101c01c00c01d20103c25081c55000b41914500003000040c80545610509203113400c0b000c01500c84280c803454100c5034120703d200e0000480702c1901c1507840c080c1002d0001d030002c0c1003803140c40100200003d5054034030100200d030b0f4010f1a403280c1640c0e9601e04040341c1c01e204a202d104c0c44000e42c003500d500000d0300c0b1103801c2c1c510046035a00e0090f262a81c680101c168070282402c3c4004481615078051500b603a492100404084843c68444801400e01540c00c030000c8076843d0650781418a021040400320350044658000c9690807140540c0d500a500c01049102d54240d102c241c052002040c04003c014494100406644114030041194036203900503900365910020320000030b042805031074034401d02c115102d20380758800301030f901d240c4031781c81e4042076216401c08410b81c0d00e005e1030020300c510070b0412500c01c03080a0310f00c0001c1c0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 779100584 1250 779099334 779099339
    0x21503040f141c080a0e100516050c0a03050a0203220608070c0b06090717190b03150103030810080f01050402030f01150e0601200109060b0901060c17160f0b06010207 73
    0x410f030602a110803103083c80213640c0042c000b01c0780c0c2d4100d2480c407a410002e0b103840005034031550000c1c19050343d400c40e966041c1c6034803694451045040d20710380004035005100170f06032038405071010341c0410842d02c00c60000704150b0030a1040c1949640c50204002040710090303190020080c030085e409030440d0304121208515101007000c002d83c0c9500a40211010b101d5500c40c1001500c00030300e5030381070f10b0241c0712010420140c60075801040724495803100061200c03104100415031076020368000c840c0d07020b45002c01800440e100c2c0a101c2e070b10490b8030000312202c0fa1220441460701d1109208192144e4441042008600303040c0314201c0c2c17829062000f48842ca0401544540e100c0b2503014408410714498000f6056a114605c0d2200c03008940c000801209400c0359030328041c00d058a0261031050500a4651407401c0070705c4428101e4203559101c5190701c0c51560740601c500510125450102e505000600c01031400d148541c0400d840f0300d00c402c00c2000a498150700c480700007400b203419034002d030208 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 779101834 1250 779100584 779100613
    0x3060c08041a25020709050117150919050a15111b0a12020d0e03060712051e0c070201080a020403020a120c080109030504081e030a0c021503040f14 65
    0x440092009000304a551a51244003200306126550034445180340031050f105581c2e40c0100740e41042e90540c402c1805036a0721381c034201191200c100140303115684201860400800c5090940e5080855082919030546505550441c00154150240ca540c0c11000030841000ba8002044d501c50b00e8040060003404811808800c20740520350711740520b0b250003000440e11160a0105142c0b155002e5100141c50f00402d00003503135101114580d0000c03903859401c094a0340340c001892807060290fa40c500c01445440c01424002c3c100251100c4540180350f0340b00024002c404400c2d5100301901c0450986071002400018061a4088c001c051010310401087c809610b5400780c19050392103038106020400702d6490b000c24502c0981e40865050751070203038114205036010307006108a030446070403203112800b500d080d84007101560411603d00e074001c10042c0180f9008000c5034141e9070000700b005c54001192200b00c030595000311412507141c10398010750400c004100000c0c008080c0e0480081206820380307200c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 779103084 1250 779101834 779101853
    0x1060810090c050d050d14070818060c0a050606031605030303011505130305060a110c0a1103070320010f02030304031425030c021f0206010b0a0504050a060903060c0804 74
    0x485030192a140c031008000d004024079100c0c010030004d84070311010541401d0203911001c80c2843c1c0400148030841c0b03040c50314018406c2d07560460300108030340d240001018007490f0900d580043d580e0011424003480811217024071483c0802c90141000d080e851134210101402c01000403009008000325007030921070758400100362810354071090980320303c04181c8901500c09001c0d8084047d5001e003114804000c200300461094014903802d0814842002000680e0b5460b001d28005410982d03c41ca080c1e070040741454829089182c800380540b4038840d280e445541c04d13003000140550015104191100141d6804001d20045452610145046040a640c010304500308010a81c40d071000c0031500c50040c1c024030a5030178244008070410340004110386006045e4192601d000e91140d0805030085d403c880da070b21351030000d540151340034003000d07800d008100240350440e211180400c2000d110106054642c401c00c5005440e071074442e46803840c60b51074480192030b003d00307210081003004400e1000041807401b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 779104334 1250 779103084 779103103
    0x106021f050c0702061903060e0c03071d0d060603050f0304060906050a02100203041b1401141c09030207080f03040e0424180501060b040b0901050a17010e011403010608 74
    0x100108041d1120b2901507407034026010040d510180000d03401c06d50082c00410369443d8221764131709004599448107040c0140c8401c5522070240002040001d401c02c0c4100f021800006035542c0d0020021111408a200400312200841e07501d41c0d121300034014000100070819002041c28015842d2a0420000a1540c0003500c541d2083c0302d00032400780308507030080c05085107180340010115164074240c2400c0407100590f0b261030902f071000380d502061400382080000c055040684800800c0c4a031840b00703540c994441c5020030500e00c8200c800310612002c43c080d0103c410b01940c028082d40d4200850b040c189000305403e000e2a50082108101c2c00005c20100f03980a6004418062241e10000c8034807100c1c510100c40443e41c81c074200c0d4044480242132540f204003400343c0000c001c91030b2035a0741102244550301613030002c414180080c1784e0940c414002403c540c640351800011501c0c0c0c00640141202c1c2c20b0f040f65603034840c0f600050040744030030b0707400d00c0009104800a00c03019152043c000e85500412 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 779105584 1250 779104334 779104393
    0x13050624040504020d0507030b040b06041503140103230106050d1e1b23131d0105190e0604020a0303030e1e0307020405100b09060d0b10030b09010602 66
    0x200c100140c100e5454196401482e0140040d5031760b480ca035452100508040300e03e6004240b4010440c09a41094428010302c500060300c007910f01814000c90b9031183c2e003084544002c2584584e152a034400c6042e003070300d000f50301c691281e4116603900d01106c8940861400b2a030400e80c50b140d420452607490888130b04601e0341000340c0c003104000c1c0001500c06500420806000c800c00c2003050f41c4180c2004804408071800107503910080c031070b248180d51528841c02a5240d101042c030ba070004440e9101c0d44011500d510081d840ca40300d02c01c00000a0030342e81c003142c0d07800d080c030401d0350960b103201c441d806403880c0705448038081c010524080d80001ca41184030b00001d010980d581c0c03085000d0b884e04101c0c0c9500e03060411102e028400a400401e07507aa48885800c9020b90309001c0450070500c0c0389944a020340301076150036818a080310040c00381640011224840c296190b001c0c0d40c4898035240da100310b0881a45e640803440210301c2052000804040e4458811548a80287c04130b18078400c1d0800c2004088 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 779106834 1250 779105584 779105629
    0x5040f0507080f04080307031805011b0e0a03030221130303080f06040b1e012715020f0303010303030c0c1e060b0901060f050c0f0609030a0801060e060702010c060920130506 76
    0x1d0560b80c9e600b0084960014105c2d0702e00500d8419000c0040411b0360140a996aa801c1500840d002d02100491a1000402591081c030142d81080c096251031101d26031014509418220002e074506208502544281c0c0481c1c802824442c2c403000074015180d100e002074400b070048514034001700c0c802000f0300301c80c0c031060600485440041d0307204418209102c00c000a141100b4003030341e2440149035001e4400e4a9030000d42032039410003180040b0f4007210342445040a14103507031039604e094000d410030b1250703c01000701c0450707040005030700c00280c2c8007011104842c50400680b1031620f041169042c400082c410504400100480c41e4001428810201140350040d129040d40b1129032402100300c0e41140240692020003007075003000000342c200c00e00242d80700d808507641d41c40155085030b400100700740c0117807080286601550183c1c440a40340c512401d00080d5041d515241c4440c805150341314498508219809249075141040f41415100c0701108100720718144070703001a0300b00c0c00303c289400d000c451 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 779108084 1250 779106834 779106851
    0x150904020d0605040e010605040f0513030807050f0301060819090203070b0c0c06030103030f02250302040905210d1103061c02011b060f1116060e0705040f0507080f0408030703 77
    0x1c141c00c1600200b01c05007060054101c6001c12601805480c01280c1c0911f10f02031180c502044507029441c01003000700200110308071542c03011a03200c01c004100e402070020400c49071421040c01d0000714000d02c0c8541e5072030040c0c240403042c4004c03501071142022505080419010250750b0200d2090f08079107409402941e0303500380088041c1080d82a170b41c0950301c004c020000100707041c0c000c0400c071100c2c81683d0130355a15100b05007c9900b100c4001141802c80755030080244014102a805068940d001e41c08480400c85800407840f452004a14089500c120204615804101d5801000001e42c03010760300300d00310b20308100410300c03022768000c4004040000480340010f690082e180c1d120b0200019080002440941c140f94000e00500a9000e81140c600300d049000e80c0e0f1458140c4920000000c0321130b01c050010f48464020700040507400249003d9082d002400303603281d219004240c0c00c0d0f000041150b2410b6500a000d40390003d01001c09a1100010080021441001c4035480516800d00140000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 779109334 1250 779108084 779108107
    0x100b0901090207051e0a0b0c1209070b0d110909090c03070614031306090503040b0702090705030c19020c06070614070e010504030f051612050105070e030c0f30010b15090402 76
    0x83c620174050031f400f417444148003600e0111340050031a10341c0c0c40e1034024152544000a5075800c2640f00c0c50b0300c00b40c8140440c518980f06038100c000b070810820082e9040c1009600000e46228050382c01032100d50101e40c1c44d48890405100c0c113801010f0908000c02c0308001d0541e0304400c1d200090404111144050300300c410403040e5844001090340140c1143c0c3c8490320341910101650120f40c090b0721813481d0303c000130191762040c002c0700d100314804c6c80100d05000403100c030305240d10120710002d020f5010380b43d8070003200d40382e0501401020b40982c10100e410705c0c031080d040858040203040d4008101005500034016608841150110b1350f00050b04040c02043e4100070b410702816080000f055100c0b60700c001030142048001102c640d009900820451726034407019240180d00341e541540640010074014031602d4038070100f0009880c0508800c8c1c0a440719152100010a50050751004155861203842811424850340e010b0481c103440555488a142c0654103c6000d556500342c451900010054102d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 779110584 1250 779109334 779109343
    0x130b03040212070f0815010303270e16120c140f04050915270a0c03020409051003050d0c0f15090c0b040812030606030105040506010c05100b0901090207051e 69
    0x101180003d40302d0150b2150400041c09802d8030a1001901c1121000c002104042c02998100d0f980b685418880540075802101030100344c1d01750001040150308002014880007074828461030b40e0940c008080300381000080c00701c0d80e8610b640d5a1041c078010881c1c48098000b00c0c2824840703003650350140c03101051165941c3c180b042c2e400c540d40001c0164180180d8862103506814000400c88059040ca040b00c0d640306150880d0448102c001d5501e02c012800e00c4185a2002502484500d8058a01a01c4031251000ea039015111040c0e0b0341c045442c10014848c051012041d00c070458548400114001e031a80350160070042d20140a40302c00308074100d00c03603046a01c0403030310781d511410700110a586c49101000c19000751044640b64000d60407041c03112440001102d1099070020002c5095908000c1404000c240003003685042c81045903017100450810041030b803081048010106500c1108014405000c40603400583d455006004c4d250004501040090380c000c9150088908140f0320903425161 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 779111834 1250 779110584 779110609
    0x9180a1523030a290a05060d02040b010c0209040f0506070206092d0a030804120f271805040302010c0806030a020409020109150905090105120a030e04140712050c130b030402 76
    0xb0710042102500584d40203c5181100151401d610000c0d500e21242e80c09994044032126404015200480300625040e484402152010300d840509540c0c1c0398003040c210174013079030b040c1c070032180340d41c2c0c2c8404201040040303591042d40b52001d04200d0520b540700c2903554070000c40510101c000070012596044540007002c08805440d0221442002103013005850120103a6055903004000500304007802d00a902e1010403000540c3c50121403a0501605150001e00544c0c0400f1600b1008000504081c2d860305c07507450b0041e1210010303c50a061401a08480404000c0001c0c0400c0b1010007520342e40200e40468030300d80582c1c0200c0d41541d244012118500c25070032140003041d000a03412104e550020001040c6e400c26100b420250342c0b10000c000c6070031840401c80c9015032000c904c280000340300d01600d5080c0c82c1c0c05840072811110f0480e501188030001c072500e40000b80304c5010342d84000554000c482c0c110391030014191a080540d400c132600e409050050f000310400c0040460708549441004103031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 779113084 1250 779111834 779111843
    0x30604140106031d0c03030a110f010c050c070510051c0e011a041802060307140405150306030c04140a020f091e0109062c01020309180a1523030a 64
    0x80660315407402400404000c600c003180c018060f0400004c420001512804900c0b00500450500614003400c8403080c0449600e0300c900d003c2d60b0f403000c0791a20240a80003c8810f1601e070390303031109120b507000361820401d54001c070312540e1a002081c1461f50000704540c01d0003a440c0d0044404841e4100c014090018520f82071010b40c6042440c0d10703242a40c00f140c06103000c044070180b111210f410084001540f03000006544040c080001c641da042c0107500003042850806099401c20790b0300c000040815a0380076100b80815000070400440340b8040c0500c89100a0485041001840509061a116400801452866a002070101c00041d00711083d9440f1610040c100b5200c1c14501140b21421105180100d001c13502c002400702e030060082640703034020402d158030380000c10340c0c812064400641c04001e06056000810450030030385ca40040000a0521080018045041c042036000c205c4a85118061181402c05030a00c1046c8245001c00007211000710303c0804c00c1481030009081c6207100500a1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 779114334 1250 779113084 779113121
    0x5180a0b041409160305041b0b0d050603031303080c1f020c0c030a1a15270702031c0c210603230606010c080d0c0201050901060b070305030c030604 65
    0x258140308500600540384840d500642201028040c4007161009a0700c00702030319600c02c420ba0300b851081e4890b40c0e006001e040340b55030071050a0002d4080c60240c2c5c00c410f440351400100b000d100305090140d11b800c0b00090740110320b041d510b8040d440c000c0704240401001024000741c020480f038001c001c002c0c2896080c003800d2034114128481000290b000c5608048039020702e0b900c10701545808140440081d820132558200300d103100010244240c3c00401c00c139109032a0b07000d80101d5860304000341c80501c00740b1020701e9001e0720120024082352401410309003198000c0087c62482e403007601404c4900c00388048013142441d0038080c243c81094240b401489540b12701d070b02e2907205041941121045a0240e0341505003001d140b0459076690584440d1030034160310660200b600c075440b49595512960080c80500e09290720032100c0c02c259000b82ca100001030b0b45500038401054801c0c070804c4014880307880c10381d207041d501c0c1c0d6001d411400700800e854803106000c4009011600d49400a81100346040642d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 779115584 1250 779114334 779114339
    0x2030c0f101406090a0f11030703020a03110f0417071220040203010b0403080903120d06330c080424030e061b0d060518010e0705090109030305180a 65
    0x100ea80700c8030140c40d614414241020a94040c801000d182c3c010140075003072205513640c03146554043e200071600c0e408280e58484a6074034a00c141005107005005a030f80251b555075070f020004080e14601c3c5408000389904004004a02d5203c1c03048504490204200c0c0000340b903511303403060805d007966125242200740e001c2c155080040c440054483da182c8010040386400f40041404100d0000740100c42c1c00442c208401e02c003040e004e2018080700c8100400b1a0400c1941c0342c2c0007192030b04252008a02603449000501c81c503030505541c01800c842c400c10034404000c1000a00d014aa16040700f00306001140c80c0100c144204441103038058620300119041d40014440007401a42072402c0010000b403914a182ca81c520011074003501a140b02030070754070749000300c121040495000706101c1817115542c4200052a07114911980c00700e40da01100e0310032940c504050300704c030070f00010001c00c10008101f10700c3d404c1b07a8105200b1010350fa0186481d984800400d070381c0e1298419540c4210317502c0080d10000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 779116834 1250 779115584 779115613
    0x601091e0b0609040e100e1f0b03060f10080304031b05060c1002091305010f0302010e37030b0f060f0409050a0206090d0206040e04060b0a141002030c 66
    0xc20040c0030400d0a00881030359400004201e55100140641c084020002070b40360f4030f8980c1060110104140549801020708080e01c1c04488589815065a40024079107080104c0c0d0000d9201090483d940244079040280d000603031500d400801d8900e1401d405030200d04200b0310148000c0291035240102c964450f22400c161510b040540304500d40c20092240200311420b0400688a10300150002002ca040c51140302002035007060b13103d01d42294030f0000c0c8106c01466409000d00805010b8440e40c1014118000104130217401050a4060340014404002000c030496407070207402501c60b644d0350070300070540c1603a509000741d60002d4501138001c0140111641d0100b211801802e0448420000c00303203600600090758030301c1c100503000e40c0104102c0340160030484014000f00200a100795180001c6500040c00da40068000306410300c0d105082000b00089481610481e50f4112043c400303081c640101d542c0c61248200300180685108690503038614005c005070344003413401c0001d9580700800c9525 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 779118084 1250 779116834 779116841
    0x90b070501021e040e04061d100902030705150d200a2f030d022113030e031506040b040b0a14030105100f050111030705010903031a03010c02060a0b0d0203060109 71
    0x842c452080403180044411000c1c00c81204c0c1121000d003402d403415502c0d41c682000501c05044031102440d000e0898281c654801d0207650f101039032a417030005104035240140340c80e25030a900454041c0880b05403046241e24074a003a01c40c120480c4401003004101429030b442c80c00e080c006e184d00b4001000c203d500c400e0f600002d1380b030010020a07400c034450540703182c9200304031000e20038541c98a0300100003680d903c0c0c07080e03001081000c0d41e4000300310080d2415202c40d001030004031f5048003403e406002a804259000442e9100c5400440007408022885e600c0b4000703001003d04854030076551006501e0b4151141d8100e4015100700500c2a12030b142c0e551080c040d401501d11025109500c2c103400202c2220003840c1400a440900802030845803c2c58019100260060300110003480300740100070000f00c0900840103404e100c1d907004624010701c040724180101d10281d0300c40c842d0b41402e030381c0105130b03a0000308284c1c00503000001080c06080b02000c501e4800c0c13003082c040d4150103404d00100d6030780c00540 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 779119334 1250 779118084 779118097
    0x7020d0b0c070c151b03091203020f030301060f02240a0b0f18010602010f050112080c100203010602160b1e0d0902060c0c030c1f0302070c090203070e0301150b040e07090b07050102 79
    0xc94030003117500003022614421800300401808903144210500403403002d0405901e2081c0300340103c0308031494010707607149150826030208002070002e44003072803070b65418000c005115440c42c0008088000c030140d000040c5c180100700100c12a61030104c400b5613a54124020408480a401c0c54031855070400325501d02c8201340100d86c055030900542c40c0014403a03114850484d408200e00100c40d4000d0390310841c1640c016124401c803480750700500c0c403c0300070510095000b070009400921034071506200c0000406010303404920301640038040000c0c0710100581c0112400c1d55001010794640b040941403000706450a0080d401540c0440c1404005400080107007910700c00f02d04482d100400300d02040540c40c49100032070481c111041c21680224002d0300508440791040200f0509603403510780540890f00202c2e1502c00240d211b245488942c202842050300c40c10f505170f80311030030724280034294815200e10f00c10703004502c0c2850300207039240b4483da00d0040a0106580b6451352001d81d820294042c0d000407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 779120584 1250 779119334 779119337
    0x7110109061403010504020a0309050f010b03070b0708120910020a03230112080a0e22110a05041a090918070806150103020d0b1c03080c07020d0b0c070c15 68
    0x440c00400c6260091200003040000852064034683c24001884040d41000003c403080c1902c984042c0001101800900591241030000048800c5980201842c1170b00311340c4600003904c02007003031502240329101100e0102000310048ca5540c0c907941921403416250818110b016403000c40c82e400f00c2641500400c2907001c120440c09550103000d6030303140b0420803e1103070004c0101a501400c00041daa04040e1500802505110000c8610381c40403403c0200981500100b041d11101c501041581070b2080030b80c84c10703001d103440d400c2502c0e502c1d003c1d04c2e600c941e00234080c22003800c181d44501c0c884400b00f203c9101c08060402000307800c15001e1102d21502117400200f041c0600c0002003030100d80001c01e9031041e104007400c542c400b40141c0040d030095000380c2052883c07070b4962081c40425100c0f003079040c0490412401d10401d022940c1030081c500d40c00944000d5070494200a940e0140e41c40c41d074400401500804100500d4946e820003c14510440700c00400c03409041c20009004210000c07600c4148409 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 779121834 1250 779120584 779120597
    0x905090309030c10030b0307030606170d1b060207150504140a020612181b030c0a0e04021002071a040e07020105040b0a150b1c06060c120f14071101 65
    0xa9281458580c0581d04000e40c043e404101000f080c0c0c5840c4000700c000e07420034140000c2040740c08000c42e0a0850139002500d03070340c1c1c581d4010004403003a03007408040c281c6444060b11100d00000c3c4024254000d02c10404406008060f00074103009040d81225401c3e0342c010f6091090082d2602c0443c090181280e040d211608184043c4494031804500300da001503004000c070b80f6281d1151044100201702420192500030500050a165081000f4252000c010500102e14400b01c1030101480c1c8a2800c107000c0c02000e5059041000706c4c04031070f805402c207a04a0f07030140e005030720400480c503042c0d480e404000d82080c2c014581100d00440001841560844481100b0b5907079007a4080e070a0b20740a88008000c02c1c03180b40001c07003d149076845020628010701c2c8440b0300c2603440c03d44603031a80000d48034100c0d240c5075004200c030307801c454800c5030010b000301e05000c0c444036886d0300c40f4202c60020450903400d2050405d22070341403074451600c00c54031107403245601d03803a20400d04040040d100f650340c220f17000c541c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 779123084 1250 779121834 779121841
    0x30708060c0a030f06080303040605190207030903023303010f06050a120f0e100e0105060d020d0311011103070f03050601230f090d050d1d0105161a07090905 69
    0x40800d1841c0300d800080d81c003614003400308904030001d052008406000350394444021911550a01c011405540a5800401c2c28108515040b40000c0a40310203041c04e403041004000298002c0055801c0340d030102c5208c0040c040003525510050502116405c482c0c00340c440740720400c2684005941603030041c000b040f401940f2100c05454901c00e800c1c0010204032410100e888a2003907810007002c071001680041b503a181311030036551a000c041040d611801d5107d82080f15001c00902c07805a1102d001c035802d00c00d00c5a00c7d004143d5280301e0382c0018040042903441d800c0301c50402d42020998007a0401001d40c0ca190620004050403942d14040000904241c04a649036101c0c0154403040c242810308041c032046032050600c4c3e250300008034042e22030301c04c5c00b8410041e1313120011205440e01660181180440f0200010300101c4000a80e0820500032900911180d17401010795040f035110001c44485550345082c8511481206103582100941c0380007000aa19400035000048031500c04061000345c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 779124334 1250 779123084 779123099
    0xf1209090f1a10020f0f0f1603080307081b07060b040c0f050301120c090603080421030c0b06030f0d021014360109081801080405070b1b0304030c050307 67
    0x2071011214610600511941a02c0b0f450440030710041503201d40111100d000f45007202c2070074901c42c5a80c1040b19041103442c007886880511101c411030713410f80d00280b051411503545035541e005c050103000c00c01102c4d00000d159090b59082c1c1c0111882c4039000c0303607110169032a148001d80051000c031806103013000740d141c4805000d5078003846007440c1e80d00d5282c11682840c10300c24008125460a49140e103c101d000100000507114442c00303940102c4078035a8503800c20000510041400b04040c491038265802040440e601481c0c10b050180c2c050200c0b52036031202e80010749420021100152140a40c0301c103841860340000c2c102c0c03e05141e802d003e00403141540d10629070040202c0c9c5000d500301c110009000e400d0050681849205c2c0b81d42a00343c2d5001205400a0844164100403580ca8000240000381103018019010300b40200b480c0056042c54503680e0a07440301e0540c41029042d030004603116090821380c0069504013400e4404980d1140e0384c9040181030800c080c4183c0c0d000f40203652001c904030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 779125584 1250 779124334 779124341
    0x17010b0117060108010506090613030f02010801080f07090f0209030d03051006050913200304030207141c03030b060f0c010614120604030e06070204051e2d040f1209090f 74
    0x3144140c448001303507880c0078280107890b07000c1c8070035503440b1508000701110440ca44210705d02450103005030301d84440c074500c0058070002041e040765040ba071081203004400640002e101c4c0640e034102c40080b071600811890355001c0c0c02900c2c1140e03494000c88004100b180d5150b4041482000325940c00c00c0150f660700005d42d450320814184a80001102907400440305054010001c40c91088401614440296a000c981d0740c009a40840050300095000c200607a1944501c0d0020709003100d9481425008442c542e52407401e2483c01002d144d160141d58606684800681c2ca08415a480c01aa11a21019170034002c000341c2c01044000015440403503404d003090318141d9460100e0714002c02564480da14199051a09407494540c0400c0c1009079800584690080303a0051940380a0503542c0d0443d5070ba40424000c000340100084000e80e0422038440400d03621403c254500d01c0c04e11000350300c5e030b4184080401c0c0ca00d00d0148c201520f04a52080d4598400120342c102c61000304104101151061842d064 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 779126834 1250 779125584 779125591
    0xf0105130e0c0408010e03130603050c030f09120f0a080f010e191e050405251511010212060306100509013302070503150f16050417010b0117 62
    0x11000d08a400340070059610350352075004000d9400b0142495a01ca20107030943c0d1350714020b240103800101c2c0500d41c101001c2e44200103840346e0301307003880715207007802840c5400d0000030800081651510080b48100005000001e000c03004804030320307a03c4007100c4501d601e540c0460595800604400002101d86154600650503070303184090040796525108800003022003460440c8034010f03a90718000c841d010f904d0070100c0b60700100c1c1340045890310386410000d007050007405030925800c0b645401807412400c1fa80c440c0c0c064580789413180085140c441003ca410b449072894059231507100160b003280c841461b40b000c0d4800c800803002c0319071f19526144566800c4c2d070f16100700c40e0050340c0180180010740c0220200a0704a0015146401114107891f0f41c1c00d450341e0795600140503800041d000e0240341010720040940502003804180d16043c060b0f400261124028081c000e05111192421170301441481100c0040010f00c043c540c90011f0f083e2200d00900c3c003100024041440c0c059444101c20a900a80d4031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 779128084 1250 779126834 779126857
    0x501060801151103071403251103010911090a06180e06060a0803070201050f070204021201050f011b170c030708030f070c02010e0118080a0f12020f0a08130b0313020f0105 75
    0x5e04070030f0782c3c460182084070300035101c640c082403040601d0300d45070241050204d040c0c050044107014680c20010b103801442d8211a0181c0d041403490300106064110000d0200d8013a40c500f049599006049002030010742c0017200e610998803c0d811201020360000ca0540c401c54007503400341d440d080200841507000c3d10800c0c0e46504240b22090141d802240034081000781700c1a1720303180040690008089901c075201d204170440300600107109a007800000e15196900031308108501c183d05030208214441c81c010000c010003d030400c03402c0344440c60070960354405a5081201c1d01d800062800712000d0300120f070040417014000c80000c55040c402c0351160012a01030b11290b1003108900011100d086ca24036100d035150103150030016000d142000f104403840d018021401c1c03080c645160075645002840040d0045511000c034400c0e1040011840c81100d50344211819516076104021101408160340840141d04010041003e110510000404601d100b2582036000d22024401501c0ba401000302d06035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 779129334 1250 779128084 779128087
    0x1a0102070608070315080d0f020111041e122001021c030b122a0d0c0e1306020406030501061112030c070f0c0824010e040609150501060801151103 64
    0x10a035401104425001000d500d4041503403c0240305d5413106003034660141c40140e1007640c5400300d4035481034202d941d0240074402072240000701080c0c85003900490003404000c0080b136029946803901d0f07003242d0b4006c0009890107180704e4004d04244290003007001d007180140136428202000c030762000c2804020944041d001ca1201c034205a001c90042201c10704507504555074044c074224070170007003049000c000030030450402504941a4013811803d0880540350040d80001583d0740095645140a819a65541d540d405550399094410102d40c18400010740180e10000f00800d0031507143e0003e0341600c450b602c40c4181d12600e18000d50b0303194070300b054100c0f441c0000d002040c0280001c2c00200011030103206940004081030311000107458055200103016805100c1c07103016424a04050065034018090b01e001541c500070500e1001a002440101660765400f40c0c01c081140c2c1708003205152101c414104001e41e1940c50251a805003030007104840c8100710b05404407148205c0310b40360048007103005103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 779130584 1250 779129334 779129339
    0xf09081306020309061614120409060501030e1e070b03040803061005090102060f070c0203060c09090619030201361a07020f190e09101505030322080118061a010207 72
    0x9034050f01d00b04101c520711041c240503144030740d00f0045500c41d003848c8201346641d00e1074200303000100d512540c0118180b40c10904400c03510718001c40e03550b1401100007a1104408001c85406044c084245c01080b100d5801000344424000c608020750700ca040c00352055040d100c0802407e907505d000e02520540140d01c00b00c0094540d5903e00c1940da008281410041849081540020b0800700d00b1100040e090781c01040c00740d0185002e03241c0b250086c1c020740b101e10341d80b149800c6664407131040f070001905114400c170241e514466001350300d5410104801c2c054550244150031019442010b1081e54005030a04401909040e17a0b88221160150f005000c0c40c0d00200407000c0c17103115203a603400002c40001401000500601a5209c6442601100c01506814410402000c120303580c600250410301d110700c0c828409500c0010803600c918500c000307000d4601160118850007000183c01030342c0c00b9400d100741d00750503160110340c0c22000d91040c08240095500058008a007443c0d210000d8010703484503504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 779131834 1250 779130584 779130607
    0x90308090d020a05030f011a01140f03130606030f020102060a060f090b06070f0b0915040314090a150c170c061609050d030f02061b031503010f0908130602030906 71
    0x8952071510103062528196601c1c0d0000b81481030343c0c502000e19035116040c00390703051a40703182811740002c00d0030407111b000c9081e901100340303004001c004001c904000010440b04181e1800c41e40146509c0681400310703039201d05d00301402580e10b08049016104000124070851864000c001c00e81d000c168120b100c003450060900040e180b240a40da4110400300004000b1600c9909480c0c2054020001c0e1405402c103a4202841c184040f8100c5025160107400d0000203a84250b4003481100005400307616030000c3c10002d090502c4591151202581845200603625001807440070303014000e10b45000c0003803010b1030030380340c4d88600c4c2c8000380303681c114030000350400b45655417041c60440240303000c0d4619601c030700124540002407c8113501142251600750b0b6200e030b040000650000c1142500e000101e070301c00c0c2003802400003401c49001358101100061858a00350b2101e0300600410106025400309801c0030040c0381c1c00146508001e00e6940004545940000301310f58181c500a8221740c0350131030504c00c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 779133084 1250 779131834 779131849
    0x1339150c0618060e07060f3e010b01110c0303070209040312020703200a02100807031e0b1206010305070b07061118010905300309130207050c0109030809 67
    0xa0072200c0542e1490410300e10450068085452889841d001a0405221008070703d40078250f40070b101000020440c84140c01e900c90720840340c5000e100010582d03600d0008144a4182d154604016450f414404001d182c100540244920900a0321007074005083d40e4115512184000741d501e4066008201d620f00500f854003c1d02d0b0702c5402890726000301908410144166804080c01f500060240300035200c4000010440903111500000109190721080e4040350f0110106500d800c14041004009903d240c080c0c3c0200001d40d1405001813003185000201c2d50080030201302660040b00000c41100d440b50001070103a0603680c00800800360756161038200003241e40000340441d16183c0322244400101c0c1140050481e40000118104440c1d40c03400c0014441c41e0b440d48080e21980c0302444607505c4080c950700b2001c0c0d04c01441084030100e500c0d21170040c510310840c1c24035a042402c20102c0950b5007141d034040c243d91031140060b103038080280c100441e111070302400b020704003180c02c001181b0507260840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 779134334 1250 779133084 779133107
    0xe030a1509020607030e01030c0305010e04231504051006062001140c36010e120a08120907050f040b041e090c15080609133915 56
    0x9011031620703120b901103403094001c82d00803008900601b6185c3c14560f0113010750016808645000c002561401113008468a005400a0560710810030110b120f0701c0d460600303410b0340c92000200c3e22b02c1e0750100320142e003050301200c0c1500d01c1d004807a001c81e2160a02e00461040718003036a120004d00b0383e549000c0760191404001003506650303564032164070710207404a1a01c54080c4015164464840c0420760080c00d00f01d111401803a001d000b1703419000d04010200d40803070301c0e003864008a189070000c0454816811220390032994400c21800008200d002e038010241028003000c180c2007500d900e002e482d03030369046024095200d14240f00908040c1060761154104040003040072680d07512110014200c1a40d1000703180706151110180018089504902e800038404035800a2044070701c47c000506025000e85401d2044001c1008600c8041281042543c00303034002e050b42000c2c1b26000303030305443e5481c8000003442000c000c407145284048040400700484448440741882c101c09140100d64000240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 779135584 1250 779134334 779134373
    0x100f0507053403030501090b013e0f010e0d020a0317130b0a0c030606020f0714180903030613050402030601060302030702010e0109143f0903010e0d08070e030a 70
    0x1c0c9000101c1011070300000b401d6038083c0e02e0000c0c181d410b00d0700715001d40c1c08403200300b810b100401c075010a1103146040c0c0014402030b51004111202402491010b075800c200301520020302c00c24200c82104541076002c401c124400300201c9403c240b084000f642c070380b07880003c00744c04103c00501107048100c050b110300364480d4000301c41ca142400c01c1e503144554808140c40408000d41e888841d001c40e02d030584a03000107041d0a000410f07880c007401840c0c2e50707512001d0285005101020001203142e46900d403203100d031901002441161840d0036201d00b40d403600129906440b41d41e4501014140c8095441014000c40c1c0203005020260700300300c419000395202a00d0002150b40e030b0700754200410028440c035a501c910500005844900c800c110030701d880c150b02c000a090025805e03002c610107086c0c0941c00101d4241074020800366454500c5c0c1d0303c0720b00985420b0354241d4200312158020410109482108070400c1e02c0d000301d29110380c1002c4407002d440d2040240c250384040d1044c0c0c04a03604001c481d0500c80b55 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 779136690 1106 779135584 779135647
    0x1209150c0e060f1b01020909040302010f06050f010203030a110c19060c17071404090507081e07120b1f08010306050726040213050108100f050705 64
    0x3481c140000c4c1c2c0d8040706010307070b07248070030340603108010b4009004030074529290038080d0185c19504540304030940b500001050520300859038400d90181a4011411681c0d441c0c220001805000d000300c446000c03d016200e0008401c2111200c43d04161620b00412840c514110050f1038129100c0c800b4031200084042110007040281c560003901841c20111100e10144000395074441c0344c001101d42c60610040040c602c0d00400d0f828060801c80301c151480b03280c090800c5018540556040001546411508400d005550050b54010383c0080c010214580e40111034030055408045072702c049000c1c6801001030001c00d1040c20340c00354650400d80603000c01d0030099050b040c44c510403454091640030209055443d501030212229138900410092941c4400b0540e41e95004038542d544583d08002c11000c00c082d0501809005500701d45030340e802c2070340301072042e02c80510a040b65500b140c075 = true := by decide +kernel

theorem cover : BRFrame.Cov 778956834 779136690 := by
  have h0 := BRFrame.cov_init 778956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 778956834 ≤ n) (h2 : n < 779136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
