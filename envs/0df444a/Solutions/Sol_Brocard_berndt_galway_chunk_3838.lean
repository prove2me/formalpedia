-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3838
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:49:47.319779+00:00
-- url     : https://prove2.me/submissions/abdf734e-71fc-4af3-ada6-86dc7a3ac19d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 690107913 ≤ n < 690287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 690109163 1250 690107913 690107917
    0x5060a020c01090b070201021b13060603150b030402060301060c0f0804141503160302030a0204051807031a0a120212070b070506010b181002070e10290d02070f1205 72
    0x41c50008104543c0494000d8100043d40c0c605603043e0014600d40342d50300ca040f21011411050550480e40030344030302c003c2d0705c290b02508000345616100020650400c04065840c000d03940c1200309248000c109000042c1c441e003080701d0440340186090301da1218545480201d0014031080600a070384046008901c00c80c0710b012181b1131410860311200d0349143d4041c0910f850000b2500d600840c403062060f6003c45000e41c0086600010f60300d0700600d044d442c1d2001669081766148049103410200342088640f0741c140c0f00d489100c3c0f2041c445600b50780c1c680c6000070201c0354103001d201600402030354204119101d050302041d1842c040c17801d0703034041500e41c4112107240d005800c007911144140000041d05801c04400c44150705064654007200340c030075005210f19114005c06283c210f20039400005105041c0da009140240b40c0b84004c8140286003400502e0303406014003012012034001c10f41c0407a900200c0d41110125441c0103030160b103c1042c0d0410012054401c1e0019090710525080c03d041c050740580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 690110413 1250 690109163 690109183
    0x30f0b0c090406030605070f080f01051e0a080106080d03180602070f020907020f1213031b0308030906070f02010c231605030d0513030807030911030d11010608010228020705060a02 79
    0xd034003085560703070b590100d541c01400d56030020b101c02e0ac08010b1000d414a041e46810700c8030b0400801c00d4146d4030501040b10303900103601416035079548410601c202202030105904c032907020300d800c0c0540c582c1105050600e0a400000409055000400b601000b921514110010b80c000781030320752510b800031001e034a5503641c040204c4c44d070103150351407a030412041050f1a40e103048003160f885403038116518503020001900e071301c2c0d107460861003002001400020080d40b20341c0c00070740681000d04040701c01410001010817110150b90412301f42d0500c22b0f0703102c1c6248142c0100c2030b9200d00094034102c0408502e01c1118074508182c00d80d0031015051240010080000c030300c08100401c0b582d510701d242c8074101400c280000300019a8140424070036882074210b011428041c0d00703015000e0202c0000286451034450514004c80d404400d842038a100a105400041148400075403070308410046031042d68944103d0122030704801701c0c007408058400c001c24406480f002d441c041d036484451001a50b2802204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 690111663 1250 690110413 690110417
    0x1202010504060506010c0c03260c0718020408100b06040b0d0504110d17070821091c0c03050c160f0801051302010e130b060a090603050c04030f0b0c09040603060507 72
    0x40c00f00d00c15500c500a5404c03d00e81041c0c16687c400d04681e24610000361003403000402c0400040351010100001005000100803080240480c500d0041101c3c940300c14071007604400742c41480301300442d600114604503402c4040c2000241c01e51030034009040350145411100c062900460600300c0d8280b10703801035000e140141254000e0900400800048444c10b44000b020b110003c1943e2640701d100d200038081443c4224050707803d101c0c1100843c000c0039210094a030400c10f011081c070514400900034040c0040031000c91489080f5480005000990340600c010100038002a103c8030f42c000c24440740110b20910030542104c0d40e552001410242101e000303240255180c000480d030491000010400060340c180c68024a480d0040100b0074805040c8261004660316400c07403132032690b2008024030714401d15440e0040c0039400c0035001021140000c203600a1100c04200501c00700d00b030340042d06116640600110110b9071a2415400c55000e180388030358000c0c0c10404080f0401155801c00391244401d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 690112913 1250 690111663 690111671
    0xc1703090901151707090801020a031e0603030e060d020c0105090609070b0a080f0c070b250207030b0c07031202071a070e090105041d060c071b0b0a030b0d120201050406 74
    0x4401d0710034180300e0100c000c008204c07030f030700c40a65070004140c4032035100702030342042400d0130340d00c14515099a0102900000003580c40080390000045050181101c550304c0d00100149030a41d58060101c018041465100e00404600d11140907032503011514501d281c0740013484076090070f81e01c19690364415a102700c0d150103500008104c0d564680306079604104169501c08054840940b56183c41c1000f5110150714481004968003144200b520f44d030040c2c04400810441c25280104001c4445843c400d0500715044058100017140444640c103070414100501540d40e02c00514041e0f902c0e51410111242071400405c07520103103d074031030300c2c0303082c0c000da40e20b2562356560b4440d000c6079015503000c0969400172010300180040c2c102984907900718402000072020f443d03d0541190701c2c105040360011080b040004152082001c1030300b401c448155503841840c506410441c2c124880d00505011000701582d955150740b00356114841d41540c0f85d0416800f1242d282d09040c001d018000485003036802c5070070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 690114163 1250 690112913 690112919
    0x4062403061a091012030309050f0703030e0409080f030c0c120405010810050d0f0203010b04020d0b031b03150907030b040f12020706020a0816170c071208160c1703090901 75
    0x10305141c6200e0511074151925150502d65144151000c802c0191b08151b0b54003280700c0007960030440782400013500b0303005044c000d145141c0140384018907403249014038140840078002032100c80a8170490104111900c2d102c0d07841e403203001245c0c01104170214461064030001007059032403000038004d5070020390700d6580c0c45c0d40d0030403903400b110786a101e000d40001108440074081b031980b04400401c2c0d80b008002003204403d03e0001400c2e44c00c441101181c06076110202c3c4007070710742040032410074101040204021001000003d44410b042c1d041000c0d548401d40010340c03c0310060100031b01469226910040b2428582030011984003084002c8030080c07400e100d5000d5841c00013030070a04494007640107040600c816640c103801c503008032800721a000d28842c5458000344c1804800c9030852004040642c4444100403541e20380724440e03202611072030041c030003c1c000c98070f44804c58004402480c0010b00300d409d50f203012103415a45500600c14446542c240741003612000c4002c0c10784900c101d6003c40d85980b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 690115413 1250 690114163 690114169
    0x30f020c2e050f040b0601090305011109011803020f1c0b040809030114090d050711030a03020109051507140901121a030c060405030d032004060c0317060904062403061a 74
    0x544102640403941c03c00200080c0c01c1c102c1c0c0c070f54044d40c181340028206d542d0b541d82c542500c1d45004030b00d0a00b10046041000f0796400b82006400c0300030902044900c51031a0003142240344581e044a000e201380411490741c26044030200592141d00c034080640900e0702e0f051054168000094141c4203500300800c040d207c940c0e80d03d545000d4240c02d4068002d2110606041c0c495920117201107581e080c000285d6440396400380300359a0350900035000418440740b207141c1103091100c9254140300c002c2c00142800740450344002d07822141088950b860382d0702d007200c40050b183c0c00040304043c45164104100500c0c0ca2000501440d80303c20140c00301e840003211001006524040c60042c95010384c040720a66940f1032083d0000551500d055003003014200d40480314402c0e5034440e411120200d0304071403400081551280c00c0c69000c00400c548440281409400520010310281010381155154040d00b0580c060031840040c0d20024800302e8070751140d480c40c080c6c001d00740c106d06050082503140c802541c20b003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 690116663 1250 690115413 690115421
    0x6170a0e072709080415020706021218032a040902060904051b0304030503011a0408150a060f12050c01020d1727060f0c04080c01030f020c2e 62
    0x100c4803401070005a800e0201c942840070a54440c4600810600700302c003902d030720a104031030b02d041c0940c076001d982c2c0f4104510410f0341d841800195045510480b000c1010030380c00316503c44800e00582c095550350180d1172400700355100b0703090040d906000360100040c180d01100080f201c80c0c2c08250060380452220b404000c100d0301940320281d08038200f006401c80602c0c0c16407220790300400c0e281110317802040803403000b40d40341c100722002c4010620000046c00050300e940c0c0c4021401a0314200b051509041c1000503840350807400b10242d100d501078010039524a665044a4084d0107a41110544166900c0520142516440d0155031600a680081e031041d40b000c20b4400c0381d614203031542c004600440c1e10784a080c0c6402485d0b903082010900d0889200c080d2410100614503625000700f407a81007504074041c0c0103801503e04460444100310402a4841c0410f01c070849000900380040c5065054600303401910a0050401d5207010787c04420326140c80000b4591100141b0311041c0c003000204490781d204032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 690117913 1250 690116663 690116681
    0x4212907031a0d061107080307110105090c0f060706110f120c1812030706410a0e070f090618021612110d0e011215060318050706170a 59
    0x10080f02c42801141450300302c021102902c46406140205a4403804d01942003a61141c000440c0c80d600400c00003002d004803030300010403178058224504a9400107000c03d0341c40d0800703805100003042e03101c1403092551100c06024459044c40d90340702c50f1110f102201b64050b8585040c401c9200c2e0121b0081300841c41554030200b084084820b241c0403000030460004499550303102e15100070014080000d84038041c10030b210902d10b800580b00c6103003084c05440b03c0340c2c140c503844c400301e8140f01e2868480100e410707160708403035150380c00207201e101c00c3c076100e0400c10a1303000380c1c90341d4104074800185c2c42050b41c00f410480d80394140c05180300c00900841016885000b00083c0094030481a240104503500c9566055900c0e038102030002011420f000750600400e03808140100301a4460b60711117507004480da85c85140c1c0e0400811010b12110100c0c00b80359624041c04081503520009041400004084403034031541000486084d03e80e100070041c90a0000702c28044840c0d118408107141552600601c252 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 690119163 1250 690117913 690117919
    0x180105011112030601450b120612011107210c0807020f0105040302041a030606040c02030409110c0601030b090c150316030f11041a04212907031a 64
    0x79580340c1d440111151002e0011801d02164860007046820034540851a601d00f01c03010783c0b82ea011300c2039004906d54040da45c800d80c5e100700c0070400d0241d40c0078040d0030650f2024003101e81e005181c001c44801401030001c407014554000002070301405001c1000b41c0346600300c88051150b048548408421035498810282c01418003000340144d0005261503541d106400b40d041c508a410240d07aa000a02600d1400e01340d8030b2040d201d84084002d030305050100561180307041d14180b058110a210003903a070310032841b030340a0745942d4443d500190030f50041190700a4609030300315651544c60b421302c65036150b803d82d007203d002d12524130300780301d5402c1901030445c205001e46201411a6185c26405c4002c2d410380200c0000c0698446a10700c403680e40344160123584100000380c07038545040c03000b0209a840002c411200ca40f80c148000c2000038080b24656942481d160f01d9051401c041e840e00c980f841f0b40c0e0900b4420450081441e240442101110803072280083e582c1c20300c0b0201c41d0440b0035040d01d4008e02444d070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 690120413 1250 690119163 690119167
    0x3030307030203191e050106030b180604020403021203030117160303050c1f020a0e0f09041e06092d0804090903020c090709030c0b040806060d0201030b180105011112 73
    0x544a40640c0c00355600080e420540d10181030781401d544111085c0f00c4d08031850280124240e01060120311550740909039078103080054407290000030382040100710f443c025450401c000200180c5464040d0b40095601902d070112180010284507221741090151202c40c10528084c201c010000107240a01a0315000412010344d0031528210340c10380c0060b006c0e800900c110394403a241e407078403015409030101c8101001078031948800001000146d200a00a10a445104c0500c0325079441e10400358010394054400d0f40c2c80035010010300048031280d14081c1c0800e1500740c81d1800e1080b80c030f88d00701200f01e5049511917240500551019060f4403180e01820b58a800e200c20301c0121996070180042c50300900403100007050b080300007a5443ca0445440c80040c9040b20204100082005254080c2034880d207c141080e0401200c640ea452008184901c07c0141c55029030079640280e2103400300400c082c10890442c240d54a12408140c003e20480d400140c58801c14010f811780400c1c02d044040040d94a24 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 690121663 1250 690120413 690120421
    0x306120604031e1808030a0e030c0307090e0a0c0902090411032e0308130806061519052703061608011418131203061401210207050102091905030303 65
    0x307506004100116014840c0300c52010b00300300f944c01031035002800003034021513031914288001441c2107007045095010350701040c000083c0369808500d031802d5a80280002481540c0745c2c041c00c0ca800f544110280017092129800b04041c610f980080c41c1101d000c0d034003400308a160014035403ca100850f223441401c440d50111020202191765507100c1a241841042000ca451740c482e42d603035034000300c10342c030386128041010841e4107018050716602407070441301c696036685841e94681492051145509078130509000880d0018003031400d07120044103062042001076119040741205000d032400891091149000003034500e0703031a1840c038000c440d4075070700c00318240d03c0d10f039050241e04611005594401c150b012005407120380c20b0344403803041030034884105034281c49090015402801075484c400b01410a401405003070040d8810443c500e03000e01e0715a000384441c9040140511105409a210318000595441407150540181005000c119810340e550f070820540e204212085200e8690150005d10000b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 690122913 1250 690121663 690121697
    0xa110114071e09051905090c040605071401090c0801051905010807211e030801050a03080a0806030a02060a090f0902040e07110a0b0f37020d0906020f030612060403 72
    0x30300050b6040341803519050b41c5a03000100c003d030b0121100500100b8080c03040046183c20030405410842030340480346014100702c8000c0041c03003040e4018046540d25600406000e0003540090740c3c0a030003501c001c500760b849104403406000d042c0d800c07001030304091014419030307016441014101c0e405000103111071403400005100802c0b401690025844801890030007268a45036030141081180556068030500c1d45006041c6a0068004501508000206200040d11981203918090650510803040d6452600180c6020007a54009400480c04160480c4846d000144034045c0c0c0e0b40142c811044a40300c042c401c049003e00d03c07400e81c000e10200301040d4414090340c800c0d400180c0050655003034403c02d4880410f000fa00f601e0300340ea002030380010010f01c3c503c0120b080c02048403810540104400d41d1810949004980c80035803100c0e81d0000b0f1144200381c25a0000b0082c48d80180e09644602d0101d1400d0f2041e00211145800390b081d01680341d442078400b0920911803980b40e21030301e000040c2504d803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 690124163 1250 690122913 690122957
    0x1a0109140607151e05070e01081312030608071a0301030204050402010c0b361e0f2b02060c16060204030203030d0c030b040c02120a02010b060a11011407 67
    0x480e005082040742e14049088800069400d082c0c08102141020410303d007000b2a500008006140501e49810300c5403190b0300002d0002000400d107001031064071020301c2c1d40040440790074014440744030450300e41c0a0980540080301112408804c0c4c8085964410300d0391240d83c520343c000d10040b07008000600041c60140e0140e40c116006150941d100440396881424014080d19406c403906840d14460003a21f10400d04502d80c03170541000d5000c80b1042d2171130217075501d1402c140154406120031025000800400c4000074504883c1c08540d01c04440e01c025003c5500400441e10031280c0700041c2c40b03089400085c03d41d00030300b25403125a240491503d030200864007890000c80d0f407a5000c10000001d40e904101900702046111000245503600080c0502164100019030707004d18244a0010742c083c0c0c001c81c01c880802106038141d40d0343d241d120300490051001107810303584001c0104040307051503440b429458201155030020003040310704040300d0a03001400c4400b240064000d0001c007011640c6144 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 690125413 1250 690124163 690124199
    0x901140d081e0a030501030605011215110904060306060e0f09211204030e010305060f011202090d050a080408070e10030809010e04061d24090916060c05011a0109 71
    0x2500030340340b100304900144141e10038200000025100d1005006000d0b403803160500402c002964004820026503894480e4503840440c401d540355a0a11a944210000f045841c614070090007000f000d62603152920040c000f0b805845190343c0c03904c00040545242039885402015080e001f0901ca0700040051410980a038580742036030302d07007031122864080b031f1901d800f0b0180307100c0d4403040e0040c0b43c0c88000500b1204004c0801d403184c218440d26805990700540a0084000801e0307026913a10000c03008982d01a003c4040144280b080f0b0000e54240303c0c03810040d0040e540c014041d203142075a52440400c08401c103680701c01d54003008103801c00004007590001c3c45080c01c1030421600e880c0c50040020210f40300340d071103004032108820000042d02c91181240c0d600c40700700400c25040c503510f1422130040400c25040f260180d4854004900c1090f4104241640c2e860303220105644243c45000041080d52058803c075500c0d0700708140c4400000f003590b440c59503d178040e594203118920348640c0c1e24400003415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 690126663 1250 690125413 690125437
    0x2031e09030c0105070f03051303140f04030f08280e010e271806090d0c0c0320040507080f0c0a0921050f07182703020c0901140d08 58
    0x4050140c0c2c0080c041d481c8501c4168682c180d810070312050103402d0b81c5000703001c070954165007148400000d40240e00301c81e034450752007074403512402144a8028144100d030000303800740115007030203c10020002c0c001c1c42c40b20f0031080124800c03140d00013203210711038a00c0691400b28180080c00d9696503c00c0d0a810b9221400424070360001c0f900800d01003028100b201840c03003a04002d0100240701114140c800d03600c8580000418141c504182d41644595880e172401c401c00c590038180d0001d01400e640681c0c0907540042030f004800e040040020b039003240081203540200e00740300004011a010b40c802510a40340c41001c441e00e60340341041981f01d03601c400710900c107100301074801085240c420070508460024010741842c01000b6802c00034980040510015140d511941041c0000038030746034245060003000c2c00229018020707918503590007070096013081c00080c030080b08c00c050680c002262695840207507500003103a620f8111401c00700006004094100c0c0c0f200c15500c0029407001c00610400301c0c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 690127913 1250 690126663 690126667
    0xc0604030803040609081b010914030c06060405071119020f090402010206040311030c120409060e01050625021003020310080706051204170403030206090f062e03020622050402031e0903 81
    0x100050756121f04c10f0203584055a035441084d00100305080a002681c2c0041c10011802c244080d40e200b55030303140082c8046d000b10f0f210000f1400c51030240c4a00c80e41d0100304000d071402a034070036800850f50029250705038400c4007001070a640608100380c0407405682c041e07010b403400750340e5914240c8803080410100b211a1204102d02c1ca25000700b0700c195907a52040b00c0d205e941c0c41c0c0c40d1280c0541520040c1d0000c1000072a07200041069030f640070708480310401240f40c41800040c0340040c8102c90006040040c0d0003070004d000106031594580d004611a540500320000340b2520340070f16651b01c0c0d03214085c03000403d40030030880c5990640b500800358414411180b4880d044800d02c05290250415807080700580d118900707000f015030b414888244190840c0000340058501300100042e002078200d601303502d11848824040c03041070200180c030051500a003460380c0e200d500c000c051010964600c8205000080300c20045181d00d007071b000301ea000e00322021800585540000e4415011000600700507554442 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 690129163 1250 690127913 690127927
    0x1309091406090a0510020a1b0c0e0c0703020d03090507120204060510201b060f09030f030c0f07180c1b0b0a060e2401021906020301080c060403080304060908 69
    0x4000280c0308400c401c003c0c00c030038000340c40c146181c09104d0020b8004240144502c540141e4040114004222024230100544840e0300340740740c400e07120350014402007682204001d12616a2002021403034882e0707003111121201c040d421800c4031201000107205401c0b02e0003c200c001035000c00035200707900080000400c541e0740c60001301c140c0d008052103030104001c0f0b0580300c00e03503d02c0c60f07200205e02d800380e018001e28000750f041b04100b01c24004c6040d215610110703103080d0703500e904006e403191890064200c800e10104050000c0da01d4111500c012203c3c403c8100c07103248004081804002c88440514000343c0401001b1201d02808404001204020004003088907041b02d0940380480a401036543c00b1321707030406100040544401e0313085035024400010034000100030902d6540140e01030140307101702034040d480040717040130448500d800c8010803030070034002405500d0380218102c940ba0011110030000301824081d86cad004078400a400580107100103000f080c4240c1040640300e11a402c11854005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 690130413 1250 690129163 690129203
    0x4150803030a0921090509180a05100c0516020f0f0d0b1905010302010804060b0102120432010903060b2205090106090219180302062b02130909 63
    0x700311409070200382c0390b003964014481d4a030744641596190843c5009244101070307000c0c10480745803141a000d00c0b030040004082c407000070700a002c0c1c01701e80c40940e40c0c860f0b501e003040c0c2d40c0ca00c1800c2000c03809138981911844042c0c011812140808031500e0150b000c030710f45400b00a04880308126882c0c2145401d60f00078407130baa0b9010445903251007100c1054142c03c0001c00000c18071030b03000b07031f91070b601d880c0400600140c0e811201243d840f90b130000d004100c40c000c03440101d0500b01030800850314400c1c081004074026141500d00b03980d5103010408023800700e0f4250f407900c07054071070425500e010441560303003440801c02c90b03040241f0300d05001d416074014150300f103100c241c2002c5c034143c1184061394881c2401408042030007628000c2460300c1055040520b40000c003450240e480442c0014010220303440c1201c2e007100b81d0004011a001000c00340c655414184140c0c212100360dd0f50090814600c40b000d1820a440c400e1b1072902400a41000c403541c14201200d0040c005040c2c00e030b681544c0301c2d0514461030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 690131663 1250 690130413 690130417
    0xc02010e130507021b06090a0e0a09020a080c042a11070e010902041503090b13030905060a080f011703030403080a0f0603030207050a06112808070f0312020703090504150803 76
    0x101d0740d00800a100c0309903105c402030358260b00c059208030780400c000c000690310b540440042d074180d10315802150316070410034802400c1c0b4080080d0040c01c1e21000040020700490400c000ca00c01356420720610018442800c0440094031141e50407800d2540c06002152081201744a040441802c4680c4d01d62140002c03002d04000740c0c00b41251580024003400306580994196500c1c030640c2c1014445039955a403840ca03080e07801441d00f81d00c0b0020902003401c1c0f41c8030f10760f08802080040d10965880d0302180000b40003020854400c1c081003407400002400700c081e46221100d40ca580c0005c2e50850302d03581e904a8040c1310103401610071039280d048982c070398095441200c0055111f500103007001072412060080414641c1e00800c01c1c000b4002100111000208081808069614803030401900345821b406045128040c00740c905070012444a040000f4404815815406030310780c404941000345e808410383c85070000040000d08040c00800150507d07400c002c00c0c0d40c04203a04000041d0b103031004140f031a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 690132913 1250 690131663 690131671
    0x308160302072417060307030303200706060f080f100207060b030610080106050a21260307171608060609120721020105030c07020d06020a111c0c02010e1305 69
    0x100c001c0f0288440c00603044040c4061900e2211204a9285055000203490340841d1001030706264949202c0b810340c1454000c0c642c0c034105542c40084c0c80c1d4695041c2000109814001c0411410010b84085204100001c5138110b1840d6580180035a542c030b400c10386c020b500240b10850b03d19031150110307115035600b48040380c4105242201d8000c82c80c80c0c41550307030945d04c20b540405e0080c0360020041c480c140130000540c4502d0302003201060720002520b0118840c0200c1421006400342500f07541ca18036400b00001e600130f000c80d68504000025802400b00480c10580302c08201c8801030055820f098003d030000c9500040c002c25480c2454071140120384c0440100c40881d03490b0300204400d100c03d0341103500b051001c1814040f68564882d8a03800038200f07200207013400c0e04190000c00e1180440d1b513001400d041c060340c4200150344031001c24002801003a002e1041031000c1c007400302118140390544802000300c201c44d0b940ca01c260702c01a001501c03000c2c507006610b41c0090328001c1080101d2400d016040c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 690134163 1250 690132913 690132959
    0x3130f060b04020c03091e010527190303090e07051b120c030403020405090c240c0703080405010e180c0912030336060106030e0a120302030105130501030816030207 72
    0x1441401b9010404c2c1400d003201040d482d034a104c6413400107030760701c60251140c0341d8242600d41201499003001d002c09080000c00d4a40c010003a010b07088440c00c4041402d02281e10074cca403007032416104c0400c18205401141c054000440c1403000d0044421841840c2c0c24007410340c415102c0e00c18104080c0d00c0b0640c00712104896551000604004508261051991240c401c0d0700ad02000200d040c0041c16004100346108030b0f5502202d0b407010009000c03001c071550001c40008a86c6203555900d0300d00032a400501c00c1070b0100f050701003012a2810704400040e440c00d0054803441b41591035440400311174010794075030364108000c664140010082000214000c6040900c0840c50100796500b1030100c486074458040d6030b01c0c035103488040000b0000b50513815074030301e820040359075401c4a03401072030a056128058411400d419204a0254055008505a07141640c04d07424a81c91422680705944d828440107000002c10000c0f08010501c00800e4100d40340b00b807054603410365403580c2003a08082680180c80e6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 690135413 1250 690134163 690134167
    0xe0712020913200c120a090e100905090f0d050f1b070f05120703020f01120213140d050c0f040209180109050a05040302060402090601020709020d0f1103130f060b04020c03 75
    0x2100f00c0da00c20641100c0042410340c0c3d4900360340c082c05981c41d041204a468101240841c5400e0f00341d0141c00104050301494040340d201c0d00e096001000001403a1103a51042840c2c4404500a400b0211700707400719091800080a01010064040b683c0e5840045031141105040c0410f5140d044442c0f030b1401c1300e01c0e01000500c00542842d446400c1301000390f20007442100c0c0702c880600c20b2200411408112a012124480c00820300001a90100780d2004d42c00d01d101c0c40041c000d840f202c00904070b80140c1d08110881e010003401c0205000341c1d1881c0d4400130380b00e540502c42c0c4009615260f00c1207981c240c4003600141c1040c280700007042941c451841d03800d13603540f080001880100c0d5588125030740403501c400c007030199060948002e034996030082c1c07029010b0794059000078842d0f402004228000e0031003981c1150342d0220303541082c5c018404400e904031540d0500c901035101e18130301e2041d00e000700c8100d844560030a4842d034410641c07580c2c50400300c034019101c064104096440344040c048400101000d16 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 690136663 1250 690135413 690135431
    0x41209050411190201060f1203051b0d02070807050114090a051002061902030402060904050414060a0e070e07090e04050c090a06050f0a0807090911030601120b010f0e0712020913 78
    0x645080e2a9618140442e031402c10100840b40e03290786810102c2c1c0e4800c60301c0e800a100e03805c0c02c42c2d49110380300d0bc0902140000c108101100703000205013076074002035400c4d10344913520380c1942d5854580912445000601051512260402c140003e05c0c10003c01030008607600d0b55030300400c40b10000035100c5005030304a8020001d288080560341e80d059503c1000840c07031490503900150450048c41c2e01c2c83d01071070f038841c001010401d60302d0010200b0001d460449015107403281c0f500001c2c080c130f0394981244d0300444000042c00b1048103030541c0544003640f02d03090103d0800124030001940100251418403c140025540352912040a80200e42051003c95094240014803023442900005280110b542c01410403001d00085174460955103d20b4000c44c44003001c0c1842c152500071105141d505001e443e00008518042000c004101803081d100121143e9884103942c5141046101c6c0d05c01070754040001840c1e080c494906107460008056005090500d900040b440450400f40110501a501c0b40f141d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 690137913 1250 690136663 690136687
    0xe01020f060f1603020301030309030816140606040e060408070b041b0b030709140f040f0f050f0603010b12120313140a060b0a030302031e190f170609041209050411 72
    0x40c80d0348103e414154515451954001c00543d01072202030000500418240303c6150025000c03551585c1198114809100000400752946010b80f10688900c1c90b05514a5401c140494036502c190303003200411f410700c4119100d00d1641c4000801c110790a010344103080158240300503c4d05c3c0a480208002d98403454107140260403080282c012411000c5038860325012079880315655a000036003a00c01245c00020000c9060117082c0d2141020009030400080041c1d4000840001d4404d8400f10000e0198081101c02e01440103900c40c1c0070140d540046a5840c0e40e503030b0040085800500c00066110000d041d6180c50a880c0c0e58004030701490b801c00f1002d032040c0306085c0642000b0009c11903100c01d041e855a5806541c902c0b50000c9902e401405542c04c00f02c000c6000e05981d4007030f00e40800500f00d641c0001005001c0b220880300340b0003092001c41d0320224405019803891040c0005407150150b51126140c0e021100001c0120208000c6d07030503030224242e112030182d841d10070701444c000e940f00e800316a42c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 690139163 1250 690137913 690137941
    0x207060b10170609010e070e010918050f071b030e03160303170a0203090c0111070509070807180501090509061f0908060108060601020715030f05010b090f01140a0e01020f060f 77
    0x140301c1c40344d03c4210042c00301140b0b0050780c0c4e40000a6080c071115000d50180180c402003440d42c0301000000c24100e90034401c001c10707001184240400a48506107584694040d034400004d4000d4a141d0015980c041001030b0040001e4250710034001d0445010255411400030039000c144c00460010300060282c2d034000107103118050300414400b03001c0d800c40c17a1070a01c1540d280c04100d103090400550030b160f0464650280444405400094450181c0c0d00c0c2204e4007074014202645c0000002e2100242e145044030758100500584005a5440902600c0c00082125401c002f4001c036510106250f04100c00142c82d0208107594503240e2540043c0e64034052900d420710340141e10018054018908001240e0707408107640042d50082400c4040780507040307008034003c104400d20750b14201c1c6048000f040a0a144003e4001703400200c0d0308545450040c0c00444840000748400c04440206010701e20344103025440c0750810103010b1040312001d2402c6010726151500942d0500310500ca0001844112611194 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 690140413 1250 690139163 690139171
    0x30f030b130f051303080a09020a03020411030907140915012706020d0504120813171f0b0904020f03030c01020403060b1f0f18051f2604060207060b1017 67
    0x131180e09540c0c41a01c000e009008010045074400e90f039201440215075070707401101c000e55005041004002461008840c3c25803054480031040c0c0f04031500002d00c18070308801c0850038000030309010319540b20480120128103043d8410340c140a207405254600011081080c071810159107568110103143c10300c046d040844000241d0200f2400300410312040542c0c400d000c20a99000d0b0095a81e02c1c0c950300180500c1c1046c0d040038070b079100c813080080102d03100003c0700c6c12248840030407a1221541070705203000300d454940420f034202f0203640c009030161900503d07421a00e0000b60a50b841c00c040099941d0882c4d025803c04c071030391aa541011b40040c00c0510700c20708407101072101070540b224184009017509050910120400540c13903910449088003108450082a0180c448400c001c1900301803541002032141d6440041e081c1d054444450a00307d440c0302080891804022158030399494100c040d5000110030f5a40703940701d031070200e01c1d41c480400903c228460313540c450b005909254200303c3d18040140c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 690141663 1250 690140413 690140431
    0xd0807050a121d091807090e2406013203040606051207150504051c0516050f040906060b0a1707030207030509040b0a030503030903071a090307030f030b130f05 70
    0x6803a04401040c4450b814210143c122400313600d41d41e50741000148600e2000c111150b60040c00b400082920584d041000000001c0702643d07502e00000000c018607225400390312809442e00c002250841d40140300140d0300d00c0e00303d010311f49a51002c0e41c502c24141544400110000f80001c00c00050101920903200a0300003221a01c036241920001990f071004a030050b03c5458041d0101d244205000d001201d00409020b0444d070f1100d00356401c60414071071080802e1350140142c44003840000740380001e517001d40781d0007001901085519000d110091a540030119401c0d0303561980171445c406190080d002600b81903580c00c0c1c80380f4001c40d84044102c405817102c024180144215000242c210080d900720041c01c8d05c0020394020b0000000302262015400607020b40400818841d000c0c2c0d0100c02015580d000d5800c41500c1c43e0490564200c03014115850000c90708103000d1080024825180300000000610740420140900310020390455041c07041b020355540e44852021101c4401d000e003580c0440340c0c1d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 690142913 1250 690141663 690141677
    0x905100e0f062818060306030506060906280807080106170f0309010804054204020307050909030f0f0403150b010915030e030c0a031e0212090d0807050a12 68
    0x100705160f040c407200702c40f001240d00b180094190407600c50703450f40d40d004c16400031034030b00305544040c082c001345400d000079920303400340e0000902c0324204946030601030381b80544420203240d10b00c50126041000e0008009408070704110005542a080114401514a000c0000368061400403004070143c5260152091a0070450752039111340004020b480c5001c4082c2040c00c4030b40c0d610b01d0140c0c01c154441c3e945c140414000403007200d02c83c14255100070070b0103007041d040c2982900401c0c503010083d011140254154864402071050741080945950016205411641044107000340380184e82c12002e00c1e011310000c00320701002486120111403028898851003040660b83e9080007c1507010748d40240d05400803140e2814107114801d03440f103801341c29034106503a1280070306121551200c078080d030207400080c100f81020910f815403006600034015650014001d282001ca2080c0c0300b0b80100c24525405030340c1e40003d1012032103c400410026100b1000b401c0303540781510300386c4000255500130400300945 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 690144163 1250 690142913 690142927
    0x1091b0f050a050a03110c1605030a0203031e0403050a0302101104080c0111031309150b030112120e1002010509011d030403150908042612090d02010905100e0f06 71
    0x100440d00c801c00300f450300f0b030303540c1086400c01d40c040d250300c00352401424400a02c02615460118820140310107214060343d000350380c0c8040590701d0710900c1d0040c0d0f040d00f081181da07100035918914108280c410310388450400380d03291589400c1c00301c4440d0035400350b00310400c030400d00b00040c45031705145062030080394145030030074007040d9460582503041c505008401d00f10745503109041090359491103100704440126a19405104c01a0418171301940b1840100c040201d110b90500041c0c03810b0b00c0080006290420f0b03144c8480c5484880c080440c0c0602c800b8200300600b946036058042c10700e40d120340000c41d0900f0801401800c403041754000e4480741ba81c50988440c14000801200c01310780d00100d40d012007441c425403407001810380542c01014031100040c00540103202d081041201e02661450044244032440b000d40c58030000101c91022203000c0018160740c1c0b8000700e0041d1801c4c010314100d00e40684400c08117019201001c01c0302c5c0410f08030a6201e480389025802801c5514080c2c03041c60030000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 690145413 1250 690144163 690144167
    0x13080f0601240212040b040504110301321e01120e060c0a02010e07090b1c0f1e0b090f0706020a08030c032208031b070b070807050c0601091b0f 63
    0x9003003518000c407180820110b0310030700d10070010300c00d100441204807942c90755110001d00869119106480c004d60070b06070410801d00c00c01040e20b0480d04803a210380e02801254244400701c890500c221000c0c001007004042c2c10f920340e0210151120743d105040e6054070804400904080c04400780324150340e0900c11005200c501c04a100760300951060461a1111300380c5030140d0140401c2c1c0b40e140410300c104000028066565000340c0c417504819154840c0c6004e251411800710402c0702c070b0140070728001e2001800002c08405c124001e5140020310540008265039900e1401001a500030b42c1c690b006a16030690707101c00744251802401580002c1614071015030303440c0030b503000c000e00d140c6462001200154100d0440f4201880040b119042c00070119041d24100d4a25001500c3d2000003100035101d4000c222120822110025003142241d0321503130300c4600488042c88000d128000304041480301040c2c034841008080c1c040c040079100807614181124a418280d00d4440e0207108000c25007552196042d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 690146663 1250 690145413 690145439
    0x30c0806070f050306010210050f06120607022109040207060911030714101809090302101118030c12010501050306070e09040b221104060501020705030c210313080f0601 74
    0x1268a00385a500c4e503030780301c0050b4144882d62020802250408080000c010302c227402407841100201c0f4200101c401c0313280100d9072410102d40c1030015038000c04004c151140b8a441c038040900342120400d1910781d1300c00c046000d90300140300c11100252102003500402115800d8090b08041c1a001001218038010142a4810340034029034001d001c000002482c183c414507802c810b0804c003480201c40a0360b15015400100503140d029401070060581f201d446814a000e43c03204102d89480d030f00d042c000031000803104070001c3c280c0c42c0c2d0315205002900003c0d40b01d2107503200121485400000361585050149410180001c000900b0800d10384005030055441004690300150030550400c940d07920b01c00c2081d1074a0a025800c1800b980c202901e81c2044240440c01403009029a414810a40d4460040e651004203000b1140e040d000354060540d00d0a02d6008641c0301080440c00c2032a80750180d078140e041d076101c12a824504941908141300a150802c25900a84d054030002c0540c0d61500c41d00e03982c42 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 690147913 1250 690146663 690146687
    0x31a070f031803111908070308060d0305040512100c03020d0b030a03051e0f0706051e061003200f0c1e03030c09030a0b07020601060e060f031b07060204030c030c080607 74
    0x2002418440c14244c540800c00c501c80c01160f000180000b40060600031060b82004070b08900080404000503410305140d200d0b2804281e05844103401c09062204010428003a00c000300b4203032160700100d0b000041180691007071061246c0b03005030348040c00c0000c001540c03201c80840380250301c0020740000203a03000046842140c041e9268034802010300c02d0b0000d2510556542d1462002d010601c00148202da0b40540c0c09160a5400f40040c00c03140c02c1d490080300400c030b5816034082c00c001d0032540c03601e0098204403080e131071148201035011240c2c0c1d0184429003000c20f032107210b4107001c1840b0b000440e0070448408241560b90440c100f14101038103a03a542d00c0020244025000e0200b0f8132141030f00c0800040c000258040300b1800f0300d18101500070741c0d8160034403c62000072241c40ca01c0b80c960400a0071500e455880000043c0785581e2000c60900100c51059889034600c2d040101c0c80c0805c4951001e84080d43c40307014600700b0701e0b203542440041c40e403880d00006481d130020402c2c009a1500800e9441c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 690149163 1250 690147913 690147917
    0x1507021807260711070803040f0e180607110c0306040f120518040207021c141b010c200d060c0f030e0c0405040606080a060504020301140103031b0507031a070f031803 73
    0x141220304413500342048070740e5026401512022402080e600019130364030707040e9000f07400012882da84d0f022003810203603503c10504200e50804000329050030700c9a410300401c8542da4046440c0440b420011a00e890400c40c0c083d40c500380452100010080b51001070303001d20b080c41ca0094280b049601c00e9a1011103061821031084e0f600281860440d02d4856200040d803150058000c00280541407110703003100c45d0080101039019450301c02c91138980403c00e40d0003000040c3c0d00c0c10600c031000e0b80c50900f03680c4035481d032540b4144401004030356030340c1d501003030a10944180b43c04510b504002c0b01c003070040400f640d051410315040c0b4a10310890345000a64080c0f00b5001c82d00400d40d61114288100141101d07040003215000f0005140c00344441c50300702c01c2c000c0f072003607000700408512101c2e1460400b00071b0000074001942141c00e0b242e03007500e1008513110503028030103840240e44c0c1c913600c004050101b4943d0302840c0350f0030300030000c81c2500302890f50716040482c00c090040501c1d503145030704800c2e0010f9000701 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 690150413 1250 690149163 690149177
    0x1c06211a060102151e071224090f0209030d02030d140f07080a0f1a090a060b03130314071a0a091e050309030d02010b0909190215070218072607 63
    0x4501000034088042d070411344c0700d0b400181c11b010700001d000c50f061401c00c12480e81000102003c02880c40100b28258004c1840041e5407410300d014a8054461001703260301c07058080c072071503442d0754042c00107080810943d00115541d42d44101010b040c3c0f090a4440c2003204907950070040c5071000c1600140d40049140b07440000395468102040040941c0e4182000302c0d441d0408490790300d080b845100401007011510402d843d41c442040d401903a4442c043c0509001081c0045003155044c50080c40c00588a828520107825050405040fa600014802d80d4004082e003050303d400b60b400303d50281c00c041100424000348030644c072080c0c694003134801000d580c2c86800130601c06012040c02a1405104014180d0b540c043c58104001d01070440d51226900c60303007001d0041488241c0020700280c500ba150b640090101e0307059005c01c07016200911840340c0104080020b02c00595450033b0851441c021294100d81e14204901c006106030744052108900f015000d50100c03140c4941d00246601000c1407401300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 690151663 1250 690150413 690150421
    0x3110306010c1412130b041202010503040804230a0905131e0c090c030c1707030b010c0f0c09051806010302060d0e06180c04060b1c06211a06010215 65
    0x103103243c044103054220f24000c80584003040045640140040354050840d07254058607101180c0452155202c0d420300d401c80148044010350203007001d154050300600c80305080a5a0703a007070318041504808041030314190005c060f5000e207401101c08010300030b904010411071800d80b00440307400b595200d02401c150101c00362020102140448540c030507501c101c0080000d90b5949200d0301805170401120f000c41c1c2442d0115400f184031f00380101500c6011900e103540c641300e07088160003e00e5844e03030b40d5041010030030320720703003c10300f40500070784000e2054190180e15840d103100c44044035005000c603040c00c40c406c2e1101990840001d21981581c0c0c044902e16641c80010603884000e2607081c0d0042c0e054010102000449034890f0040f50343c0310041002e60b5400d4601000700030890b409801502241101400320307203804102c10f01d14020b2415480c000007002c076251048009102c1c00402c40310003008000790700300208480f05c1000a0088803058072200b0904007040043d40350409840e43e0f0745200154800030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 690152913 1250 690151663 690151673
    0x30302030c16232206030b06060c03030c0d090c0303080601090e060f040b03010b040e1506180c03060117090c180f011806091a011808031614190c0603110306010c 71
    0x620003010100c40c0030300b85224004e14028054621050b5501e400e510001401810a90708843d80e60580101451840d03488140340c1105400007550000c90075541c50305c62000079241d0320250051030082d103c10b0950700d001c070001041210390390007000c6404d00c0c0905010107611028400c8020080844010820040400209c1d004100c140201584582082e400c0030154401052040b1308014802030307440559184005e00c440102100b81a40000d1540c0d00040e641002210103150041c1e414900f0031a420541c80c00784503881c10075507181b1503503003107007200c00300610740080c4a4444803903031240e9030740f140341a940b40e80c4540350502c603c000f040340c5200d82c0610003105030f01c07000260200490400801c121501ca074100c42d0f0094000e03902007162805119071007030580440008840c001401107141c084040100d607a9020200c10440d40820f1007080b0005c80803040c4241c1c030388403007811050040000c050078680c020090561101c01854540b020807000d6040361822a507000314282820b40318038120307183c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 690154163 1250 690152913 690152929
    0x161b0305070f06091a0c0304060902030a021807120e0c0402070c0801021801030e0a02090126010e0f1c0801050f0d051509330903090a030302030c1623 66
    0x38280d0b0030070b40d0044200001c95200180190007010541030106803c40c0d02001680181c620030b080c26000d000040c00100c45810401d0b1152000c1c09880e0740e200e0300d5020621070905500054034802e0b586042009584d032003130744d030b150428100f28244804003402456607251542c12400303d000e5500020b5400510911280400c000e090000003103554605068410310320050100420740001e05181c8030025031750f4006074a0700241c0d0000c01420383e030392074141a580c1180c0b20ba15200903501c050018a11130380002c0c0b00d0090992548e60191000d003112a03c2641041440d0317088482e900c0303101d009946803e9114201905490094440000001485c400500240c8000701d004285105050390307281070200002042e4000c01994080f2403090004040f01743c01c40c500800d4490380d02d80780341e000c0700c1900310024003142c0000319a42a60715050f5070201203190021903400a4000d80d000081550f40048104601c4949030800c003020202581401c05c0030032182038410600a400684014202181c0d850843e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 690155413 1250 690154163 690154177
    0x8030a111b0105150d021003050901111803060a050103050d03050903090a090c030f1109060d0f140405100c050405010f0905090a09060513050a120309051f05161b0305 73
    0x2a104014503900401034080c12003268052040d4105411905942c2089046040341130782c0207203481f6000340342e4034040b0020b010007082c0740406e41d280d404192401000078010030300302404000140000d00810181490850054801e0f018640380000410102d140400d1000d440101c920700071500744c4aa07051103146008100444d94019036005000611040c5584050850a4a0f480500c060601c250307280c8103c40c5546441c00038282c0402c003d01c0c461400d94024042d104c01c0c8840001c40c10020300081041314500c007035541e080b6150030148804c2c00300c20008265009200d94060140c8014410006c0250186120381030500c0a01e0240c1d41009014446020143c80050404009032034024280c0000c0c040520090b59200d14080c0840c901d440d83d00301100c0e0041d04680208101d43d0f403650758150000d40c0b425558101b50f03a940b1281c3c00200b0a11610400741041c1c0e0210342c4140e988000c03501290009411001481c00b141c04442c2110b0300030500c0c0724040812050036503904800d0070103807001e200300300d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 690156663 1250 690155413 690155437
    0xc0312041a010605030106031802090109150e0406291f02030705060f06010f02120702091003050105010303081501081303080a0f020c070611070e1303110109031e0c08030a11 76
    0x40c0000c00c3c05039024015504840c0b0540c1c05000d150760910800401c1095650040c0d0800c45441c0180000030540d00802120701c4550030728018540d980240e034450b03001c2503030704507649504c03400800c131a500d000c45918206154074008402074014180052500c403e1101c144800d81c82c0c0039850000e9500910a882003e60000241c1d0701078a0300741c40301e1010760001c072203a41c007082d41003680304030341c510004080070f2190002c0c03001c915101990302003181d01503004002620380024028080000f680038012240214400d48944009080c81e94072030090241c104c0440e0304021f0100104030702100b455502c14209605401c100c201c1c0d441e240308100107090364090508050380001074541070150001484801c0791072a5648200d40326400211320b0300d0301100e00c01d038200100c0c00b5003c5002d007031503640ca00c40c3c0a4801d04001c0c552202018402c2c0c00e484d03021100b83c011404c40104400d018803001510000d01d03041c0d01d0507401e0038105668480e081d000107001500ca482ea90441580015944c40445540e100d1003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 690157913 1250 690156663 690156713
    0x203010c020d021c1407051e0a0b0c070203151005030a0b090610230303040e0708040606050604230d02030618192f12030405040b03030c031204 63
    0x1a010180d5a0014203421900520400c1d03080d440200040440c2c11613110180d94111100c400041d01170b100703070850f000c1903819001c3c2010310001c08a0180c0c1200c0c0c0454490041c240918240c1841300a0b00e00c001c01000002600304443c600507640441c0c0006c1b4500302c07a1408440351211261561440102e0b0401d54140c45040907000510605100d40c5204500c18400c540555a83c50420142c0402c070b44140d160080e0010302e807103680004ea40c400386041a0180480b4103141d0b0303c00c071400242005a94890208003031406010600c81503000352409401e095030210701e0a071500320042c864003403c00d290800c1c440c1c0914013030001da131040b000c9a640f44c0c00908940c82800c00c9142d15104904c40c065980c198420580107d29030304500c2c150f88026034000400d92124500260740c0c4003c4064029440714007103810400f084c2e955901c020080d000a081c4004580319030070407090000701e03014000c0c01e91081d4414412940c03544000800c03500d01c80c42007940c0300350645503403400400240c0f180045031504614 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 690159163 1250 690157913 690157931
    0x160b090126011214010917030a090b13032c121014090f060c09121e0c01450b0c03030403080c0a02150c1608030103060b0a081513020301 60
    0x10f9000542254040c48403407514481c1c2d10809804c90b10380c010010100d0301d04d09164240c2d501e0071409583e00c02c0500c0004a80e0001554604010308011544505116503845030340050540c42891000c80e00c105806041c00c41c2c515600c0c2440c070300103600303030103100e0200c03035101c40d000240c244038011462080c3c1c0014000703541d801d000203403a00e40c1225048010301c940340800000f110002012401000c542c11820315080680040c044900343c031001c041e12900ca410303101d14546901044945040d01c0844c0905048101a80011f1902818042c000904500c010700e0361740e4245200c24419040054940120305881000d400036591180c55000740310100d03000c107451a5020f00440110310079803080d034a10019540b035a0394181030303010310843c00c070050384a01226202402c10841141d08012401207003070400d005080e80c1540700345100310440b40d4401c080010010040240103500c1c12b80c1040324008202030400f0201d41e9590000c000c1110303800d84500205d50cc0070300f07090300c0c07142041d0050024455002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 690160413 1250 690159163 690159179
    0x40f090b040605060a0608061e030d0c03080a06180e210301030c050402190810120501021314012c04060e160509030a0b041a18160b09012601 62
    0x8903029186a403c1400082c424505802d0400646009458440450703d80005210380c000d12611318408a041103a2005801c0d5130421107109101c0341070341c03400ca03590001e14004009444c05842e4440c2c603401c0c12000c1c86170191301c030310302c070045941a02d0010700301e002c0600e540d10304207800680408040701c5080c0507200c0300c41c500045041c2d82c000d140080c001c0d69500107000c200d204001c0f010961001200b40b820b803051181840e15045801c6040100301300d903c41e00c031410001c228410456550b075001450039500b442860000c4001e03c59505007003070181c0d030b100010b008850300036100d454500f01125402019207034a405c2c03180300724014008205054903419407070701c040b0065429a24621581c1c03407400c0300600c22002c403440c01c5005005062184584e075140515104003920445140241e000c2c20710340191182c0000b0b100d01e050a44400d402848459214103208245c032045500c0d101075102401b24010300d0b030866092640070718000f00794480318458042c3d0300c9180b121800d6045045070001500340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 690161663 1250 690160413 690160433
    0x10219090f060207051804170c030c0609160e0a0e070303030b0f3a05010903080717061e04020d0f06090c0509100503042103060e0a02071709040f09 65
    0x500c0d2580c50004082e1205016640c40040c0d1080c1a44000039440e0810060080403180350424880c29004a003400c0d00e06c0081091340000c4106980360348041000d11140d6010003070030b50014409005402e9402801030014401c140c0790003142045d102c101c002c203104002541c86203071002c1c1128195442c0a03185e24004001d80344003c0f48502c40d0750210f04006213490104c2030021010910781030b040d0780c0b000000446800e10200003000100c151170340c0c0c1c2003010038800c3c021808030f9482543c81c008580380000d00580524410114031145504100400401c0d440d0020b8001c03040303509906052a000030000010040d110b24800d15a640d41464461003039640280c00c00804e03150800d80a00401091441c1255280250300395250311503180c04204079081d000741c0003180c005024031400440001c0d1008104d202080e0940d283c0c001a581d52070401030700c3c0160800d15001540c80500391700d080740319101d030800d05515255a40c00310000050003800da80d9158441c0008004220041c090a503150406180213 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 690162913 1250 690161663 690161669
    0x305070c0c0308030601140c06041509020301050a091707081c0b19090c0e030718061d0103030e0f01020604060e03040f09060906060203040503060c07061d0a0302010f051005090901021909 82
    0x7c034007840b049090541030041500c00c1900e1074401448950b4403a02d80090300743c210701d01300c0f400c540c0e158440740240e2028050175104842c08500460001403615003016003079180b0b1912090368505020410002381c0f108201c030041a00000c0b540c50030400600440010440519030950107110840d43d0340c00344089490382030440300100340420808030784c400103442c1860b01c145a25415044981e09218480610140f842950050f00f400982c8179150384007855143d1a0f81c42040003440803100410805500036648118140c09403143c0c2c0080e044c4c00000703540c49034054401003001b030f01c61510300034030541001541c0050186d0f0b0059040c09544500c95402440c542c001ca40c402c40c14114046040f83c000000c9038101c0d0f0010f0002c00c0903541d41d540c1d0701c01729000710001300c0d0791641354000714200030101501080640b210101501e200b40681c038004e401c541030100d40c002c10306e0a040810013043c2120741418210390080d120b0300059034850072141d00a100b051080c005003c440d0301c0d200c40e5181d01c20741d41c0301a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 690164163 1250 690162913 690162917
    0x150a0c03050603060c091216300803060402070f12030f0b03070b071e06020f0904180506071202130602060f07020a05030a05070f0209150f09160305070c0c0308030601 73
    0x2a40b5040c0c2407503214030f411a16844105400c210804450402081e400c103120003800694114003d1200142602a9160301045551184650b20040c00040c640b1007103c81e500311003150403210b107980e80c0d8480c0340002004107204560100c4c5040910034580c4601804a40c403800c15002c220300c0040150081070507200e8115028035002401307409060004aa500f0303a01000c1f401c3c0d040c405543e5480d1201600003400c4a220150070050b03e00003006400640401d10240102a8903003e01ca0184401c0301c4002c0d4100d07a00c18a0078041001140c0003190300b6070821042d281484031030f000091034001030320032280c40002614100e44001441c5034080350843c050f1808411141d25170f100c4107012a5a04c000b40809401a0020400310360b4003401707803005064940c441c080341316044001d81c002a14048080303c03145e030342c050001002070300c51900600c030480410088403251001d0030b05179407030000746c95407600e500189035950300860b118a0041205042072540603101001088d142d02c0c209007503410035190180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 690165413 1250 690164163 690164171
    0xa0c1703011d040b1303140715050903070c031b170a06060b030f070c020f0607240c0207090b0411030403050a1206050d030e041508070f081f02030405150a0c03 70
    0x3024070142c10714000c940115000b240c6171a508016107810301c5601d0104c0900843c2200001740103c044041d040c511b0280381305000c1c541128075601d007a283c0c01800b42e80303a604100107880004284012840540341c0026102d0300388040400c4070590141e042c0c018072101009006c691041e034400017001045e00d480b0301c1c2d00f4000d9542c1c2c1c419509990005640b44441a4203120004550500c505000050b4500060502041c1c85420300450318503803013280c0a40e070901d1309103000040446c2c66104a50b207540101c0041158007019103000b9100e074018003544180c6070b12039412070200e64944e006901c1240d4008845a501d00301480c0252041e4045a1180040b561038109010100f05a114001c11110054000959000a590200c1c0c0200e14028201d0703219a48002c0141160304c0d241581000c1e105020040601c1401c003c400312003804641e10a110030ba00441008008460110715140d940c0031940c1b0140e2a07440701e1500320f04054005002070403080d1040b04110380492590409158120703d610204 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 690166663 1250 690165413 690165449
    0x20409060801060317031e060102071d180c0d0b060d0507150e0d0206120a0e03042705070f12090b100311040b030c10021603050607110312010b0a0c170301 68
    0x94881c2c0070403140c01c51030400f00c1414481f5403101c4124607902500501c19104207a40f503200760880d01d0440411b1903000c003054802c100420880480591841603840d0060400c080680d002606041c0c02c1580108061025808114591100d50a01c42600d520500352050507864003031a80d5100c42615400f4002005418601518104503108107407041d000fa0099103080484800c5040910015140d0b0031f4456450800c59901e50007840608098081421003140b80103803404240071100c1000b1680640d21300e13010034806c1c02508007485408800039801d1016108403902c3c0b0600c001c00e0350b540090000d01400e000c000d10a0f16405071101900e206042e070700301c0b058071801407104460300d8400040e013551002e8803640d0f207840c140303c000c181c00c07241d44110384030401d110b540d10170b0000d203c3c2e1003110725070f00c003c082c4007040d60000402034860b03040c3c400440c104900b80b004019410418805c00c00b0700f107000078402c50443d100f140c2846180c0c1e01b2158401d80195643c2007454240e10034441c107004038601c0b601c02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 690167913 1250 690166663 690166703
    0x40b010609080a080708070b01080f520303020105100b070f17090a03060603050609030c1504080d1407030e0705010c0602090414010e04020a062a060204090608010603 73
    0x80103840c100703801044204004d81d40c504041e031082c1420b071900d003000d01208000804100303613140a0120103018004600c0d10704041441e0941d5108035050000009280025084050703890001c0000d00c05c2c130100004d400710841c444204080080d402349019210800b2050540542205024501424071001c00540d41e1800740d001380254900201a17045111101002c101003410700748003051242213980c94081040c0003d007840b200342d40101c0361035895103801c1003444814000c0c503a1041040e0091454240c03000d44560300c500c0008244c008030700391040420144074100717081e10781c2e245803000700300321081c82c2c40c0c1000c40390b0034200c6c2c0d04030000b8280b140528421002003001001c480e010703107941c0c0c20222107a81e60406500701108181c0c22583e680154603000b0340b00d402490081842d45540010f5080c82c4c01404000c070940e411880c00d11a44002c044032078403100c500701000160983d0f112000d0001031034000040d102d941d108a1081d418214003146d002c60661248040328411000f141900003d0010303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 690169163 1250 690167913 690167927
    0x303041b0e070c060b120d020708060a0204030c06030c0e0402071103330402040b03010204180e030a050712020c1e0a1401022119030516030902100e04060b0a020303040b0106 76
    0x854000200c006410b42c1c00034404d50880005454000c000186440140d03191364a455078101c4800e006074040c00c070401804005000741d079041a0003040a42c6440c3c21910b40b5150611244140c40805654100c01c0104170303c00c40c1e0300c100d440401001550740c3c2e00c0608240034443e1040740502e01c640034a01d104000c0c555100c212aa08400c001c410f245291064100c00042100080c420303a08075443c0c034040c4a45513030030320041c0007a0200c410343c14280081d82c4000c074100e07522014074000680c01041003131a80703504002a54800c60307101050040340d82071f01c04101c0c00d202d040001c05400801d0700302c0343e2a88040745510f401c8271000a4402c255503940c6c071b401c0100f1002002c175085002d604880c10881103c0241007103c0451030440c0502d83c80d000207500c907c1c40070407903642140c001a0341c800c140314030040c020443c86800301d01880c0501400104e07030005a088060946000300b0b000d44d40310300c0460b0380c513150059001401401d900d0f40c2c4507122075101075105d80c000c4a08445140c842000814124085c2d50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 690170413 1250 690169163 690169171
    0x30f02011a0d02010212030106080115090503060103061e1b02010c0302120103030e121203060a05060304050c0906040905011805010b190b031005030319020d030603021503040609050303041b0e 84
    0x110741040481c108060120210300c80030143d045000345400d0917000407240d0011802030204e591241d81c9036242c0004d4152032010011044104404035001b0002c03660001107050540c0d4009100003040d1010104444000807801d0240e00e41c2400c041c441c000010704420b014081100366002482130568032030045040748690710b0084109003001c001800800e1041440110140c8080c03d03c0351840b0302201c0f44c0f4500500b8000720842550300004201090603c0080070f80200402e4034400e0071420300c0d560345a143c01c14404224092643c0380000b83c1d454ac2c6e59041800d08540000c000c20420340700320f904031880b540d407070019603007503081502c14410317810000308640c04800e248841d00c44040c1040d00340e025030b0b440036000e4280103a000b0800302c0e0700d0340c0610044c030941241048c2080030380980340029040c07200c001c901c2c105043c54803804002503100c071203040c8100f90207010001c0d52641c5034a403d000a090510016080740300200c01c02080041d400c48240e1800794020b44140c00e40c1d07a44442c001303000001c40d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 690171663 1250 690170413 690170441
    0x7060507170d0902130603202202090303130f05010c05060a0e01110a030501140603010e01171006060e030601091b0507080412030c050f280203120d2711090703060b04090504030f0201 80
    0x41c0c440c40350809000c00b040c140022790f405c0903190003510720000c1d10b1038210a0328402c0d041c180010800c4103402005010000308402e003088a8a407200b80c540c44d444440040c040c0011544500c4a071010320000c0d8000d5800c003080520845d15003030080c1d4000c000309024010b0050302c9030320480e185824600002568100da01002150341268200f030480c400f1108a50444080c42c8113000c005815070318240039602c040c00d02c03540e44007142174828040614002041c1c0c4040310705440c0c00107040c10740d00c194928440084c0c6a0908550398141464009514403ea0740045080d130f451905410406a0022a04091794060011608401404444940c85506000803000710716583d80c0300d01c1c1504000c0302040030460000301a0303007120406680854107903000d040f20b5011a0b0307031602c2e4600c1d0341304035441d540405281d11800c804a05055036034903a014a900101038403800e01c0301c0000d0500c0d0312079000301c0c0142a1070010142ca59039030b5184032000d07002c241c5046021a12031000040c81a10502c01c01010403a01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 690172913 1250 690171663 690171679
    0x31618050d08070c120f02210d050708120702030310082802030309181801060803030a3621080f0702010b1801060207060507170d090213060320 63
    0x1a68800304a503110304011210245880030014428145c07071591240103005484628450a00d4810441c0c0054980401540401034032007500d0051000640c05107d00140e042483d50b5296508010304240210100020310926801c20020843d42c084080c40c022071040070101c01c0e00b611821a87d0b200c0350100015224011155943c00301c01c500b91900800075400901038030f103006108000703c1c10460b22030f000103011050840c00e00ca0400e20700c4007038409601c61900204107aa040281450301c03032101400b15281c00e51285c02d4a90304e640080629012418038a2450313024a100680340d48080354144000d40d140740a089410514804558103101400d18075079903405940e8680600c4544204042e104004640d42c4080300c99076a00c455603000d08079108043d607221158582500280391401c01e0308800100031003400030100242d00c55043e0103202001032052a1220f0780e5283c5440144803611b80a903000042d0b0042204202c45a0b01100680c0d010f804000140600380d1000c0240340302c0c8203003540e040001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 690174163 1250 690172913 690172939
    0x1406060105190807031103041b051c02190509040c0e0c0408101104080d2003340213020a0801080105060f09130b0f0925090c0903050303161805 63
    0x2240c0f400c00d40c03008503410700090280020b0b0400b801340e001207900f00c5044100c10708181c200a10111040024801210098982103c404c08441340d2040070100038010403000d26600000707014205402d000e00006800c140301443e260408804a40311841200610b403846008240000101c904885c01e446421004081084126034040020510b4035015440400140004101c0101c18041110310280c280c1d03403409074072040922001c0001061401080681c0b04220181d40301d0401425444000d40d0765071060100c00d0170503c0c041e4440c0c00c8007002980301003440388220030b0360125805810520801d95030409140c0e00d540c101422a40c0c140c1c3c5050b800059500303214035502d41080100d03840b03c0650180042070f8916a240070704402c003500c0e00c0010b8039400c41000128007041200852003806d003011050914040c0062070101d00340e50040070586900c882e072800c05640580d4040d002143d01200310b035680d191070035030034100c4a00d49640c000003c4e428002c4045c0703480c903070582e0703000c0e954002c282607134140c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 690175413 1250 690174163 690174167
    0x14070b0c0703031b261303080c190305090115060210020f1b01200304030512070e130e010c0903151e0e06150d0506060103180b04140606010519 63
    0x3100c6030031801c064941010207096242819140124400d9450301d80d1590152000208864400e071019054001740d00304000e10b0711a0400602202074150030191102e403a203401032940c5200e6447c2c00d5100b28003a24029400f2503055000610030411030b8001c01407034028040049c4210082c0c8207080c010f038880c101da40054890b41d4001d204035013242c5e040900d000c140f50400314007104c1c201d80d92085a5941c412103000c55440388038501d100112240e50034070314a4a658044d2690103502480e0a107480540000b410040c05460070416559000701213044019680f200c1c2c4019007c10031a407185942008090b0790100c4c0151800d4069a6100ca200d01d18541540807520082c00c1503124880611511490418001d500f48102d081009407400030341041c2c0b80840e11040c114003820000781c0111915059080400c40100744242c12040900e00441c8102a012901e00c04d428200005003940391010140001c000d280c0a104038070501d03e005440c800e664038801076515000e000384c074040800c0359400c0890414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 690176663 1250 690175413 690175417
    0x21201021207050f040504150e0108030f03070e180f01030c09020f09060c010b1215010b0f07060c02100e03030603060906040503030a0902060d0509160915121a1614070b0c 75
    0x1e080e1307150b403c180e0307114005015150102401308001480d51070070310540600c62a424090300e0510000c0d4541510308901024620008014404000c41c052034208079940f1400745c0520740c6114840e40e0030030f0506085d60020501d0a12089a11849010380082c00003500d0080d6035113207824000f00390418075a9010320032a60b0106849100c01c0d561850164075a6555920360812084070f0801803410100ba010043c101c0003040c1c00c2072a440f141840003100b0b10121404075030740e0305c2c1d11240204118103075840c00ea00d130a01c2d9441d1580494149200402034990000c00b66201e00021030480b01141c0b030798884207480c1d034020b9030302410a800403c0010604131490b00540c006904c041c1196151868034501c2d40216602a198280079411080c106c110f8140c9800c02c0c0005000715646c2002079094112038000c4010891042c0162150001162803e010803843c06001180d115070060300c0d01d203042c240e480025108a00b10a01003625004070f11400200304054510043c0e0225201d461502d420300500019 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 690177913 1250 690176663 690176677
    0x305070203010f0c0503070e0a030c0501050c070e090a032c06030907150305090d0f020709200703050a140304021518030d0f1215090b12030a0c02120102120705 70
    0x541d2180000c1010000c3c611590000d10565a6425164201118002c00081146072414498840b0400c1070000c182d01650170403c90300d00b401c0039175583d8440c442e40c07414501c846d40710200c841c0c074000820602100c0440c8104d8400e2080c0c0e030b0503000845041403045030100400300181c1146003000c42d074030a82004402150040d44c03000881d40d80c01e54482d48603042c3d0100c134801c00001f80d161002e010001c041089070344105011810300c0704001c440b420340250b8540300d0303204032030303485849541c4a00c440c8204843e05022420f600c0305c46e50303103440b1818054010350000c1e40320800582040c4440489030714100969014076230003000819602c6994a881125030406440a6226880c00304100781a5604200c20030040040713848050142e1300e503440260031070369421300690110342840c03a0407244228245480c006c0c0e03911083d000600d80307030300c0f0f001c100000d2a03004140482d1000042c0c5510042e0029050744590380300300c2c4c08415040885807403070b080c0e0050300071003a11840040007045229015a0140441e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 690179163 1250 690177913 690177919
    0x2160f030623190e061509060d0804091d03030709140105040e15211c1b0b010e0a020702090402130f060608010311031507212903060601050703050702 66
    0x303040ca2081c0841c10401603402070303006035010280910151040c01340d0003042840402070201e80c64100c482040039420000034a01c43c7d0240c4002658546c0c0d001c482045298110041503160350300d83d01c10b800107045910185001c15881d000403002c00c20000120b038403400056880502c1c841c50440c07080c808807614221941880340c18803010541d003000b602e540384a80c049107021110f01c500032040c00b4039407542c5600d49110300e0650365001040b420000e101d419900004040ea5a004140d070012110910003100f2034225142840005003403104c020746250588055012082446d11401801000c912801c1c0c0d0094201d102200018090300d8040d0b2105446200f0801c00724101da00c001c0310748120703411500180c0100f200000140240a54040b80180b0030100368024625500043d034400407840f001011901041000820603020003061200d55800546007441489004c808811401400414941e0708400c8503140301405403c3c46e0005003240a00c5c810707141d191914115417002c80d0f40764003052059070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 690180413 1250 690179163 690179201
    0xf011e020a0e0616020a0503030a09120501022b05010e19021303140a0b0604060305120d141608060a2907050a06060303090f1401110f0a0c0602160f0306 67
    0x10480c0c0f2076100400101a05401144115820f0310401c02c048205412813406940701f800f0000710540c0042512080d102d19019180c101c404610f0700b18068424a80190802e100741da00c00d10b10702c043d00b03c56018804007800309124a85c0c882c05030380340f60390045070b035580481502200100034500643c02001283c0001c110308443c0c6480c1d80320881131140d0421413450703035444481c80c00d00344070400101039007145007210240300d05850342e1a070303980c0d8418248135015041d40000380d81088003210380c060030149200c0045030b001480c0201110a10b0020100c00d03801040e86180000d215140420701c1c14140e807513040400d00c084000144040210081a542441e1020f0411101022400811001480701c5c030900703010507042c0c02c40ca801031940c0c100b940f226914880c7d0100c28450701c2141806510a483e0070720b8641000d078203018100f403902880c6510710b031484c002c0605d45070900452030400c0083c0c400a408607046450343c0d40810880251500c648555036001c1e80050001a0064011486201c20b65024032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 690181663 1250 690180413 690180437
    0x10091208090f15070e0321030916090b01030e030a0206070f0c0f0c050f0a08070b030402010507060c030b0301051503120a030e0601060f14070b070c0c260f011e020a 72
    0x40c2c504041d6650088808a10b43e0070005100e0303100c191603818000540c0900180d103205100550000c40209a10040d100d011000881b01e280c1041000da04140700f003140301d0740b541c0d207181c000014041441c0c0c850000e818213801e800c11307110001c00c40324003001c10f60085c19250380e841003c071181e0110a48090030402d0080400010a203111648004130340540f036110318151a000c10401c444050201c1d143c001d6101c100c0410100a021411404841c02c100841d42d690f82d0b50b100482d00c500c1103a100074039441c41c12842940d01c941c198403089210030280e008000300c0d121591808100e48080c54100c3e41039026181d1001c6c481c0c0300d800038103080c0001d814040750648000005070b041c518241c200c030380095000c0d581c0600c1c06601c417038101c00c94500e4400640c5000041c1d1140403010b8802403c40d030901503e81c0e501c008100b59480e408000b04500801082111050882c501180c01880ca800c06180b1031203c40c0c050301e007018820030100d00030900c0082c400f428051010006504651001c1040c4001c0300311351 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 690182913 1250 690181663 690181693
    0x60609130618020c0d08130b09010221040b0c2a0c091614070320070902040f09060b04050d03080a0f05070c0201031a01050a0c06090501090809031009120809 69
    0x7a0405030710030341000d604c68194400240c03804525551400c02c100c80c100900a50f41c9207001110b86883d00007881700d0342a60b56404407400781c800c1c1d41c8566110041c1da08032440c07030700c000075616004500c604030030320598072185180c848600545501c6480b00944903800c540d030b450007142c0c5000106010095440f1460004005104400105d64081451104115114889500c500902c02010301101c0042c140140d68500402d00002c0d81401c291740d4011381144100c41c0b004100280062045200941d81e0702c0d1100d202408460141c45020f01550030300e40c0120b50a40c01a040d54181d4401030404040b200e46500c048030314441c040c2151210740c0d6144d4456840b12a60f01400340304001e592184403591601d440010101e50100920090440e1009291172090707078170404071200b5911520b40140100510705100c80280b100c070724014441d610385001c080411181340003a103a02d000440544403050480402d81c0190b40e00c10b0401818102401c20450103a4080c6d0314181d00700358a04100c41c4d43c0b680f20055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 690184163 1250 690182913 690182939
    0x50c0901031202070e0c0711011b080a11010605030d03200c0718090308062101151412030703051303080a0c11010e03060f0403050903030a0c0203150606091306 70
    0x69820002d0401038094064040052000510f4040400c820304c1c9440010b0106a0140b56001880c0e1801c6c0010510350341c0c8190000b980c00380ca07460024088030039034a003000c0154030404200001c0340d00d500d0080740c0101c0610a0404885010340940590601e60344210003d001001881c061034200c404031003103008950740a04444000c043c0142001c0781001c000c51400c032504d103074000b14542054244000244d2220303502e03800550130340f1101e040030400400001c164076480801c2034a50310f8202c91540c00b400162180c0110384e40f540c401040040038005104806042154049940c0c1c01005614002440348006084800004046d41d202039101c1c1d580c3e038041d81c45040090300050440500105201075083c0309880d03a00c0900302807510991a00203e5103803140100980000c1b94540300060a2500410460b4402034000741520781c3c805a6050141c818640882c060b400381c8603e105400d001d07055580035902524009103183c0c1012801020003660a000c4080c080d003030798030b034500040c42d032060b813503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 690185413 1250 690184163 690184169
    0x13020903031c020d06090501081504150f051504021e03090a02090903120a0c0e0118092301060219060b04200702090a0203040f0f050c06040e010816060e0d050c0901 72
    0x24090398035440ea01c8040f0645d16190481c907440e0340b034080100040800040e8103104401c503c04003410b269143d0501ca81060100108480154184124000403e1540e8001c0d441441c5400000b60000100d03010301c012802002d002c03140342d050800c1e540c054084820040d581c010318030001c407148408681c2c0444c1e040381c0240c4496029900c00314050102103000312580d5440b5901000801000400840080c0070028440c81a8140442d1031142140c0c0041e00203008041c0c101040c040c08580071020090045014070304e401414a65070034000310310248003041c4922546480303100c484001c161a00c401d40142071a480c8641d0140d0b0742d41d44214001c0b50034000d840d28008c0c84c45950744404082c01807003941c83c80105a08030b02c0c3d10400070400069842c4055503401c036008501175180035950f1805a142491000300c0d03990040d008100000c0c0c840540107000d050320341180585400c4d14514010101409541c0103500c04035402d0700c1409400d0600c1200c488125014008489980400030301042c1280800c3e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 690186663 1250 690185413 690185467
    0x160e120c10030b030c031b01030209040204030f141605010906050a0c14060901060e0c0708070503040b0304081305100c0615050915040b1c080a120c02060a0b0f1302090303 75
    0x40400f040c601e020300981540325026800380c031102541950f054410900c40600505065011031100d10303986a075419030300659842000307820200c01c5806d1110072101c1c1e1030114003141c8507c55000606601000d00c003001c0700e8040e100c2803055030900301c054809800c407a051000b0080300070050b10102e0030210003000100d4585015041d1070900760a02030a4610b0b030740100d243c0d08001c1d0f05000111902108a450440e0088282600d400162902c1419485503622580002e00c02000b8041808013400003054040c5011030340100741c80c2d0f290b042c03001000d40b0740e03102c5000c98039140d6098041002600f00d2241c1441c8500c084000d01d0b00e41000826070042550400c3c07819550000700704c1d1605041c4206028500d040f0b035440d80030b02651480c04200003001c030009003a400c01140c0804ea4030302032140440216aa07003014040b03103c0d4000c0096460008940180c0fa144c00e01c00810001d041210000c030500c0000f80a0b281d0640c0341c00301c0e000c041c1d88221021909403000b0410540c80d980c403500031a604072040c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 690187913 1250 690186663 690186671
    0x503190203040b1602010207030e0609040608070b09040f05060315151504150e090703020d02040f03142a06031b0c0a030801050405060607030e030705040f14160e120c1003 75
    0x9029130340b480101c1818090075684104044004649c00c40003022014108039201ea035a00103071008200901074a030b00c0740c0c805206421020801004100251140340c00c2a281040202c0d42e1101210941d881690090f4064000028414400c0140598280d001100c0c4144010b00d03428800071a0209120103904410b07144081014030400b82d1511440d20108110315000d1506000100000c008620241200061640c0000c4180c801d06141e01a5030007440d8124020904c59520300b84858000c03c943c0380241c0030b01030358a25240d0002841040b4540c10803240c8a070050100309428000c556101800e0a40e00010382d1902c26006904280200b141400d8500a400c0d091240d00e009400c100041e000ba5106500340300c00c21100f034880300c0686440c00c0d007620701040800303028400700c3d0078400603400c09600581012418001803a10f40c100e00710070758044440600355500c060f28041401240326040000400720404940246002044040b07855141010341e0031000c008000500308042803030000c008030f034032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 690189163 1250 690187913 690187921
    0x1803031806251b0c060917010507090b0c070909051c0804020603190f1a1c15110f1206100c0b18010b0d0b0a0c09150503190203040b 58
    0x5015070307070300044024402001012004108405802101002020081c52140c3d901c86100750300440c4924542181d00c0c151566110000284034540c5409421149040102c045a0540341441054031644090342c0c1d00b8211406d114203c252903002040c21143c511440783d010603464001c0c03042003100c034400c0b8020030072075030a4003250a4149000a4000034488140c0400002d6152002107070f40c8001001341203810f101d43d40701c01c0d40003442d68003c803240d01c900d414002c1c0001444003020300c0c04004129990200f0980c1c03c16110144115100000c0420104041c5805261103a42050f0b80b0901c142403d40d046c400d51043c0102d00ba0001842aa49000000c0078080d00f8200704006400c03507121482c1464020b9103d450301c0c2c050302c1000e03241003c4420b40244c0400200c10030350041051a1004114045070a01c504010103c680c040d105005100d181c1080c2c0f507004c174000c2c42c441e82110098240c01c0e0854000c10302c1607034a41c00041100341c0d070341c03022441d1190101040c80110312451090911b0301050070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 690190413 1250 690189163 690189211
    0x210905101d03030c040e0406020c0105090a05120f04091104081f060b0405210118030c150510090b060f190f02010b0d060b030c0a0308041703180108180303 68
    0x4400d00e6180003680040081c014076280b13000440d02170714801c038551002500d40345000b50083c41130812400640d480e00090101414011070929101802141110442d90110784004c26510501c2c0652200c170000f00004c102c0500550032030308142c200645101e042a070750710140c6013005080344c100820b00389011541d860710400b5100d1103002d000d40845039420241020049110080043d4a080c0304040182e40c0e680b00d54402d42140c07031740d503014801c0a0f40b400110318014001c1c01a9200440305044910740188403c501031280c18070500721010160b000c5450515010003d040c0d000300c458000700c0400134040c002e003168004124083c00c1411000000c83d852400130000310a9851010440e410803d0324074490782c0d03003908016015000700d8001400424400040c1ca400800e50140750010310520000007031140e0b01025208407506070701d80c50704810030b8000407a160f00c0707072282080340810f484550390010f500c5018101e90211026101101012007080d05a107140c2048504081042c86440340c02032400c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 690191663 1250 690190413 690190451
    0xd050718090207020904061a04061509090e06010e041704180506240a0302070b090d11060105031c18030b060f0405160e1503090a0c05090721090510 65
    0x1100c6801c08504088995001490000c0d01510280107503031a04040140c0742d61200310180c03c8100140f0400c0060394503449180107a00706483c0d0000b1460080e000210000d40d0b003d1401450107181c040c03c101e038246000003c0c6c084014100b0313101d580c284413545031076040807401000a00b40000c03c0703c903400c0c04090304400f07840005000c24007481c0c2400d820744410300c12040035401020201d14440d1a0180060100d00034015000068a201420010f020010303001041d03481c28a40b16644426000281c000200c1d582c071802e1142d103805038050140f0790964440c1702c0381150010a1131400300a6660501c482e042c07a10300c190030640b4140c08103400d2048602e0803c4000c038001e0025541400b45241c00640d1030040940344c030203c0c0a102d20034541c40c90300d42d1814001a100d2140f0504141c69040444c1c0850b903501000108031256181040040390910f000440c00f4407541d000e558907843c055001c4002d48140e8510081d05c0b13005a111303550075000070000d005101da5260740000000700503218124400c0340c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 690192913 1250 690191663 690191669
    0x2181806090606041a0a030809030c031b0a15050d05040201030603050a030305090f0d05040e06030c12030432150904060e09010b01030903140307120504030309050c03160e04080d050718 81
    0x80090000c6040709902d8560f0300004aa41107400c0c035271103210705008642460b12504206506026440e07002d140a005090410a0100203a48000440d0b403a59a218800c019040454000c5581444840841d0220350000c50f885841890b01080941d96507540c5031600fa1001000c0700441c0d1203204004420308208000059600d5070401058260709142c00036285106502034981e00c60b940400007141500c04103c0a01c0c0f03030f080540040d14030300b91803c42c561242c219005040d4511185452500035800b50001c451500c841d41c500c000113080c1c480c04018102c03100d000b0000404105200c41c520300e544500c5000020149c0122030807051034021901801c64410070302285c141132428204c0300100340c0c044051061440030440742682c0e9141c08009542c49105495500d50990415040204240d8550044990a48104200c0d83d50528020030984c82d048008800c00e03100b01000010800600405050764209003c3c9540307524180103503200030140c0d0700490b001c0010440c140c00b5803400c0d8207400242401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 690194163 1250 690192913 690192941
    0x40206160204110c0618070620070515040311040204060e0d02030a0b16030b12070e0702010207050d120f050108060a090201030209030a03080f0f1501030b060c01060f061404030218180609060604 85
    0x907d803c00c9000381c0992400d001458408100d100c40340d225080030025130f00600300040540054442d60781c1c421003da48640401c4a45009000310030780c041c100740c0250b07410b403025500ca000d07e090b251402c0c018600b02d10b05007a80c0c584618500d0802007442008d02038029039900c6083d008600648402505441848a15a000ea143d80404001140c408281c200c02e0352186242008a901d411000324064010702401030302c42c5c045d0702c50290800d5000210441d4001403007505120401c0844c1aa01c1112030904c00d0201c00c0d006640040c1100d109a844692038600c141001400d2280b8840030918098010300101c0202d002075080c881c400040d502601d91141c40f824540c5040c0c907002c48010310b009808042030b41410b03100c44c04460340ea41c450095652000d030340c80c0204500c03540c4440848004115104180124a00707010144003a0000030854042d00d80150280d001000002c0200c420254018a5514000100708032912403500a00c022805103c032000102001e0520f401080b00b11041c040680175 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 690195413 1250 690194163 690194173
    0x11b0921020303091c1205040e0106030b130b03032a0f060408120411180708070c030c0b0612070b18010518100210151d040206160204110c0618 63
    0x2006a030004115509130a0948140e03a1001501403000300344072442e24011712a00d4025540710030594084081c1c41240c0744443e1414140e43d0b961002d404a0790b070b92240700d4010096048480680b145038002c600092000382c101d0b4604000203051761b211100010026440b90480f490452915200300036141d0325258841c0070304243c2c02e1660b2040f00c1e40c822000100c501c141c1030320008040c4004000a100e201304041c01030a600d220710000f54110003004c407684004074425501207400d0b10300c03a0041000140d403644409140c10760700d4496000002c0c00802059020382a070503559012502408814014101d2911072912070001d0443e003400201180d00d124100401801040b000d40945610401901400d8a803004017020521049042505280b1088996410701c0398844030000c166600d5021100940050b4008400421441c403414030155006035001509124403040c401296540e4450302d4401003001074040e40c028000035180d00080c0710305c50544c00140802442d42c0e25240209081140007018007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 690196663 1250 690195413 690195479
    0x4030f060b0f22020f0d0b0a170d0503061504030b010f120210050721020d180f0e1005030106060f170402010f120f11070302071403060402040e011b09 66
    0xc08085001c04402a100f40d0783c078a86003411500c0c0c0c1103551324110301e61000c0e610709401281074040d01e990140700340150b4410500290f44055590030810710740512005d003e002040c400c044840707402c060542d540c4287c0ba1880034441a80341001000154030034810518550301d41000c55420142ca540300c51801032a25042c800169a0030000214040031424000d4840e1028100306a1480341c4041d40c01d10942c1009418108030f070001103004150246684076101e0150720140f0300340b121150300c600165000c050106100890004581031351203105002d02d06d5080c0d1707a6400081c00c0d02c00b25440a03000c80c1c03420741d1103841e00ba8844d20040102400303401e80211805c2aa0000b800110380304e5a510801034684500c904101c0c4642100c00500d21082d010b0159115400880d196688105030071400343c80743c0b007000036110300101100176031500024050021542c86800388800b070000450603402075584e0784024410341000c1d002c5055413108954031007240305d040c080000c200e1481c0b140d0500302003481340880 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 690197913 1250 690196663 690196669
    0x70b09010e09040510050a0f18150e030705010507051209010c0e101b06020a3513050102031006030b2d1503070e0a050f0108060103150b04030f060b0f 66
    0xa00100305040c1c03019a69595242000e17420207160440305141030381014280714101d00d49411040c0c0390301582104000d03801592009072305c40d551190b0001c0c011450100400810082540540001e080c3c10b02900c3c0340500a6403041e08555084944102080d00031403520030038100e21603040d9100620b00000c02c007428500798041c052005c0ca0310494441d510420700024a10311a0b000c040310f4034041e10304003101001b60702d84030010790001c0c02150006031030f65201030080c48114021440da0346400e10361400d001c00d603010101036400000c1400e613014107132215180000c0c0092005500c104888001c401c3c025091082c0101551224101e07644144840d00c055001400c0b59215014203000d206a11035000307d2810114000030848150301480ca203000c010408510b4203d610250941c0e000c44d540005a0784540810031161103000078140040c07084400507140c0e500907449a50100090441c1c03009070755613221200c00316442a002107a0040d04007041e40100840c0340074900303458400b21407800c0c40300088404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 690199163 1250 690197913 690197927
    0x6051c1101030f0f0b1306150804020f060705060402210d05160602070302060a151409060307030b070e15120402060a110d050c1b030c060d18050a05070b0901 69
    0x2030403240a040814100da03000382d00c003020300c0901c0d45060101001c0340380e13000000c000c10107041d800b038036586c410440c416400b4418001070320743c00e038004640c0201d4a10212580314004104a800c000740d0f6400308000d03a15100544543d512400c0102124030b032501c103206208180594542001c02903c281c00c024210216500c507005480340340c56a12400441c02c00388408001b1040500340320f10004100c400c0c90b41c0400c1d03d500c21140c0c0c0b5814070400300c11240c0f500030301101e0b10502410280d030742e201c49064604031150135085100103003110000c0b83c4a13101d40e00c2c074190595158002c98002e14008510b401d01502c4020342c2c044c8408001e007000c1001c5211220b0003802400284100800038400c01124043c1030a1b410f512401c0003251580400341a02500d145d202c240d0070703502c9101e041c251584119041c54018103022024014200f1250381600b40640307500410511807800307880d01a46e0181c0803800380c901e68028052002080c0544940c14040e08141468100e010107140800541c9013990b0400c070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 690200413 1250 690199163 690199219
    0xc0c0209060409020d02060d0c021b01020309060d0b030709050a0c02240c070b010608151c0803090f010906090c0501020703032f0d03090b060103182909010204090605 73
    0x10b03000c03d00110500c00a180c041c2a130b64003e61102001c2080501d040003688601c039100f28640032a64141d83c00f109120f074010344441a140140d00c00c110615150511f8005000c0107074684202082c2081070000280c10101d10790000071010b6a1101005040e0901e80203c00a4901e0380c0060011420400c3d00c1c041c92034149202012014484804034a60f81071000c100d4603c181c007d4035000155131202070003040c2034410740701c0d60000043c00c2c00011041c40d00f20741c3c002120800908200240b46240e03522501604002c195036158060780d140f150081c1401c0c01800103003480f0724400540804549400d10904400390041411540f02850900c00250480c00f0f01c10744034a0541011003002164503811108804000500a18010065403ca80c0d94042d049591928030440c40000742e561950011000c40301c038034402290000c10814800c0c08581040420034418000101c445031041c01441900c08401d01900c001c0110780d400074080008015911496028281c200c0e05090b04104409100704088040c40c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 690201663 1250 690200413 690200419
    0x121109090a11161b06110c0409060b0d05100e01020306031e07050a17060703050601050a0c050a06021204142b021f020a02010f0e0a1e0c090b040c0c020906 68
    0x20320405060120006540e0144640b94109105000da86400c41d14201d00c07450031130321200c4d0002c01140403801a0084030341250000010b1000030f100c0b00411000e0410410140c4020750b4405250709180c452803d95501d00f4083c80041c000010a04116001c9031002c2071540c00360392040c010b01800395000304028141c882e40356440c2c0100745840c000c1c1824407801e907121a5000280300c100007200800701c90031010460380c1000b5104265036011003907040d40c100729071144c0015400c0211115a6014181c128107031130040040702c8004000383d95020882c0c1c00300300701074129403605082008200c0084428070720141c80b0302c09400c80349a45802e0039200f07000c0130107800414a000502c0841039100300f00b00c4402101d04603121560001885112009503c84901803006508000349108d806916010300119035800034014402198261505600356442e812f00b07506008504224601084031080300b10701408035a6800500031407035402304411140030004000078410400c3c041d50160340c410b80c5040c2e10038015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 690202913 1250 690201663 690201671
    0x82401051312061407020f060714040308041202190503150604090203100e1902150a051902160e0403080c03131703091203012d05060703121109090a 65
    0xc0c07050004040e01504803a000e000d81019080074003803e5001000780c00d0800081448a4030344140480e100c1d800341e8052429507200c43d001c2035840e803041c9458000003c00072415400d25031a640c42d08010340c007681c81450410401e500c6041545000340f00c3d541889141c2e000341c0052890003000c2a2a207403540f40d0758680f04c0c18000000c18a40f07680e0401c0320110750040980300a580114404001043c1001c6441114825524021b006a24038080d9410b101e4009042103400040500040d19503445840c802080000a10860500ca0415043c00b813800368660082c01e0700d500c5d24407125407111001e5024031869403486051001007031308042c070907804c41048030840c3c0c3c0d203a07146003000c00c0c03211030502c0c014000d16006024404064031200514000c42140d01a00d4000461401d085458007003030240211107668040c0341c0000014418030b02540c220040a4908802d540c0d000041e1260000081500403a030601c1644085644a00ca10640300c1080010103003000d07801c0c00407400f242401003103030010f07684e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 690204163 1250 690202913 690202927
    0x807030f0603021f08010801381c02150a051605070807030305090f0109241b030503040309050402030c0a03050c0f040b0d0e01113901060608240105 65
    0x20581181024640141c020741e42240c15403400040304c0d1041c900712000509083c00420580410700811294103007100310f10310030b005004584400c0c61441c04000c91404010b45010f01c260311007031103040030031140c01401c024200450060021300d03006011071030344c0b1507002c205440a054002c41942d10311003400b856035882c01c0a07890a40e1a04203650011503061058450003c10180c1c0200284207081e01581c411010054050041d540c2e09282e00800c1400f41004202018206100565030f05141003490600f1080701c03980c440c010302c0c0c80140d0003500040c000004200034107030440401d40003414107640451461a1a40141b401800745a084108041d00c034400318409091040590b40f80b10462f54072103a917295603014012003a80f003480102004c0c0d003840c650103110750313061007003410210070002d401d07103031103001e080080403c540d1506442d052407200c840d510400070000b8070011800815400050300303030b041070381c0580402c000606410350340821542c01241c030000d41c55060a01c0000303081080c0c070303005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 690205413 1250 690204163 690204191
    0x3030c0f0c081b011b0210050304060f022a07150518030f010204031506140f01020f0f1605030f070e0c07060c0c0317130210030e01050a09020108070f080703 69
    0x41540c2c8400070a20600c0440c400e04076450801803500c5800741c07030b4401c880400360450780c00592100d0000e0b51001c00c041c01c2c4031129000360002c40c1d115124010024139541c600000c0c2c0c04a0304281004881d69544161400c1c2400c400849001000b1010004201c4645000403100d140f1708004000d000b00305020580c4c4924998a00188803c0d510003020f40c0c0c0564450000e00e8004d40061109841d000c40c42590f60074044118441c0782c0c01e50f02007802d0700d0001c900c60b1007403185034125031807400e0452003119036a0750002c500740041c882c00c403501c130064001410044140300000c021500414483e0304014544028480300007034400845013800442e0b170107592426800c040c24090001d01801e20390070074001c109101c2e40088507060300f5101c2d0711103c596400c650010202400d00700c4021000507041800480945040442c5132400c910b02d203800300311a1850400307282915803d4032809501512411410115a00a0346003540f10b602840c0c40200c6008103a4003d00d130f82c030050710100078141c0e6005104804a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 690206663 1250 690205413 690205433
    0xc1209061608120c0313061e02031311011103030609070201090b010b07210c0209280e0c01210e151e0c040f0b0306130c0503070f080103030c0f 63
    0x5034210341c01c0d41800207a090401c015840f241d403000d01d01d2003860001d03005400742401e8034003503240d08914041901030f69640100070700294120844840001115114041c01400294419245407805500d400518a00f01050450381804181800600c00b0801c0c5000d0002040c0e0fa4003c10442d171404042d10740000517070060103203032030180c80c5020500000c240310f00440c00900c28188101c17103084124403d0300c4040d0321070b150082c1d202c0001e0407000c401405440c0602c00950049007500704a030700111001003450060b1800070711a0700054982c0480615298207001c100900013080c2403802a203102c8613082080d8a00c20860103618543d91420100200310402809024041d1828618014200b43c0429071122401050035000c4603151000600c0034510720041d901100c40481801094a00b0040089069000100076a40121801400b0b8840418501800e00c03112400d4685981c0ca003020100140f007100c400303007c0824000041c0041000039030010440b100c00307030000000900c942032440c200c10340f1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 690207913 1250 690206663 690206677
    0x2040b04060b0c1b0a150833040e06060f0d061107080301050f0307060203190e13021306170106050c01020705010f0b1215060405100f0e010f09020c120906 68
    0x205a003c2080410020002000c14401d0100c00300c4102e01c4409000300281d220241c000e000342c00d8929160150481d02685846411070856511082e510003030615400d400c414034800711405900b804200062800e0500c00c40003011b00e0710004d03002c10b203400408201c500c41081c4260340200701890f0224284421540034003042801d0901080d5520b80c98108881c0d01e030000c0c01517178481d401100140361300303280000f0010112146500614242000388500d040c03040c401c041c4135001d000041c107140901e69950000800424202e8030016190700f841d01d04103034000010342000341072111b03401e058090700440c4c004c1c2d68111805890a82d41c0c5414000903d07002e800707486801041036003000b0803c461014184c02150420a05881420503020f94070240342d41c0740c20144000214030030100210f616402c0c503800880d840022008401100303541ca4040d0303141c1500c20b174841c9104804000051242c01d0aa03c2c0703000041000100c15814030070b602000c151210200700d22250300990016405d0710175241e510a076440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 690209163 1250 690207913 690207929
    0x2702010c0f08070f02041b0c11010e150301030309080d02030d0207080d021c0b0d0812070e1921050c0f01140408070306110705060106080709031e110405060d02040b0406 74
    0x1640c0c0300f813410001242d03051804a2080d070802400d80c0391007007007480214400c6510b40e039014125032591034004c5801c107005516410044100040206a103601401151180740400103551700e61440c100145490b010350030041c141d42204038050000390f8000151500410040c0c00166542c20030b00c1d10342000d1095481d4004a02c1c008104150001c24030448485805100242841410350600410560b4851124014803403801403000701800304600000a601580600744400c03643c180c207002402402c0307031031101011034008842c00d001188040f402882c1800001e542d01c520704a450b542c03144c94202c01101d072402051020702603400d60388a85034a1607140071500e2240d42c0c80340c03980c031800d413110641d000548505090803c4202050303110402c440c80d094214016018030f03400c210781100c090901400c0d10b810003090410120200300340510312700046080d12032140c4c00302c42e03a14203655481e410704207030b83c071841c0b0b8942001840d03203918142c0c4180590480f00000c04144400009006150b60307005045 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 690210413 1250 690209163 690209167
    0x6070624080f100203070c11030a0f1401150b07031b06020d0b030705060f12091c0e01020d0f050d0c11011103040c140604090506030a242702010c0f08 66
    0x3040c54010070b07141e80002081065038446258410200141d10054502400007210f1508000108949109010024070010241c0300c48a21075146e001e0380c40d00e0303240c0543e01c3e80d89000113059508000d01c00c03010020700010754090558038000c00f580140c010030b0000340c18850b25041d1710070380c0807694214030961940003004544520401c0d1502c1c8c0200709003203145000e0720428901040350f10300102943c6085000fa82210f14021440d240b0901c98074010b001102584214103203c40004d04134501102c0d840210b6580d5410618400002803801903030607001701c01e0182d03142490700e2640c0d100d421940c154480080210b038050141008844902174030345090503e500e4080b040080d42c04076401980124010810102c1c51900d40e10450680038041050036071080e800c200070840401141c01850b0f00500040594045007040d403202080e00300240e050700841c1e0340454000c0c54040462044409000300030b1140c030745260310802d0255404251f40c002031305100166018004000c0b034904031002c043e500c207002c5a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 690211663 1250 690210413 690210419
    0x2030f0f1c0c080706230108010c08010e092508070810230402011815030902190303021209042729060d060f0e03120a060506070624 58
    0x41d00c40303400003249a40300031520000d81c40c40340300c0c01c0e42d8281c440e080840549002c1380c556800e001000014200643c40341c00b511240c0283c0c40748560700d0b00801600002003002103120300020f01c1900c0581012000038030b40303010700200c00c0c00001e480c1c08040c0c18045441420f9017083c00d01c0c82203c12648460000d11030140c0101e8106000301d103c410401e1032000520904010b10311012202e541121550610702411300003a016610a200c012210070880c8180700c1816211402c0c00100e0400f0080d01000ca500c0c1c00c420790440c01e014400a00181c050f0100001c11429560000d4a402d200100c0e03581c4280041011100d07580c440c0d100c849203c0c01c540082f03010400180707810702041c540803c1501c1a410480c00d60003103001e82c0e11203030010403124007086000e03a524000c002180c0e00018080c2e48940d0b442c00e2600c4560824441c01d0303641c0310818025521440e5035107001803844801000c40c0ba0740b0782080c1c0c0070080750f01d030b9000b1358001d59408500840c4c0840c602e2030341c40e0003507604841100404a414800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 690212913 1250 690211663 690211693
    0x3303030708090a0e160e0109052e05090307050906040b060a0f090e0f0105120a02040e030409110a21020d050c070b0a0c090510020f010213240206040b0402030f 70
    0x2d00b0500707829940401030075a5141325000d5034208550040e040c0c140f0b6074510070400d01c12030000460b000b05051a2800719210804144c280042e44014000d08541c43c5484084202c00c60800201071000d1602c80e18200203030380805d4030f0318010301c500ca0080e1140310200d070352565542c020412030350380034005c0c58449020060060049080c100c401c40030503400800070410741100710341280f041c3c0315045103800b00d0b442c3c0b00174020010b12616280c1900c0c084d200f42e030001603546010304442034a01a0045849504207920740003207650041165038541d40c00c0200c0e4940d0764201d8840b20b84050041441554050302000034130180c441c00000c14003581c903207001c000740d9038428000b03013034924080c2c65009210303902c0c040007104907204160300c0008600b0010007004a490318401c411002c030a0b03031040e44c03051000448242d0036604034821103a0a80c505590511940499080081143c3c0b02009a4041c035090400c020b92550310141024104100d014000390640d2800c0182ca05901081011200c04019038008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 690214163 1250 690212913 690212917
    0xd03170f1b0a0504060c050f0106030b100801140103030e120a05070612020c1b130608070302010324030b1308190f172422050106083303030708 63
    0x41040c0c0d0700060400081d0103030603064403011081d940301c1501d002d05104090b20821103000b01143c0500c0b40440c1a410200d003800703050002d41c850f1040440504210b5014007400304030b03801002280c0e00d00100c5490461002028904607601414860842c096440c0440c00c0401120b4000d20180700d0652848104040003825030100c685a0341d4907400342c854a19a0400c0e4810845c403001c05521408050110788544030384206103001c01050718040b01c0d00303030200209032922030b0700040681e00403d03002c00c199600741c09071800c000c070300030710344007070158003215003c120b410170301000c2c01c140100350010701c492103404041d41c0e21903000501c00e80c440700b00d82d51940d151404100254000381016030414026805901c3c0c0d500311542d0019444580c0c0d840f03071001103200446031084004420103005145182d15091341060795100041500b035420400301c080401a2001a440b48082003092402c0000f0500b4515181034840c0c0300e158039504000402d071070742c0049501c0360740c104c0d814080000c60310204904240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 690215413 1250 690214163 690214171
    0x2030d051207080114010815031912030509150601030207080309030901090821070206040e01030c0f0803030c090d0501060f060903020a0b0304032012040608040303150807050d03170f 80
    0x4501007041d540d18070100c03100c103402c0c818108031106007030030500700d0741c0288911035100b54003070f0b200e0040d040d8240c000380c54071100040c5010200c580410900c00d006094a20071000e0803d42418040f90038400203c1c0da4400c44421104040501c54010036800c1e8441d030112100d0540100d01c80340c4138284440250748a50205200e207000c01e80c40c0d81c0000b070005011407074481c0b03005000c1c641e440d4144d034aa07401e089940441400c81e44480c04100104001c0e19051106002e1401480741407007032801e1011548804010390031100043d4018800c1103400006071003142c041d4401901c0d00e01103407001d0f00d0f0250240000750007240b0207000c003140116005500c0380c0d01c081164002c681e400480355442a44148074442901c0c00f070001552200c210740725400c1340c6420500c00c1806e80855030032190386540020241c00c01c6d04001d0004058806000074194140075225404080001800c801d030300d0003d1a640d40e0b079280c400d240c01100c0ea01070500034180103c510404c200855442d101a600e06640e0040e0304074822a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 690216663 1250 690215413 690215437
    0x60a030515040912050d18030806010f08040209042a080309040f0207021c0f17070606090b1008090f0102030c21011202040f060305010218090105010e030a14030702030d05 75
    0x1081d089140900403441101c0d003000b04060100c907580c60807102a031011124556080c2c550070380c1103440403510900d10400707000380d41740400d07402d21400040440d090300c0880410851500d0030b10025039109040c240d00607501019000c181c100740c000014030b003000030009891046a2040004200002200401002c0011581000f9003103030b030300b44081240036201010750413140c8690340e45061843c441610030400e00403901000c0c16256a550005440d000d09a081842080030507007104000c81c50048030003810340e1340c0050005c49900782c0450081100070704460b00b00070703510001c141070030824022a00c0149035000250341e43d10300484c1d0604103900c00d01241400d9899a0f0448400f000d00e050018180c1f02d1140000c1c29024050702044060700030307844288049136541d040000050f40c00d100031700c0c19400310107400031304920440800c444008140c0c025414032541406100d2141d038040760798a07495034070507040702030005a414600c0ca03600604400a426114605440c1d0078260020050b2000240d44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 690217913 1250 690216663 690216691
    0x40507020d02250e0403110a0f11090f0411061306090513050907030f1e03030b041a0f040218091f0504230601121b0e031506011805060a0305 62
    0x2824010005150f40070502d455031404041400030144a08869070000d010780b034002031a0245400c114240a680c46040f40c0c2805089800e5041140e09101703100d03188812a4240d2142c60902a400c0301041c00034002403144080c600c202c8003a40d501c80070f0f03c0c0000c60420a4001158441c44041e1410100b40104c2d07101c2caa184100b02c0780607100380500f40c8a09144400303009194916a220340d072405240100701d6000c01e80f048040d505441d08030003014514040e075800b0868400150a100440d20480f840a8041030024160340160315180c00e00420300c8410b407801a42c83d540c03a205c0e070f1044e108403d1502d5001040c00c0a12804494600c5550801d085030940d2001c0f131582c40c030401040b20034041d40000d000000d03078003090410030014415640720348107050640d6088000c403082411951000540e080000e00055480b019541c001400d005880081e00108003513043c9030310142041c98001d00b200d04128442001c018948040120100206030261030b55455103c0140040c4c09030400300c683c140c0480038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 690219163 1250 690217913 690217933
    0x120406090b090a140307021c0302011e02030a0b0d0803070c050129210706050705010e060703060906211106070f05010614031615090506160c050618090402010e040507020d02 76
    0x80700702c1b1625035009120080e5000c8014500344074030440e51040e0b080d07550baa02c20b100b84024424800e81e000b01c843d4001603a80ca05203c4000c121064840c14034020b0164841100010340341d40304680e0000d0080c1442c8400c50214078246000d02005040300e43c040d64000c0362800b00b00302c05141c2190170b10007180c00e081c070908280703001e2081c07180b0701030303034503070943c00b903501040014003640040c0203050065002281c62180c5110700c40c901352003501c407100025550303070341001079200d5482004007405241503152031955050000960307a8804d2003000d0100c0700341080c0318226913105411102a5a80103601c03081e100e803a418000e0080450f48100d40044a4400c08a0114540400c2441801b200302d1500d00409041c440300c0b01c1c400d1114410502401002080440e040d40e801002d041ca9100c11075206401314903e19040325801c41e1076108501501d010300040b51400307504841c2c3d201c2d840050704c0c18071803a40c85000407140c82d820905d02c290001e28200c01c0c407513030f15070100d409000c0c0c0200713400700c8440710a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 690220413 1250 690219163 690219203
    0x1b060204030b18060709050f010c0218010e07031422170c061605220506040803180105031e04020f0a08030d0b01050903030406030e161d1308120406090b090a 69
    0x244c21160980020340e4130005100c00d01e480d030b042c003010300c10602d4040907010b0b1641c0441c814500103403801841c2481c80c0c00400907145005416070b030000007898240401034100c5000020080301620b010b058080c402d6021113a0000e00c0d6840d010303a6002000841088030000380413400d607028055142050207214001070348080c840c415840c040e0b90030350f034040c501650399220102030040c4480c0b2200a10050800058665030131b4084c00c081d1034050302955485803401380103071021045004140c14000140100441c04407900c01500010180080321421951a4400130f070850b41e50f400095403084d1030100115090740300001400c03542c5880601085442507144c01502c00307004440c40303564940e01c10042804585e2180e080f00a000b80040116910504c0b1b4020f900046907142d08501c0f83c18103100030308400300c0c0304107918580080300c00442000c41800d989444141c0d00c600009205091b0780c0d40c010400f0044142d0100058503002a0100f00034200b040b010790b05d03160010740950f0036250001403201040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 690221663 1250 690220413 690220423
    0x140d091a0910030f06080106064404081909050108060301060e0c0d020403350f0403081c1d1e030d0b031e1f0e0705011b060204030b18 59
    0x494024407450030202c0300001103003c1d019480c02c01d050384e5203400c000201300310240141e202500d0070b51941d810003408078001030f411694541c0c502801e400c01c6480c802c000040d980180900e56040b40d0400303150368440c10100014484c084840b810042660171204205510402650a03034034243e0703554002d80c89140c20142038407010f01074041030300740c50b002154981c080ba600401180c1007084016080c1681d0381c80340c4400018a481c50100c41400400703404600750300b1114400b03101039144169082402d00e100b15540da0155004c0203065400001d1201c048c200031824146240c9004942485103281a405286007840385105203e028841d440c00d807018070349040890000959003100450030030707800c15000d00280601502d016054014814061400d604030072041c2e40c0035030800018110381c0f50185074000c00c041a40e00b04100e443c545141415004404a08801150824a0310491000301a040b6164411071507900420080c4001000001c0110410b80c451156041060480342101740700c0c0d40940307031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 690222913 1250 690221663 690221677
    0xf07060c0308070f1409150d090b011d0c1303050303092a0310111c05060f011704030311040506210c0f0406030903090308030106030b13020903120304140d091a 70
    0xb140d002000b00544445c090041d100d07181000b8030311034260040712140c10301035200352a80550103850356041428000c42001450060100030f02090421940c0c10031007045400c09011070303045031000548026556510841a8007035500502529900d00381a5202650f5050183c08024080c03016a100d2914600c0440b0003031503130101034041c101c85001314007481d000b04409001c416805d641070004040030800a40c0310242984803941c0055103083c00e50401c0045002d8034880d504100c19158842c0d00304001d0803806400c10343c14100070902c1e405885c41e410160080d078003c0c64001ca4040741c0341e85074007244c0d01c0040c0110ba1900500d41944c9aa000040c020320500c0740032001044208001c1206501c2544100209070080c9031201c0c0140c4c0340d07903507010035910a0380103400007034a035000c48140b8602509240c21004445c001140791126103c0400d40315901884000b03050200031002406001c41e56100c0210119688140d40704210003c01c09480b541041c000c3c00e0072201488640c40b0b1403c0560101c0d209 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 690224163 1250 690222913 690222917
    0x120402010306050a270213030807051005040206090915040e0705210a0318090f020406080a0626160815010e040503031b0c10050105040b0603060a050d050f07060c0308070f 75
    0xc01c05c0c0c1d10714560783c80035a9031268038020303030801041c0054040602e0003000303184580d10340c43c0d44030b126050040c5400e092083d408022844d1030184001a5550b5003107550b48501a5001101030352030840d2580c00c80404802c00350001e0a00c400c224891030003081e003505a40b401c9506c5000740010210320007404052070500d030304a501020a10000c01c0c001c03072039042c01f109050752441c0140e440740450402c0c1c4407404078410500750041002e0040682100c0c0d00c942c0401103880400a0b5850031060041d44a0200e250b601030140642403d25480301c03e1201d959a0700c0049081c1c03c445580d42d0f0f1507643c801c0e0124900f180400d040002151000c90240c0031400386800200030b5085d07842e1540c0074117000280c03403034129809008000440c0540c0f014494409604014500054158900400d000903038908007141c0c1c2c03040008108208599131008c0a290940706c2c16a0003580d600020715196103020f240c034025400038030500d01d0015126a1185080c4c010b5171096030740e2502500c0d0340c0420f54003c810714020b000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 690225413 1250 690224163 690224189
    0x7060201092a0f09060e0f070c060c0306210203011404150c050d090303060e100f1202040618200c06040b1f060e0312040602060f060a0902120402010306050a 69
    0x14964070580c0b00c0c0c0100c10200c0d604084240c1d503400e10030300d00808a0b4807640e58941c1740c6100b00302101a811005078000300000031410285084500241200314018009002982c1c0f01c6044071500d209520200141c00f2001c4c04041c54000400e5030200950300b01b41c228803035828000c000603030b0448038400c0390040e9440b501c00d45015400c0e06c20314003e403020203200003c010f028004544c1c002000e010314081c46002e604c0c0041c040e8206411100c18440040c1081e2040c1200741c070401035120304590741022190070021480050003d0320000d000f4100951040040c030104c81e03070403c03601c0300503484412000d0340820460908500034092490038011001203484c035400100004004c100c01c10340706ea9105801e0740303040184e449054019202441e45800580004119101480890400708015080c038140302c3c3c801ca05113450200000d54501c0700401407a0fa088401c008100b1a86540c140c0b14040c00000500359142c818080c2108081c550072070b420303800613040080006480c103007540e0300d40c10348d030b04091101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 690226663 1250 690225413 690225443
    0xb04140103091e030e090c0c010b010504080d18050409050d120b0f1003090203010f090c05060c06061003020d02070b07031401050303090409020a0909080c071707211a090706020109 79
    0x11000301c1405815010700085c02c20b03080040c3d0b910030308644184180b402507a101c010351024142114801c502075414032504220601456000141f41c00c050111440c040d1018420300c145141d607400c00380e100b00d4005081803110010402e0202d410b00102820381d0394080500e0342264590306603046080c0c01d54214040602403041400c141c1d107016501009400e011078010803070b43c042403c5811005d1105081c1395101200410400c80c64080360062100f00c1d03110341080c1000c640d6a45856010703210702e02c43e040d41c43d80c00800b0340c0250143c41507030100c038204548030121420540c100203c00c0b01d404e40081c0c6404000c1e503c0c04012541c107411390782c01034025403c0c106404c0511000f0650000103070303482441c0c024000340843c232070b0041e00301040c801e9811645038081d81c220545413448a8000e400e86101803524a104000c00068200480d0030a80715442c075a5007494502403c02480c2201901611015645511a00a0204003402550520101c41520396101801c031f0880e158448004c10b401420700d007903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 690227913 1250 690226663 690226703
    0x26070206070c1112011d0105060f04021201290c01060e061f1b02120307060b18061507080309011d0109051207050708060108250602151b040b0414010309 67
    0x790312604c1c402000084c290541840112121103030882c4c00c41d80360f44031002c02040307082c40d01c0c00f6000c10005441c15810244c00041004000f001402641101e02c0f0040c1018503200b081007450300c0c0d005000507055520f000034032825000c0c102d2030041e01d140f10b000760042900303410403c518081250f121064194a0200d99000321030006140d000c291592620620220160344d0b000c00300403030351007603500943d91460107203400740641e900c6002d1a480b900c118140d00101c42c900514940c4c0c000340888120300c80d050111403030402c0340510103010740b0380c030300201c104880e4280542c080c1542e03209080100002d10350700e03d40c1c03509a9101201c0203100350868200e4a066240b010003070b20340c051148099611031612050418900b0000341d00800440d40b115081003000240c42000c1d049580e0090100703502141001c0000c1d41d00d80101140310406080e00001540c1070b4428001c20400c0c20405040580d603d665160389403481c2c111b030041d4154031910210101c055030013445941502d1394400310740d50f230b280240354074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 690229163 1250 690227913 690227929
    0x30908010c08070f0f0521090d0309020a0b03040321331e050603040c090b0303030609070804020d060606020a03090803090d02131e02070b06030a03051926070206070c11 74
    0x24160610006107c2c80108220810b8000ca525010302c1d585c0c64507290507000b0a00c0e0104584000040c149025109405611010044407d0700d4043d0100d5580303495a20701151244002074101c03a4511100381410401c0b0b205401039803030341c94101c1400c3c1c400e1400f502c01d03a41d44103240507801403203020300100300888583d0840d40e094501ca803042d50401c10760740c0e40c082102e991080b14200d9411400e070b102400700054500c540645141c0550003141540340c50340218140c0c01c00604003006020001c0c00180455071040440c1d120700354455002c0c8045561100043d42d80d03610210200c2c00310700c034000d0100300060000151072000c80e009141940212094003401900c0b4030f2903221407806d07610b800c80c02c03200f008054944944a5401d42006a0b201320501f4142c140c1071000c1c00303951007a000500c0d00f08c040b03648507040d034101840080161610901c1040240c414100c541640003c54188243c0442c0610007045103505c038683d1902a2101990344a100716410041440d006002709401c01d01e490842c108000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 690230413 1250 690229163 690229187
    0x914091c09210204020d1e0c0f12020910090617040b0601140c072c0907090f091707030816271205070f050303040b040306090201020a0807030908010c08070f 69
    0x25030ba01001c0080c1d0045026039000040c4070030407130f454101401903000c00c564081070148149804122035a40544d0080c0300001983c9a641003101c20504412940324650446508090082000b01500006e0001415034a201e11400e0003003a00c041881d160030082000d842d204982c0030f910646640c1e523400c01507034042c64840800e0800c3d40c05001c4402c00c01020071407400030b0309620003400d0305007041c88040240d602281c0c42856400149034207102e0b42403000105442605c504032404202c4140c5030302248014650503401a180e4100306500880041c0040000d100060182d610103d0503921072480d0480b003c5030450240004580d000580d03050011200040d10b48404d50010006640d50303028402c00480300c1d81c20541300c68016050801c14441131941d44802004241c026506140c500300180360b45d8040c52001030000c0c0e880d000c1f040210b80c4280700d03c84016503c402c00c81d480d00660300b001020359000c2d01840802c3d42c41c14281c00344e594042d0010510a0a0b03694a03550800d82907071003101c528071000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 690231663 1250 690230413 690230459
    0x5160f03060518070f05130204140904020303090d240603022214090c010207090506030d0c11031e070501090b0313020d0209011d0f04030f0807090914091c09 69
    0x1840e11900f0f542404004024006503c0f00d000041c00c04003081102e66900d140521803e20420040014410300101e240c56103400302e414039103039600d5001090a51150000c410b91047c003400c681000c2040d01d125111080ca180c50415880d5090841081c1c2100c001d4080a58000c0203600001040180f0000030005001d02203404544a140c0c1e4540340f580c4003064540c0040c540000428501a5904014030310041c03111a10500c180d0928502003170320703480b801204104124a0111803414003800300c103940020031000e0211908001030310202412026860403524490051200002d81ca61140142805a0b950030844501c1c1d51100d1818a0100c4203120040741c010317107450541c00250f07658200300b600030000c02d003c0340420000207c1d00a0481d400405144d210710001003484003007903000620005515043c00c0200b000d40702c4c01070507281e00710150310859a9509043c19078800503040e01c145c03801a100c21007280c2d04401e06000d5000101094140c41300020031849080080840c440c840c03001d400c01031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 690232913 1250 690231663 690231691
    0x50312030408040315091406071b050106080d030606021504051504020d0b070e190b0405010311040e0a0606110a02011202031e0903030f06090f070e0a08030c070305160f030605 77
    0x66503c00d203075102d9000580c142550740761108401e208012920002ca841d20601811319427070045000390501e4605030518410302124924001000400d5208001a0040504a8041e01c492020050103005203000c0e11005001d00142d07181d03c0940a94520700455018020704912520401c00f04002c2800604c260303800306506e40f1010102e2202c078000d0340500c5440c4d0b15004200c0c4c000e0148116060b03001c2e8801003111007210200600d112150a03641600c1c02442e001c10341004400b08400b1500960b000300041141079020301681300031aa1000c41211012388034010342090010304913840703903e40d11000e800b25040c408600050b0015038021030307000032080d03415041900540c18080007280202e40709100d42d44000107012050803040c2005901c500215044413880ca082c005c014018a0b01134081e8041c864070701070801c0655501118000905201d03c21240c8401c10b19076415a0384d1007a00c42514580544c1048810141c0180d400c4420382e40c525075954803036440d696501c402007000034182c500030200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 690234163 1250 690232913 690232919
    0x403020c01050a091d040c05220c050c120a0f0509060306040f060b07141006120f051203041505070e030a1506051810080a02011205130602030a020a0e040605031203040804 75
    0x40c455001794020b0b4001081121403070b051a1038140f001031034200c0b40c4a815804401504066021520a40c20b011644c010a1600207014142c03582d000342180b102c00350240ca0b0b86c01c3d000140c0b03c405480001c5c1c0c140e507255042c19011500f80e1340e40c403605079003940000e400c100041c52420b10350084074900620081c00202036540e001884a0341e00240805c84425400d130600719620281001140394003905150100103161a00c110180156140c03d802429140408218018808140141c08110031402059652403805280c000e28241c0750107041c0c14054541004a1011445540c5564894001030010b000a0b01543c4078074800901c0c0c2e002a11040e6202d590100f901e48a140f6012959180c40011380200c0c109008200581c51098000340850340c420038660001d42e91010012807000002500004c56440d001c0480065214108011f005580000140801820307194005d180f003007010703076a614111010104000950b02580f082c564141e001400d00e00c4943c58401c02190440d205091444c54155 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 690235413 1250 690234163 690234179
    0x50906010210020c16090e0303010e040c03050d0807021006081f020d231311270903040503070e0f040318080a05010504060c052a0f060f1e0403020c01050a09 69
    0x1000081e07810b03603034224010317104c131424a0070b590202500c007929050000c840188101d9651740414401c5513102c01d10b0101140510100511341e101440d04003003a581130850081e005015198196481c2c401071080030340305195841d91344211010b85403410041c0400001d1030807400054140c4001050b0060b81c00c01c0310300d4100045204580740012990384130a01400d10200800001400038064001d040200e149140003031807501c2c88a200383e00407500403940d030081031764030b03030700305054042407080d01c515107042c02140b083c008064000c6410440490744150b882d03141c51010180c06445903c280e4209078046030000380100e404040c10041150140c444543c0c50b41d41c1da00e019000281a95565513520522080c4102e41c00f038450542c034241009442c00c42c40324041961415000744803403500210000340301c510002072062800c2a4902003c0701c06500780442e201021000588802d0008a40c0c40c101100c000f1201601d83c3c49940c140c5c002e02940310003100192200c0c0e101869405c1000325031600400e4240c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 690236663 1250 690235413 690235417
    0x924040e0f01090c021c031104090203071110290d080d0f051302180a1503061b0201110706200406030b030c060c120d020922110301050a05090601021002 67
    0x1c080340001d5082035240003618000c603007500d50680e045403c009540c1914040361620000c001d0014540004d290115141c2440c0d84c0c0581e820034000e8a0002040c401c0d503a511140d0707118641b070048203403040000e1030003a17001121a54202c43d07040c00c02404c1d500f030105204094041a0304000b41469840e1025951225526840a080900c015550381d542603603400151240584c400d00301140b4419030001c64000070300d200144203014502039030782000550300e20300b0f90b001484003005900d100003400e83c0380c6c503001d0b0241030801c40b03480c40c0c40c010148110680f0320500685a2400e85000d00d28075042154494101400051101620f22094448150b001101103801003004080c02d960004040e80d8410425042a100200191240c0c60074030800150007008900184580610044241e070f9121500c4504040d01909004c180d019a161128460040030700305094042d481302a810000c0c680c002035499801c0c0803e0180d90741100b5070000a1005050100c0c041c2c0d00050305004031440e00080d22407010684e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 690237913 1250 690236663 690236671
    0x10e04090c2d0807120b070e04020a0509130908070816051207050f06070203040b0c0705191a03041214070609060615050304172a0703030905060924040e 67
    0x3008207901a802e4100c030142c00e81c0082d00300e50703002d00840e92510040e4a01c415001d0f002400e900c141c800401c40080c0648501003e500d4082d00c103644030320301084050300580054000c2030040540400f1440410300900c901c01ca0781d40c0c0b0410080c1040b00d25141c814070350700900c005100c031084c1c200342c0a0102d50100109860000180d64950707036800c1e00c0c035003a0f0034004580701c1c500b0158000c5060240c0650044191010348000c800f003035403515880c4400a240032619801a500401042c04503607401c4003903641c0307030190350559650b10380440300c0c500504442c0c4012200900000311150300ca0248900c1000201582e6140c0408203092071801c0d1105400c83c0e04803041161156a210320401c4001e1200c0e900c15015070380c85c20311504601d49501c42050310384d4202d056029070f4100081d030800d4070013203500070841d420701031421180080284030155601c2c0c005002c25000b00310705000c000340628001080318010080506002c00e034004030b00141c400300690000b80c61031028144008204503e10950071845 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 690239163 1250 690237913 690237959
    0x27061b05060c031503060402090703050703060b1b06061f0e06040504050907080d170f0c12070e03100b0f1003061806030b0f01120803070504090204061206050609010e04090c 76
    0x43c0c0d04192410700c51568100c01400e003e504102c08000250f500e201c034050740300045081c04241552900c20840c020034654100301100040401c1c003a4183c0c05284620300521501d4003140e440391218001c01001c000a881440c000122010343da000c0c0600c00c410718080001c014248609203600d0340b001030144c60084902d807142e540a91000c00a00f641000034014103480c03403c040c40d003032000c9803200034114070044c51121588403900c049402c0500403422100706030603c1070141d07214108204010100d0042c958681d10070b21079440a854144100e10601885800050400030781c102601c044c031000040701d8200409041d5150400a171b00c1100e886c04181c81141032100090060a51508040b00320024203444900c0600a0060010110700035000fa00290001601c07034680ea100b9000b1100c81c0b00b10f41012034118004140022a950054081d000b44a1510300c140215600c45052004600401701034a001820310340741a000c0342403c1d4004161103010358200c14140b5101d40046224999203030381885 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 690240413 1250 690239163 690239167
    0x909240903021506060403020409050705220e0718150f0b0c06010905062101090f060921140c0f01051006120c0207090b19080d27061b05060c 62
    0x8055043c0f1101644207282c182d8035101c0d0a0010106095000e40e000081c081c0ea0b0703c290441c2030100401c561f0000b018010441040d0810100a040c2e204801680310300d00719041078404c0b04000c1011401c81c0656201d003100300700302800d402645010701103107d87d0003007114030740d00302040c44070000c0f07201c5000c1e20303054100e103031355505641c1c0790392610405a0107840a2403511003400056552302200000f03110100880d02012241a240f990042c69659401450100c2c04034024082050542014481e180210b035000c113031505050f47c400c4450580140100092682002000d01492901c0a803041e141e1640445020380c151071845400c49006641090401d61446001c002e801e6000c4038064000c4418071040c01104209100a0340d03900342d0380039040903641c41e030010b56000d8035503002414035402c04002841e0044e6444502c0e0391200365814211001400500304902d004d09000c3c0d4003040307500300c401003805243c54610100c601c0c2030746c500c03034501c50f07928100a000420000c0100b140900100341c0f40079 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 690241663 1250 690240413 690240431
    0x20d05061512030405150f0304230f1e0c0d0b0a06060903030c12030b06030708090f0102041a031f060f030b041107020f0406080106030501050a0608120301090924 71
    0x40004425420860b00c0746201c410705040c51900030055604659081d526150044102d00c0c01c5200c80c0510400c80303201060100070030051010101002001382040f405250070041d1005a59071101c044d00041c03203092780311050300e21060f09000c3c0802e00c00340e00e0500780c0d54200c252200294039050210019100ca072040c0f0107001c00d11078070b84982c0b001010b260402081c61444c640d409455600d10102c00f500c40780c4c076000401d00b802d00030340001c102140d00a1215070340b0301d803541e80036058003001d8554804512800c0d030f81000e00c05c014403c039420ba0b5110072213041d0070200c550416695510040c45040d80510703024041594581c00d041000c05480c25494145105c07000c00f00090840341c4280c0a030784200e00300410711b10008209070890b04081d40640303000384c14208400c0418040c01c04e81d0301440c100d46c40d10b4000418000190300041c011880c0ca44c0512005960b00005683c6c0e641c00c40c090f80c01d181c004c2004200d003110a91101c03002c2da1040c41d1103a801d0f007007601c0e00408003040c405542e008540350401a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 690242913 1250 690241663 690241681
    0x201110c07050a0f0e18010f0906140606040f12020f0415150503160f1e20060c0313061401150f210c03090b28060501050a0318020d0506 60
    0x100024115402c0c04000140c50090641407890004c0d0555603607071b804800420000c10f0a402035054880c12100c1444810410300c0c00000400d05107018420174103985002c150a441c001c0c08071802c0b6100400221401030404d010990010b00400040364440d400c2aa101e04503240d600030722255a0309500511610b9180488185041150b450110100070003081000b0558254448002c0c0c02c4556142400480d0b1a9171801d4034a02078076003440070644000c00a000d1407a0b40594111855140c00500c00d091100078000c01c1c2d500e04080d03a030a00080c0c002c7c80059656418a00c01000c0e07180075100109121302c6860390645010360070380003d03040000009001090b150000d54410401200d89400d80115424444e040340d0003560178030007403405031900401c41c4164840d400007091130750083d00348011402c00e081d400c08180c00b12988850800060070328861031100922510084ad0810b0b121185002c41c0f030760084009092228001098001c0b505910015031207240590005d2441540246000d09042c114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 690244163 1250 690242913 690242929
    0xc0b0406110a02031903111e010f060506030403030519020304060204061716181a0a020d0f0f08180a150513020102031905040b0a120b010302070f11010201110c0705 72
    0x46001c1e1036000112010068800065030500b0345121214a0301440442c17074100c0d280311f00101702080783e214103020b030750054a00003424985070100303000800c00400c4a44847c8151000c1e0301c60103501403000d200080c0828000d4000c580d1103c044008600d1034a0700b00300650407a0010f4405076481c0c0e9003c40d041c030815801501e071501610310f4111094051500303502111310786210390100410801d0240d61000305070080300b5000090500c003480103d184a00ea107245290790807502210005200d00004240301c40c0c0070380c1c04246562000c1d6544041c040380ba9206031204800685011200c03450a100c0298240d814000c600000c0d110b214500180070160340301c542554405000481c40300d40c2d04505c480180c0e0000111402c2c4043e121200f18004041501a900c0f8003503a4403003080d0840000c1c1e812540e82d40020881c02e00c41084004105071884000110101e02071a400200000d07840c4564001003000b0002c1c81c2e070301000505c0042540c0442203842d50700c0781c20442c4455070340e0748018020b02451800c424 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 690245413 1250 690244163 690244187
    0x60f0e040c0f08030304022107031412031902030712060612050f2205150c03091018060b0f030111090f10050f030709050307031515030809060a03090c0b0406 69
    0xa0070302c42803820041c8480d143d1101410013407042205a441403a0425000c03101003a02802209403030b0410b503079080001c0c0d444000100d402c440e00502c1c1c244808100001c041d82e0181084c05040307101200040c1c5803400a43c0087c0908040c00798051554190990b140548000b92643c0e54500c00c418200502c11340070385102402c81100407140b4400c021114205030301d503a0307480c0d9426020325241c045030f05006080261000e0060706484000d03041110380324801c0015402080707080200c840e0740c00d203941c100080300d0102d50001c0441001c60300b41d0000c0741320394000c1d60003050f00510b010345c50186e00e000282110155006284c050b03602040551961500340f00d04020032000380d504e41d5141488280082040c41703801c440c114002c8010011491440c0f040020f0005071101408540d8210f44a0524200075240364094ac0e22540c14120001c1d00051820a1801142c0c0e21071a0281800c071080c0801803a900000844810580d8400748040443c51020748440244501c0050303594403410048028100301c03082c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 690246663 1250 690245413 690245429
    0xf09030203121f090f0506010f1e23030f330627010219020a0b030429181501090515090a020702030d020303190b0d0218070216030b0118060f0e040c 65
    0x70241c407a0000e640000800300581000ac0d0303001103d07010341e0841e14003030180d0010398034182862031000c00140150300812601d00320400d90781e5015142002001d120700d0b00d040410361a117403030000e503a04440703854502c0d4004061608000c1185c003030101141c584a03201410386032001010102e541c0621140d40100310750202880a00d00c00e4010650442640c07143e806034440001c002420f101d505c01c28100403100300600c4850980004109000401c029210102610010741c208a6442d0000400c064502d000306c50010346c680ca846299402014000d05c114480c60b12243d612005655603141c0c40d105e001d84440040e1641d681c0c4c0140b525006c08c44400e02e080d940204107000b003210950b0f0700c0d18043c900900d40881c061680c2d001042c0300c0c181100b03009400210911407080c03080340381c0f40881d1240d14a5800c4440d00c1c002d00000241d58503845c480134004416001c01070000c20000a490385e0b504007940e4010405554a40c4c1d50000703481d1030345c000c2525400080621040011020418000708030030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 690247913 1250 690246663 690246677
    0xd0e04060b0f0a0c0b010e010515030405102a0903061a010230030415110345150108030301180509010605130608010f09030203121f090f050601 63
    0x151005003070302c80c41d4215881c080c004140903044520400344a404580c0c440d2a4007140e59444150201c0746200b8010b0a01c9040d048888404d0040140d0030350703200b41e40140007410711701c096220041c01091003005286080f0022403816032210300d1522800c0c80400940e50300c420b050301d0350802000304d0b0140c00084903604801d080412050b03900107040800c820102e44003050a900302c0488035412140c040e044200c03000c0c04010401800010410010181c800c20010310090b83c003142da1003082d1004561400c08440a950340c00c1c0c0c44249d000d12450b40f140b0308140300300c0090040409a5101c0c0303100d4825401644145460741807054645540303401002e04500031411541400c2c170201d24080601c90401b1956030700d1000907444e90007500810003c0c500640303540c0360060b0000304c00e0003400c2c1900034064550300b46003101c103480d0300c00d1013540004d641550203141050f440301c0f1f0f46035140e18003618240508064030600c14006281840b1540102501d1100040c0c0f10b01000d0b071041a02c500501950501541c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 690249163 1250 690247913 690247919
    0x110c0a0303020604020120060c09030d020c10030911090a020c071502030901030218130219050f090d39080c01021506190e0603160f05130207140d0e0406 67
    0x5100c3c0d030030644c2400c1c0080f820501099108101c2035100070b880c1540320740c01c21322048a0780c44006008604068040d0f9003000c05e0450140d03915070114880a4000b807650010060391403080d4841030f4014814034144650035082c40020300012001d651004003194001480304e8007020030801030004280048120040c42101400a51240508214241450b40008030341444c071040c05d207502c1a403107004102008044811100900940180d80407000790011381c44161a03590090050301c071000214844c00346803d0454003845442e500c20b05040700d070440b248461280344400407c9004c2001420000d0102a2501c42d9901c514400d13180d0028500d50050711185005983c00305800c0da0000484241d5191919040003280c1c6c502460800c3d203100d038403844804107188002c40d0301a03010300c40407022038840e840108400f00703086405106518290102c0d14041000b8280b00320300003c02d1080501c01030401000da00ca030501e6050654000e85990006a0000c08458200a04c00072504003900c0c108a141d017 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 690250413 1250 690249163 690249167
    0x105030f03041404060801050f0103050f1b04240308070c210b151305101e0303110109080d020c1e0c190f0e0f06010f12020d090210110c0a0303 63
    0x4181d014036006070002e50100f020300d4403560405402400f544000b00728524022000112049080c0000c0f69180079014020075900c100240c0e0380703400019034004c2007110300e910040100803c0c00c000701101c405006800128985a802104001140075a0700c0542e61506880c0458101c84543c100308039211240e80e030050b003008900400d41210b40d0010502055403181004200c1141c40c40c01000c1d48021070001001c80e0310001e03000a40903040340c0b00821045500d5001703e4010040b2007211500c00e03040c000080003c64491001c0076041c41d2a40000100000c65449450895000c503130f041040710f40000d0070701790354503041000100c40032180400b03e030311215070040d182d10740b007200060b107124081c044040b2400070041b22581c0c000345070008840c20380795030362109003c003c8800c840000d1381e2000200091901d5024204100c41102c0c29034500c40d040030b14802160007504400e48039510a55a29100300040e101c4021446c481003c54548a00140100b80c03500c0c0342018801d40a80a200d8016041002070307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 690251663 1250 690250413 690250417
    0x160303020d031506030e2b110a02060304020d110613060809120f131805070f05090d030f0c060c0914040b0d02040908070b10180e120f0c03030108060a050105030f03 72
    0x20614075000c00d100d5841b1008501e01001c4142005505200d07600d0606100c1d00140e250308480c1d480d1f25085003115035202c0e180d03100c51600c40c1c01394100804000203401454a01200000745109040c00d549007030305800840e4140d0004000d040781c014881400740041c0ea000381d0900e502040c80c80c0140031070120344d00540600d0041c60300c0c54540031b0000c00c0140e000c200300452000a000c4980284406540460703a44d006000203540850105070a0418032480d944614100c0c3c40182010f045c0b40c2d603d409a0380c0071079551070744425640c200303d4a012520000340d0140144841d4030015664400820306041c58020030004544450384954640602440b1a8a88604070301d0429011603000492066a042001c410300c5010f40043c6403268040420100e075514201e03442c160b861503100c00a0482025244200b210341e03c0e00d81145603070200507801c00b40a005030040020100c050442400d04001000082c5103410a80204c14590040c00402c54071481300c0c03103135600521049001f8a030307110681030210384034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 690252913 1250 690251663 690251669
    0x1d030a060b060403080d09060b181f150f1b0f060908160b0907060c08030612030d020403060e010c0207050a4112060709180e160303020d0315 62
    0x66440d01031510482c0d60340d20983c1c00a40d0031516241c0d6070410070040030b00401550508585192a00d00741145030700741001200305000c04404200c01c180c580907603401031102da40031401c00c886c048001c00315400310074202c1d011464005842c2e003036901d00319407400750603140414400c0101d41c17002c0e2030f9034010403240d01000d08a1500302c40b001800b0300c16402c141c0b01c284140000010748003403151701401042120948a0b06c10f02d010b00a8a12070b54035904120354003941444054100c0303000342b01140c4185040728141c1011000c1d0012280350151484814090341c00c90b40c01912884d690b5a08214502401e0040082c1c0007120310140c000703a402d100c00030341d40b800389025003040c9200400b400000312031403881d1f5400d5100030014013120350280b0b4441110405c1c3da2851180201c5d8042103100344840b00048083c0034588a459408260342007814014040c0095818041103903190a200c0407a45420700a0b00380070324984e1000c4c441d50f030550402a18181c81c2c0d4800d00105032601c51031503800c800b409040c17429 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 690254163 1250 690252913 690252923
    0xc11030607171b160506090c011403060d1b09140702070b0c012a1710060c020303220305060c040b0909040602130b0a0306080609210c070308030402011d030a 69
    0x31615201c100800300c80308020352946500c00000c0d805400a500701000344e41070f100304200c8415a840b50070302030300c0e02c194030182c60109101d20310000d01040700e500610307804140607044400a010944411510300f019081004000c200c500040c032010205014406114440c030700c160700981440c1100079070352840c2d4840c0400d070990106003001c40b840c6c29048440c0468091910404c807035010721000b10500c640086010100d000450314040300139079201528454003409690780c4d01140b805a041d0307000c00d26484100ea05010401c44098081601c6000d68110042403194440d0b4500f5450582d1a040026080030b058400034041005500428000c4030300440080e00c0400503070701d0700c2c075020380a4042c0c291000031b0740e480c0c80004220500c0d088040c0400c501643c1c0d00707100640d92880751a8941400b03a8182440390003008501005030402206000b064080720b00f11864002684a5107003810515042106c501d07900005010a40d0792002030800f0341d1f01c10054a00b44480d0344000070b50754414413800244 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 690255413 1250 690254163 690254207
    0x100203180d1e0507140409030e06030702070f03050303010611030f031302060c06150a09060315111201060c0501050f090607120f0f02071505060627100c11030607 71
    0x410021001c80c2c202d8803040d414010400300c6520f03010707864511500a5100f14100b041001c0124501400b90000702034058075440803000341e42d824130100b0350001b060303c0254860841c00040c81f0a0509000c80154001c502039900ea50424000903c41c00d440003058100e46d206000c0c00c410140601b007180d40160300a41c1528101c012840841c039280038a8200ca19180158410801981d8180c1c0754402c000b40225501c0e000c258032034038114101e420303a000103040b40501c0011601c17204401da0020101c41400c2d07103158101a0b4150025075015000d03001070001818540c000c0b403c2000900139540c100703c0e140010606468204503095550034000d2081080144e118888062001507500c2640b00e81200c443c20f020481c140e134541740107075000e048116003400080007101c549090314450540915802080310b403501010000c00b24102040300600c0030382e90801c8241090702d9a69440c0032500c0c003815259610039201a080c40b2a48020700ca440f03d00a811500400c1301031a48004103442803c00071602e20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 690256663 1250 690255413 690255439
    0x2070309050d05010e0d110a03030b0a031e15140a0216060f0c1e05040e15030a2405040809131d060f0a0e0304051216060e10020318 58
    0x40e180c0005520160304015805412028414107422001c2080b0260301101d00c0704a241c46c08590800101040c20019088074900f04002482500101110b40303000b03000540082d280d4a030b001016000c4101180844901d080e07460400019081d248841180340000b0456211030f1050310b20030841c002c00e811441607000034012504280000c400407600d230807800c204107890303038268084024551500401d02044100400300080d01004584c0b081501031580c40504051402030154800c280182c0240f0700350384500310408880d14204145001c0d131b401202c944052224003140412000c0c100c00c03154500c24200400c20010032207140031214241e4041e912010344407915404a002400d05080000d03099040d182c0d40070360564006080d07030044510b8500c1c1ca9264079040e210504440b00c440c043c0015410a000800480ca082c0d003510040c05003c0d01501d42d40c10141d4681440c200c000d07004000443c040104204c594108004036111007520381c00250f10b003e0b441f4101e8002c00e511101011300c6400728031205 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 690257913 1250 690256663 690256667
    0x41401030b18090f0c0f060a0e15070b100605122208120708070f0e1003110d0f0e0c01022d0312061306180c02070506070c1406040b0d020703 62
    0x2c06611100b00301d004050b414840316941e2100002c04490300ca030310465001828618007610b0749000321030700900e00d914084c07000d1030035650381245003401903106008030110b0820f00b441c0d000900034507100f11008031261414148600c1442c2841c6c01081c208030041c403680c610484428404e64018030150900da5501801d02040340050101c0040242207280229a60040b14200c0d209107004040f2925000c0075035aa450088a10001c00e0001c1400910140c1b0401c4060412032407451030981c191501090012190106040c81d03400000707041926aa5010f116184040d107118248400d65414040d00b003d00000c00000e44e21a42c2e0ba44000c061030340181c0042c41242031010410040844000b642d4032a10b080303040e01c0b2004e00840d00c150103140c180c060540d8021907441034005945085c44c0500184030360f019101c00501c00f082e4040150300c04d02c0004034403980d4260117001154415598901c2050038000000340320f1141c0d505090007410103200c103108107a00714041d18102002e01030010f8035011a4141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 690259163 1250 690257913 690257929
    0x31d0a150b0a0b1327020901030902060c0c031606021f020403060501030308040c0e040807110d0b13020a0f0605040314151009420803030703020c0d0203041401030b 72
    0x1c050b900a8000e80c001503100e4030000079218140c60403400d401d0003559110f40c0340c01c004c880a02d01004124840000360b074442c01c1e178058884480180b400060005d080d902041d4194020040350b10a41c0c851154504140740c2080070003118521040c5041c44036103040b8001e5921000f60300c5034100911400b05482504215505450046801c5513060003035583d281070280c412039041e034041c0c4c0e82c001510340219a01c43c100c4250b0703014070f81c807041e000d1810902d5110b000c028070070788280d9984400d00d140114041500c22800703c1c06000e828030392420548491040141e41d00d09a0b020204021800c0400c016041d0460192405c40740c0004004040c1000021840e0810070755040c0340200310100c1c0c041c807110181d400001000c2d81d804c1e100422441d896540102d16495061419442d60340401d500d10480840b40c00903d4104020100080350032a11000790900f5a0021143c550020f903000c18550145901005030016142032800654503050400d10381782412500400f1040c10301d0f4592039100c07126281c00007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 690260413 1250 690259163 690259181
    0xf1b2307051b0a120b0105062109010b03010b0409020913020604090c20211c0f0b10081521011a04050601170402100e15030106031d0a15 60
    0x751032800024800150340c1801a810341ca0082a8a01c40032407801802004903044c160000d803101443e81ca0007081084981c08001d01c0c0d8101c602e2214511a03c44d13007072601c640140200c10005c1490380c40358003410f085400440c5c031035101d030703052400b0f03480581c030760a40752a041100344030017400004160020410b1442254404c1003040d02e00241000300316031214004082141c41256400e078411250549541e1b25505909100301ca13503100c0c0340840403140320000b442050405004039045072024401138044480c501c0002c1002030301c55600d0071240c9003d207010314040300c160174032020340d08082c020350424034208001e00d070080442c03454080c000200c2e003860911400170880240b05541c00130583c2000b124805070803a02650401c000b0407807940c050341203a515401d054200c3d40d603580ea15000c2259600201200b0b4040c85840107042c200e41e1540701900c40300b81c0c6202c202075aa5407414100a00b12240510f4803854a800f09121078100c610120310140c0d0580c12950018106c8070749510b500c000c000c040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 690261663 1250 690260413 690260423
    0x10f15090e0c062701030203011d091905161a07061a1011010507110c010315050603040305070b070f0c082b0c0815010903030f0e0904060f1b2307 64
    0xb0a6803500e9040c15507410004640c0c414440c4c030210403c0005400b81d000a00502c0452200b4061445280c0c54800140b6480800c2c1d2084402c034002041c0082e030300506080090303409030031171682e164284d003a440310703403004007400c00195500010310084419580120400281015182e0001d64921000800607201200000b8404d45107a000ca003409010210b1180f0311a005501b401c0008100354000e049103005195110701a00b00032035040e00460043c12078044200d5440c0384103101080580f02e0700040c5200b18800c0d02c416541d00f207682440c00544000400880420088802600d100e40d8050101c00510341d2100005854602d502110014403004800c40c1045500ca02c0205070820015000b48541d1030341901c0e48007080e1100c00c160400d82010b544014041150113004000080c4500c0f4901902220380c03400d40402c0204100040703504034155820b84030b10341c0b40d00c0c0c002120320b11482088078130300c20304c1c00c1003043d810703400d402a1040e0412006041e0390b12100c0d003100c1410b000e8608850750161b020b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 690262913 1250 690261663 690261667
    0x1d0301020f0306040c0309020325170105040302120307211803020102090406060926030f0304030c02011d090609060f040f06150516060b0409140a05010f15090e0c06 72
    0x7115642441e0421943c8034030a609260000d016540684210345072a600039010b84020841142c1c10303440303580364600c80c10760801400301c001085422a080304100301071200022906091500700280391024030709050035030240c1003040c0b007030240d0080e6070101c0c1028114510044400038002000c020300380b0015023440040d10015a00170590706500070300a00e0400c079010001d4984401d0300b101c01c4003640c05248040c955031106161400b01c0b25480b03100c000e000d40d08070303850015840b600102540043d14110013144c0c0000c800402c668001914807020500300004052094038040000c6807200c01520f40c0380a08280400304002d9201d6510b5100e00340400307041804201c40c1300036a0402405c5500c1000000310395000c5100035580b01d601120000c000784802a403a11000f52078460040140c0700318541d1150780e50307024000003140c1030518094903040001802010a00c0d040460139104a101402d0450341740c407a03483c0c1c0c800d86248145081d100364100c000748000d40c0c47d1505141416907400b030f81d0304c0400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 690264163 1250 690262913 690262927
    0x6081e040c051f05090402030c1e070201080f150d021c030822080307182409090b010f030b0411030103051f0c0503130f150b0a050f030d1d030102 64
    0x51034908400b00c0d041610621a9801c1c208800000000340142c0030307000990400694801c3c0c900743e000b443d0404401c062051034468004041401250f14506c4200c00001c0802c61006542e007140f08a94441c20542d800c0402e072800b041c50804030402c40c1c50262049225103260303015911600c0303044145c640a60f9440c4014095400c0180c40400201c4081000e02c09010a1424a18001c0403010744503900001c0c203401c649844509480d0542c800e0002150000e050800184102c05803480c498039801010f500c040c4020044c200608004d0f1701c1d0030001c010b50519030002501e9a0101c01d5180800b0b07540750009558008a0000f8058072040c40e04d45c8070b00c0030110000c000d001c804944a44040113031150300f04206141d2103144140d8001144410120302c0c11700008001c200c000c010070740f4032845880b0001c0911503a0b514080b10800000c24082c001d0703900c201207130381418054420400b0384821074140040303204410003e56581c501c1140f4000f0000b40407004000202c0030f0500c041241d400400030354450314 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 690265413 1250 690264163 690264173
    0x140d03090f120507090b0a05220207080a030b030609120d060902040b0c0607020d09030b070c1211071d010b0912100b0f04020705120918130c0e010f06081e04 69
    0x2c03940686a0380a01480002c0c04603c0c1d201e4032121000142284501619100801c01040c07140c50390b00101c00c00c1601e0b000c4851040388000c01c00039102d201c00c02c1d25111aa10010110340c40030030414080e80c451418040e200d84001006040443d07a803002c00e82d00c400e29051100508031a50010040f14004a40421507001010281c1080e081a13400c542540c1d80d1a9012030361480b01084001c0440e03900501070001c1200e00910542c400820f0406000e80581590703200c112010746080c810000742640d100c2e1241000502c100d80081401007034128403031549080c0340050400c1031141d500302e940d000820301540d8a03214448844542c184054640701d01c098000c582c09810300d03225141c801d6401d283c500420303207401d1007075424040c0c0010050601c1824282042a00d40c4409400b40e4070140c0304044403510980701c2e40b0700388200150a5804150741c00ba03e401d01442155400044458400c0c800501c202d241e40901c10007115814649401d01c3c0d10f03844c2030030418401d140030101020810f44108000e00c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 690266663 1250 690265413 690265439
    0x102010f062d061b0609051006081b0105191106010303032007081615090c080705030a0b0f070912050303070e0f01020a0f2315060a140d03090f 63
    0x2907079503524481562011402d051040c40c15010341c0e00841c110301c1d105540100e00c3d40707010207818400d0034009014101034582920b082449811080000d8841805120300034060210038410072040340b008405000d0040046c010b4013448402001009034804082c54041c403079841c058035001b103c1e0a540d05540c50341001005800448881c0ca080500c3c0681008640003e100b01e405003900040718606118001c4c27141b00b6500b00c370754020340f0204805503046890140030310540e41920301c103c046030030003031400c260b460400d03407680d1000d886034104d80313080b001292030502c2983d8071414181c0d42d000c25035070341141074031009010f0b0841baa110314000524000c1290010003140100031548520100c146903400b00f0050000001040380140c001800c404000303408017a2100d045842481c4440c0c24100501c507580040420340c0348600d0316806040700e542d1007025110480e802c800240d0341d88880701e082c00e006520b13404550b40303814022440a03400c0340c1494030403403401c0003030004001d410517429500d00d1509161 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 690267913 1250 690266663 690266699
    0x417160e01061e030b03070626070503011703160f0203060906040c091d100b100c050a080c03160605090d05070c09020903031308070608062d0102010f06 67
    0x14164100020440e0521200c0c100d0480d40d8658622065507114812802d194860b500850700345519034000d2a51075074180302e110081d04070f5588180c0c920301c0d071302a00c18401d60040000401203a415040c0700046510100b03c90545a244c9101c0c5000580b01a41c3c0d495886030204000e2945002c4e0140380402144d0004d071051a80201c0481c1c820b9124114090748404056800a0103107454640c1003000c801e1540000d01e1701400020564882000f0301e030261f05116400c0007610900da81c40c40900390310b162007001d6605110391494400d040c0d46260380c81e542d40d04541c02015040c80000b0403480ca0541c02041100c1481c40000d9040002e440b01745410070150100b80c564196078043e074038a2900017807103003050715030342500320542e41031140c94006080020343c01401d01a8150004002201514000100c90300080002030020280d25152030001043e01c1c2e4042c0201d841211600c80f0100001c41d45110500b40d901d400000b010b0404010b00140e00406100b120b100d0854201000000d88400031070744143d803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 690269163 1250 690267913 690267943
    0x2130509070f0e011101062103020d050c03040e060a0302040207050a03030b0402070206030103260406020c040605040b0105030411062b050f060a380a0e0316090905030417 75
    0x15440c0d0500540b141070350040c00c41e00243c43c5840e6001503610415100d07110711071550001a0340342e110424a100784142048000e10300f9040a104000c241e8104284641c4418502c0c2140c28003940801c041c0d124800c91088005507840c174008200140e8540901d031004540c0101300f10f42c3c644452505944641000030283e011910303000400c8a1802c05008407080c4a0380244080d282da82566a48001010100302401d10b40e13000c0903509280c0710842c8000e00203840d5980041c0000f0340f112080206079202908401c0c080c41c1484200c51840c2d8011040c1d030741003548050540403517040800419a6809601c2418900d07110038076413080c0c0e1141da180011801a81c072802400307255544401e10101900c01d84003030b0f4219000580821a0094600702c81903281080703507410800003c810151400321010b083e00720750031240010848001d540082e916a54444144c01800201e6030348682004d0a406500c50100c88a45806105007044001c4c0f084030003400c1140c2d540780100c203a04040c507589102c0040c403908 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 690270413 1250 690269163 690269179
    0x903052b02071b082e0608150a0c1b06020306040b0415091415060304050c03030703270609180b060a020105100e04080d09030c0611091005030603060a090312021305 72
    0x107880341c40030401720b5101c112101d840d101d00500d5400069050128000110307a65a1040b012407480000c0c0000b42d13641124040c81440b50810404402c22103028050340380621460140118041e1030084d40c203080c01b0f4100c10016160fa55180120303001c0d0400321040c1d079026103007200d2295030b031200f08201803e0b100481c0b001c110b00380782c14090205c8003406036850518032030035410103138552500200642c0d00030320550a958030012008040381c0344d030300501c5045001c50f41454034210500221a124001540d241110740c2d40c1c80d24191024040e41264003440300f40640d42984010803643c207400400c00d051003e0481581d401e914100280200015a00740304181403840000645080c000707032103402213030070414443c03030b10508150410003000000021030522041005d09070220f07882c0c0c072a24200c01004003106548064400c10041c01c02450030344e15051003000c0c030900c1495200000d8582d4411030554000501505500b400c0e912500343c030312a40481400000c214901c45c1e10510b8410445001740d0b5480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 690271663 1250 690270413 690270419
    0x7030b040902031e0f010b03030f03060604090609090201030c08040b0601030e0a0b15040b06040e1609030519060c0903050a0813030c08010b10030605132403080705100903052b02071b 80
    0xd00ba5207021f40202c0d0306500c240a0016104807031002950403200c000c0109107419514580e00041d0b032007942c00150440c0d1b82e0420300095580500624400c858030f442c0841c80c030b24203990354500c04e80f00035092504050b50340010500d150010080100c0558001070928001c1c901180048960540051610f0013036003022008001c40c244101920b0556060164028203540c685244503402e40e2601e0210080255046000010070400c0c4076038960009082d94000250030281001c41c10365200000403420085180e9003003000c200c000c29114202ca90003400c240d42d803d449100c59210201035040941400e841c05800650500150f020000a41082e94000b05c018010001901111030038811141c201e07030038840032405481a07901010480c04400c0f20050080c48907001d07884a5070050f00304440400e800110181808005c00403e8103c00b0107507814003144206944c014124018810320b680c050a61044002d8070048007104400d592102d070b2011502c3d08050700b40810b00e80026850800c00150444001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 690272913 1250 690271663 690271693
    0xe0312041e0b030a0b0105090a0305010f14220602120f040b0c070b010e04020109081c0909021e07050102070b0c120a060b0313020604030b0403081e06010807030b040902031e 76
    0x860202e034042d100c0181141e0b644018400546100380c4141c5c10003000b0440394003180d0350201c51741c0c06540500000220001c2d04080700040300c01001c1e03c1d072402c45090b81004024900191030031680c603401080005988102d2901e44080d001d01004a030035100581c0401c40d6602c03d612206109500503003003801d840d19400410396107403140001c050b01e0606413000500010300310321942c642080c410b140401c421555035100a06040d003500c0360025849908515450217a401035944015001030601181f50400300c603a081c0300402020402603450102040c0103090003001c1d8180c480c0b00d904580019001e10b41041d030010310b54081904554011a01800310788841058425071040c0d0b5000a912803642e251488805a1981000c008aa0041c000c21000c0005010b00d00744500543c4241c0780c100342d50410b010841503a0280d00b41c41d000c191150f001300300032603900c0100c4a07000506820001502c04020010601628424202035058420800c1a800c1a040c1c104401e20541008060355041c40c1c1c08442 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 690274163 1250 690272913 690272969
    0x91b1513082109180c1308030310081207020f060d060909061b0c0206030901061706010f15080c0d06080f0a20150d02160c050a0905071e0e031204 64
    0x50f1940004108118034802c01c02c11a696800c220892007a070700b0f20301041c10845800405401c10421134001206015200114400c014040e00c840800b4012070344c901d2008035814002c020020303206000707842c9c6050700ca4544000703c9034200e0a4140c240103060300d8080769805400301860031680246890180c10140d41c0700240b5400e812155507940341a0300e5250200102500302400c0410295a40c41c800103c4005c200c40030100315041c0d03000b03407000c0d6140042404129500d0f50100300b04031048152050910351004907194011075210a0300c1d140d6010010300d0b0700801c00780c0c208a841e445003500e84480b00f1f4000420244840c45180c45400d80002c0c1c20b84054945071820300300b500204031610040c0600aa4409015480303020140141002030128090414180542c0300340c40c8412540c0041c042e82c104000142c010341600c1d0f106102900f003908004000c1c4020005811422034a00146142d20740708000111201c04000c0450f80c0c4c40340010149031140e030252050303029131090709074066a1000d505007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 690275413 1250 690274163 690274177
    0xa081506060f2b1802330a0203040522240501080606130605121b031614040906090e070e0609040c031b0905091b15130821 54
    0x801e24100503d2403d004101e4603200418491101e00b040c5005039005980f01d000c45101c12040240d4000e2014010300a0b807480d602c284040080300030000700022280d4050381c440c1e55003001a0a9a01c080e015000c034294000d54214039440b82c02141c0b044600c3e9801d507003200d102000444108000c0c081500c13440b00248550140c0703641c4100c0894200300560154891755071044000d021285400301161998414100325080308001c6840820b0700a14440390065603503104420071f80d0304d00510790030203180c0c000740030003060741824180c10104070780010710a24504000c040f0004131680c640c0c6c0c8402070303030300680310502944446c285407050f440c144500014403002115100c01c5040310a441e400300b48104030700024800c0e01c0c00300c0c10ba100080002c07060f4404690200040482ca40110300b001001410345001424101c3d05a01030b0100000c080c4805003400c040305c40444486036028445540c0e260240200300d00a501c14400e1900054050008904000e11007058005e6100006524101d0703052802411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 690276663 1250 690275413 690275437
    0x307030b370e160f0503061806010c05011b180515070c170102190e01080106030522050313060507080409090804080d030e060105100203030a0b06090a08150606 70
    0x44452141c800030700355004000d41d072120506078903035169644814414419604410012400851800e11981c4490303030000e42d000700c1ca085407450074814002203440300116021a4900c10f2003010601982c003078165808141d511200038840d58101380200036803121800c0307180000c10842041e140703450303403410407a40a490000b040342c400282c040c09200250b800c4601e0403580c24280c0c4101203800c000650321b11a50f00c09480015030703518501d1450302034140d1011920028030000500e03418090303070000140c0341502c0607031500003443d645204010a000220504108509000a1410090001c04001001d100040810419002d9520041100c01c0c0c803610710b028090b81401d2005010b0a086600a00e007058000e4000a040545544240f410b00f449601d001003c00d41d1105418124034052004d0340c0105000c84414800f1910400044d4681c0f20052210740d03400e5441840c1e00040c0c3c0e0304002c1c0c495801016017031400c1d40b0b03200c4046951300c264165400000c09032a10006815103085400c072404800a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 690277913 1250 690276663 690276709
    0x306161e09090221011203030b0f030d111009030c050d140307030f090605070e03010b040605010c080702040e0a03050c070b0a09060c0c0b0d0b211921050307030b 71
    0x240440c000d400c40c40c40784032a0b18140c070030120136075101e61116019161022005003030509900c3c024084400802031071780034020407006070600741e8001c02d0100080d0300500305000c0200001310018100022a911001c05030324101500050590000401d44034500c48c80403248404a003520540300c5007852010041c4080c4100005a08580f0030b030802c010801c1d200c2c00104403c1900d580702000e40f00215241400122030000020242c0350034020f0b105842c000303603020042c641c20080000c0000c0d9100c50041c00d0840c1c001031503011900c1d00d500500861003900260b4031200384a1900a20b0340e171150364403000030b02c00c0c018040b41c2c0b20101012240702081c151209215030340b44c0038058486101000341a51841510003000450040c0344009004034001c403000010314007400d101300301e600d0001e1210748142c4001141e000c1a1501d0001c0e00c210003045082d0380440841c80b5203812520182c0825541901f485039101107180107400c00c010f540507121540741805140303080c10038403d000d4445240d10111240c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 690279163 1250 690277913 690277919
    0x509070e0115110712032003030c090d08030c070212060105030a0f061506020102090103060617060d020d06090516050f130b0d0507080d080f011409150306161e09 71
    0x26102ca00c81500180d42000c40039020400c100f581442c659501c100801c0c1c42e01118a0b08055010100c441001c0312100c45100a18207a1406a81c9000003010b5109031003001500c407656a5400b90061819a03000d40702907135a1400311110820360300410310807401442031900c2000c020300045a8941030f00d81c043c0007001e000c1c001d911621100384802c10152038403942c915041c0e400356904040720025100580016a690000400060464203668014000c00404240005284000041d0076030002c5088403898010b074403c4c00020445050884000c100f90324102e080f10070441c01180d69115030392401003580e200c07556401404040601864510350180100d00500d258020715071041031801d0001d004009084019a10940740c0040e54004001d160300001442840c81e030701c86901030f40000c2681100101d5407400250060307540444210a00c1442480001055030140e200f8040404400a089400c18145110020f003243e0048040c2c000080f0302c01c14800300c0034218101e0400814081d6256074405107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 690280413 1250 690279163 690279179
    0xa0305090d031e0c030f03020f031807050a180501060f0e120c0319140c0109031e0c090507081501020c0409150903050c0f0a110d0611040b09040509070e01 68
    0x8007001d0300720180b2007803040110303540c1881041c081ca91003043d19180422501340c1009000d6507400c07040107080600412046e1168030110080c5d135002000d0640000021100004032410603201f50480c81d00b0610100f00003803422840100090300e114803600800469880c0c50b030440e8241c1c2100902c030041350490407071243e98140b02c003a0140110b15601910300c1018820300080c102402040032440d462803000103d41805456003d004081310614001d01808444a0018208407224400038242400408404800100c0802c000203025400b4103003d40054440403200020704084d900400050b00c49000a000090800001c4001c480160014406240241d04001c081c0c030340c1c0c48045501c6040548102607841d02d5004440405100751906a1100d031a250003c1c40d14415540004103544148246008150381c0c0180c0040d4a005651140300c40070b00d4144200903080b07103000c00030814400500002d044050f035003c0c080e11034084406100b541c6811031896a60900d600441c4101140c420041200031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 690281663 1250 690280413 690280429
    0x120908130f091a270c090102010f05040b0402060c01020f030106111009020916032903192012070e01090b0619050307140a0905120f06070e01030b04020c0a060e0a030509 74
    0x180ca040030102c401083e014500d80404e20642d0382046210b40071807008031640e028047d1010034107041c0c0040141d407416442d410138400015102a008183c00610241a84001c0d0112590070890302d0040b5600d580d142d100420309441010920150b008102850140340305034007407a6003d07a00145448034a0f00c1d1900c01041c0030004042c16802c2c13550b01c82c01403500308500b00a119180000c019461900582d880500d030900c0802e4400c1d0103200380e440701e150700140801685100c4c2c5121f07085a8041c40e560300001c00c40841e0807000e201c1d1035109650001a40304075540c045030607910505d03010b1115000c1d520070b0062900904100c08210300c1c20007020300605100c1e501450f4004c805190808071040c400d4000c0355254401b103400d00014265120038821400c1c901180040d2420000052211400841006407181d201030700e444200422840e0b40e0f00745a110ba0006600a01d00400440d9105601604560741c0e007080030045600c641400c051150300c5401090480782c1c203406403550f915250034807040003102 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 690282913 1250 690281663 690281689
    0x6160f0905030712050601080f060a2d05070207060f0e0616020d060e120702010f14040521061303090303050a170a02070b06060406090501120908130f091a 68
    0x6403110020315690304010b5200142084a05410702d01018100213040540580010841d5400500080318580380018503581c406150071000580039041c0c025024480032401c158070104d0300000a44110350840e40c02140259019000c0b11000ca5a44006075150300b140340c43c040120340b01200104050a01c0300040003d000301d00071000082c0c0c0303180d0010301c042241803001e4400302d640b4012041d001e0410001540003681040c0614100440b50380001c095641c400140d00420800c91188980b5003424810b54016240050448002030140c0305080e415030306400280903d88146400b04180000b01882c01c1ea002d0741650f106814182942c03000d07946c6600c01d420740d008001104103d007200d102d00b03e401c14040c48400780056507401075800e0040003020040e00d4684169070402c01080016003000040741200c5080c00c00c80420a503401c0b91000400c103811001c0c10041d00090036444018078211030200f03551807003070700700d4001e41c42e0034134103080380c65080988014804080540c1c4451030001036002e01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 690284163 1250 690282913 690282917
    0xf06010501020c1e210c0301091106090a090c0e0f0a030305040b031906060e030606011d040e0307060e0a03170403050901210f020d11070f060507052106011106160f 72
    0x4d00e0035484003203080f0741210301400513100c3e0905203041e400c034020710a00c803daa2040f0000e000120440d2188c0190f401201c02c000e1003100e00140c2000c0c2502c401ca400b8000303203041c0c01c2c01c004201e500300c000303400100d420235424418842492042503618108448c101500c1d019650300381081d0601b0a03281070751740040c02e5100540b0f4841d82d0310342403c072540940d5000c3c01250390354000b2822400245490144090311090511603010740304010a00d01c800c0301070520743d0440e00450303607101c007075000c0d130561046100140060703050007620703585004005194240903101c0c0d40c403400300b1114031440040c3c1c0102a68020b000840801420500b58480c081c498034070908a544c07488148181140001101d01c1107503401040350300800c004015a010784142e40050840c0c6203080c3c0307040f511340d588050390100e05c00000c0655a40d8000b20b80c009104105441814070030b0502c01000c0c2091b4054422000e9088481034000744107006544401d2402042c1140551121051103403a00713243c0c0303419917408078021300c4141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 690285413 1250 690284163 690284209
    0x6052a030601030507020f0a0305130824060d020a14010228033605040605121507090f030302011413051921030902031c02060c03040f1a07020f06010501020c 69
    0x40311f0741c0300b40180c440c03a603c01c1e120f59030765500424a85000804941c81b0506907000082100c0b06132011300000c20390000848500328151b9209400030b5022814840003279080001d190021950508a103480c1d800b2042c241c00300ca901e5503102c0c032100d8412850b0398001e40342440e410041d0f0300180c02510301c1c7c8401d1054407006018050340000403c0000d0b078640c0182e11301140d81c0f008000b40d051511404000c2d00c010345130b4a4110701001241ea5131408400298004181204000f0f20a103209280742c001500b00084203152150b40c80c10001c0c0682541100c046000c0e59960108481d42c9250b450006910344c000d0203010703400c80f42e01c4c0310500c001e6071207400e40d200c6010b0725104031116000c00e600c0428070050b44000074a40981d0061602c0c101c04002024501d8910711316410032640c000980c190b00c000a90b003000d80da640c5516210030035004481c001440ca46990303a10540149030b910382244120441e50886250110154840f41d40781c0c002c0c455070b03000d60003035201070500b42071082503a080c071000c450b0080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 690286663 1250 690285413 690285433
    0xb07110609040e010209100206011d0901020912070e07030b13020c0c0a08240c0f0c01020d020a030c080f06100518120f0f160501030f0e060406052a03060103050702 72
    0x42c058448001d012059a5400102404245000341d0280c5401800b480140082d604000b0545103002c03002032540d01880041000881ca41001d40444081c213030050102c0c0c45020510403115034802150040c820415429000120018864410220f070514010200342224011071241d800035030001e814400140210031400100da00c83c000c00400400c2080000e003201440c0f081c203001070701e18101004480340c6000044c0704107250303440c0c16a680c28050515190791600300055441c02849004000d024460020a07000b00041d01907011141005064a9a070f40e2595100d14a007441c0c3c800f101e08982c0281c412140141c2d0340d122384040c100d01d40c1302c1109650802a0040010f00c3e900e110590090140d00004801110400034000150a09540e44c01400c1c1e41c07041402c001e10792085400b071181050780e00c01d0100390403009038000c45080160903044d69854101800c200c0060081211944200b50205103d0801c2c04110a40d203151a03290036031007411600c07804011006040050304007400c5110700207600b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 690287769 1106 690286663 690286669
    0xc0803060f03100603060b09010602010c020a17070605190e0d0801182405010306210204090f021f1b02130e1006090f05010f0b07110609 60
    0x11030403032100c07240442e1504002000e08039003141089000024070035598031010250000ba82d220549a880301c100342d00781d5000d1040079006a100b00480008078030b0021140d58802d0940b0744551825110761118410b490042d203800c07805805100e5107010f00c0030144145006010964050000a5a03000300a4201603052146203d04440409495029285076100508103605e484d000c3c00740710180c0c070741c5100d43e08160148034046490558081000038240d03a50a07111919121f00c0000720348158240005440c10340d1003202d100104442c01d00041c1da500d03100340311441882d03c0451101c0c41c81c170070041250303203016640c00c1c94821020001c405a140c102d40048040004800420303c070450031003c40c9419481f140d440511454014081032801040d0007480b003400f10000144101d90300ca403e0030000442d070f441003c04842c0e0800c400c1000cc0c150f20b1041c05250303001400a82046000b0000c = true := by decide +kernel

theorem cover : BRFrame.Cov 690107913 690287769 := by
  have h0 := BRFrame.cov_init 690107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 690107913 ≤ n) (h2 : n < 690287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
