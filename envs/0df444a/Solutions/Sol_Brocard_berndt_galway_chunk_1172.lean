-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1172
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:35:30.677921+00:00
-- url     : https://prove2.me/submissions/be35594b-7755-4319-a648-3a55d494a308

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 210611510 ≤ n < 210791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 210612760 1250 210611510 210611519
    0x5010e12030907050105071a01060914030a030906030f0e1c080f0105030a030c050f060a020408010b0a030803060d020402070501090c050a0b04050d240c080a0b0a030c030b070507061a0109 82
    0x1030803203118160324001007608500d08801140c40d948888019201e030b08150900e03881804100800c94000e01c450b6440200031801c040e00d40e0b0110740084040ea03c00e030702c2003a0b004002900140d0000840f000350900050445880c24041c5c040e1a0403c1501781c0c0340071708500701a600400c01d00c0501c88003110b0392131110325996216002003c55007801801d03071507030140307006400207446100c00d40038103407060041d030781002c031441990b51500d403055503d603e100c0e40205061100050920611354103100c115040f8484070700d191903064840c0f10180a041c0a010401c540d9004e54503036030122040b00358048020004c0c03003c1400d0000c00d9040b81d01502e8480d070725654000449024050035101a00e200070300d51510404241e03103c1e818030048004400e0800c007841602000c1c02414401c10f0003840c4251146082854203d40b803a040741c2100c0007440c8074000c241018004100d6003001c8000740d80d44003800c80c0c240e032600340c1c064030a805101c00c0142424104003000003205041d5000d42a800e40a0b243c0312511610b4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 210614010 1250 210612760 210612793
    0x30a02030106153506010c0c0602060403080703050601120e03040e040c080c0a1d060f030604061d0708150403030b090a0f060b03060d060b061306180512100209011b05010e 75
    0x2c2010350708120707130002d1184c1d0071030302c403800107508402c05051a41144445030f50f01d038180380d040c0c2d000f100540c20200401049c1a006501194000740718642003199150540018008070300100d507841c0c115589a0f840c2805100820880380a8091001540940c1c9041d281c0b2a0181c60140203d0b10140290343c0703858507070f0410301d040c0c405613190214001c0c00a00d8031784c201900c1c1c3c00f0007030035958000116100d0240310340b001d00249007e240204400303e080030404c0b44080d26841828240320b0184c0c801201007100c01d001107040d001c1b41102c1c0700e0313600360b0361200d0030b0850290401c68905584040440c0c01d210101100d9440007056444445043c803c0c142d0328403e1800601007103d04903000090380c9032690004046034012080c25a00422090908041c071040c0c015044c11a00141c010a0752200810741d914070264601005000c201d46080500901d2050240c503040c074100255040e94020032074420396800703408400408801c110450381100d0150504a0107170400903880c01050088068200c03602c441c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 210615260 1250 210614010 210614057
    0x1305010203070209040f080708070f030315150c05030f041701050a090f1101090812090a050303130303120209100f080703111b1005040b180f1209030a0203010615 71
    0xf0002c000d00071a980c0e83d100c0305100e0f010654200c42c3c00c1020050301d0005000c034005801c0c554055040f00000c090540b401801300d80507030400c0050301c2080c0c0f800b00000503100d0020302e0681340d01e2400748070604103444c225103140210400d4071124000071901240201803511500310300842c0100030301181d11226116403c176070100300c014141408176001800414828404002000c40626041c07100607542ca0026041586a922054000400054842c518600304500c08082e103c21406180340121128401c01d1040491100a007400312000799500070303030003542c10364011050240450b0b2844071864002040c00c91504c0444021824480c0411082c921901c2041c08000320640c2c0c9074039041c1c000302803964207130b504140400b1521030200c002c0c0d40550341e402450300441c4120340c0e1704800d082a0000628281c220007401c006c0c2c0d8810541d101081c140014145118240d085007030783c1d91401303c00401c1c00c12902c1e000c065015030805100090048840f090006058441d64030111003611124203082140c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 210616510 1250 210615260 210615263
    0xa0b160c06020a0c0606060806040f23100b0d050403110f0a061509060305030306030d17040609152306010c02030307020f042a080a06051e121002130501020307 70
    0x40d5602580c600103950356008150810035820040703800e80307136961130308140c44841d004180080d0014050041d54103140c0140d1082c0d25a0301418864202c983c466000080700c400c2003000540048400316100700d070206181c0f03014001c075100d41b55a55002040300d0024180655044000a00c4100ba540000c007001c220950808802d10240c10511b1580d22064050542624a40355808150f1320020b013a6589110381d0008500c41c0001e540c50785844410181098801d0f00c41e8018005100310326807000d484d01c1c2c5440e91080c1d20140010300310141d07050074001c5191035042c4003030b21458010382020b01c034401c601030002850f0904141441e955074000440740822401002901640244119001031800448050220b040130b07100003007034068002c3c004550495072207141c1320a01008075042c1710035441409554011100c038000e0005c0d03882d0101050354108400d000200c1202d550704400c5040d0740c0e111400d2007082d855070464141200040c0d50304000d50001000184150303100034000b8413940040241ca5415 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 210617760 1250 210616510 210616517
    0x803070f060e012d052203361410121107030804030207050a03020a050d020310060906050102150405060609090307060f050406140c1e04080f0a0b16 65
    0x400a035140011400a000100d4045441d804a040101c03024030130f05840c0b6004980c1807070300c0241d20031000074194203403110300c41c15402e20b800c02c00e269145070b460310001a0111807103a4401d40c0c5003001c40d80c080303041c801d0850b00710741420380414410340d00350602025107280045404417a03840d051040900403060340b042d04104c8031800c1101180c011030f45240d00841449012540cac1388005004210740d0b00403841140818000710501050650400080c8081c0034140d07007500300b040c2140c000a550b4821441500e12a0115a084400b10f44040c40f441c107500c0b0f5030080070300c4843c1d250b01e07800d0040d1809014440c01071044540c1d4000035080800d0041c001d03600325000e080e2a40720082030207034685005040d410148003c000400004130648100402c0034903d460006c0e1600700b07885d081c000d42c0e00785807103c040154018280180652a40b0807034104141c5580e80342d41800d00442040c3e01c80c09107900180d540d0148000d14506a400803841c512840d1054076180300d6035907178204030030900d8969007196000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 210619010 1250 210617760 210617767
    0x8060703050412050c0c09040b07020f160306111608030603010b03030319050c0c120306040c0e011d01030908070501060915030b010605070c03050d03090510020a05071112060403020a110a0803 84
    0xc1c28044c0e4018030401c100c02055031804a01c40b0302149440d001901c08603541c0320135204200710780d6030502c980d402c49402c42c000b400c07954109902c0c03107404031030318000504201e40d03030303400c415016600c1c0d011035102e02c0c584801e0317003e001000c0c00c1083d40c0703030411100c0c02e01035424002042000d150201c1120322503403104004000700c1510300c0c1510010b0100500c04000384c80d04000f9010746240c204401801c100e4400030b0341e966403034100300344801e48802d80718030818807160040a03410b6a0b0003100c0a0000040040981c203404490750048001c3c044200000d0440500021410240441074000760709442090101384002d00c00404900080d180520024055a482c60014406c00d0312400040443c0c601541642c51107589944907241001d10880c000d20110341d0b902140001c020040c0030b40c02c05080138141c01c50900c1d80c0e010001d00350307100b28800108078603240043d84c240d9071703528407000b02c0540c0d5080c12200503281504c1c0295482d250700d14240c3c2d140d03030710b080c0781c4480d40303407001408084c5c2e0a400040c509 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 210620260 1250 210619010 210619043
    0x7030b1605070f0c0305011506080a0509030904060e01051e0904030c061b020105061009060e06030a060f080303012313151a040e0f010807180605060a09080607030504 73
    0x80d500001030310541003200400c245004525841c402c007052501400d00c42c20311a185141c40ea08491200b01820702032024000c041140d071b50403066031540035050940120380e0b0754030304000604500c943d202d807546c040c0c036250f4042012055811001e059550555650410f02d401d01d10304c5000b02600464250f004160340006030010f481030910581180c8a0003002c91600c0d40144a100c00803000c0c0084030050791b5400c02c211a41c0351801c00e621445007903007050004107040c002d005007502d038400c1600740140000408902c1115079039000380001c01c000724100007440d88424840d9221f510a03c41d1204050b001c41480341103000721040c0c2074210000030b1003c040c200f2240c0c44107002c0c080520040c0c0d0340a15880002405c06104051035150005895035542d5a5080c0070750010740300300141043c1403c000c440018008501c3c005009400d807040d01c3d5111481c9140358954401500064005a402600200c0c84cc0403d071341200c241001c0d2010001a034034559161101241240c0084070003500100d407140e014034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 210621510 1250 210620260 210620281
    0x61f090e07051c0f0b16030509280f08090a0605040509010909020103021306030b04140f060f0d15020910030e07030b0a060807080a05010c0801061707170414010e07030b 74
    0x40c00e441d0b91155442028144d848082d4080c1d62041e00351030a6600000b08101c04a218000540c2040681030412090a01c51009941c88900d00c800102540c1591f4105021021215001d00d0195200701e038003031001d043c0d24241540c4c2d0410140103016902d09103002c00e070280650195000e485018180700a42d80c07070494000c025149281d0280d040c140c5c03c00c085880942c1004811015000310380340821002d0300071040c40308850034000c034102c28881c40000c0c4140040951005c94000c003040320780d00188147c8400240200565040090911100d41e20140814182e038015080020381101c0d03071801d903400100154251150f2560000303c40d008200c0a00004895800068001e10030306d4001400b1507c0323144035460007030356800240e115844103215030104a02406400b03090807080c0b40c210015490b00e01e000d41903880c490b025612030041000060740652180286441004a400010096007054100b2640078004c000c0c88001da54248102c200060f28005041801c49030f000090600943d0b4440203030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 210622760 1250 210621510 210621529
    0x9110a08190e01090b07021902030303010e180a030f080c0403080d09032304050f0f0112091e0b0901050a0c0c021201091b0e130312180203061f090e0705 67
    0x1400312a0b554000080405003441401a05845009526000d080c1810040c3c035080d03c544604e0004803508041200503140442a24115801c03e06588034540301e007141801104480e1400400038400c48a00c074080c0b40d48100d074205014880c0e1180741080d100c1c2084102980301e00d00000c0d1032198200020842c044d0f6590042a001d170207450140526004480c0c82401c2480c0780080c400c00b550701050030b1106144c81c41d1101d200c45400c1b52a081c8601d01540080d11000e40d41c040a001140c0d02e04644040c4200c1e045103400e2010756080009000045142410720704205403811445580780c9000106aa851449480d081d81806c3e101d501070030075541c2c20040a1140c8408040055480340b841c5000076034507104444403601c82140301d246883c00d141108082ca0b000400e88010740c458940c600000c01d8202112200c8194492400304030442240b9205020740d45840000f5058850642009185008998060025015031422018065640440c0001d8440706a0700e40542c0d0802c0800700039514018448 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 210624010 1250 210622760 210622801
    0x1b0a141b09190501081e0102040e011514070303020309010b040507020c060703110f0a0210030203010501212a020d02210c151609080114160e04051009110a08 69
    0x19141d54420307802d80c440658500ba4001405540840321141300104070703010756806c5082200c001c50605190441800100c5010300ca074440040404002244543c031810210b0950a0030501040d41c0740d86a01e401002075008440d0b42c0c0640d40fa200c5000e00781d250502489010320066401002e1a0704440100316503a48488404c40501c4411001e1809400040c41003c12203400b100240110448500500001c003508480c2681010b10420041c40301c0c0e0b8002428a1541174501190703800c2d0300300303140300c10024000346040d4401e0a503082e1245036510510b88100090556513820b64443c10030001007a0303a942c2160008190105508030901c6000d107040010b003001c14a09002c441d54040d6100c0802e84d034400540e42110203141c0014544022074000c400e403001080303558001c03c5100310741c80d050416180302624040c030380721129120715030141c800d40e0b888420800c0200108958140311010a801118601c2001843c50900112205400c4c3e50019204079420649131540c460b954130708810000a0b6100c807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 210625260 1250 210624010 210624031
    0x140a0c030b0a0801091703040c140a03020415060e0d020f060c03070215040302150f190e0310060e06010206060d080c011803030c03050c040602100906021b0a141b09 72
    0x1060701c0c103691500300810003840804000070b0f0411260074504081c503140c1c01d0740303040d0380000c0040c4000103140740604400c80b004e180c2c02480310301d00700001424000c201e6001a42c41803c140500c0084024100030100721001d41e103528143ca140039040c4016a402070501940c1711102086941031824180002c214890800742501c2c5003019a500252408401c1c4440c0454070340086401d0046081807005111040000b034040c80c1411900390140840f0700c00c5d49280c10b202d841032007541840c00e00078514a01001001025611341c201441c0711000181024401c0e8070700c411b001c070049800d65001003070b45402810094501641d260158859051943c0308a02c0b05045650740d4000740c2461189039500c4140781d1090b078001c55040010311008083d5880a4204800017104200400c80300d80c0006142041c403105002c041046241410a00000c2c090490301001c06101c0748800207005d8000f003601418207110f811160b030b8603049652450382d616094601c4180300c5001f00c48210f4146401e4041581c130140b03014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 210626510 1250 210625260 210625271
    0x7060b0301050f0a0c0c0b0403050901020a060204180f02040b0a270303030e010f0c0905040f0617010b03100204060e04050a0b03010e0c010219050a060e030f0f030402010e04140a0c03 80
    0x4020a00310b400403030b03400141e00d4012052100400160049022020f4076180048450803d6290021510000b80008042c440001030500c03040e4000c2c001001c03201d4010204540340d5554208000300021380c043c0101c21685000c000024640c003a10a03107003514070700c504043c18110308903020f42d408004250f810a001e11010100c0c14159054081513002e54400d60700440c00450004409082d6848680d50140941c18813910102481d40a088881181d0f400c070780c04111021082e607200000c04180c0c010400e4062216a00c4400400541148042404c2030301122410701350846114200d020702d008500001c2c501c244e091941d450141c0215401100004001a03003e0900000908580340c82c1013031500c607084254424515a014884038480c0f1004034118407913406130307035510341c0c664082e03500060900e983e9200035043c010081003680c10401103002070590780c0c1044150b04d100c68100f00c80480c005100e605946240b0704090144059417929080008202e4403204d2a1201500d1806002d400f05030b0340c2e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 210627760 1250 210626510 210626531
    0xe030405190e040c140d030c03050307050c06040803100b0a0504052103120a05060a030b0f100302091008010f0207030507030e03030d020f090a1e031101020327030c041a060706 77
    0xb01c2c02c0c42c021489120082c00c5207262070341c0245035618100aa074402d2002c80542c1d00403a420402a4201c03603450314017190340741c0d154102500c46009250044405d031060f0401c000800410130b00440c001c41030070344101c40e580c1c2c0c0c071040c1c3e041c1d80c411301200b600003903c240010892801d00c80c460f804902511520450f43c418501c03d40c0d49140c1168501c0d43d411214175041c4503007001c0f82d20070146c008a041c0c1d2150251401d6455090030450060718411088034070000040201541c1803549026543c0100b041140d81081c5003220440603041c01071108552034030889035030350303901c1c4e108503464030ba03044d11410308010860710203441a407190f490301078250004100b41c540e1050148010a8011048500113450388801300a0090034141070b0803501c9694a49040401441c2d15810340304112680217010b0b21f00300d081400100d066000b0310710159143c06071030a20008088080602a6040b10150203d6821000840030081a0f52071002440b041040760700284c03006040250041114502800700801d00e03a500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 210629010 1250 210627760 210627779
    0x15090a060f0506100908030a0c0f06050c120a090b040b1005060d0603050f0a020a03020613030605132006030a020d02041203030603050d080f01061d030114010602100e03040519 77
    0x14014001d860668801c2000303911314111280b096501d0343c41c80d1021a4a0400b00c1640d560700c1181d1048042c42140004071081020121246a0080d4044401d00843c280200c1902c1580c03c59400105030b40f4210001030ba02d00b4180c40384000035504040000c03120345594032912010720015002d82072f800008500071450303032a142c0040c00181880700000507490f2542c2082801c14602c02411001f5402042d140000740e503544140c2c1003565011500c6075659038460305102441c1015900080200c0d04110070000414103550741030400901500c20f5907100540c2200c4c03640a05640c120fa40d034054000c3c4045104030a03d94090071044c0403202d401440c00d901c650780340008000429086000944481080c82001414800307000c4d09038050416130301608100756881c4150405008150800c40c1c2d488800c00c1c420810480c01d80b00c90400380c000c1004000817001c1c85507000c000d0054001612400c407a00c80c00d020640f0400140d00b840c0c6001d913082c40d0810042000000801e642c1c049200801d200200713010b40b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 210630260 1250 210629010 210629021
    0xa0f030e0714010f1d012001050708060a050d030c08030604140a1d0a0804051c0204020c0109030e0d0201120c0c0b0108070609060e01050a140f04060815040e15090a06 73
    0x10b20301d07070030b105115100001004d00000d40506020060080e80a000541e0903103140500302409003040c60140b4400e1012030740c0c95400c1141d8041560901c4140014640c20080c040e020300010b50f06424031645a40600c19549110700b030013400515504914004110302101071900304400a101040d4000c500c009610301d0130b0242e90304c0203203640d0b403c86070701e030b6140c45281e0000300700f502c07406481c1107505920358280364000c511500380260031003a00060300c4200a000070650303560080c000c540785d02d5280302c03090007850405000c03008503100103580f09172440d10170500b914417076059503001a440c8482110308050136250280009100c82d0b058520001083d081581340a020610000c214a92030210010100c5c05180e00a070f0038020741c0440e1044a90f440400c9881103140e9003820b01c150120110010744c188114495468550310219010403503c1d400003140740203034942e912403400b0300620030410080340c40502c1000c102d9844020110610341410030f00e00d900c44401d20030786414a14540310710090380d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 210631510 1250 210630260 210630269
    0x6040608031803010c0f090b0a0e04020703050a0f0504050a0909140a0807030e0d0305030106030b0a050316031a100312020f010609050f090109050705130906060f0e0c0c030a0f030e07 80
    0x1040c0b811118040d080901c05d45e4a02a4245821414003001910150004040e4014004840800141d4002e11806041c885143e83d502801c215075a50030713420024407541182454000041c03100041c1c0180d20b00c104251410380300b00404c201c0781540341001c65030003058040d408035542824070500d042002000d0020102d0117004544a56a0b400e15242c02007003007030906611441040c900094030302181c1d203d41501c0c19211141000240d880d19080040d10040740c5600666043c03152640185400407915004800c0328800d20b076641240030121030ac511407407012102c80e4418848900c00300049032554920101400560044d550031000d403a2000d429034644c0e40020b142a40c03a14140078241d8001d002043d400403c1d03100800243d42c1d16a5000d40340c00351441020b00ca04030381c1004140c40c601d40d0303001c40443c0d0b40c0210200503103075031413409441d840010321884e5021a80c040001d1480c0c0c0001d0202ea070401c001e1005145402e000c80c40c03c0e0340d5540450048020980d03610342c40c0f101520200103080240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 210632760 1250 210631510 210631537
    0x2a0402120f0109020c0a0b070e030708071e050f061c022b0c08072006040615061805010315051905130204121415180d050c0a03080604060803 62
    0x20315201d080c15000c4003040c1d110481c0c184c03040101021064000c40c440781d500d94807680c1c00113981c445003012100c0c00382a00c0380d65414011100d00042150b030025070101150441c0d2480003101200c3c44400c044202107215554100390f000b09881118a0620f004220312098100d441c100344110901441c204d03080550712403420f244071101803c928402e07021080c00c8980700c620500040295080090002601800700824051607042c500c3d010740303104800e1131705078081c082281d660b403600d420000f0207171483c8600990507095079140898154402c4481d5a0580116011030a01c180340600440081c12410640d0800201c030b40c20105880e41c3c0c0080c001e40c006441e02210004c0b80c10803041000d00100381440d91411881080200482301030f0f8010710710784a421031034088902401c03121060500003007407038030100c243c40b01c001c00040c60710a039011201c0413081012200300040d0301e00c040ea030911505a14401940c012200000080c0c03059808070f0303004002402c0400d0103540e410c429403450b00300f01c801482c1d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 210634010 1250 210632760 210632797
    0x40e010b09040524150c0a030512070801080d27060201150b09100318020306040308070f0206040b010e0403091809060509010b06030c18100908010e0105092a0402 71
    0x140c0c90305010b0140c001c0d42da0141004d001892104841080c041c500340a400b511000350001400452881076400c1c500040e82510702080b142d150007845c580c041c05000a012020b94042105c0c02d00c030b4030505041c1c0b540741e03000300403040d48180207982c082c404007401c0710405800e0021100203854007121400501407070f000440c4080c508103c11204078410b07040081294018001c004180e500e40c03490282808450400160045244800c620780120030200a0b40502c2400180f00030180d1060b8505d1103aa01d0350b94554040360206001c070b81b202c1098802034a90a0b0560051014641034444a07030050722904003440102d03034806148042503080d141c0e8021680d99030300078009028a034040c5a5118824030300800170704c0346032400110640000340c0a1070350100c010840d070300f800c402d0b100794040c0f0b06802061440c3d0910704420040c402d10350b40c041d1010310750030f20034002e100e80c0f01406254081d01c005005050f5a51000e81c0b076034101c014000303203801d416100010706e5500d40c80d984002c200da8040100e10400c1b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 210635260 1250 210634010 210634027
    0x105070816081201061101200a050405090c0c070803030717070e030d08150a15030902060c03030108060601120b010e0f0112060b040801060602121204020d0614041b08060105040203090102040e010b 86
    0x281e0340d424807425419034102122550021040195141d4000e1020f08068927642d42080845440c040c1c3c0e0483c0d13401c0215030003400380c0d00c030a110203011240b113030b6012075400c2a1500c040c507032030b80015209040841d680f0218400400c40c02e01100742c5c0702549180c400010456480028605018042000e010030f003000203100d0244001d00d01149964021f4aa00940c0d901e400390310070411084002d041c1c00c0559803603840741195662400c840c10030203002c0032240c90b540c50b0300842d620340405460150220b100040c108540c007010380a40c0c1c1c804401612403a14054030072080c05240c140c5489810b0410040c04403081b29160540f18100142c070480c0c114513280c030301703008002d030840f50242c0119043d980f1400c200c10095071040300300d41041100708146007030303600c45101040d0003000c407580c0105400d0503c040c900b55070009400d114820f40c01003600404825403003520400c2103495010711222600100014805410b180d0011600144000001860190b13501c081d20401c1500717801514690300c000036500b8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 210636510 1250 210635260 210635267
    0x3060a0f0c02071d1f03050705180105031009150f060f0e160f0c080d0c120605010f1107080f07090f060b0d15080304140307080309010507081608120106 67
    0x1c051035000600d501400d05026000552070780030301c100c107004082d00141145246072200c0203032140c1c0603540d040241c0c0760714089441d8116401628010312020750b4000c80b07189118072290403508054041d00d002c41c0300300d403800b0180200da101607940c09088044000c0000d6a40b2a00c83d01854840000500900300440454402d180e9071100d45c40c00188028404284282c0c010900d005485040aa181d030350071900171340300c9a500000241007800b000c80c0320486002590060820070358665a0981c8002050b11030504844003401201e0004031003101d180c080b240545506102a03074118115518540d6808e944c91900c904100c08507016044140300300311101e618094084002068075040c07003c54149409100c0f070740125542c14000d02e8403054540302c0a24403030043c001030320984044d01d07a629101c00e20400c09072400403080c1d0292140304400560a0000b0040d40c1c2e101170169501c9240101c0c50301c80390215000601c5100041c122001030341c0014003d8001080f9034004a8101c2a4961400318044d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 210637760 1250 210636510 210636521
    0x6030b090a05030301050d05250501020607020a0305040612110a0302070b130203190f0b0123060306030c0105071406070206061314040b07090509090a050c03030403260903060a0f 78
    0x1205540e00541d41c0a0014502005032410b4a4007540c000200c0e103d24245186000b00c8486498903281114100100041c03007014000c054503000c0e0200c03282500e40840407079807441d041308003034001f0720b040c00103026181c0f19008502540260000c040ba4503008940d0200c02036102580d000c0220350700151300c508110001800d59801003c02c002c25000107201c0d00440e480d003000c22004080c0700411443c0e04100980b056400759100e4003e82c0c1c41c200c941c4c44808006a05400f2940b1103041c103203841c4040782624060040b28400c20000e401303441050000c1e00152015003107202c08540d421907412204203412000c00020b40b007110581e00034400783c102030083c40000c0e14501140350351641418140d82c5d21520440150350420b1344031460703540c01e950f203250032070300185203422481e4800e80d02002d0007170a04000611100300c500900c02d4443c04800841016540e100d5840014100a0090105c02c6000001c9141d4402c05410300025441c0240c00c81c000707401e25030f048a07030300c0141c3e0343c5010400180a440c400d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 210639010 1250 210637760 210637771
    0x1902010305010e1303030902011e0804020114180409020102120f0304031209050c1516140607020606090a020703021203040614060a0b1206041b1d061e0a0c0c0906030b 73
    0x600c0181c1c02d202501400120301404085d0626440d405000110391090003040000c0405080f58003003941c0304e01c07000b843d41e8010307a410390000c0c0703030034207007007580e01842c001c54009003102203214100603021ba060001134003003100d0990641c010b5002d054020040c0d4001044041c1542507296501c0c0b81c646070240a0101c01c20110300070b945001102400104009801038200178200c0d80119141c3d043e40c15040d551058100d503800480c2c080e030243c0204103042c400000d803444004207540442d6100b90040381e4a00003151026442907507030b03000c160030005690060a4550207441950740d691007030101010b0f02d91041d9401c82c0c00980e510440c03c0700480400c901504a0300031030f804e900551904240d0302442c040c06054000303d051060102d14299280c0c0d00c51640c0d40c2a403500c04000708034006000d44000c0024001c0c00001c43c40311007041842c54850101e808e00d00c0078007a48400c080f201c080e000c0c210341080543e5414842100d88141c0410f18240e17290000700310402c1c002c11042d0a601d454007030001e0203040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 210640260 1250 210639010 210639029
    0x41701050714030f13050115090b09061f140307080a0b0103060608060f0d0209090102090118030213090501020c0609070f08060f060d05030712050d0605010503060d03050f0903190201030501 83
    0xd0b02520540740110b941010300200780f2101501c500d08041c3e070703012100c20010915807800e00190400c0203d91160780480700c02020030000001307500b0910600090032110181c0c003081e03084a1851070f035011000c0800a80c42440d140c40c900e0765800d1040c0d690381c015115503011400710000c02481015a01610100c80030a103030911860346880c0003c0d0600c0c001031300140c401e40f248400c41500c0d0b2071380d80440c0b0358950003c1001550341000c15200d4002d5109803843c0d8006916003c0307a85040b12400084c008072903000c1d040f01072000f94000c0b074400514114800710b481c0e540811070f4041201d400c000007809401000b0141c801c581c03401000f801404c45951101c24240c20810400588040c03101c40c9039409482501d6180320080d6502c2c0c22425032007109001440200c01c0054048003d038008050300048049800801c00182c0300c80040d1024041200e4096000040500c00c500003480b46001e030204c562000c4a1a0038129500000303400e020b0080300b10000254142d41034415036a060045500520181d074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 210641510 1250 210640260 210640277
    0x91222052707020a0605010905010302090c07121409100801060201062312070312180501140306010c020301060f060c0b0c250804030c0b0c0d0315210501020417010507 73
    0x40404810501019011a61540c0d0710300040310640280480a01c0783c0d4040c00402056071107000c9540100030171701041e4010443e0710005400010500704913844030303400c8034071044001082003040752200c4e038026140003010801d110742c0c005a00c0c1c201000070b4581c60341d110f01d45698186032000b030850303038598030180402c03e5507103117a00c09181a49841c802000305072100d207110555603105510301181076000400440052900d0344080780c2c005400c54900c00d01c5c400c0b60b2a859a10341c0112600318111003000c020000400210301c00c0d40c060380341a140203101400118409030781d960403881d251640d62110010440029107001001310b410b00442c2d00c00808010b0a0600e4041d00c4134a0b240200581040c05e0f000ca50810407050084141c2500c0065520034205583d03985c807035940520503000300c4210f8103540b042c070784006e0240307000c0e020f603400403034020b89141e08442c0b07001c49615070b40181c480130105450242d030552000c50001c0c002840a004000040c00500c041c2103e5142100e0300104903008110101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 210642760 1250 210641510 210641539
    0x914060418021c0b152d070c080c01080106030906060e13020301180c06050304030306080715030b0a03020619030609090305030714030105010f031d16050a05180402040509122205 78
    0x28015422a096450205c0c2e40710400151010700504a4003109105004607680b24544100240c000b041018803d50320031010583d01d09034a681e030700300001014041100b07640148006442075100c01c910502500c40072404a81e170b81d210300c005800954903110811211881d4000b5400c09001c6c6212120100c80c1d180301860003a01c42036010074050040c0410060000302003800d01d48690005405480e800742a1203045969200c01013a24107444961404241410904080f0f45401e00d034941c100c94019100314604100c100140c6031083c4852004030034150303103040100b5000e905201e010007980c400c4e215141c0c1c80c00d01d0500601421590462400740c080b00300b0050010740d90040f48030314070021508010030b98180e185164483c80b010141d103141c2c544650341c0501040c030070703400c00300d01161000d0754240d6540343c840c1d00748102d01506600340107980f00781102140050034985d101680c000e03500415610b0901e031144041142c2e46c0a495100e40e203403d41010740c001c402e1414400c4d4024241282c0901e03214110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 210644010 1250 210642760 210642769
    0x1803100c18140603010e0405100e03030601090905070e10090b0711031c0e060a0c0f0c06110a030507140703150501051005071e02030f010204060810050102010603030914060418021c0b 80
    0x14000c001503a410b20011804000c009c000d242c1c105002c03480c0034441d101040c039000d90359170021100e090006010b0500018a030700944142801501c40b03a0748c07d902e80c94802d0034090340c24a50852001000791a075000544038000300090030596104456080840704c0082c10180f51000342544400b40801005d07814454a81044d0300170312520b010b80d869625200b5402050303034001400e00c0050f0904250340d50810420014094000c00c0e510342d6244c0e0b0f01c88465000000751358031001c960050200b50704001010100740948001540c1650b541c0803118499240c1e81ca140148a15074000140291600014405440c103100745150940341803a10b07909041180c0c17a1010010420075542d0f80d50552204100d0a64800f4007210003010f50140082d99140d50b2413000270108001107820440d0101002c1d00800c03150320601500c0c08507501640c0e40c41a560400d09406039210240c2c0f01694801010040003600d4407482184c0c0c2050448154010380761481d00c4254104554202584240d02e454840f604031a50744 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 210645260 1250 210644010 210644017
    0x3040303090c05150c25094107030506062b020c1509030a0c0803180d0314070804051b03030d09060522081803100c181406 54
    0x101450007064010503420912050032040e04600d8001c41c0003065083e649a0307000040c12804a00001c44549803042c1841340400e130418001d90a10407170281040003055055008504240703c1034851000d0141c0752000c03803500b0321208404110204900309400c84050602104585c00241800c0a000034070b0480b00092130751298889603088540d00718180e00d03081d1082d000560760040f2842e811595000c008000c5030342d40b160004144500c40d484800111450340100a4880900003916801120495640d402016800080c111919060148050800ba400030020101c50794a1602d00281d403c594408035200d12800821200600c814a028000020700000d400360400c104403410340c800742c24441c0043d082d84501c00e0650390341410b001611007840007070382c0440e028402b078801e108041d0100190745084902c4074000a0000e07142400840d1032195609a62000000010151075003658401c00c100101e6400d01d043d05e00049012030780e20f11050b010b924840c0504442001c002c1251a068009440d0f4030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 210646510 1250 210645260 210645263
    0x151101140103060c0c050d050301081014060d030c051903031a03100c0e0a0e09070e0c180a0302061207080c041206020f0f16020306102313020a030501030215030c0304 73
    0x25071325001d0f030403102d21612820281035405800d0390108024004000c0180d0421b0203542c0050003183c480c240d004441d4816503421108050310341525541700000c101000180c45000c4e000c0c00100d00d00180014024000050407820000c0c030503080702e031103042c010200e80f03041d014403038070803e14260010a5900014103401940c03212402280d07029034114110b42102e0031001c003c0d0014000742c07002c54040040c040c210f205040c0704007220781c0307140d8404104a40c1c0009840340085070800f0082c0ea08034070304540180802040207815000c0b4140d81c0c1d404120a94807007007411481e48130032001d04c0304d02a40410466000844580654101410007094031100c65545200600059000590045c1e110440c0e040e0340c02969419201a25455180002500401983ca089100e030150b1400a01e60000203c80c0c54152003014544c21403038643e0240a183d43c250041681c8da029114800c103e102a0107030004102190b0140e03000b103015491071041c01803250160700c40c0031444100b1f2041200d1b03a01c809043c3c9a006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 210647760 1250 210646510 210646523
    0x120303162a0309120302010b3a02030a0b070210060f08030d0f0603050114090d180b0c0a0b1602060a0c0807050f0f0d090b0f04030e0402180901151101140103 69
    0x5030741601d001c2d0b0702c6034515400082c0301e1200c02c1e450310900d40c041d800484d0340030040d01ea540c00a40c81458101c0c251440f500120a070955041100c0c2400d4541d170740a90f4041e10250854600e10301e0364075005900c4604980c5900144d0024502ca09202c480d4040c1ca40284030401d40d8030440d0b41001d9034207840c1e001d01240b00c48003666030354100d0038543c2c0320b030802002950404001c01c114842500304065400702250003000d58440c2c10300c225160f0744501c1c1044600c0401070000c0c15082d00381021002250b02ca80002c141610440c483d00d40400e07652441d03c2d004080b00c400c004180030351610301034140a002812900c81f1460300c801010f105800024a50340800305240c90f43d5625000c80030882580200402c4141c1700d403000c01c620950003a640d000d1200c49009231b0520080d6940c160302911880b90444004001402e03000741e001080c01d09401a107400100180d01c050f0344480b17100445e43c2400c09030300c08000c0c1c140512071f15081c650080052030916082200a012070103080b9011a0004018400107210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 210649010 1250 210647760 210647837
    0x180315060d03020c19030506090c0607030c060902041b14030c0306010e010203070c06051209010213030b0a091a01090b0604080604031808060a06170d0e06031512030316 74
    0x1094402d1207041c040d01d01c005c16180c544440e014060017081c0c0c2c00e00040707440e4450b400104140910001e142c91016200904051038907001e80d0742282c41c10380c0034604032071540c0c550039448011798880c003603003c61400d0090419122081c00178014181c0b1034502141c481b1280c108240082c107011001101d600410a0070600c0001440c000105c0ca5407141010152a40c2c0e1440c80114142d42d00100401c040450783c03401030740c15107031003410f0383c00c07803040414542c1c000b52000c0c0200001100341e042c403944258542d000003074034107550301c2d1003910603010b2114036100c00d04d2100511010005100303030180d50200307441082c102810889126618207001c0c1020b01801401c035906244051000c1c07261016191000c20f480260801000c0c0e178015059a0090040c406681e07035062281d08000290568140d18980d0750001043c610824080350381d001400685810645108280075a1113070515007000c1c4210200540d80d134503146503069504440341407443c04006071300036013031101a80b0040101c4144082444e0800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 210650260 1250 210649010 210649013
    0x9060b180612100305060606040605031f08150603120909070c150e0a03022b0804020f060403030c11040902060415020114150411130b0c01140408180315060d 69
    0x700b80a030315031844580403603008000c0b4506000c04007074103c0b44282c040742c03000e4882c001082290302030f500440780010340602c00200d0460304545600380c840d195040f0380c0505512428805c2c1807000c40c1c00b00581d004103003001d025280c203040010600d2151000c0c0c0c103900748640000000c040b000080c11b0b010800c584030a00700f00784072104501d0f10514070701d103404105988205411135151540240300780c0150003445214041e016180c400c3d024816034199000d82003041c9010240c2c0e205c80003600980c0c1100300b0441159030b03a200c0000500c0614040d4035458581c00036458082d45500403485424050b03400c04a1190058070340101340c90550307096480040c0700d0800f140d130403401000c0a11759100410015000e00010403004008c0b40302010059030107100c1030110b1036212043d44600006010180410341c000c000010704a0094005540e0200000c04c1c481c14540310310050301d00c160740c00d0b20349402c0050b0300c5004400101101100700c1c42a00a40650180610502c003101401041c1c81e000f841d00348003540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 210651510 1250 210650260 210650269
    0x8210a0f12090b010302030c0d350705031b03070308040305031302030703080a030c0810030f02060c0d02100e0a02130e070e0435191101020c011509060b18 68
    0x1c21408952208011450302818001c0510400b072001368020302608841260b64103104a00c1200b0a40142074041101210030201c904603440c0454081980403140241d2001018200140100b034042d000a589592411708521003603980380c50700e0801680308110303201c0042d8028050942c4a50141461a1a6500d07072981c6c240182c81100c00a5240c01012004020003002c40081e1000c1c48456030100007052000000b030321712000c29030700807412401d105820400640b12040315004107201600d040e0030034004040f800c0c03a040111a42c28096000955104034803d51b611514004481c080000c00c4180c1d0b040c0c01041d500a03018642d030740d225031242e41c21039841400300190002403800c10a45c4019141600b842d1800e14228603019900da40100d12500d0002d0410184040590517555014940903040350030401031700c2107409100a00001c2c148510307480c1028405809240c41d81c0002155400700d101d035003803c125240c0c1103403c489141c00030a1185900e0303501030300c6210654000644507009000c0014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 210652760 1250 210651510 210651527
    0x317030c0f070624080c090912030106030519060b120c04081b15040807060c0507030b0115170115050904020405100929030c0d0e0d0908210a0f 63
    0x4040303038500040d80700030003c2a9009141c5100141c4d010800d03603001a44545035404c0364881c000c5a907011407551300480c9030244034150403100403400c80360341114040c10f001c45604245d000350003280c0d031041080031901c0b05061600155000503410440b050a0418440050154030300743d0590006e640009182070085008a40c05400f80108071003102d010081501c005484104505000304490900301c0050b01901d02614140c4920101404c07016007000000c440481e80c2000a4a90b4420740c01c0010108610807401406481002c1e400c0f0b01d0240f8076080079002c00320380150140c56034032040040104032a6400c0f2569691260700d805a43c0700e2200c00090080c2c01681c00c200d50040508080946481d009800d00b42119110141e1301042c140c910300c090395010805d00c6550b10420b00308001010202039030b0082c000c03200312800005100c0640100d60313241c003031034103211804a00d51002c144106001007020f1400d071048440441c941015840c038008040c080c0045140c00c0c05008281901001d0044005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 210654010 1250 210652760 210652777
    0x2011d030718021c150506070611210907080d0e0a09050921030c0301170307050a0501150e011208031b030901090b0a0209090408030c0405031905010e070317030c 71
    0x100d0390992102800b800290700c4460105109200050b940d85030680d140150688000302e0700791030034858600020300884e58006617080307800903940c02e01c00d8111006c8101600d0541e1070008424110900610403502016020f0001c40301a40084410020450300084640038405c03d072038003512060240007c580704500d25044005070b01e0800e410804900400520308600380702440c08070346c1c0030419060224aa21060b504808009001c00c01804504201011407203103c0e599000c4a14202c0d0715114035041a1541c1d0040b40c159444891f241601d500e1001c0d240042c09810f00a041d280d45400c07081140004c5041d001088040080001920001c1c801406d01c1c8058070380c00c400e40e903071034828a514020702100404469043d94840480c5610704075100b1340f12601d40c00307030454842e51240e4880d45e0840e000200200248141048049405d440503c403c00c2000c01000500c04120214a0420b0a5800701941c104c40d46d4002c01081012814001e945000e00f100909141eaa81e1521000c020403489244036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 210655260 1250 210654010 210654029
    0x20901030905030d0b0306060d0b01060c140607030b0922120c0b0916140f0d110a1d01090203060d0b060d0807050303100801020a0210050c07020d05100606050702011d0307 75
    0x40c541e0011909400c07030041140c0c1182980e00304e17901e1404101018212a01c007421841030f600060007954041c030820337200380740900040d40f0500e040e15006440c1610071210803000940b56176401601d403d0414800d600002076038803d200318602140c400c807590b004950090882203624504180741c80c011300001c805241c02134035110207440d00c4a0366560f12030055000d150700004110303000454448420030b24003051001042202c4072154030081004003000e07070100381d40e00091300910000c0e9944440481e8000c100c0703410070b001d01c003c05807412941914142e022001e420700402c20003c035551a030140c044090303400090307041e0301c0d1180000b198954201d00002080c0110000b00c600621800001851065642c50f0000c07110640381d180341c44c03d030f00a440d0204096440040681e41d03640719a0081039100302644601414100309070002101c02d004040300365407a40000300100300032040c82c06110094140c9051842c034081c065070000307080040610060201c0b0b58201c00045080d034041c09500002c008000c2d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 210656510 1250 210655260 210655267
    0x1110a080f0d0c17070503070906080a0e07080f0c09040c06050d0e190b100b030c0c1903030c0906180b070302100f0204050f090c070b1306060e01030303290402090103090503 76
    0x40003130408a40441e02c0031081c5444030000f000d99206d0030807203100b1149541e9200702903160000946810201030641d0a4150700d0b01403c0308240e40800c107182c0109030080007080071a07141d0f100c0350306004180b00d445005184400411012403206200f0104440c5a450016070b00c0c181608041c1c02010360000740c100c24022030700350740700a00c07121081800007400364140520640b00c008004504001d0303803050340c545003420320000303241501c1c0350f02400881e1b26010946400440101a101100304c521008030046070b03462100c0c031903c0d80d01c4002e010103403090381080b894240c40c1c8800e040b2200b44c1c42c8500c1018000c0000c0420400d8800d20009150b5050740e03105000c01e4001254041c080d41242c010b2502900c62528007040c145400d80361140521542c8107040d241484d45e490352140d6034801014441c103000140041c40c006500b0f8420311004261880d1811042e50451030f0080c15128002401401503060094900004001d094100e20100d411140142d071116008016001b4101400c0058054000031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 210657760 1250 210656510 210656531
    0x18270a0318050306090c061624050f09070510030b0603071d01020a0308040b07030e060702070305010605060315010f0201061e090605150717040314010e060601110a080f0d 75
    0x14404400d0300c0140000c242466850782c051541c0c0e03000803503900c5144c0d070160243d80c00718100303d0b0044c030740c0841d441e038050f414511540307400c1000e00e110300b051900c0500421090082402600ca0359070000c8072100e41c401141490015156582c5a030b0213540e11a142a03000700010354081c2d80000145500548010340f0381c54034540c06481100c0c1105d1204200950004c030300025840412210340c9564161100e40c43c1c3c0d00c482c0c03945541118010044018142c1c1c521100070201c004010107403045460b58024945030b030441c603116082d604c8561045000341400d005001e008030741ca070005c880722034084ca01080008940c3c44104d000d00400d9104545220600c441000403a10b583c00c00819140c8810007800000e40d203d0900112a0400740c4000303408100740200c00010f1401a50499284856081d4604180c1c60381c0381c500700050102e041524613952000c01070107150041c4a429841002401d0220100d180780c4042da03225410107000410030b0720005260201900281e0076075036007030543e03a800c00c54a48035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 210659010 1250 210657760 210657767
    0x20717030d0501060f031b020312060607170c0c03070f2903070203090301050c13030f03050d022107230903010e120903070f23010c0210030507090518270a03 69
    0x90105c80c1c40000d061007406e81d80e480c96045054040840745d4011498a849100240c00c00e120251840350b0050381000350801040c2103020040906010b00103040c0d6800c40141e6a6203408044070245029404c14001000740d40341016a1108880b5201181c29060b811500c5002c89c01c080101041c101510100502c4035495000014040042e0103a001304840c2d00c0d003100010013809925600401c5068070101032000541403042c0d02141486400d00600784040045008140c1e0005005c0c624100f84814005c0b003a2420300c0c0c1019007120b0b03035090408481c10360f910084d082c0d81c40f2580c0e451440c1000143c01d4055242580300f141900e0040058404030b0b0b4520075030090a84c03201003128401d10801d0fa000c2011b00c000400001114030360000360038900c2500614503e00b0490351070041c107014201e90400c0250311103664100144206035000035642c50043c401a120b9030300c540045000c1e00c441c02c04c803000c5811001e00c107500700c100100c032403100c049109480684c1040a00c00085d20f40114483e03901010780 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 210660260 1250 210659010 210659027
    0x806090d030b0d0f11150f03060409050709110315010f12020306190306150501110c010c020117310f0b100b0a0206010501080c0703080411010e0a03081c0c020717030d050106 76
    0x5003280c100706100f034103503511031680c0a43d47c170b240e03480481040428010303e0039a12504074544908151418195105112401c8540780010715012000010401504013840343c41619011002d0a154038610581d1038000c0c0116002c0c440d450030181d001020460365030319107401d2040b061401c4074101e0183d1300c0c1d2030040090552440b0207d000c850801c80410150300407043d542c0c250084a000b030490405c60340044802000704003099061090350b07400304081d69a0250b4039031003461904003500c051184800412904072951951608100010444200041200384020542074100a860106031208002c003c061070061340031078188400010400320194010924504075042622601c042e41d0f51070741808078911aa000040024003402c0001d000250308913150621200185002010880040c0c00f04001c110329400945511070081400c400c035161126100c41d281c20014024080311249401c080e40c0e454060086c40c1141001c0c10f28501c91201c10000c0d601240340e8030100b403140b565910400b811a14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 210661510 1250 210660260 210660293
    0x191d0106050a03050607030507170c1201061d2106240102031201090c02010b100504030605060a0e13060f0f050402010206090105090613080c0304080102130806090d030b0d0f 76
    0x1420214006102e190420306a01102e4018002e0320441d07403842812002040d008000c80240080b400100d03248841c04c0d09400d10521090b120360341c2e00c0c00c1d404001401034905030700210800100c003540001c1c2c00303400c40e0502e01500e82680c107440352400c04040040d41d1240494000440c1c801d2404000394000d241044182103d1118060442e19400f080126124407034030560020301c0c9440b80040007552103c0e403000040d00c0c05840005034150f00c480c0003035080146002c06100298001c5400c1c001d0240510440f42c10005c00c560031103007589080801c240035030703006149840e010700340da0180b03040c004181c10954081121150030032030350358150014070040000f600c05900500c11000002c0c0034880c14450940030713025400082140741c1c0e81a401042200d0100422129100c05122010402070200082d2010304180c20025032120003204001d241c4408903402501540c1c82402408402100814014030758202850042924400103020030600950b40304001c150301c0c00b0446150070b03c0100c2005403540d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 210662760 1250 210661510 210661513
    0x80f2a06070b130b10060c020105180d050102030117010207050703031404090501120312051e07020c12061b1314010e1305061002010b011e0315151205010303020a0209191d 75
    0x10b17284c0c07481056040710350740106408140507100885c0558007680161281040685001c00d021000c038022031006020440211500d81d000310052004a44a000313007546000c5400003181882045e80b226070f13441c211403102406200d44000d0010701c0040540c00ca5000c0c1010000c207010341c0d69110700000c1e81540603c0f040d00014401001503000c1e0055020301c501820256581d1140480e00440c00d410020002d422403055120703143c1c0071840d49e25507610403214100c02d00d001e0141da1404100e4111040c1d000300c0c025844010400c070701c85040e000c4110f03110540326246c51301d24408800301c006030344010701c0c039080e9039002c065000e482791160315680020348581000d503100c00140c02c1c1d4000923426a100d03400b50f00d01240901e130880340c0340c0070081c081c06880031582ca40440c1c02040b10301d03581c0107007110b40c100c1a1100c040c4c50300d075a201c503004030341c0c03c4101d1003080c4c00b00122341c0b40d03403402501d9260600e40244100360380c0700031a4442186e0b030750030034088042010400844030380300001010740c0311070700451041c1e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 210664010 1250 210662760 210662783
    0x305010b03010b070b0606040510080a0606052704200c0d1d04091a01060804050706050406141b01060602160e06010c0b04030c06110301080f2a06070b13 67
    0x90991034060320304031186144081e0038900c2c20b54408803800e000400c882d4018005010001d02940d5000659001d10381d0380d1143c0c1c0711801c00f00f20210644d441a00807206010042040451917444101c071103400d444101c500c1608409a4400203000d441d0401c500d909000aa201018070003903241d004004d0030100d170040b00e0300041014030941e450150142c0076040d03811030807410b88440c02d141d080711401512840c40b142091090864041d03400c01e00781c01400004100600304420000d0070040301010700034506046007801e01d0400001c04201c964031404000c8000401c01c9501e04880c442420303003800700c0ca0002d00049403681c000a5440c040c8405201500301960710010780c0442d4400254000c40041c4d480410141141d101c08000c054090000c030f0030000d0000040010030194400c64880e6440d0403801c5a0303a502d4642c103070b13240112000084c00c440c0c1001e44005840c06800030401c0115210a0b0543c42078000b04001030814082c401001d00840b800f281080400d03400d8030010250648240e0b1503204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 210665260 1250 210664010 210664019
    0x9020d080a1806050f0a0504030c03060621120f0c1205090f0a030206030411190b0304150e0a021002070e09061b07050d030b04060801090f0b06010219020405090c03060103050d030501 80
    0x1068001449580c01113101048034622000302840100410740d001d040192500750341c1e50719200d1a180550050396800d5584005000c007200300c0244804580d90041c0e007580c86415619460950300c400d00d02101446031070340c002115240980d552603030b00e9400c06d0106090924488001e801980440d01c1c8520503040305410350550b160210984042e250094049803c50740c45aa50840c0740076030100c900ea1011182580c0f202071021040508094004011303582d440b820145000003800c800880404441420214002c50f400030000300c074020142c04480c180b00c100c249007070990810001d50820980383c0910000c204071420001540760180c0004681c1c80002c034020300000c2c000d0300591400600315040224140103691180e001503001c42001071001a41598403510f190071034440040888041c4141c5c0201c100b0711207107039045540803200780094800304100007101109161000c0000b8030842d41c5901080c5100300402520950100240c21030701c055850303007003150780c40ea5103116000001e03050800114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 210666510 1250 210665260 210665297
    0x804030305090d0903060b06270102011d0c010e061c09020a0501090f062a0515011a0403021210140405060a0b0901050d111929160609020d080a 63
    0x2d43e0001c0d80d5890041e100e055070b890402901290302001e91009080c0811a2503d94181d003030302d40207049880780110f02c0aa5070019080d5240081411401105146600c040c0c403008074103d100340801746440125240f05000088180c00750490150280010610074084220980c2c001850980200c642e07208103596900111541401c0380210281d903010601c00304401d40c02101c005006866100043c08000e020030070100d4006e841000c1541c050303000851410b0802c0d404042e10303000d000e4080b04d06000081007104400382e8420f900c0004e00032003400040c5e00c1c101ca02072100cac0c10000d4621300c003400b80092103101101818000c2e10261081e009501c00f05008112900c01d14030150009420501700d60f103400304018801e03d110b07105480000305000b44907110faa4881c41900c19600f4504c0241215040904140b03401c011044806103481021100e4080b803001c40c019070f00c00001d4122507049500b19840e003100a0130b0990b800a4103c59031007410005c01190001505a00c0e040344e0f10440000a00c0d400310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 210667760 1250 210666510 210666523
    0x20705280b07020c10050d05100e0c0706020c0a05060105030d0f0c023d090603020301031e05152409040c03080a02150103060c082a18030d080403030509 67
    0x609a014600e48940c000400d500e070610b52052031030056580e141c9070b400209410790f000e4401c080000b41c2c00507038103451000c10303c02c59030070280719119698058144a60700e4042030000e000883c03150004505c2c0410810b058046560303100c000030584420400510301507039100b8081c01402e00ca80070b01007844ea41680702d151550070040107503617407203003009540d002d124425191000d2035071444d08200304041c54194480c8110001c6500030900c02510031600c40080c8881400d41100041500400c0104003181314840d100706c21940d9050031030790304c401520380741d45482c000c1c0003c0d4813503e03400340811070310f84204085601c05510700ca035158810061703002086240d5504403002070030403140400c01e0012520303400c042c0030350203000c1c0100d0340b800b11507114069090009030b0086921580b51100d8842c0c01c0d40c8045040e8100324100d814480000308810b03005010740310b100c0b0b0109060f1000c201201c038002042061410380602405403907030300c0c00b080d40003003000303c04444c181c0104e420140450240500040c42 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 210669010 1250 210667760 210667813
    0x60206010e093c0c0102060901060308120a150602030306040f060819050c0319050f0705010f03020a0e0a1202090906060f040f1103010f080f031303021003060b0d020705 74
    0x242c100c0c0307040703030f065007003900d801045111075078481c0303000041e40300003080380c100c03a24a18200400940076600d0009142a100408182d03669051190810004103000265100d503180d040d69168565a1031a81c1c0c0000c051a0000c41a0028201000212580c001c0f00542c00340400781e80c140305166000d0b071003078180c2e070403441101c003140e00000180c0568000010800307025880b07042552400c4031401c0c0000d2a2103412200e0012180280c4c0c4c0c03d0080050811800c5003040801000e8003c1c10316210011380420301456640c0305140e00012034400c1c041c0f0410081164040003003a141d600c64403084492004015100101d0042e2034100c003040b628040080c50a205800003840300601c0140c0c8070038040940008a03514004a0f1251581d2a140e468580035502918072550000c1c245450449003d140000005056210f40c004005001c5c07202c150340e030000252601940d003031418504030340d0100c0090407241d0210740301c00740100c4c0035600b410a540003000c1c503d0243d411500d504941030343c07030101c0712030a121 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 210670260 1250 210669010 210669013
    0x90712020105090a08102a0801050108090a0b0c07020f0103051605090402160501020304050709140703020f0c0f0304080706091206051b0f12010b1303061a0a03050106060206010e09 79
    0x404005600c00d40c000c2030082d4020301404203440d51890503030f00d0071907a0b017206c90100d43ca881444011003150014084d800c04a00d102c1d060705c1c0c000860160140b1010b006003030403c000c80e4000740004a080113244405584105010202d28201e202040d4030303001240124417501440102c0e51144d032090140c18060644144860300c0050590070588050b0301c010310f22038001d5000e10131002c100300014004040c4501590016a40745002c0c40e185003800c55a4001c00081807402c0000c3e00c04100c9002c0d407a62081190500595569007d0360030722581c02043c0c0c0126051140d071101919035240071000d001100c1c014000c894425494940a9480104900801950072078132101d0701d01040741c40d0031268000030440000c603048560054021640c1c0c3c00386115407408800081d61485095520304128014502c58045905000e02e8140340a40704003140b20280501d501d541d940b118000e194403010420540040c1b00c1c4410035500d14110b8060440e5100c1c045c05801f66800000c0d680c8284207405214008070030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 210671510 1250 210670260 210670289
    0xa060e0a0e1b040906091a18030306060a121a010909020c0a230610031707080d05041b0905100816030602130f080c0411190e0f09070f080907 62
    0x2020800c0c00100b5240a40e11640351801e10012580310310074820524000d01010101030003861175600014405030030f88800b11003109408452040204c02e4a411090494603966104400d0724126090b4803440b030064000c61a0007980301290b8021030320100700d01803e881d084409c60369405200d080380520200415180c00020038000000c51002000101d11070300500c0d0082e121048841d545400011202c21056191032141402804002d842160719501c81c0170461b440d01c161a0340e0307162a0300910a03108005625013010404112200326160803240c40724800c500c1d0980d9603071401d009400159807280002d4040200401c1880011a1074907008400e200d0070311025103156100300007507001003a0b80c18080c5500c6c03800f051260b9600b030b80c030000b081c5540041036048500401c1000311900c0000340a01010100f10001240f18448000d0051303280e142011000c0303501c480c0208100001040b0243d40c802c0c6480100420142c10080c0496802c1465403030420740d41d1045043d50f0b41e02d807607016111481c1580c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 210672760 1250 210671510 210671533
    0x513020c0c1f1b12050309010e0304060918093c0804231914010c0b060d030207051807020d0206040201020a08030910110d0b011806050c12030a060e0a0e 67
    0x3a61200101c02030900007141c0740320f40342c950500c80e082e101d000c20009a800400e000004809005070390038600e14030051440c241ca0204d02504001c8a40b0a0310000320728048000d403800c3e003645c131203130302d071a009080c50030140c0e02900220032004060502c0202c0340e0079155849050328025003a600411340c17101d4180d16050800981c03072186004000f0412030f0640e40a0441c045460791184400981540721010580304d040124401855a45d012842d041140c0da001090101740100d118503008034060350416048141810100c3c01c3c4041a04529003120a1800d40c1c0420780703000040511880c602d90964004003110301c01280c440e10140d9002e40164415045200413401c00300041d604240c0c2c80c2e0032504070b291004aa001136400e403440c440d505010100342c6240469090081a425000c03d1910702a807213101c8141800303014a9018403c00c001703010401d101600c0040101c10013000c14009000d45902e094042c9d01c0241821b07026281d551841600820a4490b0178000c0715074840c1040050b11210451 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 210674010 1250 210672760 210672767
    0xa0b36010509060c120909161d0f0315010e0105010804031d0a0510091404020f040909020411040f0501030b0f01051905160302011d0c060406050f040513020c0c1f 71
    0xe280c4241d48520f0400100510b000300700204e0060550704079090303803140b5060b000c01001e510010907004070f221844000c1d1610316800300e22500d0301d1043d0800030001c0c00e80b40020a60019a85e1103c40d0107100e4208032960300070958888034100c0310000a4411142c1e01c4100443e40d0030015200100410140c00710240b0080c5c01e102451a030700409019038551540e079000103440a0303c442c00380d10110780080001d00907100c000348490700c892025a0250724050111800b8031131807150388260300d000d5503070784d03060700466a503038201180300b0300070801d13a5440781c1c0c451028400716285032080340d000c02e25241c40d40351141000c411089894034140c40712418035072807902e0790030700d04014031407602000010080c2a422880c00450584c6150196000040f010314907900d21340f010000961165259002c107804c8201a0b640a0807202511304618005881b00e00c0410a50901e00442d04444c1d8081101031000080d130842da405007001e1500d18046460040c03050741400b904101880e88a0940c0044502c43c1914501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 210675260 1250 210674010 210674017
    0x4080702040906060e0a0b01080106170a021603090e070201090b0c1303020301020a0507020414010b030118060f090515011403012d030c060210020a09050f0f0a0b360105 74
    0x180002c03544a446507260011a5560741155600d05405028002009528440d51011300c500f8242455a54101840a0400c06c01e0210403071245400000091924016405447c3d0249204400d4120885036180190075003025001d1401c03103220300300003c1c0407544140130b10685a500010140003503100e00c903840007580e110105100103580d84402c0007006071024802424800000d5444c20345855107481000700b0348043c030001e905011a0240144040d21280c005c13641129118102c0070801c0c005040035501070000741d03010541103000004c0c00104032004e500554402c101100244205041000c015034520001003565030b0070803000c2c80148805d64030945c0721408110380e4007035181901200c85403048544e03002e8002312004a0721290400100d50100400d000444559000f9820070740360715801010200c140c40340d188180d12554580c103441d200c10442c482d0a00020300b00c681015141d10400325254007a0082c58600000341004224800c85c18290001c48160740340a040144446001100c0c580c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 210676510 1250 210675260 210675263
    0x160c02010c02010315060302030a0c0305390c101b14030a11030c0705060601020f1b0a030209070201050709170c04091416091d060402090912040e1b040509040807 71
    0x581c3d440c0c5d0704214503042600c1000500042c2e60150761391800b28040401c0d900040c98000a0506103024000320a03800d400388900e209150482496800d0884401300d1140c0384100408140c40000500a9401e40081030584480c500c00305c0038001c1d0014040300600011402481c040015891059100c4031042c1130011030f00b20700040c50110351108625811485c503442907030340310001e03000003e0f0442044414807450343d011000740081d180003003440305e91986039480209001d04d5030580500c8001c1e603075a1100c024020355000b900d456428078011401900130503042d00d117400800c01941000800c0c043c00c0d00c04143e0103040f40d0140803c50002c80134400a04404802118000c04031605284090400c1010320700d01d88440b00c02d142c620746850302e105c0460b42c1050541400310244606550440c0c0d000908a810070340c10303104401c0030390702c00f00301c0d07814801c15141f5140c41c0e80001400284003006601350f240140440404007185070548140c00038688100c2c03103215007120041e000600400d55401c042d15025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 210677760 1250 210676510 210676517
    0x5070207080706031401050102150c0913020309100e0c220f02120403030c0516030c0f0c15080c070519050111030c0a03050901060509150109170c0306160c02010c0201 73
    0x1191507840060400400b03400420000703650303010221038144610b0381c50340102002e00103050b1107c030548100000c041b0003414005900700015043c113068407a0303031600c21103440360701045459041c807070003090f02e50040032000d008050030101c0d0300c0c50b0610301241400310f80800515401e0b0a584003207080d0003030f0316419084c0f0220350369900710380b000c0420f5000500c040c508440c4c00d116a482c09160140071503041002d442c0030444107001c0f600030111005995444c05415040410280c041d0f460809a44e18203c1c0c8000c01108140d04000b500010311458010300d075599807a280020341d10114861070764055420080c246a00004d810111488001078981d4020301600011801106141080c881c580c420750b03108001c1d201c005800c02082e40e16206443d00691090020b001c250302d0540025000000949040364000301401c0c05c0c91035a005100354001404003030318031001754019542240d110311103507080e50b01a01903d400940498441581c03041280c12645906180320700a800441d15a040014200d040c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 210679010 1250 210677760 210677773
    0x10f1d010e090f040c2405180a090609060515030412090e04120e0102010b090708180a050304090e0d0206010e070c0506090d030609020703080f09010204180902010905090c0a03050702 80
    0x110b44504071460b02c5072082104402e59400c0c20f00c0d000d482c1c08003640c000c0000e051200c400c0081c101990414803040302c0c02e49812a10366038040010100c4a005e4104242d000a5440c0009480092038100c40100d81c0040010040203a07640d090124030070320481b88004888007040020001080c0343e102d602c8480d99480c001c00710340e1f10380b8146600505d0598081da401a584007140f603110303a00082c8454004420700c0244107078032401c80400c0da543c0b406003a0400b401202000200311312400f0b14031f40301c4d031b0300c00c501100d40c1000035040c480d450343d2040c02600215806c090580d540c4003000078512440c002958001c0100b0b03840c1460b406400c103409482d160401892031610004a03504201c2c00c1c4c010131500c00030b01001d0b0620100034003124035603804824068014001721011030740002d000c1307500c5500140b050f4215036844001b41c0c0288140c0c1c00084e10f0600003041c003155882a41d000408161003a210440c5050326402003280c00001103400c0004498200710402043e842074211070340040490046030324 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 210680260 1250 210679010 210679037
    0xc030204020c1e071e050303120604020c0703061415060d0905010b040c030b0a06081522050c120a0501031709011e1112040e0c0705030903010213080c010f1d01 70
    0x502110000d9414540c8924803e01440071000100c0100c10014110017010610b04000b0136201e00511036807080c11554500024440d4950750101c441d003010b458240c03034005490303240140041018074051401c0b00452400660707403148100030b5003040c140c01400c2c641001c03c10010318002e40607500701118103540310940c54170315444501030081110000d0f1030104501c40098280701e07014442c0d600c0802080302e1030040c400321610080080e0011501550042900c01b03010005940c030b1000c009130554621725000400200307040c6100501408544c8440c441c0280d207940710640c040c0ca000707000103814138810702c02103441c41500743c0082c4a110b0041c10003046400003409083c540c0003012003040d002c10300c0040c1c01000080103201d03411803404030480050511b030400c485020300100c001d1910b034104000045047c1400420030a032030303140d40020300a40d0307105040c036100c0206450034803c5210f18894810600789560041145420012803540d80a440112071611010040c03952020389052107880e900080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 210681510 1250 210680260 210680293
    0x40b0301170114150f010e030d050415020c03120a030b0315090c04060e04020603040c03080c03070c06020105090606040b0f121b0901030f080f04120507210c030204020c 74
    0x500030074103001d59200c1d494299006078203592928841803841803045040080d08600c0c07511209051100b07603884d10314085a032005aa011a4501806e645807040d05441181954014002e1043c0c6800d03c41c000340741c00d803c100070b0317a507020010051640b6820001482007540402e4014000001181c03601268403880500071030b0400014507441c1402105000410500c0710007003007062000076090740d080200381d00e001c1006041103400f0300020301c140e01c000040303414801112156406942c2081003150f607241c203041481d0342c9a00480c801c644014440c440003680c0390061188610414000024100d19558181004014007071540d040b94005000e080c0002151591000071404608020043c80d9410f2041b2108020703220b041c4956214000090050000864064080500c3c0c0e42c002c0b04161950400c804042c0035005541041c0c0c454461620144103110001425004880d03241585a40d41c8280d117170b034491000e00072507010301240180902000142000d9000b000034140385001d03114000105100c64 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 210682760 1250 210681510 210681517
    0x5030f15270c09130503070f02060f19120c0509040b0604080d120f0207050703030c020f18100b0910050f0d110d0e0606010c080703020f0601260a050a0b0a02040b 71
    0x100000d5100c00750b900ba9606001c2d1243e42c00c06800300c92003400c0302d01a99082d94070b10a40030001c02d800c0001e4054011511002c1c180c8141ca03d6000845e526004c036000c0116501e03880516080009185040b88000c5421a200c0c0300d587d0f0540b035030343c603152403c05001e0001800504809036000841040300089151003800410342540c0d180e0354500e4003907030307200030f05052718001c00b51400502c3c41040303141c001610010b401e00c12a980340c03c020105010600014551410906a8903000745a4240070800e00003840035003441000e55032405120141c0303942808ae514042c0e10358240d040510500042c411a0203400031b00001c03100c806260b0f00d8481c9084090007070307038514542d1500461001c1002100c0901d28080c2c4824900a440201203a02c0c0c43d1000070f00d6078000700d41c0508000c1000480ea07013450b1080c020110070301818001c5405075652405504480d08200039080e481c0c0b240000c0b240c2c0148801310301e007a01d080c1c2100050850719030f0b0340c5480e0500320014124200f0395030700b003000140100d0100042c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 210684010 1250 210682760 210682831
    0x2d0b011202130c0909111206090a0e1506030d031a010c02030f100504200306072703030f0201060e042109090f0c0305010503010b010c080d020f03040c0303030605030f15 74
    0x4800803039117800070041c2543c20510050f0890801030111921640460150590001044811010079100c251000d0300514508070180c1e1180207203141c91448082c0346190501900d015000c40745c1068482e40101d04480c105000754007800d101900429181d171241c2030003c445030001302910400c5041c0300b001441c010083d10301100cac0c551207004000502403100440a0021059501851b51451110001362a4003001300710805200010000c54203605040c0810f611421105880251054480c1400340204961070700300310046d82441408117100c0000f40d03105000d01e07804035401c0c01880383c44218119200e5043c128500700f2101c0000015601d40728010488071076145040082d010841002c01001c1d0359058104a0190781045128031190341d01015829a154100380380302d844040a507204c40c0030303200d801c4210280d03200c00310030321007400040408501104d1290300c1c10024695a28180744e04c4041150748940250032042c0030907122080308005c0b5a002000a10715244401d40301e40700350428005489 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 210685260 1250 210684010 210684017
    0x91401231e09070206040b0c0a0e1306090f060506090918060c0403030215010e04060b0102010f0906020c060a06063905030304050f031306030b0d020405042d0b011202130c 75
    0x1001c48603050240310070390020254070241c4403500d4592510142a000030300201100c81c00000c0605400c2e1090040c501c02d5140104a02200c0d1310040c40c42028001d6800b40101141c50003078140302ea00d1440c8034030011079501401003800c1400340400c021a4081c000c120804c0b014010206407600b00381889524856140c0d112155101ca0450400903d8800d40361003280141007030000601c948501c0c00c07142c82d403059000002151880e038100040b07024180800c0c040850604280c0c6c5e1008000300ca4000d41400c40360714049030b40340d5407140d68000590761548108000f2030b01d200d041c100c110200b56000c4040c01078402081d040c1c034052803100300184c1030b24081640c40f900080103000410505200c6040384a2460b0001c40c1482111140300c02609064070440060665541c8410015221032040c001401e800403c01c2190789010308001d9015002d040710340310b0100904042088055030545018201600070404600030ba09024604000c0804224241e9100481090600d10946a400740c0e01c0000501d64 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 210686510 1250 210685260 210685309
    0x108030307140310050d150203010f05033c010e070b0702010f0c030806060a02100606020a12080106090306050405010209090a0209120f0a0602090a030c0807030c09140123 75
    0x10070007024880b4111012003103000c100b007840002e1031000000d9069038021180b08080140354a8485000c0d01d490fa00d6032481400403000190101d48a8107036030403200b00741c007560801c0d00c60859907205044100c404010080803c5404541c41128044551004050b13000010340c0c4c8018459047c070b000c0e1343c2d5202c0c008a640010b07410f811075900921a0780045c3e1036080490b0094000e58001e4a02207004021600030500881c004e10400e01c2000303d255405910306081000d581c880e0002519640c01c02030030f42d05501400020f1349107920035000b0318100e49003681e548482d1070445d550301c0c0161030080e0090b1031664007030003100710301e660322140301d07001d01c00040006a03250180c0003030104140740c0070a055955045804140080070700070541822641d800040140d0350543c110009000c100b16420240c901071844a012a80c0c01d00000c084064030301072256503c0d280e540f09418000e4511940c4101c03107040100d0010441018640d60f040c188284a00400284d10301c084086190280b4940c8582035442407507 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 210687760 1250 210686510 210686521
    0x315120709022a07050f0a1a0405100f08070f27030b0a0908070206030702070305030406050d0506040501080c0f01090b070c050907020d08010e0907030f030203120c0a14090609030601080303 83
    0x446120044952a10000720031010041a0b40d110b44e000e108550050500b68584016581d90307584140c0609480840800c1c2c504c41d550885196070401d01546004a43c120500c0040743c0c000c80030114422602d503a17401c100c1d40c03103000440b03001602d00000c10501060079081110203440c5003d401a03c0141760103041741524605214801800207400d010b0b602d8a4a0404004500d05808440d0000e03019966030340c0c2c9031180780f422445c1ca00c0603070002d001c1c2e00010a0124806510500424852450800034407450700e8441c20402111400e101e0190b259100300c9489515080003000380c5904201410902c4003070340d4071040c0454662140d80c00700c444100340402030015140600032a1340000044c0300070851000c030030300081d00c5102c040c02821403521603800000d00054041180e030014552040313a83c21205420b160282d9207030080d00c1148039030f00e00007001403800c1a008056031003280c800c5e910031482c40c9140754035000c194030540c27100350011000c1080b2501900e0821000c0d0007020b41c3d070300465892900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 210689010 1250 210687760 210687787
    0x12d061d0406051c020307030c060f080603010c170714030a0b120a0c030b091c054810060e01051e0604060503060409020d0b010f050d08031512070902 66
    0x90400841c452464140d00344115210400c80d40b001c030350300d004200001c842500010f40b501c4400d074001010f1045054010803041c2d4806040790745554039480c2e020305521400c040500360344500040030001003507141c45601d0800b0b03242256070400a06e0602400e0041c411500c0c0c2079a0b401101e0103001a074442e1314911041c281542042d100d81c1c3ca10002e04048541c2d5914880100140e210244c0703042c84100100c0d0a44100703001001408050f03400900650301c1b40b0070064031540105003d00d8001541903405050807544810300100c198040703c0c3c050590621805031035040f05203c0350f100007441140708159080d003040c8a03c00251001c0c1e000380415601d04000c2003400c03000c943c441c0400700250801c135165511008250f074280c80040c1413a94030313540c0301000b0400616403004c0c040e511900d43c40c4524180504002f5090503103510007241c8201c0f80d2150300b4890792003460807005000c910304100290701055070b507451000d40c04e0000c000c00d5003100750308451880c03c05243c0000b0212a0f00060007203003401c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 210690260 1250 210689010 210689057
    0x20121060e0601020d0839070b0a060605090306070516050604080c072102011d040524010f020c0d05070302060406050c0705011e030b011b030e18040506012d06 70
    0x280380a02552800c010a8140c5041d001f4110f8040c98060214074881c48155408100c018040c18040d0344540712420240e4140c007050318501401c49c6008000300d046840751007201c2c01004040e00401198492041c21100c942c41400202c50030101c02004070300240c010301c500c900481c001d9161903114141280b00b281002c10540c400a035166a48071000044081c40c0550321003103409003005075600b46418410520a4407000f00650312600e00030801c81d48280040401414100f56400c505082008600554100314856004030143c1d1040100081d1840d04e41958441d0714400c200b0b84890355540d42c0411520780040e04100c003ca10003007a06513a84004000760390040c4800d107045658500102e00b243d200c42c1d4110100e504143e120850404107034000d60f0005182d10041405032003c4c5a1030600602c440030405e840c91107601180050100044100d1100c0c0c003580e040800761070700780d1910000c1d5091a20104c40e019101040040d040e038040006044034009265a442d9403280002c9044c10501451 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 210691510 1250 210690260 210690283
    0x40c080403080703020f1201080a1b050f0402090409060e0706020609191509080f090a090905280602070b011805010803030c0d020903030703090f0909050a020121060e060102 76
    0x22140400000c81d901001d0190003407098180142e540f03000c1c490306207281c46a16440d166146c40c001c00001e002c080002c0b0382d441680240d900e42c404020211030411030040d00d210f9907601c03202c0c00b8a00c0c100c520f415801400c000c24001c6c000111822203507580000e80d01481c4d02e502a40d01310400c10000f145d01400829400b89003034004c0c01d0080b0171700c0090030003100041c0c4050000003c0c80d1140403200079551007514500c6d04004500e8a840e00e134113295003141d001c0c5490303600030b50141c40000303040c0c0c217640142462207602078060200d210b0456000e40c1c1274200c1750242e094141c0d13820b4030040440c01c3c4d44020034502d03000d404540c0e141d60500d041c1ca010507110b003884590b040e00d03040040008050100950341c00c582680d08842d5140b4070790117581c02070301880d41c1d070f1136250200050711404c050300650843d04660011003000c00d2165900d403481f040741d03148a0058842d801c0003c40f90015807045000b0000e60714501c0005c8480b003081042e0100701d9030260484070b04c180c20707001448000e40e010002c10a020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 210692760 1250 210691510 210691517
    0x50c1e060702210c1f02040f062a02180f1005011e14040503070e01050111120a0e270106020c0a031709062203020a09050c090d05011d010b040c 63
    0x14941c0061240b81030705101006003c1d840030403c0180c0600034400707554401c0c0326064030380c1d0324403408482100960203480b4500f201c0083c15000921240110150080c40351802044070b280c0011106940b0444105007007240d20540199940604001990280c0e02a50034070a00c40300d5803138a40c03a09840490b4a4001c2070602060400401c00102003c1d10450102c090f4980a82d180100c003644407024090340c3c11180d07040c059408003050b850001113166040ba070090341c802565040b0020040e881d92443c2c1c00f02e4145200c2000102070640c0206002c00c01c01d540074005807201c0c20016050081c02c6840010302d80b00304602d0b0010400d1a034104058000301e1421504d24580c103185a64042c0b62101240901e560581c0108490ba6156900d6040d1800302c462088030902120755080300e400e01c6103040c04120300c680f4010b100030a484281b07208079840fa5051004091034421100200996801896000c490564840c0f4031b00145854035a46440580409000800c9501080f82080f00703460020301002c042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 210694010 1250 210692760 210692773
    0x30903090109122a09090602030402030c2707050f0a020d17061809030d060303230a1d0d05030d0207020901050402030403051e21010305010c080606040510050c1e060702 74
    0x22502288a07084441d00d0a0070030300c820348200c002410070132100c0c0d101d05075961600b4042401d004d481d80085120b54422020f45004500b40c0c0104001c002c140901c000c603042d500c280c028820005084040e40280d1142413042c1805607600f0246061741c0700305034080050f000011001d00345600a440181c1060000c40c0d0b50b003007840c1481c08180c141c20041000c03130b100c1c0c082ca070200318214028011105442c084c0c140600c84651a800d000d48188517003808004a40398a000d00566005208240c2d440c24407590f0340e010090b03a4040b01030300c00078040b5511a6001d039603040d203200040c0f010001401014101180561920800d004010310a10143e10145c000c6004004000000780e100c01101c1414903080f810b140c51804518000b0014042c108008440c1c0c8040c00b1800d40c80002242035604a80c814002071168100c1040700701c1d0500c070207445907a0080810f103c01d00c0325150510707040060070414608030741402c070b10030740e000e1404541000708900200500c00e14480f804090009030b0b8400f504c3c1c00140300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 210695260 1250 210694010 210694013
    0x403020a29040f05010524040b040216110102102901050c100507030f020f04270203070306030605060f09070e01050c2506110c060d0216050f010c0f020304050603091203090309010912 80
    0xe11f455801c5c0c40600c60780d40c1d481c3e1942c207940d03030798141c070f01c0d4650361800d0a8020b070f110b03d0102c4090003001c5000340507100f10160104040301c4d9000e001c0742071003541c0d0034a0001c00d88682410300002807000003810701205025400001d0020000303115403000740b210200b641d08103410b0190403210b8621a003603000e40100089502e40600d8000c0b01c1c116641d818980d8919026580c1940c03224400e8600c00500038000024010120b80c0354000205490003448104810703202c01080080d40c215401c1c040c2d4024079841c000401c1c5030300400c49440742c14018107019107407200620003141011800d0240e0f50203048a000400300102240d0152006415103080440c80c0c3d11070135a041c3ea4800c140c68946214100008c1e0040c0c01c401c181d0107840b5041c841c50300702d0784030201c0c5250441c1c81d40013450351880d40f0362810050203100c610610074940241e00d01d402862a080c04c003418030005500c01840c21486116210582e151200a02d000714456944030707014640b9050b44000050421500b94001e55030000000f11000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 210696510 1250 210695260 210695311
    0x19090f030b01030b070507020315040b0c03090d21020705150a0e06180712060903030b06090f0103020d0905062e060e040902010e06030c0c0c06030403020a29040f050105 74
    0x141560303080b121480545d0b44c2c848088403c5d10400728000d404d4000c0c84109419200c0c00d000f681d00940c42411244890340c0c6000384020716000032600b00102d94031445103100290300072060ba030300c0010410f20031055032040d04640e000b680e001010440d100da000e4554201c000c500d017000c0701c0d00040340000a20002000303c440d240c1e507040103044058074200014034250008070821600e001007404100140e42c1c084030341401d02c000c0054074800c1d07001c603081290b10041498040304613628410024506c1441100302801103000350444591100004c3d5610320020100d60100455441003030040160700a21000546a59841c800c20b907040240b02650740081c40a01c1c0c01c421198250b440584000036035008034001241d104c4020101240c014100100384601f1508040090444513005011640c441c1100400d120079884212000380043e0010a0740000060740e511000b4101030145920100302d03000110319641285051341c04440c540305040030b01081100038041c0d9a404500c400e1910301d45021850300f207 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 210697760 1250 210696510 210696533
    0x10b072604170307050105010b1b0a020604060c11090112140109050c100c15061e050303040b0721050711090402030d12060807150306080607052205040219090f03 71
    0x1440400b00c2c850000a1400800c250362615400800a1005503510030712101c1c00c2d40310315460f4400c003a00514044040302c002a180410542c0680080d180603c4c000084607240d2604a0403074428451034140102d07940c5000082d13010300703d0a1011021130300036150034824041c9040d0b1003a1603034145858107010403030200300c03104090001d55a440d0f10f00c1242c0801c071424032114100800171841c0300900e402010aa90104041d0303041041c0c080c0108070120f201608000c00c901c20307158076902c104418030040380d07500003500100b0300c9101d0100014413030444991480c202918110001a000f2030480c00b442240c4001e002d1502d0b007510038080f00d0925401003901d03081c203411848144024800301310070b4010641c0c001001031000005455000e91245801030f005002188100c1c000703400c01c50b000c2042c040c04200980a120301f030710380c03a19040c1040c41038003110150340d070410780c10030107003000040030b884900061020003800200a6980c039140c400c081d00b2041c180d085501c1011030090180001000c07044d18 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 210699010 1250 210697760 210697769
    0x10f080114010e040e0d03050601141c0b012109060501150f0e190b0705010c020102090a140a0f0e04020a090608030f0c0a05030c0604140c010e040213030605010b072604 74
    0x283c444514080108014000003550180b19208800f0000c55096051740064042c0f4001d9031052800100000070400c00d01030061646803100314040984400c00c036582c000b040c000018103141035500d000f00c07200d00340c03005540c5000300b60984850780312041005502c519405010740310016001d2441940d0010074004064401c001480081c250360b9445694070040146440c00800d44004070301c0d140c0c40408056002620120f80c0e542c20411002c10f1240103009841c0210001750404d2003280c500001500082180c07000a5040303110240d01041344404010300c5030180c060324079076604500349441405140715103540b000c00141e260890901807900040211140107021000d41da4a81c2d0101c1000790a06c10101d60051a510000410204290012403110312503801400407031925841031540700c1d00c034100a45002d0000380d82617032020a52920354040c200d070f11a203000060748680c880e51b61004461003a00400d98100000c01e2400412260301200800d1041211800104112078850345a09019a009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 210700260 1250 210699010 210699017
    0x2901090b0a050a110d020f100516140c01020f032205070504020903011b0c020118060512180a1506090207080f0313051507090b07050a0b06060c0109060b010f08011401 73
    0x83c98143e10303104101c0a9a045203540c1507070120380c1030120207943c400003200c2d94000c80c0505506510405541c2c81503d100320110091800203001d101030440340305001c503154117159042031040d201983c00034805007150101da5441c1664900f0030b0840e240c40700841d4102014080b8124010500103000070802d0001c0354010b85005d42c80300c0300035000a005d007503050941c1d1900d180302c185240034581d100003128560742c001c0c1c80740c6110032504c0320303040c010039420301801d008542c04200c0c021044815089441d03200c0c810b11502c00c40d8112055a00d400c0600381c02c3c041e42c0c403500180c1c2800f00254a48070320002008074400840c41c244c0d0310fa4030f0b0141406144414001ca06001c40000c2001c5843d2103031b152040c0c0e200c02078900356103d01d400b0820500d0250781c48000110314180120b5451047e00c11982c4440e0450005c00820383c1c2030360b40d6041c1c00c038001e000ca5007100b814010303000f00e050b00340038071703804148620b034045034488890000400f81c290118508080080140041058644016001111f07080038039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 210701510 1250 210700260 210700267
    0x504051003060f060e0c0408071202040e010c0905010906030606020c0d03090806070809010c0c050a0b06011412011e03080a05071106032404020c0c0d14012901090b0a05 74
    0x240d8490904866032014006a0400c8440c016030605a48140e0a462003000c1d10542500c41540d41696400b0b980074400281d4089c03101804035800da495014140c6100030808141c40442850846c259480d282210001c104003d40921aa40c0c0002010028292a14080150721700e003c10003950b490081032050300a00c290201c060a0521541440c0060160403003214aa41800c035802490b0340c80c00c17559520254603054200710414071034212502c0ca946c20000402c182c00340c584603000101d030090000d50600610302c1d4203103040c4202c0b4000d801104086058000d003980340020601c004460341260040c103000a5a051001520f14420307145881d105140c02911f0b1455854008190b55900350315981c0070401004202c00c0e00b480c110241840c490b0001c0100d04200a082400240d010b81c08401c4419089049038402d43c1c1410301d100e103049400381e94001c81141ea2000038030302b1100350544000c0c04003207010494140e00b05100002541c1c000c28a01030320a18a04169100c0c42c0c081c045c1e40700d04000000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 210702760 1250 210701510 210701521
    0x703030c02150a09030302120306010f0518120109031101050f0f0709090908071a010e011203051e03070810080706030b0303130e06010e010c0c09021c050103061a0306040507050405 79
    0x2c80d041030521020b0030590341c1c0d03014000c01800000807440203c0c018452a0854601e11000d48180c81c015901a103418044005a06054903107820001c15022480708040c04160301783e0b51081c016140c450781000004500c40315040090901d11003606070005a030416041c04002242ea814140e8001c850049450070ba03146d50004a8415900d648143c8007142022007540c2030055040090201c240b00d401001c1c1c0e0a1600241081c049400740f01d00040d03005040010410784001c3c44071244c1444c46442c080c3d18151100b204000070580000038014400030100c00c03c0200b0f03411007a0590800d2488000c0d40c8203915080440350386003418041c540415464500c07400950f1010070940741d000c442407100f43e258944806100403d84800c8034654002401c880c54085254040c0c4565100b898001088080b824184404c3e00f01940c002000310003041c081c0f584490408985100d440d001e18481c60f4046114450903811452001960750203a00c2070f0081c0c070038080010030000313806040360800c1c1c5011a003036945 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 210704010 1250 210702760 210702769
    0x60103150f0e010f1d01090b030f0102030c0d060e150d02010314040f06050105040b0310090507270506090717040c080307110312070c1404090f03050c06090606030703030c02 76
    0x1a07000340c85114116001044078102603101506980400354071407042c55403000036103003d52030855403682d4401104010300c40341d0a950081c080811f00501110500000b0700c3c003860880e0700441c1d503660030f900085240000c0c1200790103040c0041c0a6001000002c1c20301109603180500c010818900c80c41c0c10a020f40c3c21a4001d030403000c4040300c01c10100260b07140905001d9a10b001d40350040761042c3c0381000104a600e02403148503c9980c0150040c002c510f00c410301440104900d8005650901c103025001810f201d0314414010f2480c2d620307181e070100051000048007aa400584210b201c0ca0302e01c0101701c240355000d003052003205810700300744000b0f0b12582014500b9030040d401528481c000000e541050041043c82d020007004250110750300581100c0a00205000350741005001c582075540030400c01d20b4103644100a001c00800c0010070100c241d8440c1c00340360281c0c00440208202281c0b080c4011000c0c030405601446130000f8280a10380400029140c41c1240401020302034216035400070741d02c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 210705260 1250 210704010 210704051
    0xe0703051f060509010801051203040e0a0612080414090c120709180c08090705011e020c100f030b04090b0610050c0313030213020f0a03051905040b070e0603040209060103 75
    0x82840c03204005502d80340300511580c4405225400704000c0310000841c0c0c1410060750450945000146017402d0405005c410740c514083d0100b4059500d5550121384115181026810a44151749050740c0b40d10382040d0045004800c829140320b100c41d0401c020f44520824100c8440b07050050240c0550f6850480a4803030400641000c400e0000b4074a110700e800d6110391041c9480e603019101c1d40703000e0341d172801c80503a101d0040c01540d002440100040b2201030804910700301000d141c3c0141d844d41090500450490b8119070b0000d80011407404d40024565014405c8059026094030107200d200c03000d4031051030070840500303140d0040c802c00407008803040c8540700b521056100c46040e207a840a10341c0041040e92803d020691149005000200c1c520b01180300303c030200009119031a080c804005029002841d0007803480e0b50303001c482c045500c00e103241c600c1580c3c4140e1203400340008a00309103d00810084ca0b858070f036070003018200148005a99020950380d4841c00074640801d08400c04885c9080140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 210706510 1250 210705260 210705301
    0x1701080f102d0501050a0b1918080a05160e1513090c18050c070b0a09031e1706100801050405100503070902040303020d0801120b1017031e040e070305 66
    0x42c03442e02400c0c1200c1d035802240c1281d900705c43c11b080c01512000c0c0003140e8490600c2d8a82215455510307100300e140900110598103001d004203680f1a80e0b030f2210075080400c2e507041140e5030340008035502402c194054200d0054240c40e046a0326916007081e060011042018100f403003a000b003210203544518a8100304c2109a11010440c0155519801000c02c0414808041a10f03420300c400540c0d51040c4400340d90341150013298801042d03c0c1c8803550402015908010b40400800c1c0090900c0070320b50301c860400c01e80c0c81e03a85580004460381088070031203801505051160700103903a010255a4000300310340c1076450403a40000c640d01c82c000c1034824039040d503020a03054022000b0018080000c0d41c09881240c1c001d40036290200083c09040b51104801d0082c03442c81c41c2000c58902c049104800303000c1d44100d00c1c40300c1c510081e48901c4045036501d01502030100036400050548450a440348211001540a00485045c5230404c0c106052011000b0881001c0565841c0010780c1810000f59130341e41c1c107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 210707760 1250 210706510 210706571
    0x80d0c020c0a050102030307050d020c0712290c07112404081002090a03060b0d02130606020c040525020a020402130321020706050c0a0507061701080f10 67
    0x1908601006521100240c194600c12006035000040c07a5002000705c92145802d681e89034a090f0402d440703117009420140c0c1ea0750b400d2141e1803020519181c00d4072003a540901521100c4180c42040c85a03501000f541000c0032030104200c01400701002c0280300740d8802c80d03404080006011010004640c401041c1e1443d401d250201034200c1042820b2100140203035001da1042d1500c0d10301c55100fa00c2170b4803884010581181c681c010410100f86680d020900c2070900403c5506040c141c0e0700050300c0140c2d20941803040680c2c0750b504004854040002d03c03c2d0000c10340702408280340c0400d40310300030941c00501180184c5c0d07283e81140854800d00c00a004c45074014000c40d01e400c0114468013102308140011a00c10540680a00200e8040c26460001d00301c0d1b0b90003805140d05144040b5540d4000d90424070703940c070402c07090400252090003403002400c2c280d9640c10810507030003111000c2c0074041c3e00c0f405a81e085100361030407512012400c074132410301c50100810038407062151500006040004c3e00b52a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 210709010 1250 210707760 210707771
    0x408250b18151029090108131506080705010309150b0a030602180a060c050d230d050609071b021c0506090607020c1c15060510030203070318050c0d080d 67
    0x1900302d51910081d1007a9110090201c200d00348500b031240c0070700e13031003104204090044060540c8070700c08803980440119074001005520b560340da04007070594503502000645500061040c582c003046050b000300000d18041c010403441c1c0e103800a840d0502e031161031040e5242c8256080765140c501140340155488141196580e207080c00215000340d09021341da200302d443c40e41c00644240700b010110356854100713016100341e00700b0704402d5070480590555812055001e80c002880700b1090005400d0340c3c1c100329800f282a290603000c110725003c00400c1c1d2024002c88040c10341c850440301a01c0001c0b1075055450074800300d900d10700c0219803020000020501c0c4181d0040004616012031824010348041c0c084920709220b00c4200312211000c80208a0305c10084090351010a40096805184500001000810a8031140407801191242141101203600001408034842c0e052017220342c0e0600f0f524aa0700301d12003582d11031f0780319040028500d11a015100211003804010822a40a880d540904006 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 210710260 1250 210709010 210709021
    0xb07021c0b010f060c03050d150519080706051315051b0a12080115030504080708190e060405090103020904020f1210050f01080606010c080903060408250b1815 70
    0x800300074020120616600200064118000d4004445175503041c1c0b1403a0500d42015450401402c8074000c40200d101c12820006141e10b901440c0920310ba400c0b90301004190416601c03d14150b695427040c02000b80421803141c6c054203030700910003900c10001011808542d000750407542c902035040214520b808100c41a11000741c0050356005051042c00e800701021900842590114424440c1404125603080701a0301a4801d42c400c6901501c1481f0032402c005203034850110781d400488036030001c9526142c0380044950412031001501c001103551918060a04011404000042c032000740108441c0c03021500315510b0b20501900044064070518842281000c410740e51200e00344000b56041c82d010104480c08614030b10705040e02d031488001c21544d03c80d03400440e00d2902c2014156601c44044c86100d40740d907820b21919000f94052100140c84400401001ca1701800c024071a4445086019448001454007018280d11a000360200e918480c55443d00d54180002046820001c40c0f50004028 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 210711510 1250 210710260 210710273
    0x50f0c063a2a0806040c091505040e0108010b0607060b062715070b04020d030216090207060f0b01020601171e010212010503060c030103080f09040207140c040b0a0b07021c 75
    0x200b26411218240e40c50040340014002400c1290600e0000101e00000180c40e500b0150040d42c2048040c0c90919066652000040c9011036108490000030b070002400300708010f5800280f501404410000300481443c8000182e07261141ca20002c08964484c0002c0440e03603034181c1614230031101c041e0120841e041d1a1000085007940318191807103818800b100701c02c8840d421050303460090703002000350300c103840300e80810517054030264049045220308030781c901c0c1d58440c544000c1c009000c900e0015031a20890301e00300e0107982000c4204215246440f032070f52891380c2d0008841d41101c500e980e4102c0d490314240c1c942030412100e0181508c0c1981d60b0080c4080d1000150300030704851220401c11070309a600c81d4105903c0704816508508880402e10062001c01c6112000742500f40c14000c4407407405c2011400300382a0b8114440c01c0c0d484100f1007103038118520050000203909001210104041180600080ca402d13545004260417154003055600840d1a62605821510b0001035105000394042c503180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 210712760 1250 210711510 210711521
    0x210020c130b0310020729040b07030911010819060b090a080c0123070b150301110310030f060b030102070b100609031a100b0a0c050f0c063a 62
    0xe902840d12a00503003041c10041c802e141d92010014064407003014081c83c0c3d8006074010460644095045800500020711454400c58500c0d8888240042d0b514180c202508441c6000300f520081c5070800106ca80000d5402501941c0300e082404c240390691034030815040100b1504400c0a80b0910b07041c408904200c1900107000c40030021120244c1064541900035181e0200280032800324403960b100e0b08410030420322154100804684060406400c0d4584403d0394005689070b020010880781070711f1507400c00b8094a0001064140100c0c91403c2403240d021808005100150454106d481d41000300621600003418004008000b0b41d181d075403d003000340e01c00c0d41c150f0b1010700c0b104010030700054060265804e00b0841383c000040410300000f403443c2207034295000b4a2210440307030621011889003c00c030041d0003041d020340d075404400866490014a82198902504000d921002c03010301c0702c0e43c40e1303400c4070030222074161245100440d0040303c030008020a01035040812103005c514141d0b0403240d201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 210714010 1250 210712760 210712783
    0x19050301061e090605030613210f1d090c070212010c031506020a0c0504050a021605010f0b0f030c040e03130602211309050c0f0d0e061803120c07021002 67
    0x400c000b03e56511281d812200d0700e12811b901500315000160851604c0916088e2450241c84c0180d504c0c83c2c0ca08005182155444840000c0791481141d0340d0700c2c0354400c2c0d6100c41900d241400c120680758080000d81150703001440850221000202d80d021900c0e480d115001100c01c00c00240716003203d4102c05009881c060b0351505003291110f0001078110700c0080c0160300c260b005007807065401e047c402800040c000040c540b1605603000c00c051080010350240d20910180241d0002884400300d556003015205c1200041c2d20400300a40741d040c80365000308980600030011100051064915855103046005106510a84110b005000141160040b400d41008001e060040f00900c0b940e191380e41c024011034401612102591009008000c02640310641020079040f080e424800c581703650700580d50080541280301a29040c0c0104001402c11069401c141007071800f0701d8400138601d11542c0c90040140710540405140003082041e1001e0080f2000c4907005002e6481041c00a00082e580c1c0110303051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 210715260 1250 210714010 210714059
    0x803011706060a1a070f050a0308060f0303070506010e0709050d0804031b060c0f02031f09060e060f041b0b0301060305070207081204050d08040e100911030c07021905030106 76
    0x10410318140c2190f105a403104000703007414501c0400d04400e40d40042c0c4d030031200c0804260136000440c1003000707491007a0f40309645113007883c90724234140015010341c00d42850013581f081c4103240029070b0100e040c5040d030b840c0d1104450946d684030b00840702c00c1c19079800365802003443c459090901c54500014400e0707a00840c05441010b041c40075000345445d0b079200303000000f0110702000300090a5150b00d00203290005040f2000c1d11001c1c08246250940801415529540c43d0350042c10840c90340512840c0c615100d015010910b843c1017140e07070119008000401c0c5200c402900103851500b112000050030040c001a51250f1712004040d00610b000e581b494054807540200180e10b00d40042d0744080d01c0608007485040928100c18012000741c00401292820420300001c5400c0c2100c0961600c5848404402204507181038600c100301e0f4031400a0f24a4070504204010800010508840b00319038180d4020344149000030181090001d00d410095265081810001300850782510b1094403d0f041e42 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 210716510 1250 210715260 210715273
    0x1806070302060403030e0312010501051c110c0c0915060c01060e0103060f0506150913060902030c0406080112170702010c02030f01060906062303191b0f032009010c08030117 76
    0x540b600d47e24002c40c041144140e61403001400154480c1c00642034409242da0005200702840c05480d042c0d42600300e04034a42c00e008600094000d02c02c005403a290306040c0e1303240305c85040c46041203c02180d81c0c2201800f400d800108000c4480c0b00350321600041404d018011180d5850b450030310080d269440c468101203003407c4c003240d0146000f4481da00d12a0108400f58984039074642846040007240000381d0034940d56030030006119500e80000c43c82590004801e0303584d181001d00241c054203068002c5d070010344000d800000054a05d80031803d01d14043c20b42c50b034a0304098801210015001c1030001c0d0140100c0c245074200d040705402c40c05c1170b00c0f2503000502100392190021200d100818501001081d080030402010b2101700000303540256603016804407048460034144103440110000780c0510840c441480b06595002d20507000020140c681807012181000c0b120a44081c8510111100040043c004001d03a0082101c007420980c0440c0094496a64590710340021b00f0108051101c3e0080e007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 210717760 1250 210716510 210716531
    0x1170c0307080609100e07030b0a030c08161a09040e0a0303060e0901020c06150d080a05040609050418150b0d0503030105031e0703030819020c0d02010b03120a05180607030206040303 80
    0x5240c1940b2900c01500c0c1070302494502030f43d00c04005000b1f0080303030030301d83d0b624421991901c0f654102c20107103001d111655012442d240a403842d240782c800d188000d420b1000002d0004d14141c50707101905005580c1c1d069110101d810005000705102840032050f44191507184040540540041c02140c810303d064010710350ba1034039428280d2003850900300c02c580210000600743c0001865031090940050003000028003240c0c2c608145520880310040400d0012400704003403a400000f43d00505016503003030024a181c03d42c0d810900c610018000e20074510b111200d0003d68080d400495401d8009110800581c01030800c82d440c0d40c000e009490003806520031520000318891b801c80301403d450002840224599182190320300c03000340000d00302c01095071840b40110010300140180b1484080500103540c8180400790855600c1c0c02d06600a400c02102c9041003c085000da865020040c141b86a941c442c0e5601c1840050589119984c8a00007040580074154001480740c441c5110303850130030249841c3d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 210719010 1250 210717760 210717769
    0x10c030f05011202060706060f0b071e0237060c050f0114060d080c01051602061b0a030c05040f0e100b0408060103030e030c034c0b01170c03070806 65
    0x24061038510060314030f400c90043c02c250004105150240b500020041c1d1250103150904015610404d25034201040043c103114141100c561100e01c51050188218140c0e408aa9500c0100c91520144690240055440c0c0304101040c034043d40c100380d156440f41e445040152a0344002d0307034261510b101e038003106000c4890501c10140c8510381c40742c80c980c2517550941040303002051201c04851750101801410903800e42405007600506100d400c070b020641103071a00a2a00800400714040303803481c103001c070b0302001e044400c80e540c03651189000301d90b4146a2038251420300c102d0f88107801c0d6010b42d03800010900d01c0f000c603003801009104404015203589014003801401140540e070390980100c401000003d000e135040860454020301035540ca072503980006410f0981d502c1d81110f041e560710108101840040303408100c003003102801c0745130600d80b480c0294801c00c510207a61404550300c4e50803601580c0210030141160800511840c218a0801d01d8100c003504140c440a0103d00e00e58080b0f4000d281 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 210720260 1250 210719010 210719021
    0xd0b0a0e07050d02040b030304080102042615180a051504050607080108030a081e04060b0a1e0323060408120604060506030601030f021902060f0709050102150702100e010c030f 77
    0xb0003c2c1a0b406a00b915020003005008041d00709515101c20400080c0e591802e002900040c1210015407515a00e11301809440e102c00102c1d01807030340c000300400000028180481c40c0c12440f0b5000107000e90000c01c00544c0352003100398000e0007501c40c0c6520035070701c0303203260104622481c8601d064601c5901c50b1882078408200c28040d10381250424014685068481c0f607050b5444148038140c0d41c201c0300243e0710181d40781d000f0744081da42140c031100300c0f007220704144030004024080740d00c1c0790020510900c03100d031000328503010060404c00301088912400c0400041e0080c040740c004207075102d6040070b24000c0c4056001101c000302035880b03503000462901c0e140c490602201c0d03002d040b0700d1850341d03410300440090a5140b20301114503400d02043d000c1c19190103000c0c0d4245455002084241024070702a882e40e00300038001c0e400c10814003414010307a40e001c6201c04801d03045c0780d50441c280c0c403112400d80c140303007030202c004440514101d99203a550b00150000781005100c0e44080024580e181710b400d040d0b0340c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 210721510 1250 210720260 210720269
    0x150c07060801030519080d0504080c0c030c061209010b10021b09010b070b090a0516050114160f030201140f0f250c030210020d05060a0b0c0601060f05090d0b0a0e07 72
    0x80220301c0c401c405848405c0c58260141c0f00740f0391a89410758202d10002280d0054074151201d00000c24412601242000b400c503860030118024980d40201c2c03c0062078520941c1c03a40c40c0c441c40d4900100d024039009400102c0158030003014030405240740701c030003552105070040e90260f103c1501c0c951001420680b03006816102590503852a0055584815000c4800038004003030920072440c1341008a201031240d00f4520301e8000000d0710440ca07000004144401d41c03a51118550340030001c1034194800320682e00d00d581d9000d0b0808505040904059004005042110100d40d000b1400c00800c030741d102240364854500c4a443c544039841d81c4980d03180d000d6900220038080c40d091890144298041d48008005a209204960700001c40c0c03030202c000ea0300701c91040d90400d03440d40d041c00a5854600994409004c400040905000440b0300c9190b40d00018450314092041c1d05522000080c8104112501200b02038400c0c00d90310034518000d401d02c20122956402c291030410450010312003c00c1100468 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 210722760 1250 210721510 210721513
    0xa06150b030106050f07050f1c0215010803191808010504021e090a0b0a03080c03090307150512130501181101020a0201080c0921030706110405090420150c070608010305 74
    0x19004040e800c4480e070120380169120310800510081540d81040017155034030410000c2c0034409d0364810b010b440e044c080c00e210040f0345010b20050001c10000402d0350070050416403160204003c0390030696070000c2811541245540c6100d0100380740c00d0542040340521b10945520320f450201d04840c220704a0606d00d4a41d2207030b1407502280510419400502003240001d107038440c2255a41c0c0d4042840d8040901e4034601e403c0445c43c40820316040c0205c80c0105010f01c03c0c0780241c60f51032002022031140020104d012102d00c404607035440401c6480c0b0482c581e008000308003030300e0403500228568a0341403048410340380b0f515144040e54804244484031a0381a11a852181c50308610300304180c000c201c455800c41e0404122284012215000351103095a00c0051640c0c1c2e03100341000010b990100035260780f502003c2100300700b961161080c1d075501c10741240a443c0740815005090410790640500903034400540110505000001c6008008a104480c1210f120954501050340c00d00805d22010305035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 210724010 1250 210722760 210722767
    0xc0a0302091504020f1b010506030304151b0812060a052b0f020d03080f070c0320101a0a05030c010c1407030f11010809060105090109020a030605030a06150b03010605 73
    0xd4100594801c10840d0000f8009030601041c142c4d079440310341000b42400c0c1640440b00c04081401c0080c458560054001c1d000b4500e0941071840d504001116003c406041007ca03210b00c5508103070700500da051244d800509159101541415607224040c2900d84611171a0b215400040c50700d803492807c0d000e0741143c80400485001a99540c3e1180d4181405544c3c0141c00811000142d50305480120410701c00d48840205007000a056122201c00500d1a020701c224051030b01c010a800c04802401102880b442c40c001d920034032403950a1204198640036040d00b4140d80204103a04034401809000044c1c6002c21840c0c0c0d0740082681d200c171101591130119040d8116440800e4411611004a246401c102d502c01544c035074801d400c4030102c40c420340d031010281c181500e0541e03001001e42d03000703030514008140135410714000075020031040c8119804564001904511a8020b8202200074080242a40c1d040603c500341503000d8000c0740f41c2c550010a100c10046188481041924141c45040d99003d04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 210725260 1250 210724010 210724021
    0x1030c020a020406080d1b050303041e0b0c0a0e030111041202060c03030702030405090601020d080f0a060b040e0403021203073203070e100207030201020c090c0c030a0c0201020c0a030209 82
    0x4120014400046001d075044140240c1c849000d454004c006a40c0105450391240000a08894115000500303074400351031242d0208100006690b041504401500e521002905000b000c0c51848800202161011400c00c0081d150050103040c0901081d00d84082100c4100105400c0325000100401c51040602080c0580300252440350b003820310262134903103090f001c540618030359001241e08030010307403002900b40702a041c0b28105540010082c0020b00509600070b402610900000f410b060200035240c00041050103d5003250008010401080380d0b00ca80b1011491081c0004a4055002d8480c4410711700c0000c5102e800c8034452006565072445202200c814080c241c03c10780544820154046001840c2502c104000e50203400e1341e843d10a8906210f005004140c40ba2401a03000d6400054041000d40d0700411700b05400d80b02204c103100b603a03664501e1007289000d0036039000383e507110100301d682945410081141a09000341c003242d100100c01010082009038601000f03400c001c0641c0802c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 210726510 1250 210725260 210725267
    0x171503031b011503061e0e03091003020f071a070203131e03060e01020a0306090606050d05040c09060e0a06090203010501120f0f020f070c050301110f0d1e0c0e1e01 72
    0x1540600310000482e5582c081c5224000f480c4080e041500d5556441c5941c4040380814440c20b02c11000107017041c000c00da10080019103e000f9203038218001d220080c0d0400d41140309234100d800003010b0401c1c42d51a070341305003801c8169400800701940516140008151102c0c00001661044204260000315280c140407000600d40c0d056180b15171080081d18000c40040c0d614051203040d800703013000040e241d030364070540142034444035400740c1240c0e07107824400d0028641c0041111054101d12601090540344e0780b4054010304402c0e4132410030301c4e24046010400004a0031160f02400000f40148041521190940708920003032141b6804681441d0404c04c0c00c0c000c1d0b0f001402c0011440000044095000562209030b070701a04241c0d028240001c0e203482004180d0240a01600b030a400822402502c2400c1c3c40c03151144821400c0b80c0440402c0e01015821603402182008170b500e41d450f00c0900039448490050845425500003043d601d0b03400d0350007418100b80000003040c401c203403207009d95030038001035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 210727760 1250 210726510 210726547
    0x70302100e03010606050d0b0f030601150e060a0807021b09011202030307121806091a030c07150c030c110a0b10210203010c0f08041205041517150303 66
    0xc0d4240403041c500307241030356828460b1000800e800d0326005e5840442c568440121914219079900c00c40d60995040026100011034078151003039007410105100c001c21095070741421820034281e10260000d07031712a145a10071159130003044290210b030b02d940b5000800c0c029441c51f0b03545413500512101c00400a01203c000b10902d210300180551389440202d450304420340e546042d0300310104401e061125007810031080c40d400101918070308184030900b0600405c071440d540d8510074445110100200c2d45151540d0704641299500400540c00c03511614a260050310010b403009020030f1801202025140c002c00d4816582071103403010b000342c50f0407a9500c1c400404090700c8404170140111000c1070603010b1070b0244c1c402030641b49002e0b210f86014410142540d00070380c0041704001100700c440305216080b40d01e031600107500518103050301440302381c22036850080d03078421011803218144946620760000810000845200b0f210031155541420700e8041c0e81e1641d480c40e815600c02c020900034456440e02a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 210729010 1250 210727760 210727789
    0x11010503070e032b050f0301050d08040503070810050f040305190e420406051c0f0f060501020304151d03060906090120070605070c08040b0406020c12070302 69
    0xe060030080e020b0100e0b1602c01c00c10303c1040800400507205820100d000c1e030109804125103041450038003190008611804180310b121700513441c1c202000708106c0f400050f030b006008050125018130742d0380c0a26994138403100d1100d403804da02e04004501915032455a8911854158640500c0c102103107180401e03c2e112503054204005400c0d07a010300aa17503001000c4108480000342010034010389842103000b401220b50032441c04008401e5074124046002513408890b1281065921078030b04801030782c4100345080520951603c1c1030500d844d420019440b0401c004e00c03819042101e140c9807001645c4d07a200d24011031004c2080b00c0340d8100100d10445030030350705012420134500c4140403100420710740581610400210b422103010084404001d1148040c240c2400c14843d400f000409030080041c442c01030003130942a140d0740007429131780c02404000039482e03100030306a55995a50340c41ca44160001d00407900140502d0030400000e00c1e18085c0c0344189103428016040039440c40d802c001445c2e500028 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 210730260 1250 210729010 210729017
    0xa0f02130e0a11030702151005010c0206030a140a0911011106010506090310090b07080703050f040807061404061b0504051c02130c0507030f08160305090a02030f03040504060e041101050307 83
    0xf80d41e0900e02008001c1e43c02451150028020700d0009000d586800800800700030500070540b008010710780c0c6c0140d028084540541f1165030700d0300c4129644014080b610150b10002c6034050034403030900a183d1084a12030300444000888508480044411491880f4201202e45c08200188158030f0b04500400d4400002401c8900c1a14a040d1400075148049800d54a603c0036000300030545421640c81d952185080c981080300c1c1c580200a10403084000c1d1019042c1e1001086200c2001400d0f405880c1c5125001c00d002c1140c64285006406800d05140c05080c0350f60740040080080e0061040d58140d407002801094007510505404c052103089000503a400100842e402d41130203602c0c4a4003400010300d686455860420b0f041c050400001100614204500300080000000919003401110b41c20b074070703001c500f81d1120300750b40345400b0044402940c903020303c54074982c1240700000100300302c1c1c10546081c07000540c1c0c2d056040c4e03140ca04450260004280d0101d03c1c41079031040c030046a11841c80d04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 210731510 1250 210730260 210730271
    0x90c060a02192006040f0608040606091410060f0903110415061701140d0b04020a0b04060c1110020d030506011b06050411090c0d0b0f0907080a0f02130e0a 68
    0x2d6010b05901c003404140c5092180030503030003864000d60004510650242c44143c035013031602c40c8081d41e10001d07201d03510801010402150400c000b680001c00101004441030040024a480306034a00f801031b01c8401042d07080280002d400c501960149005414503200d0312161071031500c91021001a00400590140d500c41e0804000c40c0281049000350400740c4c4d400c0d1442180450700001c016042c1c200010b040b101c031070020155651007142052203a0701408640058485201240c1031413025082003428501c041000b0500580c0a41c000c03100e10300500104021000e20002e00c070030010035441d00c5006800900c1c400700071750b001c1d4000c290845018503010802222408684281c61030045048a05649171014001480050f400048015a0465080265003410310404100740301d600103d0a02c182c9940e0710762044d0f687c1c0b04400b03502c14005043c5106a00c0d2076180180b84100071079407111914907141d4050900d020b13030700c00d5801905041040402440c144060a4460500180400c012035240e1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 210732760 1250 210731510 210731533
    0x9090a140303071206120816021201140a060602070506070302030d020409020c0c030c01050912071d010314030705060403031a04111806090d1707050610050a050603090c060a02 77
    0x90324000c0004200310040c1d52030f41000c20b0000c010001540050844030308100c418031000c030a25402401070703907020101d2135458080180e11217071a1549100654010701255a460f051101900080000c0a04220341c0600341d07a014150702c2187d0141c0500d0005900036a410300c09030030200700900301203000c0d004a07810440d1400303e500582e030258001c4c8032102e40104000b00c20100410008003602001c0b00a0040c0c40316a10000340180140b01c0c54078422070b40d01620044c01e003014403d80001e050014030040d14040310741540c0d10000001c0c8030880d00040700c040540100d10001c41981d038050b03405401340c81c1ea511a900c04038040c1003040351074641d0b0f00d40e100800f4015034803885800c1080c03840b01c55003520786010351120003016049881c1640511010407c124860303445c0d95400101690014003040c40000300b00c11009240210017009240d88105802c0c020b50040201c4280c00b00c1d5000c0b10018046600c410901190b03010984100100354450b420b05103084c40d15201420024450303204686651950 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 210734010 1250 210732760 210732773
    0xa060b061303050d0906030b031b01173903040303090606172508070905042f03100e0a020f031009060209040609020c03040902030c12010e0601270509090a 68
    0xd58000c407801da01102da03030815140c203c9517000080503142001c00068050202103a198842c21521032251484100000e00c1031b030003402580c2700a505c03108401c6851500a505828034200c01c0083c0000f110400c03082d2200b0080c50000154001e4100c1c0c109007162119501500600384145048030382c95190030000c0341c1a00c2c0104981812140c21000341204812000110b80702081050204501e6984040c140440480000c1c1e182c200c1d014404000381da40c2d0f0320709052410903140581681000c000b2450f4040d81c04984c3d02c0000d011104800343c03000e51022010100485010f0780490300c464001c2e070701001c02351400840e800c20f881d1016003a18100c0c0c40b1220035404480902a085a0050b80420802c14074181f070320a00d0060661b08404500e002c0c81d02842d540d91b03010303c0c13113600682900000007a400f1015181981c4c240c25048110491650310b070102e20345140b10860b005070000706008102111f1414039503102c40d00c20655501d088110f8244414800c201c14010040181481a80a07510000c1c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 210735260 1250 210734010 210734047
    0x20f070803130b0901151205030c01020406120c02071a0a2f010b063a060605030105010e0901050f0409030219060501050a080604030f08060d020405150418050a060b06 73
    0xb0262100328a40760b81d00d03210242907000f0b012950543e2401078075403465041000b00406403502c114409140c1403807407a105255124126507041c1ca03500224000802e035402c1051403024a55a0006102c190300c440000c0b239035007039248114038140d50300100d003a04ca65220401082c07017a00914003103006030010040b940321200e03001818084240318007602040723101c1c203205078000c3c0b000440e40c0e40d2604110007134054200d24848030407207030100d84108900c1d140c3c0c1088000d0345103614007002030000503955400905103070000d1051303501103030080c00d8030811883c0c0407804e2030603150010902c6800c1c902c5081440001c4c440b800c07040b002d500c5200c0f0846540e05c2403000000f0380c0e03441520040f41644c18041445211242580000941d6028000303010000c0d80100d8040c0034000b10345401e41099840800058a4404110000c2d40052811061106c11444800e0407143c1c49815201448040301002544a01c848040f801a04d1034100031091800158140c00c1040030701d070300400013814802e821200e01c59404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 210736510 1250 210735260 210735271
    0x2012c0d1104151703190f0216030c0e0c161b0302130c031103070f0e0a1509210b0402130605060c0a02040b0604080a120207092f030613020f070803 65
    0x9503c1141044420040785141c90400c00b000b0156041081059440c03106e50903600110f4103005c03c0200c81901507200f0490303c0f005400100902080d0303036880c10408c0880c106402030681d200d102400003190140303e83d003294208807404060402d1a002c1e0f4440942d41000351607035014402503904004090b030354905261803041041c0380009415044038001030120f41200300180321518051040021190304000c1d144610074041c01c0513200507488800013485845560030640c02c008515a240303050590108807402500c480c00524480c0e00c1801207082c03204598150003d240c4c0100034002001401d100c83c01d000b0004ae940c201144060703d03240020740c0c603008090503108540c0704d000d1100c01c1d46024041d000d05540d05a858074a07160400d07079941e8803036521807006041d041450f0b40000001d4030801460000b04078600b0100000381510804000300c1002d010000105d903415076603010051001c00441c1c0c064003004202921324104280d0440203074010300214022083d0520403c00881d089030300651055 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 210737760 1250 210736510 210736541
    0xd05100f17060619140301060902070303090b0601230f04030807030c0309050d0b060409020d021e21030306090c090904150e0106140609030f150402012c0d1104 70
    0x24a220040714940300000303011910440b03400340300644151288030200d040d04d020036250284441c0f5903001c64050891548001e041910015060080c15850b5001500080c46400c1c00c2c0d00c0d5481c0c1c41c00458a400c04070f500c80304000c0e002140d484054018100a08040c1071805000c2c0c1401c4d40d035201c0c0e070301035000180e055004c0340e540180300c010164015401c4010f40001c55000c203652030203441c1c82e1020500180f0b01d900441d61041240159034481d52079070000c0740d0050200035610002c600c45080c1005da141e105020b11a0150f8a54600e8403140d40d00c0c14815402d8011400c56954101b00040c4140152107491422010440071202c1e4558560561040e4090000303000c01c40070907940e000c2115401c07400b4035032607450208280001c1103000a0135804640450352161590300000c0024188070020107002e907644203440d5452806807407005500e12580c006d0f21501032005400864400301c2c04030240512040c9051905800e05192002490241600598440480111080116049489419140c0d505 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 210739010 1250 210737760 210737789
    0x40c0e101701170a0b060f090115090b0f0d0903050f030103080a300c05091f08090a0b0610050d0509010902040e150a020c0c03031204020108010512030d05100f 70
    0x10001d0495400b40100701411414003102a40403400d40c85040c04040200b05001000114055558074a00c80030001030040010800396513500300d00310903128915182c000714050000003d41d05040f00b0503142629250600c66160811320145a001400300000c12001d0100c1482701b003d6489559000e0350196206a6201da501c04520308041e001600300d13403000d42e8031500e144d042d00403131807a896074003c04402d0142c042110000c0100c1074440c3d01881c140c540d0415040b20131412440e6924840c14100e42540d11101303c1070f2681d80480d0346030420f80c0000b400d40700a010110b00d15003840703801c81016100915001e0b080241080300101a80d0094070708401c01d070344440d280c1007980307080d01c10810404c02c1c00006044e0041e0101003032006c018020700300190300c3c0c1d02154003d0411010720040c81c5240c1c0c002d05583d078039a201d0f40d042d10a02c00590f41607001403071081c0040303418200f0070701c00b14003c0303e4000103604101410a1080142030000c00015014401c00e400142c00d003050798501f8050580585200c60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 210740260 1250 210739010 210739037
    0x14040e0609100510030201020a0605370b040203010305030a0f03021312140d020c01080604020403060e030319051003080c01060515040602010f060501050304030c060216141515040c0e10 81
    0x82d43c10141c1300b0b20401044a40800045c2c0c0c000641b0b48025600900200e529034480c2c43c40007002c4a01c0e440700a1900400345020220031100b1100d001c4407c01132401c00081e400181404124003007408000d1040d03008000d03c5520901404000482003aa8035000d450000500810181900940d01c8041c007200070311040000c0008602c00011010380d9040249003000c0e51a07002940c4112000e0110f052204090100d00e058455030101c80241d1341001080c040d0410f005410350b0749510840f01246000e03500500f1440024190003403d0141400c0603000e6502e85c1943c45200c00c943c0040c0c001401036590782800034a540b01c5400010100c0000e10b60070f5296494003001909641c2c1d602482a05d80c1d03d054010f100c11781c2c02a040e213801981600c0c00200d10031003407420000078411041011a83d024240080081203200a04101c0d1200402d00b07507518903a10f00c941060028065988184091100340a64010b041580c000e0b802c04d4550300d410242d070724810012804c40300c0303c8811034000030411800c981 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 210741510 1250 210740260 210740293
    0x11130c0e030111220905090f06070c0209010501030f0b0a0608011511070303080c040314010203060f2403190204081c0906080403140d050901140702030a0914040e0609 73
    0x380040001d900a003c1207003424a000101c1c03081d02002e60740540320051354050404080414000f901113413404101c142002c1c2c003680d9403803080c2e40c4403c103180b051600140f0010b100340440c502040c0d0103805502c0302e03402c05005401800011701d101007825582d080162081d6541e80c0440020140794413001e1880d4104000000c0206980b90b45078180a146a0140741c10140024503004803509441e0400081e02c070506802054440c0d584054030f000200b400d00310440f0300c103600950080000321071300d8400351000b4080c49245a034800c00145030340ca002400c4811a03800e10019a4043d01d801204981f40700544064401c0b0381007500b000000d80d001e01e40014100f06840c1c000d69400603c3d06001f81440c1c80e1040080c10050010002001c0003042e003008207103070f4012010394203030b88860305091005103440d0807114000d000c050700c40c42d01020b066020800040c00807080b52800c0c0c80c566600ca914500b0500c600101c82c0d141c01000ea000381d83c80c101d8100c0d822080c0150380c00b400715030703010341051091104a074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 210742760 1250 210741510 210741527
    0x1050f010c0b01120201111e0c090124090f0608010f2108071a071806080c0a0e0a0e0c0403110609180601020109050607030c0909020304020a05090411130c 68
    0x154184251502800045010300340554110362501d20400d40d0213029100480304020841c0142d881c501c40c9120000d0440240d200b510b803035121680c100c5100d09400781c108500e50b80b0030310030326901c240140c48200714411001b04e000001001c0d400c090b10340c0e6907904070700401c0b02f6695100309d00142c4417500602c1400509000a001800300c41290050801c5c8030350845e511044205009001060014000081040c0318071101031009090910f00740d94600050b0150401e8008640c40c160f000740d00030b0204116002e002080d001d0880c10b0542424507020890549890700d10b50121a8051402d0a00060b1482044e8180b845510383c428159140d070300d1440c0103c5944015418035220b0300060001e071645031980c8403e0020a101810490302c59255900142d0040c403111401501ca806104100f101c45034050300030485035156903990103a1203548008440c01c900041c0c40003540403c02000820a81c41e20241e981c2c0c2160180d400401b045900c080000c94003201300545420803501d51009172201034010591 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 210744010 1250 210742760 210742789
    0x91806120601090b04240b03100b040e0f090601230103021c09051605031527030c0705040501080a031107080304080705040f02030402010806040f09171b07030b07230703080105 77
    0xc191b08000b84840c14100c01080c041c80044040210014610740d003040c0b00a4002c0828515141d903a0383c030783d844900705060488070b0658881e541c00c04200304c000300042050488188261804c41c411107403c101d81c3e607400360b0401354100368090202c0c44500802640508885168000c00102e240d19450301d02d040200c440b42c1c502c080101c003c02048961000300b800f50441d545208810000d5469803215441801c030780235810440e0b0000380e441008200000018001d0034483c00490303100c15a20130401c400c2c0d0f403003405140800d4218013404000039019040b80d404a0038010165010540c851403503a141d9003084c0d1021145038440300040059023010b10628a0000041d48254a0340c51f068001900e030b0b22010781090300881c0d541e0031081e0a6001c036485600029402401d21801e29001607050481d138014480a0a040b0b03900208940002e00001d100381c204d0b40e202e036108200d40d45055083d0b0b1000c481c580402c10514400009840309080d0308010b04803a8825103400700294184001e204410300035114 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 210745260 1250 210744010 210744041
    0x301020c0319110601061e20010c1107080c10091509030204150803070f0606090c0309020a09061802090d08030c0a08070f090b030405030702060318060606091806120601090b04 77
    0x10300c29158019240144541c54460400c03191144110856560500040c0d04003c4608c01d410031444000c190000321000700c407036503280a003250100802d620b500c2a446940d00e2540b000c0700114140c10034040c1e02c00900d0003410901c2184d07998041012404031202c94050011706080e8043c403c51800380b080134600c1d45000d0309a0142410001c10580d28460600003038441d00d02003080070100512500500090140e0240905c000000d4031000f8002e800c02c80d600b28801c01003000007041c86d181d9489480c00710f6a1024403c0031007014403500341e00070761042d03000c3d40e044403d092201000c245490002d5004840000d42261340d894400d0004146030009080310301004418039801c00b1132a030160b00d15041e02d1031501199684d1729a4a0020728600c41e05a0080d0818008030070000c0c10101d50000c060451294415240d440e5202c80030407415101e5505c020340d02c9101c074942c03a001c40070070f1511a40d04c40800f030855403541300e50300405841c140c4240c0c407005156441e1840740aa9042c50b024046010000c0d80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 210746510 1250 210745260 210745273
    0x6090a0308010512100c020d0e03030705070605030a02090607110111010b0105030a1d0a060603050601080a0201140d093e150a05160605010608010605091503060301020c031911 77
    0x164010001c0c076040c4181c5108006040c9075130313902a003c0c04130007280c4100581c00c000200c0d0404010b5260040400c90350041313040649400b01504001c01210220f59001010701000341c01c003c0142d030386400182c003000760a41e0910203241301740c40b0240100703560381c05456107800b070260141c0010030660b1803d9950841d1790402c411161986d03001030035650008060300000ca202c00e8041089120304104c0c00c2d00e0303401c80c403c1020103000c1c409560300c82c0781940d00950030349180d60381700c40d201c9a0300c0302c803034000a00082d070790240700d2655146480644a8400e6100012400e14800e480301c0d03640e000d0004011007440c251041c0002c80391241940351982c002110301c0c17441d041401c01c0028060700350004c030804200c00c00140c4402a00e201d941118110a503d204802001815003000c0d0001c02c000d004900109d40041c0001c10300d503014800780d80c0d04100080c0380030b850030150754103c001c0c2c1c1c102403c85a015034080c40349003180b0304140041d044040c0e0150852100c0f10b50990020110a07410102c44425007008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 210747760 1250 210746510 210746513
    0xf040e010602070e22020405060609090103081b12042108210703060302130b012321011412010b04110d110705060f0717161409010f0e060904020c06010806090a 70
    0x8002170f1a0698044400007107a60b200b1011450603c1a000070950002c19034001104000e403040280c03108000c04501c0c01d044180120805640340b0040110b1034983c10103000404c062642103110740050400603003141495401c42e07443c5111038003c0c20443c03445508000b81c048901060100159101d0341d145030602800303103550040341c0002801d02103110450b4540800030b03843c0e4014202c9070f07282c00c118000c900d16109030712041c9a550b04034515507900030302e1a0751201060344003041102c1c1130f122046411840348022900304641e17a007131081c2003072031075403038042c00342455a551250b0845054955401961078141074440001c460b01d0001c0034801000030b0091001040d4001003a65201101c50005407241d1a501400e9078404c00100d01c002d00389440c40200f0442004105181200c14229141c1c000806107440185615014a18034a40000e104240d203481c018826502600c9428010382024601040000400d0582e481005400349983c850300040003401403c00c20a41d01400c1c00c00504102c1030103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 210749010 1250 210747760 210747811
    0x30f042a05010309110904120201051e06131506030b01021006262a0301051e07120b060705010905060a0e071401120c031a03010e120f040e010602070e 66
    0x150007094101603403041e4507401c000304401c030700d440301000038031240440c5041d1800741880c007125250f06005501f0600410034248900001690b00f2041038000d0660369a07e405000d0311100120700b20b001d403078880c2c3c503494030925040d1000028284a6401041c412180f90001e031501d072071f40180641291030030703104000401503500f49883c0611080c402c450310b642e91021040c54400e00d035240b541c0e200101d004080d1407400200c40400440e1040e0700900c1a035031440c102e40d0b0303203100c3c81c9104208010384a000410183c8507640c0313552052484540000c01807405400714903203800541040394513079500c1036900c0030301400300500d50744113402070301c2884618071036100d642e101d008502c196662100f90880158003680140006508176601200802c1592868035008018101c007440390580381e0342c00c80341c200d80c1e82418050b81d600e8800e090000e1401c2c412043c640c2055511000c1c0120003020309100110b600d10443d00814000c00b099801000c0361030401d5000000e024001c3c14422400c0e219130380548503660b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 210750260 1250 210749010 210749093
    0xf0e0307030f0305130618060e030627060a140105061c050601090905130b06030c18040f0c0906080d1707030f060b04180c05070c0311031002030f04 65
    0x510420302c40c80510580703015240390141c13000b1400700310720030035000c961590301c106a1141c81c0c1001d00443c018980e1507106503000a1248022a00358100c0d80c0014400b8040311410f400c11344801045101502d40d00b4211414807200740e64a00d00e594a49160b10001347d400b074610350145c007003110114601034424802e4058800b0b0050401592500d44000490580c00350070800c00500300d104081c0f03c645008481803d12981c1034104488241c001c502237081401e0005100c0c404907400745c510340c00e100e00d9118161054200500407641a0301c42e00c480e070005040c4c58480780c01807088002c0820070070b00f40814203041500c069203807010407000d901484151703080b100c601c580100b000e04002030b0001d170f41600e0001600c15030b04070081c01500001c00044241507a422001216442c0008000007010014104c8092203a10400f52960503200e005001207100d001400c84a090000c0c1240c0e40407440c1c1a10006a0b041280e2041000301060300304420711800741680000810301038082d050741d490400e5041d59101e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 210751510 1250 210750260 210750263
    0x1020f03031807050402070602070203070f180504151d0111030408040b09040603060e031e04030b0610050c1b0f030a030210020703021203040b061207050906101205010b04060f0e030703 81
    0x2142c2030000c1002448010041c100c00b4000790f42e41c40a0b8100074010317500a40040307000e40300b00800000c4900c802d0340084142d40a40d8091401ca810f003104c40c00281074003030000d650841403c0010b2040601512442440c904415180800b0262039105c0f18215001c900000354503d00070410400020350130790454064a2003082c035503488815043c042402000740340c00003000c0c54604080b04900b00400000b03031803541c901180c41181f03114400c0040f0164082c6100c01050701301e00a0106445103003210304103a40c4d81711071800398140684040c2041c0b81600502045003520300511036022a03003082020007070021030640c000e042c5580e141d50000d41d101c400030012021031382d0116048080601c00c0c024001c020700b14084440e00c0e403c241c00c140704914001c0d10203510a06401e00b0b0308003501d80104600c000c6810050007201b20361389060610103400c580300000410881c0b2400b50304080000d610450f80a0100c22141c10f8445061440161040701100c4c000b07000d1148100680310740760740c0001c0c2d03030003904e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 210752760 1250 210751510 210751531
    0x1b030d08190914060c03100f12020108070512010906090605031603021c020a0b09040c1b0201030c110f060103020f0d20060f030106030504050111040305030a03050907080d02160501020f0303 83
    0x400c0c42e0802001c0f0308a8111000c1c558003800c0c003072000700c45c1c08601460156940d4000004050750f20f026816468585104c1e4101e10b6002410038809580500c2c0c079664882c940342407540c0340c000703905007001262000360009144165609814000c41080b07205420240c9819002071001941101c001000340d02e69100082c0709001210a040c8000c0300003040b2203040398040c00c42642c158485d00c90051a400232020f05000702d14009005900314802e202c1c020b80703180311400740c2d00311883c0d5400442c00340203400c203080b0911800e41509010a0003c03c90f000c2441280c4010705059419841080310b0008076244136446410351803200e9000c9601500010314038010050392415501001d80810024050340240350b540000c04400040e0b0b0179059000188110b01c03230002003001011003c1e400c0f12601a42c04003a055900070b2040103011070190b4089038008200c0400c680d611030395104624540000c01d094a4016040060301c8109642e000712418040c140034009000709024041c06ca41c1d5a000c02030426407403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 210754010 1250 210752760 210752771
    0x501120609052401050f031f0c2001050405070b090a050f0d141507031118150a020a030e03030c06070c030c1b1701050903030a0e0106081b030d0819 65
    0xb001000c10104144501925400030502c01008a00b4481c240910a840c0506650808080d840c0b60200f0781c40d0780c902030350a000602100d5820042c00510041d100141030040183e00c00008007201c2d06d8544442c001d1500100b0039140c140b4005080404590001040201c2400000c02654411040c50306488040d1022003c0a10540010f040411102c01c06800141c1e110b03c80d0544101c01324080010811071102c00e8025114032a04608079006410740480340c020911039403090380401061a000500028411420180034100e07400380b9500c00c030130328005648030300541c0c020180c2041d00900d80c2c2c94200c0c065070510310304406940d00da581c001c00050030440d0440c0c41404141c001c0d10441c504d207400110740c04146170000154500d494144c004ca0030b00070b04950f11203a01c580140507542c480c2441c04007840c11601c41c042c1581c00340c4a5200d0b5041c05540b1460042120740c020807804101040c5100552160b0f00070b44281800d04a030800352a0802c503c02d02048028000c1d002c0f1448041c2d03440000040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 210755260 1250 210754010 210754013
    0x302090406030b0903091c030207051c05070905061302070b010605070f050313061704050a0809030a0b1f15230c0604031e020c18150a17010c030501120609 68
    0x7400c0d103801c002d0564401d00c00340040380c080000581030a1509450301d4020320001807415030071020800c801030041e071200b90144800d041843c060351109030401048101c03070149640300d9060880d80c1e0000c0b43c01d17641d00c5003041118074001848481c48601c4c28030440c5801025104d5042e101d005006034006d00c000040c03280100011100129241130300718090b0390712440c40b85072144810341d42c2d00c180c800003074030060314042583c5040511401b807940074009092031500e44c1e60b40011074100c45040f55040c000d2040c0e240214062410b00c91003017004580500c084004482c1c1d205070829681c021070000c00030300c0c0070a0f0f600f541020008081884103007469800444800c4c58042d00d01c1031444528640c0502c0c82840101074010b02c41940055404000c80c081c0c0d005050100d030b0300c800c00f030380003035016208008007a484401030714140e03005440c0446241c6c1299050010480c8030403240d000c1c40081c0240700111b40040000c1c843c5011605140ca000e21a551408651144200d460b91010b006655110300303910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 210756510 1250 210755260 210755269
    0xc0302060f0606070812010503070603050c0a080c0c0a06050405300c01110403060902011205070903030503060a09141602031c020a0e0405070c060b03010c14070c0e040c0315090305040501030209 85
    0x300b13550ba01242c40f03542e440605494030710fa0442845518020b108251000c115a4000e0140b6423140140c2c0300317018145800301e542152042009003454110103800c11126410358000d010307024605019481c003203405d017000d280c06403070181f0700c488200d1000056150b08c2c0100503900200c1c0f64100840140c2500c0348244c060781801490381c2c1c0b40e142d184c044006000010480c042d0401c00409000740c0f00d100f405490020031304103460080f5020000105901300901c0000d02034400b45822400203800b034000c040d15000c1c0c00003100d28102d803521603010b0b080c003003010b440d005514440d100901880a1800c080ca09002414507441e569a810109c9801240c04d0801c0c600ca810303002c03010f280040081c0a1410621006000000980030540e00142882c00c801003a0805019420911205949040401c8000d00d243da0301c6400451040320007031030800002409a1078000030030b020398010442900c0d041e28514146122449c2490903640150401c52044003103904070081d6000c0b11800e0038096510501400000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 210757760 1250 210756510 210756517
    0x40e07020c10080f16120f060531090f020607050f0610080d05070b01060c0203150c030f070810031217011202030f070e0c090604050303030f060a05010c0302060f0606 73
    0x360480c012660100515500020450044101440458003911741c20308004403024062002c1012800e0b181d400c01e8989550740c07045000ba0038800000546c80d481d4400221805030244200d0315011200302601c642205246c034858003418000002c00005c3d4a96446030802d942600c03010f4440e2002240000070700405110302c0141140c108141e42e994078190039404070000e030500907000d0f988030b2515031040c1103014a08862809410561400460307280040031035680003a014200e27054060f000306409032102d040c2260303008603041c00c0026100e03d07000c80080c0c0b04001c01888001000050f00c1400f0100c2c04412110054030741040b81c0048044c51504180d601d03070361071980d1525000100000060b0045a03903481020341e403089040e2800c080380640070b05e40d01c810038080d185060302940c001c510100c104400500c0c150708060599030400356580002810f640081310764030090840d2100300402c500d04029080068034013400c04020282158070025691302c1c00411160340103054801040c030315960081038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 210759010 1250 210757760 210757783
    0x40b01180f14010e06060703020606092505120609040b0a092904020301200d0b031504030e0301050c03071d0d0b04030f02150105061c06030c0b040303110c0303040e0702 74
    0x9101c10101034000c40100d0b6024030443e5160b4980c100400c4891030100100c407909a0994010440d40e00c030001000340c0d40300003510180c0b04006a040045551031084014042c9000940319a900d0303044c0060301c4441382c00010203903031090065204020014003420850703500309141c07002c0000c0d1100d042c9002c440034900708124003104081c0042807410412242140b511032882a0001e200145510700c1c0800f007881030443c091541d0f0404d0001201980d0700d81c0c8010030401c002821140d40101d84260000301080545084c0e00150800300821740782d040c00d010b0707036400c03960002400b442c500e04a100180145280800c1100000e08070030410360a42d04c8801c0c3c12500c903002808007581c1d06142c035002c0c0502c151590400003601401408220207950110498100c413000b41520b460321084071303642000c0100c44601035150650310540880420780c81c40d002006003126862142e5030310b007182405000107140d007642c43d200c0e50081015990a0302c012041c0c030300b1181c0711a08000c03191200301e0f080e424034081f40b10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 210760260 1250 210759010 210759041
    0x504060e310b041803050f07060507030603021206090309242101060915030903020f060a060501020106080106050a030f24050106030506060c070b0a120908031b03040b0118 75
    0x9564010302401c06200d141007070003031082028440c1c0105001c103440c640580c4a81c0ba8400144600c0400c1c021002000f40c0c05c00d01810f80d10b8030b07440356a8481150000e444e850000b903901c01007441181008060944e102c001e200007003030325160403800316036a407003102c00040c01000c40047c14201c848200b200c001c444e01e0120a019160000c803418130f8118008410400d2500452000000b9494051030741001521008170041030b5003406441d00f58090400c0c041e0441c00c604c503225040c59001001e0203100e001c0e0040180110741c00c0d2425000a0964800d60001c25680c1d151900800842e43c940c0213000c02c49901000e501e181030814200040b90307000000407030400c5002440c00960140155002506840054034100159210442407061314001e134400703003405a011a009104261300c0341c0242403108420b280004154140030001d00a0703884090b422211854080305100180c9a0035400a4090140803036560851070161104e02c1d8142042c403c0069000c10408881c0603042240c1014803521113407103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 210761510 1250 210760260 210760309
    0x60f08330103020918072003090114040503010515030105010b09090a0b030109080d0207021008060306040f0c080d030204030c0509160c020612160906030b1e190303020f07090c0504060e 81
    0xc030300070101c110849009000410311114201040c0147e0100644000160021820509000300649080c04080241106100300b8000001c81c1e6a0034000d01d03200398001100d0803580f400308410326081d074006030408080660b0074043e96101d0749072203541d40c4e0301181c084000300d02017071108042801040411000351842200240005000586c0d4000f80521391007aa42c0c01041d80b20403008458041042c0c070484d46c103401c100003050114070025070b4081a18050f40b055145c00e5541c1c0d44040c94015034500380008030f50080303820018464644c2c14900101001e42e08011549400c900c01e0a55907543c074012000e105907259820195207a420540c2c012095406051805007030801c1c604681d800c142d0a1000004d84052020400301c0c4640155a28a00b01038203292040b401c008901044103507400656030020380b61180100b400311300c20001002140260043c040300c0f01d0340a009070500302943c00031046103080106030200740361b02408a03800c07161985081310140e400b02c4005050320107540f0802e070240701034a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 210762760 1250 210761510 210761539
    0x1302150706060e090c04090b0a24080d11011401031202100203040c080616140f0705011a090106050a02060c0901050d0e0c2e050c16060f083301030209 66
    0x242400d0040c41c130a01252820b040d90001c01041da07002d41002031140b03040002056071424240c1001034031140a010003141810615240ca892444580c01045283e1100756464241e903001640b003107220a143c4024089561382c400c6c898a0b10006120091003210f540c0840017100d07100307001c114031810700c8140035035403410300741442711180c909801181c103e07004410200362070740c10405140e05c150000c0c0e16203100f104a042e0b00d80c20070f50081038018401c510108440c40006d1002c0c40340c207844200f54956089000104801d010184005070440c00c14028200040c1c00c503160006803043e480b100240c0e00301c0ea242c0124004884501603a030001c0142c03030903d4180030815074089000260807800340d80c0640742540003288004003001d8208080a103c9801d250031a190744964024242e03414500c1c2150b002100142d09021040510303031256001030710b0b0182d0700d0346c001d900c80541500a0402400840c00e84e081611010703c2148070400100002c2c2c40f6060380c2e074264041d40680e00d012070010040030100c03504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 210764010 1250 210762760 210762779
    0x90309190906030f0b0a02092103091809010b011b0b070306050303070308010303020c06041d0907180c02190209060909160605040816031505040602040b0711040e06130215070606 78
    0x54144c21240c0004050004421104a1003640e4042c00300a01d02c0d14006c01a0b180f1800042c204e010000315408204031602c03254850002003040040e2024003815a407078854030076401c40d0a40400c01e03040100b00740315180d2898170342e02400c4600e600030704002d03000c0d1200c0380c06a0040c44d096000d00d8042c0800320380c000a16420450b09030490340280c09440707812020608228240c0308601800011200007008403001180d0410b078603900050b154200c80c9480c2d1220381150989a211444030850b85e2103421042c90103506000e5082000d80e4000c0800750032505038001070702d408000f00128010002000051900d8400700000b4242d80110380680d82d005480d29401071007a4813500031103071b803403040340b241c019001a0640b44008aa80200381030b40b08880c20030010015010107030003aa842602440041075038180c40c07008102c440d108000c040110742c402001d0105441540ba884840c40d0448010891804454140802e00d1541202c41400c402440a0030060f41e0141401c0a00700b5450b201011910307001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 210765260 1250 210764010 210764033
    0x140603010b030a0b151305040c0c0b04140f030706060803040302150c070302100c051504170307020a0c12030e010c0503030703181209060801080307030f0c03030e010908030604110309030919090603 86
    0x24503402c1e155000d504c07541030201727654020031100d000130001114100030814042a5680282c41032422404098400003824034048007038001090030b400014010041240a118400080c815038002d942018950b4000036410f00152283e800c11000001d031070211f0b4001401050080d69006041c8803800361001401803540d03502240072a101c0c4104c1601d110480720418495200b198007009108402400c0d07943d5400580010708080c00394425894040c0000d2600b031160406407441c85491440ea48081c1401070200602ea542d403410b110035030124401285000c4200e1368064100c0c20007144c7e1503500c0b001c003103503880060b02c0680510f01d4420070000c01e5511040940495a4a035aa074095907204c1481d075440b0300c220b8500501142e5000c41c680c000310300640014002d68020700700001d00010740c48020303096504840084560000001c20444549403910039070041c010300f0200c071411898410826540c2e40b080c050a0b40c4100d0401005000f03011180f0102009400300c0d0300c09103d60b82e40c1e442d09015040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 210766510 1250 210765260 210765277
    0x30c011d01111819150305040303050a020a020a022403130209010b0a050301060f090801090605091011030a020f07021503160c1e03050d1d07140603010b030a0b15 71
    0x1400c10000a411040101c01e40e8070703c070703200b40103072889219800030001080b0b256501c514041c5808140007862504640940d00b1100064901103018030306460020211840189900c04c094030520003540f00c0d03a40040c518804a5040c0c4d00401069032030440b04004602c410000b10701104000100400c4034501c1c46e8524a06100343c84101c001d03622210403003181d00880d00780f140092018001040040e12441d2800c4030341c2c90906000403400c3e1a40f4800b42502c81d22401503070401c2e20741040c04a401e80070085c3c0012507804440800249943c0791105a041c84061b01c4840c2d2240c0104040c59040155170803680e14950080040503061134041d01410705401c02c581d5003d61000c4060f103800094080c00e0f00700051944816180d6191012480e03414100314070700021350030041c0900103164048a240b14840c0070050403001d8030010030110111070b1428841d134002d4140c03410b041c10384074030075154441a02d0641d5207a84c811526a540d44d03200f0002005903400040e8041030b0040c04000d4038141c1c900508180 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 210767760 1250 210766510 210766513
    0x908030a1707020a0213020702010e0603151008060a0303030b030f03070b0a0b0d0206190c080313050609122a01320402220e1b03070f1a0c030c011d 65
    0x2907403014002c0c0e0302d804c13039088060340107010b040020024004a9009104040c414141040303454400c102041a580089814448200120308603010345d18104003ca03d4402c0149060403c929003000411055807030b51100800745a1a502198020354041c0a500561241c0c1403c40742c0300c2080313040000d0400350941c1c6088a15150429010300e904151461070f051070340284c0451311f010000c3c514a4411302041c4043e4007000040f080c0c0381d002a8156008500440c101c10702440c7c0e22040381802802c024001e0f0005040c2e070300c800280c0050b0410581603480d03448140700255031504040390079003101c600211f001c50f115442c0082540102d02c0000352044941d904541d80080006181029a4180c101b581c010f54031115030321381108103000b480301e142812808440c0200d50b0050044215251a81c24242c41c820802d04105d44119401d042001c10300070802240800f02c540d00d0281403401e00685c1c9002c000c54000c0024114003169810003c4820540000000704142803000d00c01d81040320190501090a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 210769010 1250 210767760 210767807
    0x30b03061503300a0f0f0503060a050105070303090c090b0f0303090901120804150302030a0b01030b011707091d01090c021902060f041806091a15090a08060a0c0f030e0309100908030a 80
    0x7094420405d0320304ca403270050022500c55080000540342038026110403020503456920341c1c400111301004500c01401c5444010480346048001c1007082d5000301d00c514025403003804510000ea5400a90306d0440e6000f01070484420f42c1c0381000200d0f486180c2203420440c6141101502181d8164000d40c07081452001c01c001c1c50b200c00004606407002094040d001500140050140341c401200c1a90440d209003000440140d84100c5503820044410312403003580124001001111200d005150740c0d10388500c00f50480403003001e041280c29241c0c102c080d016110104002d110101501d084074040c0c0884121901d11f0342ca000a000c01610103406145442401c09420b121100d058070340880803000000c1c00c0c8044a402c02d441c01010340c01440c0d1580d403140c03032410001f442000a0012601504405001007440d054150303000d00309200d00c41c4200105458000e124030a0180441a224101c2c422940c5100410b46140c04458640707040d08080c0302408000340b400001a04528110070100141004121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 210770260 1250 210769010 210769037
    0x605010509070519030605030703080c060a1812021603051b0103062303010f0c020a110f06030a0c0207171e120304020d0c030f03030b03061503300a0f 66
    0x1100152150030204006000c601131555a43c02c0310003080702c191400052081c0e6400c00646404115803064442e5040040c0b840701c200400d001140d4406803180050103580202455031240880d1070300d0140c0050b03000380b648407106109014080d605d525010007403243c02d032a0b04015031150000e03001c241c0008450844251254060302504045aa0701307281020042e1554441c0c952004a04c000c03a40e240d5038603056841900b65910130025900259401801c0d08503051a22003040042641003d201b204c0c8400050240c0d510482103e80c401c3d500180424030181c0110164901240754000c80c60300c04001494110040c40004d5544024800052004200034520100c0d501d0340d01c00604002e229208100160140c100741d88002e07529445900381084041da80d0310f81c2904000356840c02c0380040d0303d0301f22444880c40d00304803040d0840441c007944030070003e4501c00a681c68a850040441046080441e80341c558000c14a807003920b819250b034950342c1c403510040109501074062400001c600e0a200041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 210771510 1250 210770260 210770269
    0x80d030c0207090e1e060f0a02040311010c03170103120e0910030b0408040f0f0f06050c070911041d0402041d2e02180102070b1c0911030d02030706050105 68
    0x454034081034016103221410040000094110006800380c1c91250105440d00c1021245e0800e011050304405081d4904208a48080100c0b0107800b26505d14010312092002ca4000710030040740703139000d00f0400024282da01c0c0549035442140a89198109c1e140c00000500000c90925480502159a401c409100c2801044484982900c44400c03080d02044107100040c0080c04660304503009090a50400c1e940e891102e20301009a0402c400700250641c3c2000071820040d40300b40540100d040a90078500b2000302c469448060f07108441442d91240203118025000900722001782c5414900000514200d04031030881072000e407012802580703045482c40f1100007002060500b6000d071006000d0300c811406001007103549084041c42e008104603862280701d11244020040000e20398050b000840baa01c00190500106900c14054440d0411004400b41e021400058642c54807020000c0c0701c1d5401e0801024402c03611a450390584038035026611240d4001014006043c4a072100744a582c0c6c0f542c0a11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 210772760 1250 210771510 210771521
    0x1003020708040302060a0309120306180c0806281202150307050f0a1e0206060307060f20070506160b07090b031909050303010902041a0405010c3801080d03 68
    0xe414004180b10034801440d1400c01001d8801e124038000c0740010441c0c544c060085110b100c003401181d5a810f00b0803110f104e0f407801002d0385d54009070400c000d220141d4098a81c201c020700044c46010518805c6504540d1251a007130700340301400c413980d2015110800c45203082c44d000d1040c2d115511052504d2020105441242e108240759a02c0b43e0802d2500c280e05880b0350017884080703080c0b10509006070ba0104015201c92112040350307005000c5814900b00381070600765036410080c10000d00710b07281c2c000d00380c00250000a501c40041000405000080564102040d5803c10369005400003541d098814841c40300321b00b800c3c0580c95180031500c40103020b440c1c1c4501031040d04d5440409200140792000c0c410800c24000281c400042042c5542d0340d06c86085a009030810899213034081400d20125043c2d02d03042c0080d000c2050494a40340c06c040020f48a20001c1d03034000d1101e00f031080031507580f40551103220300d14600c0500181012540150809686001740141c402c60320802918440f12442030051 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 210774010 1250 210772760 210772763
    0xb0c0322060c08071a040b010e060a05010801060e0604080f06040c30050a020a06020303091605060f0f0d020304080403030807170a0f1103150a0e0f0a0510150c0210030207 75
    0x35885003034001c1d43c078000c441c1c001103030648810139100c510a1380e540c050301c0354a10951142c80060100e41c14a142c02d5800180a400395000f04001c40c404c0c451a40c0102e040f505580040c10b12880f04054400002c1040c07050703400c409018040d018100e04e020100090b0355004510818040c0362031612407220009010310481703140080400350b128003145109c41030350382c103105006a054400e8412182c003c20764800d8a0750204005034000010802184024405ca04070300c1899880c840c8010319020004e00507000d0701050320118480014840984c0b00e62604480d18001195001e64492515041402d82d1350891f20060300890300c004002090148a0541080c0d80210317800e409032543c960842c9440185529a000d100007561601211030020a00d006140b06005401c4000c85c0f842c2090244208074042d40d0049601c00c20100c14414540640140700c1e91107401301e10006001d0f03480e482910300182c1140c0c840c400c400c0d070011440382c0c0c40b5404204846060f000b520500441e5001d00c0c4100c0492003071240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 210775260 1250 210774010 210774017
    0x130e010b1206130f180b09010e030d050c091509090106050412060e010b03011e0f0204080d08060a051f17130204020706151211010203031005040b0a0b0c032206 70
    0x902c4520b0003c05420240520304000280c2044030100081180d12080070794100a65007000c01040000104195500500300c8009000010f00d0007040780e6240510148072a10340d1312003000600c0b01616505441e4030f0035000340340c0c903c1d0403104404080c1c25070140d15090301070440030001007002c4c1d02540c1204c084031031211410b81415160380300c180003051001034140f17440d502c0c0c15900303290356002d000d01e070181c81441f208c10306071907110700180c0101c800c081d1940e02c41a006000811400101240c3c0c00c5401f4103d080401c0700e80c2c0ca9034001001240d154010f1a0b01a000c00160141004130840c2c01548003010b4844a600103103402c00480144400c0f1242030b11000340841ca14010f003000e4000c0e2850521034003010480381d0010400781021906a00403030030201e0084000300a0240029480e1803c42080c00518950708001c203101036101841c4c061640a07039121020060103444000c040402400308455140e200c001240803079480f0342c00302d5040c2610840402400c0e039544001c040c0142281c0c0c0321744 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 210776510 1250 210775260 210775297
    0x6010201060323160807140a03030c0807080c01050a051e04171c020304120f0806060304080f070203010c080a06050f09071103070f05070f06031b08130602130e010b 72
    0x80321041600c401e12207081ca80103516580d4501c0010301c10a001405d13212003d017503054100304456842c401003a80062240e1419441080403d0b080440c420b40306400c10309490340c404050074070352202d204e901010007a030342c601030802c00052042e601050082410f031451112101501400c175401890584002d071038400c00c1c460f03814102d000300b40240401d04404681682903140ca0f541c00b4200c0c2c00881d802da89030980c89a01e018403071b070302561a10740d075815400e1081050030840e020840502005000400c090800519072840c24283e009a9910b903500400034003880e95000c10040841e081a42c0062019080075000b14203450300d070030801000c00014003003030040da03a004012512400040031303036a100c2c00200b001d2808a0510001c44900c0ca0180004006440c0303402e5452018038802e601100030580360500c420403401084107402c41541d454a44072174203486120703016581c072a50704001003442e840010910341c0401200e5040085442e0a40b1a96960f80d80d4201c494041c400e6109664220b04941e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 210777760 1250 210776510 210776543
    0x50115140901110a08190206010e01060f0318230304030209150f030a0501020c1603050c010807050d060801051504090309030609050a12080906010f0503030d0b060f04060c0b060102010603 82
    0x144041c108030001458200e5401c0c0410070201d003460044901554890000206458400032064012880700424801401d066140035450345100d8018040c42082204450340007108900c650072088000503000140080640c0c6450f00da00311000c00c1603101d140c000f4a8100700c58000e80070041c1c40c100c2e60080c003170050507030780d01840c1c420341c01544481da07602407180c840e14885520200401810030f4841d4000581e1f845400d24054944543da608050350500d44400501c002580031484a80300b4200382007102254450300d03803d0740e0600a08406100c003074505840010806015001a80144441201b020100b4140f0013400140c130347c05100940132403018007080001400350303480018618001d2094a0088803a0358540d00f920007a42c14031030000704e6080c2405444401840303464014160615501d00e1a0301e0718011a80303902420040c5070105942c5c0d08100a20b4a41c20212000001090003d580d1691140405804002030326015600d009c2d88500281003540144070f12070641e5000b101e00c3e40b014607170 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 210779010 1250 210777760 210777797
    0x406180f051e03030d142202010c03030f0b0907090f0b0403020d0b07020a060504060207110a0e0a0c2d080c161203020712080105030d0513060305070903080715050115 73
    0x2907160150701440100805c0300400b0091040003ca10b84c030780400f00540c00c000305c8070550443c40d9400080d400d400c41c070100006030380021200c01000e601d4100030403845140300425000389109421160456200d90800c101c86a0150a21094030341c025900480d03903803100d100d0803c40c0a1400000d4104040d10031580209440310038055110300d031351041314040015503840c03070309039041960100e80c16a0049103130340030044401ca1701e650404058510b00350301e0b03280c140c5080c4140000f406040070a80c0da903414114440c81407201241401384108a2144a00c859030107403044000c1d004081c00199159000c504100744280c1260701c3d04007407204140d00c2c891030391a09040007405210140915508003c140009040030780c040d4054a03041c0c07508440d640c54541858108682c15921700200101009403611903810791b00c1c1041a907041b482c0c00203d69842c3c050541f0040c81542014080300301c04a444020000710360301031500610302c128107001c140d0740c0340300d042d1074091035540c4000850052080710355100366 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 210780260 1250 210779010 210779059
    0x50409060f0e04230304121e03210e0601120605060d030c2d0605071407030512060a0308030406020903071403031804060909200d03021906020f0406180f05 68
    0xc42e4504e404400303011100e491503005034400a2080c803006107110030b0061406214501003400486070003104006e035801401038000030b46603c01900ea6130b04955807071405601582e0300300c89100c22203055584a0030502c00f036091207201140c09c0c40c2840009100d9042207602102100e0b459110b6032402103180c3d0342c2c00903040c045540e00d40c2100c0111030b844218100c040843d90428020040080e50f8100428002c0c8040540381910003034000810a410000b0f50210850f4004200301640080c0d41d1192000507000001960024044a0010007404184a0268003c0c410000110220b900c8940e0781c142000b404007080d00d440f0b0741a0018003c204048076041030550005a0049c80060b00c6900c4d28854021038480103401d840c0100309401ea040481e019485461034980308440c6035030f000c616568000c1d920f00c1c50b2500031a07070a0403669801300700100c07501a6074204510310703199902d56464110050005100c89920410b10090800c0050120031108800069410143c2076042280061820301591203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 210781510 1250 210780260 210780293
    0x408071a070c02011403010f03080c01060527060d0c06080a0b12030d110906030415110a110607031401060302070302030415050a1706060913020d0c050409060f0e04 72
    0x46142400c1000040c50456900c00d000c1a2a0442d440002e800010002c00040408024400e800c00040c09001d4042c9082d00071640d0000e0859662040d40d00c00070301400305580156081000c03400c0590040c0d15504101d0081c56091042c00c2c0c0550310b6808101c0629003420006d03002d0f440b514402d201c0300c0d00c034400c2c0c60751001c201880402c0001c03d20000c00c44000c40c074405580c141c0c2000c10b0040d203001ca00e00815001d211035482e002c1c1040c3d00300c4001505488054801416240c11510300c40240d03c05401c0218900790b881c02d015113031048820b02074008040c035009000140201c10004410500900c200309015122042200260382003001c160b0095101e64020390a5102c144400910000d159044c009030000c140c0e21191178110305680a042007200004049200d84400b08020641e1603d006072016548210f828203050603c2c164075000030711400d03242d001100e04200004070040e400100410403900c860b04100105582d0391074410015a19004260201080101140126540b25207002840 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 210782760 1250 210781510 210781523
    0x70f030e010e1606020705060c0d0804050703060e03070201030506190915050301050c12010503030a0221070605090606011202040f0311041116060f0b03033a050603010506030c010503040807 83
    0x104180441600d003c603241c0c8011a080e8119500384074081d070500c8000003c000a5035010308012000c07600c240ca510b202001b101c104802140042c0074840c04000e040e000b150040403c0100c400405a400e4807640001d405a001c2414903002c21303481d04140f5884011400700b03084515849082c000301e44040c0243c0d004030140020403071004901503074203200d02406608114501542c608600840d00c141a1059200521a800c00d210620b109500460b01500b0b20303841000b8207070791504020100e1400d0141c038038046d00c1540f614041020f03880000500314022202603d0724011201c403420fa4805078800d90091a10007100980204001001c0c002c2480d03901800820104a403c0403080c3c0120136004140850a07002c0081c005001b488044e2181c3c21a401d4030b210b007808400031840204c2e40d244680d8240308044030700a016148290f1603812f05031003100c84081a0203150040c4007424003d004c084d5041407180d46003602141e0240707400108000b0441060b12041c2c2182d50b0760b02ca03010349400031007043e03d15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 210784010 1250 210782760 210782771
    0x210405191206022104020d140c220c020c01020a06050901020d0e06040515150d060f0c0216061418040b04020c0706090e090616110106060c050d031401120f020301141e070f030e01 78
    0x255503170f145000144100d614a0b4280c0c1541240d0ac5d10f041e2031802070481e0545d00003200320149a680840d0000d00580c0150000c1056180c1072007060081c0b04000840d00c446161041d04001e0710000b0490900903030003241113849800c210006055018001d540c0740b9440b881246554449007044181c03007030a10701a07000094003c61120601c010707901100035010068002b481c1485210112000740c0d8080d16191501d210b00002c1c5080c0f26842d8450340311a141031810714007041c0007682d615040050801c00c042c00035911403c3c00040180e89410707a006582c00704000d4540810b04030056104984203444000080c07103035480e1180d52a185000410403602046460090b00c3d05405090007200010300480d41c4203410410319007003890806984004d00020507041034611801484108405410340e0350703103000b01002010511b0901c0c0940752446000f5015401c10f81001400303040340c245988506042c4501c07000f4608182c0d0204d165800441e142e1010800c02e01280304c000c1c1c4664440101c00042a000040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 210785260 1250 210784010 210784033
    0x10906030908120907080f0312010509180106150e060702101404080303040812130b04020105090d060501080a052e0b040f0212060102210405191206022104020d14 71
    0x10f980003194083c0140e400504100704a07401000300f000107030340e6003002e1401c240c04200050900c40d018070400d8812407800c404075440c003188541040c5c0308036400c40200500c60f9038407203c0c40d04500340302000c0042042c02c002e540042c102041155099a40241401300e10070b170310b0b40151021800300040c0180001c0500000c240040c0c01c20045004034010800f480e2500310f01100c92241ca1401441c0050121901002c00b00190940300825002030382400c2485d103941100c0d002c90b0b2100c80601c0c02412907400c080000aa44d03001180e2070117280e0054040c1c0d0000b80c1b4103640c1804950b014005441110300c204004100813180340e0060b656804c0c02840441d070b898085522109030b0b0444c55030420b1409030401030080c00c0da01040914410719201e10b55a0605007515400c55040c0100e10075a4003502c0e8081c4000d8421103514124030207852150030300000080c0b5410301100942106000f5001820544110f26070304040300300c03082c4100e50003071403d808101c01d50340c1c0780c9a80c00903030703400c5c1250f01c140d190044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 210786510 1250 210785260 210785287
    0x615030c0e090705150a11010e011d0c0607150209010302040506041d10050112090503091519020106050907123c0603110d03020c060708120a0506010906030908 70
    0x14014035041c03514140074100100c40c2401c000150380014481c04450f80295032100700f0303600b40e0baa40d024a007400e2800b50b001c07080325400f40000f0b4041c21000d510f02410148a4902500e880704491100e0048807414036407141804200d100c1c0460142040b402400b500091540d01d030010040008185400b5081a80e15004203a0941013034214243e04d609601d04c48805c0e90311079800551054000c80000c00684c500300000c3c09011112108036001602d5425520038000d082040340d02d50702001d0700b20000a00d90845011701794012003c1c0100c014804006040814414083c1a040e25030003004c01c410394a40030380655880303441c001703141c603a030380c0fa5411000a8001c50003840300348000500714043d03032000c0c4240d402201420800c007a105500d041011702c040358030341c03481d00c2c00000d050f07034120a1000d507400d003a460302a410110991000000698134100b180c000050440f000c05000450000e03111803c0d1841030340c0781200d10600040300e5003405c1003150301c650486a003a0703000300c080a00e007612900081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 210787760 1250 210786510 210786533
    0x111030f18071d071e09060e1903080415031406060a111b0a06031401030201030207020303040806071d041406130f061418010609032306180607020712061503 69
    0x3040c03c0c0303081008101c11950010207070000c00c0c88080d100c140e81400e83d4809012070816000d031a0402c80c407805d41c2d05054441a50141101803ca1000032003240d41389042e03040c80e4001d00806182215000d0308161140c001e004500300d8241c1c05001d22626901c01080c0281600f03d6800c110030014000c548008511084c03220b40644009441b1030211041d0900030301c0090340841e0712072401c143c83e0040c41e40720000e88101e405d0641e5424a0091790700c4c0b02303a000182c40c43c01150400e1100b40101d200303015109400c00802c0e24040048400300f0000c041e0201000100c90061450888035144100010384a02d080b96603030307a03030f070307030a8040003c1c0f40c01001500022960f954000344030900c0c068601c0e088170b140c0398500348115203000c1035000c100d60510a0062560b109484010030004441c40c00d0318a001464040102c103003542c900301c0b40540741c41e03000c0302020300383c20040c1042ea020351800308031510f20100d200415189121241c01c2031f0701071a5980001030652001c1d8103141c4c50503000c0030001600c1030029 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 210789010 1250 210787760 210787799
    0x3090602190c0b01080706050d0911090106020a030305010b070203060403030b0102071a031e06010c03030f060504090303390e0f0306040804090b030c01090605030702121b0111030f1807 81
    0x342c003503042c82403814400207441078012021591140c40e01f0060070b43d120040b105640c0c19a0400710f4940d901c4e00c0c01c1d05548030460300080c0d202c00c150002282003540000c040d030046000f0781d13090203076981e1841c0d0090140705001000e501a040b590004001c24003e401072842032034184115540c0a42d181d044a2140039a0440824000000014803100c0a5100c4902441003404070704515242402c1001030545101c0d14001014140c03a01034410b04c12103198041030003404050001c0c80444881d16004008150103005000b02c220030071031640542c034603425034004030004d0001010341d0244007241511400090105140e01011049002040743c800384040c41c0a90701c50720505464130b040840b9082a03d2182c41c40501943c0401036480040e0391181100c000c076011414890303500d0b10b410400304d04101007058090081d680001d01c91081d400031f0740f24405900c03800c400811201020410b202c03558402039418004074020080412070002c070b480011082d80d2401400c031000729588000c0141d00c0d501c1c5200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 210790260 1250 210789010 210789017
    0x121306210606170a2307030204030c0b0910081009021308070b09030613150518070b25111002150f01150c0c1701020c030c030405100908030a0309060219 67
    0xc4007443e9108000840c2d410042010f0b003842a0891032254146030b901d800e14007a2003208220110764818006d40c1102c1c09542c0140e20545002c0d12046d0106455001d041410700900c40101340d11511886801d01c6c42c0202c4c4800c55844100e450a5020000394104505120840761100d0002a00d050f0410282008005450201d078903099a4001c050404000030070600e003101110005000081c0c1500614a5540250750002020340382d15014183d1003a00d11110003c80c0706161011502e03aa41501030309140c44bc039072005c03d055511025403015602c40003002401265409040019450140000082c214070303031040310038500c01c1341550059844186d44644510030b0383c10060001d040400700c180f0000d840c1d420010390400e02c507940c01410007a10f100790720f45250071905410314420203404540c03c0907030355030860b5102c185c588045034032684a0b10580d0300c41e4540b25901250240201c05101c00c888121010f1400c0038030a04080c1d010b032800343d008890459007000000d60030710601581181d24881c954 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 210791366 1106 210790260 210790277
    0x60207140609070302030d1107031e0b0c070210050a0e0f011b050102040806090a0210080601030b130f05071b030e030c090117121306210606 62
    0xc4080d10500858080c0b08100e0000200300b000d4900032000e8800351565884c1c1070b2803030302d0300c01c18001c03480c2c000301070070800b01e05000780c0d0f25680c1c84032540c80e030506005079a81d520860402c40d82200e000c000800d504056042424045d0301402541c10800c0c40d1205114000c3c004030700317100740d6900c1001070307100446141c0d10810103100c003402161058400d10b4810300d0124040d42080c010494a4031440000070b0a1003030010f0b496102580140000c11343c1001094101c41130340b401005141490f03101c41200ca455141d945c1000c400c0c0b078848000261080c030403105802503c00c00782007003041000c00e5110300710000c041e01c0030255503945414104214828200880d0070000341125180d44800b82500014030320700d0010212510300e0610040c0c54080e002c81d001d40c80540103010991403001c0228405101071070140720f50042d03040a0f2900c200c0c201a99001140a8070a280c0100d0b00154165 = true := by decide +kernel

theorem cover : BRFrame.Cov 210611510 210791366 := by
  have h0 := BRFrame.cov_init 210611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 210611510 ≤ n) (h2 : n < 210791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
