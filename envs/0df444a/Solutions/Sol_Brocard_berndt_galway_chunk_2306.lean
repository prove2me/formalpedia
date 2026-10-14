-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2306
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:18:44.3479+00:00
-- url     : https://prove2.me/submissions/e6f01a34-fab6-4508-b722-9f00c291c57b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 414568345 ≤ n < 414748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 414569595 1250 414568345 414568351
    0x3050108061e040c031a1009020301061d0406050a0f080c0a080606120c0603040305041412030d0207021504030b012301080105010f020a06050910061202090406050601110f060f 77
    0x101d0300280c0402c14081000c0e0720214000c11031903030b0703141a6543c620380303039541000365040985524000d40801c1281c86d17000b602c1e02c0c0078082e00c0114a07030081e6a401508107a00c000d0064800041d4103071601c0000c040a41e07800049494010004103000e502ca1000c2610703480c2c00d910296105480300f0307080042050510100c00c4100c01030300c5041445081c804501d90f0b40724040e2505020703410300a0050070b07000d401d00402c03c91000c000c200707a99900f4981001403a0390450702861429418801016145142c0840c0c99440720b48540091406c0902e01c403410002500f00c3c520031303030f00b204081c40009805140500104040c40c498680034905505114031002403802c5c111090300281c1e9100c0180300b40c0e0f0382269000381191403d1070300120440758507a0481c00e100c0301840041c000c81c02e020134411201000b0034040741c442281ca0080190f00d130f0368005080c9442280038085d40051840b800f00700410560740045500240c181072807120042500241441c00c00200c100c03040300e800460900201045554049030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 414570845 1250 414569595 414569609
    0xf05190b0603040c0b07020d080703020a030801150801060311040f0b0a0f05030408070b281b0507020a0e0a110a020703050d17070c030e040f0b1008070210091a090c01030501 76
    0x4150300d00f984d58402080c0a82c021101c0304000844e5000c215520102415070065020394a203868161034540659a03142280003200410301d008001310b0f4056580c40c060524a00543d2110616481c0000070b4000b402117a2109400900c02c2002148001c5c030312074214000c000620405a40d0840f15038001e2040520b115200100a400c1084c0b00c00703e0b4003081900c40c0c1076041024070841c1c0d11000071090307111101d507090347c000c0100b200c0900801040f5601c81c46500d15654114a4070181c018130444942c0b141c3d0000039849400e01106004000f80091807540c420042c02002800c0c104602d80e0141603080001d424006901c158001c3c0100242030003512044011800c0c0000300c104c0a645c03204249030002c16941c1000051003c03502854840e00c10000392050191040200d9242c03c00c000d00600040201c890046800c3d201c03400000d0b00c2110031030300c0b510301c503400341820040d080b031410042c0c02d10842c02d51701c245034010700c485074500d05c0a5845c06285603c0013080e0039a24080007400751501603016070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 414572095 1250 414570845 414570847
    0x2010201020c0d12050915041e02040f0e0f120d091e0804080705040203071b1106270337080a11012f0d02041e050102060c0c0d120f05190b06 62
    0x1180c03000c0e00b07016041c0c1141d400008510000707000d4540c00d00011027154043d42c46802c0011000406400d0387c40200f0341d05a402c240c858002e01c2c170300607940d40c0d483e110212126074410441450390004540c800080a885003100103148036040030380d4140402614002c0e01c000b01c00080400505200300702c401c0040400740c03403c0d41103240040025140103000c8410401b42050000200c0030403241906106280200901ca07546480c2e0920382e80d44a0420064801c80f80080c0006034402841e00194003e460544500da0141b280713141d0032190419501244119032005d004d643c00c00016108201a00922000d41c1c0c0daa0000e0104c8e00caa1402c0d01c2005681400c1035100501c4616180d41100c4000c40b4050b000103800e59615489502070001d00c22a40b0607a901560813500c107a40603101410242116002d9084404036121310200d90000e1103006840e01042e40101c0c12120703c1c50150074802c0c50b8440d0004001070080d804401d210a44004a4880b400c00455100383d8100c8081da00c41e500030040260366007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 414573345 1250 414572095 414572113
    0x90501020304090f150303110d030603020d0f030212030408030709051002060114010c0f060207050c01140313060e152a030f060402131418090a060902010201020c0d120509 75
    0x40c0d260b1195005044020b81c682032104400c2040750045061440a18207991260b55a404d00402c1c001c802000b00841d400307078888c2801300300d00ca80038075004d69800500c030b200b07400c0460740d520820f0840510120198005c030078001d035404001c0e601551049005e0341c2c1503a502e1409000c01001c6641036000284203800084c04005d178640d0004101c1d043d156915801402c001d800303001682d8803e6808002006e480c5800c6414013000060780240440341c1c4640b0448000d48800c10041d1604e20f00040401ca980c0001d100180d40b603030954151000c61030080314000382200307081540ca41042d0725010307ca5030110454081c00290138480030030360a002205100c040c1111210359580c0c41d00d1101400081140e640c8101041d10b40d17849504960003074500607814000c00d5a5041d1118a80b11800b406900c21009440c1c0c6007900501501000d208200c11700240070b01da11940d4400b4010005800141d045650a2114200204040107030064880250301c403403003a000c0040c017036002d40d0401002d001e000c0e0846008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 414574595 1250 414573345 414573347
    0xd090e0a091b0609031104020403021806040f06090209130507050d05090c1228080703120b100306140d02101101110f070201020d0201090506010501051305090a0e0706090501 76
    0xe41119044001081900550911100b86007498a032001d08403451280090419041080001103038441c1c3e120810002c44401008200d0050b4480a034010000703589400204244a0409a014500801c0094415541e4800380115840342d004551581d900280040b814506961002060300000340d05014500d0220002411806003015041d0640c2c2c07110081a207031001070200750800f40028000d00c00c5040d006020950300c20144600d074aa500986120f4551544191075140d005500b2080c004e02d422140e9904032103544520b41795855455032504108541da582442e08130344403101c1c2e81c1c003141150800504d414040c0c41e050358180720b00314607003044e0b006071511407424a61622034284a09406003503c040c90140801d000e414500300e400040c89480a100400980603080c000e80c22225060700610084e422070307540385e601502c03941c0440e004025942c4100c0c010465070600500c0603155031381d01c0d80441d620f10340c203403401c102c901e458001e8103500140820641e00205a945400c4c2c0c02d213460000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 414575845 1250 414574595 414574619
    0x60403090b070201090e09060123030a032f0607120e0c04050402060c010204060c0c06020f10020904060803030f0105091303050301090b01030e0a0b0a0509010204180903020c030303010311030d09 85
    0x400c4509900c004a90001035a001702038500060030316828254407441d1100041d0740380e1400740280c4c124108141c204440000100000001c8000d0240007007000c3c841d543c5069540d08495134a41d03401d0811000d01e1050f41c5241ca0501e10000580700040c600381c20b10440c003a05164410240c0600145420076801c103c60000640509000c0d081e9800a1140c95034004698648258001600290300001d0000b810942c81110424a54040c00900c8000e540b61030041ba11020010948080b030b6100d20161402001c2503402401030100c0104001145036031766628a00b1134108403008066030340c07010010041c03800c01c4428280c0c0501c17407035118a00002c0d10f1f507000d0607034001801821036040d138030203c0300f940780d000740d10000c680b00881088800200c0103281440c042403088a4001c060750034900403425501d0140292010b0796101032140c020000344403c0103006041500d0250210b2007030394011a1a40c13421300c0114040c1d8003d51580014003402000c1c1881c0070341c4a03034201c040040806041045443d014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 414577095 1250 414575845 414575849
    0x14011a1c0b0c040e0408070506070f08070e1f11160f1413020c030306030114070c08070c0b030c211009020d0912020d030b100807050d021210140306040309 68
    0x15541e410780c03a6081e180966020315042504000d40941c1840103024140f0043d00005c2d210724201c0790184c6d21001c3c00c807120f50003580d41c4404503050f400890351441c0034000a1005c1e02000d00494041500a010324610268180e85c180109000e4000c00440400502085403000606100448000e24001c000c00742c04116104003503000b9114800003540d44d880c2d10b6603040c810340303044096440d441003442a540369071094420700d120b503107001010300c2d00180038042d0354410b51258442400c14407850301c5201040d400260101d5110301c20b40d130041030385c0c0c0007000a5801382c280d5115080d141c2608903098001e00e4918402d00d049441c0b51010030005d070400740341020980d0304030040907032a54409030190340a05511130f0003e00307100900f8801400168002419000003010f6a0140040c00014081c0111611160001000070f0704180006403810b006030010008202d500000600e050302c0c101040380314030801e699010118039491010481006c000c1170030800a0000c0300030703141506250b500500104c01c80c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 414578345 1250 414577095 414577103
    0x5090c0a1802160b0a0c110c0d081303030224010b032403010c030c09050901031106090303160503031915051918060510050a0e0f0d14011a1c 62
    0xc000c0c020040c00503015500b903c410700b6400141080285440a0a00c0702144c0100d0303045c0c07521080d0200a44079040100d00061040050702c0361101101c1440003401b46c0d02d1096a101108001e0010300707101000f01c044c010360207035001d0103483d02d00050300058201d001104601d0705803004014002d1422520480740c1012100030031420300780007107a000c43e016101d5030091380e25500e4402a0a03600f034141d004100042c40360b0b62441d003425110300c00c100c0d400b2800c0c000540013810040c444e006600300440101034084c5d005045030f0030305451419003029412808400c80f102d0b0804402d11a0509040d24000541d517044481070081010000a60600c140180f003118410381d4044210380004405204020103482001921210004015090f00c00f80c18a4429140202e507400c040c00761261243c01941c40b46e403800da45040c516240201004600902045815404081e014036500022019024400c4229800f000400d001c494585100762103042404894000c03120002242c0c45010083c0704440011341c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 414579595 1250 414578345 414578369
    0x7080307030b010e0402030a0606090b1c0213030203160837060608190507060e030607180e09010e0f01060f0603020c01020f0406110d05070f02092a07030305090c0a 72
    0x2d1074004903100072411140c40d810500c000184240303208250400f2061f03a10a03155041940c1d610452581540301c2e0504002c1600d44000c00000c0b8403000d40c006083c800f820715105c042d800e40f203800207428020070302d4803411840a900303000c01c07146a0600c080c0f01025164100710f040084081003419513003c031801505c281c040c83c4c1d030403442040010340c40400a000044100d484080000f001100c5907500503600f9101d0744114040020124840c40c0c5000b33803400d001c2c01800796926405010748212030000b40000724103221030000303d10b40d450f20300503c0c4503180c00b000128184286181d40e13814a9003002d20a162a410240c3c203000440c2c0a004000884a03d450010381e0fa07580d401c4903600a00580380341d42c20710800002c002680d958401c0c01441125a5101a160310401542042d5000c0c446c5060081208520107040000743c94800309031503100d402c0b20300c03589118194001080c000e6213a0907240010010115400c2e05050307040c07048076400088003000302011114070b0005004034201c6d214402920710 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 414580845 1250 414579595 414579611
    0x14071406090111191b0c080d120606021f0b0910090f0908030c090402040317041502030a08060607020f030106170d020a0f02040c0903080409290a0608090a0b090a0302120708030703 79
    0x1545c002826002c0c0d402c80c160341075542c1c032003500c5500d64000c402c1c8440020a0040400c00710700140c0318200c00c8403083e800815140034440100e03c0c001c0c0b0002201440c1d0f50f99070140f880c064031004041c03071140005005040d0384a040480c50400c64041a0601c0c2f0f40b20702d01090800011232100c101d9805c5a802e51599131030720f411200003000f921540d00010105010804124480ba090202410648203800e02c0111002921b03201260740b80210712051001511503070110302d15041c00e50083c03031640c1c0041c1c01c03001403001c450042425240c90340c0c4800c81e2004200ba410008410034042151050142e1024040d141c00686410125140000019100781e9032503152500701ca02940e80c0400031680600700a4582d951952604001c0c8034020004400040c801034084509800d644e40c5400b2a81c001c00388080c0342e04155080b507811100500d141240c0c071440c000a8081403103039180600c203094200c02880c1c8841189030007410b28003515107480c0a054188904800550f80c030f001e803076110a03d0718001402070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 414582095 1250 414580845 414580877
    0x207060810122003190b0402011e020604060c0207120204051302090c0306090a06030b1305010e01060807140103021309020307050403020423060102030306010c031407140609011119 79
    0x1400300d82c02505590545600a003c001c401e1a034080030b000300d0b078400c441000e040401e00d81c9540146040e0040f0322400180350700000c415a041035002401850a44a05184111a803a005050030403840250f800101004104295401044a40003080c809402c210740f078074005a90010400340000d00c102e4a4400150508080811041a5a40080210021342443d4070420200e50040c7d440b180201000000121501c0c1300f80100003c81c0c1c0c3c17001d5074041075903c410040540d00710301441250fa55480c2c03041ca603407000702400780e0350141c01020301802c1e00d82d29103590408a80710424200c0c2c1858014030051840c00c01020381e50044034007a141c09a03a0307a4030250111014812900000e41c0107143c50f840201141c640840f240481120402c0c0f0105520341c0801641c2e02d01045178910b001588400d81c0d000041e00c00c0514005507000c8007034071130070001031f40c0c0c58481414039000700c0e0310710794004010414030b590240142400b00c00e1019035545000d2a0560030b44407801d00000300c0d030900031a070582100c0300d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 414583345 1250 414582095 414582121
    0x340e0f0114091318030c0312090209060907180b04060810060207050105070807022d010e09150d02130c140f0f033601110909040f0f0c0e010e090d02070608 68
    0x504c2070444800f41ca80c0980c40c0140103510151426000a06a901d03140001d81c003911502e04c4d00c0c0e40052040404c0d50720441001405c0c0001010281004195455290913028518042c800340058203a0b0a0312141084402002c800004002c0c511031f8020758400c01c8042d40220305802610004e192165a91206040040da031b48620907000307422400050301c8446800d07000300341c00136040c07a8403c1600764040500044070380c11800c4221a0780004510301240c00e07488022107440b610b460141141201d0000e5400003185e0301070448100c00e0762500c440181c01e8080d40224681d94044c6920900c90402a6180c10704056000c3d40c1404004184000b0100350055085c00528454a001a1319078030140500070311201508410285140305d0340c02c0550581c0c5600c514002c1d100000d40180c001030842d0381e90b88810341140c0c0e94404c1075590b851000807590105001c007044101803c6110170b4000030f94035196000066540044c6001d040d504071684c0c03096a26800b080f0401220b0744d500d401070460b15641c0d650054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 414584595 1250 414583345 414583361
    0x150603040512030c09040c030b1810080717160602190309092405040612080703031404030e030714030616120906050402031b09340e0f01140913 63
    0x141c42c0c003c000c001c0e01c1d6000000410324000f06035820722048802c01c41c25016500c1400d901540241d51032107012080341c50020907a80207114008218100390f942c18000e00700b441c5500450100740e030560500c511603004118004681d4203102520b04081d2504c18001d44421990301101d50000240400c20f045c144100c107400c0240240040420074a0711004969640f0130b119078010348001c40e0184005100d150510a150445031805450131711140d0541e00c9102540c0080c20480600da83d84884040503c0030500903481148a070f140d841c500142c40c0205450400701e548200400910745940380200d4501003110b580110070030f02c0d88500c441d070b145e000351880051b20200190b0300d0710f480d05110911a2542045014900980984000307801c10100449603450f04013189411995040210325030b0803990303500840025014140079900c0e1402c030500791000c4d02e02104140001c0c0d000760001454035184000621011090030811108a0b045080c5500c5008600d0924820b8185001d2108019110b82118038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 414585845 1250 414584595 414584623
    0x70507020a08100615021b03150c120c0301060c020d2d060e0309030d26190b101b02030c0301060303030e1905060609150307060503061201051506030405 67
    0xa070280d115940599106010420300103c10b0800340e001500c0600010080061070441d4098240412420240064140092265074240c840c034209225143d000700d5515001c4c4500160300345d620012042051143d0b80060001d007544942040100b0030240c120f0f0a042c2015810740c1d50000b010450700b0250401c0d6a045194200e548040303054030010600c0340c4140e541584211010061201041c1d14a66a802541c0d000c0703400d54050580958824082c250b1070090096500990010080740100da1200900940340500740e031080f03454250841c2000c1c014090800c5c401c1d1040009070300700c1000148000a07400121000c15800b881103015910b06200200c4800006402846500d03074a190080c01400c482003214070a0003401a48500000c61414021090340c01c03400a041e503403140320802c0310540f000707000710b808407054258419071610700788644c1c00180103a4480e02c2e1645420b00920101c2491a803070304001d030f45808204218140068440c078010350b0291115a200ea80d6850007518107040d0820340c032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 414587095 1250 414585845 414585859
    0x25080c0604060c020d110c120f0f0a110f1807090509090601030c050a030804140d060c1d0105040b0d0b1203030a0603110a0e2a0703180b03010e010e07050702 69
    0x20501215800c0f2001401e03040d402c03101035060900c0100c0f40c466020301240320942285c1c002004900d0b001402c000000d002d081510a40b541c0d106e285490040301d00040c21440c0c2101800409006c0c202031051400c031003c5e02d0750f640500008002038601e00c061780704442848501d00105500d94801c0013140c02810000d000c40d03405051171210141d4560003407204803101c51941a0106039801c000280900f1254080360040c00c0c031f820496004c1040030440905038000c001300e00a18003195250194032110380c1d6a0300d40d80407106003070f401c3d0300c0c28410110310340d81488410003042001405000480d030014401840015507170708a100060300d0b2001c05032070480180b10100074000316100d29031281040300e10400084d1a030b0680c0c10244007170b0000324800d505d81d402143c0009681e1140d03a51285204002060402c0c100e1072024a0007226504602815400540100e11b6900002c981104d048060402d120f803860940d17150409400a5000500a100380111504040fa0806004000340c9280c2c50f4001c0c174503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 414588345 1250 414587095 414587101
    0x106030305041a0f07081813020a080c04061205060604030c0f17150109050612100605090a020702151305030706031b0806010206071b0602030a02030702070b25080c06 73
    0x14110741050040c1541c00c10586101e041c803d807204115900d440d4010001c50600c21142c03104080c0d904079540d0f1054a10840c0903060701903540350895442010742031401a29a41c98060040c03106d400100b003515604010801482001d0300940301104d0700381504004038490f0b0743c08022900b18012a40010005208560007103003400504a80d441904e061101003540c00c05141c003c00d81d6031690404c0e1010100c4060014002203015401a9502a00107009508689110401140341c1038400c00004c015950744d0405100c5807804800550300182944d9055040c044181c00103034511105c2000c1881c4071a00044615441210503044001002c005041d91101036503400007401400407a519050007e20310036103041954046c030705460117244180d0041c126903848203401d882041e041c40548068807841108540040c0250000714460070300e00c02c0144e01c0f0309140d83e02a140402e00d800066242c0c1080c442d0000da088040c80755040a82070b441c00c807036104514200202e080c032442c645840b580c0220070030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 414589595 1250 414588345 414588347
    0x17010e0c0708160302070501120c0c17360105091f020a0501150306050a020711090a0e030d09051e06070e04020f070f11040c0e0409051c08061807230c01060303 70
    0x118404880027a03ea5031078083d0704c12400c07001c03a444244020701203000079041002060000005000540b440070601340303018100c0c1900d041c10b21f00c0d154282c2c4600040e40022007048004c601e840c40d642428240582000b040d03030300148508503214403c1400070a520b60300104948200300e21261150030070020040c0c007080340301c10300c0591030313902080e03d40314205008036641d0b4049100321101c2135048800681c00e402140c0c01c00c509403801500b020707030103034584441c51490881800103000340c1c1d80c002c0c3d00194400c15807031710034100070301450740031119440307046854003000000c0f410300d90020041c030700709501000880008009015076001603510b19404225a0201f00320500d00f2200c4e640507000c1c1e1000d00307103660304200903121000300c0341002a50b200345e00c600c10b0403d600040c0c40b1078854803d555400320803001d2565086600d02150340040c1d911400c1c08214180800d070210f2030080c983e1044114901207401500110b0789415441005031001c400c075084103040000d5030502c48807240240886603903424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 414590845 1250 414589595 414589603
    0x501140112030914060904050601120f0614100828060303020d02010608030418180212150907060c140f0708030a020c060c07180906050c070317010e0c0708160302 71
    0x41c0071004103c20f4040810406aa126004a40c8000825140c500583c00d8140310103480050130b8903040c815940c03c60b030303041d84203800b030342941008490002616518101c1c0700c048035800e42900e5030090100100c112400c6600400d15036004d0042421421002e800c00207485c003036400221401089441d01c0404800c040e40810208400b070304c0d660003404101d840c2d104468803445507205461503020240401c0c26072900a0708a100391101100682d0f07017500050f00072442a140d500190402a000034003162400380c1d0391402540c00051450080c1140c40c2040c03406840c07000307507100190410358081040d034017090040080a04910111041d14034055032071090956941088413040c02501a0441c400d400c0c1c107102c42a2958441306c50010b2000c2480e1114691585a0400b400350001e03486000c01408900d8601505020392044c0441030f82c1e0b01a42d04000340481480b1703607020004815100100001c1e03d42001054000070b026400c0c80d40c4416500c0c1c04c1281d4400c1d41006030320401003058400c20700d9000b013 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 414592095 1250 414590845 414590879
    0x1140a091e0b0a051b151501020a0510020c0d03090206040e0c190206092b030e10020708040f0e04050703120306031a0402210d0f050d0203040b06040e0d14030405011401 74
    0x102484170b10104500c219841e4a20380f2a814403d0841d000080d402c003849280120a800060054a00703c5000d511582e050888138038005054540000340b00030040f104011058040b0424942001900c20b103a000402500c074520881c41900c040740041010003c103030045544440140920100c4015000400b030744941c01100d40b8001d03401240d03914200060546203850950507410b0a020031000da0076015001440b40300c80899407445a10403c3c16507100e0343c4001d0503081d00414400d5100e40c44c00040c1e004000d1650094644141c010040c400010360000d0388609403540640d40b070709461f1500380c04030000c00140d48058030701c262440d0ba1805400380bc004440c0614000d90f482c1c1c012190141908480d03100d0b2000c0c9400f141d2001e84540e0000348580e009a4a80000340381c02d17490039071120a00c134140d81083c0c0782a00c005208000784149440c0a1050020b1070030300c09e000d000b854013a00c801503d41080d12034402c03440e420003c00281000030a5100030b2506400d40e6007034070f655864000b48240001d02d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 414593345 1250 414592095 414592117
    0xe0612040c09090f060c09030516091a1c06020f04170c010806010f05030a140a020309011505130b03070e0c03070f08040b060d0302012901140a091e0b0a05 68
    0x10035000300d284161401101c2c0c1450b0040c94030b4003840031540c1c4900c01030125030910005c028180038044006102841844ca490581cac0c01c3ca2181603062030b03607038070484500c021002d0790041c510400078095151050a8403036074018280e00c80c01c0310305030304010b0044d00c10042440c044940010f00410007406040040505000c45000c4440024051006454100043c3e840e00d0202c0e400da143d05694a21520046074090b81c80d40001c1102c0d003400804080805099912401c116004400c00208810912411529402c102c1020007690b107842e0200c2d0251a6607269014402d464000c4154940ca04110480003804040c9420750b6619000103100010b030010f5a56800007825000504038252040001e540616040301c0255015207880c0100035107814010811010b40d5228407044480b1345a054a481d034801d40c0010510900c88080300043c040c80c2c20205103001e6113011f010821003035601c58146020b80f2001e15100d01d120400604c1a00c0c14049544840b0000c100042c0e02c1901541c0800500b00c407050b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 414594595 1250 414593345 414593363
    0x100c0302040e1f2603030406090b07170a0f0207020d05060103031101060f05041d070b041d1302010509150409021206040c0f1b0b01090c02061f14010e061204 69
    0x35600042ca40343c42c11640000c00701242210a1141c0307405045003403094607034034601102e02c1503003466003800c54004a805440244d079640805003841076004085030f1209462400155038a070200c03160580420240c048842d5603510410140381c0c240302d504451a030b5030014840c0a0b101c50a01d407840e0b0300e410034001100000c41a54801507450014002c0006850703990341910203450801003840000d0614490301a5500d10341c4e070390004102011b10401020704412180c883d904d608002d034052141e0400c56440c2c0105c240d800403c5000d07440c0d0442d4045d41582481c04503544d901d0880014924001c002840316000c00001e00000c64030038a40c0101512101c20b54440d4030b030368440741003100301d810400032140868a85880d40d003c4901c0345d24000e03200036480d003d800464880b0b880d168400d00c000d030031200c4c109948203004610b064040003a00d0f403040303448007145180c450f590208034500c995403042c0249251501040e921603130142425401a001c0541060385940007040b41d04e20480d802e0303406480d8052 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 414595845 1250 414594595 414594601
    0x6090803070b0703090c1e030203010e2b1701121502030606121f080f0105090a03050d0c0203040b180f0307061416060513050d0e100809100c0302040e 66
    0x1004410745091a400504001c069501da8034103401608a010084919030340c149008501e828901851110f003901c40d02240d401d0380d04602c10f150031181603170601d41c0300d80d114520000c07800c503640700e08058000481988180e0100541c805a0741c170140c055241040042406c0042a485042c8034103c0f9070030b02414983c00038007500c01d0450100d20013903541c5a00440e040000407030070040f00c410541c12601d4611441c1010b0348111852030070044c82e4010302101d400c000c00310610500d00740600c070340040c5244043c00841219a0b406805407042e94103d2000617103c0d88141d0781d40b4024400e40e40207005c00707001c1a0350342e0942981104030000400b01d40b4030a000f88010090715040c0022034501f07481154503a94600540c40e04104855000b560340d505030b10200c4400716000032180c1c0250382c0140300703000082420350400c2ca00f1030300340100030b0002c204114a201c41e120043da0f6094200401c3d1031241041c4070291901c2c0403560901407501c0321500301908000342d85400990641c0100210f80b070440c00740351103072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 414597095 1250 414595845 414595859
    0x10602061b070c0909030915050d060e09070302011209050a030e130e030a110c180f0c030c07030e041b050319020f04140105130b0409060b07150e0a02090a02040609 72
    0x8050b80c1c0b005894555811001e205110950380240c0e4524003e090021005a4512405809882c9900c0000001c0c0000c030714118180054001d0750b010f000140318003c401d02d481000240d46001600c0040e04001900444210300d1381507500203000e040d005410b49040034a5814090300041040d1202c50044003000010130301c14030640b090040d40c081c071001540c0f80440e41102110034003c2e4040f1010540640401c5100079a1688041401155549404407003482d1072004000d070104002c00100e044002042044280d42d054000c0301d81d5264141084601b03600a071020a0080c1000d5404604c284490749950345802d070000003541c4200181d400000c0743d0203110f55000f0980c0220840b0703001081c02070100388858040b905200305200418944035007061082020300024249640c056010420001400c0c081c40b00a40070740c8000d000c010ba502850b00300e0640d10014078814007481c030809296545980c0707100b00b805000d0b51070344a40052052055082c49098480250f100d0700c10400880c6a4510000d00c034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 414598345 1250 414597095 414597097
    0x3040312080601081923011d0c030609040c17010b03190b010302040203180316060605010c08090d0c05060c0c0307170d0e0409020d0f02180c0403020f0d0b010602061b 73
    0x4001c1a511010320b030300c42c0f0300c6107051684500c05401c0c00721303254152400c1b91402c1c1d40b44a2181000c80f00700ea1000d5241c407519007040340349400401c3c1d002e0304000402c00301025142c11290010000e580410142c2c1e40d90400100090041e0030a2001b42d6203401305401d40a015045100f14400403001e40d4500250307642c00c81c01242e4060401403a100404004001610341030703029543c0524404c08035041003000886180c21039010400c0040320903000c400b903000307005580c0300d4080507003020b00300440464070648480c0e269004041840b803140c00c6213034a0700104001d11203440e000b05005480c19855000083c0f0045e150036900800501900c22060000303019400028040545000341001e0b0200003200a011104821202140d41d085611551300030016200c00f610034a00a01803190306107850340c588104400c039070b007900d204600401c18505100d4100700c0030040b6402c40303a040f24140c00310040c15011800b180d2052801800b81c4641c0800001c40c20340200700b480c410b0118883c01c9900310041c01110081d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 414599595 1250 414598345 414598351
    0x206070e1906050f13151d130b0d02060d231e07090e190c0c1101030b0307090608030a1b0b0604050601020a050a050319020c090a020304080d020301080304031208 71
    0x5920900301c81000454002e400500301c4074100f4101c81e00c0d0110f41e004140d8404d4181e80306002c0b101c0d00080e00c40c0c805a100e5000002814070000d0100c040c03040400050441002c0c014680b1071980e20315075064569112208143d4150b40580910346440c0607107601001007111030691102e6100760301142c09081c00011540c1d1003405000c3c00707204000340e01c0c51a0152240f0003029a41403060401011804000104803e0300c903041d40f4020f10b0102050400c0e42066900844501d8180f000c81030541000404403440142013100c00e18001900c01d082d43e0019180100c9a44000b0505181c400081a030301c40c08802802d681031140c5803903000180c004104104d81541ca1409000c940c070613801302d9400d00d85074002d80e410a4052040b511100401c3d00e609041040c94a0121920f5000090007000c5d2400781e0f01040c6c181100740040d00b171075444003020900d01d0754001d10342c0c20201d5000001604128003813059540603203101c0c50440d1a50f84503a445035596006001c1502d03d01030f48035136240d14612810742644 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 414600845 1250 414599595 414599629
    0x120a0c0e0105031003170706050a0c0306090b1f12020c0c10090b030f04140105090c010810180f02130f0e06040e0a020d020f061204020f030331050607030206070e 71
    0x1641d51171925040d003031100d13080d1200d040b0607007040760a020980502a00d8002c1888400c0020f00c3c6100e601c1c0902100d4007544840031181c01d0461110450380d0300c0101042e90075445800501d007180d0b4440444400040084071403885101098820803000001901e500f800c0040c0c660001d245000501611075002c2d9100342030501c001040010030400101070460342007407095180040384a810740c20182505c00403940c000d1030b64030110804007e1741c0e12407030340303074100300700c040704600c4075040c8496030003030800210b41c6819a03502e80c250345030b4550f01c6a048038440c260702002004400e48500469410f0070322840340807046107030280400c0d264a41403240c1c4d403181c05031800410070755520354240100c0c15050b0303005a901140c503903c00049038a0f054018140d07054440400c01980c9810301c10044400214070000e8081c2d8401c2c482d00d91b1200144c20401220503000e1178a80078603105103194200002c40342c00403500031a0104d411010150001440e5016640f00d07259084040251024000c1008034444025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 414602095 1250 414600845 414600871
    0x6090e01140a0b0c15150a0902190305150303030f090d26060112052706090304030b04080c0a030905040b120304180207021c0506070203070f08090105120a0c0e010503 73
    0xc01003d4000c2040a80c51002c2d1140c40b61145a101a404800c49140b1481d10354207640c240304d884c5c0214210050405864110f040c1460711685000d004c41d1180d45105160b518004035482c5140340003911002c00000f0112542c070320740b408c0050140c04055860460601c591038506906502032585061240800e160003d608922412140500c0002809450603c15540702c283e02c1c40c040ca0180911801d02d8085000c015a14000b20140d54108156810305581154003071080425010045400f00c3c0e800003003882c0030ba21541010026807107010f52440e018440c1011000800d60810814001c0b610226003c104014042040c440311041080e003501e81c43d002040f0a1001caa030300451000310030b40103480141804a81d5001c0313030f0b035110b030302d010510320314019400142080010400035074000400d10141d400d1541c282c0e600320070041c1c041c000408031030f000b05402025902c114203480b20198065522840c074100750780300c14001c00b0b40c02450400500c4500240d446940213904490107601555500e03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 414603345 1250 414602095 414602099
    0x100603210816141621050310030609030215090d0801150906030e0c031002090f0a320316050102060601020f0304180204050a081f0902011707030e0706090e01140a 71
    0xc82c0c03800c40c0403c4110f5044401d1010030544607001102401d0284543c2c2084080d80402030040142145014407000301b00c420400c012001c0c411000000891f0350204012031511520300e02641040e8040b00c039800905e2000e8104802490000358400f41203005403100c0c0080c0c1d0300c07051880c06040341e400d41e003004030301d040408001c0c182c800e0b8049260780380604207030342c182c440800001e400c011000e4408455503802240a004500c0c0c00e9050a090040858282560601d001d00d941034540b0b0083c140049100000c84484403030341c00218070b03c0013402c0142602c0d03120f4151f0014100c014031034000e07079006106a4001440355400040c11100c0c0840c890019800c1500c0e120046600c501c0404880c000c0f41d400344000940d9031140d600b81c3e00034099100103072204500345040d104a07807112800c42c2d50280e003040711f03400260341c1185580505a480311545030745a0348141094014050a010a03203140c460072800003404c40c0d02108610541c0c05010b0400341990342c4408240700c104222110907400040c101003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 414604595 1250 414603345 414603347
    0x1104110421020109050303070602190305190c23030414060705160206070813150302040509070c021807050702190e0c0c120406111905120c100603210816 67
    0x754849610500d40240c1e61525880481d046400454046420540100b07180d2207042c0021111349550701286030407c0145071000380d58000074200c0e40c240743c00700d03031f940700280c19907205510044000500102040d80c002c0f06a00c100015402190103803140d032044944100031010114089000d200703d0382d174070b90401807502c0e903d140c08039406a04a81c0303d02c0400490340080c035684041c155040112612402c104d140c80c100e01c082a4502a9001c00c06104100601565485101c0960465040c2c82d01642070907491010a00d8001c403e808040012640310400200039070180040c0f41f0340d80b007500c44041c070401c018030a840140850007250010741d6090001010b607000b2801920f03905140004036010401c1040070405194040d42000e80015100000d21032040410000c401c80691840308902c0d583d2807a441c0c294880d41107042c01b8001c5080011a00c04c4c0c110b0400a018590300001d000700552070380d0f1f04d08500304050b0145014654a440003043e01c2182c042c540e03079807285005030511820147c1ca890 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 414605845 1250 414604595 414604649
    0x120e160b0f04030b0703020c0d020a0b0a0e0a020a0308040801060b07050319020a140618032a0f01060806070311030c0301090b12010509060a061512020a02070b0711041104 75
    0x401041c405006000010200d04c2052405002d1452500c1c010380c0ea80e041e146c0c140c14811b003c0140c40c01e6500c40c4070700c0e20020b20b0f403401940d44007110071340001d064401a1840743c282030400d40060340c0212135036070100501c00644010000c80303c8000c004c00406580b80c0c0741c241d0078000d8210142c12a081441101c098446000b40c2da40c84018501c1591b030b00344020b6071542044880e090342c1d46e82562006003004103c00c1e0280c0c4c2c0d030b44000146801076040448106a920021400441e40400303024a10f00016514a0800c4200b003030156581c0248401500c43c0c04541d515541210240001303410075000300107440c0080102d900601c0302d0303801c0078075582c20010414090000300000c80d4001600441c400540c900c2803003500d00070744100340a00307851300b42050418252101c40d0814040400c1c03411064400c00e40000c84070f5603d0054440250f11603144410607070070070440d0351126944010024106d005c0010445260080120464040080018040c98481107003c1e0740918041c1c00000c841304c140d00c1081d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 414607095 1250 414605845 414605857
    0x140702030102041a030f07050906190e03070e10050d0201140a050d0f2003010f0302120a05070609090f02070f141f0902130b060403020112140403120e160b 68
    0x340026281035030741e820105130821500241d69070ba500c08014042101c00083c29250030403a90315005050804140c0000d84620a55502d8403030320706600041d046d0750b40281800320305031800a0569031243e50310354490000240460b4404c07025003600318085003510f03000264884168040c0d45848100002da0a01803a603444611b00c082408020320038030a00504a0240c0c01c480f91840c500800c0000950001f4166444d001c094060100030500040c05600124400f420440c1e0b01203d40311042ca0310545e080d03040140901c0082e0180c010284045040c68226903544100d03a00440304000d02d01c0d04d1040c5204a006044000348500f011440950101c4c0305048110400d4444409503860f2302402840b8000ca03410305110605400c0d150880b21007076140008c9106c543c001050000c2c81038942c040002105841035020003414890354032000d408c881401d91003010203e1901000e11818103241c14040d00301c0220410b031a60190034008074100c0300b0000702e40800120904540160300380d0030081d26003440e80103030b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 414608345 1250 414607095 414607099
    0x1a030a060b040308270f04181a01050a0b07030e12011407030515090f0f09190c090608151801140a0204030c051203070f1703090114090c01140702 64
    0x80c0c1021440c0c0805000820040d0700c40d0504c960b03102c101c0310168412200f10001c441c1000080500c4009903190840c080c8610103045034001000307c000402c4440e41000e020000d0414411084c01c0005c08a2503c00c6030b06848045500c403008950703400f0360442900c50319200500040fa130304401d0391030741070a803d41d81807803003940000325050341500029110b110741264804c0c002030301c910034041c402e0140402c03000422000c0d1680d00741403405480c204500000071301002c0a04030b280b00000c1c00c06a007400314a03451900700503410981a02810041020302c10f5001d0001094a070000009031010006110402e0010500b103600056991f04030400c4203210f20740000741a9500ea1030360743c0c40040f0741c6004074402c200d00030700162910700310f04043c4244500d039003220307008103040328180c44410000010303103822a5008003403504201040c07810140803d14482d010491450200a00c40000019001104050915135410900e5500e00380c225980e281e450403a60b000c210003e150444000050780101995800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 414609595 1250 414608345 414608351
    0x907020a030c1e05150903070506010e0604140103030306031104090f12050c070f03170405010801030f060906020a031d0d09050118080604050318060a080c0a09150507050c09011a030a 80
    0x10385002c3c20468140030200f11380d95000585010b9080d8015134945400c180d243c40110700b8002d080c1e8030165650018051000180d801200060241d55160030070403112440c180b000126580d01c0c40c010300980b0701d03800219400e6103030f4a000f0500d41400d00c00c0a41d841e42004040034180201e4072a9400340c8120a040001c001040128008948003001158010b052001c44070011030b25605088003070b04101e05041550403030400080115a9126501506507078110000060120181c98a58014007a684005010340c1c00866124000d80e0594071082003488048844980b0000844015481e440c462160340301090380740000384800e5114140c4040a01a07605000c00301c140c691103070b140382900071101103030141e200064686498500c0340404d02c02d8035064505e1400c0503000e1902421f03054000f010b02c05945000f180c5003407018454045040180035150010b0b500d00c0c50032030020029445401d0540d0b5622401210445078100003000324103c0310461140d01070003c2c0d0b44c0320000d180e400585503882881e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 414610845 1250 414609595 414609623
    0x1e0106050904091e03020f1b09070504030203070303051c0c09060c0c0e10030309080c010c030f030f06090b180613150f060207090605120c010e030a1b050108060907020a030c 76
    0x8084401c18041c00310f1612103419113500340c50028906071843c2c030300303003c29000030b002c0d2500101d202d9601d0303186020032580d030707001940d6408046400f07000785d501c081c1d4144141c000010a01d03801000400d290070190300082070803d04680020182c544503009200011400d000030000e080c41014050b483d5842400c103c403a8650b61440ca00d1111401d807045102100416402c104058110f10036500030710a0002030300d10040c1e138a0028000b000c0c2c1000c05001c0c0b21100340e4100b80d0a1080c1e000d2540448111030400c81c6a4580f078224004245d286840d9002c3c0c1c00e119203c07036030341e40a059403074443c1100070000a0740ac1d032108800c40107418440c6a8182c0895981000b080301001c0c0003c01c0040c1100d6030081090501c0d08080c8001d036039207980058014032107080004e428a03804102420307500d00070708000d035121401c0000b0030300c0d00e5030056000d4592030b0704045405c603003c1d002c0d8101c41120800d0b41c1d080420b8449000b0010b18010a40740c50340940d0080100340e00290107442036030a0b090007418603e08144c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 414612095 1250 414610845 414610853
    0x150a0507020307091b0801030b060d080705060f0a0606051c020f0408070305161401080714130801060f05061204061e0504030807080c0f04030b1003020301020705070305061e010605090409 82
    0x101991304000840d07522206102e0400080d562142d0000c8a6468202e0b415495611400c14808000c0d100d0390042034591716503820b00022004480b6590b500070111003051604e80780882d466001901c182c910281042000500540303e01b054801c800d00f000301d0902c0607842d50101000039840307602a1090048140400a40301e4004d1001000440c010030241c03541000c02c0405140080040d08484200b81301c4075190b1000342d0340308440a62001c1c0b503081840c02d00d40302c0c660b01601e030300074115501d05e801c03044100458401e5041d0401c0e011140350610851055480303004201c003600a2407491002801032900080200b90325402540480c01049030448905849041d003c06681c0200c038290003150040341440181079100042c2a80910f001c803a00c1e0030900c000c444001281300307a2102408508041002c15840301c180c6228000031680100215a540007a15041d5280d1015101c03d03500e50046800140c08084030240c1041170880d0404e00501d01da080040c1a01c0035040308114503005a03891041000003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 414613345 1250 414612095 414612103
    0x402030a0b010828032007031e0201080a02090603160504080304120b070801030b160201060803032a0a050405040942091109040f0501050f0a0e0a02150a05070203 71
    0xb0f81041c8029040c51070400400f26107034910300d03440341c0203845500c8a01e8003080c1d002c480121070410004038901500c00c00e14403d8500780d090b0b00051f00c1a01080e0b920581c3c0340412002c045a00d10070b8807414040da40c3c244a6000320f01600d11002d4100b807040000541114000d480a42003405c9070803c9030415403a11212803a40d00107401060301265090400c0c5c041c003042e2a14907902054910740b50321070f0341c1959180c0d40141c501900b4a015040e89818415949000790020006000750f007044907220302c1c0c0102e1514108650b6600c0c402804401c25a600d84880301a085510340308050311000e1405240c00280b00003804031207402d8030280440007507034400ca40c082640754072440154500c2e0804211080d010041e0340c500040381c407aa1440c100104001459461442000980886010354596180d09040141080b420741c002c115510308820408240d42c10140640581d00c6100100134410112000b682e8a2650080103540001c510140c5c213000a2040000d0842003294a4900c5c1482130a6002c6850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 414614595 1250 414613345 414613349
    0x60a05010e0d05031317010c0f3b0a080a03050301150e0301090c090606020102130b13050d050607090509061e01020c0a0905091005060904032a14120f09090402030a0b01 74
    0xc1d07111701081092503a401c111103c400c5004000f0040500052800341c041001e0210220a1150b5804a4040d11020401032040c90144445c0500b0744030f51055101c0e9142141c0d42128440c559424000c16500300c0010351360405a03050310750740c1c83d5900784a00300c28504040300086082001d48806081540c0303088c000c0c00f00844c0300d2200398002504140c45c0c0c030103950482c1c124108580c07040c1f0911800c20070600100781107a002d201c09990303603415140031400d40c400b02e40001c3d422004019104042010000340c80340305611580da11f440f001e888900700601044191031099010040c149400c050055820b90312441d000140126100b82161101041ea070034540d5005503042551441080300c1c0e610107101c203240d0109030700c0c002c100303a19010001038180d00000d0000780070000140c11b21106040c00a1845100382c02c04c42aa20081c0c425284c90700c2d04a074181d10481450084c080e860a0300482d80d019a0311640e90031007064100b07100041400413550000b402a64507108045d031840104800703241d5140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 414615845 1250 414614595 414614617
    0x81503010b100e0a090b2b0204090c091506080a0218100507151107030810051e011112041512020309010e160503070608151206060315060a05010e0d0503 67
    0x445668100b013004490011544180102800c0c21018074032550b40161140d00400d101039400d80c0d0b008034071a615114000703406d00940151070500d525050211045032a400c484d1000710074000c4031140c11401e60b0a0629100d140080350021000c5a0081601d0300a4051001c80001d80507910b480c1000007028400485840004034000140c2042402070390b2404003a040004981403169001e4103100f851184107103803026040150490204003200c0240402c2401402c000b4a01c040202007500c81c0c54002041c000040d020a4211941140c2c059010840c00c001941503da450300f0300b8a050821000741e029407070394004100c1501000707170000f00c00d48041c6d0302441c0540000513003d2120071762030746012003005000303031108040c1404111954001407039005032107082ca82b850494480d080065407140441c45201d500444028800d003285d54005005803040c0e0089048a420710081c900011351280c0a5800d07a82003039203c18180100d5014001c09812800043c1000601503440e0b1a8942542c0017044015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 414617095 1250 414615845 414615857
    0x306041b0f030b0117010302010807090f06020123040b0a0b0a030803090102041716030303150801020706090203070501090506070210053106090b030a050403020705120303010e0f0106081503010b10 86
    0x780415418421085441001e0034800c07812076020100c000030620500c0000e0412802c0800200214400c2e00b1950083c400740386007428190301c0d600b01074080d04415550751400ca011138410904c50742c1d4209042d0041d600a4402d04d21515003e40c02c101400c038200305c06401c0f22242d500040001e000200451140038510001a116030401c0c0740c5070a40d080c00040c0c150281d004404410000344940042422640e15060000d0000070030352151240150355405180700d5440441d090083c80306035046043c20620880c203031242d0300d40302c03c01524030150f1800341a400030700a100107001030414100f0804008054200300b0300301803180d200c0c800006040541ca800b02350b00504540d444944064025020781101d0500e44111420140c5214070340c04001c103251030943c1c40d58042407d00d4024000b0a02404000c0c0078402240b50005540c0d680358420300c00e42014203407800c00210030b0640c404030117060b5082569030490640310342100900042c3c0204039180e255503508050f510650703815005500501d41a2600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 414618345 1250 414617095 414617117
    0xa05100309140a0209070305091513030e0301050709030b0408280e010e1c021302030c04050306130f170f0a090e09070e16030e06070203030402031c0f050306041b 71
    0x702d40c4201d011007040300294071800300d09005a58111940d540a0585e190019143d55401000ba24008001d809040001c0300c5400f440002d1401e10340c00ca10950080d02e41901c40141042450300301c4e4170403141c40d80000c00c2c60381c0a1000a03c134030300c62038029000f024124140807601d0000c0d070408081c0d44400c03026200800300703807080340e4002244440503042424800e00700381660001c9094800c0e046034403100f036407500b1124021951594102e441407215010110340301d1420440c015403d034400d0148038401d1107030100040420841905500c0c00d944d20101c21101d000a80d0344005d0074400c2c107081e041440780300b8000c0061500741207001d0840e0f02c0040d901d84070641c1ca402d030100b041600c05000c0300401e400c001014412001500c903081d8201000550003110602f84900480060107040802421030117803406002d0999030000141d07004900072800d803420a0300c107007403095642078038000c040007081d0342100719054140504080c5d03502c040050300110341d16981810100210a41c0c01c021b0380070880e0741c1a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 414619595 1250 414618345 414618353
    0xf0f0806010f060801030f14060f07110a0510020a0c050a0609022701051507050303100503060624091206160305100b0702060702360f160e0a05100309 66
    0x40d541c01005100c122120b02801c10500a00040701404040c00c000c88203e440c01c00c01088034903040c408961030f8280e54442c141a0224078286000360f03203640000d1906801e82c1c0ca50704012075400941907200340101000c00800d002500a074200802900500184d015a40007291050202490051048078000780c01070241c410000d080d030303038407030301e498800c40c06800c140e5001d8640e142c09041d2003003203646044440c00c9903a100c145100b80b801c010568040030082c424a001c074014240152402103054038203d60b00e44c0140801c00b1821000c254642117615401e0780c090031080d006000055000e4041140b101110fa4914682503065504414280004000861b483d40c588121a0040e103200d40002c1c485160014550841c091264003034462000001e00400f155100c4401000c01e18840c09208020031030035901002c07142d035084100007240d500e640058003d000003e203c0f445200d03500c85040b0314a4103664200d905240310307483d064011030f040b940880d07a9985d452442c00c2c40112a5400310303035800386180c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 414620845 1250 414619595 414619603
    0x601060815013905010e070e090703060e0a2112020a0203040639120906090b03060a03081b0c040501050a06050f120c030a050601110304090c05040f0f08 67
    0x1c52241c452040100e041c1a80c0e0380500c060b20002198a5500203200006100107081503444050450710a01d02c404070081020640110484c0380b00713032090301c003056a518000007800f4002c840400c883c0c0c201f00f8091002500366844040d80880360b00440f080c03850203580700c2d1031800c003444240b50038280107400b1203699580a00440882000f03001f00794100b03100518040d5603409075001e11401d000d2041040c2d100340300b142c00041007a00d0600d440d5a808841c0e207100c5440f030880d1900644820300e207001816401c9000b0100340c401ca800c04d903030b10b201032460281ca5030300380d800c0503002691288003958000085500c04e405401e200094001d200b480180c540c01c083d1518030540d18286c000c0c0d0828004000030340d1107401441c00c8401500700b0580e13a1050b445089040d1240200d1502c0781c06900c01400074540400024502c03950703099a00304101c0e11864015100300c50114411025640b00700b0083c014005160001c822081c2a4203000d400d1a807203400e0750301d0068103504421200d0404601c01c00003006c00f00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 414622095 1250 414620845 414620851
    0x5040b060105310617042325150c030909361502120103020405040312050106030b121507050c0330130f02150702180a06150e041a0306240618130e060103030206010608 73
    0x2007019501c0b4101d981d4007510080403885401c54284d6030340c004500005600f0801d00401d40350b40e81c4010083b4800c2070f4401520001c61007a5240b01e0300c61604000f00da16031084030205501614100003680c6990708100160030024011010810f82484002c011242401041d02a222503100403e03503142c09828414203020300e440c215904d40c04010001140d0810200c41904040306e45407090380c0d100401c02c0b09181d407103500d40c4140c0c0751050f21041505a4085118032910088a0b0500400794699096124950841c2c81006d8100c1900164580c010b00d00110031700c40c02c6101c01255030400240fa000606201000d1000c04044100001044540009072041802030900030310411485c50706600020120800c1b0100107010b03039039640d900a40310043ca140c107a1402d40090441e0340c00e14000040301d40205e204c90343d60f182440c14044100c1c2074500601540c01411512102c2004c44c00d9103020081841d030024001194150741d10104103543c0d106118440c040c42c06a002003140c1d514050004040da0401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 414623345 1250 414622095 414622097
    0x1b060405090906040b0a09080403060908130605030106180b090f011808030705060c250c03240e01051618080a03050c06010905040b06010531061704232515 68
    0x886051800508008d0594091342d0300254001081042c52a000c001807041c2120000800e900c2c450000d00c0d9030b4010001c5068805070f84d00d0640c2040c0c40300c50701500040600800b4002034080c84a842e907402c008802100e00d0005242188c100d20049084400420513a0400a50f075040000c03000c0900c00e007000513581044044003503a2409507902e08000045150510400060382d05208800c1480700070054030001e141c01144c9003090540051202100300c40000001310054245400020740f031a041c8905441a0300f00c00400400c03442d044001c45080d40100700c14000001940408160920200b00455420f0304c607458103640d424160000d58a0084140c6c0030502e02400d11041100190950440a030016403c0c244152511803e900d140c50110301c580b0b040600c0740c00356494920002103400800215601c540341d45044011004844c6004401210040e000b80c403259846100c4c000060006106048840c058643d411440380250003442c80342c54600081d0b060185080c0022500c24550300300180c11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 414624595 1250 414623345 414623351
    0x3070f0b071a1605180907030606021c0519050f07052808070f1e0308061002010b15070f0f08090a080c010206040624030503070302060f01081b060405090906040b0a 72
    0x804000f0141080c0152401810460301003000316107100034400c0300300030140c0149107110b10701c1c3c1500e0040c01030526200f00b000502c40d000f00510345c1500c280c400d15001e000c1e88e0ba581e140c0864546261240303501071b400401008420400c0004020b0b940001c6e1010500c108080c0c40c6103100101842c2121200500740d4015201d030001c3c140006240d03104a5201d56030002c50b05102c02910f0403d805e101012810892900d8500107100c0d00701940010740328407540f822503180445044408049080b120f40e140010f81004d00354240c40c8020304564060f000b030a104003180ea000f0459a920b915a2490320007049840180c0400d08200718a44143d403600030f4103406004000390712052000030354a130307009071002c0c0c2100c1e41d42c02c1800e204030020002c20180d400d002c020703504141d941e14050f03960750710240c815401402901c01144840500b0030000b030403141240020320018450141c03465003490090901c5501081c200f000003907944513070030b10341d1083c4610000b600d181d00e800d0600848645008220319180ca103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 414625845 1250 414624595 414624601
    0x9150f1f08060106180504020d0501060315030f0f0c0b0a05030720190638010201060807030308100f03030f0201111606020306062107020c03030f0a0e03070f0b071a 72
    0x200010b402c6044400602d0440c0302c1c246072020014004140350070454003d400000c0c2c240b0700071095001541228240d0343c0822880b05820380940354001c540c000209036800003031082001c542e640c03806450440c010a50887c456603140034481c15540002c6407000030a5002c0304106000b40c000b14040c03001c15100c52402e001c0202480c4407500d40804102c00c503031468048c0b0001060103500e51000c0e00c8079400404c90711952001602d0380d120070610910140f414180039652a02c10b51043c0180300c112141c440043c210241955019110014010000c1e00e40d02c50b212400241014054402d03030066009440d1400e600c1454100203082d51140c0642d2a43c42c40b0070803031511180e07010a80342d0065600690300603280d44441d80000c070203200d0021f240000c02c0000d00004001001e260059020300215021202110b90190070b041c2c503801180d0b001192800c00f4007046003000e00035104440070020040588003510f844610b08100c04249030401c88a1a4006c030b020010000c219020744104081c14a2441540c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 414627095 1250 414625845 414625859
    0x60705040b030a060305060a0b1e0f010c0f0c060f021c050301230301020d020c0d171909051f0f02040302030d03091a090a0201030507050c0c0909150f1f 67
    0x803049210302001260000300040d03840380c2c598480c2d000b66a0041c00d59265040030540680500000d1079560f11580101c1c0320010340b01a010200d0000b00000341600700310012040066684c0805042c0c1601c95014800c44440020020a0030b04050480c1c0c1e01c0e00d1042841c3d044c6c00a10b8521805203098808200303c5150000c0e90b000f20a50303044404d480503583c1424070781e032510340d0300c14003c0c00e1640c1c0560000c240050400074640141030788040e003004498090039000c9040303481c16002400c0f5011a004803021070801000048900076010740b02c400828126015580c8a103402129044d00014240150b6400300051090081003100036004000303504290454000036100d901d01c02001003410750b101210710420100040c012100d9248880103522071070110f03100c0392900401d150490001c0d01d414002405140214160740913080080001c2940742c1e550b4003406900754007c0c1003d0141e20606500050405480c0c4000e4843e00c02d440f034039111814404c3c00a01c20303180f103c40400b078609055509201007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 414628345 1250 414627095 414627097
    0x1060f0909090614130203070e06010203040801060b0408010b0613140d1416050d1e06111c050121060b01050405100306050405060a061d19080619020f040306020306040e0627060705 79
    0x2d1027055001c3c14407038540800613803540c40f4550100005e542003a0000406400503405002120f401c80000d0000c402080c0030841c040c41100000460700d82009010302101102c0210304114203401360a175140381d226a100c21400181d0b0940d6160301d541b0224142015010002d45000100302c150b8040000705469503503080d02c000000d407184005442c0c00144c205020b225008008006050401540d84440184242a08420203154103408a00742400080c040310040c98820f80c0e400207081d0101013100c555500d0707002d000d18200345810804c0034030010480b030f964410207654101c02610b00081c2c16190400f804107962000305010f1056112041c1042202c0d00010750710410600220b2840d8010b491000040348403902000c809062001c541c1c000c40c00c20320000364640940444604600c5400358000700c00d069104604500010301c2c014002080020a00c0e0060f42e00035100801c00b0941c0c05400c00b880d49054401c0703a42e501c0d00a6504072403444900f0540e2400c1c103074800749000d03084d40d142c044009040d03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 414629595 1250 414628345 414628349
    0x101a0112180f0c050a080303070f09060503010b0a0c0213021e030717071e080118060b160f0605041209060525050f06040309080c06090901060f090909061413020307 72
    0x200306801514104000e502c040e810b0207840c00800805d840d9483c0c6000e19503e802c11180742012406148000c40c0403805156400c00701d46007030303540078510fa0070584192500d030006103400d024021918541e9005941d00620030360000c00c3d0010050b20342c241e041d01342da80101c83c0c813001c1c4540f1030304005000d8071540c0000241310318044030585180b182c07501201191007040440000015200032070400c60a82e61103896a41220011002c0c040c1000f4540828421540d162180030013000d001c002c038502024000040340f805d107004241c5c1c240d0f1080c003905d070300041d40c204607021540c0303c0103412a01c0b4020f81120502d4003404081c50801e041018004000700fa030b60500c0c158100c0c14443c0f818050400c0010030003480ea54101c4002d0b200d180c01c0c1440e002c0d04130781003030059059600a148026001d0b051003819603000020040c480300590b460540140c41940d1315031401d03c02c0010325103011a8460031801021311783c3d4450240040d08140818614902110240c02c80e490b0902904881c005660700080d0001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 414630845 1250 414629595 414629603
    0x306031b091b070b1608150d0623100503061f0308130512070501090b12041e0f0503030f060f1f1b0c0f0801020f031602101a011218 58
    0x1602c9482481c00700c040c021008014400c140c44003c105080f0340300f121403079030b0982c00d0701d840f40c440c0c8404120907c5e200614000a0708011003074410000b05025400175030003501c0000318801d48030011000e005400d40100d075000341b041c0100104102d542010002c0a901c00c0041c1e24000510010b03a00b440660780701d500c40600308c1c5001041c200001c0d0503200b01e55000700380003070810050400e200011901c481180c400c0c2400700310340640001d840c07030208045488450010948901d640d072141d0b1060740002c542c084408103881980040c500149000541101180c004c000550310307842c201c2100707200c584005100b02c1c014890110300f40425143c03100c0283e1004009800380c4007a00c0c027170740e08642030400503103189401042e0310740003400d03c00c0d1002072105403001b16201a80c45511201000d090b4450140b10a244210400010b01e9070702010382c040c03504107803031303c1031b05c5807440d0006c44c40c0c0c00c0d40d20039601039100340c20b1440c0d2160a90382001c1404140e011808090120352410f80e214030920f00c3d0300e00c6c00b070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 414632095 1250 414630845 414630871
    0xf090103061d0a0b030c030d0309060605100801030b010b132106020301170f03091c110d0c051f020705040b0a090c080f0903070b28060b0306031b09 65
    0x15006a010350044000b500380320016191402e0200220700c8840c4042d00e18061151900e800c8043d03500700490092202c04010700104450883d40c2809c4000301000141503441564400002c01c1642ea503035039415403844159a5a00b042d411030400484400f41130340100c4a0f039004002c00c50502c188840b1800c2141e030f0340140016403440030a0718006821010000803c014400400420342100d0103050701800d602310300445500c0c400740a50242d40e4858500c1c40f5900014012280046072080301001104a12070141c22158412236030124014a000000490702c104000303000344401c0c10000509001000e43c1c109004080d004000040d4075035149000e02405180c90f190f56000075240d40b100703500100003035070003000355203002e0710002c150a00581cac0c0e1220380c0520030f01260303140303c002040d104e0700d98014244c1c9007542c481c80c0206803500e00c034880704050310404012400c002c045a1080c034000748464103000e0f40c0c92400c40100340c00c0c40003d041c2203001c84a501313204d140d5030b25039840c1541e008043c140d0381 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 414633345 1250 414632095 414632107
    0x801030515040302010e1e0d141806160501060509060d030c031b02031002040617160c060f0905010b0a05031b0f0102010608100204050f1804060b0a1e080d02120f 71
    0x200c5c050500c080d0b246981d4852071314080411044070304c0d040c1c00701607080281c4202808441c02200d040501c099200030011090051501d402441e0b025104408401800d0301d1421562415000300790607030140550700c42c0d6480c0010401401c08010840e4040700450f03041c401380080340d030302800305a00340f03a010b01000280010016501c1c4030100071800240c00900310f640052175000d142e006544140910f10019403040640960200c0c4261103030300401c0c8618000161010f00e03d01140e076150040070650300c0a480e80142c4410801603c0380011b03c0d4018000411407452003006c1c0b2950301c3c01a80003a000e81d01520b5000d401c0003101c510500302d00c40c2220540001c481c0403004074094542904641c0231402f071540000800c5141d0390003003048038410354410142c0346101c1d0070002c000c4070000b0502008c07200413002074009005980b0429440800810416481e43c4030742e0324001c5100080d50318040411009828040100d04220303030507480707246100a240b1440380754a010070502170141d4807454a900440c0d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 414634595 1250 414633345 414633347
    0x5120418050405160b0c100b030a0303020306210a050f0f0a030c1b0f090f09080906311703041511070312031b0903050c0f0609060d051608010305150403 67
    0x11262030000aa00c0e000304c19450f850111403641c8000c28088a40c81034644801c041170450080d080f8804006000c1d1072142d14039202038010303500003401564441e2070b190030486141055009860a10036510003400c200086161851920701a2000012154080c024480385060009100c4cada19603414908600c9804040c41c0019042010040b41c0300980d50f0804003007865004007451004440402d0740078003d12040c154818119414050007400907502001002c65a091440c0180f1124801c41d03003401c1e04103a1404002e0b454124008030398210800140100880c6034407080c2c503205180789a01441c503003840c22140900108102c4500c205110f109005800d85540c14031185004603007200161400300700b454401002440b5040c1d00c81c001826a05619403201d101d0451101903e81c04402407070481141010015503010200d06541e01c5602048401926281d03180a40b0310005600c40224943c1455026010407030100c0380c4403002c0040300c4c0010000700c1c000042a20040003513181003109500d644c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 414635845 1250 414634595 414634603
    0xf02300c0111032a0a2c042409060803090d080c0304031a0f07080c0319060b030714070b070305040f0501090f0524061e1c05120418050405 61
    0x200b00c1124040c00310400c60881d0312542c1c901c0e6041c00d5070030107102800c2e1481103420030340502c81d980340c00102e454401000c2c180c005030b46100042002007031501107a401c00001015100803815650049080388400034000700c050562001a00d00608103010307943c18947c41e603039240141d02c5654481c4010ba011001840f40c03000c1220401c1c190f49003600e507120345038140f5200d40800b14900c000b04011450004040b005101034280c011074203955072000940f25069410701c160009000181061920302c186240b080151246400500d0301d000504d499181c202e0340545090100203c2c00e80c135180401c220340005502e241d8090703200580d27040c00036140c0c4950030010105000b025004060798a00007601c0107101c107050107000e46601c27881c02c50706400303016400342c1007410450380072031182c01092010170403501c1d0100b40c0e10200c12058800442907040d10300010520300451003800d1501c00510701b11000d0002c05d0000c1d20180358a080418901881c101c1c9840751064072002c41c3d80c88598801c00329041100a01c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 414637095 1250 414635845 414635861
    0xc02040c140d09050c040e19080d0c081605190507061103090102031501231b031914041d060d0b070513050307050603190605030106060f02300c01 64
    0x30711030644612150740ba0030000d010300c260a880c0c40c03091504a001c949010b01800000e482040040d1034010b842100c203400c00e81004204460050042c0700e00070301401640b2031a11051300c655641c80d07039406d01c240a1000d15450180b00410841c080010300b0036400010228042c0040500d00180c1d204440d00385480140301c82c0c0401020320300c000050190760340054020710f0054508401c056500d40c03100700195a01280200d400b021000b0300c003007150014000e0b8003e0140b801210303101c18140b001d02a00541140d1012000c44911a42d40034140d060a9000e542c13503002038105403105103018107002d20384d030804ca40080003501848443c00000e0054882d0024004916400141074111b800c090303c024040360800e503e20744084101090002d401d20f8000354690840304040c11603403943d1600018180d0301c1c9200205031100d00d803a60270004140e282440f89000401440d59074040d468604d9034001e0602125200c0b51a0364001c0c2040b01c1040120003c8611a00381700882080e981c078080c000705e82c0580068 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 414638345 1250 414637095 414637127
    0x50c0309030a030f031530020604030f170c060a02030705070f05061e01050f0d08120c030a0f2903010f050a0b0a0f061403180604030c060c0c02010c02040c 68
    0x108940e03400705908084c00030129071860721705021420f003032503e00311209100d11031070643d5100c070715054854207415052520000418030344040c4440d09500031480961181e8000c484c106421044070302800044a00624020100c255251420383d031101c81d00e580d8100600111807556000000c0355880f030144044803005540010041c1e6420028103080d5100c0004031380f030141000c040e040c00501c41c0c0382d0b8403569040c0c0704010000c1703a02c040903a00703100c04450310742004c581c80141000107520041c041c621881c8030f558454440f655929202002005a90001403031a0340c0b1810801d90f00354074002900c6030394030103031910300303c1d0070102d0004006409044c01c1d55800c0403452422050001b2110b0603000703207890781010744a6012682d07079064540d010030750314403407200001c13810010a20009100c000a5400080d0400c03400d01c1c40e03850741c45140c00c02000350360450114010800a2082201c68090006840907908190038008100d4001030301e8200c242c00d000780720b90340e1f640442c03603074500a0031018501c101c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 414639595 1250 414638345 414638353
    0x506011e030203010c0f020c18150f0a03060c0e09090a0209040c23030f030301030f030c021503090105040201030e070f0603050a020d09140f070506040e0601030b030d0504170607050a050c030903 85
    0x40c1031781c040d101c00406080038005000b03400000c031440c10019184d03101f00d101c04402c0150307660398402c5514841389a0b498554043c118a55200240e5500101700b0007440c0140c80001d100c818400c0e01501c00b20f13503282c88501400000c02001203000300418545045501a2529a8103a8a130710308440e01c00d90303d0300212684080c0c0340403008003442c200c0315054816000d80c21140042c5003890219524042480028000080020620b00281c4644640c48110744060714030418081400e0560342a0340007280e144d4002ea5460040100355a03041c0a001c0d581283c400180c11000e003480040c004852a0707000d410180340d00e0f01c011a00c0314015078122414099100401c220200d01031404226080032001c103003c0390311a01e049000b40c003201040d400c0c2101c0d40249101d00d0075140017031f07040216200500031814907a68220707052b03054405110f00328000700560341e0103503181e007040d19007550b00101125102566005800b000381160300601111307040111420000c0d10340c204110101d00e10b01c9009002901401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 414640845 1250 414639595 414639611
    0x81302040c020f0606060f16110409060b1905010f0c03021e0a02190b071713030809131e2c0106060306050d050a1103070306090c030203070608040506011e03020301 72
    0x2c1d001c60340c01c011032210004c0d54070a48030b80040202034083d071022800707000d2007044040c2c80d400c46d4588400340700b80306022a80c41003980740002011150821016140207444540d0001c40d8945080003912040c0d0b1400e0030505141030100081c03034034000c0b5080c101403020002c000b07024903000b0403859601c1000803620306c103c5202210f0481e2191400e6504078001c440c0034071004a407202900101050300e0a05101c0c0d418030109444440d0945020a02610007030300c10049044802010b503000b5014501400f10310f03540303282d0541400302d00000368010170080352902030984107280d1414240541c1000401c00411000c2805400c00d01c20b124009400c8049001c0d042e00c070004d9401900700340111562920100841c0740d43e002881031031050410000c0403034000404034000174070310704050f01800c140501154081512666690111000c5000c00c1d91800034210003041145404c1042c41d01404451a04c2a03807810690740e03480d82d80b403060241c10b911001444406040d0803000c80e06070004c640040c02440076030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 414642095 1250 414640845 414640847
    0x50c07080102090f0102190201050f040315060312030b0306130203010b09070810050d021f050d0f0e06071b17190507060605060405011202090307120b0f0a0b0f01081302040c 76
    0x50302048150b40218182e504100ca05c0d8008120000e451100c101c5800e5a030080e40d00449069202c8080c0d0306501d08180004000f10380ca003607401c400e078a070105000561074114105883d05000c00030711102014106504550252400700304540c0142d10349a401e001c0e800d880c40002d02401c04220426003061150040101091380580b0b15409001d1100014009030740303c0c0c081c8400e20701e00c18400307504550340c0d103074842202c0c92410b046100c00c032051400b1800c00f1021180c00c800d9031611100104095121840444a40d07824000750741c10901600306070840080021465040c0a01050003400700c21030b844506100440c0101220381e004407000c1140014110f40c00040c005801042003514900d1600700081511b00b000c004540581e40d05031100920b180c69050042c0182d4803d4042e5034060240800000301e0b107031a104031032040c0b880f40d0045441890101c0c91904c1c09400200302202c8141003038610010740c2c1b5040c0b50782d11500340038038010040d90344900a800b000e1090381d80080d00130f0314000314a403c0ca = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 414643345 1250 414642095 414642097
    0x61009150509132603040b0604061a070209090d0903080a09030c090501080c0d03120f140a1b0c0804141c0521030412031e02031009050903070c05010e01050c07080102 73
    0x240c410500412000c0e1142c008059108600e144c095030041d0403c0410b001c42d1112452035404070b001440826080c1d280c9802d4000603000000b090415440400c1e034004518000020351741c01800e080003000f407603043c42c00c014410705d020b11010304000400112103a44a100c0c0440c40c01a54000c14201d006a43d9050300000411003446035181500031000f071a40e50740b034031242001c03080d17030595242241c2203481d02140000b4400c1140c03440ca01a6512040344501f100508080c1c4142c4038118001040c440403450303489014102c4601008105130905401c001130350081c03d840c25510b807503184070450201d04010032255816000c002c0160300c0030394800c104220001503840040c0208040b00020960b204015007101d01081e07400412043d40a03516a15032848ac6d400641c001c549a580030f1404290b078181c0070f08a80c01900c1100c0c4110b10317150140080d81c11400b0361a0060300200040d80b07090f0712134880c40d16490f254000d65041040c1c00303104102d6a031054054a4600710420705032805c071a9036440c00c50003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 414644595 1250 414643345 414643381
    0x111012c03031302130b090405100b090403020a080d0225030e03030403080d0203090a080a050a0906050712080c040b280309020a0909170301120311061009150509 71
    0x3540e00d00c1000aa940240402543d010302c044100002141c0240da00300003980d1a0501c65404056990120351803a547e201111070045008101030484450794076410000da41c4014a40b5015076520428000007950001d0050250340c0c005002c02d80f00da516802e180d01900c44d036449144000400b000c80600c1d03004c2c0c6150345070154400c1d11a400003a10450074940c80b03001314400646000d000b4020040c83d18241d400440e4010259819181900c40b02d82c1d41c01003540060800360000740c004202c0152560f00203080d24041d115504100b41851500c4c0d0310720050681c02ca890104100803135022030a2101210300355006850200d040c15201e11850b407202c0d8842010035141c291002e10a41e101080900038440d000c00150040e2090020500744030b03401029207640d01e17080310601c81c40d003104051000e0b800d003c4d42c044c00c0d03180e4046132140c003a0304000b4480356060894509913017000051056241007200c1c01412144e0309030b000f05881d01c1c81817a8000841180c0d00045d00030b1010700070000b0344004043c4500c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 414645845 1250 414644595 414644651
    0x12091a09031c1104030f050304030215070b07030519091109090109110402030106020a080f09040501030c0e1f090b0a030507030b010501110a05030307140702030d2604120e011101 78
    0xc0025110140000d41d0410070f560040d28204000910100324500400010940a071048134505541ca80c045400c81c00002c0e1010031005000c110001042400f080103034000d000c510781400142021074140810380b850120051010340d0340d03004401001031a46104903031050091040be50b80c48d050070014081c00031400f045845090200541000385054401e80c2d05840c550707070060401e140c440d030320b28905134070001c1f203240840300501042c180c80d521402158040d501c03403880c0d101aa8605590b0386c60404000d8841e1460b220700c103440059000341c1c03a41d440115240d81d070001c13800301e2040340840e1032030006400140a40c098050301100b4413042c0d900850403a0b000ba03959080f00035a0b40091a00c030b848524000300150010000f1582da1072003a44030713101c50640203002d03618100361640024600110701c0290302c08143c045210035008440c1c81002e0302028403a440d003542c17514103650f84140114460070310f6001e004045c820400c03282d11a040030501c0c04003400080140540443d10400301c0c03110f21800c14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 414647095 1250 414645845 414645877
    0x31b0204230a0608060115080414010905161428090e0307050607020303010e0109150803070b04030905060f0904021e0a030b13060602030a03090311030706050604050c03010612091a0903 81
    0x640078030004105c5e049601d07843c040c2c25410104a0708841c0060060301c159105900c4580303001c40d0140038070401c3c484c0c511a01c0140b00151111342c2c40f60499115901107104907805489031162500c59000e00381090821100c10907130036840700d44c0c01c40020025002245070b5460f103000d5240000c0c00000922041d4050400c450595071b030720070101d81d05d11090042072031440d4010010450104140c00c0200342011140081009a032100030151954000b103000f5124802100240010f06801c201500c01070107043d0780c8a0301c0d061402e2040e50040c400c00c1d4002e030140d0780c0062007a80803401c5041204035421400c1040c0e9681c1d60300c0303000401400031800c0b240e1140010081c803513800a41c0d4483c0f0030403030744560051420103400351404ea004294080c41a0140281c58000d015020400c0c4018220b0a118100000d4241005810300048501c000c0400f848068100014416182c226014a000020204000c90710307003510300d04440074040c103501a0141e0f154440521003000004030140201c210341c03250306 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 414648345 1250 414647095 414647099
    0x30c0e040210080403140f030f071d121204080f06090d0e04050403111606121512030513030b090c0405041106130e0c190c031b0204230a06 61
    0x91004240c500960080c603548441c0c804030300400010f0f90041c040d0070320140c0c2042030504200c1c1584442022550020004100314200d03d20040300c941121b114070f081d0709017140000c45140554000320105100741000c00c42d01c1022541007128221b148620071059803201e07036441c2c000d9502e800c6540b40005900462000501080c00000e4070303d0700101039070b80c118201c0d0000d010b00000f031902900c01d90405c940c82030f200e007901d2000c0014102d0825841c94015025282c902d0060115203030301c00f5421107504201481344601b456240c0714050710003000706d41c490000d81e403400780c40d2031054029185270680091800001d01054040241c441c82500781036965004a50082104031a0201c4006000404070b40d242e81460910401404a00410300102042c0a0310340100c2c0c8541c440c1140c004807113400005401d01010b03510010090000d1040c05d250b00e441440d0b603406480c19401000c10080c9981964140f800d6644070b0308580b2181d01568001b0300800a4080011031040080364045101d038103001340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 414649595 1250 414648345 414648359
    0xe0118120f0e0603060628090e010b120919030504151b0b070c0507080a03020d0f020c0d02040b09090105041e02130f140c070201091d06010309210504030c 68
    0xc060707803407207540c0d0b2120307801009041000300d580c0001e004586c01410034443d200700c0c1074030f4081c0141c1006c0710340d1969025203030b103030002040c65010350001c01110020500403ca40301c4a0b40956014082a110364220f07996100d0185151040c8010b0351a10f80c11540192014103070040c00800a03509034000700c0780300c02004070080c1c0b4040d02c40e0580400d04e00c00740b400d0601145480034280d801074241c0c54825070010061725030320f03d4608140c110664940151419004251301001454203210541c14001641c1850040c041c1d04c50381d211080900030040b0150710b01c02c544d5164005120000d00424841003400c0c4019054000c1c4011981281e00c6020070311100704100c010300c40c00c4801540105110007280070851000f01401005158401e8552204c01c0e04400c1124101c0d1244a50608142140c81c0c022500004000290642c0440440801103016402d100c07141c05074103a100c10b082c00d020401003405d01d002950744081d10307074603041c20545072140a81c543e0300600400880e8064194440c2c07142e19a09 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 414650845 1250 414649595 414649607
    0x50a0c0f032c01151406040e10031406070f1803030c0602040e0403050705060c0306090106111f0b1e03060402010810050603010b0a1814060c010e011812 67
    0x402100450445100c2869040c032036084104100718195110102c0410308145500141c101018031440f41d444000d8841c0b0f0703100746440d110040288440481e403081030640841d001e8403c0340502c803000d25a0b480054800007901c1011801950b00c0310503010f0480a410206403201001d440510002d00d040d1550840caa01c12001e40480940300c83c80e61054600d9690150307494804103400300c1d5096000c0c007000541440341c0e000e040c41140203444045e9901d10300c0c45c0c5903060400c000c0959030140400d0061050720b488440c3c0140c1540d089003000c0184010f5041c015280c0800c1608514113201d100d104031081c1d0440e6040f004030450160761a001c105003d1201d0300c16081960152505540304d20001005988140483c0781c10080c1c40500c1c90345562a0b1021520741e91003604203424688000405840da503030310801c04861030083d1078210040303e09101c030500340c030989000000d2003140c0c0441c02488001d0300f075000b1441d007010100200004403445c00620090440d020f01582d500e1410026031400342c0c080c02d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 414652095 1250 414650845 414650861
    0x20d02030d020c0a080a0207080601091401030f020f03060a1d030408061612060914011e05060a0e030114181b101b03080f13030503190e060118050a 65
    0xa0080e40c1400ca01440c41002900200484909485001d60309000b1601d40c6000b03000c1011968061700686d414001d0300b518003241a4441e03c1d0143c640645640b40507454100d050549502c40340c5901035000d01d00000b2031401c04100c02c1031b414003031401489034800030f9a01c0751030607100e4040310401c003a418103a21900c9004500c58a14550044000207030110078501d1243c0c18080541000c1c4012401c2900c440d04a80c03254000c2c605240d990001e04501d01c111003000c50040007000700710940100344600040107142948a10703800340601042c00b4490b60301542071907141d008013800812103c4140d183c100f0300c520060b83c4004183da0b003910414042d61000c100c80e408142c5c00100320204658160520147d41602440c0804001045602c041c0444888580e4820940641d032410380d02d05000038a5048140042c04200c0d810340c500107d80c0010f82c0080c00d60364403281c104a0704500342c01d5072074120b024040940402031140103c4001280010070300b1450081c050444000b01700b01e503212102c0340c041380c0450f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 414653345 1250 414652095 414652097
    0x206270409050a0b09070e0406020301050a0b18040515030a0501051e011a0a03090804080a050d0f020a080306030f0a0311100c050f13091b02060a0c0e0603130f0b01031101020d 77
    0x2c805900003040c0300c0504540c0110702c410031100b1451f520f00303c80503495404e9800b00d07103083e000801000325180100540340907140030419070303103003400c00040c51840350030401c00e80b400349440700b001a88140310340048d0810080c01030262000400a0f03d0414000c01e02101d01c000c41000c000c0070030880b4081d80720158161005080000e9031102110804960f6401c2052103204142d151050080001c407240301810040c0400d000402c40c40c0c0880c03509074107160b400700800007044210320010007002d50000e81c480a0507080b4181c160307030b900c0d80700220782011982160901d051080920300c5003010f910407021414002448151400d121440c0300d0b900545c0c1d140448078001490a104009a83e8103220041040d0f103c00c6500c020307001e50355003444040c0c076191081c050070741401211503482c1c3c540520000b5800100c1040800c00301030008405008034420395252406408044001100c0e1041c8948040c1050b4102d0101d84c0140c52a150001e51584240801c5420001e003944889540d400010034001000c90303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 414654595 1250 414653345 414653353
    0x90e0f0403051c1a0f15090409020d0c0b04030b01380d050f01150504050d170f0423090f07030c0e0a180513030c030503070507020627040905 62
    0x3480e10111110b40080e40d0781e80e54260681241e840f0045035200c2c94044814050b0605420542a410003d010400c01d8510340111011082c814003c6110012540009411030700011591010f002180540d580300380300401c440040382c2c000c980d100342c0001810469100314807a5190f81e07214980081c485221030007a02004881940c204d44020030b10350300c4102c00d414a140642001c1000c400c1034252003040d00c00341a8811220018000100c07102e107200c008444074148180780c28036110105580507600e180160111035100009111610f1440c1103581444161000319161901c55050034a455600200c2c104116841c5070000c00c1e43c102a072a83d4425000c0c100c04008540c1c0b400c00035000380440d00454002c1016044180da0356a90743d58074a0040c1c480c0040d14540c038a80d480710801201c00c080c0c10480c902002000010009074446c820700556649464401d8490311041800d40d124051010001d5015402144144803010000c151800f0b038103d0485031100382e03480784140002c4600941010b03110f508 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 414655845 1250 414654595 414654601
    0x30d080103030e0d0b04030f2a080a090e0709051c02090415020f0d02190305220c050405010312031104060c061503020d141b210c100e01090e0f 63
    0x4025403460100f01c502420782c0e00b444281da40c0d07112900b00112412404250158140d0b881c0303a0744003030004040420b03c0042000641d40103211003003854000c40050000308000790143c9542d1048404c000100500004c00705a410000405801d00780180036085c0101c03a4003008641c4c0919a141141d4180e401030449941034540da110081401d824a020a070400c1d000c005604402c51074500400b454005c80ca00141c60304103615840f0100c011100c914000c2508110601c500104445102e03a0b10307803502c90780c61188080b80e1a24041e00a00c9030701003584586842b00010501200d0569074000111581d400c108a03003200c0207010303481c0107500805000406628005d030014240381e0000c4815000d044036528110350340d900050903994501012901031948041d15110b00b03a08000c007140380d41030f40101200e05c1e03070300c180807078021004200c0100e0280158902d05185540c203204101403280d0140101c00c2104d41d140003d07004035114601c260005030400000103040c540400201e026918554480380a61 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 414657095 1250 414655845 414655847
    0x803072109242d0f0207020a0b0304030e04110309010c08011505091302070c081006062a1208070f0507050a08130905040b1801020901300f020c010b030d08010303 71
    0x12403018020480181c1d902d6081c00f01018039654000c402040710046601400c15005081c2950070400d6041c0f1a5801803040900681c0c03040c0504064912214000340c81e079546080886401780055455074010b8a40b070010380f0000c1801c802184215949002401280c100740c0d801c94080b02c003442134800403140c954881c01d11030b1140703008114042d402090070540700c00310700340807049900c01d0000329181210782608010355001400002658400c0031010803c00303241c00c1e005061160080a0701c5c000300b60007910f080360f10404000301d0300b1050700403181190040507140c0181034103c0a0700c818001ca10890341c4003d401d071044084a851a51001c098650503100c2c1d41d4004650304441c032070420800c640074000c901c90415101e402e104500a400440c4103041001011034500c2c00040c054480e64010003120080c2d1340c0080244540c6800000030440d10b414070000d80d20070961340003089844508240000e41c0e1007082e1307005040c100d8107090017002903407002070403d9514075000b01850007003991180100013103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 414658345 1250 414657095 414657143
    0x1e02011106060f09101e05040e030c060a0506060f2106030a030519090e1e070e1809010e01152606040803060f0a09020a030501060810031106070803072109 68
    0xc008560389000c41e1540706c4111480000c0540200c0d0b01d01718025004002501e000d0150781d489041d0300014502e40b1801e001e516855420052203840e03100d0300e40780403071401d13102c40044410030400307810019162a282d0494682244049100721f92854040300824070300d00e0301140300d04030142e07d270f00d9080c42c1217101100d16142c405520f1000c4140b141600c4000707919000800403e101d40c0c403001514034803441c000c07000418494094a13400801c0314004445250351561401410200d17601ca0411401c0d644550002e40500b8240401c04901c3d4200074141007200f000e60303002c9083c4c0c2c3c1450503600e0442404088062011041d1151680c10b500220100d0b01042c0080d0045401000161800482c9204500450b0300007016910046000b5400509018599814803840d40500501d01d270440c2c041c100126600300840d40750001038004600501d00d01d40c5661b88800b2207003c640e0050b19107440e4a000f80d400340c0f1004108a52960138000070350f50261100341d6202d420500c581c41528040780e83c42c12503c0801c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 414659595 1250 414658345 414658351
    0x50310050a06050706050c340f03020a060e03040b030403120e0106090b0310090b060d03090807120515040804090b130f0b090a0b031518010603050c0406050a1202041104031e02011106060f09 83
    0x8e002011800d085c007081b44001e4400c0c0c55030280e002040d1441d050320344181151090710526456801c1130209104441c0c550048a8000d038040c0b4015100c10000422540107049030407200100390310b00040000e910049800c40d1003414002c07802d8442801480c12580c0681d2082100200301c0c0d028030000500500e422905580518040d140001c0c00ca520360704050301c0d00071540c129180706408140030001b00501003080120000103540b8604040c101540d031000741780602d004407c1c51035200c0e03070200c05584902c1c2004401c984400420b102c1c03e00d010301414010581023032401e008900140c0010b410300c84501608580000103001001e143c52120290264000060400310982c03007072404243c0400000d00a20000d58092805464480166400c000442c0c041d68000b13401072803400c00402c40c0c0215240704980d81c0e501031b030307001c20305540e4490115803620031758100402021301070140c0070f40080b1400540884c103100780c07119240280c01030b00190f95218200c800c40c0e4072030024225000d150810040c0150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 414660845 1250 414659595 414659677
    0x301030605250c0b011205070501030f020f040b04081c051c0f050f0604050112020a090c1407080706050c0322140a03180b0a0f050310050a06050706050c 67
    0xd8402c01d11500c0520000268401c0015403c500b403406002c0b4114a86005144c07030301c0c1c4081c0b0722005580d880c0d194441440390b036050541d0750500041e803814a0301207540410070007020b281e4850700c0d54150301c9290810b0047c69002d01c104031800645200c8008040300c0900c85032642403d000c20855245032400010600001450b11413400c10f0807002c040c029240150300402004030f291403c481880308881050388a030f50002e461003038110143e00c54030031104c05ea1320004004129108040700036151130707440c90488810250005056400e001c010405040041e02c039100c02d114944402c1e2000d0380340e010968249603a07003281c040311b51050000c955601302c8580316000080410300040d10041c01c142d48a45c1c1500800e9240910781d50b845400b4020502800302c91a60314140111020b00800c0030801c44610400d10030000040340d500c22804450500030a07004000d514442d40300e05000345141c010314001c0740d29a040c200400c0740111040c06596468025007a82c4004c90310170180b40050300d005000c482 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 414662095 1250 414660845 414660871
    0x30301050102061603110723010b01120e0106030210050307080a0911040b01140316030b0405090c0d051204090e010b0a0602030306150708030f041407080c10031e0608010c03110301030605 82
    0x406d02c545510081c0040d28001c46011862400225002109410b44c4d0a0f188080e40740441c100c41381c0c1e030060a241810700d003030100003820700c170904180c1e0700425450708060b40c4140c008220700030041d80b0100a51040080740d407105440c2d19040f419509449844800500151021480c82071509040d401850000014036140c004051100d111001c5940180d400e04260a4052600f02001c0e0305805100000d00c5e054070100424982403040c242c8403011803140b80d106008041c50711091020405c00c0c040c101c14040202d5075a15503541000b0300405503085140215402d00741d4508051816441800032101c2d00c0d00038500c0e5560b14810482e0724641d802461090120034000c00000c5511280594070442d01c201ca14019410b140c10020340c100000c03083d03400d4a6020900c14410a44003150f080c0703141d041940c2c010b51800900200350040d0040b03444007079003441041c1c4281440c203001e4200b8000c40c1d0540008020003001d0840403020b0325004c104e0b09021702410001040000c3c029800682e02c203100040503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 414663345 1250 414662095 414662111
    0x809040c0e030f0622021302030c04051f0225181a0a03110105070213051f0605040e01050904020102030f0703020303100e1513061a0714030301050102061603 69
    0x101120320150601001500e0314145015900302000503042d101c06074001090145000f5121040400031210014441c00300b400a40c0c0843d102c095041c3c1c0e6420b04e00d0010354503458210007110054210f842941e101d284030003101184507424044404401c8841d078094844044180b030340040426a008400c401d69040120000b4400701002e03101c000c83c00380e03210201c1c00d221042000e0000c507200c0684540301d107642001c20000525011401848601c00b820200e441f4600c074000074160301400e40308101d05508000c1048011740500e00010003900e2031516403010540c41f1242120b84d40a00d01800810f9403800e001070000386010351040c0c0d44184144100d9260414081641c5880d030001601240035a0001c02480f405201c04900c3c4c9000e4a40d1403c4141d075442e00501e1034bc5065241507039240a6044000f5181c00003c064001e940602640781c1b0002c9200b03804044403c1c16400100300b500c035029117007070b110000390001c01124104c5030143d009298545440c220140008100c550078400d041d030f5040c01c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 414664595 1250 414663345 414663349
    0x70b13020a0f06030e160b0a0309050a020d050109030206010b0f090d0804030503120a06060513030b180115050102010516020a3f03140c03070c1407080c130603080a03090809 76
    0x1c1d030b4024110f50364020480070701403445503181181002c400300303c04940540a00000e182442610f04044c1940b402203101c00181c100300342030102c1c07444080e400848040c5000d0a1000540011400c14481d0b0f08840c62681c0e01c3c0b010304113a0181300a403214242d4100004070203498181547c4807058002d01c1300c2807070b250303803541d0301e40ca1503204a44400c140080c200c1002507511041c03062000410b4203007042e81c94180000001006040c85000042c01d08010201041c0c1450390340414201e069035084c0204120200e00f01d80d50760030090341c41018015820200050307034402c5210b0007005010ba0a400070050003280e070b65917925100303403081c800c00c9501c000943c0354044003408041c0350b004da021140000c1414442d610003019990a0385241d10008070000511280c81e4220003140e034407010618103e01140a01c2c580402c40c4c2e0410055076159204079100071401541c003103404800a00120b0b84118407041c4030302c0d00019070314903220103402e5010610218a44c07502903080103401c18400c0e101c10349803480c1e00c40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 414665845 1250 414664595 414664619
    0x4170c120a022802060403150f06060305011401031116050a08220806040b06370f120f1709190911090a12020a0503030a1112070b13020a 60
    0xe00000503400015140e02200b030f0b1541c41d000181402c15000105101500420030074481d900c40140f14000021940c960328106a10083c066001854140300403551110020080c1a0a004c3c0007000e9004402031440d075030080c820000c0d42d8650011543c00d18004205041c038818a8074001d07039141c0602c042c10070020744140010800d1540c0e00c508941840b41c8003030408803018042d0080300955001000f40070100b00c04244250740401c0445010b1108450f00c5042e0288000001e00b00082c2ca034078500da8509400510341c9802039031400c074500d00e00d01c1d50b1b482c06504122400d5101034072951b10350420784c0210b88180b01c100d10f1f0b0b64401880e5482e1104c10004a51000c442088588004151000520000500f8041c5540c0303950828115801c0901203c00103407289581e21030078860f09020300c40c0004640740c44012400501008090704d444448c20140505040800011200a805042405002c806110081e070300308607042600303549030343e0307502c1e1414080d0b4044420a0b0f9020418074000101880009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 414667095 1250 414665845 414665857
    0x70201120b21011b110a1b1a120a090201051c0216030e030f160b09030a060e03030907080105240301060905090a02090a06060804121b0c050108070804170c12 69
    0x40400800000700188001c3c213030848100061040411680240007410389405a00f000411082c00800030380109500640d9201c0e04800c161048465000126140644241200e80000034250344d0b03800302d580d007159080c032030080c0801c038207100381c0035100c00c801042039440300080001480c3c9250501c4c0c0300790200050f04c0c2100048c2c0700d48201005400c042c02100811080c0000601410303604510f941100c07900e5000345100e00f800410f2440380c5039800c100d12310003550022003c00c5032080c450b07002d544070391007210240803030b11821b000091702190510500c0d100740f54490941e8042500c0314034020440c2044113046034150340302e079008218451a4828917006407034213002044c03c4100c51050200591008105645071071034900c040003180d400281050384540c2c80002400b00c146259420799000017041c01003840f55400088550070007159003280002e64800340c07034010385607a81c1c150849401000711401040300300da10b00d090051040c00b10180050001d40c000341c81c40302c00414155529500300c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 414668345 1250 414667095 414667159
    0x15030b1309050c0d0206090f01030f0203070215011e0905090313300c03020f01051e120c0306011e050d090804030b160c0f1a070906030b0402070201120b 67
    0x100300c040d0401100f0001c2c00000700e025100e56100505580019041d406424080f50103140301c50203004850b88658450b06540024410454aa09142000958074511000c1c1d00f0f03c0508a100045062901c040c142c41c0300d410900d1b8a007071f116060082c18006090b0140c8055940d100a00c80d0880341c04e81c8040c0c007005803540340540103a448000801540c81107004c100740d0240c5100c821404c02145501012000f540d8056442030743ca4400700c00101c42c42c0c454041036070210111158080e9800b00088014801d601c00710484448039140c01e034107070003188009d60b40c643c00328402e418500442c0b103151588085039031090810b14140080e94031034005442c0ca1080031945080000740910400118040c4a9004460007501800003410540c001c2c10206075640090040c100481c140d104100c50274481d03202c0850089158140307810850006007000003140540f0000c40d04045820003141090b201b0b5542141d0140d458180100300307001400d0091030800c0c00c550308520720034210b0083e1301650b40014000c01030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 414669595 1250 414668345 414668351
    0x3020418120f02010c03180803040f020603070c021801060206041104020415020f010c1e080c07021002060a0b030c0f040203220524010303080612010902100210060b030108030415030b13 81
    0x842c8002400c450024a4120600d0324010000d000850741e030680e0784500d944043c0345981da0b01c580c103141c0000c82031944000e6201078000100445140e000c40c601058520a503541440c005000300480b070084024000c09005901101c0010040342c0440c0050700c020301c018000619040c0c94851448586010b511b0050242c1d001402140a4a80c04d00c2010018459854820b9040c86250810300104001c0310000b01048940c5011860b8010b0740000c031501103a004185140e50141d41070f000c0c3d00e4980440e0f00c9a0b103140703040601901c03030901080c02d40304024010403402514044c9001c001c025080500000081703184070b00c074030310101d0310600728402590055008000117400000c0d010300903240110f01d80c1d00d080003000100000b07a0000815500200c0c216010001400c14440ca40d00400c28080060350002807417503c0c0b03501640102c1c10941d000e122002c244803840c1c503542c0e1888180b2080c8601039180d48100130411541c5940e50200a0320034143c5804101581c03007400080c41404201c000031002c40e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 414670845 1250 414669595 414669617
    0x1707060b04050a141f0b0a020102040801140402040e120406030903181d09030c0c0f2d030f0f0a111f08070e0f0a0303111e03040503061f0302041812 65
    0x20444d1035030703111400128101c04002c8005095041d031045101d80751008001080e4821918001c3d015034025006200c000c01c810a4105011030286c00b040c0c5050740107510309099926a80004900d030300461a5103800180740c01c4c5070100480003001541015000c015540e20051625100c0d030b26080d00401014003004038080203c440000000000340400d5083d610402aa02035500c01040501c1c0f03440c0100c9800c6001500d11001c40c4c054141d000072024200320b507206400d001c0f40e070303582c1841c090042602111f45584e5207481107030381c81540b00c00321803013944105010000680004840010188040c0c800113041c550b4030301c500b02903a40d100c070f1180401d40c1d030300801c601145e1001481e001e90100b2242071107030100721000701d00b80e40d4050002500304075003000c590414107810800c0801ca8502c09820030007401f030200410b40c90f50418000d81d03100b4041d10000c510f11081e4404503c00c000e101c981c601c04080d10319801c100081c14450039441600d403002e00e00c0b0010541c1c06120712201480381d00c50141d046 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 414672095 1250 414670845 414670871
    0x1e0c0a03030c181412011b02191106030901200a0201050703051909031b0f15020324031c0507020102210f09040e011107061401031707060b04050a 64
    0x2c148004010400000700030041c1c160800c541c090003144e41448091000b10480404580300c600380c1494402c00e03600340703c1c05078410743e42160041845000355007034540031070a41c0c2400c90000c46c0761078043c00c5850304584d00007041c68413100658000240c0000000d00c0c480c3e01c404400d042109041826010b8000b08420b5035482c2c080c0141540300809140070041da1400c4810003505032031521210410581d0740c0900802c0501416122020701074101c016441c01d03400b0320300140c18001140044501109101403040750b0055402968007a1300f881c20049030420000c5500543d04503952103855040c8188a20b00d100035001180e001c3c04010103588060f0b542a541c00003a240c00c803068404102002802068030700718850070143d1342044950410141d41c0c840220018014002c07a501189070381d4a041d0040c2445c089500003005101e22444007401041028100104282424070000d00100b0010001001c1c200c1c007940240310140c42644006802407000020038212081103c2415107583c1c0c0d204024468 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 414673345 1250 414672095 414672101
    0x30c17030c07031101090605010b0c210a120b06120a0b0a0b1c060509090105100608040302030d020c01091b05010e040209060712090305060412030501090e0706051e0c0a0303 76
    0x1100165a0a2840c24115401c8500b8030564502400300540d07004c1000d4499400c2d0007102c0f8260304010103001550311219100d03403a604c1902c0d0802c091240000c1d040004c41c0c804081643c5500c0403100906022604c1020346605c54202c0e8003e998581d144481c04456850f140685948615440c900000d454906800c8048650030b004c2c0780e104103040c0c01c0c200240d04018044800300d0502540c000e91441e10765014030003800c5a500903d50043c100c004000c000b080544c4268450440c0780310342141542e07914420741e65480c0544014006800800040c8241c40064000b4030506040900010305440c494840d441ca1031141c815824941111440800072903031f01c402100d4a2407001c41c0c0851400003241e001810521800c82c00900b1041e54000341000c190007142620300079600306043e1003151405150172042d501c12400300c20003180c40c000000c41d4a0310584640505885960000c1401038142641a905900b009031003507e228030108407440c20320100340c040c1008242503001842d15881c01e04d00503042d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 414674595 1250 414673345 414673373
    0x3030615070b010603110c07030602340f150f090605100e0a0c020a050a050102190c020627210c01030209090c0309030f1b1615050904060e04030c 64
    0x30300a818069080403801c805842c6045911500700043c1d520880d541c848030314083c241c12404203003d40c1400200303111844d002030440ca4092148000d809035107000c0c0d007403200710125200c0c0d05070450300001400542105034090a40e40514400c2110421155440c1c003500c05840c140e90440d40c940b1201c004000444c043da9400003000342c000d00c1c3c80380c20452050010900141200c6030581c8900c20841e52500070f10012080303e81000645100c1c01c41801c010313000c0c3d44244241420300307090341300b180000d0b4417074013018040541c000c01841c540b9081059000d0440e00d400c900140c10402c3c1c800f490300c3c40e07490382102c9030341203d440c1c503103244590b86c00c203c5410544060102c0b8107041c01008074111581c2c50303c00d081c3d032207600e1904054407a12540291440c50040b03180280d03a2000024409038445035a511607420041031170304856268028000c0740520700c0e52441118a90781d004401d6800050082c0041c0641e200c02a0001070f801d80d5078486022500400d44054000c40d404001000c10700802c075640401c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 414675845 1250 414674595 414674629
    0x40c02010c0c080711040528110a3006030506060402040503120f0f0706060806070e0108240315010501202a03060f061903170a05041502030306 63
    0x8a180300c41200940034010702d0000401c030703840004501040140d0f03c8a080d08052001e403040140b850011a40032504107506080b0303141c0b071040c00b00d5060340042800348002e20001044260304000b40d5402c00e840b64507000c10007507804100403100392941e8184540d15103410501140204200f80303581030040c00e007a00941024015801004103001c1c5403000034060500e2568a814140e50300030704c1c202c685a9010f092042c20341d4100014000e01884459000301040e24018010f45540e9210f6260650f2216203940d2100e01103017000000400d09140d0000c50f048000c1d4445009164820142c002030906100c04007505041303004c0e10050019582c0510346d0f020b40c80307200804600c448810000c169907605076880c101003440741c00c5034250f40b012203030041c180081005000c907506810302103110104e030f41041342c10314000c051603045c1e140c8006601080034205d07030700200351214180048174645955131107040c18a042c41000c010000d059020301d08040d10b03070390f042d502031078603410494104403044a6801d5014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 414677095 1250 414675845 414675851
    0x10020a05030718260f0a0b1806061f021507030b04050a0209090f09030403051516020d02062410030c0e0f1302070311030d0506102a0507080d020615040c0512090a020406080c040c0201 80
    0x161a984907070485d007000744074bc0c00c01c14007020404a16200c1b42503003030f1442c6411842802107043d01608600c801610444051005645079000c40d0120f0003105002c0b980180303400d010135001c14800804540040c2c07050709981c42d20742c0304c0c1c031054076080300e80f42400514519a000c101100010300b82e00154043c0c148040c0802c0300b40144001d51321207000d8141c091075502101c0080000c6514030303d03448032100c00340c020302125850700f0000d001400007803134120105982d84080c00c1241b0700403c59809506000340441d00511410440c0070007904100c40031401c0c801c1d40c0c2003500c0c20a10400280c80131807404d034400710b0300740b074000240b01041100740a40030a0080107600c220240c4c1800d510904041100980b03501c0122103400c5c0945000159404540103009240c0d59080c80d607400710b0100d03c0f0b0710f640504801c0c107a5065091000300d40707405d1410000102c1c2880006c1c000e100c00c0c1c0e0760744e400103101d00071900c42003401d0700000c1c21501c0c1640f02c604a80d10030a080300c5136060a020350040d00800380020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 414678345 1250 414677095 414677101
    0x80318090c03011503050a15031505070503060d0b091212040c08010c08010302090912180909070308071205040306060611011b1b0510020a05030718260f0a0b1806 71
    0x1110703180035201c08004c20b05450700005505081a60301c501c3c0020b0000365113143c0b0310799904000098044030216460401d0601000170a028000d07411640210005070001c0103900060300d5408601c54054100441c07806203032407840e030540d003d801501c01c2c03072820f050941c250704007032a2007110100b450340503907034990400381c0051030260043e080c2c4c1d0450f50152950010741d40c4540c801c604204401248002c0f0340b4010801e04891203000003500c0c4002003c1d10840c28a86032403130b442da50f9164a10000b400f0030810405800020b040b10035100b18909541449030038035480e69140750548140c0e07040100060f2010345a50f8090301c003400350024404509181c1d904511520100138a4110304080d40c03e6184220040101041410030040c056001d401d04110b4860b1312103600108541d200b40c48603800221140c4514441ca00d140304a51700b1203440402061078990302c00c94a000e80784600c52810f040f401003c0001041c14070034055800520301c12956440989441071061040b4600020f68244641c042410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 414679595 1250 414678345 414678359
    0x60a05010b0d230906010512030313060e070803160308070c02030714010e030f01140f1509040c080102030a0b091005210106261218010309030504080318090c0301 71
    0x45569101141e030002c521280444400240c038901c50440f410900000d000b003000414004ca1113a0503150115400344402201b4501c1c4d0359240010307034000070440a139003030540005400d5030103c1d04004034803003516900c0d40c0c1d400301f00382942c00a1200c00034408000d101c2c0e0040551103600c44d6801141070420f060040c0b0140c01181c4d41b50318a0081488640000c1da9080550703024814491031080c0c020202c1e5204000401254041c2c03410021007980000450b01042c401055426010b02c6002851021030406c210b400400c0b035411009030098546d541d1001d800311310500280001d5110380c1b06044013049015604080c050f02040003403240c0d0300042e200000b4040b664803554036028030480e58410f07855059000d0a40c2e070050038a544080c06100281a010a100a4181c0003440c82491041580c0d07048264004030703000c40c41581c0400164000180341036203030303601035030050700090300030724111742810b40754007519203154040d80040092a003145070844051900e2000e42c0e0b0301485230110603003036503d400c3e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 414680845 1250 414679595 414679597
    0x90a240e04180201180b040803040806070c02030a030c030e040603030e0f040b0f0112140f090d0914101403130c0b0403080423031b0126131401020f0903060a05010b 72
    0xb8024104501500810a440555031250001c1c1c1401901c2c250386a981d05481d581d00e40c0a07209400b5039008038800211380c24020003030f8043e0790790040d01800c04041d080d0f07001c54805945040c11014407064130741080103515144641c0000d0740c443d48400403010303200c02c20070801c50f0007103080324070460605034001015269005600e000307901c203080c104c00400c804c0c1d03402c3c0064010200c1c045a076605100810100c4081d9031140c0d406028640c09540008149640c11100744507503004444003c40c890060900e03500f8100a401481503c034605005071058900f11203e40d039009940100d080e900200b090403d203c00248800001c00301d213034030103152031714541d20140240142d2180c2010724103c0300c60442000c090984580c403158006041c2d51200b928062980760010310038140030b00045c0e40c1b00240d800582d6220001c1c014042d0001c130b52038180e8074892a1a141341d6445001c603000005480c240c0060003003400a000c1d0f210341e44403c140c075100620203151a04070024039080d401ca0911004110060301a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 414682095 1250 414680845 414680891
    0x1140601050d0b0d020d08090a0e011a0307031805070501020f15010e0403110d050403150c1d0303160506010611060c030115090510090305010f09030e0402090a240e04 73
    0x180b40815642d10301000500d0b03c10030a50040d40108020041d1400c01c000302000305038000c821100c03000c1d02070700c495100c144080c00340680880229410b00c1c0b1100005a000074582c0400145000b044204024641c40404002035404459a40c000c0d8000d000311340c1c040c050b03500c0d05044071004094600c40602203460410041c85500000344048000c2400e06110368800012103000d081114040001e334000101150701510058507640310135000004001c0503406402c1120360346950740142d0140e4400c00412010050010580c9444100300aa0150104403449443c103400361018180640c50719101400720104001005456003209007084509480c41060364103492070081c204101d0304034407209485110311174108a40c444009030a00c09966484204075055038880d0f402403000c0c14018181c4019903407119801008500e140b100c0d1030050900354064121004000d18a460250361040010030155070505a110b900300f012050000183c0c001ca424044043d040e1000c000d910441d036914201c1e18503907 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 414683345 1250 414682095 414682117
    0x11040213150e12031c0b030d0305060429090a020a02071e1a0307030b010201110d05060a15050c0606010c11010c320709050c03040f0c030b070e030114060105 69
    0x7245000400c0c81044042c54a60018280304898840c1d07031a92540d0760008011011940da00040380188078060b4000c940d24120050010000c0d9074040d0029005030200404081c0c006a40b0b0b031150060691300700003607844038911401d019200d40b28409101240d100109124030f00c5004004040d02103a0000d4402c089841c1511a44400c0c0300d254201003a035100340c0d000407020420050b160b01e8003241d290041d8005c207880d4904004541c1c840005a084c1e52984640c0e468210091000c4404000140c008590080004100d0009140c44202c4011000d40c1c0000000001d1404a00f45038044410800250098400d003400013080310176903512a100e6000703070911070422108800110402841089204c10034000700740b8a0950f4407084041044081051a4210507100b510b0000444407503a11541340581000303a185450350743c880c2c80300c69401c01e00800484000458000000100780140151030144980e075441a000c000c003401007509407012100340c1000d44e2205818083c003031f030700301d01111110360390b07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 414684595 1250 414683345 414683369
    0x1060c06020918061207060f03020a17040f15141501020a0c060203130f0e0a020f0d2d0506030d08060114040312180305211605060411040213 62
    0x52808502074080e0040054024112074000d49400c60002c034010721645040c1d83d85c3e0000100b4041540d41c54425210b4400070030900c25814185500c02d8004240700d801c01e06059545551201c010300c0d0b0204102c80580e45015859428000c0008503104180c19400d440810b03c544500782d903540380801c8000c0c1a402034600d64941d41100b42e40280040000203400c1150b1310001c0e070b520038020b5101e0740081c1402c0c0000701c032860041014a401c8824000b5910020320700496540c0c3c0da10303d24000e40c042000c5107461081481103039001300c030074000c040c1072020425801207a44407000c4409009600d400c07589030018104005c020389503c00062500341c0c540c0d18030341380c24207849030700040c1c42207464100f40000c2c0307040011300807080c003003800502d034441085541d8041c030000901345521034203040307800000c0a6800181421064040c0ca81601c0d0b204840f0f03002d06460701e01c0f849001041c01d00c83e003100300c400e5080a820030081c0a2040d0340b00402000075141989050a4880c0c03012043c0a58000c005440700713 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 414685845 1250 414684595 414684617
    0xb0a08220b0a0e060a021204080a02010204032120030909190c08060901050927011506022505010909050901060803070c1509060504090203091011210f0106 68
    0x10361410401102a0400989016420039841d10740c05803e2100d0f40007410304c41c0303030040f802d0078480f03208031150200b081d2040e03405d0b511746595120182e40020702e54000c664080c0000f201040f611010905940307d03440101540052221000d400200c0c0c00c100d00c0c07074100099a1409200340701004032240300344103c504203455070b20035086002000400c1203110350989404466252550000310640c060744007102c4da40b640d40c4c2e80714100014450101c1d0110340f840c1002c02141c081000015a00060305100c600125103c10354140d0001084000c3e8443e2006900940012208142e00c0d281c20010221107001da920340c50402001a012000d00e100d40c820543d601c4002801c1c3c42e0080d0f0040c0050809a006c0d41d40e600c0c824144056a020385024203103940c008180713038691050081d08901c2c03c540043d03c6080c102072405203041c000b50401400036015005140386541c0172084c61003400350602030407011580766140980704090384112100a001c1c040c2c261804e01080c060141d1000d81111072078908044241 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 414687095 1250 414685845 414685891
    0x10c1425050415270204081e030703050901050a05070b15090a0e060c0c0a05060a050402090a14040f1103060c0315030102040503101806020705011a0306100303030c0c170406090b0a08 80
    0x50304240ea009480c80403030041441c02d40400d100120380003041603400aa041c8c010b40d20784901c59000024082141008404029401a40505035205103400c20302d0030b003a02900c13000f001040c12100380b030940000340c00c4480c0f18034025500c070340c1048404404120400300805030603030350700c409082c080b084000403585800201013005100a016400f03030545d00c4a00740380e841e01028100035541240b00300c0b0b0070000582d2090b0715201d071164148003014a140c5984540c1ca82075407a8199001c29181046030440a6019413400c11034180107440d0746018980c1c0c2c0c074104210700102541c0030710840c440d90040004100030355000688500348101c1c8040003501c000d0140d401e500b9035130400b80c0140680e00208110301401410b51100c1e5203090f22004103848040e2a0080603200c9000700c800390102182da0794284007091080d80204060426030811907012000750f01e036401c140b61032900c124144c100001d0700b0b100071503110b0507000080010b00c80486c248407607454040c0c03050200401c0c4840c00140070101500c15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 414688345 1250 414687095 414687149
    0x1d0303071d0d0611191d04090215071109060a121b1a0903060114090406050c0c0102070804050312070302070308160609060e070f0f05010c1425050415 66
    0x5180d2210040200c4c00010340c211440b50040ea000303469240154440c109074600035100c0780c03410040050700c000003501400410000703111003401641c2066080161450743d20240c0000c0c2815402254405040c1da50b03a0700300030104000518146c09051044000c0080001c410609804076602184c10121040703541070301a40c240f6203901610aa4643c500c180700e41500950091040c0081602a00c40d640e03241c080a4100e806144503051700304109070009004103003660301642e00000c00c811382d076191400074202c0600b6a08075880039142d19070006810419450200040d1418400d4407a151342003402a0b1006521003207544409001a8000a251907416800100b01040503500000401100102c0e0618a00803c820084502c0302d00c201400442c488005814080c11200180810701400b0300706001100d200d2400041100d0000781d1060b40b40030913005010f040c17055000040c3c04c4080c0c8841c14290601c030011a4443c60099140c500e034426010b50786070b640d07003c1d00c1e90400300c1c41945c1310102c0c034607a807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 414689595 1250 414688345 414688369
    0x4020405030309014d0105310b01090605091608040f1403030a090506060901050a05100905041404120507050a02040c0e1002010c1103040e04060510090204091d0303071d 74
    0x1092200c00044403290300005800440707400081720b0f8442c02d01800f040d5400ca6505803400d142c2d210a4854444e00034440f45280540e026445003200c04844450380c41d00f114450a811210080b41c60b0700b0288440e08016502540c040b1342115280070803400603002406411014001074490300d00c0116107014081a81080340c00904600101d9649180810004004002204081783c06006403800b003469450b00c40c0d82641a240000d1401020364900702c1085815110b900100c800d20840c1440020700e030b40d440c460502494800800b518143c605841c28540000c9080003640502c8001d0003401e000c900d00240304400c0c00d5040d580017070352040c840800e80d5803440010540342d104418205a0000a074190040e05621441d5154a100c3c09001223403141c4034000e5002c0d8610f40d80340b002c0041e01103441900400d07003050402c42215100354562822506980c46900100d8165458105100042d585484101d106000c08006503045041010000f0304015203002e002400c051410843c11035035440408042d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 414690845 1250 414689595 414689657
    0x9140f1212070605010603090308010902180a080102190c0b0115031b091517041b0b07080a140c0307020f04020d0c0206041505040305271008060f0402040503030901 72
    0xc032440c040d400226042d03001d1001140c0150425000082903030086c09161210b82c2d058551907500d83c20140305030020b40000f03010034660810084442d403251038031301206001d400340c48009070b9038503440300058000d100021444010000c0e0043c0000204042600e518192419010185043300708010104e0207491401140e100404403038400300f807460741118408085035803c1091405250440c1c405407141032030340d40e02082c0c408017000082d001032900c020503004134022001d00142592104c4003100c403034001e1541141c3c0060001582010150003403030740b04e00c0351005c0c00901d20f440c5070f40ea00c4075280e0240c080000c3c0501315992000c40507a80360303015611190190f5800f001001c494650095480506460664100d55001081c222808203800741512030f9801d6241c0d00c1c6811003030812601c0c0c0c00003000000040510845c030340e003d103584040c803200d105511581c0f40d1803507045c80410400310072181800c10b88598410002008a903c011041d10b20381c41d000d003480000941244c000b0824428103c403810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 414692095 1250 414690845 414690853
    0x9060f09010c1a1008010c1d191701050906060114030406111305011b03090e22030e0916120207080c03040807210b130206190807030c09140f12 63
    0x181d600f2007180348203124201d601c81441c00941e540e6100742c22264070201d2503001076824620300088040c004490307071038800e018046480360400001020315140f80e0b80c004112444000012409401b001d009164000b0880b0001e0711082c203080002802c0b03200c25060411100c01c01200017070900c50103511402540c001d404046039241300f030700d141e04065030b202d0181d140450200e440e0000e01042441c003008115505440361018507040034a0341c200150300400003100718400b086803d10314115100340c1e4003200d10035100c0c280368200d500104406520020211100300e0002d44141d075100327a10a04907607440b804054010f0340d41469092280c40c43c464844400b40500c40040c3c001042080040c90500300d03440f601c00010103140301a04c100711044450400740c1302b50600e002052100d0700c001140030b0420310081c030480c50034202c0b05030142542c024031040750101e2840001c220140303400d80039140b0410b800f4640700413000d0a0241c200c0e6400410f01c0c0140c0a4580205445130544802c2c0500b03942e10b454004031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 414693345 1250 414692095 414692123
    0x10c0e040c0e120c1009120b2e030c15021f0204050d050c091b09090c0919030b07050c1222030822120b270a021509060f09010c 56
    0x26aaa96800002c00c2d4001c0072508000412140701b07121038815500410f11440d01c00c0342ca034580c06c3d07a05402905c1e001c0c4003481d910080404410f80b4000480b040807507030558654500d1030502001c041010380c0101030030149401c880e5110380d400300b600400b081c0407175021000100c5c50a4200b00071b001e113400c11500882080d1105003400800a040c250182c1c00b00c0700f1a440356128040d4500d1107481c0242c80c1c400b031800707025201051400c048000e501c8030207005810704102184000a40f100d031040c032416490340d01030038203206015a00e48440d90018842c1021840d205100340c07455551001580c90340300212380030407600c0b54494800c1d0302d10401141e4401901840c1d46a00713180000d030b81b154010400303030320140c450304001084000c501812240710000c01c4a18000d203488000d02c0100c01810b901401021420352a98030301d104a0b410320103400d05000b081d0300502441840503d01d210745208000b0902801400302d41c4d0b9440045414841c0b0f0584803989800c2c0e4440141c4401c103003408002c1c44400b4010f55 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 414694595 1250 414693345 414693379
    0x1091d04051c1701080a350d02030403020d14161a010b0c010e0a150515040e07030614091914030f031e040c0b0c07050310021209010c0e040c0e 63
    0x50a4150080b8201002203030740c0c0e803d0400da48003c0490014007034140c0c050b0f015007e85007075101c0400d029004030311040e4814020f408a44a03070003282403c2c0c00031760200901080c15810000c0801800450400300703261055404410030a024460b1044140c101d1864030004201d4010140049040003501600742541c40d24209075140d04092601f8450f0761070881e2441e1380c50b6000a4192205402101c95407400060f025802d01500e4020415962000c900d0318240d203c5d1214451542505d04400107800d4440c1145040c409a45140a03088400e41010051012810000c82c48021512070200a0909841a440c1080c42e44546d6180c82e4038901020400c580f1031071215008500c101180c4c00d40e010352011a2003007a25640081e24050b100280b0700c5024042001c10100403d0f810724507004682c0700035138680010345000004400641d1880d00030070035000703001503032000341d4010134200e000f400303680c0000390020b00b003007a00d508003403140d61076070604194180603502c0c00703802403000b0b0a50401080c0540e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 414695845 1250 414694595 414694607
    0x20c1203091902090403080702030c070303050310050a03150203220b0601110a0b060411090901030f0b06120a0206030601052203020109091a190b0d0603050c01091d04051c 75
    0x38440c0c2903000b1150345840c0c401054108040081d4000d0814515854540701203419540050450080d440104103580500104125000040d8426540c0655a180c680b0000100818a40c04607008400c200e1045c800240704209230300c23200c0044000140c5a035034850b20a403050702031000d41441000c11204000038443c500608521401e4280c80d40203d13401500c0d1840c0c0c1d240c1c00048081d010f900c8200124090f8030f000d4108110401005112070b08042d0b0302c00000e07032811720aa00898440710880f42c59420420300135019980103004544825034004007112068580d48201002440750f40c0000004001d0303809a000d44404c0d010850b80c2203000c1c42403203044d00d075044003400203a0104101d0400025514030500540c000b0a4104000581501c2c03018288401a0b8400400c4101c00440c041c010400e0300c202d9010702100040f1071008903880c3c0c51410004d00349102601910b0400807051014422030001161400703961a1140f45501640d43e1800c2c4542007225151000b0203014180f104506841d50041c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 414697095 1250 414695845 414695851
    0x80c240a050708091e07090c08240d060c03060f120b060f010c1e0b190b0f0f0f040e1e01050f0105030c06030c040b0a0c061a1c0303020c1203 62
    0x30030011502c90341010ba4070301c542100e4072130141d03020340b0800700c0c20301a1500c0301a00c0b9a103002200e0b42540c8603040e100070382c0c4104200c20001070541c8100428445d00c02c039030300c0f0303401003032aaa0440d5414840220343e16507038098010304810341744c04255119a20a41c000c800030101a60400e552a8540600641c0e0140c5818180c2e46a06e464020442c00c6c0741c408829030b071820058550480c111007540c0c80310207080d03c0001a40314410b2202000c3c01148140c552144a80086140c0c1c14051b841a40c03800211280e000c40315001d0541c18841d9255a01d50004580e61010203c030207407400f51803040010302500380701641890b18000c1c01055041c04084800740042100580000d000725980d4401840c8820b009200b0940e040e4000c071076001490a0070341c001d540000041c3d04003890a6110881c0e00650781c006920b842c00110b0740c400144c1170125a1081118051a079602c0000980404000569410b19a464800d01d4a02c2c502c0202c1090301070382c122034100000c401524001c5201241c01c2c281d5030000c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 414698345 1250 414697095 414697111
    0x270b160204290915041a0a06030c020d02010203040305160f051203100b13030f03051b0a03030f0203060a0618030209010f0f06110604080a0311030907170712080c24 72
    0x1070a0641628060000354400d00b00d551440704e420100b64100805070640081e0100c0c1100000072203840340d103c0e00200d10282010341c030041895030072407600030b24081074180500d0031a4818028080040e5100044611030100c0400c80f0b0b2800c44541000b000050303204c0c0c401030080c41050b01303006881310030a016510991620360400c43c11542c895800460340302d42c5150346d5074801600000d01c00504040300c0e01100c0d900030314059041c00c120350540140c01e4208501c0101c3c1f41c0c4000c0701c40d010183d050141006c00b1140070010350840c00c1142c080f0304003030000e00901e0309000c4003400d030807110107500c0ca00b10000d54004205440c2c03541c1d00d00c48040407a203203014411810404001c0412554041d10301d4900702100c0c00010301a036903c40c0c807040a180c0201603030508068032038914441402c850f5001e54080c903004805003217424070f0304a059004503040881c041c2c403038008800070008020006200013096410440c69940da0080c1c69a82d030400480c81604640c41c105041482e0200c04850354561007070403c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 414699595 1250 414698345 414698411
    0x1009030f140625020c03070b0f09030f0c031014070f030f060e0a0e030f04061407060608010f15050f0915090c07030201050702012c0a0b1303270b160204 67
    0x80100105d840c0c100f0708241540503840480208003d1079050018042ca5040400842c1080f2082d0700190800c6000007440030b060780710840c0c1003103518003800074034050b9540c040c0400c5034451941c0d904c0000d0704010002d4003408241c6014074206402900003204049640608020041d194560030009060542e5000a081e150034124580404000100d600c4030215800c0310b4140791514900b10342c0008080040b0311500b07024000080058803030300514014194140010030502c25040712003084032030808200c1c803140c02040040003582ca80350000b08510406559004840d07032800c04c5d040c80d69481450b100d8010070f0490811060400303a40280900c9446a40280615103030b0b01c03000c07404d0b640004011016010300814008107991344a20340d002044942051b034243d640c003501c0d8264501d100301d038074002c0d03191405500410140d0051004076400c41c3c7c205082000300c81c0110f013516424803070190700c801d580f0010340d103d003e5610b4039019000b982d00400c1401104103880f917000000d03112104108008003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 414700845 1250 414699595 414699661
    0xe07030b0906010605040b0f0415120b030d09090f0e060907030219080601050105070302011407090f09110f131e1d0912090d020607120e1009030f1406 66
    0x180402c40750f0482d4070f0f6503107160410781064810090365101042d0011868020800017420702c82030503d4203200781141c0c403620001050784500c5810ba0302d0303515215119810184414070f140c5c0c0c0042c02c81c030070703646c03c00720004010030304000010041c5010b01000100e4400d040802082440014000064a1094420300c2c408110040b0f000341b102d0503406440619080380005000e194490f5016000c5180284004034107040f04100d00c01a4500070340b038110000702040c0f0280002007075004000d00400d0484004c20403803045170303a0107e150040c145000c4c1005400035240119483c200400710140100320080c08a000c400d00030f0304400c030300510800103203940c1214010708030345c2802811031242c140300024001e0703031800360704284c6143e00201b040c1340e10916083c007410160700c80350080c044482c4141009078240c98203a41c0946100e802c603545502c181321a070340201c1e0050b0700452040c2141d5102e107010590030224940306004080c0314449a000380300701000c025001c2c0032020310860700c82c1d40388102403040c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 414702095 1250 414700845 414700861
    0x6080c0a0303020c0d150e070f0b160f05010b10030e0d090b12070908010609140a0501120b06011704050105070906020d020d050309010f061829130905010e07030b 71
    0x603900c03000c0c000d81c00c640040d490b0f9081c40c00e40882858410360200425a0220301c4500c201d88145000c0d100d60341c0100d00500c02a044d4150303c2000e000001c890900340030302484c1c907110b01010290018030b40c5801c60089800c000e000d42061181ca40020815108240d4401000b070040400d039119068500c2010004100c15000708602c01c15514a17000c3c0904d4814a414140420100541054100801d412000030343c814203214640260021100c0840d5070105591b195002100c007030f00d9610005d281c8801000310440c4020080c0015a0003840e00342c1d19501e440050b030389182c502c8052000120340340d0070070040002c1907201c1c51161503d51245000c42d611480120794a00b4000c5103440542e0000b0041052a401580030f0f60340181c0d0040089920050340340d4400c16160140d01000700c00b41c8110100250b000140115a03407901c01003c15007103200303600c042510ba8110705103494003814007203440320014840354210031811508280240b100c4d8110340f541580ea81d04520013a81c54000f0107010070100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 414703345 1250 414702095 414702109
    0x3031917060402090a0303211a03011a0f150d050c0301030b0a05150d021909090b0106020a150c0215160f0e100e0a0f270209090a02030612030d06080c 66
    0x2080c018002400181c00c0d80e4003900c0f000503e410034a4080300840e0b408d219440140507a2900300c1c1382d410010190b070320410500d801c1d41e44400301c444900c441b49045c0c00031038490920000e10580e0464900005064841016900d40315011080c480942030800300015a4941801141207a00c45c0f00700d41229550120034208440003607681001e40703083c05c480084a440e026800044003070004212030a48000b00c5041100051a0344c00010300f541c0300c40c028000c1c07119100595004100f80c0c00a048511b209a4035140415101c0a05440d007998403405000d1043c13007000907840c02034000b11030781030a007000c00f0b007009460200030924000034941d1059142d000e200d8403403010b05882c05040c1c001c1c02d030300714401511441000c0c0e4125801c02e150380b4002600d58030050103d00200219814192480003200c2c0d114014091402e034942103600411041a80341c4401010a520030f0050300010303100d4891100064501214080110641c400071986d030880c44140c2c0d11050880f401502110500b06100c4240502 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 414704595 1250 414703345 414703357
    0x4030c12111807050c01180b07030b1005191106100305070906030b011a160b090c060903061504020f0a0201020d0f0b10050a0201140f090708010e03041403031917060402 74
    0x141c1d200300340032a01003070080000d17008050070070700045581025610400a40c40f40b00400b0395048035081c2c14410080c0d014070641c0050101503810040d440036896018145214800310300100c110b0070700403000c000784640020303801c0a43e5407050310400e06113800c201c68100090301040e240c60242860000740d810b9a071140d102105e6001c40129050b0780b070940e81c0e20702030040c1001c00740d410100702f0040c1c42190307a8060711000e141c8650006d003e9410214000d5141204080415000303210400c50718610303503800940994822400d081c1910001c50b24000f080107401000310b030101005002c20b0314075100d030b0190060071004194080400c0b801c442c2029071001d8a501050703864011088aa09842c000d2046009020b5601c644c0004112040c546031040d400ca0b6045a02028001400f07090000d03c40090154800800441d4000d02200c110420155101e0ac01c0344940e50080c0c221844c1d003240c54070306000b55003000825514184801112000281c005100d2810024400d00140700040035440c00b40f080d905 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 414705845 1250 414704595 414704629
    0xb04110d0e0f0d030e190b010f0f0b0708030711060c0d151203050a0c0b04060b09070201050c09120712050c09180703021003021308070503010e060405120f04030c1211 73
    0x74203120508015401020b8200c01070b17101d40503007019090508050918162140e208501c02c2d80150300d00b02100c0101e000d550419500b24000e8503040204150603000e40301d115802c426102d42d03d0315190410f0b80d80c04201102500280110030810848071311745400b425040c5101c00d002d104081d030600003440f03000f0381e5005201d80c840d0311504510100c4d12550141515241609184c44e24800c141c90b0204030b41c40403501120b0207a02c41703810040314200014081d801201c140024130060424445100d2203009030040f05e0b0045400311342000d801141040104002c2007010f008101d0311807141003a07900e030643c404010303004450701c601160040c081180104405403242c8068804241540c2c20404040101800401019000c1c001c026510841c1b04241e001014101e000340707042340c902000d25094490f03030030000e406d50700100d08220201d2004604201d42c524900c0b41555074030602508a0403e000e640c0025202110006000c83c029143c16510301c0324074050f01d43c20319203034105420000d510100480c100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 414707095 1250 414705845 414705853
    0xd05010509010f150e18070312030c180e0c040b030a0905070519060305070309050f100b0f0a0302090408070804030f0b0606040303020d1416030e09060f0a060c02040b04110d0e0f 78
    0x41d400c2e8450301b60841e2200701030100050000461a1420030980c00c20750310365900c04210007105406104025044010341070044880e0302d402c100481a141912405a401100038001030402800a045401030205101425140e080c1100c1400082181e80d034112242e101e8002e01081300c0c902030ba040ca00400c90044407a5409040c2030084000e0b01c0040d01e60300a068440007148005071050100f0f181c48160400100a40320340c807003d403026950104c04840c002c001401010030b1544520100e2403d582d01070303a40c0386040d2078074500368a161144000c041d154103400308010003040790480c2c100c480c1c3d50003202101000d071900c4c020080744d032055210050142e800a00d0224182d4040c804108034802c40e02802410b10b10358140c0d0f255890080b18080f40001c12158182d42c013032614250841c1c1000064803c0520551010007040c0c1d50403d9000b040103000640d0442d40c110340c0c86030000408404040d02c180040c01c402032000c015504003219544a041c02c0140181c0d025000003450b1524070b0300c0a0040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 414708345 1250 414707095 414707099
    0x30a11090907050d1b0c1208091e0307140d0305010801021c09022103120114010804020915130b010f08220201120c05090a14030706031a0d05010509010f15 68
    0xaa420f07911080c0e002d030b007075501d034403428417072142a040360344581e44551202070f5090b506150441c0600319110702030060084200602804080006964846140d0f546a0b40004194660258910b00609600806980c8000701444440c0c23000704058000015030b1300c060200b40d0700d6014903402d0f4001c08112060140c040810307a4000c0507260843c2103d180003030220100300440055003d400b140410000c1c64690000074004803640c4116045c03030050a900100c800803540040000305884000780000e845400014086407011034020704e000010709006205080507030900c1c400b44090900003966038041840c4101626107540070f40030403071250b010a2030124080c81007c4004102c00115001a030401040c4800d0030981a0a849400c10000480d10b416440706200070400c517004072640c00c01d40010401c0c005101e01e64400041080a0b41c200b81004603918800300821842d044c4916025944441d0031481c0c801408010b43c03181e4024648007009100e990f500d0503005047c2c5803000151801c0300240002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 414709595 1250 414708345 414708347
    0x5060904111902010209010906020705090c13120506061c12050f0706060801050114060a120c0507120f030e0a0c03020904020a03020a0b0a230d0c03060911030a11090907 74
    0x5240d40c1010101c072181840e401d06600325441030022124809070394000359107942c940c0c0010352000109000c0c0f0042c04154201004902c20400c0900032480e0920040b80321402e03003100d02c10420141004108100454040d428610750780c0d142075410900400301c0200034008d10114620040ca415004104603166064030b031000c0325168800450b660070703c0420720000e00090014010400100200d8001060b03550400c214452020714040280d44200010000e8080e8940c211000911510342c0680024054076a6103007500c0d0740c8100c2c2d038003c041788071080d107020f103003904074074002c80c1d0341c4a541e420804001e00704011a9100580320010b0034a0001400c100010710340310030b0f66a030151014013070f00e921666a50220700c40e51441c0e003001c171910030f0200d5a03124440e80b150302040b4a0143c0c84001c0d0400801d000b51192038030a103100101c21a0304c2c0c0844c64030640c041d40107503004111250701080007680550103160343d03070001c1d10941902820040701c14050070610060390800c940c0280045003640320950 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 414710845 1250 414709595 414709601
    0x151416050111071a0109090b01140303070b0a2016060915020a0807081608010b0306120316020f03060c0a1d0301140403120e0d050a02030418090b1005060904 69
    0x14003129159202c0030308040790b503000d0b405019007034490081c1d1804030079030001104502c40c051300613644140c81c0c0701d0103c01080c26240b117981119a18106d280e414a0b01303001080c118030620601520000d0002c06101d50890164456074600a40d0340780a600e4120000a0880c180325018020345111502c60781040405d0366688034900700c1e4400c241e80210114407001800c00d981010640e02e000c1100c0c58208290950000401da910511074642c881100c0048100900790020600070317040000d07000b1000600c0c548440c01c18440004c4081f048030348600d0a00e00848003910560001ca0240e071103100b154280d0700b4002645405802002d0007075041000c601022580c08900c180c1860034102c000c20100c1c500c0e00c2c00e1140f0b6040da5840c604404042c070700360802501c42c00c800c200400324903103040c0f1a141403034004280c600040b0b10070b25020b65a042c641400300c1c5140196000046109042c03a5800b0300d0304d0132a4404460240b003400010103955640f4180b04148046202e5150801c404008070342d21450194 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 414712095 1250 414710845 414710887
    0x100c050d0f1e1e0504031509020a090f020d062c01030b0a0c02100203040f03030b030a020a090e03040509100906080303010e01050d081909090b040e03070210030e0f01061514 76
    0x200d008081e80070f0382940e0800b10151000700740c003c104001002d009020b00304061050420080d0f00520440442d5030206030301d40034500c141200540c0d115010700c031103111601100e207502ca80da54140040c544490120990381c0179151044202200c005520740c41c03e0b00d00400d20704898100e4a91451030361618016405080018142c9046000b00614500041050707c003560180740038220700250603020780780250480d00e032031100500c6a8440388440300140d03200030680c0103440c0c0000001c10864101800a403031030003503802590f8000e40c2d1030100b00300b5030000d0405c14100c0e05008818000c055540c01c006460388030a0046503140c988002c011700003820580c0d00d03040c0651044070050b1a055002c10040107130140101613400080c500368042110640c0c5d4014a6499402228104201000000075035070342c2c030804070001d00070303181c03505020f184078020741c000008001c3e040140c916111020303800c5030081200d0f01415425420a040400c115403054803094818019448164a840e241410b02c16240e103080d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 414713345 1250 414712095 414712097
    0x40b1518191404111206012a03051e091503061302030a090218010612050903070b0705120709030305090d14010e0d03140708160e100c050d0f1e 63
    0x559400741000c40d140110014112001c00c0c0311440d918404210548851105011100a0920402950300384085041c0d41010b002d003007150030708074910209009a0700c1071204242041c40c2803d5441815008401050039100e50a43c0c40c1440c07401d907001e141d150007107504c401c2c0c002c0d08905181401e45000b030001c0d07801080c01041c08072074013843e688510a0340d008403464140790b40c50f80c085e04114181580c0d240040000b05101c00c03c590304000d4001d2075841c0030051020b00546803c0854051003040c011a034145800a056008a24003040301401300d1f40705111240c0c100301c0c1600020480c910440200c0207403035150b9101882c00d071078842000000b0303c8400e0152443c3d1460340f11810001001d200b1105105a20000713009644c95144028007166480c1c04406a81c0e0615002c015006900080c440d07803040d01c0c1c04103107101c02154038044444030307410000650031940221000b020b05030000700000c48140b062040302c00310505000101e4250301500084008103030142c50f4000032a15004042e1241481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 414714595 1250 414713345 414713359
    0x1f060c051501090c12410f0105090c07050d0806131505010f030516110f1614030307020d02270f04030201140408040302241206040b1518 60
    0x204100e07440c59404281c1c008070000365118200144203410450300c0c40703001a80102001000c04106141241d008102800c0d2014810510112907070303c840c1c0d46200d0810711600d1482a03d00d06850407800350102030160501c9458181c0006008082280856030034551042c06407860709113205056440e050054038540d4010b0500400100f0001c00e841040c100c004103140000c04075150800140240f801510701000b058140000c1240310040203040964070040d621340544c00c030b5030350f00d03c04c0d050624023141007015020390306545a80440d0384000c0000d039840041c0b5031448803004410155a4843c4007802500410702030008800341c82d000742c0b050407456604010406600b140c485010030100c04440c642e18440f0000140710074103909108102d54900a0941185030781029112003100c0c1c016440003c2c420000840c0380e50820440303002c1c0201c0d0304614024036485064030b410285a800040b6050782c011898811488460304d40f548040d0010710724180f807503181c55400c00740b40018103400507100350005d407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 414715845 1250 414714595 414714613
    0xa0b0f0c0f0414010e1e01030e0d0813031103030a020304060b010305011508040c091404060b0d0b0c07110604180f0b010507080d1d060702070608160f2d081f060c05 72
    0x103038220640b6541c0d81500b5006c0d40d620940001508480300c1c2d8640700c0056014400104155400c080700c56042180c54080f03510a0038245030807507040200202006003400007000f0312242c07462070340107580a80d103d0740c0240200e007075040044003101e601b4864007144010019203440c00380c0c0100b200755000307405061040451502c0d800d280c015030700c0075044104440c000c03004000c1840b00c0340c07040d98802c3d142200d69002d100c403141c441405800010b0420820040300044460400401d002106d0b4410005019181c1f503076035402e514880400800d8041c980141480284003035100540f00399140d10005846070381c10401961144107140e0880c812a9490a03501c00510290007a0110f00500400154001301400d02d409040207081141603400041406410310500c18008491541d603403800309a40340c944100d02410204032550b0740c032142d482d0035905c591000361114022034507040005e0000c949030031900d0380b6080703e8848501218006540c40c001d10000500c03a00d48a44c0f1080800e0b0f008104640c0104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 414717095 1250 414715845 414715849
    0x912010b06131e15180e01030317090f06010b090609060d090521090609030a0f03050417060c04090504020d06020d02030f060907090608060607050a0b0f0c0f0414010e 73
    0x3034004a007059088450040400590b0064120b0001c44001e4400f8801201e2402244c81c1428242d4452134040c00715480200d0020110480008028141c4205c00c1c0720340d5940741006882080c2c0710611441144807040002c5010ba800200f05203007048110007070050341e20301041c039901900111b090580c40501000210307ea1750320440a4401c00034011070001e00c00742c4078a001c81c46c14040f02ca5940d08a071138040110a0500420140d130400301065071226580d004200c0003a0400b6642c043c001c01402074055208103142e4081c0181040c6d5030201d4034058032050a8882c8c41c0d030307001e0440d5030704080c8030304000c05d0054a0054000941240c4003900e80103500d4226a100c400340d030048000d0040680c0c1c080b04008e41c1c1c01e008002503800040a036180d14160030202001000f1007840c0c010902804110300102d00c8603150507044820940d008001d07200504e0280c9081041c610b001d4440b050540c0342007000c00c4c109030200c0f003280c00e9101d00070340c0c491825242c502c5425000360030718080750522203402e0140d0309903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 414718345 1250 414717095 414717097
    0xc1110110f0c0307060c050604020904060b04020d0b0f03010b130e150405160e071704051f0506030c0102030301180e03131706070e0d0b040f0c0806010602210912010b06 74
    0x11014401c098480100c64100f45071900a00d9130240080052105600010601c04980c43d0341090701510045040d80e120300740a0050103003819141e80040c80010641d010100c1e65001050880b4101c3d00138004d000108201401d03107880c401a0b542c004c40d070082c0e0140e00d4500703034090340b010080282610054040080035059110088805072800e0300440c1960b214000003080c2c07440a4a001c0c8103100032401c000d04010310000c005040c260454205401060074400208100c40040d4051410f101080007090352540281905442c058080e00c20a041e0508540c00403084d0b80c16030714070304811f442c1c0709a40e80542000e054410b0702c01c40a03010030403051445400110603e4050070850044c6850071550b01042440d090300140802c0412285001d4095190f23981307000e0150240d000700004030f068072a0b081101500e9280c00c002405450b030804001a803000124420f4101d41d80c0d0b4003628901c50407001c03200d034040d00c5812003400151041000c0e0f078481c94003403c0f00603c0203060340005250b2035400081001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 414719595 1250 414718345 414718363
    0x2090a18060509270102030708040f0c03060f14010b040e0c07170d2a09060f090512060415020a050904050c07240605010c0206090d0212010501120b06010c111011 71
    0x4c42e40c642d03224180e03812400d001503031001c5403a400031480c51038514002018110064001031500402c42320030340034000440341070409150041d00801403440c0941404001340111240c10070301e050407800018114103003009031801c03101030050800185d550300302d0410450b0700c07100302100d007006649041500e10004e00054040012081c00028014a1103081d40e0041119204640b220060601c0c1c482c410582c0810300d00b00b1036607542000390304008000410368810f005900a6500928104214000d000b000590305002e103006005080350780255504035030580c814142c800022035070030081803040741000c0e44010342c0003402141235800d25000e80d072034848036860b00f050a11094a40c01e05155022001c0c85440010002400c020599400950104180e40500c80403217215902d41d08016056494528015040041c400c1c000c00003980c44694466018080003c00d649207904c18002900c10b50144e10701d00300180d0001c0100d0120b1001034100012012401081d104122501c600019030400400030001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 414720845 1250 414719595 414719611
    0x7050a150302162013090f060f1e020d0608060103030509150705010f0e0c010e010c06020d1e090b06010512040215160b01050906090403051b120403060f0f02090a18060509 75
    0x44031302e901008208550241e20070051751540790068000c00207000803280203640754401c0300800c0c01d8000f40646001861032848181c80c0042068403240c010569a000b48180040340c2c0041140d00e0b243c1048540e41c0f1401d0100070003261003006074410910f4841c410f2100710440c039000a1400e80940d0715103094030380ba105060007190b00c49942d20038140080c864a0801e081c01c0c0380c04849500132200090040c00704c514080c26030365000591040301d4131140c02c041541c1d004548100c0d00c070501240d01d18020702001c80280c500c60081c0700402c00c10340c0300e1012510b80c00b4200f082c4c1d01168459408000f07025014080500482c0000c101d00c00010107441c800a1b1424050f40d5007111641c501424442d03241c1c4010032082c0300b00c410008010009420000703540e402c6440d030000144020b0240805450500c10946100ca05103001c500007003002096008074217421080f40c1c09110409402c0be5110682c051598099440400c00400b80050381c998068400800c01c0d040002c209a9581c0700810441601910821 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 414722095 1250 414720845 414720893
    0x402040b0c060901020f180f0d0503030103030e0a031205130302130b010909110417030f120114010212031f0e010b0c0f06130215191107050a15030216 66
    0x414100c01c00c0c41040c0e441078080d00258070b000c500e01d09440d11440b5032282041030f001e04680301d0440c0c0e200e06116813001c05000c1d051407a81192414010340d0f07a0000d01c01240010b5940300140ca280c1010a00281142c0e030118222a078000d01038019140b50300001d0b8903088031415010000050f941c0c0007030000c0702400110000400d54242c100060000c407041d00524100b904021003180c0342d400c88012201151002c403a241c10385101b01c12040c1c01d510982445041c45178011403d0880c1d5160090300c01d049401c000203a41d1a03500c0b50006a844012850860700c5843d01440007404a81b92026014410404407400c10f1900d61240e811b21801d245c207030440348070420082000004e0001c01c10445180d168503600500051400008040c0d8040c500d40c402801406110a902641220740d410b584041c803441c09a01340749040024003c01458114507003500c1072140a41c000f4240c20840601015039400312204003d415074114203502035441884030352a42c03130101902c5004a90380441410400d90b140c0052 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 414723345 1250 414722095 414722107
    0x140913060504110405060702062107050306102303070c020d0b1006320906031302010f0c030206010b0a090f1509050a05011d03030c0f0a0209070906050708090402090402040b 76
    0x40300c2203460241410f140003008220901490b030701c40c41034408641e411148156034a45868280c009031490030818008440002c0601400300d41020186100d25000e40d0003010300d4071000004c80d40911400d00755420b50250340c00f10088009001d000319804105170401c1c1c0421400c40e03010079400d030301190040d40d07110814001d011307090510a140300001c02c0145400540d4030a0940800c0a500b010006143d0440364118a4051440402d0a8800c9600020b00c1702d900c900e031200d04405100b0400f481240081c130040d86442209004121711a030440c1c144c0d004020580c280341c10298960b008031102800c0c040ca008c0005045101a030074440644054800c1040c440d000c0600074180d624113070030036032042c01140c60a1040340d80c045605084081080c02e52089404a603020a04604c901c0b100c120440c0110810f28840c4940000d81c1c5240c1c51003903900040d0b540c0c46441c202e65400480c001e1a0003d0420031894020501e0040901040f00001300010315000b003000c0014120307070081e130081d6410301c004544 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 414724595 1250 414723345 414723349
    0x615071a010f15050315090f070320040509060d02030307030f02161203030510030b160210050609040b092d0d091401140705060403180906060207061409130605 70
    0x40c01040700c92079090805007011140240c10714006140f00c10880d01200040ba81c90324a84c0042c98001d0140a42c00c43e401c0c80d070300e4556050005c946540c0441e003414a4005074078000b01c1c070700243c40e0f44404000e04040c20300040100041d00074090039840b200020329500540da0a10041410900c02e49407203910145011001e0b040038000454100942a20b1034200881c9108a01d0001440da040c47c00054946d50549903d4a0301d07036503080640415408801c101c201c14230110306480351034003030f02140c103102c40380f903440350903904100d403000e8015168002003800202072510050301700c0c100b08107031000307045041c00d9501c4403a00e42d4045252140030007401e0303421140078400008060344515052a689044c900840f440d542c0003000107040068070709410160a032943c084d6180540e00200b81c2d112414242030041922100a0702e000b000c80040307900064401c4a445814103c6419401520005144c0102a40c070740c0c2100352802204041000344a40c155244025007401c4a20744000040190500701 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 414725845 1250 414724595 414724643
    0xe030f071403040305121b0732030c01030b060705011b0905120d0e01090302060d020a080c25030302160f0b07021b060a0903120e03060c03060d0b061507 67
    0x84160b6002003105001145d40400c610720b80e14070144440b40c0c0d0f0481c0081040d6030034442e140c0d0b11494011100302084800f4010056a03880c43c0c1586504082869000c0a01030f012582d5995540341e0310003010b50728654026045901c2c06070004080b00c1c01c045443d21114250741c070387d411704290b103090600c0c01c140341600101d925018040540d14003052142e248181d40c5c0d01c990904901d0709010307590072a91142e03886905800051640645015102c81e10050f411004c1c2d004100c40d10040790030b00000072509119201170b203010002007003500c0c2c01158652801e50a213040c1c0c41007a010582c00f0460006e2035001ca0f0300c41202c3c141711b503511484100050400c12050f4401806550454104034001c80d004010b00d1903120b40540b0460f40255201a16101a1200340301580005c1c000c00c910345148041e2a004a4924034402c8190161034a035510b81d04ca102c09071100b250081d5028014111310300105690312442544400c000e46004819014a0134510143d0885541220301c1104082c2c040008844c1030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 414727095 1250 414725845 414725873
    0x4060207051014072d120606031413020a0504050f070f030227040f060806070f0f080c1c050a090302150103080405150906030c04050117280e030f07 65
    0x1046031400840f1510003018010740084104200351108614000b040c2111650300c510b1281ca44501c11a20310000e00f0340070700b90801c04101c5240100c005503e50083c003807400c80300c1d078440b241c102550b5503c0c9106110006100e05030703080035030102c020032951683c0c030030f07a4000c00c4500d44210040c6810a4000d2440b00c0c3c94200c3c1003058014494040340390300889490f140e440b54002c0c03640700008208003060090500002900d801c40c10300c0800190914041071850003079205940300c0c10303450017004064454045940040001130001307000500c0394503814014060b4007000803c50030101c504031f048901900c82c203681185005135295140c80405404008900c040e9820403030b859500d61640e102d0a2050040d4820180030740c040c003880240500441c4101ca40400004201c941c41b8141030001088642140c05410302051030458010885090000c0d090b10504071020405202090400348207040c84111301003050b0a900c40c0e084901c9881d091004c0c0c051800304c00d0380f054a540540c00d044900342442 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 414728345 1250 414727095 414727123
    0x606060801080d03110405010f1209060c0215040507050d0f0515150901030b0c0703090807060e2701090209060903060a020717041d060a1205010509060132180406020705 74
    0x80170320710200090607030989007203402c03d0a00328200001440151040600724000500749443c2040710702c00c2000c1a8829218000a03600700d4201401c203514140c0803c0c02a078000c2d00715440740101704441e1910a00c408415803050600314450442565068541080c00f00301500c441c055008005040c071403408902d0b007070b46044449a81039491504e408441400180144052550010b140001d050007030854100503e001c00403079040321350b5481e0044c8000b9103104820f00c216182000750341c0039070f445100a89030400c62440c40d003040c1d10348200e0000950114030b059410250500c0503512507035050241303c0c400c03900c0e40360140c1c5c1c81640c4c0c80c010f40a140509102410540d00f80410b0001c600400040c030b81414400485d041603403030b910005400c84940e58400c4004285ca001c8540400c5019080180101d100c2ca04881141c0d80310100c09048480700c4001c00209111481c0c4014158408808204c1c4108003030311100410031110000151207004840a50351a81c00094400401038104004000e075030302c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 414729595 1250 414728345 414728351
    0x1e040c0507080f0306010302120109090b071e0f1e0306030606050306090703030810090c1d030c0f06030a110712020607031404080306010905270903070807080a0c0606060801080d03 79
    0x142d036901041c0c0c000c220100f000d101011000a106902a80c12a0381c81007440460f00580c2d80d5038020032000d030500c0f550032a81c440100c0e000c80d002900640c8002c0601400780f080104030003620a08a41c6a401039103200c2c2044420403c1240c600c43c1002941e1000c20180c0e1f01140c10b80c2035041200545219611041c02a4014800c1003d40c150204040c0180c9601d45042400c94480104644108001e50042103040b454000030121480d081010800c02040440302c98100c016401c040544803c00755803000d400011514100c2c00601c1c0c030600441c0d010380002c40002c0c540810f102100c0700c41c1c0040d402192010b401c0e0301503600c00c0e0b40410405078001e8140c6424080402911941c2c1e00207580644001c203401c5c4040b020461682c080c00d458005888040c1802c292154081c3c81002840340d4441356581e446002d801040c00c050004c422241e0258010000714078004031551507010700e62241642c041044601c0f0191000120180a80702c02001a0b0b80d4003880e950602c02c205090140c0c02c2004018149 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 414730845 1250 414729595 414729607
    0x150c010c021603031e030f150608090d050d0b030a0f0b06090a050112060c0309061517060603030f07140a030215070318110411030f0a0c111009111e040c05 68
    0x580001c14440c0c04c0000884a481709140090a5020f0000141940441428600300758400b102901915080303480540e0b0788905ea031907904d0742c04c1e180e030004a000000184108440103640d501900000700f000da01a04031070114245403550004401c00200803180b14002609016561510808164001d09064401c100551411408042c400c03000b10000744007a88070119509480d0180c2c1c010096142c0000e4284000c00008100c0e0030706041c02e0003141d01c52604405105034031400018900e200e00d4010300103625041c00000f019050f9000003504031080c29a04026030b0079201d00b8022079000c0c6219030010a0009160280703401448070052010040515040e00a50014982801032440035004801d5103d498a140c02060203446805030685401c100002401403500d03510309180d00c1009403d804000300100300404a0b84000031100503109039101400b100c0010481d507001001552040da91006e01d804000003103000d81d990050075801251744c03401c807401507007002e01a501c0803040514100e86040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 414732095 1250 414730845 414730847
    0xa110105340501021308120a05160c0b07030302090f09220314041206050603010c05071b030f0b04140d05180f040905100b0402030f060103020702150c010c02160303 72
    0x21081603030005101005410780300851460414094109820000135551500034a00d00c0340c41d1001e52240325003c0c40b800c1d403116031481d03071030040c0d420140b4030743d95403403606100d1040030810301c1243c0d07010b59012010003030000d580002c4000406419119403005611080b00400304400c100090005c6e90081ca58031040142030080280303990f5500b500d007800810348520a040486094050848510761400700080106610441020142150b8031500701800715a0740c110505080e94a0000340c0302c0420403e0041400060711123041250041c0da500c0502e0407a6903036140e0b504040c112880544884089009100a20500d00360310f026001d142c41c006d204101e00100c00412912440b43d0340c04144030440c05005040da200c1040c04400c00c0c00900a01c819002400d010391104140310783c80c07034030310b01d40311086041b81020b0083e01e00c00d0001c41c11f03503201c075a2100d0042d0702a52200740f00726800898108803c130b00e56155406041400c0004000085c0c801c0048030180c90020a03500307101d071515004108000007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 414733345 1250 414732095 414732127
    0x4020906120c041a0a0815040213020c010504080301030204150b09060c070b1209060a09030207140315040804060201060605070f030f0903060203010303020102090f060901080f060d080c0a110105 85
    0xd08256200c184000001003642d08003060707140c040390f0050a02940c0c824800880b000c0c0c4203801e0741141c44070920b81d40c6141c9141d0b01c40030100c1241d1440c40c0741c0b001070098900003510b0980030704800005842d124180030f0b12800c6820864049600740700c04401841507050038495441c4200380b461001c02c10b103041010504035405107060f0580b040d4000144202398050900109001b070400e03411030707512280704102e10740b1194400ca0300e0104038802c003400246030030325a004079085c03160141c0250002c1420216070b00c401101200d021034151007180444443e0410a660b01032069000d007852035191402c0620007429242c02c0d0303101400300603040c1302601c041049074400046030b603490b00b44100b0011b080e03803080d50b04419642c0085c1a02c0d1010000006140e0103400a2841c041e045034043c110501c49001c010082c001c031a00c840c002400c5c9400122100a00700c040e03a0410b00c020001c0c0e83d20103542d500c94295a008030f1941e0180e4100e04483e00c2004103007490402312450900b42242080380e640132205403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 414734595 1250 414733345 414733351
    0x10c080d110304120c0c350c01020c10050f0d0225050d0207060909020c010603050303091605150304030e04150627080d05070615080604050c01081b09040e030a091409040209 76
    0x1e18a035100d442010100300e1114a00640001f16000000d40c094030f183d45c8500c0b4440e00240507004100c1c40d420a46844440400006240c0d02c40d9414080c413110a4000c81d004155540c002c1c81e404c11030b00c0040f1059107500a03805400d000c072811000040d01e8903070700b0440881d082030b00350341c010001845a11782041940d0300f59044110b0060729000b5928135a40503100591001c2d040e80400020300c10120400300700c50007080c0410780343c0514640d54109000c179466000319003ea5444050002c600017910462020012400085c008244540c6016210500a1440d0703c603074045485441d14036903012160001c90245201381c510303020081d02c2c0c028070f40d071514508000b01c81000b00000e59482080500e5004e14541c2c48000c44800026450301c008070307a5840c00743e40039030700c0e4032034030380710f1b018940c80740c0200c1c0d202e034042c2150142e4954040600c2e01d0250080284142d209444420703070b540e048400c01c0a440c03095840d80d01c000d8035914040781c03a5403082a1052050140d01c50320300700b001584400c0480f5030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 414735845 1250 414734595 414734609
    0x3130603020309120c0109020d0b01140105031e06030c0a12030801050316030b041a01090f0b0d0c17030903060916090c050403081b010911010f08040b0105010c080d110304120c0c 78
    0x15490000a1760716005009501e002540a40c26000550a00422005c00760590300440c0720105440d00303c03401520280030031200544500f1900c0095503145c02100c0400f50010b2001c0e003154144140c04000034580d0f02c2d241c000c02694540032034202e0a0680c05860349006110a8010b8800d810410600062145287c000602060741c0d0b400032404200321144c14210402050804400300d5031900161000b038a4204800d50b5220308103109491140307080590b0b410403c1e44034a140c0c541b10720b4180010f0100460024101881c0020b04c9070498649062040c24807030500c00c000ba24a0f80001c65003640450b160390021101d103450300002d0301d01250441c080343c1c181c039040003505480c0c80306181c5501a01d03103185c0c00c00300c05508011035101005009001e160601d0402d07203a43d4070000c2d0f010320840f490700c01281c0141100106000401244d40100000060540910200ea2924071a000008261003841c404401110310000401080c071084c42c1c5103c004185c00c6c50712000807403045d114101881c4542c0602c40e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 414737095 1250 414735845 414735847
    0x150e010509251e021617030c0105040f030f0c150506060724050117100b0612010807031104020a02030d0b040e010f0b04140c12270313060302030912 65
    0x1c82c88600844044940207844540c20070340c40754104010a070825540031043e02c52203a442c491021400407071200307a9081d20200d030030f04030303898a244082500d0174101d03080030034082003080303c0c8100c2e02030080350310542c0908000c52407031800e40340c01401c2000d108008401c2104019038400010581e000341c1191040c401004a0952541c40004400f845100c60042c00e01c241d007104040542800170780769910a03415041003020303a80e10080c03441c09003811006a19240c101c244190aa004194400014010081c000a0408031449803d20548600b80c1020034958030032141002040200c418055440c202a682581030451445000c1d580c0c2c018654100c0e42c0700d45800e100042900d03070307601c0307501e4a252843c001c1c0b0001c00034141040c014072000c801e640c020341c149080c40403030000c026642d6005140c01c1030541e16040001c42086c200c40c0700a03004042408200c40b07070010742d05c06003040da24407000e0342014550710008864011840022544800b00b4140103008000e09020041094000c0c0c0115014003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 414738345 1250 414737095 414737101
    0x30f0f02032b0f0206010f03021509061c051b030f1b0a21090f0206030403031503060b0415050f12070b0c1c02071203270612150e010509 60
    0x107070400c8031614108141180807000b499001c0c04860704002000d400761258a540c20100b80c0407a1151402d0203030042040980d4410801410601a4074080d107448401070783c10070b40301c10001116540502d0400c00701e050b00c059805180c0300316115003074000d4003031000c210103000040c090b40303100d00000385070a159981110004144001204131801200d80f03801c00255100d0075410081c0500c501c0d04081c41d01d01070700001d900203a01c2d0078801c186401e40c0140011091b040d0726070801000360700082c4203d04160700d911112209005089004028502c610740218121100da8144002c4415180014043d038551560400c030703c0c0c85038662020024400c0e20842c0c80344500344103240c6007024035030102c080450700084d803000d51800410008010b1100404803803503050350b00343c06c90360f0384007a0041e04102491301f030644001a005604aa07060214115040761705500200401407041c42070b031000d00400e0600020f40281b580034450f081c62607500307504504009040c0044801c61a405024076400b0307034588008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 414739595 1250 414738345 414738349
    0x61e0f091d0105040606060f0e030a12020a0804080d080a1a210a0f021f020c0105030a0e0102030708010e010803041217070506010f0f0b0a05030a0b010905032b0207030f0f02 76
    0x1141041001c90000d220b00d003081e2608400a003014424a000210101c0c4400c60580c42782658404c42080140201800c00a5807610f419109000800c082940b00b22015030300003401800142000700039640141002499014000c2c250a0000305200304484c64080c0c8a0741007100e590341c0c7c05034004c1c250b508100c000f00d01998159010b110204200f0715104402c001400c004050040021840c0700b62001e00308271400b02d000c208040c640c00010009a000102d80140d503510a03c06194010131103017021440d541180d2144d0b08990040c2d940d4400a80c01034010301c40c6a00000280d8014002e6800031403902e85020400c200c80c1c0b40b034000003000e400c80c2c2003907035001000e400c0075111255040000d40b00203507951000003444000501c00c0240300e10180c0d42c00600d0007210f00a4803082e40340354032030030b203150b840000c0030004002001c24541840000a004030356a1010040d900d201052640b02003941c0b281103060070103941611140380c0855105c4002800041c02c1103420360700c40f07980704c080400c0c00112880 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 414740845 1250 414739595 414739631
    0x10090e0307030e01141602180f0a090c0b04170f0309010527040204061d09011406070606091107030e0d0f0215071a153705040c03061e0f09 61
    0x2400101140104240b01810400e5401e082e442e17200b12204240b040303000c8c8030300320421707021943c03140c40c00b06490000d95074ac00150800c2001c0d503c14248405640c0d100c0104907800e80258110001a030340340400494640c01c01c00c0307904280c0c507203603004604200c041d4000805612410030b0121289a0789003841c041d4201034200743c035021700000d00654880361141801841089080301500481d00ea10381c5110b414204080c03410305071441035031188040940b1000780580c503400400100d440315600c41000403c00150301ca030060f0400c0500005695000a00b40181350b0100f60406622401c000c640d624002460880c41400f0381e030703068031700074074002652119007a540141030780034040a076080414018081300f4804540725070110f0701281c50981813030080c03040015500e04101d030a07003040c0c040450b24585400d4103401917a103000601d6021a2900046030946000c00100e602180e00d500c1e09114171070310000c01450207082c001524640c2890706c268030f05c0c0e8620500c40c14240c284d82d0711880c1914800d4003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 414742095 1250 414740845 414740867
    0xc0a051003110712030b1311090405090a0203060f1504050915130c0b0a03060902070203060c2a07030b091513030c02101701061403060f01030b03120310090e0307030e01 74
    0x190815000a205100680600b407102000c901c650072840c2c60140000d41c81c42390782c0040f00e000d603000d07080520302802d00000340360141c29220310b449010742a01c01a541004001d1040c0032402c13003800681015040c00c001300009420f454416800c040c02c0042c1044005410740048803030318184007403619001d100701c407009103500c0c0140410040440103e0045c2c6400002c1a60001c9a502000a01c1d070f5810041c04074003038808000c0d4140c0114011a0360b03020204060441c2d040c104d6211642c80b41500b51140303100d44254140703501d9804c18041003050010920794250b00c002d4960150405150032045444e10a000800c890000c10794440305005152141c452412140e03806012011145d05120010b840d0101148441551210070f8002180b0244a1032250b02003046030700c503550440d00d80c4020402c1050182c5500c50401d66030b0704407490244c3d8104a99221f20131181c030a682e880c2080e07182c031005103e564010100040c2040c0009030810000000c8480340c80d01031905130403c0c5103000041703c8c881e24003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 414743345 1250 414742095 414742103
    0xb180f070c0503130f090212190e161404020c1f0912020f1b030c040e010207020307120b060109030c060804110a080d17011d090f010903030c020c0a0510031107 70
    0x1280009003000350034901805c0c0d0340b40c4040517240650752080407043c0c1c2318054441c0b00310034070b290119041007540b0510084000008001090388511501c4040c0741c082c50440550322000c413070301e0401c00d00b428500c0014950360305035030551502e0b0b001c40301565641c3e00118088290104500c1003240c4e215550300014001d544030018203015501c40300002d54800a42110703480c1406a01140c045007101c120707060a0040002d405003032036201540030072009101140401d03460395001c008200051390b00b40300040140c5a008128020320140341005280c06500810507410b200100c0814004190340003013110031203100e498001301c640c0e00c0346404915003182c0008143c001080d42004034071000c0c04201e00900b40030a544000b48501c4400008003550400c0c415200300100030030710707181821200c900141d40310b48032108032506450500d0303000303086800422003a070019945584140d4440d03410300c6000003146003180e81c14541401c0c42c0014401804d0310b40d402c070905a407040c4000500d0680c4041d681e2071500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 414744595 1250 414743345 414743347
    0x2706030411010804080c031b06070801081f1803020a0c2702030a0902030115150e130c050c06010f050a080619050601020a0f080a080705040f0306020d0b1f030b180f070c0503 76
    0x1a0012048d49007010100c02c514096600004c41c4503114840c2513040741e00050003001c004008024058540c0d40d0300100e60079068079050b80645111241040c8005548a54000c05203d01c0906102c1c40d280307210f40040c400203140c0d241d1105103c018007a40d45050107a004016503e844000c50180201000d280c025003550a0280c1004441c20008001044404202d603040b810221036604030750740080000080c0c0c0c0100306010f18241840180d000e1400040e00f401d003030b4949280340300f9451802000340d101d02c529082c0c8034801d0180303042c44a9540c005042c40d0000b442241044c91540340140078014216070b43c1941c620000e00300780e00c2000304000c05508014a9500d122250070072003800d80c0404c003513078046141c000100b40350b00d2040044800b01c400340010810303410f0640d0764450195211210020000740c0310140b540e00c43d0782e00315551241805c842804280701000b031030041d00340c45103242d140d0b11440380d991403000c1e0b585401401d01d500203030650101c1110798030041d05440d40203c00c0700107065444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 414745845 1250 414744595 414744607
    0xa1803020105040219050108010e0c072f0603160c050c1201020702030d091203031113080c09060604230a0911030f010e041203050a060305032706030411010804080c03 73
    0x5010b41c0031030300460098a004aa07021500d078151710100c102e2241c940000c0c600d40041050000c04144a0b030000011200103180603c03a4940c0c42c05203002c1d50056141030700301041c401d0b85e01c106006c60002280e003541c2c2e4031b04528020100403030402c2d50f803002d1010301040f030042070204401030024902107034004002031118060028118001d40180804900900c129031103400e10360b010b82d030048c04813280814070300191015a42e04030041d00e0007014062a1381d8040c41580b002c0e0f16084c25150240c0000f00c0103100321010b03401048034113500034003924003e8104203c1844811000071a40582d108005100d40c901d04a690104111151660201540c11b1425910b40b40c3d00019100541c0039540076089076042d662543c506508031241034500915822501c04e1340c508040c00390b004291301030000701000510701d030750385c84031400c5070b02aa02084050300f242c0307160510720410b0300201e2050070080d1201400e51420707540711a05800318124041c113000c00c2400107020009100100d521880303104007038a466003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 414747095 1250 414745845 414745847
    0x1206080123010902130302011d180702060a06080303150a030c0f03140708030d0c1b050f10180602092202040f0608090703021e06130e01060f0c02090a1803 68
    0x20100c525a10031100d000740001541d070220b07000303032803c019450550030041450b66005540103592240c03c8040306403242c0d040840e6a0f1901d40721264016403450b0000b80e0300c0c017400024200f880080c401304441d480c120741840300e03000000c02c0da980310300303542403060003103621000144511420342c0c0010416030340c031900801c404201c20800c00881e0b104083c50850682c480501c00e48400701800b81c6949031344144002ca4143d045500b000c8031505050800e8048a1840c041d0b05840c50100c00b0706442591000091182d10716041220006c03416482d00300f0840e10f90320103243c02040306158400f60000b0b030003040d071540b0741c1d03543c401e14920b0041425101d40084002d9900c0c0700650054419034260b10058000020000c1c01020080e21662100024200a0b4155402c002c00d400039030b2000c0361603ca000400400301e403240f400404d05018403800e009a81490895541224030050300300e54204420010181e0781030741c0149891107295811605074000da5501c00c55007006114000d11424540419440903041c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 414748201 1106 414747095 414747131
    0x311202010c1505150102070f030302070b0309070807031103070b07020f0d030917101a1003020f090604030807030215090d0302090312071209091a0112060801 69
    0x42a44074802c100b211003c4603910041c10851400701e1a541c0c0410450005200074442c48501d41d0542d50020340703030075030752040b5205108040045840c00c1000c0c000d810140c614001120f55003591303814000035486072030600724001e0007000740226900c0d0320034049401090b0040c050425948003034041c40214a0305550070350400c48195004900d20071055001164425080018480480b100c0c072020102c0301e503016040d8000c03072800e418403400c2d114510302d103448100c90306005807501810b06405240748160085207500c20f0000502000b08291704003d401c13000e000b82d081303c0980c0504008003400c44002d898400840d4000740c5d07120040c034441e400070442d048000d41a0b07010b9010410005402da00030400444540002500d40001076a00542c10001400048003d018042c01309400e802420b80080449040041c0009010401c5209401038001848280c000f0082c034100c6107403500359 = true := by decide +kernel

theorem cover : BRFrame.Cov 414568345 414748201 := by
  have h0 := BRFrame.cov_init 414568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 414568345 ≤ n) (h2 : n < 414748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
