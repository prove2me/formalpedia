-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3331
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:11.900528+00:00
-- url     : https://prove2.me/submissions/72cffc84-d21f-4455-a06e-0c4b112269fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 598920863 ≤ n < 599100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 598922113 1250 598920863 598920877
    0xb07020115050d1b050607030504080d050412111c05010f05060609012016080102070209010b13061211130f0608040b070305040609020303160204060906050f150706050c 74
    0x55420055100d84000c07030910007030102c400040c00550079102030f032504031001d8000916015603420180010034140c45d48001818014420360748ca0f41d4a900c0e007200c5504100721600f4881c01c226017004100711200d10030200403007154011f003c10070b18416550016042c40303176841410b50000d40103c00f0a00740315041d48101c20360448290140481c0e9519010004140318140900d804200c10b0b55418001400c44541d0790036202600048801009034060300c080e204407241d101034110f80d000941c510450510f0450b45004200401c9540c0c00c0208a00403040161310a0007010200100d0707d0710b03c0381d40c038000d41040302e143e55a520226030324030311070b203040008503e00d00410b0b00001d1003840c005001481414001d10854011000d5612034607400c000b00c01a1030060030907a2121784400524015950600081408040301c92016001c02040d02c184001c1d02d4882e8440c4000310700d4901c04000c070b070301d0f00c3c29407842c040e074100c800030007800703100f0300340e01d1640036030600900042c1c0340a0170404ca801c480e40081000f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 598923363 1250 598922113 598922117
    0x1306091512050a030807090e10080c011806110a23060c090d110d020a063203010501181809061a0a03170d020c0a0303231b070503070b07 60
    0x6841d11038031607015103034103a24014065402900590b000c40c0c41131408940081c41880d181c080142d54442c0020203000584124101c1121050108034101e02000100c1d840e001c02e0800304488031300c110310101c241e4500d110b02d4050101110070a802c42d80203014042d450360380403642e0004003801d80c1249104c0c40003060340056034440c040105501083c440c056550f03020005141402144d403507a1414140028184c6081e0451071b4244008010ba0f282c2041101510a5603220305491314008001600150031100c0a224408084140f110560301c28040b03a040d84c1080c01d1080b030140c041202e800d40210942d215480c009140d50700321018101e640c01200c1c0380303130141200348501e1700c1045000c0c41c4002e03940c0003d540040d08540810001f20706034a0644071820180c031160804007a0b444040c16648034000003840c5030400d203041410142c25110f000740004001d20060086950055000700c0c0b03403006842e928200c0018948410840041c08c119107410384d100007030301d4030780743d1924254072070745419641640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 598924613 1250 598923363 598923401
    0x2030f0711030c1c081804020c15100308121810092006033607150915320d0608011a0103020c010f150603050714040b09130609 56
    0x2540741941c0565004c2501000d9074400400b550307584100e95020078401d03000640a030134008055a240e1000d4000107a00380058507460210703010412054600500440342c6584424080c40420008810340c0c1c550384644601c1d00c80c035103c0404960340ca030a444640303c010300c11000245810002c54110503030b114818001d0196200000c0302c00f500034050140b0107600603000740002801030b0740544072a14180003100f54a0b44441054a40e0843c0301e50f12a00500740c1c1c0d2120404201004501134200f9024103185401010729040070300c0f10340010b1000d0f01030004c010354494048556004060400e0003a14050880c580c10051b0880c9221560000c0c0e5045054515003900010308403418020813145551080c40c0449003811000154003c2d00320b0322036026035640c1d400340010222818459500104d11121a02d100c141ca426402802e0700da00030079000411010304100604007580c24103850a5841e074071282501c82c4e0b00300380440c10310311454203860085410a040002c00b40c42d6580081c43d0740041d011085 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 598925863 1250 598924613 598924633
    0x3102705010b09010f080615030a0605091b04060c03050f040e0702010f0e101508070303030e060a06030203191506320a090b030a0b010806190504031e02030f071103 72
    0x100003401049a10303404503a880c151800014452606e45610810040a40c00c43c0d48a20000c0846500111041208940d4400c4140030910b0141c1da0b056100c0d0f4402200c9041054542e242d0206000d58400e0703030207000ca2010008201f501071026990030f200405d40590b11555102d028510020042d00c240003d5441d00c02031800a00c0240114880140907400500c9000241d10355800105070590229a08100c3d101010035002c03800e200e2000114002e0303401003180d8402a499506200003e402e09403c545440f60420050318086950b1004c0002c40fa808231101000f401c0002c01c01c490f0210041c2e580d4a804000304120404001000c040a0004c001340c0002100600900120b400c3d1003030b003540251090400c20520703c168200c00031210700074003a2602e0044c079584410000d0400e801420440c0c01520030881500a4042e11002c00d0340e150005128504041c0c83c0a028000081008190000c1c107000e2607980d28020011511407148003110242d4071899410141c56400c00040890700c02d01440b0301031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 598927113 1250 598925863 598925879
    0x70506040b090312010612020d0608010f27020114090d060c0e0321070203210a2604060b0a15111203060a12030212070303020d0606030c0210020310270501 68
    0x34541d444d207520041e0307159174240182a2042c44c82d0303060218066400304000c4081040c1405044001d00c3c4450004ca001120110800c00341c880c6001d540300d0444480161100402d03138510007030f41c90707502820400e00851110b100340d0b8032403185024180e00403c01c0325800d000c2040a6201400030b54450741d40c0c0ca0896621020941c0340c8112080149070b42071003401000c0300f4080d103001400714510040446a0494110368466101003a403004641c223882d010400f00009500540e1400c21142940905a08a140500442000180540080e01c010f603215220119500e460b8510b4001d41060001c42c40c141184040c02020344421190703030710300790042000c0342090380d90002c00e69001d001c0013002504540e05041c64180c4462607814143c00310310480d070f24402241d040b00300070f01c0c1040c0030303550240e540d0702c0d03034100c40c002c1d100268090340c1010b19003a01d594a1550214051403401c0e20f2003000743ea00d0711a980000c10030860f45e000b105440343d103046081d1901514070309042c840a1040350510240e80d0715504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 598928363 1250 598927113 598927117
    0x705030607050d0513020301051f0906150503100b0f0a200601060c050a06050f041406070e13090212060601020f0a121412071d0604030f021002030c03070506040b0903 73
    0x4070340490820b00025400402a070001903004482041700c031030b09011600000c4c02d4403000c1d526808520220300b00030301d0a042e028441d101414140c00240401442c0c1021a09401781c0f0404020030444040080b820701d48039890994004d00c0c428142c680c841a00004684060340100c4012000c91046c2c50101c285001e07202620880604007070140071960710b043c1c0241c801c0d82c0b00e505c007100d142c051700307039500005600c40c8901e03801030a544c4426641752405141140c20100742501e0305005500c841f040216040c0d1201d2060100e2500343d0f18504460120280000602000640290300c81c072400c500d810100c10000308140700c4c000c02d80c21116014464000c0c0c1e5142c0c07070111005004840303420b01819003107004199001030703a00001070840c0f1b4400c05840710705d00da100c240c42000000f10350304100919250450680c101150044440781c0c50030380b965a4000455071aa44c0007070003200c0078010b06103024000e10942c2c0307080251005503a40c900c0d052038440e4651004039412070b40c1c010140e0200f2000000001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 598929613 1250 598928363 598928371
    0x801081603080702040c021f05010e060108090706050d0f240f0f0306090201051b06010602070b0f0d09051903050c060a060b0d1a0d240e0a0b0c04030f050a0507050306 73
    0x40c2c1620789590350f0240320180145650601c154843c50000c200c850510b030304152100c02034208002400d5060210400618a024118504005c500014002440d8020800074100c0e207a90615907903903001c107e444400307080c4116082c09418940b6a01c55400580f110495008441e0b0400710700c0d0243d15503810301c0c1002124050f00a02c03500e41481440010115032140d00707128014140306040900741c003584a1029140d40c40f40849401c81d00c0108007290301040440040c144540c0b01902b0203050b108808800d006c0c0e90a0481d06a03181c2d1030300c1c020b104060150386200c40142e00b0280c0707004101c5c00c01815691005141080511540000800e4514103219540603550300200702890140341c003800700c0103049450380780c0100e01d00460900055607226180504654465a03503480c1c0b5001e40c10040e5030025050015180c030b182440c441c0006804045882c544441c0d103c9004061a141c1711011501401950001480b507900e04030405c003800030001e41005414801c0e4125800b1640768404c4c140c503144292 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 598930863 1250 598929613 598929623
    0x10608150a050703020f0c0d120b030a0206070204060e07020307030e040c09052229150f131206061e0e1b1c0510060507020d111f0801081603 62
    0x300401d00103003481e009680c00516524015003015103912000200b90300441503080c20343d1248a2006460380c002d9401c0c2820303158000c040003240e07400700c0413944481642e10000e103d03400000e40f0004550b030b181c0c4000c010701039070800041149488040030f50389910415040c1c0102d00044101800c80c0391a024407600341040340c1c1c0704443c4178640018041d00e60101e034801c02d0007201c42041400100480e101741d451100c8000701110140fa80d400c040b1504104500fa8203000f80c0c0400e03804140075100034200c8a0b4201c0c41840c480e607138004040c031104011625040340c509116070581c002d0a0100942026040d18100311b40100c0c5540c1507065212441038034130940091041000014001d0452041c5429549240e99002403030304120490301e828181814000e001100e41c0c0b002480f50454074041104c001d014181001450250070341c0000e0f801c244800f100600290401141340c80d00e0b12090300408680454481060a141c03035083c014006a500b40106202c512400a0181c0040d1070040c0703103400c9036000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 598932113 1250 598930863 598930903
    0x706090605160f06060f140603010b0c100e03030a050114130209030c0406030b0f18120702040b03031c1505010c0204050c28030c0c02061204030e1011010608 69
    0x105005903499000b42d50103840c400d9040d0b40d80e5020609000b10303140301510071071000655500b01035800c80101c0f19038000e0350f00c0700e6402c08120400e031105021a810740701e68661b000d40b50a045080c0601c1d103d0071303d07034807a0100e00308507001060300341c000701079406818140c000340100da0f01d5102c58040207181520455000130085c50014400840e5402028004030250507210146804000328040d1a40e59200303c0d112070701141000751201c02c05203402c1d0403c0210131268161880f2528090b691440d00c108003c0d0f104000882c101103507699805000750284c003400f51b94a071000058014001802241302900880c1080d035407d081401e045101810740b10143c4601095041e40e03000e000081c81c1c014450070310101c2c00c0220080061030080c190b900c2c0041c0c0140403501da0490500202554900410202401a500e502d04016514042914000708102c1d040c00c400d40e440d07003411036080c1031a40c03009412104070720751070840d140c0c8603611059520109000b401465510040940d843e54060100c540000031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 598933363 1250 598932113 598932119
    0x4020915060f1204120e031002030a021c0209040506030d020d0804080d051614070b0f132003120309030403080f04030c0f03050c04050115030906110a0e0909070609 72
    0x300d03040c96900c149001e040c050404120306210302c11944440c028080b00c20300081000704002c1d07440490101c200303007850040c60760540c800120384d40700e10307655480c0307140da40100010f11424101c0d4143d41e202c50361208a1840c01c0c1a00400e0402940074070355260240d410140000c149003400140b6800300c1d88150300510301500102c00c1180c10403000361044402100410200d0600e441c10f00805000d290303401c04440b4941c1205101501c18440c12001c207000500a10000c800f080ba12000658400c00407103584510f40e84500d154510041c00300070007841c00a00c03130b000325820798620a141080d04015000c03240c0f8041c0520324410140821901540c650380104428000149024080c000704d000b032468450903d070b1a5540c01401110315040070140380643c040410070300c2400c1040d180602c2050b0340401080d41000e2a0038800c5106c455a201850b0300d4800c541c0400603190311844181462108840e01d5200c84a002000d5110301d40d01c3d144107103421004034840040c00310310042191419218041c1c4685 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 598934613 1250 598933363 598933381
    0xa0b040608100f0608011109090f0615070204020d0501030804050f030a05060a090f12050a140705071509090207060b0a05030f060f0601140a09060207091512110604060201061508040209 81
    0x600c41c800684400d803100400117204c0006d00030036081c144200886521007460307000340030341c0c2c02c00240500340300c03040641805a10303260460040300d0303404820001e55039941e80c1d00105010784142190340d00303107500c1c1c400000144062580035005481046401c511411800c02c1019511500554007400903040b01c0d0124028a01a50200c00b009200740c2d02400102c0c801d40361200b090070440c1034040400c200040b0303c00307055030001410f0611500650154103081150321001d40d1003030766000f003501110103038110512480c040c89011008044842003503584510303e01e4114081c0100c0480540500e0100350045410300c0d0110307610130002c5040c0c00514855031400071548005002400f10350510441c030750b0603040707a85034100501310040c031503c504c0c4c0c0051402000a103400e00d00c2e0700118030b0a20b04a01403907903104422140c4103d55032074502255100f05828032a0550002041e507950106002070001440c9130103411640440b80b40d4091640c100050030f0059811240407603000b0b41c032007040000204411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 598935863 1250 598934613 598934621
    0xf030c0c0b06062803020a0e1215091204231005070b070509040c1106010f0b040306150906062a0c06051608030112051c02190303020903150a0b04060810 67
    0x4c07500781003040040c0094134075841c0038040c03801d00100090700014030700d41054010380420802c04040d1076084030344480d40f0407103860b270b0100014400101c2455010038080c000400c180061041c100d4406a900d6960300303201c4c40c4200300c0340c80b0004034485e4200c4820341031034680404000c2c0320350394480907d801d0107030b5641c5c0350030400140100c0c10703c8402c4c880000c00740c80d40d2080036100d24403030b1111282901c603401540c1c54240e0592000c64a0400b02d42c003805141015026641265881100032030300140500200b4402207890304078066007842c0c017500082e600ea00102101c010b43c4164543c4812881074414081d030561b041c81c0191130b02c80111810000d5602c01c0d00109070341c0b040030350203031852030b5640d0f02c03843c00d80c6c800c1c0d00c00070b010000e070502d0707000b030140920070f0f032070089081c6030a03c0341146c2c2503034042d45130303401c17440f04298192402c1403907418507010f43c04950400c8401415100750980912a030000340340c0c00e0b282e0328121890040811524146071180d201501d81050050680415442d90003002d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 598937113 1250 598935863 598935877
    0x20405100c0c0803030a0618092003070305060f040c0603020a05120702010b04090803011a0310090902030312010803122d0c070c030605041703010f0510110d0f030c0c0b0606 76
    0x4210781d980000c3c80500500281d03008a1200001248181c9801102ea00c40c0c1044c5119100f01c5150540329000079a03440e1800020301c074640541104010400c002034204141c690001e0000d0040e28100b0000080700b02016208a10a02800d030703403640c403140110128042c51251002240c410417940340005602400503038001c0182c0f0021941d16203d6020605490b2000801c035038954000c030045c80041400308100300e200b040f0600e02030031403138013440038202401c207031140b241a242d40c0e000600943d10240111400380c10303a203c10391140d596a0841580d2a40400c1c204400c580209010440c01d054a00c40742d800f800320404111030000010180c5131040320040c0c203108290b1000c0011100082c3c91820180046000300400100c40c60300b03080001440d2107001d000c41600c0300400052040315603e48400d82964002d0b80c0032015005420429118100e03170119810a0f48211014040002d501c03c20404401070310b0b603800c0c000c800b00410142c449519400340148003484030800a8520305014000d0104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 598938363 1250 598937113 598937123
    0xa02012d05100b0a020706030606020a02130207030201060302030f060a0c0903021e0a080703061a010e03060c0a05090a090519020a02030405010c050106051906080105030318040203130506010f030b0a020405100c 92
    0x1a650350007a45040d40708007614130141c0c2103540200119030f01449294000d183c103001404014020b9400641e0800c3c43c5513585021070340c0030a0721070500d40300b5070101000d0340c1e014003200c840085505074581c1d101011560200214140522118231520407401041241e078043c11141d0f0742c9030003011240030003001c00c120f96008500c44400140280003001190025405034400203a1407809036480d058940300c1604060500007001901e08640c0c5001031090713404000c0a0342a0348814507014200c2d01807181a500329404501041c1c0410960740d41d40c00207009410755400001844190710742503050b03020700451000540c10a12042106502554500140724801c0d0000200309880f98000781502200c000850b10707100c608001031011075001040103025000450040d410036221a14189003000318032943d500031900440810000b02281c90300310b10781c80c1e029054942c5503031640702c0312292401034842550025104004505420600d100300e50903194082c11030351111240410540d50b5071500041126 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 598939613 1250 598938363 598938391
    0x304080703022d12180d0f06050a05090c041b111207060e0d0207050603010323012f03040b01120c0807080c0a090e0d1b0501020f0a02012d05 62
    0x4404a2440c503114080f86096644011000525045031501100d0184c841c6144c2d0100078001d1000007022464114510488403890101d8441c030f01001b0f07034109007400502050412040c001481829000300d4404c0b03003080200d403010104507017000b00785d985c000c2c0743e28410a200c241d010341a500c500c800e811003c0c0c100c81258070314240d01099080381d82c001c0c041919165941c0007814030b803d40c10300060300c0c0400607200600c5294180400501188030610002704074070042a039270501c01d0003440300358100045000c0200300307050700342681d0f100301c4071070f00f9030400450750503400c91020847d00f82c2a00c0c011074000317950b18526030078403040b0003010381c600e201a20340000b0b400c40061060300420100d0080c0c40b441c40541060040b141c140119540150441030000d401c0220320603d441000510718000c000d0b602c2c24040e03207404146171a051010220340a80203500000f5003102c0c0c1d04009004203100c40b200e034000c2010402c1460080303c1e1400c0034800c192a4102d0315200d948500442d00a02d821a0111070100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 598940863 1250 598939613 598939633
    0xd0207061a06180405360c06120f1302100305010303080c070803010306090611190207060536030a030806150c06010e04081603080f250c06091b031511030408070302 72
    0x120301c18540c0d504000900b46a01141c080c0640f00b80004001501c00742c501e1404c09d0600004a294100300411020060516800280d002e0f000c0b126081865030300503101f644111201500103001c1c00c401d000540200c0c8055020940308904501240d01c0150010b808a0550342150b5920b0003401c4050001e507185922101c3c45101003400d840180300a04070700440c415210324006010f414040035a1054060100074404441118270b85401520300460900a0000e81142504604c581ca44110140c5070544038400090301050740001034540100c80860350281d03049130b0240710884a1059402c029000d4111100410407101842d0007036412512440c038042c20300324040541d51031200442d10503800a25010300384040ca1707980e50300645d00450001c40ba150814181e003600f03045440f44680c0c02c402c12854410100070702a565100c0d4503000c2c0d10036a141c25004024142100c02d8020307010554440c145400c082c0b410b0040361140f601c1e070f2055944020f0540e9200e4881c64107680281d401130303080d800f03640c2803a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 598942113 1250 598940863 598940911
    0x708040f2414010b0f180a23040c0801090b0a180e07080c1503100509070e010e030c0f01050c100f02070c090c0206041e05070b0a12140105150d0207061a06180405 71
    0x45e000340c4988c0110124030b100b0720003204c00e02c040040c6041d015600e09050103900030352000c0c04c1070641e480c00c0c6000c0790350a02580402c03007400c001e40c442d4400c14a00b501d0900001080c0c2c2044000721681003c403000592078204560b251302581104e01d034030603048181078a06c1c80f103031130186074422403504030559131540c4c070004100a0a0101c0303140c00052a200e0400310150f8000510481c82e8100341d0051101038004000f20700c2c200740c40c05000f0b041c0240881c20904500040007a0329060010301414080140020540030181d04010012038040701040c8003c11030040e1340c4900401902c240d801132145868540b41c42c0050b894154904254040160301c00012620410000004000000006559a4050100070300c040381c506403104070340d401e040b620341c21201c81080103815510308a4000e1020700c1400700c01c0340c081c4985801131110318000316400060107a944d00840034080c45404802c259000c0d40c04000d1103100c1c440c10340d4101c9401d94082c480c0d600b0540c0c484c0d80d0184c0c2d004008101850a20300e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 598943363 1250 598942113 598942129
    0x70b04061713051b030a020409060c02190b0a020d020d090506011a0909180708060708010305070e090604030e1c0b04020f060703080708040f2414010b0f18 68
    0x110100c0c074034080a000201e0028040e40c1e10504100548002c42900d5480c281c80b120a6980c404241c490002c0130300aa80e801e00603c4c0c2100da008004104c003951070300d403010261104140c1d19000d802241c407411404004207007900e240c2d036840300f0038000d00e0783c81c0f5400c40020f4100b002520500c5900b803001c8129020103206205445014100034040766252002010002420316024482d004080c4182c00d9076031030302448103802a074031200d05080010810541403070201a64050072840c850002072210068004240e1810783c3c0c040c3e82650140c0780c445030041d603050307025520808680d10000c000b401080c41202681c0300b10750b0080000e0313415820101e00400c5021010001c0d10303000341c0401400f0842c54810036030b2100d00c3d0103459040c00e0400580300501800c0004103100c7c1808000d80000301000003030841100403d51110250113a50710319400c417460620488107820710940b030701d070107454000445410681290350a021030fa1070300c24190414211600006950343e08014048014601ca070780e5420b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 598944613 1250 598943363 598943369
    0x20030912010b090a0b0a05010e0f040c11160e070e152704050705070209040c080a0803091e070b18060301451a0904060608070b040e0414070b04 63
    0x10002c540129080200b201c0c40d60083c020402141c0381200090140e00c0e5a80440200d0b1400d080a000e050030000100343c42401c0010a0303580103241102240e4541d4102e1a0500c41051600403209151031401102c02e003840d003401059902c008520001d002c10b4442c000800329404007130011a4040f038138400700d045682200014075200196035405224400302000c4030000458119024461800c0201000c4c0191040441c0a80a030a0410000701407100c0e0300004001000d046007291010005400d01000f90342003900c60201500841420080fa031804005403411290584c0143c031041c2d10380354800005500030031f410340302681e2a114010165461001440c003d090540440c0d10b030415008030b108000880b0a001d203000115040380c2e207112107200b15503003040314029000291000b6142c894203d001001c00b180f0f58000c82110801003002001d410407801c540840040b540c00c0c6840c1c100c02600c9003c1c40c0101100e182e500f81c0040e02107000603036002c112401040643d000940c40340c0700401070fa44150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 598945863 1250 598944613 598944649
    0x2011401061e05040308030c0703020708030705060f0f0f0a0f0e1506271b040902211b07020402160b0f040c06030b01021b0a170a051507200309 63
    0x8902c1035201a14a40c81041c024a649402440c0c80e08580d500001c90001a00f0a520414007050140c1014020421310019115900440c1d40300c1d2094503081f992054100c95400d1216410004580700070011034a2902603002c06030800c0c0955941c240e610024200d86240c0e900294a4203540a01c0400034084401034066884070944c6601e003040901c01c40381c100c0d0155040800b0158801c2e141c0480144005400c0361086003050086890212504682c0c05150003403006544001081200c003091089001034040c40344031100c14070f9907080c0e0a95840510042200203810301000f8400061800c0d500501030b80d0461801102d5102d4540c842c040c0145040b90030302c1030100c1510a02042c821150060070003070201d49014442c0d640500d000075111522848000d07a0031481c180b1440349556944901809170801e080c16900d00081898038582d034024125095031750340a0311185901c0440a812914440c40c980c0c0c441450130900300791162030034909070307440255a000c24070601c0e01d0f5645a0403c4600120f00e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 598947113 1250 598945863 598945877
    0x5070201020a330b040b030705090411061908040c080d0c020105090a150f02010b030115031407051504140604030803180f060f070215010302210c03030a09150c210201140106 76
    0x103103003440111295101c0a500c2523200c100c04010300e9842d400065402648101945034551044001ca0054041d40c0044000c00e00388020b4042c0040d40f0614241c401c0303010300c00b040c081944c0c2e480c0440d190b010240b41d42d40040c04089284015500560041060381c4018008002240d40d0319045113140107055a2140080c100301e0000a145a090040010000046000f080700d0000b040f00210340d03803c1480300405e900d43e8003000005082091111400806003d00134192651891140310f880c3e038014000c1c006190001803021201c0d061207010b48003540c0d0303c0380115107147c403100841c3c44c2480070380032004242d00c542c1c0650706100740c2c00d0081d90b0080d41e80f015040d40b81e045c114800b80c2081401c45082c4d4480304004010005030740e440345201c5200c00e402d012500c9020885c00c02d0703410103218152043c1c1601c0b0002c4c26403449603001e9410012500951002c0c42e9429800c4003c41d403400400038060b09410000961807142c80c00c0944582c804c1d05140000610346650088607107840c2426031142c03000c1a00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 598948363 1250 598947113 598947131
    0x7050a1803050102030924010e06120309120c0109090e030702060c0a0f0f0606050102010b030604030806040608030415020d1b060b0105160c051201020c031204051f0b1005070201020a33 81
    0x1c0d10001204140301d6940740707d0707598101611002c034880024141c82c8105600c0c0e050038203405041c0304030b07002004080c2c44038111810142c4210780d03504800000d20300151a000d00000d59844522a032600b1140113400745161602a40070081c6e0381e00100c3d400d0f00d4600516088a0009010a0606d01024411112007084069a0900204941c0ca6500c1039040da4100303d03000b01541d40201d00034cd805640743c1003001460b2240f1001c9401003020b17800510b420f02c0300043c0490088a065503807101e410140d8204e90702404c0551080325100239925800c24030405250f8a200010a250091410040d0601d0318074100300880204200713482c0d442009840d00120214140300a052800c0d0341060000d0b008002d41c5006d581d240043c0e40d900c2500c01000b0301d1800c0c4800303d020088140980601c0042e50544011112030403140c1000a0415203116407040b0604d001b82c40307031781e8054801d44000b16016005020744e08080e071a0791f60091180500c002240c41800004481401200f0405651052182c400548410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 598949613 1250 598948363 598948393
    0x11202180135030406080f1f030b1b04171b0a0504110d141501020d050d02280e03070e2811032d07050a18030501020309 53
    0x324512041800010384001406507191480c00199031903984030400320700800e81c00940d4154124400d24200c0307404001030024007640d001c96814003421902414000a85900b601d03a11b980401e241c46881e080403c410400101c1c1110b60880c0e803152079002d0100080c0c12903a851451a4402d4020040c84103c0c00103030704030500c0c20803101d000d8004040c440c20748096004002150103e0328820303644216110030595041807401c40070348000c824205010b0026a01c100e1864507070b008121114181041c4884103443c031076100043e12080310303016884092400001141f464081c2d44003010b1110a0340c010310328504901720000d986c1e204403c0c00e5640c0d815011100003014100f00c0168003e081407460b0809000180c1c003131044079031444088201d200b1032180c0d0402524050300c545942400361640c0402004079060f100310005440e8142c448005545000202000c9203211095030440f0005000380046210b5900615521a10202c1040042c8605680b0365070f60b82640c2c008c45001449d030b00701104154000c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 598950863 1250 598949613 598949629
    0x1b01060611011505030c0409050307060c050405130203070c02040b0f1008100e010f0b0304030c0c031217040507230d110a05060703020c040b0109031203050103110102010b01080c07020a0b03011202 86
    0x4200010303200381c2c1d0741c90800001d80c0c0c0c05210603c40c0c400c03039888d8880760030810208101c8406507031082080c09503403013900001e0001d4125118050240408801c20509551284200da2203095191200315500200f1b40030304c801407202807100c0c1d42002c000507840d00301e81c0e941c051b030400701c44a0b40e4400a075440c2c40b500708201c3d043c150344103010803100400180100d000e08903407030041c0c40030f5002c0d40d601c07641ca83c2411a881c04a4900207803030a00b00c4400407061040d02c0b0511141000f403501c4405022000c0002c00c000c44500300c8000c1e00c10b80201340300f88550245c204640c5902c5244410907039943c20300c1c0b8002154294000000c50740b24107407046003a010308044400740e0061100719003150424515441c0a5101c40048030200d01c51540c031440e00031968020582d82d0099078008031444030300d040c000030243c0100000c3c0402d5841d800d100046c80c10035032050103242c0b1001c0042c1d4406115440d01c04011560342c0089030704a0f44031424901c045418848900690300810240c5110112400b103030050007410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 598952113 1250 598950863 598950881
    0x90f060504052a01020a020d1a0c070318030b0609180f031305010804050d0509030a0c030302031e0c0d110309090708011802130e070903061a1206010f0b1b0106061101 73
    0x103100407034900f545683c0100d9a003440c590141c1341000c0902030351070200c80c11131b05241c146010384004000d1102c400d00003809403803014402e0f21100b81c3e4046e1742c160501d04440074807006161011000001d40b10382860b60303403140c20620b818007184094014070012420006101c07280300c5640d00c0401d401c400c3c8454903810308010306d4203007850f0390541007a0301c6050305e030700807507100340b00303000f0000388412407900d040010503603d83d003000001061a440b850001d440b60301440c4004a0742e5481e080c41c0800b014250300321210803540308020000c10124070420341c0d6034120124040c1c41070000b400045d9090701c0d40064a40301f00c003166100d10305076042090ba140e01c001034800d0783d0f0045206100601d50b2170203c0c03401000342c800460114043c0c7e070b14030000311004450794000800d003a0a00300c4041c8e0340c050b80500c0212090303007100c0c41c0501e4503c01110742d541c1c000910400b201d0a900300000c2202c244143d00400c40103100402c5201d40300c10140003e0b0030340d15258041c400141e801ca540005051081c0700390261 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 598953363 1250 598952113 598952173
    0x1061a1c320121030c030e0a410112020405130b0112090507050d151b09050303130e07050c0106031127061c05061614070305030a090f06050405 63
    0x3009004a0f4460201c1c1041c020180a0825020014940a2480520407901c01003071805030640780c3c60340710b0035109414480103100c207107600c0050321310b0903030344498103034844400c42c0700c0c5903a074140d0044406184d4424404002c80d400c04c00402c0340d8845840400012a44d01c10100c1c0c4203d240000616140c8400354032050320345400b501000060b40895880d04035501100d00f05030030139650070a01940380f583c0c29500141303440c10398001c40c002d4803020031865038107103a151303249802d5503003041c10b480e40300d8206241801c00c0d900d0818828a41c0d551006a00040b05140c00c3e030038251500022403c4032565042510715186c428488801d030300c0c001d401000008003114a042c40c4010390710340c000305100042c0405120740700c1101400c844038981e00c010803490760007504490450500199450302582641c0c50bc0e000180011100c1e801d00d240300045500059040d540e0519550b541c00031100246200c45c02140e690382031442c80400705040cad01603640182c3c087d5014001444864110a080e01103070844030780703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 598954613 1250 598953363 598953389
    0x17070912081b0613060f11070c050103180203120a02160311041a180a0e030409061a0301080721021f08160207061d1203040801061a1c3201 61
    0x40b080c94401500c000d8136501c020b01007600f6180015010141621a006840e0340c5404541d15051144404100c4101d94080e03c0411000003a40580d03240b000702d052002e900b552182461064109105004000c1101a031045e13404a421000c0aa50b078484281e2064617100007541d4003418034a8284190151810000c0400d0312407070740c11003c501c01c0c6810f9900500103000c400001405001d581e08100428000041900d90741d5460b01a840000c02481c0102d04560000e8215000e01c0e900c1841140e068a814900820180f898008501000c00040a0080c103400400a4031001621191070048211182020101d00c60030b54000040c603501c001045591580101040d2800180d0013294040649119103446030304458150310002080d03507050001c03a003100c4028444d40800704084054001e1703892040c02404810303541c1200c0301808070801c4000103010010041c50340110007552040244664480021030742044852900c01898002c1c2c0c002071405003094998110755902d035141501410a4040c03481c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 598955863 1250 598954613 598954621
    0xa052409030306100f0210060b07031b05061f05040c082d070c02010309140303160305010302030c0f041d011a040204080307030c050717010c03050f040317070912081b06 74
    0x30ba408020304401c000b440760311100c40017054030074000c140b5003100000341403100746d07a5001112555400340e01e0580000b00710001c44958003000c208403118a6422000501a0f40c941200c1075510904070303039143c1030082c44984000740f2030301c82d03001e080c4400741e8644a07c03109241c99201507042d01c120522542152103c150f00308812600043c059400183c01c1c640400f2a80c9207100603002010340410280541c4000000301b66840c40000007544142c49580380074401315040321056090300c4080c040254590005c04061000d070504a46440316100c0090002c20040b4000c0c41c1c0c15401e0861041d10b0f0b0303a994403840d5050b1910341c2c0e1741c03a0880115054404500c0e09140c0010f8688034040c0c0c010041c10020700c0003010080c082d08002001c090f00b80900300340c2c3d2100c0480c48840c02042c0307400700c0c00301007270404000a0720b186240b0b020030b101d103426803039241c8000709031a42600d080c400180a101400039919000c0340d40e0b04944d10a01000e03204041c610fa86051130310850000e042200361000d06980450300300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 598957113 1250 598955863 598955869
    0x9220f052a1c0f021305011106060603040f02090405250303120b010e1002150a0615080a0608070b130b0a020a060f02120408031008010c0512090a052409030306 70
    0x1101d00c010780d160242c2c03200003071904078031012006851110558142401005841801d81c010401d4208a07074005450960319001580c240f03049688110780c64002c00c001600604040340291780c00b5129410480c0000265400034920000c1500d080d6500d9100140680e00c0400302e05540c10184d01c0c008604046038510303500108400b0340300081d88800790f11001e114000c0d90140c071040c0680788004209403031b004030b00350740207550b9580e00c840c045552030f0200124420058034890101554200141c21000d0004c28405842e80ba40151121442e80d130354000014003100305100d07040181100400c410750300c0c60517030444800e508440d002100507040c20410032000c507400003070040080b0ba0004000c10b00111110b2910002c0c001c5074003020080300480300700803c0003841e0000314404e24908141500194641c111207007205c2c0c0314007110f0007044003000f00c00c200040c0c100d500740d40b11040034122034606800390707501403c04480c50002003641d0b5118461a050750f040c5039060394040b0401005604610b071002c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 598958363 1250 598957113 598957171
    0x1020106060e06041a131701050c040b090904031e0f030509070f051311031005011106040305160c030c1512090305030a0c0e12101404110609220f05 65
    0x81d040310700f0204c080200210304440e0585006e542030f000002422a42c4912624204a5a44643c20742c1e520784400102802160310545080d00c60b50102c0f0b9051410190500c1800c0030003810540c1070040d01c40301c400f41401010b2a130000300085944440c0e0b0b483e000d83c0d02405903440a80301d190f40742c202c008180043d540030442e41d42182c0f8120745841d41510a5046800100300404991180c19400010014030704e1445140d0700441ea020b0380d0300d00c281c08003080c159890300c1c819100103001440411492156180c01803003c0080350050300303914002c960b25a5a1803000940e0351003190300c010042d1300c0514071a000000c000200583c40c070180103903142d0396801040d0f44002007400d45059650701100c001039215180d04031600f0409010300c204541c42d0b9030b2640d5545a0b01c00422161418040300114102401100502072640315060180c625155030400c6900d400c007502c615000329407204000f03103416421108071441c03c031550b0300040c80103800c036002d01a684001c0c803811110300341d112900900090800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 598959613 1250 598958363 598958369
    0x510090305151e160f030504031e03140108150108030309030a030f02120709081b0109030f03052b050c091e01020708030c030d06050301060b0f0a140c0c01020106060e0604 75
    0xb4030310119684480e031183c80703415401c040074a10321080d001c1040d000f2002040c50440140b030f890b519041a003c1900714180c640848000300080c40940c0011204070005c0c0c8044108020f505010030004400010313800185c0c000d82c000a00350344458608044000860903050261070100042c5285184c82002141d0303030701c188a4000d0030151349503460b05000e0707004d0b070648248045010070300249007003c0c6802026076806029040450003440c114071060266408008400748068541c2e43e10545191a02c101c01c160b10710f010b4050100800c40c04004a00c24203001d020480442000101d425401c968207040b650700501301058a4410030005c1055078502c414066140c00e0400010342d41c280c4180100e041c081d007544204503038031010400303144004010020746440764442004022840d038481c2010b09842d0700d0710540000d510200211000b446483c001003007c80514100713142e50981849222140e0341c003d441549942d0842c52407507805d582d081c02442c006007144d01e00200f43d920303110001b403c0c6200d144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 598960863 1250 598959613 598959643
    0x6160201091e080702040606020a14070f05010809030d11031e10090203060301140a0207051902011b032d0f09051c060603020d060504050d02030705030316050904060b040510090305 79
    0x41c5640c0b04021110040707030551940a041404200e5403160081d503240360103103084401c54000b290600c00d044000400204071480e1492400780030f0b28141c01521342d0100034054001c0c0e400704004103103410650b4021282810713085010b6580e285000004250301c40c5520394141e41c082100014480c480c08203036449030a461850b00c0c0140d0341c4e141e070030009004203000e50500c40e8207058441001310304407160303010f006000e00500503116800794001d10381703201102c031540081c00305454810314010481c3d020350000d88188642800800c694070041c694041d496011003174007040f07405000c41d10001d607000000c103804414606210410718208030004008982d5600610030f000817220340041840f1094124600075a0083c02c2075040b401c1e282881000790804490035141e40c402d550341303114024800000c0b1007095401a002e14116140d1820346c80103104101071078820800280702c03540ea680d80364481e42004081788030b40749a0b62841c220610102003120542c49043c070040c0001080820030100d45010050504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 598962113 1250 598960863 598960913
    0xf0a0209010c050d0905042703050912070e0406111e0f0405041406090c04150c031e020a14030a090b16080d050f0a11070209060102100e0616020109 65
    0x14001220964990b520280691040c03205020559411141000603641e040d102801040c41c100320150307403020fa030505101240e1401d1654004a880f03040038108680c00145440d9811030419030444c42d02040c0c0d001198004d41c2c41061204101c3e17148a40c00c07084074001388040c2041c2501041a108420386c02d0484007900e00080d0601c1d68800e22002c40e4080c0000801c10401e1002c10710681c66403160460f01103006001210109400009240c1900c0403901c402191580c44079a950040310004500d00048080c4810805050903025095003068020404c0340c3c0209030034480b60800550f0104142e005007513a800070030003d00e030030341c0c04214402501c001e6442030759265886003030020320303400205d000b91519002183d0680300380d80700d07006940500d5400c54046120744840c1000c17000c41e010500d0400780800e04020b800300509103a200160b1143e41401525015240c0c944407a003a20006100c100c0c50b600444100400c220114240e2003031404284001c00c0a00b000e43c0d241800c50540780e0b02c0ca088001c60b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 598963363 1250 598962113 598962127
    0x7020303061f321b0c0103110d0e010908031e0709120206130e01030c030b09030a050403020d0c08060703020d060e060102030a08151005030109141501030207140610050102060f0f0a02 80
    0x2c0864603451070765561002d076980da20718004d038a00d40350740b541921841d0040c104501034561007402000540109020307910321b8010381038080790003001081c0b400805035481c1c03049000403d072040c0c007442c4500c82d400f120240031413845401d100c0403407000f41361320240101c261003423180d580281036064409605840e040c2c1e417521800384101d0700d404d4070360160141032204000401006040e020305c0040f00e2060700c103540c3c2d686916914036140cac000d01440b0000110140000c002614040700342080190142051120003034032000301ca0b0a0103c102e42e6074003ca80c0006098049004610462000b084003440400c00d0b03040c0000001d44a124401001040241250120343d141903407283c03281640030700038603505c0c40106150000c2d155400902c10307410840e140410040e0200f03501e4526902c203041d1210310310544030f03a0307000643c001d4110344001e4400d0b4200c1451590840e01c100305c072500450b109254403004a14100c002440c049005148044c100b00300401c1c000e005811501d280c1c1c02c040580700243c0c0700c4407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 598964613 1250 598963363 598963427
    0x50d020a0e0d12020f1c360807080a081207140301030302011a0102010e0a1202280501060b0c0319050f0d0b131a100c0b07020303061f 59
    0xa060000c20342c0880803428110400034101e0b180003d0180503005c2d144000c03c20000c41e5110300c0700402442c1c1310b5407240982000584600548440800d0108011135481c885c10141c60240b0117603e001d401c18460a5014031610360200000300c014440200206002c0b0a55501c010050042804034000410031030042440e40740200d54240c1c154140000c055182d613500e04000340640298901c005418003031761100003a035481030140b1004d42a1400003029180c08076902c20702d41e43d4107141c0d42d100310300500300f10000c15504120742c04044080c0813080f0700004900d0401c4c0c3d00310b40751a4013000a0313400c00c0204540d0355502209031600c00f03001c4020100c0174582ca4409a4131403089061840c40d641c070000d44124004050303403100030310040544040c0c10030720b46040050304445c901c0d07a510540d06c0200702030909078074051416500c1e10241d45001c078400096070381e551a032035905882070405608080100400750800e14a5a1404264000021094907141c200a01028058035000d01441503141d02556110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 598965863 1250 598964613 598964627
    0xf1a03060f030d0e0a050108011d0702070b0c0c0a081906020901052b0c050306150912010c08041a010f030f061103010f030507050a060f0f0c02040603121e050d020a 72
    0x3000280c02d8407043e4120041c01464a4200280c0345c1c031900d140b0780041540e52090441c07a0603902040c070303520381402c4092803c03904c0d45002800e03070086200360003022030114100c4010b0704507241000020903aa120810400c9685941500000d27840d5104503a0350a6050105c940d80c8510b680180700142d8484813640125514400c2120612040980c01c205c0e440c030210448201c031618803030710341c1041112039106003140d240c88151842c41d4800740d03400082113080150700013070406034401070001740321a428051040c2074502032141400816034200421051041c4840125018682558180d84030740c10108a403602c4280703800060412411801070504110940d4844160740700601c3c219901ca41e907902c0e24044411041c04100c41c40d004210b000903d070309001e0301c11000e40c2e02585880b202041c1c4800121020000c102d1848104407001d4100000b40e02c5611400c4040d500030001e0103443c00075030502801c0c003445000301d140c4028400c650741c032a0f01c0d809819191040420704015955200c00e4108032060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 598967113 1250 598965863 598965889
    0xb0f25060c0809060f090606040c031401080109050f0c060d0e1005190c0302160201030902150706020a03052a0d0f020c06090c0105040e13020a080d02060901060f1a0306 74
    0x40d5240120791400c0d1034001c82990300c02d18240c41113400565481105d140c0310311059441c00569800440414a280780641100d0030303205440c0b80026507400c0000b51426011402c3c1e01003401c0e40d640b0a0400244102844020b0b0074401650080c2035002d80000454030500c141020700e0221607485590090b4210b042c00381c10179040c4050350502c00b90405606644200c41c2030302c00107481525010403414464040e000785c91168400b4100360710326401680041d400740000c0c0c2d400300e80c45800752030301100a0000c1d002810389140903440c0140c49081c0366801404440000e00f610507003e40042e480102e02c0402c2a040402220700c40070a03440c2c03003004240c6000303041d82403140040140080364107d0b903c0300005219200350120002c0f076405040c0240107650794802c0b4052800da005840c40040d0308400b03400c5403000464401f0702480c1110b42d413002e4440c00c20004012940058100340c4c04e1090070b140034040d81002d811044000a40d0034a44806801d050f5103a0f0848611b0313000120000e8602c0d0341c4c014000082c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 598968363 1250 598967113 598967123
    0x1e1103070e0c0d020c0d1107050406030b0117032206030539270901050109031502030601020312090c0a050108010b220308031f0902040605071e2405010b0f25 69
    0x10501c541000a40009405100070038544600c000c0003500d4500bd000e1181103c0e08080c40d0000c590800b040300b03640c005013005c44d61041c4000c0040002030031b280d50414480c01c8103120900b0015045c10b200030709940b03000d0104002141444881c8240b90140f031024032200005520056000100f201f07060070354080e810740701071500d80380e0602113520840c01502c80240b8400b1556002203a0304e600064074911503901010304164071000283c45400b150740d0055402c10014011a801c0145000305068000f00c1169081c00c10741144500c0000c40c2018550040544002d007401080c0307604125052840740034210f140310144901504400c4c48207907402c41a800303150030000050f541e2500103070303505900340c0020103105002c00e4202c4c0010703508900d00c00d59040c0c0b2280da80d803030314006064590440040e00405402083c3d080494070a0000d2140000c5113004040e05945604400c01c09006800700c0310160b01500081408000344517001c0000b40484500380192454000c100070b90040d010400c1020b0071000340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 598969613 1250 598968363 598968373
    0x120601092402010b03010501030f1704051504060807031103130201140c0706140a021b0103020909250302180d051006140a1415161e1103070e0c0d020c 66
    0xc4940e02028201000e030002c0c00404d940384140743c2292001d05c80900f201c01d025544a0005441940b8017001000e00d94040c3d050a844500103503a034001842021302e01c2000244c00c121b12500121141e610440d203003420803058109442144c164440103140012880300c0c40ca40c3e82c00c41e030040d424a64014003148620b5200d0f495104595599003250040c4004103400d00d1424490245034021140b11902030750181404004d94400400b803440e10b041d506040c99006d11490b040c1d500c4036140207104001c43d010312000c2c140928059400b800c01181d80e4010980100064280c0c40c21015001b060070300305583c1c00c2c085441e5824903505040046481c505a0390038042c0019141142e0184041c40c588101ca03101d48081e6030b481042c0c14007004a941e150081022048112414900300150442044100e0280c1400c190790751040f003144405644004030383e9440f080750003442600e840e003d036a01c00079402403103503a08000070100600d40042804c0c541110010b0150034848040d0103642d0003100d0841110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 598970863 1250 598969613 598969649
    0x1e03061503040c08010e0a03090b1b0307121d1c0f02030a0302060712050403210609020a0804200d0f050a0f0b0604050a0203070c15020702061c0c020c0612060109 71
    0x4042c03c80314401c8003055800d00042080c0007001003441c280c032540c0f580700d0006a9150549481580e0450004100c8421002403030400f1440248024040e41d0f20034084c1656402c1441c41c049c00500403401140e8007004860050700480c3c894200030b00d42c007000a03440700f1061101b850070140c03202a0b103600039018001c14212000b05900001d5440c043d03022a202c00c03480800d444003020856000303c3e40a00018105403480308800345614036900e054407100e41c0419110f40b9803410380260390100c4403d40c000b4411400b04028801c910310a600c041e0301c08040c03031064101c0b86001030a0071100e500040d060a88003001d48040020420001c04455444964a0b90f54003907070a101c035a81108841c414000d41c1070000103240c82c0c01c54400c9034032801c0103803518401c0c1e0041d929400611413144455440045e800c004a001523030780c1c4400b401c0307091a0b41035070101c0d450718064910b0603900044a41001e55000000b0b02c052507803154151107154242c03038200e05180d5540d0340102c61207440b03940000b85200801c0c81e08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 598972113 1250 598970863 598970873
    0x4020408070603060e070f08070e1e040b0307121e05010c110c040c0f0c02190f0f0b070c06111606050c19020619111f111e0306150304 59
    0x141d0308540c00b9403030810981c0c1d5107000b4266184c0c01114030200280b182d006200341c05005081c116001545450700d075401c3e00d40500401c0c00c40c01c1c0302d134040c010506071225290390782c03030320b4028082801c00030b402a0900e03e00d001c45405961003d41c01c01852549241030346401e4a40c0c1c1c0410345106600034000344003805c40440e0280800228494800007805401d043c81d62604260103950102c045035034621a107900612811a000311090504907800b81c480450705000700d1030001400b000d801ca0183d0f0304440e500d020700801d10300050b58821440b030207003030103503501040400b905601110280e04010480035890700950b81410315030101000500c080712000714005a12030060602401800300b103845514400c11241d808410011000754440340401814001c154000c4103440c030080c060500d0f1240c84c4a0261550621091402601800d02c1200c5c521003134905034081c0317481606007000d4252038260f058906601c225860900d0101c01400000819400e0701e800c619481301d920540d240c540c51707003003d00e01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 598973363 1250 598972113 598972123
    0x302030d0e13140f0a14060f01030b060c0715020a080d1a1306050a1409010b0918130c150c02010e0f030a03090311010807020322051c05010509190b040f0204020408 72
    0x2c50840d41078071030014031762900da4440c00503050810010110540d0300c40041054001d2a01c040c2810940c075031a0072000d680320400a00110500040a8a1090300b40781505002c1201700700c04808662003100c0000c0881d04810448251503030f095400b00302411001e20f40310402a0404205da0004511a540240c0445641c4a4801e6032011200202c1c1595203019440099103106542d0f5489031705040100040500701e001090707c035902400c518031400b20812050410b1004035800c605144401e49810b0411040d0380c0c00c18064850811100f100f101c00c2c1704018000306a0180003418031894000c40303207955560880600f10340c070000382150f0441e04541b4000740404d109101c101d0b45181c40030300e541404d40c000e0f255144103603c0c6900441c08e0080d1044242c0180700081c10b5410b99452500c8045a2604d80540960b1028108100740c1c21071000e5103045400c5940040c0600060b810084441c0b12811941101c101d030940c0102ea000703459111401e0064100011106c000c1d40a071000800080078480030070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 598974613 1250 598973363 598973371
    0x1170a0218060a0501050a020d0302070c030206030403090603231f031e050106080109020d080d0b0d12020f010c080c1c060618090606120509030c06040605100503070302030d0e1314 79
    0x54003a050b0f594800040d100790145052190150300f159001c1c40341a032003940a00b000d240030b601000451a9260046030040c1c3c0265000d900007020050248400c58140c080e00b034100480000e00d40b60340070704005042800c08050005403170307a503680c5900940000c01c540c800d4040c41d00104505150810100303000c07803448a01e0800c0303880754284030000448101c103200384c8014940260064100ca01d966442c0d0314681d0042c000001c00e15500c8003100c1d0340c1d4807140010002c2a12945441d4a00c18210030068681280b11122100716070404d14240240e50b0300c001c0540d040059003107440d445040900301c00d00301d11403007208828024909500002e502e035102400c6a2990322014008510f1612030240c41c040c2d404600a100114000c135040c1c06494600d03034001588145201c0c203482c107200340c10112030304005040e5400d603903454540003840307036103e820300030080100001c60003040514a0342c0e010075102c9905600c05e10501000041900050716480c541d001d100d01d90000410040d20310b400e4059034010155 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 598975863 1250 598974613 598974619
    0x3020c0f0124080606040518030d09020f1f030e071d0403140313170d0f1b0f0c022707020601080c010507030c020910090f02191701170a021806 63
    0x114020707400c04022800c203081c3c6019501410f0184c1e140c60071301010b020003522000c4140d010080f0145841820b0004d40250140c0d0140411041114010805500c1003c90072512400401e14203404184c1010390400724102d96007404600e01300503c107030f10705155859000c3d01c0b9010b00c018a070903034010300d42c880620440c0300e519514181c0480b1101d4410600045515003800341d00482900082003080e28013565000c1040b0000307203009050301009003941c05084500001d980c4520103803004031006003443c2c10101c20307454003485141e00c1500050241d02c0341c1c0006400381142d02e1800404120f0340c00c02c0280d024044100415505194900a60356582403054507a540903041050f061581705600300c44030715400d565984801031840d02001018a405031041c80c18454048002a01c4a01d60142644004105100503101c024420385102a812100c8a60040107440c0301c1455452110b0307a106419944425011048d8007202140c1c14035020f070703544009c0d50003003e0341c0141d840e594698440c18030420f025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 598977113 1250 598975863 598975901
    0x90c141603050c0f03041a03040507060e03070f090f0c02010c02030a120b03010c02031909050d12020106050a060215010f381305010323070f0203071709010813020f06070303020c0f01 80
    0x87c800e411a4002a00c0c0280706800c08101000198829042e082080800a0036039180c41c1d90380301c0000c0d25900e0703903001c1e5100645139007500c501c1c000d1034440c4441c0d200342070000380000c02c60002e0085d2644600e0742c210303040c0041c8180c03410351710007941c0c0085501d100280007000914001180655242c0011013450b084403d4140a030b10b1181c4124003500072607034082c082c520341e14542c2e5650121000143e2810701190340e038a400181560310640c54a00401e0b098015280039440c4445020b03040d401600080c404035901c4000300030140e0009901800203002d0f1800c0103840c1050b0b0022002001041c6042040c10400b2519240d03008044020000b1104262000c10108280160134103040c0240b40300da400800c00310000039800ca0107500e5034a404849441524901841ea80d12448669176420000c2c000c4000400c40e40446e5170440803150304100441035940e4044115030002c0e10100b25030000c00c0c020300000c00d80e5800c040c06074054407190800d41d42581c0001101980c1c5500918028008200030808 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 598978363 1250 598977113 598977149
    0x11010c091e050a0b07150519060b0301050a03240204030803010f08150609060a03020603010b0a170c1801140315010e122512030504090c141603050c0f0304 68
    0x180c4000d11086035406081c54810070f03d00380c85503000c2d4000c045e00b40da040324a564801d5001240d803246920072070402102086600c00d01032844100c88082d080300394110300c2003005018075941c00038682d0890340e10003000700a01c80681ea030544c00c500c0b64040c0880f83c6001140120400c03000d074000c0d40c180ca4401105000459592460a560752428015410202e40e1500800d466082140b20f0b15805440905a0402c85650f98045900796100741d010b8403041002259451401c0ea01c201140c4040425800002203400d05220810052040d20080e100e01107014040f404503901901c0a07403201c910b00300b086034076481c298003a442c004c850301010500040d9040b403e2040c900c0c000880211503581000200740c0001461800100b040c03c00280b0081d40c201000009107042c403004151141354420780d03400782c54034071b0003949406460311200b40d1300512040180c01000300000d03c0a8076018015140040c0466256040a403114498220100140d0141e019020745c0e200000004008441e000b00c0c000c3e85c0c183c4d07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 598979613 1250 598978363 598978409
    0x406030f0920030c13020c060106021c0c0501150603020909090106060e09090f0d0215060a03030f050307090314010905160503030301052e0309050f161511010c09 71
    0x80068001441c414499940d002c0c8500c500003841c2503508050116142c0ea409500000c4001c0313540c00700c1c42e03103140d000241c043d00048240b01700341c0100b0460000340070b89406040345041100d2620b40c0d0400308481040c20303d0a00000350008a440721007040e4240c0c401c0d031a0076000f406540005541c4d4050152440442c54540c41485000201c4200c2d5036488480010700003000001c14000e000f03840c0714481c0d4108441556420312a03c1c1a401d4039400501c002c452084200c440408002c090b103100d040420810004643c0016054800600502e0259074941e20500180c4141c1c0c4140c2010b04113242d40482010002c10542c01110f0190003a000c072600035080b82c0c440c800e007810502965400d030300b09000400c000d041850140c15260301d1912042039059149501c00c5a084c610801d0200007510703a9800002e100d8140324148103034058034003034180401c0d80c00500c09a00e441d449501c090f900b02c082800d0949e4070540000402c0d0725044028403800c0c4182c90000d04007101e60140d41100442c2c0c0c10141000740c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 598980863 1250 598979613 598979621
    0x8041502070b090f0d0c0e0f0f1302010e0d05162909190b0c01060f0915031403070b0103060609110a0c03121b0f1202070c15140409020406030f 63
    0x44015070000e01c0c056502e030134000700b800650300c0107400c10080381010000a802060030009440c100390500124030f410024084230440150282182c002c0f65010b200c10486026001407002c0d030282000c0500b02c5a100100b800c0381035048018101e8091000a0000c4018022034a401c40b002141821528181d10381d43d82c3c1001c20000b8481042c002c10000c2c1800c078146a10103049501042401e5070754942d60702c1c1c02d400c1d2544074080d1005140d5403200c023800101013803c0000e01a2400400400520300d40c40310030f4140f03480e5130101130405101d81040c2d10003400b0410450f4030550f4007883c210250350b90307403034507401400e82c90040c180058186000da1941a182c441560b4401d0b00c59991561214429201503888481a0b41c02101483c0c0301d21a000e210001e220410101d11419590419a1811300030003c104251680700390b408a401004136001081d900c019560542c1c030283c4450410780f112800c2039401b100c000c0180d0601941c0400c0028808a10303502034411511182c50078030208194100702e104807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 598982113 1250 598980863 598980869
    0x806040e0f070509510d0b0424020403020f150406080702030405330f040311040f0504050f060708072a020301050126010204270603020901030804150207 67
    0x1d5840580100028602011110340065450003118098400300c00c1451501e22442039100c05902d032801803101c0b03802e07074240403580380100d010900ca00c0c06008000891140071000702420290307a40000ca800e0107682c04001daa92400401001c81c002500c40504002e904144426440b542140404000900704a9481d160040040010a240a041140a80f50310728041c00180440c0300a2002181c0c1e07488001e46100d00c902c1120340d200d0b0081440c0550000400d10704900e4201c10720034003401001980d00c0c0240c1d015280c0c01043c0e070440320034582c0898001c2c42e0402010f808036060000380024020b0104820342c5800342c030010341c0c82079500c09405948040068a800e00094125210705054980c116000c0306076441e8844e101d8081030720f0750002070940e04c0c280c00c007134008980040443c081e0007180d60040c1041c0308800095040c6850b00c40008050403007a8a4214141d44c240c0801305d070514541c1c0208080d560040010304556181d0800f04031035002400b800c11044220901603070210700006628040f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 598983363 1250 598982113 598982143
    0x6200a03020d051318020301180c21020d05010312080f0f0103060504080912061812030f0403090f0e06100203031003080a09090e010504032c01030504150207030806040e 74
    0x88060800440302c44e44080300030001c18079042d4000c00e46912150702d00030108600200545c403541070440e01000610381d4114441b025151064050345039030059685469121201d06070725000184031082e001034410903400652041c03410307001004104a007241c54602c00712a44d500c0d10700d562441c28810000030290740030401400d001c0010000070741950452507005114032013042c1001c03075100c0072039450100281000700d590401d04c100241030029096074040300701c40c1c00c000d000300402c040c040042c40c0b0019140b5100000c0703400020b402c2c98041e00c01d1400400704411000c8101d6590964182403040640b1032500c10404480302510704c910010559001e441c824001900303291071552000ea0390746c8006461410300c20030400c0024084060f2150700d580c000c8160010a1624051030002c0c074458403520001720201102808204414510781d413200300e01400e007000a400e80346c80c10b006541d2a8407207607500010b80009104800c02da400000e07980110310545080c840c1c07000b040441038584a5210203915 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 598984613 1250 598983363 598983373
    0x5030c010b03211803010e0607020c060703120e01060803130f060c20030f1005040c08152202090a020a080a1811060c0115170601050105030c090406050a06200a0302 72
    0xf40c4590a03002803103500945001c480e280810400442d0035130f007907070f03524101582000302041040746c1c06008207000d904003145e2841c0790a41582d409048100d548088690b615520b0140038900a001d604c0300e0f015007504001c503910741c00991100d40003072039180a5034004000c01d400c0040c8a500401e0030400b42544001080005503500b0780b05440c5c41c4122070301f42d501d0721400b801c07007280620030301141e648503841e408041500d00e41414a410301e042d10b540f141c103a9030f020885080035440c5079405036410102242c4041c03020070110b421541c0c1c1054001001e9405224501440917400d0503a0040c1444005c0d078407054116a504c9122904a40040030b04104807c2900341240003d44112440110650b0041c00d04d82010501c201060031205000d507080384030880042d05000944820685248104212004082940c10040002c00b5808050801e5050384408584803040b40da0f00e07000500603080c0071f483c4480e2550380799401040050200c91000d0701d07040395182e500b2005008a0107a44c01901600185 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 598985863 1250 598984613 598984663
    0x2d1d01061d0f0607051f200f032206020f0406021c02061501120204031a151f031b022406100c0c0305060408090a0915051003060e0405030c010b03 64
    0x11255034005481140c0c2e9001c1c601c81c001c03070072030746c04543d44040c1e541040c0094100c0e202000820000070001f0350000c03d503020312400642e0800b000480e90f000740f01d42000c0038019403500210101152800c4001d069a00200d400d99050039030f2001f80c001c0307403226400c80391034075105004400b02416038901c1d03d0041e00000005602c00c811680865075910b01850701410016000d00740400301d800c01c3e0400c070f80a81c1d800542c48102c1c07222401d01a00410905002042d1000740000540340032078803244440c500a002584001590080d80310408101c002d0300c035509001c082c810000e444480110703546035100c419425413600071052010b0580718500150540944016000080e03034856a400d4007115400704043d070100c0012018803c840c052031052030700b2905c0302003140400c080240709801000549203015654024008100c0c1404111b031002d603402120322000c0f42088020b800799800c5050301054078000d000400c4000401410741d6a0500002c00c080e20308602050b444400d440203070040c229000780b1071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 598987113 1250 598985863 598985869
    0xb09061e030f070906050f1c020409060b031c140f0909040816050d1d03100b03190b060a1a030103080c0a06060308030603010b03072d1d01061d0f 64
    0x80490118020112510b00350009a0940b4000c03241e00b003e0440c4d83c40340320400c200d041c02e1004964014044a2160113000b0410040c481c0f200840d001074800d135120a40340007400405da0003d202410041c0507036404060b0070842140d00c245441640d000100c0158002c81d6071703071218041c2c4954100b104e1070030340792060003030412880d04c0d800380041e039410108002e01101c1e0b01c2000087d00310b0354401c01c041c4c00c046c0c0442502421102c4207640400415a03a88100d188a0f40c0118010034620240072001030b0000603000824a019440c0b03201c40c0c1214003612404041c000a5000c50b0b10401c011960000e0540d101d040c1084034000c44001d502000800b03000602c0041d0010b8040d00da240b0040f0200c6000645070345401e0203075840c1d0350055031045000000c1c012641400c0c0a2402c100f0000d0300204011854451030f909400c0300180e1f9403529042880c9151b5031990a0710054000300000503450003070400640c40d486001c107080c410540441ea80210401103038030192001824500010301e500d108400c00c8040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 598988363 1250 598987113 598987159
    0x20d0c090b210c09060a09170a08090919060602150606070b070c05210d0c17010b07050c0603010b0c06070e01300f02040518010b0315010c1709040b0906 67
    0xf420f1800d400348a4200d40351a0341004e802ca800342591032000c0c1c1442d000c0d00803a084a2100350004c2074021186110104400c1d40803990b19010075240b90708aa0340356004000b403407510131040300f0400d043c501d0001d459030303000400c83c0c0c0d07095000c855a101c40e21244104440341c460b01e600104003607001c40010302024025410b6001040c06142a81c40c040c80300c00128030308490440e0020700d052400300b040c5220124901c00c881503600ca1b401c1c00e0703402d40c3c042d55408880000511540038000000a03015041043c18081940b4801d4054901c68407961204609502c640018907031091034495a8005403201d8460103806140c0e2006071224448549507481c2d20700c3c1508244074240140c0c00034981c0c51100c1e2040e00c2004001240f0500068450342840100807094084d00f60444000d00503c0050010360614401ca80c1c10400b22103400281080780c1c80140c1d500d1020314409000403506822190704401030400800310110110740400c403d00b4180108090054142d03030301da800418161003c45071141d0444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 598989613 1250 598988363 598988371
    0x20c180a0c170a0617030a0206010b0d02040504050108060609091c050313210f110601050d1e150b10020c040f0e07171209150a030f020d0c090b21 64
    0x600780c86400d000801d410400c250948060b03405544d0788030304100364850106001c0c420f803101c0020791300d4010880300080d0b8501060040030142140004d100070b584140354100d030018000640284040e603500c0030313060740314501184c1585c06000b82c240018514240070400b0891300e4119641d800c0c0245081608840c56003004145440310800c95070b45201040d150310a806010325200807110190b11503090003454444c42c400c0b41418001b1403c40302c5000b040c0880c42c64190b480984088030001e80c6810725a0310310148140805903c5e03085402030080c41908a0803400c4207000e10000c0c4a2658400e0600c04490450032901e8016080a50101c0c118a095041032803030400c035110118001180c507400904002e40c51380805814002a0100c501500090042c00704d044091f00d2034900f06109000860311403500c001d17946003c5040060078045c0d26019902180360b51076229400c54a4403030b40e005680003040e8920340c10000c11400c01001449900a0003103030a20b0103541000060b10040c00d00001a03200090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 598990863 1250 598989613 598989617
    0x30d0513180b0a030f200d030503040501020f0c06010305010e1504110f060307030c0206010e0103020102120304031205070c1e030e10031b17091903200a03050a020c180a0c 75
    0x80104800380e90b80f56810014500410351001c0300c8400d444c001d20301e6842c807001c1030f0b035580403240713041074075070745e04031084940f50701402d003203641e5610b0740707000381c020b00c80c000c801c0e0004c400209510745031001c000b6034181a80d1143c00200301c52134000d0440307980c13200d001c030f20351f0040389013000024009000400d00500c542800342080054140c010700040c8180c00407a0441d0000399130700d0008400c1a410400c9a0040040381e400c6d9401e541035800003034580035800b4440d850a4000000701e03080500c14540c461300507400000c104000c3c01c4c02400180440c5103800c055400148031404084201c6209a11164696064075001c0112443c2800d00511090305200030040c165910207000c3c20400c65104080b00e1101e6964424100481440392080c109014084c40300d1507018000032003c008030920215280c81d00350600500720a06038010b842e5406114840e8004d600407a206c5604258100d009460090525020b8440030340c0090103102c001004818290868030000021442c407001640c00045c03851014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 598992113 1250 598990863 598990871
    0x30203043201050115030f02040b09150c0f060a0609020c060615070615050307062303100b0c0616030908041403251a090607241505030d051318 63
    0xd07031400340c00c5440981c4003c0082d4094841400711541c10b216200a0081c200411800c03c0d0802c00b0085c201d014044015004000465107112103000c604156189814140201c030b1803498213445a603214402542c0d146440c0d030070000040703403003403140c000d88148100890041000b90380341c0c020805a880f21009450891034200541400300f04036005070306590741c0d000500e003070380f03803404040c145081c0d10755212000304924000f4035500e880c040c4c42022003010791710351295201c0c3c407070040c1d00040d01d20a51011408600005550341d909001148403031184540700f04a41a00d140f1003402e4007942c0c5804030050155008000500000700902d07804461124054100c51045007200104c01802e50b442003240c010703484560041144d1090248800c5004a15624040c00c01c040700010410314041c078070008184403483c445c04051500c00c58090b484100b500081400400d074041451480c4c0d01c801d010300313402401009481450180160100c501c44020200e0307460790b091901c815032200c418441c803110001516 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 598993363 1250 598992113 598992203
    0xf020f0f09130c090213050f040e0a03030203060f09090d03051b0406110c0a081501050609010504270f0b0306060306010b03180124051305090316060f0203070f0f03020304 75
    0xc68405041002c40b06e08042007081d0500342001010070000c00018451414440014401c42010880340785075035260901589035210700e00010038030521020155007000881040111001000903e0800039083d40c13010040e40d1a0710009000c40e01c106045894210410002000040c0c4031344a954001d000070001e55015001d004005445000e155114030b40640c0031178603d07044014044007940c01020b0440e01945400c100c01c00207001e9004d94400c3c0d000744048043c00d8040d07462840c943c5d081540c0c600348100041c0400d0000b000081040d4680c0c00d000f44102000a0b119080010b9000d060b9180c804401f03045035245c18034a95100c0940e000600d0b15500c848003030003c08a00002c9104018410280154181c00c0100381718011004444000d04070341040306000d407905010040750b50381070031000c226280c100107041007400b6181322021001c801d80300000b0041034680c8800513005440d0556108060000300e44030440c2640001d4030050111002007100a04614400d09180070150392003c00c41c0311480 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 598994613 1250 598993363 598993379
    0x15050409090c030210020c0307091d0607030f0b010305091005040309080607080a112802012004050901270c090e0a1a1009140d0803040f020f0f09130c 66
    0x3200d2038084034007910100b01807003180790400000045440ca4401000e024520b8030000e5602c486512071000d11558520701c41024500e8082c0030080c0031440c900322085401c002e11700134001d001c402d25030046280381170b00c000c8240d8401c0c007510740200e45520040c510060b62a200600800e0060411014002d04a00002c1c0d00f1030288800c0d4410f840c43e4441e1005464074585441c240e5180700c03810320703c00d202007100248841039000003030580341e61400c44400414020500b0f80c01040781161201403005000d03840c0c601035403080d0040054500c162011007840c0d82e1442051050320b08100d82448509448260301d02c0c98429a009a660b014146858a41c43d90348484403001c4410555220f01001d40380e0009240350080e03480340c205440d500303543e600381c0341c00c00303410081218515016040d00064816442c0c0c0d0950340d0482d200c602c0b50741090191341e480c181131414004564400b84104c1c0035405001081d101480c0050301a400c0c1100a000303074045036600b103120b14102898500444940180ba407000c50500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 598995863 1250 598994613 598994621
    0x1a06042d140406092a18120c1203080406020304020607020607030305040203071e17070b04170706050316030518011518020f090118180c031503030915050409 69
    0x60303461030069020480303800d02040d1400f0307810074040503041030000702181034808180000c8000b140b002c1802102c09a8040b140b0410f80448000c2c03008120744c0204082070410303e030010152003001e81048103607845804e402811a01000130b004101140300150201d101e64000359070161009144030700d4a10396900007a0581c00c0007100342c0001ea41c503010030045050411042016260004c0c9003401508504914212907006020b612045a519003420144c8101085907101800c82510f106888548845140450303255501d41d140c100d2140d41000503c0f64042d604503801036008800014880103041300c04da002d84000342c1215448080c0c1541102c1040080c8a06401d00c542c41d6124070441c1e10304103840007910313204410403886610402c042404004032008440307115000382041d0040348514500004c401c1220b502c44103142c03040b400401e84032803407540010100c03903407610100920000c00c401e4501c01c403505e0000901281c6240c00900207405c0707443d503890718148240b60151605841c1c0310b502041c2c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 598997113 1250 598995863 598995869
    0x50102030f0612010506150d0b1c050706210e0c040603080a030b1f0309170307020c0111030711090604020c070f0e130317040303020f0a080a1a06042d 66
    0x1802004060010b145007030032109085141000092000e0305200000500301d00741381c6180052603500140700c50020150f030300030910705c0303400070124480c4a090f400404c0c04150181e0b0100c1d00d5005400000c20000d025044580c502507800100c0702046150491a000405407039442c1e028071300c140b105c00802a6200d001d11406580b0601c5c0742521100410400b40c00d6685003034070184075115001545984031864111f0102580305458042041a20390801248925002c205040754031800010018019000121195900d000780d8480707a10804400c060364481c06401001456030190701c1c6420f540c0d00e000074085403c103030000c08c0180380121849125180c04080c0d0f000101480c098882044011044072185a102e01c5074011086211081e58009042701903c44840d815002024040780602d0301c40c0c1d0540386841e0400702c05940e42c240071200500b040404444284515007054050644800c2c01d6500302c050700400342c00c15041c1410300c24016040c5c2286001d0104000010703462403c6006510302007802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 598998363 1250 598997113 598997131
    0xd140118050c01030b0d0b0601110a140d2f031603180b030906010b03071b030e030c011e140f27030601060906030e010f050c0a111c120905010203 64
    0x3200d5460300e5400e001a2081d1681803518001701d10403503450300d030721400082e5400303d00c15216640d8a001030321440480030506600741304071021075041002e1108240190007841c7c0407a01c0308009204100ca41c02238054658400b2201c0d0030669078012034031840301e03d40170806401d0740d0820300c4c161900d05017043d44842c20ba001540c0810301402200080c03c1032001351580690807861841c103141d030b07503076a01c0061044041c0d80360000001900b00b40b085007910403260005420080b00c61150900405d242c00c4500300300d03c203003d002000e49066004e6000e188030052100850803a01707101076416100d4003103d02006445400411015508100881c02450103070001d010100c0f060100e071844510742584100c0030342c040e40c0700c80014440c868010031000110351984c5808100c0542004205024100a09905030806e00303200900405002900252000c000e00340e480d006040704480d00d10f40d40d03800c8503e5800c44040d400744081c40d010700c0749542c036240400307905001c280102181d81c0c0700d08903442140d00c102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 598999613 1250 598998363 598998401
    0xe180705060702042c0a1505070212031012060b0319230f010504081201090606020c060d140403020105061203091c140303070203130e07210e010204030f061d0c0d1401 73
    0x2080001c1200030001f5803040d0041195107020070b400b0756510000c4286214001e0040001084113a5607801e0303402030400600038264101e82c51600380c000c0d02c0320038400f42c42805030141c001c0300889510348211169803c545400e10513002607480141c1800748404419a5000306004054100300900507907004605c41d048040d17813100c110041c60241241038000150181c2424020850641e0004410b82501c10890303207c1d070368140284800004140403000103c441d11018204028150190b026510400301075034000448803035005059201c1c41070049180d0301c09512020f920403c1071404200259510401407080c8080703003600a00e2558104440c11401a0320004407069000c1150210b04010450751202c54400c3c1032680001d85114041e860407510130740031250300c10300200c603a0001b540c8040418021903480380c881c1000401516541000c2d03561600300390419088103039810800c45104041d1010300100d0140e07a0821401440d011400c2d00e08000c14040c803c1e08140038030400011a1508020769 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 599000863 1250 598999613 598999633
    0x80c0a170f0604110a1205570a0b0d090611040905100605120a090c05040c0314061002060106080a0b0405070e0a090b0f060c12040e180705060702042c 66
    0xc446000150060240c84803024080b800140c1e0002e00501300c0007070508c4c10b545022081043c50b58482d4003103044500ba09500240700d0b180c86880c00310f040c001c200c2c41d014000b42459841400000c101038820f849400c0b20410880000c0d9180d41c0c04074240c0e43c0300b0705003c0340c1094180c0c030050313081e04250452a42913aa0302d041c0141200018406e20091145060a5007042914807801c040d00c60014546261651154812070030446840528006042d00074000c002c0d60740d070340d100240141003c0d8030381c001c2c0c00640000705410789811006a103140b80309a000f04242d070708016080720141e0014040d000300945803d200358a542e10f900555100f05419a5607460301480d2004019620b0a1944403280c49460080034a03001d49641018031818202512070740e0f0340b0200d000030140380030700c08120b40e41110390116010404174880341106002d0481a0306200e14005d4582c046a110381181c0b154680c01401044850010b040036000f03c039084a410401d40754010352500d41d8071400100000c1e075945600945070302 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 599002113 1250 599000863 599000869
    0x924060503010504150b032508060a0b0a121a0403030209130e120f040801060807031505090601030f06140a23040f02040203310309080c0a170f060411 66
    0x22500501088009000e98285034540a03a02841019440002034552a4044841c4c40030070011060100799210481c411200b0710035480c20a035580140e4225005200c0882d801005c24040c11f0300b100d87c0100958816072411006401c40070510704100d41201404002604441400810a200e2400f0380c50141c0e40703a07c61307010480c00c08a000e0500c40031324a4088018858100007030303000c080c1400007000300e644a00100281c2d842e401503500c480702c0c540c03e0800204a0036408103000c01107900c201c580c0c0400b12402d202035001e4800890301000f40d0b03440940100045414128034146143c0076000001d4034080450300d990315400c08490000400c0e403640002202445191a15070014281c1d848500040c2007aaa80440c00100e42d44e02900c51600803001c5100c59801e400d40260500c0b4889a081203080b025a0f540ca8128507000203901007580d0400005001c040030580d912189401080e0380740f4682070034448102d40c00c00ac0b200c13456900c1f90180c2ca04d41194104081c50045004e10003441000d07040c2020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 599003363 1250 599002113 599002121
    0x1803030e01121503020f06090306010f030b0c04030302120d0f020304030314090a020303040b25030c0317010501081314031b0106050f01080f130803040b1009020406020d120924 77
    0x8010002d0f860a200420107480c039801e0101526411030701c80891604c81000180039019020209505010700400020f40700710006104003124418403510303c280c1d40da00c8030101107004522010700560007030324528062107030640041c800344041c0302f4006003415611306102d0881c0c004503405c801282d51001c441d600c15250745030880e8490000c00017801131a04d90380c0801e840b405188102a0030027404502c0c0b000301c103041c480982202c080316140322011030050400400c40d454072481a0049900891202540301004400b94141e4006131075101c02c0d038994038030190143e0941182036a0692902c03d034464025010700c002d007403010190b000d18500f100d461000f103003111182e901042c82030800c514040502cac0d0f0041d410766444000440203008942c2c600302c100d0f07007803516100d00506c4960000108420412407001190180c8a14410382e0030b004e485116210032842240140c3d405640701070003032148207100300880401c0400342200814041c107103a5a45002208001c030300e0700400011800c10740b010100340300b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 599004613 1250 599003363 599003387
    0x70e04080a120c0e0103150e0408040e060109050904150e060c0c100911130f06150810030503300115080703063218070e15191803030e01 60
    0x801000710151096004e001d8000040620341810b44418000f8400e080c0c9504000c014003000d00521742d240741c285041c2115510074001c031a0304000920100e883c0b035104403022801d441026010300303125140c50300c590680c407200d40041c1515940301e962800b55158184009401803203906520354403040c00002450a015a106004528901d80031212020130b16441d0030003100301042d144801c0320b0f8080b42d000c80280c002031620640c124189040018002d403048515504034080307030b44515403600c0700781c60018145c0140c4400362495009100300010440c41d16017003171100003d60305150511048a50304d021601d02640818406140c41c103600001e039400440702907001d000e91600300301a90030320002c08101068003103030f182580c00b856a0000240031203450f400400d00d000b0700040000321404040d02032242c0844081300040d10a800d402c0e80380c201030410030503d8901c0c500403400c100740303002415003c40160003e0820061410031070591200c080c1c0c44d00002c0c5002e5910b443e80c9542c40c000240070707803104030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 599005863 1250 599004613 599004647
    0xa0f15030e190f0602040f0f0e060108010b0c07172b320723010e03090d0c050a0902040e15030312040206040b04090506030d0201020a05160203070e04080a 68
    0x400700c011420004030300c55010001001c03200000242d00d080031000385030b190301c00601c041d20008001c1b0300d00f01000710132812900450b1203090740c262903180300e105d0400191207150215000e100180102600c10f4045c04c0c0b44403601c011900340d00d5036a0800240d8110305003513100c060b04062102511180404001c5001400c80d41c070340d184503840c1c001d00a00c0301c900f00e114505402894220070042c006004407455100b0703150503a10f0745a142a051201000e0911251060701e94503018006102203010300071480c00303440c0e41001e1400d04041c5001e0145c404285001100ca8500b1000302240941c0c90700ca07440003500002800603142e03030410000482c4054094088200c120011080362010381e0004225950103c1055915000361034501c042000c9000d184c109403288000801d000c070368035100343e02961246804604580c01c502d01180103a00303e1240340c03001c01c0010410440c0d80035003a125140321301d40a1018003201d5440350341c0c40c04964003103000e4904680940340040d000e0344056003c04c0210320907640f2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 599007113 1250 599005863 599005871
    0x203010f0e0a1403041d15010201050c041703040b07050a0c0609030c03030507060e1e010f1125021806091b0d0c031d06040510060b0f180a0f1503 64
    0x8889a50b96030400000300925540301d24600040740c0c60103106960080040008107131001803804110001c06a007114011130074101c14216490640c814040d15001d10403110056251608000c140c0c2c110350003c480600c000c1c8000c100c0002d103c19008018030f00c3e10b0045c000f502e20280c2c3c505d44410300c00d50560040080000404050012500c803100390070071280c4c5801c107641c1d00c80941c03804501910390342c14136204034050203110290300c0f620948442d502e0659913000f000203028007076082045840c83c80c540c145114042c0b102e0300048a075400c40e000f02c001c800d42025440c5025a00041c2104051380742502000000000d00109082000356250031a08489800701e044450106400c1240144041182d8540d140c110840a1902076071020040802d05d0002a40e012024907260b0f82e101416501100c6a21489955034500700e5144214801d481c0c10460561070700a100c91a040190011800c0c2c80ca41c94070190207510700d90b1020044002802d02c10b141d28921442c0100394041d2041e1118158141820 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 599008363 1250 599007113 599007131
    0xc090212070c021216170304081e030c06010b04030c05030318010f030b090a050403020601050910090507270806090a05032502100305060906041112041104180203010f 73
    0x11040415501900030702d044050458140006480410710000c21180d600030319080c0d001205440c0007240644481528034091451854034440ea02e118074400c80f640c0e80c00004500305200b00000f440c2c00414206030489041002d41c141240c2420b20a82c031180100703d001404004200203031491000505007100558105010004001500f05010040504000d514107201c041d060081d4045110228090801c8506e45002c589079001414180c03820740143c032450000250720315000000c40d214080c9000703901000b500d002d09107006014003401c1c00003070110781210032800040380c100000c54000c1c440602204240340c040e030355041607030180c80a10107070040700001c23001c00d100004407508083c841012000026006d20340303650f403040003000207502100903050505030650542041e0b01450045400c0f0006071101001c00c0104c8a81c54100203c40030103100c6aa80701d443c3ea42210b82c468007039142040d40112031400079046912a040709040d03040d500c40003030f05506017481021240c01001710304203c00710f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 599009613 1250 599008363 599008387
    0xc2d0308030a0e0f03160507050906130c030b1507060c03020a0516020604080d0504090c020307020a0608090f0115230612041406040317071806110a021002010501030c0902 75
    0x20006001c404502e0711015a0303d850780c0d080290042c0aa110300a4940351a0106070502e4061071807030091794a0320507040f0101d80c502c0c0540516008580c001c040d0f0150301340058060010741801250002819917070302192103e5285c609202d011802414081e079691080c61a1410899540c8980d00c8100361051084a4140d90031004a4901300e4114415071601407142c070002e1540c1c4541d0704094060300a01242c0012a5007090140041d900c0b005018031583d50140300881c0d032806120390207988121121020083e80d03002c0c00180d50465100000e13207101001c103810350390035204010443d0105030118281040380001e00e00320001000300c4829407400e440a000002042070203081e4010030607201c0c4c000400c080002600901107100502c13001c1d50501e1510341400b0f03040b00707406400010350101120000e10800d210701d43c84c40780c41c200f080b102501942003000890700100c01d000220a1880703882018005a81e41c0c1031008082c65190780040349940c110300d05494401802d5203c0c05015005116a400e415 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 599010863 1250 599009613 599009617
    0x11e0b040506070204110708070b150904031b050a0302030c0c1905100207170601050a0905070c032102040b0301150c0c0e070c060903080708150915010504030c2d0308 73
    0x18000b200c4154540070f1134000100204003104500605200001b40e4038204040d40c0c0c041c1c80450b001c0c0c49440c40a03994280140a00c82942c0f00ca00c0c0d11070456400940000c0c0926501d52585503d40f40750382c01d4001c243d885914100085000360091390000c101d600c0c2a40040209440402c000e5500c5200015003101d401b85d08080d40c00f40d50304c11401c0740014545c0f6031003000450004c10801ca0701000c00e2019869090300ca84082c02500c0c025458048003155690b980e01445004807259550155540c40540f001c452018201044a50b5494440e000e544c50010381c1c009000070b8034803001031560300d51401907411100d20904ca40c40c0107028160414601281690b0100c2003200c80b0346950800e1503481d854200d441000040c1c00810140c60700c00f03a9001d05901c0310300584244c1a41d01c1e10742c010b80760314280304105252039940540c45000e000c0010400082820703503b0038074006041c1a402c0079100d40e46e0345403a00c616001007241c0e84094080412042740d103103503076480743e05004001d03c42ca421516542464 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 599012113 1250 599010863 599010869
    0x5070c11041e1127011b0b0a1104080a0822080a03120615020307020108180a02120307060903020a1a07050f03090a02120307020a0b0f07021c0c0608011e0b04 69
    0x2c560f039503452410b03260b40310040380c00070680001d40c00b0b40d00c002c0380480c600c0505010b090500003642100700c491a0205c1440900d102a000b400442c6e00d5a00e401c0c0c8080940580340880010b41d50500c00092030b410104003029080380f01e4130302c1c0c0343c031403007010600d0020888504465081e00e607503032001c01c0030810110b20301d4555509440e00303010f080520106000034002c15480f02900c44004092400c13650f0b0301102500c01d09100b42c0e29402603803142c2c1400e1b00e844072548105407464004004860052a00700c84540c20500d0003400e907801e201030740d1140e4046034454007003540560000005002001800d040144e18501311140300d110900b00024003c01130300400810800c0004004081402900104112080164010040d01c11001c281031000e460781c010f041d08a00078500d00e40e000c2068049074050340d800040108906003000c16903020084424007604d030182e0302824003074944000c204903190300405800f180d228081b9551421740a45410b000215491482e00c0040b90203200e4040b400e8211021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 599013363 1250 599012113 599012171
    0x3080910090e040602041805040203030d0c03230709170a17070609061506090b030c0f041814090c1008092407180e010509100905070c1104 61
    0x4118103450949650007150468528001c82c10104401c00405030001e00590f45e02600d46200b10001c01e0f104006e840040e20007c1d40350b00305000c0000601025481303402803560f035140100e004065414524030000b0000ca800f81e170541080304210600383c200d00254001d241030f203041404032140350080e90703d03800c0304600201094002d11511031806000350582e03199940080b400c12158100b803070044000c4c82c0a81ea04120708030202000a5141d0040340020100c600c0718540320f107580d81d451070141c0380e5440403e0b2181c3d000020f000115030035000b8441046001d8251800080805101d2141320950030b00820b000703c240c6c092140317200c0685444e401f1640c10703c40360609207045d44402031220f0808580c030a10300303241f4280400c00c0305130312030040c070742d41c040c15040d02c1d18040e0f100085480070100c0c1e114010301c61861071081c01046942000000c541e4403d41500d2441e8a4a40301e02034241524025a800030001e00010b042d1030510201c0c1c20706010b022000c6a04210200303003131000049140640c80d501130 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 599014613 1250 599013363 599013379
    0x50a081506070203060a06080c12250b0a030905070b0403151d1b0f0301051b030a06120302061905070905091003050607050a02011a0a030807030e030d050c16030809 72
    0xc2507140c2400781c0c0c04555000b0141e4449240c03040c441d6008140520554415108207044039000d03050001655080203900b0004d0076040d0621681040c111170b500201010f0392000c044000b1384842c03d4409840f0030401030f50003042a204c41e0a1a900d041d0081e0403280540c0340070081000050864560001840039038500441d0140b21585441005143c26070f0070000f0b80074078817070b090b00b50888200034000031100304c41d60095020760f50240760072624103c942040030302140007150034540c2240017940d0f200070121340125426031603548070500d49081d583e0803400f583c01041400b58103000b038116146003051580702080302d89485207005190550b44d1280780e001d000440301103050303c0c00d20300000000e140c0040c2110b85134188008010f005a201c1502a0b005501c0c24005900482240440010585004281d125010300b9504d0302e60706640301c0c2c0c070101d00740000ca030900d030400d0703d0a110042013006507407141d6807121051000113050141245174241542c40044081c23001405180c181c541101c801c0c0d40c140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 599015863 1250 599014613 599014651
    0x8060d020d150b0306150d03140409060503010e010209091803070510060e1501080c1c0203040c0302090c0c0c01050306061309020301050a050102030c1b2704140a0b0414100e01020a02070501050a08 86
    0x521544e240b0082703c1c25013a000039020551405c2901300904442c0258020043d914034003210608074010140f400340d1000d402004240501c02d00100c41d011400210162498926580e440b40d29042104000b10311060f294801003145020602506500c150a00880c1002c0095040000c3c41b1f085c0c01010b80d0343c4a000854406100224102c1c17040300000c0d070000440d520b0406040030b21200c50360344812445180320b007000914400451050343c0c3d5112807180140f80710401e1000560b100d81005144030340000050003017050504161030001e008281c05000141e0301e50414040c0141c41e1845e410040c1594400c02c00121591000114990000e1140a0816105070b503040043c100d40c1a54010b244840d546050107a5030801c50032906002c0d5116a41e19001d002c203688900380c0b41c0c3e5007107501410240c010000140800c021801d5510b00311088402d40c0c0721084e0702e00410080b130b801090030201d103071b50200c2c00c4201d9540410042014201c2401d0403420203107587c50040c19841c0c010840c0074610076000e008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 599017113 1250 599015863 599015867
    0x1109010b0a090e0a06030c080307060c0c08041412011406100507050712030e0a060513090515090604020d06031a071404030609020d0b0109150e1608060d020d150b0306150d03 76
    0x3140655804002c1d0200c048c0ea0384841c0d541ca801250080d03074100d180000c0e1001103070044100ca20b1007030748152030508180c500040f904d01034030140d0a80750494507030740c60f03030441c902c003032291081100d00000400707100d00b03041083c8524480c29407201c005211042100401040c3d00080e02801c4038800181d0440c0c0101d00c0c581120341c0d00e00200385030382060750315030085003554220f0082c103070b500c00c0c24900090440d502d1441070261001a1841e51050903540407901d603070f00b41140764981c40310000c1c0000d07181c0000f42c00d18000300c2d481a44183c407055907926420441803849074080e50400b8551600040001650704030014034403e501c001410b560b9251000e004544490b0040c640d100d4224007190019070b500c00c010400390041d01c040107001070980c00045012841402240e000c0e00201e00034414410781220b05851082c0064400e9034041c4516500e40010b83d2000340a0030b41e10700c5410701820300142d00340d81e1820389140c0b598251007608407a00f0840c0c604070b082404a0014000ca901400041280c181 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 599018363 1250 599017113 599017121
    0x801020a12091e1212060605041202120d050901120203100509090703080f0306030c011701140406030c09020720060d0c0e040e070f050d08041514071109010b0a090e0a 73
    0x2104200154018980140116200b0403800010584c171340202c0d110608141508071401c41c01000c0c08118144402e019941c003601e5107214507880070300b1002c01c80800c12600c51615410b0310f900f01c00984001804003255134001c552002c0d1403035542c825425800d201c03d10b000045000e01400d401801d1001c0003c1c0340034820007030079000b1500202e80c1682d455803500c004031541d104591490107031081d0742c082d004a51258203050f140000b649a03924140c0d00744084803401100f6181180c2d031040d1504008004910000d80000013007826250060b41c2d201a440c0c00410203070510310398810001040780000c0310f41c0340d001c12110480181000010b00c1048580c0a540c0050344002180c1c00c46d15120a03174903141400103061040c2c030504000301c500355640d4400c20211074804600202a040c0900c03040044c4060400b490802c01410f081c8000959900c1c041e013049034001007000c4c3c45615240d17401e040703242130250b0300d180917107612007150b860b108110802038100b203150300c03444886084002c0001e01c10002540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 599019613 1250 599018363 599018393
    0x907170a0b09100212100e1b090d060513020117070f080709030b04050f010e010209010c110109031e021305041109091905030d06060915030207021c0b07090801020a1209 74
    0x40840d21102a06400361207005c0c00c0b0b60701e03041254104000f080000c401d168003440340034a4000d0600c1600c186078013088a070810203502d908a10710b0b601d29400510700e0300506224403485484109150740341d0000610007103003000c1a007500000c039020300100d11741c008034049440d403a5041003c156280c4400480d49145143e2014240510000510041040106110310200c16120081c881c0742d1740305041500700d204500610b170208603400003803000105503066035594038505050624580d40d0300c4e2a90301c4050b000344d031103030f0361540c14000345411460a44030b41e21540141c072601b00528900707561800c50ba41c03814401d1300e00c01c0340380b00002582c144041280b0882540b0030310303004501140e0b41c5031036592034119042429099050210126460388599107040444400c2c13025040c801516150075002507214020907a0800e81e80144540300c2107001c440c840c2114414030180440f81380c0824010070030f014940001200d0707401008040380640c0c6c084860b527058802020b0000303d90040d450102c0d00142401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 599020863 1250 599019613 599019643
    0x60a0902040314011104260106030c0e0a060605041206051807121a070e0d1502030c0a180e0a0b03150c0403030908030304031e051b060907170a0b09 65
    0x703004002c112100c0310400442d22004024440c425804800d041540518022429558800c2c5900484840704074040044070241200000e0403640302d44681d0101541c0342c00801d0b0689a18080c4840d068940c800c0c82c00418451400d00d0403d400e00c8000004941c410300040c160945880211760000641488140410840012107507151307503a240b502c201030301008042e9041a5201c8010080364400d034a0180300304000da0b100075030500100c082100b0f0111030709064a034008861503003114071403180700850050301d0301043e50780c45901d00312000b00a080448040031140c403d01400704051286104500d0700184030178000b24041c01c02e4000309103800001d04e40c03040e65420784024070045550440090003a24041d40e200380d000c944404403283d691005840040000b10008405c0d0340360035840d074442c403600301d40d4036040e80792456800202005141c4c44c0380201d8641c0043c030070f1090240081107040c0c010000068007216660118096a4445002e00c0c0e000e80082c110200050001e41c06019126440200c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 599022113 1250 599020863 599020867
    0x210b0c0306060d0903090501030b0409020904020607080d0e100c02010c0c060e0c0a0e090c0603010e040305090f06070c0905090c010507060c030617030903060112110103150f080312100803030a0203060a0902 90
    0x5e00303001701445071034480c15000c207203080701400144c2064001c1ea482d15401400800268a5690070710441c0d620a02054644410510604000d00f21601a5008003090344009102c1a030040400304220792800c2c0c0b0040c08d5a2404020040c140d4202c40000d0103140c001d807001402c1d0404103191418007070201d4940f0740c40b0000b020003150128601d150103000b0507040d022211141502c0003400050b100038040c680380c00000030000307000240b19034018020200081c1903c1a000f00980c00700c0d0f140d030031000742140c1c646828035090015440f03600c079035a40a5030020081011003680c20000c2c2162242060291040e6100c2682c5541280260020402402c1c2040c00b0185074020300384807034507600b1485c2124401d000e52400000c00400090400720000e07001300d9540e85682c170f14001500100b12110130040420942c1c00d00141c00c28a0b42c032642c00030030805005d1695076800c2e600101d1300c410000c00e82d80b011302c1008001d00c6501c0b40001960b6000e1035090005a0b130343c40e1a00028254050350380000304481c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 599023363 1250 599022113 599022131
    0x1406120102041a031e0915090a150e010b0121020c010e060112030201050702060c0f0711100c0b13170309071e03060b0109050f041d0d020106210b0c0306060d 69
    0x18103c000e52003610102e070b414084844005048441040c25280c0100c141d000200c03100c998100a058140c000b50244100c41140080b0764440002c52074070526004500e50740c100384603181c81c0070f00940044010034680440c1c1c91b1004054084040c5003140ca001c00b055000c54505030240d0254401d02880e891402203510f00c0d84c1d00c1d80721714131070003008008600550034030011508550001569034000e501c0c2d502a07508251413950515090341110000f501c81c0300711030110060544514141e0b00246605560b0894240401e050101a1740c81c05040000c50722611180c607004146020a8500c0c05140245420b540352100d070000ca00c1d290864000c0301115106000114082060101407003c403441480240001c0ca00c020041d2885003040c4980740e00140a04240d01c4d80340f038642d024400c00030b940c0903e8413614440d200c05903e07141c0116048005030307549240c103001006d07510162000c0108129010442040c1940c0c0312049000080e0031111409000f20220301d00f40d40e04030a4900b0002000420400024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 599024613 1250 599023363 599023409
    0x7050304051e0a240c03120501140a0e0f130c0e240603240d080304050307140d09060c170307020c0f0a3506090d080703140612010204 59
    0x34080750795922a00008400003851a0102d0020725541c101481304102c0128501068884002180045040120408500701400d0351403058501030701c40b144080744003200c088284411699960002c10002d8149404c010301071100302d41d025032003d09001d4545007000703940782690814801e5000307075100941da100ac2024880d0986042d001c1410880341c2c0b0300a10348d01c1e40c00e10001e440107555600329001011441b00d4403040902d0103200300381029219819005580e140c1030459041035804031103642000a480c81400145c90320103501100c070401070001c440070307914083e181d059684903242c14016008c0c41c5409006018910056061980805075903074a0302007002134a40c00c00c051414810701d440d841854080c00c00d200110180d41e6400b8002c154485907020956000d02d0000c001518a191240e81401944052095500800d5128010030700c03440445000341080314002c000310100f600d440c03644c404c43c89601899903000f100030f0f25410b00a4841d000c0700383c06031196410540a000081a200c2c105c50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 599025863 1250 599024613 599024659
    0x803070f021e03030a030510050f1008070e04060303090f05040507090311130c11070e1311031009210302030f060105071a10030201020708030408030a0807030e1203150301060b030a020705030405 85
    0x2301c028048141a5038440c4104242c1c20300e5000d5198000300c184014441050007a001160021203a00300307202031b000407400181c10380b4402d42046000038200d0b10100046130301c2400fa01e01900048800740007526200300000e18115562001034440641d10300105c510f42c42e415180100d20a4005042c0700d440405903014001034000700c910840d9125040c000508448901142e0b0701410076108202192030481d01d40900c154542c05815505004a003a000a818411710492a246100715914980c07929442d01140c0a80d06210030300040c1801041007103501c020200c00168000000d091407038580c4810b00381301304190620b48440c9898191a010311800914202c3d9a40072030340f003603003268156500d0f80c8240d91240030314460200550300070710030102d0440c000e01c00c16920000914000440d8412800c8061800010000c040b4500100000344020b1289890030440603210580c0244a01c51920300d00c0c00040c4002003520304c00d681d012400c1810801c0030320417a00180801030141498181111a2040503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 599027113 1250 599025863 599025871
    0x31216030609090c15091401030b0307081009050d02030306010e011b060f06090b1807080603100501180b030c0d0b270708061608071209051608070803070f021e03030a0305 75
    0x4801c16852401d17107072090074098180c0e50ba40c100c001444082c0c000540150a004d40010b07070500130040003168154040000b5080c1111165002c46c0600540c141a814030342c41c0b00d4140b007103400070000c000540c0d03080600303020004428a403802c1d1011181590102d0040400001030106040010b001441c5201e5040394083d15004601040071002d9a0104801c01500c1d0f10381e5035510303888100040d500d80c0100ca0345c1e81c0c445070141c01d4400d4900b80d840c60b6021190241c001c600c13454660700350b000c0b024855129103910b088055000f1f1080a22020004200005060001745031090380383c0000c1e03036840030100002000e0714421442407003a00d10310303180391505401d0080c1c581501c55240041e80c0d4401004500e0003a110031340340c039a003544039407100312402d18411209049c0b054442030800e000031010410220342400074001c3c1c0c40c0d0141000c01d05403d00b03d5070762205030503038030500511011420f000e00d410031031941140c40913140da1900d902e4040c3ca46a40b9000c540c1404041203a41910750960429407203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 599028363 1250 599027113 599027129
    0x405010c020f1906050604020903060403090e16021506040e0a0503030a05100302060313050a020901060e10091a03060f030304150909050415090c150507020111031216030609090c 78
    0x8072070304203441503900c41449510f8084007140007100000f050055005a4102801034005881c5c4180040401e00d0070340156030844c0080d2030200104140380c103905d000398004150100402801258000c001c1d940d411241d0310b80060010700c000300d0b8443d41d903603005c04080700c094410b54092000703500300151640c00484140a0a0b820b0800243c01e45248464000550741c1c0241514195100d40c072145000f0b4140740000ca510b4454903401d0700c00341c5da805030514000c00407541c58841c462060802d002e045401c2450b043c0c1803100350a420702001450421010f4202010111141c413560780d100000c58540c1d03020220394150000160110b20b12850045030303004540d403a2200300d1103560b2080044110b07442150701800b15103c48100c2c8001c421150403180311a8040c00d840020140c90380818807010b6588810304003c01c2001484208558000384202c0601200002541c105118000c84240044008000c81c002112408243c0c0c6443d00a0784994080e05020b00e0400c107403101864200300050241c000c40701 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 599029613 1250 599028363 599028373
    0x1609020a0314010302030a0308100b0d09031715040e0c1509010912030801060e010c1209080f0109050604020d02010c14010504060b04020c070b0c01060522060f1215140405010c02 78
    0x107a0b2014000214100e940c0600107207401d000b5500c080f142c4c03803c0030f080c40c1c8000c0041007000900c084500080c09280070500c10001e1445440e242c007402c40c0f0f80c654141c542d1030494404100c0700c400c0c2100c0091440506480c08a007140e4980013150400901c4100b06a000416520300c4030f461520390080e0a1600c0281ca60b0355066450340401c24202c44c0d03600005000400e840c00500c540e41c403480c1050b0030784070181803141050001e545e6111000e6484000e8000150341c00d041000b952000700300c2c18850318038500c0200424041502d44a0711002d0060010340281019600300d02164400d00003030040c6908410710a80c102c100c2000369001e02019282a00c0c058204041d141c2249845d00c01c89900360791001c010400145803150a403401e400c03140480000e95603070080001d55466242e04641d00e903004001040c2c07020403048604084403d96000700d502a03030181c1c0c050218622442d900009a40c1045803140654141c0c0991030140010380c01104c60400003401b4402080320540201c40290540e8095074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 599030863 1250 599029613 599029631
    0x912070608070903150f09080c010c030c0c0f060b01020f070e010312090815190908030105041a180619080312070201051014062a060a02030402150c1609020a03 70
    0x94254140340005003450540346031650303c0c80c15950100030b646d4201d00c00480c04000d2501c5071991904400341040046c0d446041d100e0155a01d880303040d264051a0402d030b0168034186d25a0303542040078183c0100615690b03000140c841e0b00811840c402090301c2c004031b511043d120588014461070a2100b1549898400d890001c240e0240010a00f80c0301010010510b00403106000e511103903000d0011000000030350700070b20070a141800f600c22000d020f0f2880c01c2d52540751005100c1151501aa81000d0420024010900ea9034003c048940ca600105000e031068484130000b942c59030701440042ca00720b40352500091440000b00180100307144400905500307550b80c00081c2c0c281c40c000c544183c050384403044103020340480700b11400307071800e0050851401c00c200403180b04401c2103105e04080448808041004061a042084035030110355181c00350b04504181e07010815180c500d81c0d84007021740e13000c03e40307050301e40c810407003018140311b0741c0c0d48051402c0c0d8032290f0b10002d41c400d002090001e030500800f0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 599032113 1250 599030863 599030867
    0xc0f0c0b0a0201052409060d080d15050d08040303050a030608060709090b12120a03090b0709180e0309130b0406060315050306010e011e0f08031305090402150f091207060807 76
    0x1780349420b0005001012103100c0c0c000f0020a0880248900c3c0d0101320403d01a010403040d130080e20a03800100000500d18007a010351408400d0940c3c0030600c00e035080a40140040d40c0c41003a102100e5050911a4a504040c034007038020b41000d42001070180702d26020400580c0c0d1211107002100c020300000c02c1121000803d2140c428140c141040280d400641d0700310703802c1c401c0781c001c20320402d0501d0006403106580e074880c00340400c250349550000300f2202d002e1000600000c01004d4098a00070308000344142e0010340d075244c0c0542c07809584605500e0380c1d080ca00c60601e402030703081c901008000b00002501c40724090010420025070305034881c0761a0002c90941000611541662071003095500181e1a00c03844059103c0340c425000500c006840d00010151404045000a400e51034080e40e101c884003240d90403000c4450340501d100340d942006110150321a015103001d10300d0300004070742e901c000e00d2414103164422134006541000901000410109010070b0200c11381d40203a8407034003170b41c4500e901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 599033363 1250 599032113 599032141
    0x102071403031e0f16350904151202090610020d1d03030a03050406061202010813020616080301080105251404081906060801021c0504020316080d0f09060905010c0f0c0b0a020105 78
    0xc0c90324284141c02e1700311240c6d42034000d0444d541005001180d0f80e414080109001320745540090b440c41a0141000114034020410590244041c0c40119401c0d04150000799030702c007000f00c0038052080038400403000d0728240704030321a07811014084030340e076481d4294020b0040000b1503060381d02a10f00b60000c9170428081d04414200b5405a480c85400d48401c84643c05c0d210101004981c080c0c2d04110800d400c4001b200c04c10a444c0c040c0749541e4032981350001c054203440c402000b0034030084248114510f20394440140b141c1c0840e0070301d001c45980d85000045c2038a8403403904481000e110714000e880c00d4400e20001500d250740310340f4061081070350f15a9014240e000e81903000004202c50a0174002e2100154803090307205000a00302d40110323001c841140c90404a5810582583d045040480065a00407036401516409450015003207494100c0c0140301038600d000d403170f04100070102c01c142808a000740300d28406410194000003256205024070b000c1d800f14200d08095401c00300060180b49028107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 599034613 1250 599033363 599033423
    0x5060a0b0a3b0103020f0706060b0307020f010b150903420106020d11100c120b0a03080d1d1606090b03040c050d060f050a02090102071403031e0f16 65
    0xb00e0045024040c0300540280d040b500094200c0c0d00c0520090300440c4003406460f0090405004c003e6481c00e01c2c0b54028141001007010032026810850140c3d201d40710703201809215803054000d9526218410300083c10032580e80d1000f000000d03541130212851040000310110320f010310300719080041c0c0140e5541003050003445010090703000070350a02e03502c501a5a0001400d0015000d860340c44004848450031102c46d424403600140d51011600f0380c10006208110302c00c84201c0d8142207a13851a502e041207441010301414003641c540f006000750749807101210034021035680c1a194200106c4078400491342c5e4502c40d200020364841c0c0006003180000301240d0043c1d40244241c1049414501801001100c00c10101ea030307540d41d440312071550b04962040301c1c01404610307801340ea244614000245072503110340098842e410034940203040343d50001304841903c2c0d41c000d0491081e03800180710880d98080e00c2c0c850915100001000d0120700075048094480394401d014042586444005803600c40e92504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 599035863 1250 599034613 599034707
    0x6051e10050409050316050105060f030c0d02010f020102132c0c0313020f1804051608061602010b10090f09020a020a14010b0a03060b090906040f0605060a0b0a 70
    0x15424007190a090f00820038aa001384112482c210042d041c0e494290704c040d1003900c03240d64801c24040f591910941100a100007200100810008400041e1b024010620000c0c148840c0004c035050b00b84c001e405440742c4150006854070301e26503480840543d24984a00c00061204030309802d0784130084848004e01820441014504654071a565580708508005050340c0c04040c0c445010800e42d142d00c0380f0a075007100105040903e041034940729207408500c24003205e0038409500d00748100e50740000e400303521a9040390b110108005440099006113180020150004140020b0040382504661074000316800f4940d44030125075980309003c128091034448200507001003041c1000f044413000403007100320400c0300009180071341800041003583c1c0ca0340101c0384a40c0720024042c2a10340340003142c0d4040d020402428440c6020307511008024000d01c8014103d6a9920120b0070b9a201d2120807800fa202d03001c1980c0c0d60782039100f00a851859043e000e04142603aa841d20604200e0030401441044a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 599037113 1250 599035863 599035891
    0xd05010f051e0f1b03150a06050c10020d0e07121407050109120606170f1605010813030509030a03081f03020a0b09190b072303040302120c03070306051e 67
    0x103401100d043c003c020301810180035a0421030316109400d9801140110506840b0404040040c400d0004440352a0710907000e01c5014090190280b001041d507401921a003a001a52030315040d030000d00510b041e08040066101c1c03031001040c5c0340d51200a01c0c4581303008200780c070103407044c40703101c159a17007004c1c00303000d0000e40d145104010701d0498140508406214600104185440308025407422508403400481540599828001c1140c28000c202510001c80c140ba00c00c0350030b010018242d600050880c2c051400c040b02181c09162007141600c0300700400609840b84042c0c5810010080c02080e02c0c00303079148040e402004908202c401d41c0c50f0850350302500410916103402c0c50740d01140c12441c0311581200c1a40d00c0207890352000d01c090009820f040b0f009544691460034602a4004602c198a00051308200310029038440007040e90701300d0383c1c1210064282c140d02002541070180040d40076800d4454544048100311140c2c210394801c0954419000000180303d40814100400340d40c00c0b9814898 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 599038363 1250 599037113 599037121
    0x4080705090402010c050f030a1d0f01230a0801030b0c03071d0102071a03180f07030807080706140403030b010302070206070f050703050f06060a0b040509070c060b0d05010f051e 78
    0x40300072040c0e0b0180c01414400924981030f202c0318180000d441d051100d68000184103090aa04115640d0421f19004041c0d03039087d000d1381c00b05403007441204e0160f0510102e0b0924480544214602c10000c2c10b25402c0306459030362504010300501c0c000c0c08129220288040007400c0302d0100010350b403103040c40b556075000e0080344288420030720340d22900103811401980c10100d03091031024a41384000314400300c0d160340d074501041050795081510076891410b8100074001c0d00036402c00695a02525000201c040d80d074482c0e450700c02e41c603116507100144180e04080076071013000b0300381c925540704070300a44060141c4078070040118101d119000000354032207000e120400104614a003c0c2024502c0b07541110307011a100e465082c50905459981d09880d0301c00c4080007ca400c007100d9110081c600e41361854145810b05000841c4200010084002c00510b4041e41c41803004542160384880344c003400c6001181b22900705940030382003050403c02000e007401e001c5001400c6070b0f210380ca200440303103400403600d4031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 599039613 1250 599038363 599038369
    0x20712030e03190507050d0f230d0903050d0609111c060806250c0f260a0306030501050f090606090c0c030a0f0224011728020a0b04080705 61
    0xc00e185401d2000c2c4402d00000300307524410960801c4403201e80d100c1c6910384040346070041c6400440b426000c2085031242a03243e103581c100c082e04000d6510400c2d103a44690403414103c0490190986010003075040038002d60605421000602d501c0b100c1e207405200050302c0e80c00080c20344a080c400b002201004101900c010180d090910b654000441c1010410a690b40381583c90500700340c8040301a0b00d80d8240720000881c01c0070b0741c0d110741c0c03c8070305101e0f9200c0095200c00304140702cbc440b80070707107211044a03250300198a91040008007400410086895881000c0300400814003404201c48541c41d00c00071034030080b62006030394442d044103c01442d0961300c1905001710004040c2900c4c5440c0307020700c4000520502030019000c0307072110f070b520b00343c48604c0800000c0c80c01d4040804d010b640d20b403240134075407419551030031941907500c2e00c81e16240c074502050455282c0f041715940061402002045141c1c0c00b103900402001c4103000711086081d003516400b084119101c1c0e07100f0852282d10020040006007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 599040863 1250 599039613 599039621
    0x30c0103020c0c06041d0a060e0f0402041803111b0f01031e0504111008090d0806120708070e06010908150a0e01020d09021c170f0c100902040f02071203 67
    0x1080e51090f5a41c5038440700110b15190807540002602d803040003201e510b0881510400341d404a0110800d225040c60180d5900342840f002e40b20a9000c2c4142c00003809648464102c501c9000703030440711801316242414001c0242e1100000da2000340a504115030303d00b08046043c4403d0000203200104103415100190018840702e220f01c0840700d0110460402012a4407401d807103036000d003641d075100003900e10401044403500c00452003808203940074450080000550902628240d040102c10340d01ca120000b5004041107080034146d01c110034010484903404a2401c0c01c444400303080380026101c00c0c0045da015613050185000700c1c1d20010500e446a0031411125030044040200020916100c90700c0500303a922010040050340c0c2c640c81c0c0042142000001d03200580c400403001043c81c095a95240307415034030002e4803241a100800c3d10a46c141030300003200e009805002c104c861041040415034080e000c0210144d20a41c50910b4844600105008954145900c804060072080314544142c0040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 599042113 1250 599040863 599040877
    0x240b0109060f3c0c050c0a061b03050f0a020c0315010509070311072118080a03080c0c1c080a060b09040c3011070f030f1e0f02010c0e030c010302 64
    0xe00c1e403024258400b10001a04880c5040b50f540d6082030b0030405040c80f51a220318156114020310740321100704a4030313600c48040e1501c01030912854013066010b040845d928012a8580c2203c50300008d2074848a41d00040c80c0010b18405405980c2103050118050700401c1c3c003440b8082e0410350340c500249501e072207a40321886640014004500341400c0d0303198200c100c2d149038040c03440211600c1c07002010a8010000c1d103866a010301c0000065030900b00403036162070a0220080601008002103680ca102540546104040020031500040440a000c02a129140d0003200100d0308100225003140c846001e00401c0c0c0c1c4203240914a8007105505000040608212901c200959542d05d01e208002811544412000c400305003070341201e00d4184042101c90701e40842c0541d034010000f4200084264a8134100e40b030305803d241400401e086415903115541c06841243d401030a4900d18407180c01c46988600300d11154001c10082c001c20105458810310300c40425170583c0500103145043d0f101360024100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 599043363 1250 599042113 599042177
    0x1e0108040f060915090b24010c030c021503040228030b150a140310090f17190305041a0702070302060306031203010e092a04020304240b0109060f 64
    0x6202291034001c01030301350400b140c0c00c007503d5140c42804d2002c02071140d80c0000351b030200005421100000e41c101c06100000745810700c610b500d00e060030b00d802401d50f0f1b962142c01034000010464149080c1507150700444040380700300010188403040308402d10341440e5000c0805481085c80c2d0071a110101560002400200349600c0180c0322106500c4201001c80144000d440c01003d09400c8020181031400541c1a122600e181503009408182e01f05100d02e0001c1d0401d00e50501810300510103585841402d08101581d24000200d80c1140d50690005108a0042502a0360180c280004807241141551003800681c032040052016192000c001c42d04480c00070100c1d1034500d55409010f03000c0d0000d0740270742d454200c08410041203074420300c1052281303000c802c06e560714540c000c814003240e00d0a842040380648e50200008040003071032a02c4040b4019502141d60041101c0c0074600c02404044401c1c500141c4880740014800380601913a0a190416840b01c00064a0f0141040074125207030501d101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 599044613 1250 599043363 599043371
    0x2d06080a2c0f1212040605060102011808070318181125020a05040203040507060806060d050c09041505030a06020d021207092c1302010311030709051e0108040f06 71
    0xa0705407074880e104100510590701a040312080200c0090401498038504505280c0401c5201c4c0f40d524a0b01d80e4650282c3d020800180c143c40c1d090040740103200038240c800603d44180d1004d020310555030081c0598070f10030364072000310600c8a910b1491516842c41041c60414251000c4005e0213a00d402101c0d910b54007284c45424003400d22031600e0041249405a02041c40c07001c072040960604c104210b0290005076019455810244e40e40c65542d001441441d0422507090080790841c4c0e9010200c1d003500b000520280324604140300850850351007070140da48100e01e04010240100180483c86c0100c0c3c400034050288070b00541c6482011703500140620414a43c204034000e46140c8480c8030900620b40c41e80c0b144007182c1007011401468940d21414201d400b01c1c0000a4205540e11300d100352711000140e020f1643d10050301c01a0040d00514a1001c44000c4c003004102c2015403000d060300c1181c0003218480d90301402c0c410f400910382c401c882c00a00080c64070340044d011415010303a41e03e149100c1c0380300107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 599045863 1250 599044613 599044661
    0xf040c210f0e06100501111204032109060516030c1e150605030705120f1b010e0f0904080f0f03040803181b040c02010f062d06080a 58
    0x304801040e5000058819524105102080040d2103007110100c5400000c2c1800c1c241343c0001d072031641c0a4070409041103a42049103100348424400c00c40301004407c0713040d843d103480307180c000c0703100c10018200b82071000000051130be40da124500070411510940c42c0e05140078400b001c180485119602c0a03400d00220446100010744038980c40e4001c440c03840007103d0380d42141c0c80c2c01d442e031203400207140b039240781081002d02c0b0907a40800d440e02201d000719052200481210601c43c200340e00a60300b03074024002c51000d1000d04a506c0d11030b80026500b641c984403907004004c10040058081201103030010b003090006000150b1050051401c1102259801c1c100021448002050f5104036012074601c40d010061081d4400c4980c00f0909042c03a060180c54440b003042e12807941114254001445182c503640010402030007907000000300013140d2402d00c00715450b42c03c114403010340c20354401ca5045c00c240d1040d80041c1e0740301030ba0050703070215612408162507894070072020b4000b8140071111f40740c20398005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 599047113 1250 599045863 599045897
    0x20a08040902040e0c1306030c1b20010f08060f060c0607020703060b0a0b0904110d09030513080c01082a3712090c030506010e090601060306050f040c 66
    0x54801400e000c60702590740d03030410aa240c21203901030007207442010244810b00c1d42c44079841e8440142c5549242c001042500044200c42040c503404000e40c0c10000c120040003442451040c3c0d8400c04143c800d000715140700007004541c1d011926003500300054008021071950315200700c070b65171000790040c002ca0600340800b160508003042a50031001580c85004100104549c40c0213000312100100d407027400161819121070307036611401a11a01c030702d507900c0110300401580e00946118004400c02000045001d1501900c0340e8020401e80c2141400c4c035400050212001034020a4440180d582d40300d03a0700e40c00d000e02c02c05542c82007803e03145248652101e145501c00c00103000f055811505080c1205d00400b0560128106000300d15038680c046406c4140c6160001d00900000024000009482c0e159051a004d0b4007416040107005028002c00003900305907810a850141030803001342c59259a840e54150200c03506072140d42c1d00400c03503600540b0a49031541c040c0502e155641800ca600c103641d0f280c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 599048363 1250 599047113 599047117
    0x1209020d080a09231813150e010e010b0a030b07020f030d020403060b0a050603010b07060207050d0323040b0403030e0309030601270605130c09120803070e010f1e020a08 74
    0x10842c002030a440c0100090400b9194820b090031001c00c4010407072a924000c1001207050031000d40b00040c2050100385409080d801000d0340d0340e0480b04201d00d40a440703114a000d0040800c154144d582402242100303008107100d503100c9170a0080c407008400c1c0c5556205006000d0051000041d07019041301c240380c0c244180014200b00000c110010b80d81c1d0b00f50b00d0000c00b111006a00c081c02043c10010a101075200c81c8112030550310801c440640342d840742d00e0124003a119081000f0618044c000220800e81c2d0140c00c41c1800102e0303007000e0680010040c0c81d052103604100c4014020112450118001c24000d43c0000c2495140c82d05880c43c12181c0004245015020307804240761070f88000348505c000d49107140f180b9108049040a014051030100020110f18201d501610000e5580f03001c14000c6000d044800d00408000b141300703030149854209202250002c03039071040441c0e9040c0c0341728035941c4601d07151900f0100d50348a61094150144640030303504100001030701235204259400c0041043c1c440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 599049613 1250 599048363 599048377
    0x9080c03131505070302070e0c0702041104090e0604050a0210030b1008070914010c060b060405030a0b04150903080f0403090f08031e0c101e06030b1b03071209020d08 73
    0x1110304051454501d0441020b805803000d03a04100040c03182c1400640d001c60740d036080f40c07200d041c26001b6031101034051030035206421000f58024688007440c94801e00d030a0140080300c4940c9000c2210706031844403a07443d444200d034028200d800404802c0b00502c3d04903010004c260161400007808044507001c118030406120180c0003050b080010061940e0340000e02c2c04c003428480804402c1c00390780e000060b24100038950000c2800d0b440f41c03000070320380d21407000f03880c0103000007030032038070842190b007013b801d140016a000d45e04c840301040e1400d0f541c8405d000300c2d110964503036591003140c3c0d80d120180402d801c000c0e00031070801540d8100060710014100918000d00712070000707960b60b841220316144500d4641c0d100300134241c000348424441d00c0382c041410309100c1124000412810407222490782d40c0103141e040e94009524113000803081c0101d082c0c080c2e2040305a80e0b914041c0404015100b581408115000800200300c2030003203900ca03905c4d80202c01c0c554805001a040214603a5880c095500188 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 599050863 1250 599049613 599049637
    0x1006021f15050a082d07030b0613020a050a02160f0311210c0a0e1003020613080607090503061e0c070c09050705090901061701030605180f0124050a030609080c03 71
    0x528109401e407040c8001e24410301c05800640c410300300c43d46041e101c0306d1078400a002c019856000421a842d800b44041c01c030320b8965001c647d10b03000300d800500340350090603ea0006219202c00740303c510075410000d038295110394840c501e80034a1a910642c051a072a140300360409440c041d0742004440010b403071035a050400c0081c0060f0001007040c8030000c03071036501008a2200401c03c2c8500d210a140e0b4403019640c06441940e5031380260600540c4d120880d6020b000300c0e01c151010842c04540c4141148241c3d40210166200c41c0c43d41101940710482a4603015100030549002c54651050350000300040382c803c10103003034026610002c100465804076500804a24005010b1016150141c00d07180541414100b6186410289000d00c1c85e00105000003041c10b80e031440425416035030b000c01021801010812a40440350860b40140601014030a0180030120710704c1d00020f80c4118140d07032003a200e001e80b0400c01e00d8a180c036448060a050103056070700400c10410380002000910007400408101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 599052113 1250 599050863 599050873
    0xd0f020904061e02040b0d090305130b21090601170c030303040606030b1e0f04032a0506090c0619030b09040b070206061507020d11181006021f15050a08 67
    0x140c0d4aa180c41030b01040403e144a2040000340080c2a1b07080545082d00041d2a000031041c1052600fa03410307200350b03000003017070b80c551180000d880342d02e880050007a844501c5c07250326885001007074010889407d40728a0180c1d0800001800004465110711000c0500f100c2240c45000c1e244c00403234115070060394203503040d40c1c491405006200103502100d4200c003007000c0c0e20300c0000308100e048607283e6014007000e0403900755402040c02e040c0316103c0a41d0703500c400600106d6110010120724540c20072910100d4035800b0f1300c40081d03400c0c88007207900120024050007036894042c840614030300c65000b018002c424036958450042480e02c4a080725481144213010050030780c18050800b0349000d2004140030b07c6907619950f050071904c03800058550203641540c500744041c2c0503180c643c02980983d41055000607106001c00c0b03407450f15001c61401004046225840315854080c1241c442288000a0307070038610008000305600d6a551201a042c03c041d0141c4108a03151000a6107141ca1640404415840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 599053363 1250 599052113 599052131
    0x9031908060a080a0803010315060e09010203190e0703230321100b07080d0f050a090c050d021f0c06060603050a0b041406040c020a05010216031b050303060d0f02090406 74
    0x1010310b91014040ca940280305414007541c85140078801404010080440840e0414881c212608107501410360210003203424608421228000d41007107a9007645040f1543c440e40ea000c459218803420300d200307a406420000d0658444a0100c04412344600f990011240e10303620341241400944020f11a5208120340c445115a01e241d18070009415441c80c041c880104000d40f07041c3d0300c100c8240b180e00400042c1c13204035102180000b0540c6444040c03e4078104800c129001d802d81c1c1c040c00e401446803052502c00303601c0300c0034004071608107a8001c0d00003070000034805280300001d5414001074000d207440b225100f21030b40c0c0d02058801d02d44c0500d000c02e071603000f48000903249015181c0c08a13810350f01088038121340091740c00300050191107180124ac0d1400315000d603e00c00d00404040076042802995500108000a40303028401c600650000340822404445103584150051100c0c2c0c001004500316140c2e0410042110621001212000b00607100400103031a80b040007803045000c3c4c500000c98081c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 599054613 1250 599053363 599053369
    0x6090b09070806010f15110717010c0e030a02091b0d060e0610120e190807030905010c0506040b0705090d0303060e06010e0310090602040b04030b01061409180903190806 74
    0x34640c0001040e03801c460014421004642c04e070b04c5c101c5103c500502446440f0b1141654500040208403140b401034040c04280d41049028280190200300e000b000340c620010342c1241c1d19403121702041d034150020018080035280100c81242c00801c6c48180e620307142c801c088020140d07440b04006104a50310b424080080042c5a611140d01c1642035030510024602010010002c00f40404099241e507616540b081400344200420594046500d07204032102c1c41c1d60400d44d10513000701d00308800080402101082c01d51040b011a01500e5010f0000c080ca038546075503204002000a181c175003005014495039810755640c000300c0254a01903100042d0060a10030113595500e0002c00c00c5062041803440c100094034001014440005617000004911190341b500c20040c1c41164800ca50a840114010003440600140305040381c6150b281c10862414910814007503029512405d07900c0a500c0c0b0445c00816a4482c0140d804128482507926203c02c0c0341e002940c0c100941d4524001405071001c00400341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 599055863 1250 599054613 599054623
    0x90f0d11070504050a022106100e0303070b09160f03020406120c140114030a02190806060d1e0207030203041508150907140a0c0b0108010204080d0f050c0a0f0b0f10051c06090b09 78
    0x103074500d00002b40400107004a603a0f4411020010049061140050305024080c41101d81180d82111605940360b52a4038411841d001d500090740304510348200040c0f070300040200d0b907588907401612081c02d24a00546007c440400322900f505200d1003045040140358508011032052144d80d03070040e1140d0f4220560600e1614071a6a40140203204040c094a41d0380d00c001c2d184c80e6100c1c02004240c1d0f0701c008070420f210a804108682c0410300200d000001c054000c0003410940305030003450640001040320490b00d1440c10b5408026a40444039000c0542c244a14020781c00080350800c001840411031480055510030710000b0000364060240c5001c02c4440d03a41d5a00400c00e9000075414141402c003015103403d12910080c0074441141e01c030086085c042c40c2503421081454007a1a80c0c044141000c1d038509200d03e600701e481b00c40580c0050700505e100c078095400356400d000e00302c12407420002413041c00b469a5000041d00004e40603881d0005d03c3c640520800e0522414103601d4034144010b60310710b41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 599057113 1250 599055863 599055889
    0x1c0606031a0d03021f06030506090703141c05070206090a0f051302070803010501030b0a0e0c030a0f0c0c12030f020d240303270905090f0d11070504050a022106 70
    0x1d5502042c654020981c002220300400c0c041817400001d400045a007200100082d40c0024254000ca40c10807070130a030b011401e034045134010039205450300b541041d5291110700e800302035820754860280c903840700c51282c000762090300c0c400b61003a40f0b002c1c9480c0c002542c0c003078954040c11524000e40e10902c61400d00041d0b411500303088000a42c1000059031700c8502602050040a04055844103641d405a654462500040c5801d403d4a1402e0070010074055455004446c20f051160411070380c10300250b81c03803240c003108810782d6440032610300c8180d03141001c0d91400f41480c0201074036003002501c2458244001d11400d00100c2000501c100114202c01e80d91100000894810310301000400110342c03c6203643c4040b849034500e5208110180c0d10002c0034900c0d5070404000c4c035182900300142074800180c4020a080701034212008100b2000702280d00b00b50161240000340c000100820072802c00e60802c0740c014080020250401d250084400f150440058074034290000840034800942000c200c2c1d4081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 599058363 1250 599057113 599057119
    0xa17090d0c091a01080f04020d020d0804030b1510030c05040b0c0303060a0e0907030f1e120212030709060e060c0d0503040c05040c0c20030607020a0b09160b1c0606031a 74
    0xc210640c10002c5d0015000400300b403c09134000340007404540c0c80803545044554000c0011a8000003030400048070381081c0411181b510041021aa0400d00b12120340b070422070042128410300245041240a88070640e800d0702449428800851418100310140c10203042040c001c44e140e18150f03040000000301a8408048003c080c01440000400440e00d581603e820000c0c8402500280c6003240d4032400740040071100500240b58a81041050130041141801c81d9003100c40d01d0482d451a120715100c1600c0420204412000c2002081e0180c41402c80b5900010480d50401c1035450380c4a003444044405600095000810001000031004545006e090180c030704012a11072410042c201c2021050090442070543c0b10090640f0703e8280b156003a604050251210350810040c044c1d0b940c01d4608040350f09110380740004180e0762000410b041490b04812580c6051490080c0c90036040c0d0000030f03102c480070410510a40c1000d040d020380401884203503400140000c0c008032502c60060100c108600c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 599059613 1250 599058363 599058401
    0x1022101030210050f0702061b0c031f09020a0b0d0b0a0f0806071407050f060118231017071502010504150b04020c060a1d0607020a17090d0c09 63
    0x758841d10342d4542094107900f00b403517441c1e01008043c0e113a4002d810300217600c03050005d0313002c11002e00301c62130b06007420000e0201d46110801c40304040d102c25158240340340102c2c5681244190701d00703036045040b0f45030010703100408003610380d1038a40c4154003030400c00386000c3d280c81c544c840509002d10700c0070003464038a283d0b085660402c2101c1e5210b03c00580034504000d00b407040d1441c2d86a40004032001c40d41d00c207049500c41c08000508680303580c024072407200d00d00c00c0c42c0b002940340b120078000c410782d00782020781d44401d01c3c1008105c03000c42c10000d0a180601c0d200d0840c04070364407810b141d50118680140300140800d03841c2c02c001c070b4a8400c14200c050210b904040074040020b110f00d40c46840c201540c2c40110301503841c036000c10028011644031200c240b04103004d12410380b0042e03110100301201007403850f0142e840d46280c02d9540005035900d1006a11a04201010440d0307902d12100c1500c0c11480185005a40340000304041c0d020348083c1e8001d011554100046103187c803076202e07101c08078415a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 599060863 1250 599059613 599059619
    0x20f07030503030a1a221811060d150e060f10050a08182406121203040203070e1e180a2604121407030807151d01022101 53
    0x5070302c9010103001c01ea80c0c66194004465940240000c60750140405066014031504450344c0080020036114500d102a1800c016140c1d02d881000787c191a0ba5041301c1c105107900c0944041c001960312000402907582c0d520b4220010090980209030300420359400141c2c018207144040000c43d00340400840e00c102c000d107600c94591a003003000e440a00a40d8203081c03c5030340d02c0040203205881030700040c40b080c0c0101c800f408150408146020381e41300549500e555103540f51410301140c46141c441101c000d0f48400010741d00182460002c541c0f040c070240c00d64040761781d251403035245c1d80001d4a82c580003c012880c0305000715840c4441a03400b143c02c650007400b0048410880b52a848543d2000c1c0003031900c0850070204415103c840345060902036512036645580e400a01886503120b1811680025821059802c0f1400040d0f00400d0302e8000c3c004d0b9142046035991501d01c2c075152a18201d0b0182c4480101c44101c60910350780e0840b580c00c4c800580e60f4000d8814096440c8440425503540084210040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 599062113 1250 599060863 599060873
    0x150e01050f130b01090305031309180b190905030a120b03011a190e010e0103050f03190503150d080d0b09011401050f0c1b040e0102071703070e0306090706020f0703 72
    0x450140c02e0321000001c1c48070082c000484003200e654102034124400001c02d00f915850108030343e003c8800b00c290030010400450b8200005007985800030b04803800703c40210710280380382c2c03d46101072010800000b4082c6c080d075542d00d0a61700140000310100e00c44d0080400d840d1072600a40b65500c2c0224020825450400084c2400c2100441c00500400060940f008031002102d80600138102d00c1d55103c2d841d6070f590081c0c007100d08090200b100c880c0205682e1107881000041502c000d400d0341d6200d554111800c906c1113802d84c000038162004071a02c1441405c0703680382e500280c89150b00828001d903944a802c02040240c0b08034003030050040d10014010011303880f500c0e5108207016000d11b80b259443c035584c079030180030740517550182d000780c0940c3c1240a0044058890313074210613001c1d10f040c0024290440d0b014201c0c000c0f004003030480795901402018159002000750342c4501503080001c1500c0300040401d00d4080129a1100c0c0d80d44403074424440c1a4041248001c02d140303800042c2146800c650398 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 599063363 1250 599062113 599062129
    0x306050f1f05071e050c180105060a0507020603090c0a05150f0306030f16091512030f09080124050a0303050d09020103060b0a030f060905011a160204150e01050f 71
    0x155030406100c090740c0034505100320100e0b00d2950b04003103444500020322803881c00d8640b00c1d103011201391203071480001960410254030f0703904e0340c50102001d810380e20380400c0c046903600c02e1200d0410004204260707401031392001c000d18001d014000003084401c1d0000c050080e80300035034101503c200440700c1c2090141c10001c045036101c4000110300c545035247e981c0881e20707000244800030b50303901031605c0030318012800d49a01d404032280b484042c81b00d110001000c031801d08090003601d4035800b11001c1d50000c04d0140407000300440319880c010711442d036180704d501c1c219210bd00420100114024040c0182e600039170b0b0b0503014000445e14403e005182da0f0713003d806413141c18440004a81c40b04184015603020b80d2104004044603114240e440c11101801001070646143c680c4540e40391480228200310703d44641d43c1a83c01002d03a200c1000c0e04804004883c0d0006c09011b49124010030148005880350b0049101c02050402c601c280541001e01d240c1c0b000c00140c000c240540400a44a2216580c0f088 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 599064613 1250 599063363 599063389
    0x509040f200c033103080703080c031003020f130e030901090518071107090906021b07050f220606090e0c03040809090a0902100809010c0903050d18030c0803030402010306050f 77
    0x42c188501a050030f00402c60084100582c2c280f81340f03c04000043c45581801400000d00c070340d888149a644105240c070160005407a803000c85208103100780014240180d1101000700000c24406948100c2c04d1081c1c10754004551500d142d810124043c001560004900006081c0860700200402c500500350009110010f18007020002c2c140c1c3e91496a590500024014080d074010501500700e42d404c1c00000382d8400c07404400303000a106201003000401107007040907190700610004c0902100410031481c62030701001040c05124008051104031040e1140000400e00394940329481882d041c0a5003010340000c0964002c500104108000100c6072000c03240500402c44411034181c036100c00714401040143c0c00290031010764000e400d03120303800002c414030400e580300003031005103003011044541090900c001041c640c004140c910403140a1481705d0b0008030048440138503250740c0d44440a024400d0340c010807640d040007090105550381401000050101590011004403c040200d0552142da01c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 599065863 1250 599064613 599064637
    0xa0e010e06091312350c0c16030b0702010e1603060c0c02030d030b040f0b010c110f03060c0c0c01050a1d010311040306060924030b06010509040f200c03 67
    0x100020101c207503407004140e503035421039003c112a00d08a04080d014030740c54860781484032980141e105d5080002c226403c05a03440f9165030b4101c6e00c6c0d0491020468004c2c511b1140325000b446001101c0321142c10018000398042e400700603150814842c00783c00c48031421074001c3d17190020144a01e40650000e140c0084961201e40018401c24060f03040350b00303110019000754180500000700b04000d906030001941c4a02c200d8007001344c9440e0030b203281c086407008010540869500e00100e004611800c106030392024001d4040000c00e00f00038002402d00c407040f03a003000c4840000c00e1a0300d11354403c10968003042800c1c20024a070002d5460041c01702ca0f2030b0500c140e4400c0c801f8030668041c0e4440d070031003018458030b0712040b511030740c8914146020b00040d01a07140380d40c0c9411000d41d00e0411408600312211541181e0150150560712641d0502100070102c4c4d041c06410000054180c44512801b230700c00c80924000038800c05103010413140485400c510790b40d001020311134104c3c01c490200490305046200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 599067113 1250 599065863 599065879
    0x105160b0609070c05150a110412060b0a1202091302040207030807020d0905090604050712020c070611190b040f0b040c14100207090209011e03020408060106080f0103060c020a0b150a0e010e06 84
    0x52107c0c0500402180e00d0000c050100c1d00040006905005000c0c0ca413050605000111521050060a02480c4103080301c070250032480c60b015040c82d01102d0741110907018008000301107500800d00741e0344808801c40005014004025596034107200040c403204d031710303e4100d050a02d09000a00c103818090406d512030390b9203102080900e03004868500282c2c184000c299201c18640f01d002c1d85540c2c0c0342c41000e01060040e11800d10450010552034003042081d000c451325021961111207180300700800c1103d5107801040c100d000704020b1403181344241d2007142030140450501c410081c4000d0079403035050085030000c003030410080d004142c2c0303415141400001a25005100f0049070034001e01e200c843c400c05a564909400c039a41500244141c0c1d4180044840503641c500e0100c1340c000088600c0d80d020b20342c0c4001800011520b07001510401454811511b086c0d03029140c0403d4400251490305803400001c030145064200407070030a005100410210140d585885481c020010001b01410310440390 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 599068363 1250 599067113 599067121
    0x150a20010b0d030e0111150112020319060f0b0105070209060108093f07170a050f030a050609060f030a0210230c0105060423060105160b0609070c0515 66
    0x95201d0030780450010003002d030701011410060460310514003000e002441154583d41e034003100084500f0380b901c0761940260310768030740341e001035200340113450490b4540942010301e5031116411050400300f50082100040074200403c400d422500c880081d541804028400a0050b80e01c98071072540c40502824403103402c0d6500d1200900306102070202d458881082100700c660342c40c011108203903440c00a6512007140135041c500307901a0107640b0b0010800e440c0b00c0083d007002c1803401302500d50000c450900c01d0a040500b00700c6c5510384c200712089880242d0307a00c10040107107880c020b1150400401d50300c00740b03854240c00c0032a80303403e05800c004e402081203c0342d4108181c41020341d41545c1d001003401c000c008150501d013801a9010000041c02c0f50f0814021480f01c1c40c00b0302c03556180d850450081c080710840c000d03d80c004c00070003c08a81c1800014001505481c1d04624207401c0300b40316051112040c03a00d0410030801d404090180c50810400c40e840350000784c80020224101c9084000c50070351662 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 599069613 1250 599068363 599068427
    0xd06050402240c06130b01060507080f0d02070507050913060902060912070e061503160c02190602010501090204030206040614092106070f140a050702031b150a 70
    0x2551030504996841814107802d041e6025401411604010b0000c1d908980c4030341c100000c0180c02d40801600d504c114100410545000364000c1000324441c0c2c5ea01c030300f03140d4080503421041d0021101c01070307841c0c0c000852804200d4140400c0c80541011500100b59080000f0710075000410580020b0a0942c3c41c400070003507680e103c0c2030701c031390383e40007071458100d00280500203441d0703152445503000c1d000d04040410703100e241034504004072005c054136035400c6a48600200002610b545000000d000b0051060000f41e00d41c141d03003400ca03100001c610192286840c0d402421142c05034090b103001c5105103c1400141c1d540c0b0100d404507012440c040c1010310500003440d80b14807581c1805503000d0304c03e000f4901c40300164099407920350351030000e0300c2580e03031032807802d0388c0c0403800c10012000902121410100200240003808500340149010703420300707003158080ba242502d4132002d0004044c007075084124511303054220300741d142a80209641080203801c0050031400001408501500203c0d0b58844114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 599070863 1250 599069613 599069629
    0x1509030515091f1e0e060c030121060921110307021c080f03090c0a0602030a171308031f0605040303080c250c060806010507020d02060d0e030c0d09140d06050402 71
    0x500101c0c2240c49001c00a001080180807021145d183c5e80610800030310010074803803d80b8101e07840640c5c1c0006961861402e4503056101c84070441710641d443c044100840d4a4000b0314001c41084284c44030904c81c0450702925a15031400c0000320750313000300114001610b418203d0a4120a00a03480c2c95618551070004080c3c05418004049480040200108050002401e9103224000c8e100d40c00e400da00d550003243c4a104490506001c148014940e803805058542c0d9964481d01752003035440550078903680e0070442d92064407240080100d846240c0e06c1142203081d81001012a41001032400f46541d8001d1314007940100360a10f5030304081008041100c1901909000d00003c4a0380e0b2804800c0e807801f0500f480203801020700244883c000117016501510880b11400d400a041040d0020143d003082400c0d840000d560040d261603410020f40c1c010204003400700302c0110f9002d014482401607004040c01c0b0194452040000c100c24403d03020340b1464080c480f081d070003403000b046669507400410410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 599072113 1250 599070863 599070881
    0x5070e0a0b0306130605060409030518150d020723070902030c130909030f03020306060708210906011e0e0a0c140a0c0201080f01030302070b0309071509030515091f 72
    0x140610f07400c0180314800f130500188058820841042a41c41d00300c14003040300e80c100c4000340443c60401c0b903110803c4ca0055420040d032002000000d030108084070701c460a402041484c500c11350046040c2c0c080254503250590141c440314003040307643da07420380c1095032589644500f2103801d03070000100e858a450304040761545c015103c20080d2070343c0d840c00801c0041125000642c0010480c814403120702d442802200d00540c2c0041005041c0700342c0f0b86038003040354018181c02c0c2d00c1c441611101400e44150b000c280748a81c000070090102503140c541c0d44a044074000b0200f00414080390018800800d507000c4503608909081400120907840b60307003d0b5042c45022980d4000e0302d501090340d4240e20ba00c00701815046100386ea94024640b502403801e881c884084c00001d005da013080301d0601070b5003506030107140e011203010200c5405c0fa6440c0c0c10fa41d03000d8030140d036410018020403070038030034810100300035030300803140c060800c46904e062016261114220658944240e000011069000d0741a401c00140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 599073363 1250 599072113 599072119
    0x1e020a020a0621060b04140319050d020f010902030a120e0915040c09050a030f0206130306090308070e1e06040f090c030b010c170d11160201020c0d05070e0a0b 70
    0x108a8642c007001c3d1070001000e04811029010203103074400a4a54050b681c201c0d45101c60742420301c0c0c01e18091101c840c1c0380015040d0103108104c2e0204030300c0c2d084144c21802074080c0020740360900010600030b08000c3c0318580c401b8140e051101040c0140c800007120b203c500e4000324060003a141c0380d1303012508504015880c9078044841014010041141003ca002e10312085508020450058006071906441d903c12940d209000300c20400203d106a0010b118052004050324640680f0588480022a05410030303101941d484e0200000c0640040e1910f4001c00c0703d007070401c2c49203081310001d2420202400310413a8501403501d0360ba255103485081d54090314114900903056511044030400a0091000001c0080d040c54100080c550141c140f2880c0301c2d412083c0c1c0107441c0000744149203c0d620070666000003d0b43c45200864080700f240251440b02c1c1880c06008402c075150000a00c1d0500d1190f83c248141c1d0401100400034100040c80003c481d80c680300f61000b5a903503061080145060840c90350 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 599074613 1250 599073363 599073379
    0x41103030d060e130201050d0f0207080d0516050315010e0411070302160911030c030c1209060601030e0c03150a06031703100608010e0406020c0a05030f0421031e020a02 74
    0x7159040341c0e080802910220503440d0300d55598000040b03200c3c10b21041c080c0c0401c10400c001c0d20b0440b1036400245100c0003400000d4940142a56400940c2d03110400c1881031566540a000610601e200b81c030700c0c840940d2501505500704a0760030403040684003680c138107110300c807000d10341ca54581c3d822401c040e2070304004482d01e034032071810045d460352501124081c0d086001c0c0008030b880c400c2803084088844a4142c001d00f555900500c0b404d4661018001092030b6406200d80955040c0c1031800034400e84061010b4507440c1010000034003038400103c80d401968124000c1c4003c4e03910002009504601100d201d4642511200c00b88001449140c001416104e50944d85407554401c4100450003a100c031139001c60130640d43c00c2d0840d107009080c0500505220300030b020a01003205174003d07102032000041503820062081d03652038516401184110748404000c5002c100d0008010003420302140c0400200c0c000c4c0304590340c0100305546605030380f0322181d005410007001501c00c008280d45194080c001b09 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 599075863 1250 599074613 599074627
    0x3011d0708042420040923060108070e0a0f06020c1813031202040e040506101202060a120e071a1603080c0d09061424060a1101060f15230304110303 65
    0x3541945c09805444503183c10300c8042c4030f403003e503080e891801002180d40342a95484003401150303c9440038058008114141001002c9551605410b0000345180545001582c0c605940a401c0104000241c0e1250b0044c8580d0600c0b0301c3c81410003940585943c480c0c0e41c440109250540301c5c440940f0651a21920100b004038688681d050018002d030b029000315041d55031040009810f4401c503004812034207410341903103001810400003808003c03406003010040c05161620000840d03018843d5050740c0d92014008024070a0101210003004004030151450104003021040814005c004024100440c002c001a400d1215806640701d2084001d418800a0528246440601541c0d405144ca204805012903201c05840701b6103d070405550303182021302c0c2010310402c0020781003150501c0501951601a22541e1028810800640842c41d03400030340a003806454100c001e10f09554a042c0a040a1000200c90f0240e201c288280100c005e91680c036a21481d01c50030a824150081d901480301140079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 599077113 1250 599075863 599075921
    0x51e1207060c0806120a02240d05070906050403031b0606080a08121e07110c0d03110609060c040b13030807060e0d02030f07020402030a0b0603011d07080424 69
    0x110321070b400181c1d5031080c56190b03001080109803100c1c0380307054a58001e18a0900500380940c118408640d9442080704188041d0740c240042d91042c0e8004c041c1d6580d134402c000802d50064004000380c4800c0c41c010307003424255030700034181d0005030704848007080404007202c08209041d00701c83c000e09800010745032880001d01d0306c2c0c01241c0010808400c0f81c2b0141c00014903024000c00d8940282d0001101a01c16460b0500103540c2004614020744940c010032401c0c1880b43caa4600c4940341500c2a900d09031941d680702a15418000080c140d001d16030049824890804410710596058a8400345810ba481c00025144000880035a00c011720252000c00e04000744051a403149051440340000e0f2040d52102c240c00300d85034403c0c031401e6111288144121000341c103160780510b034400e0032403500041d00040c3d20002041c0360426803003643c204144c0c020600d0310241401140e0b4201c80f050034034050f01d0510341c0c2c818490066150480c5000da8141c0060180c42c00503030040e400f292540c040c460720b500008036803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 599078363 1250 599077113 599077121
    0x1113080610090b01080604090f0212072301020607180305010606090513050601020303011710060b091c03020a060207030e0d110a0617010b0304050a21080f04051e120706 74
    0x30344080401c000300140100c10350141c1400380da016595440c1994079001044001c00c41c101040d60070140340000d4100607214a41d00300d44a03030080c07004015103480c00b0445440290180c40720340000380250150092660006901c0390010014203003004208640a100c00d107170016640044d0981d82000d4000825641022001040c2d440a85010b50a02c48800c18202980e10503251140180c0c4104010060b0340d2440c0050f124007220340090391240030302d0000d00c500361186604140c2c40e400e00000c42d000341e0b1400c0364010f241c0c11408180c000500d4415140070b51a40000800a030449800051250400d88038042c0451021001880d040300c4652741e00740003001c1d01088401600480c04444049041c60160843c281811000e45804016a00b0110513100075003000e0400c4800703205005001d0006404054610f000300310001c400f0b103c03c103ea50005180b071802809400c041b0100798107000121380b0108601e208014081c0c501070070003200300040c510385414100d403041c021001040d140308000139500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 599079613 1250 599078363 599078371
    0x306090702190b180604050c10090f0b0310150e0603060402070204240911031b130306050f0106050a050d0b0102070f09060e06010e060d11070209010b0c06151311130806 74
    0x1041c03131446202e0707941d00400e60740540541e0010078028801d1030200340618000718146440b110341c55940340311a11012141d080039040a40100401610140e0030b55040020211091540d0a82e5061000074100d90310791580140102c000000242c247c1c0c685070101e0b00071a5006e031041040000c0e004030020f8a6100e1120030b031303c0c0101100c0c0042d0b0f54000740540c0c070071046044001072940e1034560601c01c140900c40c4042c2500c50301030146003a0102611814401075008000c082080e02c0c020904414504050b0130010038000240030750403002d94000c0c00d490394007035502d0740000c0180d035210043c2d18201041d41f01c21500240038502144e09121600a00f045035900944044140c80e500010b40b080912400c2e016005842801260214101600028070000000445504e043c0458002c1002804240c000300924940000c1e4440300c410208001d56012070348801124035039554000058103e01ca41e44181081038803080c0442c030342ea041c0306c2110025010400da9031a110b41c0d070825661184401c035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 599080863 1250 599079613 599079631
    0x1030f0203090c010503040f0b01080d0306120305042d150224060112020405060315010e01092603042c010605161e020d20060f0306090702190b 63
    0x2504181500a034000c0d60b000d1520701d805009020410701c0116000c2d0001001918603000001c07015000c146450301e40c6000e8503038480a00783e401ca09010150a5600e240d00400300c20b0420741c11000072030303409030a4605481541c0c080a580f440b0314800381c20605031030040800070503501c9100240034036038105d00000d089815000d0ba200114031461108400c0440c01d02240c2203d40740c8000f503059803040340309080c0d8410a4070f00600307042d241d44c003103102ca80044503a030006a2860701198007540e00712003820140340c0709180a0070b00034101f106a524455060142000d5807000c04c1c501d02941c481801550064010708000051800ea41c02c003010b045070340342846241c5464001c1c004a8150b10802c2141e03102c18002d40c030081580c885544803101e0700c0c1103041c0303d0440601d8003001001655020390340ca00700f40c003480b018585032075003042c000702800380100c010384075800400040c0071030310301c0e0015a03a005400301c8184000d40e90b1040142c1c20040255001d80c005d1451041c0c01d800c0101e491441d80c0151090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 599082113 1250 599080863 599080871
    0x11040524040207050303041205040909050a0309080c1f0c06090b0a05180c10110d1205160c08030702070302060d050a1409100c0509040f0b040b01030908031308190e0103 74
    0x381070008902c02c4000c05030003a001080020007003081c0d982042080006490090325266a6280310411105102c40454443d082100c00c0d05c1416800441040981843d40144c02c2c42c0e2040c074002810300ca1010810100401d52180c1d80c104d640c080c407446000c494000030207019101a40c0f400d441e00d10b508541501006280401140c000018803500f500f0a105217070003403c0d14940700003004070145000501100700012000e600038288001e1140610300c00040e20755002c1440403034644025148020904540111500445240e03290310103102070311140c0020016940e91a0b1200482c28190305800194219a00140038030155509030b1185100e00c20407401044400481d02d010101d50b40f050b500340e0116400f42d50180050140c3d603020340d440c1000303410000c0c500040b80c4c3c04a0f040c0c4643d5003164070349503919402c009072400c0038022001c40c04030900c1c0400a0f440959111100c42c000508151180c451480c11141000320341001c4404001188512446101c907614000304558040b0130032500290030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 599083363 1250 599082113 599082181
    0x141e07031203050f040f060906020d0203040b250809120f0408010b030601120209090f19060b030d05072003330f150303070c0e0405210f07110405 64
    0x10a120b8680030b4007134200f119040e41c81c0d0746c0b103200d8410340c1110241e035102d40e14040940041c00340d1001b0400f8801c291400340c0c40780707098140340c05030f41001040d40420301d064901c1401034450245c00c1c2c558031603490400300100d468a1100600c0e04580b50000c18005000184441103001140e0192040742e0300500280724503910302003410744414080c4900541d11142c047d0000041c5401c040540d8000c1e565412241c0d0543c07200300f42840c226080a40e02c99101168241c0f00600c035607805008018282500103250413494188028802c1c4070303411002e815005801281e00010300040ba0304c2d1568000101200c043c00d20600c54030b003003103243d9850240d517001070308401c504072008120864031079031103c60303505d40990f50043d41c00c810400c2500c03040e038140410024100092000c0c00b0140141074003c03010340e880d00e014501149400741078940350307441c240d88401481c0303c400000110f0301d8000e1049101515581c00e490000001032503541465485400d24042100241c40203020026060078402501070b9108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 599084613 1250 599083363 599083367
    0xb06100504081c02010b0a03080d0c08010506070b060307081006061b02010f031107020418030806030312070c0f121806050f0706091a0901020a0f08010e04141e070312 73
    0x100342e01c03520b032040e0800201c980d8801c2607071003220307984101c41c00042040b0b8950400907240840035082221642d10101d400d410002c882c1c0705030420f00e000e5040900032941403500083d0740340680900100002c2c215800154507890510801c00180258412a0840b1006408520107080c41e4044c0034005140520080c803500504072080aa084e010384402640c2030103d0310842c042c1040c00c1c000308840e0020000940140c4803885501190703000e582940c0c1c0d1940091600410005010b0b002501c280d100b880300c07440b400d8800001c00c2d00030b581c50030802c003540305d68540000c41c40c00001000e0040340501d0560300c0c290341c03c1100400c0111b03841c0b120300c180549442060342d00307008150030452100700c03c0c0b00000001e25168010569980100440500f4092450746d441c0d03460012900980d060f5000f184602e010f030b40025031340d11403894030704180600350306080c011140c0000050000e80340d04c000c0e12055041100500551401c041402c0702a41150801d81e800d075550b07013091004031110800e01442c001003034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 599085863 1250 599084613 599084617
    0x7121a060d15050c09100210060b0a080c030a0f090308062e050906071b08160506030703021b0115050a090522031701030b04020103050a380406030b061005 68
    0x95010707000111140a4002e10001024000c02c0c2c1c0761400002c00000302c0e26500d031502ea0300501740960062056090161046041d681c070790780142c0f9000400d0003440d6909800908440d40a450800115140e6890758158000f03400a0b001505242d03285c520010280740c2e000c00854400ca40031782c1c0442e100e103400c450020078820152040c810300d401c0c0c0f492a8000c9807198004100b94400281200d0a0054680382d0f14014203103108651303500c82c00d0708810804a034040c4020396044401f980b0020001d85050089442d0703100042600301055800504d0141d00e0540403e20500710307100400030400090081c00d1890548018001c1510820504a001490301c015000d0b10b880340307981c1c0e04c445107240312a09182c1c110b500d01d00411010b001c1c04a24003005041c0f1641c00500a50007462000c40c6414107000150031079902030413180d00c1c2c80c1060800364000c4e9034568158850b000003a103c00303005c8141c05101202c00c100361000340c1d1241c00c1030400820f0019110f40d1a0003003d0481e100c4c1584030700b00800750303054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 599087113 1250 599085863 599085889
    0xc040503010b01140307110a02090108070e07050903030703260115020118021026040305031005030a05061b0d0207150e060f0613091a041704210507121a06 68
    0x45900704001032606e482111802020540801104c02c03400345940080c0c0b000c0f00907003100499500a44080240e1500d040d04a6000119800d00c280703032101c01b2000c2a02c07441403040207001d005141c804510100b030b110350b8481c00640c1c11f401c0e1220a50712100e0741c10450000c0000f500041d800d0400b002a150f010420403041c0c2c0f60700030941d0f802c05405045c107a034000d1010100b880c00c081074441102510b000a0140b82c0303e188265281980d80c5800c45a02e1402d102642200740207503c48500040080c0000501d990440b0b1143d501c294110004152101d80d48140000c20760200d00101d248010802c01080e09a1702020031941030200000f10600c4540e101c0040f01d100e218024554045030755410300b80d807c0d4007035201015000c1407000003070300c901625550401a0700c4c00c1465101c108070502032555443c8000903802e58060740340900e02810f070b50740341241d0104400080f45001031a03041000410805009000c15504840b07003071100e04003002195583d880000d5150900c4002880500e0019625082 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 599088363 1250 599087113 599087147
    0x91e0e07060903150b060a05070302071a27030708030d0606051c09020411040806072c1c0b090a0b01090203011203080a09140304030501151401050c1002030c040503010b01 75
    0x10540c41e6403030700b5403800c03007040d03813a6980d40d65454030003135030780b1004014008160140c9603a0380c3c3d030a6524009260a11039400320307400e58240c00481a804503031104655420b5100180718004e501c00700010000d481015840c150315200c3d00d1000205044040003401d614003c0000401c9690342d28402680c142c42010f17100081c081000c4900040744c42140c1c04028801c2c006040000c000f80015900b000c5a4000e42008403694011810840b046500102800d040c0841c0c581d0b20a4040c1c80a40c0302c501d41c1d20f15410f1500c15510310000c030b01502000700003201c116421001d194039a0800c00c420340c0c1c4400c41c041c0700340c5139003c00c0340000c21311905500807641211441040b1025401c10760f24200c03001074010f880c07880381903140d58000020481700d0700c0c0c00c180030071240042d40d0b40d40c0c0f0b10300d00079084940c4821408000000403604010a07410044a0784c00e0420a0910581d10042c2081950070103858030b447c0240c480c0b01105000509000c0c102600036100141c008100c420755200066071000182c020b0802 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 599089613 1250 599088363 599088377
    0x1802040305070b0a1701031103190201123b0708010912030f15090614010206041205090d050f060a0f051005010e0f0402040806070f181509091e0e0706 66
    0x340c000c080c001069131913514502040d9941508a080700305100a034801d64081c4000d50340f00a040c902480443c0c01401e1100c840b0350601c0290380064111810780070700d040c0c1c01c1d56403560400a007030b603a681c04003520900300107141da6440c45c003001035411450410088481c42580f001050a0005205201c0a00d802c40071a6510703101c0e2031400c1340076201a8003d01005c03034070f44410714462001046400b002c0d00368020046031490034698007204014000d05402d046601c400140804958407051450740e00005203811543c2d4070411000c80c0c0700081c03d04c4014158403500010102c800070114109000701d04d00300d030074851401c42e4841c04043d00d00a03110205422140041002076600070384201070441c00151000c2c60041c00702c070000d030890300302e27a104a8480c0c004004100100e540258000449130b914100802d5410441000341401e080e0360058070075104e505522005040d0003058010024444100203003e10111420600003050b9110380c913aa403d0b0030284100359015020458105980403907403100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 599090863 1250 599089613 599089619
    0x60905150c04030b070507050307060608010b150423090108010501080705010f080703090204060513150801050c040311130e0f0d050a1202091f1706060f0706020904060519180204030507 81
    0x1544c44400942804140181005a00f00054040c405070500364018100000c61618100c501c07425142c02c811814810074416502c120024900c1c0c09807403d07101d42407078810f8400f40320505401480307200803010364488080c000000790170505410043c1680d00c480701f03031103405a64100654000360345101036004a00720b0000941b1440c4643c1c068000b0a000402c046211591040400c1e200c0c4400c0058085094a03085091141707014040000c00600000b0f00030003d910308064004503601a60100505c01d0b007030014094882d544400c15240b201c0c0c1140c00810003941c021900365a184d0100f0848640c502902c02480c032803900131002d848000c80706465403440800c000686500035482205c000d0b62040d6201146201e412000b03106c05030078032584d202c1c400f0508010b60703821603501c0002c1103070b84a04001c10840e2381032180134043d128a1a1301000c0543c45400c4500040d024043c40d40205400c203207014809680c1500300c407140380031141844031210700d103510b0700198401d0f1b200300e020240c00c42d0300c004010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 599092113 1250 599090863 599090873
    0x90b0901050904020d02130b03060c12160c1e02040b01020d020607110a080406050a0210232706060f01020a1e03170a1b080f06100201021204060905150c0403 69
    0x883e074414401059500f50907000d50000e52400403040e00001c1c81e40e41d860001000b402c080042c2608030100111403420861f090b44481c001d944010102000740424420854070940912500d0b6400c03940100c5088c0c48298240320104410f040c50026441036080103004030041d4000b00e09482c415580e40d01900b801da6030740d0400c1c1c0d400b807000081700446100d05801c48010500c40c4000e403000d440c2c9551107035998512420024580b030182200e94944a240c090460351006000e40b600e00d11000f8180818016656a91041e11410140628640c0b403900c0740313414181402d01003100744c0b10343c20449240180e003551100480e641c868a400c014020416207401c03007515a00d07400000913442c464508400d200114181031500c11405840c031402240d120060001d82e0301081403e154505d00600d8210742510384503030b4800c0034030340280c20140100309801004003014400c0d011210f211119a005136001d0405280060003421206010394580c0100c1094078401d41031001a03e0250005540c0726040500315190 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 599093363 1250 599092113 599092129
    0x18070503070c0c0305070303020601050a150c02011101090c030209090f03040e06040213120204060b0c100f02040b0f04080607020a0b0a0c09051c1a13082109070609090b090105 77
    0x2903070600c0715a03640100024a054032480113188544083e06059282d841e01034981030b01a080b40784100345a4130103004941020700d421043c80c0d4103140c0806008200d000680d0945100d00d0030102035420301d8190001d00204101503000c4900c207540120b100d0b070f180c12015858029112103801c240e00f0801c0100040001900890303000107000b03000520309110000c0881c0c4032900d66005000d4003210f0103000e400d40c50a8400d40004219030107040f40341c54a0300303030307102c1d2612400204007121035a610200f580f052001d9042e075000e44907814440b03075522102407103018103401c0303445881218411307600018151440400d02403100d503030003118500c2c55103514000300b01404505000700700b0001c0c044000030b4190b80343c1105184d00320310020740345107002d0b207420140c0e1501000e2038502d412103812402d02240012941102d60a43c5c1c0040b0380f6a20780368032126240f25800c035400803001c0000c00030b042c81091200803a1580442d44541c0b107907606507030740310707449010740703096403036895110055600400490030121a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 599094613 1250 599093363 599093371
    0x5070201140405210d050909060d151e060b0a090308030a0b0303070f0201120504020a150909060f0608070206010506070f05030c010903030218030303250c05150402010e18070503 78
    0x1141d90074161260040303607402c580c1045400d00020302030103a88010805015020002c085c17403074140c1c6051041808200505400f4000d42c0c0103504038030740c00b002d0044d040d4410403108040c0384148851541c201e81c0c24444441c148000e2140307031a0090004000403c80c0c225100503045454016180785076442d0b100c043d42004000410740e46e2940c0303080c49299810f0005043e058401c00407a132840c58030780001082084041d440780c84240c0b82500348800b50b65a4080c2004031042000070407404d0034400401c465420712940215280303401d096002c03a50f000c007441000c09840345641d40c51242d80d18200c0c2281e0f1483c082c810150003003420040358010642221a071800c1c14018000c59103400c141c8801c040c215410184140d0000e54045030341080880340720603482c52804102d00541c00c0d401c0021242d91445000a204040241b8904001110900a5600c0c1c100c2d80d0b08003041c1c4084081e030100000004800f03d400300d002410503c40d0a4007803600e50005258904202d241c1c00c0c8030340e5400c03015900d82d0b002034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 599095863 1250 599094613 599094647
    0x1401090e030d0c030c080a020a02150901180b040b07090b07024e0106030203151506070308040b01050103231009021810050304050d03180209010806090c03010b0105070201 75
    0x41560001e034500403d60700d0425564001100c4011030b000610b80c3e04090182090980100304050804e45e00081c95185210b003c2e4080c3e4440d00e0782c0c0c544900600c0000d808030700210009000c1c005010306c82100324803070742c0140b85152013076582e00c408403200c807440c0c0036a60000d041842202d0140c281304c4501e1810b03601c400c46400b00340202c400c450314070003810795200d40300c00540581200813025120294030300f15644402445024150740c0040e44030320100c3c2c011b0502c00c1d4548005024140c10b01100c0b00c2c5141d004c0e2041e82d403108141001041a0012502500d00000c982d00015043d44644110103581c0101c45442400100c4044800c94170403000d450028500e40b5428007103407001840c40180a0000701c1c541d145140c1405a085c03024103500c06c071025040c081b09008100105101003154040c0c085903241c0000d032840742c882e0721680756070889406500301d8111000400c2d14071001524a0054848008440100031032500705800d03030300803208181c00200144050001540501c40c83e8880030044 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 599097113 1250 599095863 599095867
    0x100209091819020120030a11010c1202130504020f0a170411040c0215190506240d021903020901031815110717091305060a1a0c0a03020f07091401090e03 67
    0x343c91042a182005d0290b10a150000102ca0341110b410507151501c80301e11500a12281004007006084090302481d100012a000a8144683c2000301114005030100900843d160280b01480c000c0981144070f840021840150350001d41c50320720f001091013582d000c0d20203004030742440c0901c805020f41c480b003a0298070528181035034501030526040c1c0700d95501e0500400c01e6041001c81e00544001070070a9000b00c40a0b014505c1c1c2d050a143d541c110942214001c6940c5c5901d000900024841c0d207442c110480c111080122580b64035400406840409036000d120100100d10920302080c41107100801ca01450b0034000320500780c907005031140c034800c19007241c10201d01c2c1d00d68031015102c40070807041d415800107400e0303450316040030b52580f1024411402c004511313100b40400e40080690054a002e0074506585c1e581c01c6081e0400c0320100b0814009075207281c4c00510b0f010395910038001c0040713590f00407200c000c06c640301a4400c819050f400e000d07034240241d03c0c018107400109001400d6110768001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 599098363 1250 599097113 599097137
    0x902040608060702160f06110709140402041a09060108181213060801061211091e01110c1c08090316050f01090b1909081002090918190201 61
    0x15441960010700300c0c000a000145000d9000130300b401e480581e9005c15240004050010300796040745a400e6600302c3c1030008003141c15160107403a080760b9a0100c0002800c00035107c00782c007510218180101d10944013440303400495030000581481003000c1c10342140004001610325845402e040b40c0003071001441d01c0000360242e90781c50614903a015020600c1c40300250202c00d036001900004002c11017807400e00001d50501350010511134841c5d18001c4901d80391134901c00e4003e0400112500541d0007010180801d2004a00480c4254807800c120b001c15011450070b94510004503c3e140000c00c01060782520340901801c031881900c10840550700d1110600c02104a514104441340b10868141068220a0f207032804003c107640d0440800c1d81042001c00080010980d000d0580c0d00e0550b403500300151340070b07040400302c54409441d80100d1042c49180303411803404160754001e01365800c040d56448000c1d501e4204811000d1040c080d80d0011743c0c4408190400701c460401e0180e14070388145002c02d84030704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 599099613 1250 599098363 599098369
    0xc12030807200f0a051b0604090906020d021c051021060b0d1b081501151e0c1a042402090a0e071e0807030c23130b0903031c0902 57
    0x280f070360040e0030395071000000205000007080701c03003070209404001c0720000c0d24880126085026a225030000c1c00e440300121001c04c241e41c1c06490414280140c11902d070407107100a502c54500702d0540350080e901e410085002d45400b122a001a50342190f1045c0e030004480a01580b809201042920030f07aa417504004019170310940c200140700c1c01800710380140b08490b4007840b40401d542e41b000c1d032a540b224455903d100c031003401c1a411110120448003121000c2079099031910042285651005410803284400303c0c2c20400c0c1d001340900803809940b1640c0c03510843c5c00e26a10948015106103100503140405d0962224405038400f612180507050082c241e000c1103251034640c0144424000b41130800030038562059406020540748041c01c45207031103c3c60301030810b5402801038010161501c5410703007c03c0c019020714840e03107141c0350300b103407210750524100b082e940000b215920080492040000c0e5408104c0c2a0340d100324006000d1440d00d101c41200800700c0c1e045105c40da420325141c03244180981d13 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 599100719 1106 599099613 599099623
    0x8040303050406090209010f060201060b0f0d020a1808011a010203030f01090b030c030f0c0102120c06010b03040624030314040602070e070c0b07030204030c1203080720 74
    0x144940c1005000340c04c2d110380107500668040300000c1c440380d290591400725135665000300a60b54071250450f15510881a061294000078000b0015501140d4020f01022001d800d00c40074030072104020051031016903020b009181d40d034045242d103400c111484036071030b254244055440c600d06058480004a8113000c1c502480c0c0d620840ea00380b0341c03410840d4441c000030013070440d2402c2c1c012801c120790f101140380c0c0d07450050090822480c5103030b4028090395034401d0300802411140c1c0c01c1c5103c00201c0e8100070010340300d85454008101d040000d500106640c950390010000200b03003507040103400c2c2d040000c0d0f1401180410041000721690101d000c40940748501d61550a640381c19108443c50402c03102d0261040c82034078240700070b050f010b40c024002c4030301c10060030301c0e002d070364903103005100e00003200103070104d12004001500148100c0c1042c090034541e912074943d84502c5c030390051600d = true := by decide +kernel

theorem cover : BRFrame.Cov 598920863 599100719 := by
  have h0 := BRFrame.cov_init 598920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 598920863 ≤ n) (h2 : n < 599100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
