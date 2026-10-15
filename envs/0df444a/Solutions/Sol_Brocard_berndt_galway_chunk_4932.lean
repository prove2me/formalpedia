-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4932
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:11:55.685599+00:00
-- url     : https://prove2.me/submissions/f7d66457-863a-4b13-a2eb-fa6adb30c887

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 886870503 ≤ n < 887050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 886871753 1250 886870503 886870531
    0x303021216020904060902060307030b011803080406110c0d060c081f1505090d060f0605060f0d051803070807030f0536030109140606060a09061d10020a0b 68
    0xd001e015001400c1da40d000307400b4004201c0003408100940d440203c83d10b400038a025202d01d41031400502400006041030300081501e007014160889040c8030718150780c1d000d07007924282820403200b11600711141800142c217205038110703540552580c1c030b0b112140500844020420b030040a40c00317010f12001610142da40762a000c0f42054881c41c0d1030a5105542a008036000b5103610152b045440b4090707051469441300500da060803c00009500000c006001c10600740000703640d40c000c01102c1c1c02520801007615204000b2002e21000d40c1d4002a80840c5801c10100402c4a04601c0d510f107400c00003049540103000559441899004031000072041c4043c64018a446c22840000e40c9003800c01d101d81e01d15860040a0f955421680022000d4003100a0001c104040040c1003046c07034180d800c00d0b420154081c1c0360110300ca504241007201d0008c4d0158845e403011901e48041200c0400e400c0c40c9104c241240c40e040c101d860390391103000003d03590340c96000b004503580034100584070f002d025104040901030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 886873003 1250 886871753 886871767
    0x2070b0c060705160203030a080a0b010e06030406020c120403050a0b15010e04090c09022106091e04030207120b0a0f0608210d09140609152a1303030212 67
    0x80011442e920814500e030440c1c54010450080d0050514080002c4d8180004142010420761003d591031081081d14010701425000d0070054800701020007a181c1c20400400008020070402d0700100b00500c10101100c1841c510b0f20320250603a005038000f00c80035081144200c080c8610704410300d8108504031440f070301c10111100042c2034800d03228002c0f400350703898040e0202030146a04024006002d849425076595041d41c6031012204040454103504600501c0410401d040c1104998496060313803c10940000740d00000140c140c000800c114118880e03040d02151264680b6104102503104204100090034402100d80a4802508a1000b80703032a0010030040c1a03000242d2a55401c0300007072401624981d204074030121310998207000c850754188500c26040200c01c0103016820940482581e10380c2d16031000a13038440d030091940f04032650845c0c0119200c0c80440803241c11861010049608a00710f08030005441d800ca01aa10402c0c03480c5101001070540500280030f800007032003000c6203030030302c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 886874253 1250 886873003 886873027
    0x319090e07080405160b04050406080a0809131808070b071e05160f0803040b0c070f120c050106090605012d0f260a0b030d02061b040e040b0702070b 65
    0xc401408070381041007203808141480b5090100d0400c181007900c801e400d4a4a03070380000c8a65200d482660b00841c90320360b00049a440201d00340b80e060384d000030010302c0c0c0040074080201141050151441e000e503218402100c1d01600004411060f00c01c142e01c64868a071403c0c03018010340000c0020302807009050b000c941070072068a20711110035090030419141e840004211000f034210040041800300720b03c1d1080140000039001d94842e40c4582d46011003940c42c064440400c1c0500d50004022881102c1d001e40042c04020b0700359031040c0c0e02c3c83d0407a0440020f450f00b84c2540c00070f43c040b84c045a9100c005200b6941c1c411300034180300c080c540780c506640e0714641855069520a62204040289909082c42c03214411501e80104484900ca85004042541c0d16641265805d032000e449840c9016460407a50801042c10720418249070007810840c3c2d40c120780081d0441c1d10200503122200c0c1000041440542e10411602440c01203011491a15140344044d20b808201c2d040405210700900070300003c14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 886875503 1250 886874253 886874279
    0x10091d060a230f040605090a141b030a0302030a0f0c020405160305070c0317061903060506100e030a02090a020c030d020d0e010203130f05160b030a06051f050310050a0602031909 78
    0x169214078001b6190740c42600c264201003444800521071040d030140042d80b40300008a0441c80e010030442c100c1550b03031181c10141d07100118000200941c0082c40489034aa009104500302009941040c2100f00350981c0018210340303040780e61104038540c0c07208090303442c1da0500c1069409009070a201c5821851503c002d40070054001d426990480302c100041d81070b449007c02902e8645050351140c080c6074407807500c200904400c079a0316014502c04c20502c18454440c1280405d4040050050701581d880b64091240d8108000d0000720105d40800068243c042d04200400555108240041e2980508038880f01a034203103090802003030380180180110000c00c10000004160702034100e40310711131140f07401ca04050b00c0c0c1c800342807840c10403c030009018140500840c4208610502040b20380c0d01c03a020030050845101403184d50b80800c5401d5001d99004034000c40c2c2129103601000c0c401d65803000095801d0759250001c0c2c0c0160404039410743c00048034114a000e40c070603810400011804c00c00101120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 886876753 1250 886875503 886875511
    0x7021e0a051c0e0f0a15110c0105040f0e070c05030406090e01050909060c0a0c08161a0907061404050307080109150204080a0609060b1e03070801020310091d060a230f 73
    0x81082c07440103e400c5e540c1c0c00d844002017004502c02103a50b03100ca00060500209540c601505010740256410f00358824030448082d59850506e8114070b0703080004040b460200180300c5e60078000000c82140200304108041d20081c40c641c0d5030401030504114002210f4801a4000c2d40680c429000344001401b011501a92001c02c080d2183c0c1c84034085002241c002c01d074030801410341100010b203405d544528107038035003596008101c4143c807812501050b001c450710032176000380c080c0c00c8810144240e034490085061070103001300b1050b0616444000182c10b2501c260b1006c81960f640d80032420800050000040102012000071410310349002c400ba0703101d48803003100602071a03440c280c00e03081000551020401280203021800816040e1002c1d02040c0c0300c1805c224400c0c03060303507400216413005008407032080300015013510b43c0505c1c0241180c00382005c00900c0c104200c00e564110340c8150700700040d5100d01c21810b0301181c6543c85142d100540710b00e1181001004202c8401c000644103800703840350300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 886878003 1250 886876753 886876759
    0x60215011208070201120501030809100807020705220509010203010e010b07081c11070605010602160602070b03040204060b0c03180105030412120b03100e1501050d080307021e0a051c0e 81
    0x143e03084610040b10f07410322405051440500d404004030501085902400e000c82d0151550055842040c0c019150000220b51841c01a4405c034028040c904205500f02c410258081400550000702c1e010401a504111924416a0350220040104d10f007901c111741d0040807603641c0c0900c0c0420940b20109580f04082d1070403240030010030000d0076003407030740d001c0d07980750070050060b946403901c2e4a011000740c5400c2c4a5a4014412102e20802500b281e80750740341111990b8000300440f920707052010b0056000144185c0c0d01507a50100010b000015000a1042919030341c0038540e180480d020700310101c510010343d00e040120520402000801d807940c42039191f40ca40c00c0100014241c40c3c0a50050008030404c20b4040c051000b44d500b04a00a40041014018280650310348049183c2c0d5565044024420709a0010214545002203202400103640200461043c0c0340701c0d90203080540e50424004444184943c4a5007680b401d12a090100030a1700c0b172891801070004001590081151000c810302d0340c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 886879253 1250 886878003 886878007
    0x180b010905060d0c0b071a0c04170c0306010303080906070305040305030c070f0c29160f1509030801060f0914121f1e02041802180a080601060215011208 67
    0xc40f40e49140056442ea980546070207203040d20381d50780c01880c0e000054101c03035044031a0952406090811441403043c040c5000c42c5040c24038005c40a89804900c2c60f0905190140c240c248086407400e10400380614040c1d02d88500905058400c5480c0950043c400001c0528010034400001e5120080340d0b0002c10a21340651511500d0800e02d0012401e01c4008000c100c441e04000b508241c8210102803121020400400d00c3d0180c05d400c5c8428459425007441201030041494001a00c4800c181d280c3c41c087c8400c0d0084100c0440200700300c4040d80d8080e000704019000402c5519030003034843c038080049103000141640341c04050304070210050180b0713200b00c0700301d007d4294441e400c1041e4080c0034440660041c20f151030354180c02c010900700d04a4080071075040000450018540201c400300c0d22000701b241c41c0b501c00c02d00e40c04000d406c07011590714502c50b140e00c08282540c0302c1d0300c2d1102508500d07002d01500d503d0702401924000c10590b240c940904558010017110740c11404003107944c0d810034080c607 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 886880503 1250 886879253 886879261
    0xf18030c030a05010f180b010504050c0c030f03041401230c07061401170d0c0609110405090c01030507020c03210f0a050c07091812050f0f0706180b010905 68
    0x6410566510100d50701441190920701c18804150801d50b5100005001000035403566800400340080050000d40000d01e00340040205040c903a0140b580306507940c05960400d613229032040c1c00e641c40312850241020010051100384002c00341c080700401d83c804000c100360fa8072a420120904809006440c0070404000082c103074840c580c04848846500400810440460103848402c1c04000c3c020485038003108907100282600003d40c0382a01c0b08643c85842e1100301c41d95450000c2c0035008001c03a03c8228a440010341358460780130742c900a141007030150000b01d000100040031104020a0700342154069a46400b180c0c0f00892040c42d001c443c1c0f0020034800343e20800b4518644a460300555981d4400076100042c1c0368000050f260001c00c039425111442c7c2c1e105c0780c80f015144000300c06024a800c0048070000100d20001c2e08002d07241d04d04105042c03c4415640c0c031806c1e005210b00419030303100010140d0030005c5c244101040f8842c0101100001d003880d40300c0c4ca0140c10140110f621059590001c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 886881753 1250 886880503 886880509
    0x5040b100e1302300c0907120e100c030902041103190b04060e04050601080f1605010f0201060f0b070c1d0c0a020109080f040306140403020c060f040902030103051608030f18 76
    0x1440382d02c80003102d00c414880c8090741346442c950f02c0042598000e03000c4000092600c500782c24040c580b241c2c0c5104040242c802040010208500f00d940c1511801c55090b070880e10502880c00401890340300001c21220070b006210907210708240c0003005000c20000c2110502c02442c40600e409007003240080c82103200b00100703001700042c0e00b103030000f501c80c0420003041080015140d410780e082c000950310b40200c2c076016259103080d02009105140582082803050794416806424007038901e20001c03880030b5a9490b090404282500407007a60a0b000a0510901200c40c441d1401407410f4030004110060348410043c50610113132101c0c20a09000668095081c030075000000816080300b10540c0d1880c82407404400e9600c988001c4414504050f2030000f24540f10030b0349407289402d9006002403001100800c88142d000340b00c4052030030814071021072048000d00c05107010b5031240780202a640d1181e4410242c4203c0c540c4616000d5100f080180c00451f02c201c15075811100810580d24010407440c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 886883003 1250 886881753 886881769
    0x31413020a1724130b04080712020f07050a0b16020d1203050f01060804030e33040504151a09060c0d0c0204060f03051203070e06040905040b100e1302 66
    0x400100350b100c079000010b88071008a603c5840c0121102e1031801402011005480030200700c0d07091120040900141d07000c50200003080390311500c139003090307803130580c05030380e40394462110040307c20069018160803815101c0801000e405088210307001182c80c1c2ca80744c401080d51144027045402c0850114804045440368001480000d510500506103141501002802000e0031640940c07020b010300b00000d1118025003141d030141d605503582c0e9071034603040d50510806000782c0c000f482600710070351006050b021042091143c040200c0e54110703512468a0100010f03100b03c110907101c5d0400300007042080c88040503040c101c28010302d042e41c4e180c100a000181c5030340540710a42810740180003e0307102a65000c00c0c00e1019901c2240d04001c85034a502c007180e40800c69000082c403a50000c800d1456140c00d1401039a84404a440c0c20300d0480d00640118405070850350004100d25104c2042c0b002f003042c20b0344040d520407038952000039440d140040007100d8200107805040c040c050706079080b00b9902d440031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 886884253 1250 886883003 886883009
    0x112210c02090a050f0f010303081303120e030705100e1908040504111c1a0913081201060207060e1008060f060408070302010e060f031b1c0507020d031413020a 70
    0x202401040c42d150303d100000d084221450b0015000d107000083c0362450004501303040c0d940541d0b03040d0583d500e102d222110058802d50507014041a4640850713401e8942c0120340001038120007440e1100c142d8903281c0d18042d06505004c0c1194182a199500b0f040e000401c0e541810700400860180e128a0400c8149446190480390304507050000184081d054030b0000c0c00d07038041c82d401600d00d140515540c0011962180e119000030070301ca5020a443d860b044203000c1d0440d030040102c00070132416585051b440c1e403042c0c1c0300e0f000305441140104401a01030240b4401090541410800000000005440142e900c402c0310b040c400140e0104480d6110079409890251001d048965103a855104c100d0761020b091100324002404c0d280c12440b00d04104003a2900a2a503001203420340d110b030740001d42180000070b41d4a84c00302e01070084103420003160700c80140040c9200000905424846002810403488109203030a01d810002001c0b0311b174051200c440d600403808110a0800d140d81d10002d80a120103078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 886885503 1250 886884253 886884259
    0x60a14030a05150a0311040f15090507020d080c0f0a02210c0111090906310606091202010206010b030a150f050118120204020a030b100908060112210c02 67
    0x2008001c0000e041d540410b02810044031040075001150381084200899800010880400914204018105a000740300c24416005005c80c0e81114000042e42640e01076210300302054407101400b0038940c06200159110700140703050000c03850450070b1980c65114150f1054004000020074907086031007440034075182001c41c0d160315540418100e07917290641013807020584031b500c0d00307a800910800751021a041e090015040741003a95403401001100510000d01d101d011801c80c403610702a052600122801c07064a003c00a5030900300100141242c2054011403180c542c0002c2810160381c001901c13030f0454411801c2203940c0e9a0303940e10000600b503c0500b0042c0c1003401744001c908400e1942080080e1942030f0703102031405017140602000d0400d58840c1c1240d55196402a07000760074aa00101101ba0007410b01042282100c404941c1c4e81c03501c801c1c40030029a80680500c407036030741440300c0ea00401d10284803500b072010540b1200d04030b41503030200d01510070750003810784542801058103a000503002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 886886753 1250 886885503 886885507
    0x1413140607063809011a0708030c030114090402090f040c050d06140703050c0d0507090e0a090c1403030a0305061311030106020f0a1205130906090f0b0a03030c02060a14 74
    0x255480b0503c2845410404606144944208003402520441003c1c18038014807095550f4640a0501201d54090503c001111001c00c4581e0100d11640c00640c06040000222560f0b5894001c0e854560030458140c02e1165915400f40005650703032241464001007083c2c0c51a559840c1c5d490718000c694502c0c1d201b0f83d0018064406102886200d6200c1820824500d4007000c107540ea0b140102e04030740d8215030521344068240601403c10b12a42d120307a03171020881c1810a40c982c2c480510000442c0100c030408941502c0da19004200040542c500c0b00070309a803d1201400c0e041c02001139264014000c80004050380c813000034850390b071203564a500d442d196503001c021902c860011107289900034003540f00544908665018881030000d1903810181d0400022810b00b24030003001c603120f81c17056003150b504501e501b0000c9210401762051000400104100246d01c498a001c8201134400b0410900d01c00c0380b200c1c030100301298010100b001c207264100c41003a034600d2035241c20b842075909070300c44851120300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 886888003 1250 886886753 886886771
    0x60a031e0c06020f0c0a03050624220c1d13060306090b04050d050703020a0b0a09021f020d031401061103070c12020a051e040f0204080105100303141314060706 70
    0x100d03c09104c454400213803001c9880320014082e1003141c610004050341d120200080c403000d000c502510755030180c00c51b1030080c81d6114002035201e402d9441c02c0c41210f0481007220b407210016200310902c1c0c0215040150340e030001d040c492641c0b083e001d0200d80c064256071010701e204940c160320040185034000c604004410035820803031801201103400b00c840740b0034100c00640180c000c0c010f48641c540d060307000b0440d003615556600c813f400007810030251300342c59a002e4001a5205c4200810031b00c90020441030b01010203400070301d800c24032400441030601d07280322107001502c160030003415a846c40c10701561010048010350300c0c0d4403900101420318420400b005c59031700345600c96490558000c41d1000d007000d894500b0460214800c03190501d03017481800e00342d12941401d4100c0c90110700d05800c01130500c4d544281e05425078604680314040081400020303c10150820982c00036000617089090410306e009104038001c44160080d14a810b06588130040c0656a2904030340a00340d12400601c04055 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 886889253 1250 886888003 886888007
    0x611090316090c05040e1302041b0206070237030c1a010302040c080f0703051008010e03030a0f0603020a21060e0c0405060f220e16140405060a031e0c06 67
    0x15000e088000ba00303202101c1c0c0018800e00588098605020071841c054503034541800900111940890704240c4454850b00240c09040b445210f1401e9a00988050301d44940000e0600d4030340070101403d09041882c4140548850b081c4180450000030f20240300401400c0603920f003d0312580003419003500c07442105582c9550060a8100ca1090301c00388513045c0039000c02c5d034000401700c4d680c45000381c0100014103158444d400c099004080c810006c1c03502c1d601e03200c5042c2964041e05e060040340d44000180071034000107208003500c0c1507104904000580c1550b000904010052040c14031045c4142d962204040000c000310041c00da10400070171112400c024240d40b1000400012841203103054000303091800c191903840c044020080038200c01c0c001c00f032426181c035200c071070120a00c140c1d102c003a950720a1041009a2181042c1d0010b448080c1c9003085400c692190242041e020f18240400e06c010341e00d48a07003010036241c0c0503810b560a00f0f000ca0b0038020135840c450380584a44044030000031056 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 886890503 1250 886889253 886889293
    0x3010524010801030803061c1b0305060117030304150b03030a03050103021c021f03150306140901020a1403040311070f0515090a090509100c120c0206100306110903 72
    0x100c451041108410050001981d00800901c0b016003000740420020b1000d242000341d81922040c000e46086c82c0040c2034541c0001e800c402d00e0b021034104405181403003441000c01040380140f06954000343c44480b0703890055181e0002800050000c03106a00352028150710b030300080c60700400a8100c0e41c0f580040100107000e03141c288000d9003da40e244400c10a400b0308000c031021859000742403844581d807008a00c9100b4103066080c1c0b42010365409052050103008081040114020400401d401041102d00710b852032003cbd0400010707a10420214010b03907000001d00010405404000307807607584030708060320300b01108180c82035203028039480030a2040e40307034030702205540c0141c5821400c0c0802407100c00e070600c00c041c80140e00c680110300400000e0116080346a0000d1410245c0d40c140d80c0720601103056a0400c00b250300071420351903030721205001602c91444008800c0c80108106d01307104045511524041c0000342217142c0381d00c44418103088280895800d88009003c030340500202c0c0c141d01440c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 886891753 1250 886890503 886890541
    0x200307030e0405090d0f03060b0c011416020a170d02070606090f06050a120c0302100e10301e020405030f01020406091e0b0f07020a0f060507020d060b030105 69
    0x2040300019220602d05082c03040c503124858601c010502036034219030640b10044041e07003502c2015112013000c9001c00192014003140b00c40f0380700126220700740103440f91007058003c1c40c80842c401c0b020240720a1542c0001e8030020150090000900310585000c080030724462080c4001026000286202c01c1004a82c171020440c0c007071640800a41e554407180c0420b44545100b902d41c0007130560400d204c403464039154600300700d2003601841403043d941e80c0850380c0f80311440b14030004103c489100440c4d50034900d00350b81c5202d150b0320302004d001c10700d210004112860780c241108419010503d01b182030003564480c0a00703c140d520440e04480400f00004065486030003014002d001e140000c00010005000391800c0e1921600da01c021141045038a4411150440c580c82450308040800070721812003a000700700608e410504155110054018040c1d20901c43d40010b03810100f000c030820404d0307808800c0d0b910060f81194045440422070421002610302c0400340c5906529080502002c4c00e11a0032000031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 886893003 1250 886891753 886891757
    0xd02281a03040507150914120114040b150a03240e0d020f03181e0a0f3f0515010e0601020d020d0903060b0612040303020903390120030703 61
    0x103031a00c5805c00d594000d89049402c2c0881e061040510040804030506440c240c00036240741d440804e2507030000c2c2540c5082d0300e4012210100c80c10700060044001100354840303c46881c1650300c081c0b140104080700311610000c3c10502030415984580d01d0664941d00b10000f403100181b00042c00c260340c1c6074032400e10341c0300440588500c0404001e0b80b4004420f03110a0095081c0f10700401601e007003481810104c201450440240c001401030466481c1c0055601610350307000d42d040510304010f000850500401e011610002c000c1c00c12040c07040c03024510b5609010b140c01071144000c464070300246004031143c0d0100c1030b182000c001048203c02e204810b403241d1826401c4076216403080d81d040c0d8a91007948440b20000e18004801e00100b1015003013010101e4014244c507160092100070b56003480030580d8100c00080d00040c4075260b03460100141c603015614182052130b29250316242c191003410104003800100c3d01c41c608440301d070b8000c1e408000d220704500845003000c10101003030f940b0fa5004c07040c1100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 886894253 1250 886893003 886893013
    0x1230405031314040e0a080a08040804030804090f050a14071803080c0d14130311060c030d090203070614040e0a090b1302130c02150a0b1009030b060d02281a030405 72
    0x45c3c4c40c0d03000100c2c40b5081d60004422854880204011280300f18010015501c202041100100058201c2c00400003054003080004035050b0311001002a150050940c60000c0e05008003280460406618150461075074145101072901602000c900c1d601954009020040d01140842c14080082018400440c00d03603240c00312011144603500260140b000341c2e044410402d08144002003201c10368401e0a40002c011600703180401c0191740c41e65010a80703081e5065218400038003103013410801980900514104814840e64180f9020385902503403040b031400c1891800402d40404031940520b0380240c0217400720280d0314185102e5660110141000ca0041c0b0440403000e045040503c00c0182d00ca0701303a800790481d0003048032100c3d00c481d0060070600c12b00d03a41e00380300c80f070560b12406012600d0711540c036601c66940c6941824011400c00800d814081d01001c5180300045e9101c246910301d150891401024188000342d04030100038041e0403008000d00746c1d400814143e840380005e5071080d486401214 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 886895503 1250 886894253 886894271
    0xa171501060908070603020904110c0109030e0a060f050904060911030f0f2e080d171e010501390b0a0b0f042004060915020123040503131404 62
    0x180c61100903c51600a44c110700b40a0081520076002060249002480030074180c420303468681d401d500500410a00369590b00c880340c10580c0043c1001c0742c196040f42d00300c1c01c00b460084007400d2980e841d50441c0410400040030301c019982e079802039029103d009810404071094074001034240c1d005032040d45c4017401c1c01000a00f2080d101b580544200e10000b0b441804541a4582c66483c03d1a00d0041403484403807000890041c5c020410030780c4030340c01966802d8248200d6905004081c0020b00000070321070305402c50103000308070360302c040741141c0c1c0c01e2a05034400c0586420265001000c0341000f10b180001d50603140540b40450360369860140610b034602000d23210700c100e2070200d860240507039400c2051880076a4040c540750b03200032840c09620800c49142d02d11f860741140154081d400c5003020a038048418000c01089400102c0d00a50500080100c43e003060441c45003c01050000302404400100040810005200b56100f07810442c4a40e11915184c0c030401c0c078181c018014103400385103017032281 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 886896753 1250 886895503 886895507
    0x206010b070503041203030912050a0f050c072715060e0102190206210a0e06010e010b190908031b1002070b04020607020604120804050102010507050910030b0a17150106 74
    0xc0707281541c0305008600e000d2906807040481c0785030708420790030b042d81c0b10102c0d030104200f04100c2036150100c0da030f007503070301c890b890009410741d81c0d513852140c1082018030240003c41c1c000644441541c1c665010b140300c280f04500d648242408a84907448200d0915812032152100c150030302c010703200300b62500616000c1183c0120390b9070804640c8180c02e5010120414058100500241038149002644021200301c41500c080685c00985071a200c0036130798044c0c1204d20380c060000902611020280b0881540341c42030058240c001d400e04079230007070340c1981009001c0d400313158250000d0001c0d1051700d031940428510100c0b85560041510114064000c0c41d0512031098030848002e907a11010344801d940300d0750280100303600000c0c01243c10010400001c6540d85002c4100c01d051407060040d5552107041100090075924060b1000c3e0170b00c0018001000541e0741c00c00303040101c200b80d18002482d0b0035101c0c00552801a5030f48400c503080756118002c1705140c80071800420468105a6410959984041c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 886898003 1250 886896753 886896757
    0x30b1f050a1d06040e1005042306030102070b090a0209070503011823010f031e021c0201140f07030e0306061c0c050603191b0f0c0c030f050c010206010b 67
    0x415001500821045482600070300e64201d20840c00c1e10302c01220080400490074592107074100440c0c0e50910400c01c200581c800c83c144c0c0180400780e9050020704a01d83c0200700b1007510711101d492002c0c0500009119480c03d50544201582006024036a402c00d00d007003070345600d550f04051b4001e02401001480e170074000c80c100c0341201d0951164043d207098602d550402030007030041a101c0000ca40052031030400d011203d00e40600300c03484070b80c0000341c607528150030004602051440c07041c0105500e0409a0b03500070f4000d840926080c00100ca40340940300484562004090000003814003080d4040e14180c2500580300945c400d44510303681200000170190303034403000c4518561107260718503843d41c200d50400a0300d002520840c10f42c03580302d0301d490000313400350000c40c0c1e440c04840c80508102c20000d01405080b4400350f01c502d0708145080300e40c1c4004c1081640020b203400780200d6250610400c1001f445000045400021030941c3c20903a00d4a1900e80344480811401803080500119414107441c0c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 886899253 1250 886898003 886898059
    0x218030f12130f08010522020a05011101090b01060809070f08073317010501080f0103060c021f0501091413260d090201120212270d030b 60
    0x20092001c0100c21001404075880b0b100d110212900014001544946412810307018010500001c0768618100c105001c20720715011104a012034103c03071000242c0c0f0307603001450646200786001c040c3c1c0c07446440240d001d00b0203004000c1c00b200c91000001680d55000e403d0038003691484083c0e031000359803418149c08204550299030300a410620b0100014044146c4c100b207581c1807003243d4650f491200745192070780c000b06200e26002c6070342c412100c02da4601d8048803902400003400c01c07034405e041c80382880c0054034050100414032541c44040041050080240071040d07801444c280c10440c10300e007401000381000f881811081814203c618003000b201c04030132481a04210304401c540d0a203500c981240041d1041d20010b20640a503000d9100001d81c030041c0400c401c90107012885407043d100040c4040b1010025403011032050080c026458a40d04156402a05107400105000000328440504c0380317002c41d00401e81d210b16094204d10702c0d050b80009851460890b10700c0c110314041d1100c2d40c2e010341145 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 886900503 1250 886899253 886899283
    0xe06090a150b031b010329010f08090c0123070309140604050d030c030e06030f0f060f0307060309020f04091b050402031302040c091e0509090a0b1605090a09021803 72
    0x40c0c4c84040d9a80a0484598800310514010074500304003e22840400d61001500d84108840352000041c0c3d60482d00329040c11010781703446016468013003a00b940314640c06003d281001401201010400c0b0061075540b160806418499602c403200d140213464440f083c40b50900d150407002500e03a041c82c000082d141100c00143c40c40e42602500d0750125994154503100b20248503c145c0c0310000c0e0b0301c0e032101441c401d0060054004150411441101104000400880c850030031001010056240464001c003150035504002c074200300c039440020310707001113840e50742c0d0440c0c03501c032100050001c900c0d040f010340552111010519038403507090005a100c02c0701c004180131018000200141003a0b4010070382e02e58103107015207241e51500b00700095811038414454140c600072100344034500e4940541a0030921450061402c10300b544d8a202c14041e000702501c0c1c1c1d03e0381d10160240030764000d5040340c00d003910040c02a2902910307003001c50001c1d046181ca600c1ca405141c00c070310003d0b00340058078844412081e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 886901753 1250 886900503 886900513
    0x216300b010b03100906030f06240b0f0d09030224070e22051603060f0509010b0c0325061d07090513150e160b09040504060e06090a150b03 61
    0x50300d10b1040d510250190308110300441000a01003043d01c01d202c0a580329202c5100e425559040c510241c548906400c000b8840c80381070011480f2400440c42c088440034240c00d82c4401145040810703074003e808091040d1800d01c80448201940800c120410740d500f400624400145007008031800321044070b1113000f14002109a651a01e0280303000740741e484c0440d14040840180b5100441615002d5500c0c1c003501c0380b1680708a681640502850020303018001e4036003040751419000450501040c840c0c038240e5600040c040c55001c0003841190441100d00d0101d80d039a58024070710020451080300c1c1621600c1c500381c900082041011801817002818400500c0e2031750810042d98001e08005d4492081511034a50341d500240c3c0b0070300c80113200c5d4030025000500c441d158540c2418814a0300c040351114031070f07500030b01404445005a1701000015070700081c0507030b03030f42c601100149811301c0c03880400e1044004010703401c4400240c0c6600c061180d0603103c0c0b81c002c403201403402c0d1115802102c0c2d150f003103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 886903003 1250 886901753 886901759
    0x1050f130809060408011503110f060304080c0c0d03050c071721220e06010807020d0f180e060a05060f09040902061b0f0615010c0f02010216300b01 65
    0x50809402a110300601e0031389003940d5600c415084503a00f20f15504142100c02c010014815138904c10b10101d44140c8440e20000400340009449200092008020a4020844143c040000c0000d81503458003e0f0400691034035a00740649a60046194a012449041d00120301d111401c48500c407101900300c020115401540505032078040d9404905424442c10f000701b5208061065103006074003506031a000289080c08034680015200504282c140b001d00400d1146003640019200701000d41480c00e40505608608c0031507402c280c40c0d21122180400300c601040d034401b204919401120100d45078a000b42c1c0c3c400510035280188002002c805d0814272201003c0d0400340c20852078144010585450203075110401110354030120468002c07544904014514640100b0070590003044207c100d21116080800007056600310f00c1005000405480514045900822000c58076000113003040700142d440300f03030840c1d0710140c00c1d03841071805000e083e441c2600d20b401044030210503006a04111030307a00f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 886904253 1250 886903003 886903013
    0xf0501022e0c08191b050d1506051b070f031e0503031905090c0102032205030d0903020a0605090a06051c050103030201051b07050c040e0f100204030b1608180709140901050f13 77
    0xa5040d0311205234a401d41e040030007000088800c00307403c0546a9946131030001c2520044229101d003800300da648004c3d000e0011581891089088035800006034035190418401c40b5103606980d480100280f101000b07216a11880803139201d61100703080e50800882e900c0b461500c0d0740d0005050200c0c09600208040c1e444505a01c400a07206021500603140450341d5001091038551050800400142480300500031460480030f030b00e0050a151500d00d0030714005000040091721940300750414040c3c00586a040004590303200d0f41c0403050107004220541e500d081c0a40070307103804c0ba02c8003030605c0180001c040210000d000d1341c4c040c5800000401d0030b4240700042c4401070034612010a440e200d200101101c1b80020426000780990318075000d6183c2d840e41c41d091440b01c50240c651800307264600d480507900c0f6480048644d200d001d0f02084001c440305801d004e4101000303a00001c0d00316050407445914a4030300420180100c98490003000140d80780c0310302005503141038500b94840031000b640a800f10b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 886905503 1250 886904253 886904257
    0x6121b01120b0901091a090408040902031018050a29100c0503030c0d1512030309030905040f0902100c0b0c0c10050f0406060f0501022e0c08191b05 65
    0x220603804009025400e0500091948000f44d01040b00b11361a8007846c40d03508110111031032070700d0040d00d00c507901e42482c1e658401903021b94092a81115070120001d02c1ca6600344030717094000d0080c3e00700b081050b90504070075000b0b44011603040d402e06041c9410400c0044844118034490210004041c54a0744400208100c4c0031456400008100c82840d02c107004c120f0134001180a81400b440c4503585241a84010f82980c0400c07588407800001e80340d040000e20807a8080c2800300e507151800041020b0305244c280e030520f140b604a250001c2c589841c00744085000c1c0e1110403031030b008a402201c6420490b10880b21408150300003410410b0200202c1d0025a84c100075103010a91202650300c0d03c082c081c00f00c422108221344915050003404240410b0140610900016000f09500a50301600b4840041e6a900d03205c1c02c20b0502200001c080c2400800300e00c1007039140d940410003440744151203100246040d43c2030742e00c00b050208400c8108030480309486600000201182000c45d060900b40040e251130b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 886906753 1250 886905503 886905527
    0x40b090a0b130e04020d1b0806010609150305131202010212062407061116140f250317030105011d010c060b0d0f051c03140103110303070b0f06121b01 66
    0x1c1005c0240c41000507e0041700081860543c1c00380400781e519000340783d460b004041c2e001e2010b0009103c03007840f00c4a805c00d501c144110b080d04011400381c80c1d41555400300702140300d01a0010707030043c0c4c115400ba036064005000410105000081c1c41c5c88850400141c0c02c40b468500030300320070801c00300c0d031201c0280e4040c04086d070040c040000e030680e0100440030f84e640900d400d41c81c1130002c408840100b0031140514028000c83c44006c0040d06201c5030019a51b800e0008102c6114941c05143e40030030f203000304004040e40d40000a410440340084290406400a00802e40420701c0c4221950084107216041450588141e48460004190b40c440100520b4101c44094000c2184e40803000440c2d20403100f140d0040c41100207004082103130480c05030440741100c0310400c15042c4503208a0045000d00b5a9042d60741204d6070360714000c20741e400640707103100c1c40000a020345442020040b07044541c4c1007061095030150b07030410103034941c064401d4030796001740200301d4420345107050303059a54444c003508040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 886908003 1250 886906753 886906759
    0x2041806050a15050403080c01230f0402120c030715080c190302090a030807030c0506090307030c020f03011e020301090b0f0120010e0a05010b031c0807030e12040b090a0b130e0402 79
    0x2801b5125110b8a420b98440d0030f104925a440304401409815105c94844403150741a01d00d1950382010340304a05d0180d000340001e4401e18800c510008070755000e12a410305410003c013120004c07a940c0d5803200c608004404080300bc103001c0d00002e08103203068030403120303182241501031a058001c40c100b90001e420100602d9001440c40c4408400248981d00822039540652141c600340c0281d131401e20328244008003810110f0300140314200c006070300300d4901c2c904580d04541c401d2844250030082401441247c149030b452000c002e030741300440880c503030003103042e1610000281700c3c040c504c405205080741a401854002810801c000c40d45103000d4290b681e00000e00700011070b0b00301003c0c040d40c2c905244040c0079689655598400c1d01c880c03500304211107881c070305102c005820003116880904010802001c0c5000d16442c0d09103509441c001748032251074249980c0301c140c1c90703a4507044060f210b6088404880d0142107407030004101e5194200507601c4000c608180300c02140c0c02c0040cc00000100548203d030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 886909253 1250 886908003 886908007
    0x11803081b040b0408011b0504080703080d11220b03150609150309030a1b080a2712030201050f0108100b060c03120f0a0c120e15010902041806050a1505 67
    0x240f05880d50001300004c100180000c01d10350348201540107242c090724909414030100300400c0080c00300101d100811a40c000c866075841d0a102c0b60780c040900808401c07044002c00c00104014101b524060a03055142240c0c200c1c1c00b141e40b6901100000d100555100001c241030040042e420b1600400a00040a0140482c1028140320700761105540040c0d44a015640006c1856040140d11030b66001c21032103403031010b404840c070681703d6802d548240103140c020032044e60042202060090010f06940a11056441056540b907a0345a4941b0045004070019420007003c00c40b01503402d60310074161842100070303284c0324501105090083c0900310419030402c0003401144030203001480541412041280020020314020381110300099000b00040780307103807801c00803103102c1d503201401562509104400042100c402040285000740082644143e0101c12002240d200e0141c0c010300112540c0014801142c1628161081507a24078000e01c1d400820380101000300005400d0f02e990852510708000d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 886910503 1250 886909253 886909259
    0x20a032405090705190b0a05250b0115030516180801051006020c0108010e0609040f120201090201080a140606030c040e0c070203060106030b0f040510120302010b03011803081b04 78
    0x20040d0364080740c1c0d0302416040f910302000b043c28036101c0c1070304841100882600e01824020709107402c1c01181c411800700030011941005c5050780800c1d82c0e05036407440c6004e00c4044039600d0b064104a40134001c082c10a42001c906102050090044030f004e0b030300c0394001c550b5242401d80121041958280d5a217203540c011400060005820b12450b4040d640c00601600002d04180003e454030010380ca19504020600c40104440c006110385242c015008a0360340050392921704000f4074650704040068074030300908003407030030f0300350154810814180b00f80c8074103186a96010100085a80007180c2c48050b01454000911600c3c00c400219402122000f05071708094507507201c034410140843e214643d4080004070401540f030100041030060034603140c00c0c0010382c08200403c880800c0302c00309074040c94880d0042a07140c4102e0300c10101403c92440403090000c0c82d418024084c04e2880340440c004d510b84804d051350a54400c00c030340155600b42d02c0711380300c0b602c0f8230280707500c181c01036210f550003107100780804 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 886911753 1250 886910503 886910573
    0x305190201032316020a120f0c1a0402040f11040302012007080304080f070b16060e19020a08030f03040308100513050108190507060c050c0a09020406140304020a03 72
    0x1070fa014070700962040c1c2c8a1900f031004030000d1142040600955000204000c006215650a84d4011541c2c0c54403440030340e100c1c00c080c1c80c5004410b4006000d03a4030400d801044a1942541e680f040d07008075800d2005d082042400012030701e21042c85d0030b26100821060026502983c0100c1e08011503030482c140c0c510389200700c1c1d41840041c0d000305020f900009010441c2c210100186060f251413000544422403424980750b03224440e5042e50043d0944988003041406011390219241d201000c00340c61a200311008441c801500030f0030304030b101d25140030000c16025000000e403110700d200c40c13003190b20b9511203480c10b40f100030004001d014040c0c2012000f1030f15440d800c40e40e150780d001e079600c04191541056561410101744d030390591210f51150702d061000c1440003075504125201800c1c45031942e4000c1c1080c4c4d0030103514000054100010640009941d082980108121601030350780c40208009010303001031a00c016100654002400032003480460f9003820a900c00403c0503222074042d000e40302d01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 886913003 1250 886911753 886911791
    0x90c030204150815060108070f030e0609010c03061a07020105070203190b060901170703080f041a0405040e07032402093a020102031b0703050f06060a050406030519020103 75
    0x1c82c1c200291004108400c3c2410051481800406501c200c02ca14000c000204850130003000c1004200a400c1d6240007113000758030075079488418000340c7e1402d1800001c414068088003406000091408c036002400e0444512400c4a503440a49003514007083c60b00115004e40090009070303403500880c10009a4a211584000d85441c41001c1d140e1040c07a059040006c80101644010411000a401e50b020103002040ca02c0640b03034080503490b2683c040040c03a9140c1d02440d080150504500100028a0600c038006402100c07000c0b0340c1408248580391440f41c40340b1642c44000e240e25242d1403582c03500a0384d6140000c01e005405401404c251404e00003c0120b0400c2506009a02c4c00781c091030380b41b214003005220011410070130071030308600711350000355244202d0707800b000c00c0c440b00100d030140c10805200100040d40c000b41154409180c5100940c0c481c0d0055803807c2c480c040d02034000913141032038050030742201c3d00440540b1078412111000c1d2040c21914100300d0400d0741d1095920b030b0b07100491013 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 886914253 1250 886913003 886913021
    0x3060106020703030801050915040903030e0708071e0501050d020c03090a0b09150421050a022205101406090307170a061805070302150c010f05221203090c030204 71
    0x8000c2c11180c0c9582006405030034103030015401802c00604021030280a890301c0300c00304209440009080340d00c0c4c00c1c02c800601c40c0d5500802c4a010741360300050a880700080003c262003604440400c13203489110b810074180030303a101e59404180103100100a502c8140d0190005803140815a4a4009a8000101d0921054110284214012801045a00304070210051901b40e039411585854140841c903807001c180f81c10200d0104010b07101d1942004000d11089042c19400742c505060800c444007c10a400200342c01544210b18050005401c0341240d80120211404c4508840014440c0000d03c91942e100c204080e13050f1003403410003e224003554074000d000320400d101070420b2070340078500341c01603c1405044c020b15200d000403680110b00041100c00031070354121102c0c1c00d851a100306410f02c6010740c0015411075460080d108000c2d500c0794203c14860f00d220200405100000390554400d40030400019094200074240003003c83d0080d0322806c0105d000700050b001c015981c1c0d0000f0180d85d1003c0e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 886915503 1250 886914253 886914257
    0x21b030c092806170a050c0f040f061214010c0818010b100210140123150706151e060516050a11010306060824010309021e120d120f0b03060106 63
    0x180d404c101d00c01e05000004e2942c41d1100103483c130302901d519802e580c3c007034080e40ea84c0300d2131124192010303d03501d540c000c03005110385240621610740e45504280605210810648003900c8600c0e20314990301d018031508080c540181c454100390b8468084000d400c603041c0c804603500359030724206101941e9484c12043c09804030346c4c1c0144127800d001c3d03080e0400c0d0740340c101194014400b214010f00c50086858190700141c451850441c54030360311280000c141c0382c130416160341519000a00c7c407080c4004d640159482840ea041c00c02c19440c0d071280340e1030301c071400a035110b010098500d60520105114200401004c00d03c40e02c2198100ca80761603441c02d00306003034030449424104050014807540c0501030b020081000f428102e206c3c2c5468036a031964071065456041800c0d80817100c25505a00a9000f070b000c850b0094299a400c0398501e01c2c003041400c0403100e5510902920b5000302030420000f402064070502a6106554400d10a2252001e003400e907801c1e6409070788a40808050762000c00c86280280825 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 886916753 1250 886915503 886915511
    0x3021b15060a0611100b040213030c0905070f12050a0b100801150302040614030402010903200103050108010e07090b0f030609030d0f0902010905010c0c05031c021b030c0928 76
    0xc1000b90020076503101d103091004d1006210f484020109958120810001c004105c1c140154009002031103000741d01161166098404024414400a0b8100762950000c042007282c44008040c3c49001c024030074000001c0003085d8040707606526800064004000000108484c181000010b800c0f01a0490820004a610303004000307a200c99401c0c480c0f000e078141801c524003402c1842c0140001104c40b0040003841c00080403a04591080744184009e50300100807201d11003140684450801909012a002a0601c000070421810620607006110030080081001928180c2c5800280c202012200c0c0d022401e281034110325101405020b119490b103602443c0d0b203a45094884040300d28a5941e107850600e440461401072340c100b411303003003615402d080c0b030358000c3d21a15006221022640050390180070300b800c0b2400081991171000925150b5400744c80d030100521030720340700400954115950540c04a90302c42c07410700f082507219402219440e841c1d01d034640482c03281603840034a00380405107140c2da = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 886918003 1250 886916753 886916761
    0xa0f02070f120b0405030412060902040b09010608060f031002070b1e0c120c0c011b020c04051306180f0b040b090d080a050a23070e03120a03021b15 65
    0x10511081000d0001800e00d00708950504010a5400501220042c020414280440c040c0b01080043e64001d000780401146030440920706a40030b0064070314200d00070380c1049426000d074500401214142d41e25961240444e41d00c0e02d0030003181c128421035042c0c150081c0c0c0e00d402c10104560005081c81d60148800007420304146002503259040b080d120f9403054540b8062140c80d400500c101c6202016800c4408440d854031780300e000f8107208800c0c200c0807561800031101200c02c560185202480c40c55000d880381d032146d040c01d01c401e60300121454199075580541c0c2c3d00010b1003962043c0c01038825008540f401c8045603480340c0b4a2541d10000b5161505d042040000304603680380c81c6031b8040002d001400c2e044500c440090202c40c2c02600700002d003911a40050b85c0212198403580325102c2d42d04040720f61890714003403d001071100392140d00000f8101d920306056410000b038150314164040e071403185071552109040380290428040e140d404501d00641c1ca440003000c1060303e034010303a040c84140d40c50034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 886919253 1250 886918003 886918007
    0x11706010501020a050309010c03030e06130c1505090d030215090f0615030307020409113c031c03020702040606050a031b0917151906060302090625080a0f 68
    0x41603001d00d04550040300c10340c001400c08429a07102d0f100a0900410b01d23001890160090001355035001c0003885800100000111b40d0074046411601031400104807686521401360306600030641200491010003100d03859042030200700841c140244142c40203258201840340085005450031034080d03002e01240402118180a9113801c10300a645010321600d15201123501c0b0302506402a1103541d6411203c01480b115650001e804840181007440c05070444008070010100b00349115802e000a8400c4907595030031044020009000800800b607480408030710f100c140510001840425809003c014010780b140d0085202901d155111180c640181440007002c40b4000082c1d007100744149071302c85402a0f000b03030105094941c10700c988a0010400d4119030301d0b010b01d1414034104604e10400708410a40000b0888007500c100040900542e83e0f109412010fa028881401c1d134415020011200c1040c07640c0d4429840344050802041d055006440d94038107a000380e003600020a60010140c0340a91f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 886920503 1250 886919253 886919263
    0x90925051b070f03060507020109080a0203211e0c13170114061f110f07050a0815010b071509080306040b06130302060306130513030306150e04020d020f030117 70
    0x10020700041a6403803805400c103d4140403884003514180d5075a005c520514802e411403095103800c0b890b1140c0c2c0c2d81d40c10340021350343c0d40b10700c00024420005d0298110a09520140c00340240010703803d25456040b60040b6002c0c0c9800600003142400702046005d00d01502092410300030182c2c080342d82843c405440f102400e460f8000f160740e10780305150b810004940d440c1d4055024000084000451000d40d0b0a811b6500c03041d114284c1019106070a4040d140d07610000380c04040d2070064039550801503480c04400d6942c130b0302c405149030801190b4014046040e0301c2025051361400f80102c002c02c401188000c108581c0e12110a9aa0f401c000040001a00302400780300d2a40d4026a0114900359507014840b591101c41d0100a100340f00010100d0041d98401c0b0401c205541c1c0b10b0020051404e0541140b05010303003505c000c80200b8244030f40000c11030303801c4003210980c0c0c40c0c82d12044000d42019040100079405031001031207a940c20301000c80b015050001540c0a03001c144039101d8817407884100c0900e00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 886921753 1250 886920503 886920547
    0x303050901091a07031806021306080c0702041a3007030f150b03070e0106021513150f0f240b180a0e040b062409092505 53
    0x41d80c106001c510004048440114503d0f0107400e5810083e111030804030080c05e07507800c16030884a01e42c0c403078505205055004284000320880301301c03680c1d65108030940e83e010b01150701c10700d13102050010320094100f80d000710030b60b0403000c002850100c041c80c000548445d6801d081c0e0414880032001800c0030002d045046000541010003020290b20b990b42c1c10b00300389030106004001a00e206490b1a032802c1030b801900f05441c0050580c0c030780644400762007000700310174030070351005215014050030658100c20241e8060035145005410340740150711400e01880c0c920060800a0350390b500c400c0700d071800612402842c1d51201c0c0020401644580a116007410100515001041942c008106410f010030403980c10345884092000e0340d01d1050300090780b44846500800d41410004104020043d086c9007051181c00115813444165a81400ca410181d01081160110202c10030400400345007032480141d000c07078240004184200268100152405000d510101246020070001c03282ca6801410040d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 886923003 1250 886921753 886921771
    0x1b03020606030d05131707030618050610050607020f12070f05090604060f05150c030307030c03050a0c0203041208160f0506090f0a03030908070c0b0415080108060705090d0c0e04030305 81
    0x2080004005200c1c10348081c8200744040226026004007490241f00420086400c000200a0090700045211640c528400c00700c070346001d80000200c4144c11201e02e10141d45016143c10f0030320216600340600b80c80c2c101001c0d90702c0a40d811044c0c5009a080000801800403000c50006c514505014006004030207403026100308d0500d002440346030340d0114558101c40007240c0c0b21000f640380c80500c281d18403a885031020a804000100402c540c0c06800501d20508203030303000c01c626038075000c0f080c0480d03903004500030040c0c008010420080122281c1c490416008111113440c0074640b202880c1c0b80c0010240842e0750a40b20030490003402000c0c4890fd030b11800c20030150000380458116180c5803100080000c4c1895913400400040c0103101c410340d500c46510129050319140c81ea03c843e45a50840c1c420003c004028051140081b8442d80c0d03003504865002d00144000d80701d010080d20703207030001c045564001400c101240d020562070705a0200500754504040014189410002d06a0300010138000c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 886924253 1250 886923003 886923007
    0x30405030f033c07200414070302130b1201080609162903090f070506070803221203020c16060c0318091a090a0b0604090203071b03020606030d05 64
    0x284031030315919404082803002201e0841401074081c090a034003c0c10300c02c02c0480808951442004040010f1205440d03121040b8611400010200300989104290b1b0807011084800030843c924000e402502d031501e06000c081d904151681580b11180c4c01007a01184000d20403001040380d024240107954029840001a141c0c14070b00601003942c9603130f907125507545410340d58004142000350013400407109410340201aaa0b040500d5050ba0319004912104540c2c0120b03000001c03185440c0c41120a00d41c0e02c03540e00ca04665400b21a0303602c445851070b14120380540b0700b51041c0010f10f007040d8003800e0440e036280180c803460914082d42c540006c1480c0c0300b14030603440c2c005004580e000071801d0030036035140c90000441003482d20b5000c9400249d611019003181032046502d4402080b4940400c40c000a0310b140c0800c0c1e03a016031960541c3d8040e4481c070340103070003044240100340c0720790000d59214090f0b082c40c2800003100d14070f580340960410b9050b0700582007007050040a20b020b01a03108000d6851030a24 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 886925503 1250 886924253 886924267
    0x110102072609061902011b0c11040e071403070506030c0a09050a1206020a121107060e15220f080306040b0a030b220c1706010807080a0b06010203090a0305030405030f03 74
    0x59014444c602d140d00740001300320003a20703a55100750080110003014071140088680600f0000d44002d806c0c0c40100d491070031080f09007120f401d043c0b00301a20422903030000c2480e2071800000791400707203560f195103800d809000030101c0c1ca6101d42008601078046908410303627890350101d00038004896604201d100340c6900b1002c100c410403401103101c040350018801603031000008000c2e964048103408001c41c950418600350f440c0c80e51003000e052518042c0e0303005e01a010304030b502a17031a0f1a48224030984111001d01040c0000020404015010300e41480404122619110b21440321000c0300f007103403103510000c10000a414240140011401c05540144d10281190358031410b05500500c84210312203140e015900040e00300c020b01120f00d070010310300449251036048880c0b0103400c00010000500c14080000f03400100000d0007011905d410018049501c207550303a050f5050401b501960440c8810301c50001e5035030f6038541d4030000707611650003950303110300e4007041c107081c516405000f0707190307800c00c1c440302d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 886926753 1250 886925503 886925509
    0x2010902060d020f07020d12030b090621210406140a0c0b0a02040e0112120215010317040810140601020c0913030507080c010509070e010305031801110102072609 71
    0x950b8040c1040710000d6100ca407044080c0000b40102c400195009094032030040c148603000c2c440b001c46c1202a642030140411110501615950a803011030b00915a00061110052143e00701501010b10034291280c031042c00198903880303454407a00c00c140340d81c0080c040262582014100030015210385a0710300f00054214050300d0780180d801c1c050a4800c141c5c0010740741711501d50485015000c0c0500040c3c1650b140d103c188603000c7c0046007101c0d4503031003404c01181c0fa800080c05c95a02d104003400d07034402da800c40e59545203d48080c0d520780808542400301062403402030000c81560640c616000401d4401080015a000c4001d07010505540100101e07221503100e421520341e0008600741a043d50b03415900d02103078a0300c01ca11000c0c4c01408089a200100e00e810b4001d0340c01000440c040303d039a143c460080c50b0160320300384801811a882009414101d60000c040141c0b402d030141090744448403c4042507003607030300c40d0314110380032815488140c0c1ca01e080d0824002942c0300c01c40100b0304008110b404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 886928003 1250 886926753 886926757
    0x60905040522051e03030103020f0a03051b180f040b010b090102030d020f04030501022a010506090a051e011811070201410d0e011b110a0c0e06100201090206 69
    0x4040810b91282c2c0302c00d050060410840c031032840c5100e6094241c4c00907080f03098590f0401c3c0030481c80b03011481940c03101850700702e40150640740c00101501050034501c003204c00501034150b54607084100c1c102d40c007403040a041c1c40140b113240714030620009460513240c280840c1c241600300d4481e000c0305214102050343e001056404085000a0044e50750200600c8043c45000355400184107600018441e40c408606d02891034030028103480103024941400e11341c5098400c103c0d24150030a40c00400511103401e07a400075038001054102b9071000c52101400441d1035602608002a003814094500544401c54816942071008030540b09007400d20550008089180320608231422680d82280c040b0710b132200c1d0070030005a44410408403140ca208440d44112500460802c8024a19045902e40310304c1c018012511001130905014210180d030000503a420342010180419a20400030504000341d14001f09201528104500c1507003032800404102407040d200324028111790402e11004016117030901 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 886929253 1250 886928003 886928041
    0x1914060d0f020c0f0d14070605250e10081b2506060302010806060a0c02061b0105190513150b011202130807091e0c1115010609050405 59
    0x845035503a4012018000250400c20001107a8610000f401083c0c0c590002c0c0403201035a01900740c2e0259000c1840a030f40a101c4000700c0f9103103240c00c0150000140c07841d44201c0c1c0c44002c81942d140ca440515030a50440c03003c0c0030314070010075002d0504a0291501400780311140300c413440d2410305450003440860b00103c0c0301d15407600519021030500c3c02c07003108500c1d0010218615111072243c40340e500749140a0420b034801a13010503d14000318150b8200401254401022a2111a00761510b0381c01d04c043c0b5800f00c209054048040070000c5078942d801e0003680e02031002101c0b290304109005003141c0031140c000d00f41c14114036507800c4580c005401c0200f15400034121080c00151000c4280041c0d0ba840796407038042d0180c9200142001e501c0c0c5402c4000e90540e04070f00c00321101161a000c060040f90055414003408a1800c0910b40c82c0c2d104640001c81003180c40e10b0300d061003291500a2500d00044900c0e00d200400c039800061008640c4845204000c3c00101c8003840182400030030402c41a4406c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 886930503 1250 886929253 886929259
    0xc040f110418230609010f0509060d03210501030203120415110a21020d021b060702060d09081207020303100302100e0a06120609020406020c13060509040605061914 72
    0x650640714207109584000f0300d040012a5600780040001c160303404010040700e009104010580010541e05820f42c0c05100352203025200550b6503d403039040280c8100c030380b03c080b42001140511000c03030f041c0098000b4140324000314045105e5041d4810981440d091202a0183c4c40d000e00c000c010280410020018802ea2403c119040b03501d80342c0d4490401c0c0360001c02504c4084a244c03140400b080c2d030701814007490195401d032020005503407002c0340c480bc0320008210021023078070100c01d040c0c40d011005024941c4000d040c0791411016001040990b040c50806503091040407401e00360b521101c02c00568040140c0c4041c52540c5446105000a60141e001c064014442425601103c6001e400e21007072105006107a916803543e112402804580c06001d8058820304214000515541c10700913103080d9041038001d85040d188440030303c20551052154843c4207038a030728000403aa194400a180a18018200800c8a14041080c400060700d848141034050821078000c0041541088699403402c90403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 886931753 1250 886930503 886930529
    0x70c0b07060e010c08060405090a05070614040e091c0f0c15020715240b030f070219050d0e0108100504020c0a060f060f0b07050c04020f0d09050c040f1104 68
    0x350400c0d0004100300c00b00308602d50b20702981c4d1429203405c042d40a12814080704c0a01107543c829401c180c444480d454014000e601486080c098103000e8400440c80301d0f0303003c2c121810166150032003141031505440440541c2c02c540c00030080a01ca0410045e0444681d08110005000c03003000188000700c040005000755000008034012441207030110b030350040c0c103c0d180c2d948059a08050340002d21951041207000200e03400d044c2c24061403042400b0855411700d0b8203c2c1196900c600c00090380c1c01c000e09580450050045200200d840030101880042c020002030207548036110300545885002c081060502c41801d0401c500d400b01d1620f090203640301900d000d80c483c0500350307040d4500302c02054002c04090401001100d03100c1c160f88600c040311040500241d02d960f0390150440301e4030400358060016044810520141c0c00e080c0c0080c081c1e1007000c6822850110318480c0c590468605000c1100d60f90000c406090701440e05003c1c00050f0a621001040401da4403c4000c046101da8402c00d4000e01031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 886933003 1250 886931753 886931767
    0x31507270302190506070303061401030b1e0103090f0804060917030a0e03070b120907050105130e1504020d0c0207090209030714041808072108181c020a020406080102070c0b 76
    0xc0d403d5410010b040103880745803551a94074010700501141c0c00350341500040303801c0c2440a503200380210840380754003808825070070070000e00c1400010503140c2e01905050b19501c980000600002041740d4050150018a0b1500d04040e001400d00085a00030010b01c032950f20020000c45010007125070b002800d007411000c800c0060b0100b0700300340c0c1c594000004c100021601c01040c42d100d8404512071051001a150000c1c0c030307100103440d28064040501a260b4000384103001d010110401550818005190b6040c014403c1c070008090340e0220200c0520252180a02c1c465030b501003110001502c0e0110055050000c030380f022990300c0c0d809101d01020f8900d0380441c04101e407503d134841c10100340c81112884000103e802d15403c41e0b03001007002c13251680103e0080070104030201c4280d000180c5555500050348400c0c0c40701040c42011000349102e030003010252442040203010299200038181c024028807a100d00401c02141d003542e1040040d6401088081c000842d204280d0058600344009d1948882c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 886934253 1250 886933003 886933039
    0x1021e0d050a0b0f09180708070501110303010e0f04140615010e090f1f0f0321140418021306110c0a08150702030409021c0516121a031507270302 64
    0x2420341c910341c11a000790b540c0448c0c90074012a204003925000c1c4c90340c0786401e0503618103a80d41e2009103d010700d00a0001c0114200e4411001216002070080d111080f04040f8900c4007410841c0554501110260b4000e00700050358104001308003020007190b20307010703d241c0441207405d805c0005007214a107040e44031100029001c58842800600710100341030f070340552a445c01001140307001d080c01074041010521000407038811214030144458000d0745a042c2440c1403601070440c070707003a1003000c0075a40910460f035001d0040008140145002d40c0d6008068180301402c42c20540000440c5004e220010b10511802c840040e01051075001c2040182e1f15640d0214201c0c2103008076080282c2003400010700000070700d0300c065800040301b6030070800c00040d1140e0044e2445451030340d80c000007003011b03038048922807902c540c80625103415000003c100c845c26000041c1c20441400e0106041e0b018410902c280a0750020385010165a450b800b242442c003040c1800d268110544002445070a0100d501040a9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 886935503 1250 886934253 886934281
    0x305060d1502131e05040c09170c01030605010302130e04020619080a0c030603021c0c0b1b120406081504110408011d010c050a0c0501021e0d050a0b0f09 67
    0x40c0e00728550030450580085500c000c3d5000f110000410516240013040300407204010300ba00000c40c2419402c02ca241909100190604010b89024890000310005c1c60000c00d0404c18164042c41000e0400369050000150440d2101e070001ea041510511650315040740304008036041e100607100b00704041d80c2c2c0e440000e09900c40d000400201d02c40d45403840c454240c20406c224040d1161000900840310317910001c800f1108184806948098842c024540c0f400c1c2c1903070140c41103030061200c0c2e60966118010101541d00c06c02d080d141e6148000503000541c0380911140c070341022221600b0b8a01494010018824070001c1c1103094400b260703e0f620212580d50f584a90b520358403010216445550300da010500030854441c800b04442d000907c0782800000602c10b1000140113512018140150340074100c4003103e000724201c2e2190342c00c01820102c12600824000c0f88103903024550355030080f5911290966202030300030b00f509070400794041010342d03425034182c002e03ea0541d088602036456501031140b070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 886936753 1250 886935503 886935529
    0xf05010312030e19081804020f0a02061303170604110f0a03050a05130828110c03011e0b0f0a140a08010203221b06050c070e090703030c03090905010b03010f1403060601030506 77
    0x3880010218105200c0002500790440c454080c0c1e1033a984a1010302c103640c04802c0000c00050304c100460003d1003040550300d800030005080007800c0d002905c4240e91561000340c404440407000300740d0120300c6d80d05016059010403242d01c107200d2401c000564403401010140002c01a6101040d42c060840e000b90303282d416001c00040b40c1d107010b05c1c003210245c40c0340f011300c42c0000e00d8000c04101280c18101409080301c002c07450341c454040c007185600280c1c0240f200c4c88a669001e101c80511001540e60304d030a40d00034095102030100e0008220003000f0000031107a00603150b5074018001c021201c0d2120503d02c440c1c0405c000c809640d1181c07481c003407130340b00c0402131181007800100a0208800780c0c00b601038900d9121141c00c440700f498844032901151042184c0c50401980a1031301803002a12803191102d0390dc0c1b01c3d09002c01c2181d00d6800c0481130341d009802441402c1008001045807031b4032a2440d078001c207124032086c500400654042601c0d16001808a4140350b241c034007280c0e10b030716890751080907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 886938003 1250 886936753 886936759
    0x12031107081204020a2c071214060103050108240414010207060509010b0a120213021b0a030318030e010c1b12060630060f05010312030e190818 63
    0x9202110003103000d6100050f14140d000c1e25484402043c03003012202c1d651400500f85500c880200c095183d40400110020030314420010800c20100a81c556030192004510300d41d205a455881c204000404035001644017031220352105c0c60080044640c10b0100d040c4d1421420500340035601c0f400c101c0f1a10003600402009580f0000b942c2c020301000e680300e0b41c01146000700a2003403040c41c500300444071043e0f00841e02540c5079880c9050040ca0203030790b009004001c0d1a405420300d00c4840d8410010780f0a6106c08005403c401180c4041507030511032000320b2035101606200c3c2e001d050310000d050b203014040607410300c00c1c401066028032240500380c400540840c0b000b0070002d07443d47c0794a02d513545040402c541071801c040c008a013601c1d48803a002c41c00740b01c0000705041419215010a003004207840261400c0303543e004000b8288644d070090030701841c00756080c24035a0440c50b40040480343c2c0d1301502125500305030b403456036a4034032101282800d900802c6607900ea00c02030541010301a0240d00d0941c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 886939253 1250 886938003 886938007
    0x209010912050d0f18050405150904051605030303190b030109060e250b0901180305160e0f10061128021504030317180a030503150a031203110708 64
    0x10401ca400036455041c0503c55903200220040b461003070780e00c2c6500707003841115915448028400d40c00c040c2d01080d808100c15084051481d070398004110417180a80b0290f64036040b54900101c080c1c0f003248010f0049c0b10560007985141f07041c1d03220400b03414408030b2081c40c040d00c40050101980d001d4111041c100e030001010090b480026204540d40c903a4240b44025810100c214403143e4100d50302108225407003100c25907c0c060182c001101c4001d8890a002c03c050701110020011034070801c030b01140c0d007101d00c8262003000c1c101184012400002400442541c1000041042c0288241448400c0b64540d0038218522000400b50394144281303840b07842181100440b0350114143d0094054038001d000351030341580390080c00e08030b43d01c5200c1c030f01000c1c0200f0794100036040d000303040c1c4080650200b81d9907552040040c1c443c04039400c180100e02d041c7c00041d004018011a074202105000c03c5100440340b41c016240b55507a402d00c0b030700345d0140c24014903036144039003403101e0480011201e400d640200b40c82e07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 886940503 1250 886939253 886939289
    0x91911100c170a09080a02090402040b0a0f150e100e011101020705010f0204031101082a040e160224040807030504120510180f06050601090803120405280602090109 72
    0xb0610b400211094000070000f00001582e5a070214000c80b82580242c007a445980e1aa02808054444400340c1600034490a6000801c00d0f48040d480c0c0241064900030000d600504000030301c829206c000152160398880c16031419150840e0706081022000c1c28411030203510b09240ca0b00a0258000c042c01e6942040c03108100382c01a5401442940d1080354440c189400c00c0b001161007103070844803503518111800b100800b050110800d0041c100e81581da41d80b030140c950802c654044002d4030341c1c8040c5006125680c80494061102e03160f40c4840d482d4000701c1c00f0780c1c0c0c00d019620301000b0300301800000000489000f8180b1610443d00944800c038066142d01e4000d1030199540c0141c0c0c1900e00d001f40c64450000f0701c403050b0314072011a41d5080802c0580704526911848002d0401600043c1807010181c000110250284050403015a1480c0d0015861526060060810a44c03072110110801c002c0d0099005060350050004604e8000d000180c40390400350050b41d401c0300c5038100355202c441c00007944d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 886941753 1250 886940503 886940543
    0x105011a0d0e190f02030706020a05070b0702030a06020a0309150b0f040203100e0f07180609060f020a052a060a02120714030403080406031a0a150306030812091911100c 74
    0x1390491510a038125030040f9030b41d80c0126118414040c00402e40d400148040210216900150900070700082c140d40b4038045039941c4030100c1c0e0098400401080e10340d00c4407001d0110708100244004003d11007881885841710014102e52a80031203244240e6022000ca540c104408a0070fa01a000004030301d07040e03040c03641070100c0c00d1204403a5a80062030100c2d43da1882001205004100c0c1c0c055100c810b9102c2c00d040e802e550040001a902c8210b03c03c001101010520400024080d2a202485064204080f2094400001103450003a010b42000c1001401495001486001c030204040c2c0030764844400340350010341c146a804218403e0300c408a4080144840900180708a80c0552002c102a000a203001b280c80f2440c48102544442810410441c9000041100e0700300119840c1c0082c0e07040d101d035601030072034000000c403882d140c941d10100004080b040011300b2281c07464100f0900b2507c02ca41c3c075a20f21b42c00c440c001a0041079407400f0141d41030b0048620200e0203921541c000342c5035000b0580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 886943003 1250 886941753 886941773
    0x506161806050702030f010603110d02040e010507050a020c0303030112060b06130801021b010c0f12020c030f0d060b040b16080c0a0f060b010512040803151903050105011a0d0e19 78
    0x164032038021b503400c51106200512a0f44100d81c0d100071012394030b0102200300500013503201c0c01a6040741d102d862661180c0d0003072150b2441200c90b07031941c98a805252100900e0610600e0384d4034001da1040005201e00410414955201a4412000715041c01d682d00072583c41e00031448418624250400c01050340101074024001c4940009095001100301e03160950980d5071181c2d901021585070404c116403680b00d045501400d155400d4054509000c04480d00c1c65a8001e2541c44e004610105003607a0103426406948000d0080a070141d081c00d0034180344100d148280900b128025221407951010040035009403032116440c05c080c2c41c1d5000d15030034040004807a1100480c0d006203080794400c0381d0742c020b81c20354101052031096412180c1e00c564413100c0c1c591000d42407038202c1030090b40e001140e0341c031303e40406031010b2512444244c4038518034004e07080d6070060b0000644800080d4075070700c202003805d0944601c404001000300c0d00e00000c010300c6041035082c01201e040600c00181c003005102d13003108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 886944253 1250 886943003 886943017
    0xb040e0106120504020d02012703080912060c0301060c1a0a050a1d0c1e030a030504170102031603201801090902030f010e33030f0a050616180605 64
    0x540b0b10551900501c2e21040700e0084030001e610401480e29003001d9413145208980f040c0401e0f002c041064440c980c00c070380301000c55004540d00c2d2000100a451414140102d50b100d005120003880242480c440302202400140605410441441e4002c014031184000407d4201403000400d030319809e103460780a0181c50203d0f0580540c50a040000b075030040c1e012100408004598080c010b00500030041294001c6600c070440841d000c1e441c041e24031039406200f890b000c2171198548c00d984500c0c102050403500103107405240140d205004100040c4401050300c1d00b078980394078001900110034003040640c803030441e000c059070b042c2c00324800c1c03a594901030503244120303001d0300c5000411380e48030302000c01c1c0e2100702c4090040040000041140e0008510015000000c20550442da039000141d480030160010801c5200001842d0b403d0049050a000040d0791404141c0944030740261a1600c42d55144040c0807010385c4601c850051202c0d0703104035848181080c0c60b420000820765241001001500450 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 886945503 1250 886944253 886944257
    0x212030417180415080304091e060e0f0912030a050a0e06010b130f03021305270102030106090819120c2a1d060d060207061b1803081c060b040e0106 65
    0x101ca00501513039080e4455044810960055107410b080141d008080c018520481c0000501c1030160450300d0a2400340034054140c24024031400c0c5020b002161107458080e1994005801c010040824003109900300c0742c0c800c80149000c06c0079122818058001c2241507501451030140100100300c01003404010000d603507100d101c1680050700d5907074038000d070b5a05220007540425007a446c04695000d6170006680130074074680c1c454901d5883c0d09807809259914643d283c069500100601245070441260400780c040d180c0241940d80d01019a0316180c0d02040000c4d1202000011501c0400e11804103118110740c0b000d000703001c490803802a241800b5840b40d48200d100c2c0a420b000c6144603550382e8031034000c0540e80b10003c180e26036009000101402d2001651219000c001100200e08035016400c10f07102c0e000002c146095001100070700903a042d00b844c0920040f0400108045a071003c01d48074000e580c22103003840c050018410100134059641b000c0ca8400020500040003415500301c141250703031076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 886946753 1250 886945503 886945511
    0xf102f0d020c0102061b1b161d1605091219031d0d0309061b020d05030a030e03210c040f1d090114130213050109020703030b040c02120304171804 64
    0x1c0300545070400da6003000080c10090007c0865074240313588452560745140c0954203080383c00580c00304840c0c1203801c07017051107840340c03003014800078410b140c3c90340422100780340c004481d000900102a0b106003410648220304840d0701e508612814002c008000110f1030380d01c2c09920b064500540401941800c5281e038229240741105141050300c501648658550b0b04e60001e50306206060355181956100700c010140d00d81c02c101d005031070300404140e00501580c01942c880a5103071001b0107031030041c41031800ba60420b0000100b90700c034801e0702421070751405942110782d660700b02d0840c41c2405a0390082d803902101000002340c030011306030b00ba590b1844105081c2325650310f02c11018269076101c0701c01500030300311200243c18120002d900381103051004102c030055000b034034440300540d00c0a800c1225810350014209041680602c50360740090340588061014002100c0069101d66a1441d50350399540c00100190800400260314003d15080c070100030317216907400c84480042041c0c103c0d0700b030040d858 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 886948003 1250 886946753 886946761
    0x31f2316090f12021503240d170a230903010f0605090a0b0102010e0111070b07020a0c1a130609090f060e01090c05070f0f12021b04020c1e0c0f102f0d020c010206 71
    0xc0081205140c01000900b410307108150b000340079502c00c1844a040221165030903440b130f98482c03100008200c84403005900c0d332141e1802c141c01c517224002a50080c600e403010400c82512440304d0f5582c03006010a0000700030107010300503405040c44186c3c011841d4601408045415645c10250011902480d4010180c4da11002c00341d0743c4842155020f0202c840003d13040000d03564080740c00910301000003105003003854885050000d800c040c3c000354042000c05005100040786441030000e1040401030034481c180c684040d2090b03004040c080d4603160741c1c450400809040c055011641c504e5440162050307484000e003820000300c1405002114030b890403258a2145038400289070195255605c069991440503504000c000d510024440d4031500a00314401082c00000d03081800b5001d0100c0500076543e4108104a407801c49005440d1050018900c2d4500007a441009040307040d150b040707248424202c82c480d1400398003141c5010280d0b8451a104000415801300320800c04003800e070201c0f001912 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 886949253 1250 886948003 886948009
    0x220905060c03011815120b0405010c0c08040506030a020f0408030403030e042a02070b1804150602030406050f0f030903190e031f2316090f1202150324 66
    0xb10070302c5004031074009000081c6842910390321164540780700c101d1002515607500440c5000309500307802690000054800c01c000c0c01000e001d1613640d6800c0345042e101143d915540ca0b1914041d9010b0540690030101c00142e0b41d080542c129110441c0282c0c00e95112a40c455140d55281d101c1e01080307000848007141080182807a01600d4036842c2c80e82005841ca5004021070503440c08026120800c41c4600400010242c2072140107005040c16a907504482420035402d01041d20412000c4124004100c00c0c104034459010090728189c4903c0d00c2c1096841e081685201c03128000c01024819820740002403142001001000f490303d80c81403480d849405c0003c80003560400100d500079a0140c002c0ca138150b648607103c031040e030320201c60f03c0d4001418081150500341c5000701d2142c003e0009070f40c1400e02c501d1545641085003046030f44e160080c1c100d81840700200c0404201d200c2c008000341c2c007000c00c070115a9a80c0c2d03680f8484000c80c52944d2a4070b04040360a980b0b10a14510f00042c1d8480b820940c8039003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 886950503 1250 886949253 886949257
    0x8070c1a0a110712122120090619020a0c4707051c03050405060112030f0c03030f0e01061d10060503090a1a06040507030203130809220905060c 63
    0xa40d4880100840c2c0700a520340c590f01c2008141c00d501080303000d1b00300d0f00a403200c450100d4201e400741c1c400003400c039604514908140c0341c0445100b180d17540031310498840d50390381003ca0b2140d808007048810f490052810a030329145401d04020103102204c0c5c004941090030414484e204881004130b080041d00892174203802c5412200c84c00706014880c0002402a51a400245100c074030900403240204010a89903031814032034a070840000b03071074400384424403004200c481d0241c280507901e02c02075405541d010308000700a0040d03074203015544980d2010315003c2d0b07102403200908400103203e10200d402680e8000c0496015000c0031402e40521004003201445280e48201000e9060b0403d060801c141500c0d0783d007008054500d80d20440c8403803400202e041350b0018010062074039240315030a0400400042d5000280a041058030500030002c44111620b407441c3d82503003160031141e55404100110783c1e208401302e640901c032108401500c5a0785200c3e80241039480c0580151081034441107413078904e41c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 886951753 1250 886950503 886950509
    0x1404060c110d021e0114120105032109010f050702030619110406080a050604020403140307061d06070e032107140a0b040b0a0906050f1602060c040308070c1a0a1107 72
    0x440b04c02c035140e030500f1800c91009442c005040c40291040807140e64000d0394041d03c030040208680d2401081142000c004000101220b011600703040100d1074085c40f458040d42c4860382c1089901d61814083d0388c0903d049441c80d5801409880041c0f401c0f0454039107041c1158801c0400300e20308a01001c955000d82c00761802d4545582d52170140ba00d4030001e00011341000780029a11035400c02000002401c0300518a10f4603030713030401850303c9400c24100081211003500080c1101003072a10403200d040700105606270f000c48541400c1108010703207004a85080d0a00504051842940900c2d9601c03254401c01381601d030f44203810300c5038001c0d105070303040d510f80c40c840b03c0c01403580179030f4400309001a26090949500c0001002e0000b50400b0545550054480c26140607022135404001d102e20824015044141680e840c00105a2130810300c0d0811000c1c130451001500c1e02c0d50108100040101b01d40c0444002c0250780c140421604030f4220441003a0300c1303000c0000c00300e03070001c090300c0a0030004600c41c011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 886953003 1250 886951753 886951759
    0x2030f090d090902220608190b0607030809011d010603050c0d0503030612150f01030312050403080c0913060303090f060f1211090904060e1002070818011404060c110d02 74
    0x9050703c0c000c074000183d04800020180007469403d880700105100007554024010b50341c802000b8100006c4118141904910741500242014829001d80d12608101c400c100d41c0342c81d0040d0540d98030640130b40141031222050351001e02e624078400e050b15054001c48207581c0a481929000c800c40b00410090601c03400000702181c0080c000555035240c0351510050310302d600000c4c0c64082c0384800c0070b190008811164a240007002000500c04d1503882142c0c80c0a00c0070040c020085400c0caa200030301020030050518004041c0058081143c4d141e9410809180c41100c5090000a440b4580542002140d010380c602502c10802e000858a00c1100f800315a80a1500c610380060314411040014107002c100c0c0411102040215a22546a07600d0240c46a401580001180400800d0342400c00c21810300f4040341d140140302d00d00220300340004480c400c081480d5070340003044484005940500b0204d8501f500000d020400198103504a00303550201e0b403244000c20304a00c001402c0100c120300c8070b000650 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 886954253 1250 886953003 886953017
    0x415140f0a03030f051e0a0801060e0a18240801050915040201120219030903090906030c1202030c0306090a020a050a03120305090c0a090603020f06160f1707050102030f090d 76
    0x1003c01d00400000c2e0b003070502e40c030b80385150848010101c1d103c00040764901081172000a11000d01d56400b2207003d014107014036005ca000540c1400140111029008000c019414500e0101500c03200fa03101c0403000301500f6881d000c0740d0740c00e0107050702040c482c07181207902d50a00c1c000038240030000c24902c0b10210300142c495070b29100d9400445072207401a480c101c00544c00c10450025519282d2914110f004964010032844030500c0c1c01003080010303074040f20109080c0034081c80058001d56103d07040d1400e190341c018070f1800c06c1c0000703454008181540d075014000e810900c48000000302e100d121040c000d913890000030303030388009002c07042000d480046c0920052500d1101d469110b41c0200350080402c5080300c1c4008240c200041000015030b02c150246560b801c4c0400445c00c00c0c0c0c40300d61456004a45181c100003401e01e00000880403070f540240300600700e512000c10003c0c001c9010a030a170310b91a40300c1d110789480c600a17000794415100700b4801820ba6001554058000551030600859556064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 886955503 1250 886954253 886954259
    0x207080f03043b19091202070f06090b090415180e03092809050c0705071a0a1404090204030c05190501020c040e01110d06180531020415140f0a 63
    0xa201003c060841502d032444e4400840c4d5128050060341d010303034054250407010311345a8401900d84411540410f2040d010000100f2126810805440c02c41e00d000c1050341d56002c0800002d402002c0322a0004080e0380403510110742c1700c8030607040c643c40602009040040b000c0c8d8484940d5607000b9015203c2d032040c0394013a441c4e0314010040035400010104103100c0e06654031140000143ea804031124080c0400100d511810b0120400101c030060264551f004940701d40c4081101132071141003c01402d0040413445401007080400c2200e00a22005104549494580c549842c80d12041d1045910501080c160200d21004a800d0318084510580040c0354007076582c0e040c8405001166510384255507581c08903961031b41d8010045c03480880c4441c00103166403c01044405046200904203d450310703140810043da441d90a500326564010552080072081e1080800c01055400e40029003003810080c080302c0490f180e60541c800d95086110144005100600380024051070751021980300042070810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 886956753 1250 886955503 886955609
    0x102070302031c0b0d081804091212020c0c010507030215010e1e070806130207060e06060a060906090308030a0f090609021e150c0a02100c02190b0304120207080f0304 73
    0x4087ca500300d00410440851084001001c8840c0c40400f900d10706580c1103482c0301c1650000312440501e05400046003814905440c45585900340781200b81840310005030001414000c02c1100c050300b140181c1c00071950303100c0380341200d1254240c0340e202207031510011240d000090104002d2065490795942290b90369035a0400100c0c0312441c01864030581e0802c00d610108007140203076080c2c0c0440b0070003044182046000d011008016500c48030401a01000a00c9003542c0b000c400801c9035001411252203846010940340280941c50b0f0f0007107414a0411040d003000b01c660450400d09000729009558040c00c0404c08000540c44090540c0c00500580f4200301ca03600400541444200e04040391491401c65010800f294a111004404034a400c2c28400c214900110303503444500d2070001c7d01a0051504000e5825808003610041401100c0c0b040ca04c0954030070010312005040e41011035021203503006410707407254000d000343c2201844c42d1000d0030070025441c0019240c501c1c030b551b40d4040e04800d4030035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 886958003 1250 886956753 886956757
    0x80705011419050c10020304021e090c03090c09150112050c071e020303040e0901110f0a030507020a0c0f090f0506100f18030c09051807050d0f050102070302031c0b0d08 74
    0x102e6001d100e428040b001e03450108000c48111920701c840016603c2c10b15004002503841d2030b122a0080088208070703030440346c54600000350080310704072800707450343c030b406500170f041a414050490700010b04030f0412a040c81001680d01144500781c0704c83e411460300d0011603080e14011580b1018880040003d60002031000200d01c04180e00721240d0303e020041c03503001078150351182d4070818172a41d80c2c0c000d00884180a20440781d030105030241040c07810313282c030500455600030201c1c2c0405042d0f0340c0e0300080c0d60a0092116004199011012003441a20364200d0081c00002e03005650b81d035490030044108244c40c6e449010b000d0040205552001c2d032650307008540c060582c0162000700009100d030309030500100d1581001035071040059041441c10940b100b401c44200628001c036008684022545001c8041104c03400d607541030754211041025070501d003003c0c0c00c12160007001c0d9880007400030141640440600071460320b800006900003c0f40051000750303140ca4841e1035102000b03460070340019060b040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 886959253 1250 886958003 886958047
    0x1b02070b0d02070c0e01050102120c06070804060e0604060c020d0804020a120317010909031b0b1906050919050108060717130212100606050403050613170a090807050114 74
    0x4003629084455940103440b0351560700c0488817419020060090f5078060000768000d92464481505004c202040a52749406c00350558041c850b803200401c05001c690307000a03424082c58811107101d1300301032510030001d0406464a00041c050500c500c4500c40c410b4050902075500200300056407805e02c024450030404c2c10034120305014030b0030000700702c10260030403541c0280310300503001440f040c01d410301800d01500040c09140700494001e024000a4000030543d4101038400b442c80401c5107490805001045130740c00c044c2d4424007980070841c0d100351200c0502c003200c4003a4418403103039a0350b03906595038a5081d241c080c0480d400924000c21a4100030560754041c4041c0d000c00b854100c20740100c0d41c404002e080c1c160741900041e440311900c280070b0244800030491440e1403880c0615644806444103000781c900d802104111014400748400200b00614005000300c02640c0d500000074007811088132880703541107900520800044660190785401c41800100d00c0d040d103802c41480320a052024941 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 886960503 1250 886959253 886959277
    0xa06170c010927270f03090b03010501051e0f0d02091c05191b030317061203120c2b0b030a0209011e0b1306020f0d0c0b1801050c030a1b02070b 63
    0x10b80510076005042150a0249016a00417204810350b414010040c51098000c60240102040100890b0f41e10100315000c00401c0a0240e40f0000c0c040c0c80103e00344a0b0281022030b00d4408224000c00d1259035000340412201158a01c1004025000c00300003c0c1c0018000390240d004581c011214850070018030b4999403040c0c92214104064042ca1071190100d5003007900095100207101310b00010302110f441c1c01c034030708541100540c50f03001f280d60366038480e03141101906040c44c0c0121300e010281d041614000d41e1100900d4000d454080040d0316804240c500070422107040100c00310700d5050200390807044980207068104960308140c06118400c5981641c280c46c2a10550002000c807400005010000412020380318001c0c6003130402880d1012040080c401900402014015507030000030041d10241d00c11803881540d60b500c4044100b0600c01700c01d116031542010100b007201d034140700007544581090001006040901c0d14507000d9174030248045005a0300c89079050004040303c0300548500c80c002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 886961753 1250 886960503 886960541
    0x31029070807060204150302070b0601020714130b12160b03060a0e070e10020d02010b010215010e1b041206050f0603070e0606270f031605090a06170c010927 69
    0x1d146c1811280c1a156055400281d02042c498204003400d040140c2150003480100845402c05a41108a5012070b50840c030035024085401c400b00401d4000c0d1200800c01007513232046400d417002c40e5896900b1342194103100024108003082d003d59440039070b0300407070000d44098800d6050000321000420054080e00c1400039000383c03400781e6034420b07840421043c510742c064a859488c250000c0d00b500c554007021030664010402c20040ca0000c0b001d8103044684060310f425a0b038a07560022410001a191180f200032800180440c080c0400b0303410031203140c071030f45c002c11559541d03520344000080b05446041c1d16130410314040040b045030070300d00d64204500819082c581101008500ca400c5c03042c20442080f107000b850f500c056841c10a012a010f00c6042c2e010700f9803c3d6000340c808440541c14028148a0450140400e18600030340d40010082c040350400243c0322011045500c1d602c000d12104940019001d007008101901801c403020048080400c0540c06a82c06540130300281100400c3e50307028a0300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 886963003 1250 886961753 886961759
    0x20a23040902220911060403170d060b070b1014030c0d020307050604120b070302030c070f031e080a1d0c0d2105031b1905031803031029070807060204 66
    0x1180750461450443c00a000a0004440c130344503107a00410b44413244a040107000400214070080e00b011403910341440615500c2d0740c0000d924005003040c1d0002262080041031f0030003004806102540224110514214915a00d42c2e10b4602c000d06000080e401d174011014003046402c000c40e00e02401c0344000c058588468403200812410381060740400c60403414406a28103200b00d0724001d5810072403a241c154610704d800e01c010080d0b84580100144501c1d69030305c400c42414460f081c2610b01c2e0401445032160800c0101000304001015182d060744140fa105180300e044152000d281381e0400c407400648003400b003000c10402d0101001900303a503101d0000441c0d22044c4442080d025418000b5140c60703849081c07055070351150640007002d244090000700300c20100800d0310203102d036034810382e403600f0740d0313641e0340c41c00112041003484210b40e520303120100070f000d00030402c1e420013015a42c0f40d20380030f0548500da040102e0b90484607190b01410030700401454002c51900c40c010a4868040c88000d864956 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 886964253 1250 886963003 886963039
    0x1a0d1a0301020a031a090601080c0a020312070e01021b0a0b0c0307050114040c0909080304080928150212040b031b0a0201060504060801091205031e0f04020a23040902 73
    0xf0001c2c90310000070b655105542c00c607400303100b00a81070364401d445a83c0c4602d48040060508000a401d4160b07074000810040d00040c420800c5440c440d20402d41c2e1303c11800c1403030014040c0301c801c2c0c0c2c1346c601600521981d03440940000d0203d6002001c0100024030462030510140c0c09640407088590ba540420404c50703010460900809140d0004240f00300710394a01810021b0309070507503800c03000308907007441401800f08101c1e0307060340d82068104900c00d646031000c80003d01203085103020861001c8404660100b00131304e009004040790713209440e520341a8006c07082240c803418040c105e101e00310024481880742241d104041e60307100451460301d07424202080620740c0c2c02e81000e5002e40043c1c0d15803009228604180c000c08004284070402804040c7c0f460340c2d0f44040b80c101c0c0140720104900800007446540307a90803410341202d2180004051410402414a03050b84100c50507400b500022030005106024090503000d540c440655002c0100c0e007840070040034101404040e40d02103441c00d03040703902071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 886965503 1250 886964253 886964257
    0xb100c231f05010807030c090c05070b09010501240801140a05150c2a0f0609040c02030d0c11060415110a0c1713060309080d1d071a0d1a030102 63
    0x240010740701d40140121149203019918140c114a5098000040c100000b5600310403110655940c1074020800c0d011510701103c0d14080c140d00940103858840c00d002544406600a40c140c03281c4950b090141030a11b10400b9002c81300c00ea0280005568030010070125010302204000c8240c024551402c80c1d0351000000c82c400884800700040040c00608840341c80010044d51103021407080305500407240c0700342c02003002912020b626003da520f04880d80003640c0e80c241250241000100308000c1d030461848025600c1e00700e1900140007925002a04140c04d006900180902201c000107041d656030325980c0340106041800903400203a1540c1045101800c0b110142040c03c0150390b03402d22004040c00c0145c07140f40d440d4005444501c081001c418502b000901e88400d0794003909010800c103969141042c1c1c14403a241031628811701e0314207001100001d0055a14418200c0d40c01c45003065240e01908138100d40e0030780360100c000001c20209400b445160030503088000b0700400b04624600701404682a6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 886966753 1250 886965503 886965523
    0x1801020a0810060c020901090513142409030301050d060b0607120f03050408032202030d0f080a0501240e090114040f061a0c0703061505040b100c23 65
    0x705010340204a03807054a040000024609480d0a041440140e004600d0307042c0180240c80c4c48503150b01c0080d45080716034810f40d0900d40d110481b9502c040348081d8081c0c542d8604134503606654100e070f040304403e040d0a14a50300a0721185c01441c6185d107003000b0030000d818000740407182c0710380b62600080260340d004081c0442d240194103c90260041c244020a03030030815030300f401458034102c01d0001240c068130603a94810700c05400303a00c4207052001101040850f04a000707501d4480c61220290181d40000503141154142d200c002964549810a0054070000d00500003086c4111101052105175001a001900c410f41454110040c01501040c150b5a090304204444031a001c0c441d011820180305081c0d295450450402070320341010b2200300c4541740a03002121004000c1841c4da5842818026400210fa0200d001c1104940c850501c2e0140c028900c1490312540c500200c0c1b49942c00e100d0203201707842d20325540340302102d009a6100f600e0701d030007001c840d444142c21400f55110310500f007107d80c680c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 886968003 1250 886966753 886966757
    0x15040c0c060915050108010912030509101b081e04020f010311071a06030c151b0d08010306060e330a030506091b0612190915050c040501090306051801020a 68
    0xc91900f0342d00361090365410b900c800740f507a1515518901040042d85200140501850082030b00d488150070f0074030382280107a405410b0351420014403c010082098014000c6a544460590380c1c0e9003054101081200218455400480d02c0050700614203c00b18050108050600184a240c560503201b996041410100c514400c2020300c1016032106160142d84003604038014945002e15101203407114003c0c03802c2c0301080402003100903030090301130490003412000c00d08503843c100070b0510080540000384029240c03180b4000300070640d038401d010458415501031415100c4040310440155205480c10a0811210303000d0860020316951652070000440c00ba030300030007460410028050400c010815030078483c0c4174007982e0381c8141d10f0740000e07206030342d10032001c0102c85d565a03000c0341e4070303980c40602c00090140351910708020094070100c00030f640b44142c1010041f9a071407909032841c52003240176450200d600891f04200254142d000164007000221a00c00610344149070142681c01103540c1c500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 886969253 1250 886968003 886968023
    0x30a08070c33020f070201080a14040b0117030a1e0306030503031f09054f0302060a0e03160620040e07080106140a0e03070303030e120315040c0c0609 66
    0x4460403000d10007082d8018440d4114034001481138151003c0c444e41800a0620a003000040c002c424150300501190042c0c42c0761301c1452801e0710780401240400d01406d100b0000c01c292400c1030380c0000040c1c900c038160301d880d400c0301d40600b07010b040d6540e240300c00b030801016107610004c00000c0080c005107000701e510000300b4400540078150190300344602e07042500f44614120810030b0701c00d485010118981d641000b101c00f1496240c0340c41240d41044000307040b1503404503e0307240d5140c074000e105d001c1c1f40e8000e509450980d00e448001009445100129a445a00522181c0c4004c1c6044c50002e4103d4450751000481340c0c0c002402d078902e145806920391030650042402c0000c107a49846041c4e1005103460504029070510901611b40102180354500c419004a80c1008a23400303607490050008004044075001c80e81d901c0c00034050641c0110709190360254154044804c070b0100300f9a4007407420210b030204014107100c2444011b020020100f410170156050710307004504c4c1440b40744401402042061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 886970503 1250 886969253 886969313
    0x1e0f0d1802120c15131a070507030c030209160903030f0c050601090203060f010c05060114040603140d0323130501110301080d02160608040213020d2c070503030a08070c 74
    0x1050041d2400c0914044e110708000360343d141c0b0f01000720a401d59500395207401b142c0d000c0880c4840d96004410008206120310003002c014811482024811644207c0d42445280d640700c1030340c00018141010b03440821440c80701400000c0c026603510302e44d0009850540005d80003512008e2402500f80d20503280c40e980042800a18140a1040040450f003030a045405203010340c0c4d141ea880405100d440110032a040745081c2c641e81e140c001d2001580c1114507044c0b503c4100754913940b02c000a800520100c1d01d060328580210811081002401170780c4030b000c40e182da450041c1c1501c0044542c80880d5107568900d1103413903425030b0f18040d41c040c0501c50014480120500d8002c1c0c900b2914460380c5036031002c0d0741c40c20014542d107c10300e41e44c06903040d5442e0300207007401e8400d1000b901900f8110180281041c40e01d03510030750703000141e80003039803129450b4648e80810301c2c03003648510b22400340c40d030142c0007000b003400401e024600d00d1390003400a10741655140010303111001d000131000c05036502d0340a484038031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 886971753 1250 886970503 886970509
    0xc09100c0b0612030a050c0304050a090212090d050d1d060907030b100f090f090803131b0302151b0a0b09060a1505041a151e0f0d1802120c 61
    0x101d03a00c480141c0703420741600c004400041d5070340a00c00c01d0a0401c980090b10002c01304040c01614001c1002800c4c20400e10b4448203440040d410440300354a060341004001141c17188000341001450000381c4030107240c155110410ba004c3c00c030340b505a090342d005000c040c2d06101020841148214074410103002c6560642c5440141c1d2a005020320301940184041400120b41c20680d50301150b821a20010752030000c03240c035001808084c54040c0c43c260010003040749400740c0d01c005904480c17180b00340003000d1000819030480d40700c1c54000a5045a541e07410030003070280c00c00080c05c03074642da03004031004240401100b900e81080e03484211110003124082c00040b18041111f982c005011040500ca140728821402d2480002d9102c0d10b0300c01d80d2110081010018282d005140d0039402401020311200017104104c440e0384201444500c10360150006012110901e007070316200c2c0c0689508615203129600d040024220600000e45010f01e408288001a0346222040c1a00e440400103810208094010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 886973003 1250 886971753 886971773
    0x20405060406031d160e0711011506030c0815310f0507080f0402150d020309160815010e04030302091207080106080c03150c0702031b0f04230c09100c 66
    0xd058860f51100e841000c440154415a401baa49085412109a41c43c82c034212186003020322403203019440c00c1c81d2041403c5d1660341d0038003540c0c1186c03004e000c1e100d4088400c980c042411a2204000500e61101e0b11191034038240420120bc01162007403070341d4604240040a08101a0a01402c541d903400d0a9078076031030501070fa6900c031505060000c1c0307c1c40e240041c2c02c52440010300017489414805981590800c10809031151505004000c544030301e0003880680d0740d104101d03040c0c64015400c1400245c44030707002451207010098030114060780d904e4003640d41140c55010707004a003415001c7c0301c04013080d200c00d5000450010841c0040ca1080c1c40d200341c482c00c580094110001e203810140b40071415071000944a11410505800c245142d0340d04900001c007030281e03c1009505001c0c1d006818030907a42c01c0300040d61075808450802d4200d1601080004856054610345542e803500c48152152000d420012503001c04103011f46850281600e00007442c61041a100f000401c40c14038180051000c4121 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 886974253 1250 886973003 886973051
    0x2090c030604180206310303081008031303110d2906010206060607022e11010506010f1b02040f0e0102130803091f0c02090117100c0503160302040506040603 69
    0x12042d01d4031001500800d045214150f00c51b0044100c0c0c05070155010b5481d518241d176860001103d00d0742ca40c8a2500820084050320310800c2209801c0010941050100495401840e0030000f010400d2855540941c081d4a07261450f03440b460504d03044004c10010195964448406c414142c64007030f401000308081c40c07015203032a045500800400045441d101c04407912281c04899400401e40d6901c40c2a070040c0c034580222030000350b10100c81440680141010290011a00007880300d992203600450311120b41c50500c0e800140e5a070110512841450008034a95002420100b03000b13150071242c0301594905480c0001030b03980000c00607203000e02800500040c01c03645000d1840d203a14036001903950040f40d50220b260850b01c0644000c0c1324042c410891b00380754064407921056a44528801c1031002290000149005208007080c4641d428404c807213078001d45031242030840d21103091704802c200098200034249903007004040740700d907a00e00c003030b00003401e09075000301d00d9240001100400440c606 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 886975503 1250 886974253 886974281
    0x2040503150603120912030703080601120c090302010c0516031103250b0f1c090201031404170319020c0f0c060301150c020607080a020d020618030301090b0d02090c030604 75
    0x21003806569900131030500b0114040e80110703a00ca110f0880010015401c01c95114203611001030b40408158020880d50312800c1d0988407019840198a40070040d62030807420303d0b00142c2060000c6c4010340c05400409082401641290003a00031095181700c0c0318200d410658490440c48a041ea0b00d150811080c200740081c0c0121004190005003035142c100300a020b0007211840114042c10039444400503140b99201000c942c503004e900311511600203181144050340064181000e01103426201640d460060781d0240900e062281079008100a64201a100b6a082601212101101c1000740040d01ea01d91403200a00350412103100300f40d1801c0ea00c000154012036090004010310b021403142510703c2019410b10510030780403440000e089110f20007008082e4030000c160716065a07400170340f1000054454080352007030307142c1100c010307461481c4500740c10081c0c6c030410046c4190111a0071116441901503d061a800c81c3c640c0003c0941100302c88030f010b02000401040564502400703a1200480c1030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 886976753 1250 886975503 886975543
    0x318080c0105070206091f0806030114011511010e0a050f0d0804030c12030b0411030712052e050a0605250b0a2307020d17060f01120f02040902040503 66
    0x2180020b4040d005030070000c3e202c1c00011440000c80d48600d080e02c0e03803c009207039500b1183d460b2850054642c000c1a281d2500039032803c1c01d600800410144c0c1c045c103a0b5040f007041a10b0b0746500300c00311289100f280d1b01e401e9a54840c151585180707000c029204a0a102d203003d800210100c5141e80d144c084181c0700e4400b0031000d201807001180d0000b11701c03103401da0000c4410305c0c0c1000d58070040d00a8004149210740113450304140781c1c000c0e452003001e10300070403140d62010051846686810242c81301641d580c510b04000c0d420222501c0f001c0a40c003091a0b18401140c0d440541c1d1300c0018051700c00541c082c001140e4009000c5103156940e000e07100034031044003208520210503448550f2201002480103111550781c0c00107491204108000c0001000010300141d8035203072a900c003d407100308035001000071420a0350201c44074000405046d11800c0090b010018188042004403080301489600c1280c859541d00ba62840950a000030700141c1052070000d42d5842c40c0805044c0381030400918503503a4111 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 886978003 1250 886976753 886976773
    0x5060d2f09100905032a0301060311040e0a020613060f02030a02060f060316170d08010b09060a120606031e090302100203070203040503010e10051003030903080a1b031808 75
    0x140c0d20907030319001c1c0140c030501048500540191000c1c046908416031510540f0040183c2d02e130401c0c422400b66083d10301384810342c41884145820b9030200c0c0001040090b4141e0b445485d418980c0c002e621323541c00d01c4120341e0004070030b4020030400d0f84014994100740e6200321050050b29000300c062210549a480258a000b64445c4001d403a4640942488504220b94003c943c00d41e6040200d2a80c0b41800b04200d074440740d603864400c01103410f0740c02c035110702c1c0252134003002d88500403903410b412a6040803840b0326044503401000301343d9004e0b0b100c3c602407102c5611818154102031203004040e10003500c001420459425118000191483e8000b40d41c50078229003000103507010403401c0000300c8040c40543c13282c68020342a820350085402003509580b17092101c1d4001e000010303114005c60b01e4150b08214540b10381c040a1560351103400040c0c00715900d0402040001c4d4884000d104e02d42c103134505a00103002c000f03600040807036216015400031b0b00f6203004660701d00c80f06090074010540007000f03004a4403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 886979253 1250 886978003 886978091
    0x6050411040b07060b040e1e0c0301060f090902041805062202240409090b1005030102070201090612110f071119030b0c0c0f0d180b040b1305060d 64
    0x1c2201c0d001080c031920f40c05d4104450f01c0700e80110030140c095100380e5042c202c03007650a00c281c45003103400e03220300d10030304098a900382010312511050725140c10845071258104005200940b02291040b60803a580d444194118001e0440ad03d859074440d101410300c50904e074040c02d0b0b0000141000112002d13200b1080300059650320741040c81c0d040448100c10030080141400d00450049a010311011824140003d0801c0b42c00700d18503225580342202510f00d40c0e120800d1608034012a48000c0c0422100c02060008501400070f8a1901803109004290440d90000c0788405402000d0402c040f0ba1010885004100c00b280d84820440f60646142c00b10091161840007905403030b102c0a4000d4452030003041a9040b00b400310b0b01002071100c211502d005030701d80300302c2ea641402c1d50004001036810aa50343c0e51000107800310b0490751a81c0c100c904280c01c1c400c41c506c5aa01a601c00f07595206010300006103605c82c5005400c042031101c0c400590300c008490104100820808984a450014070b0500241c0c0703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 886980503 1250 886979253 886979257
    0x509040c151e050a05370c03021203091f18080d0b01031a1309120809060a14071b0203010f020d060f080601120812010f06120b310f06050411040b 64
    0x7505100711034444080d0035800c00e009a060b00c0090321b1505510004081e64122850091540c465804c45000b01030740c83d0a05200d000a4402008030740020040c040e45217100701c0011130324a442c4000064070b2900030032280c40780343c9200e802c8131040800316000d010042c00f445090f000880c01e0030244048540036003d03080000d076520381c40c1e114003540403c0b00305440865011070140c582c0079061505004917004050002e40c01110f40d07001134400d07240000c40d40942801a00c000d8230b441d02c988411901c0d045c1041d11101c0300d40d94141c41e240c0140c3d0745880541c0e070900441c03107100c02401005a4964030031001c4000e03503503190029020a440c9100800908800180e61411501c0120702c11070807c602e032410100700d01c168408040c100c4884000450025000c400702c00859045480d41030030300a085d02d0590a981d42c0c2000d0310761010303a0074102c120b5a5040291149a01c0c100002600a8024170345140211b0b5035070001c03e00c001d551400188805e092500c070b80380e26041e06141036400e051404040340b00038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 886981753 1250 886980503 886980517
    0x32702060a0e0604030605160c05030a141903050a3c1b080906130b151207081614030703140c06030a0b10180509040c151e050a05 57
    0x104000030740c00503000d00c10041d00480348001420035966030340e81e042c018054007082e01c1600390240080e000700304443c010101c4000706e0398810081c1d400c01c800100181c0700c0c2800848a190b414400300131752a41003007182c040780311403901c80d1000601820003014010890300c091190041c400c851030a01080f0f0030340030400b141c0105038440c003c134102074020301c0c500c05081016082c0d001d400c0c2003001d50704c40c540c1040312944600c01c0c00301194041c1d56000c40345102c0010b1400e0280012074588003103040d99041c000304242068020344124900f030090105c0c0f40c41d000702540f0459581d0405180c21075103032094400e04006000740032080400c0310441002a44502c4684401031000354040c40c4c61061100074042400700060003400242c8901d000a487e40142644180e1144550040148000403034040c005c5042100d400026004850b4100801c0c0300402101400603101480907190010300c921011b89102da11130700ca0340d83c1e2102003000c002c841c00403052956141050201c1441802c804990190940350742c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 886983003 1250 886981753 886981759
    0x501171e0304240f030203060609120a051605030c040c0f0c0515040f0b0a0e0316020f04052a030121063e090f0120160303032702 57
    0x340032a000c4203480d5128550145039418005292000350040c90040d440e540351860300c2d00244a8501d40c0c040341207100c12200c89505c500180b004420034200210b00f24036803550340d011140621515240c0d5803401804907810300c0070908015003846541424003420121000036a418400342c40030040c00b0b8540000a0344c01010490b03000c101009100040240e6400b409000c030340b410542c101424a0107418081010949a07541c0500203c2c07001c041074401c051503194580069818603005001d001510f1154440580e0b00140e028a050b032595118403d06000e10800f5103001c44000489500018001c4454028004008248010800c180c82000036851085c502c1c5c1503585c0102c02c0786051401408414440c4148506141000c1c42d4130344840554101c44140026115a0b150400d04440700391044880c6150032146240360b4200f5540114401c402d41041d01e104001d194a90507907551801d04180820a044601342d9010024950140320704041003408480615200000c0c6c000c00407003080441001340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 886984253 1250 886983003 886983043
    0xc033203180112020d0507030614090103150e1b010305090307030c080a0908060703091e03050d020d021e030403080714030f15030708031909030c03060b03030f1b01050117 75
    0xd041c0c3c411182d1610035681e1403002c5490740410911320000300411a1340401003803414101143c0d9014044090155400c001d05901d41a03085940d1401038160584400030102e8a44d6441c007000304043c0401c5154100d60251000c150840074001400c1e1100038000c04840d0300100079410219a004503030b08c90060304000e038241d84480e006400c4a0540c119442000e1502070103040c801c04e01c0e03054203d0075550b801124104000003007907046004512544a0040c08103504008040148886402400b00f000d1b00d450010700745204c020711116000c1418111700c00100303000080104241e080b041d00350b086446460a10b04e032a00c40e04444200d80b10103000c48800d50420340004141214100341c010300880b004c0c2c00e90300c4440d0354600c040e46d00d800441c03042d4081c1c00200d42000400b4443c0b20391000701c0350080c601c503c2444c0303540c80d044001d160004250fa0540810007002007002c4801d0010801c0040c98070420700c02c8042940c0e100d0840703006810444a81c981c11a00c507000d040002800c00768810f803120518 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 886985503 1250 886984253 886984297
    0x305090606060c0d08060d0210030e0606032d2b080f07050f130302103902010c0510020441130915021c090203070905040303090c033203 60
    0xa00881907d0b40700a61002c541c1529003d032940c5a0001c0840e9501c0c2000c0382d07039130744130b070401c040d226032001c00a0070240100490700d001c50803211081d9400b0528640a454441882c43c046841e603c1c0c0e09003403450220702c0d580f95142e649500400043d480f150402a60a05003000c140c003e00750b214008050240400c0490340e084c0e40da041c00d0544008507030007018001000005080907180b60501d503001d02c600350f00b281146920440081e4003142c001302401c58140c91001c00d90040d10301414041042e1214480c0b40d51002c00400c4501c01032003c2c00d502241044040306902e14074071240d424010a0380200c245560701249d0407050501089103010031154010922004005940140021a0080c005000072841111220019030051100180b085400081c810481c03106400b503400c00c802c0250035501c407034010805c005584c0d000c0c9801610030b190200b440d0841e1b449130710380d148150704151140c10303401014006400d90441d100a42c6000910100c8984140b03d4045403203000701c90300c0000003103001e4030039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 886986753 1250 886985503 886985509
    0xa02040b03012303010e0105070f0804050a03081905090c040606020f2a06071b061719020c030a0f0306050103110904020f07150609060f051f021c0305090606060c0d0806 74
    0x96024450f0180003001683d010780039990190005464650100b41e500e04444000d61148804600c510703080401414011007541d401c0300c0310440204110400d00090307484d80e0700c0070610302a6030300901e0600c2c010450000f5080810040340c402e9440f140643d031110345030448103c00440c2c10038202818103040021903108070071078581c2c402a80c0907554400340010300d500800c12186034a03401101c1803180161340544585003034510070190408014111030600c002641e2a8000c03064140250703100300e01606005e40011201c1c51500020b900300007246000110543c072a40c50310501e0b00411007481c05014604d1a40f07076220047c031601c20b41c28081e82c2c002501c210380340d80100484200d554440900590030280e408903074010201130080d0340f141420300380000340f8008030400c1031040e1180107100508003040f00040000d1034070203081000c04c0d07015448800b8820f0044008600c003061450314041100e2801c0c00059042c0000240420b10036a000e0240124241c40040c101c21200900d09000c400d54541c5400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 886988003 1250 886986753 886986809
    0x30c0d090e070c1a150a1e050a0f030b07022a090c030105012f060403050705191a150306010801090c09060b04121703040f02041a0f013b090a02040b0301 67
    0x92500044c01b00000140300b40126664510180b2020b45010b44544440400c10f85402521840702d07e6412994188046015080b105805c4007190044411580525a80d50800803c0d41110301d980c4010b06104203107400c000d01581d07440708a010402c1e217113605200c0040c2c821190036a1806120200c042c410300c04a980034440c0e0300821002c01225210310703080c6402000e642c0400021501c42c05a91218080c52134503d01d6000007542c080c020041c103100581c86101c0c55980180b2690a006509184017880d032800e120086c041c5c4940030000c0341d48021818007407070440c80c40d402902540c2c5020001c10140f10000165030a0700c42c2566070181c0b0070300c903050038000141d003640819501840001031004102c40d41c40039400c064405ea0b028006190344000c2d00c80b43d201c0303054107550440301d9a541d00714158440d9400c00000c0c3d01f51417529454001e00382ca6100014a0319800c511603050603030480e440d40ca03040c1403456100d881060700390305d441e040c01e42401702c0b400b061048551200c0900040e800048030011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 886989253 1250 886988003 886988041
    0x509120903070b0d0b031b0307050922080a030b03061303050708190c02010905061c050709080f1b060c07140a030807030f0f03022703030c0d090e070c1a 67
    0x2102c0c80d210105418224000c104e4901700c40d101c0c1c440c074443d81e807903042c2d0500d1350221900020081c0803a1841c02050110951000344482e0407041c031030305041056440d948102d02c000d4000c40d003c580314000441c01604444210f68407503c203621000402c080307000000c1c1c0100d0141c0c2e1500d40251510440d180c01d085034010b4035290070003030407d4070580d01400e610124944815000340d03500c9039007982e694180300980c071407040c034242000c0c0c40504240c4c022846400c551b0304504645010300740569601001c50501540842d52940c5406c0044903000c13040700c080510a40c11000c030b485500c4d207440354441d41c0da520300a129400d0458009032008406648001d400345c02140c0040885503183c0980c600105000a0321340c108022503041d003801c601e9544a8825510482d4044099000e03405071782054449105e111040c807a030503c010482900350003030a03c80e10f0344903880c540319003d4050070142c1c0364000706801000d5008105141c4502000b0401c01103a04401e000c80310008841d03a05c2e55981450003900b40300b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 886990503 1250 886989253 886989269
    0x140f040e0a0c0b07060507210902060d02040e0f060a0b030a09060b061603030e010501080a0311101503030906031e05040c0b04060909050123190302090a021c050912090307 75
    0x50016a80c0d01d414000c002241c46001c5c1008075994030201541c2c080420070743c142c070741c082482c1d906c06880350741c0e880003e003640028450380c04c1403000700e51501a680103401c420020b01e030990034419680c68a007016500802d044866580d503504002c4100c985001c01000b52403d1510344900c6010b01c02507601800d140340000d08080d90300e40d03000300c10041002c200307081140002d2030b02c15030a03c4031a040c0f0455040c0d0b445030000e03200741d02030b0703841c116558084510110058014840302c45c609000310700c2040b03034800400c03071801205d900e1030501814200c201e9001030103060510b2444445c80c26003905428500d02e040800160301d0311030303050100c0b6121042c1c1110022060002d0007103011a0000c4203c400c0b80e82d118401e000c0c5070780340d801103810421100504c0300e00c8040c1405600c1e6030700d0007544100d200c50781641c1380041281d4175000102d501781d0542d410040c003580000c41c2c201034120b4204950426044e44024080c9040406840e80d994403000704400b588440030441c001aa502440014000c20b601 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 886991753 1250 886990503 886990523
    0x20328060f021809090303190e030304112728050903131403030714100f020a0e0409020328060501080d2c19051f09140f040e0a 56
    0x4454600001d5002141c614040300320341c0e2210b003c0b80303002c0200358803840036180690f00315240c00145140d6843e1004040c80203d440301a4090b4243c010000b840c4030754000c21801101b84090014401c242d00300c40383c141d18000e41c00c2d84150784508440c031115002041281b80ea0340c000e80f25030641148180c00d038921200182020300344090703510000040c1420704040039603000e0386955412014401801c1c2046240c060304180300c02c0021030803040da80145501c19105031000c407500342038610700322900e20040e08945580801c40c101d0302076101000d403000c1141660100a00101c50300040d41e2034102c1c940c0100105d510140da44c0c4024111142056425400700003844196198861a0b032a9518818103100040b002a0144c141c0203d9285140a00d40b039201098100e40a507400d0100040e45404110b80c0701c80c24901c00900b0751108440c010700b200310328048050202030303140014441d03841a4490b0b00d9980703041c3d010341103541e42d25401030309014080301c0c0010300d02c40e6042c115052500e10704c8041c04c0d031415 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 886993003 1250 886991753 886991771
    0x80c0403030c21200c01020c060a09050a0e16090815060f0d0c14100801030b060109121406070203041805100f0608090c06030f0105220c030b01020f010902032806 71
    0x1103010022900038000c1c10901110441d84e0780c0e980c0c4110030049005a01030040745c011414088014000040e00b4034101001988601c04201080310590000d044d2980d602c04100411141f40c214801c8004c0519021844514007a9000c0c0e407004000302c9403007480f09400115044d6a1050380c4030000c004094454440c00b5818204038003a4540d0b0310840010055001200c0701625008144a03400301c07207a1952a55030342075803140741c41e5460090407181070203049000070850340a4401c0c1040c005c1e1041180400c041c8003441070505014001c0d0040b000d540c010301042c0b0900c04120165500071000040004060b69259140303181044030740d1010407060041c41d00480c140360701981c5c1500c9403c5c64002c5420148104042c01441c0c03204403440800c0d000004010702851400c100030042c03d5040400f40c420754444000c03100304580094600c480071a5a6810300d102958050200c6080039121000810640c0e1594010a0726040900c00b5800340c150b0b1030200d8044040340d01d201000d526041581080750380700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 886994253 1250 886993003 886993007
    0x8030406030b060901080f07090e0a0c1b02030706050a03020714030301260307120309060e210304050706080c040306060f030209091c031a1801050907080c0403030c21 73
    0x48103000d84000030381020241000382c1401011110301d10b10694860090340d03100f01060b002140040c0000b01009514140002d50305600f54a2902402341c004000510300035a11001d05a44410f41c03880b5100341814001c40302681d8049500801c07182d850a203503958580c0000110028450b49100524148d40240340d010845e000002441c16140c00030210700030720065081d04892070305400c81c40021540108140400680050301c040100e0600e0309020829055030f540f01400cad690350071110199a40824071518480010750f0606004a42c10074041d480c40c20a929041c0d151029070180e082400690f0020816413000174007220003c5800200420102c3e4507000103204403181403006a100d1341400340812003080c2c011550071082281e02c450f2098000c44640240c025046010780c02c018003c02042191403922100e020074140c00c14111084120b41c1440d042050184014000c0380400040d507040101c4020316170100c1e402c1d203400d401c08050a1240d490700c0359550090010322070100062100e0040103075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 886995503 1250 886994253 886994257
    0xc01060f030b090c1509011206090e010c0914180907030512130b27131d06090106050a06050304060f020c010b01110d05070809060403062406090521160803 68
    0x1081c00c00644d421107841c0010800780303000c00114980c0f0701c6010000c01c0030303560140318010050301c020000800c034603584000e013a08842c1040c03081b8400342d4403100b00d03a184a030f004515070068840311480c1e000e280420f501281c07031040c06c0c01e4002c042c1e262100118014000c10001e0500641d40300302103e5400d00d40b100030704240c0d0055032517282e0403401c44c42c0203e8100b51442c1981e5140d0b2000a4100082d14481c0f0780100320550944941d0300400041310186684c0071a000300c5225031010504000391001c078484040c6003403c010401a9942d2401d00d0034810703944c46002d01802c455a6241440e03c0340c070340f403c140000b45910081c51800c40d1000070495040e00040d046140140c5007600d0344003005180c90412a02d40d07118051800c00a1400c025030800a030185002c0d06000401400391707424180c80340d0300e48080f038840d0701c849403c1c0d505080744040013490804000c406020b6920f8250100c41c40c2102103560743c84a0071a405807403526401c02d05a0032000c000c4660b080d0f00d004015151507070703201e00d000d03225 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 886996753 1250 886995503 886995511
    0x715020f0c1b0f060a120b280504092316060c052505060c0a020d0318120b04030807022d0706020105010b030406180f0c140301050f04080c01060f030b 66
    0x20b607a0b11420040c0e1a00c241c400e0780c06034014054519121034000200d401901490824844503030705c000114050300c03403410140480c400c4602950342101c2d84a2692415505607008910890801500c81e0000c0c2851039008547d084081740e4000c0072109004036810110a560002034004404000203150f0703a001180d03109031406841907a00404080a070151a04810744100c401407083c100104014207110000b495031a45490994070f2103c00d5a0000c4c0c43c00b1407840c019400902003004814030210100c101100502c0a80140240354005075078810b03081100030000f800f8003225a00051340310f0b00034082508a10001d4402401012610002141942010f0004005441000004129503005114060507640f80c004003505580e280c0c1c2d1810b001d002e8182441c1807040241c5250000034440a400c007410510890206000b541010f4407855100c4c10b2500d0607200784e041c80144000ca281c45004590010b030803402c15580c07041c0d00b03111580948001e0b880301740001d400c00700000c240a562241107002d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 886998003 1250 886996753 886996783
    0x70b240405040c06110a0501110a030e0d0c06090201200a1b06081506040b040f090b0d080901140c1e010c081006211e061a0715020f0c 59
    0x9008514140001c03a0002c8a00600700034031030100f44036583c01080c42c05440641038080f9001c9100e1540d800f401e407085400035000078980030810200c829054010420003056500080081c0c0c0c6081000915826000d0000b4103111b540d52102010341e446100980c00401a01a0741c8034800244800c5907941d54500d0070907030b900d02540c010f002505480ca601c020407a80c107551000c460361030302900c800c0c00c00004032407079a00007000c200010b4403091000c042c10042c1080c0311009242d070301d03100b4400c05079401c00111921485582440400040d0104251100c01e60203203410010064400307065400c92007040f0900d065803040b42c00383e90403403c01c00034995451030a48024041c2c00820b090070742c0d200c2400d89010707507103c400e044140440b5110703080001058581038000842c095905500c0c100300c0d078074075650f0808031041c500000e5404106000d4800100340444c1043e150f50340100c00c0001038000c4c180010540302080203541b000c880150142d401d203a1251501e582c1c0c0c0e662220a096490038402c001e180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 886999253 1250 886998003 886998061
    0x140a0201020d031a060906160f0309120b0718032013060302150d0603170c160501080106050702060708040b04051503151c170a0909110d050c070b 64
    0x42141d219020f101d4104090000340031052190740304101032504921b45580d08448180443ca000700c85424003441214003c0b02290a120042d0034003d00402c1a0340065202c000d2804044002072203642807d5840341d00e515143c5034046841c05203000000c0e542d400039044800701c801c00900540c400c010740340031080449140807a1403403010002d05440d000d21020f5030101b940d4000e03103850500c100c000c0150002c045030001d40310703407640d03111b030407041903031010194080740443c004498141c10007030419181a0780c0c80922103e0325240000340b50003414060281040301c02700788102151100ba0541d89a141e00c00615500c607502c4c1c3d0460110783d005031155030300c550200f001280303003011407000302ca0144031441001030400e5003071014081c550a502591400000280500f90081000d610442c0034a9850b07007011130340c1d030a030208000c08a55607500072500707691500d4001c80d0741c0c2040008030b4944801e21540410140d4901c01506050f010314031014043e80c000108100c00c44070703208001e41a40c2c1c440780d0854 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 887000503 1250 886999253 886999273
    0x10050102010f0b030703060903050412150b12060105060d06090f020d06120c03080f09060a1805030f101d06010b040305060a0603023102070303060f05060708030403050a050403140a020102 82
    0x509480c050f801c500d405400c039032401c0c40411050b410403807810f40a41000761509569200c451541302e1070740402e82d500302e8265880c540070071603070043d500440403c40c0d1071031141071200172150311000184035443c818400043d02140e8815150080c00091840c403004220512001864030042e50200007400c08083c5014004900e10781155107980c0311a40010881d41401d042d039441c003040d640400c11000c01400284800305081d6604002441c40d01d05694504420b0401c10201a40e2003d1641205100380c018001242c4104000161010b01105509005c01c620400f0072554000400140300e03071f4030305d004a000104d01e01403074000400460344075008803040b95a1f00c0301d02004488150000a40c04000440c0c44161021081c0965108400c60a01b01160106c1150040101da02c40e000031404a61203443c02c0005801450910004083c03d603032492500710305903110038042c07100810080c1400804520300c6c817a01d10480580c1c01959016900c3c2410308511141313160b0320380462004900500c1062418 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 887001753 1250 887000503 887000531
    0x1510021204080a260f0711120a1506150c0606030f05030301030b070f0c06020d060e0a0f0513170d140a0e0d0c020a1502150a051801020f0702041a091005010201 70
    0xc3d40748040740000e080c14980b0175552854954468001910403603030010941c43c681c0e0b12036030202c005201c3d110003800a01e07018a4800b0ba11000c841c044031380249489400c2281d04600b414881c030100041c6042044209545012001454203400141c1000700060320f850402200000440c107880c040c444c07002c4180c2d941f010880e100e10700303084040c0004002c00c034040e00050240c0c02505c403403400c403000803600c540c840180b02403c240888159480c0380d1103481c800c000007420303c103890300f101100450030040314168540c00c0003420751440c120070380400010f83d098001c1c00360303002207611100070a0703005060a0942c2e000e000390556058540340e9002d000c02c2c00302c146000f00c41241c0380560207001d80a120789085182006080910340c010154002c00ca03800014000d0050064071803950110009000d080000c400858210485500c0c03c80368810850300300ca0101d0082a0f403c0d5580c1160041000c003940800c61241c4a0501c4107a908994440700f4040300c1c0c00510407840641d4400c0e40208032070800a282 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 887003003 1250 887001753 887001803
    0xc0106170703030f0804050307060f02092b0212100203012402010c0804020603100b0d021902150411130509060a1104060903120203160606050102060f1510021204080a 73
    0x4001d0110340c071a011390700c209000d44942a4481d00039030559040c0100d40e00c0e0f40c0f0540c0d080350706440f50142c0c001a42012858500e1030b100e448007080a2660034a070002004809040c46041c020b0720a0b0390104601b142c0c403e04120b0030003910842c074019502d82d45c2d1528082c42c2e0000000c5c400c000480b440c0500d840f041d105100b03100300c0c1c2442d903580c7c890b5a141c940034403815520160104040c510000000300310560004000d0895205000005946494400d090b401c64170444000008641054962603420756070500e4031500305410001071200c4c920aa80060399500940154580c000c1c2081c041140813400815142d02c514144801441020052403005600d8030440c015400420119542440031034040c400711180301e41140116490301c06940e201800404100350b044545c1c40e00c03100d041c8001d5905000381600000c0e5030038001d01c2404c0158110088552807403400f401496908045420140300704490304071070044241440c1d4880d107032a201a15130400d540c080e5078500701c00d00d04104600184038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 887004253 1250 887003003 887003009
    0x131a040620030f06010203090a080f010c05030708010603020c03160605090c06090303180a0503030318010605061c0906060e1e06030a030f141e0a02160f0b07080c01020c01061707 78
    0x200d864a155103c0040540056000d020141140b0081c451019103071030304a100c4016210300c0005000703040007040c010342910b103003201d60401c20106209200c43c594201d1401415a0080d040141e25022068040352031402280c95000f000320701c100d003400900160742c2c0300300e000383e13503090a480c900600b0105006040c822201980e130558800c10851a02030881d201da144469001407800090030780e1400041c1c9160001e030380e01d040381059041710100401c0c091003104010501500c4045c00c03d9146504081d0549541000601c8140c1320464001003050503880680501030a90302e20a480c1800ad01e0341da408920b94804205100482c0082100e80c5000030321260324544c159038100190150820446138030810410b00030603c4c00a0080c0c411a01c040880780d00c8800c2500c50558a881c1c800400a00e06200c4446000e004c0c41d00702c0041c01549640d0070a0810360304810304c0b0550b54683e61402ca4142d2280c42000b00f555440030541ca203003480306411240c202c1d490782c40b28040b49a08031403916252701e4a84 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 887005503 1250 887004253 887004311
    0x1b060f0f1b0213050a051f060e041113060905030f03091c0c03060e03120c031608070c0f0c0317040b1606320711060a05131a0406 57
    0x80031103801c40344408003500040c0d10180008000c0f01c1140021000c2c0c5605582020206488038100400c04d1040c803003c1e68912240407288036140d00c0d00c81d02404002c0c84030403942c0107a03103a040b5400284120310864030588001a107094045944000c000c0c0146480d0041c98402e0007109007880fa5408000160342c1359010040c004120a84220503912103002021070841c1d400402035000030200d01c0d0b5110302e042c101011805580d4035a8090308c0c62040305002007804010314004e206010300e04101d06c6500301010468100010580c49400050fa481e138803a5a0042501001700100300070801d210301ea440407644103081b07410345a0340c0c10008402c18001c0d030252420700c1c0401c1c0000c1040e0380c0c4101040710114000c030740000302000c080060382d2030802d8403903040b468104c110300c03003a45504d01000400e610040a240101c480c0890400c102d0b21404049c228036481a119030100c0e102d19110341180092a605c41000b5640e00d16004c2840705041c821201610010715009402039066048071503801004610 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 887006753 1250 887005503 887005517
    0x6090c080105060903010915020909060909251a0d0b0a120b04020d06090f110303090d06200304050706080106020109020d12090306020408030c01050a0c1b08071b060f0f 74
    0x83c00702c0382c0c1015229a62541d01e0f2542c00000c2400501c41d011005c0c078041c1c0150f0358503650001d00c00d054001a104500407080501003180d0703040003081c51024244da80d2403920610700d00121141d01c0f021240c0259501e01c80944a08000164074001003c0403250b0b440d0031321030b1701512420800a21082e03c940840322611186800c0044c51107860b25070700030b10083c595003003074103961030b81c1007101c1144a040ba00c1041e18200c4c00c09110280c4005045c6040840040d4a0884504040781c2c2d28004c00034020183c1383c88281580d0540c9140c1c4410042405903446551217161070b050032560b49070300780714400c04541510004220244180035002c1501e4025140c01c452600564900c10450180c05503082085050f10000c000911540001c2004007102c1001b141c80d042e5980003039085407070160101d80210b180c0030805043c1c0d030f00320b41210100d082c540c10001c000030382070900c11603c1c801c1d41d400405801141140a403821000040c0100390f840c541c1e5100710040d00c6400543d0740110b62160030001c1152 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 887008003 1250 887006753 887006759
    0x207051002030d051608101a070215070c0302120f07140415080105100e04050601060507031b03080115050711091b070503040924090f2702010306090c0801 68
    0x981203105000c8a441124a031295852054007116000c1d94408000b0042052618405a004c0f60036a0407000083c600c100c0d01e490400201036076080b04810f00030f820008181c5505550f2101c00017059400300c40c04080d40e926403858041281c03c154041288661a00c0740c01c10704805001910340a541c00c2c00f001029005d090445e661088600b0b4001a98401c0d11520740c442341301000030103040103040420000c036490902d076422120a04940c0c00209406d4108000c01020075000520301c2d0440b03d260901681d600650700b000c465990303500343c42240c4054204211000c040c1e0001c2c09604941e8940c404003401e02201c0c404840d18492010054881028a00f404a15140c844201c80d00400d01c03180802e901c0510f5111024690440301c0141c443c0d40004c10b0402041e030645c05400c00c00c20001d514502d2040403444422220360141c026652400e0352002260f0a091039588459100c00010103c01c3d244002c4000103a042c94a43da0103e002030b0500e00700103502d03980d078021444c400c0c040e0740307031001d80380c1c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 887009253 1250 887008003 887008009
    0x190c090311061e13090f0902010c0b1b0c0607230304020405070e031501080c01020c150a1b0506060f04270c0b040e04141222090c05130e010303020705 66
    0x450158000c41d08140849440450403041c014940c00e12500920030740130345801c1416045910340381c1e50700c03c0182802071f1310005030b1340400300f00c80d043e9201d1845038083d145d10441c0c0303e260002c050284210b01002840451406000030342600c5107510340e035140ea112503501192a140840210300000514052000c180189002d801c981d51107074840c60446948088040003a140040c1c400b01030850480a6005000e801402d000c008900b00080c001404150030000104030b0003000160304001e040380c041048907505200d000c0c03a140d01100880410a46072090611f180c483c00240c80042c881c00a60042400600305402046000350402c0c45e20002080c9a02100c41c8108400301e0803982c4d0a0b81b40008a030401201c0060b00103840004410099840e007803411640c240c5020720301c055a9480400000e10120318102102c080400e501240356601d600c1c0700d40c05400f4a003503000b0101d0503080030030303d020665100019007213140fa80b8207011883c550751300808440c03130804c2c000a40141c120398003d000600b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 887010503 1250 887009253 887009257
    0x71a06010f17280e1b0a06110c0a0b0a030b010c05060601030903020c0d031e050c062404140a06170a0303051e010b030709171f090803190c09031106 65
    0x140c0c4a40d0b02c810f1003078508680c04402c03001c1c82100c501059031411040f090500400504c4018001c01c019441800004c500140400c44544241010011340d002c1c40400c0d490300340207000c4401740181042c10303074a860b680703c042c080e00038400c1c0c4400207183c0030a16070598812900944d0881d0014064072998988100440107402c1c181c80580c00d43c421450303034140c00d8580c540c1c0c442e48076000b80e07030f4409402c20101102a042e588a480241080020702c00040500c07070200b94160409280d0030504602c1120b5024220301090700d840d1300c0e5000303203008518000044200c9105200d4000007200b0400e194441d0700c0118841c040036800511035100b0803e101c0024020380c03080d034000341410240031481c0c0d00e42e070000b143d11409800c02c4d100e01c9004000c2c001c19581100010f00540540221106008150404a5994180001241030021b5010f91007005032005901100134260040c003550b64038500a10402001d42800401381103580c90300750b010010314030030650002500c2d8402c60041000c212070b1b040200d69 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 887011753 1250 887010503 887010511
    0xf05070c090b01090f090608060c180f0f03010f141f03171c0615030501290c070f030c060203070b070302090423040201110d2c0402071a06010f17 64
    0x30100c2d002e000f1840d0082c0d5220340b170061440d03000124049046c00a41800c0113000340801245c200d00b80303c08031520768140c03680c0c40d10380700a42c2d652501404e8200003403e541c095960302c1e030b059407825802040030b0360242c00403400b50f40d0956000c0c0e03c64541d0601005000c00e0111070021038520902c0920009082d02011041080420641c5042008500001c601080140526500140c0d02c806c10000950300340b607001c03000c8203a4103080000f58501a240018180e444100800212650a102a401440070190780b2034004c8402110030741d5880309140e41c0c1001d0789001c295094022040005030052001085032040d940c403119030681c035180c4090542c00382d000b00414550050f11030451060200e205030a5400500103118440301600b46400050061642c03529540a5a0003903503000d0750041d0024000c00c0303054242c5041d8681740520b02105027072880c0025049500c81c1c0000360b02010b11200c46e103808460016003003040b0040d20307440015188854404241c1010400a100e190750070f0308405006540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 887013003 1250 887011753 887011757
    0x7061202090d12020609120304080a0c060f0608160b13052119061a0a051009090603210503010f090e010b041103011a0702090a0c14120103030f05070c090b01 69
    0x1c0b80805a840c0c6594042d0044642c0060380304408014908078100001204c598680340030b00d29604242c7c40b80b0f0707014450300e18001d090220001c0b0b541d080010300e5000480034942c81d0420410162100d9046450341d50b4801202500c40403c40041002413850040b91061403850707903416003144c0340c10240601c6038440c2c0360100e800400c130020b4040b4038100b40040702e8401c91035480300e18072046901d440d008403009581c81c21030340d250409000c0d103913454100100c0150b500c215528441100c500344119840c0344241c002c400103900f0503c000080000c5201100505065050f03400c01c0f845d82a001129280001d21801e00210040350b41000701d488190b000aa43c40c07090000421101c00d40c00128099450a009541e98800004010499444041c0144500242d4285c2c414603000003900001c1e920007024008411960717035044007003419800b41c0c12080308420000d8440742c070380300e00450009008a0900c07040c0d0110300e88101d1101150b01c95022548444d40c400814031031076040c05640402898001407040c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 887014253 1250 887013003 887013019
    0x603030d0b130903201b04022a0307020f0603160e0111010c020a0318120803090c1302120609130b28151509031401140a090506090706120209 62
    0x1c400b152801003a00c850300039218030002d500301c1c0982c00c512110307441011516400031111540041d43c1c03507017031078421203040724090b89407140c03a40c0207240f00d02c2807801d401e490341c540c0825102c401000702c00b400c502070080f210a40644113000c1807251910040711701050030149a80e00241550144020401d0040103160103000c8080f074420380c9086400c40c40d075280141c0d010305504020198402100c00b1001400c44e46a0702c40c81c5060003d121042c82d014004000c4040400090007815040089525500005015030aa07004540703280009510040b880c04422080c4400100309080052505001e410b05100c80058800740d0740703585000c200f0203800307100c081c000880020101c110361905c0d45543c550040c800038820740860000b00608007981c0c0446021081a60b50034803040d0880c54000031070b80c0145c0514040d02009040c54011303d5200500713039680c0544418442806c4040c0e125070201ca01c20001c41d00c1c2ca8407800d00583e0740d4489485280d00240030550005c20140e07035500503210070203015015803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 887015503 1250 887014253 887014279
    0x405030f0c0102090603040f020f0103110a031d0d08040606080d0c0201120b0909030d0608011a100201060306090f1a06060d02210103050a0b01090c020a06110d1e0605090603030d0b 79
    0x40b85a070051f141514694070001e00102545885c4a0b40c4072440400d01302000301c203ca41c244c0c5241406900b0b0050141940c4000600c8800703c07102d4070070303250000002558007404071032401400e064015201540c216203091030100340000c0001d0340802c01201600d03120b844142d103500440702c419903421100b103c00d40740c401c803403500d0f1202180940680001e134043e545a4101100240484049600044c1683c1c1402c04c07034030800300c03049481220142d0548941000402c4d81600741d01404240d80000e080c2c91410b5a4041440704144031081054400c01c0e60328030083c4500d8102d03420040503120140d000004014004040248c1e40c01420511243d44104400811302d0b4024a00510264403c1d256600104800c2c0f00704481d40051502500340d0000400c00513020940c0203654484802008200031341c1c40c2120b800c041105015a41096a201e038280300e46003040c00745482c0200d01d810344c890160706113030340403580d827411030507482c82510050015170414444401c003001812036401159040071131b46c8860 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 887016753 1250 887015503 887015509
    0x8072307030308010528060f0903050f10060501030c14090d050604051e0604050c130f0c0e09060103140a090627020a050d0206220b0a090e0109050405030f0c010209 72
    0x403004601a03210000550f14200c1485504082c0d202e524010400d000c1e0b40e508007500021000045e02c501e840c00e001c22481d04034090303c4402140d00040d10701e20500c004000030000004241550224903c82031082c25547d10066059800441a0f000410741d0600390704001020700010b403c10140050019040a0103500c0341d604085c4203444c25039043d04820207103002c0052a40e034040c0c0c020002401081c8500c4d05440d01511403001d03420040c03049414a040308607449240e044000f0004a20b64100441c41c0c0343c90f005406174160b05100781c040c070304100c0000d1007580244034811141c101912610142e503030b600c05680c01885881c000300c400503a100800040b50b0824450342e41c81c400f01c0c0e9501440754405004101013001c066120038880c00710401c50b4001a11040c090b24040c058094015100c41202c054140355172005400080c41540d000c50b03600c844035407099014040741d69030200485180d0b02d42a0100c00d941d4110fa028005034010048101d00b0b0101a0003031035562480b00006051520000c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 887018003 1250 887016753 887016763
    0x402011e0e01110c19050a08061e0901022a0d1e14120414012a050a0e1018050a0f0b1303020d0b09010507030b1315050411040602070602030403080723 66
    0x24151405c2d04090309103c00c2c00c001408201400c0000000c1c0113914100715907040c8880615102028025040041200504250140d48146800500981180706045501c2002012030301c2c0c85a07151144a624042c054001c103401c80015124420540015440000030354444000850030740c00e03040100281c1e0185030444640b00d001d02d100d150020400725000c19020f0070340e150354400500801d0100d404c8680ca40142101d17012146043c1441603c40e00001002e440c0f8040e45401c4542000b00144641090303a4400441000c25595041a0ba03443d502c3d5002d02500d404140500c0c3c400d0400080b00b0702514080e40d0151184e1540100030310201d0740c40381d020420710b462002d41100e5034011a8140107444c103081c003429070b010b406071904028044150000824103c40c01500080301c44e515074803007003000006610f40d40070b0f00000c0e00c14090311500e01c2031042264000e202c0d4400600907a0342c0400c22510102c01c90301201d810560982c00c0c2026920340490000121108603001c0c2c440d20b4101c20403990900c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 887019253 1250 887018003 887018029
    0x50c0d0c08010e2a030c090a09020a0b1306032c07090c03140702012a050f070b01030201270b0f1b0a0b0a11030103200a0801050402011e0e01110c 64
    0x1d080b504d5100d410030080502e078070320b1400e210144544e0b0243e15481c00590038912550484095034141c030b5084c12200103141601d0040d4018011010100710314850b0001003030300003000c600700d9200c01e6440008608550303900c40c1070700c040d01a154441c0c4075017540d800f5100f1001c3c0300e00154ae01641da01c03600f036011500b1000f0201d0210307032111403604132400303480c40445d80700c6442c1c0002d00c10807460650135003250120808000610f405000d450b102607100e08252110700010310207a698404907428001e40540c42480102e00050b050580c40340c60303242101980322200c81b410072101a41d800d21610004a1f0006a202c0d402207500784488150b194020002100445688000d01038000300d5003466104850010840d00d416410144075041c02d85540c02100d0450303422000c0b910044041d54648035480e084054201d6000c200c030b0b07101152070f040662020b40554400d0301c480035081281c4188207400074248031048042131044440307110030b5014807502c8418030305200a651000b0a440b00084014080c54 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 887020503 1250 887019253 887019281
    0xf0d090c05090405060708070f0509101e080f06100215040615031505070e18060406050a030c06082d1e070314100b03041205160305091c050c0d0c0801 66
    0xc414006d400390416100e0b501700015251855942c00c800308081c00c1031017034420160140e058030350380c2030f4154800c000345900c205801400c2d0044680c1249c008164403c1a0350100360080c510000c50580c1c54030035414221358606802600440014842001000c0382c014010358407030380c948052150f460400f44215002e144030b01c0007020994800e03100c03c000c07610020309013024003002142c921500c0e0349014040b07a80011010890600307079100b1001ca405080741d5400385030415000038007c020000827201e1003007a45c555039580c0d0f401d603035a00e8603a64480d1a5082200410868050040f1244094a55594060083c00e0346061004084000c20880b5508644802c0001e945040c003800c3e2900c185603040d0001d400740a09825641010500e0a617840003801c001d02803007070b508403003040078041d1003038071144001c1e1001e401c071454482c14060a1a403200310301510a081c0103907422141410144446030042e04440200288887c21040c0101202c5031b440540f0b146950b0000098110424006c082000700d0721 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 887021753 1250 887020503 887020513
    0x1218030709140604110306040903020c130903020f190b1e0901061502071a0306031207030201270b0106030f0b130c140304030503060103090201171512030f0d090c05090405 75
    0x18519000c03402c002810395485142000c0b0101d4030a1100c809032908450203d60000c1d8441c51494164a01218140000e40100701c0c800c02d541008101d41c00820441c0c040e4090310328040c1c90384c00242e00c0750b40401d0350940000602840c3d00200b0100d50f000c1d5889000c0400da09a540d25601c00101702c10f400711220080d81c0e45400c1d0511040740001708909028010b40000d20240c0c0c04c016500c6802061821400141c4001100003512907078108000900407880e024016a83d8542d4200240601181c0e901072002034402000d900f030b1182c08568034443d05d40c001c82222440d909105045018103115081e01d05169142e103000112559548000300c0014018040001d882d01e500c40080c0c00143c000c80c805004c1581403003044040b941040483c0c1d884242440c00040740c00052006854140c20500010009007a030340c20070805500e041011400700ea01110014560340e0113051440d500c1c4600901d078450168240006940d0890b1504000301d014400c070550b1106a0711040498030500085805a034181c5c09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 887023003 1250 887021753 887021771
    0x2011b0c050f010504030201021e0c090c21150f190b0306280909050a0b0c0c0714010c0f0f061107110103090f0305031b040f05031204081218030709 65
    0x407281c2c00019103032007800c0150500346941c0020b512011125500d42c2c10820200d801d03031511406002e01000c1070001011680c0701d081c8400044840e8100041f5a03c446042850100000d00c1101030b45105500c2d07980040d0400300703c03109008088403c000f1041d005090911410310041042c061500038210612050b5180d2034404100a0040283c1c0c0021040c0510929000d40d40b04120b1900701c19030f6480200070980030b02d0707841c1c01481c0c440800e00c0980244840c40078031007603082c400300819103620107408a450054641184072001d00d0780c0041540860b0a503034448002941811b507480c100d038010608500241c410740c0700e110035a04000649625840005101010080701b03080b80c1c501040203280412031981c05176100d01e10ac46140b80041e0034010b0100000d220713130508000c0740e4551440402015112580d074000030103601c05600609100c0c0c010010041011682001606c2c103ca100744c009001d142c0f11b88103005a20350180c00c4640c1d55040d10350b11140c268508004000c01803905010002d45080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 887024253 1250 887023003 887023009
    0x405121501140306060a05010c020909071a04140a1511011e06080d030603020d0f02030a02041d071a0912030c0f06100e090d0813051e07060503190902011b0c05 70
    0x20001c110612a0420400174003023664441a10b004260b03041d20a030115494070200d061030015107610071201c82a81c4046401402004d5002e0130498410070b02078a820843c070010461003601c0703406042d660310004d0000c007203000e1089a124507421202000055803550607100c0001030580c45540c0e18180d91221070401080008204510001c840e5141c108112401d540c0007d00c0c40021400261684082041404c00e41d5000e2140009140e4010b00c10040f0b01d586007410540244485582100e601030100f0015810202020103201c21402c2d040103441e08103510b04001101d0002ca0700c04440744020310112084110070890341c01c0b4000828010003a41c5408042d0400310f070750326000034840002c02c6040c0003007203800103080c1c02100450308280b1003943d50020401c071a003603e180c02401038030880805058400303101c0000400c00d11007400780c0304c0003500d520054070f0ba031100752240c10324880c0a000b850030508083d4010040f06105141c940800102c1040190040c4100c10050344e02922074002040a0b00d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 887025503 1250 887024253 887024263
    0xa0b1e01091406030610031b0b031e16090509070e03030307121a031b0411070309080105070504060c0f0f1a06040f060f030803100b0a0206090106091104051215011403 73
    0x26008400420661500700c1c2d410301c041c601480b004220140b5041e00d038008244408608c03005d80050900d0b107459203040c00c1030f582d4517030101d5107102040540d18041424004030030031200324016646c0343c070404180762070144203004e10010b0001082010b00e80714a1150798003800114051117280e83e07940703040a028510f02044421901004e0750128488400c0e11860701e0205034003d00601c0c4440c914104982c4001140140c10154100362850a000501c5410590401ca02000b81d81181d402004650350301e070400c4c1c4a82c4254011000402d1425a099001035110322805210b2441050b850039000d2940d03548202ea0300d50542d81401208a0004006841c1054414a007611801e1101400814900602510040d0342030201070843c0d400040000c000007c0c140c508802030081080e1282c3c4c491840800a44848054a10f40403035402c110700000c00c6a41801060000282c00c010b8515040c644801c00c0301c00094642d1308040c5020b44415104086042c051150007884000c0082102a44040805081c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 887026753 1250 887025503 887025511
    0x6090a120207032111160311091b03040807020303040f0509070306060816030905150103150b010206013b010602010c090f09090203070b03070314070804050a0b1e010914 74
    0x5500080081001c2090240a2115051410940914058501c0007103403540990075149405110760300400c0c200d60031b1306444000312801080610b6030103100303d0030007070010004d41e80c3c00320610300c40c9a5200d085643d0802190418811403000d8a869401d60101e42550031a0340204000505c16a04200d6410401d58599200003140f80030882c4a0070044050300c010800707014444a154849014100240a5800120303001d800008441c0910549080030821510034081180c544a00c500b11040c03104460107030400b1032070141c0141030142e0800007410045141116082407071590084c0c1c0700e51620301c1880c04d02c59108131402440d0a9070600c40c019003920a0403c441080091030300041001a55681c08a410345020f2030003c80d000b1081c0c000070780707008510380003403e07104000418400e0103905076005000300d026610601100356540303c02520b05d41421a4080d0280d0090f0038003000144031204850350001070320b054140000425015103c841c0400d03007001c1003441d90f0b81340c40c80c4c0c200c0c007401c43c0d581c0c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 887028003 1250 887026753 887026757
    0xe06010e06030a03020d0e01170a020a021606050a0e0f090f04020103110a1d1f0305060f1008060121020a0503060307090905070308030901020d05041101080c251406090a12 75
    0xd00c0ca15640c002d58078001c44c424502003000d000c04554180c0c9c410820801603080140300c5440342d06049070100300a50007807000d44054032402103000340301c40c0d644085404480e140c0d1a1281441d440403010303607200300a450b040b035001d00250342d074100e0b640d20141800e02868041c120328446160920015040710341a031401960400144459900c19500441000e500d00580c1c007524031604045010445c4c1e00980401c4c880c4c04a120312200c0849076041d40950710580c0c0032640305001220303210502010610500c255000100354400040300303540940044284813000e1a03da40304c0d0160704c1100c1080b6049079404c60b0014400100380081845e04100701c2000d468180c40402c2008000d6481d166141d05903c0004d1100302c01000055101d1001e605403143c01e50900c1080c849403a10340f038026401c2c006020030f21301244480010981c0c1c9281102034500b41580780000c0e004017030701803001d46652403a01764207c5500740c0c806040b01c683c2c3c805000b403a005501d10802090001c9680c50705422405000780d907039013 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 887029253 1250 887028003 887028013
    0xc06040b07140c0a06020a05062d1302030709140c031303080c070203061501030c0905060d20300603120d0e0a0b0a060803030c04090b010c060e06010e0603 68
    0xc21105101111019035118a2054042034402c071a036003070240c03035000194400e59031400024880c0e004903424050303138458025901c803541c13074040603510241d40d150032261007420303488035035040d00c224440a50450280b4560046000300e940c00a40b5119994001004407038131610244490b000898884e90013400c1c09440c0c5046140400d41041142c507002009010480c0d08070108100c12400022a01800c3e009002c2c0c546515105e040b149016202814503070000e031074000d0704070784988504111015660003d0542e441c0c10441209000601850249003940702e08080070301e07090b0002c210081201c0400e448a01c0090394014110080d01548907224008100c0e203001000820303500840c10030082c2c03220703841482e252080c80f14440d004291241003d1078600c500380c03441043c00382e4560081d1003410f407440140503141d110300103561680000e56203002004418001400f81d2030f110741111000303503030600d41000c1450340390326100c00b0307141000b07100e05a6400c61001840010801402e4583c44041580180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 887030503 1250 887029253 887029259
    0x3190507050c0613080601060c17070209061311031302040c090b03010501080408040b1626030a020c1501140414150d050309180f060a24020307060c110c0604 69
    0x303440e50700d030741e1559201c0c1c800054000c045003011380e42c80d40070700801c2040320125030316040080d0549203001021b07070f200e0419a00c1d40481b030305050708580c00e0a9019041408a8540d84203000000140030041c1c54801d40f2031403480d400e4100c0c1d41c0913601c1600e001c00f2088040c1060f0060008a03820580d0b640f0421844038400d01815500c1021203045607070a02e480141607481c3d0401c00c1d03440c056600b2126243c500098070358030b541c03440003d840e0594007450302001d0380e00803400161140a80e030b407908105000c00740000b0b5224440390340a00034013201c103001c2e110058002c441c4003440000c241c0200c658000040f10b2000c941c24103102d00ca01504d0321504001d07150038600310381b99018411140c1144244800f9500d0010084203000343c0300081401b0780f075010f20900040034008090400c070b6464034007080300c4000800d6407500e402910b0440780f05111181002c424030b00d884001c00c01d04511102544010803280001450b280300c1e000316440c032940d4404084c2080c562680c140080861014031681e070610040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 887031753 1250 887030503 887030513
    0x9050103081204021f0302121006020703110609030706080912270f040216020405090a031e18090c020c1f05070c09050c031e25020f0d0203190507 64
    0x2070341c45101440c60b030032860b66940b0004003071440e50680c030304441da0701d484044c50054050b009060088108200040d280d92580c103850b980c003800784160401170780300c104100081195018058684500a00003a1912080c20003280c54803265a00000001b8154000c00411950070701c091140450001c00361468071140d000c60203010300d0a0f42150f041032020340e2951015070358041d100c6510010203001035445882100c03218504a0030724000b07900507400d03c00003569406021600c65805581b5444440980000e045c040c140d07006a01000301c2404070400284d035908481c03608510052001d03d02c08903500901040c000d04200e41001c4c41409240024511380c0041d00c0b140020000d64801d02d4019182c00c0c1c1030806a04179030b102c0d0b211006c0345140030244000007580f91b0040d4400c51303030004038819103d02e1025100032944220750300310a07851a81c407001d90200900d007414091581d984102d8211070f20601c3c8075424001034002c00d8016031b00004045140c941c003034008405100da2828554103064060320b40d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 887033003 1250 887031753 887031757
    0xa0801060f0507050607120b03030c0604030806030307060e2d0607180b13030b06010c0308010504090c1d06040507110307060b041d101103160807020c180f010905010308 74
    0x5032400d0219200900096500c2001901c69141d040412920702d410700c01c0c0058031258042c2600002e59041c1445c0314a64140001154180d070303000b8005001a0751580c804440e05000a85660340c1400200f01c00f4011410600582c5c01b125040c1c000341182103082051840000c81c450406450b83e00008000414841d0204116901c14414100091816034100d55280350741d086130440d107088200480c90a0390903054040010540c1d210303801c1040580c407a072005451083c80a80010005545200180700d0703030510741c001c8002907100c1d043e21208142c44420b40380c1003c014401c5800d4060540c0c080041c10700c3c003070043d150454454281030f000c4d10801c1c00380303644a210307424002e0656a11174080307402c1c0c0c0c3ca8542c02007e545d900d14560140800791195001d0f10740140701000d101039410041d4648000d921102100d0041e0386d024010081100c0b2254140d4441d9001440d0304258021f42c0c0021030591a40d01d07030405060f80d0070f09c035072200303281c002d0051088a4042c0c0040c40b01c1498036005200003048142 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 887034253 1250 887033003 887033009
    0x60e011401080f0711010e100608030405100f0309120315051e04052a0a030b220905012c01140c030402010c05120d06090e0a2a0801061d0702030a0801 66
    0x83c42d00c00c1d65107100302954800343c00c0d03100c201150310f0500c1c050f68110000c00c612603420411030050103a07035515555103503070780554000c0303035841071180040055403401451495102034041c100411082901c0d201c0c079004016108a203400700703884440144160101e0403c0401514080b02c1c0b0103582d03030b4042c03000c201b040f01000304035014550350b401042c2040216640c004c41240305050614040241702c1485595800940008001c00c0c01c01c641009a4902400405000e1480c80003441070003c100b9000d00c007800b0241c805950b203560300c14101c0d9404140100d44050b40380510416030411000814041c219110181a031580144000034049045c80c41e8044a81040e02442c004001401c3c1e4200941080d041c2031050311821400142045680025040081111104041080320f80e0b901c00101d07480c7c0d0b541d07440003000f07465035000c8442124050048089008109084510f0886d101c10038103084910541044050001c00b1401c3c001880050385001c0c3d104040d03101440c2131040c0745101402c5000180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 887035503 1250 887034253 887034271
    0x504091d0607120b130c0831151b0906090e01030b060307181b020a1515051233010303031107050d180f140d02030a021003060e01140108 60
    0x22403000300682581001d000031301d0003014584074034403509808004000703c0d00743c080400e182d100080c0305802c6851a117208840f034041402c0954201c45515098800507072011140250003a00130b4a102c1203501c900c008494101030b400c5030b07101c00108058800306580e03100c40d040021034407060118610032045107044951101455038540c8a030400641000c2c00f5410145050200c80030308111041160000c2204140e1072618803080700d12040e041780c4920041c0c50181c141c884001c942240e50701ca40c1e000003180700c080301c07000d81d11948501c0000d141c100001c000c0b28155210140400b0b10111048041802224610304c90145244081c0007442804c4148409024107665690042c1030340b50b010220f4025a520034260350501440e440080c108464000b005403040d030440798040303085505a001d90042e01ca050300c8150b25882c3d1002004a0f0040280d0b00704e030580520b104d40001610341d003040c035064007504d84000c5840c504007110b10b444054160310400641002c4080d40e502d59030400820b40c0c111003a5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 887036753 1250 887035503 887035517
    0x70605090709060f21020102030c12190503010b0316031b030219081909081e0d061a04032d0b240108160c020a0b0702090907031a180d0504091d0607 65
    0x5d800183d046004244840405010380c41c00c86600c128000020508120003182584070b100154000b01c4250009008000c8600740c01c10118510401031001103100c003400b8907000c1b40c44a40d40000c0260001100303100c0d408a50003141a00c1e42091420000071410628580422186001e440d541c3c2d01052160403220041e680c3c1111109016620701140c10401803c0c0c0b040103901120200c40c0c0455104100c0030110919110010403003200f44c44d05501d19801681d500342c02c1a04586921414008400150a103405480d06000031aa013241c3e035502024015500100d061034404400a403011002c0405501c0c80e05540a81c0180c0c0c6e081884150040d0781e00c00c0b0262410343c00082500c01c4030040710040d60040780d0101c0001e08461741001005030138802d031003c050a49646400c942da90416000040070a80e80c0080b43d003184020305d000f19400508600c10701c003002d4040801d02e0414081c1c01c0d046002540000d000e102d400190f00920701d600c0c400c071200703034010300d000c01260b0707142c10000d8540d001300300c44 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 887038003 1250 887036753 887036819
    0xc01090e0a0204050904030908210d020c01060510030b0118050303030705031302041a180903030606160605041118040c062601080d0e0d05150606070605090709060f 72
    0x2160381903c01504014220340c01302d04041c1400390040c445481100c4079072265002421044074121010840d400070a1540c6040090845003d00a90421080103145641c0d84000051030b6903a2004040000c0d0541c600050102d50400014445014070a40a2140d81c0e0700303000300900d1f20000112940b120052074010745a0319021540a00011840c0c00a5403050406070804403c02442122803a00182100d1418200010b0306880e00d6062040360000f0098005000258542c10180000c0c60130003021310001c8203602c400ea41c1c8004494041c2c8041e00ca90030307002c522156900303100003040040c500c00d8540441d00e00d00340c4d5840f615a5941e008450404c441d40041c10007002c00d80b2480c10468946208400c41582c4456601d6590b150b0010784000258402541c0700c441e08042c0000380c0155007240103045004641543c4070311030207000d0000c58100100f00a075401041c894490301e40101945000380502610701180582a62820b41001881b005260420080600c0e80d04410209902d410040200108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 887039253 1250 887038003 887038021
    0x1205250606080d030f06121106030a0908041203020105010b070b070f09090e06090d05160803061903030c03080f0106020a140319020a0c090b0d060b0301110d0b01110c01090e 76
    0x9059440b4480620440e00c20443d0303160036401c6080d41c0f5a20b41010016560382e40f5840e010b003c840380c406404c65481c881d9105003030802c48021984454806804038000180781c2d00c07408140d00c254031075070012080003880e808041d42030041ca030060002c2d0840134101100c9441e80c801c0103401900410501030b4095104005a0043d01000e0040c40c030032038108554207101c402d551b11041c007220101003602a28128944403030140007540c0c030b80701d11020402540080c1e56100c403040d60019140c030354811980d030b0f2020306021003450400c0146119a40e0031480700c04915015281000160601114004460050040680c00548041300c2c54001e4040108000341c04001404e42c821440c5944c0c0c88413480c0c1105660365000116140510b200301c03d4802481d070703a40302c00d00c112120000100d03804244007499602203100ea400c5480c41000040000400b2504041c0d580c0320ba5205248556400d525088001e0640d038100d1a02d030b6a10017810003601d007411200b070000f840701071039001b140740da101c0c0381002c581c0c10b203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 887040503 1250 887039253 887039261
    0x90f0a0b01090317041d01060519050409180303050a110d09141005091e1509011b030f0b0f1f0507050f1608030a020601140301020d020f0712052506 65
    0x5410824a140d0450550030b40200f50380180034184000d03d01b80300c060b40600d0b415901504890041e55018140195171500c0d0b05040300303a4008804102e814000030810211a00c940c07100742500e0b03900280f17500780920f000b90941308000d003260489403606000c00c00400e00c81003187d00e028140070340000c1d036014070310307101007200c2c110342801d0524480c4d210008854000c55001c0b030300441c08002103c0c910300b6031412058040d40140880a0103800c0340c80d0710150700703c00c1c0d580c25070405040c40003c20030340740ca001c0460203006412040000a40c59106203142d280344c91040c0801c40c01c040d030b4610251800180400d44c4a4074010102494110380317421484107901c40d03420b03100e0440e03101040c0c9034004e054510f0a943c840600301c2070701c503c40c050a80015905000004c580c203540041e006091140e10307044a4070248056041c10f0382e0555020020511403c1035807009101c204c000d03117070140d100c030441e0428040b6090fa80461606211040158a020301403004062644408289500120700313a81d00d4220064 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 887041753 1250 887040503 887040509
    0x6080a0c0e0c040f090e060f07020a0b04021c0606210515100503070602010203010e07110d08250206090c0d030801030813090203160f081009020705150c0a02010605090f0a0b0109 78
    0x711014102162844050300902d0b2000d1031b01c0d003240e50300c0e250710306a03050050090301c199001da4005044180056254054158061300090428a0805a08040d50031950306203104413070b040d036030b41c0091280c022880810111481e034a1945060070204c0e9840990350203c00034031045400280c4005481c1341d0001d00200003402c2c0240c1610b02c43d80d500c920182c040e41003802040045d00e01c290000303603124031071462103480603400750041005507854107080d1a54400544420700c00e140c8619901d1000420451400740e240d025801003846180804409041c100382110075841a6480c524003000b00e81c1c00a00d01c2d0540340c1003814180d07140444561164641525805842c0e807034000710803c1a0240101049001203c10b03403140108602c0b40c0b0700c00c41c0c185c20100d41c9202907110300502400b11a40b150301401860344504102c6104015864041d05200c2f4200c95070fa41d4030380002806a14a5428001c24009100c00e8621403105d041258050740c0044000b80003181c9150344018111300c1383c1c8219064401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 887043003 1250 887041753 887041769
    0x2030612070b0d20090906011205070c030908030a080c0a020a0209010909110d020627040e0a05070806070906030c0c0209010b03011e0513200c070906080a0c0e0c04 72
    0x101a580da94410354940014082c0c03030f0401d00d06181d007190001101a8841110080c458903403512a049040201c12174026100b50304101441c0c8403850404000e200b128003500c1d4540742c07980b4040d800d1500a0240e00e064100486942050080b00c01003500015601d4000c201c083e002515a0803a02c8220700c0c0c030340c0007680a17502c8148a000018604203d40c003181800d4081c82c0071041d5440240b003400103180160030000d40244080003580d004251030550a203602b081991050a60440b0100180079515a40c1e581d00654005074248410000100041c00041081c8400380100d0300c0c0006014040503031038406d92040c15118020303030000d28440d8013020900c0354000c00640e00c9585600060245800074080d03903a1540e264800d40381c80d00200281c40d011120028101d050191543c020000582071303008042d080e03507501c40494903010288401508944a100300240085498101c501060324882d6020071a66041080324501040c40a907040c4183d4000702c07058040790b101e1114405070303445154001c1039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 887044253 1250 887043003 887043013
    0x3161704060905100302072f0303041410231303080d050a0b010215220f08070b0a0614010c17070501020417010c08010909060612110109062102030612 66
    0x540030340102c010010340b042581c6030703080134409000030b6040340b084041c060004540550511120682010541030a900c41c5910030070300480400413034610780040d00005a40401201151128107000000180036006441c100d400c6180809100381000075144800c880d8401c002280c21030300c1500020b420081d540020099039511601c0c445000416080e51000d0f4202d0400011503015840051000307810105401803c0a68443c0110b515080c44054028204080e000c680300010403105070003844d2543c000d03600195103128914003840711603002440d00030200c0c9040d600b403143c00d294007079810340324600707003440b001c07044090504140f040303c0181d81040b800d034005444400c2000c10340103082151070712048992065011b9140310f098030040444440020400ca004221400264105241d0b99000e6080002c8980d151aa02a50200040c505440c0901c0280c2c0240360b95030700510361f00c010251842c1c0b08401d282c050511800d1a00404460300820350040003003503259641d11044408201d118048134 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 887045503 1250 887044253 887044259
    0x80403030c050c122503060c0207170105010f0302040b030a050f0a151a010f05090603040305120906070e24070b041502040b0f0d2d1d03161704 63
    0x14840081035100701d495000b480540f41d00303811300c010509100b4081c1e42c0070700040c0c600e514506010701030296203d840303181030403000800b049192007114080c0f4141e6000d002094184400516481d00708064412960301d45001003002c2e0100c0d00002058960480700402d590001800081c90a200b02502900c00d0090084a403c034040001d001c0c24840d1041c45140041d48980744050308403800066441c280c6001c5841c50a00e80d881001c080707040103614101141003610700004100150000c4074100d012070741c000340300c00c18a206203192990010050740140b0b803030701d07229500600c0954180c585501034200e01c440c1c1a82044800300c4000980714401c80c040d1540224148030014040541d4143c90b402c08111031004140e07454022a400d407088401c141d49081c295201c00007a40d4000c000c0b8405503695407030a00ca254040200740300a201c1040c05020400d00c1d184991000c0701c080b020b081c044c0f117010184042c2605404010745d292210301526070541c102a60074125941c150280390000d42601c002008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 887046753 1250 887045503 887045507
    0x5061c020c0708010c260402150c012904020a0903081b0f1b030a03020d0c06020d050a0b0913030c021302070203121312050312060307091509140112081608040303 71
    0xb2142603405550b541c4a0035040d03921032591b4504e00070b50f15080000d40d900290250506d1840b20603003420442016184c9052942da150844051359010009030803d00d502c50135081d03800c075038220454401c907411403400c00b1400300034203002c50f0f40c84010b03d0980c2c00310390300807070700300c07110101c00201ca5074010364640090090403241c903900d00d19410b104d41d2203aa0402c05140c1000100c3c020f0140c1d25170010103070f400d5002c00549000080c050101c403903540030007141d80d0725402401220b01a0b002c1c0140030507449445010044448402407210a49822100078840481e92042109400e00c1d0103489500070401e010140c01c0207441031881c0a50107104128407400440c031407400401500c0316442c0c81c0d003201ca840700884000d1030072552001c1e10ba54004d100381e0501c0c6c00c0e035030b5000381c0012000741111a1940d4036458181614018603e400e420055010700f001007003410f000b1805d1103143e41d404d44402c1d60400403070503001500d10002030040b22020410020314000d09414072811500301000503162542c038540 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 887048003 1250 887046753 887046761
    0x209030f030d060902030601080c0d061a12150112020c071208040e1302060306040e0c1c05120f070b040f0b040b01050414090601060f020c040e07170705061c020c070801 74
    0xc040b012902d00710300090710f11540e01c00e0f240039003016036806000361140110580d41d60803174010350301c3c0c160313407440000303010300d600c0207011547c0100c9001503032240c45000301c9c10310400780186011580420380c4c3d8009443c0e0b90182102644880c0c0c1680142c480d161040310ba40303808115040880d5040420b1b1400b004c2c0702d25140a8012266442d5001d40301e030369002d4034021104e50408000f9003005040c000301e40330f498542c000d0819440c3e40c404079141190b2100c00581c0e0460411a0956044004940307007091250521011003050100d040a515003e0095880e075841d22800e0405011035210341e010408004144149968407034018031540386e207061509040030401820711502d4482c03071a180709034130071000044c00030340b0400c660005007160760f02c0c040c81a1040d2048842d00b00450041141124481e510f078400c2070441e10300080103008841c01c080500c1c15020030801c101d80c0310b5100ca04100a15540d007822240040c880410300300901d092059040040d003e00c0000001600030b0480200e0800c00c1548 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 887049253 1250 887048003 887048017
    0x50408060c04081c090303051809012301140a030e1006090212070c030c02040e070504110d150e070e150715050114060301171c020d020c040c120c030209030f03 70
    0x503140c000810031341003260311040b03d0b041d202060340c0010400110707009401410103002144a0403280184080008007580f07802d800202140c2010200100707036000c111aa490754003401c0c203059540e08440c620860722401141203180c00c00d5111307041001c00c2c5405200c074100c40310010307605115075500c410242e0046c1d040341000400341000b03180055034940c0b0540c1c4140c0e40e5a01901d50480c03074581a002d02000e0240ca000416040c450740b80c00241c1502c552280d201000414051141c540c0e0403411140d090700e490082d00d24019880b01c1080c48003a54034030155400c50f03040d082c403500202e03106021440820400890482c034442c040b03401c2083c40000044040c003603070f01c2c9030b0030425a030300c4000103224500402c1c200380d00507409200501801210743c051440d200914011102c0052054800c42240d80b001106080160840c103203c071030440e01004004020001141c00b440040403008004109808050305103107402c1e101c215030480c641c0a0343c102c540c4200c0140c159107402d8051200e0b150b4a0713009031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 887050359 1106 887049253 887049269
    0x30b0904153206010e1008070309080307030207060c020f1f0b12031206010c0b06011b080d0b0102210a0804080f0403030305091009051c050408060c04 66
    0x19000101c8000000715158442c050074401c0032070107601400700350520084402d900090b40d02e8994a5115113610300d0150040d59600d00100c025285800000c0e201400001c18810040c0d1705400502c1071a01442060051003903218040382d07541a083c08078000d0760004004000382d42200e070011072559040a8021800d00284c2002820054450f00074118942c000120700921101310640c180e07118000742011203071003405480b04205041d0003003d0904000a40000c012203c03c00c60300c0307441c542c0e080010742d91503040a14a00000b010307000340050140c490610490990401010720740c3e82c4080080c62103050291098080c0c40c0b207000a04200c444050500280b00d080349480b0140c07000350300995001c5000c1c20038140c1d00d0304044e04c81013a5903c0c181040802e401244000400b4400b03042c07800b440340c000f0700103080121400d00840d00054554080d170800e0200c0c05900401130000d40b9008 = true := by decide +kernel

theorem cover : BRFrame.Cov 886870503 887050359 := by
  have h0 := BRFrame.cov_init 886870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 886870503 ≤ n) (h2 : n < 887050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
