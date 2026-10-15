-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4206
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:52:08.78798+00:00
-- url     : https://prove2.me/submissions/ce042278-1bb5-4372-b9e5-d14d5e2f123f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 756294964 ≤ n < 756474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 756296214 1250 756294964 756294971
    0x9150901080c0a0c06290901030209070c0f061b090509040b04060b210c01020106211b0803071209060507080d0b03070515030105030105010b16060b0a080102040603050103021c0b010603 81
    0x282044d00498142c6580c0341e0000781000040310b04061001d00910725520901034140c01c02c1c1a400030305001e03440c00e050700c1e0003c1091640da80c40b4030080341e10348481d00c0200d400070000d0104400040301402144940101c400035943c10a080d260010060051075110314801d260b90814000402c901202080e08030b40c000700041001403541c0c0c0440c2d07034500901508012580c0040010b0014100411300102d8042c090340240b05140c0d07552004a00040355070b9401500b26408507149000920132a11090b030340340b03c0c2004260b884c0e6185912415a0000341040e41d400c0750581c2d81d0703c0b490341e0029590003e007025040030303420405141c5a40c0f80a0051040d000c0215650b001c0002a6960401500c3d0091400400e40707107a80301c0784031140d4200d030001e1240d28020341c03d0400208000712407500307a0b42040d10340c501e2200400843d860700d030301074800c0601c0560030071542400070604110030f0008002810b280e48000c2903a514602c18001014081e14440912031822180d10002965400b803841c1110325600e00030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 756297464 1250 756296214 756296227
    0x3080f0604090809010c0c1e090b1212030a0b0a0308031006020d09030305071103010603080d0c030207030c120e09100305160510080702030f070b010806090d0e190302090103050309150901080c 84
    0x1260b00f8421900485071b52070741c8008c5405505100f40c5100c0554101070814440c42271524184145202c83d613400c00e840e80c1014114106c100f9070a0040c541c0b1100403040803a0141d0401c0205503e07500e00c1d0800c0e248a10008200001c041c1c0121605004024901c020300290f803503050007e190205a000080401800041c88030600400e20074403a04404010001c0000c15601e1900300c226500031680e104080c3e0514520385103060191007990841c64154403884404505907442005900741c07845c2000502a00c0c04641450340c41d05010503104030222801412001d003141440c520380b200883c05140c1c0d81b5000e000034002501d4191700012400541d0520031030307689400030182d0440c0910188070400c40d1000c00d0030781c2800341301001d143c103e801c10310a8520070740302e521a182d103801f841c0301000040740c54a03c805002d802d00848141c2c003900c1d640c1ca00203665803a9400114140402c1c4d00c25100c80d48003148844d514541100e2145803500b0180b841d41c40c28010f0f00c0043c03c803880c000c01160b148100031810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 756298714 1250 756297464 756297473
    0x16022d0102030c030403020706051c09050a1a0a140103150e030c03070507050f091003020621042d3c051b310905030703080f0604090809010c 62
    0x806a0026411000707545a2070400da4240441d04200c60a0b401486000400600c041c00b40702100c0f82c0301c1e00d1011442e0340701c40010400000c0d25100508450382d214440da000003103002c02c408654880740c0d80c8074000c42420802c40706015500c64a110f00c0034045503400410000b002200038505040d0b514402051051107032aa440c11070141040420283c00002025010041c02103000700940e54129a81484000039038248412080200c0d0000e640d00c218030000d0001d4a884805400b410201e82d0000f040c004c1c1d03882c03807101100c00c199000c9035460503910500065800140c140c07240001c601a410314518030b540c851614a4041902c0034101c80300e541c0d80f401c5165445c0c000c0c400f0945054494800f1000c461030140d07600d0010300ea001c405824907442c0c1400c985841500348020403103900c0c0c45074a2001440c1241b9000a4160101c4480d6a551a03040c0025000b4009440041d011b621034081da031511314100c00c0c50581c0180041c1c80380b8a051080c00001e0160401e031038026100b840c00304000c6915150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 756299964 1250 756298714 756298783
    0xe040b181e01080709150605030402040b150d020c0106050d0203060f071e18050910030809032803030b06030f010312020f0601090606030f090c05010807050409060308121602 76
    0x1c60311880c880724000714202c1070000d646800c44034100380820040301071340d84070b10b02035040b8026000018810000300b400351400340c015020750f0324000c00104144403403030340c02c588560000c5c410011564012a000d20240d00030300c6420003c0270b06492000c0c80c0304180d0b00080e241c10000704040080078480c004076445512910b080c20344000640e1000410000c401c40281240104d040d600c0d01a8003031100214660600705031103030040020081040d219411991180c1c0c0903080074010302c3d0148030705090314091341310350b4140c6003822a4030f039040d0889009a081c01025200c2041416010341420014451406401c00001c4d0440b0b81045407100038524000040f410014101030703030201c81c1724100c00891500c80c07550040c01140c41c244c500304240a10540320105070384448002400b8110242000c0141d54000c1054a40c00704140c80c00516281e11003080000f01c9809410903a009080410525024608401c1e101d030801c02c0f203c0013203541b0408460081d0b4510f80c900f00e1040340605100805e0302c0030301c00710 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 756301214 1250 756299964 756300001
    0x30708031f0b0c1e0c01050a03020c07090912030c050d020f19030b12070503060403111006081b090f0c0d0b1201050402180903190908030a020705010e040b18 69
    0xc07120180641c1c0d80c12580c1454121070070311030181c043c2c0300c0407064190200135601281801d24000e070282d903015200540342c9800503840788081c15020441c1112a8000740305003000340420550014183c18141801d25000940000300703003e00d46403442c0d0071b00181d041000d94500a1a9500c0580c0ea004107584941c114010380410100341744518032048141501500000090407051320141092140034050541c0c40c0420700c251501a000800840c004c68421050300e90074010b40c4044400030156604098100c4000e0340c007000c0c40d41c2100000c80713011021052074440c0602c08413201c40460800c00e9141360700c0d0401404e845004540040c80510001580e0000ca01a01c401030140c00c081c030600740c82c580a07010840341244140c8840a03c01304102c000c0c04040d00901c0400f00550800f0392180e5440804480134038031005003c1c00e141c0015000400708010f01000000341e015113200361a201c0090502402000e521740f149003440340030341070341d250381c0d85800841004104000f256201c50504010615209 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 756302464 1250 756301214 756301261
    0x100c0509031e16180209030f0a0b0108060c03061309061d16090507120b030a1502190908030a1404080f030a0e0103061a090a1509031401060803070803 66
    0x9910b070040d00e20b2820841d08288010005503440c9003001108010281c92034002c00d00b08080084281e0200416540a0301c9081c0002c4e0403201c03130111700802e061a00c00226001c840c0c110101006011510041c0241d64108003100c0c24907096045c00000200c0e4514010007100e600c5680706986410301886070814407034040c0c80f21800f04902c4006c10030f035444402c0448481845003034450001044149885240d110b106603035240207101000007284405421000c0c0034580c5403140c90703102c101280242c14121a64020381c0c50050f960007907000440318840711640d95030300740034400c0c1e0204031490011040380c5102ea01843c11fa2900544007900400c1c44c0602d4105410b14451900c0500c10392a000004000440194480080d000d100300c00450079a1b400740213000c03900080d5101e00f40300c0d04407040984001c2100a041e80c0c241d42c0c991008507070f041d6070000c4010002d14416010004d0160508250721003c90030305c024404d19047c01d451590342d1043d424002c00451000001a9240031038004030701d90460007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 756303714 1250 756302464 756302473
    0x30207170d080c0301030b04150b0303030a090209060d080a031107050730120c0203010b040e0601061412010b0918070f0311090102100c030204050306010312030507020f100c050903 79
    0x118040030340e48800742002a0040303452038002c16603580654003540d04072944041f00c2441a40c0e240e441101a101c6000681e022603190300c0201c034544c0e01400035611901900000040c4221140104085a170014051600a15415011801261303620040380d43d01c04c22030a012a103102607500c1d182c89445030b00d10281450003030700f10120741c203180c1c02100000065984004000d60441b1908904854201c160003071000490320710801c0414050a40600703914001000050481444070104059940c80c0c29084900c0e000300d401030100c103030041d4203841404110300d0313a1070810b00c940c4041c019089060060740120040400e000b6160744e50002c040c0b610803042040321890341001e0001610407080d0600110100c2e04015418a424031041d007681d0240b001680102200003200b02800c0090460000c40d80426408010204090b14200700075402140301d14080319040c0e103070301c00c02000c5800240c0080110341102c54010310200d000542000c3c1c07910110710016032812402001c1e11148124800503405024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 756304964 1250 756303714 756303749
    0x100e0103080c07050a060e1302120f160c0b011419030812150607020d14070305071e050306010b030a0f0f0b01021002041a070c09110a110109021804030207 68
    0x98803800b405081980ca821507452a40300c2007000740103419401341900044014000405620b03103559030030b0003401c1c003180040ca46100e402c41569807940c1118506090510300d400e201c8610742540300103428000c0c0e0301e405020303000c0583d80c900f4101418810302402090328010400c40399074485440722000c524422044000d5036a05e0111000d42044c0e045540c0c0d520038074005139a00300e4100d540640008010702043c50480c25a003005110040540127030ba0000300079411640c1c1140800c0144080d500441c02820514642040e4114500b6825504030070003000c40300030045a2800036006054942558001d5225940c00c1c1801004140d824141c4244a0401104241c200d001e40e12244034801d00b81d007610081c0b0200351480b0141d100310b10540c03104000b8107480042980108001d000c12034400c0100003015541e42003558260790051408130048840050341e602c07000e030070090407d8200001c0c0021710404019800003001e001000840341d0716403061800003401c01d48280b044130050510280186080807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 756306214 1250 756304964 756304973
    0x7060c110f09071d0906010c0b0a1104060509040f06030503120a0e061311193003090e0a0504020a050904020301021306050408160803031630050609070c0308100e0103 73
    0x5190504001d07011540d08004d0b116003070811046100310b80607100c14030800416560f0081070a00145041d02c40e5a4070028298030b60000801000205a01d40d151500c0f18600c0040104594003540705d1100d0038907000040000031804003d5806010410a021605668401d43e02000c0c0c0f056110504460050b0800c1048100c2c502118102960140b00740d410355002110511403401c1c1a60940340310b00d8100c0c402004000c44c040c05001c520804004501c081e10100c401c18840e15403110001c501203811580188103100c622031000d41c0c0a82e41310350500413410b140c0c010454400312400707034034082d0003060001015900c007501116603250b80782d1080020079580725402800c50300203001d050315502030030f1442d21505030107002503001d0721031810146285882d0000a0102601c1e101000000e21540e40741c0100c01141840318042d04211403100200d0f01c0d15442002e100702c07000200030f030b40320301507205c18080443d0f4131507074044031141d05007010241600c8116501004003041e80c4500400d03502c0600110801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 756307464 1250 756306214 756306227
    0x30c0d0c03080d2a0207170c0406080f011b08131112060411030114061309050d030203070201060f080c12010b04021c05010501030e030f07150c020114010807060c110f0907 75
    0x5050408111240d8441c940700340704413004031005801a4040c60041c4203132072440d01c400c58000c50010031110306204220105080c0d510541c00781d80c81e1380244043e94a54107080c080c8887e000305d4a9551541e4481c442c1000c0c0c100c0c44050131414154211080050421280c510400c55000006040b44080c110340d080c001da42c1c0d40212811a680e5280d0a1140c519040c140505820b1403090b624107481695201c0c1407001d0190703480c900e40e41c26601c0e81014404280c0604c9a2540c0003503e44d000b580e02d1408080c0a801e407219a8442d07552b260000d00304010011012540418a200803070300c0c08a510344c102141c070701400e030140ca6160b100b4400034030219a0070301d501d00c20005602c114424010390f0b80c0c560064089511003810741003190410003141c0b81c4103005800502e8540d2080314031281d12880750b1250301c00c40d01001c2100015079034960000300e03041e002995450041480800400301c0d0303030404400400c5c1d20241c00e801403070440c69000d065155500c550519080c00000f826808284c9050030000b001d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 756308714 1250 756307464 756307481
    0x3051515120a060c080c0a4401051e01030b011101050907140a0605070f03030f050c120a050610030b01021212012301080606220608100801020306030c0d0c03080d 71
    0x18a80b03040e800d00e0165020b008441d2013111b0180e0800d0820014030000d4608034030402515001c1400382420800e268044400c00344260f4510202041c2400301c01455055030314180c1180c1d1081c40c1010b103203084151060100d240442c0c003880c0100d01c680f070840050760442079440558206508000410040c20b038002030f03080403585000100c0c5030030500789040c40000c031a45e01854001680c104840c4000c604a6170208010324802c1c6030000d229408180300608032038007550001c070750200c00140c01100c1c2c0c002412940e00302d40210b8041080e400c0140000740003101122540741416160751400455030300a1141071800b504490200c0d55903e089842e94001840034001c0b10781421a60a2500c002d8400f00c13103c20804106854030340081c0c48450821400d5004801001019504610210300318510b02c5800c4004010a84801c611800d00e4800d00d0f008024941116105038814800c2080b80d40d80000d10030b0019105859000c1c8030384190402e000050140d40018050410005c0d82140178205c03913129158 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 756309964 1250 756308714 756308723
    0x90519060e0106093e0307120c17040308092104050102190c09020d0e01020c0f0606030d020613031403010303050705011401240318030513050a03051515120a 69
    0x180d03880d643c40360201d40b002070b0f03140b620035a074104e00c0741c040c0c0300f94807258020218580c0c401c0410f0410705852017942c2c400c0301c4890004030210390400c03103a010350042500c3c070310b958201044042c0c10340c005005a4040100054100800a000b00c0d004400910200072006408400c1d5540384226a9691800390300c0b9106490041c410322082c03c520640070000005603580c041d4900b120030340350013015800b0b50040424500e40b40e645884c00e4882c0c0c03109100600701c0700b4164001d48040c07005158590b00b400c10041c81d0368040d8000850390060168007241c41175020f5054940c00d082ea585500301151041c018480502e44488000f0012040c1508400a400c0e4148180d00038400c0f01f108011813040c4180a10502c1026010016289600f4084d000d05103001190307440c0014808c0c3d400300d420a10094100c005030045400042e80c80a80094400c03500c1c0505025220800c0003495595000d035034114180102105032030910110314156940b2a4401145070000c0000c001e12414908607500c81c08100350884 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 756311214 1250 756309964 756309971
    0xf030e0402120f0c0c071a09090103030807141c1107050718050702150601110c0310090204050903091c21170916090902061c020c0f060903040504090519060e01 70
    0x10b03180c0c4c00d1107084500302210b030005421014035041c180b03d1010300004610390555030503c02d9480b5a120160020b000358002d03591a02c0c41c3c1020103000d00035100384800d86c000301720b040040d45410b10b01d100c04103030114100100002c1c407a640880050090040500c018090f000394980098203025400ca81c003c4000b02c0c034401c1206440c0d0311002e0340e960b82e00700150340b4411600000102d656000c3c08a41d040484041c0070f44d610300c03d40340006030929103002c1d07c002940b40c0d194107640030760900344600d27540007248200452070046c500d80000c1d0385416405404065500351740d441406c00082d83c51070010008076001280840780c0c8a10050031982101c2e01c2210a0700039a0001821780750005880301202c3ca2101c1001800c5007070a40e10b1000d403003034600c2079030044010084440d500443c040b1001c3c0c000c00076403006840d0b0f103804208a041c01031001d0240141e41c8204140320318600d000c022102203841c22a800035202505107003d03424a1b0301901010b00d803082901100d000d00503141c100c2d400048807080200b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 756312464 1250 756311214 756311221
    0x5070f1106130828020c0303270307030f0302030d0f090b0604050c0c030304050a140706080c0703090302030114090d05130e0a0603021306050103060e130f030e0402120f 74
    0x1251014410000c000c441d40c03110300801d2001c00c0d00c0352420701e1280240c20031854503907102c510100394500102c6802801500b045901c0c01281c0c140400c0b540040102c000e989070003640c1d011800481d0b8050528100180e43ca0b03070203607a17546c08108078002540e0003450b0b940e4000407400e001c2e490307030000b040301c2e400d480c141141d03070b0b92001a5106581c2c0c442d9000b261600e20380c458200340300041c44000c001002c410801c0002c00d0700417000b040650702c110311500003004440e885180091184005003070b04285544580300034030065400c016500d07400603100c54200e4640e5158101100e414031950b1002c0d405510780203020a01000c5d13070100c1c910510004040700c071501101c180803941d600c83d03898441300c51061804140980030f509003c0d603801940c21030780401d5807a22a00000c40c4641d0310308034a92000d655080070080d41d41c041c0a071800911149401d41ea591904050440f03140d11041e800526401d9554200d4042501484c610f0642060241085440300e00440c0900d889480a9903624050103101c0d000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 756313714 1250 756312464 756312467
    0xd0207050411030f07030c0e0a030819140304030c03020a0b240906031e0703170d0605010c0f0f03121a0f03030a1718030706061e14010c0c0906030605070f 68
    0x441e0f01450030000303130712015a0751800450051110903140401c002c100c5411007029074800070720101450050032455aa41214211110100410740644041c080007050b180742d025804800d8951080e0141411400c0240340d1800700c2c201041e112004203c02c4105082c048a050b04101c81c41e251a40c3d0320b4403070441001d420400049507812600a503255002c00d451500308000c4da00c100250010080032100600e03203a50360344880c0b0014415043c40140086032401440740c4900079440244020b00300381314095900e454416400364442e8000e040c084506401c0001c26104000c00340c40c082c481c0904101c14441059445203160400400c0c5124105007180c0907001d00d404400c407045c0d5039131515100390001405070780b00d000900050152100b00c441c45a466280078007400100840791062500003040e41c10800c202003a030361403004e20000c003030306a4018031024204002010681500b400c0070500c140851508100c88900b0307410031661a8144000041002001e03003180c0d0040140f61580030350b0803600d050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 756314964 1250 756313714 756313717
    0x601020118022b0204020a111b31050408090102070603060b0d050c070605040f020405070e100e041d0309180f04030c080d0e0a051c0806150c0d0207050411 68
    0x8040d512030f00c041020001a68240340303460b1480e042c41201d05411815400080898026000030317400b080034452040244141400b0300b030403c540211001d07403058800c0c0c0114002c090101c4d0a544082c448449034008400c015a0400211400000c00e024514081c82d0035802904821222409842030480c0403a0640c080c5c040c040c00d464841e0707011420954403844407005800c018100c40b4003510b04000742e101150080c065244107a001d05440714888441d8070602080f140c1c010201020480c2808555505030780741d01003071001c19484c0c0b400f40c807440c0d0f4050014000f0620105041c1021112050004d680c41d004809070800703041c11261040c40341138070710b0300442c0342a04980b100002c00ca90000100024055800320340042e001d010030f42d06000300c0313900b0303c5d003240d46100c0c071230b042903004000e45400c01904101c000801c05a5421140155240c003e01400300c1c04003034000307449207500e5a4100200401d50058030300d0300308040300310345401c84501006511400203005041c015030505400d08440079842c0e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 756316214 1250 756314964 756315011
    0x5070303090b09101a0d060902010e060f040807050d030e1908240a020703050f0d0b0a081f0b210319090f080c010518012106080c1c03050c030c1506010201 68
    0x1d21b14203045502e55241c40081c002460102e0510030800442421515800080e000c19031038071500b10790b141e0074482c526280042643c880e0380f00e0201c2c12041c0c400a580100c01703680d4400181c4d00168039a41c4076803030700003c00190308000303000e01c038440303078003901520307460307420f0504842100d40b10f08070303100c000c0600103922903144081e001c1031042100c02e04402000d8001c3c1a502a402000204080444001001c001e00780c0d0103007100c1c0d031002c501c615900d00c003c501e404030310038480f80400c11031303840301c0100d5010b040c02001e01f03461500703911481c40741c1401401264005000301030b449021b1503440324080c000062500416003590211040840d008400003845201444140c640c2400c01e29010301302c60625200110050402c0300c0000c4102840c501030303680f50321540b0300d0752000c6601030030041e8007882d20007a0501c4512910120a40c5481c00745140c1c1d0780003245801d07280c00c0799503583d0604024a1340c8140b107413101c0903100300000446034206046c102805140240c1c02444a004003113216200c02c0041d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 756317464 1250 756316214 756316219
    0x706210b0909031209240702100c030b0f030105061c0f020405090109030f02030a020618010b10020705040b27090a0c0306140c180402031807120b100e04020105070303090b09101a 78
    0x108820107075040221b00441c0d11216502c102c0d150724100c100b400d020760b11181480f00210342c68010f9141c15242194902d0f100d024290020012031400c0000030f04601c0d01108521203c001c0d807007c01017840000c00010b088540c000e08188102d041098189008149509042e0001030855001100c00381c400700455a070000680d0040549032a120b9a032480600001601304030b0390b580e41564800703a00d9031495a200030342190080d0420618010510090f1652190001e00c1000d4101c0d6107038400b90f10103c1750811191000d1034400c84c3c2d4500d6101031800141c900c3c00703000150b1030440041000350580080c20361541d09070000c1002d498036403211007103000e28921481041650031001440d401c041d400740d0703804075604d0b054943c01a00500f02c541445c41d04d4001208140040d50858207100c0c292000f590802405440403650340d07d0240418102040904001d0402c0000202c04040c1031003a040440e040b50801210b01040c100005056560002001203681460503c10f50741545402d0720101c0e40c404101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 756318714 1250 756317464 756317503
    0x150a02060f061206040501051b0c07120224070c12020d06110f0a050c0d2a060b041a1203190e120115060e030706210b0909031209 57
    0x1078102048856000400d400d40040c010302000b480c88070308000c0c1c940201e018800000300f03810000d00044203481c170210400c0da4400e042244c8148424002416000c03a04108947c040101c080d100003250302d0007a522031a5008200980806581c10310401000d00038450f21070030105640c0e88036400b240c6000400081d60103441105484003040840c0c1200d0a0032042d00302291408488240d0455030b0741004150308005200030413a0228481300f0484103034440c21900b44808000c550306400c5400e175030144111040c1d0300708a042082009100e800143d68110000c000340103207000d01c00714205c0400c00d690031034894074040c074006a00c65004011120421510001c100703110b07040318403c7e168440c0710407190703400c800700c043c210362903040a114411080e810030350002441454402c0042c10f400000070224400d070015130b02041525041061405190404c050000e800e54000345800000d2121142898000e00750300c0800900340404802800c881e00030842031011600d50380c140f240d1f20060001c800031504c19 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 756319964 1250 756318714 756318721
    0x2131d040f080913020c03070318030803010b0a0c08070818010305221a04061d0f07120213050108030d0f0e06010501052d0301150e10030f09050a11150a0206 69
    0xb1000b81800725014000302c3c4a01c244510758822a840000c050220741c10108120302003543c081098445004680d0325091400d04503110700003280300c10300c80e207502c1d00700001d04a43e80d1400750b10340008840e0403ca40755201d0701d40d41001441c65020b6855450710f0a05110b0104082d8080c0c4a000d000e4a460b42c20f041c250103404180c5a540540e42c8816a000652820b03100030b000034119019101d18800d44022a100b000c520055800d00da106428184c1604240c901d00e56002000606400300d0381014007455481c0010b0001c6000102003151100c0040d08010010800040000041600750302d0540104011094403004008450420000c00520740110700100000c2d84608040d20401c2140c1400b0642491280d0090440c02045c4000700c03111800030004110f140d5011061001060a6040080980c0100b1000071001403017541c0d100145559160380d5040d03030310154410300c00c00385d000007212446c03009070408a44568210045900c41c9540d4281500881e0f4244242c41c01d41c0b000d60014441500d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 756321214 1250 756319964 756319973
    0x302120a0c080310080c06030f0610090b0703020f0c040b18071806030f1119080703060803121503190f02031504200f0d03030509010f02131d040f 64
    0x90088440d80200a1002080c0010802c00ea00850041512800880c64103183c000004e00300746032080d020b8072620b000c2c4100040006480c50240d4050001c481004c0384101600040c0d69091254200841440000c210380041680000300035402284400498008400540421090f03903010341c1c01941001000c407103c00c105101009040e00040141002d01210b0406034030480381441c15403001340042d85030310000c90281d60030700c20045101b1f000030348513103006490303025100e40c40705509801c4100a02c250001e844644268492406841c919043c0c0c0c2e50741d02d4207070031400d244c1c400380d41090410140c0001c90382546400a5014064000000d4110404002d91a091480c110f40e000580c0c0501641c2040800741086c0760640d8481c910401c400b14072201c80240600d0718540301c01c07819001d18680b040c4400310b030341e43d400c10900043c0e140c0340100c2c4603520be411750f0b4090005916841580e07400407800d000d00d6402e1504410650395030005500b00000d8840c5407a80340c050a94014090a09140d5140c0219 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 756322464 1250 756321214 756321217
    0xa0e09010902040c081b0306060a0c02150a02010c02070807150503040c0302060403150e0706120f09140303370903020a050a0b06040b0402070203060c0a1809020310060c030212 77
    0x41414000600d07040c0a8012909440b036240d000b00024180d14204992161802e04124600300201c2025046140500101d010b42c4900c1c0e0f10003040c8918110050215990b002018583c0ea01c03a03034000362194080c031000b034003030042c008044015010350540440c61900000b8100c0460744403024819292803100c40a480b0755101910913600c9402d20f110200160711030740000c100030b52007880d00101d070b001000840030403100e4003014403005400003803007040450362000800c0c4100c058003c2c009000c00401076288010030348600d008010542100145141c240e011003d148180313080c208810310b41070f929031110001c14002d42c40000c0a1110741000010b1308865014049280c40b90048600b01400d5071541444d044081274102c904c681c0200c10064a402c040c010a400048151419801d06005500294440f20000c0c4180b00844011a91148641c80b68043c242191903968600c10825201c92401001c0c1d8800c640e030055164072001c0c00205584100c000c000381070b815a0103007404808140340400c26 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 756323714 1250 756322464 756322471
    0x8120402031006060f0e0f03060a0c180f170304030309031101050403062d090b0619210506060f010527060f0d0c030b0d060b0a2301020c0a050a0e 64
    0x948502c0e528105040700354442c02001e407800d43c44540c0d001c0c0c44500010003207800605a907006207000c0820629a4a0000c0d1b040d802141500000c204000c104104a42803000c01140d550b0880301d8050008001c201c4044610a89441e02030b8680c480404015165503481035100040001d071091100b0004030b480007015941c0304a051420603d043e60300d40716101500ca040d06442096541518548580d5800c4c504101d500c00c0408002c3c04440c81545a0400d008401080b9074010700403001c050303400d01c1d4510400707005480701d1003090400080b04401c8001e41d44103170404a40324411240420803600c0c0603051005d0101c016900e0354034003c0420a204281214040706188080d40c5200c1d04c00607a0310a8050302d0300744000b01e03800f44c94007501881c003810f5403c080101403d06181001c41205134072032403075105059802581c0030030032034410001300d16031040c90762201c1103696102000040921118843c801034441c01d90807209100c8024003082000d101a02c1072640c03040300b0420420074801d4600600780d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 756324964 1250 756323714 756323719
    0x4060b030f072703050c09010519093204030e06091c03030f110a080c040b0412080c031c0c0305060102030307030b030a081204120f09030b0a24090606050708120402 72
    0x41c0f00c3c02c2003e5650b001d21003074000b20340d150050b41030141d960424490403401090301325020b8060b02d62562244160320a03601516031480c2e11005031803040541d4041c04000a0031a818080020654108070380028100799000c030001584104202c9c80f41c5032001c20f0743c03d00440200501c10020b82c0c4080701455590700703d003c030305054558184107141c10341c611441d0105078149140b00c0d900d00d0f03c403d0080003503100238078414440b4000e1100340b203005a080190750130b45490010200c9a025181401e21b0135000e441101042448009101d0040c0c2c001980100d24480c0e03551024004603001d00c00075010384a040f560705006902c01d0000403400c91003034000c00040f58024058420a80b0385446000096201c1503020f100a03401805100030425240040603505599140800405041c0e4400030701e140d206100160214a081002c9130700581554407080008180624100854031300b2542101858161310484003481c1c9000030005003140074004803038410358044419441c040030340c0d022041d0f51101810070b82c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 756326214 1250 756324964 756325007
    0xf030b13050c031f030c0b0705030c1b0a12110f0f0312220e040f030e061603080606070c0b031b0a2d082a0a08010504060b030f07 57
    0x1511a01485050b009100000100740d991800302d4443d0700100c0904400c801050400c402000030844000d1008266040200d01c10399804042c1080351640c01341c82081c070058002c20300130800110800381c0060840c8020341d81c2c1d1000c40d544030a410b40480780e144018104502c11300b11001d291030a01c880c3c0e80741020003001e215203c000341c0c000c00e1900c03101c03008501e151070001504080b804558894a40810040e8410700d60706420803d2450981c8405070009052101c400105010107000d20b1a5040400c0c000d8003407910b030345403901d500002103445031080e00811400d0002ca1002c1c20302c54200c41580d83c11064000c00b4900e400040b602039403002b8000804200121414000071309041c00512030146aa40c882d941800b25180f4603410511820380034420313050034039044840540050105520890490301c90220485074207080c0741100c6510a0440500c0700010395a219a8000c002a81a1401560200080c42c2c0f10f4241c1d200c0741c4030a40714412031840010000e20420b2203072440105d26544c070f40881c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 756327464 1250 756326214 756326239
    0x2030d06030b0402040b0405090d0507050c0d320a0305070206130e0406110306010c030e120319030608030f12150a030f03020636070f0608060901080d0f030b 69
    0x40003203425507001290440003641c00c0c0030962419000300000070b00d00b10307010050b508107045440d60b00c00580d040003050200101d0101d05106040c04808000c6001401501180e40145080311280c40c0807a1501100d0861485005994040c00c1c944030700301d02c41d6002018500d41c113850558041d04080740c00c0364441c40400c40804141c038017a4607440141600f041c8001076003814900901640c0501c5a15080d4400510070800c0c1030fa4071211103001207400d42003d02c080400c0f0004208550300e0301501442c03601c8002004854a90040900c0c0d00d4402c141d90b00f000400e4950030400c7e141c0c40b07034134511601c3d4003052141c42e040100319401140c00c0f841a6103915260342d480c80c00b080c0d051030654410790360f00700402041418581c042c130801e5403000e0051f020310381113007000f170340e00d609042e0301030841ca20303141c1e0202d42030b172221810407440340644125190a502035650313080042081008903025809130001900019188800003003100480103030780c9545044c0086c01d00300310010481e0400e41a80312002051b103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 756328714 1250 756327464 756327487
    0x616050d02070314031e07141c030c0809030a21050c0d0c020d0801090b030c13090618050a0803060406031b030506150a0b0a03090c090c0f03021206040902010203 71
    0x84211180240c1c01401c0082e1035401c2051950054000c003612940080140f681840d000003141040041d2640d00c26840c0c0032241420300f5145c0d1542c0c1c0120003803164414510f2180d03014621015108403941d418015911803a0007140c001d10240d034802c800354000d10900011034024204c0980d01c0310440e01001c2d0300305011269006aa0301035416107440040010000a01d001c0b078040e00601a01078002001900c1c030080b03009010741c070144695109039a4640c0201610703039050000d103550303c0d4000c6c036042031100d4076445480180701700710084840c103103023031074404241505001e8072005030b41143c0646525030241d00c0c0c581032503000908056001d81d50301c5002c000203454a403144800e524a81040102900707501d4003528051002d0b09198110a005049034129610101030754250740108680359118440e00380140d01415280400402d40303040441c0120310710701240d10558503043c4c19520002c4030485004187d04030b1141c419110344802c1701400040b91401c1907000500041d1040c81281d1400070035500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 756329964 1250 756328714 756328723
    0x3091b0617040206091e030d0f020d210212180f0607080403200f0606042f04030206030c1917070c0c030204020d14091203040b04030504030501150918020a05061605 72
    0x850a0000080b41032248480c2420030201030800840c1c18014125005131102954910f5850781c5003081002401401b0cc070301d9100184a40002d401c1c100c1035450f11003500d2040d08020045036484000d8034180e0600380c0940000841610000c0413401520b002d840303c0d0000c0342d800030014019400d0040c100859001c40d0660950290341290f150090010501e400d81c50b80e040c1680549081e01c100c0c181003c0078001248207007910074060008030341c40450046541d00381e1440c042e59001a601020101c200203810360904001d12010f111608024104904c0402c2944c4081085041280005003900010000c1c0d000300c2c00140d0881c0102c40c55002c0300d03502e5001600741d07484078200d91031ba5915214542c0c000c0070101c0d240764004808101038040c044040744030035600c0c040180702400c0200180b02040a05008030101c5010b142c01c80d00174400e02c0400c0c42400c0000c065440b510102d24070709691045080c175158500c1728101c0d8020103141c407151a21040180320b030000000072900301240081c09001400c10403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 756331214 1250 756329964 756329989
    0x9060301060804060e011e0905010f230106080403090b0a120f020417070e0a05070507050712020a1d1b13080610080a0b0705070809040c03091b061704020609 69
    0x742c40407064a49441d14900f034910410401c059a03050071018403510308080c041c600050000003001a808040e410300702d001d030456007914121036140c080185060413116161100000d00a003841c026a6030366082210840c030102c0b000783c00100c2c403007401c2c030025514030002c150713110141c0340000d01c041e05680d561080b100c02280d55815198001400c100001070358035807500a40320080502181d625141802140c240b004044545141c1c0d22400500e285010314250f443c0145c00034103da01c1103856a14035000d42001070f100b40c1c4580c140c001d0000f550801103a25482103190b480100c01552600040400308480ca903071202100e80040c400910030001403021680101680d10083c111400c0c41d038007a12911a454000b02c0e03442c0c101c040410045002101c085400c20094600036035611583d0800b951035000c0d101c2c950b5440b40c02c0c460100d01d15a8541c20003a616800383d020b01440c20b600680050050401748102e0012079010301c1d02d075515a2082080b0707613015000ae42018500260600010090450389 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 756332464 1250 756331214 756331217
    0x4051507020c0d03030f020d0e430b1209070b040503031804060504020d020306090105011106011401140a0f0e010e0a12060e030f180f18040f080406030f0e01020a050f0f0906030106 79
    0x800f111146003404228640c078200c1c0c2c642b40b0104080c0c1400135902c0c02445c00d0520071540c0b40c16170241000141d0b00f080b800050413021141621240340061003c0c03c03a80640700352105204196000c5803007500c40084038200c1300020003c1d8a4074100d91200e1f8400403414124651080c1d40e4040000c246c1c445000a00103c80d20041c01a030300c0c038051041115407030713040c0c00c01c40c100304100144442100d40050054107589440c0c0a015455003503500481e101c1a0359070106e1240740b0086004850182c110160300c0d01c0410b203485000d41e01c0440c0c0011583d440904502c2e03580896039040c100084490340300400c1c0301e18062180071502080c0164000d00c0c0d98412000d04055150008c0c00b41044000c041240003000400c035040f41d8040750400000d1071403400100c01c28030b00905000843c00300034002c02d40c01e0140b540a011951a40e40c0c69001070003e00c00e26580c0315600d801c100110802c040c043c4201d0700e482c002510350b5828481244a5505c0b15000708000f29961030040064807425175a81d40698000c4c81c0383e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 756333714 1250 756332464 756332471
    0x608250509130c0c080c0703081603030b19090b01050d0e0601030201090e01051f020a02090403020610091130010e060a0803091f09030b0f04051507020c0d03030f020d 73
    0x80341d00380024080754011085240e0314024910515580c0188241d00058005403181c1d12941c43c041c115091250540c002000310301d00103184e50200c0b140c2540c101003603000c5d440c20005015900188525140f040ca0b9403000315140384024055125180e2144c488250189022402c01c003070012200d0132104400150010755018400400442da803241c602d102030050021030342140d52500780880d8440010700991068007030110b80340325405100300f180701141d0340c00504944983c241814040d407100b809884020624004100206000b03205004802820350540041e40c07501c4201070000745019619990031150b03100c1d540035103140303140700d0003a1340c040c0030003d108013003d05103801040072920301c0d980103100c01c1d002801040025902c24070310340c3d6240e0000d0713610000c2c07041a0794112008142030b000100100308080500c10522540398070a4840d0384500c0c01c0b1050380800002400003900e089840c10010303804030140d04000d0515000d0340d01124464180400c0243c03551030014103a821040c92003040310307139 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 756334964 1250 756333714 756333727
    0xd12030c1b1b0501020d020a0f020103140a0c020714060301170304030b04061b140a031a12010203090105070915050c01021b010b0109050406051003020c0c0a0315050109060f06082505 80
    0x40e006640c0b00900c402d00062521208040c0302039201c1104000c0505010a2044c7c0c50095900a40128450a4880c1b858151520b800403d50380100720068070300c00188200000405e5230126140300c0b00040e680100143d0441c0e18160142d220b2505222100c1c4450009001c0040003840c5030314801c0c052481010301066007000031001c010f015102105040820520820003101c21401c1030440d9006445850080703036004640070000101e40302040703040c2e0000d2080c01c40141c60790040d0301560207986000d000f0f0045032104601240c000c0c2080c050405804410091031001500481c0105258940c00002608180f6000884822030045002000580c1d442e01010422507a01c650200e001d00402c840402000e0b040801084011800c8030f800b5017410360000b0f030346815041c20004003648200060507400c041380c47c0e1500006040c038018a0107500e41c20040041000500741c0070700c0c819140b0822400880d6841d24904455103240034000130000680ca06500b002c040450925039000f61941d2034942c4d0310710 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 756336214 1250 756334964 756335003
    0x50618120319050405133314060403020a05120a230d0c11040207050705060d1d0703050616050d0c110d03021201061110020a080f060d12030c1b 63
    0x202c04030840d0100b00302000180010307920005400882140c6050006118003d0046422180428451a092800700640003103003030114002ca141624220140b05a01c105c010050060364020303800000c0d03104840210610090a00c07280c00991a4030301c44c102e0303c0300c042e00d449900900c208070b101e08800601030703501801d0700c500800c15001410304030720380800c0000450304c13014100070207050054821a000200f02c02800006c0000303a026046c024005651900e088a0280040c56090320054442d280001b20400d945004a425003c40e030300700c80a040280d41d14503542283c1c1c2d80c48441041446014804106003140902c254000145c2e41c2d1542e142040c070100d8124509116400e1441c10940100000703101603100040150465500f401d213001a104001c9100c0c0c01c10820301c21540e0045d1001c6031080c10701d0b034070800590040589031401d5179140c03034000c00c3c08003460a0110242001c601003000da40c249200e41d0113190052074034a0a00440e0400f80d00038070420503910310039078041030410008000b20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 756337464 1250 756336214 756336247
    0x5130806010f0602160302090712111b0a050a06050a110c0705012a15060305062415070201080606040503030705060402040b040e060a02031f03080a030e160506181203 73
    0x5003d107000500719141c0d800c0b00f000400c4040d0000038001c00000c4041445a805403d940080000c149028031071007842c3d030003800b280e412903160b10001d851540c071190109400420740c84200303500840a0b1030304031566101c21010305000790110f051242d480403c0d81a498480c40501140c07a100c4015040c1e091410000502141c3e8141500100c0039404c104140c401391000030a442040d88807800f0348210610b0308011008202d5644003401d1401001c003001410445409074960226121002c903840508000c1801001340e46800c2d00e140d22441007000401540c090a4034652210b4000c008500d080c0c1c60320007003821900540340c00ca03004c0d0700580501046180600800c143e4020641e403c0203859a06114260755200c00340030141d0b01039002001c40d01d990040c1005014030000c1064540101c2e50307a14283c1c0041d806202000c0020340b51284092619802050f850002448844900d0000e0700303041c10824039a00120048018005201c508000c0761141007a00e041c981d00d0401454075800604a9070101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 756338714 1250 756337464 756337469
    0x103060b0301050609010c140f0d0210060f060503130507090f0513080f1c1802090709060504060e1c080720010228020d05100e0307021f05130806010f 66
    0x5508107000602160725002d09480c0303550000d1901205410a41c00c00d10030301d1422242103142070160950000c0164030000d80f008600d4459800c8600700c0c080751300041304a41c0640680b009020214400300580c40c441c0307024540000b0340013902c01024a2507a03c8900d01800d5501001c54207072107180501d142c80041c843c1682c4400e901c07404009001403940c0d80d07481881001c003501c0e040e0001045031400b15010489402182d15546000c00100002040f400e41c1524000d004a100d5600440020364261040800d01c0844a50b0b071a00350034207003460403e4034100e5102a000e9082141e2003841140c2e0014502c400c0181c501038002507603079901303604121402c07070a12907025401e111b0304500c3c40302507640002c0304030410f280000c0d2501071044280c0700303104030b54a07114060f5200b41e080946500307001010601b0540c088021030304001202c04100f007981c803800f070400081d6200307091a1005003c0702060900610381900c6143c000e28007045808070b21f0940b1596007003c80240c5c01680140242e00d40001e82202 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 756339964 1250 756338714 756338729
    0x215180d02120a1401230f1305150402090a0b090c090d20030c030d0f050304060e010c080619030f080f1b01140109052503020f120a0b012c060d140402010306 69
    0x2c14a0300300761209003010181550b07ca10740c90301700240d5508036940c18400c42d56481419224083d55400000307071240c0c02542d041e44038000030340c040f4520407402d04c82c1c45900c14000d0900840c1d956850301144d500d400c4925000c1d0840c105092030000a0f8400402e4501030301c00c110706c0c54001040c0c1c81494070f01007c00c4546402135112104603840e5a0700070304904030303c2e0443d14250365a540d45281c090081c101d2905424015030800388401e841540005409104800568080106843c111404100d00c0d0300c034030001e001640c0040300000401c0000e00100021100c26452624101d030440080300c003015003101407030050750748480da2005074084800300d500421500700d040c4840d051041d2113900e804140c5c1d01101d100d807001842456030034001d405480b600900461384a80703803404507000341c01e000012950701d4002d9241602d5900c00303600450001e28070080900030f00c031211407505940c0090b200742d103075103030381c000c0e01030107000210140c0780603002d106464081400a00d05188c8009020b84201d90003045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 756341214 1250 756339964 756340001
    0x11404060b0f071e120806060a051b031e07140102040515180405070914100507032006070302280e0d0809060f070215180d02120a1401 59
    0x425204001c010401032a51481c80c0e15003085940c407841c4100c08204c511031114424080319101c044501042601c4e00710961707480c0c60030000540700e050600d10100300305200000350f031002401c820701e1640c840c80880c2d04c4c00f140001071070000c04d01600e11081c081c00014040303081284600242c0841c1110390001e42c1130504003000510144043c203240980000007080640c0c1d00402d084502c1d11554019000b0041410f10041c01409200307036015900d07400701c0340f805040650501c51215000d00409030f80b05414140940c0c1c00315120401e8000c480701980c040c0d4aa950031403001d011607800350100d5200145d6a490441c0d075030725404e01e266070315024420304242c0400c105410842d003200144044803c85c61224040c50040d44034060041856009034001c100d008082c1107013002401d5941c003c49540b115a00740089200c079510910410b00c003400f001c00d050441d207003841c141588405100a00c0804650000740c445480c0c219801c00a68140c00c0071950f000c40100c01307101d43d007492503283e42c004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 756342464 1250 756341214 756341219
    0x209010206010e040303140901020c1b0907030209030a06020307020d080105040e251e060201060b130510110a0605040308130c0b03221b14030c130b10030501140406 72
    0x41d40301c220500c5056442c80c004800501098030983c0405030440d001c3e07206542074140625283e00075040102a15183e224030300140584802c00d600d641c10850005014104035540c00718114041d41020103100d81510400403607000003441c5001551082488d0750040640e0071802038020603105040c0d01c01d501039072406845c002422342c086500c0c0d8080c151115203da02c102420301c1d549000c1d0072540102c1c091040074015580030b08480e034200b401c0700d0f0303103a00a10409031650700080c1d2901c203c2090082704080d070329040140d0300b040720400020901d1810585140900307110314600b0240c10305c2c001c4455943e50350030001016040501785400030841b0940c145605041d41d6482c80300301103802052048080800010406903085070200f85c280582c0550302c00c01e1869103010040070800105284444a80e420b021503400c020049008000350014001c01450381110705120205005020000200351030b40ca0f058101d4030340c01c43c803440300030840c1d8000809600d0154480c1c0304003650b450f024480c0d0708043c000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 756343714 1250 756342464 756342467
    0x61103010b070215030f040210050c0d17090105100311010e06300112081b03070c030311010209150a0e21100504050606100509150301091506020319030f060801020a12020901 76
    0xa900560548540380900c807010310136500c601030400342c071905105001d0780cd4003c0340d02c00e03413000d142403860103c400300b0307110041802d00786c54007146d2807113503031106400800c0480d0100c208608484418100228107214440c046400343e4402c800010b007246c90a0006094008420308501c1c0d80c2840e4150f80d034843d41890100c0f89030580580d8082c3c41c10ba80030680c00305900c2d50341c410108410030300086a580c2c8503130345081c19000d206440203402055564640d0001807006001f15503c600c1d00500c0f080b0200e11805030249180c00000d9441c040211412022606485a012460600240202420001e031014a0a51034003100c1ca407503160742404c00040c08000b89001464a400003801c450107201c1281a088c00c81d15030181c03c2445501404803500010050304080045050300e5000ba0306001a450000380e9100c41c4056204603c01a0f20030008a0a000c00d1007010440d034010a00d0003007800040c048004c415101c46822480c460307503000694070320990300314090300d4824141c40350650814500e00700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 756344964 1250 756343714 756343741
    0x100b0f03271b03101a03070806040809041d0714121612080705060c0d0513020d060203100f0e0105240306131b0906020d1812061103010b07021503 64
    0x4070060b002d12100080300381d50340921070a0240d2205100030054182c40e03203240c08064203070a0074503000c2c1c0030342c4d5000b04080f940459101d00c1150822401071070441c04c1028040203040744d02d40b00245400340e508000100c00c090013000010240000d059101103602c03802c1022900500d450400b00c2d40c050ba03a61240b02d10500784240c1214104680700e0403400950801607079521600b44010000d00800d010802440d0014028180200c10304000300002d60303030b11031081005160614007a500c11030080c3d189000984a400035070b0700c1140b94211500c583d99455400001c2805904010344204a100060040381080302c0401d6000e10b1796520b07441007410300c0000103030a120150a00d0b00a0700c40740100031581c1c011360040781a501141c00361a00840c40c1c59001032103000d0b107014450040c040c0000b112482481061031800c0400c00c041102c08440c41d00000079400c050070142190704c43c2c0c40d48070203034010346001c001d14004c00401c000581e80380301034070400c54010b216003a9218400024401d000c00c80c810302c0c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 756346214 1250 756344964 756344983
    0xf05101a0121140709180b01170603120c011a01050f0717070f0501020918160810080d0f141303110a0302090c040305010f0504050a0b100b0f0327 64
    0x400e10800d4110342c000729000780040d02c0f10b03112842d903030b04188491164480218030888041d40c04030100030004852400030341d084044054005003800fa0300d1086101010a102d8001c0001011602c030701241e018030080503003090b50100106d95444114010001c0e4800662008503000d19241c1d1410500c01008109400381490103030052004201c45420310001c4421a030900d5000580703d009050716182c86070207907000d010300c6030041c000340103400c10362816001079a0040e408100302d01c035400130451086690070002806902c0c0c08041f2030300050001d9003030084100062495032544000c10a021021b080d420034103052030807040c0204242d00c540c1c0c522007810340c2940d50001d085c1503864220030000c0d410389110340019521051050074401380c0c20f44e400051084911840003800401100b9500781e00310390301110003600700d80026000500141000020fa40d10203980c480040b540c83d201c45040c1f840c0d800c910b848201240c000000e01002c07403035010071442c841441c030032075000c2e590300c400c40f1984606030034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 756347464 1250 756346214 756346247
    0x1090e0a080a020f030301180f0507090b0703090b070c0614040f032307080309010906081b0f0d0504050717210309100e0c09090708060718030f05101a01 67
    0x2c544201c2041c0300b4001d0140480119046940b6541c4841d001c4180b41d91b4800034000e000d03c1c01e400b05910710181d0045c503100b50865102c50503000c0c0380c0144c40802e40e0026400300d0810030000b00101d61421040050208a0b0258420038482418088003a1410950b40110030300350f50140310809c491145888050196a0300101e00c02c1d54002c900300128003003069264000103805040404150b80800001502074040709a9417041c05a9641100399001d507002d580c0708400c1410000748210340200c08000788010760070703400b1091030010801040e03411160300b51003c50f280c4c0c0000c032080044040010b03012190003913580250100c0340079400d040b00c0303900080c640740b60903010200010704810014031503c00005041340c0c0034000e014501c40c03d141c03514041040d191140a11030f01107400c0da0300000c0c6410648080340c004240302c3d01c94400c1502d0400450f04078801369a500f100100000384150b070b0300589144503000070a01a906152610155074a1091102086104590300609682d1008107803210000d607 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 756348714 1250 756347464 756347467
    0x60317030f01080a052a0612071e0c0807032303070207300c0902040f0f1d0c07110d0f03020c0616080309012d0e0d0806120106240801090e0a08 63
    0xa500c0c0070b86000d26600383c8107074024000708441c1d180230801082188035407125902d4400341e19032403045020222180060782c0019501e41807003800100d4420041600038040d0420556101c41100c8840d821036244440d81424030000c01803140003a0100988800b90105a19410606d021480a6050b00902100c406040400d60a002c81442656034191000e003070303d80c2c010f5644689880140112940611034456181b60071140004d8030001140a08800907100c1607540b00d80c0c451050314030190700002d106407450340c40b1001c1c035042d0790f841d68a141c170742a20510701000b145426003000307400c2100b807001e02c5001d4042044803403900d189000803103903900c1d8861200e40c0c9030740b80c0d100700900510b20381d0066200600303c1c682070200c0354440c0c140d10002010b0041c0c103001080c180400035442c0d070740701d00d1401c01058618010810034030f03296449483d405110030000412131307602c0c103202c60000303440c4000d0000c80c804004107110143d4003040541c090008450207000100c41400481e507640102e01002e00031900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 756349964 1250 756348714 756348763
    0x111070213110c01091a070203040611010b13050f0f0103050705041a120c13060b0a03050c0705070f0609051f0f09031407050901090c091404060317030f01080a05 71
    0x81c590009200891154085444522040c1514000c0c032070320b10103440d02c0b1410a46000c1c0644411321151240800764080d606140c900360041d80c6543d4104503644c840e5480307500404844d2a45014a5940b242043c0081242e0502c001e40c0081100d02901084260000c4001840442e80004896045900503200010a0b03c2c0e0004c42c6a2a03000306079400340d20030301000382c0490b180c6c000035550442420403030310760300f003040b240711031004851040c070490b01c0b01142130040303200060007075220a502809c201d0046203003006a955140c01c01c003680e0004800700c5c105a1051010540c0031403030b83e001c3c0600b5202c58650b10452054107110714800e4059404005c40401804c2010b80b00c1c1118400842d031007808500c00540c0049056102c0c0100d000b100d01480c004400045c41114602481c0040401034032600d0083c0d080001900001004003040f9400580307844c80000095100c0351045007401ea1821050307107904110031485480354060707101420310741c005040700700440c80104021500b8020760308104203000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 756351214 1250 756349964 756349999
    0xe03120c030f0f0a17090c0f0a1d10051008040204090c030c0e094b0f0c04180203032b1d0705010305010f0b030901060801020705031b01110702 63
    0x1c2003280b0040040c401080721142020107001600100f401612524002d04842c001510f0380314086444034082d40c01390742d003003425060290300018510b0001d843c030807940351541060030a440c900d0043c080e4141207003040200500105070550b010300070403511040c140d111403100800300c810191010748120340c0d4550300f10404c8100c040c41030043d940444910b81c0e140c3d80356040c0d040301c0400c43d185034681c0600148810a58919007840c4020242c124940546144810b5101104480840c00800040500307101c0e203891401005002c80d00c04003d40100f1180400700d0501042c0c40c1c0c005001420300c40740004400051340c0200959012640f076072419024500580c0c00c41400c0040c0841900245184c0b0912264141510b014078800070000c6003202c5602d80d9813401142110b0003407080c04034204220303206000714500703e4000d5401402c00e00c00403951a480d00440c031300320f90081808071843d0748009845c034039072a4515401d00310010120002c00c90210616010006803044180003403154000008505504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 756352464 1250 756351214 756351217
    0xf070f050d24150314060a03201e0f120712061b0306062303270706080417030108061618030b1e010810021303120f030c0e03120c03 58
    0x4540c00c07100c55003965251194510b8840003a07103940081d060403003014141707204078109800f8000c050001c480f410301d0b40e1103404da010f00c103902e90082d0070b1050481044036600c2905503041c0c4520a050741000c01049410041c2c403500c032601d640d0143e58110f05800c50300e000400e0301d0086a21031103580302c0b5800c2034980a070007001614540708415034941c89030007406d54903901072825125a03440346082003100f400c00704052410685c40202c0701d00100300040010107240c42c007400c02e030304402003441c00525504089013010115001080055400003c00c82803004200c050b0701501e000212031403842d4180480b5680750480106904088000b10b088000c42a10a40100c00e061a10034565140d081c1c40e80762200c0009019202404900700c0304100c180d032580d008020324102c41c0e40d8030040405441e40328256002c0c0d00403051180000c082c464001011440082e0425008283c0741e60700c000d80602c500000d030490b206004602c1c01c12207845900b1815032000180e20706c0c0c6414140146032242c103481c86103440c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 756353714 1250 756352464 756352511
    0x7030c02190b0609151020060103050303061903120f11010f050405011a030303041b1503090c0905090c0d0602040b0d0b122a010504120b0f070f050d 65
    0x114000526201c140b0018070356031402541c0032601e5041c6501c4011126148581c0039003500c0c0c1c05041300001d001201d009410790600c0a20f81e02d080200f020001c030a850074054243d1007515160800020000c00c0d00c0c06207082c82480e403500403802d440742e003180c0b241046203844107900d505001102160005035406000c1c0021103502d07140083c003166817400e0841003d00015181120b0943c2403034007041c1d105007a000209800307138001d801542103a036941c0b11410f0781c5100311140c00f101c2c40d00c0300c0301203030300e80c0904010390300703501c040e01c02282036606450320309205d01d00e95110081c210b20b000180800000e020a0714083c2400890340d6022105490404000074030a07a8440c06840c080040d1040b40c0382a5504455a11442110940c82c80610001450b880d414106e65552400c81481c0224682600c0d0381d09942c2042410701d0b040d41801d89a04c403040c40c0340740310681034138541810410000c0b81011b5603080e55000c510751919019001d4602409003460260302058507505880340c00c0b0444402510107400300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 756354964 1250 756353714 756353743
    0x122a030403030b0f1f080c04030f05031b010603080a110f1b1e0108160201060e040b160c0b07110c180712051506030c0d060b090a080c0907030c02 64
    0x6890525240190040c031001c0703407160164407004500040d501d040000c115107401c015860404c13200c0c03520340480c1c1000c401090986c1442091001201091411644203070b0305104800460340d441c020780030306520510607855502141c0c1040c000340005121b580650348540c4090034012110105030000c6401c160b0b02100c0f80300315100d00745415100170000919000f40b00015500c40c65131005001400c1d541c1d103000141280440c17071250119828101006651400714118800060b941d9143c400198650409450a41e014444142400207600d0158404404e000ec2c40c2001040e0f11400d94038292001c2004000000b48000820301300413221040c0b084400005001705440444003485000007941b0405641000010310a00e2103e502122a4030409005840030319030399520b0b90000041010381c0d80014a04180c1c0c0005000c00100040e0314069030024041c10b244a0b9124081034090047c000560340c44110720303030b1001d1a8407495459080e07034a6080040c92801003903641c04840140e10300110203d1140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 756356214 1250 756354964 756354967
    0x3041206090f05100b010e0d0809130c03050601140a02100f02130b0c0d08040c12170d0c02011503150207080903030d0b0a0e010312030b0f0d0302010b15122a 69
    0x10404013203600f4100c01c01c009030400044c22500011194240c04841041d0422501c1d030300c520104103200f014000f1080c005258980c581010003d09040d18010161038011907140c10034800690b070060300180c4640201000c40c1e040000440b030013517813030807940811424183d84600c1c041c4460000e40407100308001e10350000403da170390303010303807103510340c4a03081400c454010030f645440e200344292010760246800c0410b0700005030034a8104502221100c40440313030000c1e8403050070305025403040540b800740c49403400056200039030180642900c00c0001e04102d003500402003400011980000308203030056000300143c2794415460040001e2042030b0409034144808900b402d600e5030581c1000042900a0302e8510710103642d0100c80b12400b0f002e000c000c241040b9502130641e101d120798441681014010480b055000c2c902012a000c000d400609800603511040590010309001060003d440200b00d08141f400b022a500003040c41d8028111209031024a00003084429074041c00074000c0c003410500d107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 756357464 1250 756356214 756356243
    0x30610090f030305070c0b0403120f030f052502010b030d0e0307050a0e04110a2403141e060306060a060f05090402031003030f0827120c0d1806020304120609 69
    0x2511030b0700120800c940e1084a1400400e4080100713040c1c1d4112584800c00c2c0341019088400bd407010b40e4030703480c1e240c03c06650300e00001181603a401520b028150f14400000c81c21404400d08074140c40c500080d4066a041a0034800c46840000e6811034100c000d1400386007181180001034180b1360b06034490b1358030503080f0b0b1300441c108503a00742e0540564424100b15007143c0d0302100348180395810348a28044c05e9074058110f181c0c0100181d102c40c50a29500e800906156030503039006c280b0009a49204034a009244500c00002241c0b0007903801440440080c06a4503040000500640c1c8030b000f10002c2104010f1000d000c140a24103540603031500402c01d40d241d150148110100656900c400d4001498945820750180e003c3c0c0340c01401401030b8008030311084445103243c0c0814040c6520259148030707801c00c002c4800b10404c00703032280f44101005040080e5648500805204003262240c620001f051420451180c0010888049900d51070080032010740e0b50a01c000105040038018018004040c0348 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 756358714 1250 756357464 756357467
    0xa080d0306150801080c060c0c0d08130f18020c10050103080a0f030b010915021212010806061f0e04020904020c0706020129090402031c02150a02030408030610090f0303 74
    0x218151010380442e88014100041c1c100c41541e030a100c0c3e15825000f6140f0310141d0b0070610014010804020308071000c000d005800700e03000a48421044d03070690300200303000c02400354402c00c000c000c0840c404003071010790403e2400f00140306a008030039540c0d030380081e88044060040c841c40d80040002042001250303500c2c01c2c5500f49600c008401d030005525620011036041c024411540a4035040e920105031500b081e002d929641c0b9002060002d620611540711040100c040003004058000c00051030154034002c040d40c64508043c210501c901d0340d541040c2032254502c0091010030a05180802d240d94012002c03a0003441007040c0c81e90003900001c0c070480360b2600040c00c00100c4a05600030003002032507020070001c0d032071440042c42000d200301c003110700320f0b103414178280b0780240c002802c0e00d4526030080d6141c05000c144114500c01b41e001802c1d400404260b005d4102c2e80940c840b0010b44c034502c0d065550001c40d01c030081800d41325102c0d5022018800b8840d2603070102425140c1e400e400303800d450307040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 756359964 1250 756358714 756358721
    0x3090609121c09090507030507021902010207270b0301090203060a05070c02131508061b090f09040b0a050f060d290a0213080d090302060d0b03100c02010b0d120c020a080d03 76
    0x540f466131804e144c00700321a28400c0c0316040c40b42c6c80603405080007868500c1039686c40038145900380d046100c0e0350008074403000118401d40c02c02c42d80b440740301350642002541ca03081e44c1c07913419603500c45d9141c001d6800150703c0118100340e2004090200081c10383da90102a2094031840d0b10180d08245002d0000496809e546c0c03004d0681b80c031144101030003507a03c2405903692801180c200a8800000d10b03880e4a582416001c1c0c00c0c0003000030b00d5039440034030500c046000308200b190181c0312144c618003800030a174924483c10381c20120a0000c1b0099180010120306504140c20707005105400765031088000004140d80d03621004c82820303003a6500c0c1030800780f90021390400144425201a601400120700e00006824003042849855525405185408000300c0e038020021080e0182d4a4a50742807440d0f60900480070070000810340041d8450413000002d003106c01109049002d10b00501291010501d84015180406242d00c6c0206000c0c6040c0f0209220780d82c2c582c800c24061042c110048034143e0942c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 756361214 1250 756359964 756359969
    0xa0507030e12090411040e070e1207030c0e070e210c01081e063c010503060f13090206040e011406070b07080408090904150e03090609121c09 62
    0x158103201e00c0036000078881d01c854510268071100c032020040c0c90f640d03042c540c1240006803c0020720340d0409507214400070042e10304850080c0046c0086e07400302c41901e8280d4441a031070020b0001000954110340c0d54031810641343c0184203e68030304c41c00069001c2c0c894001c1408008018111080031a049050b591424000350501c0308140039806044050b54802c004045c480c244078007540700007503270b400d680600d409806002140c0080111f15180c3d00d00b42100755029441000081c56000442e410320782d002600c5040d4011410407604100f4009030360780303480f20800d4a440803103182d401d5212920b00d01008012141d80207400501c0440c0005c1d00d080480c800d81e040301d4000c980c0c0034404001d0800c2104a20030b40200601d4031100e000401d031150300c01c10001d40d01903c00c0380001e150440b617100180c1c41c0d40b0f08440441d44e120440c081041c482c1024000c2002e4001d00a0085044c030103024005115030241450260040801e505000c056203800c21030032030300703904241881c54068880d1400506801050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 756362464 1250 756361214 756361217
    0xb1c05092103070c0515190b0d020919090528020915030a0804031b23010311073009050901050111150c090a08010603110d060e060a0507 60
    0x900000d01040c0c0104008614a828801d107100e00d490700d44540006400150102007004082c000a10004030b00300441c81c52440c079044284103a140070f8a204c0441016080e602d444182800120702a545640300c004800d140d048603c0942035949000313051a50b040c6108814820f800d101d030750002d00002141140e032441d207900c2a004456003c183e0122480034041000350408040d00009003011100c0b800e450441c20000c1c250364030040e043d240c1100c0c54015400075550700c09290040c8222950700003902000b884520003441c0361018101d00003841120500760b1605040d1108010041c40c400c50303007122440e9a0141c1d21010380080ca2001d02d030034015807600c1420201019100348030a90240304d0142c210f40008000040c01d80c2000011507441c1d600f050021520301c1000c500743c0006044410740d501c02c0c0c0314035003030b903450f030a003102082900669644909000d901d400418408a992100035410300c2c00b0039a95828a8021442d20000410a01039240c03142e002c3c1c1410720075403a1050700446c3c0a130315030303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 756363714 1250 756362464 756362471
    0xd090810050c0301030b04080415110609062505070510051e06030a110d022107270b030312010608060a150806010806040b09100806220f0206040b1c 65
    0x3506108540c41030700c1c075260700b610034401000060342031003405502c140b040c001b080c00c1603500d90b420301090080c1e102c00408202104a80303461150100640c41d80404090014044c606084444d031310b1070b00791451407034408004103020704034807801201101d440c0340d88401282d20089040c1003400c0140790544220111540001c0024004010321070b1107400380303200902401c0401041e56841034410882c0d10300c070b0b40200811803001c015071b5401d85485954032141502d03440151880c4651070408080350000740000c56003c070b18005011b88103410000111044000241d980c02001c00203195015030b1466100c605c2c015000415030b01e0b030001840c0e019110075160303404600c0d1a40441d410300c4010360045000108082c000802c10742c42a11099000b01025100140302188000880e500080441d0030494004900c0f2003000545400c11065a00000c5401c0c2e0107001c03031441c0708101c9282600b0401401ea00700000d451802e541e613044c02c0724000c0c4a40134030155505a00e4694441d000040030089044515 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 756364964 1250 756363714 756363733
    0xf0f181a040801150f06260f090105070c03051e092e0f0203030a0915021b0d02030a08070c0501020409050a05040303110306060403020d0c030b0915011e0e0a0e0d0908 73
    0x30a04130b8141d952240088508904003e070482d0700b800040b40f0310420b407514240b18036a460b442d1040034001c640c0000390356a94a0821201c600f5120007400e842d0400001c22803140c04030360f01c1000c8d109101d10460550030794100c3f00314071a45034000d4aa0b5a9030240d48101036202541030a0130101e03040540e0f403981b09000c52902000c4d07404c00000d50b40403000d6001007000410f180c20036807108940d1403041120b0b000b00030782422003204a801245440907400d00201c401d600598003044240e00451842c0700441c9400c01c2841d000b05814405001007040c010080405420480290103a1b400740c401403104200628084034484007510060300c0030360100e803078100c282d501c2014410403640f143c0c1e405454189001d01d1603082c40815900103406a43c0795041d150040005105082c101c2d0054a5a1000b408030000031803000490034010791004404c6604100014801a40000408100c0e60001800e900035610410804040c06040180010a015081c242850150081102070594001c0000c941c035288 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 756366214 1250 756364964 756364991
    0x60304050109170d0b0607021513091b12021e2821060f050d020d081201030c080c0a06051b06040320060f0406111207030504020f010f0f181a040801 65
    0x10411f00040d4014010031514500e8205590060218592801d014851980e40c1c1e0300c6601180c00381d83c4d0008100e05c440b110134007100c0c1d10099180e1011904107045161404500240d0301c0306401031811620b5040101c1c42c0794541486c03001510504042c180c0f003a44c03a00006030014100403150300050041e182d182d0b100504c0488921410041c0d5180c0259001c010b420903003000004041120101e070700800c04039002c800a22403801800900343d1541350683d241d41945405c01c891040303504442c80c03680c0304000104195030ba03051150111519030504d690b507184540303000e0030000320140080f0341c0751044805000406078460b40d1501c0d2852801084820030081d076a040d900d0705010380701c070b44035034140c0c20208002c44c6460303000c1928150800719a03850301c41e20f184140d02c2c0b840b04072480303004290754800300429800d040d2000d640313508091800700c4508800c010081d02d09400410080100400e034a43c004000345080e20110142280d005035880308480d42080300d1190f8028021240c0e03550920081c1103c2c034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 756367464 1250 756366214 756366217
    0x60f0f0b0a0e09090304030228051906031d010203071d03070f03080a05040e01061d0d0f06090204060801090f05011419022208011d07050f060304050109170d0b06 71
    0x4040e542c0c80b1112445004101c900000640290418001000000300580e14180d802e202c200080b00d030907540300300c00307040720984040743c0e80300a0091110050b041da0f5101410079500c213036140c81c107000403540f28100c260203c04104240e0440c4542c400024048201d800c0344003144c0700d0354070541c3c02500d01000820705440d03111610a103208111000c400784001070100c005001c804189240440c1015504d1242082c0c0c0c603000e900c1f29012541c5d8101c691895004909038181e80c003025906000c00e680d599032451500c407001035015060568861024045541d503410800003010040c00a00c00c580d0740382080d400344940e5090459903036113000070050003100c03551107242c0b141e109030030076034514403180003004069400340c2543c0510b65401e10740f109581d4981c01c25140900741e04000010780015442002c17458400c00d00408026500a40341008980d4401000009000050b2425a100d85481c50402d015000c00e0300300070030000d50740c8004141d1522150240225500d00c2e82c050101c4005e0a0030b11003907 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 756368714 1250 756367464 756367477
    0x106231605100f0b101101020c011506020d0512070f03060305030406180509060a05131b0c02010f1809020d0605100e0a0b1801051b12030117161a0706060f0f0b 70
    0xc03820140b00035a045000d0000e03d006c91407000009482c0c5500400741c2e0742111100c7c600c050500504050600c5090750400980d120b03406641855860405c04a000c10500d41d0010700d0350080100000400c1c1c40d05200303412500c0103640c0300e021aa200e9484082c05003015403c0780720090180c0003481c001070545071828541d07000b400d000e440304180c50700f040207118200c0721001c0312440d00358440b091a0b4440200c00304141413007209a84501494849100041c2100e0020f05100e00300050b0401281400c0c9020107164111401c6890059071a010b10a40a01416144d03020700da11200c540181c094064000c07140d101540011038404803110340ba4804c01d1598000d007548010103454481d0802d071994011030040c40640f01502c0900300090141506503c0e0460080300280030800100040000d030b00450202d15007042105e000d4200140000c40012081b415403140040c2c0107028034003c01110b020000b01c81c82560070032400d00203240ca80d8081ca00501107481840c128600540b00004d04410500a40d140d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 756369964 1250 756368714 756368719
    0x305090d09181805390a17010e070807090c090b030105090c1642091b08070503060112030c020906040f02160b06090106231605100f0b 59
    0xb100480c0b8414000102068038080303151450036143c440109100708030420b1806143e0000c0ca0740d14a662030014a6070452104140070380d41081d281c400d9680e1507000c5c0c24240c2d40b01c004566420390403810001c0c003414280201d01c03168000e204003c035511101050440940c0c2007800103020340c07214050200e5804c1c2d03080c4036041c21441c040c4014809403800c201055007001c1c00103281c5060000c113018020262400d20306c100c0c3c090700100300480c1d001a5020345414601c064503c2200c401e64002e050baa409040144001c44156807500400308100125071504084800d00c50408085034442458130b503120028050301780b181c0714100000500611010400c0c1069030b042d036a1402906141d0700340b01c0e02d40030142010364415100c0050b002c07514403a1024020707c0b441c201c80c4076440186420401d01d0700001801940c0100c00c0d070001071155075008080806103a03001c0c202c80c80d41c84042140f0050b6030040c20f841118440c11403041405000d800270340031601d01c24480e001c101ca080040c01d1002201c0024042c981c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 756371214 1250 756369964 756369989
    0xf1206180106051b070b0a03090303050f240328031d06040605070201140a030f05090606031f090507030c0e06030d021002070c0e16110d0e041a030d0305090d09 70
    0x404c4420400290100000e54404a8165a44039105040c46410603e1007000090f0b442da40103040c554940141030700b040d170220080d240c1c0c0c2080304080080c0c3d548000860400e422100e0041000c0d14200030007030300950b0350004804052282d07240e000841040701015000691114a2200800312007241103009920040005142c10702e890340a440f95085030800342d05000f03100500a25086400c130052003820010394000442540c0091403808880020b802403005510880420105032000590800c01060305200ea17413240d0761181c00c850107000b80d0705009110340143c0b00d0000c1004100704419043c2e806c0800c6408280d40c3d8102419520707a051100c900050b031100c00e15843c0141d85a004004450089a50348e0400da00c0b07003050000d4104c00c0c1e58914000000c681c44d6003125600c100d100e680030241a02528880c82c032420014002c5d0b0004502c203124a42e1020007240c40e04030342110340e2010710050142d650b000f0420350301500130321048420a0303250080c4d490401045108075208410b8074207200c17411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 756372464 1250 756371214 756371227
    0x2010c08070f0c060507020610170d140d02070b19050708180f0109121b0305071101031b110c0f0306160504120c1d1e0406020f120618010605 62
    0xc4070064100380d54001481280d6030f504000c41c4042c028140300344132a07001003032a810952800031a200f0194402e0a0700100b40c100302c440f01c180800c000058040e1850402c0c0c11000c0c44040540a04c00d405030707032301550701c00542401042207141001e8441c01458600c4003030200001c40100070303100110340710400078200e00c3c00201c1c2c80c00c0c8581c0c0012441c144004940c0400ca42110640c04c5a02541007940c0c0c01080c0050402038543c4051810104a4929121841600c050341e010b04140076490004001c00d04200306058681d100354414507406040040c519100705140700060141600782c6102c0c445801241c40824040c107040500480515001e00180003903500e2065540b84078050861b8101048010840020110083e02e076041a07603000e43d4207241518030306040d003141600002079100c5101c0c844002c006000100846644d080c080704411540d0030764551500700000e205049103101e0903e004210136640d003001081d000e1060724152481c554071014002c404c0d000c1c44c0c00344202070000d001005003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 756373714 1250 756372464 756372467
    0x403030219031206080a0209010f270912170a0204050d20030d020f070509130b091608010e010e1605011d04050a0b19060203090103150803160302060702010c0807 71
    0xc0c0c03655019142c5011001803108060f03040d12030591100329070341c1c01800e020041d0700e4407150343c0380100b0300b0030b44d004603c501d400749501c2c407041d0180142038207001042d0340450b845c01681000742d20b26132011407528074042500c405403441540e105500450014200051000c40c0d1900c2250242e03100181030740000031310360f61494602400c600321960b03030005075549010300352402c0082d5429003a054014040810b04000380514240302a4001c904c40c0d00094144044003801001598215401010000d0540d640e11601480c0c541c542003851400440c400d03000801c80303c19480190f08501c3c1c24000d000407202d440d002c0c0e5541c40f803504008205c2c02030640400c025030003004000c03c0352083d400c124458980001c001812118129a90b900742900c5078001d0019107410852051420140100b01c03528030305141c002035580c01104180b606150b521030041c045150160110401400d6000c120303907480140c601d85107024241d50b20302702c0252140c0004200e0f07540c01800f50410b2080d081c0e88000055032003440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 756374964 1250 756373714 756373753
    0x70e0d0b0a0207080c030304050105330411131509080a11091b07050307020f01051306030507030603050f0d0221030c0307030e16050a060c20030106050a06090e010b04030302 76
    0xf000c6980d0801002400c80c2c0c2c6009001840c81f8034001c200024652800c541c00074108481021003440c11650b8090303040c440b1200900200c4014802d50340002e000c4140b090b5190540b1503104134000c03a090700b50000440c8168103ca4200c5c062a0781da500c1c01081d80c603000d0070354910355500f004040c1300070019890300310b041490702941c2c030440f40c2041800240e02d00d904002a0762102c00c05940e103800c0081c0b0641582001d068214890000f860000e2415101860003039001e80d44c1d001e501c04040d111300124002a109401450145800a068400d02c0c4080407449599600030348103000940161103c981e604545a1508142143d5908000745555503402403003c0903400180154103141e91100d004010320360400100c14503c03003c441000c11107060508020301515298480410002d0011a40380051301c0c6200411569101d143c1d01c45200c1a100c00203800350184d500000d801501c24080060f0580c0d1050010b81240c50072848000980d0300d80303a01441911480c0806000b5a10414505020000502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 756376214 1250 756374964 756374977
    0x90d021203130902130609061709210d050a050c040603091a090d1d01020c0913050a0503030f100302010c0206030402011206180b030a0c0e070c061103070e0d0b0a02 72
    0xc080d07034601100040a580e501603542c2101602c02e07030104d030074841540341e5005080503214038201240c005140040042c03109050740d405000741c40350003021940c201000c00c204840000f80d54140c0e00a41001000003840303800462030b03540041c1c00d000201d20608207d00c502e0703000d607401201d214139013420460f01354040c1141010403900750340c1802104841e0356000001c00e01568003400034012040d04004010400900559a203900125612030842c40fa0b8001640c00614030302902d03000e031540d0740c9100040d807a230150400504a40500c4450304100300012009500c2000001d8003420162241709898411055502009000c00d0021140c80c0141c9850b0000d1076010341b05143c480c50350080ca120000642d030640e405000b00c500b00410424686407031b4001c0a1220304103600412242405440700ca07008000c600c42d030455001e080010031640c9204451091000c0d8001900b480158207901c000b2582e42e00496403a030000d5180b6000d00d00b01e1820510141d507590b0000d040b8502903c0c1c0d0b04220000b0362100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 756377464 1250 756376214 756376249
    0xc140a02030c0304060906020606091513060e07020705100c02010f211d010f050f04020906010c08040303020714030d0905040e0f0610060311031e0604020702040e07030c0605090d02 79
    0x1403002c2c041d044400c000030400303492950b603020852031074000c0191501078007407e9039106080d12020465019440c03245640f001d175080f203d10a09242d12041c81300100b0161700286601d10030305003042a02500001c0c4001216030990f00302001c281c0101d82181d148034a48ca000f070002d110103183c075803154820031111521404140d40d0240c51031a04801c1030031601e18403500140c03107400e0301d440c00c1629401e100d10010001461000e01082c0740000d802c0040c00710040c0000d114440b4100030487c141d118041c10f100d040d5000c41040c2c0d07550349a05002e591000584560450518405482080d60801280e1003028007030949407211014101404c00001c0c00d0103a41003d00751041695000d002c900810505020f100b5040f07001050904081c0000c09a90070350072001d0b5800010028401c2d6400341580c01030480c0902000300060307441d4040090301034030446070084d50040c1403009446040c1404a44038040300d21415000013402d0b0395142c103480034014202d40e1907102030350b441040d0140c24020498200e043c01c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 756378714 1250 756377464 756377467
    0x3030c0d0f0942020a0b040501061701090204050a1109151c1a0a050607030c0c051503060f1c02010516050105091f060b160f02030601270c140a0203 65
    0x2e600f009081c030079a5481e03581500c3c074840c15820103102a16811150342c58918003036561500c4419020f9511490f0507001042c091843c40003d0603c0390a51040011f0040003004030052282021000d02801052100703900c69850700d40410005a840c0c41145411550002c07074500740b440721410400f180320b0441040c104030070100301e10140c0c3c441210300c6c000c00007082d482c002203103102080d0113200362810902c220f02540f4102024046581c42209540c402036152410303010b002000c0c50701054060155100c0742d00204081140c40c9000355040203103110741c10030350303804066410080c1009803483c0000205540340200025450140d4401e030010014800701603509a50204c02e50b94942c00c5400445d0f040400b5000100c0800e48408841540c42110b16000340511051342406201102841800c07010a100e00c80a60024104814400c0b01c419458000f01696215a542c1c0c1d031102412004691940d15060f146014078202d007584c1c4141e07241c07a812603645151a205601049190750301c074140e543c056220 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 756379964 1250 756378714 756378719
    0x905070b0f040f0b121603020706061706100308092b060b1f09060516021504170102250c09060803120c0a0c020402090a080a0602070c0503030c0d0f09 66
    0x200c10080000e1022070740c04560380c034500403c10000d01415044101020003c002d0142d02c0d42c0d0090419812080b844485c014209107184160300034400c0c080010b080d0760400500007484402d44132002c02034180d44c4140c5206503500c0d1281303900315405000c020086003086c00144c3c0302d4105441b010b1002d010a01903c0340c552000f94103c261480e4410080340c4694940c500350040341400e84a4080314000811000c1020035544800303008080940642402c0002c040307007000803030340e590030f5a082003a0081c00009400e0701000008446600c00e0003440c0000a0b00354540c20304000520881e48241e40000c40c42520100340b0f01864003000b0b042c1d0003524170b104c10b0b200208a009607440f40c2001019104d00541c0d41c0c0f4410306800180210007401903682030700500c00c03031207400e0704030410546040c0d04450060f6200c02c008005008102c958003d90024410440010300700041070340109104c50181511040c520380c1c94080641d00d12a41c83c42001c160000f41a1455007401448048515506030815100303964 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 756381214 1250 756379964 756379979
    0x1806030a0804090c020f0a03050a08041e0b0106020106060c03020309060f0c060709091a0f011110060e0114030309010543030801050a0605090909030931180204090507 73
    0x104142c0010003040d5960400d0b10703415404006c41e146081030b81d03000d0094901c5503107003c1c0203806070b40b480005100340a070005040140800e0f1480f60032400c6070454202110a0401c80304031482401480c1c0550b2a0400c007180a81c040e8007107503000e561640c011031400c0c41800030300c0003a410241b52140b40c2d1609000c0840403031403d000061003a026692a160060702d00340100080d82c0b84e0740c4240207504008552480b8544076503d0f910313940c140c20700f00621055039120b609403800304841d0694080510b0070b803001c1140e101c2101028100c039203030441090041004000c144d2a841104130407408620100120f40c030000042c5a1004161148460058507045011201000e900c0a926000000844050120805030407603001030242806440318032010b400d10401410398401c110010748100d40581c00900c40040420031540100c03005450913031400c00e03c1c6034880c2001b614918231904000004841100c40d15188100c001c0e2011030322202c1ca0981c40354003800010210724101707590314081e030b0001140300f2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 756382464 1250 756381214 756381217
    0x414060d0908030411010c020603010512100e0a0215033108070b040308130203030301060c020630010e0c0a0f050909040c150507050a08130e0405010f0b0f1806030a08 73
    0xca0042c9249a0307286010318001c20160071100c8518140080810810056261101541d0544005481080c00701e11403010407890400e4000b0080c01c4507003030002241c5681c4000c18000c54061081e0b612842075035201103094510300044445640c814036031003100d01c2031a07a66182c4c25843d00d030400188044142502e03125403581c401c000a035a02c0e9642001c0c041010340c0444042e5204c41e041001e0108184142e0003c1d84922062180c041040040c80700c560035542d4410845040c58000c0352070208101c9101c0e40100340d40e032800b00c0c085200661000000360040d134021918802e4480d007480b5860011804d5040d20107000d003180810801005000326121620f0b29144075015900a03c40001d110b49020701140c080c000f080b0502e0b04000041c400080003d10000300881215404505103031203090300d50314045400c1c402d500415440410f441400107102040d406580d40f0520039205012012034003044c040004e018404241c0c2040c90ba08082d011215045840d540140e07000707068a101a40e1500c0c0c1c00301c0d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 756383714 1250 756382464 756382481
    0x201090807141f0206042402070b0a110406020a031b0503181c0309031e0b01120c090b060702120102090a061808011808030a0f0f020306240414060d 65
    0x2054a000c45615454405151640c2009500200d2102c180f1032000944841d0b0181c002018174941c54103118040c070103803610b60b00076288002c00310b46511075410081c0c0d1035001a41d010310854501407905501c10074080850b030540b5050340092550a03400ea03803c903a40d0850112040c2d4060b0b0340521640000c0e0309000402e05e00700ea55601134082d203a81c4042002421000c84072840024680040c080040d81107041c1200701c5c0d4105140c0240e685840280024000c881000188203005007000446d160f41c1d6510305c00c5d040d502815048440340d40300c80c22101140c201540c0070764021410b1100c0001441d000060403824144c2200141c00c00c0018030108001694980054002c558409141101903040809650042c15440002d114007072066400270300000544101a000b03c00c00800210551582e400c01030380c24034040750402450004000c020000e41040c0c401510480c001c0709460160040742c0400a1325803c80a0003500d000d18042e002d5030380e40798000f00030f900316800348000d01629449100b00d008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 756384964 1250 756383714 756383729
    0x6090302010e100e2a09042303130302060a27030308100f03020607050102091003020301140117070f03090510020309070b0f0a0804020310110c011107120c0201090807 73
    0x80070481400100d0800b09001103a0300a60f2810711013042c8400c00051041020400c08100c40d0f544000714000ea00840c50311002642040d1000309000c10072940801060310200c207943d03422920742669049549900c507281c41201e151200c1401032015190004c020155141c541c2803a0b40401e50382104d82c88040c441541000c1ea0340b501c03c404105054100c242e0b90743c44098000522112405c05800c07418412060001034059103000c180382c42001401d504641c1103110090040a0300728148200802940c0240a0250480b00d242e120311810750081008804c2550b15400344003032030355405402c603114000164050105500d4015801c007140c028080d1156140441c800582c1e07038540103034102c0c50001c190740b0000c5901e00800103a0104061482501d40001d11850a0085516107000092410101202032026680b900c1c4c140e4034445090002070218846601c028418201c10221a80c218051a20082c01808076201a041c641c2d101d4441030310350510504288468640740d204151800d01d40741c01801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 756386214 1250 756384964 756384971
    0xe06040e0a05011b0314040b13060e030304030f03050402010f0302030a1808090f1e04050411130c1805010c080d020f030903130b0309100b0f040c0e1306030206070803060d0609030201 80
    0xc0d40c035800c49111319408100b800c083c4002003414001c4001c04100403c054059007212020070a220f0b00c0c1041c109103150050070600001e140b01c24843d49075030060320100d000ca140c80340340b210b9060203030290610440d016182c2c4900d16050301010350181d0f0008180c088015500d50340d032611080c5141c00b40d0991401000c1c40c40e1140180741c24004c00208982800f4441c12010341c80c44205032580b005480091825a40820146c0702c80c0703041d20700048040300c1c05a01168140125901006a9000321550461540c41c1074a081d14840c04c1c09040401e800b0b4030b400a40c0d4400c10002256003200180fa842d29240001894a4000148070009800659a610f03058100244c81c0d95428241c0d1078100207440741184007032650070510a00c0b5911030b12035900003102c9031201c10710000c550b80c50a100340c009401030310900208115401c028801e594008030584104400d084956110107144103180039282e006e07010502e00b070f0494403403d203160001041281d000c0340e034070040c1002030b8550190801c024413903000070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 756387464 1250 756386214 756386231
    0x4090203060406091401090c0c0b041a150a060311301012060b0a1707231810030c0b12150108070e18010f0509130c0e06040e0a0501 58
    0x10698189074130102d21642010481d81107000c0c4880c0050456409130b4000a2220400405481d5880d20040250807003128504201c1030101d0203004d50f0901916401300407540e0344400c4030b840d030460302030021a00129600b00a0090030301907400740c81030580342c0100030306012914201107510b199500380300c01a6002c00a08001401d117a0750095088003a200d46070380c82038209101703c0101d82440c0310142c091a11609859441e4990a00700000b822100b03001c40c2c1881d03000c80d84c85944017203a104188902803490404d10507010100707212280f004004102c443c103290061824051a0805000010300310404100000041c58038054040148481c2c080143c84018043e4210580c110040415000140c03034114668241c1c1c0c80900305074040403d00345644481c021030046040045411011b85065031008000324503014102c1000086402c111081c44c1c035540c3d040d03030440303a04038440002816091488020700140694200130782d0b00480191000482012020b01c0d280741c41a890b41c281e1f500e0b5554080c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 756388714 1250 756387464 756387469
    0x10507020c0a0b0f0f0f09030a030e030d031407050a140a031d0303040b0406020c01020f130807061b03201c020601050d0c1502030f0408070e060423040501110409020306 74
    0x200401052000d2582d400c201c2d0300c44c01030150348074603840000f20304400604800601e020100b50350401d40080d044410b21811454040e007404801810184079110300b1200c403040d14401e018090700d1402c1000c0b804220346070307a0002d0b50305070411101a424080c40b42d40350b1101c1c249960240c01f80c014251303030109210088600e0442051b001e0080d03003080703800800802c404207002c40401e40d08a613004100582d2101e50660160082c010b5842c86090b00d0741c000b440740c084c00c1000c2c0400081d15080420303240204c1e41d40509441c414168013808005010421604010078043c80d1280b440a100c01220540d01d86c85184807824080402e40c40b0741d2207580e0104221250764100442805030000342c840b994414190785441c0e1080e0f20a00c11428030885004012804d40d100b0720981d049558808025503c0b1b50f10b030724680703440d6031640c02070300391015800000038070a1406020718541929000d003044964604171014103501e0000400c2510159204c80c0d40d0140c480061004000400c0c42000058981c10714004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 756389964 1250 756388714 756388729
    0x40c050a06030e030304030e0a0911120601020607020616170712061401051e2a0c0411120702150a020d0f090308190b060d09060f060e0114060408010507020c 69
    0xc41d40c105031a2142c0d221910500004690b0005e8140c00d00810050301400014206440b030b400c10000c8034284200d95111400c035101038144211410f8a0309001d96484004a0b5a19000c8500d030300142c0c49040881e40440605e0061010001945408142070803c1d41d401c865842d425a14980099071405888448400754820b41015203c410303120940c00d49a540020414000c950030f80103560450341070b1014500c0c02608541c00c400c0007403014908183c1e0004040e0b00c02c0d115261280180c000c1050041103131606205011806a040c030b0203904082e00c0580070015950014400b82c01c0d4420001480c441d0514038444620503030810304c3c0941e5688134107038084103540c0c000d41d55618841c1041c40886c0003e07000381589034400d80b02c45c0c03001584103560784201c000d403c80110352034025000017010b4411210030342041c04000d01601d02440a80e0407140ca00d4100d8180d44154001c00307080a0050010003020b00754941d00500042040d42040e48490207542103030f005407140c03409a0b11000728494a401d02c42e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 756391214 1250 756389964 756389969
    0x4020304140c030a230c030d030603020a0b0307050403081b0f07060e09130305131509060323040204020f0f0310060801080d0207090903031407030506240d05070504030b040c050a 78
    0x4003d13002605136980c40324807004110040c510700c0a00c0e25101d40d00104200614a100e4900904440705d4080c0944094010b03c0340b800168024800c40c40007181070600c2c1000c4038090300e200d90740c182c60b16107161036440107500088041c0d400d07100040c040c40c1544c1c804102c922000c200c80c03005005a01d203403940140400031034000490040d030310901088580211208019115031f050308066988a4a1004030400e040c0c144c0c014605120307212004131f01c0c40d58413400d0071013942c90a46080121079600e09401c01500c281201540300548e84400160040c10b00b40c01070500c841384038841c0e03820420b145c8403154103034000f00c03494012200c41c0e600420095078403519090050400c040605480c201081c0025107a100302c0c018841c0040c2c60f101c1072000c1502c0b03a071080e45051540c841d0b13810542814400180685800d440040c414a0340c040052440740d4040e944081c44032030000f00c00d02d040c00b00e01d8000042c06000f0080030910000303000004c086482c200b4801e100d1840b9050300d1014608100400a0366900c94 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 756392464 1250 756391214 756391219
    0x130801330e0f04060b132403051e070b0c0309150901050a08060f0d03110c060a0906030f020d0507081906060914041b020c040e030c070b070f0204020304140c 69
    0x5101004812404a041c580140007280300c8080e641d0340f410b126004e040403400c41a0022984580403404159030752040b5004030381011a084114216640301140880c10700015000740c11a542124201c001080301011540410007504c1140b9a5022400e03985e410402e03045a00f5000041d044800e8508500d4140401d0710207004030381800d40d2030b00020b081c0d008401000052010b00300c042812590382e0344924212405c000c1c1103003240c2c10186401416905407180c0b085a0f4880c080c0c3d50201444c2074401d80344403100f980c4d24903003e42d161036000c41c00350400da1500000ea0b5420012a503805195000d00c92042545840e2043c079400c0550b40c2036860711682d050071203494074004007070181c0c40d88109080b04440c4a1103c004002e0021400a4000c14021100c240d00e0350400031030208094000c182000d803043e0880f0108a10300344284460b8503032041c0040340300c89800002083c030680d450300c4040c10142c1d004440400d015012030f808502241d200342c8064990b440b41c80d450030f483d40010030034032074882400e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 756393714 1250 756392464 756392561
    0x609020403321605040c0905030619091502030403321c050109241802070c090507020606090108191502090301060e0f010605031308130801 61
    0x215260009000c24100c450001100e2800c05007841d084a0020340303502e210700302c0076140c14070510809021841c000d841018000c0303041000c1c01e00c05900458141040724400741c05030a859a0706003442039880e11040c1c0c000841d40d5034010b881c001c540080a4074903070451003540140d590801742005000c3c143c40c0b9102c07501d400003044001603a1211002e6680e002c84100c028261520300c43c0700300c0069010a0b204c0c01d00058544000098150515003000b0290200c05ea00c10703038246507007803a002c5140001e025032081064804440300c0841d28503130040280300c0c000c20003075010517100c0a001080d18003d903a0079005900c83d5041c40079910f08400c031540104644c000501551001c281a13a640240640010f8030500071018001003009958041741c211480003002005550745078907140b615100281d621403181480000040b8840d030188040306d000d040416015180130a0581d96050145e1091211001c4a00314070b6001075000001d0041e000c0300d09402c01010681542941000c1c0c126240044100f03035100f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 756394964 1250 756393714 756393719
    0x11406090403020a02040b210105060f040212061018030606260d2709061e0509010b030a020409050123010513060503180703031e090b0f0c121b0106090204 68
    0x800003040d10243e035046e100440d1320304142000070003002440c080f40c2e642c3c511f01d01c81c980c00300f101036100350303c151011101c0000b50b10801c0140005c0380641048000140d5800001c0fa8040c40c100084807009001c61030a8240c0b07040d103001d1103292030200e0740222007460312007006001c9010469850078890660720300603080401514600c41d80e42e40c4940814003444143c0d41a600c600480104102000300000b520315030259582c0b20103001000b1620860340d00b081c180301c10501100034444140c0888600803c030914a03400c109850880342c0c4094010384e03000c3d0303081100062820b49405864000c000e07140c2854140c55501d050045000ca240c48843e0402500300600b550044d0401003190940307201d40760240e100c1e0303144003262410100000035428240704030701001040584c028080d041c81c110000424400414481007580c64102d680500c140c20b54040c4140f03103c1c40000b03005052032549880c22038103100e0445410720090f50021b140c48056500702c4090003411602400f440303008001540d001c6103047d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 756396214 1250 756394964 756394967
    0xb070209150f0411040303021216030809192901180b01020102040305011b110c150d090f11181005010c0507080102041202040c02010c0c0b0612030705011406090403 72
    0x110010a2036121950019031012141c5500b1212040c036000940100001e80c64045219a5a007041c403089005215041c4d02c80d01c41050312003a2212000d440ca11201069800d613010b41e08200c0080114000d80303d2071a100501c1d800e500000e9554074005c4a52031400304030b02d07094403d11502c02195000740c0721400010400300000c0881d094480703c0201000035006000300040340648241d60024150390b007001c0c4880101251300c00a80740004254980070070041104044980342d0700c00b21110f0f94401c1410b01c0c0030403192120802054070a441960020700809695210100d50310405401c0d61003481041440c1c5190520405503000694291068807030351600798059130000c0f4960051070f040101c40902c1c1c00400c50704000e42800380110900941d11142c40d01d040c0030780501c0c1090f069100f0342c140380010310359900601c11491000040d6075001c8440400381c0340d4000051000d0320043e0000070707130344d2050304880050025100c01d6100d4000800c1040080c0710510010b0340103042070380f28615180a010029 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 756397464 1250 756396214 756396229
    0xa0c0501030507120f0c27030b090703050304080102040509061503070f17070f121a100903080a0e01021c020a200612160e060d150b0412060c020d0e090c1b06040c0b0702 74
    0x141d910403a1070b01c8a81d224ac6240e4104442588028414440850082000ca2040d0080c000b507460a981c0c40702159100740800c40140400341d0030311304100381000841d062070f01c20450b40e001c001d0306040c40c448404000e003801100c0401210700c000002c9243c0c1c0344020701984410001445180c0100c1807103400c5140001c8010115020a0305108201500e03080020074095040000190303000700280341c6603541400d01401c03c020449006d4014060041c0d806543e03103032040000192945a401044000750a40d030300f49003461840c0800c400310f84441c86007e42503132688014100069031072080502800d0410a41c01c107002540e60550138007900b920301c4075603a260300064480542c0503240100303040345255020415103125400103000da0100044c042054182140c094071080c0c42041e003040803c102c0c180807030b142c611402e94500090307810400514030b49850010183c02816000d010307460240e84006000c40030641a02010305a0807803030400c0240a03032607120b1b40017843c0f080b03071461602e03010382d001a428 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 756398714 1250 756397464 756397469
    0x22106060a08190518070b03010e221709150a080718032001080f07080123031e060f04021309051f061401020a0c0501030507120f0c27 59
    0x40202031400140d40c00d9030a9128140384080744004c011030300300008002c0700e06101c0203503c3c101d48501c820000c7c03044516400c8a040305c021482d520b1b855181c4041c1c0460114891808400a004148042c008a04406080201440740b001100d07900c00021051051711601c0400005413040c09100051a0941141c0150740c05501442d000038007550400884656010a0f0400b51109000e1400c04805079010220503030030301426201c5040c9039882c5003054041d96412109680041c0904004200408003c1c002411151f1044500a0001c4144000c02d1520103941160011000006d814056501c0c050008580001e411454491b4038034158000c50305800344000741010140da515030320700072300a00b48051150344055006010b06071205a11450181c052400303550710741003881c18016195800020080c0000b940072154a100c0b03403030100154020003000f89018180031550408003d00c180501c201004004072100000f010803c0000051141c0c000d040c0c0ba80206e40a552900703001c1e95203992032001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 756399964 1250 756398714 756398717
    0x1a0709060e010516031803050109062a0c03050a0306170a1b0303050301031b05030102180901120c0314011410060201150e0f0c0f07050105040605060907120c021906022106060a 77
    0x43d508040644110b1b44215500240241d482d0900c50810028550880a20043c9114103000000400c25142802c0d504e251040000704141d50f0740c4c8400030b4040c0000d010a00e88500740011550b550380f0841c1c107644001150000c003900804000410020785079540940a2480c803000170701d0380c5c259a0302500f030344410302002c3e040c82c003000e408454030720400344071801030304002d4025901d88404a40000c5200042c0c01258441d0600301e001003008054406046c104640064120700110b140d83c0f41d03001441c0c0804204022035485041c420540500580c0f124011018a400b0200b040d14180c40242115041c6a04110100550600700700c8003546841d00740c2c014030845162251031f282c03c03070780e60824030921071829030b46840403d07070740188001944076a01c42d900840c818082c0d980e44c40d08000b40311108480c0d81021401d0708549191140c4030354003503c4c005900380100c03403520b1482ca140f100c1c043d844500455115030000f500c5a6284a900b1002803001c0c2e00c40002181e07410801c00081c4140502c150000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 756401214 1250 756399964 756399977
    0xb101205120d110c030901120507120e07031a0f0c1810020f0601140a1403030f0d0905060f04050c010309021309020d1a0429010e041a0709060e01051603 67
    0x1e90039031007035110000d40070000004030b60750401400c0b601d8480c1c0203442c0c01e5010071054236950162031660f0007814403503080d0fa0b03900502501020280001040c415103100300758803400340b0200004051280ca4000b101044109102c14901420841c2d840c0c400100308440030f420a000002c030102e0818049412401c08840e0407a1142d00c0c00d4003240b0b07080306103a0b4020f0300c1c89108000034165415255a50070306c201070382d03200601600d44d1401c030714884004031a19015881004960000700c0d03203030003816080035104400f080010131504c1c2c071032a01205982e42c1d4108440e138418002008010480e03010030302403c0c201840f4054007600040c001c0c902d803e0b03481c403a10f5102c10a070021591403120381003030360390304c45003003150f42d0b041c4140309203808000c94003203440e01c44040d10b070510b6040400450854040d0804444000d0f802e00d0462f21510700c01500403200c000020300540c6a24a21a9035940710b0145c55a139080303040d240c80c07001040d041e540b1052905100040155600701c00c0200d41c200c001e00c1c2c0508154 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 756402464 1250 756401214 756401227
    0x8190c05060a050d0f050a0c030e030904110408071d0114010903021221120603031c0b04060306090f0605060105040605030a0c021c020304050f040b2d0d0b10120512 72
    0x3e40e214494410344d070130311030300d4112816400308180e48418040c285d1410f0811603d12000000d504440340724460b00e546600a208219142c0340903084540801d04401c201c50034140e4400e10035250400c26003003c4000610000320f010100280c3c2d00c039900500000c4040c3c0302c107000c00030001c1c006407400c0c0800b078014400191443d00c84e01c0104150703040203a407040e001e06c03950350855041c403040c3c108080d5001803642000c00700d50289000000d40b690055845180c0703d40c080d2014060009028140c040d41e089603e074400080440c1d49403180641860203007041111140c00c40ca4440708503000100040c3c1401000c0c001407100540c48026254048650440040c15005000c800d1b07180c00d007100010084d290140d03491411040c0c2c0400a402203c4045d0307000d08199041800f084140c031682d4140d1a0030070b0f08040222440c031040f20030390f12900c00200240d4081600744000c82c8031100c0004090b2a410550350501100f0380343c102e25540180821580040482c2c403e03500c4507240c01c0354042800155a010909 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 756403714 1250 756402464 756402467
    0x1080f040309080a0f15022502030705042406020f0c0607300908010c1e0c060518150603060402190f060f020d02010b031f0b100201050108190c05060a 66
    0x9000242c03c40000300e0740c04222603d0302c54240310f007400f000c4906041d10b1851305c202e4032080c02078499034960f1f0f0b010800e45840c0c8407801062202c00c001c069a042c80b5205000030350361680d1182000c5800602003000103418030040703540000503280d00c06411580030810361080d5240c0414080a480b20480340c059840855081088a84e05100003103006d618070840d28100c4040f950324505201c10302501c0b0690703c1a5112141c0742201c0f03610000b070003c1840c503d11810300249014004400c1d41e107509101e03822200a85420b0b00704e800c11900b00b880f40d1074101c014141c00b21308004d00c8482e0720300108071000c1032618402007502c5417405032000f805147c001d50070719021402250040041c0c001c40c2d01030408140c4c1c1d007000902110010704607101600030010b40281480c07040c001d0a200c100058004d02402d20240015880d40c40c00640c5000c001d59074100c0c1c2840c0c3c0ea2950152060607000e6030004c0703100c0d41800b280728240307d0742900c250030760b0440741c80600006d4008090380d411140c0899481d6150f6011000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 756404964 1250 756403714 756403727
    0x70806010e1f05090108160206060603091603031115011404020307020a05031810110607140f1309140121060b06070f03020c03010c02190606080a08091e01080f0403 72
    0x103482108602d140a40d0038041da1040c09409614001d0f43c40b4691a2200c1d141d82000107520302d00e010058000c4c00004059040110086822540403401c490789060340e40c01440c18002140c10403800200700100740070440004003d1000500d82402203581c581d40361081040032181e030384000303500664011000514283c02444015405034100b005d50b6030324074030700505607000049a0f1141c5c1c8075074500c920940491748110702032144212588000d1256413940902500c2c407407054004c0e499607140400c9203510616903c400f070103405045d40040e07448241002146c00c01e40d4800d440894140070f010004004100e8448100e20085080b0010359084500d60309000000d40304400c489a007000c07001601c04104280424402e8440b4040c0d0f0030340d2210684c00d000c00d801d03920360340c11200041e8080e00d40f038034584d0f451640e071f120030358451100010301581d82c1d1040b60030079001c1d140640d12000d001c50622000c0c2403d091301107070908009400c2e40141c10740c0c0c00180007440040c1005c10301e10421000074003018005c41e0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 756406214 1250 756404964 756404989
    0x2d03050607110706050313300c051b01020a0303020c0309060f190206070c1112070602070e0108070302060406081503030c0f100e15040c1508070e0108070806010e 71
    0x1095403141d207814040604480101c10207081980301d22040003944d14800d000340e9000e0b900c0c0c9900300d0301c1e201203500c51b0544171200d10705401407210004101240c00d440c9078135081c2c10000c00e40301c40002e80c1c07041c00c026003001049031860346c441184211000d1142c0c2e0101c0c2d01c41240d83e041c180180c8481c24280814075500aa40350260020700c0052091148044c4c2009059001c56101d100e640f0b0250306801280c036201c1c21384441c3302168401d2502000112a511010034102020301449644009162240e01d0400260300110141c3c01c0107200f800700d038034120384407400361005800034548076141d680400c00c2c0c2c2c442e034070440e42000300c0034002c00c03450406e2940b009a200300081c00c0725195842e20303241c00d458112020039500c5622030140303484a03856060140c01d060710a00ca01510132458028810b11f01c0510043c401c603010540b03d40c01060a15100d01d50700440d08040e910b00105182012020701110303044054181800813640c100102c013580070281c241d1144003842c14500348a141408941030b204401d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 756407464 1250 756406214 756406223
    0x4080c070b1801090f0510020a05030f03010302090c1207030506031006030b01060917031614030c0d11030309060a0b0402070b0c120c03010e040b0402011b0c18062d03 73
    0x252000a10300d4061406041c40e000340038190418442c6442c01500c4070f20701ca11801300d1103110703000d041009103000c800c4400c80e80c102c1c1c0165600504d4a5039014215484403605900440c004001401076060100745a13034031826a84500c0c0c90305500c0401801540c0008052800300340d11303030300012950f40f014031800100c203a0046051101c5626072030428a50b0a00740900c0001900f41c5030000750500301d01100003484130403200030b0f62030143d00c486090502001c440342980c4d0070464030800c03103040c1c01c01c2006207203140c0c0800181c07a00d803d48600040c00c82d6003030307002c8003469401801401101840807601c1c942000740c4a000140c0c060800c4003050113806500750191422480342c04129518001000400005091682c1400155500480720285000a0240041d9504130341c0000d00001c03850383c2103a402600504041110708801410440039030183c402c120780903503401808106c0c44034040b9402e0756007030718450148039031070500342c0c2c40032103408042e100d05030fa140d00e1540d0904005858031110245411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 756408714 1250 756407464 756407473
    0x1a04050606191503050103050f0d0509040f0b060d0506040507030b130b2808070510051e0f0a050903010b0406140616140708151e090f011b0206100609030b04080c 71
    0x804013070004c01c030034030050310310f801024403c6078401804160b071010021252503c0e800c1120840511008003005201c100c2d405070380da820110f07955910000b60590441c1010003161500e00300090000341c030780160003402414144440c0c070301c1c10707560f090605216140c0104006a499103040000c1c01c1d55086607030b032003c2d00712603414413107243d108080d981c03081c0d4401108440311650380300e09000c1e00844c0300c1001e100050050005c07021940301d654040712840c4681c0c14027410490210102038031b0350300c22403218010450008242c1c8103810280101518840b00700d0341040500c0c50048841520101681581e10510000681300e2080251044e400c4484d60410a400d46040c84c4c0c0f4941039035107840d801030a01610801e81e044c144001700100c01072090a12140e07020026041300f9845c01e070018054000d030018002c20513001ea030b0020900c1400e40c0c0c488540d10080201802520103814400d01901c400c8c0980f0000000f03002c03154010096408403548500060301b996943d0802804a006680310071046004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 756409964 1250 756408714 756408749
    0x302150a0e15040501020714030d05030a2901081b0d0902010c0503030a0b0901081f020304030314040b0106110c030a020d02011101050717090d0c020609010201180804031a0405060619 80
    0x100030b000381c4155402078003103c844580743c000c444092450703100c045d0341c103074421100c8440d00c6114001943d000303042448007080130031071b407100401c446241c0e2543e14090240782861230007031b41c0d01600b40c0381c1002c4200c0300b05220550203085c035800ea1054891040707566803280c0d000000c40e4854482081c1d401d402c8000e8903100e0403d520300304007821102101c0f41c03007000b00000200b80302c003010944036810140341400b101c0c03920410340d203440a5000108280c060503600c0707404145440d4000c4405100320710600000c1d489604086010709140b8440c101c1c000300394060081c005c099200086d00ea94116012a00500e16032880c5c40100c1c1d03041941c07164410ba80d400c1009100440350000c14000d031081c039012400c12155140c4481d10341d2119840071100004480000d4407002d4100b900040c11706480610010960024141c08180d00400080301150310300c0d4000741c00c0060019190b0210289407007080410101d0404e5207510340e88a0000d8400c1c2d114400b00441c50a94440a8201900910000c0011062501c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 756411214 1250 756409964 756409999
    0xf09040807020307052d011103070606080f010905070920190206070e010e0108040204241d0c0a050906040518040b070e030312040614090a03180302150a0e 68
    0x10001c440c01c038001e10409501107000c0c07404192000c035280009107507280600d84d07413090b1540c148020001d00d040c89214400079800c94000d1004000845c0038a401085440c94000c00b0f524002d0340300340d5924680d1406402900254001c03400004540c3d1050b4045001d0920210b20058040500d00700c841e150400200040d500c03260f5003035042c080c0c009400351612682d40410640380390700c3e6680b031540002e000300c0000e00150b0003114429001030010304002890310b4086499401c050304d114400b10050010741080010119007840301c2c0c942d82500d525001346042c41c2040d60b0050042c03185070f20030310001042c20159500d40c401924001d000c02041c1d60308664070a66464402c041c1903409507241000180081e00180c001c100c59942c091018004518043c01d8103211107071008042c00c1180c0b80c44e1950184549000d40f007078010b003ea010900680b218201c01d14010742511100c4075070074144c1c0c0703001404001613500e09801000840342d08a1496890076568012507900b120040d5607030f480690714502d02902c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 756412464 1250 756411214 756411217
    0x611010209041d010c080112290a0e061b0306061608040609170f0c041d0a08030702102c010e0703030801080706080c030a0c140409021e030402010215060f090408 71
    0x14003d800070001e40701c0f0258100e8000031309004011012505110f0b030030000b0310a040041700761440c050301c074101611090f440341070550280d81c01d500c0d10b904d03248a04540d00b014002d03107030000301103022a5440780d0300305106005d0f400010100c40c0705540205c0c3c6204c25102c0182d03061009580018007940d0b483e02d5003000b0308002c100d4000c3c80516883c01c42d6124112000055a901c12414280107002c28031a800822000c1d0071141000400510048010100705008101d16448188160201526480c02860080ca032400315a084445103042000000c0011401c44034424840071100404948042c400950340c0500304072580c0440e10f104d6410000189907000103018181c0301e144064521a0365a41021100039500741e84411400c081000401d04400140c2d00000307151000f0f00300f00c00391403840444c4424641140d44044840c0da00000e031441c01141004900116055000102c0c4c1107013000c0d00001e41c5c0b00025461403042c00840000711f000781d558000101075020b4014031881c0e861411f890600c005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 756413714 1250 756412464 756412511
    0x2030406020a031d1b0f0402190807080f130609121d1207140312030a0207031806020c01030f0f0f090c05060a08130218040b04051c09061101020904 65
    0x20349040d40325020b011030400700a1340543c1c3c0000030840004036540406460b900380314183d0f4056400320403000e40d82c13268006000742c83c0000000f900d5000801001814100c0020401c8040028682c1049001c070034204259070440c0c0003145044640c40b4901e8420700034001c50b0030207001c0302080c08411202d9035104594904403401104009418241742003440103403003081281039105e0300302160601010396143c12201e03c85000404454041c5000520800554401e48091600c5c41d000222070041c940c001c0c58004801700d04298120cc50340c5401c1c8001e40341c038005841d050400d0b4903010300c4c0e40884070300d8220900b81c005050302080307111944482070005064440085842121424000a0b64035081050710124661a250600704d69100402d00b29542c0340803000320391040e10318501c8141050204d2545210313502c50b41450381a0708150400310302e8040c0c0890302d004000c440c10301048081c1c0d03010701890121941801d10746000070410740d0142c064000c51000d5908540b411a02002680207195460b11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 756414964 1250 756413714 756413717
    0x608010506120102030c040506210403120608030f03060d0f05010606050901031a0108070f03022208010f06080d0f26040c080309360f010f06110a0618050102030406020a 74
    0x440d40c101042c07a500340e000032644841302120a0004002904100740200b0240c4500740141e06801c0f00f080444d02d1460301a242540003030410101504480282c3c41108090014000210305012a003146a4510b01c030040c00d02c1e020354122003900080002952200f0003488d8414000d0000c00d4a840008100d50425002c06000909140c524046502a10042c400781503041e9109040303691080b405507110280544801c0c1095401c120600700e00b9030b800301043c0a000c0901c40d2070703203443c81e00d007826003590680b40b100c110442c03070200100441080000c03c9243c2c24403900b000492106404000d548200180d0010021088800d501500b9000f15001349071241d0301c03966000d00955117400d1610364070b02800c00d2042d000407803107650300b0200a07110b02840b101e00d0f40c803048100d00c40c004c1a4070000c4030380503251922900e112a005100c5010102501009860707d860041e8059484090940d51460070003c084d014660702c400088244414001510045030404001c0d0740c4c1382814905500207600c44000b00d0b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 756416214 1250 756414964 756414979
    0x72d0c020918160317280306050a0b1201050f210307020913080403170f1306080105040b1806010507080a081005011b030305070509041e060e010b031302130608010506 73
    0xf0800203014000015a50020031508503a01003580d081c0c1964040b250034811200141c0d42e2142940080740c2414101c181c694002c10303210f26100a0002e02541d54020707000c601c4041c000c10743c3c48000d040c1c140d41140c070308480300080800c4200100d0003040400068089440074200f1250f13894130300200400074540301b940e00c041d595407a800c904600d00c04884005007403007801c010820204011042c5071520906151040b89018903107041640c0c9984401c41080b507e00c0340110410046400822180c01080709031428001129040c0c009004540410000036445841c40081a00303070b48283c058618090b8042c5280d076982c040080003a146810496001501c00c007103000120b155440b41e804200e07210041101410f841c2c0540e90b091b0050080185010101300092184985d5039a45000b00d007400400381c01d0701e05e1400314141d418801e50f600c94100510320440040104000140001102d5200565001500a20fa0070303200040d039111654080c4d40000b402c2107004210000190f00081c092001155041d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 756417464 1250 756416214 756416233
    0x610140c0105040b090606090403030906060e070c050708030c03041e09060f030501050703060608150424030b0f070e0d1109040602031e040804090b130e01060e072d0c020918 76
    0x240d502c600854050313170032100e48e00100f00024000c0e00001c10320761003170901280d1561950a9184180c02c00c588200003d80b18401c030380148182405440c000c2c101c27a60196180485890107a42c1e20302c110b20504c20009603050400c00340114180e4284042e2803051824450f9a42d0707002c4010f02c0034582d00060380d03254030b000c020480d10f50081c8980c404494a0f40c88420341030342d81d80c4440030058484400641c02c541c841604c180d42c940090249600e5005800c805030b2060700b03604102e0009400104000d43c00d285180a02c080c85070000984150140308aa02c1030b442c40c2203241c00403641000070072494004920ba018041000301503009036200748420f40180c1c4100c400c800c9810350f0140180d801a11b07840c0c00f00320510005105412100009101408000304080d0001561080714009014151359035540d40040c0210902c0102d01d03900038000e4a84445503410319418005002200b0b45015801c0b00d8840491500c50300541c080c02003160010f2036407503945495299244070040d450540803641c000c680c103c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 756418714 1250 756417464 756417481
    0x30c03040f0905070807030207110307031b0e01030f0803181c1e081617040602090f400e0d080a02041202040f02091e011e080610140c0105040b 63
    0x10180301c4c1d802c0e0b03511207201e1380f110503054000f54403500c0d0507203d10b241d41c1c8036100c95407410810b84e4015841580e0886c4400f0709107094100d01811030b0886082c1084080c01080800c220007866038243d6005002c2969a45a1656451000075603d004001c140110020401d10a076101e91000c000c0c9842d8607910155041d10240c100180d40c1f00a40e04080b501d1200450b011041204030054a4111410300c2c407083d0b24040355984011000700d6003101d26640000d4400306a003440308020f138040c2400e440402e01c618000c0c0f060031390200721009150300401621151007a0500d840ca1846030651320560410001143c44529600c0d64840075004011620040111311000000d00c05c07074007298911220400946803550070032028085508038034071001d4090029840c42e55a80f0300b0f070041d5584000c4000205400d0340300141055a0a0341c080c0d040082261225580035040703451300350300c984100c509181398181d00d030b82541c04090400c011400a0404100350b0b10300c0c0f40551045008a0240380710f03031501c2e60f40244 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 756419964 1250 756418714 756418721
    0x60a0207080708031315021905010e01090602040305011103010b0712140f0d241a28080a0b01090509091507050a09080106081510030b0a0504030806030f120706020c030c03040f09 78
    0x28106d00503030140b012500c0c1c5002607503141002503c00e02c0046201e0700c10310345441c20342d180c400050b2103103580007604008001d024130800210780948400b00382190300d4250b8540e003a000d5828040d2042d0517106020000a00c140a41519030201c07103a59138481d450031a0300c0c4542c0e00107405c44030b640ba02e4200050303403250031b11400116410183c0707011849642441c0c401d04100ca14414450701880040c042d403c1c2888081001c10501c49254038a8070808400c100000c00750040034000311500c0340b8040b10f03003410366170060000c42642c40546400c2c601e071b280c6100aa14040b1220500303078500c8606d8007800344056110f002050142c40590301c001649072282c4480342250340c14030a4050590101c28081040b41151581e56881a003140301c0345100da60720b1300c43d030260b110115020b4408640d20420403040603041007000c0e41003103040d80202511034850319007590b10100c2c0000500807180c0400c80b2406c100941e011540c80b00840400d41c1d0301e801c400a45103503a50030600402c40300b14031001c03020400e03035480d10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 756421214 1250 756419964 756419999
    0x1e0313030e1813081b1f05010b16050c0d06020c010605010809070e0903071709040c05090a0e0c0903070f0303320a090506031e1f0302060a02070807080313 68
    0x1050403c0d114070440712401103149004450f2903005010300c00c8a0815139070350b15186450540a0b154545407113010400c90fa07407282005402901d0440103014018100d0309480c66102100381c624071041d00c2d0301b400361501c0050080f0592014642c620301041100d241c000d018200783e440000d000d443d445400541d0b0200307080b519501184e10002c0104000145060120b8114007803109482c0760511640750450000540c11104c1c2c03100b01c0018050301c0c2c5050a1040840054403494a00c0c01d000c0100d001841d41061449108910f100c44000300d001903003010201c034500e140040450703100c40e98410290601c0e140c91300c01900451100c1d4044141e454406008186088420b280c1d000c810f2680001c550f4241c20866030700c020040302c1d01011582d610707404000c0d0b016141c0300111450b84050300b02200742c14400240f680140c1000b28050840a071808802d138420303203030704035411905d50f00c004c0412460025554800301e400d2051000000d041c0034040000c20003082c4441c01021115102c2145400c8404001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 756422464 1250 756421214 756421249
    0x82407111209120307050f0705040e03090904080d0f0f0501060305040804120f0f0303051801020a0203071e05070f060f0801060e10140c03040518070c03051e0313030e 73
    0x1008640c1d040c01840006010000e0700500b481000111400103a196030070000084030258024803001d221101c0401025004020884090040400e10341160b603c90090f0065a80981d0070800450f04014100702640c007002d1240710308003c001c94070302018000e809008500807110703252200125116119001e200c2c8640e410500c0035140170310f4445400242000c20700d0603901480070620080000f0103800341207120718013980c4c021405090042011800c00001222021140e104118100d40c158000c8142d90311710341c1001018070542d18101d03079600700080f22440100540075098012900035148042041901c019035565069000300d607609845400d4207000344000b10300586540d05161030f101c0d11f4607100a03202e00d0301c04094000c0039144030064103c42e00b0400c0380e8201190a10050500703154010510041c1d0139600100e0a14200107000701e941640050100140002c0201410240c0c80c84240d04c00c1641c0030700359503840c05256424a20f00360f03107006c50005001c40c03030280f007519010000301c0c20001c08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 756423714 1250 756422464 756422473
    0x309150218060c07091a01020114010609090e030c0106030303291c020102010e0d0f0e090412030903020a1202030a080603030a081f0f14030706110304031b08240711 72
    0x41c88100000c541010412010902c509100415041d809009158510f10180c44a070143c01c0e100c1c001900355502d00f81c501e440341c1c0520307004104003a8407805420840742c00c4800010203202c0d117030100d410b510a0381d2a01586608142d8004101981540900c0130200e2030580d40c1c0c1b1240e1718014488201c0494801d280d031010354505290541c0c2d1540c500c1514051050000062002c0f16900140c20040d00c40710400c0404c408002e1305100c15000340707600d840754008807014061841d09560311482141c40c1002078040560356851802014000c00c407100d030180c0c000c9841d1240d00c81c8914025901c0d4020300140d4009486440402c0c11410004143c803898000b5441d42880fa5403188010004803d20030b0011120b040b50f00030014085604946010251504466402041c0d140000781440c00f83c0729880340041001c5440304c14081d103030100541e0241c80c0e201c102105441008412003451540c190007090b100e000703c2e40000780c480d9940032030741c01c0c2c4840130304085031035541c0d01c1c800c0c1c070380f9030800742151804e420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 756424964 1250 756423714 756423757
    0x603270f100f02120a150b28050c1f0c09050d031202090616060b0a0e1602030f0a0203130b04080a030c06060b07050607031a010509011d030d03091502 66
    0x1542c000a62506040c4030060800d80c80c3e030700d4404d540380c060f2040412160340d00e918901501d1080c05500103071400c0c2489614100b20074174441030b004922090610b641c400c011400c40040d2140c0c084a01713101d0a40c044401c0841042c0c8411301c1c00c211074020700280c40c40c010803400c41500490900044483c0184503506d908150b40303080d1601d19010b400303010312a900b005040300d29070301c030406414a00f54007030403c50400050300d401000c0714030001318948903400c1d0050820001f03a101100e00d502120200140f10544404e035020391441c007640281c00011b110110302e1201041d4004094003140c9208001c1d5000650389081d480303458030032030084c1c0d1441d401140312200401c2c0a0f15106665910580001542665891444503242c00840c0125140d402010a00403065070500404a4285003112002200318210340042c24512503200640d041c00070328014001034a80c0d403082581c13000c01c00343c19100540381c416001401815580e5040300c04c500000f140d40c101c0001c0d0b20944040c0407026903032649810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 756426214 1250 756424964 756424993
    0x705150f0903011b0509030714091801090b1315110a030e070b03151207080a030c02040921110c06041e0b0a0503181b01050310050603270f 61
    0x703104000d010b0700b40d900c44140e0105944164640f030b814000c941d8a2645030b400c240109810868654095824003e00d90b00104141d42c5007044e41c3c2e0010020a524941c015034071880703501401041d080034004018503420014042e09010580c1c0700d05100e102e10380c00c09084c0392500303000c40e8240c4c03051111500c800d0044000b01c500a070f1002e25515038420803900510b030b540130520303403a07032040710710480542440740441a142040b648c3d8924002d00240030342030517420300b51482d039100c01e0480083c04010010301d441c015515991b0120000682114500c1c050360804a50040c2503113008240c0000982030380f400c03c42004010170103505000300100b8007403400d4030f07100344414222010402c000e81c840c250a0006032144094004050441090300c0e0141c0f80c3c50005154000e002c60124209040e070402c000791041100610003410300c40400b4280907843e0748070395640710a00c03a8590002d5070084c1c00001031002500303280c800388842c94520000c04021406840e41c0545900c4400f205000c2a40801091503111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 756427464 1250 756426214 756426217
    0x80702070e1003020423221205040902030a0e0d0216030b07050f040e070210060e0414010609090303090507080109030f0309080d0501030f02033319021b0705150f 71
    0x707102a079540001c141c40f50002011260213031044032001403800120107001c0039842d10307198060035445040c500744040c50411a91442c0401c40245000f101408d0840d503e03006100340c50113440100d0086440b8585031810078010540c9405107229031140b544074078201340c40001c10070b008a18000050000c5461942d0300215040040c2500d0309004090040401c0d0300038440c0940024000c1c0d0f500003805003401c010283c1410780640c2d1f8224144c1c00d00005211440f140303240c243d0000c1d8840900e424906810000364010150758108004641c02c0c250140305040d4103400002c1494000d50a0b504c5142d82d0311000ca003200c0340a4001404940454180014a40a0350000f00c805006008141c60304800304030030340484a09800441700b0302c6000015005605007040202c0303031070729180222103100c401500d18540f42188480f400300405105400200c00407908104021f841020000564a491502d002031104945021500c0d44034418039038001018a488201c0c3d6a200f10700301c1000b0301d401400701c0d5042c80e9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 756428714 1250 756427464 756427471
    0x20a09020f16140f06150103020414060901030e03130603050a0204030b06011b170d0e060105031b06090d03032003010b16020301140a060801060902040b04060c0c17070312080702070e 80
    0x14500306906401c0c1540a0240404d0003010401410b038510341014100d94984210380d10904051040c4401c1c0440e4041360001a98540b00f00e605030746071002580101d0140040c65454101d600001ca00c85110a4400302c030601078440c551401c4c00203170b81e5805000d04030300552101400701c1d070000010a4203540a8418180052010f02141300f01c01a00e84a601b004012a910000c3c8032400052800c2105003510840410604643c05445d25515000010365205031020714414080c240101d50081681c075042240c0012102070071509400503e410094000c00f988103081c814035823400d02c04821410341c0401c881c1615040c240040c00d0094180c2c60211141007003200b20380541d86c0b08007021100c50380d0a91507100e0041c400d0b021482d40d05042d1801d096031096407081040340d0060100b84070244030307042654180c03542c80c98450100c0071581042600401264412091010605031808a4010100e44082a240103095a140c6100000400c070381541c0115003810041e040719505010f10451700000541 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 756429964 1250 756428714 756428723
    0xc15090d150504050615060a090e06060403051204060906020d020a110f030f0a2321040b07050304080105101d07110d0804060b100c080306040621020a09020f16 70
    0x61408944009000c4410980d0251010f60020040015500c08008040d0008001f940c2940c00d012140030081d000e41e840b40590500d4038000c5000541544841c82a40e00441d00801110b0a07291007410244081d4418001c00e070000e24401e801056460000440703101081542c1c1c001c0680411584074003981240c100740b0315a0124909443d94030640d41080303d130343e170400b2000140c070f0a40801d14044001001080d0304041040c815407054101410101e070881a022017180118000c07000d00c01c2084062080360091b201043c0089602c20034098004003404c10b407601e10000300701c1600c1302c031414605610b240c880c0c54003a000107030310f50300751503d110121900101c1500b4086030904010440c6800d28114190307040000d0000030400c410b00400340a00b0003c0c0700191030340d41d4900e24100c1c00903e1100480e48c06041e400340000070507960b484a80c00715004003540c0796800e40c42e400f040c4801004500c0704900b64880e00c10001c000c28200090300c00c95654a0b1803500ea10310300800d0400550198074034642c00d44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 756431214 1250 756429964 756429983
    0x270f0601020c1e0f040c0f0507050f06010e010e0901270213180203060c12130f0210080103140d050a0f020102070221060108010c080615130305030c0c15090d 69
    0x650340c46140c0c0740040310100303003408041c00c03c00b40f091118015442c1000c42c86a820300140074107054105c224004078101610b4026030324105804d00528184d4a08a0014103101e201c0000840d5140300c0c46481c10384402203090042d6868040c0d4403401e941d90162590100100d4000030b4403840d11034074444540384c0c806410503c000c0c20009181c011a01b80d10107178032021300c6405401e011450280701aa50048080c07090b01c2c20440040318110f14444001d00128001c100f20342c200c001e021010350102c00c2c590b030090034070526680d140401845a4820304c42100d06003842290410428804a0102071a0b501651001c0c240307a20401c0c2143d440495203000c505656082010f1805a100d41b851080c008814000d03003040850403a0000e03140400503031002459900d4030003548543d81e40581207640002d8121000903c4102c0611400481c0c803500c4440c24241c0480d070800002c200000c000b0b00400d154030800e4590401c50407051008070484000311641003501040013114074074002034040c0c01c4038007450307144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 756432464 1250 756431214 756431233
    0x91317030612011a0f150306220615030c0e010e040f020c16031218090b0a0509100609050f0a030b130f0503030604150e040b040203101505270f060102 66
    0x80b400c481e4841c54a0100011000780c01c0c1580c03c24245840045e0307019102c0118501010750b01c4906404050803203480b4400c291b03400164000100c00752100d41f01c81090400074503a41c5c40078088400c0c500b017112000b023420035007030680c1d043c000c4240b007811a00c182c503a8103071903040504100c01440d00c01c0d80c0c1a02680e086c0304001e004135040010b5446240380f0190800e91038110b0070f207014400a00e851b00b004000d11011041d180e0300c001407a030405c5401114001c10007807007400000d010361000b81c01444c0c1000d06241045011710012800030101c9100341c03242045903071500c09204013030340658a0380c0d8101c00440350410000d00300311601580845208000c071041800c0c0d5a03480c195081c09034054807183e0001c811700c45146000e20480d0700c83c5156010700e4070810f1401c0e0509950840040000e80504450700000d025914240842c807044000c43d4000c10603080703941d414002c2c0c0185401103c0c081d000740071520f4644017291340c1c0545605409a6000001c1d51010076070305900c0c100801280c110700a01e01c60 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 756433714 1250 756432464 756432499
    0xe0409050723030f07150e060f310503250f0e1009090f0312060306061d0105090c2718070807091a0a1403070507020913170306 56
    0x151582c40c041c1181d54072446881054540094600c000d500d980141c602040418030f41040c03108030100c0c1d400c0012180a681d40051911b005041d540c58042030006440940b10305207001c0e10b07803004c07688070985440000d0f00798040141c2081d0b000c0da0b80c01d9404010651030619841d580016080c0388490620000c0391541006881c0350240e0f4001000a001038007804281e2080c0d410100180c50269000c0000100c661500354aa1100c00000342c1407007510340c03954007011882d420910142d508018144642603845c0152041c891150708000ba19450a0002081601d040500c0b24001c440014049040c100034102224a6078249140660341e40708c0b50802081c90385803040300e5100041e0304030b40e080c01890f158401500351807005024500b0410107040038803400e5160a0141c2c005401602240d855008999090b11140d4a551014095803808010844069400002011914429520641c1d15201d1102048009000c00001040c80b03400c0c1404088100d20440a075501a4004010510721a03070303040c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 756434964 1250 756433714 756433739
    0xf1f05033403030c0b01080f0303160513060e04060e040f0b19180605070c03020a060f0209030a0b0405120c07060305220b063604060b12010203010f05040504030e04090507 75
    0xb04401003403c0142800900c150401610700600e00390001d400007035004032410361a413000400003c80d140c402d401e02803e02d032140707003610000681c3d10003001031151104000380c03461164086451103035090100100c1e0300920120311901541d40a84125030602580c0d840b502000303c0240303428039010240796590401411801035840306840341c126002c00c45101e09003076098540c000c0c422000d02040c40100f0300004c1d070014010140036000400094540782c40800c0314064425101e9841c0d041c4034000c911014000076041c240c0c0146d200358109c1328490303072041e010f140d14000c5c0f06810001c2c2e000341004000c680d0180c2c128035800400810024540014448a01e1440111100541d80e0009120030054142052500850310003460400320301e40007030710114003107582490040524002e4052010a003004425046014214401090344620f043e42c403014130b000f03400134031510581031000b000000f1681010710440b406180c140c0d0302c0e440d6821450081c007002d881c00c16400c80301391140301e90014010307040e41d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 756436214 1250 756434964 756434969
    0x1b210b030d050d060e07080f0a0b030d091404200a030f020705030d0c05030c07060b030f010e1506060f0301090207020a050a0602031c0606091e0308030f1f050334 71
    0xc82d0035803180d482805002c02c41c0c28680101404240e200305004805406c8440c5940c8101c0148a003038003581d42018040141845190407601031240031100d4006580014022084d0351040c1101241c204103c42000262012514008900844101160b2038809605e000b480c0d016550b003004215000b140404800702e82c040417058455400200d491000da641c1ea00605168220914242d4207504003440c0400651040d08402014107130703212034142250b14244072030f4071a1109180204160b2078180d1030a074454440e00e50b10080901c008001400ca8980382c1c043d21503e80d180c900321402c5130b003007100890080d8040c0d40140c0e03220b440d980c400902980c56150050240807654042e54484000001e44110f0000c070b10342d00c01d007050418006100350380d170190801007101e8041c0600e2a8045030b20308024114545a0005844400b0010401403005102001103004150321410344024071940103e403c1041528040d5a5140d004088001d101815055540211601d00a40c20b207025017a0301c11482c00000e1903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 756437464 1250 756436214 756436217
    0x80405120a030b04050f07050d021812010905240a0e0c040c09140109051003181a040c050103091119050603100f05060304080406120b0301090309091b210b030d 70
    0x400303140d95a400c01780076903604140e503414800c54900f0204000b4100e400752003032902e0301d141d0201d043c12280400c0c1011061000025025691103440174042e20301030240c101c0203a900c5d00c9003005100d40c0001e13030b001c1801401480b05186045440b60b82514025007040f03081203080388542c206004c480d5072288a264042100c64a0b03044802d0700d000b010221a421401c0c1c8141400b0107103004000e26100c40503610b42c0c0c030100b40380004143c00014070001d116001503502030005c182000c9400300d4005c10009a501a42c055500401c0181d5074100440035100c0d40180241081c802000d11141400c100070492224011400b21801842d220701c041354003600202e40250108030840020450f020510180a016103015100d5514624054966900c10301c02d9106240800c08004100481e0a00c40d0303001d080c0642005000b40b04501050030000c01600040c0034058807603250840f1b88102e6070740e04e11000c070210015160840020b4004001852851b60704120901e031607110313030b40d8901c2e594081c4071803040004c15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 756438714 1250 756437464 756437471
    0x6170a030318020d0f0c030b0c0a021203071d03030c100609050108010c08070e0604030609081b010b0109030f0c08010204081c0207030b060621090a06051b070201080405120a03 77
    0x303040c02800d03101d80c1590a80031400c24142e00300542c45614160804542001c2c4a042c01c030928500810343c18080e60018151410350018400609500001004254825800c80b40d26256849011125110548990000c12220f547d8030b008814107000d43d801d501c1008040c0c0e41072084000c0c1142c284400d030b07195601071564840d001d03c1a1440d84c0f0504e4003420720710000b000034403001c62018181c844090103071402d001000c96451510b0740e030036007111702442c0d0100c810301032090907213031020103900205124001c0c034110166a041e100300500c181e007040c050580d28220800d01d0b544a003180c400d0024015100e0303403c076030000719084030240000e00042c422100184198504824440044400c910149003150003016003000841c8010815940120b0103c800d240d50b8480d1071400e40ea000c4e030501000d100c4011141c1044413800000c44c200b05a14090102030145a0f41c00c003010091240e01441d015400744240a4400075512943c1c00c2c6902c00d21500c21a140c00350060341d904c80540280c0c0c24500000e46 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 756439964 1250 756438714 756438733
    0x30702010e150601200703020d03030b01020d0e0901050d0201032715141605281103070209040605130c1203030608032d210405162102040617 62
    0x1030801c1808105002c00180401c14101600000c000865511601d0044803510401035006070051045c54000e41c0e005042814400b294a0060042d14840c03000714003501070401c2110407140aa0210700125000801e43d0034070f0307030804082141d8800c0d911026410191b542e180124040c2145c15114000d60045100440225203450880c0e00610402039152009052402032608040314500c01500503e1200000d4603814820307004981310302401642811034040310134001c0700b0609070004103444032401e0f6210204a040d81e01903e13924403d4017002904030951600040110342c00d607200307a030040d510000014048126840302003c50710180c1003501c8202510744c55908040d003500c620380042c82c6d0316000d9400c000c41010308020000400031508202e403010025903803001c0e600070858003508005030804541d05030540d0318080b603c00854044403948160103000103041c2d04400c0c51030484000300380a8011021019494501e9107618200b00c1e04140c840002151425152143c00c0066140400800d0800c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 756441214 1250 756439964 756439991
    0x10081308040b0c01230f04171210091a0603060d0209190c030e0606010e03013e191101020d06030302060702060604050108030403170c0f03040f0f0b0304061d0303070201 74
    0xc491090000c0075040c040f0302c051724400c016405a60002c00c20000036105d40c2d6900303041180360f0951940301d001460018100c14400904c0420602444860011000c1e5544840700c280803144544268941918244171080c1c081c81c100c0025680b040c809007070300708454256808514800000e48078030700c0c00800d000c10540f01d07428504c14000c01443c540380074841640901d044507140c83e0050803a0b4100301c6040104500f644094000c0010303009144040510000041c40c016114842184000303c003081c442c10065a071004803042d03c40450310140e216400070795010066644039a58040c4451a54003400580c1c1000b400c0c1c45510000c50080d005410382c0e2519503c001d0030100010321080c469450000184642200081928250b0381c0c0318003500d181c00c401d10380580d018014403800f0200380c41540030302c845011000c030161040301c4094140c40e070a10740b190b030303200c00c034a200d40a00403890000b8800a404110340d90062050701c501c017400c8009542c4103a03160741c1140c2c01121100302603911ba03500b091514 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 756442464 1250 756441214 756441221
    0x50708091218120304150c0b0a050a09210e0301020403080417070807031a09061605070305042d09020f0928090e0c010305060d0204091e0b0714030610081308040b0c01 73
    0x40c04038541a00e0182480e44c8c0c82c1c20221024204241a550343e00c0020746681060340500c110a402c903162111100900181041100d01c00c21940e001a2000380d65161070b060500a440039280d2010820341000d040540140540c1300000b021000c030300c80e03030100080f0000c0c00e000c1500a1402034545042c5000719a840c040400e00c080c000c004503600140c02c201014440358001b0050151a01c4c0407556050581000c4845004a41200703d131104003031141100c604404c020402e1114001c1c3d500584d01d5a00da00280c224090b50fa40e681e40c41c0d0382080b0350700705c2d80f40041004105a00094490310440c00200450010301c45030380040d044595242c11503c0c900300c081040305062442460140958500318000c100503040746007009000c3c545400c117090030403584c0c0c0e90342494804010712403440c0c140035040c03c410000c1c007514040040386025400c040b048016004883c41071501500441e500b00c07001d10b044130f41d80d40003045101300d580008041da0000342e0b058001e0000b4400017440540b111b05101c0d20b242103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 756443714 1250 756442464 756442499
    0xf11090115270306060e2203021207030c05100c0e03030a1b020609030d0509100908060f04080c070303050403050c06070b18030d02030a0c03050708091218120304 71
    0x1424185015215560b512501e180100a090070b40120702c00d01c90501a010002150001443d5134144000400d1034038012412a100c1c600c1400075500c070100c010301304043c00602d01d50140c0107800c2144c51504ca45829801001d0551207441c1036510554507444180c103143c200e01c0310101a5459901000792160300000502c0d102c94101e010350b00d40355601d00041c101400b00d01c000e00200d000c1107400703000c0d0355a14080d0307005110003800351007003521101401025644101c6440e0702c682d94203484440e074184031704929801c0d200014021702c1c140c0c981001448580d28010003c866000081200c54002d40c0701f40008e84c010740c401c0d100d542c3c0769800d42c6809030920078280c0c00c05000e1310050149601040720141419004202080c04154000320601c000e03003103129040e90240c110b80004240070700c080f10b40d0301410409a4990f4104000e450311071007214010700940b80c49001c0d90148000c0a251810140100145100c60048450000e0110301107900451150700a01040c0c0001c1000c118a41a042c0074039403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 756444964 1250 756443714 756443729
    0x1020c01022d010b060a02070905090313052101181518021005130f05041401050f01030b0a05090408030702060c0a0f050306010309140d02070816061107030f110901 72
    0x1480c0c142c40001d1100300302052000c4504068091180d0000002940722100c03602024040568a480c0c000002c0c2d61003c09114071644103180c0307400104040c502105480c3c0303d01c0384c5540805110310300702c10070001c0c641115540c1a81c855014039408140c0c2c0901c200414580d5241a00000821b40d040c000c03000c010080ba001d107a10b05043d103400c2c468410884140b030751a41140d18246451108000322114019911980c3e80b1301a40d07500807441c2000c40a02604032242180c090201000e180702e0300d001d455081c401d031358104292007801e44031903000f0f80040f54030302c5014180080503651b4000203200301c0c0040c1d40944e0301e103000106026503690f0621150361b103c1c10002d0f50398941500103800070714040c2e504807824104040400410304c1a0b200340c101802585e0044140c1c40340044060003251500a00c041c5a800b41c0b0030030b00300003000312001c5400d07041c00460562180c8202d10384a0203a81180090307000a1440c050880c02200080404020394a841e002e0207015034508400c00901426086c103811004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 756446214 1250 756444964 756444973
    0x1180f180608060117030408060c1e0a0e04051e040b0709050919050c0d380901140301020909040302150105061207230409050a0b0901080712150609090201020c0102 72
    0xb0100000054403030444003d118440c450245070928075045000300c4e00f1441c0180500028030070b41215450142c2540c11450811001094176104201c0080c03103104048004034240051007007107403406921955104031840c480c2100c2e90b074400f94041449104039411a0150010803c0c000020b9010f019400a03210513901c00740303a8240721200e03080399940c01c90669180d50300d0b040000c008081000507a0001602040b051205040108100d1a052085410f4890000b43c001c0c1c030040541d50481c1d41d41c2da031900030304501d441ea42000581541c6036001000d49816640800582c40991200c2c09458440c5029901404690509507401c0c0c10414069004d644902018403483e00200d148100054121082c1e092200c0038005103880da8014043e031483c0ca106d001c8010030000750300d400580001d48a2120301e14100301d420880010084508820f00840f0314691000005004960580f00413070141c5014038550f1038940c460696171400c2e950700d9003000c8681d03605c0d0661740003103580400000e00d120400340007a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 756447464 1250 756446214 756446219
    0x1030b09010c050d02070201020a0606081005100f170c03070b03010e09010603030512100305070b0a032007080d0f0213170c060904090809030706080106020607050c10020901180f1806 80
    0x700f540c000c9850b4904da10794001504011603000b000b030b01d2100c0f580510140401c6640b06000381d1100345031095440040d09041c0013134000400300d2031601c00c0c0d13400307580200101820480e8141014180301c1141840d07101d120303019009581c0c1000040b00511710b1070b082c02e55a606040c0a00307004031026180c0b10320b0b40e0428205100207500001582c1081e50b100803c40220740d1014410445010b15500140c080d001d00f2402007121a045002054201c419480c1401a8403081e041c1607483c2e030026a092086038410b108960018400310010200c0343d43c00f81c1d0102c0d601180c4a000c504903408031f80c0c001c0210310048810418280700c040a0000104140049e2040717440910102d06607100384c0642070b10680c2d1b55040d4600700690002990910319000c0c007101c18007900c500024111101c04c0c061100988205000995286c3c882c41c00c946118500d000501030b05a40320506502035040603e5603070500021641081c4001c41d00b0000000a010f08a40070012502c0c0032007400080403c014011045802c2c079805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 756448714 1250 756447464 756447467
    0xe100e07020c0603090327030d0e030a06020f0c1c08091b0f0a0305013e0a0509011b0f1203063f06090c06052803061d01030b09010c 58
    0x214039001d0401d0f81ca0654a686616030310342144140822000180009900f0500c0e900070800c4841001809030102c13010a000341c9825071f020201c0803170007a0325038080000c001c006803494002d0120740c040798006034209030391440d0140c10b000c011402001c2800c000b01e2618000c0b54000050fa400c10201c0015028030101090310070f6205c001c010b1401d02403d4403130100c042c952150401c600013107401c44020814295140500213401e00d102240100680c0c2200010809065540664050070010800145090400e40b810303039142d040801c42605000300124001005070008250481d0144100f00388010b40c0c100d481d0030494030301808288001c0524020080c0883d190b1801d0f1643c1c1100c100e0190304d203100c92a02014480c40994405c0c42080c1c4104140108000700c0381c20542c465842a01c0182c05562100400c41e098000c0007003450a0342003180840d80502e50400346071000c0001e5181c0810601c2d11307020300c54480e5403440c02c2100e42d051808010018405032494540c1c02c0b620358402480210a403040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 756449964 1250 756448714 756448723
    0x12130905060904110102070b1602120d05070f11130c0f110309040504020409020d0c0608010501030218011b121709010b03061603090b070905010215040215070302030409060e100e0702 80
    0x100920719a14091506a001f00445002030000d482c64a41d01c0d28201d0883e070b20400c0140c000c0380201d10f1485448408000814041003140040d500d03642840b130103458141c0b01c1002020305841c484450040500c40d03880b682c0500760f190f03500c8003000c0f170103c2d00c0d100003d00b0007004980e02800c020722451420ba10100100c202d4012103411078010070b41e5155400000d0080008100096000042650f04010010119003c0b01124a161207136680c0d80e987d440103405900c641c2585400140381554032903015070043e13030140781c6074465904030a0800c50540e541c5d0b80c1e09110008020100f10440d0745d14402003288414580e00c005c040f4024000c0e5201000400e81d0741d400a00040c072102d142ca00a5584144298826800743c0d8000700c1103015420400005402e800b4140980740c01801b6078603a654944a110b00e50034011503014041240c1d205402d01c1c0300d0003e80160f01c0440450100b00000541d41031203005040182c22181c903c0b41250034120307038180c0c210304d65501c1543d0f02e0300340804012035a0b40104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 756451214 1250 756449964 756449971
    0x509070513120f0210020d091a09090415110408121b1b040f02093f3301050f010c021c030e0402040f05061b121309050609 54
    0x1003507a114100007207211071203415600001007841c502d14441003030080c0211400c6080c4d000f500d521400c200c1c03403082280c499000c24804000b0440d84442084032101c40c0000c40c041082701031009040620942c00100d29000a4030140d8104c0002c0b8803400803d499403084001d40480c1480813440e0a15044560b6191560400d94480b0341001254002c01c00384070200c03500789100641d05864001d10080c2e070508441c081140503900442c60034003403888882591084618407034005240907481182c00b048000300209140c982c0300c46103691030171328042d01e178000d85040302d01d2035680180c01907a0820490001324443c480034080100a403203000b9443e068000300880c190f840c00e64010b80c0d4060403500607204410459002900b1108000a605094082580c0c00164030310070369031030499401030010041a4060342c050002064060030b020441031030182c00421104c0c00c071001c0000c000005041c664200842110720941200d40002c03e40715039a2403038002030191901305400c001b80d050101c0490100d11004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 756452464 1250 756451214 756451217
    0x1050901021203100308030703090605181903020c061c0c0e0a0303141c050703060f0f06030914030a211b0e18010f0810050f0f10050402270a050907 65
    0x1041c00306400c0c284c1030014581224969650b4100480001c0060484c070300309644040c42c05000c60142c415907642e911104180c20300400d26888c1c13024003c80ca54004190850030341c400c02c4000100b030b84446003d05044140703284a88c50700303403000780410305990b07660301402d040003003141c420003095036404d1442d429660540b9003030034100745480300c0035103610134410f106040e0403c034110301c41e12444680000d845117400750307400e01c0000c1eaa0802d62150300c40501610010401802c0103018041c8254043c000241c000c64000d42004411001d8604592103a0074600c0080c00400b0320007542c880c0003520712018100c120f400c200141ca10400903c1c0545541c0030310b002c100500300c2d04992952480d42c0301080c88601071600109507907804a5810040e01f5210301a140e00405190322170307150083c45607912a010404140001c1e9507245000342841c0002440c162a030741c0c0303100c40400c6075211440a0b04481040c0e03d001255240e483c60204e2400c4901c3c500d42d032080f41e107240240b109481d243d285035005100e6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 756453714 1250 756452464 756452467
    0x1503060115110c06031906091e0b010c0201050315040b040f05060a0b070c03020d03033803120316090b03090705012a0201030509150c1b1501060c06020712080402090105010509010212 80
    0x1801c0f1500c1c087c210300e03803100c41038a041114401e00c0e60358030031602400303503c0d103e420000130b8008001915801402e02029010a2003440003a01500c1c101c22540e86812000b000021001407101c00641103900000903c0034240c0e88004004a5007003108114000e0111480c000d0b040040c5a40c405076200c40364000280161a44421501014040e40200c40441480480540f114a0306507209082029500d00242403100c010005a01c508021540f42404086607007518915580c140c0954684403561480c441004045c80001525079400005940101342a078042d024151408000600941c00b0083c0004881000694902103401d07400c0c4c0c007101c079682820041000c1c0d071280f4000d400c101071a0401c1440101c3c007010411900d04030b0004089203070910096003c400002c402c620360300c15120754400e200c4103002005000351409407040e004254880c5d580986029129a1003103403129480d0200c001144142c0c0c10711046280c400e82103405070070700307103010390800018400003580e0304501c08202038218030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 756454964 1250 756453714 756453751
    0x40b04060b090c22031406370b01050417010203091c0f0804150204080102030405010c081003030e0303070804080309030d14220518180601031a1503060115110c0603 72
    0x411001c980021a0010390320b41c4004103500d5038a0310345508823100c000348408045141400350392030f4110740c0e02c00c0140030941140c02d000c0c80321700d0047c4920600709040c024280070002d0014410407078008002101000941c49041802a032441d1035001c84c04210308588001041c10811b40c015582c21601d003c41c41d02d41c0c1151924104002c0300e060a0200030442400003e000c25002c005400544c0102d128600811111340b103600d08648c204825214070780c15984c13002081000c00d00c299040c0c1c00d94800201500d00e01042966456816130181d401000c1c150000300782d110700b614003400b550f80d140c1d8943c18814160b21852201c03031183c0c03080704104074010103203400c3c90801d40610205600a040701521a049c1d03a0740070000c100302e41c40c00311011520030030f01c040401c40e81140420000e0490f42c2c4041d91281d2034910036988607114600030310000c044042242004400d41e003c00c4801d0082104800b02c0c4030124903000010000010484103850720303402000130350182d0b110642140d91051000700d05c60880315 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 756456214 1250 756454964 756455017
    0xa030e0105190e041509090302150c07170c0303160e0108100b130812091c020108070c051903090524030c090a03050106030b060901080a0b0c0c0f06040b04060b090c 72
    0x10032407407841d941c201605008034800103039501407942075000727800f202c3d0700244100382c0184150086418048114007484018000b41c1d00304104181c45008401441c00c01041d05c0c0c3c0300d40781d40c0040395482114100c1042c00744000d034001c0c01d010f00e203076800c1c038001c1a030385400c080300c0c01800102e00c0344844c500400940b40c2e940708421070481c8054142c40050b01c250207a41d000060050f005615064860a00c02200c8058001c0c9021a9a0450b41c1030b180e480580c1d441820030b803082c0614103015109402480030610b450048175203000c080e41e201c0c3d1070b103021b03d6080200380b1907500f00106c80c410308100d5401d00845070803010707402d81e80d211201c1c0d40701641e98900980803841c040d11507800144950b08102010003044a00c260540c410740e000c0c0c44a40c196a40c80d00819070301d03080164040c1485e00010040741c80722084a006001e403c0064046a8903146000034061070400308580030742e0b0100c040014030040141c103002d141c49441c030403284900c0744c0c18a409203154a20504c19014401c1c00740d03440d4204243d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 756457464 1250 756456214 756456221
    0x309080f071a0c03040e060406060518090709030206070506070e06120c030402030f0f0c01170c07031d15070515010f0e04031b20061e0f04050603090a030e0105190e04 73
    0x24144074044e40d03101c50f914104080f501000741d0316107105034108400450039511803810f0b00d01c54034090300c40c401451403140500800e4030b0040d01a004000e10341e40c0c04405a15608001d00205100700010402032a1a41b0001c0c080c85102e0100c62003054100030290844040305040d94000c0a07c00a144d03584d00c1f1480040c0c030f4011140001946030040c070002508041c000304445040320000e88074281e18913022822856000400c40d844d003207c0205001d80004203100300f045d0100c00e00d50300708140354242c20f800001d502d4074201045884511002418908004050242d0505040618104112035060041d000002800f40c040d810781190550300040505104071800c1484504d00c05040003141c445040201d0791300582041c28040310401d07502c54400d41442c0d41103480d0590900c2c1941202100a0200105644009003034081185d09100c0850309035503140055010b103000340010b000305031161401500003075500500e01d050150a1202040600480058298418143c94082c100e624000000b6004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 756458714 1250 756457464 756457477
    0x171617090d0f05062a07020a031407050a08160312121d0f070e0a020c0a0b2e05130b010c1401060f080316081309020c01090309080f071a 60
    0x4a051000316040c4404001805442c41c021416103040e030341c40055540d4000c00f0b111000045102c200c036601440050240039082d0244001c0c803442105541c5d4559400210031003a1801640e00304603c104124074120340c8020042c151600940f09442d00c0300e00307040704001c0350700c000360521034100b0f80c08040034400d240c01e5240075415541008100c07100c0c410340f04d485c1111844c0110303e20820014148038000002d818040318510340125020740cfd03402000c100039403c400315503401071041e442103d00090750458458813503d10600405102d44a02e81500100e00c58402100c070003045800c8140043e0b2980c1e0303009455904120804610542d0100040700c200d88134003405801708004e8440f8400c2018190030010803204074a03103d400c155110754045440e44a62000440c0c4803504400707a00000d000790001c0d1480c80d04107500060895580c4410109a030b01038501c005441c0d5546180004141d088468400a44020030007003100e0384801a680c2e54a0560b4003e41d080c800107030f260103855030172001c101c941 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 756459964 1250 756458714 756458719
    0x6090c0c170901170709090b01020606150c010e030d0509010b10020a08030618071205010501020706021518071d0705070f0f080c010f0e120a090b0a051b030717161709 73
    0x130310b07064178010442034880c06110141801c0c0003010146601c00581a0702072040104248040000f0b480001d60a034030040080045540304c2c0d0440039000c41c140013400c022000e00c4e401141c1458201d03a103500316121060101d1041a0381a02d02016681c002540e50300d07194004c03003082e9252500c500044150100300c018100848001c42042141940001131001140002d46d0a00480c3d03202c1d001a621150305000380001603000f103035811000c1c01c10b84815a00107070740c61242070398501d1f250b2060341884c00d160454801c40342071292455981c00500101ca9018541e898060f00700348943d03440d0002820a410090410f8a02c001e00c2000e11002c0344c1155041980302d4000c02c0006904400d00f006090700c044000c4140c0900070765120000301d031408035800008107035105014136090103c01c42e252b8002050480410200303020200c5400f0918000d0400101080000e603201c404624082c4003403201042c440c1c6102c9001e000511087c0e200c9100c03001c600780e06c2548403591600081550605020f00d10704a507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 756461214 1250 756459964 756460007
    0x30405061f2301090f12020904080c0f030c070609060509010f0212031e0c160f031b0609060e010603020105091e04051006140f0d0515030a0606090c0c170901 69
    0xb12010b19480644400b02c000c1e21414401c6640781109542000305204007540ca04404045a006140000c0100c0d0f00501c034129184c144019000428500701c1e04501c43d595950000a25045081c020040300c0020000c40c031744400d1281c100f0350010b15078062150180d05125981c0b40a00217180248500e140040c44001665124940440c0c40708205684003008065481000040384d4065598012180d0080d03e6458201184040390345514842c40301c200c080d0308015014901342903088680d581c00480d0f0740101c04c0441e1281c050b04140044504501d04a8801c2e0316003c000c10060340c10000391043c80700200e0300807280b000c00003071071000c500041c10803650051030401040002c4a40d0080d00c01610341079512094883d6110344088028400d202c2c6040c903000c03051024200742011500066404003480c945900314129140c0480e192403039040c0200e5025494200070f1122f0041032007884030f510105c1c6401c2d500b055103038a4a1580383c0c081e0164075409040000c201e2941d9000d0204a018107c1c6407210f0b8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 756462464 1250 756461214 756461249
    0xe061b010605010314010317030612060405030304110102011e0e0102040e010915080d0903061104030519021c020109090b040e16050406060c11012115051302030405061f 74
    0x89008000d00e019450110f8900854004241000c052a9059aa00c80e0086130210707491207241c0c3d415000104101d61101d140301c503002030b1800c2441641e0045210328000c544a04003898400241041110560f045a00d880101081000b00d00d85242a41c4003907807000891045044449019200711341083c0d0301d8045134800020020394036400f420908030400a60780c11140c50344031071034842d920075814000181e000d94083c0301142095209200c2030030501102d80c5407236625512070b0300f4445094542424208860070120940c20010000d600340c01900c0d403940c8100200d5030003c0c1803081a80034813581c0a503201c07808665503d50358403142b20300c0c0c515000c4814800b299501040d5146c1e00707004140c000d070300f058400280035005000e80030300e103a030050722602c0c540351001c0110785041d0b491030380e0141081d003486070100c0300e100c5110303072882c0c04e00e240d2a80400b43c2c200300500003064842215030007110710420401c00461004108a50401c40040c021300c0c900881c940d0580c440301c0160410180c50100b240d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 756463714 1250 756462464 756462517
    0x714160e06091603230f0f0c22030b070513080c01120203060307050a24030c0e09040c09050115081f030f03050d11040501030b0307030b0109110c1b090f10060e06 71
    0x106031084a00c101c039209160380c0c007c03009001d51402d49444401520500003041214446010402c400100709020480b0560700d80b2404503e1030251100c2000c910b001902503994910029007901420b5210014603019400e900024400c0b400440a4000d0b1540130000ca100d990301803101c00d009040041c4810402c5448180304000800c090410154089a040c00c2c022000c1c001e014850800780c43ea11034013508941c52080c4010040000d00c11103c18011400104500481d4802c00c1d020f8501582a00b0341003180c0500609210300162090b420104030041035030200c4050152a41071b20390006107a4465602c0c2e00c1c00761003502541a0300c81d4052308080b14051801541d90161007169000d903000d0241c1c0184a007410f03101c000900010b800c2000e01c0d0f006004510264000a0892508001413441c11032481a40350624094501e048121180a00e4095091600381c21054102c2d4030f400010109040000d420344900c0c42c10312543d024041041500001aa540c10950742c4248100030580011b0009001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 756464964 1250 756463714 756463781
    0x61c050a020a08070309033f1e1104030807030c06022d2a070306150812041818060f0c1e020c060706020714160e06091603 54
    0xc02e40c000901200020700018070074010103440a405031034020500c1d03007038925003c0a071240403620544c2c0d03110001c20180c0584c104800b103546194400000341c246140984800500140a6200903c505000066807910303194070850b011030340e01058140d0360b01058941541d0200c9420700c0035006c144049004039444480c0004401c045402c2d400e401c1c0c0e440201d440301c201c1401940081c00c0c050380181100651030b240c048070040503020081c11503c08a80d02e990380400c1c1d46150740540050800488200450002001400c104540c03201c80b0600301820885070130708200f60820041140703a142c2c1004594001c83c2d840307100105800400600410096240c8400680340780741c20040014001403c10043c401c030783c0804040d00345a5805010b1074680f4104000c3c0760780141c10240c0324590308012403000685c1d241d5420031001040405402c0c80003c503400055541c0720b0b40d011800203070a5100304101c0c4da80d10b65020358029845c5406032100031164008400404880031001c0b6030005142d401040301c040c81c0e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 756466214 1250 756464964 756464977
    0x9060e0618030303041115042301200f060106030603030f030b0a030c030501020304050f0c030a03030e0c04020a020d034a01053c0106080403031b081e01030809061c050a02 75
    0x1c8040287e00c0001c1c109074114410740c8544080e40940400b03500e480b501c8000014882d5905150015294070052110580900540310000056100c00301d403200740c500500c05140108418101085090315545015140d907503404da000042594514044860b541c8820782d003000f540d044034070005020348a10f0850300030361080c1c3e400d55082c0319429804075a68000501110303e40d81c0038020302600e60300d607138042d0043d1155040078080380c000c51620207071903120f42c405400810401c1c0e006000f100148038000e01243d03114080104408022031545203044440304481007001110590a04c0c4206d280c20b003c1c2100004075030280c07055007018240f03c0d0b11001081051042c6030404915210700b80c000040128801c3c17803103e40c00da1080700500400625018488942d8054002d08011a0a40e20003540450758102c1c4403080002c80d41240502c080d90301c1900308644010100c2554800c0303541180c864244a001d0603000c180b1842000500001408061644a44c0d20340301c828280072504055035114080e41141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 756467464 1250 756466214 756466219
    0x40636030506090606010e190801020c07050a0e01030b190e33060312090d0c0303211e110904060b03150303070c05040b0f210d09060e06180303030411 66
    0x3501042c3c200502044060240c0c0c0146c5801814900c40c0c3c041c00b10282c407078441089405e01d0003000082c584401e000801c2c0041201c0060984241010300b00a140030240d0004401f8880c8200140700158211a1141c3c00c42e400043c00104d01e4030403601d0b20040c00c03030444800c0260280480305079441619521206200030a4181140ca8443c641c094aa28960484070198960f000320203402010511710010159182d020f8601c581c2820745843c0c0d20072007800307544114001080080b550801740c5040075030528025101401b80b1511134051041480f0500b450301010225540d100048032040e811001c54040140c0076100307000070341ea40d21260110703410031100035817100c6000c000c207001450080304442c06107078003849000856040c80180002040c011205580101e403031456000c043d03591018085c08002d2444d0309044d5403180306400c50a05910b04e031420103022050109019250700504041c95450041d900a5162444098204074003100c1134055601030200005104c1480340446184a864609 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 756468714 1250 756467464 756467473
    0x1605010506041a060a020a0b041505070807020309012015150d0515040602040b0705011a1e090c0d0510030c080c130b0a0b0c01020a09050906060406360305 68
    0x1824103210a898034010311100c074a4007001c102003d46801c0b0003906642034603104586884582d943c0300201c04800350760954214070065039080440301940111940428180f5140c1c420f818510070207503072401a1902ea80c1486007410b0542520080d0003d11a50441d0000464100b12051400703844081d0060711f10349100302002c40302e64030909286000320419944040200040b540f18500c1d4480300001034421141d0355020032000030b03500c840401070607400b03001d00d00016442d820303141425030729001c41c5403c42c01000f519801492852802e0342c0c0f4840b0303200540b081006655030040087d0076205032545584030794a820306009520311041e50303030b40560340704a1b8580101500c40c0e4119940e03040703a103511a80001ca42c00421420481d0f0b800a6403040c4000c0c1c1600d1405854042041c03054200421525050b980461840302050f80000e0b400004c03d403d51303442e44142021000304449101e1030040340709002003849901d03400f600385020039011800e864640710703982c1e00c0c0d4251082c07115414402610140b00c0e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 756469964 1250 756468714 756468721
    0xc0c05030304060f050a1b030509030c0414070507050a050a03090e0901090c150512070f030f14040611130609030c060219020114070611030f01060f0e0d0f0816050105 73
    0xd000049030b00740e900c20745036845003c0d044401101c160707021001e10810004444600740c20228940305035400c4038031a8590f240c07602c8504090510705a071000300248110304094415840c640725190454000d141072030026614606070600a01e82068104000c001c1e11902c115a414150712503950b100344c1300c8104c5031340b88030b0b124407548600f80e84290002402c2c406070500308000f04d40303240040c0074108900c2e04156007402c1000e042c00707090320001c641e024041070f055544503000e02d0349481105021801d41c1c6003000b40c101c07403825204c94a1402880107003100e17602c00d00118000d0300001541e0f004c0c9000e041e40541d5035298040102090160710080701c20f1130b02d1100c045450760000c10801070289a8580c0ba965518003900111010b0480e05031080d00b0010030070200021a040303000d00b651840d019001d04e07a40b810301115a00c0b190784141d200c0801c01000400c00c00303c081d4004925102c0103c1114541007013401c5040500b10701d4184003000308520300001d01c2c18aa0503035100480e001d140104020041c958 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 756471214 1250 756469964 756469969
    0x1101050702060f1213120c02010e101806020d1b031b03020a17070f0f150e010b130506010518040209642612180603091c0c0c05 56
    0x8010650050603c0c6d548020038400038891581c001c0031138014500310900040c0c3d000401e14042405042100090030b80e4241c844514110f801d4000800440c0300034034a04110101c000d010703166170003104039171181298000c02410b2190f5020b071010300300b0280c86048540580b5003c2e64070f4a80070400c45040d05c000450f49034540f80f04007519641d6400c000040450049980d0340041350400000071210054051480b07100008140305141043c0c0380c0394000141c030b290000c100440c0350040c1c03485100301e44c1000100406c070390b4000b007651140c190f02001e50f802118514005400f07030062803541d03504003004c46203d041922406500a102d03c0b082c0400307503510420411202d1610500b1441d0103000312403865a54104000401d10104504000032050021925158007050b00b038181130401010b020f90341c4448140e0b4800f80241c100942c0e05c900504d2408503507924402402c0440a40703184600f001000290640030288140320800005802ea400e082c4442c80d0080e0601143c4001580c00b44907542d000305075030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 756472464 1250 756471214 756471241
    0x60312021f09021e01020a0606090b031204080c09041103030706050f100b16020126040507090506030a110409020301090b0a14010e0c0a17070503250c1101050702060f12 74
    0x90f40241850020940680c2e100c0c959200704160b0342d045209410032100400d40910030707003000e40301900c4081140d122803001c261510f0001c010104103180c00308400c00c0b604da40041d0005c5941010313240c2540310380e514102801800841d510070740d010300001501c141005038543c00944aa544c2051814480d200c18248804441c01c9005903510054200070841105817190744101410303105240102c800480718110500d00d40d4101c1d0703900e42d010515814041005000d0002c030000d4140000d040102e4a03006000035920b0008440242404a00001c1020320703444030380141c882c41e81c0140c002c0c0304013890b514000340c00341c4045440300e07811494540343d8170001c00030200303490403a642e0a00f14040f5840b40c441c5541c0c954410f007084802c4c4011600070901074125607804a1040032140c0300c80d6241d203088002100c0f8800c5075928440440c040d240b1100d4503070b801c001046040381e0000d802c601c902e8481401a52a403089510117540907101145061164084000030119101403c074081c1040c1c8a103182003025 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 756473714 1250 756472464 756472481
    0x1624030e070b09060c0f0106050f0d0b01060c0602071b030204060902040506030420030f0d17010b07240f0e0c18040b040c0b030a02031005060c0a0b060301060312021f 73
    0x507040700200304442c0304044081c01400c000204121314180d0400401880e040d046860044907035100e1004010f6482d01041e0301c450050180c4050110090590758003116034014001c00b020311122010f1801440f000303905a44416074030526010050703101200103074006881d4401280300314244140492165818020b40d01200c00c040c1074182191180e55030711400414603000009654140c00b464042c595042103006c00c803c200c40041c008083c80450003d05d50007104403000e10180c0034000400091b98568110f1b0310881d009030b0000f441d46003180300e03000100301d9842402905420441d85003540a110b80c0500080811101210b03511031a40c424000703051007121413a0342d088500c3c130004006c07503000903401d42d006100c2c010300706c4c2c4542c848444040782d810980f4140012607001c070401ca0b076221580068400740c141100c001d4101291807680641c0d440c0211801407089a1980210b0491380303094001d00003443d0300800c0049145601c1c50001d60340d40848107483c0741c4010384054000007200c1882507922 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 756474820 1106 756473714 756473741
    0x90b0411030303011203051b0d051c05090c0d1e0312200a0309020301090b04061b03021e0c0a020a080c03121305010809162403 56
    0x40000c0010440c50203030b44100b0060102c01e15924814850070f505142a6039035040740610755804e0f8928a603850040c0c1f00d018190760616820802901e90690100032035400070b0f980d00341020640320255250301d081c0c2c008000070026410300103030312459035000b90184100d86506003142c1c0420110f1060a5002a00c148509080e102e46c502410358003a16101c040c0e000c0301c00b0180f521410348920151041415078400041c000c5490070741000c010640c12000c8450350749002d040050103014070128071000c0b94100100c00490358001d2094805003019841450910302e1001c0f5407d2040e48500c101c09040d00c14025040c0c0103a642e900300e0382c09408104c0c040c115001243c4145440c0c40c3e4124101c85040c0418001e900f80411b80c00000000c6501c00d103041c03045074540010b2241440082902141001503807407002c40e01d07001b440301c0d1501d05a50f50748a60b04030116035104904590104a1464 = true := by decide +kernel

theorem cover : BRFrame.Cov 756294964 756474820 := by
  have h0 := BRFrame.cov_init 756294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 756294964 ≤ n) (h2 : n < 756474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
