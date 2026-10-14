-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1473
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:09:20.428221+00:00
-- url     : https://prove2.me/submissions/5af36192-6aca-4922-ace0-9b2c52f84791

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 264748201 ≤ n < 264928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 264749451 1250 264748201 264748217
    0x105090a0803071103210603010c02100e1f0603120f0915110d020c030d05070f02040b010c060513150203040c030206030709080102040b03070f0507030804032d270501 73
    0x12841e080c005681010280c605810065400800381d41107800c410342c801050003000ba41301c024601c40104064104c00120300801180340025070183d80e80d48030034592003000d5102c2002d446d5200091100c82103001e5940c0302e803c078160a840100008003040d000840703000c03541c0c40d81002c05034400c0103204042003842d110900102d00348001c501d01c1015100c1241c042200007045150690b0080c041110449029002000f0356003143c0105410500952500c000300201480b50307901041800c152040d0064050b0390001c3e24050040c0100e45001e500d4401074150b034100f40c1804140b0f42220b4100c83c4a034021f108021a0030100b50840017a44010342d0080c0c011a0551001d0015140ca14025070300f15016080903603003541da07841c1c4103003aa005a48031214001c03011080054080d0403140d1502803a001e49007992400b1100e5501400d420405800601005440e500d03c80c03400200c0c000f01c4000e000a41c2c0c1022004071030304401003c56a21102c8007100410515100c1c5010b200d904080044e1380d0142c541d07003c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 264750701 1250 264749451 264749453
    0xc0803060d110315070906050f030a0e03070c030503070215120612030d180c090203101703070b0c071502040b04050d1a0f07030e0613030f0c2003060105030105090a 72
    0xc80046105840c0302c403000d44010040d50b000c0200c02944000802c00020500d00f0396005004030b00f06510000a00100304103c0c411400247d0031690300004c0c01c1c02c001810b890080c0401d296005030000140081f0f00c2c88004410301c071000000d0000700c0e108545d804202c28180842d0385460181003042c8014013544004503c00703142005164028201d4841180c0c105580310440d40183ca5081c2c0480401209013903042c001e10800581c030002814072444150b1540c00c243c0c1ca130351581e186030302c1084020305203469a05180c0809000303c8403210b410041d070ba451828240340c9400c8943c451607003118840001c06540b44401140c0c000d0fa0100d0b60944a81d50401c3d14280034040912400e010858000341c0b030b01711052203020311600860103202c071414820418a441c00c4060200e0b421203403200d84a6000404111222113460301c014a52a418500050355200006c026a80c489808a004202c0b26056901603410040c4000110074520220100c54181c1d03070706c500b854200d820944000ca095001060410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 264751951 1250 264750701 264750709
    0x90d090f1203270303030b0607050a0b04051006091b0309020f010e04020409090305030412090e0c22171e0307080903070b0a020c0109080c1807110109051c0c080306 72
    0x40c118040d060a5034855107000b020700c4441d160f19a4960010b01e2000107009159061080740c0070b6420903581d207480c2c440b4544881d9511041d2100041c59501104001404c11000f40700c2000280c401c10828846c0c0307a11490088050038498880d445454031941801201c44c0c441e0180c080f1681d005030248003d10121801191482d0b00d854113542c00540030000010824018400d048040d402992105c1d1a410a442e02c00300d60343c1a148601d0402030300710018084600d680030740503008580c40504542c1e810010540b03041107559440f400c660000300070400102c082d818a0403081c604480402d60b4041c100c2d03150150410030f070034489075a4552040c450540002e49400081c283c10300020200e0748007680e142400455944000d400d4401a08000000000740d604131380c1080160100101405400c05104080b6010040803c000b61400c506c0001103041207005003910400c41d407074000248148a800c0c1040d9179034140312103d000103c00c14400e002d164600c507121350983c282e0700508040c0f41d07403605c0c0104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 264753201 1250 264751951 264751979
    0xd060506010513030501020d060618151103030a06030506010b0703120509010207050601060c0209060d0f0b04080c0d02060907150f031a090403030e100606212003090d090f 75
    0x201d040c400100402140c224079a25000c0c001d621800c00941d441ca00c80d25038505684c86e83d400b100900010304c6000c0c018650300f06296040e100e00715210034034071051100c01c942420b4074046007091408004144840183d85070059026240610b04560b41030b42d0340c05000341030b0310844d40068002282c5401030f10580000340c00c0550050000c0e0009420418251106828a0400e0784608089090b401d580000c6003000040e099028a00b140c2001164107103803140e44201040309001040c0c0c00707500300041e040100c0207083d51607412605084036400d4100d454007075654041a81e100250340b144440005501c42c14800401d1003496994514008a080e0340301603010305151400303581e01000c050445c10442d00c41c2c00c80b41d8881d40c0642da01044401820b44401e0802100e25146003000b402c14809200c2d00d9008190b114000321010f80c030b001e000324440e5001c402000740e004141001c00c0c203c071034017100d9a036600196008000010130303102403904101068a1a8a5622440b2800c0300e4112080294412003501 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 264754451 1250 264753201 264753211
    0x1418040c030b011701110901120f09060612020111010207051e070b2a010501030206030612010b0303030901090c060201050f010911121603060b090607060b03100e010203061c020d0605 80
    0x12144403684035903402c1441c0d0803d0b04400341c14240006803c0002509000c0c50f00c81c440380c4100240380014480000f01682c0d044440c0c8406c564407109250314201844c0d000d2140d080e0488030411000c0c2c0c5640f8045441e007503643d016400100d030500340d41c5040c1e038180700f00d400d51076010000740340e04484a10841041204816004110b000c0c41000046201814004000807003144c10f1410906001d00982070300342441401800140c0e25100c010f000580310380b4100da80002048a003e0454518401e1171800b412402c80c0f03181d0140008418803400031015001004680d1040d11102000d0b52582e000b207080714411558500040c000c1001081521311a6211a00c1030003030034056460402c0c0c640d541e110f50802510711022545400b0b10308040f541d814441c0c400a8440c003084240303005181c100240c00382c0103401d40904880d0391102401895a002c008150084003011001d011501500700f156000f500200c0c0c5941c0107401860441c43c0803020040700c440b54a034001c00ba440d0418068445000420000704 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 264755701 1250 264754451 264754463
    0x40e03070c06092c22051203070305090a0506012c100503010516051b030c06010f030c1406160309171c030209010906050a0504030204020309031201141804 68
    0xc00e5001c100c03903803150005010941c4403d4030252501301001c16100d140f600000d041c90301c3d0801000c01d0b80d0b40700780c815001311315801460001c0701449405001000c20a0b401499031082900b406881000034018501c9280591070070880c40c0d84100d8010b0b01c461040e0001400360700000b0041c00324000c00c59200800c841d184070800d0f90b00d080e4801c40780b4150015a03001052812030b000c03c008500d024020990300865001d000560224580800307809801407080801046d10703810a03135000304e081001614020706008045420307a5a40d5641021070742c44c0c0e40030640780f00e9400500483c1011a1000c40101c94402034030051600204041d000e480350050761003241003000b00310700040e010080d07040b03c01c900485c15029019824607072840400142c07554444006060040c4064005a038018402a0880303040d41000f941d1100810812145842180c2000307601a1001c028025090000000b810030110240310022140e62100640c0391100c040817880c1e82c0c004029003800020200e00e60a064000348104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 264756951 1250 264755701 264755707
    0x1401030905280f050f010507092304022a010e1501060324090c1115060607050c090406021b0714060a020106090c021c0504050a03030e03100e241302040e03 68
    0xba4810f8040495208261403d038030005000c046100280701b80da411180380d040000465151280d101348420740161014401c0301521a00d5015499a0301160740c1c04401009684d006188015501c1121a040038980160362030a028032200010000700c042442e0031100c1065420f80c45d11404801030082c090b400c229030401000d080c0c11200e80d180c008230141c05c41800c0803074081c04140b1300521400042003d20002e40c0680e4540405444101c1d01f50342207072080d19243c0c0d542050b810320702c0c82e040070f5a1500760800c01200400003401a02d6010344003052006803204460541240400e98484141c09250080071181480340c2403490004010000c0091500021560356034900b500c500301d820303440405000d43c11896000306c4500c3c0b141c0c40054440e9117814a2824a81804042100003889003c010b090003401d124105087c0d8040104060101050301e041c0125820540d005481da00c80100c03501070060300451090080203403041240c41a0000c80000d10034802c0f0ba02008040c084209000e10b440c0020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 264758201 1250 264756951 264756953
    0x7030201020712050a12020403170325170f060901090c27050a12080a0c0c0816060207050103090f02090601050403022d0405040b15060405060a09140103090528 70
    0x4008482a01d02c0151070304da13254910828041e1983c01141c2d83c0c0350343e040c4104001c0c000210611a004020100040c4494880da00c000c00c01001001c10030310b00f2445440c90f90f4400b0900d5002c045205030011410315880307a40c8800c5818010035900351003182e4401803007070060148030459405100750212514040b40b045003d0a601000c100001e9144506c8040d00d0718140f0007400c01c048071000900080241c6148080c45840e1019207000d0704104c0410801c2602c0c0140600414084c60b901414200302628429042605a004080b4181c402e4101501079603100180c558042d01c50b03011101d81020042a8454542e82003090780e10006000e141405020b020100150312541481d092807100111300340a5141000303080451151001d1103d840303142007404100c005140c41c06802e0700494003070000120310052030001501070080760030843d04440c1c0892608505540041f0b150111140c69411b100030202d01e0004500352080c10b00c0281c001d82c005001001d03405081c4034501d20a01104c984501540e0785 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 264759451 1250 264758201 264758213
    0x1b09030618101e060e061008250203030604060519052701030807030e10051c0b060a030b09011a03160306030515090d03060e130303090203010606032708030c070302010207 75
    0x1029508084082004031032030b45110300c01c0d480507005d001036035480b5181820015040c1e0546144010400c070b080380c041000107940c0c03d041d005045500240107080328165030000d551380c2048076110310450074040d001450f810b00c5500c51a06010041c91170b00c0340740c200400e002d20420062080d400780c0340c0031880c0e40c944002001c1e955002e1441440c01c603940b40f500313040007081031080b40c180c144202e07110581c6120f80c60300401141c1841d80600c0300042d03244800b210040041140e080d503035400a01c001166203031258140d0184a0313010040b5481400350340c950b0005480d19142d84440401400104041500000d804400304495140d500c1d001c180c0585075681c290411000042d4002a0181c3c0018040d8119090011900c100e02074901081300c2441d081c05940c480380c010340202030340d001e4a6548030038103100360002035003941c0160007488000c1d80c50310001e00808aa810201400c1c900301400c1600100c52250740c51440e810207880c03802c6441c0c02c642e8a0140e0300840c411025507500f0050b400008031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 264760701 1250 264759451 264759461
    0x60f0c14091338030d0e01020a2301150302030604110a080d021e0d0c03030b210a0501050708040503030a0c0504120b01050306130305120406060b0d051b0903061810 72
    0x440d01104a09108418808080440d20010501c0401e0141018103d94900003640181c80c00c00d460a00554828900141d0404810789409440c40d02e4200c01128008954910094031900d038400811800c0c0b807403225085031118070f0200951680280f0040740102e80d881b03012070f404107402007194a4160ba03070074074185040f00c501c2a00d00540c0120040e800c04100b0a4040c401c14051030380a0203406018040003004040000401001e065440741507041c1511502c0c100c041d81d224141846000034030281c1303515525134948008440b10341c200000290518440c4400e1401242d010005608546034108017101030011400303504100401400002140301d2841c403e800442d01414060640394102024903003409002424000c2e1440d02031810720020341c3c80011612208401c02d503805e00c50700c03146040b0002e8205a480841e9089000c40d0243c900d0903560300160003000565a40d041c1082001d40c074001078001c8102440d41a0080000509040c88040d0207078080d0810f001a10071010404000b807003261 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 264761951 1250 264760701 264760721
    0x901060509041415060d0b040302010e030c031b01090c180908070f020f06040f0e1801290901051c060f1505030601080109120c060204050a0b07060f0c140913 69
    0x3c0e02c540e02c448680c060a02000710301d00d030354620000840c81c141012401200c41140010184010040050140f5200394804094900603009996030b07040e515a030f8a80c0e0f504003903080c0b80040702912411903001d0051066458150380607404503642840e014800e541c240110700100f018585a080b40d07000030302e50400030080244610301d200000782881c014003440a8620300b941c1e0044c28100014407249091078114411034000802681d884d64843c2c401c0705030328100313003101690740d03090075a231280c0c001030814891520503550480c5d120210004003004aa11420720403190024030b07000901070f200254131380b4000201d00515020a8100c11810340c0f40c101c644248a40074412690402448245400c1c80400e00600d8007000a00c20107050f6146c43d142d440010031a03c0500203138200d15010007101d41c040c0e84c003c000041c5951a100d6481c0f0922100e90300041c811a0481e00d00510000da124141c4102000c11400342d070340700d00c191400e00e40000c60b0390007004400e51010400c401c4140c50086801819009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 264763201 1250 264761951 264761963
    0x8190512040e040b09060103020f10021c020f060a1503080a0e0a0915090218040c021908030106030b06190e0a0f090b04050c04030b04110a0b0c01150f060203040e090106050904 77
    0x14074050601c04084131004e0286511a00480010405071380c0e10b0300d403003035003007400c44101382001014101680781036440808120b01d420780070ba640c5100c030740120310401c43ca068641541c0007039503030f80c07031103821100145486aa04041004180007060b0090041c0c0200c040702d0070070040c4082c81100042c8000070942c80024603545035400400039502151000008011140c004d60910070540341e4841039040e50340e506400307140d64004030010035100b0070002202580150f02c6140c04002d40c140401264000d0107505c1c0840e01701b201703003092428404215901036150002c7d880c0c054503464000c6900d1031041030001c0c0c0c025907960740410308000b00ca1082004020400e00080d0700c120040502007a2180248105000d0301c05002c2007000c200c07908061540140c1c0480300c0040c130340410000801c0000290840c1101d0140414002c1c42010f0550200d0b5540080c5009056102d0717032071034400c0081e400d80c0660b00040e00140000c0084002404005412030506000840c1458454000c038141d01e80841d030035948 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 264764451 1250 264763201 264763229
    0xf0304150c050f07020d030c14010c02072418050301020d02040306050606030c0f09011e020f060108210309071e14030109030f08060d021f0206100819051204 69
    0x204240d54459024048180c0c100726080c841c443c1c00c80c2c003280c003401601030300660b030381c110010415201e1007000c20b98641c00700410152103002c2242c0c6000f0b0914844440140c030030b003140070130780c100200c211441508001440c03d807240003070141200d450915036031400710130010880201c1c0c2c03541c0c20f002401c844200c150005851f10300d0b60801a09a581c003030700180c0520002c00034800d82d42d000c802100c0300e15007084019a80c030180c0d0030040b145440103449504901c03000c040d1045c4000d5022840d910002c20040859101c2d0f42c03594003440d00c4071890044010907040c040d11110040003038070f02a5a1100d0310703109a4201c240e542c1958205200721403090400c0341d119203130a11030050307001e0048213000c8081d0000c110442d001c5c3e90140828000032109030610004c04005525076546072115200340d540940a0207038001104100e681103021040c1c00000740c0038031030000c1c17542800b2480241c2140d1703131140100495003241000080c804103450060b225070045422901221020400500c000d010600940380 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 264765701 1250 264764451 264764483
    0x2090117160b0a0e010c17071a0403020a1202070b160203063d030204020a1e0f17061c03110c09040c0b2805030103020a0806040c05010809070302180609090604170f0f0304 75
    0x10b2780644050200e508044442403001084e80003503410a00ca0b80003440c1615022802026460114503522000c000840010b1041030010300444016040303100340c1c101c40c083d8403100320b504009a00c0419076619100c0442c10f502080440b00c40030784020201c0f003104404143c0b20307000328080c1e0340110400008038070454040c2104020413103415070b0a40042c5044200e50702240e070700800d8116030855000100010a001c00d0050741d410b210145202c45401110942031614580503091341c50204000405001c0c11a20300600e05080d940c2c0707445140d0122041c1207003810701e1460a90341d0401e01d4031760302c00c4507003180e2419010400c9201d00c0c80010607481d040d4496240d84104a0002e00ea070704541000c0d0007280911000400c802c81742e805440b02400c05102682e201645a464140d2561010398440308040d0020510300314109003078010402507416070410750352115000c1c0c1d80d000907a00100036032081840c1614404041019012400c000803100d454094040c0d42420240c01c10b072000d583c07031101559128 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 264766951 1250 264765701 264765713
    0x16140304260a0c0b070e0d030e011d0d02040c030216050f160b09040c03020c010f200a050307030504020a030f050606100305070e0111010902090117160b0a0e010c1707 73
    0x20540700428503458a48840850002c240d500c0100d0020300103000700000c92a0a07010700c3d08449444030150501c00c90302c1c840d060042c0308100c8000d140e40410b4100c1484c4c413500844503040c03400e0b40c1e030142c024004003080b40c2c02d0000030200c00b03040d8010940d090204000c0e0a901700301109030240910000c1c4800c4c03030803505041c206501810209130845a10304100040d408103c1603a1410000300c8000500c44503a0307100b038002c1d11900070340f0b1505503e803074211312030f0400503841020b1080102129400842c0f07908843c812038440c40c01040e02040040c000501640d129411281d40316102500364041c00e40e50b0350300d9117501c00700750b031007201c0c190000001c002d69402c04501c00600560140341c20300a074240320f0f102400848107800258100202c01849180120007504180003046c0e004e0001c0000d582d5522821760209450012049075004402c2c641080000c501081400c0da100c01c2d107002e2070509054411f50714030380300c24140c60500424021032000324440c96181d400c43c42d00704511651f81d000c14a00340f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 264768201 1250 264766951 264767003
    0xd05010b070c0b09090a0b0f030f151311060a05040803040605030a0e01050402010813020114181005040305070e06041e020a09091e021b06010602011a03010902010816140304 76
    0x2030f0010342d007803011840641c0e48140181d0446074011001a1818058021855039410001c51039014170604006070300c0c841c80014207005000c00b10782d410001d0346815505402010854401400503410f0a5004a5920b0080300800043d00e0710f007009032a0a6131848840d065030866403101c40411404810010145c5180c010405144104802041513280c2a40042c3c202d40d0003402c1d005500c40311400030801c59000f0039000b644a8800305000d41c42e07000e07098110400301c05210f84680100101d860b504003550086050300c2c150faa04c100940451410416900d1181c14001d00156100c0d03212410407410501c2c0600490501c2c2440342c000da80c5551501018107140c141d40e03c031501b040e14201d12480904c0428040c407114407580c000243c0d80750300c070340c032610b07590703201c80d170260405001d82d1000240b10341e0150710040d104c40c001c1c441c109420f0b035444100b500302c400e04000a03004c26140c600150a20740e6032010286c4a000300d007450b080408000030905855001114221801d810320f0800c080c0d480c182d0311032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 264769451 1250 264768201 264768209
    0xb0709090b09180a061a0a050102060103151806020d0506091b03010308030402270f0109020a0e220603030804110901080a0b0709121b0503060702030405090c0d05010b070c 75
    0x1040c040180c5420100d501480000d1030100c0d0348640f1000882c1c00394083c8082c22600e9002401806000401d4540e400a000321150b6280f0881c03602400141c3e550020603a18122900100f0707115a500280f041c00010700400c0c200d003e10142402c0c541c02c00181c03644050658181441c00005a5241210911003844009041c0d102040520a0608481c02d00070f021641502d50048409450f81c54600c0841d9100c5500884407000c0e200008694440702d61100250b8455003407060080300f566a0345428108078403d0400100004001c00d0300c1031443d08000700841e44050440400e070081070010400001180e0194000301c000a000006100130f010031400105603440c42211060380551404049540ea040800c00080050f0b40004c001808603010303660030001400d00b0780c0e400012442c40d1501c0054a118558070307078001c40b01c2002c00b1405040004d1240c0c8103480c02d40066280a0a1004011840c44018910006484100514070508404d4040e550003000403061a944079442460001420591504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 264770701 1250 264769451 264769469
    0x60c010b040609020f07080904020c031c0b040c1409311433040906090312060608070309060204050d03090f0b16060506061b030301090e0609061b070f0b0709 69
    0x4100c5d680300d9560464011a910280c8036645082580129010b0700901090030100d00020130000b060201010340030083c405148400c05c40d69558004000864401003802c00016030700cc06262095108034004107294900105a06007103201c1007203100d550014410342c02d14040f02c0e00085181c800f003034041c104e070440041809180c00e241103411460042107442e0041350200720b000c10082403028403000c81803500d0014109002901540c2000e00160020b0041200050703141c0c0300810304903000c0d22880050714140c1d9101400750b1a40e0608601500441500307440003a420000043d082d621802940c03105486600c1d912040c51410303403190341100940c1c1c80b100022404210300c170b405034868004640038543c000d10001c2d050b244c031804130701240945041d4a4801000c4034501c10381d1180040914101e07020030a0602802c094029038a46640054030b82c440701354001b00124120540900f0b001010804038075500341000041e8036a00f400c00c071420300c2502d501c500f503818031428aa110000c3c50240003042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 264771951 1250 264770701 264770707
    0x80c01090e0604020304030903050a0b06130e100f0f06080d09080f0c0d0c030614010323151317181c151805010b04050a1104060305060f060c010b04060902 68
    0x1959641075000000c00540c07041e903000001508160282a140c0c0145410004448941c612890010324440c8192070f050301c00c100c01d905410040340a8001c11045c1079540e00074094204020601d10080c01038070715208000350b12000d1a8200c0d54040c89000010a601d100038405504041e202401d410301c19001445950001400b45100075000202410044001e03200c1a500007040c1c2804140c0fa10241c10091483d401c00d0850000c07000e0410342181624000c8031180008060508050601010103400c25030a4126903a26008070701d0401c40e00b54080d07024080c0030542c0200d03650b86450010500d4080300011004584030300c1c9010921000e00c40420240c4901104045691000070f0114401c00000d00c944a034402c4d152080e55550894030580104034500054074041b441c10a010700b404034031190140c3d25240004900302194003844100001c0c0d00b03525850107041081c214081c0c140244031642040c28801d00403042e072103100007408541e10040001820030044030411094a015038040902c881c018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 264773201 1250 264771951 264771959
    0x120309041b140c010f0509010903031506090501180801020c0604050d0f0905040e07081e0c0411040b0d060503150901140702120a0207051002030304030f030612060b28080c0109 77
    0x102c1d00c0002c1c84058003a140c0c807030301c01d002010b015041103202c1005050404d410300204e80415004001280d100303407003e01c40150801d2001910300541d00c9071000165040b68104582d501031450341010242e00000300f01c0c0280c0300e412150a81e400304840b843c0587c80f880421041c000d0034031003000c00800034500f503107446800ba0401024603009d030140b42c1c8100d41ea40c02100c0c40c84810095000140074a10507104604003007440004115015820b0091501488010f0021441d00d071040310039104101c510f05040c00d0030410a0300b000e030423034202c449100e561040c5c0405c030755508119000c480d0324140b400038907602d000b8803240e00391801d85030350141a490540600c1a030365004078003e6000c3d0303c211041d0791600d200b014100d24048450f4040b41d0010800400c1380075881d4080001d500c110b020b41c40d929001083e070301089044806501c00c440098003409500d10001d00b00c0d8001d43d0341d41c1c07801402600c80c4803003070031211901c4071092410901c10105400400c001c01d806d103c0340e4080754090070038028484c50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 264774451 1250 264773201 264773207
    0x1020a02060c0c0312150301110f041e120c17010911091515120106020d0f0c0204111804050108030a051b07030c08060907090204031509020f120309041b 67
    0x1025190b0116514085501d030041035041082c0c80b0341d802401c4c180311309802c3c40024146200c070322480f56402942400078201d240740300c440071200c0001d000c0e00c0c00e03890289000ca44108a0a29030b41080101001401c0003604034060b101483d0740d035002c1e0700820b403001d26190500038404140d400c041e009906140c1888040740c0716100c07a030303080c1c8400e8a882041e5524a00d00d0512401d5105082d40d02500b001c81e11120201d4400280000540c60700100d201c5980303641050341e5030300951201d01c0016114002c40d814041c1b003100040031807440503001003580a03140f016110590041622410321220200f260201403601e80191801400f260b00510300cac042907a8001040b501c6013000e141d82030100706100304030f030039010800c90000b5034024001d103080d107031107008040d00d44005a0780b40301c42d4850800c01249410441c402c840484ea400032085000284071a6048040c10001e803090b80c0c49003504214032490340f1107203100d808141c5042c0203141c0d240032810412044514100059609451b0b2200110034950 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 264775701 1250 264774451 264774463
    0x129012003030406200a030506190302150d02090d030e0301050a05130b1b160308060a06091e09060603020a03050c070506040b220309170a080a0507050a020a030c06080901020a02 78
    0x18002a0200d205800d1500c5c4180d0302001080100c0c841000003000c45030594180d1140c0d01030361003100c50b10454aa80740c10f41a80070580c0c000a50b011040b00024008008901d00178150f03554040e40260410350300100107030000058030000d40c04140750044402071440c1c20301c50140d021003000c1c07003080a070800382c10000b0ba0112801004001c045490007084611440f2a0410310600c04845003d942c2d40521048003440d02400000b10041117008011403001c1c03800700c0c0207005860f00355641c0c040d90b5140050148000c2c0d46c08070310305030040811202142c0c1c05168040c1d034001c0e207240d880240c1c0d02c003941034000b42181ea0040402145030020700ca1100007030400725403a90000e800103075405a40c0c131080c055160000a032032014050240300c4500358101500a01000304803040c00c0b003c000c1c50084900e0094485080c45001000001d040084001903800f60000d0300c0200e000788100d440100495010913803014060304240c03030032410484d041000c1d5600c2240282e0003843d000c025070a01851000182da02c1d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 264776951 1250 264775701 264775703
    0xf050306060708040306060b0c1c14160c150210060315020906040e040f0c060e18071803060506190806041203111305030d0306060c11010201290120030304 68
    0x20800059040500040400743c1d001703035421400c2000410b58030000e0120550103160030121031700922070717007070010244400e92040c600081d0700d4088103001100c03400707a01580030300041403080e0000303000700c404076450400b540050700020f0b00080d01d08a1600010345080002504802e0711400d280c0c041c00096491103110b9080038040300301680320f91001d40019440c0c002e81e000080360386405410402805400b00054010034015030004030070b079480c0d60085840340e503814019034020010380c0b802440600c0700070360a0f82c031102519004080c80c0500310385446a5015038820b17200b039500c07241030145034540342240d17a50540da074012a4107443e207030411564032072000500c041c2c18022541c43c3d00f1707080c40c0250052a11341003245103290f0764030a26000c98075030ba02507015890180c415000504d65090181c8102c106075039554031200e03000c004542d0b4605041c0d09903049503046548402050300c0401000780000100c903100113850f0014202400010821810759640c000c0ba00c03d44410200854000b204494001d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 264778201 1250 264776951 264776959
    0xf060f0a09150506030703090c050406051815030a2105070201080403031109150712092702210f0702060f070309020d05030d1d07150f0201150e160f050306 68
    0x48102d0581c01120580541c0a03507003290000040007100e0383e01d0341c0010700003032040040404142e110400d01c01110319074003840c1d42188004010b4580442901001a40041c200214140f12107240c40441c0c141075003018105c0b0098070850502c1980204524844902a40da180c0709041040b5070700000d0107a400034202409050751601d203013124112a42c203e80d400c650140c0200100c2c3c92842c0b80704080c0d0702001095660300c0b20192a445801d2103541c0c440101c030003204a40d0081d41440c400d40601031841d010314410558204400d5101892452034111348500d200c01801486c6040016541c02030001000441107400000070014680e0f55524565048407481c580024207581f54400b145a01440c1e0300c3c007078014440818000315089a80d00704190309407100019020b10307405051401d035201e06e103000303aa80f013205990b05160a030380715030015200225184004200300d501c81d540804002c1a0f44c00441c0b50030b0052013000a0300c401c01c410f0702051009890118085d440c03603e001040341c04094032240c46 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 264779451 1250 264778201 264778211
    0x90f0b0a020d110f0706080a0b0409030504090c12050903030108100e1e0309040e0f0c0609060a050906071a0103141b060903010f0203010b070309060c1101030b060d05040b0f060f0a09 80
    0x5680b0003005034100401c0303504e04440030a900d500300079101c2002180c14061a60402c3d100d01a41c0c10316008500c0280d516490781400c00d4205241e0001a1820780301c0c0008200c02101040009400e501515014510003c055943c1e03505151120f4103080c03802020150f00b50030300c40700190410000907800160385841d40b190b000c2801c6241094154407600c0305035503001d1305250b2048954600811000f590b2803a82c070803a1045101c510034041c65000b2039105541c03004045c8130034450280280002c1c01c003990018406441c0c0300060340e61074034015035078a080c84091807500c011b00030050141415558072510760f0040090080c0600c441301402c1e00a0b04040c0103550200d40c9040c3e0343c801b50040c0d0301512503080155202c0d03845540c41e84140d04100c1c2c056000800f401400986903004008403001c2c15040011311560501190040d40940922141c540e041f4000b0800e8041d5070107180724031070040b03200c2c0d40010514180319990100c1503101030841da10408a0f101e480100e51b0350b429054080380c2c2883c2012031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 264780701 1250 264779451 264779477
    0x1305061b120c0c031201060818100b03031c02070515011211211b061c0b0a09050a05040c0e0603030403111801120c0614070807050c040606090f0b0a020d 67
    0x556800740300d503d0001c0d03100100da10118103948011250507140c80e83d944443d5962800580d880d00001c000700c100780da80010700710400151140c2c007c4007200e000902282d18003103056041036207211006900c0302544d42c0c0031031070404010040c81030303111201031415204203950400506c3e040054802c44000c0c41582d8090f00c440c6162036094080005c0801003601d24402c8000c01c85442d2207600765003100c810005291400c0034940f42100c00c0d26808807071414ac00480807009420340008142540c0010703030100a2000000b010203450180c2d900c108190035004c42d19080524060b07403c0105500300c22140a5408100411602e000007950300700d0340c2000011002d0200c020114044070b1b11400700c80255010000081001080c504155900f688034076100610143d8130f001c1101c0203a1811005170703c42c1c104100f41c2000c5020800078201843c050015a100301002e40d0000701242c00c0303039009802250340800100301d08050491488018201c44501620381550094000c1d01c441007541c5003018031210000c404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 264781951 1250 264780701 264780721
    0x70801050127140c04080106050619200102031504050a14130c05091005010f02010b031e0f01060f060f030504050c04110d09050615010f020a080c0f01051305061b12 72
    0x1c80d003031401010f91800d0038800c81403141c940c0140192881c660078048005460304180044031801c003580c510038070145800281c03c4419040300c407003100720202c1140c007841c0d9520080c40114080c0d00466028036540d00e00800b800261030008118080342c03848d20341007a003140e5031172030110f601ca07802c4802c1c08000d11261074584003508443e084181c008980508020607000c092903070b41c00b0340d4802d0321800004103000b0812400ea850444c03807942c054001c00302c02d00300118441a95070211b203001d41030311500c0c605620700900f1180c141c0d100c0c0e240300c4404501000441d0304854001b450740e1003840c0500c41881d041c1c451070350318082d000c00d03e0b009070340d00c4441d9030195868070705454440700e840f6000e118269940c1859995003200740c40c0326011201d01c101c0b03145258000c0384203014258190b005409400d07446d45807800380c2e82010414002a0080784902c54101c5c0c030a1069911032484e4003c03a080807002403c2803072800340e0040100380f18083c482080703010301c1e04a409071400500001801c07042c9642d25940c0c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 264783201 1250 264781951 264781961
    0x190b0105071b050312040305030a051c020309011d01110f07030c02031c1403010501020d03050703181a010b090616020a030c030605060f0906010f051602061b070801050127 75
    0x42d00c01c40b001510303010031a40840750042222022022607104100e14501117500d0300c181d11006103103030710801200044074058070244c0019402d150000170001030902c3c00200380d0b44103e032281b01c2c9954030100f4140813010180c1e01c00e102e0900030002c101d80403400401130340078403071348040415520010601c1c004152081c004001c19a41c003030103640b50900340050403a601e108070001c103400300707050030600081c11081400727503030485005074001c141402468909400414000d03280408041d200d10650040d03034100035450382403502c5151200544007104100102481c01a088622501001c22801680e0b565840507500d001c4001749860000840910010340c4120290340003d10340d03405014004140201036000d10321840040d90300c034116a115000304030004800b02c65850214402e24460840f907071160300030703143c120400b0402c0402180f403900080c5098000140e08000640c16805503c0c0c8079034280603c000500c143d5000307100075414004041c500b10400d02610041e4440b0f440003075a580c2c5507402c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 264784451 1250 264783201 264783203
    0x270a05010c09060305150109030b040c23010e04051e1801140402040f050f0106210e0a0c14090406020a030f0c020f07080a0b01030602031911090a0e190b010507 70
    0x70400762001e600080d209280d148102c0012038500310006881e052201c0b0001204001652a0700140d41540e0f071b10091584043d10666412410b840080380500100c50344840203c803c2124a0a20209400061003180c02c941800e0080b0706110a20120000d070f48540c62102809640540d0f290f580d8036000416029002a114080c0d800c003101030200700b29480803076000710b00989040c4070410f944445201521010340d905d0040e036040200400c42544030f801e2840e041d01c41210540c15058402c6120b10540d1500901d1300000e401c070902d810104420844c0c1c2400400c4e07420320303e841c04944440050440315004001030803490700083c1c2c1d81c0b2800c2c401e5002c0e500400c0034010401c50380031500d10080da10381080326024624481c144000c9600d40e00018050602540312036040a0741c4c2c03c42ea42e20000e500040d1440c07030b199280d406101c1c01e40200e8084c40c024007440361a8152601c00500030042101c81651104200241c101c05020849030b07004031704545002000301c007285001c040c3c0f0040700c8a2103000c00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 264785701 1250 264784451 264784453
    0x10c0807050319080c03040510050a060b030903030709050d05060105130209190503010606110a0602070501270c061707181a0d0608010615030c051605061806270a05 72
    0xf4054040799400303c10000d440000341d035912001d40c0c445290181c2840180c40c040e0283d4011703010f2050b00c0200e5044154000d1f802140810303040c0e03031424510910341068807a540a60000310401c0300b916403140001c0300500003111030704001d84040c4c03aa1901c60806000740b60203840103802c0c1600e0448503070112a0030b04409422141400f81f01c8020b101c1c9440b160007614425400c2c00300001c1d84621803480c1d401c0c1c55100340c0180a45500540d20b034802588545011140355480e081c0701c0d02450340c251402a100c07044582c0325a104103161501c0c0001e20201d81008003401040c8034017202d229109040d95a00a10900b0480320007a130b0702400760224034150303000302c160406549000410250180140582c3c3c0d2903840c06100c2591140c000e2402e895150003005c5002c1014200c80c242c280c481e0f0410100051142007162070540941001c91550b0414a41900c0c60b504c96400c3c4181382c00c800e40209014030070b460242115003804807460b85075208500500201d1000c0214005100c981400140b02c4194800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 264786951 1250 264785701 264785707
    0x2010c1203060b0a111e070e131b08010f051b03060d2316051c061e0227011b060605030a0b01030b07020601080a030327110418080405010c08070503 65
    0xb90081c185021028003140c2402a994890002e284c81506d0040c0c62200034060841103060918800791404c00419228211140c1281c01d8082a041311042001c03210b4032690603891400c1c52001400c0d1110031001380b00389490801049204405018540300c0c0310204812184d890b1103020004a11401d8408003a101141900070800e4a0605d10f10381c40c02ca00c1d10b0829251a50305a0000034050206132045503000707021540040300c110041e81060b03d61a01c5000c1c00181d030729449079440860038142d210500216070000c5c107002c1400c100d180502080d40a07002c1c0e500214000c00000f013501c40441c4624460100e0381e158081040310b1504148003401014048616050007410041d100410070702c801d40e030103e2040040752640384003058450581d00040e0043c04bc02c200c90b031f400c03402001f007580300303a404003000b5468079480500890442d42c480e000714820541d00008608000c00c549a400184c5110a40b1000d240300144e0180181e0301140d0013420044065003250a00c002c20784182000289640000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 264788201 1250 264786951 264786967
    0x11030d0203090f09060f090402011b03020c0a0b0a0f14070f110901080a0f0f0221100f06032d0804030c030b01150203030a1d030a0e0909070302010c1203060b 69
    0x90b01d0070050456810350200c401e0020303c000380006039403003a040b406200303442d011401e01d51120740d04144185044400060714142c0036207030030903598080f0300681096180b0102d5150881122000c1c02103012211b241262801c03020f0310b500c943c50140420700062400000340c0701101d07002ea881c099000303c4040341d2603001e49020010490118541c61080e90319600100e81c411001a008142c103600c248085680c2596845070021480f070907104070713441004c60010708424984040710701c203902e003884000c048200d50090000b003615019072004002070300d050b4080000c60b010209001d40e00d0040e04610090a80002080c2a42295842c0c00350000c503000500104114000b00c10380d0840c1d00032101c0600c82e036203500f0007803056081c0c0c541ca5801640308ac800324400a519030b100b0f000741640c40e64a400140c4200d550a411740e0032807402c0c41c022510004402d0850300740400e0700e0b588409404040c00b0000e00b5940041c1100031348040180a9030311503040064050b0090f402070015148408050383c81e0084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 264789451 1250 264788201 264788203
    0x70507230f0130021306020c0303040902090402040906060201020c070512030a120615021b040203040c03140f060705040302090105150703110106081005160c1707021305101d0403091211030d02 84
    0x2c0c80305c0c01c0018030204002007a0740b0110ba80200c1110080146150602c1d250b0400f001e50000f880450780b290342004001030b40c0c00f19204230401460b00d0780001d41c5802482c1c040c607052003959842180500000c0481c0e5020310300c00300403103c20900344d09112400480e8045c0e4074004040f550800140a1030341d013049424150005807001400192000c07444480d4802018481a4041650b000f4860340d02c03003500b40002600c2c0e1480003124001081243c28070000718004525140c4155070042c08544009400c1c400c0d4186007500300d014144c240c0e032032200c400e24012002124030440001404110302c440065078010001c0d001a801410507100300c403500025080300900916042d145500449241000540d102c0e0240d41d02c08a0241c00c1280e07951070080c1c00da1603151582c001082280e000c4460780150711607606910825000303c0741c1c2c5036410286800c20903d103054661000e841500e1f01410810030002030740c44822030f010b81f0010641204500303030740d00d4100c030000060308550b645400b803074544841060f8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 264790701 1250 264789451 264789457
    0x3290703020a03090b011e091a01030b04020702090114030106091a0d02030f0d0822031d01021612020306070819110904090311010c09300206070507230f013002 70
    0x4007c005080c1c0e40d5540d188082140e1404c03402d8001a01544100c0c10203601079400b64401d03101c05003000d0b181460720b90000c3c10500c0260004811400e2800f004612401d00b4072845c030140c045150300700800c0f8101c40300c6820714020090030b20711564642c0c001504544060010040705036a001c1103030044e13019404042c22007203044958040500544d5441540d0304c141203100c083c51600350b2901c0500d400c0310415441400e4002c1d04040c1548100c04050fa002d503580386007040103080500c0c0c6c0c10b00210840c41014281140a05500c5c20007402106101e48071036001c108881d022452a0000385011001260b55150f0180001c0347d544180f8028001c014180c1001422110000b9800200441e40c4040015103001078a030107400810551000e01c1078920700942d0741760710300c000480510749681c000341d400203023140d20900044a8a402c000000c00400745141c00d064100740c8900d40c0480920b5103003012a10341e000000407181003203080319003c035a85c009440c4070900720404c10000070114440507070740c201a45c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 264791951 1250 264790701 264790739
    0x9020d080a12111209010216050a0c06020c01091203020a14030a020124090b0a15120507170703021c1b080f010f1a0d0504030903290703020a03090b01 66
    0x1520705101c0c0c2c0c00000c0512030720415102100f103460629102aa100110700b00091403c000c940d801c100710104c880840d0316003440d10348a40000c10300b20a1034a001c0000100700c1c2e200700c0c04d5510262070384203c0da030060325440996140c0742c1c080c3d559285a0a04130702d0031400400280181084003003803050003001100038520f0601940017480000d4880007607480c0601310510481003a00084414003a01c02c03a50000b880c40f0300c004001c1030b4603a845401401040e1003418807180440d4403004402c92034070a034001d06501008074103000203074403012000c0c3c607075140f0020b0506d810164006031511620404c2922010820b000138010005242c6c4202d04000384905460b00b0008102e0700030004a041140c0142c5d14140c0e41c10f1004030305114585444610100008012007181280c05d20101200800f20321a0904c201c4c041c1d075600601e14a9070074030701001a004c8004407007100c01080080390032001d000302250803140a02d001640e910503044210300030072810301c000700880d04c6080001a00c0c042d50703203520038030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 264793201 1250 264791951 264791957
    0xa0e27030909011205192a0b0c01020310060503090c0d2406090605090402031507021510140f0906060306011812030e0901150c03050c0609060709050111100203090109020d080a 77
    0x1415010081000081000b48018290802c1c109001f85080c112041d0021105580c0b114451142c0c50301080fa9a80d0454104203079269404010454050040482e00004203181c0c14800c0c590700380200c80c42d407102211104940520900c1551608110a11000c0c1107114044240c00c89021100007a18018202d544542203a45041c0074011903d460b040d400c00d4029a4000c1c000d003450101d80f18401c04600c8020045030130340c001e120703c20a4250311101440e02c1003980840900c0101d013492507840d041006490090702072007a0342074040e41d94071900e2a103a08110304455107600d903500c080040340c5854007503030700c1219604900d1001842031222148aa0040e206c1d440d01c07066400d94800f1700001080901c80e100d810710101208141c600d0182210075130290003481c10514002d0703c0052685004000d0b40c01c00810780c01007003002003860703001d49468003030202460b01a86821003142c1c0c60b6510143c01ca8800ea20a0303001000c03e022140075400400b00d01d502815800308200c3e54204062550860100074000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 264794451 1250 264793201 264793213
    0xd0305090d0503270d020c0109121a061c03020109020f0f0901060c0812092d0d0e041401030803150a0308040909030921020a0e27030909011205 63
    0x10300002060840c90341d0350681c1c8050443c0d5400d6040400d4844030700c45000309600c0e650060040784000c0c01039420b015000c0d0000e1604c0c408100004040c2c1000f580300410704d407180525000000d40d550700454014070990400d540270b440e42000117030f01040040c041503840c54040c12417810181c0641000600d180200c80900c245041001400f8000c90406400c55100017034000500c9082e0043c0284104140200d9280e41040e03c1c0c440c1e400309644080d81e1882d407030341c032411740c0521140c41d110180300c0e84c0502e4440d41d0b0500f20402015a9201e101c24102010300036046464041070700c9581c8001c0c580c082520355085c0c3c43d607680c203001d2220391003500e40c84041519862145a43c1c02e06a04020440364805002441c06250074000b9004201040c1c3c21030410861074800914060305d0640800b0700d02c81c01d20000000419441004254002035000d840c48028503001c200950040303203c0b6014180c420581803021180c00a50542548140c6800c15800705680c0c0012a098000d4134138006006e100c0c80481d82 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 264795701 1250 264794451 264794461
    0x60c060b0904020604030206030405012c0d020c0102102d0209030601060207121205120f150901031106070311070b04140303070f061503020406090905061006092907050d0305 76
    0x10070022180030b900300318200020001810070000840d44280144000608000b1108010070004404901d440c40121720030311030794980c0c00a010544801d29a400100080028103001035121210001301d0315aa50380c50043c0c101e1512641e0015410a1403e5200c408102d05d90300b2880080d041420749500a1040c40000b0445900002e02c081c141c81d92a010a880840259622104580c1c016503110422400b8041c0c80c0c0310000a82c0b0642c00b811075400c0c031502601d0700c10420300300340f510308602501c00c0d81204010404105084a01d540c07101c0207445041e035420310303401e00740c907a2611200c2441c40d41c4203041d00000c2008504000d482554482c0030240001e5003160b08160b40d070301179402c0141072139007607106500001e821035000d03041d0081079820708108140c4e00d40005046a15a6010314407840d110100c18041040600445900c11144080c008025003042401401504603004004002801d05801c03881d032a51160850f011000713200d8169543c0e8000e2501a841d018611f1803a4007103420903011403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 264796951 1250 264795701 264795709
    0x50a1109070203030f07050904141506071a1807030501091104091509050c1306140a030c03030c030c0b090c0103060b18010315090c110c060301150c030315060c060b 72
    0xd40101c90a03401103056844e540c00103524040080d01c1d190601100300032541658a07503004205601003440490b1b8014603101c2c2d0b80010031415052007500c9228200501d100203030328401d03052000340c10280610340b10307914841210b000070003441400c2001c2c0300b003540c004204001504140c10952040303204450284040d030a001c244c0703400041c000c01042e0309401d00071032a07072542d00103c16940201c044411030078209001c00c1d45e100c00c7c002e080d4a1580c4a03c07050200b9002c13000040b0440b8030954007601090b02d903489402c000a00d5000c0207080180110285052501c02d11188450b15082865074059092041c1d245648031140b800c3c0714007189c2440780000700c90700130380c098030104201c0030f0100701c1c0e01c503428004500070041406029840c240542011845038a28401d01c90301d994181c4a0003910710603804054a060045204140b00c1d04c41000140600a210800b0142c580e281d07043c0b0000d003100504e410340c0a040c0e0070b1210064111400c0000813015441007440c8249401100c04100302c0190074148 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 264798201 1250 264796951 264796969
    0x314010f0912031a060301090614030c0a030803180102030106050405130911100c120521150103020705031e0310080c09060105072303070b06040902090a050c0f07050a11 74
    0x34004250303082a40109900a0b0015400c4d131a07060f00820000210a00007000782d0803c1e00312000c00c0d03544101c148501c8030b00102e00300c6e1510b021401021180e26600004203840d2050000410b400c0002c00411411864002d180303c80d1200300009540b690784032031004080385c00c03034400c0922600340340d031881900200a01c680001280c220355a400310007142d4050015030b03d0700a80c00d0080101c1100c084001c14900c000080590185903036403660f030358518090210091094095001c1085004d0501c081c12030986002081441d00303003005a2120351905089003540a03480b4500c1c841080d0300072030220716130b612008602c0350051460031240d480d224036125030703694102c0700103e800075423100c08244998007031005418400d2003403050b400220b45124044415846109001d07005600c0031920f2410090324400a991004041e03804001e0039600743c0020f20896006009540d2310b50351900442c0c0d211350210b00f100c4089001030005503440d01285001596008441801c1d21424464174819595103803140070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 264799451 1250 264798201 264798203
    0x11a040c181a09090f040b090d022505100c02040f020406090306021815030714090904060c1103040308030a050903030105060703030f18050102030411030708100216020a0314010f09 79
    0xc01c0000d5410482542c035460b10111152180c000b0a10600714265101540c4030310842131103150b03102c1030500d86090030398207402a0400c1850f03040f10343c80c01852a400100a441312440365429084600c085c070103da03c040482c0c001a400054991000944035000364100d86068400d803400c01c4001c3d4030071a04812805140641400608200c1c400c0011030b8a6402a00725410703040314240070b03101c6900000d400700799414810300c885c5601204100c94240c000d0307046401604207500d13043c509250400003d14a11009100a110355551100b814001c0c1c03007400c0e495a80e403502c408984d03a0340c0c0c89041000e55908200c804000705418040010741425001c400d44e4121100540380a0030114140d400b0b90240031a40b000043d07040e5a5a0f0400b800e50f100d0b000404240e014400060303490501d42003000030000d0709440e0b0781c041e50000d0070412040f00700113000b0041c040400320050f160010383c9840210b940380c05101135404001c00d48040306101e01940301d0001074250704000c00a080c0c0001a0354155050508 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 264800701 1250 264799451 264799487
    0x10050c03070b060f03010203090f15040c0b0a020106030501060f09060b040602032508121602060c09010c03020f011b0206070906231603050a02011103040503030103140f011a040c 78
    0x1e40c0000610340462650407002c020030202000c19003001084c00ca80003142d0050007607014440d5240d11041c14022440940c0c60003600e2000c3e440c090306c540d00d00700020f00c00c07012000c000203010b03c0306500c03e6214401441d4084000d004840d903035510982c041000b4080d05406900e041000254102580d0840301241d400d1740241d4181520140710b200d940c400b0020224407610a081700f1000208403000404080400b0680a640390a10b800c410141100001c2c1039000d55114505201c01c00c42c011082e5200d80000f480e11460384400c51400f03c1c1400c81d010418a450b40c00c01c24000c0d849480e00207007901c0b0304c01c642d00701d0b00706a540480403a03c0c0190b0784a84c102152580e4107001403010493f40c0c101a40489203c5180351500040c0d0062040f9103041042e00015000324952010366420f0081e41c5528202d80074450450505803070b03c1c1d849100603c4020882c104074171400c0039140044c88580c81420600008001105c101c01d208000400078101c114030a91078200301c20209400748000301c0400811030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 264801951 1250 264800701 264800707
    0x10203010e070c0c03060c05180f01021b0f0904052b05030a020d06150908070602150a1508061003060c0807020a031d040603060b040c020307031d0d02040c0e10050c03 73
    0x4501510f103400400c00586001c0038044001c40411a01d01a40010342500d59a5550343c861045100308511003084245214400c0e0303d40c0c00d003a80c2c1c2c0c00182041c2e40071411201f090143c4006002450090080c42d9240d000b00c0b800081206100c2c0204400b004840076285c20369441555111410140580d80310181c0468410700226100d40365641c050400401000350000e241912800c1c0ca10000111202d07400008480c42d80a100c0c1c0300c820700c05100180705a0004000d0010050540e20b09620010311034011660358040360408150800070880080c00b000c0191103450503c11407001101061340000d0304d8450800304034076a8184242c005500c40c405079030250980c2c82c415a4100c460b603140101e06100714000220301d030407613901c0303210f035400440c420040016403002d60002c1c00261001c0601410554000340702020100c3e400070345580c0402c81940700f206400d40e4000008081c0b003044040070703421a05c0c03c900a00750325000b0380b03a003608490403a019440c41c545000201c0b41d51064940c2056290014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 264803201 1250 264801951 264801961
    0x30506090115020a1e030201060e010605073c0501051e06041e02030703020d110337330513020d0b040e030703180b041202060d0905010518010203010e 66
    0x101c80000c80b0509206485282001d0780b00e4407910030035484541000e41c2d051031074204143d0248185e0000b0682040b0b108140c1d0303d0803d01500500030414080e080a0402c000b00b0b5203000e111000301c02400356215a401d10a6210141202c0e1068401c0b08944035071a01020400c1035580003404041e010380c0c400000e540799100814400070b040701d4503404180b00340402c200d44280e6180d002852140000383c0d00140c03900351401021007500c13002394441040510400501c16908800d030b001f13804040040b42c0849514441d04004001403070f50481802d040c40c9486c0400360702511034a425214080c5500001103841110701c141030916600d03214055000ca2221280d10100070540c01500102c0584000082c0b0401d94101240c107480110740c40c10a6900002560381c00c040d001210038101089810142ca07446042c82c00c5100c56120710700503c0c03109005051440c08541d64841101d030210003450091260241c1d51800d24068942600e201e0044041c150000021440510940341221540b04040c80070f62a5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 264804451 1250 264803201 264803219
    0x1409030309120a050109050d021e0c150c07030f060c0809060a050907121a010b041a0306061b100b030307080d0b190602150c0403030806130b19080d0305060901 70
    0x400000401070f0250f444420045202072140141050042c1c015044100c13134524002e0401c0e00300c0040d0388160a041c810311040f0403000441e04440741c02a5031032004200c8810f5000b0440c01018030280c1948a800e10100070444002c4030f0369845071080600b03000ca0340c4d5520055400c800c0c03c070351303044096206000261645d210382c7c000b2070304000f0500545a04584032000c0740748141180d00166050941c0145100e2071807041c608550041010741c0c0c07138509050900070a0915201412060408480084041350303041e500c150403226180d12503568545c070340c0c0d81104441d03119491625104042850140000c3e0305040100440d44102d034407940d810319241c01201c2040003003885d1a201a084071081c0c1c40f003e0030402c500c01d02c4c005802c054004268034000d4014581c0b0500004118400020061100700b001941001c10f19402040c1140e00da0803100d6181040001001442c890943c8032400306000341e9140c07400c8000f1415aa59070069440d100d090320400d5081d140165409604051120700411403030003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 264805701 1250 264804451 264804469
    0x40201120e0307030e0a0e040f0f03090510020a03080c09060409020c01020d050f180c061b0a081306020601050a0305060105060a050c060a0b0306240f040b0303070302010b011409030309 81
    0xc180d24001400d1001020300c07450740c1c02c6902d00302e004c0b40a46003d03200d1440c19241c070400428800c4200c1160b8940360380c42e50782c00c04802d00c0080404101c2c1841c01d0815005007030700300c050100640f00c1c1510b5214444025516803001d170701a000f0a404802003160b90294400725a1398038405003869142500d8020510001d5004400c50002d5560a1000382e00340740f442e00403180a03540000c03c00700c0310300741100d01c1400001400c26418482d440310b0749030308050b16400182c58219014000742c2c1091141415954100303103003031000811800002400d400107900c1d07944508240c400c5642112044c0c2e880ba0240300340070082e40400740084d441134004020a1034001d0060104030103902d0324608005103000400d14154095482c42d481a84500c41c04540b818200078550f030011101c2521000e26080521030510b0303441603850306011f1041d811800d40303a903c0b10703000901001c502408996072403101b820028000c04d10300100b140000c101e2110008102004411303103d205034018083d615242d011410821205 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 264806951 1250 264805701 264805727
    0x1021c020304120b01030203060f0906070503042102030d0609111806120901050105040b0607110f03032a0c0102160504020d0b0405101e030c1841010509040201 70
    0x1c8030410011501d454001c00380b4240341d02c01c90034541c903541144101400c0590041c204030780c4c001040b00700203180c82c00180c0c1c0c83d0003d515041140d034030345550825898240c15000b14402c03040032140b0314880c1c0d56000004006100e8030060800029848444e070005498103584a0991200301780701102c143c01c0c07101901c412100e001042d01e481c05d41103200c4002c6c1000f049503a4201655140c0c010032107414a0b0044004000c411507400b13260051030740d074845030004140c3c0e28501640703030398020819548041040303910310042c0454010060410820604c0703400b0440300080814054801800c0a1b94000100c0d45d00341414151045652800c2c002804001d41000c5c2807217000f00e03150380043d402501d031407007102e01414a1030071002c03d0a00b004261000707101d440b03034905821b0348540410804035000301080d605a07151660301004060a001894010301440a2000c0c988180d01d124880300b1880c1c041013403810014070030b0241d03011002a00c080881d010034894250003000d100f00040c0198070402002c1000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 264808201 1250 264806951 264806953
    0x1d03030a0f0b0909010c090911030f04170c010905070b0403410a030329060f0c010212180a120315081014090606010203160f1b0314060601021c02 64
    0x21032500000500d1100c81542c4000841e55290381c141402a44080300c80040c1418232000c0c042d1290110000009103c010a0a01020321401c040b504118401c1001c0c40c0c000c00c21620242c0310769048407098000d00030706501722010700c50004000354900000064904a94220310308079040c0015404003000001d0307002c90070f0900382d8241c1015061024106001c0c0a41030640000d02e01101186000b81c201d0301090a00c03801c0382186401030303401203e03404880049510aa07010b41d00c500c11b0000b59521801031600b014065400440c85140040031030710602d100d50001c202c4c880030001c251b5001707520340c01c0c0c0e6907001e040c10040004540b0a280203800c0003070300c22002601529010703900c41e20b01703040c0b810b652074504410b5194800055004d10b030003d075a400607800b10103410b07207040c0280080d569205000c0c0350017801407510402d0040c0401c080a001c140da8101c1da81c44600c01010f02001c022006501080710118940d28015850600001d041c40c82504107800802403048500038016106004035048070031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 264809451 1250 264808201 264808211
    0x11409040f020a030b0108011a0a05040e010b0a121e030e09090c1002030405010e0a1409040206070b04051f1521060212010824010504022a101d03030a0f 67
    0x142c90f0500c03424011070055074406910b504080080d030030759009103d00c41c041410b2030744408440d0b90f12071000c81200c004690004e01c00d004602c075940902841070300264401040c5400080d2032588114242c04140710b00504840040c0141080040004c020005000955004110b140d182013140340241c0004a207000c0300d407109140c500103070022036a2200e5200581000c24100540d5812000c0d14100e200b0880b103c2202c2410550110034881c42105c0345c1d0711554040000c1015512440c0031122080c0d00030483c00042e1a2900b00b2660b9030840070b400ca84685441106502030451034480c01650346c1c1410740010400c1e180454220910b842d080c0c0c2d007003511345c0d14009500092043d2000b81400d85400c08082d03069031400c1503907401d04200f04000392949504000340d02e50010200100c0d41540c00c07c4800580f80c900f00c002240101b80c5072400d140d104420140e041c8040d01000503d481248091841808490030020440410502d00e509024507a030040c808590003000e59041200300002000300094 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 264810701 1250 264809451 264809453
    0x70c0306051003031b02130c0903020d11030d0905031b060c070602160503030a050a030522050a020906150d0e030904230108030a0f0e01030e010606180806011409040f 73
    0xc41c1d00590b42c0c6544510004820001c1607000070b4505540303020001c40c440b080245801282d2000c511407143c0225a990707000c01c03904507008400c04000f568014040c0b4000d440b0a250030420402490740e800d2280c810041c0030f118181c1304040010940b14003401603ca51071920006075032010a20383d4580e480b043c140b10035203042c0c10130040d1134001c2c0304030350040c0030208800301c240c205e00981c0e4002c0780c041d07002000302c1c0f4090360f04042214480020752400007000e40d2410306521548a05600500c038154030041c10310b040c0080050402c0c0d0060088400e003075a525014100003454409102e0301030030520a00c101060001c5076448000c442410500707403440c1c10841000502154120f0740480c07c08103801203921031441c86110100d01611800b0015407420311000c40c0513108209190030351042040040294449034444c3d0444189040c0310402440865200c00c0040c4c181d010b0307003074202c081030034155000a16100000b4264120340e0a408018200001102170001c0480020700c1a251801004a054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 264811951 1250 264810701 264810713
    0x41416030b0910110702240703080403020a060c05030601020f0c0906100306080f0d0807020102040317030c07170918100e090a050a03120506030c01020c061b01020c010b1807050d02070c03 82
    0xc4219904031504650320700080c810000b9100182a07d140d038020710074105d002071318084080b80c0c0d040d901801c24a046590364a0101d19003049520001d0525003071910848110707800c0b0000e1030060f20240c081c0d4000c94050301515a460000020b4603071b00c9a02000895280d0030040904402032400d0f183c04544543c0380d107052407904a01140f03041ca5070340f012070070600031984004500d803c00080c1c4029407419107117440e1a110702c05402403481d140d401c000081144201d0300da00f1140f031a070340321700b1210a109241070020101c0d00181081c0b8050000c211804044c042c0e000c003810b22074604000c00190003400e10018007040e00b002440041319200300c4e0824404031308204003810300c01e4070a54598216040305071b854802c4c3c40b00544014003070380c002040c0652581c2c000c039203410381d1002a141d45840c1c1c0c1c0309032114451003c08050000113548000364000e40b41006411410040b0015110660624494504000007040440c2c0c400c0000c0d00c00e01c24401244403035002080c650b4059680740302c203181c52713440f41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 264813201 1250 264811951 264811961
    0x915020604170901032408061e0415020702180702060105030a0c0e18030d0b041b0512061c0b01090c0503010f03080706110a030213050105161511030f041416030b0910 73
    0x1030350040c03c0d40000301f202071400c01106601211642501280c2005070491818541010344002d00496050004d900307a11640d50607901c0498001b80180b40b1482030118420307502c44242e5010005018070400810241400128800762560110302c54074400d140c002c4022842a02070418109540200c2501c802c2e5081040600010800e80600140c280d02540811040750501160912035014003919180840d41110981e245c040f03070b404410105654141c0000e480c003284903440c0f0ba500800e06450428405460721140c1a034451003003c000380c0b45110f801b61102c2c042481080ca05000d101d82c2840068240e5000d0300d100380c8120408103091038440044038041d00094120310000b075000c42c810002c2d90188514400500003820514503203416120342e031603001c40380040a0000c4103007a80700c003106402c0790f10052a1480140d06035440f8144404a0321111000b82c4081d1040d030088003a20b4001c4d2804203a80107102503808403103108503e1a03039881c0b1081070051111115000d43d0712030004d58030680c003034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 264814451 1250 264813201 264813251
    0x6040305060a0c0309120302071506061d0406030209070f0908030a210e061f0e0705070201080117070e0a020c1f0612080304020904170a091502060417090103 69
    0xd03000350702e848498107040768900f0708080201820b055045d800314201c482c0031004203140307140259640d803090074550b001350700014102982501e06100050705590000690305445d402c1103102b181c9852507005c10040c1da106000103588080e00002007203175103000d41c0b01600c0c42c58090600c2114186d48518150840c2c01850070340e0302042454071580000e24500d06880c0c46d0042e4400108150305900025035958940103005000d503012441c00000b40484000034100202038502e5000010b1a10304802400c80d08000c004070702103201d0398004a0034821554040c808150100000c1020030702e410403010b901e0401034140d800c0154200000127105006101c02c55410b05002c4008280144498182048034103992244114001d03241c05000000d09403000c4a030026012030b140302454560f4100142c066001d280d203615035010006001210315009004c0c401110340e40c0d180c41c0c00700c0130b040754140d0b2591021580144040000c898080038084488058121048185400200e041c3c100899410840c80724034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 264815701 1250 264814451 264814453
    0x50f031203130311011a040b041503080d050f011202060702010e310209010c1b0f061706060c03031f1a0c010b041b21110c0d030b1003150506040305 65
    0x68880c2c01d0582000e140d110728000030008014103058245441c40982c000d2207200c0c8966140d544011003507840740c0007000c1001504101106c15545c1c0e15101055521010070310030450704020005240c090302c105010f0480f21200c0000010495541c01c1081540c400308007207061003000160f50040b51200c0040e4460701a0030594084400800740005d80700110030124100c24a004000000075030b40d11180105100754420300b0404072180d0b804580b200612140c02031240d289003c40001421b903800480343c0b0200303031614071800460715a50203010091140100311030140d80200046455900b8500c009041500040340e60589141c84140b030000700c00b010f08080c0c031840b00120381604900001e00c00d10400900032141000050607030a00500f41105085200050002c4040307082c0078016014004000001c50410400440f00a0004201e264001018888031b0740b00e6204440d038100e0007442805a000e50040c640080e140c6000c80071009491b0407000032885208141e00041c0d142c46840241c006544154 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 264816951 1250 264815701 264815731
    0x1e0d0804060804030206090f150604020c12041a03060f062212020102010f09020901030803070915030204030b1006080c0711030f030304120f201f060602010b1207050f031203 76
    0x2013002490441c0c007501140a640281043c910075010014081d0303403605035000e185081ea038803100050001d00814910300745a000b082c5030b190b00c00e14480001c0c8182c88051007411004c20150b0783c006500d0108403005600440b000c0d1187c81140b6121014180611182001030551030100103500c042e5011503122440303111112001c00c1c210768080c000d48051803000c007001c000001864000504801c81884041c103000700000114000d148121105c00c054041b0f00041c140070001c68030010003e60051100f51203107080340020034103440001c104070b41115215500d80f070b840c0d110101107200603842454102ca038094103090000542d241440181a00760301c81e80550f469150130b0411170103128441030158200201c00705102800c580002181210865007103034028481d060525540c03500c3c0b4200e00c501c64584442008800031600b58100409545203130380203110000d284c20900c0304800358120540716540044100340218103101117035402e100b40080c1182e105c41502c10710002e8550094840000da4043c030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 264818201 1250 264816951 264816953
    0x2180d050d0e0405040b0f0705070b0c0304120201020c0a0215070c2301020706020a0b040f020d061a0a030507030602070c1a0712050316030c09050307090e0601090b1e0d0804060804 79
    0x403001c03001c81a01c042d03c06000c2442c043c1e03607900d24610001d1000030240c802c540401d41c8a486041902c440c50f5004003501500d081000051809810840301210240e43e5201c034010f9aa2060003510000d50f8032500804a0343e03030507401c0010f007920307207500303070803555020f000c244003040c0009066001882d044a001c0000d0180150111680a01064603810b651049204100b841e13030002c1c4007030244d900020580d60030b40313583c40d103000c802c13000c000082e41c004400e80703420003800115072103021003d00321010f01e00e2031524581030107004805e032311000c8c040760855038040000c900b081c0c005005ca18855500a18101e44034041d020300020324410f501c002000c00b003601c6040000f42c405030354086610b400c005043d49400072007080e40d40d17280707206a020540c89001001005002d48420300140c44004d042d211003a031550414402061075000300501c43c89107400002d031142052240140c1d0321405000007034201d08004e90100d04151480c0300380c0d040070b5012104804103d00d14058400303042036a680304801c2c146 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 264819451 1250 264818201 264818207
    0x82a0406030e0c0102030a0c08091309080910081b0309160f0f09020f041401030e10020a03060b07080f0a0c020d0b0f07090b1c0209040f05040210020f0303060402180d050d 75
    0x640d07403003c1d066610400406480b02e82107451070050030350128509a5900c154001b20303062050203800c2c1210141014400d104202000780680001d441c00d941020015a40f074100f00c420a0064030400b8085110030035610700754010000440c0d006505104031554500051340403040743c050341d4800c0401c18040503091081d000f91900301c0004141504045d414200080d46c0e102e6140700d14031549a602e003001540481d01d074001c1c1c01840d40c01c400c1505030340d421020a2120000303540100c4410001905e440e0002c00d454018005441c0c81e1a0424200341c10039020b03801c0740c0c24230750268042030306010305070380c42a0050f41c60074640240184140201e44080c1485a0002c0401202418450501040071018881d454400082d2a0a099044990200000c492184d400280300300700c102600306040c006482035541d40f5030801c0303001e18400c1d18108401440e481c0c040741c5a404e50103e030883c6400420104000d8501074000c0e129641c1c06034030f0726240c1002c07a000185524084101220f0641101000301c00030742e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 264820701 1250 264819451 264819463
    0x80601090b010e12010902042d02030405031902120705010c0e0f0f01051e0f040303090b031324020a02070509070f05070602071a0403020a050c0d03082a0406030e 71
    0x2103100010701960403032000290080350414502405844001c4c1212200394094100348005600036100300182009801c0c8c1081c085c060405907404a003011450811106080c800c4a10568100d07003d0f50070044540501482c606a24840d4011849426011034060000f84010590580302e9400042c0d586038428000e400c2151810303100e4417512103000800c120ba19103420840c000282445c0031943c8a0103c402e540011940210b00310b07050130085041d4451000510050060307034082d07101c01005030b03503c95041800e032104460f661380c4090200301700000141d000c80303090030300045441602142c4a83e09800d10403a00800808001a440300c0c00030401400c3c2811080e812410302e1400c03c903c400c00e4040034180303106100008101540c000740c81c130148015403c10410200341c0c0101c100946c05c0c2420700956881d00140c0c1510f0602690325103101c5443c003001c43c1c600407603040d100c1200c3c0b560f0783c4503000c20000300002c42105485100124858580141005201600140d00c00103407038079001c007903640f03402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 264821951 1250 264820701 264820709
    0x60b0303043201050d0905030d0903020c030708060618130605090d0f11032203080c0a03091e090b0111010c090f05090405061303030b0904030f080901140726070801080601 75
    0xb11040c040341e0310690744181103900408500700045141c0480e0701d0102d185108a440d80f205081c64041402d04041d23020801c1d01c100a4110200c40001362078001036a16988151910b65110708194054407601c10000340003980000c02000340724000d0800d480e04000d58000b00c80801c1641c0080718240c8801d0b4100100a190002c00c0c64002400b0f181c00303201541e01c5c4078035030346214a01c0c0c515814407446003045984034040c581c400d80303454481c2c6a455115540395094441107021500c0e5020100b1a001942c13415602130050b02e00384a0070301c2c5042c0e01d41008191401d00e01d4108403042d03041c05401d117401d0049100e540d00a40d102d15266103090010003030900241c010310301c40e40010050102040002820070341000040e0240341b02d40d00c851409800500d1400034440e04182e0742420401819040a503284175034003551198240c6607501c1801c00c1c00c0354280c2c58000c0c1c0d1030445a01003040f243c8145502050000015500c62000c111954542614042281c0003c0082c3d603c0005104190083c4850380c010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 264823201 1250 264821951 264822029
    0x4050315010b0d020c070b0c0a170c0a03030c030f111911070e06060d0c0201320705031003020a151b050613060912020105060a080d080c07060b030304 66
    0x1d5040426108551054041020710b090b00454140190030302881000e0041c20124409070380d03030b02d90029035900c85c00d00440035558209800c0350350303460359040c4080f90f0202e0200c0028080b42e81c41076905500402c1008000300030155100c0318079844c08400e2003800d1000c8002004541ca50316108888140034030104d565100304030042a1070503030074000003078407800c6e03e0701e51414401c0d5507148008100940112001081c01e5401d21200030507168042d4411075800017481000c000076106140e10b90002e00c2e0b40346084144c8004000050b09040c0b198000c0c68101c180040c0b115000755036a0001340d01c46d00e854024484816081584200b003d030001c407a02c42280e290f01403119210311b50b03120395841d004014500800040801010020855650700841c4030943c850401604500c1c0040001c1c002c000854a15000c3c412594012030b22650015202001e442195990001e40ea2442c800014603045030100302d490036194210a9490764050003d08050301211a8a40182d0400d283c44440803c408600d250300b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 264824451 1250 264823201 264823243
    0xc031104020901050f07030509130501061407021809010b0a181a0d0f051005040506040c050108090c0114070f030f08100e010504020306030f1b09101520010c0302040503 74
    0x90344c1007800d8130160040300d2285074465107181002d690b07500c2031040c1c059008411070300e503008203001070344454140d4806da915031075144400c104041980c03082c031030040c1d80030110302940d1601c0c00e50303c02025400560780c000814502d12183c00b1912034401038000c809034403d01d0b51030402d46046481820000b060000e401841c0105690200341009064440a04030003d40000344050100400043c2001c1e006220100203600e03060500700d84580b030a4800b12804810488000740640c0f04020746c1740600d0178403014041143d00f000054410703107841141c815200b00140420404507192969000555010f901d40c2c87c1040e8601c0d5005090300c0005040d20b210500b070090602c04940b0044056064a2003600d0060340d03521140000b92500407610700030344c010b201c0c03241110b503141000d8000041c801030554200005803640340d22030400c08824003524281c40354509456503003910030f041c1084241c214a01201510001c1c000749429105d10140410101c2e400107800c1005050803c0b45502050007401d80030705c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 264825701 1250 264824451 264824467
    0x1b03091502070305122806031e0201020601050d140307081312050616030905060a060611060405060c0f0708190e060307092303060f0f0906150907090801090c03110402 73
    0x4068055605c60324510b020300f200045080e0701030207070712600e414029034514003d00c02d40f0055025021501044811240c01c1d09031010f868140d4540c07030300040e03058000c0d00480c1e003410140801000300704c40030744081c540c1464902070754005200800301d480c003410302c469640e0040d0030070b8000010107a10600003010b0b4a00484040350020500d20f400006005108100c5d4502c40b00c100c001c0c04413044050194043c00c410300c0408078040d40400c04460498454000c09901a00342d02d0300c1d8181100c003d00250000d00000d603031400180001c0401c07004000d0002e0400c0d4940d01c0b84d80c2c00d50020340030402034024903c07074554840e40100d000c8500c40c500b00c8186166281135980141119520b2064410030500071001550065842e10a0400128080c1c2152250301d041c1d0f00e030190010055600c84c2040800340e012400021010407454400d044640c04000304c50800170611034602001000002005170341a00407443c0f98082c0901c2036107600501c41d0895490550a10047d48242c0080440c0f085104006d221 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 264826951 1250 264825701 264825707
    0x1c0506010207150c03030c0e130c0f05090a211a0106021c02100c03020c01020c0307150c05030c22030b090105100510120b030106030b0906090a0201140c011b030915020703 75
    0x80700ca0703131514021031020300b00c1505445004400c032500381d00c456120000641c9c111150f01c01400c03100d42d50b03500c0c0542c4c0480305c0241c51034440c260071036810106010061200c0010700e02c00f0300c41c641c404000000c8450103a1103001d070200703281690001c941e5801d001000314903070401c0181c56101c12060410f140303085035034001c0d42e51590000d040000d1912806004aa0380c040d0b8103851000345818000d6685420311031034641c503075118800484d030340d45031241840700e60065031240090784090764440c030340b075130329030355080440c64000c000201040c900c0d8440d1000c0d1104005e41c40c000a5201c0e2001e03084a0610062030790035954001c004215250b1040020005540e800c005042003c074103007092410300c0e9505403c1c102404081c1c4841d80c066080c5840041000030342003010307119500c034000351040e41e1181c1c5003a070303100c4070403045c068002203030000c90301404c0310184000d081005c01c41000280aa1802122400c080311481c0b101010903903e820324803e00100040004041f18000e400714503110a13980d0203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 264828201 1250 264826951 264826967
    0x6031005040e071505040602070902340203030d1a010e090c0702010309060c050c1006060c060509010b0307060f0e01080f0106051b030d060609050d030816051c050601020715 76
    0x248282d0b203800729250319072000e01c00c2c0350240c01c2180e81c81c3d2019448a40c09000c2e60310502c5070900510441400007141d00f503c3c4250f814054076407041075500807600d0740403003480112041c140c80300400100d01d9001a5010402405054803100d00415081040c044c3c0400f20f13603000002505001c544802c4800a940e070918595004c0e051012464441d8444d0004900421040b00014810ba1a10601c4004075800502500803001c41504803034025100040c9001501e400d80301d1080801d46401b8913a0000d1903a8100603888010343c40002096400800001c1c5030280d17640c000f0010550072800701c0782d007661002040200c0c1500703091544035030a0102070301c0c5c040d143c140300e00f034100000890072580021080314000f083c0341d10902101e0726909100340c00b10081c00c0c240b0840c07010514104001403d401e0010340d072a034054140d1122026607548944800901c070041d00b0140c00c008003009100c00000d903880114290b07000b01140045c042c501034001a1801220350042428490782d21100ca00180d4884d0f0b42c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 264829451 1250 264828201 264828209
    0x50c0306030a120224060a05010908060a050406091208060f0a0b030604180b0c0d05071b020d1419020f04050105030a1101020703020604080d0f090b040e040f06021308010b060310 78
    0x182c1809000310000890402ca1800b080117104e12480016888566601e09a540100800c595001d40e6a94680c019584c03120188109480c81c1c024400040d002a016170113690720070701941c0d002ca0414010794503101080c00c8802500c0c0482e14200910171a400d21400072021440c0546102c1d41c800e0602e01540910b00001b05076910581d103c14031441603c8502c207100164035445a1035502e14200105140c0d8190402d641910041d8504000070b05e85e01c1c46000413480b9042d0150359941c02e0100303502400314150409000703035034095401540700c03d4100100400714601d0352554211040b110244100410700415a00f0301f4812420200140000c0da40070481410360380d0700c40030303c144021804005070b05000d40381e440a940800c020134005642c0c6808181038000b00c405507a200100c002c071a109441035030882c00f83c01c00c07400e070600041c0191560b00809941050048603181c02c2c43c5426511103040e6444402d1031602c4074203010041120740000d00412100400440f407060070351802e403180740c09420942c45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 264830701 1250 264829451 264829463
    0x70306140a1a0c0d081902073207090902041506020309062d0703030b150a030f02040b0f0a080907060806090a0e060a0b030d05040e010608061908010f050c0306030a 72
    0xb035480b80b00040804980b08403503103505444003d82d515101400680381120f031812803480348500b00c0f08100341482203070000c5610011143c0074440c01c500b08088804010340c41030801903100c0306030b25040401c1108070010034100d50081001c411500c11b11099420b40c0ba94101c80c0804a5400e0041a03000700c01d6880e0520180c0300b55407900070103603840d00d10800c50100e028018407903c800b00e4443c8107890007050603500a481c10701018640340144943c0b40f03140d481c0c1d0303060300340284641450b0340d11030b40124601c48120302c0054103082c0c40b0004054640e01003034080c46403c1c40024844045ca0700701013110390041000025040503441c1c0f00000d0310001703000342990310510020300010080c100544c09000301c40240c2d000c807103c9160080c120740c01001840d490520a1161101c3c480f907040c0714408450684903c51b81a603c0c0b41d02e4000705660f2984054103041d4490184650a11200c1c5810381c3c074002010040008509046112009011204050545101c002c0200200010341c1c8000402c100c00310344c007032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 264831951 1250 264830701 264830729
    0x5090403090b0d060306140f0c0c01020d06141008010f14040e0d0314060607020325030b0c130605090d030f14040e01091404120c0821070306140a 64
    0x4a0200e5000300107401242030807101140141d400f414941c850419244144020880c2041011a02a407884211000800400f004002030b4041802c50040c2c071503402000c0026042c447c0c00f01c8003a0030340d186a0068603000c925141410ba0340d207884001c0715503031313003103420301409950511007050188482c90052004100304440080c185448540c0105901344070308042d42c01da0302c2c116000a010306090034a00c901902d00002044151414100300d0b200a0b500500601e21b08031480035100544c26940c8154852140c8504008081100f8100c094407922480c0325480c1d80742c00303400c610424004c25422040070001c06015040c1c0b03545400c06080c1119416003481000c0500c0b040084910318000c8080900c100000704000511060b8800c00340e0503555014030500ca00011a10350203030b0320604440c0501040240001c4104041c014001c4d200c40601071414035242105041996284912000d41c201d07034801ca8104109003182d05200e0305010341264014410a00400000194500c1440c00740300c450b075445c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 264833201 1250 264831951 264831953
    0x30c0606181b0f0d0b0307080106060c020d0203100203010b070c1a070b1801020c0a14010c0905100908010504030c030201051602030a0e13060801061a03010b0a030b01030b0a080609120c0601050904 86
    0x141c030a4607526552103c01c60b994180115400000d00000901d5074044d02c201000412542d0b018041d41c01034515a030344000021819070200140400102c0d02a43c06d402544108503034033a8900055020f80415040d81e5a9030156141030050a1101d0f880504456100c424040c41004010210303105160003110445a9440340c079041602801c642025108a602c0001c0c0360704800000f2803034008ca83c0c011155500782001551006003030b600a0710250b0001154030205001f5490500704490302d140e070510381a085241c0f14800d20342100c4003a6006d50215094818500070076509008040e8000030200318580c2610002c280030396640903869843c3c0500c18242d04000480e126207134144d2800b84100c000f801340503075545603d40249070900408815507062205417071081030710310840f4120381d40100618039001540604400070f00110300c000d410940c8038031410406550301070b550406015141c4c007070802410003452461070101b04204051581006200d1404c00e0040451810304503141a6030a2900e0b82c0c803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 264834451 1250 264833201 264833251
    0x20609040b040e0c0a08011416020f1f05072f1f050403020c01110a02190e040c06022103010302090601021504030203030106080105041a040f0b12030c060618 69
    0xc541407642c100749000d0156001c403100107803660f00e405040c3d4205e042c4a4440140d1800e0300d24940386410070318000b101040e01c6040c0032454050056191065400b65147d42c20244d0801e0726901c04070888014249009170b0b981041e12942742c00001901b030000225030417250443c1c4407a81c5080d074000c2c1045200d1f640005a07014040e40000d91590403055034040030f1540300e0300041c5800e0b94240e0052103400442040b650203104245035611025000300840d200d65400c0105d80001022a01001d00d2000400038040b0042a0042e0141c1c0c828000a0f08240c10800028030b04100888031100b00c3c0307201c4900344440d41480c1c0840b8152501600c000b0701554801d001070340742c81c1c0d80031400d01120f120b80c0304000c203042d0f020000d541610a40e44e00c44040343d9950040205440800d45001003200c6550b102030a41c0c50154031602e01804c1b030207400b04030700e682000000c0c88142014080e0ba21034000241d802080c2c0c20a0201030352006088940209480c5044442407070018014110300709021102258810196 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 264835701 1250 264834451 264834461
    0xc0f03050613052e05011a12190c030e010c021b190305031b3c0f03130302010314090a1202120301030c03140a1e03030209090f0105090915010302060904 67
    0x1801a002040340e0001d9440755030000c0102802034613662800001203046850381c440c000481d2801c0b51418100085190f41d011056005803080d00307188200d018030013a40c0c85030300030b2071a9446151000038841c404904201c0c00c1d103240040c01411500303d0680034101d541500c506d4078036101e0684202006804102c0d4041c242c001a40019065200c0441c04902c6c0e40301b03150a0f0342000e030245094500c01c520003441e89000206c030714501d24a00c0556449403155001c00d4441e1000c1c4201101150840d0621444007811640030445490540c08030010520940d6014000c6a0f01401108107500386803800348449034549051080080c0410806071a0b0b124251007040100c1c40080440300d160f98a503581e19101c01034580d50b110031038550401502044070100c010440f950710716002101d2030722403000e1140031201c0c0c410019040f01030650078844403155444055005110b852032010190855040008000e510900180088220b501009408100001c48100c443c11680d0680300c0c43d40316640500050040c003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 264836951 1250 264835701 264835723
    0x5040204031b0608070806060306040b091807060804020a14011715011d0306041205040e040501061422090305040504020a020d18061b06061d040c0f0305061305 70
    0x900104012050080b4208060040c040b49800030001c140d90f49000e80340d001c0c0031203222000c142d401e000541c10f400c0000080d5408100240001844914600094242d02040d81c010f41003a81d000c810f4407008004010050251809092030f84c00d07031509a00182034507001380a2100c0110741c031800d514440e4003581d0100c10405c040d81100703034145031000016040a40080d01e290020707090748081d0021200c94640038282d80005005001103585684030035035186003144c0c1c000c0030132100300400a6140f80c2e0003c3c040c080da102c0e90007c605e15140c110b10300051b102800000d4401c0500d101d00c0c0c40c0d0101d01080001d51918078020201d07001e0107034102a5131502484c0d011035001400003130b070750480e90790101345600c2c403820a03150301c0f51042c1800f59000b0108582d0050602083c00e4115800700c03010112442c00c2041d2040002140c110b80f42c40244031024100000d1050300074040c42844200072076004540017802540b02e0401c42c682ca1902c860703568003005080d896130001d03140c80400c244041400192128 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 264838201 1250 264836951 264836959
    0x1b110f061c0f063209090d020601050901060804111323060316140d0c270203010f0e0411121b0303180105030a091e020103060f1401050f2203150606140901020705 71
    0x240c501b520580341c4a10b0703c040c20f4401405070b4400820280341031519a41a07884955032802e550780e40e82d0703e009582000200c1c603035212210100e003a660001320f001d111050054071820b41054004110030300300c1601c1c05440540300390003a10f00c81006800d6641d00d203003203c1240804184c071f03e002c1c0000c82e0301e00f00020300140c941503010b00c001c03d107001c00000000003003180e0000303003070550070a6003800104e00081c01030910f00d803307103c0c04001c2400101c40164010b8051640b001d501c1c201540003c0215411411f0000c02c2d40140b0500307070203014180000606440260069460052074942903400040f0201406050ac0300210129412089961040050780d80c0180f410031032482210800010486940d03040703002a05100010458146101200c012500c50b207444a102061000c019925604410401940c0c41018410020444e103e13800640448c03010f4402140c41038151308082e20a000c0c203070075030f041c0c007400d0450412599030f1028925a88040320342c1d10700e855074071a10040341024910b900a03540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 264839451 1250 264838201 264838219
    0xe2e0b0d0203240f01030c1202210703020c07030605040305160311070b0708040501051c050a0b12061b0d151e061b110f061c0f0632 58
    0x10003000ca0380158069002c0c076a5000e06201001c2c9840b00d00d110348010190031111981e00b4568550080d001000d071102d117414548140001c8088030402c9802241d011f424005c1d6446170003898882d0b24521642109440c0380a5180180103034000703507540c050380310040c10117980e0b40000c2c051520610960740014111440300080904600f0020000d0741c03195080c1a203030150203030000303c00c1c140404640321540e100320f003981498502001580d90360000c3c4101d207000e2140d00906501503c041c45020b20401c4224000a5100d03e070300240003d2740391035040071206910240c2072207513240100341e40803010b11241c0b400580d5507441100f00d9024080107000400000140040418040300079a5801070044da8603180c0c10010340c1d03a07001214800e0080a110940030500c1c60028045008036030034100e8200046c1140103071015000c08515140d202a5000e101b5000c241081c0c4401c0003140100d002851140409020543c1841c240c9496034402406200c60030030404c080100340407800381200c071078110081800700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 264840701 1250 264839451 264839467
    0x80a030905030d14070c0201021005060a050a0f1a04140d0203010b030312010e1e0c0c07030206030702100e030306031207060e0f0a05070b0f030604020a030609060b040e010e2e0b 78
    0x3c003500400940400ba0111900000c040c2c0348503112250740c0640580c000c000440140c1044c3d030041c64080d0030b00343c00942440d80822981c40303a90b640c1005100d00303806203883e1440e105850111002a98400544003400c11040007940003800112460b1081220b00c0085051140b0010703004048401120707815010210b00f440036441c50078a41412600b6100c10100d40c1e0f0b0358503400b03410004002001c80102c00303a5102107480012918050309005d040070040f1902c0036200d40016240307030011111200103034003240d00d501e880a030600805900d91309020003942141000c000182d210f00303d00200500349103010410405211480e0407c100c4500310800f035521150101300019212484d07420299840d1203030b080000f40e48000b00044602800660001da0704580700c990420020394001205e403010540c8176500420741e540b042c4205001424020714807941d4900d071840383d1485110584c41181041c0d13002c800c1221040c001c070091850130038a100c0601a44000e202208229556074010040c40307440419440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 264841951 1250 264840701 264840727
    0x20c0703170c0c030c010507030804051911010e03070501080721050a0b011806090e0408130609180e06010501111e0604210c060e07120809090105180103080a03090503 73
    0x1d003a01c072000740e4200030b48420904d6a03d41d80031300c01c280001c2d400c102ea800401d01c50100d1070303000351003101900c0545480d490701e00b40300300e82c010080d03400229140b002d500d5981c105807a0750701c4142c19005000c5983c03400001901d045002030546081c0504a02111440c1d0403151540b14903000b200c4080090307040a210400046c00c400751024042500c000c2000002114200c000741111700550341e4540c00c83c14072980f005852005042128020401d1180e000981f10908445014080681d510566680351000441c60001c203c800d0801242c0760a400c420781d0b080204019056a1082c05c11030115030407401c2481c41c1288180328581c0b1040007110070070710340c000820441d0103903004407600c00c9910f0706843c20010310380e40b81c0321070740108180c0201100080c0154101440d01c0c070541c030507985200d0352805e80c16402010345508540052000402c44018501a031480e4007402c1e0a40c1d15136200c0b8034602c4c41040581041c08085d0902c400031a001d0407040c4240c0010821035406011349032500301d01e05240c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 264843201 1250 264841951 264841957
    0x1140a2a050c060f07110d020301020304060b010810080712030207150201020418020a020a0b0604020910180b0f1822020706061a0a0305040f120807020606040903050904020c070317 79
    0x11141d80c0529112424149020b2040d01d10f41031034a02141e10f8004166240d0000d051600580d5400490170103a160250b6402e201943c4210f0007104003040300107951000505a01c2c0c0204051103404d45410140015400014000243d561742e422034909201281820b92a002450f8429215910030308100300303407d907040d0050000c40e402201c8200145a51880d03480a81c01010382410060f408030039081d010951a00d0301c59084031002e000180740c0100d079001b0400318612403612802184140c501d00c00303038140c60f14000d00100380381542182030810041e5010318a11440c041c0182c01441e141c40c01d0350994a24040d0100b11030b0560f414a9640008000907000e0741250a081d45c1c02494210009041114100c14046140d44403403031030b01e40f8101e18815002403001403c10758110703002001f078130001130309110340c20032a8081c1e850381c001038607100030002d19105d1b00a0455001e2810101c1c0700340020b07000740695407142421100540c9608280046034078014282c0c0c00500701030146080782142000500c02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 264844451 1250 264843201 264843203
    0x409050c040b130e0603030a050304060203130605090f06090c0a030201050c010e0601090603050d0801060203040b0d0b100e0316031a04061820031b0d020604030f0302010506040c0c0201140a2a 84
    0xa015841e07170b901c104141d281d00820300240c020460030030014000a03c2540159445010840e0720603822090307440c0c8008a500403602c074022a44410300d001480c6104004c82540000404018900000074402040490b0715605c0001d040c041c0c003040015443d071080d0004415502d146044030090740e5503443c6500030341020310064605025140282ea8100d1013034804d01d0603940d1036001140b910b8a01080003030694411041518076070ba40364203542d00c640d1098204031252045c5e5580300602d0001c01d007014100000515070500a48503064104009003d030341814070480c0c1d182600112507038650801c0009081c1481954940c03006406114003000a0810545a00700224240d0b40c03440301c21809041d070340d140041030304044114461902c1c8480c134004034420300003803015100c9070415a4a980e032103003002d24004100d000d42d440710204086810a4810a00100003900d44032443c0841c070780003c0c0c103941c4010f840c10440f03140001c61a040d24012601c0d0022404200180b4180f0460038505044803440210 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 264845701 1250 264844451 264844469
    0x16080304051507031416050d050406050a0605030a24020c0a0b01030c330c05030d02030108061e04060b1c0b01170616180512010921050409050c040b13 66
    0xc0483c11061007481850601420085015840c0d111a4400f442c4035000001035402c200e0108000300c0060440d001d03003400745202ea117010815040c82c241c00001d66085400c1701b4020303446100307075038089004000895241410a5110f0404500c06c0b50290040e100796941c00c17400d4491519001c04001c48942018101c900030035101d07003842d40318000621041c84070320700c0c441251400782103c6848401144617031030394201410701c0440301c40560340351382c21500034481c2c02071202e43c040010841c0e01001d0009603400580200070300e26800486502c81a15100034101a140c2c568038220181d171a15003041e5408100084440070380204d0031880e01010140b0240a1095442000003c08403540e000041c0e072409801e4484a5214000d0590801c54150710340e4141807840c1107040500042d035803a0030202401682985c0004518040f140c1441e0f440b107080c0d00c00903d001690001035801444d0b00030306a07030039108110302c0868640c51300319842055004076041514000800280380c0e03100384000c440002181c001c44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 264846951 1250 264845701 264845743
    0x3070b0f0d0920091005121c020303070f03020a05070b0414010204080a031e02030415090e25020d08130503070203010c030e070b03040b0f07030e011118060301050310021608030405 79
    0x80c04103000c0d007174441c103040c031610b89005d0029283c46100c0c1f2600c44003003400c945003215104080c0410070740c88521080903810020500004a502c8201c81d03034080810f080562410015050003400391140e4507014181059400102d020450800b82e80780411030400000d40d29240c5031480581c80f1801d02ca4200c3c0414104403030001d1513120205104038a04103034002e182014504603080008280740d24100e070400044400215821100ca002740c0e01880c021501c180a01c0c0d0801500c40321a40802d40e40800d41d4094641090200d0344220400d03405003000028120394601858554554003403000000d5055081000300c079543c0c0e41c943d00c179207264a032f00360031140025a19040200e0901c01643c020f050300c050400004d04010032000110380050f03042c600050b0885e0740c803aa050864601e90b410300c404840002d50000940c504400709907a1013030454800340780d0752404001943d07a045a40600b445960080b6480031009401a0300900b03140d005003d041da01e10f414030f400740d210035a0b0101044054400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 264848201 1250 264846951 264847013
    0x90b03060115030e0307120503070f170613092a050a060203160201271802090d0f020a030f0507080601090b0904111c080c0d020c03070b0f0d09 63
    0x484904035078400c07105401d000c22502c8120301500c0b00030444403481c40100003410000e004440c401c10701080958a1545904056500501406003984030108110760056122a075040340d020450300f0401c03c0341d11341c0000803c038000f500074207140d41020b042d11550961038402d0b0390500d42d03088a00016011000156500c82c010000384c03003183d00452005074403e010405030035a04034089038038180141020100c012000d0302034854644085220082003082c0302007000418101c8c80001c1d801131001c0015402c00c0d0440c40070605400c0c105074043c009010841d404010b54950140620140d5004801ca8954000b0390a02c0b5a0300e00551040c22070900c244070001440340a544550015a6002440c8901d00d4440e9160102426040740c1c0c041c1e8400134041e81102c6907080166407090b02445a441144c81c0c0e0001002c290030078481480f03510954004030305003502d40e500800e068003030382c03101d92420b03454076203081d001e035014010740c075201150303910f45082c01051080c20250240304900003011b070351010080d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 264849451 1250 264848201 264848203
    0x70801271b0e100801080a0605130b090f0606030f0d050d020d11180301050112080c010b060c0c0f031903080903091918110f090d080a080115090b0d050705090a030c090b03 75
    0x1091040b51420380116040b440003900b1900000d03002b80c1029900c586120f96a1601d28076540180c5040101c0c0d030212000041d080301c00e1154641c00750707003200540303d80c2c2c0c6074002d00c03a00d8111140780f0808002c03002850400900491741540c02c2000300c200200088c2e0703c0e004054080b07500c001058014454040d64180303862905008190585814142912003258141d8940003282c001c000483c07070b1075480e61004100c1d9101c10001d010280452002000812103000510588480424815000360000304100c159642d68180754554176515140c000c0740c9903a12100c0d142035000b40c840081c0d009040e140d01c1d040d442840c0100700203440d48604601b94816010309101e040701d00d14414604481403d0112070f000035210006030456000240c000403c001d899518052140d1091100d44080703126200144429400c104d110058400103040100c0c0e414104468a952401221070300001140c41e40000b9486503c03030000e56070003140252403030b10490f8881c0303000c04000d0441d00030202028517146110402e894 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 264850701 1250 264849451 264849467
    0x30307080a0c0e060f07061505040c0203190c141911010509010e010e0409020d050115050d030504090b010908011b0e01020304051c02061b01090506070801271b0e10 72
    0x4100d0f21071a26030b40302d000a00c6190b42010100c010300c400c0520400001c504240074428030184210915007000341400304200c1140c0d650324040c02198024000c400319001c02c0200211050b00a08290301a013905240009000800108410b564081c8082030542d40101c80202071800d4450340005a651541000455041c050741c011540020301c2a09001515400303603142c070180c803401410100355500d454010864240900c18115400da54901103100c1400b8950002405014100c91071600350340d89445c01080c42c09240100710650382c2d074100c0007009038003130740544000340f0541e0000c0c44640d8202103407440d06008107804001082040414008a40c4044110780c140c40d801040d890020820f80446920840c50040884e0007400800503e0a03040884640c800003207108000490003508a1400c1403c090007c0c1180c1c0a01c013140006021140003419414005030740d01503821400d980c5e40d114031020704140101c265910030f031001a1744410750700c002052030400007aa86035000c601039400407500c42c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 264851951 1250 264850701 264850721
    0x50327040e0a0201110f0a0302070806060405040b010306050907090515010815150c03070831050a030201110c04050112020906060a0503010e090a020a0f060315150c0203011d030307080a 81
    0x30b04102401c0d80150300546161012042c5041110321410440007050310309a0b100c101900507a02060080001c040c1c00c00c209903003d10140c0d818499420580d40c1d8400086041c00020915615000002c104140c20410302c03004103d0b522061115042130110b810340300009021040c0040d1404000890360001440030021714040903045c00100c02089800c0c2d901342d04007a6241c009400100300c2400815070f040081d00002c251070401c0314100f4403281d416554011280030083d49410348400800450b9503403c4400c040320740a0030414440810f04900c0380c01c140180a45551086c606000411200303800009112010720a4270103115545070101085200c0c041c880d1840700080040006005ea0015480469007040360700c4116441c004865002410b03200b05900704041ca402c0150003085280d40c1400781c00f601c0003240e1040b05515090000c0041980c11910049041c082c40e0034120782151802d601c2140f603402c5484480038502d2648280e251039034130940301d98001821500100d00c90130410721850b5091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 264853201 1250 264851951 264851953
    0xb070905060906070609080a05040815010515090d0b0115030608061501140d0603061406040b010f050a09090608010e0606030d08010302100302070605070f03060803070b13020d050327040e 82
    0x1c068100308200060303000d1201185c12980350908040003a00c5940500f51341d04254854503141d60a1014040c50400c0f05480320412280c0e4000402c4541c80c0d5925208100d801070341d0341507886103d4004101c2081820701300420b0b1560b58400042c42c0082d03001080d210861656050000d030383e84030b030ba0550b00d900958560000600e03486031680c80750b011707640c2c0c6070b52003501030052401c081441d5460b100302c640a91059880f2a2660b01c0c641240200c101896480541203404026005840c4002801880805100428000c1c00225244c100e80611501002044165818411151039090680c017918046040401d988180c1001c220709140114141c1f61801b03d81d0340e9061160300c0c680800498458891030001415800c101c42c001003210360203194442c0c80d00743c64400d5011081600107003142e003d43d00c40c07003807a00107022001c000340880e000c1c0d6400807240e0410100321522800010315000340600000c02074800000c1030b0040700301144c80e9101112207400d00c890f0009019050000743d0b01e002d5031004007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 264854451 1250 264853201 264853207
    0x906080106090e0c16080f07030810030302030d05070e04060305010e0d0c1a190509061006020304061b080d1b0306140105030133020a0b0a020406020a20030d0c0b07090506 75
    0xc0240598090040c002030715001d06401d20098a1b4141a40d11100c3c551030100b42c00030f048000d054001858682042440c1100c82d19241307903460094a0340200004131800d5234071400424039281c40341401ea200e0243c0107104002c055501c0c5081030007040e002c0d10f18851030007404200d050341401628041c4035550000c09198180310302c030780800c1000200421521800802200d000445041c03072280d180714034800c2c40100041e0800510740900c08500749d00450442d0f10400c0103100441e400310103181c001f1448100100c0c0f400c580d181c5101c080c0100f0004511840c500790580318002040c1d02d40c401001401d84041020546a80100d07925014404069010803410801000200042c40036110302403107020500c2140440f1001c0703e08803070355050413280140d102c2500d00080c00003c450482e04442c0300074003146400d142c0400651140e0400c6070151442216810003c90b190284007108409c00700181518800e0703031025000350103c6005a07040d24071902e0350300024041401b40d0b024506a07140202440d007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 264855701 1250 264854451 264854461
    0xf12040303020c1c0803070c060614040b120c040c0c140c12030702010221070b01060306090c0207050901060f02070e10032001020a06020f0c0303010927080909040c0e04030906080106090e 82
    0x7400e580058042400c104640d4000c8d004200c107842018042c016014408504807880d41c01c1006941940e1800c0c0d20441d11040107400b070501c00181d2180c0342c0e0040d0340114140183d80010f071410050a200070b800d40e081115121021803002c9040d112421044a404421010654815503a0300805500038003581c8010245c0d054890a02e00ca215450141074000c4e01d850ba03a9513501000030300030384c000c10101c0c1e1141d0080c0042e5486000e1800080127520007030002903c1e040006006000600c102401c1c090030090740ca484a2082c02007a0140100800301074050506012540f0400824401604d072190b20185181c054000c4400c07030503484070140d0051251400b0b030f8661100960000b1102c00c50180100f0202c904c00500b400070318002e0040c08030004105490540001c48411071150800000d000c26440d00009101e41c1e003900c0f400c403001e03101c498140d0358a25103003211591030b81082c5c8108112004002c20545d000c801007040ccc402d15580c001c180c1c0d0762094145d070000041e0140010305265a40098 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 264856951 1250 264855701 264855713
    0x1501060c03030f110c010614010c0b060f0f10020c030625030e070f06030b0f2b02030304030c0e0414071503020c0c1908010605010905010e0f01020f12040303020c1c 72
    0x11000031608003000504c20f010b00903801072036014020301040e50351144030400c01300503400d041000c884800e080003851003096aa940303000d8200140941d02c1070b512070f00e0400c8242c035483d140a454400242005600c0e40c91120b0180d621000044c44500c03921607038002444104a807840c2140103590034190560040500c50140c0141c0a41003400fa035030720403024000f51080200d56410003e1505441c00140d0400c207009002013124594141d41c01004150151001100d4440e00441d540304410540c0508842074400281140320301d0340b001e000720702c079a1004950f000280d100540030710b21401916020190407a082e6460701418032a403902c581070032130700c8100d190080d00104000b040290590b041c26101030300299171950898443c4544212140b8280710a00302403103071101514003400c10320748071854500001d18080383c104819000d41c2140150b994141d00811100c04606030080070b656103038101e415015000d41252006800511a06c411034000e400c000b807a80882300340d183d1641000d01c0c56904d40c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 264858201 1250 264856951 264856961
    0x606030921020f0106060e090a020403021810050a030303021207082e0305010e071a040810090503070606140f0f03030306010305041b08070515090d02130e010e07081501060c0303 78
    0x100041d4000c0f00c01010010000f0310424000d0401a00c86183c603d2011060200c000001002070708014070410007800036a1310710360444e0279003244403040d214a41e02c489540c01e01c01c4541d0700454009241d403601200f010780540103030001c2e11001c40001c84e03030b03a2604012254248252090b01c070112904003043c421101d668158003141c22030146250b0915500d035665801c4507164150030606070401081071182c942c040304c20364031043e8a00b00c054207190030b080f4400c7d181e100800d01441c0c01991900b0103000c205081c42503030050307504040c1c00c200f8141d445183d072804c0d284a005c03591044000002030006403804080b10714243c0300280084d800d40d598540190005d10000c5c00c203079039164240c1036000c0c0d605580003150000e00410070190943e20700c0e1400303000d4410001d21101480c00001e00200d17010751680044004043c1d0111001d40b112a810401c2400504031a4403018040d400e01e06804403401001450100702c90f000742c02c0320480303206000c00340d5400c1d90030300410000441c1d0600200102c1c1c461307001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 264859451 1250 264858201 264858263
    0x406020904020705161d040c050d11030d0801030204050a06030302060f070207030c060c06050a0203010b0901120b060f03090f01110d0b0a0b12040b071b020d080f0c0f0106060309 78
    0x51400e44107840d00c602d00085c003001520009218903040c04108003008000789400d800d0740300e2035900d0400c0d59604041148502580740910a078040c244240000d41e015030001c69009400d8a00301044104000c044100034042a4084d03400e000c045062001244079081c02c0f03981507030240c00c031a1a294003200c1c40040c05041c1104503c5415070200100c0c000d885104000d103415203400e4007030300c850300d490019500c008100c00740b05441400100140702c110411200358110928005011108000411009000d01e41e4120b400001c04201021603c03103200c011802051030b00300310344088034160b000c24207032803105050201000c4144241000d16210b500010000309000f130a2491043d1034110480c203a80007200d01940c0310070b6a030140410f11035184a51600410286071500601a2a1002200710481584000c3c05031072103203880e4081c8203402044c2c5100301c003181507080e624000c2c01d655070f940b82c4010070521105d51800d80000f0300d8034068814090101c1e4080f014500c012961010f9400d0340c110460 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 264860701 1250 264859451 264859459
    0x7080d0609020301060903050606040b0d150e060a09110306041e15050403270602030406050741010c120b030f1c03150b0f09010203130e161704060209 66
    0x90081458002400618041d102d21b580e83c5400c00d06d10306010789007200c09450b01d030003940380c00308981840d141e114454041580001890522503141040b58000f003102c2c4001c108a80511011b10154803196000701507214068580900811866010162500e009990040461500102d01c90740400040070644810380500980504501450340c0310080e03130310071103040780010020180420345500765214450100160b5480d003a40e079090140195591103540101c8d0107220001c140a8100404030034004014066062640001415880c0ca001d0000100300320118074609403421091091051050440c10001c9a5030441c901001140501c014804040c0b050340500800c408100108820400010240c0b45041c5c29169088460001012150000c05410211030345203000c12450604500351189100784150b1555200c091500503450340c82000724420700f1500c03c1c0070004171028007441c0703d84580c01c980700480740c81450280445201510682005000c01c1080105002c140507a000d0001254094 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 264861951 1250 264860701 264860711
    0xb0a0819020d060e160903150e120a0207081506010c020d02180a061221030b1504060f03050415050406021b03030402030c01020c0105120618011d0c0f07080d 69
    0x2060581640e000e1001410040c0d10f40f1420000e00c03018020702e03a440080070040885800c01c0210003080c0e10b0340c500c00604141420078140c130b4900176540c010f0540c40c940307508440000442002214040c0c0110029401500440340e001402507000315040300b0140f0054480c880c1680c07600c1c01503810328503928003a6004030080c11620016114644005c540c0c40ba007810a4043c2c1c41c01e0a692000da82e40e6400c200300c00c0241c01e202800052000f81212000d01c40360a90347d1a03400d0303414003140244040d0108039804145090040f001d50300b1640203200b5070300c1c20b0b920407540321030040c000d42c1aa01c0588000300514481c801d4186900200d500190f0007502c1400003503c1c05200403054501c800001d2100d00740d5800000902c0300314034003040461180c400c280090080c1200c07080c0080d000d8065064094484200b4034000740140e52600344661240005c84804086135071601c00414602080b03580c10120a8140300101c1d28400e100b80a03150760303541d00e0000a02d4516140d480400e03541103240b820b109291a4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 264863201 1250 264861951 264861991
    0xd1704050102041802070203010e0705011205060303090604031202010509010504170a0e0406080106080114040b0103081809040809270c090f0a120b0106090e0a051f14030706090b0a08 80
    0x2084c2800000f80d1000c0540c661501e80101401c568103d0220788195000000030049660807123001e14500c0e00b0304600144a80d5030b807021904600c120208280e100100141c0403041005d014412496280c240d4020051580d60b512a40d00702c0b002034902400c03005410441b1010052418018004c4814914203c5001032801d008102560f15a40041c00242d442d220f0a2001d2502407145290401d88080004024201074950480e030500602020306080c40010302c516180c0c2c804541e1070140c40c0058090b41152a040c100b080362600700140040c0b00305a40081c0d44240107540210700d2507800d601d0f90402403512003d0020500703a10124016030444803e0ba02d8040c07640c0e4103d101001404911a001502c0c905458403134100c0e04140c12480601000c0301c0d040c0042e0240c00c102d00d5100c02c20341d0f0001034589851090481d00500c80b00c118401c546801c802066a05410b1080d0103c200f00b035080b22891512a10203464610f007600440c800a10240080c900c014031030100c440e00a0410f0390a01c51207940313 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 264864451 1250 264863201 264863219
    0x103090606030b0a2409020c0a080406090f270507020c060f030103060b1c1b0504050a0e06160c060c09030b041a0115053406060e090d170405010204 65
    0x20a90042d201403030301504000705800980201c010080550783e8840c5e40e0202c42d4031a5641d04e5890207624010395021a013500c0d00c0d1b000304410011643c00c1590707140c0380d903620600200b203403829014008c803d440300e8500050804400c039041c100002035040800e03203c103044c80e4420003040010056021445140c40c2c0d00382039110796009250381e0000310240c9950703604608280c41503c950f82e41c102c0c002d00703600d00c0324003c5000000d0070f5101d03160304c11300d0000018942030381080301d000550041507100b4500414891214666404403022290a00540e139a542e12048000e000024851288012460300c0003050001412a484401601c2440c18400350482d120303107501084002c1220308a682800000420003018558010140107002d6007402405031602e045000782315000f110684031900c16a800392180803000c898900c0c450206c214001a180c0c0c10a0a101010300118820840000ca01c43d010451044001c03030040c00300d04454407180147e01024101081c0c0b110300074015034282d5802d02010510440c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 264865701 1250 264864451 264864461
    0x41103030f0c2a010207031202100f0906050a06060905061b061603151d130203030c15010e0c07020d1109040b090f010501080606011d0927010513080901030906 70
    0x2140e00700030003880300c0c048403401a210948000075001e0700a0820000141e07030009001b01621380c031038040419a00b400e00246d11b07103440c0b0740c00ca202040c1031440b200381f1951644e1180c0d10690140c2010310a40d2104120001203c0c0c250144e0030000311480c000380b22509001340100550081c885481d502d000d10030200d40e050000594034000900503403045441c01c40d5242c007402a0102e0349580000401d4a0b100d410050303848842e4082107001c612800150034104c0001c00b5103070454001c0d0680340d96086189429460307906c82c11704103180c031884a0020451002400d483c9204183e20802940380446a03002c02c01d1255400104075090b1070701145111f510307210721007030900584c45907950643d2401c2914841c4e0070071015070a0481141e241000411440318001491a0021420b00301218400d0040c80700840382c4845800c0ca541041d902c40034810800c1030351481c090403c500d8070310040f031003840d4a200b600742d83c801d88036014220704045020380801c4400f00100002d0005040c0007480030601e60390700341038070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 264866951 1250 264865701 264865717
    0x5030127020a03090b010905070518041b0302041d0603070506071e1a1f06110f010e030901020c12030a0e010903050a03020c03010c0903170f2a0705060a0206041103030f 74
    0x83e81301c080d010204030042070300b2405003e440d074061001c5d00c1c04040c001d01501038240c1260f0255403105991000e525194042100c1803684007080b045c0c0902c02401030082c0d440740c0f09101c0300000010341c2d645140d140e05051401904010043d02c230092030501004003e4010100c1035403003c0890885000102c00301a004402ca40701e4522140340904078078404e005100c00900d81060202c11100040100000b0740f50a400d82d010760a02d100040c44092025160036110900080700e50701e00090301201040000c06000914001d0f42120220ba0400c010302140441044540c18a0750080c40703e10050390042e1404189080185030500e585030760780d1121846c150100748280c0168004080201040c1070038020115070040d03a0400d0800c241c5103541e04035200300e054007206040d00c80031500e400c00c50803103402c803080b101c01c0d01b0320440c001300084403900388005004107108050bc100c0303d0002d450b08000c0c0c103480c0015803c0e00a82050f40d07039521207651405090403c10351502040061118881d01d0001512601d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 264868201 1250 264866951 264866957
    0xc04150906031a06030a05041e0813140d03050c0a12030504060b0105090f090406020c1c091d0f070c050708011d0601050306010b0c011b0e130c05030127020a 69
    0x2240303044405811100410700101c83c1880d81c480b4901e560711444c084036006481c0c42000034196881c0c1c1085e0302801081c8800b440203004800a102c00c0c03001240180110034040d80c2c100b101c9a55400e00e9204580304140b84541020000d603242000c41e0085000d04290300011382136a0043c1407070b940d007088190502040501007a56a014002880304a11a0200f109000e0800c50b00d8060b1110000d10242c008585040c800c1990318001010884280c050302c0351010503c00707c0315019401d03003c10a08070a007580c4240028040d02000869510b80310005585208014001d00a45c6403501705a5070782c08010409010b01102206120006404118131001868224000a0918401d808825141d0345400c40307440c07142e1042006101559002c900241101c2e003184050f5510748407d22411302402e11100640002203c4100403005c417600040a103ca0300401c440c2c240d0104000b032040c0c0c00f1510452124400500e0a0006018500840b0707402c5032060465144c516000c10300c0d0300040300b60780c8500c03820000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 264869451 1250 264868201 264868217
    0x2009011211010306061e02010204030804090915090b0114061306050d0b010c120507150608060612010c080601110a05010218030705270a06030602030702010e0c10080a050c0415 77
    0x41c4030048150301da56400c246030501007540760030401000400b0801d400d100c20044090742c080d54a000354103d400442e88181c0e003a80761941c5903c66001014011001d507820704442c5000444c0c041c9c0c1d0300c240620a0380c003c10344c90241c0d0914803c078040440c11b55219030841801c0024002a403007a408031030041005584055a0f07c1c088062201550014041c041c18000303104800000510b007924804403060880c030700319840c1d00c010b04280441041000c118904149001c1c8046891000440c00c075204660a4400b14144280c202005080341c1100b151540080c040502080f13896210b40a00e0301c28101500880e82090b62a48580c2e007280d000011a014010b0101c000340e216040520480b00104001c81c0e0040050082c07a20b814000500710540b450391213460030000d0645821a0b00503005560400700c21900d0385083c0101a0080c00381c4180b0072800e00c40c0f400070307540d207103818216620759000d02d6848078000e07140c0841c403902421004d001594620024080400d00324160f03504c5010b803030312954039565 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 264870701 1250 264869451 264869453
    0x40e040b070f020307020d0602091c0c08010c0903050a030818030414090105060a0f031e05190f020301120212010902030a0305041e061d030c0316030605060604030f20090112 76
    0xc4000c1d5205030b01c01c01e64005000080150740c905d04815459900302d4400740e40c3d51101c07000969000c203a042459a41041d0540c61030030301902507120002c2e600c10000070840001000b005642203205032100800700c0d4044202e0200080c8213400094204114490f4400310441d0750414a080d42c025801103a0558241c00c00c4042c0b500c0c2c504101401031a086e1501071030101d840100410302007032041081c0070303d600d40700002d2162101400c0c100410100c4c040400c03207404d05140f000607032256400701003003841c14105000414880c078404ca80c100c0300e0302c0390145491801075083c8812841081e03048903c1d5580d8000100240e01c05100510740c0030b2096072644c1e901c03810304184c0010b41c0807095100c24644842d0b2010720800350894180502c1601e01c44030000110040c3c000240b0b405000300e0701036010f015450543e89944104d09900741071344c0c814842400555036070424000b6a004612000e0089504050224041000c5c0441540f000b6114042603041048001c0402c503001000e07400a882c0001000c4500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 264871951 1250 264870701 264870707
    0x70f08090a090609020c070506090609090712021c050a1a0d02060403081201051221070219080106061b20030f0604080306120606210309030105090a0218010b180105040e040b07 77
    0x200a003004403440341c24250350b003001c100a330081c0740210b4061000b18010546860244080b4007102c080a0025581e0301c80600304003003403100401c20740041c2b904150200c1c480c4c07001400741418a041114a52020800c200204001805c0410059800c40b0b410080440440d80200042a10001c500070407800c551414003403003224411604a00b1094014a8000505000a2402d07420001b840d0042da9100c1c42c1500014444100e41b00c40c01c41d171805220000a0814070641086003259155145e14007011009203c101146804000090490b109084441c0b402011041014403003913029048446000d80401038502e4400d09036402c1c1d03281d03400481084000d1400001d00ba0190075000003800307450401101051001800050800c4010f032445820705030280d0810980b003405100800034400350510041d00f540315122038100ba40245040528241502c01c00062a23048030407801c01e00d403800c00b15010501d50a070400da05141042801c010000780d0005c1c500b56a0300a602030340104480d41411440a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 264873201 1250 264871951 264871963
    0x12010504020f06070c03030309150212010302030d0f05030c0f0708040e060a21020121060e0604050c0408030d0b03010b131d210304020a030b010e040b0c070f08090a090609020c 77
    0xda00c10300c070410031a000541c1d071714030b00c0f802caa51500b000f04032a20640340c4048403904645d0344400051020a1030071800e61403d1629048a000740c00b0340c0c00365507095001710b41041840e680a8007054040011580604e1180b0080480c6e600e01c00e0002c0c204a201d41d580c800079400384e40542441c034415400d00c13640d440c084030f0003801882c1181e1800c1c140c610b074610a4540500004021341440b04407400c448680e201da10749030b00d5100d130203101009000e450b5442e1078409201030340c074036004600d0040000c085450399000c0b101a11a004000e5040c045a072110401a001e9110b005401d0354072030b949080f40d5242d4203441110003c02100100340109095840304a401c2d46145201e220f0340070685803241c820b4070044580000400581d0135130f0ba80d035140049802c0818641c03008052150040001807032103003031030000b80140d104080144850321510f081c20000e0168000250240c502e0204840014200d440203002015000d48110b91389a520072030142120100d034000d40b00301e900041c8518001d1014085 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 264874451 1250 264873201 264873229
    0x150c0f060a0c08010315060305100c200c121c050d0b01030c09050105250503070506090c030c04050a24060e271b070804061707020a0305181201050402 66
    0x4100b0094101c0030000300103060621000d8400f84501c4454510702400380c002c5005076401a0440c1c1507001b40083c2000280031142c40b900025000c40010000b610202100491f01c80d100c030024201800b000d010000c110b285204190b205200700c06c400300c0580022014001da0043c02d0321a540c40711103000c00842501c1c51007181c0343c10140f8168071020284d070042c16010a0314801c2c03904548075969007913940400c085004e05000050500f044600c100100040206521440f41c0c043d04c003d0b88480d01079954504440300821785c550060328881019040c130b43e006943c01000a2400316007901e0b0300d03100390070b41010707091241b001c018100d10502c0499044068035064200030340720a0780d00303c400b1484c803030b15451014408103550914030224806c01951b902440d800314001e05465a142982e1500c8134a0754441c2c45110085100640d25102403143d000c0d0451140c0960740107002c14110907602200c0320350144040000035485162100455160f890601040001e042c000044500b4540104901c5290140c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 264875701 1250 264874451 264874471
    0x9060c0f0503041505071404120c12031403070309061a15090d0f030302090604180b06040302102f01050a0501080604031b0317400f02150c0f06 63
    0x9200000d00c0113203059208030100040094180c4038034804072004c03485403000c215541804103000c140c13404c282c040c54400301e01c41c9a104001c00d50f0b500502042423160321018010038549400b80c900d25244d00011980111285400112009036a84100846050442911240114041d04019400c06803407100c101c030b00c4211203e05016648001425400c19110002e00b508400f0001404040c0a5010b407503451800900160701c7e991141c0c8981b91241240240010306801d1481c1e040160034038100302d50035260054044c1801840b40d05003911660450142220b0080840140203d415180c80820300410401e000105140c203011404106a03001070f004403641e80c10090500c40040d822041da444c842400f0009109149010304081d2209140d0400d40c481e000160320400c864200d80314030141210552480e204808694500c0d0900d074076500358002641604000600c10200c0c0c10032002180191004000e034202100c2d0b110001d02d103821414403410180e2145c0c14902d03c0d0700e018006c0c14be101c510a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 264876951 1250 264875701 264875707
    0x60601020105160c02030312010b030703140709050105131802090f032d0f07030c0302030d030506091b040b0706020408060705090d030305060301090507171203010b03062209060c0f05 80
    0x90342c140610010700ca01e40c818440c0700f00f403400c05c54800b03005582888540c802814159a9641000b004a0740100c0344000042d1908422058032460020b82c54010f0503179980f4090618141001550654800000c040f124101d401c800a40490003c0c0d115000e05030130316016840321422424040005040d200700d42c803d0300400240c0416502103202c0e42d00381107030990044c40040d0f44410203820072114003201a12030080440100c10f102011075400200d03442901140c078000d078100411001c564094803100d40c44000200803501d900d282c40c0309100200c0c2404411442c1c44d070744001c070f41c260f80d1100d1011103401d500894100014001406503503403103da1401e00c0b901c2c3c41c04002c0090448600c01c100141815680c8002c40c0d95610254801d800b401c3c0d100c02210f070f40945800c000502004400c031229514499100d110001c00710840507281224459404c036070440c3c80751f6082003120900c800c13101070071548202110184a209019460b281c0d4020400055940c024100045c9050b04100a18051003020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 264878201 1250 264876951 264876961
    0x112091209050a1503051e0421051c0c02150a1d12121302060307030905010507020109021c110924010f020613110303040906090e0a0b010e06040626060601020105 71
    0x20000c1c668000045280009a690301c803445441107c04107081c000003070b182c0c14200810041140c00600c4010010808951580300d1a2411111440b0f043d9010000c0701b2441d03220f001c0070205400c0b24920301d40a005480511001d00c42c8566442c0048489404964441d80040d0421407800b0120210b007050b00301400b10a0030916a0320524030880d84e244600d08404400034804041c2411070030324090380201411366a08041b0b4005014103940e400c166915480e10010a884500520564612650181c212800d01000312064440c20b00110300640c0c1c100105039068000c0c1d230311041180e00c00d5404800c4129100c1e41e0f213120580c4014100350b2541405400c146580009400080c1954001c6d51003c054561851031b2030705a400b84403880909405200200e40030850f002d068104c0420340b030300138400f003196030958400985c0d1207805e40c10203003813040780b8001400307008548002154451009000429000e60350601e42c20002e495401a81002840c001c40d00350803402480703603a8100d142407000b40704074100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 264879451 1250 264878201 264878219
    0x2210105041404080f03040c090e0f0705040c0c0b0a020c030a320f070c030b07050403061404121202040f0902030720031801031508010914030c0d0c020112091209050a 73
    0x178540c0c500748402d4044000ba0401c9100000b81020f042e403103c0601401c200c0060490342c90507209440f0100340200c01001c205410548a143c901400340e55407081c01e25241d49445054200c0541030b0540c070f0f6002c028030011881c0c200014050320000d80e460310303000940b0030f820040002c0e044d0380303800500d0045ea02074518841f00100341c17002045002850340d84d0b800a80780510300e8107003640c0000c002c04501d03010405034680200240045900641c1d09011014880a00090a002c00c9034014049040310b20080100d510900044050720340c217100052600c1d454a000030205580c3c1d510101c17026800004014410358445032a1864201601c54480c5e4030304088003240c1c0740e0003043d200706a040e006035000e194580c4642c000070100000408804d82141d00e0701000b90103401131440035660404601d0030241d107484008110307000700c0100c2c0003600c103001c401441262019400241641000208240b902025406100f84841c4520038090003919603001d89016008400551120b4450500104108841c580b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 264880701 1250 264879451 264879457
    0x306030f120306060a120c09090e060c071202070806161101090c03060f0b0406030c060207120c060e130e0601063b2101020405041812080a0221010504140408 69
    0x150880c2c1c801c4d22a0285e5001701c2d811440e503802030041c079041041503203e4035041303074503401950391854090001d83c80c0d03001c61070ba03070b49025a10658803039002c01441010a10f10000c1c01c0301118544180d030f1008da51558010716218041e91980c0b80710700c0c0002230b10040340d0410442c440c200302580003404881a51340355030350b01c50110302c000340a0300c0e103860032a807900a4640c0038003100d540060042050903180d05040c042d185560051a02601c5070310300114180c0142c0002c42103256004050700c0c420307814000200c92154800c1c40360354100c043d41c013001c0350302309181c05100d40076032201c4000c0600750b260030380081006004503285880c110a4079103c525143d00042e544006040c0310481403003221209000c02c1011940701c10328028502440c4902c2a000810b400900881c0e00480d028401441c080442a2500002050040c0b0034102c140c4520003043c002c2c0c07201039012040d0f500041c20714203400886280d0061440e01600745005a600520107481e240c8a40110f406c42c290050f0414035181d914014148 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 264881951 1250 264880701 264880711
    0x7120b1f031505100c0c08030301030822170309010801050604050d170c150a06061e0305070e03030409060302010207080715050f04090c0c110d02012010110306030f1203 74
    0x68507842840320011168509000400010740958204d080c3da54000704500e180c00d03021144404003070000150704d0360000a40303040c7d9410002c081e190040c96516030041e4040b103414010039090601001482c2c815051142c0038442203000555582c50124000405c500c2d0305030003807481038105100c1030125495015103080400d501421900c18448a080c96071194007400307001d16060700c2058203c0701c2c18aa41a00d01e80900d41140c8140016500c51030241c400e5481b80042d278400349288000c0415403446508000e4020f041404c240c0c410914242c0402c0c1903900c140c20007501951554be04004550741008802c009000b220040c040050410805c0d00034140001c410f00100324020a600c0101808401201c0092001c0e81c003c0200304c0e003644000d8002b412a100a8501a9503541256840d090041c2c0000070543e0503500d44110015000e41501550200071b040409481140d5003040d00c07032503d1265000070301d45942050740781d1a00000701494041405012041500001c52011070f0361400003e684d006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 264883201 1250 264881951 264881957
    0x90c0112060503030d1d06061005030618090105180c0d0609020a0803040305100b0402090310020318060c071e1703060d080316030b0406050f0402090604050907120b1f 73
    0x21000103211030060242500003d9141c0030006103d891000b85e40d021340d506101032080062170380d542984032626110129152600b0007c04045101e90b2403240004503404000246080540f0b041042c4402c1c031000c0480f06060507a54603020f020301031128154960328108600c00408030040d00802040b0020700000c0c0080000b51208003410440d2795103500000a4181d1904490b1216074a090a030340e512661007150680524140c00301d0903a080500840c0c041c1d03000940100001001c24010000a601c018a0582102113800c40e0744241d1741d0601034031740100f1090070950b44800c81818550f0362a030021740c15001c0c031050a24400c0020740c40e8040c181100210411560f140e5540c00045001000c0d64a0010301d00361000040040303258a40d0303004284000150380070480d59101e00b092000b2070b2894050385510959443c00c0c1d08042c941a0020015040301404090500313588801041d90300900b80c58180100ba4900365040c0c01c11894400c0e05801c850441d440164000070500780c010100c2c21845017810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 264884451 1250 264883201 264883217
    0x150e04050601170f040b0f010b1206030c0d08130b070c0b160f060c0e040e030409020306030705040c0c170703120507031b05120f0705160c050310020405040c08090c01 73
    0x1941c0e00034040040303981200c031183c91161400d582c0074007580c0c20403101115008003282c045000365099a000a05881c08130f01aa841d12075030780450400301d04010b0141d5814413402c4841c88031034964032038010026108082142c1c59801255015502e08115008080001001e010750004541e00180d04011902c000f0a444d81d00c004000703c0c04205030303000301e01070440d0360101e920004020709a4000c66000c11203940d8000107540c084100010748102168541840e4014402801260850790045400c00401011103610f00e41c0c0300003040c182e070766042200020400002c0208144621400e5140c9080d0787d4043d203900c4c2410a55001c0c2c003840f0607500034440c1c140e564000035115806507109a9862041c0300300c1641c5401003402c01041940305403816410071880e04c020503200030400030241e0140c14075490f03003800d01c02d888091010701010464290b40b0400d4103c40041e80e41c90a11014811818201003d03030744504000c10701098610802000b0108015242004200b40c0040354000402c035003442d01c504 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 264885701 1250 264884451 264884461
    0x5070c0905010f06030506040c09090c0507050a0c0f0b0c030d05040609020a030c090e03091c0201090308040905011d0613050c040b1804050601020d0c0b0406060e04030c0606150e0405 80
    0x401140a4020044040c0341c200080f4803140303400034100071a8060750341400290340e03010a00003a01d40102500011603220710050101010316040469902401d00d0460f003480010b44580e850300722080001d98006680b1b01e420b10081020461140c00b90603409402e5190410f401121540ca115014064180315918008681041840e421036440c0c550014180001aa282d04180b44882d0461140809051030019030001e22007010081d54a0008010200b10541100381e00e10b034107129001108038100804980c0210005681401900240030b141000003081d40c10010384408031507610b95010100c0ca0f070306c0100003459644403848510000e202c4000314150725160b10115450081d07403c094602e0034041100c200c00d07107441c4418500b01c00115007e02c0540c0790a0011390302c030241222800700080d2680703042c50205615501c901d402c0f9210700000200e00e0b584040c49400d032002628100c0020703200b00090400c0c0319050040a000e0010252003207040000901701414640e00c4408031401070b6250000a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 264886951 1250 264885701 264885713
    0x3040809010e100305150a030b0103080a051b0705090c070b16030605060c01021e03040203071a12091e01020906090d0c0806180607080c09040506040b19031502190507 73
    0x4034041d0014020f295010300541029016140c119449801d650340100000303098580201c4520490f40c019004024590850302ca41c246948009011824000200f0851403214000801000020940005080c0541c1031a040241231003001d000070309071400a0203904045500e0920240e001308200080b4142005003400603005001c0c1e44d400290b000d070010074045032101040d0010402c9071700c0100d410b042298402100507441c0416500a034240e88405404d125401840d14030240f0004840c2c0b1305070506015480180003000300710b84a0440f074200e4002701e40104c45c003210069280624000a508198000c0d021985602130310140c140f2030391083e2421802d00071a00d00c40805040c04005540e01c82c681103511000d5042141d4030242140700b124001040a84180c6000e8095032202441600d0600300c0001c000240002a0544c0d60151b694071098209549030480d0004134445072510740906072541c00c140b082c08425006403000b0034010402040328030b900c005540006001828059161121400c080b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 264888201 1250 264886951 264886967
    0x411122703090f010f090906082811060a0e09010f170d08160306152706050f07140f1e0601030203060406050c0d060303030f0f0b09041410090609030e0a08030304080901 74
    0x4120042c0390180c0842e007150003040340060152080a40300b040d1b0ac01009085c0300c464440009040410011103981442c54004024580c0d20101d181c0652202c25890000d5410700003a8020b504c1c0320b10b1403c2c104281c1402c40b90181d4207008900142001e8480c0c0c60005d001110f00030300c0c3c503446494035414440e02501a500500141c1008000240f030101c1910740030b00310b42c40200e01307818038581078090055400701694000c41a0707480c80d901d490070802451650300147c4c00503d02102e0340c0454440000815030104007803154055a4001011242e090801a0722600e008040701c0c807032504032000500c09a1000503c02e504140c1c418000078860741c49035050081c600944050b0100c0504065000003415410f81040c0b541114810f0100104001c26042d002116909812607410240460005021552091501455000110a950420119216000c05c940c00007200302e801aa40314064801e00d5801450b0a444003025900c01448504000c2907030b0703413800001d00007005601c0004407425183d11582074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 264889451 1250 264888201 264888209
    0x8070201020c060405010902180114062b091403040e0f0c190203030402010801090e1908040504230603030c061906030f0b041a0c090411122703090f010f09 68
    0x19242c4030f0801d840c001b0301070121003205074070902d40f01060b0362004120340c400700e04848511040d180e82100c81d40c00d102184c0c0001c3c0080d501980a48900c40d00f400d40360a0302a59500d001d40000341d44403c0340782c041000c885500402c445540144014001510b600c170343e41d03422901e1003503240c0f503e0381c444c4079150700c5210f80e0080c009000060010034105030303000400f45015520076200d1143c160f80301c40050044520708010000c480c2d020501d410307400b100c0c5650404283c1d004fd400b00d0b00d05515440424191219071024000d1900ba8a0421b916840003500c15504880103e01070761501c034400f200c0d0ba13910040907050030b902d6071410081c1c41d17100c80242d10002c010341d130040359041035140e642030050303084000700c4043e00c030038090400340e0410880c4001000e1041c0107091029051210140611000f0500c000040d007154000f009098103160045001e0392058110040b55500000301c949000741c601000c11002c030b8994424000402c080c0d1b42ea0748100d000220030f1820004113100440100c0b07803403002d544 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 264890701 1250 264889451 264889453
    0x90209061e04090c02030c191113090804180f050103020a0b030903040306050f09010e070323071802091e180a0902130b01110309030706051c02040b0403020906010318020108070201020c 81
    0x13070301000c41d4002c405400e01c8030710007003503070321000950260040182a021000700340303456600510307030f99140480108070003200012001503a906590340702807240c2d015400c16003040ea100b0b42c411191480720301584050728078030001070103a5491136002c56000c122500588450442c0880060403441040083d10001e6410840c10b0040d41004985103142880985000116500b0000316078000340000840c40f048a5210406a9091049040e41075568044002141803402802c0303000a10002106c040c80c413103241d0302001a40c5044600810100013901c0c07004550740144d02d4410a403550725002e60300090710740150404c55654811600c0002015031500c0294440c0d41d00c1c0c060750501c0802d502c0181000000c2c0c844a5154080f06625580da009000350b495055000c6030041c40761502c5a005813440c1b602250314003501100043c00002030343c110340c209000c40c1c1408103007002545402c2c20b08503003105080c00c08002090a01002852070007800300b010303043c410300e000840c2410b4401d504a6880c101248 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 264891951 1250 264890701 264890711
    0x1201020a0c1104020c070311010207080604080903070609080705060706230a06050d08030c090409050304061806050301061d0121050a14130f050a02040207050f0601090209061e0409 79
    0x1003405460380c188800300b03580c1c2940e105071541c2a81010b1007100c0b102c136030b11001010820f02d140d48940c40349413401d1203d4110302a402c00028509800c004841c041da10882410742c480c5648824907103025070681c4070342c04001124408000c02e10340401d61078155141130300e1507135403001c8074100f03500a000e416010400d261a40700c280f444005441c0e00080c06184101c5080c0700310fa60f00c00c01c0000301905003401500000c4200b001c55541543c2c00c000b0030604001038400b00d40815240c03100e034215041544010040344000c2c0e16808590200b0214030041c041078203201d411541002e40041003a149d201f19a0381001007001e100045030f02803032100490540e00380c032103980ca28280050f90701400b015611700c030b80e2504002500b440c010503d990148108481c1c049880f404c0134a450b800c108091108050303070340b409048144009612140000d254a6014030001c0c03141c1700207400a203281070016071080c1c0c0c0b030501c14017034100103984440440b601c02c90310441000b607000c4a200100b103d440b0b41d80c02690454900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 264893201 1250 264891951 264891967
    0x31b030304050c12030f0c0f03190305090706080a020a270305010608010908090d03030e0d052104050d200703032705090f0406090203060703151a0409020702120102 72
    0x203521891040e0151150600d2980a0040350011040c00b81d00d9504144443d0b01c10100170406080e202c04001d04540003d800000004e0540c0d01c42286842a1380101542c662029010f000301d0ba040000003008044551404070000c2240c00041d000d04400e42d000a080300f6102c0c403030a807078031010130100140b180a20114000c4c02c0304c80000e01c82210154200003001900d0181881404501900000c4280c9840600320401070340700c0c0500c40480034942d94074141503001a081158079260400d40d100c0079030b6040340c01810025510040b0100e10148481020800041d03000b04114081312003d0820409542c1c881031080500c0903000c049030301c60321030088008140343c2e0121160052041c124005110130700032000f100d194541da8015039800c5286d5902040b4581040d030201903205000c0c590025a034a510f50000e81426826111100001d458081101a410203d180c0a0040100c0c03c0210310800b00c02400741524000d82c45284001a80400c4004c25916150700305861800c081000715565481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 264894451 1250 264893201 264893203
    0x2100513090e2d2a0409020f0603090a15090b070c110f0f0402070b07090602010b090619030803011503050a0608060402040504080d060806150405010620031b 69
    0x2040c200144406080100041c00101a104402044151001030700d10400d2001d0602c18250001896548500c1040d00888030310005010072580d03a20040701101d00c03a9103041020070744000c0c035440184918500100c1c0390040e0758001441c000d090f0180c2c1c0d5a40c5a07924148c40c0b90410318005005400184401d400106410159210a01061003802043d9150b207803002e080f030744160f07801c40040c40c4100707405104100d40340c40c2000c0032807154014800c039000c0b00b081d404101a80c00002040300d004070740c1414400c6032a00300000754050600b900c000c200d13510300740c000502c005001500c0507000c1e204800080100341c80b00c0e07140001443e0005030003a500d507505e91030b82c4104080c013604000000d15003808500400b000703010701c0e0216a4400014841500d0ba80c0070440207040240c0110341031201040b045104103440d020b900e005014110142c041490700288502c05040031103d1a0701c214070f014018004150024404100000e002da5103412001d0302601c3c051135449005041560481051010100944 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 264895701 1250 264894451 264894457
    0x5010f09051818030c01090b1501080a050405070f060f120213050904020a080109050d0311040e0106050a0c06150e0609040c0b0a05220303022a1012050c3006040203040807021005 78
    0x210840200b401c075540c9c0c00c9000d005542d8040380b540090b44207004035004040c00d4100d160428002c0d002d0314104d5917605411500d258940d4413880115600d1862411800d40000c906448500801c10562502901d0141021400090f0003050320402385100401c0942d01c032800b100f030140c50800c0003007100304224140a55035107010340d20040000c0c00c0c41c030035002c04452942075030100c6014060070103c43c0d003046420740c1e031a040300310100104517550350070701c000c10010301134211030100351200d28440600b4144800440c2e00028041270184c13001c84180030004d20030100d034500304d5001d4400c841d01c64000c090100c0e4684a501801c0001c0042041e8100a075448070745405c04882c825021941030710143c51011440205521170041555200c0007512090300f03150f0084103940541c2e280c154200d10644030314404940f010380e031400b800c140c0030440036204241c40c2c1001d2200b800885000030000d8820705611b50b2980300903c41c0740170303c0c1c0202c00301c0d041003800002c0d5107800340d0090480c08064403400f8000c02c160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 264896951 1250 264895701 264895703
    0xc0304120210030c020606010302251407080102040311060c03070f060204050f01030c0f031806020d060e060312040504111209060a0c170610110f0705010f09051818030c0109 76
    0x503410742c401c1a0703158024496801c0881d181c0d0040c004541c1d4a0006400130b402140804ca000201d41184450921182d00c04a03106480313580050309000581c04071038505050b81c2c225605a81c41000240049200c000100005100031111a40d4a600c4500000d0030740c01100760080000f2130a405142c104603039500900182c0c0c00c2681c2028071150084c0046080d5100d80e1041f42c0842c08841c40034503064440e80102d01c80640c1a408240c500c03166035100d108aa0100041d514402ea44542c180718041d030500c80315030000c2044004140f84105150105800d20440c49030038407641d41d0b544804e08000d001410744800c10b8075818107066a2520120054036242d0850358020542d19110344082e1003030003140d002d01c000c15201c0210403243d0f184d038203006680b405544000d0910100820550b40608100030a00d030460100380501030551424002610070f0002420305818440101d00c00d0081d62101c09501c0d050000e42e801c05c0e800d948800400082c11604501a0455030200094800d42c040054000040b42d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 264898201 1250 264896951 264896959
    0x20d050c0403020f09060a12030203030603010501080703120806010c170901171603091e0302070f050d080a0e04140106020106240c080a020c0901120210080f011206020c03041202 78
    0x80da14140c00c100c2501c541e0000a5200c82d80710700b02c0e070b41c5007840340c203881d84541b010782404860340c1c85065103003860401c0c60003240180d03c0041006050305082c000e090041071890001d14080342183e8400d03041c40b181440c448100320214002840603849507180d80c000c1c9411040840c002e251810104420b030703020040650108801c200c090144010b08044503125290307680b026101c202003401c084000c0e0400b55011b80d0304052101d4210002c00b84104124a4144643c0080c0589840c0030141e92008441d903000340d12400c8200c4095000c5181d0104a8945101d00c0c42d000f2015540c2d4400a002410003250b41d00c00c450701100080364194056000d1002e441c0095040c00b00341070340c01c042d81582c460b00010140000c010110740000104000058000405c4600644865041003c08074038502c41c09d0f0702400440d030f941075604041d420040f0402c280c010191400400600d00f401c1502d0b021507042c0f0030742c101e105c8407001d10000d02c211307641601c2c41d50480c103040c0c0e55074540d540101142d008071240300740c0c03003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 264899451 1250 264898201 264898211
    0x41e120806030705150d060512010e19020d02010f170c030108010b0303040b040e0c0f070606032a1412061017160302011b0204020c010903020106080f030403140718020d 74
    0x160780b400054290403620001c003007150280429034000721680114180078041c2e600c985002c00c0c0b9640700001c100e8114511000042d00340d001c840c208e4a4a443c40040783d10001883e91584e015880d070480030600320740c080c01e08804560187c00c0445101c2e09441070004854081c90901200d079030800c0003107040351080002484900b010700c041589174815403041a824001c100420000e0941c0d00760040d81c44074074101524144500e110301100c044c1d2045400f00c56013907480d5000e00400c04036030000800542d03203031520203c01d5852071307448644400324000c004000b80b00800c9082c1c0c556940c44003140120107081030f07501b182080c1904051680d214000c0ba4050072a6200c200c03003036600007440080c180c0301a601a1030661650b0015600031998050900e0341200d01c80c440c902613244e03400105400c1c204000005281c00c0d003810f00908403240d6400602858200710020055801c000080d00c054a820030742600c1ca2903840711149150100039030004200f280034040b5500c0588280c2d018041d813598507441484 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 264900701 1250 264899451 264899461
    0x31e08040c060906081618060203040305011802032e06060207150f2a0803011d010b0406020d20060c070311060705040303030b041e020c1b090f041e1208 67
    0x160502c910f0013540001034003d80052000d0241108210301c0040701e0814004079401e900d15541c01c2d0045410100160784000340800c1085400d200c0c0400030168910f00403d004a15400039480d141d80341d241c1d98810f1a482050041c40b0090911100d00482101c803c1240d256210800707511441c4520a5104602ca200d0003141c050b0302072000d110f0000c0d0566240c0c1d202c000c2c0c0e980503130400000c01107011402a5011342610004403d00025400b07000d0100c40c1c80c0410348107030700340c480a60058000c100a014140000c100315900080c101c48068514180300d007010840e4004042030b107401d4074050300d0a100d80010312510103130440007014a02c1c020f980d082d4500341c0c10b60740e80d40d40b03550517943c840004100f00001c00200744a5408211080002400410200035540841100e0f034403404050500d19400206140400b000300407001d2440324090401c00310400040005500080c0140543e041d004400001410092802c1c89001954512a0340250419107410520780c044ca1010703507500403c5800d00491 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 264901951 1250 264900701 264900707
    0x10b04051510120f0e060703060308160f080406030c1e0e300105100602010504110d2105030a0605010c020901060f020c03100b18041e031e08040c06 65
    0x240c42285980d4400710450356000034481c80a00300120070081180700140442010350900038046a4400840c1c040b0b5a503400c44211400e110002c3e01150605103081420400503818409071108038908a0411409010300d00380055203401510000744a05c000180111701c107900b6601034007019000c1c4da5250810b41c91450f20000c0008c1003d11b00000c9248004880414038041480c00c1075803440c044a0708000c0310002c4051305914120164545030f0351a0740030841030046540711040201040d1001748005d05141d207464400208602101c0d01071000e10b1184414050420301d02c0c1c0c0c1c02101c4040001c801c14000100415640090321030500407410010700140030340c80b9002c00302c003940c0c0041882e0402c0c1d20b46030040c0c42c02e20502c1a044103501590012001c513a9042c012015491340e44000420941c0c0540104444004107480004000c0c2d008024400031801703140d041202180c0d588044902982d6a080944440a00c0d07105503e030f040000c00144510b9038001089801580b0640c0709040841d10b452040e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 264903201 1250 264901951 264901961
    0x40e060702010b0108100b07031b140c030111041e15020c0108010b0a0503060d060b03150f2206020918040f02040e06070e090402040e0303010308070b0903090f09070207090f0b0102010b04 82
    0x115000441000061288000e000c0c000c00e462352180c10041d29040c0588100d14840c811070b58107445085041c1270421842000307104101880904030000c006d4088900740b481c4241c0a60701404200100200040c1100c1000344900f2028082c00c0c0c2003d90000350000000390307285845024a400030f22204000240d0008030b40a440700d040c91622410704540d00c1c0c000380550404120010f84040d902c941402c1a0f036103081c8800f1043d040d9000c1e070242e951810040344d421405024040340c040c41c04214480d0b5001c001c20310301070071071039000001507511aa10320000d92816249035400300c03a8600201400704119110300c0703102c1c00310300c00d40e0180003414034001510f0311440101c070603c0100f0103101c45040c0724902121010380c0144024800904489089039080c690341090b04202e0302148005014810700030050403c0d6804007204009503c1c21002c040840c003013040c880d04140c0038051020104003c10b00034001840941aa22010040122010340d0b00c005024410300150255103802001c0c0e04030306040c099 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 264904451 1250 264903201 264903211
    0x10090606031505131d0c0108160206060d06061d04031808031e0706060e06032e0507030f0f020406030c05040302090606131e170c030601030b0a0605040e060702010b0108 74
    0x14a0611034946014001d0904410900441c1d5517582d400c0103026482000d12007000d018407034000d001001e403900001d0701162002e00717a80c0c01404203007001c1c181d855000615990103602540c11346901900c0717140140c06400c040c3c00030008041c00e58241c2250441d002040c6104a00036641c44c0d41c401b00e61141c041852440b8007542280350030401c010403008102801e550242ca1850902c20300d82503040c0c503803c007125a50340240744080e1007442404401c0c03604001c4559256846081c003107400c0f2511900320740c0482500c1948100c10344600c00550ba0740d00030b030701c2815401d024a00c14800503015000e1a0300a5015014a030003091070300c41915901403248007610242d99015240c0c05190301d50204010310f0760014080c4044042011034040350042040c102c4a43c0b01c070005140554442c01c0c03e00c0a402806c00c00501342641e40b02d009402c400d90b030001441c5045981120101f003c41e22011082c00140c50503403c05604142441c00b03425104000203801032161086500030021100040c004442803070090ba0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 264905701 1250 264904451 264904481
    0xb01081e07110708010603060606090e070c0314070204150e0c0a0206040f061b05130b070b0a0c230712030e120901051b01021c2708121009060603 64
    0x1401040c0a01d05400c0a04802d404403001943d440c0459401d6072110381080314041d844090812a4a4114039094098410304a00e01040e290050008154241042c0080c0410541c8600c4480f0040b24230200c6410603006442400114007422002000c80c169100e6800e21404030000a280b0300b81c29801d6034a584119400b6103c25215500e48498405c610001a20740c0380c0d582c121313940c545580c0602c0c2d4101c5160768884a44440612581c26000a12a071020704464410005807001640b1080c01030346c0300350000000900c07072400c1034041700c96041100030781032640c41c582c1148480c400c0c03040c060554a881490b1002c0c40340315484044040d10568042041241d01501041c1050039050004e01001001071405a05000e0014604c3d000403070950f003015002d035030000ba85a40d512034043d200c0c0800c0d44070141403080d4004840c0e82520004005141c070b440b200c0096585080000d000116000e000300840100c0e2107003031100d001c0007484124810050f04928203100001c016000e4080d016070311840340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 264906951 1250 264905701 264905761
    0xc030a030806060d05240a0b07060213050307061107090b0303040303051b0601030c0e1308090402071e060509070f03021012150603050702070608010e01060e0114030a0b0108 76
    0x1a400381e901a1024200541c0300800b80960381e0480c40390311605205038003904203420107040510a403904c141e43c1100c940d0052000e10b40500050100d0000c403682c0c3c9074070450041c2c0e2800b0b03066070805040a65044141e02d40070b0b0500019040383d1082042c04240c003603a06035014950390f10140e60403038085d4001541c2540040c00f04001190142016000700d580360b010400c201c0c5901c0c04802d0a01109800132545085161401d005800070004000c5e8819000c0060b42c00070002500c031040680506009548125000607500040100d1440074130605a042c0c401c801400415141060181c102200d440605116056001800c17281540340001200c1c0c0107845111f41586800084030394001e90503400c0039490311184102c2d4184108100b1070000c09143d41e0000c0c0c1030604000003401c1c924240c4c0018100962200107019a01c060240c4604482c4181000d48150221200585490007501c11440c51540b0204c00c0000320406d80e048484041c009903140c401c1c80e5540b06000c1d402000c00440c8016490f111 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 264908201 1250 264906951 264906953
    0x10f1e15050d03180e070504060f18050f0103090606030b06040b03150f1003150507030c0302070201090504050a33090c02150603030d111201060507030c080901211d0c030a 75
    0x280303400311096003c41c0c045150080c0c0f1001340d0b02500809846c050006403000504101d80d070f50200391007010240310314101c1090b0f820704009118564030b500866120f180ca619a41045a0280c0c0c84521074582c48034041c0516543d80c2403d02c0505002c440c064041c03414070b0001c040d64540401e90740c400e9801e00c01c00d5080c0c1e491b01c2d9440c0d03400340780081032001d0b21000140040041750307164841e415100c4c01140042001e10f410a0000e0555601e840a0700c240741c014002e0b080180c3e0829000410340308196000582c9548803d400400b81400514484140014854441d00c401904050f041030215603d0004541961040c010045840c284041001a040500c1303060442545140940e08890014202c9043c40c01700f101310f00855014000840c18108001001c42120001c48145801001c050400d24101480d42d00d000e001c1541c4ca0710014402880080c0d25001e81e80100320220003034160000030031100303198050407001010641c2e498241e01490b184003d81c5500c0002c1c1c140d4501c02c0c003034054007403800c41f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 264909451 1250 264908201 264908207
    0x9064902030d1b0605040501020a09050301060f050114130b0403030806031b100c02100507060515091902070f0305090102010506150406210c0305220302030417010f1e15050d03 77
    0xb8140c04080400003081a0f400410658010140103500901c001a503400b0b6109010b0182982ca5101074000d074100281083f06d410078040e0f070011242c081c24026048070000e555240c86110b024100490740d03079502c401003a44241034000d0016030313210f51180650341c0c60b6101095582e0b8102a841c44158480d403003000c0c03403401c00480c0c40b4000001414412122001d9600094030080e56455010010b4404a2041c050040f01d020300341d00300e41210744e00f2400d60070701d90206103044001041501010043c5003403079040d5401d58111224982c00003010341055000b8030b8010a40c0c0c1c02526030314019820013002c160700340303004200b039004102c81c6a001d928181c0b42035400d44140c0f400d8942000c65220300c5170729401a045070f0050520b0303c0303c607503000034282c0380202c24450b005140a1002c440c80e500c00ea500c40000303400104507800d80b00b50100400441016254a138058030716444211402818001d88140440005070078100b0482a0001405040c184400d4020f10070058070a10340d100001a01100102c3c2c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 264910701 1250 264909451 264909467
    0x9191e14040e030c011d0c0402160b061c060504060e1605100903080f0c0105090d0203160f021f0807020318040b01170421110a0209064902030d 63
    0x2045060343c4c100a4030241031401c68045954507138190745070309502c07195204e09000006008104484c11402d0030200381c1c5140100701030400082c11000007101050003a5184141c490075010740d040340501e41440391503c0009000c0c00c0c0c130111344450611240030591100841e000240c0c40c0752080c21007509180804000744000360354000c81c240f1040d00c0010010038100801400d0901c940c40180da9140301c804001d42c02c4900080034001982c11810b1310454141c0d01200310b0f45200e0040c110b10341c0800301c0b414001d41c0004a410000e5000d02c407103c1c00c40c2890210740c4168202d0707200d0340355080c00d0750340d8140c280c1e280d00c43c0d103549119220519603400560300d81540329050345441031400c1058138182e440301c004424800d4600307070784d407151000c800101c20000c982c3e1042503a4842c07038104a880349010401d50f5950480100a200b50541c0d00022000e8403500c0c171b03194907800d5500800b100c9801c50302100f4001d00303c004114401c09800140340c0d5101c0c101c4480e03082015400b40051000310b400b1074084071f41c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 264911951 1250 264910701 264910721
    0x91501031d1204050a0b040605030c0c01060b1809010e01062a14100507050f0403020904030e060415110607080c030703020f0403080409150308180609191e1404 70
    0x48a80c165400300300300c0c10048000008801d82c142682d89042038108003c140303041c0c1c0b140200180802041c01401c5c0c0c0007042e25005030703030510314527241c4070901103483c090081a00003d00c80030f00401c00c0386210500b04c0000d54241c03015540207642c0e91301c132030405003000800d000d40408103007201000c12411200c00440e440609540e909580807840c540c0d210140d00e90040e5441042d50f01c6940f0800c01c01c40d051040710b8000b002070411614204003400c02102e1400f0314800070744941d81110026003458060418186548001080107545686819142140c4080005518001880c0f40120141064009582d030f0145049495241c4181d4490ba1851802d0340001d01e807008041e000c1c80ac0c10a1030610300060406140329022590301c40e0700b040b0341ca00403074900342501c11150490007410400710b1050310440d038052440400002c59498401c1c0450258443c072103030f05030002881d1280d601044141d00c103200075582007050300281001c0b0b0489032416031806014500c44002c00c11100d070102d14090307014545035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 264913201 1250 264911951 264911981
    0xc0f0804331101060e04080c160f03031110060b04080712110d080d02040905012c070e0f03061005030105090a1101050d1d010c030e0307030806040b04020c0f010c08010509150103 78
    0xc80c3e112170b900800b800065600315580030021420700030000d014001501c84903210724041012618180c070404000d021032101405010b510449082080c50074000181a440100d17005e2250559541c115481640144100a070f14003802c0408180c030f031a0520a19001504084071125184500c0c0400c064400100030407200030f07500304040d00c1c0d8203000e1b002410050ac8904d80001d501c0d8504040e17200c8452451428000c1000c400c0040c0c412848120390f11074009406240101d0010010008a070002514600c9594148034040c1044900800410001c0998005a0080c0301c66150300e1070301d503500c1444000003450003000135081902c0b540700d48041e0080740d00d001e0020900d214a07000c10101030716201d40c0d00e101651504e2055040c66094041c403824828203030700031840c0074003e8900821482001e00032070300c10780d221811442141d545405a40e03d4180400039600f1130740624411500030600070000801080c0304400000355403415556807480707000c004c6030000100c40400011801400c4c002c82080070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 264914451 1250 264913201 264913211
    0x150901050421031706010203180402090a0803190e1c062c0609060c0d1a03030a020d090503010b090109020c0a0c0f0302030106080f0705100c0f0804331101 68
    0x1440100c42e4001200c80503244044490b80450400400c040c9003105210840078555050042c266070010481d00b1500d4040c0e00202c2d041c4c90100010040c0c824111a691310080c00640425600c50110043c0014441c044114010f40c8210300c055950141100c100d60f400241515560100d000f0145002c054603c204c000283c85500504c1105404907070003ea42c1c040d0440424074925800304000d15500a524603004109078602100002424424401040280f60b15814035001401e03000031101461603005003034035225102c3d03007002556140480118400100000e0b0009801d05040c400c001d0b21030009801040c85a00303180462020750702c000c20260052050078900804a90346600210250401c51064032100b03145004150a42c0e545070002c003d01d4000c40060442c4100010f8440308407030003a610135808020704102034030280e50003080540308440c20340802c0208488440184241e0b05040324154400d140181e5203820031441e0f51454030070b42c1c0081c042c00b42407400350035030107580303154000007140c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 264915701 1250 264914451 264914459
    0x5090105031914010e0f0c04051c0b010815070507050c0402031302030a0b01090c0302090a06080601020a08040605070c0b0c060a05180708060405011d2a0d0f020109080c1509010504 79
    0xc215421150400f2800300c0070401840020036442c0404d400a04045107515a8205001e452241d0b10a078411940b052000300948000504510700042c40381e5084525107c1d2503a40b50741c04d0b0f4440903040d4441003d1003a880015803250f010320705441e416900200240300550340300701444025400a00300d002015185100a0010f0f5010440c66100c507100d90619419135140c50b0507042a07803554130710401414014000490952645204181100e8140c0307403007010741e02e40900507400c00c01c0890026110040014011030702c2c41e04803004203880ca01c42c1031514606076807584440c02c0740c0a02e01081030380340c0010010441412041d04001d4000316002c00c00c5107a201d507000c030103150420aa210314801d4001c0406c01041c03203003c0c41030143d04080e2800c45038580454003107450710b50001941403508101480386480d05030401510800c0c4011020300010700310000c41c200b0f031303450720004103040780062980c000105c1c0241c1c002c43c11107040780c000b0300109192400001055901d81014100034104141804005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 264916951 1250 264915701 264915751
    0x509060c1006090f0603170306012f060c03011d060103180f0b0109060b1903060f06020609060c0a020706050c03190801080f030702010c0212150a0f1505010509010503 73
    0x807031034048001000481518080c0e4a005842041c112102100d2510f9010008540108401c451008140720410703620760310301c0010703a1005649019051038950118640c505500406600c002c810003ca00b1521f59507981c810b4070700c0500c405d000b0b60441010718048800021198280c05410801c1418007061451841906466046007284240c402c0c0b20243c000c0024080c09040309409401d0421050101e40c0c10706000c2407044c0704019000a90740301c0c0e81411440e86101e0b9008034040d10350a09080607403903484000942e20401a68442054028070300421140c5c2407010860780c1100e0b07150058040d072840c4c541c040d03030b0301d07000007507045040d02080004240c50200c03010070304580074458440e1104c550400c1e5107103103040090003507442154030400200005d81e0304070308500e5000358100c7e040f14103000402000c0c0d041985050701e890445030000b062100b120582d410541c414001d041041120b10f901c080d944450340b90a214090104c1c600300458040e5512590081d030b4468201c103c03c8680c41c60b013010321 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 264918201 1250 264916951 264916963
    0x90305061e010b04050f0d06020904060306140702060f070f03060e010f032303070204050c0c12180d1a041703010311040e031201090c030b0d05060a0b120a030509060c 73
    0xa10300c0311464003407240c12046029500c82c050110b1201c0e850a040c00c041c0410140d40c440d40c800d51056042c6c80303c190130440142c04640c080c14014100380704041d940c1c50f007200644044004044001c21001c0050354844c40055094880c1c1e41c0c0350900403240c0c98808040e940c0090700541c15040644503040402c0e4481e401c82902d008145043d0420780452031401e2101d000c1188011500000407075410405d00c0d0540002940c01954040703030005005d4603591b085825a110700a0140500d00030600e50041c00e8180d030700544155031204821003010801101080340b401202e2200070540b40c800307075462301c0b10701008221640c040d102d41280031340e9821014404c802900241c0c021036124219102848482c20a1301810420071001c01c000c500f08940d1740c202c558000414052014480e0743c40304650581807090300040c03030040c4082c040000084060a203582c9a40049803011161800c1c0024454281005142003c4000f0481d000c0c04080515640072030f1564040012158030400034055100302c4003041c010303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 264919451 1250 264918201 264918211
    0x12020f03090a030809150105040b0d060e1506030114040f1407030f0c0b1c0e07410d080a18060c0606080609030919090e0609191109040309030506 64
    0x74100b070721003490002c28201000341050202c4d00000160940c110514071600e05443c001c40e00404c140303052001096007242c0320800038000504050798034881040210740a59007225058148002d0340d40c08003030609941c3d108030b0081c201c0009400080100c0c0180e98048036080c82030400e02030108a90805c10315002c62500240d82c40c030070b203e510404025031010400b0080016440e26803e0902400382141d0b50090380d03080c2061903482c0c0012602e00f035001d00c0b418006e03005447c420040880e030520001e440905241c101d8025487c500c0a088013107014080241e4011001494801c030b0585550b17410880d41c104004a101340b00c5070710340c0c42d4500007030416860054211651001d0004075070342048025030b18164090042500b10105000c0035400100484401d120142c0d035040b40c0101c0d00d0100e090000b8641d0005402d945010300d030303001d02440845c92501a035518002c44600b280d04050207194130510718002006462249a548640d040030190380c4c3c0e02ca0b000b070904c0440c40d580e03622900e04000040314 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 264920701 1250 264919451 264919453
    0x30d0b0d21030e010903081501020f010203010b040f090b0a18110703120c08010f0603020f16030207060216061e020a1205130b120c1308010f02031501030510050112020f0309 76
    0x76485409503151140303600322603082009110307080303064801800c0d090001e013500a5018410a0117070407079000300042c103058080e50b00219178969550600c03e20f07d400502441d4040c0314100000606c12146000e00c10442d14001c02500100745000214060045030343c545010b42a1503007000660034000c1e0f4083c101040c001e4171a600302c4064031009a00300d4002d003465005000707410b00148000e030301410655066445d5800e0060381c5010b060740d4000c1d01d0054051681840f11080c40003001c1684c08111202100d0f855000c07100c80302a040550030006486002d51800a1914035001040840c0110301d609004101c1c019503960520701c1d00c41d41450a0b0441e2107a000c25030000d041c101441c20304c0800401003201003902414010505512218a0006454900300314408101440380384002c8002400415500008001441d44c440000000c0d400031102041ea891010308001c400f54002c0c0180b5124540300d41c1b911840a0600005480c0c05640d82c3d5198822682440103c1c040b100b888000c50080e20340300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 264921951 1250 264920701 264920753
    0x130e0601120c24030b240c01020c0703050a050d09120224031f0801060e060d051203010602010507030605010503041109040303060b0f070c060c0c030f050c10031b020708030d0b0d 78
    0x250040c0986080b0b40c2c811b40140c2030f102160791011008803018035510100b00e5096038900846200c039003e40180e840c04640c5008501001081040010319040034501c603400341d900b403148030601694604891703c04c1403101841e014500e0b00518107074045481036000a40171a0808040b120030700e0381c9800c200d41e0050032800c0d066180004000c0000c681c03004111060007400442d0411405d40181080900440e00410042e94400d04024041c049030162400c494034071500e0350ba54040c005c3c045e10040c1c5110000c24901341d004503643d4406c00490344a590080034078601441c560b410721900703060090060b410556a6400800c00380c155000501c0f9000c0e900365265126034090924003102d1240c1da210700107205600030301e07000148903040454212034012400c815160001d0038914207184507001220344c0b04d00d000a10224094043d889000300c1c08421509810a9101a00590b51b0321003a0091000c227900920200c3e0f5034100a80218642d14000340044080120584d50302c09400100300840c19101c08032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 264923201 1250 264921951 264922019
    0xc0902091318060b0a030602120f0a110a21022b0b0108041506081f0b0f0901090b011e03060501080f060603070f0c0209010311130e0601120c 62
    0x54000d41429280041d001c10400c050002c0d40e901010b5544001046940c9490310b101607540c071440000011074101d0819541c4403200320b16603040e12002c030741c103821025240022501040c224800c01c03040c030360380c05040f51a184540c00180e0b00390071030000c20702c44042d43c0c4500c0d2420003468009403a0301c0050160b08106000c2c00c07044641000c020381d403940300c1d0900d480c40b0006145c1c0e00000b0145c219030050514030310794200c01e111a000d415a500982c0d02c601c034104c10288940c18661108038103000d411010411945410100686030750500c400701c7c0e0000c44400188050191680000039000c41410b0103401c40010407014105454428808400b01c0d41e201c2d410401543c0298105505c00d40e844910381492178204000750f260f0101400c041c2c00c00a00510180340340d40924582103d40c2c0d0004c1c003005c4e00b50787d645850100300b2a601c41c0c980c060320b13281c0700d40070490381e07075000d07001c1c600a103c0060192a070030181c444021140004068038903408526001803c045952800004200700c900c860221581c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 264924451 1250 264923201 264923209
    0xb040911030c0a0e010c08030106090e0609041a091f0e0105090703200f0405040506011401020309030a02040c02121c06050a050d02220c0801080c03070812090604030c090209 76
    0x10200501a02a810400c10904031042e800320380038003201c0e0a0103000d8203407480040742c0142c0062002858071030000004100e50f5001911042280c004801042c895035550090143c0c0c00300c1540c0c02070a440c074074102c3d0092147c00220076940300c0d60b0241181e902c80284c2514071340e2001d84254000415a40d40c1c0c0d88030102c4001c0c010194840701c4240200800340c0385643c4c071020020881c01c05d062281200858250a54500030707503805180c0c2c028070a004c0c80c00d03c0d041c4680c44030000e110b2103c40c41080280303101154004000c0e00d003502030003006406006416000d11000c2c2024100543c11805460004402c540f40c48002e40380350f4142c0d6056442400541e46140c0c02c40e840b58211510610112070100a00e13a10380030b80350b0145a050f00d0502c480c0c2c0488000031070310709400f00d2000388507080600386581158002c0c039060484030b082048800014238401411f881c0c14131402105c82580011055030050900c11002302f65030340d40648190316084c0d681c0c60b00d80c10780880b81c0150f0300c07141c0c0000b6000d81d10300e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 264925701 1250 264924451 264924461
    0x501150306050402090f060102061306060b07051b0102121b1203070504060306060c170a02010b030f150f04260c010c030c0206251b0b04030201020405090f0405030703050903160b0409 80
    0x34070742940f51024181f0381e001035620240109030103900c5619441c00d10410030b031071300420020034500036042d44610181c43c1c21500d50b441100140c2c021241c03400403c0d00b0f58030014058000d9030b05540960720b00004c07001c4150b9080a90620141c00380704006c08400c1c00007045000390301c20400b50703648503200d60401100070251615684030408200e034031009440495803030310340d0010000040901541c2d401c8061403d078050680c0101e10703a85402000c1123581107180c00329503a14420044c0c81d4002c3c41c0c3c1d07188007400314040010355000e00003950404012340c010888503c0e04846000c0c010156050460401c015803d445402e84c40f034000076225041c69078643d804004041e0071900c6413081c8200060615280e00910401d03001c00001c01c4005495506024503034801c0c8089180c01c14007102c03091034582000385c00303580700b48145402140b56100040a1541c1c0150b02c82c021030340070002c2c6181600548007212180c02c1500c8040d854001c0300c0414100103507520600c40280540109191914039020341075080364 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 264926951 1250 264925701 264925711
    0x50f030406031b210c020f07260601030f02040b031203040f150c02100b010c0804090501260a020105070303060801090c05040b180606030a060815060a0b0a0e0d050115030605040209 79
    0x1000131242d40c4030502c0503000000c15082d94070000d00c6046060040346018843c3c004440c140c0200c0c880030507420081d0150307200e0042040ca42800a8084130105607481c8030900c000340900c40707040300034001071905030041c10084900404070355042035038000492081c0c0c8296800c44654200504410812400d102d140428140382c0c2c004011880b40014041d456507520600281029a940004512a805003070a05600fa80100e143c540b40c64482079100b008103400e0007581000820308603c0039000269200c2d2000f1a15110040d108200040d4010b5a590304023041c102c0c18036898400206d80c2d14003d225902c1c1d81c5010741c0461640310720f00014001140c5405641030f0143c224001510781e580728800c045500070009032081070762a80c801c3d0740b030030082c2011f8000c1002030080c00b4a00c000e0404003c059409040112005c944255030f13410440c4080c1304039035201c1d0104000391043e0740140340540140d0b00700c030300400003c04c002284d0380501c444084160011504c1654072420721055080c5032203003e0b882 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 264928057 1106 264926951 264926957
    0x2010e0109031d03240601091203020109060c0810030b040609060c0903110105070c09090501061e03110a050f1e03011e05100e070507050f030406031b 66
    0x1080c010f4090044159985480f2031501c1d010501034010501c0300512031224207102c0d038601c0c003464014800c60600001101c0024101079880c440340030144643c2c00021071807101d1030010201d032440308885040042e58800c2044400e208586c07401074030f030042c428001740c1e600c500d40880600760900380100304038200101d0019554009560b102620b1040d141030320340c44810401118140078020000d000c0c03002c114010403401015901180b009401600003095044c0c0f0303459110003400c907170170410b111401c0003281041445001c41d440f202c60350702100c8006459207020700103142605a002454450210003140e100c1480a003480c0e5140100017500a114100600e00c8043d0241c0365642c105500c1c80c00c00e00002c1c61020031220074401d0311f1402052502d6612a050f04444541010908585034481c402800d00d8424003040508000c2005a50105808030900c00f080c06c0c205035003200c0014 = true := by decide +kernel

theorem cover : BRFrame.Cov 264748201 264928057 := by
  have h0 := BRFrame.cov_init 264748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 264748201 ≤ n) (h2 : n < 264928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
