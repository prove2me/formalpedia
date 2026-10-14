-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2317
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:20:43.726927+00:00
-- url     : https://prove2.me/submissions/84e81708-b9d3-4430-aa64-aeca4a5fcd41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 416546762 ≤ n < 416726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 416548012 1250 416546762 416546771
    0x60903030c0e010905040b0d0c2301140406051c050f0103120333030b0108070906090203091b12010204180b0d0302060f070318030f020c090c04120c030611030901 71
    0xa81d203200d80100d04590300140d40f880b620501e81400c10026150b1620895401a280b0a407680050304804205006000300340682200484504000303c00d0303042c16074043d0500225070baa00216240304422102510b480e81001501c030828022101c902200488520f6400391401c8207000021000d040f013a412a48525803c00d00c0900054040b0140c900007081c04451546410410050480031f080568807001030342d600f000d4469807502d403204400c0e0b0030b0b030208000343c00070700082c00204158001e84000d41015a4254030b10704140c400613548001d41c9104030904100201c80c04540d0b42e0702c100d00740741442054000c2d912140ca03030001b13204000b000079140c1038031860601000b001d800c000c1d1303402450a4164016011a030349061501c406440d005041004259940b0102d00d4201c1d07540940409550280d1b540ca400f03404c1100b4082d2801c140350f10703042e10840410f0100010703241d4030b100300d50540301c804a40922403d0350340303400e240396406600010306103810040822440d007414030245128100c0b4200070300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 416549262 1250 416548012 416548031
    0x1b0403050109170c0c090a0207051c0210090c0902030a06080d05090405090f0607081509010e0a2a14070611030906131a070e0d0506160518010c02060d020706090303 72
    0x205540b144501401e0180c200070361710321042c9011181c131a0b1250b031000c0c025160028558417181064812785032090044544030310b01a61a0b81044958241a4189010400440c0d6600c40f88000c050a12a0150700c50300040029465042a04130f0030042c041c1404568030b150301c030b06002e04544c011815070341c000ca1400c80041c1201c140083d104840081c100054141903c2d4171500b140c10610003040c850308114107030f600440a84610b04802d009251400d140c0407a401c040001c5802d035400305c0341d15204606489140c0841400070300360f00305c0d015402d0800280d06180640c0d6585913010790000644410303e00280d50801484800c003c0d84140503c80540b04559901030440c481c0400992000e06071015484102515206060702141c00611a04003040030107d104001030a43c000303000304507001d4110714140015410201301c2442503001e01d08203035040c5444510400c1400a54485a60400401800d81070540d00d940d0200c894400007603005642d10300e1039080c10f00280c100724a007200000d29041c0c580 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 416550512 1250 416549262 416549303
    0x60206010821090126010303120f0207020f09070207030c0b09010e0d0803070c11121f060501080604090305041809030e09270309030a0f02030c060c060a051b0403050109 74
    0x1d028840700d1480c81410640e100004481c0c0034107002c441c81c1424460602080c8811742100e0841c000c611a81d91107034851308003080d0070155000140d0540c819801400040c1c010b95982e500a840c1c4201131352030601c9903840b036504071301d0048517600c0500130720550000800c20b02c0c0c0c8080240780d801800e88450101c51841d030140449191020707000380c6940f0061020841b142d21a4071707040411805400049082c3c0c004d00c00042000c1a40f40c001c0c003060748450800c540d05009000e0401000070400c40c100240e61822001a120035001031600c0e106983d550702c0c04003014026402d0b5000761403401d480c4c203e120b00c0b150a042c020300701e98005601091102811001a19091a0b900d21400084500840040d00001e102e09503078007440242000f804240104109524200080320805000c0c81c8050400100b500500d03003840b10070308020b4040c1008100307552003110300003080746d0404000100040c0300c1e51940e030302c1070003402c8035a034520030507200003000414440150009116140500305400d10b42c074080c0d416 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 416551762 1250 416550512 416550553
    0x150e01051b07141005040905090c060a0c0204110a0f0813050105090607080f060a030f14010f02120609010e0c0c0c0d06050708070903050d05070f060509010c090b07050a060b06090a0602060108 84
    0x8241c00a05e082109104804040d00580d4001540d101212690881c2c03800144494206604000001d004a04c2003010b5103824052059170301c0702d0421951800403508001001c02c11074428000c1401082000314014610b41e60105400e036400000820080c1085400c054a078601507641000045250300441c0202d06850300f49409000000c0c1050180c5d0301d1550b0b0400b105070541400e480d950a500350000c0621000e000e0185d289141110069448143d60b41084c40d40d500500700d58021501c48006000c84404c2c9044650055100242252110360503040d032440c00c0943d610303081e00010001e00003000c024554019134011015600c8004850340d820314100e03035042c81440050020342c09841103040d8103000b44010102e80d03020301e21084084250340c43d0002504d9003640c00600c60303075440080c1c3c0e07050396101881a025180c200a12898841030341c503981c0e955100c0d07030005040740c0d0382d644202210703030b40e42c0d011100040006080082d00303d40d54000651541c1c0f003441058010300a4803640202c1c00d500c3d050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 416553012 1250 416551762 416551789
    0x161a0405011b020102040f140621090708011a0609060d0614040501230907090f030c0806010618091a0d0302010c0e06040b040e0c040816090c09150e01051b0714 70
    0x4041f0a00e840d80c41c0540084091180e50040403c0103c0100c0d40758103818845000c0070350b9a114280d0401095051414035651700041d0399914000141d05650620b1940f050100c1e42203071055280d403030103400108607106802c1084601c91408100044000d081b41d840d2401c00d03011282001242c0c0d03106002812030900806140c80300034000e0a00f121890020b40d00381d0001000e02e815030001d6110410901110080d802c151132910180313008100002d0104042d501500c858502841d50301c01003010035060240034010032158070707100c015000b41c804080c0c400d504511402440440081484d0a001c0c0c020405540640000341e4811514070b1542000c0b0100c3e0100c94803001c45901d810300d03280c640340403007034003800a08085408000c002a8140d00f00080ca41010800d500c08030064900300d0542d00b1039000c80042828441c9070a0704000321354100e8504100c1c201d89042070001804010012200c920404d80c07001100d41050241402e8820009074120035505100400341d5054412410840b81045121 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 416554262 1250 416553012 416553029
    0x1208030402040c11070b03010f0807050319050c04051504150b1c0b09010f0608060904030f1d040216050c03060f13030e182a161a0405011b02010204 65
    0x820010b0400d82d0225104070458a8540346840915500390300305285a40f00444207200880140311114420841c28000d109510003081100e1078a004aa11003070b80262200300740e001c035244a428440f0a01c01c0c0482003000800803c03541c80d290321695a080c00c40301d0058041d40c0ba058008a04c9884501050706654040a903181006140208c412495a040e40d0714a4402e446509030000c40c0c507030030002c5d406042245003030800b060801c680107104090080ca00e0307104403084070078080032070f4010f800d100c00036400e4605504007000e420a60300318559680604e07500304e840004d5803000d081050f20543d801034414402d4600c10310b013402c01c1544c0c660060ba020f1089581580c04070310303401992008009424840c0c20407901107664080000c040c0c026010240c554944460108502040d03410364150101000400302014404c549540c1c06440c01080260800c0c0e0509002c0c1c070051211400c101443c040b8120152041d07803405142c91800ba00d00c0d0414240c456540070140408540180261f038140da9015 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 416555512 1250 416554262 416554267
    0xb0405070219020303070f1a090c060405121c0302041a0414060901020a0605040b040c0e07120203070c021e0f0d050c151204111002160b07031103030108010b0a1208 72
    0x3202c0c031046050144100301ea0610040051a000461504041c0c490768020449000d9a81c030030744080030642001800c2c20a1354020301204411603030303410140d50a4503016079800003903060480b5480e00d0200d41144550045007151040284103500d40c00400030380e1101e07100710712420b0100b0144840c0740a980145c04a0719016038241240381091005040740240510440d403180c085900c030720b01194410740c0d0a03604013002004120a0107a10380c004001042e1024040103580f0300200300500c00400c0d010442400d64001000c54491845030444514160300101541c0001e00f140d11950800040b029032180034440c0b0001249251411000241c3d1058010001c0c01903002040108042e02034035140e4a500e06400340107484a000c40c0540a5115074400d40306122214161810481c02400134202c40c0219840401c0c55500300509901c45000c0320b01002c803290b202d00d820b03e819a81410360f0901d000440c40040000074540c98150461009000f00b40e0745207065a45400c40700401c0340c11504050300c200d504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 416556762 1250 416555512 416555533
    0x908241305160828120302090d03090302092d27100c020604020a1701140f04150b06040512070801020a021c02160b0702040b030304090603031404060f050703110d0f030b04050702 78
    0x4801d5034030300b0011980f900516107054400090302718600441d040d00012001d107014411030401d220744981080004c903406c1445100481107490040030a48a4982d0070054808900c0800300d0f001c2001590400c283c0303c80300310040b080c883d940c8505050600040f0ba0405100030741c0140041459805283c000d03185240c820b0a001070954200c100a40c0f0103071646da6050749c000024082c4404038001c01146c1800d818a04150609260701441e020460301d04034a41040314134030340e650b18200c41c1112425100c54455242d95a0058103020682d80040640d5000140001c45254040381c0e0b42c9064070040542c2c0f0b9845e905503c00c81e552101c103907880341100c6000308103000c21203d0030040c1228602c001c001241542d00701c40841d04640150f841501e5650303c9290030300426802c04113510098280c0d11041e400d1903d407850081030b02d26a81c500109000001560030300b41403041c400030380842444011901a02c914001c001c151042080c054400a8501000d120852409014840c0294500e07401081c42c03080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 416558012 1250 416556762 416556773
    0xa240303050a1d100c150c080114060c0111040302010f0507150513061a010e1f03110f03160e04020307120e010204030507150908241305160828 63
    0x690450785000003104500340c40039603031080b0030310b50302c00322642d60294040d150b4503206c481d01203e0040c00c060a410322009000f41540070381d469044940c031443c0940040d03062004101d05210340c0b500c0002c079500f403091840c9085140c00051046134405c1c4d0300d04210b80381101f000c46060141c844020004000452091100f9005420064000a030204020303501a11135030380b1400c40d1114201e503603110101e541c00720010340e00800b0f4222440b006a610402941030f00c0310007118103110542d590103046d45c440c51810224690016503803460140301210f60390b1304259192541180102c20900006101c0003d80c8002d401c080c0242c0313019400e2038071103170703242c510048105003d0300341c5141c19030f01c9650921000000c01d008000040043c10035512030019662600c00060221446400001c1d05903c00034004d400f005801070a600c241041c400c142c0a02d446401510b112050740740006800d0f4410b050b842e4070b44582c840c03404800c6980704012514603480001c115134041c414103007032101380280038144001142c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 416559262 1250 416558012 416558027
    0x70b0429011d0402012006090d0201020403030c021c0b0c040312031127040f050906150901032d060b10020c010c0f021807020304030c0e010f120c0b030a240303050a 72
    0x340705052038540582c040c1c988006c80e5410308203140e03e42d4000801d20840400a00c801d8000c3d00d590310095207800d0030350f14042c000d0b03203040310028062101d40080e81c42146e00a00310001d200d40c000030716441030800c2500c002e00d80d00719000c25945130b0b5060030540e910318003074400d006810400540060412465004401e040036203081003500da00c00640755500180c4e01e62040b4221a10f4004d800039541c10181a441c6c6010720042c0300009480e825403500c1415078032407030100d044951241514540381ca40c814501c51500e00d03c400300104212102c040300400c0803c0d00020804981a00c820000001d0710000301ea440d60054002400708640e03481120114007407000e400c9280c0d0000d4606134114045031041811484210344010060b0404942881000322181040d001040382014805055041900e86140440240710f40b43c0c0c0361a002c441c05d010445422960401481c01c11032041d160b2401141c404040c0400c5a00c00242d000000d41480c030900d21603444100340c0f43c042c1d40b00d900f4070150140c20b0700c400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 416560512 1250 416559262 416559271
    0x8031216020109020907020304090617030f0c0a050a0c090c030b0913110d0b2502120304020d0506010906180203010807170f1603020103051e0402040b0402070b0429011d 74
    0x42d52641907203005601c840c5100760044402e41d00440d074542c548245041150419008030224280c200b403007c03d01031000042d10a00d03161090215070301c008607205070307140000b00340c0024507a0040084503418056a40990400c036408410244910701080360110100c42c0303070456113030384000d010300410104c2c10380d4070031120f10754461007136004030380384880005a680c10110401c581000824007007000d62440c84402c43c283c0d55121401003103c0280e10b4001e03407a50001840c800304141c001c00050250f541e400c403803c0340603400405482007540c5481140001d8407490007402084400411140100d1000d8800c0782d048910602c00350001905100d1030100451800e0300080d91440380307007599002c0d03000074444401602c81c0c04c142c0012551642c400034068401c010211b5040f13884882d802020ba0758801358595001da812200020745640010015000b401031840241100049000b08000c02c200c1c4800340c40716078162400d100202104003214003181c8000d002c1d00c415601f5503460f078440c03030040c01e0025400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 416561762 1250 416560512 416560517
    0x6050108040f060c0207030c0906060f0c05031204020d0602071b05010509030601120615060c061404020f090c041703030a0e06091f02120901150e010503120c03090a061808031216 78
    0xc0947c1c0345c98655107c03150380c02c041d900d40c1ea2810308102c0070b50001c2203546150101d04102c6403d0b00d0a49403e6201c1c02841c0070b902e40b156011000808542e01d20380225541c03507012408540f03452071414a401c001d26108860f661102c500ca01c0414998003500580d805070700000d0080001da030030904e10203444040d03204111912034561000440720700c0d071988081c0c06408240d5449101d0724007802c1c99400c0e60074080130360012480c04828880580c039280401001c145040d240300020341c80347c4162407020720030759020090f40c1100e101c244521203008001140120703540c80e024419000e00e10707000794685106031600426a80110645800225071039010340500e26461401403c0a122000c02894250102c811680b940d40d1445031030211404052035a0190000d402c0e000310660404010940c0c1d9030030746089070280c06010921011400c420012582c44040181002e070707115586590182c0b20b0318201d04c3e1010380794090703a80820300007000001e41e10b100c1b075050683d10b510345801e4492403801c08080545002c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 416563012 1250 416561762 416561773
    0x50f0705090d06200a0c0314090901170a1b060e031b010f12050705070209090f1f02090d0b0405070b0c03030403050a03021314030c0301060e061207030507031506050108040f060c02 79
    0x11380c581d03d4005003446582c6030b111050400740c20710b4010800a081d250025001d04148048010b039101c080340c45054031140d041d02a54100c66140041c503001d4038280060132079034103140304030030024883d1901c0704840158440d0100b8552241c101a1180048140da80402c050a950704101b98880c01004540d41e220f4208904941091122181a11011500760010a000007005411820900409a400340407400508118803d5009694441d462014142c034a000c0410300e071054214641e044401c07030240105400300604c02464844900c50044a003a42d65020b4060001407043d0310804880c0150f10a0018519640c0c1d1960240c4141c0c02c01e035604400c06509010304c01001040030049000b40000b01c0210741644002800c00d07203040c600981160103a41049401c000703507080205003d81040045421544449429024504d0501c059001501c0b900c00c8400c0042488501c0e11301c3c60200201ca882408100d46520054505640503100145400500c52510010421690110b400d9030000d10650306c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 416564262 1250 416563012 416563061
    0x120307021003151d01141c020f0112140717040f0b13080a030603060c030606171302030a03030504020306010e09030a030903030f02040f05090114150304050c13050f0705090d06 77
    0x80c0e10b181c4c01c180703541c004502400140811100300c2044c000c200c40444034401d081d121010460340c1000d43c5840240600f00402c4a2070250b0b01132450140341e000240010424000842c0b860050003000380c44074808144420016007000e0036400905100d66004030400354040ca00f5a80d41200f0036009200860a8a02c1230000f00000d41540003440041c5080e900403a4250460602c03e080325100301904092511340441084100d0f00024805a000c03880c0314205515030b2a1482c50400b6419007000a6140c09103204010400d50164455801280260100d4400d40e07200d011142a10b407090f06c451300107034010b12002c054a407181c0c014590344ea200c3c2c035010030040202081030061b6003064009000f02400356005101c1814001c2c0305600500701a03007243c0044056402060086d8010b40000c0c42242000000409200c0c0070003203110110000703861500d41d28200303981d10000b4181502d8804080d4040000304072141c0c403440070b031030701104014490344030760003036680e102c00408142c401d01401840407001c11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 416565512 1250 416564262 416564279
    0x2524090c03030c0b060901081b06070c0608071d0d1407031709011409060f0d020c2a0409031b170705030a140301060e100c02150912030702100315 64
    0x304001c40c440d4807454000c1080d4908140700c0800100440c3c014a001c1c001006440b00004001c44103041517070a0050030405200400e049100303424025258074070b04000051031a0740001502d1160840e55103008880c950341e0500e03401c40d0215514550f0220490000328003040441c41004c0d66054034404884007a6940d684086150403000045e414401d00411034032015604114007a105500e6050014070b0201d1540000e0010700841000d82680140880c040c20003030320b81d604503403c8000780d50489074985c138030004600120742c80b03914005070070480c0701c0b100003a8102402001c080c01c0d4140c60711003408424001c844602c80d40341c04107403200141d00800d040b0a02c401402444000e004002841d5103440c1100050710511055880c019200782c1040104280e80c1d10417500d101144085919400019501c3c0088501003035100e4040d50000300303c0742c07510b5007003030385401061100c0040d40e0380d907800c400006034251280504a8085c0d0030281141c104a01d661080d80b140306228040b0190405c07554071040030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 416566762 1250 416565512 416565533
    0x120f060b06091801140a030203070b1e0d0603030314070801060e150c0606010f090e010504020a092c0705040515030604090b040f05060c07020d140120252409 69
    0x100f150b08081c980140129011180c1c42c0070300035402e50b50299024556800300755180d51500c0780c5542c4170f41c08141490304001601d00980c01c065100000c0d41c903480d000310480020180c0b480210003080c80c14510741404410111494410340b81c545400c41030781c0c0780520565204501280c0701d039206100c1c0b00701d001498000b401a15854060780c00034151443d00b4400501561031400381c5178203008410104100309503443d03e800e07066032070549001d81c0f11980741400303440e07100154106444640c0c412043c00108412050703041700c00e50803101901c10781d441d50342054800d8402ca000e0660040315500303060344001000d2f8021900300700c1c0a400000c6e1603580c0e4858888007030b01a10200c0c0e090350303000035400504c4401c00038550000c0b40c803a01c0070b1401c2401c0d40001c4154906800c010f00c0c6400308101e129001c68294800c01f01391081d10f140340c0288030360030424502da501009051002403c0704008141c0c44c0d0503200c02c4900b584c0c1c4810b84c0c4000b0800030001050020001680024450321007400000142615a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 416568012 1250 416566762 416566789
    0x12c0111120f2205060a03090f0b011206060b0f0702270f04050105011410030509151006030e012c0c13060e1501020601090902010207080a0b010609120f060b0609 71
    0x1145512800f82400200f03024050b0104001290045407051040d903a0729801c0b02d160645600700042c0264807841c0800b0503071007110018221040b41d034000101d011400e424090014804c1008100042c0c032482002103078040c140924042d007905000c4071006081421003210306c4419a222254481100c0202032006070044400c40301000840080c0020000300b405490b01402001044081c039003c04000b0074030380011074005400301030700c84000c149141d505101c030014080c058900e98034246041c1d01865000035140c4580030010307241095a80c00c1440603c2a030b100010825003900c0a0060310008070f404807000c1050860318000c1d0780584550b6515070f00701c00c80d460700c0d2202c0442c0281c640903c0404100700140110701190590024103002c0c1c0e03000c20754a044d03910a10700014040380300d000407440c0800513000700d0998841c1c00740203401e00109070755180c102c8115664241c403a58607400b001028a940410042442c82041d04600c0013400301d03004403030203040191070541840303a04c80005040155407007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 416569262 1250 416568012 416568037
    0x180c06210c05040609270f0b030607180e0903040303051e030915010617060603190207050604060e3f070311100b0f090c0c07030b06012c011112 63
    0xc1c04000d05904250110000d120040c0c141ba1113204100d40d681504140781c2900141c20b42d6000001b281c11a140d100c1c0c0490b0401800300c5a01746030026014002c4c2c0d400c50a21154064940390018035050360360a0503101d078452402644c203051465070305032030715040365405846000e40c001000100615580141d44122469401400c200b04850943c0724140c106070014002c1080e0f81002c90301004c42503003410380101c002c0e0342d1301d03a43e41e645003180789881e88001c031180c1c40d42c1e00004409090190002d1010b0086010300d40410000690102080c0e490b0026501c4d42c0c0e05000b5904240d120b0503c030900c014000320f50560200d070303581c64880301c80b00c90780c0140011004034002844000d2480020001d041c05c80c441280704000841040f0000b900031861001030070300c62000b00000030203242c698806d80d1207a4402101700c031081500c0b4500030080349000ca49080c0002c0350b900181810f002c03166003c00a16840c1e011100e5440c0c440c1c0011150101a003182401510a40f00c0da111850401c13801091615020f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 416570512 1250 416569262 416569267
    0x3020c030a080d0632012c0307120b07081f0e150a0501120504060207061d060901050c0d0b0d0209090717010e0d0810031b09180c06210c05 61
    0x3002c03d10112080d94110003010080c0300513041d11a0108907841c000c00300141c40f66440315034103200490755140c84914122140c2c0c07150346903886500c804e04884202403000c40c296041e441e106c80c6900040da8202c18007828085503240491702e80790040d2070031030f04440c1a40d694448200207000f424032244c600d0340480761542d46e540c1003291300c080000750011070b04001c960300a0030502c0d281c0003d05143e168034114410b15540c030045001c1050710360442c1c55665101c50240000d4203280b0600e0032000d418941231003580240d4000038501e08040c410584503002d51702665062484c4409075400030080140d002c2d81060880720410096a14403000c01e101d140d615004104103400c0c1b24060b401000c0200c52590140e0400100b42043c1e0001303e49400605914500100c05503507840c01800c1d4442c8603130000d8100d20a06c140040f40050000100080c0c0304010014070010840c0c022581d220600f800c0f01502400b2103140900149201e00b40c01075510210f801c28446114440f8001421105088035a03001b05900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 416571762 1250 416570512 416570527
    0x3080a0b010206010e180c150712090f1802120c0a020d08011206110417010b010305010b120406051b04090603020906100906080403090b0a08180a030c080703020c030a08 74
    0x110300420040550a2024240652418844000ca0030340070303082e0720124440c0180c0a14421003000320818048009000040041d03a400024810303520040007600d0219501e41040c2c1140d020700700b001c0c1115038805090014078504121041ca103894001e0b1010380c140c0130888a0b0b182c0e0051944e036800340345c6103030305941d840800600284c900005410380c2000e2000130401040082020341c0200185130300080003142d24400d8552490503803081e90020506400e41d400b508032003480c154040d0700344020030788080040c1c1c0d0720341ca400759071b07402407038036036030165244400007000240a50400c3d500082001c0d09252003501c18541c0d44082d41254012101c0c00e65200c03802c03c250300d003c10005421440945528180e0030542d00001d1510a80380950014441160045020540b00d00300751402021003031856a01c44400c2c42c0f0040c55900180d4812420a200e80d224040141c00452440040342d819210b02e00105180c1c6e44915440d0482c060a5040d806541016a0240c800b400a42038940c40341c1901640c4050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 416573012 1250 416571762 416571781
    0xf0902060d050a0f060b0702130618020a020c01030b1011030409090b042306040f03090e070e030f0102181e120a05060705070218060a150c050712050c1e0d0308 70
    0x1030064441360040c10202d041101101910031200150f8041d91884100081404400090070190f0300c800380700d82e0901084041810142d02510000b0080d41c20780351400301c50b0004505490600c003805a0050038954459444c9001d0b1010400000b10001500d06240d5036610820885161794015a2031600c141d00b0071042065500d24507080001c0c0400b500c40d4251000086a5070b01001040100324030a0000a60185030050700402c0091022023949100c82c0b6103104024030f180d980403000d40c000e115031106129548810300071344007450101400c0c0341041c0c8a480400809002d2400007000c0c040a903115410b4649407031a003019402c01087c002c0024042d140b81861a107c80105140204078080c07060710700507620b1000c003001d15001c2c0a06185180c41d000e00203417100c0c155500141345100200504c20f1820707004010030b00321600500a64819035a60320350101051030740d21000301035130800d880e400a240340155603442110220000d1f000010120004241100c025240c01e40106a400c1d082014004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 416574262 1250 416573012 416573021
    0xd020c01090915030b191b020105060a15050a050c120909130f06020903010f0501260627031b0304090b040e42010e0906070906030f0902060d050a 64
    0x2c10070701008140403c03402403203a01d241d4040248071000c0f10740400c00d2182074000403548008001000c010500610000c03898009a612049000d54240030001d0020300c4e001043d031044031034103014500a02d45a0350115a2507220144001c2448014010204080010070181c0c5005641c02e280079600e008507000c0045c6034030001c00001a0405401001c0002a0f03520000441360394040405600c0300071020000c2c0c0940a4400b00b407042c0d9142800010301354040701148001c3e03951202d0b6071a28002c10001c02a00c1e10000c07994074a4900c400c2c180c0d20706040b95200c51001c0071641e003064900b45500d82c20201c1d100c850003140d401c05a0310101d400e2003d40e51900c180f60200c0c800721001c108040105274240d03229110b0110b10145600c00e21107420744c00183c00b03040d541c1c00307502c8440454401d030021055818100c0a004128074074800310300081400710001011070148820791a041042481c09208802800e0291010002181c0703130248040140c40343e9014044034502420b0224032407900004413000c48 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 416575512 1250 416574262 416574269
    0xa050a0e0a05031809070207090f0f1505100509010206060910081f060b040501021b060408190b06010c051c020a060e060402030114060f130608030c0f01060608071215080d020c0109 79
    0xaa2001741031115441e0001943c43c1203d1640b00042540b800d40c5504d68000d0015400000e922410a00c400b0303082c0e00c1280942c1c0035200c0840b100d40381c008144800b12154094044500e000d43d0000c0081521440e04d40388803944002103000c4a802c084e00c400146060040c2256010382d004001d0036840942803480c040e0102425440c0700303c9007440d20300f4000039030b9905510811140f138660807070100031985614044031302609017a4101d43c100c00d2000d6013241840300030301d000d032510a103183c00301e800e2307610504400e046540c1001c003c008880c094048082c20386040440e100a520036007000c40b001605c140a60004005800090704062174a40185401d584130000f000585482c1c1000704143d607500c460609145d5441950007031040c0c99060701000041c25a0f03000b0605500c008100500000000200301369600000c0000b488a0780c2c0d10340003502c03100420340d030031008201501406183d48038594032481e0751000e20108540d648e5641d0080604003000b08464a0041e0012051008103503009440f0074000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 416576762 1250 416575512 416575519
    0x1e06060c120c0118080f0c010902101206170a02011115040c18060303050d11040504020c280209040807021305010f080d110303060f0102150c18040b01080a050a0e0a050318 75
    0x4044c4681c0d56401920400070119600c4502013043c1c01c03009801d50090014981c0681a81c410500840c809418640f401014481c43e0f8100000441d50046c80e0b10030003480b0f0003013030003003071400308503801581c1c1c84014104481e280c0c405e64061888000100c0301c058021030080e2070300c0c02c8240c00d01c558a050744000140d0042144d00b031481c01c0000aa010302243c0e1809004100014488501e007085c0c00144038940c0041e500900200314555542e0010812210070040703200c0b0000c903040300144070700156412041c042c0d40a1a54400500400c071400000e2020920042000d01680400000d03207003150401e0f04040940700300b040042c001500e003044440d102c0d60309420040d44030140c1c010300d5541d03848000d0031391f030190b403540c14540c5007039008100f00c0c5a0500c8801e18000145020b01800c60305400c12409059500142603101069003040d100d002c80d01318060317440308a40d03038801001401501016165628196954528800c020414030100209610400c09141e8504415506640710700780303136007130a10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 416578012 1250 416576762 416576801
    0x2031905040f12020c0a0e07170a0b0306010510050307050901090320120118020f061e090102070b040e04060b0f030102070605040606080c01080403030c020c0d060c020f061e06060c120c01 82
    0x2a0b46e495141010031580c1480001c0c40ca40d1b149802100e018040e620840704900c01c02040c0078500c0c416401002251000340d049448607a84c03201080503020001c1448000f1403030030008520b41c02c1c803e05c01481032400c181401d12105a5a0b81c641400b40614104524007400c03503000220b1a14000105100d0300c200080240100d1000040840d2034040440001740700c1c0708915101c1220307441e10820703648130308544161031804680e5500c0000c800c0d402018454010f014036040816820200820340d8255024101c900e100380c1e0300d940c1c5a0000346143d1880507031100504582980c150707024001060314511586c804200ea00b40351030450280da003140c00c07000454201050100b1140d0b40403403900d41c07081d01881c1c0410000c3da0a40140d0621506414913034010381100e000009000c0c407900b081401141c0c41e400c984407404003050850300c0b04401c0d0b4142c80900090a5500a9104d4403000c50f508540d00400e0f0514000c10030090516000011174401850100440e4100744100284210350030795250021960303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 416579262 1250 416578012 416578033
    0xb0103060f05090a0e070f14061306030510030813030c050303031608040317010b070320030307030b04020c010c0c050607050a020c0d1a2815060302031905040f1202 72
    0x3510751090041501030807a800c0020032480803030f0011800740c200001075407102601c0f94801c004800b801d000b100d070b4a581d1040007103034a0900310222440c25030004500c0c18620306050084001c1c0002902c005020550200c0100c0891044001442d201d050440b030201001d15600e000c2da00803456900540c0b00c0c0c1c0040c0300b0003031240900e1134090450b00891420007559512403406551900000400504411280c00045412242c080041180ea800b80d1160005891818a05103050071140d8140c440c507003003031011442e03c07802900a945079450040002d41041c120041443c00c60310190070f50800152400b20410a0040a205c0e19402c445246060303480c090f41c0d084044d40d180000e001d0a0301562800000406002090031060b100e014203590280d41810f0240c40c0480c0640100c5003240c1c21400c0ca0f84061108400c2e00c1a41c8416003002480c3d108149056002e030f0081d000180f404244151040e0840c0102d482442000d1045224207841210041e1340e050804014002d43c42505c1550b21620401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 416580512 1250 416579262 416579279
    0x30e0f0d050306220504140109020d0213022106010f050705121b0a120f0c0b010909390608011d070210140a050c03070c112e030b010306 60
    0x1034003065800c0682c1d60392203240108102c64940c1c0820b03140a208500c01c070300f9200c00b0ba000319001d2800b40714100008040e442da250300709c40c0004002036118008183d00d01c01424031656200303a001940d10700508008042060580854041c10b0141040c4611f80c02c2182660304114485c9507441d10b894040e06018560350f540740d482e041d240402020340310208140f000c07000080000e030010410030341a07039070001c0d06182100c40490f001041402166540d0b0f41c500030076106550003104250401e40c0b8034203a910f400440c0004000564065803000c28107200c2002c0b20b018901c4051080400034014044810308103010900c4d4000f580010301002200401007014401d031161a0b10042581c0403060040e8847c50b03000c1c0c0c035118620542401041c100032003030003e0301c5450342ca00d1049501100c18846da640303480c1134031924401107840a001c181e002403204081400c00c10300c18104800030300446403010034031012421802c3c09000c00b00e1280700d03200301201559071500031105e400d042800d09209550030044103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 416581762 1250 416580512 416580523
    0xc181208040b07110409061a0f0109030b04050109140706030f050c0403060c0c06110714010209010c030503040614010f03060b01081b0915041202180606190c0c060807030e0f 76
    0x1020880701020a6000a005100343c8030261144c2c020410010340001d4a000405011003c100c80c10400340c00c01031944c1420154620030000314165207102c0f0180c210340d60503120b000040c200307584565030f401902c40000c003040142c071841401e0300000c1c10000d107010002001d0b1461003403c6ea000b00c0c100001c1c002035100010648054941c0b080c0c5c04240c00c0d0b403603d41220401030940c0060304660402245c501040e41c030780000c210090059070110f94610390440c00c03500b41e01c204011140051440e048900210344104082d540107403290f807010a2641464905a82c1c084082c1c002e641da000c1240020030811503280701c1c140c0180c20a00348040f441c40e00300e080610326218540c420521060010750044280e844204001e003803504035900d15141c43d111414440540040e100481c010081e8031a41d41c0c400c0f03101c0c16941e100b034400070001403078010103402c0c0c04c0f40d0180082c0c0100a209000040b1310006001080c000d014017016070349ca09141c5054007004050790302004590004c0c0d00001c46840103040301088 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 416583012 1250 416581762 416581769
    0x1502010b010807050c010e01060608070311030c030f040c0b0304060209120607092705090f0105060603040803040807030c060e0d030516080a1a060c03040906091103061e040c18120804 80
    0x1086511800a03030705c264007400c059a0404803551800c480800d51640040050740146604c1e6010861500c48140e030b10501e10045c3c0f41c110543c682070000460b50190303071200c107600500c142c90b150101c03540c80d04440301e684c100b1b580c111034540e00490801c0d402d05059403401d142d00030780700c01400981030140010707203004443d01400c0400400300c038058040b4aa0496000c214500c05607041041d4548100c03165103070515540503500350350901011a10a180c03a109680c0100d4200000503d180c44990b82d000c810b6011200031418852070010320400718505100d140c03150004c400150040b507008400c0102100c0000300b040301181c1284801e10b801c20b62006116078041d02111000500300041d46101200180b221180c0754801e07000a188041c0010201c054400c07140000f10a00c59603440d14641d6050302d0b4901c01d1409101410b2000138000c0c60000783c10480c1034164000081c0c594000000f00d02a07500480d000c10110780c01c800030240f00038071040d0b8400200b941e00620701115100359959903942c4120710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 416584262 1250 416583012 416583017
    0x2061e130b0601030b03191403040807140109091404052b0c020d0b010b0703020d1409010f0903080c0a110409110118090515032a040929011502010b010807 68
    0x70700044541c1d000350f0201c0500c08008007100c03c80510041c9102c034044541d04100c1d444020703910350300c103101030000070360301901c13081b4014204d80ca0814991200981c084080c42e4101706818a00046085840c0304d45900c02c05034480715840c81c505410700e02d103000301000040340102d0500b40c05100c1c0d140c800c200044000e0f04e0340303007a401844060000401001707000b100640321001c0c0c000000344a0301030324001c3c21843c2c420303025102516034001c4140d625401c0c1c2036000082220030410085e0940c441d03090003000030120308025105940301d0300c403408260081010004290305c04c0ca50b020034000600741c0d21404800440b0705003c0d503500d640d1141d501c901907980035818861100a483c0000c03c04031101000340c82040c8003003100b450103210300300103003041c9406180a401580002c0e0384035010304d030701504807014a0054504034200b450600005001c40380041c1c459008040c19103c4100640083c420044485a60b9000303035414400d039480f031440151450700542e8548150b040460340c002151035401100d90 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 416585512 1250 416584262 416584283
    0x18010c1112010e1c0207141003050a0e1204050a0b0906070f050703050307050c010908240601090503011b09061d0103020f0d09060c020c030f15040602160302061e13 72
    0x540328140075020f4066200054000c09125039100c024003a419003260001d03034202d07101c29683c2c0d0f94191807001d41214581c0c0142110720303500d400900940016410038500507001030007520041c0841d08000c100c030750401d20035000160401051800c404440080c0a110b0209440d087c0c064001a25600c0368540091140580036072000030300c982441100010b58102d800e4035650480e501c0c04940790203c48410034007241500fa00442d80c4d54000801c414040482d558a54902401201c40301e030408004088604200098401045544080c0601865004e0011110130040001c02019040d0038594000904107c010350404400701041d07209501040b40a080050343d46c0504071131902c031403195400b650f55030303400c0c0007210701040b003580d21601d245800742c0e090390701030310f940410540c590321250341c0c1942641c0614401c05605103040c5659400521503440180340040c0d0b4010b09038007481c040c1050380075801202c1004907900051135a504a604803800d10b107290307d0306410f82105002c81e1440500400d500307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 416586762 1250 416585512 416585539
    0x35040b18100c05090a06030204050a1403061323060a0b1504030f03030605040501080606360919150507020a031403100906090b011202090f010f0c061118010c11 70
    0x6070046540d80c4c003024040c8045240c5a0310080c010350b1162003030b54001c0300c00d40b0000501042c0000c07229007e02005004d03000e142c071855503a40b250120050709903600920444900c950710303922030805542c403242c070010f0610380c50401502800c95884500e400e020f02d4071000071b0050700c0303220403c44013030700e0780400715000d04016402d01f10020b12482c1c1141707820070b140500201d02a034000420380d00c100c40484a4a0f1446102e00c180c8a81990111100c0307030b480c03c400122180c0e5040388511641c049900401c550f401680d042103420040345100e0251044a420704982a04008a002d0f07641d101c1400c0c0000c02c404200c07030303074000d150700010f004220302010040086810700580308a0719006041c0e62006012550b21410000000d0034011030785400b0521001c408403d801081c02179440a034001402c055400c042c40340103403510031090503402c4c20800b2140742d44001451f2880354610b0301644030301f041d0701d5080120801540c0215440d480341070058840501c80094803080c086a00c50506960a0060426 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 416588012 1250 416586762 416586767
    0x180f09130212070e0f0408120c071e0201050d0f020d0f0228080403050307110a0803091011040b0f12090a110d0b01140105040801020c060f01051e0135040b18100c 71
    0xe0802380701040b089040505c1082003407c2c0103441c04074041d015101111081d03c000030541c1185d040c00a001c40e000b4015030a84015a5001e682c0c1654034600c05071801090880c00012181002c08250030141d021840301c042c82c0240c0031101c03100c03c5030110207014039001c060140102c0c800400050811000100060551784102d280d59074140280c800c4848103100343c5010a0290002ca43d0619184102e00013444c2007070300782c000c15554001d08080c03589043c1c104000407420340e200c000dc9a02181c010414030400741d2412403440c0c4182104c0000d4040e030344039031401100746180544100c1c4203ca8002c1c6150104003c64130450449001107074664084043c20010b03501801a9031000f03009520105500e0810311000c106103100f030000745000c50ba11303a280c108003c902020025404003c4806608140d50780d4015002c0380368023070417105002421040420031010b1b4a840051440782404624203000400240c1d100e03194000422594094103031030035004080c4e440c0030250b01460000d44036540b0303401250 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 416589262 1250 416588012 416588017
    0x1b06040f12031e140a02070c0302121e01060e0f04050c04090c05030124060212030c0a03180303090501050c0a0e01080c0d15030c1208180f09130212070e0f0408 70
    0x40e03401c1126a000f200071003000d8010441d10b07122640a810000000c1e620f07901d148220358010ba40f210f520342c0c005065800b801198102d801c1142502e10500400b148901c983e0105036040c411030a001007001030070b00248001002c4003134901b038040324002040c00300046000c540341c10ba59406903800941240c1c6810a0700440c203407a8445601742d4a4038800d0305c900320300002c05555a407200b046008500384d907054100e136201100c0a80c981c0021040c0b0100351502216401031003050301c5807a000c03425940d072400e424030384140684200d0111740d90344105401c211013070062561005103264a1414007261802c0234013454010100f0384d040081c4040052110a901020f40d002c80c030648004202c0d009021422040442c542c2c0825501002410800540c0a50088150510543c0b01c1c1c4070a0034100011460204028645030707882c2d00c02050005076400740c0303d481c8450301c10060024018000529070040c00b54030f80a203207610300f0780d80200e01c0521142083e6070240350428000000c0701030039907071400d0048690 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 416590512 1250 416589262 416589281
    0xb07050c06030c0c0106170a120c051204060201050f01030804150c0b040b0612012a050c0109030509013507090e01060504060f020606150904090c0306021b06040f1203 73
    0x1100200038043c501500c14064030448003000000c0100c0c42d03c4085421101c0c2c81800140255813050080b540003500310081900b00c0000ca06268242402d0390740c0d076500b051000c0300d08040300600403c0400c841030742400f520f81c1000160300243c04035415521071010911450080158040c500c0b0f8910080e82d00c240d000c10013054110f088508541040d14101c41c10a4054502501c103d000ca446054604410310030b0310303d005400c909503648144440070b1f0005040c0741d6030400b41880014407074401070100c00e025000340507109650302603032821100005000360741c02c0d1600103803089401041c0c0c9a44180d80d01c01800402d0712580c40e00a5a803400002c48040115401c00c8a01c0054900000f41694005002d4000d90701c0715115080000c802140490b515070044502503408810758005400712124240280030200014002150880854968151071419a44200e030b03caa40003070402042c8110300c0d000346c04084110041c007000c1c1030607240d07610380703407010342c0050f16410325040d4000bc2a8002d900c9a06107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 416591762 1250 416590512 416590519
    0x50a0e09060316262a15070605010e0109061d04080f0f04090b040207051509030433090806070302090402040f06050901030605040b130e210a02190209010b07050c 71
    0x16100d030030f090000404c0400341c12038240040780e5590b112001080b1100c3c04441d103124074a46141d004030003400d158900c0145034200c0b601c401c0b00080108084020400315000f05004619540f40c0400803201200507403114203c20716007681409000115001c410780c01c018280c54040035111410b05500d244200302510100072400643c1c0d1503149110304c00b41080f15590301c01040250f01500c00d02c030980c41079080c024041d81055050182e0440b003042e00c21b030050300c0c65007100d040540766001c40c03802c0d20601318a811002145508984c0c82d40c070485294030383c2c244a14040001505c1d041003142d4608029002c3c0b424150007061042d19601c03142c0c1505c1c004c0c80c10078403500600f40c0c1c4140141c415070102c21964002030a024001c035a90815019000c168103024002c101040d510000d884020300d501c1d80c02c01c085000c1c1c01c42100308800485058005148800105035442015045c064036002500b00101103070a607100c0070001603034800242e0360445682c100c1466030703007003641380050820340c076003408560 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 416593012 1250 416591762 416591803
    0x30a050a11070f020108090d050732071d010f0603091109070201061403070e1308090429120705060901050d0501080327242101150e09040809010207080703030305041101050a0e090603 80
    0x40d03164000cc4800440e102494490740c0482d40e4104a0b0825409002d10036405155a0081104e41d10030340c852250306020fa41100280401d0800150000e1416915040180e4440505220b0700404038140551440214014018249404010703040e6000c020100040841000c052005100d14002199800c0c140140200440c1121840c40200707032200f00100400b050703140c1ca400d61035080c4140c0d028450000c0d00010031600e4a0703d000c1201d00d038030429919040003c1841403540440d4a8083d03d0b01030600342d4041e40c0c441910a18000c80c41e00010303400c807104184400f0501c03041c0c454001d0680c090840300780f004e60203060000f0031111171282000c513843e48803c0780744808075803445c004228140d4083c0801e00c101030800080c1290060510b110301503101005c1d2012074001100361000304540c1303006005554825650b01c59550030b028041c4d0040c3c02007500e035010441000701c04880d030b0641130340c01d080c0541800c804040c024074010207403108070300030030038500418240e070380c1005911010400e5802c000d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 416594262 1250 416593012 416593103
    0x8070c050f0106170a1109070c0c08030702030c01260a091a0603070f0b1210030803010b191b0b0a0e0109030c0c080a08030a050a11070f020108090d0507 67
    0x240200184d206010424008050212080c0d40c041640c240041e001850780801a110b841002003003440038086006010301c49921100140e103c4003103c0040881c400610340301c003098014182400c030000ca005040001c072810b20b040c400b0342007196a0600fa5400c07100702306590b0303110201004003203000c40035040c081010a018100b00304c45440324480c2d0800e40039210380b941d0301c0c1c9218038076802034012041d00130800e0202e18841270046450f2540541c8546083c205d140e40d13600c403111968000e8104030307603014000440091100700301e01c80040302081c520f0301091002150094100b079803584c0100030700380aa072402146107241d46421000900903d100204000c105515000d0125040f400003103480c100118800107000c0d4000c120f91b017800750001281440c0d41e0b10590030000804008058001c0144e0303030402c240d100020807000e04100c034480d000a0020030080c0c0005843d0003402048111207511506000e229968084191910391f6403008440d901c40711940501c05401c0d88042c01c0101480081c603410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 416595512 1250 416594262 416594293
    0x61404060506010f0518220203040c0303110601030201170a0f060609080609011404030c1b030b0603161a07020d02120a1a040807080906120a0204090f14010608070c05 73
    0x6000e09804d8990341015042c0d1001521a40070f5070702429000e6202400e4883c1c0c9041c80300d0980d201504080d403820442c070107444c0800803a04280c4040da4000c4c00391405104054220100046001c031120040805614541c00245006040c49181012484c9100410060016504500f0140c0780c0501e09006c2a521000002c0c100c6034140300e000c0191040303c0c0400e440d007906108402022400b0001d0904c1581c03140c03070a8503211002001121000880f0181c8240f10b000c40d01d0700c04c0910310940101c2c00d5801d1441c100342c5090b51141e44c1140c00c000e81074081004252104459071a29102c6c11641c1c2c42ea0400d0001610a0300882030294010341003043c03e4041e01804aa8203882d207102d640c45140c41780001040a00030901110001c01c078800401048001c601168041d040812008107203900d0325104c06407501c003900d01550342c030024a4020030300740080e40d202d0040140741054a502004000b65a034004c410303d00c018130442c41030041c048080307409a48103010084980350004110740e450032529141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 416596762 1250 416595512 416595521
    0x1014040918020a2304050114060f0d020c03030114100905010e0a0506040909060606020d0c02130204050607110906040b090415060803030702210903100c26060a0b2506140406 76
    0x200494213281213580120f518061007424180d80c4e9040d1a0a02034218100b031041e43c5e8040501c000b1b54070000d120b0101d00d0030003800282000e100c8400610b4030f035403408070403c0800d40c42c610864820240c0c2010b00d48072030361044180342200e03006d2a01c8648080c505c0041000c0302c10703540249802003400240440c2d60b50030350300044003d0748161030400480c2c0d91400101e0301c1701e809d00d030b03d100060440103032500903240200e0004c9182c00503032001803400343e60b10001000d03613102101c2141c000f00700391000b19452500035120b0354041001c0d1400d1046500542c0003030003c840c001c00040c44400552480405280140c1c07050001d01440001c807a580c1c1003200c0040d640700805010042144000034005900307141500c151180c42001500402108150403070040c0540742070300d144000c0000e80c04407020013502288940c092019082c0403188107050420500080d0040303900304424000d01007280d91003c200c2510030100301c480b812071048040c1d5481c13800f24050030b40d4025040c94104601c007804107102c1503034070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 416598012 1250 416596762 416596799
    0x20c092a03061e0901060f0512010e04030f0e0d06090c0503030406051201051c031d090a0c030608030406020c091509240d080d1112010f051014040918020a 68
    0x1100c92601401c0001d0209548555011940044400004100641c000c022000383c00c07c6909001c2d042154500036501d045c2826800b220080700003900307000a0580200c481d000e1440140b070036030140901000031410519050710010038083d66507200f4018001103030f0401019140c028150b80e40c50b581c50708020000d8008014442d1403070440740000865240034598604c43c0388500c0e250008020142c1c5003590b00712181007500c131490b0b041c65004841c0f50b848140301032003000110b5000803000d4a0000007022220f80340c0004d00145d0017000180020340d00020501140d0710b0480c2c41105c240c1d22462150590500085169080030400c02802007a121107108100b420007003206e18814100003600f0800407083c1e644014050810030042418090035540040b1904a80c03001c40600e003251540e602103000320b09a12415507841d030f51100744054901400c0e0030310045014500071945118040503161980300c0d910900c02c055a445d0700c0d8401800c0300c107002014441d0001c03c00da061542e10000e035030070f0480303485 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 416599262 1250 416598012 416598019
    0x507081506130504020102150a1b050d18020d02040207080c010203010306061a12040821040f02030601050a030b07030c091e0503010501061704080a05090d0309080d030903020c092a0306 81
    0x1110700c06002d81d40f084602c250340581c01001422020880302d01c51031401b505400c0c2d4035443d0303e012028421040340b0b110b0381c2c2081fa55010750301c21f060341030901115004014881fa01250788000c02c00341c1c1e43c152808264940465005903190003070315103020140b284101c000707029400031000206000c8554009021030300d80d0420a400f500c00c2e4848815144114800c6a8110080c8000304010800c202c002c0c01c84c0750381301c0d0070041c0d441e024007106128035503044030304846c1c0d413000c02101c40860a0a00c0344500400f0f0680b403a0210500310741d14800040700041400d810165203604c0c000110744502e400790010b042c0620079881130200b40c014804942010700800340658200000014003510802509807107511114511889480b030350303181d010541c041054501004410722003448182c1e1548a841c1e40725200385c03105046645443d600f24205191112040241490500d491001c207801250034490601c5c2110284c929640e03150440069074943c41140c211809c100b003070301c892014014003c500400088 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 416600512 1250 416599262 416599279
    0x20a26040203011103072c280e040302100b040b1f031109060703030216021903030305060f061b0f030a030f0f150e04170d0f1a0102190507081506 64
    0x2c54080c2c2080c4403d640003000203200400304080d2000e60070607000c4142d207250440d1911f4094400042444a00b2000c0103510810040c1803041340e450100250f000700904245038000b844d0648000e901c03414007125200c1c21366160003800d04a03035516400750141a01c02040130101110102a41800c101d0455001000c20301c1c1020001942c900b5900f40d52403100010b2682c0c1c5451403554045029420001e48071710001e0103d0541801691500d03c2c2a049440558180c0e0040b45582401402e840010305954051100d40d0409000746e2910412140c00c0781051109103808404403689502d002d032480792009041c0404580c0080e0383d541038104070020160400700703201c2c00d01c85004c4502101c401001c40605859a900200404070380e20b58156405401018007001d98201c00c98a465542c1c03050410310f0903d40d44656112102c1007038842c17108042c4010b0b015400104000001070f64030620031340c00021a42c1c3c08080b50301040001c1240e64040c0800005680e204070b2041c2d50391030b401f203040e2101403003803121 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 416601762 1250 416600512 416600531
    0x2010e0409110409080d052a0a0903061d0a03260c1e0c15011503051b03090a0807060c090605030c0301050f0a080607021518030706020a2604020301 65
    0x60044001058000d0300500440d03110b4000c1000400c1800c42c01c44012006106101c2c0000c0e140c03003a00d00c0380c025281c0c0c1103180040c200da803c4501006e40c0c080036944e075040c80b042c0b112035401402ea509527070380442d000500301142a0980900030381f002e42c281a5105038403000c07040540c01070341d9102502d2609054070000103032800e0042141001c603442c130b00d02c0409100680154801100c101d14808500200702d1415407100207681c18030303400034034a0011076400801080f441c0305d19102900e00f92414941082035007031402050212032905941e0f07840d000000b201044040d1010300898481c40e910030030440d40c4180925000340500415010f050214903901c030002840c40c042c0381140d00c621010101c40d8a0b5a08000c20005803070f1458910b5900030301c4107503000c070b6036540c10094503010314031031b070020324551940c0f0201d00074001300100341110754246c06c401c0d00c094920000644141030746c000c030003507250218800101c900440039150100f000808a460200c06509120070300d00641c0290020f0006029 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 416603012 1250 416601762 416601769
    0x60b0901090e0a060f06030218040c060309021806011b0b01030203061b160519030206090c0303180105090609150408061302090c0307090b1b0709090c230301140402010e 74
    0x20000380e0b00380c2540102d030122001645543c13001d110b64882d290700213051510303500442c182c1c910030300c060924a9460303824882030050702141e810007082946400e01c2143d40319030100b00035141c07504040510200400110302e6580c000c1d00140c140c000c07202c2c1d021f00c40b403a8a0824000d500800c3c4000c0e0700a00484001c9840240c0404008000f190002d0905103094904420740c41c8021402c0780070344481c0120421540080500294507502d54002d900800841c1405652141403588011400b840b9070f10402c4149802d9205240010b500b1409007841600c441c41440071a4051040c03041c410b901020564031600100500342c060b00989190004070b510f44d61320703401180c07014000c01401960140000e400140380800c90b10055a1000951070409000c0d0307951108804a6004505c0201d0020100c18003102507034005c106240090500d00014801c0a01c2500c0704010b0005500914141000c00406040c400210087d0342c0c1900e030b000f80080100140075203d8404044059408070300140f400303085403600b4035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 416604262 1250 416603012 416603021
    0x4120c18021e0304111c1b05030c01080601120f06121a100b3f1503060c03150102120c060421090e060d1703040b010b040e06060a1b060b090109 63
    0x1607000c0a100840b12042c010080c0c185c02c0c80c6e0441008500c04c80f0b00f40000b904560b02d903040311104100c510003403800c040c10182000c84002000e810010300404201d0340d03030782c400400d140b41c03030f849200010710001c210589000341105400c03500303848401c800381c5420081800300c91034600d402c80d09555501e458100d2103400e0907001f03224558038a0070600c1400b00a101c0056094a2641407080e961f5a254194580814032803440c44006110361a460820460408010380c0d080c1e0340d40114060240384c0340900080403d070001810b80a20701d04450880441640201720105481c80f44a000d1901c3e10301718209652345a1085030f044980d100042000c1118200008030760718055610307201d901c4c8503418801c1e500200503000300400c0d03000d05154001d8002c60036000881440d00c1020462035500e01c2c090070a5561410306078001d20702c0d400d0400041040c40c40c0c80d58816000ba00c1165120303543c1c2680c910803903698000d14031040c0381d840c0c3d0380f10b80020000340380c1c0400038203901651070040c260f80e154444800c0302c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 416605512 1250 416604262 416604271
    0x1b0303020d0c050c0603130609050c1201020a0503011205120309030d110c1c090b0c060609070219080913020a020109051b0102030703080603100c050c0106090501060504120c18021e03 80
    0x59101507213103141e40c40c200019540c001040340300403401e010030341c44020a03100c50040039103407900100111051818200c40c01c1282c1c0c42c807c00250b00d085560b00c0c004082c2d100520444070f119401541080c01c00805001003040c54460f101c10a840e400e0030051103440340d02100030b40c800c0d10302d06260110a605464240d0300c40c14041005007040164500c100c400c6042c44072180000c02c4903d04001ca40c4500314800707890340030302800080000d443e050061200054020741103e00f95880500319510082950741103451403940050996224000840071030008800c01c0040b054090001c101088011380c15441081c0320303400b0f003040720501044000a040c9098400c5051070050308100b10140210340141d09003a0030070350190488141c80060100e1100f00c0d40c0140c0c05800240e0f000449260011090291001900d103504081029524208000d0301e42d108611400101c41110180e0005220012a600c802040b11507100d6a80420f8800200c0082d444205942c6174201c000004d1070041e030402058138842c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 416606762 1250 416605512 416605523
    0x305030115021504060e0f010606030f0b04020f1603030e030301241107061d18062407020d03032405042307030905033901090209040813031b0303020d0c 67
    0x310b413039a07203135400a400d0f8140c00b02d409114030304012004030402d00c100401081550350020381c0d00030904003001520100c0e10070034400c60040c072416000d05a040208c0c0c440d01800d84411081030210b25043d400741440700807003a10703400040000135000e281c3c03807a0034419210750071280148041c6050160f4082152154009081e4404102441018000c2a044032055880c3c81c01d40c000104076000034003010381d1002041600d96409050000604015480400b0481c28002c043c2850f041c1e4000ca100500800c08042d00c29880e03083e100c01450f00030392081400a00c0f1800e12070301c9400482080040010503c20180034a20700064035070070300303000c441e40d040c524595071030820103480c1c07000220081d00e0b0800040e81d207404100490b21600d4000020321010107481c000a07240c014000d103100c0e0461a03160042c2007264181081800140e90f002c46e10390748694404022501c50021401c0183d191a094200a201040d021000080e0340d00346403200c01203900c2542190500315200104480b505181c0031300402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 416608012 1250 416606762 416606803
    0x21f06151107050909120705250e060f04060302060304051c0504140909010615020706021b03030a110f0102180a050102010b06040312021f021e03060109050409020604030609030503011502 82
    0x49242404a061700020f00300c0c100c4d5030580010290b40b0b40c83d8000c01e01210190720201c401901060070101c50580381c031141c0200d0480a25155100c0e54440f002003046100e50010002d10036280c0d220ba01110142d50050300c0303551030340750515089949080421851025846108048110a10990031181504c0c60005500300f0200b00300c1c2440705080707000e00f261a45540319040401c211015002605040032158000e002d404c0c600107003e414140c0c1e9496009203680240c992103110b07100001102c400d05680c0c07408000300d109260109091101c44502d5040a500000c0e403500c5110410340e4a458403c1e089411f011003d076102c3c016800c9400d1142c1c41a0048424007040021840c0012428045101401a00c007203050068188140c00c0c40050374802e059404104003030f004000c1c030303a01d41c001c80ea04100d551550400c0d6001a00a184510805204549030f6001001310345a40056800a5500480511002c801480c000d00160424040c08154030080c14040707045500c002004584510701226100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 416609262 1250 416608012 416608019
    0x80a14031e1902070f0c23011b0b09030702040b18011a0d0507082403030d0b041509050412030501030b040206090103090b0403030614090103080a050901021f06151107 73
    0x200c00d010000e0005a42502e081d00030070350880c4500007081c025100d55001e40c81e0100b980303409444400d541e085000048011403600d002244ca07002000b02d01c01c000d0814009485500a83c51000700c0180c9004104506c020240700d08100000041c10101d07108a8062003201e003208184080d42400688180641c6980401042035001010818091080414206141c500d4138811070301650410340303100000412070400c10411030181160395000a07886024030b4840900320300026a070f8040d885003034122581d164081625903940d6881250007940c010f600d200345d1691880b225000309002c847c182c640900419103440c00394800c1c071545040e254816041c0016454bd60244034403608041d00171418140e4500c98240410742000813940304520a540101d0060f0a080303140d020701c000c2542c15406041e545006100003445181512030a03001450b02caa10ac810b802c004038600644010024142c040c43c640003903098516400c07182c15503d00c0c003408039a01d0403040013154400e99403048001d441c0c000480c1030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 416610512 1250 416609262 416609311
    0x70c26032502011205070806041103100e06060d05010b0d0e0d020a08070602091e0102012412030203160f0b070e0105070212031e180102150103151107080a1403 70
    0x609180180b44c113214159204040c03e04407901a1024004907281c001000000d1800b40111005203404805580c114103101022a20010050007506003c5510000041d02c42d11007005031100c019008009001035650380c2180c0c0d07e80e5200c0c200d02c015460410710074501c0410b000840d0860342c411035005200001072502c03007814503009242d04840b210f4007001128141d9407040804811401ca030b0700300c1c80015505800190848042e44c06606d860034410b00c140d100c1454124100d002c480004005d9086054030b0300d0105c2c01c5d4402e0140016148000b20084418003040300700c0c10000e6485a036990039a604d482d4000e64803005042d4070540050801c100303040050800711460074800308442c0c120303404d00030300c145081c20300040781c041c00b02c107000041032004508005140800200d40f00307001900000c80100c0010380140c4050001500c40e600e0000c072800102c0e040c0d4000d041c141c0000c5112a15488149400000f641c4154804000107040420701d402d00d494050032240580c8543c003c05041e40d4852105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 416611762 1250 416610512 416610577
    0x90311161a03090607031a0402070b0717090309010e0409020d38060d020d080a0c021c051e0a0203070e01081515040c020a150c081e0403030b06070c2603 67
    0x442c07d0a200004c3c0d12030284e15a40054440d240c400c072100c4190345000b090050900110410101c00e80e00503a0920950b41b6002c012185030060038070b800c0050720701100c0410068460404000e4004402d80d4691060000c401d0b030414190a069034804e8400301201158044006e07440440172038020904003007803a03894000c480081c1e062018000580c0d01803641c90b4072005401c042ca0020224400e40c030079008504d840788007000c5142d544140c0c10540c51050726580e0340e400400d14400721030202149030042440301007040c030305519030080441e0350703950303c6d4a14000d4200080c46180d8061051000582c0040c64400f40c4c1c40c841ea01700d40000100e11503d10800c8064a8070411100c294029040c2d10130204190300c1c04010400c4050b1030208014501d1400204003420051102070000303044551100a1090510000d4005401d2310b0041020001480011800d1140041c02018840d0b00c28000420740310081a100c126110001d0b42c1c1c1940343c100452079141e224880f200c03a49a90325039250000f002c451341e50b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 416613012 1250 416611762 416611781
    0x4021503040f32030f0702040509030d2406020d140a27030b07090b031b09130b040506030307020307030b070903080c0a1e1203090311161a0309060703 66
    0x340741c01020600c0c3c440e50707058502500c035660014001081d00d044608043c0210383e120182c01c004519205004c2d090403554052100024030542d11900401d4002c10300300142d500000307a031507003004a1000c03040305410200820120040c0901d00c0c084c001000790010404045411785625031754203180d00501910842c0d070200901c0428000c8009074000380d00742c010007900f1038580c2d20120303100460440c20444028400103020b00c080007090001484050401025680c000c41e00c05148207145072509980703152402a040460b40160428a00c1c40344001e1302d80004000290954042105e600d0350070606031248a500400394040c1c3c0090010070000b051400601c1e030040700c615103030904540f6070b540c0f52400c0e4000c0e00e00c5001036204590810510000400070050319401d61045507401d403440e56406008044204c400d42415903810280c4140743c026039000211948a00648001c502c80340402004e40d0f9050189068010055810850b51000b45040740e01540d0100014022591581c10440180041e6071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 416614262 1250 416613012 416613023
    0x7030c0204061e08060903090a03030e0f060315090601030b06180414090a0c081903030504030201110d0603110409083103140c030a030516060b03030403120f080402150304 75
    0x8000904501c00d00104005660000c3c41030349094500100c0314641a001b41101086420800c20007201c2d544d42c90076201126071600b04040d6040005000515140c5150000c0d90045000010410108290b00304418206403c40300324049454440046084070060203459420140401900400c0c4c02002c0303485070640780041c408a07410070001540a00c0074016540507245a0141840700200910003a240740034210000003130005542c842609182596240c401171305042d0f4a00c00304051500c03c0d00010000a01c0a0201d90b58040004994006010b60320041c4e4035256080e03400181c0d481c0500a4894035504280220700f8415404407410b401000814006071107810440b40c1011814a80d1500000303600642030510343c4100f02e1880c03801c12411107500c2c1d02c01d801c01c401c10000070350428155066140380703041c417510a41d079501c0c01c04024890140419498800828004100b01e2206601c56506d4800d9850301c0d910780802500750303440402502c000303501c504076140350001010000059030b8454082e5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 416615512 1250 416614262 416614271
    0x31b020615040b0f10170a0b0f0d05031201031212090c1e08010f0507030b0303090a150318140d0c0812070e041d0610080309060d060e09010609050105040903020307030c0204 76
    0x10000315601840482d20010510000034140702010f1102c680303030b1200d800e20303060040764004400581c2212031100c42900c0ac41000b0404024080104240d800481001d82070aa031940c5a040034440c0030b2807420000d001401c070308411032700d090241c0150450181e001031206000d5040071140c58403c40744a5007110f401030304460000c5c03210742c01d00078034401140c81d40300010035040001006003904c1c48900ca5a0003541300b00150601911500c0d41001240d0482c400c3c00400d184202c02100030f00101448801c2c0300f02c160b1404424402541114401000304108560700b00d02c00100c1600c410000346405030070000c0078485240c055010103502a0700940c20325003280c4c41d0380ca2000280842e40562035655840503a800c8440500104000c2c0c242c000d1008a08101054505030b0066540e105d00c450441c020034010400140f55600354020740082c003d8100c0d6003043d45400e41202d402024584103d000c82814a0300016041c2454032610b0486a055406546494401e480584190700901c030120b030005e0b42c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 416616762 1250 416615512 416615539
    0xb0403080901170c03040c060f0e12120a0305010906080601031a040501060909050f0d02062a0903070303020f0105060d020109030f2604091d06061504030b0106031b020615040b 77
    0x803403c032880303529440d849a0b101d00b8213040480d26a1000d401c5082806807400b1702a040c1c2c0c1d0881407010a00d0f10446540303500c21901d400031030814003c0643c03003001600101c2d10400480d050380007541a504c101c03404201c480e640d00182c9965401c284000b174019241c03c43e10100b00d006511400c0d0b840307405038001140c81035807416030700d084a501e4031050313601d40c0045000092020f014404003071440c4240c03004084504011022208154001c0c00e40d10942400d50090700c03c10031100d09a40c074054004090300d80f0309a5030308010792038540340c0e05040c0c02035103048002061842c264a092030704036010b81d60961424190390340e07c2d00035044131405441c0303200b0206002e1198150b08540604408013248400c2c2c40314502200101510400205482d440954801d4250f1201001690b50360241044800c40449000000b2080c0c0320301c80c41c0c1000c0d111201040c00816000e1305500102103103010243d0110441414a0b012601d0704400c1e98880144015a024021149865004400d44c8900104030000880c1d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 416618012 1250 416616762 416616797
    0x10c0807050f1e09090a0911040b0f090702010507350a09140c01090f03020303090d0206130602150a05091c021204030c1a030c03060d080c0d0e0a09060b0403080901 72
    0x1a0b0101641d10715000516900039052451281d900300b00369903401e00c0a9181f5030303558520082411a21405a5503901415030b2a56480c40003641d41b4030b010380700201c5802c1c0307404e000b03010301320449100c40814080022500030344041c580034050b08603a580d201c00500c50345c050443e070b10300d000340c000c0c424107841c0d0306040042980c546d15140030f4500d200050007280191030025156000d258031240000650f070030100b0168401000321145000c045842d0030342c41d401480011850b002d000310706440341c5207040001c564650000f5407110025050108100c2d5a0340b0201d606040e21411209206150400b8417180740c64132101c1c40c940c1000341c250040c0e0303840081a6410014641255000381d401d0180c448040100d030202070401140752000b00e48003842c43ca0a031805d48120701c0080d1140b800782020011081c20700240e01c040e41e56659a1400392130720321920342c200800110030b04400302d11480d9079481c005544151849044103c40c013203580d4078242450b507224015960481420141800030030300c01001c9000c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 416619262 1250 416618012 416618047
    0x70210140c0d08010812070b040201030213030b011d090c04050702030c10050f010f0b04060c03210902011706030c0f060409050916090b1302160b0126010c0807050f 72
    0x1074540c0e00030180c00c014500300800b40541030f48003c100b5041090042c0c10b18100c401252002d6030040440e0406840e20310049000f407203414240c814008101e5008020460842c41d6241214403030003041a8207040c0714843d5458800036075106c042540241c40300c2c0e50b982019000b156010300350740143c0e8100488000010f0038400188000215207070703548200615400b0015245024080b0084110489402d11801600c81c2c440d0340038030014420100441c40402d481220034008840104034002c06002800c00e03420701401074448201d01041200034901424840f4400c075034416500240105400d141210a0010a00c0d082c070399240c00900c1000085103c19040c05450301500110004085401022289100c014010b0700300d420080d06064050089075601154801031510500006070fa03411411210b081c440d0f5011402000e200080c800021000e00d220301c2c4110314000e9041000c8003450070b0f0445800c0354030601103000840c68480c0810760741c80c49500503120141e60000b40701c0c074001107010f601c008032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 416620512 1250 416619262 416619277
    0xa0c08041410020a030902011704030f21060b04030203190c29041202120102030c040902030619030b1008120406030510170705040c052703011e0501031e0807021014 72
    0xf5151b41c000e01c1156800b000700700a0300000305050444c0d003020303580140952650300b648420400882c2c0d1151704401d4800f90229903024611041100c6a0380300600d2280707801034401079200c0d009110010072540a019200e0520540c040c80d012001810f08840040c0781904558541c0043c6c101c01c0c0300000c014112000700f0141c6900341440250819610400500303848400c2903100e9640103006100700361350068161400d540440101581f45d81d54000468a804846680301300e5100110b0700000034801215202c0d4010134460f1405502c080d141c6030700300da461102c40c00c2c0c403240c0c500810081042c039110791720558008107812095041c00d40d503114481000190085d8a440d00c0d0007c1c9010030451826200da400f01944034102581032101303000040e0580004030444282c03c0e18100ca1182d119507003980700c810440c0f81c50794003850104606088400401090200721441c580300384036404034880f01e03140446c01c80d43c45820a480c00c00c8684c20300091030000e0b280700c5d0501c0610300c807840403242c0300000340c0805c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 416621762 1250 416620512 416620517
    0x2a0f050a03061a191b030e0d02091f171209120f030a031a09071101020c010e01021308030403380108030c06060108161d030d12050a0c08041410020a 65
    0xe4010a001c044900000b00f0a94401d1001e000012008140400d0007024071729094101404001c80701404202c550011240081d40300707061904008401c0c50340100c000c1540301c4c0200c078009460300d8409100c80d0a918231070511550b4050080c410580076108010072002c07402170090000c01d140507581600c0d01c1c00c00320f000000d9410101d0303180003a961511500030351700a0b02c8818503515610740041a00740c6005002c0f10108103c0300252840382600350111202030b07800d20020080040700e1141c42d4002e4006143c15540e65485100000360140c002040d2010380b070304480001d10051030b100d000401d120611910009400e80550f00703d01490810345442e008052420245a44006011b80b003410004002c0c00c0e24144104482031005407c3c09844011409025041110b0840140900d041c2c1484410701c4c5103a241c400c000c1e9102c1322941c1300c500c249410302c0b23a10b0240410740304c0c1e00042e01a00c8201541c0c50000f200c09000902040c90504a900c0d01c0c0f50502c196801400b000c08960181c0e4032100030300c2c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 416623012 1250 416621762 416621767
    0x3080c030c0c04090b0f0702011b03060503060105030d080708090f0303010f1e0b0904090309080703050708071401080402130b18092109060307140c012a0f050a03061a 73
    0x7510401442405800c0d40202c90400520207643c1e00d140302c107080a0305000340801e02400007051107000b58031400314a0076000c500c500d2443e076240018090300c03041c05030074000d000341e0000142a0400146108000f405519219481d60300c2c00012140703078800070140d42040c402c00349480c080b16001e100446c0a07041c0050b0b0002c1c001d0801210559415800307a982c0d04003480c01c1b00400c0001641401c0d14140582240e002c04d40030260304080b6108a4584c100342810700841000004000700098114104c9880000383e818903545c13040a8007080e8440c90456000c100c03014000340043c502071050000043d1070400005842c0b02c4180461803010445042c1c00314642e6080910038508420072541e403404003015403550f041405828896141c0c040d080545000b09401700104a0140c00380001130625000c5a82c060349450081d00c1d1613020302645401c1103140080244142004201000c49003c40400d0ba1a0b04e00310190b2000c0403146075020065000c101903503894041015001c070094500040d100061864 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 416624262 1250 416623012 416623027
    0xc0c0b0a090f080c0102070303080c070c0f0503150412140c0102030709060201060f21051507121b08070825020109050c042a022d060c0901050417010603080c03 70
    0x142c0c00074854110303030000d42c4412081c10031170b83c1c0081c60006490341131a00c0d2000d0f8444180398080c2d809420802000c4020328a800303d40e040b600807100b41201c004900702ca83e90915854440c2110307005480180508000d040200c1c6e04500809600800b4104028500e00d41003400600c40c0c22a04141c5000f400075110b0071080144030380c240a5400904070050701d1444852a045250203803c074900440d048420102820009205080c050702003031078500c0520680b540b8204100034601142e81004501d0036180c2101d0142080344201340b005200c005845044968031043d1050741c040303000500314060105030b42940c1c7e0904c11564a0f030010f14a0725000070520b19803d01e000c0d41441000d101c1580503d00e000003004500703003a000c020004503280c2c3c0040d100001003540481c1030003080c0c4109440074107a03060181c3e0010b00d8172180e810782002401581c1301034484046401881c800c032054140000d00a00c000c0c01000d80220301c041030b2010407400050b0303980c0d403580d4090484d00600d6100e01d00d90008034020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 416625512 1250 416624262 416624279
    0xa030609020f0a0609120f0602071a010b0702060a080604090203010e0304180e030301030f0503040812030f070305092d06090d20120901020c0d11030706020303160c0c0b0a09 76
    0x10384071a508569407043e8a0400d00010504200c034850901a00680300d0504180211482c020310343c290010300c251b42e43d500e1420021220503070110100301480030302000044c05120740c4151182603034003c1c0f10302c1c640203181404403030b20b10010348046d034403d581d42c22103001039400740b0408442610200185131030302e103440d86500600c404034881080780790804860603151040401207a05483c2d11400144052075a410168558015074001c90380760310494030690301f0041000041c5100300c441d1010000c403540d8016085055034002d1b91031061650000502e03040c6104420a034450382c922110700d005069160080e4145084000c1d12103050340d4000400c040d0145500c0b820307901d0700d00300480d820468605000d460658805840101003034821022a01c1c1507140e1080c07004400018000308070045900c4c15007451321055000c42d107010320074406d00030b00180c0c031030020040c2e078070403244500440d091050205042e1200c0d482d012007210304081401c030120381c600c0504090101105650b42c1c0b02409410440307107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 416626762 1250 416625512 416625529
    0x5070e0402040305070e130606060207030204110a082d010b07050607020f0601091d010f0605100c0807060903050909090102040e011a031602210304051005061507110a03060902 77
    0x805004500401c014008200d002500030120b44d0250b0281079207585080c0c0710b200001001030002c01c0c2c1c0e420a20f0006103182c0c0000c2d0201928000c95040290050b201d0148006108020104010400000008080000d02d0034001281c91941422549403c01c110401d60170741001d07000700048c00800304000080c4282040500d0340201c580c00140340c0c2003010310200e42ea908052044012040d11a400d0132011a84401c2d182e0307400210030300034851030b46111746070f40141010340035141c081c002d0038020785840c030b02c00c0c0c007210000d94000d02c116140840d1610380101802d070300c41e07003602400000c1020900e1500e0750040203106240107070005840320b0a0030800c000c07240040e408081c1d400c0c100c0a000d070001000c8030481e608a02c264900c12080d40da82c010903801d04403405c07540740c680da01440d9002d003800c030f03000f004510652044007905c120003036000c0030303104036a820303140036800c50781e11540500c40c80061001441e9803409180c619122072031400000c0c85c10b003125041150304a8541486600710706107c2075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 416628012 1250 416626762 416626787
    0x3110f19082d03030412021c0c0b090d27050616050d05040b0a0305061503070f020c1207060c030203070b0c070201030e01050402130c110102070309260c04020a050c0a03030507 77
    0x30b400a402c0151555680c2c078080540040c2440008600c40daa4a90080190754402541000c0380b40c00d04442e0703403001c1c1c051880d040c0107455030380740500014442000841c41100c1c1c500e041c3c841010f034901c021244000300512001c0000c1e03032480036070041070907a914409031910303038060b07400900da01c00580313800f80c20140200e80040511505000511106d142c8009a0300a40c00c9442c00003441d070b480700000740206c0c03603504028080003c00000c0c070a04543c841e06004020400e5002c03176980141c001c05000000141d02d280816980250f107003807041c07a214514a0303441038043c4c4102c90502c41540c49500102c403069520654003071001400e0b000315600f500a0b02220b10114008010710310380354020070b40c90030250508188d0b01e40e50790b4111500754011a041e003c1c81011000231034480310b4614003e4000038260113590b0035501c03000e5151b86d00342013400d00810f42c080e480707018041d0007a801c1e043c000a504411181e4080c84800c2c49000b00000c010002300c0303051406a41e010604c0c4c01c05030342c0680b41600000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 416629262 1250 416628012 416628073
    0x30f0703020d02010c0903020915040908030601030b0102120d0908040803040f0501030f0921111002040302040506030f030d021e120f010504110306130b13050103050c01050403110f1908 81
    0x1034000102d5030000e46d401c003203d070103030781e00003441e903c48503c149070540e098003107640949030803820001d12016070043c40c803a203c02e807400c000305241c042c016a43c46041c1004014280c0082065000783e07011904114400f80c4190059400e0545840c080c9085400c41e41000b858400388060802007580e0600840400c009048020404107105403580c64a01c0034000040841100801e280c8890f64813884104d040c5107251410784071044e5116040201951003840164803a50801d03001c1000c2c1c0c036002c5a48490000540021880c1040e01040386d000b9400450105a07a841d13404480c1030090380b0b000082440364002c1c103141280385030042000d4101c16040e000140124540f01c84800c0030800c03942100d8101100f1100c4020f000d440150701c0d0051b010a075011600215007125040780c5c0081138004038141d82c45201900c41165094004451a0043d848050700702c006422041466050034111036007205005413254803109031118020300301d20381c0760780024425480070304a214070038442c1c1140798460700500c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 416630512 1250 416629262 416629271
    0x20304080706051e0f2b0f051b090d111f030509010c0207080d080901090f0b04050f1b1e0a08100b040b0d080f121005030f0606091f08030f0703020d0201 67
    0x40c0c01c0c42000d00400c0040c0700d200303410807404186901074000c0b001b648419448103110ba08030345001d81c80504415030b5401021045685600202e42c0e0402c29207041c2c0744003500ca05000e14040c1c95600d00d0b02e1515880c6da420042841c858181c040c1c02c0c0c542045181100c0d01d01084609000300400e0031a28150142401c41d003000d2803e20038500046410030280300d031440d0594050312080165070040040240003070054040d201170100b0003030101c000c0780c8604d000c2e400b91814044001c19071502e40c81d444000c0030031480125030100e4a850500d11950300c490380210b414040c0020440440c403083c0d810b402c5950103910282c6101011203050007000004036090324140140050100402c07103c1c01c070701c07400624407a40400d12041c00c40c2c100c81900e02e00300030003028003400e092425006500c8405402414080c0c080c0013824100e0f8200000d00324003620300a031071013103195074251100420300d00e1500000c403c94a420400100c04108101a0440300d50a200c055603c0c1c0c6245400782c81c010b808480c440559050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 416631762 1250 416630512 416630527
    0x403120b040c1d031219090503011802011103090904060903030b0904110a14090403270f09060501081e0a0e07091b08070f0c02040f1a15040f120201020304080706051e 73
    0x203000c0d1b4038680e00c01246500b08092010003542e15008a030800b6826610304200c2c2c484011100000c040c0c036a000303807110b9018544c9105026103912402d12025003045240c0f011070300007000f6922170403650740030780f90003d051010000060700c0084240d805690907400e58805400500c0c044030030700d004201d003803007074020600140c0201f4281d0000407c003506000741180124242d244094041210700010b102000000f5241d0b0807000704080c640c0100c01c0c61030300c2d201c0040750a500585c4c4007030080d840000c03030020030b5550040304c0100c100010003041c940e5031181300380040c407542000410302908003042d0100d259128180ca114140d078211a1203000c11500009004045404c071011003011405490304c02c1011145002142c003400604041701c07919031070880050071200711040c05025020045138000c458407801c600903000d82c011400b03444004000c3d0300080061044041314660014412f0040c4c9040643d503c1030755041c6000c0c0d9010354042080011403000984003015005410301000704043d013450407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 416633012 1250 416631762 416631793
    0xa0206040230030a02010515030c150f1b010b09070f1d0a080607030516050901081005030114011806120821010909150203010803030403120b040c1d03 66
    0x809440640125144010207810b05a103a00b500704056403062410341079003104244690340c3d0b1001e4980c000552030100810030820440c0b02840c0804070040080035840500e004019030014218401045400c0c2045209071a11100c0040c0c0004901d0f600448141c0c1c5000f000542501c1403003901d5841103a10100304880e454204900100d005038038500724030580d107000e940c072010885881145500401c42030000a0312500048c4251082055540c24400d03070f2190352586403903080f581d04c81c9000c54002d0081140c42d51180d588198030603240741c00c0b215110f0f66803010074215030140a81d9407026054000600c03071003465016190b0309642d84402003042900d81400800d458031260b9000306034034000216041018242044160b0b8445100369414407940d46050000060981c404101c903031640c046130b401000387c4c144c800d0300d040790540c1c070166195644940d4122015610200f514107240c0d9078540e2020b0759241c610810104d1525503c6040e04070b00480700080c8214071900b0418420303031050725038801404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 416634262 1250 416633012 416633023
    0x110610030b04030e030a0803010303020d09030308150a031401200705120f190e0102070602011a0105030c070f0c05010809010e0a1b03061a150313121e080a0507050a02 73
    0x80e0070200031546902c452400b1281d120344550f481d54144103210055051000740d50046040342e10a408480500c011584241d820b402c0601c80540801e4000e0001200c14100800c0010344000041507070011607166030702d02c1201c6101c814807a03035a072b544481c1c40510340da08584241c440e5480c00c04203802c003919995026650200101541001c12001c10016001c00d07e41c402e6400c05032124441e80c101c001400d030020001540c1010813401841a4600021618018421140122095a0b800700020305810040d01c2c03a92001d08401c0c0c078814100a00c034049035101160105440c42401c1130213806240c40d00040901c000076000c9102c50b45054020003021000007051004190322004480c0c8400c2000320ba100300c5049948064411428003401289805d9011886150200111211084901c7c0d207030b80d48400703000c200e44404201d161421031002040b403090590284035014a82813410f49190800305c2d500303001c41a03060001c070f074141301481407000f070602130703203510003018a4240c0c05c1c8034061500035500d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 416635512 1250 416634262 416634269
    0x200a0201030c0c080d15050402071505100e070e01260a09060b0303120603011803020a0f0507030c14010e01030c1202070c0b07120201150f0302060a0e0405100501110610 74
    0x55a5201d00b4040900a1550014003078101d14920345462416500102804203041603141308140c0010201e0140303028400d56004581003241e480103c0c1c40312540c1c10040c08040c20b070051240e80240300003440082c2c0300c5c020303104d03000035558650310a407260009020709607001d8810444545001e04945c00915801219a200781e10507404503c043e40303410544010a20040c41c00d4160200250038031068070055200b5000317220a800030480359540c4080c0e00c4170600111790003001a0444800f04000c1106960240501801203050366092560380da1811001c0c1c0a82e0b004007808070002e6008151582c2048000c44500401c2c00c0034404540180f01c024846881e114601801607400305040c401d00000807800c030040c0c401c104040f5500c45142c02c001400842034003c3c98019030a051300f07004000c54080301c02c0c0807182c521036a180854159420004160011007142c42006001c0c815102c00f46c0d61806454094100f4040700c0101038140320006120070304140c80e4071216030210701030001d032140c0c0c8c0030a64100e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 416636762 1250 416635512 416635517
    0x90b0108040f080901030b03070f05031504050a200a0306091b030b1f03050604050102091507030509041a101e09050303070f03090b030f0a05090a021509032b200a0201 73
    0x4900741301c1c005030002c02010209941503c65000c02260940241d001c1c441034401c1102259030b40c030081401c000c84080106c2d0018042d412048120f4000350700301c0d442020018040e514510144e080c10048ac501540036441038560303945408681c0140f00231040d45020801c021f01d42c0700e110505644841c140203c0c05015031080000c0718042c444401c1c0c0105504014640c442d00380c0d0341600385804d2040c0030350007403041e0501c00c502030f491740789031807021204591415606403926401e0035541001c000c001d0680c044c480150300b09400080d2025540e0708080040c45007242c448184c0300140e103200c00c0303030007510858050602607c0c00d0240304666000040d141069400348003054954918902220701681c2c82e40b040c5022030010061102c203103c4622600e02c110407407202007209688521038150703a202d8a40c0060341014a0b64000100d8040340c0340101079100000c0c04940150410101302401800601c50354000b1045e403014100b212070b0b020303a1580f4204d5041900c2074821144080040e154010354600906 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 416638012 1250 416636762 416636767
    0x22803030f0509030102120601020105010503033402040e0109061803090312021509010c17060121063c08070e0a11040602010b1002070b0d020304050f16090b0108040f08 74
    0x70100e01c80c404a560104020307009644901e100702810300d400c00280d03503650165080c4400440d0a044c008242d403244d00d411180480340407006081003150031400104003140d9200e0440c6000945c559005006100000d8070001a00100c41d0a0180403950100c0107041c2500c5400001004a54400c4044041d0307600041075106814507600180d2030b001036200550300ea81ba001081000a450641c403d039490405a12020790f6000c602e14480610320302115031301e0104030003940e0190030780380d040199a6155500c810000c1c08584408204041c582075804100e484d20140f40103040c51007101c030348945090031040170000701e5400d11507515181c443c0d034020321a62418400004819900c0b40d0001800403412140140d96240c82e180000c1c060494441068082c840d407020801001d48000f4900080b50819403680d410b04804210010103984050b01c140c5541c41403104c05121524180300b03008503c0c040700c003120095481c0c21240d105440c0700044440c18007001c81c00b0070010458541c0d10000156200c111141e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 416639262 1250 416638012 416638037
    0x9080703060b13060608090c060a0512280213050301020405030d1b0b040309060215010b03240907090e09060405030a030c180f08070e0c0f090604091802280303 70
    0x310f01c84994000c4121040c103215000a020b1341241c00d4500494403c029201c00c10001c1082c04014407a007020203000503010403c0c00c0f070203000691203641190002040c140128200100240e41104010410804660000342150013404161085000304400e40003542041d00e0800000d444a0030240580d0500000f0344802042e01007914900503144ea000030203080d2828a8103005024107401d010b044054443c003440075110381c80740d0704014100c2d01920203403844c59441c400c043c1c81c0403c548405030700e41c051003120166141c0d10400c1c0c0600ca00c1181d80c4800e03550340780844010b4102c4000c3c1099070305402080a01c8080f80c0b0100464000c0e826030305000c1840e003406a0103c0d41207290703072020b01e020041c3e91004205222104070f4882102c48040c00c4580280e101c142ca0b204003001910078035071111041248034006000035014040c1c40c00000c044504256a0700090000d881609030248404000c10030244210301e0301d1780c10074585690902010805c50003003001201074084030300010301440090070200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 416640512 1250 416639262 416639269
    0xf07080a0b1e010602030405090c181302040306023013110a0302060d09020405060f01020303010909230d0201110304020f0d0501180c090e031c020a0306120807030305010609080703060b 81
    0x41d0b4000e25444a007820b40d0703034811009440381c2050189900c0350350f01102040c007544060007500c460080d08102a10030144290421100d114400c1c043e00c00e46400b03000000225aa610160081203d0030644100c6002506101c220150241d25590305019544d005d002150620101c090015031f405101030001c0c22038000019031201695000a512030000522690072840503080007415900c203880c01e01842d1121710801602c18000c04c16580103901c00d20040000c084560000441d031401842c4440e200f611140c0b440e101080199000c07045070340300c102c02c01152542441002c2c169031040405c282581410340c0007a0108118040c41413040c4410805002841400c1d4461509000d180030303082900e01c8149440000008648240302e400d52610104c003212560100c00c84400760400101110122190a104070003500840d000c80c0030140c2c0c07144042900b0a070290602481402602e0041d01c85400d440e009007030b544146c020008011941404200c0c2c18000111401682c0c2c1c4480082514400c0c003012 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 416641762 1250 416640512 416640541
    0x1d03010209040501090213300f05060c070507090b09010303030e010f0f0b150703020d0f0c0516031202010b100507051f06030b010b090307090b03031201060905030f07080a0b 76
    0x601e03500a10b00400001c20b24540ea0080540300503c4092800c1c90b03944030508a201d662551403480400604104404001145a21007140030300c83c201914440b00c0d6500c0d502d14010044890050510b00040c2c0003040c00002c0203060000c2c46120f000307021089209020417413040c010310000301815203540e107082680701d0a4212110344150650100003441c800c900760006070440005a5008008101800c1e0342c1a24580480b402c003a0160010018400d400300200d8010038080404410049802100303000503009204600c04289411071005440781582410145070a100d0101410341e894504070288a40703d0b130711180072049460401d647c07142c1c00c03402c19904002208154070341e00c04500f0400402415503a005005030b0340100c0002035960307207400c900d90f07403071103890f0520740d150b03100800c20016141c80d03800070021010084c0c140c0e0304280035880c03620003804080e08484d01003900981c0a11070f03801e0030017040450b00440700017005864079110300b03952200307a4400051306891103000000c02c611092003c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 416643012 1250 416641762 416641777
    0x608061801031a06032b03061409010b160b0a091505040201020a06051512030403030806060f031906051906020c0f01080c090a030807050610061d0d05010b190f12031d030102 76
    0x242da000b01d103030100c111b0b030002110f0002440070030310345500460101020760010345a06d50103004060641d08003480034a042d0098000c0300c11071000d101814000072141c41e01c40380910b828074404075508560b4a07010140302c1c0c0a55229070110701e041c02b0003002d41e034001802c42c03501d070700517800081c991644070080d0004904aa04c0680103500b51a0452040000000800c2280e0181e40c40c52550303101c80040001a11a02c011010004818000b041d4481c4005410003644124004001074090781c3d48040341680d020028408041c55201100304400354040c4910401803c0c125000a0703483c4c5100d001038500c0c0009400c001c91407202040183d26600e0b583c1106014541040b51141c42d040c06141c601d5850008440120401c640d101c1b0008442d0b0154441c6c030000d44206070340c5052480c0c2e00c02400624500341c20140c54940d00c98903c00c03002c2e1a042e40c1104070301c1600c440250b0003810111116500a843e505c41501c0307910106c12140480c1d400000c1c0e20781c02c4e1300c08222034915540800007a001e4065800d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 416644262 1250 416643012 416643043
    0xa0b1810020325151503060c17041511041a0732070b040515070201090f080c040b120616091a250503041206060306060608061801031a0603 61
    0x400c1c1409080c4240030440451246441c2a100e80001c3c00740d04c140c44100031800110b03800d07403030148009802a004041c002c00c4503d81007403104080000030b01c5500c030540d42a80e202e038080d501c0c2c0c00c00301c030340703000382240034400c004814a03003403031f2103008031002c10303068007621040384003003032071410401c0c2c04070312000500501048603101c0c94920000380c1c141448140c0b10000e4420132800050902c1c1c5481641d04448009100d00404c071603440319000c6c1540003076000c9040029150010440401c02c4035440c01800e400c01c001c0c144021084180422209000e000a204006024120817140c030b00240d0b003a44807460800d114030b6288140026142c1e1190b0b500003404500301c01c008148003c0080000c0c0c0002504062070103035000290307800d000c0821031581c0c050560342041006209400c00c1080c1129028800c0038002212a540e80702c4004940080d00a9030000307100205010043c5004a4409035480030a501864254076558540c1d60303900800c480740f0000c11a5100007002c82d0b8051040940320700c0d401c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 416645512 1250 416644262 416644297
    0x150d0507050901020f070602070303200d090911030103021c02011b03080a0515011e090f0905010303081e040b0601050c0d02070512070e2a04090b0a0b18100203 70
    0x3820050a035800070380c845030041c03007071034402ca4802c3d200158a504030340c2d494014107c80c5055450480703685491000501401b50340110500407000100402c8a89450a581e6104840d0600b070074801612442d84014240b29018001480942d8903a0185202680302464192028500c4c1c80142d0b07151a9113004c400c0d54035030b00b8002c0710505401c000014030456420b45c0402c0541e444412604000d06115105130000b0340701200c803404030900000c0404080000e051241049640d0300824064142c10340144246603203c000400803d41c0015016401500107842d03090548800d030b4000c1084074005102a041200040101c0c5190340039404450b604400e02c016550401d80595001c0d56610a07489114024500640c046840342d8021440740c00745c603408200d031890354440d084640c0441c6000405440034545144905035011090303c000c10080c07141c0600420b0741c0824500700100c100c081e40c00030300e125808001d80300584546100e1100c2d130307240443e8108641003c0384412451402200c20b80084000c64 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 416646762 1250 416645512 416645521
    0xd060807030c031511030f150a0b0706181203091104020301090903020606030607230c061f080a0b06131103090307021e010918150608070f02011109150d05 68
    0xe01c002c202501c0c0201020254251001946811500350000840c941d00e400c3c40840d114080344824143c101d4003000b40d0241444d081d4000070000071059015035010f2900155a00c10041503001d4100403485601042c0500107031a10f0b40840401341a1a810406a0700c2c4541c46c00c00140080b4040c002e00301400440d01c03513840d4480c6500801c14001c2c10b5002d0b118040001c1c0003480e00240f982d02c02c031300b195103200000c030000c5060f0750300e0600440c4911001405012018842504002c042d1080305849509004503280060000f0b2144480d0014070450300080e1000001c01c0380c214909030003c0d402c0d00c40030080000c0d59401300c010700b010301161644e41000814401080700c008081e10035035000321091b080188500f0180805900c80401950200d15440000c02003c502030401d800b91400da080007040d03942c030089001c0d0309510030350002c9001c030b0741090030700c0050b65000e05084002c803c6030008000201248080000b40e0003005400341c4644010180d02400c2e4030400d0035100c1150301c2030402d0100b07051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 416648012 1250 416646762 416646773
    0xa02040b0306011d1b070f050c030d090b0a120f14090c0d1e06090c050a090501050f041d0a0614010b070b0c03180118110901030305271e031e060c0d06080703 69
    0xc0b5008d842038410382500083c20300c0d0214000078035800607200c0008061414122010340d4012124620038880e40c81c05122140000340524410520140c03000203217620803101404022802900072402c0713a0200d2081c500a03129850400500f503082580d4040b096030312616094012030072000100064244001c00041218100741801545c004450b24040d8607115a4140d003140c40902c1a00c0c3d10110b4440b480249041c95807110344004290035a08181001e4180700300d1130405508003c07144180d40c2d8620710468003844000601400c041c200d02807500929851f0030b9080300c006000000140000408565203d440c60900091000650000d001c44d2000000310345003c03010b6402564001200700e08a54240751140c02241a40e034182c503031a052225844072105004120195000c98810314544d80c0c203640d03194000701d5648102e08ea030340ca0288820009040c24603108001c108a0741c42840d074a0b86e1a1140070600c954008002c021103078503900743c80750860207020241e01820340703030080d60004400e000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 416649262 1250 416648012 416648033
    0x1003140a050d0509010c020409060b0a1e050105030702030a030c05040f030305030a05070512011a07060509010c0e040b100806190806070207060903030503040b06030c10020a02040b0306011d1b07 85
    0x240244161002080c20b494241c855100e91041c050000d0400100c078001481c1681c088107203a030140c100000c00c203806a0100c0d034401015003003071400c0e041d0080d10004c031018000b242e80c090142882c00c14110305050101940c1c07402104d00081c00d26458003c40c002551240c42514010100d13140000724a0340d681c1006452640290752440e0040e0401000440d4180101c0880b4200d040f510070190142c2c1ca0507440540d040047e001d8a600074008002100204501c0c0c001d071805401104000103006100501c09400340100701c1d1014003441c207060007040e180c1c1e12480c40d012100e5403800c00e9142543d44c00d001807882440441580328071070b031070705001c10150300018426200d4080344d0220781c42c007500c40300203450440c0c2510000300003c5c4100b00280004980c500c003581c200c0c00181c01c4400c0d0a28180000710b00d80c2084c006080180c1c0580c00c08425807505001e0351a22902c02e90242c141035050506a002520400301c04c204490b001c10089107400701038490040300032483e902544c1d143c0055142c1500d400b0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 416650512 1250 416649262 416649283
    0x5221a03030a0e0a0b07030f0f0201020f070b160e060a0c17131502070e0a09020102030903010f150b0f180111060c210f0106120f0f0608060108031e03100314 69
    0x21300c0c040c100030494901150443d03a0305900342d180c10300c0c3d501d04110102c458400c80c5102d401103540070b2140d1007070013903080f0280030708a108151002851800801004404000500e1281008120002c4a07010b48071082120307980c44151501204003811030a10b1017083c00c0d566005000620b0006d14040011402c0844c602524481c0000e00300040d40c0c2074049a0f07030212030244075140030160700416100700207680401c404610600544e820701d00403500280c2183c451040089030183c0710716440c011800c010234443c001d0980d810350141049115002841240941503c004003815580c021030170681c0540409804a51560202c030880d250424900e0388581000c46881a042070f0134030140c143c0440e0650781c41c4580810501460160329007401101c10920560107500c0043d602c1c0f901100041c07090103000c0312140c0d00c15002c600700b8540729280c1d1410105034422134954009010018894910285004250a400c10f45035102d840700d0030982003c1009520042030215103440078150008042911601d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 416651762 1250 416650512 416650519
    0x30b090d0804050304140d02121606110a02090709030b04050a03020607170f06040e010c23030403120519090515070305090a080d0b040203011d0105221a03030a0e 71
    0x1039024003006840ca1002501c0c000c2940e00184428001c149009114070710305d090041001d0480115500820714801e05002c81040315003105900481800150405100810142c034010076502d0503e030310540c6075040120000d00c10000000070075201407245150401440c4c101c035180c40d16091514140c0e98072900342c10300714090300801c400101c000d800750702c968024541000000d01a0399580e04145c2c138002004091540c456920880001c102809200d034500200f4240c40b01503d600096a54003170f04000c0c62500400500104100000a41d10282c0d0040a55054001003119210440300e59600242018a4480d00b4503107a03024052000020b6520801d0f200c3c54160702c1c29840700740c030803410f4440440b942ca01980c440c2d8071903000030744030700002c2140c4020300400050522417000020240da00030780c0807441411810010342d203c00b40c2ca5860354010202103a403914404035000217082d1010b915a407a0460661b41d030f000500c002e45034044144081801000da03581c0303501520700503000c1e01c1180c403618003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 416653012 1250 416651762 416651773
    0xc07121203051012140706030e060906160c03020f19110406050f0d0804090e030309070f06080402011d031f06090b0d080c0a0f0308040b060603240f0a030b09 69
    0x8441e000e403054500a200c564428040c013402c1c80e60380c4500f83d200300d5007280d4070340300060100c030011010f0002d180608829a40400c8140428003014a072610150a00189810510a00520300056400c5005082540c240850420360a0070140c0c1407001d48840306c200d1f4060f00c80a2904401881d40071119140300d01d0000211242000030f000440b030b00740c0038140e040014222507a20380d1400e90501541a84a51180c5141075151441c08080e2004c0c0803442486900200c14443d04070003d2000c200944596242b4002c9580b038640d004040d07000c0684040e05100644c2d415811b90032004020080790300303002e4103c2d007144842c14240c4910305411890490803519151022071009080e010300c000ea0a001800c10072620015201c0c2c40050340441100b83c00c500c918401207000400c074481400d14607001c0c2d201c801084c9043d04203451004402400c0034400d4000f04200800e1404803070148001041d2480390300750100152000c102784c1c2d806140c1030baa002031904400020480358403503080c4660409001cdc2c40c3e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 416654262 1250 416653012 416653043
    0x1b06021902030909060f0d06060909020102010e0d0206011e0e1302010201061205030f0f04180504020103061a0a120204050604080f0c01032705030f16030e060f040e0603030c0712 78
    0x2602d074050307500aa83d0244a40e00480c01c5440e003500d062880d400020401641211642e45000032920551702c41220292949100d01c00e560b028841d40d0071644d906c07805020003100002009440b58014004c1c1d40c5103104c98400e031b40c0c0103001400000e01810640b02121010b0800c0745070f9031500d03003002c1002ca0056007046400b0681204440c01c1c9124958010002c2d4100200035012582c242c20800c040b0000c0039041c400084c0c1c5101c4080508104038001c0e5002416040034000102a9800c0d6003207240d100d90541a0b00c25800002d01c11034182c814903262848c0c0c55814041c03008064411980096030000c0c02040109120a020070004560501801285c030350b03840b442d00540c1aa4014590045041a04c1150700754901d1141c0000c450140705509030313440c04000d1820030919405c5030400c070784410038490a80303040540000455200c0b0100700d80d59800c201e1a00744000303152055014043c030003441503000c14020748040058885001e0200c00756414243c49000ba10125440028246d036000e40040115 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 416655512 1250 416654262 416654267
    0x12030f0a020f13450e0a1a04030e06070807020f0d12020706031b0c150e070311030f0615041a0a09050906150303070609020d0b0108010f2412031b060219 67
    0x71802a80d50b022901e0190001e03e1000c0c001700b0f681c44000a07180103151501002501102543c5d8209071409040c03a045c0c02d00d4100106003030203250040c4e005c0c2100300003170000b15640405031a0071507412034070085004070703503804503103040b0f0f0f00070b002408a40c0740e4004182c01a0003180140681e501903401f080700a00d110b060030b0350b4082e1204002c1c0031842c0061480c02084008048865640740880c01007514101100717a5071801426600588051940c1500360490340303814032181c0c141c0d40380d4400070881403c00e0048808042c0c0e401c80d1040c0700390303034070703140614481d094609010080d000208400086666881c02001030102212102e08601500e07001a2001d08604d240c0b1420f120090000c6050241d256142e5005140a00050364401406203003130300003400c00074010b4041d1520748004501c40381888844001d41e01d600300054650201c401c0e4039103140c03007540041000ca50104444240368400c9080030707200140f00d42202c00c80445101f4140040c8a025002004030340070310310b2200c40f80f442e01c0404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 416656762 1250 416655512 416655599
    0x5030d020721030c0c08010606090501020c18060415090c1704120f0e0603250509010507060218180714040510030b010e0a0603090512030f0a020f13 65
    0x1c420162800c602000c0d9041000e8800b00882e6119051031002d00c49181c5850860301c203558051403042e9140e15050003010360068140d4020b100a00041c880314a2031000901901115288200d0102020b00060f4055407560030078800f0720385e440720641700355807202c45400c0034000030300300c1e03001040280022843c14112a107907107201c0c0703030002130080004d403100c00c0458010300d02c00c00c0c86040100b0400b40c00315581e5514020343c010300c43e4501c034a8503c54040c00b0000c00c000142064002e00c0424000040310ba600141125034499001400580e501300d0784e99407086100900c0100c9410401c0415403002881d000107101c1d002e44165182c2800f603211a108150680c0b189009030360f000103d02c8408100940070390010148840141090781903034080314003292104038140c0c0000000f0361100c245500780301003840706000c041e00d50321801d4950700e0007059000e8105806010301803040d50010310072030300e8990503041ea46e403500484c3c0240e09041d594440d201852810960151800c0d18031012146800781c0d0908 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 416658012 1250 416656762 416656769
    0x110403020108070e03012309120c0c150c010606110111030103110907020106150504140a0602030f0310050613090c020105310203070e1f03030c060903111605030d0207 73
    0x5030401d4640c3d5a00c000c41d941940811525059900c0e00040703000202c115250301040754220020180c00e10b812840545083ca20070000403410800700324482030203401040c5c00090310400d849003884410000050040c91080b07151ba0501540707004000300341144c1c4021084a8207000e4ac000740004041c1c0400380e88184800c1c800106441e510b04ea0381e42c02d0b03090451086602000900001070110f0369402d11510800d100d00b0207800140c0005000e00442071110540484100c1c141c80d0325000c2d82c01c0c8440a941ca105040c078843d9a007078040001a00310081c04030501c00b40102500407034542591050040481003580104081d15003010001d02d10700744140700c0c0350300c50a440f1f0013241d10301c800c1140007690091500100520340c8038181c000b03005030300c0030020340004140180205203a8a040800108000185c1c2081d03264507e045204002185e845002468800c7d0020700004803044145026030341241d07080400c5030030f40504004140740c40140142c540071a0803d80a0300c0b201c4138803800498840b42c203400b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 416659262 1250 416658012 416658017
    0xb130203011809210503090f070311091f06021b03060708010311060403081206041104080a0303270309031b0b03010b09030102120a05040c0b0309100915020408010209041104030201 79
    0x100b205250382200e4001e680042e0007542c600200283d12200c2600f4151030039941c1003c617400000380a40350b0020824144000c0300d000213050050300359958000103460f110748151040a1010111b8044103100740203100060a85901218950740c0d00400f81d195042c1e80c280400c0c81e1100c076503401d10740c2070218010f840f609050391a03802503030071551481d6090281c801d110303800c070700184800300c00030720500001d0115440c01c142c0300b005460309008100a40360420025039030035070184000c1000c02e00014458180a41c94200031400f07280c0b400c0c190420301c2c07aa101440038040000034281c02d00d5000385005042d80d020305101d00380c2c80080100e010100c11141700309942040b0420041042844041c05000a1000200054903195042c4240c0c041107000780d40706415155954140020428116890030007041d69079003890440c542501000d0b116082183d0309130141341c880340303144100030752400e03030050680140404548854a502c4020b000f50003461003107004510b0140070300d80c02d0380e01031300383c07012030360305030f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 416660512 1250 416659262 416659289
    0xf01091409061b0405100905030705040603050d0c1a1f0503030316050903070e04150b01030908070b040512190912050a02061305060d0e2401060e010c05100b13020301 73
    0x1020380c2c03e10641490800c054160301440081010343e0703046219194a105550341c500d105040801301401c1607450340c80315200303500c0c0c01410000030700b01003a02c58030600c141c10b1000030002c01d802d02c0e90f070040704803070300c0c5032070740010003c002d101c4000c209150304810031208482681a00c450906559110a481c02e0b00031000d15030038159114402d034000c10000d0000b80c1696581a580c0070780061840302580c045030404541d030203007021440303244900d00d0480024038060015524a8546401610548002070154013100700040c09004e010400041224880940983e42d54008017820601c80c00e3343d500324001540446001500344415400e0b0144507400a018000c0340c0d0303140e8200122980301021001e0125600a4000340c20381e80e0030090a502c1881540104e6144040d00c030b581c0c01c0c40055803200b02c21070f00411041c81c2c13402d500d5101c00c2c191191800d04a2202c1c01d170f800180c40e4003500000080540c030440700d048000d400c2c0c60300400c07000107007510140c00700c181c00b04050090b4003003406100024202d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 416661762 1250 416660512 416660521
    0xa080304052e0e07050904060e1507090e0702010b101107060e03060a0b12031606060603020c0d0305180a050a020109050904050309061812010506010801050402040807180b090f0109140906 82
    0xb07540900c2001d03014500b12201c2554032408035900d6141100d003960320b02e50710440c580b085c4c001404040c01301030404c8822400ea06d80900c000c0c0030003066001c1c05015000782d00000701142c3c002d51221561000c0102100310383c00201c00003c2c5035880c40b070b56403d540d006401000410710300804442031022401006400d5542d1180518002403c2c5005c2850307025140904284894000b8802003100d40c401d50300001c6940351a081070310581c2ca095000c0c0e4101403040005a60480340421000c02e0200351386000b0806880b08151001d08030f0510240d10454010505c11400304040003490029180c0700382c80b048491a502c0d002c00c40713039400071a000381954000704940c2e0040c2c07802200900b584d0440c942011840100c150108052600014119000d69500d05c1403041642c2c021650b0740c0180707000c072415841c1604000129840d11154800d0034108002d2007080511040e1641100303404000c0507105444601d040e405401000500f031003001d544030b1400550a8000c803c2c0b0070401c0c49103801c0f1005201c90307242c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 416663012 1250 416661762 416661853
    0x2130906171506240409060f120f060f1103010806130c120f0b011514090109120602090402070f030327030e0a09021b0f070f1e080a08030405 62
    0x4010072180d4807402400810b0303030701c81c01103003480c812580400700203860b50b0901c01b680040365081e41240c4c40c0d44403c080c04100701411039547c14003490303101d454012040700b41c1c40e0103400f0f07100510403444020705000f001c00342001404003850481c3c942da01124015290407000046280b040703d409043c4040c80a41409011502620164014410007907120803003c035490b078000440080e0040c890601c1c0c00800100002d921201e1030040740c0792414071504d040d0381c10002030701c00e088a10582d4441d14202034914140903c507070540d0400440900150344d9040ca6103021403000c0c1e0180800c0700420318140c41000b1080440070031520810b000d070005507200304075481c2668982d000300b124a40c8001ca014011414084c94005880f0f0240302264072a0403a05076600103080c681c0c1d408610303100713502c003610802140d0a2500c2040441700009103c04003110100035002010b031613500401c2840c0715038200c000c104202030307000b5171003140200c003501d0705d48614400d107802c0c0740d805002c240701d045190400d802c1c44a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 416664262 1250 416663012 416663053
    0x204060e070507080c070510051207141b01110a0207060f08090304050d051e0d02121c0c090b0a0804150b030a02060d0905121306142208010213090617 66
    0xb42d000c00311b410302e507511400100880e08a01904001600c041502d0204e030503c005100c0d00030926040041010030000c96001841c002c44c110300c240600d080c000c0040340350084d4044400440c11908a5a80d0b141c00f05000e5a1100c051044400041180004580c028410340115008910081c051440c0516040030000c035800c0055007a02c42c1e0007000c9502000c0d84011503040050003111002e02520100444041d06040c1c12041010000000f003014102001440034030010304400e040d00054003020064040f1400c28851f000440b2488001a4501040e90480381c050704c00d521846015440e0b064240e112019504d1032800d4a806030b1210b0307003500041c031700240602100f01c419640020644080c0c2c94481c41d020221200146200b000140c0d0444c0c840014400d1020f45498100005581070304146409507109415019520031074440c0b0b400806903221824000404900c0000e54840030000b58001080500e84a03240c40c4030300d001800070708030002c0c2401d0810440048003510000c2000300711090000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 416665512 1250 416664262 416664277
    0x604111c020f15070f050706030902030717030c070b09042018152d0306090c0a05040e070305061206010513051e0702030d0b0d080a0c03021e01090204060e07050708 72
    0x3e9040c00c40050b90702c103000f90241d00e00070041c0081086240c1801400d00e0040d0300160b0030182001084005070b1400600e04049912410812000c040002c007a541540540e0385c0e04c4110f0301030a10000f600045c81005407400e01000c440801080900035049040044101603244110000303110300c406001c0c025981030b1121201900d228030306010300142c00d503031f50b0228010030750310340045849001d006a01c14520031500720f415141c81c51424200c1c00560805401007030f07983c809000140d100d00051003031091318000c120703c000d0030515080c000c42c06800360800701c1d28180640704c00c10381c007100075500107a01c604845011340480038030b00390300e002d280107001300030090a40f81000711aa071703540d102561a50351190002c0d0f400346481d940001054030666003090612842040400583c202164103482129180d480c05c0c1442c3c404003c00e4902603080a1980300488089032032031003001100c00064000c060541d10854041000e02d07180e9031411145102034076600d000030428014000090101401003400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 416666762 1250 416665512 416665519
    0xe031914010f0c030c0201180b0f040f08070c0503190b060d0501020c0d090608011715041509081905031303030e070b03040c0929060d15080604111c020f 67
    0x9905081071160300382c3d0102000b0b0320009680d01480c0e02c24a0382031041d207118000c015580c400040a60320b0340d1b800301038040d04480510b0884400b05040005094902c01080e50104c00283c490b6924200906c80750403d10680b8028050300d584031004d00140c05120390320a6000d800c0e0307811511792a00703106020720000c000b00d078250360800600e00d156404000c1c40352400c0450307848490f05070800c08000e1409030182c0c041e100400d0041407000804501003421004600301c942d200090b5500e0341041294460200c0c1d030605810300d00010601030008020060180516065608409028061041302c1610085401c00ca080e903400001900191180d0407115180c803803041118074007078503043d4400085d8020340e802c070390080402c0d0040115610368020602601306145040040142c00301c0702e6810030140d13040640c4207200015040110210f680d00a000b4104e41c030000c100300545038081c040d9034402c1605e003a18078854040b20100d42d1f14001c03844e40d2a6240ca02d0800d10643c1d181c0d401d00c40d401000c420304d580d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 416668012 1250 416666762 416666771
    0xa1b1406180613200d110f010f0507020607081b0105040501110a080117030f03070c02191206050421020f16060c030c06060e130215090a030807020402070204090308070e03191401 78
    0x245542c940801d104054042e94034503486e50f6415081180340103d803002d0382e041c088101c0303100c60b0f05a009815211a01e1f010386161340d07112150b1914410303d11072155801c482c0007400225003c40801540964400c1d807041c0001c00c10307550344090740c82d418011a1402e000241081e001440403100120000d045800e0240849041000001c180b42c40c941013110360400052006170884207529009c1091190302d0500c180d48001e241c181611110b50081c61740b000307841e035629500443c0400c4905511020114000000080724000c0f49c0f1001b516040d9034003460f5440c0c0302d0700076102203c06040038114120380301d0752030790703210100c2542c2c3c00c0d5102c3c4000c0b46d0641e0140c0c0d68020008004580c400c104d07104009280c0c0d03d042c1c20213a80304000103032031100c40c180c8408c0001c0c4070303041c4151a03400e2000250303508a9512500c0c1d00c520320000d0080e01c141c0c48002d400c1070038100f00004060704620140d010750b000340c5130241c0c54880d282c20715a49100e94139403803c15500c00e4400e40042600c5082681021015800114 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 416669262 1250 416668012 416668073
    0x604050d08160609030f080f250c140304050f040209030d0c05010204030507030b1603112a070e060a080f1009021807050d0b010203030103080a1b1406180613 69
    0x100f112100142034001c1b80000110400301ca070300003e001c0e0301620840c0c002d01c1c1d60401508029800c81c1c20000314081a000000d11500140551841d005241d800564110000280c5210944a800c82d2140b00c0c020b05201102529a2605000392888440301500914039004070350422940140000ea00f510745550070000070000c00c6052000a001e58000c40520017142440211030355064035414080c010103203411605c24280410400700d814a80c500100368038003800c0c101100d0034080886e40300c40618811080700040a04070140928030a104c110740004d031280c0e44007103854490220040302030444d004400400100348403a4030140c0501e0000c0c1100c0343c818400f0000c2c0300d0346982521300d2030101e24049080d0104404500558282107400c1c805142994955960b004241c080c10380035074280100404843e40b0b41ca407185400790501d0300902c00480c02c0880d4000141c85420984502800d040fa860809140000014550340609180700843c1c000036019190425152100940c0c2d4a1140017a400e04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 416670512 1250 416669262 416669273
    0x30c060307140f0703030203060909030910210f0603060b010f090e0a09080c010f050108010b0d2307030c0e060103141302030c1002061f031505090304030c080a0c050604050d0816 78
    0x5013800780c400d880041e0741e418000c081221000d00104504c40f20380c002c212422031519180980c034551001c3e03050150800c411800400c0001198001c03642d511403070000004540241904101c0860b03020750f008119844100d0011140812940e01b01808101c43d13440400001440c0d0031002d9106140c14400a080203142e40d1304500c031b0f404401c8514407030307444850803c42102d0b40e1040900500301c0c08000c211071012103010407442c10443c940075000c484101140440c114000d07044456440c145825038150b55220700d0600b0000d44140504100d103a00345000034401e5000384901c5450070b4001041d14080d176038101c1c0d1003000a4070010700700d800d40254240c45005482c0c00030040200441600a0142071030003c0203502000e12500d07407581c5103881060100045480240c0301c100c0c80402043c00b04241da241e001c1945940f02e00d5100808141c090040011491008070703001c4006032160701d07200071503550749041002c81d0003180602d40d40300300781088100020f01c450004044441c061112030744090304075100d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 416671762 1250 416670512 416670517
    0x2c0a1103030f041514040e04060e0318040b0301090204151706010e061c02040f0f14010b090d0314070b0f070206011a070203100e0706020f010c120b030a0c0320030c060307140f 77
    0x1aa07c03504032681408100085c9000380036620304100c005608091101c01006950b50498001c0c600a80d41d0384440d80842c1c5084d0002d4402e60f8028000703202880c01d8102c0a18481641e01c6940402d5001d003070694400b640208085040f201840da0740c080540751071041100c0680d45030310340c2d144010742ea0344000040e2514010742c46444002d60b8000f508441c500300b0201503504010744c1e0754040c0a00780c0144900c03500041541c082c40b0091701e00d058000714528064a60000d0760000040340320012400300100201d001c00c4074407410704080401016154510305a0b500c210a0046808407040e0311075040c5400c0c516030162800a00007001c50b140c51555031142021506501c80c2031865420414040c0511501040304505c01c0c2da40c1c000810005070400300040c03500c40b01c09442c081e042c5c0c440c88043c00b02c0ea400c00003429060f1700310820340100c99a0780b03000700c499150701108000000c1c9004540c0c0b194580070842e920080406403000746142d42d000c00c1141c103045421404040d0110601c003081e13005010002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 416673012 1250 416671762 416671769
    0xa09030e2e021605151e07210f081b0315041505030106150503220204020c0d03051b0f0306010c080406080f15132c0a1103030f04151404 60
    0x14081c5110443d0b240115401240c0001d8000c0d9804032410102d09148421034454400c840322034100d58200702c0042c0b00a120b0840301900b1000d0b400701c5480b60542e41d481011440e601074442003c0c2003000345060354412402c03107404032400700031144441129202002141d00c0f500e1000c1d01881152013900280440d90044140d80b80e01d080a50144050b00b0300344240c1c40a01541039500c001c6000d106002012840300038450403107001309074060343c081e002210995051079401001503440d16000240d00f5580d0070340d48520340000e0b003400003007032481284500c145040c51942d12030b0752a2103440d030380c4924541e001a03c964100f14501c04c0d02e0700410f00c260098400350606035031300c02c4d16081007049038140000183c0742440c9041c200300c1c21a0680c0c1c031400780500031041c01d20085945040344404043e0410140c0e50b0030000c1e51076003100b2020307401c003140c2101c120780700b010001ca0311200e0206141d07513405203001ca0075241500300021701c003004007028000280c2030719150650241c8045035400889800c0b90b403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 416674262 1250 416673012 416673017
    0x90a030308010510020f070b0d0b0618150a0507030c110a1e1e180f0e0102070201260403140c030703050a110f03180f0d0c08060a09030e2e 61
    0x200180014a01825502c20040e40d078801041c0f10100315026035107e030a2480383d4007428500040c0300342c00295640140c0a2980003e2029880303142c00d40d12041182c0e15801e2040c49600c0e00c0170140068440c005c240c4002801590310030f4140031780e40e9400d84141c1542003095a40069005115410341d590352540320107070a214a03181c0f010550a44804015041038120403501d480540c03404006c1280709140c00111904102c40b448000444020f6000034840700000b88080e40c1401000c05030444150010a81d040c0f003a61090059400480040c0d4018100c9038541d600c606554042000300703100381c60f840c1403602e04425042c54110074425003465680404400c0340450804249070f00b6040d00049002a00c103c0000909482001c3c0d08070300b6103921642c4000f40120000400701890b5403604003444c070b14445e000e81241581c403080c2c00d140000c09103034481c4161612440700001d2000302507004a010f03069142e25200f140e0b040c02ca080040642651895070015400428503000d200b560b140070801d14669178 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 416675512 1250 416674262 416674277
    0x405010b0a02100c0509011d031b010207050109050f09100902031014010206040309090e120c011b05070b2206180201020609010917030c04170d1d0904031103090a0303 73
    0x800c0040e0401c3c1190074000305072803600f0741e65014160031404581001000b480d03d5480340a6107038130100b6264107441d00b113826204040003800c1800b4202140104500309800300c41d0755541e0350004440e03130b0721940101e1350030110b2500005a5820844406900041003452140d595901c8401000407a00100d0704250210305184041040d10b40d48010960629001c0c809032200d490652406404d40c8101c0c804e41000540d202c4441c01d031901d040c8102082c1c1c07002010515503ca65888140b40640b00c83c0501910340c0d10266a5034101c580904221404698804500000c80d546d80340d100084514041c0e40e0722451070440038010000d5900c2c0700e11490b00482c41c0040c941c03908140002071800c0d10041070051a43c1c540800c20307002c1007560305414107030581404096981d5650f10a803400d1400340344d00070741c0311406003c044820f0b054081900700380b0307540a9881c02c0003403003000c03543d80101014010040c4c100200c03502007000300e4032440b48110003001401c01c03039150001c0040443c004002544c4181d0008892 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 416676762 1250 416675512 416675527
    0x60e0a020d06050129090d061104080601152c04150b030702060a0c200f0102070302030d0506010f09210c060f0305100e19061d1e090705040207110405010b 68
    0x10840c3c0e01c0c04600080b07036062851800d200580e141b88148072540d481082030b0b0808804202071504542c04044084005e207440c0c654130f00303140e07540b40801c0c020b25030200b40c650f101c2038105220300c400100c080071801032036840c8100e140d4441449080b00400030b03000b580b1101c0c00000fa2024507074040040a2800304580c2d0707031814040c0281402c078040c018030720840c281000440c02550101c00c8291550341008030204000100c182075140c01948407001150354004a00303407081c56008009000c3d2082c11b00e006128981e035110044964087c82e040d5440450300b40102440400200d010591440300c41d44c2e4402820039494940c41c0b280b00080d0f03c84400540884040d81005505004003500000c3c440b001c2c11300181040450000b03240000c0641040b40f13440140040042e5160300500003c2100900c0224801820030010b80c00c43e008a614500c2c010440741400080313681000151f00c29080d40d0702405045080a00b048080d50080c10113640010403083c400326941d0326031182c607000b0003009030940e80d01c0c01b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 416678012 1250 416676762 416676779
    0xc070303050706140601120b010e030a12140c060a0b030f10021c0b0d03080c0d09031812030e06030603010f020c0a03081e0105010c031b03021f0c0903060e0a020d060501 74
    0x2401180300c91380010345014407400703076080789104000d400400c0002c00c1038880400100c1d60818060800c503858812204000244007100c1d0710b0380c0c5c1000c3c0ca90f4070340c5a5400c0300e500c0174003107100303410f640d080d5948003200044690925034010313074481c04010155002e000a01d88068904440204c240d40620780c00600e45540c92840c4242c0310146400384400d100b1125114000f0300580740184025050111384000518010104003c40c0c270444031150b000c10681d0542d047c0140f032080306044409008140c041d0201d020b0724624500070700c1682c150b441e200c00c0d01d8500c0a0001d035400140c12103805640b140c7c80d50103542840d001030218a05404018415210301f4100207100a00c094031901c80244407640d10710114511034001c50550b5000c3c00c00406500c960301e004c81c0c1c01d07007024180031440d180010322401059400700c0c07070f040400f4600480c00101009100c441084407850001c03c0c006ca025100100006002500440320b0030001d4000e880c890071194010402041840390100c4210343c1d180014010400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 416679262 1250 416678012 416678021
    0x40f14060a0513080715090f0f03030f020c062a0406050903060a09020d0b13080d020711040b100e0a091407030f0504020105031522020d060e09120703050c070303050706 74
    0x3c000a400308212075403911440500e101d141c9010f4018010103904140040d50f5402c040c54036648040c448507100a50b041c542c030000c0c0240350403000070b401c24164014100b40f50007030300c2c85d0a40c141c010f401c203601d030301507504038020180400d15603161002d10070140c46e01d240c0c0d026000504407030300c900d030340da0010208050400c0c40041c00400c0035440e280d0309602580394004c0302036541da804400303501e55440780c0504080f02c00c000c2000920080001400342040721942d006454810310814a0002e044408001c00040c0c41d00c3c082c038281c002e00d1b80c0f027140703901c0c900c28000304d4140900605000702c42d44d140c083e070301c00346d5a40805211504940c841030201171b550612400c0e044070b0100c98204154200380e40002c2c203512001c2d00b80c101040c28061038041e90355962228403070f1074601109802c01655492191006500440410025a8607282e0000b03402c0349005000e80c402d03011031020741b06d00303d210b900391389a94214640c150b003000707018810441260000c0100c0d0b000f8600035180d0340d40301c0c4c1079881c1081c02d44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 416680512 1250 416679262 416679271
    0x409151a070c120515150406030c0501080703050c09060d18050a02030715020c0103020d1407031e180f1a011229012106060f0801060b040e06010503040f14060a05 71
    0x18141c003900f800c0821800306004440c03007010290344c1220703210400120807100901460942c004d281c104004104100300003407004860f0203880d2600745a89540c4150111401115001004c81e41007294140900d8100c00420b05c00549410000b18a480d8038018803030202a20400c1b0b6050380841d0883e000c0d8582044110b00900c014150640106d41000c00252541c0c0c070f0455440c14143c0108003513840a2960b0061a00d105051103098410319200d50010098070410004645035a080c141029504000b8010b022083d10241504500c2c080c1c240da48260002d500001660051110300c42d06044049013401c4900034861420407040c10040390a00c800003400041d51000c0400300c814101c0b008144080005045910b4180820081d040d2000d00140c442003070fa4001304410f1a010002c9520a051980b1105642030b04008202090b142c0301d02404510039030092405000e080000230388150710600c01141d1044c403908090505980b2955020310700d028600e41d02c400c6421003410484555000d202c0c65611 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 416681762 1250 416680512 416680529
    0x504030821240103050601050409051e0a020a0c0b06180a140606030708040b19020f07050c0a050d0623010308031819032f07030303050a110409151a070c 67
    0xb40c0341080901074002c00094040d0381815202c000199440c0c0c092030684004104140e4103000714036089070000f15401c0c04200700c05054451a01003480d0505a00c280c52403002d00e0b444482c01074880d80c807403044402008040b80d60010414000203844525003024074010051107202040c2884149160740e000310303000308102e000300424010005545e50040615400c55000380c081e40740c68032050140010851400b5600d01414000211200b00300000e01c0100300c0c0390b00501c10703112940542010407400c182d4034401c080d4820100059540416450744c014100e0218000c0e8a541c1c0701c4204400e9000d11100340d100740c800c02004020081d006d40c80d08e40e140c2102100c040580117840b014a0381c04d290028003d0042c080013810808603201d40c80038180e804160301100c1e003e010520484e40d03101d95500b03a9001c1100003d0600303010401c03441e41e5000305c0301035125080c01581014181042d550040c42041000e90600c0508178002071070144510580401018151030b444c0c0d14402070030a26500000c90b40920003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 416683012 1250 416681762 416681791
    0x90c0503040c0b03040f020a2312070e0705040819020f1206010911040f030506041a0105090c250b1503030c030a050702120601120b010b0a0914010504030821 69
    0x3040406603900396a000c6401c3d50b00c03503c40e4240700e010006a240002d40140540c10080b80c0108890854600020070f0720b01c04803600d803e030062011001500890f001c003513001500c00d12115107100d10349039000a00340390041c02c083e41d906480b45801d4600b014084420107018200301542040f5584598818098a885003140c043d601c0081d43c40e00144900c1c5400d40c0d1312040c282c0c80c4075080040f00c004000a4100d0841e003510380c105a511000c0503501291102c01421030f90b81d100c80d128205a048804c0104801d5850340c400101441951120b55682a4198100c1d05920441c180c03a020340c400c207004420400c0c0a01e00100e00341450581c1c0040c15201e640b00f0b2200610f50352002048441e46216864030903100c54640c801320303103800c05038000030483c1e00401c000400c48403400c41310407240d503000d900d8202c41640c1c0c400161142d440381c900c0c0440042ca2481c4c0038000010341103c44009034806140140c905596030711800c0c03040e00403504c407180c00070303101581c8008600242d9220b5089507038100c0b20354 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 416684262 1250 416683012 416683021
    0x1030b0703180c05100e03011505040e060103030e06031009050a1d030c060615040f03140d0c02060703030c05040801091b0f0609090f1103090609070f060504061202040f0f090c0503 79
    0x30150241c3d4400c81e803042d030803030404200e04e500c02c50380900b404801078021300c18580004400000c840742030040c1d40c0a81d25000005041000c00101d05d070490344c01d40c450040d410b134001c00f40300326030748014241031140181000001c1d104000740f18092040500040020341d20217082c96404030441c0e410712000c01ca51080c0032a8520550206500340c01000031200341003183c00f41420300c1c0b240c2c0039a501c428024142c0407800428001d00c0300c0040c81c003248210070745207080314204040d18482c0c1c0c044d0020390031a0040c024040003c1c000c0d031000b5809805814840d0509581c1d00456003900d41038941140c2c050940c06c0385000d40c400b204410406000000303040302c882402c2040007024103003944a1150201d494030b821800b035446a50100c4014075091003001c1d52480c20f0504c0d0b80d95a00156142c0109201380100060489201c98011041d00c2c0b140c1c1e109843d00e86802c80440316000c5240041d11066400c000008031000040901c1d0010725044400e01e041910b0030001104031010030200d1001d0210400410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 416685512 1250 416684262 416684273
    0x7020a0309051504060c05100c08040b010815040201030209040e1209120c060a0c080909011d060f010806011107051804200f06070336050d0f030806030a0b01030b070318 74
    0x4c0d0203071906440e100d00d40c00a1411310b5440c0c00e005040303c40c000b0740340c40900c3e030030310703030f114042e248514083e116481a80c0d83e20401a980d601038510f103044241a4100410010b600c04d030000c08000000070b00105622003400d0300320741807174200310b0080c0b0210000909040039040047e9040d204148a00203000000d2685002c610248140500c082c1007084403080c3c00100008a002d442c84184054035615066031035095808111461403203010050900000017401854041c41411303050b001a56050f0030358443c0c00040d50711041d10070a03214507011314a8081600d0b1102034003401814001503604120f82010b040010010400d001460070b42e209031646000f00f9101c0c003803a4448204151000d595031607031810102e8954030100c5207085000781d244580303002d5000d03035800c1c22031415032003807510380090303642d001c0090b160703c8400021301380c8000180c0840400d001b029030a510440107003c4e104d041e01d10359103a26150000f60012244041080140501140d26104017a842100e5020b1240c2e43c504a4035070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 416686762 1250 416685512 416685517
    0xf010501050306031005070302032e0314070911031806040305030408071103010c0905010f0203250c080a0302070e010e010821040902040b04050f040b060f07051507020a03090515 78
    0xa06050040020200b01e07591001c10039000ca02c0c07100031007040039040400c1c000b0b0280d4002d9071140ba41804126284c0414081c00e4090503500c00351030107000308540b450340c88150070035000d044210f4074040c0074400a00d105d104d008070145c5202c05440c591b60792030010780341d0b131b034200c0108140c0c01c4c0e940c0480100800240c105040780e8000707422004003519103903946040e90560303e415822981550070320080402e66500501420b01b900d074240c07a0700038050700700241281c0da40280c01c4c0101d00d882034002800b00500c0030740007900c1143d00440c695141c09443d80f0f040c501c0c184d40b8407411801603215010402100c04403610150140c8603010381c4510300d52402c1581030b40c03001482c200381a5202d04901d02c10940c141d41046030b008010312035065407510764440800702660800e210b1706000c1e03d40c0150080c6240b6051142c0f50701c07810020182400c0c00d90016800c581e07a000503c08680f5481040320405034000b0740c90900e03100300b0700c0b80e00509040700c9070f1034000c080840030f9000038011900441d0303e80c205c6410f48203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 416688012 1250 416686762 416686769
    0x5040e07051e0402070204230c030705180d0519060b1503040308070207080d200705010c1407030b1303030b010e0a090b0120030a08090705060403110f131e050f01 71
    0x140040311624000f500074814504000d41c0980344c201c03840f50745489000560b540e01a1940300300001e6690030359815885c17004444c0403000031800c10100c602400c05d0905a820b10801400d50003400003569252454110400544803a03640c202030107038100900d5014002d00080181c1c0c4040c000f140510308000c6600010340010300303110040c4c0000700114400c004182c01020382c1d40c04c590b5605c01020000c0c03ca61010507014902c1600d1041c0c0c0e8080c800d00007401c408540e03040c4c0d685032035240c1d541c031212075404081c451000c5a00401d1000004503c001c0324090041102c0d0955401114007440c4c0502114406201c184c18490215225000c0d95140032515003222038030b4502142c14041540121145215103004402d40400d043d8501c10f54000000546003400705070311005031548a116a556071218540702c2e0940c4007104003c00c2c40040c001007800101c244c005000a010741d540c80e070025800f5a02510804441e0b80c0d50074444c0040c0700e010150b10041000c0e403d00b0042030030110103030f8603040780500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 416689262 1250 416688012 416688049
    0x90607060911100f0e1e040e10090318080114061201091719050c060408161416170c040b15071202061602031602010e03030d0605040e0705 61
    0x20a1902445100000c40300002d00040a0790500342020f40c000e0311800ba02c1c510b0800243d030f41160903040d03041c00c0c07290780e25041d20103440702c0302d8103600002c01000c0d15071001d6001107070180d4030300308038550707201c0c001d04413080d1003610740d900d0b00d81002010640601d81ca50004c1c1050303040500c02d400f01c05407122010f420201c10b070741c10041d042170704c0c03a49405410181c5000b010f200240703d68000704141c0001401041c600d400620034422000c0c40200d8a900031411300f05482d812036030200d030009a10340000c11740810500380c8608000d42544a403405042140101c00c455001214220307540000740c4040d034040c060b52800c2c009041c40009026941f00316105496004941d1000c2e14465030b40c0e82d03110400030b0200c4a000300e58503c100d280041141c50080175030405071098401046112544548107501c0040650080d820100c2003810708034041079031041641400101103501210751014002440c00c1240542c1c0800c006150000340000c5135030701d140da800c1503086204140f0841d81e50030010342d110715105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 416690512 1250 416689262 416689271
    0x1180b011818032312061320071b0801022a030901081f080d12330512070503070518010608100807060804030f020105070e0d050708030d09020a0b09060706 68
    0x70b00303a07080c030880d0200420011460100d4178450402510708410310030042582d4031440308000080342410784a00d050303220380304ca0701d6070100c034081c1c0360940c080c00005002c2c181c8180318222511206808070b11a810006080c1d400182d50940070f00d500c0303d42c220000c01c0040c50080d140c14002c04030340703d010b00c18015042005500120b04892410300724590300c41100c54607840340c1075480088030385d1031160402d114041203414443c0c03600030321244110b07503c011404400030258a18541c01040c0c000702d0624400c103004403407501250b00e444500301103030b1503e00300c001800580c0c144000c2624100040e80010302c20030412800c2000c40c1801261181100d50700e0801c090140c45010b8a801c10314540d0308040001e100b209800aa0315a0080d0002d004502a84400380c5900400000300d081c0e94007182c0c0034020500c2904498514200f403003404104038080c009a50b031542d143d1920b541554070505803502102d4540c0030a50951400702c1d201801044250241c0c3d207000c681f60041380c20380c003c0d5a0f018246030b0740e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 416691762 1250 416690512 416690537
    0x180f0c010f02030d050c12070509010c020d032706090f050d120908010c0206040201090e090d140c06010f080d05040602060c0d022110090e0a1401180b01181803 70
    0x3c0099480000c54034405112610300401800d80903000302034445d00301d00e5130b0000f1821060040b0103d541201c01a91080483c0525800340104040d562904808004143d01c45018003a01e100c28158032a200c80c062080b0a45041e034002c3c03c02c4001d030032154a07030403800000c0100b5500c4548040c40182e2141a1984280d1481c1e0140c65413581984032120329401c10300d80b800c0c4241e0114009204610036260000c0d60340d00c51010900c0d4041c12a509407140d8801210071110a0081f0882001e51440901c1c1500d0060386801441c2404001c0c1c2c840003180c441000140600141404941030028031031604906007468018000c0d612080030704601d030150b40010b205004440c00b03804541d80d548042d8603010542d01d81d45c592404025045900c10980020b400003c103130940140a0206018091001082e40d0312451319403841c40d1341c80b24503040e0b0540d42c80402d20945c04280301c0766680da80c004d454010071589803620300d039185c41c0c9071b0018003280d0f4641409078880c00d401602c152090358061414851600340e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 416693012 1250 416691762 416691767
    0xc0f05090a0b010e13020a030c05070302031b25030c0504090b070c050a12020d08100b09011d0405040305040e090d1b020406030c2309090a020108250305180f0c010f 72
    0x1148131041d000700c2018418100c003c42c2e0b0300240020f0815a42c1040320040400c5c4c1141d0740d006101e00280113030010030010a5074046598002e02c144145410759012001071502c10100c0d465150901d5081040047e0030410f20001a1560001f4030083d5418003002c00b103980e945021060003007580c028044980d4500c0f052213404c0101e00c1c841d0b6403141c040003031042d0b042c0010790b440b0170024240b0006004080000d41405600300d41c1022540c00e128568141135102c40107484203400c0305c1e400c0220554840104480703540314042d907405240280c6400e960350781080c060401210000304185080e40c0443c07a1280b4007a8465184908645154850070440d10706200080190400354000b41c0030710306420000c20003e1120f640507038150018400307018910796500600c00d4a200446401009420200401e4055409080b819511580c41400340040c0000c009004401e4950392000c1c0d00000da541082103051801c41e100d10075254901c4000740201090003207015aa142c400401504200104400911450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 416694262 1250 416693012 416693027
    0x50301151106150f030a030801140d05011521050303040f0f050f0d0f020708031213060903080708060d0b0406020a03062402070b0309190c030605040f0c0f05090a0b01 73
    0x89003001c0e075981e070800c0600e0305402c040d40743c4510310071540041840712034a000210250102c1c1e05403500d1030303141c1c0792403451102d0700c41812096070880c200680060028400f84280c046090901400840c2c40d404c0c2a50411102c20000c03501c0d045076050702c049808a90000140c0741d1003a40000d18051f01c010510784601000c00d0714a0041440c800c464080724800b8000c18030880c904241e07030300c100e02d10940041c102d0b0ba450881c0f2800034cc07908100001d04405196124181c0d01c00414542e603490306d455aa104021101010019400074180e01c00344030481c0e9010030740680003113049854042c0300b0303143c2e01d4050041001502c010025030b80002da8511103070203508103000400a4580e007080641e4469103001d035540884400b60018012000e002c121182e0480580c3d0282d01000014580303540000040c607c4003090071416140c03504034001c00000540c1d03070300490348140c1c0b050000e004500b1813403400c837460425035003041000d10300584041c0240d0326422500c5602511006010404200c0a00182ca200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 416695512 1250 416694262 416694287
    0x506090405190c12060504030e04111206030f0a030302030919110103050a0e07060512161b06150626370606080f07030501030309120c0b0301060c0204050604020a05030115 75
    0x108030304c2205828022140d000c14440c50107915038101c069846820042114101902c04030892002d102d01004461403000065025070051304031544800360a00c490f24260300d040003100065000000c21008102c180280d2615850075034410a4070b103040d58410035a0707030700b206c03010741010341da040020100d0409030006890710094a058034070380c03619040300808660140c104000c5007081c020215001e03c05407038007000c02c0f02d06a07070340c0e4080080c0780740626142d4070310003410703a003040e2290304081e4018240c485c07010043c1055107403c90300c40c101c5070300074210810325a400c080410f01c100410041d0075600b640103a400d65000d26072034141124071004e050b4400d400502030500d900d0244081003203038102d003045005408003582d80d443c40e520120100d0a9030b030240001030010b070302c4d034904212107014801c8a00080c2d01c40c51007030111648803a450ac00c541c100741e02c2040014180000c0302c055050912a6030b801040a5905501d4003031504d0b03000d49035120622460342000368518007203403220f1043e80e0b0200c90 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 416696762 1250 416695512 416695529
    0xd050702011b020c0114040509040b0a0b0402040f061704120c080d050c030f01080d05070312020c0f031e04050f060c0a08070303090b1614091507150506090405190c 72
    0x1c0641d0b14000756520038030040207000c95841a084401401800c040c0c40c22154001c02080a507075440e51000754890f406030452000603150017404000e40d0711800a04003030083c00f001c040040e494098010031400c40415505d0a44501ea0140004100300b051042240c042d0b600b0501c01c52000780c600215688240c02d4500d210b585010244a8030301d424400441c019500d107000481c00b6600c030301c4c0040c5c0310342e9064010008207008100300310000340240841000c01322101c1d001030820f45400b20311400c3c00d120301c4513000550000100300e0108159611b03212080990500601d00f0a03042c900480c1e03428142540b0a48503010114005031560410030003d00f03515800802141c50341c1ea2843c014024020042048030544403000000e8541c0140d44410303403c403400d40d690b9142c00000e40c001c0030b812b0f620001c900c3e60000d400b030140b2034004661a0050000030302c00c088080b01002c800300038000b22803000d44034900c10b041007001d103c0496000182e072441c004503501d0080110303d076481c1414864540d588003501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 416698012 1250 416696762 416696801
    0xc0703061814030901031104080c13180c0305060a0b0a12050f0f0606030705090402010e1516050f0708060c0f0c010612050309100203030105180c0702330f0d05070201 73
    0x10b10b2100800548035089003038906000900740100704601034001c4d17004046256000d100d0048851600440300b030b5207100704100002c0c01a007501000298080c2c10101035501030728940c4200100171040180c01c0e4844012603080010300c81030710000d2461500da00c52040c00120300080302050000c14011a84048a04012121796402c50f40e1050b07115034046807240e20a0054000c001450305104006a00c0380340d050b03507642d120b4071240c1c042000c101048100c90010110500400104d000300c10a10034620f4050001401702d01c06c000700052612100740c2081c05540c002501b40000c44c204101520f07829081021010345030f511041070940117140c2a403001d02e6042003074920405005020009100e80407040e0340b02d1a04c0340240340c090b60b60384400e20600d60803c0c50342006001050804030900d800028040e0001d00c3c1106640005080d1181000a600c0345168608940000d0340c0c0c6050300c560450880f00840c1c10300045d600740c08401d001c0c0121901a03a91030300c00044140d8403c0d4403090f0110304220f0f0000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 416699262 1250 416698012 416698043
    0x31207030206010303020705010c0314031801022115011e11070b0c1e070501121509060f08010b01080c030402030f25050303070c03031116081b0103020c07030618 71
    0xd50b00c40c070a02c41500540a4000d011505511407005a052250581c60350b042c40440c1711980c0119601c01400102038014547c1c1040202000f80000d02c4d24100340007808902840d0342d1205142e051000d400c40044000c4402d07402034a0f608088141001d602502c0726001100564206540c0484040d4044155001d4070b94042000702c0100058145075461404403000f14511002528000130756215525040e40300c500d042141d503229010100c0d52038070400d000300b401400713101090300f131541c0c2c1e03048038010544901060018080c1214440010108100244016110400040c0000c1c0d00604401c01c04c42c400000a070954404010889901c03c110044030389445a04004651040000090044044580c040010580382c0001030703901547d040300001d5106840c0d55400d440000341400c0b10500c84c0525103843ca003000c0700c60301b0b060081144801411b6040f8041c144015078441d40b511140c1850b1051010311210f02000822109880d80980d000039000041c00202c80303000b004000042c0081903141400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 416700512 1250 416699262 416699267
    0x41a07030203190902150a090f0f0305010b060a0f05030408090909060a0501050a0501020709020c0c060c07030515010b09040c090b07051b3304090e010911010801180b03120703 77
    0x310f128581103142c41c1d80c0f021201c00b426055544120010754031503200010301e20b488444e080103022004141c1000100d103944c0d904041503a4074164000380414031010010414000280074203014458221011850148020304c068005c101188000b010400c0100009040018100c00c8440302040140081d40518100d049aa540e81040307540710380c49420840001802d00f40341d40c15500741c440580181c01e5050800001c03500940009468220510030f2550184558403503000500080040402400381d090035810114901000c1c0b107903410511203180300406c000400441540c4072010111000302e40803560000071103080503941c01c05003840c0c5000682a080140008001654003a00f9401c0240c80340e01c4030400003051044c0450341208015200207460003c2d02c4038003101c1c4004255807090805440d00701380310407a00407440c05078141e075454000b4010b225500f80300503822102440c01d14803039030502c0307421910701c405080790300314090700c40c84e840a440c1c0e8140188011080398100032611000c060800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 416701762 1250 416700512 416700517
    0x3070905042003030f090910270c0905060d0b150a03020c4308060c0c06280c0309020603040606150201050606030105011d0306010b090f030a05070e041a070302 70
    0xd00696044490b203000c1410084140c410410100c0c0990781044680d505200d42442d0041030480e080e41d4228012862082d048515001e00b81c100c8040c2d10601c032803840d03030000c5948654114051100c480030030089596914200e40f04080740c15400318a88001c44e001c1418040a030341d00c0c412015000c01c0c180392069050f8040e004256200d012038400042c0d1410751625005268880e0300048034034800b034031403681d000071440b0400101d0038584160036500c20780241082003d503129044c040000403c05185107040050903003018032202d42c2c4464004400304034400d4410303001c1d031500440c2c0b81e42c0b4000215019078040d14100703070080d210b20780d645010700d01900144140e000f21009041400074111146205100e86481a040907281d249035900701801955a20604008141c612400300b8024232951810f001e8a4000c1011041036912284100300700b02c10090850075450003513110a4604021410009030041103c010810001803501c45041209050011000b183c503a10100c000703200c0982d916600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 416703012 1250 416701762 416701793
    0x11a0d05091b06040b030103230304091b1106010e1509160807180b28030c020f0307170901020102090303071103010b150307120e0f01050103140307080f090307090504 73
    0x10050341424a40b08004040c021030148a0840380c09100600000301c410354003541088261009128094501204ca46194450703001894030071f46500e1500c100d4040c40c1c3c0451405201410b09a8004182c9440d06030307592014404e0108441e0240045481c545001003944840000034000c4440d524040d00f80e00030407018114030400103200200040c00300c0307100340a0302c004502054a400201e40c50141806040d401003002d2015101010ba64540c4c2e440c408601c5000010300c94a000c100e10f5504400a802d01803000d0841d11030b0b400400c03500c800a56610400d5201d000100b0400c0d8803000c4c00c40040f8028065010b4294051000184d00c0301840014903912030345140440082c40051009010303c05541c16003295100011070520118038480d01680405413400144400003030508537890210f403500c1429020310031542d40d60001070041c01200043c0d020406100740c011880c3c000540c1d91110a03124800d210448501c012400b541076031fa007441988020003900700c06102c0c07400c1504100101030003128 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 416704262 1250 416703012 416703043
    0x1f051c05060702010507020a1203021c0f060504060b1b0a240c020a020d0b070c0b0a022104020906100e06030106081906080706030b01030e1c080a02030f011a0d0509 72
    0x100080b5010300c14000d03544a414142d02800c55203a069035a0000110501c80c51001d0640903c00813000c00100d00c91310150a0740e440020038100c11444200301122001e0300900d019508001c0305000303004088003250b03407100c1b240c041d900c151010b0207416810110360b5040107000d541402c00d1100c1c001c0d00307032051007a61070b0b240000b001151288182030381e03606200030300290450110007080c0d002c0380d03c1e03601c8142d00104030b090442a0001e41d9944400f00e040c00c54a0140b816408500d150208124519610b80d003104155108403c0c1016000030715410801015144522129070580c00000d2042594160628000d0102520380d42c480700d001d40318a0080360f074016822401d0400008201c00c0740a000b040b036110b1809007650a05181c81200030340511120a03040c90b84a100e01401544208140030200b50007021110509181f0034008004210140026035020300500510840030b41c0043e50b1811154020004441c006c902d405d55130041c0a20207034940024a000204551200085a411036558884 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 416705512 1250 416704262 416704273
    0x30f0c09010e040f14031204030504061404050a1712130e07020d0801090b01110a060b1008010e0c030406090807060912090b0d0513021009051806091f051c05 69
    0x35840320b1519001210058154160001280d0206504001240052284000b42c0e85020015228503001d40d0082d20210001500020200100f0b58405000c9403070140040c0d10910303040c0707450009000031210740102000a000ea540c818401203042102c00b0303a541c6844d9146031140040003105040318080e02c244984e2004203c00203c0036072011512006422580e2035208070359081c003607540010300e0304182c21814466000c1320000c1a031000c11017060701030302c00c400118402040d030050111401c0042e411401b8014244014001c1c00c00040c0500c2d03003c0c08a10702ea075140c1d034481c20950080c0c000107a0180640000044000a000c21504010044d40c0110480b400e03140842c0303000c03209410140320302032174400c2c18005d070f142074003654120f1038018102c5034190401030120b80000744a074a0f6076048201180c1041400c0010b424071801c450728482c80001c206c201e910f0100040f80040c0c0004140c211140041444101482e4405403890007808002e4010120681c400000034400c1500070001d90702481070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 416706762 1250 416705512 416705519
    0x15090314030a0c0219152106270b0d0c1706070203041a0708160308160e040b0a0f06080708150f130e010c0f080c030103050a08032e05040b18060111030405030f0c0901 73
    0x1601416040f181800460090381001482074140e500c0340f4503000120b20740300d060b403103825501c41c1c103a81511b50141c903004a031246008004401d8dd450a40044d1160300140c01b041a42e64000c030644048415405040c01e04824000c4264002d01c540c1d0070084c148800481c482050101000070050642d2194440c84500e840b42c805560022008402c090b00041000c00c8080c0c0c1b6040a810000e0b00b41d0000e400c4e64110750b1a49655104182c0d150408000104548208511030b64400040d5401a005600e0100049031280202c0c18004c0f00c41d4000d4052010407031828428003050344131111240f5030030020000947d0090004003541e18107004078000610100114080140380d500f200e0403668000020214200a03541d1003180b50001080030080c2052310001d04811215852418419080d1081c1c400155040508000488400700c0f01240502c003194404201800304100d5190400c1c000d080c000a04480049801e2451186411058044c003e0303000070319124600042200704a242120b1604250b0388 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 416708012 1250 416706762 416706827
    0x30d060308210432012f04060503010b090d060c02030406020d09081e0a050106141003290a0801020c01090c050904030c020f04020415090314030a0c021915 68
    0x1002d950240c003400046403a000c944008040342d15109401c40d02684e54160301c440850300b150301401180d22141613040d80e507800c44810200e001c1020002035180c50805003424030082481c00f050080c0d1458010001e0f0b05603082d074900c0c0300c40e0302c1e0540c0b03c0000e00c0341e095054402901e82d00070b442548050b200c0c008210130590f0103510f0010541d04400010202100e41019048482c004225011400e0145442c50300125400b03000340383c00b41c000f190100c014040441d06020f10340c0040c66a2400701850100700c4080151450360340742c80070a24002c41d00c40414481c0000d502d400e190b5118091070340c03001030340100c0503106410141400c0c0c015280c1c0b401981d552000d12414101c1140e0040018001c00d040703c0051601c218070070035054003e04010308180c2c46e1103601707200c2280710f624600800c9000700308100304099441e00306171102c55040a1800e00c1c0303503002d01030101400c20100904c11010b00076050307085406c04884000401a41001c0103481d08a000d01525500341c0b0002c04060281c0315910303160382c80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 416709262 1250 416708012 416708077
    0x206010803160204021806070c0503070608160e01020309040905150a0b0303040608040618050f060a0608070e0a0f060b030702070603050c160501060902030a020d15080607050705030d060308 83
    0x2c0a0031411070302c928941e0308000080d8424524420b0285802002c544652921030142205510400f0810220780c18441010310b064030a6203ca020031004804020445203d200440c0c603002240c14a44154403c140050b4194040c09003a20782180c5421829010300000151032451030b056117002001a4940c86100c43c1900c920461040e0164020002084407a200b12240c6502030700544c40000e4405050602c03184000f010b01c0240c2d5154010088500c01d050184040c2c3c4e080090203000b004040c0c07411403a50b0300c52900e881441600403ca10010320071401580250303c0201a01c1401c0041c00d0311111040c155400646c5c03e1030061103000c8011803464000e20445010b0040703082d40e1403c0c15407601080822500e02001201d40d95201c0b44009000d058600285003d9802c0050268540114444510071103101103100303001d4100b41c020400c500341c030216209820901d43e150640d80c44025090a9103548104000300c801640750450000074805103d0292400b0030000360180d401c1221001250443e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 416710512 1250 416709262 416709277
    0x13030b011d040b19020a05070213092013061d010618120206070f230a02060421170d0c02010b01210e060c0d050c120415180606060206010803 62
    0x10100114001c103c60751800c44e404004411000c1c60064440381c24070581e040018840040f410100740c5074210705d0040d0851004e18942801040200c025841d5540169001200312400807418000d101c1c650301c036540e815800c60501d400c203000c100d0340c2e0f0140001c4a8112503520011040307100000c110544078100313400c00124000c0e114845203080c050b00f0100d031986070f20100c0c2d218a00b0021100040e124441d005070607030040c010007222040701e81c0080da003102c9201e90442c00c0e030040308008005a44000c1683c00781c41c0c5070566461407018068501c241c0701c540100182c071020b007000d14001017000c2d1030001d000401d0121401d0002c2e1030025020fa00ba038401032140c502103200e044220401c0048080c003442c2d0302c40c5080c80803130307600b40c81482c203810704a003070741e00f450005000540c1d01d0b47e01d0f4041c0141e90f003100c2d14902c001c1c90103910b503030700581d0340d0f501800c020111007010b02200d145500301e0300b10301d8862000c10f10701c801006452914030000d10070b0f4403c500141c0152400094120800710585018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 416711762 1250 416710512 416710559
    0x90a11090906070e0d02040c0f02070b07200d05060103050a11040605010e0d061e0603051b010203040902030406110406020f060604060b0d0f020c01060f090b19050d020f03010213030b01 81
    0x11603c400b807064402408156499412614801082025030750368000d80640c51582e8031075005c2c0903828503000303040c0b00c00d0742c21008655004000c010002803a40c208150105e1f42c401000901d102840300044506680c01000350042c03066000203c01c1c0700d804500d5144441c403c10300d03420b91903074800502040d11803d1051a011030303c40e050401007824040781b949001072180100064207040340050b00240600343c1c0b0b0030118640d4585050042007000c125080e4601200348107104035100c050b00007941c0788030b20300840c1403088e008408142000241e4001083c50040b10401c103480d2511090b0095841c9580381c2004003500c104004a0040e04040c41290305071490f0340d680600e045000a0f0780005045241e00034a03005030708101444610000780304050140940880ca00525403a00c6a041c098071424032801d0b02c01c040404c072440d601e81004503a5000c0300c0f42514007101c40c0f00d85000140c048525132400300e4141d400000c010005501021401040c0c9116498801603079032150001c903401c0400311a840e40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 416713012 1250 416711762 416711773
    0x10f030201030b0d02040203161403010b0a0507030e0612040605061e0d1103010c17070807020c12030909070e03070605040b033601090c0608060a03110f0405090a110909 74
    0x35511035080040716400c0a400c4081214466002c6002c0780e204541c6e07903c0000f00c03496142d1b845079020490301c40c200d200b24200307811941070046541d1244121090502030101c0010020100344c01307542103c41d0308100504d101e1300c8034040010601ca40401f02d41c07c58110b85008001003042c07421242641c2c9454030000a8117540c0740e41030070300c051050182402d5405001800080c4a01e9034240079010501031580d59400c110001d14001052920001d007000b001c2c000401c040000e518bd0000d441020900b0444201030308410100c48181540f01c0c940b0441d4100310010b0400032519000407922103500c00550444c0d49259981c4801c03550303030003280108422a5010004240c1c0340e200c400c103983d106030038080803000560740b0441c005444d0060084440060f5110701041c41401000f50746400140700504004dd11894070100003010a034060100800d40850044413100d682c0321500140301d010384c00f80081000d401e014100d07a9407054040b400300e40b405807901008445062205106005980c60b500801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 416714262 1250 416713012 416713019
    0x60b040b03011503080a17010902070308090307050d36050a0b040311150f0304140c040c0215071e03090510020a0c0803131a0402030616050d0509120c030d05010e010f 73
    0x171130320b500c650b504204001d240841002d140d078442d5941b900030004030a005a98103820314019141100060105c00603401c01e01c17420011500115142c1031020303103840c00c6e100d400d442c0030006c0c038194011010310391100c0c80e00d4078465a8aa0400d507140c240d60040b41d003203041a40d0780312010114803d07408001c0c611020324001e01d00c1404c2854502d005c116100e600d4604001c9040410704031600304480039210440c00a51405401000b4020383c2c0341104140c0e014400c2c54000013019550b0100909800030b2081c4c14000603111611172090043e549070904040a945880740070028094296920240c42d14001c0040000612100340b00302c4607050030300e4641c07a881950a8980d00c405820003070503040705040c0c0c00244800504254040c0701d0a40000c0e40440c85070500d03005043c5041c4d0000e180011087d500308501e071010741c105042d00d80a504039000070400d690b5006186080c1030905411a110a001182c11848100c010000c1c00301820b58400400a50f82d80c0c030704800702c0c91030070312981c213211149003010b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 416715512 1250 416714262 416714273
    0x2160f17010207080c07141912060e01050910060b040509010519090c11011406030309060702010309020a060f0f020a120c030e19090e0312070c0c03060603060b040b03011503 76
    0x10300101448000041c00d0007216103640090394440c00d1402c0c00d60700850414810204c41c4520b600e0a503c5c195009401000000c0c4090555110f501aa0001125030f190700d808015080c1c104a5024a002d0028005820840e48060351440d1003c145100141440e401080d0b4001c0403040d1002c0f82c20003442c240150340303485c06018218501841c22160407080a1020941c14054026400006059500d032004031610782d03040b80c2121404440e42d00410054414024950790001c2603070b80c0b058017141c00941d20903c0f0310042c1c004200c10f0384001c1d080b82d11540700148490308070100395075404a0b9243d000000712608c0c012602c5000a00c0028400c21240300d404400d10b109800907039400380f00742080c00c686d84580703000a00c003c0a031310f15034040300c1c28100306120641c13581c000c1c2c080c00510301c030045013008900d4006560f0050000d02100400010711450b4090150b907107800401550006410440540c030303400d0020207402c804050600540c14842d112038103040501c14480c0d501c0c8203c0b00490502c1c110f507101e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 416716762 1250 416715512 416715539
    0x150d110c1903090803181e0a060323011d010e040803040f0602040b0d0b030d050406050909090a021203040509060a032316080a05060c07020307030605070507081902160f 74
    0x15420045441000324425134100005c0601d200480800c0001018020803c00c042d840c0c006030304400c1600340340144940c0c0b5102018025034809080c00b00f0b8800c001d02c8440756283c3d5086150803c41c0075000000741c0c008900a030f10070101a0400c650791540c0c1c8601c0741d01c140d401c0030385000b41034500400015001c9003108010318442c1e403203a00c0c01b501e40ba582c0e0050440507004071680b5282c80d0743d64050000c0b00e28080201d80003014041c2082410946010005440da014010401e402072140303000059079400180324410040d44c1c0201564a0056a0301c41c903956900310b40945400b60200101041841c0342108640d004c50303a200c10715002d03960fa00c1d09900046004051400d107180b049124400408614080312000742c00b02800078455075929040c1503280450260016840d183c08104500141c0ca001c1100402d603a000038020885841c0d444048800d44985103005d01880c0d0081001032069414490500c3c41c0d038125400ca907140d805000450380083e0b4544101c039040307081000204051283c6202 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 416718012 1250 416716762 416716813
    0x120a11040e0c0a03060806060102100e0102040e0c030907080a11010c03092d0b03010b070b040f06060306090b0901050603030a0c110307080c030d020f07090b0f150d110c 74
    0x9195040039580e840701600508159040c00504401258140c6101da040c441d03c4000c048040c01040107090100010b03455078400d8495401c8503403501c0f20381c880d070340d825011240140791425200c0d034a490050b10001e090b400c295450f01560007051800510084009550304815400c01c403010992080c6200540d52001040301c00c505002d556240042c46e00719108240559044070132014140ea801140f4a0703441002e580c0012019190074401803120213950401c1c1c2d803456034800d05941c0603440c0e0703051000c40521103c40003400c0c80d003003083c048100003454112800d124803070710a00310070362106400d4500313842c82160280c2c2c01d03600500004c0d104500c9120704100181c0100e002214110303801000c80c0c10f10596800c114201d90140c00000d10605003080340c08030b1802c07944098020003100758a41d546594041c403655104030345605000c0074507610042d051410f09001403d0010180742c0c00190b08494000600c1c03151550314180c0312000c0200100304a924180c04000540240010541007001081e500030303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 416719262 1250 416718012 416718041
    0xb040611190501050709050121021b0610050901120218100b0f030f090a050703031d03011b12060e1b091c05070b040e1306020c070b0711030102120a 65
    0x1000011100310a000385107954061400800e0707a01d04070101600f02da130168091810040c10741100c403001c400b0440070824281c0c0c0c0d05000341c0e0343d11010003c0440d502d206d01803405c240c02840240004041d548112108540e8244c800b07200d1030381c0e544541d07215108059400794002e007080910801050324604402d03440302c218048200900d03101c003076154864008003004180500000300303100c40c48000030800755000c50104c0c014040e403042980e51588992403480000c080c402c12800e03500360380c004210300c0c0038180c0340540200300340a13440c0003801040455000c03000c0451481c108401041d94103015103016030301010b0000b07c0d6515500041c141803401d0744010a140d0400340145095941c0d1a1044031868008506141c00442c2a0403d40c0c1403000c642d11200610030100800c020360a50704c0106507202c95032404203211201103007800406445081c0326840240900d24003c81c4100031f002c003800005004041c0426038500300001d043c201e00c40c2c0c100c101a00e06041000904082d2290414816034120700e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 416720512 1250 416719262 416719273
    0xa14071101061a070b10150f0e0d051b03061e040f080412060b040b0f091008010f0c120c050f030c0403020d0b0906090616050f07080301080303040c0801060b040611 72
    0x300c003d100c0c407036040d502694040c10005016810700c4050100640c02c00c5030184100b03001880c01d00b158a15074481c003070320740500058140c05454540a0f00d60743d000403c0c050442c43c6607921514006440700d00b520548002ca00c5020911039482c14000b0741c0d03501c00c1802a02c41085803001035452006d289004000301c424008121107d0300160b16500540010030181510034403c0e6001d140c00010380354aa601c2a0065281c44511125903480c86181a002541920344105a03110381c0d041428400f21030300848170542c01c28408421084d80c590102e01ca036881c0303590303451030701041c2d0940c28160351040701094000b80d01403081c505502e401c0030045400000300c010f840e03e09560303175011486007140300300165030102d07441041149050061140d40e610442348006401c952a20600600c54003210302c0a1000700040807803464032080702d6600b144e80140d0071040041d1a5a9183c00c40340d520360081b1811540712400d4400000c92031814060502070b5829070003018203090400c0b1088a099200840006062140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 416721762 1250 416720512 416720519
    0xa2004030507060207080d05031302010e032b14030c161523040f030305130f05010b150310050f01050f03070f261801020403050d020a0b0a1407110106 66
    0x50050008512803030141000d02e241410190812032a5440b2002c03e40040e400307102525840302c11a40d0081602002c1809451140012241a070700f201c80e8941511034901117601c803650744078000500c160b10043c9250311500f030301c504850201c6088046051203e007031011400d201401e40141103401702e241826040ca1a0a4450021180c100321035160341960f05d8107800004801020f142c2e0200c0e403808184111400c195980305d0b004981090f028003095500c1d00401ca41c040c80c0c680c240d0005401007000c82c0713100c4050802500030081c00389802d10844001402c06c0b1051f619005681c81100b01074082040145000140300400c4541c40203e410010308005841490050501441c010011f564640b164190380c035001402c44030111843d020050740240b4000350700c100100100c1c0e40304280340d00c0004289461401d10340a401290002882c0e40581445103401030350000d00c0c0c05109025408000d0790341c560031000000c6818003080d40750104803034000200f841e07000c1c120130514032050310000100240d9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 416723012 1250 416721762 416721821
    0x303021018230606010c1a100b040e061f02060a15030209040311061b0442080a050103021c050f07080d0201060918020d0c030203011103040302240a 65
    0x200340b52600c1d405003600b0302d821040740040100c194049400c3c00e00c0b014082e05500c0c0c03a00102d40f40c1a050307032842650f000044140c4007980c140030042940345003d903180c90b211a190051444101c402c1c5015200d52464004051000485007040c44040e40290001340c4601c14041e01412400d41c00312042104103e00200513200c1085440c400c0c8e000c1d5886000d1300002c038170101d090001c0580507500d84070b1030720052024981c1d0785003142c1c2280c0009a40300d00300d800010350f116030003805861a00c00c0c0203046001101242da030441e008803001c016522840d4a03a19200500c00b10b91081c0000382d0000c03007403012800701071144a214441d0a00490440e1403a205014070180b805801d500303c1c28442d045048840310858090182102405001d24248080b0062424070707940c3e40030700c0f0400b038482c0c081f014004091100c3e4800341405075030090000c0c4081c540290500c90103520a48e421001441000c412600d154900d10355524a070550500d2000f20340c580f460b542c00940544400b403510444031608541801c0c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 416724262 1250 416723012 416723033
    0x50a0e0405061c0602160606090e0d02071e09020403030c17030c0a0f020c04050106020106050316230d050a0f0c05060a080a050910090f0c0f080745050c040303021018 73
    0x1f4480c07000443c4050038040083d05480090000302941c4d8407060749180c0075a000302d070007802c1e03410028017150300650a14000c002c1c40b82d185d100c10800352001a011042c19404000548614021500031101c03240ca240b10246a110231512040b5000d000e01c03180010700e219000210551640348112941c105080c00010200c880a03800940940c2d516002080071b414144540341050703c8030701042c0001441c0c203000c18170b024040c0032050a41c104491a940f810340e01e010082030012703048030448041c918140f400801d1181c000700140c580ca81150740c0010340d880c10f071084500805a540e00e2502c50340742c8040c848051309001d40607105ea4001c0c0080c510348081c1c240305a5852a020b540e40b803503090791505203c12178440e19000203040c12603100c414030000e0030000d09482185e042001c18603c2c26202460040c5a0340d42c0100c02c020340280ba4085110600050720341000004030380c41c10003050b20b41040400c0544200d03c0001d01580200d912090140030300d80c0308180d03128281c1185815100300d940e5800c04203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 416725512 1250 416724262 416724307
    0x60f04051c020a050103090206040e040507080a030819110d0902060c01111e07051c0c080c0a060c110c2b121106040b24060a050a0e0405061c0602 64
    0xd441001c80c40c820351070300383d00800080c8401e0074100019441c41d00801ca03107228a00030603002d05079000c0420100002001001c001300066000d07990600042d24000b011414151402820305030000040300c000381c801e101d03d030014543c0d902504d1810001d698440060010701c1420fa90222041c002004003180a028241192040b0f40d00c2c29070303400c1c421100c2841034a0300c51081c0c000d000103000c0c0100007980003401100b100d21500421104030301001003202c035001e41000080c1882804500700b00008800610300d400d40c0d2140c00c09000c07841400d030007141d4035000faa00d100c05d95404200e522201e42083d000d01c0751440f50030407000301c1d00901c04180c04c1180c0c0c0300e014121f071400d0740a104810b500340d00c03000044a0300034140c050116410103458482c82c4d540e002e049102660301c0302640c0340da98000022680d1482101800701500c42c545480060643d4000c0301130030003c0fa0070041e84180a00e458401c691140000610740200301c404100f85c00d001d91a0b400044412540c02c204002140c004288141040b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 416726618 1106 416725512 416725549
    0x3020d03080406090c12110111030a2007030503041805060928050705041a03091908042d15020a03120605060d0e01111305060f0405 58
    0x10418440001c00318210680002102c110b500f00d03540e405402007c00e0804000d0450040d030f42c181200e210745441d50810000c521505024140400c034107035000d140c1a018443d10703c45649400e0081d00107035800e81c400308d000c1101800280010142d40001c40050129041003404100701440182c010000c0b1f401e16034604402520300e881c40315801105ea01f0602681c140100090017680c0180903103400c1084043c030701c40482600c0000c481c040d00d581e2000b002c409001100c231080078000414201c1c0c0c0401c04100006038119802c08482c1114855425803a9410b00d8240c420f0303c2200c03e9000c1400c141c50388240c2920190085190714015400d414480e511441c034510481c020006900003503404400816440411400ca030301410303411407204001c0040c40c012030000c00e03c90003441c48141c48001c44180911503400c1090180c080b14611000ca242001c1d140c50018005040b42040c0841 = true := by decide +kernel

theorem cover : BRFrame.Cov 416546762 416726618 := by
  have h0 := BRFrame.cov_init 416546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 416546762 ≤ n) (h2 : n < 416726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
