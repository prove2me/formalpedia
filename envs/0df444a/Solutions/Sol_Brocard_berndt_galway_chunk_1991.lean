-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1991
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:55.696789+00:00
-- url     : https://prove2.me/submissions/9fd7e2f0-f138-4069-9bed-7faed954aa0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 357913669 ≤ n < 358093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 357914919 1250 357913669 357913709
    0xb0f04060501050a061e1b081c201305090c07050d0801080703080904090c030807060510030f02040f09080d0c170103050c010c060608060c030a0506090c040902090d05010c0504060801 80
    0x840910010138203508940701840d0341c1b080486000d2080c0a0000c000780c440c400c0e050400406802402e00c0c84032448400703121a414070f428034111032213000c9055400c541081e030300c0d08040301c0e500100180301c000b0218045171525003000c50542041910b4400d001107000468109110341070042c2e82d150036a502c0c1060040d4500b080d100d82c6d64089000241a140340040d106040d9901c6078403c4041d140c1c00031000c00580d560342021811a00095800e4411508140018030803195052114090f00e600007002c500380d580c07d40a020040c0320030160071400030740c0e42c41c0101c003180040c0090900740d0203030a03000c40d040c18807181c001d00d0781042294a00a400b00203005100196010a4442c5107041c28a032502400015007000006030405502200442c0100000d0056000c030100007507200b524012410b000d642ca82c4400d02425440480f1003045002c0144010f220181c22a0000d2026500c003c00003002d40407180c55060848090403007030310105900103000c100032a04440918010000d0309030210310340d5216 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 357916169 1250 357914919 357914927
    0x809060603060112060f05340807030c09080a050105190603020a03030813170415023019080a0c050a090b09010e03100f1b0c1217070903050c030a032003070b0f04060501050a06 77
    0x1422b00800c1c0354803200c103a007440c5d21410090008000103400c485440170b507820400c0c001d000c1514001000e41c115046101150380b14001e24084907400781c140d003189407551301d08895155010307058418111103041c001011506034014a0302c0c01103084000b640c1c844c90404440800310f001d441c2c002c155080164040c40e012a82c5009410b401c80001c0d212180040e0300150b1195803051300c40301c0c080403100c4100c11038041c0c0c0c843d00e120711507003014104100c041d5608500380d515000741b0400f0800548090001e1120030007502c040e12040c001030601500c0c040781d020029041000c03000040303d005a481c41089507469030b80c001c1c8a91140c5111500400c04400d05000302818623030725020302990010040700f4401842560703800c1c03405660412038051420000070060801c41d051100340ca9a100f400803100b624900072843c10202c039410f0b25079654519010704072900c01030340c180d2a41e1140c0014050400800c01c1c3c038140d00c0c03103510601440d544078909460300404890301a00f0090090780e59090501080d500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 357917419 1250 357916169 357916171
    0x101b1805040b0607020303030906102111150f0c01050c12010b03041b03120e041109040519020a02061918080c070519060809060603060112060f053408 66
    0x4141d41c0031407450304000110300c1521490130000d4143c480041004003064000c90050300503416010400350056450350fa00341115072110a00d004030b9201c15a2400080c21124460207045000d816001c5c6002d58500e0040250051060100072010000300300c8900740c1c0030320541d9409000c85500700d0400040790f401591040e41401043d142200001c0428240401d45c51403810350350000700c1ca0035001b905d9181070701400b8020080c00021074032614509480f85418010241c00e2408165000c0c00d0050f6081040007800740034004c0c07444070070b0714604041c00c0c0300305000505842c8100d030010011420250091001203800e50f401d80c0e00c0c07601d061200300745151142180710b021604a041d0a888990380c06996041c0b880302da1203c1c1d880741e034601c58074030a000e24840b454101c0344107071a4181569200b184440e11528120f84242c2e16800400060001c0c210030580380d5020360140200054400109401c10100c0f041510b92281c3c8100a00d51010058094640300302e00b03460610030400714030403052001c0c0c203c0354 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 357918669 1250 357917419 357917429
    0x406110313050907030b1302040612140a09031101060e1009060b03060402180301060303020d0e01050702090103030507080706060e04023606030a1a0f010e07050d0c11101b18 76
    0x200543c00316046a2182e044403158080051101c03052a02810445000358000c2c4200800718030842e0300e1001405e8a8071955000445c100b03d00c21a5540e88585000107103030900c001c41c1444007a44240860321b90920800700980b24052034648641000010700d112405c1e25400248841d003050300500c90200100250384c0c110390b040e01c0c050b03101d2041105040c40b481c640e43e07040b5055880d01100109143d8002510107502d64151540c3c1c030440c00e844011140c0b445104406504003440e80c00400000e849840140f004900442c003080c140031440d6259801ea91140c3e1106a200c0540350501040d45030044410100b038036240f2154036101080709803880d40201c1000e90210342d01c209000101e040c4c40034007980c498603a124a4811650743c484500703109100054480c54082c46810700046000c904014175a8050003003030700e0740707400d0860109125001d4030345441c00c50300300800346900e03407041841000000210106064041084000020314034500804a800113041220702c01c1c6441001444e0312485042e16 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 357919919 1250 357918669 357918679
    0x17040303030b0a1a13171605042a0203070f0507030302070b071101080405011d0304031106041208090109051f110d0c1e050303040305070b060108070f0c0302160803040611031305 78
    0xe074000c4904000b80609601442d02d42c01344501e80303203c01c10041400e20001c0b096007c3d2a140c2170301e4600b440111890b0a01180200e0b5444000d8504003c00410603e8102c000d841103900e840c18076601d000395034a5604080b501540315150034001c164050016801070214145114142011074072090303040514219094144009900400d080c4070302904411001d807005412181070f083e001c001c4ca07542e54014481039440c20300d410350514052504100b1642121068a02207005512030f40790519184c1c000c40030507051001140001419071107640001400011a08079880101842030001e009507050104c0d00005400042c3c0b0f54078400d03003142038202800d4000c060807041c81000b16103454520180c40c0c000d445071101200f004105a03000000302045072140591142c00d45607003006544485090702d8840100c2c0400501c05d4510384120f000c105514024070489050401030f00d1841d10000300d64106181503080098144080d581100c18495002c081c2001035281044103003040000036845d0207094450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 357921169 1250 357919919 357919927
    0xb01090507020a08040f0513020f0316120c030c0815091302030a08030901020703021009030e090408160302010b0f0d051504080c1212060f090613020717040303030b0a1a 74
    0xc50b2082082080080d400711405588a80703030340403512140d5503489001e1048021203103181403040c050003a90000b100348c03001070b425038450301c800302285203603244200c04001c5070180f100c0d009a0b440c000c42203640d0003601c0001e2a0010250001c0803200000d0a6001e40f00ba504000011501c1d880d1140358000700b40f000300404c80c0c07654400681000100c0e07502031301080c404414000300d06010b40c01040368500c01d0302100d042d40d0400e11404262403c0081c003801003903101001202500f081c1c289994170a11450401d860071140c0c04040707043c940c814405030b0050b03565600f020842e040001100c0b2000ca4111901c205c0010a681c5083d60f50f0b03586080400900620f80109041040140643c1e41900381d0310140e03040c01c1d42e1020308081603041840d8141c1450392100114072541003004014100c40005010b0070090f688000c24082460452040444850750030050340010030364280c50044001e80d09168960b80305e1442c00c0c000d0a44103191001803048504000030031152075040240b10000100040d0503032a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 357922419 1250 357921169 357921181
    0xb0c0a0204020a050c0105091c0c05070e070302190818150c09010c1703060405010e01080a060c0509030703060204031406010e0a0b150301171209150d0f020403080301080f0a0b010905 80
    0x111700461000045540c200418030000e10000308180542d0300c003924203000c02c004c483d8012a5540ca403540046c2c100c3d080b10390140148141400c0d10365211080d030802502c1e004050a4140c48107005081b2840000c0140040c0013035070070007595110f10090b40c0c1d0700801d000c0042c0f14443d004050040c240480d200d20020301c0d038070542d00820032011002d8001c201c0c0c0381c04805210044021358411a111441a45000d00109114000000084c182d401d000d00820798021540d03a4a401030800700e82c0541805001d000140c4130384d80800504016504c110f10240e2075520318070b003044014528804951040c0c1102c8018050005100c180a50029803902c02040c0d8485480109000e18248581c01e5403044000002203000800a000c040c85041004211350501c0c2c401c071399681d9940500d10210364010989001610140300340405040c030484031040006407060b0161501d01240d001e03510480341100080010449030006003c0b00144401544c0601203810341e42d6a4591005414012804290b5036040403501c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 357923669 1250 357922419 357922427
    0x30906182e0207051b04090f02010f210905120a0e01080a11191106040b0a0e0c101707140d05070e10080108070515030f061212030a060b0c0a0204020a 66
    0x510401c550300700715519402410010f4941e40001d0400e009200898170101040c01d00d4415900e8140c1c100e480101021802d5004558450f02d03100000100000b00060000031510b40d221070710f01d030a0301000007404114603c1c000741400c980219008072407100780001601182c00002c901e002031400d00e0010403590f52109000c00610044a050300008004107014500341d0b41030348021100801500c0d04c24070010b80035210380d0f40310341c12180142009001c00214810040e00c2c1c10403506400c40741d082d54407245401001c54280e84c0b008980f03800281d0f40c02c0c46440c182c0310b41c40301241c00050314030b891520b2880c0800003001a22407050b18180b21607a07400016030703582c803820f8502c82e5a00010400d52031201ca0003001405214203000346d00c03460181c0d4600050503c1c1207810805030229402c0c08074110f9075441c03407500c0501001001c0580041d039600050080f01010b000c4190701800b6092915124208007440504a80c501c2d00f11012044040100038030341000000d0b801d80d1103030b040b2000340e5034640080d4222 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 357924919 1250 357923669 357923743
    0x204180e0a0f0515060405073009050601151704150e01020d0b031209010c020d110d03080a0c080411090403090b0d0608190804090c09051503090618 65
    0x141c0080b4210310740d0410014042500350206605000c0c40341d8030384503202000100c1d4000e84034440400e0510404041c00e55007044011000480c826032514040026181c080a96615840495254025000500c0421040103080e51020840d142c8030140c0700048004101c031480252018018480801e0b080c083c802040c0c00040c00790160785c000b5034a030024401740360041c0603045042840382c010741400400350b940c2c51060b6541000165659040000c154080c0300039024140e6040e00d000228118111140d01c580494104d80c0781300c3d580781d00d058030303141d0700c0c03842118031a00030402000b00400070f0002182c100044603000100407243c9800c1902d440c075056500b004c00c0e510120a40c000411031001c460540d0b80214112007802c01500c00300d4031a9468158181b003500001050348030180410b225803283e9600190b90305646003008840251108001481222545640816090000104807201901703001103600022140798400da80ba020303088454444050319524400080000d02c24900301403410b0742c207 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 357926169 1250 357924919 357924923
    0xa1202030a32040b0307020c03030c0c150d1805060105030d0c03031a0a0807090e01020405010912050106050414010302011e3906020a080f010302060a050d140109060f06030204180e0a 80
    0x860f6560f0f9101021101500102c0d084005401881030380b201ca400c01004951603040072001030b101c14505002000385007211000e40c507640250034040101c040f03c50f44102c200142010310842d01d802d5117441c0c041d18203030050700308a0007604010664484c8541004691038419807508001c940e540c0303149407103d40402e4000307500f54401508200061000808a20344041e10303a001f00900c16100300001641c00c1c0d02c56031250f0f40c000380c1c00040810080a402020548240c420703800400e03000d90f01e1000074140e1300c4400c01400c40c811510010800c560f0050b512408000c000c400c012605440e108001e8840f078404c41c5140c80c556102144503a280c1c0310100c00040001e100700003020f4020b0a420a4002900b00040050226081d440840c07407000c0301c1002c00c0c0c12030340d00801040ca0000041402c8400e50008000c6007499501c4001c4544c9401030403400034080c01001c01c000481610748500c8079030880c1143d102d1418144100800d000000b2090300300070358101120390205001c04a188041e24100f189880 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 357927419 1250 357926169 357926267
    0x2414070504090c05041206020a2c090a09170a03140108060405060603070b0405010e04181202010c050f04171f020a020d0306081c090b0703020a1202030a 67
    0x1001015500200540700355800e44800b0054020716103800d840d04d11403409072840f2002e8042d1010b0004002e900142030a01e41c82c03030700785a48000c580c0d000a040c0d0b0013151015841c4800c030442c0c25181000e0310440e500000c1c05105115900c804d0320b408400c407a42c4003100c01c072241c000032100c20a50094000390b581ca040b40300c002103d5039540c80c9403030304e40c9001c0e541107880d802020040350f2203280000759002035451004400b441d203454080150344100c0a0078100742c116880701642030240010812a42285000700e000c1c52103100340101c024211030030040a4000e100c0d044c040900b00351b4004007a60f0540d00100c0c018410384c04040e41e103030310f80301050b4510305200c2c040c0c0400307520310002c1c0d03000b8080c40030302c5400725210101030303120580541e5680d0048003c150302404d85550b05680d40804007020510174203003040f0711522000c11501903840070005801503804242e09404002800105603502c00c1d0390300c0590304180c1c0c07000300100141303026081c250001e15940d00201e00c0c3c070905210742100d07240c038082c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 357928669 1250 357927419 357927421
    0x18010b060a032708041e090203070e0a090c050909044b170a03110c3012040302010b03061302031c050322080a030b19032414 55
    0x40001d000c0c0050403200f810403443e08580510041844036004a52544070b244503040074102407005115541c0107500800ca40084240041c0d90801c1348001c40c05503000c1c0c0d840101c110384010034410001025800552060324001d1243c4502c1d0380002500c4a2850465042d007071074449003032454802245041080c07040c0d0054084420744003846159500c1036800b03c0306d080801070710800d580245040e00c6000740092030000b1403010603000d01001840000e4641c01d001450b140444401c5903030b900311107040482507002071851240d021601501c2c201c02440c4005170034441d1106080d601d8140241103481e9203050340100450304142c000c0d040700c45e25040c00b400b250300034940a202681c0c10040241e00340e0003805801641042d00a0451290052240316207441e4659103601041031107464400015039140700c8000b18250000d145400100030f0302e016981c000c183d40000108114003131f180070700005807060041c0005c10018180355140c6062031800b01b0419502c00c0c0040d01a00a408001104112600150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 357929919 1250 357928669 357928687
    0x15060305010e0c0306150703020a0507090509070e090a0204090302151005040c020307020102070e0601171515040f051507051009060f0c140708040e01060201020d0b0904020918010b06 80
    0x58405070488211989003040d540383c188501642e4441900e00742d40004207504e065040b40c4c241c0d402004450301c00d104a9602074100d445284c10301100303410240e105600c40090044541003002000c3c00342681841c1e420007400c2a444455881d440182d000b03020b540c5440550050600910018881420031040392a40d40740629030401090564007580384030f5450424a2010140b0000546941c0da41c180c00404bc005e0510700070740f400d2540244045d0400410307035201d402c44c050b2949030380e0003a00c40800005000c0b9640f002c02107078800e1542c41c0e07880c100c2c1c244810002c08907441d02400448005030344500c0711011171106242d0522403600050954820542080c06002c0c6903845000041c1c0500b604110541d411040c50065404542092000400d00e2000c0400f455140000b800001d104451692401c1d0781c5580044500c0c609901040c050307580821110224003980c01180002a0308070b8151040b0300d4240d00094030004040e00c09108a40e05540001e1354800c00d600c040a41100201229120301481d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 357931169 1250 357929919 357929921
    0x15030e07090915020f09040908040b0c03071103061e0603100207051c0305270c1f02060c03010303050a03090311030309100e07031e0305190e030d110d05070501150603 73
    0x10410442d40540c140e0f0b220b03030b10501c0501c245c3d44880d00c040621072a00d4543c4007040060000020160340e00c1c003081000044124004006102c01c01071400596101c01440c20b26000184411100d540241c001108008000c0c0001d11517010809094058031995166480132a10780070b40f00440d51405803002a030403007405000104044a62703200e2440c0e454088c0718600c00c4098850503641058202510700701c03015020040325065071440316100450f583e17032900e000003402c503e0210084060450000c03000000280d81440100d620081c91803000c2d00e503500d181c0c0c00800e14850401c04c802010740d100c0d40c3e8000c15205124400b01410030130100ea403281000380c034164442203040c06090000c0d1510944041c50240800c0c468104e83c0c0190442c0441c0d0044100f004078200f5041c0c0450400c4410003c0325290795810680c61502e20080c0d40b081400781c9800b091500c0c042c002c401900a01030440c0030701c1402d82e070000e00d0402c2d002203031500f19112003203440c0890260003106100c1c0c4407000c10500c003181c69941 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 357932419 1250 357931169 357931181
    0x3030903210f030b06070803010326070302030d180b040602130909050c0d0f0b090309090703140417070c17070608010308040b0310030203060901050a0e01110415030e0709 75
    0x1d0040240450200400c400c0c505118210351000300780d09102040d002802035010640060026000502d00b450310f81d160200d9910907001241d01031081d26880781c9540d100740c03010580542c10054645000460b45000c0d40d03d0180c86101c0542c1500c034002e442070441122403050a40ba0b01010340d44050606290000181d0000340c0e103004441c401102c0000d840090b40601d542d626000380103080d40d1511081407002c07021000d101070321079841c0c00382d2107800070710307500080c41c8070300341003c05940c48002110800659031005071030b0004160408402050601e49591a6070300b050f031001d040c8510302080d65901c0020f00a8030f4016000f40300c440c03130001d1681020780c101c4100c2501c020950700400d072510420783d0103c00a00003d00043c23801c0c0800c7c444c48050500a40e01f000160440e10300d0b199a0754002850700000700c0d10340e260360351200107000b080d040d0340c0207180140300c1e040000d02614071070360b00c85000c070b00661103068100c4c0c640200d241b01c050701030780c0a041d111000b0010b64488545400800001e412 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 357933669 1250 357932419 357932423
    0x10b2706030a0b090907050105030412021207060b09060d08091e040c170f01060912050102040b03241f0302030c09040603030c030809010506060403080705120a0e0f0405010b0a08130c03030903 84
    0x500031002401500c5d01003121000d0b244141c686038115180c64882075480b4504122080c00e40c403804041c458484c9118010381402403094402042c061140000d002443c50007a007600c3c02040032a01c04000034200f8800e0b2a4901c42c20f8960310031420300035006203690310711100c9158000b0310300150000801e900040106204040d004032140a40316444030802490b424410f40340001d5020106122036404c0404102400e40160009030601f9141c2c0e1500e41283c3c0242c1d000c0e916040e0070200405011601e540c0016401405c6442111400403010340b0b82c5900c584078402020194004001340914145e2400d98040300340162080003501e85a24014000880f00b480540c0410480300000e010000140103561040402501031400c1c01e1030360390381d28100d801c00c0d0b008840038080c0ca0144841e500360000680003c884503a500312015502d107003840390309030007240d01c81e01542c02c0c00010701c50100110704440403080b0314500a12141d031010041c0211040c210030080c020f152002c3c001040c103910030013071010b4034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 357934919 1250 357933669 357933679
    0xa17010b0c07050904050307170702150901110f0d05130b03040b040302100b01020d052a0718020405030606120703060e01023711071a12010806010b2706030a0b 70
    0x2a114810000450000c0703170000c0550744100301080009501209a805482110b40400e05204040e400581800f480703c02503810501e012441040660b4091041490f03c03200d0005000c0d59440c009007280c031000ba468129041c8100080e4540441070b0b81a01070000700b07140040f413600c2c0d040c40e00c0c28005402c402d035400d40052145103200d4050411070301c101e42801b481600204480741c0041020744250704101030b50241c005403819507805071460807070f604030024400c2001e01a4107085c0100000394184003440c4402c2984184004e010030740f00050f0032a00700b44103d80545280480306140d92402c000342e00700609160a1070103d6514580540103403144007824400c922182c10000b48200c0443c01c43d03480b45003440d071071520408600780941c41e92035160782900240e5400b0781d1680c05e4140c06041c60900180000800103040c45401007039224a0302400074003002d041c641d450041c40d56011300a511903a444401c0a2070030017a030180311807510030302c260082d02aa850386401466007000300400d1410714050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 357936169 1250 357934919 357934933
    0x706090b011d010608071b06141003170304020a03170706052404110d0e0a1203060b042106050705180103020418020c0f0a0c080d0509010c0201050a17010b0c 69
    0x3540690203140c00b0201d2000100d005030303103413590860300f09101a01c1c1c0300511660541100d8140b100582143c8950302071800800e6002900d500c1850170280100f0440c03513481d8045041c400a00c6464442404000700345103da03c81d100c5000103040c04c401a40010041a21201844114118240640700704ca004001c200150ba903070107003164036120035496141000e0f0b1403e41c04000c40c9050ba10425444a00c100094180b03e400c040990440b40040c94040050b4041314842040010044080c465401c452030103021262130544403540d82e0240b4003d40c1005178001c4003014410000d950110f2109030403000600c2203050210300542260300244482da030038000b802c00407070b40d0f5000c0c0c021241210702d000602240020f080540c2002500149120304c094020f281d0a01113420040005082c1c6c9401000e00340480307490202101c2c43e007840010f0304030602c581440302c08800d0303800c2000d06003100d80a00704203517603091250049814400c820800e0100c80103040001c01c4160314500507189880c500384c00c45a0b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 357937419 1250 357936169 357936179
    0x3120c0c0b0f071101050703020c060a0b102316200303090d1a010618060305060d030518090c040501090f030f06021b01020313033c11030706090b01 65
    0x81580010300941d001070041048044800103440c1e0000c3d80b0324012485190501e0100d094030400c0e02c5600010381c0100e041c800c141410f000d41504201d401c001000407000d20070101d00c0e0842100c5001042c043c5a60b9000300c907a60004d618a0026050069656141c500c41850a4444c1c5c51040a5039103000300780702d0b00e01103140c50101400b400001030065081610010401902440c00030040341c41454030604040d00c81160701119010b05825140c0244e100c410b0a203041030200280d01c000101400c0c4030070f010841c0c40b0680c414400c581c06181107992040c12142003801ea0b001c186e0400e40082207441080030103100c20019000360b4000341d0741d01103038a940d6515507200610500024103064804a01d075000035000341d00911442e0700b50b80c01c54160031182001c0c10b003242c208942c50426200d10301030000415a204440c0c1d00420f0010070380764540d171000151900003209544400188035280c4d409110003078007842c1e1789c00c0c045c00040d0440b170f90b8009a14101018084a03001240c54a810400200b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 357938669 1250 357937419 357937427
    0xf083f070206010e060d050f030717040f0e060612070c05010c05040632040308040806010b0703021c09081002130501020703021f090302040501081b060309031605030d0903120c 77
    0xc01000d00d0303401007a0310f07424240c3c40c10103644043c1007181c2c407000080e0441c000440a00203d02c0b081007402c085d540782c1c0d52034109034500b10b41c00e02c20300c14140410841440114640c5078144151614000c0342201c55484201040244c802c0c07420380160f0146c0802041000743e805501c005c2030510032030083c0880c15100006440d40d01403401a40003041480c03100c5800a0301a06910800b01c0480904c2d403a401c0d002600c9003056403103500241c507600c1c0c00003414000305004000550040050200c09840e2034040e0320001d440380100500c4941002c00104440c0c000c03032143c811000903103c250240c80b12840c52504010080d803000a14034083c400c581000519503001040800c01c50360044c01c826080320712045504a491010649542030220652020002d600e95201c0e035070103800713100d0003000040004003074070841d201010485442542c08204100b44158040103a55041ba01c440c03480c04d0081c0d013454100c0c118000c0d2203c452485d45080740c84070078980e01440900458001003800c00c407203121150111 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 357939919 1250 357938669 357938671
    0xf0408010b0301270206070c09060b07120912020d020a05100210240302190902031801050a1e020a0207030501091a070810030305030901150308041e0302030a0f083f 72
    0x1078013031450403031107002604020700200318141c03145071045003440e10392610104840305508010050b80d030108001080008500910450b441c140c00c00c1d0b00780914150001d02c000b1101100240507450481c0702204648410300b28130040d1000604803c600c0000b0f20000f5502c00b41000d40c41d5030642007500e03c0024a5608040792044810307132240c0d200c81421a0203200310404107205421803805040d400145429061026601500c0c1d410030380207020742c441c5074290075513001030210003540c0d141034007038a0004591481124020180300c030258580c0e4120b14140d04041d90390380090219420401c9a130100004108000c8103403020805101d2a41c54080c0216008141200c46c0c03a0109403250060020030300442c06581c2c84030100b00040340c00303040f8507404004a6a40d9104642001c0003040510480003840c028a80a43c130b1500c0303144050b491a0002a69441c040001800646441804030140403210742100c0351030041d40100c041411341d50390745403030403003d0002480811008402c0400e01940c810303402c07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 357941169 1250 357939919 357939971
    0x50109052a0306090403091205060106091707090b06040513020d060e010617060406210c0b09030a2006030114010f0507032309042a0504080a170f0408010b0301 70
    0x10300b903070380e44400d0103520000600103500384803060320001042100c445014260a10803005031030300d545440300240609809401c050b40d00b000e204008600b92034001403200444400713045c08640c3c0e5048201142e028413854105640100c83c02600e9647d100c55a0020810010650130420210365104002c1d20240000e02400001800050550042507419030b00290000c1c0020400a621070f9030786542140040380d2001d0f6600c4100c60100401408541d42c4110014426141a02d160640000000c0d49a00e080c40d0010181400705600e0220419910009258030001034a07041d525610f901034420078514021983d40010603122020580e40d10804c15280a1030385030f00c4000065480721543e80304078180d920702141e202000d025030911070351a8001d84c1c10450a0340c81207101c04c00c03050200c0300310b08164600c600c20300c0b034100b1081201d03120004602407901d411014599611800340b003d0740c1244561001040b46401c045004101d143c01940281004d480840081045131f2403802c0c108206043e45c444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 357942419 1250 357941169 357941251
    0x61d090c011809050603071203180e0705040b1b010603051b01051c1d0316020301140903191e0905090f06060904111c1d0a1707060b0405010905 63
    0x104140a00d43e00421780001004090b5201e2584134103510301441e0101500380c0008503800c0a14603015040a0b940000c1c090399a1107949900d0418806403481c416481051b10801c400990040d480d640344401c48149440c0d00002d1200035a00c0c10010b580300d610440354880c800f0004208059036014504560b02c0022800c0305107848101e0900b81401842c3d10740c0c407804d2103c3c021001034940d01050006020700d044803080121290341c1da005060071950300c100780f814864840e005100201e0800000c0d81c10700c0783e055442502040002d0b1044419014415601208035003401142903126000b131041c005a40f010749401d8595652039076504414081902c52980010041218079607a09068000819205180030210314007840d140d0383d80c40101003003c000040079078401204084101211241035200120001030030b5589407911a100c90500080c1180d86050000900004010007500304103100c2170005c1040140d507035a0014600500305c00c5403070b42202d01452816008513031400c1c010030310340015415 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 357943669 1250 357942419 357942467
    0x52508091c0302161407050402040e060909120403030207150302160809030a0209090c0102010c02030a020c0f0d0b180f07032105130b270f010e04061d090c01 69
    0x4104050201e80c116000c0030503070200015240c02c2441c0c0e8101c1540b910481c20300b0114000d2402d0181084216000203100d03d004020411420321702010b10307500300c002254641072944a000c0d0b05407514030341c0c2820348074440001c02c000040c140c000c20301a0845070b40c00d903e47c0c1460041c4ac03084040b40304001200791aa110b1003642400301c0c9419001d03104041d8043c0445240000d01c3d0005118448121414190b50703001023260101540d084c0184038550503140000c50030305400c1800652100580704203240600b10148440c80d0755660485801c06450700248900501d050400d1040303030b0744d00b621184501500c903500c0d001580442c00141c2000b01c9410080e0005a80111414880182e9075414a003080080600448000c11440c0300101c0060800e648400e940d20191580d10920a1031403600442d5140c5450741c54800c0e03140c1c024250b80700c82003481d010340203280700e100280042030039070410220f00e04280d1009040021044a080c0640d000c9001c8800ea10010001107444641209501900b004044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 357944919 1250 357943669 357943693
    0x40c02031c3809060105030115051e03041205090315060a0f08030d200307030504030c0516030b0105061305130b060d0b010e031c0507050309030105250809 68
    0xc00c0e50100c0701c00912011075246140310710b0b400041c55900d0301c0c60341d40740c500d2840002c0d80b03803003044520141400d590b850765a240420018005000501c04e4000b281c0f1444020300005108034101d900e07480000101030704c0781120240d0b00041ea082264103c80135481c04940d0307840c240c021000d4038000c0e800100180b114115210402c01550707005844c4c0d5801c13041100c40400c6a824480c0b001014000205c010b41e00e419082001c02c00b52a101550ba000e4481071305400c03003600b4000c1c01141e42c0007a9a080c0461340c1d44075450229007223070303880c94080c0a070f00a0407400b0541c7c40010010604584c000c2c2200034075a600c0b4400c20205103d0440c000c0c1010340444001c00071401d20b5000d0521040d00030900094125156012400c1c642c0440002540c665a48184003059038000b50500c004032402c2d0700500400314807110b80420f81000c4250070703060200c007003201c20030050100100c0704481c2014000344840c1c100384070340d1140e04041c8a513401400316012403100d00c19110302c1c00c071449455064018541c000a80c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 357946169 1250 357944919 357944947
    0x4050613051c03060503030d140f0103021302221403010f0e0304030308072309040e030702030601050613081006031202031e030a0228020d020c0117090a050708010207030806040c0203 80
    0xe0b2141c2c040c035496110000b04c070703a002c2c000341c940520342c032801256900ca10840ca0006240040844c0d2611205000610258482c0e004040c0c4140f441280103035100d81c08201d0200d144a80046044002c161172004100c2000721440000f14a00c141d0091048422081921007614004c2201d0320fa41d40c03040c081000440c1c840e00b19130b50460480d003844001a040c0413098884407003509014507280d00c1c006480c2580b8205403054000c40e0b91010b02460804026900094580c001071080741d20604000ca00389600b81c001078100802004c0348001c640500f0003540405014040c24403090340d100e2188150b01f00294008402c41d001d241c0e00517000a01029031461071221504098404101c096003442141260300c842c0c1080c0070003500f80310900b04000f0500e0802450728030114030b907508640260350540c03041d0b60401d01000036600c001e0340c50300181d51030310380c158035100102801034a10700c28204002007990b4198001c182d02030090307032100f034260f0300c202c01e10050b203903000c820b24010790041000720901519 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 357947419 1250 357946169 357946213
    0xb040605070b0709080609070f0f05031b04180c18020403080403080319091a090d0f051c141504020301050a0509040c050910050406170604031103041d0405061305 71
    0x282e0404030131031529021a81c5c40c150707084600c003078190321a11083c056607441150480003004842c070b440b0550380c24800441d0b110810044200030440c0c3e802043c0d605583e0b0381e040750070341082090780e0000351071132818a5000501107101e0000310130000c00441c0c607641143d008407410349804c009000d103414a035a9031000113030300c011b0058801c0d001c10340340b2040c014094091499218064188111031080311100e24401d00000742040c2560340c800004450341c07035000303084c940016515040060b2542084030030f1042c21401c0c80c3c503100401e854000350003251074002e0182c0d800348009070341d00d84048020b44148401c030300c001e0044c5035100f0441c5404001d149001c800f04daa002d407044414026955030355010a803100c0c002c0d00c0400180c2040c09080c4000d09041c07203110000c250700c182c2c8064080071000b016031035440192000d804c000000003495814081041100d0081c940103040b000f907015407090b21280b02c00c042d00d04079441c0c001c12000c900216100c16012800740e401001510340110241d000c0300410301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 357948669 1250 357947419 357947431
    0x3140103021c0c1a0702090901091e051c020d1d0102030d0902040b030a0602030a0c090e04020d081e0d0c02010e150a060e01080607030605010c1109340206010b040605070b 75
    0x4504001056885900003109a08000e1130715550300d4501c1d071300c104103044900500d0700e485603141c04030110200760309513255620018699aa80b8051400c0e0804509142c0302c0401d51b000042a6181807012950015074850303100c44a42d83c203000810842d0808511b0420704c10128010382c01400096001030090303001c8109184010000075244410002090030400d5640c41034030300d594080200402d603200e5020b1805c00c0161454400310182c1441c04a4400b090043c1000c0d0041552039404800c0200c60f40442d00d90101c019100c240309210007030f038442e603580104c01c940c80d01401c0ca07a0420a0b14014007074190b02a11800141500120400078850f07102802801250101d4036070100041145032014454060420030010b400b0524040c0c0300a0180c0c2c8499100904101051014501065161020b1800b40808966920490301c0d03030420101000c018000b501c050b40d8080e0b40300820105000f188a664030459001d4400c26a07035460422203501542c0726a03804120100b0101d800550310b1031025521407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 357949919 1250 357948669 357948683
    0x3050907080a1e390503101a0603010816050618010f0201200d140c0a0c03030609050f040c09151206020708070b01140a060f030903020c150a03140103021c 68
    0x886840d01d40488081c0e460041c1c040d031139603000c441c030300310141c0b41d801041e074542c1a2018014039107008a40c1d500d42a100d070052941d525940d58070802040d5a10b040e42e550b00500130303501c07940c450340456240c01001c0d9018850000c4480005031908040f4292462000900341626014000c2c0c401920040111804503045541e42c40d10707000d581c03201141c40c101c1d101e40d11f0012038854a03003814100c04c4890796a4024002804442000855400281100c650391005d250805070075000d45000c3d00508825001a0449410310041001089800c421580f00d04e008800d0712a00590b0780c0000411510b0b0340c5180c05003a1070780403082c4003039508403540141407841000018900001c94403068180d0300301c0785003100c441c80c0c114010403640303800707076030700300e01410100c688155003841c10310082e00c00d00c000c100003410325032500c0424041c5070003800214220300001c0c0644c24141c403480000d105031b42c403044400c1c000c03078503092402c801c140d40c1c0ca450700d040c1e03503000d4003a0f4071010f08050481c00082140c44111202 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 357951169 1250 357949919 357949973
    0xa06180308040906090509030c210f0a032304030f050a110d080420130e1908030601170f010611070f03030e010e0906010c0212010917030703050907080a 67
    0xc1d440e038024001041204000102d0a00b854681c070150b403409420000e45600070712141c0301680c0301180d10000100c0c0e40c03040c0b0000551410742d062041c01250700d20208120302180420704560907030840300006040700742c190180a0750011005804030192000750000d08042c0e0f05d1603540380904000c003440c417442d08141d41413904059410345001c400361000c03c00100544280030400c125a110584810040c055070980c08120a000c55171045040110b0141a9200e44150800280a00c181e01401c2c80502492000310100e00b807814195106a41480c00a0030300041420041e500c08007450140c0e07000001c880700380c0d01c0d004048802e451070904441050040180010340811340b490568000c3d8030944500050007801400034105401041c40b8900400442d000c001d07503681e00056407c1242c0c0d04031592850f107107a04000500502a11000402e070081482c80106045400c4006c0c601c640000d550911281da24803000079180e0020303105070200c51348070580180004090074900200012460301d10594 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 357952419 1250 357951169 357951173
    0x315150702090114030f03033309040f03090b25050f0d1101050106031b030906020c010c0806040b121902010c020d03030e010c020d0203160203250e150a061803 70
    0x1480b1003a4071030f42d004000540303940180d0030240304607225107160401039800d6140a1078544442d0114000104a5414910030400042c0146100f61000c00d0701818500c02840d281c9000806401a00c1064004c03402100c00041c410380c0030002c448014180072120203400c1c007603a005545503940039504503414011284042d951050800c580d03005070000381d540100303882c5800b42407400c461040c4c00100c01c040c10403030300c4c2c2e89203006112500443c018900d000240d040c11402d08030000e005035010505503508080b50148002d80c02602c26014180c211020000c1059407000c2106e407420100100e030b0f40f41c00c11403243c022183c015680815840c018100021502060307400901090058001240820b41d00c80742c0c01d444a0003481142404011400141800c1240078006582ea00407030620a582c0700040710300c2002c41d01d09000c403203d10070b07803908416082d2041030018000300045000b058492800840041c02c01140c030003010602030001b52200c515039081c1001141e030490100b0080400c04028500000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 357953669 1250 357952419 357952429
    0x40b0a0609120816080714010b1f031506020c0f10080103170c01050c072109090207031b050304060f021527100e0d08010506180a0902070309050f01050315150702 71
    0x440140301c1c01d15669506c0aa02e8070030f4900d140702880d00381d260314001e01c0258a4403543c000c41c1310690f40ca101420790703200d060340480250040c03031020000d0030000707540022aa900054450840d50080743c008180079008800c0c00314110520640200140c010b07801000442c2c20100184861000c04c401c0501d007414100555003555416a2142400640058108240140303d4405141c441300400c0c1c0020340c068890b8010300b0810a8000c4000780e0340e000940d4030070980500b003e5081d45240165502441c40281025503d9130001d208482c08a4280d4400d2a125403000c02c900059038801c00c480c00c01c90326100c0400d060400ba9a040c48096413000a0003104040100400410034142010110344c08220038022410640544605001d01070010018025903490206450311070050940d4000c81980c64030002d00c04a03159400030080e14400a00351050540c080003402c1640c4064a46030220098103004581611040340c8150f2000c46c02148441c03649889507440c28035052440059061001d43c1d00015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 357954919 1250 357953669 357953707
    0x30c15030a1805063408010905090312010f0603060b043602070c0906050a060c0609061b1d060304031b020103060512060a0b030f0607030509070e070509040b0a06091208 74
    0x140b00044c0518182d05c2e4030010705c942d603c000091548020640a43c8028101000c10f005007004242ca03140090ba2042c0104184c2c1c0c2407008000d20800f0650b5078070030410070a1542d00401d80064100b140201d50444400100d80840b0a4802e04074052001032a40920311940300b26450380c0c5507541d6859042540340c3d800604242070042c48c50402540c6400d603081c00f140c0041e80018000c02a000c0d00704034140d040003000f002c0e503401140201d100500c600d0405d00500ca42104800c0700200d003451300d049103a100e0070744044900000064409c440380002000081d01084600400249141d80c91381c082c60160340c0410442481811b000c11500d0300d440014019140342d03580100180d000c201003003904490b41c0a0346a031924290094845019420b0107680c031020000c021005040c0c48502054282e203040041500410103680140d02c181805440204207500c10003d4030301ca1400c107010142d4902e45a42c104c0121005510740d42030042c581144000c203149011030a8800f00003d010103c09040b01c04103035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 357956169 1250 357954919 357954931
    0x1e0d080a080709050a15030207060b030a1a06010c0b0601200f010903080109051512070509070305010311032d0120070b070305040c051329030c15030a180506 69
    0x11100389030401000300304034200e9100c1031092402102c2042440e028000e039001c2480a4071f40580c3c2c80a041c103000000c0d0010301140c0e90148200c1d003c01c0180b100d00c45030540e1840001d40c2c41186a1949401110030403080b9002901401041001c94129806003c500c00d482d410070358102d00f100448404641400e41144242c84d00344d4480d603c0d0010107a0100f011409031001c100301700514107049120551080c0301011041c0035850003050500035100c03c100c00001418000d08003010352400300e0005002c0d21081c40100c4141c00c482d03600b42118580410641e200138114440d040030400502801992512215034480d09550b07120300001c064181c0103222400a0003045c20581e40f010b03d460501c00e1598003c00304002c2600d400d091000082c10280c07124210350044036488030758100c1024050043c072860203800c4c0c401c0c9404104800401d02058202a1480102e094441121081052000301d881510521400442c20000103840c0b042d00d0780440c1e071001003101c0042500000d40c1e101ca207881026100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 357957419 1250 357956169 357956177
    0x9020a12060303120f021303030e130903210207050a081b03070503181509040527011406150405040515120102040503060a06272903010e0c1e0d080a 65
    0x1500c1c410000a014030000c00185d400210b1030180d017148080103a003006e0000800304041300d100f20f11283e540428104603d03400c4902000a5411498040c0044240b0303440180100b2148204010300d0b0410b00c283e0b1480d83d01301d00a042d0034a069030311960035038400480a5a410402000f548140c0410006400705600c1400150742c0d0388802c0385a043c0315505010180e1048180780348550240b61b820094501a0034281c90100d4113440304040c070a003003085600c000d0320419594444140e881015000758400c044403c0c03244845407542c0c424040080d120f1404a00e41d00c03030400c010085414154402d6038048050408400344103906000140c00b1a007071030400041d40c0d00032070f062226180900c08650010713032040742001003d282c000503442c0da00d04003200130001c035803985625203c08100d80042c402c1480c40c620700c130000d49003038400080705004558541c0c0203603e448060000e4250014071450610b000500e03604040c2c0c0c00b07000d269034421780c4031920b2350001c09018810000540c1080608175410309900c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 357958669 1250 357957419 357957437
    0x13060201090c08010e030403080307090e091b010e240d020307080403080907030c030605060a0503030a03020a080c070f12210c0e040912140408070b0403020a080105040c09020a12060303 81
    0x400c10000b4440c0d400c080c80503450041c158103444400000c950440e40e020002a450366100e440171754054826603c504c1c440c1c1006030410988100105468245480172550b88465203041c00044640c03084400f045a003008400510801103656000c02001c1103040400c00c514144005900505036041a101507011640300000d000425070000d220642c0a800c0700000c01c0d0107891034481c414116600d100203070010380c0d100c010a850780c60340800d01d0041d19001c0c040f2641c421980c01c008000358001d0038040000b03442c030030100310303100609402c44031801d401041d2001d80143d207480341120661203286000c20b104c0810303000c124000400c0000c400f001d0740c1580020740c000314681e01801500241c003125105615000a01000600c901d811701c951006038a88031030014240490715840d8441c42d001240148640c500008845a61000a0041d24800e13540d070b200803603072040100c0c01d03580305a030010044060700100b841403107440d80c050100d25101780b508880c110714075694002140c030183c00a40009860300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 357959919 1250 357958669 357958673
    0xc210d0e0a0602010e100902210d09060801050f12071e0906092318070906090b0604030f0312060302040c030f0515030c090405120a050a0e1f141306020109 68
    0x706944000d000d240003c0c016000d01240d65a214940401c0309604c45035100c0c442401e540700c184000e2001d04914084024120180384210780c1d6204014035000040c2c0c00410101d162440b801c401c604a807005440c001c4002c00180070001140414a08010644950304001030520700011411900340304400c0310680701402c00c00d4040a45441d500100344842c10040726520901010390805d01d40d034075188904015071158071403152218051400308060b4450701c00d002c100c2c4a00c3d0f90040c0125500c5100800000c00801c041c003804e80142d1001504210b403020b5100c000c2030107850122402d07800c01d01c00190765a16640040c3c00c85850f80180030009681d800d64007500c0f501032180c02e421800042c01e00c09a03014140000c0d907110021982140101000d8008c0b4041040400c031030041403501c030790119210151140700500d01e400043c2d0340c8000520340e042040c41803c0101c0a40e2007490030784043c41500e21420001d40c0c81c89204001ea03e07008100700324600c0340041c4000c04401a02e02c0381c0c00828003e2883c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 357961169 1250 357959919 357959929
    0xc44150307030602070209010f0303120504140111090913030504180f0606050d1118040b210a0302070608070909020304020a1a070218070203030f090c0901260d020c210d0e 75
    0x581020b027100c3c4501d04207001080d08903800c1c0d550007c00c201c0c00300d890794482c43c09800e41030350955580c0196090030030026041c0f090170b0140c241c0070000e81e002d400310b940381400400c5440f1000400b5000c204200414840315140404c11202c01940000100c0d0030004002100c0c2142c00b154050000a0b50200d9a44000c03d401c1c0514000c3d8003c14900904110f846518482c1107030f104030a5600c1030307689548403480d6031900d0328886804a1400d01100183e240460701540b64040e003c0200c00600410a01084250164014a0003007000740d550a03081420000c48200035400a0400c0e0f07840311780003100048050403000082c0c00c00c99550070072a03d0311201d1051080c00d00c0001e80000505114008000e4141d44c0001034980c4803c09072052841519040d0500303092010101035160411680000070814180e8208040115040d61145113050b86041d402191128800c1c3c0f84000140c1048000402a20388482d83c1c000003403101da42500f010705041c800320300d444441c10f1044046220044600164682 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 357962419 1250 357961169 357961171
    0xd0314030a0504050c0d080901120f1104030302060903251b1e051f03021c06030b0712181101051209010b0406080a030e010507080d0c44150307030602070209 69
    0x1600d0076043c6e41201d40d141000c40c0540b891036410004411005034003045541c02100300c8a00c5c3c50400c028070204480510b05d903500c540015009841014046100c5020010490701d89801d0490914a40a403021005040c1000082c09540c4d8079003100410340015040303081c0000512280180a00c9088141581c1e1410502980050f01c44c0044001b1800ca10302c4200b682d0481c01002d00d401a96a0040005042020040703442c10345164a00000482081915450a4014003040d260384001c0a20120000d06a4407801c24403038903144503c1c4542c0c00681d142d45e016034007040505009040011009071290501c508407080e040700e030346031645030255080a12540b0054001d443c007900300418192406040500c1000d0558100280040c80405210a21094514840340c00743c0070f01441d0742d9504000d000540013090039107010b40b88085000002500220f140207601c540403291401803600010070840e500052002c800d413819415a410b4941d0103114040c0918801e0000580f41c0049005001078060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 357963669 1250 357962419 357962443
    0x4020a09061b08071103071703120a0614100e0409030806120601060512090a0605090606090f071b020a030b0910050f010e0103080d060305010c030f0b1e0d0314030a050405 75
    0x4486844400400d01e10070848140b00d42040c10141700041c2540400e1402c481c60388940d5003059450044800064048010503404a1420070030303016444610041d400c03205da80c03007941100c6050b0080010a411308005030005143c10781410421040300e2004102030310f4104c0750880001e40400708008440c43c240c517104041d103d050307000741703011340c10400e0207000d91141c40c01d407104240c0100000382c1c12220030011508050340c06802480395003821010195505001e0703071650b1240c549180080c035000f2000768018400c00311641d42c2240c80c0580030b400c2840340d90a00e0241c0e0000281e002c0032001c180c040c000b02c0d010b18121002404415280f1441d202141d0015040c02c40e1005020300421443e17101100c5241500e81241449642c0ea2101c0703030840c001c01742e42d400107109508003607842d4180d0750182c1c8860008802020140140302c00703901000b4401c00f07480031000c00d42001e101c00307890900700406440d10341440380c2480340f54041c00d03001c114207581084a081806075110300c100000c2010600c1008041c00f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 357964919 1250 357963669 357963707
    0x1e09010f0f0902240903070311032401050f0f0405090303090f0604020f060f0d0c050927150d080f130611060a02180a0305240c0906070c0504020a0906 66
    0x1034210f40c00180c503904100c103000000f1003804d00ca0300003418501c080384c000c203000608548000343c2c0c034501200034101c0b03030160f648203001e118030801b002405110f43c21701920508180e002141c0c28101040648602109a9074111003c5881607040c0d0b00c861051500803031103000155240c0c500346410034a0281d103002441c1c69034100006003c0140c603140c070a40d4251038202c540c10740700d40c4181d0107100a40a16a8452a0682003280205205410a00a105c1c994059074594039107008102c0d400c112100c150700300441e0000a10010790b45901c981454004550010568102e503480354846083ca504a283d4041c556000094010008825444000010080303401c04085151680d804152525001060082d14030b4000400409604c4100c03402031184078010101140151603082c011368a1101e00380076001100e811a0075052822584803507481962840c45040c80e0003a080207100c800d07001918111011140320718040744554581c0050180d12000766154079050313103001030040c0b5074604400010910 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 357966169 1250 357964919 357964931
    0x7212a0b011d01090b0f03010f0b01080108240402150a03150e010501050304030c0201020f0d020a0c0b09031c14070f06060b030c0706150b030c040609060206060a05091e09010f0f 78
    0x9080e00d88042c1e0440315144d030700280901c0500007113a240740a004107158594a4065154001c00c41540804a10b60b002c0c1c1c5c079107029a881d11131090b5124401e4080400d543c0c082000071250b5003086180a60152018007100000d070041c00182000c2c0e004000044082074071100038440700080022040c0050010341c028854652420b00040d020303100240c00a0200171110200380196402007080b00b80ba2004a0107d901e501a400700007501c40d07441040403512114281400030380007200605031405410010080d05075140c41260203c807515030310083c4010b01c00108440128205400068502c40e80a9081100c2d510305502e440e200700c075020b4101c0c08200b0006d10502c616081098242c402c00c039400400003030903542058050030143d026500244004500008000c451110704010b0f00445800303407244c80c411911203400340d89030382c2d0031111a90850864002045545040307a0001e030403d2100046050a03045502c4171b12000b40f0841c0c1601907617440300e04c41103207520507100c1c2120700003200c0c0e010486 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 357967419 1250 357966169 357966209
    0x8060a06060801030b040c03080406090503102318011a13050708060d02130903020f1606020c01050d1b0e1e060906031801050405150c07212a0b01 64
    0x1c10b44180405400b189507180050200084aa00040039580002d51f164403140c0c0c8603001000300e107460080b41e0090040d243c2c1c04403088414050b000d80c1e03010896414a0088810b400300150110007480304904580c0d4903134081c2d600c0800c0c0b1486400d01c00c06241d40060100300d90501c000d10080302403440b0200d180c9400c00c1146544003030b8841d000103040750171100d00c05280c000031764a40b4030040c0c0740e01150300c0e24000d1000c05030001804220201004140c0340116000c503000b20800180d4400d420260700110600001d561042e402087c82a5002d000052011504540070040c1e11040311010003103441c10100966920709080030140c84200403000704010848603011540c140541d1040c940119800f20111b11081b00480150110780a407000802152900d070800c960340e48005000d45200481074404544406188030446030700d40e4115485a44601d861141d400d0700398500c405500400c02c81001d41c101200e441824600c0440c6c003c5901c02c0b0703555841c18414440f050681c07140100c08058456080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 357968669 1250 357967419 357967427
    0x24219050306032401210807080f0d0c020a02130606020a020d020d0506070c1208060d0b100b04120605130f1101181d15060702091003060c02030408060a0606 69
    0x1800405034a8001d4998550001007031030722101310122060503040100e02d412001401c082d03603048a8185400c41802105d0001c0554036400340000546200070030000c034408204035a0080c61441c60300961f045c0340c0350a80c400e400c1202c1d0707034a8032103005801c081740c08425441d02c0c803403528110f02034100402046203000c401035650002044002e00450210003498190354844010401264221041d21040e1038a550300a22495401d002192910781c42c03001d0349030403481804164030401014116100112840d214101c0070f41004015107007203071000d440400c070a940d01015000401e50050307020000501ca1031312001303642d40101a0003c0c0400c00c020207000c01c403804000700b06030350480d1150301c900850800403100e40d46002e103e501016907070303540081d0851026861903224860398040828175214084040c94802c50420300316070000382446000094613219841c00c1c0c0101c425a000c1a00d80e640c0c3d13845006486482d4031140240e080403070100b00150041c8a80f683c000c0405100f0807250f82880c42c060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 357969919 1250 357968669 357968707
    0x30601050d11060c0105100807060201180605191b02010605090c0304030f05040b190e0108100b0a0e0904050c030f0f030d0f0b0307141e0f010c0242 65
    0x2410344a582c2c44000c12039150041142d9070407000e0b200910203841d15400800070382001e4858030300c840c07149240011341d03548107201d04146240540c10f07941201107951140800360101605a03001d5017105d2607080d15122452140b0103140d289800c0d00300010502e4030b0081e007162520380c8110700900c1c24404000c0328020381e4049a92207a41420202100300b8000001c0b2a180202d0700301c40e0b5841130000369403084522140940e001d040d2a6034503003032054161401180d4000061740e1582d411b040c8800c1c2404400d02c0d4001804042c10213103002c248a03941d0754001541d01400362004d64050b08186040307265030400744007100c0030200300320060586101c3d15035200c1d40da00c00c004e1070194441e524203024408890350f070080703121954020115040c040d10396008082d401c0c1c0384400113100d0080c1e40f20501352407100041034000f281000742542da4070026200103442621031210101d074018481000c000f10710b0f00d8014a45140001e842103401d101c441494490b95016480740c00544007142848034031807822840d0780341c4d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 357971169 1250 357969919 357969923
    0x3050a03030e1005190f150515220801050906010608040b22030206090f0c0a0902030703090f0803010518040203061611030403030810120312020304030e0a080c0906030601050d 77
    0x60140e45002c6143c10641d425400c0090f00c0e00b800140142190003100c20301c180b14094034100083d005000880c0c086848000c005401c44050502c02c01c46840c043c0b503109050300d40400c800740b0b03180a1a4007512010720603c1003132400c080441043c44014005d20a6903801400b0b040100a594101400a4107044004000800c00d0200400103401002c888100f5030341c07943c01e2003013900a020346103406501c800d0f049803002c542e4498041c0d144007250000810003410b08000d800c2c134902c20306101c40600690720052083d001e0688076081100000d090150400801d4000c0030425101c0d414a010070034054617070b001420130b42c0c1c510014800541c3e80815001d401c00102443c00040c400c1580040c0d5140070200344043c0c0c280000b040000c18540c201c4140b500c283d40ba07107440c075107464170341103804003400f81e06070013900041302118194641e05880c1d0045400c1400b03401d000c071084403800001001c0504542120345282c0000076040620f08090031100d4111a04502400040d8113027130202c2c105490751400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 357972419 1250 357971169 357971171
    0x140405250e0402040b040204080c030c191802090604062003030c0f1b10020705070503191205190314070806130f020d0c0201060503120705030406121407020c0a080703050a0303 77
    0x1c0b50856460358081481c034000588159291562022510344841c01000210301a0190312182f49240c1341035202d81d0b00c0030114801603a10903042c00c00c100c045043c6203141440b803580c03c200a81065032100701400050079a0b5032010154101110b5180200140300d915500540c410300600441c1244902910107580c0c4c02e048194840d000ca080032940280b400d00000d00368003c4001c00c1060504c5034005007400ca0040e021500102d40d04d00606a540807100114801489142c40307000000e010031940c3e88140c0e00a00d480e60600c4100e01404d42a000030201002c003003540c900240c0c02e0001e60001141d48032405041c0403295142620100b5803608600d0444842c02c1c2e511280e0b080c95403100e6060f00e100e02c1d40000304018811403140e02034001c00b03030b1b400380034446d1280e070080007800c40e1000103c89680d64004003450901c0d1074044151b991300f024800441c241c98450b00309401d0018a80e030420310480780781e0f00500c408601d00041c0280e140b6282c1040b541600070040130310108400061004110341e02d4030f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 357973669 1250 357972419 357972421
    0xe060306040609020d1b05041a060702040903020f1203041703040f1b03080f03011d0c0403060507110609070f0503032514100c030b0105121315140405250e 68
    0x800100041c48104009017800014054041c200340c0c511100d1050f0340c000c3d101002009e03000003030b590415039104545a4051410060200182025042441924801c1c011112a44440351280d0b00b0403101800707010701c5100100c100010300050044082c0001000040f6918608013519582601a1408400341003ca01d840c0500e1910301071850031002103800c400040d8a40011090f8483d50340c0c000e01c50040051110544c09034041c11440b00300740516604410545400d2070340d982e001c09840c0043c842d400744480010403000b0200705000d160310036420070000e44030403404d15180100201d2582c014900a0b442032100103814050f44030039403203095080c90003075010304032440c0a601002c0304548003c014000d0f010758600380c0842d80c012003a040a0f9440c00d11006840500440710b9000e50185500888481d02c00700b44500c1c02030792000100b070301500341c20f06465524500e0300e0544544414a00310711202604110511600f0301000800c11b050140744c00b03e05004040e50060901c076405260100c181c910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 357974919 1250 357973669 357973673
    0x7061406010c11042a02071707210203010b04020313021008092503020301020a092d03030503090f030a0c0308010510090b18040c03062309160201061a03040302070e060306040609 78
    0x158680140d070f070305e4060f076030302401c2d84007000303441d0700844c840c0340d19241d900b40599030700030f0740880c1440564906001c01100300e4820142c20240c0f4403c8401030703805541c3e40081d00c50584440c00154422030703110300389002002c1c541c414011071101c0d80019900f0011040d00b80916010045a1554035680c0b04810780c050100c5002700d1003210744281e00003545984000360003000143c000c03100c2c1c03040780c02070388000c2900c2c0d800801800040c0b86038801c00c442034000180138030019000d2005150010504412a1524115030100e503203582c1c40708010708046101c00000038101070f400803403107001d0002642c40b05d410341005600a0409031481c0516003d0100104030030a8881c03801ca0607001821001b0401e022a44503000003a00404250062225031040c01c8030b07600380e403105440d05203070207000a81034046641c0c9481c0003203000d44852003020110354985c20700069020300d900321800240c40c030002080d56030800380b90281ca0545949d00c03907090301c64143c040204960380440d80b036a0094111002094070031541c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 357976169 1250 357974919 357974951
    0x1e02120a113c01020a02030a05030c1e03011403150402040c050717030708011409040b1902040306020a020d08010819030507060c0801090c0c0203120904020f07061406010c1104 77
    0x940a407210007810141420110080a90581c2da01125000c1c600107070015103401c5082c1d11800180001592080003c040981d10074401190f2144a4078641c50401481c12403030743c0400310103120b0344980704001c030040c0300f02c110f00e002407d0004011401071103010301c095441e540e1500c00802c042c2c0318aa80e07030590489240140304803207840f580018081e6010340c0220004516400540d60341000503001c0c0004522040c190803240c51030480201803521981c0d0b150b44036181074000030b102242a442d0782132000c18102c1c2034005070010710b204450150b00d480000c60000d240501180c6100c08119100004029007000401d05800d00c0c030502c02d03209400d40c80c5081c252058801c40c81e0080502d4500703007070403401c0340d40034114905031106144c1c24050300d0300e200c03030031a1380e44440b0700c0c06545900540303081011550400000c0201000250003d420b0016100681103160010002500d58a0300c880207070b0a81c81c1c2e0850f000d5802003090801001039583c039146d00e05c29024840071a405660354900d4446c0043c04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 357977419 1250 357976169 357976183
    0x2180306040c0801060e0603100f111305040c17011202030321070906030c02031606091a040308010b070c0509070c02030f030405030f0d08130f121e02120a11 69
    0xa000ca54490510780382ca0004403038284658051035190460105850480022480c041c105c024002c0811391a0784844c0b00082c42d144034101030007669134140c1c0800c010008090080f0043c007d41e00c403d03c6181000740425502c0b030110000030016240081920901c1c0c010045041d5240f850002045081610110349144211004000c2c4041d03918100b120100150441c20310424072136465030759091380c0b0718050b07098490a803d54005a0010700c480a092800104001c49680c083c06003c1904482078464180a07003400100d01701c1e0311461010030003810b81101025005260100a546c54160780e900c550341000001e025861098031130700080b0b038465202e8a002c51900f600201503696940800140c250750b5401841350500a0040d6000c00b440b2807404221703100e5007a0b00d81c4410700305070740e80d11440c1124045101c0031103107041d2140b41d00f03004c1501103284620144541e00c800c00f011100b800d08070a400f5107095020304661280c0711032030f00d0341d0f1a48e050710488641e50a103a403607500200442420059 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 357978669 1250 357977419 357977467
    0x6020312090c090115021c020c010f0915020c0901170604080a05210a0f02041d0402130614041404110616061406040e07030c1a0d020a02010902040b030109031202 71
    0xb0314400017050010380304c9032603890f02007075800f2a440003096500821208006c1c800540c0580c01249001046502400d940794043c0d001d4502001c2c1e443d10b84000896005225810700c0c01648898042e0040d030810580550141c4480ca01001600004441490340c82600810041803c040411140606801541920301e83c00da0340c00c1c4546550040d08040c400e010088905450307060500648065842040c4211030580304040c04600b25564141e201000c40c0d80003800480c1c10200d01c0340c2c030700c0135000d451041c48090602c82e8560000710301100208000da461704411401150340c5007052000040b4061044a000b4900743d461070346417070752020100c1e600395800d0b00c064951410980291005090580d00d284195411030741000709802086244d07507501260300006100c83d0703441c0801c3c00f642580840401d407540503242047e150845d14010001a41c2000348a580981e440340709810031480d05001c0d585405806600802403070609171401001b15000c4204941c145900103040d07840c0202c002000002c90f5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 357979919 1250 357978669 357978679
    0x718020d290102120f0702101701121506060203090405040c0518010f08060106080c0f07060905160e06010f0e06040b0a081503060c090613050312040305010b0a06020312090c 76
    0x22100301c01600300032902603000740140200101c003680850504162100032142603000c07410002d1603800e001c8589403d42c030741000c0c88442d44000d00000c0f00960a540a01403107030401081030920310344040c101070111000c192135030602c0810312660342c0c00416625800b81c1298081500e07100d6043c00090160146c2006401c507413440070008900281e440310310304841c1080742c079010481c0d40b042c048e40c903050213004210010702003901040040c000400608400c60100c41c03114544825650790f04112024000121504d810507003a01c206500000707514801030060707030452000c910341000000c0100c032410f000c0600f070111142682a05480f00c1c01514045c11a121285613641c3c03070404003401203c406c031010064507030101c1e5040e5141c207002c10740364042c020715013410741014044030400843d41c1148404040d8420141000078980c0e60402528811259580b80c8680c0ca03821405d04600791b03940050490f009900525003000010350002c110364004142210f14101929910140303400d20018040495000b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 357981169 1250 357979919 357979961
    0xd0b241002010209150c0c13020904050f0106020606010215160c05060109021c0b010914190b2208070501080907090c09180b09040605091207230718020d 67
    0xa405500510340100d0494100c05048405c45070821a403103018103a08050b0000700d06484141810341000d5400413003e00e004d0f04004082c0085402c441c0100e60640007c0807500040081c16010b005454200800788007802d88512840c10280000201800a03d900040c200440701e07898031031030b200c90300c0b00e51000c2924040d503920607400010350882040300e5481c1c0d00750701a0042070f282c84e10480010b8981a19290072503443c115880490001c8910f80c260000071901e40281c0f20703000c11200f02c0150102064090f12201a8040402812203440b000d140100d143d090511100398002000b03402c4031b00900e0b05900b0b640e500c1104a08142e0241e010031b65581c1015420f00086810003110010b4803030b103201801d0505101c8410030181d0f800011742e140c1042d00100481d0110b00796410069101c801e82f421640d480c1d024601c6d85d445603016100c02e4481c2c3c400740d1000360120076108142c400c011043c1009041d00c07403c1000c24082d9000d0b0043c03403000035500203120078070002c0302c2d0421401d11505100c40d05907 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 357982419 1250 357981169 357981199
    0x120a110d05150f100807090f090f03080f0604020f070b06030a0c0303090e34050f070606092d0905070b0d020d0509160618121208060d0b24 61
    0x700c10b0169000300a540b06280002c03081c000c1310700381c54100c8280500078440e071813070007040000401903450100320766603c504620000c1200c0101300002127200c2d9441d0361080c5404428040d1040026140c0d5101e64010400c60790011100d0060360041d40e003001c6150340b039403500e50000780f4010081c0e6008007441c1801500006040d08020341d081243d0740c4080700c2040d0fa989865404200c000c00800241100c4034001071304102900351000d440840707031801d1851a120915640c1c2910ba045200c04603030706e645600c01486a0201e034040e8031903c01c02d04000c1c0c0b2800e18500c5500810464640790841025a540c213604d080c040d08010140c01040d0000d541c590b40d164a840200113540151075040c01641844081804070070002100707801c442d04140010952810903000722894001d46044241403000781c1404251040441001f1a4080c842ca600c0207000c1c032050806040170000824191007245400e9440010410701c5c1c9046501804010407580c001079043d0103203c3d10005081030503003000302c0d40c0c60408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 357983669 1250 357982419 357982453
    0x50a02070b16020f06060108040b0a290f040c0c0f050a080327070521010e1603050f0601060801050906010c0605070201020a02070b0702101110020c0303010f05120a110d05 75
    0x110222141c0c2138918001c09442e010f81c2c0c6100039501c2c18009000c2e00300007404980060001500321121480115250a441502c4001501450041004160901d03480101440c000048039412031080e070301400503a807800d002030100c030f80c241805808024401704500801c007046c0300469a00b41d000c03d04a0301d9007000b0326a250418180c0002d052a01848071a00032140c1d000a0090100c1e440180021203100d240c0c0c41099810380c1c0d042194807199265140b11201003002d021800d83c504d000c14517040c0c01460b500748a0300d8111b0030129000741d60080b2005101055010070898107544e0182c413005400d48412004031100400d60101804c1c41d454070342804038003a410740003058078102c140e007202c80c020b03141d1810070700354428810b0095121050032030400c0d505008405600400403840c0035611560360f18000c1c0c0060360300c91140903007560070000050160a1805c0c10500140009507011403011150070300903075450700c828001038954413041d10000301e1995941d042e003040302d80c080240d4400e103035510a440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 357984919 1250 357983669 357983701
    0x2010522050a0c0801090b090c130c090e01081006060f0e061b030307110c010f080604050604060b2206050301060f0e060d020c0a1721091e2a030c0103050a02070b 71
    0x483c50580745001c12380f11080041c03c45401d05006101e03603c01e065089003d030050038440e103240184003000303000250f02900006418001d110034070180c06140860b45428048481c40d401407018410084a41c00300f00394041e41ea03504050381a9011956a031551480d03103140c0080301e00b44000f6201c00010054000d1340040c04002c0c0761000e030100c90703419003142d0041d00c0d0310710900c0e421400a06594001003240c41c0c9900956040240034000107038494680c2e00080e51940a03000c400c0941000741c004017207040c01002c1610060800d8603005082d13504088000301403e414103070210030400c503d1501c0b80103542c0c0030116480f80240a00c1107554a1059a0a50f2246040c0700243e44d4058950100320317050314105c04a032003102e00c40c030541c4003071210101a042c0210000c0c2c5403440e01e20682c81c4280308003210107041060040a078000b8918200b10f6146036414109540403524035415038104c0380c2d00c42c0c40c00038000701400024200442c040e80c130194000003c2c0104000900810981801d10400605035400c0f4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 357986169 1250 357984919 357984923
    0xf08091f0c0302150c0904021602030d0f0807030c0f11070b0a11060a020f0318120f03010503160b0a030e0c1e030d0305040c030803060f0409030906020d02010522050a0c080109 77
    0x19078040d40b64820981a070004c100d40120010004200b9101249040e034000d04142c3c17241043c1480c468416000729103081406000d4a010401c0d20039540c1045402c80d0a451384100e25103020301003403e5904d80103211001500b0301c03006020700441484010384050001d84090050031881e262a504c0d2240001e142040c0b01103e40034500030034020509004c154022104d041d130840f0350340e40c550348030107600900d0104000b040e4101402068a41442000b1034001420051049010700703499505044c2003504144180106030203e82c56100c00700220040c80f000e0381d100307901608000501306003e0311218201403c203035050f82c0c008940161a442a41c490030f002c00c10801c2541150f030308030540c0c60f0030b50031540c040d1000307404421010401c000081e4034100540d0b1008001d401075a038150018040743c20303151151401c60100b2020f0000f4041554104584a0304004a01c003d000500b401c6001c040ca140c1d032a0001080708001d541034000303214040002c4650294085410044a90307030b50450b9008141c00401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 357987419 1250 357986169 357986173
    0x7051b0d11070806040f0201021507090e0601020105070c031d0303070f0302062415070605040b011401020a021c08041205060709151d0f040207080c12070f08091f0c0302 74
    0x9406840240025900152a043d0000300001d07240c035156039102d2407036038004904503c91b00300100b84003030707140713004c1806000d40c2d840d884241d0781003c0c2c0d800000030000b44054110380c900010802d1076544102d5a500641d01818030103000d000716111010030b000b660700c4441c1c262100103600303410082c15088040c482c03406a42030307881c0c40d150503001071846001407401c002c01c141050b6030b0404518014135011403594130f81d030000303203401055075900d0140c52040340c061340d240190500400c03500c011200c0043c0c01807000d10150006658690010b034840b05068000c450320007400040b0410071042d803040b50050103402c0c8625081c28200e18000342ea0302d034100d44040c0061908140000c40c184001c95945418440b62100c007440315076a064140f00c54000e0a8050b88104424120184d07512903100401407035000d005021358070348540321410300e00645412203501c1c40000704138403404140e141c0580c2c03c8680e8400d082c039551740b601d01c3c0015115844100c050100c15070074012880c00c00d8004401c1d0320341600ca502 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 357988669 1250 357987419 357987437
    0xd1d06070207030827130c11010606090b1e13090b0a0b2b02040b040e06060304050a0b04062304020f010320070201030f0212071101050403020c040507051b0d 69
    0x801281c0b9a061480018020202800128908040c6501c2013108404910019907140701c91800100c10a0340c0c1c0f101c4010712981da0051914403039000800d01c01220040000303100e95440c045006004541034810110162400716500203004411000e80d4107050b007e07149039495081c1c514801041c2d0443d8421012501d2510700381000c5800c01c6040842120900ba402c581080c650407448060550f801c03100802e0203000640d482c0d082d04003480a04081d007070210030940c03507034249014000d40100c082c100d107108000a02c1080001540050610311059104606920342c1d2910318044010305800c0b141c9411400f405841106500c1b00c1c1c0030f84034841c5000300d0f500c00d1992100b50040d000c0b18030907880390400a104a000400b0101e2510050a041e40b040c503000a03007070304400300c2c003081360041e030b1701d030305d021840300b0300348142c80d40e000c6640d000c10303842c42c402003209040c0765a006c1e54410300360729058040c545900000e40c1c0c42d40100d0644544107400607580d2064140400c000f9214042952401e0200e05001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 357989919 1250 357988669 357988681
    0xf1302030609010f060e0103180c0905101205030d0908040320150a0c020111030405180105041d1f090516060206130f0803040503041a0405030111070203060a0f020d1d06 74
    0x4102d404c11103041c0d4640300c0a117600360004502500c40c19101d00540c0c00071000c0d0340002400d01d4003280003002c4030500004c44d4100a81c2e4074403440000c0c0d102888202e038429100c400b0036004401c0f01d800054039040015035041c03034504802a40201d5001900c3c8001403184001c801031a1b02d81c07601d555401701e03074107900c168103c5100c00190040b00020f5000450040400c8015401412001300241e81d640c02c89090554031400a95080d00f50040b4003e840b809100400c010304250050040100f5101200d800d105245054582d441c601e8080920803000300304156403070381e1001e5000c4449140c21901b6030302c12000441d00c0445000702441504014419480010003141030b0f0084d00e94281e0307220140007202aa291078800094101034800e81b828001044001905d19503000011414000e000c02030351154600403c0500b128403002103000720b40c3d42004110016640840c0c0c1c0c2d070b804080c04400040c94422071682000901692040300e1004e80350010000105030030002c040c01840d80c0d1000c44407196254 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 357991169 1250 357989919 357989939
    0x9080304091a0114070605060301021b1b03070806070302031b04080d0e010504120f17030f041109070905040203040f0b0a0b1302130506030901020c0703031e08060f0d020f130203060901 81
    0x5a05200509502030145000140c1d40747c03ca142c04c101d00800160801f411000c1500418804500700f45c92503000344150320300c4000000005004400c110098a1554a080c010603199038000f0800000c060307000000607040c4039a58001a16001d00555040e1070b80d8840a55665902c11140e4035000f003040c0c1400c84006610031011034007501c254030b04682c84000d0307035501c010a06000d844216101d0040b142c0000d145400003010754410801c0c400c03c84421f00389810310f4000441c84a44407400740094408202c401070308451101d048400036500140c0d01da440b070428000030031910340000d050340340c89401c0c851503007900d40225030b5040d42102c0300041c6080e400c189130228483c074694a0611400c0042c100b015183c00c0000d1a44000c0400002d450312105192150401420360021800314034440303050300703080c4c10340080e01715281c2c1207042150380c03400e00100140b4043c4d580503509116034101c0401c0070854681516140030020044d040300511840f80c102c000180d0000c4800b00c0c010080600002111428 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 357992419 1250 357991169 357991187
    0x803070c05100e07060e0406030b2a0a020a0b190501081b040612020d1a0c0711011706190f080d0f09030803130c17010c080714160309080304091a01 65
    0xb420f402041014a820b00550300504440318456205595010001c045022a00c0c810720954020041d8850000e4138203c0b030311031002824040081c9003060160518964000500f841c4180d00820005450394071000c60080b10700d12000c0d07110740361341020000140d0340700c0001d030281940303405d20030190001c00703400c00d00c82110260700c22900b09180325440c0c0005402c00c41440710703d141c003a20540702e000d201480b4590b01042c1c15640c0ea0710354640011042c0c02d02412000105590609113090079004e94030048064076440d0113031585114201244034855020b0030001c0c060300070014080c140003845d80c0e1381740b4a030716034054100d0000480c854841800303010744203c5101c0107481d8031842c81030664441040d40b030410b1021341c000b121180b00c4c1040102c1d010000320070309121b580128001152070941d07014010550640600040305001400b1403031180d0050b440c0541d903c002d8400380040c00016241030880c1d4540d01540205200d000014001c5216040341e048440c81d0b401a03080141d072200060011201d90103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 357993669 1250 357992419 357992441
    0x30703090e070203070f030809010b0d081806160506010f0605030702030d24090f0e030405030322050d050601080616080114221509050411010c030c0803070c0510 71
    0xa84600144801c12101d20610707084000c0348101c0341450015130b1250400c264801044e030208920a0030411012800d0041c034001d014240c0c0c5020140c1d0050f6580d0f00503008806280d000501e441d0000740240d1548000d550f00440190a640c3c1000070354208544c0380c0340207000350390f1614401a4041105030180089900841483d40118500300035044c82c42e00610b00302d00b80311026044e1000d8400c1d4502d64040d02c0000d08031160b000280c42100142c1c1a007161807015040c0e110381c1092000700043e94010041d15040194002103000c005441c0c40410100583c40c2c0010340d00040c42e010503018020001350b2503040c0c6e94900c0481d02e03070380c036030701801c000300300d69a402c00c03000501c000014018800c10419655003880c002d010000c0c402d440329a2000c00c82c8410f10701c00c2080780d0719100000175290385040d080051903409010801c6060a455141400710038048460603c0388209501d000c1600c5500441c01a81d00442101d843c1d00300401e006102c0048a08240e84c40c2c8207604000c8003240c264800e0b80420b407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 357994919 1250 357993669 357993677
    0x3110903190c0f0e0f28090309030609121805100c140d050a0e0105030603030d0b060c06040f030f030b090f1803041403010e070f03080310050d0605040501050702030703 74
    0xc40c035050700314540c52000c0e021120380c4042a800640c0c9203030f414100b000340c130254442c1c103607500d010030601c01444401400c1e81e1814171a0310082803000703200036000c103c80c00c0004000c28007100908081c0e5162040c1d41c00100064030301414402844040307231503945484002c0e0384411100803007404100c2068114000c6680c000042544920700d03a0040ca440300020744175941c681e0400ca14040100e051134500e80300c58010070000201c030300107030307500c0207204018181c2400c000d411401c000c408207549001c2d40c0040c450f000d44d100a900d01c01d503614405d5034100c216071811151286400e00c1c098000e40c0750004214003244a8620050505000e401480e200c10300c054184040c1e1b82c0c503070054487c00c4602a1060040c00c40416061120a800340010000390448400340103501043c4800c1c182100e0384e0150b1b40500b40c2007043c040c0310640d81642d0071403c076504080c50b41d40700d40701c0c0414401c140005501081c0d004244603592020040c45030045c51040740510002c001c0b5564200051307841e8030074aa0010006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 357996169 1250 357994919 357994933
    0x804050f01030e1005060907110c040f020405090c0901140301080d1206090e0c03150906130206160f061401151107030807030207080106060201231902130603110903 72
    0x142401052090203040525010809511842201d82000e141c9000800c0860f02d8030100305041c01c16055294110905207410f2103885480810543c0720302c026144a0f10aa89480740400c0b0005150180c030042c200007404a0401d003804055034460b0743c0000ea403940803480e502d189004200d054002e49040300c03d51400341200a41040040314100088540e000107180e8078600810626018440d07030b100010000d0003000580114010549403003800d440940f412410780d410410120004142035802a01c2410700c0010010a440020294000c7c1c107843d0001104192190050002080e11405d04601442042040009818040d210b0300c03000d014a49290300b02907119200c07144200441c0151048040684001c50385a54800e01c0395130280708242c00507070110350184a0100c1c20b01c1070000a0500d4002041010008150841030f0802c040700b1030601c0d0307091000201c003070042e01c4d80c02e1311180c03403100115a604522040300c0000030081c000c8000091401d65090103206000f011120380c204002c001f0b12030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 357997419 1250 357996169 357996179
    0x30c03080a030f0e030406030b030307030207060807111009031206140112110c010506030f0d170903120405100c0c0f1103030d0e010212090c090705031305070909020109120804 77
    0x541d2041804104040d43d8082e56505040d00f8412511403400c101d000e56a0f42c0d01c1c00d04004c041e10a048480f0340300fa00108070980019400184070012242c0a040900c0950b43c0d080c815201011701c50b54044890240910f60100b60b401c0c2d5024000e030034401c0c2c840d00c03d00d00c1818001170407949240110050b103680400500a150300400cbd00712164801d1013004114000c1d00094030b49590000350300c150083c0c3d15170040c00700c40e18051260891100041000f40000210102c1c000d148001e1145550240710420000c03451041013441106c4006045030028a52803d051038416074420101c0300384125685000291050b542c401d03000b1758031701c54102c003804060245580303442e03030034040318002680d15202c10044d500441203d802084010080c0200040e1100c1040c0340c0070900000050640c000d603001002d400f0b803165205810990800c1441ca001d5860307940b10007101a444c0325440002e003003407041440001b1600441c0c1c005214a600c02ea072458152540d03234200e188445201c8000904104040c0400d2007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 357998669 1250 357997419 357997433
    0x40506060f04020f070b0421080a090f02190312030c05040513022101030b0604060506030414010b031204090c0e010c0b0901020702060403110109080d052209060e0a05010906030c03 79
    0x1c00d003030008100524000355181d0f014075692099904403074102400d1b00300001d03c9580d500c5240036040b01c2e040c0c01d0615000c0440107080400040220a0003580e4160324030a005500040902d15603001d820740846415021010b503d00d01644411039848414010000c615032003400354015035406074840504090030001003092000070540c81d006860340c01d00480c586031140254004070040000510381d400d50460802010540c4e0041409001d541444d00402141c0c587c541107a602a4100c0c2200c001207070403542c224003501c0b40c030104370b40c548600f98a540800d40340c98014405c40380c0d410010030111450a03410394030702501d42d0016000c101200d8121011482c15030829a001d82820f000500e448002d900103445034205400561396044200d110161658102003c080506011001050640701c42500103000f482600c80b5100c4080c0101881c020310411030304120090440c01105000c4a515244000e100380c02c12200ca100b0b007418032000040320421440313048103890f001081c0034a00782c1141c5400d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 357999919 1250 357998669 357998689
    0x20d09030201111501060503180714040e010608100b0307050a0605070308040507120602210103080f0d1811030610050303040905070c02030d0e010e0f03100e03121f0e04050606 77
    0x1d440d5021303050480800c1d4164000c4a400f0703140030307103400c4e4076810030911819008000d1458030340c0742c0d07101c0101070000c10051030282507d90001ca8022070700030712840c02c0307070702429465100008620900c020107a0940440c2c00100e000d18090781211034150750b440401002d103c103480340c500441c60411540700032030b2140c4045603010f406036080364407059840d82c4404055410300030544031158007056003154041c0c1000c40070540c11603035030491000e50443e00c40200610030702c4451515110001500078188026400042030b8441d4400c641580c3e07400da040ca9045100c19041d0248640260300c0052208503040e441d000c03c0d214050000c6041600705000040146000b400e004180b084c091842d50050341e04101405030780c1700568860002101007070025081d48040d486d00b9129031041c0c0400045034400140140d0b00c9401c5150200303072911050032041c00e500c900480c0001186070311082003641811030280300c41c9182c0700b2100d25680c0303039240c0681510240c1901e0041070360b003003527001c00c02c9031030500d89007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 358001169 1250 357999919 357999947
    0x90b040b06010c0c120c06110c040e010b0301060902070c171207021804031d030d0c0615031406011d0906040308060f030a140d03020a080103170d06090209090601020d09030201 77
    0x1083c00505454900130341055a00c2042d0407a910b4100400b000103c1481034010802805e004d12800400e101c459120554008418040c035030740c5101da00052000d4001e07141089000d00204003554a81c0c141c04080e5000c401d054800c1c00080c1d00010b510140301c1c00301c0c02c8291201000d0301c6420a211400c10950744419400d9070720042618007200e60b03444a01c9140c0c0501d01c20384a0900c40103148012844c56118038540d148290401d1240f9050150450b89510840b980260001041400002e01441c510100c0d0400380080c00780f41350401003d04009152030503100c00c00c03214180c28060116140e0845d1040f1401300f01c6400100200380064000c585071500080c00500a02d012607081010915100c01204195052448e40858044480302070019482d40c40440c981940f4001c8280e4001d482120107110080240039500d19902089c003020b02641e05013540654103200e92035607007030b001303019401035a5018429049240415010f40c00010301820a00903a2682c0781180d06c0c540055414141010320 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 358002419 1250 358001169 358001177
    0xe0c010206130f08270405010501120203100905160e0406030206041401090503030a050d1104050d0b070c020d0804060e0a0305060121140d140a0504090902120601030c1701090b040b0601 81
    0x48000100c4c20005000c1103002100e691242d9107030605007203900b104803154a8099031a002c0103105590f07020304111408414071a01696a41385c0c0203030080c05103800c1c0d10900c4407a18010510085220303490b04155281100c0d41d500502c04001c43c02c0008407245880000d600c0302d410001005180000180c1100d108414101210754550b41d9002c00e0030b60f400f48040500240c030016441c24a0a01c905c03401103022400c01526042c60305210200b243c5600d440d07405013480b846440040c9030140f00d00d0751000c000d03501401000c0d054926141130a41c0750424060700c03000c1010701207041151b040080040007281e410000400d1503900e060020382c4c5200300d5401000466510150f5100450301c40440b6900c503100e00302c002c040d4203110100081c11004c500b10094154902000620300c03040d03110044e90191503020b613000603225111310015100e040d41b8501c034001c80c01000c00000038000001e43d0761003201c0300b540760a0242d003452030b260341c22101c90900c0100805105000302e0086110714002683c44441814 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 358003669 1250 358002419 358002443
    0x3050f0103060b060d0f0209120a080a0302220603020a0f02011a010503060f12070e0c030408041e0510020105180307030903260301080a051203070206041b0b04060201020309010e0c01020613 83
    0x8410000e407a400746c02c61812980000c0c040c40780e8184078003c07641d2802d80d00f01404074102d050f540c41e5554464018102c0c20544c000c0340095944600342c0d800328001c00701d01c000b5040165181000303000380d005410020041740002d000d4809050040c011444d1482e09845800d15801400005417100d400c060100c5411103404803002a135511440101449a40c21400524803035150003088001c4c090018071701c1e591100d05205010005402c00b064609441c40c000e0110f10080d4400740b801c149a0083e8440c9134402405d004803841c0740c2e0103522890007038900380f11000d00e0ba170010131025942d120380c100050010b031342d011040011980616002c000000c15080060304241d007a0101313401c0e03400c03c1e04407150b641c10000e0303010308000701009009860007000d01503c1c21440c02260180d1140302c0280040c2c81e028464400b0000400341a901101800380400304648858a51400034001d41080324903001e00e40c81e121488441e0b0000158103043d03010143e0051002d0341e1850805da0080711a9801190f020315228 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 358004919 1250 358003669 358003687
    0xf06020c070f0807050f0117151c021912080c07080d020f0705010813020f03010e0f0a0507050406030803071407080d0906150b190c05060c031603050f0103060b06 71
    0x4030410000304181e402c00d1a600f0f0500045a08003125540141c0c407035800e0b280301750280d9070002071440b07003408000345a24442d41e841d8862115030100f0030402e0f6201c80c4000b40b041c0f54407403c86801000900950703800c08800200304080d8403031565402000c40200200001100080c0014000c0c80024101000e80c0c020320303514521a40b81031066082e84000d03805c4032041c01c543e801d00b0040c80700180024a4010b503d07003401d85007110007250b00940640070304454440c60109403000d4201c0a4241e201000f10b80c3c1d45001198010b440304103004c4220707030600485100140e185414000c080039650030a02d401d203561552281501c001c0c1d00040c04804801040c0490070204103080d001d400b4041c540c2c0740c003085840392071034a4822568007020341b4040342d03204501403101c050709405850314007002000c12800302010740030a413000100704200a04504c103502c1042001c0c400e2501550080c2a02074009035400650310003981582c070100c41c401c1c01c0c2000d110040012035040e400900100c1004bd1407a8034140c011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 358006169 1250 358004919 358004923
    0x1802130c090e0408041802040f23220f0203042a12110a05010c12032f0703200a151d07050a0611071211030d020d020616020a0f06020c 59
    0x3103c0030741d1109008242040480488900140c640c8a01a011840d260501c0070304200c022103030041e9140a610034041e82811620380c03c5504080000416030b0b02a10080c0c448181c00743c040814410700c880c244160750254100e81d000703880c0150f6100c10f0035906030120390344864140302c281d603601811031000c110004a20300313000501d006060003465612290410001402080c0c0f4082e84003a04204131602010042102c88151201d04129450081000441d14811600390100080b0110a40401e401c5803800840c6480007802054403e40300d4003054801d11812482800d03452038040c040750001020200011654100d4070845400310300000350b0100900f00e40c00c5100c441c11a00f0710316511040e03040c0010b290140e0504014162441c00d20402104d620b5007545508a038491503d146404803210400c02c0725400950b0000030025003200c040f281400c1d4000c0d40c4901d00140100980511400714804025540c482403d42e0040c0d001400b01508036a508650b4041c8140d0036100325600740401500d1101c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 358007419 1250 358006169 358006171
    0xe0a1703060a1508040201020c0d0503031503010b0a1404050a0e10020319020c010902091b04060c060603050303130b131205160221010f0506030d111c0804061802130c090e 75
    0x3030340d501c1c80103605d42880060f150007a5899510310405041e90b400000440010440c0c1d4803030f03296035844943c0000900401c4c0544a94110103600c047c400c1008600180100880b144c0d80c0401c40e001c1c40546c451403030960440e440460000d82d82e4202600c103c0e0050415002035400291141c0f9824251207026010004c0f030304225001860b503511900b003c42540350009605411600d05070028280d614419503401c041c1c42144504020300001c5040003050120300c0c1d000301d0041d40c21a066990300d103020340b03640c2103c4659080454030020f545000c514210860031480340d01f81d81c0070600c2c0d1080c1020660507541c3d900070202c054034940b0000024070060311500414010384c000002e440d0f401d1810442c0d5503003900c90071851a4603091521042194550f00082d006943d04140e06000219004140110342000076542d0074101841c0c2c200c0050302c4140d07009401c00d100340d004107400c0250310103480304820016101c42c2c3c0a540810000003000038501254400311500d01c0c0c82c20301e00c1c3c1455403080502c810b504c2c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 358008669 1250 358007419 358007459
    0xd022d121f12050c030105061f0e0a140a2301120209041a03010e19020d02061201080706090e06012a14010218090c0a030203070e04021c0e0a1703060a 66
    0x1020742d0341c40c0400104000f41d840e0014101e0080c031081c91700f003001c950b84013010352a00040c202d0646140c2507c1d0f01682c10240d200d800588900e078201d0701c0e0a0361001019180c0022401850240170005d4030f0000e41c00d4424607112580070140815860300d0044800c0b160784070080d02c2d01c2da401c00c0b01d10002d5545110303d06002e0000241c03e10b02981010406084846005102103207800101151441c4004c07200002c0c1550b0303044845071610b102c54004116680030f02d55204200030041c00012441100000311001268116540c6140070b588030661110003940c169510b502190070300d410380c031400038280084074640829030801c036000d04640d00c0301c040e2051210030706009130b50b000072001804c3c882c42c403c507002c003c400d0740d001015040c03c9064810300d115400c2c0c0c6004056022010900c400d1156114a0240c24020f0081d5220450220100002c910740c1019640c003625020903000342c80004203001070050341109a031035032141c65445481701544002c2050790f00c0a1600e40c04141484641041c0540312 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 358009919 1250 358008669 358008689
    0xc120e060c1609090f0b0a14040b04120c0b180f0a0b0f010e061e03160e060907020606010e01030213080d09150503150d060905030d022d121f 62
    0x400e80c41e000c2e40001c26550040981142401c0100000c6030490400403155544200403070400e50b0b942c50002c00800191004851800091007808140702c03400070701c68080c1340211004455608001c2d0161074007a40244020321032041d600014131a2000551200140c1000400f510700c80c0100c00001401d00c45185411a003180d040b9080c0011b030b1140742c80f8035000d0300607080b40014600702840001d42c0091100303160803050380303808030104182e02c05000c0700c0407200c00e50a0742da4950352104044924038004a030480d014001510008007100c0c03000421b03a00403035060315090040040140110042d52242c4645240a4400c100c00500340100b00101e40c076407020355640c44006820312003030301c0c1004000c65103901000818000d12041580764910f217204020100c42129032500c031440e0480240c00312040141080c080480c00f400b80744c41749c1e00200070201e680380700c1100c1c8011042e0840c400c00007026007064040c0c1b05008210480065010b05500110102003880d0b6058941d40c0e00c00107200c41c2e401421400d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 358011169 1250 358009919 358009933
    0x3070f0b04091d030f180409061e0b0f0d230d020d0f020c090604091202160602010510030303021c09080d05060609090613181101080c0a0c120e060c 65
    0x4555480360003050710207108201d554080f4814029034a005d02c0140b0300c100d0100181c9400342625042c943c03ca030500c040d20a01010a11381082e80c0203111004001d0010390f20055030030701810135072003900851031005080f4400b0002c6c2506102400d85800303022100e03012030300a204000860038181d800b440c50041e00800040285010080c20070b07204091510620242d0304100769419004501e81564403c140c4030a44295100d000142c081d10180e0005040385074084086840d26601151a50b44241103880e5901c1150b668681242210400c40360140da52000c02d0060001a200350014258013407904c0448224070f041a00490072503110aa0407110880001181c0016085500546610a00c00c0383c08904145400300071504192000707122a1050822030540282c0c4002c0381d0000c046140501e0008155011a01d0106561201020154081640c1c2000645a04550030464204503c19503600f01d107128155100e0380312915407440300050240800101255807100c4002e050303031044500042080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 358012419 1250 358011169 358011179
    0x60c0c0f0b07140f09060702130203040f0c1d13032a020907111f0e03070b0603010e0606060a03050a061d16020706020a0f08090406030b0702120a0806090603070f0b04 73
    0x125500e08200d1800c20403090080244c040c08900542d044400f0030340d0920340d1040e03e0b10004800031040000381032000d201006000500040c5241800e208d4401e1004540c1d264840d03080c041800030401510560f10015000102035001c110000c256180c4a4200824a00c04a05600100f503030f000d0368996901a4440d40300b07082d441d1144003d074000e40c0b5805d10a004d001000f20094540c0d00382000402004503940c4980d0b904081c03a40f0003187d10321850280c80e2500b0440c904900c21030700680c0d80c944a5800c114100b40703c01d101162580c01000b005103018501000100305901030321008160444542c0e0300c032030000303e14a03d0105580780d010450710340a0585030045501415880703901c02e91086621a8109000d100d800080c403101c06a000070203000000e0700c5242039001442004280c5030082c1c10080000108820442801d014101c43c1e001d8030030703d0792440e44041d000c0c0503802c031050000720100041b84035814076044c1c4540017200903058a200e140c0b100b0240e4144d04403540580119400041c0401c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 358013669 1250 358012419 358012427
    0xc050a17070c0b07020708010614030106090c020303041704050607030804060c03090b060d15181406130809131b0e0102030403050d0509011e02010903080606030f0103060c0c0f0b07 79
    0xd030040944003031405904180780010150001c500000304541c40242c0894800c0e402085050001d1000b07500138400261108020a088010842064081d44c2056000309451581d40035541c8404200e070300440c03c665507500e940b0541c100141e24505604010040072030729440320380007015414043e0700c605545040070f191031070403148032030580410946408046c0000414141009800031412910f01103070043c1070800070440316a04c035802003035918140010700ea40380c8040944c205a40124a1180385840c88500b4645804084a000040080484454001a8221020344846030019100901501400d01004102d40541421546c03e008240046001ca07900900360071709440c0c00c0c0b02a600f81860355030341a9072008500c6001013482070208140c131040e440f46079612003400c142c81030b0f1144400d031070b075029008101030101900010302d140c1c000b03092400c0400449020b03541000411000ea031a545400008200c85c00841040003404603034030000c10b94035001191403034003800e8030204078184184007030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 358014919 1250 358013669 358013687
    0x60105090c031312051b070303092405160f0c051215061309020907090303020c0406030f0314040914090c090601020a060b010903020a0801021e0405031b060702040c050a 74
    0x520403500c00c104012840c9642010424050313480054030b460300c01c14030401e550314007403211402a07103400800701034a40d50740040c0f5642142e000762100c1070305c5920741c03d400a1003001068621914650b01c60141c60b01c500c1000109060b845c09000344020105942da0450404120350301928a21042e000520071454151a4005e800301610010558400030000d4901e1050004042a100c0c0d5504940e20880111540200d100c059001740b520300366207040c8001600d81c00450009500510a0b2400089941068880c03101900c1d00070398445508142580c086808155030b190052080d1018400050349007200d011310300022604013081d040c20b10b03002042528000c400d8071610b00c118a00d10921502d41d80114122001c55003080001c0785189103140180d560084550009410a90a80f400180f100e0f0660242242c2e04c28151106107250400002070301a0003240145541500840381c44004554a40103914650b4405442942088151740006049541e45420729020420000301c101c0d1540e400361442c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 358016169 1250 358014919 358014931
    0x20d0f0203090a020d02060705010c02060403110105040c0506030714030114011403100323030d0f0e0609030307301401120503040506030403020115080f16150302031e01060206010509 80
    0x31401d41c9481c02d08507544401100b400703402504100015829034035807031308851103150000000e11000041c05002540d40b0000c072010703000101c18030f000b55450001800380d41d008642044428074070f5810f2008002c11641302a01200600c220000c01d03122100844c00070b54020002c0040ca06181c050786070015040304203102c1030342072500c010410040000910410007060f6500820118090004500b21015100c0d54140b001054403012a00b4241c0c03041542010030444446501031204030b09000c42d03c3d90314081130b070b6031582580080c4000744e5447c2c86612030001041c0110b59411003010810345151400c030510300701210311600c942010500010303901c03c0b07600500100507000d510a0303054440d2034490040b406450320503540003010074213252007500000d40c1d501e03c1400c504095a03881d40c1e0159a503282c00c88060700d03405400684c81225008801c80c4003118078800d42a000c81e0b50a20086000390b00c0249040000300407860a0150380201e2040940a400b0b990010480d550401081000b5120000c0c02c2c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 358017419 1250 358016169 358016171
    0xc0d0e0a090506210f1002090a080c010206060112180b0a1b020714130203190b0d0309090504030c0b0921040302240d0207060b0f0f090415060306020d020d0f 69
    0x3d00009031185030480920796110744403c1005506800450300b80a21100d0a040034420350082103041c2e80c10703600501a02c1821606051031940d91400d042d1580300101c1454050303000800026500c0d4040c0e032010f5403407040d0341000100b070825000c60714072480070040142c503420001420010784100b9485042d4400b4820312050000701c0004c01d0096542e0700d18020200001e02c076041040e0031b901e9040245484046d01c0310199201d1070501d0000c1c41c41d0b45a000081d01684c10203032074041c0da04088501c00c2c200b0341c250f502c0042240c00c00380c4030005042d000e04224100905a80083c001c5840f4038140c0d406401100f000c2e200303803003088030f031002120f03270605015030183d204010410040e9561840c0c0020084442d040a80d1034080e500c0070080da019480a52038004e000003003036820841c1030307480002c08200407110b440103000710a013440038070b120358240c0540007840c1c50041030100d540004602800c000942c404920244c490740c45500760380004070700b001c0c4544c000c038040b48822039a02800324020441a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 358018669 1250 358017419 358017421
    0x30c1b0306010603270f050114100506090d05010207120212030c12191a150421061e05070e011d010f02120a0504030311060c040b0903030c0d0e0a0905 66
    0x40001d4940e00180704030801e0554a51204280e0090341514020807100441c2400d02c60450703041071a400950501c040740c2651030010903a9400e150f1005550107610854242024a400c1034103101c0e070317680b105a02e41c1d4803070300c1000e051000070f100b40000c0250510480414406200350800603290541d0400c804605540c1881041090000c2324103031070407038425600351421510b039078032030921f480c2c020b40c643d0844504020b500b00c01e2000c28101a01c4c1002c040d6202040800d60020308200d40c052809511404480404081c0c45010310541d12500107024504c0000c40038030440c00c1140007400e000d40230308065101c104008103150070a1003001054002e0800030001100f5817503044100a00000d02414004841d4800000500c200401c08003908444906550b4540c04500074003190418802280080c66202c6100a210301c042640c034000c5a0b00d403a41800d0130300704072100381183c0100c44069010312091040e850490070402070310b07040d0450350f00c80c00404103c0e042400b064105d01d421003030b61141040c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 358019919 1250 358018669 358018723
    0xb03030c032809150309110316080f1207020103051017060601080112022b060207051e03210c071217060303160b0c070c0905150a050117040501020405060408030c 71
    0x1e030094440c50024540010700780350607e060640e443e01e041c82580c06220306420481e480d80c241803d082544d41d40d0702103400410010342101c0d0340380c0d05c4000d034810314001840a08019406900090341206065207880c095640700e0800c4446d01905410128042e03000500703202003560065861409089680520b084a091a401040001c0d201003102c2080004910210518107201083c40b0b02196000000359650754280c140143d441c001808000440c1000d4554407070158400001c460f521020611035181d110303a141c00c0040361100080640c102c8a204211580c001b5290110200880c25152103410041c091000c0b814810240249503500079401001407144610f045102c0708001c41d48a03003000303d0b130f5640c1004001c0754084c00d8802010b80807142000300e05403205e0380240b4802d034407401104018044003030411400944a11415000c54240c400003010720b54511181580309005500140c80d041d65480490082d42c820350100c02150800300710004d00003005c1c0034941c01c0c5006801113288a00b904 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 358021169 1250 358019919 358019939
    0x120225210f02150c0111121f0603020903030f040b03100b0f1204050c10110d0c170a031d0102090f060408060f040f0f290106120b03030c032809 63
    0x1045010b40301c0d5049003400e0540403502801c440c0c0c01213104c40280181120291007a409401000071403441070f40100015068051100c840034440e0b01c1c0c94801c60030f0324a841000c2e00294400c01006400d80410448c4054110b404030003480101443c01d00c0341d40e64581072030150051100e94010b64145403082020212540c6503c0568040d510074018032000303a00c0714605140390102624156810405070070801409a4020031241c6480700e644040c1c5050307110728031045904001c455401060003590380100d8041c021740101906801a5902740095044006109400d40418824134451709a40005075078400341401030f00140c03407041c140c810343d04017410108038075181d1100a15140e0201d00031030003d81440013100380d4480321f0707800005c4440c4c1e00d03015090503280c215107001c904c0314001203804103240120710386407010304071889a078a43c140c1140381070381e10010f440420a403543c117103c00d120b08112010144024803580800001c404454031800101d1041007c81c0a0180c00740800600300300010340780 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 358022419 1250 358021169 358021193
    0x1240509010e0102070915030201090e0f0103060504030516051b18010e10090f020a080921031009111803070315020306060403080703120e010b030a12022521 69
    0xb42005820040c0102c0100c0c501078030340c0d10502010f8149051074280120011802042e80d0003a03132412200b40d04c81c0700c0100403c00a88051106046a000410110310341c2c1c8e1186400500c030386081841c1400014840303a00465400d0182c8440d0002c406a010100995240c4081003034161420520a500c010790b82e0350540c0c0521800a080d028180003502d4070704002d00000c090108500200200301d0140300101c02504140303510400315023900d004c510500344c00581d114441d60001142c0d291041241c04441c00c0c0e810281400c810001907042c0400e845180c1e000780140ca0f032001c0313504c6844400245000c0c00c40d00501c1c9815000b908000400e10205a0711880c0741c03014502100056900d07201e45001c2601441503600c050704014022404000f0075900610080d1074503440311040c08421180d2403601d00302c5240e200c4190b0b043e0b21045038034001400380005030b010035442e8010707510840807214076a601070000004030180744407880b00a014500385200b40030442d9010785130912282030385076a8100a00b031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 358023669 1250 358022419 358022437
    0x30c030604060b040e070f031112061315140411090405190302070902070317010b090d14030c0613061b05030415062d0b030403050702060a1103070b012405 68
    0x1450b1000e4520603104c9030003448481c024107045843e4241c1e5000f544450210900040b80c0340000f81881810038900980000e41c1030854402514180e02c6110859600c1e032148c010032100d0b954484649004180181701d041e01242c289030683c1e61324981840e00d4070882c0802040d0a208042910500002c5507000880980380c051b0361145840c4117107035080603484e2250783e5100d02c400d09e000103880da0030503074007007130595804000c00e070311407441e03600c070038000b0424000e034150b140d0000c40c58039100001c07072622000c25180030881d6013602d180206002105080400442d66180c0036009010340c201089404c3c400c1003650380010716030000311001514020b20034031001e030002d0900c0c1000060041007520700d5010000078040e00c403111000008030941d04204405101070107111398200c440000b465010741d82100d01c110352542e603040c035161441d030820000d600003844050801c02085008594070008200604907a401a903111410b985018240c200c0501d48280300701c843c611440e0749104494004040d921208 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 358024919 1250 358023669 358023671
    0x1022104060f0c050303150f0f06030a1112070806090a0c080613021c060501090e160503090a050102030106121d100f0f0f020405360717090601090605030c03060406 72
    0x107581c2c40045038482c411090207002c50000000384880303951025000300d01042c00f80c0d060100308031008204001c204401c43c420360007450030400242c0c50040ca074000c80c0d00c0145003440178280200c40c3c1c03890752100421203000c80420700c0301d4184800380c5010203845074840414035003401702e83c1031361030b008040c00400380c039032400ba80100202c01c0c680042a01030b94641f55145e0124004031140c070360848081c000c0c901c250b074042511500c0105010090201940c49104004038000d400f4034885c0080f2000d600c014440e6156014101c1e050707000510a0000358000d01996884c6a17101c1c40742240388040f50150641e4100b00e40d8080c0000310968400309442160b40d41d50040082c1401e0707441091406484010540c800741d03440e002c0c40d204c50715125405042940c03403c0d6013250201c00120b082058009080700c4900307011064480305e4004100808165500103210701e4483c6026420101000e0316120544400c01240c22071801400080e03d00d2183c0c8004000480042c0078410344030300860f440c3c0b480608013030042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 358026169 1250 358024919 358024937
    0x30c04060305071e09150921050106120602130e06030607140c010c08040b0108010b0603130201020703060908090f040515061305120304080d0c080405040506040b090a09020102210406 80
    0x3d60149604000340421210394071004005588010000c02c05800303016400011180c81c15019842003100000340c0325054410040c8c858000d054801b00101504101c03400c0d034840f0300118503a03501d000041c0c4801d209400250701c03901c000c50070842c010700c2e941010518811040810171140c0c0c002445503041a12424500b0a01e620501c0e910424070030311004030001c1d130912210a1144d540400d415119032f000c1d150341c00d560790320740c80d20500340d824504690b64031000c01d02c0072170980100201d80000991050041b689170300d603a41d40b0103041e2a0075100c15191180c002c1841c8800b4103289110740c50510049500f0091483d00c0e24864001c1030b600c2034102c0c0108004900724003020002903000019040003880c00c00c01800d100c0d0010f0356588103019903640c1340510b075100d501d021f0050201c80302280d40449414241810a0180002031078001c0c00d080d4010f0701c820034500b242e201d24021602440d40100007280c1445280006894154143e204400121071506146030b00b901110650b02510b050340703082c01039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 358027419 1250 358026169 358026181
    0x21306110d05220f060f02192a1802031e011a0d02120f0910090203070509271c020c090a0e1f0906060806060a0605091210050403030b06030c04060305 66
    0xf05a402d0b080300c0000000150007050243d0007021a0b000046d0380d81c21510150601c03d82c402c42c07081440c8005000760180740800c0140d4200d00c55540c0d0550010b45000d51082ea920713214046552510300c161429540041449600c03280140b011005480700b00181040354900148509030301e040725500491100c0104508000044940483d0492501c018990440781800040041c0c04003060305c1c5400f407442802d58030003096002d0b003d200e0310181c0080180a2051810080c84620304000b0922072514100380465400740044000307244100a000005124030040c5403000b4030031000858881c1d0039507120500705000c40d500c04d480b0950003c00640d01003400700341c0624944c5040c901655140b81c007000001460100c021341c1d4000d841550198000b8000c40d03035556000341d10740c0c00079180b85802000e000020f2140394000d40050545d207401529032115908032a40d400d00f80104884400c0f03c064850301804181907050044c5080340c40c040318081d1443c2402d01e041482e80c811441580203050b190400180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 358028669 1250 358027419 358027477
    0x114040906060e060415120b0601110f0c030f071419080307060e100501050f010309020f03120d1104050109060c06060b0c030901030501080f0a020d08040504021306110d05 75
    0x440c0c9a00000500940c0d0f11a0901004900200d4409004138a001d0140c00035024210241303040301e0070b0000d040840080354507040c4045c1c100030f2900d03060010084103400e00348010800c0e503051014480142100011010402d0708044204a1005007603128030004e100701e64015030201c48941d4126100c851781c08900d0310444e050004ea510038203407800045404414007000307800540ca00850300040d02c4000ae490f08041c81103071003c1c01210b0f00030071461444070595000b80d01569005000504560840b161100040d20341004100388808040001c0740c0241c42c1d00d02da0182804900103080168109818000020010000d0b403140508010701000510103100d240d03030005001d0110302c0c818540e100900301505030745e41d0202e80709030b00291400c400054440c002041e880b9117601c020000e40160b50442d0204103480801507002c0da5101c10070000055155501d1009120b04000c8566400b4401d242c1100940b65450000641000ba0008400403907000d502100b112819800321600080640b180c072082c41e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 358029919 1250 358028669 358028681
    0x906031b040608160603230105120f01021b07090905150c2502030646020c0c01141315030902040e0c0a1211060304081c05070806010c0308011404 64
    0x5000d020b401e0405031080301c001109000d030388043d1403d0240c80316480b501f0740d0390189803209520421900c1c00510441c9820280901c035010355904507040709042040711401c80c1c1c004056911070810790020318551030b9050000000424191004000910140e29002c5d1190303030a07010000c4098080d000124018485029503040d00402d0701c0452501d0809018160340416082060384644190f4000540348205071000c3c101c800c100400400400c800e4520726070034030805200181710440020303206003240b41c052021304403c00114009000b824141000504801386034242d801c0b00250410030b0703086c03c01084200c0c6007114240f000020080140c410100d0051000d0708000754070604003603003000070303110001d650b03040030800311809440d456075414015080c1d84031180040c00700c4a80412507403185442c4000d55480381c040d6844501d0402003800100071701c1442214910f90340c0d1f4441c00e010686605c40701c0141d100c1f00a081c0b5546075220f27030310040e0103008148606402015894034411687e00d030754000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 358031169 1250 358029919 358029929
    0x5040b0c0f0c0a0b040c0b0c0d1b0203060f1509010e040b04020109080307061d0c010c060207030306030b100f0e0c12070e03010c030f11160303020306010302040b04031109060906031b0406 82
    0x24070f0760310880c0d00d0015070701c4205440968117001c40b0480828621408402c80c3e5015076520014042203d00c2942900c001c86142034402c03041407001d00305001750320705000c2c00d441100e413000800494600303a80380030000b490f0070b101c090017031100350700500c00302100c1c000369504240c01506a80e8259503510040315107010541007900540004140c403402c1207080d40021050302c5425940b1030203080341060469480441c6203529000071074010701d1002040d15580280ba109000f454003103403864494031001e014480c02c3e200459150411042000160341c8181000040e14500e9410b1180d400c0039452051580030701c0040250580071007010402c45400780440c0003035100081d0084c001c0c1070070008050b0081500f01514822a4189240741060416103412207401b99081d003045c0400c0001520100c000b5013008040c2814142d08020102d18040000003400003036106101400c4045525000e018071543c001c0c0559001e59512418044a5940410748003840b40075600450b10080c03424000034058841036002e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 358032419 1250 358031169 358031173
    0xe040c0c0323071a0411041e0e1002040f060e030d0c060e100f091109091f0603020d1410050103110d030e04050108010e070807080c0d03120e1b0405040b0c0f0c 70
    0x10501090400e8800030740319034003904060008449200503c0305455041d40d09500c1c440c02610007501d00c140302c3d806000020321141c200c4403007440e00c0d1601c2b0100d0317005401003078900040450401106600048111801c60309502400048404110140c416212140000e09154990700060718282042151840c0d40d0707400001401289840c4007a0b0000700030101042d01c3c0c030345992140c50803a00308101414050841407004140d110421360200200e80e840c0000100015102c02002026983d03c2009604250140050b0038030302c0e0b100d4055501e002c0091050382501402d0000410100f0940350a120701e0100544401001d41054541118400b41c4034801d2030b0701c240380ca8000f0526290540c0404a0344c01200121600d103501d500e06695a0b0116220f10704007030f4007440c1c10194900303000c4528040b080c402c0c101900440101c9248a055030701800f0444a240d00400f03011880002d4001809004034043d2020044c41c2000d8903a500340420003000c1a2059500140c8180030350704000803a0214031707090342 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 358033669 1250 358032419 358032443
    0x30c020a0222060b04050d060c0c050d0207090605030d020a030e010302040902030a0902040b010c0c03060c0909020a030f230a05040f08040b0414040c1d031c0e040c0c032307 76
    0x444200054005400c1200c2c1440c150307000c11a100d034031381290241c500080284d0718004c0709aa070040174004241c3c02d00200001d030040c41000410800c1f070700080101580141c5100c0d4188003000007241ca1a500c11446548440e0030a000c20b500070440d490065058603108907140c5074040141c001c1e101d607510040d01a40b0001c01c21600d02d026920206005108681c24800796554100440c1c01280c0d401e00540103045070f9004000140c200d51154000304c03114100380b88030564030f1502c82d00f00e0308280440c3c00440d03140d4121510203130386c500c0760702c1d510fa081d800b940c0d030364103040d2900680c4100020f00b501e85031940c9074003080902030076812481c11981d0290003640d5642d166509009140c000341300c1c1c0a900c004212020210f40360038007030703072100c90f5090b07072041e203818900403c10b64044401c40050f90540a00400c4039404018000600600700b5107440ba40044900f0200340802c0f60100259901008403400c032840c002944010b2010310720803001c40000380c0b04004d0408111501ca1920010400c1c08040c7c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 358034919 1250 358033669 358033699
    0x100e030a15150b0f0d1404051e030a171012030c030e01030b13090f02060d14010f0303050307050a2706170103020a091a030a1410020c0706030c020a02 66
    0x429804060039501d58248011148218011600600c90090703901c1c035001032061145244050b00a40980080180c1c0415580030309122140d080009581c02d41d03c07a000044003889410030410100c14600c070750002549007415041c0018100c442c20392090034440c403240049940311f5681840c04001e440d80d5881d03030000043d9840c026004d0340c100c2030210041201d41560f00703031541c06840340a00e00e22001e4811143c55203240e0b4030000919564908480c082001c200c1170300542c9404026101c1c0b0400e00d03600007140703007402d031520b020700c1e42c1603206095292560b03000740006903200c1f080d82d4000096041c46615501100000e0701c5040302644002000070b076851040d0f14869515007050222600364407007441250005056203048038090101940203c0110300800240c03125500c400a070308203194106084c40003500000341051a03040c4290783d010030024241003503407001d010356410810340550444c603040454607071545078007461145805066540d4140e050344c074002d006200c0e0540c3e0040c070036100041c0e08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 358036169 1250 358034919 358034933
    0x1230a0504240e1212160510060f0e061809010c11032109031204060f050112110906042004140904030c1e1e120906021228050306040c08010311100e030a 67
    0x1001c8113441501c20780f00c0030481800541318071b20a4036614284003042c10300f458001854042c001c0d046507000dc00c003030800480404034140071400b80007130200100e162015a400200400b98491208400d50410000d81d40c541001d041941100e405c0380c0607041d5641c0d5172200003400c500524440032824503140c410441048201e5101c48c005204c0724400700026600e80321181110386e05031030010020014046002c4031480e08a481d03540c0860000c001040032441c501840c0e0090b03101c0c030381c00e0315181d0000c5002d1201c0f41c0001e00712030020000b9074541940d4540342d14000c2c00040c1c02c2001401010021551003a0000d00d10314110303c05400042c11181030384101448030240e10310f00c80589000d000b0340c4210985904c5211603004451483e0700500e0b840c00003890726209a8032140c041c00415410713480f1070490b41802c0c9000000c440c01a2a039907100c0c64244240000e482e26040c00004100d00400148001084c0d00103142014006a1303c2c1401031700da5007410381e541c070300e280d04880d418440c021040d4104020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 358037419 1250 358036169 358036207
    0x80a08091603021011010209030f011a0111030d0b040207080433020d05090d020301060b0703030f020406140904062117130501230a0504240e1212 64
    0x303100c00301c41c42010159440c141d40c0c0c2103400000d51100030107441003480f510401c3d0080c8039000040c0018030b46460540003a00d840c1355901110120b0751074421180312881c0140215000500a00b4000003003107145001035100e00c200712401c09480e596030004072880c1c48541c1625140c035409007155580343d0726600403900c003a1700810503c08002146644c40481065030042e28029003071a002020f0f50201c52409a03066009000c5083e04002d1030440c810250340e0901400c0c00411000f007030250340b400182401000c0d103c84e00c00d030000c00c500400c82045402e60102d04126000741c03110b0341540314000500010050040765010b40401c1c8a8031280c4402c03201071034640c002041c401c0340041d10706020345110390000d010340100349201d050315010407c807950040441b001c1d140140000351407122994071004015030882c07a049000150042014005c00c03060310080c5112141c009103c910856500c130005100140181c26a402030089035140d401284c010024592146010000c80342c036400009102055012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 358038669 1250 358037419 358037431
    0x10213030804240207270c180902090a03121b0302030301061205042307080111030106170f0c0c0a06021801030b01112a21010506041103011a0403080a08 67
    0x10019006000500c3e001904082580c0c258020707083e060314010039403445040340d182c84c070421407003031007201400303011485900c0f00c00d0303069100c0c0b03110b003a41103402c011101e55a401200a0500c10080500c00303680703481403442103036401105202c0519809a00700c0c1d100502100e13541c40403040c01400010180c0100c05141a242203a9900307150b4000c01812100345c03101aa0040c2100454400766610329000340303400031003000c485040b66580c076074a41d126030850b03422401d0a046600040018407101e58000c03a07502c0c14904500e14030400d41481507481d2158900985060382e00100026001c001e0310b000c0c00401e03d20341e00840110f468850a8114404c3c5280039810303240028504510281d130f560242c20301c103900d440c4c954001d207455464a0300743c0d81c03281000c0205d25040d040304000c07890103581d00d0f40703184108030410300c41c112030881c210310841c02d4480250040344151b040140300034038680391600f520b04460515001000101ca41c07880c03440c1d14400c5400141c035054000038614245600000c2c50350042c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 358039919 1250 358038669 358038689
    0x30d0903061808040306020304050109050307050604030f030501082a04140105090609240307090507020c0301050912090f1302030709170705010f0e0118060c211e02010213030804 78
    0x40e00c2c504071240c0c25109040080281c14180300500210300e6503409158081d11a5000080d15103154a58070b1a6070401e9a04075800d40c055010441055031280e1202869821414280705175418030481c40d444540152030941800c070551307101c405a50521442a42000307010300b00f02301c000f0314900071610306402401000c3c084e0a1640c042105404c20715036092141150307550030502080b0700398000e0342c0300e00b003450a640d1500c10140c1c085003130300e420b105450203044241c000340021114036044c5400c0d904001d0900c0c10907005000080c0426036403c1c1100c1c18010112440601002100001581049544121581c1510200c01c01c003240c1c0d040010710050303800d114000030040007501030b0380d56146400e004a50000341602c440c1c41940e405150140301a40e1f05040c011440384030701d406040c00290907408000055080300c030090501508108850f14406000c554140c40329a2010150058140b950540c01400c100e03d94042054400e41c15102c0022910769840c01d09036980c00e1500060f045406040712017 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 358041169 1250 358039919 358039931
    0xd08011401050304021309150207060e06060a15020102040b03090102040602070b2104060b0907030506011101091a0903120a0903110a020a140f040213031209031a06040b030d090306 79
    0x200e50a03600346601110169515495a41c0381e601303005603001c484191a00c2c3d039407a400c20b1000913142d1111040e0518407080c005850343c079103050030303c2500d6806442c044142c100406002842d140d008168040d121003420042c05403172950000ca00900c11a400340c141c0040c00b10074803c1000c0b06400030021160740e9800c0700c0c82c064903206030180900c94161500c0341000f80ca801c21500c000300100769070340103000311400994504004041460034108480903800240c0c0d600420610390f070841c5000303903001d0303140c002044004400e648582c1003c0b820580820440b40180c00610001c400700304803034052945074281207072401c0022140000e000d642c40201d01040a0501c050440e180000b0044081a00208901d4250740f5190358000d0603e845a800d40d04004410403c2496441e1400200340e5545191100700c500c3e4910700b440d282d045d01c40311440040082010041010821710300545030040c5641c3c3c428200e0703844010000b0000c1c1a00d054442d0103000d00c1c40000c03407098104004c001101c0c0520307070074401c2c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 358042419 1250 358041169 358041179
    0x50105010510050c0709051005130c120e0705130e0712020901140d0f0212010c09080c03010504050607030e01091a04060b01021c1b060203040c06030b041b11100e0d0801 74
    0x40e005507213010241c3c1c1c0c0505401c21000c1003075000142c01c90071205a4808850b00c034000700c1e02196140c521114070a44601e50b45e20b07429072281c0080414003196000b000b101842001036600e88580c2e108035840b0782140c11400d001034050707601c580c480240c08002c0300c100c41da890351005128041c0000c182e11030042e05000080c80b4406e4141c8150800d001091800386040c1ca270755410008000074801e9810034014956034450040034031031480e4070306868840032003051511a00d286058105000712380242d04220a0200041c8001113450308500300d400c0210351401100c00e4140100500c540180030108407480582c20200c1010255000b60300906040c4441d10302c0b0320059079620b1030548070044042c10140e2100302da91180112101c9000c005403003100c10300b00e580703c0c03a09a0f0415202551000f02c1c2c0300d0100591501480b540684102c296020b00480107030304c880c1503002400003075a8040c001b406d452080409020301015510301100c4408200b00c0682c003c5159a518030010240c01044801c400030507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 358043669 1250 358042419 358042427
    0x20105130b0115031506020703050708010b0603070809190809010e030d0f1413030503120703050c120c1204030f20030301170f030a0f0921020105030603030d0603050105010510 77
    0x5000d80100712003000382d1808aa442007802c0d00c1c0c16000800d40d641004ca0a4504041101e2005200075070007050002e065050050414085502c1001c05a162103000b494a4032142c0a40c1e50240b6181020099a034424a2180c2040c2c49801c0030f246644140d8506002c0150240141ca4402c0c42a03941c940d110081b8028180d640005074210320104901540e000c607050311840c1e600c0c2c11500b0043c189800d04000b881c2d11640e00d2400e400440702174002182c40141d026001044550001480c5401c4c000d0341030518036800c0501c500c3d18401c202220381c0e00001c0a902c0c0e40d60446105803611060040b0a1900b810010700341c601c16092400002d120b910301080d44032141480c100ba211469014510b10f034a8001031916604004406160340d0040056403400044240080c00c0011101d8559403444800090001d010441c0c036007184192310703003215480c0c8029403040d220170781c9242d0a007030141e62511400300280c598050309119104080c1069004010080306410490485405644100700c880e84111b05031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 358044919 1250 358043669 358043701
    0x40801060315050f0a0c0509091303021212011806051e15070215090111030c01020a0801170307061116050f0705010c03050d0513060c08070f03020c070506030421020607020105 77
    0x1030f0840801300100300106815440030078207006504209180c030800c140400d2510804640b81c0ca03007084803442c020203040e0140500c0084102c8845c507145441c520f40301c929000281800345016014a65a20941b500c0b01c40d80020090300f001454540001000519002051040b1400a01600b0702c000941210440c42d426a1010303030303000b419040340082d2003445031615000200210f04000186a4185512030b083c401042a42e003980005a038940c480348000d000810180c0c0103c80c0ccc0800b101344540111804000d40312103035802280414540d0070702c006840140160300c4030105543c07260b040c80d42004000110b05000128440944441655990040d10403a00d40a00940420802c100c0074600c003100c0d40c0711981c001c51080d0828024100d6403580300841c0c140d22060004210004240440c1075001110523301009030701c5c1c15441d0120365100342d0344901003489581d000d07803800310102d0b0030003007440c08002c81561a400545148011040d0080d40d940c02507031030401552811000c207034a000002144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 358046169 1250 358044919 358044931
    0x121202030a0c0207090b0105180a0914160905011403040c0801020f22030309030b071704110405090c03030433030b0a0e1b07050c0406081b060c061302010c0804080106031505 76
    0x4a04045271090700c0c0ba0798401780341101340d2111340e00e280895045413501c40d00e0344040c600200440c151034035100440804000c510564103201c02d1110410103603038400132030304068090802c0e04c0d880e40c0b100e1401c03425484158020a20a50010800304c200c0c000c06000b4040c40c981003000800e010b1a00300c00310801c04c031203000280c00110003030300900c00305200c4001c858000d011450100300d162000d00707994001820507030741290b0800d07586181c3c451070328040c021150003c00e0900a4404030082000083da80c0c4141c1c400d54119203596468003d03100b6541602034000c4a08024040307080008400c010010000043c3e480d2144054120100d11080002401c034403901c42c02005445009643c20001d40796040b5100031103c0d44103000b00c01c4442d80f181c0c01020020410b040040c1040401801021050300740c8110703807802050309200040c4d00d41000558180c0245194100280e0030f0b006000490709003404100142425500280c00507504105602c040210b0380108400348225103588680000c0c3c403815249 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 358047419 1250 358046169 358046177
    0x90210110721060e12030106090302040506010f0c0221150906010b03040305091c020619020c0303120f040206040806010303110c010c0803040b0c0d09050303240a03121202030a0c0207090b01 83
    0x8088001107003584400b480060030070481740d85070806207005a0640c800d0308100c0009800d07140400c21401c06000b40740d000701e02400d041e2109140410014450307256000068400c2c400d4003150b460841c09403000d100000710003420b032250031200c1c0c0701c00c0c2c41034941564200c8103440b4981c00041c0b0414004280c0c2d004903450307602c003440c000800c410001e038000d02d40a02940d06044001c0301c00140d07641d07001041d0b1100c10800d400c03c02c28886c80e01a007403900564545002e43c004001890b014110240c000f5806141078600c1d14107a221400443c049006a41210815104000010040c580c0260302d0351240c41414045480c50030100004440c1110f0f4400010485e4000b80701040005800422099110303440042a50809000321804401c2e2101d0140035191074100009120811103080111201ea800c0d03800c01c03441856249000c100702c0c0390b1912026120b007070008500c2600030300c03400d84030217031300c901c22015034903810a00001c0c001006100d4900d00903100e15000001d500b8010700400716a400140c517 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 358048669 1250 358047419 358047479
    0x1026161802182e0302040b0912010b060c0714010905010906030e010905031801080606030426070807060c080915220b010e060915150903010902101107 66
    0x54600007941094074100d10a62000b61910745070307141c0c810a07050503603050030601c2400ca40c1c45002c08110480b1840780007058010881802240c1611003141d10081d000d44070f00c00c1e0a1035140c01140100003103506107901950007d020100e0000000d01c0d0300540d4001420114103076050401520814817900c20f65021500c680006c102060280d4040f80a0101400022400c41c1e05070351100e0441c5c4c455842808007040d8000103818950344007400340c2d0b0200d0113903007440c0385003400d0311422040d0300003d1b1440748000a000c070303481c240040841601c6819a1021600362200081e1814201a0251207404000a00c14100148241c000080c04070600038041000030703d507403110f64280855695207420f014480c0540b100c6840040c0428803407900070010324607007403241e0800104004280001621544900501a8801c181696402c080e80003000c118018540d032200c181c400300f40502180440030b9440f0b00c00f40c2803010f416802090748860300c1c90180584501503224684800c0c9401c1c0c4049032040413000366 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 358049919 1250 358048669 358048709
    0x203060a0e1209010c14030c070909020d020402070813090506040b040207150b0114070b0603010e07080303060120010e06040201140a02191a100f0f06080f102616 71
    0x800405054070f06140904818540b921080d5224030760b800c2c0340c0c00719400060f100b82405070038440030019101641040c803200e14250001a03503072200c8031029202c6c4d0740c0000c060081005c40d074201d412041c01a9a01080103a441800400401c000c6506600641c14114000e00700c0ca0a8821250642d60202c0c20002c40008030305108020b00d6000d10780c5044c418812201c1085e40740303400103040c0c3d261041d0421900c2d803520100b45800c1d40e490380c00313010f0158002c4005022030310300402601d82c000b0007840d180d038155801d00c1c2a55001150014003810075440e103400000c0311000072030352074440e40c000c2c0c03074690003650000c1d400d4055200d0540c948005070401055460000082900003481c0c2c3c2c081e1800006020551038644070b042816121014404c200030802c0010604c041d40650081c550000c0d1150030928007000904407410040c0f17921502c182d2480050800c01140c468280584650070b030501072020600341510502c1a603e003450302622696809821940e424207010702590003003450040001d03160 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 358051169 1250 358049919 358049953
    0x1b010c09121a1909080405040b0a0312030c02071205060601200a020120031b16061d03010608030a0906140301150c11041a010f0e010504060c0501020d06060c0203060a0e 74
    0x900003604541d541c10392010f500c08140944c4e0040f50042846a0351941341908204c215101e10a80a00400c1944010400b003510034880302082540c0b4200850481c80a0504a0510340143c1012801e031400d0040c10303040c04800203038140b00b941c086e04c610105403143d203840b0041881060b1100c10f6a40328a4000c0015482500150740e4100a412049440901c028a480c210703040320080f800d014584000e10201004c0400c0f400e800001c0a1130324601007410004002e02a910b02101c40c074808403030100509403078400358400c100904443d4240e03034403140c581000801d444014441c5000194407050074150143c4020107c9040b100c07040416621101030410684406d2900c410990340c560034620300394050389990240340e01e8812240d80074101c800c801340025200c0c55a220703480b400c0001d803019070107242c1d0304070080b076040d038556003054480001e07d45082c0b40a0300c2612003407071031181003050000d04075801c203c1040c54a0301c00c0302920420b9541c401000300301c82501844940b964130441e403400c2c6031602c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 358052419 1250 358051169 358051171
    0xb19082703090d080c190201120e150a020406030f0605091b1309050a0c032310080f010501090606050c150604060b0c0a02131806111b010c09121a 64
    0x10300c0c290790034000c1c2c100000d00c102e00080030036104110006064a809607043c814070210035041c141650000b030b45900001d03c1c40c00110707041c1c0c00d06560340c2521072585c541000044103200790812030084910b86040b19201940061240c1004241080503401e0398482e940610700642d240a0114a101d9aa030840480701028118140d00c0746079080000403c0120100540c5003d407034241d001280c0b41c100b90b404002140e003845181d10070103146c200c10180380381249102003c0021811005003654588032024403444240c2d034030120992140172001c0b20820810741000d4101c50780a40204000b55461100f80d8261240d40310454190f0061400c1d900b07800300042c1050781061010f04006203c50f02d0394901c02c2154032402ca00d10056014510401c110300c0d04046019562103041810b0107807960311580003030000d81c2c40303600800d03268940054001410340d1500707a0340080344803040c4012511404441c5130003055045010000107400b0380001c5002c00060140c0d04019070310444400b0b0f010b8200c0145003441d28 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 358053669 1250 358052419 358052491
    0x30d12150302130605010206010b091f020f151504050907090e211806130501201501090c03021801050c1002030c0903160518040c030c0b1908 62
    0x280016001c805615008030402846210040010764681010000391604e0030503800b40c032215500b04021000c5803141074051104814a9100c4169204c1c21841a414403a10444000d150700c03c1c3c02500b180340f00a64081401340891450904078611013205102c16150111642040c6a1009200b00400d01c002e40c0070403100da41203015184164080b4212240194008039600400d0703a002c1800510807a503103a04000d1004101c6401d4601584001d820070a60600e10a581c10300c03040e40c00c4400d54584001800b428140000143c400700c01034084102e8205400f80103034001c01e0714100b98255124040e108613080704884c1d041e0032180388980b10045481c0d612948090019000781503074240481e03664006107010300c02c4c44904644a440c1842454035204c01004031007100506810208a551581680340d00c591a04e040005400e9407581030545c102c0c0302651008200c0622001c4c0043c5001c5e040c400f90a403c40c00d103484004442d90030804a540d40400ea400086082c81c508000010301121070a07011200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 358054919 1250 358053669 358053701
    0x1051002280b010e0a05071805040902040b18180c0a0506091207080606100e0d02010302071e060f2a050309160803070318030b060d02010c021002010605010e030d12 72
    0x30440d510090400700c00c1e4041441104d14600340110542940505c0380e0086441c07820388044501109002d0507410740c0d1240714012640d801d281030954403183c118a580500c0170741104440412610f8a072182e000448400e0650036003008600d0781000c0201c0e0103503501d50010020100d1038200f100700140c941c40000c5041d0f0080c00340c96030520b1505c080c890303007005040301c50240080e80341c440c0c10302c401c000d40c05d4980420450121204481a900c20704c0e034444154081c40d0050f207450081c9062a03408600002604420b4641d004004c200642c541096401943c800e400340440200401d42c4004100c0320140e4030310103d8001d06034016075100d1000b459000b00f149080700c3c080583e02214080da90066005020140c100041a1040c50303000804a400451843c0b01c0c1c1c010103186484004201e900580800d20520080242d602960700c40c40301c42e21300301d0b0001c3c1040b010502c0d059000e80201241d1140078045015030121230050300c0e02207420003000105032681280d148140d4003d90041042440420b816 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 358056169 1250 358054919 358054993
    0x204180b070c0510060602070e070e0d050a020103060b0c1905070527070504050d0602070201030213061710120b06041d0a050106090908040e04020117100e01051002 72
    0x114038110880c600986154a07000c40c212101d0500c2400c040900c0d403c140e016007810000c11459900144a60480d590600c0000003600e420504440400300344603d40c4c2e200c1c5a01c9007107800c0c464042440f1449603c02d0b01c0c1000300c980d032924004854050682ca6291503007140e12240900a000d0300d5110302948203100b80c51009480d030340016070401d20500d4981440100d09003601207402e058103441e4100100d400c00c01c2c2842d04d030000240d000307608850018881f9030045440740031a40260181c81c0086640598855140c5d144d5a006200092001b04182040c002d0b80101d40c9480303400224909852904101c000314a17503d8840c170301c0c0c1003030180840390000c0d070701c6a8044100c00e04080f130a0003081c03040d0240c00071072014144982076641eaa000062802c1c039105400c400105000120f0b4115094102c0b141e410b44e07590300061b12083e003240b4080b2001241130f810050509100c0c6003c205035860401c10715a0303a41c03a40d060204100038480400c001d640840d144801207126030b00709810100d2981019850 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 358057419 1250 358056169 358056173
    0x30a0f0c140a0f03030c030c1b051206010e0622020301090902010f0f0f0311120a0506270610030f1109150918040507080109030509010f0c02010801210203031206011416020418 77
    0x2218078480e048200024510700c140075918001562114001001cbc0042040d07505103c0c0e018910140a0407080c41041c141c090700106561480c075a4176080d001540454507581c3d2010002c0161101e618204e0019a00c8009a040140940c100c14000c071040e50704c1c07541c03810340d144084d40100b0402030303041c2c1a49410703c00e015031b50020410707062080e42c00310400308050414405000d03d0b0444034003c001c2458551120b5000f0030040304683d548090115443c0f0201d0020102c00e8009040c2e5000400105003014201c090f1004c03904018140410b040d2941c04c0703100c00c5070f210303600b1602440050036440381482414904070841541e0071a0400e0280080e50012691104030500310b4560140490100350042001c03443c6682040e40940c001402c0e04102c000502c40d80c0c002002c1d00814000c0031070355203e0102d2514142d004185442c0c1e9640e0203822240c1c0c0340104020307079001c402c5c202c580c0382c0080d010081890300040d00d00240ca448a0b04803080c0580403850b070f804c20001d00840a8010f000b000d0780c00c910701c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 358058669 1250 358057419 358057433
    0x5040c0e04050a02040303170c0a03020a090e130201120b0d020f030c030d090801050703020903190507080d0801030c08031c0207062318030307120b030a0f0c140a0f03030c030c 77
    0x102400f19480c006940da4038529029216905a17000940c07205503660402400507100c2c0103d50441e802c038980141d0303031505d02109845400c9290440004542c03200300300f00d41140035009222000d8001d88500040640f60701c115000c0e03c0900389540e80001d00a031111006050600400d840288003c003540e0540f8000710202e8545040002c0f0180050501d0360100b11400c030030302c5070541003000d504c3c0941c645090707a00070965881c00c0c1030f2521142c011000256081c45020b2000c90060100c0605071400079004110003000040c007800300b9511100034010008641c4400030032a1904550145664600c000c1c1c40803d50094000d01000d41b06581c860142e44440406240c3c00412084200866000d604147c0550200c1416140a003415940304100b400311054022038003425418003120041000c0501c40e0101e4180010900c1c01400700090b038100c441009001c0310701c4030690f100003000b8001240340008004a1f83c13180c0c454071110b01c14a41c0184007080c490b82c00000f00780d01a0400100010066903164 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 358059919 1250 358058669 358058671
    0x30a080a020303041509020a05060d06030c090e0f06011a0c011b110c04050121020105160b0714030f0c0f221505030105060a1b0f0c14030a0c05040c0e0405 68
    0x10050b0000420407040014074402e6560b02c54140004010003a51980802c5a44800d030103041d104000104415000341040c0d04103d000d5580040704208007a581c6c1c84003c040d0452040c050914014400040424070000400c41d040b1080000c51000d100b101c088420500e03404510713508a69500c40d44050044034a88c100000c418081e035450a05003081108a40e052403180c4201901c110f050034010081d9035580c0c1c08010301901400410a41d030403461006032403901ca41507507003180003034800c1307081c0c14001a07a520300d108904685514240191340c80b006050f910003203d202c0b00c0f03019441d002c1030200c911303072016000a41e000d001442c41d008641071001c011500782c02e100c076000c021200040c03084c8048889110200803481c2411030455052800050141c0602c20840c8100301b144030748640340c2404407030b610020300d810280b0400c0d6001541000070500c0d4aa010ba0f510055492007820321034100010b00e03080d040e4112110f02d50306070402c0c1c01c00020745500c01b903180400282c004c014202c3ea403144182 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 358061169 1250 358059919 358059937
    0x1050c01110702040c02150a150915080d020609060c071703090a060c0504030809092212020c0108071b030905130212060f0604030b040813080c090a051006080402030a08 74
    0x40c0d140c01e00b0748100b005407000c1c1c0c1846001c54100d030314080c1904001d100c1140d0803c0e00c0010208106044d2100084102c0c0301e58408403080e400d044e000c02d100302510481c0780c103440c1e9280580d24012210241a66240b00664a44510340d00003170000341085071200191028521030480491110920f1115400f1500309407006462600000c89000800c1828420050307144584d04025080c28919101c11040f40030340d240031070148410310000380320706441481d440000340c0040044d00710582903043c1208103010203c030400140c031840110034450b43c01a141c0611811280e5907004c00c0620880c040c0546c107900f45002c605006542d000492188c1e600500d000c4103e03001c80c2c005840e94880c144800785110045c01c2680a0050307829000c050307454400c220350940340c0003c1090026100c2e0b140400b1076104203407180507403250362103020404110110300c11100e4081111202026110784c42c405048400a44014003c41c005200810400e030007800007030760243c0020700b034413243ca080752a40079031540300041e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 358062419 1250 358061169 358061201
    0x20a09050c0910080105030a020118050409030c06050c0f041517130605010b09280803070602040603050a06081c18030f0c0807180509030d0f050703060e0c0403080901050c01 76
    0x410748241015240501c00c0f4445107081c2c02c80b5494007003c241c0f515030000c0041e0400a0703800e0034441100c10107410100400d0003800400c150f60301820b0061161111074811520300d030400000c0717080b100f14001550302c842c44800c0c02e549001e291035102c0c20780300289051071341882681c00101c0300000705020760a1041c001419032540a200700d280c813508540301600510764505041c0300b642015164862290208100990f0b01d540c8480f00c283c0811030300b00c455000035100d21002440004100c0c142c2c02501c1118400d0710103004c1600d598189000303813096400f50380c60542c004d82038015002d055000001d51021031382418200c6403411040301d034401c0c1c015001030300c0c8003004160785420441d607680381700c004002000141034102c2c20b08103000042c00b1a40e80c00c003005510751012840301001032040300e6044002110030054034401800d44c0010f800d0444282c00842e240030b0000900c8125000c4c40c03413090004800007440e250650b55802d1080e08207111090400005014114410000344180c00c007070079003582c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 358063669 1250 358062419 358062427
    0x6020306030d0203030c030f1305060124030c1d0402090a0f06022505090414010504150606030b24070b0906040b0a090f0f02190f080d050a0c0b04020a09050c 69
    0x3081c10b00e41440b105030703201190f00410070881c102c000e090940c2d4102c81c03146080368168840724210781110107059009040d6000382c50000170b543c02c0f2050714600c03079a40700c002c25044c4003403135409030b0485c3c2d0200c8135000811044940000b01070400b00000407541e8004100604000c3e420b0045141d2500795002182c0c9000000414019950100002c40d549c105e2841080c1c45100080e1482040c80198441c16010f8024480858104100c0c0c0004030781c0160043c0080007285810708110000394602040741e0411840c1181c003040c4180304c1e00401220720009020020803150600041c001c2c1009100c03004600d403024081240020501160b003400f0b02c00c00c00042c51a810300b0f040c8000400c0340a4021001e182ca007041354000201c0310080300c0449904090b5404c00001c45001007806401c1a0048040d440d0540e040407407072003410405002078404a4044603147c2109502c140c0c0e5074801c0401c0c540c0403841d02e03c01100040c0d003803071030785500c10710203042d0180f89a983c928200c10f540d01901c1100f00e00340045 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 358064919 1250 358063669 358063681
    0x13030f020a14130507050702120a0c0f06050a050913181703130b0603100510080705030f1e21041e0e0a0e0a0506040804031a06010509040c020c0904060203 68
    0xa00c000001c0c2100030b00c980344101000c000119043c019002c0d03015041d440d100040e0060740a402501c0310b0710f401800045071391f031048100540380d5101a10840d845413203088045503482d81a00e419003561222b440b150310b460f401e2081620550404024580d10070514a85041035100900404d149820b40130130071000b800b00c500c1c0c47c1c0b1140607900c9c00c182900d50700b88100030b8030410441149043c1600968040e000b80c5036280880c0c1411408800c1542441c02d0005019100b003404ca400012180e1401c1a03901d401d84030707010540c4610071814a03101a81c42801a002c10450b15145050403000b180c04880300340044000e201d00300084010074241060010500b00b04010706040f6880141002202858401c0c0c10b0540c0c0c0e08640724041c0420700351585d6003003940349660341040300c080c130aa000001c547c03940c5081d107444403155100e030200301c90800703d10050b000541c070316200c903c0c041d0005840703090402007100d0600c002804c131549000c04610800e62124025100d8500050040d8024180941e41e46407035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 358066169 1250 358064919 358064929
    0x90302150601212910020303060a15090f06020d0e031f020a0302071e02151e1c02130f05060a0c110f12010c02070608040b1303030213030f02 62
    0x6504054035040c04801048440d0303900880b0320a000c9001080c8240084441d0741c04002001010100311a0329088840e42c6003850b00b5560701884440c080728001d80c00c03011050203d81b07034041030f200ca640058840c032052020034076601e201c428420203403505140300790f03407401c0132500100294842e00240e0400f9030000025a0b0040d01a603056000750028800c1c550030616514230f482c0c40c14040c00250342c2c0481d8082219129030122211250403940c0c4440910440d8480303404507400c3d01e0102d11900464003503004908002e0180d840c0907882c80b0402c000d030b139204c0030440225406882001000c03090b442002c1c2c41b00329a48090015001c034500c2805c041401c0c22055540d650305900301d68828001402101c1d14240e20001d1546013990000c0400038031400714001c1185802d488603895400003501941c0760864805500281d0a0701041c0e0032100703426603c0005494003003045d030b805041540e4176400134850850182c01c00c01504e220f407038014a0008002d9415000c441c1d560403c5038007086040c150000d40c600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 358067419 1250 358066169 358066183
    0x1809030c060a0203151002060a0c020c06040e010503060f01030b0c0304061d1b1207050f0409140a20010e060a11120d0614100f020304050603010306240819050703080d090302 76
    0x421b5801020440c000342c0302030340d0b43c6c0008104580550b103910170407400350303c00d201c022400036000c0d2125031240d8076903100030f550032824090107000b0320492000440c0020915040b078101d0b6044a0841d0850720307039542110030355000820980e0f09507211706400501000c496900c1c2003940704070300902004030060720140000c1000c420070703e100300f0302c03521711200081340030a040084034421282c0413280d10000c000309001e402c000070060040605d14821590603180452a1071406209203882da503c0030080007072521020380403070703c1400200f1a003200d490f0303800d0000082195030030f02d050894800140242d59850510b01c4501d00101c3d10b80070030180085042401000c02409100c403400c0c189006c940041400c251540044508001ca2a400303065038600034801c4030098103020300b140c0d641f50b03100d05101010f81070301441043c1c00880c0d00544044c0c601400f00110a80d00400e001c1d0100c031100800514000541c0501030b15540102e420000000e10488020803404428170320200c2c40c082e460030701030b0601c0a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 358068669 1250 358067419 358067461
    0xd0b010e030c0307050d020f040e0105071b0b1605090406030606170303091b06120703090213020702030705121203010e0720030406050a0908100e0613021809030c060a0203 75
    0x84101d10b2125150b40104440301526015110340703616481c1400081d040c418400e001c0e9400c103180889a50048806401c031600c00c3d6101d03119370004a1014091000341741c00c0240241800142901080b0a01c03120b40d11060030200c40c1c90603508054003a4001411240e0715441200c0e0f407035a0315005c010918003100071090403405000611708525003000300d07a0f1140c01c01040020282c0c60010704220301e58841c0c054464000180e082c2d4005803801c0b41020b0001c001c0c0b83d0040c0e203e00003002d000d442004c2d41c1d008035250309a01a002c0c1003d646401c0c14001d0110742010700c100795000d04141800b85002c6036001d94001c2034001e5119003103081602010300191140d0801c00788141c600420512090400000c4804a0b0300c217141080e503035000f001c82102c06411642003900346020b44003c402001040b40c206030707489980001520100d840f0754010800c02243c0d01c40007500a2402035100344204080305209500811203030075240340180d030380300882c1000402c9601d6030441e0350210034420000700307151103011121 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 358069919 1250 358068669 358068673
    0x60a05132108180a1104020c030a080906010902030106020c10210213050306040203030a050c0a020a08030a030f02090d0303020d0621051506010c110f0a060c05010f150608040602040b0d0b010e03 85
    0xb0811a201e5522441c4040300174100e00c09a901d01c031013a8031542d040f91103182d2400f0a40e92a621a114001c020040c107464081e414403801c0c0010507900b01905c00c681c101c68480c1c0003405205152424011004203e00800c000d0040b4810107042000c0007011841d01c2c100303031000c0103958040c1540320b81c0c00d185a035003002e8040d41c0840100310041e10008102d603034402e4681400354540750703042c4400b450105030007030007500804010f40c00184420000003800310a08245c80038401e00c0c2885414001728015202c2c801c0c2c0c400c1203031860501090080d402070008940c8604082551511034481c0b500d6611050103401124400852180030f0140510540e040c0e2440011443c55a00380a000240509218000070f00704828405410f1826602c022540380c0a00000c1e114042c181d54441020300f02d400604001d0391a9400d001c0300c049812543c1c03082c0003a804c481c1600b09030309400c1c0a8204c58000c401401166040d6003000003144103550f03500a0320b80e072880e0f013002042c031030b100c5800144801e02c1d1003a21030090f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 358071169 1250 358069919 358069951
    0x10b0306010f060c020112020706090b01030b2514070b090d02101404080306030a0506010b0316020a0c0323030d0605010f022b120207080301091d060a05132108 70
    0x3e9602150b8075042c981c092a00c481e14a8004824500030311031050300a0240703203003d5003401044425058181280c2c006d010f8a4415507441c060003201e03081007980d068120300248203e03800c15004103007a40a0350300c800380c49800c1c61b60740c0d921011111003d40d6071450301d5200d004c0c0d103400942e042090100402c101d803000d00c078141003568403182845c000f4100410400d404000100e068504000c0c09920a822508841072960366803400c50240c2d009484000149010003402d1480c140001105290594444103812265145840700c90105403a808200c4204403291a1a00100800c0000c0d205200c416100081c4403450030300007424408200111805540020000d01403103072840207552400f400b8010240e190320031009081703d445d900800110b00c0d140c80801d4240a208000c0041c5060307450b02c1008200c0b014060101d1a1407104020b0100c400f076110400182540b0700507001142c0140080c011074010001650310b00c0503940c60300850a544050f000046c90400d9481050b054005540403858507031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 358072419 1250 358071169 358071179
    0x110909030a09090f0f18030806030309150705010b0306010f18050c180102031314040c020312040f050a0b010e0a0b120c1c0b090303040507060f0c060b1809010b0306010f 74
    0x9aa071240b10b0840744513914082d488941e0241d0300310f464155040b40081004880140b007014054500758419030004103907800243c0c43d1300340041191440d1038000e1100045c0d6074000c442940c1d9500026040721155250341454011382c908000e1107018100c0e80c4059003e00e4100810700d00d02541400e0210052401c1c0002e001d41d206290003200d41c103240c1e0400d2140d50b40c0303000c80143e03c0d47c0b054a1001d41c8070112038000181c072000030a070101c1038031070449007800071002021080ba624003a042c000c1caa00748000c008600040e4071501030390150f07482603003594200036440d01c40070300302c0209a000d041404025010000c0d45d01d030521900103a480110b80240440314400603a5030743d1000c28103154040d10141c040d00f4003070902c031031407001a40d520400c00c1002c2e00d000c0303800c2906e94106440c01c07a420311982c0800b0800c54042c0018205010070b5684a000e0b8603d5a100c90000d00101140e040e00308078683e0b200a840708806c2015071055105d000040395141201c000c0c146000e105034421100c03200285070a00c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 358073669 1250 358072419 358072427
    0x409080a02190218071112090f0405010806070522150e120303160909020a0203040e1b031506070f030225051503060319150b120c010305070c0b0103110909030a 70
    0x40d96480b00f800020085d6075105090310741050404001c6441d207d030002d090340c3e17094858000d200c1460300b42c0344403944d502c100702071100786c607028003d41526412000c0007442c424441e5024050302c0d44c03d0380220903842400c135410f8810f02c3c0240c018940101c01d8948400c00141c024030002114441030711001010808009419100d0002a206101911a0a4a4406051180300650003400c01008110340e908181031010f17540317a2051050504d1015950001036424003044441c00d41c015071082c9003461a9a541c0003104418241030b00300d0343c00a403c0c004500407070170707064001c80b43d18800e4000305802440d5060308140240255070a0240540d5803000b80174686605000100b111805007a107522903e5080010b030800100b05074411990040003100c1007846440307030400c044429038040130003205200341e0500190f0700400303812180c650301540c4110160b5207e903100c203600410515003003031103240603541c034030f2610700a0f401660040f08019400b0380614046000540001c52071009501c0c00b081044098 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 358074919 1250 358073669 358073689
    0x7090e0c160605190e07082103040f031e1805150706090c0512010c0f05040501020c0d0302210702030105182e0905060907080106060504091a0409080a021902 69
    0x141000d0b01d0390301140d41c0c84000f5207002d04e0204d01c0e880911409410200c2c03142c2d641d041c0d214000c5d551298140400042c1e00340013403040348800708100b141c0756966988411080e008042411001c000720b21b203185440400098100c03d2507121039680d80c0c00c2007800d014a01c565692a0045132080d0312a400005040803048111010180d105401142c1c000160400121050469106070340182e5100c0f4000004c200644c0040d2864145403074030f09840054200840d0640540e000303060143c0d000c42c144024500d010401c4685c80782c440e00c12100040d00c0101c02d10702c1c01a0064040741a40000f0510400b1807400b80103030340d44090500081e058050450310709541c0c5003001940100308940b10401c4a688080f190016405c90302601c50074004042907142442d62030100f19202c0c1104c0c0900c1c42c02040e244018001e0038103c2d20350b40e6500c0e04041c10482404010240b89003201050355021800d0380640d140c0380101c03c0c085d8050384040d6269a0341c02000783c200100307403141d004403002c0040400c0050703035054480c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 358076169 1250 358074919 358074923
    0x40e030406030b0a0f060c0501050f0606041214100f050c031e090f0303150f150301061b02040e0a050d090e040609020f040905010c180f0501050f070b07090e0c16 71
    0xc54241d545002160031000c8903049484482103817580403400302d1300141c64140e190703c1100200000d50f10101841c4810205072171103036012004210820813803c6032203281c0201e81c0108102381d0107020403000c1c14a031424107030503168016214040607030341e0500fa100e025441100a42c14518615141403245090503108100302c094000b04004074608113010030414028030b084004890350717824440001490058200c8200e44103000381d0811803942c2c1000200d010343c407042100320b2420340c0d003050402d550303010b400c481c0b48000f943c040540d1800343c0e90f0b038010034440b003002c00b000d8018003919003003250a043c0308203203000074000e009900700841c0008003006c0c0e41c0700e604400001080100d510001d0104900300e51107581c4681800600010301006500031161070038541c40c2d5151040d030700c40c1d50328040081803280c400120864101003000c0d50140000b01001541c62407076601c7c1c40244d07542d40e03841072025620007001130000001845524542d41800c0d40012210f1401ca0501d00c0d402541c1740750041c11940 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 358077419 1250 358076169 358076171
    0x90d050a02030d0204061701080d0806040c02150408040303030501050306101401200717120d0902240301050301050c0f09041e06060e03010b040501050a0b0f0415030903020c040e03040603 82
    0x91114401d10a006481c61115020303015035445540310402840c54069590346030303400c2e01600c00002d4048000900811103031880e1500203080e51904204401801a0500c0000754043c08042007204525944800d10462007409419103450450800608941050b0000c9020340c0c03082d024842803058514201044a12240c884507500e201040101c608042d00e80c0c2010702042010211404c0d10b0011036403905540184a402d1410501c1e1501c03242d8444842500d4140d4000410050001041a0f0005030740d039800a40400b600751800c5800b0300c80c1400907128842608008001803107a45400e00031b050304a1203200c40710f41005807280340071000d445410f504034031440d42c4001d51558900380e8a001d045580700440100001c9540d040c018042c5d0400980b064465441c143c407650913860107110b43c506030303200a00910307103690500d100804150b00c0345440000c103d50602c40000c208001210071682d44110707941c042013481603440c0c0a40342070444030b4100c0c801c5007810101000900700000743c2d800c4401e940381c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 358078669 1250 358077419 358077427
    0x106091701060b0a0f1805180a0e0a0803040c06021c03050613020a0905031e060103021011030a11300702040603020402070302060708010906050d120509030d090807080105090d05 78
    0x1881600505040e0301c05641c080d0045444c00c901d0360850309200a600040d22000d03030006000f00c0600c1c0c803010070700845500c0409030b001540d24000c400189540452004800100d40381c10540d594541120184110386020000003004200200c0c90b21820050041e40010490070503158038803134109840e80840000c00d07980384009511541c940406090b9413035409001c66a070024428010042c2c2428052680a44511701c0030780b07040c40c03030b0200d40d100e0196070401074a1103074210340c2000240d04401c61150304100180000045880042c8024440f8641e5a01c0d5581e03510064080361b0705105072595074402e550000085004608035034502000b01440c604000d07035030b4994a100040060186400194005101040c400205900042c10301c1c0103e007192035014990307070380341104003c1e00c125014444c0c000c94240d1030040020340710326600050200e075041850820405c01d01207031500c43c101e416031001400c9050100304403d01130080401070026100280614617103e150907a0f60050f06040700c04003c0001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 358079919 1250 358078669 358078709
    0x200102150915040b0a18020d0209070c08040b0910020a11010315091409010501050a2702070605040b011403070e040209100f0f0302031204141513090504050d0305010609 74
    0xc08a0b00301200482d40700c00351070a0508240c04410070072035040c8541c2d85840204c011405403c41000c2d400f550041c00c0c0c204184035036090103548480a0702050600505180c10000103405001a0002e440c849865039246d500d074504110001d15034894050a42d040071a41e0404129640400d5103c01c00030b0802160400800c1c04003000101c05a0003a00d1040c81c1c812208080ba943d000a41e006409860003030159980380d0080041c0003403036215442100620f11034150940c2001d103030f01850707289560300050500480d40c6841c000c0d5241154112181d501d100c0c01448072021030300301c8050340e00c401d8000b485c0c00340c10001c21410018001e0302c0070b84650b40036000101c4040e080522400a05451584050001d40d621801700840780d29003c124840e018050b000400c0c12a0036061301c04a50024250001c0c0c0c1440c1414440100103802c0c58032820041006211080b4039800340d400010844107000041070324050400c1c0d410000d401c07240408150401004101ca0303030340881c000c0c1c15100c10940c2185244c1f601c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 358081169 1250 358079919 358079923
    0x305030901080c0f030a09211d1504091e060e0a062108090f0d050a111509062a0d09050f2b06051e15130e070e01122001021509 56
    0x200e684c4144661543c00344045842e88500310274030324600140f210060041140800c01d80c40840f80c42c88600203400e1100300030480785a00000c00300b26480c4402182201c8c03418480d02601c20580040c105c10903104140119080ca9215508c0289212103410700c03484c141c005084503400c1040301c09002c1540215420096550344000aa1780d070320020400c00780703000341c1d02d03020b80c980100300c03016905510b800c0460503040c104041265094005444031300e1400701500100080c40c0c00c16481040ca2407007064062582e42811907a1801001401004010708004494000c02a07126600123500400c2c2041c500c1c80c00c4c1d250410074012200303444080c0084400c4040d0041d00480240310003508150410041c0300c244a89010101c4809a22400422580d070b21610b0601c41007030f0030800290040c110340c00c032200381e42143c2c0c400c1e160081107100366800e07a5514800036003450001e0300102d00780880c10840a080010003035450303114580d01e104541c2c03005000302c0080c0d02e0380600c1406000e40b8103180d00194103e0740c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 358082419 1250 358081169 358081193
    0x4030219020a0f03060b031203100e130b07030213050a030506060432040b1602070513020c01020d0209101d040b0d052e06030819020f070305030901080c0f030a09 71
    0x4070a501c4a4000daa85c100705010346404034075940207000c3c01d142d004000940404032486001c0c603001c06c10f16a03240030051080c6c50001402200d10395600710302c3c130740010000c0f0055802094103a0300540c0399403000b089041c0c0420345d5800948600c00c4d400c01000099001b003405075100104403000541d04204030580c50381800210300e006400d400440607400488502d113483c1d80582d00a0035215030b184e0311000c2c601d040c2111720620340096440300d2010030280c41c06c81050202d0a043c0c00340503003004e04111100d0b080e42c000c0e41c169842c07550049060011400c01c1105075820705954549680050f40070b1040302d10f100d00c0490010b000300d4a4501c2c44004d500d071981f80070703541c0d54040100c5200d4083c2d0500750f440002c5c0622101e0010b26071007609050030b0301d68010f05060742d1b00309440518002d41c560718600e00641110140d021741c061000e4840c200a0180407010003107000f00d02a6550300f501c000014080e440040c100071443c102449180c00c1804040b041c0c0b5880f240301000024020300c981042d49035540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 358083669 1250 358082419 358082429
    0x20a180e03040b0403060b15031504110a020c130504032015010311011e0905090901150303051905030730020418050f01051c1e06060303020c010804030219020a 70
    0x1000040018283c0c031100014001c503801240d0801c500d0717210303400b0080d6145814012400c455000d2010036003521601c034140185c20801000000c0594844101d501c858203d181d87c000560400c0040c10302d1810305a000201c007600a07001001185015076001e03010784071040e020111140000c610300fa4420003040010140320144031003a8280d80e6078031309000b15030071000c801070005e10507507800c5d8080502d5004140c64a1000d4980c01c10721803e2205019483c000206180499920740008080a04503030300420040c43c002e54529030354006408608010400718408401040010810809690741c0044070300002c1d980c070050442440100c0c3d032001c402d44003a4800e480640d00c00100041c40d03d003070400d041d00d0121100d4042c032003a6103554203204a8002407003601d030007003420303d800e500700e08950b021100030921614800780c59034810324201590781215101100c00740e685d62020f0041c103030100a4030103140001d20700003400d49420381c0e00039101ca040c00500804a29101d03080c100b150340d4804a50080c00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 358084919 1250 358083669 358083673
    0x13060501030605180120131a0417070305120f190503060f030303150d0507031e020a140f061308190605060a060806090703090204050f010f0b07020a180e 67
    0x961282088001088213aa400140b400407040c5440c2d404010700035400d4072000f08100c80a25503c162544c0695804800da420b90700c14010000308282c046801c40d0356002c140e1717184064403581041c0910011303240e100310040b940c1c0c1c4a180204001403000800342c2072510303c0035801c0d4845030024610606801900c00c0c0759800b950200218488950040c00341d442200201c0e520910365a81006150b12440140c44c46021015500304031802c6c2d00341455403072a03440c440c0f4101e42c14a503417521011400d80390302e001800305500c0e8200103c290700c0c0903450b882c003400b4030440000800d100e003c00156000c205a8034503000c0d04c008074261540d80f1003049150b00410b0703108181d8402002101c0040450082d5a1049030480d14100210355181000c0c0c0560b001c2d209207031613510840e1502c5c8204074415000400400400d03442d4007014005032100c1c09035034082c02c1e0300c0c01c9004843d41031004941c0c41800540211002000900c44c401c05652902c00c1d2070304480c221160480c0403030103441c0440181901d07146812046c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 358086169 1250 358084919 358084921
    0x2240c1b010f09050c0d110d020303040e01270b031e1c05090a0602071224290306060d080304020d050303040f0605100b0703030b031f0c080f061008130605 68
    0xc0c1007150803c4842d0342c0301d642515040e4001743c0c100710040c1c0300c22001801c960f10520b00100641062402c04015900050843c0c0c1803c1c0e9404030100c1300f40d8244c02c412284d810130400c00720819420b0360a0710500415035010322102180c100400e0761000720b40801d075242c030050042008901802c1c04110180b04c000388020706c01e05001031000d4810760100802c103000d102d49e020b0029070a40301141003400d4401c3c0c840b2441c811070483c1c0710701000c3c2c401072942d0321020060034203000303042c40ba500c1500c0303c10300180080308041110b924021a0311820942c80e5001c2e400910801c103142d0340d003401318a01d26611200d0385072246c4403400420482c1c00b00d00c40041203031100200b80300c1400180c29500c5005480b48405000b039a66405c5000e8040c6500e12405801482c240074000c0040d0003500201c1407284054225125413190402c40f1034501192041c2d404401d54a840360080c072070b805071f00c80c0d40c0401d401140c4459410080c0110302040d040b450074408002c003200c04202c0121603460000780f06a00201c00f4051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 358087419 1250 358086169 358086191
    0x3080d2c010903080f01050f0105030c04090c03090203013e04080607020c0a090b0a0302040c111606020c0102060112110315070914010c0507290f0301050102240c1b01 73
    0xa089a81043e0082454070001810310804c45540b507050301e00140280c0580000c100042d146500302400c10010207005000c086609030b06032044c030000f00701d40d540203e220403250051608607142407d403052908001540c10065100014010f0080c8070007034080000a10301041c0c041e0140510740200c4258014841804000c035400120514040e10072900120720903503486000084500c4414040d0700042851010005483d055200c83c510f070300b542c00c018000c0c60244404038140b030309103404d4078010342c00e140003802003681c1080403486c0c114080c0028049035040440340c014400c40407200400001c0b0b20015928142c0f0300740800f0035190b0b0f80a8201e030640c141264080c110540d68010041401c403017000010300781d07203d0074074408090f8010002d440c0483c1440581c0112850581c00d0303006840c440600c00e0040c1004e0300007400c540c420304000c123840e941440c000a04110340f0030710700300e15003c038100c00a014440328146190801180510240d940b54282ca00094034100b014400090f54a01429110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 358088669 1250 358087419 358087421
    0x41205031b0d0e0108070c02040e150c04050603060d0303090b0a051e06180901150807030c08010c170601020a0204020d02070b0f07020c040e0c06040803040906090603080d2c01 77
    0x2a6011103000c401818003181880c00da5524140d4402a00140c41c0126040d100c4d401085042d07045082c40c6000c60800c1a0382c1c000c901660020700901461b584400e00100510106c007119030b40040e070400030310385014906800107200340806441184074600d00b05003039003094003a0b841544526400810a1940d05e4814a05802410b044560300c882c850a070404800103900710748854840c21008140046046640300064040e86009200420966844564892481c0b1002400c0020308441d8000c080e45404c614142003200c490342e10000c40e50b030401c0415585c032608003540300c041c003103612490f40c01d079690940100d1400c6414800650814400900c00541c219260000c020407070041c0308030080fa031103c01d8684a2194105d4680005801845c66a18039107003903004042d1010b00ca5017252803070542d0f280050940da02c1980304009039800000c3c10015529a8020170004280019080000b03d182d038a81149910800d03264100103590f4403021b0401000c40c0034030808401d1001c1142c2c0d8040e8030079021138 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 358089919 1250 358088669 358088677
    0xb31091e0501060b0301120809030709060816080604112b060c02060f0f150d060c0206061c021e130c020d09140a050103181b15050711010e030304120503 67
    0xd140c1e5424000041138080106040324125100b000303040703911a017207442e150070b5a0442da44142d03140c00380c03030000100541305d8014403000e401160003408611090100790b1071000c04640c4000d026400400170030010580c40350005801203026a001550007001d04140000e1038840c103150030350708000000e5641408070307660000039007254503000c95009440311010540c42801c01c0740c3c0c2035018000740000500803080750380d015450072005481c015482886d582c404040d186c0009041c1e00603440710f4200400d41c03503d410076091140020103005001c10300c0c0d4010500003640c3c84440c1c074000403680380f07100864540c404c03680841200c2150800c890010484c0081d01c2d03c1c0040181e0300080e84031040492742c06494060070121800c0105900001454040154058041c2c1c2d803403401c030b44088403000c40226454518401403080440b280b02c1c956410701110341c00c415401c504204c10007030f040c8900d400083c01ca000700b001c50b200908201c0074142400000a01d503100d00d070804143d5401d2030032601c1c20003c0004c050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 358091169 1250 358089919 358089923
    0xc0703060e0604031205160e030304090f020304060b1509040513140a0b09010204120605060a050901090c080c070320070b0d0b0a06050c0709020a090b03070e03010b31091e 75
    0x103002e503840401035041901e10030340d03030098607c408414251701381d4010106040046000b9080d2030405a845100f0021619141d50311186e19070004100400c1004900c101c1c403500c0340c1203901d0040040900600880740c011640018066652000401e91110426082042d102d0f84512120000c2d141c0c1c5030580d0304c54000d0042103580001c0080441c5480506000f82c40030390300e100010501a0160307071078101c05400050952500305030302076808103080d201e40c4021070290a50a00c04907040a48240044c50048010120300d803150f0140141d8000a078002c03100900382400344050b4110141d980d901906000301580090b946c0074000034860030b200c0c0391750444041c180c41205d055035099661002178071144107100600413245c00090044c402c0d2182c40d030280110300721034a854081d141d29040c00182039841602c032180420002c80c00500a031409000d040c0300e0314400d03240300300c00d1000b803e00c04207182c4400500b0702e0646d0285d2070440c01c40c04207074044070a02d83c0042101032a005010041c07040d8100942e41 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 358092419 1250 358091169 358091177
    0x8070606050f0f0607080c060c120915180114090109030e030304300f0b04230706030e0f03030708090706050f030a0f02130f0504060e0105060f0c0703060e060403 71
    0x1986180c160140d2415402c06043d00b0014800c20b0700b084025880700b181181c104405008050120804025042c40b400c4c0c2c10700005ea03038660242c11341c0388103c0000c2920fa88c0380e2110716070848640c1c2ea00031598004900b031112880600344d0000660250045500d07514044611000700900c560054101c2c20750640251502c40701043c282c000c0c107480c0d10580c040c41c100203203214020b2260318643c040050b5641440365140720060800e5607450f501a030155415130714050001c0601040c0200c030750707045408031b050248400d00b000121076559210b0205100d620203250761044101268403090141e031181e0a11081505d42d41d161100001c2d000b600242c2d9401030a1180c083e020410f14003c504454001c81c00660040c1903030351300d507200c10140034010080c581041d001d0060000161501d00380c40003030401c084030441000d003030006020407100c0f2a0309c0f01e607580039403d004100d1a2103943c129107050365041d031030079910403440201610300141c03070340300400891501d840500500d4021402501451090723513 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 358093525 1106 358092419 358092431
    0x1118010f0e01050402030618100f0308070b06060a021911100206090c0102010b182509081207020918240105030c0103151202030309040504080706 64
    0x3000c0c00d441201008284000480c007840035014180c00d550445c110711301000007481c0742812079100301c0f14074904001314441803808031060010384000e206621003a5542d00e03040c180d03503110b6803003599003403550f0010411078035000c0200c41c20710340c1582c000c18181840368070f403c1ea2011001012100c2d5621142e00440a4891000c02c911003600c40d00541a646082c40300301c4c0c108409843c0e02d90459150881c0401181d481000e5a1506241100c107020103686007281e60141d445a119105110228007046102565000755010292400340003030361070000c05014081d081340940074000b07621194050018164041d040e80c3c0c1d00bc81c4060000321026031303900440362680b440241e0440105200d146005000d24203040000100c0f0403001e2034100441c0000380c0c0d805034000303140c0c02009244412810000250741c1e01304281c2d690791600030710401007418980f50450495000d00000c03501181855 = true := by decide +kernel

theorem cover : BRFrame.Cov 357913669 358093525 := by
  have h0 := BRFrame.cov_init 357913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 357913669 ≤ n) (h2 : n < 358093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
