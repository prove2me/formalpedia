-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2980
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:18:35.850212+00:00
-- url     : https://prove2.me/submissions/3ea2e133-2c0c-4ec5-a39a-df66123b9345

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 535791366 ≤ n < 535971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 535792616 1250 535791366 535791401
    0x4030b06010c1b03123203100f26070609090c110613050f010917180d080c061b090f13020f03040605010504110414060f030109020a031b0f03 62
    0x480724080383d0000d10006600440c94207100340c241950181a0281580e51880031015101d040c04c9240e180e0f2503280702d1444034030b03141950381c1da0b00d1070300d01e1004860340c02c105c5208608000c002000450740a10000c80150500c5100307500382c001c080a6524207451080d9000301d14081020400c480c200d503c1040d0608070f82c18048410700e50028420309000c4c044900c00d109100416101d810700c00c1c2001704c011540400f41c003c010b4031000f40c6526880210b9003411258010340003d468082c0c0b0001021400b41d40d0b00584110f284c041c86240880340358125194074030291244000007408011001c1d1643d00e03030800c2c407d0b06403811308280e044c040b10300e40b901c14035900903822140105806594ac0f00070400101000710044c0c0380d040c145000c0040da2410303401207100e0303070070050202c8034100403404890889000000c10304014840002051040c012806248a01c2c44007000005103240070740c00030b010801444e5820020142024844030f5540c4001c04030200080195540c1d0021034003d600100c1c0140c0041d0302c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 535793866 1250 535792616 535792643
    0xf080a020109061107030e10170612010c12050709120201200d020c03010b040933090812070207060203040902130305100608071d070804020409050f0c0a050604030b06010c 75
    0xf10811384016080c0d1043c21480041e9010925511080d80c91448004451000c0c0c1810842401040110319403405248400001c0c0840c0050b500d8000000b140c20075200244a9a002c2500c040c121200c403a0740e8003100340c20000024001272080b40007078241d580754035184d64004000d0700111291a01c0898841c03180000c0000301c1c400040802021b000752400d94028860542d40304203041c2551001070f212070090b41422982000030b500c8202c00000d03500141c00440055039402000d602e000700b05500780030028600b080304414440140001c000780e0321203461015182c1c64010040365207010500c41c003401a00180700c10b03c00325895400405500440d129200601c60f1a501d4450030002c0512504d2030072641c4403c20094245c0901ca0309000f801015500b00310342c0070b403018400500c000104805c04001c00e2400090441d9680d0348000d0810b5000b1080b1142d1203002c5903030b00d6030381c0c0150601070301c5800c00450014443c0303412000c42c1c0c241ca600c41410070440d200d10005640d2034040303210031210385c056281c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 535795116 1250 535793866 535793873
    0xb0c070f0501050c0c010e010605060318190606050f220203130203031605010b0a150f0c0807050a02040b1509100509090a05310201080403050912070905060d0f080a020109 75
    0xa95008501c0c1d41612035817044a45007150848500c80a810181d905240007042696240c0e42540d510510340c80e140c020344104044910f09140c44108070500300c0340c0c0c0000702403e214a644c0140280c860544280010504210402c400202005800c900d0729085070501c2841d09480d0300955080001407038103100c0c80c482540000d00756001000c2c04000711095024182c1070000c01d001d9010460801e0b03079107800550400020341041c0401c9803202c02480b41809103d1080e43c4107501070072942d0b4004500c0b68540c865451b1442e140c00c0e0000c0b040c1c0c4110300705910a01145800f41140340e48503c060405407a00202405014401129445410512000b880136004d55160340070041e20641044800040700c1c600400d61403200c00c0c00b2010308c451560081810f03405050550721401c640d940900b05280b2a903600e15044640e4850881510f0700100c403161500c1a40e40002040410381740d041c6800c1c08a0340d91501031000003460f140c006071280b18000c03094004201800c00801400710244004241300560340c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 535796366 1250 535795116 535795121
    0x20f0d051f02030609150d0b0705040e280c05220b03040312150f03081c02040909112e030f0c0c1b0326040e01080c120106030b0c070f0501 61
    0x711198600c2d80000801000380703410b1030130076482072220b003d11000d440000c1c0421f410106496004054440238000304009902420645008121024040d049860a015a101c01e0811840108080e0b541c00f4100c400420190040c1d2208880c4c59607441d0812030742c4256460304804208450345589041c4c8404907080a0040040d8030550007a201c003403c0c8040b4420240480d400030701c1c00d0001c1c3c942c00c00c0620000c50351100b00b204130b84c0c104140d60b4407030655048006000c1c0262010410045c80001c00245007185c540042c007849001d000120905e101010610400d540c00e0340d41c0e241803204e501400020402d0103d90b50000502e50701c0c0004241c1400a040011a81004030360301c0818003d600c44420020405080b619410070501c0056083d49150343d1b01c001d1122080d2030189002c40c000f009091000da003001c2e64002d01c141c819500195a6540d805926820240e900d0703070040740c000d00c4507030441c001406103d04070380d03102d0488551903855070841d4060340c1000000303c4a0040c0f00c40c0382300c04a5000d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 535797616 1250 535796366 535796413
    0x80408060a0221070c03050d0b090108102d090f080f0301090b1008160c021e010311160204200d0506010e0d020108060f0a030c0f030519020f0d05 64
    0x1000c0059a0302500c0000d5100481180622000c0105200801464550112a1400d126414104280c80d23040b0050144003400045928541000c904000080c64030800151008410038416040000c416140c044020041e288a680e04041c241c840a04034150207a90001c2c600d1030182c10b8140e210002a030300e0680755071192100354101500800144043c40d1280b04d143c020340c40c00c480c64042c01c200140068442c0c1002080303418050b10403410f0b5540300d4020f040800c5219070007403100301102da901d4100454649640c1c0480d0010707150292800001006904031407440b0307400f02c0c500d40610480c3e82040044c00c2140406c580d2004044210130040004501038410105064004104c52611400041c0100540035019100c0c51800e508500945d1300206060f400503002d448140d00140e044002c101a814580d1004200814500c00080c06186c4a0704540c180d0b4810800d8600755200803100361206060481c01960050381450308070041d01c1d0042400d00b8a070701c1b0340240c6000c0c00c00220780840f2100030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 535798866 1250 535797616 535797631
    0x415020f030a06030209310507090c0210050c0c03031b07020d0321051905040809060a020a0302070603021c0e0114100302130509030702090c12010605040312032708040806 75
    0xd03543d09000f10310342001280da001807030411910b8101d0035000840200b00036490400035804030b034001d0030280081440000040c01300b00c038003800b201c603031a04001c0d600c50078681e101940710b00d03000200e10741038014011034034a422001d00541c01c3d03840d1000c10071081c44481e000f902c440c1d0400c00a140c016100d640d24613908501940307410002210f20101500080c6149444004043c03405003042801c642c280708441c5030b8092280c000805940d00d10304801d691041c10700095100e00013141c1e8010b80d56002404090041c8294240d4003580d5403140213801741e0040261011240d82c0d100030b100041d4102d82d100881040200c400424011402c9141c90300c41c0c6010b039424070410703141e00824403c6d42000c00b20b100d00c07540d4a590400091070440d0203152030340910800280b28030015800f041c081d90007441074590012143c0071611440d65a8800a031481d8068403080707070310000080180305014068401c00c2500c24a440144030380c400d4480310320801148101d002c940d0a0000d10000c134400e101003200c3c611880300f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 535800116 1250 535798866 535798871
    0x60907091e0e0601081012021302030a0207021e030c042304150c1409010804020a0801021c110c060118060803040b030711030403170d06150c140a0b0415020f030a 71
    0x41880b407802c9040c005022505020500302400300e00c208600c00c000c221164041ca4454980c880d02c0000c0d181c003003009000d0005ca0011007845412241a4020318201c0e04c01c0744c00c8501010800c0d860f03284c000d20940b81c19410341110600042905284c1c000c1036009900300f24041c42100008500720307903080141e60584088284001c0d00700f00c0522480382c26160f60003030a109210010089002841c0d10074442860b04002c004800b25085440e039502e00000b5110101c0255243c200308138541d81900012003095542364244144160318120440031102d040446101800d90790707080c00c80800490900c0c8609143c1c8a83da00d10000c0e860300305001404c040c09030707050082d0380c9050145004240c0c125280e40d90540d0b4000308020400180703051311824a00c1e4110030104c3d294401030869400030240d0368001c2c07166640203c09000215070103103d00300064485d01111540b000c140d484035a40b400082d0b0b00070710480d00030022a000c81c105010850030380070460805890510324050741001508103403101c070002d94 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 535801366 1250 535800116 535800119
    0x31c120b06041814060102070f140a050303070b07020d0c0f02012a03030515040501150807030f0e2b12180c031211060c0304020f040b040614120a0b060907091e 70
    0x6104011321604444244014000c036410141c0d40c1c7c0b80128244034122030b0440b509545c40264440d440c0070401080b00a040e2520344071a410100c4110038112040b10050003098000c001081c0100303001c108a5130017808522681c8081d50064544200216040105408034821043d07918400a04800494440d94010a40b4144101400041802984410b101b01d0816005105c60828205e10400d000342c01d1900e81626100c22109030010300384400c0d049815400d00c108141c04560020300c0e00f01900340144048034000c8113442c00794000040161510014a94101c800803800e00b40c0c01c0a4240b02c107070f4a1a400d03041441c0e82c2d00090b4100d41d0320440d910141c1d00701c02c0c80b0094104500f012103c000d2006070a452900603000c251038031001f40001d12900f2040081502621607904c10f5426200241c41085200d8071141504001c0f0800380741284100b0300c5c1c905103101c1150102c1c1418a0f01d074442403194150700d170340c801c024020100030b20410400100c40c00025002c806e00c880102c0c42c038071103c07800e041c0300e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 535802616 1250 535801366 535801391
    0x11030711091306050c0901030f050c0a1b0f0c1806050916050c030406090812070f03350108010c0c020d0803090a0b010b0a030b0306130b090f07090b031c120b060418 72
    0x1e80b0203c0c42c13103d203180303024108422f8120a90880300a0030341c038640002140202d440c0c040c910300c000306000d0045401c5401c0d40e010019100321400541b50041700c52184880d49a01000130f46400340280c5401c0610380d004101c030032214401183c8404030070305040e810925010011440d68006510444c0004d010080030040400180016464100c07a0243d85182c2643e44e02e41c0f1000c0031444500a04010b51030100e51070b0b60340d041d007000800d581c1101c109501c03481c1117050080301c0142800b44610551810b031040c0038450041d41e00710841c940c0030b0051012018075455400c1c064100500f0403070207010300f21094000614400303605010f00b80d10f0041544601c080d007402030864000700d0043c2d000703034884000c0c03042004002054080080e480303032404996a5401c103102e400c044135100c007000240b0840f803010950482030b80000c59501d02c01d40440d0b02a48a100e0101603a4194052040104500c04001c040288003600107010000f400360045161a0f510045500c2d2031000310220200c0e90ba8585072035820 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 535803866 1250 535802616 535802621
    0xe0604030f0606030c0515031611030a0806100201140a1109090c0301091104030f021023040905090d08130224071a190f06050603090303040311030711091306050c090103 74
    0x160000b40c54001c80020308401d542402c8c8800b4100d45a640307404104006038504c0b0300111080b400b194815a03480e058483e01c003411515084d140144200450312030700f513525205200780300402d080c083d640e58090b0dc07034132580001042000b1091452901c06c10040b41261039110400f80108145c002c2d00d50340e589442102c2044600b182108480080300700810008a0480c0046504031a01150012042c0900310007e4031904c0d00c0e00c081c1c40140020303040e0404541c0251000e00304076040c030001800a41d8a0f507080301e480303c2c6864451408103000d140800e09031b105400360030030040d01c05016240c1101e83d512181c0020881d1206520180b440098000d003045414040018240e07081d2100140e142044504e0169400c41c18803190005650f030075070b0403403081041d0841402410b001d00720230360f2030a00b03c8079140caa031701c11601903000c50500c61074551490000004c0703404007030700007000c0014007803410100301410f000a062841c00c24001424180030803894820103014545442a403541d441140c00094203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 535805116 1250 535803866 535803869
    0x6070807050714011b02040513050115031109060109031b1d01080c09040c0b0c01091a07090806040320010b0a29070b01030b0709030f0c060815030d0e0604030f0606030c 74
    0x1005141a81c409141e021700600d4000310ba07040b1000309803035a4007800c01c0c6c03041407031500c007902701d40c00d00c80724105d0017403281c0d8540281d034090500c8990083d10b03441030040c882000d171081c4c0d000410340d0000701f021800031010000d4481c69503d9042007a80c0d40c6800f1035200c40c42804111100e5884401000700c0b440800445542c0b00741034440107501d1800e034440700407004a030300c100c0c0d552050001d11400d0f050020b500c0020381a9200c3e074005c0090380001c5103000002c2045a0b40700101e5119900030544c5100007a56a00c56640340c1d850316240c02d40800c9800040c541c00028140179901c070f20300309409a891240c3c2030041c14411801447c41d80703000c0000e0030600008041c3e244a0201042a400415149180c180c192900b010384012035840310242281e04156952000e00380b400c041e00c0c104100007560140c2003c03214599660030311525144a00750034103440d040020f0b8180e001c0a002842180514070040040d1001071000d8202a920b48880d80c02000580e0201c0da200e03502c0e40148200120f0101503030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 535806366 1250 535805116 535805119
    0x51c020d060213150c0b01050915090c0307180e060f040207050f0a21020a0f0201180b03010305010c08070816030b03030d0905060c07020607060b0d240b04020c190206070807050714 79
    0x20310070304954490a001b030206000d01405402c400c030001c0c055102c5c4604030007803894003500f80d11403844c0686250f00749800603510b480001c0d4040600c5061907610748548010b884608230600c6003074840760100035070009030180243d04035409000d02004100c081c01070007044400b410103840e8540e00392814690a20040b40403895840240e81c40300c18040c0d0001c0d481c40865030046803c00c01070301d54001613072a0040140c0042c8680d007000e9010a40d034907224051030483c0d220b0300c020f0055040c0701905440c07000003160200006408180010300707055545c0d91ba980c044015041c005607010a210109013180d210a80340e80049884007810010010100403895005545100c20303414040a03500082c218410010042c207060b8482240000076a100c0070501d0120754004a54400541e803400f400c16089030b4400302d01000c42c40c0414402440c00d0900807600c01300740000162540e070222130750000005040c8035003a40c224206100c05000602c8120051850328054401030212520f820201d6415881905426 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 535807616 1250 535806366 535806377
    0x9160f030510060c0215160302070f0317130806092a03030910051903090b0604061406071104020a02010510060c0506241e100504051c020d06021315 65
    0x194000c8000c042c1802d4540c180740019030443c4500016040300d8010b22040b980341c0f000220043e00600501100c0d1f0014469000e40b80d80e999950b09c00d1500030840e11024040d445d50303140303a030b8445e503e0f00010810507040c00c0302261115118884d95181a2040390b201800d68441c1e0228210003a4110141d544500345c03c0b500186c213651500460b889001722202d86009050b28551034010f14056000d42d4401c030710010447c3c0302070140340802000b4003a244c4040d03500440103c04504281441d00444042d81d00b034881500032464601d0610080c2d03840303050266042c05079400c0c05d1445954500003010180364541c004581810568203e405181072030344034000b4440c0040d0b104000801c00710710070740e0140700394120302410540e01c804140310524018016038800580102c09906032a403043c0c81000103001c0d5500c0d05000b00564094074035109078000d640d4810700c1130880c041310383c04c1c0a504c001082d2002e400682c0407203556564109903040469005030a2910b40d8061015070090080105000c9891030310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 535808866 1250 535807616 535807621
    0x51605060c030a08130b1608070e010207030201050c01020c01090f0b060904150f2a0e1020032515050601080406150b07050102030a180b150a0509160f0305 68
    0x8950740740b00e50060f010a200e0400001a001e084003000003048a4028841c80d40c2d9107080380e8215076801c00c170825070001c44d2a10f00403403002445083e41340d47d032400c1078000f00f40c1581950010356143c0c00c580c84049082d9001c00600128031001c0c01018861072051010041070202850a078000c5c45000344407034004c6084504000110360481e2001300340000c2e40c9400030781f8030011410180948400c2c0160128010700c07101c1941daa06100018101c0a090344d900e24058400050810450805c20038210300005c208100031002c0711141a0240070050015040300d00d803000e060280d2041440110f41c102219081032122000c1c4411b05c4111807030028807500403c140d15103140060102040900040c000795039501e0010102c94a42e0282c0015000c607084031a25468146810f42c044e51007107981c030820724200500d0380e11941c8400c07480700c1c0c0540c1c0a1404074059590a0341d08031001c00310701c00790360300003040000002c0f5512940941030082a140d00125601341080002801400c2d07290406010149007108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 535810116 1250 535808866 535808887
    0x1906080d0c05120c0a0b15060f1c050114091906030c030605010e2403071a2106010207060f0302040504020406030609053403020f0a020a0308010f0b0d0902180405160506 74
    0x19070704000d59106c100d0305529291b92090140c4d03000d01c490a55005103000504d48014010b281c06002c0c103074190101c0d100ca44d0384112200382510428800c0c6489211740c101040c510b883c2079404268445010780303441d0b05921301c0d854410107a902c9a4805e45041381c1c1c00a051061100f240200b5014091452a580050800c5203007d08401a52401c0c0b06003211030b680e0005081d6820701ca42c60041441d0341c0440c01181030314908841f298070050303c010b0a07042d190141d07801e80034003108440c41b403641600178010a61800800361800c1c0700c2540c1031020540d00b00b0007c506a41da03440038202070002c50340d00123003060030708500b01c04848000c0c040700d00b03070010b0200c84182840d4442000e002d00c03070950840c0c10f6181d10060158041d00070410420b1303440001103000d0564030b0703000038030044160282d586e5003003030307641c0b8403000c03036403007094004d03100c01403000c005516522800750482d584180c4041d101c6800c00d111096603d1801074140c0701110283c0001004840c04102e0070f240310050801260014a44444102c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 535811366 1250 535810116 535810123
    0x3031106010b040b03220203161401030917070f0f0f151a0f041d0f0d080f130c120516060f08010306051f0e06040c0c0b1906080d0c05120c 61
    0x101030116140001c51204204000ca41042c1d086c01da010341110401c01c0e0401c24252007140e140546c00000b40c010003108020f601c24010300c3c40c855040580e071600d0b4080c0408021f0280d02c0303184c1c1541c07114000e103080000203050b0240040004d001d0391000683d07825a1030042950710f036032140704034018203040030080c0a4880c48607071038060303408541541052410101140c01742141780d58100c0188594500c1044078140400d03004082d020810694407001c48405003524007500a5500d03554000488002070700c2c000566030780307010060060707140703071740c80e0ba61038601415013000700204940582085114900748e42d0142202e0f805028a410000a540d8072139800602000051102030851038603200415007407850001c0548103960080020710f241074440c02c0200c1018802d4506c2d50242d0b20b04184510300c544600020f89085a10008100c2c103601c0f1500019014941c001c4981d10b1141e48190020300381804000c003401088603900c3e0101e001919090107410a080380060746003012081040c031314640c2e07020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 535812616 1250 535811366 535811371
    0x30105060117270a0305040f0f0609030803070903080d0c1d0d06020d020f04030f150209060423040e07050a080304080627010606090512120301060509011803031106010b040b03 77
    0x72003240c0580030301c42050f1400e05220782c071410124080e03c2c03003840c10305902200070000c1e035411550440695688000100c51046244280c80010b0248402031001a10356070081d43c20400307074135001d280389407251640b01142d071007003101c0b80e2020340ea10f54500f20141c01140d4001210740c40e844d95886541c0080100341c20000580c4024080d03540000d414031010700550585462400b600001d0303403265101d00c0e1038101220b12840070344019241440d00000090305008840c44e00201411031030401d03240011044038900c10800c40203400c4140d000c040c0440c1c03614410141a1407281008114179032402c000d0203071408040e0407601464000b000309201c0814000741854000c42080b45d00c080d00f00d24080340303035031060062481c0d4085500385040014510f520580f282c0c00c0d07070f404607040007000145488040c1e50300c030100c191104101c0c0a0004202090048001d07103070364001810189100054030980014051894000702c010500d450207054801d072042010358003511000305000e10341403c0c06501e06090000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 535813866 1250 535812616 535812631
    0x11b05090d03021f020c0f16120204020d0e010b1302030408040509090307140706260601030203060111030d060924050f010306080313030501110a050d051b0d050402030105060117 78
    0x316407004051080103414120a013800e10030701c1080f2031a0407580070b54850300030303054a441016407c41d101080440d113a4032980000748051805450000400d45040c07500c00f041c1d0384580d00340322900c0904628016a01d03090360f4100002a0300721000d08008204030308903510541c10740b040c000c100000e24084100d50a41e82c0841340608690f545011840c40d5110780f94004114902864030707103c00a9001808005a9045450b80d03001004166191001d80403901b0b201c140f09407844011410550099009607042101850428034800302a40d10510f994030031020321101075075640301008240d89030b204002843d0220021040b528a035410710140c4030855015040c41190070900c4c11030641c0c080c1e80310400400c5003605032915051a0711003030142c0e540360300c401e450740d500304010038a8aa0204084440304440e5455580c2084a540114402898010240ca03891a540031003a10b0700c510340ca01424103018019804203891034944140340c296100a400e05041c005d0500c1b41840a0314007403004ca611401d07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 535815116 1250 535813866 535813879
    0x51308040b0f04080d050d0b15030a1a04060803120a05060603150d0b130302060a020c151e090304240801030f1a0c040801420e0109060503011b0509 65
    0x2442028400e02e8461903000c09141e20600072942d82e0750341c00001501c40161100e0041083c0075444041c003810450030060b81074003440400024000401660150340142d10134a004020075000e0741c042030407a82140c0103016582e2002c0345500c1d0340081a040c0607031009401600f071150b07003000c0c00810300d0341c0400740600030020f01e02441d00310342d91140728400400b81c3d0400c5045020f800c1489c450442c1c44c41000c01500180903800005405a210713000b00d4400c121220000c000c2582a003005002d842005040016004210b1581d00c00244100e11200d0240c0307003200103159100c0c42c212543ca54004126a942d000048816400304910303040003503541100d8024600030b44c10529840c01e2016a2124034004904900d81d1060003940c3c40031a0240017070751107120003003114035102520105c0740c50082d5144d40c003402c10701c017a507041000620050081c104000e4500303e80103440715004010030327070700b40c0154034119a50030f010049403609010b03803810b8428200048540f950201c000074958881c27120f01601610 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 535816366 1250 535815116 535815127
    0x60609050904061e060510030e0c01030b03030705070303030e0708070612050705070c03050106050111010e071401050d02031302100509010207050f0609030709020a2a0f06140a0609051308040b 84
    0x43c007a0481000c558100110300a14942c14120200506182c0103883c003451540403c0c1c10300e58068864100c01000a02c018102d42143e0b0f40110040d0081201d81074040c0814070070b40380042e10400030880a10b00c00e13103010030303602c0c0c0714407640e03250082c3e944c01850554080744041088a030005007034072980f01c4280d8003044541e9040f2080d6014810308000500f2440d101e4000014408198081410384000341d882602e200b00080c540340c283e82a541200c90b1542244104101440e0340b880c080c4942901810124144101405080201c1c2c00407204085a04200b0041e40118039218a4002075061141003140c1030061190000b940c60348280030b07442c0204203d150305032003560392006482e4100002000c440c17070750352603050b4031010f90000245e501c00f0468a8000021005007003414000014004d80348000800e444c0e101e081b00c0c0d070b101404c1030711000e540c0c04099034000210341742140b044801013804104030789484007250031100010f000c5039400002c50048400100c1400c129802c80d001e0a00c41764854 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 535817616 1250 535816366 535816373
    0x9010f2a1d0d03021c0507080415020a021807020d0507031b0809060a031a090402010203190e040608060405100b151b010212040b07050406050a1b08030108150109060609050904 77
    0x20508034070419400340304842c0010825a000410308401080c084800c4000b200050061391030b80142c1c000180070300014041440490301d1055412801d6200d841240c01800203a00400c520100e0380f00f9162850401c141086101d40d0104200c51210030b4030b01e05207203400844c1e10020461f503550308040742070095603117580051180b09004d4400a000040c032190f0396005030080580140201e21031010700f100d6991172800c10340b411f0b07003480b80b0070f54040e0041d5140000e01c180c0b10380701048855080c1c0a00101e0069070810380c440e4480c0d080071389095030091440f8206424214645600b030380c152459030781090700c1c002040c0c5031402180007150341c00001d9a02d4080d51820002102c4103407241031800d40c40824910740740002035000c00e002d1801000100307042e45518504842912560080d032000c141c1c01c001044480e482407d40603180164840c0501008400d5a6070000550081e8849841c40d40504034542441031104c10150042c949544100306140c07034246c0280200703c0302e01c2940d104501c0302c4000717401d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 535818866 1250 535817616 535817657
    0xb010b07030923030706020c150406080c0d020c030a0504080f0a1e150c08011a0403020105030402060d02070c0803220815180111070b07020c010c0b100e09010f2a 71
    0x80c010010141c84a5540b41d1ba0007d50f40d52620420510030b40b4901141c03c2e90120580440d400c0d1005661760302502d0303840f5400390600d6800785c4040d460841d420410303c20b99040c180040d01d56580d02350750303a6030303181d152403100c03854403554914414403900304420074000200525545082c19a02d86800500346001e401c066906140d440d4900300c9150070304504400580c4e0101d40306040c1c039022082161038100e40101c00301d01e0f00440c003009000c25030400205015203000c030301400e40c6000750100076140181d141d4900c0040c550a6005101541c4042903812400042d800c001c481b60f40180c0288120514201c0711070b699000142d0b0419a40114401150119080c0da48802c64903021100030300041501c02c1c14030101d584505002c2d1200070100c000710310b580380b01003100708501c0c0050b502c03005c0701900b60b12400b000c100301900d0180c0130380030300e08001012281e4025081c4030b904c00d00b000080d109000103107041500c0c500c440840800c02e121110761112508448417840c540312618008d01c86040c3c83da4207899 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 535820116 1250 535818866 535818929
    0x103060b010314130507080601030302060f15040905010614040207020d151d0304030b0f19111c0b040608060603030d09020f06120a0b030f0304060e0301061d040b010b070309 76
    0x11046080081000c18804000344d050001c1c459000c071303110b15641d40e58058681c242800010010f81010010518424100031015005152150b803143d18220f2a00000c0898200e9141107a19945580c01002007856903510300e1280c490a8405500d8869113600040240742640f0703009244d4908691452480500c40c1e10810707401030b8180000b03400d580780c0b446451303076600180f0040311a80400c20000b011501c5200400d030180c410f405103120725405034000107010740103c50b0350302c86180701802440e4041c645030010352507006d00c035040095072080c0750f001d010981d10690082c12980e80640b00b40116a1800000c83d890f08140c05000942840c40d4070000d203a002c1940321441d44101d020620007521064a1503660140c0c04542c400c002800b1b03184149611424103100d2682c10f07820500041120502850485180900003000052610b40315003051441c0c282d1040c5104401003175004000070011620461805000d0349051b41d42418403d98009010050038011480c607403a511501241c2800034032003011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 535821366 1250 535820116 535820141
    0x20d06050303270406050a050603060d080d020a1b020616050705130209100212040527040804063c2c031209030a0b100801060b130603050603060103060b0103 69
    0xe54501d80009002070f603440c08044030080350310004011010b0310b403a22a01040760000741c1070424207484c141c1041116000102160b420a00300070078240001c06040c0285140c844e80c00340140c071031529910081c150406491010004011109403c003da600d44003540c6508a050200003031f0b01c10503290082c00e01c070035580180c4d003001c04003080c0302d0021842c0e0003400b210360302914540b641e01c503094801c980e00c8011030104103105400304014841810045800c0c008045001460344500ea05d0726000e0780090400c840a440340360b00402d05200d002e501c02400040006503200e100340307860020341c2500d01c1d0b02170b001c2c8048142c201419411112401426000c00d02072003912601217004042520004503648a0640b0380f103030081240004800c00303c0c40c141e40c00a94040c000b4100c441c200e9036080702c00907000c0c242c480310407545a0000782d648800d0040c3c1024210985d1303400d4072000858050304284500e42c004505050410b8100481034500041da58112030300075601044000c900401a40288018481072 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 535822616 1250 535821366 535821373
    0x18011e110f0c0d03050606180f04270204051e061c050a060b0a09110d020c1513060f180204110904090c0833061909050f28020d060503 59
    0x40c40d00c0300010803d0315440da116102445650740325420004244180d0140d5041c95100c1503900301c25040c050398024003180081c00006400e410065850b0b440801d0000815a80016000a8085050500441d90040e40c2c102c080401c581d40352070588510240203200d0740c06403541c552000060410704e0300d68481e0302e8201c07050300c00029035403c1c210094001c03224068015520500700041520983c820043d50001c50782d000b90074107100e001040c001e036010a40041c2144180e8607001c1c507001100340340d1070043c403a02800031284203a510f00b11013a01c0d8085103161596107080c20f499007803030852406007103240e4101da00260218034258501250700507000c080741c1181c80c00c2010780400c50b100890605440d400f00440e4030032111421003500a140f44035010070580c82c403001c45c2c0d812050003100e40d50441c2005003050030720909a007032203e04405a51102440c103450f41c092000141110a10300c1e0020907000c0021507804000400c0c020118034038030303034607045940042e03d006d10074880e81c031001c0940402000d9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 535823866 1250 535822616 535822627
    0x604120504181d030408030403080f09030607020312010503011119031407020709110708071e080d09020f2e03090212010c09091406041a0307090518011e110f 69
    0x4101c0101904410140c07143e40c4440d106501100c00000e550480d20240015458603003542e80345160340d0090b64030101804c60078400324100340c4c2d003440703110700c84c0d07940358010354503003108561141e045107040e88008c0c0640d241c00c3c1072071000d00c00442211256005842800d00c02068142d0882c001c0105041e4416004084814000700710307400700348a011a4981d40c0c0501c01c11880c11428150f5114035040244002010024400000d050039600b4420036550f102c1c05000200d42e4441c80001e6100d0358440e00d070306607508024011460900c01105070a0003c3d100d2030891000c80c50075a4a005989820301d03007030036460034100c1600b4071a811401006a0150165241c6290072001d14080c0280c105040085a544500070071042101d12419144100c00f1144107501e4443d842480020301c81402402402c0f00c2007424803c458804000100c01031001110011702c500c1c0c42010311235481058500503040ea410482c0303030480c00407001c4801c00b80b807000038000a0f8462105200301024402c00d0b41d46080c00350003242 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 535825116 1250 535823866 535823909
    0xa08180a0309080d18060c0507031704091407020d1206030812100e130312060b1602040506040e0601050906011e0f0e010905011b0303020d110d0b090106020604120504 73
    0x4500080300c05103c220381d014034503001e0688000701504c00e5410900c040400403c84e4504c5210110012030040083c2c586558a03929028038041245201d0382c1e14100c00281044001658400e246001c5001d4611041908124000944400b01da28030322040213200c2e0b1003564030900640c00b0310029a440300361141d031913540c11440d14500f54221002c0c1c1403183e20001c000b40b0a00e160740c01510615041048041d4042c095030700340e4030120b5800106030101e6403000c0204e4101c024070300911140312500b0740140152081d01c104019034000800130ba000c0c40c24107100c070050b1440000c1c59810b44800315820041983c805004990300f242e01c000c200a0b5002d40c240204400d50080c00c0303000f1020060742e64090081c0c42c240152102101e03407147c9030005500d441780031000d429080910480c14400d144c0940b500b40c003150285c00b51030441d80001405003000030195002011482906410881a18a110290301d03103000652501c0380108041c0541c14100100220140703e101180d001c2c1115483c003010380c200a0a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 535826366 1250 535825116 535825127
    0x3160b1005040b180a0b0604060203130b2506140f0703051003120e0109180e1510121509060506180c04050f031218130606050a08180a03 60
    0x8450341104128100c01080e82d0409005800b11200050240e1191410300402c8100f00c150042c540340c0e62681da00b24943d07042d9905e0300100010a0280c1c0155103403484002d001000d41c0300303a403100403003060401400d4804502100380c000c07282c0c2c0443c1c00358900041420804054180c101208288000030420400c071701c001d080810b401900180c0e400c00c07556980580c8091218014080640306500d02c41d10b00ca54248071f540a004020b4043c54008001d40d59005140d903c02401e4141c070840603110b5102000c030140c104030201100c900400da41d481030402d4440c0d0140c0034028010800b40d1180700e80c18805000303407412009190040480c00b0000b003400d0381003407401080f054034443e04c02c0340005048142072084202d11400f8126001c102c0d85014030301400c00c564000c40c00b25954150180d252000000403c00010b040c8808090700028410031075002003005000703c440f80c0001d001e180150030f01c551039008059510420160070b103484161035a001c03284100c0c00604101400e4445c2002c40c80401d940700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 535827616 1250 535826366 535826371
    0x6040e04120c051507030e12040617160309050703080c06010608090109210c061d1212071d0907110d090e1911040602071d0609130503160b 61
    0x1051490001c280c81c620894295074440005401c540c0315034000c2094050303110740c4c0c0f5041561810b000500503186040c80b400d1404440051695000200e020002c0c40d42041c1c12051a0b10700da41310003550320380200c80c42c0410036250640010580c1c5c0d03002581c20000d08001480180d42c2103010251940740e11308010707a940700e0074010400040c0f2000081646660305024040300c00d031344052a522900001080303103150b2035052095404000000d002d61021940c6403240003100903c61181c009c404000960b00f0745054071001d490190080e003000013112000442144980044203490961201c00b280e042c900c050301c90303000105a22026000c18000c059800c500002e0018030030078142c4000460041060366100c40510911620351816000107020110f00d640c0300031450004440012403070744408582d200c03038109800000242e4800700050180110174400a144003400182e5440c062030040003080180b0380191101114003c0600c01d081004424800c0d1501010f030400c80000e01140c07418140403001e0305 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 535828866 1250 535827616 535827623
    0x70306050c0f04141003060e0612010f0f09020306180607030e031e0d0b040506030703020409051212090f0304031110023405040b03120a090504110c16050307050103150506040e04 78
    0x317002c040c40c1030f00d0081c06203008031012040340009542e07940060110a15906480841c1c81d50b80714100c0600c2003881c810f07801e000c1c41c94440010180001e1042c5441e00001030101c101c09100b0098442138064000345080d40506189000f00d01e0050405405103140560440200d4850034450705100e11a40f000c080c0c07200d068000760034404001c40b00180b00844000341d99640e01904a0001800581455002100100d100e04101c6600e0b2140c0e41c00c070641034001c245a6103407151510140400350004012000c198560b500245181619603030310440c4491442e001c40340945012001d003e020760082c00145840b156029560294403030340321030400074660b8180603002126030b650000c80c4c01e082034443d00e00b09007400b60003001860f649911110300d580061041d94108510b11001007219210307400f030b101401200300c00b00380d12074649040b454280034501c52002500e5402c40410802564005026012070700c0138200060220a00c64040c00700b02d1146d0020b41e0072031400540060114015106248510701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 535830116 1250 535828866 535828879
    0x705220b0906030c0d031850031606030f0e2404150c03020306040f18262703030301080a0828080f1305070306050c0f0414 54
    0x6064007084004141034400c41e80640c4030014600e12820b146100707030b48081c02420044641002d031116411100d200f07411001c0e00750780c1200456548042c56603112030485a000f05400c589030700748400d290307440e86010140c00445400c80b540b40a51000e000403400030441501141d80c83d9100c0b84040c0c00380c010700184000d81c910340004d40c03170203203004640d61182010540e08a42c102c03d801a03a0211008050003d5070404100c82c0d101c05608030a100b8940110704a450140e140d1800300704010441f00d10201c1000024101003201006548000c080ca04140e070005042060014140d13401760608001c41803a03100c1e0000042442003100d52a0400031b4205030900794081c2202c420050503200d00080c4100d520f940d202d052500000b8020001910402c3c407d20003104850000703040300303c100d00d589103502022680310802e10003512460440c490340308810543c8800c825400e40e840720b83d45d00c658400a8219903940d0046416031fa0352500300c880ea03081c000036080e02da1751114280d11f0100f4030720b1020342c81402d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 535831366 1250 535830116 535830131
    0x10030501030203210301090c1103070f02031225060e01060e0414032502010c02040204062006011d0c0c0d0504090e010501050f130f150905090120070302070522 70
    0x102410541c0781c13000700c07400c2e14210f920344008440501803032180d403c00e00412803520001300b07400300003130309140d802251141c40505141c0103060908500c42c13500c0902c440f08011400124007504a130501c400450784201500c01843c0c00c00302c0c014035010000000315400d0120000308100c0c0000007500a0740545011240600000c40b017603940d20a00140c05000a40c0421f99008000510422a00240103062400200000e64001402c03603209804c1540810300a03210380f2608552042c400700100c0c1c0362401490039504003020090007010040600f21000b0b900750026510b0204902540e8404401008480b41d600e01010098070642040c01941640e034513165140800440500426040301c0000e04101c603012076038014060080300605c813940d402500c0c0d4800010108035442402070000014000c440c404d4108444001a501c000d402490135a0518490180014001442e52984001c0105165444103036150590070f002480d80100d0b40552010a960540c01c242090b10390101c01c18501041003a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 535832616 1250 535831366 535831393
    0x2100203040c120510140702010b0312041e08030a090602060709120206070f05070b0903010605010e03060f060a0807080102030f0a150303050a090806090a12020303150402070201030b10030501030203 87
    0xa00007110080e014902090701088201c0182070f5100d4241e00981c150740e4484008101d40c000c5d5048240f81d4085c00d006182080541c030745c28451089800011800342c4511303c003050701d0310b400380038500030020f069801d202c104a040c0d5050391031100510070b090959032583e0033307102c000d0a61801407103140d015029940c00101410302c6100c854081d502c94001000f501041034081c0680d0b90048801144d0440c07a41804001240c0104551402403402d1540b80740d48141d403500307150079500036038400c9052000890743d0440640d00818656441070018844030301503030318400060b050800f540c0c03058040c2e01440c4000302e40042c042d00298810341362a95080103546401070f00744100c81c20500c0c00203100c10168403d1000034030510042124072158a4010401da45400b661410000240c0341403040c0d0b0302c920250320410062191003092614140091803d51a02400c0119144414030406200b983d000806000f1680603520655003284064040020130340350b1030000d0010042800181c0c400d202e400b00c40e5220 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 535833866 1250 535832616 535832621
    0xa09090b1b0a0c08091306050a0602010e06010b0306010309080a0c0614070e210114010305060f01060f11150a2f16020f0607080310050415030813170c010210 69
    0x468030761401a501d45041d1070012910003851140465607814100040481030741d03141e050820b81c01c016403001400601c1d120402c1103840355503201900f0341e41805401441c075100460640d0443d01844211903a9503501c034012002003d18400c01001000e020400781e4040d580441845002480342d0f5003040895100110b400c0000400c543c290001090090b55071118100014000c030f071160501c1809401d14040480c050030360384201e440c8000350442000420a0080030002c80b600403500004801280d41018402072100011004160900911102131078124404002044280d19460246d03805410564110340180504082d00803402d020380c81092050b440c10a1044900283c0c3c4400c1e40c90141c0082058050315100c4100b680c1c080e51110344d80d075460719006d008007070f0b139813240000c1c5035617107850309044400e8003080c2c120038040c51a02e41c4420303440c8002a980016a0b40011205482c0c0b41c03c41c0c80c12842d0100742c2c010060080100d05d42045c450b00000d403c1e0b0010400360291942280c070403c61008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 535835116 1250 535833866 535833901
    0x6031412040b030112030c0c0b07050c040b1f05041d0619141201090507081608060601051e0c0d18081504120c051903030b010203090a0b030a0207020a09090b 69
    0x1942c0080004200e030362005050503103820702c07d044c00020490142c8805c10010303d9544100c080b4040011070b1000c201050040710210308003202c00300101c6041c440400c0155081c4d10480908183e030014103e038082c0100300380c40040984280041e5481c801840389406400b081d01c545004146080c030540b06001d00646c0003007030b56500140400ca501c052008c010500c80c0c0310025400700c1d5038402141c00480d01c207020080107844a00018402c14010300f04501c20854283d01c00d040b190010000d003d00c40e07902108550b04055540d20252400e08400d000540c18071030f03040000407510070391600341c0525801c039020110641c09054084200d40d0b45010700d40e1212419140441c507200024001800150003183d20194005185003014103103100c4e0303440510705140201410b00c2d1500c070001c41c00800d035241c00351a0707200500307201840c180902d07140400d00d540d195029000030b0500c00b0000414524481d4142c403a01e0360024011b10340d240e0f607070f1100c000404408205451020351040001d40a0003004204003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 535836366 1250 535835116 535835129
    0x908040b311a1c0c09080f0c010e12070e0a020405040c080906090f0304090e150406050f01050a031e21030e1203060328140d02100b060405120705040603141204 70
    0x210301c0e90780120307068020130f040c000300c1d024400c403201c01050f40c0000300401c49138050420700801c241441c0d60700141c51640c0c0b244071141301d215203c0d160680c150010800008071108000b40d031015455600c1854080d0150750441a0000c0c9450800340c1000d0388900d5660041c0e0401095a0142e00c80608454907000c1d110840000d5500400041101062a62154810004110980e003000d01040301c80c080e100c0d8103440a660036904c40b0309000340d035100345250303500500048078400310680c9103542e690700c60140301c0204c10150b43c64519010070b00000c01405601c3c51600b07601e1010b814171218024004181c0c0d030501807110306c2601d2522520500c450300f00d07400b0f008003c000300400d410100404002d5100303040098030020f80111684001781e2005000030140b00800301621800a41980081ca800c0c03030401e16010035800e15400003c1c40d110141118140c40060700d052086584c011101850081240c0c482da0300945045000070522220305140c5d1014606801a40d8502c4502d001e00e410a000c0c901500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 535837616 1250 535836366 535836397
    0x90c130302060319111c0b0d0b09010905031b1908040312021011040816061409010e120102090307080303091506010e100305190908040b311a 62
    0x3480503140c400095039201c00e10103c0a0386030205071549800741c0d0191981e08044000116520001b0002c805c0055070b58004181e041125804410010310b14880324000a40b00f4444007001c255554000e410003186035030000220795135140101d00021240158a1098016004441d1618040c44804143c141205d8000181d02e0a042c02d5455540040562454500c15489240c4c4074001043c214054288100143c00880d81c99901e8880c40c46d040c48898400e05c2c514011303510303090001942000750522400f0107040c440746c9500303041006a404410b0084030075030002e528001d421021b0740540003400280c1013a070664214a907240d02840d624003040d42c0c8180c09c1c3c2c00610300b4001c1c00c0c4110b28480c0c0d11410524082c141c0680c1c80f401b244491610080150009481d501048800c1001000c2c0d4441c2ca09244070402c0312270b0007512100b4036401103000313a03e8010b03000105d01c120028030401e5403010720b1918180103d42c0e4041c00000f940001d0600c6040324403180e4101e0a021007603900251141e208034450b65 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 535838866 1250 535837616 535837619
    0x1012020a031407090501060e01140c0703110d02040f02040312052803180506040b0105030c2214101d15040c02030c0d030e0c03010605060a081017010506090c13 70
    0x20703030302d080312240c16a807a2407040301000a644400707402543d00138949512004075264038000010010040c95109030404a82003008090032403001038184201da40000050194540082c0010140050f448000c0d52003814201c044c1d0b1500d809034018802c4a10841c015450615009010b0340c45014841c6094100403944602c581d00c02c00062891040c00901d180010702c807129800d16406001c0b400000b5036083c0c0c0080c08003c104001308585501405084000b401420a200700103029811100072685505c00b98249802038000c0c2600583d6400e007485525116501c0d048042050b56503003031007550110401ca4080c000c190030340d018424090064514a40c400003194828030002e040c030801c5074011880204051041400140030380c0c52900000d0781c000c2030300030201c601307076240c5100e0050161090b490080108030642d00c4000711070383c2c10002c0c10990040d55a1503e86a4202020341c0039600d800c070800d8414560306010b5025501c5410101ea4521071503c070042e600f1214020400d9803003c0860300fa10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 535840116 1250 535838866 535838873
    0xb09060901030609080d060e06010314090a030507080408070602030d050f060904020607020a1e05041119120906020f0301060f09030c06030216021903050706030905100c1205040b1012020a03 83
    0x4400d03044c42c054070303200d07141020154400b13048a2240d07016906c407540c444d0a020b410341e03160080c046400d81450004040e410500c407440e0300d032400001d0050620a0000d203813420803030702000340e0300102034000071744801d503988100194599100c451006c420914100005a000f4107000030039018210103001c2c811187c1c0c507a0700f800003580c02800d080c0da1110016a00107200c0c80001034031100001582241e020103481c180c207100c19a010440010300400d014006500303000300d5201c00b56041030840c03030104800d82e0b55480c0e410050071854000351081e4000980d40041404800c000c50490b03031590b994034001950fa250071940f90410f0700000b8407410080808120b280c0c400d4000d40765966070b8428581209120350300050344c0e001207041e4070001020820007042441401c1c001c4100400050609100d40c40c4145d0320b01e40c0350124080c4850318a030b929510448014882d00394900c00b006021000c010f203040070700b0164807004c8101d13070340b41d46050039000118a00c60309860384040c0301c0d4060002e1715003e0940c0d030f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 535841366 1250 535840116 535840121
    0x10f09290102010219120b010509030c0405042d0c05010206060a06050c0c0a03050a0c0501140a0f0c1a22020d12050f03010611010b0f180603030c10050a0b090609010306 74
    0x100c00c0e0440d902407051040f4440619589065500b40b5142e40100b04400500b480a40e10101c00b15414010706111200740ca13200814107410f200c0040340c0016041c0d8641c602640c0b080340b0760400c51044030f480c900f10b0358195114020650054003031200d10709160343d50001280e95040854410781c200800220812406015102802315181d50505507110b015020003c11694405a80203031010351081da00c07903050044130303405500030304001c0c40c00000080d85010140558454a00000d0400c54214554410f00788604159400954000c03000054803500c442e552100c200d080d100b09008102910701241100740d9110740c0c000749503000d171922140210686429104000001c0c5850a015003040300740c00c1500b1500055003c0d040c2d41d1941c130b0540d545600301ca401c403080e604885001d9640500e8203c50b6590b8801904242c0d0000380f03400e41141d480001180c1903004501241c401031041040d00714410280ba00614400c0d00344010400280303040030304110311201e0503a08142c1242c2074000501c041000c2d034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 535842616 1250 535841366 535841441
    0xf06060a14150f0d14091225060e100509030a230c0a08070614190c1206081f06060e060a0504051503190c0503070c03090f0e010f09 58
    0x5030142c100f40410001e44460b600800745010403990b07500c04501c922003014034071504560850018010040e0801e2010094815805840801c486161848020300c0f604144101c145030b1011b8180b0050000c0d20480d40c0c1d50400710300c20942a41402d00113024080008190f542800103640c900011443d02181c2c0c00200c1c106a4440181131400c0181601c610010010320740c4680c841c050a035682c4089080c150203c4401000c503240394210b401c01d21258075160300e0318082e404410000041c5640b05000151003100c0300075090701c0014140080041c08101c08540c0040300312680510b003040e5020f210301c0408070b81c903030300420000ca9206680030410f818520080c01c1c1041846c03c0c29442d0945560008403203000d0075203a800190000030811030641400c01100c590008090b4007449000e4440c3c8000c1e00502001b0008070412000448500c02e16105803502c2c80201b0801ca4100000c0d070300c402210715040d10900030042001c890305000074450041e8819800b180c0000941169603813800c0c800601c440086 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 535843866 1250 535842616 535842649
    0x30807110f060126030f0406051804090c1401030905071a1612121514040b0a090504170a1e050705010e0f0c030d120902040603080a020f06060a14 64
    0x404685601e001c004104150103816014582c040c80015001a0103c0004d076003004d440c1e50f002401595039120514042c2c40a5507501c1c10302c1c40d2a0f0942d00d42e80c241c84443d0307042d0a580030f410105208148039004d8004000d540804000c40c086c020080015800e0f44d18000c40140396501600d010061081c40c51405c0003004a519049850a9020341340201038000a003019a10741500300c00e40261641c02c00c102000e80e00322500140203240c0d80080d0099280d469114000d00160740b00c010841e40ea90b164050514848001c181694403604c4440c2040188001c407421600e0603034540441e804103043d607090b07a621f8170303003030b55080601c0b04003080800c05400704c0c2c3ca81d0001d0000601010000560a000301031841c0e10002c01802110960a44286003500500405009401c42400d800b041540402c4141c959014120f0100f0001c050b4400b050050019510190100c0c10210b84880030301d50100d075002c0b0001240b011140d80b80c035140104280c1601c184030b00e06955444500d2084141000302801304101503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 535845116 1250 535843866 535843873
    0x4140304051f020d1b15020d09050a0c0605040f0902090f1201090c0509070f14071209030c0506120f04150c09050301060b03070f2001090b010311090403080711 70
    0x1960030200e00003800341075041c02c01880c0801c41c00c003070b42d604105500c445800c4c0d10f415002c3c40401c451441031110910360180c80308182400078802c0f024903404694a00700305a40402040113241440d6849400000007240d5210001e00d000820501c2036041d20291a0300d91039a8020702d2410b07040c40c00075130000e005241c00000c81a10306295a58a080b0f00e500d0203c49000802c1004e074610b0303ca5468a010b03089903215420710024800150380c00540c180f00c20302141030030b544a82036400040118002c460004001c208056a8001c1c0d4661090320350040741d1203485d025812603112010000030b070040a20700004c02010300c00288444d40c18200503074000c1d020707151850724110181c6441c0141c0b032008802401080c0004d01c1000b01e03007800d12419000b040104501415400d103510001e05040c0440f800d482000b032980440b001003103e10308100004070804008000d20182c519006000450911040e510b40784100072455407810030030080c134030a89c1d01d40d5a0484ca90b540d540d00b540c0c5903100c491590700511 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 535846366 1250 535845116 535845119
    0x3090909120f120601140d180f140609120a0c031229010806030606060307090e0a0501050a0501021c12020d0911040525050a030e01050a14160804140304 67
    0x1104000406845000b140810b50f2100c40c1d41000e0f41010003d0100c1d03042102160300d402894400c070050b2010301c90200e801040340040141c086103104240314001d021910700d0850001080313907840d03100c91540c6046042d203c0a99a4641c559100d005d0504881401141004000c4030300e449000c20040e0302c0c0c4a8244902d04548094001c02180c19900150840641e0b500c080002a40745c0c02d0162250076017440d00c08006d24103d0046625040042d0074140601004404210114040c0f60410058140c0c0c400e1000f492518003002006420700784100c5008424541001c11f055102154640540d2100030207148022a560f10451344401d180c082d0b5118035600344003002c075030b01807070041c0c404050050007084824010030b810802125005804c1c0c070300ca001100e84228010044410b000c0034100c01d420125100e0044460580c041e003498040d0401c1940313490100041e8450540c032400d41c1c0407080d810040701d07580310401036002141c80601703e0007241840c400100042c0c005208800d41240f1a0240ca050a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 535847616 1250 535846366 535846393
    0x1080f19060f0216140c1207050907140309250e0601080702010e030d0605090915011e030c0b0d0f1a0607020d02040c05031f050f060306180106050a120e03090909 71
    0x1c10b01041181e081c02c52100040317610508100e01c612120701110842c002c40c0740c40e40080d40e110040e105081c000d840810025410900034031390300e10ba440541c0341c2955a4584003d0701c640f200382180c80c07640f51b0300c0c1d50002c07000b01c00000ca03184ca0035510341e4800780c0c0141c0c80b444010364003a40001d05120443d9260000c44180c410240060050140e114a001c40c1442c1000100611000000d1a10a00354048207078400c200f07030a080300f03504540314040300c40b00d507602a648685010f61540c101600603507503c80001100d10417800140a00602d4080810500780684801010745003014240c0d005504004a44021031030120001c2540ca44010110141041d140e030214054860354950346001c07a9020040181801d40440c5610700712030000c0d61210301c03606000014942a500141c0580500390120024400b41c40700c0ca44103d5918140054140c2503035104d0005207182d01070400800010810400074008038154042d0082960619010b581002159030a21100182c020f20b052002c0c841c10b440000c91 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 535848866 1250 535847616 535847647
    0x40b040c030606080c0406080c010f0c06091e060506010c02220603050610060f09050303070f061e0e160503060109150e191a0a03060506060903060c0301080f19060f02 73
    0x1000e1040160030240100020403040f03c0c03503a80000441c0e0003924a5100c1c030b81e40101400c070f81002c00d0800c101e442485080010041c040c607030ec0109031848401c9416140105054400800b52003610240581e135204401100d8101e104070009400812502200000840e03581e0180c1030715000e5038000803807980d40c0c0c850620303211003500c010101000146003400026030000c03403214286460f00302415010310384004260380c0d102d000c6c00680403004061018081000c84e40040100d40d260070032040349403508800c80c10044c2400c160880b22403050701c040c09142c03c5804400c504545000700501041da181042c4a400b800e02501092500b1409440200b032503d40d0500c02c0c1e00038003240a0360181084581040c0c1c041743c0c100180410b035003000b600b1240080c0d4a6844030300039a68444408a49900d0b96004524540522602543d06003e84001c001482031840082c5040f241c2620840f03052054101100307444000c0ac4582d80c2000407200c030450081652500b0030580c840f817118005203009140e4251011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 535850116 1250 535848866 535848869
    0x201020f030f010305070515040504180203011e0510030203030d1104150225121101020f0102040e09060c070f0803281b3002070212031b0303040308040b040c030606 72
    0x19008182c00600902000b00f01d15005040203450080b24108a65000b460038004c52203220710803030b00da20f8080152400c0e103104004d640e9024009200c2d102104800f03103460050f40c61001000d51610002640480c509410002103e4010b4041d5203000301a810900260109905002030b00c9010403000802c1203160040c011314101c0d0354094140030f80f9111485040c802401b21103602e40c0e901010a019038a200102c641031903a10007070f8920883c00c402c2c0140d045c160820446403465201260000d010009070311124445c034058015200d03141d660100c15100790260718009130054601400540c00180d40328000c60b04480035403411104885158180908882440c0c461008280c03510b020130500d00c5200503146601c000742c200b0380d0b100e05907031040c003002c7c01000c048500d941d800d4036820300c1007a03502d0781242e1105401510014504280f52800e5070307a80c1c007220101c0ca2004404800004012011094a00982e0706030b450101c55225600d070181509030141061368070616480000000030f0b5036204880 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 535851366 1250 535850116 535850131
    0x1a06120a061d0708090a0c181508071a07030806010809030d09030509180f06061b030f120f0c37020c01030e030f071707080703170604020c0c0108070201020f03 70
    0x19214a40000001c0c030704c8030041d11118080d0b016140c2400001c0c408a08001511102c42a011460701c070003012202500e4040c0c049080841c0402c0080340d0100e01042003015981004200c08504011041c003005500c11701c10003500141c118008100250f2080b042c40c0d8120000d01c0850f400c146104081d501242c1c0024400c0b00401c80000d1204101d040ca066003c031a4085000d41c00c200385021525001c0f0302c24002c02041c450780e000650410b01060007814495000003860860303445845030500800c0590089030503546400300c40000a500c1c100c0100203510445860200c41d0030503555001c03485441c1403044545c2000c1d4502100400510750643c410740c1409403580c001d060007070416001400b00e03002c1e1190954540c004104002600d01900100c52649500820295250001c010b1101140c040e00b0402448010009444001e05600186242c078210521036088120f45038202013000700e103c1c406141b000340d00003c1020b22290b0040b44050303842280c0b40005840c080713040100d0080c550040f03990384d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 535852616 1250 535851366 535851419
    0x30c0309100c0c210c0209060418082109030d0c0c02060d381201091211010507110a12050f0c031201081603060e0309090108010c031a06120a06 63
    0x6805200740e8421102d8100140f4503070320f502213000c101c002d0015040c40c0c1c02a01075030240c0041009522561f0049150042c079001c00700800843c7c2c50220746942c0002d80c8180030600000900e820a00c1c8a40c459028500c4040294640b820a81d0b007000a03140320352902c001c0c801c031400d0020161f16604002c0c40c042c134181c0310002d000c2100a00c14648494010200e81c9201e20321356243c0302000c400140602d050600321036840c52000196845405045400382c0240406c81b0700300d25030007054101105c01c3d0000f0300c07400240301c46e64411904840701c1d01003120b090142c2d4030514054000c0b038400810540c403c00c0c2d40c51310f00d140c0780040950000a510020001c0000d0b80000303900102240c48440d0540504400000390414800c4209000c4080c46280006020704c0d684038684401118100211210803201030641c8110750707510300020b402801c061075030b540800c5c1031586161051194401760f1100c40c5000340040d0034240003040350303078410f980180782c40012036444001240102a00406008500101520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 535853866 1250 535852616 535852637
    0x5070315061d010e0303040f0806070905030105070522050405100f0506070206041e0503100b09070806032e020d0c020d0507050303060d0218070e010f02060903030c0309100c 76
    0x88140d500001c1e44075204102140404007100c040b141d12040c2c00900c00d207040011202904006411482203901800c003985480f040003031b0501d00420241d10446403a1642100c8958a5003490309035141210030800141080000d40708000e0300d01300d4501600c41e000940411552144040307800c8500c195998030910103101e4003004420048030511000e08419501641052420781c040f40190040c1c1c020502d080c0e03001c40500e100f22100702c54500040070018200e581012074042c030350f001002d5010f8454010381c0170200164a460107101c1090140001400030485800ca000840441c0700c040d042e12050b1181c004603041e20501180041c0c00c005c0742e06a0001050940c403800270b8540481c0001d0207003446000d000b0300d4003003200801500e0f408807054441004509043c4002203c0607601d010814009141000340031409030301c440c2c40d16103c0c1d0282c90f40b484141481105a070340d5601107802452581c020000070790300c00462006503420043c82c03012a080500c034a4440c50035140c0100807500016602e054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 535855116 1250 535853866 535853891
    0x30c032d10092c03070b010e0402040e03090d030f0e030a080c0712110f0612090a03140f0301031205091e0a050607030203070f0309050a1d0705040f030b0415050703 72
    0x1c4020051500e0001008071680f0010211420884440c0d15981d02000d007100c203502d22001e208503800f0b035500054a20f80da43c1c40e01c0301680b049105443c140d0085140610903880d100d80041243d9048038010005170f001e505d0365a080350021210500d0701c08000d10204841041c1c1c40030484000f00324403510718241c0314040c192840e8584900341c0d1110325500c500c4048203000c2226100d0000c401c010aa079030980c0042d103e80030800c81e114a4000800d405203a400304400c40c100441c44102d5584288c1c0c403c050400355501041250040d02000c900c000020001000020844861010100424104141011074007000505e401007003c1402130940d9540300c1a0115160860021014020480b4980c1c1824000e0b10001c1d50f130700541c00000c6c16541091001c80c00c0c10b02030142c00d8001c00c0700504c009580c80d120400ca84209141c01800c441d03140307405000c40c42c3c00d40210203582c281d50070810014080751854483d600c4481010f80181c800d0a6581d40e02880c081c203500406200e4810303a01c01040710200c010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 535856366 1250 535855116 535855141
    0xe191d0102120406241703130311150a1d1c0c06030509060c030a0c0915090e060405010e07140c1b1314011203030623190506030c032d 59
    0x1041d0702910204c803000c03150341c85c48400482c02c1c2c0d45100d4074604500c240b5107925140d8407078000c0454042140c1c00c4c0000400c00c4c40c80320703900700d910300341c03421030500742d048181c280d1a014034a690301c04551141c91550004103404841b40380c0c07240082c00a9455010702c414001b0102d081601602d04107500e0005000b83c5405d4003800750004401002003401d80b5050302000030900028080c495102d84800c0c421907880d1081c101c1038050110401000f82c0600400030280c805e041c2449030801ca03a5000d0300140c0c00380f80c41d11405040764014245032030141d5440e5811144040400307072854030f050091040e8008080d08120030383d09207914003a1242038040c02c608008081d060500640c0c00c0506011072081c2c011840e01000f81103501d8151540001341381c070b25054014002940040d5004000c0401c00d503049542c160310202c5404068a00710004514200801201452402440e40080e02000443c0103043c2d407074029030f8801301c8a4a6140411810100c268400c0a5805585ca0881c00704051090400e400c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 535857616 1250 535856366 535856381
    0x3060207120503070f05030a1508010f0e0a050a0809010207090f06052815110604081306091d060f030105040c1a0c0a0809180c0d060e191d0102120406 66
    0x10b040050444c60f04850081c0081c1c52054a0710400401001040355801d00d6080290120480402c00ca051900c0c0c044c854024074162070704041d410704090500d0b42c1c0f518080381145650b6000000342160307100b95260501154004014281103106070b40c000200345a485c131a01c442c03150070300c0011600d81d140108004928041c11120142c51150044a40703030300103115448030849016040380011420090416200d811245c5c2000019020300f40400040240020007032601110540f030002030b20352901c0d02100c90324450700980000030700c008250b590411b0068803542c0c0c416802030802c048048000040b070b003036030800e0f00e040f00e00f050000c1d018040e911180200c0e00c01400680032640c2800300c24040d8a80e10030403035070061706000c00005c101c0c4480d215555104101140180f0a07c241e0038003c20200321075104030500f0701450b2501c100425480030501c2100d000c3c0400f046544240080400f900c0014040f4043c04015800003116081c505c680a0001d04143c40440045410398a81824008207640d0315 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 535858866 1250 535857616 535857653
    0x315090109021c06050d0b0601021c031b05030c04032607060f0b4903080f13110103021638010506070b070201150e0402130e06240a03060207 62
    0x4e09800340040d0b02e6003401e450b14280c005200704600d03190240182c2c10415118200f21143c1c48006d0401c42e180c1c0c16801c08040b0702c140d075011042051b00389402b201d841c0020b40b002c140f074060030030003007003c0764000c041d0700124200e6411480321307420b10304003800b82075006000c01c07240039071914110110b441c800d226000901c8001c0d81d40d09080302d0032607038030780c018200340b42000e80c009501502102480a031000c0d007004848401c0100c40d40c18187d08001d40589001c64a1000004580300000d42d07900041c0c1e407a0300030030391144040900265940054002e501705003040315901c0c020039600d03000f0600803d07140049108201c00361101c0041005015001a10442c16030b0704802d64000400198032018120f450580e08240300814035154041c08032302500c40303045000d4045500e803001261100c40c03a070942e070044e40701325030482d44046100d4500041e03440a81080744540c000380c00040ea41541080c90184100b1a07006400c1e80c40d1020340000d20800440d0070940f8150f0b400b0400380c04100c0c8001c80384100840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 535860116 1250 535858866 535858871
    0x307031b030f0f0e120d1e050115050f041a07020415180603080306010509190308090f090405060c0f04030813030303200919050402070b061e150315090109021c 70
    0x1000d5480e9580c44807070a80d840481940010681c0d5190701552004000c100b6802c40c6151005501040f100908400e0281e050700440e0ac0d4803440342c0c1d6015508071030070300e070003012850f0420745485484044000c41547c140b1100342d00b04040300050b40c0d103210342d50310b98034041c08601c85c1506120014040301200b01c6101d04541ca00801480480c00c0d400549501c445e09203081c56950181402240e0050014074500e600500541e5021040050b900c018010490084c1c4003100248641000c024130b00c1c900392800f404540000d070104110349404001040040c9048200d80e15095803a81c3d003030710990055072008245401c40d9024410103506026000e5a5483ca40302c4880140ba070fa261211144165041075202c1d01c131842405250340c2021380600010000200110340b191400d042503102c41500302d5010b0b106900d0000728a2a0001048215403600c0d0064243d0011100650720f02820341c1c000362094181501c82c5c025000265160b514150280c25a40d02c09601e800315220101d0349040c105c03500c00001c50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 535861366 1250 535860116 535860131
    0x609031b170105041e0305180307080d09030b0c040311011211040f0312110d030209010c080406030b0a1703040905040203100c050403120503070507030c020d080301170f07030302120307031b030f0f 86
    0x2541f01c016100881d19616922001a40b80c0c0c0001e0314206c0c0c180c2c000c3d04a409003240e40303905550810b40d40b01c101c900500030b85007103569032000e4031000d10a0380401844940c6092050400e07510407988154100f0070260001402e641c54515440310380c1080e4452203512800000520400014180c0400d0310b10b02800c0001d1020a50900c00d91500c4c11380e105e1004040c0d0100d00b19116078460120390301c0c202c0d00648082d0b5215203642004010303141d00c11099018100340c410000b55171400c0c1c071440544201580c059418907051100e600f01412010b40103aa05204944802848005500c6808403090300d54882c543d80310320f0f52401d1030490660030f030000305000c4e09000b00004550080e0131900d40c80d9161503c61381280c1070f880064882c420224018040403404030000c103d030384961403001004417486046400003054903642a6551880780001001a0400348100c00d03000f0301180a180c2040d024103003c241c004855100c44480d03110300e01b941c0006601c2e500201c06aa5883c404c0700e00b80c1000050034003295 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 535862616 1250 535861366 535861373
    0x150c0106061421130b0412020115060801090903270302120303040201080736051509060406050304080d0203092a030d081b04030c03050601050603010609031b170105041e 74
    0xd00c50114212140300f590380000c014080d0314109050f801e90001c00305c60341d4201070400764503030070f0082605005503107840b60303841c4102c00d41107052088a00036545d0440a03800c1c031441e81c0c083e24a8541c11001e1202e10151070100b0400e404000348415040360164001030f143d801000020204510b601d65240c1041080c440903036885407a0513484002d6040001120710300a161400e01c0668410b03031310030201400e00880710701d4440740c039500413103500315005031800003021088201344c4148010b507903010108100c10030906000b00d01455115019810281c1046030f07454034a403d07a4400c80d84800c1503000ba1000500161841c020302ca144514400c041500f1000a0042542c03801c440c4504024070580d07034001900101e11070700100c14802c610310746640341c0c2e0340c81c5009020394246010480d1580180e000100d0182440c0080e2412a15560b032041c1d115440c5449160300c4415001000c1c1181c0c010f403102143d180000c000c42c906e90124400001020f00c4c02d8109056100c680c050701c0740540c2c4207071203181c010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 535863866 1250 535862616 535862647
    0xb040606090f0b160602030f100906060504050d0201050c070807030c141309060e150603070608070c030c08120c090f01050408100216120c05060106020a20150c01060614 74
    0x143c80b100340701c0d00c1c0e0700d80c03410f0704802c1080c120580c002e10890002040082e1503007118800c034028843c40641b03029141d2192140d0041c0d82d140c0c000c1d000004c50602040000346010380c169101c250040c10800c0c03800c1820382c0300c2ca00301402504040465442510b040041011002c401c8000f01703c030303424001c034440000c0006049280103010f41881c00380c07181200c070306010099100d946c00c45500000c641404c1d010b00b002481c480340444006201c0e0003140c0b400640c59001d900d02c0f40c411a020303a42c0c8900d148041d503040d282c41908982c2541c9654090000c0c440380b450200f1030a00a40d2041c0340261914000700400800000c81100c1e58100310f801d020800c05c0301000500707485030090120001d07850302c0300314919000029200f031014001544895002100d01c0d00012100000342c0070340305543c0681e8990720140d81c0d40003410700007840009080d05018011400c3c004450f1040001440800c205c00c0850f5030702d240f5048400556003596580d541009030a40001420b480341000141a43c10017601c14410f800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 535865116 1250 535863866 535863869
    0x2802090a021c020a0c0615080703020d0c181a0411040513140f060306150307030314120c0a020c010309020f0402030405100c020304050901170a030e060903030d0b040606090f 76
    0x2440c0790003007580c40d490305405039440034611610904548810403c040100102c00080050300c0c01ca252a200342401100c8031041020340e00100010321605240d5828051024080c18003601d5010702c4000c0420450b914841c0c43e0144a000300f0045201e05c003100780c2c000744140c4050400c4c8654901b1030712035030080340070b4151030455004a60101020300200700e540c02500741d0405042c1c2582920041006181e034401e8606e00920046c2c00700d615070f03680c6401e950485d82c4448283c960603840607004000180c4110300c00e003980c58805040e942000b003889114040460f0070b403194508050041100084541e040110458800007403806203c0b1412075000300e41c02d07407141c944590040342c00000103002c0c001c0810030121601c4022008125034000c01000075144d4105000303d500c52005603000140803c21075038030581e610403105c0034010030b007440d036815101e0810741540540c001c00c041c80b6180341e55078280040d1281c0c526400c004103945c40c912003000b044816a030000c406201030b04500f40001c40b81da003e02c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 535866366 1250 535865116 535865131
    0x210b0106030b1c05060703060e090c100905030f0a06110f0f18100e03010b090606030708061f09030c050301060b1b030f03010b190807021018080705280209 68
    0x9880b1103900003060303c0c0c2a002c20712156000b00b041c848410801d000a55500c00c1c5265070b010400103450320130141b004a000e607134aa41950201900d06401d02d008070401c0d026100c0303401d094440745c0ea00c00100b03080801c50032000420380c0007155000c052004502804880042180341380d0320f090700c0311039501c0e017038002c0c0020214001c40100d00c007030038898820940c41120b07000030040c0c1850358514400a00a1000660b0030b800f079420b025803e100344c00c144103080e0082400424403800e50f519440101d80004c0020aa6a4008068034a0240b0007071680707910507844605643e540440781c25820804002580c5034046c40c001ea240180c100111852117003a100c402410418903500501150502c40c43d500550060345030b072200c00000090000b404034010000700040c2c21050b500280078a0013030b2454001140e1003809070700058046206103a0030b61208040c3c40000600450318507903900c401c0081d801950080351300364807000304401c030070440541b0248001400402c40315428615408207450034805001d50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 535867616 1250 535866366 535866371
    0x109020306360f010e030a03180f240f090b0117030f13090f0c11071a07050f06041101110304030f060b01020a0213050114060c060c31210b010603 64
    0x18165002c28810b005440080e0002480304104150182d5205d0740568030050101746025043c0468281c4ea2000a250a80005072801c0050007915040030442e445180c2c100e04c031501d8100050080788911a41074954018003000500710141e2400120080c8181c0190b2a00c004880c04070981c204000119003c590701410503079120010345107080c5400030760746c00c64898039060a002c600350016540c815415850b2603a51040ba00750020551a00c0301030034010100aa40d00751031003a075445441c4000e02c640340c420811100c17211409010700d0f0403c80c0a64040720550031680c61844990b9208115084540c585409580341c02d14560300c101d074400310007000400d00c030f44403000500d141e070091012904058002d481d210b1a08603a1115000900d42401040311303034014a2511005400e2202c290b0701e402c001e0030010421a1120822407a440d00920a00d00c4a88001120040d1001d90340d45941c032048a41c1020401150070001c0300c03130707c0310749116620311501c025070041c50100300c070700d503240f8110f81c12402e00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 535868866 1250 535867616 535867711
    0x120e06090a080a20030304150b010807030b0f061803060606191808150103030810030807021203090a172a04050c0f070308010f0f2306040f080109020306 67
    0x1d645050403036400f00d018a80c400388141d03c01304084010b6100301d1169210442e0400c0303114801003101c115050043c0014001c0340000d181034080c1d0b01100500c1001048030a20300700620006906034003005003500c610801c1001c84899040c101b0025801000450b90346040220b54050820903a1400116604000c400c076100101a14070600c03002c0948010401c0d030b00c4148007079081c0c0c0520502840110000360981c0c0028007030a580d410000203403980801a03624228185e000c00600304201002000745010070491045107640f480401d500800705983c40e188a40d00c10691182014001c001102c0d0b80401b400a1509010312000e00b40a2407a0031078000410791500172983c0801d018030458960b103140e001803514241600104440c2c100c0d000301c003480324100d4545484001c0c888442c4070340d600035a030113281d214035109100010100301c880507206609080d80d0f2923140440b0186980701d503c6507551414400150b050920405a00c40c00c5084000c100e1050001d29055050301c01921038868401c0c103e2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 535870116 1250 535868866 535868887
    0x10501060c08130e010605070b010e16030906060e190e1b060c0c1002070512030f0a140702030316150506030c0f010309020907170f22030e0d03120e06090a08 69
    0x40401074115504880119070312264050a0348d07109841c2664080d014a00003d0b969109580f8144141c00429800d960141a0384090740900b40801d130844059841d2034000c246098070f001e04c14030800480c0c01280522136500b05050488040c46400c80042e0010040e201c0c5c0900801814103081c20190b40712a0b030f034007a404a083c02c3c203a02c034000c240d1090b146c0450851640d0700017070101c140e4200b1070306c00e0340c0b4010b00a9680d03544d100300c0d540c03d01c101c042070005551180c0104141e510b407030745007241ca80c03a14106070b000030300f141d0000d02207050b402c7c1810107400078041f040b00c1950003180400e90820550412200103640c1d003110509841c8510580000d0003020b900c41e0700504c05080c2d015001404604100c1d002800c0070b111480c00c80c01e5890074000080b61441c4803001d050144001c1c1880492244408021300005e0f4840311080c0e003480046848030549856a245080d9202c3c040d41e9142440071542d403240e02500d0b60740c0741c105220303803014003800469500402e079040d040760702c015040e540310394000e07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 535871366 1250 535870116 535870147
    0x20604150219050d06090207050a02010c1a011e12050c1905040513060b01170a05180a11030d030b0105090402070606031b150507030c241503020f03010501060c08 71
    0xc905860041094070358210b41d04000034294105002109201c400d882c0c5408808a003e221400350143e440624480d0143d4042d8000c224203034002c1c0c80300c01c0552108508000035a40c00e038041d140b803108000704100708a03440f000e4071024061603001001a503c0940310180c1e42c5840b846490712030000050a8807400812811010081c02d015000f84914034240d41c00c000c0520042a06030341060a10042e90015032183c2640071071540d145110350b0709501c50300140802444000d1010010252203134000b00020b00070041140c07903d101e80710406011400d0400d05003011f0340385c1c0e1140245410049186403980c0c019003594403041c000c4d500140c80d00e1190500d0005404280d1000e001d12200c2400c044816540e500280d05644044841c0302c2c0b80c607074109088070380c1e22a050380540022a20001d103400100c6440112034100c81c001c04540080700c0020f10001261200001030020100d03020b010400c60826000c40520380d0002c90003040b080d0f1501c2d0010b4000c0121000040c44144006801c818624000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 535872616 1250 535871366 535871377
    0x40c0905030d03020d060f03031202030a23090f0303011214030f0c0f010b1c0602091306121a010b0a0c05071a07140a02101412040506160f0206041502 66
    0x1c0403a18000c094090280083d0300c5242a00541410040e02040910046110004495040e42c0d07060081c003094032000004c0d0400707841c10850300e8485030018032210780079540d4096061040c218403000d04111003114900051100b80c82030355001403004110b01c4619107113185800e074218200c012160b0305034000c9811480380c85025541c029021480501c0440c001034694080240701000704252900c0038100200c4071801c0403036004035038032042c140c0001961600a02450348001e0240703c0801c514a19110039515550018804000403240880900134800c3e82e18014507803141200215505151013203400b071140320165010b00507041c80c9081040b1041041c44024007041c140c914149420032901415548030f44416108115040003c02e20204081031515203c2e90003000c00300c00000c0300d403040d941081e41d8002c1104a01301441005407519051102521803032148004c0c0c0168600048060a02c00158881d44e080010403038498007201d40014000f50040e4220005113410405112128040c0c1300c1c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 535873866 1250 535872616 535872619
    0xb04081522020328030f080402100c0203100509010c2601030201080603030409090305031b0c0a020906040905010509070302120f12030c07150c0e010509010c060b0a0806010b131502030702040c0905 86
    0x15800d4802450781807028804c80c14402c2d514000340d102c0c0c02100710348581c000c0d00c0180d8001c42e81d0031300d1007065029852001900b48080e040d141480e80f400e10380c004840c0c0407204030307034140d440d50000d40909a2003851200044000c9c4c54207008500a90000f044500c01408000e05101091010603a40c1d5010006d880041211040030b10821181f403800800036002a1040300f904180c000c980e4090080100a4888440c8000d00604881c4102c0d000c210080e6000b0b001281c01990b92107440001c50001e000d43e910503c4650002c1c40e48500c0d52042c4641041000d075046500d400200341d6200b800008205401c2d20204440d00c3d0341c49458050340030302244110310703000b0700701a0316804078812500749d60031400c050306060711140c2031004c80780c00555442c41100c10a9000a0007039010f4030005881b6032144441150107012030801c42d441d050711915140003a00000c8103248041603142c040c88260000c000031300380c1d4a04000301e21161b003202960740d0181e940d000744256240c0b8001200c2e030b03204031540e8006050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 535875116 1250 535873866 535873903
    0x913090510020a0807141207030b03010603050303041101030612060902010318030806031006062703080301030f0b06030a0804090c0c0605010f031704060801120302070f0b040815220203 81
    0x7520240407000f9070111880c0400700304010002140140211a003403d8140c81141c00c910b0209400c08585040c81c0040240301415540c01c00e007041601c3c00d10070301c409148100b00944c0d076401d06080044100c040b840c0e94074100341c10300c03100344086114101c29081c0300d40d1010f004601011075200603405040d9602010711340200200c50041899440f05506000d6034051b010343e0b0b40116044030300810f9458030b004503400b0403105011000224444e41c0752011004104e54000c4401e0303201d0783d404501d80c0c401c0c0d0050724136440741500740040c030140400442d08a50120010060850a81c1c0ca04485010701d21600701080c1e80c40e03500303420850203080b01a0400d94852020030096859640703001034000e9901060b14142d140718102c10101c4000021502554034689402d03415a00c0c02041240483c0c1b0003a00700d00314080c503900056440c0d101d010540107004081c9050361202d0a046820380b41c2010010a805550060410703c4001c40c1041c0c0b88019005503803c84030007040c0750b030012070701d011000c041e00401c914 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 535876366 1250 535875116 535875133
    0x1110a020d0c031713030305240f120f03030105011803050a230a03081f051e010546350f0a0b030604030909390f03090809130905 57
    0x500e003403485c00e40e203200e51010442501d416020540b10320305000031014128a01c03403030480d03a05e0500040d01c80c0711402040d451854102c2c0d03143d00c0c14040e501440c2c1c06a540080014041036070051302e81384005a18410090142d46940c6800390f44140c544070144c00ca01c40d461020380340c80960310407120712498400803141035951f01e10303005150740e40403561102d030004400e1410b082c11071f0110070740e8103c42004012003421507041c400410021098a10b25040c000c0822030b46040c1c0c080d54164200c11800410340c800549540d4400ea0020b07c0c085540d00c540c7c40f81340010f2129150880c2200001e9984d060103a8121003440701039140d0a9000343d648003000200c40100010340c070984099074417275040000e0038843d2414810901d95100c400380c07001000b2491030b40c410702034203489501687d200d02d4100300010b203284a154031412600c030b05440381b1b08510340120710445c02d00d801c031041d80e80c40c3d106481c042080740040d80340c071456070049000851094240d50f0b5250400c18242d00703c10011a00503082d40e0000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 535877616 1250 535876366 535876381
    0x815070315260709020c0c0f01021603050a1101031e0b030c060d1a0301090209070305070504090c081f18200f040f0f350f070801110a020d0c0317 64
    0xb0914010210450320507a8008618441540269442c0c0c1d0110401010340c1e40342241003040d59089072043e14118400c00c1803d107030f040603031102100114050400741014010500b00700d420640d03a141007030b0606041103d00385134010840041101182d5220000420369000c07030010f0b0804c401303044110362004d0f011030b0120705410280d00c411090030f038000d41100e03c4d0100005250985401802c0070354071004400009070094000d401550344540e0a00d0014034098440720303850100c802446c1c010001810781020030a640d000700d07616001d8003c00c00110140d16107421104608180c260724800c46d815180c1a8900e081004880780d0b450038199000995111310000c004400317290024459643c07000004500042d10103504803c910a9803070f102c46000800c1020400b81d074081854150000c00b03402d42460000303105000f44070b003681088496014206240c0303017a40003420344090420030707040e05604000c4000300c0c68002032040c0408100d41090000c000c414101031311101203803100b0010310020340c000c12108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 535878866 1250 535877616 535877669
    0x414130c0f0b091e060a08070504030c0905040311010e0d050f0d06060e100e030304060e0d060903023016230c100302130302060f1b07050103060815070315 68
    0x4203100351280700e51044c90b0b480442c2540c90100e0860b0300301c0d0040252035540b51046600766484086810100d15195030f82e510714a051810380e108008050340c5100b840200350f400302c00c20140d80c8402d4000d021060180c851b80e0348030390700040b0000c02d1103400100f030701d26110b0071000d441d54190340311000c2080603a41c3c8406840c42201422541c1f00b112202030700c281079401351400016807117018000750b0400d401d044065400c101601c0c0303d980d02c90901c080440000350b0790301402c10b120380700ea03000c0c2a04180d002e0110600500551044910801c1c0e1208200c551031440c3c142e42c6a4102d15961310b103400c0e52400e281985201ca42e003c40f003141800000002144e800041c40c004081042da004105154003d0f0200c00302e00481000010241c00ba207010005032501401030000d1150b00180240303004042151a5007020504030701c150310b500034041c00c01081d0703014840c90000389640c0025000510702c0c003800f50010309000701a042810340c1c03021200003e0b100030f50300c1c84c0a07095000d00d480410300240c0351140c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 535880116 1250 535878866 535878877
    0xe09010e0f0d09080624060904091212021c021b150619120f02010e040906090c09020a05030403080720150106110a02010c020609040513030e0414130c0f0b 68
    0x2c108010000280000000b40b0f17a4410210150048400f9524000340e2000b540c4012565a1002c000d00038403002d641c83e4403030803d16520a00c90b0104107583c040000c1c1060070345d0070b107100c01c0130f1041c040000f031950306000c00280800c201c000180d4400304e0031264040e1001d4045401000e00c036030300080d050030214a4205006d00812a40740040900204889164003083d010300c10009658234004000696010f525204240c414100383c602c0b050384802003400c844e01c040007603a41c40e844030365201c18800300030940c0300500072070038003580f810446901c00b411a1101401c014100300303401000901080c441c8940181405d41c000390105500040d00f002c0f562580060f90701d440152424000007851030080e264034129629450213099003038681d40041d5034640782c2503000da8204000700039107821666103110745849050203440581034850a81001008581e00800e19409545044090380f0340100c0e040803650b00603603141806912440d5840d24100599559201c0588525a00c00100b80344103204003920 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 535881366 1250 535880116 535880143
    0x601030c030510020a270806190b030601060e060d0902030a080a0e01020a0201120f0f020a050403031202091804030c0b090102031605090a090509070807031109150a0e09010e0f 77
    0x403220058100040c00300d1184245d40c0d03022600701c050746c8800c403403d814001c64030965600329040a941d100181400d00314216111807541f01d005007400100307401842403c650340003d40040010f90305241011300000c104014031889210042410344502c0300c0343c0c00002c5001ea0140594640e141645010f40594005007100000300701c2d940a8030b00a540b000031626000ca405030743d442e0500c405c809007000206850a8040401900c9640092341500d45000411401d4a507a80d502d540d180717542401031a46c0c00400070f14400500400118850340e80c2d441401192454000c4020308a4880d8502950520403505c80101003007149804c01331810019400b0f544100541100d41d4a5101001c0084900e0302c105155654001d041210034002901c0d5036001c2540800740390200c400140d10b41c50040d251079807a50044070381c85a540f4a905c4107040095129030890050040b0b010442244000603a5005240c01600a00184100003441c03611094001c1140070031000291000d44400e6800d054680301000c0d5640e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 535882616 1250 535881366 535881373
    0x60501170403020703030e0f0d081216080402040f091a010f060201060503060f040c0e0f091002041d0901022208190209180a02060a050c010b040213030b0a0e0601030c0305 75
    0x140c45040d0050019201d9545507025109140c00d55505603000700e4040c4e910364001784021050040740d1202080307419003d01400d20561912803810302603000c84070040c0780c0416181c46124041c040340e04480d42d150001d41c11103002c80c00e0a030f080e0b21007008000608010b080c549544041100c4401c802c01084d05076003c2030b2412a207240c079284107070309940700c61088070b42581c0414002001c00000c1d010709500305200d046040398107507640311240301c00802503c0b0840801e01140078000100b00803c600340d80311a000c4025420b061a165000c0c5032a0b10407050a40c030b0549510002e00c0354402235048032017082c20045220390a6115010710890400a03010310741d0300388541c0303518a442108003103d15482a600034400821540d8501d200486c40c0001c00b0041003511580616400503a1040040c3c40d90300c0c900d40d038554a6405031301c100360230740d00d075080b80b64011441007001b9516181c48400c82d00c15641c10024007030031b988408400030010000204c078403489014440010042040c27040c1d40108403070280085 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 535883866 1250 535882616 535882637
    0x10e190f09030201140903070b130f120305010e1003061a04180525030215040e07080f160221070512040303081e060f040e0703050c190f0b160c0603060501 68
    0x5000c402c030f064901d21b00c544e00a114900c00644201456a804110450750036500c507095a101009180c7c3c40a0490380001120407254048d585486018014030840c03030b51034082d00308214070352450b81c0b89000c0900b40688032031070305180c0d01810001c411a130101510422145010800f2900101c480e0306e42140d2a01550b490416507060280e00148603144c1c4201050703000e03155500f0081029042c0141c4801ca9805010000b1601c4002010903c41c07109501c95103c0c81ca010441e803d0a914001c0c5500060182c1c6202060b110b640098515050901021031076000c440d4140700a409008980c0014624890020105607100103040544200c9101e82c40d00500b42d1074800030629202d102e0512400240c0b503001c000350681c902031040161060001d080000ca8100c081000c0d400c001c00c80c1c1081c1c4555221603c01516410403d0005401914515810305190f05050080d080c00b100c0d44a481103160001c510210002880c3c000c00010f19844400b0703401030f41e5135090203000f42c0080e100341d5010641c1d0400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 535885116 1250 535883866 535883891
    0x3030e031b0a05060a1b031e021b0402030a060503060103080a020114091c030906090b0f0a1107110102121216052b0b040c0207150c020306010e190f09030201 69
    0x41c4581e0101c00074118462142480b00740300350394001a001e0000c000240300045082110318608440090207650354003410310000d003000e030980c003411a441e070031035101c1e0100e41d95007084030310850000601100c02595039154101540081c02441d080700d07626004400000040041c3e80e0002e040a800940090140d004070390078803905003034115001c0500c2d800002962121007400001117141d1180d80c05c000410050310380302c080c100c943d6658100c0f5029115030a1245001702c000c80300b0f5010704001d005000407090101c91400074002c0190041221a14407400c00c404e0303000388100f002101304070380c4041d1610500d10031a800450309030b07002048001030042d80c01580f4421811980503083c56800485401c1141079076021451003243c81c0080c1d55500d1a80703485d640e481b8029551607005a0f401018603e051406a4031115448819801402003074032074100141c40211b480c03411101d800d408103409a40301c220741c185487c1542c00804000746050800f0001604661080c46850301035402002560200107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 535886366 1250 535885116 535885153
    0x10501030503070f260d05060f06040e04081e12010b09090c09030f0706030e15010e1b22470408010501060918181e0b0103030e03 57
    0x1e000c40d00204603140100d8900002420050321456103030f2508541e240c0c5254030012001c0086403a2a8005203001c441d208500841d60046412500e09158200310303000504a8420f52047c5640286800c00103000e0140746000d83d403401c001072540117040d80b85042c059080b41c1c0b06012291900388044000700740c207402034007551910000a0500c5c8101d8a840100c200243c000324503059042c0306045005011034024040d14000744403544020407130b0b05041d4601c0303003000d46103604441d80040082c0108030041d001c00506400803002c4490b4403106c2402d46100e00380348201e0082c1c84540401c1e08542d40300514807015403048800e0005000019080e04242c185410b08280d031713440100b012840c003031683e130800080d22507003203540c8560700e4503150744d030001d0b1800e46400345d000d807010445003001080095280c640c112440707542c00004110504c801d80e030b0b00510285240307000c5d0200500924600d03004001c4ca142d90724150b0000d0742c2d0140341d80e607460010300c0700740600783d840e02a018492030805c0080010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 535887616 1250 535886366 535886369
    0x112050f0a03031524031a0d0507080d050c070b070f0803100e0903070b0708060a081e12040b0a0e04022505010e190b04030513080d090b070f03030902040b04060b0c010c02010501 78
    0x100e03916039174a0080308100d0242241c0d5091452031628076000c0c124694400d1804443c0ba841017014102e40751801014505140b0f51247e0070042c0502004518000c039404a030403070580312114411901e4140a00300429440352074000201105800400d20044104401d1824110b54100304100c40507690301c508541c407806110801820400400d010031110360092000540c084c0c000b914159100e40d5410890745030810313200c41e0020860058042c014038440900c401400b0324109070041c1d00d031510300300c140e100a1140e02245001c10041c01490a1941e070303950101c5c1c0305110190b084400380c040c203c400c00c400041e0407a00b00d070590310f03240000c07108440100b0101c0310005010010200c0210a0320340c040f50400c018812000c01c541080b14042c41000075607548041c0c09200001c203071124900c4030103000c11446401c1000950010f00820300040c4605801d0741e4290352501c2c1c081038205544c40824060301b00c10080c1c540c424100b00022503400302150141c00040d095800078410950358407400d81c2202c0c0e00703 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 535888866 1250 535887616 535887659
    0xf03091c030623221e05041101111b011407060f060911040e0901020f131502010204031509060608071e0e0603070b131d010315140112050f0a030315 65
    0x72079045405020340da204c01900f4140494011038000303014040d903c110b6050b10300460000c0d56420a00007401030001030803554400078240000c83ca4803110050380d86021218003c201030700070640d0803140d42d00c03401c0701402021500012680303e034107034544030015205031520180c806140a4000030b00600318003468000d45844214546440d091111000d026600200040f0066400300030041840d0f41c6000200943c1500940783d0494504207080c446c0440ea84000d030f1811680184402c0c8003182c2c0720110300b041101c007000300103890140f610307100b8007924442c0d000d002d8501400e03800041c00782c0c40401c141c501c28004801ca40119840d0f0744801d1840a0036545150141e02c00a02808040e08550047c416204045100c0625540d1480030941441c100d41e600a54420f0740d174010010884a4840703100011060a428841c2c4405a00240d040303880520808018180541050b000c7c400c041c450845882044016105641c05030b09018000d85485c81d10400514821940001d2150401c1442c5801588 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 535890116 1250 535888866 535888879
    0x1c03050a0c05041203020102040f1d010b0c03040509070c06050a0e010c14030a020f070c0602030d05180d140d0212010f0f061d061c05150103060b0f03091c030623 71
    0x1050742e4045244c504540440944d90300f0400031980c201101003a40040100c6940704c080c5004018103062910302c1a40041211101030254420a10700031042c0d5003035403015990094a0781d00c085080b0f509151401c03024240340c0c9088148540300d0743c141c004140901c1c400d0024014a0f60151044410180380150040c1101e400e001054202d00345400801d0f4840a6000305030030b1603c240c903111b203000c07200da003c50056031000032010b00c6941140038255208d000305007105e420f208d20028207511032440c2d80c0850300300600074810f62820210b003016a14260a80d070b100b107407910108446050345140a0048040c1c80340c103444001409494200907406685482d610742d024022400810305400c1c401840d915407110302800351a00030b80c025807010308808070303445000c2800d0034011031455100e224845081c1c105070511005100c6d00f1008001c82d20031240040003141e0342e903550f0115a06207081454002c00c040c50800c210710b5001d034140c000d80143c0e6040319025a800c0134000640c43c69982003100240c2111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 535891366 1250 535890116 535890119
    0xa02060f01120b270f01021207030b0d11061b0109260f0f120f070e032a0303070c170607031a01050c1f0e070e04020913050109051c03050a0c0504 64
    0x405010000b04c1c8021440500e03c82004249600e0400040b00c2581400340e5011031601c285a0519001d070781c218184d410302f004051000780104680c1110308101070305a81035000b60700e007152140c80450f009010a845032071032903141c906450b406008801070642d810305044020a902c50010342004103103654114140d0700d03118107090016102c3d00590f0101d6102c03c03051140d41080042418914415031810f034482115107403100b405092031300c0c8514030314000d034440304451461000d5051966000044010408403079501c04c00080c0c6035102e000c1000b0020094850300082c55800b9040000581c414075064810955800c2c40071001c0707425204004230307442203012010360b10707500a4005012031316600e0300395034008083d0710450400d82d0081450b118402d560700302545219109101240103002c800045c00344905091f000070f0800c1101611031240e0025844040003000000d512850030141e1120907183e0800c442545042c0c41c8003249041008242003c00040051446101d5a114002981c49903410726 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 535892616 1250 535891366 535891381
    0xc04050c07030c031403101e030305041e08030a0f17041109040609170c010c080405060609090f070b03070305060f03060a0e0708010207080915031308070204110a02060f01120b 77
    0x18010f25000e5045c801011040e03840c405a41000790700c1049401c100000c0c803032418002c14190a4040540d150545071082c00340002544401218200c4502407442a4450030b45003c018000c400b030340c01078200d84000201801d00300e40002003041e0074903641c0c4030030021000d208200030700810111002010351046100200030b52400418982c0c00500820000031144042c0e0b54190000d001e980d031a40c180000402d00742d001a1090054451a1419140244450a0a9403410740c3e901d009030040380b0403803880d000140700d80c408100b4031101c0400b94041302d85a90355041d00e16221ba1003035414200007402c04001889030f003400250800305c0103001e80141029940e40d503031030000b021400c0c03c0d625540668030001800da14240040c18540f4020308156a44080314401c201c041d503059003248006000500401c214442c840742451001604400290b0750741c441440010000c013822000440030344808a480c4200c0340d80003911034880e0f20515100711a590301e4407100482910405001040440c1440c00a21071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 535893866 1250 535892616 535892627
    0xd0507120318050303130b1006170703230f01050402040b070201080402010203160b1609050120010b0a0608060f0f060702040f0e07030f0c0608040c030b15060301080f0c04050c0703 79
    0x1510214070100000c0c2e4640d01c1c18210b80c41600d1039100b28a4180c884018002c078403507110341090505039010043c81c036113040500500e095100e4070200c00301500014140e81d000340c2010003480045c0100f02400041008100003100e400da448010300009140049024140b510803a4160b5102541c51802e01806600448030f20200910407030450006001c071210f001d81066030381c0340c0c5620440010480780390030107039500c50001c0701414004114034900c1c10092a40c1000d110680100301c52214100740c0300095440380903001d4401d955800070720403000050b0340d90f4060425070007240c04803001c1c5113144401c020070000700300114000b40c5c015010031900f001407902d41c0c810040a01e00200100c0c0580b0302400050400c1003650090701e0042c3e1280c9250104203101c480c0502801480c102207001c0d00b0a03881d1811031060500009081d0010800130455640d0161a22079403a00f0080c02e450381c80d0b8481d01c2194542c0c41e90110303a103180c412058950107928183c00b03058414500381d070300203051120544040301d6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 535895116 1250 535893866 535893881
    0x9030f020a03051e0f070e1303051e0c0f010506060a200708011e050f0112060b030a0c090605090402130504020607120c020a0605090102100f060b0c0106080d05071203 73
    0x244a16020380000000782c0038000070050810310150308004d82c1c01e1034030450500000640141c20307030f00000b0084c07041800400d81103403c0181d100d092540800c0b58031301079449210342141c400481c260303101c000c0ba101c81550014078420000c0c50960b0001d00360b24801609981040e0f0b05154006410700c600210380b0b03c0b424890602482c1d44a0780c0c044000b00071300c00390500e0b10701d4200700c0b8182d465101d085200700707401c80001c00103441c8010030003031450a190030201414040c0107050355003900340200c4041c801d15030403042c44200000c040d00c0d0b99205514059510f01d25610903800c00d581410400603051810800462045070060501c207941759040e05040002c1000030001c90b44500c003401404049080c0700e582002c0702e011a2903407030308040e550041012a850b583d10910800c1403c0040c015503903404941045030000459000c83c01c05c40ca506044003404a5400041e0f104102044048a02c54150854000c954160b0f09940300e00b64400303002c807003601c5090070140a00c40001581034046d0301c20703801a00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 535896366 1250 535895116 535895119
    0x42406030602040e060a2c060103021b07080d0504050f0d0309080304030f0203010501050d02010c121b0506041401020f04230402040b091305070e040b0f03120a1101060609030f02 78
    0x2611626036440108980041d0440c41d44003050a040150303074100080c0e880040c0510881c0e140d0010121006900c0d144201d02202d405406040c0c04100c0c10390194055070b59000c030018891412640d5509440ea803524070b445082c416100b5007000700300c060b002c1c00032501501c80245ca40c65081007018284030320710030600c000300c0c100f10601400050380201480600301031031040e103045040021074010542510301c107800032480741c0c0030903920000603a0018004100300b50711910040c0810b001603000d03190001140c4103000c055005c19030308000c000001c165540704038440e55800f800207550140f12400c03406007101203400560108000e0003001844082051100020268107000700d00c1032001ca010390700981c0c4103000444011038180c3c000c0c50642011f00014403c284108810304d04014020f180c80c0c0c4800c800e602481d950602d00e00d01b91034181c00180d88000180c100c6036841c2c142100c00001e030340a200740e00d000901d502584102880180105000c840081d6190052a4119111071905024000013203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 535897616 1250 535896366 535896371
    0x10c020312030f16020303010e0402010825050706060e0705070b0c131805070305220f0218010e150a0b09040209120705240301030b09120c07050a06080424 68
    0x540c1c16045003000314400c60010000b0318540c02c118142914031305000e020030055400600050000e010345a07c5c0c2a401902440c1c607542a0721261390805112492f211b0740d8900241041508402507041301c0100383c00f0740b01d40f02c10004903a8840002c0507040084d1b13000d200151040207400d02180f030382d0b407015800c0980e50304002e00c1c2001c03417440f0b8641011141c0c4260901691190040a1102203109265100800341410701645c03410801c0020225030003a01001c04000315040d0b4802c1c4442c203080780a466a010781042104041c401d01640d12180c02d00c00c0707801000311a00090301e100c45060500038039540260440c1032450903d80b46078101d0300b0030700895410036420b10084109541c0e01c03404020002c910360142001900b00418440c10a0004044c07111071a5030703082d6198a90801c0080ba4110f0750410f0b200583c50300c80c42e4285007041301040900821010109503881d0394031010440108480c0b00300c501114003960b440703043d1041c9000301c8000c0c0c03100c00c3c0d04000350f0075a0b40007982c1940d0300e0740c501d000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 535898866 1250 535897616 535897633
    0xc0d26041b1211210604050607091d160302040306021216020a0b07031a19061404080705040c02011d0106050108160503070305090705060406080f060d021c02130f0504050c010f0e010c0203 82
    0x116468408220746c1901c03554460b200784034903240c001090b0805444402a10b40c0d01403410401c08900040103400b002e90381003442a043c010b076200394180c1d0003460340500107659884040e0b003100404141a95929400c0401c4030050201a00000d945441c0b682e103d8840040c95a4140c410f070020030940240c2c0f0382000c103607600981030341d81d04480807914404d00450114410b0810300e0003040d0800d65040071101c0d4008101c18043c840c000209802201c2d0b0403100480c840c0e1504034100c0c090881d800300d1102a150035402020300c0179041d0003005c2603030307020780c4ca0050960f10f03a028281040040440200456010004120024440e82025a0010b039840449142c6580d800c00b16880350311960020001540c43c40030b02c4062081c3c6c203005600460100c0d10b100000c1a20307000104103104110510390a10041c4101c1011900d0b800c1d10f000c640c03102000b00b040403c07010300c1144050502114111001d0003801c40300a01c640c0207421110740010195030b020b038605100001950594100c0e00c00340d0381845a03901 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 535900116 1250 535898866 535898929
    0x20904021b012c0a02060c0102040f2306030621071a0909010b12010b0c10090303050412030e03030114190602011e020c0d26041b1211 59
    0x1100c02898020000000388829510f40300d9041c0407a030710034509803c5980d580d007001c5000020740700c4100c94046030701565505400443c2c40c020300c50341d402101c2442040b1000610320041c040c56600401141640d41101c0041c2d8003004403d100c212051640204804004540140c00307070f04003a410505582214038240d11106030911075024990700b0144420001811446810315501d010f00501043d0394a5003451801c01001c0ba205505005a019021300841e00109a002c104184030204038110020014040c1d6410000d0150008a4043c1d480c01c0d804141550803c1c481c0c81001501520380015508607402c0016200c20520002c5e2810360001c0d12086520309090218514001043d4603000081d0749000d000000069a81c1040303102c20307480c07041c040d42c030001d6800710324203071801038034030b80300b0300143d06d0391145c4200d142c0951440716060641c45c1003100300032880702180844080e00c101e170320200b60703902003e50000c0807000d4014680012004000d2860802c2d141000310400c1224904800507032004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 535901366 1250 535900116 535900147
    0x2c0c16050f1002030108010b0901050f0609011b03020d0305090c01020a0204110715270809091b19020705120c06130e0702150c0a0206150a0b130807060e1302090402 72
    0x380b8864401d41c00001000541c0c2c00b4402c010a912003900c2080071366140c60001208004842c01c82400382c04002040c0070030768131584613510f9038407200078695116213a50a0087daa80c0c20002c000d00417a19020114440c5180003a13103424440050380100740100c3d065085c000030300415500100d04038024042500014004000c1400c28500050005000880700740807510a2180184d06412a03022480c410b01140b404004c44c0c0c1d10200a0b1802002d80d10307000403100c1e200d034405960008181010900308501135281901c40d07a0200c05508452000f512402084240c02100540007041c2d800050f00001504100002e0451032108054180300303107940d98068480340c442150500f0050700408488040e40180345401504403413802d4096080842c07001001c2e5a684028001c081e03c40c200310141d51460351001e0b8602e002e0000c0341455515240400c0ca8664000302d24014049140030740003010030f08a1040c081030f003002d1402025005105001c2c0e04000080d4440448070303800c03680030020000f0030300c10700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 535902616 1250 535901366 535901383
    0x30b071206090c18051005070b06030309061804060b0a020d1b061b090e010e01090f0e030c1e0636010507050d05090708030315192c0c16050f 62
    0xd4481e04d0700aa203c08000d8410308641d00040d115030000307065412800e520109071074149610044110702038941034002440c40c0200300c14154003250000d8402d41344041d103d44074014640560701408030f680ca42988080720700541e4071240050703000c0900081035038400c00580c02c0352180041c03e801340a170300d070700d540e0140d030712030002c3d1804c2a68403119101003a0b401051000100407040e4035040c65414800504d20100b4103210b1250441e03118030109034000340e0f5601401d034040404049a03660340c0007444040d141c1d80c0540074241400316221061031120404100c240c800d210030721220102166200c40101000c00c1c5002405182d08000302d14900840e0920a040c015030781611170a8a51384c1075420b46090ba040144126829000715404100100000007900d030012100380711b24500b039a000001c50b0340b8041c80c80c41ca07020411201c40009a04d03000e105805404915408940c101d5404460006180c140940e51f448800a04000003190154940c0081e43da061140b02034a648002d61407482d172415011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 535903866 1250 535902616 535902641
    0xe0102061911121b0a02030d111b07060e0405090a03140d0204140a1d040308070c020405180105090307030813030c060e0d02070510020709090204020c0d0e0a0f030b07120609 76
    0x711814840b2050303200c10140c2005580d130100d6850690328400c02920383c0102e00516a240b40c44450300b501c41295041902c0d484407400c014918000888040f20780d0726a51f23441004e02140c0b0b0617412080b20b05090264034881c00100c0010240e03401103039012100008880091602540144618084007401d400208020202110792250b6080d20400308000300160303622007120140d12040701c010345608010110780c0142c240c28185550703511800d0a94510144041c000d41c00341c03070241045000d098400c4412070007400d550080090b0b5442c4290700d83e5920a01102a0101d050040001e1141003020400c0f03004601c80c0c60100d0350407010369184000d54641d6150001d403900000c0325a01c034180c1c100002d40c0144012150011424506140030352201340500030412413649580c0c1e240c040d034890b40c04031000d0302011021284480240d150081c0b0001020704454450307a111900001c103051010364040a40e034001080c44101d480300c007000d0300c40b92101e141002d485a00d803800001c1040c40b0744584900101d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 535905116 1250 535903866 535903897
    0x140705060105010e060702010804060c05161b050a050a09020306030309370f05010c0204180804031502030106080604021b0d09051912080c0705100504090b010e0102061911 75
    0x14500050801d40401c441306004003424041400540c4e440001d503904030750001d4000a809019a00440b07840c170a010402203090403c1840400700f2408680515980620305000040c45841c2e00402072000e5580c03084961055145405006c00f5080764015070f002040141228079121104001c900801d0010101d03058104000100000b0003038005805c8040c501201d00000300a41405c001010301d1056000c0c42c0e04000c0c90001020454803190300460f00f92403072542070709001103036181120355035001d800222910b403400111012000064000e50b8103803080741d110801281d68039000e00009400ca500880801c646484522000da0014071890341c2c1c9054941e54154001d041c2800d00120a030b00103401c0202d5080003404101c1c0001e044039150200d540224241e6403145001c482d1450403c6a40080394030000f6100c902503416004001031080740c00840c3c1c240500d079038040c0159001d6813400e000c20f0142e08050002144210390fa4680426490680e10001c1c2c50030b00200d41030031a03003001c1c15001c0c0c05070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 535906366 1250 535905116 535905119
    0x403051513320c10030e0a060501030b100803090d06020a03150801020315010e09070f02070b030108061e04030c060b04060b0c16050a0b0712090504050a09061b05191407050601 77
    0xd8040c00c0d191036503401c0300010f10000d18140e01107586400d58803000d20170542c1e81c4c3c81800300d0940034803d110005401007000d001558590505c054016015100402204e400c5240024644070110503101440001000064690b900c1d4903404040c1d40514000420941d0300c174134601e0700300c05400340000036041610005807a403501c03030b0f80c1c0c0200341600341c2024180700722130200520782d6803000c4441b030348200c051a0021004829100c140d03d0408242c0040d03407100804000400c0d2500001401da118180070501c10340301e0309100da2102c5440b5826580600018040b000c140041170050300000300d02c2c0c901a000180290303903103041c54015040040b449115801c25007034400c042c004518401c0240030111344e000c10182c54081105020720032901c0040140202003c02c0080c140602030300001448007400a01c0b0f103142c230f80c0c0080000c0000c3d42c01190300c6842d181c10603d2200c440306111440741c14640725140351601007121601d4242e414900041003015030f600450030940c104000d0a4080e100d90002c0201c0d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 535907616 1250 535906366 535906433
    0x50c0103050604020906030406230103060504030206010515030a15230a09061d0a0603020405040b0912041a0904150315140f060111070b0a170109020403051513 70
    0x907240030302400c1c89503005001482d4203036600c5045a8000c3e512200000320410b041d00342c14085020340d158680801d9144000005015181d080184280e100e607095030350927a02c81041252071020440c01903454281803000580254099000000050440d036003900c1c995075940e016541101425012020303421540d64502e00c41c2001241400a01060101800700900f84000201c2100184810303901c0085601d0124007034814681c08000038680160040c00a85030900b8203000e5088213031a404194800c003600190204004000d95041d100c460280014040541945810030381008410641c4690b5a101216003020789512003002107204200360121320b00103103032030380440746016500c1055031054001c1100d890000004503501903404d090140324000e146c41310604c0c0c400d0540181511050000da0484843d412a00c0070300c81c07001c40e4401c0046aa250f00c00c22003603024510000340150300c03060442c0655107046040341d600030441507420388030145a0f10751100719040c40d24060f190142c4169031500c0d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 535908866 1250 535907616 535907621
    0x703150305030f0a02011d0a030c080910090303110c0f060a09180902011713080325120b030a020306010302060a02030d090312180b0a05070e04021209060709030302030a08060a03050a050c0103 84
    0x481034451032400c1d55a641f401030b0346408003044002c0410132194040780030003088406945145001170480042d50444410241030809180001d0300441c03d04c0900384224000050500d442006c007400000d0001600b80c1880310a800142e0b24106200701c04038003003101607182944500c0e40707014000104600c00f07039000160924448640c0c0480591171102040f500329016991208601d51113002550f6a079960310507404581d507403031300b1402c44451090909060b83d5002d00320888003201132108001c04003680b820107503a18098036000350140c00080040026240c240c015080c070840d20b00541f1f15001c1072541701001c58226000407008110050b072030b035490507414883c240a40341007102001c4c22034026200c5d60a580e00041c1551041c2d40c540d40010003840c496000815a69070192003551600ca10f01c9916000842c1110450400d1003548c1c0003a000ca0310560010741140e4041d00a58134000c3c2642049400d808002c04954002c5c01c40c02001000030020003036510142c1c080c030054070201070300c44001000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 535910116 1250 535908866 535908881
    0xd0e010804081204170c0a06060f0305060a050c09030708030c0d08092109190e07080f04030509040917070c140102151005040509330703150305030f0a0201 68
    0x1041025001c0000061025080791074a04941c503821500d40c0e95032428601540303101922000103280407070300e0180c0110000d040d8184600c1040d0500205844d10a920036041541c840a05951301c084081140703500607903c0303590088500020245420040d10100e85488956840000c50754000101a500352106000401c0c2c40385c483c2c1b604aa0b14240b544e01690740d0070b2501002c2d40c036403441e0a814040c0740498421510008000380c41d100c810302d943c8040504515242c4501c27801d50b144000000e1019108440c0c0754420003818840c0e5401d61542e882c120b510303070040d02e11141c000da50780c0f0b54080030070525000c01e10240302180c4200d40d40ca00074a00306018000940c41003080002d07000d4003c40381da1b00410340b0007850805d02c441045580e101c0329400d50643c0c460748a25080b03803510061141156020417140304280c2c60603090300801540042448880c07001984680764202c0900100e00031134071079000740e01c00c9501da03c0c07040c809a1301e9840d014119804900740d10704520740091901c5003d502800303181d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 535911366 1250 535910116 535910119
    0x120708150a14071b0b100504150807030f05161214071401050a0215010b070308010806010f03121106070801051801030507060305090f03040f0614180108090c03030c0d0e 74
    0x40189001000b000c00d200020700150700340f104910303c400c1e80049510070801340380d80040104005044c80c2c50544050343c1306000e502d005d00c0c2049100500e01c418001d9042c200e8a145008050681c5141c44000761010744d94801c48442c0034000e0090000099499060090301800d040d100703c21600d4604242012700320a240691500601400c104040382007030a01400282030030216558000d400c022800e00a00218425000e04410000300c0d200f0f62107006803074102d10a4590b41301c1c507600c03070035441d656440911400001034181c4205000007800040e11004030b02140c100510740c01d9007440c902d420301d5811244540051242d80040000d403502c1d5003101c50418400c0d40941195046031501f81d22142180075400038140c40304003203030100b034080280d01c0f08040a10252a01d69494040b0b11a0407030142c461000025004012070008943d05800c8a10204a0600150b40c2280c114019101c0060041400100e406a4042c1461588080c00240500405c00002d4902000110400707020300701140d0440303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 535912616 1250 535911366 535911371
    0x3060501121505060c19110102010c0809031806190c050601090e1002070201020a0f0c060306060509010c02010f090f0308030402040c0c02010c14120a050c011a01120b120708150a 78
    0x184a049140903102c06940c0140c800031794560600008600c0c0241e00f5800c00f080e661010280c80902001910204420400343e0007800b02c0070912008030382481c030135106601140c100f0003174034882c03150481c1c000e02000f00140c80309041240d0300e603501002c5240c0c417001c2e5011840e501c045070208642440742354050f02c8010030030408606d203c04155513450318400b20440c2d0740d0b030015068055a00800007012069031200d64805111154606080031a01c0340c854840400d04140001c02c2c203e01501c1980c9041130b060351000615003490300111250b07140010002c05000740c03024041100654030074030401540c040e5401964908061060100302c642d0f0040f01d06c108407000c0f2203c00140c0c2d01c0400c224036217400c042c40902e020101c080150614510700401d842c0d405000500040082d0054003410f48114208004c221401d001200c059203525a4800540090b043d070400850328061940085517888014101c914500d10380c4031110320303003000b0350020041c1c2e80c804039401e10ba4580d17003941260f0244034034034203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 535913866 1250 535912616 535912631
    0xf0608030a0809150108030a0e180c0703140301140a09090b27060f0103020315161407020607050a0b0c04120f051c0810170c012604030306050112 64
    0x1403034403070258030704260800ca8540c0c045180c440d400c003c03802d10440458066540e0b9607607400e04580d660305c06200c03103002c1a5040d0700e0051a140400006180048000090050356500340c0c0032121b80c0c0c000c4d80d0403401d00c409010562500c0019502542c0030b84034150302c44000c1c0300070034100510b04848d40c1c000c005103401c1024050005500040c1c0a4006141c001e13820b0000c2004e401c642105088074018044038826041000690460380c10f045040b2802a4155180c040c0d404c4450500f0100071240907080100304801007118510604410f04800c1c00305ca001030410f5174550000c3c0c855030080c2c00540c5c66030722544094081c400714110554201010070410b918051400c6e03141d0807030b1a00c050014100480100c1c200080c404244900022510200400e280c488448200900380304c80503280030881e0f2090480c081030842d41d610700b20400c65a402c2c01043c502102c1c0c401110700c155100a9401100000d6089001c09c4411240b9a401984240c8020950030300f048001040c041c0c1a00881e08402d050064 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 535915116 1250 535913866 535913879
    0x706030e0c1003021308030d0506040f020705063105011b08040c030326090601030b0a0207022b080c280f02240a031a100813030201060f0e0a0f06 64
    0x8120b6035a442506002da22800301007880c4034403400790381c03064606001c0040c100c40c04400a034012803080078100c03000c01014400707200035000ca00407010003d2456000002090070591200395120840d503045408510700100d40010254103200c0203000c50b036a80d1228540c521316049220300005850711490720462501e4541c50343d008440d00c2d403201a00f4045e45002d05501c0002c0700c1c5056101d940b41850a100070706103044480d0750b40109120503506210358801003510f4101500850303080940050501c039608403001c920000412480d410706400c544083c0c405070000b055407015007000d40c6800b001c2d104118070800101c01000180c0c08944003200413800340000256008045094150155120070b51001c0150501500095100302c008001c40003043c40c11034564140c2040110641c1d0181c100d01b02040e02c024000071a0a401039080032a07070990000740100c0000b814904041d0281c400854015030340d202e5844040a40d070000340301e00c0008800c0043c84103240c0546080e0060020041120a01e00301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 535916366 1250 535915116 535915129
    0xa05121506070f15110703080105151c091b0905090303130605060d200a1a0f0f070b010f05032b0f02010e12091806010207090b040e07080706030e0c 65
    0x34010f00030400c90f5814000d0100ba40350350b046810440034100140c1002c200344840f00d402035101100000c0318000003003818101681500c40b01c40c3c0910314103003000d40d03104d001c0e20301c1d429401000c0f114565032100c031404105150f904041c0003421401c10341075103040491900036558020243c03102d0f54030030010b001400b90286010341006800000000352070b2603040001d0f41c206c1c0a010054070724800c00181d01400d00c0c04100014240b8811140810030507910a90810046541441c480381100c0a00082400d141c25400030b0101e40d64000c405807400085981c0c030303111000700385c02640304514044010711040c141017182914409803c4190b5003501440c10060201c114031464501c100300c5c2a40301c1081c0d840c001d412094070074100b241500d81c0252280d04c4407801d90481400d1520038030741c900a00081d41c2a80c0b2075240503c4040c0d000e80340309814481c83c00b01410900d0811900299950b44007002c855040c0242809005641c0241c041e040ca0050002c0641c0c040d008001883d802c03000f5000b805940f00b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 535917616 1250 535916366 535916377
    0x1b0108070e04090c030311100501081e0a0b010b07060b010201021315051c0e0d14040504020a11061015020312130c0b0c0109030306060e010509010e13020a05121506 72
    0x345001441080c04401003030180030fa400c2e000381400101d000100805401051030450400325030200c45070200c16801400540e0428480d108058100d2009030320303d9000c40101d4100903030960116440c000440e41ca0a42d90f22090f8414000d41c0030200300e16007002074501030b92013119004d10080d42440800380607027400100d20310078101503409030344078200e0041c045d00035105604100c022001c1c035081c034804850040c03e100b121000050107001a0110428040d05220106038094058a4106410082413100960054031110180510f200c1d4180100c0700070044144142c0303414201070700c2c0c0c0d03142141d441c000000d40352400c019500144909904001c00403d00340d030111a0124200b2510502c0c100740b04041c03000e41050448150005580c01d9811054000c42100c81c4642c2d03042225907a1038804a564250320000716000801c00c100c400714944c4242a024100c12000340540180364485501404a030301001002020a80105079444224002d111503540805a9072040350301481d242c001642a1249 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 535918866 1250 535917616 535917631
    0x91805060f1203070c0b130b090f040903030b0a06091d1302041b081f06030921030b010306050414040b07050c15092415060c0115081b0108 61
    0x94100003401551020411401d80300040d240c0503007071034039840142c0c0301d0b84090400e07034068080b81d81c0020700310b103042d00325103807445425942a0024106210190726921404807542d2214201d003e88687d55a64840c029610744203860003e101d0340d0040502041e407520b17610400902800b44010418045415484030b240a01080c1c48a150f50f00c040b0300742003a60b03541d0380c00707034005160590b2507828280b1100c11900002241e210b400c056903418803048000060040c2c001884e21802004021490203a00304c101260310800386040a5809180e800611081490b00da0000980340c02d141850355030148500d1028040c151070510400c202d5045580d510800580020440514a00080c4543d44201300751450010948140d40d0200c1c0403220700b4403190401d031115003031400781c41031401d10400d0400010000d100000040945a541d24511201c07400182407520b400040030001304150085c00e11800301e0030440e41e17034144402820b14002d1031422142a40b03244441500022085042c2e8000c40d001e075000d400d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 535920116 1250 535918866 535918871
    0xf0601020c0d030306180509061501170903070204050c090f040603021008061f12240b0f040803040e090106060f0903061d1014090106031a0903040f031209060918 71
    0x640380031802014103034000e02c1b5103600450f8840c80e1151580020f0f018003594811695140c4810b42c920720b89040603600f040c0450009481681c40c0c0f040113994546c4003070028103a9090040c16008901901e1088585148107000000d2442c85403074480c1c0c803101c8650094404106803411540420000b440507020b82007800b0441c400111140d4640d01c00c2d0085407200000e52501040020303000e40b04d1b52465012801c018140f100b4101c2c0e407641d95130040c01041101003402c00c81490404101d229500980210740e20502c20040410440d90800050004099800b1059102d10300140000d0845450383c01c0601000034415122030300c160700c590364805490700140c000601548004200b44201c008d03010103603c0b8014181040e981e403000d40d01484480c0d400000c040140ea6800b11a84e08032a483e000c002c0c401002151030080d10324031400c5495110b00082c084a15091701c8250300c15600c1d03240c1d8011a182e070340724030044501e2507000c0320100c010221307410812849030030704030319464544041103080206036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 535921366 1250 535920116 535920139
    0x70f0b06010f1b111210200304080a08060102031902072c07080703200307171e1003140f0106080c091305070515041a0c1e161206050f0601020c 63
    0x581c5c4280344101c5c40c03d880100d0702d01c00444074050703003c0c00e0b00b41041c0104000d090000294103080d81c0450b445158045882403038124100340a48003990040e0501c0e0444c80f0610014812903164900b5071000403554004120a40c40c00200c1c821001070644c0e40c44541e02e003100d91038145d03030309030312429044100d030b0030a6005079640000480007444020350407541c2000b01c1c074035a446280c10300000c41c0121080d40c1c4100c4c10090380c4200a40b9008142c80c009408041311368106c0e000080b0100301c40c1c21903109001795080c1c0b03541c0d40381c0c4148810f00c4412a00260000e0b040048075440900c1040000c002d100042c003015095500010001d58004001c0020403d61a103220b040040034000706008e00b10040c0f44107421004000900a07a0f00b250040d00c003220103c90010300c0d000071242c160741da28544a001003904441350b4030800b82450f040c0d8102840b501c01c140e20528140c0104282130b002d088000c0d421145030368141840b03425100050b0080c80e100603860140207050740e0105185c20b094006441890050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 535922616 1250 535921366 535921369
    0x1f0812070209041b030818030c03060c1b16051801060f0813050f061005060301080303130c0e0901020304020108071d0105180402040f05030d141e070f0b06010f1b11 72
    0x960115110341441d041301a0040200400400a8203d202c8101d10105843c4900e100b416a40c4004890302689a8040702c002004180300f2402808003071100d48174554244c411a003150b1034003d500c41d5062400140d0a800e000301d040c40c1144582e140e08000e0b55020035454808094200384560030000c04001e2500005450121a107686060340d5510504a450748054045640d803141c2040e00c002048520f02c29000429240a80903613040c1d0f9611130180d40356444a130003000b1929141c0000f1118503020301e400251503100b080700d50748134000740340003d6601c6c90548001084140d00510080c14081042d1004d9030f4040503800314512030a087c01d11603a0749120f401191007080400d80c815a010303000040101d45d03580e030600c170442101c5c800e9040b9903a8015151040d41c6911803a100e185040405010711641030514201c0852050a05600517280480a0300e80c5020b1500c040f0061704ca000700701d0140100c1c0c0d640310003041c5080c0e840345000f0070442c0141c3c800c1f00003460454800741c158403a001004945 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 535923866 1250 535922616 535922633
    0x30115050711060324010215010902130b0d020403060506040c080732040e0106020312041b050a0303030926071104060e040c0f06180e090705091f081207020904 70
    0x980b1004104944a28000d4084010705007007108550a03640d400c00d060a965000103030f20390407654075001500f943da003440e0130000290811081c02035400201c1c0400180c00c4098402068141c4e0f400c07d0140e552030850400f40d0075200d0141103d4011032408202c824650346c042c2003036401502c1480c000d9200060381c6180340d10101515203580a91a5802103ca000358410008100311202c890f407007003041e80c0e540c00580e2a4000c4143d14182c11050000090015070904c2c02c5841100c4500d9200b1455a21034001c55000340264004601003641c5180c513500b17115420b00c0c0e64542c000307a1a0503048170007505020007424040c483d40102a0300c8180c4149a03999a280c00c910040c2c4160f41c1d0a01a918050030020780c840b445200d92020500721410100c0d40301c0c41501e800c0d01600c0d1413080d1185940c90405140c0076424003d0000c82940035020001c00c1c82e5031000c02c0c250003038400a600642d070320000544003122507215881483c0c6030740075954800e00c00c0c403400705803000c4580403214004140d469003402c001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 535925116 1250 535923866 535923893
    0x16140111070801060e0a05060a15020a1b031e031209020609030a05060601090603050601051207030f05070e01030c0815041104080105040b0a18030207090c12060b0405150301150507 79
    0x1401d0007080c00200e210032055000408940d6000121859a00e4501a40c8111036040d51069000900c800080c0110380c0a2205448608110f10496240f0101c03900c442c0c800e200189000d03901d008540000f0001d01c4808102882d18007168941c00040900c1903801501611240c44208011a21142e00d04155541c0300e06607400c1c024081c0941d045a440d07490260b0301c030542210040c3c0402c100150103d1101c0c42031042a10071441a146c041c074200039448189030f5600e00405030410551203040c07140b01d24510b4016103004182da52a8401c1c0e2040b500d0015040d034080f07002100401241c04100500000300c41c0c0003007018001614005a40149403541d40c03d1403055800106041d0b00b448203000400c00c0041340c00f4802c0814550401520704c078a202d009081c001488041d0042e0310442051000d0411503018800d8220345040110585411a14100942e502a4080805003c0118080090341400b1506a25080306043c17420703d5517040c240c83c580740c52425403000c0d04101c0b02140c1c110030400d610940e041c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 535926366 1250 535925116 535925147
    0x3050c090310020a14070309050f0609030a05060403080919060c0311040303080f2d090c0312030108070f0605070f02010504090509060403031409280b0c180102161401 73
    0x2e00e91401620154042d41c0000b42200c000740302e01d860303800d13080e80400030780f055140e1590f92924082d16103010440840302140c9425072152082045011075a0104a180c0c44988500041c04640c989410050503001e00101800c00b1a0024404000a02810300445c241c4541c0554006030707100c15408102d00501c0080844160408001004818560841c1103548148c915100c18101641c400c00801819142184052340300b21803507000450074695680001c1d40800e002c422901c10440c2580007034a015440064800c84510000c014401d50390203109110190001581c8840c050b0302d00480181140305441c0064200b282c00c40990046a01c200d08036001000b02010a000d80e061880d00c664460701c0945080300071910741585115a04c1d280121039104200000107801c0604500c808440548090841c0c0d40ea02400c52110000085001040e1401032a0555040d501e401700a104c2c03100d4003c01e170502d13a0642d44202401180c11f4682c071034201c02d80700ca0000d0403210140220050342e03407404508858 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 535927616 1250 535926366 535926373
    0x60307170f250819020103020d2711030109020102030423030601090e060703050c03061203070203010e030301031b03020a090b0102010e07080c01140301050a060c0305160609031412010603050c0903 86
    0x40e4484070203607850141d0801c0440402801030b61115895071354081c4090f8020116441107090b805913000f6400f0741902164400045000001b00c000d00c251403aa0045406503400c0441a030700074881d200c42d1140342c918080c0c0c001c0201d03c800343c00113941c1c0c1c01184686025580b0041001e250b001c0c0702988a00c0c5418060100d84140d619a840c80c009000113801803c2144910000100010702c01e0141b58090380b070b07401c007941c55911851705000b0070808480e100051884101310000040e2070910071401ea0b1650080034507169411468090501c4008501c00c0d58805445401800561768240882d01250034550001802803040c0005038050b00810540380e030305015650001075080404980c82080d80c001b40d986040d5010304001860080c0000e0080507040031862106011841c001c04181c4852400390403d0f50030001c804808107060480d006c3c0c12500e00b511031906904150300320340c442604a0b071101042d41003103540c48036450350b80014815101019150400f080c1e900b0300b9030307084910305140a8280c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 535928866 1250 535927616 535927633
    0x705060408071511190f081605040f14030c010f0f03050604060810060906170a0b0604090b09030418050403080f06010915111204050a030809041404030e040b0306060307170f 76
    0x40c0544c6800100c5100c4800c0c040f13070800f0003014881d01600c24034070038540b030342d00040e00d80355610b14842c40300107040803e2107410000441d440c0410031005008019650b42481c0d0040380718103050520f81c00740c424230b0500058280b800b1300c2c560080d186040030545460001103a40d10304002401510241d4007444243c025003228a81030b082d10313006502039450008040c007000703a030781d64140d551540e9004004407503084440b040d0300040350185c1e010380000000f4800b00e16403020f915051032100082d24401083c0d07000140402c0040b810a50074861a4400101007000707103001d407000341c4140c1c80100b071051140000c03c0040d03210380c00b03000300d90003410242d02c0c800140b40703030700740054003181000300f003545a80303e482c0a08184102c0e02046809652020b4441890285195140000d0f50030081d038680d400780c4c480e030b40c204e862901c00a2252140340280d5411036142449020322049072a564016406074005508200b941e440001d47c0404640d0600c40440143d10501542c9050850440070105140a030008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 535930116 1250 535928866 535928891
    0x1410030b011d0303090d050a030e1e0105030901270c05010504030c0905100e0a0c03061502120f0f070f0303150b090d05030904020406020c1002030a0909022b2007050604080715 77
    0x118460090300c280c0341c2b200b506000804118a4254030315845c8100b00344c00c08400810f500c2000510f0300001e03d100040303600851848a041104010500b1080400c401d489840508c20f0b2201044000d09003800e1140c0b0b440d00b1038860780c440190b5409001e60302a29000416103254450107000010309199080d1920f50030700c50940c0303002c0c0892030386440010703007015004280e601441c800a921400f0a0300181404c40c540a00c0c10f41c1170f00711100c24010303420b05002d40070300110704070020201940b040c4d0358000324682d1443d002d01161300303800c0c40b000b100e403003910107002e414040f5080f40c0042038100d8090280d18803a150841c41c40c803a603000c0d0340d0858001700340011040d4000500300c140d860f003100c3c5c8502070140004100c1e901d01800660f000042e4103014200210300b03440e40189005c0d6140d6140300b4080d20f804001440c05400603880701e20300b030341c0c2c1c4441850103a0050030764114034240b141c4c1c50303242400e00d4481030b54803040504040c0c00b0220000d0705030104a110308407034200e50540f440603c2140304865 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 535931366 1250 535930116 535930123
    0xf150606030e0f0615040504170f040303030c0c0f081602060408030a030b1e010309140d0f090b070b0a0b06040e0c03090c04090f030c0c08071410030b011d0303090d05 73
    0x1032442c005200304045800305920114069100d181802c5040849000f241c040002800d406003050340e403d000700f5542e001401c55007005000284c1e130110207550b15851407074010115410680301070100048031818000141689103018201904185415120243c52140302010300b80c4080c001d50040f030000d40003514260201c00b410b030660140d1001c00581c026076080c0162003002c100340440344103100410084540c0280c1c400001e00c2e0058405104515000c0b00540c54026040328000c0807800d1011080e8030710780c0c410200c101500441500c41e0074a0b6140d40c0b40c2c61908030103000300e0055919101680c01c1c0b5250442680c00030a00c9150780d114038108100d8000b0580c5c02541e100c41c01d4040c001c9042024241405524082a0701082d01c42c80e40c0c001b0b0310129022102013108a03404002c8030710005580c0c0e820000240600f038203094000f8020307c0201042140f040e80449001032508128420403543c0e0028526950215289082d08081501c040042d0a501c601d41c0411b41c086a200c50741e100340300001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 535932616 1250 535931366 535931381
    0xf02031b0f0114010b0301180f050f0a0c05040b0a050d020d06120c0501090506070f14030d0b1815011b061109090906060306310f05060a05130f15060603 67
    0x20469024443c02c0000070000174007903140200400c20040048102c401c1c4080202c104c0343c2d80004501214242d040c0c140d6800b580c08204842e00384090041c102d03c00e214420810b030907420071514061514007158a180200700a00c0148480414410102040b940440c2c05d44040081c0030407e294540c103841215040000040d15002c01d0315001040f103500034410f88041d940d0040800341070000d00c3e0b440030741900a401d011192003001c2d8403070841e503400c01c00103001e002c0e2551402003901c1d59200306104404441d940c440101c040c10400f03200848801c07403c2112818020f19140345450441016803090001003d00140f4803450142c032401545600d0010b1f12609104903000c2a4644500e019169202c2065038942d43c960010070100c0c3c6404a841d02c5400000c079403042c0d245510381c401000d01c8a090284000391380d03902c00c40300c42d9010804107000c503590101c00c0413410010760030146000c00f125074058000404648603c840b940500c130700030410481496014906001c20703a15841c004000c1c1950 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 535933866 1250 535932616 535932643
    0x16021306081e07030f080702090a06051c020d2603010e15060a0906050307030b0306040b01081204060c03081305060a0e010b0307060e060f0f071a0f0c09010f02031b 72
    0x400e15100740707602c0b001001002d20604480105906411912241041921104100c070b0b881410000c0078016220500540d01c601001840050014a400180700f8091407400f0846801e40d01c00d100c4a005039103486056090b180c00050344a40c103e0001c01040c12580c80144a13031489801000001c2c0c1410000341942c494600f0501c0c144030843c1c0b000c20702442e40a149856800300360f20b00c07018080d603032041001e150300080354600400c0c07071054080440e05281060750242d41c0303e08118018001050100040d203008014001c840c1e180c10315014005290500d0480000c0410840394081030f0403003207510128042c96000350543d009814156400d2004020001c040505c0d9400e1810400d240c1c0b4001c204042252844d07210020154610303403c1001c26070091524140e038034820b221100d21171003050046c06c146881040345d02c0101520300c0321403004000c010010800d803401d24080021f02042002680c0e05480207080101180008480607415402175449081c00e4007440040420300007000105441d90a81 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 535935116 1250 535933866 535933873
    0x10b100c08180a05120f121c0b0f0d06050a1d0709020711120c0a0501031a0103050a09080304080417060103020604030f020a17071e14100c1e02040e010e10021602130608 74
    0xc1a40e4001107500684083c4607c424070860b079000c24a405411280ca00d0000a01d401c442c20314003000039142c1302104808cd150241d07190100700c4020120300c28203081a82d9680805c0d1440001d24065a440d100c03401010035054020070401e0401050003191030000100604060070544c51040260f030307035800e841d60321b403040d079061100003960b500030b200780c0d1940c0404504c80c081c1c101c07151005401404016282c031040540e038682c540c021450600185003e00d1041a143d0350344e074a0030303400c1107544220700e0803c0ca003070f0064001040140d4541c0c00f01c60444e80c2c44111a07140315110300004004200561090b0403459044020075460607021a84800341c4103603e80b4040740740700d0000102d00c840300a0180030b8089a40b142c02d2049403821144150000d021b41c070b41020401c4c40b945d10903801d050942c910010030303182100302c2d604500d4180181c498040f8980000c1181e0444860460340d128a140380070024150b0002c1d0341a6800411014100d0141d00601214003001c0f5010320340005190700d02c1405620b00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 535936366 1250 535935116 535935133
    0x5060310090c14060c0109050c031606080f0619080706020f15040212030c0102130f060e010c2604080f0c0907020c130e010e010b100c08180a05120f 65
    0x400344034054069821410032030815080c00505003007403a0f4480410380c014002e011700318550342c09018903c8194410300180040f242e5003400d15181c04298007500617280785009060001a500540c00f070382c804104000e0401c00c0d00c6103000300340706440102c1510207140640c54041400c04000492900711a10381d404c58101c06405494213032141c0780a04219445030140001c41d000d0b180981700c442d03c0c90f0800e815203103420310840485007203910182103564003003281041040700d6900005541c0060070582030462490303500d80c00082044042c100001e28030503400e1510003550f82500030030b480d0705407007003443d654858441c00c80303070394401325019030700390368450401c02c40e405041440505020300042d8000b04003140d5403108100d031098000b078040c40c02a13070703c14184401040034000c200607001014000a1140517200a00029011030290303d014403118144242c0003404220444680d846a00d85000351082c121000408000c030036403229522907000d0811a090100100d03015401d00c00003000ca44005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 535937616 1250 535936366 535936393
    0x501030b03060f2205010b031c1e03061e092f032d0f100609050111070b0417060106020607120c020c030d02011a19060507050c13050603 60
    0x103403a410030103501034009402184458906508054210010708840c040d0324814200000b141340182406840c1a034662154060300c0c10240003c10707003580000d40c0008049600d6001425a030b00901c5100c81d599031070204046080d200f6840000544829070010b040f010001c074802e030b4031070018050880c5540c44d020902e000644884400e0448070808500240116800141709003141c000800d0b03042d904040750045800880032104030220503212803150849405c0001140b2040c0100819400240f14001302c00c0c44960b400692540486009103801da0500e00400340e02400c1501a50010300062004280894403018640345011540c100f43c08a41d2160b0381c1e04812642c0307403020f0300c002e80450783c41c1c0d2002c4000251030b007000300002220700403a18080c43d000e0103e4904806080a040182d5584a40307220400111074820000303103040b289590702c000040b0280483c80045c0c8640c00034030400280180400034248014128a0310040c0b48060000c003400b17914014020880d40c00d8802c2c00392007920a004c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 535938866 1250 535937616 535937621
    0x609030903060c0a1205010b0a12051018090c09020903100902010e06030a200a030b0a0b030a0e15010803070204060503031305060f25060b010801080a06053d050103 72
    0x3640c0080041038242c0340c103907003110542d028509180403c001640c408400c41c0050050900030035040701616550002036a00400880d02916140c030003905000c2441032404060950700103039181540c94540d00c1c0e01c490030301801404070540c000e2121010400000f8108a01c0c0d0150440040079407d503a00010400b00002c03c80d03160311002408250342c41d64240c03490801001850340440a1000042d40e40c10001740740090040410088002080c00900300c00801e81c980104c039203182d425940640d0940c10810f041015000041c80e03d04682d5880c40100e150f44800c01c00100040b122a400d0320095864010494480e44520130070390041d41004030003d940c0c18000100c1d140d04045842d03401d5064108000c2082c2d41e8801d500c241d070a40d40900881e61400300030809c406512078075200b2103852040610b882002c1d43c18003440340e418081000010040aa004581c0e030a80581c41000055140c2e2030000d091000209400c07a0b00004007560880070401e40d032176150f2020310004620020070b041d03440004606 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 535940116 1250 535938866 535938877
    0x503060708010b0a03330b070b0c071b06050904141303030b0f0a1d0a0e1209011404080d0e041e020d0f1410140a1217030a0b03060903 59
    0x6081d00c00100004039009000d130028407070300c0c5000301da211224021018080f16504101101c01c400007000488540020318500041c1200020780b41440c07019111245d25900040a0301c044150000b802030403c10784480001d100540094094540c0b034490070002c0c1181c00c40702c0014000d0307142140e1114545011010507110b069070313002d005043c21242d034049002e09200c01140c0d0b0040c951240d00643c0c0d980d08440341c07024020221100455090188100307445400241241c0b061a01c0c1a560f80109000814142c000b1a060b8207115501c0035503100403901c40c00c1d2501e405045a80c00b280100305102c010171031142e46011a610000340301d10101c200403c0b035a002c031043c610f00d8031038201010f524460303030080c03e800c100e405400255200d0703100c4120283ca03494032107a0030701c014070000c0000040d84040600040d00c092000c4120300400e01001c905c03241007500500c0341781c0240c45110820000b140110b20300e8000d805c2d2204c0e45a040c088400c00180081e00b5203107109008000c0000c2c12850000250ba4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 535941366 1250 535940116 535940131
    0x7051206030610060f02010e03030a0e120903120f040506160201030f060e16051c140906100e0a0905010c0905040e0f0a06052703070b07110d0503060d140c0307050306 73
    0x22051498079009617001c0e246030350703820195500c035010141c1380c050a00c00356210b0444003c0102d03c8004002001c1c1c24490090b80740800464188850442600d00140b100344500c0d0b13500c80e0320703a22410984003000310b000d2030f44055403100002400542c0340c00280c079904892072007030301c1c14804803c50300300d954141c610702d019000b00f100381d1000140525095403001c03000c1580e10700b0540c0c41e2074100c0c8510b1100810405a5011007031f25a62900303d43c8480107580303a80054060094001420818980b20205001d40b00b420326420815010511000d5160301100e80240c0c080020000c081b60f50201800701c200038441c0d1b0348102c1c0f824485c0f841009012965561580c28600a000102c002d0343d200d50052801401a101010f0f0002c02d01c041502d5058000c0c0315004074100541e01c944651601c41c0303080b08014444001c00409209400400100045085100f81e80d410a251281c0c0c62a000c01c1000c49940c40c0500760320390840d4600305226010880940c030000a40942d05140e488100b416602d00c8240d40d044d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 535942616 1250 535941366 535941391
    0x2010b04060b03040f02060d060305060c03010e1812091201021b010506060a020a0b1b0307090f1203051b2107060c03020c03120c130b09040b03191118070512060306 72
    0x80149800c1f8000e0444482c1840300281498803900c501385400c90440700b1103008900000180010400180301a5000075443c007000d41d81c051841d0001e885582820b51040080401314080e40160380e5002101d039000e050340d008540b1060f1030395000783d030494034140b00791641d440c2401041d01410254216501403501e60001c04070318520380d0300d14000c620000c2150103014040402c0340203d44003540114061301d041d94440b0281c178180135503020001da842d8800e81600c1402c00e0400000390301720707081d00c818800105001c1d01c1c5052100382a07080c540c007040a5101c0d180112988128803490401514003240221403c00c0601c180740c40039000c9100c0d021102075076074001d04c180310460380b56240a59100980000c07a50a10451080043e82008242c0102c100c54002082a4090b42080c1c412003010620840040500b0b030201e00459000e0002000c02615003401da4003000074580f0b0b201c00003031540e90520302c000c40300c0c80c00010050081c0c01041040704044c4202000c91075a280001c2d100d8003801c0150404c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 535943866 1250 535942616 535942643
    0x3090b0d020a091e1a0706090317061f03020315040e0a1103030a0c020d050f0615030145080a020a02100903020f01110f0601080d0210150527040302010b04060b0304 72
    0x31701354501c100c00d011108400c00041001684d140907203000c5600c80e49607170500780c2045100c3da810b0380d0700400c1d03d03001301403600c403007113001d80000f8243ca90190941001613807a1122503102e6442021070b011a6005400d1880c3c1503210700b000a101b694040c00707000d1000e0400d00d1507040544034480c0d0502c00340041c18161104000d8903000102218440c8aa4110340c4203c08050606081c40d00c11103121a09059450707a10b100c1d420b083c081e5000c00c80c28402c020a06103034003940c56100ea0a1401100010211141b94030043c05222818000b5240c00c49c45a540f40e15a00030001c1d070b600d03c0598200d000d45102d12a0390f040e240103d44403020749034014018607600150000441c0d40f20481122801c00d489140102c003505101407001e02c2c040c204020140143d500c40107406403400d400092100c500629001146061800200030401920801c035114030039440181c1c42402804810030f00380906040d8242800205501540701c00702d680303400d5505000041e0307500d044850a000c100d0b0050140000a40d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 535945116 1250 535943866 535943879
    0xf05060f100c060f1e141602070b0d050a0c02120f0d1113090c050a080112021f030e07051002030306150d1401090e060405120703090b0d020a091e 64
    0x356558030844600c2d00701c000041503207480050f00d9802040500a5503128038a00b040d07054180318020b11020f544007400704100c0d400d40c143c003405004110005000d580e5954000583c800d00c5017034028150b80c040603864220b0380002c14020714050300c81c144400d140c02c260342103290000c034680c040b42c400307508440d00300ba02420320021603502c4140207110207580c81c88004ea1001d080c0303015096040c4d0702102a01d02c9410403408104940c141e40440007031000c14020b84c06045c1e0b2100c0c545054541c403480160495000380f0204842c5010342c0505002c031040040c3c1c030290b890307040e07211003600c011520464000607510014031094900100c82d401c016003007000055124206082c4062000008142083c0381c9181c141703001c4100d83e286108240c907482202e00400c0a41500c0c0103200c0b60002c484003508490034180c0d2190f43d5014400101e01c121140031480200381409000c40f84010240c020b0503550300e18221007580001e510000940c0702268680307001040786031103480501c02940f030301c1d440711409608002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 535946366 1250 535945116 535945129
    0xc0c0d05070b03100b0a031a011d0f03190503130f0e0106201207021908150429180a0b0a0213030c030305090a1d0612010207020409080d0f05060f 64
    0x14044c0c900d01a01e240002541c03040321004002c0d802d07050b580012043e0200e0740703001e00760032400c13451810001c1c0c000c01d01002e14090108140404012a41810300300352aa0100e81002400031001d200104801032072014004040002d2a54441865802c1c0c41c041c2c5400036412036a00c0c500500f84440207d10052029502911a04801140c030f103842c1c0c4503495a2442241c5412070002140740ac4400218100085040c03104145031031500300407080e01074a0400e42d13226600c2d00000e0400501045040104040c000e0041180e1668103040d007112041c814068151003401c2d00940300e01c0c1d1504a1444ca24180003004121003c1c125440412411107444030803c0f40e000c2e40042c1041da00c0701041150010001da54407a0980045100b521841d846422440400c0f01c11708075503100d00880404954110713206501c020420364841c030b08980108a404816140d1402401018002074015241242810902503100017400e900350140d030b0b0a020540c8400101001d441041d6021900b0510900e0b06810502d401c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 535947616 1250 535946366 535946371
    0x60708310b0601110706030e1506151c0906060501110c0906090601120f0f06080d0c06050403050d181401021201050f0d12050310060903112101020c030c0c0d05070b03 73
    0x149480c00d000c045158400c5e0402c0c0199014401003540c5400c1d44411500030300c01c007008140b0001611115190600216a890080b01c15440500100080c3d0001884408030043c02c42c00110b4400c010503000752600340010700c1e043c040d00703010a03010354040040c0400028107024840025280242588034041448507a0002501c0c0790306000309141c408002d885144220283d4418800020819580b403154250807610389801c0500c507038202c16203100c91b0f15002090a410580d020000140555450508444074001d040c0c07042c403214100140e5001d000c03a040104000c1501031610382940030381251201c1e00300e02c00c0100540301000180c00401152800082c0c00314001800750103000c0125582d62204207800c40301000d039010800c00710900c03a2079000c0c908000007030012800d01104090846d01c1d103c00ea48048074480307100d4401158142c08884561042400e44101c9000954076010141c07849a100d8010a100c170840748078010204140d0b103000180644401e40050140c03050b5410710303d01424a6000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 535948866 1250 535947616 535947619
    0x10501050904270507170c0904110a030c09150506090a03030804020312031305101505060706090503040b04030308090601050a170712030e18070f1b05060708310b06 72
    0x1c0d10300411001281d01c006890030310a5011700202420003c1189059070303808100900e80d030080041c108079440c3c1d999429040398110004003202c03900d150000d4038040301c0d03800042144c05084000030705c051160304a41005881100c882050321b49450a000d46030051044080c0e002c3c03208130701000803074059280540c2090000c0c0945d0f8005009200004055000340c0701301d042c00017055808410300205000310420510b40c1c04091107002c4a500c002c0014048a000b200d01c203c00c005604010000c2541c0059407841d1b1003000e481d00c41e584c561644000d90481e10041e004a40240001601098040349640c1a124002d200301c10f024103002544c0780124081030304410520030484d02244000ba145000900184030b0b541c1c121850303030701c0400d01a0501001c41602c0c600d8002d10b050090140e0099145c8549032150314003c6006900d001c0396140e020808030010704107001b048140301c03d1581c04001c03d03208a003007980d8002c00400e45004458140d0011600040700e5200c1000400010504402c407500f0000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 535950116 1250 535948866 535948901
    0x1011030d090803060109060c0309030b130b010801051b0f030a020a0c0b09060106321c020301090203040c0e040b010b030c09030d030923071716080a02010215010501050904 75
    0x44030861012503a004000b503444a00200c100181d41d030f1310028480203000a481c20443c0c40c16281c0d0060040100360000405018960002444103d11400b507000300c9500f083e44000e46503980e208003402000180c40440c401d0400c42010180941c00e40101c8000c602070010061030340e526458610003d40102d06008200050075020401040180524600460803800070380f402d545404805000d48c1d5044011401c050441c1e0a4041806203004208107017a0040ca85956200c418900505140d240400d0700c4084510100021030020003c5d8061441288104280b0f48803c1d00c2d046404040101124000c051244420041c44042e400d18084d42e0001d0000768001d0512015000007800c2c580c20b1040c81000075034900c035203000c1c0f08a40e038400d194400351250740440304002c84a5240c42c6c1e5034501400d282036a0080000c548901d00f08030f0b4035150003407101c80ca0076841d140d0034030b6500c40c201003c0981c0184a68508440c00380c1d900c010190407103c050312260301e0240308105000141c040c8013401d4a4550 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 535951366 1250 535950116 535950127
    0x5030d0b221b030e030a080c160c0e1e1821030712110921010615020708010204060813050a12110f01020a08040219120c140d02101103 59
    0x4104140c0c1240c1c951800c002044a01d110804224a1044506079404050603e050001d610034044211010f00b011850541d006a4400e60414001d10170206d030b0103000303100030020740140024442d400f0300b44d61006034010780d10307100d400d99a09c40c1000304070b5a0424402160101c1c840304100c00c4000f0003032451105481e001c1ca04004c00c65281c9403900b510000c140400000c05c104107500c01303502c05030b40780c0c184800c03c0300c40c51000d8001d006001d240e10700fa00600e03149200c031468001c1146481c1a01031040c0007404010f44401c106c5102542c04100e0b41c025120320312010400140600a44090303030746540e16800d540d600c100b50064110303428001550070380960010b40000c1204068150f880180301d8598103441e91090310846d00e44800d07400521750b613074411700c940080316522280041c3c21940460f034480080c403c012950f0700c2c40c1451342c0003d0203c4600d9035034808101c00c0856803003c41300480480c55510403114180101c20551000087d48080b4060a605240e8090500700001c088900103ca0801c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 535952616 1250 535951366 535951399
    0x5120c03060705030114040c02060c07060b030f011e0c080601120906050c04060f03050606030a0b03100921020a050c04020307090f0b04050312120c09010e030307030806030705030a05030d0b 83
    0x900c090702c100d03000032000030042c405802c0040c40704c50081300a407400c1000b0108240029102c50016043da171a00364005000401d001040d00004207210008069440710324041c0341d42402130035400c6403003480d41c0d080c1c5030b510302c0201305100d8900144401e4441d180706980d500011514106a18800c2846da607561180303202142c014400c4034418110164400d0b40c4605180b009030403100808074120816040c14100092622a501038980041000c0c0c030204188801100090401104000a00c00c2d03d1504000d801030000400780b0300b1500d030203100c0c0c00710030713266000b0304903240c02d04510040c107140d2000c241c2034403e0400d54000c591024041c5440e4900301d803544440c1048000d81d520540c1211004141840f0919082c01903400768486404501e2408152148000611000a060180b0f07181e000c06c0304002039002d40e0344400780c200b004041e030752b507a040c514024003400420b6030464080e124100012400d0b00703000a50314240f41d000303030046081441105115001c0c000c4010311941021401000094a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 535953866 1250 535952616 535952623
    0x40611070c030b060303040b090906040e0d0c29070e040605120322060906050906040f2903060d081308030714060702031e090109030b01080a031103070c05120c03 71
    0x8510995042540510b1400c1440c045072001d406075120ba041000104600715500040324145001038800329035640d90040054020011048900b060b8021000b40000e024cd002030158842d40c810588100d03102030034000003801030a02802130710300c84403200200c0c030842e004420740c000201c0b0003800403036010b45480200c0c192620690100036180e0001c641c9060314445d01031140203421264a880e00368921f8000d00510003107207403060741c040c000c0004002005848a03422503018000e55101c2580c5656103204403501032200b144400e442e10011218a00d4461241d012240543e40003080c80e2100381071a00c030300013561710004e000e1004484840b0006180c034820702c0503000941c010550f12071003480601149080c034900405140840d00300304512000511800070890b0002c0400301e0031500c0348140300068612a00c01e410217405003c0f55000081c040310000340381800103219545020071700142c01ca040d5502c0c00b48580082001c2c968000921003070170240d080340c0c00d084c2060200d40030522201d020030b0a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 535955116 1250 535953866 535953877
    0x120605100906031d0c150c0304171c120f140f040c060806010909090618050c0a0905040206160f0f0503070b011e090e0309180115050c06040605040611 66
    0x81164400300b04682501071082e02c0340d03900018a140031031080c0c00d407450340b030b40320f0851000c0c89102c42074550001c6a89038800d94110721206021641c0d0390f034807200003500880e4441c00d940700c1c40c42804a06084082c600c1200c2c0e007540c40a454049000c080d072030003031001d010810142d4441595904040040d4010580e5182c0078590340700e01d124940c01d0a041c4110903208a400070420710184106100103643d00100701d1084440507035002980403003030701c0d26a001e810340329500d2064a0f8241c80c9032040c040c02207201486c925040382c842e49100ea030b61240303c00b13644007158040d6002509100355a030310f20b41801c2c81d411492003210359012080c810b540b51100c003030440b00284c84a0740003141c44400c003c05600050702602820b510320f4a4510048000c0000040c0344c092803e0883c1ca03081411700203201001504c44c40f51000b4019690041000050710301600244030725050b46203003150030070525010307030105d03601d1102420140440d035607203840e900c01400c005001100e440707a880c46030610310111800a800f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 535956366 1250 535955116 535955149
    0x201b030f030a140702061b07060c0e1207050f040e031303081207031b0e040b032a040204081b18040803060a05030c03100e0304080d050406030501090c0f120605 70
    0x340c0700e0511500980842c1d424503034904030062000e0901c40d07140e070002001a404a0a040e8920f1a050810702c81a2503005042c001000f0a091402895000350410351280403c0c00a40d000340311401c010080c00c1c0c1d590500c0c403070140c20205845400303c05042c55041480004481800c030303860300c1d0a04980151012141d40709440e0303600049010301d248400c020381c280e0894010725041c0b00e000b0721083c1c140f10f1843c80c5841078050003031810351100705031106e42168a01580003825940c10040c0815644c02004010603c20394443d940460034003140750a04c291400c4d11440c2d0010642c0b100c2002088404c4000c0f103440a500c02c9040001e90340000790749252610541c8544a0b00303841b820103809204070180d240d04030318413030380041400500c135440000d141a0300300310314800030884080115240342980700780d410052240c00340d1100000d0140d0070000902c11590180d50030040386c0c0e41c1d03440714011144440040400544040c29040d011032203802d100c0084101450002541030f07448d00041d899165121606 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 535957616 1250 535956366 535956397
    0xa05070e07020c0102120d02030421050a030e0106031a0702010e010204090902030d02010c1e050910080912030c0d0f0e10050129070201080910061e0801201b03 70
    0x442d074140507485500a0030b0005200e00800d002d00349090380034090102d0303001e50703020001509108044007118403440c2503100e00640c00080400050030b0354010418100441d00704020b0350682c3d4414411002125040700c100380440780c007010842e214400280a8200711343d00d441d542106c60f0000c3c8010002403405940015840c1e071144103150500d5180d44610055901d0700c48502d01050700b2464007400d16403400c6800c080c0003030f002410380c1c1c280501034002d50081c8461000c2c1c02d1254200010a000e03e10800c100c0d00030313070410005196280700440e2212442c0b401440b101d80240100d070465030842c6100321000c1140960581d00724603000c052415812002d40b03a5004020295141c9a410b00c040b0f820500e14600c03001581400c242d07407280c850700078100192440050241c040030f101c04428038014000902441eaa11900308082c00011000c0c030704001000711001410700014482e0555118100b5505a00c034406000c0f0f5100d190000b942510801d803c40300b18424442c0f09000600c106042c80c4c080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 535958866 1250 535957616 535957621
    0x6111006080a03091403071503090f150513080909060f060d050103120f14090625231e030d0c201501180b0a082104150c050a05070e 58
    0x308121600c1c0c1c01040e800711aa10000610307107020501c0c006231180740c4890610030303014140840040c1980c034000703411203905c02c0d00c0e54204983d00e4188511034851a8040c40703e6100c609030400e02e4001c40c82e00905803a0104800d448600b0308565036644100c7c0208812160400c04011420547c4181c0c0c03100c03807844c0e550740144100141c0000c098070380c607c0383c80c1c84918884601d00c060003101003084410711031500407a02d40130a40d944001c80355a0100072240c107440340d50041d0f0a42018030510000c80f0b40b000a0301114007040d450040d4141001e0542c4001c0c441102c0c2e8900503c5880724100d10b01083d8041000081c8882110313000c1d50034401d03001d9079020201c1038000b80c6112088800b05c21700d40c0640001c54104c1d02031861030300300c038151b60240760941d045240c1038030f11200420a4100003500141c079500002851080881c0450240c0000398855070b803080070a40c1120f0700d2082c0d000d4140381840354100c1d103000701d11802c84c84031828071400458140400c0c2c0e89429107002c5440d4000488007581904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 535960116 1250 535958866 535958873
    0xa0e090f0d020c13020f04050a0f060f0206040309050d050a0803070906021504080f0c0304050a1401170c0d0f0b0a08060106090b07050c0f012105060a14060406111006080a 75
    0x1d0071103840403030310240c040c1d195890001198069040100c14031940c010610507440400d6400b25401018000d0200d60070703554840101142809900c03e202c0821050141c0090090021480910032945070b40c42c00649400c01080159000032600e059a66118186807580003804850085010703240a84400700c603240341c00c0d8024680b040d11200901005001414000007801d54004d481030317901d22540c2e154458060f07040d80c520314040c03a403090780d000101190000d1600d41c062044a005036003030340c0f0120754520b882589c402c49a030540e56070705104130803c050040440c560b4010048481c0080c4003056105203100000c20070b440d2608490415049a0010044241c01c920410010080001294100f00d810303100d8640710000540c0c060300a00803d07141095030b030702c5000170440700802c0500f0000c0c0030313038141d030031800400d03080311032501424600300c0100d60b070b00311074450b007903044001441d0700c0c601400c00004840440f1000c06164483c825142081020ba110b030007014068440040113201d085e600d0704 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 535961366 1250 535960116 535960123
    0xc210d110415050702190b0304060b06030613050a06120614091906110d0509010501060809070e06060a09050603010311040c0504081509100e0105010f0b0301050102030301060e0a0e090f 81
    0x1000316038a0542008100a20495031100b0b180654540c1082500c0f00310a001091040741c40d180b0421540c29110000300d48003114402440c05180125002c010b4060240d0501840740700503902c007584201c21904041c00d448050b040359500440300b002c003150640e5121001103030343c4a16a03040b81e0498440e1720700d000b0a50130b90310059114034014000d0240c1d5450700200c02c00058051006090513032110403081d826030501045070032202c4209000c00252520b0a10710b4001d18080c01002c0004502e00c000c41c1e0006400035a520548a441c0c12841c001d40b100020044694032103800320041c02025600080c4598500c00a5402035001d21030b0408a07001c50300c1000308607101d040d11700e42848800c2c401401001c000103030302c02040000c0303c1006c0351520758110051600d9040c4041071109403c1410a0043c00c030b041d001141204c1440c400d2400c40358654000c80c195000902031140181d02c18030040003260b2140340400503e00000d015880e0b05502c900c00e902c00c00100321200b41680e03111035002c000d551000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 535962616 1250 535961366 535961381
    0x16110d060f050a0b0d0b060a0b03040501090203060c040f060e0d021c050c0616020904020d0605011d0a0204140108040303062301110c0a0b09040b0306090a05060a051603020c210d 78
    0x1c01040113503004000070702d00041c4918090400c44551000428640f200500c4001501c00010300c03503200d160503e030040c00f0342100e660490283c020500400c070380c002e4050684080d00c6940d10209040760905408a6401d07803940c00315030388940f5056000001d611071052a002d03103408860b80000f050403134144203143c90220403440740200c07420802c00d46641d550b006801d1010b54103c40c03188190700d440c000980d01035040e03400a40030700d04e0200005107141543c02880800c20740252444581c0d03880c82180c03c100d001c0c030b201c2c0c0044008234040045441d13100d0154142c0c00b0307201c1c1c1030015400e03032192200486090100307100e003625400000e000784a5078024000c00b500d081041e0091010b0300d90310b00840c401e0a914860910940300120702d4081a0341c444c1c00107107400001a045998030710b0000c580c0c03642c40343c541c0b1050fa034030b001d20404103007602c1244c001c50744181411940c800264105510440007540038104644036405203001036040300c0c3c0ea14144681a600d00c050681c0c940b100d0316a50012680b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 535963866 1250 535962616 535962631
    0x190308030108061321170a020307090506030c19090806040308061f02121308011e050903210c07150501050a0b1804020c01060f09020c010b010903020616110d060f05 72
    0x41d000510f002400f00685580d2800302c44d61040482e10120406a4400090204414004502d61b04118100850341e0155100b0700c4e1955500c0c0e840c5550340140052840103031103021511204004212584a28103580040703142d0302c0c0341909015a803002000d08004050b1411030001d9141c4041c85200e02d00151210100907460702e00a403c1c4040e0a0f011355201100c0a42480c410000b081d1001800e0140c1d0b400c90084c51800002c0c40081180e086488a00000c1d41035180704a2910000c0384070000b000055404060f1030003003030362801940e0042c002d8480c000a058001c6901d0401c00070000070b4004442c100015910180841d01d5414901001590b041d16044007040d041305105005541c2103111400186c80000e0307500603038880d07a40f0306090241c1a644c00440e00107603203d1713000403608500e40c000c04c0080c82101c0200f01c1840f0010044808240c1480007075440b0200b8000241c59068200212046038070030420110b46026007004a045942449020349841380c0c4c0e50408860b03072910303004140c0d01604 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 535965116 1250 535963866 535963891
    0x1090507051c030e04150906080105181506130e152401030f091a04060b03012d0f0507020304080721030c08041d06040b010801030201051819030803010806 68
    0x182c2c0c00442408009034028003049104043c8115076195035000086880c80050041485501d801c1c0c41c03009004035203e003245542c45c2038005140440d03c000700c00ca6815071200901416140071020005d03402c4080c01c9560320124001d00c4a19904280c45800c80c2e485404000d400c084003040b001302d5400300020898001080e00500281581580c078411441191003400d0009030441c4842d03400000380040304d0010328040b0703001c041d8600f07400c69081980c89244900411f001c1000260185070a0750503c1a4445d00d00e00d842e40c200c1c0404010340195007807072880c11b0000406052a00900056030070503502c450158000280c2800401f0081c0182805008400940283c00703490348020900b600c0b0200c1c01408101400081c0b0f0104645481120f004010061031418603410841341001c0001040e54464030480c644040f20a865008a000e241240e030161074480c140b0440f491000980b1214248541c2c4c0140080c02881424049504910196006020490304c960410f1505031a140700a443c0150f001d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 535966366 1250 535965116 535965139
    0x21315020a0302030901110f03070501021902030408060a050c13030c150203090a031b0b0a031506030b0a03020103022d0304021009080d140d020d0902010318170c1e0109050705 77
    0xf6000411100c480c102843c040344081d112201840c201100e8074640c3e8450f0100007501e605100054003d8903219580e020504d401d2054024140d0782c074807661180024581009000524241c019804183c2c0300c4900c0c4000c40c5081c0c00c08002d05420350b00782e0821074001c002004140850881c14400032001c02490009500d000e20309800244040f00d244402130822902d201c00003401e40810b0010f0b4001e110307102841d40c0300e40c00c40780c000d00074000d4100c101c60541c46000002403000c0c07013801502030450015050160721411600110040c3d840101c58000d928a120042c0030744c407005191a80c00c00b1041000d49880741024810071841045115a810030025119800c4c0142040807514070103416035820f200d140c0f8101c0001e046010301039009035074952031010410070309065058100e403110f24800d0b41c08000010b0440c002507041d1030280405403c50320703040c15105517000700707000600054400004460003207900c40050107180c0d000d2142c40340965120b4209c0030420000304000405850101c540e0309801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 535967616 1250 535966366 535966373
    0x200d08030f090a080a0f12050c342402030c04151806020a0510050907170102040306051906060e130203130b240405061c030210021315020a 61
    0x502000d08808841d800d52400301da04034004103e03145a6a0380101c1d69515458001c901074504a03840001b503011806085115840c070485104440c8070304212071901c1e050100304041ca0b401842042d00705180b0098007500c1500c441c004034010104944503080a0506174000710790705001c44c0403403900d000b141c0d00500c148503103c030861058a06450320b10881c8016180d548030b0844290440c61142201d4006803a000b203040e0303601144009403036006008440440c60131560003002c4480447d100c203043d4000d01024061200420028034035102e91400250078030307849803105001c440c4255000075200d0608071004640d200c1602982c001090907003044040307050101d02044c1c0110402000e101c860782e0001c0000c8256404986035100c5c03a4000300480c0c0305182c401a401a07000d23500250214030380744d000081c87e803450680690751191801070406081109020450242100c0343c000490079070080440e8180340b0022440501386504c0c900e0f0920344010718084180341d5200d24078a42c2e008542040881c04040b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 535968866 1250 535967616 535967633
    0x91b0d03020c0d110a3308070c0206071502040510020303070e01111f0b030c09060d0609080d0e030a0809191202100e0102040e091c030203060409020d200d 68
    0x1c1054420f00404040c0e840d007000598442440c09034010115400070810b00001d00c0c1c004582104904140d500d900030481e5907485002c0c10300400005400940094030703480c4a4a5000d0740c69201400803801c00619030758407940b04416031061b440007680450704100794035209074590105600c40c00a14554100140010304840b011860305042c000d100066550429040150b440d040429807511002000c102c0c0c9410007078078086c0100751003442048aa20114600344031141d0080d2002030413201160416924103000c0c0000440c181c807110020300c010302e0910704034003c199800038041c019541c0e800c06036a001c0c240d800049c01c1c650f05907201a451041d0354002c00c0c094400d284e0060501c2e1022424505d0072803404207901c07a44003543d42018441101d00005402500550b180112120740750b9503060303503141e0350f00001d011200081c622207019a00d2140640d00840d000f0902410109062500d600800c211095142084070042d215580d904002281d00b54405400b46c41110811541036041c2c03100c044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 535970116 1250 535968866 535968883
    0xc03070c08011b0c0b160507080a080103060e070e041b050306090706091d04110301020928080c030d0810120f0309080d0905010e0a050d08030a0b030102130312020c0405091b0d0302 79
    0x6c0f2810fa541014405a0060090310841940012000e551b00c0f01c40c80700900300c51080c84100c2e091400c2c00c400d08062400070903074100342e48150ba018075940c0c4e101d482c0c00c014550428440040f80402c07003c0440e00da2424400341e0b1280301c7d41c500800490f45003a600414044465201c00325040c58240c02c640400c0441a00c19085904198036524031105080028024802d2800283e4070600b143c0300701500c20300b44074500300210140b105501115a581d54141d0b12112003030002549500021180c25040340144070b03031508003681a400140d55500c9407106054524500c006036400cad440881c00b07d0815901011010240281c1c0000d000c907001414006070910482d801441e040c00043e48145046da12060102d60090400410030b04207007441c1c1c01e1440f07042e0b109680352540079003844401540780c1014003c40304090307400c060810301c2600c0c0d41c5a00782c412030610740711811801200c080c6911030741d403406058001c01c1541e000c0c0904010a03095540e1051100c07940038011143c0940c42008607030003003600c29 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 535971223 1107 535970116 535970131
    0x3050d1d0f120a0e01200123090a030e01120b03121902010c1b020103020c0f030c0114160302160602040b04060801120b0c0c03070c08011b0c0b 63
    0x41510b2080d4100744004c134880c0c0c03600c80c103e94441d80529040482882003400060040d001841c251007014024aa6800703114031001040b40846011075008003400004004103003240c0d90180402d0402c0700c2c124180704508020003030150f0380780c04c210000a00181602c4940040250b03da1450f0040011594107020003a040a00640140320723840b5549000d80b81c40300b43d074250510100c038400c034580d41241099001d00101d49000f10402c0350383e1460b101e034406140c41c0c2e012460320340d0840350307061010451104200d050040c28000c00b50105280302440c0350150b41d85c5030b41181100c581c94180001030401d071000500190744110390018000381d81d0707299034103043c590340d40024503403250100340050702c10709021010510584404000b0b04640b81648256030400c2c4003070f1200ca81071083c981c0000d905035110340720b04401d000031001000c08221709081c0414015055250003681c08402040c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 535791366 535971223 := by
  have h0 := BRFrame.cov_init 535791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 535791366 ≤ n) (h2 : n < 535971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
