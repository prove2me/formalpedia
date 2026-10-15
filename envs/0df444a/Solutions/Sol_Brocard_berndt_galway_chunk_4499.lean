-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4499
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:49:14.13135+00:00
-- url     : https://prove2.me/submissions/660396b4-89c1-47d2-9406-4e0427b48238

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 808992805 ≤ n < 809172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 808994055 1250 808992805 808992817
    0x180603060609041508062703090a03030e0117011814101a0405030a20010302070b011203050909010806010806070e03061503031e0d06060c0503160c030606080f01050703060b 76
    0x341c0d020588401c404c40041d000d803200d8200d0fa045000c2e0781c00f000908252441c1015040130400c2d1030103002c2c80c0202d5169100d02c03a1101554025001d40350500200c1d0080e60703081c00c08a0103241a410850b03080c2041141e180c42078014603e800c04440c0341031428041070041c4440801402c0490401c2e0404049a41080030180b1900700c00c8114581410b42900034202910000e10000c1e06a91300c00180f40307020501040c03030501200343c02d24422031078003403540b09100340c610050384094484020b90901c0d118000b41582d80c041101006010080c2d140151940c112042c02402418028410395042a01882c01c0038070040842d0b04010091400c3c0300f407036500080341c80d0019583d003000030b001400d1001207421031050310030104034031481607801c0191001d40401888040324010040080b19100c40b02180c182e908000c3c0604942c2c0184482102a1072400c1204052807081c44040c0a07550350399121304c00c0d5a0785034130200d106d810030007202c000c5032028000c00f54031001525042112a04000110070f450040e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 808995305 1250 808994055 808994059
    0x61401080f0f040201051905030901050c090a260307030906031113060e2d010206090102040b250b0c0720060a1407050601030f03090e07050a050706020702040f02180603060609 77
    0x2c0c010409690103401190500406514414680000703048090156030065070341009039840c100024403503000220546665840003441e0707045552a01c50140041803070001000c030185010040040744e444200002e103201d078803d80303903603844900e800000350480c0c5445d802e8a4501c201000400041c402540010f4107960181c02c00f140700e03140c540045030038074222620400341011400340740d02030120111429840c0b144240c0c01ca541e1562400e0700b003801e0f400b4511411100003014003182d0120101c5d501c1680103003a40d1f6840d5048102944c032080c85402c2c0c00c8c4c038480d40600300000c0c070f0400c0c480700c581801c662000340d00071081200360104c0491181d110300a00a0200f0ad6070940441c0c00104200032141c4d42070f002000c840440d41c490404140078045100110301041340d22600103a0040d0f21001e1038800c00705504c8031400d01406142c184c949a020b16800c48859600300300c09001651035100d20b0036001d102d100c0c010b031220180174500c0400c0d68200300c200c3c0304031028801c0043c55036580049034000181 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 808996555 1250 808995305 808995331
    0x303060102212b0c020316060c0c0f1b0501030e06011415071104050f100e0408071b03020f03010911040f020c0a110901090e0d03050711030d061401080f 67
    0x60360446070b900880d010052106180c00c003440d401d4089030141001d880d10480100b045252804059030b592081510040d030042d034050302c001c041100f070780c040b070202d0005061070202441c0d6030340c40d418007019412040703560310801500f0300f00034584200054060308003820304100311400c401d08295688414441d0748008038034818002a151102818001001034101409442c4c401611f00302010b0380d40310b40306901079464140010b14544018801a014240c01101500c507182042d01101d8210b400510030380707106808004038800506403000d4840f5160005014200c0d01d4150310400c1045031050041603c2681461401c1c0041201801844205501102c0000d540145a91408041d005146000c031907401400345101c00d001907841c88a0200e02c040320946016030322103284804860303038030031039408a6010390181201c0a019520842c0c105030303d400d02d40340c00c0d003220302c0e00340c80c1d40c1c002e4205840440d00d68404100d6840000303403412000e5000d00b40201e10340b07030880f00074102c808000d11511030006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 808997805 1250 808996555 808996603
    0x1514060d0e030d060b04030b0a1107030809030910020d1101230a0f060b0d0b04050f0f060117130302070b0a1b080415080f0f011a0a110f0d0f020303060102 68
    0x1e810401c8480249190000340a1103548842040c0725800a01c03040d200200103e00080d4102c02500c40d030201326410200c042d04052080e00c0442e01000c00501081c01480200001d18103039507250516001601c8a0b401403140d1400084014043c002c0b0100e0040d15a0421a013012004405202d0700700043c4110000d000640d1151201e001901d00c0d9204611101e207000e41c0487c45214490003051400d40c030303201c18045454200709110884c0e13000c441d003c4000c00088041070046a200904a81001c01450010046120305407111240c01c0d09813041c030101d03900c4090041c10940c060215170300524244440386e040500d02c04010b01001070204ca9650a48014100c000410040d0f40944c1c3c06040e0441c00d02102564031407014090040c11381d0200f000a40b80400650143c2120f4110760580310348840741c00c4141490550505d09800c0200002c0030300c00b045a0301d503003a12007004ac00d4803040040c0e0003006d2242402101900c0008159880811500100304011050741c000840c2c9041060704141a01548 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 808999055 1250 808997805 808997831
    0x10e030109033c0527010f030507030905060a0b15161101020a060219030e2a2101050610090b03010b2b060e010b040e010506160f05011514060d 63
    0x3070022010000f40c01515010100616031020180c41c1e10b8541c0040d44030004466400400000c103010344150000384400c00b01e2256601c02d40045401408034100411071403041c2d80d407107040c03c02c11a8414000d40e580d01203d001882c081c4403004019024501c1249400518125165040032101005e4040c40c00c00703621f011039900c00c028180001d40c000c4400c54407203203c0d841681007a0703111007440d00080e09205071031142d07072408110418503040741c03c142065041c980740154034000b0310300307180f0340d0001000c50104440700c0d60400356900c030a59000002510b2031700c00e082200c6103020742c40034801c1040541041c050310156034100d81c10340c1c84aa492903103404602038036154242c0c0507003441e1040e1002c0b81000c03462003030b150048000d03034018060004131680c940381202414000c030321401031040b40c003500410050074150000d145282c89007946910001054540c4110114480000c55450303549604200300310040c0b0103070710050260f00e02c81480786808600003c0d400c0c0203440d40700e001181d0ba5040c1d18150 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 809000305 1250 808999055 808999127
    0x30c071406010806040c0e010608190608030f030a050a090209130c151101241202130903120f0219110705100c03020708011503031407170306010e03010903 68
    0x180c244604480c80c81da1a100c406032210340544045418411010010410121000c2918103036001c9695401080d6212007846c01840303c1d035070f4650a16503480724080341c2d03e80f081c8018000d0941032499180c0d02c2c1020b049940c11030f20005c04c0b00c84c1311071401c0700080059440744c003000d420442e185820312200441e030030110f041558540c0680194080340e1005486290002c0500d1144001c030002017001e141044050001401d86c00c100b100c1140000d81c003842514120450580101d00241407500080d08502200c81107a0409006034082110052105c000100902891400d1034007008150305000c90340110106c010319400c5030009000110f01c00d0035003010204504170040000030101c1402101a0b00081d00410450a007503005004601c030224241905008003621200981a51440541346440c01c03103442040d800c04d9a90410100131050205185221044411a121000c10360f241040000900b000c5443c04000c3c0c000d9040c803400b903010a0b0000d05041004801d40d403c020f15080d0041c02480c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 809001555 1250 809000305 809000333
    0x2030a0b07170a05040510092a08011103190b090a02070503070606150327140f060736140a030203061003020102010b032b0e030f0a06150308030c07 65
    0x1040070103000300030401c0f00d203800c40c82c021800740003601ca4600801e50f01c80d0544020100c058071400260520803001d02943d2480c3c90404031801040d40c2154a9070181703401e480255500c02c071101004401d02105041708600701090f83c40c5403100704085000480810030181c0c000303224109080e80071a44074140030040c170032101c03095400041088415200c40b80c142413400e0960355000000e107480c181946c0c2803042c043d87d4880005028906060345010341c1c0f848247c40c00210b1203a0760b4011600c9150700140300304019405501d10b0f41720707849190841c1d0380c80446c41d03084071981c20b10002d8000981368002503901c5148140c4004020103c41c404040c0049000c01c501e50b40000e4051103600100500b80c00b480b081c1d201500d1007603000340b01c4940420201036903aa00c9203001694074004029108540388924045c0040081505044400285520010381802e550b40301c100000d4000304e8085041000d24420505080100144025040d045495900482c0801403c40d40c944400280050a0024219501c82 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 809002805 1250 809001555 809001587
    0x3070c0905041110030507030e010b011205060102071d09011a130b062502040509070e070513050a030305030f060102120405041104090e1c02010c0e01030b0d0210031a0d02030a0b07 79
    0x50700c4c04004010001d01c012504400040d1401c0c0d00202d488406000b03c1071309010580d100d0101c940c1001c8114000c00020707041d2819481224800036481812000310140740c1102d5825a21a15060741118203480000e8044100d002e0440041c80440daa906680c00c007540c4ca0035400581b102040001c910544650450640007013005c814203a13280d1250801514010f1090f9002d200d20b455032940f0b02d80e42c80e500c1c06034120345481e80c40003d9001d4030402c00780c41250032801e06069803580e907601098500080390420b4000070000001c001136540342c034041d20b401400c01e10041840c801120010784181c043c0703000b503522940d140c403283c07441002d0303100030b8501170801c0c06c00402900400030031007a40c038801c100c01003a10600803900045194018130411800c16115141e20101040c46001140203100300e0b4440e40e03200103440208405a01d4000c040f02207401591800108008244510007022602c8440644141c2c0c0802c0d0480041e203020500c0344c01e190303028042da0342c01d48034608117880c05654913800003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 809004055 1250 809002805 809002819
    0x50708061302010201060b040303171911071e0503041e09060f06080f070801150507050d0908012d020c1e010204090b060324040b1206100803070c09050411 68
    0x862161201c14140c200c641c401d8008010a0ba62a24041d0f590f014500c00500420030800300d2071404260480002d500034a005400c03d40c80c41d035032107600c049440b039503045140c6420103d680c1007000050744001c1c1c0c0588180d24040c2c8580c01a54070aa9a4070441c056195001200740c0261208a102905440030301541c25007480007036240c0700c1c00c0c1c1170100719100e52070000e0750071000308400c4028414420f026118a03620564260309140c8034104040030045281e0805c0010081c00780031580a100244a40040b99103c6000d6464030311010301303442116116a00501f41c01140c448014000400d1400c030301d06500b40035031039000e82c0c6c1000d402d01c107800d2500e801d03c403c6106580e201d03100650091050b103005030b401700101c018036028804240011280e0341c1c400e4140d402000c03200350690b40d4440e80710700b0052000c0b82c46200e18000c04d1060040c46950840c0c0e912440a0042c3c80b407940310f40c200580b092500a600b0b042c2184c03107011215109108200c13200765038401060500100408090b582007029081c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 809005305 1250 809004055 809004061
    0xb0a180605010b0c061006020a03144006020c0f030c0a080601080d05030103030f140d06240f1b050c040509030a0206010605090a0e0a0204050406030302070612141305070806 76
    0xc050310391310091501d0a035003d640005440840342500f8541039a003158001c20300b5010381e640540c0c014039080c0142c00001c0041c0b0442c82040103014800110b846800c0020712120b11039807101c0300f80401000750040d000c00b04582484000c3d4009100c0c44070610444d0342c4005168824040303420410350b4110b8a1b00950305030000704d0800c100040c801d04031156071044410420344030b5000c403030600080c0070003000100c804510001042c81001c803460641d0000c9046480c248201c42e4444c02c50f0b02560041c41d580140c0c0100d80611880c002c00c11801a505060610100b80d9030a00103108810040d968000800c0340141441404410030120b03080e020058001c100074140102d181c3d40d284c001c44804030062095500202d0020710a20a13220400c1000c0c0035110388509042c030b48140d0303a000820300d00c0b413241d00380400a0503603a540911002107010741c001e07000340d60a02c58000e0140401940d07103004242049104802c107902d0a058135800150b01040340b20312280b510b00f40b070030030384103074040741c0307140f04007028 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 809006555 1250 809005305 809005319
    0x150a06031e030809121b0c0418020306090105010501091a040506070b16022e0b030a08310905040f0f0b01140405010305120c070f06051e070b0a18060501 67
    0x40844058040d0f29006020354130007207410764a1440d0162020701a809100038110036001d0441c5420441400c000d4408003102c25001c80d0403110f048a100400c199108021815030030144001500091010024019036040c200007800800d00341c03190b0301c0e92602802c1107070303600b100d0001620040c4c07500404465544409040031034003080251040c418084580e160645003c1c000600725001a80d1314101107100100c4180e081c00e901d925026404000d6251000c100f01070394148001c1345100d2099145940f1104060447c03002000c08402c81010450340c08001d01e0b68400d080e440c1011100c0308900030945650383e2a0044a5141055000341103103071070070483c420806503402d6203060310b082c0b00141c0b071070140400c02c0000340d034020310000c1c0c5a1307003180150810740b144e001c005001c02403840084501803551110180000138165102c2c10000b80b001c1105600301200d0100e0b1035030050009030060420380c06803149144244058403041344141d442880a00000c2014070030701c5201d8000c03d0400081d0b81d1410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 809007805 1250 809006555 809006603
    0x6031303050412110f01030911090a06050d08031f1202040203071407061b0512041103210301090b040c020606130b030d08040b0601030219081b16020a17150a0603 71
    0x1d0342c1701e0721103181c2503480c0394801d110742c0d040f0300d822015040030929003c3c01e10210490203400080b5040d22020003066544401d0364a0280d42c0c8108201983c1c6d1a0a4000e00d01041304903000139405128031204000301c030b03d640e480c2901d0b50380480f00141d0b079441d07102c0e05843e5107004141d400028100414018107004041c7d1110020a1501107080d05041030300d4403c880314840ca003412008100680d011401207441112031050142d8041d04071551198102152103e00400d10364082c042c4400100610203020107004688040a05403010b010b030b0032a411020351542c0008000714041c1045446002180341c1541140c9031150340982580c54915903104010240c41c0c0c1140c00342c954400e0b800100c0c0d0b41d54440d200b01c0c0c1c24034441b04242d0050300d440c601c0071944950040c0400e58a072040d680b41c0130b100b450860007407482d4440003206402030b668610500400b000307541c3c00039a0004448500c920f50300300c0803c0c0141c0e81100300010f40f6071940e40c0f400900003020340d0b82000c0d1540c2403805101004400d524 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 809009055 1250 809007805 809007833
    0x6041b0906032006031b03040203010207081c0b0d0c0605030a0f0c030c021504170f0d021b1501030c05060a1808031324050c0a0b040305030703110906031303050412 72
    0x410350f440307100f10410a1150300d02c000c2d15401d00c14003135a0190b42e081c1c007840b805503400070700c0140007610b04101c0741c0740c0c41b4141d0002d90328010b9000700510075001142640c0b00d40e03001c43e001540c1c2d0012181080d05c800804c0c81080c803514091000000c00a480110140e02405140f01d40e0a070400613004400740060050001c00b4456000d44103256800d0a1010811206407003181e001850760000c201c0310490000d1500038205d240540c0c403042c02808150f0507680041e01c410300d5040a40707000b0f42842a2254600707180403001505c40b040c0300e070060012583c0c070005070b02550000e4602d9542e902c042042100c51032400881580e50b007084040100341e50030040010228102c800e208040955144e190604038515002145010306d0180501c1e9010540540081c2c0200034500b82130300e00041e09900c07041644401120300300d001810010400c414550184203100309220802e19003410510200046806484040c1c0010301c00d000214550082510500848016101003014050170f1105880c1c0100148048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 809010305 1250 809009055 809009093
    0x30b01110a080c0c1c03030c140301120b0f06090f0c1e0d0c0f0c031d0301020a0c031805010e13020f0409020c10090f151b08040b100806041b090603 65
    0x255600008a00d44205d224260006007018410500140d41c0c00390014400440400140840c411030000b402c0740903400b95009103110300300c4a110501c50b02e070044811100a2030000212114402d0054130f0726020400d07540094084405191a180d4140d0381409001d0042d030b802c9655103450040b40501c003000050801030201801c1171145400800b810744140074405d0340c20000030000c040c2440802c1c89006001c1e0340c0d4404150060002c00d0400c0440e013a80e12000d640c0e4045000410a6010141d00c21507101c2540001c03d00e0f2503895080034002030071041ca00007040d1141140800080141d95540d0484107140380c13110010741d5440c0e5552080006e90445c090250490007185522015400c96004504070315601002d1103000c0e403c25552040d1450307045040702d55255480c4440900e038001c44a01d40c14500040d2034295042c40c2c00e1500442c0c844004048900d0421040303400c206030040018081d0300107500154814010429103818030001c40944c7c0021045401c0440001c10b04c10076142c0081500c0c51 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 809011555 1250 809010305 809010313
    0x30308191e0e1902090411061e03100e0c0f0c030d02070b041502070803160207170c0901090c2109051207051b031f0e0109080405031b060a030b01110a080c 68
    0x43c4480c0c1000d804410107500b00e040c490000d40090011a001411140014140f50811f152a04850400d000d03e403a1095146400404c6c425049084008031000300542041260799180040b10058a0700488190f41c08654010514400041003402903035050b45032250215110481401c102c4031502c0b050f1002c0d1056102120000700c0e4007514001c40310020303001380599140d1344a851000380d1041d0002d041000318054079901003102c04000811440c0000c1300740040ca1046d00f002d041140e056010b902054a003460040d5540034140c019140030141031044e10103505501c00246120040c12520310014a03502031007001d1100106408003030a5024020b90488106141380c2d41203500313030b4512065050b816401725607400e11242c01e054401c4540416040040740d2030285e140380b107080d00c2d09541d08a8a840c00407605010a040401c8420b60146520b07035000400701200004c00d80521035001c409041544814881d0940e0b40210310266001003844200d070340303201c0182003d1603241c202410038070b10b50203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 809012805 1250 809011555 809011573
    0x40e0312180309010806012105150102011e02090a030b090604033e010917181005090d021c060504020a060c030806060d1d1c09030308191e0e 62
    0x714041000030303480844021450900d1100040d03503a200000e0005041000c0e5000075003550355179141040680c58007400128460a04524071800b80c0d0181c1c07091411a072512000700d0010b80d941c9651b042288403080c006035148a0f40d0b0200c0c07803034101038101130402040907090114105c0001130892150340265546420048000300002102d4105c0a408010f01c00c82c00b034001e8800e1128070600c035580041c01c0001042c00d540d03558074940840300045600b00641c007186020789558405c15080041034229400304074591885c034003030110302a0301580760180140d03491250864441400f202c4614481d5030b11401614441c0c54541c0103071804840890081c00714003000600907000307031801c949060740b5865044581e0350301c0c1e09000380754100c0051224039940700c5540240c4819000301944c0120790720030103029400030520b0160f290410802c5284200440403004102280d0700c402820342201c6200068410b03c50341e0400040034266030241c5450641043e80013a43c100e2403680903a170121450700580d00d20704 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 809014055 1250 809012805 809012821
    0x12030712030509060403032403140606011e030f090f0f0620090d0c0f17060c0310090f0e0106090b180919170310031a010b1b030702040e0312 62
    0x151090b0f510b40c6050703100340e010034000ba010f504414810040c0625185500800100c1075160f10381a0744265802031390a483daa0707003070105105c40d6600010a00f000c3c0c12401c940031603507800d400081045c0040503900d242d640707000800c42d000039600c290010440340b5108280d040c500c0004e040748070101c900350b00e40246050a66804c541e8141542c14070030313103c0e0070180d007a01403081500c4816000c980baa48a01070104134000c155000078003500c521200b145100c807800c04214a0b102c0050401a0320100610401c006465501b21180a0324800380010400b520040c0c1c0d900003030302c111111a42a035080410100e04100c2942c083d1144020848000d02d9031500c2490700300b600942a00e000026070049800c146648600d614644801c610950204111074210f00e01c9101a800660703030003940320400602003082c0640c0350601d0001441c0303c070006c2c6441d40b5200707080c0304602c26007048038071729802210300b042400420f005403217400d500a0b02c140100d101c080c1c0f0540e125440034220600d002c4101c40400d42c18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 809015305 1250 809014055 809014061
    0x18100c0f0315080712030e030706020c031204081207240b100513050120030c0604120815090c0d021602010f090f05150921060105011403241203071203 66
    0x540c9000d0151185074106900f00e04020345c013900c00d4043c040380c0140c5020b95107040110b0002012035a01615000000c10201804c00b4a00361144851f00004c1c0824088a6000304048000c3d221034043c585e49d0f08024a085100700140d1301840b08001d403042001c0c11940050703000004070820484080241007a0404207480a0003401c1d41c0c1071890814010070300440d4040c031640c5045c04001e00c00840140c250407401c0b0b2840d80b054030a040c844d045070042c0010442d100b000b0f0031485200d81044446031522204406c034039401540040d101e82003030000300d081c01c400d03c3c00f01c030884100c203001076507a1601d83c5280c600442003070504030b000900703814a00c07400e02c2c4503007412000d5034141225118114605420401c641041003d0b100c41e0600411140b440743d03450f003541c0c02c203021001d80100b0803160304081c814201101688054144060718401c400c600c403600049990100001c00c111766224280f242c10550010340300c040a400050b5134400c8641e000000014006003031140e0040780100f43e00c103a089040e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 809016555 1250 809015305 809015309
    0x206090a230703080f0711090c12150406141e06030103060e10021b01050703020c0c060d061d011403120d0c03090606170c0d02010818100c0f0315 64
    0x51900100d140c1a10403440c032110310020025002c0340c03050383e12600c45a660350300ca101c1035000071800040920800154490b413103072614040302c141e00c00345032808002040303204008100029400e00400608a1388450882030394000e0041d000308403081d11003d4203000c0000040d5400d216089841e2104007940351034400c010307a90350140c231041c15646103a4a03000540303001020384019000320408865961000e1001c2c0040384203045000700c0c2141008503545c2100c5001d8500c03020540100010241c2042c00106080e0900e0155074039030f40c032404400c0f00c00040616402610214400c01c20b008552039070030714a01d0507160b0107618100c1da1500750b020155101c8072544000050748060004445411242e4003480d0040c4050401240748000da5462a040741d4840d00108a84400c4490345501040100800e100c00f02c0e00303480481c036501d010f400180c28a00024082040c05091245600e0b4041041c00307200394031a0b00d90020301200c00c0c4c0303010161881d1a500c224100180c0391800d900c02d403081140075541 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 809017805 1250 809016555 809016563
    0x4060206130309030b0406140f01061206030c0501050d020c03030702010c20120a0e1003060f05030c0d020f010c0f120e0916080603030c0709020c16240e090411010206090a 75
    0x1000c1c2c4e11310f50b079900d40544000e1055400d6982c80d59500343d10f03603100750001c1c4034801c50b203600340c000d43c10000054001a0147c0040420510380202070001441c0c10001d1004d0340c00c2400d1442d1210104048400a44180f4201810900001c42401000d40d015000140d141c4200d8a03410861402c2d0200600c00d030405048829480d0f0025414041b410503107402800308030ba041c80d195030301d99080e5011681c00c0d600400b900b00025a6000100b250380140541030380a40700480143c401e040c4580c1c0046d00c00464500082c0c403803155407180008580c0980c0c49a040e01d03501080c0c0210a15060a084014800500d00d0401250440030b040d40d040c40e100b48041e2080c0d403070f01980366550440041c121410000100f1b490341601c0100020088a2010403400c4000d110400c001351f6101100d00c5044e061080348071100005031035403c4184400c0c0903088105c48038120280d2114801030b840302085446131100b002c4140c000c6004401e10003400307810180e120a501080c2c003150800e03200c0c6a017182c0e40b254240d1000d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 809019055 1250 809017805 809017817
    0x305012c0d0e060d050708240607110a08070603020306090a050103031d041e150609050a0e040c0302120a050c06032406040302031c080105010e0a060e1212040602061303 74
    0x5280c00d0080c05650341c540c0b80030340041d0410040307840c0c1600315030059540740e01244900b010088a0350361124002100d0030826500340c14034501002003102d42c0989c5400410940d441c0e4401e0640340c5441404a0091007000202d034030349991101c0140c001d62007929464052052600003804441090107024126079050361006100460300c00d00645074030680380c50704c1e4002d4075410039481d024017039141c02c0f281c04200d58000501150240011041110342e0340000d091200d03c031402c001658032904c1950440c0e80701c549800c6155541d03c5c00c241140181d4100940c03201040f100416071322030015a4220041c8690101e69103070080d1020043c09010450f180c80c512801d000c1d4881048003000749181c800100900030358201902c99000905081c3c5850f4040e100307483d00f409010405034850101c5004010a091010014603940081010f06141d4001e0a047c0706405010481d10344942202c0c1c0c520310b85a038161380c2e00348415459018194040c1c82004014403079030012540e49501e091280700c5007585070703c0b25 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 809020305 1250 809019055 809019073
    0x1030204022b0e0106090b061210091a040c03060b041a0403140606010822060b1903060605030d051c0e030f031003021008091005090703020a0305012c 66
    0x70b0b501001008405124101c08190b250350751a62026081d0640a40898442110400c00342141c00c00d5100895160034010580990b0f29403c1c06c90318414a14201920725554108500140c1e4102d540050092440c18468240101c43c01d02c4407802c10004a4060084040703048045007a60b015008440001c4e000300810401a19080d555040c0c1031080d0b600582000d50700e4941c001c0e4ad85080f08540510b401450800161390381c491030b41540006a0580300c030b640c1081d6050100d02201c0d801d002046240c0d038174103500540d80c1c2d0800b0449104042070308240803d4480c9003150147c010780c031034140203116081c90300144601420554071b07000b10788208141881c40c2a5201c1c0050580d1801601c500e000070803840d9000c0402200652140214008184040e841d43c410b202e81112200c040008000c0c4103001c0c8002441d0205800783c01d81d904020100741d50702d8094181d810519170b0b5000070344c8903902e80800010040c06404c0f100c4010b48007407440340041e5400c0300c601b40c1e8424508180045802503080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 809021555 1250 809020305 809020309
    0xb030606060c150118112506140a1e2a050f030103062012042010030b10110319090504060e090f0712080d020d050705030106031103040b010302 63
    0x80c06551002c1000c482d1000304140621034040c10030303000000da41202c80010100039503240030b15414200743c107100e00c0c50314604188550380302d090074090811481c2031002c550144906030300300054509803503801c01031134242180b10030001c1203014865550417450f02c0101007036145512030b8088880c00140300780002c04904010001c1c086c0c52468000a001e818072600031200b01201c0510b002c3e500c100c0e0700252100d603a01801c801c2451290a046016404100480440b1103804204e41c00c030741e02410000108081c514041d00c002c8500c54100d401c400d0581c901100a917140d00003060400301a2485c6080c102c140b403045891a100e00b5070a44240e00400040c4011303085084281c0450400d0310340b00ea81c06484100040584185503c81e0340164040f60a001e00c102040c089108544400343c0240320301842c00fa0041c588282060001d041803402060500724049540c045410800031100108002d250211380984540c00c28010040080d1034000381c1851403111800700c3c0c0c01280c02c0040e61510303a01c0c55007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 809022805 1250 809021555 809021557
    0x1502060a1509050406020c06072601030f0b18031c0501080c1f120c030b010e0901050919090b040302061602030a02122a0c0112050103120c0515090313090b03060606 72
    0x100305c50b2241e00b003202c10110304080c00254051a09030755000245050504503501d0528044e80007940280400010400941a00f07116440b1550000e40c401c0d0765560a0f030080201507581c621071203140030004040341c05580f025050036841072104070030000c503601c030f0410700d503201c01d10030811303400c43d60000408003038240803980c1201107001403903c0d102038071400d142c1d8416150070220407004030341c40d46035881c995038006806001c010810744031000690300d88400140c00300405004c050f408050b0b4014040700407459001100010740054080c1940d00301443c00035650401211030100e5140450301c040341c002d1011044503154407042e4000d2200e404240158003076540b046800032600340e6081075180390782d480c103401e8500509824010301040c3c003a060015081840d0451000f8102c0c0c60600180b00040300d0780074410340c41034907243c03648480711740f031518501c3c01441a0a402e1140c8945003084841030b0004000c2984858850100c0111541d50700813000340d030038411303806a05070826000607095042400c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 809024055 1250 809022805 809022811
    0xd0816050322080a0905061303021c06020f0703090e1311010e10090612061d100f12060b0d03020a11061b060603070506070201080106030b04060b041502060a150905 72
    0x40c1d02911035011200511400c1401940202c07a083c801084648140d81c014440000178003007954803034500758452001d124070b01d500d404001e00c0b81d020180004090f0a40c1400552283d600030700c01c55445e40f182d06140c0d010b410202040300001c030a9203000c24041c203030f520341c035016044d025180d5030f0264082e50341040b180a10b00100f4104a403418072102d081c0c2d11039104401201c100d490b8010382c142864001400e40c0400001d0b80364075410158100302c8980d41381030751034140c5000c03071102d1240d444040f04038611500680c45140380724200c6074080b40040d503802c00158214410082000340d80e1910080c4005803020b8000275000d40c10040007030011a821080780748070140003c10091901e03000390003600c6070000310000c01c2001e901040402c00141410030860001c0c0900f00d031b0503030828055600081c50302c1c605000749420162503c3c0c00780481c1d01c564010030060220066000c2d210750300d400031503600340d0899816100504c11000441d280c044a03220b101841d140c10f4a2201a2a00700030300e500c060240a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 809025305 1250 809024055 809024071
    0x50d0f03030b1512090d0c15020417030c070504090804052e090f0b0f0f0c0c09040f21120903020304051801030308010b12010315090506010e090d08160503 68
    0x7280041410742e40d10105804203000c9a110503211501303070f4001c00d01242d000b808901c075944603400700146150001c80c02ca880070350250743c641d00351140301105e90182c040d99000c155005920b1016124240012001c0d14101c41c44008032041c03544e0300c104110640355904000b5207000803c003c24801030600c407407011641404c4003014a00340651180d5100340c9050183c160002844c007603400d201c55200710900c0c81c01000918011410400780e1100030440c2d100301030140c0d100150000c0c0220305060140901c003010384004001d80d55910302403c00f02585244e130203003200d1000070030006400508000414003000d46040e9910030384150240c0fa80402071101700c005500f03602c02480005455611050b81c60342c810040d2400d03801070f514524001d4044401030700038410549040c07188102c10440c50240d241101c0d009100d450460f82160400c60003861303985c0c0050250700883c0004940c0111340c010341400307005403000702e070700070205000e00300c07140b05007910040506036200540c1800144240051504800300d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 809026555 1250 809025305 809025311
    0x240b07032703050f0d021b0d03020f010509010b040605040c09030b060103021c0b0108100e130c080118050c0a030b0420062b06030201020c09040c0f06051b07050d0f0303 74
    0x1c0d0066010324140d5000312210362005401c041d42001c18004c2c5207007004980007c2c4a00400c408003410070310011081d40e4050f440032032840007450f01c204900d100f03101c05040208000c2c01d21025580c043e1a940c80402c1c0100e040400c009100e040c6841443c0a05c0d440f561400300135800c6607140c600100c405062241010b0f000c1c000881044a16092900b1014010301c0025403d500100050250b0302c008240c800304008000e1b003001180e16405e03000750700003400c3c650303c80446001e16111044201540200c0071700d610700101943d4201e04480751106450203881141c03940e03614171041004442c510300000b001c400300e1602040001d01c0c141d404074184030584801070030342111000406d0841d00701c1111149c03544101204581402e075001e941002070514440f00344401410341e00042d583d10440b500e03490061056000240030b100c1c07944006000381074858000fa2450f07985040040c1180c0005002081701c911550300c0410721100000c00d001184c80c050900701e41404d6985610030b80301014401503092540b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 809027805 1250 809026555 809026607
    0x6011103041e06051c091b09050f240423040c1a0a0503010b07020d05010c02101d06010b0f19030615020604022209020d06240b0703 58
    0x8288058000303030900301c82c881c2591a40614048884480da4010018014200b210702c00300c0d80c19610a07505a1016500441c4a41e802d15015005030900c00030741c10000e80009010a0103a640c0d00070074040c01c400401c100702520303000107842a100c00e801c80400e2700301c3c8546100f401428150800030100401d0203501020400401100f1075000303044408864100d045032090008002032020810b0082c810f00025080c00c20203000a03240344010f016801158801252210031556462005c0b038080d98008000d10a60200c81d01c042d6903a081c0c1354250895034144000a421442e0040c031500d881d40c8284000d08581c0d04c0d0940d90b0001d544855601900a00300300822070540b010072051013041030003030381e00081b6145042c040d22030b9a5641d04034071085402c0a002d00001d60303503c01200565040c018899001d0070080d111140060915240080d00030035122510424080785070b11518024080c000c1c41c1925a84010f50588852654011820740c1e4806202c0d00c80031a00c0b40c1404030300404a0710800c51180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 809029055 1250 809027805 809027837
    0xa080403080909180307020d0206091509130506030a030e030a210f0206040f020103150302210c0a080607120e010203040c080c060a091701060b0c060708150105120601 73
    0x160040d0420341c0d8000000502401a040080b843d82d4002c58008041201880b0b1000f040d40b24803400e400a440741211050040955441c0780450b1840034005010303c3d40e00b07265080e481090341103041d00505c10039424102e07442c0341c00c144c02030510441c0010040c0912401c60758040c0e90780c0e281224099058411908a800000d0000c0080395081c1d1b0101a480322030700c515a401051008103a00340030442d0041c3c2d0500001850007100202e0b04c95090030049910060284c425540912030707803000c0e41c41034a03c1140082c10040c64881003191401c0e205032000f0a00c08014000da0180d01d11940d0101e03130101000600b61031144403940b650b040721100c0822290724000c0002c0c00d80c1c0003500d02344c1e10348a40541c1001551010410100c90050a036051400c090f01305a0140555400744140d501c400300c102468999080c0a52003031014005070800a512103401d190441e540d05411201400401c05030300100304d0300ea074180c102c051a01e0050303640f80c0c40c007443c81a1044040d0b6010741002e0520171907060404040d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 809030305 1250 809029055 809029057
    0xb1212070528121e0f1209030801030b13080301030f021c0812180304051e090c13120b0711210a020111031023040212090d080708180a08 60
    0x188060348aa40c0c1a1545051900400445220400c00c3c080c0f560340b900c451041e46540c511000c9405e0070114004e0140800a80c1c10403070040b0b2032044603180440340b0003055001100d15050703034010344031507581c5d81d00c94864044282c2441d2021b850640240010400130f44204114a503484c8041c16081c10009500c600c0c204885c2c55810032030302c0c0c01010905031803800c944000e069200b241c1c44856407901107840d260948134821030040c0d07402441c4103168551600e800703104d10820305c680a030a0480d00e00d407408462045800020600c0240c01c01c2d9140040c03a05080c1c0c8103c80600d402003021086034450040a0381c1c00c0116402100c0180a0340180546040481103800e6450365030300c0980c0d07652104010000c1c2123902e01465400514428414805181e007178003400c100b0303203200c4018001c04244002544905011000042c1d0703000b030001500030101c8480d84c420034051600d64003107801a02da43c620965031090111094800079440b02c00041000c40c103110040c2c079051303204044c2c070b00c1c81c007540d203800c546 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 809031555 1250 809030305 809030353
    0xc0a08060c0f30090622050703050601060305011802040305032b05071812050607140c030a05040303090e07080f2701060501080c070c1a1c0e010b12120705 68
    0x42040740c45144151282c58415680084d420000d400c061401407460070700c0e203481d0081944040c0c2120909000c0041c01c000080c05907810074121842c41d80c0d00e81c8028060102401042e8504102e20050f0351201c00e01e00994003520352007809941840d1012004e544058002d4a040c21a007040551000c41510148201402100d041d030382c20050422403c1c1c0000001010350212000040038294140030440120300300da004181031511004841d22030042d0f104c0c9004009204d26240400a40407881035000401001168826107540c0880c0380c1d5005000710b00401201d1601c01b1845440000c2d03082041e14565135442000864070604014903c004003a901010482d8146180c3d90740b00300307111960b0001000b683c01150801820316008643d6035200120519114665880d0030b0902c2c0c1761050103800e41601c9540c540082800100030010f14540e014164428018925518064800c0e4142c280b42410b60540c90780c0e00300030712800c401c540007181143d202420607035a0780100b070001a12000940c44182c0b0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 809032805 1250 809031555 809031607
    0x3120f05100b0a02120f040e0709030201080c0301050607140f16030b1b0a0302070f02120d0905030f0307030c05012a09140d0b091005180c0a08060c0f 66
    0x109450208090310450041c2d4025405a540034002035400b0b41d4001440e0464540c8010f03a1a203030704030500340480900981d0042070034541204202710665a0003000041203078000d9032011001c1d15181c81340540c6210078011990000f03030400404000c00c094040a140380e8004e141103403d00e1800d298a14244400701d06030450004480d4410028002441c005035000b1007102101904d105d548003100308144144805141410380114130641885010b01d440d50b01c46070007074405441003041d8094107895404840604020801c110404103041c1000207001d001100108011880c280d03417074030203945908048504440b250348070380840d101144401d00003d80502860b4040320200d0906001070101d03000b903080325103052034804413030400b50f582d40d10002c0302e80e81104503540d044e11408107035803e2155460b41c003020241050141724040200300c400030183c3d9100b1f41951400480c102c1003022003811446000126805103004c200c20420802c000e001c04807103628210b10f0219a071408030390103c11184265 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 809034055 1250 809032805 809032811
    0xa140c0a0c080304051203040501051c021e09030f010e06072f030703080702012307030b090f0a06050d1203020901020f12091003090f150914010b010207080d080105090403120f 77
    0x41424018100b541b06a01d0001650500b4200400201103004180600314800c0a2036491960400e9542c1225851581c05544841000384140021a01c1d44000e4141e8041d100365a40c00d0601003061061a0041d0420ac010b4883c5895401c0308540a00e01c000710940e00448003400c00480722505442850300e40140c1010319200d40c40c50801614400006003810203690400c0c02105140d200d4144442601030305940c100600d0b2103810084005001c1d01c9540b80e0411061414861003c64024205103d4160340c142442042d85800910003400600746009142c5040c1d07022903145075020340c02400340d1034410300c12207500104a42c002c074689182c0380100c072031141c0c0c0001e04184905120000d440029a5400d091027040340d0b40d03a84140008072080301a01d21041c50611b9483c10340b05800c080959a0020440f4405021901c038003402400e14500b000e0240c8550200020030340004140740c040240c46880d035902c20380c6400300307100382100020b0080342000102903010000030440d10503240c148401c04400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 809035305 1250 809034055 809034059
    0x9190b190f0605030f0a021e0d060503010e0102090306161107090203221101030c031509020d051e01060815060c0c090603070b0a1d0a0e1501050a140c0a0c080304 71
    0x5801e604003035000315041040030020401c0c0001201080380c0c0040207058010794443d1071440c1400007100907502c040c0c20b200000f564071030b0300d2a41d4001c0c405556084001b00989907801a0080c01c0384954110355800d1f8000600140c00540310595182c640151800d22201220a42d0f5032503041c206141c00c844505a80441881585007412003450030900821010444110b2142c075803400c0701c3c0c0310084140c10542ca0340702059410788a034008203043c6600030811003a143c0c503480fa00300a90071482e501c0034a070740b920f4001685c2d00606110300c40385075001c40002d0066402c201e0202c40c0b0442c000c00801a045212005048540b61400109064400703e4040d04440b8840020000c000f24094100c610aa126440034066203103900211039440e10107040c162a0301900c120400f041d000481c00195000c42040000200340e0701e07814581c3d01c00d401c08040582c0449407240151a1805400074140000b0354101d5a410300080e2900144a40b6460340c0817100c0110465849405485480d0000310480c4c00110301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 809036555 1250 809035305 809035319
    0x608030a021b010201090b061909050702030c12090a120f0203030f0a030b2d01030b0d0605011a03010b0912031b0d020f0102030108100b01110d0503010611030909190b19 74
    0x110442c1d4103400d02c02131160f4141922480d002d6900600324911411140b0b184c14521048804984010300803102e00b480320303140242c170181d00c81c2c0002105000901510360302c5104c182040c0211240500000c00c020000e0b81403400c661011541940c0456906020109100269801304064585844421100c42c1d03541e640e410018203071104500c3c4217000b806048070003031401520084503401003041850700d10040a0f20750040300a0045c4c1d440960300000f20b641500c0900c00301e81c2006060318408940d2200d043c404503980c84441c8000d1040310310181e01130100304514542030403050029002041141d08001010340d01d0700c030b4100b0341c910180c4180e01184103183d0054040c00341080720b20404000714207542c54003200c2c1d80c55130546400d6001559807036191280a0f8050124558500a4441100d10341011100e020b81b242c1c1c02805190041412000520405400001110448203014058500316186d000ca001581041602c00401d07031911200241d54689884040d0514501d00c0a8a01c4100380340c524 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 809037805 1250 809036555 809036593
    0x3080403061b02060a180f050304060f090614210a090b072c0a080f010b13180318050d030905040c0c200a0e0106030219110706080603010608030a02 65
    0xb05001d280c2080200718610a0303000b013103541e401800d0100119842100b0910740500541c0010002d002042c80300e43c000c01d00c5070010141c8150f4265403a1000d198011950642d01c40401e880703600002449010000b80179611080907141012500a501c5000c41108240d070004e03d4044400135060b0355520007110034802000969604400c0c5404c0c04c1c09519200c7d09a10441000c60040c000300300390741480581c480d181c07010150000c1098000799814400103084107800382022040317443c4940c2450014ac0402200d1348180704030045844c40202000030365a400780d44d4030110748004104d00d60401000903072902e03042c40c414030700c070311954600600c0390801c0304201c00c58000080182c10040101e90907800900001c00010b440707800407850000281032800022000c8280d50854044010120f00010b281c0f41c00d50050f142110404084810342c0d0b03d5038000722918011440d03101d0240d4801007040041c2d80c080d907445c50b040507015002103441c81c2c407012070700d265500041044005030300c510405181441116 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 809039055 1250 809037805 809037821
    0x10b03070b030c090d051c09080606010215071b1e0312022506150f0303080612190828081612050702010f050106021f1b030b0a09060308040306 63
    0x103101d0504608140c031150215001c0c800c82e45020b01c02e01c0d00a10240b00d000c100124440c480d00d41d481d01e40f0b80040d000100198030500c51a919445841c01107040c960022541d00e40c10001d032601c43c2216580c80e18103c0b040c43e1402c00c51181e00c0000c22182000c00c40d40302e07528513103a080300b2a1700c030f04610701d00e4000d00d610240a0b012031041e00c1402105e82d6094a04001100c0c000c030700c1c0c102c00b01c0002a00f400002040201a504c1110000307100020312480003c0a6600300e9001e900c91401a64520f028030022421103070200483c3d80041091038841c3d041d1a4100c0505405403c44034101550701e007070401480343c01307090019000f0005005240103680941140e0303004060001d544100b000c4038201401409803084850b25058036078000644540c402d52150b128040d09410912070740d40c1d01c4101a444420600804600303550100c80c501041c2250b018042041075410340002c510200307030000b140249030301c800079640b003109180b00007940c00c40c40c001c00000e580212589540c8a1541ca000c8084942c58 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 809040305 1250 809039055 809039069
    0x720160f0312050304022106100602061320031605030d0906050a1b06140402030c0103020c1c0c0804090f0f0b0904030c060b0406092c0307060c02030d0509010b0307 72
    0x101010300000b11080b0710064011580e09085440e51507030f100107282c42d40c0d100d80c4800c1c19405844400404400081d4840c0258140b0a0060010b5115407040b6141c2c003003243e10711480d420507800e000001d40101d4a440710210240c010303600400f00d400002c3c2c1031040e42004054420a2120140045e140500110100d00807509015500920f801c60251860090807451002d0000b01d00c1030824000040000001d203540c0843c04004201c0110031000b000c0c90b042c4c4040c3e011380700b60034490074254043d108448002000100803c01655200104688140c44032004010840c05003400c0c40045e018402400203420b1105001c55460b4001b82c3d1001203c2d108c040715125642400c0d00d00d01c03a030710b94509440c1c0081e00340c6864504800b150400c1000340100707500003a0001d1500302c00284400c510b510460020212101006203403194464031802c61820350300c504030742d820070807000c000280f650f070102e1000d504500640381007000d00e01144080f50002c94940c02c00341d4607071a034000d0074502480b40d00094510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 809041555 1250 809040305 809040329
    0x250f022e0e04320a0204032f04113f070809060f1305070b0c100b0307080705060310030c0b0c0f060912090d05070303090503210304030503072016 64
    0x3444042180f94800c6207000350002c2c0300444e5580c0300a404540185800c2081204801c03801c82002c950924100e41c9440300d46420010030f0341600c0d0070300030500001106404541001c04044106d41401c50900400e52000c00b804c00d01220442010742c1d2607880582012401d13110700c0d000038041d10403c002440c0030741c1c3d500038000304424000000d0749590070170442c2c5a080700d0b13181c0b145456450400b180c0c02502ca1014041081c2070900400507504210641d041418402d18810784241650b50350b55004116940d006828280280c2c100000910340c00354200b44d0003217910f5a40e03250003000c61080d80120110100c00100030050344820040040c407070105100801d1a0b103850503095403074010750700404000301e07800118122107964150b0708500c5290850191404507540e407138041e015142500c2001d0090081d043c581711400c0131785041c0800e016002d01e4103861b55550383d4048070958001090103052100750b08890200522841c6001000c41110000f01403130101d182c1403c00d40a0389a12480201e40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 809042805 1250 809041555 809041601
    0x4c021c090c0909150914070b07200a0b040807030b06030c010207180236150d050c07050a0615141809011808250f022e0e04 54
    0x640c0d00d0201c0c0c00c454201e0000210010640b810090104426800000c00c905203005030090246e080ca5440c011580001210707012680c400c40d1010900912031301801803520403001c610309400c400a520305140c0001c100b0300e155500d0300a1030383e041d00b00e03800c05202644681024000c200c0041d8910350410300807801021a000c41100003580c808070f60150403c42c4842600100701c058507501640c600000290b0159000780d107544642d054a00602660408403920310400300481c11321301c40286280b2034544e8401c1c600964403e0f030b000a0b0802030540d8031403503c2000707814045030050054030307034841c8100c102003021404200d1100e03004009030040c2803010f4050703005803090f64496465100083da10100e98140d41d41e072002d024010301c4003014561404410900000800103882c004160a2400d14108966401c40c80b110500e0a01041d40c010890384250005602610f8241802955000441c040c82c0d207489000314080905000e00c1d41410100711404a04089441e05002d080449555402141c0c2404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 809044055 1250 809042805 809042813
    0x207020301140906160e031024360203090a0c1703071113090b24010f030e0715120506030a08070b040c0305030712030e4c021c09 57
    0x3029059441c00c031801744950701c495014030040030340401c2c0101070b18008400f1030000c0c000f40500034004020343c0100541500c1441c0300c040c030102900e510f28900908000c020500c00e1240042c1e110007802d0007a008400100b0700b610b03000030340c40307850a00041d0110303000d03900d415818502d890b0810a00382c0300c400c0c0f920b041504c4c0081900c003003d412264241c4000c3c50540843c42c1d0321000f000319440c113820203810074148445030203118060b4004201150b140313456100081a0f00b90301010160009445900f075840c040d1003a00f04114050f416000c2da10b1255131040f462602e51003074048bc02c0454003043c0c2d2280502072a116040d030120042d005050980401e07680c4403514890210000e00d80d1355000c010034240401482c0c0f00010f5a0f02030116a556807042c100644042d4410940b24006400d00e0f80c0454420404203032241c400031040030103100203001c1c0f8180303501d114044415040c00210821003c402100940711100001109140169690314030700e0b03490308046100444049540c18034642d40005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 809045305 1250 809044055 809044063
    0x22208060604020901440609040f061518060b13030201080907031401050a0f1803081902130e060a06050702060d0f090b07090501020a050604080d0902060703020102070203011409 78
    0x1800301e038010784d102c000000603512403d00c0d4050224001c1c00c84250300c0c0e800d4040c414090301c1142040012a11075518602940740e000444019400075084000b090020701e8182a109503248950f42c0401c2c461454403002e01d00046070f901c241280e402c100d141d982c0d000300c6403140002400458240600e801000501c0245100c40da01c0007d04200301400042c0385040140007800140d50b012000c07004124002000c1406000d0603214151440c0c681100042c0351034140c031401d513201804402d4407100c005145c8040e03600b002c0c0101200c203818049290340c44050024030081c140185503590106029080c45207803c02200e0003021540186c081c2c07407052007419048026250f251307504a507003999a2100c01c01c040080c04000c00c0c900041414505003201f003003288075100d8840c4403e40c1d00d0f00580c070307510401241e03525106c1c24080c055410410200d8041420000146003901050401140703110140c0c1c089015540b00c0c03502074005035030114660085240030b01504185c240c0790150038500303050000003180c070303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 809046555 1250 809045305 809045311
    0x50303010512070302060f220e0a050402061918060203040f09020f0f03010308091201062303072403060b1306030911061804050f04030f1d0604030602220806 69
    0x1040302510b07002c2c140100200304000103180c0c00340100d0b0322401951079140c0c442e0891166245a654800e4964400c2c10074400b90310704032541c0740d8030001e03580c4800b01100010800504180d810480c2013007104148d000d54104086404826901c0d00141000c1d444821100e01301504800115082048104080380b0520b400000756040d01c0307001640d1381030a100d26030003071250b03100c0b070001c540021000106000d040c5010300b9042c01d0030b9840084003030a040c003140c00c980c8a801703161a003040c40a1042c150031405a0b644e66411005002c8070901034917020407216441c540d08524642004031071902c00e8056060003801c00030511141c516060140d001c006c03a2a0100d20b01070b080030556907440c2c24003800340ea44a0184880310141050b907591809d0f03c0703810801000c90517200c1c01207007490081940d0030703221840544241d82681d544d8942c400e00110841c0c8010300980c101001c100d010006a07403550314080140300542c85488016550b07203551501616071030b48018103c8640b03520180400c4082070106449034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 809047805 1250 809046555 809046559
    0x21006030f0816061e15030308011205010207020312091c02011e030b0d390e1008010e2b0206161b0b01030501060b03091009020103090506040606030b01080a0503030105 74
    0x9210f0380160300ca5100c1400c4201d0250519081001c0c070320000c8000b0440d4400703642aa0818071804c1800e1302c1301440c44060380300060014100b8070040292001d141d00703018110f8400c1c00050319143c41600040d103400400070019640c50390000d4140c1031454018650500b0003100070070039410f40c401d074002070300512154206480110148801044042c0719602c18140600c008019014440c4035041846015182004c1d42c56074103c0c404200d8502042181440b10800d10071310708550940c1803a81901101c1c00160000e0101c2e5172840300410b15030307020301a00c11980c00703440c0200b14412411806c0003124680c1d1441112600031940410805940881c2840d4000072882404c2c000d51583c6000311008600c103c8642a941808441c4000f004003d21103a412640218024081d0070f40794403010184d0311007650145d0490348494240072a00510b50003600c111380c014140022504e1841e1903032424000101e404540240c0d0700e03c0240304001c0d081d03010b640035014050003080c0d007000540d900c6ea5070380f0060164038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 809049055 1250 809047805 809047807
    0x1d180a12120209040507020c01020708070f0b0c010e06040b0603100b0d1b15170c04180e070509091014091b0d12020601090b040b06090f04061502070303021006030f08 73
    0x2078216051a01120b03407402c400741003000320f4540f07020001e4840c90f131105d1440c014066444009401c42c400100c1038140d58206611840141c5040b042c981a0b90060004410325500d40d00c8403101e003003050000d1842140510020281464044101418603c03103000b054549813402880b01240d0f201c003541c10004d264400c080f4802c41e0b200c014210140081640103040441584c511311410680c4940800e03074039110081d2907200d07178170b51000040c0d01340901e01600329034800c80105c00781000b00c15045032406c00f00e0081550010b648650105517030400841c1c64030f8a41d409600a02c02e610f451380b165008169082420417458180b010701c498444444422040c0c6400b81c001e0041d03140d5031160f0541c00540ea003c00f40103142503055101a454480034815a8103461a03d81c880190307040c03d002e0200c1c0c501e4010038192803c0310580400811460425095804c0781d0369220126004070059400c18010340d882d002001c08502d5454024941031000c44020340f0036041080801c002802c0180168049a20900d11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 809050305 1250 809049055 809049077
    0x3070f05070b150d0b0a0207110a050f19080118050c0103090b0612031903090201020708060c0a030c0210060303020327030703080a0203120a091e050d0e0402041d180a12 74
    0x2507012101301402900641d0300c201400351840407503004108541c480d4603a14960030030182048515a002d12603075400c80686c0c0400c03c010300d40880c42c840b4512446040c40509922040d0240c212400b558006051004400280040c00010040140c0c030120034a005e20100c441962a0500c00d0409015035005d40e101205c00341c1400b2052007614400500c00503500001554040020003a01c01050309074094003540001081303600020a600e407146244c3c00d451858100c404004800401e40351000c6421070046280708058901c0a0280300010760107603000350307251310842d500d5a000004950120000000c038542144c0d068502268281c1104e400010251b00d5400c1d00c034040c3d096100d0030403a40c2c003004e841402c010810045601c07030005a401107441024035406c20301d1b0964a422450000391142c3c3c040c12000210a01c03400707455801c0c060103040541896034815111080c289110800c2c9084d542c0c050070480748000e92900078409100e54001000303601226280c0301030003100f441140c1c0412043c6c40c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 809051555 1250 809050305 809050309
    0x140310020f070501020d02180109140105070f050a031107050f030a0b0903070f0627020f0d02210309090901181214031303030c020607170a0e07080303070f05070b15 72
    0x15502c00c940c02000035950f5100c60301002000354415004074100d04401d5141d0141d0754070030024542682c0d401c3c00c01001d0900840019075685d0044003040f0380700d18800d420f140015005220084825120b51503034a2070a100c424040c0c1800ca058000500070504101062100d65001641c10001c0d60401085440d9850b007540c00c07411889000b5002c2c28256512000108102c0f00e98051031000c10f100520840303419120112a10750b040201d00030790303c403c0d146840c4880b803800c60312021020348002c2c2540b409203150054001060710311aa0000c240d000404d0601490078044062540b04201c80f0007000221044524400d004002c0b082c05040803540c07140d0400b00714003e8100c0d10003940748510f09034480c82d0141c800e03190410304a4048001904000e510000c0d5400054824010f2845031030301d007072051907101000b20607800140341d403071415122201080032810a010490280111101959407032611175000740010f6aa40001d500b0820300b00180c0340441c00b580203503500036003c0e0049081100325000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 809052805 1250 809051555 809051557
    0x362a1805030d0e01200a1401050f04020109091a0909010b0906030601300215042108030106050703120c0323070e0616060c03020d140603071a25020109140310020f 71
    0x207035845d030038410102c00900f8008045085020401c047c8000d2029658080440c0c0d180304003030303c00a02082488100b8031004103103401c15101c0342640a81c11311105441e20005520ba80151982c011a9640c0c0f80043e409082a0707241950005041d0014011945000e07601064484410280192420342900b140c0e4010642c25445c9840c2d83c001744040b03020151108000c1980d846403285641446074581e4005146419240204090740c205054500b0350303292280c10b0310359500080c022000c0000240070503020b80304500c18841c03252001c1e5000204903100c03401d1002c80640c2c600040351220141420030a290340d00035644005001c0540321035884080c11142d040440d103030144002c0000d801c0c00380d8440000e606601900001c04203120a10072401c01300c1018241d038809458154141d00403410074050303001d40320200c0014200c0309000618207813032003080d10a883d04e801c20782d055405075410303201c2c207640c1d00081c080007a0442a480880540f03858000959030040d00401d03010546c0c0119121112000d210 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 809054055 1250 809052805 809052857
    0x21e070b0720030403120f0f020c01110304030206040906050103060803032401050c010f14011203081b040b0309030307140c0606100203040f08010204362a1805030d0e01 74
    0x4080766184d58481c90080301d5002018951400112620305186101d441a00c0e0400b02040b070340c000d40408080320b40111070020100100b100984020440000140c032480c008100500c0e42c5040020054141400101612403a074420f640541c0148103000c444170904030501c056641c0d40a01894450350301c0c0058685002d0040d0120465103802c0108000e524241c1100380e041102c2d111160640e070701d0740356400b00c200c2d8024001d800941440009110a4480745a00d165600314420079401e00b582d600d68000682e00854180006030004400c1c00319842d00002001e841c400a9a01c039428100c2002c5019a100402402c0074402d424003201002d6550080c401c42e0060401c42c001613031540c0d2a400d183d80031398841d210741c9402c039448000e12b160607541e600a41001d0b0045c21210503072010300040c040c026180f915444040845800700d907142d03094000c903211660052544a034401001680c890007550501c43c0c0c0b10b203000340c01913001c041640d42d1005a6140d4172000b401d01c0c510805c00c54622060043c1c40f8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 809055305 1250 809054055 809054117
    0xa0807030f09080d02070603020f07080f04081501052d090a23040309050d030e030607080106030f0510060c0609020d260906030c1602090703021e070b07 67
    0x850505041e8025000e80c840c440588036912056034504461380e90384c403c07040f0351005802a079006c2c40854401d0b0014012414403c1d05542070150584914289500c205c0c0d01982e40c400001d410080960148078100d4180041c00c0100035030741c50407010404e044081b01580300c1c01000c0401802c900c04407540100c12902c009003480105d4038181000100608520455986a00075004103110881070055090b100e5681680c8054059280000380804200002000c4081c040c15510140c50f80e01c007007024510601450380d0f4000b01d03501d4048007504641d03e00600210a80c1040c00b000654098011150210351300c0d4900703a50184800c0c2001001002e900f0310003903000da40d00309020207019011007134101104d00e40030542071b007155100e48584a44524007850380c01c0601400054a94a00301c405840354100c0e03070900c1141d07050b465000900d141c6d42180d90f400406d078049000c501c4c415100c03a240c0008268480c40f146000c00507110148414001000c03034003003045803080c10032400701100207688000e6103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 809056555 1250 809055305 809055307
    0xa17030601170a181103010b030a050a020108060a03050a060c08060303070309060e010905040504060501050301112119020a081f0b0306060306120708060702010f0501030f02042703030e06130c090e0a08 88
    0x1d49402185c41101e84a5244203608007130410529140100d1a40d4800b58044014040a0059401920b61240c01030590340d000d0078882d40000801e10904c240321780c240c85a40c1c006075440c1d0083c5c0142080401400f85d6001340c0c818064100020741240141c002e48420381050500e0342c00e2440100c412003038a421080e003240c207010520040201c0c50b086130381651800c800900841a50030b0b5104001d000b80b009903440e56251070b181c03403107184818081c02c1c2c00007185e0600c10013002c3c8102c4110107030790094040b42c000030b40320b000f088114621904038150303208050300c18460580c41c2019000745400094285440b601c400008510141e0340c01c1c40e0a0003090001c403e650070035a8450403151595811201240554241030500c1d01a81240c8200390507641d0100442001070202e40034480240000044200c1440c0d000a680f10070b120522054003030346100781d0300407a5858000681c541004d5000e441e9a424a5600189600140e403c0c0f0070310050b01e1030f243c00082c1d0104d50399030041c074020034400080d203d604 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 809057805 1250 809056555 809056601
    0xf040606020106181e110f0307021c0305010635041b05090613020901030b030f07030c0e01060507150609050406020426061f05030d020a17030601170a 66
    0x5010b41014080780c0030354240130561981125020706480d0000020412038030701081015850043da070203d02d040700080081d0341401d11403c440c00455105542220141e804011240e0580030034261512080c5005c3c60140915458031074081d00b01000d03291406c2c1801200450b104a90900c11a501d061541c41c00c03000c200380c202802c1a00c402d8021424015035005490302c0401c060a2074142d15010b14406000544084001d00b00c400082d0084030401d41090340b00c14401a00d654104580a0701440c00b10150103801d145207441114110b0543c440c94081e1780c00e0004000302e6422105a81c02c068120340e900c40000444604400106910740200c0011031401d010f2005222143d400f42003651b4078004920341d52003000108012022695402c00f940c2d030302039800542445401d500c45100040e5850318030710595140c9000a080050020302d0000690101c1441e00511030340c0843c2c1050340c0100000e0610b581088400200b841031440d01c0f07452507204000100d0b2040d28264071072f2607020a503c806096580b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 809059055 1250 809057805 809057807
    0x509011103161e080f18030922051006030c020a02030a23060106031d060f04020f030c090c0c0d0f050306061c0504051c0e0603040f0201020118111014180f040606 71
    0x303090385c14030300080c502000954600d09140600d00b07a420400b0040d400d1541007402c00c1038610b00c40040d00f803034040201d040540089680281c0b8010108030318038002d0f0f10f060200c000d08441b45004240215402459000096200484c009940c0390700840c0007003212403030306042828082c0c20414102644620400050280c0d89039110f40ca0440042d100548160300810a05544107010f4a51040c4080c00c240803400628209851105e40c00000d41900d0308191540000f0f26060030850b05070740404000119482c80943c10320581000c03d410342003107000da00b0204c02c0107000e030100034400e602420340060f030404100c1072403c000004e01d900a40501043c600381c5425600c43c440c1c90300f00c1c0d00400364809454041c0340561031032107142034098900da003541d0300c2d92a0030705002c222241c02c0c0c0c15556035101503241324180c1508140311501440d541d012449400c010320100366100175004040000b02d48031501c2030031031a011a403003203000006962040c01808005080c01000103009680305240c44d01c0050302c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 809060305 1250 809059055 809059067
    0x105070209060d17211015030507020c0a09060f36091e05070906080c040b13060f030b0f060f0405090f0718051614070602090a030807060509011103161e 67
    0x174000b040c02d100420385614211103044c0340c2c1030059980c00a00c800349848064420313031180c0c2d0322400a1048440202c41d1101181c0c0c58004c43c1c0201090a81798402071100040050000c00104040450402c000300c084500b4169509400d154580d40130740c00c2e4002c0ba201d2402d80058600e140c201019500c95254042c0460a441130000119440e004031380e000a080520f03889800304886040b0042c100d8625040200b1000304290320709103a11010000d645403550762184180005000401070062200d410750400404110004101c04030503905d0300100645078071240000b9043c040c003520f01080644518a276581080d900d0f46804103a44541a400140d0301009010503514941011042286840e41805070f510940309070040390200f0300c0d85c4454030700d003410741004003030b4203000d0702006061009030000504c0180c405d910a0f200140040f50765030500409110b11900008002c00030091102e04203221403450000809000c10135203100091910703030f80139901c90310741c20f507a070040500f400750854005429 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 809061555 1250 809060305 809060347
    0x60207061b12200109031e0c050609030417010501050307062d020d09140609010c0302031c1b320409020c03032e030611071e020f0105070209060d17 65
    0x410f62000b014880d03580418890305408030340641d940c004141003041c02c1d442920750403c6100400004e0451913010960a00c0424081c0a040c0041d598503031611501d0250095588014001c1d80d24050040281c2e80d00061850116011402c00300044008038600007804207000b016110400e9940c42c0389040c1a5002c2028026440341e500d541c1c041c55201e1811590b898030007404960082c1c0c04201c1d04007698020301102c000306101c0d10441c0d1414100c02049024002c1d000b40707c44899440c1d0803078a00303004003d18a200ca07041d29107451070655072410700c0c40d0704120702083c100107000c102c2d10441c148104081c044801030040c9040c00d41d608c035004403846540c0c1d0301c11a00c0f543c407070fa40240300508032400d048205040d07228680b9000c000c0c03030031510340000030050340d000042074074801c0200c1800a08107140154052440c11440d14806d4403500521403a03d50070500981041403c0043c4030040c0c2d43c4128180d0005010b94016801138071074030700452004c01d0405c4d000100003010941c00c201c40c110211a009c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 809062805 1250 809061555 809061587
    0xd030e12010e0703231207060515090a0b0406120b04050610081002220b070c08161e090608030c0c010302031909110405070522060207061b12 62
    0x208029600c8000c0d400c0350190516021103070410f03031040010481c19240380021007160102981d40c08440311141c1c1c075184440d64140c1c581800030885109001842c0b050b0380d80004054420107080c025030002403038441c0000d040b090142d65031005903c2e1525076500c0003016012a050072600c030044c0c0d05142c80c0c1482c00320b0b400c0700d6502c1442c002682442413107007800f044941d60790086c4900030365060100003a4201084040b1041c1890182c83d075100800c210a5005162501d55140d45041e141001d10060b142e0381c010840c258464842c0502e1503c440e240c12080b039a44200e007111404000c401d00004104980c0502c06035420204041781c41403022005007206190f84040340d0500c40c0c12001942607002c110740c01841810392000070800c00701c46400207629244034242141602e00018001011070700142c900b100001c00101d04460b900d84460700c00c6422020644d09054010b241190081d540d50322400344c803081042c2c00190007056408001d03481f00c8a54001035802c00c0c48040b18000344000141c1074850 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 809064055 1250 809062805 809062819
    0x612040b1e07020129090403120b210c0909030a030e0f0a050d020d0315030b25030501051504080706030213080d0c0303050106110703080a020c091608010e22060204050d030e 76
    0x1110750503c04070a17102a000030384844030a50302c64905507400c000a402c1001d400303848072100d000c9540c40040c2d444241c092804040d00031a00100068038041800401e14000d101c0078091040b02c403400000e40c2ca0010440c42e000c43e04100d0b03ccc00c0e00c6d04040382c0e078215550a110f801d43c05020010040340c10b00d1009195402c60b81280100e05c1d0440c199039180032001c490341302c194414400b01f0f00c10004c03240d01c030307140c20b040b43e806068412110703444a00c40801000061368410060003140341001e10ba1282c2c000c000801410305040560301034660b00d20b0320030303a8140760340001c80104c094a0189480001c4c502c3c601900d0514a16003c06001c44800d40e4003200021300c0d040002c00c0f660f020304100c0e001c451030503004101c00c0d411035582004c1a13111101c0e075815882085004401651102c0c5114400c00d00078104079085403032850050214030b4107030451009485810200414498072280c0003580c074a00340d0802000c1d42850138098000e214580019412260262802c001d158000d03801058116058800c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 809065305 1250 809064055 809064101
    0xc12040e0f0f0c1810080f060d2a03020603041203181a0a06090207200d080d0b010c02040e06070806040204080706120f05090f010b0612040b1e070201 66
    0x103241e450340101d480919902000340030a141e030750301c4000303404041c0c030b86a682040091050005900003000c000404005500d90042005140ca0142d0268000790151900003138095036a454403038121102c000e030000840c00b041c44c0312400001c01d200c4402150050641943da00349820018030130b80c00381c5801400720342401b010155080b41d1101c4003000360f400444140034000d0710511424058406407101d01702c56107680011401d00c0e10781c4000c1c488a4494500d0140305404e4029140250100701d00c02c41c481c0700443c610078085036024044a82008074481c000031040d518a0059031281c15040300a50402d1070480802c503000c1f80022518050941380d201e0000980d43d0f0300400c0168403ca000b90020b9402000b010031041d409054800e00d15428210302080d003a5142000780d0407544100c034040442c0d405040000060039084c0b0840041d507101741c0303400745445400c180c040038414025000800a02250002032100c41c280241004d6080755001c4646550501440c001c1c081d000440c10307002010b0b1424a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 809066555 1250 809065305 809065321
    0x604090f0f0501061505030f07030b040609060303030623061c0f020c0f2d030715090b010f0305060103241a0a050901150f020a060e060406050c0702010c0b07050c12040e 74
    0x1440746110450340c9075031542e6100f0701030308823042000d03001e08145901c1b10b81d142c00c030ba036581c00744401030b14000c00c0c0007032254074500f0700400b82c4065138000c0d00d402e60300e5101c00e200e034503800030700031141c6405850300783d9203640c640c115406002d40083c4400310035180a140c12030080301c0790010400025404102c2d1010b40b00c0c0c107150b075200c441c03070404081d50500e0748840c90141c00c2403443c04120014103500340c1382401150340300c0188500c20302d200390b01d00e10741d51713002c0004102c0d8450155014000b070800c11400c040c210f94031640c2d1507106000c041e10b81000185d01402010b0650392590486008035014070985004000c04896804020b2a01c0d10038920640c003c42c0500300521245e0494030141019030742c502c0e4150382510ba042d0004407030021801941d06507004200507004a00c00300070300b00000c6c1041e00e4203041880450704050300d40c032641101000340b4405130781c1c021840400103400a0410b81e8940751290180c9103445031008060380c2c0c4c014800303c410b148000e00050002c44007070042400a540e03e48035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 809067805 1250 809066555 809066579
    0x120a0209010e13090506310f020f040b1207050f0f031504020613030309050a091b0f0e0310020c01140603120c011104090b10080613050604090f0f050106 67
    0x2103518002101c070b41c8842d0740b81c6019008000e4000c090303140012401c8882d01c130300341040c2d8129030261041e007500c0450a242d0340d140c00c00341c426500044004504101030b07902c04e840e003048080081e1048005001282240e0344a40c03015080340402004520003c0c00402841d4030340ca0940304440c440d0b00359800a40060404507000c07402c41d03c004024000c82080b0b10a0b03089103680162003a0f03040314003441603101080c0e075040c440b00a0750203a00e8130800c20f03242c03600704040381c0c0e8541c20620b002410f040c500c1e1003402c035019504d90101c8550134001d030701e041c0c1d0240803101459004e2000c0d07494800c2200035010000b980d07000b00000154400244044540344c9001c2c1901e01055648a815a10900034072580300e184001600f030603000c12002041154562402030f00d29049034024000070b86d500e000540d50752a00ca5000303008200c060525001600e4003d0004002c0d9a45c1042c0800d0b050b203c02c0092829075031588042020f0740e010391180705078903490400317800c0c1c04409001106c00390b1900c14042850880f1007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 809069055 1250 809067805 809067817
    0x50405060d1a220f021603080f01082109010e061813060f0515070206030a06061101050108100e0c0301061e0803090303190c0c0312090603050c031f0305010c05120a02 73
    0x10700f0103075161142d00f442c0b0000703011980301018a0340c1d00744400707403042c2003404040684900075614800641014840003001d401c040e409070f10303150b12902110a0300d001405644c0c43c848160441e4076203d102000c01078a800100440d1203600100014500e5500761484880600a01050310000c00c0301c1c2440007070724204d9800c0d004105960110300004c0115180285075003402c0c4455242e054284409980400d200d600191412900192155400e2240c19800300c414526002003e00074000d40d403410100c25183d008094884000c0c50302d6001c4c4400840080040e411880030103402046002d50b1488156410415241c04d0107002507003110000343c0c0a00002070307421890005010b14075024003403804103c4441040c07803c100f80588054982c020421a802150046020303110414031740d410748000512003030180d000300d02407500d06400d0103015102102600e5100c0800f10850826401840e00803103115070660008000b5800e01a036883d0303003a40303c4044c01800d0700f0b203142900399880e00116802640155 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 809070305 1250 809069055 809069089
    0x601170c190506070206070f05101a13050c0412060e0f03070803070c020f1009050114120105120102070b0705070c06030c020c190807090b030d08100b0703050405060d1a 74
    0x920320034050b902c2c2040041140f50320080c0400d1429607950f4602e072144004090981d116007050095040c3c180440c06010f41e584032100d08078140410901c00910314117001626020780940c0c40c00001e0f60800001c08550103840e12501101c0d0802c168a0403201401a40701c80342c0b92402210306007000c002c0e00205940e00c407a48541d0080c21555036150403079041480c100300b41d0b44012581055031154440e03645c103401e1060195914032034141490005404450fa001002c0600c00c41040340c402d02100801c1d82905442c0304450f010000700502d05000e01a02901d0005480c101c003803414031002541140007002c00c1e41c0b107400b1220340d00703588100650440b09204413510142e00000078840ea030b480c28081e000c3d000c442d604c0d1103401503602d408255290800703d401a107805641d0f070b1071416107403804000c401c1c641041c2d8074124520703290082803c20203440c00d2041095000010a08070101030040702640c000d894081c060b183c03581c1c0f41c6861540600203211a0507180c0140a00c800400e00340128810f04140344c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 809071555 1250 809070305 809070349
    0x110306090a020901120212091501080a02040b27041401050c0a05031905090a0201030b090106051909080d1205180303060105070305040302041812020106080a06090201020c030601170c 80
    0x140500c8503002e5405111040c0c100300d86401800e0004940d031002d840084192410251035241110b030445c60800c0514800070310412150041004407400100481c200b5030540f00451480c40382008200d6007c1c503c6901c0c2640d08822a0b21165802d00001d154480c41c0283c0c204c0502c5045441445c1c202c1d00183e83d000701c4440c08000302120345004100454002860303450060140b24411511000c499003651445000c0e0020108207080d9a1305010782e0800c04011101c0100f6545048000b43c0f2621a40c94400d0b103198090320100c140318000c440d100001c00c003c0090f9960044a110300602810708903004c1000203190070041004094000c018201c2c102c5510000d6246886020054465400c00c80d0f0840400c5010000130006890f01d0054a6248400c11394410f0050314624008050001c0c03494414116890180108200100001e003050500d40118000400c0713a860300040b070400f0200031003650184544400040c045400d82d420a01c050407040584e146001c00310100700849904071110003031200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 809072805 1250 809071555 809071561
    0x90603090309060f020f06010e01080d1e08100902030a0609140928050f0303100803031308030a0204051008150109050609090a0e1c0212030c16020604121511030609 72
    0x3000b1070321300c4505281401114161030300c800120385402c0c802d820800600d41c3c0d0030700402c031010080001044a5010b03080040b00f4007040c00d02440110f1011088a04102485001c1032000b60725465142c06404141c0f025580d910b80801840007415443c0b00b480070480c40c0855450f46129060201d07030103003681601600a40c5100d0050800007c0c1800c034041c9240d5090103407000264007080300307600d4030040c2c001075500c1e85001c00410f82d0004d20b681c072064a60f0020020015912200d2110707034051544000030b0364480e25005241c00007805660007850300034102101d603030b00c59a08200d2651046030301c1c5100201ba08440401140d0300c041621400327411080520034418103180002450f94040130075400056a180c5050000d80303002001d2a07000c02c25a442e00c00704000560600032060014003507045549541400c49200400d481480d5200305141001c40204c030440d51100e08680041c4070380c1c90300120350180342c248107079622208010545280e103880c507041d40f00c0b901c4a06491142c0300013440c2d66800d035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 809074055 1250 809072805 809072807
    0xf0321141603030b031603050c01050705150406140405030919060e13020903190615060c03111507031a09041112073f1203020a0c08030f0709060309030906 68
    0x9181e400040701451344645802c000ba031804c0001062004000194103644e41c81c40c1070140c00d0080c502034250401008002c0a070116500041c650001070480914904030380d07941c20020700030728101d403059080c01501014003091200000140c07904000444144007607007c500c00348a4469060301c603030404611030324002e80d801c1c0b030425020080c0304103d600c00351034150841e0000e400c00c0310b44803484039042503440d0001c0c2881034074420800c01206c00702400040074104600a020100e40c080000c0400c4448480a291694203100040b40c4d80007800b01c1d10340f141007d80c0c002e4060105280f003840114030841d9a812710346042c0340300c2ca0046401085514a08a100e410311101c011540760005640c0700b42d01c0d000030746501c030800b8144c18040d41d13041c18281d210481c8030003103c02c41b0030500d0303003840141210400c08600d03100c1d0b0990b07203070106040c0183d4506495000392005c00d91120050400a408400c2001d04046a5403881c4110315507661031480d01d07240d0000f9001c44420000140c0011207002c001d100b0b00d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 809075305 1250 809074055 809074087
    0x2401080c040b010f0c0303021e0a080a05040b01030f0813060305190203060a0501030b06120906191a090a1805010c17010605030a020a05040b030a151502060a02030a060f032114 77
    0x1740b40280f40143c9440030841030700c2009034a2190410b6440000120036a903d03520000c41900551103e800f40900d0601ea1544910300006000141c502c00e16404500704008600007220008101010b185070303070596071000070b07000704401ca401030001080803000040e0342809100322445001c00900883c1da60f0f08000045004103a0750b250184c01c00810040da00e42240f0043d01d4070310a020460013000d140c074290320b10700751710070910035030110182c1041103a03c04000b4402d030910203041c0560700b1103140e0740d841070464058581a8040030f42d607008200c00e20300340081900441d01200980c1c44d0700600602c1c00d03042c0c0401c1e81c800d2140c4000101c0138000719500007140c0d0028136040d1090700e0503508241e00d68410f003030a544140c4141c4c0b003050741c0d000d0b40c4041e80400c5045100500304145074000144030008007a4a41c58010014000300e603001001450007042d5a1000c0060410503a9806401e5100d28020300d0f641e41440700202010f040304040302c50648100020005800e04402c110700341540541a02d0300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 809076555 1250 809075305 809075327
    0x1210509031c270803040b09210c0114060907052b02031812070b1308211b0409020715020315040b060a080609092401080c040b010f 58
    0x35020800ca000140040307071a151503500441c40b4009400c445a0100f6120b8a210b03801200110301510034103004200c6060907039504ca81c20086041260343c8100740c85003080a00004da840700d01100030101481d803001c4010b040c40141030002000b4400350840f001b0440102110042ea04c0012007002a45440c80795010344005090700c041031002000d11510034100608055080881a60100030080349000c8a043e5080300442c0f80080c000380c640a06900590b8450714002034400203d050105140350101e035031401206421184290700c8050650241c66114a803c0d011194460003801081000840c80f401c1046000c03400c0440d85818948170824000c1c1d080801c0583e00348050300d9114602030850300055104140454070440502d00c4601048210780c48071540320b0203050305006055145800c040c009810040c02c50320001d007540c801814524000c41924501070039a202044016200380310900c1e41c1c140d50005040e200091074210910045810950000340013510403d62411440d000b140d281003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 809077805 1250 809076555 809076571
    0xa11010c0501091707151a0d08090409030503070801170c0d061d01060602120f2b0c020304171f0506030a0c12290105010e1f110c012105 60
    0x928100d8940b03ca4601a0544106401c0b2081c0090210104542000c6c8003100c04030001c0300300880314802c1e1a1202a10311204d40034010b001c1c0c8006802481010402d07208011001001844051107524004003245c00999001c0c0201d6806000490844000d170302d14400c60b1440740040c1140c40b0180c0400c420005207200a07a4015951400c4000862031051010704441782e800c00443c50a1806000901d00740d01c21040380286078050108800604030b00d81103407906070301204688024400710000340340340b41141d10303100651444c000c0440012038000c0f000d007080f074503090a1415420750009080c0e8070b441c8424000701101d00e8a264106c00c40c00c09030f00c240e0704250041d00b2200d20b00800d03910030124054941020ba104c10701c158480040012026240030711f10035200e030b40c1c64070183d04203080d94064010302950341882800e11117100c1740c2e121581141e10042442c0d101c0c03901036080c000d002e007900c03111150880c09405010340c0080359500519903100304803d0b1404403503d01800501d050010302010344041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 809079055 1250 809077805 809077811
    0xc0f0405030a030c0c0b041404150503071e0e04020906190f060507060c0c051b010507020619020606040e0d0804080d06080f0d02010c08040308070903021e120a11010c0501 75
    0x219654800304104802c5034860748810900b40b41a050040c0b141c4250b5020701c3c20140200070074407140012965203500840d09442c08a07003101d941c0c156079180800d81d08090b8051107501000030b0f01001041301c0d15015418201002c8965459050000ca468000c580c0a500052a940031411508140303c000005143c0096031450341502c89107a4a01818141d00440004034007094080c05e002203031143e4003043e05141022032420605540704d903143d050000e5800b00e8558103080c04082a4010f8080303900040c0d0040c8000d640382a24212a00f0040700203a00d00c0c010312a1000164040c20148245007105444200030800d48050758821111140c009004440720704090020460b4a9018050000600b03008001f4000840d149400c0782c0c5000d1070425050110380c1456042121680c00101068106400d8641248c141c2d60b5540c2c2a1101e403c140d0000b034000011746106e000c41403600c0c503a004040d03811180c58000d0401c02c010181d5413051164064142c2e80425100310307035980141042e18090388a0300000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 809080305 1250 809079055 809079059
    0x3031b0d0f060b1315080126060c04061701050618010207030209040302030403021008010f0b03070c140d030c030603020303030c0c1c080609010e250c0b0103150605030a0503030c0f04 80
    0x70001c2d25115440045025000f04541d5440040c1c40a20005000d5034503aa128024655030001c01100040c411203500160580d08600074466104120420008079411030343c00d4280f00104034099440340c81a05e00042800b2050300981855034034150495100400503070515003444884010b0302c03000039460b415486000c07400401600c41e003176210710642c0250059a2920f24500500c0800c407200b0768102d082207103a20060000403000080c00043c2c038150180e03280c6a0355440c1e0700740c5109541c010080c00c1009011182e0403012030014003017122501503035090000082c8604281c0c00c1e103243e404001e43c19041880020364803141c3e1341c0a0103c00070700000b02d0ba031034068a00301ca0410380001c0d90070000144440108400703800c02c00841070042a201e1201642440c00720f401d056102001c031035642c9146194a503481c4640e214402560b03009070001e09200055a5900d01851207121020100800300d081c01c00008182ca00480c0500c5941c0c0c116029501d9a0345860303002a003580a0358031845448024440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 809081555 1250 809080305 809080331
    0x207090c030b180a0c0807020d080406240303020106080c030c040509070506041401031a0f12160602010f0506150a0525050a0b0a020c0a08131d04060e03031b0d 70
    0xc010007950f42003981503410700300800b0050b52481c11449040c00042410710000550001e8246d500d02c480e86050105500c0d549005030140c48150000e641d90100d0700c6950704140d414000c9071086078800c1e0020803030160380d80c0c00c0c143c031110800441541608030034000d00223070416400c402d40c458001d078190352400b5201c10001d583e0782c10a400101d003980620542c4411940c2502c91400c4480c5c40440c0c01c140101c413140001c0c2101c01c1d100c1400d01610860595851408003009814003800c554440101c5554556400a00804d61001d092440c0c6007404040b50711810006249091218030507c1c091404521440940b110b6200b220a2240650701030034000c1922010b40d030340c90000b407083d805003403080c00324104401c40b1400a48840c40b418810000d00078540320005052445552089035140c9039124200d9030b2080c8134466010010300d40542d842e103584c01c80485080d512882c4610000c11030890035550b043d07503d001c00c0b19054140001c0d07021030095000032202034500c441a444000c11a0000090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 809082805 1250 809081555 809081569
    0x110408030f0403060605150306060a0c0b1603050f01030201020a0b070e0a030c090c18180e011b08010b0403030909051306090303150e04020d020105070807050d0210060e070207090c030b 81
    0x1d072440340e40c000414144100302c254010640105012500d03200b5144510050150b80e200190443d131103104001a01a50b02d0f0003400f46c070007026000b030064901031910382021420010032121000c0044d10307100004000142c08440315041c3d94040e40140300c0b0044503038821424100c003401d0481841550340403400c1c15501d1764070880184d44a111190170320351a003034098080e01c17002c10b002014014484c80c5050912624005034007200c01e00081d5010f01048030b4080c2c00180101c03000130b4029401e0102072000a0652680e664031b52485540f001d89030b07a0382c0d0382410400d006600004000580b010800c2001d40f400c3c1d0040e607008401c040035066402c4403680c0b080e040b1403910000700e000c00d40740c480c44183c540303068032590000c10380202090908d00c1c1030741c0010b00804015100a05014003c2403803400e1003550f03816181599800300071100441841200030f540e07240001c0d07211722901d003031031400301d20180181002d6010b03060907001040034a00b800e130f5060180214400d1002010b0755480366000c169a545 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 809084055 1250 809082805 809082817
    0x150103051032010e010e0f180a0e071203020604030305101706061011030403080307031503140c0406051c02040f2a1107060c0515040809030c1207030611040803 70
    0x44014955007242c11601e81201ea241c0d10074140b00c4c44144404250340c201c8000b000c503010031501c0344c50722107951000440207000750451396400ea45802c00c10500380750543c4079100540300c0300d0491b0f217000d0b620900c00820f484100b000500607000b407004200041e001e60800707034200540e88078455a898444481d942c41e0044a581c6200c603138811010b00c130060418a2260441045c14a403030b03007085034400781403503483c400d9200050000000000058000f807280c1d00810b00e46075940c030300540d543d9403402c21200c030351820048a0b00314065000d5000087c5070503c190b904944000d00703480034465041c010070844914516003a6001030311800c0d03110305444140714604c0e09220a00c0d4101003941d00140031244880b1043c0e054060080c142c5609803e0703107001a0b214111502da280c4800035145134030b172450030445900f100c401801a4002270004014101c405040c0c3d06500343e003120113072003103442000420041c4d44001030a54020440c03d00120344560454040c01100340c002600c0d080e5214070861035a4005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 809085305 1250 809084055 809084099
    0x41a2203020a020906090c0403080906042103022a0d110402270d2f060307030609150f0b09060c0a052401060e04020919180e03031501030510 62
    0x4a4070360811132811802040e0009070a89021082c3e1500c1402c3c03140c584036034040500506004140c5603801d6482008407405028603244020400910188904540d04207200031070160084e68a0124100360408640d0f50300b0307001da0a0b10085145039030501450240e208001c0d50080411800c8156685131400145201c1404070300c02c94009070700e0301c00d07000401c40100ba8948107809001d65240803402844004882502c0f440b1b0242c0a0480500040c0c11140c04160454002c0c1c004020804c0c482d406600c82030840346501000d005103501c5115a00c0c88090600441e401d910340220140080e08941c030160415200c080c080516203511608107a152800f44c9100321010f81c041000212110024801d40085912a94078803040c0d506044003e000b070300408030194000d5a0200e644100355a54984034001101100064407609448090b0f81c60307034007049400080c00c941040b15012440400004030ba2003400d04552207030103500044011400340c40040c4c138410701c440c1c101001260070302400b0b00c2804d84100c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 809086555 1250 809085305 809085313
    0x3240603081e0f1e070c090609060510090e070c02031b100912080702040f150f050f0102120f070c09090b06040501261906150b03041a220302 62
    0x940050b55410700ca04504a00450760300b8400c001514581d402074503240359840c4004030106004211807080d0340100080500320b00d200200000c1c1c501d00d00da000b1025294401d5080c011551140144004c406100006400044409904010300e11220920b01c5d00f042c000d03d404a0303191000c3c0c002034502800085610400b19404c4804151841c0101ca482d58035900340c10314604440c6002c074240c1d101115024003401c030a030005062011036032035030722070103180401c80010482c50505240d4089010340b140119041c1000d1001c020400e0f140c904c0d0040b0511505900070400708aa072014030702150040d815036400780340706100b560005034804000b40082c040d04940000c14002505143c1c060b02000380030680154030300001480041210071001c50b0321142c0c055100881c14500c0300c41842c20b800e00207102e04c02004049a40e007001241c2d081482000c0340f003055090419201c8010203040d110641d401064881e41540080e0f000c8000d01d500d5038040078444140749558000d40c003800144454071401c50060304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 809087805 1250 809086555 809086567
    0x1202130906060903120f0216060c1a01080c0f0f060c15060d0209040201030c02100507090503060f010806160c0501020403030509090a0b0f040e160905070807020f070324060308 77
    0x10403489080c0040000e890403c11031480d6484902e00a40000044020440c031b6013070444500e40204403c2c03040046800c412251207a640c0d80c000d00071001c100c0704513540d00c405400d41103020503004d01141a6107208000c3c007054464a42000700c20042100c2d082d40180484603811010342d100d0000e0070800ca548009410550f44461180b0070240c0000e0800788600c282008000243e10b40405165020340d0a080000382100d14010985c070f05500b0081840c2980e0405d0204092268065010022580e040d0119285a15106500d9100300400d0242400d41c3c0e0000c00000c0145050300701000f00011a828101002c0b0701ca80c65a40c00e980c021340056012034800100e01c5618181580c506901045082c001c121005001c0300040106402500540c4690b031500002c1c496610700b40f101c035502c54039000540c1710340380e5110710410203050219100340102c2e20100004000e640007044100300f901100015040141c210b50b500b000f60341d010a59407141ea6032162401d001f106042c81070720040d5000304882c41e04c0d45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 809089055 1250 809087805 809087819
    0x1106070509130603080d020a030b09010b04052b0305030c192006040c03030806040e061503060906100603050705090907020f060606040302011707020a0b0a0209010201110316030507120213 82
    0xc44201c1c03007145491800300f04101250101040d2640003001680c0965140e070501401c40140a0071512607600c0807a0030000a041c5d036511004108907801a6515201c05038240042c80c4000442c242c01180c4240c110b0783d42002074850f9004550108200142038101942d160011940002c50043c4501149944015010903c0b006021580d19448003004141b07926050f5140ba520048a100c001e0a001904010031070f569150f820079444ad909080803505d0514044c80003003810284110264040c1c001c02010078120321001c2195841094142c007107400c003a1030510101c000303040040059042050600005c229070b0b81c0e0382d01c80c070300607541c1d0744c014810542c2c03645402e420014051326052052004100410043c2d0304412501d0b810303c403944220355280d03250340b426070a014612100031709030421001004248120740d805800c00410a074000c02100b40c0c00010b0b01680d01c8280c500148541c000001001042d00c40d4004035800207162600c0320070b444807525204142e81216032990b120790860175040c8600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 809090305 1250 809089055 809089069
    0xc0307052110090c022a120a0c1d0c090a05121606031e150504180b0c040303121a0a0b07140304140d17120403020105130206090f011106070509 63
    0x80c10352203c00700600c04020801940d168807881e80d542000481d011070044006030300e8400109240054a44240c60212000507900d420364418100c81c0031a11142c0400c030f00342d429002c41401080040707080700b55155001484003d4000c42400c40d40046400408646ca0300c8403034413202b442d03440d10000d002c41d03813007440c01540c5501d1582006c403c00d4506940c0951440c03080000416849124000045680d9144000b2000115581049400c9820141080c402c4040d0101d48420f880c05502c0f00070780d588449140080e1440303a8030014000894600449000e400503a00c41c018802c0c08448101c40c850881020801400352580007149105000ca044000c1c4680403540e0440c485e00503001d1864142004612860441e614902da401404108070007400c0150702d25180451400d407500b542e0729255528020105020111011401542084082620804801d0200b29190ba000f05544d0074110b4001c2445a2058000032403410408546401d68401100384450380c0944150f0751800d070749040130030601c022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 809091555 1250 809090305 809090309
    0x602121909210302070501020c06011502010c020a230a11010f020a020d03141201080a031e0c17040902030a0c0f020a031218061d100b06030c0307052110 67
    0x20141800421800641e00462031004000182e5048088041c01c1d03038214000e02894100a06561002a03501d0000800094040c102c8019a000100d0706548a10407400e0720800301c2c01c100541e002901c80c3c00058140e0841c1300022400c071841280407004207501a1804041d0141030711282071608110b41296400341580c118028140020100070140d5400708001590448001d01005080c4082c650000408001c96408484200d1111503550f103668600e41c0b0740260311012801708120f40710904400d6280c20700c1c54801042500c0d000010134042d261a0010100ea4120712100241004046010310040c4082d600540081100107061350007840e0181031340803000d0398030303040d1b601034031002d8006170b80000103002c82d1100e10f10102e803140b40504120100490704000501c0d0904040703000c4c982c5406004076a201c0303078122049408a00d80c08000504552903031030501e402100410000e01d07085207140041d074011200e40b0b400384c42c00400304101400440d10420b01022030b04000c1c10711001d12091002c50f40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 809092805 1250 809091555 809091601
    0x3120c060b06191e17090f0a0c0905010f121103010f1503110102070510050a0207050a0305100c0509030d0809030f040b0406030605031c0c020a051201020a090f031707060207060212 79
    0x22142c082c07080117044a120400070303d440b100d0000c00200741c26030030320034801c8120000b070844000301501d02c0c040d50460b000b0300456280c03e1a000c0001100703002d007a07961045804c54580980c0c105525120048052144003140d6007641d00c400c101501d503401c1d48070301d90520604081040e15036080d13280140400050b042040e04561102c88103006554603940d80c40300001d5242440c0399502d07540031040e8100843c50f07212640c8081d00d04000010300c180440c06452903154400b0410410398a80300542c1ca0780261046540c069022100c056411809500b441303401c618104102e900303000b030309040c40c01958429041350b030783c425010404010450f09801000c002e0078084001d021344510041d18402c04800c80405413040100140000e015034407204081c8016140c05480800300500114015010b584502340c1b000000b507020f100002d001d901d465840d130507268841c241f1700c0070514010100c1160741080c0402d88459500704988000100c6500c0181150f00b10030010311800e191005080c0e0090061841d624 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 809094055 1250 809092805 809092847
    0xe0d1112071e05100912180b0a120e0d0c0302060901060506090904110d0302010b0f06040806010e1b04080705040b18060909010f020301080c100903120c060b0619 71
    0x900240308401164414036800b42400c040e403100f41842032401401c50010422030303181603100c205102c081c20f006080c900481d12100921f04c0c03145c0c6101c04082d00ca2141c10003840c014083c8182441c8200c0035031840c1c0000038804208040c001200c1418243c40c00030f59004500300d21000d00c1016014070820b58840c2d0700200030000d251400c00800c000c1d01c50742a10701e1103810b0f090300107810030800e04107110070b03004e01603c0c00e0041d40c054a13001e8003c2614a25161094601035a1301206150101c121800e0700c41d40f00141c03105910346000500220405040404000708007151681c4180264011303000600740f84000b418000e2800c024442112131209810307008041f03e800421101c1501e901140d00500195124000e030754952005c0c500402a00b81c000c080d00d40000300005801000150121050344110b68010740b1040000c0b080e00c0c492902c0c40001c0481003681c0c084119107009428020600e4004d0f140403d403881d9030b00010f910395000180d00c23510350303543c10140e050840e4020740140008020000c61 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 809095305 1250 809094055 809094067
    0x3090a0e0702070521010216060b0a0b070f14030a031406100c020f210a1a10091e05010b0c100c141c0203040c03110a03030807120e0d1112 61
    0x2903d625881c01914041c10a9104504140e003680b4081000003600d0383c003c644881c4103040c41d13070305200c00b882d09645490802da0740e01542e10300300c4c00340000c8904404802d40741401c159101032181003000e0b002e68480b0352100ba080442c1100303100410140c0140c0d40d0004018000204452140d0f00c09408240144000c04294401da604081840150b0760100d4580241061440c001041e1021030511031261402c410380301403000600150100183d480740c1810346c10b45180103040c00d0118070031078405188403561070782004003050940c001046003451550302008103500800c050281c41003a84152a500800940414408014020001548808841406051001c4800800d10b000e0031f20703140000f81000034a0703034405112100001c000040300405649904d02410080e8103c4041c0c401587d05802c40d0802c0701040c60058480826250b041c2c40315805921140422900d1142d440340c80d207006565000c2e40041002c0420509100d01019034483d40d55000c84e810702c43c00c0140004901a5211081c0304c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 809096555 1250 809095305 809095307
    0xc1214070303120e120a0c030215060603061002031603050a0f0e130b06090301090813060516110f0909010b0f0411190203130609030201032405100210060803090a0e07 73
    0x108240c03c907000404030701105451452800c0100240b10200d04103000500d040b40700b82c00040e080c2e80c5a00035026521058100410008080f90031960aa4849000c000041c3c442c0351013034000149000602c11203080c204c0c1208401c54241b94150b041c0c0100b14042408910b10354003858111440a080c07414243c000100030225070040c40d91003400964544603400c5824948400c41039428540004000b4420042517003029482d41d8402a010348035041003c00100c8c407240640c0448010312130b524401c0c5841e8045407111103c9003020141660320405a5078050083d03030b5041c01d001d005403500030000603c801d4103010031140b0b016503c043d900850030103038880b00c08450701003590118403e4100154424150310700803030443c814a03800c0d1402079445140800c030680d00400c3c80064034402e890404c0301500300440116407a41501d500200305050071010310050406510501c28200c0c2801103038030051300002200305072009500000b285a00110f0f050440d40b41001803440102001413403004e850410b444 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 809097805 1250 809096555 809096567
    0x180825091e360c06051312020120060121020108040210020a02220c05090d110105040803040b1908010509070809162304060803071403070c1214070303 66
    0x640300e00181d0301c0480100400c480c01c8040250440b40a0078952440018003100048804000981d0030318000d20001c111140150100e4050f840220703180b189240c9042c3e2407010100c4124003c81c100300d0b006c0c1800c500c000308020000c00c0700d85070b44054034a541c10300300c8200741c0407000804001e005600c8504140943d812162040e04a40c0503168068900d80110040e460808242c20003500184001002c248111a2903826084400030003018008101c102030216500e004d07500e44c142c0d001e41d0717103840d1700d00040a06046504800060404e64145940c0d24100340c20354225508c4202034100c00140c100f2510210345016403024480e003080034103541000041070041600a010500b44a2040003107420040200580c000320343d00c0c01d44d141c07429a1190384011f020780d8440740e9008000c100b004041c0b0240f4290080b0002d80300c000c0021400e141035619000510306100d0080c03403083c0010018503010403901040e880c0546120b00c10940c24009e00d10b0808030710441c6c2c0400c036503c2d4203c50001c0c4002070b4006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 809099055 1250 809097805 809097851
    0x90108160c0813080f071409040b0a0b010210150608060d1707061506030e0f06190b01180815160e12101a101e18082509 53
    0x151602c034048010650600c8209800c02c134034610456103005000c80c8009150000e80785607400f1030034040481414414029016a001401554081c0001c1d0b820200d03688010b4044c1c005104039032040d240762440c04104c0f5645404002c1000340c21009004440c0c100c400a60806c0c03064400141081041e100c0c5c0603044104100100035280000e01001030018070f80102d4600c0c0104420040c8503070f980c80010300207122000310300700907010301e00031400c05001c042285441052056a583c0c1000c402c076141200500d2140300c641c0c18000c860108081d184610400500900381d868000c020160710404d503c0950380b80101401c814085422141c2d1040354002c0c0d8039000d0103001c3d900341d05000e0151082c5414a917002103140e10081c5008008070700071101d544401d02941c8103403450808074804520464468036000c0c1030208403080c52003210011445010b00842c261280306424464a4682d884582060b0310230280d4848190000d06200e45012608004001001c0301141080100303141003801d100002e0320 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 809100305 1250 809099055 809099063
    0x307080d050903031308070e13150c091a0a0216060f03050a09051b150c06040b040c0e10090f06180e01060f090f050105040c02150406020904050c090108160c 69
    0x4030b8690466181082581c8090325100c0080e04202e0703c94030303995a15a100c2c0b00c0c4a4402c038003640801d103243c2510100103803031034200c054aa9230300d060840c010040d01c9484404410001a0b09000805140c0380680c4502040b0540c0c02c00c0c3d85405a910091400b80d01c8200306600c0308030100b0030449250092a00c0500c04242d040c0481c0130703510002010001c19112034041c9c9140a06072000249005c011407084450104444d4440190003c800507001d502034000903074001c3d44800d000c9001300d11030104035640580708110409080b92103414030b01e0081c0d0103441c41c00c00d05000940600c0500d409008407294030069007410002c441c038201c1c0065204d680701e4000b0941655504410500755001c1d04900040c01134006031107207881e40e485803007008042e400215007400e803900d80007290601e405c0c000e02c88840980e500a02c00c118400b01801c040000182089565650810984001c0d03240c038050742e44074620f1007a400c0c2c1c0360302013880090203e24008003031382540100d0040c04080030790026500d00034a070308 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 809101555 1250 809100305 809100307
    0x191806030c020a0807060219080105030c04051f080a05060601051201140d0803010f061803030c24090f05011409030415180905040203120c0c09150d0b070e0307080d05 73
    0x107803805a052501c3d11101401040e400141c3c401800020b40050075107448c20428900c082c1140382084405440038050564150000c01440340c40e850183c0181d9000642100144042405c0c820b00c0030b030b007c020f540505026005201031200b0311400340640d0394002000c0c2021480e2142c10011006c2010050282c005034241c0754000c81e070192a9130400031552903000318401da40e545c6480300c0382f000710f42511544001401380d20420880c0d10007048650304407640b584078483c0418159440b815009980ca503600c0f62008500120f000d400898026243d07854000e03a202004030000c0c0c14480e0940b409400644c104009000500c80306460000464086850815060b22090544881101c02d000324210201da41070b4019404941d07422254002809a40b00f1400c0f20301c180d5040b60390824a000e8840c11460035006000010880e09060942f06d5000010340f440210301e40800d800030701408040388080e2403100000c3c00b003000b01600715040c0700003448210010080240780041d15581c3c1c6c0300700300402c410040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 809102805 1250 809101555 809101571
    0x10801090c0e040c0306150509060d110f03040b180303040308010611010f1514104802010801060c0c360e10020a0806040e19050319180603 61
    0xb10904030401030780002401030102c03030482d41d0000e020b051036001c0c20041e141c208100c48002ca000740700312070f0690380c007030100b40c02c0c55a00412030000301002c0040703100c841c9080191034040e0001100039489207201d1142d1066900380240601090380c1014038130b41484d84208148400309421082d02c50461b051841d00d118040e121003403541c050301340c52080c160482d0410700e4160340c41a03020b901e0340580d2140c44000e80f01c1e504803010031000c42c46002504021506400500b15101d10b510640300c0d2548111046540381c09042402c0c81140d102c2800d606000074108850030f0840d0383c001440f600402d1103107442c10195503642c45225116585100b0503242ca031241c1309401d024503c003a41c418041ca211807189003a47e1316040200054140c00b03a4800b080d01500310806410f509900c2641c502403141c0d40c64403083c0d6242024000103106154002010307115100314482074030a04954000524420405140c890105002146403100307004403020511600340400218015004190401c44e0040e25012032003034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 809104055 1250 809102805 809102807
    0x503070614010302060904051815060f0405010b0f030405190501021e030601050a0c0203010f05010f03031418130902060a0314060f030a02011d061b06100506040603200301080a20010801090c 83
    0x4140400b9050f290003a881c0120500104d250348912030540cd980050284990008020444009004205100c0801c3c000100d6041c0c0740c40103503520920a5081701c0f03002c081c081482c0b03601512080c080302c081e074002403414000c0f0220804111000103c1240a08604240b00061715601841e0f03001020004405806025940d09402119104c1264402044103503103c58424485841b103010513404241800a4000151440b100302c2e101c00008285001c0d8000052081080080e13030200f039034840c40d441e500039801503a50003005044150451b20001021002c542d104c4124000040c10b56110390b1501a0020b513a80340464071f81c56107542460030b074103115000409000c240c42102007080e003080c0c02041d10b51440078208820b000c810300003011103409503104601c1020402440c0038070f507000141032000f0404039002e60884c1418101d40304c03a140e00c000c0b0036225004141c000f640800e01503400001100c05005004032040d549160610742d22200b01c103401c00103040d400040c070a664500c3e03920f1403159801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 809105305 1250 809104055 809104081
    0x30803060616120f0813020d0b060102030c0106060908151b030603030d0c08040c210219120812010806013008030a0b01020c0d150b0604030f050307061401030206090405 74
    0xb60340003c400460fa550b8040042c51500300c1280e00c80460741900c0800c00207903907071108001c9150b0080c416204464255503042500300081d195605511003840712010560b0203018550151441c0e40e240508280303021005440e0080320410b0000200c4410144052501110402a0511688211195030f0746030b80c00460720714842c4440c0f20010900c0d0054030026a0741c407128841c0030300e004440201e045030710344c1e0b8410100300030185400c3c14110980c00032001400c059980300110f400c80220b04d4211566074180c100084604c4400301c0700610001902401c0c052641121400340030f09400900c0300d503040c150030340940c190b052891152003002d01c60100581c5182c144580d00b4580c001103da44901307007280142c02621070648600d02500034000450010309001400c07800c030707540041000076511914181c44c1c00800c046004160003440410010002c0b401254002d00c0e102e00c940010742ea0b510301c40c00e140048641c203140305600c14100c0801080565181c0d0195003030903108480010311912150000d100c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 809106555 1250 809105305 809105347
    0xc0f040305150402090a050702100f0209150301081e120c03091320160809030c0616140102040617090c040608010e060c160308090a02030601031211070308030606 71
    0x89807007500c1100840d100c07882441030255201780c8040c981a02c03500c10354404e42c1c80440b24100180e0001d2000d4125039401c0e002440005443c220041c41c010344080421760040c160b05034048020800001005507850030490b0394402d0108004254898501c8040e20342c0303c00480e90209448240400c0310b0404c410140304030340271100000d00c102c00c40041400440003604980300071200d00301c0c400c0a422025880d5a080341c2040d0402c94040c04403019039035540c0042e420018070140c0501c50750124444546036a402040c031080c140740d015140c40e031640380904103c0e041031f02c5288180d005110801010390894071a2960618441d01000c817503941403e42480c0038816040903a200d03041510010701400194001640301d00c03124107440082d664501008424403904507108580d03440d0142800c003107407003606c00941080c14502500e014000c941c0000b8a0958203800a035414200480010340207074100740e003203032540c1d0141e000d0071030319203581c43e5000c0303034080140803a000b00030009030342d4940c68501c986105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 809107805 1250 809106555 809106563
    0x11070603091110020a0b040629030d080c161a070c0c0602210307020124050a050d0c14010203040801110d0c080402130e0c0d200a0f050f01112506050f030c0f0403 71
    0x1514800c0b200351012100001c0c64918020f02580c64180040ce118410041c80342d10401281440d141d07507000440d240000c240801d40d620f541d0051020608002d0000d554011101c40c0da425141ca401800c6c003e0b1150003d9000ad001e5501c110841c084503821001100c503041c840c3c0400540782d68883e030003a40901034000c3c1e10303084201c1d112254001c1c1c0084039081c0040d500b0070b6524480440d2640248010401c08910240010030459000c01c091803075020190810f040600c1940d0406035141c40c52800d4800b19600042210008144101108241c1c81400500d5520f481d011103e810907070081a06041e98401480501b0f843e80000c500d803c00030000c3c0b208441c1c0180170001060524100840e0094815003161100c08641c40c0101141c078003244c601c416a1546412260f1480c60442080755001030303082c1c20b41c140900c049c9000f80306141403164000707601180c0661840c013403070542140107450b030b250042c0f8203101040c40b010001d03200e00001d5a9002e0211046070f81d0300c140c201c48003441e500039940018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 809109055 1250 809107805 809107841
    0xf08090609090f0901050709060e1e0901030305190302070f1b0f060305090709050402130b041e09021003111b03040801060b040602010501150806060a11070603091110020a0b0406 78
    0x24154008032003c5200d000004000c0020ba161003604581600e014031620700042e00340b00000d015841c003010f00c1c0803015402e60000c0c2000d4000d002003282104241e100760702040010400d603106461404004200802c41d1508510b0415659241642d070040c60801174511583e0305000001030040c80c0c08200500b00b41d0546050013a80d0300f2004018203001c580100d070320b0040d031000290001050154502031036004042d41d10b41680591030000800444001c9030340b0a440f044034002220003015892102e6100140c01308183c0300500501c490140300c030b44400c040615150120030050125800d4031100190380b0b040442c07035142510401d20318095030304890920751034010b000880c00348003001041101c189400034400c980c1d0301d05c040c030760761103800c0c11900203e49150f0000e0b17171602d003440c000c080d10b143d141071010b82000300841c83d03032070141542c02040102e0f585080d80b07014400d801d02416008107048032444c00050011a0094548110080091040088a000c0350420100360408444094000004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 809110305 1250 809109055 809109061
    0x705151c0218270711011401140103051501051e070203030f0307090e0601050f03060301020d090809030c0d0507060f1b030207050a08150c0c01180804030c0f030f0809060909 76
    0x7840b50050303506201807068001965030114102881803400344030060b6101c1694683c0c030b0200981d00c2d413201404920881d56500c0f080600c0740908071186021301000b51b000c0301e02c00358a4002500702c4101a1890700030f2303103640381c00d00000c1ea484022a0075900d10030141d241c03039140064196020b801401d0f4001c6d418040411051001403401c0e015500c40c01d410f035034070501c0c0c6030f0f80c3c0700503802c509041d034506000650400400c070704802104021500304c000940010319202000c9000400c0300d03403d040c116591440040d050030303d071030204580c0078a01000c455240e1000d06640c3d031780c0e030f07501c1c81440b64009002d0048100e040e00c0e402000c03203a035424440d00c00c001c0c600c4840c0c68025100c070b1042c0102071003104400b001055038100060301403004602048000d145446d03035030000c0f02940084a0000340d80d920364214a22501600144000880c4038030301c0d0320380326410f41c17811204240158000a0000c04929801c00209001e40c05003045107420281c496035482041c00840c000c1d100350310390f442d003011810040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 809111555 1250 809110305 809110327
    0xc070308040b0d1506051210080d020f0d0203040501170a2309103308030f120915010311190602150f070c111201111b0705151c02 57
    0x3000f81440380802080102884501e441105001780140d4001030b4041c000d0000d141c014005d003542041131104406003580d82c903000c81c2e00c2c1601a410034001600410360185189601b00305603400d0b001e540c0042c6041c5810440000d00700c0d00c6a0716111a0003900c0c2c004a405118181e0211201c200d03840c05508055a13241881c0403089402d07603a280b03d0340b007806d1201101c0f904511500e0510400441030348050104100a0002c000b158009488941003041000401c80c03001c000414840342d110b11b060340c44461030400110f00f4000100b80030016044259200502e00441c101181074950103140e80301c03c05082e00110342045005051f032040c136000d02a01141560300040d200904a800c0d00e820380f00c2c1d0f5240e45681c145203a082d903030a808030b0092040c82d0300052550014041ea0b0001074840b1007010340c1180981e096440c1080c2000c821000003c82d40b80e0412020b01c23003200d124a05c401400c1261420000c00c01c200020403900a03003400218084043c180c01030562105145984419074a4a44041e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 809112805 1250 809111555 809111557
    0xd03020d090501090e0f04030e030105090c031501030210110a12031b0c0c0501030f020c010c08010f15080c070f0506150f041413151103101410050c070308040b 70
    0x49203402240000030009034540c82044003c0c180ca0f040c082c403001030b81340c072021068189000f50040f414403e05004031815500e092040ca44180c00f150001c080c1c0440d070000703050810004c03202c1d0014655080f00140301507152980b20780e8a1800500d0420304541402c0d00d0f03681021220140104001c003c444000d40701640758000d8000d1140030303048400c041d1152035041e20902c881c0c02c4010101d80318038030700f00215030080e409003011440401015250018a1400d94212240c2049400205400d58010710681c0d4450f8a03400c041c0403c094510b55504501720090843d200080100001d24800241c3c50100b00c01c0301c0f10440b00c2940300c07049401c2400d01c41c080300c281807548003409015a1040031650814a814090302d51040300d0307143c0720701c1c49031144548641948010002a02c07103142e03440f0101882500781c0b149900b000741401d212602d900f4035040b40c1070440099400f1008595100500e252550307120400d21903055210306000740d40c2c0e00120703101070625043e03a1001e899408080340006402c851a8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 809114055 1250 809112805 809112823
    0x19022b030f0810030b07200714061c15080604060e21071101030908040311131b0c05070803180f01020303091906020f16020f0f06070314090d0302 64
    0x24035a0101c10160729002c484080086860030340060050340104045401080c40c290020300d036203400807641140030a28004000204007034002984400c80400007410418480943c40301c003101c6040c038010500505075030101005c800b8180d4113035036010080d04e600d441d002d0030006100a006a45580c50542030040092841803070000c43d60190003400464a0b000000140d445101c00b036446051034959184c580041c0711425080703043c0740d81c40c050309000c1416200a000158070800c1080c552207040c0044c062001c7c0016080d640316800d02c0385e034001d4600c2801c12446e46090034038052000c4059401c0451410001c0e80c0300354201d01000420054845604529030120304059480c40710240c01d0340300490362444101c5044070320f80c20001501d140e0000125200d400759008220142c00e252201c0c00c40c01e1654070007a000840c0c42c441d125640d0031414034840703660340c8240494030b030941a10a940402c5c1ca070b12440300c000b0304201c150740801c881000848140c1d031008402500c1c814241c0500d02e40655181081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 809115305 1250 809114055 809114057
    0xb0d031101140702070308130302060f130902040b03221b0305120a0e010c14010c0806040e0c13090201030e0a230d09050d060f14011a090319022b03 65
    0x1241885001041c0d03145003e004500d9a4001c20f0300b10300d1500c42d00d0707444d013100010203400d00c1c41910010150b5125000ba001050516101d596a0200c000000b02424002e41c401c0409500500c01040031b03001000c1501d80c00115030f03034010740d941c01594142c4216080200e004007540a41202d071044100381c0074002d41541c2c4100103c1c1c030384100d13100e0030b102030303000d0b4086400000d0240d11010740c10703500c11200f00d142c0d00d100b0350303125403403050400141c0e0944845590783e10000b2991001c10500d03140030700034200c20005090180080041d080041448602c030002104400d981741c6c1c807078030110b9129600010008251405946c14400d0b54076000c21400515000c50442c1c6600b100a140b4080c004540c9003031688058680061492500e0240700c8020344c2001e05807030780382d510188103002407681c1c058030045c00c03035059111800d5818440f010492501e0540d009900715014000313040c040c0c80c0019100c0c200c440c041004908000540b001954030420b90030003111407240d401444043d400d40199a900746842 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 809116555 1250 809115305 809115311
    0x10e012f0f01020f0901180b070506071214040602090105040e040f0311030c15040c090c020706020f07080c120715030b010f0e01020d11070f0f0305010b0109031709040b0d031101 78
    0x710180c00c0d400c2c1c2c01074080040ca29441048101111b6000d00340e0f180001c40d40d0ba40e0403649a550780e8069815811000c0141c03040d81021080000c3c1d280e00039103440050481500421844583d0780043c4400d9900600052105600040d10301080e80660103841c000d000d5000d5030b000c1440e05280c00451716110311000c6001c070307021380c903042041301020043c0c852807000f000003030219405002c0107084280f4050800d0b24041210b4101185138603c90041c0303d0400101d03001040e1031841c1c400300904d40110714000400d40e8010304800d1101d40b10114424080c11812501e0751610051030005030f081041c240c1c0000042070282ca1400401c0d41c05401819015001b41c903030340c43d8520310309825581044101061801604117030340009805020f540b80b40d603040c0465003103600d082d489819140080307096800520543d00211000c01c1041000d003c0d2030310302c940a203000800c1628540c3e500401030300425503007080c1e00011490705400c1d1a2036001100c80d4000034410b1a02c0c405074240904041c1e80d8902d00ca0301c03035007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 809117805 1250 809116555 809116573
    0x10060603021c060810090f0b2406041d04081216080105060a1e020a05190507140d080f0d021303150c0e0d0c0f0b04170d0e010e012f 58
    0x40d0f8880c039000c030303200e000143c1040f10104040200800f414102191900c80c6800c4c080302044880a1380c80c03164051300145051054145582c0110402144219104030380c100018410b448140c4081c03100242945d41341c04103921145000c000743c0c00344e041d10400082c001c01c100030000c2e1104018003145129500c1e805400d0340c8031424020b082c4100c06620010a14254440641e0556070340c00c5030035110070b40b060340d400641c181d075001e00304441c081c1c1d072a40941d000c0c5011401d01c40103002e030710000d160444038410000030703210110782b026901c684003401460f00400d14a250141000490301034140c1e80104642d01e008010320718104401e50300040e10000b8508851103500200d502c81c2000715403032610b851800c03c05c0e4400b04120125044c20403110115090780010302108840300f140040d01c50f072801d02e512541890660b5070035401e14001c2c82c1256000c1c40c4d0007211076802860600401c4002e28101205c8010030340148d445041050f0300303c2e0b60400c481c0c0441c0300c5949036155164402944416161042 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 809119055 1250 809117805 809117857
    0x51212160c030c030e1801180621170301060203030a0e0a0224040504020c0c03010e0a0b0604020f090d050a0c090b0603060f120a151404231006060302 66
    0x10038000e4820200305052103800110340180000241c42c1d00c030b1300e0920840109040071803e8168000200020501c80c03200610006081000c0c000c0c1c4548800000c00c6001c1ca00030240d01c0002c0024480203142c06114205803d011007140d24003910300380900b5107503403540d4400000307590b5070007140c0000e5034900d4050018800e000c00704540c13500c0e40e00184104842080d0502c03c011a00c4c8050420045500420000a04d61a640098402140494050310300c03810000b040c0347c2922006024806160000c41107440010814045503070440015900181c44000c000042410f034412540382d00c1e4804502840744041040014102c0c5c0c00031302c60034190041d81e50301e80d01d841c281c482c445000b41c1e0041c4180001a15401c0c542008114940300400640010b0030114805d400e00120b46402d607440015106280c54105003030041065000300444240d680c0d00d0107441d9810301e02d00082c2c0d469041c0e0340c03568410b5a118402c102c1940303221030850342000b2003552048040c00a602507803589804011420b500d220072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 809120305 1250 809119055 809119081
    0xe0f060f16052701020f0a060203040b10050a1403010902040e03030703060602030307020705010302210f090d0c0206070201030906110a0908010b03030c031209030d0f020a02100c020d0f0c051212 85
    0x321000d480800c242104a146203244200303c0c25070451003030700b03001c2c00002c0041000d82c07c1f440c0900001070f52410203003030501d07640400502200d03010031600001c10480d120804914201d900003c40c0303180340605680020301603c94444c020394420304000c800b2400490100056006020795142085080c0c1d03502016a281e000807a400000361300480070070402ca500070380041030002c07081c080c140780113040d0700e0f8049880d01082d02d581c1041d107414420480109030820450420400c1820702079800807140d40056030074407a0b400020b040640fa821003108102c01500001803420740c3c20a4151a219110001813020005200303508844d03082c030009030300605010045590085500016514103000000c20308402c0d800170b4a500510710041250111040d02d521480942c814006005695000c4180c802861f10141611441605140c5900c032510a0b4000612502e0031846050440505080c0c0a09856041410b400540310703009003031440e6000c2c50120002c1c4602609003011a203c0e84500b4441d41803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 809121555 1250 809120305 809120317
    0x1c0510060806010e06130f060906030203040b06130b03060f150a050303040b031807060203090906010f1710120b01032105031b0c010c0306150e0609040e0f060f1605 72
    0x100d801c00011810a52080302c00040407900a441589001445284014004e441d640490040c82c80d00d00b0034003c0c5035000c0c1c0701000904040c40d0550440c101900c032600c000a01810040c4919060504600314807059000180d500b00001c007650b11070b10f8000300071903401000f158001d04410001d03e040002d0314100c45060b00b03455018005608040c14070721590005c3d03101034480c000340d682c061050708120004202c91000740081c1d07030146d41c4810111051103d540006400503050091006520445a42c0f11884003a40c801e4042c610096466080e0200e00445668010744515408220130b1030900001c40c0100713040382e01c9407030351302003100c11203d03024640656500003030009103040021841e031002d180da08000501a0303140c140c2c940011f40c00031034212100d000350440803e8271800200208580d440760310a105c40c06007400000d91b0440030009002e4443c9009280c07095650301c5104c0000e01c1c0c200840725580784d01c8000c45007141030840b900c60790000c00301c500001a60580390a450814031407815914 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 809122805 1250 809121555 809121557
    0x402091b030c0a05121e0c1c09061104060305010e010603060e04030e1519030b030c0312070c0e18120a080a0e0c04020414130209150d0902061c051006 66
    0x8115203480900c0010703680580c0d2054204502882441400c6422a407014002c065103040020104100303400702ea0b032008000c184a20401c0f0a000150150001e0440c012145000440015009e0403d02d0010300800d580b00507117420f04404200030440d1a09588003e050300c1444550180d903070b0f0f07164011826200d0700e0003030050074109000031400003400741602c00d80c0d81c10010011081a007002070140c1d82034209650144820706144121465a6003611030002601c0081d030241541344000b00100741d079003c094142e00110180000c02c0000d201d00d244034030010f0103c0b20800d4905060655018403c82c2c40070a42280a00900d03d4006001d506041265103d0b286a210284039684028034180117005481400c13001d8015100381784100d5440b44000c10250010b0010f80c0310b422450014010f8200d50a08624180c0e44100450081e503a21200188500424141c5060361107141d26039500140c481c694009401401c04500440301e0341c100941d440c2d544020600c20842c42c0c2c5c92442c0003c2d410740b10320840c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 809124055 1250 809122805 809122807
    0xc020c0906030706180b36031e150c040602060a14040f0f050d111e060a1e0903030f141302040b031204090b0f010504060504150c050a06050402091b 65
    0x800c2c1e81c0a000113000d0490249a0171401d941d454000e481c40382d01003c80400b0101c0e410001070710400c081d00040140c0d05400d120036106580d0040401c0e9200c01941c000d681285105020300200303401040101c0000300b100c4200c2d0103604020626081581244c001e0038054040e2a0014012215070b01c190015041c65601200c1c1c0ea4503151203041050803091800c0d61030b8015100b084000c1101009402e005241c175507142000041c22118081c00d020307100520074816415400d02214004000560700d03044450103c0001d04031060410b45001018043d450602c1c050801c034011040c5501540041d4009012140502200d041c5909201e03049404441181c4406814a500c20149c03c096025014295018084896584905000c0102900306034400c131503641e202d500e8010799040045040a85c2d150a0812608083c140170000d006402140a45c420b48991502c0c0018514807030703c1d4150704150010142d0703030300048608100e80540b0048500380c4c010107542000c0360f804070201e840158031103010740c000c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 809125305 1250 809124055 809124059
    0x21b15011d06130b0d0c03060e0a02030a15150f0806010911180604120506011412280b0a0209090105030c060d02090604030506160e1f0513030b01090c020c09060307 72
    0x280fa4040900506580d160302c0d0680e60f80b6004d2801d8102e9004000711040c039890f524040d42a1220000340035803e8100b0900c0d0700058800182c800300d80c562200102c2550541103e202004014080307540c1d00b180d44c070900004001d450f00c8642002da800d00d106891450707032502401001d503002e2224a041c179070003c025190444156030480403214200429007032505030307079070803410401402840640e07654009500420a00d502c01d058280a070743d090740c0040051101d1070301180c42c0c0800b2020420a00840d0b030001002d50030721100c1603481584444540c02030306145500c10000d40091200754003034920342c00089000d26001607044541c1100800e428502811008000065003090548a400c81ea040c480440058000c3c00084c0c401c3c0d00f00c0400403d02a91000e009108120909142d4050022241c0260f2244201e1094a00100207824501d5980120440001c00055650710103082540c2040010496110b89c1d00150f42c610065821030b030300141c58008000e480310302a11081d50603480b030082 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 809126555 1250 809125305 809125309
    0xa080306060318070b04061b0206090907090e0a090b06181501020106030c0303030b150f0406080402180412021608030412080d0f0204050a081c080a021b15011d06 71
    0x95501040000020707800d01c3d40310240e01d2400150342c110050602c808101032040c1c540c058000340510002036100d01521200d60042040d83c032420045500030146900000d080c1801440154000d00480011920615044941c1001010380140842d50b6412610203d1103c0c900b4800f07841410308400024841e6440701c003440592459024180d50655481f00790000100b852916003400850083e00c020640c00b48250030880415141c0e0040c01700f110041c8001c200600c409400d44040d5551070801000940f240d000181c0a02400c01514014010010800081015500071214079095030707001c66010a410380b42c484d910f202c0d24021034006500611003080b103074040b456031142081c064590a032409404255402c1912000c2c69004a07080e00080c04108605103843d2140091817104007401c440d4141403a202000c0588942c4041000010f1011900a40503681145c0d42c98610060b4032003200700745c44140d900d6001b81c880c0003d0150f50340f40002807218401c4a0008030200302c400f00c070426514402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 809127805 1250 809126555 809126557
    0x2010509060a020d090516030b0610020705102f01051608041707021009080613022202160c03050105060a03030c03081f0e04020f0a05030304030303110d061d07020a08030606 76
    0xa000c0d81503d1711110101e022480c14000c003d0107200503150f0042c000c0c01c40c00e15840348400645014000d4a42c0400046403581c045148802c0e81d070121100711038450204400c840303958980d18440300d007030712007014845503001c8441c24000c10072014009002c6607540100450940800108a1012428180c009400500010384c0244018132241e4890b0415146401096514107800103801c00700d1100b201c18800d9140400c1641d500c0081d00403442c09129895010030101190500c441c0d0441c152069400200810b540549031001e07071414003160000f5140c10701079142451480240e626500c1d1101203050f90401c08012000d5039090b40310b83d600344040b650221103000340104100f44040b00102c07009070303141c0102c1c10303d001482005010401c6081134010041d124261030103d40c42610340110401440c1c401000392002c807034050a00054405404c40300c0003580c401d11000000b0f41e440c1040208000c800c0242034018004120752240c90341d9181c0e00140c0c2c0c2c4054000010b0b044410600000d140d80c90000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 809129055 1250 809127805 809127817
    0xf0910180812160f062c06252c040b120a080714070f031103060403020d030f1107060c1404080303041502161401140c0d022203060f0c02010509060a02 66
    0x110740d10285003480d44800c0100d694000400000b00508203984c0303400030802002ca422501c5000242002e400c104c88034020400711124002c1c081400308c40c0079035040c0c0c0a81f00c4040e01e41c072070020002c1c00c1d170050403c6043c007032074181c0c426202d40e1038000241014200384c0b203250804c0741403e004203403900303003034880040f030303400c403030310031924880281d95030503c0800c20300c801001402d11020407007001d810f5207000034181c0480b06906010ba1310a804100200343e00003080240022181400250241390b210940081e004061051804080c0000c2c10300030032819910090f03800b43d00342d480c070700d030300c400e00360034421900c203d00c140c1c0c505038000d00105001c81c038801e440ac00c086165180041c600500c5c0d06a40d0403003a000041030366401103030380c46000c0790017003802420780080710240f41000d1031030000a10700c0c43d4060140134600715030f030105400407280c400f814842002103104601038400b03a03032440c2c00009002c402090000342414101d40c0c00700307580140681e60299521401800b15a564690118020340010b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 809130305 1250 809129055 809129063
    0x9080d052b090204061508060f01021e060f091f0c030902042901050c06040b04080403080f1e09010c02220c17060306010302060f0f091018081216 64
    0x10000442203840d51074410700e541c1d19912000c1901545401008100c449550060340700d4082000043c5180c2d9002c00300c00c0d406501100d2802e1001c40202c0100c2c035003000d0008511800e2592102c00d12a96400902d1902c91164051003003415034a0001e115250030328030a444640809400c060041e05002d500458809000c500d400a4035402580000d01a08c4010018851b4803014a1044081034542224214009420f00f80301d0300e0320fa01c060b4041d95510006002410070015213011404001030700c1308031001103030820403c43d241c106c03501803001705a006182d1492290401d184085007250240143c0b0391440e416159207480d030500e0707000d01c8003840004030300800085483c1c08201e014452480390542c090b10340d548030030000102c29044608a080a401c00c0c0c807980c066401040140d651400716a104035414074001e0710760042c0ca000c0e50560046502c001d034000c3c0910b00d0b81515551020740114543c40642101501d80c1d5030b14030003610347c5485030719444c0103034041000703055502111030310160091203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 809131555 1250 809130305 809130337
    0x7090207203003190c060506040203090705040e10091b05042309101b0905030c030715050702100c0303050a110f0903030c100209210309010e2101050a0c09080d05 71
    0x404940c4401d52640144c00c18017207445100c81c0d00c1404014452140c1c041c0702568110714500309405280d1b9201d1062007914415902c40a1f0342c45600018000004100d01242d4140034020032490300c2c00407681403c0100c10040b1340460002241c0c90240940724072070b007802001509900c5800c48190b1348200c02441e114440c400d076010000405514403c0606080504414404044e2003460041c0589403e40c029032080d0710211861225950101c1c01104640803400e40c2c55881d1201c80c0140e44034060700001a620140c00c200000c00d00e604941010842c52195a04101580d80d10343c42c101195803146c114005440c1c1070040c0354001c3e03003410003040010b0006003201c0c184452018018500783c00016800c0800e40c011424404604102001e020003507000a0300c0d000e409488407101d075603030080c040c44504008903804140700c0d0f900c445421088200c2203000d40c12038040a00c04050191038244c40b00f00c6840c0c030b05460007450600c6030500f00103907241540608000e007105034040310f59070405e1040e100d004e81 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 809132805 1250 809131555 809131567
    0x23060d0b04230106031e0f05070803120c16080d0204080f010b011808032d0c06040b131110031107030e04060518040209070207090207203003 62
    0x1000361440d600c00d038814200c0c80e1801106082c50035001101c1c1c0030001d45030781000b0b400c1c800a4005e8150303265408118900340078849203411f00580100e100b40010708240207030140418040b074080000c082c080b100c0201d442c00d03601c030303007441c0c80c020b11070201c8800d4011042c80316000042c0c20440201000403c20b040942032a0320b5a04180c141014a1a60b80543e136442e600442d0b156000140a00745881050704851030601c1c00c1d030195144c0c4a40d9081c12002c2e141c1404124240140f4004400c0422441039640e4940003c0500546c0e249403d0321b003520f40c0c1c0c5040c0005080c40031100350f000d48540c0e0015041034801c082509010b10901160300320b0042c9903d40703103611104440c81c3c01402d41e1303a01130781c0d400c03428007252010302c0111030b0140c10460081061084d50031801c0844822940c01950695180409507504407080b030a01c00c0319001015940e00025202d818041d071490300a40240440d12a00b001c41012802c02029030b9035080c004030750386060348000f006000403094440340700c1040000c0d245054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 809134055 1250 809132805 809132813
    0x3030201112107110f01090b090d08011a07062c0d02071a0712020a0308070f0507022211130b03040b07180506030f01060329060918010905041523060d 66
    0x60368140500026907460320204244410380b02c1813074002c827190f07004c0d10b945100c0041c0244403510500905910f8a41c1d40c02031180d000540c01118031650b00580b0400c0807407000c9801da9482940059500280e0004d11007044141102140104050109400910000f454014211101c008030800d10000745020301c094004034a441081096051865015141040103490060101d5102410600030032240c1074078001c420345c11608640e0055011251560b8021100c146030300104c0201040b0781c2c410303080403401d58038041c80d84042c0c40b442c41109c890004250b19405c10f90454001120003419200c80c00c40072401d89800781a0240140e0000d00d040c007000c035100d40100e24594010784200300204142001005065070500ca01d000071408100d0f000020848a034027480d03903102c48000c0912600d000100540180d451440030380c540d20b800c0440d0641e5603543c01404c401000c003117805a8004000110004011010744103100c182c841001040e8001c01208100c11050765005240a402013081072120001c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 809135305 1250 809134055 809134063
    0x12040519030602071a070203040e0103110402310905190e100203010311130b031f060e10030b01080a151107080c0d140a1d06040b0c06010303020111210711 68
    0xe5024a840e11240c41c0c0d130001c20017102d4401401102150400d100030f100c00740309010020f0469400c048484603d08107440094000d00c154100101d403000314170200d411030b040303103031191094005020b07001003a80da4880c10201504c004449050020741c0001051041c0c18103503001c0003844076440c0c1100c0034848191000c8049a0081e002076a41d609881c104202620340100111441140e00c9400e001074030141020030307550700400c4004004003401d07901c01048201142d1001c0c1c01030028100ca001582480300c1504080d0410307000c1a0b40005c1d100002051160000401000456209034440100040500004010042260248034480c0700300001404103036400b02400b00c82ca041c402070a000010f5003030150091001281d5200b01000521982c0c03c0a0f4010403841c0f0a800b040b0701003e81403200c80001081481150080c00707083d140450440c1989400154143c16a882a00200300105501c080304982d400303000f01c50f03040184100f4007120420b800304060340d085007036801c200c00c030b03010000c4e821810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 809136555 1250 809135305 809135317
    0x5070f03020a2f1b0a0909030e372421020405060304080d0b09010b0706090c1a0a030e07050607080a0c080309010225030206010e071202180306070212040519030602 72
    0x1c009012080d4500c0c0385040c1000b00b0003860460801c1002c800c0b0b1342d41c0030700b01c000c55001c0540320b41403800c80b01e801c040c80c00c4084104502d844211180c0ae000700060058140d005000e1610798800c0c0140480c40b040003440018104c5c1500d031188006080c03000c4e101c0040c0000303480448a06902400001047e80310740000d140030318810125a81c9030300f40c5800400031580c4000b60980b14416420040003215000300480308826082480070031b1070412402c0c2207900d042603a000503c0c941803a254900d200008101610b000c180643e8140071140098100030b5642070140100e65024a04214000000f12400028035121403075003010104038409032600f0340e0517042105c20b44100e03500000d0308048036400d10014070741e44803170b4130b0b10190004468500958a40050141c4240c1c1c82c0c10802007044035000d040c06401a03c6d031031805555641c414020140c223460380042482c081d206100114100b50f002003121030013810505101400c0074600404c00c0b100c86900380d01c08000e4094480c1c04004907244d4001010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 809137805 1250 809136555 809136583
    0x111b03070c0e190f0219090b0405040b030304030c1706070212120423011e090807020405092b1d030604080d02040f0b0405031608100902040b090a05070f03020a2f 71
    0x2860346d1940280400703040012428408104102c801032140041d9481990141d90040e500014000c0144011a1452003590805401d50790085400501500740f0120f101c40c01030314809a4119031030b4010b00780c1c0d541c101004007060050003489080c007610301e0300e4102540503010700030405e04034403030103082d000d205403042c0000c1c941d0b5104e00c00d402080c1c0c00d41912040381002d00208201500254540b00183e005400000384030f0b58484010880342802000b404440c103118000402035085940c3e2201c24182d1140c01400209171108081451a0080c4800d451003210142c081c06583e5111b07aa11366a40c1d100302e40503104a0350a100101c1ea080301072910b500540540a1016030300d60402040600e8002c3c58200c040a071040680140a113280110790341b65040b16500e0301082e8400c1c4cd00c0050302601c2c5d10281d044c1c0000b2800f08200010455801c518001c0c80243c03181e14503030719207200c100c0591060241ca00085103001603881005215016594070400320128400c180c25000403c281c02c0c1003901d40442 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 809139055 1250 809137805 809137807
    0xc0c0f030f18180b060c070b12060f060d09050118050703060f11164202190e0303090402130806010f030b01060305071101111b03070c0e190f02 63
    0x201d0a0750401c075404052460005010142481c2091040c4805144000c40b06269124000a00c0300d0f142d0200f80d0301c1c001020303020303220000d131141008402d0303800c042400d80e000034031107010604900f0415480381d00710300e02401c81440d040442d4000380161880600c2200c0542d80d4060038408d00e41d107040320080b414030130b0024141052179402c0c030a064032100300301c0340c001c0741c074005020b9005d107a075204848541d220080701d00a0f00d2898103040460301c020042200800d8082070600c45040304c1d000801e0495090210620465100490190200c4c0651030500c60420480060b1402d442e0041c80045000c82c03000701164501401c0402003400d0b030300140180c050f40c202c068014044600144003050141c00c0c001084103403d441c54503400407407541031064000745036854011070481c2e03115a00c070890000c00301009101d10111020042e890398800560503014281c03200306490750740b0000c01103c14032034000508c1c0b02c55034100346643d8000c0c98060b25002e000d1105024140012425014207554042004801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 809140305 1250 809139055 809139077
    0x60a08010608100f0501060203030f071803060e010524240a0917030306031225052a030606040b0d051c0909020a02060c0903010204080f07061808100c0c0f03 69
    0x841600c0c816104d0110060520300144105580041903a9104950300c0340c3d0541c60f01d41c50002c1d1000c540c7c601f4600140903824402006005460308404001000000200095aa40b424494011098107104845404402c1d5800d18a05d00000450601c083e4000c1c0b5114141000401c45036542c8107500c2034000c115482010410000300040b214007a5541501451031031a2041c002501c42c4065042d1904081000c5120700003840004c1180320402403d215801c0403005030b04005603618000502020001032520034240d00100d41c0b40c01c450f01c80d4000e002000c050703d0b03220400019210101143d9004400000004040ba10401c149618020600c44030020181c001c0c3c0d0007000e016a035045805402c0c0108610780070207900007003180d8007655a18410740c44085900c0000c0c068400d80c1d000c8102445414800741e0b01c5000801c01c2000c8600584030712142c012181c104107660300d410712507804a07401824540d40030404d190030403100f100042c40e003221841e1a40c0d0b2008840501540c09600180440000b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 809141555 1250 809140305 809140333
    0x60403030f0e0601180506060f030403200d17010f031e051609050a0b06120a050c09060a09050f030c030a1707080f07050f1603080c010912021c080c040905060a08010608 74
    0x1b078190000c10035903c0500d0081080803611842c4400340005080100610520210243c86501400a03221301001d55203942030a180041903c10303000c01248003c00807030000110b2450f110070f510201c0e43d00c107407010240352625a5410003a0425034050b11070380280000c600101c1455403400c00030b0807840d6800901030802008440407075401e00000383c080d400400115002c4c00c1c0d031204950303101e60000804141a40c03036100e010101d01a00305c400741c1000c004901900003680202d201015140c0654400003481003400406076a00e00c005081c6415401940c0d600021803200a1100c203285003100c001854201140c0d105001179104541c8103140b082d001c2021410000284110600381000794001c12035800c6101002c000764901d440f00510300030300025480c5d100f0f0b45c00e4108030155500a03003140c485007050600a902d03404588040480c1c41440b0191080c1103000304e080a004003840d06070142000c2c1000f99441c01000050074083e807119090304005001d145c00d01850b40074060140c00741c0024220030768 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 809142805 1250 809141555 809141561
    0xc1a1807080304210204140c040302010311030c030c03070c02060703090602060a1415030c091609080109050304050402030703090b0415060906140d0309081903110d02060403030f0e060118 82
    0x1a0142c004010801005010b4141e1800d01c41c0052507000c401c8180b880007400404200c04084034102d801420000140030a6018000b101e0003a00c0522080c981640c0c02c81051204480016080d181030010a03a0400030101451b841380c028204110341d403486400142035500001d10480018040300b201388280381e4140005d0780c02051004003800b440030780da000c00840d041d00074074019600317409140034222961304001a140f0068044c0c841700050814240c1d0a0b5103880308102c03031000c181459000034180205101c1e110103141c0100245081c103003008208006580040c0c0038404154a403042e61000c902c0700e100c114090351144205501942020b0220001d5440a0f802045250300e4042c041004607090840c007008004c00b110419034140c4c0e9449c0a0b82c443e15142c121140311b108610b002c03201000e08180340d900c150300035200d5165881c0038084080d6206101c890713690040e00712501050002e8002e0304405002d4a8120011540c02c141d1107556142003c26408203d41c1340442d01c81e090041c090384 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 809144055 1250 809142805 809142809
    0xf04061103040f080a171906060503070c02101101020d0b100302070206030a0902061210053607030615020303060a061e0503040c12150506041b0c1a1807 67
    0x6110300d411440c0c56180c00d8020140c02d10090245000040c103c102903100d9102202040c4c104a041c08450901d000e881e8081071081030400309031362034510042206070082082d288550751981d10421480015403c1c0200207008542010510650301140820500207001600261f0141c1c80b0008100340c01c0704c100b0103440d000408580c141881000b10f80f0160b00d89108980e480b50a94001044038007491000c030b12140f046130b403c4580021054240400400000b800100321081180c41c281381040501780c1103082c21304054454011070702c032480210a22503001c182c03580301e03d003030400050240e5608010040007404142c94401600b00100704207031032510031074400103800d2514000503403000640d22218008648122a03091081c00300010702040300094115000d00807251004c4038450851400e010144c41e0006000c18482c03d29000a485050600c00c1208040c800400090303811408201a140b2101081041e50b508a050032200d280008441d10f00340104c0c441200b10072554110542141084095 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 809145305 1250 809144055 809144081
    0x90f0b13020a1e020a06110915030106020c0f0a05100e0a120b1e1f03062d0e19020406120309170c0120010207050a0c080d0e06070f0201170f0406 64
    0x10300c0c83c0c83d01e6183e00050100100350f010784005010303180100103e805001360300d11254480f03848103140380e01e15843c00240d41201c00c40d4085a04590781c5004104000b40d01da208503030010f04021040113289001c044030f40101b2824104095000960004030302070140d02d80000307507104e094030740903002c201c80344104541c40314055609031802c0c203000c03162164902010b0614116a000b010702035113450443d4040c00011075010380c041040c4640803114065510080d2803588051000c40c55009415005015400e02d03d407043c405044130001c090490129014851000c1c0c3e049030b922040401c0c4464030500120102c1d01a448902c505440c0401ca1240c2d500c010b9013101c943c3d0003104004c902660451142c1000301003950307403d003c041041000718024080e8200c094540d200f9030206c001400480c031005025541088142d03a00481071550035503035102524502da8000404200c4078000c580040010005244145032a5520580c1e0209507880110300352a00d0003081c080300184800c0110300e102d142019085 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 809146555 1250 809145305 809145347
    0x21308030a0e0306091009080c100f0c0e09010504050a0e01090503040503060c0c1c0525110f01170c120f0702060f060303070201121506090825090f0b13020a 69
    0x805c0000e2915886600c0311110b01940f110354110400c10701c0c409594a22110710100c4420042042d09100600b0b0300a9001ea48a482d220880405038030031102c0781d1a088019101008591070038040c00010400180181c48159440b0a1800c44110a0007200103090140004545990030300c01094181100900421807a05041082c4960705401150078550030210790001d10024890b1802940c07540710b11100041701200324070400d00980d07440b1385200340f00c900a0301e040d10300f01d84150502c9106980d490320140030401c80d84072590b44103003015505503c44103511007141003400080010900800a40c0c031081626400d104100441750304010071507202c5049183d11066092200c003094407449500c50203810000a0282600801c80e184c02002d00c4d114044820900c0d19540c0c07000070720084a40c042c0c0005400ad022031038200c034044054510340c09843c24000c2400500d0003c540c0c0091030f141a0080340161106e4006840d90fa5107101141e41d8040108056910080b01d50010700200e03e4049110f14054 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 809147805 1250 809146555 809146561
    0x106080703061514220f0203041b060305011a0f070b2802030c1b0109050d020c030f0102400b0306040b0a240e10020703030914030d0c06021308030a0e0306 68
    0x140300c4000a002c5c000300003080d210001c03414100780140c60104480c1c640c050001040c0300c200100c0c44040a010f2075240f0f22941010b03145c04080b0b00ba0f800078860b010076070315940c0c200c054201c8980c0003041a140c0741c0c410b00380391540698a06041610407504040c0d003076000540e03210070344103030035a02d403042c0845c0704210b2a5182134110610107016482c00c0803404890001c012407500c0096000003112504542166858580508025558080131002c2402030082c00400e280c141b20500075140510080710142850305000117103000c0160b148421102c0b460000428030100030719500200001c2c03c48486410b98a281c608240800e48000070049030040f03404000401c060800102041600350340d004001500401700b120031540103c048800b5a4445524400c00c08229000505601102c1c0300f40c80344815079503a800f910320507903101c0700119010742100c1d400280e004c0c45a0a02c03801280b04c0c0e8001030519100702c0126110040c0343d041b0843c1c5a10004000502c5500650003800d081c5080707001740030910f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 809149055 1250 809147805 809147809
    0xc1401230409020a03020904050a020c0114010e16051b030a0905310b0301060e091c02030405190909030909050903090d0b101d010609050a0320030106080703061514 72
    0x841107100b5095901c0c1c0c007003081d0380e04502c250111a04000001c1041c0002d08120100c04020751019140002562a104030084501d000c060f505040320351020301901b9070764809143c0ca600180c080c5601c8100a000c204403100c0c1f500021140e402059810025038540e800c044c40904410400d40115210301d00f5000000030344e88030340c4007103400194101021f0103290140c11264016252215003e5030550801c44003107260301800c50540d110b40c031801e0403107641c0c0381400c2c00800090301000c00c020050300b080105200314240b1400d8407111040a81c800c802c0755a940072078038100d809101c030031400030300101d10030030040009021f560741059a140203507141c41c00d40800901c2c010f0940c0b000504c4c407144100014040c98803174201074001d04503204000401c1c103034111902c080d041f0034050b00300828190580414907060010040081d29407000c005205e4404c84a950802c02011141c110f900d59211000464504002d11000004620400001c1400d01e030b03950103207001c00315070341200014120b01102c2140c5a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 809150305 1250 809149055 809149057
    0x9050f0c130603151a0607060506091810090201090911030406060618090902030a050d0816050306090402010305040f02060a030e0606040e030a0c030e0a0e0402040c0f050a0311070c140123 82
    0x103001490030000301e40c996048000407105c05c0c2d849856014101045613814004141c02c1148900d5088606541c0e0303a8803240f02c402810024103c404031b60b80100f6603a40c039154a03500220000d1b0050500401d02036950a0990a41e415507546908070000401880b04003d203071700880c8060403a904100060510600701e2842e00c0c039080c420989a591951156025520f082c40703c0c900e207e070068141c40c03040c0102c1001401249064a080004100e403020b0116068420000e032405440014100c84954407950011070103418080d0040d10811311140e03d8034010b0742c0b241d0090440241030346000c50382270341c141509400d2a00080a56004500b40140d003084160080225a81c80032903081003220a5010b0904a50b5034070224003003030700300c040800b011910543c0d5103607580c0b003a48211818054524035001c2110f000e136040c400c6c0780c0421400e0040d0109180250420b416007280c50340c01c03508100440e01c0d042f5003441258000d52032500c4242041641c5e5034080c02c070615084032640100000f1501003030840701 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 809151555 1250 809150305 809150333
    0x40303020d0e1f14030c090a060309050a0602030c2110061e081008030307030209280b090f061c06080313140609030312070905150409020d09050f0c130603 68
    0x15811003c503045980394011200c8081502d800a24a40c07a0304d00400351444984c00402050b100b00c180405c0028150702ca4041c0300c121a50203c060500c80c00e0b1952210f0103900003505d404400e0100348000700f0031141581200300351141007442c4000505000040c2e0f100c10f100da400c01d03000c00c50280f142104071000c3c034013a00241c44003071901214aa580032012642e240f07081d00040d1003400000140204240c1c190094014104212010000400308507214064098100341c020100d58488004000c4254084060204614003410451800d0f007001c00040c000c1d8018240c0e0a41c03c000e001c4545000040703841101c010b403243c00000c1d40f600d40301e04485022140d03a0b20030004060603d08401015880c0e20007074620b4a0b41c06801c0b6610f6000801046452010885607000003443c603040000d1a8540b0007103100e01c0400044445291500388103078480a940004803ca0f00c1c203490307003d00c0001036010003101d10048145c4001d00f00700e080c500b003040540c0c42813251000b9070030309003441800802e0b0a940c01000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 809152805 1250 809151555 809151589
    0x40e03180301090218040611250204020904061e14012127050c0603150d05030f1306080717060f0f0a08031e04080a0305070c1a040303020d0e 62
    0x900d040e003250009024101049000350002600c100c610b0107044401185401140b18420500c00403502c1d500702d00141c0660b15a2042d03c201c122040d13140d00b807275030f0008103107540003800152420f07202d40045416a031565010341206284c0f1064030655001c5511100003401d002511200724000c0f03680001c201725001c1030401e030303450640e10b151048090140e1100c0610903208812402c030345000b01414408410642c1d09036458003413003901c40c1551030f140c000c40f84200d441c081003500e4803481c20305104102c0240c4004035003034401041804000c141403405045028200b0000c50071003400e0240050007030901409941c00c3c040d501c04c0c0d407814141004a26a403180090384c540c0010100540010802250500781c540c008140440200700b10700d0100081a502e2112a2000c3c01c1c0484100740a00902c290310543c52550040710760078001070f10603c000d144440c014841d4008054903803802149034426011080324008000504104243c0c0503c4011554011420425000c0b41c0c0030000c2511441401d000362 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 809154055 1250 809152805 809152837
    0xc05120a0603020423133c06150602010c05040909080d0c1808030702030312130512030a061e15020307080d0b09090708100515100306030b06040e03 65
    0x450242080d40110000c5400910901405505404400c05c15032100400040c1d28003840c00102c0c010310b031a140111031903100302c680c100a0032219601100c0c0ca0203502000002082043d88a64010034540d20000076004001c001810b020521450710601c49540c046c07019641850903004925804c58142d40c116a506a00481c5410300e6150031004c5d0300c209129580e04900e010310900d16160300288020381e11303d00003d5400b130b198907201015a64000d101009505620400c852111a01701c20b0005070410b407100c1031045c03101c00c0b030703500c06040c200132400500c0e00301310200070021408128000c2c0701c003d12a01191b10041c61115100d1500c3e82c52038000d140865410104a0324030a02c2002190100e0350000b0006494091401502c0040c1200c4800ea80c03042e8480e03004074801c6036000c5417400c100e4899070003c1c03940d11854190300c0060480286508150041840036411a85400b045150001c80942e00020014250700c0c0000c110700d0007a0040d80904e02d0b15800808038100041142d0442c1030a140384 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 809155305 1250 809154055 809154061
    0xb010f091d06130f0602070c140d241e0203090d1b030320070803090c060307050a0c030e060301080105060102012405060319020703080901050a09020a05240c070302030708010c0512 79
    0x4080144c8032040002c0c48248009105400d0005c2000c41c0c2064805035214405050942010800c2c1902c0041003c0e0014603161501140d1480080e002c04181c1d094000104119540403202030040200140643c00d0540010402010580070311143c0700070300700e505000000a0030901c00505984001c40018241903940c02c1d042920407404000709a50542060b446503500f00c0d5280c6070106400684100c0b8052158400d910861701d403c501b5a0720941c070aa0707540d814009040b0040341c41c1140343c41c098040c0b01c00b414000d0840d44500c0000d5001c3c101c001c00224460030440c000900f164034200c9032070000e10764440c003155110070600b40942110000ca85642d1680c0b02c088016000b0540c40360180c0d185840052000704041d0410a014803070a000002040560344d07010200081d00d0084500a41c800000a02840b20f0b240c5900c1095451001300c04141d450410208482041c0e804509040b60a5100400410840c40c00704108400340c82e00d600280302180c50380e0b4000c0d200e07004030148046c0d455005000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 809156555 1250 809155305 809155313
    0x50f0c010b0a0f091a010c1203060302130e0606010f092904120b010e040b0601050a050c070807080c1e040203061507080a0e10021b0d0b010f091d0613 66
    0x80024481d1005010480c45682c0320000440c020751445403c035958140604120070300050046500d1139141030711416407586060b56000c00815501d4190020f00d075440c0008005030310340300308a0902065500000480d020100002ca00d0103200030543d504000c185c0604a10455202c1184070480c0d00c0c098400305a20048001401d4000d04d8416502c0e5000340031800240004802c840c1d220007501a01c44622180d80391860301200302c8040350060030003010000401c4ca90751003800101940b00e40e510384141400c44002c1c04904100e4940e010304402e501c031040c2840010414441c0c00c0c05018100e031203904403401003c030364a4600f6142c1c0c03c0c0f03119a030b001c00080d0b03081c0c8900030890b001145c86c052035980d59015103004945508000c1084000a0852a411a8034200101151081146034004012044d1000c030742c80d000200c0742c1e0101c1d0304100007000c10030008a40c099058064150403074541c80640c2011107241c02c40b40007469005041c0001401340c80c04a0f0b0120b0ae50380c209562008213040004c050030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 809157805 1250 809156555 809156561
    0xa030524010b03060f040f0e1614240d060e090703030206090c0f15090306090d1202040e04021e27070507240621020a08060603030901030213050406060c1b06050f0c01 73
    0x50106c00714000d030314a0000070340e004a80b2000365901648a041e60302c1c08070042c00110040c0d00300c0c1d13a106800d89041100034bc400c1b403010301290b401c0d415000c90740310b44a042c81040d169041e100b1000d9580700e0082407040580521007541d10204240090080c101c015000411301802500c50324060521198261008c0001c00d04407051844040c084540e01c2c102010160342c0c41c02e081c01490000391200000b807101140768000c95048a000c5d00c01b16046480342e0702005070501503001c14210840c0f01862036902ca8580c0380100340700c40901803c075000c00340d99049107582840c000b003011007048420020f610000c2c0c4091580d8074071600010060205c40d441589102c000c104136017011513030100da190b40403078484084a04d0740c001031090383c0140c1515520440903a66420640700a035140d0400d024804195129902821b0700c100000d000e0010340d582c030004070b03084561030303040307e40001d0400521000b0300c01e8190000381b042c61382c001307404040c62510700000d0603401500c0000b22407040c002007510404800750 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 809159055 1250 809157805 809157821
    0xc021c0209070503011502160e060a050a120c0909051e1009061b0f050307030902010e060c0622030e01050d0e06010803090a060504051e0a030524010b03060f040f 71
    0x242000740c842c24203400240094009116029075000c50844148502e40301080e0610031280c0346e80441704060030200c1c0c0401030580200020b0700f0008002c40010b055840844040003030071820700d099045c01c0c040c00c0250391000302c1d0b002408a00e04101c203400c001036001900c20200d240b80c0750040c00c8090b9200d42a03080c07039111064101003d083c0041c460511281d680704c40d14820070310118952920800400340e4051020300301e040085102400021603160091b04140a1300e481498503058001e440c07070004400360842800740b003495001d002001803140100000d10220a644143e0f00d4a040d1030783e030024480050103407102c1c104140895468a844c1076070f0000c2069081c190b054900a685860300562b807500501c10407403041460000004e14140a44200c0d426100041c0c101d500700013540001156094a041059401682d69500000450418001e121001c02e40070f1316981900800306019907840d6041c1c101410b01c1301d01700103120142e41c4130b04022001550603a004949032384007200300c9008000714 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 809160305 1250 809159055 809159059
    0x6030a1704090f140f10031b0315050a0606110a0602070804080613021f090e0612031810211113080309040e160e09070504020711011e0c021c02 63
    0x1031988405442d00e50040324012104c040195600d41c0e90f402c607201d00b503005a4111210419030b20007400494120f4002e601010a0310040f004102d41c2c0c3d9845c400b03080d40008020081036a581c05000c0c40070018045e82000703100514040c0300d00056803600030b8a590b8080c400400d01580001c88004002e600025500288020710507200d09181031b10303409100b03255045080340300c0d18800b8480c6c40d0001c41c0c00300d445120071003660b84011007401c2400304840707403001801040e4403003a500090308041d04104003c0818448601102c040818070340300b07111115400010301800c0c05108851841d0780c2442151048103d00c0300203000c1074070500d038003060707040b0321481c1c940303401c0914546004107003030300d000008002030311047e40c040000c110322444290b02c0c0d10040c0284074038070443d041d04005030303080c00c460745400c0000d0406403001946d0301c800080403a400524100c4240395045000304641d0713000036401c41d000030a426a0800c0c1c0c190100010a090030814000b80b142c902041a6038044d15146075010400d940 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 809161555 1250 809160305 809160311
    0x106050c0a17090f04020412021c0b040f0c0905040b1603060b210108010501150507080918061e03030f070812130b070507081204050a0f0606140301020306030a170409 73
    0x8448611480d50200260a0140c1130b4000c90400d41e082503c212800c40702d446411001c0910710b41d0030000299070305c0340e00e220480790a082c0c07800810031b0350041c1c5004912460380b00c180c421013132030000620121035000c1c0401d107280c1400c00020030301d01d94040d0391180ca805100445804030060a034010821901b2140321040023007042064004135035688540c40440780c500381d402d0b0380d03074045d403070300303039002401502c1c1c6a80102c0181001d030760054018003280381c4541c5e01e642c1000c0000012882c00a07602049650b052141d6060081f5410800103500f85e0105242110b403210003584082581c91090b51248a58080002030300400c2c0700310041540d040031000c528581e8103082000a442010b51850f00c1981d0b180c02c00c1002c00c0ca03c50054085030b100c0380d4031100c01170410030407190b00117880f6001007007561580a000c0a00c1c00080c0d607008420522480340310002462030030184103854070701c10501d401e8080da204000340301e000d6034001020321481d0b50200303500064a0060000c0321041c000d50b48031402d100c2c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 809162805 1250 809161555 809161583
    0x5190f0203091920220504030f02010917031906080d0f0207030f080306060d05090a120906080a02030a020405031009150207030804020f0103180309080f0d05030106050c0a 75
    0x4198006500a00082e021607515000089083c42514841d80c2c0040003c503a07a080c0a50340c00c4201080760340038100030010060090040404596201c2c20500010942e40d900304100401d0b07003040c10b032980141288020088003c44d42c0d660005060700a5000402c4200440080c6800503080da45403014014802d0a1040c0c03551002a60758a107100032aa03070201d0141546822042d100044800031a9040301344240d9514072070f00c40240c15803001d00010b410500c20000482054541d0203000e0007008018020700d01a580b5060004d405c3e400950300c2020020400b20400c4030315481503649802c42801d940041ea40d4550b074100c20001e219030b42c4070383d1f014022691f20400f250301c4e1741d2101d2044c90144118031003103000419290304038400d255006022601c1c0b840030a0140c2040070181070000b0040c1030000d290b002d1505101e00341d00050600310000744200300c3c14009424180310802c2164029401084021a85600504a400705001f00c40801c0000324002d9001f100410603c03c0c1c541e00840a840400c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 809164055 1250 809162805 809162831
    0x5010b030a1a0c0327010b0901060c061401050a2309040b0106020105070e06030703090303060f14030f061e090724082505090607020612010e010b1303060519 69
    0x24142d0108102488810009040d0004203401c80388180c499014a01d160303070170700c03400c5c2084602c215a0a02590360b203084488107174483d00122400703003266803138204400c60b041c0b03001425100100000b0350b6070680c130001040540c0b83d0031440c8094a4845101d422099018a44016200d881d007101590040095080c0024001c0001e03005050768032a50091005075202e50003a00c6900e00326400c01d80108040002a0300b0b02e110342d001d00c8a940c400e29002c5540781e43c400172556821225040a16008042c0c2c41e0384800345410405e08001088000c050605840c0c103680300095100038201e4807140c440e04100080600906010b041e01400540100f56a8422904060704001c0d0705e4a40c00004035a40002240c00c52100c0e1201120201d400d80d1048071401485a0480d007036040681140c1d0480e00501020b00140d443c030780a001c10802800a007000c562600d1a9540201810380c0003503a022810040c62080c2c4490341003050907a83c0009012480da1070740641041040c2417050b07810400c91600e08010a84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 809165305 1250 809164055 809164073
    0x14040b0f060a1709190221100509010c0305040b0a020304080712050d0b0d2a090e03070b0606041a071a100e01140325030c12060518061305010b030a 65
    0x350b10480d4124030f40c0e4800010700e5998080703515018401403040c00760401891300c1d10048010314040341d10003000a00800147c0c2c5040282c0c80c2d00c03a0810344a0003001482c008c02d2148507043c20341d038038050156040a85a546030040c01a04580c03515800000190601000354200c410444e0301ca101d9402c1400915001815600401482500382c2e040c81240a4189042409185203540081f11b941101d00e41d61000c03541c002080070032034402c864803000095804102d2084050030311003000a035a841d02d035032508c900e40c0d00004200d10312441003804180944909c00c0d5405c42030703100c108101d5070350300c2103402c14201091003050a00100765081003001001c4550310414401c440345810801c4243c4d8840400b0b02c0148054003280703805a124004504141c0d0100400d01e5043c140c0030500020f15441340c90303501c4016015000307c410103c2202c55a01084400d101c5c01d61300c4001302000480382c0d0310505015454034806403c04248159000061003848001c1d40b000c06162401012940b000c0041c0c45c1040b88 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 809166555 1250 809165305 809165327
    0x14070c1703160804150c090512030f190e04050a0209030d050405030c01030504061b050720060d020309151003030207080c0120030c0610150914040b0f060a 68
    0x601880c0840d02518152800c00341e9001e218a184150710040201604882846000f0015036482c290b81081c0c44840d07403c2d100e400c042c5a11940c840211a060106000d14410071480011540d070081040c3d0103c07041c120165110714907821001010307400c513518102d42d441701503d82d003a8024585402e0000c290303030342d500400031510140e041ea019201d80180c19a51030140c0d01ca9942c16820171444030041798825840698003070300c9002c0000755903030748640c0c2202850340940b1110100b900000e214050000b00c100c4c150703021030f2116120030309a02e5400801c3c81030180c145101d26041d00840414017043e001e00400311842c0c00743c0d41491151808401c051000111032109170054092801c01140d811804102c4803180101070311580140c4079144c1c0180400e49004180e503900380024403002104040620007140207000c2c24510740b14035824543c2c1040d4886c1421f90080c1800000c102c1004900380c00855014002070445002400d298144d010a944600c08249a98805800a0508840354000b864062 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 809167805 1250 809166555 809166563
    0x100303020d110601050f03210702090a05150d230d031103130f050a1a01060e010203090109090c03020c011107032a0609020f060703020106062c1314070c 67
    0x24095404100907160300c10b640c594405650042d000600c05410700d000340340d004403c041e00321142d014842841020040da00000012030100001f040c000b586003050304181c10030b074181400c2205040014685884000984807280140083c181c41018420f14150038401c2c6040c01480d9600815461080e548503000c0d0544203011078607042145410b098814213880c400c0451481c00500c0b582c19854154028140c4401100e40c0e00c0355000040000345102d40076840d034011132030303584200e505258001e4000c1c07a490800504541c0309000c0701d181e42e07034062003040842d448054002207051500104030041e02c94a500700c0080d608101c00110701c80100c2c00100710080c020360b140e514103824036800780d06d04919000c0040e001c1013114100ca002c641d0507482509214802000c0d541826a580d01280c41600005029000360b5034814003088000c0d00560b46079011504513402c20400b0024142041e86070081c011a5402060386481031201d64140360300803c610403141100b0b2420b882c1c0b0704402829250802c2c0221 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 809169055 1250 809167805 809167813
    0x9030903021c12030b1e040b03030a031b0807170604060f030f1104020a02030f0d0f09150e0c010906031a060c1f09120305040c03020613090e0303043810030302 70
    0xf03500c034428801c10101200c0140100c140080807080015094008140c041e449950755100740300c00c1d9420001080e0f40052a140442d440d41d007808252288120080c0390300030b2000740e06c10050120391000c030149440e140300310000a291142d40216000782625003044800c50045103011003071000d065418880244030310f41001e0300d407046005210990241c0000c500c0541d009014000f43d80c04410007910701a05400c00c0003442c507110004100994213805400c2d20204141400710390900340c00c2c02107003504600440102088070403940020f100d6100d034412070f0201030f940c01305020481305119450307009840082166840300c41c2d0040490710380b15401c03124101410340b80310a4400881e00c0c0158000181c01208400c0c3c0c070911100c050f405050010030450b0010b0001c0400b100603034940000d04101c0400a080e564201d01b0501c540d02103c122183d0380f0b000354000d10800c0006202c0d9100d11119100c2112802040c5103e003480c0414500d0050040240851a00c10000b12540d001080011a8001d908032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 809170305 1250 809169055 809169083
    0x40522022208150609180616021b0f0f01050d0c080f010e01030b040308181e10020306030d0c051e0a12210b01050d02070606030c1a0d09030903021c 65
    0x125540b40c0f0035050300c1e9414802140028a0362410010050380040c422101c0050018150b00060804c1c0c0704603095000b0784105240d010781940c0c100301820411a420043e800300c42a40360001e0b4140c110307079030f44078414108503503c4042a446541940d0f80c152840809000c5804411005013031550110740503a041c14810000140020f200068581201c0e00441c0c08bc041e40c4654a04a03660b840042104a45c605c0341003031081c00980c20000e045881c80c083c60040d0342c0d40d0510300e6140c20500d00e92a400010740c010720500c086039034042000c0c101542d0600302840c08102c20324025041c022945820060440d10014105802c1008565003e240e03100d00000c6a401d1803064040d206074850b051120300c94481490f07007202c00f00701c980c001490410305041c5507041c0f1240d000c0c0541aa480300404940590303c07100c042040203400d29099020305000701d10030640103041e60180034240980503220583c40c0d11440044149809051102c4c06541c01501c4180c1c0c051030916200003849072a07100701d0341c2c200c4024035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 809171555 1250 809170305 809170319
    0xf0507080f0c0a0c0b180c03010b2112190210090b060f06160c0905010501030608060c090f1008060f060a0f05070c09021309061a0405220222 62
    0x110a10502080c01941c2040d142d1009544164108202801c14001c10090300710200356817900562003100d01c41d03c5440424142d4862a06000498040c03901a07030500041712030303a549808042c0c3c0c148101d24442d40401118030405441d1140b0320720301c00c0311405d0006032428422520809444594825003c481c1c4081140100a08031061040701801c1e449a000100c1c010b89450080e040c0081001851941080d03514040420408801002103c0d8210800750030800e40059020303042c01000c003402c00300500c40c54a8405d684444004000068030718000954821a507282d800e145284c4802030069100b034407a0f8a070140401c1015642d4a2084080c002480c031245001c00032180400000d0380e92030701100b03c1c13520646098000910889100b03004400201d00030075180702508080d2428145c0040442c40c00304090115125504030b681c005040203140355810800c1c5040b5002c44805507100c042141c0c0c4c100d10941300030341c00b03561002c1c03103400002c01e41007070b0085038880450310001480007160b90b6620b6003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 809172661 1106 809171555 809171567
    0xd03020106091a0301060b130e07110a06051e01082d060a0c08161407080d060605030114031c030510080105010f091b3f0f0507 56
    0xd45440113260900403107008040300100b03c0e21b00003004040482c1101076002d200d00190300d01010600040c40341c0700301200c000c103490030b80349d8152443c0340050280c0300075240b12010f24400c5001e03147c40604c120081d4100c50501c00140007800e11082801a01c11305c001120309114186241400400b005100c1c652080c201014000354451042c0c10140c91400040c4c03001300005012507001900340d40001444902d03003203503981039842c1c402c00d14002100f0310039011a07405040c102100001e049410001031416140481412042c0c50b02071000d240d84e40003100d24190400f8030604204030041d0007540802c1e00b0072074110510721030540300d82c50142564403c5c0c1c0001d990300f40c686130410143d05a0311440b10319542d01e029a080800300c03100300405403250039030728040c6030100c00d42c8030030218074510302c40030100b83c80181e150000c40c449088900410445012000440c10880001d0006200d94 = true := by decide +kernel

theorem cover : BRFrame.Cov 808992805 809172661 := by
  have h0 := BRFrame.cov_init 808992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 808992805 ≤ n) (h2 : n < 809172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
