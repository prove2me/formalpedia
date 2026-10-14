-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2163
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:50:56.899924+00:00
-- url     : https://prove2.me/submissions/7374249c-73ae-48a5-9704-41503b0ffcea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 388848920 ≤ n < 389028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 388850170 1250 388848920 388848983
    0x603032106030204180c0807080a350706050a3602030f010903080a02090d080a05041e1716061d090a0203100609080a0f0f12030f1503 59
    0x101c0d8041c1d580d00400c0440e950b03a02c40ca03441001d84030490f42407040160403000184094401005081e2070b2054003916090491001051205500fa0301c603c01140c03100701240746d00304d642d140d521388030109130030310000c0d070040104841040c103020014100c0110f42c860b80c0415070194000c00200441100c3c405503109442e108a8425000b19803600e0260300d080100383d04d80101c00000080345032850401a14020000b1700c2001c0082c0100141d208686400011800b616403001c004c41e11070559072801c0d550f0b401503403c115212104101da41b2000301e1400d030080c048494400090060100110380c090320341d06040010381046c2c60403981001181d01c50070305800103a0444100d80e036000c0d0b01c240041c01c850416515404255004414800d48810f01003903e402021903043c42e00c0840c3c90102c40d29200c41c8070140282c01c101c00c1d0547c010a2142020303448280c4c56108205200f10004904041d000b88007481610a12502d80070004c41403140c0120b514003070303942081280c900c4c00d18038000e90b4520322400c0d070f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 388851420 1250 388850170 388850237
    0x80c21030d09081207030b0a0f050a120515040f0c05040c080c031302060c01060602010b030d21180b010906060905090a090807050304291213050304050a0e0a0f060303 73
    0x80c2007001c0e001a1308682c001c3d00a680d021071482502001c11980540c01c0c0c00c418a00010a03a00300480c0d91003088490031100c0f803d51080c0d00c14181d05190381040802200314800314180c10800c0200086030f5800003445214007401e61005480d84203103c00c540322050070304003044040c0c01040c115030f02c00b405964000c00a29204000d00030b140e001c2450758002c5609040c07140c0d1202424080c0302d8080c084e0760302c044c0064009002e9000c0040004014001c0740400b18040800714990360764659164011603d84501d102401c8400f81c0a4901101030b200b01b4419504400d1800e4004182188200705260440c1e03801020300500c1c0c0c4076110154010180b10400322540702c0308106c0580000c03030030b002a2000380720304074001052a0006035108040032240100014915041103424418440d120390036810001010aa43c0422080d02e805455442950410782e80510100000201101c1d0020380d98030410710b20100344000d1007001e0007101642c03403900008022070b6032864000060b03e110a11501058500391 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 388852670 1250 388851420 388851427
    0x510081902040b03010f0203420a0b0412050607020d020d0302180a03080409360507090f0b0a15080613060e070504030308240d0201020106080601080c21030d0908 71
    0x70700007406c448a00c0d45c200344d550b801000b004084442e0b400d0b031000c009244130741180031405a002e0004800da500320700341d10383d00c21020016465101e540b05000540320008910b66190740710f400c03d07244002c2502c022a95440780303100060f03001d4804101022840d00940003000c5020a4460940294000344824103480301300848200c40d81c0d40c1e55141000450243c20320b190f40b00e00f8020014150b81200b00aa152070405620b02c1042d0041c503024000b040030842c83d544a4190786182140c00d0405940c40b461a0608148111004c640d40e0341c041030382c1714021100460b4042d9112254080140c2c03400c0000081803c1d031000a00074100f03110500c4924001d1400003074000d0310303110f05615212068500701d00080011800303004041c0c108503440d80114400e80d40d0210b21443e01c1c4140c081c141c6500701e00340500b080308810800c41e4000d4011501818010007995540c1d0b07103d04d140e81d82d8200d101d05040c41180c01d9046501c4100c400b4400703816009000000d90320709240c00c1010000303460005000c4441c0038040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 388853920 1250 388852670 388852691
    0x11060c1806031e010b03190c022505040b03120706020c100c0906030c08271203040506090d14090d0f08070605040204062313150303020709051008190204 67
    0x400041d840740c091040d044403442d48120f041d044041d0140c0242c40601c20410500c42c00082d41141080001d02844000c1a05400200103d0410070000222a184107601c00c02d9400d00050f02d80804c2a1001030700d00304480c9803040c0c00c01d5640e1905803400302051504110391800300e54190020000e5203802c00c02c0b82e0601108102000443d85140b060304001061007030141308503541401104d0742c01c842c40c5050709050624040c107901000c003600c5413041072001103043c01c071410000d210ba90b400319241e62030b2a440e0300d003504105407103d808658148181c01500700c8510064050342141461040307881d030b074504081000050104010b4804419111010940340a4000070418001803202500c2a0380c0071440342404d10501c01591090303000070501002d00300e0f0780b84d400b03c0a803542e01ca2000e01154040c000c2d405d100d60300c1e0010848985008905514002d02000f4160001422400c581031040c04210036919910742c2501c0301d0280c020540b00750810520303060209203800c042c41941c1d00003000040c070341d95603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 388855170 1250 388853920 388853929
    0x1b070b0a05070c0504050103030e0108100909051c080906130f020d0302030909060406060512150306090a12051905071b080a0317010501050f222411060c18 68
    0x5208200c009140001c10608001c603501d40f56009110130744042c031255041d554007030310210401050074104030b03220000680800081d00300e60300829284104102d240010f051054882100000d0401d9144080c40c0d52440c1921890f061440380f007100010300301035100c5640c8030000e010840b601f0307101422582c4800740035a0b03a0801011305148031f90011a070720700242051261808008040500c9245084e10030802982c000302120a244da42d07201566641e5240c8468980c04204071a0054240c49408100100a8000150f003817a803805040303840561444d846049541c0c1c0302c0d144102c480310002030207409006008070060b0404500c6000081e01c8140d036203070654069201588402d01c45d0b440324800106168018040c141044000c2d600c40f41190b051100190080c411001058199440062554026526000c0140b40a90503e540c1d458041c1d8501c1d44030009043c20340c8c2c5c510305010048014881d180101d41520120922070064066540d034150301c52120b40222592a110403030100030311969554 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 388856420 1250 388855170 388855177
    0x60307080106080601170c09130e070305070e01051011100c03060614030f070813050607020109021309020d08090409020a08030307091e0b0d06090515030c010e061b070b 74
    0x262a40c60254540c0342410060602c08043c0146061141c042201440c810500ca8041d80c000d280400507656068544041a43c45007003026810b1210f1170086800f400900208210302103d004004491030f00ba03c900300440021401e115245d07110300031054406285001c0e41100c1d0714038400a094400090344561342c070301514031106480700080d559040038402c2c00e8000f90903403400301002c1429401c624040702a4090040094100001c0c0300f00306001425580da4294070b15001e9502c0b0342910b002e4104808060b028020822049100382c00d40d0343c1d01c540410040c451940340640082001031828040d45444505901140765a070300310740c54085110250315912140c5006010b1140219500d01d08200e00070050a002e8010000e0107103541c00d9984001e00e200302620a59215083d40c0d40c2e00c806444001340100620b60100b034446042404201c0d40d5000b900580540d404250261601d8219035401101c000304030410459004070103000615503001c0780043c012000f070340d0408860450783c44400c0e0305066013 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 388857670 1250 388856420 388856431
    0x220e0f0a1704030602030412120902130b06040f06080f061c150209030a051b180f07020a0b07020c15030610050f04030803010e2d060405090c0622150c0210030b0603 72
    0x5c00030703120b21125a5010840c080c040070f03049e500300080325065001904c2203402c0907009188948a5803113030b14955a10003114001c5c502112000c808950b81c00d030140c417164080300c0820b06040743ca40040c440d410200080c103103140141d07100c100980701540c0c0f960003160a401c00b02e5085075082c0015051a102001b03503041e541d004400500c10100c3c010000305080c0003181c1200c3c041d0803480c110205030200304a03203541002c81c40000030b449030f0340c020040740f80c84400311001d05044068821b00985039008650340003200c8040e10300b801489802d000d03c40711407205641d8140c0007409040181240d610881c0900100d03604c1081051074907680c0d03225403041e038000ba00103641d0725110505000740005465186a043c500381c40d010b0340301e0003802d00c0c0d0025000d4014845030046459000148900e0703c2800030601c11440240315a440c0e903034072000c010801c0915089600305520007400441e284046054520808100340d0f250040940350f07a00380028503100d1100380040c95121601d4003481d0f0b444030f01551250 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 388858920 1250 388857670 388857683
    0x7151b05010f0e0c0d050c13090503042301090311060c0c0306010b04170c09060904020f030714030d0305131712010603052502060f070905220e0f0a17040306020304 72
    0x1090043c2841e400c0046111a1911481c084503514001400100301494000c0c4115080c0e4031180071581840064200c19400500b6030100050100340c540c0c600012148042d80c00b144031210011100064030500c400e404051b101c0b400c0103908150030325203540100000c1e8804800c0c1e850400400e000f0a2030040d003070700b02100341003000c101032024154441a25150402100c010507200c048007010a803400d50140001b401032a0349030004085d03407100004600c19103006400c492065544155590381c0d42e903110580d500ca0b0081d200c0244003140300cad0043e1400b8806001c801540c01c00030340d6600302c039030b1000300003200c5220040c007480104160000010b4024580307030b11302140616240c1940200c4e00520381100d22400004141050301070360003e22198407280e5041c043c0540c2d02e9808041d10360101e941d001c1c03a485078240d014400744007150b0425482c0420021018082d821144001036151003a40d078208500b584041e5403040803482140a0034140c0c2d030303249030151030152a03484a000f6607004503401c0d2403d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 388860170 1250 388858920 388858931
    0x1c060506010206061507030e0f10020a060e2a0d0b0702010b01031401032609040905010e0f120d1a090109230105010c020d0c0504020c0a050d0207151b05010f 69
    0xd55805122082d4490b038102c0c3d40107803080600045c1d56250080b124041e0400c001c01c1c2c2e6605894a03003402d1980c4074940105501141014ac50000755180f803442c5040b0381007410030240128051001418000f29001070035183d50303c20441c03c25050074413032184000e41c8000d02400c041c001c2005000c0d03607070040000d43d0001c103204810b1400901510f460400306161040403800410101cad1000c00b80203580d01080141e0408a4103100701807120f0301410180e15409480c04039043d04008055202801e03c004e010180c1d00c0140560f00000c2d1074009510b0000081c0d442040020014005c95102d0241845441c00e8440e0b140e02c103a0200b4441c0380243c001280080c0e42d022903000180d40145c900c08168a0302c0c910103203039818400000c002442d0458001d008034150340ca80010401c4e03d0001301c0203090041c0045483d81303e2400860355030800f541040c1e941e80140c2c6005d504081c40403400350b041d103030002c00c0c0789230b0722041c040c0072074914070803420826810104800c1080050820b0054156460601601052 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 388861420 1250 388860170 388860181
    0xc092205010e15030a0b06040203040f05070f0303110102031302130e06100306051524071703040b07020312060f0f0310021321141615080708071d1c0605 67
    0x81201104400510a17404900c4a2000a07003280c101a40700d4025600503071641c8542c13501c03072034003000403d004001d401001c0c0081008800d5800405c11a4003e641d1203074828803a0164508034401603c0b262100c486003030010000d402e010041030320111b4160030006060003440381e8203041a02c1910100c4041c00d440d402041070180600805811501c40c080600300701221400040703942c030316044400301c1040c05091401c1c1003001c1c0f009407030b065070b0071810b0f079a0a03d00343e415040351741e170049400303c0350703003040070045052284000203440b00c00200c4180000d06840b040c040011203800062404d43c0b141c000d100300711058805020400b2141449040980c40d19041402c40f2601ca4594015403420b0301c243e11003555000c401c8103040c01e8075801502c1100d65444202840d81460007114400d0003e501d040e82c00102044106c0d00815083c80958840200382c4032080700311003110054400320300192031122480001014040582e02d421401010020b04000001107400c0d2164514400d80300d450303580d0200714 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 388862670 1250 388861420 388861441
    0x60d0905060105040c031b201903020d11061b0f1204061803020303061201150b091507080319180305070c05090c0f0f0403020a090902030d080c092205010e 68
    0x1203880c9142018480c05002da548840900500e52403641000300b90110307502800c00d208c0c1c004564912a0055908201b10031414070580741d0311100031001071181807940d000d00342c400d8503160502455140500900e40301c1c840e6244078103445c07541e8034840a50800030000084209401010080d81c20030b400002c030b20b0141807030b4040710030341c07080e0600c1400720310141c000181e03002c4200d0303503c003100301d4103100085030b11811980107050012610022134418240402c00c44284005001120000c444441103a01d084040070880c0c0140031005102c0d22040c00411410140c01c0e41045030340001907030004260000c1c023a00e0100c5480344500fa40070640c0055003206010852001c0001f500c001c1c4c80031b00c224108243c1042c4244561034403000350460108079101c070107014004480080d0b030001c0c880060b0545521860000b8a41000100d1091040d035080400e1140142d05891080c0c5a071010541007800c50310038443c000c08406402842c0b01c00d59a0094000511440b0b182e02070a540300240741c0c28501421200c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 388863920 1250 388862670 388862681
    0x5060402130c12051503060c030a0c030605060904020a02011509020403020a080c0f0918120319060506180102011104030507030308010603090807020f0f09010603021801110a02010c02060d090506010504 88
    0xc01149052400101005402c50054a4103050000f00020142d5616003a10300e001e0103510600d605001d4142848580e240b030202030b50107014006c4c0100141203227098150100c621511035240c100c9401e0000800d40d2030158054580d440315400041003040a07521034822080703440c1c010800c0c03194042014015814040100405001d4482c0100060383e08540001c540700c2200b102140716607072403400524008144400240a140c0840841d0280f412a00004010f5001200e43c8a0030b8005401a240e004210740540e00c210703003005d0441844d0081841800c204801581852810b564036104050140e2111200134801540108090321b0f140c0d007549401880c94006a100c44201400c05000d280810541c108880380164104c0d91840300e840000007007046001300185050340039945d0b000002d0306541640090025104a12010800e51b5064005442c000303a9883c59450035402800588010750080340e02c403091500013001d1301d06040510074003030161600c0300ca003100c481d00035a004000c0c0341414002d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 388865170 1250 388863920 388863949
    0x5180102030f0c13030605071d01170403050309070e0408090a0605042103030b040e060a060611100e1c030b030d0305010506031317070f0203060603010c090605130f0305060402 77
    0x290700d541400c0682e02215500500b010441980001d8482c03015020031244500950b880a02409240740c1590098400c10003c055040a280342c4c0340c40800c035602c550310301201110103403c2030b07100782c035941c4080f2040e400c0240700005031b110315040400c440c504464540e125900c43c001d01a99058a1824054006800d510902c1809018002404010340c100203000140c42c41c0200840c0c1001c2a081c11005001885181a0424a8080d0f040b07204600440d20500c121f204040c180302940d5544012030b41c00f01a0800d40c54140c1181d85d142075940d13210b41003500d01085030310466444011029160008480d25645003010950f0b84070084850304042c40f4035200012103040822456241c50081140b80c880100a500c070700c3e48409400c800c010360b84201c41c5404101c81400ca8480c2414941112180d4000398160b00c0382c0300d003100182c0c11340360500612860f2403550703492000300b42c50b1503000e580700c0e04114000e13860000040000306503a100041d64100960040c0b0080040b8181401803100c0187c90034074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 388866420 1250 388865170 388865173
    0x1207060c020609030f0c010b04140a06051002102c0a0b0609100608040c031b08060c07030f18091a011e0503010501050d090b0a20040806060f0415090518 67
    0x10001806004005d446000c00c1d400201a550041c2d0032040740140300c804a51341e845803a1041c02c00c00e1142003014180b1460300c986081001584490030807402410380034103000140d200314041a035601068004440d6a00c0003424801003c8500100315080480903080c40c0c12540015180002c0c8059050030b01e40000043d82c05844a003001c0042c88144051070081505101d91840482c04004403800d030341008540062141078050aa1a607485120100e80710b9861248140e0000c2003080100404a5150700d5041d100c1e807601034044034003510414500c00c2c04c030841c501d04440010f44140b0390b01441009103c890180d044044049001402c0e41041680140080c81c4608041202503044022a81907900900340760b901c41155041e50300281c041540000c00003031101003445040c0425400401c0b50112030b001c11009103022680602c2940030318800c03500303150300c403c0201d2281c0c01c0c20001000001c001800c04030b04162034203c65500172005078000c1a005659104000926000c0100c4548000c0480c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 388867670 1250 388866420 388866433
    0x813060f02070e07110a06060f06021f0902032418030310170705060c01050105030706112107121d1e040e0a0c140f090702060f15031207060c02 63
    0x120020741d6242c2030300866101080b82c4020903c0d05019410440226801c00f04803401c03180c43d0f147c05405002c2070f10031414000100c0e000071030300c140041040102c60070a84451054000820403070310160003030040a83c0c242c040c00c00548455149040749102200b0040c209103081d04001c00903010080045031100b28940050050000a00311599400b080311201e5090441000d102c0c0384250401d099984116804031001805409124040d00600c2c1203900440030303103078220b642304030688039000051760360742d143d4220b107114030022128103031010380720710748003990364100350340e664032104080d80180035174010544c0a02204908034a00030394800d1280107540d8000764124400100103003655050f0b6a41c0b19a8603040c0d00c003003100b0704101c20b085450f00014801016956103003081040442c900307180d401110001507155042c2080c0310392600415440d8003c01c100e6640c004044604013020300801441001c4c0c140c403800036130381046044c0301c83d5200054950780c1d180c1481c1c144e040301c001094000654102c0e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 388868920 1250 388867670 388867697
    0xa0e0907110c0418060914030703090801061a0f0a12020c060a1d1506060f0f0a0801050409030f0c021819050a090f0f1401020d0218041a04090816081306 67
    0x80139140000307a0090b40401d80d011580381c2a10200b1444402c03035030a00c4041600800d00da4040700e080125406a00200f1005803600c1c0d800e202554503880306100d50008100403501d00d800e9000400400080b458100e00c4c0c5000c950740d02d826640107200d0720007107500c0355083c065021024420725078540941510780401d03103161400d458850310501907a10351b019a4900180d01a151081201c880f0203d9140032a07031411121b5042c801030300180401e0300001c125100104040c2006d2007407892544d0561611012941c840500b210088603281c002c9810400e0030005400141ca003982050103004007481400a6414210b01c08085400040030002060b0030721200d070000c03415207d401140070707401143c16650242e5600b48038a2400c10720132004032540c800035141040b820158003074008083c659071281300c0411042d00300b1054a1031b5451080382c0f481c41c0c0d00544214a81503003c401c11601c11041903060217502c1074045002045400296022080064a0f008415443c10390701e028003104c0c00d00d030480f150350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 388870170 1250 388868920 388868951
    0x32a0620150c07030210090309031703070203120910091419080a11150901061701201608070c091b091206020909150112200a0e0907110c04 61
    0x40c1c600203808500283c0340f01403610a1000d40c201100d0094240041d82081c034000b041c400c0240300a650100c039140b801030092071410101c0c2e000300d80583c0110b0401c0c000020707041c2f0481d0058aa00e226102c6c201d6500300803c2c543c00380156250203410007018607950038003020309106080c94400307446810001c0707500008114009841001e801807400c1540c040d141c0c403403240b40804002c0d0700d200b0b030041c0030204688420705400c1034080d01c003401c0ca00d03181040400545030a030342030081503081420820b0340488000380c1c50300140c50707124003e8a03030440c402e10944898141d9408100e046e17650403035007401403003050190300500c40e6981c030625210f02c0e6021850340c01440d0004a01070158004c0754120b506d0306022064040da112403000902205080c2400c100054600c1c80d400ca0090100d08078501604001c0e005110740040c00b0b0aa003140350200a12401d0101990700695517041400900403500c4c0c0c080d02d622076414444d48203a21900e042130103c04880b481c0200110b5018030441c1446150f40c024002c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 388871420 1250 388870170 388870213
    0x100e0d090b18010309020a080d14030606071713091d0a030903060b0a18090203010507050a0207030b0612150403030b031b010c0f0503210609010f032a0620 68
    0x400d2040d0b01561021004802814400c00d01940c04202c80c03501042031a00810182124030442c0c89a041a80282002d4501800201e03082da9101e003090042c6408242130459103095001c240e40300d9071400415000c4034444121070340203281501d84e03907143c2d0020400203462251169140c070008220326625a5401403404006010042a09446146074891511407500910140c060000c1004c010a0b980d4403040007000700b14030130b038401d41c01c1c0b1010514040c09901106d031a98040da01810005041d921143c0088078003902c211741207580780103955100c220500252012a010f0482c0784607605103810010305442405c1a5541f003074101c05801c949299440340c46a082a901b803d10564003000c0b4200301c0e5800d1618880034015010009505072080c0b078204840c1140d009001950f041e940340e020a01484810034044c400c010360355603d041c401b20714031908150003141c42050b100310103850b01d44e03080f80d0004c1c03d030311150200f510803048040f0070300e000e0714020b03004400f40020113505030f003450300791102103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 388872670 1250 388871420 388871437
    0x6090604120e031b090f0405190812010314070b1c1a0406030c06030e010e0d05070510060b0301050901171209010306030615150c0f02040c090503100e0d090b 69
    0x40421140c80c0c0744901850300c4440515000b0261403080f0042003100c15048854092188500002d20001c1c0d01c102c0e0205105000340d0300f00c0002c054090b1040c11040b00c0010b0490140c514407400d100e0007208080b00740b00a4041c3d0300c5002407091045c85908014901501500140303569903060040d48460710101010071102c0074000720205400000142a4000c80741412110b50450309140001c024030602041c00c00890303016980c10441003000700300c254200e807071400c2c54171100d0304402034085030b440c4144003030202d03d40241d06031803181049079a844101c2e8000da00c04619001c000c8010040d03807a142034128014000c04004004244801440a84030a070303140141080c050041620013550b4400d5108034051640700c0c1c810071181c084004850700d0002c1d6817080c1205030100e0010400e4061081c0c0491042a602940da40d183e00003d07803c00000c1c0590400d09400c000030303190006090382d0100b1a0758410018034900244401445c0003490401c0c00e1140b52900f4440d120070100103500d0350608695004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 388873920 1250 388872670 388872683
    0x206010b03150d1509110a090c020307080a050909010e060103051021080f04080618030903030d0209040f0612120f0e0409060615020f06060103060b04090e011103090309040e06090604 80
    0x24882c07803521140d04061340c05481101464503d55804010f420032400e60007400440300141c0b0300780c2c1c1e0340108040d02e44454031140160030502581c40003580080240c4000304840c00c1003030401208102241d0001400da001c62400c1c0001e206002d89960503224840d007007000102400380603800c01c41820600c904007440a48080490111001804185015035040c1c00c09441303000e6903180c0d82c150790341e130307460303058485072891482889640500f450020844503c0800038028606109000d001d20000350465042c1c80d4106d500d07205154040b0b4281e110f2540034043d1402515441540d0381084000340140342505010f00c1042510078100c3d0b0340283d007074a01c80004690118000d0541d10b0301c030015115691206170044400b41c0c040d00b01a402145151182286004a500710f6030740d880110291074881c4250300310041c1c100002c2c0400c0a803908410b410903a184d0002c1910b4144003800130407640304070740c80c042e96080420b219089141c94010f800c7e03156820402001036041295005480703400280008048 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 388875170 1250 388873920 388873939
    0xc030e0d02090711120a0e1201060e0708090a080a2d120f1b02070614031603020d090c0f0504060e0415022809030308060915010e0d06020d020a0206010b0315 69
    0x1c4100410805c0101511811600e03143c03400315401901030b201c1d4445035841480c940c07120444200f41407241d01d003203c0c2c16400030036290310f070aa010398505d04041c0046441c0c0c02000c204002156100c00180000b0b0110741c2d80a540b514600f21082000313100f120300b0b807211016202401c0322a13074411040030704034411a01c0016000d140c40741220040802035580e0f02c80d4260703001070801c860340200301682146c0043c0c85200144840c41e05152041c8801c44402160301d5200107001c140511943c080c040716008070000140c200040c0d15010020106913020290403d02d460060103d4106809800024240780d4001c4a01d4180380c0e46000e820800c283c1c0420b00154080742826400394082400b00c0300446480c241c40700780094520080c00550030b40010b40c00b06003404045031190501a44c414880ea40780e84442d100030452100441c0c0c0c0382c585490b01a4010155403090011411600c014101d01c5003090005913a070803502c4e400380c2080340580c810705c080d00382030040144484198860700c03039640c4100e540e0540b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 388876420 1250 388875170 388875197
    0x40b010504120b0708090d09150c08030a052401020c06091c0302010f06170c040921090e010f05010c0f08040905040605040209091c0e03010b100c030e0d020907 70
    0x8107030007254440c88000d0b10060041043c880840f03181d0f07009140755950100c0f030341d40307498029643c0d0a1500c1c00300001391152000b04142020b00c0c0343c45e2216121f07454080000041a202c681e07103904103030340118046661b04140801c1d803503050544200b0740500c4144070510b601020000c2d40b144184130569003d504001031010700b60782c0341c0d070300d0b0036507285080c1d80e0810241050400034000c2480580800e0341c1481c00002040c40c200581c5100c58046c40c0c0001040001e48c00c100b80005081480811a564110a070b48600302c50401031008480e0000bc2d502c2e8200e86160a2000301c02070010b91045a90110180040c0000e9038402180d003201d42d0022113002c001d032120b1600031500d208a91020407614501020700041102e150002d902441c0211106402511602d01440c0c4038960704241e0458000d07801c449000f00ba0190386607140120004000103000b010680114540100156181002900710a480800c044d000070210610500c2601c1510074110540d0220300d8840703000e440703d000d0101d2400c0600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 388877670 1250 388876420 388876427
    0x2010b37060f031113060c060b0604030c031202010902040c050a0221040303050a090f030818030706080a09050a0206070803040c0603150e06030307061b1205090604020f030709091a07050a080402040b01 88
    0x220001707401c020450b40a561100010f10b2403060903011200c0c1030078800001c0c00c91420000341d0f410b03203400480050b4840d01d15035922600100402408041d9500d440c003038001344c0e5031031054007007a0703001c0d0b00c03180d54038000000001d0a184030000045260f0391840c910b20382c0c24480748103031026250f25051050351a60000800d4a90717140560003030f4020900b000e8080100808100a04000d81d0070482c2401c1e00612a400c05441d00c403540940c0001405180004400c201181c0124020b40c2c000e0064601c0d01d41c003500410b02c01c1c0e101d071101385c031003400000a0100b08008050048001c10b0307a4601000781e201401880044607a1510a42c092005039002150300c07a40d0a0046401c05540b0420810182c643ca44201050180300500640850142c0000820040950003031600c9041b07210050320080d0f90b2030f800c1007090307800007141a400d441079001c00711344402070744030307010102e80540c2602034091040c1403a04040c03a030081812007004170901c01d0700c0031550010f07029900198101d4000c0360510790040101d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 388878920 1250 388877670 388877677
    0xe011b022a0604030c0602030d0b01020a15050a0b090916051509013006050a0501050913020d020f0307020721121d06040e062e0c020102010b37060f0311 67
    0x2074642d1050013030006d5400c1d0008014600c4141050303091114540e02e07801a6100d944054000c0c01540d00c05451401107080396005075400b0341410340000b41e004090700400c98404003102d48140720703800381b092800003c43c00480355000f800c04445424038011960885010b41c0582c0c7d0200381030200c03203a0942c086100303040b16006410011528036030303070030603031101301e80036104900c142405200c01c042c005c60594401d81c1240d5100d100034000003001c0102c441904020b40c420000114460b9092011010410703070ba41c000c1d4010400d55000f03042c82410281c003032001c5034130716070307459030011920b1400c80015004052802040309179091032368036280000d100b98800040d01c0709075070340b040380000e01180500c1405141400303a40c060341d1401060403108110020000110b048004030910b41c0d40c489841c0b8810000790f0501031062002041c1e40e00044040350b40801070120400c0c038200989149884290f04c0040383e9820010a19003600740383c0751040c081d12200201c5058410161100c509002ca034081c0001c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 388880170 1250 388878920 388878923
    0xc090302040908070c0b0a0518060d1e0c02030306010c110114031306050a0603030e0613051507052103061c050d0810080312070c030e040e011b022a060403 68
    0xd100c02c50b031514200c4020741c84108201c58050281c030010502104620540d000055542c4505142908802c0200d100345c10140c070071544020100301100603000140903883c0c004a00842d84007140307041c84002410f4034540885c100440d4414000c100c01e40c0e0340402604075142d0440080a14502d030803004960103500e8800b0500050000024000d02c50807a81c96019468001d01c1c04201130381354045550280c403600e11000d000100c440d810740010f841c20000074551244403001454840b55200e022440304c0a20300380c1840702c0c940216010301800b0090021040e000c0e205000020049020981e2200601020344140e0180c568403030091243c10751080150100764010b0100c410010070510000d1201c101201e0309084c24048481c001400600001039a49465010b0f001b22040d40c1c80240843d0407035113800082d401c002c60895010156107591140c1c420340c2c0c000c0400810f007080a5103020f540c0141000000c005c55214440e0420100340c280209420307000c0c0201d0300081d00c0700389000510b541c00356400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 388881420 1250 388880170 388880179
    0x91211070501080402041b110d17060103272303090108010306020901091d01052404030b06060d140103230601090b04020f13051009081e010e0304060903140706050a030c090302 77
    0x50140a0a8210300008010503014049a807801027032102101d2003d00e600d0303019207449001020540d158000d404ca8084d980b034140724000401911241c080c0c2c80e40300201e058811040403480c0050850801018958448061000390300d41940007000030b00c0c0c00e030b0500c809400c942c2c2c04112140036030310401c1d06c17000801151409043ca1600d0044486c101c900a00c0355600c80d004600c002c2040400c03000e102d5241c000d000d10f0403402c0c646151a49070f40043c004000a502c904d04020f200d9050b00c040c404d4003204072503448001d92960640ca003109080610011801110b80c4004620000302c3c4005441030544120201c040356114991020402a00a4613000d8004034800715400c010f01c000c4414410803a407080300c880700082c22006055904010358000d080d0250854090558188981040342c00384120070030000460700203201805065800c950004000a50200003c00501a00c05007000c450411200a0003102d850040003a0103072241e84004000d142d11130460700903a9000b01403100003540c0142 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 388882670 1250 388881420 388881461
    0x70201080109060e0615210f060f03030f070f120201020a020c0415030314040302090c030405010b0d110103051009050108010b0918030703260406050f071806270909121107050108040204 81
    0xc040d5000c02c03003241c91150581035030001809c1d80ca000307080e140400300c0c058050351804c4640c04486d840b85d4890300f0300759200f80b1044048000122402140d401481c1c240d400182c54810110000342032640c500345140c0b04505041803002c412581100e03c0080b20b906007804c90001104a90455081c019544041e45c8080307140c042000b0000040c004501c02c51281d0020800602880708000010b49001c001070080a22415200701d25401382c3d12581e046000220003500003591403006c9815034902b40c00030134459440301200c580714107043c4401c1d600820720840800c4c00031100f804603640d900540b0b801808220f504c0c0029990701c04404402d40000c001c0240310b04282c130342400c00d41e0262500b0f40e91410103458150000e50424811600d0100c400341001e001e812145c40d051041384d410410015811080848004e00c00c083c0544001c0c42000f401c4d10b10011918041c1d80c10540400e20804d8140024071075902c00403544181c000c00c0070707002e070751003420013114513201d83c00481c0043c0412a074081e417078003078103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 388883920 1250 388882670 388882717
    0x7050c011d031b01140c07061e060801140c0a0807050d020c0106181505130e0712020a0e15040203040303060506070615090b030601090207060e0a08070201080109060e0615 75
    0x30006102d0060001084080f04100f00e442d5800c0f40d00603003045040c0a54140464821650702c8020f0a02d540218404551a810b8641850095841824502450707944100801180f0380071300442c0c0c61900c0b15a4841581d18201c420b0020741d10034031240c50100504030002543c004d00800555546104c1100d04648401d040141036009100c40c1c080c100000d03a80c4849400500d9160044045407564501451291841c20f4144070508050001c3c0b00a001e171147e0440e103566004015200c01041c01181820f170310314290041c001c581e281a00180032810040c07003085114100014804a002004d8030016501d40d994102100105400c1d0001d0303a0100002403000144280d07900b1100c0c1040d4804a42450651340d03150a00499050030a8075400d500020010001c0b0241e94cc094480c0d2030140f000414072451504445041c00189407088a18541c041100019942e00402c05030151116000812000b400c20840074209007004042c47d00c24a46240b00d05508d0800300180c070004103200c4181c0e14600c046 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 388885170 1250 388883920 388883923
    0x90a0c090f11041401030b0102071a130506030603150402010c06240803180d020a0f0303110c0324062202070302010b030601030b130c050a030308060906030f0607050c011d 75
    0x300a00c00072036040c4101d955280e0a0300c8100e80403940500c8501d40c0580701240154080c2c41000341c2141035004401000a40c06500ea003a1000c46140c1840e19941d203000c450ba4080080403504a1070044c0020710400c06161130028028a05880c041c40c510041e50f5680300407a038115070044001c19003070516078405040c407940c2d007880c108086105d11820b43c55885072001507481c010801701e08036080c1074204100c254100300d40c480711044d0010386024603503511030001c3e402c0c6610f240d000710001a00c3c080c014008840a0060514080c4118060255244409894086001c0c60101c000d01c2c0411386010603840d580d0b0040c035809520007000400c4810600e00104002900162003c0c3c0155007440e5401085140120f5014107a0f80d0207c40c1c2200390300c0d42e641c804010911880115011900704d00041640d42c1c418032000c008500c01e03601c0800310701e481d2080c01031f41200070344400c1c080d600103058030701e04440c041500399110865150580d190154400a82d02401c01e07001441c0100b9243c0900d050344000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 388886420 1250 388885170 388885181
    0x10e1218090402090a0b2b12030b061804091b1d0c1207050c0102070813050d05070902030903040302040e0a050d050a080a1515030e06010501020a0b0f090a0c09 70
    0x115210301840c40c0a4014440c10711000c0300e009521103081400244549041d91004100c0000074203002152412813400c4104203002000030340c000c2d0a40c24001d4100310400c008850507400303529083c40141203d40104441340a020360799408104034581080d03607078495901542c28941c0081c01d40032030340c0004d1081d00305044039004014401d410824038511508003040c0950251240d44c1086140c0008149500c001c0d12002d001401048001c002c042c0f11340a090000d405104c3c01b40301e0351580da40b502c0700381800d1440d003a03000c14082e040b500d4410003c00c1020a41e64211140309802607034a903039184420f0f00b10f02c5907400080d07100b450312030300c2c0c11140c800081d0801401d10400c200e8490840e80c55041d161401205542c0e0009441c1034001141000c1a40101d8111003001d51155403041d1500d115204d042005015080003e0391100200610f11040100c2401020280060010080540c075124500b8200820030b4840b03403541c0000c40d0001c402003009a681d2034203c20300c0380001d9140c0f20060301a01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 388887670 1250 388886420 388886437
    0x60603020111010207030203031f0e040507050319020f040c0e040e030304050114040b1f0f140112051303050306030f01051303030e0d0507023003070309080601050105120405010e12 79
    0x58419100b00041c200520032911a290142c009504655580b86048616030800000a4000703c0540f00007a42ca2030f050b84142c011445403001d042d40c00d041c901494030b00800000c1c5c413090384a0550030000581c9030004009007a00c1d09131008203071400402d01c15a100c406042e001c9401074501120144241000b101850241e440385000b0700942698a100c1021070b41c081c2c9000d000884800017041a05100f0f260003540c50300c40d0b03071858807441d0780c0319041c0503a001c0c42d51000041502c101c03041c031140d607070100f10300b10383c845814000c100b641080c25496040d040c18203001000d00100002003821a80c08010022541010303400a00503850001602c142c0040c074648210042400c0c00b0260001340c80102d5000a52846941c2d030f2030a180c16a020400142c140702d03070031081000304a40300d4002c110460b00b00403d2007888001981e072580d061070002d1200d00981d1180b01240c02c190300612241e07a000c000c54040749850300b2424050b4440382850703401424000c81020040c810f0702d000101d1440310744042d00f03150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 388888920 1250 388887670 388887677
    0x3100c0212030c300f09060702010c021b04150305010b0a0b0a1d0d051204180b10050a091503060906050d030804080c0705030a0807060c0212090f060909040606030201 73
    0x1190a0008074054001590350350f400d5001444803400e500142d445100e203088003400596100c640210750301c03904e07034000c0e5806070390580c4420800a094a0401c1911740040a0740f0081142e000c1c40d01d00291640d1405480311451740440050840b181d91b113410003481407040501114180d0340d0382c5003c81c001d01a074170000d0f00901c070300f5a00058480301c071020340e80700403181d803a04400403125410b000140f03502c40341c64640c0320084140074004104104070301072038003100101940da55800d00324441c25031a082c00da4600028207243c1000c1e01070b241c00034004103505880c1441903d43c1881740d8256507510250304a01d0240e408184900c4003d035060700b000f4125075400b441040074984400510510f000804000317008205100003142c00141a00d00030202d08400c43d050391041d64940e00000d00b400c1c00b8520658140d900401c8107020701165208a00b400700d400c0c001009401164035104469004000c000c038824a0b0218004d15691141c070111060644010030220051419103000c0380207064602099001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 388890170 1250 388888920 388888933
    0x302210106080a0b130c0b0304050f0c0406061403071713060605010504050f0f0f10020f0c040608190302120d0e06060603130209190e030a260103060b01090503100c02 73
    0x902034081030481d00a60046250303139203540d84403a4424402907208084440c08500807001503800d200a01541c000d17032080001d0500d02ca0745c01e88241c508100030001902c640c0ca060002c112070758110150745064400030549680b25a07482505441d400d801c044c5070984881114104042c4070510b054882c0c04510078041000001e0311030004640d1070265020300750b04407408500760350321072070a094258890007006009400303102a41d00846c082c00303420b400202c00f5a0244100004014050115410300d0300242c0e01000914a80501c071355036120b00c18102102040300c031400e41d052502c2400035800f8460700b4030003155142c8401ea42c90000f0f103003080b0342c481503018142c0464114034025003100e00441e5a00d5081c941401582c0805c80a400c01820045d00c2c21118010790401860304d0080500070391070741010b15190b020031540a009070302050205c4000030515601400d02d035a5015600341920b40010b40090803000e0304005031600b001c05d4004582c50701c00d80040c80b103569a1a0400100d21507240d080d82c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 388891420 1250 388890170 388890179
    0x50406060b180108061801173d06031707111903080c011b0e091b0904020d14070c0203060106030b01120b3714030712240c030b12150705040302210106 66
    0x400c1d0030101e0040a270841010300e002001c0c12aa41c200002d6541c1140014030700d0341c990b02e0f0140f2540813042c0c4c1200480200300340c1c007841150407505081100565030b2002c50724404007000914001400014071800010500204030a4250b201d81040c101001001441d180703410740180c0480f500c40c211034444c0146500044000395038010882081e025030340c8940c2001805030400010303400003968910170300c0c1c0e14401031524802501c0d4590103040181c440418421a5005050a002c0b050f0084000d0606285920240e661300070004642e90032600c00000304d04e100b00c0c000807145008940c84500b0012044140d00100c6200004800200340e940c80d40d044480d03484900654590320a001c0130303407582080390b00f0401d1042d0010380e0000c50f442008107044012280c14003506004d080c0803c03401c15980c940e8500c00c00c45d01441507400380402219010003820040c402c0f05e55418407191602a0103d0410110340700c42c0c060425200a140e0007018581d000c280b03502c280540800b941c60b890510341c01d03e1170000c3c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 388892670 1250 388891420 388891453
    0x30515061c1203020705070f05041107050c091003060507170a0b0604031205090607081e1c0903030b03030c06040b010e0f07030213120303050406060b18010806180117 73
    0x44114110440440d40400c2a850b03251034003820b0560300c01410307000c1110340e00180c410720000300a407a40704441c0c150603040409000c2141c0b0312510700084010b080001a010501c00100d204861108845880460b541c081c3c14607182038840d070006249a0801090040194100702080c13402c2c00d90091001065541500b60307010f550400c03109a0f08854104818070128124128020100740a4180b2919000c011030114032140c1c40544c05a868040c04102030b5511484000c1203d00c0092131040d050030190700c420b1345c1e80000300c0794032105107981e81e6071021700070035020f42c02a83d641e450007416281c4072950308801b40e844100403101100e101c0d8154001007000183c0f40040d5008001c01d590482403540c8928040d0001e600c01400040d201c000741c50002036440724082e43c80e03403d51090b03401281c1c81c106850074000f5030300d03141c03c0744516080c140680c2410300103030b5440c507125000900c2c0803041903d514020954604d5104e034489001e00420340041000c41a5820000500b40034904552400c410400402c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 388893920 1250 388892670 388892689
    0x13140105150907090e0606070203070b030412030b01050904231e0a02030919050a0c1212020604030f03110706060f080d180302210f01060603060f0e0402012102030103051506 76
    0xc012a1100d003003032013512001c00e0302a50010300a041f003407400c40e040d00041d1908a560344003000b144000810001002001d804210200c01389040910102c80d00c04000780007401340142990041d551000c0ea018548090440c00102e207e1030506207900d41842a07000420740c4903181c0c3c9404004504001c100084003e00c2104d10945444001e000340f8899002c0c03c00b54817007441400d40d05840fa0354150004900d0503d5902c008126004c28945066aa480c00801e07903589890940150b4100e02d0802c40402c0d00b00c550034840f10700f030346400121a490090918054041d20138050261403510300301190300c406103500c0b50241c0303c00e1000c441441c000000100c40e8910440030f01c0d00c0e08061a10200014204045028407110900011081c1c050110b07100b10710385a582e18260b20240e442e60010402941c0600c1460058208054070b1448a414168848240b40000e84000d040200200c0c0d00300d0345440306007074000008005c040665407940d40b4144181c0e200a40b0007061480340301340012640f1841c02c0304e5031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 388895170 1250 388893920 388893931
    0x5030901061d01090b030304150302033306130e010909020f060f04050f01050c0303090604030f091d07090f08030c010f09050a060c03022116030e0312131401051509 72
    0x106607240c1c1c00e0040c200f01070070440f80011b40610041c080402c809000801b101c8000d4400d580058807440c140d020685092050f813095203010310703901d406044a4070b122018401582068450300c1d591105540760f0540150281d2025403810958000440c0440d10b607005203050500803030302c540e004541e1800304185403240c2c02074110f212900b008200200d04008140d0a1020707014180a03080c540d85820003411030b0f008030b540301850b4201c241000201500a08400001c0000d0301c1d02c000390f45d04140318114001c1218a214143c110102c0014800c81c1c401c1c1450805410a00c0b600e0062994440c0690760b02c3e000b9000e103007019424448107458561161140390701032604500109000d840a484460040030f80c521207500b00f5408001455640a1400d00d1701207110070300051340700c5890a041c00c51164412190f422081505000d06103003070742c0000003a2111440004880307400e5454502c038001003003c18042c010314207140342c08500c505603010351200d4890005004540c41a01d021810004018000c941 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 388896420 1250 388895170 388895219
    0xc051504051801291c1d0309100516080c0d030b0603060d1410050115030b0f010e01140d09030e0102190203062a0c03091905150a0302190503090106 65
    0x39038682018131007003038080b140c01400100340f60211011911044248407030340c00880702e480d00a0342a4803980c800000c07090360008005075050038411070000d000481c8842e161020030401003100c3d0042c0102c8510550150380c40140240e0f603800400c0c2041d10b41d01e05450301d601081c98040c5a041509104003124400d032801400452100c1c00d80d03864040810f0010700401c02449040707030a000c0d00010b449420301800a6007840d455500b02100010107441c08014900c0c014102034040900c140d0b08007044005034802401c00012011002075074210300d020301c11514a8103414036400c07400745900b020b00f0f4801500283d003940d40c680c1c0300700c002044104e603020000790154401d50000302403120542c0907200c501c00605468901440c14500a5001e4010760b141c40c80036000003420101501d0030000801c05e0308101103200340d600745001d001a50120400880c2c1e07001810000f04e50086034803990440c2d00c0e603d004a82d00d07040c0603201c600184190401c0b14030103004e41c038112012070f80310360001111b5600f60840341c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 388897670 1250 388896420 388896449
    0x20d03050a0e090114030f0a08070602030403110a0605010f06020d1403090f01062301090b0a120902040e0c010e0d0c1703041d0f011a160c051504051801 67
    0x650456003548459008001c100c0c182e480000b0590315038603428001c1c045103141c103441d0f604034400c160403c0a0f0310800d032904e501c4212014005a80581603c0205802150041c0c46e50788a081c1500d04001010000506c3d018903801c0f0000c00600d513000c1e9050f60749000940d99840e8030703440141c0c3c0d200c80341400203001c101001050f4900c03200920086501c400404180d680c0d10901c0f101d2a42981d4146d08075008150507281914018940c440700b4869000c0c00344dc0130003246117040c2660310188034102800b410060310b480c01c5001841d00360400c2e02d000703501400400c01da015000c841511849060109800600000b44c07107003040c9001d0300c030f8080d8942c1184d0310444081c40e02c160302041100840340015140814800000d00211020503000b50503904a5211340a25143c00071414400058100300311200480c500740110128000540d41d4008061104211180c51800e084c45002c03101d03401990700400c601103100540396070f01c005d44111082540c074000c620400c41102801cdc81c80034001e0b8052189000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 388898920 1250 388897670 388897673
    0xc0c0d030c0b1f0b0c0d030c0c060504030e0901080c0f040213090510050a0e0702070816030201050a03060f0b0c100624090b0d02030910050103030207060c02030709060e0f090703020d 80
    0x150410001c1040c9518030f4000c21403120840b0480c1c0c40382070011070204541c03400042c2803045400e90711840c9001c1003030109804000d0042100c000018140c299135000040c01c00d402441c414140c1c801c010180b01040da92682c0303150369032100032400d03409a2501410710001d8101030082e0b86244443c5082d1189250518000c4401403500901ca6064000319460004d803c0d10b40d41c011001600da142007010651920f140040e150107410380c050b202c0d5038060b504504540c0e500030488401e40b542464040d40d00ea0482d84104e018040c0c60308550880350b2900720014881c10900c008040c072941c600d013078503500420b1440c00c10480700342c2c1c0300700305254600c9081400d40204035500041d00e4a5541440620305481d60b07400c04e0250070050740b04a0b0303d54008240900d12104202d0317466101c0c500cc00134420ba43c11030750002d440d0545442040140009003811200715941880070310050410f0940800165950b80c10030118050305894644801d0301400206980740703804114442565000760031400c40c1d419a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 388900170 1250 388898920 388898933
    0x1101090b01140a030f03270b04170c041e060e16080c0705100501030201090b07110609042003151002070b07031101050f04020405100501080a0921050c0c0d030c 70
    0x800651940083c10700c801100140004481c0080c0d2402551010700c3d00034500701d030f55960b400581c200728507191034240402c50460035104403070980300111011426085400002c0f0702e0041e00c3d181c0e9690003810108984d0500c0014031720112700d0001d00c5401c1c44125a00d0410303034a02403068582c07040c1201c5108103041014054114a0f4015101881e42c51804d080b0b91103039420300300844075803a42c45071144010000c0d0343e40102e8001c050007505641c185800340700d5903110701c1c0c05241e00640d405244007080b1401659034070b45c00011040c0100040c03009400117415403560b1640304032140000c8444008607210581001031503d5117880f03440d001060f44d981042d10300c1d541600700750001c8007004007064007214103a0081c080c43d40248150344540580c0c1c02d00d44100816078500070680703054268019030400c007503070b03001c00801d8201e410568005102c3c0700f80c1c24124440440c40d500102e9140e4046d0f80d4082d02c030f9000c8001c1100d0701c580d600b038400c01d20580042103803a41d42140042d0025825442d0707000400c0c007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 388901420 1250 388900170 388900199
    0x1b0f090f0a030803090102280806212506171f090906020a02100b01020705060d0204080d050408010e0106060e131518150303090b07080c1c1101090b01 66
    0x1002400c1e5660035541e075840b1180c0703038000c039103983e00c41c0d401048495005940d220b4441004040d40c007148484121081d00401401d40100394034400c00c40310721030304400d00504000320342e103103000c0c000d07a14160900c0c100342040e9081310305002c40302c02e0980ea0001c1c5243c420700e010300746030808a41600c0143c641202034681e42c81c5480704090304030b07084c0703400080043c7d007485465201031003104056164414080080d0902e4100c441386001d150400e00704004581c4d011600f44160365049a0060300c40341c0030f1040074000d00407a041008544103130540304581c903402c04058070483e404e0030024003c2180441c0d10900f40e400611482010075014890f204541c900340d01d0700042020260380028425010a0840002d01a40c0d4043c483d80412506903240381da5a5009108202c2a04811059421b286990040c00702039039110703003048840041404000c11203494111900741460130103d0341a580300030103003c0062032081c1ca4401041c4904032040e003108044c00350700fa290f5000b40c810a2543c1c601014848000c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 388902670 1250 388901420 388901449
    0x1407032f0406030308011d160f031b18270504050a022d09040f030309021807020d09090e060402010e0411032e3209040b1b0f09 56
    0x48000340600c503600c071441903000640c0280c0d80e01405515000c611a07035090089074100518a80c4000c001408001880c0380c26844820b20f851501c000520380b00b240208245203a5203031103c2c03882c00c00648141d00200c100c139120800c01025542e25641c030549849402d40007641c0344111680b000320425a82258855580b25000e041924506c91840d400550750b0590070682e441c4440110740c15400c01d821907a104141c506040d280020300e802c0c0343c0c80d45002d461802c0c00040c20162152540c500319211481080070161514440580c1424034a0303019480708200240f810000305190b00000c0c8110050103000348842c4100054101034403150011217105d6040071181c2c2e000398544c00c21550700941c01c0019407007549411020120542c0949900102e146c9085407a02e0b2840486418003507018401805005412070031242400a0719403410012040030014025900c01480c4007000705000440b5030052080e4001c11401d0b81046c0c01c1d0346c200046000f007041009440c0b009004208550414104401894 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 388903920 1250 388902670 388902743
    0x601030b010504081006060801060309030e0904170705061b0702100f050c03040b1b010e030d180c06080603071a092101060b0a0e0a180f0e010f0603140703 68
    0x15131070360025032030540e0000c00708640550f2110100202c0c0e50000c0b0391405440503280a214881d0141c40040610b181148101d1203100030802140070441c5030f0354441c02006401e090380c2c1d1030b0042810000d484120481d42c414268041c40801c0003001030100496401d5507008040d0074081d220800308950000d8080c00510901600b040a02004007081015100810714a000a540c038812421050f9400e074031100c1061082c0e0402000d0444100b01205039010074222140010b07107540f41002e5030500c80c05106010300790501b002800700380300380e00c03400440c850300042d011140305654030718000b813000c2c0c44091031108030712007403080c0820383c580b9050700b0240545170035810520030018080e0b035084078a80d503c48800341c000007401642c20f0760004070407400100200e54510747c0c14503000216048810000a004036142c0d1003000380c1c6406020740c0410510074106000300500c0c054007070000d00070329003400142c481d9002d0000740b2102960000e1402d0a89900c4440140841410040100c48101030b21070510322 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 388905170 1250 388903920 388903927
    0x3030e030324090c0901080709030206210f01150e0a0918120302090102060112021201111c02031b03040c030819120203090a080309100207060f05010e09060601030b0105 74
    0x600080000d1030081e510a41c00049031040c0040c0d000e0244100c12034240900114420421204040d1040d500108002c0c2020704d056650319a08842e0300c050f81d00300070750008011404000c02111a0040c0c078000d0107854a40c5655200e100c028003a40009100d848070300c1500205025516211303890040201c2009040c0c540e04a84403107121013640e0502c2c8124074100071000300081482000c0c1c0c0c10742109212401c04502d0004188e00003034840f0701c14020a8404003040d032015086403180c104802c00000a80c2c005c11000b11030f85903107141a03000801040035031113038580a89003018079100300e9000c2c071400d0030480420361100301e11a869820040040c0c80810b03c107240080840d07100f10003055103108140c071480c00820ee4510103040c049034880381a080368818810021548000140d1081040e04500b155441e0394940a00f14070b001442654415020b00200f008010091107410004d81000e0350f59081c0204d80c0c90b0000d1440e01c3e0b40403140c0d408640e0121000c140d0550095001a00b00c40041c50014907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 388906420 1250 388905170 388905191
    0xa030212040515180607200f250608040b0606070f03020109030305070309031704050304080d030e0c0405070c060209060d09120e400603080c280303090303 68
    0x48614007100c054075660000c1266054201034803200961001c01404c0071000100000341c2e1940e00e4400514000510400c5003207000c41d1102c168101403442c0d2083d08035070381e00a8140b8000d45079111600b400c100c8040911802510360b00c0101014250b840300e54454810b540c130781d00c6014048202405054000104004140c0418130741c0e12036180c2c441c00b0340c00100b0302c081585030040458800500386010940380040c07030b40010350b1108001c544000703000c21811340c0ea1114240311f4110700c04d503888090b07148605001081c040e41c1540241c1c1c0741e1480e0074160343c1403001c0c04d420302081d13600480305000001c054140c030304c0016000d82d01134903007400c002d007030141031a440d1020782044400d4581c0564803000e11003c041c810307a0340403145d40fa818905940002c8564110142c20180f14003003100d4400600d000da040d4211113034140200300e00a482034100b4003d1a581b4280645268172034410600ca500568034081108107890b020502e401100d801c440721441815201100102000c000440c10503445461a0f01c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 388907670 1250 388906420 388906447
    0x1c0b0d08040608090601050127050306011205010e0c0625060c030506040513020603070f020a05070306090b0c160605040813080d020c01110604020d02060f18090a09050c060a0302 78
    0x5285109406407a03595062000c041c240c01001450384a907036102070010701c50750b41d001c600c2c10f20380b508004c0700252070003540c0c000c10001c030000c1d0490b68061094038000170304001c0807894452658084c600070000c0e00c8081045989030305c1c99980640e0000420004c04c0c103850b8004000505100301100460411b4605075030309015291a0120100002d40b40c00620800345020302c11250011000d0488000c80c0640b940490001d000082000c820711412000c000d182d18020b10244034007130740c028192000d032501e900c2c22000502000d0b0050303981140140c000b420400303000084480c178a4000030407617a01901d6665800244c071000740100c031906424810092151070b4211501d000d03119000c0900154031114030020b10300100da414482c1084420f0001e50b40f800004103046410603010796500b8900d01e0340b8008501c5c50311982c4005031001000040e011740307007100c0d11060101c0c070408035280d01954550041751426940138102c0601990400c003e50080351501c01e00030022014503090250070101c03804940d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 388908920 1250 388907670 388907689
    0xe19020603250206041a0402010909020f0409060b0c160303080a05040309082407090620010908070b0403020c060c0312071110050615120112080f2d0f1c0b 68
    0xb000540d011900344800c01c00343c1001801c9441c03c3d004001c42d50320b06500024500c04c0d0b035100340d0105540c0081d00d0301e1041c1400040798007506a80000307100039551051443d05541c80350b84440300c83c0c01042004404001d01008a40032030340c0540d0750028036150654000b0040901a0086052010340e441c0002c40d400180448824052143e514440140c0e144074002060720000382403008005090341c1c01c1c060740c3d0b02f11224141c505021800c41100181481c480b40c010b0030180c0d80070344840c0c03002c030700c5c403042000c02c440191049200e642a105044c03048002e010300c1703000c1e62291401c148c0042c0a9440c80500d02c0f182c2c140c0c01211480d012000d100d940309a942014034034044071082c076449000300300090416821035074030b0f0858404190700d0100a50140c109400040c00b45283d1064005440c100b4072100e00c0c19281c4401920081c1980c4641c0342001c0b0746650350b151a42c0c044501c107056401c00315180349098174415800081c0d842d00d000f015100c03801e03005400d21501242c503075940c002101309403100c6252 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 388910170 1250 388908920 388908991
    0x1170102093019080705010b0402040e0103050f06041e11060f0403060e060105010e09090c04180519080406030b01020717030c0f030406050703051602090403120e19020603 75
    0x10010001901d604602012141d1000d9180690054910349066141d01e0f0705030706042d42100c103d85d2103c0652034420301610407089400d030720078008100818114803030900c0b0f03030489228a0445080d14191104940c6504044030b005d001c0301d240c03851094000607400d460709400ea22a043c200100020303c000201c02e90021400c90100e98000302e014000c11005220703903000640b5410003840150b141100081030140c40d840c09038014101e1a0110342d01100030000b1054403074005005208042802c101d203000510011800e4a0510507802c11b400c40040c01182200c0a5411900b02c1d4902410690160042c00340700c20304504511400e040001e040c43c115003810321545400c4055603a501c4845160307840c000c6400d282d00060f070003c1104018040d0084100c0e1801545402c2c40b0380c880f00c0680601401108100010390812103031800c00082560140080d0b58450300c0240400c140e8540c0c8010a642d5124001441e000c0404a5141030141c60135802565000034100130442001a1900c144070291203081c24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 388911420 1250 388910170 388910209
    0x3090a03080d0606030e0c0411040806010b130b090f37030b010f0e1504270308100f0e0612070306060509011a0313080405190e090102070b0117010209 66
    0x14981080c00c2c80e40120750040206181c1408054405941355403901154404d6510640d903071104982c83c000301b1819131b0000c000c0f01c0c054800d40c2d0381d950184401640200c2d00580c59446880c40800d10311000426078685002c00f0f0400c0b125502907a0078007220100b01c04010b00e4845c41341d00c0713120100340446058079008005441200146140d460410b081c488180c02c20610705103100130500070740c1a84400d40b40e0007207100c0c1081c951000c43c2d10100d00141240d18010440420584030440031103a8000030000c0030784241e0b500c10044c0d84050300000199682c0c02040b0386948041400c0000001001d0b030581c1210b0000d0095088508896410f0f2812905501c00c0343c81d03075240c6104120340d103002c0058500508400c1003103400780c11080304128091000410190307404c410300302c00034148005241900c000d4040900001000c500002640014401620620050b2006c0f5400240401030600a0361040344c1e0220492520b079007450b0a440c143e03880101c000d40e540d0b50038002100503031f03241a048044c1c03051648 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 388912670 1250 388911420 388911427
    0x703052a040b1308060a020a0210051b070b160807090603050406060506120f01120b0f090a12051c02090609010c060f020703031a0f030c0d15140105120c0306130503090a0308 76
    0x941c585c1c2000c42c01003c510741d02d441400440d21094004c160500c1d5038400c00000541c0e955642d03003d2408808020840c91640f4002c508a8100035075040c001b4000d051580c0c0b0195034600e2540308541202e8100d1340000091000d09003086018040e4001517040b0b88a400045080c58031030b40030411541003d908901103180150501c851032030000042c50160115060b0100c10040c40d8846100242d00903010b0120402414009a680c000c113004011800d540140070207101c203007400c1c0c01401138006d21148000c0a01c25544280300d85218803c88100c0030700908903604040d45880103403a02000940b0945809882c0c0821421902d92440240040c03072003900c0004160300552400d515042101c550180541b00e620a180c07010707900002c07841c00d00c00d0304403a840904d036501d1030305c0c540007041598446011810404055291303030220014a058501c282e425140c03036003032010761b290342d2101103c400303805810080109080d4030110060422030350056003264604403030300010980c804e04540c0700f55240c4c01c1c0407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 388913920 1250 388912670 388912679
    0x7020d090e100e04030203190504050f0913060c02031c091e05070302040c030e0303040f050c09070509041a030a0605100927051c05040603050703052a040b13 69
    0x44508009400c00c481600da030741c5490440060b00000718020044940008400603007010310800c112454480f0043c6000c0c044260740101400640203402458810309480c040701d6814248003102078801c40309140c2040b22640a03441b4000207040109002c0114003042005001c0300208880c00c0000c021840d000203a602d5603070a1040e80b2408400101058181403241b98000c60000111a03042d6034040300e0000d840e4160500690050212500071000d42c00040208028014203da03641c42150290054540d68007060003000ba0000045504c40301140c424401c0c0d020504265000b071064142525801060150020000317141007001c6108486443d111001c01c44102c240041c0b050050800e400f06100f032070710107016003400c210441c00985004c603078031400100380a0100728603100101c0d105144c00b40030f910007200400c194018040e22020a06120100c1c66280c82449054843e040f0502404005540c1d00d58002048d1024075950a50070402c3c00040780181d5164024501070000402c010f883c541740 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 388915170 1250 388913920 388913927
    0x11090c180d02010e190512030c0d0f0f0c15020309161719020f09011d1006200a140a03020c04020403050a15020705010c1101050906012106110307020d 66
    0x604452070051040340340c2580141d81002c00c5080c41c60044404e12105c5080c2e2043c01c065901552203994061410b1003601141341000c0024642c02c04440140d610036001490151403c82940360035800092450348000c035410f01c141210500c00e445207060520f108601c440140581c0c00c1910748110982110046880742126804403d0041103040d8aa10358030340901016030f00d9006801c401c901c01001e0760392401c115034400d68601181c181c02840f041e02d6584880ca18001c03000041c5144c24042104c03004184090064100314040300c0440d82c1e0100702400090352240d000c0c02c1a82c1c1c3c1c0445101d000800f00018192140d48590140b0601c0201035007100c50400928040c1614034484c0220302c100014004110082000c00c00c054000c80050504115600180001c0c402c800c0003030000e518081c0e810031800c1c2d1000000d106007100070000d00040e00c4007584591104800c0c4a406d00140c08140c250424907000b803120820103003d410b0000d103640f03940380e8902403030780101c0356000182c000c7c1c0e4920044a40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 388916420 1250 388915170 388915207
    0x5071505180a0201080109020c07050d030306030215090d0314070c090b18090c06071506090504230a0201080703060801060807050a0602030315010e0406080316062904050411090c 78
    0x10298010405141543c0018142c414107004425025030001641c1800441c04c014100c02458040c5c01090810002e0500030000c24650104a110700c02c0649813440c003550304c10a69074001c00041140350300c0780a0b96801c1e182c0a0070764400000e401c006204030f8011481e1480d100700100003280c00801c1842c034017010002c1c69010a0254101a080a011300c880d0000000340d04001c10801d4403030903030710100390070804005213807807104509843c02c1c503002103004d0550b41c10550040b4400c00d040c2e400c200c000d0314042a0300000460890701540000c401c0740c0958030480715180c00805c80e050006c1c6a686401110b0300355591a0030a0205901801d01004541072405140009200d2480903609508040100c141001088001a0f0410842d0480003695030707030b1540301400411302001101d6846e03441042c0a003a00115a07001e45120b4600141d0221140016008101407030030308940540c032200e10b20800c40104800380c0240e034420b01072002070250f03441d2210322500864140c48155110788804054003080ca5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 388917670 1250 388916420 388916461
    0xd05161b05040b2706030312040c0810020711040c03110d0516051e0903010204091e0c0807020a1509020909030c060a060b070201120e011d060c040e040803040305071505 74
    0x4031000206180680184d041090301100b4580c025015155280000e245004140401002c0300f031040c00c1c0b0080000f12020101242c400c1c03400c3d90901c4403004462006c0380507000020307081c44201c590000180c0350581c044000c01c107c07810000b440e40c080059100507900b0003800385002540d1081840310f101c20018413190040781500d0800d01c0e18028142200c5100b00e425501c10b500c0b8008641018559800e40503035001d4516244100302e40154284100040c5006d00c403a1070980b45022240d00015219402091141c40c654000f00b07003032010341d84c40500d07191001072801800d43da154501001681d840e11954000c44601d0020350703c078000c01d0052424000054041d00415107000d03c10002a1030420545520580900307082001088030701205001c0e0400015600b895480d00460280d01c2c0840c8005103c41c0c1316140c1100d26990f103c00b400480e0340726501951964411200004000450080046da03000781320b40f4180741441000e958034140013104400078203056031160f0030400d4049546242c05c4c1d40741c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 388918920 1250 388917670 388917679
    0xe0406050a03170906030423010615110109020d0804030201110114160c1b060f02010203010e040f08041d0f070c1112010b090a020307021203090d05161b05040b 70
    0x60324140c005004800c0c2032000504405840c1c081250001c5003005503000310902030b100c1c565a2820340741010180c60300200e914607004400f640d1829214051141360b06954900380c0311840891510015900d20404055104241d901c4900315001601e03050100c1c000b0f5441600065116401c1d4400940103078100408045140c2c90314843c1e074070f80b800f102c0d205600907044904c042000d021805080700c08048250016002a4130200f8459a10745010b0703460701181d0040c1c1d02d140c0264400a0304a007070380f00a106075000e04074500c0208021034405408400640d101d1841a89040d554078a8460039452103440d5850801c0060204055808090403c59002c0024a401c01c0740e6102e0b13607580c5c03135030106071103106014112711215000ca5110940c484d6400d200b0080c05a03102d40341151000000e980119103804c01401002c101031340d104000d50590780540d030403c015018242c20383c00c0031141900010390304581044404800c00c0494410b91300e0f4000090036602d8003603414284814801513400c01d0132001d018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 388920170 1250 388918920 388918931
    0xa0c1706061207030807150e0c04050c0c07031b0f0b04030302010b220510120501090c0f05060703051e0c010e011a0a0b0f04030203060f070f020601120809011806030c0e04 75
    0x2c8080850b40c4410b44e540a02265102c401c5403c1c00c80c1c1501c46043c103280c038a031402d0789a44501400140c020700480301128240700d9039075900321070300e201c1c0554403210034180e00426052000614030a00c00c0480b000d2240545400c0c1d81e9044180c0610b0314981c030114a11a0000d02801410703420700622103142019580c0c070031a0340300d51a11100c10907182034a1300d04e071950f4401103001841200d0300701004104040440d0815145820080d00078400d8007000c03683d85191000004624500e04550411030303000811560030410140c41c1234030223900100d2229424480034100d000700e000d940e0040d11400318814000510194007010103400c540c01c03a0b4480c010b40011980400c001d40d51100760750709407a5129a15a01c03400320b01d025140ca4022600000d516020b0701e0204000d41200d1034820f881010b0179900d00b00503900030441aa12010280614455001e44407031110205003404006c042e08001071401e941c00307440c1e00e21025107840385500f0420020751a2200f046103a9031001290b03041e500c00315000c104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 388921420 1250 388920170 388920199
    0x30f1b0f2601091a040203091e0f031e090d0b012d06031a100302131406070b1e04080406030b010513030b04030210090804050111010b010c0b090a0c170606 68
    0x84403014468070f52802e845035000d50010244102c2032464000240066440c0e081c0031240751340711030804408115411403003241c3c00c4c9009001840010905003200914a0400340003081030740d440c1c03078083c514258201000701c0855071301c4422803c2e0581d4000e00305806a94145150a800c2c1c800100342c40b190a0204004c0510382e40b80359101c4070844005040009100511700800035a2041c11021f442d031084c40c02d21003508441d0540c0007050b007124070703041c200b42080e1100c0403141d0030245c50401c1e9030401130130f10240c1700040c01c070706480d80c1021051030030fa90607402c2d007984084101c0045404840101000c07800b0020030360540280140780c902424500c0c1420704840c510200c03030788180b001901444140021405041c0244a104500c10700044103100c0110b05040c000c2c6564000d00c1910f0028041005c1c4200180041c8218284588160b42c0d482d040c000c07e4403081c11710540904008064040d01900c800003413042c0520340000e210081c113840c0303480c16240d0814103110008004074003401c2a10000b06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 388922670 1250 388921420 388921487
    0x90102070b070e1801080c041b05030c030a0209060a020f1911090c27010207062c010201060b07050a0b0903070308010303110709020a08090601051f030f1b0f 69
    0x2d5011816140c540341600035040000e880394007007441c1200b81c42c5000000302d80400045100300d0740341d409503001d000041c01c00c0c0344c03e04a15445080702001903402c3c000300313a0481d0a40020750700000c14100c05030510040d4400280c503684000703041c80169110101040204c0720920043d1800e04607101a07500c000d500da02c0f0203100c501140f010707034422910000020300e80340080003a954890740c0008002601c2a031421040c104541c4451017a0251041003000136030288241d115418180141742c000d030004030066400c0c85101c01c150000c5040d5500e072000421460284405401014001c9004100c070340501c0c01c0044e556580a00202070380c0d0410003070613002c01e411201e15030440360701d0716003268042202c0ba0a582022015080400c0e150300000b10304640c04d41c00400c443c00f813040201950016641c1e481044a20300103210790a04c2d5550340c1003a9045c09000360b11072106402c0309100422000c9510725804060100d60a1900100b0240072240c030040d9882000b0110785801c203540344440c100c5030b24540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 388923920 1250 388922670 388922693
    0x5060a050f07020a08070b0a020609161e0305161a03070219050c09010b121302030c040b061b0105090615010509040c021507081914150a030804030302070e09010207 72
    0x3860984000a9110115181d00e58040c00034000c1d117007920626074139030b8000c4a29501410032000140704400c0490401c910110b00a0058030117041035141c06880e10300c0c810000305400d820901e00b092603c000101092061249030180d9119402070100c203802c2040d8044400c0100c0076100b1010400d00400141d03580001e6640d05c8180f403200700340e05104040c502149040110030100750005282030000661049140140c903032480394150300d1196599a4601104102c000f54001e0340c10782c48980301c51034900705a48180440c01c4040e1a070342c030b06141822030b43c2e030409920005004682d904c800b0855014030900c081c1c2d030441c1e40401c17044003041035100000c0c0540910f2182030321031665038103603c1c2001e008112010b1200140c1e2a014402d15150f000500013103400c999503200f50903661030014403402103114242c203440c4c001c01c0408407521124074240e04c42496141d81a000300e03400c00040040342d072050243c00207510070ba00034000d00d810880342c0400410098420b11480e0f005000c2c000000e00322100b00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 388925170 1250 388923920 388923937
    0x3030c151006020a1112100216060e010506030a03030203180616080601090f0e0709031a0901050601020a020603160309080d0b040612021e03010f0204060c0c080304030302060c07080904060b0306040605060a05 91
    0x1654101c6d810b0809141c01c0205104c26491004c0c0f0001d1b0000000070340c855031005041c0143d408104144e6100300b80d500361403080390402d5064000c0b10400c400240250b02950b0480d07956060224010310b003036102e03854084191460030030024454000c05087d5440f5100680c030500a20b01040d8142c50200c0c0b00064400034040c07400350314645400210014402c200b01c8004540160f0100e4a1f00109000003c82c1c0800f5101000c1ca9420706000034055400010b1550490354007520003455a500e640031148046980310040082580b110405004180c001010b0880c56054540c00030750f0100c01c0701000210303880d56026460f076120803a9100d0140c0c1d901e80100300c1800110030a071411030300b010700183c01418490b5484406034404540400e034142e00c040000031041c1700d400c006400c542c45480341d0f5075a00891000a005030f22000015010f181d0361030207040300901c1500d08605040000b800502910800e421100e030b241808410468146803601451000b040c059403005e180003503400005065200b0f0b101d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 388926420 1250 388925170 388925179
    0x5030a061410030908090a06082410110c06030f0a0b011b06021c0608030702010306080102280e0a0b190e060f0a14070506180601080d0e03030c151006020a11 69
    0x160003e2001348403c540c4500c10081107100d5540e1100b230060030808080c0d48140c0a001c0752107002c0b55056490400541d6014002c09802c400c86c00c10408558880c8100f1100500c4d001e03441c001d11940d150f11010b140030b11903100b00f258043c501048114111000c15460604010a000c0d001103980c520100801078150014005641c41c001d070b5040d0032481c040224041981898440002240070004c000741c6065071003641c05124003542d8210b510300743d00130404c50b0b042d0800324a0050000d9120078001d500c1c15822410401d4030085079034001404100568000380d00d101c00026611466a44041080b0082034582070850360a030981000c55824094026848407600001820303141090048441039a103d40c051303400787d50388c54107180c01603e440c0b003601c40103100305a0b041908078086020800078180d0b8100d0340205001d0762281d900300c0ea00160301d40455003602040040c45070904052028070080411000100100e090000d0020088201035128504542200404c42c002445000202010010484 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 388927670 1250 388926420 388926431
    0x20f150f0112060b1023070b0a18350a14090a050d080a021615030504020d061802010806060f0f0d0608060907061704050c120102160305030a06141003 66
    0x1d043e1000b0031601c042039038490001e0340c0822005922030078006070b2944001c0081c4c0c0e40c2c0c4400c00001d07103500502c038000700500b040300001000800c41c1d0348040c00142408000030300b8082251503461144d0701000d0b20380708507102c0050210880200702c00781c41e8014140ac1e140c81c030300410060b0050070b1217181c40c4a0604100001341002e001d94400580001400c0b0050504e0442090b510742548503901081d00c10026004103106038808036014045001241e50003070b404d015940c0030400480c000d00c00107002f01d90181a1445240c042001c6210b6042d0040515411404440040c00058160040100403901c280001c01002c642e0705a414151440c01300504100e540703800018a41401400c503035042000745100b540100041c0100c009104011900f40391204040e01104100ca00700ca4402107901404680c003262050560b410006900600700b040103000504003000010440c0489005a00903400a807020091100c40760951142c0c0008080f0750301c0300c45401042d00007250703000c8904540c0300141035841 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 388928920 1250 388927670 388927673
    0x10e01120e0705150408100b180705310b09030a0b040c080307080406080108010204050a060c02041e0911040203040c06050a02070906090228120b030f0d020f150f0112 73
    0x1040440d01801d001480301c0c40c184801c04c00100f154000d0310600802d84141001d800384141c80303100303c50000e0b002500710640c1b1a0300c4030311401c02e5a40030300520204401007081c034110301a031692204a2040303c0d00940f192592052419080c00340c2a0003001780c0c828200038200080d03600041682c102a03101000400c1d43c5c0c0c0b58100301034014110342c05074000340000244507041100b40002001520714076161b034580350b600c030b040382400c034080c1b805031a800c210544d605100309801801600c80720380c4001c10114050b141802c10700303605004c2540d00003015444111040c204aa03e00010582e050142d400718190b1910352982d8400442503c1000c0a000002409064151003400b181001e4032900d0780500090344e55204940003903100940007614440c03603e00d0f09200200101411001c0000741c0e0345c1910209038030034200001c0210300400380e0700d4441c804060002a5090003000c4403c3d40907009042d0441000c400507007010f40c5840303055801001c0008001c0f903c00c41c00e070000c0c10349800007444002081603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 388930170 1250 388928920 388928923
    0x30105100905040f090c1d0a0209060d06151b050c1c080309060402090a0905120a11060901060611030a0822050a0f03023a05120f010f05010e01120e 65
    0x1035802c00307900315040c44040d00c5800c4040d0071076110b00d0720400c4c409955603030381c0200200640d1081089240b6100400c003007a808680c44d0058400054010001c619004044401108032549641700d454050050650340402c5500f02003402110703c10301010b49503000301c61b9201520340ea00c04118903ca072080480890108880800101c0c495034400c0d4860b950f401d21400080d03072007804450480c41404071000060701d03142c590103151300303456110000300104261103009000a070840003058040004003170404100d003500f0080c860043e00b414000282080c10110300502c080c40900c003003e42079208004028020307031312200480e4000b610000301507007504d0502c40c40c0022040b8260290140c0b00b41c5a4071011710961203140c2c200d85200317800b11170714184030f103e0144800e8038130403544028451070700040d000d034040f4143d440101c00540c030b810344c03520b80300c2106403110100c2175603404062031043d03006011402c860150038001c0c040c2401d004486d1099100020300d130789060488044810b44507070003900c18840 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 388931420 1250 388930170 388930187
    0xc090b0702060315130b040b06120a09082715090a06030903050714061816030201110a2418020907030b0409080a020109030806040e152206290603010510 67
    0x1801018207201d1724610f03c10401038109003080c1c912461a20948060034509002203c020340300c0d04071141c07542e41c1e50316441c078014440007005036003a80f000c1115402890b100b00c0a5041b42918030010349034224071105004944024101d010360b55481042a40415515800b04400329a0a4940819400030603c1c08580720b020310003000b00001c0105150419010010175024800c00c8c4c070441b09044110fa20450741e23a1000f844125030b055518030070040c0055440f409601501461050441d6541120f9945144901400c1000c4001e01d45010b01c1040402015001d11070f4030300c0100e414809034082d250000780c020340c03001d080d11040c107940d407800d02c00d151559006030301c01c00c0d000000203444845052001e4003a1122100450000d142e80c80010000c0c03803e4452100d030305503140010302c50f41ba5110341d5040000d03800b60003c0c88000c040340c0800461440d0001102006200345000315454503c8100e460104e01446030240c48015103818442d0151107440541c1d0440d0422218151404c81c181c600351194030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 388932670 1250 388931420 388931461
    0x50609220f020f0403031722080f0d050711010c0914030a0b0709170106030503030f0c0d23150112110c060a1a0d0b04080307091e08010c090b07020603 66
    0xb40041035034400c804045001e002281d0090300d0711038801c8000102c881044504580d1130104011070385207419291113507500961105e2091a40d00c0c540b001c1600d00c580281c0080c17000c25145921002046900c69002c99800220030f40e4000900c91000d902201810300505070203a20019200149041000c0d0f5081004000c0d4a401840051003401c01000007400d0351801e00a000803251440304031600a00140300b00012240c002018506640b00d000c080c0c100b00c0c074040c3c04102510424444a41d12622900c1031041b6000c0041c41c2c0b1078505420203020141080041c848060f4070650003900340703581d030000c611255441e43d002c030002d9a02400d5502c0c4e421401070648a02c014071071030040000c8030501e81c1c000c0c82d10880f6141c0049001e103001007045070b400288180240b03007190141c0481c0000b803c0b9806541c00010500700210403e88820040021251000e8148954808400704100c0210213100c0c00940c4546850711070681c5050118507070052207045d00090086a00100141041d1040000c940c00c91 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 388933920 1250 388932670 388932701
    0xd20030702010b0a051530070503040b070c110f0424080f06040206070b090109060504030807030c0207060203070b0a0f020a1101060b1c05071101020a020d0905060922 73
    0x2400c0011009000f0070082c8a140c1c06400726a0740810503140050718400200c0c0160207080c0342c81342181c4500c1510007582d095240401a12500040841aa8079201c0c1f042140740e6401fa201c0c0340c981806001000c1c051300c2c000500070300c0070445012030303401d6500301e4444e282542c01120031070700f900124000f010078032410302c0180310f002817500508010018020131149003800b1510b480340e1003040380351115030948009501090070483c60f40000e0301c014582d940041c0c110f000141c401c00d030b43c40c0c520a42d1411038080f0002400601080461900740c840c03903a042d41148018002e580c1849804ae60324031451101030402c020744000260442d0041d080b1000c205c1c500201552918206100580900203402c16400030354241203000c00c2560405040c0c030351a02107241451074a100c0c1145000052001800103400c000300c0c4460102080c0c0240010301403039a0faa4000c00d101512404020701c0002c145e000b46100c0d19007081081803d5540c42b80047c1400303c48078140440702c6440e0003074001003c1d03940240181 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 388935170 1250 388933920 388933927
    0x51011030c211602060603010c090e090c04051e16080606090301090606030515090c060304033b040c02010207050c2b060c0807030209030709050a20091f050d20 70
    0xc60f01d60000c8200c1c00b0803180c003241c00320784402d020142070b20744040707007000040c0020400700024508000385540200c01001540c100d00850004682514411210303c24102c02043d10381e4a03c00000c441030b58015001a490300c50301c00e00c0d54008008000180c01140300c1d20000c41d140d0041d9400394800c0355299817040c000c100565613803030816141c8000e049401008640e210019030340b8480498482c009840051180e855640c85075015208500307a10301e039280c11604007100c081c85444c08401c035009103848403507aa8101d00032004200036114280300140031a4014442540010000645522a084115440d9840d0080c1442c0c44e045d0001680200030400718000e881d20a00140340c6c405007038588e40d9607550a40783d50340707402601030b881082011a0980c0c44000c04100d020b809500c420380080507c5400704009188507940d8404032480415200700c82000100e002841c50920181c868104861030200701120340c00c40050300342c1c0514031000d1030594403403c0c8202c0341c001a0358100c049442c02c43e0075986 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 388936420 1250 388935170 388935181
    0x5120f0c0a140606030d0e0d030c0602030a1a121207080f030705070b011401081807050409030504210c15050714030a030501080601050604061209020303070b04051011030c21 76
    0x201c03507580305108030b840d000c2c0401140c1c041c1008210365048450940b9081d40319003950b0280155012202c0081d02086a4551030780c0000e000b40c0001c5014036a20540401e6001d4034041249180ca020700000344510000d00090b00300c00f0340031506901e0b9020301085d4030345864050078100101c0c45444c04005852074000b040028041d040000b03048440d008415901c4560f0302e0b12034200d90303065004945030100c0e011000088a05513610084803011030f6034030a5422482d550b5006c18244c038500d050032400320b000440d051061421461101c000c400300c42c45007141a1100b034540c0c00480c80c07a4003840c603141d43c40080c0ea070301140c082c3e82102c0d121076101c4101100030002a50301a226040700040707000080c14800000f903a04000a0982e0580300000e00d076038078051406109540c00095481c0e100301103a02c4212a0b4050780d0280003400e16103002c0c40801c8010702c3c0520307019003012251010040c403d4545007070310051007034040a59600040b1045c0c803d5448915500b210b96650340d000c1d8400c4140c0d082c2c401c110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 388937670 1250 388936420 388936433
    0x90609050d060f11040306050a0c0e0402030628030203060f01210804180501092d021602030a060204180c05090105070321020a0f170406110c0304031211030705120f0c0a 74
    0x100c82c01010b04200c546c40d1101249c06503403a040000c400a41603640040080c5011741c01183c0002c0d00406e080b61001e045403103800742c03102c2c4950003003071304520032805c1080d4141840000c1d17200d00d80d55158403407581404082126040f44540311030b6686106030000c0308008424080b540901803000354016400c5000a803000900024011480440d040017192210100c02038902c0c4c150302a0380709522080c0710f160b500d2600a40210900711100c00000200101584051101c108cc05000e0301d805640d4609005007000440003520f281001185001c848004066019054510382e0009190059641c080e600302110001e01566075200e005186070302d200c81c0f850141d40140601030f141c2d01d07416011018180c0940d4054880840c0782580c1e03003001c002800191183e030195030a613440000c12401d01e1a0102c0441c550303000b9810032686a02418451079035103820116040d13085d9240c1c3e005614115055a4043e101c021800046052600104140f440046001c1c181c030000584d02c070803900780702c3c2c46003002c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 388938920 1250 388937670 388937677
    0xf030f12052203111b0f0f030606040b04200703170106052703030a0201060e16080115021507020706140405061b010e010c0525210512071d01090609050d060f11 70
    0x41e1050030b6900c40995a400c11f90380d0841c400340018003420495507141c0c14400500200c6040030350007503540075503548942c948034504a009109601140d100e068928000c0c0005004100030210188014010061240c0c07010403146041081c6444010f249007058880e030500c8103020485900d404003090402290343c1c1503200d002211504070000c6032541350701140304002d0700c5a03e00640025110401407000024800580200440038412a600001e0a442090911800307a50100058000950403c102507102e2070540c3d043e417041480c2840c1900e003100042da04d200303542c182d480d10405150b104454034002e500c55200d56007180003d110024032044024940c0e4040380d03c2a403100c01c0c580c8028400101188040c40d0140d100681e8001c640c2000540d00c140411695010700300b0104001c482240c02514240c0d41c0149455103544101c0c40d810031741c01070208407010045041043d4202c0c10011aa4010041011a031003500e804510049a003003410140c07013942c11550031581005106504990b441004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 388940170 1250 388938920 388938973
    0x408090d0c17120903030d0e07050604060903050105010506030c0a030f060b0301090f060b0702010e0607260706050703050907050114070f050606150408060105011b0f030f1205220311 80
    0x650303511030100b1103d2a02800707001d510315015882444204450041e40e8050704000b484c400840c5c0c0032075607600c00100701e41d015800c02000a00881030402c10044240582d60140800b2103a071400d514090f50040170502440c9584001c040e201c01c41d180700d4404d0396000c000640300304030101d40e40390386801c2442e003e4810341c403072030448618101001a2038681c000c140d0303010720b41c140d4403d22150b00d000104025274211083c141c42881180c05401c1090078180032881c10f5080d03c10a0985030003550800300100c03840140101c060604200400850701800f02c0e4401c2942d100f401c01c40c51610310040b00b0509401078a100030405030f80b040c801003c0c0000007400c2c911400b01181c844840c0c81d410741100c800c40c01588181c04013948080010721483d0300078180e580009908002010101942d611030844414800c04103a02203803100c2c54924060b9480f6440e408060f000404c148050b040460700c5400040140034407030305101c2c420803050f003014820710110510701c3e001c40883d0140c480502c0303045480e00d410740c1c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 388941420 1250 388940170 388940173
    0x60c030b030c0d0f02010804051207030c0c05010c030c230610080d0f0914010e13051f031505090102120114190b0913111804050604020705060408090d0c17 68
    0x16482d010f03d060521039800a40c442e040c0d100b03510682d4015900c42e18090b004450a00803094102d07a008240000b030490907010380c2d00c61805c80a503003840616040190040c0f81040700540403240401d41001c80e200c0030b90b5220f007518030b680f04c03060b181d060906190f084c4220a80181c0c001d00c000001c00d040e505003070301c00705001d841030041031541c01e0b220320600451543c081070418404201141c0380c610048803004040c10104510840400000c00032503900343c1c17004801d41c0daa8203002c0c115510f98500b4038000345c0c40260741d46040c216154030340d0300d180602580400f1503d49000601c281e40a4040e41c007004941c10b906502561107080c0c0e6000074035000d2103203003d110708586100300c0c0704409401e9400c913200b0800719460992200e00f80122448a0092001c119454102058108031441c00801400764031700c0441c55014103000c100001e80308058005481a80103010590220f840851100c0d0095804038406030740e1002c150108000da100c400001d0441c3d100d101c00005d9041009502d261955007010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 388942670 1250 388941420 388941433
    0x4120b060102030c281a0f010611030d050a06050a03081b122a0d02031308070e060d060b1801050414040b150d080f071a07020307020616060c030b03 65
    0x400483e0380c1e00901c84c82101c194080c84c844030340555000070f80700c1816000241c07040059816200e40200341440000c15048180700030401011524003000c1c2c90141080c0c0c50170101e64114400c0141c1d8a0241c1c080d0303030340000d82d1040481c010100c2640b005009241c00380120029503643d0504082a80090f80003100454100410f58000080881c0384120b0945085c03a0a08111002c084c040052100c804014080c081c20403071214440d00030000300c030001078107a00840e5243d4071428400380e010203c0e8030000d5039501c0300c00203204113001003025660000090f102c5242c0104141031030000b80020f40c02c05500b00b0b00800f0104041602c4008003816035109940912480050310345442100c241164040d0211603114040b801c00e03000030b400005101002420840c01d0500c40d2619072441d4400c56000c900c1c450001564010407503201c4160b00030380c1c21803c20000d513151481c0040d407288900d0400920820000411412004220030302c80c0821341c106a00b0410104c60a0000c5c00804802072140e01c00e00c20780 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 388943920 1250 388942670 388942681
    0xa020c0d060c020f0d300f020903120c03040605031b07030e21060a0209120f0601061112090103020d0f0c12050606130317040509040b0613050603030313080f04120b 72
    0x1910300195540c0c2c0d48101004000517030315a10034006488005d11240c140c548400300d903103035000e030841c7d44450700401691200000704052820418905280d44007100340500e011a14011081e1021266a41401c66881c3e461000e40b4010b4074081501850300500400c8040c107241d8404405410b40381c0c02e480c0080d22002d01e07188000341c082d58444005007503121200241d01441e075600540900702002c3c1c510b00081c5410f004090900c8001c51004003e81c1c07050b00100059036111044003100c4051401400b00c84102c181e0800780d900c51248030720305040d0009900c8441610540c402d425504882504020311901a0f4000700610144410240ca2a0800010880c20326000044842d40f00c291107031900054519510710002000c7c02024070040711090100041036110003042900c2107209496951481c41d244081240c1c8940b00c0e02114841442c001c02c000560303e002007100c0c0c000c0c1c2e10040c801c00b1054246491200352103080d40d070200c0010003150000e10002074101012850f84500810141036030746 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 388945170 1250 388943920 388943923
    0x1b070e040c21060e03040909111003050c221203020c04060f080304030209100312021f05040314090d0c0801021309090c030206031005060316260106050a020c0d060c020f 74
    0x40307282e42c480e00d000354503030a4006501c951140e4039403003a010940b03080035643c152510440d8103851099866900c031500c07280e028a40f101403002d004125003001c10030380c2031032880c1d000c26024010001e2900407244a2003c26442c40140c1a0020449100c403610705003214036000b03440360380c46440b23140240d0a000000ca201c4c001108030005507080c05004504080c555001c018000ac00906948600004010048040303103815010f0a1b0809998004002c5e1031100d200c403100f000608260916064a00384c00d020009a00c210003c00d030302d00034001c164440e10043d001800713030b024025008201010581c0002458070041d00917090003056140030000c640d80d00c000d030034151284a0b02c01441d868500e07030184010f150407009036402c100c07041412002c054036840410b24a500a5500d0036000078403558181038158068503c0b10207031000d90200c040509060181c82c0300b080c060241000784040480d40720a014400c11404103d507a004186190149050410000809038100b214006001d140032048520b00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 388946420 1250 388945170 388945199
    0x5010f050c12131e20131a0d0c030201080c1e071a01080105010510172206020f120c160b0603030d1812210218030d08090622081b070e040c 61
    0x70b40341001140b41d43e040103005180d602c404107001f000c40007014049882e140d98208016214a14802c0d506041d0f00024000c03880082040100300010002520354030b204481c4040e15400440616803511401c0c506210815508a013031610704042d003000158000f41500700c07a04880c0705a450101c01040300900b1200002d01c0c0d6408541545c204010139001d007500503d851400041001100552225039611400d0740d11500c5600c26052010074400400550204a60b8000205981540c41e00003590b186040781c0b04201000f41981144000003420780c0c600703004903000300090040c200021240b2401c41c1550440f031f5101078410600408100d000c0501400e40b042e00b20200070907030100c102c07403141d452001c3c0d444105c1c1c6501900b2080d5005040d03072000c00619003007003030304e413150181841d040d034119152481c001c0c280303240041d0a0549445a982281d0750350126500112625039a080b4a030342101002c40801d44204980300e021000120740301d00347c0d0403500541c442d1068a21903590340482d040a00b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 388947670 1250 388946420 388946483
    0xf10080c0a030b071e0201020a02060703020403050c0d08041214010b010203040f17010f050f040212120f030903040302030316030f0f0e1e03010e010905010f050c12131e 74
    0x1900030780c0500205844150440e0320030501d103000005200450f406241070522502e2080c00341c0c0d00481d03486d001e5501405010360201083c070f030841c1024590340780d0f503031707101c10020001e40146031400c80041400210002c44e0080d118a44405035901d60713600e0580645401b21800703120651030204560740f298408003c990850700c115881d070007401d0a10700191410740d4070302e00007400741d0350b101c605149070012802280c0c41547c1c21807a248045ca014018880a404015880701142d008009102000c03841c6c003042c1c614001107a0240342d240c2e500c600000b803541c41540c202951521000c03400ca1015809202e030384a405100359202840030ba545401503518940b210111800f003000c51002c04940e04200701490200240c9404109550070200c01103400c503028012400e045946409070103042c017200340500300308521243c0f8200214030300f01c00840502d010b800c418a9070411031501080d0030940cae0040d04d0f00b520303401c0b40804082c1e5100c03030007030b5000300c10104c000c840601000f00c00e01000031420740b1405a10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 388948920 1250 388947670 388947679
    0x2060f1e270709060906050d031b1b03020f040615200708030421020303040e04060207060e030415110a080a0c06020a0e0906030d02060a0203070908191b12020d060f050f10080c 77
    0x2301c2c0356580513621007120382300c0c1c0c00300e80e0100840c54000c6040e44c0d55040208095113030b21603020b829801070060810300705420500132802c1100c10405d901c9010540c0d0380c08e6041d854080307c58012804c02c4180f0000c608410706462203000c00c089400725000c070080003190810310700c80c0031440d1100d481a180070150000070354580c01c00e0100300100078100449c103a10074420000180341c201280e03100340c00c5412a00003c0215800401d0500015040b80b103856494021030503c0d03140300400504d041d45c1c65680c2300c4014a54030307003c00c00c0c1c20214000d03170070388003030980c880b070295150442078a005100c5110681030758403844c00440440c0e0300b820086644810b0002d5580030700344541e201009000a9413010b0f1800040241c40180007580700c106000d0b0751802141c0942c001c2c441d815034280152514003405075000c1300788019004000c44000c080c00300c0d032502d5040d030301d00d0031002180c04d110006100e00e4038045d400d0b608040400840040040540d0b114110f000355000b83d540d20307008215503564031200c844e03402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 388950170 1250 388948920 388948939
    0x6030b011103070201030506010306030203030d05090d0e030c06070c0f0603090302010f0204080d0804141b0f010e010507061104090c0c020316060c23011b02060f1e27070906090605 79
    0x155220b9041f299001c01c040c180411401c8d980d6001c070b0314507402050048049540c1e0302c14450700c01402d200c800780000942c60418001c01002e00040d0b00c40c45c40c2014503100e01400103840d42004034009130600104811003e08000c030b6581c000107009041058812001075180502c0c58041c46140d20a541c00c0c3c54042008180d8110402401c0cac1d400d00c0301800030748103510143c000c54a5580104442406695481d0740c1f2810150f02300248004145080b03411030502c90b800450400c0341e6804003d841d5041d40025001c1808820345100854070b124030703004910041c2c10b004807034545517000712400c0c440510076011a00c080d51481e034407440c5000540900000145440c4060020a0000e403860551141202c903071103182c0c6503242e0241c2110b0f844c0c0b0b002c200d8420f0415140c0d40241d018400c0542c0078049403c03071556850803003910300404c08140400c0102c4041c04020804140e00c00fa1110303001645034900c0c09140300c0504010365102458814540940c0c01c00ca004201110703240110011030b070010300259003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 388951420 1250 388950170 388950173
    0xf030a0318060c150209040f0509010b01080c0c06130606050a0b1c0c05090d02010e030a0b160504060503060103180b04140c010e030a0209091501120605010509060d170702090c030106030b01110307 86
    0xa503104039580f035071007a00c940d061484030355107102703041c001d041d038030000100c400700e081c0094010b44004141e20705100c418040c0e00380c40000801c900f61b128688a41400030030100c0d24013100180074a402c441e030013a2039900003003040e1107998010f0000102d401c3c041c3d0b9250300c00d409a0001d4910701d581000009105000c16040b0b81810011024880d105040291030b0104420101303240280e00d03501910100072640c01e00100c0d00c0c3c1c042c00001c0142840ca010b178501402c0c00c901610501c00036219504261b41d13108108101154000c0d84000d450307010700101143e00b400d040000c02503000290104080c012a080c49042c3d60060700300711101940070700900003003940e903000c0004181c0000c248840a0192240c0888a0250909040c1c080c01ca411820b001c0c500d0b40d070500c40d0440300142c102501900c002c10130f22a5a07030762403090740c07049a0b000f00c0703040364100c18074035a20303041c003450100a4100e043d160600c811500d0340000746050398400d5508103e01d0000100449406090001d1900c03d60001c02c82c220 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 388952670 1250 388951420 388951463
    0x2090f04050703110d1b0302040b03060403090308130302060a081f030c090c02031201030623040807171b0109140309010c2a06050c0618031204020f030a0318060c 71
    0x1070f44402450821a20055215288101250960030904071b46007103082c021840c00e031003855000c010550040c021450315540180445420703000103050401d0115103484c0242c20f100c42c1d880030b580d01900007529440e1420000d0903002d010b96003426043c280d040b0303a04001501c80c0d00041207941200030003607800d280c980390400a1150111a00441c0010440c500d000640000340a000718426540042e0211400c20800c06425240d1540e110f41389011080c000410180d02c141d91059030003002e240103000e2501002040d91040700b8030103a0301521900e00010014065125040e00d80c0101d4894004100d1070f00a03546034450081ea03180071880041c00355010903081206c00c580b20541c1030321000325100b044926003e00603180c1c8000009200001c1416082409211a03a08117882c10301486c4030121a6003165124080c030b0001d0303990034240e1400074056564407440380b408610040c082e5a907804023030034020310710303050600ca201109004002c0010400d00c29030300f0650710354114402012120340e060744030b07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 388953920 1250 388952670 388952693
    0x6060a0507050102040e07050d0608030307090312020709050c0c07050436020d060f1a060a0c0501020912010504030801080a03050a0e010e031002270a0b03061804030203040302090f04050703 83
    0x30b4a00e50750a10001c1821991508101e00504083e19246d89811007107100c40280c40150300402a20b0b01b040c014000419080042d030340560703500c150741130001e41840800f01d01e4004694484159641094180032a05408000400002d601036059a8021b502e0b1030900c0150345900c142c2e806145914072046200c04803403c0068800400c0c04c6040c0b00440d0070303800044052100007001c2d200c290752514040240c020038800c10010031610488103142042e804001903490107081e101c40c062000502119040060030342c11a815040000d1003640e414076118021070007480116400c602003100b4800200315800e000804054181c2c2c5944c80d540340aa100400b1200344202082c1c91703040c402001310038262036506125016848080340e10060f140c00c1405981c080d032000240000c0c03180c03034000141c490103480f820290000d594420792030942d41c1c3c40d21070214440d00c883c1c1600c01050301150047c007040540c00320040003280c3c02116811141d454403070841410394002d031001800755100300741c02c000054401050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 388955170 1250 388953920 388953923
    0x1f050106020c040b0604060507022419030b0d03030c0512091c0207121112010903030b03011b02030316051312150b092e030506040506070302250f02041a0405060906060a0507 76
    0xe1950080307801d4220f2f41da08940110040f0050041603403c8102c1c01340e01510302241c1a45400e01c40307002c01c5000304984100c0000c02030101600c90708514070007030141c011103200e40007101e2024490f140c0646030756101c8a06035108034014a90750403d10301c1d144000350b80701c103440c03600c0e040e05070242250341d82c50501c11035100310300d4104144911a41800d40288940100c4501036140030401c01c030a0401c050031a28181c11841c158032403000c0751002150700209a9a021100740c00c038511b84090b081c0c040d1014028400503580700140c40700042034010504605540c42481070301c6100b080380c43c425060060f9441d030390800da0401072503c000360030005041341d0040c4800d10300c001d01b00d8104c08a1540c5039041c0d0903403c299401c1d8801c006000400804000d91036200306240303000c40c10300c0c00c0c101014006403074980310b00b10120314640b5408140909482030340d0303e8542c0180100a0f80b045665000c98824030145001e05c502c0ca000c001035110300b1701d0720403203205040c000c1a447c5001a41d003c140e85903088851b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 388956420 1250 388955170 388955179
    0x801080615130f2d06060519030f09080a12051513050601090504060f0e0901020f030622051602060703090312020d02040b0301080309100f0801060e01021f050106020c040b060406050702 81
    0x20100a40401d500c1180b4010307000c5001c08401c40c21800c1c135400b5140742d5401003040100070480c002c14140030b400b00101c00502441e000c00c032400601c0048028050040c1c025001d1500081c1800100e07820903e4402a495590710510082d030f01d000980c007891085606941d0011803e64101460050680c8996130081c014105080c0c49611000410100c6d00d4641100801c114891028000600701d0034040ea44200c101009504d000040524a0140c3c003014251030b00500284412000150943c00f10a1070003048070810000c0b8942903016001462210342c586002d40900004541d61900c2170007600e600300d403d500c5a1003407096507071030304000303511940180b0116503082c08040740c1522810001d40c004c041c014011070f11003503443c0420034484400341d542d0080c8040a00103100f101d81100043c6e0440c3e000341060350500f80390a006034100613034076801550544200c1c0e070321001c0b00e455602c03140c10b90340190308895174080c91a00340030071101618030032640500244820411740c2d02c038000424100f8401b41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 388957670 1250 388956420 388956431
    0x708060405060c07061806021b030702060d15091b1704030f080705070f14060601050309150606120405010614060a1205130206070f020f040207031e05190801080615130f 74
    0xc8080c035130000351b094202c603080e8000485024110b82000101c154848280180d8507142450740014658402da9020607a0b10381c481c0b01c14503050b0240f120820060400842c1400110220031101d4210150200400082142184000400380082e18420f1041d03905450703c116541154109075003506004000008000040180b100055141e00c90041d0b494803407203c42c6440d04031840b003142814001859141048014000c004070104000748400104124064864803600d660000c14414451070100d0505141a07400344801c002c07055210038211460307c0134689461507810100102c03131080c500c150000401c0c0c80b52500040d42c45502050b0001c41083c03410709014000e50100c0c2ea507800c401400c0c0c0b540c030500c0100c0c009505044504046400e0100ca0451170b003841940c0141060000c1e5200e00e01c0861030a20703106585008001300d0360450340b40b070701c4180100c80d590b900420f410f0003409907040e00d008404c0843e91090564401d40f0341030500409041d0958624070f440402084411102103025031902c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 388958920 1250 388957670 388957691
    0x3180209060a1508091b0a1404060506160203071403071403190302071a130308031008031602040e0a05150403090e15010e0102070602100e0c0603011203020708060405060c0706 77
    0x320b200014020076201e030b01403803510b0140641041d2040c00c8001c00982c0c22002070381d10f6a110f11210052340d41101401c69602c458102140062074181c22031504500d0000e821562028030002010881d44224100c031030342921007580c4003610070850441d6030103038001d5800340300d0460748140611010001404840c2c00a4a90350071008800c0700310710640c091380048000380070205445c0801201683c021442d50b2800c2d15007920350340b045184d4800541442c0c40400441c154030320988000b0300910031a02100d0301c600a104440703201c0c29855504034411498070140c005c401c074000c0b60054400d0340202c0130b00481d4108603407035010554000d004400300f01c40c10300b0128140b4840744820740901099003003403004902035000502410241c1c840d65041d54401d410400156a0004480a222150300381c007041103401d00440358a8201c2c82c0080302d81c4860084004505082c1c0b105003001d20038001d50072501030302d903600d218984900040e640a41907800000001e0034001e5a10018420103101d814002260003c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 388960170 1250 388958920 388958939
    0xa031d040b03031305010810030507031713030501020a17010f0b0c0f010c17060d15150b0408031e0a121a03010e060601020f1f0f02040315050405060703180209060a 72
    0x1d07515200401039510041c417995920103038165105206400c0c2e01461070554494031b54412503480000c01d00c2c1d000c000c4024003036800701c069900000100b914000c0c41501c03850014040c2d00585409000691403803860034046002c0f008090488001200e403022041c20110300003641e910032280340d46284261403003c4110b207800d1194100455080d516008800074038805552141030140003a8480c2d0031204400d0040384655149503203008140a0000300d011860300311200c03281d0b0507400f1401c00840030400161402010009000240884020240f82041c0b503080300d07054040e1807102c10002d10076510741001400d0944c010301408480384050b0f5034560600e00060300f5514420031000043c0c104409102032960104280400302e5038040150500100252140c1840850503444048503500ca001c8003049450320350403100a9030700908080b2070700400c2c8013940060007055908440d00d1140d28001682d107032081c030803840d613410092000807008455030204103105d000500a40d40c0841d03c0840090349805 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 388961420 1250 388960170 388960177
    0xc09010311011407030e010818011401090b0a1802130321030f0203090c130f02030702070807090b1e121902040f05060306191b030e010c020a031d040b0303 68
    0x10841e0029181c0400200040c0b500012003004124480180180400a03030031080d0040c9501007842d203070001d0b03039506808204080441601810a5113001400b0004191019140d4161071450000b0710180c0301200a101c0445068452101c0702c011500e0284a03c400b030390020040c40c00c66100c041901c0c0c0c0c80340c0302c41030b010741e41c03c0239403d8468000c02d080c544e00c1d80600031203071102001c40c3c1c2141107240965441751148820954603100b90b0b1004560f0440c0d00c2e0350303485442d0030031304090110740743d140100c2c01a607102c58a00965100f4414207600040c0042c2c50b000c1c241070a130000c0d00c0070750204032030010201c0d90004003511580c0680409003a24452a00300414451141200c1500134941030324014442214200101100c000e400c3c1001c1200d03645002403a1350f0809110104804103051868002e401005100b8000142070784001d4020b1a6543c5030b000f00000701101b80080100c142c90b51400e81c0d0b20044e4542c014040790301c1138040c6803d426078001d0204080005070001c120450194002801e560 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 388962670 1250 388961420 388961423
    0x206041205011a060a030c030f06031a011509050111010902152208060105010c0302070e0c1b010e1213030209010320010807080f180a0302010504060c2303090c090103 73
    0xc102025805101d024018000444034200d0307040c45528505000c5012880751032107250a00d500c0d00407200d401c621981c4102c0301914012400c0200d1501c0b450401c4070194041d440d034069101c80400411800c100c01000e000304607154803a901c04a107480019100743c244a0000b00320b42d5a00c0040c0c0c40962200c0d0000b5543d4400780310807603502c0c010301c0180580071040e504100041c5d184020280400c00000400d14199102420b02d6440b0403a14607040389041f8a68000340303a114802410f01c0743c5a04140302420310140280180c840c1525400f0701c5030708032a42404941d0366075000c00341c0e00c0c1c1d800788048000c0c28504942000032850702d4803034000c981034100a0340700b12070700703081410620a50403170307038203035a0400d03000346480c00c1503042451000744820380186c000d05650240c40040354094003428042203000442100390f4126130800d050103402400c044030255556810403e004814601c100602d50503d0040300c1d40c00960780d4a040c8661050300028400300d824801c005407100b10b55146c01000d8002c6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 388963920 1250 388962670 388962689
    0x11a0912070e0a110301091d07030803010302040c080402100c02040608030f0c070803030106080a050603030d0504150605032422081902010504030503010506030402220e0f060402060a1209020604 85
    0x5203000e0030081d421400a0083d0711940c0f500d09400d0030854180b045134111944610003186c04040001d4004148903510348100309446003020020421079442d000d18102c078001c40301081071202c050701c25184014115002940120340c00c09180b080c50041c0854000c45001402c0015405e8880760414a50303071018658015104022920107001358040003060081c000440207903007123502d00540903104c10070107400300001e551118002082c5407420800d80710358005107441802642020301380545044040ca58100c485800e0820200c2c1c1c9003000a00340f04a0f101000c2210700c514914006c46040300006081031001880d5405030600c680c00b030b0080d0900300380c0608081a527580c0b840b40c00021006c030442c450415a4140001c21000c80d030000140da045810990702143d076642e0707910001c0c455400902d402481094940a4040d4405d0181d00c0110501c4503101220341c1d43c00c422100740c0d80cbd1001201e000354044010854000c00c28030a044820b101d580b03201e030110310030072943e000400c603030010782145108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 388965170 1250 388963920 388963933
    0x1f020a03082202040c18171e0706110c03030a0903030e0f0102060604150914060117060105030a0e0f0d0504090e0303130219080d021b0405160f0c020a0902070b1e011a0912 75
    0x84047c00e200010440100094103013403840000401500c85045100b006c0500000411100c951403080c04038529002c001811b6030f0342c400205c1d0000d480d030390040c0000c0d40060008000c040840c1401e282c4010075a0058000b0903050b0358200403c0b000c0d00c002ca002c070620701401c010001e07020b004e0703002d580840203101d0081041843c20200041113001e41c4020320640c01d28000038481243d802a04a075081f07a122040428182c805034021032a1611004c0b0b0501e443c4946800c0840d442e5201000c1d00917601c80d02000d020120001c00b4051303032400140c503611800942601c942006250500d100d001720380f0050040e031052991131080078203003c994042030b40507800000070b81da600c50501440c551903c00c01c61b4200910304006840c200c04440344002c100500048181030200c45004060342c411041d401031440c0c000c21785486c103a0003e9000640c0480e280c10002c00490b10f007080000390400c42c00c1c40d00e84140d506038a818000c107108000a01036141145080090f64207503100c909036462030b004504c004050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 388966420 1250 388965170 388965209
    0x6140c1018020301141518010513020f0a02060a29040f1b18060f02060615040f0b0403060606080c180105071202030318060606070b061f020a03082202040c18 69
    0x4080c086c007014601c645034118011400600000c0e41905480b41030711b440798540055910b07080203202d100b00000c00e000000c41c1030000c0030707400601144a20f105103010703c000903251081e03121682148840d2013406802c2802040241090352044940020040005c501c003a038100d00c0d0030482407207003807840c0003a0700c24186002c481140c2c585200103040c580382c141d00039840d00000075117034900601903500c1200c6c2010300e0f03058004182c0a94001c2c14082d4001d0342503d0b5250701c3c1c220150721a02c0111343e00c900700000050b520340a401d5451050a101c030710a850400d08030380024401030324003483c2d0b060101c18090704000ca8400c7c805980b14a82c55001140d403420074202051011540d41910581640520b0030040e640e00c520341941c00107540010503416a0701c03031000103518422503020514443c120350090040c2da61380013550f624481d000fa00c0c0c1c01d19a88400d111071401c1c003002c0701400741425a844150005080650114002000340d1401c40c040c000011030b8001c0c010455400041c103100c84600505 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 388967670 1250 388966420 388966441
    0xb2b02041d09120706180b15090906070203040b131e0e09010605030d050c15271603080c0c0405040501051503160905060303040b0a050406140c101802030114 69
    0x54019060400a02000090140340c03101813098180c010300894551020716020102400c0000041c0d5012403000c849260040c00280451400840300d80b00700201000705132141c402140c4140601040c0c1d002d075103424109003841d00942e01035071640392007107900c9800081c85003107080c28503150482403450804592902c004091801805808101d0992400d01c08118582d8001010060007141c2d041179910386900b04040703424000000c60305801c40c4032130410800010004a1801e1000100c0c0500c008214105800e181d03450700148c00e410020204c8035010b1000c200360801401914880340300303c6000908140c081020303a50300b03541c1100c85039150418450b081d00951030350002000150001c1070301000d0740c1e481250b0410b0b144242c000650350f4001090303241c1c030203008a8000e0302c0106029951062081c40050681d44284108000030301342c6100f400075400500129101004100001c00000107003481c010010490074600100d21005000750704d005840030300079540304402c13072240031800303181404c41c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 388968920 1250 388967670 388967729
    0x18060c0201090b12040219030602030a0509071a0d0504080f0a1205011d0c0306030106051203030a110702010c060b060913050f011202030307170f0d0b03070509010b2b0204 75
    0x64144034140400e0f810850050b6100d54801e40450301044501f840151046078500e07075400280c4654000020420010700b02d400c00c1c3e016001c03203011200403603901d084200311100402c0e02c418600700100318092041c0b0711500902d0700940140b100c60b141c56134000b0107008135405050920040f031861401140c00c91b51902c1030354012b06159071520b0246410102080d100800100b411000c240c0100120300607403003d51088005d40b4002d40050461102c0c0a14903507030360000c4070302e1441982040400207540c0c903200191440940c5c1a104d241402c00113a0301c900180c4010b051a9810048c24000c0c0c403a80c0e5501880403542d0541241300113454184440502032940c0160040c1c0010010b14898100684002003119102500098036004103740c1d8184c5240c207205142e16801820700104c1c088a010200d82d009002682c000c40484000a07555028403148810901c1990441c620a00c0100e061132808a160140500d09070b820f9818010251196412a00070381c0000411004202c8400701e91680003208 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 388970170 1250 388968920 388968929
    0xc1c06050109050907031e0507120618023d03060311040606021203070c1505010806151003150e01170610150f1b030503070215010e04021018060c020109 67
    0x30300061800c8003200b40e50340b01798400104102c8412040030303082c4107142c1325006019804416210340a594040c040750081d00c0765029900030340380955480e01085908555211994082d12051415000c1e420644841c9004009102c0071088001503603a2000f00c1d080b810048000d5450018085055003054814681020403481c062444c021051012a030006000d480d24210514029601c1c0d40d0302c2000c41e00a010b40c80003c041810844050310020720640185042c1c884a03003c82c0c245c2d0b550b071074038010f440074121500c9401250b0030720384c000140d100346c10095084c5554481030450300e40e41d501150100000360300142114400c0e041c00003000c07209024054100c0700380400c6181c10790902c6112500b030001e00b5800424000d2203404812118001d8030040c081260f56078440141d5a030754100540180d0046a8010040c05a03018290355112010080c9050391046207a8a44980e90350f03003171000c21030720098140140a60a003604c001c4030701d41008407000d0801c0d540d81c440e4002c1c0d944009409086190007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 388971420 1250 388970170 388970189
    0x72102190f0b070909180201080a0213090e01020405030f0105060f180f0a0f0216020108060103090f0f02030f0703060606081008100f0b0a090209151207110c1c060501 73
    0x88500200d190840380210321030300900b02039295180e010301a0768803046903010303030281814441c101c04c208a80c0000c1000d00d5000b0703210401c0566503901088100c0c802e404440d03019009149082c84924500e82c84a01c1c13000a417000140350640722800070785030443e5000c074140aa91901c04005080c1004009040e5400d41030f921200803503244c02445445110041c5000303019406000020f0440d046908665590314180000319580d40360b481134541e0b05004a0700a0b408152011301080c03455220b413061052154129051110702c00e11a81d07140309001c041c01c0181e034548645100c920a646e000e01c01100114070490340014418940b04014020b014002e0014070241d10f0080c003080030b200049500310719000e4030000007800c80340d40d030701000003091032080f803070340001082d4008100e0717030000d41c002c01806804561414030340004803488942c40c03090000d83c1c140040f000001c218000d006040010038a0000425210711010300c0010803110f5440c035400c101180401c043c12024081e0074803406000d00070380309 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 388972670 1250 388971420 388971463
    0x20c070902091c031b0f060507020628090204021b1002070c0603090507081e01050a02040b27030613031107141003020408010c020102041505030709060e06072102 71
    0x10005030480114600440f4926018907020040521a10104241c14800704194801315030320f0130240707001d01551801b00c419510b8900800ca2403400040c82d07500c5805041c842c20314000b1003079005500700b007101c05000ea009484101d20001a03880b4006048009400e60000f004c0d50030340c10701e040c9055014029040c1207807041003588d0200310a00144804c0d08c0c03880c140070400003c3e44c40d0a5250400175400344020340113440c0c105000942c071040d2807a041c40020000d02075a02c8065408040b48500d1054114198081103050750045c0d89409244407022010310180d4181e40c4040401d041200171190280884d0b6403400c1c61040640017281d0001c0c140351180107121050820a180034a841f1a03c0820302c10455032811003802d500c41d4041720b02400c1c8043c024007840c500514064049c0d040741c01450405980c29600d24002c038410713000d807441007986903104040306141c20b900b660024014003c064004800b00010004914034415189045817404015040200c1e0400c009080c40f4810403803080404201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 388973920 1250 388972670 388972687
    0x3121513050c1615090803060f010512310302010603200d14100e01060501110a05070e1b16030908070803030105120c10020304050a09050108031801030b13020c070902 73
    0x94007035507202c1a070b01580700d41d003410604107908134032100d94414011900b090101d0707040040790030145004242c180c0364010310101c520010742d03a0740146103412624141c11400691002c0d880002d02ca640542908180c00c041000884079001d50807401042e00907030f449140c100100050564900b103c040343c040c4a00007480e0600015510942030300c8007400d0700802d030381541c601c42d405108d4524103c1c0b20503010000c501e04400348078007801c6603200e0240484c1801d1031070206000d011804900c12640800501150ba04102540c1d8000001802c5400c03c44500307845807142c0384407800200790911450484035010f0890341380040c0070414a07040640301c1d0700700c00810407080030004152410b544003150440c40001500c1450740c40c114040d4480365101e41425102088243c01100030416558141e5610203c1038480d00304000b5950b083c490313800350344e10401c02549024081c016466035203205140100e8031900103400644454103691000c49841c0d8001500a41c002c0100000001402028815401c08007007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 388975170 1250 388973920 388973941
    0x60b0d05190b010f1d040e0c040c05070812070909020403200126040f1b031505070e0907022b030605040c020d050304320d02150109020c0312151305 65
    0x4441401c0c4040d42c000c11801c001d1011740807400c2c88024100300080010011120b5540039200461409a0719010300c800200f807180b0211030090340c00104240c546401c81d500c004040400401000c100308034a500465071101034002000154054078080245484900304503854840710300b00c80b4140100100d002201d16807070342548012403c1564240d20a50341d500301400002601000200980150111309100f81000102c102c1641d004026140d060100c54260204891003911818081123510554a4280c58849680e40d031203140362044c1c610002a0004410346800c1c2042c09003a2510240381d00c05401d0303410712400f001407400b22410301c481d100000010351101c00102602c010000000005030501410740b0103090060b140107041c0d03050760b80d80841fa1226030301004406a01b80190300c0441259440045c03200c01e40d50048024000c03691034600e007600254001441c1d01d4141c007040c07101416806101000c14401d01c42e225150354800383c030b40100441c04082c01d48070303e5480c0ca40000e00800d54503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 388976420 1250 388975170 388975187
    0x3010b0a0e0c0a0203070218010806010605090901030210021c0f0f0801030b010b091206040c090f0207020307050415120b04030201060806130609060b1e09130201020309040906060b0d05190b01 84
    0x400b01e00700ca50754046020220b0541c070a400019405c181c2e42d040350031500d5448403c01d4104c0d2410000d40716542d0303c6101c121414850011a00d0f44001e10400510240c5010100400b01e50114011105000c00000324001000f50602d00c040100c2c24a58900040341c0c1c00060070069107080c0d280a20f800d40c11595060306425040c090240d1174240825200542e440745103401030034050302c800300c1d412442c0a1605030305005d114040c0ca180c03142805a881e103c052a4000e49021310360003805800102d040c4028440100f816201c202201c44620000041001240a9903c45a80070301740d078400c5c078906420b000e42581c819503c0b504c034603072216003003001d0b0b03051100103401307010b5001c000424042000d08011010f046410322040e03210b00c928200b01110080f5106444843c4000c0e01d14200c103999008419100c40c0c0760b180302034090b8200300090b001d40e18107548510055442503400180749601c4648884054111143c428299540c5000380001c0e0503001040b000d55000000c4140040361407580024401c4a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 388977670 1250 388976420 388976431
    0x19050102190b041101021204080105191107151118030d0906020d050307022103070e0307051806060409021215041e0507030608010213140a0509041b030b0c040503010b0a0e 75
    0x40c80c0344181013142e02c24820b4000410955400fa03465a40300d400c03440c000c01081c0c41c0b05220540401180b051036815010b018007946134408079a082081c6521030440024940640c3e0351199034a122222014003092701070842c640840341404c0a041030300061615044030403880906104a0910411440d0381c0000d01c081c002c2d100e03290181e02c9440700c00003607240082c41e40e440d0603030700d401d04549287c80289902552180300d2030f036100100380303605000341030303e0316441d0003a135400204916100d050f0704035601003280c00c44405411146016600c0da5040200d8220030611201e00c89036200744910101589c0c55041d1180c000c440401400004c0340d42d041c1d055101300e400c1d94019032604009650305000717900150041191500039903507140008290001d6040c0d5001d03112000705620400c00840c2416640302c021b03140007800c4203541b91600d46852203c05246460507243d41c010201c080000b5106031b03c01c41c0201d031101030130346d2540e090804050a5a655101c41c41c0901582d040822030303081049101a00320 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 388978920 1250 388977670 388977683
    0x2180607020f010c0303020f0412120c08160807050a062306091302010507050d050a09140904030c14101a091311040e0313030c05121209040b19050102190b04 69
    0x2072104d4a4150041c0c0582042c44004101c0031800040305454a030285032468800c0040240c549a4904256441440c0304006407034507109018151000866502c2c004d20356001d0011942071038000c0d501c40e40b070702081c030074126001510ac00342c01e03020022203007032600380d004141c00c00b142d54681003001c1050040020158540c80391100c0381d060640e4080c0013120412904802035581003000040d028000d0340c822020080002d8000c03900003061020580e1034071040c0f2004120100a85864408035184221401c0540d90f003401c2950315401ea55041100720329000404a0110b510041610202c2c04810840e002d140a04401400c0204200400c03188900d01903121b0500e280c002c901001280043c440c01c24102c0e481d104c00505000920170f0409140c045920400b0b00c407440d903071160140444101540d40c103e04a45c0540601140c11a0000241648032000780c00022481d050100040041079141c01c6003210305e80e502000e010a590600180c5a42250b214a54a2a21701c03583c8440440c0350060015024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 388980170 1250 388978920 388978937
    0x8060904020d02031006030516050109140a080303070809100c020a260c06090105090d21200706060e0c1b070806160806030a080d15080f0102180607020f01 68
    0xc5582d01d048103940d01d40c01070110b03000700020a003400b00508660105542d14070500310b01c0415031505650300c90a98070182d440c00046450200b201c0101603008038903642c00024943c0219103003400f0000b961080e40540c2d03603140942460101e803400d00707591000c2022a41e0404003001206034002803082d00b610307807207007a15808001d555402101450024076241440d440010382c200040c0000620f54051185c1e10000c001544825941540e20907118841901180301c9031000555800c445840500c202076126000c2610700c1c4c041c40d40303ca04440c0088030f0f184a0000f023107000a0201621901001d008410203000c018184542c41e00c20500914603400760001090001c011000414442100144400405c4480c0d606140110742041d80c0b4106808002542840c0010190315001030072800a81d041901907203450003401c0c40d180074044440c0c4140d6107140c146400600da4100304007070b41d400741020300010780702c0c80010306a0031690840d10701c0b40d1140c60140080e00c00b42c1d80300c104004280009007482e800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 388981420 1250 388980170 388980173
    0x115260702010b03030d0b1801030209040305030c0903010617250b0901030f060608061005040b03060904050a0f03020607030b0a1404020c0a0b0103050a0303060b0c0618030d02040305030a02061608060904 89
    0x14210384060a44c060001040b070910000040d000300304000c2003103d070000903406400c1442026070003407001a46c0880040045004280568011500081c24483d1107140c460a84086820365404c1d903c0080714081c060340c0ea085128091024040300c070014076401c40e200128880040d1303500440d00036400300c401c00081030341c42603000758040f40d45c1c90440c000c2484441d9860402803c2d13510115001801000c0501e01812418820021a000c2c0c80e61161001e003161a500240f01011000402c2225580720700e20490021a05200580c0490740c4a82d0082040c0c6ca42010001c00355055500a540100300f5018284084946601e1650851009407030044c1c95481d20b070f48080c680b103810034001e0303d6088004c002105108010510640d05806601c00344000c641d41d84951a203403161385503100e61a0811408517406040b20119803448000c420b040303909044c22540c901d4101ea0090740308a48681c030002d0221401501806100c3e4070800c84800c683e819400100c002d041000028002407040800c02c00080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 388982670 1250 388981420 388981423
    0x8060f04090506101517070c02060702040212041202010e0601090c0320040f050618090405010617010b040507111005270d0306170a030e030a08030f0115260702 70
    0x4065802404444003410004041c14490001e80a0082204850103910161a0046c000d61041c409081880003196840f0081150303209100c80b4102d911140401201c00566654006066582c5003030742e003a6158103040c034040302c00c40516040201564180154042d01e001e001c6032150441d502c406010401c0b0710b448404600420007a820034080b91503907420703a01c4100d140b84c0600f00707403038502d50b19520503500c0340b00700b101e580200b401032450030003005040079040c1016141560000c2c450380010079581e4450440e60f201d80c41540e058445070795500240d42c802e00d800c0c021a03070000440c1c2004600c54000000c255107070748840140106003070b10340380820450340101400c00700e51320104080c440d038030401107412612440302050f542300003400d002c00450303110b040201c5240b821003100014800400141d0f802e40710400d01580007607050113840c5010000c9004100198425100000d80040c3e960500c20032000005560031042c04001003c0d00da00c9103010a01c1c1690058001844811082c0e611000100e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 388983920 1250 388982670 388982681
    0x30f18080309100504030c0302070801060b070f0201031121061e0108070c02190617150d051608010b0306071103042321010605011e031d01140609061008060f04 70
    0x82407032403920003048145541f0005c4404500d229034250b4041b50f80d100440303400da41e014014a42c1c540c070104020300002e1030341022141c80b540f0606021803d0108200001040e800c407410341c0e625544031003500c80c640300f80c80c507070701e0750151040310030050402c1c5c04130170240034881d400b4403d0305005081e0080b0360194000c0420942651f8000c00d00c089400c58480030030000b0030395201d0007000c580441c0280400300c50000070288600348854034010402181c4041001c1805203080541c1c00780540e078003009040741c1e0400d000c00038008410001c5102038402003454504103000307002c0800c00c083c82e80702e01105800401210f00700e50b00241d00504009265400c02415030204000355400180b050700300d0b003800c8006c0026040711014400800445a03074000540e101c03c8440459005458514040900b0362f01070351204240340100150499204c840000c12400c49a441c241c022034070000300704211703640c50710000140d800312040d5110030701c1c82c5880d40050464800544103506c1210184010007080d219640071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 388985170 1250 388983920 388983943
    0x2010509031b150123010c15020310090204081c0f0c0f1a09060108010506241e0406090905010504020c0a020433080d0f120209130f020901030f18080309 67
    0xc035a03ca5942d0341e1540e20400c0d20681044d040400380c90603541560040c21030341e10300394104a10b0040400d4043c0008000d5200800280a90703414610204010381d1350310207400034181c51030040404001c0c040e00400c1206001e4080d030100001011800101507000781008040355004034500504255031514801e15252100025454111003041000c20080015128101d500200c02081580c66030300170b00400c002d6944141551507610006454060302c401e0051041d15201d005400480d07075421440580b580c042e9103d180000c440807020301c50f2203128460315004000440e4114600006905001d0720b401c8400300207031040d0340d915001f40d50081520342040600d0035070b44003920b070100541043c5601e80114064800e40b807040c0540c0740d1004c3d002d241520306848554035503d940e68120800e41000e980524503c0740c01569907500610725004600452840d1012281c002d42c41d1003c4500040481d130020031003e074414107000d080341d5101c100001c111445600130b40c0030f0313641e81e440c07085035031401803900764 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 388986420 1250 388985170 388985203
    0x906050c0d050114030d0c2a03030305060109030c2108041806050f0d0b04081215010305091c0f031103010803090306070e031509390102010509031b 65
    0x40080d00c09504009214034400c5150401059888200380c2865070002e015071030b0558419041e0f444854010404a00000e2003400c02d0000b4001800d004030b003041c2040001c400ca1414004180101600360007081d0f403000e070a18110441d68a1911180d08980940c403070000c43c02d41076801d400c0c1c0c000018400306804d94000301902e03529079680052241d108158a9480c02d882d00c0c01c1408149442c09000000205600421100c40d911068582c034000c48005401103500000c2000078241411071503080b14800d1b07d40000d2240c11454080c0050141e82008107080080e4014400d0b41031a02d0000500350444055072414440c2001d0f00c43c01640249406541d0301c001030800301c000194410000005e10800400b0783c1038800c1c94544c07860507645240717503104040c1d040e0080310507207400c01c04141c01e090b8410002d004540e604108a12040c801e00d120160242500c001e07000000001c42030302a104040480a100070407080c5851f0408540324041e04400107043d8500180c03280c5020700421149008651280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 388987670 1250 388986420 388986431
    0x906041e1109041103011a0603041e050f0105061f0c11030a0203101a150301050f010e0d030e01081b0f1608030c0a1206060507020f131805011b050409090302010906 72
    0x109141030384e10342d00d2801d100e5820110030800052603207050041e011009440c1d603085403a03a540d24aa12107a4040203650620810300326004034070200084807941595000014050800405111203108001490030481c0f0492108900c540d60001c24040815040316400e0942c40d48680040d0030004103c501130360520400d01e408070301d05800d0348410010540a503500580901650621a0080000d1000010158140010401c1d41040704e190780074104140340c01c04214036000006400c40d0311038103003900010054241e108585d6080b05050b900f141d14040c1c262080d00581c0349a0b802c910524805081243d00810318241c692040101440d00e0780e8407400840c1c0f02d03d80f00742400c0458001307504034400501142603440c1410140d10550080d1015a43c816142003455028008410b0328010340c180c000c4101c43c81c0d00c0e5002401d124515491740910b448505121050404500b5640320744028462040300c0f100c200e000c903400508503800c4400b04840491100c0c41da003026801003808200c0a80704c40d0400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 388988920 1250 388987670 388987673
    0x2030f0703050708010c11120a360b030c0912160e070f231e0c011d1606270b070323030a021c0f0203040b0906041e110904 54
    0x114503e010390b20318900030410080201000c40d880884008a81c1c0c081e0080c00c030b0a001103881c1002044154428288a215076204c0c00b0804100b07800c1010745d0126010400c1042c40c0c401070040300b40010030a0715102419420b1161151100d4400c107a09075100300c41c08040ea00040c0014440030300c0c0c104601014100303842e0f40e80c0601d14241c0003101d41c200000c0070006424003090241c40c01d01142c45c0320760f10800101c84d0349100ca840701e0740400103507203102c80445030822040c9a0800140701c06800d420000c40d002851842c140c10507900303601380001e03d800114030150718a40075a4070f1403c60f002c030301e04202c4656502040d80b40e4980c060341a00c0103110803140100d8100b060380028108035202e61394565017500c82c18602c0b2007030268440c9120020034200081a40c0720303802c1c0c01134903030b010810002d51810b4048440c200219000a89002380007a008000c000030300034281c04050780025448060443c91805a940111403c00500d207013451081e010207402c02c0c086110200c40400c00050300704010390419 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 388990170 1250 388988920 388988923
    0x319090f030e011403040b0705030901091202030d060f1404050c0d02040914160801170102040503030c010f0e030c100f0b041a1512010302040c020f03040f030c0b120a0902030f070305 80
    0x100d02d0704501043c1154403403080145080c0803240b05580202c0c500c000e0307841d591012200c0d40e10150403c11150340758007000c00072a0342e4481c400f107460b810f60025969035961070307030003001d580c0c9940c880081c003481d440041080c0c90110f001e0441c2004203c6001603656a50810744005009860080311b01d207101140110305040103078003c4c0105126518425855520038038500d02c0490705208103800902d000c001041010f031801d000e201c09000c03010016061940b41e0010a2075904809246160740c2e4590f0400042c40e58148554542100c0502c0914500041040e5032950750500c0c50010903030581e1307a01e00203408855a4000540340c6d8000f4001d00001d15030080001044d07030801501c1f0b2040c2c101c140644046100402114074207003c80d501c460301c603032031b58007044014080c00f040ca5056001c1c60742c1c90028420107000401c00f524140c503030000742c0d03419420b000c1383c40f1909400865075002e0030469004121641c40301c040d07102101e408082030725940c0b4070105c0d08001e20340c4d450f40b1240c4541403010040250 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 388991420 1250 388990170 388990187
    0x9030f0c05011b052509020c0312070c200402070609060506010e1e150403081b0d050304020901030803060a03050d020d1205060a1211031c0e01020d050319090f03 71
    0x509907905290301000071100f002c02490604028060790004a411013064508030114804106881c0701e0260300d65103164690590b44200f040344115000090507440201c000954103820040754500b04400d41c2840d950301443d1004c01e49034a001003019544207100343d646130100c0380c695900090038003400000303103006406440b0a03156140850520078000456007810a03070200d2500e140d603c1071100d000f4074010700c1100c1c1214107401a1aa20801c4044080b400d000300810040b82c0040044180e9980800903900b8100610001000c00004209000240c0d940c101040d0640341c01038801550b80e260007000a413030145543c03004246001d40044c040c2c0c07164010640e1654a800f98503403010b6941101c06460440c2e03011103005900580301007040c17140c1c04090114000c3c0700d04c0b8000c40280c00c11103900003032401d4100d840c0d0040384a10064200d6840d50301036030101683c4028001022101316100d0081c3c42c0d030000400c220b00066032800c0c041c158079586d4000030f00150f004403206000d400c0d54240200b2405 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 388992670 1250 388991420 388991429
    0x15330102010b1203180d05070e0f070521070210060b03150301091e080c010501030f030908030319020903100609050108061012320a0606090c0504140109030f0c 70
    0x1440c0581e8141c6a0801c0c00a15100602c001c01030b40c500610a10314105c0d10002c410301c103400282c4410ba00700044c40c204240c101030300701e941ea10b09075072811491072080d0103001821402080000d00064480c66031b1501000308042c51907002340700e940c0d1040c4040303190030010031001034400c4c10316030009486580c020043d030280c002031840d6440c68100609040c00e940900f10014146000350040d03004041c1e91640c410300261080d44240e1609003661040d909449003a0030640348c8500c030b4041c000405820032464001411000e01960561030301c12000a0754030304d0300d46030700c2180f500040ca40c0700643c0c081c800c00c6034541e1007a20400030030b510385e46403000812090085940e02d04c141e201048081c0c1c0700074a554100c1c0c0c130343e8003505420700613559401003402d914000b502c038580c515007080d4008481c04a09c03440481501d00144100b0502d030629405850096010b201014503000e21416110b500108803410303a076050022a9440001c1c8004032807039043c55001506582e5940448803c1181017103680c0202d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 388993920 1250 388992670 388992673
    0x1e070305060a0909021804020402090a080105061008010815090319050301090608030c0a08090406171f06080705190b0406021b09010e01091d0105130204060b0c15330102 74
    0x9a16543c5000440e0442c22000c0d5001d10034240305000244410101d0b9030044c405030000d8248640306002c10040252508408000e94540c01007250390308101045412034142d600e0081c00e82d515200d0602e07150035a403020545050780310740000d1000042001200ea26085005021840c0401e40c50000e00541081c0500b200380c40c1444c00c006840200081a81c1c0410012000762403030b5446640c1c0c1c07018940c0600c45c1c3c50b070490f0b140c080014151441c42084803000c4441c0d03014102c080003900e0707140007082c0140f0b01003521030f142038007c0c4010b42d8001484429244182c0782c00e0101c00200c581800b64844642c0030700000c480002e00840c02c0c0d540810201303001140122501d0107000c508040080078242401850100842980104190f00043d0004111070100d515258900c00000d8140d500b590011182140c0b0540f00c1300d1081c0450070544111002844002e6249080ca081c0140154554040182044804843c80003160824030600409247d16007034140252890050310014001021702d918000e015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 388995170 1250 388993920 388993939
    0x314130e10080607110c0a090203061207030b0a09020301020712020a0b162109150b120c092e0906031a1003062c0c030607170403081e07030506 63
    0x11600c8074407080e5402e41014045a984580c01250410131401c06000035201c0d10066480e1a21410a200064a02c4e24809a66031500c0c0f000e0040780a10ba001a150781d42c0000b1080012070440411183c01550f0100e000c0380304060780c00001c0c00b9008103c070181c90300d03a5070f20b01600240d400050950b603d5105090900c5556603000d48207482c0150b00150030003052203c15a84180c0a174031006060b01ca543c40d500244000003070300c2d100440c034500031042c9030003075680d0594a540d01d001d02c4000580c1d404400100310310704161010a04125010700000e65100c0c081e041048680755280b0006203803681400b031803450326500d220080240405100c00d803106c01420303075403890014a41100134031130013002c000b025a00386140c0e10302000b403521460703499130903846034403440e03000c10f078400d1042c1c200d1000d60081502c040c92000705070070a98040c20040a005814000f10080340101000f0342d84260141416242d035512000d18031464032003901342c681c80e64440c2c1301300442c035030b0580d2041d8040c41c2c007581e08107403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 388996420 1250 388995170 388995181
    0x111061806101d070908030d06050406080d0c0b06040605130f0b180414030904061d0622020c031b06040302060f1911160c060215130803040314130e 65
    0x1400c80c694020340c20701c46040c546a81c81c05805440091304210149010021340c0d03500c0300242d046030441140740300b1854131507800f0080ca01d064000e03400901444e1014200035052070314013500700101c2d13620003042011004006210f5960300d41c051401018003030411625030009208030360080054101009030070b4541a02c0c0c4101d420328001e0041c0e60000000b03904916211901c600344066510140a00035101c00c1103041c0c4591102c2c02044000d02c80001c01d03443e284175282c01c180d04244002c01c1540920403038140e440e403481e01c280380d001010350311100040e40c44800100c024254402c140c1001810752103580d11201e09500020640c2c03113140294250f03851034940941c0100c0084d020b0b94001c0300401c0ea0300008027058038641c05121321450039101380745004102d1022000411110205580f1400400d404102840e0144000f02c0c41c2031224407007030140d03d8180d10141120030742110180a600011000508160064801c0d4610000b03204409884100c40b540500c11910280602060f42d1100300102c2c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 388997670 1250 388996420 388996441
    0x230a0b07050d11120702060706201e090607081b010c080108100606050d020a0c020d080307140c100902010c0606030b15060306030a020d020a090c09150e0901050f0111061806 76
    0x2000d41da132100d0942c44e01e42680c003008440d0b0011001030318800c7e655031121800b41c4519821445264564110540b144001c2c150000c020f80d40901c0c01e007500310100900d000c0c60307071002d040b5010640d106103104d403503d05040c1940300f120800d910002d02c0e586804100100950082e418134103d0b0f41c0c0130300701e501040d4081211020384490740314407000b1400a22020b0342107401500900b031003040d6864041c50403100c3c3e8001404008003400103a424031000001d22860030b0b0300c01110700e0080140b0101502d48161904c4050b664245966101002940c0302146000c6a10404400701015000740b01400220b0300e038140500415420703540c0c11011802001c0c85001c0b820545c0a480c460640140036160a0720f00740c0901040a1000c50120781c4134407030325808642c1c10500d00c544821880c0315138071070302864181048002d10b003040f00300400510004e03907a00082603071200001419610700761041000c42400c800181c51a000c4409055038038001c6000b003041130a0745800040d008101842166070b41d865061054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 388998920 1250 388997670 388997683
    0x50402040b061306052b0c0f020703030909021312060605030f010c0507020f0312070317011223071208120604050c030406051312020f1006230a0b07050d11 68
    0x4140341e0001c410200041801103018042c50041900d521441b86071819508080786586a01c10031141d50312485606540d030300c4440d140d4050f07010300081001c04e0039078801a10103038091090b00c0f06181c00048004c107255500c091a07006020f8010480b8171241d040c90424041e00700c501404d800391007a960940012038050181403662401512030341c1c40d0200f260240f0030354000300d03007882d501441203007801011852240c1c024200140240d680703d05000c000c5601200841041e404030240e40074002011012500101c0b00003100b400040c0f201c444e001c41046264203299265208001945402901c0000d101d00d0300018036000200c1c144401c05660b4200400c000c48005895030000c060742840094009081d07940056003040900200c01d00000640d0340d0b100101d160752801c180141c00031a89282d5000f402c00a960100643e400148065801c040070080902059070f48890220703100380c814091a214500700501400840350001e90f03d1945040060395503080881d01e00000e040302c2d03003480035030b100071404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 389000170 1250 388998920 388998937
    0x3010b1225051e060f0304080720060d020c150c040618080d05070303060e040c090b03011a0d03050c0607031d0a0507030822090b012c0607050a1203050402040b06 71
    0x601c20f034109003a20b00c0007089002c0d000340b50400401c1006528850000000d14440c52040c40d08d665941c04030b2403c280392003000c14140b80c121164564200f0155606001d0342d070b480041040c016212654550050715121280007051007c140130821b105111032404000d00a0392001c0e119440c1c40821056015807200c941c2c8501403040c0c1148403104040c0c0d10810040141c82c0c001c1c500890440d440b201815a4110306030f500f00c42c2128014410403d154250083d851640c408030020440c10905070a1404080403c800b011f110300115004141018000c00130350740b118a441003100c0140c6030440020740141049049e003406410004003a0700500000240050302c2035100020740046482c560300c00c980394101040080012403454212051545110b4140c0000c110b5032001240080c0e05e9400505160100500b82d04441200d0306182e0b020443c1000d20050980240c48865440c4003d0078085e0514441c86001440100c039a081192465410341007180224002c8038200180c0011404004661103074080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 389001420 1250 389000170 389000179
    0x5010303121d03090108070924110c0f19030b0c070b010f180506120109030201060f0501051e180315010503070e15221107060e0114041103010b122505 66
    0x148003aa52282080942006988c14110400350700c4019040410034226681c00500c07100f140050170165011481ba11022032100190454a0800010070314954a00107154041d42c18210b0140707802074107049004c01190071814051484c2021151000103610212054424114620000c107594100c0701500e8211001d440300380410600c400c2c00f9101a040007007401e07601816094007030703003020028081e25960500c60360000410304d04003032a102507481c10342c1017a07041110603c1491a1103088a00520201009400302611a15200342900c03009800d000c842e90140035617582e06820000c507021a5041e02c00c21400e45280d5a02d85456070720010089914000d0500055050100d90406010320641c11220400c2144281e030b50701c1d43d11080d60495507191982d2040021081c0501c1098403403c0d00c00554040240a00391900c1646038a01c000170300080d141c582c01102c2d030082e0b0f640940c094110300b0b4010b01943d00d986414002a80c942801d4464800141c0a03011140350b400146090b01096640051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 389002670 1250 389001420 389001427
    0x5070929130b03011e060f032705150c040501170a0f060312030b0607030806010c0507030506070e0f0a0f1a070c0e0103030813230102250c0815040f05030d05010303121d03 75
    0x1d0440180c86d4402054089c00c131421071001a000c01c112441c0720f0f06000340004c202c5141200c51140c100d204c01031010f41503260074413050110340e030700100c8400c0b03000c07109500c281991507412121000340100032040088500c0d1010010800c000c00c1c005001c0c0380a981c03130400241110406000c640d20491b440100003170040d200103481036000f03403a101a9140200c0403541450f44907518140f07400b03c1504c034030340030692402061080380362170301070102d48070019201500c420745840c000d0f0310802164001c1c80d408122449035000b0b04520b0710b042c0c580ea19001001002080d42c0c0d2814074400c400280410350001c3c90030340005a69a2940c500416076640c0001030040300301d103444602852201c100b0700d041c0710395000c101d2040c0001c08030318524480e4866910350080040d0a15044406c003025070710004d29034000003600728144500d801c80d140e111781c201504102d10681440c1c15410344c410300b007200c00243d2601d40080141a170040f88020189440b00b030800c5103818403070b10703c030042a40701c00b440b142d94000c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 389003920 1250 389002670 389002697
    0xe0703200a1106270a02060d0b03120a0503150402031506030604021315020706091d060103020708070b07030b04090224070507030b0a05070929130b03011e06 69
    0x19401410a014903141058001940b10101c0341003010a4614000324400c246981c1084440ca0b1416066044031a005251030215a40030810134083e8003840740701140d983c9114a4640c40c14000c04024200524010784c3c0c070019881c001c1c2c01da82040e0ba130300c0f001da084082c6528071801c251084178002c40200480c50350440010041001551001300000e030496028420740c0016844034048401900300703507000d03070540d40301e54100914180759540720404005a0804c204155031032070341740d480701c0c400645144040d941e0f2300e80140e0107440380500007007200c1c0380056680c0c18081d0142c149402040d07540d03002d0011109030342c108015103240110103540012a409008a1120401010207100c41c1c0d505865040c03c4e01c5480d12810b00e5030780d9000b500d2980c40c4400300102451140725442d40040b1a040581501d4200010b001c0c015900c10300864a400942103003000043c6000145c0c3c141c16140080148100d41f16940550b0640080c031882d054802040c85110890070384d0100307102929102d81c0d880c0d8070100b05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 389005170 1250 389003920 389003981
    0xa062909040e0c06040801060320130b030a0c1e09150b070c09050705031509070c0f150216110301050105032104030f2108011802070515100e0703 64
    0x2c10b000d0310594883c001c030b201c4494030b9000140c4000c0c0420b00001a6061460401c1442d0880c40d1141704441140c85080e40843d50383c55a00000301c2100020006061280c00f011030700e4410080405802ca401c1000002a03a0280c0104c07c9050300e041d03070001100981d41e20046080d1441000b02031025170340000203211070310104d0082c0031882e001d0106241c000b551100c1d040c04031042600c2507800240000204154481c81581507111600180c40b00001c9240149000b840702060807001064550a6100320051200004902141c0e9801000071541c80d104504950758170f0300303146012180d6003012042004035140c10b11032903040baa03000c0c0207040546030080090450310300914804140034014000880400c002408500020f8071a0819a2201e0f0002210040e101400d0b40071104010300c0324010f01440c1c411040090100b210580007503180c1e882440e000d0304144403007801240c600d0105040041d4070110140361001c41d601064880d03c1d54640d044102d040e55070f000000c48907d0413001d005800400c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 389006420 1250 389005170 389005181
    0x80d241502030918011d100b180a0e0106020f0109210c05030f03010e09012009010207050414011a0c07060c0807020607030e0310020a020a0809010c08030a06290904 72
    0x311071058038504000b100c00101d20318070240500200d4810100148407800703c0410161210340c0301d1400c0b451500d42a4150207141980d4040c0d030303444481c0494070180c0c3c0000500e802c4455030300102140701c260f45400b0b02c101c05050900c80c041c0144a984d0040041070f20601c105100b0503000400c0152131000d07922031140240c4010b1020b810880d41c02880008250184060003d00588001c50b659951500e80b00101c80d8001030204030460f454024480342c00901c4007011150082e80007a025100d0302d0f100c006034103100c242c2d4800b68009003050100d01c16100603903606070588643d131a0100102000c004900c4540c0141610002e19a0003400d0a01903113015020200310580705494151400445034003060030b6800924081b0041600030600840504c0c1c1400004045818510114200301c20040000e5441c507500340b0107010060001020109a441441c5240b000c50300110495070342c1c10305d0747d039410080846100d16056501490034540c0f00000880c04103403484820324007181800310420403c0700808 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 389007670 1250 389006420 389006459
    0x5030a09020a0503120a080c0c030a0e0604181b090e0f06210c0a06110304060302090f0d05030721050304080a030623090906070c0f060b0d080d24 64
    0x2074585800040c01c2d6000c004040e003a29011110701d03146d0141070f03030240c203101d800342c111f9170013810600c080100060004250b1703400c880d507454142040c40b9400080b41191080b50010990851180c218104d07040564100c4440f00b50203e40480d12200070002c2202e52403a64041d00c05001060390125044c58040c881d180d800c800014404003059800041c0705a5a40b000a20401e09800c9030501c801507240c0044006d00622490815003140343c5402c010903164800e501620003810750200d000d641c2525604050f01c25014050040c00c643c010302d00b8803036929080040d007100c40707504910600283c1d143c58090810140800e440c1e1b50b0642e100c80d660000d140d00000d901c40e04041d170341c020001c0c840b02034244081001c011400d00034000d81c00b54003407000e00007006149a456502010a205c00103038010003807049240c00038020003c0280514040018100b0032010f298051b02c9900030f40d00b48403011005062190140c0c004029640580c1c2203141159400b03801103611102c88001009085882401c084451 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 389008920 1250 389007670 389007679
    0xd050a02030c0a0c1412030a0c03120c0203070b01090b01050901030c0201020d0c050a02010c0302040b03060609030a05241503060619030f0c140d1502070c0902030415180305030a0902 80
    0x10b054000481c9000c10001064640c15145007041000c040d00024041d0801003d0b64403800581c00038030469624820021848104996008008240340c0320300030030010102403642c00c2c80400780d0030000035500c0d04010b0054074000403440000650b44190300c070362505c0d108180c403210700b0030221f180190001e1424020740025035401f00b048000d030810f02e2150f41d54513289a1101e603100c0e155044002d00b1194450401003d0500c100310901c1030b00d4252040c1e0754446001c90382d8503995900c400100e4180658044000c1040c4a01c1c10042404582c5200382088189280ea038a6203982da4103425018021088504c075825402c00c0d00400c03d9404c00d0000b48901130011245111000d9036540d5199100f04880000e41d0344002119060010ba03101031500351104500725218410943e0369290756801030303d00748954003201e034005403500811212070385100040800140454592925081c4541c01c2a02c0e514500d00d20391400310342d0504804164a031a800c560517548450659442412030703001000c0217041a07911 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 389010170 1250 389008920 389008927
    0x1090e1b0d17072003070311060904020c0613111804020103111303030302030402090a050c0f07060609090501140703060b0d180203010e0a050615010503041509150c0914030d050a0203 80
    0x204400402040f0303403032142096403050300e00315000940013802c8002c050f1003500240d070104080f4007000305d044a045801c6a0165940b804100041c00a10034004010220300076901040142c0c03074050121041c85000381c0c450044043d14100b00030f0407400c103078201018000407038007090165101e07501010a09203050300250c42c2034100c1115809101d580d1b4422070020f42c00004010071800e2000001390080c51143d000c0c002400d00d5492016140030308940707250307500c9000ca2900140280d5420680080c02c9441c401c001010b854204240a0060304400503585596640807601445c0319105d0300007214504503040c1d00740140e020303280d000f6140d80581c0d881c0151005041380c025070b4081c03040d40c0307809401c50000d281c3c2032580d00e0080d0918070000d040300c1c83c640400210300400d9820500f16980301d540041510301004070180d07900c0052500c040046c05418000b000c10402d20080ea01089030012103803242c0b10f44030f50710000050210309040d0801e03015001118040c844c0360250340a03040380e0722140181c03400d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 389011420 1250 389010170 389010203
    0x2030304080a0815041107140106050f010503040503130321110c0f06090301050705031b0406080a0518100e1204030203030a030e1515090c0a0c1103190b01090e1b0d 72
    0x81d1101c6d0741c1801841c42c00003402200b001444c040c3c0c50007024a880091260714607240020b454402d0800d02941480340c004000f0702000002e00032520400c2d8168014403099459007442045810010301c0260156480b101e8881068003600c1c0c0c3d200f0501184004141e140c46000621003040482c03c903040d0000001d2180d104156828000c06100c5d18407680d580761a0702d4504001d400075121181410100c1c00c0030041030280a9029603e182c0c810b218560129543d11880b800003011803644480da00f05000d1f000810b034a89451f074202c5164015254110340e412075102c80301c10894400c520009500d980200b0011503440d000340c2110f01086024400d031503034200400009404041e0441d42591040140700640401e40f4000d010617410403000254241042080d600c080c0450300b030018013908000c08102d000c001541c04209050000c042121440714254152610b043e444000780549664242442c203900203461001504862081107000b080b810442c820041c4100507050840c02d40b0003a0440300c0090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 389012670 1250 389011420 389011429
    0x15080603060c09031f0218010513031707050d080403090f0506071211070611011401120b0406060b0a0306090534020723031b24190f0f02030304080a0815 67
    0x2214a0108071006d6680e1804103000310409640034881414420305020408508550042c1081900c1e8050074a07021a40000c61540281c068a00001c1445c8030703c0001d03004103588500c0482c06903100342c84a1400b0f648500000c4159034090183c2a0412020b20980300402c01ca0400b042d400c20203414080c075007183c2c0315601030a1050f40d400c0240410705218008964110034400c10a0350046a100409594103150b02d05a10700080d01e009032078501c03200082707010310041d0341c4910001c240c06120300d0b0b910b08a8040103400b6000a10841d0440e500d4400010f109246840c050280c8485110a070116400b40ea907010002404481c1110114426038001040c545403100350340001600340045103100340810030801d8580300c0e010110180c01808041d0031502e540394105c1c1031442030b0b160b204055441820b1039075002c19000707a41d0303840f050341161520352807041d400c00510300e490100c0da078030200155800001aa62440181d078006d1070340d0010082d0049041c414003201c0d402402c8010000c001201820010303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 389013920 1250 389012670 389012713
    0x6090f0506011707060201140403030b03101a0a08070b091e0d030518010207140f010201320f070903020411070c0608011707030f030e1809010615080603060c0903 71
    0x15241c2c0b80c034101440011403080243c0360082400d84000c1c0541414234000081c1400e000d4801000d2540320b04000c0801d650a01904d030460704070807010807900143c0100b0709608250601824010840d0030b501040381440410303040103546901424034034040500c0e083c011201152156040c001031115180c41090f5104a101036182e4000c0d5501600c0385000c01e2410350150364181907e0565000c40c208200c0c10440207550030402400722010a5001c10b8000141c1c05420407400406032501c002c0300e080022001044001c0303d0301324808040d0301995802641401040c800e072030703600128201c0c10003013006107082d800541c07440104075503540c18070040c4e98841e809100c030740e0800004900c0e14401403010800c0d008881018544d101c0003401d9840c5103844590a50790b1505014042120100d43ca0300c3c00d40721510700b05202c0e08a20894481490140c41ca0380c000c20440c00f421002030428101e0514a512071a401ca000d1503000b805410b0341d44414880c4c4030700d41d02c048032090705405851105c604a00c21000b44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 389015170 1250 389013920 389013929
    0x1505040807020406050f010207060302030c04050901032603010e0a020d0e03070b04030806010507020a09020c0a02150a020607050403050c010c02040e0118150e1903092301090b031306090f050601 85
    0xa8a46a41c054410002035030002c1d004240103880804000709140c1c1d00090f4070003114641d0030010b980744c6a1030074038655072160b03400c82c58000300c0b804000000c11140c184c2406503941f001e0661101c84003401d00c061500c1c8000c4c070a21000c2d05244003c600089455030042c0582c51042e4000108408454081c2d4115000780e10240c03081041c83c01000149504000003590045003464080c2c17400c40150f000882640003070284600080d030100f40c0081790a020400d940e0290380082001d07100d11201040700c0d20f0355201c443c00c640180901c1021406c0c9902450545d000d4070b9209010b0540a07484400468942502d03940030303680181c4450306040303004030a1140380030a05940c1c00c4547d55011a090100700d008030210300441051824040503c3d6210200d070b18181400206540d1821400d1400c00b1a5100c1030398011000c5246c9186408540b00d2081c0d44d610040700003a00c80e240c95950310300301070f14a80401c030b880c000110416005000001c01591101e2102031040000030048641170700c0f0310303240a200740c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 389016420 1250 389015170 389015183
    0x60b0a0e0414010e0601180e0a0c0e150102010204050f010e031227030c01020604170f120f10030201080a020d02040b030106020303010602061f21050607020303220c12150504 76
    0x30242c29007401c0c054900441130310b030001c2c01d15516040040b0b500c81d1107070300e41c4554070380d45810750841c09500b4000c20300c03584e4011822000b526140d02865010890580d008030480301e400300214000e50046c000d4404aa40040c094203d887c003140054418801c4034118580c540500030400c603030311701c0d02c20103844c00501c005400c5a103d00300c00c14040717103290b00e41e100900c03d52140d03074404060703a80001c080364000e920020301c04810501c80302040030340c05071043d02c0c1c2d81d6079400708014000c008103400a510400d510f10824503951101500d03041201d080f4040680000d104030b001404951458004008040d0b80a03c010300c0d09031303a103081440e1508203030084001a0000030042001c16030401c111070b0801c4030041c1d81041c807106105003510703609092080c45009003101034031000f420103035801010020b410405039401441d02020081d00c0c3e034000c070380751a0064101d5140c0004050390001520003503134014100300300c0702d0074002251b86c088000c40c0100d402404130a40c5100e41c6107a802614000c0e4810403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 389017670 1250 389016420 389016443
    0x90112021306110c0301151406071e06050705090307060305220609030314130b0403030f1b0f0504030c050906040e03040303080106030614060d0c410c0a060b0a0e04 72
    0x10315031070810304144d0b10305100c1d030b051a0100f01205000c40c8600200c1e80442e83e541344140c50000400d566025111029084c60701d40901c0c000150410005028040d100700b00070403050381c0e0244207170396500484031f105425030700c00d00c014803d0501a80c0a907401600042801c0c00a0b000a18201c20321a010f172002c4400c01c1c0c41d440800101742d0940150070024107605a03554040c40c011020120003c0b250b540039104003492004141414040d03880520165030410080c030901450321254003001280b441040d001070984021161007a10950a89098940c024281084140380c0001c105081501411882d8083d81c5c0d010040c0c07001004000400096100b80c54007402d640c90030300041c0441d5101d034015200c00400104002e15952104211f90703100400c0000004c81d551110b0080701c1a007010b1210701d80d0000c4d06060400e030b45a04c9001c194002100100401c5a003e110b009140d25004145031031826911a042e0322000030680d8002e0003501c00c2c00380419591a030b0720902c400300703024141c030207440300c00020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 389018920 1250 389017670 389017697
    0x25051c0c06060e011208070836010f05040e100806040c060f050403081c090605012904050306010b1b030307200f07050d1502030a0c09090501030206090112021306 71
    0x34002d65006000c1e912000550b90324200703000d91101d104c0c01000b80511800101e01c810401204c1c16141071464420b02d038141011042491007207810080c03e0060200b030120b020506a600c18015a41980320f199120f030301f02487d0540e40030030110301902e2100c0340c3d03144000101d4030590400c05144164020f4507141400e40c03601d4005440b0030403520400701006410003060020400010840d92140580008403e51003034241001d80241f100440c000c101a04020002501d00c40e100322080c49524810110358278182d14025800280c8580d104094040d040500108070060015001d80030100302d20305500300c0c0800e0215250300350303802100c2d01c0d40842c0318059060404051400b903541c00d00e0b0100001c02c800703200307190141d984218134031449215410148a4004020840c6c0904950611001080d5200d0420f0702d0500054020550000000780c0c050b14005102001400365034102e98015100301c0ca40800320004440315005540e105407020340801c0a0180070615a154070010440c0d6919001c4a031100b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 389020170 1250 389018920 389018933
    0x10e1e15040509090a0308041103030702130501091d120903122a0d0801090c030e07030b0105010e090709030803101e0e07090f05040b0109030215090406060525051c0c 73
    0x340c111103451744010021000243c21032105a0002d0304541c8800d540c04644000074558401c19000a4000c107520f0440d803007914194101c00e059410682051203c00e003903002280a2880542c2000030360b074802c0014010500341e0400800f092600941690303000000102171b20078945c402200300360700d44440103a06581e501c000c42d1403909103c000c000790030560860100240014010700815414683d0340000d111140e0080c0d1110340c098541c902a40c420541e681452032440809226041c0410342d4004c0300403092401002017407183c0d00c00e0b140c0741c441a0558458000582000f081081080c00c40e00010a0071210285102483c103070800001300d0090170f000419020890240c03480080c03001c07495090007041c0c8004004400d69505030360001d085031203400101c60402140e4400703504101d070000c0c0320398010311440090251900540c0c0c00d0202e00e5580300120303154450954000315040c44840b40764017a080181c008101180100104c942d15021201152000c00000d00c00c0008105170f48011010801d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 389021420 1250 389020170 389020189
    0xd140706031b2a23031908040606030f05060403170702071208040b1605010608030406120203280b030606090f070f02010f020403140c040605010e1e150405 68
    0x110310341488410710b8190010006841c0304001400d103e030080032814090504400ca01e0345412030304421400c0029401e00100b12502c1551292100c248030003184001da42c0042150510401162000d030a0b000c0b01d50b0444032284003034404c465140d141c1c04000041408180100c03e41406500504901e050620700540343c01c0d44a002184035030b907010100b06841350040b50380d008880641c82e004200380024070f08142c035841541c00c8010b440801003005240c1036a803640040b181c500ca50000c200c200d464801080c0c2ea4000e61003580c002034661001c000f041d000640245800202c41910030795070300c52004061b2003510701e501e40c013050700c0e0b5103045420311450204145908135000340c076810224141040d45200b42e0708002c114809100e40d000320800c640e4800d610802107484501d208545641e16850130031140f1808920742c1da050f00c588e4490958a01e000d01c6164125031058403032503113a038641c3c020310005102e5502c001159840100d164003041e202c1c1550f0824415546607000d507070b1420001041510b01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 389022670 1250 389021420 389021429
    0x5041b080f0919050a080406030e06103b090d120501030213180506010308030f0a05060306160e090c0301030c061103070303022a0114060301091113020403020d1407 72
    0x6082a061100100020903001890b40c291088110400c00c0d40c104140b070700302c2180c0006c00c40b1400080015000c2c0d41640140408000c16065a12a80700d6040c03070100e0b00080d0140e2200702000702e00d40b2401c8110740c4c1004200e003031030f100526489403001e400c814007483c1c22102c0303118a81044655031501e651003c0d0140d102c48022204016650551300400c0c850200341c901c81101680c0e030440300703502d11220714503800c00341d5102c4110740349980c6a10348050140c00a52358035800d1903000011601e840c555010786441440f02500401599940280026100c00e2540031081031248042d648006501c900b4484c6100b5860580030b5179880d450b40c45c0200840a140d80b0500402001580780320f005d01000c030480d100d017605482d0258460f04820708030305042404c01341c1003000c40122010003011b480e042d013050300342d0103c80300300980f10f640700b00a2500340c1e010200c00a101d010286442c80c494645418070144d60043c000006080580b01e40c00308007a2102c24609694404c9440c0300c030041036038100440805031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 389023920 1250 389022670 389022691
    0xc110c04060303081303050408030408010b0301050f1303140d060b0315010c0b0118060b0406020a0b011712030c04090509150105101d011e180506040e04080a020705041b08 75
    0x10702e540c0780108a150040d02d24200f00018031809005c1c0b5100f00140c4028008420542c0d548984e07840c41c1034028131072005254000d500303200026020981d10f01010f40310307400c82903080d010340c00b00340c0e82114907000d0000d02c01d55000c01880065882c15061060001400ea07a00a0540c0d81c01d0020340c2e60b000d4903000c0d5481b810442c00d50b0401c0300040c81012040e0441e10b05080507040d0400c144210400760025400954505401003000290340760b0010f501c0c07000074081c41d10f00c85142d881e45282400d0408034280481d20b6444044008111580c2400440d80144441c0d00f0030300307054545445000b51001038404403001e5011031a05c50780100030751300c2640184012110003049040300d03074015110b2207401c00804194100a030400e401c5901505194030810310507030b00c51000c000b410030060a181d401e08020030307601150400c041410300f03110f0100c0f02a584410740150465455030307514003080d0300c00540b10046004000c0c0000d80340c2c45600a034600baa4000a2100402084040042c040c100051506d0444c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 389025170 1250 389023920 389023931
    0x51008100e07051e04110307030b18010b0702060c010911010f0f0909020c01140a1e0e0303062b0f03030f05190e0118080301080c0306150f010c060c110c04 68
    0x8400c80041c2e91421202d003550702c10f400700e400003c1c1300300e102d44550207190041d003030003599455030402100451003103240303480420840c0400e00500031082c01c10900d4881c4a001440140442c08110300508032441c0b00610f0a40b6040b4800700c1c0c82d003034500f400700c200c0d00922407001c05081580c02003800c40c090b035403d1070402510b50340ca6800520100140c45110111607000031016031548003908030800307085068503851000c0c1040c203803010051405007403041d9140f8548039a8909000d00e40251052b2142032170003141140c81d0041000031060010352a80e41d115120f410700b8083c942005034980c80c0c180a0b0640d010405403074200035080c4e03141c01c000c1070310b0285040c0070000c42c5621110a0880348039401400600c40341c17860240e40c0108484200b0040c041d94540f02c40003080841c6c1d00950503104000c05070343e00d88211009055903040203542c20107514902c0c1c80d0494841c108903c0c440303415101458404e600c80d4250301c4903800c41e0180d00d45000081c00781e01d010801e61001300040e4116a0054404214 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 389026420 1250 389025170 389025191
    0x10c0809150601030f0e1e010c270f0902070b0f0609040605100b04121505010b030a051003021f02010c0203040602030f090301090204110304060c1d1002010e0105100810 74
    0x12122900007814640c2001880807070516407082e03001c0050780b000740200700200403440c40078030398640003547c014108205641c00c0d81020031040c05440007144540e00c40d143d0a00200c418803c030141308681d000c0521400200c0041e01031000203420b0000c1c07076040c400681c2c030202da00b040208040010b00d801c50140203001400000d4a800c01c4180d802508010002240c0e140d110750403805803080ea0120840c020041000314904000100c00d008461160a41c13201c4144201d4042c026114248a01c4207501d1083c40001d80100c000d410031507000c100301c00c0340314801e62a41d0004080e440304588642d022041c0034069a2095024032a40c42001070500007581024500000250744e1302c2509a0060390040101e0a004c0a803000d4000b00c50341a070060043c485001c10006400341364000311800da50b03007420107000c0861140a034141c2200340bd9049001c0b0402100001441041200840124219981c0f100030316518a020b1090074050010006910010f6142c07041842c0b4245d4090f080401c034a24200341c150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 389027670 1250 389026420 389026423
    0x30e060420010215090d23030115090b04060503042906010509010c0b13050d0f0f05030c090406170d0219030e010c08030c0307110a030e0405060d020a03060b03010c0809 74
    0x70980400034960074840446400403130510f540803060184405110040c00004038003c9108480d00060740c3c1c420030310502000b00140c10000113500d001d0044030401c010310100000c03503061801c1c080241000404117945040da015141d205a1281c0000341000c0b0601c81005468042e40c130440000f004911018a04019801050100a01100e060040014102940d6401100d000d4110b641052600c0034030302d0182101580700e001c50303404403064041c0f280c0d0300551074080c410011b16040780d0349d50041410324000c2e0941c1e581e0710207070115069807014000c01240e5540d40c00344101410319601c1c5521007a96891a0a240031003480000042d134104041c0c0d0580202020903400d441c40e010300c1c01c00814000706005941d0301c501a04081c0c4490800030402203144000d400441c010740807591005481c480c0300c545551658030844000340001d80040000d0201d00c1d1030f400c01d5030020b0004010a015405c5580000e000b203a0760f901c121800c0d919464207031400e00d401e21a500145242e03080601041c1342844115 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 389028776 1106 389027670 389027693
    0x310020a020715050909250e030706030b0f0603330306060109081005070e2e170c03090c0a0e040c2c0c09040903050307030e0604 57
    0x8498802500580c1e0180c43c994406082c00c0d4408104681d51801404410090f1603440e0540e44c41d401d0114040300f4040c054488409035002c00781458104a510f5001c2c0e4203162600318020b02c0d85e150700201000350182258001d5499803903007000044209c00400c07940d807002101e80b1b2851030030700282105448010403800c0712510b40e01c1e14011a41051a0302a14000da084661110350300d12280c0c204030f8001c0d402d4103288902a070f005c4081510039102d07100d03140205031010400b0070048172654480d0b40c1d20000c0d24000c2c2043c881c4c0e0352500310010001c1c1c07003082c01080c008005121510244190381c0d14801c0289a80300240d51800c0d90813000e42c0a50b4141c50810541300009101d0720014502d6010442e10088a0504159149100b015100003000c061050000700504090703651148202100c00d23210362180c60700c9041c00b080003021280380c03005101c4240d00030340900000c14080c0c0c01c032 = true := by decide +kernel

theorem cover : BRFrame.Cov 388848920 389028776 := by
  have h0 := BRFrame.cov_init 388848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 388848920 ≤ n) (h2 : n < 389028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
