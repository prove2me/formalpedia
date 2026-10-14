-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2223
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:03:05.986357+00:00
-- url     : https://prove2.me/submissions/c6794d41-f940-4bcd-937f-9546e1ffafbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 399640287 ≤ n < 399820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 399641537 1250 399640287 399640331
    0xe0f03070803100f1404050603150f010617130b070215012c04020108160203040503030708120702030a05090607020a09050a090308090102070c030209060303071a010317190305090709090501 83
    0x40d04c910b070341035071411685900069201c40e4640c0110303200c800040309550140318450101c0c0003890608498a40b012007501d00d00c07000d00603c1c0110785030151490006c1c0c1620301c1c4910840500d021551811a180c803400e48072074000309200214030500d9080d806002c0200c50060080040c08114003030392141e00d40c036145000030249411003500420f4100710250b80d200140c41c1c0c011100040060300317036010480803411442141c000d10342501c40000c2074010450100c004090640e403500358418292118a0104d840384103543c203040014a06101c075500a00d4074000a020045c170003810155000d03540c01c0840f0036204102c1e0720050071590790660b40d040c1500000019401180c41000b1843c01c01c40f582d41f0030b00e41c855404060301542000c40042e086840c00c00840d0140c07500a400c2d010040c015a00fa406000c03001d000444d0194040b447e4401d20018010075102003141581d0306080389200e0640071002024000c0c824146031060190000c4c2a1400c0e201c0e544103103005800102d10341300000c07440449074403c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 399642787 1250 399641537 399641549
    0xa030804090b01050a0c1b0b3108060a020a1e03090302060705090d06180602070c06020c04021206010c050106090c0c06050c030c0301030b0c040e0f07030e0609030306040e0f0307080310 81
    0x4101700355000340e00256664071240d00100340040ea031104001e4541e4040d864200d400b441c1030005038003100340003003140100c007503440d41800030020707460301d1454540340352030b21034041d081c0d00107008500041d0054001e040a05c005280450b40c102d00c2001900b111040c05082a0210b03a42c0e5101030b00741039043c40b15580c0702c507442c00d01c185041040c401085601d0754440018043d184d4440a10071203440300700006200d2500650155200d80c03d90606d680080708500c2a84054031810410942504040c02542c98581d46a50391a055035541c0e401074903000015001100c455682e02004228a0034030310070745203080090b56a000014540749845012a81c000e1301a400c42c1c3c8042c0304001952080b0400c49040d00d034002c440b810342c0d4540009002c1d2500854000d070242c2c0d000c900802200301c1d500c0c004035104007a02c0c0c2e01408540a00c140498460000b980e1006c101e400400000d031442c00c1641144404042040841d004140c0604c84241107400455007124540c03800001d016000507009050400340c16 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 399644037 1250 399642787 399642797
    0x112140106080d050c0a0609061d0105060609010e030313031b06030204083403052409060601050921010b040c02072306040b030906040311160b07110a030804090b01 72
    0x100300341c0740c2c990f42c15416800b50100480040d00310660301c5c0c248442051103900c40014003510004d464490050020070060347c4e00b50401014403108907205008c1c20b0302584004d800580340105550044481d21140c41d40e494161108000418500303102c0c3d0f0703214000b503004902030041d1020060b00847d62910591120702003500602090100c150b005c244a001d109204040d0403602c18103420000b89203924805480b18081403140002c10b228002c11091000705582503281665100a1103240d520030090700e1940684c0d0084000441a50040c0010400d00400034204000d0741d504400c148443c6c640541480d8685e5115150410b803070425008403130021283d40050078003070342400f90040e1180d00c00c003040d440d0034492902e07500c40c40d15072004540203814804200b5031f40340f6000c48010f80c0c0320010b88080340018030b80c007218004c0920119038030342c80c045141c202d004014542401c80800d600000010358400c03944050500091b540c0d80482d0004611410780651214034260f2280c0c116458126140c2c1480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 399645287 1250 399644037 399644039
    0xf0308011410080c03060d080d1a040e1b040b030d0c020a0501110d03050a1509090309080706272606360f060c090301110f0f03040f08030112140106 65
    0x2030f80103030a03030358010040d1050701e4403030340c6890001d502c201a030400a0440e200002e00304407840816041510309070031802c00c08102001010501085132000103000c03280f80c029070500b48040b240c0350b668020b2404000c10100d54282c44000203420010000c01c20000b00700c0d19042e030b10441c24002041002840c2c01d090201650b08684070840e00d030444d207803c881c20141d0311000944c07a55001e9210320001c071000f103004a4502e8071081c8150041084401c29000300e04c0070400043d80704000515081924040e07542c5000d886601d1a0120310485620079090010b1100c00c0c02040504641e0860000d40703000e513043c0258000f00c640d5003400d0142c00b50071107010186440407216001481c0c02c0301d644071410b50209600100030040c1160400da40b0002d85800b0740a60f5003400350034811000900080442100200200205481080703a140310f601000340c02da107030030300c0b032030004859074805190710a021f50101d0300c2000c02c0355103542d01c41e4000d0300800c00350300541e079140c002d0105d0f0004030802d041ca900c00801041d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 399646537 1250 399645287 399645319
    0x90f0b0123040519240816020d030b0406030501021201180c09030201050705010e010e030c0c0d020a05010e0319051e0f060a05090309041e1b080109050406090f03080114 74
    0x82e10442c01054000c450313a20222800f034000c1803440f0002c0400b45040c401d8070b0006180f0a2640205540090002d030001000c1035100700500e01c0201e2103070344c0340c0040029120f0100241c016140241c003165000b40d0f11440000800c40130300003440c1c034148400f102020756050501d10a10702c4400c001d9030142030316000da844040c0740c001a0f41c40030f603602401c201d40c81d4a154a0030380e015140088011480d5402c18043c0303900010000054101049070b041a5400c40c94010180a1400344240010b036014103401c00411582d4041d112040180c03c0c0035080c2c0300f540f20070340580100304c850008121003581c00211401d50040c0c96400440140b1401005806c441c52030034407941c2d5900c005044103400d82da03a0804a081c128040049a5401c00058414460350101455051808180004150320642001c84000052480c004c2110301c0031101c2e141c42c42944d090101b510b00504000380202c1e2280d0b41d580f100c0b0301040c40ba81c0c40d64a001e11030398400c1d805605100309406000044440180143c101156407541 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 399647787 1250 399646537 399646607
    0x30506060706150312110d08060d080a0305010509010b0a05030c030a020c07151d030a02010e010e0a080a050d0813060b0f220f1a010503040c0b07030215070c11090709090f0b01 77
    0x2003202031608c10407544540001550140300290020100e41002652512554054016078100d803011114400c06a0340c4400488003840f510381da410008504200140c4040000b40145400200c3c100c030050a180305284028541115500f03c800c008031440c2d4180b442036070065001c104801101c180207c0124140003280e50780420200081c1800423007410334810740d200b0308000d01d229000810307055201c0c1c1d036000500d40300c0c2c0b100720b015102405a40e100050841c020740681d8082c0c6001c04252240c2952511030f1402850003114440d880780c07a40342440800e42d00c0c510144403030003001c108441031114103001c04084a0744117440341a4103083c07410110100e01035428402e140002803e259651b51354900d0324101181803074008204003000844e841003415400900c6200d8403820841c09a41c035201c42c403080d2070444260030002c2407900b544030000d00702d08000702100c3d008030043c10545030300350b144d09040f000c0d94041554000020382d10031100d00030350b81c04580c421900c04820070480c0340b04541000059 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 399649037 1250 399647787 399647803
    0x6120f15120303110a030b0f0306060a05060f0c0106090606020d09050f040e10020408030909240d060b0405090c0307051c111c0c06090509070207030303050606070615031211 76
    0x31080202403a0072061600a8006040c00c050304806681ea413450100302070000d061400c0317204d0044030810b4850a9070f007400a0315600820004000100341c81c6810b041040c2e941c000714014000130307810b11010145070000d004d404050440640c000c1441c0341424002440c05103001d202000b0480b00131420001e58440c0100040307454025100802c01d0070002c8802c40c50101d40390550060305100080004085d00080085e0021900480e0300241c903481c0c07030482420030740c1a0f504103000b00d2215141455245445a603400c0c545105240c0402c01016480c0080d08540c0c0c1101c0000898015071448042c916052141c40c0140c80c0c11101c6031501c00316241100148405800b0081c01d219008c10130006a6882c4500f2503035418090700c0e888442c1007113262100900400744a02e80200b00840d002103640c0c90140101d612030410740e4000c103c1640b56440c12405014007a07d8280c004804020b0b8034042100740c002c413581e04458080000c40c0074a5443c0004400c042c881211040105d13a0300d0345040c0c2030011a40ca0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 399650287 1250 399649037 399649049
    0xb090a0c06080f0c1c050a060b0c01050411031b0418050d020a0201080a0e0c060901110604110405060909100b04061802030f070207080d0c2904030210052a0405060406120f15 76
    0x5a580d4071f900200d8020005034000c80843c03680498900300c04601504000e01c1548078410741c418001404050541e0740442d010205000d40c1a408803030060b04060b03020792000c503c64011401e2404150b11000d003014080d00c0d8220042c0c00c201407410555030485150743e044200c130350040015808065109455614130a25035100340e0000078008002d0b0f101d500b11200c000701da4403e9418500741890b01e00345d1401203590b090f006908010003e0344a191840040380b044071608080c00d40a096103d050b40200703240380d84594419603030440442c5c40d2082c0d40c0c18450b00010301c0401a500d003000010701c3d840710070040c40f0702e0841d440400203200408002c192107481d0710f01c0d403e00380700e400c00c94600310070f00210141c042d042c2d810301c9a188840b0b0024110040380140e000342c00340c40041d00340241d0441038800c03c44031005081d01d4150840f41000e542901843d010300044035490405c1d4a0304001189036001d03600c1034001950303403e40010080c50350703c14200c1c2031410040800c004080706100e90110001c501c224 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 399651537 1250 399650287 399650291
    0x702120d140f04080708060a18080706150b0a030b19030807030f09090908180405010f150e0607060615080103050a0b060316030b09010c110303040b090a0c06080f0c1c 73
    0x80c1550310210649029190950555006980301c6d805180d8407a02100c2500086003890180c240006190b040309900503000352600f03148c01610b44490001e803a401c4e00300914080d413058002044000c2c640602a00451550040b84040c0c83c4801c200481e45042c0c80041d0600d046442000020010000c031104ea640c54104048008034030101520031907111344c0844011810001c1c5402003150240003800e90343c02c0507007000d030031010f6a000e01080342c1c800d004002d506002604180001c101d013000e004235509403460903001c10600705001c2802c90300b10b0035003204c0883c0c13140d5081c4400159002503c4409545140400b495032450315015038425030000003520046000003c00d026072020700080d0480714100781400070712a40c0385810003003030380110340da8903140d441d00901c0600c0c644130316904c0c884c08101c84d004500b1500c44e600c0d182401d000107085014188100c40032040090100080000241450b807600503184ca030803222801e40c3d540040c04042a100108001246020351909200d100341c7d5103540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 399652787 1250 399651537 399651547
    0x3021e13061404080f07050109060e030a11040605130501090506060c03090418020306040b04060501050303040f0302040b0609130501150503091509030c2512120e0f1201020702120d14 80
    0x100c0c25841280c200104c1c1d400350220180303009100150000440f00203076aa0310b9850343d200b0301256894046502243e06401405420010a24281e42a10500c83c001c1000900c0c680d1100012130a0b0f500640104115032100c00411010b1007520400c1d5120ba4165030007844c140c4481002500d074419141000d100e00da03124608034207005030700c061012082d0301900b1a070080c00c06051103140000c0840b070890b0303101c5c100000444c2c18140401a20700b200d100140b0b409285e411542004050000c1390080c503008001840702408035036906004090003c803140c4006400e504000c814500c0c0140407081c1d10501c0420403e1058140300054108401041684103018549849245070b065210b020350308c010603c51908c50803004004140702c542d940400a56401050b0380e18452804010107800001e8001100e8480c4031545034041c096032042d807400104011182000c034000685c0d07802c105401d103846698041080750071030819054441019040c14010641212401001003200c00f10000f540c8030310310013040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 399654037 1250 399652787 399652817
    0x10b030405120324010e010c0b0c0c0601030f050c03010207110915060c0d0e030706020d080a0207060f05070807090b03070f2015010e0405071202120d03021e1306 71
    0x20100c0000d5815114a643c0e900f8501c440405010011800326807444030800d600d10258090503800030720b0603041e1a100a644002e481e00c1219890040003031140c034604010100040c18148a0300e4065441025107840d503d900d810b00c5482c28241c3c48016010b60300c100f0054022952a02444404040440d00c1c0001a5901e810b10700d14070400822480d0000004100c06540801c040b40001800080380d8a0746400c4807200101a0384051710b05c244030158110b403002a41d0580b0a051055102e00d0b0501c0251800c0e81560f074101c01c075110005040d91455542c414040040d6000315496004012883d00e4610142003500410b52072002030055020312a01414035981280551034402943d02c0c5100c0c10b0190381d590303104058030766100314030310722640781400008540d2400320f0300540c4c05550048010034659040419006140780c03e0340c030503a800b04111801919020040040550b0004181d80140c1c82d45e001c05c000d085400c0b004c0c0d14034850100d043c41501d6141c1207030354002d0110384081c94003d03480c04003c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 399655287 1250 399654037 399654043
    0x809011107060806030d092d030c0603090b07030c0e09100b070c080f1209010e060c0105070f0813020616020f0306090703050c0609030c120f010e06010801060f0509010b030405 77
    0x5080d55040340202040014115082a115031181d42c1c00d409469104001c0c1804491000a9000c0c1c0c030201c1c0404202000a1840f0050340c40c021f40300c144103140015100c1e01c4540324940150701074800240c540c1203003800c1160020b0150380080d00c90a0900081800c3c1e4009024600400f0125000c3c160320800079100c42603ca0001008000c11800684e9400075410200ca40e00c91034000c03039502d0b00c250341090346804000203030240140c1501c030009081c00c0490300112070080705880c825900400500040c00c40c00c9003885400c0c007030b20403500c984000c4c944081000d0030008000308108240300e6544180350150f100c0c40c04581001715080007000704041c0d1480024800ca4148101a4161180b10100708442030300065800c180c07030260b4201d850541444013008072512401c1c090b650190051521202d40e421302b502c030840510b40c104240c6960701c00b03c800150840740724a00c081d2869000100400620341c0a101c1c0401610900d02082045030804000c504214018403614203100000400241804014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 399656537 1250 399655287 399655307
    0x307031803020612451614010203070209070f031119050904020f04150813120c0203101503030801150915180603050403202a1c1403090d080901 63
    0x103107400c070305c10700b0026a400f000b607146640c0000110141560382c0b03508070700140e001507420000194480003400c10040e0941c0b0051120b0f202e0540c4000d02001005948000407184600410341e222195425881c2c4000c2c1035490358409600350752420000c404880301c4408014601d500c03a420260740d2204c52401003002403250300d0201c18080c0011402003841d2580e8420010240c00076543c280440d00e920340c600e01601040640100b01400c000d041d0f0f40500d0094032501c84032400103082d5921203494068640680f22080e0240195101c1403e041c000c0542207644c0d20701406c001c1c45c920040c1903004102030230f4603546002d4806e00580e81a04408840e1180c1103a8403002c80c00c09120107541c3e51036502a01404050f90100c001c1044950381503241d1900d0a600d584000681c0014003100d021008208402c6034541c0210003080310706005224152a01e00040c0c112055690001c0b076004251b0404002071003504449001d40d400400c142807490742c174414a200b109800c209016601c0f006140140c03406604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 399657787 1250 399656537 399656581
    0xf270203070312020706090f050f090403180e061315120804090912030e1507030c11060405030a020c0603090a0221010e060106030e120313020406170307031803020612 73
    0x452000100c3c401e6003c919402210b50076200d2201244c0c41c0da0101d03611240034001e103038000d070300300c00ca5950304c2c64402c1c2c041750464043d040859950b185a01421031078680358105228904289080c800c4604100e40b070040d240342e084100b00031100c21070480380b4010b01e15124410369030300184101c800703219504046034014620190108106a0a03141103004c0700315107007242001c21b2511548600f0031138007040102d06d072500c04d8401c8001c0d40c1d0360441074000b0100c00c8007500c1089001c0e014151403040402c07060380984d002e400155226074000c034001341307403101560300e20303008a0003401440801d00d80040c5113224142e04440030100003400c00620400d0f0030040c0382c20080d940c203000031508040804139402d8140d8030030342d03010711a610b6411135062ba185540a40200c51a4040000501010b106610061002d1000f40045501030f61090783c05081d940b00d01c0c1c01410390304001400c404040c0c000710b1043c840341c146403454940390b1460700018402e000e2031002d9135000110200081d03070034000030900380c66000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 399659037 1250 399657787 399657803
    0xf150c03040816050d0305060904030503270307080d050105010c050a060b0f04050703050702060610170a0f23061905090a1d03070212011505121218040f2702030703 72
    0x9030b08016179140804203d48001c42d190038003003405800c0c0242c0d103d210b150140c0710030303155440b207442d0884e8051003190700d080b07014070151341c1e21181c003824001401d0050045490540365802400550201c442c181d000728140024038480c0c0c000580040380c24a011a004400002c14200b914040340302c0700300754034001764007914050400503280e4140d84041d020303800950844c1c915545000503c0098108410b40c0000300350b81810480c4510207220141b5403011780440041503600f2800114020f4805105140f52003509c400014446140f4180301e0b1503200c041120306491403005d142241030400701900505014110b000000350344480036811800030b6841c4d00c82c03a0041c4410000c180f684039003086a08900c80d02941c0c5c1c0300914004140100c0c000b0a901c090305107800d40ca000100b100c0c120303c519003240ea46c090002d9040000c8242d4015010f00e503090b045055002050303208100c1121a8905024021850200300c40c5d142034461030050b00c80c40c1014a582c01e41140d40c000070b85026400d50004251f24 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 399660287 1250 399659037 399659077
    0x60e060c07053a030912020a0504020a0203030708090106030b0703020d1407110d0801051f020a050f0604020a050306070e09150d06020702030d020703121d060c0f0f150c030408 77
    0x104103c05001000a1400340d4900104a4100fa0510042c0c0000700900020f81010081c050501d0142181c01d62600c014940c0c0800d5a03268045800e0b42c1103c5001d8015030404020009010341000c562503110104a008100d018159519021541d001418030300400d603020901500c480419400382800c4803080301c03545070514000b58000c3c007080e00d0581110b060301a50040c0514035015812543c180c40c8000e01809052020041d44500221210340000440c40703040c884501140c814007450b04c41c0324550014004500e02401800001e11041d44068001e601000402c40b446038030620020007100c046603415460b8481c131410503504c1d080f096409900903482d050b9072080291550040621030b10a5080e0f4100204242d030980e115407641c0b2000c1c1180146d0b20200742c60700e02c2210100300440c0744038040a040c0d00b050000c5101a00308000100706648103800e81c1d100b850301080340311000f00100d0700401004a0b0040c00b04581140908503905000011000c90208907105083d91001510040400011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 399661537 1250 399660287 399660319
    0x20c010608010b010509180411060a1e0f0f0f0e06040602010209120604020102031813060806100b13180b090403080406060b0f0910020c06030108030d05010f060e060c0705 75
    0x204094030441c5015803034040507101650040c01502c0504d00c0041c8403643d0031030b201c1042e6080b070344000d008442904c4c104190683c240e0350000500480e1420717540d580001c401c030500c1442680b00c1501548107211721450340d503102c076920054080701c034020f900e89240d07020701d0418180d0f0340030000801280e101201040100f0b65583c154060005110201d03026450020300308200b903101c08041c2c6019005800c00c010f0301c1c1c82014503c00300b410a1102800c1c40b02800c050003a800c08803241508168000e0704034400b44101d100340640071001034802c4080c0103281104140d0000c14000c0144182c4491003400d58010100a200740e010b111b102c00003034107454407890710740b40082c01c0340c400b1181100c0741c0e13203231060108103c0c0014059891070703003c0c020024a02510b4000b040071b9410506d0310301d0114481c00000c0c0d071603500d030710700558001d1186800840d112013142e0820320070380fa01600641c1131141c20440401c4040c0e8031500391031295109450182d50307080c503641c0f00d41c07c0481e150006d0b41c200c00d200c00c8180c50303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 399662787 1250 399661537 399661541
    0x90804270f151e05010503220c05180f181f021e0a08010b0c0c120d02010f0b0310050910020a050d060b120406110d05040b150108091506040e01020c01 66
    0xb507030070741401c04a02e032030f0b110b9504003000021075071001c01d200e4081404107500490007160040d440044e0368055070103034900d84482c2c0e00d4801c01101c1090510404200e54109500d41b02e2081c0185012a916440c045445105c0c803107000780701e01400c43d0042070544182d203003840511007071140c41b100d0850007190024000041d600c015103107280e48600e4200114092441000d8070388280b031035680c4d481180d01c1c2030200c003440c0d040031b0406000e0f4000d071f0558442581c2c609081da4501002000a0308134101607610182c2100e00c00c1c600021002e042a055141c1568080340700010130111800004060f01c500c0065454101250690251a440003c55001041c1c00c01b0150160140c001c40078042c1d90303159500326016025100b1052038500c07101021030000f40d466001585105101d02004d420301112031200e1f42030703d1041d1000d9444c2c100c3c070410b200c016100408060a8441c1c2030030000c001d4181402a240e0713540d14034a6407103454040382d010450503510307604101c200b082c4c0f0000940d26201c0d90414140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 399664037 1250 399662787 399662801
    0x2040906061d010e151201182018040305070218101d04121b150b09010b07030e0103091401150503211c0212010612090804270f 56
    0x51840d1820b0089500720040504034143c8010118802042d11031000b020001d05503503c2140d48001c07100c0f40f011000d40b00340b240800c208152581c520b54103444d0300f864507040c00d81e600c44000a480b080c210040316114403e0207030030010820300c10141036481e402c04a03440d0161400080d07000d0b40410782d0180500b00e045544d401349140d000c000181c40e42e16414021a5407032220b0070400300400900040100c1c0d1201c0049603141d0407030900c16402c6040100780c0c0c104a07083c2c5400c943c1c0c0b591410b050807011041c0c0c4030380a21000309440c0e00d00a541490707090074060180345c0000342008840d400c401044e92284c0c00504205030302c200100000e41d41c5440d400d010317101c401d81c102d400054001c0300048034940000e642201c800882010b801ea010b400000e007245078451031092410054000440042a40c2031004142e07000ca805440f0090354100382006060341500d400d040040350608050b0808244c501080320216000d1841c81d8201401d1360280781c40991740328440660040c07810110548076443e03074102d46 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 399665287 1250 399664037 399664049
    0x6010e010312030605101808010510031b060813151b02210306190503060103050c030f0303040b01050d240209040e071a0f0c0f0d0306092f070204090606 67
    0x2d0003000340110880c11149a0320560350302079843c20003a00c860340240010382e0302d80d011440040416459055890941d00280e92401c6141c5000d5410000c1c056502201c12070020821101c015161400100921920001c0d1204000000300141003040001ca0307515144070108800041c4100814441d009003044c0202c1a8803002d0b000d400781854501104c2000c69a0414002000600b59102e05050040c60041401c100440d4034050038040307840c1d0380400c0040d009510801c01003070174529103014941400003514101c2d03859881401403000003007103076a100d41034444c00d0701e2909103000203040c02080d0345002c070034502c242c80701c0001c09502c01021340c00405090005031424040382c01e02d90300803550340b01144503014004078461064040c0c052850f00404502c1c1250103060b08003200341e070425080c5802c2c400700c1d80c0103901801085800b61380502810008089003801007015200c81c601c80c10190b050b1059528205401c4100c8440c489201e2041d01e4a183d0050810001c900c2d15241000c01400d40d40205 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 399666537 1250 399665287 399665303
    0x8040519030c0f0e0f090a11010207050901080f1203011202040f020906071401270b07020a050f030406020610060c03080606131412010c120513120215010603021305090604090506010e0103 82
    0x3030405c1112028003802541258020000b140c40e03038850703007440c4080d1143c85046009030340c0002019910350480b00d010b0030400e405845610028001580303000c0741042c00500300d41080c40100505e0800041c0342c100260140c0c0c02003038034405056042c00a10400102e04d90016000c1401824083d000000c080104803c5000b00128881801c074180242c6003055104101400c0504000c0080c207103400694104045004a407102c1e101c0b070791120706009131011964540e500c045804c00c2a41da04015150304021810b41901240e42002c1c0c0041c008480710307201400b403154603408034030151502000c0319019640301d18481e402c59294600741d249002c50302112842520003004800d1040c03010300c25000301c1e03d01070702c410025680d0b210600300a07010042c1040301c0826a00741e4803000c611203400001810348154090000c0d95004801c2c0b181009040c0c0000c070400d8410b0027072140c050404410b54090366001c5070407040030b030349820000340500b12201c40284030b80a080000207100c3e0004030014107a0b8403400071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 399667787 1250 399666537 399666541
    0x31303020f011b0e0310021204060f061410020c060f040602010b0906090f0a06080303070306031a040510020d0b0d060b01080a05090d05070302011d070807060c08040519030c0f0e 78
    0x310314243c0340100701d080c0003884800154482c40d801951414003071140a000c0c0c4042480a40c140d0040380c000342c200c3d000030714a205c01c101c00c01540d44a603081c225030801c8108001d60410b07414000141200c40342c1409804201901c0310038500820101c010803000508090b55030980c1540402d90780c01620940e400b42d82418005800c0d890300c442e0b0240b0411025002100682c1c6000b0405960a0040e090440c0180e1320007020030a8407050008603c1900715072804500f840c0780d49402c00040032080c000c1c080200c0d04800b440005007020400ea1240d002601025849084950141c0300a101202905a00040c00003021040140c0d41d0040d017410f02091b210305005546d0341842005607941207524150b680c011441c1e9182042c000d101134030b03400d03000307100003e0f074040c0300d0078004120034074008a041035900140d81046003510422090014050b1b9140040050086541d000c00034001da01505e80301e12401c080d4444189039002154005540201e8038283c0f080c0d980410b940319101e0b500a042d0740c603c0f2400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 399669037 1250 399667787 399667813
    0x20f010204120215040911032d16180f1508040f0201080c2b050106031103150d2f040b0603270a030509030f0604053003130302 56
    0x10a0301c0440780b0034031040c040c584203a420004202e406101e03005072003034140004160312400c0d12542c0e88400c2070402e21030b942d040043c450840000c5101420361001d0600090100020071402d131381e42c00027102d95041c2e0210306403000660310001c240071404104415070b540001c2d4540c02d0384030340d8115050740102c1d418110402908480764030f022500a0803080d4810004801540300301e10b102e5216190b000482d040407010b0300c82007101a083c00711f505400c02d000d45485101c1c0c905204250043c19113042c102724050000441c0b248a000092290b40b0381c0d40003c00c1c01d54a070700d403150407082c11130380468030f807400c04a92245005220304444609072203980001e2000c4042c24240728550300780d10b00408942c02c41d41e4a041000762240840c4078401c90401224041c4128401002070000c214400d03115a070322411380d601803605e042400c290054007680140c050001140d80451481c0c0c24000300510f1191564800214200300481c4a0105100180c0002000110000011004101d600c6942075410340d004000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 399670287 1250 399669037 399669041
    0x12050c0f0a180e0402010503130302120706090203010c0509010c080c150c0c16050a1512020c0a03080615030c25030807020c0108040b0601050c150406021c11070809030313030c06020f01 81
    0x813030080c0450010004600b045042e001075944403440703441260341108000c400100a40c000203000c445079915841004110301e020f0240414078070b003074a4540c0c106450340340000c2c6041c114034405827205000141c0d0805030719040c813000001540c4540c00c14040d05000b4880510b40d404070500c0303200d0b0b010350085110001c4204154804959000b05103120040c10034116003041e88000381b0031424840311168250340c501041c00a8001898045e01502003680ca9083c0500780d204024134182c030891100c00d2034030000c1c00080503a6080002124816165200c4000c441e002c1036441e00da2907522425030340c1081c20140e00c420380600c518569400c6d00d070113800d050700654009c10241d500600010914000480c2ca521170005010710a500c03000700c0b86100112401d64450400540e0181c50a81e000100d2103180e405000e0b403d00900d5105104201c0080704264031300c0e09006130100140491000102c10b1000c0e41c00f0000d4961004140501035445942c918159201c1e601c54801d0b42c01600880340c1150b1405018 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 399671537 1250 399670287 399670291
    0xf2a12090c170a02012a022115011214100204080a110d03020a0311031c050f010605040608011413020313020906010903020a15110d030902040b1012050c0f0a180e 71
    0x42c6c4608039141c11505084400c1407601e12441001c2d169004d101e005aa5880034000c1b0070440481c2500340748910f003120608011000e004416802031540040203021210140c0b005119089414070b55850740403401a814500d4030340b4520101d500203e40850000301c003140d081c0b44da034031928641e070b406140134050103440002010050096000808104080303401291400000c81d18841075a00e824954600200400c942000050490f6070319010452005035442030300340034150301d080c01410306107040c0d00140b002c07005000365024203070000007580d03880e114540034081d885101003055440c0c0c6002080003065140c0721005903c03404100340441c0155005010610a482d00a0042e161050802440480039030307028440f001000120900c54000c5030080c05030355100d9420390340c086034080030350040106403048039a007603100752140704600c06c005030401c51060001c0c4d13000f0400305181e82d50008401c200d024040400f034143d080054000f400740d40c080c00002a413641224082c0c241c41e01e984100d900d440d02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 399672787 1250 399671537 399671539
    0x90f0b090406090804170f0111070c0308090406030c0b09100e0a09020714070e150a0605030a0e0a02120c09090f151f15030f2a12090c170a02 62
    0xe00d004200403409941101081a020300d412600e403681e11100440c02407000c4881c6070322504200703925000038401b030250b400ea0403030701209941000c040d511940f07040303009840000c0070100300040640c401d407901e40000b40255080150212959a5041c840c00e283e4000355400d417180c0c10358a4520b802c24015150199080c0b0007800550310207003082909030082d4429203081e2900045040030884c5507000304060009000c1d14400c6036580d05103602ca45e214500303641886403190a00754418000746600001b92a40030400840c00304410006c008200e00780121600c001e50044416100c000c8420390010303c620211200780d0390580c51780d45001e080e41d103404c10840311000c1508041d04160070000480d806640020400510000707030b050359052100350001d07130340c40107108180d179501500d0342a41500c1000d003a00003e5030706014a420040784001d8418000310040c5607540003250000095104407070410300c04460103410400c05844d03040000301d1058a00c6540941070310101d5461451101040304072030154 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 399674037 1250 399672787 399672799
    0x70c1404150b0c0a080c010902011205090606040c0c06060303051b0705030c041e060e06040b1008010513020705073b0403030513050a030807181406180d03030204090f0b 74
    0x1c10800d00b09140d500c440403e68141c8201c3c0c40f40d43c0800c008200901d8582e00e081d00000345240144005030041c66084071070002c55103040f041020092011850b035a00c080106c400081e080c144410a8403da0344240b005052585451404010507400c200101810040b80c00d502140b0303105d152000e50741d0300c079501884e0f4240d00001400d4006d42416040310b400440d034500b40d1001a0140c10703d0074100d454a60100d141e1401581c00e00044d8282445003c800900595925440d0105100302902c40041840303003d010f032030072501201c410303801079069405081e8048291038030030b907907003502017000a24980022422a141400b400308005c4140d5202c550010b0f000c02e242069a071a1000c0c2c2c000c010081030706200c001c00c20540f80014006010038091284a41c81d40700c12420a0400200141d402a0340c020854030070361000d002081c081c10b030b81140c80c001260b0705a981d00018500120110182c1801c6030004406840141019050b0b0041d01c195030183c001048001c610340259025120303954007054000c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 399675287 1250 399674037 399674039
    0x1101230708031510021c03051e0411061b0618120a050d0905060406060e07090302060f0705190605070e01050a0e0406030209101a0405090f040c0b070c140415 69
    0xd07092070051a808040d00800404400307107540800d00345908401c101006030420b07020294100103210410710780c411140380410441c1790000c01490f0a007048618012442282c0b0000b40800070725650b030119040024100c2d40d2a034100e0302c281e415a130801e50606005000d1130000424120000a0000031030fa410001082000c40c060300105030341d800f405684081060810440c07a0701c1407613000d6810100d00c00c10040186241a00385081211550341260160032109410b00c5455030344184400203480d012a815990b42410105080161281e5200100580100c010342a10082c4040c2843d03c154040c030030078001d41d510074008680039030049112901194090140c10074072882068407698480b0013810002c1c40da0b4498000490007101280d4180103012070107810301040e9084006482d0f42808501907509241c144400502515001005000c081e00048005000e1000000d080401850880550355960002d41009089081c0f07e01600e281e1180c0e000082295081074880c0350280c001d10f1107950134072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 399676537 1250 399675287 399675293
    0xd02030901080415060e09010e0c10050904092910061e020a060510050f011e0c081e12160906030c020c03060a02190c03090e1008030711012307 63
    0x4800241040e540801c03207140c141500f1480717204a202628070042581e07903074034141c0c1c0803030709480c043c00f04c101d40354012402284403500e44d00440c203110642c074140652503a41800c049802045602800b070301e214a01d4008140501803c81c0902ea402c41d990108942c4e6030f140981e0804040b2a84110303000075040f40b0b841c4100315030b03800c1021a03100003841a60100b0300103468440503a00c0070744850040102400d01003144e80b422090400c0100400c0c20315124004900e03603200c1c890710b00d01c4040c00a0084074a0b140082140034000c0340c4000204130003003094052010644c02c119041411072508091034600400d4581c000403141602d580b0381942c910071560304101085000c0c0040300d22820540c46031803078403e032a030707000c0c440144038810b02d02c401602c4561000d142c00d1001200b01c429414403542e4600c00d03001c030354000c00d07200540f11030341e4800300d450315106030403c209050b991114000740030102d1100f04114800300c1c0000b4290702640e410248900b6442c4000c0948000050b822803100100150000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 399677787 1250 399676537 399676547
    0x240709060c0f02010804083601020111040b0703050f180109140310090c08010606080415020f0409110d0908091827011b050c01061a0904051009021602030106080d02030901 75
    0x2215210301da4050400b65101c1154046080748c2c21000080b0200b2506008041095a0070380d00c010340c00d01c001d000c0b645808621088030301c518000c40b0b542040c000f41c4141458040c01c00c580e0401003803641127698642d941d0828460003000c92a5a00184000000150070502844a82d0382588000c01406000c410940048000c100003102203034242c0303156000094444080c49a0001001d103a00c603128507140c50300d42101c50b043c2011102001d244144503000900603858180c600b900e290110000c1c07283c607120701d5080b031030103140341e0482283c2c240b1466070104000e03040948071000040e100c103503070808040c2c1000f020300011100318100001c0504000c52801500c82000241c001501c00050591072014446102c00300d0100d010b004640d0000d0f6000e4070480906c00c480040c10508401454040b0124001c0f416210749401c8a110769207500100f00021b000b20420741c01031070054001c640d900030100002c010035002c40c405a206c1c2d46032a00c005080300011804082e02901e0303078040c0d0303d011604401524 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 399679037 1250 399677787 399677791
    0xa05130b0a030b090903121303050d1503020f0a06140f0c0601030f020316030209070c080d061e050a050a210822080309030a060509240709060c0f020108 67
    0x5002204100002038140484008107190341281d54045039a1a445050200b00c060113414845258820400742804405111403160000c00d5940b0b0364100a520381401c032070a00869052000325440c2c29840800d4050b2007040a007168401e480a0301ca50b0301c000c0421100b200035110f4040840c603c032102500c840c000134014209107118259850910072804030091500f0400d81003158004483e0105c2401d619042004000402d8040d1804d20a02e0271580840e00c00d5002400003c2072250b0850f00348200700400c0166001105001e5040242c190396109000040001c034101500c5034649003c00318142c01c0048615095510203400c8442032441e10801d50b9500074044d04d0040403101480c0d20314002030001000704400d850360071035442003086250001c001c07450300760300419059204002c000041e880116000f48295004040040e85a03944103e250514000b00108081c41c0582d0700c4400e20b400614010344d0040348903a80300d540c510746445c07081da00700c000794401400d2502c29140a000542c40754004136 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 399680287 1250 399679037 399679057
    0x3280c081b2d030f0a060c0305010803070f0611190206010e0a0e06041401090c030c031e030f0e0111070909110a06090b0307030209090a0b0f0613060c0c08030c030318120a05 76
    0x61a004c03a468880741080501002241e0b4161141e205002159041c0a01d50250903a40041c500c0e01d9a6556503100b003d07022440202111384039041696100224001c0d101c5000090710010900f94a03803c0080d104c810074000d02c00815403850115a0103486071162440b81c103140002044542c440340c031281450002d28840005c20742d00d80503500b00240703241d02d0b84d40c0114402e9a400b8251400e6240c16542581c0066602d00301020040032140880c0d800041c0d48000d0130a801d000b400500d841004880380c1c0d0f02d0040500c2c40f0721845c1d0300011070403100e500ca504040e0080c4000c03140a5031440400c42c00480c2d6100782000900046c100303100c04003401005541100b480d00340149415882d00102f095260122403003100c1503540c040c40d80341e80c1426236070400c803114211441854110020a105021040c40c01400708121241900f075041003008003e00300904120b5045030345450001322100c8d607a5204490f0394034104c8005243c030003451000182134070280b40b50304515003400382000048500e600240000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 399681537 1250 399680287 399680293
    0x319062102061b07080c0306060d030516060501060c0605010f05090117031c0b03010e011e02131a032202010906030b061b0303061e03280c081b2d03 65
    0x181a0940a103443c03601c030014a00081d152040c503000c0100c1c28144255920781c000e4000508019207a51100c0000d04841c0c1d05042082d162041c1410204130b001d198140240443d1511001207001034001607044465803091170144043da881780140039503120380b0311429421000700c10048c0851411181c01030041d8149008590030701100550b40a4001d6030b214038148aa60760b0f0449070a0b0b420300b80108001890000000e001102420401e80f1100c10b00f52901e2082650210b60724103503840d44010800205041d2540d4905900240d1000c0c40c0c590041c0d503010b241c6503111410140401000e0705100866405031100e1103440d24201e81580a4080a4442035202d2810400610b510507070449110646041c00002d44e12807500000340030001c01c0140d8241c92000300812000601d0340c0018003402c00c6601c000c150003d24004210500701007107456002003160315580e0002c030355000005070150180c0101c4d66003031a214007001c01c1c030001e8034082c03613141c02d00c1ca0300340015072005a10440007040c5d0b6070046c0413 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 399682787 1250 399681537 399681547
    0x61a041202010e01021009031709030a02070528170f0607050d1a1f0f02070302060d2304050c0103060501050a0c030c020a1d10050a0e1b070605010803031906210206 72
    0x1855007247c200c044c1c00c07808207203030706609903014202c01032055214101c0300055240c10703580400a9501e51052080c64800c0b022401c00b900b8400b031034011906000420041d4507042a114411864407100015561a807440f4441c030500040500041a9000303d00c56103906181c40386619200340900b50300c02c0b80789010008062400c42988032101c05020a1030f1581070b900007000500c0005003090510f019003c21584441d0b000d00142e500e4000321030117803120703841c00206040d00318040c0703507152001c903070f100c41d9882510b08104c207100e404140c0c005c1000c400d1360100304042d2154019108d90190102d07140006a8000f4000d00103401509034108282c0020882c821060b6170390411110800d0b2031001800d5002114140709142d14120030b500c0180c001251500912400d106c6400c0c54a04004c040340381d0508002920310348203c0280495403c250030000c140070380e41e19014800d030740740c1c000d07507103921360000b0f00702244160151803203041c0c180c46a00c20807071000d29900d00e825034404450380e0181ea0020381044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 399684037 1250 399682787 399682813
    0x40512040e0921121f0f03110406060801030b180f0106061106040506040b0c090d03031b03060509060103020c100e010506030d0809030a0c0609020d0303061a041202010e0102 76
    0x40c10040680d045610442c0c9030031400c450030165001c2c00c00707034003035070000c800d0a140c0229401c1c0d5110207048548845656108080200e8000c42d04a840c42e5100d107142c0c011032a0101c40141405990140054200c10810041444122a06407280c10b00040380382005000103124800c600f9046040030700c1000070f003140d000205051104103041c04101c1d81d5030302800c000a54000f40710b0822200c100014001600d45510780c80c0c2c0b83c040091004244c00441c0340040c2401903450103981d032214000d0106075250031940f4001e03004107810703840e20420b06000350f4864107107842402a8030603260060080344d403d844050056019400010044000d4000c0011844480c040c1c0c0c460441c9040500c40041010304200082c141031004411035001006000003c02c00820000000c0314142e101c4e070b1500a0360000b440c2007040c020410603c0080d44030310380c40507481c10b240d859048102a544c1030850b00b448100c2a6500215a02c111720071414110082a0504095802062000202401070068440c0400d00712 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 399685287 1250 399684037 399684073
    0x3070507090f1109030312090a05030307090e0c090a060e0102071205070f0b121609050907121a01020a0b0a020403020d080a02010b121e0f011107120519080405 70
    0x1d08125049651014020075114260103840d0040e900404514600b241e03420100e900d074855101410300815a030008240c014104000340010701f41c008040e240c40c2d00301503d004008208600c1202c405001c21008030f428800440700b101d600d800010f01e04d0140d1440c01c41d05a40c0c00d02c6030f070025030550003180400150f207109000b941580da4460ba000e001e52608110b000403004c0480d411186d0909024481d04615883d2005000d4000c05c0341050020b51202400d0203c41c50b06030780c0c1100360002449014003ca55801205a0000103411501404a141e03d10300111000c035000c02d606005a000380d103402c0210344201070494000c0700821000d4035203038407900401c0d035010160710200e40402c80051035032100c5074203120700340d0132a0003103846810200c0107080b441d54980001c03100001400034081c200c00800000c010b01c50750b11040100034041301d2003040aa140d2900408020788e260146002107042d524030030400c4584c41440000038280380c2000200448030440001d00488080c450f020480d00890307111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 399686537 1250 399685287 399685289
    0x1e0c0f01060302040f020f040909050726010c0e1e041107050303090c0f0604090c030b0907112b05030a0f0204030b04060f050403210b0a0e0106140405010e01030e03070507 75
    0x800400c00c41d1a6105000c2114100a00300703810a1050010012482d1008115000c9038101c01c00030402c44030070708255003030914a078410344d81000000166071507082c00407010504050a000200242110468242c50041c40c2c0880c60390b0240034020f203842d45082134070001101c60000b81c8000380600710044400016403043c0d80c16150f560002c0204449001e00700320307098002c0d1040c0e031945141c070004c0000c40c03814040c81c010703240003d84039251400b0013031207944010168203004200300494200050041c220410401c9100207a0003445541e088602d520222641c0254105080701e030340406244003102c03e90000751400f95155202c081d040d0a40b261030000d03001640c06009440014140343c58000200c4c0c400c41e604001560030442004040f07500701c000300600c01ea0b00720440034186010307a41c100050401d02c6a0740d41c01482a44040b4102003000e0400c0e05844003030700c40f9a000c250044040c00705005512503d400500d1a01c41507440794480e810242e90368062500721f9080089540e00d4078100141 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 399687787 1250 399686537 399686563
    0x1060503060106021507020d021e01020d0504060f060905040f0f14030c0705011124130c120b0906220f0b0f040210050403200619030902190b1e0c 64
    0x3826200b045c100707601d24101c1d003103010341c0010150f6104000b4060340710401c01e00c50031940c0555070143c20064030290121381c030b141103100c03041110380b4140c60514004e020f040843c00c3c1e81e6207050b1002c140511544940ea00482e005011400c0e00505541c851001011080c0122441038105009040000c03041002c0d04010001b000a407001070f0038400010315606409412075601d43c420030850401c081960020b407040c02c00703941c5010f81550f840303150790b104610b00e0500030504070400100003050710103030541960350780c070520f5820a6515140722f15070340d40034142c40c400c01b0b403680c2100103400403018910b03070f200036880f03030300c00b11446003060f1aa41c0c3c41039400c94001008a100c0070401085142c045141992001c00341040381c10581182c452a9191480c1c6e0204c1c8100c804c4d000c10018203a80c1c3c042507643d048040d0305000641411880000c0103004c203110100e0241e01d2100e000f010160f0340120781c6050764540c0300c02d24101102c00304011000d00c2c06036001d100d00303941000300ca15001c0040c000d6400c9940c0d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 399689037 1250 399687787 399687793
    0x1401020307080f071d031e0a061409070e070e060a08060a08060c0d02030a0e03272d01030603120c0201020709021201050d080f04170616021207050106050306010602 72
    0x140050015003202c50003046208030403820410000405e0300403010301c000603483c500e00c9000003d1200400d2404145291703401110111144105c0c04a10024002000f28402c3c1030611440320303c5030f0801013404007550200603540060200b030012542a20302c559010075070b031404001d03100414010075840e902c14041007002849141c104503580c00c0c0503141e14028000c14006000c540362031003013480c0c1402240da07904040d40e00040410001c920903008001e14400c07800a0307a50318241551081c1503286085203428a02c91504c907401c945290002c95211456800540044284c20560040b450b003a41502c030541810b030350305008004500c8400401e14070403515250900703401c080d4000a8941102940100c45031401040711024010150b8003003411a0403e40d4480c1501e030b4503142c08080b41c045c00000e018144c4000c0b9001031081428404103086011240a45246032940720741680c08010004e440000760f4440040000601c80c1100101100343c010b5000080716030729900000d085c050b0a9000c0c0006034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 399690287 1250 399689037 399689041
    0x9080a1106040803070f0c05030310050a1e090507110d05090117060d0f0c080118030f080f150f060d050a0e0706020c0907091203270b03130203070314010203 69
    0x59008148031900010100040455103801d98480f01c251000174400b000304200c56180c3c48015019003503005215074850123607512842c0404164070281140c1c82401d1292144050004512200599a81d03c204040003224100340c00c14099001810014043c03408001c081503400411030020301940503600b41176030311203586004500005110b0342036404000800f0b400c03041405010741d60324018103402039002d0701c402d072030101f50b042403e0101202d0380041140d5081c10070039800c0403035101025400304d10030784a1000c40c0b449401304554207002254181c401c07070b07540c00109000182180e4403c000c1e010080400140c0c02003000400c1164000101c0c0128550715001800419061030190300f541e04030172001002d07110b03e0003000039038a007900d441c5c02c0d000740914000f242d01c151182c050030303001d050355600f044802501403800402c412003640e00e102081c90060740e16004803011342030b035100b105d518100e0700b030940e21041307522040103030a104202e0f45807260040000c0000e2480031803c03c030f2115071000580728 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 399691537 1250 399690287 399690307
    0x10306050601051909030b011707090e030f04030b040c0f0e060f0301020c03040b0306180708040f0503040f06050705010e0303010620190f0512030403050a080604060509090a031d030a1b090908 84
    0x50001a0030003c1c1da100e000700c9c0404c09150008444084962409001c160710345480c0005041d40704007680456800b800180110512100b20340320b6024071f11414607407650980c1c2e12310151500ca110f000c0e0000310200000410700b5860328000c00140310301d00078001450410510540351075a80540c0c81195080404002c00041e450030845800408904425480003883c1480005001d000d004100400901c1d41d440300c4400c1c05010015034024040e141c801c00e4ad16900e480014050380c124400407031303856081800340c81d03000c840402980d04032141501c035406103416482e64a2502078501038010440e01c039121070035901c1c031204c50300c0c0003019000c1c0e8010321036a030441c14000c2c20044403280241103490b04109010010303074041e04594920180f40740c1716071a44c407200c00140181007590302041e84013191000780800c42801180c0008203501c641c8810602d07507090342110401c84402000c03d541078018040d5400450030132500201ca009074851000c0740551210807080480ba0100c10a84074204080740c03d6101c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 399692787 1250 399691537 399691553
    0x90614030c060c03030601080c042112030b03070501050903210c0d0e061c0207050a0602090102011406360403090e090120090307081912140301030605060105190903 72
    0x300090754994500fa9050030610f90342d20000d06403604005034100020201080101a18050801924110140c1110307074241d01d84544a0481928008038004140c20580c0c000d102d2064441c070058040c0510391b19090054400d5000408088d406000300c1584006010b8804244445802d184404588524080109a1520f2181c2072170500303000d40d800c4005410358540d4240c401d220010b0141080740180150b0300381c00b074064080010614031030410100c0c1008196006400c01c104280c1c0200710b010080428404412130a807009504052400c214010702e0001000c1124641da001134440208108003038084056801104c007a40054100401403240012402c1c03000e41200151000784401544812038912a40784600b40c04507480340061205400e840c1404144010b14411054426490009000446194494004070340c10f910003044102401d00030103409060702c00e0806100e04580c00c552b5101e0061102801c0b80707041c0a401c0c010303984105804040741c0e00030040340c4c1e1109041c40c558a84404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 399694037 1250 399692787 399692803
    0x204021c0527120301090203180f0d1805010c0b090f0a050a0c0b04061d04110403031106010803070302060c030618130308010603061206090f02040203040f200a060f0909061403 77
    0xa094100d01c411403108200f030003d03030741503461881c40140e40340c4403c026090445500301c1c848481c3c0c0283c01c0740d02c950f01e4010030844402812501d0743d50491404080800e00c140c003a0041c00d01003581040f000c0d01183d8404002503120740c8034002c8810090300000700b24604100c02d401281c6a6002d00908010441703100000d20007401c90580c068206030030290050f00407058a48020750f5180c144402941c1980c40ea041300d500d0010403c001641e8039141c1c2402401030242e117140591603c600b10000030400c000004031500c50f601a030103000503844860050121798006000c040c0e0243e004403c211040d00c0001b8158012000320385401c04400039868003801c0140140d00c24400d041c90100e080083c0c0d0322442c01000032944c0301c100010110481c0c604080d4181065102940141c40481003000f0000c1c08003c50f4030060040c550a14502100c041c00032001080c028060307000303401148100540e078051585000e0501603400c000080b503484079100c2e4100e81c0a6440070303240c01d4017a40054428101406100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 399695287 1250 399694037 399694111
    0x7030e0309150903160603020a030605030706050a30050405010c0c0c12033e06130b06060705100605041d150c07050708010f1d0a0204021c05 62
    0x40c1802440300000d03000d400300b014000c0c400d0100040e802265a000c0c80284420503c651521781101c0d00c03541d0007002504000443d40119142040114170f40c940080d841c02282e8650780c40900d0681c07000c1e4111551030850203100b403010071800e000200100341e02d000f816480c248010024081c682414101d00391030304007514905021400f80f100700030496144951040e291581c4444e08124803520741201e0303081c42e94800341080d4010a1554181c008003140b2405104c02c0420081c0a0032201c0c0a81c0340c61310016590081854045204003002412b186035007503000c000241000c0c00d0902d56201e850030205001c02d082406030740d804080c003c0746400c0c895501d103a500703003119039100c1401014945e654000c00b40482003a011010010706041400c1041300c207056800701c282da05103035442c0354650103041080503035002d481c00c01986030500c600c02446c940500c40c0120040404644540922000390b1168424030019072203090301c100d80303a584e8052180120001200e0b0aa0000d40000300f110303507818840c1d50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 399696537 1250 399695287 399695293
    0x1020d0903031a09072001050f10080706080714040306090f0215090d0213090203030d020a0219030e120309040e0a02090708040b2e09020d0608160b0d0e1507030e 71
    0x12840513201d0300c3c140c0c3c0d840001740c20030550301500c948400040c3c8009240541c01076081c0810844000754214105d8000c080e01144001c000392112601034580c030842c055140011039400000f40c074144076101c180300803091100c0d01490513440c0d4a078841640c58000b010389000407024803410440c00c140890b45a6610f4945a140c14100440c00080300701021740806441018a581826083c00c21a40078002c50f41d4010100daa5820420441d08083d400c038100400160140304200741d5007101400b2040b01d0b00350301d0b83e5100718001c035030810405201c403144e40400280c40f050003500c4407034480d841620b9040c40d1200041111030701520411124140c02081c101c04c02c2070100500c0f0020f46601902500f0800c0c984808282c80c02e40c4400c08040d00308080d10803d140c801d01000600c0014070750040007a4118840140012622200207580d20000c0c420003c0b865010274008104000e8a44040c00e10141d0010700400d01074100c2911030310b00664890040d8a00111030280000d09400d4400c60181407001d0001d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 399697787 1250 399696537 399696581
    0xe030711010315121707150501060c0218100801060f080c03010605011e02010908070303020306090601080907090b0a1706010806010e1303050a0e09180706030908030c091201020d090303 81
    0x85003168000c0d62061420504400e88113604003e104425420401d07200103085840d2161410451228034011104000c02841c10002080591013000c01a4000e90081d122520100c19104c1080c50010010b0102c403c6045042c40420501e80a000d14001400d000c1c001c24485414652454103092841c1d074600d2290385400820441d40c2d03045000000280c460718590004134050030001d0380503041e144001400d1042c00250f0404054040d40a1402000250b070780352440ea0f141700065440d02001d50310f4520a0380100c000300500205900080b40304c01c0c0c00b40424140541d591002e02d443c18070704401d0411074101000500071540100205401003e0f5112844840e0515400c440408442071030080c04202000990451070f44c09401c114a0f58030000d45403a0151a2464042d45022540c410004403801208000903951f44240100420940c0042d69245180c445402e50440da50000f101103400c050000c43c1e15130700303410a101901a890380580301203100305032881c0c010202e071b5411506102e05040d0400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 399699037 1250 399697787 399697811
    0x602100c030e1c051201180b1020010e03030c070b06060313030e010e06031006030507020313120512190306052e0905040624020d140307120e0307110103 67
    0x2808a040c01c3c03541c02848607070340c00c0702c0c401c035001e20981d41428201c00340f00000150340c8071101801c1401513900030342006101c0b2584204003461044c8204072001407039554240b03885c490551030740381401001c4800001c40c2640748146e2400c540007100c41c82e807808001309140c02400100c41c0210340c069411583c40380b86103420320b050040d00103002405400c00609111200299005501080030910010310240d140c0c9040c80c8020024611409030f140000d0074880451840d500000a883c009000d0038080b00b5901d013028861514011800c0301034405104405401610020036001020000c824810030200043e080d0006400c3d10f586070300c40b5000c4da000c0400c1017840500c17040f04800c02c0c620030b04503a1036501241d0045411041503040164801d24050f0009201020b00d03200c000045030303941d8416030700c500e044000d81e12940d095141d0b2001c12a910460510b40d54040004c540c03240480c140040d664141c2c440503421699040c80c08040b0b64000604107040c040c2007203c0601854007440d045c026181450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 399700287 1250 399699037 399699043
    0x18090a27050f0a1a04030e0405190b060f1b0109060504050f0705030c01210905010f0207032003071410060f1e060905010c060b0603070804031b0b07120f060602100c030e 74
    0x143c90b00000120210342010f07c10088049a001e00400c18801b07802d14048582204c0b070114032032181c0702d15040c0802800d042c45015208178200c01c6440030300f400172001403140c000312100f802810ba5542d441c0d040000410300c1c8140c80c0030358020401403140d99440c90342103142c541250000c40c4660301c1102d6842d85680d001e414021342206617640c554000043c0e111040251a1a0000401550030059040f610b203601e41c2c00391030420301941d02d88110000800341e026425400000c452080d400c204070100105007040510159040c1400c1122114444813480004803882034111580091010790100180442c0c100700c441d04505101ba25845103140070005405e480c05403040030705000740d070160f42003486990780c45800d01d0304001c0e207140e0352890030748001003031104101d40840100700103410041500d210324102152841e40080792040030340300d03480240c0384d00308072600100000791150800706400150b40502d81c000d12843d0010aa200761000c0008291008407140104061400c403214009039800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 399701537 1250 399700287 399700313
    0x70203070b04020409050a14031c0911012102120412051303030e03072d15020606040f110a020a0b1501020703020904060219050c07090218090a27050f0a 67
    0x104d0b4002103480f01460b1060a000000303d0113403c002d0090405025044040028003880340d400f80c40c41455810052508200d620051001e0500c2959089615955005000312002d40c0001000076400c0840c0030303d450281da00520030608104000401c1c001040900603030000c10780342505200b410043c6000c80055070116521010301000a50b102c0c1d2031b141d840c10701030700e0043c00c40d802c41d103010301c2c5000d101094464501900070200c201e02c00000511000e0241c0c1003086101c169000e822682c46900820000e000f080030003072605039a4201d0394400d10a800000d045035049a0003034000c2402c603041110500c0790007840d01000012407590418561787c0410b02005580e4102d91700043e545541c100b0300000c0c019221110542c082001c039028000e81c000001d09419490101107440311070f190780d4064140d000c0c1c90340d640c08240c00c118000d01140752480801758030072100e480000c0c1c0c00380c0a46042580c5140301d00b880c400c1581d180380f0542408804d100b8071269070320b107030020001e18001341d03580003a420417 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 399702787 1250 399701537 399701539
    0x60b01140711040b1215010e06030a060e0705100e0301050c1603120207060c081b040f050f0102160f1e150c0510090c05011e140703030e0a030e09070203070b0402 71
    0x14410141c5142e6161341c0441d4640340c010306800900f401c1c0540301035403070b1030120507110080e040e9000080d04080380d540c1e043c800d140c0a000340883c1c004a944020240c008c03991070142c01c1c040c0c4440800c00b130310342c91014035095400703645003840038654100741801c40d50054004c4c00788650410041048121a0020803032141d031503c2c0407015561260302c800001c1c060314000070016410030b160342d4109948140713828020800740e6070321900b40310320a000b464680300c2c502c202031100c203140c1001c006502c0d000d03203416800041801503c1200c0070304014a0001e28194104800004c2d401070144042c0d0b050605510301100c1c0b01e0484041b4a0a1125181d0b20031b00a0951304108540080d441040040c2400291a58480400300780041c0c00341e0300d40007890440a00589000440180200001c9030710500c054001c01101d807500d2464548160303101c3c403a6401b480c001d809060303d504000750845002c00c003010019001e80d1b107101040c1000d0b4108803400d0005855402150f02c00e101c081c0c04145070032445600594 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 399704037 1250 399702787 399702803
    0x90b07020a090f38091e090d0f020111040e0c0c150402090c0306012012030901090c05010c080f13080607020d020d0f020c040525020307060b011407 65
    0x509100007082003040c0c0d0402ea05083c1410500c604003c0c090b00071440314108030441c07411146412100c1c0000241e202007640030749404031691401414140c1035240c009455a00703c84412180071a42c402450098418041c190f0100407444200c590116250080c41402e00c0280025200c50003c248680a18081d002441c10504c01050300c01079564110b81d910f05040083d85c0101c14841406c44800900721010b0b40210201c1c0d00080020842c101228801c940517141e03404891070385404004641c00311807c00025202d10b2054101000c1c03820f0286114484041c0049850422490004202c01c0581e01480c180800c0c000500c002400302e00950f00000b4204003003503101d44035204040099459a40814128040c0b90103100b51706a001c240b09502d020710340c08031580c01c0380d4035800b00e40f000c400718560390044e001070000c0c004a150542040c3d4100751000b2880709000c10388012105c814804201307900250b400014400700b001454000c540c0705217401d0030302001a444071003540042d4800c4100044c0003030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 399705287 1250 399704037 399704047
    0x70c050301052d07020a020a03120206010506071505040813091d01020a08070e0a050a060804110f030309190801050106180e0121060f020d1e0e030f0a02010b10170f010501090b 77
    0x7174401c101d10f400964000b0411001075541e42065481240f24100c22030050041c1030010489040020031a01ca40e81c1c0040c3c1c0000745d10010201a0003401c0240080b00c01c01000c12030107c00c1d51081ca50400502521000052840c160111b988140902d0034503c0865034014800c00c2003241e04880e0f001ea0000d007034240b0710507030000301c0006842d6803401c0e080030307510540a280205001d584450a548141e104a54007401031003040100100900079480880c3e26600030844000310741400c541501d5243c00402e02d1400c442e45501c0114203540d0240c002c0c1c000142c000c0e40d1180c07090700540300a00141402850714a595041025440c1310a0824004a0350340c8030000301a02000465445885108102c0c0700441d140c04810683d00c0140c6000710500b500862413250580d080182c900c21015100116001946004400d100c0d60030305070085080001555a00c9603855903035203401c150341c070b8008480d503210320152508804001103071201601c101b0f62030100f140144200e0b600000540c00b507030b0003504803580f94 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 399706537 1250 399705287 399705301
    0x105040c1a16030e120106050f040b04020910030c1709070b070201020307050609060117060c0304020d020d0602190318050a0602030c040b161a040f0809040f02070c050301052d 77
    0x5114091500c0d89a403001c002403803d05030711606162500104a4504c0421300d0025000d03801e03103501c1d028090b888150780d201840d03d80313003d43c413580e40c5190141000d17042c0301070000083d101d06052244c00300071980341c01c0450b20303403075202d0701b448075020800c0056401800c10410f020340d130309502e00a9500320341000a0142c103580c000c00c280c1e200e080c0d000c4100c4200780380c90741d8040d403030790800c0c460940300c6610548220503103200031a00038441e13111000c580d400c1d40d45e15000c000c0783d40c01905007a070300b100100e8140c0012945a00081040a0780032900030b0251028100080031a403401c400e0b403e00801904400000413004a0145422500207901685903210351000c0f002501c030355400300040103030001c1e50f0098030700354603600c40f01e05001e00c145010080e40c90000d40078900d0f04840081c0516500780d03a82d00021400c2d00035006141d009040040d60320350151491080740e020007000d5030400040c3c80100024a802d00410354400030b02c0300410b41220200700300a88941c5031440851000880400140e11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 399707787 1250 399706537 399706589
    0x120804030201051804050405010b01091d0f04030e06070503090906040e06130320060907060918090c1a03040224070809040908161106040609060c02040b040e031b0105040c 75
    0x301344001041040703241803500e00503000f00b80a10000d804116051030005104100207500141095011010000307942c5181e501e0001920040048040c4907044420710b040340c075050b0103400c0452041f002160b031124004200700132840001d00d280e204038281040b11604c0c25012030000e80004502c204c980241c0d030a890b090300d6040c28402c0740c5003102c1680282d1040810005000340c0140082010758802c151191801c80322016075003c0e00005d00013102503d52509440d902ca01d24141c005e43c91a02030945840110f9459200c402500c0d80a24004c418041949814203141d00c07040054840e0218040042048080a01800c00040c0401002140a030b07019203079074200c0e00f00c2c00d0740486200d80e9892481d0002d2070345040644250340c41d0b0000c82130320000381000421601901d84649400c2c0d0150b1503c00b00712010000884200c3c1c026440e20880c000c0d6440c1d90182c03244995031100555214044440114690014007000c1049a81000c06020218400700ca190094032040d40321240d20b05020810300031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 399709037 1250 399707787 399707827
    0x30a140a0c21031802091803040f091a1206010501032304080a0215010522021204080a020c060f180a1a07030e2706030703080d02070c12080403020105 66
    0x116031880d00e2102c05003401485541e48140e0300c1a10308001103030f120401c110f4018410480250403918250209004200002901e018180d054084078603003519000720050084180d40000f2446031902e40000ca000d02c0310101e42c007a090107035950308035115800351040d9200418403070541415613804020314541504014000a401008a200c0003410180b4241460b58400b41002c00103018500e484c4a01041c1100c1c20380c1200d1004102070340000d003580ca40003c0542c4410000307101a4200003032034035445a11100b0b881a0702455409448081c05800a42000800f00d55244184010440042c0d051b4021065802003070581c0750000265031350b4800320312850700304d801052207640418038515901d0b840d00d0052401d00e102e5940e050540e0710324024842c0e409103243e04403420850402525a2160f07072101c21681c011b10090894040b241e4035120b8000c3c55000780c05203100d4907000036150081c0003095807044000c007500c50542d001c4482c3d549458080303000e80d0200034100310b4001460160010880000e03c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 399710287 1250 399709037 399709043
    0x1051c02040e15030a050304061d09070903030f02070b1602030705130b0a09020307050703181e03050c010809030f09060906040b090a060329300609030a140a0c 70
    0x15901c50310384800040c800c0c000c99221010032918000303030b50241004580d900207943d121004604050800c50b090f03800030f440036101001e00d1155000341406540d404002c034080c0800d516140318241c15814001c028a01c1a03030350600759808200204100c8502c40110381084c10a48900405100c845c40001d05000171540129440500d0301d0f100014a24203030b0004410b9a02140c40414140d51003a052099000c1200c81c800030507406d125010200380111080041040e00c204007444681e110b01c2c02000388000c40c0c40c1e410000c0d00000c0d007802004070070004218071882c24203092201e071800d03490744c0f03075030b40304189100110745408076071002d0684481043d02c07070040000700801d880d5a00c070400d003c4c82d03030041e1203510312a0351100c40016490740244904840030004890012011300e8a07002174000d90b40302c0f84080d0300401206110700c0e5000007902904101c100001e580b03144e407034511102529000303015000b100c041d041000340f00308003034110801241c541440400d8070b842c0c0201a606441010b03801e1000f0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 399711537 1250 399710287 399710291
    0x80d0b010e122107120801180501030f0605130b0c090a1409010501120b030303011706060a18020f0409020307050c153d060915090b0d1e0e060601080c0a0e01051c 71
    0x1c80c4009420114141c10b840401e04540103184080234101c3c103844081c800908002041f440000200d1450340000350f11036000c10f03480790400001d9988034072401040354040c6140c03c000c16025402d10300f52210703000030109404030030026460980052503500040c031404d414007002014204044155421448000d4401802c0c0c0b6140d40e5150b810501040c0e0300e00c0d52203040d000f80c2000551720710f0030103061010b07182e644080210f04a051a0500002c0d801b850014210b58030500000800c5503050000b544207510b6541c40940f604203c40910345003181e01c0d4200203d0307000c03100804c145070045040813400d00c85200460044400e403004180009443c98042910343c042d04240418601c1e008104041115045e80d10750b07805134040c9200321114440d0707000722600604108289005864950462801c54190119141d1110308002d4070700c048a15000c600c560710f41000040200f2585c214044a42c03142c2c9000c081480d000c044100242554120706800e8103100001c262045007074510780000c40100803c03002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 399712787 1250 399711537 399711563
    0xe180108030a03230a02090402070f1505010b030118020d0b0607120212250318031103010c03020906030609040c0b0703030203090c0103060303050301060318080d0b010e122107 77
    0x14103489034030600b5014042414140080b0105050086044203406042c00700720181e03c0301c00c0d00c00c005e544620783c00c640c81a0240030040114418070b07083c00085101d01c80702c244c4bc208403e110703000c0c0e40050303000c4946880140010442c1101c420455200301c5c0c4000d40040e6280c400b0f20444009008d03021815402110211f40c280403c64440000004d00f5902e03021960f02110700b0f00014054416001d009100d100740802c03000c0260380c54000c5001d0300b8400d0a00740344890090b00c10381d4a0031a282d006991029820161602b541028821001906828a4154038044518001c101300e880702034a121700925003200010240a56034404002030140c00041550f90001800d00a0281d0800c0d203014026006903901200950301034414001220380c540c50381070a60307180181c182c004200003202e40e12004446071201000540301001020b003511340010010b12542440f0004051942d01046240103440d05030010851035030014010108010042c20003440503040350a8051174010b00000611510349201 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 399714037 1250 399712787 399712799
    0x60308031501110d050702041e020a050711010c2a2d08030c0703081612050c01051e130201020a1b0e13080406030504110a140a0b0f0a0e1801 62
    0x198242000c002603a85088a40e1410702464483c100503c00d40c000c17134400c208400050601d0340144405d041c100780c05035610410115020203a030302101440c4001600000c600042040c03c110b040200c1200307207007880981210307a4481e00112003c440001c0404014041c964503a00c00c2503000c0043c200d0502400951510050000e50740041c007100030940c003106220101d04190b0000a6651a210b820006d044143c07a544900e20f13954020406a92904020401c04001c50003c000c02403004a59541c3c56540307500314528242100d0024116014402a440f0b554180c2000350000507000319400040e0b100d00a181e200503468203450000080507004a00300000c081a41d00062408403525200f00598507580c41003107641e030002c13021004041000c01d00c000d028952090b8800d0341e005104d400400d011040a03400038a00b0362140c1d226000f0f0b40c40489510031780381424a1300c00c5c02020610101410a140b00c01c0070102c0e409508421403c202d102881034400e5030390807e10844c40440a80f8048165031141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 399715287 1250 399714037 399714061
    0x501030f02070f210206060904020108130506070207030b0105010305060f0f06090d0c080106150f08180a05160f060e040f060b04080d020d0c0b13060f0608030310080309060d02070606030803 83
    0xf1380e1035441c01e0080c0700700181c0c40707002150307061144000030018011a5074a1b401074460600203010602e281414260300c60000300204000781c0140890f8000784501c516501d4603d4501c20141c000e5410141003c0901109441d505035821985500311103515808072a403012032014000c440c800c80d0302c0716490301c0383d0703040c050413004180031b55418030001d110301a00c8502e01d0490350508240300e8005884443d0100c0e10324840c0c00030311b40000141260f0503507079152071010b61410354121010769298204c1005007014102c0c0075001c07401440031410710011545054000703084100c04072100350140761284804901d401c0c195000001900b4403082c92602c0d10340700d081a07555903d4490800015101c1c411020002d00d001c0c40c03d102c0200d9000c0c000e10052ba4600d581c4100032400e040782162010b403642d00307181540a030740c0129000b401054008549900c4c100281814080c00d5a0100451f80c10410000d0322680380c3c01d04541c0342c9281d8130805640c0d4140b0b07203001070040000303500180c208100072051040d005018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 399716537 1250 399715287 399715313
    0x21306050405090c03071d0112020c15060a181a0a06050706050f10050103020d0b03030a0c030e090411010c0f06091211060106081306021603170a0c0206010501030f02070f 75
    0x250b81060295486002c00c049170703c41912690082807824403050741c0b0b4120030340b0301c81d0612010314100c401c02da440d1100707100780e800c4442580c0445d005960840040c030701d00304855034050411210125450318002150f8240f0003500380224402c0e031075166000c1c1c00d1810048038291058090700c4010500c0d6100c100604ac1d0b0050382c4126580741c10300d03000c6107160340758891641c003d80388501c0551009150600540c025480900c004065589a20740c041980d5018009000380c1d20003a207866401411516005086102c0ca41c0280c4c07090010b2010702000c00c050740c0c80180120710178203120348403c4084c10140459401c89200418480c04c00aa2000700001103406070b000b9605c1e502c0c0c001818510001c21501d64000340500b90000f40f03032000080d80c10f00799440100c50705004000c0186014032803052151018030307891043c0d022552420340c28031200e01485080ea0b001c4000c0d4420003140208605c001d491711010b01c1a141010b0b11403041960140442c3e04494041c3d6005091950340c198501d400340d112131f40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 399717787 1250 399716537 399716539
    0x109080c0a03080c1912140c0406030c050f0d090f060e03130503010b030615010c02040216030206060d05210c061801060510080414030c060a050a0612020f040906021306050405 77
    0x125400308480a40344c809070390790601341c03160b00241503540340005c44280304515440004c0e00d48815058415034248400d0500540b42d0541050b52141051405016101500451810883d00300403050344038210f0303020b031070081500c42c07400304a552107401c08100903c05501c2c0500164905074011003049400002030003010340090a01d81c240d030b940c40400d4200c45c110b01a0b550140c020360009200310410041e445401c2005050100e0320941ca6004201203030401c0340340e4121a00358a803100e042c15010801140e00000458270049080f43c1c9503185603c0703200d900e41000b8800210311034114425a0001130321044445a81184c10300e190400c6001042070a0004034102075281440100d01410020110164a6071513111003c1e69100c940c0e80900038200c04150344050301040c0b054400c6c40c030301440540c1c005c55030f1440100301c90411451040458055038480348200fa803016a040c0140c84111701840e507490221800120000b1508126020784961446500684030b44040480d006400c070010b4819544 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 399719037 1250 399717787 399717797
    0x30105040c0c03050a030e19110906040e030406050d1805010b1f021203100305070305071a04030308010303210e0f0105010f0501050720090c04031a06210109080c0a03 73
    0x2a40100c01d42e400d18405078090f000841c2002020704c0e10f402900003800c02c0f90710780e04a03951040ca07034011210401000c441150380b006c2c200c001c4140381c90041c00603500403c1c1110100440f089a1040c156640b0407442560180079000c20b4100c00d8840d0355100740040c000500407024411041d10f41580204000e612075031191814000602080446800c25031000c070032a00145644d001c8010000300542004003012003000901b00c010002031410f01c5000011841600103119842c01c0045c40d007486000e80342c00b42c1030500b0520041010a41c0510031604494040c149030446090f8580e4400d040300188000803400c1e402e048420300002e10014810f1590000e44000300150390f25602032424901040c0301e1a40090303002c0c4440408200c83c190314030707502c006c900c0216a440070b041c404110314040860b00c511503408042801c0041c000e40f146001d8141d6405070018060f86824800102d420344180d2202034151540500c410100c2c0d400d41c002d404847c4c0041110b521244070340011507581d0041c141c1100090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 399720287 1250 399719037 399719051
    0x70f02120a020105030720011a0a150c02010804060e06010e090f0712140a060c030c030e0102070201120506040906020c240403080402060f04260d1704021314090303010504 75
    0x1801050890074240e05945140c516280e19400301c60390052911200700b5210340d040c1c94013082009100c1d651400d9640c00204810007100010082c0528945c1c1c00051548210302004090300e47c403524030201079a090074007100907119403d1400c001c11040301040d0980c41603e001040500c80460502c2c400c1011200310341401340400c0380e154907441e05100e0344c03171802800d90300440010401c0c44032042085544c411101010900c1c1c80301c074161485240b0f1080402da41307030741040c800d680c140618001c000e03d610080d80352180c558002000c0c10241c23150700e4030f12692000070030040d40c2d450300481c56041d04980c040d03450b8501c003801d094a645500505402016100000d03018164008141520543d09034a8041c560354031502449001d5208035a40b00000504000c089002c4440e402d507451f00d040b6440454031705240c0c051900740b60006041c505000e02c040300c0c100350001400080420350099059940031802c0d480310080c031020700304450b4260714011007902000b141b0319000001e141255402c6a05000382 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 399721537 1250 399720287 399720319
    0x302060c1b0f07030c06030218040c05160b071206060215040302010b0303072a0e010b090a09060b0d0f06080304061d090408071104110f130513020408060a0509151b070f02 75
    0x20700c500420040d00460009c0c1c551120718043c0d00010a20020b4241189440d11a50b604030711017042300e4040350504440707010b20060340e034808419024644600d400304900d03410f01002a46e5501c50071200062400e4180001d420036100b0340003807296110103411a62104101d20300003602d8150319841005260000c9403507a80040380c0000c560460300031001d03c1c00c007642800d80d0012541c0c4101c0d03900d500302c0000040042c8400741d030301c10040100030740448980c50310315450868055483d80350031000100e007807240601440c00c02000703e4085070003174103020050140d03011448030030100d262070301c40e032080a0070300b0031091003004002410914416544400d00307a01107010001103898210002800032400d00c41080c40048040c01051004403640608160325542c0c03001601083c2c91480c0258559008076041164800421000b60088a003d6040c0090b180080c041350751031000e4603110700245e12640c003203940b840d038443d29001140c1c81d10800587c0c0c2c2d4054103090140c100a03180483c041c503440700010040e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 399722787 1250 399721537 399721541
    0x313080708060105150712210c12091a040f08070305030402030609010e0d0e0d050609060105012a0303090206120916060e0321040e2d1b0d0605130e0d09030302060c1b0f07030c0603 79
    0xe41d800081085c0750240c44800743312005004104441ca216507000460102d4100000b414000c0c0c4240d94003a5240790920516082c010003601855581c3c0c1082d202e085881d4010812122049041c5403000801c042030002440f01c9102c01006400d0340207510a2000c003901c0851030030306031102a2582d12407585100d5122040c0040b0240320310340c0340a100b2204000911a801034030459000414550501e0801501c1c031010500588408102d030f4482c124074403d10404081e9000249502c3c1440f00b4030b883c0003004241c0700d10f40383c555a09143d045602450a010909054401031f00846524000a1400c011100c02d0442021154523000600c80a840c01601c8104841032082c40ba10a5000c60303444450603026141d04000391b800340c1a52500e60108040d01d8880759903020340360b1000003060f44555148090304088071301c0c0b84d001c200324400b070040c00480d40024410785c1100146100f25603136100e8400300290b2220420b141d009900a11080c40601c42c40054007500b5680914a081043d956901007501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 399724037 1250 399722787 399722801
    0x90209090f0c0619120204030210080106090b070b04020603060604150507060617030d0c02030c0a06020301140603160c030e060a020d080a1a01030e0313080708060105150712210c12 79
    0x403d541d8040901c204c50784108960900140002d4000d0304081d103a41c0000c00c0b801c0448200c000003010319004020090307109400f58003c0982c0040d036440d04565880d5002030310002040070b4010342c00000481c009480300c0c42124018604c4a0769503181550060004141d075100c4082641c1d101c0c14646c010408210b108003201940304054021441d02400c4003c203006080c01401d100c0c06d502003408803400920080c490040c1d4644952001032392981031400d0740c00701101e0314460310700403407041c0200241d4a00c48401d038241c078034050030030448105403403400701c8100345480311060300a5008503204900316000107103e29a5072042e102c59015540d0340405608468040314040030700c0d03070b00c04660903055010f5480740c00e1003940704098910b0410906464074203407038180c1c4140f071564000b40d010044140c080c88043e0151008841812a008030b0084044040c0a007c0c00604820220383d001c06c0707202d00030040031028000a021140320f0805510140000300084200340001c40c1c0c03200340e030f181d0700e0060b4800c0c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 399725287 1250 399724037 399724057
    0xd080408060a0f1a130f060f210201080f130206041401110f0c0105310e01060f0806060a170a0608150907031b03140607120207120e04090209090f0c06 66
    0x5030710072160008028410289414555280c0c6d9603580440c90100140581c4019001c041e480d0000c451500000c140c0040c8107211402c814003194210a0041c1e81c000605900702021484014064a071082102040e21410390000c0d031060700004c0020390517230801122021841c00740c0320b000300c0340c03481c200c140d0b1a81898000e40071160081450f00d5815800703040600001d0f41030b02d410340e4001304611800040f05603814400c031800380d144c400401c44503800c40311a901414541c501401c0d0784c031000c4405024200003801e4a07101d4540818120b400d9441440528002c40f030116a076000c03801c101d012240200302501640109006508180c1e000d2190000d4442c0281344140007400308034039603200d00c00482c11721040b2101405038038030700002045000c4190f007400080745000e44402d051170039014001828208522180600601c1041c0100700d005400304ea00c1901410000c030a8010080060020600040f0003035105014038148462444001032040005144808541c001c022010401c11a8010b5010072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 399726537 1250 399725287 399725321
    0x90f0411010f0e0405040f050d090609060c0f02040216050d0207050f040b01030e06010b0310051e041e0e01020309060705090a150903060903050a0f0e010219020d080408060a0f 77
    0xd5042035100d098105450b441030301c0c1030b5020290150016040e01d0301503d0a440401003100c40354107000090000f50070303440860402c100510315180002e41825018802c0360144290040c5250500203400004402c10b43d00030001c42d03070ba81085c2070348a00940c1d24030301a9010b00c188150001c0f194000549402030307640040c54080005e2000c82080040d2080183d91030402d81c51b00c800a981210070030036180a01000f080194407031a08800c0131585041c140c2c0911701c03038100c080185660010400b4070550603a4280c4000c42c01e030075000c0c0d848100c0e080ca4a050309801d843c2c91108200340c14103501550041580b03000766449034076501411603003030240240142c0c0c0b0503034810303080102180a0020f10b000032803074145540b19139505d482d903004580c080d00e42a00407807000a400ca0801d980812440c03c00880c50410892510801000171342d06d0f4088148054284030040d400015540c0b81841e00c002c466211000941d1283c45984c81034a400041e96111001e9080100d14800034026000e00070040c00440a5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 399727787 1250 399726537 399726563
    0x20c03010515040504021c030f0e0118030f060e0609010603060b0603040c05061305150a1803080a0e010504080706020f1915050a090f050d02070806040b0c030402030f0706020606090f04 81
    0x80200501340a48100e0b8007000406450540030300c02c143c007400c103d001e506c81c000d4108880b400903101000740c00f40c0c2410820380140c0300455503007603668001520382200c1d55050b0000c00345080340c0180410030145002d44204003c02188800542192050b207200f00170900280c0c00460500c2094003003500e0007448152803101c240a00d0070400040c01c03504a0140c92800841c0c0d0ba100031802c020400907155155040004410810365000300d0a81010400f1441c0040c40034910307112001c641c02126140c0381007141d0401e056410ba88a1429500505040e10a4501d12035640c20007a6656580c1c20f541000c43c0a000480400c42040782c0b0b071306170219000004444a40c101c410264000c100c002d00511840c0d6540c0d0800c00825203030300300741c03c0c43d0384180000c2400811500c000307443e04100b540050078541c00f034010480003856144285410902e800d01d0700343c403038460f4400203040c1401800c01d10031030302c10b0030383c0052210b5001400501500050b10b80303c1c0c0c60389030803a411003200c0b41218003030040646114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 399729037 1250 399727787 399727789
    0x91006020f21130b040e0a0b0f090a150806090102130501110c010302070c12050619090201020c040e07050904060b0f0409020102031c0b100804061401032a09021603020c03010515 78
    0x4000d2143c94a400c0d031000c182e503180c1a1092035600075800c071a1001c94103070100240c15145104007a12031404858091700f248100d00043c81842006042c1003445132101258502003048030112070180c0084401d4410f146040510b450017504441c01202031001045400a4154080c2606009801c0d0810141c80d40c0b1224200540c082d41c0181d008454030345140c100015002118055181201d00c140d000e80f8180c2003050421400740580002182d02c40d2034114103400503a00015458281c0200340d4020882a00405109080c40102e0f030185401940d400708000070041182d000b540d030120106c864004452441c000e0100301d074084070009015900400c0303960107078410034120520200c6168070101780038164001081c6550100d29640c40480c4100050200b01320540c050320300a00402480460303d507145448072900480d1000c8011034085182d1036000580040302c0009010380000780742556501d04c01d9601b0310707082c090040300307030014051114406010310307060040c1402400800303032605200010b80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 399730287 1250 399729037 399729103
    0x5010509011512170405130e010e030a0c020d050703020d05060115020607080708090c12010b0405010506120612010e070f03031e09090f18050313090605010c03110a02091006020f 78
    0x4c40c2e14a070205080c40001802e55a90500c1126001d1300319010034203200544602e03007519400c41024555400c14001502019070051a500384142c045812506150003030811301e040049036080690402c02940349030b0240000050700d02e04aa0804010304500f074000b001c100d8039100301352900000910f04a011500c0d0601c241401908480d0441c150350409841c4800250040859000e07045d15946800307000340145428452180180415a00c139031801d1507810248581c11401054940308049400b07070050030210035030016484c088000111100f007512071410071200a0184030403400034084151075030001e507180040c204203400503118007485505100761000034006154100300450f940750a441d21032304d610301c11803d40c180208003031a6120803030b1046820255503074206400e0541420010401e99070b101c0ca66105081d0103142070002002c00d4080d81e8140b0b45d1711003010398803d80d118244655590b01000e46002c80302180c00b120201041058410f0320391895840040d84d43e640030078959000f840c51 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 399731537 1250 399730287 399730313
    0x717060c090303160302010e0f1c02060103050304090e070e1003300e0303070c140109080a11010c080d1e050601020a050a02150c03030a061a09031e0c0303040305010509011512 77
    0x5c0e0002003441da00c0c40c40036516000310408a0540da50001c00748600b403a5510305030045011052010340a41d41c1103860701e555a1049224a440715540e0b043c4a200d440d405212907005041d92909204c1d440c01c24580d1a180041e00c0c0c0030980d8940c408015842e84004404540100a806100c2c5001c032600304d08010740319241d18001c40da42500003048008001207201407440050052265140d154901d1207000416000307079604094502e40c0700030f203904c002c43c4000c2da40b10b111075424680980200c1c21032a00d60000d024a0044a1102e410490b64586c040c40d11a1000d00700c00180358100600da4401004a907030720f0342d4160140298000c121a01c0c00350900c0c02081ca2016007000030985498010412580303158000c4402201041d5500c2e002d0100c540300d0424840c040d02910000780c1410901d0b800207840e0500148103074a1810200b6514820308404e0182d9031008900406aa8903141d8904187d4084d0a08940c40c501d99464032104a107000c0f0140e01400c1500c020514036000390140f55582a140e806e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 399732787 1250 399731537 399731543
    0x702090f040b150135070807020307200d05062a090402092107062304090c020709110901080f04030c0b0702010204030204150302120c06180d050717060c09030316 71
    0x1240f010f0440944105d446003841410030f0046100c0c01c982c410440c140048003600900401c5601c4090044966001058584003504514115101c44010b40c680d144481c500078041d40190881300d00500307010010840e030348101107400c0c540d405856075aa15031a045c03101c0b00d4980394940709120309080d07820b00e64050309c2c1400c2d02801045107040c003823508048a4603601240701e120b1340001c1052084907441040103855075003e0741e00c00e14841600840ea442c1b8040c41c0107a030030740f039515a010b0300c0141c030801c9080000d24010004028002c1a0102d42905602405c0f145010031944004a2443d801c0c4070310380307849131790580c0d1501c6591404e991540681c0700302400300400c540d000d10010025035107a02c01c040d0032001a0165034485451441445142c183c19526620703550070240505103d62120005c59144076180b141445020700300400148040c0da2490000d805486484004128402414264418807690001300c85003503891808403545403145452098040d0800e0105910078100d0030700c80071074544 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 399734037 1250 399732787 399732797
    0x31503030906052110181505010e0d021207061419030228020a060c08040f1103030403080c03030105041b02070513061503090c1a032a0307050702090f040b1501 70
    0x50130400b81c1d800103400ba105101d4060300300c0810020202113068107501d0400e100c005211156444101c940445100d1244c03e040c02034000c5030485d560f441507140120700d540185181c0c2e4014aa5040320b6070381c0301c1030240501195aa46440c91120041c20940342e12910b030b401c800c0c121800c41380044001e9048070f407100c00c1c80045da001d0208044191013502c012442141c0c003c01440c8042e09080040d07c2140c03454400b400400d800307101c00704c1e00d80a013000c00190000c060000e1100c08001003883c51040360310103804800c0c00300711070403143c0000c80210304844003104c05020840c0b80302ca1000c60b0045107401c0c5c071b0240c2d110701c104100b182070052640c2c0c0003035811100015410b9403070900048040c1a102010002030b5904141c4040090f081100c030040d103041d02000681790540c441d02d2035503110144c07500e000c070544800100d8201c01d82000f0307402c0c101400201b5640324104014041e0264002c008124410318220000406003c2c803d040148200d41000c0350300303c15102c240704491100c18013603510381004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 399735287 1250 399734037 399734077
    0x30b0102071a0d0b03030d02030f0109020408060a05040201050d150e01051512100902040803070213020301061b1e05060109050901050c0403121101150806060405090a0210090e04080a03150303090605 87
    0x50390031b0001c2c10032103811903005a6a032a0402d0350301c0003090141c01400120b0705c184018412500000f07040b9070300521481000885e51520300040e6014000c0044510704182828034071580244040c40381340c01c4a280304c11010441e626102088170701910343c40c0e14280c04105000b1100328010034144603401280c018185030040344c070fa9800308240d07400360f000022264000204401181403c0521102072074002c1c508500715418014010705404038000d142020241d20740e0307280248607941e1007800b515081c0d000044080f000503c2c00d140c40342024410403a8080c038000010b110944180520b40c82446851316580c41e146c2595a10390304080008040010080341c0d02d0820b103544002d10032440a4000902d00c2d4240780d2034048050702c0e00b00028680c5010ba802c1505000d6111390025400c9046607049446c14916407468408a40c0d03640d480d4452143d080c2043c0034007003400000300050035022000d0350140b2a90f5100191500f0310421031000900080101f40e0411a09104101514140c1c80743c44205043d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 399736537 1250 399735287 399735289
    0x140102060f0415092d03020c040f061205011d0c0f010804231b010c0209040b04170a08040317040b0105012703050c0f03150a0b1c050d030b0102071a0d0b 67
    0x2145088005c8a11010451420008804410820640540700100e0045240183d40c0c02900d070142000305a0103540c440440c2c40d00700958bd00404058043ca840300c2d070b2443d02c1410014042c10f00a010902c3d848550801c1a0000c403001c180c0f001c820303101030040503100740d04c94011105640d0003481602c401ca0800e202503501c4107880568140110500300904042c01300030f900c0c2228199038400e1a0501120808030320058580d11700d0303554040e42245550906a03602d06105e81c4c6107260008da12203510000410541c0302d90000c4082d40198001d03620752030b010300b42c804a03804591056401401030f503690801081607601c141404480d06041e50071040c000012000c5895420010b5002142c140d00481d02e00c5100d8101615403a0210104070020204104404003200e286807010b00007082c8551164400715080c0c5480c103840300e80c0c20918101168020b41401e00a07200c05900840c80000303030420112007240d600c0041c0800903980d8640c0035540c24840005100503030307844814603641d19515582d580d00c01e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 399737787 1250 399736537 399736541
    0x61503010b12070e1e0918190203150103050313050a1d0604060510120c0516080c190303020d051501022a0904052107120f03111b07140102060f0415 65
    0x410313000c0c400d51075644030321700040104080c3c2c0100600da69804042800002d0200020403040044408801c482e07241d42e00d0001c40d0034941c071000b41a004404503000002040000801000311054a4120041140d02c803010404015124810782d4280c110701b448076582d0f9011041502d030404001480018010398420109190b454040083c0022030070642c400c00540186000d203190801d4280741c00c2d458039403100708040403c8130398040540a00e20215051a01030002c120941790324260a40d86c001016080c640100650312000a001403542020041214054240c1605100d080160007030007a5942ea0302d90010b507828411a440204440301104a0040d119513807001e0056005002074803541daa03404817921680c03c0d00c2540300c0d00290810001c00400d11002000540c04c000e0b01d40080d04c2d03201500120007500d216410001ca81c0700004503a592020740307030555900c02e03000200b0723196074594461403240c200c0c0d41c007054603000d600f00344006491107102491071588544508034042c41c1201442001c41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 399739037 1250 399737787 399737809
    0xd03291210020406180e0c0a0203041e03030f02070e01180609020304030302071b03020d121808010b01021510033807030b030307030c0312020d090803061503010b12070e 74
    0x5582e40094188000c42d0300071501c40c06200c4c02c1200c01d91a51414002044180004041d201301440200d000d10055100303200702c600400d1208590602070100c0450381521801510003100410b100900c0e40c48882d001040100807074600355003d41403a0f29011384c403044134183c0703000c521405a4507130000c11641c0580c405140140c0c0039503001a143c0d506441d0014038409060f120044084400f00100b0042c0d030f800308044090b40c0d000c4401d00d0421200501540c100408820f800c4520181001c0440c1c802e03015405900041001d07400c031a10921020141391080c90265058041820b0312201400811103444181142c2610300c02c1c0e00885409045030300303001c4107506000b500030f000900f0520510b550b050181c0b21280004134065441c100e00b581c0d0103085210020001410310500503400303980300c2080e41c1500d0260b001700605205090061070140000d50040341c00d070b4070403c561040d444009001501b928140d17149024980d161940811000007004002000e0b0820841caa5028254581b6483d280705 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 399740287 1250 399739037 399739063
    0xf070c080c0c09090a0b070e040f0518061506030109020c070e0703020306030d030e0c30100e0601050112090204090c0e0402150a05040905150907110d032912 69
    0xc041d0b454a010050740301d002401e040344c96880441d41c0c41c0031585402a03290080c107541400f0760300c0b86024010a01502a030421103502030b26103010410a0084005007e515110903c242c03141641c03114a01c51000710203809880c1c00c55018030041c403112815500800081c0c80710303421295001e60303402104001840c21516a00029004000c1c00f00c00d050070495038180200b03c1c00c0501100c00b00c0301240d40d480c03c000141c244994196118807611410021881000d0021f407911520070a03000451180e865164020321100c407813600340c140c084224040740b1705059820595424900c10714400081014120454069078840e03502c6c2c40d03501c00034140c612100300900351038481e1152840c05004005032181e40c114541300201080084407680c3d40d00400321001d90b0400600019140c40d80c407015051101c0c1c5030441a0040701c0e040500180310303080002c82460501e424111402c402d0380c540c00720180c641031041d00c0380d00c0740c51001280010481c0341c0c204a20b582c004d405072201c040c030041c240b40380102c5001c0c08 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 399741537 1250 399740287 399740293
    0x50903010207061b090909020d0b0402040b0a06030b180115051c050a0614030705011e0c06020a0306030b010f0e0714090d0b061c0503041202130c0e270f070c080c 71
    0x513446094100d15500c005260b00c01c410003540c01c26070003041015120400007401c1d0a0028001000c658880c4e0000b4902a0013608603680f4030b0f214038001e00209490441248941141001750101c2a514484a41640c0c985041d5052805070000180c07115002010b404190036402000d1801c1120248a510301c41d031480e1401141c46880d00c404110b081020400c0140203030002e02044c400390340c010f008166248042828003003054890783c411100340f0b0380e402c8000c10083c0001564001da50f4160402002c0c6c0307000d8880070700d07036076660702000381d082140f449407032016001c1c0400500700e43e000f480503c01100440c40750a18190380040010005581070000b02d810008000500c481414042c2407800718518074017410003410042d0b214141e40c1e001e03600c62458522107400559003152540d6040420045054600b4880c0f001054000350080d100c40c036040780105040ea8046201e07007031420201a919207584006045510350000d1301d9501c01c0010051404c1c007170030507941800100d8510050403200c5240e409 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 399742787 1250 399741537 399741581
    0x5040f020a0905071d0a08010f0510080607020a11011e03050403020d03090201090e070509092409060f010f090b0703020f0d03110d20070302010c030b0103051605090301020706 77
    0x10020504810b4200282440c03400081010607074010491402c06030038400343e101d9030000400010b44400498002814950034000901c40752441c940000f0b0184501c20712002c070301900e42c0001e41d80d524080b504500164011846513010861f01d50031112080d1040c500f60000d0513610403002700046c40404480c000a0b6601e040009050f4144818111207445240c01d01202a450300000d08580a6018003541c06114002046c0710394000c900700c40c01e18101510365202d41c0380c086000410030748a80360f0150309000340c120480e4185030480c0494801e1500070303c09254046c1c941d0044403605c5010351401c045c0401c6a13404610007401030054440503100742d0060a0342d00071011000e040c1400803010005040c1005041d900038841481600c010303501500c00021402c85290028030040442d03d0909040a00000c60000741a07064200095440342038809010303903840040110112001190041040c040c4000703640030305403050300188107900d0020000340c201089600d03540122000100c52104200d00d801d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 399744037 1250 399742787 399742789
    0x7021f0f08090718330305190314090f0301020d0204030215030412110102221e030206030105100309080a0c0201020d02060108030f03060d05011a1e13090c0905040f02 73
    0x85610740c004941400340859030f02c0c0c600004820401004498801d9403291542c0e0385c89085041c0d40590410300c14409a00400c3c0000119030b0b00d0b040340800c0d21940035405204100106ca00c042c0d5540390740c50355034030301c61100d2607002003241e400811300d09501c040050ba8505d0316507424006400031030903241006960fa8610301c104030140c40248000390403454103001f040045006003901d00d101c041c0d24142082c140d100382300701600910034216000d140e110b0a0741d40410501407a0500d0080d9050381581100e0074210349101000d151040c8002980403008000611003400c1c46044640e6000c0b040c10080380010301961600c2d49a009240034100145264000e00b00395a81046600100e42d2580050803c65042840c040e07128896000018420071000020400544410005144064120000301700d080360882c4140125214513000e1845405c07100d90381c41c00043c00e1600c1c41041c3c04000d102c451541d1082c0144030203003ca401081d5601e046481c000640d28103c1e0103014822031082c26101000f0413a44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 399745287 1250 399744037 399744047
    0x91903060e01060819060c2a0b06060c120906040b0304050105060901150801090c050c010f06080c150301030209040c08120307020d031a091f080106080c0102010b011407021f0f 77
    0x684a42001da00001c0085c820320b00c902c414a40d41d076000391010030700304400c0c44141e8980e0410012440f62040b8120a00e1803460588107188929204104c804019120101040a14042c43c9804034060b080fa00942004e21200e0006106c0c4620141205082a589440034449030700115415075050351150308005103458401c12480c003400d00e00304030b0b41c14004078843c0149448070501a00c914540c0d07501454605a01440c16a031980e83c1250007800340c1114083c07903001800e140c0c0f060140302d11802c00001e220386480003450700d484495030340449c19680317180c00f0410341120161003038030f111850800110303141105000001e140c0240102280d40c0341030200c0024601000c00e10601d0800d481c1ca00018801c004c5070304c02c100f207170408030740c2c038213240e12403c1565929025000a00d654001800c0d000912182c040d08000c085880c140142e5018409000040e42620b14003064640080d842c02160030781164030768003400326540040e20440540e0010302600da0301d00705085016001c20101d04070412a65801 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 399746537 1250 399745287 399745289
    0x4061e09020a1203050d050901090807030c0b0f070f050d0917030f01050a14011d10020703170a020c01110106030b0709032a061110050421050405030a0602091903060e0106 75
    0x2c115085090801341c4009100d4001e255180c0c0c1d8141e29a40800c2d819082504030030902500091003d5980c10300b4030b8094408054002700310354203c116000100e401c140d1104051103000991604d0078549048901141c4590000304101c1c03480c0d9032580b038007000c40da0035003c0325181c04418520030780e20f042000c00c0c4641e00380c2c141e00c01c40c0724103248003040c080000019400883d8000a0810300f640c1d40726410074402961032100520f130404100002c0103980707540002d5800c100d03030280401040740c1c0c0702c80340da000b0103118145040003d0b900245003442c2c0c2d5403142e014094000010000060410703240e0340d4020b5007000945a080008840036000e005009054501443c1c003804400e07512039100f00c51141c507109500c14403480c07042c0403154004201e050310078000c1104a642c1903404111914041c82e18400740307501c40c0048440011040803c2c81e045001e0000c50301641c20060042480f50025036544010350701080c0407940050f0b0a40c2c0641000c0340490101e0040c41c883e0a002c01d405c43c2c001c482908454a03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 399747787 1250 399746537 399746549
    0x4180207080702060705191209050d020303030417070b0405010510061803020103051f0308030a0b0d0c050d06060b0c0705010230091809011a0103111204061e09020a 72
    0x81080840002a444002c45001c039030f055440719110105070820b54141010864813008070320106480100308804004115180e450035150244015141c0040c400b41c00022302d80203405500400c0441c000c10403040280064248802042e8540020381e52501d4542d0000e6508442a0b91a0802d0100d070346540d08a00d40a0041340c5004080940812001501c00c01d16102c00b0b4103040e502c8000c190710320b040b51400004400328003892101c141c1e0307914080300315034000c81d415082e0720f1805040504618000c0102c580003600441042c0071a42003000b00031800c2000130049070015580c02c00011503405032800740848041c240042d01e01545814000785c20400190015100042000401024a0810400240d2100c00c55500c503844414000c08036400300800c3e408000040301c15820001e6090054019000740720305004044c05485e035000065042d26072148084c030072044140803614291080405581d03000780100c40c0440d10300495860211140300c0c1e0010103c801d5212484c0001f5420078445003001000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 399749037 1250 399747787 399747791
    0x705190302060612030703031d070602060603070911030721060608060906011115040c0515070303150510031a120f06100e13050a02041d01051b0901050a020712030201020418 76
    0xb407070130100d5160b00c01c14500806042c0e80307107010f0002d190808684c50380441c00408881081d0b40310040a0f659280494049109100d80c481c080b0b4003404500400341500c0f850141c09055445442059484d03049102c25a204002c000c2100903101c9482c0c001d1400400745074440e882c030b605056050003090749006004a0500000d10900d04018000041200400e0810060078100742c81d20300d81a06090740c0c0e81e0107d40c0c40323490140f08200000b04e1900030540184603803801c1025103110184010510706d1480360503402000210110880c0c0c0c0a0780100b202c0044880710910745524040009001000d4420b100e6010360002a94080814041004980004443c41083c80043c54078103041c0780008010021704881e0a004508000c1010030008044004d900920500c101043c0300301240c032900960440104039070908012900340c21113010142c0c00241d50458242c07a26201f2401964254440c0b02d5641c1148102d0320000b8240244144403517005101e91300141c3da4a02d840e0103580010000c00840c04258 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 399750287 1250 399749037 399749059
    0x22090c1b050606040b0105040f1502070f050108060907030b0d050607170603060403110a1e121b0611040801110d0507090b09041a12010e01240504050c07051903020606 73
    0x400000300b00e0b0780110110307000b003a02c1c085480121810b0207542c2c00040f101e4085400880c110242d00c4004c4031141c40e035402c98102650b124582202ca0711684181408100c3d960003196003401c00d07213113495015802e8200030403031400d030030081503151a0450003555150017920a121000b0360194104194400400c0c0e248460f050020001e0745410b40540010140544081d02d0060392509100b510b04568118005441c030040708600e0104852003644116042805000210b840c50300415404006403810300c0d4146882d0a01c1d9200310003440c5400d107842d030101d424440001c55110900031a48500800c1181a4031200701320b000000303980d4007810190078001c00010034014a20400b00b030381d0321444122004a404a40c1000840240030009070650f081004241c40d40d4500c0c405410066120704440b000b000314003007540f1030016290b81c00d40541143c18032542c0030486850190459900460f4501c16546052000d5880525141001484c1400c5c00c444180c000305040d01440069440300c0b00755001e401c94 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 399751537 1250 399750287 399750293
    0x60720060705030421020d03091a1903050c0f0d0f0b0f0306041e21021606020a020d05160e09070605040e060607060b060310090f06150522090c1b 64
    0x28056402008455003040311140300c0d119a0b00c17100407405401804034004501c1d5410000c003103070b2281c0500078840241c403005a4604860204960000301d2243c220f074960a00d40b04201c1c00390078094040d0006500074031904c46200410b00092001803400007002400c4226070302400c0c152442e800d40d07184540300c510140311158402150301503200364407100c0b542d65110751501c0040c041e50120000b07040c50021603900e081481d8880c104190b0000e20b41c0031104103224124180c3c6440503e40541c0c0016044a003001d001404c00c01e000001a610500c280c40d44410140002e05100000744d010548045010040c0800c000003809450042c0040e0f1920710f1030181407801d480c2d00b109001d400e84c6d020344000141c6209102191b0311000c4545c600400ca15500c2c00c004103c0000d06406004512031070303140c980a0400c0031141e200d6a02220740c1d80702818104c10040e13000340e40c1070b00040c004295008502c40341c0d0f1041034401000001521090700b0004811904d00002825040d6030300c08507540305540381c503504c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 399752787 1250 399751537 399751543
    0x50a0b0d03051e0a0507050c0301051b0a05070503030f1008030c070303110f0105010b090102010c0309020f04022109030a03050601020a0f170702060309030304020108090706090b0306040b060720060705 88
    0x40c890301400c00c1a034858a005a5810104041592102c112408980100382c241d11a0007003942c01d000c0c4d02244d0a10544030201401c0390005d544140010903a6200101000080c2010706a002c4417403e120781403441796203940303003558011038041c0c4144000004026074801200792000160400382d005505107403070f540c0c00c0380da22001c3d400f016090080300382d0604102d0000704100c07588400d04800038001541c0d61b581c00507140d000400418099400c1800f420440c500c00d1007110381194005004642d034220203003d02c00298010200443c84000000101c45d0700250401880d000301440b0000b9540d901540c040241181d0000e003d090442d000704403218041555106030489090304501041045032001c1c2d801c8a8030b204015009402c150044204100e1280c0400510302c00d80c002e80714056181e072303200c14903525036580b4000d0f8804030351041014042c42c2c0080c000342d9808080a0b000041404403500010b03015080600100c0e500304034a03003000e5802d80d05a0140c500c80405864030340c2001995030355161 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 399754037 1250 399752787 399752809
    0x31e0d0207291b010e0c040b180a020702010e150d0c211d07060503041511030c070f080f030a06060e01090329010b18010f05041502070b0c0f01050a0b 66
    0x2c4040040340e840044120582080d45282010000f006000c1090390981c1d181c60508104030b02c564900442541a41000a036490300440400185021603440000050003504403800980c1041040103111886440d5500d090b038804107200006e50710384000600600a0790326528202c810402c0d40d1300800004401c08a590700800c0d4104408920a100e079680179070400c0d58014401c0d0700d8821040c000600d203801c0402140200c0c00b42120240b00c1c21007402000585405080124201c0700800003e480100302e50080c00c00030b0b220724924003980c102c5880e489216000384880fa01801800001d0050f0388945100302c3c3d00a060b10300300090007405134400039003400380d40d20014000443d0004c40541b070411480c81ca803000170300b244440742a56144c100c072000035003003130f9240940103107070307003c2e1031160360042d650440c0c481c5580e9117842c5001d050059001c0c0b0342d509840079105502c1204000304406d43d501d005404180103102c020010003019034002c5083d2400035100e41051854241464059110b1007800d81c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 399755287 1250 399754037 399754109
    0x110a060f111f060815090a0318080601062c10050d020d0f0b2706060f070506090115050d21021006031a0601080609010e06031e0d0207 59
    0x28403a0782001042c00e2080c001d200c1036030b1100e2196200c8907400c0e903502c200151001031040701c0c002111000d1400c0e500000359882440c0303a104d44640307400a880382200c01120820f14014641d1180d603088541d140c46da080c3c00000c08600308882c441c00d8061101c6002e40070203140100a545010030030041f4500342c04640e003e0080040c0081d42c4142d43c01941c04507150380c407040e201013010f400b0340c81002d001801f012203018860610010304040000b000c50505c4000a001d400c592010349448042228550003141c1070803003500140502c034040f0300c1c24090305200e4580400003003030503855290f1080070449550045482a6007038006c10001c40c1000ca0b83c0d181403010b1030080345c1280070740b41003645443e21403940c440440c2c0c101003001c070402c030002c000007074a410040350024071600c6200040d55109011540386402c0002c40004000f03c42c0d01d08100c0b034103c10042d068450310342c414005614880b002107100e00c0103510050450703203503660400c00b10005022401c00c0e400d215260b050000740c0c1403c2c4507548 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 399756537 1250 399755287 399755297
    0x8150906040f141003050d020303090303060d020103111803120a14030a0e0604050a03020607050f090f01050d060311090c03090d26180105010b16030804060e0604050a110a060f 77
    0xd039050307041d82c1c058046540010b0111605180c086502048601e1310f0000b04c50758040ca0300c003103803081c1c0001f0950f4001d81c0b0400203076046a41d50b6050100e2030602801c16810107481c0c041d03200c880d40401c4010501070311207200c1448003008a01c11b040c07400741c21004058012000b01710b001d80090740080c1440c22000700c02220713696900d500d0440780140c036440c5800456400f400040c0020040001003040c44a03210f80c00b960780036902e04606032400e00504480d442c2d550010059034140e0301e0900082e0001c1c0d881410014184007130400c0c0d0400b2551550011140c2c02c0800d0401956840d09064290740710f4005181c0510b103261081c042511400c10000c507c041c40819064041c0c0d200f01030850428510f0740304201c00301c0f8500000307080308940c2c4100300c840d05541303403c0004c1340d842c0c0b035a403c850400401010300550b07004945e80c1151200d070024000d60391690b58841000c51b600c400e02034180100c1c020070003896140c4242c100300d800501c0e40c036a00b0303200d180031800400120390041a2080000308500340 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 399757787 1250 399756537 399756551
    0x1050d020405040609022101150e1f080303070f02060c0a1707090902070809010f0e090c0f090d03050306011205011d0c070506090105070e06070c1214010f050103030815090604 77
    0x10020261000c45c030000e41c4143c0740102150340011200e41c80c803040f5003080c003c0c0010058500c52440b01e42044c0610f581d0b10320380000042c0d14585e1542c01d0500d50038110b0b5003200c0b466842030302c9415600251035200001e503120003800303400380d41003101a4102050070a07641c41d1042e06900030303005000d200e040514060a610009886034000c001c0c001c010040c1c500155542ca180741f40c01c01040c0c1c0b24804080c0072030f0030082440c50380f80c85204c245a840700081d010640c1c0b503c5e0401d0030314541d0000341c094120401c04019503e030540f18400001c4205129443c3d054503801c00000241c056a070445560401901c1e02004002e4041000d20100200f0200b960340513032616040d6842030244901200070344140f054100b440500441540014400c00490395040e480e0101a41005414402c040004d006517200010a11000c0d180c8100114014440c8001562318138200090b00c0c2590310b00c1006500060342c40004106041d000060183e0024003445840c0c0620404000a00040c0001d010180101c2ea07400c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 399759037 1250 399757787 399757793
    0x7050f010c080f03010b030121150506150c010509071a04060e0d240e0109030207051c02090a0f0507030908120709080312180a0b0103080702040207080a0806100801050d02040504 78
    0x8102c890318081a038183d5560343e1191408081e0351b0081c441c0d4040a00507080801260401c40c40f04078501d5800b4030034405103140c204580e400742c42c0140c40030358400302110381d410f01d051084008048210440b03001144c130b841c080240c103080511992001c2d8614142d520a1210701101e44201c0d810349116081c00300113034a10001041106030034078401000c00c0f00c0c620321207080000c044816108003080c140c1c24000100303220101c2e0700340c1e0203a20004001d82d0280d002070009140007904905824200b038280e01808026400007520350070300750342c020201661982c034a060400d40c1d0050560045c940c1c00c0a01c04005a42d44541e80c2d031090901c03514009041901017980f040c0300c1c6100c00020006801181e445406001d0324004440085c0d035501c40064106080c0c0302031990114942c00c0007900105281b035168039580701c00b243c0c2e5000c5201240c3c403a038200110400100540f0141812514aaa0342c8107249408000c1c05044003189201c2c40500407000c0041025960329101f4190b03095040d00c0125180e200e6103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 399760287 1250 399759037 399759053
    0x6011802120c0d06050a0b16080705010c0c060c08040803010b0c0c12030c061803040320090a060518040b06040c17010e0f0a05150904080c0f070f0807050f010c 70
    0x1c8401440d800005060007000809a00580b0420010322401c0002035503810170020750804610848062070001d201c8042c07031044902d0402c18040c000c0c0802850b0255a1356a0380c01c5409003510381c404251100c50070410f21aa600c641401c520013424000003904003501d030580d49010512440e0000000010b10174600b010a0003021190440a420810542000341c50706403030b5040700032000160300c100400140a002c103690450360001c101d201540c5041d00f540c4441d0f4116001140c0c803c8244c9140d41c40200c1d40d00c60558152051400702c00000c0c0340d42c11b040801c800704039600c0d50140d01004031024000415052000141c10420403500003541b06100c105c256030407080340f8032025400302c0300000001c1d003030f05a0340c090341310318010050121590340303020040b400c6a00036111052038007441e80d03100b04142000c030f400390381044c060404181400711160300d56103070420b11203d482c580d4000f20410440089201090009850100c024050380f40c00d12000c03c0070001201180d904101e41c0f41c0c0d5460910070070b8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 399761537 1250 399760287 399760297
    0x30c0d091202071509180504051f02040501260f06121209120f07030809011b0c050316211403030f01031208090d030902060918060a0e06010206011802 66
    0x840c0140c00903040740103515005540705032200c1080c456400211207100d6000b05050303441403042d41d10402d48081c0b105005050080c004c80340c5200e01c90b010f001090380201c600701c04406080380541e07030b01e00700310004040d2a9060141070103000a1540c60144d00032240d07040e41d00c10761070300214619960342400510440040d00c00203405004034114000c5005052004014840066800b06107141082946c69130f07440300d0820a50aa800100302440003554100c0181402e090500d4521807482040585860080100c41e044400c508450310401640c1814040d07100700b01c4041140c90f090500d44209241d22020800c0e4420218110840001c01c125080c10600c500c000040f017102d8807840c00f0400c2c0c0d11000d5080c040ed8403c01c5000604003251881040d42501c1000b140002e0001156145015000707001c806104a071700c11020301400f00c0c1d40d29000c224100701d0314910681140b9050440038840500141e821080e010300201080010300d0360001482811207005031000b821104065010358024091 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 399762787 1250 399761537 399761543
    0x1002030d23010b1306080c3f01050a050405060303130e150303040612020711040507030c0e060406080705031509040b01030203010e151602071809050d08040305030c0d09 74
    0x1d8210422808804441c03079000c0c0c0480ea008108150741c9440c00b0f8049030003210b5070002040c11042061200c030344100c458603046007819111905125210b420500d88072000c3e81c0c0c20899558140040f0170544100c40403103102407140082007801d5060901040807138115000f560f0080ba103d0021903440e450804c100c8005020240182c071825031650050b12200c035080d100c110043c407034605201e14900d004000c48007100c0480e241c1001e210603c003890400303074000040507506600600e11041c003c2d10f8900850740300d9140383e90002560034090a01800d1201005880381c0241414401800443c0d001140a600302c4501c3c20029120f0740c8019454151450300e6064580000601d014481000b01881c80700707043e01d1084009000c1d0315444440c4039a642d0b413100d405180620204045007646018038925001d0103031a01c10381e007009864080c24019407420149040c00389a8541601c802d1100501014482d28601d140c001000d05094600030024080a80401c034400c1c40020044989039a9501c0080e0300e581c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 399764037 1250 399762787 399762791
    0x140603070c060b180a29040e070909081903020336152d010905060a1a190201150315020c03030c09010f020304060c080313050d020a0c06030902090a1d19030905090c091002030d 77
    0x2603407503340015003000c100c0080f00d5580809030007509019000341c9110750050201c541c0301c44500b4010303250426540c0820255444000822161140144001c3c11640301615145400c0d003400407a26010100c00c4640501d03120081e003442100303410303464140e8115502c40c1404540c4e616201c00007140b6071015030100740c924a41d002001c10300710002c0d001c1d2611488101c04070071206410703641a4265005c044151928100c00e01080c80007664482c0800540b80e075401d401810b20340803c1d0a42d14503803094940141001000c00d40b04455a404511101c031026540301841c1003610780580603040190401c0001c1c039014002c000124210000c0c0d130051407094004c2d04448030300b054070f500a034895000b00e03070544401d641030b2008121207010f40111010664041d20b00302d803d6851004800090501c404004104c0501081d02d500321403041100c0340b0003500e1000101003120a070b01d0007070448000740e44070307501540c41002003168000b054002d4900103141a50b4074140300110900032400d62280e10880040b080c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 399765287 1250 399764037 399764051
    0x10c030903060c260609060f030a12021204060c110105070818010e090103150515010207031506080f0d030c03270606230307140603070c060b180a29040e0709 69
    0x16102d911005d001e60b2058030b50300c07105d03150340060101d0182c0303050840350164070142c56540000c1a605a003000301070184181e8074070f40f501814242540c1e00640c0b20000140c04225608107000400d174210140700f80c2407c229242c0b000d2030392980c1c6980a9000c018030100055030340803001c0d9001c0c643e244e0303a007a00101034503115a128607000c0e56203080f40e9400c2000d24a00000200c804113913030501500000160020042d1914541d034401c14a061303202101590b40c0c6840001400300c500700691115000c01c1c1018150142000034000d00f01c0343c01c5100d0341d08250501c0c080b100301b0130b5200385043c1e10200c1880248030031120340c14a58060718050380321103005115400380c040950031014014031024000c5064030300c0e42d07540c1d045080c141955030b00482c0d880281000401c1c6041c1c010303460b01407a94410310000c60000d0103a80011243c540a09407080400c0c20700342001008411841892000050107080c00d0030781200d00011403541414440301e40c0039a40d01c94111440c41e104105000041505075000e108032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 399766537 1250 399765287 399765347
    0x403020306011706070e2809020a03140907030c03030503370b03030304020603060d0c030609030513050102011406060307110115030501140f0c0913050f07020c010c030903060c 77
    0x1e080030320401d003070f075010700000300700c0052003800002e5241d14020141074428250880c2e203000d00f040d0164101c603500b0100fa00003180c800350700140107800c0032031310001811000080314400ca0b4000501800a54005103002d1000810340340c0b00d4001e80c0d40518105480c0d98400103c072085042850001880400c2d000c0a00c9515452519000415441c00d00600102d06004149580e03400300703840c005e40c84007040c0005142801c103041041801030007050301850003039481c4c454000b02c584039482034001031000140b100e0603400c0103a0b908004c000030304c0200002c0800000440801c0405000320388141c50000101d0075082c0f04003603c200d0302318200005c000907948005483c80034001e40c8001c541d00d5090039001c600310317122400d41612500b4080c650000c2642e60700c8502c03103143e120844c600d90000030800003402140d140c0c850b0700e00c81d0807492542c4d0070604010401a242c5890b01841a04201032402d4000011f580003204008803540f240c0f0108074010103000c00c5e250249805001d074075a440c011214442 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 399767787 1250 399766537 399766559
    0x2a0320060105010f23070609020a0f0905010e06030a0204091b06090e0709060c030f0c0f0b04050c060c0d0302070f081c0b09010501050f0c0c130606090e04030e01080408040302030601 80
    0x122007090b00c4a0045820100b0292228a4407100543ca020745c0d002c002142e034401c000003448070074820f081c0002c0f1501c595000905988864102c000c010895002c00d20040b0602d101d05805850121004066450008000b03582d42c80090700c0240655281d507011020050f5800340d45150900354000c040c542510f581004105158070310500300c10050040101c3d003064064150b01d0155003d079030303603a8400711303040c1c40507582c100c0030082040030000142008004610300d01c1145600f02d2060340100110b0400d13042040c506450000c2c620300c00c900800031040d400300c0000b41860785a95034100940c231907119050148540c0e1298401404400300040d2000d44e0f03240d6800214409443e2440820020a040c0b0600804150901500340412010040800507001e00000351843c1120f500c1246c40407001040402d00218404901c0c04840e901d0b0320040c0b002580050410001c3c149010191004d4074240e1402004180100512030502001102140c01d1088210443e005980c024041b00c4107965500c0120720 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 399769037 1250 399767787 399767789
    0xd020a0b0a1202040e070f0909050a050910050601091a0c0303090a02030709050705030403050f130305100608210304030c050f0309040612051002090a03021203070c062a03200601 78
    0x100050310200c21600e542464801c0d1340c16a82500741803401540c460f00c0981e0345035402c1003000c01703108011600040038242030280305d01c0303050704120100e00c1c0c0c01c20712101c1385080c00b94a103099603c0e080c0700070000766903841101813049882c02e4507902858411103140070700c90301c50302c882e1741900c0c0400000c020070500c000038552020741c070075021070700d200c0e03507880780320b070440308161401e0f80014010004600842e200320080c00f03a01040c0504103207015054107402d5404620741d032044805411508400c01d62004034441c0074014070034030b00600305031380810205403c0200852525440d40c003002c000304041c0361081f0010b01050794490f04503004001c410302c080383e0720380119280c5481036003042004640c40c0a00700005c00d9055102009207070b041040035081e80a0b4110442880c2c000b44490f07c00000343c1d6440707101c2401c0d00131201c05180c0ea085541480d1000c0885508138800b40078000340a100b085648038050550660f440c8100c019150341482d0480701c0c0d5142d9405800721803010203100c4007404001c0743c2c0324 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 399770287 1250 399769037 399769057
    0x9080a050c1206150103020a110a030f0906020f07030204020c010b10090f05010e09070c02010e03030706060f0b0702010512090307063e070605040203031306050301060807020c0f0d020d020a0b 84
    0xc2c000c0e0280d5028581d44100444203602c502000d12410031907540660041d050b00300340707401c1c0604d007000084002440d1034980300d070540010311000e040581c2d440c0c00004e0b140250059101031b107441044400071079038506591100902540d4002298a2820310a40c0300c8080c4080c01003580c060014a400014211401ca010b40802221000c00000701517000701d40c1c1c0714030080c001d800000d0390366030f2450642e00040e54090503414060520030b09542a0303411300003030106510801700091524105821050301031a10780104401a8040111901503a001420750b544425044803614990b074411701c00504600621030000d25031801e120009810140080c1c04810001d403040c0c410241641c0070b00c10700e0560041c04079003200b5903010403240d00803506039000701e60300c80c0c0040c0c122480d040480c015400c1c1030545074403204c0015404401400000c0d0f00c60141d641111240c4010948080b10200103a041820055654822080000f2140854907002c40c59230038280c005109401890796015000c000e41d00103400342c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 399771537 1250 399770287 399770299
    0x4151107170909010e18010e1e010e1c1b0c06030c0305040c14010306030b130309060207030302030a0e041e02040603110c030318030d09111f0f0f09080a050c 69
    0x266072400781d01010780e000030000400d800d0560b441c0003905030040700090544400d580d02071460a42d0100240070340520325002900420340a41500d036001c01900030400500000d9040200144a8a8001403554140c03246610302c410742c0c3e116900d003139035071140b140041d51603540d685960800380900c9800c144115000394805200003041c1c3c044c1101240c1d0308441c010000f01400d04280502c411800220910074010b0400080b0152651240d09011001712625000714078010661400c1550140c3d40400814090000f0a101815039a0203520b078003600e0080300401801034100c018682e0383d50083e400e42c803406260b83d04103040c0c400107140607601c1402040046800c000c409005d58031900c040b10007002d6021f005d18110348548881f1604080e2030350181c83c0c5880244904820200300d40303d1106e065110f030b0440a076005405045c001107000c0890500c00d03c01860400983c2990055034600c1e0a1044aca07140103058007241080d101c20303940d80c1104100348940d005070b03020000b00041c15000720300d0407211 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 399772787 1250 399771537 399771563
    0x120f07050f0703171c02090609040204090605120d020307110d08030a05010e090a02060409090503070b010b1314090a0c260a11091c020a030f0f0317090a080304151107 73
    0x109480358410030f0b002c0581c0c002228a9505c200140781d0142c600403400500884c9450f8034540014166004dd41298806076a107030740c20442441c0c6204d10180e03040200c00a0890062a094042d40703078003640b14041c240d4611000d809900b590742d402851010356214070855120304120507400014007090140744d1440f004800840c032086000030351084280c1e0f00500c4180307030030b060003006005455145000c13912440180800d1001070107000c3c0d154083e20202c1c8000b91a440c034110b825412071a5540b101e00c0180741d50201420383c3c0c45516203103500c81e00c40170020a060134074000403145203024000d0b684401003001289040c006032503a045014000d6110309000403814001950f525104807800300340c1c000d003803010041d80c6e620158090141d10f800180400c0c642c80c3e030b03621541800300400c0c0045861407050964070040581060788070010703224140401540340390940161756116031112014054400c01b000080410403403405107880110406001d1101c010b602250352000d0f0440b180407070b101310200c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 399774037 1250 399772787 399772823
    0x111906020c151303050c03282c10020a020303030c07060b09010609170304081b010818061b0f0c0f1015060806031009080307120509120f07050f0703 65
    0x40a5018070018802c404007007095603000e561560180580d401b1030701042c8030700184c6d241080c1c00100314007103c03000b03450082035644c0000c0c0385001c46070303107c1707003440200ca1000520141c1d045040b041d4481512800d86050030400181c0c5004044100254144000410454800d106030094000548244c1d428403114030468100121501c09005400000310b50f00e00401942c038250701c40c5841581d035141500e240c01e850300c2445050903859070761000400b90880603c3c2965910048481d4000c50030041d4a01005540c8111600d41801030074180c11780f80c0c0900900e908169150855828140b030003041951111441703c010f071240c1c0e0307110003040a8014000303c0907260300180592607510042411012103641041d42c162540e0740040e260300e40503c5152049681d1a08511072144201d010340a000e4032494400c400403e2900b89a4035005a1420682400100c0c0340008070dc142c40b0707924039103058131102d045032540624048c1c6a000340642c42201d031a0301904a0208144c0140c0307020faa400040e049102e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 399775287 1250 399774037 399774073
    0x111c030b0406050301061404180804150f05030415050702150f1e1504090c05040207060b04050a1107151e060911090d021002010e030a1d0f03060403111906020c 70
    0xf225021900340b80416500e0103143c42c1c2d0018441c01c07003071127030b000d0403100c00d4580064580040e0440030103117403e21000848150080403079100c16036203180503031179490b0950303c00c1000300781107201d980c01c19191750220300c070b0a000740030082e0a50968000502c40f81740801c018a0300040039521006030701070640350605034000c01c8400c2c0c0d210b4612000134903071f44540401070000030b0503404400e40e0607c0d008030b000700d200d40c0c0311300041c005180202404952032800d40104400c44401401c84d00c7c11614045c082d122000e040000e070717551960000480c0560924081000d00940020403c065100c1303c041904807005d0100d80c031030340c1951030300442041703180f00510f480f0101d0310803000456406a0b810813201d0041c680041c0d40c9100352214400800d42000e80541d0902d5500b01e40c0c08100031803034400014400a40c0140d280b2810356046030f00440e09880880403a848001c0908040e04100c1c072020210341c01502009840d15070012260460640c00040c1440d074000c0d00194083703d514010803a44c40c2d0400581 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 399776537 1250 399775287 399775289
    0x2070b07020d140a09051002010f110a02100e03070219031104060e0109050603011d0f190c051302090d0812101a0c0114041a010b0307020c01111c030b040605030106 72
    0x20351504503283d80502d8002c00381d40c02807900c50b03003003041c0d50314041815250001040794035400b580021904005044030300060700caa5800525010b9011305c1000000b507400a1882c0e9845000701c0c0001d000c1d0482c03140030342035101d06500603400031500b05c000c12102e1400d0101ca401c81c0d0003096086840441c4508000660b0610709c034000d11440c41400522104a159100580129008000040c0c5102403164581c0807071018070401c043d60000d03c01c4215804081c000d10503d5221800e40c031030455441c0c2d41d2503d0303a8070140210360080135411030094209100f81d048610035040100b29104c0b0549034a0000710950100c003030042c07000303080030100744443c0c01c0d4003488043d101409030081c0c1d6401c40e1001440c0702d42000b880360584e5920b8040003100814240c0b445401140199100c80c0c0c0244841243e03446c03c5810b9100c04180c840402c20003513045c1d07020802d24410300f42480c1840d0200d0744940218500821030101c07000301c031205d45e14094160b406032720032005035400351001d000e034996403002c041c00c032000313 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 399777787 1250 399776537 399776563
    0x40e16080d0219020f0f1f0f03140f070203040e19110a0804020609010309080f030a0c0504060e2214070219020306010b030417030a05040201031b0c0f050309030f0102070b0702 77
    0x8520120052a011755070481401c000703012500000703103081c0044ca0007685481d105400703008081d20785680c29800284103148604c3c83c20144074480c10740c05d514a8146d00285014080c002a20100726524030a2085070000d0551511909190404216481210740c207802000d4450789000b906100350f0301c1d0482900d00110003038407000700c81e58464090100d242d10004a107410159500e10800006042d000a89807200542c1c8c0490307213a20301003008000329101c1c00803000602c4828401003006662100c2e618548060903a2218041c0804c1c07241d0328070940550b05461001410701c08404c01441d41001141d03c5100c20790b0843e500800054100c0b402d4590b44c40b00690560450310051160154410096405c144141d018101001d141c6280004a400558558440e107450b0307003d00003550780c1400303a03031015003810600340040d000160020300810558071006082c0403901c0704c000c0c00c0c44000d00540b4040b90300a402c2c0d91400100c07806990013540b0420041321030351500e1000c04d40640c80020b0312407818074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 399779037 1250 399777787 399777823
    0xc020d030f0908010f050405010606300912020a020307060302030c090603100905010b0414061c0c030902091017030a09051315060c060e0a1101030b040e16080d02 71
    0x1815440031140000d105158409014260500140401d401d21865594213880310001996041c80d00d030803070960300c0a1b800102041104408000c01081070220108281c02a100200010003001000409030811a802800710707851621280c20780781c0c0218070000054800c50a03a10411385440c010b40480c001a0703010143c0c00c1c0180509281d90400d1030086070001d845801c5088655076a054000c16101c0c02d03044024110004101007068041850f0b882c10324103002c5400300e0070015098156041e08003440c941c02032641e141e005521596000760300c45000560007819030784851426030410441200c0c1c03442141c000204491952561540c040143c60f610610f665842c3c1c01075150004000809003422040b0648aa88032440001480030380f201400900041d29400300412850812108555480081b20144d8002241c0310002884802c2820200c040c00d00340014242c0249011034010310610220524903c02c03881c80f403441000850540d0110784002c0112030003401d0541c4101c0c5c0340da551009400942d6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 399780287 1250 399779037 399779059
    0x1508091b010e030c0411090306010602030c06071d040509010e190b0601110322050f1206040602031e18160b070b07050c100902150a0504090f09080d0e010c0c02 70
    0x903100352512032000c81d00804844000c13110000150441c2c141056254596200080d42c040d54142030003440d00603c070a0002e14203042c20300e4111502c030400200004200101c0c50000c41d100d02000c03008045003030300070b813003088540f40c41d01045009010141c100c0405208a12030540751600e18002c0d00441e51340000d02d03074240e455100055900c1d16401d0019040d600051245801c2070294078608002a08510341d42c865282c94282441381420b4903240b5640180d25543c800b6400d00b000003901c41c0c102d0780c010f00041c0d0782d5440052180041032843c2d44025118202c4061200c1e90020101c0099207403890707400e440c1000010f0715040594101d0f0b210f10401c8400c280050030104810055440c0e0148150030b02300c0c600070b40b90181604141201c2c0c54055002d58030007841065040016149103083c0701d002041e440c02e08030220251143c00b451142311f011a480d0300440842101c6138000326081030740f02c40c525844034001010f5001a001100c004034041d840c20120801c018800d02003440c029070080c0c103801200c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 399781537 1250 399780287 399780289
    0xd020d0b060301090b1003110402040e060d03050c0102040306021c0507090902090604120b1006020d02100e03040e0408030912030c070305090f0a090603031b0c18090803011508091b 79
    0x1085000349020b9055590307401c084d001ca001d803a1141d128281c01c540d001049411850055446603155941074050751050100380315a4443d24140c982100080b100c00a458140f03250885a522508030a01c50130750000c200001003182d143c011f000012207000c0d611201483c200140d000b1102c04488842c0010181c210030800c508043e4010000810040c180340e00c0c0a131600320f0f0700070000c0791a404599120030501089003982c04912510090701452015184403980c44500035550002202901c020543e00c03441286844030400469000740b0704201000b074946024100601c00d03400480b6014158000d10103165000e088000c03c69209000380c900150405e103554a040312203401504020303410419240c1c0303048139a5a0800250010007a0b05004140e050852070001e00030400000c421550b0003d62140100181240702010261141004180c0940710884410030180c188400c0180c2302103000070011503640b42a402c1b4081500043d2582080354076107880065a0b100380c080400c02c525040507195580d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 399782787 1250 399781537 399781553
    0x50309060319053103020c01111e0f25090f29210606010c05070909030f0f080708040204020c03040b0c1b03120304030e150a030507030b0d020d 63
    0x10241e514008420001e22500001c1100c0d000d4840d0221004840c45600d880d210350b09680c2e074503404c2110400301002c0c0d00d943c042e581d0301c030003107c16050041e1400b2050820b50200b007000c14440200302039084044848040c981c454007491a080098028103200b44c81ea90006501901e200200c880092849854400306000600b1030411540c5490345408900e0f1244103d45d52a10209183c115841465180c0c1070821003c1440c49000781d1f1040c20010900400c0040800c101e58002000c2c00d01004d100100d01d8103505000302030700071143d01c1d460b0894500506610591412002106454070407511007e880d05590405048803c1400a0750b004009001800c2079000360180180c03c1c82180c0c1069183c107a6550190808002120507500114410702c4d104100303030303054070004419400f81c4a4550203000c071407044d1000801c09410302461300d04000c126242c1220802c0c00d013129a02c2c850300c505002c01c006000c0e06d01550150700107401c206401d1001d140032222070413a01c3d03008103500501c0780141d40d40c0503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 399784037 1250 399782787 399782791
    0x110a0b0109180b0405061801090c1401090503120a08240d150915050610120515151903020a2001110f040609060804110d0507180b1c0503090603 63
    0x3404804030904140003c54451405009a204001801e40c0d0302d4642c58841c44c0700144c2c1c032070480580c100411000414001d058407000d03182240550000c0d44800310044e184009598009905489070343c0c8014401445030004e800721103e03235902d40c00745072100c03c486448210325940541041d260440391502520f4100d2080070b00303030b102c0d60b05410108202c1e80000b00301d441c004d8003940e801920306400c20b031f4070905101d02580050308990200d490042c3ea0001400c00c0d1740924401000380c1d4800c08a04070f0344c40d200080050500041a41c542c03140104e0100c040c5070003501c017020b900c58031b04a003881158000d000351480d5030b850f82d6828034a40c59036034080682c884c3c44009100036550341c070041c81003d0318102c001c0c8140c0e0b800e54202981d9a140c00d03401418001c46600032001c100301d40c014400083c1d401ca1408415103403c8500c0c824810381802c2c01410f000681c0e00059034040401c10381e550b050402d030407881251000704e440079040034609281d1910b1808103440249107400c20007001e42540341801c051a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 399785287 1250 399784037 399784061
    0xb0304050706080c040f18060312030e070f030506040b040606050306190b0f031c11030403031106090316080702210c010905030f0d080c040f03081903090c0302060f0c0106090507110a0b0109 83
    0x2185160303807910ac2c541c2d03c0d003a00b00700b0760000e40c81d001035890750801005040000d003446400355008910350f4032100c1c1c8407040500010590350148001c6420700005401140c040c0800406684003070801c800000071903503c4608101d0348030700300140c0c1d04c4180742c8940da085c0502d002a0191420410451a0405810300450314000b40441199540c14112040000d13202952082e01c820120200c454406494568000c0c004241a441000068010340001d8001d412159012030751035103400305840000c5014103400001c400c42d40001154440700000000c50001103107081c0c0b82e20524036201c10906441e204a4a0250800d030311035100007070450b104a80c4682c3c041c115800c2c48ac00d03d61070700f11035410405107a10a0300c62035804103401c4e44442c40201410b00588407804c0c20030002941340e480107200001c0744000b0780300b040040303108170f07001404000300c0355800c100400070810036031642907000c02424152a01c000084400041d0b4851000c0010b00d000d541da0080e00d91000750b0304c0c02c010708000e840032601103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 399786537 1250 399785287 399785291
    0xb01092d060e100504110c030418110d0605040c0203040b0306091506211518040201120608070801061403072c18060c09010507110a0b0304050706080c040f18 69
    0x24042e80d03425400c1e00810140c280e6281403440d110801c002c0e1103c1d5001d40030302c1c80007009200104000002100e040380e01e600c004030083c4005040f89002440311108003e1302c40c0c40080d1518420f111a0b002d00e043c0c0311708a508010641010360203d999001e40c2c01028050042040415041c2c03421300501c940c0400038078032218813030400c1c0000c105240c100c9111b1184074031b11000c01e80510042d182180350300030041c203036925191151100041461800503134002c1c039100740f003020406591040810101010b50b004040c000680e4072203903142c4d40d988912500341d49510f0401e010411210521184404590040042030464100250300380c0d03034400d400c2e200400c01840e0b030024000000031403c2c140324a800000944041030404625410004000d110080492003002a05000e80c4c01600303503281c1c160012400b105072881c010108480f220250005086c1c40d0007c020481003160014240301a0369081e034800f503298849820a04040c0218060912240038541c002c0c0250061200320350942d080541c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 399787787 1250 399786537 399786539
    0x302031005101d010c021804110603070e1203030403230919031208010627050a09090515010f0b0d02090901080715020703171309020408010203040b01092d06 69
    0x10340c000e03200c203002101007960300002a141c18809404090060400c5c24900d2142125900084045105641c40626400840c0124090000b44981100030300c80c050b20a03940c904060310b001d058880d03d0f10115210346440d459402030404040141c1e03029683c9510b441d078070400c840650840340c025241215651680030310250180d0380ea410340790110000c141c0d40c4a1040e0b42103040078603106000703d0301e6005203c04400104069903022001007440d16071800000740015191380e40c03422410996002941c0212660390102e800f16070365110080c424404e00843c0c1c4c22141b9400515000d090900c00c3c43c0d42000740b8041048460b00e210300420002c00203503c010b1524480708001249100281c20061a9034010002400010304a140c1d50314556076500090607a00d02d0750b0b07610300c41e20119206400c1c0000c3c012a0b0075002c003913941c1304403003d01a103002c150344031500d604200303000303410854003910181441800021803c0c600d1061744180f803e078201a10a184504040654035140b882480f0500c55541d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 399789037 1250 399787787 399787789
    0x9020d05030d0f0614130b0a0f0b030a1409030d0b0a0905130201020c010c02090a09110a0602101104181a03150103122606060d240b04150302031005 65
    0x2400051402c1a0000301c0c81c004032007400880e40e8a8000040c0818a0b0003c190070b07a40302586404010501500481e56001c1036001c10002d418503840007205009905001c2840441e60380030318807138044140100180701c000c81d241d60030100140c0e40c1a00d90f401c1003100b02c05c412900d80003404065000340c011161155945490021035804035084403103d0400c0803250119a410b112141c43d081d0246041080c100385d640000c1c50342c1d02c02400b88002c02d0f0b17403030707200100700001c03041407440c024802440030802c144c0d103040c065210f080c11500585200e00c1c14400020412a00060300e054403d840e003a0582500b10403100740003080103000c80850319019200b0070515503070802158013452051244240a54034516140c00c041e402414001e09004c0c7c0160400560003201da049010092409880c01d11900c036440458403600c16001781e10396a6007032582c040400e00d049400c002c40d9072001d820300518244c0c0c038000b02e061406a80034a94080c0050100840014843c0c0c000c0e40d0000304090038940e00913a108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 399790287 1250 399789037 399789043
    0x501050403152a021c0e0904020a030503070b09070f0b030403030c09092f03090a02060304031115040b070315051011010504050c130605011202030406020c1506270a09020d05 76
    0x2241c007008104083d0b20102c000d6070601010103c100e010700382810018a20501801501c8400021806000701078000b40a541d85c031844c0030010758000040d01e9540103a41005a19040121401505407062640004480510351078090480d20711200301c50075621240da08501401004001104104c003040340414012410b00c00c1c0200e18150210145149503c0700307003401c0c0c0d41d00e03001d0780d40c0c0050001e1017004040040800c400c06410341c1156a00d0743d80c0d481e850141c4141c08050b820000c1d80c468104803444a012250300c032805640200d6101e0403a580710042203065403012090b030f103140d80c0c00d540308014500b400b100091198000f8100031054194419540c1d0850310300f142c058405074482051607001d8207007441e010503421b00280050007024148000607110200d00f40d0b405011903400000102030005903819104007450071004da0740c2c0306a4040501d494640150b5095114906c036681906046100120303145200005680b0f05020ba80d42202000007044495001ea070010341c41506180007400034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 399791537 1250 399790287 399790331
    0x206150409021011070803030903070f031202030903130e0907231509011b0c0e07120f0b120721030207030c060206041208010b090909030409180203010e07050105040315 74
    0xd944d0303514103454000d5202d19024a40d4401c240d10340041003400018070000c4103c0d445590000440d0417852414035046a10320100b0941000c00c510110038000c86c12000b200502c240c90001851086c101d4440006170071102c0e041e101804c0d10f50041008200300d4600180c81c00880c1240c0c601d94501e4408280441e84010b6a00090f03404047c00140c1c00c02c0540c1c202078a040503170724071018080c0c1c2d407005541d00095585a40940402c1584032000a1119440b036140c078441d04511141c2803054030070a024410151505902d200d1144041010420191100149600460f14010590143c4036411114583c224000000c213600f10b000341d00000c0f0100324928644001048103600801b00741c43c0c5802c000b0804400b03414031008101c5000010000f100e0f055050b6000c407a411606c810268865030600351840c82690b0125414504100c3c1a101000c92460066a00c50003070b8000c0c00744075160551240c403203105018090115400b4081031000c200d200e521129100c0041d4000200388020501c0120a0006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 399792787 1250 399791537 399791569
    0x100908030604050f0906040602090411070f02010e010e0d0f0204020c01021b070e150f0406090e2d070e0403020c0d0f02040c030c09060c030302040f03060504050d0e01020615040902 79
    0x200100348502070519101e06540b100210484066034201701c01c88030785585010300040d0580c0d070003080000080d0f072158810b00c0d07212428a600daa9a140519001c0c00d402d003602c40503030100c1c2c40d075001c00420354041ca0348240032110090803501c085225a480039100c3c0040c3e40d060340c1140d8240414208044248000d1500d03130325009503c10904d07004038201d403030f003c2c00717803c841202003882c01481644814000b0313a4680100454007007503204201030205009017125440341c211141007c0c000000b02d00e01242c01034001c03081c00c1c601c0d0b03010060400704050a08012401c003002d036000c0c4004014001030ba0341c41c0ba800c148248150f03100d1022420000320781d015100350684045048524410844c034040c41442c0b0301040506040c850000301c000040c050b107400344161401e002045d100d003001c040c825411a000303050060350382030f2880d4490516400808049070110f411b4414001c0400343c0500680e00c00705040e1050303000700021340c0c4071207080e0b86c030060780820550040d403035404010043e506d50f01003002c8510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 399794037 1250 399792787 399792803
    0x50f0d05010e09190b070f050d050106110c03010b0d020f01090e040326091f150b131e0b16050109060f061202012f1f060e0106050313051009 62
    0x10301c0310143d402c10110701000314418080e15034a500240092070103560184007402d20507000c424110f01507486104030340c551410700d49020000300d01c4a40024504400751301a20446072400d09040a140c202d0302c00c4490b8a9009041c03006401c01860b24411440c109081032600f6941260b88440380204100b060b82d0440100d00e1003012980304200b01c00007c0c01c03140791040c1148040c2080c55819454149482c0c84143c040c0103c0540b00c3e900c0001d42280502d640035202040d40c00d036540302000ca40f07400c01c00d003411050640343c41c005840903160889242c0c50041e0400c914100c1e01c1e0120402d130651100c3c0020103c0030400300c4540c0031030f10a1249040a40c003c2001046501d4500c5809007111480d4004680e4855031455400150342d104410440c62042650002001c00c50304030b40200c1001d207070742c0d0030100b03100320300321303429400c800804c0c400f10310081d108280500b640f0340040010a0809016040000e2030a00c0022800a45000070541c81e0303015100307440b4401d50034104907081e54030405058420403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 399795287 1250 399794037 399794041
    0x30d0902010e0d0807020d0516140f010201060305030a081e0a0903030509060106020d030209130c0203130b03250c1205040513050103030c03110c0a0e0703150510050f0d05010e 77
    0x35800c40b0441c64103400c1107845145102c42a55401c0950054110190103004a10099001c0150070092415041c11565041e003c40760740e1600c119560611300d03a8030303004a401a2401c8519401406800d040d0b0368001c018600307040100c8011511103000825414000038480c50940038061900c0c42d25024400c411004a10b0412031304010702611000781041141d81d101c1e03001080419130221f04020342c40e90600d40941c1d01c005000c00205c03240b02c080003030300034240b07070803003100701c0e990000020300700461300910b84081c00b96151180b01c02d42c04200c8107009034280c0c2500e01c0540710600303200ca2019801604050b8441c14503078441041190406901d034010450004060103146041e412030607004002c084184030035070555800900245024000805100d40d6070204051502c041c88403030300b0000007505c8810020754802006450380303826601080401d140c4020b20360717941c0140c41c854050300d40103059540018001c41c0c00b2501507200d00301c24414424103002e69180e0756a01e005090090a00d403003000064 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 399796537 1250 399795287 399795289
    0x2280e061201150e0105040504110d0e030702012c0904030c050f061b13140625060f0c210609050903040303080606120109020711130914030408070314030903030d0902 73
    0x5450f0b4050500c2c00e0024500e40404c040e0703402400c890a44106403404240d02d414408808082d004007944a6140703410130f01d941d60701103000805085414000daa07031f804c3c10030300c0c07410080c050008980240b00514a50008170020300f403420681750464480d14140103403c0998070f43c04c0c1824990300801c0050380000c01801646810031038403034540b5150800c2d5916121200194584080d0701d81715068284d0700b0182d9146240d0381d0300c1d041d244403404154246040c0810240c011082c40b0705000100c600b24540b41c1c80700c2d140c440c0c511603003003100b4040e1943e0115420501c8443d58050002805103aa19100c1401254264890107514060b1501c900107603155421494050002040144040d0140e102480100c5480c1e41d4080100e044540154006030748509a08055194548108200e03400880c051924602010154407110419002e9406048081044a01117071a0b1049109025280d03205c00000d00c04225405805044d1001000032649483c90110101e4110340085003181c8080ba903a103410703815 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 399797787 1250 399796537 399796559
    0x30f160c0b15120708030d2703210b01121d12040503100b06180a05220b040216020405090f07030b0a0c02010209062517070203010e0102280e061201 65
    0x3d02940b00e0252160b01e04005001d9030301d01074404e911810382e4450700030410205258152508554400ea403100c000c0c1c0c041c0c1409001804620008490608403102e000c00040192041070300030501650f414006203207828030b0601500039010109540d00306140c000e50448410040318458008030100c01b42c61f1440c050815040c8048009512446410410141d1403540c42100300c0790300d101c2c0800d8043c0c01c24000c0001c5903440f94142c02c010341181401581c100000082c01e1487c45501c0781000511540d01e1400500c000c2e4000c00c00c1c1c01c811904071081020040c94240c20041d0720004c00310441c0e103141d40d000fa10703034030b8801c4540c0123640306400307542030251022850043c0f41050480d230000754600110080440d00c3d0784a08041040280555002c203541420320f00d258180c45900b18009c10244410000200c0c626030003a04100d200e91b01c0e00048000460041c020703100d2506203000d0082d8404600c52608009111500110b070801c20404072004940e0384041c09042e0b0b08000040c0080e042d81412600c0e00c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 399799037 1250 399797787 399797809
    0xf03010519170c1e2103070c060804140a170c01090606090c020f0f1207060b03010509010e070f12111314060405090a0f0305160507120c0b030f160c0b15 67
    0x203071406409801100503101e582c0049a10b5140440321001c2c02050440c0311b045019480b0001d040ca41608400a001d41d440304006001e035001e0542c410a01302e1404034250360700d256020040101820074450008005100040c200c1c80380008008500e0705150740e03814080703404941107558201d07596076144010030b030b040202800303c2242c40c0040c00c541404000640e40c0300c021030300543d8120000a512810000641c01c0064040d001034001d105500300040b0b149c1c041e0140c003071107a940e8802e10b0f0f40094503104044c00c98040740c41010101d41c4400113600c500c04101001c19416800502c031701c0400005452500ca42c0d5209801c1a00400f05400c0c00000c003c00e560010f012800103901600702c4502142044595541c0c1c03984c941402659028510000f05009000300c201501ca4020140000f801c4800030324400d0030750384200c11181002c2e48460314050980410340d0f00400000e071100001c1c9148801d031852078144002d6007014800901d4982e1000001e5001700c42d200c41c0f84040751200511400e107405208 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 399800287 1250 399799037 399799069
    0x9180c1707090902040e0a0b19111905120112020a0e060f04050a231501020307050304060e0301020912031b01020f0a0c11040203040c06090b0f03010519170c 69
    0xc0c03204010004195111020300900c155241d481140008540e81c03640070041782100541544d01606c074501b007000c04c500c4121190240c0e120702c5603038842c45419502c00d0840d902c0c82c440920341048414040d080041841084940038132030104100c0ad086442c118106000304103400100c8130440756072041c81403100d004e9010b542c140c1c021105201c1e0300e5a4041c1260300c8058203480000b501e5858a00c5100504621a1a6144083c05441c00110388001d041214410710082100c04c3c4000e6440004980d41d119540b0082d1440d0401d010504c951881803415152002d002000903051030b02d80b0000880d118003094074441c407036100007800c84011000031400002c00d4a20402103041c40c00c0c04408000070b20030001c1042c10000748d8003510342046860810394036185009041151a4a07142c40e101720040b40602440001c0383c0901d40008100c2000c60484114680e500303401801c50b440e0005014811034040c816a121a00610f804182560104a40c90000d070f0300340010013064000307006000c04081000040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 399801537 1250 399800287 399800309
    0x30903050d0509100509150915010b07240204060e030c010801140303040305030f090a1a0409020c0307060c050301050f04090f260c0c130903020d050306040609180c 72
    0x50209801100355071005400c6003001c2107541ea040e00a0b0306028460130b42c01042032514050103a400320001d40707220650900035500c0181d0f11403058a40d9110f4010815416000c0000014000a1525000350203490b1041c0b440065004600036140000c0f40507081c2e28113450707408074041100591010642c0309448095010700103c804580008010080502804404c1c00200805450940701081140d00a5821502b681c0d01d8800c0d12045500329480340c2d0100d4800c030f1510001081c02d100c3c0c0d6000440700c1810721242032815142507030582c0a90480b2529890301c0c0030070b0000b10007041041c011074000050342c1e03842d41c0e0790358104410411000102c0492500592400103d400001c0580e128040c0594005040e8100301040941c4100642c011203c904072204000ca01702c00b0000001809442c5103008642d0040004a4200d01c0d9080b00d02840014006078480b40340009060300510056030003a201a00200340c541c3c5030b0310312200b034508441001f000300e14013421000c2446046800400a003c400c448 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 399802787 1250 399801537 399801551
    0x521030a06140d02010311040e040809040c0f020d0c0c08060403120609020a14030a02040f0312080703020309030a030c09080d05030a0605060c07090507120f0f150f0308070227070e0103 81
    0x100f0408200c02c2002414103994584280210b80304500b524020414003003441c80910306480c00f40b01c9030b0420030400380a5030520152614142c09020620042c0240d54010f01c0424800d04048030804502d203426502d400048802084000d41800101d2082c0d00a44681880d245401c840204440c86644108261341c410300c00d520f440c07a031100c5d4180728a614000f5194880d19441c0810000744682d600c0034909550202c400410402301001c6840511015192031500355210074050b8142e03c012110181250420070603050010301940c1f00d96188240c3c0c0c54031100864035490746030302c1e2811030300900c0d021900100410029548602070300018010550b0528105020008a150b68414601940303103800d80f6203000498582c4648070b0110f62505035034040c4041c0c45944500402814000c201e036100030708009248588030028510001150301100043c203ea500d1911251a40d030060300c400ca03480300a505205140f411b040c03000351503d402e4024100d205d030428038809002e030869070f40b00c3c506060070030702 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 399804037 1250 399802787 399802789
    0x1060e010504051207050d0317090a0f0b04170c031b1c11030d020a0f020c04050105030d0309111e10020109050c12010e0607031e02090604120521030a0614 68
    0x20a690490f0b030305585a550501e440d0300620b017006070030b801141e040003200c2c0400c800e240e80715501c1c100614000c1601003c689510044a40b12038405101070300800345100c18030005040c081e641a0311500860a214000c60401c0c041c01c00755000c02d59201581e8008500307040c10850041380c10100e0320006004010307c035031250311164003045140c4a0310500408107690f503c1c2d4402881110b404040e0540d08643d1080904006405071100d00e00d400300521450031981e509040520034541605c1006000700b14400501d401180941421201105c4103406642c500089031150070b0034528007407a83c241c0e0130f071458010061011135108480e10340116810a429000840c10100d0204580c102c141d40f03410b800b21750075890710b003d811014060009845404200a262030389070380800c07809891030100301d0500d0f182c0104041680108800340c0e602c1001000104460000c1c1d0701d40440d490b21070b40036200200d03803a81c0d0f004481200390303500405841c2c0000030400703000303058881c9102908141c0c0e030400d960207410b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 399805287 1250 399804037 399804047
    0x7030b0108072c1807031a130f0b060105040f090902150304030807230a2a0506010504020a230301050306180613080d020d060503011a010527090406020a0801060e01 72
    0x3880c0d840108034200c042078065507610f4103601c030304c18140b00f10b0306441e6483c13030041b0030291a159645890325042010407900c0c0162500c00360350300c0c0c04c540a01d5403080b0342e0702c9100000034098034543c1400401c0000051040c0321001480041c00c009000266541060052082c100101c580f0491803500030800c2000180e00403d145811003d18580310951101e03283c2e2031001d00103a01c8841407280f030042030700d00815602440e07010000301c20020b140301400d854010362007580c000704002051a040300300103202904003a27014120072241071030f00109254203034400b4440c20b0390071811a20b05050000c010310050400300302030341e0440880e03400c0d03404c0141c4044003e47c4402c0090119410508641540344c00e01001200340d9074007045040f021541e440d0000c400800070601403154601039424400c0e1860405c2400070200c24480060716100c0c81c0c007268020001c1d4512640e45500c402080d04042d9070a00e8603503616161146100b2040142d46201c1060090300740d02059011408211440041002d41e91713001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 399806537 1250 399805287 399805349
    0x21c14090106061d0301060e0c031f0506040905270f0c06040b190309140106030b1b03060105030709090213140301050c0901031e050405160b03150f0d0507030b010807 73
    0xa1000708044d8020040002c2c0584480d0b030061000080000610105640b6100110f000f220100700d40d9800e801d49110804010600744203540d44113601340400c0041da2010b401440d400509404290101c0d0070384248404002441020708580c3c1d40100115404803604106000a901080381c5642c00e16180121344079291094480c1030004801a19046071680d000340c100c000c0312a440a00c5460032902d00310742c603000f040148010b84a001200d404544007007400307244c0c400301031200711906241d90340b1440151075643c000703040e03c010000c0321400050445103034409061525800f4440ea6000707464a07484020a04401081030700ca40d24150a100040b101042201da0981c400c0c28007080102c0512801c44015181083d400c038480e080001300402c0003c0850440303600c5501a400d42500d0b51216180402c60000300c07000c1690300590880416145443c180111400324000d200f1986002c203941c80c2030800c0480e60080b0b586000f8900144080c0c001400903030701510042401846411400d407030000c80002d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 399807787 1250 399806537 399806567
    0x4050a0c0f0b0412060f05361504051c0203090a080d080a0c14120106170106080f0c0f0c0a0302010b010201020909150402070803010b0706050a0e0a1203021c1409010606 74
    0x102d018882000903d03005442c4010382c25108111600d07251445064400c01d01c15041480c2007030115103075070323020f08503141d0301140c4490b4010841007281b200d0740ca04035003020340251668400c150001005a200c107029501220040c0c1c055500c079001d18043c00b002040b01e410061858002040b07102c221035000482c1680701b07000101c046941c20700c21784161101c02d00490380000c6003c0016100d0f103550240b007021b40c1202e001d0313a00d07001c0c456804900e0400791503085c01441c0010b038903c00810640f00b03600e514550806036015149180a201e140f9044040e4040c5414400e11f801010000c000e1580a215505445070280002d5103460102d5000a101020040c040750f0340000302c80240310303244c0301c40c0d060f210307000e61000000340e4a5840e00c0022500e0b400c50b11041340e0890503c0300181d4000c80ccc500910000c885031030001e0410304c041c2c0c0c1d1541c517052218244103040660a0112210802d0008400c1805074000b080010303075101c1c41284c0c0001035500a00408841c0c0c1030071401c00c1802d41c050740000b807540c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 399809037 1250 399807787 399807809
    0x50c0a12050d182006030a05090c0a03030f020f014508030406050a110906030a090210050d060f0e0403110a0b0103060e06070e01050d020d1404050a0c0f0b04 69
    0xd640e2000e451501070503101e0b810315860000d640f0742c040d44060900c2141c81c014002c0b24602d00e10351941207081000003a036070390851001d01c081780c02c0d89496048a90090302880075038000e1644500452030500c040e034802d500195101c8450700301242c043c807882000c004014000e001a0300300b040c181130103280c1d501200c5580c40e18522840c58240c0500d0301400111381821950415a145051040311500203803016500945000089940b000c49445011412950a00c41c00e0070f08058070100038090700014a00c00e030190306d1b29010401652510324000081d481c50326105d80b9803801801c0c00044902640003c0004c003200da9043c002b130580d00100c030343d015901d172030f19440054241120900b402c80038040104211107160010040140c1a0004ca0f140e108000c1101c06c00e60340d410701141c0940ca80d4040340d01140042051074000081070b0000c0c00804204100814082c0c507550400020340d80484080e90150003040e0031904100e44000c807140280014092181c0e02400d04010103010b1241e0701c120141c0314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 399810287 1250 399809037 399809063
    0x3190e07051c0b1e090f0a02010e040216050106060e01020708060f040c0816050f041401030615050d150501060c212a02030f01020711040903091203020c0a06050c0a 72
    0x100500722500342c600d50004159a031828403000a8a6808601c0c1d040d20000c4415800100000c4001070b514139040d22080082071001c1c5150010f5912024441c40503400940030000c030a44074145645145c10940711313400010f0345038234050000f015000310799080d0b0f0464104501c100503080c000100c20341c03c4015404a8101900c49103000b40542042c2c0c0d00900d418041e02c650303a2138061039041a101203c206841c0260781c841c004081204a0341d0b500c1d0025170002e9110014400301c0c1c0c440c1e00c101076072003441903400c6026464100140741e0004468040310780101e802c1300c412400302c050040da4014485030400f09910b554941e19000205042c03041c2c0c03c5001029410701b5419840b5207815034448041010540100400c0301c150644142605400d900910500c4607a88200d881403084900550b00700c0b0031588500445404c01000d020070345802c0e02040740d241e1000c034510403003003d0001d9280c86500240003504094050200710081136000070184641844001154440411206055580280c0b0b00f4260 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 399811537 1250 399810287 399810319
    0x5011403010b0c031201030516060302040305030d0f0f111c0203060a030813030c1401030c0e1e0f030d0c0c08070303050a1b0b010605040f0e090a1704050402030c03190e0705 76
    0x41c01240d1001640e80c17424000001402000b00d0000fa04600d862480c26581c0d440d0f06068041e8452880000d00b00e510422032180344c80c0703a0b6400318414500352a0081071100c20300c00c0a02c01c2d035403d415440c0b100d220004000c110302400d80252004010840c50a40c198a000400a24043c032903200c09414400d002134070400703040302050160043d690104488034215103459040b43e05020003405d041c0828a0041681301990040172603103000c0900418500342d0316a5004108003d00d81420110b4210900e001c080041c0d640a100031040394070349a440c4003240b461030406140003101548006256004840b0520129500c04102d840e194401d0429101011382160a0101d0902d1403402405114480c1d00100b0304952042c018004c650400c458400038070744542c04005101400d45000350701d540f00e034801c200000d10301281505003803100003003241050355440114040e42e004032042034103928004100300100d020b04022400840b0440000c2107005ca44a00309aa141c4072801040e02c5024a10384c04400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 399812787 1250 399811537 399811543
    0x504231c030e03030a050403060e060420150a0c020a15050403080f130b030a0c080c0405010305100918020405150f1c15090201030608152208130503060105011403010b0c 74
    0x708a0b0180c01c80303035140c0c0445401002034116000031203a0500740103c41c4207042000480c21700403904250340c860710b03d84203040003e12402e01d400481c0c00c213a4038070422900801342c2c4003800718000c0b40d840b5181c40711030600c10800200e1a030340040c5841d051091038409942d902c10240d070117595100c13070303010707a030b100100303080c0070980504104d500140c1421000070a0803099a07020314082c0c0c290362030900030802208010b0b1990340048500c80401e800c18802040213601c01d030415038020005091005406844d903403010103869224043d00b031000349001500701103040612507640d001d1128810840c210881c5000251010f0f242c0c9220343c8940c94034605094070345504030511520723a9112a08107461030381440008043e14810b40183d0201c0c0c41c0c1407000030310040103d8036a407400710b10b80340400507544105038041c61209249004c24807800b48034144000070044401000d061004800398800503141808040c031388803050304520b040051010f6441ca14149810543e41503622000381e144d26100c00c0c3d081070386 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 399814037 1250 399812787 399812807
    0x2100903091205071703040614130f0806191a040f18030903060b040e0a060c020a0f03180503030405060d271202151005010c11060a0504231c03 63
    0x40d8044031200e107000f040b000240740f0046402625401c1c4804400910154990007140701b40300211300b036000040000340060380145102c4201d40403001107551983d60b25001c0c0c040e141c0000e11107078000c200380410101040350114440e00420030a0010f001001d02c1446244005454130f4046c41c0c4450480900300903c1d0070940390a00941a985050081c9007401010f56516100540f07001e45030882010040c289070007202c03d03000c0d20000500399400c1983e21040101001c810040440c000c88000d000001d6461850500150280e640c59410204040c5a480d01101c40d51090b44240d104110812413500c0d400140d569507407045000195007e4411141c0b1803003078480302c00c0700c0940c500c4c2c0019010002c2501d8600340540896080b265010701c103000d0f9030001c1200b82d40b0700e00e049241e044100099841340d0941304035144114008400460700401085a40e007050440d18041038010034184106103490035072451440c211182e003a94140c403207011610943d00707207200101c001880786081080c1805644501 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 399815287 1250 399814037 399814049
    0x90302130e06092a0307060c050102040e0703140f01030b0606070c09051f080d0c020f180a0b030111070804031b030c06020309040b0d0c06110c04060e06010206070206070210090309 79
    0x14424a4a0f070f41444e10781c02d208403480d098240c51a040c5210042950003c01c0d110740c0900100040b5003814420b03542e00c070700c007081282c50399002c1201050700d144030790020340555400d8030041400c201000361041d050800800540d071100c102e90041020514544603290483c0c01a24415503c4280d41081181c100c0a50081d0b047e80341010148581d82d10038001c1c4003100c441103100211f081d5141c02c1c81c0394580c484a44140e0005807c0e140c2900035240080d40010800130061107600c20110f040d80070002e0399802c850001e0344540d641c6098a0505080c0109006188203103100741c0b805109607a04c2c00c880c0a00c0c000609103c104001c2010f0b40d20340342c09140080c64000000c101c43d107aaa2000035680c0d8002c4540d01d01850400131282400c2c1480b0201c00c44555103c0c5040c600c841c2080011a00c119100405803c54400d881144200c0d4481e4480c90340036182444a61495240c0f94002a10f0a9805000901150302c184100040141c0c080b030003094402002c1408250401941403c4402002680044e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 399816537 1250 399815287 399815293
    0x3051e091c030b0a14030105071d131b030603050f030c060f09011e0218150901080705160b1b070807110609130b0120070909020402070b0408070501110703090302130e 73
    0x82090705e00401c0c1414403520480003400309549542080300d0232048401c185030401d080c060400164a010f070340d41036841000d00c50000e900302c291442e050491900d840c0b4400400c0d84c42c0b005006005081c44103030706082e0240e000703500d05001d85c8162955160001c100c558501004804501103550039000b07005045400b50110040000e202074075030080d8803000e40507a01107420200d56446040c0403005d4105501e10b03440c018200b03c0048015151210020070396401c020040100b03244008144491085050148078000320a151059007101101036072004164040030a03c440d6000981010440318200e0f4440807003507081003020302164290142d908881d6104c0c80c014002c410100d1141d010401d81c2c0002d9941100e0003200360070b0048499200c2e0002c81c110341010400740b10109154221001440c4090401490000d0035214480d03034a070181e400320340401c0000790f54428842d00f40607405c3e4007006c0445c40c5241000540e0b01070300461191200034020340038012420000c0c002c540c00020228800b9081d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 399817787 1250 399816537 399816539
    0x20c070602061f05010e01030926070201090e04081603050c060f04031d032a06190f0813020f030a0203010f06050114120a0203091c03051e091c030b0a 66
    0x102a45a05080f110600500038140403c0c081c0840511400100c65060b110302d080400b50500450150240c20029a008100500001c0d10072110100040000c4c5181c06455203481251000401c1d84201340c2c40780d074284446200f03100210f0300450494030040c500089810f010300d200d240903140d40c000e0f2003108003039000340b600b01300c000f02c03000882d036104900c81c2d90340300e5002070712036002c58444088010036a0558482c0301d0320241c0c4c40c0200304221150b0040d01c4101c042540e04400079105503c0845200710078150001e10001c02504503844496034482400c11400d01e1801020046c031050081e03c0103440740c003840401d4001902e00b40034512036550064000d0001030750540300b0b1005818280300b090b0001d00301d40d0408035841507090588041110814a060403600c2d440510000380d08040c095aa0038040e10f00c1a000c07907500720101c1181400503840200300345c94011540d104000e04410b00386d0f80603052004105029801207040704034910b889000a800c0070071400100d00400f02c00418607006092104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 399819037 1250 399817787 399817799
    0x3030901032706090c0b16080903010e0609010c08062b080706020c0601030c050103090f02100203040b070b01090606030b03250f091a0103180809010507060c110106050a05031f020c07 80
    0x302c6682c00380645064813080c0d9aa5616041d82c1c415124a945001b19420920340016aa00c00415127a40c0003400451140d04040d9201c0c10880180e400c0c1d00e40307a5495803045005a0403210381940100100c566800101a00c00400300c00801c00b500700c9160200b401c2204200084c003810340d94603a4002c4c04c1152a00303520400aa03844000303000680d0085980e480003e91036119006512916030310a04550400c0641d0f800e000c1001c6200003071005600041c040442e0540744200078029160103855000b242e035151403809800c461164100204041c20301c0c4e10318405440000302040c21b508201840140315000d10507003031190403540c01c00380224880b88400189030019400159040da41d181c0209c013030070400030043d400c075450401030301308808420340d554020598240145c41241d0041c1850382c41c2c031000e55240e0040340c100c01070007008101080d2407445000024490784002d41800e8601103011420b0a000a6540550320148d000143c04400d124241981c1364060722131440c44c403c126142c6940b542 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 399820143 1106 399819037 399819041
    0x4060806060f060309150c03011e1a0307020c120c040b193605041a04030813050a020a120b1e07113a0e03030901032706 53
    0x20260409185401c038086d4412081001c815a9035070520b424010001d40355041802c5000308079109200100048105a8500c1d1b0000b950305d0310382e41c886c40202d16140390422002d81088001890642030480060303610303030f0420212810301042440f841802103c400c45982002c030100d100305c0800881007810031084802001c81c0341d0b0307500c451090191900f4069090b03021012503640e9020802400401c0c03140d0b86607440542c62810450401d628000d281e81c0b0040c00c00c0300240c07907503403c040401c5020480701c1420f590140c40c1010b8103a4a0145480b4400304c2c070350541e0007202e04000950f2071030f00c03009420180b29582e0003e98260b114184111050800c080007407007a40305d4050140d0005610800e01000e000c0d420700003400310260410010141c3c03024503074178800d00c07040c54010140c6940c04000d558085d1828030303001402500d030b0038190742c2c0c000040c02c031250380c00703072180b405000d1181e15 = true := by decide +kernel

theorem cover : BRFrame.Cov 399640287 399820143 := by
  have h0 := BRFrame.cov_init 399640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 399640287 ≤ n) (h2 : n < 399820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
