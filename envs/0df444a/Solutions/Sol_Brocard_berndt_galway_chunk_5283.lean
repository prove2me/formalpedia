-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5283
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:21:22.393552+00:00
-- url     : https://prove2.me/submissions/c1d71804-3c5c-468d-83c7-cf464ecdae0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 950000000 ≤ n < 950179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 950001250 1250 950000000 950000017
    0x4050c010c1b0b0307032d050726060405060603061f260106090f1202041a06071a0901020403021f03021308010204150f121a06041d060904080d02 64
    0x9509001c1d40401004108100300c0d00141c02d24080841000217068140c4510001c404802c2203482111206644101e204402039020500032030b21480400c41450190040904c800c074410502c401580e526008080503460031100ca42c407460800002c00d4140c2407400403039024840c040d2000500e5a408003064040503c184501c104020b540c40c490341000005074101d01d1155414420320480e5494480000d2406100741c0000611100039401000a950100194541c1550648001c2450381205141e0441d07200c10310f0281d40c00900c00103000040110050300882208245880300815889001c0070301e08078003c501000307400c201078030340c50311144c899083c5203010303e0154980540340c444882c42031007400400c0d5200d803030542c1d00860148015004205058201c0c001341c41c00c5080b0341100c110051800a550014010107070f510f58202440e054200e0b181106000c3c0070b05001d40e80d654407480b0002c030789211b00d8100600ea9003000882c1c8140751640c5403602880d0000070244c2040302d041d60100080d07000c00c12 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 950002500 1250 950001250 950001263
    0x81324020c0f06070b3303012d05060301061715010e06180a020906072d03140c070312120e030a0c080d0609180201030c300603020402180a0b0304050c010c 68
    0x81c01c40700d1b086000c00d03004000c24000b459541104483e02818251455400f005204075841300c4036200015818546402643c800440400c00f503c424010038010b01680c1c1080c00c1002c5140c0d082400310000088180f2944c08a070041c0c2c0b4503aa844105040e41740707040d2201036000305410411000310103032140103508030700075101c0146040b0030400050f03001c0d031061070203c5481c20280b161040700f4504400c0e0030004003803403401c56003102031a1f400604031110000348541c1e40c8000b18110901d80381c104005000f80d0751164140104491080e40030b081d0701b829040c010445414020000e0002c0c401105541882d2346649504c5100e103401e558600e5141c2010781980c002996464000032107141720b00070807210510030498a286160780c4d000060988421441c0c2c0f074240180e041c04c00c000c02502026032001c1e02100f9050780171440c0a00b103424080e02c5264000395000d400803d0461900c20000c0c807a1b00c040b44e00b19000c1c0c442c141c0c0c8611611060004503805001768005000b001a40d50103403200d00c150760700c07925 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 950003750 1250 950002500 950002531
    0x8030d02130b0309070503120a050306010804030203091008090c060c0d0f210c0314040c0311060f03010f0f08060c1c020f070f030e120a081324020c0f06070b 69
    0x2440014190000c484d0701465a009100810003407c0600400e0780d8244440d16041c0750004a68000e04075102c00341031281004440c400050a0501c280700343c80010800404000000380c180d4402460765000791a5202c140c01140b03401c0e001d83c6800b1084490808080020700816486903200f542c0100c1a4041c07030051001d03c0180a00a010602011a10580c40c010024038202410700c004c0440d0f48440c2c00300c00c101c00303001c28031012a82c10212441204e50041079000c0940303440000c6401070107109045c0794400320101c0081070b03880b10501079000b55441c03046404d1565684542d1580d84e8130f025968071600c24400c0065060803060143c1240b4404240e0070003500d8403410218075030540c2c0c089102076410b0080408000100341d0710140b001c180c504200d8240030011410b42a6940b103064420008005a400144281402c1001034001e4014070940f101c0f01c2c61508440340e12003480f08500c0c40c05005000700114107441d803801d1004c42e4001c000180c00d207400d01c115517950030f44080000c1c00300010200c192 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 950005000 1250 950003750 950003759
    0xd111f111c15060c0b0f04080c15092b08060409240b041b030b0414090313091103010302130912031d0f030702090717012303060108030d0213 62
    0x403803603004224800c1e0005040000d5080c840121100d0340c00c01c00c1000780618048020071000030700030b5044065080604025101c620349a006441280e881d05c045002d49071800c1002068080c1d0701c2d1044070a8015982601201e0541451509141542c440c1040ca2210f03403422907440f035241c0c643d1104001d840021000803544560920105c0c900c50f50a88004040000c11101446c2c001e0601ca007106603001e001c240c00004410032002c111241d00b07000c0555500d181c02031a5141e400c00d13034075013000f244045003038200402090786035400b0001c1004a4800d4a800040d21502c605c039001076a4080802103080d41d08540c200045000c11050056901d074981100d0000319414560042c4170f40c00c6e680300001c0b234074034000c0074501c0201221045035644d04829001d040100022048800080d0b04031503198040d40c81003001c0e584e00e030702003d8565003131340c03003d002086040d0380c1840d030000340384841d25560240d0fa0030020590348110074080e10711a50004c0c450504000150b4001d400c07010083c02d808003031507840c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 950006250 1250 950005000 950005027
    0x209163006030602030601030e010b031002071511030f07020d020601060e130606051305030a05030403020411040b0d0212010e091510090f0204091b0e06070f080c0d111f11 75
    0xa94200762412a800406d00c501e41d82c1520840c0000050140203104038507007600003d4031400c0c9400328880031500043c42d981004040038404040b501c1042042007485c90114041455030000c6610000d101d480c00c0209500718000540c4800c1040b65500030407060b070800c0011130302d041000344410380000105908100c0000310340500e40c041c081550b01e5a490b4960b40c40c1c9005001601d6201c24001e400a03092400031400c040301311820f4a4056401055410070480e10341894807443c0d2211190038800718800045421a030003c1200b6983c00017450307804c3c0d80725403041d00748807010b44d0603100a82c0419106031100e00780941090b030140202c561035500c02e42e80c0d40d98000751540740c1410030000e6070000f000d01076000300c0e02c81c030100b41d41c40c66006c0c2080c0ca201d01020b4007070205015460b100d80c00210350001041591031a680c1c5040e40900015151304130940c246950320f0984806101185204000913200c10300040c421440c65201e0f09400741c803a044d02800740007420106102c10f0111401c0010b48890a03a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 950007500 1250 950006250 950006261
    0x50609150a112118010c15140c09010f12060801090b1e06060f18060a03050907080c030d0e03010b030a0308011806050f060a120e0a02091630 62
    0x41d103031034602105161000301424441d8440c8501504024070b8408402000c0181c00d80d4000395a40c0785003828560520f00686414040400c000c000080b413400d440b540440d11341000c0002c081c01c070312a00050726100c86008560140d1b50550740000d0282246040c080d02c100a041d240e95140100042c00a440e28442400e6640903503064030400c91100522044055a22025020341e10408400069090003000104207101b0200780500c148004649250107221400002202d000010103950f60f4085051003d001340c82c0c21110303482d150098600c0010b41c824086400300440d0070050152016100c107030401d42e582103c00c0740141d05990b0b90880345020348c50402150b00c02c41e0081c0c40b00c3c45a0340c5089101c04c0c01100003d03102210300d0901400700032030307100d86d40c0e05540902d04a40d01615015003034021a0001c292010308a102e0b402d000010b81000000f081c01d611041c000d503425080d95481c004081038040f4400030001c00075501c1d445003044020103980b40e407040f100c0f01c003204e81403038555250034003a5030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 950008750 1250 950007500 950007517
    0x120e0901060201020c060a153c090c02010c0801050d0f140a0209150904020112140c0a030606030908030109150b0a051809090d0e03070b070b0f06061305060915 70
    0x30344c009440d400c44c02d000c0003a1603000d00400000d1006800801c3c0170752910a8500c03800003907080f240500c4096440c0c0022020380307001e440e071076549825000307104400411100e21034021401c1c9810748103c21a44180560000d58140c0d40b50500d00e40d103050184401d0000150080d03a0401e0707003c0c51600001d0504030070b004075004800041000c0c942034010800c1035a005000c010765a43c100925040035250510303010341c080d030242400344c8020000c103041005001030380041d0b45128a018200701c550721003a0060304140b0155601001040e0b01c8c0e0720709804071580200050a00c4906200410403540c06801c041c402002c03032503805100175969600840c2a8010180d8000480d0b400314890200f2506100440900c0ea0101e60300a25420f021640f00c0c0c0300c1c084929030204100140d0000e00440d10304200e124010250381503070369640c02807801c04001ba1517040e14256003110a110218000b0314004084e54644c10700c3c036806240041c5400100000c0c3d40c4000d09640d00484d550703840c11181c0c054803000c1c2440b43d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 950010000 1250 950008750 950008753
    0x20d09020406080316080f0705011b260402060d0618020306130c08270706020102040e0f01060203041215060915060f0207140a173007120e09010602 65
    0xa040520400040d20415003100420f9842440542142c11210401c09000760f041922140c0d02e640700c1d14482c03c207115070200074065600b80801d0008080b2829504050340c1d0b1030b640da20190024034012501c0d5141d8000382c0c1150283c109010501501d0030100410150103114800034100766600c0b4851081c481040c03501200c65030100810100307080041000c2c2c2e0044007082c0c00c020112594002070a245c2014080c90b140120502802c903190b01c11500305d40a01d03001c4001c485030329a40381c1009004c2c0d44a030040b01041c130031000106503890b030021402816544203402030340c00d00382019662402c102144001307540b0243c11100c402041280d921a080242c10582000b24401c1034001078680039405c203920000070000c000700c4d001080d650210740403059801c2b03100840000d0301150005030703062074590800003409148241d010940d80d400500b044454544801d040c9445200103002040b00000c41c1d000542d281003000104002400b41e02e07241558000380c1041d06101d10490045042c1c900240c1114016 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 950011250 1250 950010000 950010011
    0xb0c2409151801151503060e150a1a071a0f0c21041101020c0f0a09020a17150a1a070305030603010e0d050c0c06030118090201050706141815060f030106030204020d 72
    0x240d117110101144032040b0341c20148082468002c0c442113410340280328242a8000640c000c0b281e50382e206070030b00189041c840203113030101c5020010100f5442100d084500900122010303407400d480c081402d2050100c030310407004a40d01c98800c0d00d0b4a9204080b40420428213101d8040034540030000d05020314000c40705180c00c40b500000281c0360100e0350b15964818030685085074110350310f0081ea80c0a0380c415110160300c5090002080d83c4210b03c46000003141c1c64183c040160007156103a54500301c00e002c65459010540d0390404018002600c404c1241501d010085000404c3c0120000c0d90009400b0300001a0140403402003800c0005178010800040c01c002109007035250308005002040c4000c542080c07940d45411100302d554625000da800203142c0b508607200940e030158058500803508241c1c01c1c825000200d424191903007040b035940750100301c01004d0113180e4a0014880000f1180e8505415040e203a441c1000342154010742c00c680e0564940d6804001a10355002800d0400f88008000c0341 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 950012500 1250 950011250 950011259
    0x160c080c0405090303060a051210050a051b03070c1e08070302061005030f0709051b0c03130e04121d130f051308071203060b0c240915180115 62
    0x240c540281c0f5102e0160301c10b20501c40a96034901d0303800c0840d5822030b450108c0580140585040074440c1074581c0d031a030f107854108080c00805401492141b00703880412005400d22781d103084114002a200c860005000f62800400110300144202180c002e140040d541d00a00366a000e006600c104012001600a1018842102c02003420348010340000c9002d400514070184226688203482e21a4000007502c45000c12040c1c03500415a95850307801d50b0020f5651203050b10b031103a40741d1250320110354040712404001194661211494000c80c0c0c009250030845034624422140340124180413602001003249500403a44d840f008603051101131980420790050303c01d0911704482004020580450302c944094002031000000c5589a590100d2202daa0294032501100100107139000303100c1000d0300087d8440c00d41800900b2198440340134982c0d0b030062042207008101c080b0181d48850003603022007110201e0000c480491648038040031078201200c0c0f50701c11072070300b50b13074828180c2c2e0f0241c00c1c060006d20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 950013750 1250 950012500 950012509
    0x601030f0206074b030507080405030a1a070c03080a3c050c0c030304140a060f050402101d04021b0d1808011a010f0e0a03052505090a02160c080c 64
    0x9041c055010143e1404c501c15407001080d03071914401000c010002074507404000340c070005e482c09480d0140c1101c035078009505d00300402c0c424150324142110450b50000d4a114802c050540b4015450340d44d14803035031200503245000d028a186102c46204206400090b07d01071101100b020300611002e510214031415800c1044a0340903140c0c0c07441110030407440b440004000b084030740040e885030400741c9220444081c581002051200202500c1c109205003000402c0c5400c00c902a5000311000011003c3c030510039111031807004025102d8808854000d40e6a203490340c0907003400080b40c01052403100700000c0007410000560540f5021881c034450720011800d4002c801d901a05001c00200030381c60b000040b0712498a10f40e408241004041c030700460300c0d584141040c01c1c0c200405003c56415548901d019270719104844021440020030700d00d262042e0300f15844210031900c01070004851526440c03441c501a501158401101210300246240010744194030003000b480280c0c00341c02c04071007020420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 950015000 1250 950013750 950013833
    0x7232505090c03070f09030f030f0e120705011209061e230a0504030c0b240402090a05060d0207150501211a0907090f060305070b0c0601030f020607 65
    0x29024849980420511060350003c481e04885607052038826a4442c4400312021403040d08001c3c06814604020000c00d81c100340382090144594880010424052040c02094603c00c0400c45c00e651081008000d21350190814030044000740d00080307010007054507194252005c610410319050303500000d202003101c587c40350700b806c035008290301c1c12482d41141c2c88221849000e4003001e0354035a92030220301018003410300250b1107a80f005000e1039502d006100e0141800d5810543c1107e48084c10f48513420303140a00c00ca4010301380080c606003d10b070404050204541080e000c0540055080080c840440c800e41c44000700700351000404542c0350306000300000101c103141c41d100910000b41051600244200c21005015030440c02c003100701d5035030b0034441c41c03805007941d005901d035500c2c110501e175840071079070820815680544125a603043da1000303000200e20850a440c2400e40108005000080351409541c625a00090505040c0368040c0ca6084a41d0200f0101000c407004404407a1006019800344c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 950016250 1250 950015000 950015009
    0x2150c011820211504060b1503061518030718060609050906060313060c02160f03080a120b040c081806061e060d06030c06180b072325 59
    0xa240d03000200b200440c080341d5019050204055555100d0010481c04204122400251240e622014286828541c0041581c0b1000c0c40c00703035140f5500c1205c0c0d400410112805000003800025141e000c00e41070b011290000c4142190003d4a000a10714075a02088000b000c2e1615040030f0341050702d000084800c80307003541c4c0954140000d02900b00180e99428005641c042019101141c0c0e0f6519408010b02d40302e025000200740d14640000147c000780d0005400004403444000e00403810f8640c00d0100094480b03100080003007800f08413108a0500c5801220700c0403455000208002d000707400054142ca050519580c0020085000c01c41c060745d069585804004881c0058403031400c0503008202e044034011a00e00c0f000185207813090141e11044111000341e64030341820030105450340f800c9224140c3c11b03c541000546c81c00006407100e00100345190494240000c01c518010140d5215440c140200302c0030100e110300d10401070f1005400f4040b8400521501003043d03140d51710780203c80c0c21003000d60071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 950017500 1250 950016250 950016293
    0x39041b0206090d0e030c011b02040e0309121204050d050a05010906020d0f0c0f0f17091024030b2d061c0b1906080a0609050c0906060702150c0118 64
    0x7000f0303401d84002c00c1404040c0740070700c0c0000310a00b80d8424402300780c011040c0203422500c2d200c108540090302101400c40440c0489a103004c030340206091681d100d101140c420f8031a40c0030001003085103030500603448600e21038004da508803215a1156800c40d00790b00015220740f50000307000c1e200700350310b4401c40f0321107000100e040004903191100242144c4003e00031a0170b0141000d040074015000e0b81d40b003090303140300341c42d01505403074480c607415102c2030141c0e04490113a0411103207084940300c541d20703a0b00e201168048407802d42d295071036a2611640281204400750f5480c01000102107012021440704619140403585e241030141c140840754030038802d004440700c1281119000141407040701d0350882504843c00030301c4184004004000c0c419075000381441d2007081106800c1026a40118000301d0050302940c5a550200d802d1104410040b070b6101da00c504104800030040c070302019010b141102c459411820208898009800c503401e14400c404029104030158007001140b100c0d0580a1041b043d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 950018750 1250 950017500 950017517
    0x170411010e220e071a0c2b0f142703120f0c01110a0210110a0909050a150f03021f0912080c0304030b0939041b0206090d 53
    0xc1d480310011840002c08002d080d11540400b8011500f000068068542c1c2c0039a036603e02984801c0110725481180000b5441c026160060030041445488102005491134020b200003d00d06044408e0b110300806c21050104005000001000d0311002d400010a200403034012903019208006401881105861003a8003044481c00b0342082c03c01580c0314682e94520103a00c42c0c800410160142c4100588074404200c00700d00034070069030003e400c5090302686074081041701101c0c00307061524814510035101003010f40c40104500f40072940695488000000e001580d410340030485106006154803566440b0940c40c414006e51401100340e05d01d080200303640f0081600340d401c019202d03120610940c000310907903502c51824081c4400880b540d40300c0840540ea52180c6910b0245d40140050b01c064500e44254030440d4030407403c80944815000d5500c11803920201448007000084105103102c0343c0258940b400f803044100d1040b10742070007030403c0c0c010b4003081c41c21450161034100d42d41d100004122918 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 950020000 1250 950018750 950018779
    0x18060f04020319140d0503010e0106030902010804110607060507050309010c031a010e0111150412030c020703081b011a040e06010b030c0703110604050a03090501050406120c170411010e 81
    0x10f20600350f041c5403600d9458410190500110005550b4103140f001c2c021074000c0e030340c490703030210045044e01c107503040c0c0d0364050b601e03280201c00303c880d14140280818491008a0041481c850303206283e0400200710a20700035480c8d035048140c802c00d554000100d0750110500071088000c8c0a15400d06515140c00c1140401c031030b0002c0b00300050901e640d818000d9259480380e0603403040c04010081c408060840e0100030348070300341420a81040b28162800c2ca030f02240c0748040740c424010440040780685c010301c1c845040d03031204907540d80400b144809a808981500d421000203009200031003050000e0503507580004070a0005403a104640041150404c0c4011700c40119480260394010300c1405459440d002c0758a030644c0c1050300c400e0048024420348040104001c800960315842d184603544070021035030755200548039405a4000c0c2e10105440c850280c01001480d4084039903804145401100d41a070380d1295100184241d13000c1d034800840c165600c000b56040340038003070004402c1d00c4100c038103642c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 950021250 1250 950020000 950020003
    0x10513020a0302210313060905180601030b19030b040204110403020604090b131b0f020f12131215180b0a090204200a030b030f03190504030b18060f040203 68
    0xc1d404002e00c90300002c88080c040d814850084076841401008480e0345409405900d890f9280034811400090f07901c00b00492282808850305c84e038400907440024682d103e030001034014044e12100385800400050081018145106640d0000c40c060002c2ba51241050b0042c407041d1015640b045005400c03c100420058545408070340455640792800a210074131400014402c00054444064803424008221341030b1481c1c0140070041101512030b44c078103109003001640c5402c4504001c01541c1c02210010700b80340e1007040202a41c8200355808119262118900c404072810520103881c0044500089190703d4820f204d841c51411806215202024590351540d08407074000f058520140d4982c0c6a500454889800082408429950b8001070300e0519844400030342001031414000307402d10a40c00542e00b000308000303556421070b0000d140b03000b51b1380001c459400d881b0413191082101c1000700002095543c8940381c0107a1007000301080140380d45034840e1400c00301a00c5085c00306146018030005940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 950022500 1250 950021250 950021269
    0x6090905190606030503181905030c06090a1d010f080313050d0503090d030305071b0b1b0d06080c04060503300c0307060603050d050a020706030b06040b0a0f0201051302 74
    0x1a0051141e4103400c2500d04030000d0200380e03000410364400411006201016094a00045581501d038050303004850304e55564145214811103030076412055902e0064108607006000640c00941007051140d940c0b001118000d0303e6001d2503420309080380c014007250441e88145802400410011410441d400c0350031800c0041c0c9204607807096485084030020000d0030300544000701c4000b07099128840e29410060064141124803c0010b09100520380c501c96202c071000c6409034100d00001c28590b00d2000b0001c0140c0e0014044401e06804c2c041301401241a01540c0041c0c40c04c50b02034103000c400d020a2005495260708001d20a4119454952079003540849400000d4075401c5000004140b0140720030f424441d91200e03075414000007a012051000c00e07089441140e11404c1121080d187c1c5580c2142c0e03070300070345102c60010380114004012003403081d0451010358000801080c07a2540c0c1d44100c41c015800403130399101049004406180483d0207100d521350100c00c601910310b8140440d400980b8110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 950023750 1250 950022500 950022523
    0xf0d02030a121d0106290f0a020129090a061401030b010306080a0b0609130530030103060f050907080a0b0c0706060e18011a010f020a020415050406090905 68
    0x80d182e0410110001c460700801e01e800c1203811203d079100358015005010b44814081c8405408406c05002c0f03003400c6d40e40302c00c40700c007001202080c00c01c03000309415131007a07014411403800c541d00c88580d06402c2042c0f1040c0c0b08541302e51412003100c0001ea03418000352000007046e1034021443c1420801c030714400010035090045003480c00082c00782041d401078002300920b4008507158411551190108a13a238091640110001c031801c0c0c00595846a5640c5019004040280300d600f00401c0c200d542c0415034100210386202c0d10280480051403c903860b01500241e006607007071074482d40c4402566000744500b603000118800900201e60812258036a51100000d0040100064000041608041c8010b0b50705590340480140581d90f581c40040000072019a91b540003000304000200c1060814400c0403062000d0741504020400f40000664903c02042034820560088000090040e5a41d12401c402c1030300c4400880c42c0c2a080c00c0600003128195002035401510b419111800300307000181c00401a03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 950025000 1250 950023750 950023757
    0xd050a08010e090a0605240301020a050702010c050705090a0c0f090602060105060c10021801080108070f030b0903090d03030f0b0603010803030c0c0a0f061b05090901060323010906080f0d02030a 85
    0x10344400702c080f407504c0c07038110028184da403800b018854580040c54500f59902207c0c09041c920340c003c8001c1500300d1045028003000b02c1d40c100710f108010350085a0141000e0b001700146c6401e15650000300c1e91403d000c43e1280e48041e40c1340e01241095401c4903403205801007034030b0003c1c5810704003500030795030b20418050503201c0c074000700c0c42c00c2e030a20040161500c02e01c1654020354a0b00310851000d55032001150440703011540040c00421080000101441164801aa100e0f401482d5031519090020003406501d55400300f0807003400c3c151109035085514600c40d0350001244440b0f10400b80032942d001313500d0307807084800708010441c459001090325000700c0f809000a6a40302c1c030004882c585040e0042c0100440c21140e441401d00c1150380c002034003044600100402d4060780a012100ea100e44030005512540350001030240324030030761000041030040011407044180d080001c5c0f28248090b840206c195485210038016010203120840980704108000c0c4468024440041d4030703409000d0945003007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 950026250 1250 950025000 950025029
    0x20702150c01020412080a0f020616031a0d1a060d0209041202070e010b030106140901050a0e0303042d0501033617090405310f0812090d050a0801 64
    0x1e81080d070440e401801e9071414071142c0c030a1890a1030b1160851950b04010a00ca968002907440c00401c10030301c80c290b820341807100202d4040f0f080d0002c1c00b140140f203001102100c1c0115480e00c0312941e407120b0300e001c0c0030000300750b0746061009161460020701c0d0500444810b201e0b0801a200e000340c941d0483c0c0d20440c9210300514070b01d8101d00e03107240c0c1c0d0b00c000e5441810704000108516000010b60689900743c1c1c40044688829030342c2d100c10312a05164a000880170070030303100600d01c65101b2900201005080c2c074a03096a800b400c0c100d40c494403002e040d452076402d081003003245000c07019000a101c00e08087c002019086002c1405d0000c444588c100140c990001620009041c0900c08001e13034070103808112401c2c00a030794078080e0400340c2c0e0a40034a01c1d08003c034003600710000e0307201d64442060500400304c00c0601e00c0140c50300038551086840940d41c0941d040003483c20300c050280c40c0700d4121240d103d031070403480141c40c101c0b4550300d91090003420003002298a0384030034000d065521000b140d1a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 950027500 1250 950026250 950026267
    0x40b0a0503130204020a0809070f0b0f0c12270405060d02060304050703061103041208041518020409240605030601050105301e010803040e0c0f0301060903140102070215 74
    0x14500c2c80004003e510602c001161851180c0241009001c2c5c80054111600f01c2c3c0c47d80765034a075140c0c403070040c00714941c0180413200300744c06108005e00580890200b514011001c05215543e9500100010450b002c1c048000e07040c10b01060100a8804504450500240c106600440c0015a42c101c2c00782c010303180000014103100c400c21082c4011a0b00c014200864080000c3e040180c1e0809c1da42250f0b500380150f04074000380e00c22001c0c40d00a03500700d03404071041c2c0309120300c0c0002411404a0fa0401c1c007101e122400140ea254465030250500035602c070f0004003254842c402c070003901d40c020010110f1400c4002e02040d180010307a203054410a09080b42e4030070341c0f480c0003005039044036001070f95104000341510ba407200340200c160140e69416020406800400c004100c0d1280901030b41010f603000f40070802a400a1550701c0750822913820314603150542c03003400d8055a501c03d80102021032010041001001480307110303442500c4100b4004c43c01c12055500185500c8903909030b80c01c1070300002c42c0b0b049 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 950028750 1250 950027500 950027521
    0x3050d0f0212070620130312170a0506030a0807060603030206060913030f03180c0501030b120a0609030e0d050c1c122708010902030d032007030203040e070c1106040b0a0503 76
    0x30101c01d02c80c5d01c0710b6180c00c0e54484d1b00d14801018001212150860ba10101206000b1200c6548884080c3c03944000c540d50707007c1d0b10001300310040090758903104101e103100100c1e000c3c0000300240c6004150108109046080103450a800a02103a000340501c81c108010700c6000003203144031540c1442c001003024015070702100600175402c0507580d6440c642c01000e0400101869002c102e0f102070301c1c240030000052081003051290a024100f071504881001c0000401c0e83d400044428480d003490880350301e10720042580c429020300219407030341c440c2c5078101c0185010342c40c4c0580004600d09041c181412b0341d8480c2d40c070900b00d0b1300003020300040c1840034a802d00540c0c0514181201648030b410ba4980d6038038014043c00c03d286c02a4042d004540b028080c1c00e10a004942100c84070080194400c0c0d410007031010300382c3c1310780000e5045001c01d100101d1600a94a1458020b06081da15418150074900b400c1a0031201d109007140b01394030412041050345010000d46a03494001c0c00d05603240d688501d07009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 950030000 1250 950028750 950028791
    0x230a2106060b03010909050c0105040b0d0216120c03090807050d060b0424030620091e18190e0d031a0607050102030106320c03070501050103050d0f02120706 69
    0xc0b003042c00400082100180b0303503c9403080074090411521007801d1074005590030b02c12405442e052000030001c0c4a26002c1e903400a050303100340207400c88000d201c5c03520b40306e0801020000c0d40d000600d00b0402c01040c16400810200a02404000340405501d414002500d800980d440205880d4a640d4000344940c0e80c0d502c41d602e8404650b030421859240070b510b140c01d03054203000443d5924030f403403940035070342c10b0040081040068030440646800d20600c100082c255040e22400c2060703c000d0650f402d544c40d201c1808100910344100ba8900d0709189014402881ca03076104422114078114900c0210100041d003104000524100050080d100d0420b91158004540e031035504240001400c0e0104841540214101e842c03540d521070034501980c1040c1000d109070030321610300540100c03e90006090b0480188200c0c9030300401c90f40341240c599151800d5070802d0707000366050b801c00009540e44c20f42004840703200c46103d102074140c0500c1008050400e014028010708802d43c2e80320562542004030040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 950031250 1250 950030000 950030009
    0xe0108030a1d031005011d0405032d12070915081b0d050f01081e06060f0f0d030314060f0d080c012009130902030a02190f230a210606 59
    0x9440000c2d0110303507008017800007803050350004000c8503000d500c1c0742c000c2c8007030074001e5601c100a90b2525501000000d8003140f02c601b02c0008013400ca22030116414508005c0c800c00d007644045d07008610708490003800d400c3d2141d1104003c0b0044203050f405040d40040c085501c100a1103110a103c8910000e43c12903004800803103030600d16000034000c420750303801e40c1c0b03e0407180e84104584034480512000d013170715684500e200e2060360024005c620b05203080594028466009844201200140d400186000c1011002600480c0c0e81d034140d0030782119501c1c80c00c0d9101c40305403080704419090f0341c081100e241903036a010b0908103011450300d00006080d04040311003403200e007041440441e81081d0129550042c144548181d01c584501c0800d140030b8041c02c20b009400801924041c0d4854090082040d040450750040001c8020082804413458010002a010340c20208031544c8541002a4041e035680708901d1040c480c0365030070003184c00380004084540d200398020843c00311a034a0180082d2003140c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 950032500 1250 950031250 950031253
    0x15051e100b0a030b0f030d020714042702041409030a030906151508090718020703020c19030b1302030c0d112115070f0f0c0512090a0e0108030a1d03 65
    0x50642c00309034580c100c1c036007004046030560340041245041540d10305000d14010056000024100b0100d60801018040315001610200300c11410900141400f40058141894141307004030b41801e40c10f00f031042a00d02c8034418040411410710440d0a5a6801303090b1250041544034900701d410095150000c107021303061544410196a2a850b0386020300708040d45410004014000240c003800303000a2070800c0310b4840b4003035191849004c06c400065400103400343e0a41c03007202d10040c0e42c0d450704042410700e107110a20b500461402d501d00081040d40c094010b00808821054000240ea0040741460606000319070443c4072404516011208448148400d9480802800160b00740d42e01c160342c04410140490940d540c00c0d00c0e10079000c00c4c0180540342000015048124000194080e9600c4100706915080800000f80aa0745180c603007803540c2452010000041559941070800c01e40c40000382100303025203001c941c10200c40503621b008041d00c180c00c01800703031288030719a02907085c46841d111000c0e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 950033750 1250 950032500 950032507
    0xc0c090903020f01020702060d0b18010303030606110a0b0a02070c090603050c1825050d05090d0f09060f0507080d0f09050f16091104080a05070315051e100b 69
    0x46090004148200003070300540990a075241c1001d0041c070803280340a600a00660030700c916580100007d2450504e007681102c0d20f001d24030071458004680f1402584a542d01040050801e1001426103c4040094502c2d600c181d03221070004121250507540064400302c01070300e4a036242485100c14129600064440d45000300200a00c580441c1410f450801070b248250725614111600c91400f000b1220b120320061680700b480b01c10b050307094000348490a640381c06420010160340c81c5044034401ea6107082c280d4410302002d00020b4218060030840d2040d0b04055008518160014029032280020002040000a042020090000c09035002c260700f11400700000c0c6008041e0b01c0082c41c2c8103005039041e110f5074038000d800060004d00d500320701004180c1183d03038518051020000d0a21000e85608010f004d10000c140340701c041100020316406170008160103840c500742175086500704020844004c1c1003501300040704102c039604901a60341d40800e40300940e40c0303601900001c035243e04851208103000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 950035000 1250 950033750 950033759
    0x4060203041406031504050603030c1b03160e07030504240f1505010f080a061505070b0718120302012012010b18060703031814010c020c0604150c0c 65
    0xe07009440d100981840061500c50821809000450748029401c0600b02008418101070704560780001001e0112424042141d40340c50410802d0400e01d80c3c0c09000c1c0c10721036420301c0c081001c440540d02c07004018410600b422405203055100800b400149522140481d04000104100440d0410504805240b141807030124002506942107035805550030f002e000c0341a070080440c2c2404459050b1200a00158400c00c166000070008190003482650b903900003401c07001081100540070400d9503240d5485101e1303e00351190b9803002c3e15190411101510301f40108251141d09020b41d640030744103038a03412a618089015102c1c141c402c1c003101c4c81801c2c1e0f2640c58074003200039106045149100e0401aa2204015036580c0900c0c0420700c44040070340040203042c1001402014464028a8003084e4172403c50903000c2000b240807030403201c4003900303c452644c11030288185444520148007070003820407900002801030155010316a1329090300c1080d5100d00340078544000205070b00c1503030341e4880c9658 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 950036250 1250 950035000 950035003
    0x2090901290a0f08090705061c06083309150405030c070807060e01020109080a140d02041404050708100e0907080f0c090705040317030c0c0a060504170708040902090d08040602 77
    0xb50f441440109580740c001c1403440002154401c20b03110003504e000d04004200c038032618282440700780110410303510f040c082a2518140940103061109800700c4452200032000e00152800b0b21619440841c403034401d0158407407000c62003d48a51000341a040c1c0c540b51410180e046110b00c4007158545d00c91210700186186001c141401100e00680340d040800c80004016820703206c8203103004003500030420814101900503a400407000140d220b9003420414106040340c00c0f40d115411000001c00910184d010a1929002d8560702021070b180403e02c1d404d22a049100382ca106001e0040346000132400102603550410070040203000d03000882e480d0044404041d602c542000c00c4090013074000b4000900c010b40503508132011654010004208a4900b801951980c0c0002e4500e0100b084104001840e02004114001204d0701503480002c0c1030806103020b45590709182c203100c140803014881c1d0004a0180d605960880c0c029160150351101000002140300c81401d034001e298090220300811040d60 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 950037500 1250 950036250 950036267
    0x1504260d0b060d0203041b0611031c060b040618120f0b0705090d0b060a150921020915090a0b131a1203041d100b0c07030c08011e02090901290a 63
    0x703001fa00ca211090b111030044070b0a144e146040045a8010055800b17845030fa44040d081c901040c0e0b01c001416511911180e20540c02607011500142034003010440880c03400341d10700700600c14407222a4403120f45a4031001c00c1154824017034007600e0f0000002c0c0001e8003d800b01c407802000108038400e00c1d0130524042c4e40c400e00a566040c0204030a22003c100962015018084c8030051307101d018806142842c100c500c0c2c42c010000350132a180c9240300c4030041c0c881095041c003400800307640780c81c4d92508000b4000989001003070040e86a0400440011a4403003103d204001c2080007000b0a0340e0810140394074000403100138041d0030070700d13408a81c2141140480548191128112800a400b80003040403c60900030b6560b241003d00b00002008280740b8407005041c1724811100307440c81a541c90300c4448100350f80380e010300c645035142d540c05423001104640c00c050040c030143c411814640c8007004100509014020308550031400070383d0788054100c040350032003075242d04203032140e8450103100b00802111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 950038750 1250 950037500 950037533
    0xe060a0c14060609040f0c090c05090f0a06050915070c06020a05060a2d1b030b0a05010c110f0a09020a18050f0d0318081504260d0b060d020304 63
    0xc101c5000e82941c2004a0014040d000040c4500c849445035203540040e0189540d085039869803907800015100380030302070039510321b1880c0c8840d5140d0340d211007842840c1031a018054840c1302107400070f0020507040f0054410801007602c400c04c0c01d6202a98075a42845045406010950a090f0010300c8a900040b81d0007064810020b451a80c3c58000c1044181c0b00c40704039088845c10120b080d404c003049920300c40c101c41c0424020201e000e07110003911000c2d1900030780000002a44403101c0c41902e00701424100c0040c5002e1805240c40c005a460342800b00403d19200d900c240c0926409000f0b40d5210040c000251010308000c555501d00c004002e0201055001003640440804000040780d1078003098001d85804080c00e2000c092400f55001c403515038214802c003e03408061180480c058004005030f804494420701d01e00528207090070541c149200b07040e1200010316410340c100b41d480d80c20009480e214065808041564000f040c0080e003140240e003078080b4603d201100300018424500d03201103401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 950040000 1250 950038750 950038763
    0x5030304181d0307030806040204030209100e10080a0f031e03020910050c061305010608070e09071403030417010f05040609030e0103050c091909020c060108010516080103120e060a0c 80
    0x101c40c480100d82c1c0d05025042041140c1042c0080c00100c2e01416046d81d00c82c1d80217000518290302c130b50021780c00f01e10a641c210a200c1d0056018010740034500c980d540c02c84801054038031900d14107000b01341d450303420711002030003d0034852460003018055500e85511507070841c00b62081d1005054018002d411600700c0384c1c401e95460f02510384660064044800740800203015201580c1d86850007031186031681e600311100d640c0c4031000900d916090000c000942061800800b890400f0081d4601d00104c80d00075081000796900c01c5500b41d94000304560441d0004000d42c0a03002c4289001da00421400c100a8112800d18041104100300d907804001041e2103a111351120709201c5c001141103da0456206002c0101001410360510f4212100c1d841440d034000c2e8000b8041e00c0e403008400fa40c0055010381101d074000c20040c4079a070828001c0360342c8a58285403982c20810340354001843c0c042c040c40017804d01c1ca80c591094070b629110700314a070540040504002c1e0b4820803202c00a0915800c00d0f005c0c0d50b00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 950041250 1250 950040000 950040011
    0x801110310090605060d150504050108150a0b0315100510030207052406060904090501020703020a0c06020c090c18120c0406090608030a0305090a050715090522150503030418 76
    0x4542c2c1407080c001502c2000d8001400c00d0124544075004054109040301d00d40d4682900080031f51f15402118080c2c0b4001015208403181d04018081510001d820090558100b07120803a140e200026000c404543e03049502d00c05032580d2914480c180000e400550708101c00030300542c9444c0d0103400400025102c1c0b4116030303507c008840c0a000034815900d07030380e1718044a4004111240361000240c0031200000b0000203071000580c1e0f07400d00f203030b000a5040300940c02c201014414403010441480061140340060079100c40c0c0400040c12071800207101c4400410041520000d0b005613052106441c03201811003500c01120320440303580c901060b100244913500f00700c00800c5810340c41c018441103c100070010750800582d90004d601804001f814911588107040e03118001c24001c00c074800003000d00d070803441400e88070b200000340200f045400540c001d8002603040780c00740510394070351504c2111201001078900d24044403800100400e51042d6418400800c0200d83c1d40c02507078070300c0002003401c2c104100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 950042500 1250 950041250 950041259
    0x50a0b0315040c03140f01030209010e0415020a0e120114090a15020a02151e13031d190627030b15010504150503240f0105090402040801110310 63
    0x85100c22951032a240030880d501c00c07503034141500021020320b01400c0c0030a40da4101c2003854440e503822034207400c640e4004e40040081d400c000c581d1a0140402c080181d07403629041c0c03038024010803002c0210a00542c00108610218881c1a21150303030030700140085c420130fa94680042c0a0208202182540c0d0180c9003c118207680024a80d4800c070342c0980031040f421651210f07a40250072101e10f5a0640c09100008009445034000451007508038907403002202c002c1b00903440b001d2078010003412160b03003410b9555012940200c00c40718003c13501c0000c5141c0540400106c2c4203070503640703118001c00598240210325190001200340c425a0f000e0086203d40c8501c101804014801d8400601000d460b0301c081000608901d6039402c1da0941070405c0b0b03241590700d0985075180c4048508500004401005010b49030a8555030b403508801180c5916100302c0003200094501110480214144400098440e46a03112901a24000c0807140004c004901d5000200d80255100b1691182c100e0340c170810105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 950043750 1250 950042500 950042519
    0x80d1a0907140d020405040524010207060c0f030c051b09130c15020a0c0303110c01032d0e06040b1b0c030412081201060518120d2a030504050a 63
    0x600c5195960b403100d0794514119040320b0107030310074907550041507003c0001280c2d50715680a4680941c400541c0401000000f01002a4040d05003014504640080404118165000355035030030701a000f06c11802005034910b010750b403820301c80e51300501c02c0c0603d020416508003509049502c206007960440d03450f40d6040c0341b601101500030001002c0d1000e071202400480b820034881c0442c54202c0c0100c03400072481d80c590030015411a0701c220009540340051141c805c5c400e1001c3d060900c800c0c28140000300040511001d030203080c3d60f0b032a01f0108900c2c40301050211a402c1816009560800d5503101e05260800c84000a412580c40e9000b441c2441401012000b010032911908840c5016500f01414001d9800c12a15503a03001d446a03c414010010f500c610b03050b406000344080d84480c1d0340d620060504241024003440d0261040b0303102c603003c080b603d8010804080003500c0d403602070001c19081c003c41b040701240744450001c659403200c1910415400100400130b481c400c03104561025561070310360 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 950045000 1250 950043750 950043769
    0xf12060420030c0315100305070305010504150218040e1002070c081c090e130506070f0e0301020a020a020d0201051209100b0d031b06110a0e0a170d05090d080d1a 71
    0x26415905c140200241c2405c2c1da45041d030400701a29030740ca017056403a1101480e02c1025001070f100c60750355030305000c100300c3c0e41001290b40d02c170604000d6007000f00800d4120004181c1d092102e00441d140d020740c58102c4010701090164028010085407180d00314144401c01d103085009400181c401c1c1e001c10901404902640010351000f40d6402c3c41090a02c00e902c8240ca6015104440003000400103000280f42800030701d2185466a90305010007200c0e1000500703015041c003d0380e0103a44100302c080ea4032a07001c1034244003d50161409294500548012580c520402072401500c0d0f02440501014500120710480450b070050002e0081040d103e0400c08103108042e40200400c14180c6d250545001d4180092501d1340684000103421154044c80d00c3d140d44910000000240c036008160b90354135080784200d01074210a1100040ca000700000c180d9159031541150041c0100840c0011709075880c40c4400d1099644903105e561100038221030400030f481c080d8421200c08160f114842c5c15401d06a120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 950046250 1250 950045000 950045023
    0xc05070c0b0903032a0721080c160e010e280e0c060a03150e0f0c0f0d0c0509130506030d0318020406060804140304060c020f1206042003 60
    0x180446841c080e2182001e0b0302015180c1e401d03000038043d80155208032901c1503000f009035400e80c0d039503840c2d240c003440c00c1c50002d800c0000348414501c3c0701005000d5441400c40f903207510850150b552031000c0419407a000e6094100c000441145401203a0445d0341c2c401709048811854414055031209520090070b00d50340310021040000311005000300a02c182c0000030301140b010142c40c0141207401c08210a64085440000801e4640e010400901840352028009110090003c441800d040071600c002000241c952a806403000c1041701080321000215041080c0c516020049044e0000016255410201e841c42c4144822840c400000e01103018003480b035000200a002030280006040d0300800401c4007200f81600c5181600c00140c886100b0030700903118030340740d00e065480c0918000c280300d101c40c0c2141825801c00c0c002000107941140480480d40e0f8122810980d010002c00800e110350f100300004c0909100c0d00c000d2006001410111002da151103280c080182001c00d020b043d9507800c2141c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 950047500 1250 950046250 950046263
    0x100606020a0f02010c0218270d030c110601090501140d030206070f0c08032406040806010e040231060b040f0b0304060b0d14060117030319022203060c0507 68
    0x1e0414071402e007066205041c04c3c00d510003140c001c5101e80240b200201000e0324580c0a01c0380e020300021500a11002c50351880740399000c140042616544075005040078191269481c0e0030300e5001d0007410900d40c0540e41240c06540c0d48104e075201500d8284100c502000d0140c02d14005424001e07580843c00c0e030136800030301c0d003a10703080c8045482010f080840004c210b0040041d20000d0382d41c5000394041c441d0302078070b41c01c030801400b403155624019105262080700f08020412012030003285aa044501d44810380c44941e4985c00420094008448443c01c48064003020700302a1000002d284101d1500d1901044241e4035100b181010f803096009480c0c000d00100c104025860386100203690280c401d843c013249120030030000c038500403110f107002c40ea844442d41d0183d440303402c1080380500404003d11500c080c0800c84082540300d00c000781c6060395101d54031424000c40b500300c0d011200a801480c060f0000860040c42100108100d8002111058242900019030910400540d00d1b502d41228 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 950048750 1250 950047500 950047513
    0xe010507030806010210140105090a05040203120d110c01140c13051c06020403150e150408030a06081b090c03060a050d030e06030709180c0516030306030b090a0510060602 75
    0x3201620b41d240014000d0781140b1540313031035030300603500d81c000d51400340078450041445505050401061402c02000f80105034a00405c000150f600041c020003142d0004030040d60700e5143c04002c001500b03009da1000800e90340025202d0380540c0550080e2220801170f80c0d5070742c09864803020721040344070340c0c4043c0c01da50014290030300261a04961084116010701204006030040c3e0b45c850341a43c100342d0050314040c43c0b5000030850048180030308559601c1940290142c044150309810b503540001d030018200902c0440000c00b01030050380800040e250b07004c1100c440c0c03a4001d40404441008400e4a8000c194020104000924003801d13240144001070014824908007024403043c40c0180201b50200030758444001c50a441d414000c41c0661403503680c0c250071508100061303942c111441500b68a03580703004a03151780164400142c40c40d900364400102000407441c00c044000d09466000903000c003c1c1c000503c8418040040d481011038401c0341510102030341c444002c400c0f80c0d10342c4103080141e003100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 950050000 1250 950048750 950048753
    0x901050f01020f0d030606200a03030c050909040b071715060a2102131d0a050612011803080106090f0909141009140d12020711090403031b0e010507 65
    0x2021200d204010610480f0000a00042d0582c68001034194000c0480d03561171052064070342c44401d14460400884030103500310b80010059503142c1c4049005020160390f041c0c101c1c02d607071103001141c0300700c40014280e08030f1f0f081504210b41108801c0e0340140209082c0000c400d10b88800c013030001e1240c2c500e100310117150361038142844100e51000b01d2a8003085074007081045410354149580038100c0c441400142c480949030f07802240c0c2c0099401110b02116000808110032006c6001c0541c806182a004582030320303014040f035850340c05a444441070754244040140d8486c1d8500082c001180241d89002e080d076070711002581c2c002020700403100b6444c0781da501400700b00c9407a0071580c0b4180c89510300416242c0105065424030071a6190711081948610180d4140a42d942c81c4030741002d81034010b060003118000700509107240d945c1200000070b40102c0d9071420300c84039215160384510013402405062400d464001c0c010500b04801018450080d411f088400d44140100c49080070103856862511495 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 950051250 1250 950050000 950050009
    0x1505031005090313080a0b3304060807180b090f04030302090f04050c070c0806060102100b0a090c08010e0714030619150203070507050f0d080703030b19060f0e090105 73
    0x2820200c4520042050030400350015603071301e0040401c000903284042c02854090381540020b010a0400000c01c059001c40910540e540f0b110f2803c00c040f080104444200860f01411665008a8a13801907150024105580d5000002c0d0848c0000080140c0d680700300400c8220603042e01d13919418940080040d00084c000e50041036801001010114540084000181502d0044941d00d8040e14003040d03030410090105101e002070b18955015020078a44180000d507a4403149103415081070f21919124170b035440e00402e00c00508010b110074006541c0420000c0c00d41c0d0403c7c4107007003030b80040e4400103000d20b2041000000d44244a56501e1842c2c458808115081c141c10021000000c082c000004a02124540d4007460740387d240c025584913201070403c0ea042c09040e078003a030300034005010740844561b1040d602d848010ba0000e00d0503100c80503401e0450041c80d150b1006500b100112074801d00000404416004132460f6582340d03005c09000740412100d05201440c07440e00404050b00600c2079150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 950052500 1250 950051250 950051261
    0xf03040f021005070506070c033606020105480912010519050105090106051b010f0617210c0a0803040b090c010203040f0315020c01020a021015050310 66
    0x5801628508609500015000d101d0300c0d220ba80803076000640b900401500384481c691268084c20200280f00e91520b001c0e081d55030070410108001d803040c2d2182c8460704846588864242603945200c41c00f6114030019008010030b40d8044001100301d00a031105541713100b042d803240c01e80d055070580401380001034414000c20070303000e0303584180b0203001401984d110f40d20242491180b00e000801d0030308140a1030385400c452a1020700c0071600b450014441d94982014280c11641e582c645280c0ea1040701c41c800c40a681c2c40300110b0425401d00b4035442221210390401d400341d404840b11552500701f441c518a9603001c140008204007000071911403001000880640001c441000a075120401d0355981e00645500444085130440500428046003c20801048090002c03c0c0025850182004014440e003e40713440300030902c0d254403076460084060391301036503032001c0010000e54423102e4158000e0345402d0b50410321203c291038074a80c0310b0800d462400d16021210082d024215101d10004524003802 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 950053750 1250 950052500 950052503
    0x10f0608070519030605010e03010905030313020406050a030b1b03071e1115090717190341040b090d050705120a120503041e0f0c0621020f0f0304 64
    0x40c00740241d45480504488480150f00240d0f070014815081c00005000d686500c9001d80c000ea14100b0b1030000181c0000440c0e8003c150700080303e0107400d1a200040180c100c503041650070040503580082000050b270100d50090304100c070150b124013403404a05850b4001101c3d8400010200b4404900c03850040c80c82d0060840189441e120344100c0d0326460b0b2a19254184100032400801d0030030103046d1040c0000c40103070600104044103204180c864507924146541c0e1851146190402401010f02908070241000100303080303400349502c000344440000703240503580000320003183c5070b103d04003140d00300b103400395500441294103102d10302d0306001c0c0101441350115058480c0c16030124055440402503442a24400c009000c00f29041c504030b60f000740e00c2d460020a100e07044c010301000403034201e1038003070b4800483d01c04071080c4480c0c10814081e044080024001c00312411b0045002903000742070310b4500c0301525060705520441071095049108450290542803014045420f489640c0c100951b00306 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 950055000 1250 950053750 950053757
    0x15210e1507051201140406080105090703060b0d0327050307030b0910050c030c0d0608030c0102041505030106142d190809070e10090e150708040506060f01030216110306060306010f060807 82
    0x4079100c0001d182101c02c1501c40cbc0c81030344e0000d0410070408c1014040c280f2000300658515460405950b4041d01005403020700c40030192284c07c4503c0c031400d40200141c010540241180c0245a49040c48c00c448902620b0528550040d000503800c100107a0052501601ca0704402514680c3c81d1010b5400c690000c1111032041034584400080c0c50100300050058200e100c0300041e41c0f2460000310320805040c004042c801d0080500c0100541500100b80c01d4408603d502c200380d0341c17007100001c911000815484107001c1300c0221207547c00592248081c103580a58000080700c80c41003e2800e8580d800201c0f01c20354181d01c01c4000784520440003040503040180c2d5100710803031a88030000f15060300d0300c01c2100502c84c0d01050380b8400d021210341403680c12070840e04040b04030f4241500c030b503512004014003250003942d01c1c220318030f416480b035070440e8441c034080b100d41c280904c0a4a44807800111303140c0c0c0244684030b1400030030028540031880034100c41c0311441906100385004010341c2c100b400204010f040c07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 950056250 1250 950055000 950055011
    0xb120a0b0105070209100e070f090b0f0f030403030f0c03090f120306080d080f06090105031e030d020711030c0103020c0d080c0708070602090a080715210e15070512011404 75
    0x10703140c190b0001d004004503002058018140f6002c0c124201d0008c1611081040c1d840c125044207406c003500c0c8098541003c0b045985401b40894641544100002e8a400c107100000308414560701d0f6018103002c025261041c000400080e5040301911050398029110f1015000403c0c00201150b944094038183c1d4100424102c0d6280700d41814202e00c4051000440c16990800c440d4211680e10a41d1010040300d03152800e504200200e130340d074072440616031a11002c1c41d51404d11180d080080c0c5529841d2100c3c15990713100d15203405800030000924040c040e01c40e10740490200c2d8000c2c001c0da51498440c40003000b5071403c0e0701c0112150040035001c1c03555404200940004600013400420303869005400241c3d0750020798083c0030540030181c2c081d20176604101d900344401407580203007a80c05801807400c052401c500580e00d940c08681c0d00a2108698604070300140310f50404211030b104a56a00c43c408444c0c0e8884c1d0782500c240c0f151440c01d02108070040014460034000220039161103102600001d036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 950057500 1250 950056250 950056253
    0x3120d090203101b080604050c04030f0314031602190812100509040b070f11031803071d091b18070513170f01110f0f0c0106030812010b120a0b010507 66
    0xb11407001301310480340114518139105607a04000e24a40082d01502c04000901c1d0601c0142e0440c0101d01005050b220604500e80a240c458003003d2807120b26140d070183d036402e107541190f403030b46104400000075008420410703903541401c0200003503007908070320a245004c0d03121141010a03d0000c00c1000d50311003620b00400c0303548030254002e1259100700142e40460400703d6015008250440c40c0d10b007041620255400121004800c0d01d03400c0030b400d10117480d0751101a0004c1c0c148081500445502034050300c0d04102c82c9800c03800140035603450420b4468030008001c15503501b00f1900a00c1d50413000d03440e10103c0c846800e054007030740503000740b4016081001c1c0348840c04e2108030b42d5010a03051002200703901d440e5035060000701c0540d20214020000103103050f415020f28012010642c0d00b403000403480314280c0c0c0c6d044c0221068111020004c0060584924240780e40e90041d00300f141d42984208004203401c0005c4040b91003038040840741c185290380b64000140a0300011011904200c0140000e40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 950058750 1250 950057500 950057533
    0x1406030618070e0f1b090d08130b030906390f040905040f02030708030705150615040b0a090b0a0c0f1110030518060f1f18020a02070503120d090203 65
    0x207000358820007444d0502e0920f40d04e03022040725a203000c1c1c62001c00400c05041160781c0c0294502d0a10ba01c813001c582c5951403a007650b8031458036544042000c8038000100015414081213403031240003040c80d40504d40000e040d03401c0141201c00d410200d401501c403132400c0203401c004064008134503266007840c40c05031901150001d544c400e450488003d10307100c01d5241140340920160300a08104401107041148a0701e6440c2e0711046040241c002034820f0700820b41d50303110b0344001c1944402c07500d4115915035450803590352035400000214000f40107944085607440c08102181c030301401980c1c131a0448400c0791502c001440654804462086000c1070700841921401070304003200710035450000c1d8a2422001886031001305c0300c43d101140c0c00c9401040300e201e0515507000d4100c1c9040c0750440c034810101e030094030311500640000401018460241d800c84805800a100503113466095030887d942e2803050540c0c03507944074003502200405009403110110958091401c0c0d6000400f202c003180c02c40e04404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 950060000 1250 950058750 950058779
    0x102130306020702030606090c27090c030405010b09190b13150501020106050a080703080a020f15011e0b041406071a1b0708030117010f05011503140603061807 70
    0x11501a9008200d0f4420344c902171100a81c042c10030b07908000316182c80c1c000220366114882c43c106509501c1c6c540091802c0d10f420074450103400140541d0454101952101d0355a0001c07a0308440c290308000c020501406c0c082e1340c0900404151041099048a03090b169000e0440008041e401034011003062040e400d00f03020b13500001400b006800d040303a041000090962b11550040c5000b080c094038208041c80700000c010080307070f410201843d15580a040101e06125203000781901d60312494011090041c0b802c900c132070484003403041004907001a001e400a400c0114810b4010060003440200003000c10f0381c01c054941c250042c072031071510302c8a503100e00004d21114102c05551240c51304000f0110456050f0001c1c100c45801030b141000003036a240e0180340b0050117100d10791120800200b04052094002240d0410550824091580c440c0604202d01f1000d078602d000103030610900036511842500e04500445014001d00700b25601c421820000c0380b506c6503024000e104811001032001411b10b0f01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 950061250 1250 950060000 950060003
    0xf09040605070908030910050306031002070501060e1503071e230a290a1b06470312041e0e160c0501020c070b07060e070501080f0901021303 62
    0x1640d09107140d000700300fa290b82d001072115a02c02c000740c100c03d56406e804c60301880141d1905c10b550f42c1da803001090400703c006a100c20420300201c0c0b04402c02c901904054252074103503042c20003039501c440302003407007010745090542c0641020b8000c1c4018a00c00804440c80c0041101c0551040d50319120f06c608000c1580d002c07049085c191180d51150b19210712140000c1850a0140700e401048901c20014461054032410b2103043c00241042410f000b514555445540010044500e41090510a0181c440001011220100c203a0010446445803989264464007504095034001400c0e1060041c44480070307042c1da05110724102c0c10004d60190300280058080220118604451150079070518411a040041c0c805400002c00042600c6600e6031840d01600c0d10302003610525909147d8024401d0301c0b41034699005001002c145101e8040080400c54440e18040240070701744190591252203d0040390300041001002c68452249031030141c2d00510901c0005182c40c3e2840310360210742ea000e510 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 950062500 1250 950061250 950061263
    0x50315040921020f070b0306030d080a090c060e0405060405090c040504021203190207080319030203071806051809073930050306040f060902030f04200108060d020f0904 74
    0x1058154620140045c00003810034984a5055007080d00c0003d13100c0c2000540e5004010700c2c68009841031400e40c021044040c2c200c2200030700b65480c6c18004146195104030b66000710708010116095082a2107282d04c6121600c2c060018150610308100290501600036a0300151046441d04091402c4c0001d042250400300e803062200b80350400a42040125130040049400c14400d030000d800308602d4016060b005440e0060780c03aa6550400d40e41ea0309007144003007500350028808101d154100e0000d100070744101854030308081d4140308010800c0000c68084000810140660081c1d81c19001d010312040c40080303141503202c42c9418801030040e0200000da9880060100070348082c052031110101c1100075141c5000c04400d001c0c400b810301d01c4064038050060347c0c0c60304a00114001540407002610442c02c3c02d5550741040f028940004000b9107050f98420341c3c000c5949030205001d1804080c010060b152500740356204420444100f0416a0998100c103401b018001c482c1d030340c034148510071403240b130 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 950063750 1250 950062500 950062513
    0x4020f0d1d011e111308010614190b030402220b040c03050402030c0f0406030b1006110d0c15020705010c02010c08070e0102030904091103060907030203010b0105031504092102 77
    0x1070103144100e18070080c0421a45404403c8100c69580c48410610401e09040401c0346140e0202d28a454070500c88005660080c0d2600072812500c19006042168201e07008028018410000c014540c51380910f0305002520724003080000340846800356070b000e40000c200c041001034083d00c40507200c4024105540c00da039a030004c1c61151410303200e4200700c0440e030703d07040025203041c0c1c4c082550762210007056882410b1140303200c0f0031980d56400a602840e88607001c6036150074042d51042d5000e04a0103018003003106c0620494460900141c400c680c0c1d1040e5603425681da20341d8440c0c00b408503a900a1801c22602000720f240812024000c2211030707411030b800000c0c074440e0458010140c0201801d00b4080120440d6481550781e40001980c08600c0d00300ea0014a507505442d1100410b480102d2454060150004108a40002040301c030216070081c0d00030300c40c480d6004011106488219201e082a209038481101c441c181644000203041c81911060048406400d030700b4904104e0b4094100164840c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 950065000 1250 950063750 950063771
    0x80109060c0903120e0f1810060309081e0904020a0203071b0f0603020f0721030e0c060a0c050c09010f0f0b09010c120e0a09020304061518020904020f0d 67
    0x900c1075824084462800c55101400c55071448242045a01c107501040103400c0b0f0741e4142da560350045000004020010700d0700c0340e0b0803075412106940849550380e0700d066100c0e00081c039900074003903148010b505c00e00c2103103860a41502491107030032504640801d9201400b07100081e0300d40344004c00c1081c2c2a50021a00c2d0300c0d10345401002e030040d101c1041200400c08004101c100398041034001502c00b18100940c0701c01c54640b04001034043c250300600007822030303406c1000301120528000369420350f5550070b00481c05200303040360343c0d40b08150f2490740165080081d4103000384250300d8004041d2044c025035141c0703080000060b00280b42a0411911102d40c03031402c0042c1900641c6000042050900e440d050422040001c0c2c80a1194080984010a640c0c001508075100d40b05c80003500c0401040301751510f0f161100c010080d00b0071101110340c0c80c40d201c2c544c002c040001815601700d4a005840c004c0d0b0b04454a10000039400c00e04103140c206400380002484d5074010b501a08800c45039080c00503110121 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 950066250 1250 950065000 950065013
    0x3705090403081614120a0c090e0a1a04020414100504060207140d06110a021e1002160b040f0201030605030f0d031d06091c0c030507080703170f070f0f2a0507080109 72
    0x1f000400c070602404150400c07000c0c16540c2119032044140c540010b010b4101102c604400e02c0c065000d5a00030310004000c04d016121403044042c20718207851801c80d9840300c0c14252080d00c91400f420300564007100082002d000ca1180000c00a00c001c1c1c81c844c0340c1202c44d03a403501602d240c4034606d01c10000201d8a00005507040080500310200c0500090b090504900015201c40c10740c0740801190340c00050850142d14400300c00d24403e94800000109454181000709940240c204205c0c00039061000024492800144a900d00342d10400500988402008140d00820941e0310107940542007038009080300c8410f1007081d204000303140c00750801c000d141000f040e04507480400501030100e03484100b00800d6000055450360b95010285070703130300d43c050f00b0140c0d00388201e500c03e2015220804100000c489a4680c1507014500c1d5031103c138144402102c091301c0348100c1c000400005840e4080788400d60518464440d0f644400750400c000110f15615440c2c10000d40d030300001d401d0b030344401c1c09404001c4d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 950067500 1250 950066250 950066261
    0xa02090c0711060901170a0b09010b0403080a030f0f06080a060e070e0c09011e17060f0f1309080c0313060e0f040b3705090403081614120a 61
    0x4500c00c280745071200c0c9503680d4031024071807103046008140110f900c40482e40140c03070181c2c10b004a94070310580e61509071104005003c0042805014040c140d000040300304201e810f84041d00da020321501e05100006804038010042100c454903170300e40300d0308410b120811380d100341e4019004130346c00307480d00c15668203040c019981100b198009a5001450400c0307001094426030390070041030080c1c5643c924003000100c0350919608552504004184071140301581c02804100c0220101181210b0b9542d0780c41c1042154289084101d03003004180a01c030300545000c944649500140075000034416000351514034041d040101c49500c69400003d02620b442482840c1c90000c106a2400c1e1184c400341c880400ca48155005085000e26150540101c072a501c0c00a00011510801c0021001081c0001520604400101c00d500e80311300e20080403680b410f01d4818188500d0b010b03225000c141c0c0b5250300007114515018082c00c01c1020404008140f010a4001440d00c0c050702d2002116900f000000030085a1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 950068750 1250 950067500 950067511
    0x40f0c2306070b060111011407050a2c010c02060c0d020c0102070f0b0403020907050c060a1508072405040305030a09090525120603050312150d110d0305090409050a0209 74
    0x1c051121400040400c2c80650780b1803400c0c40c103e503000702000465405824806800710b101301d81a010018050703802070107071161030803d41e61200c5402140035140302c060407500043c21408215103d40a00d940a4042e441c1198405400c1c0351a000340c1c040010309060180345050016044179251102d650303410410344002d841341c2c8120074005860450b03a4803180c41a0b00c0000c1c0240503100009030050700805c02d0b1051030b580901690030f580b60690402c001050b100b101070106902c8500d001c0358881002458a00703540c140382100c2400848010384409c4500034400d10070810008110200000728180003828120101c1e880d86641c0c1d80c03e143d01d580642d20000c10302880d82c103200c03400104a4440c440000802026030a0440c1032041c040381f00030103806581c20140031848009a00b0a00034500a4054031440303a0110520f01903a100c820411120301a9001070b2460003449034604030b0349040e010131603400c3d2085c28824584594603010400361035207140103032030780d402850110081d0304050b08610f9000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 950070000 1250 950068750 950068759
    0x5090613110901090509130605180604030c1203060f0b130b0a110105150f120f070305100612020117060607020a030f030f020610091d0604050f010c05040b0d05040f0c23 74
    0x1441c00e00c410007505461f4900141105031074402080b614981000c03401461500074050300d1451803d4100602700c800320b40d004940182e404101404114030911405040e211540a111012031800d003904035560400713114203c522100490011b5608036030001000c1c512241d4603016900144107400d40c1c00c648009200002c020b6001c000b041490341c0d403602460800303904403184036a0b40401f84010f450443c885581e180203200c0d0341800b10900c48002500700300b241c992442442070f191076101509200f208030340e0090105130355030148440c80b03540018841c1e0040003d420710f0f060801c150002000019541d2040c6d88c2d040c042020801415402035991030f0584543c00100610308080b040f42e0213850041c071a000c4c40c41d0f511a4040081550503101c08076041c0900101c03026401d103414220344a0f03181c1188881a58038000c0450041801002a1401c50b21a940240d061072040d00205020f000000d00440716010700e08441400509485441006002d6807105100c091003a844d0503180a40d4400d50244038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 950071250 1250 950070000 950070019
    0x1811220e0112031808072615040228060f0e0901030b130c0312020c011709030706021b0f0c01021002040305030d020c1002160213020a09050906131109010905 69
    0x7010b1040b00344061980d01d49004c030200440c0b00c540300d03041c004c203400000c0c081c05625000910402d0285c41c00203402c000012500500148400d03030380d507840181c50f0b044001840180010098640022a8210000c0164000c8543c1010003081c0300a48040c5d0030500108607030741101c0001c10b62041d000c211283c01075601084a5040d61a07900480c180201602201440921404208855109048001e640c02405000d6582a105d400703500d82c40c1c0c048401d800520b0004009600070f042e04605800b602d9490041c0d40340420a40f6154040e5020500700d0420601860b0b036004c800c0d0040208025113800341001c0c0c231209501c02d00090034203c545a04081080c0144000d01c0401e60100407100013800700c400069803003075400d120704e05009200503c0101c0b9840072403c6400c0581044085003203034400c0b101889204010280d442c224080c0c00240c0d000034145603801e004030b0070140311082d003208006154400c00b140540b80001030b00d4100030809a4a4404681400c0550300180805c6c054241201d81868 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 950072500 1250 950071250 950071259
    0x9030c03081201170c0411251a0c16020120011d01021809280606030501060314130201050f04060203090901050a0617100e01081c11071811220e01 64
    0x21303911400841c0c540300b103641e00d020a2180304010103c032407008c01ca82060800e4024007500b11040f80800310291040d080160b90212941201204140b00710303480941c460400045162030111001400da0490600c00380003c5500c3c0400580400c44140c40c08400116540c00e035440c09c50208000e100d440407107a0300501825800c06002101560160000e440c0384101da03a62980b0f902e43c211010300c8851090f0848140f140255089800100039a202514148101d980c0c07040100d08607414075880031800b00300e00000c6a03001d000c60b1000500980149406804c080345107610003001c2d0300c81c0d80000056400011010001e007052940c16006210440d202d108007844c0c00350152807200400c11001007031120100103024014681e582c1d00103003002d80b92410407581c4482070a695002d040c01c170070011030740241180508620890401c0c2c40a040ca40c094001c0c4c516006103010314a001d803070910f0200743c403a04440e800304901c00240c00940c02c8407444911344510314003440c0044140b07070481080703010403800520 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 950073750 1250 950072500 950072503
    0x5010207120b1f0f03140c06070f020117102303060403051c0903030501092a0f020c0d1a070512130f0506090d0e06030105090f0709030c0308120117 65
    0x4242503000002c002540d40e416481c4000211410b40d514103202c900240800d0280401c411081070700d2040d1091702c0241c020300c0306640c0d201c0c51001c6469020208008004c0059041070000200c2c40c4181009003401f8081c441400704002c003200d1010310045620020041001245410599030a9050044080703c101101081d12014000c102505000000501c0782115881c41484801e01e02140c00801480d144d601e00280501400c0c13140d000f08508140703081c9160780d200c68045d034082d2a6015880d080404003803050b41d80101903030001b02980a03030b08924031380c4d8442500c402c0360039102d16602c038054015045500000103000d04400b040250602c8030030f010b018043c0030550420600041d4614030102450030810315036040703400030164020401405041a00007900013040d244986528820000440c10b20030765000900c01d1a600540d41d1000c036101c55100400e07030380c00214524040140ca501d9403150f0300c542a141c1d10849481c40d002940c08104003e01340c01c81e0140a034940c400d050400c50b8035109 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 950075000 1250 950073750 950073779
    0x1e3b0a0f050405100b030a0b0a02030406060509100311030c0603090304050a0b0c0a0b15120d080604110d0b0402161208160e0f01050c010f051909030f0305040501060306020f0c0705010207 82
    0x3540d00b0341d505c21100c55030fa420810042c1d0b141c2d01c4414500680b40101105001e500142c8049808030306181c1c01055038640b0b100554805c460319440601d030740e0b107140c8940303403134a0038005603030740501030b84980141e43c0c1c444000651040d15602d009580c3d940ca000c007806841c00090303003c90700021061002c3c1d900900c0101d1500340c03540d040240740b4016220200203910544400c0300c1280d03c495681d821601102c0081600f40310740100780c4843c00c1c0b9555550512040c1c41caa100c02c003030110002c2201502d020090750142580340c6014200500f000c9007070408141a452101c4103941810042c4420000c2c2a03002c13982c1540206480702003401284009005400301201e040250b200390b1b500011249140d10640071354441c19005402406013181d11240c1030004e01051342e1418031204160317044c401d0030000b0701485070900d81c03581c4ea201502d818100308900910300a0000c0711955210f040000128105001034040389200c101c070303c1e65501c0c145410501d05174099100a040d90009007040246084c0c00020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 950076250 1250 950075000 950075023
    0x10c03230f03070f0e0105090d150204080304081c031a0f030a060204090606020c042a020102040948180e01030c030c1e3b0a0f050405 59
    0x12600d20105100048103001e401c0d02030751100c07400720420003003e07805210280510201c0c0c65a01010560070f004403070a1290020060b040b0082070044400685010000310400034010720050a00342c070740400703070b0a41d4003a6021000c283e20540d1028100301c2135800ca21543c5006090802c03884140140d619140c055520203180304090070382914900c0c0d00c050040c01e2103254002c0c811583c50f0340352401c1c41d000b000301e40902d80040c0b040c0348180005007028891000200d107100d003801d0034810703185410400c1c1d295030403035102155001d2100281c2240c00d4007680f46803152a048082082038402015041100748002c10005030000c1c008103580302d0080c0b02035171400031081c600232104007109260022941003940c8405007141d9130000000910202050001c15248141a0040d0345540c60800c03140645c050b20060603004d00c492000c10400c5000385c280404840d2b44c0320b07a1400042c2ca0709120722203100d0104400c3c41d0041c84000c03c00405c40c18400c9542d1012001420405403d00d070719500c1ea40c040d03d012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 950077500 1250 950076250 950076287
    0x406121a011214180f010b0d0b060109180c080a0c080c0901090302090a0504061104030b0c0a0309140f010e0304140f030705150a1e05030a1104051c11010c03 69
    0x1480d1441e5041034000f40301c800c0c0400348000140c20203800a08040c2c8180780800d803140111684402c001340103010b0b84e820500024044001ea0200f911040f10b174079409400c903414003040c0040015014070110f03035180590203031200050101c5880e1005842c108001705001620b514110f55422501e40140310660020070f0309841540724a4000e0040e1040c1c56150800313503200d000f200c10003400750801e40140f442203208180c02e0201481400301803c0500036400010f041c120300d180040c1d8160500d0010705907131001d9140205080905803903584142404038083e83d180d0b0003140000104c08002d01507400381307003880c070000d6240a20b0804291030701500005074510a08a5030f043c0391559400b000603801400005001203201103051000c4282684490600710101c3c5804044110800d41d5404005200d515070303d801c2d15503907460b200c182c000c1c60700440b4016103050900000c22540c44800f078103039080d060075150b4050b840343c505041d4038801c07080c1d071268104040b024000780080e80c0324a2541c110081d03440d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 950078750 1250 950077500 950077517
    0x14060304120e06120402030106051504060503040f02180402190602031c020f1611031534050406080f0124030b030a0804170d0203161103120406121a01 66
    0x1d0300715520603050041d00e50210022806940344860030084070301581c0b080707000704034403555002400300d1181a04480c00408006020820407140110300856100b8420003620103054040e50000303240299449001012098040c108011420203034049074507a085184818190380ca003020081da6172050040145203070320400301407500d81c05242c05070303865201c0320121641c0350340410300c090103004a5550143c6230600301c0840040e55040100380d101c0d1460210000e954a03039511100300c00c1000c3e801030350900710090000c101100041c48400468441032542d5295a07945c075002004201043c0502500c1d4100401c03c01008186040c06848030703252280400215103842040040d00203040103803109400d40205108a4200203d96005009a45000a420784e0360700c2007905e02d40d5100d4403545c860000d640100115410390300c9441c11201c90794840d40700340302c0c2d480701030021900300400213000500d025400715050229a800c20802c8179200d00801c0108400003104110050000016042506118501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 950080000 1250 950078750 950078783
    0xb010e0913080c0d0f1805180c1b0607020d1b260c0106090e01020a080612010b03010f021206010c1a10050402130801112b0615020304030c14060304 65
    0x1d03041d00c0e011100703030f0195280d03030071061009000d9440311842080002c1801d042010004800d0000205480000d40726a0b54000b281e503007190340356805000726103c100213100c0184044201d009c0108039941640c007400c040d040c00900a4544045002040c007440122000b1140c1a1182c0f80f604e1076007900809a01c545410300071800c04480c0441190503c291000643d148108405410074030480343c103420100490850008460700301d002c0e03080c40343c00040c07404010560628024580c03400003c071a600000c2e10102c0c6200081c215104244d640142507004110088450350481e005036001c5403c0c04c04035210702c655a03440314070071402c0183e180b000c01a8004588a54181290380000e004090000c43d6140c03a203c000d0482e410652048020f00c0d801e0030341058150f90030509a1710903501c490250402d80f1060505030410011600c1e500184582d141800140c140c6c80ca100004400c1c1e0b25000f541d652401e600300140410055004072603420391401c0c800040751038100c100d950194020190503666902ea = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 950081250 1250 950080000 950080013
    0x50a060b0612040b1e0906060409020402090a0801090c12170c1005010339120f050a0c080d0302030c0f03100b0301060512160203042c040f060b010e0913 67
    0x802560006841c100001c120130400304030320807401494a6404005648103500030107103408030480303800016420031001b02e5040c0c00d003038021064840c4020405410086000b0105c0e513140b20a60140481d691039a1142042c0640485100e024099001c4202d6400440d51182c41d0313104446102002e0301000010310800b16a01401010089403013500144400c1d43c0d64105041c45000c1000e00740c80c00540010b5158203a180b12007070310b409549003003448021078a40403034040c4586030f044d000d54040c1c90742246107000030790500012058921501054036050b05141207240341890340c1c0007080c20702d48100306201c1c1004105040c0c070500100d00752020303600d6680c1c52005000c500e0940c402c80c45c0810200003c10001e40000103400458800c0101018545e44d00404c4480112580b05a4025070004c0009002da0008500188145001024200f41114144d041150310303100071101a00c0d241d01d0f09114008002060092130140c2800340382c01c02c2680003070000254100300103801007008441192416081181 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 950082500 1250 950081250 950081257
    0xd08030a0e060a0c080601110717030c060708010303110a0b060d02030a0501110c0c030115060c0c0b07030e040c050702210c060705010b310f0e0d030912030207050a060b06 75
    0x3001050360b00307500384014544094180700c030344036010540d207000240240d44582d02d01080d40390490002c1065174a880001c800d841794940000c4124001041184490f14040050314080d41c5141ea400d1040c1d031450800070003848940e10250801e030840860781001c901c9581103643c1014045138050314100891000900d04104c2c01401026942000303551a2099150700103840d0031440c0109079540f03018107100b054202c400159040007402ca504070700b4041184900c3c045210140b00c6c0c000e030300b00d26446002449080d0050704d0f048000039082d000300c03d071034240780c0030781070f81d030030040c10080d0a0008950001e14180445640700da107241d0520b02482480d1810030034240e503000060f04644d41d808240c20320502034032151182600908186a410303004c1c407089c203503044020300f148031081d03030500d140020b003030141c020782788084026515114803452121090140725080b15a0307403800a14459545800380c060b0b240417042c007042c54814814900440e5007c01c00003c0c040e441038000522504c0310000641d07602 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 950083750 1250 950082500 950082521
    0xe01240309150b120d0c0b0720030301080d080108030306240a080604050108060105010c0305030601090e09100e1c0c0f0804150e06090a031103070801020d020901030b06090d08030a 79
    0x250404a01a20030410f600040c0c80b020240e500544444800360300558980305811540c5c0050000c60350200031440c000200780e00a0942e1601001e0203010300c002000e5840c80c0140c0b100c05420000042000c0203080064004000c41801c00c00081e40c506a540ca490f40001003c180c098440e4044105c40d5103045140c00000180d40001c0e140c031410308401c01401c1400490b003590007245404008624008002011030407501c050755401012546d070359049600707410142060303043c44516440440c40a44c00c89515225280301001071001748464459281961000d00902c1c503180c0000007044c0004815040850580c5c6140c140251b80841c05c5c5402d03a1501c43d000c0025054040204020881c0c0c1004001083c05690943e6541380340e841c07080401c60a44107004505500c02481d69081001603241e4500c8440100700805803012a561603607400c0c00da0b80003070481500950300060481d540c2d82c04d4800d440742003c054036204e040c014101e01081001c1c807420b40291649501200045810a10790004032045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 950085000 1250 950083750 950083763
    0x8070201140403080126030c160537030501050106030b0f0d0b0c0c07090606090e070e0d150e0604051c0801120311030c0d021011030f0c1602060c0d090e01240309 71
    0xa9200b08e1095454041c9000c85941036840131304002840d19040540008810200c121010a040940080640c00000658407144d8440c003400001c0403c400f07200b620700801c0346131000f2807041282010010f40c01c2c400d10445214404000d180000f0600c0b070744100ea44001d91800076651104543c11061504d55543d10a40b080380c201500460b49551040744441206c02004031402c5ca41c650100665810045110b0345800000100780600800c0c01d45d0091210011880d41c00511a000301c020a0f0800d0345c00c550a44141c0e10a441d1010040e00021541000b000d00d40741901e011350400801044807495924050104181d0203800e0349080b8040c002c40381d0100000c02154400c06010402035110780c1c818920b450800d00d40100c0c2c000c1da44628086900c90b01502c04140b0a650740c6608001050300088041207440000030340380e20058540740c00074440c02c04510003c01a00301c0e501801070610029401220080760701c00d0040040101560b101e80e003c00c0580700310441d44484150450003002401030141c8003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 950086250 1250 950085000 950085007
    0x105010f2a02090c04230d060221060a05131a0a1707241d0402070b0f13051b030c151201150e090408070807030807020114040308012603 60
    0x90001c42159203000744240c90b00011540e0391011500240254460013092a4103c5600081c2010026040b400d900005044618000c070030744130f4408a812100003200007015074482240c507980000320320b9a04c40ca0407160f5100c034034200000b0852542080722942d50058485003604088003c0796807012102c0c5000c3c0034042d10070307952038200147c428007132a07010139402400b601051000300d1203041c1400302c0750461768424410301804211600044064a09000030003000c00300c0c0140d0701d9000074501180516070300038050400385105a00d841002d03000038a2100401140c200103080460b44074007958600d100807001d52007090200381001103000c0129408112890f840004a400c40044c2c12405100719411281e81e898008020351102c182180c200400c24242012525240444105510910501c0c0c101c2c20098960340c1d02405821800003100800c501904001940780d09204803c16180b00204c41942800d02c0e850161105106024101044904075144001c01e01c9800d003004640e00a003003260707078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 950087500 1250 950086250 950086307
    0x20f0d020607050d080f0f040305071b060216050f0f190305011e1805060a0f02090d0309060815090606031e090d0e01030e03030109020a02120307020102070b01090e060105010f 77
    0x4440404c914400f01103407201c0041078a684040040620400c02050013501036211601c0603103680d00404c0c01103c1500001441e1818000c240c2d00071401081c01d60010b00c0d80340110280d15403610401c0e001240540c500102001c810b5070744d86101841d0940c140e0b50100414009200f2410050440e08060901e600385802d1469488400b242c032103030079040380010001c00c0c010030500c803206803003510058115482800030800c8112070340d00c241c0306c03a80a15801450405080c000c5002c00305640d0302540410280c68080003059004091180d10000d85003000300151007800c009281038001602490254902200041c0000c860b0758000d04840b103600c40400b1903183c074007941d80d503481d20425030400051001c501101254003034080d0004c0c600024001e9819603003084030340d0740250481203900307003184900c041d0300d0100c8000c41c00840c010740c01d9600261790b600c0315041c114041c02d010f82c08480380c249813441004c1c10410116585041d54001d03e4804010400d950044074aa03030400c078080645a4400010030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 950088750 1250 950087500 950087503
    0x110f061e06060901080712090f0f0c12080d05150d0c0320210a0c0f0906050a06050d050c1e0405030d0201150e0604020708030108060a14010b07020f0d02060705 70
    0x80040303615011151640c0e101001c1c00401d020380000725001c0340e00302010410050140c110000c0c030f400d40c00800105116141c40746403a940089409540341c1d80800d0905080c44150702125028040003902400304039040c0da243c2085114608040c0e402540d070314082181d43d020745032102d192140040c1402909c03045030818903c200381910007221640013210101d00700b0881303d00c2000346000c005003180e080500303004001400e5125800366820314001d1640720b2000a880c1c00001015102101c043e502243c2004200750480e0015000140320309407410b4200409a88901143e0142e0200a0086499100e1204031111406038103050210034070700ea01404218040480540100d035411001c580340203070310a106a01721003102c002c01221080341032003800001242241590080c1c40035100520340000d6440303030b001d10b800a0700114007681060007849100c0005000d00f502c07420450390303008c1e80307075141421040780ea200354800240100384079a105100d41d56290042503000760080d01c89695403d80f0325046 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 950090000 1250 950088750 950088781
    0x1b02030a0305160912060b04050c030a0507020604321f0b04060f1a0f1602030c101d0103110706090b0c1309020f0d060b0c0d11060106110f06 62
    0x40000074608000149908107640c041114403c481c1c13100c80683d4206581d003038513000000d0094581645403100709505032550310490f4803824400b04481d40783c0c142007900c0300603500042c2900302150301040900002c101e11001c00101442c00c4048480941800c400e555609042c107090203916019410340405060408a1002d0405003c424208400d000c06400c00040381c170240192030420010090034845e5403207095940c02c540b64110300c99400c000f41c010480840c0c1e84080000e240503e0b030f0021400442c10200100f981301c40c000c640c3c888461003c2072004018002d520301d50020809442c4074a180c590280d4882e200c00950f100401d42d03903041c13605080c2c01411584c081160020607190026600d0401c0c00140c41e8108040160f40700d290380b501086a01035006641031443c001c2c410895855001814807540e40203042c1006410b0310303051107042071424124010307011000d00410850100c00c103000483c80c24195012410070000580d040107182e403402c0c9540561505610487c024884000031480b0314 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 950091250 1250 950090000 950090017
    0x1116060e0a050f0706140714070f0306060e070e09160c02090a0e0d020d0e060d1410080c0102070f1221020a1506030803133e0306060904151b0203 64
    0x1125005030b6141d1048981003c846c8a4404584081c804003000401006a1524540c000012500314071346070010300360002d009510032642e555136040c04004103465040d0340f5501080504140e44004002d0340032a040f490000c0c4146440c0031200300c0090326901a0491400c55600546418002d10380f1000d40c000a103100c1500320305622500d92004100c920000340040030805c1550380c032814540c10740600c05242c1062040c040001d456003000070b00d51200001e014440e051030030039010788070700c0c01014a05000e6291101c604641048105009401d0429034201c101c1d26506000d14449003141494404144c08903012103400c0f0702200d484240c680d0001d000d41c2001c1c010101e0400f03a00003e012038046604c00e00c8001d00c600b50034000216404595800407406c0c6000c4e01d07115014407801101c3c0d4410b0441c450b80c0710500841c20040e020340c0010310319102c020178401c3c0e000709a6802d00d1400038000c0c240c01071004000c00288000d4030444d880307a41060f907005181741319025400031819000f0351030b0380001c0827 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 950092500 1250 950091250 950091253
    0xb0c070e13032c1201090c05090112023604030906080106120504050f0f15060303090d150b0916030f0b0112151a07151116060e0a050f 59
    0x301e070034411144074001590364940c488400f00001c52031055400c0a10000e0225883d0301040d00d800161100040b51624140303140002a41c40707200d15024402d1107640d0001d034003c800a00c01481804501400c00350b2064048840c1c0c1f01480c3c0c004410b01c901140b0345000401210b00460f0010301ea1281a02d0074007807842912a03100301619a07504694221013449103000194008101d503844070318944c051030b0842e000e401030b90814002054014603003020f81080143d940e000032290320058500b401c140750030800c1100554070f4900064005011a4010b92024000c2005070418480184c0258406480800e01074411000d524011014400350f180320070307104011078280462920816000c6c440d245402c181616140d00907106900703400d00422a030841c55200303094950000c10b0301d00d543d02201148203034a50420f50740d0328052901818117041c04100036400c41c10440351903810034190701694111100304d081003240202d641403d01c064403141c441c10215010710003041d41400000b0608070241c0d02d1900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 950093750 1250 950092500 950092529
    0x9060d060f0608150a030f0807050d051c09020a050f131b080f0405070b030712050a0e070e070918021b060412170a0504031e050d060b090d1b0b0c07 65
    0x13503c54009000c08245a580030001d140f05100080000d450700b040c05024410301410f00665589441c0b41050012440001c16400b0400d9480c100222410b07442080899509210404460b0702060b4202c560b03001c0e95101d56200c55814045e500d41c5140300c00021b448440c01e10002c00501c1c3e14800c050341240d032060002c1c0c1017a00145441d00c00754160350080d40d102c0000c18820b8600b4800303d0450300080c00f030764100100380108d200300106501840e401642e4a0100040140810a0142c54400b65031b11407212195032008100d42560820584802c80345081d0740e500315001c01039030040c001d11a81b17a13009420444000640d44501c000100103115510804181c0c040324039400c01a5498014407100002807039500000640d064041e81101c0d803c54401c1c1040440990b0141403c03d40d14403900841300010b002080030030307031132a42d802090f00804507442007a03d041400004903100145042c80038001c114180103582c0604c00e901c0800d0010424800540d0300c42408a1506459030360038481c40f180800d144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 950095000 1250 950093750 950093761
    0x510060302101103030f06130c080f060117011e03020406060203091e030c2214070305010f180b0d050303070c050f03040b030f180a0305031e090c040209060d060f0608 73
    0x4880f00c0c4801c6254000850440da5059000702c180c440c001c00f09900711940c03074110803e400450242408091140d00c980a00c1e1a055500604000780204464100030f00100e4091544c072030100081c0c15038207403205120340d180d41000c2e03c0709a03100640c40290880c2c5002c000040132580030028040342d032011a0f2a810b03081240140105044441c1c00359a416040364110606601d40181c0d0700e03e60204e05000810a076113440c21a0040322544a90034400b10002400c1207080c1c0e6141c41614090803106100d184080c1c10700c00041c0107400c9082d40401c01c655108003210035640d4040a00c10600e510070300310b9a6910b8035030001845540245e004a0300c4d482244044202d40001205442c2501c15801400b42155520f4603010112007000d07040d070044051220380051144d80c03e1229504140c025120103550741413103401607014800d01c40501c083e040d121800c1c80300000003c26142000a01140c0141e100d019510004030700e40702d1a0320340002e8034503107040001c5500311310250700100c90181e107440c0000d580303c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 950096250 1250 950095000 950095007
    0x1203091f121506031a030715080915040f050f0f0102040918021516060f0207032006161b05010603050c03030a0504030b1b13030203121c0513051006030210 68
    0xc2c4072281840d80349540080c45514807a80c08071481808486510100c00c1540b40800c0c00e14085801c00c41500da03041c5c003070203045038200300d9042e000074403a130007840312109810303910154a4000d0402031031072600c041d1020500800f0443c1880031400e010540e000c00394146642d038000c1d4480d100b200303a607030b0400d669004a284542564070341250007500740c07441d110001d845500141d00428540e034005d07101c0807000011550310b04c100900d036401002c0041c0e40701c280d41030203041030b000d524508240c0b89040140c0c861740100440c03000d40001c0b06d0144520403600511003511140180c1c20b100a9803524120182b0901c1015007000b0110390080d410b1b10354841c541800d054a0b4420008801c001c200304010070000144212117a40e40f182d585400902c040d8161000020700c1d91008007c200f5110200500380154503042c0300e80001e0707981c8030b4071003890007012480700c20003110100e21880880340d03120001151300c2198410480035036800030a030340c007401d8540d40220041030323035004c140d014510001590307600030701 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 950097500 1250 950096250 950096261
    0x503041406090610080f30070b1909020f010c2a091401060c030f05041d060a08030c0d0806181303080108030a090306050603010b0603131106070305091203091f12 71
    0x895405000b01440b5094003140070b2040303990071420302c01f18a1008041980740c02c09000414820005101b075410150098074440000c00c9001c5c1c49549442009001662020000c00107001c0170b0a00204c0d0100d1030802002104030030b0b0074201401a54848400003d001381400300503210706280800205503124699420801c0c240146030108014a482c08080381c001c10004032101035a02d00240341503201c4180c5460107482222180d0130350001c009011170362919802d1240541040c00c011420681041080e030758441440c50304c00705211042000ca25681c0300c0e21446102d07420103480014490400080c0b25100200c5000150009601a0000318600708040200c0d085003003907950307407040182540c4602d402000060501079040d9660303010015541c64400203144200b44000f55920140c0d1641051154040b0321a50144500c0003045035a0009030400180c03002c0740306c00c1e1a1000d0301c10b1602d1006145100d202100ca5008001800b800e56600d0390506004602c1180e075200b151103800861140140c94 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 950098750 1250 950097500 950097523
    0xe0f041b050c2803112107110f010f0e03100e0a02190302030c01050c010e0604111002031314121506010e01211a0612041b030b0106050304140609061008 67
    0x40c40780d038000f01191003007a41d070b01c0c603a602c08296002d074401c03055020f205121030711080050403408102c16052203007584102c003100c1c0059030100d0109602c50002440303030b01902800414042d601087d1b55590f10200f00e89034040b40d50702404c12050b007041d00f04c640c0c2c5140d41c2e42c1c1244228688074151111a411050003412a580036005002011008005545a030499101d003142c0f50b580307424002c4000340c02c0141074041c6006094442ca00312058042c003070413400c50760b080340641d40100010410f81500810b030f001107462842800d0000f040394000281c510309a2891406548281c50511030304a00454209002d001c098031903548160318100155165001600041d02d41d82507007000d2015041e03079420080c900040c0c14a421050700b10140050130680000705448100405070080108104a810041285514000242003120314640c1d0f03c03241910140222806c100010020404100000d06005c10000c401000e40d020f501c1c1c4010820794402c4121102050181d00400000d06003501090351200034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 950100000 1250 950098750 950098813
    0xa05130f2010020a02211c0801062307030203041805010e1e060f1c03030204090b09040c170102040302180f0a0c2003040801050702150a06060e0f041b050c 68
    0x203021383e400308a05070030580c0345042d8801050040c40150340d0140694007010960318204252030802c41001445c5440580001c0c3c2405129801e0901810740303510802085e002c07003152607a5640740c81c41c0490450080ba40312080c2d6540c070603400070745d00c011a001107060b11480d140d05002c0d9629509600ca6206000d103402c0580b840d41c00101d0800e041c481c10703c1c00d0300e91000d450300301c91a80138220303070840082262049d00080c0e40401e06100600700b0307029000a854013101c0049580c1403a4582101d101102d200e4907414007240100300c500300d2000e40580e0019600249245008811034501001005044480c03407aa4411503000400210f90751190380100d50300303940c4040341089000880f40c074038802d00c072051100d4402400b0001d01c0c06424010103104036000d034041d142c110b41c42403006000d4400a8100480141001030070300283d40d00c11481c19244104031051461440090f01050051044039621451200070351000400c580e0800c00400d5026040d0080707035080d0720000d41d14203034483c00c0c14140241 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 950101250 1250 950100000 950100013
    0x20a0b01060c0c1a0a0306080c03030f1b01060909120906080a0e0102040302130905150403120507051606062108090d020616060618140a05130f201002 66
    0x501e48240d903064045840388880c01440b540303800b8418079a501c00b008294000000140310101d0130703890f0084a004109410040000f40740c0d500001381c50b07024041c1e06292081010824a50302c2544610900d20400340a008200c01c6441d102c80c4030242078038000564100035030460342e07181588101e80039003c44071183c0d101c0303032030b0b840c4c102080c8003508122200045964087c40f010015030744000c0818407a0460305400501424180380050404150b5054266041c04440411002c01e800804285880c0103011000907107544007a402e030b0b880c0c007461030b002c10107100081507402080b0481d846001a0703400c0c13240700300c90030060085503119044001002856030030144910300c0c1c1424421401e1252a01c010607290400c802c0d0f03103001a0708004050181e50550300c4440803c5480310011f5a84a031031609402407003040b45440d0707050403545000d0f0081082a41d035070300040c415201120300c10a0380d58001740c2101e56641034181103141500c541071140c0031600020169030180b91082840142d40c182c1d4019103207 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 950102500 1250 950101250 950101259
    0x3191b0f0203030730050c030406060f1a0310080d020706090f051e0f130b040507080f04030f1e030e0f070303091e0b0d0905010506060c0c2404080a050d020a0b01 71
    0x18040c205c00c00344010080311030f40907894501401070302d1040102005440d1030b45480c0c01d10000b91802c0d94010407200310544000c0c000035580104030460301240c03d2469581e034480f80025020001158042411805903002c2107085c142e001c40c0d81c0f03046030000d9685601c100e0301e41c41c03070201d401c0242c412103030b010680d40d0341e8030403031480001034075000c0c04000c001208080001c00801c2100301c0340c00b00300c0751550b035808010b0302c1464644120b640080c450300c0c0c00066450301142c400c410400c0a0005014070400c21001e944441c4a00209005109041018000d1803042d04000c0c014218900203e19180204901c0840c24074001485100b00d17509596021807952902d042040f81c0244194814411000c1c10781c08584800c005004084080c5645c00c0007590800760b081050131a07034064445480f800007000400a07240000510030604042164803000c605040702c01241c04280200d840690504041000980541d0200751581020f02800c15a1901100e086040762640b8141c0300040414030007100600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 950103750 1250 950102500 950102537
    0x30e0c060703031a0a06020d110d05070615051309030905100906180506042319052b0c1802030f01090b03010e010f0f0b0d0804030803191b0f02030307 66
    0x1589000c80d04148000c03044d15801051038007510f50004000350717101d000200a45a13005024588007031805000c4d2102c0480910000c1c420f110307190380038080c1c68035034644402c4c200d000c0b2081e02c000c2c0401002204240d81c2c404aa40207402001001e401081c0300e00300011b41c40c1048040b4000c881c446079100440306d030030040243d43c914010038134004141c043e140003050980301d020041028240001c52569540d81d11140c8101544403c0300c528000c0c0c41000070325080e01070810114060b59800c4a034944051210b00c02000ba104008040d0441408030103178450a104900f10030000b600c82903400240349404642010f816440f05035a070100d180005401004200415401000c2c0c3e13010040001c1002044401d14509642c0c0c102c02c2842c0c143c0c0d440040d4145552203200380d01c4112016102041d240e51540c681400740e000d603210180c0100c000100190310706028400150000706022010844107901900311490420840c010380080356503084641c02080c000030a0340e11076002a641e04900d08800404007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 950105000 1250 950103750 950103761
    0x1707054c0905030a380103121d010f0201230702211806040806090c0901090b090c071b2d210201050c01020d09290406050c070f050a03030e0c06070303 66
    0x144018801617030700c0d60700701041e01c2c0154041c0006030b5a580c00ea5055080017600100c2c20300503642070209004501e071121025001c50301208000b400c0102c420420074400b079000d03160800c20ba600c50703281d600342000c28911244900f03010300c1c5603500700c5004050903002446102002c0da0300c040b181100380f00001a240141003001c011a402810340c908142d96009a10300d0214281c54103075407600320036070401540c00e1000341ca034010300c0c4843c002c4c4111082000071445a46001d081c2410b003003030019180d03090040d10801c241903044d84003000d40c1100d41d680d9902065a03030b100c1c90741c400d60500c10300d240f04d1a41c030442e50005550704600d10362004c0302ca800301d02c0f8162816906c101d06208060041038214402840a05405420ba08000c905408a440c04c4060403201445200e591030781d41c41d00c2d400e400280c20f41e540c3d0190707000304000f42e2910703523500462560084150040164031080205010098045030f420701107803103601c05102c50314003c2d10a030745a14002250b660000024807076480440c1c480d4105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 950106250 1250 950105000 950105033
    0x10b0d050403050d110325090927050d02070f05090a02090114030106090609080703230307051b09060a06120c030212070f091707054c0905030a 63
    0x200d103130040c5015080c0035a6051307090110762603004420030160003c0303085201024501c11000310001a40010003030074140c9540100d807941662440448103400c02411008400420401c40300032020b031070310f4000d0f500e20000d002c480060181810001e50100300400000644100070807000465583c070840000070342161800504014559200d82c00c1c03100305600039800f82040d95540f0407518100100582124104d074030140190f03100c0c83d0200080345000605d0101404500910030220520340010343c614000c1140250582c0907078420031b24050758042c9a000020420b0310f65040c1c5569040800a003615180310748400308141440c0d01c1c0e008580c2d9071101c6421070031418014140401c400488400a00468607000401d0801043c031070000c2d00428440c0003806990703403121a040304000403540f10700241c81031500680d0700c1101c030b00c22404503565420a00c103404042260504914100410764403080c034100c440c440c0c410a80720003e5201d81c1740340054820140040c0001c0328941d903070001d1400b08040c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 950107500 1250 950106250 950106257
    0x100305100e030913090615050f060c0a1e0506010602070f0816090b04020d0204030f030315060c080310080303070801090c0c0302210f0a030509013b120706150501030203010b0d050403 80
    0x55000004019114121914407118901f0324620706100522140501c030b6083d0364803900381070214084800300081e80c0301040c0c1d800740c944044011911a84050742038007550040484c01940c0000c03400075400109281100d2080615014031655104106e46440c00aa021015881d40ca501441014141d030401c8003600c101410047c600743c4888404001c980040e0801c0780e00c0e03806413603c8418158180180200203005803d0495003528080010f01110a080300c01450201c0120016028a40e10260300c2c0085c1502d01c02d803035407403070031110040200809004040b00c551400c1d07403030403c4a01c545000b942c01c0d681038008290002401800441c0c0c5540b42900041290080005a1040003400e001d040c3d110340702d80700460b80381444061760f0300b521070021102d4142e240f10b0301e90024038040204080c0000720343c030141b18100c001ea050030f1818079181c1544880c07640000100001000099800000860045400c521045480d0001142a44005c0c8240c826030042481040340c000d1582e40a02e4108c0c1c842d04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 950108750 1250 950107500 950107511
    0x7020c0301060902130e06060412020616050c120d0e0d08040306110d0509150a0e251802030f010302101119142b090b03100305100e030913 61
    0x200000c0c02c2d1480c5800004045402091000441c1a80403241e0b0240c0f82c0e108076020145010030100381d00e03004510580350060020040b460a540720241103032094042c4c0f200400b40e040407400c1042d0f50300c0740e83c0c01250069008101c400c0000c000841c0034a50300005558101104000504018245030707241400d4509103410030000000039105d21400032410100201680c5640d10805040c04071364004040040d9900203020440c1c0355400c3d09205a80010690000220302e151883d02c54908100c20241074000c038401c83c2d0b8905094164150a02203130311208001c05c8240c0000c6445044c0d00003034404045442e1418014401442c0ca8501400008810714002d80388001144030107190600c1e02100c1620301c5200a960400d115441c1141c0f21400454402044c104104000307140b446e2080d08a500344400d50034540710300c21482041c0c004010a402e074034075a26820284052100d4028505c0100c0d194400c0741c41c0201145c0f628092100f940520102071400d0040d60000d210440e1040044041d1140d502c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 950110000 1250 950108750 950108773
    0x11203021f0b0909010903080c250c15170c0715020a0c0212150106030b03010e0a08090306010608040c060f05040e04060605030105070516020f0d0203030f03100b0906120702 76
    0x244801e001d030140080812007001d8403090000c900c0010b081300749242d06081000c0c01281d04000816000000c400074103640301e84500e080d1000c6203d400422081410100c9000d00f44400481040306440c2d0403000f58800040742e290a40711450354541480d20305811000060305c030205034000e00f1405024114030b80c4255040d15007082260f1014a804000c14500c022102c10342c207000c031000b64002c22401c003c01801d045050480e640901c144544000c042e2070700410700039a182904061621083c000c04c48004401d0742c902416241c002c1124580648074030400041c0d440d00c110384482c021900b02000c007000a04121045411102c410314010a01c41e0400c00010079800450407280301e03a000b4500020414240400c0600703480000e40481300304082400b901007030032001e0709a41c501a0303044030b1000380c03110f0380800700d41d4036030340040041c0d4140004a0820380111040300210302c0303060040302802865841e5407000c504c5000d54500950414424010405040019220743c1d410501c42d00482c1c1084040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 950111250 1250 950110000 950110033
    0x190b010312032c1006180c0e220f150b03040c05120a0b0c0901050a0e1201020403030c1b1523030910361b15020c1801120302 55
    0x141904502082c10140f031480010344203008000140400034010701506282203c280c07080144040132020041e46c811111080b5070003000359845840c00601384031280002c040300c20b0080300d107030082c0034078231800c15580c0820701c62603101d00307031919a80300100c00e1001e01b00b080c0e107a1190070081c03040301e01d10500340d004681c6036038000002c000c404030f0100400c3c070001d90307140c201078400700505000c0c3c0e075040c1880104003684c0c10400f5120890300d180b40001780c450f0150b000550f41d051074610702426501c0054040309240d480200b0035012400740c00c00d40744014403c00c40d0410410309100f1420030070020100400490300c503001009181c01590201c5d1150f403128040f10f4996401512584902d83c8400c41300c241c94150380c0100102541e090b00f880d50745003010300c4003a032807072190f40700b900c8056081c0b4811000c11004c1101c0c808504080365943c41c1c1140c5449015200620424421000d4440d1071903000641c0f070b000d035500400820850700b900c3c0d103929002c2074002d4500d138580202e0070360182e80030070240300030b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 950112500 1250 950111250 950111291
    0x8011e150332100203091b0307060e0a0f09020c160530010608010b0a081203010909052b030f0b18100308030c090a050315160c1211190b01031203 64
    0x3c0c80c000c0140e1360f0400350714407460810120701e80031100d8000e26050f90b19a8010a01004650f010309003010b207001202c0c002120b803a1140c016440641c1d030340c840817544c4451a4043c000e11050700040b21484a81103100c008020700c2840741c1580280109011402c0844030f18102c84411528501c0c402400d090701b40190030743d503440d040760703010b617640e040d1003030a41c0b400001c0b803c01000c082004d05904400092804500d110500440000944852517101004410012448254950b000f180c04030724107940c002c400882d071030300702c00002401d0650042c16074039144580304000c0e0008104c080000c503d8800c005107200c1c010a1002c0c21a0240030000115403040e000718810781c1c1c0c4038905a500e600304070030400d081d2603d070083d60190b404240c0c60082a80c030101500e42000c440e40807240c40c913408400403900400d0001005140c401010f6040c02d0b4640c124070345212543c40007041d15030301603500380108a281d0a40401500d038040080040021840c400f5151b21030102e58940420a040409a940f04458 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 950113750 1250 950112500 950112523
    0x10f0510030906090b07140403080f0306010507020a030c030c0b0c030306043204060c0206060603070507110d050a050d05090a062f1f0b06030610020708011e150332 72
    0x140031030401070640d5001019a10089005801c1c41c08d250660302d1302e010340e00030681104160070000003c0f6003142c3c021021f0303604c0c0540c01404500d4070317070301d03850404c048884606c400c0303400c1412003802054100d292003c0c0c854582e103c40045095585420800c4050044401d42c1201c1000445440750380c0c000e410f0014040310708440405445082c685420000c680d10f9590190854001c0b00511580313544100446e40c00101c10f01d095902d500c414180f42d40c40111f8681039581c002c0308103051404202010070200001c60055003902c0c129203580f8400c0da11751044103100d5034003405100042c054540211a41891141508183c2c8a040c0720044d4111404048030344410055200010b22140007900d00c40e10b20342100d00e10720500200540c400416014000988071a100b003c0603080304048510810614000304202c80027440905140d4000f50141010359100110f00303810030702c1840652403000c008908680d40142c407d0100d10300000010780c00782c41d05801c80d1804c1d84d11141c41c05030b42c00801c400410724 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 950115000 1250 950113750 950113763
    0xd06020301150233092d0d020604080f0a02011506180609060c0b0a090209040b070905120303070e01091203050d05150f0907030b0415170303010f051003090609 70
    0x30076103840a40b810b41e1640c0e0b0301c00081410a515920400f89014040c48044e030602c030101c40e03485d100029420f00c540600c064083c0e441d8640490400480080e10b094280d90358410f030341c10006002c0c0100d8071881c00b110003400c40b10080101c0b02821034800300400102c0c9a134400000c10360f85100100050f85034960050000560340d441c0c10002d50071281c209001894241400d003451494248081e00d10b68514002629940d007000000f0a030024540151006c181e009081c40d95a141500c0e2803801c800056032000b000482d4807501144500f00b9421242000030134100960441d41c4412048510072202089181005200b03000040c3c440480c28070181000d121751070700ba4907403500105100446500401d04521055816443c076910307254188485481c0c801034590741403a0b07844407401d6028241e01012240c11501d40310381c40404408100c1280b0555445d0304100d000001c4215045940c4d02080c051103110302c0400703000f00721078584500700a00301d100c1e1b8240840e08e028251103000480e02001c03000c0e03030b5a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 950116250 1250 950115000 950115029
    0x90a0204093801051003090503120a0614010507021201060e09060a0b0405010b0706050408041e05040c020f030d05090c1f0206160212030c130807031401290d06020301 73
    0x1419010304040300c031210020441810030b01015441c006500062140c1c500488801c698810528440e42000c00400e81090880384c0e940c11444e1107a0f0f045104641000d242840d002011500300d03881c050041d42c42e03505a454508080e06034080204607070000b512042d0035036a1f00c000180c40044050f119210360328060107481a031a0450000e000e540c0c0c08030005118516000052007407495072000e0324111030f00071400148955991074090100c2c032660300902020700901315100c00401100820764181c4805440512014050007002d0381c0c2c8007410b940348140d0f504107120b0400c00040960040da070207010310046465225128001c01c9201f40140b254852040e00c0c000304450258040100070f4000a00203002c48036000e14401c001d4540b160b6400b442034010700080400c5100340008250f803130301208507598a07026981e500b00c3e15030302c8415100450350302610140e65000003c040c8515200341da90311070b084495501ca084048142c00041094942c44100c441440340130682d140301950107000d1f44160103c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 950117500 1250 950116250 950116283
    0x41a031002280f110c100f140c01020405040b0609010e06070c0306020711010201051008070603110c10060812040302060a080a0f05071d0411090402031305010c09030b13020a030b090a020409 83
    0x70000c16220041045d90100302250321030f40740c04003810040d070392501e03140c075860300645411101c00071240085134118901141e9130104c4a41980241300712141224104005041031040c021180600003000340481c00d91841000f207800d08030300528141d8070403851032460307030b480743d9400040307030050b90084d511036221501e12821940c0911030b03950001c115481c010720f0b01c0e20700a4400d958600902800c001c141d251201111450011015070f04200d036440e007030320040300b0025010340c014500761281a541b4030030225000200f20010b13048409503a00901841e00c0d00c4801c000c01d54440e100944540409581c07410380c4025080c40e40300d101d01812141da00d4008504500b11008002e0108031401c4d0b20803441e100b070000840b03d0b50b001b1200c00c03842c00e840141c3c41e695125510b500034020020040d1255007000d0002d10001e900006810a61380310b81c0d0a400b454951002c0f50809007d4048000c1d00103114a10a001044450918641c030500e864101d80005c01c4c20380c041402c0c0c1d000300008441c2000c4506124a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 950118750 1250 950117500 950117507
    0x9030b240f091f0b040905040507050105040b04060804030905090415111c200f131508040b150310050105040f0c080c0f13060806041a031002280f 64
    0x314034a00860352621401120303000542e020740040c28004020a10a048109031240d02010740002c0000800040e04c455444024201405040390101c8890044c018045241d40c0120261000e44e402d0b5800c070350429080281c03d48100c00060710036000d112482c00c000540f552070504492086100d28149028513a04440c84015078402c0346d655141c2031414004561a981e1240f1409041500c3e520702084541150a0202c2c0c8400100071749110302d180010440468010382004182180b64130351440e603520796800010040300c1a4214110004010a01041c0840d2540c154070350000090344815035084e0a8800282c5094a0460b11081e80c584800c010040c0b480d151080c0c1c604d1800281080c009500c0c0c0b41002070151100030500c906900c00131a801c82c08450480644510054170040900110380b145005021410b044880c903107e24203000e0380703141001c03c0303842d9100c4c81000980145440302c82c4503000c0001c0e402001030a0402e65441540c860b503d80d508041d444c03400c00e80e8844055452041c24000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 950120000 1250 950118750 950118811
    0x8131a0304123b0f1302030408190207030b0606040e01170c102606030c010804030c020409111003140c07080f3106090b0c01090b09060604140f07030c09030b 69
    0xe4800d0f40813000e4820a034a440c80c0c60a03031040d06640c01681c0ea52145402e0302d280c0a1034400c155003184c0045c450821540000e10001030740d002c0c442c070780da00e0fa4800c400c0040c80c1c8118025280400d0740600100040c10b1680000914030b0325140030f5860300341030600402c5107000c011a15600141000006906140032040403503601010540304016600d00400402e55072200c8220b054100080ca5001030103151080c4101e2002c641d004100740265002070600030b000d5503036550321520030506015410460b074043c2c460000705102d01c5200c5d0b000d81d9a103900b00c51136600720010540b441502084009804820100148002e5083e4841041c6001c903c0c200858002003582d00c600078400da4000511100c3d40040d00d00e0304071400e071080507a072200402d600c0c1e03001d08030100e401009400c0403401e0000b07994011606510444c8240c804000c04480100a411489400e40d00c030740302d0850100109111500c030b07400290303401c100ca041c409086550313030760b13010600e00c2c00300c0c1c00c0d80000c4c160f000c85464001c89018030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 950121250 1250 950120000 950120117
    0xa0615050105070c050d080f040806061206040f02040c2d14070308010e04030912030c020306100f1a0c0609010204051302210604110708131a030412 65
    0x64107100b440d079201c4c19058098001c0a2041c0d90884482d400c00030340c1ca04403078003c07521444030703502d0f5580c0301c14483d03481c60141c0d84944205154048034445210003d2910f101c0c1e50456a003039a810403540900c40140f0045080c00208110009038044001c0b01000300602080390b2886921100020240200140c0084000c80e024140403c602e0000c00d600402c56070644051900f80b4902e5100c1d46000d84d8011040c1d4891000700e80c000351188181a089004051124000c1d410b4500c560781c0d01800700d280b2942c50141c1c240c0c5420419003400904443d03400c0285c001c0040141d00e142042d0161014900001110100550303900054144010300307107207050b1200204518000d5081c035440f0044a40070030b00f81c003034214116055200080650383c5036001400c1c1a040170725056541d1540d420312101660000c1c10900d1025240c80001811000c00320490442482c000c1c407850441c0c071503950720780780f207400f081d08841004911650210b0790038403001001000d4425030060001d01105014805480f17028405 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 950122500 1250 950121250 950121257
    0x302030d09060807030b03010902040e030a0906140f09040228020f030711090402030c120c011815110a0203013206031b0a031b0806010b1e09120a06150501 68
    0x80800286030010090344c0c0208190030701040100405020078018000d040f00a54800d081122003e9200c5010004149500c080d68907903007547e84610042c1c61409449484440701e00b010091385410014001c09000004001030003d071800790520351080f42e14a10300c1c803101146440700b44d1081410340401280b40005421009035043c40c52075120506142e00182e10b07140110100c1d0b000504550f01800700001d071f583c00810458804102d05034041c0c0d60070341e4106507400b1480010712130081849003603100040300c2c0f00401d022440c0e0580b140445115804451280d901c0c0708944100c00103076000c2c010000e01e0045800341c0001c08c0ea01203e403034003c98041500580001c084414814a41c80103d04900800745207401070030a40e00b4840030500c00045135101a011101404480b4404211000004100e40d41013045480513601c0304070007401489402800307024841c1100410b2401d81000c4003601b01000000e01003035041180c041d8090801a19860895086a41c2c0440500803540c00c1042d8001e04030030318 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 950123750 1250 950122500 950122517
    0x1305011811040e07111501080d0e09070302130b03010602010504120305130b07021005090c03210a082725081f020912030c0c0f09061003110a090302030d 67
    0x5001200502c02c0340142c4070b00d103a4807800900c44501400310301e0101e54070181201c054880303541000d01c0a030300c2801440c4080c020a00405406480b8a140d01035011008100c007203181c80c0c00a042c0c0003944412020a2200071840c8006030714440d020146000346119000499540b40034500000e0004c0342c1d4456100340341c50b11051208240e2140c05104880303a003e80c0742c078041d854519050b460400f40514060350b6a04003010041d25400c046001507540c0000c0d401c030f400030100c004504100c200080d040c800c0e451001e00085403564800c0a00e150001401c02d00840700820035031200000400711005012141d0008100b05030881e110b02c0c01410743c010340741d000400d081c18528050f844414084641404141d9012603e8814500340e041343e0305800e0080c0b2081c14032008101d01900c03034006091a840600407080040c400741000c10a008090400400d41d031a55a1a0b60800038219002c40e441010182d07103122582d0040c526800911210000340c440c8400c2d0380c80c5104051800d0f040c00c030002c08018040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 950125000 1250 950123750 950123771
    0x10603020f16050c03070f080606010c0519031b060207020109141c050f0f0d110303060a0605341103070e0403081302180a0b010c020604090e01060513050118 69
    0x10180c800074041403000b501e402896092851610b104810040d5150042d01000180e88000f0803115007190450020f541c260b0351480019504001660805481508450808414030300d42d10b00da0a4010b110f4200340303003d0000705241c5c0200340901751088482e26800113690040d0360700550300e2402000040b001d400d10000240200b50b14004c010980001301c0a0f40c240d070010440305100985500100100705d4014113155081e1070b503104181c19a00c004588109004030b054440442264070410024180b907086030b1516108807001d61111025900c040400c0004001c034940e24100c24409a401d205825513084060400c180344040c0341101034400d47c4100d004003e0510b0142c25103a0182e0541040c00303055031020088000c0c0c02c02c000f402580042036486002500e25103d03c0d850244c1c0c04400208114000d460064598207d18400a54031032024441080031010a41200815094007000400c1596071000443c42c2c6c414622200f1002648a000520078101d81c55074860440640480602c03101e82031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 950126250 1250 950125000 950125027
    0x3150c1d130207061107050307031b0f0809060705100605011b0507032603010b07030905010e28080a0804030308240409060b0607110a05061c0f09050d02010c02010501060302 76
    0x184000c10080ca0b402080e000c00b03100c803992004003011500c4074001e54944d402d1400d20303200d41c40841c040b030110b5400d03084100751400c3c1c00c141c07014041d4483c500549109150301d5108094110f4142143e010108100c10b000050707050003048040104000089005400c1c03000140c500d4200d812130b031a0011150011002003003000804004030380d0400c41c40340b028008840803d03208018080005002d140020001401280400081c008940a682d808442c1900c403001165502d04012643d82c1c44040b596010b2004d0300103991007a503030072044a07a42c03952541e40c14290b090603803481040e02c1d20400883c0800c2850b030840c40c020f9002c821441d1003079490440590303080f6050b844440050244d699180c600f01000420780c0400c1c03000c0c400074211515000e540c907014010020188015024204c1d0200026050400304140e070540600542042e051002c00c001401c020001035002c585095201d50b006400301d0002d101d01d1841c2c01b0300d58000306030304640c203001a0940e801030780602c082510400c101030070940d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 950127500 1250 950126250 950126269
    0x60d1509020f0111122d071e05030a0809031909031a0112030e0f1309060c1b02090919080d06061d090a090602190921120903150c1d 58
    0x480d0804151103c003082c840205d8406c0542e4a5000460a86808610854400040d01d403181c030901c203801170741c80f5803202c00242c180178070802042a481440010701c000d0003424210391050030001205c0c00c120307103030840c01502d4010021060109081c40418002e00981701c211000f4035120b510b007100103500d4100815619440d154002c1c0410100d00d00070126680e5600d00d1014601004113410b840103211941200240810001110560b140284d000d04c51800741440c0550b050b01c3c10703404403180e0019024851110001400302d11103000c4c4111006407c42c140c00100801d60045440b240c0781d6058007416021919030350000401c0c465074006d4100c00b0980c400801c140b80b80700341c40c00c0c0e0850b20307401d2010028010384600102035a0010031194600100c0030110f401c080c03025500c40c44142c0e51034001140c400544541704c8580b1903218042004a5003081613003410b4041c030b250409007a9566111203084c1d854a800078500240c8078410510b1095106075400d00720710804281c0d011440d00301002655500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 950128750 1250 950127500 950127523
    0x30c0405030606060a23041d15090708150406030803040b0601080f1006052119152411060702160e072115080303100f0f030b060d1509020f0111 63
    0x40540030441075000446c1501c0040402496166408410780380340704007084220780b00c504000448034580304503d0112015130041106403a511f049864401d510307161041c0034a40e041e000354840c2800400181d600000b1403089005021071480c50030000001030101d00042e080c08550078120040c00341c0e0b40c0c010b1040300201c42e036504007280d60381c108240030400b50030005680d110180d509010418214120716800d044001305503800c1040700111018528048800c2c042c03003d01d01ca08a00c1c0001420000065094160755410407144850280c6002403a242044615100503009101782400e00c0c4041801e2f40054010880040928944000000d050256041e0003484640c240400000c5552060307110304061141641c82c243c01684034540e41d40e999000340c5e280210611207010000740d1034190726040e001da0300c4084180040c1d515544170114800006000385900407810f603201400182d66003084c0c2845003080d60042a410781c84d004214010700c61130000340c107100c50b52070100c04c1030201084403001c1c0c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 950130000 1250 950128750 950128787
    0x15090b0d240603060603020c0c061b06040c0509070e1c0318091401090606090b090a05120d1713032d020708010c0c12030b01030b0402030c0405030606060a 68
    0x1000e03240805805071588606009030295815089248404881e45060503910261030900080d90781d45070840803031040b0842d2406640142268000c2c0746010f00050a404c19050183c01c0d008506c4460340d403d14a00342c1d01150401e942c0c0501f005241407003481158000c2007801c0caa0780a000000c08240c0003d90a0008454503250700030000400d13002d009007085044020013007003c0c030343c0c49014402c02072030b105040b0000c1507a541c1c0009114085400b501c01a00c3d0290fa03030380642441c0001c00311a90304000c88040c0d022404040128042c0c45000c89540d0081100d0018503420160420140010070503000384071141e008001040a6022a441f40200084d031518003c11401280540300303117000b21800c81a140300c442c20304e24041256002940d40300303654140c4020008046c28042c26a28104900c80007044912894481400d0a009a00031074819406050101e103d610000004080340d200315010022640c001c034061000d0705041118039404401620301a2030000802005000e030882c1818a0850 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 950131250 1250 950130000 950130007
    0x3030e03070e1305010e0f0a03050c03090409030905040b0d0201091401090815040309060f0c151b05041802030903070f050a060e010b010f080f070e010c0b0c0306040615090b 76
    0x50303102040841d004120602d0514403600b040c4078102c140c1e4900340300a071074a6080c80c100c07200c51000442c030541d03003030302d000010411a003882e68140c505401c4201c40703000d5400305010b40000c60b1154021540241d100342e40b086c00359410070041200319511049800e014050400d42003005076040035a13042912a8203118804404504004813008440358204010030f00034200646984000300014501481c401d496020489031181d40482d64440c0c10540030002031061f041000c080385010001c0c0e16510329803a40032913606091007001c0c4d8001055042c5200081000800300142e0f1100c41c2c0c04482c20200740300551030742c10102009640d0b4040c49001801010b8031000c42020010200010707449140d00c000d0501000c100e62410500030080d035400d080c003043c80c1034004e80400344550711452043c52180c143c3c04c0aa00d0354202110303108500c203a40c1c0e060020003604800400d00d5203441d288210075400c1c2060b87c0785042c03000d01095070003981c00307a013020b0110202070000036004a0038009a9001040007500c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 950132500 1250 950131250 950131277
    0x10b0c030f0414030f120a0318020d15060b0a0c0b070302090a1508010603050402030d0f020c0a0e0105030c19030807060b04060b0d15051014070c0e0405070902130303 73
    0x318812060400740c20725000800040100100a10301c2030000110240da220300048051207490b00e11190000100300780c10400048040e00a81c000001811002c00001d0040f507644d0128001c003070703690829141540503c28100c0140b072036004280c060900300304079500b44441d04102610507001624000d120030200700009001c180300741d040c2c40007070500404850316207a41c0d01a100c25001e80a10440005040d4000852180e020303018160080d54040c0040211040002c01247c0041a4905020441c081e4107582c1516549070905580a418a405c0024440d4540b40405103803c1c0b80c10a260700406e0342242d00b04901c902100503004985c0c10030f0000da51240e442c94004000c1001e15001940285040780c081151351418001c0c0c00c0c4486840d86c10811403036010491b0407a070079184599540328904411010344503200d4074010b04094040c4d010103080064680d501c1581c0443c540000b065149880b04120502908101d94001044001011880d00e540f000083e0a04501c40c00b000e400d11010407000341 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 950133750 1250 950132500 950132503
    0x3d0e12010e0a0209150301021914040f0311010c05121803150c0c070503011104030224030a020d090c03050d140f040b16061b0e030c1c03050409090b040b1e010b0c 71
    0x10f0541780001d008640e516406901c02c60514510280c002c0040e4030f030426402405801000c44041d0740f045200c01d81032625550b581c01411400c03500c92810051020741c070724005041004540020010107031080d0b02c07420f0201d0b19101d01448041000d100b80c0c04224051183d64002d60380c550040c41000b9455950301440b1200c92501071070b40d000c07039050741c40e09810380151252000a40300f035920880f103000c49a64000080c0c3d03003c8180700481072102c00100007191406404d94000c00000101d407070301040808580d140d00441600691081c1c82d240c014111003080342c1d900908180710489100710681c1841c0c4498030040382030080340103d41000e03000244d003030801e1b5041e00030a25241e44c010801e200680e0004080340351100025a1100882d441c40b6039000980f401140200c40c000300600180403640340388003001d400d06c1954905a00340b00c4100702c081120000d601400c28a40d005602d200034a060a2070f0490071420000d0442100d08503080c075680d008a441c0c118141145d1365019501d4581d6050610305 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 950135000 1250 950133750 950133781
    0xf09140c1f03051f0f0e06040524030703020909150906040b010608060a1707080c01030b090a02210a2403020f0d1b1e090b3d0e12010e0a0209 62
    0x5007484040701e44d0004514583d040700358207071400800d9150040e150741080c00141c5c1c005440e0028010303000c2d0198001398000c01e41242119200034211001f440e600c0e00403901110081e50128260b802c842081035140c01a4500c1981010700c242c0185154030f461b40307031000c0c50041801407404004420006c80d859540d0680d0501c003603c00712010700129900014441da9586083c0306610f0103010781c22600382d2a602a114030304418001810305c0300e030781e0303180d580da40003c0d03000b001c500318400358408066403100080d00d40c45216030080c52000840304c003c0200c1509030490b03140c59140150f42c0500920068030303500c880340714428050350080c02c40c510718607000001001d0034480b080c040040507000550b07004562039111880d0031104a032800035485040d00d6084c1c2d0101502541c1040321200a41c1c280500c000c84205560440c140c10480020300145011182110032402800a0b09100c8804542c2c0303170030004101440c280b10300801c130500800500b180c94540c04100684200500300c0000c0020200ca041c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 950136250 1250 950135000 950135041
    0xa0906020403140c101e1b050d0518061c050703140a1a040203040b070c050a05150105011701060e040e1e030304030f0924030f09140c1f0305 62
    0x144003000d00400a443e554102c4c0201c0148900c038445018081540a4004040008642c0340b200052410003174080c0c030f600c0c00d20034040302a802210302c190b0200301c007406800c40c0a662075841c0b035071740c0c13820086004040c4c035242c0180d44a29000c03c410641c0080e40701448038840410f2002154503580c404003907004042a07165100203a54110401925641c3c613444604410350f9411016400524207091008031700045500400b2a10010080b07009540900c0440a4a1f4801c40455120600f02d584d054205048007003028200301588005003d03a6803c8644203015044059826039a98904140240040b546034a02409283c0d510194419081e0a004004040c0304010b0010541e2121701d00f01c41c2d0382d80c006c82d8264006040380c8020000244a00b0b03486007210310380c4070349501465880c0c1c88100402c40c0d101140c13040c150b0381c00041625500314045da2085d140210b0054a0241d03201ea07145051003410034517a44640701000d003140002901d011091a1405a464005602d54441ca00007078200301d084103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 950137500 1250 950136250 950136263
    0x30c07031b061d10140622020a1706010c020d08090d0203070b0301051809060c1303061d0c04140a051503070902070204140408090d030e040e16050a0e0a0906020403 72
    0x1064200452140c1034260f214803140225402003a5400407641194805240c0c900c0ca110842c02203581447c04145004410040504c0200c1181d40d143d80881241e0044110f0008a505459400740524072100141e44c48207003070078550340906440d800038041c0070490800800d0070102103900c144603124280e0151080d40c0c05021240a2a2100c0e4800840c0e0405d109061180e000100ca01586040548659000710a050b005040c0780d19105034428403034000003107000114420383c0700040440d44500980900800c03503400290400842141c8604110451004a0040782052820354048101040c1d203640002e41d15030000300c507126003100500c0030855845080c0e044c4075078040404d1130f10307040c1e0003400000c1c800c41e410009a580c01c0440b034607070041120b01410494003848044028208451065050f6100740740c0250200c0c2881c0c0000c085503900040344402e5400352028040c003000398a82d403005000100c0b120044589010741030844910002c016180c0c1d213840340c030400208156901a500599031151 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 950138750 1250 950137500 950137511
    0xf09062e0305070e100b040b030705090a0e070909020c12090a0e070801060e0a030f080d060e090703020306091506060f04090f022104111011070f08060c030c07031b06 73
    0xc2c40b5a0742c0c2410301405900c02003400210ba200c50300ba4181c903044600c3c84c0782c0c803401e06241c8600503415030001042541032001c1004039a00560701e501180000c2d0981c0f891134403c07400c048400404594594205881c2c01c1e00c100103515088600103080319245803031080350f655800e00701000ca104050650701c400c105500c0708050040040c0c01c200e0b81c1e0305841140ea00d02c0e5948420404102c002c21580c480034160400e058100408616078030010203001c4901100415100c1e5134003890030300304400f114514107075001a0000e0003140b800388455038001540304003c3c4a29101e044003c0e50280e4041c1090340704500025600a5690031001550010701001d20f00b082500c810500c60f00c081e40c01052410280c80d101c0403094611407100103510300880e00b00325030342050703040c000030f2282006d4144c8020050291410300c0c444055070400c20780d00035085000d008880c1c0c0740b810344054a492406062204140c40c2031080000e040c1402d416500704542502c0d00f41943c450b4804001e9180c0c2001502030180b43c02c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 950140000 1250 950138750 950138753
    0x15140a14070201360507090c14070f120c02030f010b1905090f1b030a0219021f0b03072105061e1902090d1109070306050a05090901020c06040302060702060f09062e03 73
    0x7640308234108011038981c8125507038404a840d489202c0d814005298003554070041004c1a1903816903a00040300d824440100c11594000901d01100555490403e82d1079640c0805030741000d1410407264181c18154180142c181000a0062100104840410000300b400110b26201042c44d028956001c07119466580c1880403080020b580001c01e0442c0710075a840d18081d0252000031145c050b0039250420741c41d40c40d8041000c102526524640641c98460088041004101551a0380b44000c2202c0e040902c02d0242c50b100741031442c010810005000300c3c01d0380c14002c19165a6440e840090100c01c120560310409510b0300900501c20403640088c1c03c00340000410036402d9500b10a00f000b204d00079060741d1034000c02c5050781e003140500e9410090404007007001c3c1c141103003120741100d0380d0b4002504100d074200903a80b030000100c0c1c05070010317400311013480407071031b0107104103500842d1074140d900c464a090f001c0d0030354900015014202070001032044803034408880d95450051010307000c103000c84594a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 950141250 1250 950140000 950140019
    0x90d030306080d0518041d010e070f0902091c0519050610300614070513060206010303050a120902120d090906050d15140a14070201360507 61
    0x141d000e41c440503c264207000c1e444900620a071080f20b0111145400d41d800c40c1d1080c4409048650310705807120b4003550b50544546428000c0c02e46000041c001801c1b2a8a000d201c8464040d0982c031000549204000300f00b00c80e140c010920644506001c5255400803017071503d10f00d0f05101c4160f0841c8001d0072142c200c204800820613038050503100c49140041030f101d500d0104071a580f4404441c81a500e4030182c1020441c08150480d014010440003ea42040b2049070310341e0f0b502101d0240004030001241c1481c082c405a0400243c5403034402040107605540e0040c04c5031050780b07110400c0c451201c1d1240c1000c1c0c066041030010581c05010080b0342d244406016582e5203030700d03144d00c000c40c01c041c030301049100c0389200d0316080342c40003408d614801c03855031140c080303e0300c0041210604903214102010b00c2403844464a02400420701c000480c001c107080d48100f2040054481d01c1164140110010f05401c143c0c8070b01515071140d14154041c0341010311580c41c840d15608001c2a5004040001607810f030f1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 950142500 1250 950141250 950141261
    0xa050103031107050a122405100f06050a0c1407030b0a0b0d05030415050c0a030203040e0705070b040204020d060905040b010f0602070614161a060f04060e15010302090d0303 76
    0x110b034039164142410518815160211030203010f07086100c0160400c50f92001506501069014580585030302406410920031480d10507034800605031207a0601c9007400d903106d2410000c05940c007090140d13a06080f001040c0340303c0c90075036004000142d900304080c06135081d601c118445c0c01d2401c580d6456900c3c40c0002031070b00201c42024109103001e40b0b489081c10940c94803403250707a208001e1031403d07040404140a4102910b14602045414000001000c4040090882c80f500030740080d901e440c5802802610b03520018829820403609218210000d80301c2451203402580c12103002d030300c800384007100300d000700029400f0352061810700c014802480007950320a8141c40462601e92400da4503401c040e43c0d544924800e443c00910411100303081447c0300009440000001008044008089d49544a5848c44030703d1701c2c40d50a158070103202c160314001301d40c4c9103040c0d0152001d000303161411a40143c1c070b200c0140782c0380f0343d440010140d5425a11070341c1150211000180220700020807820001c00810f03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 950143750 1250 950142500 950142503
    0x50a1415090a060b04050d061d030c0115050102100c020316030512010801050417090114030403120615021f02071a04050f010203060904110102070e073c080417030a050103 75
    0x2a44103000c2030180b4814040e107815104000d003500d24091506082c048000d01003030007a42c03410340c0e41c0000d064040e94020781c903a0511002005580707071049a2045400c603500300c4050454001c8001c8200110798010400301e43c42c0c52041c1d400140140c0417807082c1e0451044081030517114610081410805d80c1080140000d541c1220215001ea0b03220618542205c806840241800300d108100e56100b207415002000c40e000c040c901181d002625a0001905401c00e8400300c0c0407800c2008103004110803482944000c0c0394901c0a02c10300149010040d440394203510500f1502e03c3c00948040701c903150b5404454145501640740c1d01c01c045141c1a000c03c3d40c1c1d041c0c404541a02483c40b003124814414002d40b030007118020100207042d210b0782e8845030150661340e14141503009900e00082e2601a40001c0742c4500010f8644004d135449182418141082c170886802c4680f40c6140070489461000411603500d00f05803e06002c01d448600302008440c502da0b0140d11114400001c00c4680301e960382196049a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 950145000 1250 950143750 950143759
    0x6010315270905280807082701050f0c011803200303010302090f270303071b0506011e08010213061407121202090a1214030705030a03050a1415 63
    0x41d92602941510342411002d4669440350140300707284030b0014070020601d040c007030503880768003103695038131000f03801074a8107170f80001b004126104008017a44da0b105070380c1e40c48501228075120020010303200d07000f01a428650f0b00000300c0c2401d40b0007401d51258007a280e400750002c8030b070007176444c1c01840550f5248424810305901c5001d840c1d00c1c10004203480c182ca41c02440c444240d59200150300c0b14010050496410043d0030038010151450000882d003801011400307103a417494140405040e142140c41c13b4540340d02511800008a00003181c1241560440e08030070508200c50410f03010440426001202954400503803800c007029070401c04d904031003644d20ba075400183c1e003c240c06514040c00d60040d201c1c0032218842c255651103401c105c104015070880050504528501003548005144c01052820020070750704018443d00302c041c03001903100d850040d03280c0662542c0380c648078024000c20700c003031507140d0f030200f12400d800e5005101e446a032000000c0b22441d02c00407061280c83da142d5901d024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 950146250 1250 950145000 950145059
    0x6011d18190c050c19020604150c0606080c030c0f0f0a08160b04030f11060d1a040b091014130f020307030b0a050f011d150c121303020906010315 64
    0x3850081d404d60390034078141c901600b21400e4030345509890701c0300604120fa00c604100008240c51107a10120f105c2d0101720f941d41d051615051402c03908445842d00b00c400190702c5440c0607a0140c1d400218054000e03400e5884404142d503800103d010401092980c03980650405804a0015000a0740300c601c8102150105c0d445561107500d40043d100710300015050304201411135011501500724000305a5014254516080e001301105e022140050390548055030b001000b9081c52a003400740d82c0799050100c410301086d04203150701d580c410038940309049004d9828003094003030f913840c0c02801034032031a00345041c040d15000aa18100030360080743c041c00442c0c906102c11981e4100440a0030640300e0103080c581429442000546a10070321001c031042080002e003580d000342d251040c1540781403420400554071a401c40009500340b9084501040703c5000078803031141070500d041c82c40d00441c0d4040d200c001d0304c0c0d200c48004070050401d403004039135405000c55002070780d240d81d5801a610640080ca02c1103c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 950147500 1250 950146250 950146271
    0x3061807061b02010503091608070614030c0922140a0e0706120b0604030609030e01080f040b06040506040207120f351806090a03120506011d1819 64
    0x102c9600110741e080e4040203214001c030055001d2001103400a9500741103030f021410516000308020659088500c3e00e030440c15040181541007031620344010314001c1080d0443c50808620030150040e242c2003031051034105092140c1561110588000c1483c0040a02900003401503540d0348180c2514118011464022901004100450030109441965845c1200e00b09036140131006030002c0b00c00c0c640c2c002020000000012040c0c410007854511940356031880914040015152040c000e2044030f0242c40d0008000000340c0403564954026000c603800621034846c400071400038002c440b0010310780450004501406a08401d40d100b020781d441d03031482090320f02c0c801c8d406855400400401c400704116004203529800218005507c036070f03045211240354002034885450408180da982003103030011400f040c18154410003501035614444000e00182c10a040000e003155020392410f1921103601034901c02eaa500ca01590200000311071070940c407410076600c22240155001c40368420140703403014404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 950148750 1250 950147500 950147507
    0x60708040b0427090203100c110601030f030206070f05090103020a0309020d1a06010e06030a0902180114090a020c0c0d3e12060408071a07051c020c120f04050306180706 74
    0x139110b80d000d0007911041a01000d802d01801c10002d41205000b03c801125010040c1003064500070f40c09040d5410300c04040b418040d00f41007020300303e80e0410080340045008507800c1011210709960a10b00181d13140c80300003048005040d0303031000a60026488088409110500061a26403580c0039000c1d429a1520700040d20001c000c43d1905070081d03810320018490000e1680301060460001e800c1c0d0312040403008004840075001d802800008040d001c5210305400c0c400c0110f0340c44040680114541810f03141119525442080110700c180980040d8008010740e003607031701c581c2a80f000710300e2512484c443c0c40404110041d0100541c0d2810003598804203140c003c400c1101c81c90302d14090f00e55525503450f04880c692120a055426014020089000100c0444494841c0303003d992540d4a804803100c005c0011460120480d880c5401800345041d8094081100074207900c0700103106a40d484640d10400b40c0740030759840b1582c076010303c00130030405030f240d2040c08421a4100c0180d401040d19080180c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 950150000 1250 950148750 950148761
    0x4061805042c03160b0a060506040f0311130f090303230403050a0203120406061e0627090911090f240111011517010b030a02060708040b0427 62
    0x204007096072041c00b682040c00d0001c0032400c0500c4181030300d24000419802040c1d00c1c6104108881e0403022008200a032403a40c420711000d1710048032031504d01880c101e90002c103e0102d00020703024203c01c9020704200d0355001c508440c440c1101d50700f0300c102800c1001ca4002001100300a50209060081003407400d01d07a210350a241a803a0184400c1d40d07201c54400b00c65640181e2031032015480104041c001804017100658860b46c443c401c00700300300d82421900d090390010345a103840c0d01c0f00c2c82031040c0062a0840700c0c042020010400c1c210812803550160492605a80c1c015244e243c904000c1d50280403008102d0380d1103450a41d0512015150011001c00d0644111625010402d031145208000e1070703c070300303502c070710807414035004e02c80200c1111840e08551500415003590140b4140401840c880c01501407507041d545802003203100c43c5880440d84850034284021b103d0140042c040042101900680380076042113400f064a581c0c481807001d4030a2911900c035540c4d18109120380c4042c58280c02107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 950151250 1250 950150000 950150021
    0x61a06040f0e071211070210020d0f030b0d0204060e15030703150c0509061b060c0c0604140f0d0507020315010513050a0e10140f0c04030b040305040b0406180504 71
    0x1104814601590007900341e402801102c10411009003a0304d182d442801000c020412180f000707a80c4200b284100302800c0d12015540c0d0030f5400086003800042d40050407540c02415505000c141180d50100040070078500c410029403080c50600e010890b800c4402025100708520315005142d46246000c06603100300c6480014401510320742c640800310b0341504205481240c90070800c0c102400000026007503080f0203144610914040c001082800080001039008200c41d821149450880c1803807a4503800c0042015080345912082c0c00c4203035504010084404030584181c0d60452956032001304264041d22042c1d12a12850420006025440342000d0403104000c05420f43c0c21601e165540c083c14004014808550359031461402e008010302c03020b41c8800300c5140000d5008050f401d007072465200902817064022841040107021410101100c060f60703040f2402c50341c5565146001c440a21494108541ca034602050008105400100710071070035071b00140c0c494046444106000894840008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 950152500 1250 950151250 950151269
    0xc0d0905210403080301090e0309060a030e060709080a0b1305030406211a011d10021617190602041a0309010e01050c0307050d06031e021008091225061a0604 69
    0x42111f6130340790f40700700e81903240c002c19030342402029000a50341e508481d480d42c0210343c48458902161900780320040e441007032400e01c80d0700700d420a003440390307925507500c402040700030b050b000b16011190200780d0101e060381c0002203942d1152906401040407441603950250b00c0d6841c000204a18003030300034180c0c20001d003e0f409602a0b90134004441085e41ca080c480001c04041501b00c0684d215913244109905c1190020722020814040340d08140005a001d41290a410008000032020114032042c138400c0111022181000e11b041c520000d205680c45100070070b00107910001c40c9003050001e18400c441d01c4008111f0880c04140791030990f00201d4941030000750400010b0a17107801100a0302c0141c40003500083c0480c1c0301d41d01d1043e813040c085060182c0220340c161010443c85c104009080c481010324090026080449507030307035107070303000d628040d0075a8021461441c506109806074540354429410703548a2512424a0002802018120644c0192001c00516107003040317130445049a03400741 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 950153750 1250 950152500 950152507
    0x605041b14120a1d070303110d03090c0603110d061203032415140c03090a060c15200d050403082410030e03071101080a1e050c0d090521040308 63
    0x100d80310024451340d1050040514913040038000210100f104001851207a281c2243d4804025055071504d1500d203288402c050414082100103820a2113000c100c50442c100070681400c48012074202e401100070313481c091442c0090001d44a040201b1100710785010b500d042012039070300c05070322911940180c0d086e0582c3e154030808101e601c181c9042c01c28080d60300d00d0000a030688000a400a0380c0c40500501400e510200ba403004034a80105040d0041c0040e0600502440b126601d0030003122080071a1b0000780d80d2484000c02c600d213603240c00200105002040c2d03136100e2103034880a00a000070344064000410080c0015001300c070f02c5122068804850a0010f80400c0034010001c03018000c80d402c0d020591501e46400c2441d400300080d240e0540316640f28071400381c80c440010b10ba800020f120341606400c20380c134154036034140ca0511001c00814800810316641e81031058a0901c0384110305281c2c50b1034404110240f250100b990001d0386c139403900e800581200190340c4c4120780510701000c0c01040080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 950155000 1250 950153750 950153761
    0xc12141602090709050d11011e030501140402031e090705100f17010b0708070c0302180a0f0c09050d060b0907030207110907080f04050f03071a060d150905010605041b1412 75
    0x10440480c0c0b4100514207001c010f504201e09e00d95401d03111b01c000d00800c1e100c6005100203050400c00412401054a0440c2142703040c03002c3d16214624007102d180c040800740c0c0410100c1030180b2000c0003400016018043d1130103101c0005019201d410800340000701111605022155a88078a90407a0041c1d64410304000b00c07500c0e10072032640111803c41e075050143c1c0300080103031a0000140c151280b00c1c400d850070351500c1d00700c000584800301c07525501c00c0d242540d0782e1051038018610700c00b0355000340e1360300d40c68464603d01800145400324445e5407045a4001300010b16074150002c05180b841400c00c20f812a1101050169001050714180080f031405000190103940c00030410b41d201e401740c2c080f180481d041124540c1184d008031402c0e24020038010300383c00c802454440d8260418000d0381c6018045007152101c0700c600e060b80143c140b0b41911603c5060a101c825007104028010040041044100149400300b00c42905403030780001c00c0001550b210103258010564041c04a0450313081825640c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 950156250 1250 950155000 950155013
    0x1d06010f051e09040e0102120a270501090c0e0114030c0f040e070f0608071d0f120106080601090b0319030e0d03270602060c0403030c12141602090709050d 68
    0x5002c400714002c4014003141c80560f81d540039802081c51000001640d89018201c0300303900c01d80081481b00c100d030030712901900454001d40400b010315001c04040144640c0f42c90f01c5805801c40c69000390402c2480417001c5000305003d5080e504a4582c0100600070100d040f090540f9884e4a03d840b0350302c00b6040d4081040ba0070715801c9403104c0755901d01901c0d41030382c484110344a14950b98102800255994082000b05c070741025107940f04118031580c03622401140300004e240c1035500702c0340c43d0041c000354038846032210094101501828600d0203860096842c0c0010340010015206120b220b40319842c4c80701940341454200e12082905a603942c50980002030502440340740f242d40460801c01181140320462441d4040215040c0040300000d40c050f00d07140000b4608400030b402504034040402c030800000707801003991441194006007002a42c51000f505072015002c0000c44800d2010019405038140c89801c1c680003800c1c0308036000f11103511610b500320340d24080f60142d60b400c61803c0d0a6403010079007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 950157500 1250 950156250 950156287
    0xd03200a11060903070b0a05060306040f08090d0b0402031b01050301060e060405040f0b0414071b02120708030a180f0e0a0b150d0e0d081317041d06010f05 68
    0x100350800745140482040840d15250341100d5400d50394201055241c03c005a042105400c0319100800f4011410480b000a860742c801900050000702ea01c0c041c0d03010803c400095a400d80001814410206280c3c14001819401110100d20a014034642020000840f001d007403039421040c0c0d203071820342c2e090280c2683e0640719081e002e41c2c448020f1100150903600c500034103010844034079000c1101c441d0b11003880240c13150003280c000320184100800000725030000c0030880c8420010405003c4004c1c600214000c00e0358903590a030365000350000490014000001050810740542c0c03100091881c1c100141402810740c0145843c40310007103400c105030900446850b403c44440340b00091101b071140001aa40b001c0c040c1c0c03042e80d0600100c0e080c1003070a581d00c01d0b411000d4101015002d1004212001000c08070010181b991480520b0101014404500082c840000c1c03110f0380d4980e9151110580884284a4001e5003c001c1114000901c554400c9240c01440c00740e90300c84a00300001081510744484 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 950158750 1250 950157500 950157517
    0xd08040209100b040b0c1e12090406090615020d030c09050d03020c2d0117040618051609060503191103011e05010806010b04081b0609090a0e0d0320 65
    0x32549a001c50301416a40042009003003280d1055a03440000c0d458505010100c0b0318010100500008070b1800b0b9404500f01040441520a0315510070a500015000700784bd0b800c440c2505250080216100c1e80034288401c50300f0058084a4036202141000c41c00c3d9041010380b0000604a20780412440c1031030302508103020302c41d005641d448520074000c152174028495030120795a50706509003080c03201006443d29003480078039006a0040b01c01a12070215800508000d00440c0d8900d8001510b420b0454102c17007103580007090324010f050310104448040300d40d0085540d25840c098001840e171030000b0b06405068002282d180404400da152140c03402c0042c1c030000d07099500ca141d031413055170030791400b8600f00303504020004840d410001c00900e8220160460b10b0302113404c110510a002e8001610229602000300304800c41c007000c80410385034040c5d000901e0b005401740c028025540102d40018069200c2c17042140d00e000e00740da00031800d8809045846080503034400140720101d01e9103000300001c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 950160000 1250 950158750 950158771
    0x9040902040207020414040c0b1821070e04060b010503160e041d060a0507030b13050903040f0b0c0d0f20070b07030801090b01050a170a06080706020106170d08040209 73
    0x3e0396035004202501d0310b100d840610002c003501040b00304417074114050003418034080c0081c24440d00c64200e400c1c14241c043c8161051200c400511a60041403903055440c1e09441c060b00c512641c1c8182052052200752011a82079051680c42040d80d449082a40e1040f0000503000c90140800242503c0070340c0402c0038550400d84401611400e200100036000c01100c8480050980c0c0c5801e824403812100d001d4020001c02d070400c0300ca4021503440d142ca1039080040020002866160100c001d07203181f1584c1d2000e0400d514200000860744511805080c51107041c07010b80b10390b51070100e82260705044c180d00320b1010880841200c04000c40b103004099044400404480c049038aa50100d969500002012000201b143c00140310402c29030144a41c00c06080c09c0c4a414001c29050180100d0300114484088241220019a201c000743d0420302c0101020807e0316011503d42d030000340030381498042d042c0e03914070030302c2054864a00080c0e80c14048a8030b80d20b50800b61250780c20807000000c00b03400c24404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 950161250 1250 950160000 950160007
    0xb010311120607020c0109051e01052b020d05100f150509060304060e1b0a0905060319080a09120206070308061807090f0b0c0d11010f02030c04031109040305090409020402 75
    0x1060382081041c3c0079410580061040c42c0810000400840700341d04003502580341d100c070355030302e007071111801008240c002d0034510388034081e25111104c80303d14403000c8a100b8840c040c80912015050340280480085454140710564034405a030303a40c1c1d1901c0c416840c0c5010184c0013006118000c2c14811078071101460110310b04007900e4001401070700240d1301900e029964000f41940c080d0b0030021403890101040614403651084000640b540555110f65034101c0d44910008d695550180100fa0f426081001c10030301020290500003c00d411149448011480c0c120300480c0310046441c40c01421503000b00420f2521006503011568014090701194001c20201c2040c440b180c6e0003050f80d84181d41c25a0f40c0d40e0b0309847d00c1c0300d14820f0380e034641c8054a40c0702c0c10040c07104112404100603040030032a090050319564038011385030050110000c40c0c030709a403021042c40740c00024200284202d0f40100d180c440260800410041034140968005000c52420041000142410b812110f800d9000410040c03c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 950162500 1250 950161250 950161279
    0x20f0904020d06151d0603070309080d140601030e0705041808030412091a0306120304090c1e030605030613020a12060504030f021914030c370b010311 66
    0x380e800c1501c045190703507103800007400345124904c0480ca403480c0300c1c07500c9507041015801c680407061050140d54085c086c0040000d000c203000c0d0b041514100d0344402c0700340e558100301198400600c42c010403402c2c03510498011401c25071280c0284002200300354050561036203000c042100400c07601801203d4002c000400340d011900c0c100c05588a54024507041001c01c141a0009040c602c40d50803140c40c100160454031000d10f09842601e5110b9020795068035407000c0d08134524614000e41e8006001c0609000311414200c0c0c0c0001e500b0944030042c0c0c580101d440840134180c2c00d130b43d0b07a40103a581641c0820b000030b03010110803526030841c500182101061645030359192046e110550401d0720301640398824402055400311584003030040a202030308644c054003580c1c00d0381d51100f0f000070342034101c40340d05170344040c600744110307640455800125592089690300780952002182d100044040d034410a1005814540d0058a070340b50f40702c0e19280e03c5a086030ba61820364140c0c0b500d070741d4000352581078419 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 950163750 1250 950162500 950162509
    0x3020711060316080c040e0a0c0e100c031701080a0b100f0311180115351009020f040b220801050114030111040603020906070f08070c0e10030303020f09 67
    0x5015094950f001038450240d0340010b070229101515800510b2800c000c100a003c0a650107140c000e2074940000c10021200e003412654903078043c0446a01420b400c90140d01240c009940c01c1d951882170b02c0e03010740d00b0124803174044050024400c900c0340da08820300310000551241a140d074082501203110044c00d464071a2460340003a65041100d16031030742045c1450b585080d00c1326103010211180004880d43c14602e02d1142075540751002810f2100550000c80000c1140d000300341000051038001c15403000340340c142c00402c002030324442034000b004500400e002040f0700807945000d1014004514040c5080c030b9600e1241d0004401d1140c4041e02c6400703850407889402494000c004240021800e54105030f208140b001070608150b01c203a01d03016504d51010f2601081d2800c441d00c1e81401602ccd0500880402d141d072007911030080040a08124171401c2191610242c10054000c081c118003881c0c13900c1e00490160404ea4400d07202041c407890800011340f10703400901c2d01d1121840036500344410b1a000c10b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 950165000 1250 950163750 950163757
    0xe01141905130f03090b0f030708010b130302040e010b0d0b0a0c05270111060a0c02010506010918050601050c1e06060f030a11031204090204150810060804170705012301080d0302071106 81
    0xa4200a400420300c42140e2b8000380c41c07409421034264551900e601d260118000200c5881b00a00850720303511040440354080d4044030300c2c4400034050040c0b01d40390b840c0980f071210007103400030310003482c0000c0c4001c254415819100351070780c05521701e50010a550307021004490007507105030400c04d0102d0404112142407001038018001c0e010080f810345003070030002c0c0c02d642008001c03d0400c00540e0702003020001015020320034080301d140024840e00e41c0001290780d489411030380b110703501c0b94998109800b03210344101c0c0c103c01c407004162100d6480340c4040102c0c4507906034804d40c0c16404004400c000c250f110790448041e010080803558203181d080004000350308142e0044c440e2903804241040064815802d40a6902103480c0c901c0d103503d81150341c460382541a000796020011420700203420000b42c1300707103a00e17016012a45961581617070b05d0000c0c0604403400446004d5070382a10040205c1c0f0782000d17464141e801e02e401400450803d0704045000703400c11a000c2e074803806074040303040380c3d600d804008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 950166250 1250 950165000 950165017
    0x2060a050d05010e0603100b060d061508072c0d05071e17070e1b04030807031101050c0d150f140102072112030e01141905130f03090b 59
    0x1003940300e01c0004940000c42d907059000307030b500460b00383c104000c85d90007143c80041141e43c1d240004148081d5000306140f405a40300789000207141c0303c0040b50184030905486081102541d90340ea140d954690212204586c120781000c0c418007440a160303600118041001040304007802e18144230800340c0300ca900d06540e0b54007c1d8110949107a6031800d500c5c2e402c030140c0c060080c1c290310115040008001c01e0b41c40600d8450101c3c3c01c03481202040c000c3c1e500d0511080c10084817620680c13516202c0c204014a503000c0942100450144080381e0011035042c081c1a108038240d041103420000081d15440203012002403506415454107800300f8402d41500603100906513680594061203408800a80345c121140c00514090044000d0a1032886800314013440641e440340901606020f42c40c400d40c00340c030310841821120b5082401c4030f0764060f10b030411248600d9484a27100c0b1080341c291420385c121101620800c40f88103040d0f400c0740200f4458401d4085d45c5100745441743c03025035034201e40001c5401c030a29 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 950167500 1250 950166250 950166257
    0x120809040e031224010e030a0227010303033204030f0504050607200909120901091d090d0c050a081615020d0506120312181e240a150302060a 62
    0x1c00440e00c1101c1c0030400b0340c1c0318003806e16030480380d0580002565074021820003440f42c00296501903401c2416a00c0104000302c0c15000c0700956120718000d00509081c864040e1481f48109040c235401c0d0380c1c41ca1b20985180744c4604003030503072201c0e2011030700503425108040500004010015807501e03803800804072030380104854041c0000c40300350400b0850240c08401e20640a0105018140c4004124844d080703017440d407000d568114060041e00c500c072031030b840651070012281c40404900a500042071180c881002901c00c0101e1a610a5407000c41d100d10140483e0302550b0301100080700740004101c0882050b911104141055607070069411045540780606900401c80e280c42c007825001d41038000c10111400401e500303d020840e41da0340251980d0080380006600412040d080e04055041300f00c030342d1802e440c00b59030013480c50030700d1007818010b0b07070743c903209840c1280251182d40721a50200004600140a42c1c0c4034002118080c0c90601440740740f400d5040000001a52048010128031005ea00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 950168750 1250 950167500 950167531
    0x120c04180917040e130f0b0a05040b01080601140d210c0b06030712081c060f060216080601170c060d050a0c020c0303031617010e040c120809040e0312 66
    0x1d004506042e80a600b0b4080c618140070a01c1018108440b20f41c1c0400c0c40c900d0800a40701d58140010f85031b040881c054034000300101032203c00e61403038000c03500ca580035036400748051f66151009a51141d007486032101c4203841001d81f03a150b103080417003102c845005d8800e00d51503441c4a00c00700d002c40b00250003000481d00d0b44c1c03002002c00040c41001036005c03030110003600c4220b03d0a0042d00702c00e100c0000c010407a510009030708264010345070215900d02118142004516221066013400d84004e0080d41e02502c0f80c191184060414004903c0941c4c074100003805a5918001141e40a0700b629661150107002d9000e445100d0b85420000e8100e071154143d020540f800d000b107010040360b03c030308ad948045402524850400e510300004903034202d4855081c0f1560207001e01421144040125074018840c0c0e60340e000094080e0120b0384541c0154010031006a00542d0707104400055114820024100501444244058581039100780151403118003603a05d0203021444030703829407508451504010380c0e05c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 950170000 1250 950168750 950168753
    0x80d090503160b0405040b041d0105061302090f01050c0f0d0e0109090b18060a03020301050a48050d05090106030510110d0c140c06010503150705120c041809 69
    0x10040e9071901010312025141c0b90342070a18048051040303004481c001e82d00d80c0008503642d151030388189900585c0d502c0000a880e42800d840b4042c10090b150144160700022001c41d00080c0b40c401c84480d480010801c904405e805801540c82d5000310810340c7ca107000e2610708018201050200c00c0145a560303452045449141d0005403442986070000d5407154a4243c80c64110745a0074140041041481000d900303039076400c00010b170121006c2c0c000075055401d060a000310003a15800c01140d4445c1e0108407809400460aa40208003001090409400000b03000409542032108203d00c00c00041c5842454460b001c107041c419141d06990f1222642c1d52400d040040c40818028800202c40d1010103014440c0010910310b1140221301e0017411441d55110790301e04041c085e80d046921003104450310342d25000c1c0000265110042445114040d01840f00503078010782160103038070b200e00282d4443e036041c10b0055a91440c0050300900880c0380d1103041002050281c02031810500c070b81080c800101c0c10765042d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 950171250 1250 950170000 950170003
    0xa05070206070801151d03030406020721120806010302070c03050c1e0f010e060d0c0804120f05030c0705071809060b150a0c060f0906020307031b021e0304080d090503 73
    0x6060104020743c000040c0004494181c4e620140d00b91440c21504601400719002090170301e03000916898130002800280c1d0795000b280c0802200c0800701c041120f41004213a1003003031456910003e0504c10a044d1814010303001d9043c1d030380c00c00c40614005080000c03039680c09861042e6504169401e80c0811000245440d0112043e02002e0341c2c3e8140e4000c0b00c1a21001c220744407007880c88941440a030603481d0980d42c03607403015601c40c02c60481051190814000c0c010304004400d540548180c000304540501c2c150080e0454044e08100c2d684480c9140d4460301e401034190410b883c1214280680e000c009455003a1b0031080c96010171522000a400070b082c91701c04200c604000c0001c0c00b898810b1070400c401d003007400a0f80c4143c1c00600300440030004030305d040402041d81d509125003c0f4980f400003402e001c01980654403c2d0540e8904200c2900c0d0000b4540342e141d400d400240045e8020100c201800d40207032480089484907008076818a0303121394030582494450030f1a10300203840301e80100000d150 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 950172500 1250 950171250 950171263
    0x5070e060319030e0f010c0614040c0806060a121b15030b01020115050409080c060429060901090c02031e0d050c0c060c0a090315050105041a0303030a05040503120a050702 75
    0x1401482c03144200d079155005020702036403651040c8540643d051800907a4002d4401c00289644400100040d01e201800380b03031003000c150b84c1940c6030512601e02181030700d400501680a1400200b4022409140400040300c613a05030340b0450b1880c03000710034071103000c00029074440038000346440e80c000e0102c0380c00001c08032051240c001d81103a041c440310042c949460300034401950070607100443c08070000d0600c1c18a07482040d80251042c03203164100720900043c40c06504143e20103851076445003030783c8060403900f60f40560f00194091002d80040009040b01e50011b08801610300540781462210031141c1c442c0661032110845040e00010a60842c02c854800c8541c404080b14102d4200340480c0724240c0d0b5841e00800394080800005403441c1c085000d001c00b00d005540c00050008005507030345c0318002900f0203100307041c010743c10803802c040741130700389180c500301040090005c1d41141c0c0d4041c0d000d005002c0180040d99240000c221a1200e15200b0900c0e034404d8000b61008501400d20240003464540d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 950173750 1250 950172500 950172523
    0x204090321021204080c0f0a081215010203160c09020403060626120705122a1b01051614030c10110301050d0c0b0310140303070c06120905070e0603 65
    0x520401c80c44040d0f81602c44202d03006504021403503201c03036082c411503192414441c0810300a11400305130008004035840107000400f868080d844142d00c9d100b0341c1055080403401c1c8240941c00078450288540750107203401d20298040c0b50300740b105035030355996182283d11503041529010307143e80d000d0041e4040c0c1105c01c030f00c1e0a81003007200140d1000040c00350f110014ac0c41d41006ca140c0000340320082c01020802d22071900d00003136a950b0345503035502884101d1001d82c0115948128151440b0b004d000300881d41500016002d0072349001d0391030801c0115095030010a806501680f0810795501280780c000010b40c040590384004c665400010340d00c0d902e819240909581e005081a100103080c034554410b590454006903030301500f0003d545007400b44140d181d04100c102c8034002c010803413580c40c001440c0381240ca942c154110b4804000381459201d11a04070054041007242c181001058403600010000050304240014080c034035540700c0303083c05c105038011000760340c000c07060040c03d2030244503419030f41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 950175000 1250 950173750 950173817
    0x16050603070504061101020d020a0c02120a02010f050a030e0703060c09080703240b040906020301290712021c0c0204060b070c05150d05010e150d08032202040903 71
    0x40c5001c240003000b9100d580503100800c41001c1e03100f070320b0ba0b90940658122000c405015512180d803808018a60380c028041a8400d40d8030270011400d502d008181508a1a0103956040c80c41d1003410050320581e12000102c8200742c1d41d274048513051602808824003075417045801084507543d50100608c42c0032960000000c98200c52410000078101d113a800602c100c1c0940303034044540c000c4030b01d0401801c56184954203c1d040c000124200003c540c010740c16610f15014490040280c2115100442d0709007002c21001c0504111080109101d403860890040e101e10494151340e10510300740c4141d1b16400d4038400442c0c80c01c0183c1c02185800d008220203800408890713800c0411948580d46c035001d580c2f00b400d0082406011031b10707821507100700b2034241419050003800309503560010030f069003800312003040d5024a96004030285280c00c603103051569401aa0103030454440044010440c55403802d00c03605904000305c41d00041c0c545010310018a80651076086140b250426003406501c07103100c01c007040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 950176250 1250 950175000 950175007
    0xd050a05030a1109040c090906060f021b240a0807030c0c0311032505061b041e0e0a1b111b06070606080a1106030708160c0c08160506 59
    0x61991080a4a911820314807003c201812520101c94152149040c015009810b00003203c0006400040d6041211317846041040700e03603920281190142103038059600140c000100078421041110303111003603048000d00c0e44d10060b18000309010300511228010418980100e00008050380240785682e121000d800d091051000303510000300001c91030800101845004608098100001c10548980004110008000114240104110340b0354250115100c0c0f24030000078482c1c0500110001401000112031420a800c0075038070060091100d85142c841d031025080094000700320000c06000e10880316000500034803071482d45000e40c140184070000e0046520704d4409c40b00001581c00400452141403c41c1c0c0c80d821800a82c1c140f080740b4014000c1d5040a20120b072040700812030311403a6210388100601e40502d001813140c0ca000844240d0003050124001555903e00700c1d03a44481c1988a2411102c107500d00c1e95040b4100c01190407244480d800560301004891f50308040402070141140e11504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 950177500 1250 950176250 950176267
    0x5031f0f06181e0606020109060513020d14010f020d0912020d052704150e070e0306010302010c020301330609081b01020a14030d050606270112050103140d05 69
    0xb50800030100800c140c0d461100401c2c050007080c2c0b0a1420089070400e018190740e441d4002d003c0d250317000060391007901d418049100708880c410004641903001d01442c4042000d510f034000490351110309121b955417160070500703005c0b000c0e1008020f1040b81c2400000d4038030843c104207200c0440c9424050075580310685a1303c03866000026621252002c002d140b00c0401c000c030066500c1f1a950a42981041c140a110130540f480e490b1040b0a0719051f01e007100d01c5a441030012900a4071044840f0f403da08424014009541300e029428440341c009400401c40101174141b0003a1020314041c0744040c4080f20751071000062444c45020018100d81c0742600ca81814020b105807140981458031656081d0f296298110342d00034404219410b0308001100f0015444005241d100e40c01040c3c01c3e44010701e040009a0b0520742002601c06032011684464450505403103405e40d0698404105414030856191206103c1083d024040c080c61103120300417030500b05003000b50315006240300110309015050082c0d94 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 950178750 1250 950177500 950177519
    0x301b020c15090301092f09191107081c1b020c040b031908030a1b0c0b06040e0109150b0607021503040609081207020c09070f030e0705031f0f06 63
    0x5a240700445036682d2140301d080000c0c010800d401000301161812030341c05c03040c10410380e903502c1c030705540c04000c1280c002210200710342902d04590b100c4000014211140703260704680d001084c085001601186050402d0301c1700011030704001e608500f4400c03000b84410072501140034419420504661344207141a1181c00a9220001c40540c180116175440c0e41c0003036540c04120f03504c400381188030010352100a604186d6015841100c19404841c1820f48291400c00c507172043c030070481126030b18100c0600caa50b8400d845080e019203151b500030b131625041e8120f18001c0c85120b160030f1044244200990200b07092074240c508000300c0d64031450080c044100940c5840815030684004800150b5032a0707207902d0310030300802701e90360050040c00000c40e22030b9a001c40742d61090b0282c1c0c442e0f001c643c3c242c030840003003100041049a2a400284105a070700d00030900903001600748255500c01e40d841c554540003c80c0c074003441071002d200003841510603001d40a0341846540444284a0f206101d41410004001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 950179856 1106 950178750 950178769
    0x3031503060709060807180605040302030613020f060714030313030809060123040b13090b10080a14012408070806060d0201301b020c 59
    0x284192a00048080c401c5142c0d642e4a040c890400e0011140003030050012030900200c0403803045034a0714032400c880a0845540e8080d04d43d440d5004051504502400c0014800d20740811280581c0700e82d440702c0d17506401545c010b40d41d9006458540c4824140c9907060720180008814881c00c40320303040e8907043c0240a030b6600780154030f408c40c51075250b100a103c2c0752141001c54408400c50031000c117074007292400082c40082d0561410010071302c1024001403801c0250360f500e80c1d000c03c1106280c900343c2c00c40014900a221a4102041d0300c0d41c40c800c004005d401e0124104900d488080c094224000d0000c900142010001c019410b0440c1101a030040d0303103090040b400003184100c400250148511030041c40511045000d80041d5100002550900401d2100c03a0300304205035402c0d84000304520994400107042d003c1c10000403d0314417048030200c00c41d040503081441c6030b030380d00400 = true := by decide +kernel

theorem cover : BRFrame.Cov 950000000 950179856 := by
  have h0 := BRFrame.cov_init 950000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 950000000 ≤ n) (h2 : n < 950179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
