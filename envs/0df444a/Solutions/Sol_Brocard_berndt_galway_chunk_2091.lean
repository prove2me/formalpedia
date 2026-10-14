-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2091
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:57.35558+00:00
-- url     : https://prove2.me/submissions/fd222099-e635-4087-a73c-680550032aa3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 375899280 ≤ n < 376079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 375900530 1250 375899280 375899297
    0x30f02010c03030e1006180e071a042301080a050c0703080a020d0207050709060501030903481e08070b0907050a0603050f130c090218040614090a0516 66
    0x3090b001c0d502841c880d1309071034200c903018098401013000405942c083d01050400010180f4090041f60040c0442c40d050000074062681c5170141c2c0140c0189481c50a0f00140403e00000c030320401c401440c2c064070b000013508100c82421460001d000c04070042c01424000c0c1c1000f08004c240c2c031f81403040700d03c040da03d898400083e40c7d07454013a5009015400b004c0f05450300000745182800f10000d890070075103906c072a0800c4525903450054080303401f44900200807850b0090f60311504100b061651403040201d4004800c0303036078126040d50b891500d2103102003400c020340c04c0f030b0020302c899040507500d1700c05a0316126806080b80d403507004050246410050500801c0c2001038040c2c00c051080708001c041c050303d14202d141d1076180150140000700c0c0d8800c0241c01e1100001c1e60254000c03a0b600d05030307800070041c0808908000170a37010f944550005d044414811801102c1612144944002003a00c08851811001d010003082408034010b451001d03954140014841c0100c1150036880d944075860504910 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 375901780 1250 375900530 375900533
    0x53160201020409111909050306040201050703020a020405040311210313020111060915071d0405150619020d020307051902151b06010506070b130f020306040501140c04030f02010c 78
    0x6882560081c0c01900d04094007002c10313860a0015241c0b01122600712a24842100c80850308000c55118043d40340e4410400320300554007a2004107446070080c410f8402e00740081d00401c00f542c10546044001032018504044a5681072100d08040044680c2e40300784441d500e601c519031408060000c1d107a1000400c091421a8010001d000010320441c098590514003450203644030500001000444508400000c21a40c8103030007074598000448131010400e00c04800344002070400130103800400f000d00c9e90101d560355444000d002640b6462000700c0d28040e000c3d6009080ca1031510005003598000c0c03140b440007942c007180c40c5900507182c600d00111003030715000040961108851200002d20300180da003440c1d20150300b800d000d881c0d1440c00c51314140d80e03078018007090f4400c0c800042e001e4040540841c07219480e24031144501402100c1986120f690303500000e003000010f0b0f404540320382d500c43e01503070000c418001d440d038003140034211b8038245440c5449001c00c1d031150600090400940c0c040010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 375903030 1250 375901780 375901783
    0x100c030e1011120106080910060302060a110115090e1606050d05040c0e0702060601090e1017030903030a090815160305070c0b090a0b09010c021c531602 67
    0x2103400a03d4060030310503580d01c0f080900500001d580707548441c018550740003c0242e180c051481260360150030306180182c07451049400074403441d00340700ca55480e00f02011050310324010329800741c0a03a51000580c01c000c180f410745812110b002c0e840c82c0703102c500760821516421805413011442c06400c04100c0ea92540f5140c103226906401c18810540404c0601912540c0040e20910660007038030740074030140d10784c6101c1201407030441d044401c00d90781c00300901600040c49021364050841c1400c80f0b003002100800641580c02000075400025000b4100300f01c0b4440c100440c20b08454440b030108406e00f41040b00c024403075204001841031684a001044181c0d116510f44422946c005034055a20b050190045454200711102990700351000c0c00461200301040c444c1d80003a1241d03800030007800340002c1d20101c00d001420a26424000d081e403003489101c000302848043c0e05a01885405c4c00040e50016400035101088501400301d20a41c0f44110074a90f03070030b00d0760042002a442c1d0b01c40010504c3c2203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 375904280 1250 375903030 375903037
    0x150607060b03150405010e2e06050312070b0a020705100218040501030b070e010e0f0f03030d06031110170a02160f05070e09060708280e100c030e1011 66
    0x140d018800e010354083d0fa9441d0045007409039106000070f000d0181d030039030f441d41e454144650b400c0e0300c0540102c0c0c1c40c4200030955800581d032082e2080104e400c030380d0b460020342405040c1203a410071400002d619010040e0024160758040c05016086040035160703241c0c950344018504031900c040c0d80c0010f400069407044000850a200f00038001d00241d0384901d0540749000c0203603600d03400b094081101d001290302911500b1070300e942c090404000078506da0308104e480f0b030313554a056805010800c0303030107a21129401707844040c0d1f0043c1c03d0210107545500c18420840010803800342040a800c0c0079008c5200c0803040c03c0c0d000818100701503102c84020000e49500c42144070000d081d000300c1c030300c0746d41005004600f107405c4551044108016603140e0fa0700a84030343c421140355001455000c00070304280380c101d54081c2d03803880c9041800141c440c160401c90840700c641d00441d4240d03001c01100b9041248500070380380d00ca00c46240502c170385405020b00c1981c800b60802408107050719078118458401500058 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 375905530 1250 375904280 375904301
    0x2d030105060a201011041d06040204120b040302070b0f0d0b1f120b12060106030218060403030806030c060a05161b0b03011a03100303110f160e090615060706 69
    0x1050502d5214842c401d55601491340e8401032181014100007140f41c1c92003d450458403241c1c50102c1003882d03803510710510040140280d510035428440480c2c80d460500c00b40580038410b111107001402d25003806482c0038095800101e522104010041c00e4504501c01ea03a400b4040744000310709441403500003058415111040407410505003402425640e000e0400600c0028608003003021403d8513040c0b11300c81480c0041e01c1c40c1a400100100320709031103980200030340c64001500c49003c0e44460002883c580c800d0303200703400141c118000d0001a1070705012500c90107200300e0b401e600e800c0c440340c0058020b000d0703070b1042205481401d1124050000c20000c8101c40d4800185100c5226260b0304840c1e50303030f0004e0159061190500d40e09404142c1880101d80c0603074000365692505910356541140c0040c40064a0b500b98054151550b00d414420400c6203000e803150405d1f084114108040408410300c001d0030b8500c2d5502c01014000c40c07000c81c2100011700750090f100207a03100803c6c14080040c00600c0702 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 375906780 1250 375905530 375905567
    0x200f0609030703171c050c0a08100308031e09161509030501051f080313030b0a0207060509070602010b010504032d12021b120c06030a06090509032d030105060a 70
    0x350b941e402841c9000a09881090190a4010f10b480490000c1210411100705901c081c003041000040b50062200950168000908034ae000b0b44a9480e03a9040d0000e42d600c445080d0054808070202c901d8070341c507541c0308460500411010400c00002e0741d4800040c4116000348011f4255848414801c0c2443c0e00510b401c40020311440c10850082940400c00c003403d10038440c04003102250642010044a07000e04400454828450550311809407151019000c455103907420400380000030050300500e0b01c01d41ca048040c1c500280342603000703425039031007000702c90400c0700c100070610004600c0c6400d003004d00d40a520000d80c0740e60802c1030300c500100319003010b421034100c480d8202c5926030015030b01204401c0d03141c10304149031484007400800400103110000e282c02c404600002c504140d405180e200c403030ba01c8042402503031498501c0c1111410340e0111015000005d03000105010403c0c54904803520311500600300807507040c40d0b450340c081070281912401c00010010b0001e0301c0703054208040907003d80e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 375908030 1250 375906780 375906803
    0x3006200a1d120f0607080606120106050d1b020c090a140a0b1903060b10140306090421050702150f040611011b0c06110a020a020111011407050403200f0609030703 71
    0xb21150f44c1d4000481c0e40f800040e81d540d0025025090400c26100c0c0c9807400700000000fa420510142c4580e00540018510240d580700c010140441c402d074070413032800c0c0c00c1e000740c45058540030610103241001050000c846040c031204e4150050510001507200801c20390000f000724844000800c1401801d29100b40c0072282c2c40003000344020b5611503688450101d8401c2c00316a0280c0b02070798200b0f40c0c1d22103182000f41c140300141160804039107a0764003610510700004030b0026405002c1440c103994581d24000340e0040307980011410a003032303080081c806404049003050051803403c007140c0b299000d51804c0054440b542c4003a5142500425040c401c0341500720008035943c0130041c000258290280d8100f4200100c0748900f07002001214140012907001d00014640380d001982c8002030300450301c64966a45650144103610030003170b580100720958985503154514140140d003e60000500074a005180144503180eaa4684400c0100c1a00b0750b00b00703072248400d000085c10300c0025800600341c080d200c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 375909280 1250 375908030 375908053
    0x81b030a0b010b0d18020609210708031213240e01090f0203150f070507050a0c08210c03031302040b090708071704020603013006200a1d12 61
    0x1001130001c2110200c010450490180e0400e46081c1907400041e4001d4401c2015034014188441c400a4010ba400c0c6a04800d0051911403131804134541e0104d40d068102142820400358501c01681e0010320040f4001c2400d00c9079250400381c000140c808000c02d801841406140101c40d802c01c5405100340402000101a282854201e10f08007034012482809244003005038900c03100d2079140615180c9584200554400341c00b55041d40c40880191100d103d200c50355000a058483e0084c040d10740741004d040c0b62840b20304240b420702c9480d589003a0300f01b000e2000c0d07500c0caa000029650700010314417001c130107044507002103001060f4084c04c840d0004064810456200c4c2c11190241c0070345010790705e5070552a18a608000c900c9400c1e20000c0d408642040100242c2e2580e401c5200c174118292141c4800da641101d0485810090712800c48241b9201d2007a000c0300244844510801d11500d41d099103480d608150007819680281012040e24000203202c41c6140c40703803038803107464401040c101c45120421 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 375910530 1250 375909280 375909299
    0xf0204030b0f04051b0402120a24031a06060f0a0f180e060d0219120501060609050906330306040b01020d020d110a1208070e010801081b030a0b01 64
    0xa4002524860040008512202070454040388200c4d08140036000c8a607015030007208a00e00480110b0307010740c0921103900b01488400119025100103c000501105080018403400d2016a030380601e1014084040000c034143d034080c900300311207261000c012a59044000b512501807a0004407016001095131070581d50401c644c800010031076100c84141d050a09108003940107980a01c40032010b4500c00304500b070421618412005200801e40368102280c0300c82c2581150042c0c2c4405440c000c0300b5070201c1030000070311584024012a24081d4189402d24010486e080c0000c1c01d020300407030710320808402c019200c00508503400307001d05503500d40803117648840442390800c0e01c2042c071079850400074810542c00017900a1298075103401520a2440408050302c00c01c2c101c1d04151f1090041310880c07000102c01130034080324040143c80d800308600300420300404040c015850701b1306100600300107002030740300018149500c00803081d04210030802500407038103215003024003c0c43c6407803810020403c1c02c1e6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 375911780 1250 375910530 375910537
    0x150305060103050c130905040c0803070f0b1005010c030e0411030a020a021b09040b19020f03071b0c09111303030e03060f28240f0f08060a05070c060f02 67
    0x8003642e0900181d19980c0d0ba030245407080400c00001d4648140041120000a4200380da00901030115141c0b85680c6842503400d41d44000c2045030405c0c1c0890030202082030b0100c090f500b00b0380650048021a061400280c51011190700203000e00954040940c010369868018410721980c00b02c4190b10b034213207040064069007000700c030038025024815118105803070070590705010980c020130b01c4401c0c0d00c5070b440b17101c082980a8084007543c0724820344200d50440600003071000c003071801c090558900d04030a0042100920310001d0511900702d010403400b003807900f00c0703200c2651000140060300c62544100700e0780a20588001c4001031444210003c14190081c561840308007090703065682d6a0b5941030b0503854041c00704c07501d64018042e100c051400303440310110721a240010500c005821098910400c10000000015030741400e9030075814007035041030101d160020f240e04058980c085050081142e1201d50007080d6081180da2040001c0e95144a1500071400740e0b0007400422001d4403201e00d62010350b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 375913030 1250 375911780 375911791
    0x7060617070e0f0c0307050c06040b040204050c0703020a030f0908010e060106080907180903110303100906060c0809091b07121d01021c181412030a0203180a150305 72
    0xc0c001c00040321014002c0191081c01c421502c40b08907980c2e00c0c0d10303448503000641504d0400c1418407107940c040c00e0400c950390240f0b02804c000b22103403030035204110540c0c100900c1c2d14000d103002d201203400242c0015030101140c0d494100000141c071070480c1101e64021640c040e004942c03c0090b260b9403584040390b00707416691542d80703201d0142d071a201006d03070301d50103031243d15a03601d0941512000e141140d8813808103e846403500c00c51404242050394915003060f075070000c175840800c4040240d03443d207126843c020103d5061108a150749a246c16032a4000c0804035405035048200050000032414014403000c40d2804c0f40584410040c00c180001400d030040c4c1c100851040c000005d03c0300c80199000c0090b6005074000d01111021021000584100456000a0004d06803160b00440c030381c21600409414801103002c1c2c3c0b03107841800c0260344c06101a0a034500e800402003100301907400320440d8543e803c42d03100c10b007035400520b01040204605070f024512050008803503c00c0264181c0146024a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 375914280 1250 375913030 375913033
    0x20714010c0c021f0201110c01050601020d26180d0c0b10120f03021e03090102070e01062c03031611120615010921120507151107060617 60
    0x1d0700c0c0c1d041a50340700d41c04100070b90b1001400c4428029110840310181403407020b4800426140310350104455690824402c0c0f13209030751100700304425035074100b1140e01d07801040d14000c841c0d2055041007100c80c5070050320003a10f43c018200001c034161418545030030404020b40071a500c01c059280c00814015589000711082e5002c80302140c806141e07032810600b500c0c0380b1091800d164419a89552240101036130840075800380c1000700d1000301883c6894180c0c413070540084c55869010340c00090500d10581c100ca0030b4598a2001031002ca0350206010507000d107040c0801c05140300c010404050030002c4e4020303a50600c0000303410b0b48911211954080901d20800c6012000300e907600c10040b2400e00c444044032181c0c001000508401000a0340b81100241810200e601c1a150075580852020200188100d1588081384004000d805091950001081e01e04203041401035600d00110110080a900a16441c2c004000105041104854805074802d104100300d03030f035480107001c0104060306001400e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 375915530 1250 375914280 375914291
    0x1e03050303070c2f010503180706110d09380708040905091b060d09050a12081311040507030b1f0206070309051507020a300507030c1104020d02071401 66
    0x10500c01d0041d0484c100d441e07040f08001400e14401144c3c1c40d04020030091054440850050614a0500c045009006550741d20315281c05c905404902e4104da1440e01010011288070400111030314035980c501424002d0604204000602c4425540c0c5105080f0680341d990002610001c002095005000f260b043d820180050341d5a11880c070789480e0301400302001c0d070060a82c0d100042c5400401031030b0340560000d0006504c04140c03a01e41c6000d0740c225040300d2040020202c41502a008603449601c4951404a507002a280360388a4155102146030640074580f101c01048009000c1c1e0030000090101414448510110010b2940e02c0100100b011025000341d60214034007501c01c2c05402c010640000061450342d01600c4000c10050780100792400f14094038071410001044020300b506070281c00d00742140005118a401e0464143c0c01c0d049070240300e0100b064400107170b00120f00d4000305070406004602d001001c00464040d00c15940040061440058010108141c004a009501c811103008000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 375916780 1250 375915530 375915563
    0x5070f06090b0c030d090c0801020a050d05060f03030a050c2e0f111602040207080313061a0907030b0411130801060902040503060c03040609021c0b0a151e03050303070c 74
    0xb0341c0d22503107070280d119410070052008007214031340040106034410310500c07500c3c1e940d0b41e416500f21303086251241c00184000610b1140c07a003d03401410303003215049800c540b80c5562038000994a11590306114140900070030500c1d240c14090003c910754250703404604450440007040d03a000300002c020005085882c100c0000c0c0900581d00c01c40001710080c1c1c408510f00354035158050768080f0120022a0b10580800c280000259030202841c06505102c0c8a6941600249464004c0d00c1411500314450248030b05000010b980d52070700d054006001d8140040d0303441d480c502190140250505016034180002803101400b030401500d4400c9440f0b51000b00001d41c1c68806040580c42988105030703140d4820401701d05c1800c1024000d5401a1298000062145481e40810621180b403201d10070b08076000d05034181441003d041045d441040c2200400460001d220503903985500e82c00b480100214841e81544800c0900c1e040744065500801220785901e4122001460b101504400301e03943e0700221003004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 375918030 1250 375916780 375916799
    0xf02160f060210050c09131b18170c1003090c08031b011503020603061c080702090601030e0d030506060d0509030a092309040c03021e19080c0d08040305070f0609 71
    0xd01070b42e1750103465803500034a503042117a03526601000707001599407001d00e4894080036808520201e00c039919105950b000c0300940c207401141551043c103006025800585a80c0f02c042407103a0300c0c00c0304030340c0450800c00d9403004400404c60504010501e0300c003c4004500ca000010140100704405401103000740c0900002c2400e07148109030064140400d4102800149444406180d018030003503c0c14068905d074603000000c42c2c00080041c0c0b85010b0024203a425401d10103500e40c1c0c0010282001e000714450360210907a204203050301042059592008102a90346030004c880f148941d800050006050089041e501d0740d20842c4502e0204104a130000341d141d010300141068080da4840d00c00c0751022540620201801c021710850701d40c2124080840140d5445100c3c0f44441502002502030004040901100d180b040b0701c5140d10600c280d0040222071000544e014601d442502e641c0c50b505202e15162000d0b000d260401031490240308004150b101c900036165044900c5aa1202000c039a40e55124 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 375919280 1250 375918030 375918041
    0x9100c0905010c12020c030318010e0f0616110d0b06040c0206060d03050307140c01020d051513020d0f0504051506060403170c120c0109060e0d020d0f02160f060210 72
    0x741c0480d2500c004440410364001030f061101c40d90340150b80c3c1100d0340d88000381c111742c001c04400200d00c441000342c00e21940e00a0100900070000d40b00b40c9034041c21240003e0072070240311441c0d2045e02c03011945000300042c2c02901490a000540320025064091802c41d0040c038003124428022460020441c6031644000742c0c190060340080e02e075030382009290305c080314264002030070b1000340074210780c900e00c5440f2083d004066540d203440c001601d40a0400d140000d64201800442403071004518030190760740c076103171080c0111701c0c0788000603541d1707000104440140c0318800c11107c0003403804c000c002c14010081515109112031031082841c1d5a503206c108019400f0f00d02020f03002c1680510010302c4d1342d2071200200b8040c02c0d9036044841c60300b14040080501d030304c141d06020b1165150f04e00801046901d00a01c0d1088031000064420000e0100c4029980d5851039840030030030a98180200a0324000d1044400c1010445000d544003030b1121b10511300c03102d180c072520700184201640c8141003c05442031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 375920530 1250 375919280 375919289
    0x240f0b18010e060d0c1d04031e0f1206120515010b0705062215020901031805100b120706051b0a0b0411060d050a0905150c04030308040609060509100c09 67
    0x400039a0b124a81801388548502000311480da000070408509058820b0311840c050f041c41551301d03902e24140c50010060922031460641c0b440f400c00148410030340001440110b40700d203107840410561a500b00c0005007070180c2c00f100140030042d50b500140301011031b49042c40d0b112201e2803402641d96200c103000700d10907940c002e8000c0d0042c1000c034526800090b18010030842026801580b48c01549070b0345c00031140350140c00d5000d070340001d0307075407095805008400003841c1076120340c1344400081c0c40d0940c40d2259400745056460b65600e0900c0669254580050108500b4007111443c42d20359070042c00c280e02c005e142040f400e241e02d507444418000001c41e98812030703001d82c3c01c0803d9102c035035179405110340c000886a030008c0280300701c0c0400c65041c841c0e64170540d940d04011884840d641070441c1080316140000303002086813402c026a0219a1003280d0840b0381c50702d08240680e0b2941451002082d480700010400c506040c14020001c10001e03042841c2d071000c090411030342034208401d0700d045c140ca105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 375921780 1250 375920530 375920549
    0x31801020a0f021504081b01020c0105040602060a05060d23100b03030d0c14160b0714180a15031406040e0d05070c080a03080106020f0102031003240f0b1801 69
    0x602c006007020300b41d881e2101510840d01c2e003800d0f150421b0070304000302100c24000701480d01c44881895030741004840c80c4818203080c41440d21b030526400948800d002400c0991090701c2f840444d5844e240d0089642e4101c0e0005480e00f54038485180e00030110201c221445614402c4000d0500080d000c2d00c0388030304652005000394545600149440080c0c050b298045091201444400780000c00c0d00004103c00b281444031102400450315100c40d0582e0003a0410007004101039500809107500c0e81250a40000b04440508810120300007403200c0303445420051101c880f50310781c1d142c1d00f90503030000c10040401035442c0c2801e54825090004031050445410a50b42c0710190a10025028800610025000750051102d040d2a0340000b8602241031350221f00042140c1c0c0104a0180c8c1480100c8464010350020b519500b000008a07088801d240006042c0302e02a5400145083c448410b048818540c40c405200750003290b6035030340080441c041420301440038801001c23400055a242c0c3c905036100c041c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 375923030 1250 375921780 375921803
    0xc150504050a120c170f070b0f03040b100302180601032d11040e160807080702120a0513060305010510020705180c120a09021c020906041a040905031801020a 69
    0x10001d01c070b0602da8001d84d800c804145020540400007424030307241c000460001d28440d49070082652500110b54419002400140081207c00e40c0900890b49c20035040388029071551078404d0a5070403149154802940083d410401903a8411140c460034030a61007620100440005e02c480c4200321445138020a001c108544c160711a07402040c0d0010200b41c004c40011802c181d164108544648002d40d400c0c3c19403807031000d0441c0100d60201466034480d01501d40110b05050407480656100000c2101c2c0390400f001190100c0a1842038060719985011500124501e5550f008050010202802400e01401d0300d445080506400081c00c80112540074000300401684500c0d040c3c14294060103094084100f01710380d00c0450010b81c2458010500c3c514005105440740c810050703202a0350852031a401ea54589280c00748e65540f428a60155056402140c0c064400920084900210080315400b030720307006003003041c0880013000d0711500074800d00e008081840c0100681e61a412024028460550304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 375924280 1250 375923030 375923039
    0x30506040e0606101d04020c100c0903111c1b0810150b030408040f080c09010f050105030610020f0f03071b0806010614070803010b180f03030a0c1e0c150504050a 71
    0x455820f600d00100300c0c00d0703045c000d800400260582e8003468403000710394442e070500d4181e02c00d0791013084601880b03400c00000705491035544038490414035214601c00d10b050228510f00c81106140301002c15403003080c0b22946600785140381500c1409004007001c0d44107001d000c042100e002d100300e2014000344890380000d00d2405a556000d13600c010400c450401c028040080c004201c14074104c054506c1c180034013075a07103600c070511141d184142d1144034850001c103820420742c1d0304007040700d0700440c003a10851041c1c4440c40c000d0740351007104075130000c0c50310880c040d003564028080090f100092181d500c08800403840320001c00c00c04e0403805000c04e43d80002c8010000d041c0503401c11090301040c8140c003421308045441d03070142500300740c1c080201041c00241c5460403e40b61804028040011150005020400408070366207005458940c0b05001e0031150210612110f0403a40480c2c072140c100007510030b1001e29000345142d80303a100d00320300340c95803905003a406401402541c09a0310301511aa801c1d0340340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 375925530 1250 375924280 375924287
    0x1902040b0f03011419110d18140c090a0501030c182004051f022e06060e18010e040f0305090307090209031204050a0b07050f01020703030506040e060610 67
    0x45110560311032148030071101c1c1600c0c00e008207040400080d03986446482e003101000400503116170703075100351860001c100c5140700c658800d031100d02181e03080018601c2c00c40d200403a40030308440009131000c4c6071040c0b2421154800284040d0b41102583e005020f0341f02c012104040d10700c00c0c0401041c1c070054104c20300c038891003a0f041003030b40494540085102034000703a18100014075015a800c06036400a03050246040242c1c0211084180c03052000903003521800082d03da4103050903902e0850f1490318808034041d00001b004904009400701005050345c4c0380300203003d804141b10781e14050b41464903241d44014141000604840000301081e0060383c0e10768444000d204101012400c0c06018015401d10340c40070442c000c068a404040182e80e1a0100300b054500089140c8100001d082000280840d45561050030100d5052141440e251089898401d040882c030030114400c0d5032000c50740c6024143d1603002180140429502042007040004000c2d4548904840e42e80d0401c0c018201a913400340b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 375926780 1250 375925530 375925541
    0x6150804022e0908210c0307170d141003030c031b0c05030f01151401020307050d0804150203060d03180b040b12060d05071703070f0503070c08190204 66
    0x3009008890790300000c0492400d8610540d0060042008196882c90482d080394004024200703500003014031030110041c9102c1408001840c10041102003007501c1581810030a441d41c030743d400307200c10b02aa040c200014903950401100301801034241800000b40051000d80c0700d020b410b0369480912201e0840c0c0b4195445080602e00710100880201802e22411105410007074075403280400d05101803800e0101450304002081c42e000301e074500352040400040d030310000411903191240c0f0440d0702c031403100140c0c20f43c0074015010b0903600486890844040c5e0151141d807242c1c1c0708490342aa408040721001049010883d4050b400501401d402e03000300340a06100b4920301d040115543c4980c1d1210031000d00d03600b01d64840d03208e21001180c490101401c0050300f5902c080309540f48aa0164640c503483d0340c409091103407083c640030300122600156814800c0300e01803900301b4130003c695000c918216643c0d034420032060300c41c1212440d0204a40b100444c0250303484068405d0007000d01455000c0000400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 375928030 1250 375926780 375926783
    0x10c030606020d08070c080708030a05090f0c010e0a0306060e1b03042a0b160c0509040b01120503121006020d030501050105030a0e0118050105074d1c02010c0306150804 74
    0x61030006c0400a1500c000500c1e90300d1044c560140c4a0500c01a40c40c04c0d1003001e4501602d40c1c1050448125503c0d000604100300402442c01e08400300c6c00501281c448115600003130701590074440040340301c00c545904580110102400ec0102c03480d17003003400005010a0313034000c01528280d040e8000811b20b41c0d5400303d0040c40e21780100070441d91f88902043c03a07440b000302c50b00c0e2001e501e00b004003400013861744080204801d44240c0d00c9850b0070394510b95684414015802c45400300d40340041800810000c0d940603031441e845c003a03a50b0400e040400b8810020f40315007001481142c00641035035100e1301031541226810b0715428110303207850059001810340c20f203140005651341e40310054426032105c10100c506010b80000500ca05042900400b00b00c02c50801c2c0d401c03000d5050030b151400c142c8660081541007400d160a02c502c6520344680030100c2846c010a815103e05440740212240c1407019007506030058008008192081c1c07001d03029600e5520a071a13220000030750301181c0a000700d55142e8041e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 375929280 1250 375928030 375928037
    0x506090117070e091603030807032d020a181e090e1b030a1b0302120a0f0602130315050702100606140d061d150f060304020f0604120501050603010c030606020d0807 72
    0x40600005030700502c0031b03038000d600040c003030024081030640500c00c0d20440344042d001c800c0700c6001b200c4152240031008480589195001410000c010b10400091486410503410414000d03503503a0718068401c900182c1c4c80036082c016100003031006162003000c1401c00c41c800540919180480304844c848010441c59405000e409443c034002640820300ca8501d080e007010003101c290540c014040000300c196400b80e11540300c49040e1010454204000964650164015981e81c5601e001d11100005550008002c00001c8810341d0081040f40c002c2407058215600725501d0b00d440038414010340354a44520800301d031004400d201c91007508001492034507054480030510035a01c40c0034224500e0881410080004144e05000320150b220710510103509003100c0b0340b6102111000000c0c400e1001074070091003038140125440c956100c4000352402400344000da031410702203078200380303018000455070303070b4400d510b03121200e52003078007074400c000955039594024202401c03201015105918041c08500c2030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 375930530 1250 375929280 375929293
    0x110d020406170a05070e01030308010e06040b040e010902030c010201150e0c0f0408070602010e01050c03010b0a2a0c08030f030106120e0304140f010e060a0c14010e010506090117070e09 81
    0x5016844002e40800c0801c680100119000c60416500b080b4458101902c5030b41101d00405c04030307500840c0d90b0305540300707071011215903114180054000c0c0b118000c0b461300a8140f04010015400c1035208482c1c0ca4000d4050310b41c0c103026503004908032040060850304580ea100000c2c02480f131028103090348164640c058a1400110091506c0c60384c1083c0c4c0120f44641c80542e0a20890741d0a000b1080c0500707005009108900700250390341e03030360b0005003d6001c80134408901d548410b4031424a100f5421a9035690700e43c15030b0018041e44403d1707403084051301e14010f09800091444c01c008101e96072b000c9891540350a590800004881c0706001c096048001901c544518200540034001030000304500082c252800202005002c04450b00c001014107008507400505240e4841c5000ca0300c451185181c01d00e0074404514000c100d8084020b04840d466113000880000544158012801001d0803541e0041d2072703984074694602154900e4400340301c5d40200908020000d01640d01d140c2055032041035920 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 375931780 1250 375930530 375930539
    0x5280f0e1e07140904090b16051303240c031b020c03060606160510140106020102070309030209070302160803011a070c060807140a020705010306050303070203030715020c0601080705040c0309110d020406 89
    0xe84001100070f440c4542c487d010f105012000301d690740c101030703400d0410904280001c0c0000800c40752910026216900403030307110840543c00c50401002030a2944104206411400014000d01c841000004829018601c0c002c0300ca00005020341c82c01070050041c0001d94070071040c4001030704080000e80800e1180314003000081c0061101c042540c0286c2c1c8001010140042007000d20a410f80c051015039104010f04400703c0da014440d40203480e01030301c8200e0701d52a6032030304800074856030484a0440c1c1102c1c1d003c00421001c0c100450480c3d0700c4c801650000b80300401c0c0d004683c8600b600040c0300c1c00c1b141c0317001c00c505801a201168082c1180c2007a04400b2041c10140e03265500c1040120010b80024070280000d680521501003d490b040d8000e60504580f0340c04a59240701d03100005d0280070102c1d01058942880d5011141f40040c10415204956540c20754103603102c0c280e006007841141085802d101c00d40c80b900c01ca410080c0c10011000c50780745813200f440514482c2d080182d802c580ca4240214 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 375933030 1250 375931780 375931789
    0xc012a06021903021207080f04030809030d18050c0402040e040f051f020c0106080d050f0f04120f0308060d022d1011121305280f0e1e071409 62
    0xb007500020b450141c1e840020440d28158030703100415801c14811480284000004d0550710142d0007035050a001d0b0154417030313440b110b2660042c00a40c0021601b8482d0200d1142c00300fa1040c544144120304440d005c40c12441044284d02a6008040700a03401b5000600480d00c074036900c02c007035400f54003070316038002c5040074154441400302c10800b82d260300041d07960705211091280c01c0040041c2d0001e00030300c030000d560041c50f522501d134440b41c0e10040071861030341e04440c2c241102c00034005640e25810304003051400c041140f0074040c054010807410000507032a4204216032200c920741c01003c400c0e81241146442520155120341e0303210982148070b43c03050030745038003906d4000211a0340f19580844031a60915280c03407040810001e103004180b084000c284110460241a2034049a07490014074034015080c840940da0622081d04c1d204c0108001031280c503540e900307400d60304912071108669480803918075681c0e0400d001070089010320400a07284500c601c10f200d0580071800e60483c640f001c6400042d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 375934280 1250 375933030 375933067
    0xc120304240c15110d05010e070c030f0f020c030d0807080708070504090e0a021801170a05060106110f060c042c01300506091920010903061d0c012a0602 67
    0x5020641c2d506c00621900c5011042c460780002c803440e01002a010320368006103425100300d040d4041c4841040d007011558000c0c0015480500003904995684101c000c1c001c184a2081d150170340401c00b0840414101c5100e201202e03c584140d13181c603440c040c0303880840001013810b41915030300c5000d00249140107a071842c00c0008514800020f032152541054840c4c01c2030000a640b05045601c1100107400080c40815030030304468145c10552118203203408094102000c05006a516005a0b82004844a0b03c1400750003600c00c5030f0b100c00900004081c06103044601c0c0b8404451078048cd4004002308940200084040048400900083c1c0011200000e8502030003808449941001c002c20041070801c00540180c0014603004025104031622b440721900400c0c8025914180c0c044044d81c0d469004a80400046a110307500b004a62000d4040c00c00518804003940f09070300400030b40445961296140a00f0002141c80c4160b103080325806c1d440c40703142e81031802c603860f03602800744000c5184526040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 375935530 1250 375934280 375934297
    0x210c17032809020108061c061a060d060906050603010b1b0f070e0604050a05010b030403081e0f0601170c120a09020907050d060801060e0a09050c120304240c1511 71
    0x841d40c50610f100141c113080c03000342070382e0040c50360781040c0881001d201c2e03004459a400c202d002030710494440781c92485840c60009542c010b0000100e17480c0f0000c070340e80103a08880d02c0e4801002455110703c00c1101c544800c4c0308401042e80207121200ca907030004050751004000400c21960b503200080c100ca424007855500c01060b0100b1a03080018a0506006007036010400319800c029660401440754250701015102804100c52000004c25000540c0d101c02c0d0b06480d840c08560091405548101c1c207114122011400505000101900e803a0b089131068000d200311902e050500715030703903150080f41380c004264001c0e140d01c1e010f20310701680b80c54460b580505115078940f43d5505112140c1c5040c0c91599001034110f0b0314000b004c20103441c0c0c29508907044000c00d00040307034581050410b07500c0c0c1b0380c91a49035a0b0019415180038545140080104121101d20a2480c184454101f1101d1040b0017048084042100781208500180c40036501d140a0104500001200325a03082c007264a40c202100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 375936780 1250 375935530 375935611
    0x30c0306010f0e15010c0f03121103010501020c0306060f0103112107091e120305130902030106200a080a0504090e0a14010b15031302040504210c1703 66
    0x4061041c22424040703c4c1d400b4008100d251145035503240000e00c0395410340400351020262120110030544200e4660151042e40790b0140710780d01001c0700155180e4800e20030540948510300d40d04485003400f29140b0b11030701005040510705001440150003504c2c81080c10840f180d000c10404288194003100e4550103c2890712407181031500d3300001c0e11003040c94120540e41e0b1183e0030b55400190100c90000305035402e4035000da00b0510745281c02d44680c02049880c2136004910640803e0160340c1c1c1d8042e504031102996480c41d00c0a0a034006501042c0c04080c103442c1e038011040b5034020540d6280100b00c12421072604038030b003580e1009104c2c100e507103503000142c1c5500113880017000c0c0404000f004064002010080101440c15000641d402c40c03950b41c000500389011002410a240102d505071007590040e0080c000f40ca07052078100030007a02e600000060303142011100070f2080c070903800000156844503500c01e00508016030a907007504028096100c8500300d04a0f1203041d90381c00c082c050b201790b41b01d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 375938030 1250 375936780 375936809
    0xa06090203090706030e031e160203030d05100501140f07020f120a030f0807120902150d021c020304020a12050115080c030f01020322110604030c0f081504030509030c030601 76
    0x4401406d80d04c0502d4601e05961007441118420080e07980000d40120905d030b036280e0b41c0c0602600c007450a013001d5402a40c076020100380403ca004040c0c1180348075450b04000c10b007902e5220301c01582d02130111540c50f90720103014003965002c420401c00a00500c0d000400c0130341c3c0c02ea0081c00280803203800322643d009542089080d4410150030072070316903100c00340c1e0803e0790305440c0015009198902d00013141c040d41e600c509100342951100684e489a1030b170f0f14070900c0c0d920b800d200c0100010307620501c4045423640360b040c07903c04400040d1080e00d001e164001c2040c94a90b241101024050703501c0c0b00e00782d80c69540c2c3c0a1502005548980318802010098041e100d8600a42c04150504024642090f09039004008001061032200e150402c01000050710124822182c00c05c4100103480c0a02650800c0000038044180022184034400b1100da103d03070031000700d80391281c260b01c030000c0c034030800b150380d07003d0b008a800031b80540064156101c02900319076144244c1000a840c04800380e005181361022035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 375939280 1250 375938030 375938039
    0x40b04090b030a03120c1206090b0910030b070807140a11060f36061807060c030c080c01200307030c0311030105060f0f040b1308010b1302030a060902030907 69
    0x107000c0c001c04084202d010f007010840c503841c080c10703500100b410b1200059966030314501d00350041c00000040c50f0a0382080144540300d140005c024001413181c1c92252059200003012038110180b207009403a07101c01854a6038941c0c0e07100740d03144480944500305100314010400401c8181d000609080c10b01076407007009100c1c1001c0044d0608801420103814200c0744010411441882c000d045560b01490003006e1509070601030b1841c40560038a207103c15802000c080c0000e03469400d5070300d0003000728071058980a81c0d6981c0300b42e07140c0c6202d00000300814100c0d65408080760038040a000012141000480c000d031900d801c0c0c0d0414103820740304c5140c0810100500540d25130520030040e14103c90b046c02c000c0c0030035024904105004c14812a07105038000240110540001c000365116041032400d60341d11a0744a141c80c0b20707180c1240c0c0c84034100c19141c00340000c0c2c01c841401041c4241e10007400e01e04003000c6141e8a1006948021f252204041d110000000d10101920041d8030449401001c2d00126080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 375940530 1250 375939280 375939299
    0x280206040213090209010302120c041406010905030d020c01030b0103140406060f12050601170a02090408030103052a1306080a03050705070501030203160c020a0e070314060415030201051e040b04 85
    0x10752100d0b40420701c1c1001a0005807580f0701c45c0c07410740b81c04580d403c040d24541040c2c03620344404044001e800505018928a088a00b080d01c540201c40c00d89034000c8950311102899901e40001c0c05d02c0e401a40030808051655000c0ea002403141c000c10700d400310313101203104600303052040700382c0303003221101d54440041007c414182201c0000d4002d9859404600e4031649416555603010b0040c41c401555810075000a0002004042e14095001c0d100c403915183c03e08007111150000d20060b1024002c0601010a94000c0c22038900708402c01e5400441d200301a44c02d1004454405091021075913603900040350b910400c1149180c120701c2076031000d5450903186840303400c080265101606050051050120b0b6200803540d0203d888014900f4101610306400042d100c004a540140d0018204034188070555515810035810032003101e00c403103415200e0100740b00464040c1454203240881002c42800190311820041540c0700048240e050380c005010b90000c02a80a54810b4402c0a00042c00300203a882 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 375941780 1250 375940530 375940549
    0x11b020f06070803150a050117182b08070c030e011419030b060c03090d0503041a03090609070b03190b060a0f0206090c0a0b070f170408150115052802060402 69
    0x2902c003450024581f4001921203050450024110b0341000700090607105041118280d200002c0d04859824030f50903ca03403208182c1d0390050501540503039040c2209802018018059030852340c1e0081681c440343c408480c844a0b500303505040004440444455071182c01c0034200b8008181d10501c2c04001c819005403c903190a14581d01589050005600425010050341d04405040e5840d00c00110580b908030f040d4803071900513403916894010150000340e50700c2c0c041c52140c41004201e07101900e51074007d40d40d03200b540c0300b02c07907a80030200f0000d5041c0b00c0c088a1500e4512860030081400d01400c40040e80300c0d0001103250b40011128a03d440c40c81b0390411070190032440d0103002d091540c1049000c02e07800c02c0d0354010110142400101c0c2c600f00f246010300880322036041000c140c81620110302003981d0b9031191003011401e02c80c022080c440c440503100c02d103040f100704009807043d04185d1902a61181c005080d94001d90b03c48070304030000f2080d658250360340181c06501038840ea14203441004079461 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 375943030 1250 375941780 375941821
    0x6122706010e0a020328020301170f1209040609050f09070e01120201050a050904090c0302130c0806100e090103030302210402061209100212040b070e011b020f06070803 74
    0xa0088004001c107202d40700702c40350019202c0d0400b51780c1e03542d100e40c0845001c486007070103a01c13200707050403540c0e6200d40c503030195050b41e20b056124064441901d1203a542d402c1c40502c40d014035040f0b01302c02d262801e00b00c0300034072427044007030b1011a103103603210501c41c116901254002c0c417004011003000ba0f843c03810b0141e00080c02c84030313844180550400c00543d890b1214460003d043c05400a21040c106018005035000c203080244184025011450f11500c4405d040c03004a003d1070039400002c4800f100ea0180490301c100030350b5421030654402d070401c9032900d000403841081c0100e403510184240c031076060340c5003e5070080d02d01603590700a04c020100c10b00071425112580340301d008140801643c401c4121030706592552401c8a664540d0a007150800c526064483ca070544001010155a016858200c0c13159014000c60708a540d20f105054440241c151241c42c005041d0820050700801821098956240080c040030b00320804c1c140843c001d42d02014058a02e00e50120400c01401c1d0f030307043d4504100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 375944280 1250 375943030 375943033
    0x10605030d050c0a030f030603122006160302031902030117060109060f0501050c0f190611090a05090702032a19120e121009120903050a0204050402061227 68
    0x19820310140f40d00d4040310340004042141702e000c0300c445a4401d03000307000a15080039079410784600588029080003400c01241034034841200090319110408204544110030031402013044204008044000794030040204030010341888084070710104520145000c0c000700d5130900c01c41c1404030707032481c54250141d011000407400e011003407090641c1e011030a01210020b0a0803920b030000003044038245040d84c154404d00707100e102114034151825640c51064140142000c106a04030404024510300c03030107003402d4200321104000c201c181084690598002010720641e418a441403070008400e80e40111600a440172625480d004104140304103d4066060750070254481015a20300011b40b144001c50000d0016196504a661b01c3e0f55090302c0c5020000340546204210380745a0900a11282c07070b0580c1d641d0002464a83c829000345001c0f0140d90f048001400c1c1c99506034204809820010008c980002041c409040e044405954050088401c0500c0e00130050350002441c0c86e2400b10035554059 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 375945530 1250 375944280 375944287
    0x31d010b0f090a1d030d0c030e060627010b0301050406080316020909010917030711060403140a030b18011703090a03060506030304080a05060f0c3604020c010605030d05 74
    0x80d40d41c0d007500201c0200e01a00c0181c1c042d41c03610700e0750000700407600541c03044051495585071050400b10003400000d000031800c00408080c1d44040f822945005102c16055201501103080d03031521114000d25014603801d64000d00e0903c0200520081c003c1c0d2120b9008100800140070600d02070080a0191034001c00640c04c114030054040360181c20300740043d00441c840d0b000301e54206420740104810a4001c05400081e106001e12000c0a0340111013450001307400004c0a91403420100f1018002c81e010383c3c60104102c0460b040e081d007948100381220a050342d07080f65984a46030800d00c400d1003030f8180d064101c42d600d8001940310a502140340854150010040c440203991a5512036043d40c0e0040700000c7d04bd5a2980401d19501c5035401c40290f500c51500480d0800100040003881000c04030141e002e00c0e1160013818a40f80241d44038440e08035020301d80700050041174011140701403404401000181070742030215041340e02408009a80d40d455030740c08c0c080d1f4141082425a034a0726890032528 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 375946780 1250 375945530 375945551
    0x405060402090408041d0a0c0c03050f0c0709050108010903080606041d061201020f0417120711190906090b0f1008040501140f070f0903030509010c0204060308030106031d01 76
    0x49448005000902c5044040c0200303040c0724042c019100604000c25424602030b075080d10000713007000d08031450303111141003030030710800141300300c1d4141d4016600d40ca950b410880e1807400c40b11680c2080340910710720710036410002000300041c080c1c80d009205d0b4500004840e10503040091205100401a90240c10304110401c003400580110352401100ea200000b1151600e40010320720440c0400100c1240d80040b90107000c6048641c020700c00c499081d81c90701c0c440c0420804140d00d07207000c00d070342804402c818012080894045c1c080d003807030142d00800f014450603d90a403004103090903042030300340c03940c1d6030000e000030700d40c034030a000d259a411903258445034541800203280414902d000f8042110300400715003004400d40006d41d002d0882e4210891500d041034030720b0a14030044620b2000900603003c0ca4140743d018550100951743c150f40c8007464500540015640c0071011042240c1169660360008003017090b04010b5800f030070340c2d40c2c3d010801142a141b0194030032901401c811450745080703203510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 375948030 1250 375946780 375946783
    0x106020d0305150d0201141b0f240604151502010c030506061b03070f121202070c1e0f0807330818010213060809011a0607060603080c010207030909050405 68
    0x41c0307921003100d410318811300340e02c0101c9895403900313035041c8208000300d5000e202100301041442552200d60803100c41643c1501d100d0341e11411403029408901c001078000c0c0c1541032021a643e40008040d2010440d00313030a0700880200e0700550301c581184d006181406075000d0703081c0118001075004c1d250500071800c2110001d03645221700c8119000344418449807007140b120078020745914030b820210300e1008041500303004c400b0200c00c040080010b442220011402d01c0c0c2413080c0c402c1d298201e500314622a0403c11300c0404406a5040d515092a80c2c00c0c0000352842c1441204000c0c003000c1010704001d41c0392901c0c1007040001021324560141e5844500d6480034042c480e503070b64840503444c10341010749960802d2410312007a01110361455000080810400c2c058545030f06c111252552042e4184d03803042401800c840003c2c1003002400b101004c41d062034074000010344003160098100041580c0e40c0e40d161446603014803240300d002d075004680d210a050f04261114002c00840505014520f010b66419 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 375949280 1250 375948030 375948061
    0x51003020303032a0f0c060c1c0c0504170c03010b0603010312031505041113050103060b07080f0d060f030b09010203040c060522081e0a080304170c010c05030106020d0305 75
    0x3600c0c1d90042d204c40075000181e40d603080c01d10b89001c0700300c0da544006007442200558410101707101079100b01c0c030110f1002c00d5280200c81c51401c0301558000001d000006410150402c82d51800810105201c085461881034139140304840c004801400000201824182541c1500005911131a0140010008501d090144803030000f228500014807046030f0b2102c410708600380d004103402074a801040034203c54800000e0031141480011004216601c07001141901c2040c056150041c60034400d040005a00c04081c003c981c031114006810030390510340700021038050794805d2546055003102003080c4500a202c064200c54000000e42c958030742030300d461580000c41d04c940d504204001604412400c1000304100c0003c0c410001191700540c1c03040703080ea43d0f100c4031250011612a50203a038400d40381c0001c025000c0e03903014050700c0c05c0da9610b403107105055000c0300c038940c044c000400c040300b4807200a124550704501c803505c9a80d103950616030000c0c0352880400d50303107083c5850001031040516070701164 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 375950530 1250 375949280 375949291
    0x2012c060f040b0408070c120309080c0306070906050c0a06051e0c07050d0e031f0b030c0109030b0103170705010509010515030a03090b0904020c01020c010218060a050a080a0e0a12020105100302030303 88
    0x1255030340e101914000c0040340d0032390f02c060500150031035013400701a4060768a1040f5058401100c04e40460b240406843d0036094034071101140c1c0c146820041640954041d2102c1071010055849942150b00ea55003a03030002c48007011030500c41e2030001c14001c0c06a00c09a08000902011402e00101d40e90755070b40c651064683c2000d001d50410808280d5808001940f41140c0c544003031684c42e20000c1c0c2c10350103424540500c9102e809180c41b50000c651280c2c4c20f00c811250015403d803026441c548030581c1c0c0c48400040b03540d1400381040300b000807403400d00a0b14001c404220000403030789000c070500347d030b00d40080d1b101e40d1207600b050881c5004254040403820a542062185a0340d076040a07000400070320410403e241994004203466041010640c060610003045050505c81907404a04001e4140320b8000307040040f07803061040841181c0b00b0b0101c26801408628001908400c510300b0601d0125042c9040750704480e115160b640003942030050641145840d41c0852256045a0010340c590000030030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 375951780 1250 375950530 375950543
    0x16150801180603021f030605010e060d020c030f1801120506130b04240812030717060f0604091d030f0901080a0204260d0e0a0506090102012c060f040b04 67
    0x90000e140441030b80198000d50740100505080018010fa42e01032400301360124012901d0003400203480c0d4060411310705c01500007041203181c2808004580000d4220b1000070605220920030401c4c2c1a0303da800821980200f03812001d901a440e200050002e8941c3d2411039140381414180041c944420314a00c0d10018401d5003c21080390880c08140109a1011000f10a044a194401840c4000300000081da2044420307175101c460400003020b03c6101c15208007001032241c0c0541c480660380003001c0c981148006007081900a03400c400a1220740050300080c205a1340c9180c0104a084100d80d09851321095401031070410001c03c0000307400d80201005036042c860b1510000f00d50b0405541140c000e40006410740304080e00c0f0840481c0c2441d035842c5059400c0c400c6080b01004940540a00f60154100400210b50b880c00c00003032103141c2d040000f4003410b42d03498146007034210410840c240c000110f000390482240844508403464214003400d5951402d091409120100d52121912544640c0008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 375953030 1250 375951780 375951809
    0x1206030715020a020409050f0f21181c0c0b040503010f1a0904050c1f11070501080c13030506010902090310051012081218102f040902030405010906050906090d0f0908070816150801 79
    0x18418033541201e0f410051841c24951400300d00d41d20020050415500290000c001041950108004507030300c000c5002030b802d01501d1000503620300403c0090740984280d0642d0310b0a00d40c54085034000800038601d07803c00108154050200d41c2c01614041084040001020064034160018010440c0a414201d40600000b00c64802444843c1024000c6a0000442b07006682d2002d0590003500801003151090145015000c0401900c0c060307140507445104904c42104d14090054642c031812550482d2002e10900414103456440c00c0014880c0707076440d8404a03041019941c0a051075980c2c003507004007628003100700c40f00e60903c03181c00c1d030036080c0182020302d80c03001c01c540908240035030f41c020a42e150001003040200720045d0041016144603600a000c20f4070703010141ca850b10411034050510b81c0c4200408035456200b501b102e8030180c40ba0a000e040380e5112003242d414210241c04ca401b20340c0c806001c443e1111100c828250080440c031100c981d02001e0044010040d0806125890ba2440c011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 375954280 1250 375953030 375953059
    0x150c0611030f161103040e06030c1909020306040905030c06041407080c0909070f030f0b0f060306150f040c051e0a05030103080c121206030715020a020409050f0f2118 73
    0x407000c2059801380d41046a86a603910300342801c10020842c3c149010380514041900319003814640b80305408104030002c081a41800410ba0094000910721644140c64140b01008150207200410800401070050700003441e280c200f500c0742110200402c14540d202d0343c820040e410020030103101460003164400780a4840030621850000e9035003080300012041d141c00403c0002c040c81c8425003a21607410b420740c03941c0362201409680f20444415800d0b40000c00044e11036102c214480700d203c0402007813a00503d0746800810100e030700c08004070010540008400c8458494075540407003031000c4c250030034503014039030200501d64001032000400121000c036148180c06003d1201900d016041043d117511a10301c1810240122410760b82c450003805a00310100d07540e14036491552000300b151700105181d050b19030900c0020300d50345800740d92038042c2c0c1c00045035140061200402c0e40c4a113100800061001c00c1c0d680c16004a124900f003c0070104028140c10026920f1150221000840320003010f00c031074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 375955530 1250 375954280 375954287
    0x1c060e07080105010e07080c07020603040605270c01170402180403030f290414010b0d09050d030c0207060305060a060c08120a0e0c0a1a03060109150c0611030f16 71
    0xd58000029a509010010601d5051541014414075a955410030241c4800d8a0a240c0d4850303080080d41100040000070041145a00035903000002c1c4140d1a00728010008040000320040c2c2400750190403d0318151159070b400b014441d007420300307841c5002403824507070300140d081844420802107184440c0006401d242c06940305081102c1940f80900c02075801007090703150012120300c5c662a031214080d8008250800303210751040340391600062401c990074106401a150000320450aa003604c84403800c00040d070034003d56941c00140d172804580103018a40107820901607400041c101407500301001641c0c0d07a613170840d2003196610b0800251025403400d0a800c80c0c41916001c44030072580c81c050141c604111b510004043e0110070507150f42952990400c40208070520400390450440700708485d14980079001582c004a050414113009550b6030340301039440c841d80000e0303070105144901103404d00285008010707084002441030341c030b5850000566011154060070000042080340182c2c20801d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 375956780 1250 375955530 375955543
    0x1401091d0303010e1006050307020607030209120f060f0f040f0821040f0204060b0f0906160b0103030306031703010e0a090302160e04050c0409120507020607210305061c060e 76
    0x100c1059036a60342c0c58005103440300c541900d03144045040a03a00041c1d8910400c00d41e4081c074030a80c050050394946d05801c50107900036410b4070740d21122941c180701081e2030401c0740d00b06440c10b160203001140751902a005014100502002c10f15280b41c0030071000a21040c0000c1200303900450790b076204c0d91003030482d02c034a102195024806030402070502c81400141100200791a01c00c460502c8400d17114505d048181c0244040c4c04102e0b1418054807520345007043c06048860120b81100321206c0c41c5844602c0d00c401d0030390060340400da95490a205100704d400924003200e59100702d040c6594035010060702c0e030f03010052184004d255980055000c00d80b0900c003a081000c0a8030b41c0407040c50f1180222642078038183d408988034400d2500440842c02d00d8000c14505070b811808036400141040c5007915194010713141203a00280c1000b5200024842d2100a0110010042003d8075075100d610040c2c12914080c00c1d661050041c02c8440041d030241041d42048103a1000b03011510b5040300c0505443c049 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 375958030 1250 375956780 375956831
    0x1060315064a01060e0906060406020c0603190c11070e0f010311040902100210060918140c030105190f0b0a140301060308120f130b16230301080d03140109 68
    0x1880b00000603981e640183c06400d1880104e85404540e00c03105c0c10801c00384258810100945c0203882e8448076403414502451744641d0940500c1100d810b0308140348210307610703480710101140e444004c002c1412000c00429001d8001010710000c182007100f1010340b181c070144401012580c40501046098442c1c1d04031011407a8060145e080084a140e406516640c0b40f15620105510b0550300041c10303c10b0b40241c02d030801d05011a94040700d815144d81c00307803070140f84040300d01d44288072188800340c800f440342920480541b507160035140644004030040e5102d0008601c009410482c0346819607641c0082d076002c40e0280d9858510402070500030034007610255101a003582c3c6c1c081904044403c0481030385e80b00e198406e010729104d0f0380303595413418545140c01024240c840418001039144d41c40c4d410f140403141503418100d05030044581d20600880e04e0880b031003070000003c001044440b004200d80c44107070085d4181072169860390402100098814442c1d030112a071641c00c2e100c031241c1101000100c21 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 375959280 1250 375958030 375958169
    0x312091703030613140103121202090f0f0d05060c04060f081510020c0d0b0103060c0203030c03150d1407090b030706050d0506010c14070509010b030702031b0f0106031506 75
    0xa41e03403400e202381d400309060340f020f002c94000c0031030038100d800500c22600440d50040c401002c100840c0103101c00340f0450b0b400c0c0c070f030007000040034800030410820030940b103090300b03c1d80240d0740c605244d030040a00040100100030312244800380007000c0c2c00c600f2641103500b026115245c440d803401c0c1c0102d190075a52052150000c28805103c1c003401211402a8107a038000c840500000c003003903200726074901c021500300301c0c9101d05101146980342d281003003001c4850f004054922400c2d81c0e4681d001082e0180750101401d03405180204240001c174001c0c801c0304881207025240c0d00c0d143c424064a02e100345200c0d00322880e41d49000504503805211b481f012a034008000b41050b041a20046584614501800d88101c50b8940006040507040e000c40b4401e081d5940554100340c5140416900c1c48000c0c04040c0f201d0040241210020509210b00c01c011801001600800020115903004894261308008180d862521341c40100500a2228a01b0f40c1c0365100c0f6400c19080203480c40d102c228440e00340c180d80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 375960530 1250 375959280 375959321
    0xb0c07030203070e0c030a020d060b04060302030f0106031505060d0e030304030228030c0f02030a1502090103050c090102070e070504050406140f2b0f0c0312091703030613 75
    0x11000095020589100b6000c6940e42034454500d00c0504508440c4000c07615001c200188800400d500a4401040614004a801a01d820131414160015001540025804420070051940201c031240c01000c482c00d041215620507007040c4d11445550007254051200040c3c46940c210304e5034010240403681e08203036a03d1b42400d00d4002e45904178076003d02c0071107403802c0d500002910380d81a42d0960640c503803a401e1034482d007030360355480c020091502a41d142c02030201020100b000042000300d082c8034400c00580e1000c0860000d0212880079108c0c00d29070405010070708503642c0000c0d8440a5844040c40c02605640d484030485280c0b0580d0005c41d045030400400051600b0002a61a000001111080b180d100c0d0071051107007011411003620707030b40c101c603582d600391401c0d4000d000c003869406200100349041c0e160320348004001199004503003149001c168000115401080c400c0540401014805000700100110341c6d03034000580590b201e20b270540311180c0c03004140e03801b840315011074141e000394 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 375961780 1250 375960530 375960547
    0xf0601060f090f26010e100204090c170a0209150c030a3506030a082710020a060c0903050a140d031e020d02040302062704141f0b 57
    0x940c8a030031402402049101c01d0100b410001c2c3c00560080d201e03e0118a55030728581131955004035109a0300805039541c842c150300c068001407041c1044003059010143e950b83c50500c07400304990b00c0006103c00c010048035440b58810b00d040d000c07034020200c40c00144e01c038a00da0001580c100100c0140508404000070416510b00001c40507241311181a1034130100c101c0e04003010360948007503044185a80454500e0001d0000010810310382191014084665101c02031350f5204140d804030808041403151004618800501d41d10310b08000d1405603451040c42d05180c802139940c240b0300f60020f244a4481c190408800d10400d014801550042c1c112080c4107803c0c03c101c1104502044520702c1409a0900c55291a00170300a003000c052156441c7d60b07110b80e200c19130340d0003074020b0f00e402408e01d50200700010160b42d4110142c060b032200c002ca04d2130181d04410f6000f0721b018001c2d1411f40600d003001041f40c51300d0003c0e00565031020000905082006420b103160110264680007039882d100041350140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 375963030 1250 375961780 375961787
    0x1b041125020108100e0f07020309030708030403060b010212070602090637022a0f040c170609010e040f02040e061302030c0a0f17070e071706040e03040b07050f060106 73
    0x8200a00030f03202c070001c5803500206440c480c2d0550158180007070400010904030b041010405030301c0356491040c0d0341001c41d1880000d04050455110003034581c00810144240309141c890300c00100c01c02d000421071801400641c0110340507040740a4103032540410040307050b40303507034007100c1328021f92180d126810040b0404000c44150105280c0e0800b1200304a0000000c2c0006503a440400020080d210444100c454011140034126802600305400c07400544583d00c0c0d0303000d22041a29503464139140f4005c0c002510101e424010007a620503800031004200c400b41024086402903000f00c041d8502d0081070000c500681440c0c14081003e01c2810708020144e1030070500c95074014070860035100c0d2408039804000400e081c5010380340c00120300078401c1080a5445150300c4018440d1001c0d02c54155542101d0600e2420072220200864030b81101040d000d0340b1703030300c0f03240c4d2060b0212410402842d042c082d0f90b503280220f000d017001642c00083d51a040c05002c00c084100c501812003268529a11444001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 375964280 1250 375963030 375963097
    0x71823090d020a11060d0e070f150c020609040203041b0305071a09030312060109080d03020901030c170c03101a0c0c010f020a021306180605030f1b0411 67
    0x580380520703032448016600c04545020415049a20100d0a4045208000e45580500400710700c4503901d01d0078401c84c2c1d00511449005001000340c903c1224684180e518441c2d190103003803810003402400d81e400503030301c1900784e07103c0c1d200949005072a40c2c2c42d46403650800411000a12800401c00c00010400c000000e98205032042070302901e82404030406452a40d000380b0103c0d9906030800d2280d030351054002610903501c00e60502d0a84401955912441c3c10541c0740c07100307040001d0300041c1025695070140120502146c407440c3c09000c01d0440c007254240040054140703e800b01c4004041184041c4608002003e4800420b010300c0300d4403661101d40140c1e01032030508900f8024245800c0b040d601960428502030380f95000b80c14001c010742d082101c840d191520f130300c5103139640e03020114002407080780c0034952000400001501900b007504061925464081d145103030b501401020b03031004005680070780c91010035140803614601400601c2e06502640346070f8200240e0242410010001c42c01a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 375965530 1250 375964280 375964291
    0x140703211b0f050706020702030c0d200d26040f120c0e010509040b07032307090806011518030501230108074202030702130509071823 59
    0x45820800031001e4641a00085481c00403d0040c48540c0110f01c0799001800307000e10040c1036804000105001a850800040e07050352070017066841c18141c20383d1203102c0d0481c803038102c3c2c66204e4480b031a940d51100d080d81a00724941c0510705c0180082840c07040b015075014007041d41d1082c0780d40e6116180c9003c1c80e81280015140078203982000551400090718880c181c130030242400c0400d03a116100d1164003103010700074100b05540c414140e1003810300242070022648104c81c400d141801c0c801c000500540154001402e02e8104d03000410516100c014140342c441450f0502c14421000c2c8409505030721021350000c0d04a508200c3c5440c140c102c146c4101a480040b04414181039032104241035031440c0e98014400b02c4502c1480c0d24608004140181102e4402ca20707800702103401c80341d880580c3ca1901c00307408000d0381c0f0100d40481140b9000030710015802c0c201004000c45c1c50702000460755a40d00c1d22a2040c10038030071402d03403508141900049841707031020313031a0045800c044601001d20341e0110f40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 375966780 1250 375965530 375965561
    0x1b0e070c0c051203040b031009020315040b0102010b240702040e0c10020307081c1b030f1d0705010e030312090a02040b0103091208150916030b03060714070321 70
    0x3020441c0d2400303c40c60f03002c100d003410086007031500300003079440b0b181d20151152050245d40800000c1c05070380b41c00150710a6448495600d20741d100501400141c407144d00a881c15179040030003003140c0e92160048440c026504910310201d4412a2145410510ae0902c0181d0000d060410380080b00100090104000d142621a000603584500d0100d84900560500501c400d104114034811401c1c5140740440001c03051100013584640b2070420740030303c140a020080801e407103280c80700d006c1c0c80f248241d07201c0c0e01c5010300c0c2c024880140d02d400741e120b0a160184c1070510a031000c1c2c015107a1010816074040b00b0204902803100d0519101c156074407401d12500320710482c18601412070a5100c4c1c02607800c040d911414101d020035848100b5900503c0c01041070311300e0022056070311820307525000d00340e02400038001200c460384030400008094402c01820240a136000e0300134008050740c4400340655900c0804012a1a0a800e10b4100c5401e0b902c40a0713110b15035071000c6020a1441183c0c41045006982c91 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 375968030 1250 375966780 375966803
    0x21c140321010e07051c1b0206070905060318150a09021f050a0f0e0a09091a0402010203120408090405011410030c09030212010b18041a131b0e070c 65
    0x400780c0c1030022007401584642d10380300f0080b61031070f401100600100f00010300528240b5000c04800001c4441c250400f090800c2400c000c0e03202145c0510501d604a05186000300308181440b02080719840081c00d65072805600d801590280d01d0103006103c04010407800d0035000c3e04180354060003411503801c090744100a00702c2105800c405560300030503072001e26101c250905051000c160b40c0c440b81c160241c0306000c0e000c440710440c2d42d585025000600455035001451a42a0501001c0100720450b05484600d9240c14400541c1e0000180c03405a00e00d04829182d9030b580d890018544d008000780340341c109041a002003401c80d0a080250000903054130b030185c03240b0b41020220156881c0d8607021001c0360407102d0a1000d0304001090844907246600040b408911041c089401c0002000300c2601355000c403402e000400c4030115180703000e80c1c0ca90100d290f040c00c00f500d6510040c5603090f0000c14440a0201403100c08070224000e038024503055008103424a0164005400310ac2c01c200111104060b08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 375969280 1250 375968030 375968077
    0x20f070308160804261c060b0903071503110d0c0f02010911010509041e0603051b100e030a0c0308130503070f0504090302070b0409150803070b04021c1403 68
    0x114001d03042c2207000e607220b9600342ca581e00d030b08a5100001a0b20003c2c10f07400c0c0b13056180c103054040184411101e034000c0080440c042650001298000d800119403000c08120040c0c5544c0e001902d0b0003550309d400381030311001d11020002e400410102c00200080311300850070061102c3e00c0d0382302a00324102625459404107094004900300e0303031403800c018414030002c0707905111944034502030710317444a02800014030640b000e101801d02d01a4a42c6402c05962142020700800c4024010f0399800040b055254aa4049543c0003865101280c003548041010116820000f65010402598481e42000c401080b054403428082915406080041003400c401c00e00041c160900050174411a25513002d038030105424042003201a100d252002d4046205400d40410340c5400303480184020305042600081d0b2030348110511810800d95031043d0610780050141c80b011403021105280c1c45a412108015075039001d1a40780c0000c09004006400041310300c5d1440c110100001c0141020400c40c0c0d10020481c510303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 375970530 1250 375969280 375969301
    0x14060403120902130222090504210f0f03020d020a080a05060f031b010903140607080c04081e01020c190b15011b020d15020307030e030301081f06030204020f070308 72
    0x20100081d04448050f00c807100401c0309070f015060388128050403811b0780e020100d44140c00410341d00550603d960b608184030400803980320140b00e03859814200ca400e5a002c1c40b01a010384040000001801000d08002d030203a072017a2304841c0302015140c000c5440d4580c05000500c0f000c8100c0e50f9144582c40c2001282d0145000b050030448040020001c0c20f4522007014080301101707019003e20b0510540307035030100000e803203d00c010114001c04001441d0301c1c0342ca1315004082c0040a0240c0f00c035501d040009200035070002c101c203000c060b0130310044c24000d044041c1a90092041c0801c00c4002e0051321848090744c0c1ea03c0110342800e500403225034031070741c868001240c0040030320440345000c2201e061705c411400c580c01208503006400140f000100c008103454003e540803c9024441284e82d0000400506a800d44030304e0400550403802542150b0401206c02d65403c034651606040d6148011850b00044107034020300c014660142c0195181c1e404000d52031441c2c0c0080c07608030041104400003c003101c62 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 375971780 1250 375970530 375970541
    0x106030614040902060408070b12070503060a0e1f0b1b070f17030c06160f020604030e24130e010b0a08010306180b0c1b0c03070b0306010c1406040312 66
    0x18905149894a0303440d07001c00004280c1070008076001202400001844e030300a112310801840500b44030381c1e44180589500100010041108042c00f40910074070a241e121961424195920a050460151114101c601c50070031541820a101c85220001284002c0b00e02c0241054404e051003644400c408866990385680c418041d0616910014a0030800c4118142605004654480c1a24540548180018180441242e4480740d02c03030302c202c0e41800107038000d0f140915140180b000e00540c0c01e16550040ca0f841060100382d12072040c1c0c4070a0703040c0c1848044103010b542240c140196a4444940110010749018410b03000049002000044d01c5018542220480c1c1c843c1d0382d44050b140e00355610940284030f05141c80c0710344810100001d000031000c0361503030b015020048496480301c0c0b01c13403c40c051072100c0304101340701798001305441c80f20381e01d0010310b44051352007500c2c146480c0d81c0d6210048601c080070203406040c030795003034100ca4041d02020070382c180954042e0780c551501e2890541e40c00251036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 375973030 1250 375971780 375971789
    0xe0105090a0e1c090b0c19030507050a1b050631120b0103050708033f0708010513090503070f110607030f080606071a0411120f071e090e0313030b06040501060306 71
    0x1f000000c022182041402c0d19030b120901c00e0a01d9404c101561b292180f60068610f0700f02d4116400f0508400426550889900100400c94030245080c00e00c84444c0d1029070b00895007801d2041c0d480359160607011107056480605550710310307180c0c01c91490a00041c4a0020310090b10ba0340900c403030228050802004a594145240c6101ca0252441e904651021400d051315268040740101882c801911640350440c00364042e640d8481680d4104802c00003040c034004c8440c0201841d0140e40000500c021003620007668110011400140641c1044245072690012141c0e0090000402c2020182c02250310190b0003080c2d51090803da80b040706011482c402c521380500a00418000030881e0602e9404803a80540305034108110400c10ba00801c50180c0150154419a0400e89410351181e504100d5500100842c0e50f000039031052288130700302110b4190055081c4651030341d105c0610101c0800881c1c26060401d104101200c0d580d0801500342e81082c3c900740e12481c1020000144c051103030044000740c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 375974280 1250 375973030 375973033
    0xb0f0a0516050702011e050309070501080105151b0a03110d140904020304030e0907022a090412030204031e060b1f0f020c130606020706090e0105090a0e1c090b0c 71
    0x200780100080e01d0395006403400300e0402c044440002c0c2d98008251306440b400c0110f41340d071038803410310304415400c1c03501b00d4101604016078000104a9a540c046594040e44154a8207a0f81c42c0d041c0f0b039a607480c442868036440e501d0f210300c462881c10103a0124a9a228038804019605042c140240803210151581450b000c0f0030310501000701a40350070742c010754009100b03061000f0000000030100d42404012a19440946c001c038050800b448a941840c99100c80740c0c085900314141041700041303201c400030304094640401452030601e03850081c0c0c11100595005201408002c003a83c911308540a60200110740503414003000540c0c505084440385050380005803c04030707140141c00c003140d02a000d03806000440c4104040b920507074a400c5081c440302c0d0945400851190f04024002c0c2c42d00425030300c000c0070450282001c001001c4400768003415140200c603003c0140d00d5a105440142900181c460214004e40007102508150030300803010807281601d4030300003160388801c03140340790040c07549c0178219 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 375975530 1250 375974280 375974311
    0x70f050c0a0b090f120307061d12030c040b070f152003060306070e18040c030303050108030a020d050307030204180506030708010e030403141f0e010b0d0305180402040b070b0f0a05 79
    0x258549408583d4034002500c1c211ba0600c1071949422095588000320450701140d070010b40e0031418018045413030340e80480ba140724910f05040401002c82d102c0c521880a05000105001d4104040e400c1000d80054020821364504201d41c05c000c0c0040050f4000f0400990156590880c0c0341c2c0c0c0841980d00ca810024007403e44d541e120b03070b025241d150b107820055500c502e401516500640100308881c0c05180500200c501c0300341585005030031194181c10840580c0e009100c0d24141c0c550004000a0314850703131400503220f841c0c56200f9400390249070015860608013004074070084400c0c1e44040d128003070480480b0495076440400500302e1b038008010607110b401c104007d0000c600d072000c5100c00c404905080310105110007610031303000600548000d42d210b4881c200102c05038024010703e0800f5108030369218110b2000d942c007501c41c0c81040e20001d091400e40640c05800e542c0c650564000301820010260380342250f1a11a0703220004854440b00f4515050122710058464818503104402c03106c204420b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 375976780 1250 375975530 375975559
    0x1020606010804021c0303021c0902030607030905101a132708090306040f0506070f0512150a0f0306060b1e0d0f14060108071706040c05070f050c0a0b09 67
    0x4020740003c20a0b40c0106002c00c01402114200d001000014001d580050310340c180303903000c03070001100c007039041e0051420100d00001595010035629040b1180d400d000505d84cae1a03107009820000f40c039050140044c41c0c1000d402c00c4066080c00704c0e8086030202c2d10000450030017050981210503c0d141c2410600c40c071210409641c0c01d04104002d00c9005848840c04c08602c840000e05d40501111f084a0410072904104200300c010000c680e0881c8150800a030420a90302c0028002e01614805000071100c0c40040b40070110342c5072031094907002c050101d01041e900d6000c6024241103134401102c0007441d1010019080c0d401303800740c6202664002405070001d01304c50146800b500410803241151766184156280760791a48140c0d00c223a240c41c9584941c51074181d0014060000080c10403090110281060300101d0405803d258001c1048400080340382c5041d004035428010301d01c0050a03081c95289070018801e000035800c0f04128101c40b440c07555511030f00e10108a0003205c13600c0350403000719092047c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 375978030 1250 375976780 375976787
    0xb06090f090304090b0a0f031110030506010c0b07030e0a031d010809030f1e0301121103010e0d031a09040b100f06170604090506190c030216080c010617100f0504020102060601 77
    0x204a500006c000340206500c40744451403003c5c199100300d407a000b1201c04182c0c50308007001100791b080e44500303082000741f5080340003802c1c1d4404801c00611240312440042ea04e18065800070003140004c00444804203414640078040384600c0d1074180452844030030314034281d885040f1051084d0105400341d403e1490200d01100740c0e80140d0003102507070891000c540660541103018600924010b100d40c0c0700c0c0c40172803d01c080560020311016000740d04020a940c140040060701107102c041926001840c000c00000310f00b500304840c40c0455003c1c0642040c40240400565814082c40b618400038003150f41d2640143c2441401d8800d900c041860750812110007121034100b554005800380c0041080c0c400e61307844604040d004c54001109118091060701c0000c1107100705e1410308024202140380c0010110114801108928020140e400c001131001c410403007074001d41c00421540c40322000d01c018403c451500c0340c0c0c0191625a080b46402c0c401d111102242c002d00d80240d8040e0040c002c42d07201c440045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 375979280 1250 375978030 375978041
    0x50a0e061005011b140f0304030201030b06030121050f0a030c110904030c08031003150915051302040207050c0a23011d01260a020a081b040b0a090f030b06090f09030409 74
    0x50303a05402404061405c46414410941514020006181d88905500c0090129099040054007400c0e042c0014081d03500050620718102c1d03103c0c03445a400308a14a02a40307480000c0d44401060301810b11510101038002d030103690306911a520304481e102c41c40033130091240e4100c0d005800104034101010101d407800c0011030b04045050500100c00d5200c3e2210010500c100c1e050a01140c1c0d01c1440e50f05001031031030310284602c40234200f40f00343e04082000b0740403111181e101034030403580080c0d00c1007045000c0156214811028164450041d69a50091544e210000100c2c0001403031700314080e401e40c410380344030f00c201580925080348401300800440f9072201d420104580307400c1c9440342d0300c1340a81415440d889101b4018000d030755030100b108000d10b841e0020300f240d12a81a2074003803440500061041c0e6042e80c070341342d5815486031340c4c490086039110040c0c0d04c2003031102e00c0400040103200c039544000348542c06c2542c3c520392980710b480d5446c1c0c503407804884025440d0028031091000c00d811340c004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 375980530 1250 375979280 375979283
    0x13050901080a2312040b0301080f0d050d11120c090a1703030103030318050a080c0106090204120305091c050a1709030705100c1a0615040b0f0d0e01050a0e061005011b 73
    0x844411136000544a00b050b8000e401c00d0410f07510100040090003c01c03c62a04226002c00281a024007000c1000d0901e003d001c1d1903186664a0b031100210079580002074890014002400c0403940c20280c1d9a40000d0b40004d65081c0100789008010800d6a820520090784945801c0258038513807075501c08800400d40d203c8040a8031000d18440350100b1020011030a916015044007960360709003a180e40d0850b603195110703071600781c0188400c00840000c2801c000c480760301810041d40d44d602c0d45000803544c0d03660802d04d102400412100030280500040c0d42c262451140503420000382492400110902074076052541c1503001d58424002c50030704807980c401082e03407070800d10101c0d074890b9078818410b80300301140000c884400040040502d003070710042111204000c00700d40350a00341a14001107100c0c42e01c0101280d940040c2105603168282c2c80031803241036580c001c201c6800c1958810018280400ca003002512504000c5914140300b0031600b003c560307058443d240c1d864002ca4130942d024110020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 375981780 1250 375980530 375980533
    0x2090a090203040308090d0e0112050901020c1606020d1b150b0d051516080c0702061902030a030b0312160609020307060f120501051c05100213050901080a23 69
    0x800030341030005001031400b41d4030076100c1c04c17441c2c135012118503e061200740ca000f003009008003900310240d81016500034003078101711004c90709540b002901d07806403203003801144040c440c0b50345900072075030b00079116001e4540f80e0b420b548040c20040000c0350715480c407a1003a444000750322910800075910800e1407081c80203201003c11092146800202d26460500082c1e5164120f0207800c49103968108100303520451100d4103081581d03030480010310700c1000070844a8070203000100750043d0340c0c54105075140351024a00440e01c65966007402903c2e0b4116001000200c3e0074040074150514011444083c0705107a41724540c2040000360002e21000e08008040c1c0d00540d50b014078002580b028403080380500040e840e03410103c19080da0060064429410041c2c006107400c0c01801a940c3d8030110031001c4940d04981036003100b050400302d0400c41c0924120307800610004a40c00710421251703210084410465000390b0584e40d03014440e84480705140002c083c3d820304040051580350b01d85041000518040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 375983030 1250 375981780 375981799
    0xb0f0a0f0c1a1b2223090c07080310060806150a0c0309081009020909010c0c020f1f020d020d090b0922060902030a0617120307021203010f0303020c0102070b09040209 73
    0xf40c0d8407580c402140401545a0807101d034049480c00407444000301990810041d09840745484110a00f114100c094841c1001c580403c1d070a0400d07800791001190056280d6030f42e4105800421034082142c850200801c0d10400001d04034580b20349082c1c1d03c8541d2610036071504500500c00c03a84075503031610032001e0152444000c12460703400c003c3c0704204242600000341d02e01c03480c010042000c1004000d038007a68104050725280d9a0b00030040b40103507a040d100403030600003c0c0001406203440b10700040301d000b9002e40b0144406e0b400a800481f1403800d400b6140060312800c012100e01e25580941c48000d5010072603182c41c1d00b001c0e4403c20b1199090038003100d0030441e0000382c0040d160203a0002c16065004018840304031901e210303c3c002400e401c0f1685a60148010b401521440d500c01c1910030000c012001900860080c8080846012050301c6580d4948e1501c40085040b202d600040d00140714408100e40070b5400014040c042d500305084050a217030005c0200b00c041d5000000c401c0d005240903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 375984280 1250 375983030 375983071
    0xf1101110d020403020a0e0c0f1602130501030b0c070c050918030304080d06090e0c190504110d0f02030c041208090a03030c02120d0c08070501060b0f0a0f0c1a 70
    0x6401522a0400700003001d40d030783e40b03940104080c0800d04c3e080881e03441800d01c10b0108400c0c0c42e40440310440c514112054642550007001c50007000c01e250069042034200f44e110403550b03681e50220b81030320300c2401e1028003034446030074901407402011401408104841c1050004d03151039059958004a60001211147c10008002d82140c0041c2d0b0126100700b004107180c0d401c410180070340c40240640071002c0044800003c1a980e45c1c0000071420340c003886540d815054140d040c00340400140101520500404081c0e42004e00f1541c44450b0b190142854903041070070b59000350084130702840311040054203050401080103503180c2a1582100c4d40c0508201900540e181c00c408480254041d4607003045080c2d80b401401005e290300d10900d0b0349a0440102000aa6082400610100e03009102d040d12811a0301d415801410540c1061100001c0401c002c252168030f840104801d6146681d5846c42d1880303000c0a44d107004204030001e00c083d04207020070f060080c1228480740d00c812101528040000b11703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 375985530 1250 375984280 375984311
    0x180a11060403140714040c0f0509040e120702040f020c0c120709060f0501030e010e0712020307050d0b0601170906060904060f1509060605030103080d111e03071d010f1101 75
    0xf020031030740d165001850304200e01c3c00158011410703800c09442c103100c0350000b102c006040100c3c3e1a0701030188580865070740c080392900d40c00070044400d654101d0300b007004100c011009a40010b4412485903003014408040900c09000f82c60300d07004000300400b9407070381c900208620a241c400c625510745c411084006101040707801540007c6c03888200400c462810580010300395041400d1074000c40e81040c1103e00180340014415044511107408006084001e2000908100b02c5901c95503025070701407140001e201c581900c142c083d4109803500b05214070601c20901d41100c044617a03210300d4001d10001082810f1540519a10034828400040d890100c41c079020100c41c94203072110307001181c0c07220501c0310059a100c2d81015101d9420180c0c11036165940f110703c540f0406000510f440e49481400c000100c2c0d9400340c90482540c00500058250300c41044e19503074100300e0301480012900b00f0089081441c40002ca003641d074041e51000d0020440d050192803440890a46a50640d03881ca69007040001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 375986780 1250 375985530 375985553
    0x6170c010323010e0414030315010e030102090a09020417060f07050f0d15030c0f23010c02101d090403020c0f0307080a0605160e1c02190305030c06180a11060403 71
    0x82c07074445030134103007481e08000c3d510b25003507118224994800c1061224006a19901b00f500c0142442d110001f009070b4008030303000e401520700b8903030048005103022401c540d13181c01920585001c40d64280c400c0c0e1024070215601c0009464034004164410042548240700ea0010100c6d00241040146040c1590042e50101c681400c81c205034102c004800303104012086980038001c19604001000b81e0f41810b140d0800300511402000d23408100489962450340a02121001380e40c005011440b19490070038041c1c29699480c0021028451601e020f0849141103114140280c1d05680103109095440040c400c1c48802c910449906105000c00000d0404007041030308200fa1080a0100d0365007080b000540c0c041705560510020f00c0314000c228207a40c0c80d1088003144200d1520f000500019140c0041440340d1075801c038000003003030200e00c08024014008020301600034024100c6030242d4031b030100915000000c03880c1ca0b04c1038004a08001c0440c140c01d04c2c2510485005024500c0c00e642da54640c0c80300380 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 375988030 1250 375986780 375986789
    0x150e060307260c0316030515061e0c030d0606050a08131112030a09050307060c03140d05040807150b0f0402090a080d030e0609070e04060f0216030e0406170c01032301 73
    0x3c0c800010000709405000e9105c001740c3c0c150030188111304205e0701200350030324010b4421b4007a0300040384400c18a41e00902c40200b000c403000d121a9124071201c903545d01d039400088613030002800c0c0500000c045114408a901080040d501c030b0740503466600c880940c0e000d01c854183d4034080624000300b119a0389540c1d00302e4030441c090003141c1d1108214000703055081e0320303880300f0f105c0e411204040040c03d4000003014003c031350524140384100c3d4090211030541c0503600c821241107107000208030400510400800c0454001d04402d9492900c80e41580d094070901d0a94941040507601c041c2e0f11420250040d2100550052646548686034010517241202d030341c01c04000079807207140c452001001400743c1c0f5000344540f4007031f011050a1418140c0050006400240350030354031408002c2e500060f034162484010781c80e90581c0703494020b0400602d004402c0903150320507031030403100241c0c4032000d600248103031104502900f50b40c114a00150001e01c48580d000c035034400c4c0d6200d0f042d514a11650118040c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 375989280 1250 375988030 375988051
    0xe01090509011d0606011803080d020906160503070b0a0b0f0f011b08040906060c0b0601051605060709060306060c0317090a020a231c06090c050301090c150e06030726 73
    0x41c45e244000420705100c1c442841e60280d0219414000300e15a1070844040600c0c0b03250241c1d840c81c07160041a528401e50841c1d00d0f400485040d01c1c0204a00440200051401346442d15140e894803003c1038111031201e2603042d44030400421110403801c0080c404500b4181c14107101c0c0450b440d440921042c1c02d0303140c90855242c140081c0034041c003080c40c45004c4c0030348060f1600030310b401a02e41d1003003040b078405850b4a0500c400411910490301d1240010f500e0b0036400016280182459800900020064055480400e09150300840c4485c4038040405d03010ba01030780c0d195100d5480f070800900c2500301034003400c1d60707005104070f24003d80c03100005030000b03000000e035001d1410041000b01c2c403151030352004d49200c2c1400d00b20b880d83d083c01c0e0408250f0b0340f5400200000d0306151520f4030f5410410241d20064155003040805024014110070700021901070b82c0c121103100d0b150720b204841455030039001c5584000c1c14808200c065100f2420a404600284003400440c11614107000b4071490445140c14807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 375990530 1250 375989280 375989293
    0x180a0e071404060819061503060603120f110a17090307060504030b10030c0905070c051b0f10050712020f031204030314091c020c041418070e01090509011d 68
    0x282003c0c03107074900a01104016011404900620000c840d10506004d000d10340c4a40328800109090321a000040d0f9120f20200301c8642d5034a48400b4200c051008000400c0c3c1d1840080d1856009000000e004038624000d80521a90350f950101008602c0f2070030b02c0710700020b0080e07c1154070200300b03070b00c050411519640c1e1506d14602d020308103200000d04845620041d500e003040007c45421400041d2000c0040205041d6036102040740c00c885043c501800c284507401860506084945001d111480f081d80c1401c1307110108028814825808120140081c008100000228040b041c0e203814011240c41900c1c0f281100e21821403864002c0e004401c5116564014441010340511031054000c40142140b860380c600703c04000d0300c8032440340c03561844440c01c0c0f0000e00002c0c800e003d07041d01d40300c00070300410011034440700040c00448111815401c50060045e540040d030300c0000c4580403101e07079000e00d074160381c00d002c03906000d0301026000450642d00c2d5000e41156618851034460b1215164000b40750 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 375991780 1250 375990530 375990569
    0x421121d12130e040b090f010b01081303020a0b01140a0501020105150f010903050a050d0908060402010f030f150909120c050604030f0507060e06070f031103040209180703240209180a0e07 82
    0x90200b00140c0547c030f03a1400e1040c144a036007200005500a0944000a00411103030074141d04103201c50b2070040042300c0450001c0340074030040700c4143c224038056500701c600b41d80360401079080301c0d4140c80c02400480c152940041070b14050200740c40e90703c818900350814031790300d036515440c010409004480941015100140c100d81c01355001004007814070092813141002d0b000a44440603603002030301015290500c00081e440640c110008906441045c0c030341e032a070361764001c130000c01104808031400e01c4803105c021501841480744040d0150047c0c05468a911a90b40c140c3d02c01c2c60b2241d0031000d100c014005500030800502c2001c450516032409054240380c80c02c0000c054002840e250301c01e040c0740058160390740d44540f0a176079100b5030546d40304c40b03541c07a40c1d42d001120340000301c1c031002c0903c80c90b42e0200810a549065007003a4800c000300381c4da0584000803800036401a010704a1700300c504c02911000c01c0503407610041c2c0000380e0110010b084040448110304295958010b020309000d0020f0820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 375993030 1250 375991780 375991783
    0x19080712030e15220b07060204050a0602030a080a020c01201317100e030405120a0c0504060b0a0c110907020d020f03030c120421121d12130e040b09 65
    0x20115800c0352191600100b00441020074000c40c01c0315540d8003050041340382103082964110001d0585680516290002c42c40c0240196025000e500c2c0903102503d00024007a0000060303c4007040030391500103240da43c50040100940004d00c244105640310390280c001244a91701c61200e19031080006607540c02d420710ba00400581c0c55202c19002c00b0000c410502600d80422021411040c401022421540d0801c54500d50300468000591242c02c02024100c40b120010b05022924441c0d0124202c041d6120304100495031244501010360004000b045407032880395109400c1305100e6406004d00841c2d4101107480080704031041c20140e448803446081194041000c060b1501102c00190300d9803808501c0a00303180108503507000000500f8020404001d5218a610311041070801409100b07003007080c009000c4003071000326180c01c0d482c0001c01c50b40315200291004a100303200f0b00902c0582061f59103611140d115002a007660b803039001d00402c0c902c900b03151740f070300542c05100b1009803400e2011003c2d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 375994280 1250 375993030 375993047
    0x90a021902120f0c0a020303030108010e060f04050d030b0d060501030606090b0303090a050d0201051b1506030c10050307110105010b0c1225061d010507030b06120103021908071203 79
    0x2409642c010100d40d84007503100b0080b02d580b018071000c45070700c9100d002c070002e191030880034001354540008000811101c00541c4215010a00d01d800c564682d101c200a0314031005003a1805807568210003513203c11207010350044100244054080c40008281c1e4072000e00310ba0302038000729042c540351107040000d408070740501c400306031080340594501401240018100202449094007074a110b0000e81d040d0380c0124190b0300d0000b12890007440c018402c065094945000c0180a0605030741e800c0465014200014001c1c901040a40021000c2d00e15100688007904028414010001c0d140704403000c880003801001d000f080030822894031100e089107051308111030400386065452040c01040c8600c80d13903001c0c40310600d02041200d6500501d40c18403c0140c408a180b0300340030365030030b9101e40b0307090b00552027240b003805940e40402c010000781d01000360b14450030808035441c54800c0b0040c809441c1ca100d258034401d900f2900745410031341e149040c50521580da400034214000401020b000e064100880707 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 375995530 1250 375994280 375994327
    0xd09090b01090909020109080a03020c1011030d0f020904061205060612031801050f0301080607090602160501121b080f061c0b04020a08011803090e280902090a02 71
    0x5110503032850000070700e8640203200c1d00800b40d13250b49620f000e59000d0913070000500340310401c1c3e6012805505000e561003691000c043d0040d180c410384244803902c9810348400758442003025510345100340741045c0c00b403c00124801c0c3c503680c1c00c20507219182d13a14841e100060095107559103000326542407460401100a245038002c080303584c10640c09000110880316002e84541c0c030048001111320040b6098003034a4101c466402000001095820780058500c0c4160300c559a8aa0403d80780c4030f0890300d0380b80742c0b85076403030b084202c810a000640c022071500380f00904046000414104104152a14550030040100447c00c0107007440611b034240809103034804000c0d185021b9880c403c00d1244411440004041d10160485001c5003c41d5903010707802000b810208000c0c8030000209a0f8080110000c4801301c01140301d0385000500314045a1280341324203038011050380c0100c4ca031140c0202d0b0600d42043e00310025a1111340384010303600d00c50040e00401c070300d000040c0c4580301d0340304d041c6444004c0c0c1e40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 375996780 1250 375995530 375995549
    0x718050a050108070506070309030f150c210b060d0204030c060912080403080919091b0c050a1707050609100c08060310230c0a0206070f02070605031e0403020d09 71
    0x18442c4500c009210380032a172098804664501403410201c44400742a00f00512017149840c02c002403000e00c01052003141d0f5201000c00c50780400308001e403480d0107d000c140c0ca0500400c48001ca1252503644040341c6888050200b6240041c0c4036000e80c00ca920036041122070304010401440380a80c0b001280020381210350824600140c0c58840c4196402544801050211b00250103c65a101c248065010301c50110b168425180c1b10040700d070140050081c00760300014002d4110044601c981082030250750440c0140607051091784803040c101d18003c4400ca0000c50400c52800010700c20800c051054000320701524121201c00c1214081d1031440d1809007c101b140801c3c40019940403403000040b49001800252150070800c40b04e43c1114002500981c5a502101b001a90340314000100003101c4540d0940e0590b50301d000083c0c80d1401c80c091000c0060380210303010b000302c5021b200110f4000e000c4c81c1407086400c8400540248145040b5030403801070300009803078210542c014600401411400380c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 375998030 1250 375996780 375996791
    0x50106080c0f0307050c01020d06030201020c0a0b040b030a0216051b010503280b0d0f0c0905012301020106211a01050f131401060504080c040b090a0510080718050a 72
    0xd0703503080e004840c0c0b5025006400008a80864082c20803074052071074400c000e41d103a9581108080081216110580c00b50050012400d070503c0c04007030361004e43e500d001c44541040d041c4610925281c1005147d083d489508014062040550160310300e2600c0c480d0700240601c0100404030017081d00207901483c18091305000b0f102c888880030240603280c07441c002614040041120018020b0000b039550030b5005005081c0b08000d1120860001d50164061207070b8404640d43d07408501d0071514244030f80d2103031b40300f81c0c4c0041c40380d002210104c00d00400148000700e280c03922414000c0704c0c00310308840c3e108003165624400e810000504c040e54035403100c22003088015072611000c90f01015941c440503115485c0100844284e00030f55006484c0c03d54240c00a815540e100c00000d40700303a001e03004122941c0702c4c0c1c507840781007894680180d22960728050481e0b500e17503c2e181d0f00e1202408020701400d042012400300801c0c040402c210000007000c0b003140d40c1c40c2d03103144000780d00c0172141c0181075215513a0500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 375999280 1250 375998030 375998041
    0x3160206060d020906030a080a030e24040f060f0c09050f190506130b0309030403170c030a030b04021b060601090f14010c1505010b1305010203130e1003050f010f05010608 75
    0x45400001d0781d50140c03070351341050f80e034140042d003020205480180032110110340e5003122585540103102c1c461038a01100d81501040c0401c008503520740a10b031413400c5500b00007500087d50a981030140030322458000c24032881a0041c001a151601c2a18000030b045000402c190325000d2180c0d0710ad88825100041d0b1015060000c50191226000e2503014140000e4100030b02d400c1406544010240806039544071f007171a03688103071258031611080c4d0f100780ca85c0d15462955180081180c1e8102d05503001580340c1035681c80300303174094070a0400350340e48a40e007403289801800010f05044d40a0840754007a090310318000c0005450810280c00c106010b000c0c545043c444801c08250340c2c03859000900b0000600009891f101c2100300031900380b00c4040b03003018000501040f60001504070f4000f051000c4c0e45d0701e43c0311401207981740140f800c445c411540c06182005003081c2c6911560300b0161031589841901e4a135150a80b03003078240210505281e40d130742c8030354403140300c0b61040b81d0240185140c201c4882c10726 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 376000530 1250 375999280 375999289
    0x2040513170a020c0303070f03020c10121109090a050f1305060609061c0503040303090b0f0307030c0201020c03070f141c050a030902090a14010b0405060d090501060512030316020606 80
    0x4040c0041c500040c85101180200041c00c086280101100d990350960326181c1b85801d07070070b04201c1c09841410780c0d62069140035001030f4122074203952140780130001049424007030048000140b80ba8441005403224541350f49008900c5080d20700c0e400314003810411081080700e440203018245000304080910001040814203036000041140d8a003090f4849100180310340650745542400e22035184c1820b0300300000440a40100d80c000c1e240c5542c00340c2d80c0c800000581c403c044031540d60741310410001c1c42041c0241e01000c0315851603c00181000f80040d103d03441d40c0d200410941c5c984550b2503c840c02c2140d00351400100440e003001030407070030704105407011000c401d010000c0309003c004101c000e9454840e511002d003041c2c00826034542420315584400040034000148890005090000f0501c071030100212022140040d110610702162494180000c0807900c80c02c813840c0d501d8500c00102640c58214402c003400e0058081c45e80c07401c1c0b44124034000f038181d030b4030003041d034006d08100001c2d942ca = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 376001780 1250 376000530 376000553
    0x62106080327040203070233070c0c150c0c0807270b06070b04060506010c080f0a020102040e0103030e1008070905060c030d09080307020c03070305061812041202040513 74
    0x2d80c0c00c241c84a152a04840d600d20020300e62105411510200030801e089038000340c8804841400c01d40704004079041c4001c000e4480c95502c0002000885001140619101c2d9100c1c1203c00d008010203500240c64181481440c0304040f05900010712800703200d002e014503204890000e0449000801c0002c2c41c0c40c1b060210303846c0e01080081c2124103c80e2454402c010f94011143c8417000810541d91204507141c0300741904800d40d4140c03805d61400300024440d50007481e50f080c1064011490f03034144001280892007950280c04480e0440d5024007000074132813044041c6074041c611036115285808c0801042c0503a2001812001040080802c2480142d50f00810b02c90160351055546d90360fa48130440c40c1914510a10403c9001300d031400000030240042c0c400918021207059098800b611190f40c20160f42d2100f034000070345250007620108440b420702d0740f40b600c00003602a054a5200d00400e8205801e500160701103a900403105010800310300d014851a40d00501050031420014070300d03201ca8a13001c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 376003030 1250 376001780 376001797
    0x28110111030706060915170a082505060a0e0312160905100306080c030a03021e15010315060f0303021509280204060603053903010621060803 62
    0x90300140311000380051040ba000e250300680203121055903001c82c5030007400d0600071040503c58080c40400d8030403118100b01000785c030102c0146440011901e890155510a00c0901034418480303004040505120610200640c000d20241006107010159202600c000981c000419001004100708200340d000201d60031800d0701c050306458140d03032001500d0200140d0486940b25016190b4285002d91540061056803039981c1034500c00c0110005140c1d84012000004000d40c0000c24640d0403551182d6100b6101c03108038080320f58000350b100c0d07641742c525400e8105644c01075540350445200744403805182e0044c4030080a0184107071a5440007501d4003440c0b100d00311607138140701c00700d0020402000105850b441310740744a0607040c030b8164014860b0014550403401a410145c000400500034420705100d0070144466420345180001c820612220903006080d59280c0e03070704140b030341259060107140a811143c483c0008254100c0c01280c680700c800551509081c1007c10601038000080280c03038140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 376004280 1250 376003030 376003037
    0x4030f0f03031401140307050907140919080303040303060f0e1807081b040f0c0512090109060c0c060e0723040608030a0903120e0a2102090702281101 66
    0x1440a0301d03040300509074440d000760048800301c0c00070551000c40c00d80d0000c2d0090031000c0b5206079a41c1d6080c01122078045a00c240421180340003015420078202c010050304200a1200428038444e851548207103031180c1004489078408410001056014461b400c0a001320769038003c88107103400c0c45a0241c0b0002400c01d1510900b100c2807c840300010002d5038050710461096031030007404450f09a40e9000d0108401d445141031403d0035202d000070384915001c00c41160340b06854240704400901064102828520541d9079881e01800410528401c80200303502c0c4d6505d8890400180c1480001e940d0380c4180910300c4d802c580000c10034102d48e285c181d40000720841c1640d506802210025005200f41d900040b0b550000250266809038070110310b4060320300c02d000a89005100110450324480c2d0180b209801031031000040c0441d01d03414548030f03c01030040042c40c260116550204410440583c2d009016034415a44100b0302d00a02e0115040034400c8160a100098a91106c2020065805803a03060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 376005530 1250 376004280 376004303
    0x21b1c031d01050702061b040b03060d050f03070807060605062b060f0810051602071a211518240a1509060507050d0828021b0304030f 59
    0x107104400007641d5203441003002040f043c0303070041000e0f484100c11110001803003985841090752212000554007030b620031110715400d542c1c03400f00340541e842424100f55000e00c12206001c901d07400030001818018490b01400380c49008518210007941d070142c0146100381c20900101a00060344400d541c0201e07c00c1d00341d00407900850030204001c0115821080100307415000201c0e8500c40000c044080235143d030b400f0015551007440c84550550030002000c0160403600d010050081c04d248801201c1544000291611140b803840c65100708004040c4e448030080d680c10082e0514024100801071081a6000c1c5c0422508540344140040c0007460f0807544d502c80c0d668410200c0d00405920b1113601d001e080ca00c103c5071540010640d40c588a400702e000aa0b075904041402841801a140c3c050b0f48440144100116200180e40000d00100b510080b800c1203070b600200c1c055984084071a0603800302c00103981d4000c83d0b110f03450300c021030380c065407199004000c10000a01240c5408504581240143c0603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 376006780 1250 376005530 376005551
    0x504050f0609041115070b0a060302090109020d06091e14072705271e04150b060d15170d0f03020d05040b010e07230c0106030204090501021b1c03 64
    0x204c07000060300390b54014140f85400d5090070300e86402098070b0b501998140f442c994461000806030381290100a4200c60f8004c0100b10700e0711180c028184444482c1c0d40802d403d40c0f60701c2e0392821101601654184188058030034000c80c00d1070310980b000d07030b914007070000d10700d203025800501002103502c0b038038400c0034403d503c010151f0300b01e11094014000003094280d4954010707031115004820740c0408001601140e010955078000c11205458003200140802c01960f500d403988441c0361a028200c62410340c9504e00c14080d13035203040c014105c0700090980001da800901d44006880611074200c01030b6145014040c202e02203000400c0030304089145009407440b00c150358114068000c598400d808181040207000030081c410b40b541c0d0503103000e00304000c243e58440d10100c07400319816204083c00100030080c80e1105070104010f02840306081d0006c20b1856036507001c01c2c111402c1080503140c036540420350700340070340b04141410501010744004001e5401003401044403040060003280600d43e0b20a110788 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 376008030 1250 376006780 376006793
    0xa0f061a0f010c0204060f0909140a020d0618020316090e070b04090203040816050102090f0103090b01030201140c0f0c0f0d080904020d09060c1d03010212041101030908030109150504050f060904 85
    0x1409040c0030038035461f181d6950b203400d501802d082c800844109000107004031100100044242c941034008050401020680d2035510040400c1224004d040b4154160040581c5003001601065094030355403840c1289490b0142e030031111101e5040340d1a0300101c604204003d82402910103952092200581d03986903490142d40790300c101800110400d255003240c106002040d03014014400f0280c8160703c0035274540004404443c8168001441c04030540014400755108006c52404151440c11a5150208518009142c0352000f83d8400b0154849180c100341c83c108041240281d0000b60b40d00000220255911040d50003115480d6004580c04100e4a2044400360000b090f40ca03004001041441505000204000c0280302c551607290754070070041581e410148225040d48040703e002c0340f07060b11590790b414692501091308904050702c07403072080b000c42e2202c0e00460003031400b030038005035644540118003101c4031540e01c000c0c450b510b4013041000d03221b54500c00641c0504201d80c48050b5a44034503245 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 376009280 1250 376008030 376008041
    0x705030d050f03092b170c1e1b100b0f031f061701050a06060e0a0e0603012a08060a06140309071e06091a041206020c0a0f061a0f010c0204 61
    0x105d0a03014102c40303030610702c1c82041102000c02019682c01e20510b01120302c0d1118a50f060b50203a804000400120b90070302c40e030032000c41081c0d944110803442e01c3c5004440d540409862607031403000307400038401e05240023031512501c2c0c0c8143d010340341c050034003c5030000281c854000340c4128005402800e142d021004035640020050158409003250003100c0a002c00d000340000c03905401c005251410100d8604d0044031040c80c3c02d48001c00703002210b400c0c20029600c2c050090403150b0550341354a2000819079039041b5805c00055241c20245c2c1c0490b48190040803082e014000c540075044004080c4120355000e0311000d540c5d07828001003076407030310307180c050501d056407a80c46407080b6584e01041c15034020174190080100c1e001070780c88460311600d0380c004441c0550100d0b000b208a403010003003000341070382c0c4807645c0c40c209005080c0103061031700c3d04d14124107164078110b00300c1794070381c0700c0180904001141c441c0381044200003503070303045554101c800714200c05890031015052042c0341000300d0131035840381c00c0b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 376010530 1250 376009280 376009303
    0xa050d090b10080c0409210903020a1403060714070f03170708090f12180d08070b060111060424060306020d0204030611030907052b050a050705030d050f0309 69
    0xc03401d145407041c000940329039180101c1da044d014044c0425a50300c2d180c002c0b0300302941c100300c8040c84040c64032200c03200f0305580c010b52818804a41070010142e41d54400c501d0003450015046c1914045141c10141410303c010801002d00c0001c603040c002a8400200340e49000344d0107285078174505080c1c02c2c240c030b4140c0010341820800c4c50440802815a9004030180e014111a8003220200342c519910282c45000020354000d0300041031000720607801c0d0f0703000303c4000714a018200344550040c0d5150904a030b8410380041c0c80391803014045c40700c15648848040c1855944001414460401c1d903a2000d4040100c100074000f200ca204107506420030315400900250383c13004085603601404ca0503c4081e41082c0300644007545040740200e92100400c0803030b03110310001030103401a030342064100300700c4200d09240801e40180e0b5044c0210551103002860b82101c0c00b800003484428942e07c0d0040c907042285d080301c0e0203500940710040b5030b10b4008060340c103588459242c0c96200e81c0c4c4c18040750700d042c0c3e11000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 376011780 1250 376010530 376010543
    0x602130503160e011203050d0b120a060b0f06071e0203010b040c020c0a050303030717090106030c0b09150f070f1a01061e02150117070f170f120a050d09 67
    0x2c0c071600403030101c03a52000700e074002001c040081c0e0380d404050300d0805803002e020b800705000f001a2904001103600c0304da401103000340300300300c980700394038000e0703c3c000c441d420464445984071000c407070b01e2504050b42048088202c0da150310f0400d0311782d0f54440c008507102c504c2e28244071002d0400110b50b402e400080c0202d2020f041040614003d0100940d60f6075800c51081c01904410004100350801104591007141683c54080d010f0b16050308030804002c0040c200c0030070b550b0300e490200000e0b0365501070000030418016020784070f03202035003000211900c2002d0000c101004010003219403800130309841c215500403107880e0601c0964105000003011250516126034104000441d0854010644500c1d0059080403c0f11444501d1001c2e40d07109440104140d000445800400440d01022500002207541c2c405590311140d45410040821143d9085030545070101d000340408641e040101d5400c220090707000b04402d5a01051601403446800c000804000000a08450020264008440840c9e0004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 376013030 1250 376011780 376011793
    0x6070501060b03090a1103010203040b060904030509031b040f0b09070e01030204050301051611010e0615060d05090303092802010e031203070e040b0906220e030d0b18130602130503 79
    0x51050311640310000807181211406d819081c182814400d4a1080d41d2040e903041880c0c690038100600000001d104400b001010015001c80d614180700c50380c0c0315042d0b841c04101c07402403001000155040d0141c0000410301e45495956075039643c03128590440c1c40382c10b0070203408816a0040f4003a10a0b5004583c2541c00e08080c000107000200c9141800c00d45503940b0711540e801202c6003800e89416003004030a0b0743c0100e0110740c071498921066a4050070007040303030b0b1030050005003180585d942100c000c0d1143d00027008210502d41d00f40500c0218284104214444000600411903028504503002e070400c448044048402c1c5c8013000051400300c550450300342c603803070305801c000c020724001031660340282e007400d4a501c1e9034240040c2a60113581c0c004c0c0341040c2e11245108000801c090115150002e076201d01c100030542c2020310003000b0380f001955011079921411010300405680d1800c40d080411003240c100500c00c40c001450391061640700e500035a80c2c03410003422500c080c2d410740019508d4054003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 376014280 1250 376013030 376013041
    0x40308070b0402030c01050c070e1305010c080609100f0902090604170a021903030203090907020c0a081509070b0a0c0213050a0e01060602010c12021e0a0206240f06070501060b03 78
    0x41ca401c078800c0d0700c00c500721400c0f0914080111258000c070580003205e58450102800000c6607005490351000400024008540c51602c580f802c0d121183c07030407000710700c00c3c5d001d010450401c030001c250f015600c0700410310414a04401c2070b515011b140318052843d1750100740b8040c5503449100319001081003100c040c0002c9442c404154a4402490b0701700d1080203100303400104038a0005072101200c3c0c0540186041060304402c3c04040d0100620306000c5001d99003401c12035036504c00b20040501b040d40024461071318120b0140814100103003015856500003481045411110780c120b03075800000b4070f030040150b0024400714841c1c0b9150394000100900b4401001141c1509074851a032117504a00240710032591182c0c241d0803960b803c42d5210000307900756410281c500f1150010b20b6409980304101d4408401e1070710012035508403200620060300301c1c8050102403c0350302c0c001c95582c010560f019080b502c4a100080c900002402c1d05030080e40c01040c0e00d024030200b903005100a00c9004c49180e174a1404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 376015530 1250 376014280 376014293
    0xa140702100f020c1e0603040c1809020102060a0203012105070812180906030c040e030d020403030509120106050a030b04050f070b13060804080906070c031b0e06090f190204030807 79
    0x350242e01005105445140050345031503001108103211214880b1800400d0005002d0682d100070800d03206855079400c0000c45441107001c6002c003c0b50f0304c600040c14542480020b003820005040d030f204407401800140030034041840101c0910100d1134580c11010805d00d049802e01c8442c2d03006030224043c60800035450015100100f0036000b16840d001000d880c140c080180201040e50450307050752103500b64243c0b0f402c3c2035101641c0b0205403400c070b81c203000500c5000c8059034001c2d0011000101c3c04512480c86082001001500030100310081c04410b00305400b18419500511018040f18111300200c3e082c0081440041705915509080d5500d0540702c0744003201c90ba00c01d02c60010441e01d49900061654410415940039a0b03102c5c130060314001600c0308000503900100d00507191812603401c0000015814581502c1a1003031407070780ca0a941c503200c0000c0c13403280c00074841c030700911004003004406ca2054420791b52082c602c10f5030120446d24024802d00074040c80e00003d10070a000505541031008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 376016780 1250 376015530 376015547
    0x1104141306060f2d05030a0b04050c0d050c03010303120b010e280b0906030105060906040e1018020a050a081b0a1722030309020609060d0e01200a14070210 68
    0x1903d806440c04441d86031081100c9004884ca160041c8034000c02c411180704000543d000901010302140e0492110009411a0401d9420302d440f180002044212158140074155101c281209110f007076601d1510040c10107200d001c0c3c0307090310350303a5000c96040036809091300109081018213641e082d141c0d0301c0100f906400c1c2500c420440c0b6041c540c80080c0350041074040722042c180180400381140d10706814800c1a03001070303d4840d8000707424440403d109041603c0d01b80f060f0141c55801500f5843c044204807840801d0007290b9180f8010007034015110f40040403510b091005103081d4076195200240b510041040d81030329541003900013150380c03030302d80d00100d143c00046104205160a032a21030500803842e9090795020b01108000d0000808030340250b100000301130024240714640440c0c1000103501e588210002d000460303450214811940e400d2040910090580581c46170213100356140c5083c0e401a01d0152042010700714940400c196400184c4010941c0900748211041d10b016000e8143e64 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 376018030 1250 376016780 376016807
    0x3030c0b0c04140105030621070603110403020904020105090312030a0c0e190b1308100f0c03050c040504090303060b0a020105091203040c030b180a030503060a09110414130606 77
    0xe084086160391590300c003140c08882000341d50b80d034103201c10001941d40e50002442c45034006100800c840b040e6200c44003840c19403840001038102981080f03405821685e1110b101844041c0901c400d0005882c0d1080d600e8101d1740900304980c64000070000649403035600c02444503d032001105100340344010717400c04407955145444884c1e4841944051140c4000ca0b00720840c2e0b4070b040d100c8204500080c2e400148000000da000118915450319012403420303144400c0d0289081e541d00d116210611140300311220414503150522803801c000d501e07940540520b01800f841a0b42d2401e0000c1054003ea20240042c16060920781c1c6800d89403402900030071084900100f240103180390b10b40c600303801c04d0803207204550004000c1c0f4240c1c155110740d20802001480a00709a458510200c180300b400c202c42c1c041c140c443d41e02d81c0c5d62441c2100034410182103d5008911007410540d9040203049407000b41c400f40c0300b03051400b03483d0744844070010b01001d0440d00b034010010b15146001c80e01c190b01540000100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 376019280 1250 376018030 376018043
    0x1150f0b030c03070e0627040501090b09070e06070b010e040b0c041212110625020a020d060209030307200406120308040303050921040801050604021603081f03030c 72
    0x16035660210324080c8000c88100148500400025003158040d1406034004080030340b01508100d12080220303110156103009000d080169401000d180c03038a406200d000d00581401030003815580310119000810180c00c50040c405108a4440203480f100d003031320fa050b908403407244100d50b5104803280c0140c1c02030300c4c10b94050302c42c40d0000c4c80c04100d44003218121222003409003140000d0342c58a00c2200504102c4108000140c0c598041200c8100507035402454401c103950b02c45810003042e103140060254186007550404090301026a441c043c200b0319003a040304000d81e030f41d02204000307421845043c46c024000d07030100b200001580f81d04200c0040c0903a01340c0c0c04000d8191a2100924003100d005801000241c1c1f00700041d001034440d801098001242504231980d9404080280b071840b00d04094841c00c03103074081400c0003002c0e001d00030f5941104c020396003140360401200207584840c9178920042e0520580001260607a030301c20b0301c2901040d8400650a07265a2a840c005000402518003502d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 376020530 1250 376019280 376019309
    0x120c030506100f090e1b0703030e010f200c010209100f020f030304080708070c0803030c070c1d390711010e0a05120307060504030e12120f090f030115 66
    0x10940900d00c210003075600e50300e620b01a286040b040386010107009021100e40d014440c51000a0b51079032002c0c000303080c0b080d1000b04042b1120342c01c0c1d40c2114142403d409a02d8204800051170004080c030661034450031000c62603446060604041c064801d00c048150000000c030f07120004075a015101c52030a0b10990309840206060420051352400306940180c40403804110401c00103010030010421244541e1030081102d41c2d4100b5a403c6400c1114116030300a8005801c4040148054181c806004100d08181e200d244804c0030642b5000700420079204000810303200f2481c151000801103000c0340701110b42a00219219a10300070f6040400f003205e00030640d00340c1c011150701502e904c076410398010b088000010701d860b00b0400300909040044016000c100301d204042460750040d188254040c0e11a140c6061261003846070f6200c0d1140501e00e2a0044d410499000382a00e003222545c07000e0380b0709680c550042e400091203e50002c0b29095042d072070100d100728001c000014942c101c44134030505032074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 376021780 1250 376020530 376020559
    0x509100e0d0b0108100507050301050402180a09270506040f020a0308030702070303030c031e15030f050102131a04050d030912240603051203331c051c120c030506 71
    0x19200141e590b1f81c0440c00070f200521203424036a0140140308511101e091405c401000030030001c44090700038040d0346031a80400f058542030050030030f0a48c1001841c0f84258400c0d0b403519515540b02620041100c4248a605400d560b02e106000d006180c1004400d40d8074244010041c5d503424080c48200c000c03a0030101504040c0d4042d10420091111080c0d211000a40f250400d80042896225882e400d10700280e0120215107041c10201006100350700050b81d41248155415840e405980044180070043d0552403054034040265422a54140c1d100d032140b1841d03180658503a021a0808004004454090b40034070081c0c401d01001120361480500403184100c0781042502c0c01e0f4000034007990302a05c001180c0c62913100080d44e100c0003000c000410f420710800c010810013410901126580301c2402010424a048a625050540c010340740c040814556910075840d07810002000b500041009864401176000b540c01e003c0c00e50380e5000802004d115140087d005002c1904c0f10740c02913030f00205040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 376023030 1250 376021780 376021813
    0xb0105010305040b040339060e070f03060c030207080d0c14090604060503250908010f0b0d02091f0807031b0305070e0c0d11030f060301060302010509100e0d0b0108 72
    0x140140e400c01c0714014140d840341c40a951030440d07c0012110340134481400d22209522512203107102c6900f01d0360355240705080c1001400d82c1d030000140440c5412a030810404503c1400c4071504030381c0d01c180081041700202c1c0043c0c0080c002e060002d070174008006201c080c0003455500c4130868401f25200da01d00010203404007011030155205040c0c00c42030411045c000d0030b01400240d64020325a000401c40c042c200e4a0100072100c210900d20b0109506003810301165001b80501c4505004078030042050445090000c1e095240600c0d002e400307004500c0109820420500c51200c412040704852003043e951600741c2c03a5502d203288410b0f110711090300c0440090000f481d41c6602240c0e0004011301040341880d6460501c940054200701044c1c3c0f0030401c109206c8140e01943d00c2201c1d80408042e00ca20f4004086050010010305c2c5a10a0349041400c0c00140c2c0c0090545003040000d5030b40c11034410f0380001c182d0350151809103880d030090008007164108000c820089060300c0c032070420703152074441c10707071640 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 376024280 1250 376023030 376023041
    0x90303021210081e1c03020c0d0203070f02061809010803030601020d0203030c0406030c0210060b180103093306300f030f0c1a010312020316020f030309090903070b01050103 76
    0x603445030403004c08420740410402650565080400584102c031410070302800c03507040c550041e8404030340c01051800b0301c540d0038403402c1120701d80c90014615107800c3d0340d15503902a040350f8000b481020041820a00c0c0102c4440206035070101400a42c450b50311040105c0c0ea0fa082101c540c2d005114004220386c00364800700170341c0d0184008100c00c40c20241000002e601500458244800318400d02e038548801c401180940402046a540c03181e0740c468400b0107100c01d500700009400e06060410780182c00260f80d04e140203100382d4585000c84680e0010020245107400d40b11001010242410001b0032195104001c90014040c05a5400c240700b45103521025541c1e446180648201013500114010034001c43c0e1a1040c00c507589840d03250f848187c1d880c000c0c0a000d0743e1510010140140040c420044802401c6400c0011400114103044244c031a86920261400300280950310008074152507450410540e13800000040c1440d499150419041c1d980341c00c0500240c5804e040712000181c00e501038400c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 376025530 1250 376024280 376024289
    0x5010807051305070309020d0309030c0e07050d1d0f0102090405060d0213110d090f050606121209040f0204032009010e0f130611130b0301080a030c0f0204090303021210 74
    0x407040303501c2030080c040010702000703208000b4103491b080003030016503032403010300f510380e11940f2000d4100d421400d200d444513240c0c2d0461406100184140100c07103801206803601084001c2010401034985403c044c2c2001e100d5507101030700d1107140320f19202140107402070081020190760802c155550801049942c2506060107500710740c1c180846100d5402c160010a030070015401d500f80b41c502519031880480d4900901591030303c1d0840f0b51030301000801e1101d15000081200d00b80c2d0074802414419898100340140d100d22220300155505d0035456981040220349505070086494640e603080032081300001c01c03040fa20b858041c80a03210b56203020003200d416500004240c00d40c6a4941641007280e44000d403c003000c86c040500c11030300081950240013a0640c04040e82502c0b031802d0048122300a604d5001000ba0b080140018000e49200040740d0382c54517050f00d07001c0e80302d2485081042c01e812182d10044d4215003000102414142c243d00107142c48400401540155950a41c0401c582d8806004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 376026780 1250 376025530 376025539
    0x303010b0d1401050a17030915041d0603060a2004080c090106030c120b010e0a06201c05070311060a02070c05040b011215211b06080417090301020706060305010501080705 75
    0x5083c400c010846c04071380440c10328039003220300c0e014182000924084145402e500b402000140c28010388440007010f240040540800101600b0520b00190b11120010b1410381c601c1d541700d0440401c114425050401443c80c0307130242c0d5072075441d0314440e81c03650050307000c150069a1044c00090403074407901c03032062151510707500e070312401c0100040d003c041d0112002c41410440072010494030340c1da40c01165402400f5588032404907500e03083c000d50b0302c3c40c1001070350992500001c000000c2c00e06140d00b0001045100c1c98480d40e80d20075860151400102c4c100d4409103403050307100308406060300e40c0c01002c6540c002d2842586040e5035004000c240c440580070540000c0c00070003070150200854016880d0507880361001040030ba2a03441c080045201c0c0c0c54012181d600840505080c04000901c1031161404410704043d00e40c10041c01411111019100514402c000c5548004182e01041070b1200b07840c00800a560707030360b0281000d0001d445580401d07540c0f940303440d000040d43c41000903c001112000391 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 376028030 1250 376026780 376026799
    0x9030c01171f091409070f050a0e07110618100603030e0d02041d01020d0b0402090a120c0504140906010e011503090f0204111905071e03110303010b0d140105 69
    0x10b01600640709210050039458007080300104032009140141c03005000c000307124000c285000010146890401d0344119214100003405006a440e000340d180d0944403012103540031a20f9620003200c00e0000b100d42249903000700ca041c00341400d50000110302501b2310720100c4007841c18503000300341150301c44e10004011598500c0c1c42e02483c24214a078410041c0020300c00101d07159490130140078180b0300d80c00500940d41c00030740c0c1c80c3c01881e02e1145406d201005d460850070000c455000c281100c000c0d0050490340d05102c41180c0800c10441c4140c405070401030010f00020580000c0c092801e8400c1e41d4414441c0201000414590040d0401604982ca000f500640c14188201c090340200f180420076182424142550300260f20307203000e60401000341a80040d038030308c0c03905d0540900c00c01140801c400c004081101d02c01282ca100c0d600c85100400150414070f104881c41c2c26542c102c54000e02000d41c2c00301000028030074400002424540822000034440c03403000c10800900c19200b401402d07440203800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 376029280 1250 376028030 376028041
    0x31109010e0904050a0b1e1006050406080c0c0d0f020c0405040308061011011505011101020a020a0b1302090a0b010201060503011503060213091b1218060209010302040e090309030c0117 81
    0x2242c555402a0007a019100300700c90f9510f0780c001000c030407181021001c1d02c942c100800c1465000d43c8aa00142d005480340049081000c01410340c030852040204210005010440141c02c8400310b031080042802283c0e461036401a0141840c0c05541c1b800340540101440d14980341001e000d154440c42d45592054940ea03250010080200301702e054490030061126200e0401080c24410210342c000750a0010f020f031460700000500402d51452071142070f90050040350b803240c1c0c0010360b40044a5000e480e4a000e5a100c3c84040321a0307841c403002075800045801031100104082c0d21201d0f0021087c3d00a204450b12101890f00b41c0300e8110910f03003007501780d61040002c1201540034103240c0151a1091006070b0341c444107501a42d0f443c1890080030344182c0c0b0004402d580002c8081584d54007003009100025001c1c20007411070340e0800c1c1c0a4072451700000e00c1c8d8a680e119a0440d07028015000c0c4040702400c0200c429030350b9801200c012406403241c14065a21907018044003800c2c48500400342c030311907445 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 376030530 1250 376029280 376029289
    0x90405061602010207080412261c1407030b0f04092001030212010b04051003050702100f2903060912160609080f070302012403080310090516031109010e 67
    0x700581142107560a1124800142003040244010445501c000820582d00c0c280017502c01800141e038004038040d0508031101c40c4601041e201c0080429a000848888922400c406410881402ca1000f07401c078081040316a095800a94400020360781104003080000070712048540d00d200c003408402c807c00745418640e4116940d440c03444810315015003030401200c21500c0105080e0008000081c01190900041c00c00002c10505900c00c2d140074406828140b5010303407210309a500301c440040d180c0360600d4a00d80c65800500094024010070100c08402034a4850b5401c02440c005100340181804100407081c000b440c1f01040584449861400d004003e0402e41c40300e101030111f4040c0d03101c100990204500308040c140d103100002440e552802c0d00e280c0203085a4601c011903520b05e01c04030030340c4418081d100340c52050740d9104203e43d9498607000080c141c051869030202500a041c5000c0114003400000c00c0003800c40340707803414062400c2100005000e8043c9540140c0001e1020f0240440c0785003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 376031780 1250 376030530 376030561
    0x20310060f0c0b04021c14010b0105130b0705010e0607030f110909010611070806010b03041103060906010b07080903161802040518070c020d3221040b04090c0e09040506 74
    0x1300403c0b0326510b59025100d8682c0006c03815080e10126064044240400da083c00345140c443c00c00d1074440e1030480301c0c4440c22084010b5020310f0041c0000451281d0400009601140407400c0500c2160303440d107880750009015001c41c92184291a05003151000f06010342c0c1e090320200c03240240110354581c01c00b00c1c105c5080600d00030b259840e200b10003000854540074401d0074040d04112140c180c0d03138a05400c01d01543c006180c2c4850195115408001c40325001085480c1500c025174001d40c3c0d1103035182019002c078061000101d9040c05119580303d1030a522494200459981c0c22001946000308610501240101c0c0b103580d81001ca0820807014007240f4130011580101c1e2400e000100700f4031034020030211804010b045074000009294041d518200032098402107001e81c019045100044078010780315141540c503000c184c1520751030240542002c500390740c040e0055104540e22180e44010040c09002400b105a01094160108405c3c0b8203100014520540d00f02d8003c0c90346858250f9103c1401c0c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 376033030 1250 376031780 376031783
    0x120c030f0a0516080403111801050f03030904060e07091508010b0901030603050d0306090b040c053f1f150e130204030602180d030903060507170a020310060f0c0b04 72
    0x40000d43c02d0619051a00600c66000300b11007a00e541c1140750800b080390051f01040e101d10205a180101400c42e0a001415600291b80744100c0c5a034401c0824030358041d22034100e0b0b0207803c0450104880420000f010b00c14220f56035103062031230b030f50b1141d070304550340d04000e0038005500c800051140707000c0c01e0018092283d040c5000500300c0ea80e0b8a07203600b04125000b54078002900d4103004c03c00d0001e1809880ba186200710741c104408550a000603000b80704900402800211003034114420199038080303030150b10465200c454141842e4400e00141c0c00b8202c83c61502654020400b410003010300b807544040c2d0b61301e54598012640329550681c0d1403059002c8656008420b074855039031000f860300252005600c00c200260321345515251000f045010140700394014021005030030046a8400d0180d13040b0b9410402c009103d44612004981406c200c07503085205a54030001e000340496968010361151700c4a460b01c1291540310002212221003455060700051001000840170520301d416090b00076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 376034280 1250 376033030 376033037
    0xb04120909050a0f0b09070e0d020a030501050705131418180d090e0c130b0d06030b07090303080f09030d020a020102091002061014030304090209010c05150603120c030f0a 75
    0x31a515000c05041e90000c6840c4540c00d502c504100119030b8403030050100400c1d086982031103920b401d5000030a151000441c06201d03011070f801e00c1042d0348410b4504409940c000d8000d001e00d01c0c101d5401392240c0d2041691b04080d00703034071100180512005040c4e0351104030041c02400c4619500110902c0080040c04d08022044010b6030141407c5040042c0006441140c407903030f0329980741c001240300c0000020a46074144008010360b00e004005070541c001611504605c0030303102d50b60342c21150024612a0130003040c02d4030810038810340742c2e005084c2038122403003566411019558184c000c0d09002007a221180d039039009010000b09450350ba00501111100e03840018144140500060503640750410740b00e0241e0410002d0150003286105810090802d5a2400d501d050100002c00c2d0359120300e2058065581c0c0c08689212560f12450303103681825001401c039804444404c810001040c030654199100b4440c00d481025020140416a02c10080d034802030340c28140c50380003040042d849102000b040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 376035530 1250 376034280 376034297
    0x92702090c031e010e0610080105100c0314040609051f020c010302090409080301090f05090304060215041e05010b010905030c0f091512010516030b1c0c05060a0c1b030b0412 76
    0x2020400c010a0091421102405c03850822800b03004851030b1076120340d002c04c6214401800309840c0d560a010400020703241c6202980070506085a282812094a505403000050009501944070240c403094900c11240307624494140c283c4107880e6841100203501503000843d44900e190f000c0d43c040c0c50b9031080901301013081c000c2d541c1c4550103948240c01520340c80d42d40e108000080642c1744101a0700c08003020055140034101360300a9aa42100c3c03000300d905500810000d010001d0b049809845181949816030385079517545003003800703403103000701050015808072b0001907503290008810011040c060f041d070000f00219000d211806000620881b0100390361158480b003902d4006924030a4400040005190300b0302e00c01d850303c0c040e07902030804201804d08642880b580c1e190355841c00701c900000c40c4440074581038078002240d000c583c1d001c164031820101d50081184e030810302c0e400005105211601c4040c00812803400c81c075900b4003001e0a107402240010700020290032452812044a0130729014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 376036780 1250 376035530 376035571
    0xd030b090925180e010507020a03021c03020405041803030c0807120b06070506070503010303270b0a02010f0e01060e0c0c0601030b071106011403060711100f0603020a092702090c03 79
    0x1201e1403c0c0d200003034540e60f829240d030215800384182a080f496920141403d06881e40300255a200782c1c3c003e00500795408180403081a010764115030003014060824004100c000801c4071050b000c019099002c241482d1496101078403649119114859540b50980000440007006000740303c4680180c3d0019410040302000c0b500401415104000d95510b0035038941c10342ca0001e02d83c004148014070307404848003000072411548103261054031418544241c80304101c8500b2805024250041c1a11a01c0d0112003420701c00103400110580d9043e00010905440b0040314a1080c455076102469039007100d8014000107400700c0d52183c120301546040c1102900307a0940c2420040203a11205140750300c4c0d0f044a4050400f4461103502021a04084003e000e00c1c05586480d100f608610000d015503030b0000c2c690028a550000002c0c5d41c014080180c0503850b43c0da420000c00c09030300d20041c0314015016400c0e608811031410010903a001e4965140e54a41c204d4116458002810401d0080c0d2164141107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 376038030 1250 376036780 376036799
    0xa02011d061821041502030a0e0f18040b0121050705010302130b0c101b0f3204050f03280f0602070f0605062e02030f0301080d030b090925 61
    0x12143d0503840d00d6556140240c29282080e144100d0015900180401d0814076003101c1c000c000050261000160007500030000f94859050810b484104540d2005000030f20a40c0301c11281640c4204400807807100306c0000070411480c401c0c000a05541c4203070400d11980d44280c0140c003500700680b80c80d030040d54031f40b4026620b0b80c020980d038640b99403180b0024051008075000e0800c1500c0c0c4072249054101c02d0a00c01422244094440000c1c40396131000c52a94140c507003c41d400c000104600341c0746828030006060840c0e40980305040c407400001011845078a000314040441c4c9058040308519400305030002058441c610400350784000d0801a20030115180740010300b045c504c95000407100041c5464444200c540c0942128082d0b102c901304002007014000003e0075041e101402030312408140c0c1c1c0128030f140724041ca00211400040000548075070002140d8280242903103050003c0c0507490f0a02a0740d40c130444441000c4d50110803c03524211b010a154031500b0b11201c03810000940301c41c0142d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 376039280 1250 376038030 376038073
    0x712090807082b1e0b0d021203040803070303060305070f0b0a030c1b061431050102160b010f0801020f0a05130b190e09040f080a090e07050a02011d0618 67
    0x20140306442e0740b28071440904181d80040349181c401d1302000580760701400701d0101420540001c0c02200490070004c1030860070401da03001060b00c034080740d0751801c1d0b9103401009081d0500c0108d44611500c0008290081d00c0f641d080180c070303002c044a5080c8880811b04401411140d003d0700c082c42141c42d000130005c010685074400740b41c0143d40200314050740c5c5003d5004c6241c0202819100200881c4070350509d20020501000141d51907550f50800c040e40c00d01ba802842592001c8600d100c0c06401e0104224030640e5507812542d003038041001081c1d6a407422400c0c1d214002c4050100075040010b030200ba8003e04c040d1589101c8041134034401034549850b094298440c0c0a200601d032001600d4040199010540715944603040d5000303041410f00c2c3e902d00071410091f078401401000c0100d0340017021803003081d144008007090450400b242c140204050a541e000f0018007006508281841000ba2405c106441c0c03a462404028003040d515100c04441c40103a42d11600d0300c600a41c10040e80c54a03504042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 376040530 1250 376039280 376039357
    0x503070e030a0f05061b220f03120809030715091a04060b120c09130f050d0e01120c1d04020d0e060601030c0216120809031005071209080708 62
    0x100d2144180c0f5082080c0750a2000b07107a20103804070041d0401c52030318000305407444c3c9000b102c4200c038600752850404010401c5500215195405100004180a8000d20140d4000004d49401a50340c65a1a0702912803145020203460350418455140700303016283d200d600034034002c1009005400c00112070b03090b028419502614805e4603956450b40d01d1800869115002ea0910020480509a280400e6802400401201600c0b9042c3c0d0030760144000400d03a100c4e0780742e003d001d079110705084400c00f070703d0550300d80300c1640002c40c6160085c19040151094a441c5400f035251501464540e000303154400c1c98034a00710350442d4091200301400c50b00360081e0209040440c01521092403c1000101180c00c80350702c1d03500b154131412151041c4100302000b041a5298007004a0301d00400f418000303c0c41c4036503625642c0512810015003207500307103a441140560480c0e070b2980c91000c40f00748004280c4011308009056200100011000125010300401d80c1100204030342c580ea1180400800034031449820 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 376041780 1250 376040530 376040543
    0x1090302030d081f08120307180e01060e060304021804080c1912031509020a0207030222060b04060e010c0203341a090d051011120108030405100503070e030a 69
    0x900090011500c80b44c1207400d210040b420a1501c2c041e8000d9681c2000c0e07141e081e400c140000400c040d984036420a80701e014034624102c072242c0da1390342c0a8008910910800000482a0400c0d226610304101200d01441d002000c032840c14007a01c1c5000c1c081440038100f22501102041702c01d840307840601007040c04a1900e1000c000b08660340c1029407607412502c803046d04061500505040c01d0300c8028040040d203103500401038549040303503400e03449c00c8115000039600140f03102d114060090741c1c617211604841d10030014460319039504c50032104e0340500d00540002c2243c41100004c1540f15848241d8190b000900301c40e600300b07441c50701500701060a041208140d180c0120703800e020801200c4c42c0010450b074110f285416603016034180b9103002d100c0070544120504101e035010700c2000c01c260b103580348111108101c80d16180440c1001540701c000340702d081301c0c00702d0000210351001009a508941d4050450182255101350883c1c1d07591008109609001c820042c1c01da80b91020000c5101407442a007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 376043030 1250 376041780 376041797
    0x70f03050313140703050f060c040e1308030a0203011e1503020f120108010509060907080d080601050c01140108070e0609060f0a090203151f090303080a0f090f0b06090112020f01090302030d 83
    0x10090301f002c2070000f2440d041e82c002c0d400d0045282c06913003140e044402e0420075241503290000e400c1c42ca0313100100f000c0c069210200601101030310680c0254100c41c14081b00034090741003d04c1030f0000340c5092044609841102860a8640740260020f0101024a941b07861800701c060792592070044003a006aa030710782d50703402080440e100c1001526000142440100f00640ca0104483d90310082c0f001041c08014103000803910590140003900d181c0101b50b0001d02080c204070700c0c0c0c0e81d50003500344104030441c401c00c60f0000d68400d00e00c0348240074480c0030f03005184540d600740c180829901c0344020725802c1310071a2400114403507a8400396014080744490410010950400c00c85200c0c132510a0060381c07030a4002c02900382d03800155035800c49030701d8201200e080e5940d105400090841c0c480e5499507500b82104030382040740382040302a806104600150003603c0381c0f402d000c400c0100b402105110040701d1921030140c13030000781030001e03070b801403400d42e00d007076126404642040c0302084500c2c0443e0044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 376044280 1250 376043030 376043033
    0x303030605090f04060f02120703200a1b08120f0406060b0a021b03010b210f150114040b1c05010f0506010c0206070c0807030b01140105070f03050313140703 69
    0x6000d5031008150490b24203140781080c0e0944424404003810050103183e4400d8421540c50082e0151480c13044030400042e81c5107482400030700079000c105004580110042210307501f41240e4026114005207179602d01c09000c5240b418560401d1184000751210102806200c24800c041607d080c89801d0032440a10181054a440c50a2303400c0e03600f00d101c00d54814048144000da0002d00c5421605c4510022418004410007003401071912202450300605951310302d542100c80a0341c61103602c1e403c54101c94103d500c0c0c840b132544880240c4865000d08081000401800c0d207001d4a1030207040000b0b10009810300380070300007180303c203800840d4204011050354940c24890f082c41980307a09041040e00348018034009000820940c0d031614002d02ca0140420b886090007064109900a02112022203903040e440e0f041103030285000f441074081c1e540740d020010038107501c41c8080d6900f8603030041d54050f4041050350251840e800c01040c80f003551509850150228440d88002100003818001501101d41507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 376045530 1250 376044280 376044287
    0x717031305010504030201050f070303110406050c0f24070324180606080a09081312150606020709021b100606090504021c110403050604060b120c0a061121040303 71
    0x81c0e00c11414860700340000c0000d030b6085030444c0e071001c0300c4141ca29038a0303c05283c140e00604e4644100d080c2082c1c00b0902207030f0a6000401001e85641c110f04940e24082c45a0503030742d0b191101505080040340c2808154900342d10083c107150402e0319806e0200329503031b90911401070750b001400010044020340301c0810600b48400c46820240080311410701001c1c1c280388003e004d40304050702d084a46503441a0703400a015541080d5500013982004507a5080d545101081c103030054014240c1c3d01010604c11075080f10618400e1104403146500540440e600d0f004030407000b900802482e0000101c103600100e060b0b0014448092240194180002c0090814030000d110105c00e03040280158810014840c500c000d9001c1d11245c607440030400318042c0c0788080f03007510764061a84018400e205000511003008200cdd04041c8010f182600e000240d04000b1801c00e81e0340013440780031600800345103000d00c0940d114404100510b0f900d20100c403c00b4049c69202089603e070b85040941c3300c5404a0180704043d030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 376046780 1250 376045530 376045567
    0xa030305070807020a030806190509040c0915120803190516030501090c1d010201200405030d08040b070c0c080a0b010806010504090c06080702160e3312071703 70
    0x84134402440c034486107907009030851001800c418030801c0c0072484032001485444180014203c043c0130714640d07090a01d4000112400740c000c1c40d014a00300001d00c04d03803d1745c00c00c0007800c40360050040c0f4103440054407802e000c1d50018151a641d481d00382c5040c07900038a14002d4a00490a840a08e00001c0d270001005003200c1040c0c0040355260304050b8009030540e80821038134180501c511280d5000502c0500507401480500300c240e0700c80110f21912880e070a03d0b8400740c030031581c00340c3c165110291103120444903d101250001c18500c00e07100072918042c401c5c0505050030340315443c82c03810242c440d1511450101600c0c8101d941118040c01400391801c01e0208070700500341a00d05204a00481d95140c0020383c5ea40030b02e40400220500081c00c40340700b000355445840514070076240903074991000b49a1101d0480d411049281200c0b0804c905111440c2d0b00d141c1c0400c0104008600140e40080010188182885d01903030320404001140c0308505600300005504000000c540c0c880e54400942e0f070f0102c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 376048030 1250 376046780 376046791
    0x41109040c031b0818070b041706010e070e030705030303130203011802030c0112060e040602070501180309120203030405040507020102040807060c0c180e072d0f12080c0a0303050708 80
    0x142400514020040140c443c00a2102c3e00d0401041a42d215011114081211241414640700b1041d00251540600b030051055400c6c4040c20580314504003078544e501c0100784a017202200b91040000c07500c82c4100880340c05060700400b40d0f036000d80d80700700180c80c1da0010f441d40c00140c400045400c045190903c01d00104001c001d288030b945801c1c90f000203803507400040400f41800100100c0c08d03003004903030784401c001c0d00c0818602c1d02603060030b040c400000d4010050459444d17181c8400d0010005044844560003070340f541c1c500307101074100240340302d0520741c1c0071041303805100c1880040345550700c07401003500c40d4807580d0005840d20f203880459490030480f83d010009102900c1064400304034295061403e40d290380700225114104501a81c1c001d080c850b84005140c002d4000120310600c00f420001e2039034589641c542d0301c961424508c0c01f1114494031070714042d41010b0b442002000494005c0580d0030380203100341401c2c40d000c103034078500b01485004101d000a544104001d03d540c0c002d0300554008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 376049280 1250 376048030 376048037
    0xd141906140904050a050609060a050705090d080901030905011802040c0804080f1b1515030f100b03120d0b01081b18060f1b01051f03060c0e041109040c 67
    0xa1828000c007440041e001e400c0c40c0103252400008061100800203c0b1a580d80042160211310302a9111921000c0a40b81d06954a0a0001054840c1d1180303090700c0900328000c101381a40841952220215480200c985042c90b0715207992001150086c45844880700800800c408840300b1441003104542d2500c40e017206000c90282800085a800000c2d2050720008412442d61428420b50503c076000d000c0c0c6411030284210f81301c00090316000f1200c0c90103040341410b20000c99406204050b2209480080036540340c0c8019607001c44044271340c00400e40243c014080c0c2e400c1c1d21040701c410649921010360060384a888141c01496540d200c800998000c030603000d81100e010102c100100140f01e0f0b40c1082031007100c2406601155900d8000301d6603907680c2c000103169250502c42034102800070280300c4002c19460600015002601003e82c0d03d864403000140007255802d40e070741c48000f040003408840030002c80c04111081c41c0c0720340c40350031019003030203000c4c03902d5132400760170082070b1805000240f040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 376050530 1250 376049280 376049291
    0x80106030204180c060e030304050616020102060106020609030d2412110904080301050906032505030708030906040b0a11100905060618011406070c170d05040305060601140d1419 78
    0x454500d01c104c20a036910761803c03603150050304c40007c1c5940215013046a1114000502c0030307044d10313003c800c40d51180c400e030280e99071130780d0340c0034260303181c0c00100c07031581c66a04200908c0000038141c0c5d00c01c03024070f065211980400c042803026a1281c91450700044070320019042408103200010a00e2f204c410b86c11600c841041ca0542d50341102d90006114980c014107070349010403402c3d9428060408605d0309201001503803650000b0035141061144039107800b074040c014004c5807a400210403a1100b4802421403450f091500c03400c41d1303165010503861820410751000381258110103200a403807001802c0d001080114660a0031405d25402130f114601c1040361000c804050034640700002c0c11149076100100050b078111303012507031a2240b02802050078040050120f4070407a0201100c0c4088401c03400c8a08086c10b45909444600c1940005446940070a00007501e541c03241d040c0180c0b91600802c0703d4102203600720070001783c46c8907007801300202da24001084010407004c110500d01800c4030205124 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 376051780 1250 376050530 376050533
    0x61401060207092706090605040b012903072f1501051c06020a03060e0a0608060615090d0804080105070e01110c1f05120c04030201030b121518030408010603020418 72
    0x9800709110713200490850f1680c0c00e882403090769800881500c4e04000c080c010b03407415203000c03161107209008500c581a00c11780c00c0c88001c0112100110b14680c0c034003e89155481d284419588604081000200300c1d4861440d0003c001d103254078800c82e040c000005004c1e00c6224050001422016040503015032844090700c600b4007046000829659004200181c0d5400d00e00e00031400350685400564103000d04034284000c0341c005610003030031142850155500c9032619010080803001c440075000000605201040161900d25501b1040318030501da000c3c0340580c0ca10a850964000f210600003203200c8e5588135510b540c01103181000c030000900a040e18003407a400180c1411500312201240920012208c01030324041c404440481e080501c008c0f0381c92500740c4000d5029809400b040340040d00b00624003201d401e10b00c0362540c005651601805040100f0b002c45803442900801c07400c2e1000314a07403000c640355414001071018001d000b002158440c2540140800c0c5c42c0440e1045d204400207a14280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 376053030 1250 376051780 376051811
    0x602120a0b03060f04060e0703031121030c03250e0301050c04060210050c04050414070207051807051c0e0c0319050303180f011803031a1c030c06140106020709 70
    0x1a40700d4180070860f075007910b440c108035005080c0d4000d0820123205a48000c0180740e00a00c04403120402c031021103401d901c46401404042e03c0d0060b81141c800400e20100e40400000030156a1184070314041001080340c40c1c000c40f0700b0460010b0f068010a880c0f0303000d4080c9090178001c50b91711104281e8200d02d0b00e03241506c0255125104503a041010380e9503070203c1c4200d06210102e1b4000d02d402030003070103242080d20091a010f003060300c10034054400c490000170f072814800d6a2030101c4103100791404c00e41d030360780d00203a8043c0d221011803942800321050204041c14140f02e01040290001c00074880c0c0d402550038107182851080140c00386000d19040d200024400200702c03540701d12607648910014101744a103d14002459103004015400c01c400507144070401c000003050305009642c24400c0c80701400c006e082c011800303442c0c203820401c150702c1c0400c61440c614580030142d100381340c804c0420980342c59032400c07a8a00a4048440303094000104041981000804044c20080008101c5407510f21300c0d01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 376054280 1250 376053030 376053043
    0x30405062401030b03011103040326011401050a030917090a080a0f020418120e1f020c0405220b01090b031c20030a08071e0203040e13020d0602120a0b03 67
    0x241016102d040d5840c840d1000e40194070856603860784a501ca06091a012f800c0400b1980d0000082c401c1d504500c0d0300c11a00d240c0c0904854075050b503c005602445c0044400350b01440c51901810345a05805001404d0364000031080c0e0a240171884c0c0304c001100c10800425803235440f00300160705c07000309540495040c100c2416020303411030780041d0b01c0c2003449812420441010001d000e41c8178200480300d425400402030702d00071100300d60503024102c1180c21031044810300e0341141d005034860001c0245c98142030b48505e0300301900754401e000d506801016140c0030040180c1c1140c00005081c010000b4a0b403a00032800c2400c4101c01424845c8946142458109400070503801080a03030f003030031b22550828058003002c155614090300e50750503c20402a0000da4117a035070000040c81e06405910702c0c01c4920100c1c5102059501440c5018a42013504007104000383c1401d1781d04441059600c010f90b9013111740c0701070340c0c840c100241e1a0850b004c1505800e0500030207451505003004800b40c410394022811 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 376055530 1250 376054280 376054351
    0x10603020f121c05120106082502070515070b010f03261201060c1406010b0a11030c150406180f02010c031e0504080601081204170c060d0203040506 65
    0x601d0040c81d0b40410107140168091190040e010001c08410b02da5504c0f00c01400c2c4101c4030303200ca00141e40d0740c000c04c40c0d80c3d05003142e80c00c0d4696220248145001001c900300981c10701e96104641d03034a81c41d00000b400102513011210114040050544200b00329000264018a21641803200062940d01c0e0510003c4111000030410608880503880c0c10b40700000f0358452a85032192281c0329a110035019146841840703003a56901c00c0c200003111856400203e15040e2000c1d002010308004060750259000e000ea40076000181c0018028409070000c01c220b400f511107110342083d0000d08141c28200308036044051441c01c0c0d40c1005e5200ba005c6401d84100c0e40c061542031070280094510303805d04542214420120a5005290070445c00300f175030307101c0042c4c000c3c0d582610546031031340da0360602142c1e00c82e4040d0031039107110424003080080e464107810880c141d0310000300740d541c0c4140400c00160035521130071100c140154080184828000b04102665100e1220b911800d40810503000c6090503c144503507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 376056780 1250 376055530 376055539
    0x405060a1703040911040504050f04050c040c020a050a0c0608070f02030301150c0506092103010e01030807080408030301060f0e0405040b0a1d010e060610021209011412100306060503010603020f 85
    0xd9500c1581c100b080f0340041c00e580500b086503001c3d071000c507081644248103003449582482c0200d0090b051908035170307000d02c1e840002001041c01c5c002c1400040d289030222038055000308010000410720900043d88118440e03501500c034176091480143c00000d01500300e104002c080070441d000c40c0d40000451307054074050903500a0000700c1c080700700d416000b10100201580641c03030501841003800140d41c0c215441a201c0c3c004140c404184040303040c003003445400130014030f0070010804a00103000502d04139009140c903515090f2a00c03061451a4004c0c1d0000002501c0b101da4104540d03408644e4018942040310180580c1c1010340381c00c5c0c041039001d00080c1c0717100d98581c82904201443d0048007100000350000703104a401c4899000d0310791204503012801050100c9103018024404180541d00d04440c525007410a5003040044032025500341494603100c0003007180300d218110500c8014030481203941800c40352801c525080d402e56041781d00c114000d0b81402814001a92801a00c109840060390b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 376058030 1250 376056780 376056809
    0x6050103052217042309061e100c0803090c090c270f041e0e031309150909111305070207090e070306050f040506011d0411040905060903040e060405060a 67
    0x100c0402c400e00c1598028000404100300a000440401700f10041d4031404540010b002e40d512024072003800780c82c48801014040010880c40300d89011900b419205a441c078019405003881e40d60500c0c40d070b2056500301078542c0310500061301490815030b481c0e1b100e040404d506061040e403103080480303440b0800b440f5000b520718494040c620b446092101c0145a4020010f110120384030740d005d0fa100400c007480c200c020782081c81030048007800108a072a0b45a640d400c64001d00d00d4140b840c0001d110b070320304800783c1d100d81580000d03049800c1d00a076144140914440e03040d210380141007104010f94001e8600c801401e0004022a054012074640c0c121000c0080114100c4d046a00c2c031820407480e50401400c9038a440c0620840034404004103200d50b208501300d440d01e91b203e00c080e014808686a040c00030340c01d84000140000e00310b8885051107400a080410410b50564545003008811102203170554000304013000040e4001c000f458102105950811060070b250011403d03c8400740140c00d145d80015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 376059280 1250 376058030 376058063
    0xa020907080712020f181503010315060503061602010c020604030806010f110138090a18050d020313050103180b10171b22051003020d06060501030522 66
    0x16003e441c40c51040c90741c215a00c90042590600c1508440d92510400038421600e00f81401c04021f020041c041c0d20103078600310f81c42c50f034401001021000342e40f400140c4600000506480411a42d8000d10003030038007490b207001c0e0200003401c681d0040840d00441d0b22020078000400d4000c11103d0f0894000e01c0e000703044240e00c00c003d032480844e00800702003640c6000c6110384044c90900c145441c00c0c0201d2401c00400548074000c0c00780c100c000b50740c141e001d86010041154010305a10108050740c242c0441d0500c42c0c0c00752109420000a00c45000258100040c180c0d02c2c0380b104402c50010700000d00301084a5403052a40402c00b1400f010010082d0031604049590788005003900e000600350840c1404100d29101710300d94440c41c0e640e040c19580c101480506c506481c01d172130810f0301414400c5000990340180366018010300005041c00301e141c0f801c0000440942c4078005c461401074080c01000c14100d113480c0005049880017049034072420030f01d4890340240c814441d0313103103101038006402c6600e10021 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 376060530 1250 376059280 376059287
    0x20f01050c012901080721021806160c05040606020304090213080a0c0602010507110d0f030e01020403230309060708030403170a051501031a040203090106051c05010501080a0209070807 81
    0x203124101c1410744100b5070b0f880321101084628030b800080c2d80d0583d860715503420a03129266401d040440da40140007585400254541c094210b421980181c00203a0f0044804203d5aa0021a4602100206907449828007400030740060041200380c508020356850100300945034011802030a10242c1c00054094070b001c507203542c03240070304002020382d08040558500b000ea103030b0380740c400d0380003550074800041c9055000f100802940032000c0c01a01013010907000c00c88022081c500712009243e03880c1c3e030b039921024091002d0000765100742c0881c000c001d604080700c004109880c0c800c900c164020400014180c0b620400e86842c9a8403030203d684075103841c5400d030740301c1e0000a002c1480d003020208101410180e80c00280c00340082c06400d02020340780314011420f890442d81822040e580140c0c850499080c1076001703580c0480e0110001540039140d100164101c1e05c2c416410724181c548041880501000707120741030044c8030400c010079030400f2681c0841c100c2c007001000801800710550020303002e82e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 376061780 1250 376060530 376060541
    0x9060d02070b012903010f0e04140d02100b06040302030d0c060e1002031503011a01110c0409030207050901060302031b0729070e060301230a0b070c140607020f01050c01 74
    0x5000c810b511556031503000c5030700e9003111021441000d40000300400138241e842c0d012641603c4416a807613003124140101c0b44200c42c009802211103402e241441c001c0c0500601c11002004a00c1e0302030100d0b134112550f0f640503108009202845040e00304401c0005a9000600d00e040d0720450502e801d2540e0941050703c002c14000c0305480e04c6014041038040c7c00030003580214442c141040e05200c807980d0800070b050880319000700820001140741c1c100e00aa602882c078503d50388800328115140c011441c40841d09440c034a00c022005603102000901081c07500342c0c070042c003400f101d00d41142949000240c6c0c048284440c50203c0c0c5001380051548248446105803000017614411034600d068620100003040c100304540c0d02d000103c052004069030f1908a0450b81224184e452020b101f0580c54044011801941641035000c404800d0000388080d5040151038858010350741582034074030380401c1c8003904c1449072140d07200341410007402c00140e072000012080000e0030301e030451301c0b20031548040b8010030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 376063030 1250 376061780 376061783
    0xc020c151b0703060c0f090b0901020d0806030307050703080304022404030305070606151206050102070e0406050a0605031501140a122607060614010807020312070207050918010507110309060d0207 86
    0x50170100c4d100c039560340043c440b8280d14410b80c5c07480c0440d540c92002d01c52502440c4500350041e0088920083d43c140700e0004940c1002c0b0050650385080042d036107162800c0090303030040710914404803c020940c6860304100040c180000400c290452171141100b03146d2103207000050a01001007001400d000e9150700810180c40140d201580c45641c203280a454007090901c1c10800a0504001040d954800304607001101c0901616080c1500c980c0d556001910340184440f0429540e0b242c0042c9a680c02c001c038000302c42044060400c55418a03030208114004c1c0e444041c080d80413010300704010115504d00707005540e04000540e081c0d03e00f4030442d10400100540b0880701c10001305188090160035404401100e1074001248440140e180054620b000110340400158006000403024286403000d0243d01022520548039000e40b6030740040d03024241610f0025440030aa5294400351030244226038000d4403504026450000b03a9444964a204102c1403a0164002044016400d40160107403a00341d07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 376064280 1250 376063030 376063043
    0x20306180a06021206040f0e0c061e0a0c030f02060c03010e0403090b0307050409050f010b0f0d0e120a0f0905030d0e03010e34050a03080f0c010f0c020c151b0703 71
    0x201d400c0c1000070181c03130341a101c2c0b40c446c40c03034110900d0011116100b101c0c05400c0b210007a2026941171420445107404c0010100c020158814022140d00304040040c6901d520b0780c1c4400304a4009824005c160400e602c11800666002d081884141c1c000d2505480c1100c407403c1000549075103e28040301c42075602d0380140032100f00030040c00591034101018205039080b46004001654680b0225150110284074552604004116038090107a551006160300340c2c1518000c6102c035181c5102d140741c01d128800d5100b180c3d10200d0041d1046600c030100340401241d626050f81c000d403c100009440319060840c42c02030100d00f28110885842c21340010f410900184150768446130441c0d06000160342070484146201c0c03c1e07440300700c200b90981c0c0018091707840203003040014908550341c0c1c8406a004502c0380081b00750a001f040c441c04401d008206500c1c1030210040341c452420003019140071200c00da0b191240c440e01c508202105003240030381e171074480041080d03800d60340d0220244d800c000194001070000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 376065530 1250 376064280 376064287
    0x280507080a26030f04050f070807090c0527060705060406021305040e0c01080601021e01020d060509090a0201030207030512090a06050109290a031514060a03050d08040c151d030604020306180a0602 86
    0x31014003154007421a2fa0070f11041c054066166000c0312140306080c3c00c014030441812261059500300c002e62008400c014041d40c0c075101c1103480351b51612200b201c04850080c1c00048140e440c8510b0040c45000b0070007603506011507407a1b0701c282d0307441e0f42c0f0b074000f00c0341000030002c000b03409a0700c01c12200058000040040d00d04802c10390303c0314007070350101102900c081c1c1006c5000495041c00b01885128882c280040d24110b41c0030b50044010350700c424819010403106101515a407440da0308541d0280d40008004e10070903507030b0715050003a11016408002028a440c04404a000d40b2181e9009401175288400c4401c0c0140c0c4005040d0a0694002074007429007154044403282a0741c1c00078001c848016501391403540c944040109442590000034003503080202d4503100d90b406540f145412500c143c0c405044203464068114066044211110004660104444041d044602039044004003a40074081600c3c040c1c0200341d40d60f0014058000282108800c111000c40510030401d40d10f42c0700301c05654 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 376066780 1250 376065530 376065539
    0x1112062106150d0c06080903040b0f0705012d0e030c1c0815100509040f0c2115030f030c0203150f090f280507080a26030f04050f07 58
    0xd840c80202d4140300600001c40141695143c92080416142d601c15a003042d0b035810a4811101600c003d411515a03104c00d03c4007088045580010700700a0744a06071103503c452207410000c2c29569441c0c62291500e0089038801d12410114501440c001e491500c046034500c50b580c0d865145200e20100e10000d0f000f07628130304448450007012100c8503007482c1e0302c1c540740307856841c01109907d81102c50142c0c0705040d522924030347c90050340585a0309000601c0000d0b442c1844480209460184051600049100442c2002c580a02c0c0845841d44070700f160401100340c2d002424680b4000501020740000903104484040520906903400c03d030758041d0641c1e6000c4104218a586980e003580c00c0c3c01d02d0303207a0070001210801d0000710701880c45554001054905050516004503c01680086d85646580820038010400401c100001810640c00614860300e0a0410b07061200e00c003076940c5c02894801c01500c1d041094a401d40b600090400c0d0641c50071b880e18907005140000e60340d002c0da107a0092010004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 376068030 1250 376066780 376066783
    0xa1e0e040c0905041d0609030306010f0c061b02010e0d1d1207091b0f0c03020c10020709052a0a1d1c050f0d17040f020d140109120311120621 62
    0x114401740040480f03089490b030381c0c03d0b952240000c44000c0c1c0014461f075009006c42d44510000180580100c8001604100c1c50343c848801c140c9070404980980c7d124507100c06040410808459082d5081c17510380000c4440545148042540000d41071007490319401495109400780984001080501c40400510829254401c580c1c0070605150f00450303c00c0130229041c600031040d003075425034158041e00040f0f559100304449106110036200c214413401c88042015680c41c07180c1c0303002d8040c1d4060207000c4000301c035202190480b403d803540c0c0703061401e1051016003030f0060b203030a00c3c3c21000001c8a10640c141000b051f904403d100151030501481e0f070241c01802800720741d0741040340c1e01c1c10030b0358112400080203585102000d11041241c2c2c1c404000600441c000d040c034007115500c02080424041c01a803141c0e0440460300030306125a95484151008100c440d1074103032003001080c01d0600524100d034400f2a0b160080c41802c1460007040740026256540d20910300366110a49003242c00c80c60808007255 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 376069280 1250 376068030 376068071
    0x30605150405011b230606041b0801030b1f032909150402040f090c0e2401080601140d02040603110f16050307050a080a1e0e040c090504 60
    0x194000d14401045486245201007250291003042c0c4455402d0880004c9010424000035029166201c5010142080c0c200d443c1814035401c8411004251070304100d0308100484125440c1c0c6041d03c85072034204a0943c3e0002070640c1120740043c0c014015550303484031081c0050310380d002041c41c01503045000c0100811004c40b803c4c420108800c0c501611820400c210103008241c66400041c0d10910003820168450085194400d1000d0404594525900c002c481540c940f040100c8401001500038450300c02114029603100b14195140005055844c1070140102d1b40c074861141000244000038000307901a02e1903500c904a8035402e02c1d610158004103200940041c021040001c0c2001c4000d107042c00010291103981000400e0b10b854a458907070a10350103041100c08035050b0205108890118809100140b5114000c400042da2403243e50001440c08000090b248a1645504582e02015600c00140e203080d02c1d081d200020710b181c141c3d01c1a1000c00060740040ea006041c860040c20b0030110364000e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 376070530 1250 376069280 376069289
    0xa120f0e04060b0f0901200a02030d030903080f091507020f011d060c07030c14070302040c0f020703030513090f0e120a020a11060903060414070609030f02040c09150306 74
    0x31111050a5103081005030b80c180d2142109a450902000c1d1000d010400209213501d0305042606050a10f810341c1c42107150904140c40c159000004d160080d410180324184800916207420040c8540699024000f1600500300d5091840290b00265000a040180c3d86010b4400b8611090910780440c0007562100156009241d5500f020001c0c0344941c244014041159180704c00fa008544d40c0c50ba804081c3d03001498298100452028203401040b40c0039407000c01c426100340a020940e00354014131088da1686000041004080131806040c0c55000ca03103801500d40c5461b00b070b903540c410051f001d603580c003990b0010707580c55161040c01e0300c1c48000f5612140c074044000301078440070007040e8065129802030a10800160304000c0403400003440703004062100b0800200400c1c01c007405400401e282000c1140c08940c0c1c419007800d01c0103000f030108020401025981350004545007180c0e03c100d800c256000b4000e01440c0c0300c80a6481c198055403040c00030b040f50b540c1c0c040340b50b405103500030003800d031500c80c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 376071780 1250 376070530 376070537
    0xf060705010e0d020a050709020c070f150e0a1401032d09050f34030609050303040b01090e0304050d1115121b0403110103090506010627050306060d050a120f 69
    0x501c20f00d0020910303005458010000c0d040703c62602c150340000c0c0d4002c194014060181100100b144602c2c022040d01620003080f28144050f08140c010b803811103480cac2d0f45889010510710800400c200c050315494a0b840a2a021a400b82030011004c1c0517008048220340000701c0030041d440349030307880d4000005203015900712410b0311302c00381041e13488a492110040b90340c10301e90f00140b03096040c0d000e5840c0000c4100d1040104640e42e454840881d0100b150445064000005000500c6a2180060702400344000100800c0d8040c001156980c031031440349030b019182c251044000c2c001010420075400740003400c0c1016410b1807040c1580a41c1c8075007000d50709150100702190b03c010410004082d54140b4161541c9002d0548e2103201c40c0d8445007036003904160316141004002541440100d00030155a26055034900c244c0355800f102c1d00d5409940c000906052104005560300007400d2a00701e14181c4007526210341c1d5050a60a01140340005070001125040c8482416404240c0d1090707555a690b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 376073030 1250 376071780 376071793
    0x51c06050f090604030f0c06290102070f15030e0f01060509090a0f08030405030d0c03021801020c06070b0c04170c0103060806040209190b04090602071118040605060f060705010e 78
    0x81c0c00e5120500c10b0314000520362000300054000382c01904400c52200080c2410703084808a955206c003611458503800203082111885a0322503240010626580c0c2c1d424001740c82c03941e0070701c0700951540010380b00745119003900802c40010342e4065485021841003c0d0140c2c0d06002c05400420b001c2c11561280c0c074095001c900001d0701020b000f107941c1d00c1c00360340148121451240c540703032000f49030800380040c1c03118041004074146c2024207110f406020119906c001da240d107604d411007508044c0c027500440c15500959024180c43c2d448070304407091140e1110b118150b5032501d055054003400346800c014514a5000d040341c00000002a050044482c260b90521030300341c540907842d84410050b640203404c03d8400c408210b1160302c80004201405d5114000504d030347d0440700080c1641e00c3d904080e0341c2503500117912414020044034000c60030006981001c1c4140c024000708040220090010303003004e41d03403000301d1031540d42c4da9180c504119005001684070b02d914100f041c024030f60b0640f003a04620414 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 376074280 1250 376073030 376073041
    0x803030106170c19031103070e030f0d05041e030507030b0402210d0f02031908040b0f060d030c0c0509010e160e030309060c0a08030f16091518051c0605 67
    0x40040d1071258000d80040e6044c5084c0c0c401410a200b5150040c40c145512949040701c0000700d58051403040010360b07101182c0003801340505041c26040b0004591a410141d052018160480125001c036100c41c0b0919940381c1001600c0c4d00c0006003034100a14074043c1342c10000610103030058081c01140200d956417200d80f500300d003a440d000302c001e601000b0b0303420405140c800180140c2c1802c2c01d42c509401500e140c205003400c8543e1005410031800042404001444140400a032403941d00041c1510144458100040000d0904159031310007420841c0b021010005c114600702200d00800c4090302c0c0d0429540c54600d0300070b80040840f6881c601d05400d80c20360610b184114841410114058099864441c0130010f004040d17000e41c1002c545031082161300800500c1f038400451081d42451540049402d00c4160040f4900c0314400c45010440901c5040c425a580029100e6980503182084003180c9450418100404c0d401c0c1d0005900083e002e0055801401001801c4960b91141004200a5550 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 376075530 1250 376074280 376074317
    0x307120209010815010c0c0b07030e04061409040510050c19021b130617010209120c06040e090f07090618050c250b100905070e030a170d060803030106 66
    0x107200700d181c00500440d010649198003c502161494410300d00a51040c0040d2102580146658800e110400300050b8410171f240d440940c4c03141c0741c44102c03020f0120500d840c1d111803458080003009840b60030803001007403c1050400855120071180a410302451070580c00645203900100250020040400041c52980d4404507000f000409a07401c0146450019000e00c403608202003018011641c5c2c402c13000c20b8800300410300f49001c501c2d0f000056601d90300c4105102e21004213010714000740c2c1c001a40001959134680a440030794035501c080c0302496503000c01d11450f002030707296008000d0080c4100802c5c000c1c580c1c1c1141e010390301d0340c5451034001d021040320700044035000c940001ca003c0c018440c0c0070068813018034408480c490101c004000c1d12264941e14246503003501c00c0146000c2000f010007204000f03000355588000242420001c0d02023290129407a0820040300429100515510900018142040e140d8400b40f0141c100506078607554515601e0340280108000f0a0107190341507a159031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 376076780 1250 376075530 376075537
    0x2106150f2f0c1207050a051e01050a12051303081501050412030c1b0905061e01030c110706090801050f06060a03090204060b030906040b1501020a0f0215040b03071202 73
    0x100075201000105508034101e03241c0d803040d1059a11802090816141c0341e0360506841d140415000103014440c0c0361808119008000d60311803030044842c841c111845001200750072843d18000e081c00e982e1070301100000c80d9014628980441e409250000f40441c2e00004604440701600c00d4980c51101c1d110b1f05000e00881c10703427140e0725000a45c03c00c024450201c58001d94495076209003071800c04828243d8414104910810b040c4039690003901003040f0046042c043ca9811030000e903482c221100707a0b00c4a004400748076500c0d0b9030501d80c9685a0410342440381540d1602d90500388240c81010752502c2c00100352050600c40e036030b055800d100200c0c10300c1801005c1c0030700608000b09841c0c900300000300244c0c0541100c40c0306991061361580b001550f201304a0066104425400c082d180c585000d24040c8299007014120000c0c42460151210190f40c000840c0031050760440d0b0300b1050385403a4030000c0d40810b05030480100005022070002590001000514003c14540d20741c00d01d003e1841000c2800c038003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 376078030 1250 376076780 376076807
    0x6090906110301140105090a080f030d0c231602130f050609130b15100309050d02070b030a0e0f0f0c030d050f0703051819091112072106150f 62
    0x10804e141c88541c0c0d80903800400d521a4058661030754603950b080d09904007070000030410036542002681001d405024456482c02c0b00090a15110000130522005040050701710600406000024075a8100035658000245154000d0103007468200170169003016149488112030f460741484049034a0703107051000c0030f1054240500c2c181440e02079454003850000046c1c20b0f1040c0808009811080b9101c001241c00c0904094a02003025035862030220b1030408182d1496086400803081400b204a000003280e800c624078140c0070811414041c2450304202010b10288020310400980d000091008102d6040b088022816200341014001c426140d81c8143ca14035690b030b0302e0802c0300c0000680648007901001c0324400380a80c8290160010401407440b4458000907104148002c0050110b1350203800034144968001c0c03070030502210b6416000d00c030041e0501c1c0601030f0141401410201c80034a80b14200c0f8148011322185684280204d89442c02d481d0740c2d000990303c8040c000c08603005002c00d0f607159 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 376079136 1106 376078030 376078049
    0x6160806010513060c2109061431060c112106090a120504030203070b03151804020405070e060d05060a3302071203080402010c0606090906110301 64
    0x420403440018000c460010040c010547c020642c1d0101d40907403c0ca510000c40c11441c2c3c424500581c2055100140c8142c01001240d411160981d00126403024103a005611a803044510071000a00503000121003c0c0000c0d0300d080c9841c18420f00d40d622004042e814107131042c03840c149a010344e45001c1951082c1031000c1030102d500030030402804941401031415285a0220751251418442d41c9101076001c0001044003c840144045194004007112003400c1e049816401050050702d080e03000d24039200000d90441c0c041c01090820082c000d24650a01041200b20009051700800041d002028080300103140d030283c1001a51030070401c0e84602103c0e500000301074040020301d103450115070001c1c00c10800110200100002c20341c240c03811002c00d517103600040e1068850315400600c1b40c1e240442c0003c1d956896404540128480d460900140d41c1e91a030956460000b0300501520 = true := by decide +kernel

theorem cover : BRFrame.Cov 375899280 376079136 := by
  have h0 := BRFrame.cov_init 375899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 375899280 ≤ n) (h2 : n < 376079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
