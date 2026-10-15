-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4288
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:08:08.489509+00:00
-- url     : https://prove2.me/submissions/bf6a2aca-a6e0-4825-ab9b-b83d22ce08b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 771043165 ≤ n < 771223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 771044415 1250 771043165 771043193
    0xf0d0209040e0a02060a0f02190f030e09090d1202040e0903030114030a0f031d060307020d020c0f06040e070e0409080403050c0f0f0f040e161d06090c09030118 70
    0x21001d002c542d085000b07090b1282e1100e0402540448100001407615009440801102c1c4440c010b551200822061807420211070301c0c0c0c01c59000702822000b408040e080682007a80000a0f1020075a900d41611004d81e104140b0700b252081c0102194007032496005501104d002e000712a006c00c0c22418038005840c0e9039002030042c000c0000344d4640c050854180040e0200c003e07a0031445e216800c2c815501e09480c15202d0308601ca50541c590714034402141c0f5040c0c0254002c20131540280300c0001843c10090500703c4034500d441c810b41c0500c8440c0360680e1000c09903001e6a180c122040402d0301c892500741e8070411503010044c0c101e81405e4500d414007a0110181c03007128041c0050701c424042c0702c01000030b080e00003102c65911683c8020406503a00b441c00c208101d030000a400003c0307052200158510b029100504402d0718a074403401400f09907506840c0d1495a1b981009500b410f04140001904015008240c0040c0740408540c100566402b50400d001160040900101c190400c0c100b03103c81090103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 771045665 1250 771044415 771044419
    0x9031504151a04063002091311040507020f070f0b03010303050c0a060f050115110d11120c071d040302070501030906090605041a0c040308040b03070c0c060c050706050405030a170f0d0209 82
    0x81d517144030150f90200d090740c100c958000d004100c0e41d42c6000e41030307036240f288100940d490203c01e14130342529120751003940d00546041e0001c00f10280c01c4c003000c915101c40c3d42c01c120001406030b03a0130010b001d4002c09507815282d060401944034440c4a64540c03403c500c007900a019181018400b001840285c1d000300d040e0b6500f04540e0407078101100c01135405140c54840141140d010084180c41584120b0001005008800503a121218030720f02107801a0031001051714913800ca00b001b004684001c2d19851002100c1d4075001201c0d00d40380c1c13030194941c18240f00352070515032a0f01c0d41c0b404001ca154041017451383c1c054010811420a8100100d864040b1045d44090400050214411914240c1941d007126402190580381505000100c002604050700e40740510045140d4180060018610000070f130420383d44141d914282e509000380380032150340c0050113000d0108028419503e0204500b0481508150522030105038162400c0580c400c0d1144150807d1000c01d00920076000d90300248070325602 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 771046915 1250 771045665 771045719
    0x90609060e0d120e0604030c0e060405130f0510090305031f0b071b080303010e040614070804030e01120507090302010201060504050c09130f0f0209031504151a0406 72
    0x3240c5007a200c0c0051010069031092000e16607000092092560100140107490f04140546108000c140a030f0801e40080b164102c02400c00e001d680131400e0403e91100c07080b074042c4054180f03a0301600b0a800382610143c542a14861003000340034082040101540103038800700300340d14140c100241a0f800c01d50301c1ca0000d2184d030104c4010702c40707074842010517030369607151103841c0400c00c1d62003a45c80c1281145100c100c031030040000405002c240041c40c001c1c040c00c032007241c151405281078422038140a001c02c0d000020b81d000d00c40c2e0079074080324031a07015505060001c0380c030304240016a0302c030410400c2c400d800c41c200010000e1042e804030091088a100781c000f840035a407940200300c1610b00c2215814a074581c00c1c02205032a2400e01008181c4d03421040c00003c4070102c0341040c1e4162030b8100e04203c1d0b000c1d00041c1c600014102000b51600e102da40da03403110010708040d5a400f1a04c441030012100441d2190b6501900c2c0040d401200d1003401d00620420040d07980701522010200603107440c1d40910740c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 771048165 1250 771046915 771046919
    0x1c1505060f0a080615040e030a031b05031009020f070c0f06110109050606060f040305030301030821060a14030102040509012d060509041508030d05040606050103090803061c0b07090609 81
    0x4100c4107031029100e400000d4040c9070746000194031000042d00c5017a91240c0c03510b504c02040380c5e0600050445852641e000309071100d15084070201c164074180b4800800c05c0420420030b01810340305811302901c80350000565625808103500e02d4038000c41201030035004003150001494426040c08008a400541b52402c0e000180d41c9038608903980801c1c06807039038101400141551800f00000c2c640e140750340c8009800c0c1620390700e84a00c3c2d504241c1003150f0054000840e00c00d1010401c8402704107245221000c204c5207030000c00304014012a11030200c01d12445e4004e209140e80030340507140907100140480c0455a5140c81611021849e0221607100780c9c0d404584030700054000b0034101c00e48003980c44030341c5072140e250203010007030043e000307007640f91741001401182652043c00200b41000055401260b9408d0074205a070491300d255000e0740c1418039040c081c00c0002d00002c1600d9100ca411101d00d10f01905c544038000c900f86144031b000341401a41005c1040c02a0001160780640e6075566a034140310b9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 771049415 1250 771048165 771048169
    0x80106050a05070f020d0f03090e0c0702220605040f0911010504030320030d06091d07080c0d0609020303040305032d070b1b30151c1505060f 62
    0x2104110300c11002030020003c103400b0407102c4034210f100620280030030698201da80c42d95801414280ca00301c00080b10002c0402103001800902c50b0442d40d10042d0318a440307210340c00945c00f95900e01c000d040000c0c0c2a4100c52a0031341c1a40070400404002d4014000d40f640001307040020320030b180c0b0855600c0d85017044014194410b42c162003c0d00d0b40740c0c49480c2101b10785403680c0d001200d00481c907034192104001d40103a10040b4020b4200804120790042000c60032205c0580346030311403803900709060740b100c1400c00c00301304d000130311054000040d50b0716803500000e41230040280080140280d0503200001e80002005000001007080c42d0425403c04001c8110003004d03d0400600c11082c205080c091008101142e110f07081c054210300b220001e80c21400d50b60306040c2c0301c0d810030710301c1c01d8006008078441d054018084840d4042c3ca82c4141c0034007020306c1c050005000d0301c113017404e0190252100540c44490700d10142e02c1c2920381600480320341301d100c150840400207050100c4001e07000d03c2840800103628 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 771050665 1250 771049415 771049417
    0x30a080a06031e0f0606060e03100e1b1c03020c0901080303090303070e060c070314010e01020319090314030a02091c0b04120c140304170a031211091c0308010605 71
    0x900da1056101001c03e004080310211102e03c40015542c01d00c03241001000204a80f041c000109582d4980c10300c21400781e0101410100d100681192050601044808070403002c28200300b19020074200c04004a2000302149040e0043c2200090101a4032600d1040c0343d00000c900c0d100b203408480d901c2c4c040e80c0f0740c500c0b80d86a02054803140d12581c41403021900c01401018190f035050009003005041048044a49291070629407054071032721503503103d05000981c20300071104010b400c0c1c0029403440c02c00d4000039030304408002016070201c0c1d07984180d804052090b518038245909100d0741c951241000f07441480254001c120051048064140103c00049400c00c8403c00c140c01030344000c00ca40c2c0d251121001042c2c8d80b5002d10800c4003011030302000421544d02d503403145a104000b5920f490503d0b10020310340c2e0403900000c146501040f07103000000c0d800000165406101100465079458103001001503020348041e86a024103103140c41000890141510b00580340695983c00302d0366030714001540c00e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 771051915 1250 771050665 771050669
    0xc04050114030d1d1e04050414060a02040812030c12010b0a0923010309060204090c020c040c031803111921090501140705030f0a09141c060b0a05040e030a080a06 71
    0x80448604e60781e842c0415a081010304034034a034240400d0303a640007404a4104403001c6401501d40d100822901004001c11980002582c07411864681007070402540c894150480350070b041340c00000a210b4180700410f0f1000d000c24500c45200c6541c58030703045003a541200c010207002482280000950050504e02ca22003202e0843c0c10310004c014490045019041d200c805403030316074003000000b580c1da066104400000c0b40c0c903400b0b0003010004100308000d88801078400c400b010304024500c201c5e0082125000c4040b41e25042c0312900c805561000d504040c0b4101c44000705095a0401c082032204510780684007109040540d203001851740015a410b001c18040c050000c1c4807000d100b50012079182c01819042d008404030b030300300040068004001c1d03201c0308110000400d0403504001d468007a91421410001c102c4450320541d030003444200450602c00005040681c9035500b201c401c0e281c006845006d81800390051190031000807600342d0300c0d40315109072000203148000040d241520b910418003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 771053165 1250 771051915 771051947
    0x180414010911040b190b04140a08340b19030e060601030e0106050a06030603050724031d0f0607110f0a020f0a0e0a06050a09050f16020c04050114030d 66
    0x10030002c02d00c007400003c0242050064100702040c1c05280550184403203040100403034441540d581c0d0170100030b0007148103a0304096000d007607500750a1004000101b46900340030052540718090160f40d203e0b881380e9852100303094030006a1800c1c042180e100d03280080090003a1490070721038840054008a003100c03079241807251a9009040402d400c0d40c0310742c00030740c0403080020000c01d075192654000f800700d403100c0d40003e02190303551008208200782030001c9001042c14441a000c504c0304903038051814003048420604050b603c14a5801007c111340b20600310f15100d03000c0b10303c1c8640c0414407a0b540e04007620104003041046002e15111100005c1582a60f200180540305400f20380c0d09001140d5007000074254052a440341c0841c140f405010420320035844944041030143c90f0071706009072000035030040d83c096801c1c1410020f69403102c0410350741201040c0341c1030303d104042d001e081303003400b1600d41040da105003004000126900e0000c03412000ca035086041c0e6041030321515041d01c44110300d2903014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 771054415 1250 771053165 771053183
    0x10302210a06140f1e0d0b0a0c02070b1326010f090b0612030708070c082b2d05210a060f15122a08070822111804140109 53
    0x83c20700c80545d0440c0a030030000341141b22806011394610207202c8044075aa6038060f03403900c20482441e0304101041c000d04589560b1403401180c1107076031001c00042c0c0203851840c0742c07040c038249003a503508543c10917103040c0c8002040702d540440c5030040504041003056034404a4000031924600d0800e160320411b81a485c019803410380c969951113000e070803d0a0a581a5214110000b18288144202c401c5c0803913010700c4805014102c47c2c10b640b2084281c070108108402420304502c1682d01d82200d500d010000f140d401c00c003601a42084901d4070035412401010000b060001c81d050f2206090580500340010f020300a0580310b1401240500700c905c904070802180d0407074131a0030b9000c0d03003640344640500f02001c07404070600041c040b8141070119505813212802a0340462040d44640801e03084891464003c4003802c009068218071000c050764032050b4031600681804008526006191745600540034181100380345190b0244500d08079001c3e2a04c0301000a81d034001d40041c401d0454440c1d008a81da = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 771055665 1250 771054415 771054439
    0x30712050606040b151602061b07060f050a0507080c01060513020c0708010b0d020d0f0803101d0103050309060a0516050a02010912020102100b01110a062004080a02010302210a06140f 80
    0x40d40c2200c1e84047e40c001908120895030f4920f041c40c100d600603000c0005050540c07070400c0090288181d84c80010400c60700313001c040c01456010741204d0f54950003200340d075103643c95940c0c0b460040c4060b5000383c3e4040f0b0804043c2050000303d401510341070140070b0035165429594641a401e81d01280b244541c8840000d0000c001407402401d030f150418010b001d030f180650200d545102e80d036401500c1d8000c01c2c0b100c50000304080c20390811105154a40707490035407003079499591919aa0302a011815103d0b04002c24181000c1b480b40064038a000f01e4000e02c1d203078207102030030400c2e1034200f0300d40140e000405c107400c00f00740402050211026580c1c1a40180401c216500500d0700420455455904210301c000c110310021008010000c69035002d15000a4540000070204800d0750280e0f80c01103240380306020800c644c1d5804602e1658580c2c0a00b000b6944012042c00f002c032111254641c03c01351030b01102440b001013240c0d400107017a280d414110302c05817401001000200c200c00c88002d40d006803c0d1440d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 771056915 1250 771055665 771055687
    0x20414270a1a1801050108060f13030903061113030f0203010509031602040911180105030105160203031504020912072c15060c010c030b10110714030712050606040b15 73
    0xc1d0b00403c05003400e488002c909100c42d00352036081c0e0040138107900140602400c1c0004400b1243c0041a90b90f070744103144843c2d900580000c042e403001405960303842040d100314003d03120880e01c02d010400803140070b080d102d190628500003148000e90080d0f1078000000c12031200081251101c52001000e110480155800c01010f446004000c032481030080b00d10300515192426200d41040c002c81c1035817a550304100c10f15003140c1000f00499542200c0c250031610603070f004802c5030f0304011000030040c541ba48200200380644502c2e290aa08603103008180d010f03600c40070a140042d1030740c80d000c186042c3c06543c04241290b52456401c0c44028040d03000c40c201d180091100403680708040e04443c20b144a80703210500712208448003602081d121720740e4040328600706c407060403d00d80509200d0400c2c035a6200c3c180c0e4030015405010100c070300c3c0c180c0c80720182da8204010002003507200d0508a1810440c0750080d01e40c0000e0b5461400b4604080c001c00780c81c500400108445103401c0075a42c10b000061744 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 771058165 1250 771056915 771056963
    0x1e0503060117030909010608090d0525020f030a050703050106060306140f0307051309050c040c020303071b020307090c020d020c0f0415050303030c030402011701030507050607020414270a 82
    0x2c004109100c204001551520750a1000c0d00070510303616100c4035460302182c3c950401030202c01d19030401104100d00d4084800421001d60305803042100368000300c2c05840850102403000c1c0480340c0c1403052007000401c00c6070001c1d40c141545d104800900c4041e542d0503059050303840368007070060a440310403070030b43c25402d00d00302109207044003c0c00c40d8140741c0c2c0c410108004c10450300b45000d82c1600c41c0401c2c0144002045030110700c0e041518100600c18480e02d000707449010203400c0c0310400c011400c1c0440c00c4c40c2101c0b0540d900c0c1d07800030207880c0c080d903884038410002c011800c102009805030f42d041c0702981c2d002003a0b51a110320058080c1e038411042c48200300c02048240a140c030000e88411780400e0b580c80407c040d62150000a07401556814540000341c61400f169504a005540c40c00c01440014008590700003141d0302640e205d07480315103510000340680b8640e48215019840c50080203040010080a160f0400149480c000107010040010740c5890300d801018000c3d042021800d00d80e0038000d9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 771059415 1250 771058165 771058199
    0x307050a020c0406031103070b0306130b150f0a0f11060712060305030c0604050105010e0c0904020d1112100b070506310308060103050f0708151c0c1e05030601 70
    0x841542c04842220380001e00b1960150030680e41400f04003100e20607810108100c0018005000219045103010070003d0b00c1c001c058640c4070482a00c0304030b40c0c001e503180d901804a1090403000308540300c1d0310002c3c0d40c1c126504210417a800140700c014184540b54000c41c01145141d04240241071030b07682c1c500003074492680d0681c8121380304c1e0b5156030000c08903a080c005003094444c00300c09000e15080604141382901c80c103801c910003041d10141400610031189080321209601074401680b40d24603007003c00004e00000d00d40c96101e1000080b10803082e030700070540a119115041d1040d001544030303900b1002c07a00440784000c0c19548442c001c9031441800e101d584200c000303460340c43c3d0b00010401c8100b90302e075011100c044011660320780030b202e401d40c1c05015044c0c0c0312840b13440000561818440042403620090310505e00c2c083c00c944400c030241c4446011007184100140190f040180034540a124040c03d0706c10801c04d182030850140d01d0440e284494001c6800c014000d2403280d003401100803d04180d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 771060665 1250 771059415 771059417
    0xa12020f0a030305040c0806010f03060c02150c0c0f06070f0309020d02060c1b0118060810030219030b0a0e0d052b06051207050a060e03070306090f05190302030307050a 74
    0x440111409120810110030014803d41d40402c032402c0603c2d05043c203140c0383c0c01020180e0072100040c00128810170100003220380140c03000c03c3c0c000505e5401e03424988002c007032410020b0070008105210314100018a04580004101d410103641c3c1040251140c9069403905c00080c2003248040c4441d129410102c02d2600007402052096202d6002865a9100d00100d2146401006000014078081420302751070700000e0030b2074000000700d00110601c5090360b01910b8280003844011814a03589003c078800a1507001e0480050186030004503002071f88948004caa408905000141c1d0088650260700000400034000b800e12802c0c4c00015501a0018008a030b00441e4200044104c02c812840e4003500015091000817007074145401d11840000d21003d0701c07800d6000c41c40c1001551100c404ac0411100c40785410180d907442400040d0901c00b141e80090091030901900c40e05014814078262030b624407900446203410302c0849200c1d491802d44034080d0141c0c105000007885103001e000204810185 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 771061915 1250 771060665 771060673
    0x309140d020f041508010213050a080a0c06030e010b030106080619020403021c052a10030911060a020102070204050c04051224060607200103061e05240403081306090302030a1202 78
    0x48041c034508a0b08985048e2a9401d4881020003180c00c110600e070001d021340d0f070b0241082c00340715104c9042c1e800c3c0710310a0208040d0343d100c2d1303d00048803c0d40a20a4004024001c0c00942c1d075a07540c3c640d0361074050703940d040e05c0800300700001c0ca20b401ea482200e040301d50140005184c1080581000c1840d07801d01e0003902c1a000c2c22000010040c1891040046548240000307103c1c02402d03401c1c0403820102c1a48041818500060308003c14081010314a601b2400c940c0c0030f91b10604102c04901a00516100a40140c14441400f0250040101420542d9400c0c0c5040d082c0440000c2c0080c6d0b00c032013848440e040c0c035400081c4041405894134a19607c46405400d0b90320303050480d541c00b60407020300703901da40d03030090120483c00c919a494000e0700010405140001c80c0d94030030b1102610b25000754450284a200c1ca281126941905181420500b0740c0064151351516030302d0070240926480110011500c2400c50800702c3c80074001c824103402c0d42d4003d4020103100c40d00c1d07514004901181000e241c03e602c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 771063165 1250 771061915 771061919
    0x23130c0201140a02030405070e0c0702150d1508120a050301030b0a020906040308090907080615160c120c08160b03250c060b0306070819180309140d020f0415 69
    0x200b0400100d000b198680030041c4d4a01e0715081080c1080c1c00342d000101c203640c2120600040c50004030603a171525030100d8280148250b03d1040c901d0300d10400500c260158241f00e6286801103031600c4543c12207820303409461401e03440701680c00700b41c03103485088008a002440180040f6101b4110719034002540900149030064060001d442a00a58001c980c09030000511000509006001c1d94020f49117040042403410850005504100354a401c0304032008042410b0310700101c1c1038400802203810400c42948951200e09103100d00500180a503500e8040240010710840005002070040c003900c105125039070305050741d299080e48007030005200c4455280109901c0c00030f585003180c1000341c070788170b07992f17540c01915141c020707125035401c078500c02d07004076003007158543e000f0940f250300400c0c031400205000c038600140f40040c4410322210031518180d681400815800c0030f0074030305071441c00485000001c0042e04015070315002c0000290800080560003442d81800d400c110750705090302c2818201c140d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 771064415 1250 771063165 771063191
    0xf09090d230d06031b03020f010f03020d0e010c090e010f050904020402090415051201110a050a020304081b210c0103020a260a140c0a081308031023130c0201 69
    0xe0014030703019602c6075407000304004010048010341864a02d94006061461454001690706452100c81506002c494098203610368802e41c12107003015103024007008403840101d1040e009152014101e80030540c100c1c030104196001000d41412691420701c86c1001d0303030a00c0c051120348000607200f260071607001e101c400940e030b5030390059040b01d110350f440a07201645010100000300e2818441680c0d2640b61000100041680c181103404000346030400d990341c0c01e621041240346128540c8014001d0168014201d80c8000d50101102c3c00c801c11941d104101305070360200d0005541c51032641029034440c15201c0c6146d4001c3d0003802510055007003c0d0211218a0011590b503c01d0302e00e1491113180f03c0f020810030024a110b0421100710000381441e140c90607000481d818840c0500d4402486803c0001542c090506114074600c5940110802e450b800c0000101c5212003950040540740703404424800703101d05411000825030360b0014004038403202c03003a000301700030040c68000b40119501c41100304d05071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 771065665 1250 771064415 771064417
    0x61d0a18140d020c0a050102100b0a030b0f06010e0418030c080d020d1b02060f011806030204021902010b0405091e010f110a03060503060c03011502010605090a0b0f09090d23 76
    0x103a80c000540a10264010024207020007800c0c0c9a2040b24210800c0c1b02c642d031f0004a0011660300f01c43d0018541d4181e8001031410551540001c180a00e02c40402c00310640d88d02860780251001e80760310b00100e105008001c1684c000c0c1d0031040500310122400301c0460b100ba200381040c1801043c88034a048043c4000c8016640860340d440342658980814086140c50a1440e0903010fa162024004c43d0600c0354242c1c840c81810302c80d803010ba014402c00c9005070300c3c06500800055a004100b15a505061300002083d03018107994500075502c1d08036501c0550410303014151048441070041d00070150808e4500312303900000c3c04007030665981c410303410039403145a22410602d0000c19520544032280d80340020281c40180d08520300a0300201d003402405113600c4142c0781907410400095280403020b050890041c1260341c0519030103003400041c01640c4030680d00c032543c50241902c603030810340e50513403d03c10440c40954200031103902c04098552400d2142c82c944140700d414101d00662040a24218211 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 771066915 1250 771065665 771065693
    0x210203040213290d05210c01090b1504151502030409060b03012c04081c051503012a0e03070b04180501090506031c1b0b04020103061d0a18 61
    0xd11507440c00103071264440401c02c08814070f800c960108020b00d02d540c0742ca4803110b20710003071410151203503a0018030b00d0031201902c800e642c141008100000180c24460681c4500b41d418062614802c0303649116420240a80f200b2000082004200c0c0351801003841100c46041031540b0860006110100d04000240102c000618450f40055201d505104003058106c10001c10060381000c02d0a1046040c6000c00d034655029401900741c036210400070964850008800c019542103503d0700c010090f840061408411072030400742d008019441680795411001c80300d0b1051180ea800611500d224458881e210b00041c590011f0160358800d65140000b0003150461f40090101c00c400c48040040800c49115150045c084407205101908091001c40c1e00c0d01581c0010040c450310500d01600e0150250100300c9803154a000c103194002c680f400c0c00408600309403000ca00182c2440c00014651048e01160b01603000e400c05038003003584449582e00c009202105031140c503072250a001002080740d403890400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 771068165 1250 771066915 771066941
    0x3140103060518030a0e010c0212150901060605090a0e090c060a0f081518041b0303020f0708070506040e0403020712030f030c020f030d0e0a05010c050c060601210203040213 76
    0x7010f003800700c00021000c101c41c1c001d00103036006000e003040309940104c84540114081c05c1500c0702c0400390011580070307850006449102d00c5400b41072011240356002c800d20a90594008000c004c1c0c03145021a85403040a144680c0061108024040500802c1c1426004007500c811a564070000c1000302d2402d40241d010380d804191008030107280541c020350200e82c400091607492980700040341c005060400d40d006800c400d0914000050100300c0c0c4440200c1c5030054500c40303400c10f20781d00c0c9070003035071010004d842d04080d004d88800040c0d00e00340040c03007d058880040c000c07818103060082040719880c00902c00d40451089071000507424030001b500b011024000d0780d5403401300b005102d015054604220743ca104640c015922a410808040180d8401c201c06090108a140f0034240280c6040010140a40f965180c030756012005c0760045d00424040c03075580c054580a640e46401500c15804040701070b0030b800750604540701c2d050807a90095511920003031140d10030403405101e400071190f030712144031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 771069415 1250 771068165 771068171
    0x61c0f090215071e0305030a360c0b0f03040212030d060b040e090732090a090b070f050d090f170c0f0f150c0d020c030904061508160314010306 63
    0x54188000c80410300c80c0c100740d40c40100c94260b0031780ea004001340300c0106103082030f030342e1001c50141c00c259000d41200c114481508035001000f001140005882d82d00c0c901303c559002c2c000c000208142c1c80400c2c0d039450050403103400e0a40d611b580034414bc00301044400003241c00104542800c1007928403840020300361003228a0b40707441c1090861062442c01a08a4440340d01002c0100500b02c410300c628456481d2000d07959021640d50303454500c00c2880207003410780c4280030008100040f0711a52180448501500d040c4481c0d444482054031903003411004900002c104005c1c24403910b070700742c010b403507a13038071070100d11030710040c035884203080c0c9803d090300030381c3c002c10024004582c1c2c1810460042c07440004005031100940441e10b1075a2510550669203030814110b000415401c50b060503a00142213550040d503403100645500398980c0c0c0425403051145190a01c00b15031441203d42a080d203103000d0300e03400159210652082203070400c0241240c1050707265070340d8030440003280110600a611404000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 771070665 1250 771069415 771069427
    0x314010518030319020c0109020a03060b040506010f020a060c05120405011e0b01050912030c06090a02091506031b0904141909050d0e131407020606061c0f090215 71
    0x40c0300010854005801e980240240400036058422450b0402441a40181d030b400c1c0700c4280501601004102a5110028420000c1031003101e1704998645001107800700700d1a075a100056508020275040354006034003064200001401e2a400301c1c84844072800c0c030070b0804014501031404800211411109651621803240c0d01d030001a41040314000200000d10820414000003022405018041e51207031100f4101491826024000c484102d022002034030baa0346003401c48141c2d9541c040f2404c070b00503490340d0300050541403080005902400003c0c40e091860300d370300c10020b0902c3c42c0320842100801042160340f2080d0703107a201d14108414088585001840c0c10002942c8191002030010400303400c0c04201000100003040d0b900038000103007882c0108401d00b50118000300c2441d400c0c180020315124070307160342020707000e003540c8104125821a1003541e00c0c202804a1405040c2c100c1d141303110800300441201885800c104158501c4880001c3e01200b150000f41d0540c031a8050740080364400130344c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 771071915 1250 771070665 771070681
    0x30712050702040509010b130b06090a0314061b09040207030315120606080d0903080d06180b120c2d06120106090f030f02060708070c081f15030b060a03140105 70
    0x20139a01c120003000800101058a01140b04401e8000780c030061159103084020881d0b0740c0388103803001d62401806071401240c0340c1c90303d0b020700d8419401a40c1c440c810703c8000344072041c9160740c10940b40202408142000c00400510000c2c0d040010114189501c0e00c02e0520300d409071011301401000c2d5114004d41c180001e042c00400c60301d00e500650f00c2c581000051038120b81d003200d6480e080300d03844016280e542c2004006030004200356000412480302c540005c4014a00350782103503002502c01c4a2101c00707a40812099030751920388280c8240c0210f40d100c0c1407040c0786941c9540d03050803c061300741520596003000c00a1144ea00c078403420140e1907810700050061076030145010f07001c0d007107206440d000c8500b503071280104104400f50092080b01c2c0040d61104000152040d50040e0340c2c03242e5101c1e182ca8a840c1c1003900c81d00408143da406e002c0d40507003542c1201103030081a03c0b903030080050005041c2191030302c41025000800036a0020008000000043c0b90382201f44090381d21840000307401c1c100011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 771073165 1250 771071915 771071921
    0x3200d1d040612020d080d020f0706060905100905130f120f020307080f2b06060e0a0f14010c05030d06080c10051912020c0606121504120203071205070204 68
    0x2140354059890100306000e07880341000000e0005404880d00c513611042d0f40f030034450380d21034500c0030b140860002c00c00a02800c101c402525919208500a1000c280c403250110101c50040300c803007030b40144141c402c111150702544039980002038000c4204695025440b070314017840c0049801c940348440d4800b44450660311105003052032801d84040c515114507611500385a000700a1802c050500000b00c0f06003c0800f01c043e42d1014120f02d8010501851000f520360050003036101da1000300b40e50680c80c42c6c10340f600140340025900350b904600300d100e0034420404141e9401d901501e05021000c3c00c52004a6810009005803406200000c150b0b2820194494103003645140751074020107000071402d9106410405031a090b001d1075491140c4d5a80e13071002143c03a598000000c8090510010302020002d03800f2451038400c90041c0c650344412017866010300c1e541d6030320f00c3c50460111549000b280010310304150780c491038645481144c3c1007100d00c0d242c0300d9140081011010101d9000502440dc504045c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 771074415 1250 771073165 771073217
    0x3140c0402211312081b0408070603020c0c0402030f01090b012d0c0c15021e060f0c040e0a090209060117070f1e02010c090807030f03200d 61
    0xd1000d50500203608080600340255101e914400405000010032401840c2c620b054200c1c4c11898483c41504424000303098860207443c00c0d00d60003254401805030101d40c8040301d040303c0184000340043c80c41c0c07081c02c80080d00542c2c010801d60245008400261755680017950003059101d040507040e5140241c40c004850305929136a042c04112002101d0f1040010162a000b00c0440018039401c00603080440e034040c04c250b070003042e148400c040460500d503080d0011500404940844e08410307220b514a904000c0003401c225501e920200c00500420891841140c03c40440704803141400e484030b603407005403c000c9a40c610b0302a0717100112015031070039812094000f2000e081940320111961421018180020000c80500c804021a040c140d44900d1070600d030200d2840200c4801e1401c400004d001e8034003484039200088000301c021070000d40c00300c3d04004407907000c41e00c0da00944140e80c0a83c0c00200a420031125101e0041503985a501c2c20b00280c07580103d90781c1c0324080039980e814203641c502d8400f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 771075665 1250 771074415 771074419
    0x323120705280f080a020c04050c041a090d06110c2e0203090604060c0c06021b1203010609050d031403090c01031104081e0f070308030708010b16120905030703140c 72
    0x141107002003400b41c3c1050584541010080f9502c505450003a480c004c00c10f950f50b90054580b80c1000710703002004c1e0140003550039213034445024081c01080c000183c020400d0550b448100b0f80d0714100020382c0360740000346001d2412113050500490285040c20071030b80f14030362882c401e8104548000e0b80c01c4604280001c3c1c1850408600390300f003000345259608c5006000130601030303540506c1e0041c1c1d8021a080704549520040a554580140c200f018481310500d08242c610302c24105902c5c241e11800781078a05135441580c40e210300070300c3e00c2d040014020000340281c0620110000b900008505800103510030b05000c001422410110350005045400d034842ca030903200000d00003800504000305001c040385122514405200c0c802c0041141080c038200d02c01c00292207280000001c101c1d003072003c0d40c130450158807002040e80e42c0d1140d40c916882004000c409100d030308604040001c001041c401450440751405042c2c2544801c0800e03c0d008650700305a4803100003405c9030008c0402081407c4400b001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 771076915 1250 771075665 771075733
    0x3040f0b0337091b121a10030b04110a0801060f060c060b121c0c020d02010c0c091517010c0509011409090703051603060323120705 58
    0x41009403110600c0c40c1c110410140c0b42d20032008880b141c502406078950741c00420061030f219854840c0611205402441c48120408000250400c0250080d51035035040380304040364003c682d01910080100401003003000600c8000400410003800b07019105034070272004000d410b14410b04101e41c03061581d101d030b01303030303070f04002041c02103400b07855078102242d00c1810810a006101e19140c00905101c0350255082003c2c0c1c0440e40e50544006000700066040031031900380d08070768020889207c0300341040650001c030000c0014005500c501040d40e1481c0c0991005500c00762940301031340948000602e4041d00850b0402d040c441c04c00350448141244810304000c129011101d0005040d5005407441e03503040c0044221341d8407071004503400725402150014401c40076440c10310f40c050000d04050ba13100d04141c681409680b03209000c1c1c894030055980094000c0320403040610540442215a0071660301401403500c0c00c0d01840080000c0c01049105801409008241c454a480313400c09441c1401c00d034000f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 771078165 1250 771076915 771076921
    0x6060901050a090b04110a02010506090c0c06240301090c051314010b1c0608010c120911040b19080606270408070c05030a0b010510050a120e070302100203040f0b03 72
    0x1640d4003030b110440c0c105450104618100360001402056198104481403200040c00309034194107500035449694212100440bc1d1950710207503065004d00041e00c003440e8041320128111000481459481e403134190508000e8041c0540400e00b502c129031400c03611030408c610706229624001e02208605070004004110300d4645840d070808034141071064590029000030450060041c6031084900d02d01c02407010302440b9654a2500d009051015450740000c0b0326044200008845001d1019096081200310751780d00440c0c020803005002d50540d00d0b90122821a140a140c60401c40c8040141543c502812151418030180208100d6200c404100902c0881c0116105100d8144da02d81194003c0491910340c0442e28091085141940100f0361510903880c0c1c050403c40001400c81c162082a20031044000c1000000d40d118010306034400041003094400c4104410b4541c4583d04021243e001c640c60f42e0340d04d80125400120007084400140c200040c18804081e40e0140c04c0d0051040815080c0303189 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 771079415 1250 771078165 771078169
    0x6050414100b0a09090504020f100f1d060a030c11011a210d080606040b1204020a05010e01270b040b030a0b0f1c11090a02040e1f0b070822030201020606090105 70
    0x82d41c002d59104646c1c881c04a000d6403079a4545645420001c3c0649840c4100c2c81806003900fa0708000c41000a1003107001c22104955101058130215006440c007130410407480b00c290082d090349400c5c14200600c0c0d100c200110403003401980301400541100000100034901480080012240c0c41c0d10300040406054003e040d00042c2c072094030b499803074602416220034000440c5803160b5803011200c41008142244407104c0011550700940c407ca48416000d60703034000544491002c9018140400e0191609655000700115486d02c030301964140310b2002501c400c84a429030b08103411041c0c80540102c100000b45003640308582c000041141c05404079038102002402c64410b5940000f01b00c071900402900f0405030352810418044002c00311403540c640401000c000350800c0c07113040741603044080415140d441e031502070084504201d41c40101c4905100880301142e0107600103d9412004220f2030000b90152800503c1100c1102d000d00d505900d14000280f6144026040c2c52055030340c140100126 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 771080665 1250 771079415 771079427
    0x9050706120e06152403010605070201110f060f0a1806020706021e032e150c0c030c090b0906010e010e030a020604091409070b07020103020d06050414100b0a 69
    0x84803a454011214502050100c014004001401070030b44102c405100c00140f400e5800312440c942595241d0201c54501403505072401d512103c0f04003d0340400060059a225000803c00c07280181401120742170b1021003e4604a007000d100505508401c06110681446c482d00340d421007580c49050145c0c0c0c1c40c502000a0b6802262001003403203034006110000c0000540685450300e0032040b400d155000c0143e42e0101d5640101d0f51404411900c0100c0e080f01cde2411000000103074101c0901604050510b81d250a0000c041e20100e400c1c424111038040004070030200300c80255100300a4410000d01d003801800a40b2301518045110703801c80001c000d00c43e60320001c0602403617000d02e0607d4001d002c8901013170401d80902400f03500a00b0000d008281250940c0241264204000e0301c4c011544c0e45030b4156899000314010943c89a000300301036070140d031107900038082640c4500302c00186c45507203400190441d41004481603201d4107600030440201c140c04102c1c8020019691200d180c923000203002460 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 771081915 1250 771080665 771080669
    0x1a06190e041b0201051807030308040b07021f0603060c0c03020c010804080d0905030913050103080706020705070e0109091401060b09040203090102190507050f0c0a06030c0c060627090507 82
    0x40202041494800760741d03a0300300000d4801e486078040c00084040314002c0c082c0030100d41d21882441c42800d010105000084d14500f202d0700759480c031116449540c0d4481038503c000c1d1a900462042c0c1002c5402402002440700c001c2d8008400043c42c18558686a0261140f5a100700d051101456600010a802141d85484100f091800811681d00c40c40c06540b64042d40070940d89840c5028000c81c10000000014030896404550441f090a2095200b4050340d02c2400024040c1c5414000c05d000950550003170122329114400752050662550703240a0198401da10030010107031910768600520240412488041003400b000b0300001d8102580d40000348122150705001d59030000c0055000002941079070702e1128064035001041000c00001030413500700283c240c030180a00043c20f510108002000240b1400150101412a29042098006110300c85888040c050308a009000050440c8919000361561300e03404440b0481c010390b002810b400f07800d00a42107030b180c00d60340808680000703a1801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 771083165 1250 771081915 771081917
    0x1140613060c050106170703060501090b030c1003061d0a140f1f0308070614010603020301150c1b3215130902030c0a03140709361a0619 60
    0x5103107121031511500400940c0c1c081442c054480e5516141d1010105401f811a4002c540c14421a45c031001c84008842d850205150700d07502c14103001c003031410649001010b0001c0c1d070400092140d13a82d05031455200a038135035402160070803010087d40081620940c80e4000944c104034280740b0b003d110081412a0160036400c0d84868800800074103000c2041c09070240d070703200f08000d45840441c5800c0000d00301c909000301c50f00292a0000c24450f20a00c2981c0c100c403003001c11918417800d401c50a441001c0d414000f0342c0c1c100c0e002c0c5403081418200b80407800040071011060b07448040144038500c801d01c600c2c0c4140409147c5440741e120140e554248115003007980140c45650390403c41d44500b03c1907090b5000c0c01443d4000710410903020580c80103030020741f60070788041c0601a90551a00f8a00d079049551001041a8400030300c0300903d002c0c0680003182c0d20340d6804110a00c0661410101481e44000c4140252226040c0c444800d0a44440300d005405070381c9a41041c003058007209945c0c42d0403e00b04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 771084415 1250 771083165 771083177
    0x30210111f0603140a11010c080d1109090411130c020303040b091908070b010b090618012601090b010f140d0906110d0c0503060d0611070506010e0114061306 69
    0x1901c90a45034081c00007954003c00940403d501c40c1101c1c0d46a4602c050240c4040e420000032640550140c2c08132004140e109200918164103070030110014200c0a80341d0401101c00c0c0700484440d00c030040e109001e5801410f0551941080008211a2860210341c440c4018140f4100954003a000015690095446044101195030746143e02d844c1001011301c2d03681e40904020040284a42c001c028207441c1d000341a00003c9130380b660200c0c8464816540501d4100c4020484076141003945000303900d0100b030525102e51500301900c08400403640c842101d440c50350740e07440100001c0ea060301c54030300e03846000e0810700040203d21801400150600d280c01441d40c2c4000ae04c1410410701e80d01084016600078420000b0b1441940840c1a9030844e64141100501c1c200c1120b5416010700305892161000a142c1601c0038100c5d55081d01828403001c1e80f0148130414007030600018010303c41c1c1c1c0d01809c4007403034850841d854041d00c400c200e120240307218000c0c0000c114060300f030b100700346200d0203880c2141440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 771085665 1250 771084415 771084463
    0x15060c140604080d0c0f0f03020d0905010507030218030c100c06090f0b090606030f031b03042301021b0109090b03031c062603030402100903050a080403021011 70
    0x3040a4044980046545005501c10001003141ca28007804254000000400c10f040c084c0c481580c140f04080711807808658118000195244260018115200702c00d17004200d5a502e40d803080e0075104181c50410200e43c002c12454600c00e1982c0300680343c214220018151142000301090342c82d40501010f108100140303c8000501009412029626501c80d2020107a4030550503d0050404190b8a0524600070b003000724505190000b07034801140500805107151032444000508079031422115007100e80000c1c040094406070070040005580c1d20031030030707181c03d407807a000081c140036400a4a80024001e140018050390f800403018081c1c52014100080c92001e10000a03d18025000c50144400340c200c4922100715158100c074089820f07486007880341002d811f46401d05942304000a018580c81400002d01519203556a40c0003000e05007010308045899464070f40c1040801e44041d9000c078800a42007046050941c094031300c210381450a104051907400e03d05403581a08074020700303141a00480c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 771086915 1250 771085665 771085673
    0x3161d040f1707030314041104150f09020406080606031e070509100306081204050310050c07050f01091709211c02010501030c05030d080f0a0209090f0f0a15060c 71
    0x1040000d0760300000705160221281980c2071580c1e200980450009003170420140070070744003e00140c01164005800d01059541c002403000600c0c40c7c1841e044e800c0740395180011500d524444e0718024100e17118026079074030708101000d06940300160030785001d0001041041041e4513074030722016207841e10701c56200103600d9081003200e503270140c1000c0784d900070144280303500350070b030181c3c03000085036025425981d00110400b0141447d0203a44107071901500810032108550419a000552041100c00700609000341500e9007450721125903020400d0b695188c094000707001e81d0302c1e2144000c54041142c6450801510302140a0346e0031040c9800703100a00c0185160048400d020124403a403816000416005210100074080c00f001e00c400e0321b242c1010f040100341401c01090100008181b92513006d42a121440103507008007000f054160443c2d4240596070700d907601c45c410300c1e01802c03032918124500d0a08400040f501c04c0064024042c0c4c40c03405100c2088002d80191301d00c126012400c04880b80200380c14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 771088165 1250 771086915 771086933
    0x90c0d081e180306060103060b0702130615050c120901050a1b150c030e0d0905010804031803140c0a08060604110405030f03031f0f050603040f050f070503161d04 71
    0x1c80915100404601103441482107650540e0701c0c4401c8040390703c0c1c1e4076508015801c44403240141000b50b0030800c003020150620041c03281104000c0040010007590b1410610010001d06842c400002c03070000b40110501c1e0100592081d0415090b206840c203d03041d40060180e10540c0340910900029402074444910f90f94003030001180c20a4002644a0000300c2c000e005040070011080405d1818050301c030b00f030a0005240d40d100c425074540441c1c86042000544e01000c000b84103c040200c46040024003850903820340000b5072048075020721040841180905002040c2c1c41640180007028080110000c009081d540120090f900010642c00340c00f10300090744640c0d0030950b010b118030001c100c1a00702c000000d610803031154001d41c0341501002c0070042c00c804140b0440751301510821042c00989070403402181c00520507007100302004415902c1d0750502c09008c44054094100b10800c1000d4201449000d840c2103031141455241030400324000e2480c4071018900007084c4400c0002410000030312 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 771089415 1250 771088165 771088207
    0x41221170115030f1e0c08060d02040902120a060911090402010c03051b120405011b08120a33080115090c020c0d05010b190509040605100f12050105090c0d08 69
    0x101e005e0250101282c0882a03461000d9101d9074264a400c180100151140107544d008030ba00400759000380c000c5408003c094400c18400307980c0400b508285200e017110400c2005003a510520b00480c510102c2d00382682c0c01401452068040c03040d078030070400180ea02c14581704800f039250601d5901ea80d038810344103160820601c1076904600c600d01055840c805002e001d0421190b00743c0c0c90104400c40012032540c05107203150010301301603040c02600d0701d051001408a03442a110080001d528219254101d401e020390010f2260f810240300081403a00b090b1402500540704200007071020140740d802400a1540038030600010300d517148030701b00c00140300780316807603003801700130044a00c1034040c1c00e0942c001e21b0003840c0350717102d8490101c0724160b00e1802c42803423085450082581c240c0707650f10f4596901405d0000d025650488107044007260905030306440b01c1c0902444480641140b01c1868114212074018040455a6201c3c41000c00540d9880e00781c411b5883e07001c01a20386841400c110202e040c0524 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 771090665 1250 771089415 771089441
    0x91f0b0a030804081c02100209060706020304061a0103290607141609090c12020a0e19050c07020a1802070606060e03100e1b0604122117011503 63
    0x80360300000340011040030300150b071000380981751401c841c1505065580030803a050005a009045604004941a40905101100070b40703c580f61242c9582c0300412644100c500b151b80301d91b5010121660440080c1b074000448080c2410001c00a040aa40c6400c0841c0c80310104400c00c03581503156907440e00c20942d11131642c800d00d900c940300800420710b500e4403408181160701c105c0904d0000796440035070140c94180c64119000707594280c20008904901d519040c3c4c1130340c01080720000000c94038070641800380b254038a03034440117801d404030715a0400c2d5003001e0800c0000200070310001000d40d85690070341c0304445100f200005904101c6006501a000b503d1003e80414546140080d03011380100c004208008100e05540c0c101e4401140030049410040c86580b06600030241a81148401d1941410a01006140b40d04141e070390301c02440045040041242d1400c080207044841480c4030868072500655810908140002d070071041d07043c107005100d1070140424246450942070b000e9482240c8500395 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 771091915 1250 771090665 771090679
    0xa0602070308010314190b070c050d030615110c210d02160b070507171204080c01170702030a0f0c060c080702070b0c0304030f080f03100801060e091f0b 67
    0xc03908000c1c2400500b48800e98810340142500d00389480040f5078030750303903220300404e01a03400d1041d101e103807010000074038120030310440c4144100800c0c000c001d20380070018142d80100d051400d1070229082c4400041c2040c06004145804407008180402c02c8104000c090300d03030b4116111080d40e0f42c4d021406804045081d4040c0305400d201071940460496400904c0741105070304540e81e8040340b11103204201000e0488e40101c902400740084007030140c40c4601318141251107680a004228469612030750015509500c8485600d0080d6040f612080409c0c01500c845022403500308000f94803849002d181d042000913000b80e45034502e024840c00c00c55103402120400040c00c1484000d84880001e9601101521030304d000042d214403800d048580c0301c0d501c8000380d801c00e0b00d16070f11019014a800e400302c41c10a018080d85880172482005035100700080300b100c080c0c8900d003030520340c01c451081d04a11a00091442000300d90304002494801540c2c1d140c1c92803505081c5030700c006000308421105954003441e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 771093165 1250 771091915 771091927
    0x150a03090b04060e190305070605040c05030106061e0306150e04020f0d0902010e0306280207080c250e0f310c0f060e190f260607051b0a0602 62
    0x40d0f40d41c0103186a00310503044540a00701c0ca0704288515544010040024008000300d5000400307513000241c00c94032900c0103084240e241c8001030700351245508281c0014003480c0940d04456529880c250b82c0305020300b420081c1d50b041000d60848240e490909000342300c03a5640c412007a450350303412561080d0a090b0302985030786d00521010f01a101c0d1000a80c002400c0c400100154603002c2000e40c042e424140c1e421412120700c903a402c7d50140d80c04c041200807682800b00034085000380004214004a1002074105603101d10f45401c24500881002c8115860b0810244904880c40700d0700380e00110140004034203643c03040980d05104810040f0283c0380c07039420180c2d10340702030310b62186100341e48152402d4032142d444000d8901c80c581d041c828000007400188840f8050704149001b111400c0d00b107440c0125072511100510b603954041c0d40a40d90044086400c08000346100300010700c1c82d04154040d040030306003200002c1031809030884040d251409103100d0041804204140e0522550100043d91644 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 771094415 1250 771093165 771093173
    0x3020301110405040c140d1d0102161703040b060d051e06240f061308060906040b090c1e010c1b030c05010c051005130b0a0c0f030b150a03090b04 64
    0x30700726114480c007071410700e4410103070f086c01620344100c801140b540050038101c0c64122031024280d18800a55081640f042401c0096820b000620000300085103028003100c040c81c040c540000144001e07800000107000b03100c00500030f0003d058110f00112001d4252803040c3c20220308045043d00d02c003103044010400c07c0c1e208400481c001e4442c42803040c0901403a25070f81d05600480d10700680c1540c1c80072208100706201e11b460f40c0a44000710900d60b41c1516207494030801440c0c10005e442c85038043c0d200348100300c01c220340041000c0d4800c00d80b002404102c2011008911150a0070312117400c1490104104040340e4410310f80701780c800d50020085058200e00603181c84200e0030701e01040d1606000d84074040fa940d4000d4001c1000c01c1da11200920000d4036127021030005141c05031000107402010b01d0400085160b13460001c0c011004d6a1001404800160020b0a104100d644001c10302d070404004015a640f00152814102000140c0d0b555540c0c404400320003c0200710f42c0100260041000d02082c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 771095665 1250 771094415 771094417
    0x140403021e10020705030606030c0d080d090f0f050d050c06040b06060c010c030207140708250e091501090605060d050a0e010903170702190f020d06020c0f0c092a040302030111 77
    0x842c0d01b90150340b4107480c1c00301803644415140126030340041810411500048940380202100011030800280c0c1c800c00e40c0d0388250351401f051007a600d4084807880a4144281489503007105029414000d01d05200c8004458448400810282070740d08881c0c00030302c0300d803207042c00c6400075118000200700600d40b01c074000d4020340120b10160b038607440c00200c1e050585800540c40c0c06490360803000b040b506922607400200300402102c40b4204811482000404042c81c468450148800101802080210050742280c424059211072403480c108441007025481d00011155220700b816000314080d44c9181c5428081c11280c0c03118036142d031034521203505059008032503045030125005842a03d450300e40003203a403040e5810b0030140ca80c144020400014040048641d0170900c0078111702e580103500e450700b2049810041d035002594200d554400415542031100d40c1d41c0e00e030115a03003085401d0402c0d81c61060209401000c0c07081d8000031b0b50302d1544004a0994004590050007400140e0b0302e04a00002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 771096915 1250 771095665 771095669
    0x4050a0e060924091903210b0f0d020105090d03051e0403050607031a010302070501152d0e07030e3d05072a0204020c1606140403021e100207 62
    0x1e1555038004001c951000300c3d40143c00c43e50080031031408050301d114590702540e00480600440407118000030800994100492000741c1000440305410002c0c0321808880314080391040f111700000100507078100c0b0075203030800b0080d01d24604803141c03441c00341d41038842d00014290301c520303074910400740360349100081041d01d2044003903035010746a800e019003d072500c500249205103113000741070085511a50282c11254001c10020079240302c400d0400503071502d250030a202d58450708075130091840340c0d81c16092800000000d59400ca070301c0c010405600035000340c9200304040d1607030000040410100500c40c07605100345001c0000342d1951020103480d2082c0c5c0c11611011503003c6007920744502038441c4a2042c0c41c0d9407945400072030440100b00c400da0350003030001801003021341c040c000340c0c950744080d080c00301d9001c008115080d21410341052400c46a80082d082225804010008980d80800d40301200e0f41070f180c03250006a510100c140d49000d80e202c6d45e41000c240d0f85aa00044e90004802e01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 771098165 1250 771096915 771096943
    0x909142719050c09010614130b0a08010609050f0306060616020a150909090201020a021002010e121e09150d06051002011d030f070b0c090d0c080c09040b01030204050a0e0609 76
    0xf44603002c400c02c1c406070b000240310b40c0020411002e00300c41a15103450040550b07a020b01512441151205801800f603044450910b00180120b401489a01d4021542c1c401400084800c0c0400e0241400003e03600d03030001740082d008075808904c02111803500030300204030542c010202d462841e1910b06030825402c00c6030081d800101507403c0000c4900305032042014464060f4050241280070f034080c0700808150070f40150441d075030341007501c13003408050010321100401c0345100795484540d030710003918900050500030255441008034810590350400c2c044280000e661072240c941500902420042007690300c2690840d6440304800b104507419071191841440703005101c800e12605075032840e945d0140024082c0100d0040000d24045041042406da00168505441d45442d180401003203076116501403c80c0c004095a9043c806e031041480321215035581541e050324549401d880300e40c9002410710019020301d51f14400700340e41c0b12080e0803102060406c0d600301c070024103102382d507103a94004c000c000030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 771099415 1250 771098165 771098173
    0x260405120f071e0506030408030c0c100c050c010f02040f05130605130609051b0d020912160303020f01110403080304050309040908090a050118030201030507050408011407090914271905 81
    0x11a6605c2c1503010360780200e8120745018203660318403881041961000b181d002c8544190003040104500c50302511006418a0f138038aa150928841010b096404c8031811810090051200f8400c11030f08243d0b41040300e0701140c1c14160344200f98094401891150000394014002a4074604440d5081d0005011614050360401c102d565003003211080401c0c9003030f11160a5410060b020000580780c02424a81e0780052201d00d0301d6210042840c030b082d4054590b42c486d120140700c20414580c041c40311030503460042c0d0082c00707441d420100d420781c01c0c80740e8040280407040210104007230000c108281d41d8810f40207481001003500d1805e10002d00c0e0010000548148152200810a9480307802484640d07281e6080d00f040c503904541c0107502908005019404201081c08000703513164090142035030900300c840014040d41000c19009049681a400c51001d9505150384582c480c407182131400d900044007a040410b01e005842108411008581c01a005115401884003010150b020035854540314104903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 771100665 1250 771099415 771099419
    0x501060f0201051e1506032521090c17010e0601061704080304061b080916081c030f090b2403100f0b1c260405120f071e 53
    0x40303090f02c00c21100c080c6416000644001e1030003101c840560015902e800c0c20840d481c8000108445410841d0110f80c000401d0811283c03107000501410401e4140c0d01c0c00c090070365001c100c10707140c01544d03071103000e100d82d0780d503c15a044c001621000d1014003d0b05803021010940e58503000d0203001d03c4003210b1081d002d04000000d0950003a01850070010080da054252980c0725101c0f22410b4100500684842d500d0369107910800400021502100d02d05440c2c504841c02d0589050b890f01414120a81039080510030500000e070700003d0395444c5003081030240502100340f103000c03400392401301c0e59000d60f542000c00c10001c000300382400a10030301300d03440b03071a0210901e40310414440c2070184800c0e426401100690030440201e820071440c160701100040348284604021a00418940361444c1704c20348001c004000300310b010b01608901e9980d030b4550105010590303800200910852040b20f100b691940b0110401d0582889100c0d00c0300e96220541d10074654841456400b08080800780300d50b10410000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 771101915 1250 771100665 771100667
    0x111e03190305060a03110f030a080706050a020a0e060306010c0b010803070618030f14090a0e0906070e060a20030403060b12030f030a020d021b010c020d0201020414240c010501060f 79
    0x382c54030420b0010100701d001071840d125980001440c0d0445a0131079194542501143c804201615081c3e102d24005581d0790543d04015003150800362909801d5401003206581c0c040c0e0200500000510440d419030307594607560010b80b462825444003c200180c80000040c03007400c04800381ca0024050324042c000d044c4111103039259070003900d42c0180821801080d500344240700320028a403909401c22102d14003810000001c02030480b95205143c900980010418100403e00250350805020700f00551180c0c2d00d00006403880c01104d070441c00704611201081c03000c40210105819100b00c0406583d5915241d042240c05405002c80660090034023480002600b0300c0041211000b07880c29041a082d03850b0402484060340c005108240c82035001d02c04950264050039400d800203650000002c3c0c041d80c41c81c8040e003481207500150096920501080109180002101d074031088115000100400f2203641c100601d8080a400362403000041041910340805500c214103a42550300d8100104503150b80c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 771103165 1250 771101915 771101921
    0x33e0312070305240901260f030406030f0212010b091315060f0207060c0809060f0d050603101406090601110a030e2115190c02060a050109020403080a111e031903 71
    0x102c3c640210401004101000042031004400a41c0c00000305aa00260107c61300e0305032051241080d40e04002020410260544034191455401c540290308201c10380a014078014014410030000da2400100070110707541e4030221810205444c501040001c07500c030040b801038065402090007244010b805604000c6c00040c10408480c5035a42d002d0401c0c410b5510b01c2d10580001e442c02c1e4209805104400d22030702e800001c0c00b0346508503e8009120314001080515003210001549100d0f49081c194441c6071001103920b03544018150382d8000380307844080040310400c1c0c44046042240c01040d60240030154407002100c0100002c80e03824005814000015003281c1020424454990000e521450764140300c10325154410300404120358400d03a0940300209a80c0c2c010b000100503000803041212841c3c0034411180501601c4c04114105425555940d00510444c83d4060a010703034400c030311000b14002c01c0000002c088140b0301554039244601219547d030013440f050242d180c0400741844013980f10344 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 771104415 1250 771103165 771103231
    0x60605060d021305030628060314061609230a0e04050f010c0203030c071b03022107090903020307150b130c02010b0409230f060c07033e0312070305 65
    0xc0e80380c030085201c02d011f01040070341e005903000d800c2e03201d40c4000042096042845206400e140c09002c1c1e914040714040c50542c107404445c0c080c0030b001c0c00180308007000d54801034803814020240c0340200c907c3c1d00000b01803464030f5004001088030b0008010800002180b042e405007480c1c0c009100d130036078212003641c680c00100d54803081c8000910840020810003542010052100648500c10356280c2d00420150244003400c0c0050040c0c85208114000f0104501801841210410812440242d4000b034070381c4100600501280a11290a40c159000d03500018101c00010320711011050341e00744040c0030300070254044c4095403800d040c1d0446802d140c00703842c6c1a03540c440301070780141d18410503c1c1010800c01d002d0081c036103d503440200700c1d15410084036001e241d81051480c4c45030349610b001407410070710000c0440340079400403007000701c1c0b000010650002000d111300c0c03000780d4001510507455070040c0306000c0c0c6034a500605000317125030150710513401004c40340181224800203038020000483c0ca4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 771105665 1250 771104415 771104431
    0x91308031306090605090d1d0307060818010f0c3018141b030d17040f0203030711040b04020c06190b0904050d090608091009060605060d0213050306 65
    0x4000190480940d0101c59000a100d00300000f8110301d2a204d0303d089500849103210303c0c4e84511a00b010407a005039050b100c0154501c036000c075440392080402e856100b90320602d802e0100c0f18000c5420720b50034028800d03221510300000c000170492009008050304900c1035410110b034401503410503640c00480000e00d41d00503031030504644880c540e40c50b00240014006003c01e05180082c0d91b0006040e04099403440068900500c151411800190314048001100910070340c00960240c100d01d070030003003401c04848441d0000e000307030351035080080761030b0b004000095240c0000508101006481905480303803100a98041040007070a8041c40100d1149884a00d551742c85840000d481c9926281105401042c11802050000407400440c5240d841540d04403001c1c4c04c420000301c1901d80c4120365500a000c4c038a4121024140f000b80b083c1c441e030201d10170741e00b120317180c041000502026030040c01c000c180240c007c0741c1c0d840603111250000c1d006500d409440c08100b94000900340b9000800f14054448 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 771106915 1250 771105665 771105667
    0x140d0b18070314090c011121070b06030c0901090507020a06020723011e1e0516030b010201060f17120a0507030e060403080901210606080402030c010f0e100302040e0114091308 77
    0xd8500644815411841c5803000b842030144608c1c2402c0c40c80d5445e143c1d400d00080c0c058031290701e0720300600100f400400c0b9074003a81c043d0312441d1031640e5020000d03045131200440000c40303845c0e050007207003400ea800384090a51400054110304100c80e50b18259244411030b0f82006c8070030f850b50315150a0b01d000701c810196000c01780c8400226002554000d4013590700003005030301d4050303185005c04190354003224004510201d0600404200b0b801d4022903104d030b00700340b0013000030343c0c20a001c01e24a0b604030b0041c01d81c1d950603c11004c2c0b210380c04000340219284c0c8500c10580340d442d0641c0040c80795100c01011000107e0024000d06182000d00c161030540364007030b10041c10103100c1d500450f4001d00c0c0a181c20b070303440520018882c919000384280c0e00a07046603a640c0c41c8d02d1074180181460b20300c580003001d04200030842403401060b4032000100d0360708004c0328101d51003001313504120003a024503000b500725094204000950907044038542040d403107003a82c0451084e9281c0001400141700c042025040e007030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 771108165 1250 771106915 771106933
    0x41509050f040b180307140610090e03071403120420040203091c050403060207121409010207170309090f0901060e090c0114040b07060608070510140d0b1807031409 72
    0xa0f940c24440c8013000c0500072a400d00c2c0a0307440700d4503c0c85140071f01000360303082001070003c0c500c24209404c014202251050115041c2d0049040d0b4074412482c0180501c000e400381c0c114454400c4c400c85899040e0342403040031604241c14801c0c887c580071503100c00380142210070810203050a0003541d1140903404007400415460300308140200c1c0c1021700001c2044020403010000498030304c042c0500358040e004401540c50b85040c05810311024005007031540c00c1c18043c1410623a40060b24200380d0701d01c243d4900980d2480b001c602c1c030358044c040c64660302104202c1044110740408060134811000307400240314071a514030078804450400d0b10740804d80e130405088213685501400034250060081e020552030960345003032400341a00b01d00412101551a0182040007160420948000d40011034940020003162100a801c0c6102102d4041c41403101042802c0324810303035071212405d11405400401480505c001740b081c0c0d0041210300501003454844410543e140001086100f4020b60b4002c0c65640 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 771109415 1250 771108165 771108181
    0x1b070806090a050c040e0708060c03060a060e060712050d0608151f060e0d0606060203070314040b0d0504080903060c030703060905100605031b040b042102210309041509050f040b 78
    0x584440e01b80110310403000b00040401040051500c6020a00641c9499061500800046103180d40c0044100f00044441d86055031307404007103800c07499002c814141e13039140202d0240c426000c0c001900180c2442c0c90000207608401280300800c0e5458018008480c3e600e0200c5c84140c007283c140d0a42d80b05a450b982803206034021500101c0c034071001421201502100d6132980c0959440d41c003e407005030004107580702016042a201c4a285540301012420503060240135105405203c4d00301e015a0b4640d0081401e000c0d00c20101e566116000d0182c41c2d076858401031003a00d40c1d0041d248100001e2502600141520702c0b403182d24003480c40c4841d000030091400c1d0741280e1680000e04290b2001030540700c0400d00d6246100144006d14001060f01d4a035480c15004000700b18580c820408810002c0110384016500d8041e424042040c0020b00304441203943c00a6280d8000c00449513002890100070103054040f4144100031a170442c01c0910203a07482036080340e004402905c00600011b0780e00003080e10a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 771110665 1250 771109415 771109421
    0x60603010305300a030c11070806060607020414040605061201050709030b06010219050c0a0801180602071a010b0d0506010512060f0d0c0b031f2301051b070806090a050c04 75
    0x900312006401c0c620045548604165801302c4a1500882d07035900d0312a44e080d401c5440065540b02c000081c020f280d1610500c1a19810004e00030b41c0302d00000248581159200d0780101c0c062020641241141e103083d1400000502c81070f507440d0b1182407144200d4003e1079050082074442c04850f9500414540f459484004104005d000c1c039043d0f00500904030120f400b12460003040700d0091008024184c1da19040c0b00c51220942c120807401d90404141c0041d190508884c0c0c0007080d801500140d9a400ca4244000722141c1000301000035a5904d000080c0000c00c28050280d460b81205e0400032a00c40c0401940c0320310601c68001002807400c00040c0c40b80c5070085204441c1c40003e080b03070000c1c40b1aa42d03007905d07501d41500304d41c45540e030110620400d62091140c0103074211a82c0100d00e441800c1c0002480d0541003000e203418503522610031285580d2060080e1000303115400481150040e04d40001615149240904085031144074001801c085000406281d0306030004050700100780074109000107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 771111915 1250 771110665 771110713
    0x3909120f03071716050c0f1c0210300c03050106080a0e0f0f0318010c020d080a02191202100c0c0b060d0f0b0a050f06060f1c1109010206060603010305 66
    0x6006044c480c00502c00d5003c6104820350f0303c924003500b4200405c80400c4208551450b05600445180390103992002c1c3d60740d41d9500042d01160740c0444460f0412017140d07900c0c09242c41100c1440d400d038550300c0501d081007080001c16944401802900c8140000302d00710740c0c0900c111800640d00304040b800060980e0700c0310401e41100400d0f0f60bc51060403505500e444411031044c280c41c0c0c4009070864045036580440c81c0b00c0d05091074404201001500010220704000c44c01a0400b203000407800203d6000708a03040052090f901c4142d007111003810038020002041006001502400da400e1b84800810320482c82c000b4816201c1d4640c048581c2c0b161020030750700801c07241d0040400c1d00c448020503c8400e83c48031240c840d0542c561b09140400b1083c0c1030b40c0001d040920400031400c01d100c0e250f0347c2c2c00b003a1061006509042619040381e151412042c54202c2c140c90a500e182034501c0d0030481802000b40700c000400e070201c451985604080c004140310134800500035810491101d560a00385c1034000c15 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 771113165 1250 771111915 771111953
    0x61206090a06031b030308090106060f1d0301050709032a0918020301020301260303070f081e04050f010c4508060412080405063909120f0307 62
    0x41c905440303070340e500c4808950112070b44c1c40003c09881042017540c4520b46075441b88020009001c00ca00c0d00401800c0080c020200f5802e0103140c0c40041d50554400d0006450364400a00038400c034140394201602041080c00300303a07154100b500102034a200c0748481200b03285510a00502503600e40700d842002060744104c9235541d9045c0011000c00f5075000d00241d0f01030004107404001c5a410303041c1507031039180c52075001101030b0002d10030005003681165240060344106e0030f11000c4e90750369480300004000d038551100c4110080000744010b2180000b2001102c92901c0002c0140c003580d00002c1da407010001e180c0c01203803183d424241c41c0d0858081c1507071035191000c4400c045808880c103000310069076aa00a8991584410100400c0c031508483d641c00c840814202001141056265280c590310004c10081e01c3e428801e5618813280f507514244c1c0f81e02c504d00072904200d0014144001c00580c000926103224985c0c0000a40d2244404640d4003029010309009502d01491980d4005150395011036050f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 771114415 1250 771113165 771113171
    0x30c070303110a0b01140f191a0c010e01090506281a090a140105101209030909020714070618090e0a020d06050901050a06051503060f0409120e061206090a 68
    0x740020b501c0c070900d98080c0586c40f0f941900703030340300d10103008520300b9540b5003510512000169401460f406840301042c0c407880060a160902e035036000701128070400400d6012903107441c007081074951041d8082203440d441202500c0786c2d901c40c0012400352002d1a489080c0d030b19041c03800d6007203410b0340f80d009403401000c6204038403654244400180d01c0c00700c00c60b903860398241c480c5161206040010307201805404201c8509800e100300c1503005080c100c510441315403266580001000749401241150020100c0c284103554949007450038420761310003500754071880d01c6218804a84140a0100d851080b55178610178840e03203107070201c114058940c80396080c00b03074001c041035030025032111083e1118a600074040400d042c1800c0a103a400c445006042c1d4120350300d0404240455510b01e521030601b29107007801c11361283c540c04001001d454002d40c1069100d840d1107240c0e400c200150040b5000b480003a22010750740c51001c828400c0a104003000360b544e4400e81b9000810368900b100006400c6003120f2000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 771115665 1250 771114415 771114433
    0x1403090a1e0611010f050702060a0e060f04110d020306131106070308190e0d0507050f07080304180f02130503060c0702030a0201030c1101110d06090e03040e070c080d0c030509030c07030311 83
    0x11070446d18140c4481c4e005070409008c0100248035030184282141d2050000c05285c509441d00080912000d4001010550b902810401c19901d00721001840d03900202550b2050800364000c147c0b0b038a156038226404c1d038201920341074502e08401511101c540580320b01c0c0d200d43e00d40e94010842c20b80ea921003c0280e642e18102c20081e8000c2141040c90301e080e4940e0359443c0400d050052a01d580e51001c012558850034060201400220940d4122070390080030ba0003400784441030101400c0c1641d2004030441c80410461107541e61005008100c800230360648500e500d0383c88065403540b040e4440a50103912410341540103502c2a480b5804a10f81480d00298505d1f81298541c05d59100c000106907411020549240c0395185210b58002410300580070400a880341e40316580341c0c051881080014074981c000968000d0060028424895210341500d0341e49841411134002000064480c90000c2e15010024409803000000c84270b1207002c20005040392840c564080311a01c0700c2c640078090602500300b003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 771116915 1250 771115665 771115691
    0x180f06230307051803010e0a0204051b270102060103030c0f08070b04050a020910050a1a04050a0b2133040c0e09090d0516060204031403090a1e061101 66
    0x756005035000d80c0c5080da140c4c002c0c090820b045110040035032099140103c051a19500020003030384407541924081029500d040e810748120b91400c46411240c0e80004111080305900c1c820410a40001801d00307058101d1900120b903500ca09003c003c000c0b6080c60a01030100360b0410310006040e05c03a0300303524a8180541e0b1580c44014080d50122107552040040030114680f80b4062640084902c448071207091422000580302102440fa41e8050320421508000c0d00c807104080310050000540603100d02c60380c5506651065000100e001c02000306091507614020480e40b40b070380140100818012080c00c5419128264030f4014140221900c00b02e50004844d19140100404e81503951240070707404954000f8010950710007044000150404800361090580060643c0d4402c50b25000e9200048403c1c54803000a00c02d0fa000a000ca140078171403801e030810008000c2508a105a0300f0001060b03031400701038080248040100c0741003251000a1040762312404004941180c4000040f40e000d00001d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 771118165 1250 771116915 771116917
    0xd050f0d0e0c0607060b03010605030c010c02040e0118290c0a05031005090108010903090e130b0408070f06020406390c0f08060615120606091201060b0a180f0623 71
    0x3a00b162111b4035620030342281d04d000c0c4108030042c8006c0d406413a82c14034020000307100c03d864110080c400c5665031152880103909500c84058103150380f1050302c003420113051480241156140d858440f401d5400ae00c07202c000d03104c9003107004641b100042c1e410322160100c25149504010044c8421400307421001070f082e03803601e201c10300a0020400001d0300e01440e0070002d085a0141d000940c0341c21040040c0320240100c07404e1419160782001c0b020b4140d441e40d16004c5000d200d01d202c0604a00c10b06131014007031180c1d07a0300800840d10700340c8410940c00d19050102c0700214500c1038581d0b4035812840b03003011428020a9861610f84a0644c00a030151a8550f90784460b0154024000381d904c03c170104242420151343c4040390000048440341010341091301000030170001020f0314022a000315a204036510380820f01d4000802000003406a503407601d6481110b40c02202141000603440040f4004070940601b100042d10b203111000201141400d0342525042120b1000d0340e41c4590f454100c0b04c0c440740d140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 771119415 1250 771118165 771118177
    0x20c01060611010e03070b180a1718091e10030512070c1d0712230702061b030a0504020604080f0303010501030f05010503060a0c022104080d050f0d0e0c06 68
    0x929206000150800e0b220b08490080c1d00960b642c0d4001c001c41000304076000e40c51a44006243d0f0203600c2882d040c164141480060783d0010041034010741c1482c40d2a0700540034024180c24001c1001c03448007000700300301081605480302070b0300440700b4404c451144410700341c0702e907c09485e45407a00b030140d4a83c0ea580c036102e0900c010303441d0740c0000f0a0320340400c200c140140e002001c0640c1e440c002070b9640f0310605500e81010340b0000c1402004100204025090380014091000c000703115002c0d481c26101d0203540c40c004850200050013040005943d100065002c0e018111110360041d04540e00c4000b041c00400340504140e0b40150140000504c9600410500e40c202a8403000b841d100c0d45007200140580f05030f51580e003c05410f220062000751130004841e42d02c0302c4aa040822180d0350342005a040c0020301f000c44104280305520020310107601c0c00180b00700d441e0381084480c450b13800c0d07a00711000e00800400c0040082c08000c0e040e9854005e40050043c04540401e8900c140074040c00034206078012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 771120665 1250 771119415 771119417
    0x10305091e101805030d2c010e0c01031505010809070b03090d021c080a0c1403010611061003050d050a05040b1201050301180c1e03060513050607020a030509040c03020c010606 77
    0x400c80c9507020382c41074060345010100305100410714000b1680c40c1034036030240d0003544000903130303c040135030b2001d0b01001c4220f4911107221009000c20400d4642c1d6010f4545440a24030320312030700c1c4d070aa4aa510030712072220011450301d10015000d04001c0110f6011501070814002c3d40309142020a02074029001140502003403c01002d0313098920030064201410800c50810b80d540c00079040da601a08840380640c0140c120200042031807100b0700a0f10f404914003140442040f020001080c2c040c1c0040320808440303034007030486445548042004182d0141c0d03010091070303a0020010360b8103040c041d001820010f400f038181181455114540301000740c01c0b02000402c0b071011800101f015040078440c2c0307440c0701038400c55205080030648844c030f804003586c8161312003071200152140d20360000103100c2c8041d51b40300c4024000d5061a0010800d48180c1d204241d40c81d008800100b8407140c00010355a0803240d06403a0103040080002c10800101441d001a0041c160200079103000c0c11001e104a1700070b0405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 771121915 1250 771120665 771120673
    0x60f06040909060209060c0c01110f211303151410030807050a2001080106230a030e06010801020703090807060801260a121818020c01020405272202010305091e 70
    0x5236070001041c00094100c211500d4010181054003000081244003007040c40320410226061100d040506c14402c0322000c03850300c2c03400200442049440442402d042c0b00c00722007804a0340c40c0c043ca8036884241174882450b504040181000083e0806000c1e00c1420b01810607981c009010307480d40140c07070304000d242d1030008004c10310b03883c8203603001343c0b146000d010b142c80c0002ea11000620071001054000c8400e4505140c082860001e040c0b01e0b82000e40c00007014010399030300d0b50351000302078081d410401c2d040f00410802d8a0114003210700141074404c6824903503a081c1103910b0700c0e8080750781c12815145441d80c00407110798a02042c00401a810030240301d641e030760351400c1b0648001041c4c00540400f000c11030306580740410011948643d24070020700c0301000184c0e1415641585402031003568051500486540f020405420802c00b603600108030140c1c000c46140d81d142d00e154001261409840b40406101c1040405035110360310080e40103c60f58220784c2450a0092640c00c80600031061091542c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 771123165 1250 771121915 771121933
    0x515011b17120a061d0a0b0f040c0206010f050d080301060f03180807110f010e060c010204082e05070c08070c0e0109020d06120203030406080907090c09030605060f06040909060209060c 81
    0x81e2030710030007004140b42c030040003117200340080c1001180f13805007048aa2584516941001c2d03a1004204034020400074010031901110800182d2100000d100315090700710981d8000401e41004a4040c00302580039200381e140d0ba0030810107070380c15604030340501c1c02c05503148501803552281c1c481c0103500c507008260a50315901c0a01d41114152800c2345a175005141d924980c44a03a60010035108121000321502c5403078900144805009009030b1703001290794401c0f45110f00244401c00d40c1c2d440142000c03c69540b0b1491043c0502c010b4440c1616104d00040700c0806d0400403500640107440c040d8071504401c4003440e51070380f5460b05101c007070300030310140c9900040d060105010392140d40000c2c000b80007084454241900065180e0145118000600400720b0000e01070f9203044c4a01d03000f1742105030b82084400c96440000700a00158002243c11764a00400304151b460458000d44101000402c513030314160078030040760041d055002c01101d807282c0a0201d8110f5540740c0b005044c90503660f00007003482039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 771124415 1250 771123165 771123181
    0x120905030c0a0b09060a0e04051303081b0a0c02061204030504090b1f0f0c1e0b090105090715020109051b09100315020703171602010515011b1712 64
    0x398481c981a0721941e5815010032091038080c042e102c4129084a100e0380f50038142d1416241c01000002c03241e07009140808000c50b044c900c40d1042c5400e4000d80d01c150306035079075415003640d0754200440104425014803015040310300c0342c128050000d202501042c02c0c008101c01c140c88a181c02c1d40d013100443c80114051201e0180c0b845543c010f04400c483e07c0c1c541000500143c5c41c1800080080300c10060703500d003c42100c2e80203141c0440c135160300000301c80c0112400340300c21703aa80074026422a40f000c45640070448152050046070f0090080e0005003030003500c3d1008041d402c0c0c801d96080f2055540b40c0e0004000720300140b040b062042c1ea16801c400c69240c0c6442080300720140248a000a03002403641071022940d074a842210081c0702c403200590318041d07810300355044400c80106081d11040d0504014040710f0700c0c50000380d494101c5d0000d004c107443d08000e020304140c040341003078005290071101448030b94010031454403450048031200f5040040f504100c5d0261300228440000c4560b01c41400100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 771125665 1250 771124415 771124423
    0x81612030c0c08070615030b0108010204030201030b0604150f180909050c01020111030f04080909070e010906030b100503180106030c0e090a02010c0209070e0301020c0a0317010501270312090503 85
    0x5101e032900200207071460f910600076008582016241079138a031544da6409000389001300156030400120362031983d607851801d02075486070000f280041d0414090a066041440564082d00c4240c56130048100507003c0c1110b020450390b210808001c01010030030019004044410064135420301e0201e01010107007800c03403070107100800f103d04582c5071103041c050408601003900d4000c01035403078007034442d00c0300e04004410b409003618440d031150200301408081600068104c11007207003031321240006903840380d040e411542c80403c041e40006000c3c000c884820301c41d07001103500c00c9840c95030101c1c010000500c1403c68400703400450307080700c45180501c44d90745003000b500d520907004001010300414507400244a050f078294002d0088004401190405002d0000e80c41c200b24040c000310345400c021185d850fa0f92420420980104030140d25003103a50031051f00e00c1c1d0580364185c40303110410840080c0300c010f02000040c0c110361085003401c08400120180245484d04566075a40340c3e103c1d0a080405081c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 771126915 1250 771125665 771125681
    0x30a150b010216060806060304030212040e06011b200d140705150301050a1203020c190f090b060708090a0806040605011d04050d21061d06060c0703060908161203 71
    0x10700030043c0000c00444c1e03400b801030f43c0d01401c240c90591300ca407139901c2c080e441d02005200302d1140d898046808500101e41c00b260f9440b900e07090303807407141002d500c051594805d4050300000d000d4109504000c1441c2c501001d807a0030011001e8582001840f035a100c1c0c2500d0f40c1c82080d110010340100c1e00c104031524144568a0113280040c8000d4038551500d03000550f105021300c150b0941c800700d080740c0814180280588800d0341380142448185580b101d0640e1484030003801565401c40f01c2042c04960000d0510070981c80040190500d80783c200603031680056500840c0a0b15400104200007040900c03050101d180924850780300442ca039418003100e1103d00c0d5420002599040c1d6240401001c0303100081ca0075828112414040000e805d0f00846182c9030b58a40004a1007500340040000c503543c26071158100d03505207103c0b01040740c4489041080c2841007170080c41241c0c3c0510014400b2800e039601140841d441600d40130300d01191101d4060161480440c140c0f640060403080303825481d0140940c0031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 771128165 1250 771126915 771126943
    0x111c1e060e1e1501081b1801020d1b080903030c15061c150510121109130819120f14012103051e04121709100e030a150b0102 55
    0x60b540c0b42881243c1e0701c2a01c1c10781100e0400481c9000b00740c10214850503508451310180e85035550308410740f40d0400c0c0c9134812140900600c554607130250054418001240840d20079036042540d0040e90711200e500d40c000d2601e00b035060000308000f4250300810891444040b045032000001460110108000480b06a0900040d14041d000b24000944004d11402c1000a00440000c3d0f903144d000211880b6a802c0e04510001c204030a00c081c03e0103104030035040b4000e4200c0d180d40e0fa83d075410040c0f1210342e0003004010129a020310160310004080410f03821a403180c0d18060348640001d0f032016007a43e10002090b020141d4841411002100c40d400c62809003004000307050030300181941040e109642e140000c4c040000201d8101c0c948450105c0600b4643c00a01c0c41030348880e01c42103d0200b151809100300d0741413000e03035440103e0582c0b045c2034a0203840300905540c070040d04060152900703020420b60f01d52500031406500c0000f1004101c100c10115a4880090070107506400a07282c00e00880d0540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 771129415 1250 771128165 771128221
    0x6070e04020a05030123040e150c0906160503090a06050408060f09060c0d06030b040c21050714190f05040606020c0616170c060a111c1e060e 62
    0x180d40b458020b821a8119200d0101c072282c050300205180f110307a480d00c030549521a0070203c0c0c03807080100000319140400080300c0b591120740c0701c40e107000c01c2c140b09130070a841d00410288440c2103502600c603130002d091801501501c1c80c2c90103040005200741407507041040485d1020401380003180c000c1210560203000a0500706031814080304896903504018201c5580f10000070b808401d40c0a02d810420046a02141581e42ea003418640785451246501890080a4105800011044048000f40043d070703004800307000540d04181140c7e9103024042c017480d0300194055451b00401c03a490034800000d00d81c0c015001000303400c00c0e0802042c0c40c4650310200456000d085042c1c03007960b0300d000b21020101e442da500d40002d102850000354010040503c8200c4880114504218480200d40f41c0c0c45182c0552003009400c0081010b0b0140e406102c43c1070203403a0383d50508040c040d00381d5014840c5079454110552450400e400707813a003a940d49030403819a582a250912500404100511502d072140b031401c0c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 771130665 1250 771129415 771129427
    0x81b0603090a060f0e0a1401150e07050d32010b0a14130305060703020405150406020d0f02070503030a0504150e1807031404050c1201020c03090d11030f06070e0402 72
    0x99986880b000c0c0040c041940e902c0350514140311940c44110a10b4542066603810151070800480340f103220003003201d0319420011085000e03035000c0365134015690b6840c041e10070351f26803482c211002d402c441c4910190582d200e5210b440180540070b16600044248000a074800959149888101040c0d000f03641c001010720800101d15081900654152541c510381c1c0c0d202d603078030b21145006055540c400350144c001c0d5014480c2030390781500140706940d41650030800780070b13907030a107092180b045218240041e046101c110008500c910100c1200c10030910490344900d4172040000d00710781c0110f55240106000150030003003421124160010398040303007002282d0f6680000410266454030382c4480303c0304544000541d005009601c00b851004080d030403120340f86407518203240c2d21500001e4243c8566000f54006800c5401402150320514410001e14100400c00041c84980d81c84144101d543c824078440001030358808106a07100c5006030401010642410980a400b950801c1e03d0103000b1030042100c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 771131915 1250 771130665 771130681
    0x23031306081005010c0f06140f10031208070c02130e1005130b07021609021810050d09080409020703051306030b060403032f010c020d0e03060403080601050d06081b0603 74
    0x400002c883d07081c2041c00046000c1d1800710314054154600034000c51609000c4074614084207001c503c210b20000441c0880e883d030610710901e4403100c0c0320080240004d00061002a4444c00b2104d40140f400c0c101980b580000b5400200e0302e4419540e001c0c0c200740c1d00c120f08200020204a452003400d2036a00420080c10010b1840c03404501d412400f030070403040c02d404070351034a02c05c1040b0001d0302480c0c0c240c05138891320360000c0c0c0c02035446448209284010b080d20103540c1d190642645268030342c291a002d25010b8201c42c40c80103446006011381d01c5000030b0100041d014a680003d007a554800e42c3e07800e0380d40111252000079095031b030b00428105450444416925100c10b0b0858003901e40504141103404a5020321504401144640e90242e150001c0d040340c1d0300405411140094406400703640c1c4550b20260100e550845030305079154541e1205020501182c001c011150300040706141151402000c52a8182981c015034008a9154041c1c7d81d0002c080328589249030003031404481180c0b030f40c01d00800c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 771133165 1250 771131915 771131941
    0xf100f0b060d0e0715210b010c11060708180109080f060708060d061b0e0f03060c031333141b0903010f0209040513031403042303130608 60
    0x140042c2d40e0352620741860f2010104802401440789480140058504800003060300c0070b0052000e01c480c24071410311500c0c0805010300702103030506a4030501480d425444100d2402c02c1a0f44650300319004201b600c02003181b040c01421421403500343c60326540b0181000501c0020560700000c400c3c1c0210013007845191010901c141c20124901c0e0090541d102c88000030a4009250001030006140c0202054074120348017609420321003588610300801d04007418891850841d499082d81900020b0025441207100005560010150107001240c0b0200359902c81d4a18081320140c07401c220921481c6429010001c2c402c100100751410a00c041c49407540b5151340c44078050540340303400703810441a25041d94207109903a5031000c028000e0146541c400c40c0d5030000d60010390382c603002d0740c01c040000d82002d81c5034414001e21a81070380c481d0b050510b02030b85e84c02280c0000e0811110102420007903014805140b40c8801800c0090020f990b48007080401c244003c00254480c0f030920000104000d85004011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 771134415 1250 771133165 771133177
    0x9120606031c03060f1d070908030403060207050c150d0f110313050c060417010e0d02030405220606032909061012051f0b0c0c0103110c0f100f0b06 65
    0x1004001080c480b00c08164050800d9800201d269001110005a03c9101c0c40c4002c04448101d41e00110640780c040c02250300c0c90860044152941c8204410000120194000c0180500807801d0b90f490a80c0d031800101050800d0310107060038040410900c550805502c02c24400c00844803040000ea0954804c020150200030080e1015035100c506071801d01805020305c0800441c014081c6680c2d50300d03a0030181c1c201c1040d403820038866282c466900701014000807070819192070740d0004c40c00d1500c3c210400a04c11070000400c040c0d050141e82c56000100a402a44054001a00c0c0031036114002c4800c20741d01d40060f00d00100000c44410440511344410700235079000310003668000072640c0c46480071390380d21403a40b110201d96032400007013001c0213041c880400c0f071001040301c9004c81640c0d01c440740511806502040ca02642001414400e6903009500024030020084451818500a030a550b802c140440c0004032080e00544544032801d042031194003112300e00b90300100160300074400400c045018032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 771135665 1250 771134415 771134443
    0x1090f020915030604051b0303120c03070c05030f0a14030402090103140f0f2401080c040c0921031b080409090204090c140103110903031c150b0912060603 68
    0x78022035494144840301805411010f001c54a2606092510343d60b03031200340088400300381582c01c50384818607010088440070030302c241e5880c000303031980d030759000c89580050031007000d01680785130682c001441400580302d03031054450300342e4481c00c00040180400c03450300555041c000d010401c020041ea240f80030241520381004044058415800b0450318001e0744d03249c6c003043c0744900d40c290280070200192245100d0403042c004c2040354801460b5001c2c040d028010b140940c2c02c5005282d410f801c203544400d40030704141c03a00c2074000799100b00c80032420a0406400c600303098105659820f054008014920300ca035640080d084058090b07c8840650040b0300420782601c1d150b202c00340542d0b49681120401e1500b140302107400d190f03590f855040e40d102012619010030f0401d240c110700084c10038260780350500c2c0640a907152400743c41c2c0280390303d0002001f03c607040b0741e21080d81444009039061400a820440030503a91180c511003006048520140e200f4171940c40721082001d191000321b1a900d40420f2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 771136915 1250 771135665 771135679
    0x50715120e0d08100b0d020405180907060c050c10031b090612150b120a051509060d1a270607020a140a150b010f080f06060d0209040501060504051201090f02 69
    0x5240d04ca12550704050348480c0b0104000315182c00e03c00040d900920403180704940840709101e4203198000328a2003200d140d45c00e600101000c100290082245140e07042c4244252108030241c0c800241e41c0a181d100d1240c000b96035814070800170000800c0540080b40982410703100a8903110000700b01c6511105060300c401e0702d4000120051200d45111000340044c0c440098450b103140c0310b0880400b004407100460903041a022480782440280d01c0c0100d09005047c6803050307910349040c401c4905194204580f03410000c1107030310004900d415018000c02001d03068005400d00381c48005040408040443c00ca81c0108091003801740d000191240841e07406441400407030800b0200b107080107a039800103400a1152030401e01e040c084c0b0707444104078440980f134101020f01600412100701404896008054658401080c0306161090140440d40e004c808050318140703801000c582950401c2c2e2003d8040f5001142c00d01447c5400354a41c515514030302c00800c0307061100d850305442284018406801846 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 771138165 1250 771136915 771136921
    0x213020f130608060108011212030b12010507090f1a0d0507140403080912010c020a020112090611070c17100b0402090d140c0303280c050715120e0d08 66
    0x10300c40066900800300c81400001c4182d030354502501c0f52000b1280f0f9400030704600b0011804100b5622201042500f255015810340784145060300103100ca09035003a4400502c1d803904004c9842402110b1180c201c3c0c0d51099070381458041001080f540507040060141c8021510360f0600c0249030544d5100000804046900d468000040d034013003002c102c01c2c071b0159400042c08418419010010901c181c815100841001a4000f8481c222280c000d0701400580007100480d02562280c01854506200700100142c0c82d03949540303202c100c9015480c0d02ca100480071600c0020320504282e50710040510f000505904444801300548801904802801c5241c0d1000340d022076450b180d0558040e131f8400b0b0000e4980d2a61814840c0b02c16004510035451440f072081e0201042c03d0100039281c4014140c0002d582e4a540c0303411303028100303070800484801c000e801c801030000300d242088280c00070f00d80042c40801d07503080c5040091480720000310000b1424104520039109600000e42210060390758900208651 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 771139415 1250 771138165 771138187
    0xd0c0609020f0324060a051807030b03010c02100b0f090f132a140604030b130501090803070806090415020c070522050603010515060f0d02121f03021302 67
    0x2e07030422030203a05842508107640c90b105001c44402060f074040403030720307680e07a0b034142c00c00c0b8400303085001345604044000001c1511803034012582c1d07000516400e01281c1100040080390856103100110300040e80202400c01012030f80b4440d01d10b400f40142d807070755a20804940883c03000703540503100003000402800001c680c4598810f0402100d42d0241030903c402811070039049088a9031519018050008000081e0080d115192041c0c0303400c000c1c1c000390500746161189540c03100010084c4441c40c000b10800301c0001c50a100741d815a030302c00c800307107a01c0b403c00400c01424440000c1400b40601c2540044c0004580c60f007000680074084140d025985a080400361800d1080e00d9015640003c2c81040502e42041c07130080c2d0301184592901c040207550394100c1018240c545c01e840c10142d4401c000303210140707802e0180041113900c40c58100d0a1070034003d802c0c814203e078069441d24051360b110405121469451001e0340a0b480c2a9074000044241103800040480300410340c0454803580c001480c0303c1d98 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 771140665 1250 771139415 771139429
    0x60907030b04140f09060108060a020d1112010303121404080a02010f1d0d02011b030b0105041505033c090c03101a060c1522060f0e0d0c060902 63
    0x42c009000e9a6400c025100255105446881d220a01140001c1d0802d600140c0310341241e400c3c200410498403581e121000070342c824222401d00c592103180d510812203541e0300030315150410203442c005541c0746050040c004200243c4060b282424000150b900070301124100d600507030440341d90359480031181c1c0103900400c0741e01031110b10740b414890703002e114050001040403020070f0b05054543c24211000b089089402e45500384840c0c00c00140740003000713803103940060f0280b801030421a20f442e45171031034080b00250404085d80010000001c00004035a80350b0500b00b946e500008007480b1040e030b09040c56040d444002000c0e00070401c0b00c0011072044081150214401028040d100d0451502c006c0d0070250050840d20941071040041110481c1841000c5900e006005d402a10003403525106900ca6000090302c021b1944104401c80050001015103c0030354900c152000101403040000c00e10076210450360114841e0480c004035040c21303400144040003142e000780001175010540c8002285 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 771141915 1250 771140665 771140681
    0x21011160302010e0f0a0201170c070b0a02210103080d0b0a1d06040614030d03111209010212010609060c0f02030a0b04030c0c0e01031505060d050115030201200606090703 75
    0x140c02884200000e0540642c800c90040800b074059400103480a151650384d07039030414000f030002c0c902070041082d03030400740d4110b5002518a00160b26006460f1540c6129500642e5010790b0180d0014030340c0c2a282a02c414100e00c0141100d0000c0c1943c50341d103c509560044e07018240d240cbc4e8451030450b070356a480c0395001d005031506402100940c2d5800d044141601012140c180c051403400c078000c0b0303203c044866211070f03041e0001c1c0144803210383d90310f04074003600c6402c803d030300e55200c2400243c0700b84690f1540c0a22035140d0400050311980808084c3d2070440042e4070900a000c5401001e010040d031040d1004826500072004060035681072005c00d01c1c1810012000d0590384101d0180420541e10005079810f81d0b011300c802e000c07000d46415070130410703010a10006054401c1112207550603202a00200e0744081c4c001c001c0d00c4200700c1a1a92401d4070b414142c0c0c0159442c800100740110740c0c0001980342c25101c8006000702524000641c0e03640c0f01c4014155901c1001001e002401d054480e0700290742d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 771143165 1250 771141915 771141937
    0x30a0504060603020303191d150c0f12091f020c060a021009110a0b031e130c030602130b03060d1412270102010203040f0303150f0b0912030a021011 65
    0xa5150000d0076104210310b29020540d000810008c1d11940603100d06d545200c000d030300140349001c085048400500d255000b410403105078040e070a0004c404040501c42c030000e495000b096141e480c0121410450340451810005285030000d086d001c149660001e1800c05003071055450a0b940c01c00b9070070591401d00c0324070a2003815401c1c03140701e00800c0a500c0c0c03580348450342500c1c6005010380f18514042940011200b0480401904c501c0a80b14420801d000f500f201c80d00c2c070520a80c520548403540020120b8000365800e40d000500d4800b0b41c8204084003000300442c82d040c42c151306003480042c5009100b42800340902401210341c1842d4601800b4951240b09420241543c0d0030349a00040011703500c0c04071074a00030390035010b42d2581c1c2d4010b0085a00c202d501c848201a07210171941c1c21f400411200c4844100c40e6409030300802d1400301d0358000c0c1c0c05000c03000d41d91500c50304184100b01c8140300341c4442c80d08330f8100344402c2c1c00c49034000030810068003000401050516400042150324003584030b0301d00e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 771144415 1250 771143165 771143167
    0x150118060806090a051504110103180204021809060f090c070c0522060501080103080316030b1201140105032b0219260301080a030c02030309060703110d090b030a0504060603020303 79
    0xc455401d00160070421310b881681501c4e01074144c20568200c000e4201c601400d44040c9586902d0903621a030701c080301026003c0c80c3c4101e0f890303d40d000314003241c0110b00001460384056a00c05407624140703140907840391003241c1c5c059240a4040c080307221458041c003c0c107080354002ca00c4808001700c1074050b40c0a00780c040d00014007401c80c916080d07000003034050141e100c40d1030560b001c034140d4403480e04207060701d030032070b04041ca141c8404503c0050407069071000e40401d40d0b50111407007207075581d5840084c0301d60568004141e0303075000440f800841c401030748007510907885206043c01800c1c0203d5010750800c07200302010217401c8107010a030306001890440360b0f00c0030f0302c2c491075070104880c18400b410356900c810041008000c00d410300c2090361100380112034466001c0261040024812201416407038030181c20341c0d0408824002080031900400c2007240400c3c0e92100051a4030300810003001e02c16124541084058a82810b01d0301c2c521028100418440d1504000340510003d5000744006507400f400726 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 771145665 1250 771144415 771144421
    0x109080a0f020c01050f07020a0302040510080f012003090712140f12040b0c070302090405010615030903050706050414060a0f1503080a0f11030d1409150118060806 72
    0x1020240d40281580c00c0810640341e0804045403002034207012488068541c1440c10101d00070740701068004141c200c3c1d22030403190002c001620390340a45406841d04000d080412408c0c60034590804c554440c071030510345e141c40f0001c100f00c1d42c1c80c18030a070ba030043d0b070419980c2c03515540625414400d0030380241d5803100300d0349001c01c10400952420400750a51009407615001540e50b5280c95090200b01e11100c200c092105100b8500c680d4001c041d02e400c4c4004076a003403a40c9030701080c0c00b07100448080c0c4542e5550002006a601f4040c40c00b20005000e1504100820141d0350151650080d0803000c1e21060340c82c00041d003002403d4581c0d41400003000200d480034901200d0400282c07482a0f0102401401c110201f0702d2025500e03201410303240e0100e005420002c000300102c980d00c640303540c030404010005421000c824414002010403400341000461480840b2140c04d10160300a4144e0030254820306440d01e044180ca02da00e810b64802100c3c1e50101200500480f0141280d0b822000c0980641014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 771146915 1250 771145665 771145673
    0x30c0a24020a0e01030506040507140c0712050a03030c1704170c0a1407060c0c1505090a0b03040b180d03050405030c0d09030c0b0a3c0c03030f1503020904140109 71
    0x14201c07900f04241c1e4180060f035203030300611080d10000d40d1050f01003110740e616a801002e07520042c1c41121000801c1b9501e00d603440c5160303a96904025000e40d2590881d403454030030b05078103005005500348607041c02c0341d50444044800100401c01480074007a07842020584000c00c008608440c420342d040c6044683c003041c2d500348600400216500e1103d02d10400400148403806100401c0c40300d500200c030f80100c146416402c4881a5062407402c04004080040e01c0f006c2c3d58030000d44014103883c4800940b41e19140c541002003020103171180700c2c00650310301c0d2440c080c44000f4402401040e2032030003051903191460500c1c07541c003d080303102006002e80c50000c1da100e58000442002c40307010f00e80a100c8507650320039405451142d10548000141950342c1200280d206111108101018441c81d00c1d220030034607020726000740104202000603551080c50814117515010340c070810305401e103003000708032620903c610326450140f1000303003d017400f100000c5c01c0c800302d00d0301c441c40784020f80001e019030111454 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 771148165 1250 771146915 771146927
    0x1090b0406170702010b0607020616020604062007150c111507020a0902090f210303150108060a0f140a05040f0509151311030f120318030c0a24020a 65
    0x20b407424102e07025800080300760788140078841d403200020f84518075011039074007441019031000f0803100c0c0342b1400722070354070060b1075110051000300056969002e21613a00d01d00b0003228211280102020ba0102e0b8041c40740700340c00c030b5010740e01c0502c41c20840030208207440c1c41c0415900040304294001121501d28801100c4580100000752084916100031612200014100d0003801314064111401800411060401c204980394400031005803420300301d400c3d45014519402207600021003d10300d0400c000da5600502055003000d0100c850b210464200307000c4020951003441249490100044001c045807518180100038010140c400c3c4080c06007911800c02a082c01d03110301c4020310907000e02d40510740c4003000d003a001c0c1421040e080e41590340c54840c800c00101d1503030105d626004610a581140c0c0b02003181844050b000c10b565070b16443e116582d8441801c5012050060350020041041180300c049201061654051854048034045489040340040051101d00c1080d100003088000e26402c11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 771149415 1250 771148165 771148187
    0x90f0f170c151308010212012601090f02040e15040308060f04020d020702100507080301030201200a06140106020f1018140703060b100503060405091603080c0d1e0e01090b0406 77
    0x1c00c0c240c42c5a69503031141d00700e01c1f40354540ca0143c0c0c032070b0005200812000c44240c024081280d4220045034003085510708580002200301c886148651400c000c40c101030045007070a494042c0a007198078120142e588803890700420080801c03044030001f9071a070781c4407820380c24201070113042151988511a03084009502500c401e0b80b080d5000c40a18240d20700c108100d030724039940300c0079003401c0d80d19503801074404210140041c807140383c0c62880b460300d459040100700200b5028240200d09454210584109082d040e080002150420b03400e0046901001a00c2403c0c03001103407002800f9074031b400190b4030748188000001c01a5140174010400980006001d406480c007035042040440320503400c00000f21440603034500416400d1001840e2480c15511443d4018059010740e10305251226000320715440c03e0304229031480e0089545c01c0098002c112140984a02e424640c0c0a003c2c4003c5010449040c00e02070800c02c140e080c800500703648103542d41001042003108d00d548640d119080507007904120 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 771150665 1250 771149415 771149437
    0x19050a0c050415180605130f06090b1c0f0b040c0812130b071a0a06080c030109032106090204141804021005160507090507090f0f170c15 60
    0xc4000300702803030180709220743c03c218009140c480d1481c101c084182040180a201c003603e90381c01c00001d07a503c0e5054003400314000c03c500020766803050440d4000b00c1e082c030303000f0180045c600b40d0985c0082c2c541150900280c0b4070407100300c5182c406464264065035007040020a40001d000c01c3c8010003252404210a6800100503180d031207046401030385140c002d004903480c910720342410400103228a600280b800b513015012101d21521008000c1003000416201100990b0f03a03100100a510b90a0082919041c0c08034000d001d095290346004083d18517001040203810200303d251074001c04107901040040c03e200c041036450b581d0b00c150072a140344419030300038000c98503660014400b011685030320744182d03070042c450040301e00b820074200c0b042e17007080c1c80c4034004040c03030704400022500c104411001040023540108203490140030082034115203500030291000c0300d540521000700c5500f01c040645090410101d010520341444a161006c84d0035815085100d000e000c0f5110304004d8010980ca10030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 771151915 1250 771150665 771150683
    0x703050c07060c0f0803060d0c0e06042d0b060d050f0106120e071a1e0304110d08071b05120d320d200c0709021206040b0319050a 57
    0x1903090251441d406024000304403c2ca0604d4640011340d0a0001d10340100018104d44251001d903501c12102d4242900001c2607441c1c1c003001c203d41391805000784052101441c1140e01c10500b801c8010900310706407010340426a8503100c07401c003d9242c58041c0c60107070300c01c64428400d606081403060000c00c800e02520000680e2909481a190320074000c40c0c0c04030070141f00401c140c030f19000d40c0c09409810b810330440038081c20480c4003c80c1e124004005900001060803070703030f41d00b006d15007400c3c940b41600002e40101084d48000c0d0104980e10181c640032900042c4852111181d88004031a4801e20b402156004d904042c41101c14800001c04d143d507540039841c1c41c1045420724541c1605600c1c5010428412804814008002c1e21814041c0250304842e11000ca01e840000c0d405c010040c10380c3d0301c40d88814102007401c440d04182045000010320005504516044100d180840190300c0280014042e40d1190400c1410391030801128a0041101d0381e2024441907502d801c3c2d480d014100d600360b401d206 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 771153165 1250 771151915 771151919
    0x130903030f09020d02041d01020403060b03250e150a080a0302010b030102180d0516080a110a060909021e0406020d021b030616110706120507090513020903070504020703050c07 77
    0x3603440740842d1207400070302d481c100c1e0105034208009081c81000886a501c03011508071412002400900043c0d03104060120700b00c0601d8040c585020100300b01462400709000c01d03105020030030045403065a4046c02410a10790b6070840d001520301c2d4100c40300340c001d82000e20010b0400404107000051a01c079500901c407024002c01003600781d00840148489030320310b1000c81022847d1483d6801c94407031050060b90000003054050b48040d0045501404a5400ca0800c1d0400c010030030a007c0300010040341d500c007043d800c0081c01410350b01c4074050720a00d10750015500d0601007a0a048102c0f52400c58440c550b03854854500079280d800688400025110f00c8105426640403043d1070200501c000c0d00504050751002042030403550b808030501d0070f02c101c0034040024140d040c480f510282c802500e81d4034850342d55800309012904000c2507041044203065040c85290b44451b00f40d4105c400e035480250b02c07680040c0019003049140d42c40b003540b00384002038a80405030400d000d03103040b646140664904075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 771154415 1250 771153165 771153191
    0xa05041404090507090b370803070503040b0702120a06021b060906070302090144070c230a06091a01060203120406060810050906090304030201120903020a0213090303 73
    0xc088410052464011040510021080394000d02c4030100041105481d400c81802101d00114200e8905280424040c03010321541101c0105600600181002790f160410b26105d55480c0e000380d009010342c4180c0004c150095580d5040c8020002800e40e09a4404000d0391a1000003540420702440313183c407140f00c24010364440401e00300d200d900c1440c040e00c00740c2c1da00d030001c40007503100c00f07009030510610700d0040548d640c4109050490742d07000501450f0301d140003100b24500c1c54010032108440941401040801c070f60107160740d418a98084c988001821100c0880d0050758203441d908580303841100b519800344581070f00b005018600505003080d403070340400381c0d01516038400d02070000580e0042002e0030252031004451644140103c2c4001070603078036600d00500b01034210782d101240035280c10510651241c01e0000a402070341e07100045280c585542d001810350211500040c1d00c5603500c400c440705150080c07111242c102d0340140203010020308960383c180100094142a0000f92400351710038151 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 771155665 1250 771154415 771154421
    0xb0615032410020304030204111303060506090c16030e220f0e030705031210050907030c020d0806010906050c01180f030201060603020315040c030e0f24070816050c030a05041404 78
    0xb42090340d018610701800c5800b400090300c441c00c100442440100086450b0f104001074040103544a1840851141051010022091400342c8550011801001805040c2c42c20f00d6116080d035506003405404000c0c003030300103281490b521032030849545015600f52001c00c010381c442c1030f0103620714404118104c541e0840980c0c0c0c0c019004010800d500400c000c00300b8031000c00a0300da22600c0d996440e064591a800410065075090310075801094840540c072003650740500c06040000700525220495141010000704078105511458050040008106c03145041c29000900305c556000c03014800c00c1c01500e01610172103001c090a50042d481c14601040c102c0c4a40201c81c0110100c0580754425507001041000034805100d48500f499515652b40318001801e00c080940140315a0182400003019086900c030713026100b5401124003094010440c00f5508100080c0e0008414141c0e25024003481009541c603204041d02e030a810712020907050300040d4413400400655070071060807403070000803100388415 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 771156915 1250 771155665 771155689
    0x706030606090e22050c0a090c08091b04091401090f02150a08060111032205030d1407060203130c0801021b011a012105040602070302190f0b06150324 66
    0x500141207400314107154403041c111307028021400c0d45c040552140c001180318503d41d200c1c0d44c1072038403a5280c0203103941100c2c040e50300020201c09007080030700003401456888041010f1368031403580c5140090a1204400c4000c85280300f00c0001c000618850820010107005854101d1249526500801102d42c85200341c4680082989030446240c450b6001900c58100c01003500b1941d202c20312000c130091a4042816025004070f0040854080c2480309041c01d00c01032001c00c005100d0009a143c1808100c80201ea100f80e4105100603100d4554070741401104101c2800603007030302c0203514085580c840660050a1811100c0800031805a42e10007142c01c0ea6650702c11144d40d50071489440e820755001d90000c10338003900502ca10000442ea1000c00d0448105135030a541640d8040f48810805404114079414031000f0304088403000c080e65202c1c032076844800741c0184600004808501541c440c240b940d10300c891700104a603113a00d0502c10b0b1900001081303550084912626242c83d40e0342c02d0103601086 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 771158165 1250 771156915 771156931
    0xc04060801060c0212011506020111040803030414011b030e0d11060406050709090c050702030d230703030b0d060f051f090e0705100522050a060c060e0706030606090e 73
    0x40c540c0c2c42c00000f80c5142107102c00990300b1004825030a40b003441c0a10071100d08a40000c00f403900107041c05002421525008a0300d08110410807007805000c0000040d294004c0c0d100075a0102404a14403150162801035070b011040084030868620154140e0040c1c50302c0340700241140e91410706810b080700c8075951003140300358542033a008180400d4154026507400b501d541808540d0590f00c02c03030101115080e1400c2e80010700701184007011440e081c0306010782c085551919441034031101801c10b06800380302066000180000414000b0140280c010342400d18004008899010715410890080c20001c050002107500c0c0200040d20010400c003440c000300300341e0601000050900c00c03400d00414141904085506c05c280d130008482d03a401c5c1d010482d1600a55850b034071100340c03182a0301682e1203200700c142c508020301e1081c046a1958104401240c400746004001300f0b0481c01d0400041050f1080f041d003500501d20042030b0729426401440031581555901640359030350f42107030700d41c000707003603518034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 771159415 1250 771158165 771158177
    0x12011e0e130f020306090a210906121b09150f0e120c060a030c021605030a12031404051f0506301f0f18170c1204030b0c0406 55
    0xea107140120030071054035204080c1c91100740000d40000b490100102c5000841d50b010341490300411507283c2d070300d003244031600c86c00c1001685101d80248c00840640103170010052540c550300d2600126400c40c411480001444082020a060000300050712501880d0b92090140e219035020034858207458250401a07a1038002d43d4903c5401c0066100c0740c00499a0b4911480c0c3d2001855640c010081030310140d1600c0002e545100000013030704141d180c9081d149d400c81051020402600c0c003099001800e40d01c400b5243d101c0d082d008081c0c005002041401021440c2442000100321000510440d401507141d906c20059055060850544904030b4203180c0240d000c82030707003e04010300016200c203512a140b41c19021083d082d44289000c024014148124103800c0183d42485400c6c8540034003060412001d201c1d00700440300c41c1804034092080205004801c140c02d0006211010698003c1c07048003040ea90a000710f00d6400c0d00d25040350006891604c01e80c0c0105900001000c212412910940c07505 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 771160665 1250 771159415 771159421
    0x60b091302090c0d051e06090103050c13021b0d09090204140f060c030c1b0913031404120506063604060b04020a020f0f120f0306041112011e0e 63
    0x4002030308400340c440903c0d440c06002e150311203019800781500c0f40f52400a18070780303203104518512002a02800c498003c010080041c408610b000c110144401d0007500c4182854914141d000020b2040342024001d0003850a22601e10701d8010421031006809a611905030a4492154004034807071485046051103540001c01c01d541050103518903c201c008107601d00b0850400646030850f803040c10240895000300c8106440800680480e21140c0c2083e190300c0802e1505201c42c0c4c03115284c00300050103004500c910014100d1041007141d0181040c0e4294604c03000c2c0354038040f42d850200b81e844505c02d0201d042e0080200580e500b0805500700c60201c40c5034001c101d03071004001440301800030b407121525841280401c2c1c07a540001c0c1102d80c0c0d2a4024141801c0a503041401c0c44003000103001950414003c8000e035150300d9083d140101c003030300b80c2a2b9483d1600000a030082081840106103940c0201c0c85107010189880840d0407507500403001880404c0841a00031501c0050051081e00c00e161008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 771161915 1250 771160665 771160669
    0x40554100b031f060902040b03040c06020a0f020409020d080c03070314030721021e0318150610050c010905010e060c0a090e0c0c1506010f02190f020a030b070507060b091302 76
    0x2800d0f0712003c2d0800003915948500c2d440d002d99200f900034914a00000045c081005001800035006001600c040c001401407039030f8500020110309406445980c403040c48005541c4c6042080390210b03484180a555106107000964407034006031025404a040c1c1c800aa084048820850f80300d08000e40d1407031071182601c079018081742c18424101d4020f583c00d00c111103c0311038000c4402013241d44a9001070300c80c90f1654000444200c4030003401f40c19004016200c080000d148400ba40241d0112420003940b603120500b11141c0c0a0000716188030342c2400300d80c1b405d1001c194401c50500103404c00341c0d481c640e507071021494148920120140000c821310800c0094006804002c2c2d040114140c455140c101c0c5107802502d041502c030f240642d207454010030f0150560b0019113807240c481d0343d03001030b0110f01f2090380c8680ac120480c2001a1a20703074018214401c550701c403030058014640c401c03c1c1010f00d040c8000010819006450206da1031440c000f0b90000501d0b203000040d02c2810040b4205c9000320065007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 771163165 1250 771161915 771161953
    0xf030605150a1112030103050717010c120b041118092a090a1e050102071d132117070c0b1b04080109150605040554100b03 54
    0x1944610600a070513041508290450041d4000c0d8094801007502900700048134150422000b4807401580c500b181b040c0381160090314452100403900c0000680503041d40101b4003900760f42010740c0d29140d000440100210703003019103111750142501e495000d03035200d1280001c0305141c240310007550031948051030f41d0030280100800420a024041c6480d095a407044070507420140080e00c1c01c01c2c407038401e00f0322043d681082250002c5ca0020011000e00a6402c10102e0b6040050304800082c0c203014000c42c00d01003410240340000d407540000728204d0410000040c10a0140800307460040e1007200802d03902c0e4412a409008075070081217022060701c0754000342100c6c411001030401e2407142440006400c80c0b003841101c41e142d004910708184100141541c00071039000c4e8022600c02d0f85442c0a2050102850160560710302500b044408050b0094100007401035001c008610207607500701100c03160001400d5111400b07210b1000b1120000011210002900c81d452074158041d88255901085c04243c58 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 771164415 1250 771163165 771163187
    0xe1f0c0c0501050a1704050a02060a080711010b0f0d080f04120606120336080106050415240e0307090218031c050a050c070f060f0e0105030a0e0c100f030605150a 71
    0x12115014239544c08204950003c00c00341011803200c4040251040d00180310444030310016000b000038006c440d0010b81000502c42074280254034400e031841c104003000f000c4071240b181065000b81c845a0303540021100c2a0202d42c00c9444074144200040c40c02c112080d400d036503641c503071030700a000854150f94a20b0041c07180394540060446128000380418280f80e01d002911a40c40082141400d1005000c00d81d0520400c003520500304100400c1032112000c1c0d2410f01016008030306001e80704900c800c40720510406010340d4140928040001c00c451180d00a0440d48003112071540005400c0040544800c041c0307001501c0c510303c41b01900402442640105903950060514030305184504d00703207501d8168190044d4051054126050000e00d400c16001c18900c035251800348501d0300842d000a01900000d4001c1591903254100707501018000c0c00721280d2000c3c082d02c0c00511140c081d41c0203180138803203600c91010030318200c00440c55041c06180c0108100702c42002c1c82c500089002c04031041c030740c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 771165665 1250 771164415 771164423
    0x1e0f02040602121c020a0c1a1f18051b0c07141212090102032a070b0712080c041e0f0f0308071502070507030c030b07110d0e1f0c0c0501050a1704 64
    0x1fa05c0000000b40c6560224601e001c1180c1c8044014506004040c0302c14a11654024040441e440100100880704821900f4442c0c0c685000c07801c2d4071454407407208003030054168440a5400304088121410001d2400101d400c001c210300c0b18000e10005200c040c08914200c0039540d003101e80f44800c0b9030b00000c000c105401c41803046034901482c0c01564001303c920750100c040580c9100e101152501001c00902015140301003101e880c08002c0d070b4407140041102d1421a05000803240011000e810110a4030010400c141c41c4000c07404045e0002400030013140039500d4042c8100001141c4003040b8032514099035481030706145015001e850f0361004885960441101036002c00902001880600c003c1c0019442600345400315400c5207490a00880000c080d4010044203100c00015142e001400b20000e14107130400e14000f201140206202190340070480280c00d010720701c0e0307448599004410a900ca80504c4001458948a5004503428440d110690303001405005111078010a0508010381241c82 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 771166915 1250 771165665 771165677
    0x1302010305220f0204050c0901050301090b0117010608101e050402030c07230d08040308150d170405030f07050901030b09071527050a091e0f02040602121c020a 70
    0x2105024002076148070848441074842c101c1000c40c1001d0180d1030700300c54401e21f158103161200000034160300052103411115510344000c1800d42e4098201840d9800450ba04040c440d82c560001800403070003900d0307141c1c5484401d400024240100c140464100845078101c510107032a000400002e500054102180d00802f0422400002c0c058500c645070b24920fa20640a030038211002c0d1400c1940d620340410a202c000c004010019900508603030380000c4429084030001140800319003016900d1130001d0018000c0960381c040c225a0300090411a4000c60468403081b081d0500c00b51598054031036070390401111001440010403140e00300354010354010440b40e02075a10028100c01480b1512014003180110709003070302070010245022600d28140c502e04010a01d4400414400d10302d44c0304203500940e54247c2c460780382d905849070083c1000c1000040c00400707aa841404000e6000780704410140c4203046040000c10b01c24416124900e11300c41c0c90400daa0b070b201d04840080d601001c142da04001c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 771168165 1250 771166915 771166951
    0x70f140a0c1203050f07030c020c0904031812110108040201023909060a03020f0f0406030b0702012d1a0409060603140a0f02120a0c091e051302010305 66
    0x52810064900240c25548081d5281514288a004a01c45201c00c804250070302040000500f4046045a040f6845207000515890302503000c90800c0f2000d07109540c000b0300c000612082c16441000d842c5034404000c503445134696030307040d00007d00a0081c3c0080034082a541801c0c8250f00810150b03500170b006005480e50001003075252401891400c1c0300c8214182451724006540d0a031640345a41d0441c144d91829090500c500012003021051000a20a00ca820302c000c1c403544550070085c90021020f4401d0100b00d80ba1314101113401001c9980000546c40e05070f950924041d0400c4980c110650031114446c2020070032002d20242c9824402543c049000e55911180d42d1180d10138031070410300540002410381d04600c3d01e0742615107a51502a5103501c04891000800c0da64031405c4400b96045a2039070144c2504001182401c06104010f81050180c01c00002c460155030411003d004148800b5481807003054004012100203441802120040154071801940260b000c550080070070020001240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 771169415 1250 771168165 771168197
    0xb01140607151a0105070201120f060504060b070b0a0b100c060915090201111605010509121207030306060c0b04030c060e031305180402090606070809090703060608100806070f 77
    0x22098550101c007003992900000b404803007441020f00501000d107002490302401d500020303c6812410002a4620b50341d06440f0002c030403e5102d00d00030321015005010090750303180d090046801c5940181c4a40da1b100e000201da0301561b10420030b40a40083c80309110b0f10810400302c5002d500000210745042d03844c4d80050100d90001e0419000f0750ba100e901040701c0366203100040c8904c403a0310301001e8541c85a000c0021a162013402d00c0c040c0c403000e00e0800e0710343c1d001a00003000c664031414229030318000c1ca00d401040c024107100802d04280a514140a010740d00c4604581d1050b2001c405400d8400c2c05000c01c0000e4404e00084842c50301511700410b003414050345242c19a4421112a584060324400070000c030308203400b000040c21541c82e01280340f031801d038002c2140503000a002920440307000a40d54108803207001911042d9201914042c0380f85000c50019000b030805001d8440403603001400182c00052042c10b60b01500c400360007405541c1c0f20a2010345142c0b141e046207a0a006036092802008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 771170665 1250 771169415 771169433
    0xe01080a03080c07051e1c021e0a0f0b060114071a0c1207080603150105090a18050703080405151c152408070206070c0803041707140f01090b01140607 66
    0x452403c6d070040744028228a82090040e4031041c1070135140504011035008500c0345140c06405807541d207c0403a08002600301410700e54024964a5110080010700c10880700c0c0320b100d00002c3c0c850300d50032031041824a03064080c24074010207200c0000c1800b044a000c1d00401600090141c0c4000d040c032406071a622a907a408540880000c0c0380d02041089a10381002441203400502600072f03000e50524001c00d90b040e070000c040101258982c1c00b203130410200d804030000c0300b0740c0040c20750301007948900d044c02295000d4400c1038800c41c6180c0c40745249015800448813481d240b405070202851401e8103580140a00f01d500403200200b001d0005203610030080c10283c3c08001481441e60401d0490010f860310402a280300b00315848039040200c2160403051442d40640c01c44041a00ca58a41c40c0c5050640000e6011003c4030b0b00100300b90741000b801d504c0c0c02d882c900c620300a603120b1851012406089500c41e1a002d031440e41c640004210040a8038000c4507000c81c05080346103409400d440d403640c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 771171915 1250 771170665 771170683
    0x6020a0c14101d1902030a050303011403011a03030d15080d082406040915120f06060501051317030d15031403040513020c0c03011d070e01080a03080c0705 68
    0x26500070040342c01c500e18982c07188080c030560340c4203d540e500300300c02903096036030300000c5101201e1070b5001c02210070340d6003c0000e001c4c0b40707038400d00301c0b50340350303110f00c0300010f05210038040030700039803c240ba0884a003aa9660780c01034450080c0040d07042c12030011500e0b016081041501c51400d0f0b25010109440b0000e010320b042280c0283c640f00402d041c0350f4100c1c1010950440c8200c408040401035580c1503985504650403034400d8000401c1e945119219217105030046e9009140d41c41c88403001204004540c401884004e00583c0c04210340f551fa44015a030318402c0104101441c1d106040611100700401100c0ba0300d4002c9400b16810060138000c3c040c2145e00e10905081000e007912800c100300010000c203080354881000245007402c1ca8140400c0ca407564513400f04d081715401003064900031100308140100c00320001c00234480c02054000610b070742099903c920b1054050640085600c003403510707a2604a500c1c1c203009042600b03140c0c07021076045101405e900401082002460080fa00402440103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 771173165 1250 771171915 771171953
    0x2d0b121e0307031d0f040606031e02040609120623070216060905010309151a19060f0f021f0c090902130501270b040f090902031e0f060c030703050112050a06020a0c 72
    0x1c0000c0041c50f06800001c0d42a02c0c0030320ad5004100601100303900c42c152400311414401c002000c64014500100507101c240f0201040e01c00843c01043c00703000ca141c14a01445182c2c0036a400c41c0303602c0107400d40a036114000d0001055104000300080e522070360080e4011800b407806c241400d2460601c040c01d0f10914001c540c120441420401914680805000c4195412400d4007091a1620102404000c0110112418805004400003001c0e0092025581781c0f600c880c00c2c1c03007902054982d890000c101d102450400520b56490125041d62113100319800d00c05a41441c1160324900001100c5008c29070381c40c03440b6111001d52a000c611811203009024060328415541c503142001c1000d2a41c0006038440c0e80755500f03148001e005620003060020b810059000c1290700141103030400c0e464503020f4201540903100b408200b10300d100c0c0c0039018501409180c0d80c00e0009982e2141c44071604451000d014102c0e8200c4250003001450039070060104244504081198002c580c6490460b0b0420700c0040d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 771174415 1250 771173165 771173171
    0x4021806030c0c030d050709060206090a02060f0c06070c140d0210110405090405030703030f09111201110c07170a0c09021806040806060a06032d0b121e0307031d0f04060603 76
    0x1140d11f030340120440d0050085480144080e1500450203075035030f5642c3c44064000d11002803c40400550141100d01c070f0344c100d508072502400e11704c40041200701014800d454a9100f214804401e40000c103c0c950b078122250b0040000c0c107010308000e001400540002a5840c0c810000020706489401c0014030690144000d035072501218280034095803800d0f1407240846140600341d40003d0301030b40050f0845d1000b0303038581650324002c59003c0d00400d050b0b00e244140050120380341007091800102e8038142d610000e030600d22241c10b100969960300350490010050702c04001d0a002001c0c0a0f405400d02c83c582490b5043c1403004400032039440d03071107038103d0700c8103410020411441382005800751000304442d1800b00031102c50280e1a081c00c0c0d40034070014664074101c01c025030410581d0317006600c00c100010112503001c8481d50040c0d41ea10280c02c403d080083d82800d6000010b4404400e480b140f030703050303100d1030b0b800d05042140c10340e00c068000d6141e6100e82011900c60041e181c40c826100540300b107031800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 771175665 1250 771174415 771174421
    0x405010806040906110d0606021908091219061505100503090705190602010b030d020d0e06070209011401170907120311150919110f060d1e0b04021806030c0c030d05 72
    0x44140c41c7d464000c0025076200c5043c041c0d016028800689289401842568517003028500003880704500d600444900e00c40c01075450040c84e04210010070491068508104c5230200d002c40c0e85a02816126084c2e1003409450918980750242c80210390181410b001d03124044c2d10740c0c00048040b6025200007041a982c0d550a0100342c0e0240f04000018800300c0c0100400510804025619442c140c081010000f4140f007001058507440d054441ca141c0c000c040880369a11218100600030b0400f01440c0012400d40c08504048034010226000710b010344003500c00136040241e280c85090f400c5000310204841c005405801507000e1101d610360724981c03020400241000d81c800c03890710302020300301c03041c0540040c280070010303005e404107003c060029240500c14010510000380700e030140810103440c15040c1107600681d42c08011002109045001c02040480741603824801240030315040355400801e440103840c1a860b03d040a56132064100e030701e103440e054280c0c042504540180b880c4a0501b80c4030018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 771176915 1250 771175665 771175687
    0x1d130b010902030f010e0f24040e0c0f010f05090d030c050a03080a0c050913050c07050d0507120801050906090405120d060f0503010c23040b030702061902030705040501080604090611 80
    0x250500501b444c80d0144141d09220341070601d0000054401d0300403556508040c0b408164045100c01d25420041c81008600003280da16a01e4086105009200d000060000126507002e0307500a501c801c46a41e85604101c81d403001d000d03507a0031200b030a0303051080945590b400190100101da2019110f9500e018050404424000c291a40003200d9020b2000511103e00c071a00c410a200c1c450050191000c502910b81000b010700d40d100e030a03006010380c0900511588140d07000b40090004a103c1d00c9040c0d281d0040842c100c520500a010b2564000c0c8000085900740c6007412071150098000c02c162812094001e071020000c0d03007c4100514050340345e56041205034040c16001000f000e0590081c060007103540d400501010080020000c01c4115039040c00403404c1240a41d405010030307044283d624103020001a645000c201c1d5036014001509003254030042c540c0c0290390160740c0e642c8806040608010040d03d0400000f0002078126a880c0908404150a0302418150001660925540e6185440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 771178165 1250 771176915 771176941
    0xc0303050903100605100305100b121504090c1215060f050405150d0215090934091809080301120b07020723011e020102030910061d130b01090203 64
    0x4006220180340070800c0251ba1204000206641981c6c0f0740003d1558462041032400714188e0013204c40548007081e01d8000c000c9030740799503000d441120900003080071460200030a03605d091000504120118200704039a040c0786010302007262080d02c1140780d103103040c1d50342d40448145a01400205c45500000c002c0b03030801744510780c0c0001849024503500312031070000c00d03107003854560000d02500b078018204044403105005d8560204006200340c40c581400d152219060b03185286d0507507170403160070320000d2010a0580c1001c071240e0a442c0c8071100d626040720f418105221090018100d42c480351414001401500154041c00e24903a44e600d000748542001c40034001d000f03000c0c4065601c404400d2241600c804604d03544d5a0f0301109100d44c585a40300101d481070b81500324021001c404c255810346850b01074019502c102410740c01c40c2d061064113070140064541921070000c42c51304d420f2102c103100d514079036490391100300209810300a40e05035a400750110007da2108140a50202c1031104800b0710700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 771179415 1250 771178165 771178183
    0xf060e030c2e110301030b04050319030c080708040b1f08070f060e060f04030803040f02090906220305030f0403030e070b03190c0e040506120a050f01050907060207030f0204090c0303050903 83
    0x5a04100300c080702d030f6401c03000d4071043c0005041e5240c0d1400050401a08004840704aa00ca030680801440210005006040382607604400300d646080091009031080c10400d01c1503821000880540c0c880b03410302c00300d40301400d0001403201d04d0b0100c040f646d410100450700040c50048034449076149080c9008002c0440360b645d241c8182c17400c0250f0041000c0741d809507806c1c1d030703000038440355640c0b61450080707000450908000e402c00703140b200b007048481c00461024403800c030b140c080e0f8113079010780c1c1090229410383c00310080c0402c0c0c00303002246407203161580c141e90107442810005002801104160300e0500c440d1b01ca0b0101703010010410112012000128100e0101c4800c00d00c00c03180e900001400c10300701d040c0154003966480300024040d81d22080d41a66117440201907411411140c180107440b2501d070b50041a45608207404140c0c682d4000817040122030b800c0d80a0b118103800c540d90025069030301941a0791154440b026030f808074a41ca44400011842070315442e554040300c0050500b02003600c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 771180665 1250 771179415 771179503
    0x60501050603010501120b0105210a05090303070207062a12030605061806070f0602162306180709110405010f0201110313060f060801021c05040f060e030c 68
    0x5000400860360025100820b050301c6c1100414174000701d034012510b5009000c031141120b020b400c0d442e120003507c030760b526001d0030302100280840d40d1100240c9039284801e0700d221340164450301040008611030b402c907105280369030801c8841c013104402c00680f803602005042e0f541484040060211036054031505004140c141d8149041c00f20040c035017203241c02034030389403809a0000902442001000e041e60102c2350b0307101c501151500b6242c101d5100180146000701e841124080c03c0b580400b042820384000f0704903407401001c3e03550f614000d104460079a0b030200030052081da400450708002c20301034502c80000320010182c44034507110004251440120a880569140c0200f000d004414081102e91003600e1b01086101140f0625007a4010f0040980184d00a850007602181d4041c06400521000301d1030100048100c0c130300b094440031100d0688004001e0b212004c1c0070f100082c803a4200f000009200000d0340d013482071400e400c500700901d4070007621071008001c0e80c00412100091240780c2840603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 771181915 1250 771180665 771180667
    0x60a02031f0f0315022701020c180703020f131202010f0c0b2e030c0e1b03130f0b040f020a09110d0e01021303030302070b0f0402030c0108220309030605010506 70
    0x640b6182004200e1940400340090101040f414600202901100c603030002806410010b031103101c0c10108440f01150580380140590b1212411a1400500d024600c05542510a4094551f01c1c015402176001055125a498090100b01c0da00389400e00b0220080517045a096040e039103070b100061079a03400030501014440c030350990728045035081050640c412032816a04105030075016a14072607030b00005407410280b03003841c7c02004208000032030f40100e6007040003a0f082d0361101801d2110700010003000c6e0400000074400944d03c00782d52515451080c0c058045182110300c1c0c0d403a14140450100c90a0760400b111550b41c81c21401c00c02515401802126808c05c600407082d10081c1191080c882070b03103806a101d140320308500308294100d95551450000801c80181c0d2072074054080d4220550513981302e486600060458503840c01602e11841d8002d0142102d80e0360380c001590840ca010f004400b05e101c0c110040d0310b81c0b00c085a940301040e8080d441710118945185042c40c143c0368141c1019001d00e41c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 771183165 1250 771181915 771181919
    0x90b01060c050607110708012a05040b070f060603020d05010b10030e07050121020c070807080106120602072f130e06010b0a021501060c14161403070503060a02031f 72
    0x10000c0b440035000080c918010813030485c1d001440d4a03040360307030f0449a42c95180040403425480400b00300302514024503a00c0e0411045410242d803a4089c51040f21018001080401c0004600c001c1602e1000d1140e070000034a80c2c0c4030b4011405040c40038404440b141e66401c000e0101d45001c82c40707441c0c10551460107000e02c0b858001d0031502c0302e15501c521418050301059800700090302803850203808007030007c2151102003d060066807103105210b0440380d80682d140104070701e507040c0114403d80c1c5650418010424042c2e41d0711000350b100500c1540e0001d50110300320381d1000b96070301596201c00084405215004420208821201840a03c80f281880d161001d6400100030a915044070720f40c400135501c0301d03c005026420601000300000c0c11100000010805a42007030401c00064080c2803003180070850710061035602c0300350203d451800300c65460b0400c000d88201c2070030324071b108001d016a0038450b03640011910f024001d441410705e25030044200140845913403031240d14145000c1841003214 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 771184415 1250 771183165 771183173
    0x90121090c06090617010f05100201270210260406290103060807120305030402010c0f080307030609020a08010b09010e06030c070203010c020a1a070e120d030b0618090916030501090b01060c 83
    0x101c03d423280c540281d03450103002401500030340c07010701078a4491035003003c0b941004541c02038082141e08124030400c80f011104041d40c0c800e032b0000503509440128032038509c0b8030498248a2060050080707850340d0329202c04d11a1807405480e1610142c10082d07201c1105400100050203840e07240d00140740c47d134020902000142c4070510700c0172520b0b8240c1031240e904c0d02d403400100c81c5c411003d01d001d00900518515403080000c444002c5106246942d0304210182c1c4451030346081e44a0741c10344000241803000144140e0f101c0d40c00410309480141085140e43d0b0300f19010503419041165060706c4240081000b000750304081c06207140c640b105101404c00440c1c00e590310b20311a496405418200c002100001d1550382c06000ba20722496401481000407503030300d010656035880c048034082c00180c282030b030886076428040143d800e40c2c000e8480c2c0206c07103c0c0f500148208402c0040403451948140350000758070f20000003a901c050b41c0900700100d1040c4c0300342000400c0c0b11041c0d000d1002c015102c84010041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 771185665 1250 771184415 771184439
    0x1e010206180c06070303150e0106021b090f07050c071403010f14011e0f0905161d0108090304151e02070e011806030b070512010506090121090c0609061701 68
    0x560b00031602c4607281c44680c00c0440080564006008009440550119040301300707031a403030f04079182a801c6407039182803420001503203112443c0454106030f414000c5061866035258143d406042440c00d039003007020f03100d2540d1514240d5800444030045015103070300d49090a0040312082218440d0510030a15104041100d40f04140308242210840b1148449250102140c02000780300080358a1040c0c1d40f500b06040060406850601c502c43d0403038500c200c01401280c807074844032980042e80407a10211340042d0752004000f030040403280410400030444017030368600f10300c4801c0daa99400c0c1010310103025981d0380c0c2903400080e10035503204040070001d950440b4981ca064601c0f400003800801d80d010440006412182c1004203100c640604000156030b001000e050090322046034a41543d90b10401d0110500c0b4140c0c00b14001892041c3e440003944116000b0f0407104030f60800004d0303440c01601c800c2c0103607160303402090000300c1c01c290821540381e201d083e03440c41da14480b03903d00865241c40c001c0703400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 771186915 1250 771185665 771185683
    0x1305160815090a02060720040b0a09020a0c0b01060203040e0f010e0402150705010911030106090608120901020a150207060507030c020a0b06010c0c0801150e070e041a1e01020618 78
    0x450301c9800020786907a40500104070110743c0600349580343d20b4603141503000c20103070174030612240d280a1350b04a4649030038002c1e05040301014110183c11070810044201030761080b190030042c4110448010001165142c1d0240204003640c05141c50b203003840c1c841c445d02c0070040c000c00200e540c4c0c000107001d0415a140b0140c0c00c1a03040390300c0394270006e0031001c0420303a014540000d0450b5280c90001d00621070040382c4204006400c8000b04031007034407007029100b2144075026207103641e4030145104c500c108030799006001c1084140122003101d00326a43d0103071440d000a405110681d00860210100191405081d401240f00d05050203410ac6174480250b0b039100b8090050614421480800c030300741d008050034500352750000007004050740c483c03580714017030f18a1809a00715000200d000040058901c003603d806054184e9426185906420403c07010b803d1030b03010288070b81401e0b12445600c5d994110103c07e0042006150b03040001c2c1d210003e810701ea8028481d0403050420300b19200900400b044880c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 771188165 1250 771186915 771186943
    0xc09080c060d060815060f0406231f020a0210031416110a0602041502060c07110f120a050c010503070203250f080301080123070c03030f020313051608 66
    0x902c6107041d0070018058038856021003c0c500828401104007444000d10720b1050b4019203004001d0a110400c0c003040360840e22520101c41d0306035602580210492111550540000780b030034411101101c48488810340d40e04d802030159011a00c941c085052008203c04590181c2c1000c00000e400030760000c0c09558014581c030307070b10401d541d603000b02030380154561441610440215640e035041440c280300294010301510802160120f8120006440002d5883c80384a0340e90315241803249655840c10491800d1702c13550340c840b01c2c0c11040c80d007070b072515010b05074045008002800301c0040c41c100241000202d032030450401c1002c10400095503000030884072000056480142c0b04071105601d1071500c2d0120380010180648180a401845008000345050313420006c0200310880e507881d401001c0307840041002a40b014540c00003000780d8014208102c0042c003c0c24003095a0300c0c43e00a0400701d030700c12510400b0400b0b0746162002800820080d952958180c45031010309141041d034202e41e00c0001c0200c1403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 771189415 1250 771188165 771188167
    0xa350118120201151401020106090b03030a120b09073c0c021c03170c090f01050d150906080f03072d050a0308180a0201081f0f03080d0c09080c06 64
    0x2480c900c00d50204a054003d042c186244c1912959002c4001564280881c0150300b028800700e20070f5028480e1203400c0c0d800500541c50810194402d803044111641d88000071a52000c81d0312003610344215280c4944007960f00c00182d149461a540130018901c1440400030320020440300c1b4801848580f01d241c111607007170400c00c2c0310321480040c004442110b4664000c2804070130450800d5040034204d4030b0030300e09042c549a5583c03208080b0000340106100f40e0380c01030111410f600a5400b4000401c65940000404240c1d294019281014051980d007d110001d980300c0c01004090024000601e03280d1140d0f02a52502c42291203505e140445010301d0030107154a41c0b200d00c9400e00e22080030000030760000075194800700c2410050110380d401c5545043c5080806d6100034100d00c04501c22150613816120340c01035446440d65510481c14107034010300419800400030440030001c41922005510840809130742c1c1d0061040700e810f4881000c0c030746042c880750000600204002048000620400b078880c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 771190665 1250 771189415 771189443
    0x117070f1b170c031b0a060b01020609030910121b120c0801031704260c090103020303180f060d050a0b04090209150117090a052104060e0a350118 64
    0x211300354402c06483d04195481d51410b00303519800400d044007483c0c0207881c10008901098010b903290001291011425041080780081a20300605c1c501581c03001e41c82d188400d05082c4c0904004c48242007250102c0b046074010b42d000c10741e4007020900351501010002c0c8185c1403d400d01805101041c040102410348411490420012030010740d4010040301036042540403a1002e585880d04500b40e40e0391860098444101030fa00300790380058100d030381c00742c002c40c41c100c035642569091281c600c045643c8034200c94080c3d0040d44d5100007520000002100c00180c070305200b919541220036840c00c0500541c10200b10300050303543c101025510905510700803100010510040f05c0011041511300c1d02d0300a44000d1100001d0300045410645108008961241e002907040140c800180c3c0050f29a0303000411050101da80f0903408404800c0f0083d004820b55625155103c820900c1d004403050f80604500760b42d402c5841202d082890446040000c100c007400028403184407a003400b501802107007108110f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 771191915 1250 771190665 771190687
    0x1a12011a060d090206070c030510060b07020621100f120c0513060308070609060b0409020a14011704061512020109051c020a2403021201030f020117070f1b17 69
    0x41840f1540c000d014580c0c80752186000c030251452800103403550b1203502b2030110088801e1142130203680350f00e0715031400c004503542005a164404001c4113440c04082010f04165002203140d039004a07000c6240b07806c21030030821200708841c859403100940d8078500d0480c101152055420348142e54064030044081c079418024074000d4040c40d40000c140d03210000349541408443d60140481d1031290500340301454802d4204410780d842a000039600940201c01005071621224088500e064181040640103000810303a9a40d01c000320b500f601c4076034607001a5030b8074840f02c0c1d0000d00900400c0804900080403500001c1c02c0d04014010f09015450720030702150f210744a40c0140c0d03011940180646000394030f5910056000860040740c103041010150f01b81c035541d010b070003615016009613425000300e070f01c0c6440c1d0305102425118180c0c140601d50401c4030300c1e1402c40d40414802c46168890154024120b01c005000c2804100501c000c000e2000d6088009010200c2e075040050040080d0307519080d040392 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 771193165 1250 771191915 771191921
    0xf2b080c0a05010906050108160506130902120f0709030c090506041d1c05160b0c0c06010306061a0a0509010c11030a0b0109111204030810091a12011a060d 68
    0x28003511684162489a4104001500301c034080c140b14003c00c1c0416642c815600f56280d10750508030416481072002408142070403000303800d41e1001512000c007110381d00c5d02500c00700e902800701d0392403125110040000300c42450380c1440c1c00c09503520703108442a25585a031140c44555004a00629481f4404225141d07242e0700a0301040364a0180a800410080c811a0b07440c00326050f9a4044030034501485c41384c90160068030f600e0250891520103070081a5130b031055024004120406000e0b050040303100210341000400d020b188500e900080b000d0506000c50308240c6803215021031070400304010800ca07a8020203480d4040b80c00c0c00c06529111186c0791a94185100303c117031365094030520242c04d05008072100a98100d03003984d03400300b010628842c1c81410314400c840c00300c400c0c8200c04c004240040c1c807542209610400300007179030a035543c9401c01c0304182c0d0414600344550140300030301e1481030b160019840e42c40503103040080003c40e41d040100304402c0100f8500c0c5100300c001080c440e0507910039030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 771194415 1250 771193165 771193177
    0xc18220c06030e07060207050a0b0c010f0203040c030618020105160309030b15240f1318060905070c02030d1404030b070903120315170307050106080c0f2b08 69
    0x241644010307880307100041c018000120b1118a51103090300c000786060002ca00b02041d26809002d095400d4100440c0d0103141c0d01440c00e80c0265940c600007030f03e1180640c800345000f244a004250f94091640c01e000c001c0e14101005030000702d070f08100d00401031b0b802000b10b46c180249915050100c03041824250750851140e40f01030040d42d0150108042c0d801034014102000300119842800100a503402e0035100043d9440f002d03031900100203c503007120317040018000035454a101c849880da11031800d542044915a1454886074488a06000c48150b0740220741c0d0100c114a0480d0b8851103035000655510300d02144101405018200c01c19109086c40407100619001a808011410207140040c21a8414481a00d142c0d9101c0b0012040354440c2c001c1c900000001020210001c0c1442c0c448111411900b01031249440100840c00c00247c0a0180c50014a034100107405180701d51030500000e204480082c0d88181000021400851707501c1c41c6c6185c4d18040c0d10003002c1940050f2500000c584180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 771195665 1250 771194415 771194423
    0x20a08060c0322050a030e24121b0a09060807030902030c04051305150907050109030b01210203010c02161406040e04110904080307031d340608090c1822 67
    0x119803902419081010200790100982c0c4640014003020100c5410310111803000380210b42c09c11045046a1950740300603003143c20302e0080f0343e0003075003400034514030f902c4100c60102045480100b000603e07044494668043d00c00d050902c100061540040d0b103407a552200a41324603600c070041001140645100742205074400102c404500d0b03003422805210908407082d41d41c80c4204000400d481d486035149401700e0758007012130300e903a9086c421100180981c184081c0381070701d960000c07000540d40034000c08000c0c14060b0007421407000803440003400c24080b0340003218506030b0650121a541c45d2001190200c882c01d15080480745c686241810600c07000081c500d900240d031030144000d101b0b40704010360165289481c204055940ba562030152010301c00c2c150906038229800c1074203c052104040504404056410709524030302d041c000d28111260b402c0900040c10000800c42807850030070407007918000883d41c1244c40594110202d8031040c0041444440d81c01604841e9484680641c80010345648 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 771196915 1250 771195665 771195673
    0x130321152301080a29130b031009022d1519080c1908010611010b010f0f090f06050a090f05090714070b070806030114010b1b0c06070609020a08060c032205 68
    0x510408000c10407038001701c14840c20b000340815108459a1150001d103202c0600900688403490202c0c200a00c102c01d82641c100c1703403021078180104440c892001c0d2210090100c1706101107000c040c0328181500032094401c0241c10032441c02000c10b0303100110640b094510b44440b0950b41e14000b000309005525231540d0080c2c036038001c0040345401800c014166a0343e5030b1117104034894001e14500380c500811089000c00c4080450000c042c0c841ca500465541c01428080400b65880010b401260600d502c8040000c0c408250356440700e03805055180102107203103103030780d0160500001500c0c14501400c1e4a092100c4031415401000d0380e034084d11a5240c200070111498500514090840e00b41254041d100b07528103100381c0802700c8000041c0b41610307050240507041c140d4050500030700205040c43c01d0054418180c2142da0b80d503603c0000c06020307224850224aa02d002d10510400c41c625401c00310302c40c1c210700c0801920b4050348080d070340c3c440c00e21407c0e0388040e152034035001190b0340c0c51500601a801 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 771198165 1250 771196915 771196961
    0x8073009120e0907030204120b0c0913051b12010611070f080a0201030513050606060a05091f26040201030c0306080312010e090f0303130321152301080a 67
    0x6005880044031090036107810f01c09940f912001c0303007244101d000f40940800030590240200f0b00c5030700203581c0b018110201a140c640c40c6400540f030501c03001052900c060700c0301c040284490700d00b40c18205500010001c54100140300000044181707050050000b046030f0441800400c4c00c00b080040002d02608000f004c0c450345030541a6142c01810750b00341e02181c00c002c0400d0340103a802916480d1542c1101c0541030036114031040003200d40c00090705004010041c00320010503a50242003200c0a103d13070114000302888520081c0040c04074180a0441c220540750f00c06060154a601035403203a42486c00082040724004146d008000c95003210ba007500c0301103050741e81260380c4c505090684410500717140d50f03942c80c0d02e902560b4205c41e07080410b440d08203001145544507030b4894020514800c4c01c180780a0f50140c00b10910b2090024044483d40d6210400e03a0002021802c104000c2c00a440042c0701d02007240881003000886107009904016040300040c841072880c0d0301c240c0c0721b5081d105044044c24 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 771199415 1250 771198165 771198167
    0x1a0604060201060920073c060c080106080c090414090c0109090c050a0e0d06020c06040b0609040206030c0a03060915210b040b0c071703070807300912 66
    0x22800f409910000c82c617001400218000b007400400745441d071160058544a0f1950b5071482c1c2d02e80d000b002c00100300316050700056040709400d00201400c1c2000d000d043c02043d5040140030b56040e4641c140c188038100005108281e80030080652103540780300c14556401c81c003000b04000f004004205e103d803000302000e0010020b000300340e56042d903000340d88210207191590303003103400c540c80070f202080414020802c1e103401501a60405d401d00700000d1921002c44030980740d16042ea80701c03022220300c5d60020b104100400c130842c81040d8004006441649051500f640840c0481c400609501d403002c1e00030408604a5110390003030400b404000741c0a01c01103003450010b452602032030007082c8036905000404498252400c2d03224240907003010060a00e074480d5103445440c190060081c00d000c51082102c2c0000c02c50f010040c2c1e406420105402c2c0c2c0c0e901e0941c000400c004d00c0079020104100400c20711284104406460003d00107600f11424148030303030783c2d482600030308a5000080c480711020010799682 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 771200665 1250 771199415 771199421
    0x140c010513050c040e0318060705030d061802090603040308040807050d09081e0a080715020301060509040b030a0302100e192006030403090612021c0603050106120c091a0604060201 79
    0x2252081085502c965095820001916071060305c81d0b400354400d1248560aa640540031010450082c118514019076600d80b01e05650003650066045901c0e400104026485810001803c0c013907110110700340300300d11001507a035110203003019003007000e100003107024040550120755026034010111100c0544486026000d0000351141c1d110a0149a11180751003010300799031418a090b100140001599980d900b0080b034004200030750304051814901100c0740c1e0688025030203055240ca0f41a05c80615504020549100c107801c50b002c1c2d007140f0017580c002a000180038200f203071448000b08030010405880ba1270034054001d04e20030951032030305110500080c42c05140080d68200700201e88407400a051085a2005a8005002846a180c10050940309580b03501116500180148c0b0b050701c40c41210b011320f8480444490200d9a5550820401c5002d209020040c001c9102010107001300d600d410020060f9881102002d944a1401c01085260340c0305c001d4810100804d01030302c07039071100002030003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 771201915 1250 771200665 771200701
    0x5010506030f01090203120c01060b3c16060f090308240306071101200d05160e0906040905120d0605010e100e040b060406021f1401030201140c0105 65
    0x80c0a040b06100e0740303010602400011a8014000b05044011007080340c0343e42c0c1c015a001380c0e0555072180042607900c4068010440b9600c0c0703482111f044141081603010300d6904200d0b2400c0507420740306043c070700000c44d0191801b0010500c41c6c141c00040c80d0070014080c3c940140b075825003501d800c0d1064105a00004143e0050030301254400c6008601c0031419118004d41e02d1142e450740c469400922001d2088400c2102031401c07000102d01e1440f012500500e80c401d10b6401c01c041c000100b5000d103440041d03c40c0315808025081e180000141010340541003455418901d401031200e0740002cac41903240c82d0807a040c81a0b12000b00c662407400780070300907929008a40600c0c1d10b81d052000c0090700750700c80c4000341400d20b070007007885400a030911400d07944441c00c203203140c0d0055100c04c010451640c2e0000980006c140f25009444400b4480a00464501d0001d000603902443e002d801d000703240c4101c0700e15054070340c207003406000b81000304020756a41c02503034685c0402e13600b000c04001107079803811040c4103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 771203165 1250 771201915 771201919
    0xe27090a050609031b06040305071203061a030601030c09180207050a050d05040e10030210050d14010308040906061d0f0a030609050309011d09040303110903060a0605091003030504091a0d05010506 86
    0x82035005c428816885d0350055074080d000502c244080e0000c110000010b1007140018200020f00130b070382d0424404440d940711f400e0301e64000c02000f004007950b010302606118160310300e400b186540c01c00c6014400d2000c40400d9400513a070204600040020820a90400031703084004c9800c1100c5000c0010246d5006000320104102aa80441e00541c012458a001d81c0e5005020411182e40e6240c00c0b03a20390803000c070101080c1c3d00d03040718228007049500168043c500840c00f8582d124200034449003521003e51000080083c100189050247c0d5600c0340740100c601100c100c1703003034680100003d80d0820180c00180440307151103451001c2010000c000c00c40323408203807140441085600c280034010300c03010841c1030300907100400080000344258021003a43c0b490003c601c0c20b040485001c2490803400300d800310203031682e9407424440380c500425200d0780501c240c80c0d4080d145017140c3e40100680100d00c180c0c1600ca07140c0881c04850850300e03199400c000001340102e902e1341c01c02c0c01d01501910003510858 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 771204415 1250 771203165 771203197
    0x408030717040e040308040809090a1a0a0302280503030c010207030215060d06270320060c0403031818051504061401050c010e07080a030e27090a05060903 68
    0x903040700d058240d400b1940c05169551030303036403203407403d903013441004001300d6040c001005525029511811000d0148001601c00900c0580e1040e00c2c2031668125604503114083c210381c01c00041e6a01c0300304045145441941030b040c5481e0f201c400740c2000032030b04056494007000c20b84450b0a84154003400c4054080c1d400c9840d040030303001c07081c66201001e0b1540c0c2d401928000203140850119004809142c1030304141100302025400f83c5003803000c07680310480002c0c1c2414110740100c001b025540c0b090402240280030241048500d000c018895484001d09010722580c039240860b100e10441d100030012031b0b00011034442c406ca42e080c01048115181c10400e00d60781440c0740700c0c0c1001c0c45031405603641141b44800d031442c000010f5405820000703194140e99262507030281e03003610512109000b84074290082052300b085250103032080d0300e003080345070040b80c008150a0040189140030441644d144001c40c00640b105109141045090580a0b00e18032503036052100c0014004024500280e0b042c030f0315 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 771205665 1250 771204415 771204443
    0x9071206060e060901300b04110306010203070212070b0714010c02010605010207090f02041d090d0503061c030e091609060207030812180703111c0b18011104080307 72
    0x81c1d8010340c09002c0107421860602140700c1d594050320b54031070511500401003144601ca0000c40d55003c0418070500c0e10152a0441210035040900410745d201911000f05800d500d48840000d54a010300c440c083d00c40c40141d944030070800300c00c1c80341c0c07005019009a107550f5024030703043c40c0080c004041c418081c07a41c6400c1c410846140f042c0306640c2030b00c00c140c0c080c109441c42d004500001e804e0981c1c0c4200c800d5070030040042c0c03489108880c15140142d406161907207150442c2c10070309102041003070b501800420010031030706554041949850f00907440324a01585424102242c11321801c4841c280c0014640c018070001201401200310040141d81d5004095030b0bc41030200d89801091000908a1406221400c00040d00c2c0c0160340d0b10041c814030000482c1202c0c4203803417500c809a441a03418558160a00341a81030045440d40950081480a2912103070395441c0002008010305c0034039000080f1000040650080d00003441030300c0d001c140c103500d954543c41c010b610ba90050400700e851110b00260 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 771206915 1250 771205665 771205667
    0xa0b04021309230607080c0318030d14010b0a0813080c0a0c030203060c040e0f070c021f020607090315091e1a070c0308070e061207080601110610090f0b0907120606 72
    0xc0c481c405c0000d617580e02c000e912007030070804264101410500c06000788502450051074100054030341c05640313180206030901c62074100f1021110603000f100751700c4800c00c489116981c0003991140c012002000c5201c0050007030030b01210b03a0040d00e00c41881d90064404902c28003400c281d005041d680201c09440c1c0c0341d2994441c100030f512881c03140003040c044400015410b20303100001c84d03601040f64100b0a048094550000d0f503107000d003c03424280301082c16800e00360550704100c550752151040c103044d858039080d6150f284107414655580111a501c8081c80c40c10072680303810410901a025010500d84000d0f03242c0f0184081740740c10102004850480010b0245200d40e0700452860b0700348d02c45d00320542318038804551050340c0044d000d80100301003081012600a500045109803481d5980d801c03141800d80006000419586c02c641d1240d00100c11301508185d00042074048444114002400075200700102e00a064403503071142e44001c80c0f400b002403c1d600860340e403030426507296042100640b80c0354 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 771208165 1250 771206915 771206923
    0xa0b090106020715050c0c100c11030c0f1e04051303020606151204111005040e07181e050307080a030f03021315120f1505120a0b0402130923 62
    0x204074080703140c0c40340c01e841009004174020310f9800b22440940f0109041d54000c06c0e4101c039000c581c00002001d400c02c0409204820401d203100d40c0080340a0070b4000c0c2c640d00062802d10910041d039205410320310b034070308c1c81d080207016040c12850054400e21140c90210003442d9083e81109003a00940103100c00a155841c03d203c08282010100d82d0369824001102e000700c03140c0000420840d400b0038a40134035195561461091102c8402c59503415642c3d90411303885c1e203400600a82003074103008180c4564402032000650300e5013550031020031220b0030300b6a003414031071a000f60740c480b9805005126021400c00400300b41e11070441c5c0070751598408841c00f65022000ca00c22881000105184003500f4031603003800c440408a0b4441360326100040c0c035172104489089550a61054600c0d540d0b90008080740464600760318020401220800070003150038265684414004c5401003400c44000d0004003107544104004c014141041010440d03c10f06181000c040320817012041007850780d0605024032550006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 771209415 1250 771208165 771208169
    0x3080a2304061112070b04020604030602030a0b21071701090611030604060b0f0702010c140105070e0102071d011802070f081e03070e101214010f08070e04080c12030a0b0901060207 79
    0x40c0740a482c00480341c8801b446200060004c9074482e40420000010410303600155000d104c12030000030741100c84c44104500c60040100e0b1800d594120140014a40400300305102200c11070590320158035032440149004000e440c0004199a20701601c000040340c240b80507520134041900d00b00b0403251070b10b101181c640201805c2a000e58820071103031005520511580c400544540d9145840000c1045040d081d01d4007101e45400040c0402c440c4100c1d50f07410800719004041c2040c03080a0b00914503004001f0315814003e298101d00090301400004829a040741c440a401c0020442c001d841032038080400c2c0e02c910b0710303400a0115098101803601080702140c1c0a4012074031030499020f1517000344410151403440b80001d0280c1e04030510355405a5000c0c21050b0030202a203826251f0401e07204480341d411940000d8042e6206174028040d130000c41c28038503006508100b58984070366501001610f01002c4070840f0071590008000d011200441e50080c003c40700301220354124503030726400c0c2260b0b5840340d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 771210665 1250 771209415 771209443
    0xc0809100b0301021209060714091e0d020a0f060216050109030b0a090c0f05090901090c12052a010e030109120518060a0c120f050403080a23040611 65
    0x208480035011a95400015400c9001d000581840071110b003d110f180800c64032a002d41d0404410000c03820760004003450041201d600300b0342030010040200300404040040d942c0342020500341e00016a0f03650390f104c10056801454101441c0c0c4039418400346215500c034500c050301c140c040040c00c1c4011080c0b04001d035603042c3d448040061864448076034a4901401440c80d160ba14560f0201180804060002400c48c00715100860740c6040d05100100800811014440e40341091010000381515000c20403200f110f905400c3e000c1d01c1c0d040c214240040480385074140310381d151030107103408502642c8100c1060700341c80e1a1030000e20f0030207143c21b0701c0340d482c80140356860382200e9502c458011009084012101030a0485100b50140450f0310380d441480c41e2004a402101c1030410000c002120b0b4450f00918504800b481c0c0e40302c0f2020700140140d000080c022280450780fa00c070540300fa1110103840032054015400001c03c01c03000034089e07005000781c5001803485c2c400d0380100341c400921070740c0107162 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 771211915 1250 771210665 771210673
    0xf2d0909051c0e1c0b040809040209040f0c200303010b0f0d06080616020a050d120209030609070314161203030209030d110105010b12040609050313090516030c0206151f03020d0c0809 80
    0x11b07541d00c594130b90740005c40035540076901303224201482c1c07564401d003024a158441c0001d4810403040c806040240c113400d410364012640b81c80441c42800110581e030440358100c840c262540000ba07a4500d6030f010f90042c0d880328038134010b4005803454000901c24095089414511007035091498100c1c2c0b10964000040c09690000b008440b00303500c949000c050701034a40f800142403407601000a410005c064a004030740d0b0b40130420034414402202d20078480800220700a00c40706142c00c450b8900d10b00030b4820895000300030950309007458040e4044609202008054034641e01700e0070030181c842259404034200ba0b40c68130b400443c00e0401c01c41280e800500c2400e03200c196958554030741c8060003c0e00811180c42c0403d0012000da503000d1014400900070100d070224052420070362545031b14503400100400c040c01c1030003a41c4810740104815400035500340c5060302c1c40061070003046d2024880768031103801201d10812101d5065065001d802c420505c0c90003400681c402410403038103030101351002d160b6500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 771213165 1250 771211915 771211921
    0x7020102030a0f121a0a0906060c03030b0d0204020333150d0906110d0f15061d131d12090d0c0f0f2d0909051c0e1c0b 52
    0x1004040e01e4041507110301d89020009480c02501080d034103000280100c0010074055030403c6d01d00208a20043c00d61040b0801c2441d16000b0000c060108070b44000c0c0501d5a181040d00c4582c55802c0440300064001c1d000313554a0804040c111a000a90b091200986030503028410000d0110f01c182c002e007031001020f58082c102500e1080c404d40d40310101703444510303990301c21420006006001da46410203000c00004d860385200707241141a03551030201082e01a10f081c18500c400107044c0040b00680b19285000650442d11150280034000382542155010b0a9181001c0c0c0c80c0c4407980113080a00d03103500c135401ca0701c050f00b45042c2e600c8000c88810b08003070505101107036142c00c15801d100300c101c1c010003034241c8040c1ea07051510544142c0e0340101b0b4402034458800e000b00540c2003143c080c60220802207486a80002e110f4116202d1a400303547d00c61500c1310750480c12b202c006c0007144504843d00b1a030340852480850060000c034000500d660148404c80c10b00305552800c0e030300700085680c105504460640d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 771214415 1250 771213165 771213167
    0x80c0405091f0b0301090c0501121b120f090b010603151a03060303250212060f01182d180f0204051806040c060206100605072d062007020102030a 64
    0x55400c03031440b014180e941440389001d503024068000081d00885800c4045400d020004180d50351000c41e0079442405c02c142c20100140d0695040345103403591400128404034420303000051710f1050200c03031600d07003070407843c40c14808885643c50403210192000c01803040050780621406801d44100c0341c4041c3c0d031007040340c90000c84c400110b500042c02420b81e4a85000350300340356100c18059292020350754440c60001c0450410929990441c921900203007801d10703100514040780b280502070103c0c0b81c02180c04404881d0b54903048100c1ca0f4100d003111f014110f804103021701214111480b00008242000d40410f070282e194100ca5018076082505003c00781c04507000d000281c500542840c244450114518003660300c03c0c0540da00492050003c0001c2600d0008028a060b0b40a0030740211644000020481d00b5000000c032a641c40d0302900e0500c001c03840c2c4000721a00821040d0003000c000040c0f221100300541e40c5e0282103a0040d1107002c500c032400c4213030f80240e02e000704000240980d1041156041d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 771215665 1250 771214415 771214453
    0x102070e1906030209040809030c01080402030a1401152301050a050d15090204120c0e010803070609051005070f0906170109020d06031203020c21030118090516080c040509 75
    0x10715071a00700070501603075030b50224100103000c40d401d4034159400304038840b480c603040c000c1800908091030701d84076500f000d8000a84410110400070010202c007014100d11403029000308030001038a00e00b011045545005d03108803100300030b03044054948c0b0311030700b40d91541c0100296000c000250f03a4403800c0a11402485c8004c001c420010361000407100000248a0624001030001e09040c010310032030711480340750410300c15031f1541001d0309000325580140030a10000064505040d00940d0201d05008c003818002d082181d03c01c1500b111509110400c61310542117000030888a24035651301203690750320301d42102ca04000350019045003045200400508007650090109440d0545000071802c0c2d89a03203c000c03010020b0750b030101182d00880c44084a480520104030b01c41043c0d500c0c0e12503804441c036490144c1c44140545606501401d105020b5140294003612101d9407100449090008500d404803624004d403160703a490b44103d4600304041d00f01401000d0140040c44000c0220396032405030070b000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 771216915 1250 771215665 771215701
    0x23011a0405012d0302100e0f03070501020d2706051909060503010315020d052505041a03040c1d011a07020a18140f06090108060c0d0b06070f0302060709050102070e 72
    0x5402c00700f1001001680e10400c091450454545036551101c09440034000c40700304024410f0b2181d002003008210f166004991105108403900d041d4030046003024003140210f02090005d07500255245010440d43e400400800c91400b0f0204c031604410404031045542400d00e00603140020783c1840108001041c100144643e072840c0280941003400c15003016048842c101c50b01c40c0350315007450744040f84552006000e085442c5504d4070318606810800b6207940c0340a00f14a0303549801001001800b0b2240025404010380f83c01c0404440c0c0060b22104400880e03002c0c001d080c1740080d0405155140402c0400f00c1e54100d41c054454000382c1d00e04000003200b44000000980485d40356105079403190201e225040c80756001e041d080d501401d08a0502c003180005811010365030313000900740301c061080307007080d950005d00078040400c48030484004555603018540300107000004100c4030404242d0049196441550186d43d04030304070344d48000481c0d41d55081d108026100140c04081a08100013490f000c0c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 771218165 1250 771216915 771216989
    0x1a04112817160e060c15180d08041b0515090306160e0d0804050607080d0e0303070813080904020d20040510120b1c0302060c04030b070c23011a040501 66
    0xb0402000805c1181030110014404061044179001c11059613054644180f820185100421901040c564064004407000d4806000d0105d000203030341070090914440006004064242e2800f0070081004030f0480d000407404a1003402540c0c0040c410804045046000c05002d6941c10100302d080d00500003021152901610300f140c0402c004103041c0c0340c410003418224801c0c3c80c601c3d5a00707a045408003c071606035034802056041041030214203644040d0b100d402803074030b544140300c2006501d81a0024400c101c01b83e40c01900204040008004a42c0055159202011425184031202c0341201c294810390060580c086c1c07080518088151044485d100c01d01d01449000940181d10030000e0b44039415010104004c5210104d4141007640c107100c11604410807803c1642000c0c115641c4000a0310002c020a040000c07000c155014413009100a018204031840c24135a0240ba4090182c040d00ca11001781c0e404d07001601446039141064800c0b40e040f40c10080300041c80c081310350010121000c02c424145 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 771219415 1250 771218165 771218167
    0xc040e060a030506090c120c0303040501051602040501181a03120a091a220605041418251704110105120720011a04112817160e06 57
    0xb10008200f082800c1c004c4050340c000b000304100160400540c04608030b01c07002c0381e8000300345a583c81e4400006840c00d4541c00d003005916280c0302c80c0c1000141d01d5510010794401d0409000040048021032441c260b034160b10310900c079121904044001924000600c107401d94000d02c0c404110312214005041026241e290004a81c0c0d52000e046180c200703840c0410702541b00000700c400c03242d0b884c404d04030325000440d0450348400703290040c041c4c02d0307020341d12a0150030001501c101c082d03591803801070411002c3c040b80d81040d500701070f51040e441070000c540e810030303045088034059000d03030007107018000d210301c03c1d1010344580e90396940d0300c00704d90184902c41e81031080034040b034032400082c040950310070440b980c1c4030000405891901c081441c020301ca400d4242e45043d101004c140c10341c07500700015500c01c0d20f0104034580c81415204aa1042c1d050100504101e840120f0803003500440c1a101174515980710f800760b0820b4036011024203015070f03c4030290048021a0605035016020b04a004e141c014082 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 771220665 1250 771219415 771219419
    0xc01030b0609090a020a0314041a0408090d05010c080a1a060c070b0f1314060307030c050c10060302030c120615150301031109090105010803160f0609031211030c040e060a 75
    0xc540c41ea40f05480c0c041c002c54000c02c4025034154140f103015220006601c0c100d00030305080d00c4003600130510003448011070302e6280002d010f0049082c03c0300c50340040600400c03203200540c20500c0c000c001303400d4400006451000442c10029807402603400140c0044090803883c12404100310150b4805ca407910340710f006e82d103000140c8070840005840d00c0c5070003004c9c4995405441a407442070702e800340c11424040f41500300c1080541c449206481e8450a90304002405000c54401503901d4010411584d00c548111003840d1a40152500030348101d03442901101c5621140b0703070402041c032001f00403040030341c1d205078002407540d010844070010b001400341c207031a603684240010a440d903109030400d4413440c3d40c2e4011039200703041006007180d01c031006000811031541002c0d001c94882c45403104143c0c00007031042e0883c050144840f8400d13176441d072020003040617004c9850050100042040044200d910b0309100d00000c42081040340e11804c86028a00d04d02410616200307280440542102d41104d18080c0c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 771221915 1250 771220665 771220669
    0xe030708030703120b0319030c020301060e070309060b091302090c070605100e0702011a041a0402030f10060903030806210607030e1b0f092503150e090c01030b0609 72
    0x1400a98065500c100351014104c40c00001e84114200300c6000368001030040c59600315065905c40ca40c3d5051501407a0802d080c0006409440c3c05d0b007005140320341601c00d00ca06541c0550003030061a2083e803081c04a41e6605007001504442144c8070410030009a1003030006242280030b40d0f5000b103c014019003042047d8495404546080b100e04030746945480d418002400580c01965006d00c2d42d1009000c03075284404c030141d1a9842103500c40c01203440e01806003d050700350b404062181030140c0215164681a04242c80c005001d8900030700180b80c9810108503248240300d400180c0743c0580390345d00303039858803010301035080c240740b0306415560703200d11440d8102131f03081c80003d0103104c03280c4e00030501d0003070071300300030b041500405c05d0250441e41e01106200640302c440c0643c0300750404a0352100b10790348940c0c2240d8074441c18400e502c41000c6210546600300e0305907101104141c5001000c0004584503c0c0c08243c45c3d905403140101030b4841203c05105610a130000b20007500c000d0581420003402c500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 771223021 1106 771221915 771221917
    0xe04050a090203030309010c1403010e0f0a09050d02060702010506010e090a0f1d0610060f1d060c0f060109050a14010e0703060e1320060a0e03070803 66
    0xd00455026409088525000b0b800d881ea00d28100c01041d00800110390400d01103a0707105850150000c8200c2a6410381d120305151182945a201e1124041c3c036000706010101902c0d90358145c00900b080c08048543c0722150020501070400c008080d007950303c002c041604100d81480c0b04281569007440054201091307140c00106190200020f101030196001c682440c20a0440700c2003038900b00045103407042000c0403400c9a11900d400c42140c48010025100000030680c0d000224400000b032036400c854640145942d10340000c9045260424038060b0f0042041c1d00581300401000c0a207020b115840328141c641000402d041041c0f200300c288040c051080c10702d00520005908a000b58408805050400c104540500e421120308107907540140341200e40e0000003080f0241d08400d0b40c403000c0d810100900f80c1e030828031100422610a106007401540c144591500010a610188 = true := by decide +kernel

theorem cover : BRFrame.Cov 771043165 771223021 := by
  have h0 := BRFrame.cov_init 771043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 771043165 ≤ n) (h2 : n < 771223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
